-- Prove2me | solution 1 for syracuse_descends_range_1736569_1738569
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:33:15.568031+00:00
-- url     : https://prove2.me/submissions/107fa426-d5e7-40de-87d3-1add79d110d4

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


theorem B2605061 : Blo 1736569 2605061 := bbase (se 4 (by rfl) ⟨244224, by rfl⟩ : syracuseStep 2605061 = 488449) (by norm_num)
theorem B2605085 : Blo 1736569 2605085 := bbase (se 3 (by rfl) ⟨488453, by rfl⟩ : syracuseStep 2605085 = 976907) (by norm_num)
theorem B2474021 : Blo 1736569 2474021 := bbase (se 4 (by rfl) ⟨231939, by rfl⟩ : syracuseStep 2474021 = 463879) (by norm_num)
theorem B3907637 : Blo 1736569 3907637 := bbase (se 5 (by rfl) ⟨183170, by rfl⟩ : syracuseStep 3907637 = 366341) (by norm_num)
theorem B2605109 : Blo 1736569 2605109 := bbase (se 5 (by rfl) ⟨122114, by rfl⟩ : syracuseStep 2605109 = 244229) (by norm_num)
theorem B2605133 : Blo 1736569 2605133 := bbase (se 3 (by rfl) ⟨488462, by rfl⟩ : syracuseStep 2605133 = 976925) (by norm_num)
theorem B4399181 : Blo 1736569 4399181 := bbase (se 3 (by rfl) ⟨824846, by rfl⟩ : syracuseStep 4399181 = 1649693) (by norm_num)
theorem B2605157 : Blo 1736569 2605157 := bbase (se 4 (by rfl) ⟨244233, by rfl⟩ : syracuseStep 2605157 = 488467) (by norm_num)
theorem B2228329 : Blo 1736569 2228329 := bbase (se 2 (by rfl) ⟨835623, by rfl⟩ : syracuseStep 2228329 = 1671247) (by norm_num)
theorem B2474101 : Blo 1736569 2474101 := bbase (se 5 (by rfl) ⟨115973, by rfl⟩ : syracuseStep 2474101 = 231947) (by norm_num)
theorem B3907709 : Blo 1736569 3907709 := bbase (se 3 (by rfl) ⟨732695, by rfl⟩ : syracuseStep 3907709 = 1465391) (by norm_num)
theorem B2605181 : Blo 1736569 2605181 := bbase (se 3 (by rfl) ⟨488471, by rfl⟩ : syracuseStep 2605181 = 976943) (by norm_num)
theorem B2932861 : Blo 1736569 2932861 := bbase (se 3 (by rfl) ⟨549911, by rfl⟩ : syracuseStep 2932861 = 1099823) (by norm_num)
theorem B1761421 : Blo 1736569 1761421 := bbase (se 3 (by rfl) ⟨330266, by rfl⟩ : syracuseStep 1761421 = 660533) (by norm_num)
theorem B2605205 : Blo 1736569 2605205 := bbase (se 6 (by rfl) ⟨61059, by rfl⟩ : syracuseStep 2605205 = 122119) (by norm_num)
theorem B2605229 : Blo 1736569 2605229 := bbase (se 3 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 2605229 = 976961) (by norm_num)
theorem B1761469 : Blo 1736569 1761469 := bbase (se 3 (by rfl) ⟨330275, by rfl⟩ : syracuseStep 1761469 = 660551) (by norm_num)
theorem B3907781 : Blo 1736569 3907781 := bbase (se 4 (by rfl) ⟨366354, by rfl⟩ : syracuseStep 3907781 = 732709) (by norm_num)
theorem B2605253 : Blo 1736569 2605253 := bbase (se 4 (by rfl) ⟨244242, by rfl⟩ : syracuseStep 2605253 = 488485) (by norm_num)
theorem B2932949 : Blo 1736569 2932949 := bbase (se 7 (by rfl) ⟨34370, by rfl⟩ : syracuseStep 2932949 = 68741) (by norm_num)
theorem B2605277 : Blo 1736569 2605277 := bbase (se 3 (by rfl) ⟨488489, by rfl⟩ : syracuseStep 2605277 = 976979) (by norm_num)
theorem B2474221 : Blo 1736569 2474221 := bbase (se 3 (by rfl) ⟨463916, by rfl⟩ : syracuseStep 2474221 = 927833) (by norm_num)
theorem B2605301 : Blo 1736569 2605301 := bbase (se 5 (by rfl) ⟨122123, by rfl⟩ : syracuseStep 2605301 = 244247) (by norm_num)
theorem B7921925 : Blo 1736569 7921925 := bbase (se 4 (by rfl) ⟨742680, by rfl⟩ : syracuseStep 7921925 = 1485361) (by norm_num)
theorem B3907853 : Blo 1736569 3907853 := bbase (se 3 (by rfl) ⟨732722, by rfl⟩ : syracuseStep 3907853 = 1465445) (by norm_num)
theorem B2605325 : Blo 1736569 2605325 := bbase (se 3 (by rfl) ⟨488498, by rfl⟩ : syracuseStep 2605325 = 976997) (by norm_num)
theorem B4399373 : Blo 1736569 4399373 := bbase (se 3 (by rfl) ⟨824882, by rfl⟩ : syracuseStep 4399373 = 1649765) (by norm_num)
theorem B5865749 : Blo 1736569 5865749 := bbase (se 6 (by rfl) ⟨137478, by rfl⟩ : syracuseStep 5865749 = 274957) (by norm_num)
theorem B2605349 : Blo 1736569 2605349 := bbase (se 4 (by rfl) ⟨244251, by rfl⟩ : syracuseStep 2605349 = 488503) (by norm_num)
theorem B2605373 : Blo 1736569 2605373 := bbase (se 3 (by rfl) ⟨488507, by rfl⟩ : syracuseStep 2605373 = 977015) (by norm_num)
theorem B2474317 : Blo 1736569 2474317 := bbase (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) (by norm_num)
theorem B3907925 : Blo 1736569 3907925 := bbase (se 10 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 3907925 = 11449) (by norm_num)
theorem B2605397 : Blo 1736569 2605397 := bbase (se 10 (by rfl) ⟨3816, by rfl⟩ : syracuseStep 2605397 = 7633) (by norm_num)
theorem B2933077 : Blo 1736569 2933077 := bbase (se 10 (by rfl) ⟨4296, by rfl⟩ : syracuseStep 2933077 = 8593) (by norm_num)
theorem B2605421 : Blo 1736569 2605421 := bbase (se 3 (by rfl) ⟨488516, by rfl⟩ : syracuseStep 2605421 = 977033) (by norm_num)
theorem B2605445 : Blo 1736569 2605445 := bbase (se 4 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 2605445 = 488521) (by norm_num)
theorem B3907997 : Blo 1736569 3907997 := bbase (se 3 (by rfl) ⟨732749, by rfl⟩ : syracuseStep 3907997 = 1465499) (by norm_num)
theorem B2605469 : Blo 1736569 2605469 := bbase (se 3 (by rfl) ⟨488525, by rfl⟩ : syracuseStep 2605469 = 977051) (by norm_num)
theorem B2933165 : Blo 1736569 2933165 := bbase (se 3 (by rfl) ⟨549968, by rfl⟩ : syracuseStep 2933165 = 1099937) (by norm_num)
theorem B6685109 : Blo 1736569 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B2605493 : Blo 1736569 2605493 := bbase (se 5 (by rfl) ⟨122132, by rfl⟩ : syracuseStep 2605493 = 244265) (by norm_num)
theorem B2605517 : Blo 1736569 2605517 := bbase (se 3 (by rfl) ⟨488534, by rfl⟩ : syracuseStep 2605517 = 977069) (by norm_num)
theorem B3908069 : Blo 1736569 3908069 := bbase (se 4 (by rfl) ⟨366381, by rfl⟩ : syracuseStep 3908069 = 732763) (by norm_num)
theorem B2605541 : Blo 1736569 2605541 := bbase (se 4 (by rfl) ⟨244269, by rfl⟩ : syracuseStep 2605541 = 488539) (by norm_num)
theorem B3523061 : Blo 1736569 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B2605565 : Blo 1736569 2605565 := bbase (se 3 (by rfl) ⟨488543, by rfl⟩ : syracuseStep 2605565 = 977087) (by norm_num)
theorem B3523085 : Blo 1736569 3523085 := bbase (se 3 (by rfl) ⟨660578, by rfl⟩ : syracuseStep 3523085 = 1321157) (by norm_num)
theorem B2605589 : Blo 1736569 2605589 := bbase (se 6 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 2605589 = 122137) (by norm_num)
theorem B3908141 : Blo 1736569 3908141 := bbase (se 3 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 3908141 = 1465553) (by norm_num)
theorem B2605613 : Blo 1736569 2605613 := bbase (se 3 (by rfl) ⟨488552, by rfl⟩ : syracuseStep 2605613 = 977105) (by norm_num)
theorem B2933293 : Blo 1736569 2933293 := bbase (se 3 (by rfl) ⟨549992, by rfl⟩ : syracuseStep 2933293 = 1099985) (by norm_num)
theorem B6595141 : Blo 1736569 6595141 := bbase (se 4 (by rfl) ⟨618294, by rfl⟩ : syracuseStep 6595141 = 1236589) (by norm_num)
theorem B2605637 : Blo 1736569 2605637 := bbase (se 4 (by rfl) ⟨244278, by rfl⟩ : syracuseStep 2605637 = 488557) (by norm_num)
theorem B2605661 : Blo 1736569 2605661 := bbase (se 3 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 2605661 = 977123) (by norm_num)
theorem B6431333 : Blo 1736569 6431333 := bbase (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) (by norm_num)
theorem B4399717 : Blo 1736569 4399717 := bbase (se 4 (by rfl) ⟨412473, by rfl⟩ : syracuseStep 4399717 = 824947) (by norm_num)
theorem B3908213 : Blo 1736569 3908213 := bbase (se 5 (by rfl) ⟨183197, by rfl⟩ : syracuseStep 3908213 = 366395) (by norm_num)
theorem B2605685 : Blo 1736569 2605685 := bbase (se 5 (by rfl) ⟨122141, by rfl⟩ : syracuseStep 2605685 = 244283) (by norm_num)
theorem B2933381 : Blo 1736569 2933381 := bbase (se 4 (by rfl) ⟨275004, by rfl⟩ : syracuseStep 2933381 = 550009) (by norm_num)
theorem B2605709 : Blo 1736569 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B2605733 : Blo 1736569 2605733 := bbase (se 4 (by rfl) ⟨244287, by rfl⟩ : syracuseStep 2605733 = 488575) (by norm_num)
theorem B2507429 : Blo 1736569 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B3908285 : Blo 1736569 3908285 := bbase (se 3 (by rfl) ⟨732803, by rfl⟩ : syracuseStep 3908285 = 1465607) (by norm_num)
theorem B2605757 : Blo 1736569 2605757 := bbase (se 3 (by rfl) ⟨488579, by rfl⟩ : syracuseStep 2605757 = 977159) (by norm_num)
theorem B5866181 : Blo 1736569 5866181 := bbase (se 4 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 5866181 = 1099909) (by norm_num)
theorem B2605781 : Blo 1736569 2605781 := bbase (se 7 (by rfl) ⟨30536, by rfl⟩ : syracuseStep 2605781 = 61073) (by norm_num)
theorem B4399829 : Blo 1736569 4399829 := bbase (se 7 (by rfl) ⟨51560, by rfl⟩ : syracuseStep 4399829 = 103121) (by norm_num)
theorem B7045861 : Blo 1736569 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B2605805 : Blo 1736569 2605805 := bbase (se 3 (by rfl) ⟨488588, by rfl⟩ : syracuseStep 2605805 = 977177) (by norm_num)
theorem B3908357 : Blo 1736569 3908357 := bbase (se 4 (by rfl) ⟨366408, by rfl⟩ : syracuseStep 3908357 = 732817) (by norm_num)
theorem B2605829 : Blo 1736569 2605829 := bbase (se 4 (by rfl) ⟨244296, by rfl⟩ : syracuseStep 2605829 = 488593) (by norm_num)
theorem B3711749 : Blo 1736569 3711749 := bbase (se 4 (by rfl) ⟨347976, by rfl⟩ : syracuseStep 3711749 = 695953) (by norm_num)
theorem B2933509 : Blo 1736569 2933509 := bbase (se 4 (by rfl) ⟨275016, by rfl⟩ : syracuseStep 2933509 = 550033) (by norm_num)
theorem B2605853 : Blo 1736569 2605853 := bbase (se 3 (by rfl) ⟨488597, by rfl⟩ : syracuseStep 2605853 = 977195) (by norm_num)
theorem B2605877 : Blo 1736569 2605877 := bbase (se 5 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 2605877 = 244301) (by norm_num)
theorem B8799029 : Blo 1736569 8799029 := bbase (se 5 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 8799029 = 824909) (by norm_num)
theorem B2474813 : Blo 1736569 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B3908429 : Blo 1736569 3908429 := bbase (se 3 (by rfl) ⟨732830, by rfl⟩ : syracuseStep 3908429 = 1465661) (by norm_num)
theorem B2605901 : Blo 1736569 2605901 := bbase (se 3 (by rfl) ⟨488606, by rfl⟩ : syracuseStep 2605901 = 977213) (by norm_num)
theorem B20071253 : Blo 1736569 20071253 := bbase (se 9 (by rfl) ⟨58802, by rfl⟩ : syracuseStep 20071253 = 117605) (by norm_num)
theorem B2933597 : Blo 1736569 2933597 := bbase (se 3 (by rfl) ⟨550049, by rfl⟩ : syracuseStep 2933597 = 1100099) (by norm_num)
theorem B2605925 : Blo 1736569 2605925 := bbase (se 4 (by rfl) ⟨244305, by rfl⟩ : syracuseStep 2605925 = 488611) (by norm_num)
theorem B6595445 : Blo 1736569 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B2605949 : Blo 1736569 2605949 := bbase (se 3 (by rfl) ⟨488615, by rfl⟩ : syracuseStep 2605949 = 977231) (by norm_num)
theorem B5358469 : Blo 1736569 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B3908501 : Blo 1736569 3908501 := bbase (se 6 (by rfl) ⟨91605, by rfl⟩ : syracuseStep 3908501 = 183211) (by norm_num)
theorem B2605973 : Blo 1736569 2605973 := bbase (se 6 (by rfl) ⟨61077, by rfl⟩ : syracuseStep 2605973 = 122155) (by norm_num)
theorem B4400021 : Blo 1736569 4400021 := bbase (se 6 (by rfl) ⟨103125, by rfl⟩ : syracuseStep 4400021 = 206251) (by norm_num)
theorem B2605997 : Blo 1736569 2605997 := bbase (se 3 (by rfl) ⟨488624, by rfl⟩ : syracuseStep 2605997 = 977249) (by norm_num)
theorem B2606021 : Blo 1736569 2606021 := bbase (se 4 (by rfl) ⟨244314, by rfl⟩ : syracuseStep 2606021 = 488629) (by norm_num)
theorem B3908573 : Blo 1736569 3908573 := bbase (se 3 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 3908573 = 1465715) (by norm_num)
theorem B2606045 : Blo 1736569 2606045 := bbase (se 3 (by rfl) ⟨488633, by rfl⟩ : syracuseStep 2606045 = 977267) (by norm_num)
theorem B2933725 : Blo 1736569 2933725 := bbase (se 3 (by rfl) ⟨550073, by rfl⟩ : syracuseStep 2933725 = 1100147) (by norm_num)
theorem B2606069 : Blo 1736569 2606069 := bbase (se 5 (by rfl) ⟨122159, by rfl⟩ : syracuseStep 2606069 = 244319) (by norm_num)
theorem B3711989 : Blo 1736569 3711989 := bbase (se 5 (by rfl) ⟨173999, by rfl⟩ : syracuseStep 3711989 = 347999) (by norm_num)
theorem B2606093 : Blo 1736569 2606093 := bbase (se 3 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 2606093 = 977285) (by norm_num)
theorem B3908645 : Blo 1736569 3908645 := bbase (se 4 (by rfl) ⟨366435, by rfl⟩ : syracuseStep 3908645 = 732871) (by norm_num)
theorem B2606117 : Blo 1736569 2606117 := bbase (se 4 (by rfl) ⟨244323, by rfl⟩ : syracuseStep 2606117 = 488647) (by norm_num)
theorem B4949045 : Blo 1736569 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B2933813 : Blo 1736569 2933813 := bbase (se 5 (by rfl) ⟨137522, by rfl⟩ : syracuseStep 2933813 = 275045) (by norm_num)
theorem B2606141 : Blo 1736569 2606141 := bbase (se 3 (by rfl) ⟨488651, by rfl⟩ : syracuseStep 2606141 = 977303) (by norm_num)
theorem B9389141 : Blo 1736569 9389141 := bbase (se 8 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 9389141 = 110029) (by norm_num)
theorem B2606165 : Blo 1736569 2606165 := bbase (se 8 (by rfl) ⟨15270, by rfl⟩ : syracuseStep 2606165 = 30541) (by norm_num)
theorem B3908717 : Blo 1736569 3908717 := bbase (se 3 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 3908717 = 1465769) (by norm_num)
theorem B2606189 : Blo 1736569 2606189 := bbase (se 3 (by rfl) ⟨488660, by rfl⟩ : syracuseStep 2606189 = 977321) (by norm_num)
theorem B5866613 : Blo 1736569 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B2606213 : Blo 1736569 2606213 := bbase (se 4 (by rfl) ⟨244332, by rfl⟩ : syracuseStep 2606213 = 488665) (by norm_num)
theorem B2606237 : Blo 1736569 2606237 := bbase (se 3 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 2606237 = 977339) (by norm_num)
theorem B3908789 : Blo 1736569 3908789 := bbase (se 5 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 3908789 = 366449) (by norm_num)
theorem B2606261 : Blo 1736569 2606261 := bbase (se 5 (by rfl) ⟨122168, by rfl⟩ : syracuseStep 2606261 = 244337) (by norm_num)
theorem B7423157 : Blo 1736569 7423157 := bbase (se 5 (by rfl) ⟨347960, by rfl⟩ : syracuseStep 7423157 = 695921) (by norm_num)
theorem B2606285 : Blo 1736569 2606285 := bbase (se 3 (by rfl) ⟨488678, by rfl⟩ : syracuseStep 2606285 = 977357) (by norm_num)
theorem B5014757 : Blo 1736569 5014757 := bbase (se 4 (by rfl) ⟨470133, by rfl⟩ : syracuseStep 5014757 = 940267) (by norm_num)
theorem B2606309 : Blo 1736569 2606309 := bbase (se 4 (by rfl) ⟨244341, by rfl⟩ : syracuseStep 2606309 = 488683) (by norm_num)
theorem B4400365 : Blo 1736569 4400365 := bbase (se 3 (by rfl) ⟨825068, by rfl⟩ : syracuseStep 4400365 = 1650137) (by norm_num)
theorem B3908861 : Blo 1736569 3908861 := bbase (se 3 (by rfl) ⟨732911, by rfl⟩ : syracuseStep 3908861 = 1465823) (by norm_num)
theorem B2606333 : Blo 1736569 2606333 := bbase (se 3 (by rfl) ⟨488687, by rfl⟩ : syracuseStep 2606333 = 977375) (by norm_num)
theorem B2606357 : Blo 1736569 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B2606381 : Blo 1736569 2606381 := bbase (se 3 (by rfl) ⟨488696, by rfl⟩ : syracuseStep 2606381 = 977393) (by norm_num)
theorem B3908933 : Blo 1736569 3908933 := bbase (se 4 (by rfl) ⟨366462, by rfl⟩ : syracuseStep 3908933 = 732925) (by norm_num)
theorem B3343685 : Blo 1736569 3343685 := bbase (se 4 (by rfl) ⟨313470, by rfl⟩ : syracuseStep 3343685 = 626941) (by norm_num)
theorem B2606405 : Blo 1736569 2606405 := bbase (se 4 (by rfl) ⟨244350, by rfl⟩ : syracuseStep 2606405 = 488701) (by norm_num)
theorem B2606429 : Blo 1736569 2606429 := bbase (se 3 (by rfl) ⟨488705, by rfl⟩ : syracuseStep 2606429 = 977411) (by norm_num)
theorem B4400477 : Blo 1736569 4400477 := bbase (se 3 (by rfl) ⟨825089, by rfl⟩ : syracuseStep 4400477 = 1650179) (by norm_num)
theorem B2475365 : Blo 1736569 2475365 := bbase (se 4 (by rfl) ⟨232065, by rfl⟩ : syracuseStep 2475365 = 464131) (by norm_num)
theorem B2860397 : Blo 1736569 2860397 := bbase (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) (by norm_num)
theorem B2229617 : Blo 1736569 2229617 := bbase (se 2 (by rfl) ⟨836106, by rfl⟩ : syracuseStep 2229617 = 1672213) (by norm_num)
theorem B2606453 : Blo 1736569 2606453 := bbase (se 5 (by rfl) ⟨122177, by rfl⟩ : syracuseStep 2606453 = 244355) (by norm_num)
theorem B3909005 : Blo 1736569 3909005 := bbase (se 3 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 3909005 = 1465877) (by norm_num)
theorem B2606477 : Blo 1736569 2606477 := bbase (se 3 (by rfl) ⟨488714, by rfl⟩ : syracuseStep 2606477 = 977429) (by norm_num)
theorem B2606501 : Blo 1736569 2606501 := bbase (se 4 (by rfl) ⟨244359, by rfl⟩ : syracuseStep 2606501 = 488719) (by norm_num)
theorem B7423397 : Blo 1736569 7423397 := bbase (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) (by norm_num)
theorem B2115001 : Blo 1736569 2115001 := bbase (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) (by norm_num)
theorem B2606525 : Blo 1736569 2606525 := bbase (se 3 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 2606525 = 977447) (by norm_num)
theorem B3909077 : Blo 1736569 3909077 := bbase (se 7 (by rfl) ⟨45809, by rfl⟩ : syracuseStep 3909077 = 91619) (by norm_num)
theorem B2606549 : Blo 1736569 2606549 := bbase (se 7 (by rfl) ⟨30545, by rfl⟩ : syracuseStep 2606549 = 61091) (by norm_num)
theorem B2606573 : Blo 1736569 2606573 := bbase (se 3 (by rfl) ⟨488732, by rfl⟩ : syracuseStep 2606573 = 977465) (by norm_num)
theorem B3712493 : Blo 1736569 3712493 := bbase (se 3 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 3712493 = 1392185) (by norm_num)
theorem B3712501 : Blo 1736569 3712501 := bbase (se 5 (by rfl) ⟨174023, by rfl⟩ : syracuseStep 3712501 = 348047) (by norm_num)
theorem B2606597 : Blo 1736569 2606597 := bbase (se 4 (by rfl) ⟨244368, by rfl⟩ : syracuseStep 2606597 = 488737) (by norm_num)
theorem B3909149 : Blo 1736569 3909149 := bbase (se 3 (by rfl) ⟨732965, by rfl⟩ : syracuseStep 3909149 = 1465931) (by norm_num)
theorem B2606621 : Blo 1736569 2606621 := bbase (se 3 (by rfl) ⟨488741, by rfl⟩ : syracuseStep 2606621 = 977483) (by norm_num)
theorem B5867045 : Blo 1736569 5867045 := bbase (se 4 (by rfl) ⟨550035, by rfl⟩ : syracuseStep 5867045 = 1100071) (by norm_num)
theorem B4400669 : Blo 1736569 4400669 := bbase (se 3 (by rfl) ⟨825125, by rfl⟩ : syracuseStep 4400669 = 1650251) (by norm_num)
theorem B2606645 : Blo 1736569 2606645 := bbase (se 5 (by rfl) ⟨122186, by rfl⟩ : syracuseStep 2606645 = 244373) (by norm_num)
theorem B4458053 : Blo 1736569 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B2606669 : Blo 1736569 2606669 := bbase (se 3 (by rfl) ⟨488750, by rfl⟩ : syracuseStep 2606669 = 977501) (by norm_num)
theorem B3909221 : Blo 1736569 3909221 := bbase (se 4 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 3909221 = 732979) (by norm_num)
theorem B3130981 : Blo 1736569 3130981 := bbase (se 4 (by rfl) ⟨293529, by rfl⟩ : syracuseStep 3130981 = 587059) (by norm_num)
theorem B2606693 : Blo 1736569 2606693 := bbase (se 4 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 2606693 = 488755) (by norm_num)
theorem B2606717 : Blo 1736569 2606717 := bbase (se 3 (by rfl) ⟨488759, by rfl⟩ : syracuseStep 2606717 = 977519) (by norm_num)
theorem B2606741 : Blo 1736569 2606741 := bbase (se 6 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 2606741 = 122191) (by norm_num)
theorem B3909293 : Blo 1736569 3909293 := bbase (se 3 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 3909293 = 1465985) (by norm_num)
theorem B2606765 : Blo 1736569 2606765 := bbase (se 3 (by rfl) ⟨488768, by rfl⟩ : syracuseStep 2606765 = 977537) (by norm_num)
theorem B2606789 : Blo 1736569 2606789 := bbase (se 4 (by rfl) ⟨244386, by rfl⟩ : syracuseStep 2606789 = 488773) (by norm_num)
theorem B8914645 : Blo 1736569 8914645 := bbase (se 7 (by rfl) ⟨104468, by rfl⟩ : syracuseStep 8914645 = 208937) (by norm_num)
theorem B2606813 : Blo 1736569 2606813 := bbase (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) (by norm_num)
theorem B3909365 : Blo 1736569 3909365 := bbase (se 5 (by rfl) ⟨183251, by rfl⟩ : syracuseStep 3909365 = 366503) (by norm_num)
theorem B2606837 : Blo 1736569 2606837 := bbase (se 5 (by rfl) ⟨122195, by rfl⟩ : syracuseStep 2606837 = 244391) (by norm_num)
theorem B3131149 : Blo 1736569 3131149 := bbase (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) (by norm_num)
theorem B2606861 : Blo 1736569 2606861 := bbase (se 3 (by rfl) ⟨488786, by rfl⟩ : syracuseStep 2606861 = 977573) (by norm_num)
theorem B15255317 : Blo 1736569 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B2606885 : Blo 1736569 2606885 := bbase (se 4 (by rfl) ⟨244395, by rfl⟩ : syracuseStep 2606885 = 488791) (by norm_num)
theorem B3909437 : Blo 1736569 3909437 := bbase (se 3 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 3909437 = 1466039) (by norm_num)
theorem B2606909 : Blo 1736569 2606909 := bbase (se 3 (by rfl) ⟨488795, by rfl⟩ : syracuseStep 2606909 = 977591) (by norm_num)
theorem B21137237 : Blo 1736569 21137237 := bbase (se 9 (by rfl) ⟨61925, by rfl⟩ : syracuseStep 21137237 = 123851) (by norm_num)
theorem B2606933 : Blo 1736569 2606933 := bbase (se 9 (by rfl) ⟨7637, by rfl⟩ : syracuseStep 2606933 = 15275) (by norm_num)
theorem B2606957 : Blo 1736569 2606957 := bbase (se 3 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 2606957 = 977609) (by norm_num)
theorem B11134837 : Blo 1736569 11134837 := bbase (se 5 (by rfl) ⟨521945, by rfl⟩ : syracuseStep 11134837 = 1043891) (by norm_num)
theorem B3909509 : Blo 1736569 3909509 := bbase (se 4 (by rfl) ⟨366516, by rfl⟩ : syracuseStep 3909509 = 733033) (by norm_num)
theorem B2606981 : Blo 1736569 2606981 := bbase (se 4 (by rfl) ⟨244404, by rfl⟩ : syracuseStep 2606981 = 488809) (by norm_num)
theorem B2607005 : Blo 1736569 2607005 := bbase (se 3 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 2607005 = 977627) (by norm_num)
theorem B2607029 : Blo 1736569 2607029 := bbase (se 5 (by rfl) ⟨122204, by rfl⟩ : syracuseStep 2607029 = 244409) (by norm_num)
theorem B3909581 : Blo 1736569 3909581 := bbase (se 3 (by rfl) ⟨733046, by rfl⟩ : syracuseStep 3909581 = 1466093) (by norm_num)
theorem B2607053 : Blo 1736569 2607053 := bbase (se 3 (by rfl) ⟨488822, by rfl⟩ : syracuseStep 2607053 = 977645) (by norm_num)
theorem B5867477 : Blo 1736569 5867477 := bbase (se 7 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 5867477 = 137519) (by norm_num)
theorem B2607077 : Blo 1736569 2607077 := bbase (se 4 (by rfl) ⟨244413, by rfl⟩ : syracuseStep 2607077 = 488827) (by norm_num)
theorem B2607101 : Blo 1736569 2607101 := bbase (se 3 (by rfl) ⟨488831, by rfl⟩ : syracuseStep 2607101 = 977663) (by norm_num)
theorem B3909653 : Blo 1736569 3909653 := bbase (se 6 (by rfl) ⟨91632, by rfl⟩ : syracuseStep 3909653 = 183265) (by norm_num)
theorem B2607125 : Blo 1736569 2607125 := bbase (se 6 (by rfl) ⟨61104, by rfl⟩ : syracuseStep 2607125 = 122209) (by norm_num)
theorem B2607149 : Blo 1736569 2607149 := bbase (se 3 (by rfl) ⟨488840, by rfl⟩ : syracuseStep 2607149 = 977681) (by norm_num)
theorem B4458557 : Blo 1736569 4458557 := bbase (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) (by norm_num)
theorem B2607173 : Blo 1736569 2607173 := bbase (se 4 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 2607173 = 488845) (by norm_num)
theorem B8800325 : Blo 1736569 8800325 := bbase (se 4 (by rfl) ⟨825030, by rfl⟩ : syracuseStep 8800325 = 1650061) (by norm_num)
theorem B3909725 : Blo 1736569 3909725 := bbase (se 3 (by rfl) ⟨733073, by rfl⟩ : syracuseStep 3909725 = 1466147) (by norm_num)
theorem B2607197 : Blo 1736569 2607197 := bbase (se 3 (by rfl) ⟨488849, by rfl⟩ : syracuseStep 2607197 = 977699) (by norm_num)
theorem B2607221 : Blo 1736569 2607221 := bbase (se 5 (by rfl) ⟨122213, by rfl⟩ : syracuseStep 2607221 = 244427) (by norm_num)
theorem B2607245 : Blo 1736569 2607245 := bbase (se 3 (by rfl) ⟨488858, by rfl⟩ : syracuseStep 2607245 = 977717) (by norm_num)
theorem B4696213 : Blo 1736569 4696213 := bbase (se 6 (by rfl) ⟨110067, by rfl⟩ : syracuseStep 4696213 = 220135) (by norm_num)
theorem B3909797 : Blo 1736569 3909797 := bbase (se 4 (by rfl) ⟨366543, by rfl⟩ : syracuseStep 3909797 = 733087) (by norm_num)
theorem B2607269 : Blo 1736569 2607269 := bbase (se 4 (by rfl) ⟨244431, by rfl⟩ : syracuseStep 2607269 = 488863) (by norm_num)
theorem B2607293 : Blo 1736569 2607293 := bbase (se 3 (by rfl) ⟨488867, by rfl⟩ : syracuseStep 2607293 = 977735) (by norm_num)
theorem B2607317 : Blo 1736569 2607317 := bbase (se 7 (by rfl) ⟨30554, by rfl⟩ : syracuseStep 2607317 = 61109) (by norm_num)
theorem B4950229 : Blo 1736569 4950229 := bbase (se 7 (by rfl) ⟨58010, by rfl⟩ : syracuseStep 4950229 = 116021) (by norm_num)
theorem B3811549 : Blo 1736569 3811549 := bbase (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) (by norm_num)
theorem B3909869 : Blo 1736569 3909869 := bbase (se 3 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 3909869 = 1466201) (by norm_num)
theorem B2607341 : Blo 1736569 2607341 := bbase (se 3 (by rfl) ⟨488876, by rfl⟩ : syracuseStep 2607341 = 977753) (by norm_num)
theorem B2607365 : Blo 1736569 2607365 := bbase (se 4 (by rfl) ⟨244440, by rfl⟩ : syracuseStep 2607365 = 488881) (by norm_num)
theorem B2607389 : Blo 1736569 2607389 := bbase (se 3 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 2607389 = 977771) (by norm_num)
theorem B3909941 : Blo 1736569 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B2607413 : Blo 1736569 2607413 := bbase (se 5 (by rfl) ⟨122222, by rfl⟩ : syracuseStep 2607413 = 244445) (by norm_num)
theorem B3131725 : Blo 1736569 3131725 := bbase (se 3 (by rfl) ⟨587198, by rfl⟩ : syracuseStep 3131725 = 1174397) (by norm_num)
theorem B3344717 : Blo 1736569 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B2607437 : Blo 1736569 2607437 := bbase (se 3 (by rfl) ⟨488894, by rfl⟩ : syracuseStep 2607437 = 977789) (by norm_num)
theorem B2197849 : Blo 1736569 2197849 := bbase (se 2 (by rfl) ⟨824193, by rfl⟩ : syracuseStep 2197849 = 1648387) (by norm_num)
theorem B2607461 : Blo 1736569 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B4950389 : Blo 1736569 4950389 := bbase (se 5 (by rfl) ⟨232049, by rfl⟩ : syracuseStep 4950389 = 464099) (by norm_num)
theorem B3910013 : Blo 1736569 3910013 := bbase (se 3 (by rfl) ⟨733127, by rfl⟩ : syracuseStep 3910013 = 1466255) (by norm_num)
theorem B2607485 : Blo 1736569 2607485 := bbase (se 3 (by rfl) ⟨488903, by rfl⟩ : syracuseStep 2607485 = 977807) (by norm_num)
theorem B2607509 : Blo 1736569 2607509 := bbase (se 6 (by rfl) ⟨61113, by rfl⟩ : syracuseStep 2607509 = 122227) (by norm_num)
theorem B2607533 : Blo 1736569 2607533 := bbase (se 3 (by rfl) ⟨488912, by rfl⟩ : syracuseStep 2607533 = 977825) (by norm_num)
theorem B2197945 : Blo 1736569 2197945 := bbase (se 2 (by rfl) ⟨824229, by rfl⟩ : syracuseStep 2197945 = 1648459) (by norm_num)
theorem B3910085 : Blo 1736569 3910085 := bbase (se 4 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 3910085 = 733141) (by norm_num)
theorem B2607557 : Blo 1736569 2607557 := bbase (se 4 (by rfl) ⟨244458, by rfl⟩ : syracuseStep 2607557 = 488917) (by norm_num)
theorem B2607581 : Blo 1736569 2607581 := bbase (se 3 (by rfl) ⟨488921, by rfl⟩ : syracuseStep 2607581 = 977843) (by norm_num)
theorem B8792549 : Blo 1736569 8792549 := bbase (se 4 (by rfl) ⟨824301, by rfl⟩ : syracuseStep 8792549 = 1648603) (by norm_num)
theorem B3303917 : Blo 1736569 3303917 := bbase (se 3 (by rfl) ⟨619484, by rfl⟩ : syracuseStep 3303917 = 1238969) (by norm_num)
theorem B2607605 : Blo 1736569 2607605 := bbase (se 5 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 2607605 = 244463) (by norm_num)
theorem B3910157 : Blo 1736569 3910157 := bbase (se 3 (by rfl) ⟨733154, by rfl⟩ : syracuseStep 3910157 = 1466309) (by norm_num)
theorem B2607629 : Blo 1736569 2607629 := bbase (se 3 (by rfl) ⟨488930, by rfl⟩ : syracuseStep 2607629 = 977861) (by norm_num)
theorem B2607653 : Blo 1736569 2607653 := bbase (se 4 (by rfl) ⟨244467, by rfl⟩ : syracuseStep 2607653 = 488935) (by norm_num)
theorem B2607677 : Blo 1736569 2607677 := bbase (se 3 (by rfl) ⟨488939, by rfl⟩ : syracuseStep 2607677 = 977879) (by norm_num)
theorem B3910229 : Blo 1736569 3910229 := bbase (se 8 (by rfl) ⟨22911, by rfl⟩ : syracuseStep 3910229 = 45823) (by norm_num)
theorem B2607701 : Blo 1736569 2607701 := bbase (se 8 (by rfl) ⟨15279, by rfl⟩ : syracuseStep 2607701 = 30559) (by norm_num)
theorem B2198117 : Blo 1736569 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B4950629 : Blo 1736569 4950629 := bbase (se 4 (by rfl) ⟨464121, by rfl⟩ : syracuseStep 4950629 = 928243) (by norm_num)
theorem B2607725 : Blo 1736569 2607725 := bbase (se 3 (by rfl) ⟨488948, by rfl⟩ : syracuseStep 2607725 = 977897) (by norm_num)
theorem B5565061 : Blo 1736569 5565061 := bbase (se 4 (by rfl) ⟨521724, by rfl⟩ : syracuseStep 5565061 = 1043449) (by norm_num)
theorem B2607749 : Blo 1736569 2607749 := bbase (se 4 (by rfl) ⟨244476, by rfl⟩ : syracuseStep 2607749 = 488953) (by norm_num)
theorem B2198173 : Blo 1736569 2198173 := bbase (se 3 (by rfl) ⟨412157, by rfl⟩ : syracuseStep 2198173 = 824315) (by norm_num)
theorem B3910301 : Blo 1736569 3910301 := bbase (se 3 (by rfl) ⟨733181, by rfl⟩ : syracuseStep 3910301 = 1466363) (by norm_num)
theorem B2607773 : Blo 1736569 2607773 := bbase (se 3 (by rfl) ⟨488957, by rfl⟩ : syracuseStep 2607773 = 977915) (by norm_num)
theorem B2607797 : Blo 1736569 2607797 := bbase (se 5 (by rfl) ⟨122240, by rfl⟩ : syracuseStep 2607797 = 244481) (by norm_num)
theorem B2607821 : Blo 1736569 2607821 := bbase (se 3 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 2607821 = 977933) (by norm_num)
theorem B3910373 : Blo 1736569 3910373 := bbase (se 4 (by rfl) ⟨366597, by rfl⟩ : syracuseStep 3910373 = 733195) (by norm_num)
theorem B2607845 : Blo 1736569 2607845 := bbase (se 4 (by rfl) ⟨244485, by rfl⟩ : syracuseStep 2607845 = 488971) (by norm_num)
theorem B2198269 : Blo 1736569 2198269 := bbase (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) (by norm_num)
theorem B19786517 : Blo 1736569 19786517 := bbase (se 6 (by rfl) ⟨463746, by rfl⟩ : syracuseStep 19786517 = 927493) (by norm_num)
theorem B4950821 : Blo 1736569 4950821 := bbase (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) (by norm_num)
theorem B3910445 : Blo 1736569 3910445 := bbase (se 3 (by rfl) ⟨733208, by rfl⟩ : syracuseStep 3910445 = 1466417) (by norm_num)
theorem B2640709 : Blo 1736569 2640709 := bbase (se 4 (by rfl) ⟨247566, by rfl⟩ : syracuseStep 2640709 = 495133) (by norm_num)
theorem B2640757 : Blo 1736569 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B3910517 : Blo 1736569 3910517 := bbase (se 5 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 3910517 = 366611) (by norm_num)
theorem B13200245 : Blo 1736569 13200245 := bbase (se 5 (by rfl) ⟨618761, by rfl⟩ : syracuseStep 13200245 = 1237523) (by norm_num)
theorem B2198441 : Blo 1736569 2198441 := bbase (se 2 (by rfl) ⟨824415, by rfl⟩ : syracuseStep 2198441 = 1648831) (by norm_num)
theorem B6597557 : Blo 1736569 6597557 := bbase (se 5 (by rfl) ⟨309260, by rfl⟩ : syracuseStep 6597557 = 618521) (by norm_num)
theorem B3910589 : Blo 1736569 3910589 := bbase (se 3 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 3910589 = 1466471) (by norm_num)
theorem B3132365 : Blo 1736569 3132365 := bbase (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) (by norm_num)
theorem B2198497 : Blo 1736569 2198497 := bbase (se 2 (by rfl) ⟨824436, by rfl⟩ : syracuseStep 2198497 = 1648873) (by norm_num)
theorem B4172789 : Blo 1736569 4172789 := bbase (se 5 (by rfl) ⟨195599, by rfl⟩ : syracuseStep 4172789 = 391199) (by norm_num)
theorem B3763189 : Blo 1736569 3763189 := bbase (se 5 (by rfl) ⟨176399, by rfl⟩ : syracuseStep 3763189 = 352799) (by norm_num)
theorem B3910661 : Blo 1736569 3910661 := bbase (se 4 (by rfl) ⟨366624, by rfl⟩ : syracuseStep 3910661 = 733249) (by norm_num)
theorem B2198593 : Blo 1736569 2198593 := bbase (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) (by norm_num)
theorem B3910733 : Blo 1736569 3910733 := bbase (se 3 (by rfl) ⟨733262, by rfl⟩ : syracuseStep 3910733 = 1466525) (by norm_num)
theorem B6261877 : Blo 1736569 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B3132533 : Blo 1736569 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B3910805 : Blo 1736569 3910805 := bbase (se 6 (by rfl) ⟨91659, by rfl⟩ : syracuseStep 3910805 = 183319) (by norm_num)
theorem B6597845 : Blo 1736569 6597845 := bbase (se 7 (by rfl) ⟨77318, by rfl⟩ : syracuseStep 6597845 = 154637) (by norm_num)
theorem B3910877 : Blo 1736569 3910877 := bbase (se 3 (by rfl) ⟨733289, by rfl⟩ : syracuseStep 3910877 = 1466579) (by norm_num)
theorem B2198765 : Blo 1736569 2198765 := bbase (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) (by norm_num)
theorem B13192469 : Blo 1736569 13192469 := bbase (se 6 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 13192469 = 618397) (by norm_num)
theorem B2198821 : Blo 1736569 2198821 := bbase (se 4 (by rfl) ⟨206139, by rfl⟩ : syracuseStep 2198821 = 412279) (by norm_num)
theorem B3910949 : Blo 1736569 3910949 := bbase (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) (by norm_num)
theorem B12520757 : Blo 1736569 12520757 := bbase (se 5 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 12520757 = 1173821) (by norm_num)
theorem B1854781 : Blo 1736569 1854781 := bbase (se 3 (by rfl) ⟨347771, by rfl⟩ : syracuseStep 1854781 = 695543) (by norm_num)
theorem B3911021 : Blo 1736569 3911021 := bbase (se 3 (by rfl) ⟨733316, by rfl⟩ : syracuseStep 3911021 = 1466633) (by norm_num)
theorem B4173173 : Blo 1736569 4173173 := bbase (se 5 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 4173173 = 391235) (by norm_num)
theorem B2198917 : Blo 1736569 2198917 := bbase (se 4 (by rfl) ⟨206148, by rfl⟩ : syracuseStep 2198917 = 412297) (by norm_num)
theorem B1854901 : Blo 1736569 1854901 := bbase (se 5 (by rfl) ⟨86948, by rfl⟩ : syracuseStep 1854901 = 173897) (by norm_num)
theorem B3911093 : Blo 1736569 3911093 := bbase (se 5 (by rfl) ⟨183332, by rfl⟩ : syracuseStep 3911093 = 366665) (by norm_num)
theorem B3911165 : Blo 1736569 3911165 := bbase (se 3 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 3911165 = 1466687) (by norm_num)
theorem B2199089 : Blo 1736569 2199089 := bbase (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) (by norm_num)
theorem B4173373 : Blo 1736569 4173373 := bbase (se 3 (by rfl) ⟨782507, by rfl⟩ : syracuseStep 4173373 = 1565015) (by norm_num)
theorem B3911237 : Blo 1736569 3911237 := bbase (se 4 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 3911237 = 733357) (by norm_num)
theorem B2199145 : Blo 1736569 2199145 := bbase (se 2 (by rfl) ⟨824679, by rfl⟩ : syracuseStep 2199145 = 1649359) (by norm_num)
theorem B5860997 : Blo 1736569 5860997 := bbase (se 4 (by rfl) ⟨549468, by rfl⟩ : syracuseStep 5860997 = 1098937) (by norm_num)
theorem B3911309 : Blo 1736569 3911309 := bbase (se 3 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 3911309 = 1466741) (by norm_num)
theorem B7425685 : Blo 1736569 7425685 := bbase (se 6 (by rfl) ⟨174039, by rfl⟩ : syracuseStep 7425685 = 348079) (by norm_num)
theorem B3296933 : Blo 1736569 3296933 := bbase (se 4 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 3296933 = 618175) (by norm_num)
theorem B1855153 : Blo 1736569 1855153 := bbase (se 2 (by rfl) ⟨695682, by rfl⟩ : syracuseStep 1855153 = 1391365) (by norm_num)
theorem B1855157 : Blo 1736569 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B2199241 : Blo 1736569 2199241 := bbase (se 2 (by rfl) ⟨824715, by rfl⟩ : syracuseStep 2199241 = 1649431) (by norm_num)
theorem B3911381 : Blo 1736569 3911381 := bbase (se 7 (by rfl) ⟨45836, by rfl⟩ : syracuseStep 3911381 = 91673) (by norm_num)
theorem B8793845 : Blo 1736569 8793845 := bbase (se 5 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 8793845 = 824423) (by norm_num)
theorem B3911453 : Blo 1736569 3911453 := bbase (se 3 (by rfl) ⟨733397, by rfl⟩ : syracuseStep 3911453 = 1466795) (by norm_num)
theorem B3911525 : Blo 1736569 3911525 := bbase (se 4 (by rfl) ⟨366705, by rfl⟩ : syracuseStep 3911525 = 733411) (by norm_num)
theorem B2199413 : Blo 1736569 2199413 := bbase (se 5 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 2199413 = 206195) (by norm_num)
theorem B1953661 : Blo 1736569 1953661 := bbase (se 3 (by rfl) ⟨366311, by rfl⟩ : syracuseStep 1953661 = 732623) (by norm_num)
theorem B1953697 : Blo 1736569 1953697 := bbase (se 2 (by rfl) ⟨732636, by rfl⟩ : syracuseStep 1953697 = 1465273) (by norm_num)
theorem B2199469 : Blo 1736569 2199469 := bbase (se 3 (by rfl) ⟨412400, by rfl⟩ : syracuseStep 2199469 = 824801) (by norm_num)
theorem B3911597 : Blo 1736569 3911597 := bbase (se 3 (by rfl) ⟨733424, by rfl⟩ : syracuseStep 3911597 = 1466849) (by norm_num)
theorem B1953733 : Blo 1736569 1953733 := bbase (se 4 (by rfl) ⟨183162, by rfl⟩ : syracuseStep 1953733 = 366325) (by norm_num)
theorem B4698053 : Blo 1736569 4698053 := bbase (se 4 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 4698053 = 880885) (by norm_num)
theorem B5566421 : Blo 1736569 5566421 := bbase (se 7 (by rfl) ⟨65231, by rfl⟩ : syracuseStep 5566421 = 130463) (by norm_num)
theorem B1953769 : Blo 1736569 1953769 := bbase (se 2 (by rfl) ⟨732663, by rfl⟩ : syracuseStep 1953769 = 1465327) (by norm_num)
theorem B3911669 : Blo 1736569 3911669 := bbase (se 5 (by rfl) ⟨183359, by rfl⟩ : syracuseStep 3911669 = 366719) (by norm_num)
theorem B1953805 : Blo 1736569 1953805 := bbase (se 3 (by rfl) ⟨366338, by rfl⟩ : syracuseStep 1953805 = 732677) (by norm_num)
theorem B2199565 : Blo 1736569 2199565 := bbase (se 3 (by rfl) ⟨412418, by rfl⟩ : syracuseStep 2199565 = 824837) (by norm_num)
theorem B1953841 : Blo 1736569 1953841 := bbase (se 2 (by rfl) ⟨732690, by rfl⟩ : syracuseStep 1953841 = 1465381) (by norm_num)
theorem B7041077 : Blo 1736569 7041077 := bbase (se 5 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 7041077 = 660101) (by norm_num)
theorem B5861429 : Blo 1736569 5861429 := bbase (se 5 (by rfl) ⟨274754, by rfl⟩ : syracuseStep 5861429 = 549509) (by norm_num)
theorem B2347069 : Blo 1736569 2347069 := bbase (se 3 (by rfl) ⟨440075, by rfl⟩ : syracuseStep 2347069 = 880151) (by norm_num)
theorem B3911741 : Blo 1736569 3911741 := bbase (se 3 (by rfl) ⟨733451, by rfl⟩ : syracuseStep 3911741 = 1466903) (by norm_num)
theorem B1953877 : Blo 1736569 1953877 := bbase (se 8 (by rfl) ⟨11448, by rfl⟩ : syracuseStep 1953877 = 22897) (by norm_num)
theorem B1953913 : Blo 1736569 1953913 := bbase (se 2 (by rfl) ⟨732717, by rfl⟩ : syracuseStep 1953913 = 1465435) (by norm_num)
theorem B1953949 : Blo 1736569 1953949 := bbase (se 3 (by rfl) ⟨366365, by rfl⟩ : syracuseStep 1953949 = 732731) (by norm_num)
theorem B2199737 : Blo 1736569 2199737 := bbase (se 2 (by rfl) ⟨824901, by rfl⟩ : syracuseStep 2199737 = 1649803) (by norm_num)
theorem B1953985 : Blo 1736569 1953985 := bbase (se 2 (by rfl) ⟨732744, by rfl⟩ : syracuseStep 1953985 = 1465489) (by norm_num)
theorem B1954021 : Blo 1736569 1954021 := bbase (se 4 (by rfl) ⟨183189, by rfl⟩ : syracuseStep 1954021 = 366379) (by norm_num)
theorem B1855721 : Blo 1736569 1855721 := bbase (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) (by norm_num)
theorem B2199793 : Blo 1736569 2199793 := bbase (se 2 (by rfl) ⟨824922, by rfl⟩ : syracuseStep 2199793 = 1649845) (by norm_num)
theorem B1954057 : Blo 1736569 1954057 := bbase (se 2 (by rfl) ⟨732771, by rfl⟩ : syracuseStep 1954057 = 1465543) (by norm_num)
theorem B1954093 : Blo 1736569 1954093 := bbase (se 3 (by rfl) ⟨366392, by rfl⟩ : syracuseStep 1954093 = 732785) (by norm_num)
theorem B1954129 : Blo 1736569 1954129 := bbase (se 2 (by rfl) ⟨732798, by rfl⟩ : syracuseStep 1954129 = 1465597) (by norm_num)
theorem B2199889 : Blo 1736569 2199889 := bbase (se 2 (by rfl) ⟨824958, by rfl⟩ : syracuseStep 2199889 = 1649917) (by norm_num)
theorem B9163109 : Blo 1736569 9163109 := bbase (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) (by norm_num)
theorem B1954165 : Blo 1736569 1954165 := bbase (se 5 (by rfl) ⟨91601, by rfl⟩ : syracuseStep 1954165 = 183203) (by norm_num)
theorem B6599029 : Blo 1736569 6599029 := bbase (se 5 (by rfl) ⟨309329, by rfl⟩ : syracuseStep 6599029 = 618659) (by norm_num)
theorem B3297685 : Blo 1736569 3297685 := bbase (se 6 (by rfl) ⟨77289, by rfl⟩ : syracuseStep 3297685 = 154579) (by norm_num)
theorem B1954201 : Blo 1736569 1954201 := bbase (se 2 (by rfl) ⟨732825, by rfl⟩ : syracuseStep 1954201 = 1465651) (by norm_num)
theorem B1855909 : Blo 1736569 1855909 := bbase (se 4 (by rfl) ⟨173991, by rfl⟩ : syracuseStep 1855909 = 347983) (by norm_num)
theorem B1954237 : Blo 1736569 1954237 := bbase (se 3 (by rfl) ⟨366419, by rfl⟩ : syracuseStep 1954237 = 732839) (by norm_num)
theorem B1954273 : Blo 1736569 1954273 := bbase (se 2 (by rfl) ⟨732852, by rfl⟩ : syracuseStep 1954273 = 1465705) (by norm_num)
theorem B5861861 : Blo 1736569 5861861 := bbase (se 4 (by rfl) ⟨549549, by rfl⟩ : syracuseStep 5861861 = 1099099) (by norm_num)
theorem B2200061 : Blo 1736569 2200061 := bbase (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) (by norm_num)
theorem B1954309 : Blo 1736569 1954309 := bbase (se 4 (by rfl) ⟨183216, by rfl⟩ : syracuseStep 1954309 = 366433) (by norm_num)
theorem B3297829 : Blo 1736569 3297829 := bbase (se 4 (by rfl) ⟨309171, by rfl⟩ : syracuseStep 3297829 = 618343) (by norm_num)
theorem B1954345 : Blo 1736569 1954345 := bbase (se 2 (by rfl) ⟨732879, by rfl⟩ : syracuseStep 1954345 = 1465759) (by norm_num)
theorem B2200117 : Blo 1736569 2200117 := bbase (se 5 (by rfl) ⟨103130, by rfl⟩ : syracuseStep 2200117 = 206261) (by norm_num)
theorem B1880641 : Blo 1736569 1880641 := bbase (se 2 (by rfl) ⟨705240, by rfl⟩ : syracuseStep 1880641 = 1410481) (by norm_num)
theorem B1954381 : Blo 1736569 1954381 := bbase (se 3 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 1954381 = 732893) (by norm_num)
theorem B1954417 : Blo 1736569 1954417 := bbase (se 2 (by rfl) ⟨732906, by rfl⟩ : syracuseStep 1954417 = 1465813) (by norm_num)
theorem B1954453 : Blo 1736569 1954453 := bbase (se 6 (by rfl) ⟨45807, by rfl⟩ : syracuseStep 1954453 = 91615) (by norm_num)
theorem B2200213 : Blo 1736569 2200213 := bbase (se 6 (by rfl) ⟨51567, by rfl⟩ : syracuseStep 2200213 = 103135) (by norm_num)
theorem B6599333 : Blo 1736569 6599333 := bbase (se 4 (by rfl) ⟨618687, by rfl⟩ : syracuseStep 6599333 = 1237375) (by norm_num)
theorem B1954489 : Blo 1736569 1954489 := bbase (se 2 (by rfl) ⟨732933, by rfl⟩ : syracuseStep 1954489 = 1465867) (by norm_num)
theorem B3297989 : Blo 1736569 3297989 := bbase (se 4 (by rfl) ⟨309186, by rfl⟩ : syracuseStep 3297989 = 618373) (by norm_num)
theorem B1954525 : Blo 1736569 1954525 := bbase (se 3 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 1954525 = 732947) (by norm_num)
theorem B1954561 : Blo 1736569 1954561 := bbase (se 2 (by rfl) ⟨732960, by rfl⟩ : syracuseStep 1954561 = 1465921) (by norm_num)
theorem B6689557 : Blo 1736569 6689557 := bbase (se 6 (by rfl) ⟨156786, by rfl⟩ : syracuseStep 6689557 = 313573) (by norm_num)
theorem B1954597 : Blo 1736569 1954597 := bbase (se 4 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 1954597 = 366487) (by norm_num)
theorem B4395829 : Blo 1736569 4395829 := bbase (se 5 (by rfl) ⟨206054, by rfl⟩ : syracuseStep 4395829 = 412109) (by norm_num)
theorem B1954633 : Blo 1736569 1954633 := bbase (se 2 (by rfl) ⟨732987, by rfl⟩ : syracuseStep 1954633 = 1465975) (by norm_num)
theorem B3298133 : Blo 1736569 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B1954669 : Blo 1736569 1954669 := bbase (se 3 (by rfl) ⟨366500, by rfl⟩ : syracuseStep 1954669 = 733001) (by norm_num)
theorem B2782069 : Blo 1736569 2782069 := bbase (se 5 (by rfl) ⟨130409, by rfl⟩ : syracuseStep 2782069 = 260819) (by norm_num)
theorem B5641093 : Blo 1736569 5641093 := bbase (se 4 (by rfl) ⟨528852, by rfl⟩ : syracuseStep 5641093 = 1057705) (by norm_num)
theorem B1954705 : Blo 1736569 1954705 := bbase (se 2 (by rfl) ⟨733014, by rfl⟩ : syracuseStep 1954705 = 1466029) (by norm_num)
theorem B5862293 : Blo 1736569 5862293 := bbase (se 6 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 5862293 = 274795) (by norm_num)
theorem B4395941 : Blo 1736569 4395941 := bbase (se 4 (by rfl) ⟨412119, by rfl⟩ : syracuseStep 4395941 = 824239) (by norm_num)
theorem B1954741 : Blo 1736569 1954741 := bbase (se 5 (by rfl) ⟨91628, by rfl⟩ : syracuseStep 1954741 = 183257) (by norm_num)
theorem B27128789 : Blo 1736569 27128789 := bbase (se 7 (by rfl) ⟨317915, by rfl⟩ : syracuseStep 27128789 = 635831) (by norm_num)
theorem B1954777 : Blo 1736569 1954777 := bbase (se 2 (by rfl) ⟨733041, by rfl⟩ : syracuseStep 1954777 = 1466083) (by norm_num)
theorem B1954813 : Blo 1736569 1954813 := bbase (se 3 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 1954813 = 733055) (by norm_num)
theorem B8795141 : Blo 1736569 8795141 := bbase (se 4 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 8795141 = 1649089) (by norm_num)
theorem B1954849 : Blo 1736569 1954849 := bbase (se 2 (by rfl) ⟨733068, by rfl⟩ : syracuseStep 1954849 = 1466137) (by norm_num)
theorem B8352821 : Blo 1736569 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B1954885 : Blo 1736569 1954885 := bbase (se 4 (by rfl) ⟨183270, by rfl⟩ : syracuseStep 1954885 = 366541) (by norm_num)
theorem B4396133 : Blo 1736569 4396133 := bbase (se 4 (by rfl) ⟨412137, by rfl⟩ : syracuseStep 4396133 = 824275) (by norm_num)
theorem B4174949 : Blo 1736569 4174949 := bbase (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) (by norm_num)
theorem B1954921 : Blo 1736569 1954921 := bbase (se 2 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 1954921 = 1466191) (by norm_num)
theorem B3298421 : Blo 1736569 3298421 := bbase (se 5 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 3298421 = 309227) (by norm_num)
theorem B1954957 : Blo 1736569 1954957 := bbase (se 3 (by rfl) ⟨366554, by rfl⟩ : syracuseStep 1954957 = 733109) (by norm_num)
theorem B3962029 : Blo 1736569 3962029 := bbase (se 3 (by rfl) ⟨742880, by rfl⟩ : syracuseStep 3962029 = 1485761) (by norm_num)
theorem B1954993 : Blo 1736569 1954993 := bbase (se 2 (by rfl) ⟨733122, by rfl⟩ : syracuseStep 1954993 = 1466245) (by norm_num)
theorem B23778517 : Blo 1736569 23778517 := bbase (se 7 (by rfl) ⟨278654, by rfl⟩ : syracuseStep 23778517 = 557309) (by norm_num)
theorem B1955029 : Blo 1736569 1955029 := bbase (se 7 (by rfl) ⟨22910, by rfl⟩ : syracuseStep 1955029 = 45821) (by norm_num)
theorem B7042277 : Blo 1736569 7042277 := bbase (se 4 (by rfl) ⟨660213, by rfl⟩ : syracuseStep 7042277 = 1320427) (by norm_num)
theorem B1955065 : Blo 1736569 1955065 := bbase (se 2 (by rfl) ⟨733149, by rfl⟩ : syracuseStep 1955065 = 1466299) (by norm_num)
theorem B3298573 : Blo 1736569 3298573 := bbase (se 3 (by rfl) ⟨618482, by rfl⟩ : syracuseStep 3298573 = 1236965) (by norm_num)
theorem B1955101 : Blo 1736569 1955101 := bbase (se 3 (by rfl) ⟨366581, by rfl⟩ : syracuseStep 1955101 = 733163) (by norm_num)
theorem B2782525 : Blo 1736569 2782525 := bbase (se 3 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 2782525 = 1043447) (by norm_num)
theorem B1955137 : Blo 1736569 1955137 := bbase (se 2 (by rfl) ⟨733176, by rfl⟩ : syracuseStep 1955137 = 1466353) (by norm_num)
theorem B5862725 : Blo 1736569 5862725 := bbase (se 4 (by rfl) ⟨549630, by rfl⟩ : syracuseStep 5862725 = 1099261) (by norm_num)
theorem B1955173 : Blo 1736569 1955173 := bbase (se 4 (by rfl) ⟨183297, by rfl⟩ : syracuseStep 1955173 = 366595) (by norm_num)
theorem B1955209 : Blo 1736569 1955209 := bbase (se 2 (by rfl) ⟨733203, by rfl⟩ : syracuseStep 1955209 = 1466407) (by norm_num)
theorem B2348453 : Blo 1736569 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B1955245 : Blo 1736569 1955245 := bbase (se 3 (by rfl) ⟨366608, by rfl⟩ : syracuseStep 1955245 = 733217) (by norm_num)
theorem B1881517 : Blo 1736569 1881517 := bbase (se 3 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 1881517 = 705569) (by norm_num)
theorem B4396477 : Blo 1736569 4396477 := bbase (se 3 (by rfl) ⟨824339, by rfl⟩ : syracuseStep 4396477 = 1648679) (by norm_num)
theorem B1955281 : Blo 1736569 1955281 := bbase (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) (by norm_num)
theorem B1955317 : Blo 1736569 1955317 := bbase (se 5 (by rfl) ⟨91655, by rfl⟩ : syracuseStep 1955317 = 183311) (by norm_num)
theorem B1955353 : Blo 1736569 1955353 := bbase (se 2 (by rfl) ⟨733257, by rfl⟩ : syracuseStep 1955353 = 1466515) (by norm_num)
theorem B4945445 : Blo 1736569 4945445 := bbase (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) (by norm_num)
theorem B4396589 : Blo 1736569 4396589 := bbase (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) (by norm_num)
theorem B3298877 : Blo 1736569 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B1955389 : Blo 1736569 1955389 := bbase (se 3 (by rfl) ⟨366635, by rfl⟩ : syracuseStep 1955389 = 733271) (by norm_num)
theorem B1955425 : Blo 1736569 1955425 := bbase (se 2 (by rfl) ⟨733284, by rfl⟩ : syracuseStep 1955425 = 1466569) (by norm_num)
theorem B1955461 : Blo 1736569 1955461 := bbase (se 4 (by rfl) ⟨183324, by rfl⟩ : syracuseStep 1955461 = 366649) (by norm_num)
theorem B1955497 : Blo 1736569 1955497 := bbase (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) (by norm_num)
theorem B8345285 : Blo 1736569 8345285 := bbase (se 4 (by rfl) ⟨782370, by rfl⟩ : syracuseStep 8345285 = 1564741) (by norm_num)
theorem B1955533 : Blo 1736569 1955533 := bbase (se 3 (by rfl) ⟨366662, by rfl⟩ : syracuseStep 1955533 = 733325) (by norm_num)
theorem B4396781 : Blo 1736569 4396781 := bbase (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) (by norm_num)
theorem B1955569 : Blo 1736569 1955569 := bbase (se 2 (by rfl) ⟨733338, by rfl⟩ : syracuseStep 1955569 = 1466677) (by norm_num)
theorem B5863157 : Blo 1736569 5863157 := bbase (se 5 (by rfl) ⟨274835, by rfl⟩ : syracuseStep 5863157 = 549671) (by norm_num)
theorem B12048149 : Blo 1736569 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B1955605 : Blo 1736569 1955605 := bbase (se 6 (by rfl) ⟨45834, by rfl⟩ : syracuseStep 1955605 = 91669) (by norm_num)
theorem B2930485 : Blo 1736569 2930485 := bbase (se 5 (by rfl) ⟨137366, by rfl⟩ : syracuseStep 2930485 = 274733) (by norm_num)
theorem B1955641 : Blo 1736569 1955641 := bbase (se 2 (by rfl) ⟨733365, by rfl⟩ : syracuseStep 1955641 = 1466731) (by norm_num)
theorem B1955677 : Blo 1736569 1955677 := bbase (se 3 (by rfl) ⟨366689, by rfl⟩ : syracuseStep 1955677 = 733379) (by norm_num)
theorem B1955713 : Blo 1736569 1955713 := bbase (se 2 (by rfl) ⟨733392, by rfl⟩ : syracuseStep 1955713 = 1466785) (by norm_num)
theorem B2930573 : Blo 1736569 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B1955749 : Blo 1736569 1955749 := bbase (se 4 (by rfl) ⟨183351, by rfl⟩ : syracuseStep 1955749 = 366703) (by norm_num)
theorem B1955785 : Blo 1736569 1955785 := bbase (se 2 (by rfl) ⟨733419, by rfl⟩ : syracuseStep 1955785 = 1466839) (by norm_num)
theorem B2783197 : Blo 1736569 2783197 := bbase (se 3 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 2783197 = 1043699) (by norm_num)
theorem B1955821 : Blo 1736569 1955821 := bbase (se 3 (by rfl) ⟨366716, by rfl⟩ : syracuseStep 1955821 = 733433) (by norm_num)
theorem B2930701 : Blo 1736569 2930701 := bbase (se 3 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 2930701 = 1099013) (by norm_num)
theorem B1955857 : Blo 1736569 1955857 := bbase (se 2 (by rfl) ⟨733446, by rfl⟩ : syracuseStep 1955857 = 1466893) (by norm_num)
theorem B29677589 : Blo 1736569 29677589 := bbase (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) (by norm_num)
theorem B3708965 : Blo 1736569 3708965 := bbase (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) (by norm_num)
theorem B4397125 : Blo 1736569 4397125 := bbase (se 4 (by rfl) ⟨412230, by rfl⟩ : syracuseStep 4397125 = 824461) (by norm_num)
theorem B2086985 : Blo 1736569 2086985 := bbase (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) (by norm_num)
theorem B2930789 : Blo 1736569 2930789 := bbase (se 4 (by rfl) ⟨274761, by rfl⟩ : syracuseStep 2930789 = 549523) (by norm_num)
theorem B5863589 : Blo 1736569 5863589 := bbase (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) (by norm_num)
theorem B4397237 : Blo 1736569 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B2349253 : Blo 1736569 2349253 := bbase (se 4 (by rfl) ⟨220242, by rfl⟩ : syracuseStep 2349253 = 440485) (by norm_num)
theorem B15849685 : Blo 1736569 15849685 := bbase (se 7 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 15849685 = 371477) (by norm_num)
theorem B2930917 : Blo 1736569 2930917 := bbase (se 4 (by rfl) ⟨274773, by rfl⟩ : syracuseStep 2930917 = 549547) (by norm_num)
theorem B4946197 : Blo 1736569 4946197 := bbase (se 6 (by rfl) ⟨115926, by rfl⟩ : syracuseStep 4946197 = 231853) (by norm_num)
theorem B8796437 : Blo 1736569 8796437 := bbase (se 6 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 8796437 = 412333) (by norm_num)
theorem B3299629 : Blo 1736569 3299629 := bbase (se 3 (by rfl) ⟨618680, by rfl⟩ : syracuseStep 3299629 = 1237361) (by norm_num)
theorem B2931005 : Blo 1736569 2931005 := bbase (se 3 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 2931005 = 1099127) (by norm_num)
theorem B4397429 : Blo 1736569 4397429 := bbase (se 5 (by rfl) ⟨206129, by rfl⟩ : syracuseStep 4397429 = 412259) (by norm_num)
theorem B2783621 : Blo 1736569 2783621 := bbase (se 4 (by rfl) ⟨260964, by rfl⟩ : syracuseStep 2783621 = 521929) (by norm_num)
theorem B2087317 : Blo 1736569 2087317 := bbase (se 6 (by rfl) ⟨48921, by rfl⟩ : syracuseStep 2087317 = 97843) (by norm_num)
theorem B8346037 : Blo 1736569 8346037 := bbase (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) (by norm_num)
theorem B2931133 : Blo 1736569 2931133 := bbase (se 3 (by rfl) ⟨549587, by rfl⟩ : syracuseStep 2931133 = 1099175) (by norm_num)
theorem B3299773 : Blo 1736569 3299773 := bbase (se 3 (by rfl) ⟨618707, by rfl⟩ : syracuseStep 3299773 = 1237415) (by norm_num)
theorem B5282293 : Blo 1736569 5282293 := bbase (se 5 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 5282293 = 495215) (by norm_num)
theorem B4176373 : Blo 1736569 4176373 := bbase (se 5 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 4176373 = 391535) (by norm_num)
theorem B4233725 : Blo 1736569 4233725 := bbase (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) (by norm_num)
theorem B2931221 : Blo 1736569 2931221 := bbase (se 6 (by rfl) ⟨68700, by rfl⟩ : syracuseStep 2931221 = 137401) (by norm_num)
theorem B5864021 : Blo 1736569 5864021 := bbase (se 8 (by rfl) ⟨34359, by rfl⟩ : syracuseStep 5864021 = 68719) (by norm_num)
theorem B3299933 : Blo 1736569 3299933 := bbase (se 3 (by rfl) ⟨618737, by rfl⟩ : syracuseStep 3299933 = 1237475) (by norm_num)
theorem B2931349 : Blo 1736569 2931349 := bbase (se 6 (by rfl) ⟨68703, by rfl⟩ : syracuseStep 2931349 = 137407) (by norm_num)
theorem B3709597 : Blo 1736569 3709597 := bbase (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) (by norm_num)
theorem B2783909 : Blo 1736569 2783909 := bbase (se 4 (by rfl) ⟨260991, by rfl⟩ : syracuseStep 2783909 = 521983) (by norm_num)
theorem B9894581 : Blo 1736569 9894581 := bbase (se 5 (by rfl) ⟨463808, by rfl⟩ : syracuseStep 9894581 = 927617) (by norm_num)
theorem B4397773 : Blo 1736569 4397773 := bbase (se 3 (by rfl) ⟨824582, by rfl⟩ : syracuseStep 4397773 = 1649165) (by norm_num)
theorem B3390157 : Blo 1736569 3390157 := bbase (se 3 (by rfl) ⟨635654, by rfl⟩ : syracuseStep 3390157 = 1271309) (by norm_num)
theorem B2931437 : Blo 1736569 2931437 := bbase (se 3 (by rfl) ⟨549644, by rfl⟩ : syracuseStep 2931437 = 1099289) (by norm_num)
theorem B3300077 : Blo 1736569 3300077 := bbase (se 3 (by rfl) ⟨618764, by rfl⟩ : syracuseStep 3300077 = 1237529) (by norm_num)
theorem B4397885 : Blo 1736569 4397885 := bbase (se 3 (by rfl) ⟨824603, by rfl⟩ : syracuseStep 4397885 = 1649207) (by norm_num)
theorem B2931565 : Blo 1736569 2931565 := bbase (se 3 (by rfl) ⟨549668, by rfl⟩ : syracuseStep 2931565 = 1099337) (by norm_num)
theorem B2931653 : Blo 1736569 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B7527397 : Blo 1736569 7527397 := bbase (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) (by norm_num)
theorem B16694261 : Blo 1736569 16694261 := bbase (se 5 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 16694261 = 1565087) (by norm_num)
theorem B4398077 : Blo 1736569 4398077 := bbase (se 3 (by rfl) ⟨824639, by rfl⟩ : syracuseStep 4398077 = 1649279) (by norm_num)
theorem B5864453 : Blo 1736569 5864453 := bbase (se 4 (by rfl) ⟨549792, by rfl⟩ : syracuseStep 5864453 = 1099585) (by norm_num)
theorem B3300365 : Blo 1736569 3300365 := bbase (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) (by norm_num)
theorem B2931781 : Blo 1736569 2931781 := bbase (se 4 (by rfl) ⟨274854, by rfl⟩ : syracuseStep 2931781 = 549709) (by norm_num)
theorem B2088013 : Blo 1736569 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B2088061 : Blo 1736569 2088061 := bbase (se 3 (by rfl) ⟨391511, by rfl⟩ : syracuseStep 2088061 = 783023) (by norm_num)
theorem B3013757 : Blo 1736569 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B6593669 : Blo 1736569 6593669 := bbase (se 4 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 6593669 = 1236313) (by norm_num)
theorem B4177045 : Blo 1736569 4177045 := bbase (se 6 (by rfl) ⟨97899, by rfl⟩ : syracuseStep 4177045 = 195799) (by norm_num)
theorem B2931869 : Blo 1736569 2931869 := bbase (se 3 (by rfl) ⟨549725, by rfl⟩ : syracuseStep 2931869 = 1099451) (by norm_num)
theorem B3300517 : Blo 1736569 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B2931997 : Blo 1736569 2931997 := bbase (se 3 (by rfl) ⟨549749, by rfl⟩ : syracuseStep 2931997 = 1099499) (by norm_num)
theorem B4398421 : Blo 1736569 4398421 := bbase (se 11 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 4398421 = 6443) (by norm_num)
theorem B2932085 : Blo 1736569 2932085 := bbase (se 5 (by rfl) ⟨137441, by rfl⟩ : syracuseStep 2932085 = 274883) (by norm_num)
theorem B15859061 : Blo 1736569 15859061 := bbase (se 5 (by rfl) ⟨743393, by rfl⟩ : syracuseStep 15859061 = 1486787) (by norm_num)
theorem B4177277 : Blo 1736569 4177277 := bbase (se 3 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 4177277 = 1566479) (by norm_num)
theorem B6593957 : Blo 1736569 6593957 := bbase (se 4 (by rfl) ⟨618183, by rfl⟩ : syracuseStep 6593957 = 1236367) (by norm_num)
theorem B5864885 : Blo 1736569 5864885 := bbase (se 5 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 5864885 = 549833) (by norm_num)
theorem B7421381 : Blo 1736569 7421381 := bbase (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) (by norm_num)
theorem B4398533 : Blo 1736569 4398533 := bbase (se 4 (by rfl) ⟨412362, by rfl⟩ : syracuseStep 4398533 = 824725) (by norm_num)
theorem B2784709 : Blo 1736569 2784709 := bbase (se 4 (by rfl) ⟨261066, by rfl⟩ : syracuseStep 2784709 = 522133) (by norm_num)
theorem B2473429 : Blo 1736569 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B2932213 : Blo 1736569 2932213 := bbase (se 5 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 2932213 = 274895) (by norm_num)
theorem B3710485 : Blo 1736569 3710485 := bbase (se 6 (by rfl) ⟨86964, by rfl⟩ : syracuseStep 3710485 = 173929) (by norm_num)
theorem B8797733 : Blo 1736569 8797733 := bbase (se 4 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 8797733 = 1649575) (by norm_num)
theorem B2932301 : Blo 1736569 2932301 := bbase (se 3 (by rfl) ⟨549806, by rfl⟩ : syracuseStep 2932301 = 1099613) (by norm_num)
theorem B4398725 : Blo 1736569 4398725 := bbase (se 4 (by rfl) ⟨412380, by rfl⟩ : syracuseStep 4398725 = 824761) (by norm_num)
theorem B3710605 : Blo 1736569 3710605 := bbase (se 3 (by rfl) ⟨695738, by rfl⟩ : syracuseStep 3710605 = 1391477) (by norm_num)
theorem B20332181 : Blo 1736569 20332181 := bbase (se 6 (by rfl) ⟨476535, by rfl⟩ : syracuseStep 20332181 = 953071) (by norm_num)
theorem B4456093 : Blo 1736569 4456093 := bbase (se 3 (by rfl) ⟨835517, by rfl⟩ : syracuseStep 4456093 = 1671035) (by norm_num)
theorem B12689077 : Blo 1736569 12689077 := bbase (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) (by norm_num)
theorem B2932429 : Blo 1736569 2932429 := bbase (se 3 (by rfl) ⟨549830, by rfl⟩ : syracuseStep 2932429 = 1099661) (by norm_num)
theorem B3907349 : Blo 1736569 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B17841941 : Blo 1736569 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B2932517 : Blo 1736569 2932517 := bbase (se 4 (by rfl) ⟨274923, by rfl⟩ : syracuseStep 2932517 = 549847) (by norm_num)
theorem B2604869 : Blo 1736569 2604869 := bbase (se 4 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 2604869 = 488413) (by norm_num)
theorem B2604893 : Blo 1736569 2604893 := bbase (se 3 (by rfl) ⟨488417, by rfl⟩ : syracuseStep 2604893 = 976835) (by norm_num)
theorem B3907421 : Blo 1736569 3907421 := bbase (se 3 (by rfl) ⟨732641, by rfl⟩ : syracuseStep 3907421 = 1465283) (by norm_num)
theorem B5865317 : Blo 1736569 5865317 := bbase (se 4 (by rfl) ⟨549873, by rfl⟩ : syracuseStep 5865317 = 1099747) (by norm_num)
theorem B2604917 : Blo 1736569 2604917 := bbase (se 5 (by rfl) ⟨122105, by rfl⟩ : syracuseStep 2604917 = 244211) (by norm_num)
theorem B1761161 : Blo 1736569 1761161 := bbase (se 2 (by rfl) ⟨660435, by rfl⟩ : syracuseStep 1761161 = 1320871) (by norm_num)
theorem B2604941 : Blo 1736569 2604941 := bbase (se 3 (by rfl) ⟨488426, by rfl⟩ : syracuseStep 2604941 = 976853) (by norm_num)
theorem B3710861 : Blo 1736569 3710861 := bbase (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) (by norm_num)
theorem B2604965 : Blo 1736569 2604965 := bbase (se 4 (by rfl) ⟨244215, by rfl⟩ : syracuseStep 2604965 = 488431) (by norm_num)
theorem B3907493 : Blo 1736569 3907493 := bbase (se 4 (by rfl) ⟨366327, by rfl⟩ : syracuseStep 3907493 = 732655) (by norm_num)
theorem B2932645 : Blo 1736569 2932645 := bbase (se 4 (by rfl) ⟨274935, by rfl⟩ : syracuseStep 2932645 = 549871) (by norm_num)
theorem B2604989 : Blo 1736569 2604989 := bbase (se 3 (by rfl) ⟨488435, by rfl⟩ : syracuseStep 2604989 = 976871) (by norm_num)
theorem B2605013 : Blo 1736569 2605013 := bbase (se 7 (by rfl) ⟨30527, by rfl⟩ : syracuseStep 2605013 = 61055) (by norm_num)
theorem B4399069 : Blo 1736569 4399069 := bbase (se 3 (by rfl) ⟨824825, by rfl⟩ : syracuseStep 4399069 = 1649651) (by norm_num)
theorem B4456421 : Blo 1736569 4456421 := bbase (se 4 (by rfl) ⟨417789, by rfl⟩ : syracuseStep 4456421 = 835579) (by norm_num)
theorem B2605037 : Blo 1736569 2605037 := bbase (se 3 (by rfl) ⟨488444, by rfl⟩ : syracuseStep 2605037 = 976889) (by norm_num)
theorem B3907565 : Blo 1736569 3907565 := bbase (se 3 (by rfl) ⟨732668, by rfl⟩ : syracuseStep 3907565 = 1465337) (by norm_num)
theorem B2932733 : Blo 1736569 2932733 := bbase (se 3 (by rfl) ⟨549887, by rfl⟩ : syracuseStep 2932733 = 1099775) (by norm_num)
theorem B1736707 : Blo 1736569 1736707 := bstep (se 1 (by rfl) ⟨1302530, by rfl⟩ : syracuseStep 1736707 = 2605061) B2605061
theorem B3907601 : Blo 1736569 3907601 := bstep (se 2 (by rfl) ⟨1465350, by rfl⟩ : syracuseStep 3907601 = 2930701) B2930701
theorem B2605073 : Blo 1736569 2605073 := bstep (se 2 (by rfl) ⟨976902, by rfl⟩ : syracuseStep 2605073 = 1953805) B1953805
theorem B1736723 : Blo 1736569 1736723 := bstep (se 1 (by rfl) ⟨1302542, by rfl⟩ : syracuseStep 1736723 = 2605085) B2605085
theorem B2932753 : Blo 1736569 2932753 := bstep (se 2 (by rfl) ⟨1099782, by rfl⟩ : syracuseStep 2932753 = 2199565) B2199565
theorem B4694051 : Blo 1736569 4694051 := bstep (se 1 (by rfl) ⟨3520538, by rfl⟩ : syracuseStep 4694051 = 7041077) B7041077
theorem B3907619 : Blo 1736569 3907619 := bstep (se 1 (by rfl) ⟨2930714, by rfl⟩ : syracuseStep 3907619 = 5861429) B5861429
theorem B2605091 : Blo 1736569 2605091 := bstep (se 1 (by rfl) ⟨1953818, by rfl⟩ : syracuseStep 2605091 = 3907637) B3907637
theorem B1736739 : Blo 1736569 1736739 := bstep (se 1 (by rfl) ⟨1302554, by rfl⟩ : syracuseStep 1736739 = 2605109) B2605109
theorem B1736755 : Blo 1736569 1736755 := bstep (se 1 (by rfl) ⟨1302566, by rfl⟩ : syracuseStep 1736755 = 2605133) B2605133
theorem B2932787 : Blo 1736569 2932787 := bstep (se 1 (by rfl) ⟨2199590, by rfl⟩ : syracuseStep 2932787 = 4399181) B4399181
theorem B2605121 : Blo 1736569 2605121 := bstep (se 2 (by rfl) ⟨976920, by rfl⟩ : syracuseStep 2605121 = 1953841) B1953841
theorem B1736771 : Blo 1736569 1736771 := bstep (se 1 (by rfl) ⟨1302578, by rfl⟩ : syracuseStep 1736771 = 2605157) B2605157
theorem B3129425 : Blo 1736569 3129425 := bstep (se 2 (by rfl) ⟨1173534, by rfl⟩ : syracuseStep 3129425 = 2347069) B2347069
theorem B2605139 : Blo 1736569 2605139 := bstep (se 1 (by rfl) ⟨1953854, by rfl⟩ : syracuseStep 2605139 = 3907709) B3907709
theorem B1736787 : Blo 1736569 1736787 := bstep (se 1 (by rfl) ⟨1302590, by rfl⟩ : syracuseStep 1736787 = 2605181) B2605181
theorem B1736803 : Blo 1736569 1736803 := bstep (se 1 (by rfl) ⟨1302602, by rfl⟩ : syracuseStep 1736803 = 2605205) B2605205
theorem B2605169 : Blo 1736569 2605169 := bstep (se 2 (by rfl) ⟨976938, by rfl⟩ : syracuseStep 2605169 = 1953877) B1953877
theorem B1736819 : Blo 1736569 1736819 := bstep (se 1 (by rfl) ⟨1302614, by rfl⟩ : syracuseStep 1736819 = 2605229) B2605229
theorem B2605187 : Blo 1736569 2605187 := bstep (se 1 (by rfl) ⟨1953890, by rfl⟩ : syracuseStep 2605187 = 3907781) B3907781
theorem B1736835 : Blo 1736569 1736835 := bstep (se 1 (by rfl) ⟨1302626, by rfl⟩ : syracuseStep 1736835 = 2605253) B2605253
theorem B1736851 : Blo 1736569 1736851 := bstep (se 1 (by rfl) ⟨1302638, by rfl⟩ : syracuseStep 1736851 = 2605277) B2605277
theorem B2605217 : Blo 1736569 2605217 := bstep (se 2 (by rfl) ⟨976956, by rfl⟩ : syracuseStep 2605217 = 1953913) B1953913
theorem B1736867 : Blo 1736569 1736867 := bstep (se 1 (by rfl) ⟨1302650, by rfl⟩ : syracuseStep 1736867 = 2605301) B2605301
theorem B2605235 : Blo 1736569 2605235 := bstep (se 1 (by rfl) ⟨1953926, by rfl⟩ : syracuseStep 2605235 = 3907853) B3907853
theorem B1736883 : Blo 1736569 1736883 := bstep (se 1 (by rfl) ⟨1302662, by rfl⟩ : syracuseStep 1736883 = 2605325) B2605325
theorem B2932915 : Blo 1736569 2932915 := bstep (se 1 (by rfl) ⟨2199686, by rfl⟩ : syracuseStep 2932915 = 4399373) B4399373
theorem B1736899 : Blo 1736569 1736899 := bstep (se 1 (by rfl) ⟨1302674, by rfl⟩ : syracuseStep 1736899 = 2605349) B2605349
theorem B2605265 : Blo 1736569 2605265 := bstep (se 2 (by rfl) ⟨976974, by rfl⟩ : syracuseStep 2605265 = 1953949) B1953949
theorem B1736915 : Blo 1736569 1736915 := bstep (se 1 (by rfl) ⟨1302686, by rfl⟩ : syracuseStep 1736915 = 2605373) B2605373
theorem B2605283 : Blo 1736569 2605283 := bstep (se 1 (by rfl) ⟨1953962, by rfl⟩ : syracuseStep 2605283 = 3907925) B3907925
theorem B1736931 : Blo 1736569 1736931 := bstep (se 1 (by rfl) ⟨1302698, by rfl⟩ : syracuseStep 1736931 = 2605397) B2605397
theorem B1736947 : Blo 1736569 1736947 := bstep (se 1 (by rfl) ⟨1302710, by rfl⟩ : syracuseStep 1736947 = 2605421) B2605421
theorem B2605313 : Blo 1736569 2605313 := bstep (se 2 (by rfl) ⟨976992, by rfl⟩ : syracuseStep 2605313 = 1953985) B1953985
theorem B1736963 : Blo 1736569 1736963 := bstep (se 1 (by rfl) ⟨1302722, by rfl⟩ : syracuseStep 1736963 = 2605445) B2605445
theorem B11133197 : Blo 1736569 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B2605331 : Blo 1736569 2605331 := bstep (se 1 (by rfl) ⟨1953998, by rfl⟩ : syracuseStep 2605331 = 3907997) B3907997
theorem B1736979 : Blo 1736569 1736979 := bstep (se 1 (by rfl) ⟨1302734, by rfl⟩ : syracuseStep 1736979 = 2605469) B2605469
theorem B4456739 : Blo 1736569 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B1736995 : Blo 1736569 1736995 := bstep (se 1 (by rfl) ⟨1302746, by rfl⟩ : syracuseStep 1736995 = 2605493) B2605493
theorem B3907889 : Blo 1736569 3907889 := bstep (se 2 (by rfl) ⟨1465458, by rfl⟩ : syracuseStep 3907889 = 2930917) B2930917
theorem B2605361 : Blo 1736569 2605361 := bstep (se 2 (by rfl) ⟨977010, by rfl⟩ : syracuseStep 2605361 = 1954021) B1954021
theorem B1737011 : Blo 1736569 1737011 := bstep (se 1 (by rfl) ⟨1302758, by rfl⟩ : syracuseStep 1737011 = 2605517) B2605517
theorem B2933057 : Blo 1736569 2933057 := bstep (se 2 (by rfl) ⟨1099896, by rfl⟩ : syracuseStep 2933057 = 2199793) B2199793
theorem B3907907 : Blo 1736569 3907907 := bstep (se 1 (by rfl) ⟨2930930, by rfl⟩ : syracuseStep 3907907 = 5861861) B5861861
theorem B2605379 : Blo 1736569 2605379 := bstep (se 1 (by rfl) ⟨1954034, by rfl⟩ : syracuseStep 2605379 = 3908069) B3908069
theorem B22257989 : Blo 1736569 22257989 := bstep (se 4 (by rfl) ⟨2086686, by rfl⟩ : syracuseStep 22257989 = 4173373) B4173373
theorem B1737027 : Blo 1736569 1737027 := bstep (se 1 (by rfl) ⟨1302770, by rfl⟩ : syracuseStep 1737027 = 2605541) B2605541
theorem B1737043 : Blo 1736569 1737043 := bstep (se 1 (by rfl) ⟨1302782, by rfl⟩ : syracuseStep 1737043 = 2605565) B2605565
theorem B2605409 : Blo 1736569 2605409 := bstep (se 2 (by rfl) ⟨977028, by rfl⟩ : syracuseStep 2605409 = 1954057) B1954057
theorem B1737059 : Blo 1736569 1737059 := bstep (se 1 (by rfl) ⟨1302794, by rfl⟩ : syracuseStep 1737059 = 2605589) B2605589
theorem B6594929 : Blo 1736569 6594929 := bstep (se 2 (by rfl) ⟨2473098, by rfl⟩ : syracuseStep 6594929 = 4946197) B4946197
theorem B2605427 : Blo 1736569 2605427 := bstep (se 1 (by rfl) ⟨1954070, by rfl⟩ : syracuseStep 2605427 = 3908141) B3908141
theorem B1737075 : Blo 1736569 1737075 := bstep (se 1 (by rfl) ⟨1302806, by rfl⟩ : syracuseStep 1737075 = 2605613) B2605613
theorem B1737091 : Blo 1736569 1737091 := bstep (se 1 (by rfl) ⟨1302818, by rfl⟩ : syracuseStep 1737091 = 2605637) B2605637
theorem B2605457 : Blo 1736569 2605457 := bstep (se 2 (by rfl) ⟨977046, by rfl⟩ : syracuseStep 2605457 = 1954093) B1954093
theorem B4399505 : Blo 1736569 4399505 := bstep (se 2 (by rfl) ⟨1649814, by rfl⟩ : syracuseStep 4399505 = 3299629) B3299629
theorem B1737107 : Blo 1736569 1737107 := bstep (se 1 (by rfl) ⟨1302830, by rfl⟩ : syracuseStep 1737107 = 2605661) B2605661
theorem B2605475 : Blo 1736569 2605475 := bstep (se 1 (by rfl) ⟨1954106, by rfl⟩ : syracuseStep 2605475 = 3908213) B3908213
theorem B1737123 : Blo 1736569 1737123 := bstep (se 1 (by rfl) ⟨1302842, by rfl⟩ : syracuseStep 1737123 = 2605685) B2605685
theorem B1737139 : Blo 1736569 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B2605505 : Blo 1736569 2605505 := bstep (se 2 (by rfl) ⟨977064, by rfl⟩ : syracuseStep 2605505 = 1954129) B1954129
theorem B1737155 : Blo 1736569 1737155 := bstep (se 1 (by rfl) ⟨1302866, by rfl⟩ : syracuseStep 1737155 = 2605733) B2605733
theorem B4399555 : Blo 1736569 4399555 := bstep (se 1 (by rfl) ⟨3299666, by rfl⟩ : syracuseStep 4399555 = 6599333) B6599333
theorem B2933185 : Blo 1736569 2933185 := bstep (se 2 (by rfl) ⟨1099944, by rfl⟩ : syracuseStep 2933185 = 2199889) B2199889
theorem B2605523 : Blo 1736569 2605523 := bstep (se 1 (by rfl) ⟨1954142, by rfl⟩ : syracuseStep 2605523 = 3908285) B3908285
theorem B1737171 : Blo 1736569 1737171 := bstep (se 1 (by rfl) ⟨1302878, by rfl⟩ : syracuseStep 1737171 = 2605757) B2605757
theorem B1737187 : Blo 1736569 1737187 := bstep (se 1 (by rfl) ⟨1302890, by rfl⟩ : syracuseStep 1737187 = 2605781) B2605781
theorem B2933219 : Blo 1736569 2933219 := bstep (se 1 (by rfl) ⟨2199914, by rfl⟩ : syracuseStep 2933219 = 4399829) B4399829
theorem B5865965 : Blo 1736569 5865965 := bstep (se 3 (by rfl) ⟨1099868, by rfl⟩ : syracuseStep 5865965 = 2199737) B2199737
theorem B2605553 : Blo 1736569 2605553 := bstep (se 2 (by rfl) ⟨977082, by rfl⟩ : syracuseStep 2605553 = 1954165) B1954165
theorem B8798705 : Blo 1736569 8798705 := bstep (se 2 (by rfl) ⟨3299514, by rfl⟩ : syracuseStep 8798705 = 6599029) B6599029
theorem B1737203 : Blo 1736569 1737203 := bstep (se 1 (by rfl) ⟨1302902, by rfl⟩ : syracuseStep 1737203 = 2605805) B2605805
theorem B2605571 : Blo 1736569 2605571 := bstep (se 1 (by rfl) ⟨1954178, by rfl⟩ : syracuseStep 2605571 = 3908357) B3908357
theorem B1737219 : Blo 1736569 1737219 := bstep (se 1 (by rfl) ⟨1302914, by rfl⟩ : syracuseStep 1737219 = 2605829) B2605829
theorem B1737235 : Blo 1736569 1737235 := bstep (se 1 (by rfl) ⟨1302926, by rfl⟩ : syracuseStep 1737235 = 2605853) B2605853
theorem B2605601 : Blo 1736569 2605601 := bstep (se 2 (by rfl) ⟨977100, by rfl⟩ : syracuseStep 2605601 = 1954201) B1954201
theorem B1737251 : Blo 1736569 1737251 := bstep (se 1 (by rfl) ⟨1302938, by rfl⟩ : syracuseStep 1737251 = 2605877) B2605877
theorem B5866019 : Blo 1736569 5866019 := bstep (se 1 (by rfl) ⟨4399514, by rfl⟩ : syracuseStep 5866019 = 8799029) B8799029
theorem B2474545 : Blo 1736569 2474545 := bstep (se 2 (by rfl) ⟨927954, by rfl⟩ : syracuseStep 2474545 = 1855909) B1855909
theorem B2605619 : Blo 1736569 2605619 := bstep (se 1 (by rfl) ⟨1954214, by rfl⟩ : syracuseStep 2605619 = 3908429) B3908429
theorem B1737267 : Blo 1736569 1737267 := bstep (se 1 (by rfl) ⟨1302950, by rfl⟩ : syracuseStep 1737267 = 2605901) B2605901
theorem B1737283 : Blo 1736569 1737283 := bstep (se 1 (by rfl) ⟨1302962, by rfl⟩ : syracuseStep 1737283 = 2605925) B2605925
theorem B3908177 : Blo 1736569 3908177 := bstep (se 2 (by rfl) ⟨1465566, by rfl⟩ : syracuseStep 3908177 = 2931133) B2931133
theorem B2605649 : Blo 1736569 2605649 := bstep (se 2 (by rfl) ⟨977118, by rfl⟩ : syracuseStep 2605649 = 1954237) B1954237
theorem B1737299 : Blo 1736569 1737299 := bstep (se 1 (by rfl) ⟨1302974, by rfl⟩ : syracuseStep 1737299 = 2605949) B2605949
theorem B4399697 : Blo 1736569 4399697 := bstep (se 2 (by rfl) ⟨1649886, by rfl⟩ : syracuseStep 4399697 = 3299773) B3299773
theorem B3908195 : Blo 1736569 3908195 := bstep (se 1 (by rfl) ⟨2931146, by rfl⟩ : syracuseStep 3908195 = 5862293) B5862293
theorem B2605667 : Blo 1736569 2605667 := bstep (se 1 (by rfl) ⟨1954250, by rfl⟩ : syracuseStep 2605667 = 3908501) B3908501
theorem B1737315 : Blo 1736569 1737315 := bstep (se 1 (by rfl) ⟨1302986, by rfl⟩ : syracuseStep 1737315 = 2605973) B2605973
theorem B2933347 : Blo 1736569 2933347 := bstep (se 1 (by rfl) ⟨2200010, by rfl⟩ : syracuseStep 2933347 = 4400021) B4400021
theorem B4948589 : Blo 1736569 4948589 := bstep (se 3 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 4948589 = 1855721) B1855721
theorem B1737331 : Blo 1736569 1737331 := bstep (se 1 (by rfl) ⟨1302998, by rfl⟩ : syracuseStep 1737331 = 2605997) B2605997
theorem B2605697 : Blo 1736569 2605697 := bstep (se 2 (by rfl) ⟨977136, by rfl⟩ : syracuseStep 2605697 = 1954273) B1954273
theorem B1737347 : Blo 1736569 1737347 := bstep (se 1 (by rfl) ⟨1303010, by rfl⟩ : syracuseStep 1737347 = 2606021) B2606021
theorem B2605715 : Blo 1736569 2605715 := bstep (se 1 (by rfl) ⟨1954286, by rfl⟩ : syracuseStep 2605715 = 3908573) B3908573
theorem B1737363 : Blo 1736569 1737363 := bstep (se 1 (by rfl) ⟨1303022, by rfl⟩ : syracuseStep 1737363 = 2606045) B2606045
theorem B1737379 : Blo 1736569 1737379 := bstep (se 1 (by rfl) ⟨1303034, by rfl⟩ : syracuseStep 1737379 = 2606069) B2606069
theorem B2474659 : Blo 1736569 2474659 := bstep (se 1 (by rfl) ⟨1855994, by rfl⟩ : syracuseStep 2474659 = 3711989) B3711989
theorem B2605745 : Blo 1736569 2605745 := bstep (se 2 (by rfl) ⟨977154, by rfl⟩ : syracuseStep 2605745 = 1954309) B1954309
theorem B1737395 : Blo 1736569 1737395 := bstep (se 1 (by rfl) ⟨1303046, by rfl⟩ : syracuseStep 1737395 = 2606093) B2606093
theorem B2605763 : Blo 1736569 2605763 := bstep (se 1 (by rfl) ⟨1954322, by rfl⟩ : syracuseStep 2605763 = 3908645) B3908645
theorem B1737411 : Blo 1736569 1737411 := bstep (se 1 (by rfl) ⟨1303058, by rfl⟩ : syracuseStep 1737411 = 2606117) B2606117
theorem B1737427 : Blo 1736569 1737427 := bstep (se 1 (by rfl) ⟨1303070, by rfl⟩ : syracuseStep 1737427 = 2606141) B2606141
theorem B2605793 : Blo 1736569 2605793 := bstep (se 2 (by rfl) ⟨977172, by rfl⟩ : syracuseStep 2605793 = 1954345) B1954345
theorem B6259427 : Blo 1736569 6259427 := bstep (se 1 (by rfl) ⟨4694570, by rfl⟩ : syracuseStep 6259427 = 9389141) B9389141
theorem B1737443 : Blo 1736569 1737443 := bstep (se 1 (by rfl) ⟨1303082, by rfl⟩ : syracuseStep 1737443 = 2606165) B2606165
theorem B2933489 : Blo 1736569 2933489 := bstep (se 2 (by rfl) ⟨1100058, by rfl⟩ : syracuseStep 2933489 = 2200117) B2200117
theorem B2605811 : Blo 1736569 2605811 := bstep (se 1 (by rfl) ⟨1954358, by rfl⟩ : syracuseStep 2605811 = 3908717) B3908717
theorem B1737459 : Blo 1736569 1737459 := bstep (se 1 (by rfl) ⟨1303094, by rfl⟩ : syracuseStep 1737459 = 2606189) B2606189
theorem B1737475 : Blo 1736569 1737475 := bstep (se 1 (by rfl) ⟨1303106, by rfl⟩ : syracuseStep 1737475 = 2606213) B2606213
theorem B2605841 : Blo 1736569 2605841 := bstep (se 2 (by rfl) ⟨977190, by rfl⟩ : syracuseStep 2605841 = 1954381) B1954381
theorem B1737491 : Blo 1736569 1737491 := bstep (se 1 (by rfl) ⟨1303118, by rfl⟩ : syracuseStep 1737491 = 2606237) B2606237
theorem B2605859 : Blo 1736569 2605859 := bstep (se 1 (by rfl) ⟨1954394, by rfl⟩ : syracuseStep 2605859 = 3908789) B3908789
theorem B1737507 : Blo 1736569 1737507 := bstep (se 1 (by rfl) ⟨1303130, by rfl⟩ : syracuseStep 1737507 = 2606261) B2606261
theorem B4948771 : Blo 1736569 4948771 := bstep (se 1 (by rfl) ⟨3711578, by rfl⟩ : syracuseStep 4948771 = 7423157) B7423157
theorem B5866289 : Blo 1736569 5866289 := bstep (se 2 (by rfl) ⟨2199858, by rfl⟩ : syracuseStep 5866289 = 4399717) B4399717
theorem B1737523 : Blo 1736569 1737523 := bstep (se 1 (by rfl) ⟨1303142, by rfl⟩ : syracuseStep 1737523 = 2606285) B2606285
theorem B2605889 : Blo 1736569 2605889 := bstep (se 2 (by rfl) ⟨977208, by rfl⟩ : syracuseStep 2605889 = 1954417) B1954417
theorem B4694851 : Blo 1736569 4694851 := bstep (se 1 (by rfl) ⟨3521138, by rfl⟩ : syracuseStep 4694851 = 7042277) B7042277
theorem B1737539 : Blo 1736569 1737539 := bstep (se 1 (by rfl) ⟨1303154, by rfl⟩ : syracuseStep 1737539 = 2606309) B2606309
theorem B2605907 : Blo 1736569 2605907 := bstep (se 1 (by rfl) ⟨1954430, by rfl⟩ : syracuseStep 2605907 = 3908861) B3908861
theorem B1737555 : Blo 1736569 1737555 := bstep (se 1 (by rfl) ⟨1303166, by rfl⟩ : syracuseStep 1737555 = 2606333) B2606333
theorem B1737571 : Blo 1736569 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B3908465 : Blo 1736569 3908465 := bstep (se 2 (by rfl) ⟨1465674, by rfl⟩ : syracuseStep 3908465 = 2931349) B2931349
theorem B2605937 : Blo 1736569 2605937 := bstep (se 2 (by rfl) ⟨977226, by rfl⟩ : syracuseStep 2605937 = 1954453) B1954453
theorem B1737587 : Blo 1736569 1737587 := bstep (se 1 (by rfl) ⟨1303190, by rfl⟩ : syracuseStep 1737587 = 2606381) B2606381
theorem B2933617 : Blo 1736569 2933617 := bstep (se 2 (by rfl) ⟨1100106, by rfl⟩ : syracuseStep 2933617 = 2200213) B2200213
theorem B3908483 : Blo 1736569 3908483 := bstep (se 1 (by rfl) ⟨2931362, by rfl⟩ : syracuseStep 3908483 = 5862725) B5862725
theorem B2605955 : Blo 1736569 2605955 := bstep (se 1 (by rfl) ⟨1954466, by rfl⟩ : syracuseStep 2605955 = 3908933) B3908933
theorem B1737603 : Blo 1736569 1737603 := bstep (se 1 (by rfl) ⟨1303202, by rfl⟩ : syracuseStep 1737603 = 2606405) B2606405
theorem B1737619 : Blo 1736569 1737619 := bstep (se 1 (by rfl) ⟨1303214, by rfl⟩ : syracuseStep 1737619 = 2606429) B2606429
theorem B2933651 : Blo 1736569 2933651 := bstep (se 1 (by rfl) ⟨2200238, by rfl⟩ : syracuseStep 2933651 = 4400477) B4400477
theorem B2605985 : Blo 1736569 2605985 := bstep (se 2 (by rfl) ⟨977244, by rfl⟩ : syracuseStep 2605985 = 1954489) B1954489
theorem B1737635 : Blo 1736569 1737635 := bstep (se 1 (by rfl) ⟨1303226, by rfl⟩ : syracuseStep 1737635 = 2606453) B2606453
theorem B2606003 : Blo 1736569 2606003 := bstep (se 1 (by rfl) ⟨1954502, by rfl⟩ : syracuseStep 2606003 = 3909005) B3909005
theorem B1737651 : Blo 1736569 1737651 := bstep (se 1 (by rfl) ⟨1303238, by rfl⟩ : syracuseStep 1737651 = 2606477) B2606477
theorem B1737667 : Blo 1736569 1737667 := bstep (se 1 (by rfl) ⟨1303250, by rfl⟩ : syracuseStep 1737667 = 2606501) B2606501
theorem B4948931 : Blo 1736569 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B2606033 : Blo 1736569 2606033 := bstep (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) B1954525
theorem B1737683 : Blo 1736569 1737683 := bstep (se 1 (by rfl) ⟨1303262, by rfl⟩ : syracuseStep 1737683 = 2606525) B2606525
theorem B2606051 : Blo 1736569 2606051 := bstep (se 1 (by rfl) ⟨1954538, by rfl⟩ : syracuseStep 2606051 = 3909077) B3909077
theorem B1737699 : Blo 1736569 1737699 := bstep (se 1 (by rfl) ⟨1303274, by rfl⟩ : syracuseStep 1737699 = 2606549) B2606549
theorem B1737715 : Blo 1736569 1737715 := bstep (se 1 (by rfl) ⟨1303286, by rfl⟩ : syracuseStep 1737715 = 2606573) B2606573
theorem B2606081 : Blo 1736569 2606081 := bstep (se 2 (by rfl) ⟨977280, by rfl⟩ : syracuseStep 2606081 = 1954561) B1954561
theorem B1737731 : Blo 1736569 1737731 := bstep (se 1 (by rfl) ⟨1303298, by rfl⟩ : syracuseStep 1737731 = 2606597) B2606597
theorem B2606099 : Blo 1736569 2606099 := bstep (se 1 (by rfl) ⟨1954574, by rfl⟩ : syracuseStep 2606099 = 3909149) B3909149
theorem B1737747 : Blo 1736569 1737747 := bstep (se 1 (by rfl) ⟨1303310, by rfl⟩ : syracuseStep 1737747 = 2606621) B2606621
theorem B2933779 : Blo 1736569 2933779 := bstep (se 1 (by rfl) ⟨2200334, by rfl⟩ : syracuseStep 2933779 = 4400669) B4400669
theorem B1737763 : Blo 1736569 1737763 := bstep (se 1 (by rfl) ⟨1303322, by rfl⟩ : syracuseStep 1737763 = 2606645) B2606645
theorem B2606129 : Blo 1736569 2606129 := bstep (se 2 (by rfl) ⟨977298, by rfl⟩ : syracuseStep 2606129 = 1954597) B1954597
theorem B1737779 : Blo 1736569 1737779 := bstep (se 1 (by rfl) ⟨1303334, by rfl⟩ : syracuseStep 1737779 = 2606669) B2606669
theorem B2606147 : Blo 1736569 2606147 := bstep (se 1 (by rfl) ⟨1954610, by rfl⟩ : syracuseStep 2606147 = 3909221) B3909221
theorem B1737795 : Blo 1736569 1737795 := bstep (se 1 (by rfl) ⟨1303346, by rfl⟩ : syracuseStep 1737795 = 2606693) B2606693
theorem B1737811 : Blo 1736569 1737811 := bstep (se 1 (by rfl) ⟨1303358, by rfl⟩ : syracuseStep 1737811 = 2606717) B2606717
theorem B2606177 : Blo 1736569 2606177 := bstep (se 2 (by rfl) ⟨977316, by rfl⟩ : syracuseStep 2606177 = 1954633) B1954633
theorem B1737827 : Blo 1736569 1737827 := bstep (se 1 (by rfl) ⟨1303370, by rfl⟩ : syracuseStep 1737827 = 2606741) B2606741
theorem B2606195 : Blo 1736569 2606195 := bstep (se 1 (by rfl) ⟨1954646, by rfl⟩ : syracuseStep 2606195 = 3909293) B3909293
theorem B1737843 : Blo 1736569 1737843 := bstep (se 1 (by rfl) ⟨1303382, by rfl⟩ : syracuseStep 1737843 = 2606765) B2606765
theorem B5563523 : Blo 1736569 5563523 := bstep (se 1 (by rfl) ⟨4172642, by rfl⟩ : syracuseStep 5563523 = 8345285) B8345285
theorem B1737859 : Blo 1736569 1737859 := bstep (se 1 (by rfl) ⟨1303394, by rfl⟩ : syracuseStep 1737859 = 2606789) B2606789
theorem B3908753 : Blo 1736569 3908753 := bstep (se 2 (by rfl) ⟨1465782, by rfl⟩ : syracuseStep 3908753 = 2931565) B2931565
theorem B2606225 : Blo 1736569 2606225 := bstep (se 2 (by rfl) ⟨977334, by rfl⟩ : syracuseStep 2606225 = 1954669) B1954669
theorem B1737875 : Blo 1736569 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B3908771 : Blo 1736569 3908771 := bstep (se 1 (by rfl) ⟨2931578, by rfl⟩ : syracuseStep 3908771 = 5863157) B5863157
theorem B2606243 : Blo 1736569 2606243 := bstep (se 1 (by rfl) ⟨1954682, by rfl⟩ : syracuseStep 2606243 = 3909365) B3909365
theorem B1737891 : Blo 1736569 1737891 := bstep (se 1 (by rfl) ⟨1303418, by rfl⟩ : syracuseStep 1737891 = 2606837) B2606837
theorem B7144625 : Blo 1736569 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B1737907 : Blo 1736569 1737907 := bstep (se 1 (by rfl) ⟨1303430, by rfl⟩ : syracuseStep 1737907 = 2606861) B2606861
theorem B2606273 : Blo 1736569 2606273 := bstep (se 2 (by rfl) ⟨977352, by rfl⟩ : syracuseStep 2606273 = 1954705) B1954705
theorem B1737923 : Blo 1736569 1737923 := bstep (se 1 (by rfl) ⟨1303442, by rfl⟩ : syracuseStep 1737923 = 2606885) B2606885
theorem B2606291 : Blo 1736569 2606291 := bstep (se 1 (by rfl) ⟨1954718, by rfl⟩ : syracuseStep 2606291 = 3909437) B3909437
theorem B1737939 : Blo 1736569 1737939 := bstep (se 1 (by rfl) ⟨1303454, by rfl⟩ : syracuseStep 1737939 = 2606909) B2606909
theorem B14091491 : Blo 1736569 14091491 := bstep (se 1 (by rfl) ⟨10568618, by rfl⟩ : syracuseStep 14091491 = 21137237) B21137237
theorem B1737955 : Blo 1736569 1737955 := bstep (se 1 (by rfl) ⟨1303466, by rfl⟩ : syracuseStep 1737955 = 2606933) B2606933
theorem B2606321 : Blo 1736569 2606321 := bstep (se 2 (by rfl) ⟨977370, by rfl⟩ : syracuseStep 2606321 = 1954741) B1954741
theorem B1737971 : Blo 1736569 1737971 := bstep (se 1 (by rfl) ⟨1303478, by rfl⟩ : syracuseStep 1737971 = 2606957) B2606957
theorem B2606339 : Blo 1736569 2606339 := bstep (se 1 (by rfl) ⟨1954754, by rfl⟩ : syracuseStep 2606339 = 3909509) B3909509
theorem B1737987 : Blo 1736569 1737987 := bstep (se 1 (by rfl) ⟨1303490, by rfl⟩ : syracuseStep 1737987 = 2606981) B2606981
theorem B1738003 : Blo 1736569 1738003 := bstep (se 1 (by rfl) ⟨1303502, by rfl⟩ : syracuseStep 1738003 = 2607005) B2607005
theorem B37578005 : Blo 1736569 37578005 := bstep (se 6 (by rfl) ⟨880734, by rfl⟩ : syracuseStep 37578005 = 1761469) B1761469
theorem B2606369 : Blo 1736569 2606369 := bstep (se 2 (by rfl) ⟨977388, by rfl⟩ : syracuseStep 2606369 = 1954777) B1954777
theorem B1738019 : Blo 1736569 1738019 := bstep (se 1 (by rfl) ⟨1303514, by rfl⟩ : syracuseStep 1738019 = 2607029) B2607029
theorem B10036529 : Blo 1736569 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B2606387 : Blo 1736569 2606387 := bstep (se 1 (by rfl) ⟨1954790, by rfl⟩ : syracuseStep 2606387 = 3909581) B3909581
theorem B1738035 : Blo 1736569 1738035 := bstep (se 1 (by rfl) ⟨1303526, by rfl⟩ : syracuseStep 1738035 = 2607053) B2607053
theorem B1738051 : Blo 1736569 1738051 := bstep (se 1 (by rfl) ⟨1303538, by rfl⟩ : syracuseStep 1738051 = 2607077) B2607077
theorem B5866829 : Blo 1736569 5866829 := bstep (se 3 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 5866829 = 2200061) B2200061
theorem B2606417 : Blo 1736569 2606417 := bstep (se 2 (by rfl) ⟨977406, by rfl⟩ : syracuseStep 2606417 = 1954813) B1954813
theorem B1738067 : Blo 1736569 1738067 := bstep (se 1 (by rfl) ⟨1303550, by rfl⟩ : syracuseStep 1738067 = 2607101) B2607101
theorem B19785059 : Blo 1736569 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B2606435 : Blo 1736569 2606435 := bstep (se 1 (by rfl) ⟨1954826, by rfl⟩ : syracuseStep 2606435 = 3909653) B3909653
theorem B1738083 : Blo 1736569 1738083 := bstep (se 1 (by rfl) ⟨1303562, by rfl⟩ : syracuseStep 1738083 = 2607125) B2607125
theorem B1738099 : Blo 1736569 1738099 := bstep (se 1 (by rfl) ⟨1303574, by rfl⟩ : syracuseStep 1738099 = 2607149) B2607149
theorem B2606465 : Blo 1736569 2606465 := bstep (se 2 (by rfl) ⟨977424, by rfl⟩ : syracuseStep 2606465 = 1954849) B1954849
theorem B1738115 : Blo 1736569 1738115 := bstep (se 1 (by rfl) ⟨1303586, by rfl⟩ : syracuseStep 1738115 = 2607173) B2607173
theorem B5866883 : Blo 1736569 5866883 := bstep (se 1 (by rfl) ⟨4400162, by rfl⟩ : syracuseStep 5866883 = 8800325) B8800325
theorem B2606483 : Blo 1736569 2606483 := bstep (se 1 (by rfl) ⟨1954862, by rfl⟩ : syracuseStep 2606483 = 3909725) B3909725
theorem B1738131 : Blo 1736569 1738131 := bstep (se 1 (by rfl) ⟨1303598, by rfl⟩ : syracuseStep 1738131 = 2607197) B2607197
theorem B1738147 : Blo 1736569 1738147 := bstep (se 1 (by rfl) ⟨1303610, by rfl⟩ : syracuseStep 1738147 = 2607221) B2607221
theorem B3909041 : Blo 1736569 3909041 := bstep (se 2 (by rfl) ⟨1465890, by rfl⟩ : syracuseStep 3909041 = 2931781) B2931781
theorem B2606513 : Blo 1736569 2606513 := bstep (se 2 (by rfl) ⟨977442, by rfl⟩ : syracuseStep 2606513 = 1954885) B1954885
theorem B1738163 : Blo 1736569 1738163 := bstep (se 1 (by rfl) ⟨1303622, by rfl⟩ : syracuseStep 1738163 = 2607245) B2607245
theorem B3909059 : Blo 1736569 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B2606531 : Blo 1736569 2606531 := bstep (se 1 (by rfl) ⟨1954898, by rfl⟩ : syracuseStep 2606531 = 3909797) B3909797
theorem B1738179 : Blo 1736569 1738179 := bstep (se 1 (by rfl) ⟨1303634, by rfl⟩ : syracuseStep 1738179 = 2607269) B2607269
theorem B1738195 : Blo 1736569 1738195 := bstep (se 1 (by rfl) ⟨1303646, by rfl⟩ : syracuseStep 1738195 = 2607293) B2607293
theorem B2606561 : Blo 1736569 2606561 := bstep (se 2 (by rfl) ⟨977460, by rfl⟩ : syracuseStep 2606561 = 1954921) B1954921
theorem B1738211 : Blo 1736569 1738211 := bstep (se 1 (by rfl) ⟨1303658, by rfl⟩ : syracuseStep 1738211 = 2607317) B2607317
theorem B8349169 : Blo 1736569 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B2606579 : Blo 1736569 2606579 := bstep (se 1 (by rfl) ⟨1954934, by rfl⟩ : syracuseStep 2606579 = 3909869) B3909869
theorem B1738227 : Blo 1736569 1738227 := bstep (se 1 (by rfl) ⟨1303670, by rfl⟩ : syracuseStep 1738227 = 2607341) B2607341
theorem B1738243 : Blo 1736569 1738243 := bstep (se 1 (by rfl) ⟨1303682, by rfl⟩ : syracuseStep 1738243 = 2607365) B2607365
theorem B2606609 : Blo 1736569 2606609 := bstep (se 2 (by rfl) ⟨977478, by rfl⟩ : syracuseStep 2606609 = 1954957) B1954957
theorem B1738259 : Blo 1736569 1738259 := bstep (se 1 (by rfl) ⟨1303694, by rfl⟩ : syracuseStep 1738259 = 2607389) B2607389
theorem B2606627 : Blo 1736569 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1738275 : Blo 1736569 1738275 := bstep (se 1 (by rfl) ⟨1303706, by rfl⟩ : syracuseStep 1738275 = 2607413) B2607413
theorem B4400689 : Blo 1736569 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B2229811 : Blo 1736569 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B1738291 : Blo 1736569 1738291 := bstep (se 1 (by rfl) ⟨1303718, by rfl⟩ : syracuseStep 1738291 = 2607437) B2607437
theorem B2606657 : Blo 1736569 2606657 := bstep (se 2 (by rfl) ⟨977496, by rfl⟩ : syracuseStep 2606657 = 1954993) B1954993
theorem B1738307 : Blo 1736569 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B2606675 : Blo 1736569 2606675 := bstep (se 1 (by rfl) ⟨1955006, by rfl⟩ : syracuseStep 2606675 = 3910013) B3910013
theorem B1738323 : Blo 1736569 1738323 := bstep (se 1 (by rfl) ⟨1303742, by rfl⟩ : syracuseStep 1738323 = 2607485) B2607485
theorem B1738339 : Blo 1736569 1738339 := bstep (se 1 (by rfl) ⟨1303754, by rfl⟩ : syracuseStep 1738339 = 2607509) B2607509
theorem B31704689 : Blo 1736569 31704689 := bstep (se 2 (by rfl) ⟨11889258, by rfl⟩ : syracuseStep 31704689 = 23778517) B23778517
theorem B2606705 : Blo 1736569 2606705 := bstep (se 2 (by rfl) ⟨977514, by rfl⟩ : syracuseStep 2606705 = 1955029) B1955029
theorem B1738355 : Blo 1736569 1738355 := bstep (se 1 (by rfl) ⟨1303766, by rfl⟩ : syracuseStep 1738355 = 2607533) B2607533
theorem B2606723 : Blo 1736569 2606723 := bstep (se 1 (by rfl) ⟨1955042, by rfl⟩ : syracuseStep 2606723 = 3910085) B3910085
theorem B1738371 : Blo 1736569 1738371 := bstep (se 1 (by rfl) ⟨1303778, by rfl⟩ : syracuseStep 1738371 = 2607557) B2607557
theorem B1738387 : Blo 1736569 1738387 := bstep (se 1 (by rfl) ⟨1303790, by rfl⟩ : syracuseStep 1738387 = 2607581) B2607581
theorem B5867153 : Blo 1736569 5867153 := bstep (se 2 (by rfl) ⟨2200182, by rfl⟩ : syracuseStep 5867153 = 4400365) B4400365
theorem B2606753 : Blo 1736569 2606753 := bstep (se 2 (by rfl) ⟨977532, by rfl⟩ : syracuseStep 2606753 = 1955065) B1955065
theorem B1738403 : Blo 1736569 1738403 := bstep (se 1 (by rfl) ⟨1303802, by rfl⟩ : syracuseStep 1738403 = 2607605) B2607605
theorem B2606771 : Blo 1736569 2606771 := bstep (se 1 (by rfl) ⟨1955078, by rfl⟩ : syracuseStep 2606771 = 3910157) B3910157
theorem B1738419 : Blo 1736569 1738419 := bstep (se 1 (by rfl) ⟨1303814, by rfl⟩ : syracuseStep 1738419 = 2607629) B2607629
theorem B1738435 : Blo 1736569 1738435 := bstep (se 1 (by rfl) ⟨1303826, by rfl⟩ : syracuseStep 1738435 = 2607653) B2607653
theorem B3909329 : Blo 1736569 3909329 := bstep (se 2 (by rfl) ⟨1465998, by rfl⟩ : syracuseStep 3909329 = 2931997) B2931997
theorem B2606801 : Blo 1736569 2606801 := bstep (se 2 (by rfl) ⟨977550, by rfl⟩ : syracuseStep 2606801 = 1955101) B1955101
theorem B1738451 : Blo 1736569 1738451 := bstep (se 1 (by rfl) ⟨1303838, by rfl⟩ : syracuseStep 1738451 = 2607677) B2607677
theorem B3909347 : Blo 1736569 3909347 := bstep (se 1 (by rfl) ⟨2932010, by rfl⟩ : syracuseStep 3909347 = 5864021) B5864021
theorem B2606819 : Blo 1736569 2606819 := bstep (se 1 (by rfl) ⟨1955114, by rfl⟩ : syracuseStep 2606819 = 3910229) B3910229
theorem B1738467 : Blo 1736569 1738467 := bstep (se 1 (by rfl) ⟨1303850, by rfl⟩ : syracuseStep 1738467 = 2607701) B2607701
theorem B1738483 : Blo 1736569 1738483 := bstep (se 1 (by rfl) ⟨1303862, by rfl⟩ : syracuseStep 1738483 = 2607725) B2607725
theorem B2606849 : Blo 1736569 2606849 := bstep (se 2 (by rfl) ⟨977568, by rfl⟩ : syracuseStep 2606849 = 1955137) B1955137
theorem B1738499 : Blo 1736569 1738499 := bstep (se 1 (by rfl) ⟨1303874, by rfl⟩ : syracuseStep 1738499 = 2607749) B2607749
theorem B6686477 : Blo 1736569 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B7423757 : Blo 1736569 7423757 := bstep (se 3 (by rfl) ⟨1391954, by rfl⟩ : syracuseStep 7423757 = 2783909) B2783909
theorem B2606867 : Blo 1736569 2606867 := bstep (se 1 (by rfl) ⟨1955150, by rfl⟩ : syracuseStep 2606867 = 3910301) B3910301
theorem B1738515 : Blo 1736569 1738515 := bstep (se 1 (by rfl) ⟨1303886, by rfl⟩ : syracuseStep 1738515 = 2607773) B2607773
theorem B6596387 : Blo 1736569 6596387 := bstep (se 1 (by rfl) ⟨4947290, by rfl⟩ : syracuseStep 6596387 = 9894581) B9894581
theorem B1738531 : Blo 1736569 1738531 := bstep (se 1 (by rfl) ⟨1303898, by rfl⟩ : syracuseStep 1738531 = 2607797) B2607797
theorem B2606897 : Blo 1736569 2606897 := bstep (se 2 (by rfl) ⟨977586, by rfl⟩ : syracuseStep 2606897 = 1955173) B1955173
theorem B1738547 : Blo 1736569 1738547 := bstep (se 1 (by rfl) ⟨1303910, by rfl⟩ : syracuseStep 1738547 = 2607821) B2607821
theorem B2606915 : Blo 1736569 2606915 := bstep (se 1 (by rfl) ⟨1955186, by rfl⟩ : syracuseStep 2606915 = 3910373) B3910373
theorem B1738563 : Blo 1736569 1738563 := bstep (se 1 (by rfl) ⟨1303922, by rfl⟩ : syracuseStep 1738563 = 2607845) B2607845
theorem B2606945 : Blo 1736569 2606945 := bstep (se 2 (by rfl) ⟨977604, by rfl⟩ : syracuseStep 2606945 = 1955209) B1955209
theorem B13191011 : Blo 1736569 13191011 := bstep (se 1 (by rfl) ⟨9893258, by rfl⟩ : syracuseStep 13191011 = 19786517) B19786517
theorem B2606963 : Blo 1736569 2606963 := bstep (se 1 (by rfl) ⟨1955222, by rfl⟩ : syracuseStep 2606963 = 3910445) B3910445
theorem B2606993 : Blo 1736569 2606993 := bstep (se 2 (by rfl) ⟨977622, by rfl⟩ : syracuseStep 2606993 = 1955245) B1955245
theorem B2508689 : Blo 1736569 2508689 := bstep (se 2 (by rfl) ⟨940758, by rfl⟩ : syracuseStep 2508689 = 1881517) B1881517
theorem B2607011 : Blo 1736569 2607011 := bstep (se 1 (by rfl) ⟨1955258, by rfl⟩ : syracuseStep 2607011 = 3910517) B3910517
theorem B8800163 : Blo 1736569 8800163 := bstep (se 1 (by rfl) ⟨6600122, by rfl⟩ : syracuseStep 8800163 = 13200245) B13200245
theorem B2607041 : Blo 1736569 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B14837701 : Blo 1736569 14837701 := bstep (se 4 (by rfl) ⟨1391034, by rfl⟩ : syracuseStep 14837701 = 2782069) B2782069
theorem B2607059 : Blo 1736569 2607059 := bstep (se 1 (by rfl) ⟨1955294, by rfl⟩ : syracuseStep 2607059 = 3910589) B3910589
theorem B3909617 : Blo 1736569 3909617 := bstep (se 2 (by rfl) ⟨1466106, by rfl⟩ : syracuseStep 3909617 = 2932213) B2932213
theorem B2607089 : Blo 1736569 2607089 := bstep (se 2 (by rfl) ⟨977658, by rfl⟩ : syracuseStep 2607089 = 1955317) B1955317
theorem B4950001 : Blo 1736569 4950001 := bstep (se 2 (by rfl) ⟨1856250, by rfl⟩ : syracuseStep 4950001 = 3712501) B3712501
theorem B3909635 : Blo 1736569 3909635 := bstep (se 1 (by rfl) ⟨2932226, by rfl⟩ : syracuseStep 3909635 = 5864453) B5864453
theorem B2607107 : Blo 1736569 2607107 := bstep (se 1 (by rfl) ⟨1955330, by rfl⟩ : syracuseStep 2607107 = 3910661) B3910661
theorem B9897997 : Blo 1736569 9897997 := bstep (se 3 (by rfl) ⟨1855874, by rfl⟩ : syracuseStep 9897997 = 3711749) B3711749
theorem B2607137 : Blo 1736569 2607137 := bstep (se 2 (by rfl) ⟨977676, by rfl⟩ : syracuseStep 2607137 = 1955353) B1955353
theorem B2607155 : Blo 1736569 2607155 := bstep (se 1 (by rfl) ⟨1955366, by rfl⟩ : syracuseStep 2607155 = 3910733) B3910733
theorem B2607185 : Blo 1736569 2607185 := bstep (se 2 (by rfl) ⟨977694, by rfl⟩ : syracuseStep 2607185 = 1955389) B1955389
theorem B2009171 : Blo 1736569 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B2607203 : Blo 1736569 2607203 := bstep (se 1 (by rfl) ⟨1955402, by rfl⟩ : syracuseStep 2607203 = 3910805) B3910805
theorem B2607233 : Blo 1736569 2607233 := bstep (se 2 (by rfl) ⟨977712, by rfl⟩ : syracuseStep 2607233 = 1955425) B1955425
theorem B2607251 : Blo 1736569 2607251 := bstep (se 1 (by rfl) ⟨1955438, by rfl⟩ : syracuseStep 2607251 = 3910877) B3910877
theorem B2607281 : Blo 1736569 2607281 := bstep (se 2 (by rfl) ⟨977730, by rfl⟩ : syracuseStep 2607281 = 1955461) B1955461
theorem B2607299 : Blo 1736569 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B5941457 : Blo 1736569 5941457 := bstep (se 2 (by rfl) ⟨2228046, by rfl⟩ : syracuseStep 5941457 = 4456093) B4456093
theorem B2607329 : Blo 1736569 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B16918769 : Blo 1736569 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B2607347 : Blo 1736569 2607347 := bstep (se 1 (by rfl) ⟨1955510, by rfl⟩ : syracuseStep 2607347 = 3911021) B3911021
theorem B3909905 : Blo 1736569 3909905 := bstep (se 2 (by rfl) ⟨1466214, by rfl⟩ : syracuseStep 3909905 = 2932429) B2932429
theorem B2607377 : Blo 1736569 2607377 := bstep (se 2 (by rfl) ⟨977766, by rfl⟩ : syracuseStep 2607377 = 1955533) B1955533
theorem B3909923 : Blo 1736569 3909923 := bstep (se 1 (by rfl) ⟨2932442, by rfl⟩ : syracuseStep 3909923 = 5864885) B5864885
theorem B2607395 : Blo 1736569 2607395 := bstep (se 1 (by rfl) ⟨1955546, by rfl⟩ : syracuseStep 2607395 = 3911093) B3911093
theorem B2607425 : Blo 1736569 2607425 := bstep (se 2 (by rfl) ⟨977784, by rfl⟩ : syracuseStep 2607425 = 1955569) B1955569
theorem B2607443 : Blo 1736569 2607443 := bstep (se 1 (by rfl) ⟨1955582, by rfl⟩ : syracuseStep 2607443 = 3911165) B3911165
theorem B4696429 : Blo 1736569 4696429 := bstep (se 3 (by rfl) ⟨880580, by rfl⟩ : syracuseStep 4696429 = 1761161) B1761161
theorem B2607473 : Blo 1736569 2607473 := bstep (se 2 (by rfl) ⟨977802, by rfl⟩ : syracuseStep 2607473 = 1955605) B1955605
theorem B2607491 : Blo 1736569 2607491 := bstep (se 1 (by rfl) ⟨1955618, by rfl⟩ : syracuseStep 2607491 = 3911237) B3911237
theorem B2607521 : Blo 1736569 2607521 := bstep (se 2 (by rfl) ⟨977820, by rfl⟩ : syracuseStep 2607521 = 1955641) B1955641
theorem B2607539 : Blo 1736569 2607539 := bstep (se 1 (by rfl) ⟨1955654, by rfl⟩ : syracuseStep 2607539 = 3911309) B3911309
theorem B2197955 : Blo 1736569 2197955 := bstep (se 1 (by rfl) ⟨1648466, by rfl⟩ : syracuseStep 2197955 = 3296933) B3296933
theorem B2607569 : Blo 1736569 2607569 := bstep (se 2 (by rfl) ⟨977838, by rfl⟩ : syracuseStep 2607569 = 1955677) B1955677
theorem B2607587 : Blo 1736569 2607587 := bstep (se 1 (by rfl) ⟨1955690, by rfl⟩ : syracuseStep 2607587 = 3911381) B3911381
theorem B14846449 : Blo 1736569 14846449 := bstep (se 2 (by rfl) ⟨5567418, by rfl⟩ : syracuseStep 14846449 = 11134837) B11134837
theorem B2607617 : Blo 1736569 2607617 := bstep (se 2 (by rfl) ⟨977856, by rfl⟩ : syracuseStep 2607617 = 1955713) B1955713
theorem B2607635 : Blo 1736569 2607635 := bstep (se 1 (by rfl) ⟨1955726, by rfl⟩ : syracuseStep 2607635 = 3911453) B3911453
theorem B3910193 : Blo 1736569 3910193 := bstep (se 2 (by rfl) ⟨1466322, by rfl⟩ : syracuseStep 3910193 = 2932645) B2932645
theorem B2607665 : Blo 1736569 2607665 := bstep (se 2 (by rfl) ⟨977874, by rfl⟩ : syracuseStep 2607665 = 1955749) B1955749
theorem B3910211 : Blo 1736569 3910211 := bstep (se 1 (by rfl) ⟨2932658, by rfl⟩ : syracuseStep 3910211 = 5865317) B5865317
theorem B2607683 : Blo 1736569 2607683 := bstep (se 1 (by rfl) ⟨1955762, by rfl⟩ : syracuseStep 2607683 = 3911525) B3911525
theorem B2607713 : Blo 1736569 2607713 := bstep (se 2 (by rfl) ⟨977892, by rfl⟩ : syracuseStep 2607713 = 1955785) B1955785
theorem B2607731 : Blo 1736569 2607731 := bstep (se 1 (by rfl) ⟨1955798, by rfl⟩ : syracuseStep 2607731 = 3911597) B3911597
theorem B3132035 : Blo 1736569 3132035 := bstep (se 1 (by rfl) ⟨2349026, by rfl⟩ : syracuseStep 3132035 = 4698053) B4698053
theorem B2607761 : Blo 1736569 2607761 := bstep (se 2 (by rfl) ⟨977910, by rfl⟩ : syracuseStep 2607761 = 1955821) B1955821
theorem B2607779 : Blo 1736569 2607779 := bstep (se 1 (by rfl) ⟨1955834, by rfl⟩ : syracuseStep 2607779 = 3911669) B3911669
theorem B2607809 : Blo 1736569 2607809 := bstep (se 2 (by rfl) ⟨977928, by rfl⟩ : syracuseStep 2607809 = 1955857) B1955857
theorem B8800973 : Blo 1736569 8800973 := bstep (se 3 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 8800973 = 3300365) B3300365
theorem B2607827 : Blo 1736569 2607827 := bstep (se 1 (by rfl) ⟨1955870, by rfl⟩ : syracuseStep 2607827 = 3911741) B3911741
theorem B6597389 : Blo 1736569 6597389 := bstep (se 3 (by rfl) ⟨1237010, by rfl⟩ : syracuseStep 6597389 = 2474021) B2474021
theorem B3910481 : Blo 1736569 3910481 := bstep (se 2 (by rfl) ⟨1466430, by rfl⟩ : syracuseStep 3910481 = 2932861) B2932861
theorem B3910499 : Blo 1736569 3910499 := bstep (se 1 (by rfl) ⟨2932874, by rfl⟩ : syracuseStep 3910499 = 5865749) B5865749
theorem B5565293 : Blo 1736569 5565293 := bstep (se 3 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 5565293 = 2086985) B2086985
theorem B6261617 : Blo 1736569 6261617 := bstep (se 2 (by rfl) ⟨2348106, by rfl⟩ : syracuseStep 6261617 = 4696213) B4696213
theorem B3132337 : Blo 1736569 3132337 := bstep (se 2 (by rfl) ⟨1174626, by rfl⟩ : syracuseStep 3132337 = 2349253) B2349253
theorem B5082065 : Blo 1736569 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B10030085 : Blo 1736569 10030085 := bstep (se 4 (by rfl) ⟨940320, by rfl⟩ : syracuseStep 10030085 = 1880641) B1880641
theorem B3910769 : Blo 1736569 3910769 := bstep (se 2 (by rfl) ⟨1466538, by rfl⟩ : syracuseStep 3910769 = 2933077) B2933077
theorem B2198659 : Blo 1736569 2198659 := bstep (se 1 (by rfl) ⟨1648994, by rfl⟩ : syracuseStep 2198659 = 3297989) B3297989
theorem B3910787 : Blo 1736569 3910787 := bstep (se 1 (by rfl) ⟨2933090, by rfl⟩ : syracuseStep 3910787 = 5866181) B5866181
theorem B16698565 : Blo 1736569 16698565 := bstep (se 4 (by rfl) ⟨1565490, by rfl⟩ : syracuseStep 16698565 = 3130981) B3130981
theorem B2198755 : Blo 1736569 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B11128049 : Blo 1736569 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B13372685 : Blo 1736569 13372685 := bstep (se 3 (by rfl) ⟨2507378, by rfl⟩ : syracuseStep 13372685 = 5014757) B5014757
theorem B11136325 : Blo 1736569 11136325 := bstep (se 4 (by rfl) ⟨1044030, by rfl⟩ : syracuseStep 11136325 = 2088061) B2088061
theorem B3911057 : Blo 1736569 3911057 := bstep (se 2 (by rfl) ⟨1466646, by rfl⟩ : syracuseStep 3911057 = 2933293) B2933293
theorem B3911075 : Blo 1736569 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B8793521 : Blo 1736569 8793521 := bstep (se 2 (by rfl) ⟨3297570, by rfl⟩ : syracuseStep 8793521 = 6595141) B6595141
theorem B3911345 : Blo 1736569 3911345 := bstep (se 2 (by rfl) ⟨1466754, by rfl⟩ : syracuseStep 3911345 = 2933509) B2933509
theorem B3296963 : Blo 1736569 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B3911363 : Blo 1736569 3911363 := bstep (se 1 (by rfl) ⟨2933522, by rfl⟩ : syracuseStep 3911363 = 5867045) B5867045
theorem B2199251 : Blo 1736569 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B5861105 : Blo 1736569 5861105 := bstep (se 2 (by rfl) ⟨2197914, by rfl⟩ : syracuseStep 5861105 = 4395829) B4395829
theorem B6262541 : Blo 1736569 6262541 := bstep (se 3 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 6262541 = 2348453) B2348453
theorem B10170211 : Blo 1736569 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B1953715 : Blo 1736569 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B9899981 : Blo 1736569 9899981 := bstep (se 3 (by rfl) ⟨1856246, by rfl⟩ : syracuseStep 9899981 = 3712493) B3712493
theorem B3911633 : Blo 1736569 3911633 := bstep (se 2 (by rfl) ⟨1466862, by rfl⟩ : syracuseStep 3911633 = 2933725) B2933725
theorem B3911651 : Blo 1736569 3911651 := bstep (se 1 (by rfl) ⟨2933738, by rfl⟩ : syracuseStep 3911651 = 5867477) B5867477
theorem B5017585 : Blo 1736569 5017585 := bstep (se 2 (by rfl) ⟨1881594, by rfl⟩ : syracuseStep 5017585 = 3763189) B3763189
theorem B1953859 : Blo 1736569 1953859 := bstep (se 1 (by rfl) ⟨1465394, by rfl⟩ : syracuseStep 1953859 = 2930789) B2930789
theorem B1954003 : Blo 1736569 1954003 := bstep (se 1 (by rfl) ⟨1465502, by rfl⟩ : syracuseStep 1954003 = 2931005) B2931005
theorem B1855747 : Blo 1736569 1855747 := bstep (se 1 (by rfl) ⟨1391810, by rfl⟩ : syracuseStep 1855747 = 2783621) B2783621
theorem B17150221 : Blo 1736569 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B5861645 : Blo 1736569 5861645 := bstep (se 3 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 5861645 = 2198117) B2198117
theorem B5861699 : Blo 1736569 5861699 := bstep (se 1 (by rfl) ⟨4396274, by rfl⟩ : syracuseStep 5861699 = 8792549) B8792549
theorem B9892165 : Blo 1736569 9892165 := bstep (se 4 (by rfl) ⟨927390, by rfl⟩ : syracuseStep 9892165 = 1854781) B1854781
theorem B2822483 : Blo 1736569 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B1954147 : Blo 1736569 1954147 := bstep (se 1 (by rfl) ⟨1465610, by rfl⟩ : syracuseStep 1954147 = 2931221) B2931221
theorem B2199955 : Blo 1736569 2199955 := bstep (se 1 (by rfl) ⟨1649966, by rfl⟩ : syracuseStep 2199955 = 3299933) B3299933
theorem B1954291 : Blo 1736569 1954291 := bstep (se 1 (by rfl) ⟨1465718, by rfl⟩ : syracuseStep 1954291 = 2931437) B2931437
theorem B2200051 : Blo 1736569 2200051 := bstep (se 1 (by rfl) ⟨1650038, by rfl⟩ : syracuseStep 2200051 = 3300077) B3300077
theorem B5861969 : Blo 1736569 5861969 := bstep (se 2 (by rfl) ⟨2198238, by rfl⟩ : syracuseStep 5861969 = 4396477) B4396477
theorem B3297905 : Blo 1736569 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B1954435 : Blo 1736569 1954435 := bstep (se 1 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 1954435 = 2931653) B2931653
theorem B2781859 : Blo 1736569 2781859 := bstep (se 1 (by rfl) ⟨2086394, by rfl⟩ : syracuseStep 2781859 = 4172789) B4172789
theorem B11129507 : Blo 1736569 11129507 := bstep (se 1 (by rfl) ⟨8347130, by rfl⟩ : syracuseStep 11129507 = 16694261) B16694261
theorem B30085829 : Blo 1736569 30085829 := bstep (se 4 (by rfl) ⟨2820546, by rfl⟩ : syracuseStep 30085829 = 5641093) B5641093
theorem B4395779 : Blo 1736569 4395779 := bstep (se 1 (by rfl) ⟨3296834, by rfl⟩ : syracuseStep 4395779 = 6593669) B6593669
theorem B13202189 : Blo 1736569 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B1954579 : Blo 1736569 1954579 := bstep (se 1 (by rfl) ⟨1465934, by rfl⟩ : syracuseStep 1954579 = 2931869) B2931869
theorem B6599501 : Blo 1736569 6599501 := bstep (se 3 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 6599501 = 2474813) B2474813
theorem B8794979 : Blo 1736569 8794979 := bstep (se 1 (by rfl) ⟨6596234, by rfl⟩ : syracuseStep 8794979 = 13192469) B13192469
theorem B9900913 : Blo 1736569 9900913 := bstep (se 2 (by rfl) ⟨3712842, by rfl⟩ : syracuseStep 9900913 = 7425685) B7425685
theorem B53523341 : Blo 1736569 53523341 := bstep (se 3 (by rfl) ⟨10035626, by rfl⟩ : syracuseStep 53523341 = 20071253) B20071253
theorem B2782115 : Blo 1736569 2782115 := bstep (se 1 (by rfl) ⟨2086586, by rfl⟩ : syracuseStep 2782115 = 4173173) B4173173
theorem B1954723 : Blo 1736569 1954723 := bstep (se 1 (by rfl) ⟨1466042, by rfl⟩ : syracuseStep 1954723 = 2932085) B2932085
theorem B10572707 : Blo 1736569 10572707 := bstep (se 1 (by rfl) ⟨7929530, by rfl⟩ : syracuseStep 10572707 = 15859061) B15859061
theorem B4395971 : Blo 1736569 4395971 := bstep (se 1 (by rfl) ⟨3296978, by rfl⟩ : syracuseStep 4395971 = 6593957) B6593957
theorem B4174865 : Blo 1736569 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B1954867 : Blo 1736569 1954867 := bstep (se 1 (by rfl) ⟨1466150, by rfl⟩ : syracuseStep 1954867 = 2932301) B2932301
theorem B13554787 : Blo 1736569 13554787 := bstep (se 1 (by rfl) ⟨10166090, by rfl⟩ : syracuseStep 13554787 = 20332181) B20332181
theorem B5862509 : Blo 1736569 5862509 := bstep (se 3 (by rfl) ⟨1099220, by rfl⟩ : syracuseStep 5862509 = 2198441) B2198441
theorem B5862563 : Blo 1736569 5862563 := bstep (se 1 (by rfl) ⟨4396922, by rfl⟩ : syracuseStep 5862563 = 8793845) B8793845
theorem B1955011 : Blo 1736569 1955011 := bstep (se 1 (by rfl) ⟨1466258, by rfl⟩ : syracuseStep 1955011 = 2932517) B2932517
theorem B8352973 : Blo 1736569 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B2970947 : Blo 1736569 2970947 := bstep (se 1 (by rfl) ⟨2228210, by rfl⟩ : syracuseStep 2970947 = 4456421) B4456421
theorem B1955155 : Blo 1736569 1955155 := bstep (se 1 (by rfl) ⟨1466366, by rfl⟩ : syracuseStep 1955155 = 2932733) B2932733
theorem B5862833 : Blo 1736569 5862833 := bstep (se 2 (by rfl) ⟨2198562, by rfl⟩ : syracuseStep 5862833 = 4397125) B4397125
theorem B1955299 : Blo 1736569 1955299 := bstep (se 1 (by rfl) ⟨1466474, by rfl⟩ : syracuseStep 1955299 = 2932949) B2932949
theorem B3298801 : Blo 1736569 3298801 := bstep (se 2 (by rfl) ⟨1237050, by rfl⟩ : syracuseStep 3298801 = 2474101) B2474101
theorem B5281283 : Blo 1736569 5281283 := bstep (se 1 (by rfl) ⟨3960962, by rfl⟩ : syracuseStep 5281283 = 7921925) B7921925
theorem B2348561 : Blo 1736569 2348561 := bstep (se 2 (by rfl) ⟨880710, by rfl⟩ : syracuseStep 2348561 = 1761421) B1761421
theorem B6108739 : Blo 1736569 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B21132913 : Blo 1736569 21132913 := bstep (se 2 (by rfl) ⟨7924842, by rfl⟩ : syracuseStep 21132913 = 15849685) B15849685
theorem B6600305 : Blo 1736569 6600305 := bstep (se 2 (by rfl) ⟨2475114, by rfl⟩ : syracuseStep 6600305 = 4950229) B4950229
theorem B1955443 : Blo 1736569 1955443 := bstep (se 1 (by rfl) ⟨1466582, by rfl⟩ : syracuseStep 1955443 = 2933165) B2933165
theorem B8795789 : Blo 1736569 8795789 := bstep (se 3 (by rfl) ⟨1649210, by rfl⟩ : syracuseStep 8795789 = 3298421) B3298421
theorem B3298961 : Blo 1736569 3298961 := bstep (se 2 (by rfl) ⟨1237110, by rfl⟩ : syracuseStep 3298961 = 2474221) B2474221
theorem B2348723 : Blo 1736569 2348723 := bstep (se 1 (by rfl) ⟨1761542, by rfl⟩ : syracuseStep 2348723 = 3523085) B3523085
theorem B1955587 : Blo 1736569 1955587 := bstep (se 1 (by rfl) ⟨1466690, by rfl⟩ : syracuseStep 1955587 = 2933381) B2933381
theorem B4175633 : Blo 1736569 4175633 := bstep (se 2 (by rfl) ⟨1565862, by rfl⟩ : syracuseStep 4175633 = 3131725) B3131725
theorem B2930465 : Blo 1736569 2930465 := bstep (se 2 (by rfl) ⟨1098924, by rfl⟩ : syracuseStep 2930465 = 2197849) B2197849
theorem B4396913 : Blo 1736569 4396913 := bstep (se 2 (by rfl) ⟨1648842, by rfl⟩ : syracuseStep 4396913 = 3297685) B3297685
theorem B2783089 : Blo 1736569 2783089 := bstep (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) B2087317
theorem B11884421 : Blo 1736569 11884421 := bstep (se 4 (by rfl) ⟨1114164, by rfl⟩ : syracuseStep 11884421 = 2228329) B2228329
theorem B1955731 : Blo 1736569 1955731 := bstep (se 1 (by rfl) ⟨1466798, by rfl⟩ : syracuseStep 1955731 = 2933597) B2933597
theorem B2930593 : Blo 1736569 2930593 := bstep (se 2 (by rfl) ⟨1098972, by rfl⟩ : syracuseStep 2930593 = 2197945) B2197945
theorem B4396963 : Blo 1736569 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B2930627 : Blo 1736569 2930627 := bstep (se 1 (by rfl) ⟨2197970, by rfl⟩ : syracuseStep 2930627 = 4395941) B4395941
theorem B5863373 : Blo 1736569 5863373 := bstep (se 3 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 5863373 = 2198765) B2198765
theorem B18085859 : Blo 1736569 18085859 := bstep (se 1 (by rfl) ⟨13564394, by rfl⟩ : syracuseStep 18085859 = 27128789) B27128789
theorem B7043057 : Blo 1736569 7043057 := bstep (se 2 (by rfl) ⟨2641146, by rfl⟩ : syracuseStep 7043057 = 5282293) B5282293
theorem B5568497 : Blo 1736569 5568497 := bstep (se 2 (by rfl) ⟨2088186, by rfl⟩ : syracuseStep 5568497 = 4176373) B4176373
theorem B5863427 : Blo 1736569 5863427 := bstep (se 1 (by rfl) ⟨4397570, by rfl⟩ : syracuseStep 5863427 = 8795141) B8795141
theorem B3299363 : Blo 1736569 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B5568547 : Blo 1736569 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B1955875 : Blo 1736569 1955875 := bstep (se 1 (by rfl) ⟨1466906, by rfl⟩ : syracuseStep 1955875 = 2933813) B2933813
theorem B4397105 : Blo 1736569 4397105 := bstep (se 2 (by rfl) ⟨1648914, by rfl⟩ : syracuseStep 4397105 = 3297829) B3297829
theorem B35665973 : Blo 1736569 35665973 := bstep (se 5 (by rfl) ⟨1671842, by rfl⟩ : syracuseStep 35665973 = 3343685) B3343685
theorem B2930755 : Blo 1736569 2930755 := bstep (se 1 (by rfl) ⟨2198066, by rfl⟩ : syracuseStep 2930755 = 4396133) B4396133
theorem B7420081 : Blo 1736569 7420081 := bstep (se 2 (by rfl) ⟨2782530, by rfl⟩ : syracuseStep 7420081 = 5565061) B5565061
theorem B2930897 : Blo 1736569 2930897 := bstep (se 2 (by rfl) ⟨1099086, by rfl⟩ : syracuseStep 2930897 = 2198173) B2198173
theorem B4946129 : Blo 1736569 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B1906931 : Blo 1736569 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B9894149 : Blo 1736569 9894149 := bstep (se 4 (by rfl) ⟨927576, by rfl⟩ : syracuseStep 9894149 = 1855153) B1855153
theorem B6600973 : Blo 1736569 6600973 := bstep (se 3 (by rfl) ⟨1237682, by rfl⟩ : syracuseStep 6600973 = 2475365) B2475365
theorem B5863697 : Blo 1736569 5863697 := bstep (se 2 (by rfl) ⟨2198886, by rfl⟩ : syracuseStep 5863697 = 4397773) B4397773
theorem B4520209 : Blo 1736569 4520209 := bstep (se 2 (by rfl) ⟨1695078, by rfl⟩ : syracuseStep 4520209 = 3390157) B3390157
theorem B5945645 : Blo 1736569 5945645 := bstep (se 3 (by rfl) ⟨1114808, by rfl⟩ : syracuseStep 5945645 = 2229617) B2229617
theorem B9394481 : Blo 1736569 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B2931025 : Blo 1736569 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B8919409 : Blo 1736569 8919409 := bstep (se 2 (by rfl) ⟨3344778, by rfl⟩ : syracuseStep 8919409 = 6689557) B6689557
theorem B2931059 : Blo 1736569 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B2972035 : Blo 1736569 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B3520945 : Blo 1736569 3520945 := bstep (se 2 (by rfl) ⟨1320354, by rfl⟩ : syracuseStep 3520945 = 2640709) B2640709
theorem B3521009 : Blo 1736569 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B2931187 : Blo 1736569 2931187 := bstep (se 1 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 2931187 = 4396781) B4396781
theorem B2931329 : Blo 1736569 2931329 := bstep (se 2 (by rfl) ⟨1099248, by rfl⟩ : syracuseStep 2931329 = 2198497) B2198497
theorem B9394829 : Blo 1736569 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B2472643 : Blo 1736569 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B2972371 : Blo 1736569 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B2931457 : Blo 1736569 2931457 := bstep (se 2 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 2931457 = 2198593) B2198593
theorem B2784017 : Blo 1736569 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B2931491 : Blo 1736569 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B5864237 : Blo 1736569 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B5864291 : Blo 1736569 5864291 := bstep (se 1 (by rfl) ⟨4398218, by rfl⟩ : syracuseStep 5864291 = 8796437) B8796437
theorem B5569393 : Blo 1736569 5569393 := bstep (se 2 (by rfl) ⟨2088522, by rfl⟩ : syracuseStep 5569393 = 4177045) B4177045
theorem B5282705 : Blo 1736569 5282705 := bstep (se 2 (by rfl) ⟨1981014, by rfl⟩ : syracuseStep 5282705 = 3962029) B3962029
theorem B2931619 : Blo 1736569 2931619 := bstep (se 1 (by rfl) ⟨2198714, by rfl⟩ : syracuseStep 2931619 = 4397429) B4397429
theorem B3300259 : Blo 1736569 3300259 := bstep (se 1 (by rfl) ⟨2475194, by rfl⟩ : syracuseStep 3300259 = 4950389) B4950389
theorem B2202611 : Blo 1736569 2202611 := bstep (se 1 (by rfl) ⟨1651958, by rfl⟩ : syracuseStep 2202611 = 3303917) B3303917
theorem B4398097 : Blo 1736569 4398097 := bstep (se 2 (by rfl) ⟨1649286, by rfl⟩ : syracuseStep 4398097 = 3298573) B3298573
theorem B2931761 : Blo 1736569 2931761 := bstep (se 2 (by rfl) ⟨1099410, by rfl⟩ : syracuseStep 2931761 = 2198821) B2198821
theorem B3300419 : Blo 1736569 3300419 := bstep (se 1 (by rfl) ⟨2475314, by rfl⟩ : syracuseStep 3300419 = 4950629) B4950629
theorem B13196357 : Blo 1736569 13196357 := bstep (se 4 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 13196357 = 2474317) B2474317
theorem B3710033 : Blo 1736569 3710033 := bstep (se 2 (by rfl) ⟨1391262, by rfl⟩ : syracuseStep 3710033 = 2782525) B2782525
theorem B5864561 : Blo 1736569 5864561 := bstep (se 2 (by rfl) ⟨2199210, by rfl⟩ : syracuseStep 5864561 = 4398421) B4398421
theorem B4947085 : Blo 1736569 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B2931889 : Blo 1736569 2931889 := bstep (se 2 (by rfl) ⟨1099458, by rfl⟩ : syracuseStep 2931889 = 2198917) B2198917
theorem B2931923 : Blo 1736569 2931923 := bstep (se 1 (by rfl) ⟨2198942, by rfl⟩ : syracuseStep 2931923 = 4397885) B4397885
theorem B2473201 : Blo 1736569 2473201 := bstep (se 2 (by rfl) ⟨927450, by rfl⟩ : syracuseStep 2473201 = 1854901) B1854901
theorem B4398371 : Blo 1736569 4398371 := bstep (se 1 (by rfl) ⟨3298778, by rfl⟩ : syracuseStep 4398371 = 6597557) B6597557
theorem B2932051 : Blo 1736569 2932051 := bstep (se 1 (by rfl) ⟨2199038, by rfl⟩ : syracuseStep 2932051 = 4398077) B4398077
theorem B4947313 : Blo 1736569 4947313 := bstep (se 2 (by rfl) ⟨1855242, by rfl⟩ : syracuseStep 4947313 = 3710485) B3710485
theorem B32128397 : Blo 1736569 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B2088355 : Blo 1736569 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B2932193 : Blo 1736569 2932193 := bstep (se 2 (by rfl) ⟨1099572, by rfl⟩ : syracuseStep 2932193 = 2199145) B2199145
theorem B4398563 : Blo 1736569 4398563 := bstep (se 1 (by rfl) ⟨3298922, by rfl⟩ : syracuseStep 4398563 = 6597845) B6597845
theorem B4947473 : Blo 1736569 4947473 := bstep (se 2 (by rfl) ⟨1855302, by rfl⟩ : syracuseStep 4947473 = 3710605) B3710605
theorem B8347171 : Blo 1736569 8347171 := bstep (se 1 (by rfl) ⟨6260378, by rfl⟩ : syracuseStep 8347171 = 12520757) B12520757
theorem B2784851 : Blo 1736569 2784851 := bstep (se 1 (by rfl) ⟨2088638, by rfl⟩ : syracuseStep 2784851 = 4177277) B4177277
theorem B2932321 : Blo 1736569 2932321 := bstep (se 2 (by rfl) ⟨1099620, by rfl⟩ : syracuseStep 2932321 = 2199241) B2199241
theorem B11886193 : Blo 1736569 11886193 := bstep (se 2 (by rfl) ⟨4457322, by rfl⟩ : syracuseStep 11886193 = 8914645) B8914645
theorem B4947587 : Blo 1736569 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B2932355 : Blo 1736569 2932355 := bstep (se 1 (by rfl) ⟨2199266, by rfl⟩ : syracuseStep 2932355 = 4398533) B4398533
theorem B11280005 : Blo 1736569 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B5865101 : Blo 1736569 5865101 := bstep (se 3 (by rfl) ⟨1099706, by rfl⟩ : syracuseStep 5865101 = 2199413) B2199413
theorem B5865155 : Blo 1736569 5865155 := bstep (se 1 (by rfl) ⟨4398866, by rfl⟩ : syracuseStep 5865155 = 8797733) B8797733
theorem B14851781 : Blo 1736569 14851781 := bstep (se 4 (by rfl) ⟨1392354, by rfl⟩ : syracuseStep 14851781 = 2784709) B2784709
theorem B3907313 : Blo 1736569 3907313 := bstep (se 2 (by rfl) ⟨1465242, by rfl⟩ : syracuseStep 3907313 = 2930485) B2930485
theorem B3907331 : Blo 1736569 3907331 := bstep (se 1 (by rfl) ⟨2930498, by rfl⟩ : syracuseStep 3907331 = 5860997) B5860997
theorem B2932483 : Blo 1736569 2932483 := bstep (se 1 (by rfl) ⟨2199362, by rfl⟩ : syracuseStep 2932483 = 4398725) B4398725
theorem B2604881 : Blo 1736569 2604881 := bstep (se 2 (by rfl) ⟨976830, by rfl⟩ : syracuseStep 2604881 = 1953661) B1953661
theorem B2604899 : Blo 1736569 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B11894627 : Blo 1736569 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B2604929 : Blo 1736569 2604929 := bstep (se 2 (by rfl) ⟨976848, by rfl⟩ : syracuseStep 2604929 = 1953697) B1953697
theorem B1736579 : Blo 1736569 1736579 := bstep (se 1 (by rfl) ⟨1302434, by rfl⟩ : syracuseStep 1736579 = 2604869) B2604869
theorem B2932625 : Blo 1736569 2932625 := bstep (se 2 (by rfl) ⟨1099734, by rfl⟩ : syracuseStep 2932625 = 2199469) B2199469
theorem B1736595 : Blo 1736569 1736595 := bstep (se 1 (by rfl) ⟨1302446, by rfl⟩ : syracuseStep 1736595 = 2604893) B2604893
theorem B2604947 : Blo 1736569 2604947 := bstep (se 1 (by rfl) ⟨1953710, by rfl⟩ : syracuseStep 2604947 = 3907421) B3907421
theorem B1736611 : Blo 1736569 1736611 := bstep (se 1 (by rfl) ⟨1302458, by rfl⟩ : syracuseStep 1736611 = 2604917) B2604917
theorem B2604977 : Blo 1736569 2604977 := bstep (se 2 (by rfl) ⟨976866, by rfl⟩ : syracuseStep 2604977 = 1953733) B1953733
theorem B1736627 : Blo 1736569 1736627 := bstep (se 1 (by rfl) ⟨1302470, by rfl⟩ : syracuseStep 1736627 = 2604941) B2604941
theorem B2473907 : Blo 1736569 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1736643 : Blo 1736569 1736643 := bstep (se 1 (by rfl) ⟨1302482, by rfl⟩ : syracuseStep 1736643 = 2604965) B2604965
theorem B2604995 : Blo 1736569 2604995 := bstep (se 1 (by rfl) ⟨1953746, by rfl⟩ : syracuseStep 2604995 = 3907493) B3907493
theorem B3710929 : Blo 1736569 3710929 := bstep (se 2 (by rfl) ⟨1391598, by rfl⟩ : syracuseStep 3710929 = 2783197) B2783197
theorem B1736659 : Blo 1736569 1736659 := bstep (se 1 (by rfl) ⟨1302494, by rfl⟩ : syracuseStep 1736659 = 2604989) B2604989
theorem B5865425 : Blo 1736569 5865425 := bstep (se 2 (by rfl) ⟨2199534, by rfl⟩ : syracuseStep 5865425 = 4399069) B4399069
theorem B2605025 : Blo 1736569 2605025 := bstep (se 2 (by rfl) ⟨976884, by rfl⟩ : syracuseStep 2605025 = 1953769) B1953769
theorem B1736675 : Blo 1736569 1736675 := bstep (se 1 (by rfl) ⟨1302506, by rfl⟩ : syracuseStep 1736675 = 2605013) B2605013
theorem B3710947 : Blo 1736569 3710947 := bstep (se 1 (by rfl) ⟨2783210, by rfl⟩ : syracuseStep 3710947 = 5566421) B5566421
theorem B1736691 : Blo 1736569 1736691 := bstep (se 1 (by rfl) ⟨1302518, by rfl⟩ : syracuseStep 1736691 = 2605037) B2605037
theorem B2605043 : Blo 1736569 2605043 := bstep (se 1 (by rfl) ⟨1953782, by rfl⟩ : syracuseStep 2605043 = 3907565) B3907565
theorem B2605067 : Blo 1736569 2605067 := bstep (se 1 (by rfl) ⟨1953800, by rfl⟩ : syracuseStep 2605067 = 3907601) B3907601
theorem B1736715 : Blo 1736569 1736715 := bstep (se 1 (by rfl) ⟨1302536, by rfl⟩ : syracuseStep 1736715 = 2605073) B2605073
theorem B13197329 : Blo 1736569 13197329 := bstep (se 2 (by rfl) ⟨4948998, by rfl⟩ : syracuseStep 13197329 = 9897997) B9897997
theorem B3129367 : Blo 1736569 3129367 := bstep (se 1 (by rfl) ⟨2347025, by rfl⟩ : syracuseStep 3129367 = 4694051) B4694051
theorem B2605079 : Blo 1736569 2605079 := bstep (se 1 (by rfl) ⟨1953809, by rfl⟩ : syracuseStep 2605079 = 3907619) B3907619
theorem B1736727 : Blo 1736569 1736727 := bstep (se 1 (by rfl) ⟨1302545, by rfl⟩ : syracuseStep 1736727 = 2605091) B2605091
theorem B1736747 : Blo 1736569 1736747 := bstep (se 1 (by rfl) ⟨1302560, by rfl⟩ : syracuseStep 1736747 = 2605121) B2605121
theorem B1736759 : Blo 1736569 1736759 := bstep (se 1 (by rfl) ⟨1302569, by rfl⟩ : syracuseStep 1736759 = 2605139) B2605139
theorem B1736779 : Blo 1736569 1736779 := bstep (se 1 (by rfl) ⟨1302584, by rfl⟩ : syracuseStep 1736779 = 2605169) B2605169
theorem B1736791 : Blo 1736569 1736791 := bstep (se 1 (by rfl) ⟨1302593, by rfl⟩ : syracuseStep 1736791 = 2605187) B2605187
theorem B3907673 : Blo 1736569 3907673 := bstep (se 2 (by rfl) ⟨1465377, by rfl⟩ : syracuseStep 3907673 = 2930755) B2930755
theorem B2605145 : Blo 1736569 2605145 := bstep (se 2 (by rfl) ⟨976929, by rfl⟩ : syracuseStep 2605145 = 1953859) B1953859
theorem B1736811 : Blo 1736569 1736811 := bstep (se 1 (by rfl) ⟨1302608, by rfl⟩ : syracuseStep 1736811 = 2605217) B2605217
theorem B1736823 : Blo 1736569 1736823 := bstep (se 1 (by rfl) ⟨1302617, by rfl⟩ : syracuseStep 1736823 = 2605235) B2605235
theorem B1736843 : Blo 1736569 1736843 := bstep (se 1 (by rfl) ⟨1302632, by rfl⟩ : syracuseStep 1736843 = 2605265) B2605265
theorem B1736855 : Blo 1736569 1736855 := bstep (se 1 (by rfl) ⟨1302641, by rfl⟩ : syracuseStep 1736855 = 2605283) B2605283
theorem B1736875 : Blo 1736569 1736875 := bstep (se 1 (by rfl) ⟨1302656, by rfl⟩ : syracuseStep 1736875 = 2605313) B2605313
theorem B3907763 : Blo 1736569 3907763 := bstep (se 1 (by rfl) ⟨2930822, by rfl⟩ : syracuseStep 3907763 = 5861645) B5861645
theorem B7422131 : Blo 1736569 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B1736887 : Blo 1736569 1736887 := bstep (se 1 (by rfl) ⟨1302665, by rfl⟩ : syracuseStep 1736887 = 2605331) B2605331
theorem B2605259 : Blo 1736569 2605259 := bstep (se 1 (by rfl) ⟨1953944, by rfl⟩ : syracuseStep 2605259 = 3907889) B3907889
theorem B1736907 : Blo 1736569 1736907 := bstep (se 1 (by rfl) ⟨1302680, by rfl⟩ : syracuseStep 1736907 = 2605361) B2605361
theorem B3907799 : Blo 1736569 3907799 := bstep (se 1 (by rfl) ⟨2930849, by rfl⟩ : syracuseStep 3907799 = 5861699) B5861699
theorem B2605271 : Blo 1736569 2605271 := bstep (se 1 (by rfl) ⟨1953953, by rfl⟩ : syracuseStep 2605271 = 3907907) B3907907
theorem B1736919 : Blo 1736569 1736919 := bstep (se 1 (by rfl) ⟨1302689, by rfl⟩ : syracuseStep 1736919 = 2605379) B2605379
theorem B5357789 : Blo 1736569 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B1736939 : Blo 1736569 1736939 := bstep (se 1 (by rfl) ⟨1302704, by rfl⟩ : syracuseStep 1736939 = 2605409) B2605409
theorem B1736951 : Blo 1736569 1736951 := bstep (se 1 (by rfl) ⟨1302713, by rfl⟩ : syracuseStep 1736951 = 2605427) B2605427
theorem B1736971 : Blo 1736569 1736971 := bstep (se 1 (by rfl) ⟨1302728, by rfl⟩ : syracuseStep 1736971 = 2605457) B2605457
theorem B2933003 : Blo 1736569 2933003 := bstep (se 1 (by rfl) ⟨2199752, by rfl⟩ : syracuseStep 2933003 = 4399505) B4399505
theorem B1736983 : Blo 1736569 1736983 := bstep (se 1 (by rfl) ⟨1302737, by rfl⟩ : syracuseStep 1736983 = 2605475) B2605475
theorem B2605337 : Blo 1736569 2605337 := bstep (se 2 (by rfl) ⟨977001, by rfl⟩ : syracuseStep 2605337 = 1954003) B1954003
theorem B1737003 : Blo 1736569 1737003 := bstep (se 1 (by rfl) ⟨1302752, by rfl⟩ : syracuseStep 1737003 = 2605505) B2605505
theorem B1737015 : Blo 1736569 1737015 := bstep (se 1 (by rfl) ⟨1302761, by rfl⟩ : syracuseStep 1737015 = 2605523) B2605523
theorem B1737035 : Blo 1736569 1737035 := bstep (se 1 (by rfl) ⟨1302776, by rfl⟩ : syracuseStep 1737035 = 2605553) B2605553
theorem B5865803 : Blo 1736569 5865803 := bstep (se 1 (by rfl) ⟨4399352, by rfl⟩ : syracuseStep 5865803 = 8798705) B8798705
theorem B1737047 : Blo 1736569 1737047 := bstep (se 1 (by rfl) ⟨1302785, by rfl⟩ : syracuseStep 1737047 = 2605571) B2605571
theorem B2474329 : Blo 1736569 2474329 := bstep (se 2 (by rfl) ⟨927873, by rfl⟩ : syracuseStep 2474329 = 1855747) B1855747
theorem B14836061 : Blo 1736569 14836061 := bstep (se 3 (by rfl) ⟨2781761, by rfl⟩ : syracuseStep 14836061 = 5563523) B5563523
theorem B32579941 : Blo 1736569 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B1737067 : Blo 1736569 1737067 := bstep (se 1 (by rfl) ⟨1302800, by rfl⟩ : syracuseStep 1737067 = 2605601) B2605601
theorem B1737079 : Blo 1736569 1737079 := bstep (se 1 (by rfl) ⟨1302809, by rfl⟩ : syracuseStep 1737079 = 2605619) B2605619
theorem B3907979 : Blo 1736569 3907979 := bstep (se 1 (by rfl) ⟨2930984, by rfl⟩ : syracuseStep 3907979 = 5861969) B5861969
theorem B2605451 : Blo 1736569 2605451 := bstep (se 1 (by rfl) ⟨1954088, by rfl⟩ : syracuseStep 2605451 = 3908177) B3908177
theorem B1737099 : Blo 1736569 1737099 := bstep (se 1 (by rfl) ⟨1302824, by rfl⟩ : syracuseStep 1737099 = 2605649) B2605649
theorem B2933131 : Blo 1736569 2933131 := bstep (se 1 (by rfl) ⟨2199848, by rfl⟩ : syracuseStep 2933131 = 4399697) B4399697
theorem B2605463 : Blo 1736569 2605463 := bstep (se 1 (by rfl) ⟨1954097, by rfl⟩ : syracuseStep 2605463 = 3908195) B3908195
theorem B1737111 : Blo 1736569 1737111 := bstep (se 1 (by rfl) ⟨1302833, by rfl⟩ : syracuseStep 1737111 = 2605667) B2605667
theorem B1737131 : Blo 1736569 1737131 := bstep (se 1 (by rfl) ⟨1302848, by rfl⟩ : syracuseStep 1737131 = 2605697) B2605697
theorem B13189553 : Blo 1736569 13189553 := bstep (se 2 (by rfl) ⟨4946082, by rfl⟩ : syracuseStep 13189553 = 9892165) B9892165
theorem B1737143 : Blo 1736569 1737143 := bstep (se 1 (by rfl) ⟨1302857, by rfl⟩ : syracuseStep 1737143 = 2605715) B2605715
theorem B3908033 : Blo 1736569 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B1737163 : Blo 1736569 1737163 := bstep (se 1 (by rfl) ⟨1302872, by rfl⟩ : syracuseStep 1737163 = 2605745) B2605745
theorem B1737175 : Blo 1736569 1737175 := bstep (se 1 (by rfl) ⟨1302881, by rfl⟩ : syracuseStep 1737175 = 2605763) B2605763
theorem B2605529 : Blo 1736569 2605529 := bstep (se 2 (by rfl) ⟨977073, by rfl⟩ : syracuseStep 2605529 = 1954147) B1954147
theorem B1737195 : Blo 1736569 1737195 := bstep (se 1 (by rfl) ⟨1302896, by rfl⟩ : syracuseStep 1737195 = 2605793) B2605793
theorem B1737207 : Blo 1736569 1737207 := bstep (se 1 (by rfl) ⟨1302905, by rfl⟩ : syracuseStep 1737207 = 2605811) B2605811
theorem B1737227 : Blo 1736569 1737227 := bstep (se 1 (by rfl) ⟨1302920, by rfl⟩ : syracuseStep 1737227 = 2605841) B2605841
theorem B1737239 : Blo 1736569 1737239 := bstep (se 1 (by rfl) ⟨1302929, by rfl⟩ : syracuseStep 1737239 = 2605859) B2605859
theorem B2933273 : Blo 1736569 2933273 := bstep (se 2 (by rfl) ⟨1099977, by rfl⟩ : syracuseStep 2933273 = 2199955) B2199955
theorem B1737259 : Blo 1736569 1737259 := bstep (se 1 (by rfl) ⟨1302944, by rfl⟩ : syracuseStep 1737259 = 2605889) B2605889
theorem B4399667 : Blo 1736569 4399667 := bstep (se 1 (by rfl) ⟨3299750, by rfl⟩ : syracuseStep 4399667 = 6599501) B6599501
theorem B1737271 : Blo 1736569 1737271 := bstep (se 1 (by rfl) ⟨1302953, by rfl⟩ : syracuseStep 1737271 = 2605907) B2605907
theorem B4694593 : Blo 1736569 4694593 := bstep (se 2 (by rfl) ⟨1760472, by rfl⟩ : syracuseStep 4694593 = 3520945) B3520945
theorem B2605643 : Blo 1736569 2605643 := bstep (se 1 (by rfl) ⟨1954232, by rfl⟩ : syracuseStep 2605643 = 3908465) B3908465
theorem B1737291 : Blo 1736569 1737291 := bstep (se 1 (by rfl) ⟨1302968, by rfl⟩ : syracuseStep 1737291 = 2605937) B2605937
theorem B2605655 : Blo 1736569 2605655 := bstep (se 1 (by rfl) ⟨1954241, by rfl⟩ : syracuseStep 2605655 = 3908483) B3908483
theorem B1737303 : Blo 1736569 1737303 := bstep (se 1 (by rfl) ⟨1302977, by rfl⟩ : syracuseStep 1737303 = 2605955) B2605955
theorem B5866073 : Blo 1736569 5866073 := bstep (se 2 (by rfl) ⟨2199777, by rfl⟩ : syracuseStep 5866073 = 4399555) B4399555
theorem B1737323 : Blo 1736569 1737323 := bstep (se 1 (by rfl) ⟨1302992, by rfl⟩ : syracuseStep 1737323 = 2605985) B2605985
theorem B1737335 : Blo 1736569 1737335 := bstep (se 1 (by rfl) ⟨1303001, by rfl⟩ : syracuseStep 1737335 = 2606003) B2606003
theorem B1737355 : Blo 1736569 1737355 := bstep (se 1 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 1737355 = 2606033) B2606033
theorem B1737367 : Blo 1736569 1737367 := bstep (se 1 (by rfl) ⟨1303025, by rfl⟩ : syracuseStep 1737367 = 2606051) B2606051
theorem B3908249 : Blo 1736569 3908249 := bstep (se 2 (by rfl) ⟨1465593, by rfl⟩ : syracuseStep 3908249 = 2931187) B2931187
theorem B2605721 : Blo 1736569 2605721 := bstep (se 2 (by rfl) ⟨977145, by rfl⟩ : syracuseStep 2605721 = 1954291) B1954291
theorem B2933401 : Blo 1736569 2933401 := bstep (se 2 (by rfl) ⟨1100025, by rfl⟩ : syracuseStep 2933401 = 2200051) B2200051
theorem B1737387 : Blo 1736569 1737387 := bstep (se 1 (by rfl) ⟨1303040, by rfl⟩ : syracuseStep 1737387 = 2606081) B2606081
theorem B1737399 : Blo 1736569 1737399 := bstep (se 1 (by rfl) ⟨1303049, by rfl⟩ : syracuseStep 1737399 = 2606099) B2606099
theorem B1737419 : Blo 1736569 1737419 := bstep (se 1 (by rfl) ⟨1303064, by rfl⟩ : syracuseStep 1737419 = 2606129) B2606129
theorem B1737431 : Blo 1736569 1737431 := bstep (se 1 (by rfl) ⟨1303073, by rfl⟩ : syracuseStep 1737431 = 2606147) B2606147
theorem B1737451 : Blo 1736569 1737451 := bstep (se 1 (by rfl) ⟨1303088, by rfl⟩ : syracuseStep 1737451 = 2606177) B2606177
theorem B3908339 : Blo 1736569 3908339 := bstep (se 1 (by rfl) ⟨2931254, by rfl⟩ : syracuseStep 3908339 = 5862509) B5862509
theorem B1737463 : Blo 1736569 1737463 := bstep (se 1 (by rfl) ⟨1303097, by rfl⟩ : syracuseStep 1737463 = 2606195) B2606195
theorem B2605835 : Blo 1736569 2605835 := bstep (se 1 (by rfl) ⟨1954376, by rfl⟩ : syracuseStep 2605835 = 3908753) B3908753
theorem B1737483 : Blo 1736569 1737483 := bstep (se 1 (by rfl) ⟨1303112, by rfl⟩ : syracuseStep 1737483 = 2606225) B2606225
theorem B3908375 : Blo 1736569 3908375 := bstep (se 1 (by rfl) ⟨2931281, by rfl⟩ : syracuseStep 3908375 = 5862563) B5862563
theorem B2605847 : Blo 1736569 2605847 := bstep (se 1 (by rfl) ⟨1954385, by rfl⟩ : syracuseStep 2605847 = 3908771) B3908771
theorem B1737495 : Blo 1736569 1737495 := bstep (se 1 (by rfl) ⟨1303121, by rfl⟩ : syracuseStep 1737495 = 2606243) B2606243
theorem B1737515 : Blo 1736569 1737515 := bstep (se 1 (by rfl) ⟨1303136, by rfl⟩ : syracuseStep 1737515 = 2606273) B2606273
theorem B25051949 : Blo 1736569 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B1737527 : Blo 1736569 1737527 := bstep (se 1 (by rfl) ⟨1303145, by rfl⟩ : syracuseStep 1737527 = 2606291) B2606291
theorem B1737547 : Blo 1736569 1737547 := bstep (se 1 (by rfl) ⟨1303160, by rfl⟩ : syracuseStep 1737547 = 2606321) B2606321
theorem B1737559 : Blo 1736569 1737559 := bstep (se 1 (by rfl) ⟨1303169, by rfl⟩ : syracuseStep 1737559 = 2606339) B2606339
theorem B2605913 : Blo 1736569 2605913 := bstep (se 2 (by rfl) ⟨977217, by rfl⟩ : syracuseStep 2605913 = 1954435) B1954435
theorem B25052003 : Blo 1736569 25052003 := bstep (se 1 (by rfl) ⟨18789002, by rfl⟩ : syracuseStep 25052003 = 37578005) B37578005
theorem B1737579 : Blo 1736569 1737579 := bstep (se 1 (by rfl) ⟨1303184, by rfl⟩ : syracuseStep 1737579 = 2606369) B2606369
theorem B1737591 : Blo 1736569 1737591 := bstep (se 1 (by rfl) ⟨1303193, by rfl⟩ : syracuseStep 1737591 = 2606387) B2606387
theorem B1737611 : Blo 1736569 1737611 := bstep (se 1 (by rfl) ⟨1303208, by rfl⟩ : syracuseStep 1737611 = 2606417) B2606417
theorem B13190039 : Blo 1736569 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B1737623 : Blo 1736569 1737623 := bstep (se 1 (by rfl) ⟨1303217, by rfl⟩ : syracuseStep 1737623 = 2606435) B2606435
theorem B1737643 : Blo 1736569 1737643 := bstep (se 1 (by rfl) ⟨1303232, by rfl⟩ : syracuseStep 1737643 = 2606465) B2606465
theorem B1737655 : Blo 1736569 1737655 := bstep (se 1 (by rfl) ⟨1303241, by rfl⟩ : syracuseStep 1737655 = 2606483) B2606483
theorem B3908555 : Blo 1736569 3908555 := bstep (se 1 (by rfl) ⟨2931416, by rfl⟩ : syracuseStep 3908555 = 5862833) B5862833
theorem B2606027 : Blo 1736569 2606027 := bstep (se 1 (by rfl) ⟨1954520, by rfl⟩ : syracuseStep 2606027 = 3909041) B3909041
theorem B1737675 : Blo 1736569 1737675 := bstep (se 1 (by rfl) ⟨1303256, by rfl⟩ : syracuseStep 1737675 = 2606513) B2606513
theorem B2606039 : Blo 1736569 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B1737687 : Blo 1736569 1737687 := bstep (se 1 (by rfl) ⟨1303265, by rfl⟩ : syracuseStep 1737687 = 2606531) B2606531
theorem B1737707 : Blo 1736569 1737707 := bstep (se 1 (by rfl) ⟨1303280, by rfl⟩ : syracuseStep 1737707 = 2606561) B2606561
theorem B1737719 : Blo 1736569 1737719 := bstep (se 1 (by rfl) ⟨1303289, by rfl⟩ : syracuseStep 1737719 = 2606579) B2606579
theorem B3908609 : Blo 1736569 3908609 := bstep (se 2 (by rfl) ⟨1465728, by rfl⟩ : syracuseStep 3908609 = 2931457) B2931457
theorem B1737739 : Blo 1736569 1737739 := bstep (se 1 (by rfl) ⟨1303304, by rfl⟩ : syracuseStep 1737739 = 2606609) B2606609
theorem B1737751 : Blo 1736569 1737751 := bstep (se 1 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 1737751 = 2606627) B2606627
theorem B2606105 : Blo 1736569 2606105 := bstep (se 2 (by rfl) ⟨977289, by rfl⟩ : syracuseStep 2606105 = 1954579) B1954579
theorem B1737771 : Blo 1736569 1737771 := bstep (se 1 (by rfl) ⟨1303328, by rfl⟩ : syracuseStep 1737771 = 2606657) B2606657
theorem B1737783 : Blo 1736569 1737783 := bstep (se 1 (by rfl) ⟨1303337, by rfl⟩ : syracuseStep 1737783 = 2606675) B2606675
theorem B44549189 : Blo 1736569 44549189 := bstep (se 4 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 44549189 = 8352973) B8352973
theorem B21136459 : Blo 1736569 21136459 := bstep (se 1 (by rfl) ⟨15852344, by rfl⟩ : syracuseStep 21136459 = 31704689) B31704689
theorem B1737803 : Blo 1736569 1737803 := bstep (se 1 (by rfl) ⟨1303352, by rfl⟩ : syracuseStep 1737803 = 2606705) B2606705
theorem B4400203 : Blo 1736569 4400203 := bstep (se 1 (by rfl) ⟨3300152, by rfl⟩ : syracuseStep 4400203 = 6600305) B6600305
theorem B1737815 : Blo 1736569 1737815 := bstep (se 1 (by rfl) ⟨1303361, by rfl⟩ : syracuseStep 1737815 = 2606723) B2606723
theorem B1737835 : Blo 1736569 1737835 := bstep (se 1 (by rfl) ⟨1303376, by rfl⟩ : syracuseStep 1737835 = 2606753) B2606753
theorem B1737847 : Blo 1736569 1737847 := bstep (se 1 (by rfl) ⟨1303385, by rfl⟩ : syracuseStep 1737847 = 2606771) B2606771
theorem B2606219 : Blo 1736569 2606219 := bstep (se 1 (by rfl) ⟨1954664, by rfl⟩ : syracuseStep 2606219 = 3909329) B3909329
theorem B1737867 : Blo 1736569 1737867 := bstep (se 1 (by rfl) ⟨1303400, by rfl⟩ : syracuseStep 1737867 = 2606801) B2606801
theorem B2606231 : Blo 1736569 2606231 := bstep (se 1 (by rfl) ⟨1954673, by rfl⟩ : syracuseStep 2606231 = 3909347) B3909347
theorem B1737879 : Blo 1736569 1737879 := bstep (se 1 (by rfl) ⟨1303409, by rfl⟩ : syracuseStep 1737879 = 2606819) B2606819
theorem B1737899 : Blo 1736569 1737899 := bstep (se 1 (by rfl) ⟨1303424, by rfl⟩ : syracuseStep 1737899 = 2606849) B2606849
theorem B4457651 : Blo 1736569 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B1737911 : Blo 1736569 1737911 := bstep (se 1 (by rfl) ⟨1303433, by rfl⟩ : syracuseStep 1737911 = 2606867) B2606867
theorem B4949171 : Blo 1736569 4949171 := bstep (se 1 (by rfl) ⟨3711878, by rfl⟩ : syracuseStep 4949171 = 7423757) B7423757
theorem B1737931 : Blo 1736569 1737931 := bstep (se 1 (by rfl) ⟨1303448, by rfl⟩ : syracuseStep 1737931 = 2606897) B2606897
theorem B1737943 : Blo 1736569 1737943 := bstep (se 1 (by rfl) ⟨1303457, by rfl⟩ : syracuseStep 1737943 = 2606915) B2606915
theorem B3908825 : Blo 1736569 3908825 := bstep (se 2 (by rfl) ⟨1465809, by rfl⟩ : syracuseStep 3908825 = 2931619) B2931619
theorem B2606297 : Blo 1736569 2606297 := bstep (se 2 (by rfl) ⟨977361, by rfl⟩ : syracuseStep 2606297 = 1954723) B1954723
theorem B4400345 : Blo 1736569 4400345 := bstep (se 2 (by rfl) ⟨1650129, by rfl⟩ : syracuseStep 4400345 = 3300259) B3300259
theorem B1737963 : Blo 1736569 1737963 := bstep (se 1 (by rfl) ⟨1303472, by rfl⟩ : syracuseStep 1737963 = 2606945) B2606945
theorem B1737975 : Blo 1736569 1737975 := bstep (se 1 (by rfl) ⟨1303481, by rfl⟩ : syracuseStep 1737975 = 2606963) B2606963
theorem B7922947 : Blo 1736569 7922947 := bstep (se 1 (by rfl) ⟨5942210, by rfl⟩ : syracuseStep 7922947 = 11884421) B11884421
theorem B1737995 : Blo 1736569 1737995 := bstep (se 1 (by rfl) ⟨1303496, by rfl⟩ : syracuseStep 1737995 = 2606993) B2606993
theorem B1738007 : Blo 1736569 1738007 := bstep (se 1 (by rfl) ⟨1303505, by rfl⟩ : syracuseStep 1738007 = 2607011) B2607011
theorem B5866775 : Blo 1736569 5866775 := bstep (se 1 (by rfl) ⟨4400081, by rfl⟩ : syracuseStep 5866775 = 8800163) B8800163
theorem B1738027 : Blo 1736569 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B9389357 : Blo 1736569 9389357 := bstep (se 3 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 9389357 = 3521009) B3521009
theorem B3908915 : Blo 1736569 3908915 := bstep (se 1 (by rfl) ⟨2931686, by rfl⟩ : syracuseStep 3908915 = 5863373) B5863373
theorem B1738039 : Blo 1736569 1738039 := bstep (se 1 (by rfl) ⟨1303529, by rfl⟩ : syracuseStep 1738039 = 2607059) B2607059
theorem B4695371 : Blo 1736569 4695371 := bstep (se 1 (by rfl) ⟨3521528, by rfl⟩ : syracuseStep 4695371 = 7043057) B7043057
theorem B2606411 : Blo 1736569 2606411 := bstep (se 1 (by rfl) ⟨1954808, by rfl⟩ : syracuseStep 2606411 = 3909617) B3909617
theorem B1738059 : Blo 1736569 1738059 := bstep (se 1 (by rfl) ⟨1303544, by rfl⟩ : syracuseStep 1738059 = 2607089) B2607089
theorem B3712331 : Blo 1736569 3712331 := bstep (se 1 (by rfl) ⟨2784248, by rfl⟩ : syracuseStep 3712331 = 5568497) B5568497
theorem B3908951 : Blo 1736569 3908951 := bstep (se 1 (by rfl) ⟨2931713, by rfl⟩ : syracuseStep 3908951 = 5863427) B5863427
theorem B2606423 : Blo 1736569 2606423 := bstep (se 1 (by rfl) ⟨1954817, by rfl⟩ : syracuseStep 2606423 = 3909635) B3909635
theorem B1738071 : Blo 1736569 1738071 := bstep (se 1 (by rfl) ⟨1303553, by rfl⟩ : syracuseStep 1738071 = 2607107) B2607107
theorem B1738091 : Blo 1736569 1738091 := bstep (se 1 (by rfl) ⟨1303568, by rfl⟩ : syracuseStep 1738091 = 2607137) B2607137
theorem B1738103 : Blo 1736569 1738103 := bstep (se 1 (by rfl) ⟨1303577, by rfl⟩ : syracuseStep 1738103 = 2607155) B2607155
theorem B1738123 : Blo 1736569 1738123 := bstep (se 1 (by rfl) ⟨1303592, by rfl⟩ : syracuseStep 1738123 = 2607185) B2607185
theorem B1738135 : Blo 1736569 1738135 := bstep (se 1 (by rfl) ⟨1303601, by rfl⟩ : syracuseStep 1738135 = 2607203) B2607203
theorem B2606489 : Blo 1736569 2606489 := bstep (se 2 (by rfl) ⟨977433, by rfl⟩ : syracuseStep 2606489 = 1954867) B1954867
theorem B1738155 : Blo 1736569 1738155 := bstep (se 1 (by rfl) ⟨1303616, by rfl⟩ : syracuseStep 1738155 = 2607233) B2607233
theorem B1738167 : Blo 1736569 1738167 := bstep (se 1 (by rfl) ⟨1303625, by rfl⟩ : syracuseStep 1738167 = 2607251) B2607251
theorem B1738187 : Blo 1736569 1738187 := bstep (se 1 (by rfl) ⟨1303640, by rfl⟩ : syracuseStep 1738187 = 2607281) B2607281
theorem B1738199 : Blo 1736569 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B18073049 : Blo 1736569 18073049 := bstep (se 2 (by rfl) ⟨6777393, by rfl⟩ : syracuseStep 18073049 = 13554787) B13554787
theorem B1738219 : Blo 1736569 1738219 := bstep (se 1 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 1738219 = 2607329) B2607329
theorem B1738231 : Blo 1736569 1738231 := bstep (se 1 (by rfl) ⟨1303673, by rfl⟩ : syracuseStep 1738231 = 2607347) B2607347
theorem B6596099 : Blo 1736569 6596099 := bstep (se 1 (by rfl) ⟨4947074, by rfl⟩ : syracuseStep 6596099 = 9894149) B9894149
theorem B3909131 : Blo 1736569 3909131 := bstep (se 1 (by rfl) ⟨2931848, by rfl⟩ : syracuseStep 3909131 = 5863697) B5863697
theorem B2606603 : Blo 1736569 2606603 := bstep (se 1 (by rfl) ⟨1954952, by rfl⟩ : syracuseStep 2606603 = 3909905) B3909905
theorem B1738251 : Blo 1736569 1738251 := bstep (se 1 (by rfl) ⟨1303688, by rfl⟩ : syracuseStep 1738251 = 2607377) B2607377
theorem B6596113 : Blo 1736569 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B2606615 : Blo 1736569 2606615 := bstep (se 1 (by rfl) ⟨1954961, by rfl⟩ : syracuseStep 2606615 = 3909923) B3909923
theorem B1738263 : Blo 1736569 1738263 := bstep (se 1 (by rfl) ⟨1303697, by rfl⟩ : syracuseStep 1738263 = 2607395) B2607395
theorem B1738283 : Blo 1736569 1738283 := bstep (se 1 (by rfl) ⟨1303712, by rfl⟩ : syracuseStep 1738283 = 2607425) B2607425
theorem B1738295 : Blo 1736569 1738295 := bstep (se 1 (by rfl) ⟨1303721, by rfl⟩ : syracuseStep 1738295 = 2607443) B2607443
theorem B3909185 : Blo 1736569 3909185 := bstep (se 2 (by rfl) ⟨1465944, by rfl⟩ : syracuseStep 3909185 = 2931889) B2931889
theorem B1738315 : Blo 1736569 1738315 := bstep (se 1 (by rfl) ⟨1303736, by rfl⟩ : syracuseStep 1738315 = 2607473) B2607473
theorem B1738327 : Blo 1736569 1738327 := bstep (se 1 (by rfl) ⟨1303745, by rfl⟩ : syracuseStep 1738327 = 2607491) B2607491
theorem B2606681 : Blo 1736569 2606681 := bstep (se 2 (by rfl) ⟨977505, by rfl⟩ : syracuseStep 2606681 = 1955011) B1955011
theorem B1738347 : Blo 1736569 1738347 := bstep (se 1 (by rfl) ⟨1303760, by rfl⟩ : syracuseStep 1738347 = 2607521) B2607521
theorem B1738359 : Blo 1736569 1738359 := bstep (se 1 (by rfl) ⟨1303769, by rfl⟩ : syracuseStep 1738359 = 2607539) B2607539
theorem B1738379 : Blo 1736569 1738379 := bstep (se 1 (by rfl) ⟨1303784, by rfl⟩ : syracuseStep 1738379 = 2607569) B2607569
theorem B1738391 : Blo 1736569 1738391 := bstep (se 1 (by rfl) ⟨1303793, by rfl⟩ : syracuseStep 1738391 = 2607587) B2607587
theorem B1738411 : Blo 1736569 1738411 := bstep (se 1 (by rfl) ⟨1303808, by rfl⟩ : syracuseStep 1738411 = 2607617) B2607617
theorem B1738423 : Blo 1736569 1738423 := bstep (se 1 (by rfl) ⟨1303817, by rfl⟩ : syracuseStep 1738423 = 2607635) B2607635
theorem B2606795 : Blo 1736569 2606795 := bstep (se 1 (by rfl) ⟨1955096, by rfl⟩ : syracuseStep 2606795 = 3910193) B3910193
theorem B1738443 : Blo 1736569 1738443 := bstep (se 1 (by rfl) ⟨1303832, by rfl⟩ : syracuseStep 1738443 = 2607665) B2607665
theorem B2606807 : Blo 1736569 2606807 := bstep (se 1 (by rfl) ⟨1955105, by rfl⟩ : syracuseStep 2606807 = 3910211) B3910211
theorem B1738455 : Blo 1736569 1738455 := bstep (se 1 (by rfl) ⟨1303841, by rfl⟩ : syracuseStep 1738455 = 2607683) B2607683
theorem B1738475 : Blo 1736569 1738475 := bstep (se 1 (by rfl) ⟨1303856, by rfl⟩ : syracuseStep 1738475 = 2607713) B2607713
theorem B1738487 : Blo 1736569 1738487 := bstep (se 1 (by rfl) ⟨1303865, by rfl⟩ : syracuseStep 1738487 = 2607731) B2607731
theorem B1738507 : Blo 1736569 1738507 := bstep (se 1 (by rfl) ⟨1303880, by rfl⟩ : syracuseStep 1738507 = 2607761) B2607761
theorem B1738519 : Blo 1736569 1738519 := bstep (se 1 (by rfl) ⟨1303889, by rfl⟩ : syracuseStep 1738519 = 2607779) B2607779
theorem B3909401 : Blo 1736569 3909401 := bstep (se 2 (by rfl) ⟨1466025, by rfl⟩ : syracuseStep 3909401 = 2932051) B2932051
theorem B2606873 : Blo 1736569 2606873 := bstep (se 2 (by rfl) ⟨977577, by rfl⟩ : syracuseStep 2606873 = 1955155) B1955155
theorem B1738539 : Blo 1736569 1738539 := bstep (se 1 (by rfl) ⟨1303904, by rfl⟩ : syracuseStep 1738539 = 2607809) B2607809
theorem B5867315 : Blo 1736569 5867315 := bstep (se 1 (by rfl) ⟨4400486, by rfl⟩ : syracuseStep 5867315 = 8800973) B8800973
theorem B1738551 : Blo 1736569 1738551 := bstep (se 1 (by rfl) ⟨1303913, by rfl⟩ : syracuseStep 1738551 = 2607827) B2607827
theorem B6596417 : Blo 1736569 6596417 := bstep (se 2 (by rfl) ⟨2473656, by rfl⟩ : syracuseStep 6596417 = 4947313) B4947313
theorem B8791901 : Blo 1736569 8791901 := bstep (se 3 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 8791901 = 3296963) B3296963
theorem B3909491 : Blo 1736569 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B2606987 : Blo 1736569 2606987 := bstep (se 1 (by rfl) ⟨1955240, by rfl⟩ : syracuseStep 2606987 = 3910481) B3910481
theorem B3909527 : Blo 1736569 3909527 := bstep (se 1 (by rfl) ⟨2932145, by rfl⟩ : syracuseStep 3909527 = 5864291) B5864291
theorem B2606999 : Blo 1736569 2606999 := bstep (se 1 (by rfl) ⟨1955249, by rfl⟩ : syracuseStep 2606999 = 3910499) B3910499
theorem B2607065 : Blo 1736569 2607065 := bstep (se 2 (by rfl) ⟨977649, by rfl⟩ : syracuseStep 2607065 = 1955299) B1955299
theorem B6686723 : Blo 1736569 6686723 := bstep (se 1 (by rfl) ⟨5015042, by rfl⟩ : syracuseStep 6686723 = 10030085) B10030085
theorem B7424045 : Blo 1736569 7424045 := bstep (se 3 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 7424045 = 2784017) B2784017
theorem B5867585 : Blo 1736569 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B3909707 : Blo 1736569 3909707 := bstep (se 1 (by rfl) ⟨2932280, by rfl⟩ : syracuseStep 3909707 = 5864561) B5864561
theorem B2607179 : Blo 1736569 2607179 := bstep (se 1 (by rfl) ⟨1955384, by rfl⟩ : syracuseStep 2607179 = 3910769) B3910769
theorem B2607191 : Blo 1736569 2607191 := bstep (se 1 (by rfl) ⟨1955393, by rfl⟩ : syracuseStep 2607191 = 3910787) B3910787
theorem B3909761 : Blo 1736569 3909761 := bstep (se 2 (by rfl) ⟨1466160, by rfl⟩ : syracuseStep 3909761 = 2932321) B2932321
theorem B2607257 : Blo 1736569 2607257 := bstep (se 2 (by rfl) ⟨977721, by rfl⟩ : syracuseStep 2607257 = 1955443) B1955443
theorem B8915123 : Blo 1736569 8915123 := bstep (se 1 (by rfl) ⟨6686342, by rfl⟩ : syracuseStep 8915123 = 13372685) B13372685
theorem B2607371 : Blo 1736569 2607371 := bstep (se 1 (by rfl) ⟨1955528, by rfl⟩ : syracuseStep 2607371 = 3911057) B3911057
theorem B2607383 : Blo 1736569 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B3909977 : Blo 1736569 3909977 := bstep (se 2 (by rfl) ⟨1466241, by rfl⟩ : syracuseStep 3909977 = 2932483) B2932483
theorem B2607449 : Blo 1736569 2607449 := bstep (se 2 (by rfl) ⟨977793, by rfl⟩ : syracuseStep 2607449 = 1955587) B1955587
theorem B3910067 : Blo 1736569 3910067 := bstep (se 1 (by rfl) ⟨2932550, by rfl⟩ : syracuseStep 3910067 = 5865101) B5865101
theorem B2607563 : Blo 1736569 2607563 := bstep (se 1 (by rfl) ⟨1955672, by rfl⟩ : syracuseStep 2607563 = 3911345) B3911345
theorem B3910103 : Blo 1736569 3910103 := bstep (se 1 (by rfl) ⟨2932577, by rfl⟩ : syracuseStep 3910103 = 5865155) B5865155
theorem B2607575 : Blo 1736569 2607575 := bstep (se 1 (by rfl) ⟨1955681, by rfl⟩ : syracuseStep 2607575 = 3911363) B3911363
theorem B13560281 : Blo 1736569 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B6597085 : Blo 1736569 6597085 := bstep (se 3 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 6597085 = 2473907) B2473907
theorem B2607641 : Blo 1736569 2607641 := bstep (se 2 (by rfl) ⟨977865, by rfl⟩ : syracuseStep 2607641 = 1955731) B1955731
theorem B3910283 : Blo 1736569 3910283 := bstep (se 1 (by rfl) ⟨2932712, by rfl⟩ : syracuseStep 3910283 = 5865425) B5865425
theorem B2607755 : Blo 1736569 2607755 := bstep (se 1 (by rfl) ⟨1955816, by rfl⟩ : syracuseStep 2607755 = 3911633) B3911633
theorem B2607767 : Blo 1736569 2607767 := bstep (se 1 (by rfl) ⟨1955825, by rfl⟩ : syracuseStep 2607767 = 3911651) B3911651
theorem B3910337 : Blo 1736569 3910337 := bstep (se 2 (by rfl) ⟨1466376, by rfl⟩ : syracuseStep 3910337 = 2932753) B2932753
theorem B7424729 : Blo 1736569 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B2607833 : Blo 1736569 2607833 := bstep (se 2 (by rfl) ⟨977937, by rfl⟩ : syracuseStep 2607833 = 1955875) B1955875
theorem B14838659 : Blo 1736569 14838659 := bstep (se 1 (by rfl) ⟨11128994, by rfl⟩ : syracuseStep 14838659 = 22257989) B22257989
theorem B3910553 : Blo 1736569 3910553 := bstep (se 2 (by rfl) ⟨1466457, by rfl⟩ : syracuseStep 3910553 = 2932915) B2932915
theorem B3910643 : Blo 1736569 3910643 := bstep (se 1 (by rfl) ⟨2932982, by rfl⟩ : syracuseStep 3910643 = 5865965) B5865965
theorem B22866961 : Blo 1736569 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B8801297 : Blo 1736569 8801297 := bstep (se 2 (by rfl) ⟨3300486, by rfl⟩ : syracuseStep 8801297 = 6600973) B6600973
theorem B3910679 : Blo 1736569 3910679 := bstep (se 1 (by rfl) ⟨2933009, by rfl⟩ : syracuseStep 3910679 = 5866019) B5866019
theorem B2198603 : Blo 1736569 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B20057219 : Blo 1736569 20057219 := bstep (se 1 (by rfl) ⟨15042914, by rfl⟩ : syracuseStep 20057219 = 30085829) B30085829
theorem B6261905 : Blo 1736569 6261905 := bstep (se 2 (by rfl) ⟨2348214, by rfl⟩ : syracuseStep 6261905 = 4696429) B4696429
theorem B4172951 : Blo 1736569 4172951 := bstep (se 1 (by rfl) ⟨3129713, by rfl⟩ : syracuseStep 4172951 = 6259427) B6259427
theorem B8801459 : Blo 1736569 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B3910859 : Blo 1736569 3910859 := bstep (se 1 (by rfl) ⟨2933144, by rfl⟩ : syracuseStep 3910859 = 5866289) B5866289
theorem B3910913 : Blo 1736569 3910913 := bstep (se 2 (by rfl) ⟨1466592, by rfl⟩ : syracuseStep 3910913 = 2933185) B2933185
theorem B1854743 : Blo 1736569 1854743 := bstep (se 1 (by rfl) ⟨1391057, by rfl⟩ : syracuseStep 1854743 = 2782115) B2782115
theorem B7048471 : Blo 1736569 7048471 := bstep (se 1 (by rfl) ⟨5286353, by rfl⟩ : syracuseStep 7048471 = 10572707) B10572707
theorem B19795265 : Blo 1736569 19795265 := bstep (se 2 (by rfl) ⟨7423224, by rfl⟩ : syracuseStep 19795265 = 14846449) B14846449
theorem B3911129 : Blo 1736569 3911129 := bstep (se 2 (by rfl) ⟨1466673, by rfl⟩ : syracuseStep 3911129 = 2933347) B2933347
theorem B3911219 : Blo 1736569 3911219 := bstep (se 1 (by rfl) ⟨2933414, by rfl⟩ : syracuseStep 3911219 = 5866829) B5866829
theorem B3911255 : Blo 1736569 3911255 := bstep (se 1 (by rfl) ⟨2933441, by rfl⟩ : syracuseStep 3911255 = 5866883) B5866883
theorem B3296857 : Blo 1736569 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B6598361 : Blo 1736569 6598361 := bstep (se 2 (by rfl) ⟨2474385, by rfl⟩ : syracuseStep 6598361 = 4948771) B4948771
theorem B2199307 : Blo 1736569 2199307 := bstep (se 1 (by rfl) ⟨1649480, by rfl⟩ : syracuseStep 2199307 = 3298961) B3298961
theorem B3911435 : Blo 1736569 3911435 := bstep (se 1 (by rfl) ⟨2933576, by rfl⟩ : syracuseStep 3911435 = 5867153) B5867153
theorem B13201217 : Blo 1736569 13201217 := bstep (se 2 (by rfl) ⟨4950456, by rfl⟩ : syracuseStep 13201217 = 9900913) B9900913
theorem B3911489 : Blo 1736569 3911489 := bstep (se 2 (by rfl) ⟨1466808, by rfl⟩ : syracuseStep 3911489 = 2933617) B2933617
theorem B7425857 : Blo 1736569 7425857 := bstep (se 2 (by rfl) ⟨2784696, by rfl⟩ : syracuseStep 7425857 = 5569393) B5569393
theorem B5861213 : Blo 1736569 5861213 := bstep (se 3 (by rfl) ⟨1098977, by rfl⟩ : syracuseStep 5861213 = 2197955) B2197955
theorem B1953643 : Blo 1736569 1953643 := bstep (se 1 (by rfl) ⟨1465232, by rfl⟩ : syracuseStep 1953643 = 2930465) B2930465
theorem B8794007 : Blo 1736569 8794007 := bstep (se 1 (by rfl) ⟨6595505, by rfl⟩ : syracuseStep 8794007 = 13191011) B13191011
theorem B1953751 : Blo 1736569 1953751 := bstep (se 1 (by rfl) ⟨1465313, by rfl⟩ : syracuseStep 1953751 = 2930627) B2930627
theorem B2199575 : Blo 1736569 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B3911705 : Blo 1736569 3911705 := bstep (se 2 (by rfl) ⟨1466889, by rfl⟩ : syracuseStep 3911705 = 2933779) B2933779
theorem B23777315 : Blo 1736569 23777315 := bstep (se 1 (by rfl) ⟨17832986, by rfl⟩ : syracuseStep 23777315 = 35665973) B35665973
theorem B6262829 : Blo 1736569 6262829 := bstep (se 3 (by rfl) ⟨1174280, by rfl⟩ : syracuseStep 6262829 = 2348561) B2348561
theorem B3960971 : Blo 1736569 3960971 := bstep (se 1 (by rfl) ⟨2970728, by rfl⟩ : syracuseStep 3960971 = 5941457) B5941457
theorem B1953931 : Blo 1736569 1953931 := bstep (se 1 (by rfl) ⟨1465448, by rfl⟩ : syracuseStep 1953931 = 2930897) B2930897
theorem B3297419 : Blo 1736569 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B1954039 : Blo 1736569 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B3297601 : Blo 1736569 3297601 := bstep (se 2 (by rfl) ⟨1236600, by rfl⟩ : syracuseStep 3297601 = 2473201) B2473201
theorem B25039205 : Blo 1736569 25039205 := bstep (se 4 (by rfl) ⟨2347425, by rfl⟩ : syracuseStep 25039205 = 4694851) B4694851
theorem B1954219 : Blo 1736569 1954219 := bstep (se 1 (by rfl) ⟨1465664, by rfl⟩ : syracuseStep 1954219 = 2931329) B2931329
theorem B14848433 : Blo 1736569 14848433 := bstep (se 2 (by rfl) ⟨5568162, by rfl⟩ : syracuseStep 14848433 = 11136325) B11136325
theorem B6263219 : Blo 1736569 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B6263261 : Blo 1736569 6263261 := bstep (se 3 (by rfl) ⟨1174361, by rfl⟩ : syracuseStep 6263261 = 2348723) B2348723
theorem B1954327 : Blo 1736569 1954327 := bstep (se 1 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 1954327 = 2931491) B2931491
theorem B4174411 : Blo 1736569 4174411 := bstep (se 1 (by rfl) ⟨3130808, by rfl⟩ : syracuseStep 4174411 = 6261617) B6261617
theorem B3388043 : Blo 1736569 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B1954507 : Blo 1736569 1954507 := bstep (se 1 (by rfl) ⟨1465880, by rfl⟩ : syracuseStep 1954507 = 2931761) B2931761
theorem B2200279 : Blo 1736569 2200279 := bstep (se 1 (by rfl) ⟨1650209, by rfl⟩ : syracuseStep 2200279 = 3300419) B3300419
theorem B11129561 : Blo 1736569 11129561 := bstep (se 2 (by rfl) ⟨4173585, by rfl⟩ : syracuseStep 11129561 = 8347171) B8347171
theorem B1954615 : Blo 1736569 1954615 := bstep (se 1 (by rfl) ⟨1465961, by rfl⟩ : syracuseStep 1954615 = 2931923) B2931923
theorem B15848257 : Blo 1736569 15848257 := bstep (se 2 (by rfl) ⟨5943096, by rfl⟩ : syracuseStep 15848257 = 11886193) B11886193
theorem B28177217 : Blo 1736569 28177217 := bstep (se 2 (by rfl) ⟨10566456, by rfl⟩ : syracuseStep 28177217 = 21132913) B21132913
theorem B7418699 : Blo 1736569 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B21418931 : Blo 1736569 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B5862347 : Blo 1736569 5862347 := bstep (se 1 (by rfl) ⟨4396760, by rfl⟩ : syracuseStep 5862347 = 8793521) B8793521
theorem B1954795 : Blo 1736569 1954795 := bstep (se 1 (by rfl) ⟨1466096, by rfl⟩ : syracuseStep 1954795 = 2932193) B2932193
theorem B3298315 : Blo 1736569 3298315 := bstep (se 1 (by rfl) ⟨2473736, by rfl⟩ : syracuseStep 3298315 = 4947473) B4947473
theorem B6689837 : Blo 1736569 6689837 := bstep (se 3 (by rfl) ⟨1254344, by rfl⟩ : syracuseStep 6689837 = 2508689) B2508689
theorem B1856567 : Blo 1736569 1856567 := bstep (se 1 (by rfl) ⟨1392425, by rfl⟩ : syracuseStep 1856567 = 2784851) B2784851
theorem B3298391 : Blo 1736569 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B1954903 : Blo 1736569 1954903 := bstep (se 1 (by rfl) ⟨1466177, by rfl⟩ : syracuseStep 1954903 = 2932355) B2932355
theorem B9901187 : Blo 1736569 9901187 := bstep (se 1 (by rfl) ⟨7425890, by rfl⟩ : syracuseStep 9901187 = 14851781) B14851781
theorem B4175027 : Blo 1736569 4175027 := bstep (se 1 (by rfl) ⟨3131270, by rfl⟩ : syracuseStep 4175027 = 6262541) B6262541
theorem B5862617 : Blo 1736569 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B1955083 : Blo 1736569 1955083 := bstep (se 1 (by rfl) ⟨1466312, by rfl⟩ : syracuseStep 1955083 = 2932625) B2932625
theorem B6599987 : Blo 1736569 6599987 := bstep (se 1 (by rfl) ⟨4949990, by rfl⟩ : syracuseStep 6599987 = 9899981) B9899981
theorem B6600001 : Blo 1736569 6600001 := bstep (se 2 (by rfl) ⟨2475000, by rfl⟩ : syracuseStep 6600001 = 4950001) B4950001
theorem B6690113 : Blo 1736569 6690113 := bstep (se 2 (by rfl) ⟨2508792, by rfl⟩ : syracuseStep 6690113 = 5017585) B5017585
theorem B1955191 : Blo 1736569 1955191 := bstep (se 1 (by rfl) ⟨1466393, by rfl⟩ : syracuseStep 1955191 = 2932787) B2932787
theorem B2086283 : Blo 1736569 2086283 := bstep (se 1 (by rfl) ⟨1564712, by rfl⟩ : syracuseStep 2086283 = 3129425) B3129425
theorem B1955371 : Blo 1736569 1955371 := bstep (se 1 (by rfl) ⟨1466528, by rfl⟩ : syracuseStep 1955371 = 2933057) B2933057
theorem B9893441 : Blo 1736569 9893441 := bstep (se 2 (by rfl) ⟨3710040, by rfl⟩ : syracuseStep 9893441 = 7420081) B7420081
theorem B4396619 : Blo 1736569 4396619 := bstep (se 1 (by rfl) ⟨3297464, by rfl⟩ : syracuseStep 4396619 = 6594929) B6594929
theorem B1955479 : Blo 1736569 1955479 := bstep (se 1 (by rfl) ⟨1466609, by rfl⟩ : syracuseStep 1955479 = 2933219) B2933219
theorem B6026945 : Blo 1736569 6026945 := bstep (se 2 (by rfl) ⟨2260104, by rfl⟩ : syracuseStep 6026945 = 4520209) B4520209
theorem B3299059 : Blo 1736569 3299059 := bstep (se 1 (by rfl) ⟨2474294, by rfl⟩ : syracuseStep 3299059 = 4948589) B4948589
theorem B7419671 : Blo 1736569 7419671 := bstep (se 1 (by rfl) ⟨5564753, by rfl⟩ : syracuseStep 7419671 = 11129507) B11129507
theorem B19052333 : Blo 1736569 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B11892545 : Blo 1736569 11892545 := bstep (se 2 (by rfl) ⟨4459704, by rfl⟩ : syracuseStep 11892545 = 8919409) B8919409
theorem B1955659 : Blo 1736569 1955659 := bstep (se 1 (by rfl) ⟨1466744, by rfl⟩ : syracuseStep 1955659 = 2933489) B2933489
theorem B2930519 : Blo 1736569 2930519 := bstep (se 1 (by rfl) ⟨2197889, by rfl⟩ : syracuseStep 2930519 = 4395779) B4395779
theorem B5863319 : Blo 1736569 5863319 := bstep (se 1 (by rfl) ⟨4397489, by rfl⟩ : syracuseStep 5863319 = 8794979) B8794979
theorem B35682227 : Blo 1736569 35682227 := bstep (se 1 (by rfl) ⟨26761670, by rfl⟩ : syracuseStep 35682227 = 53523341) B53523341
theorem B1955767 : Blo 1736569 1955767 := bstep (se 1 (by rfl) ⟨1466825, by rfl⟩ : syracuseStep 1955767 = 2933651) B2933651
theorem B2930647 : Blo 1736569 2930647 := bstep (se 1 (by rfl) ⟨2197985, by rfl⟩ : syracuseStep 2930647 = 4395971) B4395971
theorem B3299287 : Blo 1736569 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B5085149 : Blo 1736569 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B2783243 : Blo 1736569 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B3299393 : Blo 1736569 3299393 := bstep (se 2 (by rfl) ⟨1237272, by rfl⟩ : syracuseStep 3299393 = 2474545) B2474545
theorem B11884637 : Blo 1736569 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B9394327 : Blo 1736569 9394327 := bstep (se 1 (by rfl) ⟨7045745, by rfl⟩ : syracuseStep 9394327 = 14091491) B14091491
theorem B6691019 : Blo 1736569 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B1980631 : Blo 1736569 1980631 := bstep (se 1 (by rfl) ⟨1485473, by rfl⟩ : syracuseStep 1980631 = 2970947) B2970947
theorem B3709145 : Blo 1736569 3709145 := bstep (se 2 (by rfl) ⟨1390929, by rfl⟩ : syracuseStep 3709145 = 2781859) B2781859
theorem B3299545 : Blo 1736569 3299545 := bstep (se 2 (by rfl) ⟨1237329, by rfl⟩ : syracuseStep 3299545 = 2474659) B2474659
theorem B7526621 : Blo 1736569 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B3963161 : Blo 1736569 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B3520855 : Blo 1736569 3520855 := bstep (se 1 (by rfl) ⟨2640641, by rfl⟩ : syracuseStep 3520855 = 5281283) B5281283
theorem B47569301 : Blo 1736569 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B5863859 : Blo 1736569 5863859 := bstep (se 1 (by rfl) ⟨4397894, by rfl⟩ : syracuseStep 5863859 = 8795789) B8795789
theorem B2783755 : Blo 1736569 2783755 := bstep (se 1 (by rfl) ⟨2087816, by rfl⟩ : syracuseStep 2783755 = 4175633) B4175633
theorem B4397591 : Blo 1736569 4397591 := bstep (se 1 (by rfl) ⟨3298193, by rfl⟩ : syracuseStep 4397591 = 6596387) B6596387
theorem B4176449 : Blo 1736569 4176449 := bstep (se 2 (by rfl) ⟨1566168, by rfl⟩ : syracuseStep 4176449 = 3132337) B3132337
theorem B2931275 : Blo 1736569 2931275 := bstep (se 1 (by rfl) ⟨2198456, by rfl⟩ : syracuseStep 2931275 = 4396913) B4396913
theorem B12057239 : Blo 1736569 12057239 := bstep (se 1 (by rfl) ⟨9042929, by rfl⟩ : syracuseStep 12057239 = 18085859) B18085859
theorem B5864129 : Blo 1736569 5864129 := bstep (se 2 (by rfl) ⟨2199048, by rfl⟩ : syracuseStep 5864129 = 4398097) B4398097
theorem B2931403 : Blo 1736569 2931403 := bstep (se 1 (by rfl) ⟨2198552, by rfl⟩ : syracuseStep 2931403 = 4397105) B4397105
theorem B11279179 : Blo 1736569 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B2931545 : Blo 1736569 2931545 := bstep (se 2 (by rfl) ⟨1099329, by rfl⟩ : syracuseStep 2931545 = 2198659) B2198659
theorem B3963763 : Blo 1736569 3963763 := bstep (se 1 (by rfl) ⟨2972822, by rfl⟩ : syracuseStep 3963763 = 5945645) B5945645
theorem B22264753 : Blo 1736569 22264753 := bstep (se 2 (by rfl) ⟨8349282, by rfl⟩ : syracuseStep 22264753 = 16698565) B16698565
theorem B2931673 : Blo 1736569 2931673 := bstep (se 2 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 2931673 = 2198755) B2198755
theorem B2088023 : Blo 1736569 2088023 := bstep (se 1 (by rfl) ⟨1566017, by rfl⟩ : syracuseStep 2088023 = 3132035) B3132035
theorem B4398259 : Blo 1736569 4398259 := bstep (se 1 (by rfl) ⟨3298694, by rfl⟩ : syracuseStep 4398259 = 6597389) B6597389
theorem B2784473 : Blo 1736569 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B5864669 : Blo 1736569 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B3710195 : Blo 1736569 3710195 := bstep (se 1 (by rfl) ⟨2782646, by rfl⟩ : syracuseStep 3710195 = 5565293) B5565293
theorem B3521803 : Blo 1736569 3521803 := bstep (se 1 (by rfl) ⟨2641352, by rfl⟩ : syracuseStep 3521803 = 5282705) B5282705
theorem B11132225 : Blo 1736569 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B4398401 : Blo 1736569 4398401 := bstep (se 2 (by rfl) ⟨1649400, by rfl⟩ : syracuseStep 4398401 = 3298801) B3298801
theorem B15850853 : Blo 1736569 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B8797571 : Blo 1736569 8797571 := bstep (se 1 (by rfl) ⟨6598178, by rfl⟩ : syracuseStep 8797571 = 13196357) B13196357
theorem B2473355 : Blo 1736569 2473355 := bstep (se 1 (by rfl) ⟨1855016, by rfl⟩ : syracuseStep 2473355 = 3710033) B3710033
theorem B2932247 : Blo 1736569 2932247 := bstep (se 1 (by rfl) ⟨2199185, by rfl⟩ : syracuseStep 2932247 = 4398371) B4398371
theorem B2932375 : Blo 1736569 2932375 := bstep (se 1 (by rfl) ⟨2199281, by rfl⟩ : syracuseStep 2932375 = 4398563) B4398563
theorem B7520003 : Blo 1736569 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B3710785 : Blo 1736569 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B2604875 : Blo 1736569 2604875 := bstep (se 1 (by rfl) ⟨1953656, by rfl⟩ : syracuseStep 2604875 = 3907313) B3907313
theorem B3907403 : Blo 1736569 3907403 := bstep (se 1 (by rfl) ⟨2930552, by rfl⟩ : syracuseStep 3907403 = 5861105) B5861105
theorem B2604887 : Blo 1736569 2604887 := bstep (se 1 (by rfl) ⟨1953665, by rfl⟩ : syracuseStep 2604887 = 3907331) B3907331
theorem B3907457 : Blo 1736569 3907457 := bstep (se 2 (by rfl) ⟨1465296, by rfl⟩ : syracuseStep 3907457 = 2930593) B2930593
theorem B1736587 : Blo 1736569 1736587 := bstep (se 1 (by rfl) ⟨1302440, by rfl⟩ : syracuseStep 1736587 = 2604881) B2604881
theorem B1736599 : Blo 1736569 1736599 := bstep (se 1 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 1736599 = 2604899) B2604899
theorem B7929751 : Blo 1736569 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B2604953 : Blo 1736569 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B1736619 : Blo 1736569 1736619 := bstep (se 1 (by rfl) ⟨1302464, by rfl⟩ : syracuseStep 1736619 = 2604929) B2604929
theorem B19783601 : Blo 1736569 19783601 := bstep (se 2 (by rfl) ⟨7418850, by rfl⟩ : syracuseStep 19783601 = 14837701) B14837701
theorem B1736631 : Blo 1736569 1736631 := bstep (se 1 (by rfl) ⟨1302473, by rfl⟩ : syracuseStep 1736631 = 2604947) B2604947
theorem B4947905 : Blo 1736569 4947905 := bstep (se 2 (by rfl) ⟨1855464, by rfl⟩ : syracuseStep 4947905 = 3710929) B3710929
theorem B1736651 : Blo 1736569 1736651 := bstep (se 1 (by rfl) ⟨1302488, by rfl⟩ : syracuseStep 1736651 = 2604977) B2604977
theorem B1736663 : Blo 1736569 1736663 := bstep (se 1 (by rfl) ⟨1302497, by rfl⟩ : syracuseStep 1736663 = 2604995) B2604995
theorem B4947929 : Blo 1736569 4947929 := bstep (se 2 (by rfl) ⟨1855473, by rfl⟩ : syracuseStep 4947929 = 3710947) B3710947
theorem B5873629 : Blo 1736569 5873629 := bstep (se 3 (by rfl) ⟨1101305, by rfl⟩ : syracuseStep 5873629 = 2202611) B2202611
theorem B1736683 : Blo 1736569 1736683 := bstep (se 1 (by rfl) ⟨1302512, by rfl⟩ : syracuseStep 1736683 = 2605025) B2605025
theorem B1736695 : Blo 1736569 1736695 := bstep (se 1 (by rfl) ⟨1302521, by rfl⟩ : syracuseStep 1736695 = 2605043) B2605043
theorem B1736711 : Blo 1736569 1736711 := bstep (se 1 (by rfl) ⟨1302533, by rfl⟩ : syracuseStep 1736711 = 2605067) B2605067
theorem B8798219 : Blo 1736569 8798219 := bstep (se 1 (by rfl) ⟨6598664, by rfl⟩ : syracuseStep 8798219 = 13197329) B13197329
theorem B1736719 : Blo 1736569 1736719 := bstep (se 1 (by rfl) ⟨1302539, by rfl⟩ : syracuseStep 1736719 = 2605079) B2605079
theorem B15851543 : Blo 1736569 15851543 := bstep (se 1 (by rfl) ⟨11888657, by rfl⟩ : syracuseStep 15851543 = 23777315) B23777315
theorem B2605115 : Blo 1736569 2605115 := bstep (se 1 (by rfl) ⟨1953836, by rfl⟩ : syracuseStep 2605115 = 3907673) B3907673
theorem B1736763 : Blo 1736569 1736763 := bstep (se 1 (by rfl) ⟨1302572, by rfl⟩ : syracuseStep 1736763 = 2605145) B2605145
theorem B5865533 : Blo 1736569 5865533 := bstep (se 3 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 5865533 = 2199575) B2199575
theorem B2605175 : Blo 1736569 2605175 := bstep (se 1 (by rfl) ⟨1953881, by rfl⟩ : syracuseStep 2605175 = 3907763) B3907763
theorem B1736839 : Blo 1736569 1736839 := bstep (se 1 (by rfl) ⟨1302629, by rfl⟩ : syracuseStep 1736839 = 2605259) B2605259
theorem B2605199 : Blo 1736569 2605199 := bstep (se 1 (by rfl) ⟨1953899, by rfl⟩ : syracuseStep 2605199 = 3907799) B3907799
theorem B1736847 : Blo 1736569 1736847 := bstep (se 1 (by rfl) ⟨1302635, by rfl⟩ : syracuseStep 1736847 = 2605271) B2605271
theorem B3571859 : Blo 1736569 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B8798381 : Blo 1736569 8798381 := bstep (se 3 (by rfl) ⟨1649696, by rfl⟩ : syracuseStep 8798381 = 3299393) B3299393
theorem B2605241 : Blo 1736569 2605241 := bstep (se 2 (by rfl) ⟨976965, by rfl⟩ : syracuseStep 2605241 = 1953931) B1953931
theorem B1736891 : Blo 1736569 1736891 := bstep (se 1 (by rfl) ⟨1302668, by rfl⟩ : syracuseStep 1736891 = 2605337) B2605337
theorem B12525769 : Blo 1736569 12525769 := bstep (se 2 (by rfl) ⟨4697163, by rfl⟩ : syracuseStep 12525769 = 9394327) B9394327
theorem B2605319 : Blo 1736569 2605319 := bstep (se 1 (by rfl) ⟨1953989, by rfl⟩ : syracuseStep 2605319 = 3907979) B3907979
theorem B1736967 : Blo 1736569 1736967 := bstep (se 1 (by rfl) ⟨1302725, by rfl⟩ : syracuseStep 1736967 = 2605451) B2605451
theorem B1736975 : Blo 1736569 1736975 := bstep (se 1 (by rfl) ⟨1302731, by rfl⟩ : syracuseStep 1736975 = 2605463) B2605463
theorem B4399393 : Blo 1736569 4399393 := bstep (se 2 (by rfl) ⟨1649772, by rfl⟩ : syracuseStep 4399393 = 3299545) B3299545
theorem B2605355 : Blo 1736569 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B1737019 : Blo 1736569 1737019 := bstep (se 1 (by rfl) ⟨1302764, by rfl⟩ : syracuseStep 1737019 = 2605529) B2605529
theorem B2605385 : Blo 1736569 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B2933111 : Blo 1736569 2933111 := bstep (se 1 (by rfl) ⟨2199833, by rfl⟩ : syracuseStep 2933111 = 4399667) B4399667
theorem B1737095 : Blo 1736569 1737095 := bstep (se 1 (by rfl) ⟨1302821, by rfl⟩ : syracuseStep 1737095 = 2605643) B2605643
theorem B1737103 : Blo 1736569 1737103 := bstep (se 1 (by rfl) ⟨1302827, by rfl⟩ : syracuseStep 1737103 = 2605655) B2605655
theorem B2605499 : Blo 1736569 2605499 := bstep (se 1 (by rfl) ⟨1954124, by rfl⟩ : syracuseStep 2605499 = 3908249) B3908249
theorem B1737147 : Blo 1736569 1737147 := bstep (se 1 (by rfl) ⟨1302860, by rfl⟩ : syracuseStep 1737147 = 2605721) B2605721
theorem B4694473 : Blo 1736569 4694473 := bstep (se 2 (by rfl) ⟨1760427, by rfl⟩ : syracuseStep 4694473 = 3520855) B3520855
theorem B23773661 : Blo 1736569 23773661 := bstep (se 3 (by rfl) ⟨4457561, by rfl⟩ : syracuseStep 23773661 = 8915123) B8915123
theorem B11887069 : Blo 1736569 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B19792349 : Blo 1736569 19792349 := bstep (se 3 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 19792349 = 7422131) B7422131
theorem B2605559 : Blo 1736569 2605559 := bstep (se 1 (by rfl) ⟨1954169, by rfl⟩ : syracuseStep 2605559 = 3908339) B3908339
theorem B1737223 : Blo 1736569 1737223 := bstep (se 1 (by rfl) ⟨1302917, by rfl⟩ : syracuseStep 1737223 = 2605835) B2605835
theorem B2605583 : Blo 1736569 2605583 := bstep (se 1 (by rfl) ⟨1954187, by rfl⟩ : syracuseStep 2605583 = 3908375) B3908375
theorem B1737231 : Blo 1736569 1737231 := bstep (se 1 (by rfl) ⟨1302923, by rfl⟩ : syracuseStep 1737231 = 2605847) B2605847
theorem B17842717 : Blo 1736569 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B18784811 : Blo 1736569 18784811 := bstep (se 1 (by rfl) ⟨14088608, by rfl⟩ : syracuseStep 18784811 = 28177217) B28177217
theorem B2605625 : Blo 1736569 2605625 := bstep (se 2 (by rfl) ⟨977109, by rfl⟩ : syracuseStep 2605625 = 1954219) B1954219
theorem B1737275 : Blo 1736569 1737275 := bstep (se 1 (by rfl) ⟨1302956, by rfl⟩ : syracuseStep 1737275 = 2605913) B2605913
theorem B20070989 : Blo 1736569 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B1737351 : Blo 1736569 1737351 := bstep (se 1 (by rfl) ⟨1303013, by rfl⟩ : syracuseStep 1737351 = 2606027) B2606027
theorem B3908231 : Blo 1736569 3908231 := bstep (se 1 (by rfl) ⟨2931173, by rfl⟩ : syracuseStep 3908231 = 5862347) B5862347
theorem B2605703 : Blo 1736569 2605703 := bstep (se 1 (by rfl) ⟨1954277, by rfl⟩ : syracuseStep 2605703 = 3908555) B3908555
theorem B1737359 : Blo 1736569 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B2605739 : Blo 1736569 2605739 := bstep (se 1 (by rfl) ⟨1954304, by rfl⟩ : syracuseStep 2605739 = 3908609) B3908609
theorem B3711673 : Blo 1736569 3711673 := bstep (se 2 (by rfl) ⟨1391877, by rfl⟩ : syracuseStep 3711673 = 2783755) B2783755
theorem B1737403 : Blo 1736569 1737403 := bstep (se 1 (by rfl) ⟨1303052, by rfl⟩ : syracuseStep 1737403 = 2606105) B2606105
theorem B2605769 : Blo 1736569 2605769 := bstep (se 2 (by rfl) ⟨977163, by rfl⟩ : syracuseStep 2605769 = 1954327) B1954327
theorem B6259457 : Blo 1736569 6259457 := bstep (se 2 (by rfl) ⟨2347296, by rfl⟩ : syracuseStep 6259457 = 4694593) B4694593
theorem B1737479 : Blo 1736569 1737479 := bstep (se 1 (by rfl) ⟨1303109, by rfl⟩ : syracuseStep 1737479 = 2606219) B2606219
theorem B1737487 : Blo 1736569 1737487 := bstep (se 1 (by rfl) ⟨1303115, by rfl⟩ : syracuseStep 1737487 = 2606231) B2606231
theorem B3908411 : Blo 1736569 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B2605883 : Blo 1736569 2605883 := bstep (se 1 (by rfl) ⟨1954412, by rfl⟩ : syracuseStep 2605883 = 3908825) B3908825
theorem B1737531 : Blo 1736569 1737531 := bstep (se 1 (by rfl) ⟨1303148, by rfl⟩ : syracuseStep 1737531 = 2606297) B2606297
theorem B2933563 : Blo 1736569 2933563 := bstep (se 1 (by rfl) ⟨2200172, by rfl⟩ : syracuseStep 2933563 = 4400345) B4400345
theorem B6259571 : Blo 1736569 6259571 := bstep (se 1 (by rfl) ⟨4694678, by rfl⟩ : syracuseStep 6259571 = 9389357) B9389357
theorem B2605943 : Blo 1736569 2605943 := bstep (se 1 (by rfl) ⟨1954457, by rfl⟩ : syracuseStep 2605943 = 3908915) B3908915
theorem B4399991 : Blo 1736569 4399991 := bstep (se 1 (by rfl) ⟨3299993, by rfl⟩ : syracuseStep 4399991 = 6599987) B6599987
theorem B3130247 : Blo 1736569 3130247 := bstep (se 1 (by rfl) ⟨2347685, by rfl⟩ : syracuseStep 3130247 = 4695371) B4695371
theorem B1737607 : Blo 1736569 1737607 := bstep (se 1 (by rfl) ⟨1303205, by rfl⟩ : syracuseStep 1737607 = 2606411) B2606411
theorem B2474887 : Blo 1736569 2474887 := bstep (se 1 (by rfl) ⟨1856165, by rfl⟩ : syracuseStep 2474887 = 3712331) B3712331
theorem B2605967 : Blo 1736569 2605967 := bstep (se 1 (by rfl) ⟨1954475, by rfl⟩ : syracuseStep 2605967 = 3908951) B3908951
theorem B1737615 : Blo 1736569 1737615 := bstep (se 1 (by rfl) ⟨1303211, by rfl⟩ : syracuseStep 1737615 = 2606423) B2606423
theorem B3908537 : Blo 1736569 3908537 := bstep (se 2 (by rfl) ⟨1465701, by rfl⟩ : syracuseStep 3908537 = 2931403) B2931403
theorem B2606009 : Blo 1736569 2606009 := bstep (se 2 (by rfl) ⟨977253, by rfl⟩ : syracuseStep 2606009 = 1954507) B1954507
theorem B1737659 : Blo 1736569 1737659 := bstep (se 1 (by rfl) ⟨1303244, by rfl⟩ : syracuseStep 1737659 = 2606489) B2606489
theorem B2933705 : Blo 1736569 2933705 := bstep (se 2 (by rfl) ⟨1100139, by rfl⟩ : syracuseStep 2933705 = 2200279) B2200279
theorem B2606087 : Blo 1736569 2606087 := bstep (se 1 (by rfl) ⟨1954565, by rfl⟩ : syracuseStep 2606087 = 3909131) B3909131
theorem B1737735 : Blo 1736569 1737735 := bstep (se 1 (by rfl) ⟨1303301, by rfl⟩ : syracuseStep 1737735 = 2606603) B2606603
theorem B1737743 : Blo 1736569 1737743 := bstep (se 1 (by rfl) ⟨1303307, by rfl⟩ : syracuseStep 1737743 = 2606615) B2606615
theorem B5563421 : Blo 1736569 5563421 := bstep (se 3 (by rfl) ⟨1043141, by rfl⟩ : syracuseStep 5563421 = 2086283) B2086283
theorem B6595613 : Blo 1736569 6595613 := bstep (se 3 (by rfl) ⟨1236677, by rfl⟩ : syracuseStep 6595613 = 2473355) B2473355
theorem B6595627 : Blo 1736569 6595627 := bstep (se 1 (by rfl) ⟨4946720, by rfl⟩ : syracuseStep 6595627 = 9893441) B9893441
theorem B2606123 : Blo 1736569 2606123 := bstep (se 1 (by rfl) ⟨1954592, by rfl⟩ : syracuseStep 2606123 = 3909185) B3909185
theorem B1737787 : Blo 1736569 1737787 := bstep (se 1 (by rfl) ⟨1303340, by rfl⟩ : syracuseStep 1737787 = 2606681) B2606681
theorem B2606153 : Blo 1736569 2606153 := bstep (se 2 (by rfl) ⟨977307, by rfl⟩ : syracuseStep 2606153 = 1954615) B1954615
theorem B1737863 : Blo 1736569 1737863 := bstep (se 1 (by rfl) ⟨1303397, by rfl⟩ : syracuseStep 1737863 = 2606795) B2606795
theorem B1737871 : Blo 1736569 1737871 := bstep (se 1 (by rfl) ⟨1303403, by rfl⟩ : syracuseStep 1737871 = 2606807) B2606807
theorem B5285017 : Blo 1736569 5285017 := bstep (se 2 (by rfl) ⟨1981881, by rfl⟩ : syracuseStep 5285017 = 3963763) B3963763
theorem B2606267 : Blo 1736569 2606267 := bstep (se 1 (by rfl) ⟨1954700, by rfl⟩ : syracuseStep 2606267 = 3909401) B3909401
theorem B1737915 : Blo 1736569 1737915 := bstep (se 1 (by rfl) ⟨1303436, by rfl⟩ : syracuseStep 1737915 = 2606873) B2606873
theorem B2606327 : Blo 1736569 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B1737991 : Blo 1736569 1737991 := bstep (se 1 (by rfl) ⟨1303493, by rfl⟩ : syracuseStep 1737991 = 2606987) B2606987
theorem B3908879 : Blo 1736569 3908879 := bstep (se 1 (by rfl) ⟨2931659, by rfl⟩ : syracuseStep 3908879 = 5863319) B5863319
theorem B2606351 : Blo 1736569 2606351 := bstep (se 1 (by rfl) ⟨1954763, by rfl⟩ : syracuseStep 2606351 = 3909527) B3909527
theorem B1737999 : Blo 1736569 1737999 := bstep (se 1 (by rfl) ⟨1303499, by rfl⟩ : syracuseStep 1737999 = 2606999) B2606999
theorem B3908897 : Blo 1736569 3908897 := bstep (se 2 (by rfl) ⟨1465836, by rfl⟩ : syracuseStep 3908897 = 2931673) B2931673
theorem B2606393 : Blo 1736569 2606393 := bstep (se 2 (by rfl) ⟨977397, by rfl⟩ : syracuseStep 2606393 = 1954795) B1954795
theorem B1738043 : Blo 1736569 1738043 := bstep (se 1 (by rfl) ⟨1303532, by rfl⟩ : syracuseStep 1738043 = 2607065) B2607065
theorem B4949363 : Blo 1736569 4949363 := bstep (se 1 (by rfl) ⟨3712022, by rfl⟩ : syracuseStep 4949363 = 7424045) B7424045
theorem B2606471 : Blo 1736569 2606471 := bstep (se 1 (by rfl) ⟨1954853, by rfl⟩ : syracuseStep 2606471 = 3909707) B3909707
theorem B1738119 : Blo 1736569 1738119 := bstep (se 1 (by rfl) ⟨1303589, by rfl⟩ : syracuseStep 1738119 = 2607179) B2607179
theorem B1738127 : Blo 1736569 1738127 := bstep (se 1 (by rfl) ⟨1303595, by rfl⟩ : syracuseStep 1738127 = 2607191) B2607191
theorem B7923091 : Blo 1736569 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B2606507 : Blo 1736569 2606507 := bstep (se 1 (by rfl) ⟨1954880, by rfl⟩ : syracuseStep 2606507 = 3909761) B3909761
theorem B28181945 : Blo 1736569 28181945 := bstep (se 2 (by rfl) ⟨10568229, by rfl⟩ : syracuseStep 28181945 = 21136459) B21136459
theorem B1738171 : Blo 1736569 1738171 := bstep (se 1 (by rfl) ⟨1303628, by rfl⟩ : syracuseStep 1738171 = 2607257) B2607257
theorem B5866937 : Blo 1736569 5866937 := bstep (se 2 (by rfl) ⟨2200101, by rfl⟩ : syracuseStep 5866937 = 4400203) B4400203
theorem B2606537 : Blo 1736569 2606537 := bstep (se 2 (by rfl) ⟨977451, by rfl⟩ : syracuseStep 2606537 = 1954903) B1954903
theorem B1738247 : Blo 1736569 1738247 := bstep (se 1 (by rfl) ⟨1303685, by rfl⟩ : syracuseStep 1738247 = 2607371) B2607371
theorem B1738255 : Blo 1736569 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B2606651 : Blo 1736569 2606651 := bstep (se 1 (by rfl) ⟨1954988, by rfl⟩ : syracuseStep 2606651 = 3909977) B3909977
theorem B1738299 : Blo 1736569 1738299 := bstep (se 1 (by rfl) ⟨1303724, by rfl⟩ : syracuseStep 1738299 = 2607449) B2607449
theorem B31712867 : Blo 1736569 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B3909239 : Blo 1736569 3909239 := bstep (se 1 (by rfl) ⟨2931929, by rfl⟩ : syracuseStep 3909239 = 5863859) B5863859
theorem B2606711 : Blo 1736569 2606711 := bstep (se 1 (by rfl) ⟨1955033, by rfl⟩ : syracuseStep 2606711 = 3910067) B3910067
theorem B1738375 : Blo 1736569 1738375 := bstep (se 1 (by rfl) ⟨1303781, by rfl⟩ : syracuseStep 1738375 = 2607563) B2607563
theorem B2606735 : Blo 1736569 2606735 := bstep (se 1 (by rfl) ⟨1955051, by rfl⟩ : syracuseStep 2606735 = 3910103) B3910103
theorem B1738383 : Blo 1736569 1738383 := bstep (se 1 (by rfl) ⟨1303787, by rfl⟩ : syracuseStep 1738383 = 2607575) B2607575
theorem B4695737 : Blo 1736569 4695737 := bstep (se 2 (by rfl) ⟨1760901, by rfl⟩ : syracuseStep 4695737 = 3521803) B3521803
theorem B2606777 : Blo 1736569 2606777 := bstep (se 2 (by rfl) ⟨977541, by rfl⟩ : syracuseStep 2606777 = 1955083) B1955083
theorem B1738427 : Blo 1736569 1738427 := bstep (se 1 (by rfl) ⟨1303820, by rfl⟩ : syracuseStep 1738427 = 2607641) B2607641
theorem B9397961 : Blo 1736569 9397961 := bstep (se 2 (by rfl) ⟨3524235, by rfl⟩ : syracuseStep 9397961 = 7048471) B7048471
theorem B8800001 : Blo 1736569 8800001 := bstep (se 2 (by rfl) ⟨3300000, by rfl⟩ : syracuseStep 8800001 = 6600001) B6600001
theorem B2606855 : Blo 1736569 2606855 := bstep (se 1 (by rfl) ⟨1955141, by rfl⟩ : syracuseStep 2606855 = 3910283) B3910283
theorem B1738503 : Blo 1736569 1738503 := bstep (se 1 (by rfl) ⟨1303877, by rfl⟩ : syracuseStep 1738503 = 2607755) B2607755
theorem B8038159 : Blo 1736569 8038159 := bstep (se 1 (by rfl) ⟨6028619, by rfl⟩ : syracuseStep 8038159 = 12057239) B12057239
theorem B1738511 : Blo 1736569 1738511 := bstep (se 1 (by rfl) ⟨1303883, by rfl⟩ : syracuseStep 1738511 = 2607767) B2607767
theorem B3909419 : Blo 1736569 3909419 := bstep (se 1 (by rfl) ⟨2932064, by rfl⟩ : syracuseStep 3909419 = 5864129) B5864129
theorem B2606891 : Blo 1736569 2606891 := bstep (se 1 (by rfl) ⟨1955168, by rfl⟩ : syracuseStep 2606891 = 3910337) B3910337
theorem B4949819 : Blo 1736569 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B1738555 : Blo 1736569 1738555 := bstep (se 1 (by rfl) ⟨1303916, by rfl⟩ : syracuseStep 1738555 = 2607833) B2607833
theorem B2606921 : Blo 1736569 2606921 := bstep (se 2 (by rfl) ⟨977595, by rfl⟩ : syracuseStep 2606921 = 1955191) B1955191
theorem B2607035 : Blo 1736569 2607035 := bstep (se 1 (by rfl) ⟨1955276, by rfl⟩ : syracuseStep 2607035 = 3910553) B3910553
theorem B2607095 : Blo 1736569 2607095 := bstep (se 1 (by rfl) ⟨1955321, by rfl⟩ : syracuseStep 2607095 = 3910643) B3910643
theorem B5867531 : Blo 1736569 5867531 := bstep (se 1 (by rfl) ⟨4400648, by rfl⟩ : syracuseStep 5867531 = 8801297) B8801297
theorem B2607119 : Blo 1736569 2607119 := bstep (se 1 (by rfl) ⟨1955339, by rfl⟩ : syracuseStep 2607119 = 3910679) B3910679
theorem B2607161 : Blo 1736569 2607161 := bstep (se 2 (by rfl) ⟨977685, by rfl⟩ : syracuseStep 2607161 = 1955371) B1955371
theorem B13371479 : Blo 1736569 13371479 := bstep (se 1 (by rfl) ⟨10028609, by rfl⟩ : syracuseStep 13371479 = 20057219) B20057219
theorem B5867639 : Blo 1736569 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B2607239 : Blo 1736569 2607239 := bstep (se 1 (by rfl) ⟨1955429, by rfl⟩ : syracuseStep 2607239 = 3910859) B3910859
theorem B3909779 : Blo 1736569 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B2607275 : Blo 1736569 2607275 := bstep (se 1 (by rfl) ⟨1955456, by rfl⟩ : syracuseStep 2607275 = 3910913) B3910913
theorem B3909833 : Blo 1736569 3909833 := bstep (se 2 (by rfl) ⟨1466187, by rfl⟩ : syracuseStep 3909833 = 2932375) B2932375
theorem B2607305 : Blo 1736569 2607305 := bstep (se 2 (by rfl) ⟨977739, by rfl⟩ : syracuseStep 2607305 = 1955479) B1955479
theorem B54241589 : Blo 1736569 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B2607419 : Blo 1736569 2607419 := bstep (se 1 (by rfl) ⟨1955564, by rfl⟩ : syracuseStep 2607419 = 3911129) B3911129
theorem B2607479 : Blo 1736569 2607479 := bstep (se 1 (by rfl) ⟨1955609, by rfl⟩ : syracuseStep 2607479 = 3911219) B3911219
theorem B2607503 : Blo 1736569 2607503 := bstep (se 1 (by rfl) ⟨1955627, by rfl⟩ : syracuseStep 2607503 = 3911255) B3911255
theorem B2607545 : Blo 1736569 2607545 := bstep (se 2 (by rfl) ⟨977829, by rfl⟩ : syracuseStep 2607545 = 1955659) B1955659
theorem B57117149 : Blo 1736569 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B2607623 : Blo 1736569 2607623 := bstep (se 1 (by rfl) ⟨1955717, by rfl⟩ : syracuseStep 2607623 = 3911435) B3911435
theorem B8800811 : Blo 1736569 8800811 := bstep (se 1 (by rfl) ⟨6600608, by rfl⟩ : syracuseStep 8800811 = 13201217) B13201217
theorem B2607659 : Blo 1736569 2607659 := bstep (se 1 (by rfl) ⟨1955744, by rfl⟩ : syracuseStep 2607659 = 3911489) B3911489
theorem B4950571 : Blo 1736569 4950571 := bstep (se 1 (by rfl) ⟨3712928, by rfl⟩ : syracuseStep 4950571 = 7425857) B7425857
theorem B2607689 : Blo 1736569 2607689 := bstep (se 2 (by rfl) ⟨977883, by rfl⟩ : syracuseStep 2607689 = 1955767) B1955767
theorem B2607803 : Blo 1736569 2607803 := bstep (se 1 (by rfl) ⟨1955852, by rfl⟩ : syracuseStep 2607803 = 3911705) B3911705
theorem B4172489 : Blo 1736569 4172489 := bstep (se 2 (by rfl) ⟨1564683, by rfl⟩ : syracuseStep 4172489 = 3129367) B3129367
theorem B2640647 : Blo 1736569 2640647 := bstep (se 1 (by rfl) ⟨1980485, by rfl⟩ : syracuseStep 2640647 = 3960971) B3960971
theorem B2198279 : Blo 1736569 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B4950845 : Blo 1736569 4950845 := bstep (se 3 (by rfl) ⟨928283, by rfl⟩ : syracuseStep 4950845 = 1856567) B1856567
theorem B3910535 : Blo 1736569 3910535 := bstep (se 1 (by rfl) ⟨2932901, by rfl⟩ : syracuseStep 3910535 = 5865803) B5865803
theorem B9890707 : Blo 1736569 9890707 := bstep (se 1 (by rfl) ⟨7418030, by rfl⟩ : syracuseStep 9890707 = 14836061) B14836061
theorem B8793035 : Blo 1736569 8793035 := bstep (se 1 (by rfl) ⟨6594776, by rfl⟩ : syracuseStep 8793035 = 13189553) B13189553
theorem B9898955 : Blo 1736569 9898955 := bstep (se 1 (by rfl) ⟨7424216, by rfl⟩ : syracuseStep 9898955 = 14848433) B14848433
theorem B16698413 : Blo 1736569 16698413 := bstep (se 3 (by rfl) ⟨3130952, by rfl⟩ : syracuseStep 16698413 = 6261905) B6261905
theorem B3910715 : Blo 1736569 3910715 := bstep (se 1 (by rfl) ⟨2933036, by rfl⟩ : syracuseStep 3910715 = 5866073) B5866073
theorem B3910841 : Blo 1736569 3910841 := bstep (se 2 (by rfl) ⟨1466565, by rfl⟩ : syracuseStep 3910841 = 2933131) B2933131
theorem B8793359 : Blo 1736569 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B29699459 : Blo 1736569 29699459 := bstep (se 1 (by rfl) ⟨22274594, by rfl⟩ : syracuseStep 29699459 = 44549189) B44549189
theorem B2198927 : Blo 1736569 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B5565881 : Blo 1736569 5565881 := bstep (se 2 (by rfl) ⟨2087205, by rfl⟩ : syracuseStep 5565881 = 4174411) B4174411
theorem B3911183 : Blo 1736569 3911183 := bstep (se 1 (by rfl) ⟨2933387, by rfl⟩ : syracuseStep 3911183 = 5866775) B5866775
theorem B3911201 : Blo 1736569 3911201 := bstep (se 2 (by rfl) ⟨1466700, by rfl⟩ : syracuseStep 3911201 = 2933401) B2933401
theorem B4460075 : Blo 1736569 4460075 := bstep (se 1 (by rfl) ⟨3345056, by rfl⟩ : syracuseStep 4460075 = 6690113) B6690113
theorem B21131009 : Blo 1736569 21131009 := bstep (se 2 (by rfl) ⟨7924128, by rfl⟩ : syracuseStep 21131009 = 15848257) B15848257
theorem B10563365 : Blo 1736569 10563365 := bstep (se 4 (by rfl) ⟨990315, by rfl⟩ : syracuseStep 10563365 = 1980631) B1980631
theorem B12701555 : Blo 1736569 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B3911543 : Blo 1736569 3911543 := bstep (se 1 (by rfl) ⟨2933657, by rfl⟩ : syracuseStep 3911543 = 5867315) B5867315
theorem B1953679 : Blo 1736569 1953679 := bstep (se 1 (by rfl) ⟨1465259, by rfl⟩ : syracuseStep 1953679 = 2930519) B2930519
theorem B5861267 : Blo 1736569 5861267 := bstep (se 1 (by rfl) ⟨4395950, by rfl⟩ : syracuseStep 5861267 = 8791901) B8791901
theorem B1855495 : Blo 1736569 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B3911723 : Blo 1736569 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B2642107 : Blo 1736569 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B9040187 : Blo 1736569 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B10563929 : Blo 1736569 10563929 := bstep (se 2 (by rfl) ⟨3961473, by rfl⟩ : syracuseStep 10563929 = 7922947) B7922947
theorem B1954183 : Blo 1736569 1954183 := bstep (se 1 (by rfl) ⟨1465637, by rfl⟩ : syracuseStep 1954183 = 2931275) B2931275
theorem B1954363 : Blo 1736569 1954363 := bstep (se 1 (by rfl) ⟨1465772, by rfl⟩ : syracuseStep 1954363 = 2931545) B2931545
theorem B9892439 : Blo 1736569 9892439 := bstep (se 1 (by rfl) ⟨7419329, by rfl⟩ : syracuseStep 9892439 = 14838659) B14838659
theorem B8794817 : Blo 1736569 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B2781967 : Blo 1736569 2781967 := bstep (se 1 (by rfl) ⟨2086475, by rfl⟩ : syracuseStep 2781967 = 4172951) B4172951
theorem B4395809 : Blo 1736569 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1856315 : Blo 1736569 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B192779189 : Blo 1736569 192779189 := bstep (se 5 (by rfl) ⟨9036524, by rfl⟩ : syracuseStep 192779189 = 18073049) B18073049
theorem B1954831 : Blo 1736569 1954831 := bstep (se 1 (by rfl) ⟨1466123, by rfl⟩ : syracuseStep 1954831 = 2932247) B2932247
theorem B13194413 : Blo 1736569 13194413 := bstep (se 3 (by rfl) ⟨2473952, by rfl⟩ : syracuseStep 13194413 = 4947905) B4947905
theorem B10573001 : Blo 1736569 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B5862671 : Blo 1736569 5862671 := bstep (se 1 (by rfl) ⟨4397003, by rfl⟩ : syracuseStep 5862671 = 8794007) B8794007
theorem B3298619 : Blo 1736569 3298619 := bstep (se 1 (by rfl) ⟨2473964, by rfl⟩ : syracuseStep 3298619 = 4947929) B4947929
theorem B17831261 : Blo 1736569 17831261 := bstep (se 3 (by rfl) ⟨3343361, by rfl⟩ : syracuseStep 17831261 = 6686723) B6686723
theorem B4175219 : Blo 1736569 4175219 := bstep (se 1 (by rfl) ⟨3131414, by rfl⟩ : syracuseStep 4175219 = 6262829) B6262829
theorem B17839565 : Blo 1736569 17839565 := bstep (se 3 (by rfl) ⟨3344918, by rfl⟩ : syracuseStep 17839565 = 6689837) B6689837
theorem B1955335 : Blo 1736569 1955335 := bstep (se 1 (by rfl) ⟨1466501, by rfl⟩ : syracuseStep 1955335 = 2933003) B2933003
theorem B5862941 : Blo 1736569 5862941 := bstep (se 3 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 5862941 = 2198603) B2198603
theorem B5568061 : Blo 1736569 5568061 := bstep (se 3 (by rfl) ⟨1044011, by rfl⟩ : syracuseStep 5568061 = 2088023) B2088023
theorem B16692803 : Blo 1736569 16692803 := bstep (se 1 (by rfl) ⟨12519602, by rfl⟩ : syracuseStep 16692803 = 25039205) B25039205
theorem B4175479 : Blo 1736569 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B4175507 : Blo 1736569 4175507 := bstep (se 1 (by rfl) ⟨3131630, by rfl⟩ : syracuseStep 4175507 = 6263261) B6263261
theorem B1955515 : Blo 1736569 1955515 := bstep (se 1 (by rfl) ⟨1466636, by rfl⟩ : syracuseStep 1955515 = 2933273) B2933273
theorem B4396801 : Blo 1736569 4396801 := bstep (se 2 (by rfl) ⟨1648800, by rfl⟩ : syracuseStep 4396801 = 3297601) B3297601
theorem B2258695 : Blo 1736569 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B3299105 : Blo 1736569 3299105 := bstep (se 2 (by rfl) ⟨1237164, by rfl⟩ : syracuseStep 3299105 = 2474329) B2474329
theorem B43439921 : Blo 1736569 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B7419707 : Blo 1736569 7419707 := bstep (se 1 (by rfl) ⟨5564780, by rfl⟩ : syracuseStep 7419707 = 11129561) B11129561
theorem B16701299 : Blo 1736569 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B4945799 : Blo 1736569 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B16701335 : Blo 1736569 16701335 := bstep (se 1 (by rfl) ⟨12526001, by rfl⟩ : syracuseStep 16701335 = 25052003) B25052003
theorem B8796113 : Blo 1736569 8796113 := bstep (se 2 (by rfl) ⟨3298542, by rfl⟩ : syracuseStep 8796113 = 6597085) B6597085
theorem B4945981 : Blo 1736569 4945981 := bstep (se 3 (by rfl) ⟨927371, by rfl⟩ : syracuseStep 4945981 = 1854743) B1854743
theorem B6600791 : Blo 1736569 6600791 := bstep (se 1 (by rfl) ⟨4950593, by rfl⟩ : syracuseStep 6600791 = 9901187) B9901187
theorem B2783351 : Blo 1736569 2783351 := bstep (se 1 (by rfl) ⟨2087513, by rfl⟩ : syracuseStep 2783351 = 4175027) B4175027
theorem B3299447 : Blo 1736569 3299447 := bstep (se 1 (by rfl) ⟨2474585, by rfl⟩ : syracuseStep 3299447 = 4949171) B4949171
theorem B4397399 : Blo 1736569 4397399 := bstep (se 1 (by rfl) ⟨3298049, by rfl⟩ : syracuseStep 4397399 = 6596099) B6596099
theorem B2931079 : Blo 1736569 2931079 := bstep (se 1 (by rfl) ⟨2198309, by rfl⟩ : syracuseStep 2931079 = 4396619) B4396619
theorem B15038905 : Blo 1736569 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B4946447 : Blo 1736569 4946447 := bstep (se 1 (by rfl) ⟨3709835, by rfl⟩ : syracuseStep 4946447 = 7419671) B7419671
theorem B4397611 : Blo 1736569 4397611 := bstep (se 1 (by rfl) ⟨3298208, by rfl⟩ : syracuseStep 4397611 = 6596417) B6596417
theorem B7928363 : Blo 1736569 7928363 := bstep (se 1 (by rfl) ⟨5946272, by rfl⟩ : syracuseStep 7928363 = 11892545) B11892545
theorem B29686337 : Blo 1736569 29686337 := bstep (se 2 (by rfl) ⟨11132376, by rfl⟩ : syracuseStep 29686337 = 22264753) B22264753
theorem B23788151 : Blo 1736569 23788151 := bstep (se 1 (by rfl) ⟨17841113, by rfl⟩ : syracuseStep 23788151 = 35682227) B35682227
theorem B4397753 : Blo 1736569 4397753 := bstep (se 2 (by rfl) ⟨1649157, by rfl⟩ : syracuseStep 4397753 = 3298315) B3298315
theorem B30489281 : Blo 1736569 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B2472763 : Blo 1736569 2472763 := bstep (se 1 (by rfl) ⟨1854572, by rfl⟩ : syracuseStep 2472763 = 3709145) B3709145
theorem B5864345 : Blo 1736569 5864345 := bstep (se 2 (by rfl) ⟨2199129, by rfl⟩ : syracuseStep 5864345 = 4398259) B4398259
theorem B2931727 : Blo 1736569 2931727 := bstep (se 1 (by rfl) ⟨2198795, by rfl⟩ : syracuseStep 2931727 = 4397591) B4397591
theorem B2784299 : Blo 1736569 2784299 := bstep (se 1 (by rfl) ⟨2088224, by rfl⟩ : syracuseStep 2784299 = 4176449) B4176449
theorem B16071853 : Blo 1736569 16071853 := bstep (se 3 (by rfl) ⟨3013472, by rfl⟩ : syracuseStep 16071853 = 6026945) B6026945
theorem B2473463 : Blo 1736569 2473463 := bstep (se 1 (by rfl) ⟨1855097, by rfl⟩ : syracuseStep 2473463 = 3710195) B3710195
theorem B7421483 : Blo 1736569 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B2932267 : Blo 1736569 2932267 := bstep (se 1 (by rfl) ⟨2199200, by rfl⟩ : syracuseStep 2932267 = 4398401) B4398401
theorem B13196843 : Blo 1736569 13196843 := bstep (se 1 (by rfl) ⟨9897632, by rfl⟩ : syracuseStep 13196843 = 19795265) B19795265
theorem B10567235 : Blo 1736569 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B5865047 : Blo 1736569 5865047 := bstep (se 1 (by rfl) ⟨4398785, by rfl⟩ : syracuseStep 5865047 = 8797571) B8797571
theorem B4398745 : Blo 1736569 4398745 := bstep (se 2 (by rfl) ⟨1649529, by rfl⟩ : syracuseStep 4398745 = 3299059) B3299059
theorem B2932409 : Blo 1736569 2932409 := bstep (se 2 (by rfl) ⟨1099653, by rfl⟩ : syracuseStep 2932409 = 2199307) B2199307
theorem B4947713 : Blo 1736569 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B2604857 : Blo 1736569 2604857 := bstep (se 2 (by rfl) ⟨976821, by rfl⟩ : syracuseStep 2604857 = 1953643) B1953643
theorem B4398907 : Blo 1736569 4398907 := bstep (se 1 (by rfl) ⟨3299180, by rfl⟩ : syracuseStep 4398907 = 6598361) B6598361
theorem B5013335 : Blo 1736569 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B1736583 : Blo 1736569 1736583 := bstep (se 1 (by rfl) ⟨1302437, by rfl⟩ : syracuseStep 1736583 = 2604875) B2604875
theorem B2604935 : Blo 1736569 2604935 := bstep (se 1 (by rfl) ⟨1953701, by rfl⟩ : syracuseStep 2604935 = 3907403) B3907403
theorem B1736591 : Blo 1736569 1736591 := bstep (se 1 (by rfl) ⟨1302443, by rfl⟩ : syracuseStep 1736591 = 2604887) B2604887
theorem B3907475 : Blo 1736569 3907475 := bstep (se 1 (by rfl) ⟨2930606, by rfl⟩ : syracuseStep 3907475 = 5861213) B5861213
theorem B2604971 : Blo 1736569 2604971 := bstep (se 1 (by rfl) ⟨1953728, by rfl⟩ : syracuseStep 2604971 = 3907457) B3907457
theorem B1736635 : Blo 1736569 1736635 := bstep (se 1 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 1736635 = 2604953) B2604953
theorem B2605001 : Blo 1736569 2605001 := bstep (se 2 (by rfl) ⟨976875, by rfl⟩ : syracuseStep 2605001 = 1953751) B1953751
theorem B3907529 : Blo 1736569 3907529 := bstep (se 2 (by rfl) ⟨1465323, by rfl⟩ : syracuseStep 3907529 = 2930647) B2930647
theorem B13189067 : Blo 1736569 13189067 := bstep (se 1 (by rfl) ⟨9891800, by rfl⟩ : syracuseStep 13189067 = 19783601) B19783601
theorem B4399049 : Blo 1736569 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B7831505 : Blo 1736569 7831505 := bstep (se 2 (by rfl) ⟨2936814, by rfl⟩ : syracuseStep 7831505 = 5873629) B5873629
theorem B5865479 : Blo 1736569 5865479 := bstep (se 1 (by rfl) ⟨4399109, by rfl⟩ : syracuseStep 5865479 = 8798219) B8798219
theorem B2473993 : Blo 1736569 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B1736743 : Blo 1736569 1736743 := bstep (se 1 (by rfl) ⟨1302557, by rfl⟩ : syracuseStep 1736743 = 2605115) B2605115
theorem B42270781 : Blo 1736569 42270781 := bstep (se 3 (by rfl) ⟨7925771, by rfl⟩ : syracuseStep 42270781 = 15851543) B15851543
theorem B1736783 : Blo 1736569 1736783 := bstep (se 1 (by rfl) ⟨1302587, by rfl⟩ : syracuseStep 1736783 = 2605175) B2605175
theorem B6594641 : Blo 1736569 6594641 := bstep (se 2 (by rfl) ⟨2472990, by rfl⟩ : syracuseStep 6594641 = 4945981) B4945981
theorem B1736799 : Blo 1736569 1736799 := bstep (se 1 (by rfl) ⟨1302599, by rfl⟩ : syracuseStep 1736799 = 2605199) B2605199
theorem B5865587 : Blo 1736569 5865587 := bstep (se 1 (by rfl) ⟨4399190, by rfl⟩ : syracuseStep 5865587 = 8798381) B8798381
theorem B1736827 : Blo 1736569 1736827 := bstep (se 1 (by rfl) ⟨1302620, by rfl⟩ : syracuseStep 1736827 = 2605241) B2605241
theorem B1736879 : Blo 1736569 1736879 := bstep (se 1 (by rfl) ⟨1302659, by rfl⟩ : syracuseStep 1736879 = 2605319) B2605319
theorem B1736903 : Blo 1736569 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B1736923 : Blo 1736569 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B3522809 : Blo 1736569 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B1736999 : Blo 1736569 1736999 := bstep (se 1 (by rfl) ⟨1302749, by rfl⟩ : syracuseStep 1736999 = 2605499) B2605499
theorem B1737039 : Blo 1736569 1737039 := bstep (se 1 (by rfl) ⟨1302779, by rfl⟩ : syracuseStep 1737039 = 2605559) B2605559
theorem B1737055 : Blo 1736569 1737055 := bstep (se 1 (by rfl) ⟨1302791, by rfl⟩ : syracuseStep 1737055 = 2605583) B2605583
theorem B1737083 : Blo 1736569 1737083 := bstep (se 1 (by rfl) ⟨1302812, by rfl⟩ : syracuseStep 1737083 = 2605625) B2605625
theorem B5865857 : Blo 1736569 5865857 := bstep (se 2 (by rfl) ⟨2199696, by rfl⟩ : syracuseStep 5865857 = 4399393) B4399393
theorem B6594959 : Blo 1736569 6594959 := bstep (se 1 (by rfl) ⟨4946219, by rfl⟩ : syracuseStep 6594959 = 9892439) B9892439
theorem B2605487 : Blo 1736569 2605487 := bstep (se 1 (by rfl) ⟨1954115, by rfl⟩ : syracuseStep 2605487 = 3908231) B3908231
theorem B1737135 : Blo 1736569 1737135 := bstep (se 1 (by rfl) ⟨1302851, by rfl⟩ : syracuseStep 1737135 = 2605703) B2605703
theorem B1737159 : Blo 1736569 1737159 := bstep (se 1 (by rfl) ⟨1302869, by rfl⟩ : syracuseStep 1737159 = 2605739) B2605739
theorem B1737179 : Blo 1736569 1737179 := bstep (se 1 (by rfl) ⟨1302884, by rfl⟩ : syracuseStep 1737179 = 2605769) B2605769
theorem B3908105 : Blo 1736569 3908105 := bstep (se 2 (by rfl) ⟨1465539, by rfl⟩ : syracuseStep 3908105 = 2931079) B2931079
theorem B2605577 : Blo 1736569 2605577 := bstep (se 2 (by rfl) ⟨977091, by rfl⟩ : syracuseStep 2605577 = 1954183) B1954183
theorem B2605607 : Blo 1736569 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1737255 : Blo 1736569 1737255 := bstep (se 1 (by rfl) ⟨1302941, by rfl⟩ : syracuseStep 1737255 = 2605883) B2605883
theorem B1737295 : Blo 1736569 1737295 := bstep (se 1 (by rfl) ⟨1302971, by rfl⟩ : syracuseStep 1737295 = 2605943) B2605943
theorem B2933327 : Blo 1736569 2933327 := bstep (se 1 (by rfl) ⟨2199995, by rfl⟩ : syracuseStep 2933327 = 4399991) B4399991
theorem B1737311 : Blo 1736569 1737311 := bstep (se 1 (by rfl) ⟨1302983, by rfl⟩ : syracuseStep 1737311 = 2605967) B2605967
theorem B6259297 : Blo 1736569 6259297 := bstep (se 2 (by rfl) ⟨2347236, by rfl⟩ : syracuseStep 6259297 = 4694473) B4694473
theorem B2605691 : Blo 1736569 2605691 := bstep (se 1 (by rfl) ⟨1954268, by rfl⟩ : syracuseStep 2605691 = 3908537) B3908537
theorem B1737339 : Blo 1736569 1737339 := bstep (se 1 (by rfl) ⟨1303004, by rfl⟩ : syracuseStep 1737339 = 2606009) B2606009
theorem B1737391 : Blo 1736569 1737391 := bstep (se 1 (by rfl) ⟨1303043, by rfl⟩ : syracuseStep 1737391 = 2606087) B2606087
theorem B1737415 : Blo 1736569 1737415 := bstep (se 1 (by rfl) ⟨1303061, by rfl⟩ : syracuseStep 1737415 = 2606123) B2606123
theorem B23790289 : Blo 1736569 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B1737435 : Blo 1736569 1737435 := bstep (se 1 (by rfl) ⟨1303076, by rfl⟩ : syracuseStep 1737435 = 2606153) B2606153
theorem B2605817 : Blo 1736569 2605817 := bstep (se 2 (by rfl) ⟨977181, by rfl⟩ : syracuseStep 2605817 = 1954363) B1954363
theorem B1737511 : Blo 1736569 1737511 := bstep (se 1 (by rfl) ⟨1303133, by rfl⟩ : syracuseStep 1737511 = 2606267) B2606267
theorem B1737551 : Blo 1736569 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B3908447 : Blo 1736569 3908447 := bstep (se 1 (by rfl) ⟨2931335, by rfl⟩ : syracuseStep 3908447 = 5862671) B5862671
theorem B2605919 : Blo 1736569 2605919 := bstep (se 1 (by rfl) ⟨1954439, by rfl⟩ : syracuseStep 2605919 = 3908879) B3908879
theorem B1737567 : Blo 1736569 1737567 := bstep (se 1 (by rfl) ⟨1303175, by rfl⟩ : syracuseStep 1737567 = 2606351) B2606351
theorem B2605931 : Blo 1736569 2605931 := bstep (se 1 (by rfl) ⟨1954448, by rfl⟩ : syracuseStep 2605931 = 3908897) B3908897
theorem B1737595 : Blo 1736569 1737595 := bstep (se 1 (by rfl) ⟨1303196, by rfl⟩ : syracuseStep 1737595 = 2606393) B2606393
theorem B11887507 : Blo 1736569 11887507 := bstep (se 1 (by rfl) ⟨8915630, by rfl⟩ : syracuseStep 11887507 = 17831261) B17831261
theorem B4948897 : Blo 1736569 4948897 := bstep (se 2 (by rfl) ⟨1855836, by rfl⟩ : syracuseStep 4948897 = 3711673) B3711673
theorem B1737647 : Blo 1736569 1737647 := bstep (se 1 (by rfl) ⟨1303235, by rfl⟩ : syracuseStep 1737647 = 2606471) B2606471
theorem B1737671 : Blo 1736569 1737671 := bstep (se 1 (by rfl) ⟨1303253, by rfl⟩ : syracuseStep 1737671 = 2606507) B2606507
theorem B1737691 : Blo 1736569 1737691 := bstep (se 1 (by rfl) ⟨1303268, by rfl⟩ : syracuseStep 1737691 = 2606537) B2606537
theorem B13198301 : Blo 1736569 13198301 := bstep (se 3 (by rfl) ⟨2474681, by rfl⟩ : syracuseStep 13198301 = 4949363) B4949363
theorem B3908627 : Blo 1736569 3908627 := bstep (se 1 (by rfl) ⟨2931470, by rfl⟩ : syracuseStep 3908627 = 5862941) B5862941
theorem B1737767 : Blo 1736569 1737767 := bstep (se 1 (by rfl) ⟨1303325, by rfl⟩ : syracuseStep 1737767 = 2606651) B2606651
theorem B2606159 : Blo 1736569 2606159 := bstep (se 1 (by rfl) ⟨1954619, by rfl⟩ : syracuseStep 2606159 = 3909239) B3909239
theorem B1737807 : Blo 1736569 1737807 := bstep (se 1 (by rfl) ⟨1303355, by rfl⟩ : syracuseStep 1737807 = 2606711) B2606711
theorem B1737823 : Blo 1736569 1737823 := bstep (se 1 (by rfl) ⟨1303367, by rfl⟩ : syracuseStep 1737823 = 2606735) B2606735
theorem B1737851 : Blo 1736569 1737851 := bstep (se 1 (by rfl) ⟨1303388, by rfl⟩ : syracuseStep 1737851 = 2606777) B2606777
theorem B5866667 : Blo 1736569 5866667 := bstep (se 1 (by rfl) ⟨4400000, by rfl⟩ : syracuseStep 5866667 = 8800001) B8800001
theorem B1737903 : Blo 1736569 1737903 := bstep (se 1 (by rfl) ⟨1303427, by rfl⟩ : syracuseStep 1737903 = 2606855) B2606855
theorem B2606279 : Blo 1736569 2606279 := bstep (se 1 (by rfl) ⟨1954709, by rfl⟩ : syracuseStep 2606279 = 3909419) B3909419
theorem B1737927 : Blo 1736569 1737927 := bstep (se 1 (by rfl) ⟨1303445, by rfl⟩ : syracuseStep 1737927 = 2606891) B2606891
theorem B28959947 : Blo 1736569 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B1737947 : Blo 1736569 1737947 := bstep (se 1 (by rfl) ⟨1303460, by rfl⟩ : syracuseStep 1737947 = 2606921) B2606921
theorem B11134199 : Blo 1736569 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B11134223 : Blo 1736569 11134223 := bstep (se 1 (by rfl) ⟨8350667, by rfl⟩ : syracuseStep 11134223 = 16701335) B16701335
theorem B1738023 : Blo 1736569 1738023 := bstep (se 1 (by rfl) ⟨1303517, by rfl⟩ : syracuseStep 1738023 = 2607035) B2607035
theorem B6595901 : Blo 1736569 6595901 := bstep (se 3 (by rfl) ⟨1236731, by rfl⟩ : syracuseStep 6595901 = 2473463) B2473463
theorem B1738063 : Blo 1736569 1738063 := bstep (se 1 (by rfl) ⟨1303547, by rfl⟩ : syracuseStep 1738063 = 2607095) B2607095
theorem B1738079 : Blo 1736569 1738079 := bstep (se 1 (by rfl) ⟨1303559, by rfl⟩ : syracuseStep 1738079 = 2607119) B2607119
theorem B3908969 : Blo 1736569 3908969 := bstep (se 2 (by rfl) ⟨1465863, by rfl⟩ : syracuseStep 3908969 = 2931727) B2931727
theorem B2606441 : Blo 1736569 2606441 := bstep (se 2 (by rfl) ⟨977415, by rfl⟩ : syracuseStep 2606441 = 1954831) B1954831
theorem B13190525 : Blo 1736569 13190525 := bstep (se 3 (by rfl) ⟨2473223, by rfl⟩ : syracuseStep 13190525 = 4946447) B4946447
theorem B1738107 : Blo 1736569 1738107 := bstep (se 1 (by rfl) ⟨1303580, by rfl⟩ : syracuseStep 1738107 = 2607161) B2607161
theorem B8914319 : Blo 1736569 8914319 := bstep (se 1 (by rfl) ⟨6685739, by rfl⟩ : syracuseStep 8914319 = 13371479) B13371479
theorem B4400527 : Blo 1736569 4400527 := bstep (se 1 (by rfl) ⟨3300395, by rfl⟩ : syracuseStep 4400527 = 6600791) B6600791
theorem B1738159 : Blo 1736569 1738159 := bstep (se 1 (by rfl) ⟨1303619, by rfl⟩ : syracuseStep 1738159 = 2607239) B2607239
theorem B2606519 : Blo 1736569 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B1738183 : Blo 1736569 1738183 := bstep (se 1 (by rfl) ⟨1303637, by rfl⟩ : syracuseStep 1738183 = 2607275) B2607275
theorem B2606555 : Blo 1736569 2606555 := bstep (se 1 (by rfl) ⟨1954916, by rfl⟩ : syracuseStep 2606555 = 3909833) B3909833
theorem B1738203 : Blo 1736569 1738203 := bstep (se 1 (by rfl) ⟨1303652, by rfl⟩ : syracuseStep 1738203 = 2607305) B2607305
theorem B7046689 : Blo 1736569 7046689 := bstep (se 2 (by rfl) ⟨2642508, by rfl⟩ : syracuseStep 7046689 = 5285017) B5285017
theorem B1738279 : Blo 1736569 1738279 := bstep (se 1 (by rfl) ⟨1303709, by rfl⟩ : syracuseStep 1738279 = 2607419) B2607419
theorem B1738319 : Blo 1736569 1738319 := bstep (se 1 (by rfl) ⟨1303739, by rfl⟩ : syracuseStep 1738319 = 2607479) B2607479
theorem B1738335 : Blo 1736569 1738335 := bstep (se 1 (by rfl) ⟨1303751, by rfl⟩ : syracuseStep 1738335 = 2607503) B2607503
theorem B1738363 : Blo 1736569 1738363 := bstep (se 1 (by rfl) ⟨1303772, by rfl⟩ : syracuseStep 1738363 = 2607545) B2607545
theorem B38078099 : Blo 1736569 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B1738415 : Blo 1736569 1738415 := bstep (se 1 (by rfl) ⟨1303811, by rfl⟩ : syracuseStep 1738415 = 2607623) B2607623
theorem B5285575 : Blo 1736569 5285575 := bstep (se 1 (by rfl) ⟨3964181, by rfl⟩ : syracuseStep 5285575 = 7928363) B7928363
theorem B5867207 : Blo 1736569 5867207 := bstep (se 1 (by rfl) ⟨4400405, by rfl⟩ : syracuseStep 5867207 = 8800811) B8800811
theorem B1738439 : Blo 1736569 1738439 := bstep (se 1 (by rfl) ⟨1303829, by rfl⟩ : syracuseStep 1738439 = 2607659) B2607659
theorem B1738459 : Blo 1736569 1738459 := bstep (se 1 (by rfl) ⟨1303844, by rfl⟩ : syracuseStep 1738459 = 2607689) B2607689
theorem B11134685 : Blo 1736569 11134685 := bstep (se 3 (by rfl) ⟨2087753, by rfl⟩ : syracuseStep 11134685 = 4175507) B4175507
theorem B1738535 : Blo 1736569 1738535 := bstep (se 1 (by rfl) ⟨1303901, by rfl⟩ : syracuseStep 1738535 = 2607803) B2607803
theorem B20326187 : Blo 1736569 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B2607023 : Blo 1736569 2607023 := bstep (se 1 (by rfl) ⟨1955267, by rfl⟩ : syracuseStep 2607023 = 3910535) B3910535
theorem B3909563 : Blo 1736569 3909563 := bstep (se 1 (by rfl) ⟨2932172, by rfl⟩ : syracuseStep 3909563 = 5864345) B5864345
theorem B2607113 : Blo 1736569 2607113 := bstep (se 2 (by rfl) ⟨977667, by rfl⟩ : syracuseStep 2607113 = 1955335) B1955335
theorem B2607143 : Blo 1736569 2607143 := bstep (se 1 (by rfl) ⟨1955357, by rfl⟩ : syracuseStep 2607143 = 3910715) B3910715
theorem B3909689 : Blo 1736569 3909689 := bstep (se 2 (by rfl) ⟨1466133, by rfl⟩ : syracuseStep 3909689 = 2932267) B2932267
theorem B7424081 : Blo 1736569 7424081 := bstep (se 2 (by rfl) ⟨2784030, by rfl⟩ : syracuseStep 7424081 = 5568061) B5568061
theorem B2607227 : Blo 1736569 2607227 := bstep (se 1 (by rfl) ⟨1955420, by rfl⟩ : syracuseStep 2607227 = 3910841) B3910841
theorem B4950173 : Blo 1736569 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B2607353 : Blo 1736569 2607353 := bstep (se 2 (by rfl) ⟨977757, by rfl⟩ : syracuseStep 2607353 = 1955515) B1955515
theorem B2607455 : Blo 1736569 2607455 := bstep (se 1 (by rfl) ⟨1955591, by rfl⟩ : syracuseStep 2607455 = 3911183) B3911183
theorem B2607467 : Blo 1736569 2607467 := bstep (se 1 (by rfl) ⟨1955600, by rfl⟩ : syracuseStep 2607467 = 3911201) B3911201
theorem B3910031 : Blo 1736569 3910031 := bstep (se 1 (by rfl) ⟨2932523, by rfl⟩ : syracuseStep 3910031 = 5865047) B5865047
theorem B2607695 : Blo 1736569 2607695 := bstep (se 1 (by rfl) ⟨1955771, by rfl⟩ : syracuseStep 2607695 = 3911543) B3911543
theorem B8792711 : Blo 1736569 8792711 := bstep (se 1 (by rfl) ⟨6594533, by rfl⟩ : syracuseStep 8792711 = 13189067) B13189067
theorem B5221003 : Blo 1736569 5221003 := bstep (se 1 (by rfl) ⟨3915752, by rfl⟩ : syracuseStep 5221003 = 7831505) B7831505
theorem B2607815 : Blo 1736569 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B3910355 : Blo 1736569 3910355 := bstep (se 1 (by rfl) ⟨2932766, by rfl⟩ : syracuseStep 3910355 = 5865533) B5865533
theorem B7424797 : Blo 1736569 7424797 := bstep (se 3 (by rfl) ⟨1392149, by rfl⟩ : syracuseStep 7424797 = 2784299) B2784299
theorem B13380659 : Blo 1736569 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B4172971 : Blo 1736569 4172971 := bstep (se 1 (by rfl) ⟨3129728, by rfl⟩ : syracuseStep 4172971 = 6259457) B6259457
theorem B4173047 : Blo 1736569 4173047 := bstep (se 1 (by rfl) ⟨3129785, by rfl⟩ : syracuseStep 4173047 = 6259571) B6259571
theorem B128519459 : Blo 1736569 128519459 := bstep (se 1 (by rfl) ⟨96389594, by rfl⟩ : syracuseStep 128519459 = 192779189) B192779189
theorem B7048667 : Blo 1736569 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B2199079 : Blo 1736569 2199079 := bstep (se 1 (by rfl) ⟨1649309, by rfl⟩ : syracuseStep 2199079 = 3298619) B3298619
theorem B18787963 : Blo 1736569 18787963 := bstep (se 1 (by rfl) ⟨14090972, by rfl⟩ : syracuseStep 18787963 = 28181945) B28181945
theorem B3911291 : Blo 1736569 3911291 := bstep (se 1 (by rfl) ⟨2933468, by rfl⟩ : syracuseStep 3911291 = 5866937) B5866937
theorem B11128535 : Blo 1736569 11128535 := bstep (se 1 (by rfl) ⟨8346401, by rfl⟩ : syracuseStep 11128535 = 16692803) B16692803
theorem B3297017 : Blo 1736569 3297017 := bstep (se 2 (by rfl) ⟨1236381, by rfl⟩ : syracuseStep 3297017 = 2472763) B2472763
theorem B3911417 : Blo 1736569 3911417 := bstep (se 2 (by rfl) ⟨1466781, by rfl⟩ : syracuseStep 3911417 = 2933563) B2933563
theorem B2199403 : Blo 1736569 2199403 := bstep (se 1 (by rfl) ⟨1649552, by rfl⟩ : syracuseStep 2199403 = 3299105) B3299105
theorem B3297199 : Blo 1736569 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B3911687 : Blo 1736569 3911687 := bstep (se 1 (by rfl) ⟨2933765, by rfl⟩ : syracuseStep 3911687 = 5867531) B5867531
theorem B12046373 : Blo 1736569 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B8794169 : Blo 1736569 8794169 := bstep (se 2 (by rfl) ⟨3297813, by rfl⟩ : syracuseStep 8794169 = 6595627) B6595627
theorem B1855567 : Blo 1736569 1855567 := bstep (se 1 (by rfl) ⟨1391675, by rfl⟩ : syracuseStep 1855567 = 2783351) B2783351
theorem B2199631 : Blo 1736569 2199631 := bstep (se 1 (by rfl) ⟨1649723, by rfl⟩ : syracuseStep 2199631 = 3299447) B3299447
theorem B3911759 : Blo 1736569 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B2781659 : Blo 1736569 2781659 := bstep (se 1 (by rfl) ⟨2086244, by rfl⟩ : syracuseStep 2781659 = 4172489) B4172489
theorem B12521965 : Blo 1736569 12521965 := bstep (se 3 (by rfl) ⟨2347868, by rfl⟩ : syracuseStep 12521965 = 4695737) B4695737
theorem B10564121 : Blo 1736569 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B5862023 : Blo 1736569 5862023 := bstep (se 1 (by rfl) ⟨4396517, by rfl⟩ : syracuseStep 5862023 = 8793035) B8793035
theorem B6599303 : Blo 1736569 6599303 := bstep (se 1 (by rfl) ⟨4949477, by rfl⟩ : syracuseStep 6599303 = 9898955) B9898955
theorem B7041725 : Blo 1736569 7041725 := bstep (se 3 (by rfl) ⟨1320323, by rfl⟩ : syracuseStep 7041725 = 2640647) B2640647
theorem B5862077 : Blo 1736569 5862077 := bstep (se 3 (by rfl) ⟨1099139, by rfl⟩ : syracuseStep 5862077 = 2198279) B2198279
theorem B5567305 : Blo 1736569 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B5862239 : Blo 1736569 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B5862401 : Blo 1736569 5862401 := bstep (se 2 (by rfl) ⟨2198400, by rfl⟩ : syracuseStep 5862401 = 4396801) B4396801
theorem B1954939 : Blo 1736569 1954939 := bstep (se 1 (by rfl) ⟨1466204, by rfl⟩ : syracuseStep 1954939 = 2932409) B2932409
theorem B14087339 : Blo 1736569 14087339 := bstep (se 1 (by rfl) ⟨10565504, by rfl⟩ : syracuseStep 14087339 = 21131009) B21131009
theorem B3298475 : Blo 1736569 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B7042243 : Blo 1736569 7042243 := bstep (se 1 (by rfl) ⟨5281682, by rfl⟩ : syracuseStep 7042243 = 10563365) B10563365
theorem B8467703 : Blo 1736569 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B2381239 : Blo 1736569 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B7042619 : Blo 1736569 7042619 := bstep (se 1 (by rfl) ⟨5281964, by rfl⟩ : syracuseStep 7042619 = 10563929) B10563929
theorem B1955407 : Blo 1736569 1955407 := bstep (se 1 (by rfl) ⟨1466555, by rfl⟩ : syracuseStep 1955407 = 2933111) B2933111
theorem B15849107 : Blo 1736569 15849107 := bstep (se 1 (by rfl) ⟨11886830, by rfl⟩ : syracuseStep 15849107 = 23773661) B23773661
theorem B13194899 : Blo 1736569 13194899 := bstep (se 1 (by rfl) ⟨9896174, by rfl⟩ : syracuseStep 13194899 = 19792349) B19792349
theorem B171480725 : Blo 1736569 171480725 := bstep (se 6 (by rfl) ⟨4019079, by rfl⟩ : syracuseStep 171480725 = 8038159) B8038159
theorem B12523207 : Blo 1736569 12523207 := bstep (se 1 (by rfl) ⟨9392405, by rfl⟩ : syracuseStep 12523207 = 18784811) B18784811
theorem B5863211 : Blo 1736569 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B2930539 : Blo 1736569 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B20051873 : Blo 1736569 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B2086831 : Blo 1736569 2086831 := bstep (se 1 (by rfl) ⟨1565123, by rfl⟩ : syracuseStep 2086831 = 3130247) B3130247
theorem B15849425 : Blo 1736569 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B1955803 : Blo 1736569 1955803 := bstep (se 1 (by rfl) ⟨1466852, by rfl⟩ : syracuseStep 1955803 = 2933705) B2933705
theorem B3708947 : Blo 1736569 3708947 := bstep (se 1 (by rfl) ⟨2781710, by rfl⟩ : syracuseStep 3708947 = 5563421) B5563421
theorem B4397075 : Blo 1736569 4397075 := bstep (se 1 (by rfl) ⟨3297806, by rfl⟩ : syracuseStep 4397075 = 6595613) B6595613
theorem B5863481 : Blo 1736569 5863481 := bstep (se 2 (by rfl) ⟨2198805, by rfl⟩ : syracuseStep 5863481 = 4397611) B4397611
theorem B6600761 : Blo 1736569 6600761 := bstep (se 2 (by rfl) ⟨2475285, by rfl⟩ : syracuseStep 6600761 = 4950571) B4950571
theorem B8796275 : Blo 1736569 8796275 := bstep (se 1 (by rfl) ⟨6597206, by rfl⟩ : syracuseStep 8796275 = 13194413) B13194413
theorem B144644237 : Blo 1736569 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B24107165 : Blo 1736569 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B2783479 : Blo 1736569 2783479 := bstep (se 1 (by rfl) ⟨2087609, by rfl⟩ : syracuseStep 2783479 = 4175219) B4175219
theorem B11893043 : Blo 1736569 11893043 := bstep (se 1 (by rfl) ⟨8919782, by rfl⟩ : syracuseStep 11893043 = 17839565) B17839565
theorem B3709289 : Blo 1736569 3709289 := bstep (se 2 (by rfl) ⟨1390983, by rfl⟩ : syracuseStep 3709289 = 2781967) B2781967
theorem B5863805 : Blo 1736569 5863805 := bstep (se 3 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 5863805 = 2198927) B2198927
theorem B66804101 : Blo 1736569 66804101 := bstep (se 4 (by rfl) ⟨6262884, by rfl⟩ : syracuseStep 66804101 = 12525769) B12525769
theorem B21141911 : Blo 1736569 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B6265307 : Blo 1736569 6265307 := bstep (se 1 (by rfl) ⟨4698980, by rfl⟩ : syracuseStep 6265307 = 9397961) B9397961
theorem B14842349 : Blo 1736569 14842349 := bstep (se 3 (by rfl) ⟨2782940, by rfl⟩ : syracuseStep 14842349 = 5565881) B5565881
theorem B3299849 : Blo 1736569 3299849 := bstep (se 2 (by rfl) ⟨1237443, by rfl⟩ : syracuseStep 3299849 = 2474887) B2474887
theorem B13187609 : Blo 1736569 13187609 := bstep (se 2 (by rfl) ⟨4945353, by rfl⟩ : syracuseStep 13187609 = 9890707) B9890707
theorem B4946471 : Blo 1736569 4946471 := bstep (se 1 (by rfl) ⟨3709853, by rfl⟩ : syracuseStep 4946471 = 7419707) B7419707
theorem B3299879 : Blo 1736569 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B5864075 : Blo 1736569 5864075 := bstep (se 1 (by rfl) ⟨4398056, by rfl⟩ : syracuseStep 5864075 = 8796113) B8796113
theorem B2931599 : Blo 1736569 2931599 := bstep (se 1 (by rfl) ⟨2198699, by rfl⟩ : syracuseStep 2931599 = 4397399) B4397399
theorem B21429137 : Blo 1736569 21429137 := bstep (se 2 (by rfl) ⟨8035926, by rfl⟩ : syracuseStep 21429137 = 16071853) B16071853
theorem B19790891 : Blo 1736569 19790891 := bstep (se 1 (by rfl) ⟨14843168, by rfl⟩ : syracuseStep 19790891 = 29686337) B29686337
theorem B15858767 : Blo 1736569 15858767 := bstep (se 1 (by rfl) ⟨11894075, by rfl⟩ : syracuseStep 15858767 = 23788151) B23788151
theorem B2931835 : Blo 1736569 2931835 := bstep (se 1 (by rfl) ⟨2198876, by rfl⟩ : syracuseStep 2931835 = 4397753) B4397753
theorem B3300563 : Blo 1736569 3300563 := bstep (se 1 (by rfl) ⟨2475422, by rfl⟩ : syracuseStep 3300563 = 4950845) B4950845
theorem B11132275 : Blo 1736569 11132275 := bstep (se 1 (by rfl) ⟨8349206, by rfl⟩ : syracuseStep 11132275 = 16698413) B16698413
theorem B5864993 : Blo 1736569 5864993 := bstep (se 2 (by rfl) ⟨2199372, by rfl⟩ : syracuseStep 5864993 = 4398745) B4398745
theorem B19799639 : Blo 1736569 19799639 := bstep (se 1 (by rfl) ⟨14849729, by rfl⟩ : syracuseStep 19799639 = 29699459) B29699459
theorem B4947655 : Blo 1736569 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B8797895 : Blo 1736569 8797895 := bstep (se 1 (by rfl) ⟨6598421, by rfl⟩ : syracuseStep 8797895 = 13196843) B13196843
theorem B2973383 : Blo 1736569 2973383 := bstep (se 1 (by rfl) ⟨2230037, by rfl⟩ : syracuseStep 2973383 = 4460075) B4460075
theorem B7044823 : Blo 1736569 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B5865209 : Blo 1736569 5865209 := bstep (se 2 (by rfl) ⟨2199453, by rfl⟩ : syracuseStep 5865209 = 4398907) B4398907
theorem B2604905 : Blo 1736569 2604905 := bstep (se 2 (by rfl) ⟨976839, by rfl⟩ : syracuseStep 2604905 = 1953679) B1953679
theorem B1736571 : Blo 1736569 1736571 := bstep (se 1 (by rfl) ⟨1302428, by rfl⟩ : syracuseStep 1736571 = 2604857) B2604857
theorem B3342223 : Blo 1736569 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B1736623 : Blo 1736569 1736623 := bstep (se 1 (by rfl) ⟨1302467, by rfl⟩ : syracuseStep 1736623 = 2604935) B2604935
theorem B2604983 : Blo 1736569 2604983 := bstep (se 1 (by rfl) ⟨1953737, by rfl⟩ : syracuseStep 2604983 = 3907475) B3907475
theorem B3907511 : Blo 1736569 3907511 := bstep (se 1 (by rfl) ⟨2930633, by rfl⟩ : syracuseStep 3907511 = 5861267) B5861267
theorem B1736647 : Blo 1736569 1736647 := bstep (se 1 (by rfl) ⟨1302485, by rfl⟩ : syracuseStep 1736647 = 2604971) B2604971
theorem B1736667 : Blo 1736569 1736667 := bstep (se 1 (by rfl) ⟨1302500, by rfl⟩ : syracuseStep 1736667 = 2605001) B2605001
theorem B2605019 : Blo 1736569 2605019 := bstep (se 1 (by rfl) ⟨1953764, by rfl⟩ : syracuseStep 2605019 = 3907529) B3907529
theorem B2932699 : Blo 1736569 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B56361041 : Blo 1736569 56361041 := bstep (se 2 (by rfl) ⟨21135390, by rfl⟩ : syracuseStep 56361041 = 42270781) B42270781
theorem B2932841 : Blo 1736569 2932841 := bstep (se 2 (by rfl) ⟨1099815, by rfl⟩ : syracuseStep 2932841 = 2199631) B2199631
theorem B1736991 : Blo 1736569 1736991 := bstep (se 1 (by rfl) ⟨1302743, by rfl⟩ : syracuseStep 1736991 = 2605487) B2605487
theorem B3711305 : Blo 1736569 3711305 := bstep (se 2 (by rfl) ⟨1391739, by rfl⟩ : syracuseStep 3711305 = 2783479) B2783479
theorem B2605403 : Blo 1736569 2605403 := bstep (se 1 (by rfl) ⟨1954052, by rfl⟩ : syracuseStep 2605403 = 3908105) B3908105
theorem B1737051 : Blo 1736569 1737051 := bstep (se 1 (by rfl) ⟨1302788, by rfl⟩ : syracuseStep 1737051 = 2605577) B2605577
theorem B1737071 : Blo 1736569 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B9896357 : Blo 1736569 9896357 := bstep (se 4 (by rfl) ⟨927783, by rfl⟩ : syracuseStep 9896357 = 1855567) B1855567
theorem B1737127 : Blo 1736569 1737127 := bstep (se 1 (by rfl) ⟨1302845, by rfl⟩ : syracuseStep 1737127 = 2605691) B2605691
theorem B3908015 : Blo 1736569 3908015 := bstep (se 1 (by rfl) ⟨2931011, by rfl⟩ : syracuseStep 3908015 = 5862023) B5862023
theorem B4399535 : Blo 1736569 4399535 := bstep (se 1 (by rfl) ⟨3299651, by rfl⟩ : syracuseStep 4399535 = 6599303) B6599303
theorem B4694483 : Blo 1736569 4694483 := bstep (se 1 (by rfl) ⟨3520862, by rfl⟩ : syracuseStep 4694483 = 7041725) B7041725
theorem B3908051 : Blo 1736569 3908051 := bstep (se 1 (by rfl) ⟨2931038, by rfl⟩ : syracuseStep 3908051 = 5862077) B5862077
theorem B1737211 : Blo 1736569 1737211 := bstep (se 1 (by rfl) ⟨1302908, by rfl⟩ : syracuseStep 1737211 = 2605817) B2605817
theorem B3908159 : Blo 1736569 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B2605631 : Blo 1736569 2605631 := bstep (se 1 (by rfl) ⟨1954223, by rfl⟩ : syracuseStep 2605631 = 3908447) B3908447
theorem B1737279 : Blo 1736569 1737279 := bstep (se 1 (by rfl) ⟨1302959, by rfl⟩ : syracuseStep 1737279 = 2605919) B2605919
theorem B1737287 : Blo 1736569 1737287 := bstep (se 1 (by rfl) ⟨1302965, by rfl⟩ : syracuseStep 1737287 = 2605931) B2605931
theorem B16695953 : Blo 1736569 16695953 := bstep (se 2 (by rfl) ⟨6260982, by rfl⟩ : syracuseStep 16695953 = 12521965) B12521965
theorem B8798867 : Blo 1736569 8798867 := bstep (se 1 (by rfl) ⟨6599150, by rfl⟩ : syracuseStep 8798867 = 13198301) B13198301
theorem B3908267 : Blo 1736569 3908267 := bstep (se 1 (by rfl) ⟨2931200, by rfl⟩ : syracuseStep 3908267 = 5862401) B5862401
theorem B2605751 : Blo 1736569 2605751 := bstep (se 1 (by rfl) ⟨1954313, by rfl⟩ : syracuseStep 2605751 = 3908627) B3908627
theorem B1737439 : Blo 1736569 1737439 := bstep (se 1 (by rfl) ⟨1303079, by rfl⟩ : syracuseStep 1737439 = 2606159) B2606159
theorem B1737519 : Blo 1736569 1737519 := bstep (se 1 (by rfl) ⟨1303139, by rfl⟩ : syracuseStep 1737519 = 2606279) B2606279
theorem B7422799 : Blo 1736569 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B5645135 : Blo 1736569 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B7422815 : Blo 1736569 7422815 := bstep (se 1 (by rfl) ⟨5567111, by rfl⟩ : syracuseStep 7422815 = 11134223) B11134223
theorem B2605979 : Blo 1736569 2605979 := bstep (se 1 (by rfl) ⟨1954484, by rfl⟩ : syracuseStep 2605979 = 3908969) B3908969
theorem B1737627 : Blo 1736569 1737627 := bstep (se 1 (by rfl) ⟨1303220, by rfl⟩ : syracuseStep 1737627 = 2606441) B2606441
theorem B31720385 : Blo 1736569 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B1737679 : Blo 1736569 1737679 := bstep (se 1 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 1737679 = 2606519) B2606519
theorem B1737703 : Blo 1736569 1737703 := bstep (se 1 (by rfl) ⟨1303277, by rfl⟩ : syracuseStep 1737703 = 2606555) B2606555
theorem B4695079 : Blo 1736569 4695079 := bstep (se 1 (by rfl) ⟨3521309, by rfl⟩ : syracuseStep 4695079 = 7042619) B7042619
theorem B7423073 : Blo 1736569 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B114320483 : Blo 1736569 114320483 := bstep (se 1 (by rfl) ⟨85740362, by rfl⟩ : syracuseStep 114320483 = 171480725) B171480725
theorem B7423123 : Blo 1736569 7423123 := bstep (se 1 (by rfl) ⟨5567342, by rfl⟩ : syracuseStep 7423123 = 11134685) B11134685
theorem B3908807 : Blo 1736569 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B1738015 : Blo 1736569 1738015 := bstep (se 1 (by rfl) ⟨1303511, by rfl⟩ : syracuseStep 1738015 = 2607023) B2607023
theorem B2606375 : Blo 1736569 2606375 := bstep (se 1 (by rfl) ⟨1954781, by rfl⟩ : syracuseStep 2606375 = 3909563) B3909563
theorem B1738075 : Blo 1736569 1738075 := bstep (se 1 (by rfl) ⟨1303556, by rfl⟩ : syracuseStep 1738075 = 2607113) B2607113
theorem B1738095 : Blo 1736569 1738095 := bstep (se 1 (by rfl) ⟨1303571, by rfl⟩ : syracuseStep 1738095 = 2607143) B2607143
theorem B3908987 : Blo 1736569 3908987 := bstep (se 1 (by rfl) ⟨2931740, by rfl⟩ : syracuseStep 3908987 = 5863481) B5863481
theorem B2606459 : Blo 1736569 2606459 := bstep (se 1 (by rfl) ⟨1954844, by rfl⟩ : syracuseStep 2606459 = 3909689) B3909689
theorem B4400507 : Blo 1736569 4400507 := bstep (se 1 (by rfl) ⟨3300380, by rfl⟩ : syracuseStep 4400507 = 6600761) B6600761
theorem B4949387 : Blo 1736569 4949387 := bstep (se 1 (by rfl) ⟨3712040, by rfl⟩ : syracuseStep 4949387 = 7424081) B7424081
theorem B1738151 : Blo 1736569 1738151 := bstep (se 1 (by rfl) ⟨1303613, by rfl⟩ : syracuseStep 1738151 = 2607227) B2607227
theorem B96429491 : Blo 1736569 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B8799677 : Blo 1736569 8799677 := bstep (se 3 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 8799677 = 3299879) B3299879
theorem B3909113 : Blo 1736569 3909113 := bstep (se 2 (by rfl) ⟨1465917, by rfl⟩ : syracuseStep 3909113 = 2931835) B2931835
theorem B2606585 : Blo 1736569 2606585 := bstep (se 2 (by rfl) ⟨977469, by rfl⟩ : syracuseStep 2606585 = 1954939) B1954939
theorem B1738235 : Blo 1736569 1738235 := bstep (se 1 (by rfl) ⟨1303676, by rfl⟩ : syracuseStep 1738235 = 2607353) B2607353
theorem B5563961 : Blo 1736569 5563961 := bstep (se 2 (by rfl) ⟨2086485, by rfl⟩ : syracuseStep 5563961 = 4172971) B4172971
theorem B1738303 : Blo 1736569 1738303 := bstep (se 1 (by rfl) ⟨1303727, by rfl⟩ : syracuseStep 1738303 = 2607455) B2607455
theorem B1738311 : Blo 1736569 1738311 := bstep (se 1 (by rfl) ⟨1303733, by rfl⟩ : syracuseStep 1738311 = 2607467) B2607467
theorem B3909203 : Blo 1736569 3909203 := bstep (se 1 (by rfl) ⟨2931902, by rfl⟩ : syracuseStep 3909203 = 5863805) B5863805
theorem B9389657 : Blo 1736569 9389657 := bstep (se 2 (by rfl) ⟨3521121, by rfl⟩ : syracuseStep 9389657 = 7042243) B7042243
theorem B2606687 : Blo 1736569 2606687 := bstep (se 1 (by rfl) ⟨1955015, by rfl⟩ : syracuseStep 2606687 = 3910031) B3910031
theorem B8791739 : Blo 1736569 8791739 := bstep (se 1 (by rfl) ⟨6593804, by rfl⟩ : syracuseStep 8791739 = 13187609) B13187609
theorem B1738463 : Blo 1736569 1738463 := bstep (se 1 (by rfl) ⟨1303847, by rfl⟩ : syracuseStep 1738463 = 2607695) B2607695
theorem B3909383 : Blo 1736569 3909383 := bstep (se 1 (by rfl) ⟨2932037, by rfl⟩ : syracuseStep 3909383 = 5864075) B5864075
theorem B1738543 : Blo 1736569 1738543 := bstep (se 1 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 1738543 = 2607815) B2607815
theorem B2606903 : Blo 1736569 2606903 := bstep (se 1 (by rfl) ⟨1955177, by rfl⟩ : syracuseStep 2606903 = 3910355) B3910355
theorem B5867369 : Blo 1736569 5867369 := bstep (se 2 (by rfl) ⟨2200263, by rfl⟩ : syracuseStep 5867369 = 4400527) B4400527
theorem B2607209 : Blo 1736569 2607209 := bstep (se 2 (by rfl) ⟨977703, by rfl⟩ : syracuseStep 2607209 = 1955407) B1955407
theorem B16697609 : Blo 1736569 16697609 := bstep (se 2 (by rfl) ⟨6261603, by rfl⟩ : syracuseStep 16697609 = 12523207) B12523207
theorem B6596873 : Blo 1736569 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B7047433 : Blo 1736569 7047433 := bstep (se 2 (by rfl) ⟨2642787, by rfl⟩ : syracuseStep 7047433 = 5285575) B5285575
theorem B3909995 : Blo 1736569 3909995 := bstep (se 1 (by rfl) ⟨2932496, by rfl⟩ : syracuseStep 3909995 = 5864993) B5864993
theorem B13199759 : Blo 1736569 13199759 := bstep (se 1 (by rfl) ⟨9899819, by rfl⟩ : syracuseStep 13199759 = 19799639) B19799639
theorem B2607527 : Blo 1736569 2607527 := bstep (se 1 (by rfl) ⟨1955645, by rfl⟩ : syracuseStep 2607527 = 3911291) B3911291
theorem B2198011 : Blo 1736569 2198011 := bstep (se 1 (by rfl) ⟨1648508, by rfl⟩ : syracuseStep 2198011 = 3297017) B3297017
theorem B3910139 : Blo 1736569 3910139 := bstep (se 1 (by rfl) ⟨2932604, by rfl⟩ : syracuseStep 3910139 = 5865209) B5865209
theorem B2607611 : Blo 1736569 2607611 := bstep (se 1 (by rfl) ⟨1955708, by rfl⟩ : syracuseStep 2607611 = 3911417) B3911417
theorem B3910265 : Blo 1736569 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B2607737 : Blo 1736569 2607737 := bstep (se 2 (by rfl) ⟨977901, by rfl⟩ : syracuseStep 2607737 = 1955803) B1955803
theorem B3910319 : Blo 1736569 3910319 := bstep (se 1 (by rfl) ⟨2932739, by rfl⟩ : syracuseStep 3910319 = 5865479) B5865479
theorem B2607791 : Blo 1736569 2607791 := bstep (se 1 (by rfl) ⟨1955843, by rfl⟩ : syracuseStep 2607791 = 3911687) B3911687
theorem B8030915 : Blo 1736569 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B9890525 : Blo 1736569 9890525 := bstep (se 3 (by rfl) ⟨1854473, by rfl⟩ : syracuseStep 9890525 = 3708947) B3708947
theorem B2607839 : Blo 1736569 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B3910391 : Blo 1736569 3910391 := bstep (se 1 (by rfl) ⟨2932793, by rfl⟩ : syracuseStep 3910391 = 5865587) B5865587
theorem B3910571 : Blo 1736569 3910571 := bstep (se 1 (by rfl) ⟨2932928, by rfl⟩ : syracuseStep 3910571 = 5865857) B5865857
theorem B9391559 : Blo 1736569 9391559 := bstep (se 1 (by rfl) ⟨7043669, by rfl⟩ : syracuseStep 9391559 = 14087339) B14087339
theorem B2198983 : Blo 1736569 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B3911111 : Blo 1736569 3911111 := bstep (se 1 (by rfl) ⟨2933333, by rfl⟩ : syracuseStep 3911111 = 5866667) B5866667
theorem B8793683 : Blo 1736569 8793683 := bstep (se 1 (by rfl) ⟨6595262, by rfl⟩ : syracuseStep 8793683 = 13190525) B13190525
theorem B445525589 : Blo 1736569 445525589 := bstep (se 8 (by rfl) ⟨2610501, by rfl⟩ : syracuseStep 445525589 = 5221003) B5221003
theorem B5942879 : Blo 1736569 5942879 := bstep (se 1 (by rfl) ⟨4457159, by rfl⟩ : syracuseStep 5942879 = 8914319) B8914319
theorem B9899729 : Blo 1736569 9899729 := bstep (se 2 (by rfl) ⟨3712398, by rfl⟩ : syracuseStep 9899729 = 7424797) B7424797
theorem B3911471 : Blo 1736569 3911471 := bstep (se 1 (by rfl) ⟨2933603, by rfl⟩ : syracuseStep 3911471 = 5867207) B5867207
theorem B6598529 : Blo 1736569 6598529 := bstep (se 2 (by rfl) ⟨2474448, by rfl⟩ : syracuseStep 6598529 = 4948897) B4948897
theorem B7417757 : Blo 1736569 7417757 := bstep (se 3 (by rfl) ⟨1390829, by rfl⟩ : syracuseStep 7417757 = 2781659) B2781659
theorem B16707485 : Blo 1736569 16707485 := bstep (se 3 (by rfl) ⟨3132653, by rfl⟩ : syracuseStep 16707485 = 6265307) B6265307
theorem B18796445 : Blo 1736569 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B44536067 : Blo 1736569 44536067 := bstep (se 1 (by rfl) ⟨33402050, by rfl⟩ : syracuseStep 44536067 = 66804101) B66804101
theorem B14094607 : Blo 1736569 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B2199899 : Blo 1736569 2199899 := bstep (se 1 (by rfl) ⟨1649924, by rfl⟩ : syracuseStep 2199899 = 3299849) B3299849
theorem B3297647 : Blo 1736569 3297647 := bstep (se 1 (by rfl) ⟨2473235, by rfl⟩ : syracuseStep 3297647 = 4946471) B4946471
theorem B5861807 : Blo 1736569 5861807 := bstep (se 1 (by rfl) ⟨4396355, by rfl⟩ : syracuseStep 5861807 = 8792711) B8792711
theorem B3174985 : Blo 1736569 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B1954399 : Blo 1736569 1954399 := bstep (se 1 (by rfl) ⟨1465799, by rfl⟩ : syracuseStep 1954399 = 2931599) B2931599
theorem B13193927 : Blo 1736569 13193927 := bstep (se 1 (by rfl) ⟨9895445, by rfl⟩ : syracuseStep 13193927 = 19790891) B19790891
theorem B10572511 : Blo 1736569 10572511 := bstep (se 1 (by rfl) ⟨7929383, by rfl⟩ : syracuseStep 10572511 = 15858767) B15858767
theorem B54203165 : Blo 1736569 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B2200375 : Blo 1736569 2200375 := bstep (se 1 (by rfl) ⟨1650281, by rfl⟩ : syracuseStep 2200375 = 3300563) B3300563
theorem B2782031 : Blo 1736569 2782031 := bstep (se 1 (by rfl) ⟨2086523, by rfl⟩ : syracuseStep 2782031 = 4173047) B4173047
theorem B9393097 : Blo 1736569 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B57144365 : Blo 1736569 57144365 := bstep (se 3 (by rfl) ⟨10714568, by rfl⟩ : syracuseStep 57144365 = 21429137) B21429137
theorem B7419023 : Blo 1736569 7419023 := bstep (se 1 (by rfl) ⟨5564267, by rfl⟩ : syracuseStep 7419023 = 11128535) B11128535
theorem B4396265 : Blo 1736569 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B2782441 : Blo 1736569 2782441 := bstep (se 2 (by rfl) ⟨1043415, by rfl⟩ : syracuseStep 2782441 = 2086831) B2086831
theorem B3298657 : Blo 1736569 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B5862779 : Blo 1736569 5862779 := bstep (se 1 (by rfl) ⟨4397084, by rfl⟩ : syracuseStep 5862779 = 8794169) B8794169
theorem B4396427 : Blo 1736569 4396427 := bstep (se 1 (by rfl) ⟨3297320, by rfl⟩ : syracuseStep 4396427 = 6594641) B6594641
theorem B4396639 : Blo 1736569 4396639 := bstep (se 1 (by rfl) ⟨3297479, by rfl⟩ : syracuseStep 4396639 = 6594959) B6594959
theorem B1955551 : Blo 1736569 1955551 := bstep (se 1 (by rfl) ⟨1466663, by rfl⟩ : syracuseStep 1955551 = 2933327) B2933327
theorem B9394157 : Blo 1736569 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B8345729 : Blo 1736569 8345729 := bstep (se 2 (by rfl) ⟨3129648, by rfl⟩ : syracuseStep 8345729 = 6259297) B6259297
theorem B19306631 : Blo 1736569 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B4397267 : Blo 1736569 4397267 := bstep (se 1 (by rfl) ⟨3297950, by rfl⟩ : syracuseStep 4397267 = 6595901) B6595901
theorem B10566071 : Blo 1736569 10566071 := bstep (se 1 (by rfl) ⟨7924553, by rfl⟩ : syracuseStep 10566071 = 15849107) B15849107
theorem B25385399 : Blo 1736569 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B8796599 : Blo 1736569 8796599 := bstep (se 1 (by rfl) ⟨6597449, by rfl⟩ : syracuseStep 8796599 = 13194899) B13194899
theorem B15850009 : Blo 1736569 15850009 := bstep (se 2 (by rfl) ⟨5943753, by rfl⟩ : syracuseStep 15850009 = 11887507) B11887507
theorem B13367915 : Blo 1736569 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B10566283 : Blo 1736569 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B2931383 : Blo 1736569 2931383 := bstep (se 1 (by rfl) ⟨2198537, by rfl⟩ : syracuseStep 2931383 = 4397075) B4397075
theorem B28170989 : Blo 1736569 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B5864183 : Blo 1736569 5864183 := bstep (se 1 (by rfl) ⟨4398137, by rfl⟩ : syracuseStep 5864183 = 8796275) B8796275
theorem B16071443 : Blo 1736569 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B3300115 : Blo 1736569 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B7928695 : Blo 1736569 7928695 := bstep (se 1 (by rfl) ⟨5946521, by rfl⟩ : syracuseStep 7928695 = 11893043) B11893043
theorem B2472859 : Blo 1736569 2472859 := bstep (se 1 (by rfl) ⟨1854644, by rfl⟩ : syracuseStep 2472859 = 3709289) B3709289
theorem B9894899 : Blo 1736569 9894899 := bstep (se 1 (by rfl) ⟨7421174, by rfl⟩ : syracuseStep 9894899 = 14842349) B14842349
theorem B14843033 : Blo 1736569 14843033 := bstep (se 2 (by rfl) ⟨5566137, by rfl⟩ : syracuseStep 14843033 = 11132275) B11132275
theorem B8920439 : Blo 1736569 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B9395585 : Blo 1736569 9395585 := bstep (se 2 (by rfl) ⟨3523344, by rfl⟩ : syracuseStep 9395585 = 7046689) B7046689
theorem B2932105 : Blo 1736569 2932105 := bstep (se 2 (by rfl) ⟨1099539, by rfl⟩ : syracuseStep 2932105 = 2199079) B2199079
theorem B25050617 : Blo 1736569 25050617 := bstep (se 2 (by rfl) ⟨9393981, by rfl⟩ : syracuseStep 25050617 = 18787963) B18787963
theorem B85679639 : Blo 1736569 85679639 := bstep (se 1 (by rfl) ⟨64259729, by rfl⟩ : syracuseStep 85679639 = 128519459) B128519459
theorem B5865263 : Blo 1736569 5865263 := bstep (se 1 (by rfl) ⟨4398947, by rfl⟩ : syracuseStep 5865263 = 8797895) B8797895
theorem B1982255 : Blo 1736569 1982255 := bstep (se 1 (by rfl) ⟨1486691, by rfl⟩ : syracuseStep 1982255 = 2973383) B2973383
theorem B3907385 : Blo 1736569 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B2932537 : Blo 1736569 2932537 := bstep (se 2 (by rfl) ⟨1099701, by rfl⟩ : syracuseStep 2932537 = 2199403) B2199403
theorem B4456297 : Blo 1736569 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B1736603 : Blo 1736569 1736603 := bstep (se 1 (by rfl) ⟨1302452, by rfl⟩ : syracuseStep 1736603 = 2604905) B2604905
theorem B1736655 : Blo 1736569 1736655 := bstep (se 1 (by rfl) ⟨1302491, by rfl⟩ : syracuseStep 1736655 = 2604983) B2604983
theorem B2605007 : Blo 1736569 2605007 := bstep (se 1 (by rfl) ⟨1953755, by rfl⟩ : syracuseStep 2605007 = 3907511) B3907511
theorem B1736679 : Blo 1736569 1736679 := bstep (se 1 (by rfl) ⟨1302509, by rfl⟩ : syracuseStep 1736679 = 2605019) B2605019
theorem B84533381 : Blo 1736569 84533381 := bstep (se 4 (by rfl) ⟨7925004, by rfl⟩ : syracuseStep 84533381 = 15850009) B15850009
theorem B1736935 : Blo 1736569 1736935 := bstep (se 1 (by rfl) ⟨1302701, by rfl⟩ : syracuseStep 1736935 = 2605403) B2605403
theorem B3907871 : Blo 1736569 3907871 := bstep (se 1 (by rfl) ⟨2930903, by rfl⟩ : syracuseStep 3907871 = 5861807) B5861807
theorem B2605343 : Blo 1736569 2605343 := bstep (se 1 (by rfl) ⟨1954007, by rfl⟩ : syracuseStep 2605343 = 3908015) B3908015
theorem B2933023 : Blo 1736569 2933023 := bstep (se 1 (by rfl) ⟨2199767, by rfl⟩ : syracuseStep 2933023 = 4399535) B4399535
theorem B2605367 : Blo 1736569 2605367 := bstep (se 1 (by rfl) ⟨1954025, by rfl⟩ : syracuseStep 2605367 = 3908051) B3908051
theorem B9396577 : Blo 1736569 9396577 := bstep (se 2 (by rfl) ⟨3523716, by rfl⟩ : syracuseStep 9396577 = 7047433) B7047433
theorem B18792809 : Blo 1736569 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B2605439 : Blo 1736569 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B1737087 : Blo 1736569 1737087 := bstep (se 1 (by rfl) ⟨1302815, by rfl⟩ : syracuseStep 1737087 = 2605631) B2605631
theorem B5865911 : Blo 1736569 5865911 := bstep (se 1 (by rfl) ⟨4399433, by rfl⟩ : syracuseStep 5865911 = 8798867) B8798867
theorem B2605511 : Blo 1736569 2605511 := bstep (se 1 (by rfl) ⟨1954133, by rfl⟩ : syracuseStep 2605511 = 3908267) B3908267
theorem B1737167 : Blo 1736569 1737167 := bstep (se 1 (by rfl) ⟨1302875, by rfl⟩ : syracuseStep 1737167 = 2605751) B2605751
theorem B21144053 : Blo 1736569 21144053 := bstep (se 5 (by rfl) ⟨991127, by rfl⟩ : syracuseStep 21144053 = 1982255) B1982255
theorem B36135443 : Blo 1736569 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B4948543 : Blo 1736569 4948543 := bstep (se 1 (by rfl) ⟨3711407, by rfl⟩ : syracuseStep 4948543 = 7422815) B7422815
theorem B1737319 : Blo 1736569 1737319 := bstep (se 1 (by rfl) ⟨1302989, by rfl⟩ : syracuseStep 1737319 = 2605979) B2605979
theorem B4948715 : Blo 1736569 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B2605865 : Blo 1736569 2605865 := bstep (se 2 (by rfl) ⟨977199, by rfl⟩ : syracuseStep 2605865 = 1954399) B1954399
theorem B2605871 : Blo 1736569 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B9896813 : Blo 1736569 9896813 := bstep (se 3 (by rfl) ⟨1855652, by rfl⟩ : syracuseStep 9896813 = 3711305) B3711305
theorem B1737583 : Blo 1736569 1737583 := bstep (se 1 (by rfl) ⟨1303187, by rfl⟩ : syracuseStep 1737583 = 2606375) B2606375
theorem B5866397 : Blo 1736569 5866397 := bstep (se 3 (by rfl) ⟨1099949, by rfl⟩ : syracuseStep 5866397 = 2199899) B2199899
theorem B3908519 : Blo 1736569 3908519 := bstep (se 1 (by rfl) ⟨2931389, by rfl⟩ : syracuseStep 3908519 = 5862779) B5862779
theorem B2605991 : Blo 1736569 2605991 := bstep (se 1 (by rfl) ⟨1954493, by rfl⟩ : syracuseStep 2605991 = 3908987) B3908987
theorem B1737639 : Blo 1736569 1737639 := bstep (se 1 (by rfl) ⟨1303229, by rfl⟩ : syracuseStep 1737639 = 2606459) B2606459
theorem B2933671 : Blo 1736569 2933671 := bstep (se 1 (by rfl) ⟨2200253, by rfl⟩ : syracuseStep 2933671 = 4400507) B4400507
theorem B5866451 : Blo 1736569 5866451 := bstep (se 1 (by rfl) ⟨4399838, by rfl⟩ : syracuseStep 5866451 = 8799677) B8799677
theorem B2606075 : Blo 1736569 2606075 := bstep (se 1 (by rfl) ⟨1954556, by rfl⟩ : syracuseStep 2606075 = 3909113) B3909113
theorem B1737723 : Blo 1736569 1737723 := bstep (se 1 (by rfl) ⟨1303292, by rfl⟩ : syracuseStep 1737723 = 2606585) B2606585
theorem B4400153 : Blo 1736569 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B2606135 : Blo 1736569 2606135 := bstep (se 1 (by rfl) ⟨1954601, by rfl⟩ : syracuseStep 2606135 = 3909203) B3909203
theorem B6259771 : Blo 1736569 6259771 := bstep (se 1 (by rfl) ⟨4694828, by rfl⟩ : syracuseStep 6259771 = 9389657) B9389657
theorem B1737791 : Blo 1736569 1737791 := bstep (se 1 (by rfl) ⟨1303343, by rfl⟩ : syracuseStep 1737791 = 2606687) B2606687
theorem B2933833 : Blo 1736569 2933833 := bstep (se 2 (by rfl) ⟨1100187, by rfl⟩ : syracuseStep 2933833 = 2200375) B2200375
theorem B9897065 : Blo 1736569 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B2606255 : Blo 1736569 2606255 := bstep (se 1 (by rfl) ⟨1954691, by rfl⟩ : syracuseStep 2606255 = 3909383) B3909383
theorem B25044157 : Blo 1736569 25044157 := bstep (se 3 (by rfl) ⟨4695779, by rfl⟩ : syracuseStep 25044157 = 9391559) B9391559
theorem B1737935 : Blo 1736569 1737935 := bstep (se 1 (by rfl) ⟨1303451, by rfl⟩ : syracuseStep 1737935 = 2606903) B2606903
theorem B12518621 : Blo 1736569 12518621 := bstep (se 3 (by rfl) ⟨2347241, by rfl⟩ : syracuseStep 12518621 = 4694483) B4694483
theorem B6260105 : Blo 1736569 6260105 := bstep (se 2 (by rfl) ⟨2347539, by rfl⟩ : syracuseStep 6260105 = 4695079) B4695079
theorem B1738139 : Blo 1736569 1738139 := bstep (se 1 (by rfl) ⟨1303604, by rfl⟩ : syracuseStep 1738139 = 2607209) B2607209
theorem B5563819 : Blo 1736569 5563819 := bstep (se 1 (by rfl) ⟨4172864, by rfl⟩ : syracuseStep 5563819 = 8345729) B8345729
theorem B9897497 : Blo 1736569 9897497 := bstep (se 2 (by rfl) ⟨3711561, by rfl⟩ : syracuseStep 9897497 = 7423123) B7423123
theorem B2606663 : Blo 1736569 2606663 := bstep (se 1 (by rfl) ⟨1954997, by rfl⟩ : syracuseStep 2606663 = 3909995) B3909995
theorem B8799839 : Blo 1736569 8799839 := bstep (se 1 (by rfl) ⟨6599879, by rfl⟩ : syracuseStep 8799839 = 13199759) B13199759
theorem B1738351 : Blo 1736569 1738351 := bstep (se 1 (by rfl) ⟨1303763, by rfl⟩ : syracuseStep 1738351 = 2607527) B2607527
theorem B2606759 : Blo 1736569 2606759 := bstep (se 1 (by rfl) ⟨1955069, by rfl⟩ : syracuseStep 2606759 = 3910139) B3910139
theorem B1738407 : Blo 1736569 1738407 := bstep (se 1 (by rfl) ⟨1303805, by rfl⟩ : syracuseStep 1738407 = 2607611) B2607611
theorem B2606843 : Blo 1736569 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B1738491 : Blo 1736569 1738491 := bstep (se 1 (by rfl) ⟨1303868, by rfl⟩ : syracuseStep 1738491 = 2607737) B2607737
theorem B2606879 : Blo 1736569 2606879 := bstep (se 1 (by rfl) ⟨1955159, by rfl⟩ : syracuseStep 2606879 = 3910319) B3910319
theorem B1738527 : Blo 1736569 1738527 := bstep (se 1 (by rfl) ⟨1303895, by rfl⟩ : syracuseStep 1738527 = 2607791) B2607791
theorem B1738559 : Blo 1736569 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B3909455 : Blo 1736569 3909455 := bstep (se 1 (by rfl) ⟨2932091, by rfl⟩ : syracuseStep 3909455 = 5864183) B5864183
theorem B2606927 : Blo 1736569 2606927 := bstep (se 1 (by rfl) ⟨1955195, by rfl⟩ : syracuseStep 2606927 = 3910391) B3910391
theorem B3909473 : Blo 1736569 3909473 := bstep (se 2 (by rfl) ⟨1466052, by rfl⟩ : syracuseStep 3909473 = 2932105) B2932105
theorem B2607047 : Blo 1736569 2607047 := bstep (se 1 (by rfl) ⟨1955285, by rfl⟩ : syracuseStep 2607047 = 3910571) B3910571
theorem B6596599 : Blo 1736569 6596599 := bstep (se 1 (by rfl) ⟨4947449, by rfl⟩ : syracuseStep 6596599 = 9894899) B9894899
theorem B2607401 : Blo 1736569 2607401 := bstep (se 2 (by rfl) ⟨977775, by rfl⟩ : syracuseStep 2607401 = 1955551) B1955551
theorem B2607407 : Blo 1736569 2607407 := bstep (se 1 (by rfl) ⟨1955555, by rfl⟩ : syracuseStep 2607407 = 3911111) B3911111
theorem B3910049 : Blo 1736569 3910049 := bstep (se 2 (by rfl) ⟨1466268, by rfl⟩ : syracuseStep 3910049 = 2932537) B2932537
theorem B5941729 : Blo 1736569 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B3910175 : Blo 1736569 3910175 := bstep (se 1 (by rfl) ⟨2932631, by rfl⟩ : syracuseStep 3910175 = 5865263) B5865263
theorem B2607647 : Blo 1736569 2607647 := bstep (se 1 (by rfl) ⟨1955735, by rfl⟩ : syracuseStep 2607647 = 3911471) B3911471
theorem B29690711 : Blo 1736569 29690711 := bstep (se 1 (by rfl) ⟨22268033, by rfl⟩ : syracuseStep 29690711 = 44536067) B44536067
theorem B2198431 : Blo 1736569 2198431 := bstep (se 1 (by rfl) ⟨1648823, by rfl⟩ : syracuseStep 2198431 = 3297647) B3297647
theorem B6597571 : Blo 1736569 6597571 := bstep (se 1 (by rfl) ⟨4948178, by rfl⟩ : syracuseStep 6597571 = 9896357) B9896357
theorem B3763423 : Blo 1736569 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B21146923 : Blo 1736569 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B38096243 : Blo 1736569 38096243 := bstep (se 1 (by rfl) ⟨28572182, by rfl⟩ : syracuseStep 38096243 = 57144365) B57144365
theorem B76213655 : Blo 1736569 76213655 := bstep (se 1 (by rfl) ⟨57160241, by rfl⟩ : syracuseStep 76213655 = 114320483) B114320483
theorem B64286327 : Blo 1736569 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B5861159 : Blo 1736569 5861159 := bstep (se 1 (by rfl) ⟨4395869, by rfl⟩ : syracuseStep 5861159 = 8791739) B8791739
theorem B10571593 : Blo 1736569 10571593 := bstep (se 2 (by rfl) ⟨3964347, by rfl⟩ : syracuseStep 10571593 = 7928695) B7928695
theorem B14839685 : Blo 1736569 14839685 := bstep (se 4 (by rfl) ⟨1391220, by rfl⟩ : syracuseStep 14839685 = 2782441) B2782441
theorem B3911579 : Blo 1736569 3911579 := bstep (se 1 (by rfl) ⟨2933684, by rfl⟩ : syracuseStep 3911579 = 5867369) B5867369
theorem B6262771 : Blo 1736569 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B1954255 : Blo 1736569 1954255 := bstep (se 1 (by rfl) ⟨1465691, by rfl⟩ : syracuseStep 1954255 = 2931383) B2931383
theorem B5353943 : Blo 1736569 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B18780659 : Blo 1736569 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B5862185 : Blo 1736569 5862185 := bstep (se 2 (by rfl) ⟨2198319, by rfl⟩ : syracuseStep 5862185 = 4396639) B4396639
theorem B7418749 : Blo 1736569 7418749 := bstep (se 3 (by rfl) ⟨1391015, by rfl⟩ : syracuseStep 7418749 = 2782031) B2782031
theorem B6263723 : Blo 1736569 6263723 := bstep (se 1 (by rfl) ⟨4697792, by rfl⟩ : syracuseStep 6263723 = 9395585) B9395585
theorem B16700411 : Blo 1736569 16700411 := bstep (se 1 (by rfl) ⟨12525308, by rfl⟩ : syracuseStep 16700411 = 25050617) B25050617
theorem B57119759 : Blo 1736569 57119759 := bstep (se 1 (by rfl) ⟨42839819, by rfl⟩ : syracuseStep 57119759 = 85679639) B85679639
theorem B5862455 : Blo 1736569 5862455 := bstep (se 1 (by rfl) ⟨4396841, by rfl⟩ : syracuseStep 5862455 = 8793683) B8793683
theorem B3961919 : Blo 1736569 3961919 := bstep (se 1 (by rfl) ⟨2971439, by rfl⟩ : syracuseStep 3961919 = 5942879) B5942879
theorem B19780685 : Blo 1736569 19780685 := bstep (se 3 (by rfl) ⟨3708878, by rfl⟩ : syracuseStep 19780685 = 7417757) B7417757
theorem B6599819 : Blo 1736569 6599819 := bstep (se 1 (by rfl) ⟨4949864, by rfl⟩ : syracuseStep 6599819 = 9899729) B9899729
theorem B11138323 : Blo 1736569 11138323 := bstep (se 1 (by rfl) ⟨8353742, by rfl⟩ : syracuseStep 11138323 = 16707485) B16707485
theorem B12530963 : Blo 1736569 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B37574027 : Blo 1736569 37574027 := bstep (se 1 (by rfl) ⟨28180520, by rfl⟩ : syracuseStep 37574027 = 56361041) B56361041
theorem B1955227 : Blo 1736569 1955227 := bstep (se 1 (by rfl) ⟨1466420, by rfl⟩ : syracuseStep 1955227 = 2932841) B2932841
theorem B51484349 : Blo 1736569 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B11130635 : Blo 1736569 11130635 := bstep (se 1 (by rfl) ⟨8347976, by rfl⟩ : syracuseStep 11130635 = 16695953) B16695953
theorem B8795951 : Blo 1736569 8795951 := bstep (se 1 (by rfl) ⟨6596963, by rfl⟩ : syracuseStep 8795951 = 13193927) B13193927
theorem B2930681 : Blo 1736569 2930681 := bstep (se 2 (by rfl) ⟨1099005, by rfl⟩ : syracuseStep 2930681 = 2198011) B2198011
theorem B4946015 : Blo 1736569 4946015 := bstep (se 1 (by rfl) ⟨3709511, by rfl⟩ : syracuseStep 4946015 = 7419023) B7419023
theorem B4233313 : Blo 1736569 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B2930843 : Blo 1736569 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B14088377 : Blo 1736569 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B2930951 : Blo 1736569 2930951 := bstep (se 1 (by rfl) ⟨2198213, by rfl⟩ : syracuseStep 2930951 = 4396427) B4396427
theorem B3299591 : Blo 1736569 3299591 := bstep (se 1 (by rfl) ⟨2474693, by rfl⟩ : syracuseStep 3299591 = 4949387) B4949387
theorem B14096681 : Blo 1736569 14096681 := bstep (se 2 (by rfl) ⟨5286255, by rfl⟩ : syracuseStep 14096681 = 10572511) B10572511
theorem B3709307 : Blo 1736569 3709307 := bstep (se 1 (by rfl) ⟨2781980, by rfl⟩ : syracuseStep 3709307 = 5563961) B5563961
theorem B12524129 : Blo 1736569 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B2931511 : Blo 1736569 2931511 := bstep (se 1 (by rfl) ⟨2198633, by rfl⟩ : syracuseStep 2931511 = 4397267) B4397267
theorem B11131739 : Blo 1736569 11131739 := bstep (se 1 (by rfl) ⟨8348804, by rfl⟩ : syracuseStep 11131739 = 16697609) B16697609
theorem B4397915 : Blo 1736569 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B16923599 : Blo 1736569 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B7044047 : Blo 1736569 7044047 := bstep (se 1 (by rfl) ⟨5283035, by rfl⟩ : syracuseStep 7044047 = 10566071) B10566071
theorem B5864399 : Blo 1736569 5864399 := bstep (se 1 (by rfl) ⟨4398299, by rfl⟩ : syracuseStep 5864399 = 8796599) B8796599
theorem B8911943 : Blo 1736569 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B4398209 : Blo 1736569 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B6593683 : Blo 1736569 6593683 := bstep (se 1 (by rfl) ⟨4945262, by rfl⟩ : syracuseStep 6593683 = 9890525) B9890525
theorem B10714295 : Blo 1736569 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B2931977 : Blo 1736569 2931977 := bstep (se 2 (by rfl) ⟨1099491, by rfl⟩ : syracuseStep 2931977 = 2198983) B2198983
theorem B9895355 : Blo 1736569 9895355 := bstep (se 1 (by rfl) ⟨7421516, by rfl⟩ : syracuseStep 9895355 = 14843033) B14843033
theorem B13188581 : Blo 1736569 13188581 := bstep (se 4 (by rfl) ⟨1236429, by rfl⟩ : syracuseStep 13188581 = 2472859) B2472859
theorem B5946959 : Blo 1736569 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B297017059 : Blo 1736569 297017059 := bstep (se 1 (by rfl) ⟨222762794, by rfl⟩ : syracuseStep 297017059 = 445525589) B445525589
theorem B2604923 : Blo 1736569 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B4399019 : Blo 1736569 4399019 := bstep (se 1 (by rfl) ⟨3299264, by rfl⟩ : syracuseStep 4399019 = 6598529) B6598529
theorem B1736671 : Blo 1736569 1736671 := bstep (se 1 (by rfl) ⟨1302503, by rfl⟩ : syracuseStep 1736671 = 2605007) B2605007
theorem B5644417 : Blo 1736569 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B2605247 : Blo 1736569 2605247 := bstep (se 1 (by rfl) ⟨1953935, by rfl⟩ : syracuseStep 2605247 = 3907871) B3907871
theorem B1736895 : Blo 1736569 1736895 := bstep (se 1 (by rfl) ⟨1302671, by rfl⟩ : syracuseStep 1736895 = 2605343) B2605343
theorem B1736911 : Blo 1736569 1736911 := bstep (se 1 (by rfl) ⟨1302683, by rfl⟩ : syracuseStep 1736911 = 2605367) B2605367
theorem B1736959 : Blo 1736569 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B1737007 : Blo 1736569 1737007 := bstep (se 1 (by rfl) ⟨1302755, by rfl⟩ : syracuseStep 1737007 = 2605511) B2605511
theorem B37569005 : Blo 1736569 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B3908123 : Blo 1736569 3908123 := bstep (se 1 (by rfl) ⟨2931092, by rfl⟩ : syracuseStep 3908123 = 5862185) B5862185
theorem B1737243 : Blo 1736569 1737243 := bstep (se 1 (by rfl) ⟨1302932, by rfl⟩ : syracuseStep 1737243 = 2605865) B2605865
theorem B1737247 : Blo 1736569 1737247 := bstep (se 1 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 1737247 = 2605871) B2605871
theorem B2605673 : Blo 1736569 2605673 := bstep (se 2 (by rfl) ⟨977127, by rfl⟩ : syracuseStep 2605673 = 1954255) B1954255
theorem B2605679 : Blo 1736569 2605679 := bstep (se 1 (by rfl) ⟨1954259, by rfl⟩ : syracuseStep 2605679 = 3908519) B3908519
theorem B1737327 : Blo 1736569 1737327 := bstep (se 1 (by rfl) ⟨1302995, by rfl⟩ : syracuseStep 1737327 = 2605991) B2605991
theorem B7922305 : Blo 1736569 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B1737383 : Blo 1736569 1737383 := bstep (se 1 (by rfl) ⟨1303037, by rfl⟩ : syracuseStep 1737383 = 2606075) B2606075
theorem B11133607 : Blo 1736569 11133607 := bstep (se 1 (by rfl) ⟨8350205, by rfl⟩ : syracuseStep 11133607 = 16700411) B16700411
theorem B2933435 : Blo 1736569 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B3908303 : Blo 1736569 3908303 := bstep (se 1 (by rfl) ⟨2931227, by rfl⟩ : syracuseStep 3908303 = 5862455) B5862455
theorem B1737423 : Blo 1736569 1737423 := bstep (se 1 (by rfl) ⟨1303067, by rfl⟩ : syracuseStep 1737423 = 2606135) B2606135
theorem B4399879 : Blo 1736569 4399879 := bstep (se 1 (by rfl) ⟨3299909, by rfl⟩ : syracuseStep 4399879 = 6599819) B6599819
theorem B1737503 : Blo 1736569 1737503 := bstep (se 1 (by rfl) ⟨1303127, by rfl⟩ : syracuseStep 1737503 = 2606255) B2606255
theorem B1737775 : Blo 1736569 1737775 := bstep (se 1 (by rfl) ⟨1303331, by rfl⟩ : syracuseStep 1737775 = 2606663) B2606663
theorem B5866559 : Blo 1736569 5866559 := bstep (se 1 (by rfl) ⟨4399919, by rfl⟩ : syracuseStep 5866559 = 8799839) B8799839
theorem B3908681 : Blo 1736569 3908681 := bstep (se 2 (by rfl) ⟨1465755, by rfl⟩ : syracuseStep 3908681 = 2931511) B2931511
theorem B1737839 : Blo 1736569 1737839 := bstep (se 1 (by rfl) ⟨1303379, by rfl⟩ : syracuseStep 1737839 = 2606759) B2606759
theorem B1737895 : Blo 1736569 1737895 := bstep (se 1 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 1737895 = 2606843) B2606843
theorem B1737919 : Blo 1736569 1737919 := bstep (se 1 (by rfl) ⟨1303439, by rfl⟩ : syracuseStep 1737919 = 2606879) B2606879
theorem B2606303 : Blo 1736569 2606303 := bstep (se 1 (by rfl) ⟨1954727, by rfl⟩ : syracuseStep 2606303 = 3909455) B3909455
theorem B1737951 : Blo 1736569 1737951 := bstep (se 1 (by rfl) ⟨1303463, by rfl⟩ : syracuseStep 1737951 = 2606927) B2606927
theorem B2606315 : Blo 1736569 2606315 := bstep (se 1 (by rfl) ⟨1954736, by rfl⟩ : syracuseStep 2606315 = 3909473) B3909473
theorem B1738031 : Blo 1736569 1738031 := bstep (se 1 (by rfl) ⟨1303523, by rfl⟩ : syracuseStep 1738031 = 2607047) B2607047
theorem B8791577 : Blo 1736569 8791577 := bstep (se 2 (by rfl) ⟨3296841, by rfl⟩ : syracuseStep 8791577 = 6593683) B6593683
theorem B1738267 : Blo 1736569 1738267 := bstep (se 1 (by rfl) ⟨1303700, by rfl⟩ : syracuseStep 1738267 = 2607401) B2607401
theorem B1738271 : Blo 1736569 1738271 := bstep (se 1 (by rfl) ⟨1303703, by rfl⟩ : syracuseStep 1738271 = 2607407) B2607407
theorem B9397787 : Blo 1736569 9397787 := bstep (se 1 (by rfl) ⟨7048340, by rfl⟩ : syracuseStep 9397787 = 14096681) B14096681
theorem B33392209 : Blo 1736569 33392209 := bstep (se 2 (by rfl) ⟨12522078, by rfl⟩ : syracuseStep 33392209 = 25044157) B25044157
theorem B2606699 : Blo 1736569 2606699 := bstep (se 1 (by rfl) ⟨1955024, by rfl⟩ : syracuseStep 2606699 = 3910049) B3910049
theorem B2606783 : Blo 1736569 2606783 := bstep (se 1 (by rfl) ⟨1955087, by rfl⟩ : syracuseStep 2606783 = 3910175) B3910175
theorem B1738431 : Blo 1736569 1738431 := bstep (se 1 (by rfl) ⟨1303823, by rfl⟩ : syracuseStep 1738431 = 2607647) B2607647
theorem B8349419 : Blo 1736569 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B2606969 : Blo 1736569 2606969 := bstep (se 2 (by rfl) ⟨977613, by rfl⟩ : syracuseStep 2606969 = 1955227) B1955227
theorem B19793807 : Blo 1736569 19793807 := bstep (se 1 (by rfl) ⟨14845355, by rfl⟩ : syracuseStep 19793807 = 29690711) B29690711
theorem B11282399 : Blo 1736569 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B4696031 : Blo 1736569 4696031 := bstep (se 1 (by rfl) ⟨3522023, by rfl⟩ : syracuseStep 4696031 = 7044047) B7044047
theorem B3909599 : Blo 1736569 3909599 := bstep (se 1 (by rfl) ⟨2932199, by rfl⟩ : syracuseStep 3909599 = 5864399) B5864399
theorem B5941295 : Blo 1736569 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B25397495 : Blo 1736569 25397495 := bstep (se 1 (by rfl) ⟨19048121, by rfl⟩ : syracuseStep 25397495 = 38096243) B38096243
theorem B50809103 : Blo 1736569 50809103 := bstep (se 1 (by rfl) ⟨38106827, by rfl⟩ : syracuseStep 50809103 = 76213655) B76213655
theorem B6596903 : Blo 1736569 6596903 := bstep (se 1 (by rfl) ⟨4947677, by rfl⟩ : syracuseStep 6596903 = 9895355) B9895355
theorem B8792387 : Blo 1736569 8792387 := bstep (se 1 (by rfl) ⟨6594290, by rfl⟩ : syracuseStep 8792387 = 13188581) B13188581
theorem B2607719 : Blo 1736569 2607719 := bstep (se 1 (by rfl) ⟨1955789, by rfl⟩ : syracuseStep 2607719 = 3911579) B3911579
theorem B8350361 : Blo 1736569 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B56355587 : Blo 1736569 56355587 := bstep (se 1 (by rfl) ⟨42266690, by rfl⟩ : syracuseStep 56355587 = 84533381) B84533381
theorem B12528539 : Blo 1736569 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B3910607 : Blo 1736569 3910607 := bstep (se 1 (by rfl) ⟨2932955, by rfl⟩ : syracuseStep 3910607 = 5865911) B5865911
theorem B33385445 : Blo 1736569 33385445 := bstep (se 4 (by rfl) ⟨3129885, by rfl⟩ : syracuseStep 33385445 = 6259771) B6259771
theorem B12520439 : Blo 1736569 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B3910697 : Blo 1736569 3910697 := bstep (se 2 (by rfl) ⟨1466511, by rfl⟩ : syracuseStep 3910697 = 2933023) B2933023
theorem B12528769 : Blo 1736569 12528769 := bstep (se 2 (by rfl) ⟨4698288, by rfl⟩ : syracuseStep 12528769 = 9396577) B9396577
theorem B6597875 : Blo 1736569 6597875 := bstep (se 1 (by rfl) ⟨4948406, by rfl⟩ : syracuseStep 6597875 = 9896813) B9896813
theorem B3910931 : Blo 1736569 3910931 := bstep (se 1 (by rfl) ⟨2933198, by rfl⟩ : syracuseStep 3910931 = 5866397) B5866397
theorem B3910967 : Blo 1736569 3910967 := bstep (se 1 (by rfl) ⟨2933225, by rfl⟩ : syracuseStep 3910967 = 5866451) B5866451
theorem B38079839 : Blo 1736569 38079839 := bstep (se 1 (by rfl) ⟨28559879, by rfl⟩ : syracuseStep 38079839 = 57119759) B57119759
theorem B6598043 : Blo 1736569 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B6598057 : Blo 1736569 6598057 := bstep (se 2 (by rfl) ⟨2474271, by rfl⟩ : syracuseStep 6598057 = 4948543) B4948543
theorem B6598331 : Blo 1736569 6598331 := bstep (se 1 (by rfl) ⟨4948748, by rfl⟩ : syracuseStep 6598331 = 9897497) B9897497
theorem B9891665 : Blo 1736569 9891665 := bstep (se 2 (by rfl) ⟨3709374, by rfl⟩ : syracuseStep 9891665 = 7418749) B7418749
theorem B3911561 : Blo 1736569 3911561 := bstep (se 2 (by rfl) ⟨1466835, by rfl⟩ : syracuseStep 3911561 = 2933671) B2933671
theorem B1953787 : Blo 1736569 1953787 := bstep (se 1 (by rfl) ⟨1465340, by rfl⟩ : syracuseStep 1953787 = 2930681) B2930681
theorem B3297343 : Blo 1736569 3297343 := bstep (se 1 (by rfl) ⟨2473007, by rfl⟩ : syracuseStep 3297343 = 4946015) B4946015
theorem B3911777 : Blo 1736569 3911777 := bstep (se 2 (by rfl) ⟨1466916, by rfl⟩ : syracuseStep 3911777 = 2933833) B2933833
theorem B1953895 : Blo 1736569 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B1953967 : Blo 1736569 1953967 := bstep (se 1 (by rfl) ⟨1465475, by rfl⟩ : syracuseStep 1953967 = 2930951) B2930951
theorem B2199727 : Blo 1736569 2199727 := bstep (se 1 (by rfl) ⟨1649795, by rfl⟩ : syracuseStep 2199727 = 3299591) B3299591
theorem B112783589 : Blo 1736569 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B5017897 : Blo 1736569 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B7418425 : Blo 1736569 7418425 := bstep (se 2 (by rfl) ⟨2781909, by rfl⟩ : syracuseStep 7418425 = 5563819) B5563819
theorem B1954651 : Blo 1736569 1954651 := bstep (se 1 (by rfl) ⟨1465988, by rfl⟩ : syracuseStep 1954651 = 2931977) B2931977
theorem B396022745 : Blo 1736569 396022745 := bstep (se 2 (by rfl) ⟨148508529, by rfl⟩ : syracuseStep 396022745 = 297017059) B297017059
theorem B42857551 : Blo 1736569 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B14095457 : Blo 1736569 14095457 := bstep (se 2 (by rfl) ⟨5285796, by rfl⟩ : syracuseStep 14095457 = 10571593) B10571593
theorem B9893123 : Blo 1736569 9893123 := bstep (se 1 (by rfl) ⟨7419842, by rfl⟩ : syracuseStep 9893123 = 14839685) B14839685
theorem B8795465 : Blo 1736569 8795465 := bstep (se 2 (by rfl) ⟨3298299, by rfl⟩ : syracuseStep 8795465 = 6596599) B6596599
theorem B10565117 : Blo 1736569 10565117 := bstep (se 3 (by rfl) ⟨1980959, by rfl⟩ : syracuseStep 10565117 = 3961919) B3961919
theorem B14096035 : Blo 1736569 14096035 := bstep (se 1 (by rfl) ⟨10572026, by rfl⟩ : syracuseStep 14096035 = 21144053) B21144053
theorem B24090295 : Blo 1736569 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B3299143 : Blo 1736569 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B4175815 : Blo 1736569 4175815 := bstep (se 1 (by rfl) ⟨3131861, by rfl⟩ : syracuseStep 4175815 = 6263723) B6263723
theorem B13187123 : Blo 1736569 13187123 := bstep (se 1 (by rfl) ⟨9890342, by rfl⟩ : syracuseStep 13187123 = 19780685) B19780685
theorem B8345747 : Blo 1736569 8345747 := bstep (se 1 (by rfl) ⟨6259310, by rfl⟩ : syracuseStep 8345747 = 12518621) B12518621
theorem B8353975 : Blo 1736569 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B25049351 : Blo 1736569 25049351 := bstep (se 1 (by rfl) ⟨18787013, by rfl⟩ : syracuseStep 25049351 = 37574027) B37574027
theorem B16693613 : Blo 1736569 16693613 := bstep (se 3 (by rfl) ⟨3130052, by rfl⟩ : syracuseStep 16693613 = 6260105) B6260105
theorem B34322899 : Blo 1736569 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B7420423 : Blo 1736569 7420423 := bstep (se 1 (by rfl) ⟨5565317, by rfl⟩ : syracuseStep 7420423 = 11130635) B11130635
theorem B5863967 : Blo 1736569 5863967 := bstep (se 1 (by rfl) ⟨4397975, by rfl⟩ : syracuseStep 5863967 = 8795951) B8795951
theorem B2931241 : Blo 1736569 2931241 := bstep (se 2 (by rfl) ⟨1099215, by rfl⟩ : syracuseStep 2931241 = 2198431) B2198431
theorem B14277181 : Blo 1736569 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B8796761 : Blo 1736569 8796761 := bstep (se 2 (by rfl) ⟨3298785, by rfl⟩ : syracuseStep 8796761 = 6597571) B6597571
theorem B2472871 : Blo 1736569 2472871 := bstep (se 1 (by rfl) ⟨1854653, by rfl⟩ : syracuseStep 2472871 = 3709307) B3709307
theorem B14851097 : Blo 1736569 14851097 := bstep (se 2 (by rfl) ⟨5569161, by rfl⟩ : syracuseStep 14851097 = 11138323) B11138323
theorem B7421159 : Blo 1736569 7421159 := bstep (se 1 (by rfl) ⟨5565869, by rfl⟩ : syracuseStep 7421159 = 11131739) B11131739
theorem B2931943 : Blo 1736569 2931943 := bstep (se 1 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 2931943 = 4397915) B4397915
theorem B2932139 : Blo 1736569 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B7142863 : Blo 1736569 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B3964639 : Blo 1736569 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B3907439 : Blo 1736569 3907439 := bstep (se 1 (by rfl) ⟨2930579, by rfl⟩ : syracuseStep 3907439 = 5861159) B5861159
theorem B1736615 : Blo 1736569 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B2932679 : Blo 1736569 2932679 := bstep (se 1 (by rfl) ⟨2199509, by rfl⟩ : syracuseStep 2932679 = 4399019) B4399019
theorem B1736831 : Blo 1736569 1736831 := bstep (se 1 (by rfl) ⟨1302623, by rfl⟩ : syracuseStep 1736831 = 2605247) B2605247
theorem B2605193 : Blo 1736569 2605193 := bstep (se 2 (by rfl) ⟨976947, by rfl⟩ : syracuseStep 2605193 = 1953895) B1953895
theorem B2605289 : Blo 1736569 2605289 := bstep (se 2 (by rfl) ⟨976983, by rfl⟩ : syracuseStep 2605289 = 1953967) B1953967
theorem B2932969 : Blo 1736569 2932969 := bstep (se 2 (by rfl) ⟨1099863, by rfl⟩ : syracuseStep 2932969 = 2199727) B2199727
theorem B2605415 : Blo 1736569 2605415 := bstep (se 1 (by rfl) ⟨1954061, by rfl⟩ : syracuseStep 2605415 = 3908123) B3908123
theorem B1737115 : Blo 1736569 1737115 := bstep (se 1 (by rfl) ⟨1302836, by rfl⟩ : syracuseStep 1737115 = 2605673) B2605673
theorem B1737119 : Blo 1736569 1737119 := bstep (se 1 (by rfl) ⟨1302839, by rfl⟩ : syracuseStep 1737119 = 2605679) B2605679
theorem B228573605 : Blo 1736569 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B2605535 : Blo 1736569 2605535 := bstep (se 1 (by rfl) ⟨1954151, by rfl⟩ : syracuseStep 2605535 = 3908303) B3908303
theorem B2605787 : Blo 1736569 2605787 := bstep (se 1 (by rfl) ⟨1954340, by rfl⟩ : syracuseStep 2605787 = 3908681) B3908681
theorem B3908321 : Blo 1736569 3908321 := bstep (se 2 (by rfl) ⟨1465620, by rfl⟩ : syracuseStep 3908321 = 2931241) B2931241
theorem B9396971 : Blo 1736569 9396971 := bstep (se 1 (by rfl) ⟨7047728, by rfl⟩ : syracuseStep 9396971 = 14095457) B14095457
theorem B1737535 : Blo 1736569 1737535 := bstep (se 1 (by rfl) ⟨1303151, by rfl⟩ : syracuseStep 1737535 = 2606303) B2606303
theorem B1737543 : Blo 1736569 1737543 := bstep (se 1 (by rfl) ⟨1303157, by rfl⟩ : syracuseStep 1737543 = 2606315) B2606315
theorem B6595415 : Blo 1736569 6595415 := bstep (se 1 (by rfl) ⟨4946561, by rfl⟩ : syracuseStep 6595415 = 9893123) B9893123
theorem B14844809 : Blo 1736569 14844809 := bstep (se 2 (by rfl) ⟨5566803, by rfl⟩ : syracuseStep 14844809 = 11133607) B11133607
theorem B5866505 : Blo 1736569 5866505 := bstep (se 2 (by rfl) ⟨2199939, by rfl⟩ : syracuseStep 5866505 = 4399879) B4399879
theorem B1737799 : Blo 1736569 1737799 := bstep (se 1 (by rfl) ⟨1303349, by rfl⟩ : syracuseStep 1737799 = 2606699) B2606699
theorem B2606201 : Blo 1736569 2606201 := bstep (se 2 (by rfl) ⟨977325, by rfl⟩ : syracuseStep 2606201 = 1954651) B1954651
theorem B1737855 : Blo 1736569 1737855 := bstep (se 1 (by rfl) ⟨1303391, by rfl⟩ : syracuseStep 1737855 = 2606783) B2606783
theorem B1737979 : Blo 1736569 1737979 := bstep (se 1 (by rfl) ⟨1303484, by rfl⟩ : syracuseStep 1737979 = 2606969) B2606969
theorem B7521599 : Blo 1736569 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B3130687 : Blo 1736569 3130687 := bstep (se 1 (by rfl) ⟨2348015, by rfl⟩ : syracuseStep 3130687 = 4696031) B4696031
theorem B2606399 : Blo 1736569 2606399 := bstep (se 1 (by rfl) ⟨1954799, by rfl⟩ : syracuseStep 2606399 = 3909599) B3909599
theorem B8791415 : Blo 1736569 8791415 := bstep (se 1 (by rfl) ⟨6593561, by rfl⟩ : syracuseStep 8791415 = 13187123) B13187123
theorem B25060765 : Blo 1736569 25060765 := bstep (se 3 (by rfl) ⟨4698893, by rfl⟩ : syracuseStep 25060765 = 9397787) B9397787
theorem B5563831 : Blo 1736569 5563831 := bstep (se 1 (by rfl) ⟨4172873, by rfl⟩ : syracuseStep 5563831 = 8345747) B8345747
theorem B16705025 : Blo 1736569 16705025 := bstep (se 2 (by rfl) ⟨6264384, by rfl⟩ : syracuseStep 16705025 = 12528769) B12528769
theorem B3909257 : Blo 1736569 3909257 := bstep (se 2 (by rfl) ⟨1465971, by rfl⟩ : syracuseStep 3909257 = 2931943) B2931943
theorem B3909311 : Blo 1736569 3909311 := bstep (se 1 (by rfl) ⟨2931983, by rfl⟩ : syracuseStep 3909311 = 5863967) B5863967
theorem B1738479 : Blo 1736569 1738479 := bstep (se 1 (by rfl) ⟨1303859, by rfl⟩ : syracuseStep 1738479 = 2607719) B2607719
theorem B37570391 : Blo 1736569 37570391 := bstep (se 1 (by rfl) ⟨28177793, by rfl⟩ : syracuseStep 37570391 = 56355587) B56355587
theorem B2607071 : Blo 1736569 2607071 := bstep (se 1 (by rfl) ⟨1955303, by rfl⟩ : syracuseStep 2607071 = 3910607) B3910607
theorem B2607131 : Blo 1736569 2607131 := bstep (se 1 (by rfl) ⟨1955348, by rfl⟩ : syracuseStep 2607131 = 3910697) B3910697
theorem B2607287 : Blo 1736569 2607287 := bstep (se 1 (by rfl) ⟨1955465, by rfl⟩ : syracuseStep 2607287 = 3910931) B3910931
theorem B2607311 : Blo 1736569 2607311 := bstep (se 1 (by rfl) ⟨1955483, by rfl⟩ : syracuseStep 2607311 = 3910967) B3910967
theorem B18794713 : Blo 1736569 18794713 := bstep (se 2 (by rfl) ⟨7048017, by rfl⟩ : syracuseStep 18794713 = 14096035) B14096035
theorem B5286185 : Blo 1736569 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B2607707 : Blo 1736569 2607707 := bstep (se 1 (by rfl) ⟨1955780, by rfl⟩ : syracuseStep 2607707 = 3911561) B3911561
theorem B2607851 : Blo 1736569 2607851 := bstep (se 1 (by rfl) ⟨1955888, by rfl⟩ : syracuseStep 2607851 = 3911777) B3911777
theorem B75189059 : Blo 1736569 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B25046003 : Blo 1736569 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B45763865 : Blo 1736569 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B264015163 : Blo 1736569 264015163 := bstep (se 1 (by rfl) ⟨198011372, by rfl⟩ : syracuseStep 264015163 = 396022745) B396022745
theorem B3911039 : Blo 1736569 3911039 := bstep (se 1 (by rfl) ⟨2933279, by rfl⟩ : syracuseStep 3911039 = 5866559) B5866559
theorem B9891233 : Blo 1736569 9891233 := bstep (se 2 (by rfl) ⟨3709212, by rfl⟩ : syracuseStep 9891233 = 7418425) B7418425
theorem B5861051 : Blo 1736569 5861051 := bstep (se 1 (by rfl) ⟨4395788, by rfl⟩ : syracuseStep 5861051 = 8791577) B8791577
theorem B3297161 : Blo 1736569 3297161 := bstep (se 2 (by rfl) ⟨1236435, by rfl⟩ : syracuseStep 3297161 = 2472871) B2472871
theorem B3960863 : Blo 1736569 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B16699567 : Blo 1736569 16699567 := bstep (se 1 (by rfl) ⟨12524675, by rfl⟩ : syracuseStep 16699567 = 25049351) B25049351
theorem B5861591 : Blo 1736569 5861591 := bstep (se 1 (by rfl) ⟨4396193, by rfl⟩ : syracuseStep 5861591 = 8792387) B8792387
theorem B11129075 : Blo 1736569 11129075 := bstep (se 1 (by rfl) ⟨8346806, by rfl⟩ : syracuseStep 11129075 = 16693613) B16693613
theorem B5566907 : Blo 1736569 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B8352359 : Blo 1736569 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B9523817 : Blo 1736569 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B9900731 : Blo 1736569 9900731 := bstep (se 1 (by rfl) ⟨7425548, by rfl⟩ : syracuseStep 9900731 = 14851097) B14851097
theorem B1954759 : Blo 1736569 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B5567753 : Blo 1736569 5567753 := bstep (se 2 (by rfl) ⟨2087907, by rfl⟩ : syracuseStep 5567753 = 4175815) B4175815
theorem B1955119 : Blo 1736569 1955119 := bstep (se 1 (by rfl) ⟨1466339, by rfl⟩ : syracuseStep 1955119 = 2932679) B2932679
theorem B4396457 : Blo 1736569 4396457 := bstep (se 2 (by rfl) ⟨1648671, by rfl⟩ : syracuseStep 4396457 = 3297343) B3297343
theorem B7525889 : Blo 1736569 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B11138633 : Blo 1736569 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B6690529 : Blo 1736569 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B1955623 : Blo 1736569 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B42252293 : Blo 1736569 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B9893897 : Blo 1736569 9893897 := bstep (se 2 (by rfl) ⟨3710211, by rfl⟩ : syracuseStep 9893897 = 7420423) B7420423
theorem B19036241 : Blo 1736569 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B5863643 : Blo 1736569 5863643 := bstep (se 1 (by rfl) ⟨4397732, by rfl⟩ : syracuseStep 5863643 = 8795465) B8795465
theorem B101546237 : Blo 1736569 101546237 := bstep (se 3 (by rfl) ⟨19039919, by rfl⟩ : syracuseStep 101546237 = 38079839) B38079839
theorem B7043411 : Blo 1736569 7043411 := bstep (se 1 (by rfl) ⟨5282558, by rfl⟩ : syracuseStep 7043411 = 10565117) B10565117
theorem B13195871 : Blo 1736569 13195871 := bstep (se 1 (by rfl) ⟨9896903, by rfl⟩ : syracuseStep 13195871 = 19793807) B19793807
theorem B16931663 : Blo 1736569 16931663 := bstep (se 1 (by rfl) ⟨12698747, by rfl⟩ : syracuseStep 16931663 = 25397495) B25397495
theorem B33872735 : Blo 1736569 33872735 := bstep (se 1 (by rfl) ⟨25404551, by rfl⟩ : syracuseStep 33872735 = 50809103) B50809103
theorem B4397935 : Blo 1736569 4397935 := bstep (se 1 (by rfl) ⟨3298451, by rfl⟩ : syracuseStep 4397935 = 6596903) B6596903
theorem B5864507 : Blo 1736569 5864507 := bstep (se 1 (by rfl) ⟨4398380, by rfl⟩ : syracuseStep 5864507 = 8796761) B8796761
theorem B8797409 : Blo 1736569 8797409 := bstep (se 2 (by rfl) ⟨3299028, by rfl⟩ : syracuseStep 8797409 = 6598057) B6598057
theorem B22265117 : Blo 1736569 22265117 := bstep (se 3 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 22265117 = 8349419) B8349419
theorem B22256963 : Blo 1736569 22256963 := bstep (se 1 (by rfl) ⟨16692722, by rfl⟩ : syracuseStep 22256963 = 33385445) B33385445
theorem B8346959 : Blo 1736569 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B44522945 : Blo 1736569 44522945 := bstep (se 2 (by rfl) ⟨16696104, by rfl⟩ : syracuseStep 44522945 = 33392209) B33392209
theorem B4947439 : Blo 1736569 4947439 := bstep (se 1 (by rfl) ⟨3710579, by rfl⟩ : syracuseStep 4947439 = 7421159) B7421159
theorem B4398583 : Blo 1736569 4398583 := bstep (se 1 (by rfl) ⟨3298937, by rfl⟩ : syracuseStep 4398583 = 6597875) B6597875
theorem B32120393 : Blo 1736569 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B4398695 : Blo 1736569 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B4398857 : Blo 1736569 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B4398887 : Blo 1736569 4398887 := bstep (se 1 (by rfl) ⟨3299165, by rfl⟩ : syracuseStep 4398887 = 6598331) B6598331
theorem B6594443 : Blo 1736569 6594443 := bstep (se 1 (by rfl) ⟨4945832, by rfl⟩ : syracuseStep 6594443 = 9891665) B9891665
theorem B2604959 : Blo 1736569 2604959 := bstep (se 1 (by rfl) ⟨1953719, by rfl⟩ : syracuseStep 2604959 = 3907439) B3907439
theorem B2605049 : Blo 1736569 2605049 := bstep (se 2 (by rfl) ⟨976893, by rfl⟩ : syracuseStep 2605049 = 1953787) B1953787
theorem B1736795 : Blo 1736569 1736795 := bstep (se 1 (by rfl) ⟨1302596, by rfl⟩ : syracuseStep 1736795 = 2605193) B2605193
theorem B3907727 : Blo 1736569 3907727 := bstep (se 1 (by rfl) ⟨2930795, by rfl⟩ : syracuseStep 3907727 = 5861591) B5861591
theorem B1736859 : Blo 1736569 1736859 := bstep (se 1 (by rfl) ⟨1302644, by rfl⟩ : syracuseStep 1736859 = 2605289) B2605289
theorem B22266089 : Blo 1736569 22266089 := bstep (se 2 (by rfl) ⟨8349783, by rfl⟩ : syracuseStep 22266089 = 16699567) B16699567
theorem B1736943 : Blo 1736569 1736943 := bstep (se 1 (by rfl) ⟨1302707, by rfl⟩ : syracuseStep 1736943 = 2605415) B2605415
theorem B3711271 : Blo 1736569 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B25059617 : Blo 1736569 25059617 := bstep (se 2 (by rfl) ⟨9397356, by rfl⟩ : syracuseStep 25059617 = 18794713) B18794713
theorem B1737023 : Blo 1736569 1737023 := bstep (se 1 (by rfl) ⟨1302767, by rfl⟩ : syracuseStep 1737023 = 2605535) B2605535
theorem B6349211 : Blo 1736569 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B1737191 : Blo 1736569 1737191 := bstep (se 1 (by rfl) ⟨1302893, by rfl⟩ : syracuseStep 1737191 = 2605787) B2605787
theorem B2605547 : Blo 1736569 2605547 := bstep (se 1 (by rfl) ⟨1954160, by rfl⟩ : syracuseStep 2605547 = 3908321) B3908321
theorem B9896539 : Blo 1736569 9896539 := bstep (se 1 (by rfl) ⟨7422404, by rfl⟩ : syracuseStep 9896539 = 14844809) B14844809
theorem B1737467 : Blo 1736569 1737467 := bstep (se 1 (by rfl) ⟨1303100, by rfl⟩ : syracuseStep 1737467 = 2606201) B2606201
theorem B3711835 : Blo 1736569 3711835 := bstep (se 1 (by rfl) ⟨2783876, by rfl⟩ : syracuseStep 3711835 = 5567753) B5567753
theorem B5014399 : Blo 1736569 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B1737599 : Blo 1736569 1737599 := bstep (se 1 (by rfl) ⟨1303199, by rfl⟩ : syracuseStep 1737599 = 2606399) B2606399
theorem B2606171 : Blo 1736569 2606171 := bstep (se 1 (by rfl) ⟨1954628, by rfl⟩ : syracuseStep 2606171 = 3909257) B3909257
theorem B2606207 : Blo 1736569 2606207 := bstep (se 1 (by rfl) ⟨1954655, by rfl⟩ : syracuseStep 2606207 = 3909311) B3909311
theorem B2606345 : Blo 1736569 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B1738047 : Blo 1736569 1738047 := bstep (se 1 (by rfl) ⟨1303535, by rfl⟩ : syracuseStep 1738047 = 2607071) B2607071
theorem B6595931 : Blo 1736569 6595931 := bstep (se 1 (by rfl) ⟨4946948, by rfl⟩ : syracuseStep 6595931 = 9893897) B9893897
theorem B1738087 : Blo 1736569 1738087 := bstep (se 1 (by rfl) ⟨1303565, by rfl⟩ : syracuseStep 1738087 = 2607131) B2607131
theorem B12690827 : Blo 1736569 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B1738191 : Blo 1736569 1738191 := bstep (se 1 (by rfl) ⟨1303643, by rfl⟩ : syracuseStep 1738191 = 2607287) B2607287
theorem B1738207 : Blo 1736569 1738207 := bstep (se 1 (by rfl) ⟨1303655, by rfl⟩ : syracuseStep 1738207 = 2607311) B2607311
theorem B3909095 : Blo 1736569 3909095 := bstep (se 1 (by rfl) ⟨2931821, by rfl⟩ : syracuseStep 3909095 = 5863643) B5863643
theorem B3524123 : Blo 1736569 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B4695607 : Blo 1736569 4695607 := bstep (se 1 (by rfl) ⟨3521705, by rfl⟩ : syracuseStep 4695607 = 7043411) B7043411
theorem B1738471 : Blo 1736569 1738471 := bstep (se 1 (by rfl) ⟨1303853, by rfl⟩ : syracuseStep 1738471 = 2607707) B2607707
theorem B2606825 : Blo 1736569 2606825 := bstep (se 2 (by rfl) ⟨977559, by rfl⟩ : syracuseStep 2606825 = 1955119) B1955119
theorem B352020217 : Blo 1736569 352020217 := bstep (se 2 (by rfl) ⟨132007581, by rfl⟩ : syracuseStep 352020217 = 264015163) B264015163
theorem B1738567 : Blo 1736569 1738567 := bstep (se 1 (by rfl) ⟨1303925, by rfl⟩ : syracuseStep 1738567 = 2607851) B2607851
theorem B6596585 : Blo 1736569 6596585 := bstep (se 2 (by rfl) ⟨2473719, by rfl⟩ : syracuseStep 6596585 = 4947439) B4947439
theorem B16697335 : Blo 1736569 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B3909671 : Blo 1736569 3909671 := bstep (se 1 (by rfl) ⟨2932253, by rfl⟩ : syracuseStep 3909671 = 5864507) B5864507
theorem B30509243 : Blo 1736569 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B14837975 : Blo 1736569 14837975 := bstep (se 1 (by rfl) ⟨11128481, by rfl⟩ : syracuseStep 14837975 = 22256963) B22256963
theorem B5564639 : Blo 1736569 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B2607359 : Blo 1736569 2607359 := bstep (se 1 (by rfl) ⟨1955519, by rfl⟩ : syracuseStep 2607359 = 3911039) B3911039
theorem B29681963 : Blo 1736569 29681963 := bstep (se 1 (by rfl) ⟨22261472, by rfl⟩ : syracuseStep 29681963 = 44522945) B44522945
theorem B2607497 : Blo 1736569 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B2198107 : Blo 1736569 2198107 := bstep (se 1 (by rfl) ⟨1648580, by rfl⟩ : syracuseStep 2198107 = 3297161) B3297161
theorem B2640575 : Blo 1736569 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B152382403 : Blo 1736569 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B3910625 : Blo 1736569 3910625 := bstep (se 2 (by rfl) ⟨1466484, by rfl⟩ : syracuseStep 3910625 = 2932969) B2932969
theorem B3911003 : Blo 1736569 3911003 := bstep (se 1 (by rfl) ⟨2933252, by rfl⟩ : syracuseStep 3911003 = 5866505) B5866505
theorem B342617525 : Blo 1736569 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B5860943 : Blo 1736569 5860943 := bstep (se 1 (by rfl) ⟨4395707, by rfl⟩ : syracuseStep 5860943 = 8791415) B8791415
theorem B11136683 : Blo 1736569 11136683 := bstep (se 1 (by rfl) ⟨8352512, by rfl⟩ : syracuseStep 11136683 = 16705025) B16705025
theorem B5017259 : Blo 1736569 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B7425755 : Blo 1736569 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B25046927 : Blo 1736569 25046927 := bstep (se 1 (by rfl) ⟨18785195, by rfl⟩ : syracuseStep 25046927 = 37570391) B37570391
theorem B28168195 : Blo 1736569 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B4174249 : Blo 1736569 4174249 := bstep (se 2 (by rfl) ⟨1565343, by rfl⟩ : syracuseStep 4174249 = 3130687) B3130687
theorem B22581823 : Blo 1736569 22581823 := bstep (se 1 (by rfl) ⟨16936367, by rfl⟩ : syracuseStep 22581823 = 33872735) B33872735
theorem B7418441 : Blo 1736569 7418441 := bstep (se 2 (by rfl) ⟨2781915, by rfl⟩ : syracuseStep 7418441 = 5563831) B5563831
theorem B4396295 : Blo 1736569 4396295 := bstep (se 1 (by rfl) ⟨3297221, by rfl⟩ : syracuseStep 4396295 = 6594443) B6594443
theorem B7419383 : Blo 1736569 7419383 := bstep (se 1 (by rfl) ⟨5564537, by rfl⟩ : syracuseStep 7419383 = 11129075) B11129075
theorem B5568239 : Blo 1736569 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B6600487 : Blo 1736569 6600487 := bstep (se 1 (by rfl) ⟨4950365, by rfl⟩ : syracuseStep 6600487 = 9900731) B9900731
theorem B6264647 : Blo 1736569 6264647 := bstep (se 1 (by rfl) ⟨4698485, by rfl⟩ : syracuseStep 6264647 = 9396971) B9396971
theorem B4396943 : Blo 1736569 4396943 := bstep (se 1 (by rfl) ⟨3297707, by rfl⟩ : syracuseStep 4396943 = 6595415) B6595415
theorem B2930971 : Blo 1736569 2930971 := bstep (se 1 (by rfl) ⟨2198228, by rfl⟩ : syracuseStep 2930971 = 4396457) B4396457
theorem B5863913 : Blo 1736569 5863913 := bstep (se 2 (by rfl) ⟨2198967, by rfl⟩ : syracuseStep 5863913 = 4397935) B4397935
theorem B67697491 : Blo 1736569 67697491 := bstep (se 1 (by rfl) ⟨50773118, by rfl⟩ : syracuseStep 67697491 = 101546237) B101546237
theorem B8797247 : Blo 1736569 8797247 := bstep (se 1 (by rfl) ⟨6597935, by rfl⟩ : syracuseStep 8797247 = 13195871) B13195871
theorem B33414353 : Blo 1736569 33414353 := bstep (se 2 (by rfl) ⟨12530382, by rfl⟩ : syracuseStep 33414353 = 25060765) B25060765
theorem B50126039 : Blo 1736569 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B11287775 : Blo 1736569 11287775 := bstep (se 1 (by rfl) ⟨8465831, by rfl⟩ : syracuseStep 11287775 = 16931663) B16931663
theorem B5864777 : Blo 1736569 5864777 := bstep (se 2 (by rfl) ⟨2199291, by rfl⟩ : syracuseStep 5864777 = 4398583) B4398583
theorem B5864939 : Blo 1736569 5864939 := bstep (se 1 (by rfl) ⟨4398704, by rfl⟩ : syracuseStep 5864939 = 8797409) B8797409
theorem B14843411 : Blo 1736569 14843411 := bstep (se 1 (by rfl) ⟨11132558, by rfl⟩ : syracuseStep 14843411 = 22265117) B22265117
theorem B6594155 : Blo 1736569 6594155 := bstep (se 1 (by rfl) ⟨4945616, by rfl⟩ : syracuseStep 6594155 = 9891233) B9891233
theorem B8920705 : Blo 1736569 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B2932463 : Blo 1736569 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B3907367 : Blo 1736569 3907367 := bstep (se 1 (by rfl) ⟨2930525, by rfl⟩ : syracuseStep 3907367 = 5861051) B5861051
theorem B2932571 : Blo 1736569 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B2932591 : Blo 1736569 2932591 := bstep (se 1 (by rfl) ⟨2199443, by rfl⟩ : syracuseStep 2932591 = 4398887) B4398887
theorem B1736639 : Blo 1736569 1736639 := bstep (se 1 (by rfl) ⟨1302479, by rfl⟩ : syracuseStep 1736639 = 2604959) B2604959
theorem B1736699 : Blo 1736569 1736699 := bstep (se 1 (by rfl) ⟨1302524, by rfl⟩ : syracuseStep 1736699 = 2605049) B2605049
theorem B2605151 : Blo 1736569 2605151 := bstep (se 1 (by rfl) ⟨1953863, by rfl⟩ : syracuseStep 2605151 = 3907727) B3907727
theorem B14844059 : Blo 1736569 14844059 := bstep (se 1 (by rfl) ⟨11133044, by rfl⟩ : syracuseStep 14844059 = 22266089) B22266089
theorem B1737031 : Blo 1736569 1737031 := bstep (se 1 (by rfl) ⟨1302773, by rfl⟩ : syracuseStep 1737031 = 2605547) B2605547
theorem B3907961 : Blo 1736569 3907961 := bstep (se 2 (by rfl) ⟨1465485, by rfl⟩ : syracuseStep 3907961 = 2930971) B2930971
theorem B4948361 : Blo 1736569 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B1737447 : Blo 1736569 1737447 := bstep (se 1 (by rfl) ⟨1303085, by rfl⟩ : syracuseStep 1737447 = 2606171) B2606171
theorem B1737471 : Blo 1736569 1737471 := bstep (se 1 (by rfl) ⟨1303103, by rfl⟩ : syracuseStep 1737471 = 2606207) B2606207
theorem B1737563 : Blo 1736569 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B2606063 : Blo 1736569 2606063 := bstep (se 1 (by rfl) ⟨1954547, by rfl⟩ : syracuseStep 2606063 = 3909095) B3909095
theorem B4949113 : Blo 1736569 4949113 := bstep (se 2 (by rfl) ⟨1855917, by rfl⟩ : syracuseStep 4949113 = 3711835) B3711835
theorem B1737883 : Blo 1736569 1737883 := bstep (se 1 (by rfl) ⟨1303412, by rfl⟩ : syracuseStep 1737883 = 2606825) B2606825
theorem B3712159 : Blo 1736569 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B6685865 : Blo 1736569 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B2606447 : Blo 1736569 2606447 := bstep (se 1 (by rfl) ⟨1954835, by rfl⟩ : syracuseStep 2606447 = 3909671) B3909671
theorem B1738239 : Blo 1736569 1738239 := bstep (se 1 (by rfl) ⟨1303679, by rfl⟩ : syracuseStep 1738239 = 2607359) B2607359
theorem B1738331 : Blo 1736569 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B3909275 : Blo 1736569 3909275 := bstep (se 1 (by rfl) ⟨2931956, by rfl⟩ : syracuseStep 3909275 = 5863913) B5863913
theorem B2607083 : Blo 1736569 2607083 := bstep (se 1 (by rfl) ⟨1955312, by rfl⟩ : syracuseStep 2607083 = 3910625) B3910625
theorem B6260809 : Blo 1736569 6260809 := bstep (se 2 (by rfl) ⟨2347803, by rfl⟩ : syracuseStep 6260809 = 4695607) B4695607
theorem B22276235 : Blo 1736569 22276235 := bstep (se 1 (by rfl) ⟨16707176, by rfl⟩ : syracuseStep 22276235 = 33414353) B33414353
theorem B33417359 : Blo 1736569 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B3909851 : Blo 1736569 3909851 := bstep (se 1 (by rfl) ⟨2932388, by rfl⟩ : syracuseStep 3909851 = 5864777) B5864777
theorem B2607335 : Blo 1736569 2607335 := bstep (se 1 (by rfl) ⟨1955501, by rfl⟩ : syracuseStep 2607335 = 3911003) B3911003
theorem B228411683 : Blo 1736569 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B3909959 : Blo 1736569 3909959 := bstep (se 1 (by rfl) ⟨2932469, by rfl⟩ : syracuseStep 3909959 = 5864939) B5864939
theorem B812706149 : Blo 1736569 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B8800649 : Blo 1736569 8800649 := bstep (se 2 (by rfl) ⟨3300243, by rfl⟩ : syracuseStep 8800649 = 6600487) B6600487
theorem B7424455 : Blo 1736569 7424455 := bstep (se 1 (by rfl) ⟨5568341, by rfl⟩ : syracuseStep 7424455 = 11136683) B11136683
theorem B3344839 : Blo 1736569 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B4950503 : Blo 1736569 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B3910121 : Blo 1736569 3910121 := bstep (se 2 (by rfl) ⟨1466295, by rfl⟩ : syracuseStep 3910121 = 2932591) B2932591
theorem B16697951 : Blo 1736569 16697951 := bstep (se 1 (by rfl) ⟨12523463, by rfl⟩ : syracuseStep 16697951 = 25046927) B25046927
theorem B16706411 : Blo 1736569 16706411 := bstep (se 1 (by rfl) ⟨12529808, by rfl⟩ : syracuseStep 16706411 = 25059617) B25059617
theorem B5565665 : Blo 1736569 5565665 := bstep (se 2 (by rfl) ⟨2087124, by rfl⟩ : syracuseStep 5565665 = 4174249) B4174249
theorem B14839037 : Blo 1736569 14839037 := bstep (se 3 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 14839037 = 5564639) B5564639
theorem B30109097 : Blo 1736569 30109097 := bstep (se 2 (by rfl) ⟨11290911, by rfl⟩ : syracuseStep 30109097 = 22581823) B22581823
theorem B90263321 : Blo 1736569 90263321 := bstep (se 2 (by rfl) ⟨33848745, by rfl⟩ : syracuseStep 90263321 = 67697491) B67697491
theorem B9891983 : Blo 1736569 9891983 := bstep (se 1 (by rfl) ⟨7418987, by rfl⟩ : syracuseStep 9891983 = 14837975) B14837975
theorem B19787975 : Blo 1736569 19787975 := bstep (se 1 (by rfl) ⟨14840981, by rfl⟩ : syracuseStep 19787975 = 29681963) B29681963
theorem B7525183 : Blo 1736569 7525183 := bstep (se 1 (by rfl) ⟨5643887, by rfl⟩ : syracuseStep 7525183 = 11287775) B11287775
theorem B4396103 : Blo 1736569 4396103 := bstep (se 1 (by rfl) ⟨3297077, by rfl⟩ : syracuseStep 4396103 = 6594155) B6594155
theorem B1954975 : Blo 1736569 1954975 := bstep (se 1 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 1954975 = 2932463) B2932463
theorem B1955047 : Blo 1736569 1955047 := bstep (se 1 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 1955047 = 2932571) B2932571
theorem B22263113 : Blo 1736569 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B37557593 : Blo 1736569 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B4232807 : Blo 1736569 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B4945627 : Blo 1736569 4945627 := bstep (se 1 (by rfl) ⟨3709220, by rfl⟩ : syracuseStep 4945627 = 7418441) B7418441
theorem B2930809 : Blo 1736569 2930809 := bstep (se 2 (by rfl) ⟨1099053, by rfl⟩ : syracuseStep 2930809 = 2198107) B2198107
theorem B13195385 : Blo 1736569 13195385 := bstep (se 2 (by rfl) ⟨4948269, by rfl⟩ : syracuseStep 13195385 = 9896539) B9896539
theorem B2930863 : Blo 1736569 2930863 := bstep (se 1 (by rfl) ⟨2198147, by rfl⟩ : syracuseStep 2930863 = 4396295) B4396295
theorem B4397287 : Blo 1736569 4397287 := bstep (se 1 (by rfl) ⟨3297965, by rfl⟩ : syracuseStep 4397287 = 6595931) B6595931
theorem B8460551 : Blo 1736569 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B4946255 : Blo 1736569 4946255 := bstep (se 1 (by rfl) ⟨3709691, by rfl⟩ : syracuseStep 4946255 = 7419383) B7419383
theorem B2349415 : Blo 1736569 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B4176431 : Blo 1736569 4176431 := bstep (se 1 (by rfl) ⟨3132323, by rfl⟩ : syracuseStep 4176431 = 6264647) B6264647
theorem B2931295 : Blo 1736569 2931295 := bstep (se 1 (by rfl) ⟨2198471, by rfl⟩ : syracuseStep 2931295 = 4396943) B4396943
theorem B4397723 : Blo 1736569 4397723 := bstep (se 1 (by rfl) ⟨3298292, by rfl⟩ : syracuseStep 4397723 = 6596585) B6596585
theorem B20339495 : Blo 1736569 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B1760383 : Blo 1736569 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B5864831 : Blo 1736569 5864831 := bstep (se 1 (by rfl) ⟨4398623, by rfl⟩ : syracuseStep 5864831 = 8797247) B8797247
theorem B11894273 : Blo 1736569 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B469360289 : Blo 1736569 469360289 := bstep (se 2 (by rfl) ⟨176010108, by rfl⟩ : syracuseStep 469360289 = 352020217) B352020217
theorem B9895607 : Blo 1736569 9895607 := bstep (se 1 (by rfl) ⟨7421705, by rfl⟩ : syracuseStep 9895607 = 14843411) B14843411
theorem B3907295 : Blo 1736569 3907295 := bstep (se 1 (by rfl) ⟨2930471, by rfl⟩ : syracuseStep 3907295 = 5860943) B5860943
theorem B2604911 : Blo 1736569 2604911 := bstep (se 1 (by rfl) ⟨1953683, by rfl⟩ : syracuseStep 2604911 = 3907367) B3907367
theorem B1736767 : Blo 1736569 1736767 := bstep (se 1 (by rfl) ⟨1302575, by rfl⟩ : syracuseStep 1736767 = 2605151) B2605151
theorem B6594655 : Blo 1736569 6594655 := bstep (se 1 (by rfl) ⟨4945991, by rfl⟩ : syracuseStep 6594655 = 9891983) B9891983
theorem B8347745 : Blo 1736569 8347745 := bstep (se 2 (by rfl) ⟨3130404, by rfl⟩ : syracuseStep 8347745 = 6260809) B6260809
theorem B9896039 : Blo 1736569 9896039 := bstep (se 1 (by rfl) ⟨7422029, by rfl⟩ : syracuseStep 9896039 = 14844059) B14844059
theorem B3907745 : Blo 1736569 3907745 := bstep (se 2 (by rfl) ⟨1465404, by rfl⟩ : syracuseStep 3907745 = 2930809) B2930809
theorem B3907817 : Blo 1736569 3907817 := bstep (se 2 (by rfl) ⟨1465431, by rfl⟩ : syracuseStep 3907817 = 2930863) B2930863
theorem B2605307 : Blo 1736569 2605307 := bstep (se 1 (by rfl) ⟨1953980, by rfl⟩ : syracuseStep 2605307 = 3907961) B3907961
theorem B1737375 : Blo 1736569 1737375 := bstep (se 1 (by rfl) ⟨1303031, by rfl⟩ : syracuseStep 1737375 = 2606063) B2606063
theorem B9388709 : Blo 1736569 9388709 := bstep (se 4 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 9388709 = 1760383) B1760383
theorem B4457243 : Blo 1736569 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B3908393 : Blo 1736569 3908393 := bstep (se 2 (by rfl) ⟨1465647, by rfl⟩ : syracuseStep 3908393 = 2931295) B2931295
theorem B1737631 : Blo 1736569 1737631 := bstep (se 1 (by rfl) ⟨1303223, by rfl⟩ : syracuseStep 1737631 = 2606447) B2606447
theorem B2606183 : Blo 1736569 2606183 := bstep (se 1 (by rfl) ⟨1954637, by rfl⟩ : syracuseStep 2606183 = 3909275) B3909275
theorem B1738055 : Blo 1736569 1738055 := bstep (se 1 (by rfl) ⟨1303541, by rfl⟩ : syracuseStep 1738055 = 2607083) B2607083
theorem B2606567 : Blo 1736569 2606567 := bstep (se 1 (by rfl) ⟨1954925, by rfl⟩ : syracuseStep 2606567 = 3909851) B3909851
theorem B1738223 : Blo 1736569 1738223 := bstep (se 1 (by rfl) ⟨1303667, by rfl⟩ : syracuseStep 1738223 = 2607335) B2607335
theorem B152274455 : Blo 1736569 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B2606633 : Blo 1736569 2606633 := bstep (se 2 (by rfl) ⟨977487, by rfl⟩ : syracuseStep 2606633 = 1954975) B1954975
theorem B2606639 : Blo 1736569 2606639 := bstep (se 1 (by rfl) ⟨1954979, by rfl⟩ : syracuseStep 2606639 = 3909959) B3909959
theorem B541804099 : Blo 1736569 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B5867099 : Blo 1736569 5867099 := bstep (se 1 (by rfl) ⟨4400324, by rfl⟩ : syracuseStep 5867099 = 8800649) B8800649
theorem B2606729 : Blo 1736569 2606729 := bstep (se 2 (by rfl) ⟨977523, by rfl⟩ : syracuseStep 2606729 = 1955047) B1955047
theorem B2606747 : Blo 1736569 2606747 := bstep (se 1 (by rfl) ⟨1955060, by rfl⟩ : syracuseStep 2606747 = 3910121) B3910121
theorem B13559663 : Blo 1736569 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B3909887 : Blo 1736569 3909887 := bstep (se 1 (by rfl) ⟨2932415, by rfl⟩ : syracuseStep 3909887 = 5864831) B5864831
theorem B20072731 : Blo 1736569 20072731 := bstep (se 1 (by rfl) ⟨15054548, by rfl⟩ : syracuseStep 20072731 = 30109097) B30109097
theorem B6597071 : Blo 1736569 6597071 := bstep (se 1 (by rfl) ⟨4947803, by rfl⟩ : syracuseStep 6597071 = 9895607) B9895607
theorem B13191983 : Blo 1736569 13191983 := bstep (se 1 (by rfl) ⟨9893987, by rfl⟩ : syracuseStep 13191983 = 19787975) B19787975
theorem B9899273 : Blo 1736569 9899273 := bstep (se 2 (by rfl) ⟨3712227, by rfl⟩ : syracuseStep 9899273 = 7424455) B7424455
theorem B25038395 : Blo 1736569 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B2821871 : Blo 1736569 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B22278239 : Blo 1736569 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B71356565 : Blo 1736569 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B6598817 : Blo 1736569 6598817 := bstep (se 2 (by rfl) ⟨2474556, by rfl⟩ : syracuseStep 6598817 = 4949113) B4949113
theorem B5640367 : Blo 1736569 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B3297503 : Blo 1736569 3297503 := bstep (se 1 (by rfl) ⟨2473127, by rfl⟩ : syracuseStep 3297503 = 4946255) B4946255
theorem B1251627437 : Blo 1736569 1251627437 := bstep (se 3 (by rfl) ⟨234680144, by rfl⟩ : syracuseStep 1251627437 = 469360289) B469360289
theorem B12530213 : Blo 1736569 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B11137607 : Blo 1736569 11137607 := bstep (se 1 (by rfl) ⟨8353205, by rfl⟩ : syracuseStep 11137607 = 16706411) B16706411
theorem B9892691 : Blo 1736569 9892691 := bstep (se 1 (by rfl) ⟨7419518, by rfl⟩ : syracuseStep 9892691 = 14839037) B14839037
theorem B60175547 : Blo 1736569 60175547 := bstep (se 1 (by rfl) ⟨45131660, by rfl⟩ : syracuseStep 60175547 = 90263321) B90263321
theorem B3298907 : Blo 1736569 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B5863049 : Blo 1736569 5863049 := bstep (se 2 (by rfl) ⟨2198643, by rfl⟩ : syracuseStep 5863049 = 4397287) B4397287
theorem B2930735 : Blo 1736569 2930735 := bstep (se 1 (by rfl) ⟨2198051, by rfl⟩ : syracuseStep 2930735 = 4396103) B4396103
theorem B19798181 : Blo 1736569 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B14842075 : Blo 1736569 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B10033577 : Blo 1736569 10033577 := bstep (se 2 (by rfl) ⟨3762591, by rfl⟩ : syracuseStep 10033577 = 7525183) B7525183
theorem B8796923 : Blo 1736569 8796923 := bstep (se 1 (by rfl) ⟨6597692, by rfl⟩ : syracuseStep 8796923 = 13195385) B13195385
theorem B14850823 : Blo 1736569 14850823 := bstep (se 1 (by rfl) ⟨11138117, by rfl⟩ : syracuseStep 14850823 = 22276235) B22276235
theorem B3300335 : Blo 1736569 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2784287 : Blo 1736569 2784287 := bstep (se 1 (by rfl) ⟨2088215, by rfl⟩ : syracuseStep 2784287 = 4176431) B4176431
theorem B11131967 : Blo 1736569 11131967 := bstep (se 1 (by rfl) ⟨8348975, by rfl⟩ : syracuseStep 11131967 = 16697951) B16697951
theorem B2931815 : Blo 1736569 2931815 := bstep (se 1 (by rfl) ⟨2198861, by rfl⟩ : syracuseStep 2931815 = 4397723) B4397723
theorem B3710443 : Blo 1736569 3710443 := bstep (se 1 (by rfl) ⟨2782832, by rfl⟩ : syracuseStep 3710443 = 5565665) B5565665
theorem B6594169 : Blo 1736569 6594169 := bstep (se 2 (by rfl) ⟨2472813, by rfl⟩ : syracuseStep 6594169 = 4945627) B4945627
theorem B7929515 : Blo 1736569 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B2604863 : Blo 1736569 2604863 := bstep (se 1 (by rfl) ⟨1953647, by rfl⟩ : syracuseStep 2604863 = 3907295) B3907295
theorem B1736607 : Blo 1736569 1736607 := bstep (se 1 (by rfl) ⟨1302455, by rfl⟩ : syracuseStep 1736607 = 2604911) B2604911
theorem B14852159 : Blo 1736569 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B2605163 : Blo 1736569 2605163 := bstep (se 1 (by rfl) ⟨1953872, by rfl⟩ : syracuseStep 2605163 = 3907745) B3907745
theorem B4399211 : Blo 1736569 4399211 := bstep (se 1 (by rfl) ⟨3299408, by rfl⟩ : syracuseStep 4399211 = 6598817) B6598817
theorem B2605211 : Blo 1736569 2605211 := bstep (se 1 (by rfl) ⟨1953908, by rfl⟩ : syracuseStep 2605211 = 3907817) B3907817
theorem B1736871 : Blo 1736569 1736871 := bstep (se 1 (by rfl) ⟨1302653, by rfl⟩ : syracuseStep 1736871 = 2605307) B2605307
theorem B7520489 : Blo 1736569 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B26763641 : Blo 1736569 26763641 := bstep (se 2 (by rfl) ⟨10036365, by rfl⟩ : syracuseStep 26763641 = 20072731) B20072731
theorem B190284173 : Blo 1736569 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B6259139 : Blo 1736569 6259139 := bstep (se 1 (by rfl) ⟨4694354, by rfl⟩ : syracuseStep 6259139 = 9388709) B9388709
theorem B2605595 : Blo 1736569 2605595 := bstep (se 1 (by rfl) ⟨1954196, by rfl⟩ : syracuseStep 2605595 = 3908393) B3908393
theorem B6595127 : Blo 1736569 6595127 := bstep (se 1 (by rfl) ⟨4946345, by rfl⟩ : syracuseStep 6595127 = 9892691) B9892691
theorem B1737455 : Blo 1736569 1737455 := bstep (se 1 (by rfl) ⟨1303091, by rfl⟩ : syracuseStep 1737455 = 2606183) B2606183
theorem B40117031 : Blo 1736569 40117031 := bstep (se 1 (by rfl) ⟨30087773, by rfl⟩ : syracuseStep 40117031 = 60175547) B60175547
theorem B1737711 : Blo 1736569 1737711 := bstep (se 1 (by rfl) ⟨1303283, by rfl⟩ : syracuseStep 1737711 = 2606567) B2606567
theorem B19801097 : Blo 1736569 19801097 := bstep (se 2 (by rfl) ⟨7425411, by rfl⟩ : syracuseStep 19801097 = 14850823) B14850823
theorem B101516303 : Blo 1736569 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B1737755 : Blo 1736569 1737755 := bstep (se 1 (by rfl) ⟨1303316, by rfl⟩ : syracuseStep 1737755 = 2606633) B2606633
theorem B1737759 : Blo 1736569 1737759 := bstep (se 1 (by rfl) ⟨1303319, by rfl⟩ : syracuseStep 1737759 = 2606639) B2606639
theorem B3908699 : Blo 1736569 3908699 := bstep (se 1 (by rfl) ⟨2931524, by rfl⟩ : syracuseStep 3908699 = 5863049) B5863049
theorem B1737819 : Blo 1736569 1737819 := bstep (se 1 (by rfl) ⟨1303364, by rfl⟩ : syracuseStep 1737819 = 2606729) B2606729
theorem B1737831 : Blo 1736569 1737831 := bstep (se 1 (by rfl) ⟨1303373, by rfl⟩ : syracuseStep 1737831 = 2606747) B2606747
theorem B13198787 : Blo 1736569 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B2606591 : Blo 1736569 2606591 := bstep (se 1 (by rfl) ⟨1954943, by rfl⟩ : syracuseStep 2606591 = 3909887) B3909887
theorem B21145373 : Blo 1736569 21145373 := bstep (se 3 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 21145373 = 7929515) B7929515
theorem B722405465 : Blo 1736569 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B8792225 : Blo 1736569 8792225 := bstep (se 2 (by rfl) ⟨3297084, by rfl⟩ : syracuseStep 8792225 = 6594169) B6594169
theorem B6597359 : Blo 1736569 6597359 := bstep (se 1 (by rfl) ⟨4948019, by rfl⟩ : syracuseStep 6597359 = 9896039) B9896039
theorem B8792873 : Blo 1736569 8792873 := bstep (se 2 (by rfl) ⟨3297327, by rfl⟩ : syracuseStep 8792873 = 6594655) B6594655
theorem B2198335 : Blo 1736569 2198335 := bstep (se 1 (by rfl) ⟨1648751, by rfl⟩ : syracuseStep 2198335 = 3297503) B3297503
theorem B22260653 : Blo 1736569 22260653 := bstep (se 3 (by rfl) ⟨4173872, by rfl⟩ : syracuseStep 22260653 = 8347745) B8347745
theorem B7425071 : Blo 1736569 7425071 := bstep (se 1 (by rfl) ⟨5568803, by rfl⟩ : syracuseStep 7425071 = 11137607) B11137607
theorem B3911399 : Blo 1736569 3911399 := bstep (se 1 (by rfl) ⟨2933549, by rfl⟩ : syracuseStep 3911399 = 5867099) B5867099
theorem B9039775 : Blo 1736569 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B1953823 : Blo 1736569 1953823 := bstep (se 1 (by rfl) ⟨1465367, by rfl⟩ : syracuseStep 1953823 = 2930735) B2930735
theorem B6689051 : Blo 1736569 6689051 := bstep (se 1 (by rfl) ⟨5016788, by rfl⟩ : syracuseStep 6689051 = 10033577) B10033577
theorem B8794655 : Blo 1736569 8794655 := bstep (se 1 (by rfl) ⟨6595991, by rfl⟩ : syracuseStep 8794655 = 13191983) B13191983
theorem B7524989 : Blo 1736569 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B2200223 : Blo 1736569 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B1856191 : Blo 1736569 1856191 := bstep (se 1 (by rfl) ⟨1392143, by rfl⟩ : syracuseStep 1856191 = 2784287) B2784287
theorem B1954543 : Blo 1736569 1954543 := bstep (se 1 (by rfl) ⟨1465907, by rfl⟩ : syracuseStep 1954543 = 2931815) B2931815
theorem B6599515 : Blo 1736569 6599515 := bstep (se 1 (by rfl) ⟨4949636, by rfl⟩ : syracuseStep 6599515 = 9899273) B9899273
theorem B16692263 : Blo 1736569 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B19789433 : Blo 1736569 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B8353475 : Blo 1736569 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B2971495 : Blo 1736569 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B3337673165 : Blo 1736569 3337673165 := bstep (se 3 (by rfl) ⟨625813718, by rfl⟩ : syracuseStep 3337673165 = 1251627437) B1251627437
theorem B8797085 : Blo 1736569 8797085 := bstep (se 3 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 8797085 = 3298907) B3298907
theorem B4398047 : Blo 1736569 4398047 := bstep (se 1 (by rfl) ⟨3298535, by rfl⟩ : syracuseStep 4398047 = 6597071) B6597071
theorem B5864615 : Blo 1736569 5864615 := bstep (se 1 (by rfl) ⟨4398461, by rfl⟩ : syracuseStep 5864615 = 8796923) B8796923
theorem B4947257 : Blo 1736569 4947257 := bstep (se 2 (by rfl) ⟨1855221, by rfl⟩ : syracuseStep 4947257 = 3710443) B3710443
theorem B7421311 : Blo 1736569 7421311 := bstep (se 1 (by rfl) ⟨5565983, by rfl⟩ : syracuseStep 7421311 = 11131967) B11131967
theorem B1736575 : Blo 1736569 1736575 := bstep (se 1 (by rfl) ⟨1302431, by rfl⟩ : syracuseStep 1736575 = 2604863) B2604863
theorem B2605097 : Blo 1736569 2605097 := bstep (se 2 (by rfl) ⟨976911, by rfl⟩ : syracuseStep 2605097 = 1953823) B1953823
theorem B1736775 : Blo 1736569 1736775 := bstep (se 1 (by rfl) ⟨1302581, by rfl⟩ : syracuseStep 1736775 = 2605163) B2605163
theorem B2932807 : Blo 1736569 2932807 := bstep (se 1 (by rfl) ⟨2199605, by rfl⟩ : syracuseStep 2932807 = 4399211) B4399211
theorem B1736807 : Blo 1736569 1736807 := bstep (se 1 (by rfl) ⟨1302605, by rfl⟩ : syracuseStep 1736807 = 2605211) B2605211
theorem B5013659 : Blo 1736569 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B17842427 : Blo 1736569 17842427 := bstep (se 1 (by rfl) ⟨13381820, by rfl⟩ : syracuseStep 17842427 = 26763641) B26763641
theorem B1737063 : Blo 1736569 1737063 := bstep (se 1 (by rfl) ⟨1302797, by rfl⟩ : syracuseStep 1737063 = 2605595) B2605595
theorem B2605799 : Blo 1736569 2605799 := bstep (se 1 (by rfl) ⟨1954349, by rfl⟩ : syracuseStep 2605799 = 3908699) B3908699
theorem B2474921 : Blo 1736569 2474921 := bstep (se 2 (by rfl) ⟨928095, by rfl⟩ : syracuseStep 2474921 = 1856191) B1856191
theorem B8799191 : Blo 1736569 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B2606057 : Blo 1736569 2606057 := bstep (se 2 (by rfl) ⟨977271, by rfl⟩ : syracuseStep 2606057 = 1954543) B1954543
theorem B1737727 : Blo 1736569 1737727 := bstep (se 1 (by rfl) ⟨1303295, by rfl⟩ : syracuseStep 1737727 = 2606591) B2606591
theorem B8799353 : Blo 1736569 8799353 := bstep (se 2 (by rfl) ⟨3299757, by rfl⟩ : syracuseStep 8799353 = 6599515) B6599515
theorem B5867261 : Blo 1736569 5867261 := bstep (se 3 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 5867261 = 2200223) B2200223
theorem B4950047 : Blo 1736569 4950047 := bstep (se 1 (by rfl) ⟨3712535, by rfl⟩ : syracuseStep 4950047 = 7425071) B7425071
theorem B3909743 : Blo 1736569 3909743 := bstep (se 1 (by rfl) ⟨2932307, by rfl⟩ : syracuseStep 3909743 = 5864615) B5864615
theorem B2607599 : Blo 1736569 2607599 := bstep (se 1 (by rfl) ⟨1955699, by rfl⟩ : syracuseStep 2607599 = 3911399) B3911399
theorem B12053033 : Blo 1736569 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B4459367 : Blo 1736569 4459367 := bstep (se 1 (by rfl) ⟨3344525, by rfl⟩ : syracuseStep 4459367 = 6689051) B6689051
theorem B126856115 : Blo 1736569 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B4172759 : Blo 1736569 4172759 := bstep (se 1 (by rfl) ⟨3129569, by rfl⟩ : syracuseStep 4172759 = 6259139) B6259139
theorem B5016659 : Blo 1736569 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B13200731 : Blo 1736569 13200731 := bstep (se 1 (by rfl) ⟨9900548, by rfl⟩ : syracuseStep 13200731 = 19801097) B19801097
theorem B67677535 : Blo 1736569 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B11128175 : Blo 1736569 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B13192955 : Blo 1736569 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B481603643 : Blo 1736569 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B5861483 : Blo 1736569 5861483 := bstep (se 1 (by rfl) ⟨4396112, by rfl⟩ : syracuseStep 5861483 = 8792225) B8792225
theorem B2225115443 : Blo 1736569 2225115443 := bstep (se 1 (by rfl) ⟨1668836582, by rfl⟩ : syracuseStep 2225115443 = 3337673165) B3337673165
theorem B5861915 : Blo 1736569 5861915 := bstep (se 1 (by rfl) ⟨4396436, by rfl⟩ : syracuseStep 5861915 = 8792873) B8792873
theorem B15847973 : Blo 1736569 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B14840435 : Blo 1736569 14840435 := bstep (se 1 (by rfl) ⟨11130326, by rfl⟩ : syracuseStep 14840435 = 22260653) B22260653
theorem B3298171 : Blo 1736569 3298171 := bstep (se 1 (by rfl) ⟨2473628, by rfl⟩ : syracuseStep 3298171 = 4947257) B4947257
theorem B9901439 : Blo 1736569 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B5863103 : Blo 1736569 5863103 := bstep (se 1 (by rfl) ⟨4397327, by rfl⟩ : syracuseStep 5863103 = 8794655) B8794655
theorem B4396751 : Blo 1736569 4396751 := bstep (se 1 (by rfl) ⟨3297563, by rfl⟩ : syracuseStep 4396751 = 6595127) B6595127
theorem B26744687 : Blo 1736569 26744687 := bstep (se 1 (by rfl) ⟨20058515, by rfl⟩ : syracuseStep 26744687 = 40117031) B40117031
theorem B2931113 : Blo 1736569 2931113 := bstep (se 2 (by rfl) ⟨1099167, by rfl⟩ : syracuseStep 2931113 = 2198335) B2198335
theorem B5568983 : Blo 1736569 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B14096915 : Blo 1736569 14096915 := bstep (se 1 (by rfl) ⟨10572686, by rfl⟩ : syracuseStep 14096915 = 21145373) B21145373
theorem B4398239 : Blo 1736569 4398239 := bstep (se 1 (by rfl) ⟨3298679, by rfl⟩ : syracuseStep 4398239 = 6597359) B6597359
theorem B9895081 : Blo 1736569 9895081 := bstep (se 2 (by rfl) ⟨3710655, by rfl⟩ : syracuseStep 9895081 = 7421311) B7421311
theorem B5864723 : Blo 1736569 5864723 := bstep (se 1 (by rfl) ⟨4398542, by rfl⟩ : syracuseStep 5864723 = 8797085) B8797085
theorem B2932031 : Blo 1736569 2932031 := bstep (se 1 (by rfl) ⟨2199023, by rfl⟩ : syracuseStep 2932031 = 4398047) B4398047
theorem B1736731 : Blo 1736569 1736731 := bstep (se 1 (by rfl) ⟨1302548, by rfl⟩ : syracuseStep 1736731 = 2605097) B2605097
theorem B321069095 : Blo 1736569 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B3907655 : Blo 1736569 3907655 := bstep (se 1 (by rfl) ⟨2930741, by rfl⟩ : syracuseStep 3907655 = 5861483) B5861483
theorem B3342439 : Blo 1736569 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B11894951 : Blo 1736569 11894951 := bstep (se 1 (by rfl) ⟨8921213, by rfl⟩ : syracuseStep 11894951 = 17842427) B17842427
theorem B3907943 : Blo 1736569 3907943 := bstep (se 1 (by rfl) ⟨2930957, by rfl⟩ : syracuseStep 3907943 = 5861915) B5861915
theorem B1737199 : Blo 1736569 1737199 := bstep (se 1 (by rfl) ⟨1302899, by rfl⟩ : syracuseStep 1737199 = 2605799) B2605799
theorem B5866127 : Blo 1736569 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B1737371 : Blo 1736569 1737371 := bstep (se 1 (by rfl) ⟨1303028, by rfl⟩ : syracuseStep 1737371 = 2606057) B2606057
theorem B5866235 : Blo 1736569 5866235 := bstep (se 1 (by rfl) ⟨4399676, by rfl⟩ : syracuseStep 5866235 = 8799353) B8799353
theorem B53511029 : Blo 1736569 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B3908735 : Blo 1736569 3908735 := bstep (se 1 (by rfl) ⟨2931551, by rfl⟩ : syracuseStep 3908735 = 5863103) B5863103
theorem B2606495 : Blo 1736569 2606495 := bstep (se 1 (by rfl) ⟨1954871, by rfl⟩ : syracuseStep 2606495 = 3909743) B3909743
theorem B3712655 : Blo 1736569 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B1738399 : Blo 1736569 1738399 := bstep (se 1 (by rfl) ⟨1303799, by rfl⟩ : syracuseStep 1738399 = 2607599) B2607599
theorem B9397943 : Blo 1736569 9397943 := bstep (se 1 (by rfl) ⟨7048457, by rfl⟩ : syracuseStep 9397943 = 14096915) B14096915
theorem B90236713 : Blo 1736569 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B3909815 : Blo 1736569 3909815 := bstep (se 1 (by rfl) ⟨2932361, by rfl⟩ : syracuseStep 3909815 = 5864723) B5864723
theorem B8800487 : Blo 1736569 8800487 := bstep (se 1 (by rfl) ⟨6600365, by rfl⟩ : syracuseStep 8800487 = 13200731) B13200731
theorem B3910409 : Blo 1736569 3910409 := bstep (se 2 (by rfl) ⟨1466403, by rfl⟩ : syracuseStep 3910409 = 2932807) B2932807
theorem B1483410295 : Blo 1736569 1483410295 := bstep (se 1 (by rfl) ⟨1112557721, by rfl⟩ : syracuseStep 1483410295 = 2225115443) B2225115443
theorem B3911507 : Blo 1736569 3911507 := bstep (se 1 (by rfl) ⟨2933630, by rfl⟩ : syracuseStep 3911507 = 5867261) B5867261
theorem B17829791 : Blo 1736569 17829791 := bstep (se 1 (by rfl) ⟨13372343, by rfl⟩ : syracuseStep 17829791 = 26744687) B26744687
theorem B13193441 : Blo 1736569 13193441 := bstep (se 2 (by rfl) ⟨4947540, by rfl⟩ : syracuseStep 13193441 = 9895081) B9895081
theorem B1954075 : Blo 1736569 1954075 := bstep (se 1 (by rfl) ⟨1465556, by rfl⟩ : syracuseStep 1954075 = 2931113) B2931113
theorem B84570743 : Blo 1736569 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B2781839 : Blo 1736569 2781839 := bstep (se 1 (by rfl) ⟨2086379, by rfl⟩ : syracuseStep 2781839 = 4172759) B4172759
theorem B1954687 : Blo 1736569 1954687 := bstep (se 1 (by rfl) ⟨1466015, by rfl⟩ : syracuseStep 1954687 = 2932031) B2932031
theorem B7418783 : Blo 1736569 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B6599789 : Blo 1736569 6599789 := bstep (se 3 (by rfl) ⟨1237460, by rfl⟩ : syracuseStep 6599789 = 2474921) B2474921
theorem B8795303 : Blo 1736569 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B10565315 : Blo 1736569 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B9893623 : Blo 1736569 9893623 := bstep (se 1 (by rfl) ⟨7420217, by rfl⟩ : syracuseStep 9893623 = 14840435) B14840435
theorem B6600959 : Blo 1736569 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B2931167 : Blo 1736569 2931167 := bstep (se 1 (by rfl) ⟨2198375, by rfl⟩ : syracuseStep 2931167 = 4396751) B4396751
theorem B4397561 : Blo 1736569 4397561 := bstep (se 2 (by rfl) ⟨1649085, by rfl⟩ : syracuseStep 4397561 = 3298171) B3298171
theorem B3300031 : Blo 1736569 3300031 := bstep (se 1 (by rfl) ⟨2475023, by rfl⟩ : syracuseStep 3300031 = 4950047) B4950047
theorem B8035355 : Blo 1736569 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B2972911 : Blo 1736569 2972911 := bstep (se 1 (by rfl) ⟨2229683, by rfl⟩ : syracuseStep 2972911 = 4459367) B4459367
theorem B2932159 : Blo 1736569 2932159 := bstep (se 1 (by rfl) ⟨2199119, by rfl⟩ : syracuseStep 2932159 = 4398239) B4398239
theorem B2605103 : Blo 1736569 2605103 := bstep (se 1 (by rfl) ⟨1953827, by rfl⟩ : syracuseStep 2605103 = 3907655) B3907655
theorem B4456585 : Blo 1736569 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B2605295 : Blo 1736569 2605295 := bstep (se 1 (by rfl) ⟨1953971, by rfl⟩ : syracuseStep 2605295 = 3907943) B3907943
theorem B2605433 : Blo 1736569 2605433 := bstep (se 2 (by rfl) ⟨977037, by rfl⟩ : syracuseStep 2605433 = 1954075) B1954075
theorem B31719869 : Blo 1736569 31719869 := bstep (se 3 (by rfl) ⟨5947475, by rfl⟩ : syracuseStep 31719869 = 11894951) B11894951
theorem B4399859 : Blo 1736569 4399859 := bstep (se 1 (by rfl) ⟨3299894, by rfl⟩ : syracuseStep 4399859 = 6599789) B6599789
theorem B2605823 : Blo 1736569 2605823 := bstep (se 1 (by rfl) ⟨1954367, by rfl⟩ : syracuseStep 2605823 = 3908735) B3908735
theorem B4400041 : Blo 1736569 4400041 := bstep (se 2 (by rfl) ⟨1650015, by rfl⟩ : syracuseStep 4400041 = 3300031) B3300031
theorem B1737663 : Blo 1736569 1737663 := bstep (se 1 (by rfl) ⟨1303247, by rfl⟩ : syracuseStep 1737663 = 2606495) B2606495
theorem B2606249 : Blo 1736569 2606249 := bstep (se 2 (by rfl) ⟨977343, by rfl⟩ : syracuseStep 2606249 = 1954687) B1954687
theorem B2606543 : Blo 1736569 2606543 := bstep (se 1 (by rfl) ⟨1954907, by rfl⟩ : syracuseStep 2606543 = 3909815) B3909815
theorem B5866991 : Blo 1736569 5866991 := bstep (se 1 (by rfl) ⟨4400243, by rfl⟩ : syracuseStep 5866991 = 8800487) B8800487
theorem B4400639 : Blo 1736569 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B2606939 : Blo 1736569 2606939 := bstep (se 1 (by rfl) ⟨1955204, by rfl⟩ : syracuseStep 2606939 = 3910409) B3910409
theorem B3909545 : Blo 1736569 3909545 := bstep (se 2 (by rfl) ⟨1466079, by rfl⟩ : syracuseStep 3909545 = 2932159) B2932159
theorem B13191497 : Blo 1736569 13191497 := bstep (se 2 (by rfl) ⟨4946811, by rfl⟩ : syracuseStep 13191497 = 9893623) B9893623
theorem B2607671 : Blo 1736569 2607671 := bstep (se 1 (by rfl) ⟨1955753, by rfl⟩ : syracuseStep 2607671 = 3911507) B3911507
theorem B56380495 : Blo 1736569 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B1854559 : Blo 1736569 1854559 := bstep (se 1 (by rfl) ⟨1390919, by rfl⟩ : syracuseStep 1854559 = 2781839) B2781839
theorem B3910751 : Blo 1736569 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B3910823 : Blo 1736569 3910823 := bstep (se 1 (by rfl) ⟨2933117, by rfl⟩ : syracuseStep 3910823 = 5866235) B5866235
theorem B1977880393 : Blo 1736569 1977880393 := bstep (se 2 (by rfl) ⟨741705147, by rfl⟩ : syracuseStep 1977880393 = 1483410295) B1483410295
theorem B1954111 : Blo 1736569 1954111 := bstep (se 1 (by rfl) ⟨1465583, by rfl⟩ : syracuseStep 1954111 = 2931167) B2931167
theorem B9900413 : Blo 1736569 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B214046063 : Blo 1736569 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B8795627 : Blo 1736569 8795627 := bstep (se 1 (by rfl) ⟨6596720, by rfl⟩ : syracuseStep 8795627 = 13193441) B13193441
theorem B35674019 : Blo 1736569 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B4945855 : Blo 1736569 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B5863535 : Blo 1736569 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B6265295 : Blo 1736569 6265295 := bstep (se 1 (by rfl) ⟨4698971, by rfl⟩ : syracuseStep 6265295 = 9397943) B9397943
theorem B7043543 : Blo 1736569 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B3963881 : Blo 1736569 3963881 := bstep (se 2 (by rfl) ⟨1486455, by rfl⟩ : syracuseStep 3963881 = 2972911) B2972911
theorem B2931707 : Blo 1736569 2931707 := bstep (se 1 (by rfl) ⟨2198780, by rfl⟩ : syracuseStep 2931707 = 4397561) B4397561
theorem B5356903 : Blo 1736569 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B120315617 : Blo 1736569 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B11886527 : Blo 1736569 11886527 := bstep (se 1 (by rfl) ⟨8914895, by rfl⟩ : syracuseStep 11886527 = 17829791) B17829791
theorem B1736735 : Blo 1736569 1736735 := bstep (se 1 (by rfl) ⟨1302551, by rfl⟩ : syracuseStep 1736735 = 2605103) B2605103
theorem B1736863 : Blo 1736569 1736863 := bstep (se 1 (by rfl) ⟨1302647, by rfl⟩ : syracuseStep 1736863 = 2605295) B2605295
theorem B1736955 : Blo 1736569 1736955 := bstep (se 1 (by rfl) ⟨1302716, by rfl⟩ : syracuseStep 1736955 = 2605433) B2605433
theorem B2605481 : Blo 1736569 2605481 := bstep (se 2 (by rfl) ⟨977055, by rfl⟩ : syracuseStep 2605481 = 1954111) B1954111
theorem B2933239 : Blo 1736569 2933239 := bstep (se 1 (by rfl) ⟨2199929, by rfl⟩ : syracuseStep 2933239 = 4399859) B4399859
theorem B1737215 : Blo 1736569 1737215 := bstep (se 1 (by rfl) ⟨1302911, by rfl⟩ : syracuseStep 1737215 = 2605823) B2605823
theorem B1737499 : Blo 1736569 1737499 := bstep (se 1 (by rfl) ⟨1303124, by rfl⟩ : syracuseStep 1737499 = 2606249) B2606249
theorem B142697375 : Blo 1736569 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B1737695 : Blo 1736569 1737695 := bstep (se 1 (by rfl) ⟨1303271, by rfl⟩ : syracuseStep 1737695 = 2606543) B2606543
theorem B2933759 : Blo 1736569 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B5866721 : Blo 1736569 5866721 := bstep (se 2 (by rfl) ⟨2200020, by rfl⟩ : syracuseStep 5866721 = 4400041) B4400041
theorem B1737959 : Blo 1736569 1737959 := bstep (se 1 (by rfl) ⟨1303469, by rfl⟩ : syracuseStep 1737959 = 2606939) B2606939
theorem B23782679 : Blo 1736569 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B2606363 : Blo 1736569 2606363 := bstep (se 1 (by rfl) ⟨1954772, by rfl⟩ : syracuseStep 2606363 = 3909545) B3909545
theorem B3909023 : Blo 1736569 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B4695695 : Blo 1736569 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B1738447 : Blo 1736569 1738447 := bstep (se 1 (by rfl) ⟨1303835, by rfl⟩ : syracuseStep 1738447 = 2607671) B2607671
theorem B2607167 : Blo 1736569 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B2607215 : Blo 1736569 2607215 := bstep (se 1 (by rfl) ⟨1955411, by rfl⟩ : syracuseStep 2607215 = 3910823) B3910823
theorem B80210411 : Blo 1736569 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B7924351 : Blo 1736569 7924351 := bstep (se 1 (by rfl) ⟨5943263, by rfl⟩ : syracuseStep 7924351 = 11886527) B11886527
theorem B21146579 : Blo 1736569 21146579 := bstep (se 1 (by rfl) ⟨15859934, by rfl⟩ : syracuseStep 21146579 = 31719869) B31719869
theorem B9890981 : Blo 1736569 9890981 := bstep (se 4 (by rfl) ⟨927279, by rfl⟩ : syracuseStep 9890981 = 1854559) B1854559
theorem B23768453 : Blo 1736569 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B3911327 : Blo 1736569 3911327 := bstep (se 1 (by rfl) ⟨2933495, by rfl⟩ : syracuseStep 3911327 = 5866991) B5866991
theorem B75173993 : Blo 1736569 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B8794331 : Blo 1736569 8794331 := bstep (se 1 (by rfl) ⟨6595748, by rfl⟩ : syracuseStep 8794331 = 13191497) B13191497
theorem B2642587 : Blo 1736569 2642587 := bstep (se 1 (by rfl) ⟨1981940, by rfl⟩ : syracuseStep 2642587 = 3963881) B3963881
theorem B1954471 : Blo 1736569 1954471 := bstep (se 1 (by rfl) ⟨1465853, by rfl⟩ : syracuseStep 1954471 = 2931707) B2931707
theorem B2637173857 : Blo 1736569 2637173857 := bstep (se 2 (by rfl) ⟨988940196, by rfl⟩ : syracuseStep 2637173857 = 1977880393) B1977880393
theorem B6600275 : Blo 1736569 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B5863751 : Blo 1736569 5863751 := bstep (se 1 (by rfl) ⟨4397813, by rfl⟩ : syracuseStep 5863751 = 8795627) B8795627
theorem B4176863 : Blo 1736569 4176863 := bstep (se 1 (by rfl) ⟨3132647, by rfl⟩ : syracuseStep 4176863 = 6265295) B6265295
theorem B7142537 : Blo 1736569 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B6594473 : Blo 1736569 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B1736987 : Blo 1736569 1736987 := bstep (se 1 (by rfl) ⟨1302740, by rfl⟩ : syracuseStep 1736987 = 2605481) B2605481
theorem B19046765 : Blo 1736569 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B1737575 : Blo 1736569 1737575 := bstep (se 1 (by rfl) ⟨1303181, by rfl⟩ : syracuseStep 1737575 = 2606363) B2606363
theorem B2605961 : Blo 1736569 2605961 := bstep (se 2 (by rfl) ⟨977235, by rfl⟩ : syracuseStep 2605961 = 1954471) B1954471
theorem B2606015 : Blo 1736569 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B4400183 : Blo 1736569 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B3130463 : Blo 1736569 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B1738111 : Blo 1736569 1738111 := bstep (se 1 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 1738111 = 2607167) B2607167
theorem B1738143 : Blo 1736569 1738143 := bstep (se 1 (by rfl) ⟨1303607, by rfl⟩ : syracuseStep 1738143 = 2607215) B2607215
theorem B3909167 : Blo 1736569 3909167 := bstep (se 1 (by rfl) ⟨2931875, by rfl⟩ : syracuseStep 3909167 = 5863751) B5863751
theorem B15845635 : Blo 1736569 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B2607551 : Blo 1736569 2607551 := bstep (se 1 (by rfl) ⟨1955663, by rfl⟩ : syracuseStep 2607551 = 3911327) B3911327
theorem B3910985 : Blo 1736569 3910985 := bstep (se 2 (by rfl) ⟨1466619, by rfl⟩ : syracuseStep 3910985 = 2933239) B2933239
theorem B3911147 : Blo 1736569 3911147 := bstep (se 1 (by rfl) ⟨2933360, by rfl⟩ : syracuseStep 3911147 = 5866721) B5866721
theorem B15855119 : Blo 1736569 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B3516231809 : Blo 1736569 3516231809 := bstep (se 2 (by rfl) ⟨1318586928, by rfl⟩ : syracuseStep 3516231809 = 2637173857) B2637173857
theorem B53473607 : Blo 1736569 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B4396315 : Blo 1736569 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B50115995 : Blo 1736569 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B5862887 : Blo 1736569 5862887 := bstep (se 1 (by rfl) ⟨4397165, by rfl⟩ : syracuseStep 5862887 = 8794331) B8794331
theorem B56375189 : Blo 1736569 56375189 := bstep (se 6 (by rfl) ⟨1321293, by rfl⟩ : syracuseStep 56375189 = 2642587) B2642587
theorem B95131583 : Blo 1736569 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B1955839 : Blo 1736569 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B10565801 : Blo 1736569 10565801 := bstep (se 2 (by rfl) ⟨3962175, by rfl⟩ : syracuseStep 10565801 = 7924351) B7924351
theorem B14097719 : Blo 1736569 14097719 := bstep (se 1 (by rfl) ⟨10573289, by rfl⟩ : syracuseStep 14097719 = 21146579) B21146579
theorem B2784575 : Blo 1736569 2784575 := bstep (se 1 (by rfl) ⟨2088431, by rfl⟩ : syracuseStep 2784575 = 4176863) B4176863
theorem B6593987 : Blo 1736569 6593987 := bstep (se 1 (by rfl) ⟨4945490, by rfl⟩ : syracuseStep 6593987 = 9890981) B9890981
theorem B12697843 : Blo 1736569 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B21127513 : Blo 1736569 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B1737307 : Blo 1736569 1737307 := bstep (se 1 (by rfl) ⟨1302980, by rfl⟩ : syracuseStep 1737307 = 2605961) B2605961
theorem B1737343 : Blo 1736569 1737343 := bstep (se 1 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 1737343 = 2606015) B2606015
theorem B2933455 : Blo 1736569 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B3908591 : Blo 1736569 3908591 := bstep (se 1 (by rfl) ⟨2931443, by rfl⟩ : syracuseStep 3908591 = 5862887) B5862887
theorem B2606111 : Blo 1736569 2606111 := bstep (se 1 (by rfl) ⟨1954583, by rfl⟩ : syracuseStep 2606111 = 3909167) B3909167
theorem B1738367 : Blo 1736569 1738367 := bstep (se 1 (by rfl) ⟨1303775, by rfl⟩ : syracuseStep 1738367 = 2607551) B2607551
theorem B9398479 : Blo 1736569 9398479 := bstep (se 1 (by rfl) ⟨7048859, by rfl⟩ : syracuseStep 9398479 = 14097719) B14097719
theorem B2607323 : Blo 1736569 2607323 := bstep (se 1 (by rfl) ⟨1955492, by rfl⟩ : syracuseStep 2607323 = 3910985) B3910985
theorem B2607431 : Blo 1736569 2607431 := bstep (se 1 (by rfl) ⟨1955573, by rfl⟩ : syracuseStep 2607431 = 3911147) B3911147
theorem B10570079 : Blo 1736569 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B2607785 : Blo 1736569 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B7425533 : Blo 1736569 7425533 := bstep (se 3 (by rfl) ⟨1392287, by rfl⟩ : syracuseStep 7425533 = 2784575) B2784575
theorem B33410663 : Blo 1736569 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B5861753 : Blo 1736569 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B4395991 : Blo 1736569 4395991 := bstep (se 1 (by rfl) ⟨3296993, by rfl⟩ : syracuseStep 4395991 = 6593987) B6593987
theorem B2344154539 : Blo 1736569 2344154539 := bstep (se 1 (by rfl) ⟨1758115904, by rfl⟩ : syracuseStep 2344154539 = 3516231809) B3516231809
theorem B35649071 : Blo 1736569 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B2086975 : Blo 1736569 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B37583459 : Blo 1736569 37583459 := bstep (se 1 (by rfl) ⟨28187594, by rfl⟩ : syracuseStep 37583459 = 56375189) B56375189
theorem B63421055 : Blo 1736569 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B7043867 : Blo 1736569 7043867 := bstep (se 1 (by rfl) ⟨5282900, by rfl⟩ : syracuseStep 7043867 = 10565801) B10565801
theorem B3907835 : Blo 1736569 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B2605727 : Blo 1736569 2605727 := bstep (se 1 (by rfl) ⟨1954295, by rfl⟩ : syracuseStep 2605727 = 3908591) B3908591
theorem B1737407 : Blo 1736569 1737407 := bstep (se 1 (by rfl) ⟨1303055, by rfl⟩ : syracuseStep 1737407 = 2606111) B2606111
theorem B23766047 : Blo 1736569 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B1738215 : Blo 1736569 1738215 := bstep (se 1 (by rfl) ⟨1303661, by rfl⟩ : syracuseStep 1738215 = 2607323) B2607323
theorem B1738287 : Blo 1736569 1738287 := bstep (se 1 (by rfl) ⟨1303715, by rfl⟩ : syracuseStep 1738287 = 2607431) B2607431
theorem B7046719 : Blo 1736569 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B42280703 : Blo 1736569 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B1738523 : Blo 1736569 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B4695911 : Blo 1736569 4695911 := bstep (se 1 (by rfl) ⟨3521933, by rfl⟩ : syracuseStep 4695911 = 7043867) B7043867
theorem B4950355 : Blo 1736569 4950355 := bstep (se 1 (by rfl) ⟨3712766, by rfl⟩ : syracuseStep 4950355 = 7425533) B7425533
theorem B3911273 : Blo 1736569 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B5861321 : Blo 1736569 5861321 := bstep (se 2 (by rfl) ⟨2197995, by rfl⟩ : syracuseStep 5861321 = 4395991) B4395991
theorem B25055639 : Blo 1736569 25055639 := bstep (se 1 (by rfl) ⟨18791729, by rfl⟩ : syracuseStep 25055639 = 37583459) B37583459
theorem B3125539385 : Blo 1736569 3125539385 := bstep (se 2 (by rfl) ⟨1172077269, by rfl⟩ : syracuseStep 3125539385 = 2344154539) B2344154539
theorem B12531305 : Blo 1736569 12531305 := bstep (se 2 (by rfl) ⟨4699239, by rfl⟩ : syracuseStep 12531305 = 9398479) B9398479
theorem B16930457 : Blo 1736569 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B11130533 : Blo 1736569 11130533 := bstep (se 4 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 11130533 = 2086975) B2086975
theorem B28170017 : Blo 1736569 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B22273775 : Blo 1736569 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B2605223 : Blo 1736569 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B16703759 : Blo 1736569 16703759 := bstep (se 1 (by rfl) ⟨12527819, by rfl⟩ : syracuseStep 16703759 = 25055639) B25055639
theorem B2083692923 : Blo 1736569 2083692923 := bstep (se 1 (by rfl) ⟨1562769692, by rfl⟩ : syracuseStep 2083692923 = 3125539385) B3125539385
theorem B1737151 : Blo 1736569 1737151 := bstep (se 1 (by rfl) ⟨1302863, by rfl⟩ : syracuseStep 1737151 = 2605727) B2605727
theorem B15844031 : Blo 1736569 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B3130607 : Blo 1736569 3130607 := bstep (se 1 (by rfl) ⟨2347955, by rfl⟩ : syracuseStep 3130607 = 4695911) B4695911
theorem B33416813 : Blo 1736569 33416813 := bstep (se 3 (by rfl) ⟨6265652, by rfl⟩ : syracuseStep 33416813 = 12531305) B12531305
theorem B2607515 : Blo 1736569 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B18780011 : Blo 1736569 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B14849183 : Blo 1736569 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B37582501 : Blo 1736569 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B6600473 : Blo 1736569 6600473 := bstep (se 2 (by rfl) ⟨2475177, by rfl⟩ : syracuseStep 6600473 = 4950355) B4950355
theorem B11286971 : Blo 1736569 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B7420355 : Blo 1736569 7420355 := bstep (se 1 (by rfl) ⟨5565266, by rfl⟩ : syracuseStep 7420355 = 11130533) B11130533
theorem B28187135 : Blo 1736569 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B3907547 : Blo 1736569 3907547 := bstep (se 1 (by rfl) ⟨2930660, by rfl⟩ : syracuseStep 3907547 = 5861321) B5861321
theorem B1736815 : Blo 1736569 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B8348285 : Blo 1736569 8348285 := bstep (se 3 (by rfl) ⟨1565303, by rfl⟩ : syracuseStep 8348285 = 3130607) B3130607
theorem B4400315 : Blo 1736569 4400315 := bstep (se 1 (by rfl) ⟨3300236, by rfl⟩ : syracuseStep 4400315 = 6600473) B6600473
theorem B1738343 : Blo 1736569 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B12520007 : Blo 1736569 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B11135839 : Blo 1736569 11135839 := bstep (se 1 (by rfl) ⟨8351879, by rfl⟩ : syracuseStep 11135839 = 16703759) B16703759
theorem B1389128615 : Blo 1736569 1389128615 := bstep (se 1 (by rfl) ⟨1041846461, by rfl⟩ : syracuseStep 1389128615 = 2083692923) B2083692923
theorem B10562687 : Blo 1736569 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B9899455 : Blo 1736569 9899455 := bstep (se 1 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 9899455 = 14849183) B14849183
theorem B22277875 : Blo 1736569 22277875 := bstep (se 1 (by rfl) ⟨16708406, by rfl⟩ : syracuseStep 22277875 = 33416813) B33416813
theorem B7524647 : Blo 1736569 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B4946903 : Blo 1736569 4946903 := bstep (se 1 (by rfl) ⟨3710177, by rfl⟩ : syracuseStep 4946903 = 7420355) B7420355
theorem B18791423 : Blo 1736569 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B50110001 : Blo 1736569 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B2605031 : Blo 1736569 2605031 := bstep (se 1 (by rfl) ⟨1953773, by rfl⟩ : syracuseStep 2605031 = 3907547) B3907547
theorem B2933543 : Blo 1736569 2933543 := bstep (se 1 (by rfl) ⟨2200157, by rfl⟩ : syracuseStep 2933543 = 4400315) B4400315
theorem B13199273 : Blo 1736569 13199273 := bstep (se 2 (by rfl) ⟨4949727, by rfl⟩ : syracuseStep 13199273 = 9899455) B9899455
theorem B12527615 : Blo 1736569 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B5016431 : Blo 1736569 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B5565523 : Blo 1736569 5565523 := bstep (se 1 (by rfl) ⟨4174142, by rfl⟩ : syracuseStep 5565523 = 8348285) B8348285
theorem B14847785 : Blo 1736569 14847785 := bstep (se 2 (by rfl) ⟨5567919, by rfl⟩ : syracuseStep 14847785 = 11135839) B11135839
theorem B926085743 : Blo 1736569 926085743 := bstep (se 1 (by rfl) ⟨694564307, by rfl⟩ : syracuseStep 926085743 = 1389128615) B1389128615
theorem B3297935 : Blo 1736569 3297935 := bstep (se 1 (by rfl) ⟨2473451, by rfl⟩ : syracuseStep 3297935 = 4946903) B4946903
theorem B7041791 : Blo 1736569 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B8346671 : Blo 1736569 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B29703833 : Blo 1736569 29703833 := bstep (se 2 (by rfl) ⟨11138937, by rfl⟩ : syracuseStep 29703833 = 22277875) B22277875
theorem B33406667 : Blo 1736569 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B1736687 : Blo 1736569 1736687 := bstep (se 1 (by rfl) ⟨1302515, by rfl⟩ : syracuseStep 1736687 = 2605031) B2605031
theorem B617390495 : Blo 1736569 617390495 := bstep (se 1 (by rfl) ⟨463042871, by rfl⟩ : syracuseStep 617390495 = 926085743) B926085743
theorem B4694527 : Blo 1736569 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B8799515 : Blo 1736569 8799515 := bstep (se 1 (by rfl) ⟨6599636, by rfl⟩ : syracuseStep 8799515 = 13199273) B13199273
theorem B5564447 : Blo 1736569 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B19802555 : Blo 1736569 19802555 := bstep (se 1 (by rfl) ⟨14851916, by rfl⟩ : syracuseStep 19802555 = 29703833) B29703833
theorem B9898523 : Blo 1736569 9898523 := bstep (se 1 (by rfl) ⟨7423892, by rfl⟩ : syracuseStep 9898523 = 14847785) B14847785
theorem B8351743 : Blo 1736569 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B8794493 : Blo 1736569 8794493 := bstep (se 3 (by rfl) ⟨1648967, by rfl⟩ : syracuseStep 8794493 = 3297935) B3297935
theorem B22271111 : Blo 1736569 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B1955695 : Blo 1736569 1955695 := bstep (se 1 (by rfl) ⟨1466771, by rfl⟩ : syracuseStep 1955695 = 2933543) B2933543
theorem B7420697 : Blo 1736569 7420697 := bstep (se 2 (by rfl) ⟨2782761, by rfl⟩ : syracuseStep 7420697 = 5565523) B5565523
theorem B13377149 : Blo 1736569 13377149 := bstep (se 3 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 13377149 = 5016431) B5016431
theorem B6259369 : Blo 1736569 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B5866343 : Blo 1736569 5866343 := bstep (se 1 (by rfl) ⟨4399757, by rfl⟩ : syracuseStep 5866343 = 8799515) B8799515
theorem B2607593 : Blo 1736569 2607593 := bstep (se 2 (by rfl) ⟨977847, by rfl⟩ : syracuseStep 2607593 = 1955695) B1955695
theorem B11135657 : Blo 1736569 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B411593663 : Blo 1736569 411593663 := bstep (se 1 (by rfl) ⟨308695247, by rfl⟩ : syracuseStep 411593663 = 617390495) B617390495
theorem B14847407 : Blo 1736569 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B13201703 : Blo 1736569 13201703 := bstep (se 1 (by rfl) ⟨9901277, by rfl⟩ : syracuseStep 13201703 = 19802555) B19802555
theorem B6599015 : Blo 1736569 6599015 := bstep (se 1 (by rfl) ⟨4949261, by rfl⟩ : syracuseStep 6599015 = 9898523) B9898523
theorem B8918099 : Blo 1736569 8918099 := bstep (se 1 (by rfl) ⟨6688574, by rfl⟩ : syracuseStep 8918099 = 13377149) B13377149
theorem B5862995 : Blo 1736569 5862995 := bstep (se 1 (by rfl) ⟨4397246, by rfl⟩ : syracuseStep 5862995 = 8794493) B8794493
theorem B3709631 : Blo 1736569 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B4947131 : Blo 1736569 4947131 := bstep (se 1 (by rfl) ⟨3710348, by rfl⟩ : syracuseStep 4947131 = 7420697) B7420697
theorem B4399343 : Blo 1736569 4399343 := bstep (se 1 (by rfl) ⟨3299507, by rfl⟩ : syracuseStep 4399343 = 6599015) B6599015
theorem B3908663 : Blo 1736569 3908663 := bstep (se 1 (by rfl) ⟨2931497, by rfl⟩ : syracuseStep 3908663 = 5862995) B5862995
theorem B1738395 : Blo 1736569 1738395 := bstep (se 1 (by rfl) ⟨1303796, by rfl⟩ : syracuseStep 1738395 = 2607593) B2607593
theorem B9898271 : Blo 1736569 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B8801135 : Blo 1736569 8801135 := bstep (se 1 (by rfl) ⟨6600851, by rfl⟩ : syracuseStep 8801135 = 13201703) B13201703
theorem B3910895 : Blo 1736569 3910895 := bstep (se 1 (by rfl) ⟨2933171, by rfl⟩ : syracuseStep 3910895 = 5866343) B5866343
theorem B274395775 : Blo 1736569 274395775 := bstep (se 1 (by rfl) ⟨205796831, by rfl⟩ : syracuseStep 274395775 = 411593663) B411593663
theorem B3298087 : Blo 1736569 3298087 := bstep (se 1 (by rfl) ⟨2473565, by rfl⟩ : syracuseStep 3298087 = 4947131) B4947131
theorem B5945399 : Blo 1736569 5945399 := bstep (se 1 (by rfl) ⟨4459049, by rfl⟩ : syracuseStep 5945399 = 8918099) B8918099
theorem B8345825 : Blo 1736569 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B29695085 : Blo 1736569 29695085 := bstep (se 3 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 29695085 = 11135657) B11135657
theorem B2473087 : Blo 1736569 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B2932895 : Blo 1736569 2932895 := bstep (se 1 (by rfl) ⟨2199671, by rfl⟩ : syracuseStep 2932895 = 4399343) B4399343
theorem B2605775 : Blo 1736569 2605775 := bstep (se 1 (by rfl) ⟨1954331, by rfl⟩ : syracuseStep 2605775 = 3908663) B3908663
theorem B5563883 : Blo 1736569 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B5867423 : Blo 1736569 5867423 := bstep (se 1 (by rfl) ⟨4400567, by rfl⟩ : syracuseStep 5867423 = 8801135) B8801135
theorem B2607263 : Blo 1736569 2607263 := bstep (se 1 (by rfl) ⟨1955447, by rfl⟩ : syracuseStep 2607263 = 3910895) B3910895
theorem B3297449 : Blo 1736569 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B6598847 : Blo 1736569 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B19796723 : Blo 1736569 19796723 := bstep (se 1 (by rfl) ⟨14847542, by rfl⟩ : syracuseStep 19796723 = 29695085) B29695085
theorem B365861033 : Blo 1736569 365861033 := bstep (se 2 (by rfl) ⟨137197887, by rfl⟩ : syracuseStep 365861033 = 274395775) B274395775
theorem B4397449 : Blo 1736569 4397449 := bstep (se 2 (by rfl) ⟨1649043, by rfl⟩ : syracuseStep 4397449 = 3298087) B3298087
theorem B3963599 : Blo 1736569 3963599 := bstep (se 1 (by rfl) ⟨2972699, by rfl⟩ : syracuseStep 3963599 = 5945399) B5945399
theorem B4399231 : Blo 1736569 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B1737183 : Blo 1736569 1737183 := bstep (se 1 (by rfl) ⟨1302887, by rfl⟩ : syracuseStep 1737183 = 2605775) B2605775
theorem B13197815 : Blo 1736569 13197815 := bstep (se 1 (by rfl) ⟨9898361, by rfl⟩ : syracuseStep 13197815 = 19796723) B19796723
theorem B1738175 : Blo 1736569 1738175 := bstep (se 1 (by rfl) ⟨1303631, by rfl⟩ : syracuseStep 1738175 = 2607263) B2607263
theorem B8793197 : Blo 1736569 8793197 := bstep (se 3 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 8793197 = 3297449) B3297449
theorem B3911615 : Blo 1736569 3911615 := bstep (se 1 (by rfl) ⟨2933711, by rfl⟩ : syracuseStep 3911615 = 5867423) B5867423
theorem B2642399 : Blo 1736569 2642399 := bstep (se 1 (by rfl) ⟨1981799, by rfl⟩ : syracuseStep 2642399 = 3963599) B3963599
theorem B1955263 : Blo 1736569 1955263 := bstep (se 1 (by rfl) ⟨1466447, by rfl⟩ : syracuseStep 1955263 = 2932895) B2932895
theorem B5863265 : Blo 1736569 5863265 := bstep (se 2 (by rfl) ⟨2198724, by rfl⟩ : syracuseStep 5863265 = 4397449) B4397449
theorem B3709255 : Blo 1736569 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B243907355 : Blo 1736569 243907355 := bstep (se 1 (by rfl) ⟨182930516, by rfl⟩ : syracuseStep 243907355 = 365861033) B365861033
theorem B5865641 : Blo 1736569 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B1761599 : Blo 1736569 1761599 := bstep (se 1 (by rfl) ⟨1321199, by rfl⟩ : syracuseStep 1761599 = 2642399) B2642399
theorem B8798543 : Blo 1736569 8798543 := bstep (se 1 (by rfl) ⟨6598907, by rfl⟩ : syracuseStep 8798543 = 13197815) B13197815
theorem B3908843 : Blo 1736569 3908843 := bstep (se 1 (by rfl) ⟨2931632, by rfl⟩ : syracuseStep 3908843 = 5863265) B5863265
theorem B162604903 : Blo 1736569 162604903 := bstep (se 1 (by rfl) ⟨121953677, by rfl⟩ : syracuseStep 162604903 = 243907355) B243907355
theorem B2607017 : Blo 1736569 2607017 := bstep (se 2 (by rfl) ⟨977631, by rfl⟩ : syracuseStep 2607017 = 1955263) B1955263
theorem B2607743 : Blo 1736569 2607743 := bstep (se 1 (by rfl) ⟨1955807, by rfl⟩ : syracuseStep 2607743 = 3911615) B3911615
theorem B5862131 : Blo 1736569 5862131 := bstep (se 1 (by rfl) ⟨4396598, by rfl⟩ : syracuseStep 5862131 = 8793197) B8793197
theorem B4945673 : Blo 1736569 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B5865695 : Blo 1736569 5865695 := bstep (se 1 (by rfl) ⟨4399271, by rfl⟩ : syracuseStep 5865695 = 8798543) B8798543
theorem B3908087 : Blo 1736569 3908087 := bstep (se 1 (by rfl) ⟨2931065, by rfl⟩ : syracuseStep 3908087 = 5862131) B5862131
theorem B2605895 : Blo 1736569 2605895 := bstep (se 1 (by rfl) ⟨1954421, by rfl⟩ : syracuseStep 2605895 = 3908843) B3908843
theorem B1738011 : Blo 1736569 1738011 := bstep (se 1 (by rfl) ⟨1303508, by rfl⟩ : syracuseStep 1738011 = 2607017) B2607017
theorem B1738495 : Blo 1736569 1738495 := bstep (se 1 (by rfl) ⟨1303871, by rfl⟩ : syracuseStep 1738495 = 2607743) B2607743
theorem B3910427 : Blo 1736569 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B4697597 : Blo 1736569 4697597 := bstep (se 3 (by rfl) ⟨880799, by rfl⟩ : syracuseStep 4697597 = 1761599) B1761599
theorem B3297115 : Blo 1736569 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B216806537 : Blo 1736569 216806537 := bstep (se 2 (by rfl) ⟨81302451, by rfl⟩ : syracuseStep 216806537 = 162604903) B162604903
theorem B2605391 : Blo 1736569 2605391 := bstep (se 1 (by rfl) ⟨1954043, by rfl⟩ : syracuseStep 2605391 = 3908087) B3908087
theorem B1737263 : Blo 1736569 1737263 := bstep (se 1 (by rfl) ⟨1302947, by rfl⟩ : syracuseStep 1737263 = 2605895) B2605895
theorem B2606951 : Blo 1736569 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B3131731 : Blo 1736569 3131731 := bstep (se 1 (by rfl) ⟨2348798, by rfl⟩ : syracuseStep 3131731 = 4697597) B4697597
theorem B3910463 : Blo 1736569 3910463 := bstep (se 1 (by rfl) ⟨2932847, by rfl⟩ : syracuseStep 3910463 = 5865695) B5865695
theorem B4396153 : Blo 1736569 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B144537691 : Blo 1736569 144537691 := bstep (se 1 (by rfl) ⟨108403268, by rfl⟩ : syracuseStep 144537691 = 216806537) B216806537
theorem B192716921 : Blo 1736569 192716921 := bstep (se 2 (by rfl) ⟨72268845, by rfl⟩ : syracuseStep 192716921 = 144537691) B144537691
theorem B1736927 : Blo 1736569 1736927 := bstep (se 1 (by rfl) ⟨1302695, by rfl⟩ : syracuseStep 1736927 = 2605391) B2605391
theorem B1737967 : Blo 1736569 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B2606975 : Blo 1736569 2606975 := bstep (se 1 (by rfl) ⟨1955231, by rfl⟩ : syracuseStep 2606975 = 3910463) B3910463
theorem B5861537 : Blo 1736569 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B4175641 : Blo 1736569 4175641 := bstep (se 2 (by rfl) ⟨1565865, by rfl⟩ : syracuseStep 4175641 = 3131731) B3131731
theorem B3907691 : Blo 1736569 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B1737983 : Blo 1736569 1737983 := bstep (se 1 (by rfl) ⟨1303487, by rfl⟩ : syracuseStep 1737983 = 2606975) B2606975
theorem B128477947 : Blo 1736569 128477947 := bstep (se 1 (by rfl) ⟨96358460, by rfl⟩ : syracuseStep 128477947 = 192716921) B192716921
theorem B22270085 : Blo 1736569 22270085 := bstep (se 4 (by rfl) ⟨2087820, by rfl⟩ : syracuseStep 22270085 = 4175641) B4175641
theorem B2605127 : Blo 1736569 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B171303929 : Blo 1736569 171303929 := bstep (se 2 (by rfl) ⟨64238973, by rfl⟩ : syracuseStep 171303929 = 128477947) B128477947
theorem B14846723 : Blo 1736569 14846723 := bstep (se 1 (by rfl) ⟨11135042, by rfl⟩ : syracuseStep 14846723 = 22270085) B22270085
theorem B1736751 : Blo 1736569 1736751 := bstep (se 1 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 1736751 = 2605127) B2605127
theorem B9897815 : Blo 1736569 9897815 := bstep (se 1 (by rfl) ⟨7423361, by rfl⟩ : syracuseStep 9897815 = 14846723) B14846723
theorem B114202619 : Blo 1736569 114202619 := bstep (se 1 (by rfl) ⟨85651964, by rfl⟩ : syracuseStep 114202619 = 171303929) B171303929
theorem B6598543 : Blo 1736569 6598543 := bstep (se 1 (by rfl) ⟨4948907, by rfl⟩ : syracuseStep 6598543 = 9897815) B9897815
theorem B76135079 : Blo 1736569 76135079 := bstep (se 1 (by rfl) ⟨57101309, by rfl⟩ : syracuseStep 76135079 = 114202619) B114202619
theorem B203026877 : Blo 1736569 203026877 := bstep (se 3 (by rfl) ⟨38067539, by rfl⟩ : syracuseStep 203026877 = 76135079) B76135079
theorem B8798057 : Blo 1736569 8798057 := bstep (se 2 (by rfl) ⟨3299271, by rfl⟩ : syracuseStep 8798057 = 6598543) B6598543
theorem B135351251 : Blo 1736569 135351251 := bstep (se 1 (by rfl) ⟨101513438, by rfl⟩ : syracuseStep 135351251 = 203026877) B203026877
theorem B5865371 : Blo 1736569 5865371 := bstep (se 1 (by rfl) ⟨4399028, by rfl⟩ : syracuseStep 5865371 = 8798057) B8798057
theorem B3910247 : Blo 1736569 3910247 := bstep (se 1 (by rfl) ⟨2932685, by rfl⟩ : syracuseStep 3910247 = 5865371) B5865371
theorem B90234167 : Blo 1736569 90234167 := bstep (se 1 (by rfl) ⟨67675625, by rfl⟩ : syracuseStep 90234167 = 135351251) B135351251
theorem B240624445 : Blo 1736569 240624445 := bstep (se 3 (by rfl) ⟨45117083, by rfl⟩ : syracuseStep 240624445 = 90234167) B90234167
theorem B2606831 : Blo 1736569 2606831 := bstep (se 1 (by rfl) ⟨1955123, by rfl⟩ : syracuseStep 2606831 = 3910247) B3910247
theorem B320832593 : Blo 1736569 320832593 := bstep (se 2 (by rfl) ⟨120312222, by rfl⟩ : syracuseStep 320832593 = 240624445) B240624445
theorem B1737887 : Blo 1736569 1737887 := bstep (se 1 (by rfl) ⟨1303415, by rfl⟩ : syracuseStep 1737887 = 2606831) B2606831
theorem B213888395 : Blo 1736569 213888395 := bstep (se 1 (by rfl) ⟨160416296, by rfl⟩ : syracuseStep 213888395 = 320832593) B320832593
theorem B570369053 : Blo 1736569 570369053 := bstep (se 3 (by rfl) ⟨106944197, by rfl⟩ : syracuseStep 570369053 = 213888395) B213888395
theorem B380246035 : Blo 1736569 380246035 := bstep (se 1 (by rfl) ⟨285184526, by rfl⟩ : syracuseStep 380246035 = 570369053) B570369053
theorem B506994713 : Blo 1736569 506994713 := bstep (se 2 (by rfl) ⟨190123017, by rfl⟩ : syracuseStep 506994713 = 380246035) B380246035
theorem B337996475 : Blo 1736569 337996475 := bstep (se 1 (by rfl) ⟨253497356, by rfl⟩ : syracuseStep 337996475 = 506994713) B506994713
theorem B225330983 : Blo 1736569 225330983 := bstep (se 1 (by rfl) ⟨168998237, by rfl⟩ : syracuseStep 225330983 = 337996475) B337996475
theorem B150220655 : Blo 1736569 150220655 := bstep (se 1 (by rfl) ⟨112665491, by rfl⟩ : syracuseStep 150220655 = 225330983) B225330983
theorem B100147103 : Blo 1736569 100147103 := bstep (se 1 (by rfl) ⟨75110327, by rfl⟩ : syracuseStep 100147103 = 150220655) B150220655
theorem B66764735 : Blo 1736569 66764735 := bstep (se 1 (by rfl) ⟨50073551, by rfl⟩ : syracuseStep 66764735 = 100147103) B100147103
theorem B44509823 : Blo 1736569 44509823 := bstep (se 1 (by rfl) ⟨33382367, by rfl⟩ : syracuseStep 44509823 = 66764735) B66764735
theorem B29673215 : Blo 1736569 29673215 := bstep (se 1 (by rfl) ⟨22254911, by rfl⟩ : syracuseStep 29673215 = 44509823) B44509823
theorem B19782143 : Blo 1736569 19782143 := bstep (se 1 (by rfl) ⟨14836607, by rfl⟩ : syracuseStep 19782143 = 29673215) B29673215
theorem B13188095 : Blo 1736569 13188095 := bstep (se 1 (by rfl) ⟨9891071, by rfl⟩ : syracuseStep 13188095 = 19782143) B19782143
theorem B8792063 : Blo 1736569 8792063 := bstep (se 1 (by rfl) ⟨6594047, by rfl⟩ : syracuseStep 8792063 = 13188095) B13188095
theorem B5861375 : Blo 1736569 5861375 := bstep (se 1 (by rfl) ⟨4396031, by rfl⟩ : syracuseStep 5861375 = 8792063) B8792063
theorem B3907583 : Blo 1736569 3907583 := bstep (se 1 (by rfl) ⟨2930687, by rfl⟩ : syracuseStep 3907583 = 5861375) B5861375
theorem B2605055 : Blo 1736569 2605055 := bstep (se 1 (by rfl) ⟨1953791, by rfl⟩ : syracuseStep 2605055 = 3907583) B3907583
theorem B1736703 : Blo 1736569 1736703 := bstep (se 1 (by rfl) ⟨1302527, by rfl⟩ : syracuseStep 1736703 = 2605055) B2605055

theorem C0 (j : ℕ) (h1 : 434142 ≤ j) (h2 : j ≤ 434641) : Blo 1736569 (4 * j + 3) := by
  interval_cases j
  · exact B1736571
  · exact B1736575
  · exact B1736579
  · exact B1736583
  · exact B1736587
  · exact B1736591
  · exact B1736595
  · exact B1736599
  · exact B1736603
  · exact B1736607
  · exact B1736611
  · exact B1736615
  · exact B1736619
  · exact B1736623
  · exact B1736627
  · exact B1736631
  · exact B1736635
  · exact B1736639
  · exact B1736643
  · exact B1736647
  · exact B1736651
  · exact B1736655
  · exact B1736659
  · exact B1736663
  · exact B1736667
  · exact B1736671
  · exact B1736675
  · exact B1736679
  · exact B1736683
  · exact B1736687
  · exact B1736691
  · exact B1736695
  · exact B1736699
  · exact B1736703
  · exact B1736707
  · exact B1736711
  · exact B1736715
  · exact B1736719
  · exact B1736723
  · exact B1736727
  · exact B1736731
  · exact B1736735
  · exact B1736739
  · exact B1736743
  · exact B1736747
  · exact B1736751
  · exact B1736755
  · exact B1736759
  · exact B1736763
  · exact B1736767
  · exact B1736771
  · exact B1736775
  · exact B1736779
  · exact B1736783
  · exact B1736787
  · exact B1736791
  · exact B1736795
  · exact B1736799
  · exact B1736803
  · exact B1736807
  · exact B1736811
  · exact B1736815
  · exact B1736819
  · exact B1736823
  · exact B1736827
  · exact B1736831
  · exact B1736835
  · exact B1736839
  · exact B1736843
  · exact B1736847
  · exact B1736851
  · exact B1736855
  · exact B1736859
  · exact B1736863
  · exact B1736867
  · exact B1736871
  · exact B1736875
  · exact B1736879
  · exact B1736883
  · exact B1736887
  · exact B1736891
  · exact B1736895
  · exact B1736899
  · exact B1736903
  · exact B1736907
  · exact B1736911
  · exact B1736915
  · exact B1736919
  · exact B1736923
  · exact B1736927
  · exact B1736931
  · exact B1736935
  · exact B1736939
  · exact B1736943
  · exact B1736947
  · exact B1736951
  · exact B1736955
  · exact B1736959
  · exact B1736963
  · exact B1736967
  · exact B1736971
  · exact B1736975
  · exact B1736979
  · exact B1736983
  · exact B1736987
  · exact B1736991
  · exact B1736995
  · exact B1736999
  · exact B1737003
  · exact B1737007
  · exact B1737011
  · exact B1737015
  · exact B1737019
  · exact B1737023
  · exact B1737027
  · exact B1737031
  · exact B1737035
  · exact B1737039
  · exact B1737043
  · exact B1737047
  · exact B1737051
  · exact B1737055
  · exact B1737059
  · exact B1737063
  · exact B1737067
  · exact B1737071
  · exact B1737075
  · exact B1737079
  · exact B1737083
  · exact B1737087
  · exact B1737091
  · exact B1737095
  · exact B1737099
  · exact B1737103
  · exact B1737107
  · exact B1737111
  · exact B1737115
  · exact B1737119
  · exact B1737123
  · exact B1737127
  · exact B1737131
  · exact B1737135
  · exact B1737139
  · exact B1737143
  · exact B1737147
  · exact B1737151
  · exact B1737155
  · exact B1737159
  · exact B1737163
  · exact B1737167
  · exact B1737171
  · exact B1737175
  · exact B1737179
  · exact B1737183
  · exact B1737187
  · exact B1737191
  · exact B1737195
  · exact B1737199
  · exact B1737203
  · exact B1737207
  · exact B1737211
  · exact B1737215
  · exact B1737219
  · exact B1737223
  · exact B1737227
  · exact B1737231
  · exact B1737235
  · exact B1737239
  · exact B1737243
  · exact B1737247
  · exact B1737251
  · exact B1737255
  · exact B1737259
  · exact B1737263
  · exact B1737267
  · exact B1737271
  · exact B1737275
  · exact B1737279
  · exact B1737283
  · exact B1737287
  · exact B1737291
  · exact B1737295
  · exact B1737299
  · exact B1737303
  · exact B1737307
  · exact B1737311
  · exact B1737315
  · exact B1737319
  · exact B1737323
  · exact B1737327
  · exact B1737331
  · exact B1737335
  · exact B1737339
  · exact B1737343
  · exact B1737347
  · exact B1737351
  · exact B1737355
  · exact B1737359
  · exact B1737363
  · exact B1737367
  · exact B1737371
  · exact B1737375
  · exact B1737379
  · exact B1737383
  · exact B1737387
  · exact B1737391
  · exact B1737395
  · exact B1737399
  · exact B1737403
  · exact B1737407
  · exact B1737411
  · exact B1737415
  · exact B1737419
  · exact B1737423
  · exact B1737427
  · exact B1737431
  · exact B1737435
  · exact B1737439
  · exact B1737443
  · exact B1737447
  · exact B1737451
  · exact B1737455
  · exact B1737459
  · exact B1737463
  · exact B1737467
  · exact B1737471
  · exact B1737475
  · exact B1737479
  · exact B1737483
  · exact B1737487
  · exact B1737491
  · exact B1737495
  · exact B1737499
  · exact B1737503
  · exact B1737507
  · exact B1737511
  · exact B1737515
  · exact B1737519
  · exact B1737523
  · exact B1737527
  · exact B1737531
  · exact B1737535
  · exact B1737539
  · exact B1737543
  · exact B1737547
  · exact B1737551
  · exact B1737555
  · exact B1737559
  · exact B1737563
  · exact B1737567
  · exact B1737571
  · exact B1737575
  · exact B1737579
  · exact B1737583
  · exact B1737587
  · exact B1737591
  · exact B1737595
  · exact B1737599
  · exact B1737603
  · exact B1737607
  · exact B1737611
  · exact B1737615
  · exact B1737619
  · exact B1737623
  · exact B1737627
  · exact B1737631
  · exact B1737635
  · exact B1737639
  · exact B1737643
  · exact B1737647
  · exact B1737651
  · exact B1737655
  · exact B1737659
  · exact B1737663
  · exact B1737667
  · exact B1737671
  · exact B1737675
  · exact B1737679
  · exact B1737683
  · exact B1737687
  · exact B1737691
  · exact B1737695
  · exact B1737699
  · exact B1737703
  · exact B1737707
  · exact B1737711
  · exact B1737715
  · exact B1737719
  · exact B1737723
  · exact B1737727
  · exact B1737731
  · exact B1737735
  · exact B1737739
  · exact B1737743
  · exact B1737747
  · exact B1737751
  · exact B1737755
  · exact B1737759
  · exact B1737763
  · exact B1737767
  · exact B1737771
  · exact B1737775
  · exact B1737779
  · exact B1737783
  · exact B1737787
  · exact B1737791
  · exact B1737795
  · exact B1737799
  · exact B1737803
  · exact B1737807
  · exact B1737811
  · exact B1737815
  · exact B1737819
  · exact B1737823
  · exact B1737827
  · exact B1737831
  · exact B1737835
  · exact B1737839
  · exact B1737843
  · exact B1737847
  · exact B1737851
  · exact B1737855
  · exact B1737859
  · exact B1737863
  · exact B1737867
  · exact B1737871
  · exact B1737875
  · exact B1737879
  · exact B1737883
  · exact B1737887
  · exact B1737891
  · exact B1737895
  · exact B1737899
  · exact B1737903
  · exact B1737907
  · exact B1737911
  · exact B1737915
  · exact B1737919
  · exact B1737923
  · exact B1737927
  · exact B1737931
  · exact B1737935
  · exact B1737939
  · exact B1737943
  · exact B1737947
  · exact B1737951
  · exact B1737955
  · exact B1737959
  · exact B1737963
  · exact B1737967
  · exact B1737971
  · exact B1737975
  · exact B1737979
  · exact B1737983
  · exact B1737987
  · exact B1737991
  · exact B1737995
  · exact B1737999
  · exact B1738003
  · exact B1738007
  · exact B1738011
  · exact B1738015
  · exact B1738019
  · exact B1738023
  · exact B1738027
  · exact B1738031
  · exact B1738035
  · exact B1738039
  · exact B1738043
  · exact B1738047
  · exact B1738051
  · exact B1738055
  · exact B1738059
  · exact B1738063
  · exact B1738067
  · exact B1738071
  · exact B1738075
  · exact B1738079
  · exact B1738083
  · exact B1738087
  · exact B1738091
  · exact B1738095
  · exact B1738099
  · exact B1738103
  · exact B1738107
  · exact B1738111
  · exact B1738115
  · exact B1738119
  · exact B1738123
  · exact B1738127
  · exact B1738131
  · exact B1738135
  · exact B1738139
  · exact B1738143
  · exact B1738147
  · exact B1738151
  · exact B1738155
  · exact B1738159
  · exact B1738163
  · exact B1738167
  · exact B1738171
  · exact B1738175
  · exact B1738179
  · exact B1738183
  · exact B1738187
  · exact B1738191
  · exact B1738195
  · exact B1738199
  · exact B1738203
  · exact B1738207
  · exact B1738211
  · exact B1738215
  · exact B1738219
  · exact B1738223
  · exact B1738227
  · exact B1738231
  · exact B1738235
  · exact B1738239
  · exact B1738243
  · exact B1738247
  · exact B1738251
  · exact B1738255
  · exact B1738259
  · exact B1738263
  · exact B1738267
  · exact B1738271
  · exact B1738275
  · exact B1738279
  · exact B1738283
  · exact B1738287
  · exact B1738291
  · exact B1738295
  · exact B1738299
  · exact B1738303
  · exact B1738307
  · exact B1738311
  · exact B1738315
  · exact B1738319
  · exact B1738323
  · exact B1738327
  · exact B1738331
  · exact B1738335
  · exact B1738339
  · exact B1738343
  · exact B1738347
  · exact B1738351
  · exact B1738355
  · exact B1738359
  · exact B1738363
  · exact B1738367
  · exact B1738371
  · exact B1738375
  · exact B1738379
  · exact B1738383
  · exact B1738387
  · exact B1738391
  · exact B1738395
  · exact B1738399
  · exact B1738403
  · exact B1738407
  · exact B1738411
  · exact B1738415
  · exact B1738419
  · exact B1738423
  · exact B1738427
  · exact B1738431
  · exact B1738435
  · exact B1738439
  · exact B1738443
  · exact B1738447
  · exact B1738451
  · exact B1738455
  · exact B1738459
  · exact B1738463
  · exact B1738467
  · exact B1738471
  · exact B1738475
  · exact B1738479
  · exact B1738483
  · exact B1738487
  · exact B1738491
  · exact B1738495
  · exact B1738499
  · exact B1738503
  · exact B1738507
  · exact B1738511
  · exact B1738515
  · exact B1738519
  · exact B1738523
  · exact B1738527
  · exact B1738531
  · exact B1738535
  · exact B1738539
  · exact B1738543
  · exact B1738547
  · exact B1738551
  · exact B1738555
  · exact B1738559
  · exact B1738563
  · exact B1738567

theorem solution (m : ℕ) (hlo : 1736569 ≤ m) (hhi : m ≤ 1738569) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 434142 ≤ j := by omega
    have hj2 : j ≤ 434641 := by omega
    have hb : Blo 1736569 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
