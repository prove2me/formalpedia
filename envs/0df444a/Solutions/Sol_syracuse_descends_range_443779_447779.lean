-- Prove2me | solution 1 for syracuse_descends_range_443779_447779
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:57.368391+00:00
-- url     : https://prove2.me/submissions/193060c5-c253-4334-84fb-3d65ab859078

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


theorem B753725 : Blo 443779 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B1802341 : Blo 443779 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B1900709 : Blo 443779 1900709 := bbase (se 4 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 1900709 = 356383) (by norm_num)
theorem B753853 : Blo 443779 753853 := bbase (se 3 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 753853 = 282695) (by norm_num)
theorem B1147085 : Blo 443779 1147085 := bbase (se 3 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 1147085 = 430157) (by norm_num)
theorem B753941 : Blo 443779 753941 := bbase (se 6 (by rfl) ⟨17670, by rfl⟩ : syracuseStep 753941 = 35341) (by norm_num)
theorem B688493 : Blo 443779 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B1507733 : Blo 443779 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B754069 : Blo 443779 754069 := bbase (se 6 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 754069 = 35347) (by norm_num)
theorem B688589 : Blo 443779 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B557533 : Blo 443779 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B754157 : Blo 443779 754157 := bbase (se 3 (by rfl) ⟨141404, by rfl⟩ : syracuseStep 754157 = 282809) (by norm_num)
theorem B754285 : Blo 443779 754285 := bbase (se 3 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 754285 = 282857) (by norm_num)
theorem B754373 : Blo 443779 754373 := bbase (se 4 (by rfl) ⟨70722, by rfl⟩ : syracuseStep 754373 = 141445) (by norm_num)
theorem B1508165 : Blo 443779 1508165 := bbase (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) (by norm_num)
theorem B754501 : Blo 443779 754501 := bbase (se 4 (by rfl) ⟨70734, by rfl⟩ : syracuseStep 754501 = 141469) (by norm_num)
theorem B1835909 : Blo 443779 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B1606549 : Blo 443779 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B754589 : Blo 443779 754589 := bbase (se 3 (by rfl) ⟨141485, by rfl⟩ : syracuseStep 754589 = 282971) (by norm_num)
theorem B951277 : Blo 443779 951277 := bbase (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) (by norm_num)
theorem B2262005 : Blo 443779 2262005 := bbase (se 5 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 2262005 = 212063) (by norm_num)
theorem B754717 : Blo 443779 754717 := bbase (se 3 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 754717 = 283019) (by norm_num)
theorem B754805 : Blo 443779 754805 := bbase (se 5 (by rfl) ⟨35381, by rfl⟩ : syracuseStep 754805 = 70763) (by norm_num)
theorem B722117 : Blo 443779 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B1508597 : Blo 443779 1508597 := bbase (se 5 (by rfl) ⟨70715, by rfl⟩ : syracuseStep 1508597 = 141431) (by norm_num)
theorem B754933 : Blo 443779 754933 := bbase (se 5 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 754933 = 70775) (by norm_num)
theorem B1017157 : Blo 443779 1017157 := bbase (se 4 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 1017157 = 190717) (by norm_num)
theorem B755021 : Blo 443779 755021 := bbase (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) (by norm_num)
theorem B755149 : Blo 443779 755149 := bbase (se 3 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 755149 = 283181) (by norm_num)
theorem B755237 : Blo 443779 755237 := bbase (se 4 (by rfl) ⟨70803, by rfl⟩ : syracuseStep 755237 = 141607) (by norm_num)
theorem B1509029 : Blo 443779 1509029 := bbase (se 4 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 1509029 = 282943) (by norm_num)
theorem B755365 : Blo 443779 755365 := bbase (se 4 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 755365 = 141631) (by norm_num)
theorem B755453 : Blo 443779 755453 := bbase (se 3 (by rfl) ⟨141647, by rfl⟩ : syracuseStep 755453 = 283295) (by norm_num)
theorem B952165 : Blo 443779 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B755581 : Blo 443779 755581 := bbase (se 3 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 755581 = 283343) (by norm_num)
theorem B1509461 : Blo 443779 1509461 := bbase (se 8 (by rfl) ⟨8844, by rfl⟩ : syracuseStep 1509461 = 17689) (by norm_num)
theorem B919757 : Blo 443779 919757 := bbase (se 3 (by rfl) ⟨172454, by rfl⟩ : syracuseStep 919757 = 344909) (by norm_num)
theorem B2263301 : Blo 443779 2263301 := bbase (se 4 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 2263301 = 424369) (by norm_num)
theorem B952661 : Blo 443779 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B1018325 : Blo 443779 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B1509893 : Blo 443779 1509893 := bbase (se 4 (by rfl) ⟨141552, by rfl⟩ : syracuseStep 1509893 = 283105) (by norm_num)
theorem B1510325 : Blo 443779 1510325 := bbase (se 5 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 1510325 = 141593) (by norm_num)
theorem B723973 : Blo 443779 723973 := bbase (se 4 (by rfl) ⟨67872, by rfl⟩ : syracuseStep 723973 = 135745) (by norm_num)
theorem B5704789 : Blo 443779 5704789 := bbase (se 8 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 5704789 = 66853) (by norm_num)
theorem B953525 : Blo 443779 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B953669 : Blo 443779 953669 := bbase (se 4 (by rfl) ⟨89406, by rfl⟩ : syracuseStep 953669 = 178813) (by norm_num)
theorem B1510757 : Blo 443779 1510757 := bbase (se 4 (by rfl) ⟨141633, by rfl⟩ : syracuseStep 1510757 = 283267) (by norm_num)
theorem B2264597 : Blo 443779 2264597 := bbase (se 6 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 2264597 = 106153) (by norm_num)
theorem B1511189 : Blo 443779 1511189 := bbase (se 6 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 1511189 = 70837) (by norm_num)
theorem B3379157 : Blo 443779 3379157 := bbase (se 7 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 3379157 = 79199) (by norm_num)
theorem B954413 : Blo 443779 954413 := bbase (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) (by norm_num)
theorem B1904741 : Blo 443779 1904741 := bbase (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) (by norm_num)
theorem B6426773 : Blo 443779 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B1020077 : Blo 443779 1020077 := bbase (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) (by norm_num)
theorem B4297045 : Blo 443779 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B1217045 : Blo 443779 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B561745 : Blo 443779 561745 := bbase (se 2 (by rfl) ⟨210654, by rfl⟩ : syracuseStep 561745 = 421309) (by norm_num)
theorem B725701 : Blo 443779 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B561917 : Blo 443779 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B955165 : Blo 443779 955165 := bbase (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) (by norm_num)
theorem B2265893 : Blo 443779 2265893 := bbase (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) (by norm_num)
theorem B561973 : Blo 443779 561973 := bbase (se 5 (by rfl) ⟨26342, by rfl⟩ : syracuseStep 561973 = 52685) (by norm_num)
theorem B562069 : Blo 443779 562069 := bbase (se 6 (by rfl) ⟨13173, by rfl⟩ : syracuseStep 562069 = 26347) (by norm_num)
theorem B955309 : Blo 443779 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B726013 : Blo 443779 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B3052565 : Blo 443779 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B562241 : Blo 443779 562241 := bbase (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) (by norm_num)
theorem B562297 : Blo 443779 562297 := bbase (se 2 (by rfl) ⟨210861, by rfl⟩ : syracuseStep 562297 = 421723) (by norm_num)
theorem B1021133 : Blo 443779 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B562393 : Blo 443779 562393 := bbase (se 2 (by rfl) ⟨210897, by rfl⟩ : syracuseStep 562393 = 421795) (by norm_num)
theorem B955685 : Blo 443779 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B1709429 : Blo 443779 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B562565 : Blo 443779 562565 := bbase (se 4 (by rfl) ⟨52740, by rfl⟩ : syracuseStep 562565 = 105481) (by norm_num)
theorem B562621 : Blo 443779 562621 := bbase (se 3 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 562621 = 210983) (by norm_num)
theorem B562717 : Blo 443779 562717 := bbase (se 3 (by rfl) ⟨105509, by rfl⟩ : syracuseStep 562717 = 211019) (by norm_num)
theorem B1087013 : Blo 443779 1087013 := bbase (se 4 (by rfl) ⟨101907, by rfl⟩ : syracuseStep 1087013 = 203815) (by norm_num)
theorem B956053 : Blo 443779 956053 := bbase (se 6 (by rfl) ⟨22407, by rfl⟩ : syracuseStep 956053 = 44815) (by norm_num)
theorem B562889 : Blo 443779 562889 := bbase (se 2 (by rfl) ⟨211083, by rfl⟩ : syracuseStep 562889 = 422167) (by norm_num)
theorem B562945 : Blo 443779 562945 := bbase (se 2 (by rfl) ⟨211104, by rfl⟩ : syracuseStep 562945 = 422209) (by norm_num)
theorem B1906517 : Blo 443779 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B563041 : Blo 443779 563041 := bbase (se 2 (by rfl) ⟨211140, by rfl⟩ : syracuseStep 563041 = 422281) (by norm_num)
theorem B2037653 : Blo 443779 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B563213 : Blo 443779 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B563269 : Blo 443779 563269 := bbase (se 4 (by rfl) ⟨52806, by rfl⟩ : syracuseStep 563269 = 105613) (by norm_num)
theorem B563365 : Blo 443779 563365 := bbase (se 4 (by rfl) ⟨52815, by rfl⟩ : syracuseStep 563365 = 105631) (by norm_num)
theorem B563537 : Blo 443779 563537 := bbase (se 2 (by rfl) ⟨211326, by rfl⟩ : syracuseStep 563537 = 422653) (by norm_num)
theorem B563593 : Blo 443779 563593 := bbase (se 2 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 563593 = 422695) (by norm_num)
theorem B1612229 : Blo 443779 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B563689 : Blo 443779 563689 := bbase (se 2 (by rfl) ⟨211383, by rfl⟩ : syracuseStep 563689 = 422767) (by norm_num)
theorem B563861 : Blo 443779 563861 := bbase (se 6 (by rfl) ⟨13215, by rfl⟩ : syracuseStep 563861 = 26431) (by norm_num)
theorem B563917 : Blo 443779 563917 := bbase (se 3 (by rfl) ⟨105734, by rfl⟩ : syracuseStep 563917 = 211469) (by norm_num)
theorem B564013 : Blo 443779 564013 := bbase (se 3 (by rfl) ⟨105752, by rfl⟩ : syracuseStep 564013 = 211505) (by norm_num)
theorem B1907509 : Blo 443779 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B1809317 : Blo 443779 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B564185 : Blo 443779 564185 := bbase (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) (by norm_num)
theorem B695285 : Blo 443779 695285 := bbase (se 5 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 695285 = 65183) (by norm_num)
theorem B564241 : Blo 443779 564241 := bbase (se 2 (by rfl) ⟨211590, by rfl⟩ : syracuseStep 564241 = 423181) (by norm_num)
theorem B564337 : Blo 443779 564337 := bbase (se 2 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 564337 = 423253) (by norm_num)
theorem B1055861 : Blo 443779 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B564509 : Blo 443779 564509 := bbase (se 3 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 564509 = 211691) (by norm_num)
theorem B564565 : Blo 443779 564565 := bbase (se 11 (by rfl) ⟨413, by rfl⟩ : syracuseStep 564565 = 827) (by norm_num)
theorem B564661 : Blo 443779 564661 := bbase (se 5 (by rfl) ⟨26468, by rfl⟩ : syracuseStep 564661 = 52937) (by norm_num)
theorem B2137589 : Blo 443779 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B499261 : Blo 443779 499261 := bbase (se 3 (by rfl) ⟨93611, by rfl⟩ : syracuseStep 499261 = 187223) (by norm_num)
theorem B499297 : Blo 443779 499297 := bbase (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) (by norm_num)
theorem B564833 : Blo 443779 564833 := bbase (se 2 (by rfl) ⟨211812, by rfl⟩ : syracuseStep 564833 = 423625) (by norm_num)
theorem B499333 : Blo 443779 499333 := bbase (se 4 (by rfl) ⟨46812, by rfl⟩ : syracuseStep 499333 = 93625) (by norm_num)
theorem B564889 : Blo 443779 564889 := bbase (se 2 (by rfl) ⟨211833, by rfl⟩ : syracuseStep 564889 = 423667) (by norm_num)
theorem B499369 : Blo 443779 499369 := bbase (se 2 (by rfl) ⟨187263, by rfl⟩ : syracuseStep 499369 = 374527) (by norm_num)
theorem B2530997 : Blo 443779 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B499405 : Blo 443779 499405 := bbase (se 3 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 499405 = 187277) (by norm_num)
theorem B499441 : Blo 443779 499441 := bbase (se 2 (by rfl) ⟨187290, by rfl⟩ : syracuseStep 499441 = 374581) (by norm_num)
theorem B564985 : Blo 443779 564985 := bbase (se 2 (by rfl) ⟨211869, by rfl⟩ : syracuseStep 564985 = 423739) (by norm_num)
theorem B499477 : Blo 443779 499477 := bbase (se 6 (by rfl) ⟨11706, by rfl⟩ : syracuseStep 499477 = 23413) (by norm_num)
theorem B1154837 : Blo 443779 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B4267829 : Blo 443779 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B499513 : Blo 443779 499513 := bbase (se 2 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 499513 = 374635) (by norm_num)
theorem B499549 : Blo 443779 499549 := bbase (se 3 (by rfl) ⟨93665, by rfl⟩ : syracuseStep 499549 = 187331) (by norm_num)
theorem B761717 : Blo 443779 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B499585 : Blo 443779 499585 := bbase (se 2 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 499585 = 374689) (by norm_num)
theorem B499621 : Blo 443779 499621 := bbase (se 4 (by rfl) ⟨46839, by rfl⟩ : syracuseStep 499621 = 93679) (by norm_num)
theorem B565157 : Blo 443779 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B499657 : Blo 443779 499657 := bbase (se 2 (by rfl) ⟨187371, by rfl⟩ : syracuseStep 499657 = 374743) (by norm_num)
theorem B565213 : Blo 443779 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B499693 : Blo 443779 499693 := bbase (se 3 (by rfl) ⟨93692, by rfl⟩ : syracuseStep 499693 = 187385) (by norm_num)
theorem B499729 : Blo 443779 499729 := bbase (se 2 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 499729 = 374797) (by norm_num)
theorem B499765 : Blo 443779 499765 := bbase (se 5 (by rfl) ⟨23426, by rfl⟩ : syracuseStep 499765 = 46853) (by norm_num)
theorem B565309 : Blo 443779 565309 := bbase (se 3 (by rfl) ⟨105995, by rfl⟩ : syracuseStep 565309 = 211991) (by norm_num)
theorem B499801 : Blo 443779 499801 := bbase (se 2 (by rfl) ⟨187425, by rfl⟩ : syracuseStep 499801 = 374851) (by norm_num)
theorem B1351781 : Blo 443779 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B499837 : Blo 443779 499837 := bbase (se 3 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 499837 = 187439) (by norm_num)
theorem B1351829 : Blo 443779 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B499873 : Blo 443779 499873 := bbase (se 2 (by rfl) ⟨187452, by rfl⟩ : syracuseStep 499873 = 374905) (by norm_num)
theorem B499909 : Blo 443779 499909 := bbase (se 4 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 499909 = 93733) (by norm_num)
theorem B499945 : Blo 443779 499945 := bbase (se 2 (by rfl) ⟨187479, by rfl⟩ : syracuseStep 499945 = 374959) (by norm_num)
theorem B565481 : Blo 443779 565481 := bbase (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) (by norm_num)
theorem B4301045 : Blo 443779 4301045 := bbase (se 5 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 4301045 = 403223) (by norm_num)
theorem B499981 : Blo 443779 499981 := bbase (se 3 (by rfl) ⟨93746, by rfl⟩ : syracuseStep 499981 = 187493) (by norm_num)
theorem B565537 : Blo 443779 565537 := bbase (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) (by norm_num)
theorem B500017 : Blo 443779 500017 := bbase (se 2 (by rfl) ⟨187506, by rfl⟩ : syracuseStep 500017 = 375013) (by norm_num)
theorem B500053 : Blo 443779 500053 := bbase (se 10 (by rfl) ⟨732, by rfl⟩ : syracuseStep 500053 = 1465) (by norm_num)
theorem B500089 : Blo 443779 500089 := bbase (se 2 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 500089 = 375067) (by norm_num)
theorem B565633 : Blo 443779 565633 := bbase (se 2 (by rfl) ⟨212112, by rfl⟩ : syracuseStep 565633 = 424225) (by norm_num)
theorem B4825493 : Blo 443779 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B500125 : Blo 443779 500125 := bbase (se 3 (by rfl) ⟨93773, by rfl⟩ : syracuseStep 500125 = 187547) (by norm_num)
theorem B500161 : Blo 443779 500161 := bbase (se 2 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 500161 = 375121) (by norm_num)
theorem B500197 : Blo 443779 500197 := bbase (se 4 (by rfl) ⟨46893, by rfl⟩ : syracuseStep 500197 = 93787) (by norm_num)
theorem B500233 : Blo 443779 500233 := bbase (se 2 (by rfl) ⟨187587, by rfl⟩ : syracuseStep 500233 = 375175) (by norm_num)
theorem B500269 : Blo 443779 500269 := bbase (se 3 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 500269 = 187601) (by norm_num)
theorem B565805 : Blo 443779 565805 := bbase (se 3 (by rfl) ⟨106088, by rfl⟩ : syracuseStep 565805 = 212177) (by norm_num)
theorem B500305 : Blo 443779 500305 := bbase (se 2 (by rfl) ⟨187614, by rfl⟩ : syracuseStep 500305 = 375229) (by norm_num)
theorem B565861 : Blo 443779 565861 := bbase (se 4 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 565861 = 106099) (by norm_num)
theorem B500341 : Blo 443779 500341 := bbase (se 5 (by rfl) ⟨23453, by rfl⟩ : syracuseStep 500341 = 46907) (by norm_num)
theorem B500377 : Blo 443779 500377 := bbase (se 2 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 500377 = 375283) (by norm_num)
theorem B500413 : Blo 443779 500413 := bbase (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) (by norm_num)
theorem B565957 : Blo 443779 565957 := bbase (se 4 (by rfl) ⟨53058, by rfl⟩ : syracuseStep 565957 = 106117) (by norm_num)
theorem B500449 : Blo 443779 500449 := bbase (se 2 (by rfl) ⟨187668, by rfl⟩ : syracuseStep 500449 = 375337) (by norm_num)
theorem B500485 : Blo 443779 500485 := bbase (se 4 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 500485 = 93841) (by norm_num)
theorem B2564885 : Blo 443779 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B500521 : Blo 443779 500521 := bbase (se 2 (by rfl) ⟨187695, by rfl⟩ : syracuseStep 500521 = 375391) (by norm_num)
theorem B500557 : Blo 443779 500557 := bbase (se 3 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 500557 = 187709) (by norm_num)
theorem B2532181 : Blo 443779 2532181 := bbase (se 9 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 2532181 = 14837) (by norm_num)
theorem B500593 : Blo 443779 500593 := bbase (se 2 (by rfl) ⟨187722, by rfl⟩ : syracuseStep 500593 = 375445) (by norm_num)
theorem B566129 : Blo 443779 566129 := bbase (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) (by norm_num)
theorem B500629 : Blo 443779 500629 := bbase (se 6 (by rfl) ⟨11733, by rfl⟩ : syracuseStep 500629 = 23467) (by norm_num)
theorem B566185 : Blo 443779 566185 := bbase (se 2 (by rfl) ⟨212319, by rfl⟩ : syracuseStep 566185 = 424639) (by norm_num)
theorem B500665 : Blo 443779 500665 := bbase (se 2 (by rfl) ⟨187749, by rfl⟩ : syracuseStep 500665 = 375499) (by norm_num)
theorem B500701 : Blo 443779 500701 := bbase (se 3 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 500701 = 187763) (by norm_num)
theorem B500737 : Blo 443779 500737 := bbase (se 2 (by rfl) ⟨187776, by rfl⟩ : syracuseStep 500737 = 375553) (by norm_num)
theorem B566281 : Blo 443779 566281 := bbase (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) (by norm_num)
theorem B500773 : Blo 443779 500773 := bbase (se 4 (by rfl) ⟨46947, by rfl⟩ : syracuseStep 500773 = 93895) (by norm_num)
theorem B4138037 : Blo 443779 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B500809 : Blo 443779 500809 := bbase (se 2 (by rfl) ⟨187803, by rfl⟩ : syracuseStep 500809 = 375607) (by norm_num)
theorem B631901 : Blo 443779 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B1123429 : Blo 443779 1123429 := bbase (se 4 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 1123429 = 210643) (by norm_num)
theorem B500845 : Blo 443779 500845 := bbase (se 3 (by rfl) ⟨93908, by rfl⟩ : syracuseStep 500845 = 187817) (by norm_num)
theorem B500881 : Blo 443779 500881 := bbase (se 2 (by rfl) ⟨187830, by rfl⟩ : syracuseStep 500881 = 375661) (by norm_num)
theorem B500917 : Blo 443779 500917 := bbase (se 5 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 500917 = 46961) (by norm_num)
theorem B566453 : Blo 443779 566453 := bbase (se 5 (by rfl) ⟨26552, by rfl⟩ : syracuseStep 566453 = 53105) (by norm_num)
theorem B1123541 : Blo 443779 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B500953 : Blo 443779 500953 := bbase (se 2 (by rfl) ⟨187857, by rfl⟩ : syracuseStep 500953 = 375715) (by norm_num)
theorem B533729 : Blo 443779 533729 := bbase (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) (by norm_num)
theorem B566509 : Blo 443779 566509 := bbase (se 3 (by rfl) ⟨106220, by rfl⟩ : syracuseStep 566509 = 212441) (by norm_num)
theorem B2172149 : Blo 443779 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B500989 : Blo 443779 500989 := bbase (se 3 (by rfl) ⟨93935, by rfl⟩ : syracuseStep 500989 = 187871) (by norm_num)
theorem B501025 : Blo 443779 501025 := bbase (se 2 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 501025 = 375769) (by norm_num)
theorem B501061 : Blo 443779 501061 := bbase (se 4 (by rfl) ⟨46974, by rfl⟩ : syracuseStep 501061 = 93949) (by norm_num)
theorem B566605 : Blo 443779 566605 := bbase (se 3 (by rfl) ⟨106238, by rfl⟩ : syracuseStep 566605 = 212477) (by norm_num)
theorem B501097 : Blo 443779 501097 := bbase (se 2 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 501097 = 375823) (by norm_num)
theorem B501133 : Blo 443779 501133 := bbase (se 3 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 501133 = 187925) (by norm_num)
theorem B1123733 : Blo 443779 1123733 := bbase (se 6 (by rfl) ⟨26337, by rfl⟩ : syracuseStep 1123733 = 52675) (by norm_num)
theorem B501169 : Blo 443779 501169 := bbase (se 2 (by rfl) ⟨187938, by rfl⟩ : syracuseStep 501169 = 375877) (by norm_num)
theorem B1811909 : Blo 443779 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B2139605 : Blo 443779 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B501205 : Blo 443779 501205 := bbase (se 7 (by rfl) ⟨5873, by rfl⟩ : syracuseStep 501205 = 11747) (by norm_num)
theorem B2041301 : Blo 443779 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B533989 : Blo 443779 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B501241 : Blo 443779 501241 := bbase (se 2 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 501241 = 375931) (by norm_num)
theorem B5416469 : Blo 443779 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B501277 : Blo 443779 501277 := bbase (se 3 (by rfl) ⟨93989, by rfl⟩ : syracuseStep 501277 = 187979) (by norm_num)
theorem B501313 : Blo 443779 501313 := bbase (se 2 (by rfl) ⟨187992, by rfl⟩ : syracuseStep 501313 = 375985) (by norm_num)
theorem B1222229 : Blo 443779 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B501349 : Blo 443779 501349 := bbase (se 4 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 501349 = 94003) (by norm_num)
theorem B632453 : Blo 443779 632453 := bbase (se 4 (by rfl) ⟨59292, by rfl⟩ : syracuseStep 632453 = 118585) (by norm_num)
theorem B501385 : Blo 443779 501385 := bbase (se 2 (by rfl) ⟨188019, by rfl⟩ : syracuseStep 501385 = 376039) (by norm_num)
theorem B2139797 : Blo 443779 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B534181 : Blo 443779 534181 := bbase (se 4 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 534181 = 100159) (by norm_num)
theorem B501421 : Blo 443779 501421 := bbase (se 3 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 501421 = 188033) (by norm_num)
theorem B534205 : Blo 443779 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B534209 : Blo 443779 534209 := bbase (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) (by norm_num)
theorem B501457 : Blo 443779 501457 := bbase (se 2 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 501457 = 376093) (by norm_num)
theorem B1124077 : Blo 443779 1124077 := bbase (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) (by norm_num)
theorem B501493 : Blo 443779 501493 := bbase (se 5 (by rfl) ⟨23507, by rfl⟩ : syracuseStep 501493 = 47015) (by norm_num)
theorem B501529 : Blo 443779 501529 := bbase (se 2 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 501529 = 376147) (by norm_num)
theorem B501565 : Blo 443779 501565 := bbase (se 3 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 501565 = 188087) (by norm_num)
theorem B894797 : Blo 443779 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B1124189 : Blo 443779 1124189 := bbase (se 3 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 1124189 = 421571) (by norm_num)
theorem B501601 : Blo 443779 501601 := bbase (se 2 (by rfl) ⟨188100, by rfl⟩ : syracuseStep 501601 = 376201) (by norm_num)
theorem B501637 : Blo 443779 501637 := bbase (se 4 (by rfl) ⟨47028, by rfl⟩ : syracuseStep 501637 = 94057) (by norm_num)
theorem B501673 : Blo 443779 501673 := bbase (se 2 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 501673 = 376255) (by norm_num)
theorem B501709 : Blo 443779 501709 := bbase (se 3 (by rfl) ⟨94070, by rfl⟩ : syracuseStep 501709 = 188141) (by norm_num)
theorem B501745 : Blo 443779 501745 := bbase (se 2 (by rfl) ⟨188154, by rfl⟩ : syracuseStep 501745 = 376309) (by norm_num)
theorem B501781 : Blo 443779 501781 := bbase (se 6 (by rfl) ⟨11760, by rfl⟩ : syracuseStep 501781 = 23521) (by norm_num)
theorem B1124381 : Blo 443779 1124381 := bbase (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) (by norm_num)
theorem B501817 : Blo 443779 501817 := bbase (se 2 (by rfl) ⟨188181, by rfl⟩ : syracuseStep 501817 = 376363) (by norm_num)
theorem B665669 : Blo 443779 665669 := bbase (se 4 (by rfl) ⟨62406, by rfl⟩ : syracuseStep 665669 = 124813) (by norm_num)
theorem B665693 : Blo 443779 665693 := bbase (se 3 (by rfl) ⟨124817, by rfl⟩ : syracuseStep 665693 = 249635) (by norm_num)
theorem B501853 : Blo 443779 501853 := bbase (se 3 (by rfl) ⟨94097, by rfl⟩ : syracuseStep 501853 = 188195) (by norm_num)
theorem B665717 : Blo 443779 665717 := bbase (se 5 (by rfl) ⟨31205, by rfl⟩ : syracuseStep 665717 = 62411) (by norm_num)
theorem B501889 : Blo 443779 501889 := bbase (se 2 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 501889 = 376417) (by norm_num)
theorem B665741 : Blo 443779 665741 := bbase (se 3 (by rfl) ⟨124826, by rfl⟩ : syracuseStep 665741 = 249653) (by norm_num)
theorem B665765 : Blo 443779 665765 := bbase (se 4 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 665765 = 124831) (by norm_num)
theorem B600229 : Blo 443779 600229 := bbase (se 4 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 600229 = 112543) (by norm_num)
theorem B501925 : Blo 443779 501925 := bbase (se 4 (by rfl) ⟨47055, by rfl⟩ : syracuseStep 501925 = 94111) (by norm_num)
theorem B534709 : Blo 443779 534709 := bbase (se 5 (by rfl) ⟨25064, by rfl⟩ : syracuseStep 534709 = 50129) (by norm_num)
theorem B665789 : Blo 443779 665789 := bbase (se 3 (by rfl) ⟨124835, by rfl⟩ : syracuseStep 665789 = 249671) (by norm_num)
theorem B501961 : Blo 443779 501961 := bbase (se 2 (by rfl) ⟨188235, by rfl⟩ : syracuseStep 501961 = 376471) (by norm_num)
theorem B665813 : Blo 443779 665813 := bbase (se 7 (by rfl) ⟨7802, by rfl⟩ : syracuseStep 665813 = 15605) (by norm_num)
theorem B665837 : Blo 443779 665837 := bbase (se 3 (by rfl) ⟨124844, by rfl⟩ : syracuseStep 665837 = 249689) (by norm_num)
theorem B501997 : Blo 443779 501997 := bbase (se 3 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 501997 = 188249) (by norm_num)
theorem B665861 : Blo 443779 665861 := bbase (se 4 (by rfl) ⟨62424, by rfl⟩ : syracuseStep 665861 = 124849) (by norm_num)
theorem B502033 : Blo 443779 502033 := bbase (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) (by norm_num)
theorem B534805 : Blo 443779 534805 := bbase (se 6 (by rfl) ⟨12534, by rfl⟩ : syracuseStep 534805 = 25069) (by norm_num)
theorem B665885 : Blo 443779 665885 := bbase (se 3 (by rfl) ⟨124853, by rfl⟩ : syracuseStep 665885 = 249707) (by norm_num)
theorem B665909 : Blo 443779 665909 := bbase (se 5 (by rfl) ⟨31214, by rfl⟩ : syracuseStep 665909 = 62429) (by norm_num)
theorem B3909941 : Blo 443779 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B502069 : Blo 443779 502069 := bbase (se 5 (by rfl) ⟨23534, by rfl⟩ : syracuseStep 502069 = 47069) (by norm_num)
theorem B665933 : Blo 443779 665933 := bbase (se 3 (by rfl) ⟨124862, by rfl⟩ : syracuseStep 665933 = 249725) (by norm_num)
theorem B502105 : Blo 443779 502105 := bbase (se 2 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 502105 = 376579) (by norm_num)
theorem B665957 : Blo 443779 665957 := bbase (se 4 (by rfl) ⟨62433, by rfl⟩ : syracuseStep 665957 = 124867) (by norm_num)
theorem B3058037 : Blo 443779 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B1124725 : Blo 443779 1124725 := bbase (se 5 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 1124725 = 105443) (by norm_num)
theorem B633205 : Blo 443779 633205 := bbase (se 5 (by rfl) ⟨29681, by rfl⟩ : syracuseStep 633205 = 59363) (by norm_num)
theorem B665981 : Blo 443779 665981 := bbase (se 3 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 665981 = 249743) (by norm_num)
theorem B502141 : Blo 443779 502141 := bbase (se 3 (by rfl) ⟨94151, by rfl⟩ : syracuseStep 502141 = 188303) (by norm_num)
theorem B666005 : Blo 443779 666005 := bbase (se 6 (by rfl) ⟨15609, by rfl⟩ : syracuseStep 666005 = 31219) (by norm_num)
theorem B502177 : Blo 443779 502177 := bbase (se 2 (by rfl) ⟨188316, by rfl⟩ : syracuseStep 502177 = 376633) (by norm_num)
theorem B666029 : Blo 443779 666029 := bbase (se 3 (by rfl) ⟨124880, by rfl⟩ : syracuseStep 666029 = 249761) (by norm_num)
theorem B666053 : Blo 443779 666053 := bbase (se 4 (by rfl) ⟨62442, by rfl⟩ : syracuseStep 666053 = 124885) (by norm_num)
theorem B502213 : Blo 443779 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B666077 : Blo 443779 666077 := bbase (se 3 (by rfl) ⟨124889, by rfl⟩ : syracuseStep 666077 = 249779) (by norm_num)
theorem B1124837 : Blo 443779 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B502249 : Blo 443779 502249 := bbase (se 2 (by rfl) ⟨188343, by rfl⟩ : syracuseStep 502249 = 376687) (by norm_num)
theorem B666101 : Blo 443779 666101 := bbase (se 5 (by rfl) ⟨31223, by rfl⟩ : syracuseStep 666101 = 62447) (by norm_num)
theorem B666125 : Blo 443779 666125 := bbase (se 3 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 666125 = 249797) (by norm_num)
theorem B502285 : Blo 443779 502285 := bbase (se 3 (by rfl) ⟨94178, by rfl⟩ : syracuseStep 502285 = 188357) (by norm_num)
theorem B666149 : Blo 443779 666149 := bbase (se 4 (by rfl) ⟨62451, by rfl⟩ : syracuseStep 666149 = 124903) (by norm_num)
theorem B502321 : Blo 443779 502321 := bbase (se 2 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 502321 = 376741) (by norm_num)
theorem B666173 : Blo 443779 666173 := bbase (se 3 (by rfl) ⟨124907, by rfl⟩ : syracuseStep 666173 = 249815) (by norm_num)
theorem B5089877 : Blo 443779 5089877 := bbase (se 8 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 5089877 = 59647) (by norm_num)
theorem B666197 : Blo 443779 666197 := bbase (se 8 (by rfl) ⟨3903, by rfl⟩ : syracuseStep 666197 = 7807) (by norm_num)
theorem B502357 : Blo 443779 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B666221 : Blo 443779 666221 := bbase (se 3 (by rfl) ⟨124916, by rfl⟩ : syracuseStep 666221 = 249833) (by norm_num)
theorem B502393 : Blo 443779 502393 := bbase (se 2 (by rfl) ⟨188397, by rfl⟩ : syracuseStep 502393 = 376795) (by norm_num)
theorem B666245 : Blo 443779 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B666269 : Blo 443779 666269 := bbase (se 3 (by rfl) ⟨124925, by rfl⟩ : syracuseStep 666269 = 249851) (by norm_num)
theorem B502429 : Blo 443779 502429 := bbase (se 3 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 502429 = 188411) (by norm_num)
theorem B1125029 : Blo 443779 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B666293 : Blo 443779 666293 := bbase (se 5 (by rfl) ⟨31232, by rfl⟩ : syracuseStep 666293 = 62465) (by norm_num)
theorem B1452725 : Blo 443779 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B502465 : Blo 443779 502465 := bbase (se 2 (by rfl) ⟨188424, by rfl⟩ : syracuseStep 502465 = 376849) (by norm_num)
theorem B666317 : Blo 443779 666317 := bbase (se 3 (by rfl) ⟨124934, by rfl⟩ : syracuseStep 666317 = 249869) (by norm_num)
theorem B666341 : Blo 443779 666341 := bbase (se 4 (by rfl) ⟨62469, by rfl⟩ : syracuseStep 666341 = 124939) (by norm_num)
theorem B502501 : Blo 443779 502501 := bbase (se 4 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 502501 = 94219) (by norm_num)
theorem B666365 : Blo 443779 666365 := bbase (se 3 (by rfl) ⟨124943, by rfl⟩ : syracuseStep 666365 = 249887) (by norm_num)
theorem B502537 : Blo 443779 502537 := bbase (se 2 (by rfl) ⟨188451, by rfl⟩ : syracuseStep 502537 = 376903) (by norm_num)
theorem B666389 : Blo 443779 666389 := bbase (se 6 (by rfl) ⟨15618, by rfl⟩ : syracuseStep 666389 = 31237) (by norm_num)
theorem B2534165 : Blo 443779 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B666413 : Blo 443779 666413 := bbase (se 3 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 666413 = 249905) (by norm_num)
theorem B502573 : Blo 443779 502573 := bbase (se 3 (by rfl) ⟨94232, by rfl⟩ : syracuseStep 502573 = 188465) (by norm_num)
theorem B666437 : Blo 443779 666437 := bbase (se 4 (by rfl) ⟨62478, by rfl⟩ : syracuseStep 666437 = 124957) (by norm_num)
theorem B502609 : Blo 443779 502609 := bbase (se 2 (by rfl) ⟨188478, by rfl⟩ : syracuseStep 502609 = 376957) (by norm_num)
theorem B666461 : Blo 443779 666461 := bbase (se 3 (by rfl) ⟨124961, by rfl⟩ : syracuseStep 666461 = 249923) (by norm_num)
theorem B666485 : Blo 443779 666485 := bbase (se 5 (by rfl) ⟨31241, by rfl⟩ : syracuseStep 666485 = 62483) (by norm_num)
theorem B502645 : Blo 443779 502645 := bbase (se 5 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 502645 = 47123) (by norm_num)
theorem B666509 : Blo 443779 666509 := bbase (se 3 (by rfl) ⟨124970, by rfl⟩ : syracuseStep 666509 = 249941) (by norm_num)
theorem B502681 : Blo 443779 502681 := bbase (se 2 (by rfl) ⟨188505, by rfl⟩ : syracuseStep 502681 = 377011) (by norm_num)
theorem B666533 : Blo 443779 666533 := bbase (se 4 (by rfl) ⟨62487, by rfl⟩ : syracuseStep 666533 = 124975) (by norm_num)
theorem B666557 : Blo 443779 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B502717 : Blo 443779 502717 := bbase (se 3 (by rfl) ⟨94259, by rfl⟩ : syracuseStep 502717 = 188519) (by norm_num)
theorem B666581 : Blo 443779 666581 := bbase (se 7 (by rfl) ⟨7811, by rfl⟩ : syracuseStep 666581 = 15623) (by norm_num)
theorem B502753 : Blo 443779 502753 := bbase (se 2 (by rfl) ⟨188532, by rfl⟩ : syracuseStep 502753 = 377065) (by norm_num)
theorem B666605 : Blo 443779 666605 := bbase (se 3 (by rfl) ⟨124988, by rfl⟩ : syracuseStep 666605 = 249977) (by norm_num)
theorem B1125373 : Blo 443779 1125373 := bbase (se 3 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 1125373 = 422015) (by norm_num)
theorem B666629 : Blo 443779 666629 := bbase (se 4 (by rfl) ⟨62496, by rfl⟩ : syracuseStep 666629 = 124993) (by norm_num)
theorem B502789 : Blo 443779 502789 := bbase (se 4 (by rfl) ⟨47136, by rfl⟩ : syracuseStep 502789 = 94273) (by norm_num)
theorem B666653 : Blo 443779 666653 := bbase (se 3 (by rfl) ⟨124997, by rfl⟩ : syracuseStep 666653 = 249995) (by norm_num)
theorem B502825 : Blo 443779 502825 := bbase (se 2 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 502825 = 377119) (by norm_num)
theorem B666677 : Blo 443779 666677 := bbase (se 5 (by rfl) ⟨31250, by rfl⟩ : syracuseStep 666677 = 62501) (by norm_num)
theorem B666701 : Blo 443779 666701 := bbase (se 3 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 666701 = 250013) (by norm_num)
theorem B502861 : Blo 443779 502861 := bbase (se 3 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 502861 = 188573) (by norm_num)
theorem B666725 : Blo 443779 666725 := bbase (se 4 (by rfl) ⟨62505, by rfl⟩ : syracuseStep 666725 = 125011) (by norm_num)
theorem B1125485 : Blo 443779 1125485 := bbase (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) (by norm_num)
theorem B502897 : Blo 443779 502897 := bbase (se 2 (by rfl) ⟨188586, by rfl⟩ : syracuseStep 502897 = 377173) (by norm_num)
theorem B666749 : Blo 443779 666749 := bbase (se 3 (by rfl) ⟨125015, by rfl⟩ : syracuseStep 666749 = 250031) (by norm_num)
theorem B633997 : Blo 443779 633997 := bbase (se 3 (by rfl) ⟨118874, by rfl⟩ : syracuseStep 633997 = 237749) (by norm_num)
theorem B666773 : Blo 443779 666773 := bbase (se 6 (by rfl) ⟨15627, by rfl⟩ : syracuseStep 666773 = 31255) (by norm_num)
theorem B502933 : Blo 443779 502933 := bbase (se 6 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 502933 = 23575) (by norm_num)
theorem B666797 : Blo 443779 666797 := bbase (se 3 (by rfl) ⟨125024, by rfl⟩ : syracuseStep 666797 = 250049) (by norm_num)
theorem B502969 : Blo 443779 502969 := bbase (se 2 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 502969 = 377227) (by norm_num)
theorem B666821 : Blo 443779 666821 := bbase (se 4 (by rfl) ⟨62514, by rfl⟩ : syracuseStep 666821 = 125029) (by norm_num)
theorem B666845 : Blo 443779 666845 := bbase (se 3 (by rfl) ⟨125033, by rfl⟩ : syracuseStep 666845 = 250067) (by norm_num)
theorem B503005 : Blo 443779 503005 := bbase (se 3 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 503005 = 188627) (by norm_num)
theorem B535781 : Blo 443779 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B666869 : Blo 443779 666869 := bbase (se 5 (by rfl) ⟨31259, by rfl⟩ : syracuseStep 666869 = 62519) (by norm_num)
theorem B503041 : Blo 443779 503041 := bbase (se 2 (by rfl) ⟨188640, by rfl⟩ : syracuseStep 503041 = 377281) (by norm_num)
theorem B666893 : Blo 443779 666893 := bbase (se 3 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 666893 = 250085) (by norm_num)
theorem B666917 : Blo 443779 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B503077 : Blo 443779 503077 := bbase (se 4 (by rfl) ⟨47163, by rfl⟩ : syracuseStep 503077 = 94327) (by norm_num)
theorem B1125677 : Blo 443779 1125677 := bbase (se 3 (by rfl) ⟨211064, by rfl⟩ : syracuseStep 1125677 = 422129) (by norm_num)
theorem B666941 : Blo 443779 666941 := bbase (se 3 (by rfl) ⟨125051, by rfl⟩ : syracuseStep 666941 = 250103) (by norm_num)
theorem B503113 : Blo 443779 503113 := bbase (se 2 (by rfl) ⟨188667, by rfl⟩ : syracuseStep 503113 = 377335) (by norm_num)
theorem B666965 : Blo 443779 666965 := bbase (se 11 (by rfl) ⟨488, by rfl⟩ : syracuseStep 666965 = 977) (by norm_num)
theorem B666989 : Blo 443779 666989 := bbase (se 3 (by rfl) ⟨125060, by rfl⟩ : syracuseStep 666989 = 250121) (by norm_num)
theorem B503149 : Blo 443779 503149 := bbase (se 3 (by rfl) ⟨94340, by rfl⟩ : syracuseStep 503149 = 188681) (by norm_num)
theorem B667013 : Blo 443779 667013 := bbase (se 4 (by rfl) ⟨62532, by rfl⟩ : syracuseStep 667013 = 125065) (by norm_num)
theorem B503185 : Blo 443779 503185 := bbase (se 2 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 503185 = 377389) (by norm_num)
theorem B667037 : Blo 443779 667037 := bbase (se 3 (by rfl) ⟨125069, by rfl⟩ : syracuseStep 667037 = 250139) (by norm_num)
theorem B667061 : Blo 443779 667061 := bbase (se 5 (by rfl) ⟨31268, by rfl⟩ : syracuseStep 667061 = 62537) (by norm_num)
theorem B503221 : Blo 443779 503221 := bbase (se 5 (by rfl) ⟨23588, by rfl⟩ : syracuseStep 503221 = 47177) (by norm_num)
theorem B667085 : Blo 443779 667085 := bbase (se 3 (by rfl) ⟨125078, by rfl⟩ : syracuseStep 667085 = 250157) (by norm_num)
theorem B503257 : Blo 443779 503257 := bbase (se 2 (by rfl) ⟨188721, by rfl⟩ : syracuseStep 503257 = 377443) (by norm_num)
theorem B634333 : Blo 443779 634333 := bbase (se 3 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 634333 = 237875) (by norm_num)
theorem B667109 : Blo 443779 667109 := bbase (se 4 (by rfl) ⟨62541, by rfl⟩ : syracuseStep 667109 = 125083) (by norm_num)
theorem B667133 : Blo 443779 667133 := bbase (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) (by norm_num)
theorem B503293 : Blo 443779 503293 := bbase (se 3 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 503293 = 188735) (by norm_num)
theorem B667157 : Blo 443779 667157 := bbase (se 6 (by rfl) ⟨15636, by rfl⟩ : syracuseStep 667157 = 31273) (by norm_num)
theorem B503329 : Blo 443779 503329 := bbase (se 2 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 503329 = 377497) (by norm_num)
theorem B667181 : Blo 443779 667181 := bbase (se 3 (by rfl) ⟨125096, by rfl⟩ : syracuseStep 667181 = 250193) (by norm_num)
theorem B3386933 : Blo 443779 3386933 := bbase (se 5 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 3386933 = 317525) (by norm_num)
theorem B667205 : Blo 443779 667205 := bbase (se 4 (by rfl) ⟨62550, by rfl⟩ : syracuseStep 667205 = 125101) (by norm_num)
theorem B503365 : Blo 443779 503365 := bbase (se 4 (by rfl) ⟨47190, by rfl⟩ : syracuseStep 503365 = 94381) (by norm_num)
theorem B667229 : Blo 443779 667229 := bbase (se 3 (by rfl) ⟨125105, by rfl⟩ : syracuseStep 667229 = 250211) (by norm_num)
theorem B503401 : Blo 443779 503401 := bbase (se 2 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 503401 = 377551) (by norm_num)
theorem B667253 : Blo 443779 667253 := bbase (se 5 (by rfl) ⟨31277, by rfl⟩ : syracuseStep 667253 = 62555) (by norm_num)
theorem B1126021 : Blo 443779 1126021 := bbase (se 4 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 1126021 = 211129) (by norm_num)
theorem B667277 : Blo 443779 667277 := bbase (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) (by norm_num)
theorem B503437 : Blo 443779 503437 := bbase (se 3 (by rfl) ⟨94394, by rfl⟩ : syracuseStep 503437 = 188789) (by norm_num)
theorem B667301 : Blo 443779 667301 := bbase (se 4 (by rfl) ⟨62559, by rfl⟩ : syracuseStep 667301 = 125119) (by norm_num)
theorem B503473 : Blo 443779 503473 := bbase (se 2 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 503473 = 377605) (by norm_num)
theorem B634549 : Blo 443779 634549 := bbase (se 5 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 634549 = 59489) (by norm_num)
theorem B667325 : Blo 443779 667325 := bbase (se 3 (by rfl) ⟨125123, by rfl⟩ : syracuseStep 667325 = 250247) (by norm_num)
theorem B536257 : Blo 443779 536257 := bbase (se 2 (by rfl) ⟨201096, by rfl⟩ : syracuseStep 536257 = 402193) (by norm_num)
theorem B2141893 : Blo 443779 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B1912517 : Blo 443779 1912517 := bbase (se 4 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 1912517 = 358597) (by norm_num)
theorem B667349 : Blo 443779 667349 := bbase (se 7 (by rfl) ⟨7820, by rfl⟩ : syracuseStep 667349 = 15641) (by norm_num)
theorem B503509 : Blo 443779 503509 := bbase (se 7 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 503509 = 11801) (by norm_num)
theorem B536285 : Blo 443779 536285 := bbase (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) (by norm_num)
theorem B667373 : Blo 443779 667373 := bbase (se 3 (by rfl) ⟨125132, by rfl⟩ : syracuseStep 667373 = 250265) (by norm_num)
theorem B1126133 : Blo 443779 1126133 := bbase (se 5 (by rfl) ⟨52787, by rfl⟩ : syracuseStep 1126133 = 105575) (by norm_num)
theorem B3092213 : Blo 443779 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B503545 : Blo 443779 503545 := bbase (se 2 (by rfl) ⟨188829, by rfl⟩ : syracuseStep 503545 = 377659) (by norm_num)
theorem B667397 : Blo 443779 667397 := bbase (se 4 (by rfl) ⟨62568, by rfl⟩ : syracuseStep 667397 = 125137) (by norm_num)
theorem B6893333 : Blo 443779 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B667421 : Blo 443779 667421 := bbase (se 3 (by rfl) ⟨125141, by rfl⟩ : syracuseStep 667421 = 250283) (by norm_num)
theorem B503581 : Blo 443779 503581 := bbase (se 3 (by rfl) ⟨94421, by rfl⟩ : syracuseStep 503581 = 188843) (by norm_num)
theorem B667445 : Blo 443779 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B503617 : Blo 443779 503617 := bbase (se 2 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 503617 = 377713) (by norm_num)
theorem B667469 : Blo 443779 667469 := bbase (se 3 (by rfl) ⟨125150, by rfl⟩ : syracuseStep 667469 = 250301) (by norm_num)
theorem B667493 : Blo 443779 667493 := bbase (se 4 (by rfl) ⟨62577, by rfl⟩ : syracuseStep 667493 = 125155) (by norm_num)
theorem B503653 : Blo 443779 503653 := bbase (se 4 (by rfl) ⟨47217, by rfl⟩ : syracuseStep 503653 = 94435) (by norm_num)
theorem B667517 : Blo 443779 667517 := bbase (se 3 (by rfl) ⟨125159, by rfl⟩ : syracuseStep 667517 = 250319) (by norm_num)
theorem B503689 : Blo 443779 503689 := bbase (se 2 (by rfl) ⟨188883, by rfl⟩ : syracuseStep 503689 = 377767) (by norm_num)
theorem B667541 : Blo 443779 667541 := bbase (se 6 (by rfl) ⟨15645, by rfl⟩ : syracuseStep 667541 = 31291) (by norm_num)
theorem B536473 : Blo 443779 536473 := bbase (se 2 (by rfl) ⟨201177, by rfl⟩ : syracuseStep 536473 = 402355) (by norm_num)
theorem B667565 : Blo 443779 667565 := bbase (se 3 (by rfl) ⟨125168, by rfl⟩ : syracuseStep 667565 = 250337) (by norm_num)
theorem B503725 : Blo 443779 503725 := bbase (se 3 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 503725 = 188897) (by norm_num)
theorem B1126325 : Blo 443779 1126325 := bbase (se 5 (by rfl) ⟨52796, by rfl⟩ : syracuseStep 1126325 = 105593) (by norm_num)
theorem B667589 : Blo 443779 667589 := bbase (se 4 (by rfl) ⟨62586, by rfl⟩ : syracuseStep 667589 = 125173) (by norm_num)
theorem B667613 : Blo 443779 667613 := bbase (se 3 (by rfl) ⟨125177, by rfl⟩ : syracuseStep 667613 = 250355) (by norm_num)
theorem B667637 : Blo 443779 667637 := bbase (se 5 (by rfl) ⟨31295, by rfl⟩ : syracuseStep 667637 = 62591) (by norm_num)
theorem B667661 : Blo 443779 667661 := bbase (se 3 (by rfl) ⟨125186, by rfl⟩ : syracuseStep 667661 = 250373) (by norm_num)
theorem B536593 : Blo 443779 536593 := bbase (se 2 (by rfl) ⟨201222, by rfl⟩ : syracuseStep 536593 = 402445) (by norm_num)
theorem B667685 : Blo 443779 667685 := bbase (se 4 (by rfl) ⟨62595, by rfl⟩ : syracuseStep 667685 = 125191) (by norm_num)
theorem B602149 : Blo 443779 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B634925 : Blo 443779 634925 := bbase (se 3 (by rfl) ⟨119048, by rfl⟩ : syracuseStep 634925 = 238097) (by norm_num)
theorem B667709 : Blo 443779 667709 := bbase (se 3 (by rfl) ⟨125195, by rfl⟩ : syracuseStep 667709 = 250391) (by norm_num)
theorem B667733 : Blo 443779 667733 := bbase (se 8 (by rfl) ⟨3912, by rfl⟩ : syracuseStep 667733 = 7825) (by norm_num)
theorem B667757 : Blo 443779 667757 := bbase (se 3 (by rfl) ⟨125204, by rfl⟩ : syracuseStep 667757 = 250409) (by norm_num)
theorem B667781 : Blo 443779 667781 := bbase (se 4 (by rfl) ⟨62604, by rfl⟩ : syracuseStep 667781 = 125209) (by norm_num)
theorem B667805 : Blo 443779 667805 := bbase (se 3 (by rfl) ⟨125213, by rfl⟩ : syracuseStep 667805 = 250427) (by norm_num)
theorem B667829 : Blo 443779 667829 := bbase (se 5 (by rfl) ⟨31304, by rfl⟩ : syracuseStep 667829 = 62609) (by norm_num)
theorem B667853 : Blo 443779 667853 := bbase (se 3 (by rfl) ⟨125222, by rfl⟩ : syracuseStep 667853 = 250445) (by norm_num)
theorem B2699477 : Blo 443779 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B667877 : Blo 443779 667877 := bbase (se 4 (by rfl) ⟨62613, by rfl⟩ : syracuseStep 667877 = 125227) (by norm_num)
theorem B667901 : Blo 443779 667901 := bbase (se 3 (by rfl) ⟨125231, by rfl⟩ : syracuseStep 667901 = 250463) (by norm_num)
theorem B602365 : Blo 443779 602365 := bbase (se 3 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 602365 = 225887) (by norm_num)
theorem B1126669 : Blo 443779 1126669 := bbase (se 3 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 1126669 = 422501) (by norm_num)
theorem B667925 : Blo 443779 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B667949 : Blo 443779 667949 := bbase (se 3 (by rfl) ⟨125240, by rfl⟩ : syracuseStep 667949 = 250481) (by norm_num)
theorem B667973 : Blo 443779 667973 := bbase (se 4 (by rfl) ⟨62622, by rfl⟩ : syracuseStep 667973 = 125245) (by norm_num)
theorem B667997 : Blo 443779 667997 := bbase (se 3 (by rfl) ⟨125249, by rfl⟩ : syracuseStep 667997 = 250499) (by norm_num)
theorem B668021 : Blo 443779 668021 := bbase (se 5 (by rfl) ⟨31313, by rfl⟩ : syracuseStep 668021 = 62627) (by norm_num)
theorem B1126781 : Blo 443779 1126781 := bbase (se 3 (by rfl) ⟨211271, by rfl⟩ : syracuseStep 1126781 = 422543) (by norm_num)
theorem B668045 : Blo 443779 668045 := bbase (se 3 (by rfl) ⟨125258, by rfl⟩ : syracuseStep 668045 = 250517) (by norm_num)
theorem B2699669 : Blo 443779 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B668069 : Blo 443779 668069 := bbase (se 4 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 668069 = 125263) (by norm_num)
theorem B668093 : Blo 443779 668093 := bbase (se 3 (by rfl) ⟨125267, by rfl⟩ : syracuseStep 668093 = 250535) (by norm_num)
theorem B668117 : Blo 443779 668117 := bbase (se 7 (by rfl) ⟨7829, by rfl⟩ : syracuseStep 668117 = 15659) (by norm_num)
theorem B5419477 : Blo 443779 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B668141 : Blo 443779 668141 := bbase (se 3 (by rfl) ⟨125276, by rfl⟩ : syracuseStep 668141 = 250553) (by norm_num)
theorem B668165 : Blo 443779 668165 := bbase (se 4 (by rfl) ⟨62640, by rfl⟩ : syracuseStep 668165 = 125281) (by norm_num)
theorem B668189 : Blo 443779 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B668213 : Blo 443779 668213 := bbase (se 5 (by rfl) ⟨31322, by rfl⟩ : syracuseStep 668213 = 62645) (by norm_num)
theorem B1126973 : Blo 443779 1126973 := bbase (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) (by norm_num)
theorem B668237 : Blo 443779 668237 := bbase (se 3 (by rfl) ⟨125294, by rfl⟩ : syracuseStep 668237 = 250589) (by norm_num)
theorem B668261 : Blo 443779 668261 := bbase (se 4 (by rfl) ⟨62649, by rfl⟩ : syracuseStep 668261 = 125299) (by norm_num)
theorem B668285 : Blo 443779 668285 := bbase (se 3 (by rfl) ⟨125303, by rfl⟩ : syracuseStep 668285 = 250607) (by norm_num)
theorem B668309 : Blo 443779 668309 := bbase (se 6 (by rfl) ⟨15663, by rfl⟩ : syracuseStep 668309 = 31327) (by norm_num)
theorem B668333 : Blo 443779 668333 := bbase (se 3 (by rfl) ⟨125312, by rfl⟩ : syracuseStep 668333 = 250625) (by norm_num)
theorem B668357 : Blo 443779 668357 := bbase (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) (by norm_num)
theorem B668381 : Blo 443779 668381 := bbase (se 3 (by rfl) ⟨125321, by rfl⟩ : syracuseStep 668381 = 250643) (by norm_num)
theorem B668405 : Blo 443779 668405 := bbase (se 5 (by rfl) ⟨31331, by rfl⟩ : syracuseStep 668405 = 62663) (by norm_num)
theorem B668429 : Blo 443779 668429 := bbase (se 3 (by rfl) ⟨125330, by rfl⟩ : syracuseStep 668429 = 250661) (by norm_num)
theorem B1815317 : Blo 443779 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B668453 : Blo 443779 668453 := bbase (se 4 (by rfl) ⟨62667, by rfl⟩ : syracuseStep 668453 = 125335) (by norm_num)
theorem B668477 : Blo 443779 668477 := bbase (se 3 (by rfl) ⟨125339, by rfl⟩ : syracuseStep 668477 = 250679) (by norm_num)
theorem B668501 : Blo 443779 668501 := bbase (se 9 (by rfl) ⟨1958, by rfl⟩ : syracuseStep 668501 = 3917) (by norm_num)
theorem B668525 : Blo 443779 668525 := bbase (se 3 (by rfl) ⟨125348, by rfl⟩ : syracuseStep 668525 = 250697) (by norm_num)
theorem B668549 : Blo 443779 668549 := bbase (se 4 (by rfl) ⟨62676, by rfl⟩ : syracuseStep 668549 = 125353) (by norm_num)
theorem B1127317 : Blo 443779 1127317 := bbase (se 6 (by rfl) ⟨26421, by rfl⟩ : syracuseStep 1127317 = 52843) (by norm_num)
theorem B668573 : Blo 443779 668573 := bbase (se 3 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 668573 = 250715) (by norm_num)
theorem B2536373 : Blo 443779 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B668597 : Blo 443779 668597 := bbase (se 5 (by rfl) ⟨31340, by rfl⟩ : syracuseStep 668597 = 62681) (by norm_num)
theorem B603061 : Blo 443779 603061 := bbase (se 5 (by rfl) ⟨28268, by rfl⟩ : syracuseStep 603061 = 56537) (by norm_num)
theorem B668621 : Blo 443779 668621 := bbase (se 3 (by rfl) ⟨125366, by rfl⟩ : syracuseStep 668621 = 250733) (by norm_num)
theorem B1029077 : Blo 443779 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B668645 : Blo 443779 668645 := bbase (se 4 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 668645 = 125371) (by norm_num)
theorem B668669 : Blo 443779 668669 := bbase (se 3 (by rfl) ⟨125375, by rfl⟩ : syracuseStep 668669 = 250751) (by norm_num)
theorem B1127429 : Blo 443779 1127429 := bbase (se 4 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 1127429 = 211393) (by norm_num)
theorem B668693 : Blo 443779 668693 := bbase (se 6 (by rfl) ⟨15672, by rfl⟩ : syracuseStep 668693 = 31345) (by norm_num)
theorem B668717 : Blo 443779 668717 := bbase (se 3 (by rfl) ⟨125384, by rfl⟩ : syracuseStep 668717 = 250769) (by norm_num)
theorem B668741 : Blo 443779 668741 := bbase (se 4 (by rfl) ⟨62694, by rfl⟩ : syracuseStep 668741 = 125389) (by norm_num)
theorem B668765 : Blo 443779 668765 := bbase (se 3 (by rfl) ⟨125393, by rfl⟩ : syracuseStep 668765 = 250787) (by norm_num)
theorem B668789 : Blo 443779 668789 := bbase (se 5 (by rfl) ⟨31349, by rfl⟩ : syracuseStep 668789 = 62699) (by norm_num)
theorem B668813 : Blo 443779 668813 := bbase (se 3 (by rfl) ⟨125402, by rfl⟩ : syracuseStep 668813 = 250805) (by norm_num)
theorem B668837 : Blo 443779 668837 := bbase (se 4 (by rfl) ⟨62703, by rfl⟩ : syracuseStep 668837 = 125407) (by norm_num)
theorem B668861 : Blo 443779 668861 := bbase (se 3 (by rfl) ⟨125411, by rfl⟩ : syracuseStep 668861 = 250823) (by norm_num)
theorem B1127621 : Blo 443779 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B668885 : Blo 443779 668885 := bbase (se 7 (by rfl) ⟨7838, by rfl⟩ : syracuseStep 668885 = 15677) (by norm_num)
theorem B570601 : Blo 443779 570601 := bbase (se 2 (by rfl) ⟨213975, by rfl⟩ : syracuseStep 570601 = 427951) (by norm_num)
theorem B668909 : Blo 443779 668909 := bbase (se 3 (by rfl) ⟨125420, by rfl⟩ : syracuseStep 668909 = 250841) (by norm_num)
theorem B668933 : Blo 443779 668933 := bbase (se 4 (by rfl) ⟨62712, by rfl⟩ : syracuseStep 668933 = 125425) (by norm_num)
theorem B668957 : Blo 443779 668957 := bbase (se 3 (by rfl) ⟨125429, by rfl⟩ : syracuseStep 668957 = 250859) (by norm_num)
theorem B668981 : Blo 443779 668981 := bbase (se 5 (by rfl) ⟨31358, by rfl⟩ : syracuseStep 668981 = 62717) (by norm_num)
theorem B669005 : Blo 443779 669005 := bbase (se 3 (by rfl) ⟨125438, by rfl⟩ : syracuseStep 669005 = 250877) (by norm_num)
theorem B669029 : Blo 443779 669029 := bbase (se 4 (by rfl) ⟨62721, by rfl⟩ : syracuseStep 669029 = 125443) (by norm_num)
theorem B669053 : Blo 443779 669053 := bbase (se 3 (by rfl) ⟨125447, by rfl⟩ : syracuseStep 669053 = 250895) (by norm_num)
theorem B669077 : Blo 443779 669077 := bbase (se 6 (by rfl) ⟨15681, by rfl⟩ : syracuseStep 669077 = 31363) (by norm_num)
theorem B669101 : Blo 443779 669101 := bbase (se 3 (by rfl) ⟨125456, by rfl⟩ : syracuseStep 669101 = 250913) (by norm_num)
theorem B636349 : Blo 443779 636349 := bbase (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) (by norm_num)
theorem B669125 : Blo 443779 669125 := bbase (se 4 (by rfl) ⟨62730, by rfl⟩ : syracuseStep 669125 = 125461) (by norm_num)
theorem B669149 : Blo 443779 669149 := bbase (se 3 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 669149 = 250931) (by norm_num)
theorem B669173 : Blo 443779 669173 := bbase (se 5 (by rfl) ⟨31367, by rfl⟩ : syracuseStep 669173 = 62735) (by norm_num)
theorem B669197 : Blo 443779 669197 := bbase (se 3 (by rfl) ⟨125474, by rfl⟩ : syracuseStep 669197 = 250949) (by norm_num)
theorem B1127965 : Blo 443779 1127965 := bbase (se 3 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 1127965 = 422987) (by norm_num)
theorem B669221 : Blo 443779 669221 := bbase (se 4 (by rfl) ⟨62739, by rfl⟩ : syracuseStep 669221 = 125479) (by norm_num)
theorem B669245 : Blo 443779 669245 := bbase (se 3 (by rfl) ⟨125483, by rfl⟩ : syracuseStep 669245 = 250967) (by norm_num)
theorem B669269 : Blo 443779 669269 := bbase (se 8 (by rfl) ⟨3921, by rfl⟩ : syracuseStep 669269 = 7843) (by norm_num)
theorem B669293 : Blo 443779 669293 := bbase (se 3 (by rfl) ⟨125492, by rfl⟩ : syracuseStep 669293 = 250985) (by norm_num)
theorem B570997 : Blo 443779 570997 := bbase (se 5 (by rfl) ⟨26765, by rfl⟩ : syracuseStep 570997 = 53531) (by norm_num)
theorem B669317 : Blo 443779 669317 := bbase (se 4 (by rfl) ⟨62748, by rfl⟩ : syracuseStep 669317 = 125497) (by norm_num)
theorem B1128077 : Blo 443779 1128077 := bbase (se 3 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 1128077 = 423029) (by norm_num)
theorem B669341 : Blo 443779 669341 := bbase (se 3 (by rfl) ⟨125501, by rfl⟩ : syracuseStep 669341 = 251003) (by norm_num)
theorem B669365 : Blo 443779 669365 := bbase (se 5 (by rfl) ⟨31376, by rfl⟩ : syracuseStep 669365 = 62753) (by norm_num)
theorem B669389 : Blo 443779 669389 := bbase (se 3 (by rfl) ⟨125510, by rfl⟩ : syracuseStep 669389 = 251021) (by norm_num)
theorem B669413 : Blo 443779 669413 := bbase (se 4 (by rfl) ⟨62757, by rfl⟩ : syracuseStep 669413 = 125515) (by norm_num)
theorem B669437 : Blo 443779 669437 := bbase (se 3 (by rfl) ⟨125519, by rfl⟩ : syracuseStep 669437 = 251039) (by norm_num)
theorem B669461 : Blo 443779 669461 := bbase (se 6 (by rfl) ⟨15690, by rfl⟩ : syracuseStep 669461 = 31381) (by norm_num)
theorem B669485 : Blo 443779 669485 := bbase (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) (by norm_num)
theorem B3094325 : Blo 443779 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B3815221 : Blo 443779 3815221 := bbase (se 5 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 3815221 = 357677) (by norm_num)
theorem B669509 : Blo 443779 669509 := bbase (se 4 (by rfl) ⟨62766, by rfl⟩ : syracuseStep 669509 = 125533) (by norm_num)
theorem B1128269 : Blo 443779 1128269 := bbase (se 3 (by rfl) ⟨211550, by rfl⟩ : syracuseStep 1128269 = 423101) (by norm_num)
theorem B669533 : Blo 443779 669533 := bbase (se 3 (by rfl) ⟨125537, by rfl⟩ : syracuseStep 669533 = 251075) (by norm_num)
theorem B669557 : Blo 443779 669557 := bbase (se 5 (by rfl) ⟨31385, by rfl⟩ : syracuseStep 669557 = 62771) (by norm_num)
theorem B669581 : Blo 443779 669581 := bbase (se 3 (by rfl) ⟨125546, by rfl⟩ : syracuseStep 669581 = 251093) (by norm_num)
theorem B669605 : Blo 443779 669605 := bbase (se 4 (by rfl) ⟨62775, by rfl⟩ : syracuseStep 669605 = 125551) (by norm_num)
theorem B669629 : Blo 443779 669629 := bbase (se 3 (by rfl) ⟨125555, by rfl⟩ : syracuseStep 669629 = 251111) (by norm_num)
theorem B669653 : Blo 443779 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B669677 : Blo 443779 669677 := bbase (se 3 (by rfl) ⟨125564, by rfl⟩ : syracuseStep 669677 = 251129) (by norm_num)
theorem B669701 : Blo 443779 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B604165 : Blo 443779 604165 := bbase (se 4 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 604165 = 113281) (by norm_num)
theorem B636941 : Blo 443779 636941 := bbase (se 3 (by rfl) ⟨119426, by rfl⟩ : syracuseStep 636941 = 238853) (by norm_num)
theorem B669725 : Blo 443779 669725 := bbase (se 3 (by rfl) ⟨125573, by rfl⟩ : syracuseStep 669725 = 251147) (by norm_num)
theorem B669749 : Blo 443779 669749 := bbase (se 5 (by rfl) ⟨31394, by rfl⟩ : syracuseStep 669749 = 62789) (by norm_num)
theorem B669773 : Blo 443779 669773 := bbase (se 3 (by rfl) ⟨125582, by rfl⟩ : syracuseStep 669773 = 251165) (by norm_num)
theorem B637021 : Blo 443779 637021 := bbase (se 3 (by rfl) ⟨119441, by rfl⟩ : syracuseStep 637021 = 238883) (by norm_num)
theorem B669797 : Blo 443779 669797 := bbase (se 4 (by rfl) ⟨62793, by rfl⟩ : syracuseStep 669797 = 125587) (by norm_num)
theorem B669821 : Blo 443779 669821 := bbase (se 3 (by rfl) ⟨125591, by rfl⟩ : syracuseStep 669821 = 251183) (by norm_num)
theorem B669845 : Blo 443779 669845 := bbase (se 6 (by rfl) ⟨15699, by rfl⟩ : syracuseStep 669845 = 31399) (by norm_num)
theorem B1128613 : Blo 443779 1128613 := bbase (se 4 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 1128613 = 211615) (by norm_num)
theorem B669869 : Blo 443779 669869 := bbase (se 3 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 669869 = 251201) (by norm_num)
theorem B2406581 : Blo 443779 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B669893 : Blo 443779 669893 := bbase (se 4 (by rfl) ⟨62802, by rfl⟩ : syracuseStep 669893 = 125605) (by norm_num)
theorem B2865365 : Blo 443779 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B637141 : Blo 443779 637141 := bbase (se 7 (by rfl) ⟨7466, by rfl⟩ : syracuseStep 637141 = 14933) (by norm_num)
theorem B669917 : Blo 443779 669917 := bbase (se 3 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 669917 = 251219) (by norm_num)
theorem B669941 : Blo 443779 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B669965 : Blo 443779 669965 := bbase (se 3 (by rfl) ⟨125618, by rfl⟩ : syracuseStep 669965 = 251237) (by norm_num)
theorem B1128725 : Blo 443779 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B604445 : Blo 443779 604445 := bbase (se 3 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 604445 = 226667) (by norm_num)
theorem B669989 : Blo 443779 669989 := bbase (se 4 (by rfl) ⟨62811, by rfl⟩ : syracuseStep 669989 = 125623) (by norm_num)
theorem B637237 : Blo 443779 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B670013 : Blo 443779 670013 := bbase (se 3 (by rfl) ⟨125627, by rfl⟩ : syracuseStep 670013 = 251255) (by norm_num)
theorem B670037 : Blo 443779 670037 := bbase (se 10 (by rfl) ⟨981, by rfl⟩ : syracuseStep 670037 = 1963) (by norm_num)
theorem B670061 : Blo 443779 670061 := bbase (se 3 (by rfl) ⟨125636, by rfl⟩ : syracuseStep 670061 = 251273) (by norm_num)
theorem B670085 : Blo 443779 670085 := bbase (se 4 (by rfl) ⟨62820, by rfl⟩ : syracuseStep 670085 = 125641) (by norm_num)
theorem B506261 : Blo 443779 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B670109 : Blo 443779 670109 := bbase (se 3 (by rfl) ⟨125645, by rfl⟩ : syracuseStep 670109 = 251291) (by norm_num)
theorem B670133 : Blo 443779 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B670157 : Blo 443779 670157 := bbase (se 3 (by rfl) ⟨125654, by rfl⟩ : syracuseStep 670157 = 251309) (by norm_num)
theorem B3422677 : Blo 443779 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B1128917 : Blo 443779 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B670181 : Blo 443779 670181 := bbase (se 4 (by rfl) ⟨62829, by rfl⟩ : syracuseStep 670181 = 125659) (by norm_num)
theorem B670205 : Blo 443779 670205 := bbase (se 3 (by rfl) ⟨125663, by rfl⟩ : syracuseStep 670205 = 251327) (by norm_num)
theorem B6404629 : Blo 443779 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B670229 : Blo 443779 670229 := bbase (se 6 (by rfl) ⟨15708, by rfl⟩ : syracuseStep 670229 = 31417) (by norm_num)
theorem B670253 : Blo 443779 670253 := bbase (se 3 (by rfl) ⟨125672, by rfl⟩ : syracuseStep 670253 = 251345) (by norm_num)
theorem B670277 : Blo 443779 670277 := bbase (se 4 (by rfl) ⟨62838, by rfl⟩ : syracuseStep 670277 = 125677) (by norm_num)
theorem B670301 : Blo 443779 670301 := bbase (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) (by norm_num)
theorem B670325 : Blo 443779 670325 := bbase (se 5 (by rfl) ⟨31421, by rfl⟩ : syracuseStep 670325 = 62843) (by norm_num)
theorem B670349 : Blo 443779 670349 := bbase (se 3 (by rfl) ⟨125690, by rfl⟩ : syracuseStep 670349 = 251381) (by norm_num)
theorem B670373 : Blo 443779 670373 := bbase (se 4 (by rfl) ⟨62847, by rfl⟩ : syracuseStep 670373 = 125695) (by norm_num)
theorem B670397 : Blo 443779 670397 := bbase (se 3 (by rfl) ⟨125699, by rfl⟩ : syracuseStep 670397 = 251399) (by norm_num)
theorem B670421 : Blo 443779 670421 := bbase (se 7 (by rfl) ⟨7856, by rfl⟩ : syracuseStep 670421 = 15713) (by norm_num)
theorem B670445 : Blo 443779 670445 := bbase (se 3 (by rfl) ⟨125708, by rfl⟩ : syracuseStep 670445 = 251417) (by norm_num)
theorem B670469 : Blo 443779 670469 := bbase (se 4 (by rfl) ⟨62856, by rfl⟩ : syracuseStep 670469 = 125713) (by norm_num)
theorem B670493 : Blo 443779 670493 := bbase (se 3 (by rfl) ⟨125717, by rfl⟩ : syracuseStep 670493 = 251435) (by norm_num)
theorem B1129261 : Blo 443779 1129261 := bbase (se 3 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 1129261 = 423473) (by norm_num)
theorem B670517 : Blo 443779 670517 := bbase (se 5 (by rfl) ⟨31430, by rfl⟩ : syracuseStep 670517 = 62861) (by norm_num)
theorem B670541 : Blo 443779 670541 := bbase (se 3 (by rfl) ⟨125726, by rfl⟩ : syracuseStep 670541 = 251453) (by norm_num)
theorem B670565 : Blo 443779 670565 := bbase (se 4 (by rfl) ⟨62865, by rfl⟩ : syracuseStep 670565 = 125731) (by norm_num)
theorem B670589 : Blo 443779 670589 := bbase (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) (by norm_num)
theorem B670613 : Blo 443779 670613 := bbase (se 6 (by rfl) ⟨15717, by rfl⟩ : syracuseStep 670613 = 31435) (by norm_num)
theorem B1129373 : Blo 443779 1129373 := bbase (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) (by norm_num)
theorem B670637 : Blo 443779 670637 := bbase (se 3 (by rfl) ⟨125744, by rfl⟩ : syracuseStep 670637 = 251489) (by norm_num)
theorem B801733 : Blo 443779 801733 := bbase (se 4 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 801733 = 150325) (by norm_num)
theorem B670661 : Blo 443779 670661 := bbase (se 4 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 670661 = 125749) (by norm_num)
theorem B670685 : Blo 443779 670685 := bbase (se 3 (by rfl) ⟨125753, by rfl⟩ : syracuseStep 670685 = 251507) (by norm_num)
theorem B670709 : Blo 443779 670709 := bbase (se 5 (by rfl) ⟨31439, by rfl⟩ : syracuseStep 670709 = 62879) (by norm_num)
theorem B670733 : Blo 443779 670733 := bbase (se 3 (by rfl) ⟨125762, by rfl⟩ : syracuseStep 670733 = 251525) (by norm_num)
theorem B1424405 : Blo 443779 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B670757 : Blo 443779 670757 := bbase (se 4 (by rfl) ⟨62883, by rfl⟩ : syracuseStep 670757 = 125767) (by norm_num)
theorem B670781 : Blo 443779 670781 := bbase (se 3 (by rfl) ⟨125771, by rfl⟩ : syracuseStep 670781 = 251543) (by norm_num)
theorem B670805 : Blo 443779 670805 := bbase (se 8 (by rfl) ⟨3930, by rfl⟩ : syracuseStep 670805 = 7861) (by norm_num)
theorem B1129565 : Blo 443779 1129565 := bbase (se 3 (by rfl) ⟨211793, by rfl⟩ : syracuseStep 1129565 = 423587) (by norm_num)
theorem B670829 : Blo 443779 670829 := bbase (se 3 (by rfl) ⟨125780, by rfl⟩ : syracuseStep 670829 = 251561) (by norm_num)
theorem B670853 : Blo 443779 670853 := bbase (se 4 (by rfl) ⟨62892, by rfl⟩ : syracuseStep 670853 = 125785) (by norm_num)
theorem B965773 : Blo 443779 965773 := bbase (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) (by norm_num)
theorem B998549 : Blo 443779 998549 := bbase (se 6 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 998549 = 46807) (by norm_num)
theorem B670877 : Blo 443779 670877 := bbase (se 3 (by rfl) ⟨125789, by rfl⟩ : syracuseStep 670877 = 251579) (by norm_num)
theorem B670901 : Blo 443779 670901 := bbase (se 5 (by rfl) ⟨31448, by rfl⟩ : syracuseStep 670901 = 62897) (by norm_num)
theorem B670925 : Blo 443779 670925 := bbase (se 3 (by rfl) ⟨125798, by rfl⟩ : syracuseStep 670925 = 251597) (by norm_num)
theorem B998621 : Blo 443779 998621 := bbase (se 3 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 998621 = 374483) (by norm_num)
theorem B670949 : Blo 443779 670949 := bbase (se 4 (by rfl) ⟨62901, by rfl⟩ : syracuseStep 670949 = 125803) (by norm_num)
theorem B670973 : Blo 443779 670973 := bbase (se 3 (by rfl) ⟨125807, by rfl⟩ : syracuseStep 670973 = 251615) (by norm_num)
theorem B670997 : Blo 443779 670997 := bbase (se 6 (by rfl) ⟨15726, by rfl⟩ : syracuseStep 670997 = 31453) (by norm_num)
theorem B998693 : Blo 443779 998693 := bbase (se 4 (by rfl) ⟨93627, by rfl⟩ : syracuseStep 998693 = 187255) (by norm_num)
theorem B671021 : Blo 443779 671021 := bbase (se 3 (by rfl) ⟨125816, by rfl⟩ : syracuseStep 671021 = 251633) (by norm_num)
theorem B671045 : Blo 443779 671045 := bbase (se 4 (by rfl) ⟨62910, by rfl⟩ : syracuseStep 671045 = 125821) (by norm_num)
theorem B671069 : Blo 443779 671069 := bbase (se 3 (by rfl) ⟨125825, by rfl⟩ : syracuseStep 671069 = 251651) (by norm_num)
theorem B998765 : Blo 443779 998765 := bbase (se 3 (by rfl) ⟨187268, by rfl⟩ : syracuseStep 998765 = 374537) (by norm_num)
theorem B671093 : Blo 443779 671093 := bbase (se 5 (by rfl) ⟨31457, by rfl⟩ : syracuseStep 671093 = 62915) (by norm_num)
theorem B671117 : Blo 443779 671117 := bbase (se 3 (by rfl) ⟨125834, by rfl⟩ : syracuseStep 671117 = 251669) (by norm_num)
theorem B671141 : Blo 443779 671141 := bbase (se 4 (by rfl) ⟨62919, by rfl⟩ : syracuseStep 671141 = 125839) (by norm_num)
theorem B474545 : Blo 443779 474545 := bbase (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) (by norm_num)
theorem B998837 : Blo 443779 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B1129909 : Blo 443779 1129909 := bbase (se 5 (by rfl) ⟨52964, by rfl⟩ : syracuseStep 1129909 = 105929) (by norm_num)
theorem B671165 : Blo 443779 671165 := bbase (se 3 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 671165 = 251687) (by norm_num)
theorem B671189 : Blo 443779 671189 := bbase (se 7 (by rfl) ⟨7865, by rfl⟩ : syracuseStep 671189 = 15731) (by norm_num)
theorem B1687013 : Blo 443779 1687013 := bbase (se 4 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 1687013 = 316315) (by norm_num)
theorem B671213 : Blo 443779 671213 := bbase (se 3 (by rfl) ⟨125852, by rfl⟩ : syracuseStep 671213 = 251705) (by norm_num)
theorem B998909 : Blo 443779 998909 := bbase (se 3 (by rfl) ⟨187295, by rfl⟩ : syracuseStep 998909 = 374591) (by norm_num)
theorem B2145797 : Blo 443779 2145797 := bbase (se 4 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 2145797 = 402337) (by norm_num)
theorem B671237 : Blo 443779 671237 := bbase (se 4 (by rfl) ⟨62928, by rfl⟩ : syracuseStep 671237 = 125857) (by norm_num)
theorem B900629 : Blo 443779 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B671261 : Blo 443779 671261 := bbase (se 3 (by rfl) ⟨125861, by rfl⟩ : syracuseStep 671261 = 251723) (by norm_num)
theorem B1130021 : Blo 443779 1130021 := bbase (se 4 (by rfl) ⟨105939, by rfl⟩ : syracuseStep 1130021 = 211879) (by norm_num)
theorem B671285 : Blo 443779 671285 := bbase (se 5 (by rfl) ⟨31466, by rfl⟩ : syracuseStep 671285 = 62933) (by norm_num)
theorem B998981 : Blo 443779 998981 := bbase (se 4 (by rfl) ⟨93654, by rfl⟩ : syracuseStep 998981 = 187309) (by norm_num)
theorem B671309 : Blo 443779 671309 := bbase (se 3 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 671309 = 251741) (by norm_num)
theorem B671333 : Blo 443779 671333 := bbase (se 4 (by rfl) ⟨62937, by rfl⟩ : syracuseStep 671333 = 125875) (by norm_num)
theorem B671357 : Blo 443779 671357 := bbase (se 3 (by rfl) ⟨125879, by rfl⟩ : syracuseStep 671357 = 251759) (by norm_num)
theorem B999053 : Blo 443779 999053 := bbase (se 3 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 999053 = 374645) (by norm_num)
theorem B671381 : Blo 443779 671381 := bbase (se 6 (by rfl) ⟨15735, by rfl⟩ : syracuseStep 671381 = 31471) (by norm_num)
theorem B671405 : Blo 443779 671405 := bbase (se 3 (by rfl) ⟨125888, by rfl⟩ : syracuseStep 671405 = 251777) (by norm_num)
theorem B671429 : Blo 443779 671429 := bbase (se 4 (by rfl) ⟨62946, by rfl⟩ : syracuseStep 671429 = 125893) (by norm_num)
theorem B507593 : Blo 443779 507593 := bbase (se 2 (by rfl) ⟨190347, by rfl⟩ : syracuseStep 507593 = 380695) (by norm_num)
theorem B999125 : Blo 443779 999125 := bbase (se 7 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 999125 = 23417) (by norm_num)
theorem B671453 : Blo 443779 671453 := bbase (se 3 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 671453 = 251795) (by norm_num)
theorem B1130213 : Blo 443779 1130213 := bbase (se 4 (by rfl) ⟨105957, by rfl⟩ : syracuseStep 1130213 = 211915) (by norm_num)
theorem B802541 : Blo 443779 802541 := bbase (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) (by norm_num)
theorem B3817205 : Blo 443779 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B671477 : Blo 443779 671477 := bbase (se 5 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 671477 = 62951) (by norm_num)
theorem B1687301 : Blo 443779 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B671501 : Blo 443779 671501 := bbase (se 3 (by rfl) ⟨125906, by rfl⟩ : syracuseStep 671501 = 251813) (by norm_num)
theorem B999197 : Blo 443779 999197 := bbase (se 3 (by rfl) ⟨187349, by rfl⟩ : syracuseStep 999197 = 374699) (by norm_num)
theorem B671525 : Blo 443779 671525 := bbase (se 4 (by rfl) ⟨62955, by rfl⟩ : syracuseStep 671525 = 125911) (by norm_num)
theorem B671549 : Blo 443779 671549 := bbase (se 3 (by rfl) ⟨125915, by rfl⟩ : syracuseStep 671549 = 251831) (by norm_num)
theorem B671573 : Blo 443779 671573 := bbase (se 9 (by rfl) ⟨1967, by rfl⟩ : syracuseStep 671573 = 3935) (by norm_num)
theorem B999269 : Blo 443779 999269 := bbase (se 4 (by rfl) ⟨93681, by rfl⟩ : syracuseStep 999269 = 187363) (by norm_num)
theorem B474989 : Blo 443779 474989 := bbase (se 3 (by rfl) ⟨89060, by rfl⟩ : syracuseStep 474989 = 178121) (by norm_num)
theorem B671597 : Blo 443779 671597 := bbase (se 3 (by rfl) ⟨125924, by rfl⟩ : syracuseStep 671597 = 251849) (by norm_num)
theorem B671621 : Blo 443779 671621 := bbase (se 4 (by rfl) ⟨62964, by rfl⟩ : syracuseStep 671621 = 125929) (by norm_num)
theorem B671645 : Blo 443779 671645 := bbase (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) (by norm_num)
theorem B999341 : Blo 443779 999341 := bbase (se 3 (by rfl) ⟨187376, by rfl⟩ : syracuseStep 999341 = 374753) (by norm_num)
theorem B671669 : Blo 443779 671669 := bbase (se 5 (by rfl) ⟨31484, by rfl⟩ : syracuseStep 671669 = 62969) (by norm_num)
theorem B999413 : Blo 443779 999413 := bbase (se 5 (by rfl) ⟨46847, by rfl⟩ : syracuseStep 999413 = 93695) (by norm_num)
theorem B5783573 : Blo 443779 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B999485 : Blo 443779 999485 := bbase (se 3 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 999485 = 374807) (by norm_num)
theorem B1130557 : Blo 443779 1130557 := bbase (se 3 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 1130557 = 423959) (by norm_num)
theorem B475237 : Blo 443779 475237 := bbase (se 4 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 475237 = 89107) (by norm_num)
theorem B999557 : Blo 443779 999557 := bbase (se 4 (by rfl) ⟨93708, by rfl⟩ : syracuseStep 999557 = 187417) (by norm_num)
theorem B1130669 : Blo 443779 1130669 := bbase (se 3 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 1130669 = 424001) (by norm_num)
theorem B999629 : Blo 443779 999629 := bbase (se 3 (by rfl) ⟨187430, by rfl⟩ : syracuseStep 999629 = 374861) (by norm_num)
theorem B4079861 : Blo 443779 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B999701 : Blo 443779 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B803117 : Blo 443779 803117 := bbase (se 3 (by rfl) ⟨150584, by rfl⟩ : syracuseStep 803117 = 301169) (by norm_num)
theorem B999773 : Blo 443779 999773 := bbase (se 3 (by rfl) ⟨187457, by rfl⟩ : syracuseStep 999773 = 374915) (by norm_num)
theorem B1130861 : Blo 443779 1130861 := bbase (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) (by norm_num)
theorem B999845 : Blo 443779 999845 := bbase (se 4 (by rfl) ⟨93735, by rfl⟩ : syracuseStep 999845 = 187471) (by norm_num)
theorem B999917 : Blo 443779 999917 := bbase (se 3 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 999917 = 374969) (by norm_num)
theorem B6242837 : Blo 443779 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B475669 : Blo 443779 475669 := bbase (se 6 (by rfl) ⟨11148, by rfl⟩ : syracuseStep 475669 = 22297) (by norm_num)
theorem B999989 : Blo 443779 999989 := bbase (se 5 (by rfl) ⟨46874, by rfl⟩ : syracuseStep 999989 = 93749) (by norm_num)
theorem B475741 : Blo 443779 475741 := bbase (se 3 (by rfl) ⟨89201, by rfl⟩ : syracuseStep 475741 = 178403) (by norm_num)
theorem B1000061 : Blo 443779 1000061 := bbase (se 3 (by rfl) ⟨187511, by rfl⟩ : syracuseStep 1000061 = 375023) (by norm_num)
theorem B1000133 : Blo 443779 1000133 := bbase (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) (by norm_num)
theorem B541381 : Blo 443779 541381 := bbase (se 4 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 541381 = 101509) (by norm_num)
theorem B1131205 : Blo 443779 1131205 := bbase (se 4 (by rfl) ⟨106050, by rfl⟩ : syracuseStep 1131205 = 212101) (by norm_num)
theorem B1000205 : Blo 443779 1000205 := bbase (se 3 (by rfl) ⟨187538, by rfl⟩ : syracuseStep 1000205 = 375077) (by norm_num)
theorem B1131317 : Blo 443779 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B1000277 : Blo 443779 1000277 := bbase (se 9 (by rfl) ⟨2930, by rfl⟩ : syracuseStep 1000277 = 5861) (by norm_num)
theorem B1000349 : Blo 443779 1000349 := bbase (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) (by norm_num)
theorem B1688485 : Blo 443779 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B476113 : Blo 443779 476113 := bbase (se 2 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 476113 = 357085) (by norm_num)
theorem B1000421 : Blo 443779 1000421 := bbase (se 4 (by rfl) ⟨93789, by rfl⟩ : syracuseStep 1000421 = 187579) (by norm_num)
theorem B1131509 : Blo 443779 1131509 := bbase (se 5 (by rfl) ⟨53039, by rfl⟩ : syracuseStep 1131509 = 106079) (by norm_num)
theorem B1000493 : Blo 443779 1000493 := bbase (se 3 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 1000493 = 375185) (by norm_num)
theorem B803909 : Blo 443779 803909 := bbase (se 4 (by rfl) ⟨75366, by rfl⟩ : syracuseStep 803909 = 150733) (by norm_num)
theorem B1000565 : Blo 443779 1000565 := bbase (se 5 (by rfl) ⟨46901, by rfl⟩ : syracuseStep 1000565 = 93803) (by norm_num)
theorem B1000637 : Blo 443779 1000637 := bbase (se 3 (by rfl) ⟨187619, by rfl⟩ : syracuseStep 1000637 = 375239) (by norm_num)
theorem B1688789 : Blo 443779 1688789 := bbase (se 7 (by rfl) ⟨19790, by rfl⟩ : syracuseStep 1688789 = 39581) (by norm_num)
theorem B804053 : Blo 443779 804053 := bbase (se 7 (by rfl) ⟨9422, by rfl⟩ : syracuseStep 804053 = 18845) (by norm_num)
theorem B1000709 : Blo 443779 1000709 := bbase (se 4 (by rfl) ⟨93816, by rfl⟩ : syracuseStep 1000709 = 187633) (by norm_num)
theorem B476489 : Blo 443779 476489 := bbase (se 2 (by rfl) ⟨178683, by rfl⟩ : syracuseStep 476489 = 357367) (by norm_num)
theorem B1000781 : Blo 443779 1000781 := bbase (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) (by norm_num)
theorem B1131853 : Blo 443779 1131853 := bbase (se 3 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 1131853 = 424445) (by norm_num)
theorem B509317 : Blo 443779 509317 := bbase (se 4 (by rfl) ⟨47748, by rfl⟩ : syracuseStep 509317 = 95497) (by norm_num)
theorem B476561 : Blo 443779 476561 := bbase (se 2 (by rfl) ⟨178710, by rfl⟩ : syracuseStep 476561 = 357421) (by norm_num)
theorem B1000853 : Blo 443779 1000853 := bbase (se 6 (by rfl) ⟨23457, by rfl⟩ : syracuseStep 1000853 = 46915) (by norm_num)
theorem B1131965 : Blo 443779 1131965 := bbase (se 3 (by rfl) ⟨212243, by rfl⟩ : syracuseStep 1131965 = 424487) (by norm_num)
theorem B1000925 : Blo 443779 1000925 := bbase (se 3 (by rfl) ⟨187673, by rfl⟩ : syracuseStep 1000925 = 375347) (by norm_num)
theorem B1066517 : Blo 443779 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B1000997 : Blo 443779 1000997 := bbase (se 4 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 1000997 = 187687) (by norm_num)
theorem B476749 : Blo 443779 476749 := bbase (se 3 (by rfl) ⟨89390, by rfl⟩ : syracuseStep 476749 = 178781) (by norm_num)
theorem B1001069 : Blo 443779 1001069 := bbase (se 3 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 1001069 = 375401) (by norm_num)
theorem B1132157 : Blo 443779 1132157 := bbase (se 3 (by rfl) ⟨212279, by rfl⟩ : syracuseStep 1132157 = 424559) (by norm_num)
theorem B1001141 : Blo 443779 1001141 := bbase (se 5 (by rfl) ⟨46928, by rfl⟩ : syracuseStep 1001141 = 93857) (by norm_num)
theorem B1623797 : Blo 443779 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1001213 : Blo 443779 1001213 := bbase (se 3 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 1001213 = 375455) (by norm_num)
theorem B476933 : Blo 443779 476933 := bbase (se 4 (by rfl) ⟨44712, by rfl⟩ : syracuseStep 476933 = 89425) (by norm_num)
theorem B1001285 : Blo 443779 1001285 := bbase (se 4 (by rfl) ⟨93870, by rfl⟩ : syracuseStep 1001285 = 187741) (by norm_num)
theorem B1001357 : Blo 443779 1001357 := bbase (se 3 (by rfl) ⟨187754, by rfl⟩ : syracuseStep 1001357 = 375509) (by norm_num)
theorem B1066949 : Blo 443779 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B1001429 : Blo 443779 1001429 := bbase (se 7 (by rfl) ⟨11735, by rfl⟩ : syracuseStep 1001429 = 23471) (by norm_num)
theorem B1132501 : Blo 443779 1132501 := bbase (se 7 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 1132501 = 26543) (by norm_num)
theorem B1001501 : Blo 443779 1001501 := bbase (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) (by norm_num)
theorem B1132613 : Blo 443779 1132613 := bbase (se 4 (by rfl) ⟨106182, by rfl⟩ : syracuseStep 1132613 = 212365) (by norm_num)
theorem B1001573 : Blo 443779 1001573 := bbase (se 4 (by rfl) ⟨93897, by rfl⟩ : syracuseStep 1001573 = 187795) (by norm_num)
theorem B1427557 : Blo 443779 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B837749 : Blo 443779 837749 := bbase (se 5 (by rfl) ⟨39269, by rfl⟩ : syracuseStep 837749 = 78539) (by norm_num)
theorem B1001645 : Blo 443779 1001645 := bbase (se 3 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 1001645 = 375617) (by norm_num)
theorem B1001717 : Blo 443779 1001717 := bbase (se 5 (by rfl) ⟨46955, by rfl⟩ : syracuseStep 1001717 = 93911) (by norm_num)
theorem B1132805 : Blo 443779 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B1001789 : Blo 443779 1001789 := bbase (se 3 (by rfl) ⟨187835, by rfl⟩ : syracuseStep 1001789 = 375671) (by norm_num)
theorem B2148677 : Blo 443779 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B1001861 : Blo 443779 1001861 := bbase (se 4 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 1001861 = 187849) (by norm_num)
theorem B2574773 : Blo 443779 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B1001933 : Blo 443779 1001933 := bbase (se 3 (by rfl) ⟨187862, by rfl⟩ : syracuseStep 1001933 = 375725) (by norm_num)
theorem B903653 : Blo 443779 903653 := bbase (se 4 (by rfl) ⟨84717, by rfl⟩ : syracuseStep 903653 = 169435) (by norm_num)
theorem B477685 : Blo 443779 477685 := bbase (se 5 (by rfl) ⟨22391, by rfl⟩ : syracuseStep 477685 = 44783) (by norm_num)
theorem B1002005 : Blo 443779 1002005 := bbase (se 6 (by rfl) ⟨23484, by rfl⟩ : syracuseStep 1002005 = 46969) (by norm_num)
theorem B1067573 : Blo 443779 1067573 := bbase (se 5 (by rfl) ⟨50042, by rfl⟩ : syracuseStep 1067573 = 100085) (by norm_num)
theorem B477757 : Blo 443779 477757 := bbase (se 3 (by rfl) ⟨89579, by rfl⟩ : syracuseStep 477757 = 179159) (by norm_num)
theorem B1002077 : Blo 443779 1002077 := bbase (se 3 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 1002077 = 375779) (by norm_num)
theorem B1133149 : Blo 443779 1133149 := bbase (se 3 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 1133149 = 424931) (by norm_num)
theorem B1002149 : Blo 443779 1002149 := bbase (se 4 (by rfl) ⟨93951, by rfl⟩ : syracuseStep 1002149 = 187903) (by norm_num)
theorem B1133261 : Blo 443779 1133261 := bbase (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) (by norm_num)
theorem B1002221 : Blo 443779 1002221 := bbase (se 3 (by rfl) ⟨187916, by rfl⟩ : syracuseStep 1002221 = 375833) (by norm_num)
theorem B477937 : Blo 443779 477937 := bbase (se 2 (by rfl) ⟨179226, by rfl⟩ : syracuseStep 477937 = 358453) (by norm_num)
theorem B1264405 : Blo 443779 1264405 := bbase (se 6 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 1264405 = 59269) (by norm_num)
theorem B1002293 : Blo 443779 1002293 := bbase (se 5 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 1002293 = 93965) (by norm_num)
theorem B1526597 : Blo 443779 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B1002365 : Blo 443779 1002365 := bbase (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) (by norm_num)
theorem B871309 : Blo 443779 871309 := bbase (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) (by norm_num)
theorem B1264565 : Blo 443779 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B1002437 : Blo 443779 1002437 := bbase (se 4 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 1002437 = 187957) (by norm_num)
theorem B642053 : Blo 443779 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B1002509 : Blo 443779 1002509 := bbase (se 3 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 1002509 = 375941) (by norm_num)
theorem B2247749 : Blo 443779 2247749 := bbase (se 4 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 2247749 = 421453) (by norm_num)
theorem B674893 : Blo 443779 674893 := bbase (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) (by norm_num)
theorem B1002581 : Blo 443779 1002581 := bbase (se 8 (by rfl) ⟨5874, by rfl⟩ : syracuseStep 1002581 = 11749) (by norm_num)
theorem B674941 : Blo 443779 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B3394709 : Blo 443779 3394709 := bbase (se 6 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 3394709 = 159127) (by norm_num)
theorem B1002653 : Blo 443779 1002653 := bbase (se 3 (by rfl) ⟨187997, by rfl⟩ : syracuseStep 1002653 = 375995) (by norm_num)
theorem B1264805 : Blo 443779 1264805 := bbase (se 4 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 1264805 = 237151) (by norm_num)
theorem B1002725 : Blo 443779 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B1690901 : Blo 443779 1690901 := bbase (se 6 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 1690901 = 79261) (by norm_num)
theorem B1002797 : Blo 443779 1002797 := bbase (se 3 (by rfl) ⟨188024, by rfl⟩ : syracuseStep 1002797 = 376049) (by norm_num)
theorem B1625429 : Blo 443779 1625429 := bbase (se 11 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 1625429 = 2381) (by norm_num)
theorem B1264997 : Blo 443779 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B1002869 : Blo 443779 1002869 := bbase (se 5 (by rfl) ⟨47009, by rfl⟩ : syracuseStep 1002869 = 94019) (by norm_num)
theorem B1002941 : Blo 443779 1002941 := bbase (se 3 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 1002941 = 376103) (by norm_num)
theorem B1003013 : Blo 443779 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B1691189 : Blo 443779 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1003085 : Blo 443779 1003085 := bbase (se 3 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 1003085 = 376157) (by norm_num)
theorem B1003157 : Blo 443779 1003157 := bbase (se 6 (by rfl) ⟨23511, by rfl⟩ : syracuseStep 1003157 = 47023) (by norm_num)
theorem B1003229 : Blo 443779 1003229 := bbase (se 3 (by rfl) ⟨188105, by rfl⟩ : syracuseStep 1003229 = 376211) (by norm_num)
theorem B1003301 : Blo 443779 1003301 := bbase (se 4 (by rfl) ⟨94059, by rfl⟩ : syracuseStep 1003301 = 188119) (by norm_num)
theorem B872245 : Blo 443779 872245 := bbase (se 5 (by rfl) ⟨40886, by rfl⟩ : syracuseStep 872245 = 81773) (by norm_num)
theorem B4083509 : Blo 443779 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B642925 : Blo 443779 642925 := bbase (se 3 (by rfl) ⟨120548, by rfl⟩ : syracuseStep 642925 = 241097) (by norm_num)
theorem B1003373 : Blo 443779 1003373 := bbase (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) (by norm_num)
theorem B1003445 : Blo 443779 1003445 := bbase (se 5 (by rfl) ⟨47036, by rfl⟩ : syracuseStep 1003445 = 94073) (by norm_num)
theorem B2543605 : Blo 443779 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B1003517 : Blo 443779 1003517 := bbase (se 3 (by rfl) ⟨188159, by rfl⟩ : syracuseStep 1003517 = 376319) (by norm_num)
theorem B1003589 : Blo 443779 1003589 := bbase (se 4 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 1003589 = 188173) (by norm_num)
theorem B1003661 : Blo 443779 1003661 := bbase (se 3 (by rfl) ⟨188186, by rfl⟩ : syracuseStep 1003661 = 376373) (by norm_num)
theorem B643253 : Blo 443779 643253 := bbase (se 5 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 643253 = 60305) (by norm_num)
theorem B1003733 : Blo 443779 1003733 := bbase (se 7 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 1003733 = 23525) (by norm_num)
theorem B1003805 : Blo 443779 1003805 := bbase (se 3 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 1003805 = 376427) (by norm_num)
theorem B1265989 : Blo 443779 1265989 := bbase (se 4 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 1265989 = 237373) (by norm_num)
theorem B2249045 : Blo 443779 2249045 := bbase (se 10 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 2249045 = 6589) (by norm_num)
theorem B1003877 : Blo 443779 1003877 := bbase (se 4 (by rfl) ⟨94113, by rfl⟩ : syracuseStep 1003877 = 188227) (by norm_num)
theorem B1003949 : Blo 443779 1003949 := bbase (se 3 (by rfl) ⟨188240, by rfl⟩ : syracuseStep 1003949 = 376481) (by norm_num)
theorem B2150869 : Blo 443779 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B1004021 : Blo 443779 1004021 := bbase (se 5 (by rfl) ⟨47063, by rfl⟩ : syracuseStep 1004021 = 94127) (by norm_num)
theorem B1921589 : Blo 443779 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B1004093 : Blo 443779 1004093 := bbase (se 3 (by rfl) ⟨188267, by rfl⟩ : syracuseStep 1004093 = 376535) (by norm_num)
theorem B1462853 : Blo 443779 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B1004165 : Blo 443779 1004165 := bbase (se 4 (by rfl) ⟨94140, by rfl⟩ : syracuseStep 1004165 = 188281) (by norm_num)
theorem B1004237 : Blo 443779 1004237 := bbase (se 3 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 1004237 = 376589) (by norm_num)
theorem B1692373 : Blo 443779 1692373 := bbase (se 7 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 1692373 = 39665) (by norm_num)
theorem B873181 : Blo 443779 873181 := bbase (se 3 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 873181 = 327443) (by norm_num)
theorem B1004309 : Blo 443779 1004309 := bbase (se 6 (by rfl) ⟨23538, by rfl⟩ : syracuseStep 1004309 = 47077) (by norm_num)
theorem B676669 : Blo 443779 676669 := bbase (se 3 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 676669 = 253751) (by norm_num)
theorem B1004381 : Blo 443779 1004381 := bbase (se 3 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 1004381 = 376643) (by norm_num)
theorem B1430389 : Blo 443779 1430389 := bbase (se 5 (by rfl) ⟨67049, by rfl⟩ : syracuseStep 1430389 = 134099) (by norm_num)
theorem B1004453 : Blo 443779 1004453 := bbase (se 4 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 1004453 = 188335) (by norm_num)
theorem B906149 : Blo 443779 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B1430453 : Blo 443779 1430453 := bbase (se 5 (by rfl) ⟨67052, by rfl⟩ : syracuseStep 1430453 = 134105) (by norm_num)
theorem B1004525 : Blo 443779 1004525 := bbase (se 3 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 1004525 = 376697) (by norm_num)
theorem B1692677 : Blo 443779 1692677 := bbase (se 4 (by rfl) ⟨158688, by rfl⟩ : syracuseStep 1692677 = 317377) (by norm_num)
theorem B1004597 : Blo 443779 1004597 := bbase (se 5 (by rfl) ⟨47090, by rfl⟩ : syracuseStep 1004597 = 94181) (by norm_num)
theorem B1004669 : Blo 443779 1004669 := bbase (se 3 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 1004669 = 376751) (by norm_num)
theorem B1004741 : Blo 443779 1004741 := bbase (se 4 (by rfl) ⟨94194, by rfl⟩ : syracuseStep 1004741 = 188389) (by norm_num)
theorem B1004813 : Blo 443779 1004813 := bbase (se 3 (by rfl) ⟨188402, by rfl⟩ : syracuseStep 1004813 = 376805) (by norm_num)
theorem B1004885 : Blo 443779 1004885 := bbase (se 17 (by rfl) ⟨11, by rfl⟩ : syracuseStep 1004885 = 23) (by norm_num)
theorem B1267093 : Blo 443779 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B1004957 : Blo 443779 1004957 := bbase (se 3 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 1004957 = 376859) (by norm_num)
theorem B1070533 : Blo 443779 1070533 := bbase (se 4 (by rfl) ⟨100362, by rfl⟩ : syracuseStep 1070533 = 200725) (by norm_num)
theorem B1005029 : Blo 443779 1005029 := bbase (se 4 (by rfl) ⟨94221, by rfl⟩ : syracuseStep 1005029 = 188443) (by norm_num)
theorem B1005101 : Blo 443779 1005101 := bbase (se 3 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 1005101 = 376913) (by norm_num)
theorem B2250341 : Blo 443779 2250341 := bbase (se 4 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 2250341 = 421939) (by norm_num)
theorem B1005173 : Blo 443779 1005173 := bbase (se 5 (by rfl) ⟨47117, by rfl⟩ : syracuseStep 1005173 = 94235) (by norm_num)
theorem B1070725 : Blo 443779 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1070765 : Blo 443779 1070765 := bbase (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) (by norm_num)
theorem B1005245 : Blo 443779 1005245 := bbase (se 3 (by rfl) ⟨188483, by rfl⟩ : syracuseStep 1005245 = 376967) (by norm_num)
theorem B1005317 : Blo 443779 1005317 := bbase (se 4 (by rfl) ⟨94248, by rfl⟩ : syracuseStep 1005317 = 188497) (by norm_num)
theorem B2709301 : Blo 443779 2709301 := bbase (se 5 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 2709301 = 253997) (by norm_num)
theorem B1005389 : Blo 443779 1005389 := bbase (se 3 (by rfl) ⟨188510, by rfl⟩ : syracuseStep 1005389 = 377021) (by norm_num)
theorem B579457 : Blo 443779 579457 := bbase (se 2 (by rfl) ⟨217296, by rfl⟩ : syracuseStep 579457 = 434593) (by norm_num)
theorem B1005461 : Blo 443779 1005461 := bbase (se 6 (by rfl) ⟨23565, by rfl⟩ : syracuseStep 1005461 = 47131) (by norm_num)
theorem B1071053 : Blo 443779 1071053 := bbase (se 3 (by rfl) ⟨200822, by rfl⟩ : syracuseStep 1071053 = 401645) (by norm_num)
theorem B1005533 : Blo 443779 1005533 := bbase (se 3 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 1005533 = 377075) (by norm_num)
theorem B1005605 : Blo 443779 1005605 := bbase (se 4 (by rfl) ⟨94275, by rfl⟩ : syracuseStep 1005605 = 188551) (by norm_num)
theorem B1005677 : Blo 443779 1005677 := bbase (se 3 (by rfl) ⟨188564, by rfl⟩ : syracuseStep 1005677 = 377129) (by norm_num)
theorem B1005749 : Blo 443779 1005749 := bbase (se 5 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 1005749 = 94289) (by norm_num)
theorem B1005821 : Blo 443779 1005821 := bbase (se 3 (by rfl) ⟨188591, by rfl⟩ : syracuseStep 1005821 = 377183) (by norm_num)
theorem B1005893 : Blo 443779 1005893 := bbase (se 4 (by rfl) ⟨94302, by rfl⟩ : syracuseStep 1005893 = 188605) (by norm_num)
theorem B18340181 : Blo 443779 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1005965 : Blo 443779 1005965 := bbase (se 3 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 1005965 = 377237) (by norm_num)
theorem B1006037 : Blo 443779 1006037 := bbase (se 7 (by rfl) ⟨11789, by rfl⟩ : syracuseStep 1006037 = 23579) (by norm_num)
theorem B711197 : Blo 443779 711197 := bbase (se 3 (by rfl) ⟨133349, by rfl⟩ : syracuseStep 711197 = 266699) (by norm_num)
theorem B1006109 : Blo 443779 1006109 := bbase (se 3 (by rfl) ⟨188645, by rfl⟩ : syracuseStep 1006109 = 377291) (by norm_num)
theorem B2546261 : Blo 443779 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1006181 : Blo 443779 1006181 := bbase (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) (by norm_num)
theorem B1006253 : Blo 443779 1006253 := bbase (se 3 (by rfl) ⟨188672, by rfl⟩ : syracuseStep 1006253 = 377345) (by norm_num)
theorem B1497797 : Blo 443779 1497797 := bbase (se 4 (by rfl) ⟨140418, by rfl⟩ : syracuseStep 1497797 = 280837) (by norm_num)
theorem B1006325 : Blo 443779 1006325 := bbase (se 5 (by rfl) ⟨47171, by rfl⟩ : syracuseStep 1006325 = 94343) (by norm_num)
theorem B842557 : Blo 443779 842557 := bbase (se 3 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 842557 = 315959) (by norm_num)
theorem B1006397 : Blo 443779 1006397 := bbase (se 3 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 1006397 = 377399) (by norm_num)
theorem B2251637 : Blo 443779 2251637 := bbase (se 5 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 2251637 = 211091) (by norm_num)
theorem B1268597 : Blo 443779 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B1006469 : Blo 443779 1006469 := bbase (se 4 (by rfl) ⟨94356, by rfl⟩ : syracuseStep 1006469 = 188713) (by norm_num)
theorem B1006541 : Blo 443779 1006541 := bbase (se 3 (by rfl) ⟨188726, by rfl⟩ : syracuseStep 1006541 = 377453) (by norm_num)
theorem B842717 : Blo 443779 842717 := bbase (se 3 (by rfl) ⟨158009, by rfl⟩ : syracuseStep 842717 = 316019) (by norm_num)
theorem B1006613 : Blo 443779 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B1694789 : Blo 443779 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B1006685 : Blo 443779 1006685 := bbase (se 3 (by rfl) ⟨188753, by rfl⟩ : syracuseStep 1006685 = 377507) (by norm_num)
theorem B842861 : Blo 443779 842861 := bbase (se 3 (by rfl) ⟨158036, by rfl⟩ : syracuseStep 842861 = 316073) (by norm_num)
theorem B1498229 : Blo 443779 1498229 := bbase (se 5 (by rfl) ⟨70229, by rfl⟩ : syracuseStep 1498229 = 140459) (by norm_num)
theorem B973973 : Blo 443779 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B1006757 : Blo 443779 1006757 := bbase (se 4 (by rfl) ⟨94383, by rfl⟩ : syracuseStep 1006757 = 188767) (by norm_num)
theorem B1006829 : Blo 443779 1006829 := bbase (se 3 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 1006829 = 377561) (by norm_num)
theorem B580853 : Blo 443779 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B1006901 : Blo 443779 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B1695077 : Blo 443779 1695077 := bbase (se 4 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 1695077 = 317827) (by norm_num)
theorem B1006973 : Blo 443779 1006973 := bbase (se 3 (by rfl) ⟨188807, by rfl⟩ : syracuseStep 1006973 = 377615) (by norm_num)
theorem B843149 : Blo 443779 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B1007045 : Blo 443779 1007045 := bbase (se 4 (by rfl) ⟨94410, by rfl⟩ : syracuseStep 1007045 = 188821) (by norm_num)
theorem B1007117 : Blo 443779 1007117 := bbase (se 3 (by rfl) ⟨188834, by rfl⟩ : syracuseStep 1007117 = 377669) (by norm_num)
theorem B1498661 : Blo 443779 1498661 := bbase (se 4 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 1498661 = 280999) (by norm_num)
theorem B843301 : Blo 443779 843301 := bbase (se 4 (by rfl) ⟨79059, by rfl⟩ : syracuseStep 843301 = 158119) (by norm_num)
theorem B1007189 : Blo 443779 1007189 := bbase (se 8 (by rfl) ⟨5901, by rfl⟩ : syracuseStep 1007189 = 11803) (by norm_num)
theorem B1007261 : Blo 443779 1007261 := bbase (se 3 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 1007261 = 377723) (by norm_num)
theorem B1007333 : Blo 443779 1007333 := bbase (se 4 (by rfl) ⟨94437, by rfl⟩ : syracuseStep 1007333 = 188875) (by norm_num)
theorem B1007405 : Blo 443779 1007405 := bbase (se 3 (by rfl) ⟨188888, by rfl⟩ : syracuseStep 1007405 = 377777) (by norm_num)
theorem B843605 : Blo 443779 843605 := bbase (se 9 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 843605 = 4943) (by norm_num)
theorem B1007477 : Blo 443779 1007477 := bbase (se 5 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 1007477 = 94451) (by norm_num)
theorem B1433477 : Blo 443779 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B712613 : Blo 443779 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B1499093 : Blo 443779 1499093 := bbase (se 7 (by rfl) ⟨17567, by rfl⟩ : syracuseStep 1499093 = 35135) (by norm_num)
theorem B483445 : Blo 443779 483445 := bbase (se 5 (by rfl) ⟨22661, by rfl⟩ : syracuseStep 483445 = 45323) (by norm_num)
theorem B712837 : Blo 443779 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B2252933 : Blo 443779 2252933 := bbase (se 4 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 2252933 = 422425) (by norm_num)
theorem B680293 : Blo 443779 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B1499525 : Blo 443779 1499525 := bbase (se 4 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 1499525 = 281161) (by norm_num)
theorem B1270181 : Blo 443779 1270181 := bbase (se 4 (by rfl) ⟨119079, by rfl⟩ : syracuseStep 1270181 = 238159) (by norm_num)
theorem B1696261 : Blo 443779 1696261 := bbase (se 4 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 1696261 = 318049) (by norm_num)
theorem B844357 : Blo 443779 844357 := bbase (se 4 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 844357 = 158317) (by norm_num)
theorem B844501 : Blo 443779 844501 := bbase (se 7 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 844501 = 19793) (by norm_num)
theorem B5726933 : Blo 443779 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B1499957 : Blo 443779 1499957 := bbase (se 5 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 1499957 = 140621) (by norm_num)
theorem B1696565 : Blo 443779 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B484181 : Blo 443779 484181 := bbase (se 9 (by rfl) ⟨1418, by rfl⟩ : syracuseStep 484181 = 2837) (by norm_num)
theorem B844661 : Blo 443779 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B2417525 : Blo 443779 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B1369045 : Blo 443779 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B844805 : Blo 443779 844805 := bbase (se 4 (by rfl) ⟨79200, by rfl⟩ : syracuseStep 844805 = 158401) (by norm_num)
theorem B1270853 : Blo 443779 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B1500389 : Blo 443779 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B484589 : Blo 443779 484589 := bbase (se 3 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 484589 = 181721) (by norm_num)
theorem B845093 : Blo 443779 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B2254229 : Blo 443779 2254229 := bbase (se 6 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 2254229 = 105667) (by norm_num)
theorem B845245 : Blo 443779 845245 := bbase (se 3 (by rfl) ⟨158483, by rfl⟩ : syracuseStep 845245 = 316967) (by norm_num)
theorem B1074637 : Blo 443779 1074637 := bbase (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) (by norm_num)
theorem B1271285 : Blo 443779 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B2942453 : Blo 443779 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B714253 : Blo 443779 714253 := bbase (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) (by norm_num)
theorem B4285973 : Blo 443779 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B1500821 : Blo 443779 1500821 := bbase (se 6 (by rfl) ⟨35175, by rfl⟩ : syracuseStep 1500821 = 70351) (by norm_num)
theorem B845549 : Blo 443779 845549 := bbase (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) (by norm_num)
theorem B714509 : Blo 443779 714509 := bbase (se 3 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 714509 = 267941) (by norm_num)
theorem B714701 : Blo 443779 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B1140709 : Blo 443779 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B1468469 : Blo 443779 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1501253 : Blo 443779 1501253 := bbase (se 4 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 1501253 = 281485) (by norm_num)
theorem B1075301 : Blo 443779 1075301 := bbase (se 4 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 1075301 = 201619) (by norm_num)
theorem B1272037 : Blo 443779 1272037 := bbase (se 4 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 1272037 = 238507) (by norm_num)
theorem B1075589 : Blo 443779 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B846301 : Blo 443779 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B1501685 : Blo 443779 1501685 := bbase (se 5 (by rfl) ⟨70391, by rfl⟩ : syracuseStep 1501685 = 140783) (by norm_num)
theorem B846445 : Blo 443779 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B2255525 : Blo 443779 2255525 := bbase (se 4 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 2255525 = 422911) (by norm_num)
theorem B846605 : Blo 443779 846605 := bbase (se 3 (by rfl) ⟨158738, by rfl⟩ : syracuseStep 846605 = 317477) (by norm_num)
theorem B715637 : Blo 443779 715637 := bbase (se 5 (by rfl) ⟨33545, by rfl⟩ : syracuseStep 715637 = 67091) (by norm_num)
theorem B1698677 : Blo 443779 1698677 := bbase (se 5 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 1698677 = 159251) (by norm_num)
theorem B846749 : Blo 443779 846749 := bbase (se 3 (by rfl) ⟨158765, by rfl⟩ : syracuseStep 846749 = 317531) (by norm_num)
theorem B1502117 : Blo 443779 1502117 := bbase (se 4 (by rfl) ⟨140823, by rfl⟩ : syracuseStep 1502117 = 281647) (by norm_num)
theorem B3796085 : Blo 443779 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B1698965 : Blo 443779 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B847037 : Blo 443779 847037 := bbase (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) (by norm_num)
theorem B2616533 : Blo 443779 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B453853 : Blo 443779 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B716021 : Blo 443779 716021 := bbase (se 5 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 716021 = 67127) (by norm_num)
theorem B748885 : Blo 443779 748885 := bbase (se 11 (by rfl) ⟨548, by rfl⟩ : syracuseStep 748885 = 1097) (by norm_num)
theorem B1502549 : Blo 443779 1502549 := bbase (se 11 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 1502549 = 2201) (by norm_num)
theorem B847189 : Blo 443779 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B716149 : Blo 443779 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B748973 : Blo 443779 748973 := bbase (se 3 (by rfl) ⟨140432, by rfl⟩ : syracuseStep 748973 = 280865) (by norm_num)
theorem B1601045 : Blo 443779 1601045 := bbase (se 6 (by rfl) ⟨37524, by rfl⟩ : syracuseStep 1601045 = 75049) (by norm_num)
theorem B749101 : Blo 443779 749101 := bbase (se 3 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 749101 = 280913) (by norm_num)
theorem B1142333 : Blo 443779 1142333 := bbase (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) (by norm_num)
theorem B749189 : Blo 443779 749189 := bbase (se 4 (by rfl) ⟨70236, by rfl⟩ : syracuseStep 749189 = 140473) (by norm_num)
theorem B847493 : Blo 443779 847493 := bbase (se 4 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 847493 = 158905) (by norm_num)
theorem B749317 : Blo 443779 749317 := bbase (se 4 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 749317 = 140497) (by norm_num)
theorem B1502981 : Blo 443779 1502981 := bbase (se 4 (by rfl) ⟨140904, by rfl⟩ : syracuseStep 1502981 = 281809) (by norm_num)
theorem B749405 : Blo 443779 749405 := bbase (se 3 (by rfl) ⟨140513, by rfl⟩ : syracuseStep 749405 = 281027) (by norm_num)
theorem B2256821 : Blo 443779 2256821 := bbase (se 5 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 2256821 = 211577) (by norm_num)
theorem B1142741 : Blo 443779 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B749533 : Blo 443779 749533 := bbase (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) (by norm_num)
theorem B1929205 : Blo 443779 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B749621 : Blo 443779 749621 := bbase (se 5 (by rfl) ⟨35138, by rfl⟩ : syracuseStep 749621 = 70277) (by norm_num)
theorem B749749 : Blo 443779 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B1503413 : Blo 443779 1503413 := bbase (se 5 (by rfl) ⟨70472, by rfl⟩ : syracuseStep 1503413 = 140945) (by norm_num)
theorem B749837 : Blo 443779 749837 := bbase (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) (by norm_num)
theorem B1700149 : Blo 443779 1700149 := bbase (se 5 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 1700149 = 159389) (by norm_num)
theorem B717149 : Blo 443779 717149 := bbase (se 3 (by rfl) ⟨134465, by rfl⟩ : syracuseStep 717149 = 268931) (by norm_num)
theorem B3371381 : Blo 443779 3371381 := bbase (se 5 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 3371381 = 316067) (by norm_num)
theorem B848245 : Blo 443779 848245 := bbase (se 5 (by rfl) ⟨39761, by rfl⟩ : syracuseStep 848245 = 79523) (by norm_num)
theorem B749965 : Blo 443779 749965 := bbase (se 3 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 749965 = 281237) (by norm_num)
theorem B750053 : Blo 443779 750053 := bbase (se 4 (by rfl) ⟨70317, by rfl⟩ : syracuseStep 750053 = 140635) (by norm_num)
theorem B1896949 : Blo 443779 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B848389 : Blo 443779 848389 := bbase (se 4 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 848389 = 159073) (by norm_num)
theorem B750181 : Blo 443779 750181 := bbase (se 4 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 750181 = 140659) (by norm_num)
theorem B1503845 : Blo 443779 1503845 := bbase (se 4 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 1503845 = 281971) (by norm_num)
theorem B848549 : Blo 443779 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B750269 : Blo 443779 750269 := bbase (se 3 (by rfl) ⟨140675, by rfl⟩ : syracuseStep 750269 = 281351) (by norm_num)
theorem B848693 : Blo 443779 848693 := bbase (se 5 (by rfl) ⟨39782, by rfl⟩ : syracuseStep 848693 = 79565) (by norm_num)
theorem B750397 : Blo 443779 750397 := bbase (se 3 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 750397 = 281399) (by norm_num)
theorem B750485 : Blo 443779 750485 := bbase (se 6 (by rfl) ⟨17589, by rfl⟩ : syracuseStep 750485 = 35179) (by norm_num)
theorem B1274885 : Blo 443779 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B750613 : Blo 443779 750613 := bbase (se 6 (by rfl) ⟨17592, by rfl⟩ : syracuseStep 750613 = 35185) (by norm_num)
theorem B1504277 : Blo 443779 1504277 := bbase (se 6 (by rfl) ⟨35256, by rfl⟩ : syracuseStep 1504277 = 70513) (by norm_num)
theorem B848981 : Blo 443779 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B750701 : Blo 443779 750701 := bbase (se 3 (by rfl) ⟨140756, by rfl⟩ : syracuseStep 750701 = 281513) (by norm_num)
theorem B2258117 : Blo 443779 2258117 := bbase (se 4 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 2258117 = 423397) (by norm_num)
theorem B750829 : Blo 443779 750829 := bbase (se 3 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 750829 = 281561) (by norm_num)
theorem B849133 : Blo 443779 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B750917 : Blo 443779 750917 := bbase (se 4 (by rfl) ⟨70398, by rfl⟩ : syracuseStep 750917 = 140797) (by norm_num)
theorem B816509 : Blo 443779 816509 := bbase (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) (by norm_num)
theorem B751045 : Blo 443779 751045 := bbase (se 4 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 751045 = 140821) (by norm_num)
theorem B1504709 : Blo 443779 1504709 := bbase (se 4 (by rfl) ⟨141066, by rfl⟩ : syracuseStep 1504709 = 282133) (by norm_num)
theorem B751133 : Blo 443779 751133 := bbase (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) (by norm_num)
theorem B849437 : Blo 443779 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B1013381 : Blo 443779 1013381 := bbase (se 4 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 1013381 = 190009) (by norm_num)
theorem B1603205 : Blo 443779 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B2717333 : Blo 443779 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B751261 : Blo 443779 751261 := bbase (se 3 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 751261 = 281723) (by norm_num)
theorem B751349 : Blo 443779 751349 := bbase (se 5 (by rfl) ⟨35219, by rfl⟩ : syracuseStep 751349 = 70439) (by norm_num)
theorem B2029349 : Blo 443779 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B751477 : Blo 443779 751477 := bbase (se 5 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 751477 = 70451) (by norm_num)
theorem B1505141 : Blo 443779 1505141 := bbase (se 5 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 1505141 = 141107) (by norm_num)
theorem B948125 : Blo 443779 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B948133 : Blo 443779 948133 := bbase (se 4 (by rfl) ⟨88887, by rfl⟩ : syracuseStep 948133 = 177775) (by norm_num)
theorem B1603493 : Blo 443779 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B1898437 : Blo 443779 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B751565 : Blo 443779 751565 := bbase (se 3 (by rfl) ⟨140918, by rfl⟩ : syracuseStep 751565 = 281837) (by norm_num)
theorem B1898453 : Blo 443779 1898453 := bbase (se 7 (by rfl) ⟨22247, by rfl⟩ : syracuseStep 1898453 = 44495) (by norm_num)
theorem B3799061 : Blo 443779 3799061 := bbase (se 6 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 3799061 = 178081) (by norm_num)
theorem B3045397 : Blo 443779 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B751693 : Blo 443779 751693 := bbase (se 3 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 751693 = 281885) (by norm_num)
theorem B751781 : Blo 443779 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B751909 : Blo 443779 751909 := bbase (se 4 (by rfl) ⟨70491, by rfl⟩ : syracuseStep 751909 = 140983) (by norm_num)
theorem B1505573 : Blo 443779 1505573 := bbase (se 4 (by rfl) ⟨141147, by rfl⟩ : syracuseStep 1505573 = 282295) (by norm_num)
theorem B751997 : Blo 443779 751997 := bbase (se 3 (by rfl) ⟨140999, by rfl⟩ : syracuseStep 751997 = 281999) (by norm_num)
theorem B817597 : Blo 443779 817597 := bbase (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) (by norm_num)
theorem B2259413 : Blo 443779 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B752125 : Blo 443779 752125 := bbase (se 3 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 752125 = 282047) (by norm_num)
theorem B752213 : Blo 443779 752213 := bbase (se 8 (by rfl) ⟨4407, by rfl⟩ : syracuseStep 752213 = 8815) (by norm_num)
theorem B555709 : Blo 443779 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B752341 : Blo 443779 752341 := bbase (se 7 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 752341 = 17633) (by norm_num)
theorem B1506005 : Blo 443779 1506005 := bbase (se 7 (by rfl) ⟨17648, by rfl⟩ : syracuseStep 1506005 = 35297) (by norm_num)
theorem B457445 : Blo 443779 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B2849525 : Blo 443779 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B752429 : Blo 443779 752429 := bbase (se 3 (by rfl) ⟨141080, by rfl⟩ : syracuseStep 752429 = 282161) (by norm_num)
theorem B752557 : Blo 443779 752557 := bbase (se 3 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 752557 = 282209) (by norm_num)
theorem B1145821 : Blo 443779 1145821 := bbase (se 3 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 1145821 = 429683) (by norm_num)
theorem B752645 : Blo 443779 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B949261 : Blo 443779 949261 := bbase (se 3 (by rfl) ⟨177986, by rfl⟩ : syracuseStep 949261 = 355973) (by norm_num)
theorem B5405717 : Blo 443779 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B752773 : Blo 443779 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B1506437 : Blo 443779 1506437 := bbase (se 4 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 1506437 = 282457) (by norm_num)
theorem B752861 : Blo 443779 752861 := bbase (se 3 (by rfl) ⟨141161, by rfl⟩ : syracuseStep 752861 = 282323) (by norm_num)
theorem B752989 : Blo 443779 752989 := bbase (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) (by norm_num)
theorem B949637 : Blo 443779 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B3210677 : Blo 443779 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B753077 : Blo 443779 753077 := bbase (se 5 (by rfl) ⟨35300, by rfl⟩ : syracuseStep 753077 = 70601) (by norm_num)
theorem B1015325 : Blo 443779 1015325 := bbase (se 3 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 1015325 = 380747) (by norm_num)
theorem B753205 : Blo 443779 753205 := bbase (se 5 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 753205 = 70613) (by norm_num)
theorem B1506869 : Blo 443779 1506869 := bbase (se 5 (by rfl) ⟨70634, by rfl⟩ : syracuseStep 1506869 = 141269) (by norm_num)
theorem B753293 : Blo 443779 753293 := bbase (se 3 (by rfl) ⟨141242, by rfl⟩ : syracuseStep 753293 = 282485) (by norm_num)
theorem B917149 : Blo 443779 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B2260709 : Blo 443779 2260709 := bbase (se 4 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 2260709 = 423883) (by norm_num)
theorem B753421 : Blo 443779 753421 := bbase (se 3 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 753421 = 282533) (by norm_num)
theorem B753509 : Blo 443779 753509 := bbase (se 4 (by rfl) ⟨70641, by rfl⟩ : syracuseStep 753509 = 141283) (by norm_num)
theorem B753637 : Blo 443779 753637 := bbase (se 4 (by rfl) ⟨70653, by rfl⟩ : syracuseStep 753637 = 141307) (by norm_num)
theorem B1507301 : Blo 443779 1507301 := bbase (se 4 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 1507301 = 282619) (by norm_num)
theorem B1507409 : Blo 443779 1507409 := bstep (se 2 (by rfl) ⟨565278, by rfl⟩ : syracuseStep 1507409 = 1130557) B1130557
theorem B753745 : Blo 443779 753745 := bstep (se 2 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 753745 = 565309) B565309
theorem B753779 : Blo 443779 753779 := bstep (se 1 (by rfl) ⟨565334, by rfl⟩ : syracuseStep 753779 = 1130669) B1130669
theorem B2719907 : Blo 443779 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B950449 : Blo 443779 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B458995 : Blo 443779 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B753907 : Blo 443779 753907 := bstep (se 1 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 753907 = 1130861) B1130861
theorem B459059 : Blo 443779 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B754049 : Blo 443779 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B754177 : Blo 443779 754177 := bstep (se 2 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 754177 = 565633) B565633
theorem B754211 : Blo 443779 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B1507949 : Blo 443779 1507949 := bstep (se 3 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 1507949 = 565481) B565481
theorem B1508003 : Blo 443779 1508003 := bstep (se 1 (by rfl) ⟨1131002, by rfl⟩ : syracuseStep 1508003 = 2262005) B2262005
theorem B754339 : Blo 443779 754339 := bstep (se 1 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 754339 = 1131509) B1131509
theorem B2261681 : Blo 443779 2261681 := bstep (se 2 (by rfl) ⟨848130, by rfl⟩ : syracuseStep 2261681 = 1696261) B1696261
theorem B754481 : Blo 443779 754481 := bstep (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) B565861
theorem B721841 : Blo 443779 721841 := bstep (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) B541381
theorem B1508273 : Blo 443779 1508273 := bstep (se 2 (by rfl) ⟨565602, by rfl⟩ : syracuseStep 1508273 = 1131205) B1131205
theorem B754609 : Blo 443779 754609 := bstep (se 2 (by rfl) ⟨282978, by rfl⟩ : syracuseStep 754609 = 565957) B565957
theorem B754643 : Blo 443779 754643 := bstep (se 1 (by rfl) ⟨565982, by rfl⟩ : syracuseStep 754643 = 1131965) B1131965
theorem B754771 : Blo 443779 754771 := bstep (se 1 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 754771 = 1132157) B1132157
theorem B3376241 : Blo 443779 3376241 := bstep (se 2 (by rfl) ⟨1266090, by rfl⟩ : syracuseStep 3376241 = 2532181) B2532181
theorem B1082531 : Blo 443779 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B754913 : Blo 443779 754913 := bstep (se 2 (by rfl) ⟨283092, by rfl⟩ : syracuseStep 754913 = 566185) B566185
theorem B755041 : Blo 443779 755041 := bstep (se 2 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 755041 = 566281) B566281
theorem B755075 : Blo 443779 755075 := bstep (se 1 (by rfl) ⟨566306, by rfl⟩ : syracuseStep 755075 = 1132613) B1132613
theorem B16647565 : Blo 443779 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B558499 : Blo 443779 558499 := bstep (se 1 (by rfl) ⟨418874, by rfl⟩ : syracuseStep 558499 = 837749) B837749
theorem B2852293 : Blo 443779 2852293 := bstep (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) B534805
theorem B1508813 : Blo 443779 1508813 := bstep (se 3 (by rfl) ⟨282902, by rfl⟩ : syracuseStep 1508813 = 565805) B565805
theorem B1508867 : Blo 443779 1508867 := bstep (se 1 (by rfl) ⟨1131650, by rfl⟩ : syracuseStep 1508867 = 2263301) B2263301
theorem B755203 : Blo 443779 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B755345 : Blo 443779 755345 := bstep (se 2 (by rfl) ⟨283254, by rfl⟩ : syracuseStep 755345 = 566509) B566509
theorem B1509137 : Blo 443779 1509137 := bstep (se 2 (by rfl) ⟨565926, by rfl⟩ : syracuseStep 1509137 = 1131853) B1131853
theorem B755473 : Blo 443779 755473 := bstep (se 2 (by rfl) ⟨283302, by rfl⟩ : syracuseStep 755473 = 566605) B566605
theorem B755507 : Blo 443779 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B1017731 : Blo 443779 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B952337 : Blo 443779 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B2263139 : Blo 443779 2263139 := bstep (se 1 (by rfl) ⟨1697354, by rfl⟩ : syracuseStep 2263139 = 3394709) B3394709
theorem B1083619 : Blo 443779 1083619 := bstep (se 1 (by rfl) ⟨812714, by rfl⟩ : syracuseStep 1083619 = 1625429) B1625429
theorem B1509677 : Blo 443779 1509677 := bstep (se 3 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 1509677 = 566129) B566129
theorem B4360517 : Blo 443779 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B1509731 : Blo 443779 1509731 := bstep (se 1 (by rfl) ⟨1132298, by rfl⟩ : syracuseStep 1509731 = 2264597) B2264597
theorem B2722339 : Blo 443779 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B1510001 : Blo 443779 1510001 := bstep (se 2 (by rfl) ⟨566250, by rfl⟩ : syracuseStep 1510001 = 1132501) B1132501
theorem B1903409 : Blo 443779 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B2263949 : Blo 443779 2263949 := bstep (se 3 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 2263949 = 848981) B848981
theorem B1281059 : Blo 443779 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B1510541 : Blo 443779 1510541 := bstep (se 3 (by rfl) ⟨283226, by rfl⟩ : syracuseStep 1510541 = 566453) B566453
theorem B1510595 : Blo 443779 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B953635 : Blo 443779 953635 := bstep (se 1 (by rfl) ⟨715226, by rfl⟩ : syracuseStep 953635 = 1430453) B1430453
theorem B2035043 : Blo 443779 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B1510865 : Blo 443779 1510865 := bstep (se 2 (by rfl) ⟨566574, by rfl⟩ : syracuseStep 1510865 = 1133149) B1133149
theorem B724675 : Blo 443779 724675 := bstep (se 1 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 724675 = 1087013) B1087013
theorem B7606385 : Blo 443779 7606385 := bstep (se 2 (by rfl) ⟨2852394, by rfl⟩ : syracuseStep 7606385 = 5704789) B5704789
theorem B12226787 : Blo 443779 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B5706125 : Blo 443779 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B954865 : Blo 443779 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B561811 : Blo 443779 561811 := bstep (se 1 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 561811 = 842717) B842717
theorem B463523 : Blo 443779 463523 := bstep (se 1 (by rfl) ⟨347642, by rfl⟩ : syracuseStep 463523 = 695285) B695285
theorem B561907 : Blo 443779 561907 := bstep (se 1 (by rfl) ⟨421430, by rfl⟩ : syracuseStep 561907 = 842861) B842861
theorem B5084045 : Blo 443779 5084045 := bstep (se 3 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 5084045 = 1906517) B1906517
theorem B2855857 : Blo 443779 2855857 := bstep (se 2 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 2855857 = 2141893) B2141893
theorem B2528333 : Blo 443779 2528333 := bstep (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) B948125
theorem B857233 : Blo 443779 857233 := bstep (se 2 (by rfl) ⟨321462, by rfl⟩ : syracuseStep 857233 = 642925) B642925
theorem B1905869 : Blo 443779 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B562403 : Blo 443779 562403 := bstep (se 1 (by rfl) ⟨421802, by rfl⟩ : syracuseStep 562403 = 843605) B843605
theorem B955651 : Blo 443779 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B3872069 : Blo 443779 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B3216995 : Blo 443779 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B2266865 : Blo 443779 2266865 := bstep (se 2 (by rfl) ⟨850074, by rfl⟩ : syracuseStep 2266865 = 1700149) B1700149
theorem B1709923 : Blo 443779 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B563107 : Blo 443779 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B1611683 : Blo 443779 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B2529265 : Blo 443779 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B563203 : Blo 443779 563203 := bstep (se 1 (by rfl) ⟨422402, by rfl⟩ : syracuseStep 563203 = 844805) B844805
theorem B2758691 : Blo 443779 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B5150789 : Blo 443779 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B1448099 : Blo 443779 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B3610979 : Blo 443779 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B1350029 : Blo 443779 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B1907185 : Blo 443779 1907185 := bstep (se 2 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 1907185 = 1430389) B1430389
theorem B563699 : Blo 443779 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B4299277 : Blo 443779 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B596531 : Blo 443779 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B2038691 : Blo 443779 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B760801 : Blo 443779 760801 := bstep (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) B570601
theorem B564403 : Blo 443779 564403 := bstep (se 1 (by rfl) ⟨423302, by rfl⟩ : syracuseStep 564403 = 846605) B846605
theorem B1219853 : Blo 443779 1219853 := bstep (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) B457445
theorem B564499 : Blo 443779 564499 := bstep (se 1 (by rfl) ⟨423374, by rfl⟩ : syracuseStep 564499 = 846749) B846749
theorem B2530723 : Blo 443779 2530723 := bstep (se 1 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 2530723 = 3796085) B3796085
theorem B1744355 : Blo 443779 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B761329 : Blo 443779 761329 := bstep (se 2 (by rfl) ⟨285498, by rfl⟩ : syracuseStep 761329 = 570997) B570997
theorem B499315 : Blo 443779 499315 := bstep (se 1 (by rfl) ⟨374486, by rfl⟩ : syracuseStep 499315 = 748973) B748973
theorem B761555 : Blo 443779 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B3612401 : Blo 443779 3612401 := bstep (se 2 (by rfl) ⟨1354650, by rfl⟩ : syracuseStep 3612401 = 2709301) B2709301
theorem B5086961 : Blo 443779 5086961 := bstep (se 2 (by rfl) ⟨1907610, by rfl⟩ : syracuseStep 5086961 = 3815221) B3815221
theorem B499459 : Blo 443779 499459 := bstep (se 1 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 499459 = 749189) B749189
theorem B564995 : Blo 443779 564995 := bstep (se 1 (by rfl) ⟨423746, by rfl⟩ : syracuseStep 564995 = 847493) B847493
theorem B4595555 : Blo 443779 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B499603 : Blo 443779 499603 := bstep (se 1 (by rfl) ⟨374702, by rfl⟩ : syracuseStep 499603 = 749405) B749405
theorem B2531249 : Blo 443779 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B761827 : Blo 443779 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B1712141 : Blo 443779 1712141 := bstep (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) B642053
theorem B499747 : Blo 443779 499747 := bstep (se 1 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 499747 = 749621) B749621
theorem B499891 : Blo 443779 499891 := bstep (se 1 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 499891 = 749837) B749837
theorem B500035 : Blo 443779 500035 := bstep (se 1 (by rfl) ⟨375026, by rfl⟩ : syracuseStep 500035 = 750053) B750053
theorem B565699 : Blo 443779 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B500179 : Blo 443779 500179 := bstep (se 1 (by rfl) ⟨375134, by rfl⟩ : syracuseStep 500179 = 750269) B750269
theorem B565795 : Blo 443779 565795 := bstep (se 1 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 565795 = 848693) B848693
theorem B500323 : Blo 443779 500323 := bstep (se 1 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 500323 = 750485) B750485
theorem B4563569 : Blo 443779 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B1548941 : Blo 443779 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B500467 : Blo 443779 500467 := bstep (se 1 (by rfl) ⟨375350, by rfl⟩ : syracuseStep 500467 = 750701) B750701
theorem B500611 : Blo 443779 500611 := bstep (se 1 (by rfl) ⟨375458, by rfl⟩ : syracuseStep 500611 = 750917) B750917
theorem B500755 : Blo 443779 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B566291 : Blo 443779 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B1123409 : Blo 443779 1123409 := bstep (se 2 (by rfl) ⟨421278, by rfl⟩ : syracuseStep 1123409 = 842557) B842557
theorem B1811555 : Blo 443779 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B500899 : Blo 443779 500899 := bstep (se 1 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 500899 = 751349) B751349
theorem B1352899 : Blo 443779 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B501043 : Blo 443779 501043 := bstep (se 1 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 501043 = 751565) B751565
theorem B2532707 : Blo 443779 2532707 := bstep (se 1 (by rfl) ⟨1899530, by rfl⟩ : syracuseStep 2532707 = 3799061) B3799061
theorem B501187 : Blo 443779 501187 := bstep (se 1 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 501187 = 751781) B751781
theorem B1910243 : Blo 443779 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B501331 : Blo 443779 501331 := bstep (se 1 (by rfl) ⟨375998, by rfl⟩ : syracuseStep 501331 = 751997) B751997
theorem B501475 : Blo 443779 501475 := bstep (se 1 (by rfl) ⟨376106, by rfl⟩ : syracuseStep 501475 = 752213) B752213
theorem B1353581 : Blo 443779 1353581 := bstep (se 3 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 1353581 = 507593) B507593
theorem B501619 : Blo 443779 501619 := bstep (se 1 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 501619 = 752429) B752429
theorem B501763 : Blo 443779 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B1124401 : Blo 443779 1124401 := bstep (se 2 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 1124401 = 843301) B843301
theorem B665681 : Blo 443779 665681 := bstep (se 2 (by rfl) ⟨249630, by rfl⟩ : syracuseStep 665681 = 499261) B499261
theorem B665699 : Blo 443779 665699 := bstep (se 1 (by rfl) ⟨499274, by rfl⟩ : syracuseStep 665699 = 998549) B998549
theorem B665729 : Blo 443779 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B2861189 : Blo 443779 2861189 := bstep (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) B536473
theorem B665747 : Blo 443779 665747 := bstep (se 1 (by rfl) ⟨499310, by rfl⟩ : syracuseStep 665747 = 998621) B998621
theorem B501907 : Blo 443779 501907 := bstep (se 1 (by rfl) ⟨376430, by rfl⟩ : syracuseStep 501907 = 752861) B752861
theorem B665777 : Blo 443779 665777 := bstep (se 2 (by rfl) ⟨249666, by rfl⟩ : syracuseStep 665777 = 499333) B499333
theorem B665795 : Blo 443779 665795 := bstep (se 1 (by rfl) ⟨499346, by rfl⟩ : syracuseStep 665795 = 998693) B998693
theorem B1222865 : Blo 443779 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B665825 : Blo 443779 665825 := bstep (se 2 (by rfl) ⟨249684, by rfl⟩ : syracuseStep 665825 = 499369) B499369
theorem B665843 : Blo 443779 665843 := bstep (se 1 (by rfl) ⟨499382, by rfl⟩ : syracuseStep 665843 = 998765) B998765
theorem B633091 : Blo 443779 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B665873 : Blo 443779 665873 := bstep (se 2 (by rfl) ⟨249702, by rfl⟩ : syracuseStep 665873 = 499405) B499405
theorem B665891 : Blo 443779 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B2140451 : Blo 443779 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B502051 : Blo 443779 502051 := bstep (se 1 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 502051 = 753077) B753077
theorem B665921 : Blo 443779 665921 := bstep (se 2 (by rfl) ⟨249720, by rfl⟩ : syracuseStep 665921 = 499441) B499441
theorem B1124675 : Blo 443779 1124675 := bstep (se 1 (by rfl) ⟨843506, by rfl⟩ : syracuseStep 1124675 = 1687013) B1687013
theorem B665939 : Blo 443779 665939 := bstep (se 1 (by rfl) ⟨499454, by rfl⟩ : syracuseStep 665939 = 998909) B998909
theorem B600419 : Blo 443779 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B665969 : Blo 443779 665969 := bstep (se 2 (by rfl) ⟨249738, by rfl⟩ : syracuseStep 665969 = 499477) B499477
theorem B665987 : Blo 443779 665987 := bstep (se 1 (by rfl) ⟨499490, by rfl⟩ : syracuseStep 665987 = 998981) B998981
theorem B666017 : Blo 443779 666017 := bstep (se 2 (by rfl) ⟨249756, by rfl⟩ : syracuseStep 666017 = 499513) B499513
theorem B666035 : Blo 443779 666035 := bstep (se 1 (by rfl) ⟨499526, by rfl⟩ : syracuseStep 666035 = 999053) B999053
theorem B502195 : Blo 443779 502195 := bstep (se 1 (by rfl) ⟨376646, by rfl⟩ : syracuseStep 502195 = 753293) B753293
theorem B666065 : Blo 443779 666065 := bstep (se 2 (by rfl) ⟨249774, by rfl⟩ : syracuseStep 666065 = 499549) B499549
theorem B666083 : Blo 443779 666083 := bstep (se 1 (by rfl) ⟨499562, by rfl⟩ : syracuseStep 666083 = 999125) B999125
theorem B535027 : Blo 443779 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B666113 : Blo 443779 666113 := bstep (se 2 (by rfl) ⟨249792, by rfl⟩ : syracuseStep 666113 = 499585) B499585
theorem B1124867 : Blo 443779 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B666131 : Blo 443779 666131 := bstep (se 1 (by rfl) ⟨499598, by rfl⟩ : syracuseStep 666131 = 999197) B999197
theorem B666161 : Blo 443779 666161 := bstep (se 2 (by rfl) ⟨249810, by rfl⟩ : syracuseStep 666161 = 499621) B499621
theorem B666179 : Blo 443779 666179 := bstep (se 1 (by rfl) ⟨499634, by rfl⟩ : syracuseStep 666179 = 999269) B999269
theorem B502339 : Blo 443779 502339 := bstep (se 1 (by rfl) ⟨376754, by rfl⟩ : syracuseStep 502339 = 753509) B753509
theorem B666209 : Blo 443779 666209 := bstep (se 2 (by rfl) ⟨249828, by rfl⟩ : syracuseStep 666209 = 499657) B499657
theorem B666227 : Blo 443779 666227 := bstep (se 1 (by rfl) ⟨499670, by rfl⟩ : syracuseStep 666227 = 999341) B999341
theorem B666257 : Blo 443779 666257 := bstep (se 2 (by rfl) ⟨249846, by rfl⟩ : syracuseStep 666257 = 499693) B499693
theorem B666275 : Blo 443779 666275 := bstep (se 1 (by rfl) ⟨499706, by rfl⟩ : syracuseStep 666275 = 999413) B999413
theorem B666305 : Blo 443779 666305 := bstep (se 2 (by rfl) ⟨249864, by rfl⟩ : syracuseStep 666305 = 499729) B499729
theorem B666323 : Blo 443779 666323 := bstep (se 1 (by rfl) ⟨499742, by rfl⟩ : syracuseStep 666323 = 999485) B999485
theorem B502483 : Blo 443779 502483 := bstep (se 1 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 502483 = 753725) B753725
theorem B666353 : Blo 443779 666353 := bstep (se 2 (by rfl) ⟨249882, by rfl⟩ : syracuseStep 666353 = 499765) B499765
theorem B666371 : Blo 443779 666371 := bstep (se 1 (by rfl) ⟨499778, by rfl⟩ : syracuseStep 666371 = 999557) B999557
theorem B666401 : Blo 443779 666401 := bstep (se 2 (by rfl) ⟨249900, by rfl⟩ : syracuseStep 666401 = 499801) B499801
theorem B2403121 : Blo 443779 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B666419 : Blo 443779 666419 := bstep (se 1 (by rfl) ⟨499814, by rfl⟩ : syracuseStep 666419 = 999629) B999629
theorem B764723 : Blo 443779 764723 := bstep (se 1 (by rfl) ⟨573542, by rfl⟩ : syracuseStep 764723 = 1147085) B1147085
theorem B666449 : Blo 443779 666449 := bstep (se 2 (by rfl) ⟨249918, by rfl⟩ : syracuseStep 666449 = 499837) B499837
theorem B666467 : Blo 443779 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B502627 : Blo 443779 502627 := bstep (se 1 (by rfl) ⟨376970, by rfl⟩ : syracuseStep 502627 = 753941) B753941
theorem B535411 : Blo 443779 535411 := bstep (se 1 (by rfl) ⟨401558, by rfl⟩ : syracuseStep 535411 = 803117) B803117
theorem B666497 : Blo 443779 666497 := bstep (se 2 (by rfl) ⟨249936, by rfl⟩ : syracuseStep 666497 = 499873) B499873
theorem B666515 : Blo 443779 666515 := bstep (se 1 (by rfl) ⟨499886, by rfl⟩ : syracuseStep 666515 = 999773) B999773
theorem B666545 : Blo 443779 666545 := bstep (se 2 (by rfl) ⟨249954, by rfl⟩ : syracuseStep 666545 = 499909) B499909
theorem B666563 : Blo 443779 666563 := bstep (se 1 (by rfl) ⟨499922, by rfl⟩ : syracuseStep 666563 = 999845) B999845
theorem B666593 : Blo 443779 666593 := bstep (se 2 (by rfl) ⟨249972, by rfl⟩ : syracuseStep 666593 = 499945) B499945
theorem B666611 : Blo 443779 666611 := bstep (se 1 (by rfl) ⟨499958, by rfl⟩ : syracuseStep 666611 = 999917) B999917
theorem B502771 : Blo 443779 502771 := bstep (se 1 (by rfl) ⟨377078, by rfl⟩ : syracuseStep 502771 = 754157) B754157
theorem B666641 : Blo 443779 666641 := bstep (se 2 (by rfl) ⟨249990, by rfl⟩ : syracuseStep 666641 = 499981) B499981
theorem B666659 : Blo 443779 666659 := bstep (se 1 (by rfl) ⟨499994, by rfl⟩ : syracuseStep 666659 = 999989) B999989
theorem B666689 : Blo 443779 666689 := bstep (se 2 (by rfl) ⟨250008, by rfl⟩ : syracuseStep 666689 = 500017) B500017
theorem B666707 : Blo 443779 666707 := bstep (se 1 (by rfl) ⟨500030, by rfl⟩ : syracuseStep 666707 = 1000061) B1000061
theorem B666737 : Blo 443779 666737 := bstep (se 2 (by rfl) ⟨250026, by rfl⟩ : syracuseStep 666737 = 500053) B500053
theorem B666755 : Blo 443779 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B502915 : Blo 443779 502915 := bstep (se 1 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 502915 = 754373) B754373
theorem B1715341 : Blo 443779 1715341 := bstep (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) B643253
theorem B666785 : Blo 443779 666785 := bstep (se 2 (by rfl) ⟨250044, by rfl⟩ : syracuseStep 666785 = 500089) B500089
theorem B666803 : Blo 443779 666803 := bstep (se 1 (by rfl) ⟨500102, by rfl⟩ : syracuseStep 666803 = 1000205) B1000205
theorem B2534597 : Blo 443779 2534597 := bstep (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) B475237
theorem B666833 : Blo 443779 666833 := bstep (se 2 (by rfl) ⟨250062, by rfl⟩ : syracuseStep 666833 = 500125) B500125
theorem B666851 : Blo 443779 666851 := bstep (se 1 (by rfl) ⟨500138, by rfl⟩ : syracuseStep 666851 = 1000277) B1000277
theorem B666881 : Blo 443779 666881 := bstep (se 2 (by rfl) ⟨250080, by rfl⟩ : syracuseStep 666881 = 500161) B500161
theorem B1223939 : Blo 443779 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B666899 : Blo 443779 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B503059 : Blo 443779 503059 := bstep (se 1 (by rfl) ⟨377294, by rfl⟩ : syracuseStep 503059 = 754589) B754589
theorem B666929 : Blo 443779 666929 := bstep (se 2 (by rfl) ⟨250098, by rfl⟩ : syracuseStep 666929 = 500197) B500197
theorem B666947 : Blo 443779 666947 := bstep (se 1 (by rfl) ⟨500210, by rfl⟩ : syracuseStep 666947 = 1000421) B1000421
theorem B666977 : Blo 443779 666977 := bstep (se 2 (by rfl) ⟨250116, by rfl⟩ : syracuseStep 666977 = 500233) B500233
theorem B634225 : Blo 443779 634225 := bstep (se 2 (by rfl) ⟨237834, by rfl⟩ : syracuseStep 634225 = 475669) B475669
theorem B666995 : Blo 443779 666995 := bstep (se 1 (by rfl) ⟨500246, by rfl⟩ : syracuseStep 666995 = 1000493) B1000493
theorem B535939 : Blo 443779 535939 := bstep (se 1 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 535939 = 803909) B803909
theorem B667025 : Blo 443779 667025 := bstep (se 2 (by rfl) ⟨250134, by rfl⟩ : syracuseStep 667025 = 500269) B500269
theorem B667043 : Blo 443779 667043 := bstep (se 1 (by rfl) ⟨500282, by rfl⟩ : syracuseStep 667043 = 1000565) B1000565
theorem B503203 : Blo 443779 503203 := bstep (se 1 (by rfl) ⟨377402, by rfl⟩ : syracuseStep 503203 = 754805) B754805
theorem B1125809 : Blo 443779 1125809 := bstep (se 2 (by rfl) ⟨422178, by rfl⟩ : syracuseStep 1125809 = 844357) B844357
theorem B667073 : Blo 443779 667073 := bstep (se 2 (by rfl) ⟨250152, by rfl⟩ : syracuseStep 667073 = 500305) B500305
theorem B634321 : Blo 443779 634321 := bstep (se 2 (by rfl) ⟨237870, by rfl⟩ : syracuseStep 634321 = 475741) B475741
theorem B667091 : Blo 443779 667091 := bstep (se 1 (by rfl) ⟨500318, by rfl⟩ : syracuseStep 667091 = 1000637) B1000637
theorem B1125859 : Blo 443779 1125859 := bstep (se 1 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 1125859 = 1688789) B1688789
theorem B667121 : Blo 443779 667121 := bstep (se 2 (by rfl) ⟨250170, by rfl⟩ : syracuseStep 667121 = 500341) B500341
theorem B667139 : Blo 443779 667139 := bstep (se 1 (by rfl) ⟨500354, by rfl⟩ : syracuseStep 667139 = 1000709) B1000709
theorem B667169 : Blo 443779 667169 := bstep (se 2 (by rfl) ⟨250188, by rfl⟩ : syracuseStep 667169 = 500377) B500377
theorem B667187 : Blo 443779 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B503347 : Blo 443779 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B667217 : Blo 443779 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B667235 : Blo 443779 667235 := bstep (se 1 (by rfl) ⟨500426, by rfl⟩ : syracuseStep 667235 = 1000853) B1000853
theorem B1126001 : Blo 443779 1126001 := bstep (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) B844501
theorem B667265 : Blo 443779 667265 := bstep (se 2 (by rfl) ⟨250224, by rfl⟩ : syracuseStep 667265 = 500449) B500449
theorem B667283 : Blo 443779 667283 := bstep (se 1 (by rfl) ⟨500462, by rfl⟩ : syracuseStep 667283 = 1000925) B1000925
theorem B667313 : Blo 443779 667313 := bstep (se 2 (by rfl) ⟨250242, by rfl⟩ : syracuseStep 667313 = 500485) B500485
theorem B667331 : Blo 443779 667331 := bstep (se 1 (by rfl) ⟨500498, by rfl⟩ : syracuseStep 667331 = 1000997) B1000997
theorem B503491 : Blo 443779 503491 := bstep (se 1 (by rfl) ⟨377618, by rfl⟩ : syracuseStep 503491 = 755237) B755237
theorem B667361 : Blo 443779 667361 := bstep (se 2 (by rfl) ⟨250260, by rfl⟩ : syracuseStep 667361 = 500521) B500521
theorem B667379 : Blo 443779 667379 := bstep (se 1 (by rfl) ⟨500534, by rfl⟩ : syracuseStep 667379 = 1001069) B1001069
theorem B667409 : Blo 443779 667409 := bstep (se 2 (by rfl) ⟨250278, by rfl⟩ : syracuseStep 667409 = 500557) B500557
theorem B667427 : Blo 443779 667427 := bstep (se 1 (by rfl) ⟨500570, by rfl⟩ : syracuseStep 667427 = 1001141) B1001141
theorem B667457 : Blo 443779 667457 := bstep (se 2 (by rfl) ⟨250296, by rfl⟩ : syracuseStep 667457 = 500593) B500593
theorem B667475 : Blo 443779 667475 := bstep (se 1 (by rfl) ⟨500606, by rfl⟩ : syracuseStep 667475 = 1001213) B1001213
theorem B503635 : Blo 443779 503635 := bstep (se 1 (by rfl) ⟨377726, by rfl⟩ : syracuseStep 503635 = 755453) B755453
theorem B667505 : Blo 443779 667505 := bstep (se 2 (by rfl) ⟨250314, by rfl⟩ : syracuseStep 667505 = 500629) B500629
theorem B2142065 : Blo 443779 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B667523 : Blo 443779 667523 := bstep (se 1 (by rfl) ⟨500642, by rfl⟩ : syracuseStep 667523 = 1001285) B1001285
theorem B667553 : Blo 443779 667553 := bstep (se 2 (by rfl) ⟨250332, by rfl⟩ : syracuseStep 667553 = 500665) B500665
theorem B667571 : Blo 443779 667571 := bstep (se 1 (by rfl) ⟨500678, by rfl⟩ : syracuseStep 667571 = 1001357) B1001357
theorem B634817 : Blo 443779 634817 := bstep (se 2 (by rfl) ⟨238056, by rfl⟩ : syracuseStep 634817 = 476113) B476113
theorem B667601 : Blo 443779 667601 := bstep (se 2 (by rfl) ⟨250350, by rfl⟩ : syracuseStep 667601 = 500701) B500701
theorem B667619 : Blo 443779 667619 := bstep (se 1 (by rfl) ⟨500714, by rfl⟩ : syracuseStep 667619 = 1001429) B1001429
theorem B667649 : Blo 443779 667649 := bstep (se 2 (by rfl) ⟨250368, by rfl⟩ : syracuseStep 667649 = 500737) B500737
theorem B667667 : Blo 443779 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B667697 : Blo 443779 667697 := bstep (se 2 (by rfl) ⟨250386, by rfl⟩ : syracuseStep 667697 = 500773) B500773
theorem B667715 : Blo 443779 667715 := bstep (se 1 (by rfl) ⟨500786, by rfl⟩ : syracuseStep 667715 = 1001573) B1001573
theorem B667745 : Blo 443779 667745 := bstep (se 2 (by rfl) ⟨250404, by rfl⟩ : syracuseStep 667745 = 500809) B500809
theorem B667763 : Blo 443779 667763 := bstep (se 1 (by rfl) ⟨500822, by rfl⟩ : syracuseStep 667763 = 1001645) B1001645
theorem B667793 : Blo 443779 667793 := bstep (se 2 (by rfl) ⟨250422, by rfl⟩ : syracuseStep 667793 = 500845) B500845
theorem B667811 : Blo 443779 667811 := bstep (se 1 (by rfl) ⟨500858, by rfl⟩ : syracuseStep 667811 = 1001717) B1001717
theorem B667841 : Blo 443779 667841 := bstep (se 2 (by rfl) ⟨250440, by rfl⟩ : syracuseStep 667841 = 500881) B500881
theorem B667859 : Blo 443779 667859 := bstep (se 1 (by rfl) ⟨500894, by rfl⟩ : syracuseStep 667859 = 1001789) B1001789
theorem B667889 : Blo 443779 667889 := bstep (se 2 (by rfl) ⟨250458, by rfl⟩ : syracuseStep 667889 = 500917) B500917
theorem B667907 : Blo 443779 667907 := bstep (se 1 (by rfl) ⟨500930, by rfl⟩ : syracuseStep 667907 = 1001861) B1001861
theorem B667937 : Blo 443779 667937 := bstep (se 2 (by rfl) ⟨250476, by rfl⟩ : syracuseStep 667937 = 500953) B500953
theorem B1716515 : Blo 443779 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B667955 : Blo 443779 667955 := bstep (se 1 (by rfl) ⟨500966, by rfl⟩ : syracuseStep 667955 = 1001933) B1001933
theorem B602435 : Blo 443779 602435 := bstep (se 1 (by rfl) ⟨451826, by rfl⟩ : syracuseStep 602435 = 903653) B903653
theorem B667985 : Blo 443779 667985 := bstep (se 2 (by rfl) ⟨250494, by rfl⟩ : syracuseStep 667985 = 500989) B500989
theorem B668003 : Blo 443779 668003 := bstep (se 1 (by rfl) ⟨501002, by rfl⟩ : syracuseStep 668003 = 1002005) B1002005
theorem B668033 : Blo 443779 668033 := bstep (se 2 (by rfl) ⟨250512, by rfl⟩ : syracuseStep 668033 = 501025) B501025
theorem B668051 : Blo 443779 668051 := bstep (se 1 (by rfl) ⟨501038, by rfl⟩ : syracuseStep 668051 = 1002077) B1002077
theorem B668081 : Blo 443779 668081 := bstep (se 2 (by rfl) ⟨250530, by rfl⟩ : syracuseStep 668081 = 501061) B501061
theorem B1356209 : Blo 443779 1356209 := bstep (se 2 (by rfl) ⟨508578, by rfl⟩ : syracuseStep 1356209 = 1017157) B1017157
theorem B668099 : Blo 443779 668099 := bstep (se 1 (by rfl) ⟨501074, by rfl⟩ : syracuseStep 668099 = 1002149) B1002149
theorem B668129 : Blo 443779 668129 := bstep (se 2 (by rfl) ⟨250548, by rfl⟩ : syracuseStep 668129 = 501097) B501097
theorem B668147 : Blo 443779 668147 := bstep (se 1 (by rfl) ⟨501110, by rfl⟩ : syracuseStep 668147 = 1002221) B1002221
theorem B668177 : Blo 443779 668177 := bstep (se 2 (by rfl) ⟨250566, by rfl⟩ : syracuseStep 668177 = 501133) B501133
theorem B668195 : Blo 443779 668195 := bstep (se 1 (by rfl) ⟨501146, by rfl⟩ : syracuseStep 668195 = 1002293) B1002293
theorem B668225 : Blo 443779 668225 := bstep (se 2 (by rfl) ⟨250584, by rfl⟩ : syracuseStep 668225 = 501169) B501169
theorem B1126993 : Blo 443779 1126993 := bstep (se 2 (by rfl) ⟨422622, by rfl⟩ : syracuseStep 1126993 = 845245) B845245
theorem B668243 : Blo 443779 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B668273 : Blo 443779 668273 := bstep (se 2 (by rfl) ⟨250602, by rfl⟩ : syracuseStep 668273 = 501205) B501205
theorem B668291 : Blo 443779 668291 := bstep (se 1 (by rfl) ⟨501218, by rfl⟩ : syracuseStep 668291 = 1002437) B1002437
theorem B668321 : Blo 443779 668321 := bstep (se 2 (by rfl) ⟨250620, by rfl⟩ : syracuseStep 668321 = 501241) B501241
theorem B668339 : Blo 443779 668339 := bstep (se 1 (by rfl) ⟨501254, by rfl⟩ : syracuseStep 668339 = 1002509) B1002509
theorem B668369 : Blo 443779 668369 := bstep (se 2 (by rfl) ⟨250638, by rfl⟩ : syracuseStep 668369 = 501277) B501277
theorem B668387 : Blo 443779 668387 := bstep (se 1 (by rfl) ⟨501290, by rfl⟩ : syracuseStep 668387 = 1002581) B1002581
theorem B668417 : Blo 443779 668417 := bstep (se 2 (by rfl) ⟨250656, by rfl⟩ : syracuseStep 668417 = 501313) B501313
theorem B668435 : Blo 443779 668435 := bstep (se 1 (by rfl) ⟨501326, by rfl⟩ : syracuseStep 668435 = 1002653) B1002653
theorem B635683 : Blo 443779 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B668465 : Blo 443779 668465 := bstep (se 2 (by rfl) ⟨250674, by rfl⟩ : syracuseStep 668465 = 501349) B501349
theorem B668483 : Blo 443779 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B668513 : Blo 443779 668513 := bstep (se 2 (by rfl) ⟨250692, by rfl⟩ : syracuseStep 668513 = 501385) B501385
theorem B1127267 : Blo 443779 1127267 := bstep (se 1 (by rfl) ⟨845450, by rfl⟩ : syracuseStep 1127267 = 1690901) B1690901
theorem B668531 : Blo 443779 668531 := bstep (se 1 (by rfl) ⟨501398, by rfl⟩ : syracuseStep 668531 = 1002797) B1002797
theorem B635779 : Blo 443779 635779 := bstep (se 1 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 635779 = 953669) B953669
theorem B668561 : Blo 443779 668561 := bstep (se 2 (by rfl) ⟨250710, by rfl⟩ : syracuseStep 668561 = 501421) B501421
theorem B668579 : Blo 443779 668579 := bstep (se 1 (by rfl) ⟨501434, by rfl⟩ : syracuseStep 668579 = 1002869) B1002869
theorem B668609 : Blo 443779 668609 := bstep (se 2 (by rfl) ⟨250728, by rfl⟩ : syracuseStep 668609 = 501457) B501457
theorem B668627 : Blo 443779 668627 := bstep (se 1 (by rfl) ⟨501470, by rfl⟩ : syracuseStep 668627 = 1002941) B1002941
theorem B668657 : Blo 443779 668657 := bstep (se 2 (by rfl) ⟨250746, by rfl⟩ : syracuseStep 668657 = 501493) B501493
theorem B668675 : Blo 443779 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B668705 : Blo 443779 668705 := bstep (se 2 (by rfl) ⟨250764, by rfl⟩ : syracuseStep 668705 = 501529) B501529
theorem B1127459 : Blo 443779 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B668723 : Blo 443779 668723 := bstep (se 1 (by rfl) ⟨501542, by rfl⟩ : syracuseStep 668723 = 1003085) B1003085
theorem B668753 : Blo 443779 668753 := bstep (se 2 (by rfl) ⟨250782, by rfl⟩ : syracuseStep 668753 = 501565) B501565
theorem B668771 : Blo 443779 668771 := bstep (se 1 (by rfl) ⟨501578, by rfl⟩ : syracuseStep 668771 = 1003157) B1003157
theorem B668801 : Blo 443779 668801 := bstep (se 2 (by rfl) ⟨250800, by rfl⟩ : syracuseStep 668801 = 501601) B501601
theorem B668819 : Blo 443779 668819 := bstep (se 1 (by rfl) ⟨501614, by rfl⟩ : syracuseStep 668819 = 1003229) B1003229
theorem B668849 : Blo 443779 668849 := bstep (se 2 (by rfl) ⟨250818, by rfl⟩ : syracuseStep 668849 = 501637) B501637
theorem B668867 : Blo 443779 668867 := bstep (se 1 (by rfl) ⟨501650, by rfl⟩ : syracuseStep 668867 = 1003301) B1003301
theorem B668897 : Blo 443779 668897 := bstep (se 2 (by rfl) ⟨250836, by rfl⟩ : syracuseStep 668897 = 501673) B501673
theorem B668915 : Blo 443779 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B668945 : Blo 443779 668945 := bstep (se 2 (by rfl) ⟨250854, by rfl⟩ : syracuseStep 668945 = 501709) B501709
theorem B668963 : Blo 443779 668963 := bstep (se 1 (by rfl) ⟨501722, by rfl⟩ : syracuseStep 668963 = 1003445) B1003445
theorem B1520945 : Blo 443779 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B668993 : Blo 443779 668993 := bstep (se 2 (by rfl) ⟨250872, by rfl⟩ : syracuseStep 668993 = 501745) B501745
theorem B669011 : Blo 443779 669011 := bstep (se 1 (by rfl) ⟨501758, by rfl⟩ : syracuseStep 669011 = 1003517) B1003517
theorem B669041 : Blo 443779 669041 := bstep (se 2 (by rfl) ⟨250890, by rfl⟩ : syracuseStep 669041 = 501781) B501781
theorem B636275 : Blo 443779 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B669059 : Blo 443779 669059 := bstep (se 1 (by rfl) ⟨501794, by rfl⟩ : syracuseStep 669059 = 1003589) B1003589
theorem B669089 : Blo 443779 669089 := bstep (se 2 (by rfl) ⟨250908, by rfl⟩ : syracuseStep 669089 = 501817) B501817
theorem B669107 : Blo 443779 669107 := bstep (se 1 (by rfl) ⟨501830, by rfl⟩ : syracuseStep 669107 = 1003661) B1003661
theorem B669137 : Blo 443779 669137 := bstep (se 2 (by rfl) ⟨250926, by rfl⟩ : syracuseStep 669137 = 501853) B501853
theorem B669155 : Blo 443779 669155 := bstep (se 1 (by rfl) ⟨501866, by rfl⟩ : syracuseStep 669155 = 1003733) B1003733
theorem B669185 : Blo 443779 669185 := bstep (se 2 (by rfl) ⟨250944, by rfl⟩ : syracuseStep 669185 = 501889) B501889
theorem B669203 : Blo 443779 669203 := bstep (se 1 (by rfl) ⟨501902, by rfl⟩ : syracuseStep 669203 = 1003805) B1003805
theorem B669233 : Blo 443779 669233 := bstep (se 2 (by rfl) ⟨250962, by rfl⟩ : syracuseStep 669233 = 501925) B501925
theorem B669251 : Blo 443779 669251 := bstep (se 1 (by rfl) ⟨501938, by rfl⟩ : syracuseStep 669251 = 1003877) B1003877
theorem B1685069 : Blo 443779 1685069 := bstep (se 3 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 1685069 = 631901) B631901
theorem B669281 : Blo 443779 669281 := bstep (se 2 (by rfl) ⟨250980, by rfl⟩ : syracuseStep 669281 = 501961) B501961
theorem B669299 : Blo 443779 669299 := bstep (se 1 (by rfl) ⟨501974, by rfl⟩ : syracuseStep 669299 = 1003949) B1003949
theorem B669329 : Blo 443779 669329 := bstep (se 2 (by rfl) ⟨250998, by rfl⟩ : syracuseStep 669329 = 501997) B501997
theorem B669347 : Blo 443779 669347 := bstep (se 1 (by rfl) ⟨502010, by rfl⟩ : syracuseStep 669347 = 1004021) B1004021
theorem B669377 : Blo 443779 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B669395 : Blo 443779 669395 := bstep (se 1 (by rfl) ⟨502046, by rfl⟩ : syracuseStep 669395 = 1004093) B1004093
theorem B669425 : Blo 443779 669425 := bstep (se 2 (by rfl) ⟨251034, by rfl⟩ : syracuseStep 669425 = 502069) B502069
theorem B669443 : Blo 443779 669443 := bstep (se 1 (by rfl) ⟨502082, by rfl⟩ : syracuseStep 669443 = 1004165) B1004165
theorem B669473 : Blo 443779 669473 := bstep (se 2 (by rfl) ⟨251052, by rfl⟩ : syracuseStep 669473 = 502105) B502105
theorem B669491 : Blo 443779 669491 := bstep (se 1 (by rfl) ⟨502118, by rfl⟩ : syracuseStep 669491 = 1004237) B1004237
theorem B669521 : Blo 443779 669521 := bstep (se 2 (by rfl) ⟨251070, by rfl⟩ : syracuseStep 669521 = 502141) B502141
theorem B669539 : Blo 443779 669539 := bstep (se 1 (by rfl) ⟨502154, by rfl⟩ : syracuseStep 669539 = 1004309) B1004309
theorem B669569 : Blo 443779 669569 := bstep (se 2 (by rfl) ⟨251088, by rfl⟩ : syracuseStep 669569 = 502177) B502177
theorem B2144141 : Blo 443779 2144141 := bstep (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) B804053
theorem B669587 : Blo 443779 669587 := bstep (se 1 (by rfl) ⟨502190, by rfl⟩ : syracuseStep 669587 = 1004381) B1004381
theorem B1423277 : Blo 443779 1423277 := bstep (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) B533729
theorem B669617 : Blo 443779 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B669635 : Blo 443779 669635 := bstep (se 1 (by rfl) ⟨502226, by rfl⟩ : syracuseStep 669635 = 1004453) B1004453
theorem B604099 : Blo 443779 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B1292237 : Blo 443779 1292237 := bstep (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) B484589
theorem B1128401 : Blo 443779 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B669665 : Blo 443779 669665 := bstep (se 2 (by rfl) ⟨251124, by rfl⟩ : syracuseStep 669665 = 502249) B502249
theorem B636913 : Blo 443779 636913 := bstep (se 2 (by rfl) ⟨238842, by rfl⟩ : syracuseStep 636913 = 477685) B477685
theorem B669683 : Blo 443779 669683 := bstep (se 1 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 669683 = 1004525) B1004525
theorem B1128451 : Blo 443779 1128451 := bstep (se 1 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 1128451 = 1692677) B1692677
theorem B669713 : Blo 443779 669713 := bstep (se 2 (by rfl) ⟨251142, by rfl⟩ : syracuseStep 669713 = 502285) B502285
theorem B669731 : Blo 443779 669731 := bstep (se 1 (by rfl) ⟨502298, by rfl⟩ : syracuseStep 669731 = 1004597) B1004597
theorem B669761 : Blo 443779 669761 := bstep (se 2 (by rfl) ⟨251160, by rfl⟩ : syracuseStep 669761 = 502321) B502321
theorem B669779 : Blo 443779 669779 := bstep (se 1 (by rfl) ⟨502334, by rfl⟩ : syracuseStep 669779 = 1004669) B1004669
theorem B669809 : Blo 443779 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B669827 : Blo 443779 669827 := bstep (se 1 (by rfl) ⟨502370, by rfl⟩ : syracuseStep 669827 = 1004741) B1004741
theorem B1128593 : Blo 443779 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B669857 : Blo 443779 669857 := bstep (se 2 (by rfl) ⟨251196, by rfl⟩ : syracuseStep 669857 = 502393) B502393
theorem B669875 : Blo 443779 669875 := bstep (se 1 (by rfl) ⟨502406, by rfl⟩ : syracuseStep 669875 = 1004813) B1004813
theorem B669905 : Blo 443779 669905 := bstep (se 2 (by rfl) ⟨251214, by rfl⟩ : syracuseStep 669905 = 502429) B502429
theorem B669923 : Blo 443779 669923 := bstep (se 1 (by rfl) ⟨502442, by rfl⟩ : syracuseStep 669923 = 1004885) B1004885
theorem B669953 : Blo 443779 669953 := bstep (se 2 (by rfl) ⟨251232, by rfl⟩ : syracuseStep 669953 = 502465) B502465
theorem B669971 : Blo 443779 669971 := bstep (se 1 (by rfl) ⟨502478, by rfl⟩ : syracuseStep 669971 = 1004957) B1004957
theorem B670001 : Blo 443779 670001 := bstep (se 2 (by rfl) ⟨251250, by rfl⟩ : syracuseStep 670001 = 502501) B502501
theorem B637249 : Blo 443779 637249 := bstep (se 2 (by rfl) ⟨238968, by rfl⟩ : syracuseStep 637249 = 477937) B477937
theorem B670019 : Blo 443779 670019 := bstep (se 1 (by rfl) ⟨502514, by rfl⟩ : syracuseStep 670019 = 1005029) B1005029
theorem B670049 : Blo 443779 670049 := bstep (se 2 (by rfl) ⟨251268, by rfl⟩ : syracuseStep 670049 = 502537) B502537
theorem B1685873 : Blo 443779 1685873 := bstep (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) B1264405
theorem B670067 : Blo 443779 670067 := bstep (se 1 (by rfl) ⟨502550, by rfl⟩ : syracuseStep 670067 = 1005101) B1005101
theorem B670097 : Blo 443779 670097 := bstep (se 2 (by rfl) ⟨251286, by rfl⟩ : syracuseStep 670097 = 502573) B502573
theorem B670115 : Blo 443779 670115 := bstep (se 1 (by rfl) ⟨502586, by rfl⟩ : syracuseStep 670115 = 1005173) B1005173
theorem B670145 : Blo 443779 670145 := bstep (se 2 (by rfl) ⟨251304, by rfl⟩ : syracuseStep 670145 = 502609) B502609
theorem B670163 : Blo 443779 670163 := bstep (se 1 (by rfl) ⟨502622, by rfl⟩ : syracuseStep 670163 = 1005245) B1005245
theorem B670193 : Blo 443779 670193 := bstep (se 2 (by rfl) ⟨251322, by rfl⟩ : syracuseStep 670193 = 502645) B502645
theorem B670211 : Blo 443779 670211 := bstep (se 1 (by rfl) ⟨502658, by rfl⟩ : syracuseStep 670211 = 1005317) B1005317
theorem B4831757 : Blo 443779 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B1161745 : Blo 443779 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B670241 : Blo 443779 670241 := bstep (se 2 (by rfl) ⟨251340, by rfl⟩ : syracuseStep 670241 = 502681) B502681
theorem B670259 : Blo 443779 670259 := bstep (se 1 (by rfl) ⟨502694, by rfl⟩ : syracuseStep 670259 = 1005389) B1005389
theorem B18233909 : Blo 443779 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B670289 : Blo 443779 670289 := bstep (se 2 (by rfl) ⟨251358, by rfl⟩ : syracuseStep 670289 = 502717) B502717
theorem B1358435 : Blo 443779 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B670307 : Blo 443779 670307 := bstep (se 1 (by rfl) ⟨502730, by rfl⟩ : syracuseStep 670307 = 1005461) B1005461
theorem B670337 : Blo 443779 670337 := bstep (se 2 (by rfl) ⟨251376, by rfl⟩ : syracuseStep 670337 = 502753) B502753
theorem B670355 : Blo 443779 670355 := bstep (se 1 (by rfl) ⟨502766, by rfl⟩ : syracuseStep 670355 = 1005533) B1005533
theorem B965297 : Blo 443779 965297 := bstep (se 2 (by rfl) ⟨361986, by rfl⟩ : syracuseStep 965297 = 723973) B723973
theorem B670385 : Blo 443779 670385 := bstep (se 2 (by rfl) ⟨251394, by rfl⟩ : syracuseStep 670385 = 502789) B502789
theorem B670403 : Blo 443779 670403 := bstep (se 1 (by rfl) ⟨502802, by rfl⟩ : syracuseStep 670403 = 1005605) B1005605
theorem B670433 : Blo 443779 670433 := bstep (se 2 (by rfl) ⟨251412, by rfl⟩ : syracuseStep 670433 = 502825) B502825
theorem B670451 : Blo 443779 670451 := bstep (se 1 (by rfl) ⟨502838, by rfl⟩ : syracuseStep 670451 = 1005677) B1005677
theorem B899857 : Blo 443779 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B670481 : Blo 443779 670481 := bstep (se 2 (by rfl) ⟨251430, by rfl⟩ : syracuseStep 670481 = 502861) B502861
theorem B670499 : Blo 443779 670499 := bstep (se 1 (by rfl) ⟨502874, by rfl⟩ : syracuseStep 670499 = 1005749) B1005749
theorem B670529 : Blo 443779 670529 := bstep (se 2 (by rfl) ⟨251448, by rfl⟩ : syracuseStep 670529 = 502897) B502897
theorem B899921 : Blo 443779 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B670547 : Blo 443779 670547 := bstep (se 1 (by rfl) ⟨502910, by rfl⟩ : syracuseStep 670547 = 1005821) B1005821
theorem B670577 : Blo 443779 670577 := bstep (se 2 (by rfl) ⟨251466, by rfl⟩ : syracuseStep 670577 = 502933) B502933
theorem B670595 : Blo 443779 670595 := bstep (se 1 (by rfl) ⟨502946, by rfl⟩ : syracuseStep 670595 = 1005893) B1005893
theorem B3259277 : Blo 443779 3259277 := bstep (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) B1222229
theorem B670625 : Blo 443779 670625 := bstep (se 2 (by rfl) ⟨251484, by rfl⟩ : syracuseStep 670625 = 502969) B502969
theorem B670643 : Blo 443779 670643 := bstep (se 1 (by rfl) ⟨502982, by rfl⟩ : syracuseStep 670643 = 1005965) B1005965
theorem B670673 : Blo 443779 670673 := bstep (se 2 (by rfl) ⟨251502, by rfl⟩ : syracuseStep 670673 = 503005) B503005
theorem B670691 : Blo 443779 670691 := bstep (se 1 (by rfl) ⟨503018, by rfl⟩ : syracuseStep 670691 = 1006037) B1006037
theorem B670721 : Blo 443779 670721 := bstep (se 2 (by rfl) ⟨251520, by rfl⟩ : syracuseStep 670721 = 503041) B503041
theorem B1686541 : Blo 443779 1686541 := bstep (se 3 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 1686541 = 632453) B632453
theorem B474131 : Blo 443779 474131 := bstep (se 1 (by rfl) ⟨355598, by rfl⟩ : syracuseStep 474131 = 711197) B711197
theorem B670739 : Blo 443779 670739 := bstep (se 1 (by rfl) ⟨503054, by rfl⟩ : syracuseStep 670739 = 1006109) B1006109
theorem B670769 : Blo 443779 670769 := bstep (se 2 (by rfl) ⟨251538, by rfl⟩ : syracuseStep 670769 = 503077) B503077
theorem B670787 : Blo 443779 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B670817 : Blo 443779 670817 := bstep (se 2 (by rfl) ⟨251556, by rfl⟩ : syracuseStep 670817 = 503113) B503113
theorem B998513 : Blo 443779 998513 := bstep (se 2 (by rfl) ⟨374442, by rfl⟩ : syracuseStep 998513 = 748885) B748885
theorem B1129585 : Blo 443779 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B670835 : Blo 443779 670835 := bstep (se 1 (by rfl) ⟨503126, by rfl⟩ : syracuseStep 670835 = 1006253) B1006253
theorem B998531 : Blo 443779 998531 := bstep (se 1 (by rfl) ⟨748898, by rfl⟩ : syracuseStep 998531 = 1497797) B1497797
theorem B670865 : Blo 443779 670865 := bstep (se 2 (by rfl) ⟨251574, by rfl⟩ : syracuseStep 670865 = 503149) B503149
theorem B670883 : Blo 443779 670883 := bstep (se 1 (by rfl) ⟨503162, by rfl⟩ : syracuseStep 670883 = 1006325) B1006325
theorem B1424557 : Blo 443779 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B670913 : Blo 443779 670913 := bstep (se 2 (by rfl) ⟨251592, by rfl⟩ : syracuseStep 670913 = 503185) B503185
theorem B670931 : Blo 443779 670931 := bstep (se 1 (by rfl) ⟨503198, by rfl⟩ : syracuseStep 670931 = 1006397) B1006397
theorem B670961 : Blo 443779 670961 := bstep (se 2 (by rfl) ⟨251610, by rfl⟩ : syracuseStep 670961 = 503221) B503221
theorem B670979 : Blo 443779 670979 := bstep (se 1 (by rfl) ⟨503234, by rfl⟩ : syracuseStep 670979 = 1006469) B1006469
theorem B671009 : Blo 443779 671009 := bstep (se 2 (by rfl) ⟨251628, by rfl⟩ : syracuseStep 671009 = 503257) B503257
theorem B671027 : Blo 443779 671027 := bstep (se 1 (by rfl) ⟨503270, by rfl⟩ : syracuseStep 671027 = 1006541) B1006541
theorem B671057 : Blo 443779 671057 := bstep (se 2 (by rfl) ⟨251646, by rfl⟩ : syracuseStep 671057 = 503293) B503293
theorem B671075 : Blo 443779 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B671105 : Blo 443779 671105 := bstep (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) B503329
theorem B1129859 : Blo 443779 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B998801 : Blo 443779 998801 := bstep (se 2 (by rfl) ⟨374550, by rfl⟩ : syracuseStep 998801 = 749101) B749101
theorem B671123 : Blo 443779 671123 := bstep (se 1 (by rfl) ⟨503342, by rfl⟩ : syracuseStep 671123 = 1006685) B1006685
theorem B998819 : Blo 443779 998819 := bstep (se 1 (by rfl) ⟨749114, by rfl⟩ : syracuseStep 998819 = 1498229) B1498229
theorem B703907 : Blo 443779 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B671153 : Blo 443779 671153 := bstep (se 2 (by rfl) ⟨251682, by rfl⟩ : syracuseStep 671153 = 503365) B503365
theorem B671171 : Blo 443779 671171 := bstep (se 1 (by rfl) ⟨503378, by rfl⟩ : syracuseStep 671171 = 1006757) B1006757
theorem B671201 : Blo 443779 671201 := bstep (se 2 (by rfl) ⟨251700, by rfl⟩ : syracuseStep 671201 = 503401) B503401
theorem B671219 : Blo 443779 671219 := bstep (se 1 (by rfl) ⟨503414, by rfl⟩ : syracuseStep 671219 = 1006829) B1006829
theorem B671249 : Blo 443779 671249 := bstep (se 2 (by rfl) ⟨251718, by rfl⟩ : syracuseStep 671249 = 503437) B503437
theorem B671267 : Blo 443779 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B671297 : Blo 443779 671297 := bstep (se 2 (by rfl) ⟨251736, by rfl⟩ : syracuseStep 671297 = 503473) B503473
theorem B1130051 : Blo 443779 1130051 := bstep (se 1 (by rfl) ⟨847538, by rfl⟩ : syracuseStep 1130051 = 1695077) B1695077
theorem B671315 : Blo 443779 671315 := bstep (se 1 (by rfl) ⟨503486, by rfl⟩ : syracuseStep 671315 = 1006973) B1006973
theorem B671345 : Blo 443779 671345 := bstep (se 2 (by rfl) ⟨251754, by rfl⟩ : syracuseStep 671345 = 503509) B503509
theorem B671363 : Blo 443779 671363 := bstep (se 1 (by rfl) ⟨503522, by rfl⟩ : syracuseStep 671363 = 1007045) B1007045
theorem B671393 : Blo 443779 671393 := bstep (se 2 (by rfl) ⟨251772, by rfl⟩ : syracuseStep 671393 = 503545) B503545
theorem B1425059 : Blo 443779 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B999089 : Blo 443779 999089 := bstep (se 2 (by rfl) ⟨374658, by rfl⟩ : syracuseStep 999089 = 749317) B749317
theorem B671411 : Blo 443779 671411 := bstep (se 1 (by rfl) ⟨503558, by rfl⟩ : syracuseStep 671411 = 1007117) B1007117
theorem B999107 : Blo 443779 999107 := bstep (se 1 (by rfl) ⟨749330, by rfl⟩ : syracuseStep 999107 = 1498661) B1498661
theorem B671441 : Blo 443779 671441 := bstep (se 2 (by rfl) ⟨251790, by rfl⟩ : syracuseStep 671441 = 503581) B503581
theorem B671459 : Blo 443779 671459 := bstep (se 1 (by rfl) ⟨503594, by rfl⟩ : syracuseStep 671459 = 1007189) B1007189
theorem B1162993 : Blo 443779 1162993 := bstep (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) B872245
theorem B671489 : Blo 443779 671489 := bstep (se 2 (by rfl) ⟨251808, by rfl⟩ : syracuseStep 671489 = 503617) B503617
theorem B671507 : Blo 443779 671507 := bstep (se 1 (by rfl) ⟨503630, by rfl⟩ : syracuseStep 671507 = 1007261) B1007261
theorem B1687331 : Blo 443779 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B671537 : Blo 443779 671537 := bstep (se 2 (by rfl) ⟨251826, by rfl⟩ : syracuseStep 671537 = 503653) B503653
theorem B671555 : Blo 443779 671555 := bstep (se 1 (by rfl) ⟨503666, by rfl⟩ : syracuseStep 671555 = 1007333) B1007333
theorem B671585 : Blo 443779 671585 := bstep (se 2 (by rfl) ⟨251844, by rfl⟩ : syracuseStep 671585 = 503689) B503689
theorem B671603 : Blo 443779 671603 := bstep (se 1 (by rfl) ⟨503702, by rfl⟩ : syracuseStep 671603 = 1007405) B1007405
theorem B671633 : Blo 443779 671633 := bstep (se 2 (by rfl) ⟨251862, by rfl⟩ : syracuseStep 671633 = 503725) B503725
theorem B671651 : Blo 443779 671651 := bstep (se 1 (by rfl) ⟨503738, by rfl⟩ : syracuseStep 671651 = 1007477) B1007477
theorem B475075 : Blo 443779 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B999377 : Blo 443779 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B999395 : Blo 443779 999395 := bstep (se 1 (by rfl) ⟨749546, by rfl⟩ : syracuseStep 999395 = 1499093) B1499093
theorem B2572273 : Blo 443779 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B802865 : Blo 443779 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B901187 : Blo 443779 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B901219 : Blo 443779 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B2867363 : Blo 443779 2867363 := bstep (se 1 (by rfl) ⟨2150522, by rfl⟩ : syracuseStep 2867363 = 4301045) B4301045
theorem B999665 : Blo 443779 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B999683 : Blo 443779 999683 := bstep (se 1 (by rfl) ⟨749762, by rfl⟩ : syracuseStep 999683 = 1499525) B1499525
theorem B803153 : Blo 443779 803153 := bstep (se 2 (by rfl) ⟨301182, by rfl⟩ : syracuseStep 803153 = 602365) B602365
theorem B1687985 : Blo 443779 1687985 := bstep (se 2 (by rfl) ⟨632994, by rfl⟩ : syracuseStep 1687985 = 1265989) B1265989
theorem B3817955 : Blo 443779 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B1130993 : Blo 443779 1130993 := bstep (se 2 (by rfl) ⟨424122, by rfl⟩ : syracuseStep 1130993 = 848245) B848245
theorem B999953 : Blo 443779 999953 := bstep (se 2 (by rfl) ⟨374982, by rfl⟩ : syracuseStep 999953 = 749965) B749965
theorem B999971 : Blo 443779 999971 := bstep (se 1 (by rfl) ⟨749978, by rfl⟩ : syracuseStep 999971 = 1499957) B1499957
theorem B1131043 : Blo 443779 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B7225969 : Blo 443779 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B2867825 : Blo 443779 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B1131185 : Blo 443779 1131185 := bstep (se 2 (by rfl) ⟨424194, by rfl⟩ : syracuseStep 1131185 = 848389) B848389
theorem B1000241 : Blo 443779 1000241 := bstep (se 2 (by rfl) ⟨375090, by rfl⟩ : syracuseStep 1000241 = 750181) B750181
theorem B1000259 : Blo 443779 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B2540429 : Blo 443779 2540429 := bstep (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) B952661
theorem B967601 : Blo 443779 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B1164241 : Blo 443779 1164241 := bstep (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) B873181
theorem B1426403 : Blo 443779 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1360867 : Blo 443779 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1000529 : Blo 443779 1000529 := bstep (se 2 (by rfl) ⟨375198, by rfl⟩ : syracuseStep 1000529 = 750397) B750397
theorem B902225 : Blo 443779 902225 := bstep (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) B676669
theorem B1000547 : Blo 443779 1000547 := bstep (se 1 (by rfl) ⟨750410, by rfl⟩ : syracuseStep 1000547 = 1500821) B1500821
theorem B476339 : Blo 443779 476339 := bstep (se 1 (by rfl) ⟨357254, by rfl⟩ : syracuseStep 476339 = 714509) B714509
theorem B1000817 : Blo 443779 1000817 := bstep (se 2 (by rfl) ⟨375306, by rfl⟩ : syracuseStep 1000817 = 750613) B750613
theorem B443779 : Blo 443779 443779 := bstep (se 1 (by rfl) ⟨332834, by rfl⟩ : syracuseStep 443779 = 665669) B665669
theorem B1000835 : Blo 443779 1000835 := bstep (se 1 (by rfl) ⟨750626, by rfl⟩ : syracuseStep 1000835 = 1501253) B1501253
theorem B443795 : Blo 443779 443795 := bstep (se 1 (by rfl) ⟨332846, by rfl⟩ : syracuseStep 443795 = 665693) B665693
theorem B443811 : Blo 443779 443811 := bstep (se 1 (by rfl) ⟨332858, by rfl⟩ : syracuseStep 443811 = 665717) B665717
theorem B443827 : Blo 443779 443827 := bstep (se 1 (by rfl) ⟨332870, by rfl⟩ : syracuseStep 443827 = 665741) B665741
theorem B443843 : Blo 443779 443843 := bstep (se 1 (by rfl) ⟨332882, by rfl⟩ : syracuseStep 443843 = 665765) B665765
theorem B443859 : Blo 443779 443859 := bstep (se 1 (by rfl) ⟨332894, by rfl⟩ : syracuseStep 443859 = 665789) B665789
theorem B443875 : Blo 443779 443875 := bstep (se 1 (by rfl) ⟨332906, by rfl⟩ : syracuseStep 443875 = 665813) B665813
theorem B443891 : Blo 443779 443891 := bstep (se 1 (by rfl) ⟨332918, by rfl⟩ : syracuseStep 443891 = 665837) B665837
theorem B443907 : Blo 443779 443907 := bstep (se 1 (by rfl) ⟨332930, by rfl⟩ : syracuseStep 443907 = 665861) B665861
theorem B443923 : Blo 443779 443923 := bstep (se 1 (by rfl) ⟨332942, by rfl⟩ : syracuseStep 443923 = 665885) B665885
theorem B443939 : Blo 443779 443939 := bstep (se 1 (by rfl) ⟨332954, by rfl⟩ : syracuseStep 443939 = 665909) B665909
theorem B2606627 : Blo 443779 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B443955 : Blo 443779 443955 := bstep (se 1 (by rfl) ⟨332966, by rfl⟩ : syracuseStep 443955 = 665933) B665933
theorem B443971 : Blo 443779 443971 := bstep (se 1 (by rfl) ⟨332978, by rfl⟩ : syracuseStep 443971 = 665957) B665957
theorem B443987 : Blo 443779 443987 := bstep (se 1 (by rfl) ⟨332990, by rfl⟩ : syracuseStep 443987 = 665981) B665981
theorem B444003 : Blo 443779 444003 := bstep (se 1 (by rfl) ⟨333002, by rfl⟩ : syracuseStep 444003 = 666005) B666005
theorem B444019 : Blo 443779 444019 := bstep (se 1 (by rfl) ⟨333014, by rfl⟩ : syracuseStep 444019 = 666029) B666029
theorem B444035 : Blo 443779 444035 := bstep (se 1 (by rfl) ⟨333026, by rfl⟩ : syracuseStep 444035 = 666053) B666053
theorem B1001105 : Blo 443779 1001105 := bstep (se 2 (by rfl) ⟨375414, by rfl⟩ : syracuseStep 1001105 = 750829) B750829
theorem B1132177 : Blo 443779 1132177 := bstep (se 2 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 1132177 = 849133) B849133
theorem B444051 : Blo 443779 444051 := bstep (se 1 (by rfl) ⟨333038, by rfl⟩ : syracuseStep 444051 = 666077) B666077
theorem B444067 : Blo 443779 444067 := bstep (se 1 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 444067 = 666101) B666101
theorem B1001123 : Blo 443779 1001123 := bstep (se 1 (by rfl) ⟨750842, by rfl⟩ : syracuseStep 1001123 = 1501685) B1501685
theorem B444083 : Blo 443779 444083 := bstep (se 1 (by rfl) ⟨333062, by rfl⟩ : syracuseStep 444083 = 666125) B666125
theorem B444099 : Blo 443779 444099 := bstep (se 1 (by rfl) ⟨333074, by rfl⟩ : syracuseStep 444099 = 666149) B666149
theorem B444115 : Blo 443779 444115 := bstep (se 1 (by rfl) ⟨333086, by rfl⟩ : syracuseStep 444115 = 666173) B666173
theorem B444131 : Blo 443779 444131 := bstep (se 1 (by rfl) ⟨333098, by rfl⟩ : syracuseStep 444131 = 666197) B666197
theorem B3393251 : Blo 443779 3393251 := bstep (se 1 (by rfl) ⟨2544938, by rfl⟩ : syracuseStep 3393251 = 5089877) B5089877
theorem B444147 : Blo 443779 444147 := bstep (se 1 (by rfl) ⟨333110, by rfl⟩ : syracuseStep 444147 = 666221) B666221
theorem B444163 : Blo 443779 444163 := bstep (se 1 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 444163 = 666245) B666245
theorem B444179 : Blo 443779 444179 := bstep (se 1 (by rfl) ⟨333134, by rfl⟩ : syracuseStep 444179 = 666269) B666269
theorem B444195 : Blo 443779 444195 := bstep (se 1 (by rfl) ⟨333146, by rfl⟩ : syracuseStep 444195 = 666293) B666293
theorem B968483 : Blo 443779 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B444211 : Blo 443779 444211 := bstep (se 1 (by rfl) ⟨333158, by rfl⟩ : syracuseStep 444211 = 666317) B666317
theorem B444227 : Blo 443779 444227 := bstep (se 1 (by rfl) ⟨333170, by rfl⟩ : syracuseStep 444227 = 666341) B666341
theorem B444243 : Blo 443779 444243 := bstep (se 1 (by rfl) ⟨333182, by rfl⟩ : syracuseStep 444243 = 666365) B666365
theorem B444259 : Blo 443779 444259 := bstep (se 1 (by rfl) ⟨333194, by rfl⟩ : syracuseStep 444259 = 666389) B666389
theorem B1689443 : Blo 443779 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B1689457 : Blo 443779 1689457 := bstep (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) B1267093
theorem B444275 : Blo 443779 444275 := bstep (se 1 (by rfl) ⟨333206, by rfl⟩ : syracuseStep 444275 = 666413) B666413
theorem B444291 : Blo 443779 444291 := bstep (se 1 (by rfl) ⟨333218, by rfl⟩ : syracuseStep 444291 = 666437) B666437
theorem B444307 : Blo 443779 444307 := bstep (se 1 (by rfl) ⟨333230, by rfl⟩ : syracuseStep 444307 = 666461) B666461
theorem B444323 : Blo 443779 444323 := bstep (se 1 (by rfl) ⟨333242, by rfl⟩ : syracuseStep 444323 = 666485) B666485
theorem B477091 : Blo 443779 477091 := bstep (se 1 (by rfl) ⟨357818, by rfl⟩ : syracuseStep 477091 = 715637) B715637
theorem B1132451 : Blo 443779 1132451 := bstep (se 1 (by rfl) ⟨849338, by rfl⟩ : syracuseStep 1132451 = 1698677) B1698677
theorem B1001393 : Blo 443779 1001393 := bstep (se 2 (by rfl) ⟨375522, by rfl⟩ : syracuseStep 1001393 = 751045) B751045
theorem B1427377 : Blo 443779 1427377 := bstep (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) B1070533
theorem B444339 : Blo 443779 444339 := bstep (se 1 (by rfl) ⟨333254, by rfl⟩ : syracuseStep 444339 = 666509) B666509
theorem B444355 : Blo 443779 444355 := bstep (se 1 (by rfl) ⟨333266, by rfl⟩ : syracuseStep 444355 = 666533) B666533
theorem B1001411 : Blo 443779 1001411 := bstep (se 1 (by rfl) ⟨751058, by rfl⟩ : syracuseStep 1001411 = 1502117) B1502117
theorem B444371 : Blo 443779 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B444387 : Blo 443779 444387 := bstep (se 1 (by rfl) ⟨333290, by rfl⟩ : syracuseStep 444387 = 666581) B666581
theorem B444403 : Blo 443779 444403 := bstep (se 1 (by rfl) ⟨333302, by rfl⟩ : syracuseStep 444403 = 666605) B666605
theorem B444419 : Blo 443779 444419 := bstep (se 1 (by rfl) ⟨333314, by rfl⟩ : syracuseStep 444419 = 666629) B666629
theorem B444435 : Blo 443779 444435 := bstep (se 1 (by rfl) ⟨333326, by rfl⟩ : syracuseStep 444435 = 666653) B666653
theorem B444451 : Blo 443779 444451 := bstep (se 1 (by rfl) ⟨333338, by rfl⟩ : syracuseStep 444451 = 666677) B666677
theorem B444467 : Blo 443779 444467 := bstep (se 1 (by rfl) ⟨333350, by rfl⟩ : syracuseStep 444467 = 666701) B666701
theorem B444483 : Blo 443779 444483 := bstep (se 1 (by rfl) ⟨333362, by rfl⟩ : syracuseStep 444483 = 666725) B666725
theorem B444499 : Blo 443779 444499 := bstep (se 1 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 444499 = 666749) B666749
theorem B444515 : Blo 443779 444515 := bstep (se 1 (by rfl) ⟨333386, by rfl⟩ : syracuseStep 444515 = 666773) B666773
theorem B1132643 : Blo 443779 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B444531 : Blo 443779 444531 := bstep (se 1 (by rfl) ⟨333398, by rfl⟩ : syracuseStep 444531 = 666797) B666797
theorem B444547 : Blo 443779 444547 := bstep (se 1 (by rfl) ⟨333410, by rfl⟩ : syracuseStep 444547 = 666821) B666821
theorem B444563 : Blo 443779 444563 := bstep (se 1 (by rfl) ⟨333422, by rfl⟩ : syracuseStep 444563 = 666845) B666845
theorem B444579 : Blo 443779 444579 := bstep (se 1 (by rfl) ⟨333434, by rfl⟩ : syracuseStep 444579 = 666869) B666869
theorem B477347 : Blo 443779 477347 := bstep (se 1 (by rfl) ⟨358010, by rfl⟩ : syracuseStep 477347 = 716021) B716021
theorem B1427633 : Blo 443779 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B444595 : Blo 443779 444595 := bstep (se 1 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 444595 = 666893) B666893
theorem B444611 : Blo 443779 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B1001681 : Blo 443779 1001681 := bstep (se 2 (by rfl) ⟨375630, by rfl⟩ : syracuseStep 1001681 = 751261) B751261
theorem B444627 : Blo 443779 444627 := bstep (se 1 (by rfl) ⟨333470, by rfl⟩ : syracuseStep 444627 = 666941) B666941
theorem B444643 : Blo 443779 444643 := bstep (se 1 (by rfl) ⟨333482, by rfl⟩ : syracuseStep 444643 = 666965) B666965
theorem B1001699 : Blo 443779 1001699 := bstep (se 1 (by rfl) ⟨751274, by rfl⟩ : syracuseStep 1001699 = 1502549) B1502549
theorem B444659 : Blo 443779 444659 := bstep (se 1 (by rfl) ⟨333494, by rfl⟩ : syracuseStep 444659 = 666989) B666989
theorem B444675 : Blo 443779 444675 := bstep (se 1 (by rfl) ⟨333506, by rfl⟩ : syracuseStep 444675 = 667013) B667013
theorem B444691 : Blo 443779 444691 := bstep (se 1 (by rfl) ⟨333518, by rfl⟩ : syracuseStep 444691 = 667037) B667037
theorem B444707 : Blo 443779 444707 := bstep (se 1 (by rfl) ⟨333530, by rfl⟩ : syracuseStep 444707 = 667061) B667061
theorem B444723 : Blo 443779 444723 := bstep (se 1 (by rfl) ⟨333542, by rfl⟩ : syracuseStep 444723 = 667085) B667085
theorem B444739 : Blo 443779 444739 := bstep (se 1 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 444739 = 667109) B667109
theorem B444755 : Blo 443779 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B1067363 : Blo 443779 1067363 := bstep (se 1 (by rfl) ⟨800522, by rfl⟩ : syracuseStep 1067363 = 1601045) B1601045
theorem B444771 : Blo 443779 444771 := bstep (se 1 (by rfl) ⟨333578, by rfl⟩ : syracuseStep 444771 = 667157) B667157
theorem B444787 : Blo 443779 444787 := bstep (se 1 (by rfl) ⟨333590, by rfl⟩ : syracuseStep 444787 = 667181) B667181
theorem B444803 : Blo 443779 444803 := bstep (se 1 (by rfl) ⟨333602, by rfl⟩ : syracuseStep 444803 = 667205) B667205
theorem B444819 : Blo 443779 444819 := bstep (se 1 (by rfl) ⟨333614, by rfl⟩ : syracuseStep 444819 = 667229) B667229
theorem B444835 : Blo 443779 444835 := bstep (se 1 (by rfl) ⟨333626, by rfl⟩ : syracuseStep 444835 = 667253) B667253
theorem B444851 : Blo 443779 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B444867 : Blo 443779 444867 := bstep (se 1 (by rfl) ⟨333650, by rfl⟩ : syracuseStep 444867 = 667301) B667301
theorem B444883 : Blo 443779 444883 := bstep (se 1 (by rfl) ⟨333662, by rfl⟩ : syracuseStep 444883 = 667325) B667325
theorem B444899 : Blo 443779 444899 := bstep (se 1 (by rfl) ⟨333674, by rfl⟩ : syracuseStep 444899 = 667349) B667349
theorem B1001969 : Blo 443779 1001969 := bstep (se 2 (by rfl) ⟨375738, by rfl⟩ : syracuseStep 1001969 = 751477) B751477
theorem B444915 : Blo 443779 444915 := bstep (se 1 (by rfl) ⟨333686, by rfl⟩ : syracuseStep 444915 = 667373) B667373
theorem B772609 : Blo 443779 772609 := bstep (se 2 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 772609 = 579457) B579457
theorem B444931 : Blo 443779 444931 := bstep (se 1 (by rfl) ⟨333698, by rfl⟩ : syracuseStep 444931 = 667397) B667397
theorem B1001987 : Blo 443779 1001987 := bstep (se 1 (by rfl) ⟨751490, by rfl⟩ : syracuseStep 1001987 = 1502981) B1502981
theorem B444947 : Blo 443779 444947 := bstep (se 1 (by rfl) ⟨333710, by rfl⟩ : syracuseStep 444947 = 667421) B667421
theorem B444963 : Blo 443779 444963 := bstep (se 1 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 444963 = 667445) B667445
theorem B1264177 : Blo 443779 1264177 := bstep (se 2 (by rfl) ⟨474066, by rfl⟩ : syracuseStep 1264177 = 948133) B948133
theorem B444979 : Blo 443779 444979 := bstep (se 1 (by rfl) ⟨333734, by rfl⟩ : syracuseStep 444979 = 667469) B667469
theorem B444995 : Blo 443779 444995 := bstep (se 1 (by rfl) ⟨333746, by rfl⟩ : syracuseStep 444995 = 667493) B667493
theorem B445011 : Blo 443779 445011 := bstep (se 1 (by rfl) ⟨333758, by rfl⟩ : syracuseStep 445011 = 667517) B667517
theorem B445027 : Blo 443779 445027 := bstep (se 1 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 445027 = 667541) B667541
theorem B445043 : Blo 443779 445043 := bstep (se 1 (by rfl) ⟨333782, by rfl⟩ : syracuseStep 445043 = 667565) B667565
theorem B445059 : Blo 443779 445059 := bstep (se 1 (by rfl) ⟨333794, by rfl⟩ : syracuseStep 445059 = 667589) B667589
theorem B445075 : Blo 443779 445075 := bstep (se 1 (by rfl) ⟨333806, by rfl⟩ : syracuseStep 445075 = 667613) B667613
theorem B445091 : Blo 443779 445091 := bstep (se 1 (by rfl) ⟨333818, by rfl⟩ : syracuseStep 445091 = 667637) B667637
theorem B805553 : Blo 443779 805553 := bstep (se 2 (by rfl) ⟨302082, by rfl⟩ : syracuseStep 805553 = 604165) B604165
theorem B445107 : Blo 443779 445107 := bstep (se 1 (by rfl) ⟨333830, by rfl⟩ : syracuseStep 445107 = 667661) B667661
theorem B445123 : Blo 443779 445123 := bstep (se 1 (by rfl) ⟨333842, by rfl⟩ : syracuseStep 445123 = 667685) B667685
theorem B445139 : Blo 443779 445139 := bstep (se 1 (by rfl) ⟨333854, by rfl⟩ : syracuseStep 445139 = 667709) B667709
theorem B445155 : Blo 443779 445155 := bstep (se 1 (by rfl) ⟨333866, by rfl⟩ : syracuseStep 445155 = 667733) B667733
theorem B445171 : Blo 443779 445171 := bstep (se 1 (by rfl) ⟨333878, by rfl⟩ : syracuseStep 445171 = 667757) B667757
theorem B445187 : Blo 443779 445187 := bstep (se 1 (by rfl) ⟨333890, by rfl⟩ : syracuseStep 445187 = 667781) B667781
theorem B1002257 : Blo 443779 1002257 := bstep (se 2 (by rfl) ⟨375846, by rfl⟩ : syracuseStep 1002257 = 751693) B751693
theorem B445203 : Blo 443779 445203 := bstep (se 1 (by rfl) ⟨333902, by rfl⟩ : syracuseStep 445203 = 667805) B667805
theorem B445219 : Blo 443779 445219 := bstep (se 1 (by rfl) ⟨333914, by rfl⟩ : syracuseStep 445219 = 667829) B667829
theorem B1002275 : Blo 443779 1002275 := bstep (se 1 (by rfl) ⟨751706, by rfl⟩ : syracuseStep 1002275 = 1503413) B1503413
theorem B445235 : Blo 443779 445235 := bstep (se 1 (by rfl) ⟨333926, by rfl⟩ : syracuseStep 445235 = 667853) B667853
theorem B445251 : Blo 443779 445251 := bstep (se 1 (by rfl) ⟨333938, by rfl⟩ : syracuseStep 445251 = 667877) B667877
theorem B445267 : Blo 443779 445267 := bstep (se 1 (by rfl) ⟨333950, by rfl⟩ : syracuseStep 445267 = 667901) B667901
theorem B445283 : Blo 443779 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B445299 : Blo 443779 445299 := bstep (se 1 (by rfl) ⟨333974, by rfl⟩ : syracuseStep 445299 = 667949) B667949
theorem B445315 : Blo 443779 445315 := bstep (se 1 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 445315 = 667973) B667973
theorem B445331 : Blo 443779 445331 := bstep (se 1 (by rfl) ⟨333998, by rfl⟩ : syracuseStep 445331 = 667997) B667997
theorem B478099 : Blo 443779 478099 := bstep (se 1 (by rfl) ⟨358574, by rfl⟩ : syracuseStep 478099 = 717149) B717149
theorem B2247587 : Blo 443779 2247587 := bstep (se 1 (by rfl) ⟨1685690, by rfl⟩ : syracuseStep 2247587 = 3371381) B3371381
theorem B445347 : Blo 443779 445347 := bstep (se 1 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 445347 = 668021) B668021
theorem B445363 : Blo 443779 445363 := bstep (se 1 (by rfl) ⟨334022, by rfl⟩ : syracuseStep 445363 = 668045) B668045
theorem B445379 : Blo 443779 445379 := bstep (se 1 (by rfl) ⟨334034, by rfl⟩ : syracuseStep 445379 = 668069) B668069
theorem B445395 : Blo 443779 445395 := bstep (se 1 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 445395 = 668093) B668093
theorem B445411 : Blo 443779 445411 := bstep (se 1 (by rfl) ⟨334058, by rfl⟩ : syracuseStep 445411 = 668117) B668117
theorem B445427 : Blo 443779 445427 := bstep (se 1 (by rfl) ⟨334070, by rfl⟩ : syracuseStep 445427 = 668141) B668141
theorem B445443 : Blo 443779 445443 := bstep (se 1 (by rfl) ⟨334082, by rfl⟩ : syracuseStep 445443 = 668165) B668165
theorem B445459 : Blo 443779 445459 := bstep (se 1 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 445459 = 668189) B668189
theorem B445475 : Blo 443779 445475 := bstep (se 1 (by rfl) ⟨334106, by rfl⟩ : syracuseStep 445475 = 668213) B668213
theorem B1002545 : Blo 443779 1002545 := bstep (se 2 (by rfl) ⟨375954, by rfl⟩ : syracuseStep 1002545 = 751909) B751909
theorem B445491 : Blo 443779 445491 := bstep (se 1 (by rfl) ⟨334118, by rfl⟩ : syracuseStep 445491 = 668237) B668237
theorem B445507 : Blo 443779 445507 := bstep (se 1 (by rfl) ⟨334130, by rfl⟩ : syracuseStep 445507 = 668261) B668261
theorem B1002563 : Blo 443779 1002563 := bstep (se 1 (by rfl) ⟨751922, by rfl⟩ : syracuseStep 1002563 = 1503845) B1503845
theorem B2542661 : Blo 443779 2542661 := bstep (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) B476749
theorem B445523 : Blo 443779 445523 := bstep (se 1 (by rfl) ⟨334142, by rfl⟩ : syracuseStep 445523 = 668285) B668285
theorem B445539 : Blo 443779 445539 := bstep (se 1 (by rfl) ⟨334154, by rfl⟩ : syracuseStep 445539 = 668309) B668309
theorem B445555 : Blo 443779 445555 := bstep (se 1 (by rfl) ⟨334166, by rfl⟩ : syracuseStep 445555 = 668333) B668333
theorem B445571 : Blo 443779 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B445587 : Blo 443779 445587 := bstep (se 1 (by rfl) ⟨334190, by rfl⟩ : syracuseStep 445587 = 668381) B668381
theorem B445603 : Blo 443779 445603 := bstep (se 1 (by rfl) ⟨334202, by rfl⟩ : syracuseStep 445603 = 668405) B668405
theorem B445619 : Blo 443779 445619 := bstep (se 1 (by rfl) ⟨334214, by rfl⟩ : syracuseStep 445619 = 668429) B668429
theorem B445635 : Blo 443779 445635 := bstep (se 1 (by rfl) ⟨334226, by rfl⟩ : syracuseStep 445635 = 668453) B668453
theorem B445651 : Blo 443779 445651 := bstep (se 1 (by rfl) ⟨334238, by rfl⟩ : syracuseStep 445651 = 668477) B668477
theorem B445667 : Blo 443779 445667 := bstep (se 1 (by rfl) ⟨334250, by rfl⟩ : syracuseStep 445667 = 668501) B668501
theorem B445683 : Blo 443779 445683 := bstep (se 1 (by rfl) ⟨334262, by rfl⟩ : syracuseStep 445683 = 668525) B668525
theorem B445699 : Blo 443779 445699 := bstep (se 1 (by rfl) ⟨334274, by rfl⟩ : syracuseStep 445699 = 668549) B668549
theorem B1428749 : Blo 443779 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B445715 : Blo 443779 445715 := bstep (se 1 (by rfl) ⟨334286, by rfl⟩ : syracuseStep 445715 = 668573) B668573
theorem B1690915 : Blo 443779 1690915 := bstep (se 1 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 1690915 = 2536373) B2536373
theorem B445731 : Blo 443779 445731 := bstep (se 1 (by rfl) ⟨334298, by rfl⟩ : syracuseStep 445731 = 668597) B668597
theorem B445747 : Blo 443779 445747 := bstep (se 1 (by rfl) ⟨334310, by rfl⟩ : syracuseStep 445747 = 668621) B668621
theorem B445763 : Blo 443779 445763 := bstep (se 1 (by rfl) ⟨334322, by rfl⟩ : syracuseStep 445763 = 668645) B668645
theorem B1002833 : Blo 443779 1002833 := bstep (se 2 (by rfl) ⟨376062, by rfl⟩ : syracuseStep 1002833 = 752125) B752125
theorem B445779 : Blo 443779 445779 := bstep (se 1 (by rfl) ⟨334334, by rfl⟩ : syracuseStep 445779 = 668669) B668669
theorem B1002851 : Blo 443779 1002851 := bstep (se 1 (by rfl) ⟨752138, by rfl⟩ : syracuseStep 1002851 = 1504277) B1504277
theorem B445795 : Blo 443779 445795 := bstep (se 1 (by rfl) ⟨334346, by rfl⟩ : syracuseStep 445795 = 668693) B668693
theorem B8539505 : Blo 443779 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B445811 : Blo 443779 445811 := bstep (se 1 (by rfl) ⟨334358, by rfl⟩ : syracuseStep 445811 = 668717) B668717
theorem B445827 : Blo 443779 445827 := bstep (se 1 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 445827 = 668741) B668741
theorem B445843 : Blo 443779 445843 := bstep (se 1 (by rfl) ⟨334382, by rfl⟩ : syracuseStep 445843 = 668765) B668765
theorem B445859 : Blo 443779 445859 := bstep (se 1 (by rfl) ⟨334394, by rfl⟩ : syracuseStep 445859 = 668789) B668789
theorem B445875 : Blo 443779 445875 := bstep (se 1 (by rfl) ⟨334406, by rfl⟩ : syracuseStep 445875 = 668813) B668813
theorem B445891 : Blo 443779 445891 := bstep (se 1 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 445891 = 668837) B668837
theorem B445907 : Blo 443779 445907 := bstep (se 1 (by rfl) ⟨334430, by rfl⟩ : syracuseStep 445907 = 668861) B668861
theorem B445923 : Blo 443779 445923 := bstep (se 1 (by rfl) ⟨334442, by rfl⟩ : syracuseStep 445923 = 668885) B668885
theorem B445939 : Blo 443779 445939 := bstep (se 1 (by rfl) ⟨334454, by rfl⟩ : syracuseStep 445939 = 668909) B668909
theorem B445955 : Blo 443779 445955 := bstep (se 1 (by rfl) ⟨334466, by rfl⟩ : syracuseStep 445955 = 668933) B668933
theorem B445971 : Blo 443779 445971 := bstep (se 1 (by rfl) ⟨334478, by rfl⟩ : syracuseStep 445971 = 668957) B668957
theorem B445987 : Blo 443779 445987 := bstep (se 1 (by rfl) ⟨334490, by rfl⟩ : syracuseStep 445987 = 668981) B668981
theorem B446003 : Blo 443779 446003 := bstep (se 1 (by rfl) ⟨334502, by rfl⟩ : syracuseStep 446003 = 669005) B669005
theorem B5164597 : Blo 443779 5164597 := bstep (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) B484181
theorem B446019 : Blo 443779 446019 := bstep (se 1 (by rfl) ⟨334514, by rfl⟩ : syracuseStep 446019 = 669029) B669029
theorem B740945 : Blo 443779 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B446035 : Blo 443779 446035 := bstep (se 1 (by rfl) ⟨334526, by rfl⟩ : syracuseStep 446035 = 669053) B669053
theorem B544339 : Blo 443779 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B446051 : Blo 443779 446051 := bstep (se 1 (by rfl) ⟨334538, by rfl⟩ : syracuseStep 446051 = 669077) B669077
theorem B1003121 : Blo 443779 1003121 := bstep (se 2 (by rfl) ⟨376170, by rfl⟩ : syracuseStep 1003121 = 752341) B752341
theorem B446067 : Blo 443779 446067 := bstep (se 1 (by rfl) ⟨334550, by rfl⟩ : syracuseStep 446067 = 669101) B669101
theorem B1003139 : Blo 443779 1003139 := bstep (se 1 (by rfl) ⟨752354, by rfl⟩ : syracuseStep 1003139 = 1504709) B1504709
theorem B446083 : Blo 443779 446083 := bstep (se 1 (by rfl) ⟨334562, by rfl⟩ : syracuseStep 446083 = 669125) B669125
theorem B446099 : Blo 443779 446099 := bstep (se 1 (by rfl) ⟨334574, by rfl⟩ : syracuseStep 446099 = 669149) B669149
theorem B446115 : Blo 443779 446115 := bstep (se 1 (by rfl) ⟨334586, by rfl⟩ : syracuseStep 446115 = 669173) B669173
theorem B446131 : Blo 443779 446131 := bstep (se 1 (by rfl) ⟨334598, by rfl⟩ : syracuseStep 446131 = 669197) B669197
theorem B446147 : Blo 443779 446147 := bstep (se 1 (by rfl) ⟨334610, by rfl⟩ : syracuseStep 446147 = 669221) B669221
theorem B2248397 : Blo 443779 2248397 := bstep (se 3 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 2248397 = 843149) B843149
theorem B446163 : Blo 443779 446163 := bstep (se 1 (by rfl) ⟨334622, by rfl⟩ : syracuseStep 446163 = 669245) B669245
theorem B446179 : Blo 443779 446179 := bstep (se 1 (by rfl) ⟨334634, by rfl⟩ : syracuseStep 446179 = 669269) B669269
theorem B2543345 : Blo 443779 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B446195 : Blo 443779 446195 := bstep (se 1 (by rfl) ⟨334646, by rfl⟩ : syracuseStep 446195 = 669293) B669293
theorem B675587 : Blo 443779 675587 := bstep (se 1 (by rfl) ⟨506690, by rfl⟩ : syracuseStep 675587 = 1013381) B1013381
theorem B1068803 : Blo 443779 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B446211 : Blo 443779 446211 := bstep (se 1 (by rfl) ⟨334658, by rfl⟩ : syracuseStep 446211 = 669317) B669317
theorem B446227 : Blo 443779 446227 := bstep (se 1 (by rfl) ⟨334670, by rfl⟩ : syracuseStep 446227 = 669341) B669341
theorem B12865301 : Blo 443779 12865301 := bstep (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) B603061
theorem B446243 : Blo 443779 446243 := bstep (se 1 (by rfl) ⟨334682, by rfl⟩ : syracuseStep 446243 = 669365) B669365
theorem B1265453 : Blo 443779 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B446259 : Blo 443779 446259 := bstep (se 1 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 446259 = 669389) B669389
theorem B5066549 : Blo 443779 5066549 := bstep (se 5 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 5066549 = 474989) B474989
theorem B446275 : Blo 443779 446275 := bstep (se 1 (by rfl) ⟨334706, by rfl⟩ : syracuseStep 446275 = 669413) B669413
theorem B446291 : Blo 443779 446291 := bstep (se 1 (by rfl) ⟨334718, by rfl⟩ : syracuseStep 446291 = 669437) B669437
theorem B446307 : Blo 443779 446307 := bstep (se 1 (by rfl) ⟨334730, by rfl⟩ : syracuseStep 446307 = 669461) B669461
theorem B446323 : Blo 443779 446323 := bstep (se 1 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 446323 = 669485) B669485
theorem B446339 : Blo 443779 446339 := bstep (se 1 (by rfl) ⟨334754, by rfl⟩ : syracuseStep 446339 = 669509) B669509
theorem B1003409 : Blo 443779 1003409 := bstep (se 2 (by rfl) ⟨376278, by rfl⟩ : syracuseStep 1003409 = 752557) B752557
theorem B446355 : Blo 443779 446355 := bstep (se 1 (by rfl) ⟨334766, by rfl⟩ : syracuseStep 446355 = 669533) B669533
theorem B1003427 : Blo 443779 1003427 := bstep (se 1 (by rfl) ⟨752570, by rfl⟩ : syracuseStep 1003427 = 1505141) B1505141
theorem B446371 : Blo 443779 446371 := bstep (se 1 (by rfl) ⟨334778, by rfl⟩ : syracuseStep 446371 = 669557) B669557
theorem B1068977 : Blo 443779 1068977 := bstep (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) B801733
theorem B446387 : Blo 443779 446387 := bstep (se 1 (by rfl) ⟨334790, by rfl⟩ : syracuseStep 446387 = 669581) B669581
theorem B1068995 : Blo 443779 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B446403 : Blo 443779 446403 := bstep (se 1 (by rfl) ⟨334802, by rfl⟩ : syracuseStep 446403 = 669605) B669605
theorem B1527761 : Blo 443779 1527761 := bstep (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) B1145821
theorem B446419 : Blo 443779 446419 := bstep (se 1 (by rfl) ⟨334814, by rfl⟩ : syracuseStep 446419 = 669629) B669629
theorem B1265635 : Blo 443779 1265635 := bstep (se 1 (by rfl) ⟨949226, by rfl⟩ : syracuseStep 1265635 = 1898453) B1898453
theorem B446435 : Blo 443779 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B446451 : Blo 443779 446451 := bstep (se 1 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 446451 = 669677) B669677
theorem B446467 : Blo 443779 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B1265681 : Blo 443779 1265681 := bstep (se 2 (by rfl) ⟨474630, by rfl⟩ : syracuseStep 1265681 = 949261) B949261
theorem B446483 : Blo 443779 446483 := bstep (se 1 (by rfl) ⟨334862, by rfl⟩ : syracuseStep 446483 = 669725) B669725
theorem B446499 : Blo 443779 446499 := bstep (se 1 (by rfl) ⟨334874, by rfl⟩ : syracuseStep 446499 = 669749) B669749
theorem B446515 : Blo 443779 446515 := bstep (se 1 (by rfl) ⟨334886, by rfl⟩ : syracuseStep 446515 = 669773) B669773
theorem B446531 : Blo 443779 446531 := bstep (se 1 (by rfl) ⟨334898, by rfl⟩ : syracuseStep 446531 = 669797) B669797
theorem B446547 : Blo 443779 446547 := bstep (se 1 (by rfl) ⟨334910, by rfl⟩ : syracuseStep 446547 = 669821) B669821
theorem B446563 : Blo 443779 446563 := bstep (se 1 (by rfl) ⟨334922, by rfl⟩ : syracuseStep 446563 = 669845) B669845
theorem B446579 : Blo 443779 446579 := bstep (se 1 (by rfl) ⟨334934, by rfl⟩ : syracuseStep 446579 = 669869) B669869
theorem B446595 : Blo 443779 446595 := bstep (se 1 (by rfl) ⟨334946, by rfl⟩ : syracuseStep 446595 = 669893) B669893
theorem B446611 : Blo 443779 446611 := bstep (se 1 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 446611 = 669917) B669917
theorem B446627 : Blo 443779 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B1003697 : Blo 443779 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B446643 : Blo 443779 446643 := bstep (se 1 (by rfl) ⟨334982, by rfl⟩ : syracuseStep 446643 = 669965) B669965
theorem B1003715 : Blo 443779 1003715 := bstep (se 1 (by rfl) ⟨752786, by rfl⟩ : syracuseStep 1003715 = 1505573) B1505573
theorem B446659 : Blo 443779 446659 := bstep (se 1 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 446659 = 669989) B669989
theorem B446675 : Blo 443779 446675 := bstep (se 1 (by rfl) ⟨335006, by rfl⟩ : syracuseStep 446675 = 670013) B670013
theorem B446691 : Blo 443779 446691 := bstep (se 1 (by rfl) ⟨335018, by rfl⟩ : syracuseStep 446691 = 670037) B670037
theorem B446707 : Blo 443779 446707 := bstep (se 1 (by rfl) ⟨335030, by rfl⟩ : syracuseStep 446707 = 670061) B670061
theorem B446723 : Blo 443779 446723 := bstep (se 1 (by rfl) ⟨335042, by rfl⟩ : syracuseStep 446723 = 670085) B670085
theorem B446739 : Blo 443779 446739 := bstep (se 1 (by rfl) ⟨335054, by rfl⟩ : syracuseStep 446739 = 670109) B670109
theorem B446755 : Blo 443779 446755 := bstep (se 1 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 446755 = 670133) B670133
theorem B446771 : Blo 443779 446771 := bstep (se 1 (by rfl) ⟨335078, by rfl⟩ : syracuseStep 446771 = 670157) B670157
theorem B446787 : Blo 443779 446787 := bstep (se 1 (by rfl) ⟨335090, by rfl⟩ : syracuseStep 446787 = 670181) B670181
theorem B446803 : Blo 443779 446803 := bstep (se 1 (by rfl) ⟨335102, by rfl⟩ : syracuseStep 446803 = 670205) B670205
theorem B446819 : Blo 443779 446819 := bstep (se 1 (by rfl) ⟨335114, by rfl⟩ : syracuseStep 446819 = 670229) B670229
theorem B446835 : Blo 443779 446835 := bstep (se 1 (by rfl) ⟨335126, by rfl⟩ : syracuseStep 446835 = 670253) B670253
theorem B446851 : Blo 443779 446851 := bstep (se 1 (by rfl) ⟨335138, by rfl⟩ : syracuseStep 446851 = 670277) B670277
theorem B446867 : Blo 443779 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B446883 : Blo 443779 446883 := bstep (se 1 (by rfl) ⟨335162, by rfl⟩ : syracuseStep 446883 = 670325) B670325
theorem B446899 : Blo 443779 446899 := bstep (se 1 (by rfl) ⟨335174, by rfl⟩ : syracuseStep 446899 = 670349) B670349
theorem B446915 : Blo 443779 446915 := bstep (se 1 (by rfl) ⟨335186, by rfl⟩ : syracuseStep 446915 = 670373) B670373
theorem B1003985 : Blo 443779 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B446931 : Blo 443779 446931 := bstep (se 1 (by rfl) ⟨335198, by rfl⟩ : syracuseStep 446931 = 670397) B670397
theorem B1004003 : Blo 443779 1004003 := bstep (se 1 (by rfl) ⟨753002, by rfl⟩ : syracuseStep 1004003 = 1506005) B1506005
theorem B446947 : Blo 443779 446947 := bstep (se 1 (by rfl) ⟨335210, by rfl⟩ : syracuseStep 446947 = 670421) B670421
theorem B446963 : Blo 443779 446963 := bstep (se 1 (by rfl) ⟨335222, by rfl⟩ : syracuseStep 446963 = 670445) B670445
theorem B446979 : Blo 443779 446979 := bstep (se 1 (by rfl) ⟨335234, by rfl⟩ : syracuseStep 446979 = 670469) B670469
theorem B446995 : Blo 443779 446995 := bstep (se 1 (by rfl) ⟨335246, by rfl⟩ : syracuseStep 446995 = 670493) B670493
theorem B447011 : Blo 443779 447011 := bstep (se 1 (by rfl) ⟨335258, by rfl⟩ : syracuseStep 447011 = 670517) B670517
theorem B447027 : Blo 443779 447027 := bstep (se 1 (by rfl) ⟨335270, by rfl⟩ : syracuseStep 447027 = 670541) B670541
theorem B447043 : Blo 443779 447043 := bstep (se 1 (by rfl) ⟨335282, by rfl⟩ : syracuseStep 447043 = 670565) B670565
theorem B1430093 : Blo 443779 1430093 := bstep (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) B536285
theorem B447059 : Blo 443779 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B447075 : Blo 443779 447075 := bstep (se 1 (by rfl) ⟨335306, by rfl⟩ : syracuseStep 447075 = 670613) B670613
theorem B447091 : Blo 443779 447091 := bstep (se 1 (by rfl) ⟨335318, by rfl⟩ : syracuseStep 447091 = 670637) B670637
theorem B447107 : Blo 443779 447107 := bstep (se 1 (by rfl) ⟨335330, by rfl⟩ : syracuseStep 447107 = 670661) B670661
theorem B8245901 : Blo 443779 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B447123 : Blo 443779 447123 := bstep (se 1 (by rfl) ⟨335342, by rfl⟩ : syracuseStep 447123 = 670685) B670685
theorem B447139 : Blo 443779 447139 := bstep (se 1 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 447139 = 670709) B670709
theorem B447155 : Blo 443779 447155 := bstep (se 1 (by rfl) ⟨335366, by rfl⟩ : syracuseStep 447155 = 670733) B670733
theorem B447171 : Blo 443779 447171 := bstep (se 1 (by rfl) ⟨335378, by rfl⟩ : syracuseStep 447171 = 670757) B670757
theorem B447187 : Blo 443779 447187 := bstep (se 1 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 447187 = 670781) B670781
theorem B447203 : Blo 443779 447203 := bstep (se 1 (by rfl) ⟨335402, by rfl⟩ : syracuseStep 447203 = 670805) B670805
theorem B1004273 : Blo 443779 1004273 := bstep (se 2 (by rfl) ⟨376602, by rfl⟩ : syracuseStep 1004273 = 753205) B753205
theorem B447219 : Blo 443779 447219 := bstep (se 1 (by rfl) ⟨335414, by rfl⟩ : syracuseStep 447219 = 670829) B670829
theorem B1004291 : Blo 443779 1004291 := bstep (se 1 (by rfl) ⟨753218, by rfl⟩ : syracuseStep 1004291 = 1506437) B1506437
theorem B447235 : Blo 443779 447235 := bstep (se 1 (by rfl) ⟨335426, by rfl⟩ : syracuseStep 447235 = 670853) B670853
theorem B447251 : Blo 443779 447251 := bstep (se 1 (by rfl) ⟨335438, by rfl⟩ : syracuseStep 447251 = 670877) B670877
theorem B447267 : Blo 443779 447267 := bstep (se 1 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 447267 = 670901) B670901
theorem B447283 : Blo 443779 447283 := bstep (se 1 (by rfl) ⟨335462, by rfl⟩ : syracuseStep 447283 = 670925) B670925
theorem B447299 : Blo 443779 447299 := bstep (se 1 (by rfl) ⟨335474, by rfl⟩ : syracuseStep 447299 = 670949) B670949
theorem B447315 : Blo 443779 447315 := bstep (se 1 (by rfl) ⟨335486, by rfl⟩ : syracuseStep 447315 = 670973) B670973
theorem B447331 : Blo 443779 447331 := bstep (se 1 (by rfl) ⟨335498, by rfl⟩ : syracuseStep 447331 = 670997) B670997
theorem B447347 : Blo 443779 447347 := bstep (se 1 (by rfl) ⟨335510, by rfl⟩ : syracuseStep 447347 = 671021) B671021
theorem B447363 : Blo 443779 447363 := bstep (se 1 (by rfl) ⟨335522, by rfl⟩ : syracuseStep 447363 = 671045) B671045
theorem B447379 : Blo 443779 447379 := bstep (se 1 (by rfl) ⟨335534, by rfl⟩ : syracuseStep 447379 = 671069) B671069
theorem B447395 : Blo 443779 447395 := bstep (se 1 (by rfl) ⟨335546, by rfl⟩ : syracuseStep 447395 = 671093) B671093
theorem B447411 : Blo 443779 447411 := bstep (se 1 (by rfl) ⟨335558, by rfl⟩ : syracuseStep 447411 = 671117) B671117
theorem B447427 : Blo 443779 447427 := bstep (se 1 (by rfl) ⟨335570, by rfl⟩ : syracuseStep 447427 = 671141) B671141
theorem B447443 : Blo 443779 447443 := bstep (se 1 (by rfl) ⟨335582, by rfl⟩ : syracuseStep 447443 = 671165) B671165
theorem B447459 : Blo 443779 447459 := bstep (se 1 (by rfl) ⟨335594, by rfl⟩ : syracuseStep 447459 = 671189) B671189
theorem B447475 : Blo 443779 447475 := bstep (se 1 (by rfl) ⟨335606, by rfl⟩ : syracuseStep 447475 = 671213) B671213
theorem B1430531 : Blo 443779 1430531 := bstep (se 1 (by rfl) ⟨1072898, by rfl⟩ : syracuseStep 1430531 = 2145797) B2145797
theorem B447491 : Blo 443779 447491 := bstep (se 1 (by rfl) ⟨335618, by rfl⟩ : syracuseStep 447491 = 671237) B671237
theorem B1004561 : Blo 443779 1004561 := bstep (se 2 (by rfl) ⟨376710, by rfl⟩ : syracuseStep 1004561 = 753421) B753421
theorem B676883 : Blo 443779 676883 := bstep (se 1 (by rfl) ⟨507662, by rfl⟩ : syracuseStep 676883 = 1015325) B1015325
theorem B447507 : Blo 443779 447507 := bstep (se 1 (by rfl) ⟨335630, by rfl⟩ : syracuseStep 447507 = 671261) B671261
theorem B1004579 : Blo 443779 1004579 := bstep (se 1 (by rfl) ⟨753434, by rfl⟩ : syracuseStep 1004579 = 1506869) B1506869
theorem B447523 : Blo 443779 447523 := bstep (se 1 (by rfl) ⟨335642, by rfl⟩ : syracuseStep 447523 = 671285) B671285
theorem B447539 : Blo 443779 447539 := bstep (se 1 (by rfl) ⟨335654, by rfl⟩ : syracuseStep 447539 = 671309) B671309
theorem B447555 : Blo 443779 447555 := bstep (se 1 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 447555 = 671333) B671333
theorem B447571 : Blo 443779 447571 := bstep (se 1 (by rfl) ⟨335678, by rfl⟩ : syracuseStep 447571 = 671357) B671357
theorem B447587 : Blo 443779 447587 := bstep (se 1 (by rfl) ⟨335690, by rfl⟩ : syracuseStep 447587 = 671381) B671381
theorem B447603 : Blo 443779 447603 := bstep (se 1 (by rfl) ⟨335702, by rfl⟩ : syracuseStep 447603 = 671405) B671405
theorem B447619 : Blo 443779 447619 := bstep (se 1 (by rfl) ⟨335714, by rfl⟩ : syracuseStep 447619 = 671429) B671429
theorem B447635 : Blo 443779 447635 := bstep (se 1 (by rfl) ⟨335726, by rfl⟩ : syracuseStep 447635 = 671453) B671453
theorem B2544803 : Blo 443779 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B447651 : Blo 443779 447651 := bstep (se 1 (by rfl) ⟨335738, by rfl⟩ : syracuseStep 447651 = 671477) B671477
theorem B447667 : Blo 443779 447667 := bstep (se 1 (by rfl) ⟨335750, by rfl⟩ : syracuseStep 447667 = 671501) B671501
theorem B447683 : Blo 443779 447683 := bstep (se 1 (by rfl) ⟨335762, by rfl⟩ : syracuseStep 447683 = 671525) B671525
theorem B447699 : Blo 443779 447699 := bstep (se 1 (by rfl) ⟨335774, by rfl⟩ : syracuseStep 447699 = 671549) B671549
theorem B447715 : Blo 443779 447715 := bstep (se 1 (by rfl) ⟨335786, by rfl⟩ : syracuseStep 447715 = 671573) B671573
theorem B447731 : Blo 443779 447731 := bstep (se 1 (by rfl) ⟨335798, by rfl⟩ : syracuseStep 447731 = 671597) B671597
theorem B447747 : Blo 443779 447747 := bstep (se 1 (by rfl) ⟨335810, by rfl⟩ : syracuseStep 447747 = 671621) B671621
theorem B447763 : Blo 443779 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B447779 : Blo 443779 447779 := bstep (se 1 (by rfl) ⟨335834, by rfl⟩ : syracuseStep 447779 = 671669) B671669
theorem B1004849 : Blo 443779 1004849 := bstep (se 2 (by rfl) ⟨376818, by rfl⟩ : syracuseStep 1004849 = 753637) B753637
theorem B1004867 : Blo 443779 1004867 := bstep (se 1 (by rfl) ⟨753650, by rfl⟩ : syracuseStep 1004867 = 1507301) B1507301
theorem B15422861 : Blo 443779 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B1267139 : Blo 443779 1267139 := bstep (se 1 (by rfl) ⟨950354, by rfl⟩ : syracuseStep 1267139 = 1900709) B1900709
theorem B1693133 : Blo 443779 1693133 := bstep (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) B634925
theorem B644593 : Blo 443779 644593 := bstep (se 2 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 644593 = 483445) B483445
theorem B1005137 : Blo 443779 1005137 := bstep (se 2 (by rfl) ⟨376926, by rfl⟩ : syracuseStep 1005137 = 753853) B753853
theorem B1005155 : Blo 443779 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B907057 : Blo 443779 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B1005425 : Blo 443779 1005425 := bstep (se 2 (by rfl) ⟨377034, by rfl⟩ : syracuseStep 1005425 = 754069) B754069
theorem B1005443 : Blo 443779 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B481411 : Blo 443779 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B1005713 : Blo 443779 1005713 := bstep (se 2 (by rfl) ⟨377142, by rfl⟩ : syracuseStep 1005713 = 754285) B754285
theorem B1005731 : Blo 443779 1005731 := bstep (se 1 (by rfl) ⟨754298, by rfl⟩ : syracuseStep 1005731 = 1508597) B1508597
theorem B3201221 : Blo 443779 3201221 := bstep (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) B600229
theorem B711011 : Blo 443779 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B1006001 : Blo 443779 1006001 := bstep (se 2 (by rfl) ⟨377250, by rfl⟩ : syracuseStep 1006001 = 754501) B754501
theorem B1006019 : Blo 443779 1006019 := bstep (se 1 (by rfl) ⟨754514, by rfl⟩ : syracuseStep 1006019 = 1509029) B1509029
theorem B2251313 : Blo 443779 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B711299 : Blo 443779 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B1268369 : Blo 443779 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B1006289 : Blo 443779 1006289 := bstep (se 2 (by rfl) ⟨377358, by rfl⟩ : syracuseStep 1006289 = 754717) B754717
theorem B1006307 : Blo 443779 1006307 := bstep (se 1 (by rfl) ⟨754730, by rfl⟩ : syracuseStep 1006307 = 1509461) B1509461
theorem B1497905 : Blo 443779 1497905 := bstep (se 2 (by rfl) ⟨561714, by rfl⟩ : syracuseStep 1497905 = 1123429) B1123429
theorem B613171 : Blo 443779 613171 := bstep (se 1 (by rfl) ⟨459878, by rfl⟩ : syracuseStep 613171 = 919757) B919757
theorem B1432451 : Blo 443779 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B3398597 : Blo 443779 3398597 := bstep (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) B637237
theorem B678883 : Blo 443779 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B1006577 : Blo 443779 1006577 := bstep (se 2 (by rfl) ⟨377466, by rfl⟩ : syracuseStep 1006577 = 754933) B754933
theorem B1006595 : Blo 443779 1006595 := bstep (se 1 (by rfl) ⟨754946, by rfl⟩ : syracuseStep 1006595 = 1509893) B1509893
theorem B711715 : Blo 443779 711715 := bstep (se 1 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 711715 = 1067573) B1067573
theorem B1006865 : Blo 443779 1006865 := bstep (se 2 (by rfl) ⟨377574, by rfl⟩ : syracuseStep 1006865 = 755149) B755149
theorem B843043 : Blo 443779 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B1006883 : Blo 443779 1006883 := bstep (se 1 (by rfl) ⟨755162, by rfl⟩ : syracuseStep 1006883 = 1510325) B1510325
theorem B711985 : Blo 443779 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B1498445 : Blo 443779 1498445 := bstep (se 3 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 1498445 = 561917) B561917
theorem B1498499 : Blo 443779 1498499 := bstep (se 1 (by rfl) ⟨1123874, by rfl⟩ : syracuseStep 1498499 = 2247749) B2247749
theorem B843203 : Blo 443779 843203 := bstep (se 1 (by rfl) ⟨632402, by rfl⟩ : syracuseStep 843203 = 1264805) B1264805
theorem B712241 : Blo 443779 712241 := bstep (se 2 (by rfl) ⟨267090, by rfl⟩ : syracuseStep 712241 = 534181) B534181
theorem B1007153 : Blo 443779 1007153 := bstep (se 2 (by rfl) ⟨377682, by rfl⟩ : syracuseStep 1007153 = 755365) B755365
theorem B1007171 : Blo 443779 1007171 := bstep (se 1 (by rfl) ⟨755378, by rfl⟩ : syracuseStep 1007171 = 1510757) B1510757
theorem B1498769 : Blo 443779 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B2973509 : Blo 443779 2973509 := bstep (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) B557533
theorem B1007441 : Blo 443779 1007441 := bstep (se 2 (by rfl) ⟨377790, by rfl⟩ : syracuseStep 1007441 = 755581) B755581
theorem B1007459 : Blo 443779 1007459 := bstep (se 1 (by rfl) ⟨755594, by rfl⟩ : syracuseStep 1007459 = 1511189) B1511189
theorem B2252771 : Blo 443779 2252771 := bstep (se 1 (by rfl) ⟨1689578, by rfl⟩ : syracuseStep 2252771 = 3379157) B3379157
theorem B1269827 : Blo 443779 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B4284515 : Blo 443779 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B680051 : Blo 443779 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B1499309 : Blo 443779 1499309 := bstep (se 3 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 1499309 = 562241) B562241
theorem B1499363 : Blo 443779 1499363 := bstep (se 1 (by rfl) ⟨1124522, by rfl⟩ : syracuseStep 1499363 = 2249045) B2249045
theorem B712945 : Blo 443779 712945 := bstep (se 2 (by rfl) ⟨267354, by rfl⟩ : syracuseStep 712945 = 534709) B534709
theorem B1696049 : Blo 443779 1696049 := bstep (se 2 (by rfl) ⟨636018, by rfl⟩ : syracuseStep 1696049 = 1272037) B1272037
theorem B6447413 : Blo 443779 6447413 := bstep (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) B604445
theorem B2548037 : Blo 443779 2548037 := bstep (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) B477757
theorem B811363 : Blo 443779 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B975235 : Blo 443779 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B1499633 : Blo 443779 1499633 := bstep (se 2 (by rfl) ⟨562362, by rfl⟩ : syracuseStep 1499633 = 1124725) B1124725
theorem B844273 : Blo 443779 844273 := bstep (se 2 (by rfl) ⟨316602, by rfl⟩ : syracuseStep 844273 = 633205) B633205
theorem B2253581 : Blo 443779 2253581 := bstep (se 3 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 2253581 = 845093) B845093
theorem B2548493 : Blo 443779 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B680755 : Blo 443779 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B1270637 : Blo 443779 1270637 := bstep (se 3 (by rfl) ⟨238244, by rfl⟩ : syracuseStep 1270637 = 476489) B476489
theorem B1500173 : Blo 443779 1500173 := bstep (se 3 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 1500173 = 562565) B562565
theorem B1270829 : Blo 443779 1270829 := bstep (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) B476561
theorem B1500227 : Blo 443779 1500227 := bstep (se 1 (by rfl) ⟨1125170, by rfl⟩ : syracuseStep 1500227 = 2250341) B2250341
theorem B713843 : Blo 443779 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B714035 : Blo 443779 714035 := bstep (se 1 (by rfl) ⟨535526, by rfl⟩ : syracuseStep 714035 = 1071053) B1071053
theorem B1500497 : Blo 443779 1500497 := bstep (se 2 (by rfl) ⟨562686, by rfl⟩ : syracuseStep 1500497 = 1125373) B1125373
theorem B11429261 : Blo 443779 11429261 := bstep (se 3 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 11429261 = 4285973) B4285973
theorem B845329 : Blo 443779 845329 := bstep (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) B633997
theorem B1697507 : Blo 443779 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1501037 : Blo 443779 1501037 := bstep (se 3 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 1501037 = 562889) B562889
theorem B1501091 : Blo 443779 1501091 := bstep (se 1 (by rfl) ⟨1125818, by rfl⟩ : syracuseStep 1501091 = 2251637) B2251637
theorem B845731 : Blo 443779 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B1206211 : Blo 443779 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B845777 : Blo 443779 845777 := bstep (se 2 (by rfl) ⟨317166, by rfl⟩ : syracuseStep 845777 = 634333) B634333
theorem B1271821 : Blo 443779 1271821 := bstep (se 3 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 1271821 = 476933) B476933
theorem B649315 : Blo 443779 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B1501361 : Blo 443779 1501361 := bstep (se 2 (by rfl) ⟨563010, by rfl⟩ : syracuseStep 1501361 = 1126021) B1126021
theorem B846065 : Blo 443779 846065 := bstep (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) B634549
theorem B715009 : Blo 443779 715009 := bstep (se 2 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 715009 = 536257) B536257
theorem B7301573 : Blo 443779 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B2845219 : Blo 443779 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B715457 : Blo 443779 715457 := bstep (se 2 (by rfl) ⟨268296, by rfl⟩ : syracuseStep 715457 = 536593) B536593
theorem B1501901 : Blo 443779 1501901 := bstep (se 3 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 1501901 = 563213) B563213
theorem B1698509 : Blo 443779 1698509 := bstep (se 3 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 1698509 = 636941) B636941
theorem B1501955 : Blo 443779 1501955 := bstep (se 1 (by rfl) ⟨1126466, by rfl⟩ : syracuseStep 1501955 = 2252933) B2252933
theorem B846787 : Blo 443779 846787 := bstep (se 1 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 846787 = 1270181) B1270181
theorem B1502225 : Blo 443779 1502225 := bstep (se 2 (by rfl) ⟨563334, by rfl⟩ : syracuseStep 1502225 = 1126669) B1126669
theorem B5729393 : Blo 443779 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B847235 : Blo 443779 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B748993 : Blo 443779 748993 := bstep (se 2 (by rfl) ⟨280872, by rfl⟩ : syracuseStep 748993 = 561745) B561745
theorem B749027 : Blo 443779 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B1502765 : Blo 443779 1502765 := bstep (se 3 (by rfl) ⟨281768, by rfl⟩ : syracuseStep 1502765 = 563537) B563537
theorem B749155 : Blo 443779 749155 := bstep (se 1 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 749155 = 1123733) B1123733
theorem B1502819 : Blo 443779 1502819 := bstep (se 1 (by rfl) ⟨1127114, by rfl⟩ : syracuseStep 1502819 = 2254229) B2254229
theorem B2256497 : Blo 443779 2256497 := bstep (se 2 (by rfl) ⟨846186, by rfl⟩ : syracuseStep 2256497 = 1692373) B1692373
theorem B847523 : Blo 443779 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1961635 : Blo 443779 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B1273553 : Blo 443779 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B749297 : Blo 443779 749297 := bstep (se 2 (by rfl) ⟨280986, by rfl⟩ : syracuseStep 749297 = 561973) B561973
theorem B2420549 : Blo 443779 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B749425 : Blo 443779 749425 := bstep (se 2 (by rfl) ⟨281034, by rfl⟩ : syracuseStep 749425 = 562069) B562069
theorem B1503089 : Blo 443779 1503089 := bstep (se 2 (by rfl) ⟨563658, by rfl⟩ : syracuseStep 1503089 = 1127317) B1127317
theorem B749459 : Blo 443779 749459 := bstep (se 1 (by rfl) ⟨562094, by rfl⟩ : syracuseStep 749459 = 1124189) B1124189
theorem B1273745 : Blo 443779 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B749587 : Blo 443779 749587 := bstep (se 1 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 749587 = 1124381) B1124381
theorem B978979 : Blo 443779 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B716867 : Blo 443779 716867 := bstep (se 1 (by rfl) ⟨537650, by rfl⟩ : syracuseStep 716867 = 1075301) B1075301
theorem B749729 : Blo 443779 749729 := bstep (se 2 (by rfl) ⟨281148, by rfl⟩ : syracuseStep 749729 = 562297) B562297
theorem B717059 : Blo 443779 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B749857 : Blo 443779 749857 := bstep (se 2 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 749857 = 562393) B562393
theorem B749891 : Blo 443779 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B1503629 : Blo 443779 1503629 := bstep (se 3 (by rfl) ⟨281930, by rfl⟩ : syracuseStep 1503629 = 563861) B563861
theorem B750019 : Blo 443779 750019 := bstep (se 1 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 750019 = 1125029) B1125029
theorem B1503683 : Blo 443779 1503683 := bstep (se 1 (by rfl) ⟨1127762, by rfl⟩ : syracuseStep 1503683 = 2255525) B2255525
theorem B750161 : Blo 443779 750161 := bstep (se 2 (by rfl) ⟨281310, by rfl⟩ : syracuseStep 750161 = 562621) B562621
theorem B848465 : Blo 443779 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B2716357 : Blo 443779 2716357 := bstep (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) B509317
theorem B750289 : Blo 443779 750289 := bstep (se 2 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 750289 = 562717) B562717
theorem B1503953 : Blo 443779 1503953 := bstep (se 2 (by rfl) ⟨563982, by rfl⟩ : syracuseStep 1503953 = 1127965) B1127965
theorem B750323 : Blo 443779 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B1274737 : Blo 443779 1274737 := bstep (se 2 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 1274737 = 956053) B956053
theorem B750451 : Blo 443779 750451 := bstep (se 1 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 750451 = 1125677) B1125677
theorem B750593 : Blo 443779 750593 := bstep (se 2 (by rfl) ⟨281472, by rfl⟩ : syracuseStep 750593 = 562945) B562945
theorem B2257955 : Blo 443779 2257955 := bstep (se 1 (by rfl) ⟨1693466, by rfl⟩ : syracuseStep 2257955 = 3386933) B3386933
theorem B5731397 : Blo 443779 5731397 := bstep (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) B1074637
theorem B750721 : Blo 443779 750721 := bstep (se 2 (by rfl) ⟨281520, by rfl⟩ : syracuseStep 750721 = 563041) B563041
theorem B1275011 : Blo 443779 1275011 := bstep (se 1 (by rfl) ⟨956258, by rfl⟩ : syracuseStep 1275011 = 1912517) B1912517
theorem B750755 : Blo 443779 750755 := bstep (se 1 (by rfl) ⟨563066, by rfl⟩ : syracuseStep 750755 = 1126133) B1126133
theorem B1504493 : Blo 443779 1504493 := bstep (se 3 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 1504493 = 564185) B564185
theorem B750883 : Blo 443779 750883 := bstep (se 1 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 750883 = 1126325) B1126325
theorem B1504547 : Blo 443779 1504547 := bstep (se 1 (by rfl) ⟨1128410, by rfl⟩ : syracuseStep 1504547 = 2256821) B2256821
theorem B4060529 : Blo 443779 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B751025 : Blo 443779 751025 := bstep (se 2 (by rfl) ⟨281634, by rfl⟩ : syracuseStep 751025 = 563269) B563269
theorem B849361 : Blo 443779 849361 := bstep (se 2 (by rfl) ⟨318510, by rfl⟩ : syracuseStep 849361 = 637021) B637021
theorem B1799651 : Blo 443779 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B751153 : Blo 443779 751153 := bstep (se 2 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 751153 = 563365) B563365
theorem B1504817 : Blo 443779 1504817 := bstep (se 2 (by rfl) ⟨564306, by rfl⟩ : syracuseStep 1504817 = 1128613) B1128613
theorem B751187 : Blo 443779 751187 := bstep (se 1 (by rfl) ⟨563390, by rfl⟩ : syracuseStep 751187 = 1126781) B1126781
theorem B1799779 : Blo 443779 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B849521 : Blo 443779 849521 := bstep (se 2 (by rfl) ⟨318570, by rfl⟩ : syracuseStep 849521 = 637141) B637141
theorem B751315 : Blo 443779 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B2258765 : Blo 443779 2258765 := bstep (se 3 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 2258765 = 847037) B847037
theorem B751457 : Blo 443779 751457 := bstep (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) B563593
theorem B1210211 : Blo 443779 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B751585 : Blo 443779 751585 := bstep (se 2 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 751585 = 563689) B563689
theorem B686051 : Blo 443779 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B751619 : Blo 443779 751619 := bstep (se 1 (by rfl) ⟨563714, by rfl⟩ : syracuseStep 751619 = 1127429) B1127429
theorem B849923 : Blo 443779 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B1505357 : Blo 443779 1505357 := bstep (se 3 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 1505357 = 564509) B564509
theorem B751747 : Blo 443779 751747 := bstep (se 1 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 751747 = 1127621) B1127621
theorem B1505411 : Blo 443779 1505411 := bstep (se 1 (by rfl) ⟨1129058, by rfl⟩ : syracuseStep 1505411 = 2258117) B2258117
theorem B3373325 : Blo 443779 3373325 := bstep (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) B1264997
theorem B751889 : Blo 443779 751889 := bstep (se 2 (by rfl) ⟨281958, by rfl⟩ : syracuseStep 751889 = 563917) B563917
theorem B2849093 : Blo 443779 2849093 := bstep (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) B534205
theorem B752017 : Blo 443779 752017 := bstep (se 2 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 752017 = 564013) B564013
theorem B1505681 : Blo 443779 1505681 := bstep (se 2 (by rfl) ⟨564630, by rfl⟩ : syracuseStep 1505681 = 1129261) B1129261
theorem B752051 : Blo 443779 752051 := bstep (se 1 (by rfl) ⟨564038, by rfl⟩ : syracuseStep 752051 = 1128077) B1128077
theorem B2062883 : Blo 443779 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B752179 : Blo 443779 752179 := bstep (se 1 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 752179 = 1128269) B1128269
theorem B752321 : Blo 443779 752321 := bstep (se 2 (by rfl) ⟨282120, by rfl⟩ : syracuseStep 752321 = 564241) B564241
theorem B1604387 : Blo 443779 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B752449 : Blo 443779 752449 := bstep (se 2 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 752449 = 564337) B564337
theorem B752483 : Blo 443779 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B1506221 : Blo 443779 1506221 := bstep (se 3 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 1506221 = 564833) B564833
theorem B752611 : Blo 443779 752611 := bstep (se 1 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 752611 = 1128917) B1128917
theorem B1506275 : Blo 443779 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B752753 : Blo 443779 752753 := bstep (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) B564565
theorem B1899683 : Blo 443779 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B5078213 : Blo 443779 5078213 := bstep (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) B952165
theorem B752881 : Blo 443779 752881 := bstep (se 2 (by rfl) ⟨282330, by rfl⟩ : syracuseStep 752881 = 564661) B564661
theorem B1506545 : Blo 443779 1506545 := bstep (se 2 (by rfl) ⟨564954, by rfl⟩ : syracuseStep 1506545 = 1129909) B1129909
theorem B752915 : Blo 443779 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B3603811 : Blo 443779 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B949603 : Blo 443779 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B3079565 : Blo 443779 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B753043 : Blo 443779 753043 := bstep (se 1 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 753043 = 1129565) B1129565
theorem B753185 : Blo 443779 753185 := bstep (se 2 (by rfl) ⟨282444, by rfl⟩ : syracuseStep 753185 = 564889) B564889
theorem B2031245 : Blo 443779 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B753313 : Blo 443779 753313 := bstep (se 2 (by rfl) ⟨282492, by rfl⟩ : syracuseStep 753313 = 564985) B564985
theorem B753347 : Blo 443779 753347 := bstep (se 1 (by rfl) ⟨565010, by rfl⟩ : syracuseStep 753347 = 1130021) B1130021
theorem B1507085 : Blo 443779 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B753475 : Blo 443779 753475 := bstep (se 1 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 753475 = 1130213) B1130213
theorem B1507139 : Blo 443779 1507139 := bstep (se 1 (by rfl) ⟨1130354, by rfl⟩ : syracuseStep 1507139 = 2260709) B2260709
theorem B13565893 : Blo 443779 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B753617 : Blo 443779 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B16482325 : Blo 443779 16482325 := bstep (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) B772609
theorem B753995 : Blo 443779 753995 := bstep (se 1 (by rfl) ⟨565496, by rfl⟩ : syracuseStep 753995 = 1130993) B1130993
theorem B1507787 : Blo 443779 1507787 := bstep (se 1 (by rfl) ⟨1130840, by rfl⟩ : syracuseStep 1507787 = 2261681) B2261681
theorem B754123 : Blo 443779 754123 := bstep (se 1 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 754123 = 1131185) B1131185
theorem B1081817 : Blo 443779 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B754265 : Blo 443779 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B950935 : Blo 443779 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B1508057 : Blo 443779 1508057 := bstep (se 2 (by rfl) ⟨565521, by rfl⟩ : syracuseStep 1508057 = 1131043) B1131043
theorem B754393 : Blo 443779 754393 := bstep (se 2 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 754393 = 565795) B565795
theorem B9634625 : Blo 443779 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B1606493 : Blo 443779 1606493 := bstep (se 3 (by rfl) ⟨301217, by rfl⟩ : syracuseStep 1606493 = 602435) B602435
theorem B2262167 : Blo 443779 2262167 := bstep (se 1 (by rfl) ⟨1696625, by rfl⟩ : syracuseStep 2262167 = 3393251) B3393251
theorem B3802373 : Blo 443779 3802373 := bstep (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) B712945
theorem B754967 : Blo 443779 754967 := bstep (se 1 (by rfl) ⟨566225, by rfl⟩ : syracuseStep 754967 = 1132451) B1132451
theorem B1508759 : Blo 443779 1508759 := bstep (se 1 (by rfl) ⟨1131569, by rfl⟩ : syracuseStep 1508759 = 2263139) B2263139
theorem B755095 : Blo 443779 755095 := bstep (se 1 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 755095 = 1132643) B1132643
theorem B951755 : Blo 443779 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B1803865 : Blo 443779 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B4130509 : Blo 443779 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B3803057 : Blo 443779 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B1509299 : Blo 443779 1509299 := bstep (se 1 (by rfl) ⟨1131974, by rfl⟩ : syracuseStep 1509299 = 2263949) B2263949
theorem B854039 : Blo 443779 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B952499 : Blo 443779 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B1509569 : Blo 443779 1509569 := bstep (se 2 (by rfl) ⟨566088, by rfl⟩ : syracuseStep 1509569 = 1132177) B1132177
theorem B3377699 : Blo 443779 3377699 := bstep (se 1 (by rfl) ⟨2533274, by rfl⟩ : syracuseStep 3377699 = 5066549) B5066549
theorem B1903169 : Blo 443779 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B1608281 : Blo 443779 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B1018507 : Blo 443779 1018507 := bstep (se 1 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 1018507 = 1527761) B1527761
theorem B1510109 : Blo 443779 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B6195973 : Blo 443779 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B3804083 : Blo 443779 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B1444825 : Blo 443779 1444825 := bstep (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) B1083619
theorem B953345 : Blo 443779 953345 := bstep (se 2 (by rfl) ⟨357504, by rfl⟩ : syracuseStep 953345 = 715009) B715009
theorem B2886749 : Blo 443779 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B953687 : Blo 443779 953687 := bstep (se 1 (by rfl) ⟨715265, by rfl⟩ : syracuseStep 953687 = 1430531) B1430531
theorem B1904093 : Blo 443779 1904093 := bstep (se 3 (by rfl) ⟨357017, by rfl⟩ : syracuseStep 1904093 = 714035) B714035
theorem B1511243 : Blo 443779 1511243 := bstep (se 1 (by rfl) ⟨1133432, by rfl⟩ : syracuseStep 1511243 = 2266865) B2266865
theorem B6951005 : Blo 443779 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B2134147 : Blo 443779 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B2265731 : Blo 443779 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B6886129 : Blo 443779 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B725785 : Blo 443779 725785 := bstep (se 2 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 725785 = 544339) B544339
theorem B562135 : Blo 443779 562135 := bstep (se 1 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 562135 = 843203) B843203
theorem B2856343 : Blo 443779 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B4298275 : Blo 443779 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B14522773 : Blo 443779 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B3807809 : Blo 443779 3807809 := bstep (se 2 (by rfl) ⟨1427928, by rfl⟩ : syracuseStep 3807809 = 2855857) B2855857
theorem B563851 : Blo 443779 563851 := bstep (se 1 (by rfl) ⟨422888, by rfl⟩ : syracuseStep 563851 = 845777) B845777
theorem B1907459 : Blo 443779 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B859457 : Blo 443779 859457 := bstep (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) B644593
theorem B2858341 : Blo 443779 2858341 := bstep (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) B535939
theorem B2399705 : Blo 443779 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B2399789 : Blo 443779 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B564823 : Blo 443779 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B499351 : Blo 443779 499351 := bstep (se 1 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 499351 = 749027) B749027
theorem B3383045 : Blo 443779 3383045 := bstep (se 4 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 3383045 = 634321) B634321
theorem B499531 : Blo 443779 499531 := bstep (se 1 (by rfl) ⟨374648, by rfl⟩ : syracuseStep 499531 = 749297) B749297
theorem B1613699 : Blo 443779 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B499639 : Blo 443779 499639 := bstep (se 1 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 499639 = 749459) B749459
theorem B499819 : Blo 443779 499819 := bstep (se 1 (by rfl) ⟨374864, by rfl⟩ : syracuseStep 499819 = 749729) B749729
theorem B499927 : Blo 443779 499927 := bstep (se 1 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 499927 = 749891) B749891
theorem B500107 : Blo 443779 500107 := bstep (se 1 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 500107 = 750161) B750161
theorem B565643 : Blo 443779 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B500215 : Blo 443779 500215 := bstep (se 1 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 500215 = 750323) B750323
theorem B500395 : Blo 443779 500395 := bstep (se 1 (by rfl) ⟨375296, by rfl⟩ : syracuseStep 500395 = 750593) B750593
theorem B500503 : Blo 443779 500503 := bstep (se 1 (by rfl) ⟨375377, by rfl⟩ : syracuseStep 500503 = 750755) B750755
theorem B500683 : Blo 443779 500683 := bstep (se 1 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 500683 = 751025) B751025
theorem B1123379 : Blo 443779 1123379 := bstep (se 1 (by rfl) ⟨842534, by rfl⟩ : syracuseStep 1123379 = 1685069) B1685069
theorem B500791 : Blo 443779 500791 := bstep (se 1 (by rfl) ⟨375593, by rfl⟩ : syracuseStep 500791 = 751187) B751187
theorem B566347 : Blo 443779 566347 := bstep (se 1 (by rfl) ⟨424760, by rfl⟩ : syracuseStep 566347 = 849521) B849521
theorem B500971 : Blo 443779 500971 := bstep (se 1 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 500971 = 751457) B751457
theorem B861491 : Blo 443779 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B501079 : Blo 443779 501079 := bstep (se 1 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 501079 = 751619) B751619
theorem B566615 : Blo 443779 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B501259 : Blo 443779 501259 := bstep (se 1 (by rfl) ⟨375944, by rfl⟩ : syracuseStep 501259 = 751889) B751889
theorem B1975853 : Blo 443779 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1123915 : Blo 443779 1123915 := bstep (se 1 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 1123915 = 1685873) B1685873
theorem B501367 : Blo 443779 501367 := bstep (se 1 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 501367 = 752051) B752051
theorem B3221171 : Blo 443779 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B1124057 : Blo 443779 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B501547 : Blo 443779 501547 := bstep (se 1 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 501547 = 752321) B752321
theorem B501655 : Blo 443779 501655 := bstep (se 1 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 501655 = 752483) B752483
theorem B2172851 : Blo 443779 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B665675 : Blo 443779 665675 := bstep (se 1 (by rfl) ⟨499256, by rfl⟩ : syracuseStep 665675 = 998513) B998513
theorem B501835 : Blo 443779 501835 := bstep (se 1 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 501835 = 752753) B752753
theorem B665687 : Blo 443779 665687 := bstep (se 1 (by rfl) ⟨499265, by rfl⟩ : syracuseStep 665687 = 998531) B998531
theorem B3385475 : Blo 443779 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B665753 : Blo 443779 665753 := bstep (se 2 (by rfl) ⟨249657, by rfl⟩ : syracuseStep 665753 = 499315) B499315
theorem B501943 : Blo 443779 501943 := bstep (se 1 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 501943 = 752915) B752915
theorem B665867 : Blo 443779 665867 := bstep (se 1 (by rfl) ⟨499400, by rfl⟩ : syracuseStep 665867 = 998801) B998801
theorem B665879 : Blo 443779 665879 := bstep (se 1 (by rfl) ⟨499409, by rfl⟩ : syracuseStep 665879 = 998819) B998819
theorem B469271 : Blo 443779 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B1550657 : Blo 443779 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B665945 : Blo 443779 665945 := bstep (se 2 (by rfl) ⟨249729, by rfl⟩ : syracuseStep 665945 = 499459) B499459
theorem B3221861 : Blo 443779 3221861 := bstep (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) B604099
theorem B502123 : Blo 443779 502123 := bstep (se 1 (by rfl) ⟨376592, by rfl⟩ : syracuseStep 502123 = 753185) B753185
theorem B1354163 : Blo 443779 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B666059 : Blo 443779 666059 := bstep (se 1 (by rfl) ⟨499544, by rfl⟩ : syracuseStep 666059 = 999089) B999089
theorem B666071 : Blo 443779 666071 := bstep (se 1 (by rfl) ⟨499553, by rfl⟩ : syracuseStep 666071 = 999107) B999107
theorem B502231 : Blo 443779 502231 := bstep (se 1 (by rfl) ⟨376673, by rfl⟩ : syracuseStep 502231 = 753347) B753347
theorem B1124887 : Blo 443779 1124887 := bstep (se 1 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 1124887 = 1687331) B1687331
theorem B666137 : Blo 443779 666137 := bstep (se 2 (by rfl) ⟨249801, by rfl⟩ : syracuseStep 666137 = 499603) B499603
theorem B633433 : Blo 443779 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B666251 : Blo 443779 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B502411 : Blo 443779 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B666263 : Blo 443779 666263 := bstep (se 1 (by rfl) ⟨499697, by rfl⟩ : syracuseStep 666263 = 999395) B999395
theorem B535243 : Blo 443779 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B600791 : Blo 443779 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B666329 : Blo 443779 666329 := bstep (se 2 (by rfl) ⟨249873, by rfl⟩ : syracuseStep 666329 = 499747) B499747
theorem B502519 : Blo 443779 502519 := bstep (se 1 (by rfl) ⟨376889, by rfl⟩ : syracuseStep 502519 = 753779) B753779
theorem B1813271 : Blo 443779 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1911575 : Blo 443779 1911575 := bstep (se 1 (by rfl) ⟨1433681, by rfl⟩ : syracuseStep 1911575 = 2867363) B2867363
theorem B666443 : Blo 443779 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B666455 : Blo 443779 666455 := bstep (se 1 (by rfl) ⟨499841, by rfl⟩ : syracuseStep 666455 = 999683) B999683
theorem B666521 : Blo 443779 666521 := bstep (se 2 (by rfl) ⟨249945, by rfl⟩ : syracuseStep 666521 = 499891) B499891
theorem B502699 : Blo 443779 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B1125323 : Blo 443779 1125323 := bstep (se 1 (by rfl) ⟨843992, by rfl⟩ : syracuseStep 1125323 = 1687985) B1687985
theorem B666635 : Blo 443779 666635 := bstep (se 1 (by rfl) ⟨499976, by rfl⟩ : syracuseStep 666635 = 999953) B999953
theorem B666647 : Blo 443779 666647 := bstep (se 1 (by rfl) ⟨499985, by rfl⟩ : syracuseStep 666647 = 999971) B999971
theorem B502807 : Blo 443779 502807 := bstep (se 1 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 502807 = 754211) B754211
theorem B1911883 : Blo 443779 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B666713 : Blo 443779 666713 := bstep (se 2 (by rfl) ⟨250017, by rfl⟩ : syracuseStep 666713 = 500035) B500035
theorem B666827 : Blo 443779 666827 := bstep (se 1 (by rfl) ⟨500120, by rfl⟩ : syracuseStep 666827 = 1000241) B1000241
theorem B502987 : Blo 443779 502987 := bstep (se 1 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 502987 = 754481) B754481
theorem B666839 : Blo 443779 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B666905 : Blo 443779 666905 := bstep (se 2 (by rfl) ⟨250089, by rfl⟩ : syracuseStep 666905 = 500179) B500179
theorem B503095 : Blo 443779 503095 := bstep (se 1 (by rfl) ⟨377321, by rfl⟩ : syracuseStep 503095 = 754643) B754643
theorem B1125697 : Blo 443779 1125697 := bstep (se 2 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 1125697 = 844273) B844273
theorem B1912157 : Blo 443779 1912157 := bstep (se 3 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 1912157 = 717059) B717059
theorem B667019 : Blo 443779 667019 := bstep (se 1 (by rfl) ⟨500264, by rfl⟩ : syracuseStep 667019 = 1000529) B1000529
theorem B667031 : Blo 443779 667031 := bstep (se 1 (by rfl) ⟨500273, by rfl⟩ : syracuseStep 667031 = 1000547) B1000547
theorem B667097 : Blo 443779 667097 := bstep (se 2 (by rfl) ⟨250161, by rfl⟩ : syracuseStep 667097 = 500323) B500323
theorem B1224157 : Blo 443779 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B503275 : Blo 443779 503275 := bstep (se 1 (by rfl) ⟨377456, by rfl⟩ : syracuseStep 503275 = 754913) B754913
theorem B2141741 : Blo 443779 2141741 := bstep (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) B803153
theorem B667211 : Blo 443779 667211 := bstep (se 1 (by rfl) ⟨500408, by rfl⟩ : syracuseStep 667211 = 1000817) B1000817
theorem B667223 : Blo 443779 667223 := bstep (se 1 (by rfl) ⟨500417, by rfl⟩ : syracuseStep 667223 = 1000835) B1000835
theorem B503383 : Blo 443779 503383 := bstep (se 1 (by rfl) ⟨377537, by rfl⟩ : syracuseStep 503383 = 755075) B755075
theorem B667289 : Blo 443779 667289 := bstep (se 2 (by rfl) ⟨250233, by rfl⟩ : syracuseStep 667289 = 500467) B500467
theorem B667403 : Blo 443779 667403 := bstep (se 1 (by rfl) ⟨500552, by rfl⟩ : syracuseStep 667403 = 1001105) B1001105
theorem B503563 : Blo 443779 503563 := bstep (se 1 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 503563 = 755345) B755345
theorem B667415 : Blo 443779 667415 := bstep (se 1 (by rfl) ⟨500561, by rfl⟩ : syracuseStep 667415 = 1001123) B1001123
theorem B667481 : Blo 443779 667481 := bstep (se 2 (by rfl) ⟨250305, by rfl⟩ : syracuseStep 667481 = 500611) B500611
theorem B503671 : Blo 443779 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B1126295 : Blo 443779 1126295 := bstep (se 1 (by rfl) ⟨844721, by rfl⟩ : syracuseStep 1126295 = 1689443) B1689443
theorem B1552321 : Blo 443779 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B667595 : Blo 443779 667595 := bstep (se 1 (by rfl) ⟨500696, by rfl⟩ : syracuseStep 667595 = 1001393) B1001393
theorem B667607 : Blo 443779 667607 := bstep (se 1 (by rfl) ⟨500705, by rfl⟩ : syracuseStep 667607 = 1001411) B1001411
theorem B1814489 : Blo 443779 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B634891 : Blo 443779 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B667673 : Blo 443779 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B667787 : Blo 443779 667787 := bstep (se 1 (by rfl) ⟨500840, by rfl⟩ : syracuseStep 667787 = 1001681) B1001681
theorem B667799 : Blo 443779 667799 := bstep (se 1 (by rfl) ⟨500849, by rfl⟩ : syracuseStep 667799 = 1001699) B1001699
theorem B3813581 : Blo 443779 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B667865 : Blo 443779 667865 := bstep (se 2 (by rfl) ⟨250449, by rfl⟩ : syracuseStep 667865 = 500899) B500899
theorem B667979 : Blo 443779 667979 := bstep (se 1 (by rfl) ⟨500984, by rfl⟩ : syracuseStep 667979 = 1001969) B1001969
theorem B667991 : Blo 443779 667991 := bstep (se 1 (by rfl) ⟨500993, by rfl⟩ : syracuseStep 667991 = 1001987) B1001987
theorem B15446389 : Blo 443779 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B668057 : Blo 443779 668057 := bstep (se 2 (by rfl) ⟨250521, by rfl⟩ : syracuseStep 668057 = 501043) B501043
theorem B537035 : Blo 443779 537035 := bstep (se 1 (by rfl) ⟨402776, by rfl⟩ : syracuseStep 537035 = 805553) B805553
theorem B668171 : Blo 443779 668171 := bstep (se 1 (by rfl) ⟨501128, by rfl⟩ : syracuseStep 668171 = 1002257) B1002257
theorem B22196753 : Blo 443779 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B668183 : Blo 443779 668183 := bstep (se 1 (by rfl) ⟨501137, by rfl⟩ : syracuseStep 668183 = 1002275) B1002275
theorem B668249 : Blo 443779 668249 := bstep (se 2 (by rfl) ⟨250593, by rfl⟩ : syracuseStep 668249 = 501187) B501187
theorem B1127105 : Blo 443779 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B668363 : Blo 443779 668363 := bstep (se 1 (by rfl) ⟨501272, by rfl⟩ : syracuseStep 668363 = 1002545) B1002545
theorem B668375 : Blo 443779 668375 := bstep (se 1 (by rfl) ⟨501281, by rfl⟩ : syracuseStep 668375 = 1002563) B1002563
theorem B668441 : Blo 443779 668441 := bstep (se 2 (by rfl) ⟨250665, by rfl⟩ : syracuseStep 668441 = 501331) B501331
theorem B668555 : Blo 443779 668555 := bstep (se 1 (by rfl) ⟨501416, by rfl⟩ : syracuseStep 668555 = 1002833) B1002833
theorem B668567 : Blo 443779 668567 := bstep (se 1 (by rfl) ⟨501425, by rfl⟩ : syracuseStep 668567 = 1002851) B1002851
theorem B1356695 : Blo 443779 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B668633 : Blo 443779 668633 := bstep (se 2 (by rfl) ⟨250737, by rfl⟩ : syracuseStep 668633 = 501475) B501475
theorem B668747 : Blo 443779 668747 := bstep (se 1 (by rfl) ⟨501560, by rfl⟩ : syracuseStep 668747 = 1003121) B1003121
theorem B668759 : Blo 443779 668759 := bstep (se 1 (by rfl) ⟨501569, by rfl⟩ : syracuseStep 668759 = 1003139) B1003139
theorem B668825 : Blo 443779 668825 := bstep (se 2 (by rfl) ⟨250809, by rfl⟩ : syracuseStep 668825 = 501619) B501619
theorem B1127641 : Blo 443779 1127641 := bstep (se 2 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 1127641 = 845731) B845731
theorem B636121 : Blo 443779 636121 := bstep (se 2 (by rfl) ⟨238545, by rfl⟩ : syracuseStep 636121 = 477091) B477091
theorem B668939 : Blo 443779 668939 := bstep (se 1 (by rfl) ⟨501704, by rfl⟩ : syracuseStep 668939 = 1003409) B1003409
theorem B668951 : Blo 443779 668951 := bstep (se 1 (by rfl) ⟨501713, by rfl⟩ : syracuseStep 668951 = 1003427) B1003427
theorem B669017 : Blo 443779 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B669131 : Blo 443779 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B3388877 : Blo 443779 3388877 := bstep (se 3 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 3388877 = 1270829) B1270829
theorem B669143 : Blo 443779 669143 := bstep (se 1 (by rfl) ⟨501857, by rfl⟩ : syracuseStep 669143 = 1003715) B1003715
theorem B865753 : Blo 443779 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B669209 : Blo 443779 669209 := bstep (se 2 (by rfl) ⟨250953, by rfl⟩ : syracuseStep 669209 = 501907) B501907
theorem B2405933 : Blo 443779 2405933 := bstep (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) B902225
theorem B669323 : Blo 443779 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B669335 : Blo 443779 669335 := bstep (se 1 (by rfl) ⟨502001, by rfl⟩ : syracuseStep 669335 = 1004003) B1004003
theorem B669401 : Blo 443779 669401 := bstep (se 2 (by rfl) ⟨251025, by rfl⟩ : syracuseStep 669401 = 502051) B502051
theorem B669515 : Blo 443779 669515 := bstep (se 1 (by rfl) ⟨502136, by rfl⟩ : syracuseStep 669515 = 1004273) B1004273
theorem B669527 : Blo 443779 669527 := bstep (se 1 (by rfl) ⟨502145, by rfl⟩ : syracuseStep 669527 = 1004291) B1004291
theorem B669593 : Blo 443779 669593 := bstep (se 2 (by rfl) ⟨251097, by rfl⟩ : syracuseStep 669593 = 502195) B502195
theorem B3389363 : Blo 443779 3389363 := bstep (se 1 (by rfl) ⟨2542022, by rfl⟩ : syracuseStep 3389363 = 5084045) B5084045
theorem B669707 : Blo 443779 669707 := bstep (se 1 (by rfl) ⟨502280, by rfl⟩ : syracuseStep 669707 = 1004561) B1004561
theorem B669719 : Blo 443779 669719 := bstep (se 1 (by rfl) ⟨502289, by rfl⟩ : syracuseStep 669719 = 1004579) B1004579
theorem B1685555 : Blo 443779 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B1685569 : Blo 443779 1685569 := bstep (se 2 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 1685569 = 1264177) B1264177
theorem B669785 : Blo 443779 669785 := bstep (se 2 (by rfl) ⟨251169, by rfl⟩ : syracuseStep 669785 = 502339) B502339
theorem B669899 : Blo 443779 669899 := bstep (se 1 (by rfl) ⟨502424, by rfl⟩ : syracuseStep 669899 = 1004849) B1004849
theorem B669911 : Blo 443779 669911 := bstep (se 1 (by rfl) ⟨502433, by rfl⟩ : syracuseStep 669911 = 1004867) B1004867
theorem B669977 : Blo 443779 669977 := bstep (se 2 (by rfl) ⟨251241, by rfl⟩ : syracuseStep 669977 = 502483) B502483
theorem B1128755 : Blo 443779 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B670091 : Blo 443779 670091 := bstep (se 1 (by rfl) ⟨502568, by rfl⟩ : syracuseStep 670091 = 1005137) B1005137
theorem B2144663 : Blo 443779 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B670103 : Blo 443779 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B670169 : Blo 443779 670169 := bstep (se 2 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 670169 = 502627) B502627
theorem B637465 : Blo 443779 637465 := bstep (se 2 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 637465 = 478099) B478099
theorem B670283 : Blo 443779 670283 := bstep (se 1 (by rfl) ⟨502712, by rfl⟩ : syracuseStep 670283 = 1005425) B1005425
theorem B670295 : Blo 443779 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B1129049 : Blo 443779 1129049 := bstep (se 2 (by rfl) ⟨423393, by rfl⟩ : syracuseStep 1129049 = 846787) B846787
theorem B670361 : Blo 443779 670361 := bstep (se 2 (by rfl) ⟨251385, by rfl⟩ : syracuseStep 670361 = 502771) B502771
theorem B670475 : Blo 443779 670475 := bstep (se 1 (by rfl) ⟨502856, by rfl⟩ : syracuseStep 670475 = 1005713) B1005713
theorem B670487 : Blo 443779 670487 := bstep (se 1 (by rfl) ⟨502865, by rfl⟩ : syracuseStep 670487 = 1005731) B1005731
theorem B670553 : Blo 443779 670553 := bstep (se 2 (by rfl) ⟨251457, by rfl⟩ : syracuseStep 670553 = 502915) B502915
theorem B474007 : Blo 443779 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B2407319 : Blo 443779 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B900019 : Blo 443779 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B670667 : Blo 443779 670667 := bstep (se 1 (by rfl) ⟨503000, by rfl⟩ : syracuseStep 670667 = 1006001) B1006001
theorem B670679 : Blo 443779 670679 := bstep (se 1 (by rfl) ⟨503009, by rfl⟩ : syracuseStep 670679 = 1006019) B1006019
theorem B670745 : Blo 443779 670745 := bstep (se 2 (by rfl) ⟨251529, by rfl⟩ : syracuseStep 670745 = 503059) B503059
theorem B670859 : Blo 443779 670859 := bstep (se 1 (by rfl) ⟨503144, by rfl⟩ : syracuseStep 670859 = 1006289) B1006289
theorem B670871 : Blo 443779 670871 := bstep (se 1 (by rfl) ⟨503153, by rfl⟩ : syracuseStep 670871 = 1006307) B1006307
theorem B998603 : Blo 443779 998603 := bstep (se 1 (by rfl) ⟨748952, by rfl⟩ : syracuseStep 998603 = 1497905) B1497905
theorem B670937 : Blo 443779 670937 := bstep (se 2 (by rfl) ⟨251601, by rfl⟩ : syracuseStep 670937 = 503203) B503203
theorem B998657 : Blo 443779 998657 := bstep (se 2 (by rfl) ⟨374496, by rfl⟩ : syracuseStep 998657 = 748993) B748993
theorem B1359127 : Blo 443779 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B671051 : Blo 443779 671051 := bstep (se 1 (by rfl) ⟨503288, by rfl⟩ : syracuseStep 671051 = 1006577) B1006577
theorem B671063 : Blo 443779 671063 := bstep (se 1 (by rfl) ⟨503297, by rfl⟩ : syracuseStep 671063 = 1006595) B1006595
theorem B3390821 : Blo 443779 3390821 := bstep (se 4 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 3390821 = 635779) B635779
theorem B671129 : Blo 443779 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B998873 : Blo 443779 998873 := bstep (se 2 (by rfl) ⟨374577, by rfl⟩ : syracuseStep 998873 = 749155) B749155
theorem B671243 : Blo 443779 671243 := bstep (se 1 (by rfl) ⟨503432, by rfl⟩ : syracuseStep 671243 = 1006865) B1006865
theorem B671255 : Blo 443779 671255 := bstep (se 1 (by rfl) ⟨503441, by rfl⟩ : syracuseStep 671255 = 1006883) B1006883
theorem B998963 : Blo 443779 998963 := bstep (se 1 (by rfl) ⟨749222, by rfl⟩ : syracuseStep 998963 = 1498445) B1498445
theorem B998999 : Blo 443779 998999 := bstep (se 1 (by rfl) ⟨749249, by rfl⟩ : syracuseStep 998999 = 1498499) B1498499
theorem B966233 : Blo 443779 966233 := bstep (se 2 (by rfl) ⟨362337, by rfl⟩ : syracuseStep 966233 = 724675) B724675
theorem B671321 : Blo 443779 671321 := bstep (se 2 (by rfl) ⟨251745, by rfl⟩ : syracuseStep 671321 = 503491) B503491
theorem B474827 : Blo 443779 474827 := bstep (se 1 (by rfl) ⟨356120, by rfl⟩ : syracuseStep 474827 = 712241) B712241
theorem B671435 : Blo 443779 671435 := bstep (se 1 (by rfl) ⟨503576, by rfl⟩ : syracuseStep 671435 = 1007153) B1007153
theorem B671447 : Blo 443779 671447 := bstep (se 1 (by rfl) ⟨503585, by rfl⟩ : syracuseStep 671447 = 1007171) B1007171
theorem B999179 : Blo 443779 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B671513 : Blo 443779 671513 := bstep (se 2 (by rfl) ⟨251817, by rfl⟩ : syracuseStep 671513 = 503635) B503635
theorem B507703 : Blo 443779 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B999233 : Blo 443779 999233 := bstep (se 2 (by rfl) ⟨374712, by rfl⟩ : syracuseStep 999233 = 749425) B749425
theorem B2408267 : Blo 443779 2408267 := bstep (se 1 (by rfl) ⟨1806200, by rfl⟩ : syracuseStep 2408267 = 3612401) B3612401
theorem B3391307 : Blo 443779 3391307 := bstep (se 1 (by rfl) ⟨2543480, by rfl⟩ : syracuseStep 3391307 = 5086961) B5086961
theorem B1982339 : Blo 443779 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B671627 : Blo 443779 671627 := bstep (se 1 (by rfl) ⟨503720, by rfl⟩ : syracuseStep 671627 = 1007441) B1007441
theorem B671639 : Blo 443779 671639 := bstep (se 1 (by rfl) ⟨503729, by rfl⟩ : syracuseStep 671639 = 1007459) B1007459
theorem B3063703 : Blo 443779 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B1687499 : Blo 443779 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B1687513 : Blo 443779 1687513 := bstep (se 2 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 1687513 = 1265635) B1265635
theorem B999449 : Blo 443779 999449 := bstep (se 2 (by rfl) ⟨374793, by rfl⟩ : syracuseStep 999449 = 749587) B749587
theorem B7356509 : Blo 443779 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B999539 : Blo 443779 999539 := bstep (se 1 (by rfl) ⟨749654, by rfl⟩ : syracuseStep 999539 = 1499309) B1499309
theorem B999575 : Blo 443779 999575 := bstep (se 1 (by rfl) ⟨749681, by rfl⟩ : syracuseStep 999575 = 1499363) B1499363
theorem B1130699 : Blo 443779 1130699 := bstep (se 1 (by rfl) ⟨848024, by rfl⟩ : syracuseStep 1130699 = 1696049) B1696049
theorem B999755 : Blo 443779 999755 := bstep (se 1 (by rfl) ⟨749816, by rfl⟩ : syracuseStep 999755 = 1499633) B1499633
theorem B999809 : Blo 443779 999809 := bstep (se 2 (by rfl) ⟨374928, by rfl⟩ : syracuseStep 999809 = 749857) B749857
theorem B1000025 : Blo 443779 1000025 := bstep (se 2 (by rfl) ⟨375009, by rfl⟩ : syracuseStep 1000025 = 750019) B750019
theorem B1000115 : Blo 443779 1000115 := bstep (se 1 (by rfl) ⟨750086, by rfl⟩ : syracuseStep 1000115 = 1500173) B1500173
theorem B1000151 : Blo 443779 1000151 := bstep (se 1 (by rfl) ⟨750113, by rfl⟩ : syracuseStep 1000151 = 1500227) B1500227
theorem B475895 : Blo 443779 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B4571909 : Blo 443779 4571909 := bstep (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) B857233
theorem B1000331 : Blo 443779 1000331 := bstep (se 1 (by rfl) ⟨750248, by rfl⟩ : syracuseStep 1000331 = 1500497) B1500497
theorem B1688471 : Blo 443779 1688471 := bstep (se 1 (by rfl) ⟨1266353, by rfl⟩ : syracuseStep 1688471 = 2532707) B2532707
theorem B3621809 : Blo 443779 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B7619507 : Blo 443779 7619507 := bstep (se 1 (by rfl) ⟨5714630, by rfl⟩ : syracuseStep 7619507 = 11429261) B11429261
theorem B1000385 : Blo 443779 1000385 := bstep (se 2 (by rfl) ⟨375144, by rfl⟩ : syracuseStep 1000385 = 750289) B750289
theorem B1131671 : Blo 443779 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B1000601 : Blo 443779 1000601 := bstep (se 2 (by rfl) ⟨375225, by rfl⟩ : syracuseStep 1000601 = 750451) B750451
theorem B1000691 : Blo 443779 1000691 := bstep (se 1 (by rfl) ⟨750518, by rfl⟩ : syracuseStep 1000691 = 1501037) B1501037
theorem B902387 : Blo 443779 902387 := bstep (se 1 (by rfl) ⟨676790, by rfl⟩ : syracuseStep 902387 = 1353581) B1353581
theorem B1000727 : Blo 443779 1000727 := bstep (se 1 (by rfl) ⟨750545, by rfl⟩ : syracuseStep 1000727 = 1501091) B1501091
theorem B443787 : Blo 443779 443787 := bstep (se 1 (by rfl) ⟨332840, by rfl⟩ : syracuseStep 443787 = 665681) B665681
theorem B443799 : Blo 443779 443799 := bstep (se 1 (by rfl) ⟨332849, by rfl⟩ : syracuseStep 443799 = 665699) B665699
theorem B443819 : Blo 443779 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B443831 : Blo 443779 443831 := bstep (se 1 (by rfl) ⟨332873, by rfl⟩ : syracuseStep 443831 = 665747) B665747
theorem B443851 : Blo 443779 443851 := bstep (se 1 (by rfl) ⟨332888, by rfl⟩ : syracuseStep 443851 = 665777) B665777
theorem B1000907 : Blo 443779 1000907 := bstep (se 1 (by rfl) ⟨750680, by rfl⟩ : syracuseStep 1000907 = 1501361) B1501361
theorem B443863 : Blo 443779 443863 := bstep (se 1 (by rfl) ⟨332897, by rfl⟩ : syracuseStep 443863 = 665795) B665795
theorem B1590749 : Blo 443779 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B443883 : Blo 443779 443883 := bstep (se 1 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 443883 = 665825) B665825
theorem B443895 : Blo 443779 443895 := bstep (se 1 (by rfl) ⟨332921, by rfl⟩ : syracuseStep 443895 = 665843) B665843
theorem B1000961 : Blo 443779 1000961 := bstep (se 2 (by rfl) ⟨375360, by rfl⟩ : syracuseStep 1000961 = 750721) B750721
theorem B443915 : Blo 443779 443915 := bstep (se 1 (by rfl) ⟨332936, by rfl⟩ : syracuseStep 443915 = 665873) B665873
theorem B443927 : Blo 443779 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B1426967 : Blo 443779 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B443947 : Blo 443779 443947 := bstep (se 1 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 443947 = 665921) B665921
theorem B443959 : Blo 443779 443959 := bstep (se 1 (by rfl) ⟨332969, by rfl⟩ : syracuseStep 443959 = 665939) B665939
theorem B443979 : Blo 443779 443979 := bstep (se 1 (by rfl) ⟨332984, by rfl⟩ : syracuseStep 443979 = 665969) B665969
theorem B443991 : Blo 443779 443991 := bstep (se 1 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 443991 = 665987) B665987
theorem B444011 : Blo 443779 444011 := bstep (se 1 (by rfl) ⟨333008, by rfl⟩ : syracuseStep 444011 = 666017) B666017
theorem B444023 : Blo 443779 444023 := bstep (se 1 (by rfl) ⟨333017, by rfl⟩ : syracuseStep 444023 = 666035) B666035
theorem B4867715 : Blo 443779 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B444043 : Blo 443779 444043 := bstep (se 1 (by rfl) ⟨333032, by rfl⟩ : syracuseStep 444043 = 666065) B666065
theorem B444055 : Blo 443779 444055 := bstep (se 1 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 444055 = 666083) B666083
theorem B444075 : Blo 443779 444075 := bstep (se 1 (by rfl) ⟨333056, by rfl⟩ : syracuseStep 444075 = 666113) B666113
theorem B444087 : Blo 443779 444087 := bstep (se 1 (by rfl) ⟨333065, by rfl⟩ : syracuseStep 444087 = 666131) B666131
theorem B444107 : Blo 443779 444107 := bstep (se 1 (by rfl) ⟨333080, by rfl⟩ : syracuseStep 444107 = 666161) B666161
theorem B444119 : Blo 443779 444119 := bstep (se 1 (by rfl) ⟨333089, by rfl⟩ : syracuseStep 444119 = 666179) B666179
theorem B1001177 : Blo 443779 1001177 := bstep (se 2 (by rfl) ⟨375441, by rfl⟩ : syracuseStep 1001177 = 750883) B750883
theorem B444139 : Blo 443779 444139 := bstep (se 1 (by rfl) ⟨333104, by rfl⟩ : syracuseStep 444139 = 666209) B666209
theorem B444151 : Blo 443779 444151 := bstep (se 1 (by rfl) ⟨333113, by rfl⟩ : syracuseStep 444151 = 666227) B666227
theorem B444171 : Blo 443779 444171 := bstep (se 1 (by rfl) ⟨333128, by rfl⟩ : syracuseStep 444171 = 666257) B666257
theorem B444183 : Blo 443779 444183 := bstep (se 1 (by rfl) ⟨333137, by rfl⟩ : syracuseStep 444183 = 666275) B666275
theorem B444203 : Blo 443779 444203 := bstep (se 1 (by rfl) ⟨333152, by rfl⟩ : syracuseStep 444203 = 666305) B666305
theorem B476971 : Blo 443779 476971 := bstep (se 1 (by rfl) ⟨357728, by rfl⟩ : syracuseStep 476971 = 715457) B715457
theorem B1001267 : Blo 443779 1001267 := bstep (se 1 (by rfl) ⟨750950, by rfl⟩ : syracuseStep 1001267 = 1501901) B1501901
theorem B1132339 : Blo 443779 1132339 := bstep (se 1 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 1132339 = 1698509) B1698509
theorem B444215 : Blo 443779 444215 := bstep (se 1 (by rfl) ⟨333161, by rfl⟩ : syracuseStep 444215 = 666323) B666323
theorem B444235 : Blo 443779 444235 := bstep (se 1 (by rfl) ⟨333176, by rfl⟩ : syracuseStep 444235 = 666353) B666353
theorem B444247 : Blo 443779 444247 := bstep (se 1 (by rfl) ⟨333185, by rfl⟩ : syracuseStep 444247 = 666371) B666371
theorem B1001303 : Blo 443779 1001303 := bstep (se 1 (by rfl) ⟨750977, by rfl⟩ : syracuseStep 1001303 = 1501955) B1501955
theorem B444267 : Blo 443779 444267 := bstep (se 1 (by rfl) ⟨333200, by rfl⟩ : syracuseStep 444267 = 666401) B666401
theorem B444279 : Blo 443779 444279 := bstep (se 1 (by rfl) ⟨333209, by rfl⟩ : syracuseStep 444279 = 666419) B666419
theorem B509815 : Blo 443779 509815 := bstep (se 1 (by rfl) ⟨382361, by rfl⟩ : syracuseStep 509815 = 764723) B764723
theorem B444299 : Blo 443779 444299 := bstep (se 1 (by rfl) ⟨333224, by rfl⟩ : syracuseStep 444299 = 666449) B666449
theorem B444311 : Blo 443779 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B444331 : Blo 443779 444331 := bstep (se 1 (by rfl) ⟨333248, by rfl⟩ : syracuseStep 444331 = 666497) B666497
theorem B444343 : Blo 443779 444343 := bstep (se 1 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 444343 = 666515) B666515
theorem B1132481 : Blo 443779 1132481 := bstep (se 2 (by rfl) ⟨424680, by rfl⟩ : syracuseStep 1132481 = 849361) B849361
theorem B444363 : Blo 443779 444363 := bstep (se 1 (by rfl) ⟨333272, by rfl⟩ : syracuseStep 444363 = 666545) B666545
theorem B444375 : Blo 443779 444375 := bstep (se 1 (by rfl) ⟨333281, by rfl⟩ : syracuseStep 444375 = 666563) B666563
theorem B444395 : Blo 443779 444395 := bstep (se 1 (by rfl) ⟨333296, by rfl⟩ : syracuseStep 444395 = 666593) B666593
theorem B444407 : Blo 443779 444407 := bstep (se 1 (by rfl) ⟨333305, by rfl⟩ : syracuseStep 444407 = 666611) B666611
theorem B444427 : Blo 443779 444427 := bstep (se 1 (by rfl) ⟨333320, by rfl⟩ : syracuseStep 444427 = 666641) B666641
theorem B1001483 : Blo 443779 1001483 := bstep (se 1 (by rfl) ⟨751112, by rfl⟩ : syracuseStep 1001483 = 1502225) B1502225
theorem B444439 : Blo 443779 444439 := bstep (se 1 (by rfl) ⟨333329, by rfl⟩ : syracuseStep 444439 = 666659) B666659
theorem B444459 : Blo 443779 444459 := bstep (se 1 (by rfl) ⟨333344, by rfl⟩ : syracuseStep 444459 = 666689) B666689
theorem B444471 : Blo 443779 444471 := bstep (se 1 (by rfl) ⟨333353, by rfl⟩ : syracuseStep 444471 = 666707) B666707
theorem B1001537 : Blo 443779 1001537 := bstep (se 2 (by rfl) ⟨375576, by rfl⟩ : syracuseStep 1001537 = 751153) B751153
theorem B444491 : Blo 443779 444491 := bstep (se 1 (by rfl) ⟨333368, by rfl⟩ : syracuseStep 444491 = 666737) B666737
theorem B3819595 : Blo 443779 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B444503 : Blo 443779 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B4278365 : Blo 443779 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B444523 : Blo 443779 444523 := bstep (se 1 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 444523 = 666785) B666785
theorem B444535 : Blo 443779 444535 := bstep (se 1 (by rfl) ⟨333401, by rfl⟩ : syracuseStep 444535 = 666803) B666803
theorem B1689731 : Blo 443779 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B444555 : Blo 443779 444555 := bstep (se 1 (by rfl) ⟨333416, by rfl⟩ : syracuseStep 444555 = 666833) B666833
theorem B444567 : Blo 443779 444567 := bstep (se 1 (by rfl) ⟨333425, by rfl⟩ : syracuseStep 444567 = 666851) B666851
theorem B444587 : Blo 443779 444587 := bstep (se 1 (by rfl) ⟨333440, by rfl⟩ : syracuseStep 444587 = 666881) B666881
theorem B444599 : Blo 443779 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B444619 : Blo 443779 444619 := bstep (se 1 (by rfl) ⟨333464, by rfl⟩ : syracuseStep 444619 = 666929) B666929
theorem B444631 : Blo 443779 444631 := bstep (se 1 (by rfl) ⟨333473, by rfl⟩ : syracuseStep 444631 = 666947) B666947
theorem B444651 : Blo 443779 444651 := bstep (se 1 (by rfl) ⟨333488, by rfl⟩ : syracuseStep 444651 = 666977) B666977
theorem B444663 : Blo 443779 444663 := bstep (se 1 (by rfl) ⟨333497, by rfl⟩ : syracuseStep 444663 = 666995) B666995
theorem B444683 : Blo 443779 444683 := bstep (se 1 (by rfl) ⟨333512, by rfl⟩ : syracuseStep 444683 = 667025) B667025
theorem B444695 : Blo 443779 444695 := bstep (se 1 (by rfl) ⟨333521, by rfl⟩ : syracuseStep 444695 = 667043) B667043
theorem B1001753 : Blo 443779 1001753 := bstep (se 2 (by rfl) ⟨375657, by rfl⟩ : syracuseStep 1001753 = 751315) B751315
theorem B444715 : Blo 443779 444715 := bstep (se 1 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 444715 = 667073) B667073
theorem B444727 : Blo 443779 444727 := bstep (se 1 (by rfl) ⟨333545, by rfl⟩ : syracuseStep 444727 = 667091) B667091
theorem B444747 : Blo 443779 444747 := bstep (se 1 (by rfl) ⟨333560, by rfl⟩ : syracuseStep 444747 = 667121) B667121
theorem B444759 : Blo 443779 444759 := bstep (se 1 (by rfl) ⟨333569, by rfl⟩ : syracuseStep 444759 = 667139) B667139
theorem B3819869 : Blo 443779 3819869 := bstep (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) B1432451
theorem B444779 : Blo 443779 444779 := bstep (se 1 (by rfl) ⟨333584, by rfl⟩ : syracuseStep 444779 = 667169) B667169
theorem B1001843 : Blo 443779 1001843 := bstep (se 1 (by rfl) ⟨751382, by rfl⟩ : syracuseStep 1001843 = 1502765) B1502765
theorem B444791 : Blo 443779 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B444811 : Blo 443779 444811 := bstep (se 1 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 444811 = 667217) B667217
theorem B444823 : Blo 443779 444823 := bstep (se 1 (by rfl) ⟨333617, by rfl⟩ : syracuseStep 444823 = 667235) B667235
theorem B1001879 : Blo 443779 1001879 := bstep (se 1 (by rfl) ⟨751409, by rfl⟩ : syracuseStep 1001879 = 1502819) B1502819
theorem B444843 : Blo 443779 444843 := bstep (se 1 (by rfl) ⟨333632, by rfl⟩ : syracuseStep 444843 = 667265) B667265
theorem B444855 : Blo 443779 444855 := bstep (se 1 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 444855 = 667283) B667283
theorem B444875 : Blo 443779 444875 := bstep (se 1 (by rfl) ⟨333656, by rfl⟩ : syracuseStep 444875 = 667313) B667313
theorem B444887 : Blo 443779 444887 := bstep (se 1 (by rfl) ⟨333665, by rfl⟩ : syracuseStep 444887 = 667331) B667331
theorem B2279897 : Blo 443779 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B444907 : Blo 443779 444907 := bstep (se 1 (by rfl) ⟨333680, by rfl⟩ : syracuseStep 444907 = 667361) B667361
theorem B444919 : Blo 443779 444919 := bstep (se 1 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 444919 = 667379) B667379
theorem B444939 : Blo 443779 444939 := bstep (se 1 (by rfl) ⟨333704, by rfl⟩ : syracuseStep 444939 = 667409) B667409
theorem B444951 : Blo 443779 444951 := bstep (se 1 (by rfl) ⟨333713, by rfl⟩ : syracuseStep 444951 = 667427) B667427
theorem B444971 : Blo 443779 444971 := bstep (se 1 (by rfl) ⟨333728, by rfl⟩ : syracuseStep 444971 = 667457) B667457
theorem B444983 : Blo 443779 444983 := bstep (se 1 (by rfl) ⟨333737, by rfl⟩ : syracuseStep 444983 = 667475) B667475
theorem B445003 : Blo 443779 445003 := bstep (se 1 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 445003 = 667505) B667505
theorem B1002059 : Blo 443779 1002059 := bstep (se 1 (by rfl) ⟨751544, by rfl⟩ : syracuseStep 1002059 = 1503089) B1503089
theorem B1428043 : Blo 443779 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B445015 : Blo 443779 445015 := bstep (se 1 (by rfl) ⟨333761, by rfl⟩ : syracuseStep 445015 = 667523) B667523
theorem B445035 : Blo 443779 445035 := bstep (se 1 (by rfl) ⟨333776, by rfl⟩ : syracuseStep 445035 = 667553) B667553
theorem B445047 : Blo 443779 445047 := bstep (se 1 (by rfl) ⟨333785, by rfl⟩ : syracuseStep 445047 = 667571) B667571
theorem B1002113 : Blo 443779 1002113 := bstep (se 2 (by rfl) ⟨375792, by rfl⟩ : syracuseStep 1002113 = 751585) B751585
theorem B445067 : Blo 443779 445067 := bstep (se 1 (by rfl) ⟨333800, by rfl⟩ : syracuseStep 445067 = 667601) B667601
theorem B445079 : Blo 443779 445079 := bstep (se 1 (by rfl) ⟨333809, by rfl⟩ : syracuseStep 445079 = 667619) B667619
theorem B445099 : Blo 443779 445099 := bstep (se 1 (by rfl) ⟨333824, by rfl⟩ : syracuseStep 445099 = 667649) B667649
theorem B445111 : Blo 443779 445111 := bstep (se 1 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 445111 = 667667) B667667
theorem B445131 : Blo 443779 445131 := bstep (se 1 (by rfl) ⟨333848, by rfl⟩ : syracuseStep 445131 = 667697) B667697
theorem B445143 : Blo 443779 445143 := bstep (se 1 (by rfl) ⟨333857, by rfl⟩ : syracuseStep 445143 = 667715) B667715
theorem B477911 : Blo 443779 477911 := bstep (se 1 (by rfl) ⟨358433, by rfl⟩ : syracuseStep 477911 = 716867) B716867
theorem B1264349 : Blo 443779 1264349 := bstep (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) B474131
theorem B445163 : Blo 443779 445163 := bstep (se 1 (by rfl) ⟨333872, by rfl⟩ : syracuseStep 445163 = 667745) B667745
theorem B445175 : Blo 443779 445175 := bstep (se 1 (by rfl) ⟨333881, by rfl⟩ : syracuseStep 445175 = 667763) B667763
theorem B445195 : Blo 443779 445195 := bstep (se 1 (by rfl) ⟨333896, by rfl⟩ : syracuseStep 445195 = 667793) B667793
theorem B445207 : Blo 443779 445207 := bstep (se 1 (by rfl) ⟨333905, by rfl⟩ : syracuseStep 445207 = 667811) B667811
theorem B445227 : Blo 443779 445227 := bstep (se 1 (by rfl) ⟨333920, by rfl⟩ : syracuseStep 445227 = 667841) B667841
theorem B445239 : Blo 443779 445239 := bstep (se 1 (by rfl) ⟨333929, by rfl⟩ : syracuseStep 445239 = 667859) B667859
theorem B445259 : Blo 443779 445259 := bstep (se 1 (by rfl) ⟨333944, by rfl⟩ : syracuseStep 445259 = 667889) B667889
theorem B445271 : Blo 443779 445271 := bstep (se 1 (by rfl) ⟨333953, by rfl⟩ : syracuseStep 445271 = 667907) B667907
theorem B641881 : Blo 443779 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B1002329 : Blo 443779 1002329 := bstep (se 2 (by rfl) ⟨375873, by rfl⟩ : syracuseStep 1002329 = 751747) B751747
theorem B445291 : Blo 443779 445291 := bstep (se 1 (by rfl) ⟨333968, by rfl⟩ : syracuseStep 445291 = 667937) B667937
theorem B445303 : Blo 443779 445303 := bstep (se 1 (by rfl) ⟨333977, by rfl⟩ : syracuseStep 445303 = 667955) B667955
theorem B445323 : Blo 443779 445323 := bstep (se 1 (by rfl) ⟨333992, by rfl⟩ : syracuseStep 445323 = 667985) B667985
theorem B445335 : Blo 443779 445335 := bstep (se 1 (by rfl) ⟨334001, by rfl⟩ : syracuseStep 445335 = 668003) B668003
theorem B445355 : Blo 443779 445355 := bstep (se 1 (by rfl) ⟨334016, by rfl⟩ : syracuseStep 445355 = 668033) B668033
theorem B1002419 : Blo 443779 1002419 := bstep (se 1 (by rfl) ⟨751814, by rfl⟩ : syracuseStep 1002419 = 1503629) B1503629
theorem B445367 : Blo 443779 445367 := bstep (se 1 (by rfl) ⟨334025, by rfl⟩ : syracuseStep 445367 = 668051) B668051
theorem B445387 : Blo 443779 445387 := bstep (se 1 (by rfl) ⟨334040, by rfl⟩ : syracuseStep 445387 = 668081) B668081
theorem B904139 : Blo 443779 904139 := bstep (se 1 (by rfl) ⟨678104, by rfl⟩ : syracuseStep 904139 = 1356209) B1356209
theorem B445399 : Blo 443779 445399 := bstep (se 1 (by rfl) ⟨334049, by rfl⟩ : syracuseStep 445399 = 668099) B668099
theorem B1002455 : Blo 443779 1002455 := bstep (se 1 (by rfl) ⟨751841, by rfl⟩ : syracuseStep 1002455 = 1503683) B1503683
theorem B445419 : Blo 443779 445419 := bstep (se 1 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 445419 = 668129) B668129
theorem B445431 : Blo 443779 445431 := bstep (se 1 (by rfl) ⟨334073, by rfl⟩ : syracuseStep 445431 = 668147) B668147
theorem B445451 : Blo 443779 445451 := bstep (se 1 (by rfl) ⟨334088, by rfl⟩ : syracuseStep 445451 = 668177) B668177
theorem B445463 : Blo 443779 445463 := bstep (se 1 (by rfl) ⟨334097, by rfl⟩ : syracuseStep 445463 = 668195) B668195
theorem B445483 : Blo 443779 445483 := bstep (se 1 (by rfl) ⟨334112, by rfl⟩ : syracuseStep 445483 = 668225) B668225
theorem B445495 : Blo 443779 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B445515 : Blo 443779 445515 := bstep (se 1 (by rfl) ⟨334136, by rfl⟩ : syracuseStep 445515 = 668273) B668273
theorem B445527 : Blo 443779 445527 := bstep (se 1 (by rfl) ⟨334145, by rfl⟩ : syracuseStep 445527 = 668291) B668291
theorem B445547 : Blo 443779 445547 := bstep (se 1 (by rfl) ⟨334160, by rfl⟩ : syracuseStep 445547 = 668321) B668321
theorem B445559 : Blo 443779 445559 := bstep (se 1 (by rfl) ⟨334169, by rfl⟩ : syracuseStep 445559 = 668339) B668339
theorem B445579 : Blo 443779 445579 := bstep (se 1 (by rfl) ⟨334184, by rfl⟩ : syracuseStep 445579 = 668369) B668369
theorem B1002635 : Blo 443779 1002635 := bstep (se 1 (by rfl) ⟨751976, by rfl⟩ : syracuseStep 1002635 = 1503953) B1503953
theorem B445591 : Blo 443779 445591 := bstep (se 1 (by rfl) ⟨334193, by rfl⟩ : syracuseStep 445591 = 668387) B668387
theorem B445611 : Blo 443779 445611 := bstep (se 1 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 445611 = 668417) B668417
theorem B445623 : Blo 443779 445623 := bstep (se 1 (by rfl) ⟨334217, by rfl⟩ : syracuseStep 445623 = 668435) B668435
theorem B1002689 : Blo 443779 1002689 := bstep (se 2 (by rfl) ⟨376008, by rfl⟩ : syracuseStep 1002689 = 752017) B752017
theorem B445643 : Blo 443779 445643 := bstep (se 1 (by rfl) ⟨334232, by rfl⟩ : syracuseStep 445643 = 668465) B668465
theorem B445655 : Blo 443779 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B445675 : Blo 443779 445675 := bstep (se 1 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 445675 = 668513) B668513
theorem B445687 : Blo 443779 445687 := bstep (se 1 (by rfl) ⟨334265, by rfl⟩ : syracuseStep 445687 = 668531) B668531
theorem B445707 : Blo 443779 445707 := bstep (se 1 (by rfl) ⟨334280, by rfl⟩ : syracuseStep 445707 = 668561) B668561
theorem B445719 : Blo 443779 445719 := bstep (se 1 (by rfl) ⟨334289, by rfl⟩ : syracuseStep 445719 = 668579) B668579
theorem B445739 : Blo 443779 445739 := bstep (se 1 (by rfl) ⟨334304, by rfl⟩ : syracuseStep 445739 = 668609) B668609
theorem B445751 : Blo 443779 445751 := bstep (se 1 (by rfl) ⟨334313, by rfl⟩ : syracuseStep 445751 = 668627) B668627
theorem B2542913 : Blo 443779 2542913 := bstep (se 2 (by rfl) ⟨953592, by rfl⟩ : syracuseStep 2542913 = 1907185) B1907185
theorem B445771 : Blo 443779 445771 := bstep (se 1 (by rfl) ⟨334328, by rfl⟩ : syracuseStep 445771 = 668657) B668657
theorem B445783 : Blo 443779 445783 := bstep (se 1 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 445783 = 668675) B668675
theorem B445803 : Blo 443779 445803 := bstep (se 1 (by rfl) ⟨334352, by rfl⟩ : syracuseStep 445803 = 668705) B668705
theorem B445815 : Blo 443779 445815 := bstep (se 1 (by rfl) ⟨334361, by rfl⟩ : syracuseStep 445815 = 668723) B668723
theorem B3820931 : Blo 443779 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B445835 : Blo 443779 445835 := bstep (se 1 (by rfl) ⟨334376, by rfl⟩ : syracuseStep 445835 = 668753) B668753
theorem B445847 : Blo 443779 445847 := bstep (se 1 (by rfl) ⟨334385, by rfl⟩ : syracuseStep 445847 = 668771) B668771
theorem B1002905 : Blo 443779 1002905 := bstep (se 2 (by rfl) ⟨376089, by rfl⟩ : syracuseStep 1002905 = 752179) B752179
theorem B445867 : Blo 443779 445867 := bstep (se 1 (by rfl) ⟨334400, by rfl⟩ : syracuseStep 445867 = 668801) B668801
theorem B445879 : Blo 443779 445879 := bstep (se 1 (by rfl) ⟨334409, by rfl⟩ : syracuseStep 445879 = 668819) B668819
theorem B445899 : Blo 443779 445899 := bstep (se 1 (by rfl) ⟨334424, by rfl⟩ : syracuseStep 445899 = 668849) B668849
theorem B445911 : Blo 443779 445911 := bstep (se 1 (by rfl) ⟨334433, by rfl⟩ : syracuseStep 445911 = 668867) B668867
theorem B445931 : Blo 443779 445931 := bstep (se 1 (by rfl) ⟨334448, by rfl⟩ : syracuseStep 445931 = 668897) B668897
theorem B1002995 : Blo 443779 1002995 := bstep (se 1 (by rfl) ⟨752246, by rfl⟩ : syracuseStep 1002995 = 1504493) B1504493
theorem B445943 : Blo 443779 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B445963 : Blo 443779 445963 := bstep (se 1 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 445963 = 668945) B668945
theorem B1003031 : Blo 443779 1003031 := bstep (se 1 (by rfl) ⟨752273, by rfl⟩ : syracuseStep 1003031 = 1504547) B1504547
theorem B445975 : Blo 443779 445975 := bstep (se 1 (by rfl) ⟨334481, by rfl⟩ : syracuseStep 445975 = 668963) B668963
theorem B445995 : Blo 443779 445995 := bstep (se 1 (by rfl) ⟨334496, by rfl⟩ : syracuseStep 445995 = 668993) B668993
theorem B446007 : Blo 443779 446007 := bstep (se 1 (by rfl) ⟨334505, by rfl⟩ : syracuseStep 446007 = 669011) B669011
theorem B2707019 : Blo 443779 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B446027 : Blo 443779 446027 := bstep (se 1 (by rfl) ⟨334520, by rfl⟩ : syracuseStep 446027 = 669041) B669041
theorem B446039 : Blo 443779 446039 := bstep (se 1 (by rfl) ⟨334529, by rfl⟩ : syracuseStep 446039 = 669059) B669059
theorem B446059 : Blo 443779 446059 := bstep (se 1 (by rfl) ⟨334544, by rfl⟩ : syracuseStep 446059 = 669089) B669089
theorem B446071 : Blo 443779 446071 := bstep (se 1 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 446071 = 669107) B669107
theorem B446091 : Blo 443779 446091 := bstep (se 1 (by rfl) ⟨334568, by rfl⟩ : syracuseStep 446091 = 669137) B669137
theorem B1199767 : Blo 443779 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B446103 : Blo 443779 446103 := bstep (se 1 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 446103 = 669155) B669155
theorem B446123 : Blo 443779 446123 := bstep (se 1 (by rfl) ⟨334592, by rfl⟩ : syracuseStep 446123 = 669185) B669185
theorem B446135 : Blo 443779 446135 := bstep (se 1 (by rfl) ⟨334601, by rfl⟩ : syracuseStep 446135 = 669203) B669203
theorem B1199809 : Blo 443779 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B1003211 : Blo 443779 1003211 := bstep (se 1 (by rfl) ⟨752408, by rfl⟩ : syracuseStep 1003211 = 1504817) B1504817
theorem B446155 : Blo 443779 446155 := bstep (se 1 (by rfl) ⟨334616, by rfl⟩ : syracuseStep 446155 = 669233) B669233
theorem B446167 : Blo 443779 446167 := bstep (se 1 (by rfl) ⟨334625, by rfl⟩ : syracuseStep 446167 = 669251) B669251
theorem B446187 : Blo 443779 446187 := bstep (se 1 (by rfl) ⟨334640, by rfl⟩ : syracuseStep 446187 = 669281) B669281
theorem B446199 : Blo 443779 446199 := bstep (se 1 (by rfl) ⟨334649, by rfl⟩ : syracuseStep 446199 = 669299) B669299
theorem B1003265 : Blo 443779 1003265 := bstep (se 2 (by rfl) ⟨376224, by rfl⟩ : syracuseStep 1003265 = 752449) B752449
theorem B446219 : Blo 443779 446219 := bstep (se 1 (by rfl) ⟨334664, by rfl⟩ : syracuseStep 446219 = 669329) B669329
theorem B446231 : Blo 443779 446231 := bstep (se 1 (by rfl) ⟨334673, by rfl⟩ : syracuseStep 446231 = 669347) B669347
theorem B446251 : Blo 443779 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B446263 : Blo 443779 446263 := bstep (se 1 (by rfl) ⟨334697, by rfl⟩ : syracuseStep 446263 = 669395) B669395
theorem B446283 : Blo 443779 446283 := bstep (se 1 (by rfl) ⟨334712, by rfl⟩ : syracuseStep 446283 = 669425) B669425
theorem B446295 : Blo 443779 446295 := bstep (se 1 (by rfl) ⟨334721, by rfl⟩ : syracuseStep 446295 = 669443) B669443
theorem B446315 : Blo 443779 446315 := bstep (se 1 (by rfl) ⟨334736, by rfl⟩ : syracuseStep 446315 = 669473) B669473
theorem B446327 : Blo 443779 446327 := bstep (se 1 (by rfl) ⟨334745, by rfl⟩ : syracuseStep 446327 = 669491) B669491
theorem B446347 : Blo 443779 446347 := bstep (se 1 (by rfl) ⟨334760, by rfl⟩ : syracuseStep 446347 = 669521) B669521
theorem B446359 : Blo 443779 446359 := bstep (se 1 (by rfl) ⟨334769, by rfl⟩ : syracuseStep 446359 = 669539) B669539
theorem B806807 : Blo 443779 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B446379 : Blo 443779 446379 := bstep (se 1 (by rfl) ⟨334784, by rfl⟩ : syracuseStep 446379 = 669569) B669569
theorem B1429427 : Blo 443779 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B446391 : Blo 443779 446391 := bstep (se 1 (by rfl) ⟨334793, by rfl⟩ : syracuseStep 446391 = 669587) B669587
theorem B446411 : Blo 443779 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B446423 : Blo 443779 446423 := bstep (se 1 (by rfl) ⟨334817, by rfl⟩ : syracuseStep 446423 = 669635) B669635
theorem B1003481 : Blo 443779 1003481 := bstep (se 2 (by rfl) ⟨376305, by rfl⟩ : syracuseStep 1003481 = 752611) B752611
theorem B905177 : Blo 443779 905177 := bstep (se 2 (by rfl) ⟨339441, by rfl⟩ : syracuseStep 905177 = 678883) B678883
theorem B446443 : Blo 443779 446443 := bstep (se 1 (by rfl) ⟨334832, by rfl⟩ : syracuseStep 446443 = 669665) B669665
theorem B446455 : Blo 443779 446455 := bstep (se 1 (by rfl) ⟨334841, by rfl⟩ : syracuseStep 446455 = 669683) B669683
theorem B446475 : Blo 443779 446475 := bstep (se 1 (by rfl) ⟨334856, by rfl⟩ : syracuseStep 446475 = 669713) B669713
theorem B2248721 : Blo 443779 2248721 := bstep (se 2 (by rfl) ⟨843270, by rfl⟩ : syracuseStep 2248721 = 1686541) B1686541
theorem B446487 : Blo 443779 446487 := bstep (se 1 (by rfl) ⟨334865, by rfl⟩ : syracuseStep 446487 = 669731) B669731
theorem B446507 : Blo 443779 446507 := bstep (se 1 (by rfl) ⟨334880, by rfl⟩ : syracuseStep 446507 = 669761) B669761
theorem B1003571 : Blo 443779 1003571 := bstep (se 1 (by rfl) ⟨752678, by rfl⟩ : syracuseStep 1003571 = 1505357) B1505357
theorem B446519 : Blo 443779 446519 := bstep (se 1 (by rfl) ⟨334889, by rfl⟩ : syracuseStep 446519 = 669779) B669779
theorem B446539 : Blo 443779 446539 := bstep (se 1 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 446539 = 669809) B669809
theorem B1003607 : Blo 443779 1003607 := bstep (se 1 (by rfl) ⟨752705, by rfl⟩ : syracuseStep 1003607 = 1505411) B1505411
theorem B446551 : Blo 443779 446551 := bstep (se 1 (by rfl) ⟨334913, by rfl⟩ : syracuseStep 446551 = 669827) B669827
theorem B446571 : Blo 443779 446571 := bstep (se 1 (by rfl) ⟨334928, by rfl⟩ : syracuseStep 446571 = 669857) B669857
theorem B446583 : Blo 443779 446583 := bstep (se 1 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 446583 = 669875) B669875
theorem B446603 : Blo 443779 446603 := bstep (se 1 (by rfl) ⟨334952, by rfl⟩ : syracuseStep 446603 = 669905) B669905
theorem B446615 : Blo 443779 446615 := bstep (se 1 (by rfl) ⟨334961, by rfl⟩ : syracuseStep 446615 = 669923) B669923
theorem B446635 : Blo 443779 446635 := bstep (se 1 (by rfl) ⟨334976, by rfl⟩ : syracuseStep 446635 = 669953) B669953
theorem B2248883 : Blo 443779 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B446647 : Blo 443779 446647 := bstep (se 1 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 446647 = 669971) B669971
theorem B446667 : Blo 443779 446667 := bstep (se 1 (by rfl) ⟨335000, by rfl⟩ : syracuseStep 446667 = 670001) B670001
theorem B446679 : Blo 443779 446679 := bstep (se 1 (by rfl) ⟨335009, by rfl⟩ : syracuseStep 446679 = 670019) B670019
theorem B446699 : Blo 443779 446699 := bstep (se 1 (by rfl) ⟨335024, by rfl⟩ : syracuseStep 446699 = 670049) B670049
theorem B446711 : Blo 443779 446711 := bstep (se 1 (by rfl) ⟨335033, by rfl⟩ : syracuseStep 446711 = 670067) B670067
theorem B4837637 : Blo 443779 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B1003787 : Blo 443779 1003787 := bstep (se 1 (by rfl) ⟨752840, by rfl⟩ : syracuseStep 1003787 = 1505681) B1505681
theorem B446731 : Blo 443779 446731 := bstep (se 1 (by rfl) ⟨335048, by rfl⟩ : syracuseStep 446731 = 670097) B670097
theorem B446743 : Blo 443779 446743 := bstep (se 1 (by rfl) ⟨335057, by rfl⟩ : syracuseStep 446743 = 670115) B670115
theorem B446763 : Blo 443779 446763 := bstep (se 1 (by rfl) ⟨335072, by rfl⟩ : syracuseStep 446763 = 670145) B670145
theorem B446775 : Blo 443779 446775 := bstep (se 1 (by rfl) ⟨335081, by rfl⟩ : syracuseStep 446775 = 670163) B670163
theorem B1003841 : Blo 443779 1003841 := bstep (se 2 (by rfl) ⟨376440, by rfl⟩ : syracuseStep 1003841 = 752881) B752881
theorem B446795 : Blo 443779 446795 := bstep (se 1 (by rfl) ⟨335096, by rfl⟩ : syracuseStep 446795 = 670193) B670193
theorem B446807 : Blo 443779 446807 := bstep (se 1 (by rfl) ⟨335105, by rfl⟩ : syracuseStep 446807 = 670211) B670211
theorem B446827 : Blo 443779 446827 := bstep (se 1 (by rfl) ⟨335120, by rfl⟩ : syracuseStep 446827 = 670241) B670241
theorem B446839 : Blo 443779 446839 := bstep (se 1 (by rfl) ⟨335129, by rfl⟩ : syracuseStep 446839 = 670259) B670259
theorem B446859 : Blo 443779 446859 := bstep (se 1 (by rfl) ⟨335144, by rfl⟩ : syracuseStep 446859 = 670289) B670289
theorem B905623 : Blo 443779 905623 := bstep (se 1 (by rfl) ⟨679217, by rfl⟩ : syracuseStep 905623 = 1358435) B1358435
theorem B446871 : Blo 443779 446871 := bstep (se 1 (by rfl) ⟨335153, by rfl⟩ : syracuseStep 446871 = 670307) B670307
theorem B446891 : Blo 443779 446891 := bstep (se 1 (by rfl) ⟨335168, by rfl⟩ : syracuseStep 446891 = 670337) B670337
theorem B446903 : Blo 443779 446903 := bstep (se 1 (by rfl) ⟨335177, by rfl⟩ : syracuseStep 446903 = 670355) B670355
theorem B643531 : Blo 443779 643531 := bstep (se 1 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 643531 = 965297) B965297
theorem B446923 : Blo 443779 446923 := bstep (se 1 (by rfl) ⟨335192, by rfl⟩ : syracuseStep 446923 = 670385) B670385
theorem B446935 : Blo 443779 446935 := bstep (se 1 (by rfl) ⟨335201, by rfl⟩ : syracuseStep 446935 = 670403) B670403
theorem B4805081 : Blo 443779 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B1266137 : Blo 443779 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B446955 : Blo 443779 446955 := bstep (se 1 (by rfl) ⟨335216, by rfl⟩ : syracuseStep 446955 = 670433) B670433
theorem B446967 : Blo 443779 446967 := bstep (se 1 (by rfl) ⟨335225, by rfl⟩ : syracuseStep 446967 = 670451) B670451
theorem B446987 : Blo 443779 446987 := bstep (se 1 (by rfl) ⟨335240, by rfl⟩ : syracuseStep 446987 = 670481) B670481
theorem B446999 : Blo 443779 446999 := bstep (se 1 (by rfl) ⟨335249, by rfl⟩ : syracuseStep 446999 = 670499) B670499
theorem B1004057 : Blo 443779 1004057 := bstep (se 2 (by rfl) ⟨376521, by rfl⟩ : syracuseStep 1004057 = 753043) B753043
theorem B447019 : Blo 443779 447019 := bstep (se 1 (by rfl) ⟨335264, by rfl⟩ : syracuseStep 447019 = 670529) B670529
theorem B447031 : Blo 443779 447031 := bstep (se 1 (by rfl) ⟨335273, by rfl⟩ : syracuseStep 447031 = 670547) B670547
theorem B447051 : Blo 443779 447051 := bstep (se 1 (by rfl) ⟨335288, by rfl⟩ : syracuseStep 447051 = 670577) B670577
theorem B447063 : Blo 443779 447063 := bstep (se 1 (by rfl) ⟨335297, by rfl⟩ : syracuseStep 447063 = 670595) B670595
theorem B447083 : Blo 443779 447083 := bstep (se 1 (by rfl) ⟨335312, by rfl⟩ : syracuseStep 447083 = 670625) B670625
theorem B1004147 : Blo 443779 1004147 := bstep (se 1 (by rfl) ⟨753110, by rfl⟩ : syracuseStep 1004147 = 1506221) B1506221
theorem B447095 : Blo 443779 447095 := bstep (se 1 (by rfl) ⟨335321, by rfl⟩ : syracuseStep 447095 = 670643) B670643
theorem B447115 : Blo 443779 447115 := bstep (se 1 (by rfl) ⟨335336, by rfl⟩ : syracuseStep 447115 = 670673) B670673
theorem B1004183 : Blo 443779 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B447127 : Blo 443779 447127 := bstep (se 1 (by rfl) ⟨335345, by rfl⟩ : syracuseStep 447127 = 670691) B670691
theorem B447147 : Blo 443779 447147 := bstep (se 1 (by rfl) ⟨335360, by rfl⟩ : syracuseStep 447147 = 670721) B670721
theorem B447159 : Blo 443779 447159 := bstep (se 1 (by rfl) ⟨335369, by rfl⟩ : syracuseStep 447159 = 670739) B670739
theorem B447179 : Blo 443779 447179 := bstep (se 1 (by rfl) ⟨335384, by rfl⟩ : syracuseStep 447179 = 670769) B670769
theorem B447191 : Blo 443779 447191 := bstep (se 1 (by rfl) ⟨335393, by rfl⟩ : syracuseStep 447191 = 670787) B670787
theorem B447211 : Blo 443779 447211 := bstep (se 1 (by rfl) ⟨335408, by rfl⟩ : syracuseStep 447211 = 670817) B670817
theorem B447223 : Blo 443779 447223 := bstep (se 1 (by rfl) ⟨335417, by rfl⟩ : syracuseStep 447223 = 670835) B670835
theorem B447243 : Blo 443779 447243 := bstep (se 1 (by rfl) ⟨335432, by rfl⟩ : syracuseStep 447243 = 670865) B670865
theorem B1266455 : Blo 443779 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B447255 : Blo 443779 447255 := bstep (se 1 (by rfl) ⟨335441, by rfl⟩ : syracuseStep 447255 = 670883) B670883
theorem B447275 : Blo 443779 447275 := bstep (se 1 (by rfl) ⟨335456, by rfl⟩ : syracuseStep 447275 = 670913) B670913
theorem B447287 : Blo 443779 447287 := bstep (se 1 (by rfl) ⟨335465, by rfl⟩ : syracuseStep 447287 = 670931) B670931
theorem B1004363 : Blo 443779 1004363 := bstep (se 1 (by rfl) ⟨753272, by rfl⟩ : syracuseStep 1004363 = 1506545) B1506545
theorem B447307 : Blo 443779 447307 := bstep (se 1 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 447307 = 670961) B670961
theorem B447319 : Blo 443779 447319 := bstep (se 1 (by rfl) ⟨335489, by rfl⟩ : syracuseStep 447319 = 670979) B670979
theorem B447339 : Blo 443779 447339 := bstep (se 1 (by rfl) ⟨335504, by rfl⟩ : syracuseStep 447339 = 671009) B671009
theorem B447351 : Blo 443779 447351 := bstep (se 1 (by rfl) ⟨335513, by rfl⟩ : syracuseStep 447351 = 671027) B671027
theorem B1004417 : Blo 443779 1004417 := bstep (se 2 (by rfl) ⟨376656, by rfl⟩ : syracuseStep 1004417 = 753313) B753313
theorem B447371 : Blo 443779 447371 := bstep (se 1 (by rfl) ⟨335528, by rfl⟩ : syracuseStep 447371 = 671057) B671057
theorem B447383 : Blo 443779 447383 := bstep (se 1 (by rfl) ⟨335537, by rfl⟩ : syracuseStep 447383 = 671075) B671075
theorem B447403 : Blo 443779 447403 := bstep (se 1 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 447403 = 671105) B671105
theorem B2053043 : Blo 443779 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B447415 : Blo 443779 447415 := bstep (se 1 (by rfl) ⟨335561, by rfl⟩ : syracuseStep 447415 = 671123) B671123
theorem B447435 : Blo 443779 447435 := bstep (se 1 (by rfl) ⟨335576, by rfl⟩ : syracuseStep 447435 = 671153) B671153
theorem B447447 : Blo 443779 447447 := bstep (se 1 (by rfl) ⟨335585, by rfl⟩ : syracuseStep 447447 = 671171) B671171
theorem B447467 : Blo 443779 447467 := bstep (se 1 (by rfl) ⟨335600, by rfl⟩ : syracuseStep 447467 = 671201) B671201
theorem B447479 : Blo 443779 447479 := bstep (se 1 (by rfl) ⟨335609, by rfl⟩ : syracuseStep 447479 = 671219) B671219
theorem B447499 : Blo 443779 447499 := bstep (se 1 (by rfl) ⟨335624, by rfl⟩ : syracuseStep 447499 = 671249) B671249
theorem B447511 : Blo 443779 447511 := bstep (se 1 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 447511 = 671267) B671267
theorem B447531 : Blo 443779 447531 := bstep (se 1 (by rfl) ⟨335648, by rfl⟩ : syracuseStep 447531 = 671297) B671297
theorem B3396653 : Blo 443779 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B447543 : Blo 443779 447543 := bstep (se 1 (by rfl) ⟨335657, by rfl⟩ : syracuseStep 447543 = 671315) B671315
theorem B447563 : Blo 443779 447563 := bstep (se 1 (by rfl) ⟨335672, by rfl⟩ : syracuseStep 447563 = 671345) B671345
theorem B447575 : Blo 443779 447575 := bstep (se 1 (by rfl) ⟨335681, by rfl⟩ : syracuseStep 447575 = 671363) B671363
theorem B1004633 : Blo 443779 1004633 := bstep (se 2 (by rfl) ⟨376737, by rfl⟩ : syracuseStep 1004633 = 753475) B753475
theorem B447595 : Blo 443779 447595 := bstep (se 1 (by rfl) ⟨335696, by rfl⟩ : syracuseStep 447595 = 671393) B671393
theorem B447607 : Blo 443779 447607 := bstep (se 1 (by rfl) ⟨335705, by rfl⟩ : syracuseStep 447607 = 671411) B671411
theorem B447627 : Blo 443779 447627 := bstep (se 1 (by rfl) ⟨335720, by rfl⟩ : syracuseStep 447627 = 671441) B671441
theorem B447639 : Blo 443779 447639 := bstep (se 1 (by rfl) ⟨335729, by rfl⟩ : syracuseStep 447639 = 671459) B671459
theorem B447659 : Blo 443779 447659 := bstep (se 1 (by rfl) ⟨335744, by rfl⟩ : syracuseStep 447659 = 671489) B671489
theorem B1692845 : Blo 443779 1692845 := bstep (se 3 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 1692845 = 634817) B634817
theorem B1004723 : Blo 443779 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B447671 : Blo 443779 447671 := bstep (se 1 (by rfl) ⟨335753, by rfl⟩ : syracuseStep 447671 = 671507) B671507
theorem B447691 : Blo 443779 447691 := bstep (se 1 (by rfl) ⟨335768, by rfl⟩ : syracuseStep 447691 = 671537) B671537
theorem B1004759 : Blo 443779 1004759 := bstep (se 1 (by rfl) ⟨753569, by rfl⟩ : syracuseStep 1004759 = 1507139) B1507139
theorem B447703 : Blo 443779 447703 := bstep (se 1 (by rfl) ⟨335777, by rfl⟩ : syracuseStep 447703 = 671555) B671555
theorem B447723 : Blo 443779 447723 := bstep (se 1 (by rfl) ⟨335792, by rfl⟩ : syracuseStep 447723 = 671585) B671585
theorem B447735 : Blo 443779 447735 := bstep (se 1 (by rfl) ⟨335801, by rfl⟩ : syracuseStep 447735 = 671603) B671603
theorem B447755 : Blo 443779 447755 := bstep (se 1 (by rfl) ⟨335816, by rfl⟩ : syracuseStep 447755 = 671633) B671633
theorem B447767 : Blo 443779 447767 := bstep (se 1 (by rfl) ⟨335825, by rfl⟩ : syracuseStep 447767 = 671651) B671651
theorem B3429697 : Blo 443779 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B1004939 : Blo 443779 1004939 := bstep (se 1 (by rfl) ⟨753704, by rfl⟩ : syracuseStep 1004939 = 1507409) B1507409
theorem B1004993 : Blo 443779 1004993 := bstep (se 2 (by rfl) ⟨376872, by rfl⟩ : syracuseStep 1004993 = 753745) B753745
theorem B1201625 : Blo 443779 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B1267265 : Blo 443779 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B2545303 : Blo 443779 2545303 := bstep (se 1 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 2545303 = 3817955) B3817955
theorem B611993 : Blo 443779 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B1005209 : Blo 443779 1005209 := bstep (se 2 (by rfl) ⟨376953, by rfl⟩ : syracuseStep 1005209 = 753907) B753907
theorem B1005299 : Blo 443779 1005299 := bstep (se 1 (by rfl) ⟨753974, by rfl⟩ : syracuseStep 1005299 = 1507949) B1507949
theorem B1005335 : Blo 443779 1005335 := bstep (se 1 (by rfl) ⟨754001, by rfl⟩ : syracuseStep 1005335 = 1508003) B1508003
theorem B1300313 : Blo 443779 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B1693619 : Blo 443779 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B1005515 : Blo 443779 1005515 := bstep (se 1 (by rfl) ⟨754136, by rfl⟩ : syracuseStep 1005515 = 1508273) B1508273
theorem B645067 : Blo 443779 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B1005569 : Blo 443779 1005569 := bstep (se 2 (by rfl) ⟨377088, by rfl⟩ : syracuseStep 1005569 = 754177) B754177
theorem B2250827 : Blo 443779 2250827 := bstep (se 1 (by rfl) ⟨1688120, by rfl⟩ : syracuseStep 2250827 = 3376241) B3376241
theorem B1005785 : Blo 443779 1005785 := bstep (se 2 (by rfl) ⟨377169, by rfl⟩ : syracuseStep 1005785 = 754339) B754339
theorem B1005875 : Blo 443779 1005875 := bstep (se 1 (by rfl) ⟨754406, by rfl⟩ : syracuseStep 1005875 = 1508813) B1508813
theorem B1005911 : Blo 443779 1005911 := bstep (se 1 (by rfl) ⟨754433, by rfl⟩ : syracuseStep 1005911 = 1508867) B1508867
theorem B1006091 : Blo 443779 1006091 := bstep (se 1 (by rfl) ⟨754568, by rfl⟩ : syracuseStep 1006091 = 1509137) B1509137
theorem B645655 : Blo 443779 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B1006145 : Blo 443779 1006145 := bstep (se 2 (by rfl) ⟨377304, by rfl⟩ : syracuseStep 1006145 = 754609) B754609
theorem B1006361 : Blo 443779 1006361 := bstep (se 2 (by rfl) ⟨377385, by rfl⟩ : syracuseStep 1006361 = 754771) B754771
theorem B1006451 : Blo 443779 1006451 := bstep (se 1 (by rfl) ⟨754838, by rfl⟩ : syracuseStep 1006451 = 1509677) B1509677
theorem B2907011 : Blo 443779 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B711575 : Blo 443779 711575 := bstep (se 1 (by rfl) ⟨533681, by rfl⟩ : syracuseStep 711575 = 1067363) B1067363
theorem B1006487 : Blo 443779 1006487 := bstep (se 1 (by rfl) ⟨754865, by rfl⟩ : syracuseStep 1006487 = 1509731) B1509731
theorem B1006667 : Blo 443779 1006667 := bstep (se 1 (by rfl) ⟨755000, by rfl⟩ : syracuseStep 1006667 = 1510001) B1510001
theorem B1236061 : Blo 443779 1236061 := bstep (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) B463523
theorem B1006721 : Blo 443779 1006721 := bstep (se 2 (by rfl) ⟨377520, by rfl⟩ : syracuseStep 1006721 = 755041) B755041
theorem B1268939 : Blo 443779 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B744665 : Blo 443779 744665 := bstep (se 2 (by rfl) ⟨279249, by rfl⟩ : syracuseStep 744665 = 558499) B558499
theorem B1498391 : Blo 443779 1498391 := bstep (se 1 (by rfl) ⟨1123793, by rfl⟩ : syracuseStep 1498391 = 2247587) B2247587
theorem B1006937 : Blo 443779 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B1695107 : Blo 443779 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B1007027 : Blo 443779 1007027 := bstep (se 1 (by rfl) ⟨755270, by rfl⟩ : syracuseStep 1007027 = 1510541) B1510541
theorem B1007063 : Blo 443779 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B5693003 : Blo 443779 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B1007243 : Blo 443779 1007243 := bstep (se 1 (by rfl) ⟨755432, by rfl⟩ : syracuseStep 1007243 = 1510865) B1510865
theorem B1007297 : Blo 443779 1007297 := bstep (se 2 (by rfl) ⟨377736, by rfl⟩ : syracuseStep 1007297 = 755473) B755473
theorem B1498931 : Blo 443779 1498931 := bstep (se 1 (by rfl) ⟨1124198, by rfl⟩ : syracuseStep 1498931 = 2248397) B2248397
theorem B2252609 : Blo 443779 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B1695563 : Blo 443779 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B712535 : Blo 443779 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B8576867 : Blo 443779 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B843635 : Blo 443779 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B712651 : Blo 443779 712651 := bstep (se 1 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 712651 = 1068977) B1068977
theorem B843787 : Blo 443779 843787 := bstep (se 1 (by rfl) ⟨632840, by rfl⟩ : syracuseStep 843787 = 1265681) B1265681
theorem B1695761 : Blo 443779 1695761 := bstep (se 2 (by rfl) ⟨635910, by rfl⟩ : syracuseStep 1695761 = 1271821) B1271821
theorem B1499201 : Blo 443779 1499201 := bstep (se 2 (by rfl) ⟨562200, by rfl⟩ : syracuseStep 1499201 = 1124401) B1124401
theorem B5070923 : Blo 443779 5070923 := bstep (se 1 (by rfl) ⟨3803192, by rfl⟩ : syracuseStep 5070923 = 7606385) B7606385
theorem B8151191 : Blo 443779 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B844121 : Blo 443779 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B5497267 : Blo 443779 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B1270237 : Blo 443779 1270237 := bstep (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) B476339
theorem B1499741 : Blo 443779 1499741 := bstep (se 3 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 1499741 = 562403) B562403
theorem B713369 : Blo 443779 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B451255 : Blo 443779 451255 := bstep (se 1 (by rfl) ⟨338441, by rfl⟩ : syracuseStep 451255 = 676883) B676883
theorem B3793625 : Blo 443779 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B3629785 : Blo 443779 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B1696535 : Blo 443779 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B1270579 : Blo 443779 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B2581379 : Blo 443779 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B10281907 : Blo 443779 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B844759 : Blo 443779 844759 := bstep (se 1 (by rfl) ⟨633569, by rfl⟩ : syracuseStep 844759 = 1267139) B1267139
theorem B1696733 : Blo 443779 1696733 := bstep (se 3 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 1696733 = 636275) B636275
theorem B3204161 : Blo 443779 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B713881 : Blo 443779 713881 := bstep (se 2 (by rfl) ⟨267705, by rfl⟩ : syracuseStep 713881 = 535411) B535411
theorem B1074455 : Blo 443779 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B3433859 : Blo 443779 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B2287121 : Blo 443779 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B1500875 : Blo 443779 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B2254553 : Blo 443779 2254553 := bstep (se 2 (by rfl) ⟨845457, by rfl⟩ : syracuseStep 2254553 = 1690915) B1690915
theorem B1271513 : Blo 443779 1271513 := bstep (se 2 (by rfl) ⟨476817, by rfl⟩ : syracuseStep 1271513 = 953635) B953635
theorem B845579 : Blo 443779 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B845633 : Blo 443779 845633 := bstep (se 2 (by rfl) ⟨317112, by rfl⟩ : syracuseStep 845633 = 634225) B634225
theorem B1501145 : Blo 443779 1501145 := bstep (se 2 (by rfl) ⟨562929, by rfl⟩ : syracuseStep 1501145 = 1125859) B1125859
theorem B813235 : Blo 443779 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B2615513 : Blo 443779 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B2713949 : Blo 443779 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B1501847 : Blo 443779 1501847 := bstep (se 1 (by rfl) ⟨1126385, by rfl⟩ : syracuseStep 1501847 = 2252771) B2252771
theorem B1141427 : Blo 443779 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B846551 : Blo 443779 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B1305305 : Blo 443779 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B453367 : Blo 443779 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B1698691 : Blo 443779 1698691 := bstep (se 1 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 1698691 = 2548037) B2548037
theorem B3042379 : Blo 443779 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B1272925 : Blo 443779 1272925 := bstep (se 3 (by rfl) ⟨238673, by rfl⟩ : syracuseStep 1272925 = 477347) B477347
theorem B1502387 : Blo 443779 1502387 := bstep (se 1 (by rfl) ⟨1126790, by rfl⟩ : syracuseStep 1502387 = 2253581) B2253581
theorem B1698995 : Blo 443779 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B847091 : Blo 443779 847091 := bstep (se 1 (by rfl) ⟨635318, by rfl⟩ : syracuseStep 847091 = 1270637) B1270637
theorem B2256173 : Blo 443779 2256173 := bstep (se 3 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 2256173 = 846065) B846065
theorem B1273153 : Blo 443779 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B748939 : Blo 443779 748939 := bstep (se 1 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 748939 = 1123409) B1123409
theorem B1207703 : Blo 443779 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B1502657 : Blo 443779 1502657 := bstep (se 2 (by rfl) ⟨563496, by rfl⟩ : syracuseStep 1502657 = 1126993) B1126993
theorem B749081 : Blo 443779 749081 := bstep (se 2 (by rfl) ⟨280905, by rfl⟩ : syracuseStep 749081 = 561811) B561811
theorem B7597637 : Blo 443779 7597637 := bstep (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) B1424557
theorem B1601117 : Blo 443779 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B1273495 : Blo 443779 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B749209 : Blo 443779 749209 := bstep (se 2 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 749209 = 561907) B561907
theorem B847577 : Blo 443779 847577 := bstep (se 2 (by rfl) ⟨317841, by rfl⟩ : syracuseStep 847577 = 635683) B635683
theorem B1699649 : Blo 443779 1699649 := bstep (se 2 (by rfl) ⟨637368, by rfl⟩ : syracuseStep 1699649 = 1274737) B1274737
theorem B1503197 : Blo 443779 1503197 := bstep (se 3 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 1503197 = 563699) B563699
theorem B815243 : Blo 443779 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B749783 : Blo 443779 749783 := bstep (se 1 (by rfl) ⟨562337, by rfl⟩ : syracuseStep 749783 = 1124675) B1124675
theorem B749911 : Blo 443779 749911 := bstep (se 1 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 749911 = 1124867) B1124867
theorem B1274201 : Blo 443779 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1896797 : Blo 443779 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B815959 : Blo 443779 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B750539 : Blo 443779 750539 := bstep (se 1 (by rfl) ⟨562904, by rfl⟩ : syracuseStep 750539 = 1125809) B1125809
theorem B750667 : Blo 443779 750667 := bstep (se 1 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 750667 = 1126001) B1126001
theorem B1504331 : Blo 443779 1504331 := bstep (se 1 (by rfl) ⟨1128248, by rfl⟩ : syracuseStep 1504331 = 2256497) B2256497
theorem B849035 : Blo 443779 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B750809 : Blo 443779 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B3372353 : Blo 443779 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B849217 : Blo 443779 849217 := bstep (se 2 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 849217 = 636913) B636913
theorem B750937 : Blo 443779 750937 := bstep (se 2 (by rfl) ⟨281601, by rfl⟩ : syracuseStep 750937 = 563203) B563203
theorem B1504601 : Blo 443779 1504601 := bstep (se 2 (by rfl) ⟨564225, by rfl⟩ : syracuseStep 1504601 = 1128451) B1128451
theorem B1144343 : Blo 443779 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B849665 : Blo 443779 849665 := bstep (se 2 (by rfl) ⟨318624, by rfl⟩ : syracuseStep 849665 = 637249) B637249
theorem B751511 : Blo 443779 751511 := bstep (se 1 (by rfl) ⟨563633, by rfl⟩ : syracuseStep 751511 = 1127267) B1127267
theorem B5732369 : Blo 443779 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B751639 : Blo 443779 751639 := bstep (se 1 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 751639 = 1127459) B1127459
theorem B1505303 : Blo 443779 1505303 := bstep (se 1 (by rfl) ⟨1128977, by rfl⟩ : syracuseStep 1505303 = 2257955) B2257955
theorem B850007 : Blo 443779 850007 := bstep (se 1 (by rfl) ⟨637505, by rfl⟩ : syracuseStep 850007 = 1275011) B1275011
theorem B1013963 : Blo 443779 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B817561 : Blo 443779 817561 := bstep (se 2 (by rfl) ⟨306585, by rfl⟩ : syracuseStep 817561 = 613171) B613171
theorem B1505843 : Blo 443779 1505843 := bstep (se 1 (by rfl) ⟨1129382, by rfl⟩ : syracuseStep 1505843 = 2258765) B2258765
theorem B4651613 : Blo 443779 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B948851 : Blo 443779 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B1014401 : Blo 443779 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B752267 : Blo 443779 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B457367 : Blo 443779 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B948953 : Blo 443779 948953 := bstep (se 2 (by rfl) ⟨355857, by rfl⟩ : syracuseStep 948953 = 711715) B711715
theorem B752395 : Blo 443779 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B1506113 : Blo 443779 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B1899395 : Blo 443779 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B752537 : Blo 443779 752537 := bstep (se 2 (by rfl) ⟨282201, by rfl⟩ : syracuseStep 752537 = 564403) B564403
theorem B1375255 : Blo 443779 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B752665 : Blo 443779 752665 := bstep (se 2 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 752665 = 564499) B564499
theorem B12155939 : Blo 443779 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B949313 : Blo 443779 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B2260061 : Blo 443779 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B7699637 : Blo 443779 7699637 := bstep (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) B721841
theorem B3374297 : Blo 443779 3374297 := bstep (se 2 (by rfl) ⟨1265361, by rfl⟩ : syracuseStep 3374297 = 2530723) B2530723
theorem B1015105 : Blo 443779 1015105 := bstep (se 2 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 1015105 = 761329) B761329
theorem B1801565 : Blo 443779 1801565 := bstep (se 3 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 1801565 = 675587) B675587
theorem B1506653 : Blo 443779 1506653 := bstep (se 3 (by rfl) ⟨282497, by rfl⟩ : syracuseStep 1506653 = 564995) B564995
theorem B753239 : Blo 443779 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B753367 : Blo 443779 753367 := bstep (se 1 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 753367 = 1130051) B1130051
theorem B950039 : Blo 443779 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B2850653 : Blo 443779 2850653 := bstep (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) B1068995
theorem B18087857 : Blo 443779 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B1015769 : Blo 443779 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B753799 : Blo 443779 753799 := bstep (se 1 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 753799 = 1130699) B1130699
theorem B3047939 : Blo 443779 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B6423083 : Blo 443779 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B5079671 : Blo 443779 5079671 := bstep (se 1 (by rfl) ⟨3809753, by rfl⟩ : syracuseStep 5079671 = 7619507) B7619507
theorem B1508111 : Blo 443779 1508111 := bstep (se 1 (by rfl) ⟨1131083, by rfl⟩ : syracuseStep 1508111 = 2262167) B2262167
theorem B754447 : Blo 443779 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B951311 : Blo 443779 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B1508381 : Blo 443779 1508381 := bstep (se 3 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 1508381 = 565643) B565643
theorem B3245143 : Blo 443779 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B754987 : Blo 443779 754987 := bstep (se 1 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 754987 = 1132481) B1132481
theorem B2852243 : Blo 443779 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B755129 : Blo 443779 755129 := bstep (se 2 (by rfl) ⟨283173, by rfl⟩ : syracuseStep 755129 = 566347) B566347
theorem B951841 : Blo 443779 951841 := bstep (se 2 (by rfl) ⟨356940, by rfl⟩ : syracuseStep 951841 = 713881) B713881
theorem B3377213 : Blo 443779 3377213 := bstep (se 3 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 3377213 = 1266455) B1266455
theorem B10815605 : Blo 443779 10815605 := bstep (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) B1013963
theorem B5507345 : Blo 443779 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B1804679 : Blo 443779 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B1509785 : Blo 443779 1509785 := bstep (se 2 (by rfl) ⟨566169, by rfl⟩ : syracuseStep 1509785 = 1132339) B1132339
theorem B1084313 : Blo 443779 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B1510487 : Blo 443779 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B2264435 : Blo 443779 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B1904057 : Blo 443779 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B1510973 : Blo 443779 1510973 := bstep (se 3 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 1510973 = 566615) B566615
theorem B8261297 : Blo 443779 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B855841 : Blo 443779 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B2264921 : Blo 443779 2264921 := bstep (se 2 (by rfl) ⟨849345, by rfl⟩ : syracuseStep 2264921 = 1698691) B1698691
theorem B6098989 : Blo 443779 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B1938007 : Blo 443779 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B11539381 : Blo 443779 11539381 := bstep (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) B1081817
theorem B2069761 : Blo 443779 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B3380615 : Blo 443779 3380615 := bstep (se 1 (by rfl) ⟨2535461, by rfl⟩ : syracuseStep 3380615 = 5070923) B5070923
theorem B16226021 : Blo 443779 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B2529083 : Blo 443779 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B858041 : Blo 443779 858041 := bstep (se 2 (by rfl) ⟨321765, by rfl⟩ : syracuseStep 858041 = 643531) B643531
theorem B2136107 : Blo 443779 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B1251389 : Blo 443779 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B8591629 : Blo 443779 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B9181505 : Blo 443779 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B1317235 : Blo 443779 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B563755 : Blo 443779 563755 := bstep (se 1 (by rfl) ⟨422816, by rfl⟩ : syracuseStep 563755 = 845633) B845633
theorem B1448567 : Blo 443779 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B1809299 : Blo 443779 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1219645 : Blo 443779 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B760951 : Blo 443779 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B3808457 : Blo 443779 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B2530541 : Blo 443779 2530541 := bstep (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) B948953
theorem B564727 : Blo 443779 564727 := bstep (se 1 (by rfl) ⟨423545, by rfl⟩ : syracuseStep 564727 = 847091) B847091
theorem B499387 : Blo 443779 499387 := bstep (se 1 (by rfl) ⟨374540, by rfl⟩ : syracuseStep 499387 = 749081) B749081
theorem B565051 : Blo 443779 565051 := bstep (se 1 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 565051 = 847577) B847577
theorem B499855 : Blo 443779 499855 := bstep (se 1 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 499855 = 749783) B749783
theorem B1090081 : Blo 443779 1090081 := bstep (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) B817561
theorem B500359 : Blo 443779 500359 := bstep (se 1 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 500359 = 750539) B750539
theorem B860873 : Blo 443779 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B566023 : Blo 443779 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B500539 : Blo 443779 500539 := bstep (se 1 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 500539 = 750809) B750809
theorem B762895 : Blo 443779 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B566443 : Blo 443779 566443 := bstep (se 1 (by rfl) ⟨424832, by rfl⟩ : syracuseStep 566443 = 849665) B849665
theorem B632009 : Blo 443779 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B501007 : Blo 443779 501007 := bstep (se 1 (by rfl) ⟨375755, by rfl⟩ : syracuseStep 501007 = 751511) B751511
theorem B1123703 : Blo 443779 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B566671 : Blo 443779 566671 := bstep (se 1 (by rfl) ⟨425003, by rfl⟩ : syracuseStep 566671 = 850007) B850007
theorem B1648081 : Blo 443779 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B1812169 : Blo 443779 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B632567 : Blo 443779 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B1353473 : Blo 443779 1353473 := bstep (se 2 (by rfl) ⟨507552, by rfl⟩ : syracuseStep 1353473 = 1015105) B1015105
theorem B501511 : Blo 443779 501511 := bstep (se 1 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 501511 = 752267) B752267
theorem B3811121 : Blo 443779 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B501691 : Blo 443779 501691 := bstep (se 1 (by rfl) ⟨376268, by rfl⟩ : syracuseStep 501691 = 752537) B752537
theorem B8103959 : Blo 443779 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B632875 : Blo 443779 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B665735 : Blo 443779 665735 := bstep (se 1 (by rfl) ⟨499301, by rfl⟩ : syracuseStep 665735 = 998603) B998603
theorem B665771 : Blo 443779 665771 := bstep (se 1 (by rfl) ⟨499328, by rfl⟩ : syracuseStep 665771 = 998657) B998657
theorem B665801 : Blo 443779 665801 := bstep (se 2 (by rfl) ⟨249675, by rfl⟩ : syracuseStep 665801 = 499351) B499351
theorem B665915 : Blo 443779 665915 := bstep (se 1 (by rfl) ⟨499436, by rfl⟩ : syracuseStep 665915 = 998873) B998873
theorem B665975 : Blo 443779 665975 := bstep (se 1 (by rfl) ⟨499481, by rfl⟩ : syracuseStep 665975 = 998963) B998963
theorem B665999 : Blo 443779 665999 := bstep (se 1 (by rfl) ⟨499499, by rfl⟩ : syracuseStep 665999 = 998999) B998999
theorem B502159 : Blo 443779 502159 := bstep (se 1 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 502159 = 753239) B753239
theorem B666041 : Blo 443779 666041 := bstep (se 2 (by rfl) ⟨249765, by rfl⟩ : syracuseStep 666041 = 499531) B499531
theorem B3811805 : Blo 443779 3811805 := bstep (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) B1429427
theorem B666119 : Blo 443779 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B633359 : Blo 443779 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B666155 : Blo 443779 666155 := bstep (se 1 (by rfl) ⟨499616, by rfl⟩ : syracuseStep 666155 = 999233) B999233
theorem B666185 : Blo 443779 666185 := bstep (se 2 (by rfl) ⟨249819, by rfl⟩ : syracuseStep 666185 = 499639) B499639
theorem B1321559 : Blo 443779 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B1124999 : Blo 443779 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B1125049 : Blo 443779 1125049 := bstep (se 2 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 1125049 = 843787) B843787
theorem B666299 : Blo 443779 666299 := bstep (se 1 (by rfl) ⟨499724, by rfl⟩ : syracuseStep 666299 = 999449) B999449
theorem B666359 : Blo 443779 666359 := bstep (se 1 (by rfl) ⟨499769, by rfl⟩ : syracuseStep 666359 = 999539) B999539
theorem B666383 : Blo 443779 666383 := bstep (se 1 (by rfl) ⟨499787, by rfl⟩ : syracuseStep 666383 = 999575) B999575
theorem B666425 : Blo 443779 666425 := bstep (se 2 (by rfl) ⟨249909, by rfl⟩ : syracuseStep 666425 = 499819) B499819
theorem B666503 : Blo 443779 666503 := bstep (se 1 (by rfl) ⟨499877, by rfl⟩ : syracuseStep 666503 = 999755) B999755
theorem B502663 : Blo 443779 502663 := bstep (se 1 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 502663 = 753995) B753995
theorem B666539 : Blo 443779 666539 := bstep (se 1 (by rfl) ⟨499904, by rfl⟩ : syracuseStep 666539 = 999809) B999809
theorem B666569 : Blo 443779 666569 := bstep (se 2 (by rfl) ⟨249963, by rfl⟩ : syracuseStep 666569 = 499927) B499927
theorem B2173981 : Blo 443779 2173981 := bstep (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) B815243
theorem B666683 : Blo 443779 666683 := bstep (se 1 (by rfl) ⟨500012, by rfl⟩ : syracuseStep 666683 = 1000025) B1000025
theorem B502843 : Blo 443779 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B666743 : Blo 443779 666743 := bstep (se 1 (by rfl) ⟨500057, by rfl⟩ : syracuseStep 666743 = 1000115) B1000115
theorem B666767 : Blo 443779 666767 := bstep (se 1 (by rfl) ⟨500075, by rfl⟩ : syracuseStep 666767 = 1000151) B1000151
theorem B666809 : Blo 443779 666809 := bstep (se 2 (by rfl) ⟨250053, by rfl⟩ : syracuseStep 666809 = 500107) B500107
theorem B666887 : Blo 443779 666887 := bstep (se 1 (by rfl) ⟨500165, by rfl⟩ : syracuseStep 666887 = 1000331) B1000331
theorem B1125647 : Blo 443779 1125647 := bstep (se 1 (by rfl) ⟨844235, by rfl⟩ : syracuseStep 1125647 = 1688471) B1688471
theorem B666923 : Blo 443779 666923 := bstep (se 1 (by rfl) ⟨500192, by rfl⟩ : syracuseStep 666923 = 1000385) B1000385
theorem B666953 : Blo 443779 666953 := bstep (se 2 (by rfl) ⟨250107, by rfl⟩ : syracuseStep 666953 = 500215) B500215
theorem B667067 : Blo 443779 667067 := bstep (se 1 (by rfl) ⟨500300, by rfl⟩ : syracuseStep 667067 = 1000601) B1000601
theorem B667127 : Blo 443779 667127 := bstep (se 1 (by rfl) ⟨500345, by rfl⟩ : syracuseStep 667127 = 1000691) B1000691
theorem B601591 : Blo 443779 601591 := bstep (se 1 (by rfl) ⟨451193, by rfl⟩ : syracuseStep 601591 = 902387) B902387
theorem B2534915 : Blo 443779 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B667151 : Blo 443779 667151 := bstep (se 1 (by rfl) ⟨500363, by rfl⟩ : syracuseStep 667151 = 1000727) B1000727
theorem B503311 : Blo 443779 503311 := bstep (se 1 (by rfl) ⟨377483, by rfl⟩ : syracuseStep 503311 = 754967) B754967
theorem B667193 : Blo 443779 667193 := bstep (se 2 (by rfl) ⟨250197, by rfl⟩ : syracuseStep 667193 = 500395) B500395
theorem B601673 : Blo 443779 601673 := bstep (se 2 (by rfl) ⟨225627, by rfl⟩ : syracuseStep 601673 = 451255) B451255
theorem B667271 : Blo 443779 667271 := bstep (se 1 (by rfl) ⟨500453, by rfl⟩ : syracuseStep 667271 = 1000907) B1000907
theorem B1060499 : Blo 443779 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B667307 : Blo 443779 667307 := bstep (se 1 (by rfl) ⟨500480, by rfl⟩ : syracuseStep 667307 = 1000961) B1000961
theorem B667337 : Blo 443779 667337 := bstep (se 2 (by rfl) ⟨250251, by rfl⟩ : syracuseStep 667337 = 500503) B500503
theorem B667451 : Blo 443779 667451 := bstep (se 1 (by rfl) ⟨500588, by rfl⟩ : syracuseStep 667451 = 1001177) B1001177
theorem B667511 : Blo 443779 667511 := bstep (se 1 (by rfl) ⟨500633, by rfl⟩ : syracuseStep 667511 = 1001267) B1001267
theorem B667535 : Blo 443779 667535 := bstep (se 1 (by rfl) ⟨500651, by rfl⟩ : syracuseStep 667535 = 1001303) B1001303
theorem B13709209 : Blo 443779 13709209 := bstep (se 2 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 13709209 = 10281907) B10281907
theorem B667577 : Blo 443779 667577 := bstep (se 2 (by rfl) ⟨250341, by rfl⟩ : syracuseStep 667577 = 500683) B500683
theorem B1126345 : Blo 443779 1126345 := bstep (se 2 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 1126345 = 844759) B844759
theorem B2535371 : Blo 443779 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B667655 : Blo 443779 667655 := bstep (se 1 (by rfl) ⟨500741, by rfl⟩ : syracuseStep 667655 = 1001483) B1001483
theorem B569359 : Blo 443779 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B667691 : Blo 443779 667691 := bstep (se 1 (by rfl) ⟨500768, by rfl⟩ : syracuseStep 667691 = 1001537) B1001537
theorem B667721 : Blo 443779 667721 := bstep (se 2 (by rfl) ⟨250395, by rfl⟩ : syracuseStep 667721 = 500791) B500791
theorem B1126487 : Blo 443779 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B667835 : Blo 443779 667835 := bstep (se 1 (by rfl) ⟨500876, by rfl⟩ : syracuseStep 667835 = 1001753) B1001753
theorem B667895 : Blo 443779 667895 := bstep (se 1 (by rfl) ⟨500921, by rfl⟩ : syracuseStep 667895 = 1001843) B1001843
theorem B667919 : Blo 443779 667919 := bstep (se 1 (by rfl) ⟨500939, by rfl⟩ : syracuseStep 667919 = 1001879) B1001879
theorem B667961 : Blo 443779 667961 := bstep (se 2 (by rfl) ⟨250485, by rfl⟩ : syracuseStep 667961 = 500971) B500971
theorem B1519931 : Blo 443779 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B668039 : Blo 443779 668039 := bstep (se 1 (by rfl) ⟨501029, by rfl⟩ : syracuseStep 668039 = 1002059) B1002059
theorem B668075 : Blo 443779 668075 := bstep (se 1 (by rfl) ⟨501056, by rfl⟩ : syracuseStep 668075 = 1002113) B1002113
theorem B668105 : Blo 443779 668105 := bstep (se 2 (by rfl) ⟨250539, by rfl⟩ : syracuseStep 668105 = 501079) B501079
theorem B668219 : Blo 443779 668219 := bstep (se 1 (by rfl) ⟨501164, by rfl⟩ : syracuseStep 668219 = 1002329) B1002329
theorem B2536055 : Blo 443779 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B668279 : Blo 443779 668279 := bstep (se 1 (by rfl) ⟨501209, by rfl⟩ : syracuseStep 668279 = 1002419) B1002419
theorem B602759 : Blo 443779 602759 := bstep (se 1 (by rfl) ⟨452069, by rfl⟩ : syracuseStep 602759 = 904139) B904139
theorem B668303 : Blo 443779 668303 := bstep (se 1 (by rfl) ⟨501227, by rfl⟩ : syracuseStep 668303 = 1002455) B1002455
theorem B635563 : Blo 443779 635563 := bstep (se 1 (by rfl) ⟨476672, by rfl⟩ : syracuseStep 635563 = 953345) B953345
theorem B668345 : Blo 443779 668345 := bstep (se 2 (by rfl) ⟨250629, by rfl⟩ : syracuseStep 668345 = 501259) B501259
theorem B668423 : Blo 443779 668423 := bstep (se 1 (by rfl) ⟨501317, by rfl⟩ : syracuseStep 668423 = 1002635) B1002635
theorem B2405153 : Blo 443779 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B4829989 : Blo 443779 4829989 := bstep (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) B905623
theorem B668459 : Blo 443779 668459 := bstep (se 1 (by rfl) ⟨501344, by rfl⟩ : syracuseStep 668459 = 1002689) B1002689
theorem B668489 : Blo 443779 668489 := bstep (se 2 (by rfl) ⟨250683, by rfl⟩ : syracuseStep 668489 = 501367) B501367
theorem B635791 : Blo 443779 635791 := bstep (se 1 (by rfl) ⟨476843, by rfl⟩ : syracuseStep 635791 = 953687) B953687
theorem B7943093 : Blo 443779 7943093 := bstep (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) B744665
theorem B27898805 : Blo 443779 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B668603 : Blo 443779 668603 := bstep (se 1 (by rfl) ⟨501452, by rfl⟩ : syracuseStep 668603 = 1002905) B1002905
theorem B668663 : Blo 443779 668663 := bstep (se 1 (by rfl) ⟨501497, by rfl⟩ : syracuseStep 668663 = 1002995) B1002995
theorem B668687 : Blo 443779 668687 := bstep (se 1 (by rfl) ⟨501515, by rfl⟩ : syracuseStep 668687 = 1003031) B1003031
theorem B668729 : Blo 443779 668729 := bstep (se 2 (by rfl) ⟨250773, by rfl⟩ : syracuseStep 668729 = 501547) B501547
theorem B668807 : Blo 443779 668807 := bstep (se 1 (by rfl) ⟨501605, by rfl⟩ : syracuseStep 668807 = 1003211) B1003211
theorem B668843 : Blo 443779 668843 := bstep (se 1 (by rfl) ⟨501632, by rfl⟩ : syracuseStep 668843 = 1003265) B1003265
theorem B668873 : Blo 443779 668873 := bstep (se 2 (by rfl) ⟨250827, by rfl⟩ : syracuseStep 668873 = 501655) B501655
theorem B668987 : Blo 443779 668987 := bstep (se 1 (by rfl) ⟨501740, by rfl⟩ : syracuseStep 668987 = 1003481) B1003481
theorem B603451 : Blo 443779 603451 := bstep (se 1 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 603451 = 905177) B905177
theorem B669047 : Blo 443779 669047 := bstep (se 1 (by rfl) ⟨501785, by rfl⟩ : syracuseStep 669047 = 1003571) B1003571
theorem B669071 : Blo 443779 669071 := bstep (se 1 (by rfl) ⟨501803, by rfl⟩ : syracuseStep 669071 = 1003607) B1003607
theorem B4634003 : Blo 443779 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B669113 : Blo 443779 669113 := bstep (se 2 (by rfl) ⟨250917, by rfl⟩ : syracuseStep 669113 = 501835) B501835
theorem B5092793 : Blo 443779 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B3225091 : Blo 443779 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B669191 : Blo 443779 669191 := bstep (se 1 (by rfl) ⟨501893, by rfl⟩ : syracuseStep 669191 = 1003787) B1003787
theorem B669227 : Blo 443779 669227 := bstep (se 1 (by rfl) ⟨501920, by rfl⟩ : syracuseStep 669227 = 1003841) B1003841
theorem B669257 : Blo 443779 669257 := bstep (se 2 (by rfl) ⟨250971, by rfl⟩ : syracuseStep 669257 = 501943) B501943
theorem B669371 : Blo 443779 669371 := bstep (se 1 (by rfl) ⟨502028, by rfl⟩ : syracuseStep 669371 = 1004057) B1004057
theorem B669431 : Blo 443779 669431 := bstep (se 1 (by rfl) ⟨502073, by rfl⟩ : syracuseStep 669431 = 1004147) B1004147
theorem B669455 : Blo 443779 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B669497 : Blo 443779 669497 := bstep (se 2 (by rfl) ⟨251061, by rfl⟩ : syracuseStep 669497 = 502123) B502123
theorem B669575 : Blo 443779 669575 := bstep (se 1 (by rfl) ⟨502181, by rfl⟩ : syracuseStep 669575 = 1004363) B1004363
theorem B669611 : Blo 443779 669611 := bstep (se 1 (by rfl) ⟨502208, by rfl⟩ : syracuseStep 669611 = 1004417) B1004417
theorem B669641 : Blo 443779 669641 := bstep (se 2 (by rfl) ⟨251115, by rfl⟩ : syracuseStep 669641 = 502231) B502231
theorem B669755 : Blo 443779 669755 := bstep (se 1 (by rfl) ⟨502316, by rfl⟩ : syracuseStep 669755 = 1004633) B1004633
theorem B1128563 : Blo 443779 1128563 := bstep (se 1 (by rfl) ⟨846422, by rfl⟩ : syracuseStep 1128563 = 1692845) B1692845
theorem B669815 : Blo 443779 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B669839 : Blo 443779 669839 := bstep (se 1 (by rfl) ⟨502379, by rfl⟩ : syracuseStep 669839 = 1004759) B1004759
theorem B1358009 : Blo 443779 1358009 := bstep (se 2 (by rfl) ⟨509253, by rfl⟩ : syracuseStep 1358009 = 1018507) B1018507
theorem B669881 : Blo 443779 669881 := bstep (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) B502411
theorem B669959 : Blo 443779 669959 := bstep (se 1 (by rfl) ⟨502469, by rfl⟩ : syracuseStep 669959 = 1004939) B1004939
theorem B669995 : Blo 443779 669995 := bstep (se 1 (by rfl) ⟨502496, by rfl⟩ : syracuseStep 669995 = 1004993) B1004993
theorem B801083 : Blo 443779 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B670025 : Blo 443779 670025 := bstep (se 2 (by rfl) ⟨251259, by rfl⟩ : syracuseStep 670025 = 502519) B502519
theorem B670139 : Blo 443779 670139 := bstep (se 1 (by rfl) ⟨502604, by rfl⟩ : syracuseStep 670139 = 1005209) B1005209
theorem B670199 : Blo 443779 670199 := bstep (se 1 (by rfl) ⟨502649, by rfl⟩ : syracuseStep 670199 = 1005299) B1005299
theorem B670223 : Blo 443779 670223 := bstep (se 1 (by rfl) ⟨502667, by rfl⟩ : syracuseStep 670223 = 1005335) B1005335
theorem B2538013 : Blo 443779 2538013 := bstep (se 3 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 2538013 = 951755) B951755
theorem B670265 : Blo 443779 670265 := bstep (se 2 (by rfl) ⟨251349, by rfl⟩ : syracuseStep 670265 = 502699) B502699
theorem B1129079 : Blo 443779 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B670343 : Blo 443779 670343 := bstep (se 1 (by rfl) ⟨502757, by rfl⟩ : syracuseStep 670343 = 1005515) B1005515
theorem B670379 : Blo 443779 670379 := bstep (se 1 (by rfl) ⟨502784, by rfl⟩ : syracuseStep 670379 = 1005569) B1005569
theorem B670409 : Blo 443779 670409 := bstep (se 2 (by rfl) ⟨251403, by rfl⟩ : syracuseStep 670409 = 502807) B502807
theorem B670523 : Blo 443779 670523 := bstep (se 1 (by rfl) ⟨502892, by rfl⟩ : syracuseStep 670523 = 1005785) B1005785
theorem B670583 : Blo 443779 670583 := bstep (se 1 (by rfl) ⟨502937, by rfl⟩ : syracuseStep 670583 = 1005875) B1005875
theorem B670607 : Blo 443779 670607 := bstep (se 1 (by rfl) ⟨502955, by rfl⟩ : syracuseStep 670607 = 1005911) B1005911
theorem B670649 : Blo 443779 670649 := bstep (se 2 (by rfl) ⟨251493, by rfl⟩ : syracuseStep 670649 = 502987) B502987
theorem B670727 : Blo 443779 670727 := bstep (se 1 (by rfl) ⟨503045, by rfl⟩ : syracuseStep 670727 = 1006091) B1006091
theorem B2538539 : Blo 443779 2538539 := bstep (se 1 (by rfl) ⟨1903904, by rfl⟩ : syracuseStep 2538539 = 3807809) B3807809
theorem B670763 : Blo 443779 670763 := bstep (se 1 (by rfl) ⟨503072, by rfl⟩ : syracuseStep 670763 = 1006145) B1006145
theorem B670793 : Blo 443779 670793 := bstep (se 2 (by rfl) ⟨251547, by rfl⟩ : syracuseStep 670793 = 503095) B503095
theorem B998585 : Blo 443779 998585 := bstep (se 2 (by rfl) ⟨374469, by rfl⟩ : syracuseStep 998585 = 748939) B748939
theorem B670907 : Blo 443779 670907 := bstep (se 1 (by rfl) ⟨503180, by rfl⟩ : syracuseStep 670907 = 1006361) B1006361
theorem B670967 : Blo 443779 670967 := bstep (se 1 (by rfl) ⟨503225, by rfl⟩ : syracuseStep 670967 = 1006451) B1006451
theorem B474383 : Blo 443779 474383 := bstep (se 1 (by rfl) ⟨355787, by rfl⟩ : syracuseStep 474383 = 711575) B711575
theorem B670991 : Blo 443779 670991 := bstep (se 1 (by rfl) ⟨503243, by rfl⟩ : syracuseStep 670991 = 1006487) B1006487
theorem B671033 : Blo 443779 671033 := bstep (se 2 (by rfl) ⟨251637, by rfl⟩ : syracuseStep 671033 = 503275) B503275
theorem B671111 : Blo 443779 671111 := bstep (se 1 (by rfl) ⟨503333, by rfl⟩ : syracuseStep 671111 = 1006667) B1006667
theorem B671147 : Blo 443779 671147 := bstep (se 1 (by rfl) ⟨503360, by rfl⟩ : syracuseStep 671147 = 1006721) B1006721
theorem B671177 : Blo 443779 671177 := bstep (se 2 (by rfl) ⟨251691, by rfl⟩ : syracuseStep 671177 = 503383) B503383
theorem B998927 : Blo 443779 998927 := bstep (se 1 (by rfl) ⟨749195, by rfl⟩ : syracuseStep 998927 = 1498391) B1498391
theorem B998945 : Blo 443779 998945 := bstep (se 2 (by rfl) ⟨374604, by rfl⟩ : syracuseStep 998945 = 749209) B749209
theorem B572971 : Blo 443779 572971 := bstep (se 1 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 572971 = 859457) B859457
theorem B671291 : Blo 443779 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B1130071 : Blo 443779 1130071 := bstep (se 1 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 1130071 = 1695107) B1695107
theorem B671351 : Blo 443779 671351 := bstep (se 1 (by rfl) ⟨503513, by rfl⟩ : syracuseStep 671351 = 1007027) B1007027
theorem B671375 : Blo 443779 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B671417 : Blo 443779 671417 := bstep (se 2 (by rfl) ⟨251781, by rfl⟩ : syracuseStep 671417 = 503563) B503563
theorem B671495 : Blo 443779 671495 := bstep (se 1 (by rfl) ⟨503621, by rfl⟩ : syracuseStep 671495 = 1007243) B1007243
theorem B671531 : Blo 443779 671531 := bstep (se 1 (by rfl) ⟨503648, by rfl⟩ : syracuseStep 671531 = 1007297) B1007297
theorem B671561 : Blo 443779 671561 := bstep (se 2 (by rfl) ⟨251835, by rfl⟩ : syracuseStep 671561 = 503671) B503671
theorem B999287 : Blo 443779 999287 := bstep (se 1 (by rfl) ⟨749465, by rfl⟩ : syracuseStep 999287 = 1498931) B1498931
theorem B1130375 : Blo 443779 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B5717911 : Blo 443779 5717911 := bstep (se 1 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 5717911 = 8576867) B8576867
theorem B1130507 : Blo 443779 1130507 := bstep (se 1 (by rfl) ⟨847880, by rfl⟩ : syracuseStep 1130507 = 1695761) B1695761
theorem B999467 : Blo 443779 999467 := bstep (se 1 (by rfl) ⟨749600, by rfl⟩ : syracuseStep 999467 = 1499201) B1499201
theorem B999827 : Blo 443779 999827 := bstep (se 1 (by rfl) ⟨749870, by rfl⟩ : syracuseStep 999827 = 1499741) B1499741
theorem B475579 : Blo 443779 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B999881 : Blo 443779 999881 := bstep (se 2 (by rfl) ⟨374955, by rfl⟩ : syracuseStep 999881 = 749911) B749911
theorem B2539997 : Blo 443779 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B20595185 : Blo 443779 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B1131023 : Blo 443779 1131023 := bstep (se 1 (by rfl) ⟨848267, by rfl⟩ : syracuseStep 1131023 = 1696535) B1696535
theorem B15483413 : Blo 443779 15483413 := bstep (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) B725785
theorem B1720919 : Blo 443779 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B1131155 : Blo 443779 1131155 := bstep (se 1 (by rfl) ⟨848366, by rfl⟩ : syracuseStep 1131155 = 1696733) B1696733
theorem B574327 : Blo 443779 574327 := bstep (se 1 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 574327 = 861491) B861491
theorem B2147447 : Blo 443779 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B1000583 : Blo 443779 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B1000763 : Blo 443779 1000763 := bstep (se 1 (by rfl) ⟨750572, by rfl⟩ : syracuseStep 1000763 = 1501145) B1501145
theorem B443783 : Blo 443779 443783 := bstep (se 1 (by rfl) ⟨332837, by rfl⟩ : syracuseStep 443783 = 665675) B665675
theorem B443791 : Blo 443779 443791 := bstep (se 1 (by rfl) ⟨332843, by rfl⟩ : syracuseStep 443791 = 665687) B665687
theorem B1000889 : Blo 443779 1000889 := bstep (se 2 (by rfl) ⟨375333, by rfl⟩ : syracuseStep 1000889 = 750667) B750667
theorem B443835 : Blo 443779 443835 := bstep (se 1 (by rfl) ⟨332876, by rfl⟩ : syracuseStep 443835 = 665753) B665753
theorem B443911 : Blo 443779 443911 := bstep (se 1 (by rfl) ⟨332933, by rfl⟩ : syracuseStep 443911 = 665867) B665867
theorem B443919 : Blo 443779 443919 := bstep (se 1 (by rfl) ⟨332939, by rfl⟩ : syracuseStep 443919 = 665879) B665879
theorem B1033771 : Blo 443779 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B443963 : Blo 443779 443963 := bstep (se 1 (by rfl) ⟨332972, by rfl⟩ : syracuseStep 443963 = 665945) B665945
theorem B444039 : Blo 443779 444039 := bstep (se 1 (by rfl) ⟨333029, by rfl⟩ : syracuseStep 444039 = 666059) B666059
theorem B444047 : Blo 443779 444047 := bstep (se 1 (by rfl) ⟨333035, by rfl⟩ : syracuseStep 444047 = 666071) B666071
theorem B2705069 : Blo 443779 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B444091 : Blo 443779 444091 := bstep (se 1 (by rfl) ⟨333068, by rfl⟩ : syracuseStep 444091 = 666137) B666137
theorem B4572929 : Blo 443779 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B1132289 : Blo 443779 1132289 := bstep (se 2 (by rfl) ⟨424608, by rfl⟩ : syracuseStep 1132289 = 849217) B849217
theorem B444167 : Blo 443779 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B444175 : Blo 443779 444175 := bstep (se 1 (by rfl) ⟨333131, by rfl⟩ : syracuseStep 444175 = 666263) B666263
theorem B1001231 : Blo 443779 1001231 := bstep (se 1 (by rfl) ⟨750923, by rfl⟩ : syracuseStep 1001231 = 1501847) B1501847
theorem B1001249 : Blo 443779 1001249 := bstep (se 2 (by rfl) ⟨375468, by rfl⟩ : syracuseStep 1001249 = 750937) B750937
theorem B444219 : Blo 443779 444219 := bstep (se 1 (by rfl) ⟨333164, by rfl⟩ : syracuseStep 444219 = 666329) B666329
theorem B870203 : Blo 443779 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B444295 : Blo 443779 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B444303 : Blo 443779 444303 := bstep (se 1 (by rfl) ⟨333227, by rfl⟩ : syracuseStep 444303 = 666455) B666455
theorem B444347 : Blo 443779 444347 := bstep (se 1 (by rfl) ⟨333260, by rfl⟩ : syracuseStep 444347 = 666521) B666521
theorem B444423 : Blo 443779 444423 := bstep (se 1 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 444423 = 666635) B666635
theorem B444431 : Blo 443779 444431 := bstep (se 1 (by rfl) ⟨333323, by rfl⟩ : syracuseStep 444431 = 666647) B666647
theorem B444475 : Blo 443779 444475 := bstep (se 1 (by rfl) ⟨333356, by rfl⟩ : syracuseStep 444475 = 666713) B666713
theorem B4835389 : Blo 443779 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B1001591 : Blo 443779 1001591 := bstep (se 1 (by rfl) ⟨751193, by rfl⟩ : syracuseStep 1001591 = 1502387) B1502387
theorem B1132663 : Blo 443779 1132663 := bstep (se 1 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 1132663 = 1698995) B1698995
theorem B444551 : Blo 443779 444551 := bstep (se 1 (by rfl) ⟨333413, by rfl⟩ : syracuseStep 444551 = 666827) B666827
theorem B444559 : Blo 443779 444559 := bstep (se 1 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 444559 = 666839) B666839
theorem B444603 : Blo 443779 444603 := bstep (se 1 (by rfl) ⟨333452, by rfl⟩ : syracuseStep 444603 = 666905) B666905
theorem B3393737 : Blo 443779 3393737 := bstep (se 2 (by rfl) ⟨1272651, by rfl⟩ : syracuseStep 3393737 = 2545303) B2545303
theorem B444679 : Blo 443779 444679 := bstep (se 1 (by rfl) ⟨333509, by rfl⟩ : syracuseStep 444679 = 667019) B667019
theorem B444687 : Blo 443779 444687 := bstep (se 1 (by rfl) ⟨333515, by rfl⟩ : syracuseStep 444687 = 667031) B667031
theorem B805135 : Blo 443779 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B1001771 : Blo 443779 1001771 := bstep (se 1 (by rfl) ⟨751328, by rfl⟩ : syracuseStep 1001771 = 1502657) B1502657
theorem B444731 : Blo 443779 444731 := bstep (se 1 (by rfl) ⟨333548, by rfl⟩ : syracuseStep 444731 = 667097) B667097
theorem B1427827 : Blo 443779 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B5065091 : Blo 443779 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B444807 : Blo 443779 444807 := bstep (se 1 (by rfl) ⟨333605, by rfl⟩ : syracuseStep 444807 = 667211) B667211
theorem B444815 : Blo 443779 444815 := bstep (se 1 (by rfl) ⟨333611, by rfl⟩ : syracuseStep 444815 = 667223) B667223
theorem B1067411 : Blo 443779 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B444859 : Blo 443779 444859 := bstep (se 1 (by rfl) ⟨333644, by rfl⟩ : syracuseStep 444859 = 667289) B667289
theorem B444935 : Blo 443779 444935 := bstep (se 1 (by rfl) ⟨333701, by rfl⟩ : syracuseStep 444935 = 667403) B667403
theorem B444943 : Blo 443779 444943 := bstep (se 1 (by rfl) ⟨333707, by rfl⟩ : syracuseStep 444943 = 667415) B667415
theorem B1133099 : Blo 443779 1133099 := bstep (se 1 (by rfl) ⟨849824, by rfl⟩ : syracuseStep 1133099 = 1699649) B1699649
theorem B444987 : Blo 443779 444987 := bstep (se 1 (by rfl) ⟨333740, by rfl⟩ : syracuseStep 444987 = 667481) B667481
theorem B445063 : Blo 443779 445063 := bstep (se 1 (by rfl) ⟨333797, by rfl⟩ : syracuseStep 445063 = 667595) B667595
theorem B445071 : Blo 443779 445071 := bstep (se 1 (by rfl) ⟨333803, by rfl⟩ : syracuseStep 445071 = 667607) B667607
theorem B1002131 : Blo 443779 1002131 := bstep (se 1 (by rfl) ⟨751598, by rfl⟩ : syracuseStep 1002131 = 1503197) B1503197
theorem B445115 : Blo 443779 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B1002185 : Blo 443779 1002185 := bstep (se 2 (by rfl) ⟨375819, by rfl⟩ : syracuseStep 1002185 = 751639) B751639
theorem B2247425 : Blo 443779 2247425 := bstep (se 2 (by rfl) ⟨842784, by rfl⟩ : syracuseStep 2247425 = 1685569) B1685569
theorem B445191 : Blo 443779 445191 := bstep (se 1 (by rfl) ⟨333893, by rfl⟩ : syracuseStep 445191 = 667787) B667787
theorem B445199 : Blo 443779 445199 := bstep (se 1 (by rfl) ⟨333899, by rfl⟩ : syracuseStep 445199 = 667799) B667799
theorem B2542387 : Blo 443779 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B445243 : Blo 443779 445243 := bstep (se 1 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 445243 = 667865) B667865
theorem B445319 : Blo 443779 445319 := bstep (se 1 (by rfl) ⟨333989, by rfl⟩ : syracuseStep 445319 = 667979) B667979
theorem B445327 : Blo 443779 445327 := bstep (se 1 (by rfl) ⟨333995, by rfl⟩ : syracuseStep 445327 = 667991) B667991
theorem B1264531 : Blo 443779 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B445371 : Blo 443779 445371 := bstep (se 1 (by rfl) ⟨334028, by rfl⟩ : syracuseStep 445371 = 668057) B668057
theorem B445447 : Blo 443779 445447 := bstep (se 1 (by rfl) ⟨334085, by rfl⟩ : syracuseStep 445447 = 668171) B668171
theorem B14797835 : Blo 443779 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B445455 : Blo 443779 445455 := bstep (se 1 (by rfl) ⟨334091, by rfl⟩ : syracuseStep 445455 = 668183) B668183
theorem B445499 : Blo 443779 445499 := bstep (se 1 (by rfl) ⟨334124, by rfl⟩ : syracuseStep 445499 = 668249) B668249
theorem B445575 : Blo 443779 445575 := bstep (se 1 (by rfl) ⟨334181, by rfl⟩ : syracuseStep 445575 = 668363) B668363
theorem B445583 : Blo 443779 445583 := bstep (se 1 (by rfl) ⟨334187, by rfl⟩ : syracuseStep 445583 = 668375) B668375
theorem B445627 : Blo 443779 445627 := bstep (se 1 (by rfl) ⟨334220, by rfl⟩ : syracuseStep 445627 = 668441) B668441
theorem B445703 : Blo 443779 445703 := bstep (se 1 (by rfl) ⟨334277, by rfl⟩ : syracuseStep 445703 = 668555) B668555
theorem B445711 : Blo 443779 445711 := bstep (se 1 (by rfl) ⟨334283, by rfl⟩ : syracuseStep 445711 = 668567) B668567
theorem B904463 : Blo 443779 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B445755 : Blo 443779 445755 := bstep (se 1 (by rfl) ⟨334316, by rfl⟩ : syracuseStep 445755 = 668633) B668633
theorem B1002887 : Blo 443779 1002887 := bstep (se 1 (by rfl) ⟨752165, by rfl⟩ : syracuseStep 1002887 = 1504331) B1504331
theorem B445831 : Blo 443779 445831 := bstep (se 1 (by rfl) ⟨334373, by rfl⟩ : syracuseStep 445831 = 668747) B668747
theorem B445839 : Blo 443779 445839 := bstep (se 1 (by rfl) ⟨334379, by rfl⟩ : syracuseStep 445839 = 668759) B668759
theorem B445883 : Blo 443779 445883 := bstep (se 1 (by rfl) ⟨334412, by rfl⟩ : syracuseStep 445883 = 668825) B668825
theorem B445959 : Blo 443779 445959 := bstep (se 1 (by rfl) ⟨334469, by rfl⟩ : syracuseStep 445959 = 668939) B668939
theorem B445967 : Blo 443779 445967 := bstep (se 1 (by rfl) ⟨334475, by rfl⟩ : syracuseStep 445967 = 668951) B668951
theorem B2248235 : Blo 443779 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B1003067 : Blo 443779 1003067 := bstep (se 1 (by rfl) ⟨752300, by rfl⟩ : syracuseStep 1003067 = 1504601) B1504601
theorem B446011 : Blo 443779 446011 := bstep (se 1 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 446011 = 669017) B669017
theorem B446087 : Blo 443779 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B446095 : Blo 443779 446095 := bstep (se 1 (by rfl) ⟨334571, by rfl⟩ : syracuseStep 446095 = 669143) B669143
theorem B1003193 : Blo 443779 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B446139 : Blo 443779 446139 := bstep (se 1 (by rfl) ⟨334604, by rfl⟩ : syracuseStep 446139 = 669209) B669209
theorem B446215 : Blo 443779 446215 := bstep (se 1 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 446215 = 669323) B669323
theorem B446223 : Blo 443779 446223 := bstep (se 1 (by rfl) ⟨334667, by rfl⟩ : syracuseStep 446223 = 669335) B669335
theorem B446267 : Blo 443779 446267 := bstep (se 1 (by rfl) ⟨334700, by rfl⟩ : syracuseStep 446267 = 669401) B669401
theorem B446343 : Blo 443779 446343 := bstep (se 1 (by rfl) ⟨334757, by rfl⟩ : syracuseStep 446343 = 669515) B669515
theorem B446351 : Blo 443779 446351 := bstep (se 1 (by rfl) ⟨334763, by rfl⟩ : syracuseStep 446351 = 669527) B669527
theorem B1200025 : Blo 443779 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B446395 : Blo 443779 446395 := bstep (se 1 (by rfl) ⟨334796, by rfl⟩ : syracuseStep 446395 = 669593) B669593
theorem B446471 : Blo 443779 446471 := bstep (se 1 (by rfl) ⟨334853, by rfl⟩ : syracuseStep 446471 = 669707) B669707
theorem B3821579 : Blo 443779 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B1003535 : Blo 443779 1003535 := bstep (se 1 (by rfl) ⟨752651, by rfl⟩ : syracuseStep 1003535 = 1505303) B1505303
theorem B446479 : Blo 443779 446479 := bstep (se 1 (by rfl) ⟨334859, by rfl⟩ : syracuseStep 446479 = 669719) B669719
theorem B1003553 : Blo 443779 1003553 := bstep (se 2 (by rfl) ⟨376332, by rfl⟩ : syracuseStep 1003553 = 752665) B752665
theorem B446523 : Blo 443779 446523 := bstep (se 1 (by rfl) ⟨334892, by rfl⟩ : syracuseStep 446523 = 669785) B669785
theorem B446599 : Blo 443779 446599 := bstep (se 1 (by rfl) ⟨334949, by rfl⟩ : syracuseStep 446599 = 669899) B669899
theorem B446607 : Blo 443779 446607 := bstep (se 1 (by rfl) ⟨334955, by rfl⟩ : syracuseStep 446607 = 669911) B669911
theorem B446651 : Blo 443779 446651 := bstep (se 1 (by rfl) ⟨334988, by rfl⟩ : syracuseStep 446651 = 669977) B669977
theorem B2543845 : Blo 443779 2543845 := bstep (se 4 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 2543845 = 476971) B476971
theorem B446727 : Blo 443779 446727 := bstep (se 1 (by rfl) ⟨335045, by rfl⟩ : syracuseStep 446727 = 670091) B670091
theorem B1429775 : Blo 443779 1429775 := bstep (se 1 (by rfl) ⟨1072331, by rfl⟩ : syracuseStep 1429775 = 2144663) B2144663
theorem B446735 : Blo 443779 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B446779 : Blo 443779 446779 := bstep (se 1 (by rfl) ⟨335084, by rfl⟩ : syracuseStep 446779 = 670169) B670169
theorem B1003895 : Blo 443779 1003895 := bstep (se 1 (by rfl) ⟨752921, by rfl⟩ : syracuseStep 1003895 = 1505843) B1505843
theorem B446855 : Blo 443779 446855 := bstep (se 1 (by rfl) ⟨335141, by rfl⟩ : syracuseStep 446855 = 670283) B670283
theorem B446863 : Blo 443779 446863 := bstep (se 1 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 446863 = 670295) B670295
theorem B3101075 : Blo 443779 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B446907 : Blo 443779 446907 := bstep (se 1 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 446907 = 670361) B670361
theorem B446983 : Blo 443779 446983 := bstep (se 1 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 446983 = 670475) B670475
theorem B446991 : Blo 443779 446991 := bstep (se 1 (by rfl) ⟨335243, by rfl⟩ : syracuseStep 446991 = 670487) B670487
theorem B18469397 : Blo 443779 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B1266205 : Blo 443779 1266205 := bstep (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) B474827
theorem B1004075 : Blo 443779 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B447035 : Blo 443779 447035 := bstep (se 1 (by rfl) ⟨335276, by rfl⟩ : syracuseStep 447035 = 670553) B670553
theorem B1266263 : Blo 443779 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B447111 : Blo 443779 447111 := bstep (se 1 (by rfl) ⟨335333, by rfl⟩ : syracuseStep 447111 = 670667) B670667
theorem B447119 : Blo 443779 447119 := bstep (se 1 (by rfl) ⟨335339, by rfl⟩ : syracuseStep 447119 = 670679) B670679
theorem B447163 : Blo 443779 447163 := bstep (se 1 (by rfl) ⟨335372, by rfl⟩ : syracuseStep 447163 = 670745) B670745
theorem B447239 : Blo 443779 447239 := bstep (se 1 (by rfl) ⟨335429, by rfl⟩ : syracuseStep 447239 = 670859) B670859
theorem B447247 : Blo 443779 447247 := bstep (se 1 (by rfl) ⟨335435, by rfl⟩ : syracuseStep 447247 = 670871) B670871
theorem B5133091 : Blo 443779 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B2249531 : Blo 443779 2249531 := bstep (se 1 (by rfl) ⟨1687148, by rfl⟩ : syracuseStep 2249531 = 3374297) B3374297
theorem B447291 : Blo 443779 447291 := bstep (se 1 (by rfl) ⟨335468, by rfl⟩ : syracuseStep 447291 = 670937) B670937
theorem B447367 : Blo 443779 447367 := bstep (se 1 (by rfl) ⟨335525, by rfl⟩ : syracuseStep 447367 = 671051) B671051
theorem B447375 : Blo 443779 447375 := bstep (se 1 (by rfl) ⟨335531, by rfl⟩ : syracuseStep 447375 = 671063) B671063
theorem B1201043 : Blo 443779 1201043 := bstep (se 1 (by rfl) ⟨900782, by rfl⟩ : syracuseStep 1201043 = 1801565) B1801565
theorem B1004435 : Blo 443779 1004435 := bstep (se 1 (by rfl) ⟨753326, by rfl⟩ : syracuseStep 1004435 = 1506653) B1506653
theorem B447419 : Blo 443779 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B1004489 : Blo 443779 1004489 := bstep (se 2 (by rfl) ⟨376683, by rfl⟩ : syracuseStep 1004489 = 753367) B753367
theorem B2249693 : Blo 443779 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B447495 : Blo 443779 447495 := bstep (se 1 (by rfl) ⟨335621, by rfl⟩ : syracuseStep 447495 = 671243) B671243
theorem B447503 : Blo 443779 447503 := bstep (se 1 (by rfl) ⟨335627, by rfl⟩ : syracuseStep 447503 = 671255) B671255
theorem B644155 : Blo 443779 644155 := bstep (se 1 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 644155 = 966233) B966233
theorem B447547 : Blo 443779 447547 := bstep (se 1 (by rfl) ⟨335660, by rfl⟩ : syracuseStep 447547 = 671321) B671321
theorem B2151485 : Blo 443779 2151485 := bstep (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) B806807
theorem B676937 : Blo 443779 676937 := bstep (se 2 (by rfl) ⟨253851, by rfl⟩ : syracuseStep 676937 = 507703) B507703
theorem B447623 : Blo 443779 447623 := bstep (se 1 (by rfl) ⟨335717, by rfl⟩ : syracuseStep 447623 = 671435) B671435
theorem B447631 : Blo 443779 447631 := bstep (se 1 (by rfl) ⟨335723, by rfl⟩ : syracuseStep 447631 = 671447) B671447
theorem B447675 : Blo 443779 447675 := bstep (se 1 (by rfl) ⟨335756, by rfl⟩ : syracuseStep 447675 = 671513) B671513
theorem B4084937 : Blo 443779 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B447751 : Blo 443779 447751 := bstep (se 1 (by rfl) ⟨335813, by rfl⟩ : syracuseStep 447751 = 671627) B671627
theorem B447759 : Blo 443779 447759 := bstep (se 1 (by rfl) ⟨335819, by rfl⟩ : syracuseStep 447759 = 671639) B671639
theorem B2250017 : Blo 443779 2250017 := bstep (se 2 (by rfl) ⟨843756, by rfl⟩ : syracuseStep 2250017 = 1687513) B1687513
theorem B677179 : Blo 443779 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B21976433 : Blo 443779 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B4904339 : Blo 443779 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B1005191 : Blo 443779 1005191 := bstep (se 1 (by rfl) ⟨753893, by rfl⟩ : syracuseStep 1005191 = 1507787) B1507787
theorem B1005371 : Blo 443779 1005371 := bstep (se 1 (by rfl) ⟨754028, by rfl⟩ : syracuseStep 1005371 = 1508057) B1508057
theorem B1070995 : Blo 443779 1070995 := bstep (se 1 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 1070995 = 1606493) B1606493
theorem B7329689 : Blo 443779 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1005497 : Blo 443779 1005497 := bstep (se 2 (by rfl) ⟨377061, by rfl⟩ : syracuseStep 1005497 = 754123) B754123
theorem B2414539 : Blo 443779 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B1693649 : Blo 443779 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B1267913 : Blo 443779 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B2250989 : Blo 443779 2250989 := bstep (se 3 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 2250989 = 844121) B844121
theorem B1005839 : Blo 443779 1005839 := bstep (se 1 (by rfl) ⟨754379, by rfl⟩ : syracuseStep 1005839 = 1508759) B1508759
theorem B1005857 : Blo 443779 1005857 := bstep (se 2 (by rfl) ⟨377196, by rfl⟩ : syracuseStep 1005857 = 754393) B754393
theorem B4839713 : Blo 443779 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B1694105 : Blo 443779 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B1432093 : Blo 443779 1432093 := bstep (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) B537035
theorem B1006199 : Blo 443779 1006199 := bstep (se 1 (by rfl) ⟨754649, by rfl⟩ : syracuseStep 1006199 = 1509299) B1509299
theorem B1006379 : Blo 443779 1006379 := bstep (se 1 (by rfl) ⟨754784, by rfl⟩ : syracuseStep 1006379 = 1509569) B1509569
theorem B2546579 : Blo 443779 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B2251799 : Blo 443779 2251799 := bstep (se 1 (by rfl) ⟨1688849, by rfl⟩ : syracuseStep 2251799 = 3377699) B3377699
theorem B1268779 : Blo 443779 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B1072187 : Blo 443779 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B842899 : Blo 443779 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B1006739 : Blo 443779 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B1006793 : Blo 443779 1006793 := bstep (se 2 (by rfl) ⟨377547, by rfl⟩ : syracuseStep 1006793 = 755095) B755095
theorem B1269053 : Blo 443779 1269053 := bstep (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) B475895
theorem B1924499 : Blo 443779 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1498553 : Blo 443779 1498553 := bstep (se 2 (by rfl) ⟨561957, by rfl⟩ : syracuseStep 1498553 = 1123915) B1123915
theorem B1695275 : Blo 443779 1695275 := bstep (se 1 (by rfl) ⟨1271456, by rfl⟩ : syracuseStep 1695275 = 2542913) B2542913
theorem B2547287 : Blo 443779 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B1269395 : Blo 443779 1269395 := bstep (se 1 (by rfl) ⟨952046, by rfl⟩ : syracuseStep 1269395 = 1904093) B1904093
theorem B679753 : Blo 443779 679753 := bstep (se 2 (by rfl) ⟨254907, by rfl⟩ : syracuseStep 679753 = 509815) B509815
theorem B1007495 : Blo 443779 1007495 := bstep (se 1 (by rfl) ⟨755621, by rfl⟩ : syracuseStep 1007495 = 1511243) B1511243
theorem B1499147 : Blo 443779 1499147 := bstep (se 1 (by rfl) ⟨1124360, by rfl⟩ : syracuseStep 1499147 = 2248721) B2248721
theorem B1499255 : Blo 443779 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B3203387 : Blo 443779 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B844091 : Blo 443779 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B1368695 : Blo 443779 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1499849 : Blo 443779 1499849 := bstep (se 2 (by rfl) ⟨562443, by rfl⟩ : syracuseStep 1499849 = 1124887) B1124887
theorem B844577 : Blo 443779 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B713657 : Blo 443779 713657 := bstep (se 2 (by rfl) ⟨267621, by rfl⟩ : syracuseStep 713657 = 535243) B535243
theorem B844843 : Blo 443779 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B1926433 : Blo 443779 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B2417957 : Blo 443779 2417957 := bstep (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) B453367
theorem B1500551 : Blo 443779 1500551 := bstep (se 1 (by rfl) ⟨1125413, by rfl⟩ : syracuseStep 1500551 = 2250827) B2250827
theorem B2549177 : Blo 443779 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B1697233 : Blo 443779 1697233 := bstep (se 2 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 1697233 = 1272925) B1272925
theorem B1631981 : Blo 443779 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B1500929 : Blo 443779 1500929 := bstep (se 2 (by rfl) ⟨562848, by rfl⟩ : syracuseStep 1500929 = 1125697) B1125697
theorem B1697537 : Blo 443779 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B4351781 : Blo 443779 4351781 := bstep (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) B815959
theorem B1271639 : Blo 443779 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B14444405 : Blo 443779 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B1632209 : Blo 443779 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B2254877 : Blo 443779 2254877 := bstep (se 3 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 2254877 = 845579) B845579
theorem B845959 : Blo 443779 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1599689 : Blo 443779 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1697993 : Blo 443779 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B3467501 : Blo 443779 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B1599745 : Blo 443779 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B1599803 : Blo 443779 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B1599859 : Blo 443779 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B3795335 : Blo 443779 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B2255363 : Blo 443779 2255363 := bstep (se 1 (by rfl) ⟨1691522, by rfl⟩ : syracuseStep 2255363 = 3383045) B3383045
theorem B1501739 : Blo 443779 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B1075799 : Blo 443779 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B846521 : Blo 443779 846521 := bstep (se 2 (by rfl) ⟨317445, by rfl⟩ : syracuseStep 846521 = 634891) B634891
theorem B5434127 : Blo 443779 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B2845529 : Blo 443779 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B748919 : Blo 443779 748919 := bstep (se 1 (by rfl) ⟨561689, by rfl⟩ : syracuseStep 748919 = 1123379) B1123379
theorem B716303 : Blo 443779 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B2289239 : Blo 443779 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B749371 : Blo 443779 749371 := bstep (se 1 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 749371 = 1124057) B1124057
theorem B1503035 : Blo 443779 1503035 := bstep (se 1 (by rfl) ⟨1127276, by rfl⟩ : syracuseStep 1503035 = 2254553) B2254553
theorem B847675 : Blo 443779 847675 := bstep (se 1 (by rfl) ⟨635756, by rfl⟩ : syracuseStep 847675 = 1271513) B1271513
theorem B749513 : Blo 443779 749513 := bstep (se 2 (by rfl) ⟨281067, by rfl⟩ : syracuseStep 749513 = 562135) B562135
theorem B2256983 : Blo 443779 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B1503521 : Blo 443779 1503521 := bstep (se 2 (by rfl) ⟨563820, by rfl⟩ : syracuseStep 1503521 = 1127641) B1127641
theorem B848161 : Blo 443779 848161 := bstep (se 2 (by rfl) ⟨318060, by rfl⟩ : syracuseStep 848161 = 636121) B636121
theorem B1274383 : Blo 443779 1274383 := bstep (se 1 (by rfl) ⟨955787, by rfl⟩ : syracuseStep 1274383 = 1911575) B1911575
theorem B1602109 : Blo 443779 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B2257469 : Blo 443779 2257469 := bstep (se 3 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 2257469 = 846551) B846551
theorem B1274429 : Blo 443779 1274429 := bstep (se 3 (by rfl) ⟨238955, by rfl⟩ : syracuseStep 1274429 = 477911) B477911
theorem B750215 : Blo 443779 750215 := bstep (se 1 (by rfl) ⟨562661, by rfl⟩ : syracuseStep 750215 = 1125323) B1125323
theorem B5731033 : Blo 443779 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B1504115 : Blo 443779 1504115 := bstep (se 1 (by rfl) ⟨1128086, by rfl⟩ : syracuseStep 1504115 = 2256173) B2256173
theorem B1274771 : Blo 443779 1274771 := bstep (se 1 (by rfl) ⟨956078, by rfl⟩ : syracuseStep 1274771 = 1912157) B1912157
theorem B750863 : Blo 443779 750863 := bstep (se 1 (by rfl) ⟨563147, by rfl⟩ : syracuseStep 750863 = 1126295) B1126295
theorem B1209659 : Blo 443779 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B849467 : Blo 443779 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B751403 : Blo 443779 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B19363697 : Blo 443779 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B849953 : Blo 443779 849953 := bstep (se 2 (by rfl) ⟨318732, by rfl⟩ : syracuseStep 849953 = 637465) B637465
theorem B751801 : Blo 443779 751801 := bstep (se 2 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 751801 = 563851) B563851
theorem B2259251 : Blo 443779 2259251 := bstep (se 1 (by rfl) ⟨1694438, by rfl⟩ : syracuseStep 2259251 = 3388877) B3388877
theorem B1603955 : Blo 443779 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B2259575 : Blo 443779 2259575 := bstep (se 1 (by rfl) ⟨1694681, by rfl⟩ : syracuseStep 2259575 = 3389363) B3389363
theorem B1833673 : Blo 443779 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B752503 : Blo 443779 752503 := bstep (se 1 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 752503 = 1128755) B1128755
theorem B752699 : Blo 443779 752699 := bstep (se 1 (by rfl) ⟨564524, by rfl⟩ : syracuseStep 752699 = 1129049) B1129049
theorem B1604879 : Blo 443779 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B1506707 : Blo 443779 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B753097 : Blo 443779 753097 := bstep (se 2 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 753097 = 564823) B564823
theorem B1900093 : Blo 443779 1900093 := bstep (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) B712535
theorem B2260547 : Blo 443779 2260547 := bstep (se 1 (by rfl) ⟨1695410, by rfl⟩ : syracuseStep 2260547 = 3390821) B3390821
theorem B3440357 : Blo 443779 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B1605511 : Blo 443779 1605511 := bstep (se 1 (by rfl) ⟨1204133, by rfl⟩ : syracuseStep 1605511 = 2408267) B2408267
theorem B2260871 : Blo 443779 2260871 := bstep (se 1 (by rfl) ⟨1695653, by rfl⟩ : syracuseStep 2260871 = 3391307) B3391307
theorem B1900435 : Blo 443779 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B950201 : Blo 443779 950201 := bstep (se 2 (by rfl) ⟨356325, by rfl⟩ : syracuseStep 950201 = 712651) B712651
theorem B12058571 : Blo 443779 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B753671 : Blo 443779 753671 := bstep (se 1 (by rfl) ⟨565253, by rfl⟩ : syracuseStep 753671 = 1130507) B1130507
theorem B13730123 : Blo 443779 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B2031959 : Blo 443779 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B754015 : Blo 443779 754015 := bstep (se 1 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 754015 = 1131023) B1131023
theorem B10322275 : Blo 443779 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B1147279 : Blo 443779 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B754103 : Blo 443779 754103 := bstep (se 1 (by rfl) ⟨565577, by rfl⟩ : syracuseStep 754103 = 1131155) B1131155
theorem B1901495 : Blo 443779 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B754697 : Blo 443779 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B1803379 : Blo 443779 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B3048619 : Blo 443779 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B754859 : Blo 443779 754859 := bstep (se 1 (by rfl) ⟨566144, by rfl⟩ : syracuseStep 754859 = 1132289) B1132289
theorem B1017193 : Blo 443779 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B7210403 : Blo 443779 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B4326857 : Blo 443779 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B2262491 : Blo 443779 2262491 := bstep (se 1 (by rfl) ⟨1696868, by rfl⟩ : syracuseStep 2262491 = 3393737) B3393737
theorem B3671563 : Blo 443779 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B755257 : Blo 443779 755257 := bstep (se 2 (by rfl) ⟨283221, by rfl⟩ : syracuseStep 755257 = 566443) B566443
theorem B3376727 : Blo 443779 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B1607357 : Blo 443779 1607357 := bstep (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) B602759
theorem B755399 : Blo 443779 755399 := bstep (se 1 (by rfl) ⟨566549, by rfl⟩ : syracuseStep 755399 = 1133099) B1133099
theorem B755561 : Blo 443779 755561 := bstep (se 2 (by rfl) ⟨283335, by rfl⟩ : syracuseStep 755561 = 566671) B566671
theorem B722875 : Blo 443779 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B2197441 : Blo 443779 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B2262977 : Blo 443779 2262977 := bstep (se 2 (by rfl) ⟨848616, by rfl⟩ : syracuseStep 2262977 = 1697233) B1697233
theorem B9865223 : Blo 443779 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1378361 : Blo 443779 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B1509623 : Blo 443779 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B5507531 : Blo 443779 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B1903085 : Blo 443779 1903085 := bstep (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) B713657
theorem B1509947 : Blo 443779 1509947 := bstep (se 1 (by rfl) ⟨1132460, by rfl⟩ : syracuseStep 1509947 = 2264921) B2264921
theorem B1510217 : Blo 443779 1510217 := bstep (se 2 (by rfl) ⟨566331, by rfl⟩ : syracuseStep 1510217 = 1132663) B1132663
theorem B953183 : Blo 443779 953183 := bstep (se 1 (by rfl) ⟨714887, by rfl⟩ : syracuseStep 953183 = 1429775) B1429775
theorem B1805165 : Blo 443779 1805165 := bstep (se 3 (by rfl) ⟨338468, by rfl⟩ : syracuseStep 1805165 = 676937) B676937
theorem B2067383 : Blo 443779 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B2132993 : Blo 443779 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B2133145 : Blo 443779 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B1903769 : Blo 443779 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B2723291 : Blo 443779 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B14650955 : Blo 443779 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B10817347 : Blo 443779 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B4886459 : Blo 443779 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B2265245 : Blo 443779 2265245 := bstep (se 3 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 2265245 = 849467) B849467
theorem B1282999 : Blo 443779 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B759145 : Blo 443779 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B8131985 : Blo 443779 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B2266541 : Blo 443779 2266541 := bstep (se 3 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 2266541 = 849953) B849953
theorem B2135591 : Blo 443779 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B562727 : Blo 443779 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B563051 : Blo 443779 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B3381101 : Blo 443779 3381101 := bstep (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) B1267913
theorem B2136145 : Blo 443779 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B2136221 : Blo 443779 2136221 := bstep (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) B801083
theorem B1611971 : Blo 443779 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B7641377 : Blo 443779 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B1087987 : Blo 443779 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B2530223 : Blo 443779 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B3611621 : Blo 443779 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B2759681 : Blo 443779 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B564347 : Blo 443779 564347 := bstep (se 1 (by rfl) ⟨423260, by rfl⟩ : syracuseStep 564347 = 846521) B846521
theorem B4300121 : Blo 443779 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B9182645 : Blo 443779 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B499279 : Blo 443779 499279 := bstep (se 1 (by rfl) ⟨374459, by rfl⟩ : syracuseStep 499279 = 748919) B748919
theorem B3219385 : Blo 443779 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B499675 : Blo 443779 499675 := bstep (se 1 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 499675 = 749513) B749513
theorem B500143 : Blo 443779 500143 := bstep (se 1 (by rfl) ⟨375107, by rfl⟩ : syracuseStep 500143 = 750215) B750215
theorem B3384017 : Blo 443779 3384017 := bstep (se 2 (by rfl) ⟨1269006, by rfl⟩ : syracuseStep 3384017 = 2538013) B2538013
theorem B1909457 : Blo 443779 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B500575 : Blo 443779 500575 := bstep (se 1 (by rfl) ⟨375431, by rfl⟩ : syracuseStep 500575 = 750863) B750863
theorem B3089335 : Blo 443779 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B500935 : Blo 443779 500935 := bstep (se 1 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 500935 = 751403) B751403
theorem B1910141 : Blo 443779 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B1123865 : Blo 443779 1123865 := bstep (se 2 (by rfl) ⟨421449, by rfl⟩ : syracuseStep 1123865 = 842899) B842899
theorem B2827997 : Blo 443779 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B501799 : Blo 443779 501799 := bstep (se 1 (by rfl) ⟨376349, by rfl⟩ : syracuseStep 501799 = 752699) B752699
theorem B763961 : Blo 443779 763961 := bstep (se 2 (by rfl) ⟨286485, by rfl⟩ : syracuseStep 763961 = 572971) B572971
theorem B2533457 : Blo 443779 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B665723 : Blo 443779 665723 := bstep (se 1 (by rfl) ⟨499292, by rfl⟩ : syracuseStep 665723 = 998585) B998585
theorem B6400133 : Blo 443779 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B17410229 : Blo 443779 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B665849 : Blo 443779 665849 := bstep (se 2 (by rfl) ⟨249693, by rfl⟩ : syracuseStep 665849 = 499387) B499387
theorem B665951 : Blo 443779 665951 := bstep (se 1 (by rfl) ⟨499463, by rfl⟩ : syracuseStep 665951 = 998927) B998927
theorem B665963 : Blo 443779 665963 := bstep (se 1 (by rfl) ⟨499472, by rfl⟩ : syracuseStep 665963 = 998945) B998945
theorem B2140681 : Blo 443779 2140681 := bstep (se 2 (by rfl) ⟨802755, by rfl⟩ : syracuseStep 2140681 = 1605511) B1605511
theorem B2533913 : Blo 443779 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B32156189 : Blo 443779 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B666191 : Blo 443779 666191 := bstep (se 1 (by rfl) ⟨499643, by rfl⟩ : syracuseStep 666191 = 999287) B999287
theorem B633467 : Blo 443779 633467 := bstep (se 1 (by rfl) ⟨475100, by rfl⟩ : syracuseStep 633467 = 950201) B950201
theorem B666311 : Blo 443779 666311 := bstep (se 1 (by rfl) ⟨499733, by rfl⟩ : syracuseStep 666311 = 999467) B999467
theorem B666473 : Blo 443779 666473 := bstep (se 2 (by rfl) ⟨249927, by rfl⟩ : syracuseStep 666473 = 499855) B499855
theorem B666551 : Blo 443779 666551 := bstep (se 1 (by rfl) ⟨499913, by rfl⟩ : syracuseStep 666551 = 999827) B999827
theorem B666587 : Blo 443779 666587 := bstep (se 1 (by rfl) ⟨499940, by rfl⟩ : syracuseStep 666587 = 999881) B999881
theorem B3386447 : Blo 443779 3386447 := bstep (se 1 (by rfl) ⟨2539835, by rfl⟩ : syracuseStep 3386447 = 5079671) B5079671
theorem B634105 : Blo 443779 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B667055 : Blo 443779 667055 := bstep (se 1 (by rfl) ⟨500291, by rfl⟩ : syracuseStep 667055 = 1000583) B1000583
theorem B667145 : Blo 443779 667145 := bstep (se 2 (by rfl) ⟨250179, by rfl⟩ : syracuseStep 667145 = 500359) B500359
theorem B667175 : Blo 443779 667175 := bstep (se 1 (by rfl) ⟨500381, by rfl⟩ : syracuseStep 667175 = 1000763) B1000763
theorem B667259 : Blo 443779 667259 := bstep (se 1 (by rfl) ⟨500444, by rfl⟩ : syracuseStep 667259 = 1000889) B1000889
theorem B503419 : Blo 443779 503419 := bstep (se 1 (by rfl) ⟨377564, by rfl⟩ : syracuseStep 503419 = 755129) B755129
theorem B667385 : Blo 443779 667385 := bstep (se 2 (by rfl) ⟨250269, by rfl⟩ : syracuseStep 667385 = 500539) B500539
theorem B765769 : Blo 443779 765769 := bstep (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) B574327
theorem B667487 : Blo 443779 667487 := bstep (se 1 (by rfl) ⟨500615, by rfl⟩ : syracuseStep 667487 = 1001231) B1001231
theorem B667499 : Blo 443779 667499 := bstep (se 1 (by rfl) ⟨500624, by rfl⟩ : syracuseStep 667499 = 1001249) B1001249
theorem B1126457 : Blo 443779 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B667727 : Blo 443779 667727 := bstep (se 1 (by rfl) ⟨500795, by rfl⟩ : syracuseStep 667727 = 1001591) B1001591
theorem B667847 : Blo 443779 667847 := bstep (se 1 (by rfl) ⟨500885, by rfl⟩ : syracuseStep 667847 = 1001771) B1001771
theorem B3649853 : Blo 443779 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B668009 : Blo 443779 668009 := bstep (se 2 (by rfl) ⟨250503, by rfl⟩ : syracuseStep 668009 = 501007) B501007
theorem B2568577 : Blo 443779 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B668087 : Blo 443779 668087 := bstep (se 1 (by rfl) ⟨501065, by rfl⟩ : syracuseStep 668087 = 1002131) B1002131
theorem B668123 : Blo 443779 668123 := bstep (se 1 (by rfl) ⟨501092, by rfl⟩ : syracuseStep 668123 = 1002185) B1002185
theorem B602975 : Blo 443779 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B668591 : Blo 443779 668591 := bstep (se 1 (by rfl) ⟨501443, by rfl⟩ : syracuseStep 668591 = 1002887) B1002887
theorem B668681 : Blo 443779 668681 := bstep (se 2 (by rfl) ⟨250755, by rfl⟩ : syracuseStep 668681 = 501511) B501511
theorem B668711 : Blo 443779 668711 := bstep (se 1 (by rfl) ⟨501533, by rfl⟩ : syracuseStep 668711 = 1003067) B1003067
theorem B668795 : Blo 443779 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B668921 : Blo 443779 668921 := bstep (se 2 (by rfl) ⟨250845, by rfl⟩ : syracuseStep 668921 = 501691) B501691
theorem B669023 : Blo 443779 669023 := bstep (se 1 (by rfl) ⟨501767, by rfl⟩ : syracuseStep 669023 = 1003535) B1003535
theorem B669035 : Blo 443779 669035 := bstep (se 1 (by rfl) ⟨501776, by rfl⟩ : syracuseStep 669035 = 1003553) B1003553
theorem B2536829 : Blo 443779 2536829 := bstep (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) B951311
theorem B5813765 : Blo 443779 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B1127945 : Blo 443779 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B669263 : Blo 443779 669263 := bstep (se 1 (by rfl) ⟨501947, by rfl⟩ : syracuseStep 669263 = 1003895) B1003895
theorem B669383 : Blo 443779 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B669545 : Blo 443779 669545 := bstep (se 2 (by rfl) ⟨251079, by rfl⟩ : syracuseStep 669545 = 502159) B502159
theorem B1685357 : Blo 443779 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B800695 : Blo 443779 800695 := bstep (se 1 (by rfl) ⟨600521, by rfl⟩ : syracuseStep 800695 = 1201043) B1201043
theorem B669623 : Blo 443779 669623 := bstep (se 1 (by rfl) ⟨502217, by rfl⟩ : syracuseStep 669623 = 1004435) B1004435
theorem B669659 : Blo 443779 669659 := bstep (se 1 (by rfl) ⟨502244, by rfl⟩ : syracuseStep 669659 = 1004489) B1004489
theorem B3225757 : Blo 443779 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B3389849 : Blo 443779 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B670127 : Blo 443779 670127 := bstep (se 1 (by rfl) ⟨502595, by rfl⟩ : syracuseStep 670127 = 1005191) B1005191
theorem B670217 : Blo 443779 670217 := bstep (se 2 (by rfl) ⟨251331, by rfl⟩ : syracuseStep 670217 = 502663) B502663
theorem B1686041 : Blo 443779 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B1686055 : Blo 443779 1686055 := bstep (se 1 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 1686055 = 2529083) B2529083
theorem B670247 : Blo 443779 670247 := bstep (se 1 (by rfl) ⟨502685, by rfl⟩ : syracuseStep 670247 = 1005371) B1005371
theorem B572027 : Blo 443779 572027 := bstep (se 1 (by rfl) ⟨429020, by rfl⟩ : syracuseStep 572027 = 858041) B858041
theorem B670331 : Blo 443779 670331 := bstep (se 1 (by rfl) ⟨502748, by rfl⟩ : syracuseStep 670331 = 1005497) B1005497
theorem B1129099 : Blo 443779 1129099 := bstep (se 1 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 1129099 = 1693649) B1693649
theorem B1424071 : Blo 443779 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B2898641 : Blo 443779 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B670457 : Blo 443779 670457 := bstep (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) B502843
theorem B670559 : Blo 443779 670559 := bstep (se 1 (by rfl) ⟨502919, by rfl⟩ : syracuseStep 670559 = 1005839) B1005839
theorem B670571 : Blo 443779 670571 := bstep (se 1 (by rfl) ⟨502928, by rfl⟩ : syracuseStep 670571 = 1005857) B1005857
theorem B3226475 : Blo 443779 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B52312949 : Blo 443779 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B1129403 : Blo 443779 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B965711 : Blo 443779 965711 := bstep (se 1 (by rfl) ⟨724283, by rfl⟩ : syracuseStep 965711 = 1448567) B1448567
theorem B670799 : Blo 443779 670799 := bstep (se 1 (by rfl) ⟨503099, by rfl⟩ : syracuseStep 670799 = 1006199) B1006199
theorem B670919 : Blo 443779 670919 := bstep (se 1 (by rfl) ⟨503189, by rfl⟩ : syracuseStep 670919 = 1006379) B1006379
theorem B1686845 : Blo 443779 1686845 := bstep (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) B632567
theorem B802121 : Blo 443779 802121 := bstep (se 2 (by rfl) ⟨300795, by rfl⟩ : syracuseStep 802121 = 601591) B601591
theorem B671081 : Blo 443779 671081 := bstep (se 2 (by rfl) ⟨251655, by rfl⟩ : syracuseStep 671081 = 503311) B503311
theorem B671159 : Blo 443779 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B2538971 : Blo 443779 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B671195 : Blo 443779 671195 := bstep (se 1 (by rfl) ⟨503396, by rfl⟩ : syracuseStep 671195 = 1006793) B1006793
theorem B1687027 : Blo 443779 1687027 := bstep (se 1 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 1687027 = 2530541) B2530541
theorem B999035 : Blo 443779 999035 := bstep (se 1 (by rfl) ⟨749276, by rfl⟩ : syracuseStep 999035 = 1498553) B1498553
theorem B1130183 : Blo 443779 1130183 := bstep (se 1 (by rfl) ⟨847637, by rfl⟩ : syracuseStep 1130183 = 1695275) B1695275
theorem B999161 : Blo 443779 999161 := bstep (se 2 (by rfl) ⟨374685, by rfl⟩ : syracuseStep 999161 = 749371) B749371
theorem B1130233 : Blo 443779 1130233 := bstep (se 2 (by rfl) ⟨423837, by rfl⟩ : syracuseStep 1130233 = 847675) B847675
theorem B671663 : Blo 443779 671663 := bstep (se 1 (by rfl) ⟨503747, by rfl⟩ : syracuseStep 671663 = 1007495) B1007495
theorem B999431 : Blo 443779 999431 := bstep (se 1 (by rfl) ⟨749573, by rfl⟩ : syracuseStep 999431 = 1499147) B1499147
theorem B999503 : Blo 443779 999503 := bstep (se 1 (by rfl) ⟨749627, by rfl⟩ : syracuseStep 999503 = 1499255) B1499255
theorem B3391793 : Blo 443779 3391793 := bstep (se 2 (by rfl) ⟨1271922, by rfl⟩ : syracuseStep 3391793 = 2543845) B2543845
theorem B1130881 : Blo 443779 1130881 := bstep (se 2 (by rfl) ⟨424080, by rfl⟩ : syracuseStep 1130881 = 848161) B848161
theorem B999899 : Blo 443779 999899 := bstep (se 1 (by rfl) ⟨749924, by rfl⟩ : syracuseStep 999899 = 1499849) B1499849
theorem B1688273 : Blo 443779 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1000367 : Blo 443779 1000367 := bstep (se 1 (by rfl) ⟨750275, by rfl⟩ : syracuseStep 1000367 = 1500551) B1500551
theorem B6439985 : Blo 443779 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B1000619 : Blo 443779 1000619 := bstep (se 1 (by rfl) ⟨750464, by rfl⟩ : syracuseStep 1000619 = 1500929) B1500929
theorem B902315 : Blo 443779 902315 := bstep (se 1 (by rfl) ⟨676736, by rfl⟩ : syracuseStep 902315 = 1353473) B1353473
theorem B1131691 : Blo 443779 1131691 := bstep (se 1 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 1131691 = 1697537) B1697537
theorem B2901187 : Blo 443779 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B2540747 : Blo 443779 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B15385841 : Blo 443779 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B1688957 : Blo 443779 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B443823 : Blo 443779 443823 := bstep (se 1 (by rfl) ⟨332867, by rfl⟩ : syracuseStep 443823 = 665735) B665735
theorem B443847 : Blo 443779 443847 := bstep (se 1 (by rfl) ⟨332885, by rfl⟩ : syracuseStep 443847 = 665771) B665771
theorem B1066459 : Blo 443779 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B443867 : Blo 443779 443867 := bstep (se 1 (by rfl) ⟨332900, by rfl⟩ : syracuseStep 443867 = 665801) B665801
theorem B1131995 : Blo 443779 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B2311667 : Blo 443779 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B1066535 : Blo 443779 1066535 := bstep (se 1 (by rfl) ⟨799901, by rfl⟩ : syracuseStep 1066535 = 1599803) B1599803
theorem B443943 : Blo 443779 443943 := bstep (se 1 (by rfl) ⟨332957, by rfl⟩ : syracuseStep 443943 = 665915) B665915
theorem B2868797 : Blo 443779 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B443983 : Blo 443779 443983 := bstep (se 1 (by rfl) ⟨332987, by rfl⟩ : syracuseStep 443983 = 665975) B665975
theorem B443999 : Blo 443779 443999 := bstep (se 1 (by rfl) ⟨332999, by rfl⟩ : syracuseStep 443999 = 665999) B665999
theorem B444027 : Blo 443779 444027 := bstep (se 1 (by rfl) ⟨333020, by rfl⟩ : syracuseStep 444027 = 666041) B666041
theorem B2541203 : Blo 443779 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B444079 : Blo 443779 444079 := bstep (se 1 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 444079 = 666119) B666119
theorem B444103 : Blo 443779 444103 := bstep (se 1 (by rfl) ⟨333077, by rfl⟩ : syracuseStep 444103 = 666155) B666155
theorem B1001159 : Blo 443779 1001159 := bstep (se 1 (by rfl) ⟨750869, by rfl⟩ : syracuseStep 1001159 = 1501739) B1501739
theorem B444123 : Blo 443779 444123 := bstep (se 1 (by rfl) ⟨333092, by rfl⟩ : syracuseStep 444123 = 666185) B666185
theorem B804601 : Blo 443779 804601 := bstep (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) B603451
theorem B444199 : Blo 443779 444199 := bstep (se 1 (by rfl) ⟨333149, by rfl⟩ : syracuseStep 444199 = 666299) B666299
theorem B444239 : Blo 443779 444239 := bstep (se 1 (by rfl) ⟨333179, by rfl⟩ : syracuseStep 444239 = 666359) B666359
theorem B444255 : Blo 443779 444255 := bstep (se 1 (by rfl) ⟨333191, by rfl⟩ : syracuseStep 444255 = 666383) B666383
theorem B3622751 : Blo 443779 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B444283 : Blo 443779 444283 := bstep (se 1 (by rfl) ⟨333212, by rfl⟩ : syracuseStep 444283 = 666425) B666425
theorem B444335 : Blo 443779 444335 := bstep (se 1 (by rfl) ⟨333251, by rfl⟩ : syracuseStep 444335 = 666503) B666503
theorem B444359 : Blo 443779 444359 := bstep (se 1 (by rfl) ⟨333269, by rfl⟩ : syracuseStep 444359 = 666539) B666539
theorem B444379 : Blo 443779 444379 := bstep (se 1 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 444379 = 666569) B666569
theorem B444455 : Blo 443779 444455 := bstep (se 1 (by rfl) ⟨333341, by rfl⟩ : syracuseStep 444455 = 666683) B666683
theorem B444495 : Blo 443779 444495 := bstep (se 1 (by rfl) ⟨333371, by rfl⟩ : syracuseStep 444495 = 666743) B666743
theorem B444511 : Blo 443779 444511 := bstep (se 1 (by rfl) ⟨333383, by rfl⟩ : syracuseStep 444511 = 666767) B666767
theorem B444539 : Blo 443779 444539 := bstep (se 1 (by rfl) ⟨333404, by rfl⟩ : syracuseStep 444539 = 666809) B666809
theorem B444591 : Blo 443779 444591 := bstep (se 1 (by rfl) ⟨333443, by rfl⟩ : syracuseStep 444591 = 666887) B666887
theorem B444615 : Blo 443779 444615 := bstep (se 1 (by rfl) ⟨333461, by rfl⟩ : syracuseStep 444615 = 666923) B666923
theorem B444635 : Blo 443779 444635 := bstep (se 1 (by rfl) ⟨333476, by rfl⟩ : syracuseStep 444635 = 666953) B666953
theorem B444711 : Blo 443779 444711 := bstep (se 1 (by rfl) ⟨333533, by rfl⟩ : syracuseStep 444711 = 667067) B667067
theorem B444751 : Blo 443779 444751 := bstep (se 1 (by rfl) ⟨333563, by rfl⟩ : syracuseStep 444751 = 667127) B667127
theorem B1689943 : Blo 443779 1689943 := bstep (se 1 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 1689943 = 2534915) B2534915
theorem B444767 : Blo 443779 444767 := bstep (se 1 (by rfl) ⟨333575, by rfl⟩ : syracuseStep 444767 = 667151) B667151
theorem B444795 : Blo 443779 444795 := bstep (se 1 (by rfl) ⟨333596, by rfl⟩ : syracuseStep 444795 = 667193) B667193
theorem B1526159 : Blo 443779 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B444847 : Blo 443779 444847 := bstep (se 1 (by rfl) ⟨333635, by rfl⟩ : syracuseStep 444847 = 667271) B667271
theorem B444871 : Blo 443779 444871 := bstep (se 1 (by rfl) ⟨333653, by rfl⟩ : syracuseStep 444871 = 667307) B667307
theorem B444891 : Blo 443779 444891 := bstep (se 1 (by rfl) ⟨333668, by rfl⟩ : syracuseStep 444891 = 667337) B667337
theorem B1427993 : Blo 443779 1427993 := bstep (se 2 (by rfl) ⟨535497, by rfl⟩ : syracuseStep 1427993 = 1070995) B1070995
theorem B444967 : Blo 443779 444967 := bstep (se 1 (by rfl) ⟨333725, by rfl⟩ : syracuseStep 444967 = 667451) B667451
theorem B1002023 : Blo 443779 1002023 := bstep (se 1 (by rfl) ⟨751517, by rfl⟩ : syracuseStep 1002023 = 1503035) B1503035
theorem B445007 : Blo 443779 445007 := bstep (se 1 (by rfl) ⟨333755, by rfl⟩ : syracuseStep 445007 = 667511) B667511
theorem B445023 : Blo 443779 445023 := bstep (se 1 (by rfl) ⟨333767, by rfl⟩ : syracuseStep 445023 = 667535) B667535
theorem B445051 : Blo 443779 445051 := bstep (se 1 (by rfl) ⟨333788, by rfl⟩ : syracuseStep 445051 = 667577) B667577
theorem B1690247 : Blo 443779 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B445103 : Blo 443779 445103 := bstep (se 1 (by rfl) ⟨333827, by rfl⟩ : syracuseStep 445103 = 667655) B667655
theorem B445127 : Blo 443779 445127 := bstep (se 1 (by rfl) ⟨333845, by rfl⟩ : syracuseStep 445127 = 667691) B667691
theorem B445147 : Blo 443779 445147 := bstep (se 1 (by rfl) ⟨333860, by rfl⟩ : syracuseStep 445147 = 667721) B667721
theorem B445223 : Blo 443779 445223 := bstep (se 1 (by rfl) ⟨333917, by rfl⟩ : syracuseStep 445223 = 667835) B667835
theorem B445263 : Blo 443779 445263 := bstep (se 1 (by rfl) ⟨333947, by rfl⟩ : syracuseStep 445263 = 667895) B667895
theorem B445279 : Blo 443779 445279 := bstep (se 1 (by rfl) ⟨333959, by rfl⟩ : syracuseStep 445279 = 667919) B667919
theorem B1002347 : Blo 443779 1002347 := bstep (se 1 (by rfl) ⟨751760, by rfl⟩ : syracuseStep 1002347 = 1503521) B1503521
theorem B445307 : Blo 443779 445307 := bstep (se 1 (by rfl) ⟨333980, by rfl⟩ : syracuseStep 445307 = 667961) B667961
theorem B1002401 : Blo 443779 1002401 := bstep (se 2 (by rfl) ⟨375900, by rfl⟩ : syracuseStep 1002401 = 751801) B751801
theorem B445359 : Blo 443779 445359 := bstep (se 1 (by rfl) ⟨334019, by rfl⟩ : syracuseStep 445359 = 668039) B668039
theorem B445383 : Blo 443779 445383 := bstep (se 1 (by rfl) ⟨334037, by rfl⟩ : syracuseStep 445383 = 668075) B668075
theorem B445403 : Blo 443779 445403 := bstep (se 1 (by rfl) ⟨334052, by rfl⟩ : syracuseStep 445403 = 668105) B668105
theorem B11455505 : Blo 443779 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B445479 : Blo 443779 445479 := bstep (se 1 (by rfl) ⟨334109, by rfl⟩ : syracuseStep 445479 = 668219) B668219
theorem B1690703 : Blo 443779 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B445519 : Blo 443779 445519 := bstep (se 1 (by rfl) ⟨334139, by rfl⟩ : syracuseStep 445519 = 668279) B668279
theorem B445535 : Blo 443779 445535 := bstep (se 1 (by rfl) ⟨334151, by rfl⟩ : syracuseStep 445535 = 668303) B668303
theorem B445563 : Blo 443779 445563 := bstep (se 1 (by rfl) ⟨334172, by rfl⟩ : syracuseStep 445563 = 668345) B668345
theorem B1756313 : Blo 443779 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B445615 : Blo 443779 445615 := bstep (se 1 (by rfl) ⟨334211, by rfl⟩ : syracuseStep 445615 = 668423) B668423
theorem B445639 : Blo 443779 445639 := bstep (se 1 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 445639 = 668459) B668459
theorem B445659 : Blo 443779 445659 := bstep (se 1 (by rfl) ⟨334244, by rfl⟩ : syracuseStep 445659 = 668489) B668489
theorem B1002743 : Blo 443779 1002743 := bstep (se 1 (by rfl) ⟨752057, by rfl⟩ : syracuseStep 1002743 = 1504115) B1504115
theorem B5295395 : Blo 443779 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B18599203 : Blo 443779 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B445735 : Blo 443779 445735 := bstep (se 1 (by rfl) ⟨334301, by rfl⟩ : syracuseStep 445735 = 668603) B668603
theorem B445775 : Blo 443779 445775 := bstep (se 1 (by rfl) ⟨334331, by rfl⟩ : syracuseStep 445775 = 668663) B668663
theorem B445791 : Blo 443779 445791 := bstep (se 1 (by rfl) ⟨334343, by rfl⟩ : syracuseStep 445791 = 668687) B668687
theorem B445819 : Blo 443779 445819 := bstep (se 1 (by rfl) ⟨334364, by rfl⟩ : syracuseStep 445819 = 668729) B668729
theorem B1265021 : Blo 443779 1265021 := bstep (se 3 (by rfl) ⟨237191, by rfl⟩ : syracuseStep 1265021 = 474383) B474383
theorem B445871 : Blo 443779 445871 := bstep (se 1 (by rfl) ⟨334403, by rfl⟩ : syracuseStep 445871 = 668807) B668807
theorem B445895 : Blo 443779 445895 := bstep (se 1 (by rfl) ⟨334421, by rfl⟩ : syracuseStep 445895 = 668843) B668843
theorem B445915 : Blo 443779 445915 := bstep (se 1 (by rfl) ⟨334436, by rfl⟩ : syracuseStep 445915 = 668873) B668873
theorem B445991 : Blo 443779 445991 := bstep (se 1 (by rfl) ⟨334493, by rfl⟩ : syracuseStep 445991 = 668987) B668987
theorem B446031 : Blo 443779 446031 := bstep (se 1 (by rfl) ⟨334523, by rfl⟩ : syracuseStep 446031 = 669047) B669047
theorem B446047 : Blo 443779 446047 := bstep (se 1 (by rfl) ⟨334535, by rfl⟩ : syracuseStep 446047 = 669071) B669071
theorem B2444897 : Blo 443779 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B446075 : Blo 443779 446075 := bstep (se 1 (by rfl) ⟨334556, by rfl⟩ : syracuseStep 446075 = 669113) B669113
theorem B3395195 : Blo 443779 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B446127 : Blo 443779 446127 := bstep (se 1 (by rfl) ⟨334595, by rfl⟩ : syracuseStep 446127 = 669191) B669191
theorem B446151 : Blo 443779 446151 := bstep (se 1 (by rfl) ⟨334613, by rfl⟩ : syracuseStep 446151 = 669227) B669227
theorem B446171 : Blo 443779 446171 := bstep (se 1 (by rfl) ⟨334628, by rfl⟩ : syracuseStep 446171 = 669257) B669257
theorem B446247 : Blo 443779 446247 := bstep (se 1 (by rfl) ⟨334685, by rfl⟩ : syracuseStep 446247 = 669371) B669371
theorem B1003337 : Blo 443779 1003337 := bstep (se 2 (by rfl) ⟨376251, by rfl⟩ : syracuseStep 1003337 = 752503) B752503
theorem B446287 : Blo 443779 446287 := bstep (se 1 (by rfl) ⟨334715, by rfl⟩ : syracuseStep 446287 = 669431) B669431
theorem B446303 : Blo 443779 446303 := bstep (se 1 (by rfl) ⟨334727, by rfl⟩ : syracuseStep 446303 = 669455) B669455
theorem B446331 : Blo 443779 446331 := bstep (se 1 (by rfl) ⟨334748, by rfl⟩ : syracuseStep 446331 = 669497) B669497
theorem B446383 : Blo 443779 446383 := bstep (se 1 (by rfl) ⟨334787, by rfl⟩ : syracuseStep 446383 = 669575) B669575
theorem B446407 : Blo 443779 446407 := bstep (se 1 (by rfl) ⟨334805, by rfl⟩ : syracuseStep 446407 = 669611) B669611
theorem B446427 : Blo 443779 446427 := bstep (se 1 (by rfl) ⟨334820, by rfl⟩ : syracuseStep 446427 = 669641) B669641
theorem B446503 : Blo 443779 446503 := bstep (se 1 (by rfl) ⟨334877, by rfl⟩ : syracuseStep 446503 = 669755) B669755
theorem B1691705 : Blo 443779 1691705 := bstep (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) B1268779
theorem B446543 : Blo 443779 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B1626193 : Blo 443779 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B446559 : Blo 443779 446559 := bstep (se 1 (by rfl) ⟨334919, by rfl⟩ : syracuseStep 446559 = 669839) B669839
theorem B905339 : Blo 443779 905339 := bstep (se 1 (by rfl) ⟨679004, by rfl⟩ : syracuseStep 905339 = 1358009) B1358009
theorem B446587 : Blo 443779 446587 := bstep (se 1 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 446587 = 669881) B669881
theorem B446639 : Blo 443779 446639 := bstep (se 1 (by rfl) ⟨334979, by rfl⟩ : syracuseStep 446639 = 669959) B669959
theorem B446663 : Blo 443779 446663 := bstep (se 1 (by rfl) ⟨334997, by rfl⟩ : syracuseStep 446663 = 669995) B669995
theorem B446683 : Blo 443779 446683 := bstep (se 1 (by rfl) ⟨335012, by rfl⟩ : syracuseStep 446683 = 670025) B670025
theorem B1069303 : Blo 443779 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B446759 : Blo 443779 446759 := bstep (se 1 (by rfl) ⟨335069, by rfl⟩ : syracuseStep 446759 = 670139) B670139
theorem B446799 : Blo 443779 446799 := bstep (se 1 (by rfl) ⟨335099, by rfl⟩ : syracuseStep 446799 = 670199) B670199
theorem B446815 : Blo 443779 446815 := bstep (se 1 (by rfl) ⟨335111, by rfl⟩ : syracuseStep 446815 = 670223) B670223
theorem B446843 : Blo 443779 446843 := bstep (se 1 (by rfl) ⟨335132, by rfl⟩ : syracuseStep 446843 = 670265) B670265
theorem B446895 : Blo 443779 446895 := bstep (se 1 (by rfl) ⟨335171, by rfl⟩ : syracuseStep 446895 = 670343) B670343
theorem B446919 : Blo 443779 446919 := bstep (se 1 (by rfl) ⟨335189, by rfl⟩ : syracuseStep 446919 = 670379) B670379
theorem B446939 : Blo 443779 446939 := bstep (se 1 (by rfl) ⟨335204, by rfl⟩ : syracuseStep 446939 = 670409) B670409
theorem B447015 : Blo 443779 447015 := bstep (se 1 (by rfl) ⟨335261, by rfl⟩ : syracuseStep 447015 = 670523) B670523
theorem B447055 : Blo 443779 447055 := bstep (se 1 (by rfl) ⟨335291, by rfl⟩ : syracuseStep 447055 = 670583) B670583
theorem B447071 : Blo 443779 447071 := bstep (se 1 (by rfl) ⟨335303, by rfl⟩ : syracuseStep 447071 = 670607) B670607
theorem B1004129 : Blo 443779 1004129 := bstep (se 2 (by rfl) ⟨376548, by rfl⟩ : syracuseStep 1004129 = 753097) B753097
theorem B447099 : Blo 443779 447099 := bstep (se 1 (by rfl) ⟨335324, by rfl⟩ : syracuseStep 447099 = 670649) B670649
theorem B447151 : Blo 443779 447151 := bstep (se 1 (by rfl) ⟨335363, by rfl⟩ : syracuseStep 447151 = 670727) B670727
theorem B1692359 : Blo 443779 1692359 := bstep (se 1 (by rfl) ⟨1269269, by rfl⟩ : syracuseStep 1692359 = 2538539) B2538539
theorem B447175 : Blo 443779 447175 := bstep (se 1 (by rfl) ⟨335381, by rfl⟩ : syracuseStep 447175 = 670763) B670763
theorem B447195 : Blo 443779 447195 := bstep (se 1 (by rfl) ⟨335396, by rfl⟩ : syracuseStep 447195 = 670793) B670793
theorem B447271 : Blo 443779 447271 := bstep (se 1 (by rfl) ⟨335453, by rfl⟩ : syracuseStep 447271 = 670907) B670907
theorem B447311 : Blo 443779 447311 := bstep (se 1 (by rfl) ⟨335483, by rfl⟩ : syracuseStep 447311 = 670967) B670967
theorem B1069919 : Blo 443779 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B447327 : Blo 443779 447327 := bstep (se 1 (by rfl) ⟨335495, by rfl⟩ : syracuseStep 447327 = 670991) B670991
theorem B447355 : Blo 443779 447355 := bstep (se 1 (by rfl) ⟨335516, by rfl⟩ : syracuseStep 447355 = 671033) B671033
theorem B447407 : Blo 443779 447407 := bstep (se 1 (by rfl) ⟨335555, by rfl⟩ : syracuseStep 447407 = 671111) B671111
theorem B1004471 : Blo 443779 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B447431 : Blo 443779 447431 := bstep (se 1 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 447431 = 671147) B671147
theorem B447451 : Blo 443779 447451 := bstep (se 1 (by rfl) ⟨335588, by rfl⟩ : syracuseStep 447451 = 671177) B671177
theorem B447527 : Blo 443779 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B447567 : Blo 443779 447567 := bstep (se 1 (by rfl) ⟨335675, by rfl⟩ : syracuseStep 447567 = 671351) B671351
theorem B447583 : Blo 443779 447583 := bstep (se 1 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 447583 = 671375) B671375
theorem B906337 : Blo 443779 906337 := bstep (se 2 (by rfl) ⟨339876, by rfl⟩ : syracuseStep 906337 = 679753) B679753
theorem B447611 : Blo 443779 447611 := bstep (se 1 (by rfl) ⟨335708, by rfl⟩ : syracuseStep 447611 = 671417) B671417
theorem B447663 : Blo 443779 447663 := bstep (se 1 (by rfl) ⟨335747, by rfl⟩ : syracuseStep 447663 = 671495) B671495
theorem B447687 : Blo 443779 447687 := bstep (se 1 (by rfl) ⟨335765, by rfl⟩ : syracuseStep 447687 = 671531) B671531
theorem B7623881 : Blo 443779 7623881 := bstep (se 2 (by rfl) ⟨2858955, by rfl⟩ : syracuseStep 7623881 = 5717911) B5717911
theorem B447707 : Blo 443779 447707 := bstep (se 1 (by rfl) ⟨335780, by rfl⟩ : syracuseStep 447707 = 671561) B671561
theorem B1005065 : Blo 443779 1005065 := bstep (se 2 (by rfl) ⟨376899, by rfl⟩ : syracuseStep 1005065 = 753799) B753799
theorem B1693331 : Blo 443779 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B4282055 : Blo 443779 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B1005407 : Blo 443779 1005407 := bstep (se 1 (by rfl) ⟨754055, by rfl⟩ : syracuseStep 1005407 = 1508111) B1508111
theorem B1005587 : Blo 443779 1005587 := bstep (se 1 (by rfl) ⟨754190, by rfl⟩ : syracuseStep 1005587 = 1508381) B1508381
theorem B1431631 : Blo 443779 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B4053149 : Blo 443779 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1005929 : Blo 443779 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B580135 : Blo 443779 580135 := bstep (se 1 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 580135 = 870203) B870203
theorem B2251475 : Blo 443779 2251475 := bstep (se 1 (by rfl) ⟨1688606, by rfl⟩ : syracuseStep 2251475 = 3377213) B3377213
theorem B1203119 : Blo 443779 1203119 := bstep (se 1 (by rfl) ⟨902339, by rfl⟩ : syracuseStep 1203119 = 1804679) B1804679
theorem B711607 : Blo 443779 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B1006523 : Blo 443779 1006523 := bstep (se 1 (by rfl) ⟨754892, by rfl⟩ : syracuseStep 1006523 = 1509785) B1509785
theorem B1006649 : Blo 443779 1006649 := bstep (se 2 (by rfl) ⟨377493, by rfl⟩ : syracuseStep 1006649 = 754987) B754987
theorem B1498283 : Blo 443779 1498283 := bstep (se 1 (by rfl) ⟨1123712, by rfl⟩ : syracuseStep 1498283 = 2247425) B2247425
theorem B1269121 : Blo 443779 1269121 := bstep (se 2 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 1269121 = 951841) B951841
theorem B1006991 : Blo 443779 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B6413741 : Blo 443779 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B2416225 : Blo 443779 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1269371 : Blo 443779 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B1498823 : Blo 443779 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B1007315 : Blo 443779 1007315 := bstep (se 1 (by rfl) ⟨755486, by rfl⟩ : syracuseStep 1007315 = 1510973) B1510973
theorem B2547719 : Blo 443779 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B843833 : Blo 443779 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B6447185 : Blo 443779 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B12312931 : Blo 443779 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B1073513 : Blo 443779 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B844175 : Blo 443779 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B1499687 : Blo 443779 1499687 := bstep (se 1 (by rfl) ⟨1124765, by rfl⟩ : syracuseStep 1499687 = 2249531) B2249531
theorem B1499795 : Blo 443779 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B1434323 : Blo 443779 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1500011 : Blo 443779 1500011 := bstep (se 1 (by rfl) ⟨1125008, by rfl⟩ : syracuseStep 1500011 = 2250017) B2250017
theorem B1500065 : Blo 443779 1500065 := bstep (se 2 (by rfl) ⟨562524, by rfl⟩ : syracuseStep 1500065 = 1125049) B1125049
theorem B2253743 : Blo 443779 2253743 := bstep (se 1 (by rfl) ⟨1690307, by rfl⟩ : syracuseStep 2253743 = 3380615) B3380615
theorem B1500659 : Blo 443779 1500659 := bstep (se 1 (by rfl) ⟨1125494, by rfl⟩ : syracuseStep 1500659 = 2250989) B2250989
theorem B6121003 : Blo 443779 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B1206199 : Blo 443779 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B1697719 : Blo 443779 1697719 := bstep (se 1 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 1697719 = 2546579) B2546579
theorem B1501199 : Blo 443779 1501199 := bstep (se 1 (by rfl) ⟨1125899, by rfl⟩ : syracuseStep 1501199 = 2251799) B2251799
theorem B714791 : Blo 443779 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B846035 : Blo 443779 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B1141121 : Blo 443779 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B1698191 : Blo 443779 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B846263 : Blo 443779 846263 := bstep (se 1 (by rfl) ⟨634697, by rfl⟩ : syracuseStep 846263 = 1269395) B1269395
theorem B18278945 : Blo 443779 18278945 := bstep (se 2 (by rfl) ⟨6854604, by rfl⟩ : syracuseStep 18278945 = 13709209) B13709209
theorem B1501793 : Blo 443779 1501793 := bstep (se 2 (by rfl) ⟨563172, by rfl⟩ : syracuseStep 1501793 = 1126345) B1126345
theorem B3337037 : Blo 443779 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B3435493 : Blo 443779 3435493 := bstep (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) B644155
theorem B1699177 : Blo 443779 1699177 := bstep (se 2 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 1699177 = 1274383) B1274383
theorem B2584009 : Blo 443779 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B847417 : Blo 443779 847417 := bstep (se 2 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 847417 = 635563) B635563
theorem B749135 : Blo 443779 749135 := bstep (se 1 (by rfl) ⟨561851, by rfl⟩ : syracuseStep 749135 = 1123703) B1123703
theorem B1699451 : Blo 443779 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B6844121 : Blo 443779 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B847721 : Blo 443779 847721 := bstep (se 2 (by rfl) ⟨317895, by rfl⟩ : syracuseStep 847721 = 635791) B635791
theorem B847759 : Blo 443779 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B9629603 : Blo 443779 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B5402639 : Blo 443779 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B1503251 : Blo 443779 1503251 := bstep (se 1 (by rfl) ⟨1127438, by rfl⟩ : syracuseStep 1503251 = 2254877) B2254877
theorem B1503575 : Blo 443779 1503575 := bstep (se 1 (by rfl) ⟨1127681, by rfl⟩ : syracuseStep 1503575 = 2255363) B2255363
theorem B881039 : Blo 443779 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B749999 : Blo 443779 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B1897019 : Blo 443779 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B750431 : Blo 443779 750431 := bstep (se 1 (by rfl) ⟨562823, by rfl⟩ : syracuseStep 750431 = 1125647) B1125647
theorem B750991 : Blo 443779 750991 := bstep (se 1 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 750991 = 1126487) B1126487
theorem B1504655 : Blo 443779 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B1504979 : Blo 443779 1504979 := bstep (se 1 (by rfl) ⟨1128734, by rfl⟩ : syracuseStep 1504979 = 2257469) B2257469
theorem B849619 : Blo 443779 849619 := bstep (se 1 (by rfl) ⟨637214, by rfl⟩ : syracuseStep 849619 = 1274429) B1274429
theorem B849847 : Blo 443779 849847 := bstep (se 1 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 849847 = 1274771) B1274771
theorem B751673 : Blo 443779 751673 := bstep (se 2 (by rfl) ⟨281877, by rfl⟩ : syracuseStep 751673 = 563755) B563755
theorem B12909131 : Blo 443779 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B752375 : Blo 443779 752375 := bstep (se 1 (by rfl) ⟨564281, by rfl⟩ : syracuseStep 752375 = 1128563) B1128563
theorem B1014601 : Blo 443779 1014601 := bstep (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) B760951
theorem B1604461 : Blo 443779 1604461 := bstep (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) B601673
theorem B1506167 : Blo 443779 1506167 := bstep (se 1 (by rfl) ⟨1129625, by rfl⟩ : syracuseStep 1506167 = 2259251) B2259251
theorem B752719 : Blo 443779 752719 := bstep (se 1 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 752719 = 1129079) B1129079
theorem B1506383 : Blo 443779 1506383 := bstep (se 1 (by rfl) ⟨1129787, by rfl⟩ : syracuseStep 1506383 = 2259575) B2259575
theorem B752969 : Blo 443779 752969 := bstep (se 2 (by rfl) ⟨282363, by rfl⟩ : syracuseStep 752969 = 564727) B564727
theorem B1506761 : Blo 443779 1506761 := bstep (se 2 (by rfl) ⟨565035, by rfl⟩ : syracuseStep 1506761 = 1130071) B1130071
theorem B1507031 : Blo 443779 1507031 := bstep (se 1 (by rfl) ⟨1130273, by rfl⟩ : syracuseStep 1507031 = 2260547) B2260547
theorem B753401 : Blo 443779 753401 := bstep (se 2 (by rfl) ⟨282525, by rfl⟩ : syracuseStep 753401 = 565051) B565051
theorem B2293571 : Blo 443779 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B753583 : Blo 443779 753583 := bstep (se 1 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 753583 = 1130375) B1130375
theorem B1507247 : Blo 443779 1507247 := bstep (se 1 (by rfl) ⟨1130435, by rfl⟩ : syracuseStep 1507247 = 2260871) B2260871
theorem B2261195 : Blo 443779 2261195 := bstep (se 1 (by rfl) ⟨1695896, by rfl⟩ : syracuseStep 2261195 = 3391793) B3391793
theorem B16417241 : Blo 443779 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B13763033 : Blo 443779 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B1507841 : Blo 443779 1507841 := bstep (se 2 (by rfl) ⟨565440, by rfl⟩ : syracuseStep 1507841 = 1130881) B1130881
theorem B4293323 : Blo 443779 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B10257227 : Blo 443779 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B2884571 : Blo 443779 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B1508327 : Blo 443779 1508327 := bstep (se 1 (by rfl) ⟨1131245, by rfl⟩ : syracuseStep 1508327 = 2262491) B2262491
theorem B754663 : Blo 443779 754663 := bstep (se 1 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 754663 = 1131995) B1131995
theorem B1541111 : Blo 443779 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B1508651 : Blo 443779 1508651 := bstep (se 1 (by rfl) ⟨1131488, by rfl⟩ : syracuseStep 1508651 = 2262977) B2262977
theorem B918907 : Blo 443779 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B4064825 : Blo 443779 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B1508921 : Blo 443779 1508921 := bstep (se 2 (by rfl) ⟨565845, by rfl⟩ : syracuseStep 1508921 = 1131691) B1131691
theorem B3868249 : Blo 443779 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B3671687 : Blo 443779 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B951995 : Blo 443779 951995 := bstep (se 1 (by rfl) ⟨713996, by rfl⟩ : syracuseStep 951995 = 1427993) B1427993
theorem B1378255 : Blo 443779 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B7637003 : Blo 443779 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B8161337 : Blo 443779 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B1607933 : Blo 443779 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B9767303 : Blo 443779 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B2263463 : Blo 443779 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B1608265 : Blo 443779 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B2263625 : Blo 443779 2263625 := bstep (se 2 (by rfl) ⟨848859, by rfl⟩ : syracuseStep 2263625 = 1697719) B1697719
theorem B1510163 : Blo 443779 1510163 := bstep (se 1 (by rfl) ⟨1132622, by rfl⟩ : syracuseStep 1510163 = 2265245) B2265245
theorem B2854241 : Blo 443779 2854241 := bstep (se 2 (by rfl) ⟨1070340, by rfl⟩ : syracuseStep 2854241 = 2140681) B2140681
theorem B5082587 : Blo 443779 5082587 := bstep (se 1 (by rfl) ⟨3811940, by rfl⟩ : syracuseStep 5082587 = 7623881) B7623881
theorem B1511027 : Blo 443779 1511027 := bstep (se 1 (by rfl) ⟨1133270, by rfl⟩ : syracuseStep 1511027 = 2266541) B2266541
theorem B2854703 : Blo 443779 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B2265569 : Blo 443779 2265569 := bstep (se 2 (by rfl) ⟨849588, by rfl⟩ : syracuseStep 2265569 = 1699177) B1699177
theorem B3445345 : Blo 443779 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B14423129 : Blo 443779 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B1021025 : Blo 443779 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B562555 : Blo 443779 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B4298123 : Blo 443779 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B2168257 : Blo 443779 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B562783 : Blo 443779 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B956215 : Blo 443779 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B11376773 : Blo 443779 11376773 := bstep (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) B2133145
theorem B4069757 : Blo 443779 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B1710665 : Blo 443779 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B4266755 : Blo 443779 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B11606819 : Blo 443779 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B564023 : Blo 443779 564023 := bstep (se 1 (by rfl) ⟨423017, by rfl⟩ : syracuseStep 564023 = 846035) B846035
theorem B99195749 : Blo 443779 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B760747 : Blo 443779 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B564175 : Blo 443779 564175 := bstep (se 1 (by rfl) ⟨423131, by rfl⟩ : syracuseStep 564175 = 846263) B846263
theorem B21437459 : Blo 443779 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B499423 : Blo 443779 499423 := bstep (se 1 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 499423 = 749135) B749135
theorem B4562747 : Blo 443779 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B565147 : Blo 443779 565147 := bstep (se 1 (by rfl) ⟨423860, by rfl⟩ : syracuseStep 565147 = 847721) B847721
theorem B1908841 : Blo 443779 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B4301009 : Blo 443779 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2433235 : Blo 443779 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B499999 : Blo 443779 499999 := bstep (se 1 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 499999 = 749999) B749999
theorem B500287 : Blo 443779 500287 := bstep (se 1 (by rfl) ⟨375215, by rfl⟩ : syracuseStep 500287 = 750431) B750431
theorem B1450649 : Blo 443779 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B2138989 : Blo 443779 2138989 := bstep (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) B802121
theorem B3875843 : Blo 443779 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B1352801 : Blo 443779 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B2139281 : Blo 443779 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B1123571 : Blo 443779 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B501115 : Blo 443779 501115 := bstep (se 1 (by rfl) ⟨375836, by rfl⟩ : syracuseStep 501115 = 751673) B751673
theorem B3384989 : Blo 443779 3384989 := bstep (se 3 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 3384989 = 1269371) B1269371
theorem B1124027 : Blo 443779 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B501583 : Blo 443779 501583 := bstep (se 1 (by rfl) ⟨376187, by rfl⟩ : syracuseStep 501583 = 752375) B752375
theorem B34875299 : Blo 443779 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B665705 : Blo 443779 665705 := bstep (se 2 (by rfl) ⟨249639, by rfl⟩ : syracuseStep 665705 = 499279) B499279
theorem B3221633 : Blo 443779 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B1124563 : Blo 443779 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B501979 : Blo 443779 501979 := bstep (se 1 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 501979 = 752969) B752969
theorem B666023 : Blo 443779 666023 := bstep (se 1 (by rfl) ⟨499517, by rfl⟩ : syracuseStep 666023 = 999035) B999035
theorem B666107 : Blo 443779 666107 := bstep (se 1 (by rfl) ⟨499580, by rfl⟩ : syracuseStep 666107 = 999161) B999161
theorem B502267 : Blo 443779 502267 := bstep (se 1 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 502267 = 753401) B753401
theorem B666233 : Blo 443779 666233 := bstep (se 2 (by rfl) ⟨249837, by rfl⟩ : syracuseStep 666233 = 499675) B499675
theorem B666287 : Blo 443779 666287 := bstep (se 1 (by rfl) ⟨499715, by rfl⟩ : syracuseStep 666287 = 999431) B999431
theorem B502447 : Blo 443779 502447 := bstep (se 1 (by rfl) ⟨376835, by rfl⟩ : syracuseStep 502447 = 753671) B753671
theorem B666335 : Blo 443779 666335 := bstep (se 1 (by rfl) ⟨499751, by rfl⟩ : syracuseStep 666335 = 999503) B999503
theorem B9153415 : Blo 443779 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B1354639 : Blo 443779 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B502735 : Blo 443779 502735 := bstep (se 1 (by rfl) ⟨377051, by rfl⟩ : syracuseStep 502735 = 754103) B754103
theorem B666599 : Blo 443779 666599 := bstep (se 1 (by rfl) ⟨499949, by rfl⟩ : syracuseStep 666599 = 999899) B999899
theorem B1125515 : Blo 443779 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B666857 : Blo 443779 666857 := bstep (se 2 (by rfl) ⟨250071, by rfl⟩ : syracuseStep 666857 = 500143) B500143
theorem B666911 : Blo 443779 666911 := bstep (se 1 (by rfl) ⟨500183, by rfl⟩ : syracuseStep 666911 = 1000367) B1000367
theorem B503131 : Blo 443779 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B667079 : Blo 443779 667079 := bstep (se 1 (by rfl) ⟨500309, by rfl⟩ : syracuseStep 667079 = 1000619) B1000619
theorem B601543 : Blo 443779 601543 := bstep (se 1 (by rfl) ⟨451157, by rfl⟩ : syracuseStep 601543 = 902315) B902315
theorem B503239 : Blo 443779 503239 := bstep (se 1 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 503239 = 754859) B754859
theorem B1125971 : Blo 443779 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B2862701 : Blo 443779 2862701 := bstep (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) B1073513
theorem B667433 : Blo 443779 667433 := bstep (se 2 (by rfl) ⟨250287, by rfl⟩ : syracuseStep 667433 = 500575) B500575
theorem B667439 : Blo 443779 667439 := bstep (se 1 (by rfl) ⟨500579, by rfl⟩ : syracuseStep 667439 = 1001159) B1001159
theorem B503599 : Blo 443779 503599 := bstep (se 1 (by rfl) ⟨377699, by rfl⟩ : syracuseStep 503599 = 755399) B755399
theorem B503707 : Blo 443779 503707 := bstep (se 1 (by rfl) ⟨377780, by rfl⟩ : syracuseStep 503707 = 755561) B755561
theorem B2404505 : Blo 443779 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B667913 : Blo 443779 667913 := bstep (se 2 (by rfl) ⟨250467, by rfl⟩ : syracuseStep 667913 = 500935) B500935
theorem B668015 : Blo 443779 668015 := bstep (se 1 (by rfl) ⟨501011, by rfl⟩ : syracuseStep 668015 = 1002023) B1002023
theorem B1126831 : Blo 443779 1126831 := bstep (se 1 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 1126831 = 1690247) B1690247
theorem B1356257 : Blo 443779 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B635455 : Blo 443779 635455 := bstep (se 1 (by rfl) ⟨476591, by rfl⟩ : syracuseStep 635455 = 953183) B953183
theorem B668231 : Blo 443779 668231 := bstep (se 1 (by rfl) ⟨501173, by rfl⟩ : syracuseStep 668231 = 1002347) B1002347
theorem B668267 : Blo 443779 668267 := bstep (se 1 (by rfl) ⟨501200, by rfl⟩ : syracuseStep 668267 = 1002401) B1002401
theorem B1421945 : Blo 443779 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1421995 : Blo 443779 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B4895417 : Blo 443779 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B1127135 : Blo 443779 1127135 := bstep (se 1 (by rfl) ⟨845351, by rfl⟩ : syracuseStep 1127135 = 1690703) B1690703
theorem B668495 : Blo 443779 668495 := bstep (se 1 (by rfl) ⟨501371, by rfl⟩ : syracuseStep 668495 = 1002743) B1002743
theorem B1815527 : Blo 443779 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B668891 : Blo 443779 668891 := bstep (se 1 (by rfl) ⟨501668, by rfl⟩ : syracuseStep 668891 = 1003337) B1003337
theorem B963833 : Blo 443779 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B3257639 : Blo 443779 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B1127803 : Blo 443779 1127803 := bstep (se 1 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 1127803 = 1691705) B1691705
theorem B669065 : Blo 443779 669065 := bstep (se 2 (by rfl) ⟨250899, by rfl⟩ : syracuseStep 669065 = 501799) B501799
theorem B603559 : Blo 443779 603559 := bstep (se 1 (by rfl) ⟨452669, by rfl⟩ : syracuseStep 603559 = 905339) B905339
theorem B669419 : Blo 443779 669419 := bstep (se 1 (by rfl) ⟨502064, by rfl⟩ : syracuseStep 669419 = 1004129) B1004129
theorem B1128239 : Blo 443779 1128239 := bstep (se 1 (by rfl) ⟨846179, by rfl⟩ : syracuseStep 1128239 = 1692359) B1692359
theorem B669647 : Blo 443779 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B5421323 : Blo 443779 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B670043 : Blo 443779 670043 := bstep (se 1 (by rfl) ⟨502532, by rfl⟩ : syracuseStep 670043 = 1005065) B1005065
theorem B1423727 : Blo 443779 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B1128887 : Blo 443779 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B670271 : Blo 443779 670271 := bstep (se 1 (by rfl) ⟨502703, by rfl⟩ : syracuseStep 670271 = 1005407) B1005407
theorem B670391 : Blo 443779 670391 := bstep (se 1 (by rfl) ⟨502793, by rfl⟩ : syracuseStep 670391 = 1005587) B1005587
theorem B2702099 : Blo 443779 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B1424147 : Blo 443779 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B7650125 : Blo 443779 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B5094251 : Blo 443779 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B670619 : Blo 443779 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B1686815 : Blo 443779 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B802079 : Blo 443779 802079 := bstep (se 1 (by rfl) ⟨601559, by rfl⟩ : syracuseStep 802079 = 1203119) B1203119
theorem B671015 : Blo 443779 671015 := bstep (se 1 (by rfl) ⟨503261, by rfl⟩ : syracuseStep 671015 = 1006523) B1006523
theorem B2407747 : Blo 443779 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B671099 : Blo 443779 671099 := bstep (se 1 (by rfl) ⟨503324, by rfl⟩ : syracuseStep 671099 = 1006649) B1006649
theorem B1129889 : Blo 443779 1129889 := bstep (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) B847417
theorem B998855 : Blo 443779 998855 := bstep (se 1 (by rfl) ⟨749141, by rfl⟩ : syracuseStep 998855 = 1498283) B1498283
theorem B671225 : Blo 443779 671225 := bstep (se 2 (by rfl) ⟨251709, by rfl⟩ : syracuseStep 671225 = 503419) B503419
theorem B2866747 : Blo 443779 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B671327 : Blo 443779 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B4275827 : Blo 443779 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B999215 : Blo 443779 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B671543 : Blo 443779 671543 := bstep (se 1 (by rfl) ⟨503657, by rfl⟩ : syracuseStep 671543 = 1007315) B1007315
theorem B1130345 : Blo 443779 1130345 := bstep (se 2 (by rfl) ⟨423879, by rfl⟩ : syracuseStep 1130345 = 847759) B847759
theorem B1425737 : Blo 443779 1425737 := bstep (se 2 (by rfl) ⟨534651, by rfl⟩ : syracuseStep 1425737 = 1069303) B1069303
theorem B999791 : Blo 443779 999791 := bstep (se 1 (by rfl) ⟨749843, by rfl⟩ : syracuseStep 999791 = 1499687) B1499687
theorem B999863 : Blo 443779 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B3424769 : Blo 443779 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1000007 : Blo 443779 1000007 := bstep (se 1 (by rfl) ⟨750005, by rfl⟩ : syracuseStep 1000007 = 1500011) B1500011
theorem B1000043 : Blo 443779 1000043 := bstep (se 1 (by rfl) ⟨750032, by rfl⟩ : syracuseStep 1000043 = 1500065) B1500065
theorem B1000439 : Blo 443779 1000439 := bstep (se 1 (by rfl) ⟨750329, by rfl⟩ : syracuseStep 1000439 = 1500659) B1500659
theorem B1885331 : Blo 443779 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1000799 : Blo 443779 1000799 := bstep (se 1 (by rfl) ⟨750599, by rfl⟩ : syracuseStep 1000799 = 1501199) B1501199
theorem B476527 : Blo 443779 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B1688971 : Blo 443779 1688971 := bstep (se 1 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 1688971 = 2533457) B2533457
theorem B443815 : Blo 443779 443815 := bstep (se 1 (by rfl) ⟨332861, by rfl⟩ : syracuseStep 443815 = 665723) B665723
theorem B443899 : Blo 443779 443899 := bstep (se 1 (by rfl) ⟨332924, by rfl⟩ : syracuseStep 443899 = 665849) B665849
theorem B443967 : Blo 443779 443967 := bstep (se 1 (by rfl) ⟨332975, by rfl⟩ : syracuseStep 443967 = 665951) B665951
theorem B443975 : Blo 443779 443975 := bstep (se 1 (by rfl) ⟨332981, by rfl⟩ : syracuseStep 443975 = 665963) B665963
theorem B1132127 : Blo 443779 1132127 := bstep (se 1 (by rfl) ⟨849095, by rfl⟩ : syracuseStep 1132127 = 1698191) B1698191
theorem B1689245 : Blo 443779 1689245 := bstep (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) B633467
theorem B1525405 : Blo 443779 1525405 := bstep (se 3 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 1525405 = 572027) B572027
theorem B1689275 : Blo 443779 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B444127 : Blo 443779 444127 := bstep (se 1 (by rfl) ⟨333095, by rfl⟩ : syracuseStep 444127 = 666191) B666191
theorem B1001195 : Blo 443779 1001195 := bstep (se 1 (by rfl) ⟨750896, by rfl⟩ : syracuseStep 1001195 = 1501793) B1501793
theorem B444207 : Blo 443779 444207 := bstep (se 1 (by rfl) ⟨333155, by rfl⟩ : syracuseStep 444207 = 666311) B666311
theorem B1001321 : Blo 443779 1001321 := bstep (se 2 (by rfl) ⟨375495, by rfl⟩ : syracuseStep 1001321 = 750991) B750991
theorem B444315 : Blo 443779 444315 := bstep (se 1 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 444315 = 666473) B666473
theorem B444367 : Blo 443779 444367 := bstep (se 1 (by rfl) ⟨333275, by rfl⟩ : syracuseStep 444367 = 666551) B666551
theorem B444391 : Blo 443779 444391 := bstep (se 1 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 444391 = 666587) B666587
theorem B1132825 : Blo 443779 1132825 := bstep (se 2 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 1132825 = 849619) B849619
theorem B444703 : Blo 443779 444703 := bstep (se 1 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 444703 = 667055) B667055
theorem B444763 : Blo 443779 444763 := bstep (se 1 (by rfl) ⟨333572, by rfl⟩ : syracuseStep 444763 = 667145) B667145
theorem B444783 : Blo 443779 444783 := bstep (se 1 (by rfl) ⟨333587, by rfl⟩ : syracuseStep 444783 = 667175) B667175
theorem B444839 : Blo 443779 444839 := bstep (se 1 (by rfl) ⟨333629, by rfl⟩ : syracuseStep 444839 = 667259) B667259
theorem B1132967 : Blo 443779 1132967 := bstep (se 1 (by rfl) ⟨849725, by rfl⟩ : syracuseStep 1132967 = 1699451) B1699451
theorem B444923 : Blo 443779 444923 := bstep (se 1 (by rfl) ⟨333692, by rfl⟩ : syracuseStep 444923 = 667385) B667385
theorem B444991 : Blo 443779 444991 := bstep (se 1 (by rfl) ⟨333743, by rfl⟩ : syracuseStep 444991 = 667487) B667487
theorem B444999 : Blo 443779 444999 := bstep (se 1 (by rfl) ⟨333749, by rfl⟩ : syracuseStep 444999 = 667499) B667499
theorem B1067593 : Blo 443779 1067593 := bstep (se 2 (by rfl) ⟨400347, by rfl⟩ : syracuseStep 1067593 = 800695) B800695
theorem B1133129 : Blo 443779 1133129 := bstep (se 2 (by rfl) ⟨424923, by rfl⟩ : syracuseStep 1133129 = 849847) B849847
theorem B7359149 : Blo 443779 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B1002167 : Blo 443779 1002167 := bstep (se 1 (by rfl) ⟨751625, by rfl⟩ : syracuseStep 1002167 = 1503251) B1503251
theorem B445151 : Blo 443779 445151 := bstep (se 1 (by rfl) ⟨333863, by rfl⟩ : syracuseStep 445151 = 667727) B667727
theorem B445231 : Blo 443779 445231 := bstep (se 1 (by rfl) ⟨333923, by rfl⟩ : syracuseStep 445231 = 667847) B667847
theorem B1002383 : Blo 443779 1002383 := bstep (se 1 (by rfl) ⟨751787, by rfl⟩ : syracuseStep 1002383 = 1503575) B1503575
theorem B445339 : Blo 443779 445339 := bstep (se 1 (by rfl) ⟨334004, by rfl⟩ : syracuseStep 445339 = 668009) B668009
theorem B445391 : Blo 443779 445391 := bstep (se 1 (by rfl) ⟨334043, by rfl⟩ : syracuseStep 445391 = 668087) B668087
theorem B445415 : Blo 443779 445415 := bstep (se 1 (by rfl) ⟨334061, by rfl⟩ : syracuseStep 445415 = 668123) B668123
theorem B1264679 : Blo 443779 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B445727 : Blo 443779 445727 := bstep (se 1 (by rfl) ⟨334295, by rfl⟩ : syracuseStep 445727 = 668591) B668591
theorem B445787 : Blo 443779 445787 := bstep (se 1 (by rfl) ⟨334340, by rfl⟩ : syracuseStep 445787 = 668681) B668681
theorem B445807 : Blo 443779 445807 := bstep (se 1 (by rfl) ⟨334355, by rfl⟩ : syracuseStep 445807 = 668711) B668711
theorem B2248073 : Blo 443779 2248073 := bstep (se 2 (by rfl) ⟨843027, by rfl⟩ : syracuseStep 2248073 = 1686055) B1686055
theorem B773513 : Blo 443779 773513 := bstep (se 2 (by rfl) ⟨290067, by rfl⟩ : syracuseStep 773513 = 580135) B580135
theorem B445863 : Blo 443779 445863 := bstep (se 1 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 445863 = 668795) B668795
theorem B445947 : Blo 443779 445947 := bstep (se 1 (by rfl) ⟨334460, by rfl⟩ : syracuseStep 445947 = 668921) B668921
theorem B446015 : Blo 443779 446015 := bstep (se 1 (by rfl) ⟨334511, by rfl⟩ : syracuseStep 446015 = 669023) B669023
theorem B446023 : Blo 443779 446023 := bstep (se 1 (by rfl) ⟨334517, by rfl⟩ : syracuseStep 446023 = 669035) B669035
theorem B1691219 : Blo 443779 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B1003103 : Blo 443779 1003103 := bstep (se 1 (by rfl) ⟨752327, by rfl⟩ : syracuseStep 1003103 = 1504655) B1504655
theorem B446175 : Blo 443779 446175 := bstep (se 1 (by rfl) ⟨334631, by rfl⟩ : syracuseStep 446175 = 669263) B669263
theorem B446255 : Blo 443779 446255 := bstep (se 1 (by rfl) ⟨334691, by rfl⟩ : syracuseStep 446255 = 669383) B669383
theorem B1003319 : Blo 443779 1003319 := bstep (se 1 (by rfl) ⟨752489, by rfl⟩ : syracuseStep 1003319 = 1504979) B1504979
theorem B446363 : Blo 443779 446363 := bstep (se 1 (by rfl) ⟨334772, by rfl⟩ : syracuseStep 446363 = 669545) B669545
theorem B446415 : Blo 443779 446415 := bstep (se 1 (by rfl) ⟨334811, by rfl⟩ : syracuseStep 446415 = 669623) B669623
theorem B446439 : Blo 443779 446439 := bstep (se 1 (by rfl) ⟨334829, by rfl⟩ : syracuseStep 446439 = 669659) B669659
theorem B1003625 : Blo 443779 1003625 := bstep (se 2 (by rfl) ⟨376359, by rfl⟩ : syracuseStep 1003625 = 752719) B752719
theorem B446751 : Blo 443779 446751 := bstep (se 1 (by rfl) ⟨335063, by rfl⟩ : syracuseStep 446751 = 670127) B670127
theorem B446811 : Blo 443779 446811 := bstep (se 1 (by rfl) ⟨335108, by rfl⟩ : syracuseStep 446811 = 670217) B670217
theorem B446831 : Blo 443779 446831 := bstep (se 1 (by rfl) ⟨335123, by rfl⟩ : syracuseStep 446831 = 670247) B670247
theorem B8606087 : Blo 443779 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B446887 : Blo 443779 446887 := bstep (se 1 (by rfl) ⟨335165, by rfl⟩ : syracuseStep 446887 = 670331) B670331
theorem B446971 : Blo 443779 446971 := bstep (se 1 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 446971 = 670457) B670457
theorem B1692161 : Blo 443779 1692161 := bstep (se 2 (by rfl) ⟨634560, by rfl⟩ : syracuseStep 1692161 = 1269121) B1269121
theorem B447039 : Blo 443779 447039 := bstep (se 1 (by rfl) ⟨335279, by rfl⟩ : syracuseStep 447039 = 670559) B670559
theorem B447047 : Blo 443779 447047 := bstep (se 1 (by rfl) ⟨335285, by rfl⟩ : syracuseStep 447047 = 670571) B670571
theorem B2150983 : Blo 443779 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B1004111 : Blo 443779 1004111 := bstep (se 1 (by rfl) ⟨753083, by rfl⟩ : syracuseStep 1004111 = 1506167) B1506167
theorem B2249369 : Blo 443779 2249369 := bstep (se 2 (by rfl) ⟨843513, by rfl⟩ : syracuseStep 2249369 = 1687027) B1687027
theorem B643807 : Blo 443779 643807 := bstep (se 1 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 643807 = 965711) B965711
theorem B1004255 : Blo 443779 1004255 := bstep (se 1 (by rfl) ⟨753191, by rfl⟩ : syracuseStep 1004255 = 1506383) B1506383
theorem B447199 : Blo 443779 447199 := bstep (se 1 (by rfl) ⟨335399, by rfl⟩ : syracuseStep 447199 = 670799) B670799
theorem B447279 : Blo 443779 447279 := bstep (se 1 (by rfl) ⟨335459, by rfl⟩ : syracuseStep 447279 = 670919) B670919
theorem B447387 : Blo 443779 447387 := bstep (se 1 (by rfl) ⟨335540, by rfl⟩ : syracuseStep 447387 = 671081) B671081
theorem B447439 : Blo 443779 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B1004507 : Blo 443779 1004507 := bstep (se 1 (by rfl) ⟨753380, by rfl⟩ : syracuseStep 1004507 = 1506761) B1506761
theorem B1692647 : Blo 443779 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B447463 : Blo 443779 447463 := bstep (se 1 (by rfl) ⟨335597, by rfl⟩ : syracuseStep 447463 = 671195) B671195
theorem B11719685 : Blo 443779 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B1004687 : Blo 443779 1004687 := bstep (se 1 (by rfl) ⟨753515, by rfl⟩ : syracuseStep 1004687 = 1507031) B1507031
theorem B1529047 : Blo 443779 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B1004777 : Blo 443779 1004777 := bstep (se 2 (by rfl) ⟨376791, by rfl⟩ : syracuseStep 1004777 = 753583) B753583
theorem B1004831 : Blo 443779 1004831 := bstep (se 1 (by rfl) ⟨753623, by rfl⟩ : syracuseStep 1004831 = 1507247) B1507247
theorem B447775 : Blo 443779 447775 := bstep (se 1 (by rfl) ⟨335831, by rfl⟩ : syracuseStep 447775 = 671663) B671663
theorem B1005353 : Blo 443779 1005353 := bstep (se 2 (by rfl) ⟨377007, by rfl⟩ : syracuseStep 1005353 = 754015) B754015
theorem B1529705 : Blo 443779 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B8148917 : Blo 443779 8148917 := bstep (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) B763961
theorem B1267663 : Blo 443779 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B1693831 : Blo 443779 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B4806935 : Blo 443779 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B711023 : Blo 443779 711023 := bstep (se 1 (by rfl) ⟨533267, by rfl⟩ : syracuseStep 711023 = 1066535) B1066535
theorem B2251151 : Blo 443779 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B1694135 : Blo 443779 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B1071571 : Blo 443779 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B2415167 : Blo 443779 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B4119113 : Blo 443779 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B6576815 : Blo 443779 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B1006415 : Blo 443779 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B1268723 : Blo 443779 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B1006631 : Blo 443779 1006631 := bstep (se 1 (by rfl) ⟨754973, by rfl⟩ : syracuseStep 1006631 = 1509947) B1509947
theorem B1006811 : Blo 443779 1006811 := bstep (se 1 (by rfl) ⟨755108, by rfl⟩ : syracuseStep 1006811 = 1510217) B1510217
theorem B1203443 : Blo 443779 1203443 := bstep (se 1 (by rfl) ⟨902582, by rfl⟩ : syracuseStep 1203443 = 1805165) B1805165
theorem B1007009 : Blo 443779 1007009 := bstep (se 2 (by rfl) ⟨377628, by rfl⟩ : syracuseStep 1007009 = 755257) B755257
theorem B1170875 : Blo 443779 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1269179 : Blo 443779 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B3530263 : Blo 443779 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B843347 : Blo 443779 843347 := bstep (se 1 (by rfl) ⟨632510, by rfl⟩ : syracuseStep 843347 = 1265021) B1265021
theorem B1072801 : Blo 443779 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B1629931 : Blo 443779 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B2253257 : Blo 443779 2253257 := bstep (se 2 (by rfl) ⟨844971, by rfl⟩ : syracuseStep 2253257 = 1689943) B1689943
theorem B713279 : Blo 443779 713279 := bstep (se 1 (by rfl) ⟨534959, by rfl⟩ : syracuseStep 713279 = 1069919) B1069919
theorem B2254067 : Blo 443779 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B4580657 : Blo 443779 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1500605 : Blo 443779 1500605 := bstep (se 3 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 1500605 = 562727) B562727
theorem B1074647 : Blo 443779 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B845473 : Blo 443779 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B1500983 : Blo 443779 1500983 := bstep (se 1 (by rfl) ⟨1125737, by rfl⟩ : syracuseStep 1500983 = 2251475) B2251475
theorem B1501469 : Blo 443779 1501469 := bstep (se 3 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 1501469 = 563051) B563051
theorem B6121763 : Blo 443779 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B1698479 : Blo 443779 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B2256011 : Blo 443779 2256011 := bstep (se 1 (by rfl) ⟨1692008, by rfl⟩ : syracuseStep 2256011 = 3384017) B3384017
theorem B1272971 : Blo 443779 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B1502495 : Blo 443779 1502495 := bstep (se 1 (by rfl) ⟨1126871, by rfl⟩ : syracuseStep 1502495 = 2253743) B2253743
theorem B1273427 : Blo 443779 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B749243 : Blo 443779 749243 := bstep (se 1 (by rfl) ⟨561932, by rfl⟩ : syracuseStep 749243 = 1123865) B1123865
theorem B1208449 : Blo 443779 1208449 := bstep (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) B906337
theorem B12185963 : Blo 443779 12185963 := bstep (se 1 (by rfl) ⟨9139472, by rfl⟩ : syracuseStep 12185963 = 18278945) B18278945
theorem B1012193 : Blo 443779 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B2224691 : Blo 443779 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B2257631 : Blo 443779 2257631 := bstep (se 1 (by rfl) ⟨1693223, by rfl⟩ : syracuseStep 2257631 = 3386447) B3386447
theorem B6419735 : Blo 443779 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B3601759 : Blo 443779 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B750971 : Blo 443779 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B2848193 : Blo 443779 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B587359 : Blo 443779 587359 := bstep (se 1 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 587359 = 881039) B881039
theorem B1504925 : Blo 443779 1504925 := bstep (se 3 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 1504925 = 564347) B564347
theorem B1505465 : Blo 443779 1505465 := bstep (se 2 (by rfl) ⟨564549, by rfl⟩ : syracuseStep 1505465 = 1129099) B1129099
theorem B1898761 : Blo 443779 1898761 := bstep (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) B1424071
theorem B751963 : Blo 443779 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B948809 : Blo 443779 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B2259899 : Blo 443779 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B1932427 : Blo 443779 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B752935 : Blo 443779 752935 := bstep (se 1 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 752935 = 1129403) B1129403
theorem B1506977 : Blo 443779 1506977 := bstep (se 2 (by rfl) ⟨565116, by rfl⟩ : syracuseStep 1506977 = 1130233) B1130233
theorem B753455 : Blo 443779 753455 := bstep (se 1 (by rfl) ⟨565091, by rfl⟩ : syracuseStep 753455 = 1130183) B1130183
theorem B4292513 : Blo 443779 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B1507463 : Blo 443779 1507463 := bstep (se 1 (by rfl) ⟨1130597, by rfl⟩ : syracuseStep 1507463 = 2261195) B2261195
theorem B950491 : Blo 443779 950491 := bstep (se 1 (by rfl) ⟨712868, by rfl⟩ : syracuseStep 950491 = 1425737) B1425737
theorem B3244313 : Blo 443779 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B10944827 : Blo 443779 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B9175355 : Blo 443779 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B754751 : Blo 443779 754751 := bstep (se 1 (by rfl) ⟨566063, by rfl⟩ : syracuseStep 754751 = 1132127) B1132127
theorem B2851985 : Blo 443779 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B5440891 : Blo 443779 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B1508975 : Blo 443779 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B755311 : Blo 443779 755311 := bstep (se 1 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 755311 = 1132967) B1132967
theorem B1509083 : Blo 443779 1509083 := bstep (se 1 (by rfl) ⟨1131812, by rfl⟩ : syracuseStep 1509083 = 2263625) B2263625
theorem B755419 : Blo 443779 755419 := bstep (se 1 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 755419 = 1133129) B1133129
theorem B2033873 : Blo 443779 2033873 := bstep (se 2 (by rfl) ⟨762702, by rfl⟩ : syracuseStep 2033873 = 1525405) B1525405
theorem B1902827 : Blo 443779 1902827 := bstep (se 1 (by rfl) ⟨1427120, by rfl⟩ : syracuseStep 1902827 = 2854241) B2854241
theorem B1903135 : Blo 443779 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B1837673 : Blo 443779 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B3607469 : Blo 443779 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B2722733 : Blo 443779 2722733 := bstep (se 3 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 2722733 = 1021025) B1021025
theorem B5737391 : Blo 443779 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B1510379 : Blo 443779 1510379 := bstep (se 1 (by rfl) ⟨1132784, by rfl⟩ : syracuseStep 1510379 = 2265569) B2265569
theorem B1510433 : Blo 443779 1510433 := bstep (se 2 (by rfl) ⟨566412, by rfl⟩ : syracuseStep 1510433 = 1132825) B1132825
theorem B1806185 : Blo 443779 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B1019803 : Blo 443779 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B1610111 : Blo 443779 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B66130499 : Blo 443779 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B14291639 : Blo 443779 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B562231 : Blo 443779 562231 := bstep (se 1 (by rfl) ⟨421673, by rfl⟩ : syracuseStep 562231 = 843347) B843347
theorem B1611265 : Blo 443779 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B4593793 : Blo 443779 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B3053771 : Blo 443779 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B2038729 : Blo 443779 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B2891009 : Blo 443779 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B1908467 : Blo 443779 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B499495 : Blo 443779 499495 := bstep (se 1 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 499495 = 749243) B749243
theorem B2531681 : Blo 443779 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B1483127 : Blo 443779 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B500647 : Blo 443779 500647 := bstep (se 1 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 500647 = 750971) B750971
theorem B3122333 : Blo 443779 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B3614215 : Blo 443779 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B632539 : Blo 443779 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B1124543 : Blo 443779 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B534719 : Blo 443779 534719 := bstep (se 1 (by rfl) ⟨401039, by rfl⟩ : syracuseStep 534719 = 802079) B802079
theorem B665897 : Blo 443779 665897 := bstep (se 2 (by rfl) ⟨249711, by rfl⟩ : syracuseStep 665897 = 499423) B499423
theorem B665903 : Blo 443779 665903 := bstep (se 1 (by rfl) ⟨499427, by rfl⟩ : syracuseStep 665903 = 998855) B998855
theorem B2173241 : Blo 443779 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B666143 : Blo 443779 666143 := bstep (se 1 (by rfl) ⟨499607, by rfl⟩ : syracuseStep 666143 = 999215) B999215
theorem B502303 : Blo 443779 502303 := bstep (se 1 (by rfl) ⟨376727, by rfl⟩ : syracuseStep 502303 = 753455) B753455
theorem B2861675 : Blo 443779 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B666527 : Blo 443779 666527 := bstep (se 1 (by rfl) ⟨499895, by rfl⟩ : syracuseStep 666527 = 999791) B999791
theorem B666575 : Blo 443779 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B666665 : Blo 443779 666665 := bstep (se 2 (by rfl) ⟨249999, by rfl⟩ : syracuseStep 666665 = 499999) B499999
theorem B666671 : Blo 443779 666671 := bstep (se 1 (by rfl) ⟨500003, by rfl⟩ : syracuseStep 666671 = 1000007) B1000007
theorem B666695 : Blo 443779 666695 := bstep (se 1 (by rfl) ⟨500021, by rfl⟩ : syracuseStep 666695 = 1000043) B1000043
theorem B2862215 : Blo 443779 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B666959 : Blo 443779 666959 := bstep (se 1 (by rfl) ⟨500219, by rfl⟩ : syracuseStep 666959 = 1000439) B1000439
theorem B667049 : Blo 443779 667049 := bstep (se 2 (by rfl) ⟨250143, by rfl⟩ : syracuseStep 667049 = 500287) B500287
theorem B1256887 : Blo 443779 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B667199 : Blo 443779 667199 := bstep (se 1 (by rfl) ⟨500399, by rfl⟩ : syracuseStep 667199 = 1000799) B1000799
theorem B1126163 : Blo 443779 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B1126183 : Blo 443779 1126183 := bstep (se 1 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 1126183 = 1689275) B1689275
theorem B634663 : Blo 443779 634663 := bstep (se 1 (by rfl) ⟨475997, by rfl⟩ : syracuseStep 634663 = 951995) B951995
theorem B667463 : Blo 443779 667463 := bstep (se 1 (by rfl) ⟨500597, by rfl⟩ : syracuseStep 667463 = 1001195) B1001195
theorem B667547 : Blo 443779 667547 := bstep (se 1 (by rfl) ⟨500660, by rfl⟩ : syracuseStep 667547 = 1001321) B1001321
theorem B5091335 : Blo 443779 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B668111 : Blo 443779 668111 := bstep (se 1 (by rfl) ⟨501083, by rfl⟩ : syracuseStep 668111 = 1002167) B1002167
theorem B635369 : Blo 443779 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B13054445 : Blo 443779 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B668153 : Blo 443779 668153 := bstep (se 2 (by rfl) ⟨250557, by rfl⟩ : syracuseStep 668153 = 501115) B501115
theorem B668255 : Blo 443779 668255 := bstep (se 1 (by rfl) ⟨501191, by rfl⟩ : syracuseStep 668255 = 1002383) B1002383
theorem B5157665 : Blo 443779 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B1127297 : Blo 443779 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B3388391 : Blo 443779 3388391 := bstep (se 1 (by rfl) ⟨2541293, by rfl⟩ : syracuseStep 3388391 = 5082587) B5082587
theorem B1127479 : Blo 443779 1127479 := bstep (se 1 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 1127479 = 1691219) B1691219
theorem B668735 : Blo 443779 668735 := bstep (se 1 (by rfl) ⟨501551, by rfl⟩ : syracuseStep 668735 = 1003103) B1003103
theorem B668777 : Blo 443779 668777 := bstep (se 2 (by rfl) ⟨250791, by rfl⟩ : syracuseStep 668777 = 501583) B501583
theorem B668879 : Blo 443779 668879 := bstep (se 1 (by rfl) ⟨501659, by rfl⟩ : syracuseStep 668879 = 1003319) B1003319
theorem B4109629 : Blo 443779 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B669083 : Blo 443779 669083 := bstep (se 1 (by rfl) ⟨501812, by rfl⟩ : syracuseStep 669083 = 1003625) B1003625
theorem B669305 : Blo 443779 669305 := bstep (se 2 (by rfl) ⟨250989, by rfl⟩ : syracuseStep 669305 = 501979) B501979
theorem B1128107 : Blo 443779 1128107 := bstep (se 1 (by rfl) ⟨846080, by rfl⟩ : syracuseStep 1128107 = 1692161) B1692161
theorem B669407 : Blo 443779 669407 := bstep (se 1 (by rfl) ⟨502055, by rfl⟩ : syracuseStep 669407 = 1004111) B1004111
theorem B34748149 : Blo 443779 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B669503 : Blo 443779 669503 := bstep (se 1 (by rfl) ⟨502127, by rfl⟩ : syracuseStep 669503 = 1004255) B1004255
theorem B669671 : Blo 443779 669671 := bstep (se 1 (by rfl) ⟨502253, by rfl⟩ : syracuseStep 669671 = 1004507) B1004507
theorem B2570221 : Blo 443779 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B1128431 : Blo 443779 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B669689 : Blo 443779 669689 := bstep (se 2 (by rfl) ⟨251133, by rfl⟩ : syracuseStep 669689 = 502267) B502267
theorem B9615419 : Blo 443779 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B669791 : Blo 443779 669791 := bstep (se 1 (by rfl) ⟨502343, by rfl⟩ : syracuseStep 669791 = 1004687) B1004687
theorem B1423457 : Blo 443779 1423457 := bstep (se 2 (by rfl) ⟨533796, by rfl⟩ : syracuseStep 1423457 = 1067593) B1067593
theorem B669851 : Blo 443779 669851 := bstep (se 1 (by rfl) ⟨502388, by rfl⟩ : syracuseStep 669851 = 1004777) B1004777
theorem B669887 : Blo 443779 669887 := bstep (se 1 (by rfl) ⟨502415, by rfl⟩ : syracuseStep 669887 = 1004831) B1004831
theorem B669929 : Blo 443779 669929 := bstep (se 2 (by rfl) ⟨251223, by rfl⟩ : syracuseStep 669929 = 502447) B502447
theorem B2865415 : Blo 443779 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B12204553 : Blo 443779 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B670235 : Blo 443779 670235 := bstep (se 1 (by rfl) ⟨502676, by rfl⟩ : syracuseStep 670235 = 1005353) B1005353
theorem B670313 : Blo 443779 670313 := bstep (se 2 (by rfl) ⟨251367, by rfl⟩ : syracuseStep 670313 = 502735) B502735
theorem B7584515 : Blo 443779 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B1129423 : Blo 443779 1129423 := bstep (se 1 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 1129423 = 1694135) B1694135
theorem B670841 : Blo 443779 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B670943 : Blo 443779 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B802057 : Blo 443779 802057 := bstep (se 2 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 802057 = 601543) B601543
theorem B670985 : Blo 443779 670985 := bstep (se 2 (by rfl) ⟨251619, by rfl⟩ : syracuseStep 670985 = 503239) B503239
theorem B671087 : Blo 443779 671087 := bstep (se 1 (by rfl) ⟨503315, by rfl⟩ : syracuseStep 671087 = 1006631) B1006631
theorem B671207 : Blo 443779 671207 := bstep (se 1 (by rfl) ⟨503405, by rfl⟩ : syracuseStep 671207 = 1006811) B1006811
theorem B802295 : Blo 443779 802295 := bstep (se 1 (by rfl) ⟨601721, by rfl⟩ : syracuseStep 802295 = 1203443) B1203443
theorem B671339 : Blo 443779 671339 := bstep (se 1 (by rfl) ⟨503504, by rfl⟩ : syracuseStep 671339 = 1007009) B1007009
theorem B671465 : Blo 443779 671465 := bstep (se 2 (by rfl) ⟨251799, by rfl⟩ : syracuseStep 671465 = 503599) B503599
theorem B671609 : Blo 443779 671609 := bstep (se 2 (by rfl) ⟨251853, by rfl⟩ : syracuseStep 671609 = 503707) B503707
theorem B2867339 : Blo 443779 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B475519 : Blo 443779 475519 := bstep (se 1 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 475519 = 713279) B713279
theorem B967099 : Blo 443779 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B2867977 : Blo 443779 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B1426187 : Blo 443779 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B1000403 : Blo 443779 1000403 := bstep (se 1 (by rfl) ⟨750302, by rfl⟩ : syracuseStep 1000403 = 1500605) B1500605
theorem B1000655 : Blo 443779 1000655 := bstep (se 1 (by rfl) ⟨750491, by rfl⟩ : syracuseStep 1000655 = 1500983) B1500983
theorem B23250199 : Blo 443779 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B443803 : Blo 443779 443803 := bstep (se 1 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 443803 = 665705) B665705
theorem B2147755 : Blo 443779 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B1000979 : Blo 443779 1000979 := bstep (se 1 (by rfl) ⟨750734, by rfl⟩ : syracuseStep 1000979 = 1501469) B1501469
theorem B4081175 : Blo 443779 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B444015 : Blo 443779 444015 := bstep (se 1 (by rfl) ⟨333011, by rfl⟩ : syracuseStep 444015 = 666023) B666023
theorem B444071 : Blo 443779 444071 := bstep (se 1 (by rfl) ⟨333053, by rfl⟩ : syracuseStep 444071 = 666107) B666107
theorem B444155 : Blo 443779 444155 := bstep (se 1 (by rfl) ⟨333116, by rfl⟩ : syracuseStep 444155 = 666233) B666233
theorem B444191 : Blo 443779 444191 := bstep (se 1 (by rfl) ⟨333143, by rfl⟩ : syracuseStep 444191 = 666287) B666287
theorem B1132319 : Blo 443779 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B4802345 : Blo 443779 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B444223 : Blo 443779 444223 := bstep (se 1 (by rfl) ⟨333167, by rfl⟩ : syracuseStep 444223 = 666335) B666335
theorem B804745 : Blo 443779 804745 := bstep (se 2 (by rfl) ⟨301779, by rfl⟩ : syracuseStep 804745 = 603559) B603559
theorem B4900837 : Blo 443779 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B444399 : Blo 443779 444399 := bstep (se 1 (by rfl) ⟨333299, by rfl⟩ : syracuseStep 444399 = 666599) B666599
theorem B30951517 : Blo 443779 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B444571 : Blo 443779 444571 := bstep (se 1 (by rfl) ⟨333428, by rfl⟩ : syracuseStep 444571 = 666857) B666857
theorem B444607 : Blo 443779 444607 := bstep (se 1 (by rfl) ⟨333455, by rfl⟩ : syracuseStep 444607 = 666911) B666911
theorem B1001663 : Blo 443779 1001663 := bstep (se 1 (by rfl) ⟨751247, by rfl⟩ : syracuseStep 1001663 = 1502495) B1502495
theorem B444719 : Blo 443779 444719 := bstep (se 1 (by rfl) ⟨333539, by rfl⟩ : syracuseStep 444719 = 667079) B667079
theorem B444955 : Blo 443779 444955 := bstep (se 1 (by rfl) ⟨333716, by rfl⟩ : syracuseStep 444955 = 667433) B667433
theorem B444959 : Blo 443779 444959 := bstep (se 1 (by rfl) ⟨333719, by rfl⟩ : syracuseStep 444959 = 667439) B667439
theorem B1690217 : Blo 443779 1690217 := bstep (se 2 (by rfl) ⟨633831, by rfl⟩ : syracuseStep 1690217 = 1267663) B1267663
theorem B445275 : Blo 443779 445275 := bstep (se 1 (by rfl) ⟨333956, by rfl⟩ : syracuseStep 445275 = 667913) B667913
theorem B445343 : Blo 443779 445343 := bstep (se 1 (by rfl) ⟨334007, by rfl⟩ : syracuseStep 445343 = 668015) B668015
theorem B674795 : Blo 443779 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B904171 : Blo 443779 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B445487 : Blo 443779 445487 := bstep (se 1 (by rfl) ⟨334115, by rfl⟩ : syracuseStep 445487 = 668231) B668231
theorem B445511 : Blo 443779 445511 := bstep (se 1 (by rfl) ⟨334133, by rfl⟩ : syracuseStep 445511 = 668267) B668267
theorem B1002617 : Blo 443779 1002617 := bstep (se 2 (by rfl) ⟨375981, by rfl⟩ : syracuseStep 1002617 = 751963) B751963
theorem B445663 : Blo 443779 445663 := bstep (se 1 (by rfl) ⟨334247, by rfl⟩ : syracuseStep 445663 = 668495) B668495
theorem B1428761 : Blo 443779 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B445927 : Blo 443779 445927 := bstep (se 1 (by rfl) ⟨334445, by rfl⟩ : syracuseStep 445927 = 668891) B668891
theorem B4279823 : Blo 443779 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B446043 : Blo 443779 446043 := bstep (se 1 (by rfl) ⟨334532, by rfl⟩ : syracuseStep 446043 = 669065) B669065
theorem B1003283 : Blo 443779 1003283 := bstep (se 1 (by rfl) ⟨752462, by rfl⟩ : syracuseStep 1003283 = 1504925) B1504925
theorem B446279 : Blo 443779 446279 := bstep (se 1 (by rfl) ⟨334709, by rfl⟩ : syracuseStep 446279 = 669419) B669419
theorem B446431 : Blo 443779 446431 := bstep (se 1 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 446431 = 669647) B669647
theorem B1003643 : Blo 443779 1003643 := bstep (se 1 (by rfl) ⟨752732, by rfl⟩ : syracuseStep 1003643 = 1505465) B1505465
theorem B2576569 : Blo 443779 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B446695 : Blo 443779 446695 := bstep (se 1 (by rfl) ⟨335021, by rfl⟩ : syracuseStep 446695 = 670043) B670043
theorem B446847 : Blo 443779 446847 := bstep (se 1 (by rfl) ⟨335135, by rfl⟩ : syracuseStep 446847 = 670271) B670271
theorem B1003913 : Blo 443779 1003913 := bstep (se 2 (by rfl) ⟨376467, by rfl⟩ : syracuseStep 1003913 = 752935) B752935
theorem B446927 : Blo 443779 446927 := bstep (se 1 (by rfl) ⟨335195, by rfl⟩ : syracuseStep 446927 = 670391) B670391
theorem B5100083 : Blo 443779 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B3396167 : Blo 443779 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B447079 : Blo 443779 447079 := bstep (se 1 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 447079 = 670619) B670619
theorem B4707017 : Blo 443779 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B3822329 : Blo 443779 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B447343 : Blo 443779 447343 := bstep (se 1 (by rfl) ⟨335507, by rfl⟩ : syracuseStep 447343 = 671015) B671015
theorem B1430401 : Blo 443779 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B447399 : Blo 443779 447399 := bstep (se 1 (by rfl) ⟨335549, by rfl⟩ : syracuseStep 447399 = 671099) B671099
theorem B447483 : Blo 443779 447483 := bstep (se 1 (by rfl) ⟨335612, by rfl⟩ : syracuseStep 447483 = 671225) B671225
theorem B447551 : Blo 443779 447551 := bstep (se 1 (by rfl) ⟨335663, by rfl⟩ : syracuseStep 447551 = 671327) B671327
theorem B1004651 : Blo 443779 1004651 := bstep (se 1 (by rfl) ⟨753488, by rfl⟩ : syracuseStep 1004651 = 1506977) B1506977
theorem B447695 : Blo 443779 447695 := bstep (se 1 (by rfl) ⟨335771, by rfl⟩ : syracuseStep 447695 = 671543) B671543
theorem B2545121 : Blo 443779 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B2283179 : Blo 443779 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1005227 : Blo 443779 1005227 := bstep (se 1 (by rfl) ⟨753920, by rfl⟩ : syracuseStep 1005227 = 1507841) B1507841
theorem B6838151 : Blo 443779 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B1923047 : Blo 443779 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B1005551 : Blo 443779 1005551 := bstep (se 1 (by rfl) ⟨754163, by rfl⟩ : syracuseStep 1005551 = 1508327) B1508327
theorem B1005767 : Blo 443779 1005767 := bstep (se 1 (by rfl) ⟨754325, by rfl⟩ : syracuseStep 1005767 = 1508651) B1508651
theorem B2709883 : Blo 443779 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B1005947 : Blo 443779 1005947 := bstep (se 1 (by rfl) ⟨754460, by rfl⟩ : syracuseStep 1005947 = 1508921) B1508921
theorem B1006217 : Blo 443779 1006217 := bstep (se 2 (by rfl) ⟨377331, by rfl⟩ : syracuseStep 1006217 = 754663) B754663
theorem B1071955 : Blo 443779 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B6511535 : Blo 443779 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B4906099 : Blo 443779 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B1006775 : Blo 443779 1006775 := bstep (se 1 (by rfl) ⟨755081, by rfl⟩ : syracuseStep 1006775 = 1510163) B1510163
theorem B2251961 : Blo 443779 2251961 := bstep (se 2 (by rfl) ⟨844485, by rfl⟩ : syracuseStep 2251961 = 1688971) B1688971
theorem B843119 : Blo 443779 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B1498715 : Blo 443779 1498715 := bstep (se 1 (by rfl) ⟨1124036, by rfl⟩ : syracuseStep 1498715 = 2248073) B2248073
theorem B515675 : Blo 443779 515675 := bstep (se 1 (by rfl) ⟨386756, by rfl⟩ : syracuseStep 515675 = 773513) B773513
theorem B1007351 : Blo 443779 1007351 := bstep (se 1 (by rfl) ⟨755513, by rfl⟩ : syracuseStep 1007351 = 1511027) B1511027
theorem B31252493 : Blo 443779 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B1499417 : Blo 443779 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B8577413 : Blo 443779 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B1499579 : Blo 443779 1499579 := bstep (se 1 (by rfl) ⟨1124684, by rfl⟩ : syracuseStep 1499579 = 2249369) B2249369
theorem B3433637 : Blo 443779 3433637 := bstep (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) B643807
theorem B5432611 : Blo 443779 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B3204623 : Blo 443779 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B2713171 : Blo 443779 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1500767 : Blo 443779 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B9791165 : Blo 443779 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1140443 : Blo 443779 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B2746075 : Blo 443779 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B4384543 : Blo 443779 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B2844503 : Blo 443779 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B845815 : Blo 443779 845815 := bstep (se 1 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 845815 = 1268723) B1268723
theorem B846119 : Blo 443779 846119 := bstep (se 1 (by rfl) ⟨634589, by rfl⟩ : syracuseStep 846119 = 1269179) B1269179
theorem B3041831 : Blo 443779 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B1502171 : Blo 443779 1502171 := bstep (se 1 (by rfl) ⟨1126628, by rfl⟩ : syracuseStep 1502171 = 2253257) B2253257
theorem B1502441 : Blo 443779 1502441 := bstep (se 2 (by rfl) ⟨563415, by rfl⟩ : syracuseStep 1502441 = 1126831) B1126831
theorem B2583895 : Blo 443779 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B847273 : Blo 443779 847273 := bstep (se 2 (by rfl) ⟨317727, by rfl⟩ : syracuseStep 847273 = 635455) B635455
theorem B749047 : Blo 443779 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B1502711 : Blo 443779 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B1895993 : Blo 443779 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B1896061 : Blo 443779 1896061 := bstep (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) B711023
theorem B716431 : Blo 443779 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B2256659 : Blo 443779 2256659 := bstep (se 1 (by rfl) ⟨1692494, by rfl⟩ : syracuseStep 2256659 = 3384989) B3384989
theorem B749351 : Blo 443779 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B750073 : Blo 443779 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B1503737 : Blo 443779 1503737 := bstep (se 2 (by rfl) ⟨563901, by rfl⟩ : syracuseStep 1503737 = 1127803) B1127803
theorem B7205597 : Blo 443779 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B3797725 : Blo 443779 3797725 := bstep (se 3 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 3797725 = 1424147) B1424147
theorem B750343 : Blo 443779 750343 := bstep (se 1 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 750343 = 1125515) B1125515
theorem B1504007 : Blo 443779 1504007 := bstep (se 1 (by rfl) ⟨1128005, by rfl⟩ : syracuseStep 1504007 = 2256011) B2256011
theorem B848647 : Blo 443779 848647 := bstep (se 1 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 848647 = 1272971) B1272971
theorem B750377 : Blo 443779 750377 := bstep (se 2 (by rfl) ⟨281391, by rfl⟩ : syracuseStep 750377 = 562783) B562783
theorem B783145 : Blo 443779 783145 := bstep (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) B587359
theorem B1504061 : Blo 443779 1504061 := bstep (se 3 (by rfl) ⟨282011, by rfl⟩ : syracuseStep 1504061 = 564023) B564023
theorem B750647 : Blo 443779 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B848951 : Blo 443779 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B1274953 : Blo 443779 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B1603003 : Blo 443779 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B2258441 : Blo 443779 2258441 := bstep (se 2 (by rfl) ⟨846915, by rfl⟩ : syracuseStep 2258441 = 1693831) B1693831
theorem B8123975 : Blo 443779 8123975 := bstep (se 1 (by rfl) ⟨6092981, by rfl⟩ : syracuseStep 8123975 = 12185963) B12185963
theorem B947963 : Blo 443779 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B751423 : Blo 443779 751423 := bstep (se 1 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 751423 = 1127135) B1127135
theorem B1505087 : Blo 443779 1505087 := bstep (se 1 (by rfl) ⟨1128815, by rfl⟩ : syracuseStep 1505087 = 2257631) B2257631
theorem B1210351 : Blo 443779 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B1898795 : Blo 443779 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B752159 : Blo 443779 752159 := bstep (se 1 (by rfl) ⟨564119, by rfl⟩ : syracuseStep 752159 = 1128239) B1128239
theorem B1014329 : Blo 443779 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B752233 : Blo 443779 752233 := bstep (se 2 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 752233 = 564175) B564175
theorem B949151 : Blo 443779 949151 := bstep (se 1 (by rfl) ⟨711863, by rfl⟩ : syracuseStep 949151 = 1423727) B1423727
theorem B752591 : Blo 443779 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B3210329 : Blo 443779 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B1506599 : Blo 443779 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B753259 : Blo 443779 753259 := bstep (se 1 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 753259 = 1129889) B1129889
theorem B2850551 : Blo 443779 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B753529 : Blo 443779 753529 := bstep (se 2 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 753529 = 565147) B565147
theorem B753563 : Blo 443779 753563 := bstep (se 1 (by rfl) ⟨565172, by rfl⟩ : syracuseStep 753563 = 1130345) B1130345
theorem B2162875 : Blo 443779 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B950791 : Blo 443779 950791 := bstep (se 1 (by rfl) ⟨713093, by rfl⟩ : syracuseStep 950791 = 1426187) B1426187
theorem B1901323 : Blo 443779 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B2720783 : Blo 443779 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B754879 : Blo 443779 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B31000265 : Blo 443779 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B7243481 : Blo 443779 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B4818953 : Blo 443779 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B952507 : Blo 443779 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B2853215 : Blo 443779 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B2264111 : Blo 443779 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B1282031 : Blo 443779 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B2035847 : Blo 443779 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B3445193 : Blo 443779 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B2528081 : Blo 443779 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B955241 : Blo 443779 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B562079 : Blo 443779 562079 := bstep (se 1 (by rfl) ⟨421559, by rfl⟩ : syracuseStep 562079 = 843119) B843119
theorem B988751 : Blo 443779 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B2136415 : Blo 443779 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B760295 : Blo 443779 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B1907201 : Blo 443779 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B564079 : Blo 443779 564079 := bstep (se 1 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 564079 = 846119) B846119
theorem B1907783 : Blo 443779 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B5479505 : Blo 443779 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B24353909 : Blo 443779 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B2137337 : Blo 443779 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B1908143 : Blo 443779 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B499567 : Blo 443779 499567 := bstep (se 1 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 499567 = 749351) B749351
theorem B1613801 : Blo 443779 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B3613177 : Blo 443779 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B500251 : Blo 443779 500251 := bstep (se 1 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 500251 = 750377) B750377
theorem B7709357 : Blo 443779 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B500431 : Blo 443779 500431 := bstep (se 1 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 500431 = 750647) B750647
theorem B565967 : Blo 443779 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B5415983 : Blo 443779 5415983 := bstep (se 1 (by rfl) ⟨4061987, by rfl⟩ : syracuseStep 5415983 = 8123975) B8123975
theorem B631975 : Blo 443779 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B501439 : Blo 443779 501439 := bstep (se 1 (by rfl) ⟨376079, by rfl⟩ : syracuseStep 501439 = 752159) B752159
theorem B5056343 : Blo 443779 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B632767 : Blo 443779 632767 := bstep (se 1 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 632767 = 949151) B949151
theorem B501727 : Blo 443779 501727 := bstep (se 1 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 501727 = 752591) B752591
theorem B2140219 : Blo 443779 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B534863 : Blo 443779 534863 := bstep (se 1 (by rfl) ⟨401147, by rfl⟩ : syracuseStep 534863 = 802295) B802295
theorem B665993 : Blo 443779 665993 := bstep (se 2 (by rfl) ⟨249747, by rfl⟩ : syracuseStep 665993 = 499495) B499495
theorem B502375 : Blo 443779 502375 := bstep (se 1 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 502375 = 753563) B753563
theorem B1911559 : Blo 443779 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B634025 : Blo 443779 634025 := bstep (se 2 (by rfl) ⟨237759, by rfl⟩ : syracuseStep 634025 = 475519) B475519
theorem B1289465 : Blo 443779 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B666935 : Blo 443779 666935 := bstep (se 1 (by rfl) ⟨500201, by rfl⟩ : syracuseStep 666935 = 1000403) B1000403
theorem B503167 : Blo 443779 503167 := bstep (se 1 (by rfl) ⟨377375, by rfl⟩ : syracuseStep 503167 = 754751) B754751
theorem B667103 : Blo 443779 667103 := bstep (se 1 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 667103 = 1000655) B1000655
theorem B667319 : Blo 443779 667319 := bstep (se 1 (by rfl) ⟨500489, by rfl⟩ : syracuseStep 667319 = 1000979) B1000979
theorem B667529 : Blo 443779 667529 := bstep (se 2 (by rfl) ⟨250323, by rfl⟩ : syracuseStep 667529 = 500647) B500647
theorem B667775 : Blo 443779 667775 := bstep (se 1 (by rfl) ⟨500831, by rfl⟩ : syracuseStep 667775 = 1001663) B1001663
theorem B1355915 : Blo 443779 1355915 := bstep (se 1 (by rfl) ⟨1016936, by rfl⟩ : syracuseStep 1355915 = 2033873) B2033873
theorem B1126811 : Blo 443779 1126811 := bstep (se 1 (by rfl) ⟨845108, by rfl⟩ : syracuseStep 1126811 = 1690217) B1690217
theorem B1225115 : Blo 443779 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B7254521 : Blo 443779 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B2863673 : Blo 443779 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B2404979 : Blo 443779 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B1815155 : Blo 443779 1815155 := bstep (se 1 (by rfl) ⟨1361366, by rfl⟩ : syracuseStep 1815155 = 2722733) B2722733
theorem B668411 : Blo 443779 668411 := bstep (se 1 (by rfl) ⟨501308, by rfl⟩ : syracuseStep 668411 = 1002617) B1002617
theorem B3617561 : Blo 443779 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B5846057 : Blo 443779 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B668855 : Blo 443779 668855 := bstep (se 1 (by rfl) ⟨501641, by rfl⟩ : syracuseStep 668855 = 1003283) B1003283
theorem B6534449 : Blo 443779 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B1127753 : Blo 443779 1127753 := bstep (se 2 (by rfl) ⟨422907, by rfl⟩ : syracuseStep 1127753 = 845815) B845815
theorem B669095 : Blo 443779 669095 := bstep (se 1 (by rfl) ⟨501821, by rfl⟩ : syracuseStep 669095 = 1003643) B1003643
theorem B41268689 : Blo 443779 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B669275 : Blo 443779 669275 := bstep (se 1 (by rfl) ⟨501956, by rfl⟩ : syracuseStep 669275 = 1003913) B1003913
theorem B44086999 : Blo 443779 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B2537513 : Blo 443779 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B669737 : Blo 443779 669737 := bstep (se 2 (by rfl) ⟨251151, by rfl⟩ : syracuseStep 669737 = 502303) B502303
theorem B669767 : Blo 443779 669767 := bstep (se 1 (by rfl) ⟨502325, by rfl⟩ : syracuseStep 669767 = 1004651) B1004651
theorem B670151 : Blo 443779 670151 := bstep (se 1 (by rfl) ⟨502613, by rfl⟩ : syracuseStep 670151 = 1005227) B1005227
theorem B670367 : Blo 443779 670367 := bstep (se 1 (by rfl) ⟨502775, by rfl⟩ : syracuseStep 670367 = 1005551) B1005551
theorem B670511 : Blo 443779 670511 := bstep (se 1 (by rfl) ⟨502883, by rfl⟩ : syracuseStep 670511 = 1005767) B1005767
theorem B670631 : Blo 443779 670631 := bstep (se 1 (by rfl) ⟨502973, by rfl⟩ : syracuseStep 670631 = 1005947) B1005947
theorem B670811 : Blo 443779 670811 := bstep (se 1 (by rfl) ⟨503108, by rfl⟩ : syracuseStep 670811 = 1006217) B1006217
theorem B1129697 : Blo 443779 1129697 := bstep (se 2 (by rfl) ⟨423636, by rfl⟩ : syracuseStep 1129697 = 847273) B847273
theorem B4341023 : Blo 443779 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B998729 : Blo 443779 998729 := bstep (se 2 (by rfl) ⟨374523, by rfl⟩ : syracuseStep 998729 = 749047) B749047
theorem B671183 : Blo 443779 671183 := bstep (se 1 (by rfl) ⟨503387, by rfl⟩ : syracuseStep 671183 = 1006775) B1006775
theorem B999143 : Blo 443779 999143 := bstep (se 1 (by rfl) ⟨749357, by rfl⟩ : syracuseStep 999143 = 1498715) B1498715
theorem B671567 : Blo 443779 671567 := bstep (se 1 (by rfl) ⟨503675, by rfl⟩ : syracuseStep 671567 = 1007351) B1007351
theorem B1359737 : Blo 443779 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B999611 : Blo 443779 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B1687787 : Blo 443779 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B5718275 : Blo 443779 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B999719 : Blo 443779 999719 := bstep (se 1 (by rfl) ⟨749789, by rfl⟩ : syracuseStep 999719 = 1499579) B1499579
theorem B1425917 : Blo 443779 1425917 := bstep (se 3 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 1425917 = 534719) B534719
theorem B26165861 : Blo 443779 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B1000097 : Blo 443779 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B2081555 : Blo 443779 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B5063633 : Blo 443779 5063633 := bstep (se 2 (by rfl) ⟨1898862, by rfl⟩ : syracuseStep 5063633 = 3797725) B3797725
theorem B1000457 : Blo 443779 1000457 := bstep (se 2 (by rfl) ⟨375171, by rfl⟩ : syracuseStep 1000457 = 750343) B750343
theorem B1131529 : Blo 443779 1131529 := bstep (se 2 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 1131529 = 848647) B848647
theorem B1000511 : Blo 443779 1000511 := bstep (se 1 (by rfl) ⟨750383, by rfl⟩ : syracuseStep 1000511 = 1500767) B1500767
theorem B8111549 : Blo 443779 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B443931 : Blo 443779 443931 := bstep (se 1 (by rfl) ⟨332948, by rfl⟩ : syracuseStep 443931 = 665897) B665897
theorem B443935 : Blo 443779 443935 := bstep (se 1 (by rfl) ⟨332951, by rfl⟩ : syracuseStep 443935 = 665903) B665903
theorem B444095 : Blo 443779 444095 := bstep (se 1 (by rfl) ⟨333071, by rfl⟩ : syracuseStep 444095 = 666143) B666143
theorem B444351 : Blo 443779 444351 := bstep (se 1 (by rfl) ⟨333263, by rfl⟩ : syracuseStep 444351 = 666527) B666527
theorem B444383 : Blo 443779 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B1001447 : Blo 443779 1001447 := bstep (se 1 (by rfl) ⟨751085, by rfl⟩ : syracuseStep 1001447 = 1502171) B1502171
theorem B2148353 : Blo 443779 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B444443 : Blo 443779 444443 := bstep (se 1 (by rfl) ⟨333332, by rfl⟩ : syracuseStep 444443 = 666665) B666665
theorem B444447 : Blo 443779 444447 := bstep (se 1 (by rfl) ⟨333335, by rfl⟩ : syracuseStep 444447 = 666671) B666671
theorem B444463 : Blo 443779 444463 := bstep (se 1 (by rfl) ⟨333347, by rfl⟩ : syracuseStep 444463 = 666695) B666695
theorem B1001627 : Blo 443779 1001627 := bstep (se 1 (by rfl) ⟨751220, by rfl⟩ : syracuseStep 1001627 = 1502441) B1502441
theorem B444639 : Blo 443779 444639 := bstep (se 1 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 444639 = 666959) B666959
theorem B444699 : Blo 443779 444699 := bstep (se 1 (by rfl) ⟨333524, by rfl⟩ : syracuseStep 444699 = 667049) B667049
theorem B6703397 : Blo 443779 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1001807 : Blo 443779 1001807 := bstep (se 1 (by rfl) ⟨751355, by rfl⟩ : syracuseStep 1001807 = 1502711) B1502711
theorem B1263995 : Blo 443779 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B444799 : Blo 443779 444799 := bstep (se 1 (by rfl) ⟨333599, by rfl⟩ : syracuseStep 444799 = 667199) B667199
theorem B1001897 : Blo 443779 1001897 := bstep (se 2 (by rfl) ⟨375711, by rfl⟩ : syracuseStep 1001897 = 751423) B751423
theorem B444975 : Blo 443779 444975 := bstep (se 1 (by rfl) ⟨333731, by rfl⟩ : syracuseStep 444975 = 667463) B667463
theorem B445031 : Blo 443779 445031 := bstep (se 1 (by rfl) ⟨333773, by rfl⟩ : syracuseStep 445031 = 667547) B667547
theorem B3426961 : Blo 443779 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B3394223 : Blo 443779 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B445407 : Blo 443779 445407 := bstep (se 1 (by rfl) ⟨334055, by rfl⟩ : syracuseStep 445407 = 668111) B668111
theorem B8702963 : Blo 443779 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B445435 : Blo 443779 445435 := bstep (se 1 (by rfl) ⟨334076, by rfl⟩ : syracuseStep 445435 = 668153) B668153
theorem B1002491 : Blo 443779 1002491 := bstep (se 1 (by rfl) ⟨751868, by rfl⟩ : syracuseStep 1002491 = 1503737) B1503737
theorem B3820553 : Blo 443779 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B445503 : Blo 443779 445503 := bstep (se 1 (by rfl) ⟨334127, by rfl⟩ : syracuseStep 445503 = 668255) B668255
theorem B4803731 : Blo 443779 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B1002671 : Blo 443779 1002671 := bstep (se 1 (by rfl) ⟨752003, by rfl⟩ : syracuseStep 1002671 = 1504007) B1504007
theorem B1002707 : Blo 443779 1002707 := bstep (se 1 (by rfl) ⟨752030, by rfl⟩ : syracuseStep 1002707 = 1504061) B1504061
theorem B16272737 : Blo 443779 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B445823 : Blo 443779 445823 := bstep (se 1 (by rfl) ⟨334367, by rfl⟩ : syracuseStep 445823 = 668735) B668735
theorem B445851 : Blo 443779 445851 := bstep (se 1 (by rfl) ⟨334388, by rfl⟩ : syracuseStep 445851 = 668777) B668777
theorem B445919 : Blo 443779 445919 := bstep (se 1 (by rfl) ⟨334439, by rfl⟩ : syracuseStep 445919 = 668879) B668879
theorem B1002977 : Blo 443779 1002977 := bstep (se 2 (by rfl) ⟨376116, by rfl⟩ : syracuseStep 1002977 = 752233) B752233
theorem B446055 : Blo 443779 446055 := bstep (se 1 (by rfl) ⟨334541, by rfl⟩ : syracuseStep 446055 = 669083) B669083
theorem B446203 : Blo 443779 446203 := bstep (se 1 (by rfl) ⟨334652, by rfl⟩ : syracuseStep 446203 = 669305) B669305
theorem B1429273 : Blo 443779 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B446271 : Blo 443779 446271 := bstep (se 1 (by rfl) ⟨334703, by rfl⟩ : syracuseStep 446271 = 669407) B669407
theorem B1003391 : Blo 443779 1003391 := bstep (se 1 (by rfl) ⟨752543, by rfl⟩ : syracuseStep 1003391 = 1505087) B1505087
theorem B446335 : Blo 443779 446335 := bstep (se 1 (by rfl) ⟨334751, by rfl⟩ : syracuseStep 446335 = 669503) B669503
theorem B446447 : Blo 443779 446447 := bstep (se 1 (by rfl) ⟨334835, by rfl⟩ : syracuseStep 446447 = 669671) B669671
theorem B446459 : Blo 443779 446459 := bstep (se 1 (by rfl) ⟨334844, by rfl⟩ : syracuseStep 446459 = 669689) B669689
theorem B6410279 : Blo 443779 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B446527 : Blo 443779 446527 := bstep (se 1 (by rfl) ⟨334895, by rfl⟩ : syracuseStep 446527 = 669791) B669791
theorem B446567 : Blo 443779 446567 := bstep (se 1 (by rfl) ⟨334925, by rfl⟩ : syracuseStep 446567 = 669851) B669851
theorem B446591 : Blo 443779 446591 := bstep (se 1 (by rfl) ⟨334943, by rfl⟩ : syracuseStep 446591 = 669887) B669887
theorem B446619 : Blo 443779 446619 := bstep (se 1 (by rfl) ⟨334964, by rfl⟩ : syracuseStep 446619 = 669929) B669929
theorem B1265863 : Blo 443779 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1069409 : Blo 443779 1069409 := bstep (se 2 (by rfl) ⟨401028, by rfl⟩ : syracuseStep 1069409 = 802057) B802057
theorem B446823 : Blo 443779 446823 := bstep (se 1 (by rfl) ⟨335117, by rfl⟩ : syracuseStep 446823 = 670235) B670235
theorem B676219 : Blo 443779 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B446875 : Blo 443779 446875 := bstep (se 1 (by rfl) ⟨335156, by rfl⟩ : syracuseStep 446875 = 670313) B670313
theorem B447227 : Blo 443779 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B1004345 : Blo 443779 1004345 := bstep (se 2 (by rfl) ⟨376629, by rfl⟩ : syracuseStep 1004345 = 753259) B753259
theorem B447295 : Blo 443779 447295 := bstep (se 1 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 447295 = 670943) B670943
theorem B447323 : Blo 443779 447323 := bstep (se 1 (by rfl) ⟨335492, by rfl⟩ : syracuseStep 447323 = 670985) B670985
theorem B1004399 : Blo 443779 1004399 := bstep (se 1 (by rfl) ⟨753299, by rfl⟩ : syracuseStep 1004399 = 1506599) B1506599
theorem B447391 : Blo 443779 447391 := bstep (se 1 (by rfl) ⟨335543, by rfl⟩ : syracuseStep 447391 = 671087) B671087
theorem B447471 : Blo 443779 447471 := bstep (se 1 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 447471 = 671207) B671207
theorem B447559 : Blo 443779 447559 := bstep (se 1 (by rfl) ⟨335669, by rfl⟩ : syracuseStep 447559 = 671339) B671339
theorem B447643 : Blo 443779 447643 := bstep (se 1 (by rfl) ⟨335732, by rfl⟩ : syracuseStep 447643 = 671465) B671465
theorem B1004705 : Blo 443779 1004705 := bstep (se 2 (by rfl) ⟨376764, by rfl⟩ : syracuseStep 1004705 = 753529) B753529
theorem B447739 : Blo 443779 447739 := bstep (se 1 (by rfl) ⟨335804, by rfl⟩ : syracuseStep 447739 = 671609) B671609
theorem B1004975 : Blo 443779 1004975 := bstep (se 1 (by rfl) ⟨753731, by rfl⟩ : syracuseStep 1004975 = 1507463) B1507463
theorem B7296551 : Blo 443779 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B6116903 : Blo 443779 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B1267321 : Blo 443779 1267321 := bstep (se 2 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 1267321 = 950491) B950491
theorem B3823969 : Blo 443779 3823969 := bstep (se 2 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 3823969 = 2867977) B2867977
theorem B1005983 : Blo 443779 1005983 := bstep (se 1 (by rfl) ⟨754487, by rfl⟩ : syracuseStep 1005983 = 1508975) B1508975
theorem B1006055 : Blo 443779 1006055 := bstep (se 1 (by rfl) ⟨754541, by rfl⟩ : syracuseStep 1006055 = 1509083) B1509083
theorem B3201563 : Blo 443779 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B1694317 : Blo 443779 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B1268551 : Blo 443779 1268551 := bstep (se 1 (by rfl) ⟨951413, by rfl⟩ : syracuseStep 1268551 = 1902827) B1902827
theorem B3824927 : Blo 443779 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B1006919 : Blo 443779 1006919 := bstep (se 1 (by rfl) ⟨755189, by rfl⟩ : syracuseStep 1006919 = 1510379) B1510379
theorem B1006955 : Blo 443779 1006955 := bstep (se 1 (by rfl) ⟨755216, by rfl⟩ : syracuseStep 1006955 = 1510433) B1510433
theorem B1007081 : Blo 443779 1007081 := bstep (se 2 (by rfl) ⟨377655, by rfl⟩ : syracuseStep 1007081 = 755311) B755311
theorem B843385 : Blo 443779 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B3661433 : Blo 443779 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1007225 : Blo 443779 1007225 := bstep (se 2 (by rfl) ⟨377709, by rfl⟩ : syracuseStep 1007225 = 755419) B755419
theorem B1073407 : Blo 443779 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B3400055 : Blo 443779 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B9527759 : Blo 443779 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B3138011 : Blo 443779 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B2548219 : Blo 443779 2548219 := bstep (se 1 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 2548219 = 3822329) B3822329
theorem B1696747 : Blo 443779 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B1205561 : Blo 443779 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B26109773 : Blo 443779 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1501307 : Blo 443779 1501307 := bstep (se 1 (by rfl) ⟨1125980, by rfl⟩ : syracuseStep 1501307 = 2251961) B2251961
theorem B1501577 : Blo 443779 1501577 := bstep (se 2 (by rfl) ⟨563091, by rfl⟩ : syracuseStep 1501577 = 1126183) B1126183
theorem B846217 : Blo 443779 846217 := bstep (se 2 (by rfl) ⟨317331, by rfl⟩ : syracuseStep 846217 = 634663) B634663
theorem B1272311 : Blo 443779 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B20834995 : Blo 443779 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B3435425 : Blo 443779 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B2289091 : Blo 443779 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B5795309 : Blo 443779 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B1044193 : Blo 443779 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B1896335 : Blo 443779 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B749641 : Blo 443779 749641 := bstep (se 2 (by rfl) ⟨281115, by rfl⟩ : syracuseStep 749641 = 562231) B562231
theorem B1503305 : Blo 443779 1503305 := bstep (se 2 (by rfl) ⟨563739, by rfl⟩ : syracuseStep 1503305 = 1127479) B1127479
theorem B1699937 : Blo 443779 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B749695 : Blo 443779 749695 := bstep (se 1 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 749695 = 1124543) B1124543
theorem B46330865 : Blo 443779 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B750775 : Blo 443779 750775 := bstep (se 1 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 750775 = 1126163) B1126163
theorem B1504439 : Blo 443779 1504439 := bstep (se 1 (by rfl) ⟨1128329, by rfl⟩ : syracuseStep 1504439 = 2256659) B2256659
theorem B1799453 : Blo 443779 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B6125057 : Blo 443779 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B3438443 : Blo 443779 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B751531 : Blo 443779 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B2258927 : Blo 443779 2258927 := bstep (se 1 (by rfl) ⟨1694195, by rfl⟩ : syracuseStep 2258927 = 3388391) B3388391
theorem B1505627 : Blo 443779 1505627 := bstep (se 1 (by rfl) ⟨1129220, by rfl⟩ : syracuseStep 1505627 = 2258441) B2258441
theorem B752071 : Blo 443779 752071 := bstep (se 1 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 752071 = 1128107) B1128107
theorem B2718305 : Blo 443779 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1505897 : Blo 443779 1505897 := bstep (se 2 (by rfl) ⟨564711, by rfl⟩ : syracuseStep 1505897 = 1129423) B1129423
theorem B752287 : Blo 443779 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B948971 : Blo 443779 948971 := bstep (se 1 (by rfl) ⟨711728, by rfl⟩ : syracuseStep 948971 = 1423457) B1423457
theorem B72940277 : Blo 443779 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B1375133 : Blo 443779 1375133 := bstep (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) B515675
theorem B4291973 : Blo 443779 4291973 := bstep (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) B804745
theorem B4816493 : Blo 443779 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B1900367 : Blo 443779 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B2883833 : Blo 443779 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B950611 : Blo 443779 950611 := bstep (se 1 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 950611 = 1425917) B1425917
theorem B3375755 : Blo 443779 3375755 := bstep (se 1 (by rfl) ⟨2531816, by rfl⟩ : syracuseStep 3375755 = 5063633) B5063633
theorem B4817569 : Blo 443779 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B2851757 : Blo 443779 2851757 := bstep (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) B1069409
theorem B2262329 : Blo 443779 2262329 := bstep (se 2 (by rfl) ⟨848373, by rfl⟩ : syracuseStep 2262329 = 1696747) B1696747
theorem B3212635 : Blo 443779 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B1508705 : Blo 443779 1508705 := bstep (se 2 (by rfl) ⟨565764, by rfl⟩ : syracuseStep 1508705 = 1131529) B1131529
theorem B1902143 : Blo 443779 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B2262815 : Blo 443779 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B1509245 : Blo 443779 1509245 := bstep (se 3 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 1509245 = 565967) B565967
theorem B5801975 : Blo 443779 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B1509407 : Blo 443779 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B10848491 : Blo 443779 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B854687 : Blo 443779 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B2853625 : Blo 443779 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B2296795 : Blo 443779 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B3214829 : Blo 443779 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B659167 : Blo 443779 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B21630797 : Blo 443779 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B3052121 : Blo 443779 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B1905697 : Blo 443779 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B2266703 : Blo 443779 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B3610655 : Blo 443779 3610655 := bstep (se 1 (by rfl) ⟨2707991, by rfl⟩ : syracuseStep 3610655 = 5415983) B5415983
theorem B17406515 : Blo 443779 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B859643 : Blo 443779 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B1909115 : Blo 443779 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B1812203 : Blo 443779 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B632647 : Blo 443779 632647 := bstep (se 1 (by rfl) ⟨474485, by rfl⟩ : syracuseStep 632647 = 948971) B948971
theorem B1124513 : Blo 443779 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B2894015 : Blo 443779 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B665819 : Blo 443779 665819 := bstep (se 1 (by rfl) ⟨499364, by rfl⟩ : syracuseStep 665819 = 998729) B998729
theorem B2861315 : Blo 443779 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B666089 : Blo 443779 666089 := bstep (se 2 (by rfl) ⟨249783, by rfl⟩ : syracuseStep 666089 = 499567) B499567
theorem B666095 : Blo 443779 666095 := bstep (se 1 (by rfl) ⟨499571, by rfl⟩ : syracuseStep 666095 = 999143) B999143
theorem B4303469 : Blo 443779 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B666407 : Blo 443779 666407 := bstep (se 1 (by rfl) ⟨499805, by rfl⟩ : syracuseStep 666407 = 999611) B999611
theorem B1125191 : Blo 443779 1125191 := bstep (se 1 (by rfl) ⟨843893, by rfl⟩ : syracuseStep 1125191 = 1687787) B1687787
theorem B3812183 : Blo 443779 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B666479 : Blo 443779 666479 := bstep (se 1 (by rfl) ⟨499859, by rfl⟩ : syracuseStep 666479 = 999719) B999719
theorem B17443907 : Blo 443779 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B666731 : Blo 443779 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B1387703 : Blo 443779 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B666971 : Blo 443779 666971 := bstep (se 1 (by rfl) ⟨500228, by rfl⟩ : syracuseStep 666971 = 1000457) B1000457
theorem B1813855 : Blo 443779 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B667001 : Blo 443779 667001 := bstep (se 2 (by rfl) ⟨250125, by rfl⟩ : syracuseStep 667001 = 500251) B500251
theorem B667007 : Blo 443779 667007 := bstep (se 1 (by rfl) ⟨500255, by rfl⟩ : syracuseStep 667007 = 1000511) B1000511
theorem B667241 : Blo 443779 667241 := bstep (se 2 (by rfl) ⟨250215, by rfl⟩ : syracuseStep 667241 = 500431) B500431
theorem B2535097 : Blo 443779 2535097 := bstep (se 2 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 2535097 = 1901323) B1901323
theorem B4828987 : Blo 443779 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B667631 : Blo 443779 667631 := bstep (se 1 (by rfl) ⟨500723, by rfl⟩ : syracuseStep 667631 = 1001447) B1001447
theorem B667751 : Blo 443779 667751 := bstep (se 1 (by rfl) ⟨500813, by rfl⟩ : syracuseStep 667751 = 1001627) B1001627
theorem B4468931 : Blo 443779 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B667871 : Blo 443779 667871 := bstep (se 1 (by rfl) ⟨500903, by rfl⟩ : syracuseStep 667871 = 1001807) B1001807
theorem B667931 : Blo 443779 667931 := bstep (se 1 (by rfl) ⟨500948, by rfl⟩ : syracuseStep 667931 = 1001897) B1001897
theorem B668327 : Blo 443779 668327 := bstep (se 1 (by rfl) ⟨501245, by rfl⟩ : syracuseStep 668327 = 1002491) B1002491
theorem B668447 : Blo 443779 668447 := bstep (se 1 (by rfl) ⟨501335, by rfl⟩ : syracuseStep 668447 = 1002671) B1002671
theorem B668471 : Blo 443779 668471 := bstep (se 1 (by rfl) ⟨501353, by rfl⟩ : syracuseStep 668471 = 1002707) B1002707
theorem B668585 : Blo 443779 668585 := bstep (se 2 (by rfl) ⟨250719, by rfl⟩ : syracuseStep 668585 = 501439) B501439
theorem B668651 : Blo 443779 668651 := bstep (se 1 (by rfl) ⟨501488, by rfl⟩ : syracuseStep 668651 = 1002977) B1002977
theorem B668927 : Blo 443779 668927 := bstep (se 1 (by rfl) ⟨501695, by rfl⟩ : syracuseStep 668927 = 1003391) B1003391
theorem B668969 : Blo 443779 668969 := bstep (se 2 (by rfl) ⟨250863, by rfl⟩ : syracuseStep 668969 = 501727) B501727
theorem B4273519 : Blo 443779 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B1357231 : Blo 443779 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B1128289 : Blo 443779 1128289 := bstep (se 2 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 1128289 = 846217) B846217
theorem B669563 : Blo 443779 669563 := bstep (se 1 (by rfl) ⟨502172, by rfl⟩ : syracuseStep 669563 = 1004345) B1004345
theorem B1685387 : Blo 443779 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B636827 : Blo 443779 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B669599 : Blo 443779 669599 := bstep (se 1 (by rfl) ⟨502199, by rfl⟩ : syracuseStep 669599 = 1004399) B1004399
theorem B4798541 : Blo 443779 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B669803 : Blo 443779 669803 := bstep (se 1 (by rfl) ⟨502352, by rfl⟩ : syracuseStep 669803 = 1004705) B1004705
theorem B669833 : Blo 443779 669833 := bstep (se 2 (by rfl) ⟨251187, by rfl⟩ : syracuseStep 669833 = 502375) B502375
theorem B4569281 : Blo 443779 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B669983 : Blo 443779 669983 := bstep (se 1 (by rfl) ⟨502487, by rfl⟩ : syracuseStep 669983 = 1004975) B1004975
theorem B4864367 : Blo 443779 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B4077935 : Blo 443779 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B670655 : Blo 443779 670655 := bstep (se 1 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 670655 = 1005983) B1005983
theorem B506863 : Blo 443779 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B670703 : Blo 443779 670703 := bstep (se 1 (by rfl) ⟨503027, by rfl⟩ : syracuseStep 670703 = 1006055) B1006055
theorem B670889 : Blo 443779 670889 := bstep (se 2 (by rfl) ⟨251583, by rfl⟩ : syracuseStep 670889 = 503167) B503167
theorem B3653003 : Blo 443779 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B16235939 : Blo 443779 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B1424891 : Blo 443779 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B671279 : Blo 443779 671279 := bstep (se 1 (by rfl) ⟨503459, by rfl⟩ : syracuseStep 671279 = 1006919) B1006919
theorem B671303 : Blo 443779 671303 := bstep (se 1 (by rfl) ⟨503477, by rfl⟩ : syracuseStep 671303 = 1006955) B1006955
theorem B1392257 : Blo 443779 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B671387 : Blo 443779 671387 := bstep (se 1 (by rfl) ⟨503540, by rfl⟩ : syracuseStep 671387 = 1007081) B1007081
theorem B2440955 : Blo 443779 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B671483 : Blo 443779 671483 := bstep (se 1 (by rfl) ⟨503612, by rfl⟩ : syracuseStep 671483 = 1007225) B1007225
theorem B999521 : Blo 443779 999521 := bstep (se 2 (by rfl) ⟨374820, by rfl⟩ : syracuseStep 999521 = 749641) B749641
theorem B999593 : Blo 443779 999593 := bstep (se 2 (by rfl) ⟨374847, by rfl⟩ : syracuseStep 999593 = 749695) B749695
theorem B1687817 : Blo 443779 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B901625 : Blo 443779 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B1426301 : Blo 443779 1426301 := bstep (se 3 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 1426301 = 534863) B534863
theorem B8537501 : Blo 443779 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B1000871 : Blo 443779 1000871 := bstep (se 1 (by rfl) ⟨750653, by rfl⟩ : syracuseStep 1000871 = 1501307) B1501307
theorem B1001033 : Blo 443779 1001033 := bstep (se 2 (by rfl) ⟨375387, by rfl⟩ : syracuseStep 1001033 = 750775) B750775
theorem B443995 : Blo 443779 443995 := bstep (se 1 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 443995 = 665993) B665993
theorem B1001051 : Blo 443779 1001051 := bstep (se 1 (by rfl) ⟨750788, by rfl⟩ : syracuseStep 1001051 = 1501577) B1501577
theorem B1689761 : Blo 443779 1689761 := bstep (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) B1267321
theorem B444623 : Blo 443779 444623 := bstep (se 1 (by rfl) ⟨333467, by rfl⟩ : syracuseStep 444623 = 666935) B666935
theorem B444735 : Blo 443779 444735 := bstep (se 1 (by rfl) ⟨333551, by rfl⟩ : syracuseStep 444735 = 667103) B667103
theorem B444879 : Blo 443779 444879 := bstep (se 1 (by rfl) ⟨333659, by rfl⟩ : syracuseStep 444879 = 667319) B667319
theorem B1002041 : Blo 443779 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B445019 : Blo 443779 445019 := bstep (se 1 (by rfl) ⟨333764, by rfl⟩ : syracuseStep 445019 = 667529) B667529
theorem B1264223 : Blo 443779 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B1002203 : Blo 443779 1002203 := bstep (se 1 (by rfl) ⟨751652, by rfl⟩ : syracuseStep 1002203 = 1503305) B1503305
theorem B1133291 : Blo 443779 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B445183 : Blo 443779 445183 := bstep (se 1 (by rfl) ⟨333887, by rfl⟩ : syracuseStep 445183 = 667775) B667775
theorem B903943 : Blo 443779 903943 := bstep (se 1 (by rfl) ⟨677957, by rfl⟩ : syracuseStep 903943 = 1355915) B1355915
theorem B4836347 : Blo 443779 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B1690733 : Blo 443779 1690733 := bstep (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) B634025
theorem B5098625 : Blo 443779 5098625 := bstep (se 2 (by rfl) ⟨1911984, by rfl⟩ : syracuseStep 5098625 = 3823969) B3823969
theorem B445607 : Blo 443779 445607 := bstep (se 1 (by rfl) ⟨334205, by rfl⟩ : syracuseStep 445607 = 668411) B668411
theorem B2411707 : Blo 443779 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B1002761 : Blo 443779 1002761 := bstep (se 2 (by rfl) ⟨376035, by rfl⟩ : syracuseStep 1002761 = 752071) B752071
theorem B30887243 : Blo 443779 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B1002959 : Blo 443779 1002959 := bstep (se 1 (by rfl) ⟨752219, by rfl⟩ : syracuseStep 1002959 = 1504439) B1504439
theorem B445903 : Blo 443779 445903 := bstep (se 1 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 445903 = 668855) B668855
theorem B1003049 : Blo 443779 1003049 := bstep (se 2 (by rfl) ⟨376143, by rfl⟩ : syracuseStep 1003049 = 752287) B752287
theorem B446063 : Blo 443779 446063 := bstep (se 1 (by rfl) ⟨334547, by rfl⟩ : syracuseStep 446063 = 669095) B669095
theorem B27512459 : Blo 443779 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B4083371 : Blo 443779 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B446183 : Blo 443779 446183 := bstep (se 1 (by rfl) ⟨334637, by rfl⟩ : syracuseStep 446183 = 669275) B669275
theorem B1691401 : Blo 443779 1691401 := bstep (se 2 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 1691401 = 1268551) B1268551
theorem B1691675 : Blo 443779 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B446491 : Blo 443779 446491 := bstep (se 1 (by rfl) ⟨334868, by rfl⟩ : syracuseStep 446491 = 669737) B669737
theorem B446511 : Blo 443779 446511 := bstep (se 1 (by rfl) ⟨334883, by rfl⟩ : syracuseStep 446511 = 669767) B669767
theorem B1003751 : Blo 443779 1003751 := bstep (se 1 (by rfl) ⟨752813, by rfl⟩ : syracuseStep 1003751 = 1505627) B1505627
theorem B446767 : Blo 443779 446767 := bstep (se 1 (by rfl) ⟨335075, by rfl⟩ : syracuseStep 446767 = 670151) B670151
theorem B1003931 : Blo 443779 1003931 := bstep (se 1 (by rfl) ⟨752948, by rfl⟩ : syracuseStep 1003931 = 1505897) B1505897
theorem B446911 : Blo 443779 446911 := bstep (se 1 (by rfl) ⟨335183, by rfl⟩ : syracuseStep 446911 = 670367) B670367
theorem B447007 : Blo 443779 447007 := bstep (se 1 (by rfl) ⟨335255, by rfl⟩ : syracuseStep 447007 = 670511) B670511
theorem B447087 : Blo 443779 447087 := bstep (se 1 (by rfl) ⟨335315, by rfl⟩ : syracuseStep 447087 = 670631) B670631
theorem B447207 : Blo 443779 447207 := bstep (se 1 (by rfl) ⟨335405, by rfl⟩ : syracuseStep 447207 = 670811) B670811
theorem B447455 : Blo 443779 447455 := bstep (se 1 (by rfl) ⟨335591, by rfl⟩ : syracuseStep 447455 = 671183) B671183
theorem B1266911 : Blo 443779 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B447711 : Blo 443779 447711 := bstep (se 1 (by rfl) ⟨335783, by rfl⟩ : syracuseStep 447711 = 671567) B671567
theorem B906491 : Blo 443779 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B1431209 : Blo 443779 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B3397625 : Blo 443779 3397625 := bstep (se 2 (by rfl) ⟨1274109, by rfl⟩ : syracuseStep 3397625 = 2548219) B2548219
theorem B1267721 : Blo 443779 1267721 := bstep (se 2 (by rfl) ⟨475395, by rfl⟩ : syracuseStep 1267721 = 950791) B950791
theorem B20666843 : Blo 443779 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B1432235 : Blo 443779 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B842633 : Blo 443779 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B842663 : Blo 443779 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B1006505 : Blo 443779 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B2547035 : Blo 443779 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B3202487 : Blo 443779 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B1498877 : Blo 443779 1498877 := bstep (se 3 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 1498877 = 562079) B562079
theorem B843689 : Blo 443779 843689 := bstep (se 2 (by rfl) ⟨316383, by rfl⟩ : syracuseStep 843689 = 632767) B632767
theorem B1270009 : Blo 443779 1270009 := bstep (se 2 (by rfl) ⟨476253, by rfl⟩ : syracuseStep 1270009 = 952507) B952507
theorem B27779993 : Blo 443779 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B2548745 : Blo 443779 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B1271467 : Blo 443779 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B1271855 : Blo 443779 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B2549951 : Blo 443779 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B1272095 : Blo 443779 1272095 := bstep (se 1 (by rfl) ⟨954071, by rfl⟩ : syracuseStep 1272095 = 1908143) B1908143
theorem B6351839 : Blo 443779 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B2092007 : Blo 443779 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B5139571 : Blo 443779 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B3370895 : Blo 443779 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B848207 : Blo 443779 848207 := bstep (se 1 (by rfl) ⟨636155, by rfl⟩ : syracuseStep 848207 = 1272311) B1272311
theorem B2290283 : Blo 443779 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B58782665 : Blo 443779 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B3863539 : Blo 443779 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B3667021 : Blo 443779 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B751207 : Blo 443779 751207 := bstep (se 1 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 751207 = 1126811) B1126811
theorem B816743 : Blo 443779 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1603319 : Blo 443779 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1210103 : Blo 443779 1210103 := bstep (se 1 (by rfl) ⟨907577, by rfl⟩ : syracuseStep 1210103 = 1815155) B1815155
theorem B2848553 : Blo 443779 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B3897371 : Blo 443779 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B2259089 : Blo 443779 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B4356299 : Blo 443779 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B751835 : Blo 443779 751835 := bstep (se 1 (by rfl) ⟨563876, by rfl⟩ : syracuseStep 751835 = 1127753) B1127753
theorem B752105 : Blo 443779 752105 := bstep (se 2 (by rfl) ⟨282039, by rfl⟩ : syracuseStep 752105 = 564079) B564079
theorem B2292295 : Blo 443779 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B1505951 : Blo 443779 1505951 := bstep (se 1 (by rfl) ⟨1129463, by rfl⟩ : syracuseStep 1505951 = 2258927) B2258927
theorem B48626851 : Blo 443779 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B753131 : Blo 443779 753131 := bstep (se 1 (by rfl) ⟨564848, by rfl⟩ : syracuseStep 753131 = 1129697) B1129697
theorem B3210995 : Blo 443779 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B950867 : Blo 443779 950867 := bstep (se 1 (by rfl) ⟨713150, by rfl⟩ : syracuseStep 950867 = 1426301) B1426301
theorem B1901171 : Blo 443779 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B1508219 : Blo 443779 1508219 := bstep (se 1 (by rfl) ⟨1131164, by rfl⟩ : syracuseStep 1508219 = 2262329) B2262329
theorem B6423425 : Blo 443779 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B1508543 : Blo 443779 1508543 := bstep (se 1 (by rfl) ⟨1131407, by rfl⟩ : syracuseStep 1508543 = 2262815) B2262815
theorem B3867983 : Blo 443779 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B755527 : Blo 443779 755527 := bstep (se 1 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 755527 = 1133291) B1133291
theorem B2722247 : Blo 443779 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B14420531 : Blo 443779 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B3804833 : Blo 443779 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B1511135 : Blo 443779 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B2265083 : Blo 443779 2265083 := bstep (se 1 (by rfl) ⟨1698812, by rfl⟩ : syracuseStep 2265083 = 3397625) B3397625
theorem B4821029 : Blo 443779 4821029 := bstep (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) B903943
theorem B6852761 : Blo 443779 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B3215609 : Blo 443779 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B11604343 : Blo 443779 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B954823 : Blo 443779 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B561755 : Blo 443779 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B3380129 : Blo 443779 3380129 := bstep (se 2 (by rfl) ⟨1267548, by rfl⟩ : syracuseStep 3380129 = 2535097) B2535097
theorem B2134991 : Blo 443779 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B562459 : Blo 443779 562459 := bstep (se 1 (by rfl) ⟨421844, by rfl⟩ : syracuseStep 562459 = 843689) B843689
theorem B18519995 : Blo 443779 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B5151385 : Blo 443779 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B1907543 : Blo 443779 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B1809641 : Blo 443779 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B4234559 : Blo 443779 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B565471 : Blo 443779 565471 := bstep (se 1 (by rfl) ⟨424103, by rfl⟩ : syracuseStep 565471 = 848207) B848207
theorem B3056393 : Blo 443779 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B9741341 : Blo 443779 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B3515557 : Blo 443779 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B1123591 : Blo 443779 1123591 := bstep (se 1 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 1123591 = 1685387) B1685387
theorem B2598247 : Blo 443779 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B501223 : Blo 443779 501223 := bstep (se 1 (by rfl) ⟨375917, by rfl⟩ : syracuseStep 501223 = 751835) B751835
theorem B501403 : Blo 443779 501403 := bstep (se 1 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 501403 = 752105) B752105
theorem B10823959 : Blo 443779 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B502087 : Blo 443779 502087 := bstep (se 1 (by rfl) ⟨376565, by rfl⟩ : syracuseStep 502087 = 753131) B753131
theorem B928171 : Blo 443779 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B2140663 : Blo 443779 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B666347 : Blo 443779 666347 := bstep (se 1 (by rfl) ⟨499760, by rfl⟩ : syracuseStep 666347 = 999521) B999521
theorem B666395 : Blo 443779 666395 := bstep (se 1 (by rfl) ⟨499796, by rfl⟩ : syracuseStep 666395 = 999593) B999593
theorem B1125211 : Blo 443779 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B667247 : Blo 443779 667247 := bstep (se 1 (by rfl) ⟨500435, by rfl⟩ : syracuseStep 667247 = 1000871) B1000871
theorem B667355 : Blo 443779 667355 := bstep (se 1 (by rfl) ⟨500516, by rfl⟩ : syracuseStep 667355 = 1001033) B1001033
theorem B667367 : Blo 443779 667367 := bstep (se 1 (by rfl) ⟨500525, by rfl⟩ : syracuseStep 667367 = 1001051) B1001051
theorem B2404333 : Blo 443779 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B1126507 : Blo 443779 1126507 := bstep (se 1 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 1126507 = 1689761) B1689761
theorem B8138989 : Blo 443779 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B668027 : Blo 443779 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B569791 : Blo 443779 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B668135 : Blo 443779 668135 := bstep (se 1 (by rfl) ⟨501101, by rfl⟩ : syracuseStep 668135 = 1002203) B1002203
theorem B3224231 : Blo 443779 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B1127155 : Blo 443779 1127155 := bstep (se 1 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 1127155 = 1690733) B1690733
theorem B668507 : Blo 443779 668507 := bstep (se 1 (by rfl) ⟨501380, by rfl⟩ : syracuseStep 668507 = 1002761) B1002761
theorem B20591495 : Blo 443779 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B668639 : Blo 443779 668639 := bstep (se 1 (by rfl) ⟨501479, by rfl⟩ : syracuseStep 668639 = 1002959) B1002959
theorem B2143219 : Blo 443779 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B668699 : Blo 443779 668699 := bstep (se 1 (by rfl) ⟨501524, by rfl⟩ : syracuseStep 668699 = 1003049) B1003049
theorem B1127783 : Blo 443779 1127783 := bstep (se 1 (by rfl) ⟨845837, by rfl⟩ : syracuseStep 1127783 = 1691675) B1691675
theorem B669167 : Blo 443779 669167 := bstep (se 1 (by rfl) ⟨501875, by rfl⟩ : syracuseStep 669167 = 1003751) B1003751
theorem B669287 : Blo 443779 669287 := bstep (se 1 (by rfl) ⟨501965, by rfl⟩ : syracuseStep 669287 = 1003931) B1003931
theorem B3062393 : Blo 443779 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B2407103 : Blo 443779 2407103 := bstep (se 1 (by rfl) ⟨1805327, by rfl⟩ : syracuseStep 2407103 = 3610655) B3610655
theorem B13777895 : Blo 443779 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B3816557 : Blo 443779 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B671003 : Blo 443779 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B4275517 : Blo 443779 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B573095 : Blo 443779 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B6438649 : Blo 443779 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B999251 : Blo 443779 999251 := bstep (se 1 (by rfl) ⟨749438, by rfl⟩ : syracuseStep 999251 = 1498877) B1498877
theorem B2703269 : Blo 443779 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B11616797 : Blo 443779 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B2540929 : Blo 443779 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B443879 : Blo 443779 443879 := bstep (se 1 (by rfl) ⟨332909, by rfl⟩ : syracuseStep 443879 = 665819) B665819
theorem B444059 : Blo 443779 444059 := bstep (se 1 (by rfl) ⟨333044, by rfl⟩ : syracuseStep 444059 = 666089) B666089
theorem B444063 : Blo 443779 444063 := bstep (se 1 (by rfl) ⟨333047, by rfl⟩ : syracuseStep 444063 = 666095) B666095
theorem B2868979 : Blo 443779 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B444271 : Blo 443779 444271 := bstep (se 1 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 444271 = 666407) B666407
theorem B2541455 : Blo 443779 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B444319 : Blo 443779 444319 := bstep (se 1 (by rfl) ⟨333239, by rfl⟩ : syracuseStep 444319 = 666479) B666479
theorem B1394671 : Blo 443779 1394671 := bstep (se 1 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 1394671 = 2092007) B2092007
theorem B444487 : Blo 443779 444487 := bstep (se 1 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 444487 = 666731) B666731
theorem B1001609 : Blo 443779 1001609 := bstep (se 2 (by rfl) ⟨375603, by rfl⟩ : syracuseStep 1001609 = 751207) B751207
theorem B444647 : Blo 443779 444647 := bstep (se 1 (by rfl) ⟨333485, by rfl⟩ : syracuseStep 444647 = 666971) B666971
theorem B444667 : Blo 443779 444667 := bstep (se 1 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 444667 = 667001) B667001
theorem B444671 : Blo 443779 444671 := bstep (se 1 (by rfl) ⟨333503, by rfl⟩ : syracuseStep 444671 = 667007) B667007
theorem B444827 : Blo 443779 444827 := bstep (se 1 (by rfl) ⟨333620, by rfl⟩ : syracuseStep 444827 = 667241) B667241
theorem B2247101 : Blo 443779 2247101 := bstep (se 3 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 2247101 = 842663) B842663
theorem B2247263 : Blo 443779 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B445087 : Blo 443779 445087 := bstep (se 1 (by rfl) ⟨333815, by rfl⟩ : syracuseStep 445087 = 667631) B667631
theorem B445167 : Blo 443779 445167 := bstep (se 1 (by rfl) ⟨333875, by rfl⟩ : syracuseStep 445167 = 667751) B667751
theorem B445247 : Blo 443779 445247 := bstep (se 1 (by rfl) ⟨333935, by rfl⟩ : syracuseStep 445247 = 667871) B667871
theorem B445287 : Blo 443779 445287 := bstep (se 1 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 445287 = 667931) B667931
theorem B1526855 : Blo 443779 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B445551 : Blo 443779 445551 := bstep (se 1 (by rfl) ⟨334163, by rfl⟩ : syracuseStep 445551 = 668327) B668327
theorem B445631 : Blo 443779 445631 := bstep (se 1 (by rfl) ⟨334223, by rfl⟩ : syracuseStep 445631 = 668447) B668447
theorem B445647 : Blo 443779 445647 := bstep (se 1 (by rfl) ⟨334235, by rfl⟩ : syracuseStep 445647 = 668471) B668471
theorem B445723 : Blo 443779 445723 := bstep (se 1 (by rfl) ⟨334292, by rfl⟩ : syracuseStep 445723 = 668585) B668585
theorem B445767 : Blo 443779 445767 := bstep (se 1 (by rfl) ⟨334325, by rfl⟩ : syracuseStep 445767 = 668651) B668651
theorem B445951 : Blo 443779 445951 := bstep (se 1 (by rfl) ⟨334463, by rfl⟩ : syracuseStep 445951 = 668927) B668927
theorem B445979 : Blo 443779 445979 := bstep (se 1 (by rfl) ⟨334484, by rfl⟩ : syracuseStep 445979 = 668969) B668969
theorem B544495 : Blo 443779 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B806735 : Blo 443779 806735 := bstep (se 1 (by rfl) ⟨605051, by rfl⟩ : syracuseStep 806735 = 1210103) B1210103
theorem B446375 : Blo 443779 446375 := bstep (se 1 (by rfl) ⟨334781, by rfl⟩ : syracuseStep 446375 = 669563) B669563
theorem B446399 : Blo 443779 446399 := bstep (se 1 (by rfl) ⟨334799, by rfl⟩ : syracuseStep 446399 = 669599) B669599
theorem B3199027 : Blo 443779 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B446535 : Blo 443779 446535 := bstep (se 1 (by rfl) ⟨334901, by rfl⟩ : syracuseStep 446535 = 669803) B669803
theorem B446555 : Blo 443779 446555 := bstep (se 1 (by rfl) ⟨334916, by rfl⟩ : syracuseStep 446555 = 669833) B669833
theorem B446655 : Blo 443779 446655 := bstep (se 1 (by rfl) ⟨334991, by rfl⟩ : syracuseStep 446655 = 669983) B669983
theorem B64835801 : Blo 443779 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B1003967 : Blo 443779 1003967 := bstep (se 1 (by rfl) ⟨752975, by rfl⟩ : syracuseStep 1003967 = 1505951) B1505951
theorem B447103 : Blo 443779 447103 := bstep (se 1 (by rfl) ⟨335327, by rfl⟩ : syracuseStep 447103 = 670655) B670655
theorem B447135 : Blo 443779 447135 := bstep (se 1 (by rfl) ⟨335351, by rfl⟩ : syracuseStep 447135 = 670703) B670703
theorem B447259 : Blo 443779 447259 := bstep (se 1 (by rfl) ⟨335444, by rfl⟩ : syracuseStep 447259 = 670889) B670889
theorem B447519 : Blo 443779 447519 := bstep (se 1 (by rfl) ⟨335639, by rfl⟩ : syracuseStep 447519 = 671279) B671279
theorem B447535 : Blo 443779 447535 := bstep (se 1 (by rfl) ⟨335651, by rfl⟩ : syracuseStep 447535 = 671303) B671303
theorem B447591 : Blo 443779 447591 := bstep (se 1 (by rfl) ⟨335693, by rfl⟩ : syracuseStep 447591 = 671387) B671387
theorem B1627303 : Blo 443779 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B447655 : Blo 443779 447655 := bstep (se 1 (by rfl) ⟨335741, by rfl⟩ : syracuseStep 447655 = 671483) B671483
theorem B1922555 : Blo 443779 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1693345 : Blo 443779 1693345 := bstep (se 2 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 1693345 = 1270009) B1270009
theorem B2250503 : Blo 443779 2250503 := bstep (se 1 (by rfl) ⟨1687877, by rfl⟩ : syracuseStep 2250503 = 3375755) B3375755
theorem B1267481 : Blo 443779 1267481 := bstep (se 2 (by rfl) ⟨475305, by rfl⟩ : syracuseStep 1267481 = 950611) B950611
theorem B1005803 : Blo 443779 1005803 := bstep (se 1 (by rfl) ⟨754352, by rfl⟩ : syracuseStep 1005803 = 1508705) B1508705
theorem B5691667 : Blo 443779 5691667 := bstep (se 1 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 5691667 = 8537501) B8537501
theorem B1006163 : Blo 443779 1006163 := bstep (se 1 (by rfl) ⟨754622, by rfl⟩ : syracuseStep 1006163 = 1509245) B1509245
theorem B1006271 : Blo 443779 1006271 := bstep (se 1 (by rfl) ⟨754703, by rfl⟩ : syracuseStep 1006271 = 1509407) B1509407
theorem B7232327 : Blo 443779 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B842815 : Blo 443779 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B4283513 : Blo 443779 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B3399083 : Blo 443779 3399083 := bstep (se 1 (by rfl) ⟨2549312, by rfl⟩ : syracuseStep 3399083 = 5098625) B5098625
theorem B1695289 : Blo 443779 1695289 := bstep (se 2 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 1695289 = 1271467) B1271467
theorem B18341639 : Blo 443779 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B843529 : Blo 443779 843529 := bstep (se 2 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 843529 = 632647) B632647
theorem B2417309 : Blo 443779 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B844607 : Blo 443779 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B845147 : Blo 443779 845147 := bstep (se 1 (by rfl) ⟨633860, by rfl⟩ : syracuseStep 845147 = 1267721) B1267721
theorem B5072381 : Blo 443779 5072381 := bstep (se 3 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 5072381 = 1902143) B1902143
theorem B2418473 : Blo 443779 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B1698023 : Blo 443779 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B2255201 : Blo 443779 2255201 := bstep (se 2 (by rfl) ⟨845700, by rfl⟩ : syracuseStep 2255201 = 1691401) B1691401
theorem B1698205 : Blo 443779 1698205 := bstep (se 3 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 1698205 = 636827) B636827
theorem B1272743 : Blo 443779 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B19557445 : Blo 443779 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B1699163 : Blo 443779 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B1208135 : Blo 443779 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B847903 : Blo 443779 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B749675 : Blo 443779 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B1929343 : Blo 443779 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B1699967 : Blo 443779 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B848063 : Blo 443779 848063 := bstep (se 1 (by rfl) ⟨636047, by rfl⟩ : syracuseStep 848063 = 1272095) B1272095
theorem B5698025 : Blo 443779 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B750127 : Blo 443779 750127 := bstep (se 1 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 750127 = 1125191) B1125191
theorem B11629271 : Blo 443779 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B1504385 : Blo 443779 1504385 := bstep (se 2 (by rfl) ⟨564144, by rfl⟩ : syracuseStep 1504385 = 1128289) B1128289
theorem B2979287 : Blo 443779 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B3700541 : Blo 443779 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B39188443 : Blo 443779 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B1899035 : Blo 443779 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B3799709 : Blo 443779 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B1506059 : Blo 443779 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B3046187 : Blo 443779 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B3242911 : Blo 443779 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B2718623 : Blo 443779 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B753961 : Blo 443779 753961 := bstep (se 2 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 753961 = 565471) B565471
theorem B16286453 : Blo 443779 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B4687409 : Blo 443779 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B4950245 : Blo 443779 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B1510055 : Blo 443779 1510055 := bstep (se 1 (by rfl) ⟨1132541, by rfl⟩ : syracuseStep 1510055 = 2265083) B2265083
theorem B3214019 : Blo 443779 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B43223867 : Blo 443779 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B2264273 : Blo 443779 2264273 := bstep (se 2 (by rfl) ⟨849102, by rfl⟩ : syracuseStep 2264273 = 1698205) B1698205
theorem B2854217 : Blo 443779 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B4821551 : Blo 443779 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B2855675 : Blo 443779 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B2266055 : Blo 443779 2266055 := bstep (se 1 (by rfl) ⟨1699541, by rfl⟩ : syracuseStep 2266055 = 3399083) B3399083
theorem B725993 : Blo 443779 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B12227759 : Blo 443779 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B4265369 : Blo 443779 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B10851985 : Blo 443779 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B1611539 : Blo 443779 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B15472457 : Blo 443779 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B759721 : Blo 443779 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B563431 : Blo 443779 563431 := bstep (se 1 (by rfl) ⟨422573, by rfl⟩ : syracuseStep 563431 = 845147) B845147
theorem B3381587 : Blo 443779 3381587 := bstep (se 1 (by rfl) ⟨2536190, by rfl⟩ : syracuseStep 3381587 = 5072381) B5072381
theorem B1612315 : Blo 443779 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B2857625 : Blo 443779 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B2169737 : Blo 443779 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B36741053 : Blo 443779 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B499783 : Blo 443779 499783 := bstep (se 1 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 499783 = 749675) B749675
theorem B565375 : Blo 443779 565375 := bstep (se 1 (by rfl) ⟨424031, by rfl⟩ : syracuseStep 565375 = 848063) B848063
theorem B2467027 : Blo 443779 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B1123753 : Blo 443779 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B2041595 : Blo 443779 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B2533139 : Blo 443779 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B1812415 : Blo 443779 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B3221693 : Blo 443779 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B1124705 : Blo 443779 1124705 := bstep (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) B843529
theorem B666167 : Blo 443779 666167 := bstep (se 1 (by rfl) ⟨499625, by rfl⟩ : syracuseStep 666167 = 999251) B999251
theorem B633911 : Blo 443779 633911 := bstep (se 1 (by rfl) ⟨475433, by rfl⟩ : syracuseStep 633911 = 950867) B950867
theorem B30978125 : Blo 443779 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B667739 : Blo 443779 667739 := bstep (se 1 (by rfl) ⟨500804, by rfl⟩ : syracuseStep 667739 = 1001609) B1001609
theorem B1814831 : Blo 443779 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B9613687 : Blo 443779 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B3387905 : Blo 443779 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B668297 : Blo 443779 668297 := bstep (se 2 (by rfl) ⟨250611, by rfl⟩ : syracuseStep 668297 = 501223) B501223
theorem B668537 : Blo 443779 668537 := bstep (se 2 (by rfl) ⟨250701, by rfl⟩ : syracuseStep 668537 = 501403) B501403
theorem B2536555 : Blo 443779 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B537823 : Blo 443779 537823 := bstep (se 1 (by rfl) ⟨403367, by rfl⟩ : syracuseStep 537823 = 806735) B806735
theorem B4568507 : Blo 443779 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2143739 : Blo 443779 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B669311 : Blo 443779 669311 := bstep (se 1 (by rfl) ⟨501983, by rfl⟩ : syracuseStep 669311 = 1003967) B1003967
theorem B14431945 : Blo 443779 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B669449 : Blo 443779 669449 := bstep (se 2 (by rfl) ⟨251043, by rfl⟩ : syracuseStep 669449 = 502087) B502087
theorem B1423327 : Blo 443779 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B5126813 : Blo 443779 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B670535 : Blo 443779 670535 := bstep (se 1 (by rfl) ⟨502901, by rfl⟩ : syracuseStep 670535 = 1005803) B1005803
theorem B670775 : Blo 443779 670775 := bstep (se 1 (by rfl) ⟨503081, by rfl⟩ : syracuseStep 670775 = 1006163) B1006163
theorem B670847 : Blo 443779 670847 := bstep (se 1 (by rfl) ⟨503135, by rfl⟩ : syracuseStep 670847 = 1006271) B1006271
theorem B1130537 : Blo 443779 1130537 := bstep (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) B847903
theorem B2572457 : Blo 443779 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B1000169 : Blo 443779 1000169 := bstep (se 2 (by rfl) ⟨375063, by rfl⟩ : syracuseStep 1000169 = 750127) B750127
theorem B1132015 : Blo 443779 1132015 := bstep (se 1 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 1132015 = 1698023) B1698023
theorem B444231 : Blo 443779 444231 := bstep (se 1 (by rfl) ⟨333173, by rfl⟩ : syracuseStep 444231 = 666347) B666347
theorem B444263 : Blo 443779 444263 := bstep (se 1 (by rfl) ⟨333197, by rfl⟩ : syracuseStep 444263 = 666395) B666395
theorem B1132775 : Blo 443779 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B444831 : Blo 443779 444831 := bstep (se 1 (by rfl) ⟨333623, by rfl⟩ : syracuseStep 444831 = 667247) B667247
theorem B444903 : Blo 443779 444903 := bstep (se 1 (by rfl) ⟨333677, by rfl⟩ : syracuseStep 444903 = 667355) B667355
theorem B444911 : Blo 443779 444911 := bstep (se 1 (by rfl) ⟨333683, by rfl⟩ : syracuseStep 444911 = 667367) B667367
theorem B52251257 : Blo 443779 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B1133311 : Blo 443779 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B445351 : Blo 443779 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B445423 : Blo 443779 445423 := bstep (se 1 (by rfl) ⟨334067, by rfl⟩ : syracuseStep 445423 = 668135) B668135
theorem B7588889 : Blo 443779 7588889 := bstep (se 2 (by rfl) ⟨2845833, by rfl⟩ : syracuseStep 7588889 = 5691667) B5691667
theorem B2149487 : Blo 443779 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B7752847 : Blo 443779 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B445671 : Blo 443779 445671 := bstep (se 1 (by rfl) ⟨334253, by rfl⟩ : syracuseStep 445671 = 668507) B668507
theorem B445759 : Blo 443779 445759 := bstep (se 1 (by rfl) ⟨334319, by rfl⟩ : syracuseStep 445759 = 668639) B668639
theorem B445799 : Blo 443779 445799 := bstep (se 1 (by rfl) ⟨334349, by rfl⟩ : syracuseStep 445799 = 668699) B668699
theorem B1002923 : Blo 443779 1002923 := bstep (se 1 (by rfl) ⟨752192, by rfl⟩ : syracuseStep 1002923 = 1504385) B1504385
theorem B11292157 : Blo 443779 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B6868513 : Blo 443779 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1986191 : Blo 443779 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B446111 : Blo 443779 446111 := bstep (se 1 (by rfl) ⟨334583, by rfl⟩ : syracuseStep 446111 = 669167) B669167
theorem B446191 : Blo 443779 446191 := bstep (se 1 (by rfl) ⟨334643, by rfl⟩ : syracuseStep 446191 = 669287) B669287
theorem B1266023 : Blo 443779 1266023 := bstep (se 1 (by rfl) ⟨949517, by rfl⟩ : syracuseStep 1266023 = 1899035) B1899035
theorem B1528253 : Blo 443779 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B1004039 : Blo 443779 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B2544371 : Blo 443779 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B447335 : Blo 443779 447335 := bstep (se 1 (by rfl) ⟨335501, by rfl⟩ : syracuseStep 447335 = 671003) B671003
theorem B1267447 : Blo 443779 1267447 := bstep (se 1 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 1267447 = 1901171) B1901171
theorem B1005479 : Blo 443779 1005479 := bstep (se 1 (by rfl) ⟨754109, by rfl⟩ : syracuseStep 1005479 = 1508219) B1508219
theorem B4282283 : Blo 443779 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1005695 : Blo 443779 1005695 := bstep (se 1 (by rfl) ⟨754271, by rfl⟩ : syracuseStep 1005695 = 1508543) B1508543
theorem B2578655 : Blo 443779 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1694303 : Blo 443779 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B1498013 : Blo 443779 1498013 := bstep (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) B561755
theorem B1498067 : Blo 443779 1498067 := bstep (se 1 (by rfl) ⟨1123550, by rfl⟩ : syracuseStep 1498067 = 2247101) B2247101
theorem B1498121 : Blo 443779 1498121 := bstep (se 2 (by rfl) ⟨561795, by rfl⟩ : syracuseStep 1498121 = 1123591) B1123591
theorem B1498175 : Blo 443779 1498175 := bstep (se 1 (by rfl) ⟨1123631, by rfl⟩ : syracuseStep 1498175 = 2247263) B2247263
theorem B3464329 : Blo 443779 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B8150381 : Blo 443779 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B2252285 : Blo 443779 2252285 := bstep (se 3 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 2252285 = 844607) B844607
theorem B3825305 : Blo 443779 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B1007369 : Blo 443779 1007369 := bstep (se 2 (by rfl) ⟨377763, by rfl⟩ : syracuseStep 1007369 = 755527) B755527
theorem B1007423 : Blo 443779 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B1859561 : Blo 443779 1859561 := bstep (se 2 (by rfl) ⟨697335, by rfl⟩ : syracuseStep 1859561 = 1394671) B1394671
theorem B25976909 : Blo 443779 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B2253419 : Blo 443779 2253419 := bstep (se 1 (by rfl) ⟨1690064, by rfl⟩ : syracuseStep 2253419 = 3380129) B3380129
theorem B1500281 : Blo 443779 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B1500335 : Blo 443779 1500335 := bstep (se 1 (by rfl) ⟨1125251, by rfl⟩ : syracuseStep 1500335 = 2250503) B2250503
theorem B844987 : Blo 443779 844987 := bstep (se 1 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 844987 = 1267481) B1267481
theorem B12346663 : Blo 443779 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B26076593 : Blo 443779 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B1271695 : Blo 443779 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B1206427 : Blo 443779 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B3205777 : Blo 443779 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B1502009 : Blo 443779 1502009 := bstep (se 2 (by rfl) ⟨563253, by rfl⟩ : syracuseStep 1502009 = 1126507) B1126507
theorem B1273097 : Blo 443779 1273097 := bstep (se 2 (by rfl) ⟨477411, by rfl⟩ : syracuseStep 1273097 = 954823) B954823
theorem B1502873 : Blo 443779 1502873 := bstep (se 2 (by rfl) ⟨563577, by rfl⟩ : syracuseStep 1502873 = 1127155) B1127155
theorem B1503467 : Blo 443779 1503467 := bstep (se 1 (by rfl) ⟨1127600, by rfl⟩ : syracuseStep 1503467 = 2255201) B2255201
theorem B749945 : Blo 443779 749945 := bstep (se 2 (by rfl) ⟨281229, by rfl⟩ : syracuseStep 749945 = 562459) B562459
theorem B848495 : Blo 443779 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B2257793 : Blo 443779 2257793 := bstep (se 2 (by rfl) ⟨846672, by rfl⟩ : syracuseStep 2257793 = 1693345) B1693345
theorem B3798683 : Blo 443779 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B13727663 : Blo 443779 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B751855 : Blo 443779 751855 := bstep (se 1 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 751855 = 1127783) B1127783
theorem B4323881 : Blo 443779 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B5700689 : Blo 443779 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B1604735 : Blo 443779 1604735 := bstep (se 1 (by rfl) ⟨1203551, by rfl⟩ : syracuseStep 1604735 = 2407103) B2407103
theorem B2030791 : Blo 443779 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B2260385 : Blo 443779 2260385 := bstep (se 2 (by rfl) ⟨847644, by rfl⟩ : syracuseStep 2260385 = 1695289) B1695289
theorem B8584865 : Blo 443779 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B1802179 : Blo 443779 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B753691 : Blo 443779 753691 := bstep (se 1 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 753691 = 1130537) B1130537
theorem B753833 : Blo 443779 753833 := bstep (se 2 (by rfl) ⟨282687, by rfl⟩ : syracuseStep 753833 = 565375) B565375
theorem B69271757 : Blo 443779 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B755183 : Blo 443779 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B2262653 : Blo 443779 2262653 := bstep (se 3 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 2262653 = 848495) B848495
theorem B34834171 : Blo 443779 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B1509353 : Blo 443779 1509353 := bstep (se 2 (by rfl) ⟨566007, by rfl⟩ : syracuseStep 1509353 = 1132015) B1132015
theorem B1509515 : Blo 443779 1509515 := bstep (se 1 (by rfl) ⟨1132136, by rfl⟩ : syracuseStep 1509515 = 2264273) B2264273
theorem B1902811 : Blo 443779 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B1608569 : Blo 443779 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B1018835 : Blo 443779 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B3214367 : Blo 443779 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B1510703 : Blo 443779 1510703 := bstep (se 1 (by rfl) ⟨1133027, by rfl⟩ : syracuseStep 1510703 = 2266055) B2266055
theorem B1511081 : Blo 443779 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B2854855 : Blo 443779 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B1905083 : Blo 443779 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B1446491 : Blo 443779 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B12818249 : Blo 443779 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B3382073 : Blo 443779 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B19242593 : Blo 443779 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B20652083 : Blo 443779 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B499963 : Blo 443779 499963 := bstep (se 1 (by rfl) ⟨374972, by rfl⟩ : syracuseStep 499963 = 749945) B749945
theorem B2532455 : Blo 443779 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B9151775 : Blo 443779 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B3417875 : Blo 443779 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B2402905 : Blo 443779 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B666377 : Blo 443779 666377 := bstep (se 2 (by rfl) ⟨249891, by rfl⟩ : syracuseStep 666377 = 499783) B499783
theorem B6859885 : Blo 443779 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B666779 : Blo 443779 666779 := bstep (se 1 (by rfl) ⟨500084, by rfl⟩ : syracuseStep 666779 = 1000169) B1000169
theorem B10857635 : Blo 443779 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B3124939 : Blo 443779 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B1126649 : Blo 443779 1126649 := bstep (se 2 (by rfl) ⟨422493, by rfl⟩ : syracuseStep 1126649 = 844987) B844987
theorem B3289369 : Blo 443779 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B16462217 : Blo 443779 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B28815911 : Blo 443779 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B7615133 : Blo 443779 7615133 := bstep (se 3 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 7615133 = 2855675) B2855675
theorem B5059259 : Blo 443779 5059259 := bstep (se 1 (by rfl) ⟨3794444, by rfl⟩ : syracuseStep 5059259 = 7588889) B7588889
theorem B668615 : Blo 443779 668615 := bstep (se 1 (by rfl) ⟨501461, by rfl⟩ : syracuseStep 668615 = 1002923) B1002923
theorem B1324127 : Blo 443779 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B669359 : Blo 443779 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B4274369 : Blo 443779 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B670319 : Blo 443779 670319 := bstep (se 1 (by rfl) ⟨502739, by rfl⟩ : syracuseStep 670319 = 1005479) B1005479
theorem B670463 : Blo 443779 670463 := bstep (se 1 (by rfl) ⟨502847, by rfl⟩ : syracuseStep 670463 = 1005695) B1005695
theorem B1719103 : Blo 443779 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B10337129 : Blo 443779 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B1129535 : Blo 443779 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B998675 : Blo 443779 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B998711 : Blo 443779 998711 := bstep (se 1 (by rfl) ⟨749033, by rfl⟩ : syracuseStep 998711 = 1498067) B1498067
theorem B15056209 : Blo 443779 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B998747 : Blo 443779 998747 := bstep (se 1 (by rfl) ⟨749060, by rfl⟩ : syracuseStep 998747 = 1498121) B1498121
theorem B998783 : Blo 443779 998783 := bstep (se 1 (by rfl) ⟨749087, by rfl⟩ : syracuseStep 998783 = 1498175) B1498175
theorem B9158017 : Blo 443779 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B671579 : Blo 443779 671579 := bstep (se 1 (by rfl) ⟨503684, by rfl⟩ : syracuseStep 671579 = 1007369) B1007369
theorem B671615 : Blo 443779 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B24494035 : Blo 443779 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B1000187 : Blo 443779 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B1000223 : Blo 443779 1000223 := bstep (se 1 (by rfl) ⟨750167, by rfl⟩ : syracuseStep 1000223 = 1500335) B1500335
theorem B17384395 : Blo 443779 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B1361063 : Blo 443779 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B1688759 : Blo 443779 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B2147795 : Blo 443779 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B444111 : Blo 443779 444111 := bstep (se 1 (by rfl) ⟨333083, by rfl⟩ : syracuseStep 444111 = 666167) B666167
theorem B8570717 : Blo 443779 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B1001339 : Blo 443779 1001339 := bstep (se 1 (by rfl) ⟨751004, by rfl⟩ : syracuseStep 1001339 = 1502009) B1502009
theorem B14469313 : Blo 443779 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B1689929 : Blo 443779 1689929 := bstep (se 2 (by rfl) ⟨633723, by rfl⟩ : syracuseStep 1689929 = 1267447) B1267447
theorem B1001915 : Blo 443779 1001915 := bstep (se 1 (by rfl) ⟨751436, by rfl⟩ : syracuseStep 1001915 = 1502873) B1502873
theorem B445159 : Blo 443779 445159 := bstep (se 1 (by rfl) ⟨333869, by rfl⟩ : syracuseStep 445159 = 667739) B667739
theorem B1690429 : Blo 443779 1690429 := bstep (se 3 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 1690429 = 633911) B633911
theorem B1002311 : Blo 443779 1002311 := bstep (se 1 (by rfl) ⟨751733, by rfl⟩ : syracuseStep 1002311 = 1503467) B1503467
theorem B1002473 : Blo 443779 1002473 := bstep (se 2 (by rfl) ⟨375927, by rfl⟩ : syracuseStep 1002473 = 751855) B751855
theorem B445531 : Blo 443779 445531 := bstep (se 1 (by rfl) ⟨334148, by rfl⟩ : syracuseStep 445531 = 668297) B668297
theorem B445691 : Blo 443779 445691 := bstep (se 1 (by rfl) ⟨334268, by rfl⟩ : syracuseStep 445691 = 668537) B668537
theorem B2149753 : Blo 443779 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B1429159 : Blo 443779 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B446207 : Blo 443779 446207 := bstep (se 1 (by rfl) ⟨334655, by rfl⟩ : syracuseStep 446207 = 669311) B669311
theorem B446299 : Blo 443779 446299 := bstep (se 1 (by rfl) ⟨334724, by rfl⟩ : syracuseStep 446299 = 669449) B669449
theorem B2707721 : Blo 443779 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B447023 : Blo 443779 447023 := bstep (se 1 (by rfl) ⟨335267, by rfl⟩ : syracuseStep 447023 = 670535) B670535
theorem B447183 : Blo 443779 447183 := bstep (se 1 (by rfl) ⟨335387, by rfl⟩ : syracuseStep 447183 = 670775) B670775
theorem B1069823 : Blo 443779 1069823 := bstep (se 1 (by rfl) ⟨802367, by rfl⟩ : syracuseStep 1069823 = 1604735) B1604735
theorem B447231 : Blo 443779 447231 := bstep (se 1 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 447231 = 670847) B670847
theorem B5723243 : Blo 443779 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B1005281 : Blo 443779 1005281 := bstep (se 2 (by rfl) ⟨376980, by rfl⟩ : syracuseStep 1005281 = 753961) B753961
theorem B1006703 : Blo 443779 1006703 := bstep (se 1 (by rfl) ⟨755027, by rfl⟩ : syracuseStep 1006703 = 1510055) B1510055
theorem B1498337 : Blo 443779 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B1432991 : Blo 443779 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B1695593 : Blo 443779 1695593 := bstep (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) B1271695
theorem B2416553 : Blo 443779 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B844015 : Blo 443779 844015 := bstep (se 1 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 844015 = 1266023) B1266023
theorem B1696247 : Blo 443779 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B483995 : Blo 443779 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B8151839 : Blo 443779 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B2843579 : Blo 443779 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1074359 : Blo 443779 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B10314971 : Blo 443779 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B2254391 : Blo 443779 2254391 := bstep (se 1 (by rfl) ⟨1690793, by rfl⟩ : syracuseStep 2254391 = 3381587) B3381587
theorem B5433587 : Blo 443779 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B1501523 : Blo 443779 1501523 := bstep (se 1 (by rfl) ⟨1126142, by rfl⟩ : syracuseStep 1501523 = 2252285) B2252285
theorem B2550203 : Blo 443779 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B1239707 : Blo 443779 1239707 := bstep (se 1 (by rfl) ⟨929780, by rfl⟩ : syracuseStep 1239707 = 1859561) B1859561
theorem B1502279 : Blo 443779 1502279 := bstep (se 1 (by rfl) ⟨1126709, by rfl⟩ : syracuseStep 1502279 = 2253419) B2253419
theorem B13200653 : Blo 443779 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B749803 : Blo 443779 749803 := bstep (se 1 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 749803 = 1124705) B1124705
theorem B717097 : Blo 443779 717097 := bstep (se 2 (by rfl) ⟨268911, by rfl⟩ : syracuseStep 717097 = 537823) B537823
theorem B848731 : Blo 443779 848731 := bstep (se 1 (by rfl) ⟨636548, by rfl⟩ : syracuseStep 848731 = 1273097) B1273097
theorem B1012961 : Blo 443779 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B1897769 : Blo 443779 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B1209887 : Blo 443779 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B751241 : Blo 443779 751241 := bstep (se 2 (by rfl) ⟨281715, by rfl⟩ : syracuseStep 751241 = 563431) B563431
theorem B2258603 : Blo 443779 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B1505195 : Blo 443779 1505195 := bstep (se 1 (by rfl) ⟨1128896, by rfl⟩ : syracuseStep 1505195 = 2257793) B2257793
theorem B3045671 : Blo 443779 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B4619105 : Blo 443779 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B2882587 : Blo 443779 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B3800459 : Blo 443779 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B1506923 : Blo 443779 1506923 := bstep (se 1 (by rfl) ⟨1130192, by rfl⟩ : syracuseStep 1506923 = 2260385) B2260385
theorem B1508435 : Blo 443779 1508435 := bstep (se 1 (by rfl) ⟨1131326, by rfl⟩ : syracuseStep 1508435 = 2262653) B2262653
theorem B1805147 : Blo 443779 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B9146513 : Blo 443779 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B1905545 : Blo 443779 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B4166585 : Blo 443779 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B955327 : Blo 443779 955327 := bstep (se 1 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 955327 = 1432991) B1432991
theorem B3806473 : Blo 443779 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B1611035 : Blo 443779 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B13768055 : Blo 443779 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B956129 : Blo 443779 956129 := bstep (se 2 (by rfl) ⟨358548, by rfl⟩ : syracuseStep 956129 = 717097) B717097
theorem B6101183 : Blo 443779 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B826471 : Blo 443779 826471 := bstep (se 1 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 826471 = 1239707) B1239707
theorem B19210607 : Blo 443779 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B500827 : Blo 443779 500827 := bstep (se 1 (by rfl) ⟨375620, by rfl⟩ : syracuseStep 500827 = 751241) B751241
theorem B3843449 : Blo 443779 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B6891419 : Blo 443779 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B665783 : Blo 443779 665783 := bstep (se 1 (by rfl) ⟨499337, by rfl⟩ : syracuseStep 665783 = 998675) B998675
theorem B665807 : Blo 443779 665807 := bstep (se 1 (by rfl) ⟨499355, by rfl⟩ : syracuseStep 665807 = 998711) B998711
theorem B665831 : Blo 443779 665831 := bstep (se 1 (by rfl) ⟨499373, by rfl⟩ : syracuseStep 665831 = 998747) B998747
theorem B665855 : Blo 443779 665855 := bstep (se 1 (by rfl) ⟨499391, by rfl⟩ : syracuseStep 665855 = 998783) B998783
theorem B2533639 : Blo 443779 2533639 := bstep (se 1 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 2533639 = 3800459) B3800459
theorem B502555 : Blo 443779 502555 := bstep (se 1 (by rfl) ⟨376916, by rfl⟩ : syracuseStep 502555 = 753833) B753833
theorem B46181171 : Blo 443779 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B1125353 : Blo 443779 1125353 := bstep (se 2 (by rfl) ⟨422007, by rfl⟩ : syracuseStep 1125353 = 844015) B844015
theorem B666617 : Blo 443779 666617 := bstep (se 2 (by rfl) ⟨249981, by rfl⟩ : syracuseStep 666617 = 499963) B499963
theorem B666791 : Blo 443779 666791 := bstep (se 1 (by rfl) ⟨500093, by rfl⟩ : syracuseStep 666791 = 1000187) B1000187
theorem B666815 : Blo 443779 666815 := bstep (se 1 (by rfl) ⟨500111, by rfl⟩ : syracuseStep 666815 = 1000223) B1000223
theorem B1125839 : Blo 443779 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B503455 : Blo 443779 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B5713811 : Blo 443779 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B667559 : Blo 443779 667559 := bstep (se 1 (by rfl) ⟨500669, by rfl⟩ : syracuseStep 667559 = 1001339) B1001339
theorem B23179193 : Blo 443779 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B1126619 : Blo 443779 1126619 := bstep (se 1 (by rfl) ⟨844964, by rfl⟩ : syracuseStep 1126619 = 1689929) B1689929
theorem B667943 : Blo 443779 667943 := bstep (se 1 (by rfl) ⟨500957, by rfl⟩ : syracuseStep 667943 = 1001915) B1001915
theorem B1290653 : Blo 443779 1290653 := bstep (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) B483995
theorem B668207 : Blo 443779 668207 := bstep (se 1 (by rfl) ⟨501155, by rfl⟩ : syracuseStep 668207 = 1002311) B1002311
theorem B668315 : Blo 443779 668315 := bstep (se 1 (by rfl) ⟨501236, by rfl⟩ : syracuseStep 668315 = 1002473) B1002473
theorem B2142911 : Blo 443779 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B46445561 : Blo 443779 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B2537081 : Blo 443779 2537081 := bstep (se 2 (by rfl) ⟨951405, by rfl⟩ : syracuseStep 2537081 = 1902811) B1902811
theorem B964327 : Blo 443779 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B3815495 : Blo 443779 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B5060717 : Blo 443779 5060717 := bstep (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) B1897769
theorem B670187 : Blo 443779 670187 := bstep (se 1 (by rfl) ⟨502640, by rfl⟩ : syracuseStep 670187 = 1005281) B1005281
theorem B2866337 : Blo 443779 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B671135 : Blo 443779 671135 := bstep (se 1 (by rfl) ⟨503351, by rfl⟩ : syracuseStep 671135 = 1006703) B1006703
theorem B998891 : Blo 443779 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B12828395 : Blo 443779 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B1130395 : Blo 443779 1130395 := bstep (se 1 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 1130395 = 1695593) B1695593
theorem B999737 : Blo 443779 999737 := bstep (se 2 (by rfl) ⟨374901, by rfl⟩ : syracuseStep 999737 = 749803) B749803
theorem B1130831 : Blo 443779 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B1688303 : Blo 443779 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B1131641 : Blo 443779 1131641 := bstep (se 2 (by rfl) ⟨424365, by rfl⟩ : syracuseStep 1131641 = 848731) B848731
theorem B2278583 : Blo 443779 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B3622391 : Blo 443779 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B1001015 : Blo 443779 1001015 := bstep (se 1 (by rfl) ⟨750761, by rfl⟩ : syracuseStep 1001015 = 1501523) B1501523
theorem B80299781 : Blo 443779 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B444251 : Blo 443779 444251 := bstep (se 1 (by rfl) ⟨333188, by rfl⟩ : syracuseStep 444251 = 666377) B666377
theorem B1001519 : Blo 443779 1001519 := bstep (se 1 (by rfl) ⟨751139, by rfl⟩ : syracuseStep 1001519 = 1502279) B1502279
theorem B444519 : Blo 443779 444519 := bstep (se 1 (by rfl) ⟨333389, by rfl⟩ : syracuseStep 444519 = 666779) B666779
theorem B8800435 : Blo 443779 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B445743 : Blo 443779 445743 := bstep (se 1 (by rfl) ⟨334307, by rfl⟩ : syracuseStep 445743 = 668615) B668615
theorem B675307 : Blo 443779 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B806591 : Blo 443779 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B446239 : Blo 443779 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B1003463 : Blo 443779 1003463 := bstep (se 1 (by rfl) ⟨752597, by rfl⟩ : syracuseStep 1003463 = 1505195) B1505195
theorem B446879 : Blo 443779 446879 := bstep (se 1 (by rfl) ⟨335159, by rfl⟩ : syracuseStep 446879 = 670319) B670319
theorem B446975 : Blo 443779 446975 := bstep (se 1 (by rfl) ⟨335231, by rfl⟩ : syracuseStep 446975 = 670463) B670463
theorem B12210689 : Blo 443779 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1004615 : Blo 443779 1004615 := bstep (se 1 (by rfl) ⟨753461, by rfl⟩ : syracuseStep 1004615 = 1506923) B1506923
theorem B447719 : Blo 443779 447719 := bstep (se 1 (by rfl) ⟨335789, by rfl⟩ : syracuseStep 447719 = 671579) B671579
theorem B447743 : Blo 443779 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B32658713 : Blo 443779 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B1004921 : Blo 443779 1004921 := bstep (se 2 (by rfl) ⟨376845, by rfl⟩ : syracuseStep 1004921 = 753691) B753691
theorem B907375 : Blo 443779 907375 := bstep (se 1 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 907375 = 1361063) B1361063
theorem B1431863 : Blo 443779 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B1006235 : Blo 443779 1006235 := bstep (se 1 (by rfl) ⟨754676, by rfl⟩ : syracuseStep 1006235 = 1509353) B1509353
theorem B1006343 : Blo 443779 1006343 := bstep (se 1 (by rfl) ⟨754757, by rfl⟩ : syracuseStep 1006343 = 1509515) B1509515
theorem B1072379 : Blo 443779 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B679223 : Blo 443779 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B1007135 : Blo 443779 1007135 := bstep (se 1 (by rfl) ⟨755351, by rfl⟩ : syracuseStep 1007135 = 1510703) B1510703
theorem B1007387 : Blo 443779 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B3531005 : Blo 443779 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B19292417 : Blo 443779 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B1270055 : Blo 443779 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B713215 : Blo 443779 713215 := bstep (se 1 (by rfl) ⟨534911, by rfl⟩ : syracuseStep 713215 = 1069823) B1069823
theorem B3203873 : Blo 443779 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B2253905 : Blo 443779 2253905 := bstep (se 2 (by rfl) ⟨845214, by rfl⟩ : syracuseStep 2253905 = 1690429) B1690429
theorem B8545499 : Blo 443779 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B2254715 : Blo 443779 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B4385825 : Blo 443779 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B5434559 : Blo 443779 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1895719 : Blo 443779 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B716239 : Blo 443779 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B6876647 : Blo 443779 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B1502927 : Blo 443779 1502927 := bstep (se 1 (by rfl) ⟨1127195, by rfl⟩ : syracuseStep 1502927 = 2254391) B2254391
theorem B1700135 : Blo 443779 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B7238423 : Blo 443779 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B751099 : Blo 443779 751099 := bstep (se 1 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 751099 = 1126649) B1126649
theorem B10974811 : Blo 443779 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B5076755 : Blo 443779 5076755 := bstep (se 1 (by rfl) ⟨3807566, by rfl⟩ : syracuseStep 5076755 = 7615133) B7615133
theorem B3372839 : Blo 443779 3372839 := bstep (se 1 (by rfl) ⟨2529629, by rfl⟩ : syracuseStep 3372839 = 5059259) B5059259
theorem B2292137 : Blo 443779 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B1505735 : Blo 443779 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B2849579 : Blo 443779 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B2030447 : Blo 443779 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B3079403 : Blo 443779 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B753023 : Blo 443779 753023 := bstep (se 1 (by rfl) ⟨564767, by rfl⟩ : syracuseStep 753023 = 1129535) B1129535
theorem B753887 : Blo 443779 753887 := bstep (se 1 (by rfl) ⟨565415, by rfl⟩ : syracuseStep 753887 = 1130831) B1130831
theorem B950953 : Blo 443779 950953 := bstep (se 2 (by rfl) ⟨356607, by rfl⟩ : syracuseStep 950953 = 713215) B713215
theorem B754427 : Blo 443779 754427 := bstep (se 1 (by rfl) ⟨565820, by rfl⟩ : syracuseStep 754427 = 1131641) B1131641
theorem B19302461 : Blo 443779 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B6097675 : Blo 443779 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B11733913 : Blo 443779 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B3378185 : Blo 443779 3378185 := bstep (se 2 (by rfl) ⟨1266819, by rfl⟩ : syracuseStep 3378185 = 2533639) B2533639
theorem B9178703 : Blo 443779 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B4067455 : Blo 443779 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B954575 : Blo 443779 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B2527625 : Blo 443779 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B954985 : Blo 443779 954985 := bstep (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) B716239
theorem B2135915 : Blo 443779 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B2562299 : Blo 443779 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B4594279 : Blo 443779 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B2923883 : Blo 443779 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B1285769 : Blo 443779 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B3809207 : Blo 443779 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B860435 : Blo 443779 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B1811261 : Blo 443779 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B3384503 : Blo 443779 3384503 := bstep (se 1 (by rfl) ⟨2538377, by rfl⟩ : syracuseStep 3384503 = 5076755) B5076755
theorem B1353631 : Blo 443779 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B1910891 : Blo 443779 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B502015 : Blo 443779 502015 := bstep (se 1 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 502015 = 753023) B753023
theorem B665927 : Blo 443779 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B666491 : Blo 443779 666491 := bstep (se 1 (by rfl) ⟨499868, by rfl⟩ : syracuseStep 666491 = 999737) B999737
theorem B1125535 : Blo 443779 1125535 := bstep (se 1 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 1125535 = 1688303) B1688303
theorem B1519055 : Blo 443779 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B667343 : Blo 443779 667343 := bstep (se 1 (by rfl) ⟨500507, by rfl⟩ : syracuseStep 667343 = 1001015) B1001015
theorem B667679 : Blo 443779 667679 := bstep (se 1 (by rfl) ⟨500759, by rfl⟩ : syracuseStep 667679 = 1001519) B1001519
theorem B667769 : Blo 443779 667769 := bstep (se 2 (by rfl) ⟨250413, by rfl⟩ : syracuseStep 667769 = 500827) B500827
theorem B537727 : Blo 443779 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B668975 : Blo 443779 668975 := bstep (se 1 (by rfl) ⟨501731, by rfl⟩ : syracuseStep 668975 = 1003463) B1003463
theorem B8140459 : Blo 443779 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B669743 : Blo 443779 669743 := bstep (se 1 (by rfl) ⟨502307, by rfl⟩ : syracuseStep 669743 = 1004615) B1004615
theorem B21772475 : Blo 443779 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B669947 : Blo 443779 669947 := bstep (se 1 (by rfl) ⟨502460, by rfl⟩ : syracuseStep 669947 = 1004921) B1004921
theorem B670073 : Blo 443779 670073 := bstep (se 2 (by rfl) ⟨251277, by rfl⟩ : syracuseStep 670073 = 502555) B502555
theorem B670823 : Blo 443779 670823 := bstep (se 1 (by rfl) ⟨503117, by rfl⟩ : syracuseStep 670823 = 1006235) B1006235
theorem B670895 : Blo 443779 670895 := bstep (se 1 (by rfl) ⟨503171, by rfl⟩ : syracuseStep 670895 = 1006343) B1006343
theorem B900409 : Blo 443779 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B671273 : Blo 443779 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B671423 : Blo 443779 671423 := bstep (se 1 (by rfl) ⟨503567, by rfl⟩ : syracuseStep 671423 = 1007135) B1007135
theorem B671591 : Blo 443779 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B12861611 : Blo 443779 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B443855 : Blo 443779 443855 := bstep (se 1 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 443855 = 665783) B665783
theorem B443871 : Blo 443779 443871 := bstep (se 1 (by rfl) ⟨332903, by rfl⟩ : syracuseStep 443871 = 665807) B665807
theorem B443887 : Blo 443779 443887 := bstep (se 1 (by rfl) ⟨332915, by rfl⟩ : syracuseStep 443887 = 665831) B665831
theorem B443903 : Blo 443779 443903 := bstep (se 1 (by rfl) ⟨332927, by rfl⟩ : syracuseStep 443903 = 665855) B665855
theorem B30787447 : Blo 443779 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B1001465 : Blo 443779 1001465 := bstep (se 2 (by rfl) ⟨375549, by rfl⟩ : syracuseStep 1001465 = 751099) B751099
theorem B444411 : Blo 443779 444411 := bstep (se 1 (by rfl) ⟨333308, by rfl⟩ : syracuseStep 444411 = 666617) B666617
theorem B444527 : Blo 443779 444527 := bstep (se 1 (by rfl) ⟨333395, by rfl⟩ : syracuseStep 444527 = 666791) B666791
theorem B14633081 : Blo 443779 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B444543 : Blo 443779 444543 := bstep (se 1 (by rfl) ⟨333407, by rfl⟩ : syracuseStep 444543 = 666815) B666815
theorem B3623039 : Blo 443779 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B1001951 : Blo 443779 1001951 := bstep (se 1 (by rfl) ⟨751463, by rfl⟩ : syracuseStep 1001951 = 1502927) B1502927
theorem B445039 : Blo 443779 445039 := bstep (se 1 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 445039 = 667559) B667559
theorem B15452795 : Blo 443779 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B445295 : Blo 443779 445295 := bstep (se 1 (by rfl) ⟨333971, by rfl⟩ : syracuseStep 445295 = 667943) B667943
theorem B1133423 : Blo 443779 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B445471 : Blo 443779 445471 := bstep (se 1 (by rfl) ⟨334103, by rfl⟩ : syracuseStep 445471 = 668207) B668207
theorem B445543 : Blo 443779 445543 := bstep (se 1 (by rfl) ⟨334157, by rfl⟩ : syracuseStep 445543 = 668315) B668315
theorem B1428607 : Blo 443779 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B1691387 : Blo 443779 1691387 := bstep (se 1 (by rfl) ⟨1268540, by rfl⟩ : syracuseStep 1691387 = 2537081) B2537081
theorem B2248559 : Blo 443779 2248559 := bstep (se 1 (by rfl) ⟨1686419, by rfl⟩ : syracuseStep 2248559 = 3372839) B3372839
theorem B2543663 : Blo 443779 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B1101961 : Blo 443779 1101961 := bstep (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) B826471
theorem B1528091 : Blo 443779 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B1003823 : Blo 443779 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B446791 : Blo 443779 446791 := bstep (se 1 (by rfl) ⟨335093, by rfl⟩ : syracuseStep 446791 = 670187) B670187
theorem B2052935 : Blo 443779 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B447423 : Blo 443779 447423 := bstep (se 1 (by rfl) ⟨335567, by rfl⟩ : syracuseStep 447423 = 671135) B671135
theorem B1005623 : Blo 443779 1005623 := bstep (se 1 (by rfl) ⟨754217, by rfl⟩ : syracuseStep 1005623 = 1508435) B1508435
theorem B2414927 : Blo 443779 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B53533187 : Blo 443779 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B1203431 : Blo 443779 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1270363 : Blo 443779 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B2777723 : Blo 443779 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1074023 : Blo 443779 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B2549677 : Blo 443779 2549677 := bstep (se 3 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 2549677 = 956129) B956129
theorem B714919 : Blo 443779 714919 := bstep (se 1 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 714919 = 1072379) B1072379
theorem B2354003 : Blo 443779 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B846703 : Blo 443779 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B12807071 : Blo 443779 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B1502603 : Blo 443779 1502603 := bstep (se 1 (by rfl) ⟨1126952, by rfl⟩ : syracuseStep 1502603 = 2253905) B2253905
theorem B5696999 : Blo 443779 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B1503143 : Blo 443779 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B1273769 : Blo 443779 1273769 := bstep (se 2 (by rfl) ⟨477663, by rfl⟩ : syracuseStep 1273769 = 955327) B955327
theorem B5075297 : Blo 443779 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B750235 : Blo 443779 750235 := bstep (se 1 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 750235 = 1125353) B1125353
theorem B750559 : Blo 443779 750559 := bstep (se 1 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 750559 = 1125839) B1125839
theorem B4584431 : Blo 443779 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B751079 : Blo 443779 751079 := bstep (se 1 (by rfl) ⟨563309, by rfl⟩ : syracuseStep 751079 = 1126619) B1126619
theorem B1209833 : Blo 443779 1209833 := bstep (se 2 (by rfl) ⟨453687, by rfl⟩ : syracuseStep 1209833 = 907375) B907375
theorem B30963707 : Blo 443779 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B3373811 : Blo 443779 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B1899719 : Blo 443779 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B8552263 : Blo 443779 8552263 := bstep (se 1 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 8552263 = 12828395) B12828395
theorem B1507193 : Blo 443779 1507193 := bstep (se 2 (by rfl) ⟨565197, by rfl⟩ : syracuseStep 1507193 = 1130395) B1130395
theorem B755615 : Blo 443779 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B1804841 : Blo 443779 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B1018727 : Blo 443779 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B953225 : Blo 443779 953225 := bstep (se 2 (by rfl) ⟨357459, by rfl⟩ : syracuseStep 953225 = 714919) B714919
theorem B8130233 : Blo 443779 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B1708199 : Blo 443779 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B1904809 : Blo 443779 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B1609951 : Blo 443779 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B35688791 : Blo 443779 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B857179 : Blo 443779 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B10853945 : Blo 443779 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B3383531 : Blo 443779 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B3056287 : Blo 443779 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B25109365 : Blo 443779 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B500719 : Blo 443779 500719 := bstep (se 1 (by rfl) ⟨375539, by rfl⟩ : syracuseStep 500719 = 751079) B751079
theorem B502591 : Blo 443779 502591 := bstep (se 1 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 502591 = 753887) B753887
theorem B502951 : Blo 443779 502951 := bstep (se 1 (by rfl) ⟨377213, by rfl⟩ : syracuseStep 502951 = 754427) B754427
theorem B667643 : Blo 443779 667643 := bstep (se 1 (by rfl) ⟨500732, by rfl⟩ : syracuseStep 667643 = 1001465) B1001465
theorem B667967 : Blo 443779 667967 := bstep (se 1 (by rfl) ⟨500975, by rfl⟩ : syracuseStep 667967 = 1001951) B1001951
theorem B10301863 : Blo 443779 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B1127591 : Blo 443779 1127591 := bstep (se 1 (by rfl) ⟨845693, by rfl⟩ : syracuseStep 1127591 = 1691387) B1691387
theorem B636383 : Blo 443779 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B669215 : Blo 443779 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B1685083 : Blo 443779 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B669353 : Blo 443779 669353 := bstep (se 2 (by rfl) ⟨251007, by rfl⟩ : syracuseStep 669353 = 502015) B502015
theorem B1128937 : Blo 443779 1128937 := bstep (se 2 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 1128937 = 846703) B846703
theorem B1423943 : Blo 443779 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B670415 : Blo 443779 670415 := bstep (se 1 (by rfl) ⟨502811, by rfl⟩ : syracuseStep 670415 = 1005623) B1005623
theorem B1949255 : Blo 443779 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B2539471 : Blo 443779 2539471 := bstep (se 1 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 2539471 = 3809207) B3809207
theorem B5423273 : Blo 443779 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B573623 : Blo 443779 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B5095709 : Blo 443779 5095709 := bstep (se 3 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 5095709 = 1910891) B1910891
theorem B1851815 : Blo 443779 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B1000313 : Blo 443779 1000313 := bstep (se 2 (by rfl) ⟨375117, by rfl⟩ : syracuseStep 1000313 = 750235) B750235
theorem B1000745 : Blo 443779 1000745 := bstep (se 2 (by rfl) ⟨375279, by rfl⟩ : syracuseStep 1000745 = 750559) B750559
theorem B443951 : Blo 443779 443951 := bstep (se 1 (by rfl) ⟨332963, by rfl⟩ : syracuseStep 443951 = 665927) B665927
theorem B444327 : Blo 443779 444327 := bstep (se 1 (by rfl) ⟨333245, by rfl⟩ : syracuseStep 444327 = 666491) B666491
theorem B8538047 : Blo 443779 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B1001735 : Blo 443779 1001735 := bstep (se 1 (by rfl) ⟨751301, by rfl⟩ : syracuseStep 1001735 = 1502603) B1502603
theorem B444895 : Blo 443779 444895 := bstep (se 1 (by rfl) ⟨333671, by rfl⟩ : syracuseStep 444895 = 667343) B667343
theorem B1002095 : Blo 443779 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B445119 : Blo 443779 445119 := bstep (se 1 (by rfl) ⟨333839, by rfl⟩ : syracuseStep 445119 = 667679) B667679
theorem B445179 : Blo 443779 445179 := bstep (se 1 (by rfl) ⟨333884, by rfl⟩ : syracuseStep 445179 = 667769) B667769
theorem B445983 : Blo 443779 445983 := bstep (se 1 (by rfl) ⟨334487, by rfl⟩ : syracuseStep 445983 = 668975) B668975
theorem B806555 : Blo 443779 806555 := bstep (se 1 (by rfl) ⟨604916, by rfl⟩ : syracuseStep 806555 = 1209833) B1209833
theorem B446495 : Blo 443779 446495 := bstep (se 1 (by rfl) ⟨334871, by rfl⟩ : syracuseStep 446495 = 669743) B669743
theorem B446631 : Blo 443779 446631 := bstep (se 1 (by rfl) ⟨334973, by rfl⟩ : syracuseStep 446631 = 669947) B669947
theorem B446715 : Blo 443779 446715 := bstep (se 1 (by rfl) ⟨335036, by rfl⟩ : syracuseStep 446715 = 670073) B670073
theorem B1200545 : Blo 443779 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B2249207 : Blo 443779 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B447215 : Blo 443779 447215 := bstep (se 1 (by rfl) ⟨335411, by rfl⟩ : syracuseStep 447215 = 670823) B670823
theorem B447263 : Blo 443779 447263 := bstep (se 1 (by rfl) ⟨335447, by rfl⟩ : syracuseStep 447263 = 670895) B670895
theorem B1266479 : Blo 443779 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B447515 : Blo 443779 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B447615 : Blo 443779 447615 := bstep (se 1 (by rfl) ⟨335711, by rfl⟩ : syracuseStep 447615 = 671423) B671423
theorem B447727 : Blo 443779 447727 := bstep (se 1 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 447727 = 671591) B671591
theorem B1004795 : Blo 443779 1004795 := bstep (se 1 (by rfl) ⟨753596, by rfl⟩ : syracuseStep 1004795 = 1507193) B1507193
theorem B8574407 : Blo 443779 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B1693817 : Blo 443779 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B1267937 : Blo 443779 1267937 := bstep (se 2 (by rfl) ⟨475476, by rfl⟩ : syracuseStep 1267937 = 950953) B950953
theorem B12868307 : Blo 443779 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B9755387 : Blo 443779 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B2415359 : Blo 443779 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B2252123 : Blo 443779 2252123 := bstep (se 1 (by rfl) ⟨1689092, by rfl⟩ : syracuseStep 2252123 = 3378185) B3378185
theorem B6119135 : Blo 443779 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B41049929 : Blo 443779 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B3399569 : Blo 443779 3399569 := bstep (se 2 (by rfl) ⟨1274838, by rfl⟩ : syracuseStep 3399569 = 2549677) B2549677
theorem B1499039 : Blo 443779 1499039 := bstep (se 1 (by rfl) ⟨1124279, by rfl⟩ : syracuseStep 1499039 = 2248559) B2248559
theorem B1695775 : Blo 443779 1695775 := bstep (se 1 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 1695775 = 2543663) B2543663
theorem B1368623 : Blo 443779 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B1500713 : Blo 443779 1500713 := bstep (se 2 (by rfl) ⟨562767, by rfl⟩ : syracuseStep 1500713 = 1125535) B1125535
theorem B62580869 : Blo 443779 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B1469281 : Blo 443779 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B1207507 : Blo 443779 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B716015 : Blo 443779 716015 := bstep (se 1 (by rfl) ⟨537011, by rfl⟩ : syracuseStep 716015 = 1074023) B1074023
theorem B2256335 : Blo 443779 2256335 := bstep (se 1 (by rfl) ⟨1692251, by rfl⟩ : syracuseStep 2256335 = 3384503) B3384503
theorem B1273313 : Blo 443779 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B716969 : Blo 443779 716969 := bstep (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) B537727
theorem B1012703 : Blo 443779 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B3797999 : Blo 443779 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B849179 : Blo 443779 849179 := bstep (se 1 (by rfl) ⟨636884, by rfl⟩ : syracuseStep 849179 = 1273769) B1273769
theorem B3209149 : Blo 443779 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B6125705 : Blo 443779 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B20642471 : Blo 443779 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B14514983 : Blo 443779 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B11403017 : Blo 443779 11403017 := bstep (se 2 (by rfl) ⟨4276131, by rfl⟩ : syracuseStep 11403017 = 8552263) B8552263
theorem B2261033 : Blo 443779 2261033 := bstep (se 2 (by rfl) ⟨847887, by rfl⟩ : syracuseStep 2261033 = 1695775) B1695775
theorem B23792527 : Blo 443779 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B1610009 : Blo 443779 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B27366619 : Blo 443779 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B2266379 : Blo 443779 2266379 := bstep (se 1 (by rfl) ⟨1699784, by rfl⟩ : syracuseStep 2266379 = 3399569) B3399569
theorem B13735817 : Blo 443779 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B41720579 : Blo 443779 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B2531999 : Blo 443779 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B566119 : Blo 443779 566119 := bstep (se 1 (by rfl) ⟨424589, by rfl⟩ : syracuseStep 566119 = 849179) B849179
theorem B9676655 : Blo 443779 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B3385961 : Blo 443779 3385961 := bstep (se 2 (by rfl) ⟨1269735, by rfl⟩ : syracuseStep 3385961 = 2539471) B2539471
theorem B3615515 : Blo 443779 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B1911917 : Blo 443779 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B666875 : Blo 443779 666875 := bstep (se 1 (by rfl) ⟨500156, by rfl⟩ : syracuseStep 666875 = 1000313) B1000313
theorem B667163 : Blo 443779 667163 := bstep (se 1 (by rfl) ⟨500372, by rfl⟩ : syracuseStep 667163 = 1000745) B1000745
theorem B4075049 : Blo 443779 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B503743 : Blo 443779 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B667625 : Blo 443779 667625 := bstep (se 2 (by rfl) ⟨250359, by rfl⟩ : syracuseStep 667625 = 500719) B500719
theorem B667823 : Blo 443779 667823 := bstep (se 1 (by rfl) ⟨500867, by rfl⟩ : syracuseStep 667823 = 1001735) B1001735
theorem B668063 : Blo 443779 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B635483 : Blo 443779 635483 := bstep (se 1 (by rfl) ⟨476612, by rfl⟩ : syracuseStep 635483 = 953225) B953225
theorem B2700541 : Blo 443779 2700541 := bstep (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) B1012703
theorem B800363 : Blo 443779 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B669863 : Blo 443779 669863 := bstep (se 1 (by rfl) ⟨502397, by rfl⟩ : syracuseStep 669863 = 1004795) B1004795
theorem B5716271 : Blo 443779 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B670121 : Blo 443779 670121 := bstep (se 2 (by rfl) ⟨251295, by rfl⟩ : syracuseStep 670121 = 502591) B502591
theorem B1129211 : Blo 443779 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B670601 : Blo 443779 670601 := bstep (se 2 (by rfl) ⟨251475, by rfl⟩ : syracuseStep 670601 = 502951) B502951
theorem B6503591 : Blo 443779 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B4079423 : Blo 443779 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B999359 : Blo 443779 999359 := bstep (se 1 (by rfl) ⟨749519, by rfl⟩ : syracuseStep 999359 = 1499039) B1499039
theorem B2539745 : Blo 443779 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B2146601 : Blo 443779 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B1000475 : Blo 443779 1000475 := bstep (se 1 (by rfl) ⟨750356, by rfl⟩ : syracuseStep 1000475 = 1500713) B1500713
theorem B6440957 : Blo 443779 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B2246777 : Blo 443779 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B477343 : Blo 443779 477343 := bstep (se 1 (by rfl) ⟨358007, by rfl⟩ : syracuseStep 477343 = 716015) B716015
theorem B4278865 : Blo 443779 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B445095 : Blo 443779 445095 := bstep (se 1 (by rfl) ⟨333821, by rfl⟩ : syracuseStep 445095 = 667643) B667643
theorem B445311 : Blo 443779 445311 := bstep (se 1 (by rfl) ⟨333983, by rfl⟩ : syracuseStep 445311 = 667967) B667967
theorem B446143 : Blo 443779 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B446235 : Blo 443779 446235 := bstep (se 1 (by rfl) ⟨334676, by rfl⟩ : syracuseStep 446235 = 669353) B669353
theorem B4083803 : Blo 443779 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B2150813 : Blo 443779 2150813 := bstep (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) B806555
theorem B446943 : Blo 443779 446943 := bstep (se 1 (by rfl) ⟨335207, by rfl⟩ : syracuseStep 446943 = 670415) B670415
theorem B21680621 : Blo 443779 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B1299503 : Blo 443779 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B3397139 : Blo 443779 3397139 := bstep (se 1 (by rfl) ⟨2547854, by rfl⟩ : syracuseStep 3397139 = 5095709) B5095709
theorem B1234543 : Blo 443779 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B33479153 : Blo 443779 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B5692031 : Blo 443779 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B1203227 : Blo 443779 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B679151 : Blo 443779 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B1138799 : Blo 443779 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B1499471 : Blo 443779 1499471 := bstep (se 1 (by rfl) ⟨1124603, by rfl⟩ : syracuseStep 1499471 = 2249207) B2249207
theorem B844319 : Blo 443779 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B1959041 : Blo 443779 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B1697021 : Blo 443779 1697021 := bstep (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) B636383
theorem B845291 : Blo 443779 845291 := bstep (se 1 (by rfl) ⟨633968, by rfl⟩ : syracuseStep 845291 = 1267937) B1267937
theorem B8578871 : Blo 443779 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B1501415 : Blo 443779 1501415 := bstep (se 1 (by rfl) ⟨1126061, by rfl⟩ : syracuseStep 1501415 = 2252123) B2252123
theorem B7235963 : Blo 443779 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B2255687 : Blo 443779 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B912415 : Blo 443779 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1142905 : Blo 443779 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B24474581 : Blo 443779 24474581 := bstep (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) B573623
theorem B1504223 : Blo 443779 1504223 := bstep (se 1 (by rfl) ⟨1128167, by rfl⟩ : syracuseStep 1504223 = 2256335) B2256335
theorem B848875 : Blo 443779 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B1505249 : Blo 443779 1505249 := bstep (se 2 (by rfl) ⟨564468, by rfl⟩ : syracuseStep 1505249 = 1128937) B1128937
theorem B751727 : Blo 443779 751727 := bstep (se 1 (by rfl) ⟨563795, by rfl⟩ : syracuseStep 751727 = 1127591) B1127591
theorem B949295 : Blo 443779 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B13761647 : Blo 443779 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B7602011 : Blo 443779 7602011 := bstep (se 1 (by rfl) ⟨5701508, by rfl⟩ : syracuseStep 7602011 = 11403017) B11403017
theorem B1507355 : Blo 443779 1507355 := bstep (se 1 (by rfl) ⟨1130516, by rfl⟩ : syracuseStep 1507355 = 2261033) B2261033
theorem B754825 : Blo 443779 754825 := bstep (se 2 (by rfl) ⟨283059, by rfl⟩ : syracuseStep 754825 = 566119) B566119
theorem B4293971 : Blo 443779 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B2722535 : Blo 443779 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B14453747 : Blo 443779 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B5705153 : Blo 443779 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B1510919 : Blo 443779 1510919 := bstep (se 1 (by rfl) ⟨1133189, by rfl⟩ : syracuseStep 1510919 = 2266379) B2266379
theorem B2264759 : Blo 443779 2264759 := bstep (se 1 (by rfl) ⟨1698569, by rfl⟩ : syracuseStep 2264759 = 3397139) B3397139
theorem B31723369 : Blo 443779 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B1216553 : Blo 443779 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B22319435 : Blo 443779 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B562879 : Blo 443779 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B563527 : Blo 443779 563527 := bstep (se 1 (by rfl) ⟨422645, by rfl⟩ : syracuseStep 563527 = 845291) B845291
theorem B4823975 : Blo 443779 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B1646057 : Blo 443779 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B17342909 : Blo 443779 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B1811069 : Blo 443779 1811069 := bstep (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) B679151
theorem B533575 : Blo 443779 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B501151 : Blo 443779 501151 := bstep (se 1 (by rfl) ⟨375863, by rfl⟩ : syracuseStep 501151 = 751727) B751727
theorem B3810847 : Blo 443779 3810847 := bstep (se 1 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 3810847 = 5716271) B5716271
theorem B632863 : Blo 443779 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B666239 : Blo 443779 666239 := bstep (se 1 (by rfl) ⟨499679, by rfl⟩ : syracuseStep 666239 = 999359) B999359
theorem B666983 : Blo 443779 666983 := bstep (se 1 (by rfl) ⟨500237, by rfl⟩ : syracuseStep 666983 = 1000475) B1000475
theorem B866335 : Blo 443779 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B9157211 : Blo 443779 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B802151 : Blo 443779 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B671657 : Blo 443779 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B1523873 : Blo 443779 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B999647 : Blo 443779 999647 := bstep (se 1 (by rfl) ⟨749735, by rfl⟩ : syracuseStep 999647 = 1499471) B1499471
theorem B1687999 : Blo 443779 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B1131347 : Blo 443779 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B5719247 : Blo 443779 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B1131833 : Blo 443779 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B1000943 : Blo 443779 1000943 := bstep (se 1 (by rfl) ⟨750707, by rfl⟩ : syracuseStep 1000943 = 1501415) B1501415
theorem B36488825 : Blo 443779 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B2410343 : Blo 443779 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B444583 : Blo 443779 444583 := bstep (se 1 (by rfl) ⟨333437, by rfl⟩ : syracuseStep 444583 = 666875) B666875
theorem B444775 : Blo 443779 444775 := bstep (se 1 (by rfl) ⟨333581, by rfl⟩ : syracuseStep 444775 = 667163) B667163
theorem B445083 : Blo 443779 445083 := bstep (se 1 (by rfl) ⟨333812, by rfl⟩ : syracuseStep 445083 = 667625) B667625
theorem B445215 : Blo 443779 445215 := bstep (se 1 (by rfl) ⟨333911, by rfl⟩ : syracuseStep 445215 = 667823) B667823
theorem B445375 : Blo 443779 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B1002815 : Blo 443779 1002815 := bstep (se 1 (by rfl) ⟨752111, by rfl⟩ : syracuseStep 1002815 = 1504223) B1504223
theorem B1003499 : Blo 443779 1003499 := bstep (se 1 (by rfl) ⟨752624, by rfl⟩ : syracuseStep 1003499 = 1505249) B1505249
theorem B446575 : Blo 443779 446575 := bstep (se 1 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 446575 = 669863) B669863
theorem B446747 : Blo 443779 446747 := bstep (se 1 (by rfl) ⟨335060, by rfl⟩ : syracuseStep 446747 = 670121) B670121
theorem B447067 : Blo 443779 447067 := bstep (se 1 (by rfl) ⟨335300, by rfl⟩ : syracuseStep 447067 = 670601) B670601
theorem B5068007 : Blo 443779 5068007 := bstep (se 1 (by rfl) ⟨3801005, by rfl⟩ : syracuseStep 5068007 = 7602011) B7602011
theorem B1693163 : Blo 443779 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B3036797 : Blo 443779 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B5724269 : Blo 443779 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B2545829 : Blo 443779 2545829 := bstep (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) B477343
theorem B1497851 : Blo 443779 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B1694621 : Blo 443779 1694621 := bstep (se 3 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 1694621 = 635483) B635483
theorem B1073339 : Blo 443779 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B1433875 : Blo 443779 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B3794687 : Blo 443779 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B27813719 : Blo 443779 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1306027 : Blo 443779 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B6451103 : Blo 443779 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B3600721 : Blo 443779 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B2257307 : Blo 443779 2257307 := bstep (se 1 (by rfl) ⟨1692980, by rfl⟩ : syracuseStep 2257307 = 3385961) B3385961
theorem B1503791 : Blo 443779 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B1274611 : Blo 443779 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B2716699 : Blo 443779 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B16316387 : Blo 443779 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B752807 : Blo 443779 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B9174431 : Blo 443779 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B2719615 : Blo 443779 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B1015915 : Blo 443779 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B3244141 : Blo 443779 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B3375269 : Blo 443779 3375269 := bstep (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) B632863
theorem B754231 : Blo 443779 754231 := bstep (se 1 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 754231 = 1131347) B1131347
theorem B754555 : Blo 443779 754555 := bstep (se 1 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 754555 = 1131833) B1131833
theorem B1606895 : Blo 443779 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B9635831 : Blo 443779 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B5081129 : Blo 443779 5081129 := bstep (se 2 (by rfl) ⟨1905423, by rfl⟩ : syracuseStep 5081129 = 3810847) B3810847
theorem B3803435 : Blo 443779 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1509839 : Blo 443779 1509839 := bstep (se 1 (by rfl) ⟨1132379, by rfl⟩ : syracuseStep 1509839 = 2264759) B2264759
theorem B14879623 : Blo 443779 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B3378671 : Blo 443779 3378671 := bstep (se 1 (by rfl) ⟨2534003, by rfl⟩ : syracuseStep 3378671 = 5068007) B5068007
theorem B3215983 : Blo 443779 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B2529791 : Blo 443779 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B676765205 : Blo 443779 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B1155113 : Blo 443779 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B6104807 : Blo 443779 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B501871 : Blo 443779 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B534767 : Blo 443779 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B666431 : Blo 443779 666431 := bstep (se 1 (by rfl) ⟨499823, by rfl⟩ : syracuseStep 666431 = 999647) B999647
theorem B1911833 : Blo 443779 1911833 := bstep (se 2 (by rfl) ⟨716937, by rfl⟩ : syracuseStep 1911833 = 1433875) B1433875
theorem B3812831 : Blo 443779 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B2862647 : Blo 443779 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B667295 : Blo 443779 667295 := bstep (se 1 (by rfl) ⟨500471, by rfl⟩ : syracuseStep 667295 = 1000943) B1000943
theorem B24325883 : Blo 443779 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B1815023 : Blo 443779 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B668201 : Blo 443779 668201 := bstep (se 2 (by rfl) ⟨250575, by rfl⟩ : syracuseStep 668201 = 501151) B501151
theorem B668543 : Blo 443779 668543 := bstep (se 1 (by rfl) ⟨501407, by rfl⟩ : syracuseStep 668543 = 1002815) B1002815
theorem B668999 : Blo 443779 668999 := bstep (se 1 (by rfl) ⟨501749, by rfl⟩ : syracuseStep 668999 = 1003499) B1003499
theorem B1128775 : Blo 443779 1128775 := bstep (se 1 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 1128775 = 1693163) B1693163
theorem B3816179 : Blo 443779 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B998567 : Blo 443779 998567 := bstep (se 1 (by rfl) ⟨748925, by rfl⟩ : syracuseStep 998567 = 1497851) B1497851
theorem B1129747 : Blo 443779 1129747 := bstep (se 1 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 1129747 = 1694621) B1694621
theorem B1097371 : Blo 443779 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B4800961 : Blo 443779 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B3622265 : Blo 443779 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B444159 : Blo 443779 444159 := bstep (se 1 (by rfl) ⟨333119, by rfl⟩ : syracuseStep 444159 = 666239) B666239
theorem B6965477 : Blo 443779 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B444655 : Blo 443779 444655 := bstep (se 1 (by rfl) ⟨333491, by rfl⟩ : syracuseStep 444655 = 666983) B666983
theorem B1002527 : Blo 443779 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B24465149 : Blo 443779 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B3626153 : Blo 443779 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B447771 : Blo 443779 447771 := bstep (se 1 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 447771 = 671657) B671657
theorem B1004903 : Blo 443779 1004903 := bstep (se 1 (by rfl) ⟨753677, by rfl⟩ : syracuseStep 1004903 = 1507355) B1507355
theorem B2250665 : Blo 443779 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B711433 : Blo 443779 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B1006433 : Blo 443779 1006433 := bstep (se 2 (by rfl) ⟨377412, by rfl⟩ : syracuseStep 1006433 = 754825) B754825
theorem B1007279 : Blo 443779 1007279 := bstep (se 1 (by rfl) ⟨755459, by rfl⟩ : syracuseStep 1007279 = 1510919) B1510919
theorem B2024531 : Blo 443779 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B1697219 : Blo 443779 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B715559 : Blo 443779 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B11561939 : Blo 443779 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B1207379 : Blo 443779 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B1699481 : Blo 443779 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B18542479 : Blo 443779 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B750505 : Blo 443779 750505 := bstep (se 2 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 750505 = 562879) B562879
theorem B1504871 : Blo 443779 1504871 := bstep (se 1 (by rfl) ⟨1128653, by rfl⟩ : syracuseStep 1504871 = 2257307) B2257307
theorem B751369 : Blo 443779 751369 := bstep (se 2 (by rfl) ⟨281763, by rfl⟩ : syracuseStep 751369 = 563527) B563527
theorem B10877591 : Blo 443779 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B17202941 : Blo 443779 17202941 := bstep (se 3 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 17202941 = 6451103) B6451103
theorem B4325521 : Blo 443779 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B6423887 : Blo 443779 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B1349687 : Blo 443779 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B4069871 : Blo 443779 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B7707959 : Blo 443779 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B1908431 : Blo 443779 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B7251727 : Blo 443779 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B665711 : Blo 443779 665711 := bstep (se 1 (by rfl) ⟨499283, by rfl⟩ : syracuseStep 665711 = 998567) B998567
theorem B1354553 : Blo 443779 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B6401281 : Blo 443779 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B3387419 : Blo 443779 3387419 := bstep (se 1 (by rfl) ⟨2540564, by rfl⟩ : syracuseStep 3387419 = 5081129) B5081129
theorem B2535623 : Blo 443779 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B668351 : Blo 443779 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B669161 : Blo 443779 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B669935 : Blo 443779 669935 := bstep (se 1 (by rfl) ⟨502451, by rfl⟩ : syracuseStep 669935 = 1004903) B1004903
theorem B19839497 : Blo 443779 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1686527 : Blo 443779 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B670955 : Blo 443779 670955 := bstep (se 1 (by rfl) ⟨503216, by rfl⟩ : syracuseStep 670955 = 1006433) B1006433
theorem B671519 : Blo 443779 671519 := bstep (se 1 (by rfl) ⟨503639, by rfl⟩ : syracuseStep 671519 = 1007279) B1007279
theorem B24723305 : Blo 443779 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B770075 : Blo 443779 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B1426045 : Blo 443779 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B1131479 : Blo 443779 1131479 := bstep (se 1 (by rfl) ⟨848609, by rfl⟩ : syracuseStep 1131479 = 1697219) B1697219
theorem B1000673 : Blo 443779 1000673 := bstep (se 2 (by rfl) ⟨375252, by rfl⟩ : syracuseStep 1000673 = 750505) B750505
theorem B444287 : Blo 443779 444287 := bstep (se 1 (by rfl) ⟨333215, by rfl⟩ : syracuseStep 444287 = 666431) B666431
theorem B804919 : Blo 443779 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B2541887 : Blo 443779 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B1001825 : Blo 443779 1001825 := bstep (se 2 (by rfl) ⟨375684, by rfl⟩ : syracuseStep 1001825 = 751369) B751369
theorem B1132987 : Blo 443779 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B444863 : Blo 443779 444863 := bstep (se 1 (by rfl) ⟨333647, by rfl⟩ : syracuseStep 444863 = 667295) B667295
theorem B445467 : Blo 443779 445467 := bstep (se 1 (by rfl) ⟨334100, by rfl⟩ : syracuseStep 445467 = 668201) B668201
theorem B445695 : Blo 443779 445695 := bstep (se 1 (by rfl) ⟨334271, by rfl⟩ : syracuseStep 445695 = 668543) B668543
theorem B5852645 : Blo 443779 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B445999 : Blo 443779 445999 := bstep (se 1 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 445999 = 668999) B668999
theorem B1003247 : Blo 443779 1003247 := bstep (se 1 (by rfl) ⟨752435, by rfl⟩ : syracuseStep 1003247 = 1504871) B1504871
theorem B2544119 : Blo 443779 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B2250179 : Blo 443779 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B1005641 : Blo 443779 1005641 := bstep (se 2 (by rfl) ⟨377115, by rfl⟩ : syracuseStep 1005641 = 754231) B754231
theorem B1071263 : Blo 443779 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B2414843 : Blo 443779 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1006073 : Blo 443779 1006073 := bstep (se 2 (by rfl) ⟨377277, by rfl⟩ : syracuseStep 1006073 = 754555) B754555
theorem B4643651 : Blo 443779 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B1006559 : Blo 443779 1006559 := bstep (se 1 (by rfl) ⟨754919, by rfl⟩ : syracuseStep 1006559 = 1509839) B1509839
theorem B2252447 : Blo 443779 2252447 := bstep (se 1 (by rfl) ⟨1689335, by rfl⟩ : syracuseStep 2252447 = 3378671) B3378671
theorem B16310099 : Blo 443779 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B2417435 : Blo 443779 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B1500443 : Blo 443779 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B3794309 : Blo 443779 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B451176803 : Blo 443779 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B4287977 : Blo 443779 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B1274555 : Blo 443779 1274555 := bstep (se 1 (by rfl) ⟨955916, by rfl⟩ : syracuseStep 1274555 = 1911833) B1911833
theorem B16217255 : Blo 443779 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B1210015 : Blo 443779 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B7632629 : Blo 443779 7632629 := bstep (se 5 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 7632629 = 715559) B715559
theorem B1505033 : Blo 443779 1505033 := bstep (se 2 (by rfl) ⟨564387, by rfl⟩ : syracuseStep 1505033 = 1128775) B1128775
theorem B1506329 : Blo 443779 1506329 := bstep (se 2 (by rfl) ⟨564873, by rfl⟩ : syracuseStep 1506329 = 1129747) B1129747
theorem B11468627 : Blo 443779 11468627 := bstep (se 1 (by rfl) ⟨8601470, by rfl⟩ : syracuseStep 11468627 = 17202941) B17202941
theorem B5767361 : Blo 443779 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B754319 : Blo 443779 754319 := bstep (se 1 (by rfl) ⟨565739, by rfl⟩ : syracuseStep 754319 = 1131479) B1131479
theorem B1901393 : Blo 443779 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B3901763 : Blo 443779 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B9668969 : Blo 443779 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B1510649 : Blo 443779 1510649 := bstep (se 2 (by rfl) ⟨566493, by rfl⟩ : syracuseStep 1510649 = 1132987) B1132987
theorem B1609895 : Blo 443779 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B2856701 : Blo 443779 2856701 := bstep (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) B1071263
theorem B1611623 : Blo 443779 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B2529539 : Blo 443779 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B300784535 : Blo 443779 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B1613353 : Blo 443779 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B2858651 : Blo 443779 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B5088419 : Blo 443779 5088419 := bstep (se 1 (by rfl) ⟨3816314, by rfl⟩ : syracuseStep 5088419 = 7632629) B7632629
theorem B1124351 : Blo 443779 1124351 := bstep (se 1 (by rfl) ⟨843263, by rfl⟩ : syracuseStep 1124351 = 1686527) B1686527
theorem B7645751 : Blo 443779 7645751 := bstep (se 1 (by rfl) ⟨5734313, by rfl⟩ : syracuseStep 7645751 = 11468627) B11468627
theorem B667115 : Blo 443779 667115 := bstep (se 1 (by rfl) ⟨500336, by rfl⟩ : syracuseStep 667115 = 1000673) B1000673
theorem B667883 : Blo 443779 667883 := bstep (se 1 (by rfl) ⟨500912, by rfl⟩ : syracuseStep 667883 = 1001825) B1001825
theorem B668831 : Blo 443779 668831 := bstep (se 1 (by rfl) ⟨501623, by rfl⟩ : syracuseStep 668831 = 1003247) B1003247
theorem B899791 : Blo 443779 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B670427 : Blo 443779 670427 := bstep (se 1 (by rfl) ⟨502820, by rfl⟩ : syracuseStep 670427 = 1005641) B1005641
theorem B670715 : Blo 443779 670715 := bstep (se 1 (by rfl) ⟨503036, by rfl⟩ : syracuseStep 670715 = 1006073) B1006073
theorem B8535041 : Blo 443779 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B3095767 : Blo 443779 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B671039 : Blo 443779 671039 := bstep (se 1 (by rfl) ⟨503279, by rfl⟩ : syracuseStep 671039 = 1006559) B1006559
theorem B1000295 : Blo 443779 1000295 := bstep (se 1 (by rfl) ⟨750221, by rfl⟩ : syracuseStep 1000295 = 1500443) B1500443
theorem B52905325 : Blo 443779 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B443807 : Blo 443779 443807 := bstep (se 1 (by rfl) ⟨332855, by rfl⟩ : syracuseStep 443807 = 665711) B665711
theorem B903035 : Blo 443779 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1690415 : Blo 443779 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B445567 : Blo 443779 445567 := bstep (se 1 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 445567 = 668351) B668351
theorem B446107 : Blo 443779 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B1003355 : Blo 443779 1003355 := bstep (se 1 (by rfl) ⟨752516, by rfl⟩ : syracuseStep 1003355 = 1505033) B1505033
theorem B446623 : Blo 443779 446623 := bstep (se 1 (by rfl) ⟨334967, by rfl⟩ : syracuseStep 446623 = 669935) B669935
theorem B1004219 : Blo 443779 1004219 := bstep (se 1 (by rfl) ⟨753164, by rfl⟩ : syracuseStep 1004219 = 1506329) B1506329
theorem B447303 : Blo 443779 447303 := bstep (se 1 (by rfl) ⟨335477, by rfl⟩ : syracuseStep 447303 = 670955) B670955
theorem B447679 : Blo 443779 447679 := bstep (se 1 (by rfl) ⟨335759, by rfl⟩ : syracuseStep 447679 = 671519) B671519
theorem B513383 : Blo 443779 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B4282591 : Blo 443779 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B1694591 : Blo 443779 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B1073225 : Blo 443779 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B1696079 : Blo 443779 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B1500119 : Blo 443779 1500119 := bstep (se 1 (by rfl) ⟨1125089, by rfl⟩ : syracuseStep 1500119 = 2250179) B2250179
theorem B2713247 : Blo 443779 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B5138639 : Blo 443779 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B1501631 : Blo 443779 1501631 := bstep (se 1 (by rfl) ⟨1126223, by rfl⟩ : syracuseStep 1501631 = 2252447) B2252447
theorem B1272287 : Blo 443779 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B10873399 : Blo 443779 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B2258279 : Blo 443779 2258279 := bstep (se 1 (by rfl) ⟨1693709, by rfl⟩ : syracuseStep 2258279 = 3387419) B3387419
theorem B849703 : Blo 443779 849703 := bstep (se 1 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 849703 = 1274555) B1274555
theorem B10811503 : Blo 443779 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B16482203 : Blo 443779 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B1904467 : Blo 443779 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B4297661 : Blo 443779 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B1905767 : Blo 443779 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B1808831 : Blo 443779 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B5710121 : Blo 443779 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B10988135 : Blo 443779 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B3844907 : Blo 443779 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B502879 : Blo 443779 502879 := bstep (se 1 (by rfl) ⟨377159, by rfl⟩ : syracuseStep 502879 = 754319) B754319
theorem B666863 : Blo 443779 666863 := bstep (se 1 (by rfl) ⟨500147, by rfl⟩ : syracuseStep 666863 = 1000295) B1000295
theorem B602023 : Blo 443779 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B2601175 : Blo 443779 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1126943 : Blo 443779 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B668903 : Blo 443779 668903 := bstep (se 1 (by rfl) ⟨501677, by rfl⟩ : syracuseStep 668903 = 1003355) B1003355
theorem B669479 : Blo 443779 669479 := bstep (se 1 (by rfl) ⟨502109, by rfl⟩ : syracuseStep 669479 = 1004219) B1004219
theorem B14497865 : Blo 443779 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B1686359 : Blo 443779 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B1129727 : Blo 443779 1129727 := bstep (se 1 (by rfl) ⟨847295, by rfl⟩ : syracuseStep 1129727 = 1694591) B1694591
theorem B200523023 : Blo 443779 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B1130719 : Blo 443779 1130719 := bstep (se 1 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 1130719 = 1696079) B1696079
theorem B1000079 : Blo 443779 1000079 := bstep (se 1 (by rfl) ⟨750059, by rfl⟩ : syracuseStep 1000079 = 1500119) B1500119
theorem B3392279 : Blo 443779 3392279 := bstep (se 1 (by rfl) ⟨2544209, by rfl⟩ : syracuseStep 3392279 = 5088419) B5088419
theorem B3392765 : Blo 443779 3392765 := bstep (se 3 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 3392765 = 1272287) B1272287
theorem B3425759 : Blo 443779 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B1001087 : Blo 443779 1001087 := bstep (se 1 (by rfl) ⟨750815, by rfl⟩ : syracuseStep 1001087 = 1501631) B1501631
theorem B5097167 : Blo 443779 5097167 := bstep (se 1 (by rfl) ⟨3822875, by rfl⟩ : syracuseStep 5097167 = 7645751) B7645751
theorem B444743 : Blo 443779 444743 := bstep (se 1 (by rfl) ⟨333557, by rfl⟩ : syracuseStep 444743 = 667115) B667115
theorem B1132937 : Blo 443779 1132937 := bstep (se 2 (by rfl) ⟨424851, by rfl⟩ : syracuseStep 1132937 = 849703) B849703
theorem B445255 : Blo 443779 445255 := bstep (se 1 (by rfl) ⟨333941, by rfl⟩ : syracuseStep 445255 = 667883) B667883
theorem B445887 : Blo 443779 445887 := bstep (se 1 (by rfl) ⟨334415, by rfl⟩ : syracuseStep 445887 = 668831) B668831
theorem B446951 : Blo 443779 446951 := bstep (se 1 (by rfl) ⟨335213, by rfl⟩ : syracuseStep 446951 = 670427) B670427
theorem B447143 : Blo 443779 447143 := bstep (se 1 (by rfl) ⟨335357, by rfl⟩ : syracuseStep 447143 = 670715) B670715
theorem B5690027 : Blo 443779 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B2151137 : Blo 443779 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B447359 : Blo 443779 447359 := bstep (se 1 (by rfl) ⟨335519, by rfl⟩ : syracuseStep 447359 = 671039) B671039
theorem B1267595 : Blo 443779 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B6445979 : Blo 443779 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B70540433 : Blo 443779 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1007099 : Blo 443779 1007099 := bstep (se 1 (by rfl) ⟨755324, by rfl⟩ : syracuseStep 1007099 = 1510649) B1510649
theorem B1073263 : Blo 443779 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B1369021 : Blo 443779 1369021 := bstep (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) B513383
theorem B19195541 : Blo 443779 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B715483 : Blo 443779 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B749567 : Blo 443779 749567 := bstep (se 1 (by rfl) ⟨562175, by rfl⟩ : syracuseStep 749567 = 1124351) B1124351
theorem B14415337 : Blo 443779 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B1505519 : Blo 443779 1505519 := bstep (se 1 (by rfl) ⟨1129139, by rfl⟩ : syracuseStep 1505519 = 2258279) B2258279
theorem B4127689 : Blo 443779 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B1507625 : Blo 443779 1507625 := bstep (se 2 (by rfl) ⟨565359, by rfl⟩ : syracuseStep 1507625 = 1130719) B1130719
theorem B2261519 : Blo 443779 2261519 := bstep (se 1 (by rfl) ⟨1696139, by rfl⟩ : syracuseStep 2261519 = 3392279) B3392279
theorem B2261843 : Blo 443779 2261843 := bstep (se 1 (by rfl) ⟨1696382, by rfl⟩ : syracuseStep 2261843 = 3392765) B3392765
theorem B755291 : Blo 443779 755291 := bstep (se 1 (by rfl) ⟨566468, by rfl⟩ : syracuseStep 755291 = 1132937) B1132937
theorem B5736365 : Blo 443779 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B953977 : Blo 443779 953977 := bstep (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) B715483
theorem B4297319 : Blo 443779 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B47026955 : Blo 443779 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B3806747 : Blo 443779 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B2563271 : Blo 443779 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B499711 : Blo 443779 499711 := bstep (se 1 (by rfl) ⟨374783, by rfl⟩ : syracuseStep 499711 = 749567) B749567
theorem B1124239 : Blo 443779 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B666719 : Blo 443779 666719 := bstep (se 1 (by rfl) ⟨500039, by rfl⟩ : syracuseStep 666719 = 1000079) B1000079
theorem B667391 : Blo 443779 667391 := bstep (se 1 (by rfl) ⟨500543, by rfl⟩ : syracuseStep 667391 = 1001087) B1001087
theorem B2865107 : Blo 443779 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B670505 : Blo 443779 670505 := bstep (se 2 (by rfl) ⟨251439, by rfl⟩ : syracuseStep 670505 = 502879) B502879
theorem B671399 : Blo 443779 671399 := bstep (se 1 (by rfl) ⟨503549, by rfl⟩ : syracuseStep 671399 = 1007099) B1007099
theorem B2539289 : Blo 443779 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B12797027 : Blo 443779 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B7325423 : Blo 443779 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B19220449 : Blo 443779 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B444575 : Blo 443779 444575 := bstep (se 1 (by rfl) ⟨333431, by rfl⟩ : syracuseStep 444575 = 666863) B666863
theorem B445935 : Blo 443779 445935 := bstep (se 1 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 445935 = 668903) B668903
theorem B446319 : Blo 443779 446319 := bstep (se 1 (by rfl) ⟨334739, by rfl⟩ : syracuseStep 446319 = 669479) B669479
theorem B1003679 : Blo 443779 1003679 := bstep (se 1 (by rfl) ⟨752759, by rfl⟩ : syracuseStep 1003679 = 1505519) B1505519
theorem B133682015 : Blo 443779 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B1431017 : Blo 443779 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B2283839 : Blo 443779 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B3398111 : Blo 443779 3398111 := bstep (se 1 (by rfl) ⟨2548583, by rfl⟩ : syracuseStep 3398111 = 5097167) B5097167
theorem B1825361 : Blo 443779 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B3793351 : Blo 443779 3793351 := bstep (se 1 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 3793351 = 5690027) B5690027
theorem B1270511 : Blo 443779 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B845063 : Blo 443779 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B1205887 : Blo 443779 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B3468233 : Blo 443779 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B751295 : Blo 443779 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B12843157 : Blo 443779 12843157 := bstep (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) B602023
theorem B5503585 : Blo 443779 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B9665243 : Blo 443779 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B753151 : Blo 443779 753151 := bstep (se 1 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 753151 = 1129727) B1129727
theorem B1507679 : Blo 443779 1507679 := bstep (se 1 (by rfl) ⟨1130759, by rfl⟩ : syracuseStep 1507679 = 2261519) B2261519
theorem B1507895 : Blo 443779 1507895 := bstep (se 1 (by rfl) ⟨1130921, by rfl⟩ : syracuseStep 1507895 = 2261843) B2261843
theorem B4883615 : Blo 443779 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B1607849 : Blo 443779 1607849 := bstep (se 2 (by rfl) ⟨602943, by rfl⟩ : syracuseStep 1607849 = 1205887) B1205887
theorem B25627265 : Blo 443779 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B954011 : Blo 443779 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B2265407 : Blo 443779 2265407 := bstep (se 1 (by rfl) ⟨1699055, by rfl⟩ : syracuseStep 2265407 = 3398111) B3398111
theorem B1216907 : Blo 443779 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B1708847 : Blo 443779 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B563375 : Blo 443779 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B500863 : Blo 443779 500863 := bstep (se 1 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 500863 = 751295) B751295
theorem B1910071 : Blo 443779 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B666281 : Blo 443779 666281 := bstep (se 2 (by rfl) ⟨249855, by rfl⟩ : syracuseStep 666281 = 499711) B499711
theorem B5057801 : Blo 443779 5057801 := bstep (se 2 (by rfl) ⟨1896675, by rfl⟩ : syracuseStep 5057801 = 3793351) B3793351
theorem B8531351 : Blo 443779 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B503527 : Blo 443779 503527 := bstep (se 1 (by rfl) ⟨377645, by rfl⟩ : syracuseStep 503527 = 755291) B755291
theorem B669119 : Blo 443779 669119 := bstep (se 1 (by rfl) ⟨501839, by rfl⟩ : syracuseStep 669119 = 1003679) B1003679
theorem B2864879 : Blo 443779 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B2537831 : Blo 443779 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B1522559 : Blo 443779 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B2312155 : Blo 443779 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B444479 : Blo 443779 444479 := bstep (se 1 (by rfl) ⟨333359, by rfl⟩ : syracuseStep 444479 = 666719) B666719
theorem B444927 : Blo 443779 444927 := bstep (se 1 (by rfl) ⟨333695, by rfl⟩ : syracuseStep 444927 = 667391) B667391
theorem B17124209 : Blo 443779 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B6443495 : Blo 443779 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B447003 : Blo 443779 447003 := bstep (se 1 (by rfl) ⟨335252, by rfl⟩ : syracuseStep 447003 = 670505) B670505
theorem B1004201 : Blo 443779 1004201 := bstep (se 2 (by rfl) ⟨376575, by rfl⟩ : syracuseStep 1004201 = 753151) B753151
theorem B447599 : Blo 443779 447599 := bstep (se 1 (by rfl) ⟨335699, by rfl⟩ : syracuseStep 447599 = 671399) B671399
theorem B1692859 : Blo 443779 1692859 := bstep (se 1 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 1692859 = 2539289) B2539289
theorem B1005083 : Blo 443779 1005083 := bstep (se 1 (by rfl) ⟨753812, by rfl⟩ : syracuseStep 1005083 = 1507625) B1507625
theorem B3824243 : Blo 443779 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B1498985 : Blo 443779 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B31351303 : Blo 443779 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B89121343 : Blo 443779 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B1271969 : Blo 443779 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B847007 : Blo 443779 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B7338113 : Blo 443779 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B3082873 : Blo 443779 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B1510271 : Blo 443779 1510271 := bstep (se 1 (by rfl) ⟨1132703, by rfl⟩ : syracuseStep 1510271 = 2265407) B2265407
theorem B4295663 : Blo 443779 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B564671 : Blo 443779 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B1909919 : Blo 443779 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B4892075 : Blo 443779 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B118828457 : Blo 443779 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B3255743 : Blo 443779 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B667817 : Blo 443779 667817 := bstep (se 2 (by rfl) ⟨250431, by rfl⟩ : syracuseStep 667817 = 500863) B500863
theorem B17084843 : Blo 443779 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B11416139 : Blo 443779 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B636007 : Blo 443779 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B669467 : Blo 443779 669467 := bstep (se 1 (by rfl) ⟨502100, by rfl⟩ : syracuseStep 669467 = 1004201) B1004201
theorem B670055 : Blo 443779 670055 := bstep (se 1 (by rfl) ⟨502541, by rfl⟩ : syracuseStep 670055 = 1005083) B1005083
theorem B671369 : Blo 443779 671369 := bstep (se 2 (by rfl) ⟨251763, by rfl⟩ : syracuseStep 671369 = 503527) B503527
theorem B999323 : Blo 443779 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B444187 : Blo 443779 444187 := bstep (se 1 (by rfl) ⟨333140, by rfl⟩ : syracuseStep 444187 = 666281) B666281
theorem B5687567 : Blo 443779 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B446079 : Blo 443779 446079 := bstep (se 1 (by rfl) ⟨334559, by rfl⟩ : syracuseStep 446079 = 669119) B669119
theorem B1691887 : Blo 443779 1691887 := bstep (se 1 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 1691887 = 2537831) B2537831
theorem B1005119 : Blo 443779 1005119 := bstep (se 1 (by rfl) ⟨753839, by rfl⟩ : syracuseStep 1005119 = 1507679) B1507679
theorem B1005263 : Blo 443779 1005263 := bstep (se 1 (by rfl) ⟨753947, by rfl⟩ : syracuseStep 1005263 = 1507895) B1507895
theorem B1071899 : Blo 443779 1071899 := bstep (se 1 (by rfl) ⟨803924, by rfl⟩ : syracuseStep 1071899 = 1607849) B1607849
theorem B2546761 : Blo 443779 2546761 := bstep (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) B1910071
theorem B167206949 : Blo 443779 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B811271 : Blo 443779 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B1139231 : Blo 443779 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B2549495 : Blo 443779 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B1502333 : Blo 443779 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B847979 : Blo 443779 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B2257145 : Blo 443779 2257145 := bstep (se 2 (by rfl) ⟨846429, by rfl⟩ : syracuseStep 2257145 = 1692859) B1692859
theorem B3371867 : Blo 443779 3371867 := bstep (se 1 (by rfl) ⟨2528900, by rfl⟩ : syracuseStep 3371867 = 5057801) B5057801
theorem B1015039 : Blo 443779 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B2170495 : Blo 443779 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B565319 : Blo 443779 565319 := bstep (se 1 (by rfl) ⟨423989, by rfl⟩ : syracuseStep 565319 = 847979) B847979
theorem B7610759 : Blo 443779 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B1353385 : Blo 443779 1353385 := bstep (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) B1015039
theorem B666215 : Blo 443779 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B2863775 : Blo 443779 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B4110497 : Blo 443779 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B670079 : Blo 443779 670079 := bstep (se 1 (by rfl) ⟨502559, by rfl⟩ : syracuseStep 670079 = 1005119) B1005119
theorem B670175 : Blo 443779 670175 := bstep (se 1 (by rfl) ⟨502631, by rfl⟩ : syracuseStep 670175 = 1005263) B1005263
theorem B540847 : Blo 443779 540847 := bstep (se 1 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 540847 = 811271) B811271
theorem B3261383 : Blo 443779 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B1001555 : Blo 443779 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B79218971 : Blo 443779 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B445211 : Blo 443779 445211 := bstep (se 1 (by rfl) ⟨333908, by rfl⟩ : syracuseStep 445211 = 667817) B667817
theorem B11389895 : Blo 443779 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B2247911 : Blo 443779 2247911 := bstep (se 1 (by rfl) ⟨1685933, by rfl⟩ : syracuseStep 2247911 = 3371867) B3371867
theorem B446311 : Blo 443779 446311 := bstep (se 1 (by rfl) ⟨334733, by rfl⟩ : syracuseStep 446311 = 669467) B669467
theorem B3395681 : Blo 443779 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B446703 : Blo 443779 446703 := bstep (se 1 (by rfl) ⟨335027, by rfl⟩ : syracuseStep 446703 = 670055) B670055
theorem B447579 : Blo 443779 447579 := bstep (se 1 (by rfl) ⟨335684, by rfl⟩ : syracuseStep 447579 = 671369) B671369
theorem B3037949 : Blo 443779 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B3791711 : Blo 443779 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1006847 : Blo 443779 1006847 := bstep (se 1 (by rfl) ⟨755135, by rfl⟩ : syracuseStep 1006847 = 1510271) B1510271
theorem B714599 : Blo 443779 714599 := bstep (se 1 (by rfl) ⟨535949, by rfl⟩ : syracuseStep 714599 = 1071899) B1071899
theorem B111471299 : Blo 443779 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B2255849 : Blo 443779 2255849 := bstep (se 2 (by rfl) ⟨845943, by rfl⟩ : syracuseStep 2255849 = 1691887) B1691887
theorem B1273279 : Blo 443779 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B1699663 : Blo 443779 1699663 := bstep (se 1 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 1699663 = 2549495) B2549495
theorem B848009 : Blo 443779 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B1504763 : Blo 443779 1504763 := bstep (se 1 (by rfl) ⟨1128572, by rfl⟩ : syracuseStep 1504763 = 2257145) B2257145
theorem B1505789 : Blo 443779 1505789 := bstep (se 3 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 1505789 = 564671) B564671
theorem B1507517 : Blo 443779 1507517 := bstep (se 3 (by rfl) ⟨282659, by rfl⟩ : syracuseStep 1507517 = 565319) B565319
theorem B2261357 : Blo 443779 2261357 := bstep (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) B848009
theorem B2884517 : Blo 443779 2884517 := bstep (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) B540847
theorem B1804513 : Blo 443779 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B2263787 : Blo 443779 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B2527807 : Blo 443779 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B2266217 : Blo 443779 2266217 := bstep (se 2 (by rfl) ⟨849831, by rfl⟩ : syracuseStep 2266217 = 1699663) B1699663
theorem B1909183 : Blo 443779 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B11575973 : Blo 443779 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B2174255 : Blo 443779 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B667703 : Blo 443779 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B671231 : Blo 443779 671231 := bstep (se 1 (by rfl) ⟨503423, by rfl⟩ : syracuseStep 671231 = 1006847) B1006847
theorem B476399 : Blo 443779 476399 := bstep (se 1 (by rfl) ⟨357299, by rfl⟩ : syracuseStep 476399 = 714599) B714599
theorem B444143 : Blo 443779 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B1003175 : Blo 443779 1003175 := bstep (se 1 (by rfl) ⟨752381, by rfl⟩ : syracuseStep 1003175 = 1504763) B1504763
theorem B2740331 : Blo 443779 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B446719 : Blo 443779 446719 := bstep (se 1 (by rfl) ⟨335039, by rfl⟩ : syracuseStep 446719 = 670079) B670079
theorem B446783 : Blo 443779 446783 := bstep (se 1 (by rfl) ⟨335087, by rfl⟩ : syracuseStep 446783 = 670175) B670175
theorem B1003859 : Blo 443779 1003859 := bstep (se 1 (by rfl) ⟨752894, by rfl⟩ : syracuseStep 1003859 = 1505789) B1505789
theorem B52812647 : Blo 443779 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B7593263 : Blo 443779 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B1498607 : Blo 443779 1498607 := bstep (se 1 (by rfl) ⟨1123955, by rfl⟩ : syracuseStep 1498607 = 2247911) B2247911
theorem B2025299 : Blo 443779 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B1697705 : Blo 443779 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B5073839 : Blo 443779 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B74314199 : Blo 443779 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B1503899 : Blo 443779 1503899 := bstep (se 1 (by rfl) ⟨1127924, by rfl⟩ : syracuseStep 1503899 = 2255849) B2255849
theorem B1507571 : Blo 443779 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B1509191 : Blo 443779 1509191 := bstep (se 1 (by rfl) ⟨1131893, by rfl⟩ : syracuseStep 1509191 = 2263787) B2263787
theorem B1510811 : Blo 443779 1510811 := bstep (se 1 (by rfl) ⟨1133108, by rfl⟩ : syracuseStep 1510811 = 2266217) B2266217
theorem B1350199 : Blo 443779 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B3382559 : Blo 443779 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B1449503 : Blo 443779 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B668783 : Blo 443779 668783 := bstep (se 1 (by rfl) ⟨501587, by rfl⟩ : syracuseStep 668783 = 1003175) B1003175
theorem B669239 : Blo 443779 669239 := bstep (se 1 (by rfl) ⟨501929, by rfl⟩ : syracuseStep 669239 = 1003859) B1003859
theorem B2406017 : Blo 443779 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B35208431 : Blo 443779 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B5062175 : Blo 443779 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B999071 : Blo 443779 999071 := bstep (se 1 (by rfl) ⟨749303, by rfl⟩ : syracuseStep 999071 = 1498607) B1498607
theorem B7717315 : Blo 443779 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1131803 : Blo 443779 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B445135 : Blo 443779 445135 := bstep (se 1 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 445135 = 667703) B667703
theorem B1002599 : Blo 443779 1002599 := bstep (se 1 (by rfl) ⟨751949, by rfl⟩ : syracuseStep 1002599 = 1503899) B1503899
theorem B447487 : Blo 443779 447487 := bstep (se 1 (by rfl) ⟨335615, by rfl⟩ : syracuseStep 447487 = 671231) B671231
theorem B1005011 : Blo 443779 1005011 := bstep (se 1 (by rfl) ⟨753758, by rfl⟩ : syracuseStep 1005011 = 1507517) B1507517
theorem B2545577 : Blo 443779 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B1923011 : Blo 443779 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B1826887 : Blo 443779 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B1270397 : Blo 443779 1270397 := bstep (se 3 (by rfl) ⟨238199, by rfl⟩ : syracuseStep 1270397 = 476399) B476399
theorem B3370409 : Blo 443779 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B49542799 : Blo 443779 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B10289753 : Blo 443779 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B754535 : Blo 443779 754535 := bstep (se 1 (by rfl) ⟨565901, by rfl⟩ : syracuseStep 754535 = 1131803) B1131803
theorem B1282007 : Blo 443779 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B23472287 : Blo 443779 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B666047 : Blo 443779 666047 := bstep (se 1 (by rfl) ⟨499535, by rfl⟩ : syracuseStep 666047 = 999071) B999071
theorem B2435849 : Blo 443779 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B668399 : Blo 443779 668399 := bstep (se 1 (by rfl) ⟨501299, by rfl⟩ : syracuseStep 668399 = 1002599) B1002599
theorem B670007 : Blo 443779 670007 := bstep (se 1 (by rfl) ⟨502505, by rfl⟩ : syracuseStep 670007 = 1005011) B1005011
theorem B966335 : Blo 443779 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B2246939 : Blo 443779 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B445855 : Blo 443779 445855 := bstep (se 1 (by rfl) ⟨334391, by rfl⟩ : syracuseStep 445855 = 668783) B668783
theorem B446159 : Blo 443779 446159 := bstep (se 1 (by rfl) ⟨334619, by rfl⟩ : syracuseStep 446159 = 669239) B669239
theorem B1005047 : Blo 443779 1005047 := bstep (se 1 (by rfl) ⟨753785, by rfl⟩ : syracuseStep 1005047 = 1507571) B1507571
theorem B1006127 : Blo 443779 1006127 := bstep (se 1 (by rfl) ⟨754595, by rfl⟩ : syracuseStep 1006127 = 1509191) B1509191
theorem B1007207 : Blo 443779 1007207 := bstep (se 1 (by rfl) ⟨755405, by rfl⟩ : syracuseStep 1007207 = 1510811) B1510811
theorem B7201061 : Blo 443779 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B1697051 : Blo 443779 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B2255039 : Blo 443779 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B846931 : Blo 443779 846931 := bstep (se 1 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 846931 = 1270397) B1270397
theorem B66057065 : Blo 443779 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B1604011 : Blo 443779 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B3374783 : Blo 443779 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B854671 : Blo 443779 854671 := bstep (se 1 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 854671 = 1282007) B1282007
theorem B2138681 : Blo 443779 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B6859835 : Blo 443779 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B503023 : Blo 443779 503023 := bstep (se 1 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 503023 = 754535) B754535
theorem B670031 : Blo 443779 670031 := bstep (se 1 (by rfl) ⟨502523, by rfl⟩ : syracuseStep 670031 = 1005047) B1005047
theorem B1129241 : Blo 443779 1129241 := bstep (se 2 (by rfl) ⟨423465, by rfl⟩ : syracuseStep 1129241 = 846931) B846931
theorem B670751 : Blo 443779 670751 := bstep (se 1 (by rfl) ⟨503063, by rfl⟩ : syracuseStep 670751 = 1006127) B1006127
theorem B671471 : Blo 443779 671471 := bstep (se 1 (by rfl) ⟨503603, by rfl⟩ : syracuseStep 671471 = 1007207) B1007207
theorem B4800707 : Blo 443779 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1131367 : Blo 443779 1131367 := bstep (se 1 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 1131367 = 1697051) B1697051
theorem B15648191 : Blo 443779 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B444031 : Blo 443779 444031 := bstep (se 1 (by rfl) ⟨333023, by rfl⟩ : syracuseStep 444031 = 666047) B666047
theorem B1623899 : Blo 443779 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B10307573 : Blo 443779 10307573 := bstep (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) B966335
theorem B445599 : Blo 443779 445599 := bstep (se 1 (by rfl) ⟨334199, by rfl⟩ : syracuseStep 445599 = 668399) B668399
theorem B446671 : Blo 443779 446671 := bstep (se 1 (by rfl) ⟨335003, by rfl⟩ : syracuseStep 446671 = 670007) B670007
theorem B2249855 : Blo 443779 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B1497959 : Blo 443779 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B1503359 : Blo 443779 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B44038043 : Blo 443779 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B1508489 : Blo 443779 1508489 := bstep (se 2 (by rfl) ⟨565683, by rfl⟩ : syracuseStep 1508489 = 1131367) B1131367
theorem B5703149 : Blo 443779 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B4330397 : Blo 443779 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B10432127 : Blo 443779 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B670697 : Blo 443779 670697 := bstep (se 2 (by rfl) ⟨251511, by rfl⟩ : syracuseStep 670697 = 503023) B503023
theorem B998639 : Blo 443779 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B4573223 : Blo 443779 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B1002239 : Blo 443779 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B446687 : Blo 443779 446687 := bstep (se 1 (by rfl) ⟨335015, by rfl⟩ : syracuseStep 446687 = 670031) B670031
theorem B447167 : Blo 443779 447167 := bstep (se 1 (by rfl) ⟨335375, by rfl⟩ : syracuseStep 447167 = 670751) B670751
theorem B447647 : Blo 443779 447647 := bstep (se 1 (by rfl) ⟨335735, by rfl⟩ : syracuseStep 447647 = 671471) B671471
theorem B3200471 : Blo 443779 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B6871715 : Blo 443779 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B1499903 : Blo 443779 1499903 := bstep (se 1 (by rfl) ⟨1124927, by rfl⟩ : syracuseStep 1499903 = 2249855) B2249855
theorem B1139561 : Blo 443779 1139561 := bstep (se 2 (by rfl) ⟨427335, by rfl⟩ : syracuseStep 1139561 = 854671) B854671
theorem B29358695 : Blo 443779 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B752827 : Blo 443779 752827 := bstep (se 1 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 752827 = 1129241) B1129241
theorem B3802099 : Blo 443779 3802099 := bstep (se 1 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 3802099 = 5703149) B5703149
theorem B3048815 : Blo 443779 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B2886931 : Blo 443779 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B2133647 : Blo 443779 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B759707 : Blo 443779 759707 := bstep (se 1 (by rfl) ⟨569780, by rfl⟩ : syracuseStep 759707 = 1139561) B1139561
theorem B6954751 : Blo 443779 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B19572463 : Blo 443779 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B665759 : Blo 443779 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B668159 : Blo 443779 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B999935 : Blo 443779 999935 := bstep (se 1 (by rfl) ⟨749951, by rfl⟩ : syracuseStep 999935 = 1499903) B1499903
theorem B1003769 : Blo 443779 1003769 := bstep (se 2 (by rfl) ⟨376413, by rfl⟩ : syracuseStep 1003769 = 752827) B752827
theorem B447131 : Blo 443779 447131 := bstep (se 1 (by rfl) ⟨335348, by rfl⟩ : syracuseStep 447131 = 670697) B670697
theorem B1005659 : Blo 443779 1005659 := bstep (se 1 (by rfl) ⟨754244, by rfl⟩ : syracuseStep 1005659 = 1508489) B1508489
theorem B4581143 : Blo 443779 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B2032543 : Blo 443779 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B3054095 : Blo 443779 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B666623 : Blo 443779 666623 := bstep (se 1 (by rfl) ⟨499967, by rfl⟩ : syracuseStep 666623 = 999935) B999935
theorem B26096617 : Blo 443779 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B1422431 : Blo 443779 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B669179 : Blo 443779 669179 := bstep (se 1 (by rfl) ⟨501884, by rfl⟩ : syracuseStep 669179 = 1003769) B1003769
theorem B506471 : Blo 443779 506471 := bstep (se 1 (by rfl) ⟨379853, by rfl⟩ : syracuseStep 506471 = 759707) B759707
theorem B670439 : Blo 443779 670439 := bstep (se 1 (by rfl) ⟨502829, by rfl⟩ : syracuseStep 670439 = 1005659) B1005659
theorem B3849241 : Blo 443779 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B443839 : Blo 443779 443839 := bstep (se 1 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 443839 = 665759) B665759
theorem B445439 : Blo 443779 445439 := bstep (se 1 (by rfl) ⟨334079, by rfl⟩ : syracuseStep 445439 = 668159) B668159
theorem B5069465 : Blo 443779 5069465 := bstep (se 2 (by rfl) ⟨1901049, by rfl⟩ : syracuseStep 5069465 = 3802099) B3802099
theorem B9273001 : Blo 443779 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B2036063 : Blo 443779 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B3379643 : Blo 443779 3379643 := bstep (se 1 (by rfl) ⟨2534732, by rfl⟩ : syracuseStep 3379643 = 5069465) B5069465
theorem B1350589 : Blo 443779 1350589 := bstep (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) B506471
theorem B12364001 : Blo 443779 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B444415 : Blo 443779 444415 := bstep (se 1 (by rfl) ⟨333311, by rfl⟩ : syracuseStep 444415 = 666623) B666623
theorem B446119 : Blo 443779 446119 := bstep (se 1 (by rfl) ⟨334589, by rfl⟩ : syracuseStep 446119 = 669179) B669179
theorem B5132321 : Blo 443779 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B446959 : Blo 443779 446959 := bstep (se 1 (by rfl) ⟨335219, by rfl⟩ : syracuseStep 446959 = 670439) B670439
theorem B10840229 : Blo 443779 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B34795489 : Blo 443779 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B948287 : Blo 443779 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B2528765 : Blo 443779 2528765 := bstep (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) B948287
theorem B3421547 : Blo 443779 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B7226819 : Blo 443779 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B8242667 : Blo 443779 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B5429501 : Blo 443779 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B2253095 : Blo 443779 2253095 := bstep (se 1 (by rfl) ⟨1689821, by rfl⟩ : syracuseStep 2253095 = 3379643) B3379643
theorem B46393985 : Blo 443779 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B1800785 : Blo 443779 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B4817879 : Blo 443779 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B1685843 : Blo 443779 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B3619667 : Blo 443779 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B123717293 : Blo 443779 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B2281031 : Blo 443779 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B1200523 : Blo 443779 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B5495111 : Blo 443779 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B1502063 : Blo 443779 1502063 := bstep (se 1 (by rfl) ⟨1126547, by rfl⟩ : syracuseStep 1502063 = 2253095) B2253095
theorem B3211919 : Blo 443779 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B82478195 : Blo 443779 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B1123895 : Blo 443779 1123895 := bstep (se 1 (by rfl) ⟨842921, by rfl⟩ : syracuseStep 1123895 = 1685843) B1685843
theorem B1520687 : Blo 443779 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B1001375 : Blo 443779 1001375 := bstep (se 1 (by rfl) ⟨751031, by rfl⟩ : syracuseStep 1001375 = 1502063) B1502063
theorem B2413111 : Blo 443779 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B3663407 : Blo 443779 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B1600697 : Blo 443779 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B54985463 : Blo 443779 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B3217481 : Blo 443779 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B2141279 : Blo 443779 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B667583 : Blo 443779 667583 := bstep (se 1 (by rfl) ⟨500687, by rfl⟩ : syracuseStep 667583 = 1001375) B1001375
theorem B2442271 : Blo 443779 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B1067131 : Blo 443779 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B749263 : Blo 443779 749263 := bstep (se 1 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 749263 = 1123895) B1123895
theorem B1013791 : Blo 443779 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B1351721 : Blo 443779 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B3256361 : Blo 443779 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B1422841 : Blo 443779 1422841 := bstep (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) B1067131
theorem B2144987 : Blo 443779 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B999017 : Blo 443779 999017 := bstep (se 2 (by rfl) ⟨374631, by rfl⟩ : syracuseStep 999017 = 749263) B749263
theorem B1427519 : Blo 443779 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B445055 : Blo 443779 445055 := bstep (se 1 (by rfl) ⟨333791, by rfl⟩ : syracuseStep 445055 = 667583) B667583
theorem B36656975 : Blo 443779 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B951679 : Blo 443779 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B2170907 : Blo 443779 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B666011 : Blo 443779 666011 := bstep (se 1 (by rfl) ⟨499508, by rfl⟩ : syracuseStep 666011 = 999017) B999017
theorem B901147 : Blo 443779 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1429991 : Blo 443779 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B24437983 : Blo 443779 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B1897121 : Blo 443779 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B953327 : Blo 443779 953327 := bstep (se 1 (by rfl) ⟨714995, by rfl⟩ : syracuseStep 953327 = 1429991) B1429991
theorem B1447271 : Blo 443779 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B32583977 : Blo 443779 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B444007 : Blo 443779 444007 := bstep (se 1 (by rfl) ⟨333005, by rfl⟩ : syracuseStep 444007 = 666011) B666011
theorem B1264747 : Blo 443779 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B1201529 : Blo 443779 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B1268905 : Blo 443779 1268905 := bstep (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) B951679
theorem B964847 : Blo 443779 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B801019 : Blo 443779 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B1686329 : Blo 443779 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B2542205 : Blo 443779 2542205 := bstep (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) B953327
theorem B1691873 : Blo 443779 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B21722651 : Blo 443779 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B1124219 : Blo 443779 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B4272101 : Blo 443779 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B1127915 : Blo 443779 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B643231 : Blo 443779 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B1694803 : Blo 443779 1694803 := bstep (se 1 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 1694803 = 2542205) B2542205
theorem B14481767 : Blo 443779 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B857641 : Blo 443779 857641 := bstep (se 2 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 857641 = 643231) B643231
theorem B38618045 : Blo 443779 38618045 := bstep (se 3 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 38618045 = 14481767) B14481767
theorem B749479 : Blo 443779 749479 := bstep (se 1 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 749479 = 1124219) B1124219
theorem B2848067 : Blo 443779 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B751943 : Blo 443779 751943 := bstep (se 1 (by rfl) ⟨563957, by rfl⟩ : syracuseStep 751943 = 1127915) B1127915
theorem B2259737 : Blo 443779 2259737 := bstep (se 2 (by rfl) ⟨847401, by rfl⟩ : syracuseStep 2259737 = 1694803) B1694803
theorem B501295 : Blo 443779 501295 := bstep (se 1 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 501295 = 751943) B751943
theorem B999305 : Blo 443779 999305 := bstep (se 2 (by rfl) ⟨374739, by rfl⟩ : syracuseStep 999305 = 749479) B749479
theorem B25745363 : Blo 443779 25745363 := bstep (se 1 (by rfl) ⟨19309022, by rfl⟩ : syracuseStep 25745363 = 38618045) B38618045
theorem B1143521 : Blo 443779 1143521 := bstep (se 2 (by rfl) ⟨428820, by rfl⟩ : syracuseStep 1143521 = 857641) B857641
theorem B1898711 : Blo 443779 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B1506491 : Blo 443779 1506491 := bstep (se 1 (by rfl) ⟨1129868, by rfl⟩ : syracuseStep 1506491 = 2259737) B2259737
theorem B762347 : Blo 443779 762347 := bstep (se 1 (by rfl) ⟨571760, by rfl⟩ : syracuseStep 762347 = 1143521) B1143521
theorem B666203 : Blo 443779 666203 := bstep (se 1 (by rfl) ⟨499652, by rfl⟩ : syracuseStep 666203 = 999305) B999305
theorem B668393 : Blo 443779 668393 := bstep (se 2 (by rfl) ⟨250647, by rfl⟩ : syracuseStep 668393 = 501295) B501295
theorem B1265807 : Blo 443779 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B1004327 : Blo 443779 1004327 := bstep (se 1 (by rfl) ⟨753245, by rfl⟩ : syracuseStep 1004327 = 1506491) B1506491
theorem B17163575 : Blo 443779 17163575 := bstep (se 1 (by rfl) ⟨12872681, by rfl⟩ : syracuseStep 17163575 = 25745363) B25745363
theorem B11442383 : Blo 443779 11442383 := bstep (se 1 (by rfl) ⟨8581787, by rfl⟩ : syracuseStep 11442383 = 17163575) B17163575
theorem B669551 : Blo 443779 669551 := bstep (se 1 (by rfl) ⟨502163, by rfl⟩ : syracuseStep 669551 = 1004327) B1004327
theorem B508231 : Blo 443779 508231 := bstep (se 1 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 508231 = 762347) B762347
theorem B444135 : Blo 443779 444135 := bstep (se 1 (by rfl) ⟨333101, by rfl⟩ : syracuseStep 444135 = 666203) B666203
theorem B445595 : Blo 443779 445595 := bstep (se 1 (by rfl) ⟨334196, by rfl⟩ : syracuseStep 445595 = 668393) B668393
theorem B843871 : Blo 443779 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B1125161 : Blo 443779 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B446367 : Blo 443779 446367 := bstep (se 1 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 446367 = 669551) B669551
theorem B2710565 : Blo 443779 2710565 := bstep (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) B508231
theorem B7628255 : Blo 443779 7628255 := bstep (se 1 (by rfl) ⟨5721191, by rfl⟩ : syracuseStep 7628255 = 11442383) B11442383
theorem B1807043 : Blo 443779 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B5085503 : Blo 443779 5085503 := bstep (se 1 (by rfl) ⟨3814127, by rfl⟩ : syracuseStep 5085503 = 7628255) B7628255
theorem B750107 : Blo 443779 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B4818781 : Blo 443779 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B500071 : Blo 443779 500071 := bstep (se 1 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 500071 = 750107) B750107
theorem B3390335 : Blo 443779 3390335 := bstep (se 1 (by rfl) ⟨2542751, by rfl⟩ : syracuseStep 3390335 = 5085503) B5085503
theorem B6425041 : Blo 443779 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B666761 : Blo 443779 666761 := bstep (se 2 (by rfl) ⟨250035, by rfl⟩ : syracuseStep 666761 = 500071) B500071
theorem B2260223 : Blo 443779 2260223 := bstep (se 1 (by rfl) ⟨1695167, by rfl⟩ : syracuseStep 2260223 = 3390335) B3390335
theorem B8566721 : Blo 443779 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B444507 : Blo 443779 444507 := bstep (se 1 (by rfl) ⟨333380, by rfl⟩ : syracuseStep 444507 = 666761) B666761
theorem B1506815 : Blo 443779 1506815 := bstep (se 1 (by rfl) ⟨1130111, by rfl⟩ : syracuseStep 1506815 = 2260223) B2260223
theorem B5711147 : Blo 443779 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B1004543 : Blo 443779 1004543 := bstep (se 1 (by rfl) ⟨753407, by rfl⟩ : syracuseStep 1004543 = 1506815) B1506815
theorem B3807431 : Blo 443779 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B669695 : Blo 443779 669695 := bstep (se 1 (by rfl) ⟨502271, by rfl⟩ : syracuseStep 669695 = 1004543) B1004543
theorem B2538287 : Blo 443779 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B446463 : Blo 443779 446463 := bstep (se 1 (by rfl) ⟨334847, by rfl⟩ : syracuseStep 446463 = 669695) B669695
theorem B1692191 : Blo 443779 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1128127 : Blo 443779 1128127 := bstep (se 1 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 1128127 = 1692191) B1692191
theorem B1504169 : Blo 443779 1504169 := bstep (se 2 (by rfl) ⟨564063, by rfl⟩ : syracuseStep 1504169 = 1128127) B1128127
theorem B1002779 : Blo 443779 1002779 := bstep (se 1 (by rfl) ⟨752084, by rfl⟩ : syracuseStep 1002779 = 1504169) B1504169
theorem B668519 : Blo 443779 668519 := bstep (se 1 (by rfl) ⟨501389, by rfl⟩ : syracuseStep 668519 = 1002779) B1002779
theorem B445679 : Blo 443779 445679 := bstep (se 1 (by rfl) ⟨334259, by rfl⟩ : syracuseStep 445679 = 668519) B668519

theorem C0 (j : ℕ) (h1 : 110944 ≤ j) (h2 : j ≤ 111643) : Blo 443779 (4 * j + 3) := by
  interval_cases j
  · exact B443779
  · exact B443783
  · exact B443787
  · exact B443791
  · exact B443795
  · exact B443799
  · exact B443803
  · exact B443807
  · exact B443811
  · exact B443815
  · exact B443819
  · exact B443823
  · exact B443827
  · exact B443831
  · exact B443835
  · exact B443839
  · exact B443843
  · exact B443847
  · exact B443851
  · exact B443855
  · exact B443859
  · exact B443863
  · exact B443867
  · exact B443871
  · exact B443875
  · exact B443879
  · exact B443883
  · exact B443887
  · exact B443891
  · exact B443895
  · exact B443899
  · exact B443903
  · exact B443907
  · exact B443911
  · exact B443915
  · exact B443919
  · exact B443923
  · exact B443927
  · exact B443931
  · exact B443935
  · exact B443939
  · exact B443943
  · exact B443947
  · exact B443951
  · exact B443955
  · exact B443959
  · exact B443963
  · exact B443967
  · exact B443971
  · exact B443975
  · exact B443979
  · exact B443983
  · exact B443987
  · exact B443991
  · exact B443995
  · exact B443999
  · exact B444003
  · exact B444007
  · exact B444011
  · exact B444015
  · exact B444019
  · exact B444023
  · exact B444027
  · exact B444031
  · exact B444035
  · exact B444039
  · exact B444043
  · exact B444047
  · exact B444051
  · exact B444055
  · exact B444059
  · exact B444063
  · exact B444067
  · exact B444071
  · exact B444075
  · exact B444079
  · exact B444083
  · exact B444087
  · exact B444091
  · exact B444095
  · exact B444099
  · exact B444103
  · exact B444107
  · exact B444111
  · exact B444115
  · exact B444119
  · exact B444123
  · exact B444127
  · exact B444131
  · exact B444135
  · exact B444139
  · exact B444143
  · exact B444147
  · exact B444151
  · exact B444155
  · exact B444159
  · exact B444163
  · exact B444167
  · exact B444171
  · exact B444175
  · exact B444179
  · exact B444183
  · exact B444187
  · exact B444191
  · exact B444195
  · exact B444199
  · exact B444203
  · exact B444207
  · exact B444211
  · exact B444215
  · exact B444219
  · exact B444223
  · exact B444227
  · exact B444231
  · exact B444235
  · exact B444239
  · exact B444243
  · exact B444247
  · exact B444251
  · exact B444255
  · exact B444259
  · exact B444263
  · exact B444267
  · exact B444271
  · exact B444275
  · exact B444279
  · exact B444283
  · exact B444287
  · exact B444291
  · exact B444295
  · exact B444299
  · exact B444303
  · exact B444307
  · exact B444311
  · exact B444315
  · exact B444319
  · exact B444323
  · exact B444327
  · exact B444331
  · exact B444335
  · exact B444339
  · exact B444343
  · exact B444347
  · exact B444351
  · exact B444355
  · exact B444359
  · exact B444363
  · exact B444367
  · exact B444371
  · exact B444375
  · exact B444379
  · exact B444383
  · exact B444387
  · exact B444391
  · exact B444395
  · exact B444399
  · exact B444403
  · exact B444407
  · exact B444411
  · exact B444415
  · exact B444419
  · exact B444423
  · exact B444427
  · exact B444431
  · exact B444435
  · exact B444439
  · exact B444443
  · exact B444447
  · exact B444451
  · exact B444455
  · exact B444459
  · exact B444463
  · exact B444467
  · exact B444471
  · exact B444475
  · exact B444479
  · exact B444483
  · exact B444487
  · exact B444491
  · exact B444495
  · exact B444499
  · exact B444503
  · exact B444507
  · exact B444511
  · exact B444515
  · exact B444519
  · exact B444523
  · exact B444527
  · exact B444531
  · exact B444535
  · exact B444539
  · exact B444543
  · exact B444547
  · exact B444551
  · exact B444555
  · exact B444559
  · exact B444563
  · exact B444567
  · exact B444571
  · exact B444575
  · exact B444579
  · exact B444583
  · exact B444587
  · exact B444591
  · exact B444595
  · exact B444599
  · exact B444603
  · exact B444607
  · exact B444611
  · exact B444615
  · exact B444619
  · exact B444623
  · exact B444627
  · exact B444631
  · exact B444635
  · exact B444639
  · exact B444643
  · exact B444647
  · exact B444651
  · exact B444655
  · exact B444659
  · exact B444663
  · exact B444667
  · exact B444671
  · exact B444675
  · exact B444679
  · exact B444683
  · exact B444687
  · exact B444691
  · exact B444695
  · exact B444699
  · exact B444703
  · exact B444707
  · exact B444711
  · exact B444715
  · exact B444719
  · exact B444723
  · exact B444727
  · exact B444731
  · exact B444735
  · exact B444739
  · exact B444743
  · exact B444747
  · exact B444751
  · exact B444755
  · exact B444759
  · exact B444763
  · exact B444767
  · exact B444771
  · exact B444775
  · exact B444779
  · exact B444783
  · exact B444787
  · exact B444791
  · exact B444795
  · exact B444799
  · exact B444803
  · exact B444807
  · exact B444811
  · exact B444815
  · exact B444819
  · exact B444823
  · exact B444827
  · exact B444831
  · exact B444835
  · exact B444839
  · exact B444843
  · exact B444847
  · exact B444851
  · exact B444855
  · exact B444859
  · exact B444863
  · exact B444867
  · exact B444871
  · exact B444875
  · exact B444879
  · exact B444883
  · exact B444887
  · exact B444891
  · exact B444895
  · exact B444899
  · exact B444903
  · exact B444907
  · exact B444911
  · exact B444915
  · exact B444919
  · exact B444923
  · exact B444927
  · exact B444931
  · exact B444935
  · exact B444939
  · exact B444943
  · exact B444947
  · exact B444951
  · exact B444955
  · exact B444959
  · exact B444963
  · exact B444967
  · exact B444971
  · exact B444975
  · exact B444979
  · exact B444983
  · exact B444987
  · exact B444991
  · exact B444995
  · exact B444999
  · exact B445003
  · exact B445007
  · exact B445011
  · exact B445015
  · exact B445019
  · exact B445023
  · exact B445027
  · exact B445031
  · exact B445035
  · exact B445039
  · exact B445043
  · exact B445047
  · exact B445051
  · exact B445055
  · exact B445059
  · exact B445063
  · exact B445067
  · exact B445071
  · exact B445075
  · exact B445079
  · exact B445083
  · exact B445087
  · exact B445091
  · exact B445095
  · exact B445099
  · exact B445103
  · exact B445107
  · exact B445111
  · exact B445115
  · exact B445119
  · exact B445123
  · exact B445127
  · exact B445131
  · exact B445135
  · exact B445139
  · exact B445143
  · exact B445147
  · exact B445151
  · exact B445155
  · exact B445159
  · exact B445163
  · exact B445167
  · exact B445171
  · exact B445175
  · exact B445179
  · exact B445183
  · exact B445187
  · exact B445191
  · exact B445195
  · exact B445199
  · exact B445203
  · exact B445207
  · exact B445211
  · exact B445215
  · exact B445219
  · exact B445223
  · exact B445227
  · exact B445231
  · exact B445235
  · exact B445239
  · exact B445243
  · exact B445247
  · exact B445251
  · exact B445255
  · exact B445259
  · exact B445263
  · exact B445267
  · exact B445271
  · exact B445275
  · exact B445279
  · exact B445283
  · exact B445287
  · exact B445291
  · exact B445295
  · exact B445299
  · exact B445303
  · exact B445307
  · exact B445311
  · exact B445315
  · exact B445319
  · exact B445323
  · exact B445327
  · exact B445331
  · exact B445335
  · exact B445339
  · exact B445343
  · exact B445347
  · exact B445351
  · exact B445355
  · exact B445359
  · exact B445363
  · exact B445367
  · exact B445371
  · exact B445375
  · exact B445379
  · exact B445383
  · exact B445387
  · exact B445391
  · exact B445395
  · exact B445399
  · exact B445403
  · exact B445407
  · exact B445411
  · exact B445415
  · exact B445419
  · exact B445423
  · exact B445427
  · exact B445431
  · exact B445435
  · exact B445439
  · exact B445443
  · exact B445447
  · exact B445451
  · exact B445455
  · exact B445459
  · exact B445463
  · exact B445467
  · exact B445471
  · exact B445475
  · exact B445479
  · exact B445483
  · exact B445487
  · exact B445491
  · exact B445495
  · exact B445499
  · exact B445503
  · exact B445507
  · exact B445511
  · exact B445515
  · exact B445519
  · exact B445523
  · exact B445527
  · exact B445531
  · exact B445535
  · exact B445539
  · exact B445543
  · exact B445547
  · exact B445551
  · exact B445555
  · exact B445559
  · exact B445563
  · exact B445567
  · exact B445571
  · exact B445575
  · exact B445579
  · exact B445583
  · exact B445587
  · exact B445591
  · exact B445595
  · exact B445599
  · exact B445603
  · exact B445607
  · exact B445611
  · exact B445615
  · exact B445619
  · exact B445623
  · exact B445627
  · exact B445631
  · exact B445635
  · exact B445639
  · exact B445643
  · exact B445647
  · exact B445651
  · exact B445655
  · exact B445659
  · exact B445663
  · exact B445667
  · exact B445671
  · exact B445675
  · exact B445679
  · exact B445683
  · exact B445687
  · exact B445691
  · exact B445695
  · exact B445699
  · exact B445703
  · exact B445707
  · exact B445711
  · exact B445715
  · exact B445719
  · exact B445723
  · exact B445727
  · exact B445731
  · exact B445735
  · exact B445739
  · exact B445743
  · exact B445747
  · exact B445751
  · exact B445755
  · exact B445759
  · exact B445763
  · exact B445767
  · exact B445771
  · exact B445775
  · exact B445779
  · exact B445783
  · exact B445787
  · exact B445791
  · exact B445795
  · exact B445799
  · exact B445803
  · exact B445807
  · exact B445811
  · exact B445815
  · exact B445819
  · exact B445823
  · exact B445827
  · exact B445831
  · exact B445835
  · exact B445839
  · exact B445843
  · exact B445847
  · exact B445851
  · exact B445855
  · exact B445859
  · exact B445863
  · exact B445867
  · exact B445871
  · exact B445875
  · exact B445879
  · exact B445883
  · exact B445887
  · exact B445891
  · exact B445895
  · exact B445899
  · exact B445903
  · exact B445907
  · exact B445911
  · exact B445915
  · exact B445919
  · exact B445923
  · exact B445927
  · exact B445931
  · exact B445935
  · exact B445939
  · exact B445943
  · exact B445947
  · exact B445951
  · exact B445955
  · exact B445959
  · exact B445963
  · exact B445967
  · exact B445971
  · exact B445975
  · exact B445979
  · exact B445983
  · exact B445987
  · exact B445991
  · exact B445995
  · exact B445999
  · exact B446003
  · exact B446007
  · exact B446011
  · exact B446015
  · exact B446019
  · exact B446023
  · exact B446027
  · exact B446031
  · exact B446035
  · exact B446039
  · exact B446043
  · exact B446047
  · exact B446051
  · exact B446055
  · exact B446059
  · exact B446063
  · exact B446067
  · exact B446071
  · exact B446075
  · exact B446079
  · exact B446083
  · exact B446087
  · exact B446091
  · exact B446095
  · exact B446099
  · exact B446103
  · exact B446107
  · exact B446111
  · exact B446115
  · exact B446119
  · exact B446123
  · exact B446127
  · exact B446131
  · exact B446135
  · exact B446139
  · exact B446143
  · exact B446147
  · exact B446151
  · exact B446155
  · exact B446159
  · exact B446163
  · exact B446167
  · exact B446171
  · exact B446175
  · exact B446179
  · exact B446183
  · exact B446187
  · exact B446191
  · exact B446195
  · exact B446199
  · exact B446203
  · exact B446207
  · exact B446211
  · exact B446215
  · exact B446219
  · exact B446223
  · exact B446227
  · exact B446231
  · exact B446235
  · exact B446239
  · exact B446243
  · exact B446247
  · exact B446251
  · exact B446255
  · exact B446259
  · exact B446263
  · exact B446267
  · exact B446271
  · exact B446275
  · exact B446279
  · exact B446283
  · exact B446287
  · exact B446291
  · exact B446295
  · exact B446299
  · exact B446303
  · exact B446307
  · exact B446311
  · exact B446315
  · exact B446319
  · exact B446323
  · exact B446327
  · exact B446331
  · exact B446335
  · exact B446339
  · exact B446343
  · exact B446347
  · exact B446351
  · exact B446355
  · exact B446359
  · exact B446363
  · exact B446367
  · exact B446371
  · exact B446375
  · exact B446379
  · exact B446383
  · exact B446387
  · exact B446391
  · exact B446395
  · exact B446399
  · exact B446403
  · exact B446407
  · exact B446411
  · exact B446415
  · exact B446419
  · exact B446423
  · exact B446427
  · exact B446431
  · exact B446435
  · exact B446439
  · exact B446443
  · exact B446447
  · exact B446451
  · exact B446455
  · exact B446459
  · exact B446463
  · exact B446467
  · exact B446471
  · exact B446475
  · exact B446479
  · exact B446483
  · exact B446487
  · exact B446491
  · exact B446495
  · exact B446499
  · exact B446503
  · exact B446507
  · exact B446511
  · exact B446515
  · exact B446519
  · exact B446523
  · exact B446527
  · exact B446531
  · exact B446535
  · exact B446539
  · exact B446543
  · exact B446547
  · exact B446551
  · exact B446555
  · exact B446559
  · exact B446563
  · exact B446567
  · exact B446571
  · exact B446575

theorem C1 (j : ℕ) (h1 : 111644 ≤ j) (h2 : j ≤ 111944) : Blo 443779 (4 * j + 3) := by
  interval_cases j
  · exact B446579
  · exact B446583
  · exact B446587
  · exact B446591
  · exact B446595
  · exact B446599
  · exact B446603
  · exact B446607
  · exact B446611
  · exact B446615
  · exact B446619
  · exact B446623
  · exact B446627
  · exact B446631
  · exact B446635
  · exact B446639
  · exact B446643
  · exact B446647
  · exact B446651
  · exact B446655
  · exact B446659
  · exact B446663
  · exact B446667
  · exact B446671
  · exact B446675
  · exact B446679
  · exact B446683
  · exact B446687
  · exact B446691
  · exact B446695
  · exact B446699
  · exact B446703
  · exact B446707
  · exact B446711
  · exact B446715
  · exact B446719
  · exact B446723
  · exact B446727
  · exact B446731
  · exact B446735
  · exact B446739
  · exact B446743
  · exact B446747
  · exact B446751
  · exact B446755
  · exact B446759
  · exact B446763
  · exact B446767
  · exact B446771
  · exact B446775
  · exact B446779
  · exact B446783
  · exact B446787
  · exact B446791
  · exact B446795
  · exact B446799
  · exact B446803
  · exact B446807
  · exact B446811
  · exact B446815
  · exact B446819
  · exact B446823
  · exact B446827
  · exact B446831
  · exact B446835
  · exact B446839
  · exact B446843
  · exact B446847
  · exact B446851
  · exact B446855
  · exact B446859
  · exact B446863
  · exact B446867
  · exact B446871
  · exact B446875
  · exact B446879
  · exact B446883
  · exact B446887
  · exact B446891
  · exact B446895
  · exact B446899
  · exact B446903
  · exact B446907
  · exact B446911
  · exact B446915
  · exact B446919
  · exact B446923
  · exact B446927
  · exact B446931
  · exact B446935
  · exact B446939
  · exact B446943
  · exact B446947
  · exact B446951
  · exact B446955
  · exact B446959
  · exact B446963
  · exact B446967
  · exact B446971
  · exact B446975
  · exact B446979
  · exact B446983
  · exact B446987
  · exact B446991
  · exact B446995
  · exact B446999
  · exact B447003
  · exact B447007
  · exact B447011
  · exact B447015
  · exact B447019
  · exact B447023
  · exact B447027
  · exact B447031
  · exact B447035
  · exact B447039
  · exact B447043
  · exact B447047
  · exact B447051
  · exact B447055
  · exact B447059
  · exact B447063
  · exact B447067
  · exact B447071
  · exact B447075
  · exact B447079
  · exact B447083
  · exact B447087
  · exact B447091
  · exact B447095
  · exact B447099
  · exact B447103
  · exact B447107
  · exact B447111
  · exact B447115
  · exact B447119
  · exact B447123
  · exact B447127
  · exact B447131
  · exact B447135
  · exact B447139
  · exact B447143
  · exact B447147
  · exact B447151
  · exact B447155
  · exact B447159
  · exact B447163
  · exact B447167
  · exact B447171
  · exact B447175
  · exact B447179
  · exact B447183
  · exact B447187
  · exact B447191
  · exact B447195
  · exact B447199
  · exact B447203
  · exact B447207
  · exact B447211
  · exact B447215
  · exact B447219
  · exact B447223
  · exact B447227
  · exact B447231
  · exact B447235
  · exact B447239
  · exact B447243
  · exact B447247
  · exact B447251
  · exact B447255
  · exact B447259
  · exact B447263
  · exact B447267
  · exact B447271
  · exact B447275
  · exact B447279
  · exact B447283
  · exact B447287
  · exact B447291
  · exact B447295
  · exact B447299
  · exact B447303
  · exact B447307
  · exact B447311
  · exact B447315
  · exact B447319
  · exact B447323
  · exact B447327
  · exact B447331
  · exact B447335
  · exact B447339
  · exact B447343
  · exact B447347
  · exact B447351
  · exact B447355
  · exact B447359
  · exact B447363
  · exact B447367
  · exact B447371
  · exact B447375
  · exact B447379
  · exact B447383
  · exact B447387
  · exact B447391
  · exact B447395
  · exact B447399
  · exact B447403
  · exact B447407
  · exact B447411
  · exact B447415
  · exact B447419
  · exact B447423
  · exact B447427
  · exact B447431
  · exact B447435
  · exact B447439
  · exact B447443
  · exact B447447
  · exact B447451
  · exact B447455
  · exact B447459
  · exact B447463
  · exact B447467
  · exact B447471
  · exact B447475
  · exact B447479
  · exact B447483
  · exact B447487
  · exact B447491
  · exact B447495
  · exact B447499
  · exact B447503
  · exact B447507
  · exact B447511
  · exact B447515
  · exact B447519
  · exact B447523
  · exact B447527
  · exact B447531
  · exact B447535
  · exact B447539
  · exact B447543
  · exact B447547
  · exact B447551
  · exact B447555
  · exact B447559
  · exact B447563
  · exact B447567
  · exact B447571
  · exact B447575
  · exact B447579
  · exact B447583
  · exact B447587
  · exact B447591
  · exact B447595
  · exact B447599
  · exact B447603
  · exact B447607
  · exact B447611
  · exact B447615
  · exact B447619
  · exact B447623
  · exact B447627
  · exact B447631
  · exact B447635
  · exact B447639
  · exact B447643
  · exact B447647
  · exact B447651
  · exact B447655
  · exact B447659
  · exact B447663
  · exact B447667
  · exact B447671
  · exact B447675
  · exact B447679
  · exact B447683
  · exact B447687
  · exact B447691
  · exact B447695
  · exact B447699
  · exact B447703
  · exact B447707
  · exact B447711
  · exact B447715
  · exact B447719
  · exact B447723
  · exact B447727
  · exact B447731
  · exact B447735
  · exact B447739
  · exact B447743
  · exact B447747
  · exact B447751
  · exact B447755
  · exact B447759
  · exact B447763
  · exact B447767
  · exact B447771
  · exact B447775
  · exact B447779

theorem solution (m : ℕ) (hlo : 443779 ≤ m) (hhi : m ≤ 447779) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 110944 ≤ j := by omega
    have hj2 : j ≤ 111944 := by omega
    have hb : Blo 443779 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 111644 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
