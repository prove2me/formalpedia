-- Prove2me | solution 1 for syracuse_descends_range_1488064_1490064
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:46:33.309263+00:00
-- url     : https://prove2.me/submissions/3729dce5-a6a2-472b-bd65-5e969056040e

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


theorem B1884161 : Blo 1488064 1884161 := bbase (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) (by norm_num)
theorem B3350573 : Blo 1488064 3350573 := bbase (se 3 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 3350573 = 1256465) (by norm_num)
theorem B4767797 : Blo 1488064 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B2039861 : Blo 1488064 2039861 := bbase (se 5 (by rfl) ⟨95618, by rfl⟩ : syracuseStep 2039861 = 191237) (by norm_num)
theorem B1884217 : Blo 1488064 1884217 := bbase (se 2 (by rfl) ⟨706581, by rfl⟩ : syracuseStep 1884217 = 1413163) (by norm_num)
theorem B7536725 : Blo 1488064 7536725 := bbase (se 8 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 7536725 = 88321) (by norm_num)
theorem B3350645 : Blo 1488064 3350645 := bbase (se 5 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 3350645 = 314123) (by norm_num)
theorem B1589377 : Blo 1488064 1589377 := bbase (se 2 (by rfl) ⟨596016, by rfl⟩ : syracuseStep 1589377 = 1192033) (by norm_num)
theorem B1884313 : Blo 1488064 1884313 := bbase (se 2 (by rfl) ⟨706617, by rfl⟩ : syracuseStep 1884313 = 1413235) (by norm_num)
theorem B6037685 : Blo 1488064 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B3350717 : Blo 1488064 3350717 := bbase (se 3 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 3350717 = 1256519) (by norm_num)
theorem B3768565 : Blo 1488064 3768565 := bbase (se 5 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 3768565 = 353303) (by norm_num)
theorem B2826485 : Blo 1488064 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B1589501 : Blo 1488064 1589501 := bbase (se 3 (by rfl) ⟨298031, by rfl⟩ : syracuseStep 1589501 = 596063) (by norm_num)
theorem B3350789 : Blo 1488064 3350789 := bbase (se 4 (by rfl) ⟨314136, by rfl⟩ : syracuseStep 3350789 = 628273) (by norm_num)
theorem B2384149 : Blo 1488064 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B8053013 : Blo 1488064 8053013 := bbase (se 6 (by rfl) ⟨188742, by rfl⟩ : syracuseStep 8053013 = 377485) (by norm_num)
theorem B5652773 : Blo 1488064 5652773 := bbase (se 4 (by rfl) ⟨529947, by rfl⟩ : syracuseStep 5652773 = 1059895) (by norm_num)
theorem B1884485 : Blo 1488064 1884485 := bbase (se 4 (by rfl) ⟨176670, by rfl⟩ : syracuseStep 1884485 = 353341) (by norm_num)
theorem B3350861 : Blo 1488064 3350861 := bbase (se 3 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 3350861 = 1256573) (by norm_num)
theorem B3768677 : Blo 1488064 3768677 := bbase (se 4 (by rfl) ⟨353313, by rfl⟩ : syracuseStep 3768677 = 706627) (by norm_num)
theorem B6037877 : Blo 1488064 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B1884541 : Blo 1488064 1884541 := bbase (se 3 (by rfl) ⟨353351, by rfl⟩ : syracuseStep 1884541 = 706703) (by norm_num)
theorem B3350933 : Blo 1488064 3350933 := bbase (se 6 (by rfl) ⟨78537, by rfl⟩ : syracuseStep 3350933 = 157075) (by norm_num)
theorem B1884637 : Blo 1488064 1884637 := bbase (se 3 (by rfl) ⟨353369, by rfl⟩ : syracuseStep 1884637 = 706739) (by norm_num)
theorem B3351005 : Blo 1488064 3351005 := bbase (se 3 (by rfl) ⟨628313, by rfl⟩ : syracuseStep 3351005 = 1256627) (by norm_num)
theorem B6447605 : Blo 1488064 6447605 := bbase (se 5 (by rfl) ⟨302231, by rfl⟩ : syracuseStep 6447605 = 604463) (by norm_num)
theorem B1589753 : Blo 1488064 1589753 := bbase (se 2 (by rfl) ⟨596157, by rfl⟩ : syracuseStep 1589753 = 1192315) (by norm_num)
theorem B3310093 : Blo 1488064 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B29000213 : Blo 1488064 29000213 := bbase (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) (by norm_num)
theorem B13591061 : Blo 1488064 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B6357541 : Blo 1488064 6357541 := bbase (se 4 (by rfl) ⟨596019, by rfl⟩ : syracuseStep 6357541 = 1192039) (by norm_num)
theorem B3768869 : Blo 1488064 3768869 := bbase (se 4 (by rfl) ⟨353331, by rfl⟩ : syracuseStep 3768869 = 706663) (by norm_num)
theorem B3351077 : Blo 1488064 3351077 := bbase (se 4 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 3351077 = 628327) (by norm_num)
theorem B5653061 : Blo 1488064 5653061 := bbase (se 4 (by rfl) ⟨529974, by rfl⟩ : syracuseStep 5653061 = 1059949) (by norm_num)
theorem B3351149 : Blo 1488064 3351149 := bbase (se 3 (by rfl) ⟨628340, by rfl⟩ : syracuseStep 3351149 = 1256681) (by norm_num)
theorem B1884809 : Blo 1488064 1884809 := bbase (se 2 (by rfl) ⟨706803, by rfl⟩ : syracuseStep 1884809 = 1413607) (by norm_num)
theorem B3351221 : Blo 1488064 3351221 := bbase (se 5 (by rfl) ⟨157088, by rfl⟩ : syracuseStep 3351221 = 314177) (by norm_num)
theorem B1884865 : Blo 1488064 1884865 := bbase (se 2 (by rfl) ⟨706824, by rfl⟩ : syracuseStep 1884865 = 1413649) (by norm_num)
theorem B3351293 : Blo 1488064 3351293 := bbase (se 3 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 3351293 = 1256735) (by norm_num)
theorem B7742213 : Blo 1488064 7742213 := bbase (se 4 (by rfl) ⟨725832, by rfl⟩ : syracuseStep 7742213 = 1451665) (by norm_num)
theorem B2417413 : Blo 1488064 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B5022485 : Blo 1488064 5022485 := bbase (se 6 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 5022485 = 235429) (by norm_num)
theorem B6791957 : Blo 1488064 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B1884961 : Blo 1488064 1884961 := bbase (se 2 (by rfl) ⟨706860, by rfl⟩ : syracuseStep 1884961 = 1413721) (by norm_num)
theorem B3351365 : Blo 1488064 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B3769213 : Blo 1488064 3769213 := bbase (se 3 (by rfl) ⟨706727, by rfl⟩ : syracuseStep 3769213 = 1413455) (by norm_num)
theorem B3351437 : Blo 1488064 3351437 := bbase (se 3 (by rfl) ⟨628394, by rfl⟩ : syracuseStep 3351437 = 1256789) (by norm_num)
theorem B8479637 : Blo 1488064 8479637 := bbase (se 6 (by rfl) ⟨198741, by rfl⟩ : syracuseStep 8479637 = 397483) (by norm_num)
theorem B2384821 : Blo 1488064 2384821 := bbase (se 5 (by rfl) ⟨111788, by rfl⟩ : syracuseStep 2384821 = 223577) (by norm_num)
theorem B1590197 : Blo 1488064 1590197 := bbase (se 5 (by rfl) ⟨74540, by rfl⟩ : syracuseStep 1590197 = 149081) (by norm_num)
theorem B1885133 : Blo 1488064 1885133 := bbase (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) (by norm_num)
theorem B3351509 : Blo 1488064 3351509 := bbase (se 7 (by rfl) ⟨39275, by rfl⟩ : syracuseStep 3351509 = 78551) (by norm_num)
theorem B2827237 : Blo 1488064 2827237 := bbase (se 4 (by rfl) ⟨265053, by rfl⟩ : syracuseStep 2827237 = 530107) (by norm_num)
theorem B3769325 : Blo 1488064 3769325 := bbase (se 3 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 3769325 = 1413497) (by norm_num)
theorem B1885189 : Blo 1488064 1885189 := bbase (se 4 (by rfl) ⟨176736, by rfl⟩ : syracuseStep 1885189 = 353473) (by norm_num)
theorem B3179549 : Blo 1488064 3179549 := bbase (se 3 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 3179549 = 1192331) (by norm_num)
theorem B3351581 : Blo 1488064 3351581 := bbase (se 3 (by rfl) ⟨628421, by rfl⟩ : syracuseStep 3351581 = 1256843) (by norm_num)
theorem B7251029 : Blo 1488064 7251029 := bbase (se 8 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 7251029 = 84973) (by norm_num)
theorem B1885285 : Blo 1488064 1885285 := bbase (se 4 (by rfl) ⟨176745, by rfl⟩ : syracuseStep 1885285 = 353491) (by norm_num)
theorem B3351653 : Blo 1488064 3351653 := bbase (se 4 (by rfl) ⟨314217, by rfl⟩ : syracuseStep 3351653 = 628435) (by norm_num)
theorem B2827381 : Blo 1488064 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B3179693 : Blo 1488064 3179693 := bbase (se 3 (by rfl) ⟨596192, by rfl⟩ : syracuseStep 3179693 = 1192385) (by norm_num)
theorem B3769517 : Blo 1488064 3769517 := bbase (se 3 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 3769517 = 1413569) (by norm_num)
theorem B1590445 : Blo 1488064 1590445 := bbase (se 3 (by rfl) ⟨298208, by rfl⟩ : syracuseStep 1590445 = 596417) (by norm_num)
theorem B3351725 : Blo 1488064 3351725 := bbase (se 3 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 3351725 = 1256897) (by norm_num)
theorem B1508537 : Blo 1488064 1508537 := bbase (se 2 (by rfl) ⟨565701, by rfl⟩ : syracuseStep 1508537 = 1131403) (by norm_num)
theorem B5022917 : Blo 1488064 5022917 := bbase (se 4 (by rfl) ⟨470898, by rfl⟩ : syracuseStep 5022917 = 941797) (by norm_num)
theorem B3351797 : Blo 1488064 3351797 := bbase (se 5 (by rfl) ⟨157115, by rfl⟩ : syracuseStep 3351797 = 314231) (by norm_num)
theorem B6358277 : Blo 1488064 6358277 := bbase (se 4 (by rfl) ⟨596088, by rfl⟩ : syracuseStep 6358277 = 1192177) (by norm_num)
theorem B1697041 : Blo 1488064 1697041 := bbase (se 2 (by rfl) ⟨636390, by rfl⟩ : syracuseStep 1697041 = 1272781) (by norm_num)
theorem B1885457 : Blo 1488064 1885457 := bbase (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) (by norm_num)
theorem B2827541 : Blo 1488064 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B3351869 : Blo 1488064 3351869 := bbase (se 3 (by rfl) ⟨628475, by rfl⟩ : syracuseStep 3351869 = 1256951) (by norm_num)
theorem B1885513 : Blo 1488064 1885513 := bbase (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) (by norm_num)
theorem B7538021 : Blo 1488064 7538021 := bbase (se 4 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 7538021 = 1413379) (by norm_num)
theorem B3351941 : Blo 1488064 3351941 := bbase (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) (by norm_num)
theorem B2827685 : Blo 1488064 2827685 := bbase (se 4 (by rfl) ⟨265095, by rfl⟩ : syracuseStep 2827685 = 530191) (by norm_num)
theorem B1885609 : Blo 1488064 1885609 := bbase (se 2 (by rfl) ⟨707103, by rfl⟩ : syracuseStep 1885609 = 1414207) (by norm_num)
theorem B1508797 : Blo 1488064 1508797 := bbase (se 3 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 1508797 = 565799) (by norm_num)
theorem B3352013 : Blo 1488064 3352013 := bbase (se 3 (by rfl) ⟨628502, by rfl⟩ : syracuseStep 3352013 = 1257005) (by norm_num)
theorem B7849477 : Blo 1488064 7849477 := bbase (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) (by norm_num)
theorem B3769861 : Blo 1488064 3769861 := bbase (se 4 (by rfl) ⟨353424, by rfl⟩ : syracuseStep 3769861 = 706849) (by norm_num)
theorem B3180053 : Blo 1488064 3180053 := bbase (se 6 (by rfl) ⟨74532, by rfl⟩ : syracuseStep 3180053 = 149065) (by norm_num)
theorem B3352085 : Blo 1488064 3352085 := bbase (se 6 (by rfl) ⟨78564, by rfl⟩ : syracuseStep 3352085 = 157129) (by norm_num)
theorem B32212565 : Blo 1488064 32212565 := bbase (se 8 (by rfl) ⟨188745, by rfl⟩ : syracuseStep 32212565 = 377491) (by norm_num)
theorem B1885781 : Blo 1488064 1885781 := bbase (se 8 (by rfl) ⟨11049, by rfl⟩ : syracuseStep 1885781 = 22099) (by norm_num)
theorem B3352157 : Blo 1488064 3352157 := bbase (se 3 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 3352157 = 1257059) (by norm_num)
theorem B1590889 : Blo 1488064 1590889 := bbase (se 2 (by rfl) ⟨596583, by rfl⟩ : syracuseStep 1590889 = 1193167) (by norm_num)
theorem B5023349 : Blo 1488064 5023349 := bbase (se 5 (by rfl) ⟨235469, by rfl⟩ : syracuseStep 5023349 = 470939) (by norm_num)
theorem B3769973 : Blo 1488064 3769973 := bbase (se 5 (by rfl) ⟨176717, by rfl⟩ : syracuseStep 3769973 = 353435) (by norm_num)
theorem B1885837 : Blo 1488064 1885837 := bbase (se 3 (by rfl) ⟨353594, by rfl⟩ : syracuseStep 1885837 = 707189) (by norm_num)
theorem B1590949 : Blo 1488064 1590949 := bbase (se 4 (by rfl) ⟨149151, by rfl⟩ : syracuseStep 1590949 = 298303) (by norm_num)
theorem B3352229 : Blo 1488064 3352229 := bbase (se 4 (by rfl) ⟨314271, by rfl⟩ : syracuseStep 3352229 = 628543) (by norm_num)
theorem B2827973 : Blo 1488064 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B5654245 : Blo 1488064 5654245 := bbase (se 4 (by rfl) ⟨530085, by rfl⟩ : syracuseStep 5654245 = 1060171) (by norm_num)
theorem B3352301 : Blo 1488064 3352301 := bbase (se 3 (by rfl) ⟨628556, by rfl⟩ : syracuseStep 3352301 = 1257113) (by norm_num)
theorem B1910557 : Blo 1488064 1910557 := bbase (se 3 (by rfl) ⟨358229, by rfl⟩ : syracuseStep 1910557 = 716459) (by norm_num)
theorem B3770165 : Blo 1488064 3770165 := bbase (se 5 (by rfl) ⟨176726, by rfl⟩ : syracuseStep 3770165 = 353453) (by norm_num)
theorem B3352373 : Blo 1488064 3352373 := bbase (se 5 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 3352373 = 314285) (by norm_num)
theorem B2828125 : Blo 1488064 2828125 := bbase (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) (by norm_num)
theorem B3352445 : Blo 1488064 3352445 := bbase (se 3 (by rfl) ⟨628583, by rfl⟩ : syracuseStep 3352445 = 1257167) (by norm_num)
theorem B2385821 : Blo 1488064 2385821 := bbase (se 3 (by rfl) ⟨447341, by rfl⟩ : syracuseStep 2385821 = 894683) (by norm_num)
theorem B3352517 : Blo 1488064 3352517 := bbase (se 4 (by rfl) ⟨314298, by rfl⟩ : syracuseStep 3352517 = 628597) (by norm_num)
theorem B19335125 : Blo 1488064 19335125 := bbase (se 7 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 19335125 = 453167) (by norm_num)
theorem B3352589 : Blo 1488064 3352589 := bbase (se 3 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 3352589 = 1257221) (by norm_num)
theorem B5654549 : Blo 1488064 5654549 := bbase (se 6 (by rfl) ⟨132528, by rfl⟩ : syracuseStep 5654549 = 265057) (by norm_num)
theorem B5023781 : Blo 1488064 5023781 := bbase (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) (by norm_num)
theorem B8480821 : Blo 1488064 8480821 := bbase (se 5 (by rfl) ⟨397538, by rfl⟩ : syracuseStep 8480821 = 795077) (by norm_num)
theorem B9545845 : Blo 1488064 9545845 := bbase (se 5 (by rfl) ⟨447461, by rfl⟩ : syracuseStep 9545845 = 894923) (by norm_num)
theorem B1697917 : Blo 1488064 1697917 := bbase (se 3 (by rfl) ⟨318359, by rfl⟩ : syracuseStep 1697917 = 636719) (by norm_num)
theorem B3770509 : Blo 1488064 3770509 := bbase (se 3 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 3770509 = 1413941) (by norm_num)
theorem B2828429 : Blo 1488064 2828429 := bbase (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) (by norm_num)
theorem B9537749 : Blo 1488064 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B4237541 : Blo 1488064 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B3770621 : Blo 1488064 3770621 := bbase (se 3 (by rfl) ⟨706991, by rfl⟩ : syracuseStep 3770621 = 1413983) (by norm_num)
theorem B4770053 : Blo 1488064 4770053 := bbase (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) (by norm_num)
theorem B3393917 : Blo 1488064 3393917 := bbase (se 3 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 3393917 = 1272719) (by norm_num)
theorem B4770181 : Blo 1488064 4770181 := bbase (se 4 (by rfl) ⟨447204, by rfl⟩ : syracuseStep 4770181 = 894409) (by norm_num)
theorem B3180941 : Blo 1488064 3180941 := bbase (se 3 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 3180941 = 1192853) (by norm_num)
theorem B12069269 : Blo 1488064 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B3770813 : Blo 1488064 3770813 := bbase (se 3 (by rfl) ⟨707027, by rfl⟩ : syracuseStep 3770813 = 1414055) (by norm_num)
theorem B5024213 : Blo 1488064 5024213 := bbase (se 7 (by rfl) ⟨58877, by rfl⟩ : syracuseStep 5024213 = 117755) (by norm_num)
theorem B2263621 : Blo 1488064 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B1509985 : Blo 1488064 1509985 := bbase (se 2 (by rfl) ⟨566244, by rfl⟩ : syracuseStep 1509985 = 1132489) (by norm_num)
theorem B1698409 : Blo 1488064 1698409 := bbase (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) (by norm_num)
theorem B7539317 : Blo 1488064 7539317 := bbase (se 5 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 7539317 = 706811) (by norm_num)
theorem B3181189 : Blo 1488064 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B1510021 : Blo 1488064 1510021 := bbase (se 4 (by rfl) ⟨141564, by rfl⟩ : syracuseStep 1510021 = 283129) (by norm_num)
theorem B1698565 : Blo 1488064 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B1788689 : Blo 1488064 1788689 := bbase (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) (by norm_num)
theorem B3771157 : Blo 1488064 3771157 := bbase (se 6 (by rfl) ⟨88386, by rfl⟩ : syracuseStep 3771157 = 176773) (by norm_num)
theorem B1674085 : Blo 1488064 1674085 := bbase (se 4 (by rfl) ⟨156945, by rfl⟩ : syracuseStep 1674085 = 313891) (by norm_num)
theorem B5024645 : Blo 1488064 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B3771269 : Blo 1488064 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B1674121 : Blo 1488064 1674121 := bbase (se 2 (by rfl) ⟨627795, by rfl⟩ : syracuseStep 1674121 = 1255591) (by norm_num)
theorem B1674157 : Blo 1488064 1674157 := bbase (se 3 (by rfl) ⟨313904, by rfl⟩ : syracuseStep 1674157 = 627809) (by norm_num)
theorem B1698737 : Blo 1488064 1698737 := bbase (se 2 (by rfl) ⟨637026, by rfl⟩ : syracuseStep 1698737 = 1274053) (by norm_num)
theorem B1674193 : Blo 1488064 1674193 := bbase (se 2 (by rfl) ⟨627822, by rfl⟩ : syracuseStep 1674193 = 1255645) (by norm_num)
theorem B1698769 : Blo 1488064 1698769 := bbase (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) (by norm_num)
theorem B5368789 : Blo 1488064 5368789 := bbase (se 7 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 5368789 = 125831) (by norm_num)
theorem B1674229 : Blo 1488064 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B1674265 : Blo 1488064 1674265 := bbase (se 2 (by rfl) ⟨627849, by rfl⟩ : syracuseStep 1674265 = 1255699) (by norm_num)
theorem B1674301 : Blo 1488064 1674301 := bbase (se 3 (by rfl) ⟨313931, by rfl⟩ : syracuseStep 1674301 = 627863) (by norm_num)
theorem B3771461 : Blo 1488064 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B3820621 : Blo 1488064 3820621 := bbase (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) (by norm_num)
theorem B12725333 : Blo 1488064 12725333 := bbase (se 8 (by rfl) ⟨74562, by rfl⟩ : syracuseStep 12725333 = 149125) (by norm_num)
theorem B1674337 : Blo 1488064 1674337 := bbase (se 2 (by rfl) ⟨627876, by rfl⟩ : syracuseStep 1674337 = 1255753) (by norm_num)
theorem B8047733 : Blo 1488064 8047733 := bbase (se 5 (by rfl) ⟨377237, by rfl⟩ : syracuseStep 8047733 = 754475) (by norm_num)
theorem B3181693 : Blo 1488064 3181693 := bbase (se 3 (by rfl) ⟨596567, by rfl⟩ : syracuseStep 3181693 = 1193135) (by norm_num)
theorem B1674373 : Blo 1488064 1674373 := bbase (se 4 (by rfl) ⟨156972, by rfl⟩ : syracuseStep 1674373 = 313945) (by norm_num)
theorem B1674409 : Blo 1488064 1674409 := bbase (se 2 (by rfl) ⟨627903, by rfl⟩ : syracuseStep 1674409 = 1255807) (by norm_num)
theorem B1674445 : Blo 1488064 1674445 := bbase (se 3 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 1674445 = 627917) (by norm_num)
theorem B12717269 : Blo 1488064 12717269 := bbase (se 7 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 12717269 = 298061) (by norm_num)
theorem B1674481 : Blo 1488064 1674481 := bbase (se 2 (by rfl) ⟨627930, by rfl⟩ : syracuseStep 1674481 = 1255861) (by norm_num)
theorem B1674517 : Blo 1488064 1674517 := bbase (se 6 (by rfl) ⟨39246, by rfl⟩ : syracuseStep 1674517 = 78493) (by norm_num)
theorem B5025077 : Blo 1488064 5025077 := bbase (se 5 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 5025077 = 471101) (by norm_num)
theorem B6794549 : Blo 1488064 6794549 := bbase (se 5 (by rfl) ⟨318494, by rfl⟩ : syracuseStep 6794549 = 636989) (by norm_num)
theorem B1674553 : Blo 1488064 1674553 := bbase (se 2 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 1674553 = 1255915) (by norm_num)
theorem B1674589 : Blo 1488064 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B1674625 : Blo 1488064 1674625 := bbase (se 2 (by rfl) ⟨627984, by rfl⟩ : syracuseStep 1674625 = 1255969) (by norm_num)
theorem B4238725 : Blo 1488064 4238725 := bbase (se 4 (by rfl) ⟨397380, by rfl⟩ : syracuseStep 4238725 = 794761) (by norm_num)
theorem B1674661 : Blo 1488064 1674661 := bbase (se 4 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 1674661 = 313999) (by norm_num)
theorem B1674697 : Blo 1488064 1674697 := bbase (se 2 (by rfl) ⟨628011, by rfl⟩ : syracuseStep 1674697 = 1256023) (by norm_num)
theorem B1674733 : Blo 1488064 1674733 := bbase (se 3 (by rfl) ⟨314012, by rfl⟩ : syracuseStep 1674733 = 628025) (by norm_num)
theorem B1551857 : Blo 1488064 1551857 := bbase (se 2 (by rfl) ⟨581946, by rfl⟩ : syracuseStep 1551857 = 1163893) (by norm_num)
theorem B1674769 : Blo 1488064 1674769 := bbase (se 2 (by rfl) ⟨628038, by rfl⟩ : syracuseStep 1674769 = 1256077) (by norm_num)
theorem B4238885 : Blo 1488064 4238885 := bbase (se 4 (by rfl) ⟨397395, by rfl⟩ : syracuseStep 4238885 = 794791) (by norm_num)
theorem B1674805 : Blo 1488064 1674805 := bbase (se 5 (by rfl) ⟨78506, by rfl⟩ : syracuseStep 1674805 = 157013) (by norm_num)
theorem B1674841 : Blo 1488064 1674841 := bbase (se 2 (by rfl) ⟨628065, by rfl⟩ : syracuseStep 1674841 = 1256131) (by norm_num)
theorem B1674877 : Blo 1488064 1674877 := bbase (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) (by norm_num)
theorem B1674913 : Blo 1488064 1674913 := bbase (se 2 (by rfl) ⟨628092, by rfl⟩ : syracuseStep 1674913 = 1256185) (by norm_num)
theorem B9178805 : Blo 1488064 9178805 := bbase (se 5 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 9178805 = 860513) (by norm_num)
theorem B1674949 : Blo 1488064 1674949 := bbase (se 4 (by rfl) ⟨157026, by rfl⟩ : syracuseStep 1674949 = 314053) (by norm_num)
theorem B12889813 : Blo 1488064 12889813 := bbase (se 7 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 12889813 = 302105) (by norm_num)
theorem B5025509 : Blo 1488064 5025509 := bbase (se 4 (by rfl) ⟨471141, by rfl⟩ : syracuseStep 5025509 = 942283) (by norm_num)
theorem B1674985 : Blo 1488064 1674985 := bbase (se 2 (by rfl) ⟨628119, by rfl⟩ : syracuseStep 1674985 = 1256239) (by norm_num)
theorem B3018485 : Blo 1488064 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B1675021 : Blo 1488064 1675021 := bbase (se 3 (by rfl) ⟨314066, by rfl⟩ : syracuseStep 1675021 = 628133) (by norm_num)
theorem B4239125 : Blo 1488064 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B2232101 : Blo 1488064 2232101 := bbase (se 4 (by rfl) ⟨209259, by rfl⟩ : syracuseStep 2232101 = 418519) (by norm_num)
theorem B1675057 : Blo 1488064 1675057 := bbase (se 2 (by rfl) ⟨628146, by rfl⟩ : syracuseStep 1675057 = 1256293) (by norm_num)
theorem B4525877 : Blo 1488064 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B2232125 : Blo 1488064 2232125 := bbase (se 3 (by rfl) ⟨418523, by rfl⟩ : syracuseStep 2232125 = 837047) (by norm_num)
theorem B6041413 : Blo 1488064 6041413 := bbase (se 4 (by rfl) ⟨566382, by rfl⟩ : syracuseStep 6041413 = 1132765) (by norm_num)
theorem B2232149 : Blo 1488064 2232149 := bbase (se 9 (by rfl) ⟨6539, by rfl⟩ : syracuseStep 2232149 = 13079) (by norm_num)
theorem B1675093 : Blo 1488064 1675093 := bbase (se 9 (by rfl) ⟨4907, by rfl⟩ : syracuseStep 1675093 = 9815) (by norm_num)
theorem B2232173 : Blo 1488064 2232173 := bbase (se 3 (by rfl) ⟨418532, by rfl⟩ : syracuseStep 2232173 = 837065) (by norm_num)
theorem B1675129 : Blo 1488064 1675129 := bbase (se 2 (by rfl) ⟨628173, by rfl⟩ : syracuseStep 1675129 = 1256347) (by norm_num)
theorem B2232197 : Blo 1488064 2232197 := bbase (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) (by norm_num)
theorem B7540613 : Blo 1488064 7540613 := bbase (se 4 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 7540613 = 1413865) (by norm_num)
theorem B6123413 : Blo 1488064 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2232221 : Blo 1488064 2232221 := bbase (se 3 (by rfl) ⟨418541, by rfl⟩ : syracuseStep 2232221 = 837083) (by norm_num)
theorem B1675165 : Blo 1488064 1675165 := bbase (se 3 (by rfl) ⟨314093, by rfl⟩ : syracuseStep 1675165 = 628187) (by norm_num)
theorem B2232245 : Blo 1488064 2232245 := bbase (se 5 (by rfl) ⟨104636, by rfl⟩ : syracuseStep 2232245 = 209273) (by norm_num)
theorem B3821501 : Blo 1488064 3821501 := bbase (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) (by norm_num)
theorem B1789885 : Blo 1488064 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B1675201 : Blo 1488064 1675201 := bbase (se 2 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 1675201 = 1256401) (by norm_num)
theorem B2232269 : Blo 1488064 2232269 := bbase (se 3 (by rfl) ⟨418550, by rfl⟩ : syracuseStep 2232269 = 837101) (by norm_num)
theorem B4239317 : Blo 1488064 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B2232293 : Blo 1488064 2232293 := bbase (se 4 (by rfl) ⟨209277, by rfl⟩ : syracuseStep 2232293 = 418555) (by norm_num)
theorem B1675237 : Blo 1488064 1675237 := bbase (se 4 (by rfl) ⟨157053, by rfl⟩ : syracuseStep 1675237 = 314107) (by norm_num)
theorem B8482805 : Blo 1488064 8482805 := bbase (se 5 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 8482805 = 795263) (by norm_num)
theorem B2232317 : Blo 1488064 2232317 := bbase (se 3 (by rfl) ⟨418559, by rfl⟩ : syracuseStep 2232317 = 837119) (by norm_num)
theorem B1789957 : Blo 1488064 1789957 := bbase (se 4 (by rfl) ⟨167808, by rfl⟩ : syracuseStep 1789957 = 335617) (by norm_num)
theorem B1675273 : Blo 1488064 1675273 := bbase (se 2 (by rfl) ⟨628227, by rfl⟩ : syracuseStep 1675273 = 1256455) (by norm_num)
theorem B2232341 : Blo 1488064 2232341 := bbase (se 6 (by rfl) ⟨52320, by rfl⟩ : syracuseStep 2232341 = 104641) (by norm_num)
theorem B2232365 : Blo 1488064 2232365 := bbase (se 3 (by rfl) ⟨418568, by rfl⟩ : syracuseStep 2232365 = 837137) (by norm_num)
theorem B1675309 : Blo 1488064 1675309 := bbase (se 3 (by rfl) ⟨314120, by rfl⟩ : syracuseStep 1675309 = 628241) (by norm_num)
theorem B1863745 : Blo 1488064 1863745 := bbase (se 2 (by rfl) ⟨698904, by rfl⟩ : syracuseStep 1863745 = 1397809) (by norm_num)
theorem B2232389 : Blo 1488064 2232389 := bbase (se 4 (by rfl) ⟨209286, by rfl⟩ : syracuseStep 2232389 = 418573) (by norm_num)
theorem B1675345 : Blo 1488064 1675345 := bbase (se 2 (by rfl) ⟨628254, by rfl⟩ : syracuseStep 1675345 = 1256509) (by norm_num)
theorem B5656661 : Blo 1488064 5656661 := bbase (se 8 (by rfl) ⟨33144, by rfl⟩ : syracuseStep 5656661 = 66289) (by norm_num)
theorem B2986069 : Blo 1488064 2986069 := bbase (se 8 (by rfl) ⟨17496, by rfl⟩ : syracuseStep 2986069 = 34993) (by norm_num)
theorem B6451285 : Blo 1488064 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B2232413 : Blo 1488064 2232413 := bbase (se 3 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 2232413 = 837155) (by norm_num)
theorem B2232437 : Blo 1488064 2232437 := bbase (se 5 (by rfl) ⟨104645, by rfl⟩ : syracuseStep 2232437 = 209291) (by norm_num)
theorem B1675381 : Blo 1488064 1675381 := bbase (se 5 (by rfl) ⟨78533, by rfl⟩ : syracuseStep 1675381 = 157067) (by norm_num)
theorem B10735733 : Blo 1488064 10735733 := bbase (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) (by norm_num)
theorem B2232461 : Blo 1488064 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B5025941 : Blo 1488064 5025941 := bbase (se 6 (by rfl) ⟨117795, by rfl⟩ : syracuseStep 5025941 = 235591) (by norm_num)
theorem B1675417 : Blo 1488064 1675417 := bbase (se 2 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 1675417 = 1256563) (by norm_num)
theorem B2232485 : Blo 1488064 2232485 := bbase (se 4 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 2232485 = 418591) (by norm_num)
theorem B2232509 : Blo 1488064 2232509 := bbase (se 3 (by rfl) ⟨418595, by rfl⟩ : syracuseStep 2232509 = 837191) (by norm_num)
theorem B1675453 : Blo 1488064 1675453 := bbase (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) (by norm_num)
theorem B3395789 : Blo 1488064 3395789 := bbase (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) (by norm_num)
theorem B2232533 : Blo 1488064 2232533 := bbase (se 7 (by rfl) ⟨26162, by rfl⟩ : syracuseStep 2232533 = 52325) (by norm_num)
theorem B15282389 : Blo 1488064 15282389 := bbase (se 7 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 15282389 = 358181) (by norm_num)
theorem B1675489 : Blo 1488064 1675489 := bbase (se 2 (by rfl) ⟨628308, by rfl⟩ : syracuseStep 1675489 = 1256617) (by norm_num)
theorem B2232557 : Blo 1488064 2232557 := bbase (se 3 (by rfl) ⟨418604, by rfl⟩ : syracuseStep 2232557 = 837209) (by norm_num)
theorem B2232581 : Blo 1488064 2232581 := bbase (se 4 (by rfl) ⟨209304, by rfl⟩ : syracuseStep 2232581 = 418609) (by norm_num)
theorem B1675525 : Blo 1488064 1675525 := bbase (se 4 (by rfl) ⟨157080, by rfl⟩ : syracuseStep 1675525 = 314161) (by norm_num)
theorem B2232605 : Blo 1488064 2232605 := bbase (se 3 (by rfl) ⟨418613, by rfl⟩ : syracuseStep 2232605 = 837227) (by norm_num)
theorem B1675561 : Blo 1488064 1675561 := bbase (se 2 (by rfl) ⟨628335, by rfl⟩ : syracuseStep 1675561 = 1256671) (by norm_num)
theorem B2232629 : Blo 1488064 2232629 := bbase (se 5 (by rfl) ⟨104654, by rfl⟩ : syracuseStep 2232629 = 209309) (by norm_num)
theorem B2232653 : Blo 1488064 2232653 := bbase (se 3 (by rfl) ⟨418622, by rfl⟩ : syracuseStep 2232653 = 837245) (by norm_num)
theorem B1675597 : Blo 1488064 1675597 := bbase (se 3 (by rfl) ⟨314174, by rfl⟩ : syracuseStep 1675597 = 628349) (by norm_num)
theorem B2265421 : Blo 1488064 2265421 := bbase (se 3 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 2265421 = 849533) (by norm_num)
theorem B2232677 : Blo 1488064 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B1675633 : Blo 1488064 1675633 := bbase (se 2 (by rfl) ⟨628362, by rfl⟩ : syracuseStep 1675633 = 1256725) (by norm_num)
theorem B5656949 : Blo 1488064 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B2511229 : Blo 1488064 2511229 := bbase (se 3 (by rfl) ⟨470855, by rfl⟩ : syracuseStep 2511229 = 941711) (by norm_num)
theorem B2232701 : Blo 1488064 2232701 := bbase (se 3 (by rfl) ⟨418631, by rfl⟩ : syracuseStep 2232701 = 837263) (by norm_num)
theorem B2232725 : Blo 1488064 2232725 := bbase (se 6 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 2232725 = 104659) (by norm_num)
theorem B1675669 : Blo 1488064 1675669 := bbase (se 6 (by rfl) ⟨39273, by rfl⟩ : syracuseStep 1675669 = 78547) (by norm_num)
theorem B2232749 : Blo 1488064 2232749 := bbase (se 3 (by rfl) ⟨418640, by rfl⟩ : syracuseStep 2232749 = 837281) (by norm_num)
theorem B1675705 : Blo 1488064 1675705 := bbase (se 2 (by rfl) ⟨628389, by rfl⟩ : syracuseStep 1675705 = 1256779) (by norm_num)
theorem B2232773 : Blo 1488064 2232773 := bbase (se 4 (by rfl) ⟨209322, by rfl⟩ : syracuseStep 2232773 = 418645) (by norm_num)
theorem B2511317 : Blo 1488064 2511317 := bbase (se 7 (by rfl) ⟨29429, by rfl⟩ : syracuseStep 2511317 = 58859) (by norm_num)
theorem B2232797 : Blo 1488064 2232797 := bbase (se 3 (by rfl) ⟨418649, by rfl⟩ : syracuseStep 2232797 = 837299) (by norm_num)
theorem B1675741 : Blo 1488064 1675741 := bbase (se 3 (by rfl) ⟨314201, by rfl⟩ : syracuseStep 1675741 = 628403) (by norm_num)
theorem B6361573 : Blo 1488064 6361573 := bbase (se 4 (by rfl) ⟨596397, by rfl⟩ : syracuseStep 6361573 = 1192795) (by norm_num)
theorem B2232821 : Blo 1488064 2232821 := bbase (se 5 (by rfl) ⟨104663, by rfl⟩ : syracuseStep 2232821 = 209327) (by norm_num)
theorem B1675777 : Blo 1488064 1675777 := bbase (se 2 (by rfl) ⟨628416, by rfl⟩ : syracuseStep 1675777 = 1256833) (by norm_num)
theorem B2232845 : Blo 1488064 2232845 := bbase (se 3 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 2232845 = 837317) (by norm_num)
theorem B2232869 : Blo 1488064 2232869 := bbase (se 4 (by rfl) ⟨209331, by rfl⟩ : syracuseStep 2232869 = 418663) (by norm_num)
theorem B1675813 : Blo 1488064 1675813 := bbase (se 4 (by rfl) ⟨157107, by rfl⟩ : syracuseStep 1675813 = 314215) (by norm_num)
theorem B4026917 : Blo 1488064 4026917 := bbase (se 4 (by rfl) ⟨377523, by rfl⟩ : syracuseStep 4026917 = 755047) (by norm_num)
theorem B2232893 : Blo 1488064 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B5026373 : Blo 1488064 5026373 := bbase (se 4 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 5026373 = 942445) (by norm_num)
theorem B1675849 : Blo 1488064 1675849 := bbase (se 2 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 1675849 = 1256887) (by norm_num)
theorem B2511445 : Blo 1488064 2511445 := bbase (se 8 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 2511445 = 29431) (by norm_num)
theorem B2232917 : Blo 1488064 2232917 := bbase (se 8 (by rfl) ⟨13083, by rfl⟩ : syracuseStep 2232917 = 26167) (by norm_num)
theorem B7156309 : Blo 1488064 7156309 := bbase (se 8 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 7156309 = 83863) (by norm_num)
theorem B2863717 : Blo 1488064 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B2232941 : Blo 1488064 2232941 := bbase (se 3 (by rfl) ⟨418676, by rfl⟩ : syracuseStep 2232941 = 837353) (by norm_num)
theorem B1675885 : Blo 1488064 1675885 := bbase (se 3 (by rfl) ⟨314228, by rfl⟩ : syracuseStep 1675885 = 628457) (by norm_num)
theorem B2232965 : Blo 1488064 2232965 := bbase (se 4 (by rfl) ⟨209340, by rfl⟩ : syracuseStep 2232965 = 418681) (by norm_num)
theorem B1675921 : Blo 1488064 1675921 := bbase (se 2 (by rfl) ⟨628470, by rfl⟩ : syracuseStep 1675921 = 1256941) (by norm_num)
theorem B2232989 : Blo 1488064 2232989 := bbase (se 3 (by rfl) ⟨418685, by rfl⟩ : syracuseStep 2232989 = 837371) (by norm_num)
theorem B2511533 : Blo 1488064 2511533 := bbase (se 3 (by rfl) ⟨470912, by rfl⟩ : syracuseStep 2511533 = 941825) (by norm_num)
theorem B2233013 : Blo 1488064 2233013 := bbase (se 5 (by rfl) ⟨104672, by rfl⟩ : syracuseStep 2233013 = 209345) (by norm_num)
theorem B1675957 : Blo 1488064 1675957 := bbase (se 5 (by rfl) ⟨78560, by rfl⟩ : syracuseStep 1675957 = 157121) (by norm_num)
theorem B2233037 : Blo 1488064 2233037 := bbase (se 3 (by rfl) ⟨418694, by rfl⟩ : syracuseStep 2233037 = 837389) (by norm_num)
theorem B1675993 : Blo 1488064 1675993 := bbase (se 2 (by rfl) ⟨628497, by rfl⟩ : syracuseStep 1675993 = 1256995) (by norm_num)
theorem B2233061 : Blo 1488064 2233061 := bbase (se 4 (by rfl) ⟨209349, by rfl⟩ : syracuseStep 2233061 = 418699) (by norm_num)
theorem B2233085 : Blo 1488064 2233085 := bbase (se 3 (by rfl) ⟨418703, by rfl⟩ : syracuseStep 2233085 = 837407) (by norm_num)
theorem B1676029 : Blo 1488064 1676029 := bbase (se 3 (by rfl) ⟨314255, by rfl⟩ : syracuseStep 1676029 = 628511) (by norm_num)
theorem B2233109 : Blo 1488064 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1676065 : Blo 1488064 1676065 := bbase (se 2 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 1676065 = 1257049) (by norm_num)
theorem B2511661 : Blo 1488064 2511661 := bbase (se 3 (by rfl) ⟨470936, by rfl⟩ : syracuseStep 2511661 = 941873) (by norm_num)
theorem B2233133 : Blo 1488064 2233133 := bbase (se 3 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 2233133 = 837425) (by norm_num)
theorem B2233157 : Blo 1488064 2233157 := bbase (se 4 (by rfl) ⟨209358, by rfl⟩ : syracuseStep 2233157 = 418717) (by norm_num)
theorem B1676101 : Blo 1488064 1676101 := bbase (se 4 (by rfl) ⟨157134, by rfl⟩ : syracuseStep 1676101 = 314269) (by norm_num)
theorem B2233181 : Blo 1488064 2233181 := bbase (se 3 (by rfl) ⟨418721, by rfl⟩ : syracuseStep 2233181 = 837443) (by norm_num)
theorem B1676137 : Blo 1488064 1676137 := bbase (se 2 (by rfl) ⟨628551, by rfl⟩ : syracuseStep 1676137 = 1257103) (by norm_num)
theorem B2233205 : Blo 1488064 2233205 := bbase (se 5 (by rfl) ⟨104681, by rfl⟩ : syracuseStep 2233205 = 209363) (by norm_num)
theorem B2511749 : Blo 1488064 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B2233229 : Blo 1488064 2233229 := bbase (se 3 (by rfl) ⟨418730, by rfl⟩ : syracuseStep 2233229 = 837461) (by norm_num)
theorem B1676173 : Blo 1488064 1676173 := bbase (se 3 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 1676173 = 628565) (by norm_num)
theorem B2233253 : Blo 1488064 2233253 := bbase (se 4 (by rfl) ⟨209367, by rfl⟩ : syracuseStep 2233253 = 418735) (by norm_num)
theorem B3019685 : Blo 1488064 3019685 := bbase (se 4 (by rfl) ⟨283095, by rfl⟩ : syracuseStep 3019685 = 566191) (by norm_num)
theorem B1676209 : Blo 1488064 1676209 := bbase (se 2 (by rfl) ⟨628578, by rfl⟩ : syracuseStep 1676209 = 1257157) (by norm_num)
theorem B4240309 : Blo 1488064 4240309 := bbase (se 5 (by rfl) ⟨198764, by rfl⟩ : syracuseStep 4240309 = 397529) (by norm_num)
theorem B2233277 : Blo 1488064 2233277 := bbase (se 3 (by rfl) ⟨418739, by rfl⟩ : syracuseStep 2233277 = 837479) (by norm_num)
theorem B3019717 : Blo 1488064 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B2233301 : Blo 1488064 2233301 := bbase (se 7 (by rfl) ⟨26171, by rfl⟩ : syracuseStep 2233301 = 52343) (by norm_num)
theorem B1676245 : Blo 1488064 1676245 := bbase (se 7 (by rfl) ⟨19643, by rfl⟩ : syracuseStep 1676245 = 39287) (by norm_num)
theorem B2233325 : Blo 1488064 2233325 := bbase (se 3 (by rfl) ⟨418748, by rfl⟩ : syracuseStep 2233325 = 837497) (by norm_num)
theorem B5026805 : Blo 1488064 5026805 := bbase (se 5 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 5026805 = 471263) (by norm_num)
theorem B1676281 : Blo 1488064 1676281 := bbase (se 2 (by rfl) ⟨628605, by rfl⟩ : syracuseStep 1676281 = 1257211) (by norm_num)
theorem B2511877 : Blo 1488064 2511877 := bbase (se 4 (by rfl) ⟨235488, by rfl⟩ : syracuseStep 2511877 = 470977) (by norm_num)
theorem B2233349 : Blo 1488064 2233349 := bbase (se 4 (by rfl) ⟨209376, by rfl⟩ : syracuseStep 2233349 = 418753) (by norm_num)
theorem B2233373 : Blo 1488064 2233373 := bbase (se 3 (by rfl) ⟨418757, by rfl⟩ : syracuseStep 2233373 = 837515) (by norm_num)
theorem B1676317 : Blo 1488064 1676317 := bbase (se 3 (by rfl) ⟨314309, by rfl⟩ : syracuseStep 1676317 = 628619) (by norm_num)
theorem B2233397 : Blo 1488064 2233397 := bbase (se 5 (by rfl) ⟨104690, by rfl⟩ : syracuseStep 2233397 = 209381) (by norm_num)
theorem B2233421 : Blo 1488064 2233421 := bbase (se 3 (by rfl) ⟨418766, by rfl⟩ : syracuseStep 2233421 = 837533) (by norm_num)
theorem B2511965 : Blo 1488064 2511965 := bbase (se 3 (by rfl) ⟨470993, by rfl⟩ : syracuseStep 2511965 = 941987) (by norm_num)
theorem B2233445 : Blo 1488064 2233445 := bbase (se 4 (by rfl) ⟨209385, by rfl⟩ : syracuseStep 2233445 = 418771) (by norm_num)
theorem B2233469 : Blo 1488064 2233469 := bbase (se 3 (by rfl) ⟨418775, by rfl⟩ : syracuseStep 2233469 = 837551) (by norm_num)
theorem B2233493 : Blo 1488064 2233493 := bbase (se 6 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 2233493 = 104695) (by norm_num)
theorem B7541909 : Blo 1488064 7541909 := bbase (se 6 (by rfl) ⟨176763, by rfl⟩ : syracuseStep 7541909 = 353527) (by norm_num)
theorem B2233517 : Blo 1488064 2233517 := bbase (se 3 (by rfl) ⟨418784, by rfl⟩ : syracuseStep 2233517 = 837569) (by norm_num)
theorem B2233541 : Blo 1488064 2233541 := bbase (se 4 (by rfl) ⟨209394, by rfl⟩ : syracuseStep 2233541 = 418789) (by norm_num)
theorem B4773077 : Blo 1488064 4773077 := bbase (se 7 (by rfl) ⟨55934, by rfl⟩ : syracuseStep 4773077 = 111869) (by norm_num)
theorem B2512093 : Blo 1488064 2512093 := bbase (se 3 (by rfl) ⟨471017, by rfl⟩ : syracuseStep 2512093 = 942035) (by norm_num)
theorem B2233565 : Blo 1488064 2233565 := bbase (se 3 (by rfl) ⟨418793, by rfl⟩ : syracuseStep 2233565 = 837587) (by norm_num)
theorem B2233589 : Blo 1488064 2233589 := bbase (se 5 (by rfl) ⟨104699, by rfl⟩ : syracuseStep 2233589 = 209399) (by norm_num)
theorem B2233613 : Blo 1488064 2233613 := bbase (se 3 (by rfl) ⟨418802, by rfl⟩ : syracuseStep 2233613 = 837605) (by norm_num)
theorem B1611037 : Blo 1488064 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B2233637 : Blo 1488064 2233637 := bbase (se 4 (by rfl) ⟨209403, by rfl⟩ : syracuseStep 2233637 = 418807) (by norm_num)
theorem B2512181 : Blo 1488064 2512181 := bbase (se 5 (by rfl) ⟨117758, by rfl⟩ : syracuseStep 2512181 = 235517) (by norm_num)
theorem B2233661 : Blo 1488064 2233661 := bbase (se 3 (by rfl) ⟨418811, by rfl⟩ : syracuseStep 2233661 = 837623) (by norm_num)
theorem B2233685 : Blo 1488064 2233685 := bbase (se 14 (by rfl) ⟨204, by rfl⟩ : syracuseStep 2233685 = 409) (by norm_num)
theorem B2233709 : Blo 1488064 2233709 := bbase (se 3 (by rfl) ⟨418820, by rfl⟩ : syracuseStep 2233709 = 837641) (by norm_num)
theorem B2233733 : Blo 1488064 2233733 := bbase (se 4 (by rfl) ⟨209412, by rfl⟩ : syracuseStep 2233733 = 418825) (by norm_num)
theorem B2119061 : Blo 1488064 2119061 := bbase (se 6 (by rfl) ⟨49665, by rfl⟩ : syracuseStep 2119061 = 99331) (by norm_num)
theorem B2233757 : Blo 1488064 2233757 := bbase (se 3 (by rfl) ⟨418829, by rfl⟩ : syracuseStep 2233757 = 837659) (by norm_num)
theorem B5027237 : Blo 1488064 5027237 := bbase (se 4 (by rfl) ⟨471303, by rfl⟩ : syracuseStep 5027237 = 942607) (by norm_num)
theorem B2512309 : Blo 1488064 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B2233781 : Blo 1488064 2233781 := bbase (se 5 (by rfl) ⟨104708, by rfl⟩ : syracuseStep 2233781 = 209417) (by norm_num)
theorem B2012621 : Blo 1488064 2012621 := bbase (se 3 (by rfl) ⟨377366, by rfl⟩ : syracuseStep 2012621 = 754733) (by norm_num)
theorem B2233805 : Blo 1488064 2233805 := bbase (se 3 (by rfl) ⟨418838, by rfl⟩ : syracuseStep 2233805 = 837677) (by norm_num)
theorem B2233829 : Blo 1488064 2233829 := bbase (se 4 (by rfl) ⟨209421, by rfl⟩ : syracuseStep 2233829 = 418843) (by norm_num)
theorem B2233853 : Blo 1488064 2233853 := bbase (se 3 (by rfl) ⟨418847, by rfl⟩ : syracuseStep 2233853 = 837695) (by norm_num)
theorem B2512397 : Blo 1488064 2512397 := bbase (se 3 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 2512397 = 942149) (by norm_num)
theorem B2233877 : Blo 1488064 2233877 := bbase (se 6 (by rfl) ⟨52356, by rfl⟩ : syracuseStep 2233877 = 104713) (by norm_num)
theorem B2233901 : Blo 1488064 2233901 := bbase (se 3 (by rfl) ⟨418856, by rfl⟩ : syracuseStep 2233901 = 837713) (by norm_num)
theorem B7534133 : Blo 1488064 7534133 := bbase (se 5 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 7534133 = 706325) (by norm_num)
theorem B2233925 : Blo 1488064 2233925 := bbase (se 4 (by rfl) ⟨209430, by rfl⟩ : syracuseStep 2233925 = 418861) (by norm_num)
theorem B11310677 : Blo 1488064 11310677 := bbase (se 8 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 11310677 = 132547) (by norm_num)
theorem B2233949 : Blo 1488064 2233949 := bbase (se 3 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 2233949 = 837731) (by norm_num)
theorem B2233973 : Blo 1488064 2233973 := bbase (se 5 (by rfl) ⟨104717, by rfl⟩ : syracuseStep 2233973 = 209435) (by norm_num)
theorem B2512525 : Blo 1488064 2512525 := bbase (se 3 (by rfl) ⟨471098, by rfl⟩ : syracuseStep 2512525 = 942197) (by norm_num)
theorem B2233997 : Blo 1488064 2233997 := bbase (se 3 (by rfl) ⟨418874, by rfl⟩ : syracuseStep 2233997 = 837749) (by norm_num)
theorem B2234021 : Blo 1488064 2234021 := bbase (se 4 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 2234021 = 418879) (by norm_num)
theorem B2234045 : Blo 1488064 2234045 := bbase (se 3 (by rfl) ⟨418883, by rfl⟩ : syracuseStep 2234045 = 837767) (by norm_num)
theorem B2234069 : Blo 1488064 2234069 := bbase (se 7 (by rfl) ⟨26180, by rfl⟩ : syracuseStep 2234069 = 52361) (by norm_num)
theorem B3348197 : Blo 1488064 3348197 := bbase (se 4 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 3348197 = 627787) (by norm_num)
theorem B5093093 : Blo 1488064 5093093 := bbase (se 4 (by rfl) ⟨477477, by rfl⟩ : syracuseStep 5093093 = 954955) (by norm_num)
theorem B2512613 : Blo 1488064 2512613 := bbase (se 4 (by rfl) ⟨235557, by rfl⟩ : syracuseStep 2512613 = 471115) (by norm_num)
theorem B2234093 : Blo 1488064 2234093 := bbase (se 3 (by rfl) ⟨418892, by rfl⟩ : syracuseStep 2234093 = 837785) (by norm_num)
theorem B2234117 : Blo 1488064 2234117 := bbase (se 4 (by rfl) ⟨209448, by rfl⟩ : syracuseStep 2234117 = 418897) (by norm_num)
theorem B2234141 : Blo 1488064 2234141 := bbase (se 3 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 2234141 = 837803) (by norm_num)
theorem B3348269 : Blo 1488064 3348269 := bbase (se 3 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 3348269 = 1255601) (by norm_num)
theorem B2234165 : Blo 1488064 2234165 := bbase (se 5 (by rfl) ⟨104726, by rfl⟩ : syracuseStep 2234165 = 209453) (by norm_num)
theorem B2234189 : Blo 1488064 2234189 := bbase (se 3 (by rfl) ⟨418910, by rfl⟩ : syracuseStep 2234189 = 837821) (by norm_num)
theorem B5027669 : Blo 1488064 5027669 := bbase (se 9 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 5027669 = 29459) (by norm_num)
theorem B3577693 : Blo 1488064 3577693 := bbase (se 3 (by rfl) ⟨670817, by rfl⟩ : syracuseStep 3577693 = 1341635) (by norm_num)
theorem B2512741 : Blo 1488064 2512741 := bbase (se 4 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 2512741 = 471139) (by norm_num)
theorem B2234213 : Blo 1488064 2234213 := bbase (se 4 (by rfl) ⟨209457, by rfl⟩ : syracuseStep 2234213 = 418915) (by norm_num)
theorem B3348341 : Blo 1488064 3348341 := bbase (se 5 (by rfl) ⟨156953, by rfl⟩ : syracuseStep 3348341 = 313907) (by norm_num)
theorem B2234237 : Blo 1488064 2234237 := bbase (se 3 (by rfl) ⟨418919, by rfl⟩ : syracuseStep 2234237 = 837839) (by norm_num)
theorem B2234261 : Blo 1488064 2234261 := bbase (se 6 (by rfl) ⟨52365, by rfl⟩ : syracuseStep 2234261 = 104731) (by norm_num)
theorem B2234285 : Blo 1488064 2234285 := bbase (se 3 (by rfl) ⟨418928, by rfl⟩ : syracuseStep 2234285 = 837857) (by norm_num)
theorem B5650357 : Blo 1488064 5650357 := bbase (se 5 (by rfl) ⟨264860, by rfl⟩ : syracuseStep 5650357 = 529721) (by norm_num)
theorem B3348413 : Blo 1488064 3348413 := bbase (se 3 (by rfl) ⟨627827, by rfl⟩ : syracuseStep 3348413 = 1255655) (by norm_num)
theorem B2119613 : Blo 1488064 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B2512829 : Blo 1488064 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B2234309 : Blo 1488064 2234309 := bbase (se 4 (by rfl) ⟨209466, by rfl⟩ : syracuseStep 2234309 = 418933) (by norm_num)
theorem B2234333 : Blo 1488064 2234333 := bbase (se 3 (by rfl) ⟨418937, by rfl⟩ : syracuseStep 2234333 = 837875) (by norm_num)
theorem B6789109 : Blo 1488064 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B11302901 : Blo 1488064 11302901 := bbase (se 5 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 11302901 = 1059647) (by norm_num)
theorem B2234357 : Blo 1488064 2234357 := bbase (se 5 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 2234357 = 209471) (by norm_num)
theorem B3397621 : Blo 1488064 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B3348485 : Blo 1488064 3348485 := bbase (se 4 (by rfl) ⟨313920, by rfl⟩ : syracuseStep 3348485 = 627841) (by norm_num)
theorem B4241413 : Blo 1488064 4241413 := bbase (se 4 (by rfl) ⟨397632, by rfl⟩ : syracuseStep 4241413 = 795265) (by norm_num)
theorem B2234381 : Blo 1488064 2234381 := bbase (se 3 (by rfl) ⟨418946, by rfl⟩ : syracuseStep 2234381 = 837893) (by norm_num)
theorem B2234405 : Blo 1488064 2234405 := bbase (se 4 (by rfl) ⟨209475, by rfl⟩ : syracuseStep 2234405 = 418951) (by norm_num)
theorem B2512957 : Blo 1488064 2512957 := bbase (se 3 (by rfl) ⟨471179, by rfl⟩ : syracuseStep 2512957 = 942359) (by norm_num)
theorem B2234429 : Blo 1488064 2234429 := bbase (se 3 (by rfl) ⟨418955, by rfl⟩ : syracuseStep 2234429 = 837911) (by norm_num)
theorem B3577925 : Blo 1488064 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B3348557 : Blo 1488064 3348557 := bbase (se 3 (by rfl) ⟨627854, by rfl⟩ : syracuseStep 3348557 = 1255709) (by norm_num)
theorem B2234453 : Blo 1488064 2234453 := bbase (se 8 (by rfl) ⟨13092, by rfl⟩ : syracuseStep 2234453 = 26185) (by norm_num)
theorem B2234477 : Blo 1488064 2234477 := bbase (se 3 (by rfl) ⟨418964, by rfl⟩ : syracuseStep 2234477 = 837929) (by norm_num)
theorem B2234501 : Blo 1488064 2234501 := bbase (se 4 (by rfl) ⟨209484, by rfl⟩ : syracuseStep 2234501 = 418969) (by norm_num)
theorem B9664661 : Blo 1488064 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B3348629 : Blo 1488064 3348629 := bbase (se 6 (by rfl) ⟨78483, by rfl⟩ : syracuseStep 3348629 = 156967) (by norm_num)
theorem B2513045 : Blo 1488064 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B8485013 : Blo 1488064 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B2234525 : Blo 1488064 2234525 := bbase (se 3 (by rfl) ⟨418973, by rfl⟩ : syracuseStep 2234525 = 837947) (by norm_num)
theorem B2234549 : Blo 1488064 2234549 := bbase (se 5 (by rfl) ⟨104744, by rfl⟩ : syracuseStep 2234549 = 209489) (by norm_num)
theorem B2234573 : Blo 1488064 2234573 := bbase (se 3 (by rfl) ⟨418982, by rfl⟩ : syracuseStep 2234573 = 837965) (by norm_num)
theorem B3578069 : Blo 1488064 3578069 := bbase (se 7 (by rfl) ⟨41930, by rfl⟩ : syracuseStep 3578069 = 83861) (by norm_num)
theorem B3348701 : Blo 1488064 3348701 := bbase (se 3 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 3348701 = 1255763) (by norm_num)
theorem B1611997 : Blo 1488064 1611997 := bbase (se 3 (by rfl) ⟨302249, by rfl⟩ : syracuseStep 1611997 = 604499) (by norm_num)
theorem B5650661 : Blo 1488064 5650661 := bbase (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) (by norm_num)
theorem B2234597 : Blo 1488064 2234597 := bbase (se 4 (by rfl) ⟨209493, by rfl⟩ : syracuseStep 2234597 = 418987) (by norm_num)
theorem B2234621 : Blo 1488064 2234621 := bbase (se 3 (by rfl) ⟨418991, by rfl⟩ : syracuseStep 2234621 = 837983) (by norm_num)
theorem B2177285 : Blo 1488064 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B5028101 : Blo 1488064 5028101 := bbase (se 4 (by rfl) ⟨471384, by rfl⟩ : syracuseStep 5028101 = 942769) (by norm_num)
theorem B2513173 : Blo 1488064 2513173 := bbase (se 6 (by rfl) ⟨58902, by rfl⟩ : syracuseStep 2513173 = 117805) (by norm_num)
theorem B2234645 : Blo 1488064 2234645 := bbase (se 6 (by rfl) ⟨52374, by rfl⟩ : syracuseStep 2234645 = 104749) (by norm_num)
theorem B3348773 : Blo 1488064 3348773 := bbase (se 4 (by rfl) ⟨313947, by rfl⟩ : syracuseStep 3348773 = 627895) (by norm_num)
theorem B2234669 : Blo 1488064 2234669 := bbase (se 3 (by rfl) ⟨419000, by rfl⟩ : syracuseStep 2234669 = 838001) (by norm_num)
theorem B2234693 : Blo 1488064 2234693 := bbase (se 4 (by rfl) ⟨209502, by rfl⟩ : syracuseStep 2234693 = 419005) (by norm_num)
theorem B2234717 : Blo 1488064 2234717 := bbase (se 3 (by rfl) ⟨419009, by rfl⟩ : syracuseStep 2234717 = 838019) (by norm_num)
theorem B3348845 : Blo 1488064 3348845 := bbase (se 3 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 3348845 = 1255817) (by norm_num)
theorem B2513261 : Blo 1488064 2513261 := bbase (se 3 (by rfl) ⟨471236, by rfl⟩ : syracuseStep 2513261 = 942473) (by norm_num)
theorem B2234741 : Blo 1488064 2234741 := bbase (se 5 (by rfl) ⟨104753, by rfl⟩ : syracuseStep 2234741 = 209507) (by norm_num)
theorem B2234765 : Blo 1488064 2234765 := bbase (se 3 (by rfl) ⟨419018, by rfl⟩ : syracuseStep 2234765 = 838037) (by norm_num)
theorem B2234789 : Blo 1488064 2234789 := bbase (se 4 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 2234789 = 419023) (by norm_num)
theorem B7543205 : Blo 1488064 7543205 := bbase (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) (by norm_num)
theorem B3348917 : Blo 1488064 3348917 := bbase (se 5 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 3348917 = 313961) (by norm_num)
theorem B2234813 : Blo 1488064 2234813 := bbase (se 3 (by rfl) ⟨419027, by rfl⟩ : syracuseStep 2234813 = 838055) (by norm_num)
theorem B3578309 : Blo 1488064 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B3766733 : Blo 1488064 3766733 := bbase (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) (by norm_num)
theorem B2234837 : Blo 1488064 2234837 := bbase (se 7 (by rfl) ⟨26189, by rfl⟩ : syracuseStep 2234837 = 52379) (by norm_num)
theorem B2513389 : Blo 1488064 2513389 := bbase (se 3 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 2513389 = 942521) (by norm_num)
theorem B2234861 : Blo 1488064 2234861 := bbase (se 3 (by rfl) ⟨419036, by rfl⟩ : syracuseStep 2234861 = 838073) (by norm_num)
theorem B3348989 : Blo 1488064 3348989 := bbase (se 3 (by rfl) ⟨627935, by rfl⟩ : syracuseStep 3348989 = 1255871) (by norm_num)
theorem B2234885 : Blo 1488064 2234885 := bbase (se 4 (by rfl) ⟨209520, by rfl⟩ : syracuseStep 2234885 = 419041) (by norm_num)
theorem B2234909 : Blo 1488064 2234909 := bbase (se 3 (by rfl) ⟨419045, by rfl⟩ : syracuseStep 2234909 = 838091) (by norm_num)
theorem B2234933 : Blo 1488064 2234933 := bbase (se 5 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 2234933 = 209525) (by norm_num)
theorem B3349061 : Blo 1488064 3349061 := bbase (se 4 (by rfl) ⟨313974, by rfl⟩ : syracuseStep 3349061 = 627949) (by norm_num)
theorem B2546245 : Blo 1488064 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B2513477 : Blo 1488064 2513477 := bbase (se 4 (by rfl) ⟨235638, by rfl⟩ : syracuseStep 2513477 = 471277) (by norm_num)
theorem B2234957 : Blo 1488064 2234957 := bbase (se 3 (by rfl) ⟨419054, by rfl⟩ : syracuseStep 2234957 = 838109) (by norm_num)
theorem B2234981 : Blo 1488064 2234981 := bbase (se 4 (by rfl) ⟨209529, by rfl⟩ : syracuseStep 2234981 = 419059) (by norm_num)
theorem B2235005 : Blo 1488064 2235005 := bbase (se 3 (by rfl) ⟨419063, by rfl⟩ : syracuseStep 2235005 = 838127) (by norm_num)
theorem B3766925 : Blo 1488064 3766925 := bbase (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) (by norm_num)
theorem B3349133 : Blo 1488064 3349133 := bbase (se 3 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 3349133 = 1255925) (by norm_num)
theorem B22928021 : Blo 1488064 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B2235029 : Blo 1488064 2235029 := bbase (se 6 (by rfl) ⟨52383, by rfl⟩ : syracuseStep 2235029 = 104767) (by norm_num)
theorem B2120365 : Blo 1488064 2120365 := bbase (se 3 (by rfl) ⟨397568, by rfl⟩ : syracuseStep 2120365 = 795137) (by norm_num)
theorem B2235053 : Blo 1488064 2235053 := bbase (se 3 (by rfl) ⟨419072, by rfl⟩ : syracuseStep 2235053 = 838145) (by norm_num)
theorem B5028533 : Blo 1488064 5028533 := bbase (se 5 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 5028533 = 471425) (by norm_num)
theorem B2513605 : Blo 1488064 2513605 := bbase (se 4 (by rfl) ⟨235650, by rfl⟩ : syracuseStep 2513605 = 471301) (by norm_num)
theorem B2235077 : Blo 1488064 2235077 := bbase (se 4 (by rfl) ⟨209538, by rfl⟩ : syracuseStep 2235077 = 419077) (by norm_num)
theorem B3349205 : Blo 1488064 3349205 := bbase (se 7 (by rfl) ⟨39248, by rfl⟩ : syracuseStep 3349205 = 78497) (by norm_num)
theorem B4528885 : Blo 1488064 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B3349277 : Blo 1488064 3349277 := bbase (se 3 (by rfl) ⟨627989, by rfl⟩ : syracuseStep 3349277 = 1255979) (by norm_num)
theorem B2513693 : Blo 1488064 2513693 := bbase (se 3 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 2513693 = 942635) (by norm_num)
theorem B7535429 : Blo 1488064 7535429 := bbase (se 4 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 7535429 = 1412893) (by norm_num)
theorem B3349349 : Blo 1488064 3349349 := bbase (se 4 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 3349349 = 628003) (by norm_num)
theorem B2513821 : Blo 1488064 2513821 := bbase (se 3 (by rfl) ⟨471341, by rfl⟩ : syracuseStep 2513821 = 942683) (by norm_num)
theorem B3349421 : Blo 1488064 3349421 := bbase (se 3 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 3349421 = 1256033) (by norm_num)
theorem B3767269 : Blo 1488064 3767269 := bbase (se 4 (by rfl) ⟨353181, by rfl⟩ : syracuseStep 3767269 = 706363) (by norm_num)
theorem B3349493 : Blo 1488064 3349493 := bbase (se 5 (by rfl) ⟨157007, by rfl⟩ : syracuseStep 3349493 = 314015) (by norm_num)
theorem B2513909 : Blo 1488064 2513909 := bbase (se 5 (by rfl) ⟨117839, by rfl⟩ : syracuseStep 2513909 = 235679) (by norm_num)
theorem B3349565 : Blo 1488064 3349565 := bbase (se 3 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 3349565 = 1256087) (by norm_num)
theorem B2825293 : Blo 1488064 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B3767381 : Blo 1488064 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B5028965 : Blo 1488064 5028965 := bbase (se 4 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 5028965 = 942931) (by norm_num)
theorem B2514037 : Blo 1488064 2514037 := bbase (se 5 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 2514037 = 235691) (by norm_num)
theorem B3349637 : Blo 1488064 3349637 := bbase (se 4 (by rfl) ⟨314028, by rfl⟩ : syracuseStep 3349637 = 628057) (by norm_num)
theorem B3579077 : Blo 1488064 3579077 := bbase (se 4 (by rfl) ⟨335538, by rfl⟩ : syracuseStep 3579077 = 671077) (by norm_num)
theorem B1883341 : Blo 1488064 1883341 := bbase (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) (by norm_num)
theorem B3349709 : Blo 1488064 3349709 := bbase (se 3 (by rfl) ⟨628070, by rfl⟩ : syracuseStep 3349709 = 1256141) (by norm_num)
theorem B2514125 : Blo 1488064 2514125 := bbase (se 3 (by rfl) ⟨471398, by rfl⟩ : syracuseStep 2514125 = 942797) (by norm_num)
theorem B2825437 : Blo 1488064 2825437 := bbase (se 3 (by rfl) ⟨529769, by rfl⟩ : syracuseStep 2825437 = 1059539) (by norm_num)
theorem B6790405 : Blo 1488064 6790405 := bbase (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) (by norm_num)
theorem B3767573 : Blo 1488064 3767573 := bbase (se 6 (by rfl) ⟨88302, by rfl⟩ : syracuseStep 3767573 = 176605) (by norm_num)
theorem B3349781 : Blo 1488064 3349781 := bbase (se 6 (by rfl) ⟨78510, by rfl⟩ : syracuseStep 3349781 = 157021) (by norm_num)
theorem B9534773 : Blo 1488064 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B2514253 : Blo 1488064 2514253 := bbase (se 3 (by rfl) ⟨471422, by rfl⟩ : syracuseStep 2514253 = 942845) (by norm_num)
theorem B3349853 : Blo 1488064 3349853 := bbase (se 3 (by rfl) ⟨628097, by rfl⟩ : syracuseStep 3349853 = 1256195) (by norm_num)
theorem B1883513 : Blo 1488064 1883513 := bbase (se 2 (by rfl) ⟨706317, by rfl⟩ : syracuseStep 1883513 = 1412635) (by norm_num)
theorem B2825597 : Blo 1488064 2825597 := bbase (se 3 (by rfl) ⟨529799, by rfl⟩ : syracuseStep 2825597 = 1059599) (by norm_num)
theorem B6364565 : Blo 1488064 6364565 := bbase (se 6 (by rfl) ⟨149169, by rfl⟩ : syracuseStep 6364565 = 298339) (by norm_num)
theorem B3349925 : Blo 1488064 3349925 := bbase (se 4 (by rfl) ⟨314055, by rfl⟩ : syracuseStep 3349925 = 628111) (by norm_num)
theorem B2514341 : Blo 1488064 2514341 := bbase (se 4 (by rfl) ⟨235719, by rfl⟩ : syracuseStep 2514341 = 471439) (by norm_num)
theorem B1883569 : Blo 1488064 1883569 := bbase (se 2 (by rfl) ⟨706338, by rfl⟩ : syracuseStep 1883569 = 1412677) (by norm_num)
theorem B2121157 : Blo 1488064 2121157 := bbase (se 4 (by rfl) ⟨198858, by rfl⟩ : syracuseStep 2121157 = 397717) (by norm_num)
theorem B4242917 : Blo 1488064 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B3349997 : Blo 1488064 3349997 := bbase (se 3 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 3349997 = 1256249) (by norm_num)
theorem B2825741 : Blo 1488064 2825741 := bbase (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) (by norm_num)
theorem B1883665 : Blo 1488064 1883665 := bbase (se 2 (by rfl) ⟨706374, by rfl⟩ : syracuseStep 1883665 = 1412749) (by norm_num)
theorem B6356501 : Blo 1488064 6356501 := bbase (se 6 (by rfl) ⟨148980, by rfl⟩ : syracuseStep 6356501 = 297961) (by norm_num)
theorem B2514469 : Blo 1488064 2514469 := bbase (se 4 (by rfl) ⟨235731, by rfl⟩ : syracuseStep 2514469 = 471463) (by norm_num)
theorem B3350069 : Blo 1488064 3350069 := bbase (se 5 (by rfl) ⟨157034, by rfl⟩ : syracuseStep 3350069 = 314069) (by norm_num)
theorem B3767917 : Blo 1488064 3767917 := bbase (se 3 (by rfl) ⟨706484, by rfl⟩ : syracuseStep 3767917 = 1412969) (by norm_num)
theorem B3350141 : Blo 1488064 3350141 := bbase (se 3 (by rfl) ⟨628151, by rfl⟩ : syracuseStep 3350141 = 1256303) (by norm_num)
theorem B1883837 : Blo 1488064 1883837 := bbase (se 3 (by rfl) ⟨353219, by rfl⟩ : syracuseStep 1883837 = 706439) (by norm_num)
theorem B3350213 : Blo 1488064 3350213 := bbase (se 4 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 3350213 = 628165) (by norm_num)
theorem B55115477 : Blo 1488064 55115477 := bbase (se 7 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 55115477 = 1291769) (by norm_num)
theorem B3768029 : Blo 1488064 3768029 := bbase (se 3 (by rfl) ⟨706505, by rfl⟩ : syracuseStep 3768029 = 1413011) (by norm_num)
theorem B1883893 : Blo 1488064 1883893 := bbase (se 5 (by rfl) ⟨88307, by rfl⟩ : syracuseStep 1883893 = 176615) (by norm_num)
theorem B3350285 : Blo 1488064 3350285 := bbase (se 3 (by rfl) ⟨628178, by rfl⟩ : syracuseStep 3350285 = 1256357) (by norm_num)
theorem B2121493 : Blo 1488064 2121493 := bbase (se 6 (by rfl) ⟨49722, by rfl⟩ : syracuseStep 2121493 = 99445) (by norm_num)
theorem B2826029 : Blo 1488064 2826029 := bbase (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) (by norm_num)
theorem B6356789 : Blo 1488064 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B7151429 : Blo 1488064 7151429 := bbase (se 4 (by rfl) ⟨670446, by rfl⟩ : syracuseStep 7151429 = 1340893) (by norm_num)
theorem B1883989 : Blo 1488064 1883989 := bbase (se 9 (by rfl) ⟨5519, by rfl⟩ : syracuseStep 1883989 = 11039) (by norm_num)
theorem B3350357 : Blo 1488064 3350357 := bbase (se 9 (by rfl) ⟨9815, by rfl⟩ : syracuseStep 3350357 = 19631) (by norm_num)
theorem B6791045 : Blo 1488064 6791045 := bbase (se 4 (by rfl) ⟨636660, by rfl⟩ : syracuseStep 6791045 = 1273321) (by norm_num)
theorem B3768221 : Blo 1488064 3768221 := bbase (se 3 (by rfl) ⟨706541, by rfl⟩ : syracuseStep 3768221 = 1413083) (by norm_num)
theorem B3350429 : Blo 1488064 3350429 := bbase (se 3 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 3350429 = 1256411) (by norm_num)
theorem B2826181 : Blo 1488064 2826181 := bbase (se 4 (by rfl) ⟨264954, by rfl⟩ : syracuseStep 2826181 = 529909) (by norm_num)
theorem B3350501 : Blo 1488064 3350501 := bbase (se 4 (by rfl) ⟨314109, by rfl⟩ : syracuseStep 3350501 = 628219) (by norm_num)
theorem B3178531 : Blo 1488064 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B3350609 : Blo 1488064 3350609 := bstep (se 2 (by rfl) ⟨1256478, by rfl⟩ : syracuseStep 3350609 = 2512957) B2512957
theorem B3350627 : Blo 1488064 3350627 := bstep (se 1 (by rfl) ⟨2512970, by rfl⟩ : syracuseStep 3350627 = 5025941) B5025941
theorem B3981425 : Blo 1488064 3981425 := bstep (se 2 (by rfl) ⟨1493034, by rfl⟩ : syracuseStep 3981425 = 2986069) B2986069
theorem B8601713 : Blo 1488064 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B5439629 : Blo 1488064 5439629 := bstep (se 3 (by rfl) ⟨1019930, by rfl⟩ : syracuseStep 5439629 = 2039861) B2039861
theorem B1884323 : Blo 1488064 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B3768515 : Blo 1488064 3768515 := bstep (se 1 (by rfl) ⟨2826386, by rfl⟩ : syracuseStep 3768515 = 5652773) B5652773
theorem B19333475 : Blo 1488064 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B9060707 : Blo 1488064 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B3178865 : Blo 1488064 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B3350897 : Blo 1488064 3350897 := bstep (se 2 (by rfl) ⟨1256586, by rfl⟩ : syracuseStep 3350897 = 2513173) B2513173
theorem B3768707 : Blo 1488064 3768707 := bstep (se 1 (by rfl) ⟨2826530, by rfl⟩ : syracuseStep 3768707 = 5653061) B5653061
theorem B3350915 : Blo 1488064 3350915 := bstep (se 1 (by rfl) ⟨2513186, by rfl⟩ : syracuseStep 3350915 = 5026373) B5026373
theorem B8479181 : Blo 1488064 8479181 := bstep (se 3 (by rfl) ⟨1589846, by rfl⟩ : syracuseStep 8479181 = 3179693) B3179693
theorem B4022765 : Blo 1488064 4022765 := bstep (se 3 (by rfl) ⟨754268, by rfl⟩ : syracuseStep 4022765 = 1508537) B1508537
theorem B5161475 : Blo 1488064 5161475 := bstep (se 1 (by rfl) ⟨3871106, by rfl⟩ : syracuseStep 5161475 = 7742213) B7742213
theorem B8053253 : Blo 1488064 8053253 := bstep (se 4 (by rfl) ⟨754992, by rfl⟩ : syracuseStep 8053253 = 1509985) B1509985
theorem B9544205 : Blo 1488064 9544205 := bstep (se 3 (by rfl) ⟨1789538, by rfl⟩ : syracuseStep 9544205 = 3579077) B3579077
theorem B5653091 : Blo 1488064 5653091 := bstep (se 1 (by rfl) ⟨4239818, by rfl⟩ : syracuseStep 5653091 = 8479637) B8479637
theorem B3351185 : Blo 1488064 3351185 := bstep (se 2 (by rfl) ⟨1256694, by rfl⟩ : syracuseStep 3351185 = 2513389) B2513389
theorem B3351203 : Blo 1488064 3351203 := bstep (se 1 (by rfl) ⟨2513402, by rfl⟩ : syracuseStep 3351203 = 5026805) B5026805
theorem B8053445 : Blo 1488064 8053445 := bstep (se 4 (by rfl) ⟨755010, by rfl⟩ : syracuseStep 8053445 = 1510021) B1510021
theorem B4834019 : Blo 1488064 4834019 := bstep (se 1 (by rfl) ⟨3625514, by rfl⟩ : syracuseStep 4834019 = 7251029) B7251029
theorem B1885027 : Blo 1488064 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B2827153 : Blo 1488064 2827153 := bstep (se 2 (by rfl) ⟨1060182, by rfl⟩ : syracuseStep 2827153 = 2120365) B2120365
theorem B3351473 : Blo 1488064 3351473 := bstep (se 2 (by rfl) ⟨1256802, by rfl⟩ : syracuseStep 3351473 = 2513605) B2513605
theorem B1885123 : Blo 1488064 1885123 := bstep (se 1 (by rfl) ⟨1413842, by rfl⟩ : syracuseStep 1885123 = 2827685) B2827685
theorem B3351491 : Blo 1488064 3351491 := bstep (se 1 (by rfl) ⟨2513618, by rfl⟩ : syracuseStep 3351491 = 5027237) B5027237
theorem B5022701 : Blo 1488064 5022701 := bstep (se 3 (by rfl) ⟨941756, by rfl⟩ : syracuseStep 5022701 = 1883513) B1883513
theorem B6038513 : Blo 1488064 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B5022755 : Blo 1488064 5022755 := bstep (se 1 (by rfl) ⟨3767066, by rfl⟩ : syracuseStep 5022755 = 7534133) B7534133
theorem B5366989 : Blo 1488064 5366989 := bstep (se 3 (by rfl) ⟨1006310, by rfl⟩ : syracuseStep 5366989 = 2012621) B2012621
theorem B3351761 : Blo 1488064 3351761 := bstep (se 2 (by rfl) ⟨1256910, by rfl⟩ : syracuseStep 3351761 = 2513821) B2513821
theorem B3351779 : Blo 1488064 3351779 := bstep (se 1 (by rfl) ⟨2513834, by rfl⟩ : syracuseStep 3351779 = 5027669) B5027669
theorem B5653745 : Blo 1488064 5653745 := bstep (se 2 (by rfl) ⟨2120154, by rfl⟩ : syracuseStep 5653745 = 4240309) B4240309
theorem B4138285 : Blo 1488064 4138285 := bstep (se 3 (by rfl) ⟨775928, by rfl⟩ : syracuseStep 4138285 = 1551857) B1551857
theorem B5023025 : Blo 1488064 5023025 := bstep (se 2 (by rfl) ⟨1883634, by rfl⟩ : syracuseStep 5023025 = 3767269) B3767269
theorem B3769649 : Blo 1488064 3769649 := bstep (se 2 (by rfl) ⟨1413618, by rfl⟩ : syracuseStep 3769649 = 2827237) B2827237
theorem B3769699 : Blo 1488064 3769699 := bstep (se 1 (by rfl) ⟨2827274, by rfl⟩ : syracuseStep 3769699 = 5654549) B5654549
theorem B2385283 : Blo 1488064 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B1885619 : Blo 1488064 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B6358499 : Blo 1488064 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B2385379 : Blo 1488064 2385379 := bstep (se 1 (by rfl) ⟨1789034, by rfl⟩ : syracuseStep 2385379 = 3578069) B3578069
theorem B3769841 : Blo 1488064 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B3352049 : Blo 1488064 3352049 := bstep (se 2 (by rfl) ⟨1257018, by rfl⟩ : syracuseStep 3352049 = 2514037) B2514037
theorem B3180035 : Blo 1488064 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B3352067 : Blo 1488064 3352067 := bstep (se 1 (by rfl) ⟨2514050, by rfl⟩ : syracuseStep 3352067 = 5028101) B5028101
theorem B2262611 : Blo 1488064 2262611 := bstep (se 1 (by rfl) ⟨1696958, by rfl⟩ : syracuseStep 2262611 = 3393917) B3393917
theorem B8046179 : Blo 1488064 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B2385539 : Blo 1488064 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B9053873 : Blo 1488064 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B2148049 : Blo 1488064 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B3352337 : Blo 1488064 3352337 := bstep (se 2 (by rfl) ⟨1257126, by rfl⟩ : syracuseStep 3352337 = 2514253) B2514253
theorem B3352355 : Blo 1488064 3352355 := bstep (se 1 (by rfl) ⟨2514266, by rfl⟩ : syracuseStep 3352355 = 5028533) B5028533
theorem B5023565 : Blo 1488064 5023565 := bstep (se 3 (by rfl) ⟨941918, by rfl⟩ : syracuseStep 5023565 = 1883837) B1883837
theorem B5023619 : Blo 1488064 5023619 := bstep (se 1 (by rfl) ⟨3767714, by rfl⟩ : syracuseStep 5023619 = 7535429) B7535429
theorem B2828209 : Blo 1488064 2828209 := bstep (se 2 (by rfl) ⟨1060578, by rfl⟩ : syracuseStep 2828209 = 2121157) B2121157
theorem B4769837 : Blo 1488064 4769837 := bstep (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) B1788689
theorem B3352625 : Blo 1488064 3352625 := bstep (se 2 (by rfl) ⟨1257234, by rfl⟩ : syracuseStep 3352625 = 2514469) B2514469
theorem B3352643 : Blo 1488064 3352643 := bstep (se 1 (by rfl) ⟨2514482, by rfl⟩ : syracuseStep 3352643 = 5028965) B5028965
theorem B12069005 : Blo 1488064 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B5023889 : Blo 1488064 5023889 := bstep (se 2 (by rfl) ⟨1883958, by rfl⟩ : syracuseStep 5023889 = 3767917) B3767917
theorem B7538993 : Blo 1488064 7538993 := bstep (se 2 (by rfl) ⟨2827122, by rfl⟩ : syracuseStep 7538993 = 5654245) B5654245
theorem B2828611 : Blo 1488064 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B4237667 : Blo 1488064 4237667 := bstep (se 1 (by rfl) ⟨3178250, by rfl⟩ : syracuseStep 4237667 = 6356501) B6356501
theorem B2828657 : Blo 1488064 2828657 := bstep (se 2 (by rfl) ⟨1060746, by rfl⟩ : syracuseStep 2828657 = 2121493) B2121493
theorem B8055217 : Blo 1488064 8055217 := bstep (se 2 (by rfl) ⟨3020706, by rfl⟩ : syracuseStep 8055217 = 6041413) B6041413
theorem B4770257 : Blo 1488064 4770257 := bstep (se 2 (by rfl) ⟨1788846, by rfl⟩ : syracuseStep 4770257 = 3577693) B3577693
theorem B3770833 : Blo 1488064 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B36743651 : Blo 1488064 36743651 := bstep (se 1 (by rfl) ⟨27557738, by rfl⟩ : syracuseStep 36743651 = 55115477) B55115477
theorem B4237859 : Blo 1488064 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B68774453 : Blo 1488064 68774453 := bstep (se 5 (by rfl) ⟨3223802, by rfl⟩ : syracuseStep 68774453 = 6447605) B6447605
theorem B2386513 : Blo 1488064 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B4082275 : Blo 1488064 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B5655203 : Blo 1488064 5655203 := bstep (se 1 (by rfl) ⟨4241402, by rfl⟩ : syracuseStep 5655203 = 8482805) B8482805
theorem B5024429 : Blo 1488064 5024429 := bstep (se 3 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 5024429 = 1884161) B1884161
theorem B5655217 : Blo 1488064 5655217 := bstep (se 2 (by rfl) ⟨2120706, by rfl⟩ : syracuseStep 5655217 = 4241413) B4241413
theorem B41863877 : Blo 1488064 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B9546437 : Blo 1488064 9546437 := bstep (se 4 (by rfl) ⟨894978, by rfl⟩ : syracuseStep 9546437 = 1789957) B1789957
theorem B5024483 : Blo 1488064 5024483 := bstep (se 1 (by rfl) ⟨3768362, by rfl⟩ : syracuseStep 5024483 = 7536725) B7536725
theorem B3771107 : Blo 1488064 3771107 := bstep (se 1 (by rfl) ⟨2828330, by rfl⟩ : syracuseStep 3771107 = 5656661) B5656661
theorem B11307761 : Blo 1488064 11307761 := bstep (se 2 (by rfl) ⟨4240410, by rfl⟩ : syracuseStep 11307761 = 8480821) B8480821
theorem B4025123 : Blo 1488064 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B2263859 : Blo 1488064 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B2263889 : Blo 1488064 2263889 := bstep (se 2 (by rfl) ⟨848958, by rfl⟩ : syracuseStep 2263889 = 1697917) B1697917
theorem B5368675 : Blo 1488064 5368675 := bstep (se 1 (by rfl) ⟨4026506, by rfl⟩ : syracuseStep 5368675 = 8053013) B8053013
theorem B4025251 : Blo 1488064 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B3771299 : Blo 1488064 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B1674211 : Blo 1488064 1674211 := bstep (se 1 (by rfl) ⟨1255658, by rfl⟩ : syracuseStep 1674211 = 2511317) B2511317
theorem B5024753 : Blo 1488064 5024753 := bstep (se 2 (by rfl) ⟨1884282, by rfl⟩ : syracuseStep 5024753 = 3768565) B3768565
theorem B1674355 : Blo 1488064 1674355 := bstep (se 1 (by rfl) ⟨1255766, by rfl⟩ : syracuseStep 1674355 = 2511533) B2511533
theorem B6360241 : Blo 1488064 6360241 := bstep (se 2 (by rfl) ⟨2385090, by rfl⟩ : syracuseStep 6360241 = 4770181) B4770181
theorem B1674499 : Blo 1488064 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B8482097 : Blo 1488064 8482097 := bstep (se 2 (by rfl) ⟨3180786, by rfl⟩ : syracuseStep 8482097 = 6361573) B6361573
theorem B4238669 : Blo 1488064 4238669 := bstep (se 3 (by rfl) ⟨794750, by rfl⟩ : syracuseStep 4238669 = 1589501) B1589501
theorem B1674643 : Blo 1488064 1674643 := bstep (se 1 (by rfl) ⟨1255982, by rfl⟩ : syracuseStep 1674643 = 2511965) B2511965
theorem B3018161 : Blo 1488064 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B2264545 : Blo 1488064 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B3182051 : Blo 1488064 3182051 := bstep (se 1 (by rfl) ⟨2386538, by rfl⟩ : syracuseStep 3182051 = 4773077) B4773077
theorem B4238851 : Blo 1488064 4238851 := bstep (se 1 (by rfl) ⟨3179138, by rfl⟩ : syracuseStep 4238851 = 6358277) B6358277
theorem B5025293 : Blo 1488064 5025293 := bstep (se 3 (by rfl) ⟨942242, by rfl⟩ : syracuseStep 5025293 = 1884485) B1884485
theorem B1674787 : Blo 1488064 1674787 := bstep (se 1 (by rfl) ⟨1256090, by rfl⟩ : syracuseStep 1674787 = 2512181) B2512181
theorem B5025347 : Blo 1488064 5025347 := bstep (se 1 (by rfl) ⟨3769010, by rfl⟩ : syracuseStep 5025347 = 7538021) B7538021
theorem B3223217 : Blo 1488064 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B2264753 : Blo 1488064 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B1674931 : Blo 1488064 1674931 := bstep (se 1 (by rfl) ⟨1256198, by rfl⟩ : syracuseStep 1674931 = 2512397) B2512397
theorem B7540451 : Blo 1488064 7540451 := bstep (se 1 (by rfl) ⟨5655338, by rfl⟩ : syracuseStep 7540451 = 11310677) B11310677
theorem B21475043 : Blo 1488064 21475043 := bstep (se 1 (by rfl) ⟨16106282, by rfl⟩ : syracuseStep 21475043 = 32212565) B32212565
theorem B2232113 : Blo 1488064 2232113 := bstep (se 2 (by rfl) ⟨837042, by rfl⟩ : syracuseStep 2232113 = 1674085) B1674085
theorem B2232131 : Blo 1488064 2232131 := bstep (se 1 (by rfl) ⟨1674098, by rfl⟩ : syracuseStep 2232131 = 3348197) B3348197
theorem B3395395 : Blo 1488064 3395395 := bstep (se 1 (by rfl) ⟨2546546, by rfl⟩ : syracuseStep 3395395 = 5093093) B5093093
theorem B1675075 : Blo 1488064 1675075 := bstep (se 1 (by rfl) ⟨1256306, by rfl⟩ : syracuseStep 1675075 = 2512613) B2512613
theorem B5025617 : Blo 1488064 5025617 := bstep (se 2 (by rfl) ⟨1884606, by rfl⟩ : syracuseStep 5025617 = 3769213) B3769213
theorem B2232161 : Blo 1488064 2232161 := bstep (se 2 (by rfl) ⟨837060, by rfl⟩ : syracuseStep 2232161 = 1674121) B1674121
theorem B2232179 : Blo 1488064 2232179 := bstep (se 1 (by rfl) ⟨1674134, by rfl⟩ : syracuseStep 2232179 = 3348269) B3348269
theorem B2232209 : Blo 1488064 2232209 := bstep (se 2 (by rfl) ⟨837078, by rfl⟩ : syracuseStep 2232209 = 1674157) B1674157
theorem B2232227 : Blo 1488064 2232227 := bstep (se 1 (by rfl) ⟨1674170, by rfl⟩ : syracuseStep 2232227 = 3348341) B3348341
theorem B4026289 : Blo 1488064 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B2232257 : Blo 1488064 2232257 := bstep (se 2 (by rfl) ⟨837096, by rfl⟩ : syracuseStep 2232257 = 1674193) B1674193
theorem B2232275 : Blo 1488064 2232275 := bstep (se 1 (by rfl) ⟨1674206, by rfl⟩ : syracuseStep 2232275 = 3348413) B3348413
theorem B1675219 : Blo 1488064 1675219 := bstep (se 1 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 1675219 = 2512829) B2512829
theorem B4239341 : Blo 1488064 4239341 := bstep (se 3 (by rfl) ⟨794876, by rfl⟩ : syracuseStep 4239341 = 1589753) B1589753
theorem B2232305 : Blo 1488064 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B2232323 : Blo 1488064 2232323 := bstep (se 1 (by rfl) ⟨1674242, by rfl⟩ : syracuseStep 2232323 = 3348485) B3348485
theorem B39759893 : Blo 1488064 39759893 := bstep (se 6 (by rfl) ⟨931872, by rfl⟩ : syracuseStep 39759893 = 1863745) B1863745
theorem B2232353 : Blo 1488064 2232353 := bstep (se 2 (by rfl) ⟨837132, by rfl⟩ : syracuseStep 2232353 = 1674265) B1674265
theorem B2232371 : Blo 1488064 2232371 := bstep (se 1 (by rfl) ⟨1674278, by rfl⟩ : syracuseStep 2232371 = 3348557) B3348557
theorem B2232401 : Blo 1488064 2232401 := bstep (se 2 (by rfl) ⟨837150, by rfl⟩ : syracuseStep 2232401 = 1674301) B1674301
theorem B6443107 : Blo 1488064 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B2232419 : Blo 1488064 2232419 := bstep (se 1 (by rfl) ⟨1674314, by rfl⟩ : syracuseStep 2232419 = 3348629) B3348629
theorem B1675363 : Blo 1488064 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B5656675 : Blo 1488064 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B2232449 : Blo 1488064 2232449 := bstep (se 2 (by rfl) ⟨837168, by rfl⟩ : syracuseStep 2232449 = 1674337) B1674337
theorem B2232467 : Blo 1488064 2232467 := bstep (se 1 (by rfl) ⟨1674350, by rfl⟩ : syracuseStep 2232467 = 3348701) B3348701
theorem B2232497 : Blo 1488064 2232497 := bstep (se 2 (by rfl) ⟨837186, by rfl⟩ : syracuseStep 2232497 = 1674373) B1674373
theorem B2232515 : Blo 1488064 2232515 := bstep (se 1 (by rfl) ⟨1674386, by rfl⟩ : syracuseStep 2232515 = 3348773) B3348773
theorem B2232545 : Blo 1488064 2232545 := bstep (se 2 (by rfl) ⟨837204, by rfl⟩ : syracuseStep 2232545 = 1674409) B1674409
theorem B2232563 : Blo 1488064 2232563 := bstep (se 1 (by rfl) ⟨1674422, by rfl⟩ : syracuseStep 2232563 = 3348845) B3348845
theorem B1675507 : Blo 1488064 1675507 := bstep (se 1 (by rfl) ⟨1256630, by rfl⟩ : syracuseStep 1675507 = 2513261) B2513261
theorem B2511121 : Blo 1488064 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B2232593 : Blo 1488064 2232593 := bstep (se 2 (by rfl) ⟨837222, by rfl⟩ : syracuseStep 2232593 = 1674445) B1674445
theorem B2232611 : Blo 1488064 2232611 := bstep (se 1 (by rfl) ⟨1674458, by rfl⟩ : syracuseStep 2232611 = 3348917) B3348917
theorem B2511155 : Blo 1488064 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B2232641 : Blo 1488064 2232641 := bstep (se 2 (by rfl) ⟨837240, by rfl⟩ : syracuseStep 2232641 = 1674481) B1674481
theorem B2232659 : Blo 1488064 2232659 := bstep (se 1 (by rfl) ⟨1674494, by rfl⟩ : syracuseStep 2232659 = 3348989) B3348989
theorem B5026157 : Blo 1488064 5026157 := bstep (se 3 (by rfl) ⟨942404, by rfl⟩ : syracuseStep 5026157 = 1884809) B1884809
theorem B2232689 : Blo 1488064 2232689 := bstep (se 2 (by rfl) ⟨837258, by rfl⟩ : syracuseStep 2232689 = 1674517) B1674517
theorem B2232707 : Blo 1488064 2232707 := bstep (se 1 (by rfl) ⟨1674530, by rfl⟩ : syracuseStep 2232707 = 3349061) B3349061
theorem B1675651 : Blo 1488064 1675651 := bstep (se 1 (by rfl) ⟨1256738, by rfl⟩ : syracuseStep 1675651 = 2513477) B2513477
theorem B2232737 : Blo 1488064 2232737 := bstep (se 2 (by rfl) ⟨837276, by rfl⟩ : syracuseStep 2232737 = 1674553) B1674553
theorem B5026211 : Blo 1488064 5026211 := bstep (se 1 (by rfl) ⟨3769658, by rfl⟩ : syracuseStep 5026211 = 7539317) B7539317
theorem B2511283 : Blo 1488064 2511283 := bstep (se 1 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 2511283 = 3766925) B3766925
theorem B2232755 : Blo 1488064 2232755 := bstep (se 1 (by rfl) ⟨1674566, by rfl⟩ : syracuseStep 2232755 = 3349133) B3349133
theorem B2232785 : Blo 1488064 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B2232803 : Blo 1488064 2232803 := bstep (se 1 (by rfl) ⟨1674602, by rfl⟩ : syracuseStep 2232803 = 3349205) B3349205
theorem B2232833 : Blo 1488064 2232833 := bstep (se 2 (by rfl) ⟨837312, by rfl⟩ : syracuseStep 2232833 = 1674625) B1674625
theorem B7541261 : Blo 1488064 7541261 := bstep (se 3 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 7541261 = 2827973) B2827973
theorem B2232851 : Blo 1488064 2232851 := bstep (se 1 (by rfl) ⟨1674638, by rfl⟩ : syracuseStep 2232851 = 3349277) B3349277
theorem B1675795 : Blo 1488064 1675795 := bstep (se 1 (by rfl) ⟨1256846, by rfl⟩ : syracuseStep 1675795 = 2513693) B2513693
theorem B2232881 : Blo 1488064 2232881 := bstep (se 2 (by rfl) ⟨837330, by rfl⟩ : syracuseStep 2232881 = 1674661) B1674661
theorem B2511425 : Blo 1488064 2511425 := bstep (se 2 (by rfl) ⟨941784, by rfl⟩ : syracuseStep 2511425 = 1883569) B1883569
theorem B2232899 : Blo 1488064 2232899 := bstep (se 1 (by rfl) ⟨1674674, by rfl⟩ : syracuseStep 2232899 = 3349349) B3349349
theorem B2011729 : Blo 1488064 2011729 := bstep (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) B1508797
theorem B2232929 : Blo 1488064 2232929 := bstep (se 2 (by rfl) ⟨837348, by rfl⟩ : syracuseStep 2232929 = 1674697) B1674697
theorem B2232947 : Blo 1488064 2232947 := bstep (se 1 (by rfl) ⟨1674710, by rfl⟩ : syracuseStep 2232947 = 3349421) B3349421
theorem B8049293 : Blo 1488064 8049293 := bstep (se 3 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 8049293 = 3018485) B3018485
theorem B2232977 : Blo 1488064 2232977 := bstep (se 2 (by rfl) ⟨837366, by rfl⟩ : syracuseStep 2232977 = 1674733) B1674733
theorem B2232995 : Blo 1488064 2232995 := bstep (se 1 (by rfl) ⟨1674746, by rfl⟩ : syracuseStep 2232995 = 3349493) B3349493
theorem B1675939 : Blo 1488064 1675939 := bstep (se 1 (by rfl) ⟨1256954, by rfl⟩ : syracuseStep 1675939 = 2513909) B2513909
theorem B5026481 : Blo 1488064 5026481 := bstep (se 2 (by rfl) ⟨1884930, by rfl⟩ : syracuseStep 5026481 = 3769861) B3769861
theorem B2511553 : Blo 1488064 2511553 := bstep (se 2 (by rfl) ⟨941832, by rfl⟩ : syracuseStep 2511553 = 1883665) B1883665
theorem B2233025 : Blo 1488064 2233025 := bstep (se 2 (by rfl) ⟨837384, by rfl⟩ : syracuseStep 2233025 = 1674769) B1674769
theorem B2233043 : Blo 1488064 2233043 := bstep (se 1 (by rfl) ⟨1674782, by rfl⟩ : syracuseStep 2233043 = 3349565) B3349565
theorem B2511587 : Blo 1488064 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B8483555 : Blo 1488064 8483555 := bstep (se 1 (by rfl) ⟨6362666, by rfl⟩ : syracuseStep 8483555 = 12725333) B12725333
theorem B2233073 : Blo 1488064 2233073 := bstep (se 2 (by rfl) ⟨837402, by rfl⟩ : syracuseStep 2233073 = 1674805) B1674805
theorem B2233091 : Blo 1488064 2233091 := bstep (se 1 (by rfl) ⟨1674818, by rfl⟩ : syracuseStep 2233091 = 3349637) B3349637
theorem B61092629 : Blo 1488064 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B2233121 : Blo 1488064 2233121 := bstep (se 2 (by rfl) ⟨837420, by rfl⟩ : syracuseStep 2233121 = 1674841) B1674841
theorem B2233139 : Blo 1488064 2233139 := bstep (se 1 (by rfl) ⟨1674854, by rfl⟩ : syracuseStep 2233139 = 3349709) B3349709
theorem B1676083 : Blo 1488064 1676083 := bstep (se 1 (by rfl) ⟨1257062, by rfl⟩ : syracuseStep 1676083 = 2514125) B2514125
theorem B2233169 : Blo 1488064 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B2511715 : Blo 1488064 2511715 := bstep (se 1 (by rfl) ⟨1883786, by rfl⟩ : syracuseStep 2511715 = 3767573) B3767573
theorem B2233187 : Blo 1488064 2233187 := bstep (se 1 (by rfl) ⟨1674890, by rfl⟩ : syracuseStep 2233187 = 3349781) B3349781
theorem B2233217 : Blo 1488064 2233217 := bstep (se 2 (by rfl) ⟨837456, by rfl⟩ : syracuseStep 2233217 = 1674913) B1674913
theorem B2233235 : Blo 1488064 2233235 := bstep (se 1 (by rfl) ⟨1674926, by rfl⟩ : syracuseStep 2233235 = 3349853) B3349853
theorem B2233265 : Blo 1488064 2233265 := bstep (se 2 (by rfl) ⟨837474, by rfl⟩ : syracuseStep 2233265 = 1674949) B1674949
theorem B2233283 : Blo 1488064 2233283 := bstep (se 1 (by rfl) ⟨1674962, by rfl⟩ : syracuseStep 2233283 = 3349925) B3349925
theorem B1676227 : Blo 1488064 1676227 := bstep (se 1 (by rfl) ⟨1257170, by rfl⟩ : syracuseStep 1676227 = 2514341) B2514341
theorem B12719045 : Blo 1488064 12719045 := bstep (se 4 (by rfl) ⟨1192410, by rfl⟩ : syracuseStep 12719045 = 2384821) B2384821
theorem B2233313 : Blo 1488064 2233313 := bstep (se 2 (by rfl) ⟨837492, by rfl⟩ : syracuseStep 2233313 = 1674985) B1674985
theorem B2511857 : Blo 1488064 2511857 := bstep (se 2 (by rfl) ⟨941946, by rfl⟩ : syracuseStep 2511857 = 1883893) B1883893
theorem B2233331 : Blo 1488064 2233331 := bstep (se 1 (by rfl) ⟨1674998, by rfl⟩ : syracuseStep 2233331 = 3349997) B3349997
theorem B18109453 : Blo 1488064 18109453 := bstep (se 3 (by rfl) ⟨3395522, by rfl⟩ : syracuseStep 18109453 = 6791045) B6791045
theorem B2233361 : Blo 1488064 2233361 := bstep (se 2 (by rfl) ⟨837510, by rfl⟩ : syracuseStep 2233361 = 1675021) B1675021
theorem B2233379 : Blo 1488064 2233379 := bstep (se 1 (by rfl) ⟨1675034, by rfl⟩ : syracuseStep 2233379 = 3350069) B3350069
theorem B2233409 : Blo 1488064 2233409 := bstep (se 2 (by rfl) ⟨837528, by rfl⟩ : syracuseStep 2233409 = 1675057) B1675057
theorem B6362189 : Blo 1488064 6362189 := bstep (se 3 (by rfl) ⟨1192910, by rfl⟩ : syracuseStep 6362189 = 2385821) B2385821
theorem B2233427 : Blo 1488064 2233427 := bstep (se 1 (by rfl) ⟨1675070, by rfl⟩ : syracuseStep 2233427 = 3350141) B3350141
theorem B2511985 : Blo 1488064 2511985 := bstep (se 2 (by rfl) ⟨941994, by rfl⟩ : syracuseStep 2511985 = 1883989) B1883989
theorem B2233457 : Blo 1488064 2233457 := bstep (se 2 (by rfl) ⟨837546, by rfl⟩ : syracuseStep 2233457 = 1675093) B1675093
theorem B2233475 : Blo 1488064 2233475 := bstep (se 1 (by rfl) ⟨1675106, by rfl⟩ : syracuseStep 2233475 = 3350213) B3350213
theorem B4240525 : Blo 1488064 4240525 := bstep (se 3 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 4240525 = 1590197) B1590197
theorem B2512019 : Blo 1488064 2512019 := bstep (se 1 (by rfl) ⟨1884014, by rfl⟩ : syracuseStep 2512019 = 3768029) B3768029
theorem B2233505 : Blo 1488064 2233505 := bstep (se 2 (by rfl) ⟨837564, by rfl⟩ : syracuseStep 2233505 = 1675129) B1675129
theorem B2233523 : Blo 1488064 2233523 := bstep (se 1 (by rfl) ⟨1675142, by rfl⟩ : syracuseStep 2233523 = 3350285) B3350285
theorem B1488067 : Blo 1488064 1488067 := bstep (se 1 (by rfl) ⟨1116050, by rfl⟩ : syracuseStep 1488067 = 2232101) B2232101
theorem B5027021 : Blo 1488064 5027021 := bstep (se 3 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 5027021 = 1885133) B1885133
theorem B2233553 : Blo 1488064 2233553 := bstep (se 2 (by rfl) ⟨837582, by rfl⟩ : syracuseStep 2233553 = 1675165) B1675165
theorem B1488083 : Blo 1488064 1488083 := bstep (se 1 (by rfl) ⟨1116062, by rfl⟩ : syracuseStep 1488083 = 2232125) B2232125
theorem B1488099 : Blo 1488064 1488099 := bstep (se 1 (by rfl) ⟨1116074, by rfl⟩ : syracuseStep 1488099 = 2232149) B2232149
theorem B2233571 : Blo 1488064 2233571 := bstep (se 1 (by rfl) ⟨1675178, by rfl⟩ : syracuseStep 2233571 = 3350357) B3350357
theorem B7533809 : Blo 1488064 7533809 := bstep (se 2 (by rfl) ⟨2825178, by rfl⟩ : syracuseStep 7533809 = 5650357) B5650357
theorem B1488115 : Blo 1488064 1488115 := bstep (se 1 (by rfl) ⟨1116086, by rfl⟩ : syracuseStep 1488115 = 2232173) B2232173
theorem B2233601 : Blo 1488064 2233601 := bstep (se 2 (by rfl) ⟨837600, by rfl⟩ : syracuseStep 2233601 = 1675201) B1675201
theorem B1488131 : Blo 1488064 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B5027075 : Blo 1488064 5027075 := bstep (se 1 (by rfl) ⟨3770306, by rfl⟩ : syracuseStep 5027075 = 7540613) B7540613
theorem B1488147 : Blo 1488064 1488147 := bstep (se 1 (by rfl) ⟨1116110, by rfl⟩ : syracuseStep 1488147 = 2232221) B2232221
theorem B2512147 : Blo 1488064 2512147 := bstep (se 1 (by rfl) ⟨1884110, by rfl⟩ : syracuseStep 2512147 = 3768221) B3768221
theorem B2233619 : Blo 1488064 2233619 := bstep (se 1 (by rfl) ⟨1675214, by rfl⟩ : syracuseStep 2233619 = 3350429) B3350429
theorem B1488163 : Blo 1488064 1488163 := bstep (se 1 (by rfl) ⟨1116122, by rfl⟩ : syracuseStep 1488163 = 2232245) B2232245
theorem B2233649 : Blo 1488064 2233649 := bstep (se 2 (by rfl) ⟨837618, by rfl⟩ : syracuseStep 2233649 = 1675237) B1675237
theorem B1488179 : Blo 1488064 1488179 := bstep (se 1 (by rfl) ⟨1116134, by rfl⟩ : syracuseStep 1488179 = 2232269) B2232269
theorem B1488195 : Blo 1488064 1488195 := bstep (se 1 (by rfl) ⟨1116146, by rfl⟩ : syracuseStep 1488195 = 2232293) B2232293
theorem B2233667 : Blo 1488064 2233667 := bstep (se 1 (by rfl) ⟨1675250, by rfl⟩ : syracuseStep 2233667 = 3350501) B3350501
theorem B1488211 : Blo 1488064 1488211 := bstep (se 1 (by rfl) ⟨1116158, by rfl⟩ : syracuseStep 1488211 = 2232317) B2232317
theorem B2233697 : Blo 1488064 2233697 := bstep (se 2 (by rfl) ⟨837636, by rfl⟩ : syracuseStep 2233697 = 1675273) B1675273
theorem B1488227 : Blo 1488064 1488227 := bstep (se 1 (by rfl) ⟨1116170, by rfl⟩ : syracuseStep 1488227 = 2232341) B2232341
theorem B1488243 : Blo 1488064 1488243 := bstep (se 1 (by rfl) ⟨1116182, by rfl⟩ : syracuseStep 1488243 = 2232365) B2232365
theorem B2233715 : Blo 1488064 2233715 := bstep (se 1 (by rfl) ⟨1675286, by rfl⟩ : syracuseStep 2233715 = 3350573) B3350573
theorem B1488259 : Blo 1488064 1488259 := bstep (se 1 (by rfl) ⟨1116194, by rfl⟩ : syracuseStep 1488259 = 2232389) B2232389
theorem B2233745 : Blo 1488064 2233745 := bstep (se 2 (by rfl) ⟨837654, by rfl⟩ : syracuseStep 2233745 = 1675309) B1675309
theorem B1488275 : Blo 1488064 1488275 := bstep (se 1 (by rfl) ⟨1116206, by rfl⟩ : syracuseStep 1488275 = 2232413) B2232413
theorem B2512289 : Blo 1488064 2512289 := bstep (se 2 (by rfl) ⟨942108, by rfl⟩ : syracuseStep 2512289 = 1884217) B1884217
theorem B1488291 : Blo 1488064 1488291 := bstep (se 1 (by rfl) ⟨1116218, by rfl⟩ : syracuseStep 1488291 = 2232437) B2232437
theorem B2233763 : Blo 1488064 2233763 := bstep (se 1 (by rfl) ⟨1675322, by rfl⟩ : syracuseStep 2233763 = 3350645) B3350645
theorem B7157155 : Blo 1488064 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B1488307 : Blo 1488064 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B2233793 : Blo 1488064 2233793 := bstep (se 2 (by rfl) ⟨837672, by rfl⟩ : syracuseStep 2233793 = 1675345) B1675345
theorem B1488323 : Blo 1488064 1488323 := bstep (se 1 (by rfl) ⟨1116242, by rfl⟩ : syracuseStep 1488323 = 2232485) B2232485
theorem B1488339 : Blo 1488064 1488339 := bstep (se 1 (by rfl) ⟨1116254, by rfl⟩ : syracuseStep 1488339 = 2232509) B2232509
theorem B2233811 : Blo 1488064 2233811 := bstep (se 1 (by rfl) ⟨1675358, by rfl⟩ : syracuseStep 2233811 = 3350717) B3350717
theorem B1488355 : Blo 1488064 1488355 := bstep (se 1 (by rfl) ⟨1116266, by rfl⟩ : syracuseStep 1488355 = 2232533) B2232533
theorem B2233841 : Blo 1488064 2233841 := bstep (se 2 (by rfl) ⟨837690, by rfl⟩ : syracuseStep 2233841 = 1675381) B1675381
theorem B12727793 : Blo 1488064 12727793 := bstep (se 2 (by rfl) ⟨4772922, by rfl⟩ : syracuseStep 12727793 = 9545845) B9545845
theorem B1488371 : Blo 1488064 1488371 := bstep (se 1 (by rfl) ⟨1116278, by rfl⟩ : syracuseStep 1488371 = 2232557) B2232557
theorem B2119169 : Blo 1488064 2119169 := bstep (se 2 (by rfl) ⟨794688, by rfl⟩ : syracuseStep 2119169 = 1589377) B1589377
theorem B1488387 : Blo 1488064 1488387 := bstep (se 1 (by rfl) ⟨1116290, by rfl⟩ : syracuseStep 1488387 = 2232581) B2232581
theorem B2233859 : Blo 1488064 2233859 := bstep (se 1 (by rfl) ⟨1675394, by rfl⟩ : syracuseStep 2233859 = 3350789) B3350789
theorem B5027345 : Blo 1488064 5027345 := bstep (se 2 (by rfl) ⟨1885254, by rfl⟩ : syracuseStep 5027345 = 3770509) B3770509
theorem B1488403 : Blo 1488064 1488403 := bstep (se 1 (by rfl) ⟨1116302, by rfl⟩ : syracuseStep 1488403 = 2232605) B2232605
theorem B2512417 : Blo 1488064 2512417 := bstep (se 2 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 2512417 = 1884313) B1884313
theorem B2233889 : Blo 1488064 2233889 := bstep (se 2 (by rfl) ⟨837708, by rfl⟩ : syracuseStep 2233889 = 1675417) B1675417
theorem B1488419 : Blo 1488064 1488419 := bstep (se 1 (by rfl) ⟨1116314, by rfl⟩ : syracuseStep 1488419 = 2232629) B2232629
theorem B1488435 : Blo 1488064 1488435 := bstep (se 1 (by rfl) ⟨1116326, by rfl⟩ : syracuseStep 1488435 = 2232653) B2232653
theorem B2233907 : Blo 1488064 2233907 := bstep (se 1 (by rfl) ⟨1675430, by rfl⟩ : syracuseStep 2233907 = 3350861) B3350861
theorem B1488451 : Blo 1488064 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B2512451 : Blo 1488064 2512451 := bstep (se 1 (by rfl) ⟨1884338, by rfl⟩ : syracuseStep 2512451 = 3768677) B3768677
theorem B2233937 : Blo 1488064 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B1488467 : Blo 1488064 1488467 := bstep (se 1 (by rfl) ⟨1116350, by rfl⟩ : syracuseStep 1488467 = 2232701) B2232701
theorem B1488483 : Blo 1488064 1488483 := bstep (se 1 (by rfl) ⟨1116362, by rfl⟩ : syracuseStep 1488483 = 2232725) B2232725
theorem B2233955 : Blo 1488064 2233955 := bstep (se 1 (by rfl) ⟨1675466, by rfl⟩ : syracuseStep 2233955 = 3350933) B3350933
theorem B1488499 : Blo 1488064 1488499 := bstep (se 1 (by rfl) ⟨1116374, by rfl⟩ : syracuseStep 1488499 = 2232749) B2232749
theorem B2233985 : Blo 1488064 2233985 := bstep (se 2 (by rfl) ⟨837744, by rfl⟩ : syracuseStep 2233985 = 1675489) B1675489
theorem B1488515 : Blo 1488064 1488515 := bstep (se 1 (by rfl) ⟨1116386, by rfl⟩ : syracuseStep 1488515 = 2232773) B2232773
theorem B21460621 : Blo 1488064 21460621 := bstep (se 3 (by rfl) ⟨4023866, by rfl⟩ : syracuseStep 21460621 = 8047733) B8047733
theorem B1488531 : Blo 1488064 1488531 := bstep (se 1 (by rfl) ⟨1116398, by rfl⟩ : syracuseStep 1488531 = 2232797) B2232797
theorem B2234003 : Blo 1488064 2234003 := bstep (se 1 (by rfl) ⟨1675502, by rfl⟩ : syracuseStep 2234003 = 3351005) B3351005
theorem B1488547 : Blo 1488064 1488547 := bstep (se 1 (by rfl) ⟨1116410, by rfl⟩ : syracuseStep 1488547 = 2232821) B2232821
theorem B2234033 : Blo 1488064 2234033 := bstep (se 2 (by rfl) ⟨837762, by rfl⟩ : syracuseStep 2234033 = 1675525) B1675525
theorem B1488563 : Blo 1488064 1488563 := bstep (se 1 (by rfl) ⟨1116422, by rfl⟩ : syracuseStep 1488563 = 2232845) B2232845
theorem B1488579 : Blo 1488064 1488579 := bstep (se 1 (by rfl) ⟨1116434, by rfl⟩ : syracuseStep 1488579 = 2232869) B2232869
theorem B2512579 : Blo 1488064 2512579 := bstep (se 1 (by rfl) ⟨1884434, by rfl⟩ : syracuseStep 2512579 = 3768869) B3768869
theorem B13579973 : Blo 1488064 13579973 := bstep (se 4 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 13579973 = 2546245) B2546245
theorem B2234051 : Blo 1488064 2234051 := bstep (se 1 (by rfl) ⟨1675538, by rfl⟩ : syracuseStep 2234051 = 3351077) B3351077
theorem B2684611 : Blo 1488064 2684611 := bstep (se 1 (by rfl) ⟨2013458, by rfl⟩ : syracuseStep 2684611 = 4026917) B4026917
theorem B1488595 : Blo 1488064 1488595 := bstep (se 1 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 1488595 = 2232893) B2232893
theorem B2234081 : Blo 1488064 2234081 := bstep (se 2 (by rfl) ⟨837780, by rfl⟩ : syracuseStep 2234081 = 1675561) B1675561
theorem B1488611 : Blo 1488064 1488611 := bstep (se 1 (by rfl) ⟨1116458, by rfl⟩ : syracuseStep 1488611 = 2232917) B2232917
theorem B1488627 : Blo 1488064 1488627 := bstep (se 1 (by rfl) ⟨1116470, by rfl⟩ : syracuseStep 1488627 = 2232941) B2232941
theorem B2234099 : Blo 1488064 2234099 := bstep (se 1 (by rfl) ⟨1675574, by rfl⟩ : syracuseStep 2234099 = 3351149) B3351149
theorem B1488643 : Blo 1488064 1488643 := bstep (se 1 (by rfl) ⟨1116482, by rfl⟩ : syracuseStep 1488643 = 2232965) B2232965
theorem B2234129 : Blo 1488064 2234129 := bstep (se 2 (by rfl) ⟨837798, by rfl⟩ : syracuseStep 2234129 = 1675597) B1675597
theorem B3020561 : Blo 1488064 3020561 := bstep (se 2 (by rfl) ⟨1132710, by rfl⟩ : syracuseStep 3020561 = 2265421) B2265421
theorem B1488659 : Blo 1488064 1488659 := bstep (se 1 (by rfl) ⟨1116494, by rfl⟩ : syracuseStep 1488659 = 2232989) B2232989
theorem B1488675 : Blo 1488064 1488675 := bstep (se 1 (by rfl) ⟨1116506, by rfl⟩ : syracuseStep 1488675 = 2233013) B2233013
theorem B2234147 : Blo 1488064 2234147 := bstep (se 1 (by rfl) ⟨1675610, by rfl⟩ : syracuseStep 2234147 = 3351221) B3351221
theorem B1488691 : Blo 1488064 1488691 := bstep (se 1 (by rfl) ⟨1116518, by rfl⟩ : syracuseStep 1488691 = 2233037) B2233037
theorem B2234177 : Blo 1488064 2234177 := bstep (se 2 (by rfl) ⟨837816, by rfl⟩ : syracuseStep 2234177 = 1675633) B1675633
theorem B1488707 : Blo 1488064 1488707 := bstep (se 1 (by rfl) ⟨1116530, by rfl⟩ : syracuseStep 1488707 = 2233061) B2233061
theorem B3348305 : Blo 1488064 3348305 := bstep (se 2 (by rfl) ⟨1255614, by rfl⟩ : syracuseStep 3348305 = 2511229) B2511229
theorem B2512721 : Blo 1488064 2512721 := bstep (se 2 (by rfl) ⟨942270, by rfl⟩ : syracuseStep 2512721 = 1884541) B1884541
theorem B1488723 : Blo 1488064 1488723 := bstep (se 1 (by rfl) ⟨1116542, by rfl⟩ : syracuseStep 1488723 = 2233085) B2233085
theorem B2234195 : Blo 1488064 2234195 := bstep (se 1 (by rfl) ⟨1675646, by rfl⟩ : syracuseStep 2234195 = 3351293) B3351293
theorem B3348323 : Blo 1488064 3348323 := bstep (se 1 (by rfl) ⟨2511242, by rfl⟩ : syracuseStep 3348323 = 5022485) B5022485
theorem B1488739 : Blo 1488064 1488739 := bstep (se 1 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 1488739 = 2233109) B2233109
theorem B4527971 : Blo 1488064 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B2234225 : Blo 1488064 2234225 := bstep (se 2 (by rfl) ⟨837834, by rfl⟩ : syracuseStep 2234225 = 1675669) B1675669
theorem B1488755 : Blo 1488064 1488755 := bstep (se 1 (by rfl) ⟨1116566, by rfl⟩ : syracuseStep 1488755 = 2233133) B2233133
theorem B1488771 : Blo 1488064 1488771 := bstep (se 1 (by rfl) ⟨1116578, by rfl⟩ : syracuseStep 1488771 = 2233157) B2233157
theorem B2234243 : Blo 1488064 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B40753037 : Blo 1488064 40753037 := bstep (se 3 (by rfl) ⟨7641194, by rfl⟩ : syracuseStep 40753037 = 15282389) B15282389
theorem B1488787 : Blo 1488064 1488787 := bstep (se 1 (by rfl) ⟨1116590, by rfl⟩ : syracuseStep 1488787 = 2233181) B2233181
theorem B2234273 : Blo 1488064 2234273 := bstep (se 2 (by rfl) ⟨837852, by rfl⟩ : syracuseStep 2234273 = 1675705) B1675705
theorem B1488803 : Blo 1488064 1488803 := bstep (se 1 (by rfl) ⟨1116602, by rfl⟩ : syracuseStep 1488803 = 2233205) B2233205
theorem B1488819 : Blo 1488064 1488819 := bstep (se 1 (by rfl) ⟨1116614, by rfl⟩ : syracuseStep 1488819 = 2233229) B2233229
theorem B2234291 : Blo 1488064 2234291 := bstep (se 1 (by rfl) ⟨1675718, by rfl⟩ : syracuseStep 2234291 = 3351437) B3351437
theorem B1488835 : Blo 1488064 1488835 := bstep (se 1 (by rfl) ⟨1116626, by rfl⟩ : syracuseStep 1488835 = 2233253) B2233253
theorem B2512849 : Blo 1488064 2512849 := bstep (se 2 (by rfl) ⟨942318, by rfl⟩ : syracuseStep 2512849 = 1884637) B1884637
theorem B2234321 : Blo 1488064 2234321 := bstep (se 2 (by rfl) ⟨837870, by rfl⟩ : syracuseStep 2234321 = 1675741) B1675741
theorem B1488851 : Blo 1488064 1488851 := bstep (se 1 (by rfl) ⟨1116638, by rfl⟩ : syracuseStep 1488851 = 2233277) B2233277
theorem B1488867 : Blo 1488064 1488867 := bstep (se 1 (by rfl) ⟨1116650, by rfl⟩ : syracuseStep 1488867 = 2233301) B2233301
theorem B2234339 : Blo 1488064 2234339 := bstep (se 1 (by rfl) ⟨1675754, by rfl⟩ : syracuseStep 2234339 = 3351509) B3351509
theorem B1488883 : Blo 1488064 1488883 := bstep (se 1 (by rfl) ⟨1116662, by rfl⟩ : syracuseStep 1488883 = 2233325) B2233325
theorem B2512883 : Blo 1488064 2512883 := bstep (se 1 (by rfl) ⟨1884662, by rfl⟩ : syracuseStep 2512883 = 3769325) B3769325
theorem B2234369 : Blo 1488064 2234369 := bstep (se 2 (by rfl) ⟨837888, by rfl⟩ : syracuseStep 2234369 = 1675777) B1675777
theorem B1488899 : Blo 1488064 1488899 := bstep (se 1 (by rfl) ⟨1116674, by rfl⟩ : syracuseStep 1488899 = 2233349) B2233349
theorem B5806093 : Blo 1488064 5806093 := bstep (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) B2177285
theorem B4413457 : Blo 1488064 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B2119699 : Blo 1488064 2119699 := bstep (se 1 (by rfl) ⟨1589774, by rfl⟩ : syracuseStep 2119699 = 3179549) B3179549
theorem B1488915 : Blo 1488064 1488915 := bstep (se 1 (by rfl) ⟨1116686, by rfl⟩ : syracuseStep 1488915 = 2233373) B2233373
theorem B2234387 : Blo 1488064 2234387 := bstep (se 1 (by rfl) ⟨1675790, by rfl⟩ : syracuseStep 2234387 = 3351581) B3351581
theorem B1488931 : Blo 1488064 1488931 := bstep (se 1 (by rfl) ⟨1116698, by rfl⟩ : syracuseStep 1488931 = 2233397) B2233397
theorem B5027885 : Blo 1488064 5027885 := bstep (se 3 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 5027885 = 1885457) B1885457
theorem B8476721 : Blo 1488064 8476721 := bstep (se 2 (by rfl) ⟨3178770, by rfl⟩ : syracuseStep 8476721 = 6357541) B6357541
theorem B1488947 : Blo 1488064 1488947 := bstep (se 1 (by rfl) ⟨1116710, by rfl⟩ : syracuseStep 1488947 = 2233421) B2233421
theorem B2234417 : Blo 1488064 2234417 := bstep (se 2 (by rfl) ⟨837906, by rfl⟩ : syracuseStep 2234417 = 1675813) B1675813
theorem B1488963 : Blo 1488064 1488963 := bstep (se 1 (by rfl) ⟨1116722, by rfl⟩ : syracuseStep 1488963 = 2233445) B2233445
theorem B2234435 : Blo 1488064 2234435 := bstep (se 1 (by rfl) ⟨1675826, by rfl⟩ : syracuseStep 2234435 = 3351653) B3351653
theorem B1488979 : Blo 1488064 1488979 := bstep (se 1 (by rfl) ⟨1116734, by rfl⟩ : syracuseStep 1488979 = 2233469) B2233469
theorem B2234465 : Blo 1488064 2234465 := bstep (se 2 (by rfl) ⟨837924, by rfl⟩ : syracuseStep 2234465 = 1675849) B1675849
theorem B1488995 : Blo 1488064 1488995 := bstep (se 1 (by rfl) ⟨1116746, by rfl⟩ : syracuseStep 1488995 = 2233493) B2233493
theorem B5027939 : Blo 1488064 5027939 := bstep (se 1 (by rfl) ⟨3770954, by rfl⟩ : syracuseStep 5027939 = 7541909) B7541909
theorem B3348593 : Blo 1488064 3348593 := bstep (se 2 (by rfl) ⟨1255722, by rfl⟩ : syracuseStep 3348593 = 2511445) B2511445
theorem B9541745 : Blo 1488064 9541745 := bstep (se 2 (by rfl) ⟨3578154, by rfl⟩ : syracuseStep 9541745 = 7156309) B7156309
theorem B1489011 : Blo 1488064 1489011 := bstep (se 1 (by rfl) ⟨1116758, by rfl⟩ : syracuseStep 1489011 = 2233517) B2233517
theorem B2513011 : Blo 1488064 2513011 := bstep (se 1 (by rfl) ⟨1884758, by rfl⟩ : syracuseStep 2513011 = 3769517) B3769517
theorem B2234483 : Blo 1488064 2234483 := bstep (se 1 (by rfl) ⟨1675862, by rfl⟩ : syracuseStep 2234483 = 3351725) B3351725
theorem B3348611 : Blo 1488064 3348611 := bstep (se 1 (by rfl) ⟨2511458, by rfl⟩ : syracuseStep 3348611 = 5022917) B5022917
theorem B1489027 : Blo 1488064 1489027 := bstep (se 1 (by rfl) ⟨1116770, by rfl⟩ : syracuseStep 1489027 = 2233541) B2233541
theorem B25426061 : Blo 1488064 25426061 := bstep (se 3 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 25426061 = 9534773) B9534773
theorem B2234513 : Blo 1488064 2234513 := bstep (se 2 (by rfl) ⟨837942, by rfl⟩ : syracuseStep 2234513 = 1675885) B1675885
theorem B1489043 : Blo 1488064 1489043 := bstep (se 1 (by rfl) ⟨1116782, by rfl⟩ : syracuseStep 1489043 = 2233565) B2233565
theorem B1489059 : Blo 1488064 1489059 := bstep (se 1 (by rfl) ⟨1116794, by rfl⟩ : syracuseStep 1489059 = 2233589) B2233589
theorem B2234531 : Blo 1488064 2234531 := bstep (se 1 (by rfl) ⟨1675898, by rfl⟩ : syracuseStep 2234531 = 3351797) B3351797
theorem B4241585 : Blo 1488064 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B1489075 : Blo 1488064 1489075 := bstep (se 1 (by rfl) ⟨1116806, by rfl⟩ : syracuseStep 1489075 = 2233613) B2233613
theorem B2234561 : Blo 1488064 2234561 := bstep (se 2 (by rfl) ⟨837960, by rfl⟩ : syracuseStep 2234561 = 1675921) B1675921
theorem B1489091 : Blo 1488064 1489091 := bstep (se 1 (by rfl) ⟨1116818, by rfl⟩ : syracuseStep 1489091 = 2233637) B2233637
theorem B1489107 : Blo 1488064 1489107 := bstep (se 1 (by rfl) ⟨1116830, by rfl⟩ : syracuseStep 1489107 = 2233661) B2233661
theorem B2234579 : Blo 1488064 2234579 := bstep (se 1 (by rfl) ⟨1675934, by rfl⟩ : syracuseStep 2234579 = 3351869) B3351869
theorem B1489123 : Blo 1488064 1489123 := bstep (se 1 (by rfl) ⟨1116842, by rfl⟩ : syracuseStep 1489123 = 2233685) B2233685
theorem B2234609 : Blo 1488064 2234609 := bstep (se 2 (by rfl) ⟨837978, by rfl⟩ : syracuseStep 2234609 = 1675957) B1675957
theorem B1489139 : Blo 1488064 1489139 := bstep (se 1 (by rfl) ⟨1116854, by rfl⟩ : syracuseStep 1489139 = 2233709) B2233709
theorem B2513153 : Blo 1488064 2513153 := bstep (se 2 (by rfl) ⟨942432, by rfl⟩ : syracuseStep 2513153 = 1884865) B1884865
theorem B1489155 : Blo 1488064 1489155 := bstep (se 1 (by rfl) ⟨1116866, by rfl⟩ : syracuseStep 1489155 = 2233733) B2233733
theorem B2234627 : Blo 1488064 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B1489171 : Blo 1488064 1489171 := bstep (se 1 (by rfl) ⟨1116878, by rfl⟩ : syracuseStep 1489171 = 2233757) B2233757
theorem B2234657 : Blo 1488064 2234657 := bstep (se 2 (by rfl) ⟨837996, by rfl⟩ : syracuseStep 2234657 = 1675993) B1675993
theorem B1489187 : Blo 1488064 1489187 := bstep (se 1 (by rfl) ⟨1116890, by rfl⟩ : syracuseStep 1489187 = 2233781) B2233781
theorem B1489203 : Blo 1488064 1489203 := bstep (se 1 (by rfl) ⟨1116902, by rfl⟩ : syracuseStep 1489203 = 2233805) B2233805
theorem B2234675 : Blo 1488064 2234675 := bstep (se 1 (by rfl) ⟨1676006, by rfl⟩ : syracuseStep 2234675 = 3352013) B3352013
theorem B1489219 : Blo 1488064 1489219 := bstep (se 1 (by rfl) ⟨1116914, by rfl⟩ : syracuseStep 1489219 = 2233829) B2233829
theorem B2234705 : Blo 1488064 2234705 := bstep (se 2 (by rfl) ⟨838014, by rfl⟩ : syracuseStep 2234705 = 1676029) B1676029
theorem B1489235 : Blo 1488064 1489235 := bstep (se 1 (by rfl) ⟨1116926, by rfl⟩ : syracuseStep 1489235 = 2233853) B2233853
theorem B2120035 : Blo 1488064 2120035 := bstep (se 1 (by rfl) ⟨1590026, by rfl⟩ : syracuseStep 2120035 = 3180053) B3180053
theorem B1489251 : Blo 1488064 1489251 := bstep (se 1 (by rfl) ⟨1116938, by rfl⟩ : syracuseStep 1489251 = 2233877) B2233877
theorem B2234723 : Blo 1488064 2234723 := bstep (se 1 (by rfl) ⟨1676042, by rfl⟩ : syracuseStep 2234723 = 3352085) B3352085
theorem B5028209 : Blo 1488064 5028209 := bstep (se 2 (by rfl) ⟨1885578, by rfl⟩ : syracuseStep 5028209 = 3771157) B3771157
theorem B1489267 : Blo 1488064 1489267 := bstep (se 1 (by rfl) ⟨1116950, by rfl⟩ : syracuseStep 1489267 = 2233901) B2233901
theorem B2513281 : Blo 1488064 2513281 := bstep (se 2 (by rfl) ⟨942480, by rfl⟩ : syracuseStep 2513281 = 1884961) B1884961
theorem B2234753 : Blo 1488064 2234753 := bstep (se 2 (by rfl) ⟨838032, by rfl⟩ : syracuseStep 2234753 = 1676065) B1676065
theorem B1489283 : Blo 1488064 1489283 := bstep (se 1 (by rfl) ⟨1116962, by rfl⟩ : syracuseStep 1489283 = 2233925) B2233925
theorem B5650829 : Blo 1488064 5650829 := bstep (se 3 (by rfl) ⟨1059530, by rfl⟩ : syracuseStep 5650829 = 2119061) B2119061
theorem B3348881 : Blo 1488064 3348881 := bstep (se 2 (by rfl) ⟨1255830, by rfl⟩ : syracuseStep 3348881 = 2511661) B2511661
theorem B1489299 : Blo 1488064 1489299 := bstep (se 1 (by rfl) ⟨1116974, by rfl⟩ : syracuseStep 1489299 = 2233949) B2233949
theorem B2234771 : Blo 1488064 2234771 := bstep (se 1 (by rfl) ⟨1676078, by rfl⟩ : syracuseStep 2234771 = 3352157) B3352157
theorem B3348899 : Blo 1488064 3348899 := bstep (se 1 (by rfl) ⟨2511674, by rfl⟩ : syracuseStep 3348899 = 5023349) B5023349
theorem B1489315 : Blo 1488064 1489315 := bstep (se 1 (by rfl) ⟨1116986, by rfl⟩ : syracuseStep 1489315 = 2233973) B2233973
theorem B2513315 : Blo 1488064 2513315 := bstep (se 1 (by rfl) ⟨1884986, by rfl⟩ : syracuseStep 2513315 = 3769973) B3769973
theorem B2234801 : Blo 1488064 2234801 := bstep (se 2 (by rfl) ⟨838050, by rfl⟩ : syracuseStep 2234801 = 1676101) B1676101
theorem B1489331 : Blo 1488064 1489331 := bstep (se 1 (by rfl) ⟨1116998, by rfl⟩ : syracuseStep 1489331 = 2233997) B2233997
theorem B1489347 : Blo 1488064 1489347 := bstep (se 1 (by rfl) ⟨1117010, by rfl⟩ : syracuseStep 1489347 = 2234021) B2234021
theorem B2234819 : Blo 1488064 2234819 := bstep (se 1 (by rfl) ⟨1676114, by rfl⟩ : syracuseStep 2234819 = 3352229) B3352229
theorem B1489363 : Blo 1488064 1489363 := bstep (se 1 (by rfl) ⟨1117022, by rfl⟩ : syracuseStep 1489363 = 2234045) B2234045
theorem B2234849 : Blo 1488064 2234849 := bstep (se 2 (by rfl) ⟨838068, by rfl⟩ : syracuseStep 2234849 = 1676137) B1676137
theorem B1489379 : Blo 1488064 1489379 := bstep (se 1 (by rfl) ⟨1117034, by rfl⟩ : syracuseStep 1489379 = 2234069) B2234069
theorem B1489395 : Blo 1488064 1489395 := bstep (se 1 (by rfl) ⟨1117046, by rfl⟩ : syracuseStep 1489395 = 2234093) B2234093
theorem B2234867 : Blo 1488064 2234867 := bstep (se 1 (by rfl) ⟨1676150, by rfl⟩ : syracuseStep 2234867 = 3352301) B3352301
theorem B1489411 : Blo 1488064 1489411 := bstep (se 1 (by rfl) ⟨1117058, by rfl⟩ : syracuseStep 1489411 = 2234117) B2234117
theorem B2234897 : Blo 1488064 2234897 := bstep (se 2 (by rfl) ⟨838086, by rfl⟩ : syracuseStep 2234897 = 1676173) B1676173
theorem B1489427 : Blo 1488064 1489427 := bstep (se 1 (by rfl) ⟨1117070, by rfl⟩ : syracuseStep 1489427 = 2234141) B2234141
theorem B1489443 : Blo 1488064 1489443 := bstep (se 1 (by rfl) ⟨1117082, by rfl⟩ : syracuseStep 1489443 = 2234165) B2234165
theorem B2513443 : Blo 1488064 2513443 := bstep (se 1 (by rfl) ⟨1885082, by rfl⟩ : syracuseStep 2513443 = 3770165) B3770165
theorem B2234915 : Blo 1488064 2234915 := bstep (se 1 (by rfl) ⟨1676186, by rfl⟩ : syracuseStep 2234915 = 3352373) B3352373
theorem B1489459 : Blo 1488064 1489459 := bstep (se 1 (by rfl) ⟨1117094, by rfl⟩ : syracuseStep 1489459 = 2234189) B2234189
theorem B2234945 : Blo 1488064 2234945 := bstep (se 2 (by rfl) ⟨838104, by rfl⟩ : syracuseStep 2234945 = 1676209) B1676209
theorem B1489475 : Blo 1488064 1489475 := bstep (se 1 (by rfl) ⟨1117106, by rfl⟩ : syracuseStep 1489475 = 2234213) B2234213
theorem B1489491 : Blo 1488064 1489491 := bstep (se 1 (by rfl) ⟨1117118, by rfl⟩ : syracuseStep 1489491 = 2234237) B2234237
theorem B2234963 : Blo 1488064 2234963 := bstep (se 1 (by rfl) ⟨1676222, by rfl⟩ : syracuseStep 2234963 = 3352445) B3352445
theorem B1489507 : Blo 1488064 1489507 := bstep (se 1 (by rfl) ⟨1117130, by rfl⟩ : syracuseStep 1489507 = 2234261) B2234261
theorem B7158385 : Blo 1488064 7158385 := bstep (se 2 (by rfl) ⟨2684394, by rfl⟩ : syracuseStep 7158385 = 5368789) B5368789
theorem B2234993 : Blo 1488064 2234993 := bstep (se 2 (by rfl) ⟨838122, by rfl⟩ : syracuseStep 2234993 = 1676245) B1676245
theorem B1489523 : Blo 1488064 1489523 := bstep (se 1 (by rfl) ⟨1117142, by rfl⟩ : syracuseStep 1489523 = 2234285) B2234285
theorem B1489539 : Blo 1488064 1489539 := bstep (se 1 (by rfl) ⟨1117154, by rfl⟩ : syracuseStep 1489539 = 2234309) B2234309
theorem B2235011 : Blo 1488064 2235011 := bstep (se 1 (by rfl) ⟨1676258, by rfl⟩ : syracuseStep 2235011 = 3352517) B3352517
theorem B1489555 : Blo 1488064 1489555 := bstep (se 1 (by rfl) ⟨1117166, by rfl⟩ : syracuseStep 1489555 = 2234333) B2234333
theorem B2235041 : Blo 1488064 2235041 := bstep (se 2 (by rfl) ⟨838140, by rfl⟩ : syracuseStep 2235041 = 1676281) B1676281
theorem B7535267 : Blo 1488064 7535267 := bstep (se 1 (by rfl) ⟨5651450, by rfl⟩ : syracuseStep 7535267 = 11302901) B11302901
theorem B1489571 : Blo 1488064 1489571 := bstep (se 1 (by rfl) ⟨1117178, by rfl⟩ : syracuseStep 1489571 = 2234357) B2234357
theorem B3349169 : Blo 1488064 3349169 := bstep (se 2 (by rfl) ⟨1255938, by rfl⟩ : syracuseStep 3349169 = 2511877) B2511877
theorem B2513585 : Blo 1488064 2513585 := bstep (se 2 (by rfl) ⟨942594, by rfl⟩ : syracuseStep 2513585 = 1885189) B1885189
theorem B1489587 : Blo 1488064 1489587 := bstep (se 1 (by rfl) ⟨1117190, by rfl⟩ : syracuseStep 1489587 = 2234381) B2234381
theorem B2235059 : Blo 1488064 2235059 := bstep (se 1 (by rfl) ⟨1676294, by rfl⟩ : syracuseStep 2235059 = 3352589) B3352589
theorem B3349187 : Blo 1488064 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B1489603 : Blo 1488064 1489603 := bstep (se 1 (by rfl) ⟨1117202, by rfl⟩ : syracuseStep 1489603 = 2234405) B2234405
theorem B2235089 : Blo 1488064 2235089 := bstep (se 2 (by rfl) ⟨838158, by rfl⟩ : syracuseStep 2235089 = 1676317) B1676317
theorem B1489619 : Blo 1488064 1489619 := bstep (se 1 (by rfl) ⟨1117214, by rfl⟩ : syracuseStep 1489619 = 2234429) B2234429
theorem B1489635 : Blo 1488064 1489635 := bstep (se 1 (by rfl) ⟨1117226, by rfl⟩ : syracuseStep 1489635 = 2234453) B2234453
theorem B1489651 : Blo 1488064 1489651 := bstep (se 1 (by rfl) ⟨1117238, by rfl⟩ : syracuseStep 1489651 = 2234477) B2234477
theorem B1489667 : Blo 1488064 1489667 := bstep (se 1 (by rfl) ⟨1117250, by rfl⟩ : syracuseStep 1489667 = 2234501) B2234501
theorem B9050885 : Blo 1488064 9050885 := bstep (se 4 (by rfl) ⟨848520, by rfl⟩ : syracuseStep 9050885 = 1697041) B1697041
theorem B3767057 : Blo 1488064 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B5094161 : Blo 1488064 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1489683 : Blo 1488064 1489683 := bstep (se 1 (by rfl) ⟨1117262, by rfl⟩ : syracuseStep 1489683 = 2234525) B2234525
theorem B1489699 : Blo 1488064 1489699 := bstep (se 1 (by rfl) ⟨1117274, by rfl⟩ : syracuseStep 1489699 = 2234549) B2234549
theorem B2513713 : Blo 1488064 2513713 := bstep (se 2 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 2513713 = 1885285) B1885285
theorem B1489715 : Blo 1488064 1489715 := bstep (se 1 (by rfl) ⟨1117286, by rfl⟩ : syracuseStep 1489715 = 2234573) B2234573
theorem B3767107 : Blo 1488064 3767107 := bstep (se 1 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 3767107 = 5650661) B5650661
theorem B2825027 : Blo 1488064 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B1489731 : Blo 1488064 1489731 := bstep (se 1 (by rfl) ⟨1117298, by rfl⟩ : syracuseStep 1489731 = 2234597) B2234597
theorem B4242257 : Blo 1488064 4242257 := bstep (se 2 (by rfl) ⟨1590846, by rfl⟩ : syracuseStep 4242257 = 3181693) B3181693
theorem B2513747 : Blo 1488064 2513747 := bstep (se 1 (by rfl) ⟨1885310, by rfl⟩ : syracuseStep 2513747 = 3770621) B3770621
theorem B1489747 : Blo 1488064 1489747 := bstep (se 1 (by rfl) ⟨1117310, by rfl⟩ : syracuseStep 1489747 = 2234621) B2234621
theorem B1489763 : Blo 1488064 1489763 := bstep (se 1 (by rfl) ⟨1117322, by rfl⟩ : syracuseStep 1489763 = 2234645) B2234645
theorem B1489779 : Blo 1488064 1489779 := bstep (se 1 (by rfl) ⟨1117334, by rfl⟩ : syracuseStep 1489779 = 2234669) B2234669
theorem B1489795 : Blo 1488064 1489795 := bstep (se 1 (by rfl) ⟨1117346, by rfl⟩ : syracuseStep 1489795 = 2234693) B2234693
theorem B5028749 : Blo 1488064 5028749 := bstep (se 3 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 5028749 = 1885781) B1885781
theorem B2120593 : Blo 1488064 2120593 := bstep (se 2 (by rfl) ⟨795222, by rfl⟩ : syracuseStep 2120593 = 1590445) B1590445
theorem B1489811 : Blo 1488064 1489811 := bstep (se 1 (by rfl) ⟨1117358, by rfl⟩ : syracuseStep 1489811 = 2234717) B2234717
theorem B1489827 : Blo 1488064 1489827 := bstep (se 1 (by rfl) ⟨1117370, by rfl⟩ : syracuseStep 1489827 = 2234741) B2234741
theorem B2120627 : Blo 1488064 2120627 := bstep (se 1 (by rfl) ⟨1590470, by rfl⟩ : syracuseStep 2120627 = 3180941) B3180941
theorem B1489843 : Blo 1488064 1489843 := bstep (se 1 (by rfl) ⟨1117382, by rfl⟩ : syracuseStep 1489843 = 2234765) B2234765
theorem B1489859 : Blo 1488064 1489859 := bstep (se 1 (by rfl) ⟨1117394, by rfl⟩ : syracuseStep 1489859 = 2234789) B2234789
theorem B5028803 : Blo 1488064 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B3767249 : Blo 1488064 3767249 := bstep (se 2 (by rfl) ⟨1412718, by rfl⟩ : syracuseStep 3767249 = 2825437) B2825437
theorem B3349457 : Blo 1488064 3349457 := bstep (se 2 (by rfl) ⟨1256046, by rfl⟩ : syracuseStep 3349457 = 2512093) B2512093
theorem B2513875 : Blo 1488064 2513875 := bstep (se 1 (by rfl) ⟨1885406, by rfl⟩ : syracuseStep 2513875 = 3770813) B3770813
theorem B1489875 : Blo 1488064 1489875 := bstep (se 1 (by rfl) ⟨1117406, by rfl⟩ : syracuseStep 1489875 = 2234813) B2234813
theorem B3349475 : Blo 1488064 3349475 := bstep (se 1 (by rfl) ⟨2512106, by rfl⟩ : syracuseStep 3349475 = 5024213) B5024213
theorem B1489891 : Blo 1488064 1489891 := bstep (se 1 (by rfl) ⟨1117418, by rfl⟩ : syracuseStep 1489891 = 2234837) B2234837
theorem B1489907 : Blo 1488064 1489907 := bstep (se 1 (by rfl) ⟨1117430, by rfl⟩ : syracuseStep 1489907 = 2234861) B2234861
theorem B1489923 : Blo 1488064 1489923 := bstep (se 1 (by rfl) ⟨1117442, by rfl⟩ : syracuseStep 1489923 = 2234885) B2234885
theorem B1489939 : Blo 1488064 1489939 := bstep (se 1 (by rfl) ⟨1117454, by rfl⟩ : syracuseStep 1489939 = 2234909) B2234909
theorem B1489955 : Blo 1488064 1489955 := bstep (se 1 (by rfl) ⟨1117466, by rfl⟩ : syracuseStep 1489955 = 2234933) B2234933
theorem B1489971 : Blo 1488064 1489971 := bstep (se 1 (by rfl) ⟨1117478, by rfl⟩ : syracuseStep 1489971 = 2234957) B2234957
theorem B1489987 : Blo 1488064 1489987 := bstep (se 1 (by rfl) ⟨1117490, by rfl⟩ : syracuseStep 1489987 = 2234981) B2234981
theorem B1490003 : Blo 1488064 1490003 := bstep (se 1 (by rfl) ⟨1117502, by rfl⟩ : syracuseStep 1490003 = 2235005) B2235005
theorem B2514017 : Blo 1488064 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B15285347 : Blo 1488064 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B1490019 : Blo 1488064 1490019 := bstep (se 1 (by rfl) ⟨1117514, by rfl⟩ : syracuseStep 1490019 = 2235029) B2235029
theorem B1490035 : Blo 1488064 1490035 := bstep (se 1 (by rfl) ⟨1117526, by rfl⟩ : syracuseStep 1490035 = 2235053) B2235053
theorem B1490051 : Blo 1488064 1490051 := bstep (se 1 (by rfl) ⟨1117538, by rfl⟩ : syracuseStep 1490051 = 2235077) B2235077
theorem B24476813 : Blo 1488064 24476813 := bstep (se 3 (by rfl) ⟨4589402, by rfl⟩ : syracuseStep 24476813 = 9178805) B9178805
theorem B5651633 : Blo 1488064 5651633 := bstep (se 2 (by rfl) ⟨2119362, by rfl⟩ : syracuseStep 5651633 = 4238725) B4238725
theorem B2514145 : Blo 1488064 2514145 := bstep (se 2 (by rfl) ⟨942804, by rfl⟩ : syracuseStep 2514145 = 1885609) B1885609
theorem B3349745 : Blo 1488064 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B3349763 : Blo 1488064 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B2514179 : Blo 1488064 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B34389269 : Blo 1488064 34389269 := bstep (se 6 (by rfl) ⟨805998, by rfl⟩ : syracuseStep 34389269 = 1611997) B1611997
theorem B2514307 : Blo 1488064 2514307 := bstep (se 1 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 2514307 = 3771461) B3771461
theorem B7536077 : Blo 1488064 7536077 := bstep (se 3 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 7536077 = 2826029) B2826029
theorem B2121185 : Blo 1488064 2121185 := bstep (se 2 (by rfl) ⟨795444, by rfl⟩ : syracuseStep 2121185 = 1590889) B1590889
theorem B8478179 : Blo 1488064 8478179 := bstep (se 1 (by rfl) ⟨6358634, by rfl⟩ : syracuseStep 8478179 = 12717269) B12717269
theorem B3350033 : Blo 1488064 3350033 := bstep (se 2 (by rfl) ⟨1256262, by rfl⟩ : syracuseStep 3350033 = 2512525) B2512525
theorem B2514449 : Blo 1488064 2514449 := bstep (se 2 (by rfl) ⟨942918, by rfl⟩ : syracuseStep 2514449 = 1885837) B1885837
theorem B3350051 : Blo 1488064 3350051 := bstep (se 1 (by rfl) ⟨2512538, by rfl⟩ : syracuseStep 3350051 = 5025077) B5025077
theorem B4529699 : Blo 1488064 4529699 := bstep (se 1 (by rfl) ⟨3397274, by rfl⟩ : syracuseStep 4529699 = 6794549) B6794549
theorem B2121265 : Blo 1488064 2121265 := bstep (se 2 (by rfl) ⟨795474, by rfl⟩ : syracuseStep 2121265 = 1590949) B1590949
theorem B1883731 : Blo 1488064 1883731 := bstep (se 1 (by rfl) ⟨1412798, by rfl⟩ : syracuseStep 1883731 = 2825597) B2825597
theorem B4243043 : Blo 1488064 4243043 := bstep (se 1 (by rfl) ⟨3182282, by rfl⟩ : syracuseStep 4243043 = 6364565) B6364565
theorem B17186417 : Blo 1488064 17186417 := bstep (se 2 (by rfl) ⟨6444906, by rfl⟩ : syracuseStep 17186417 = 12889813) B12889813
theorem B1883827 : Blo 1488064 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B2825923 : Blo 1488064 2825923 := bstep (se 1 (by rfl) ⟨2119442, by rfl⟩ : syracuseStep 2825923 = 4238885) B4238885
theorem B2547409 : Blo 1488064 2547409 := bstep (se 2 (by rfl) ⟨955278, by rfl⟩ : syracuseStep 2547409 = 1910557) B1910557
theorem B9060101 : Blo 1488064 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B8052493 : Blo 1488064 8052493 := bstep (se 3 (by rfl) ⟨1509842, by rfl⟩ : syracuseStep 8052493 = 3019685) B3019685
theorem B4529965 : Blo 1488064 4529965 := bstep (se 3 (by rfl) ⟨849368, by rfl⟩ : syracuseStep 4529965 = 1698737) B1698737
theorem B3350321 : Blo 1488064 3350321 := bstep (se 2 (by rfl) ⟨1256370, by rfl⟩ : syracuseStep 3350321 = 2512741) B2512741
theorem B3350339 : Blo 1488064 3350339 := bstep (se 1 (by rfl) ⟨2512754, by rfl⟩ : syracuseStep 3350339 = 5025509) B5025509
theorem B5652301 : Blo 1488064 5652301 := bstep (se 3 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 5652301 = 2119613) B2119613
theorem B2826083 : Blo 1488064 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B4767619 : Blo 1488064 4767619 := bstep (se 1 (by rfl) ⟨3575714, by rfl⟩ : syracuseStep 4767619 = 7151429) B7151429
theorem B51560333 : Blo 1488064 51560333 := bstep (se 3 (by rfl) ⟨9667562, by rfl⟩ : syracuseStep 51560333 = 19335125) B19335125
theorem B11304845 : Blo 1488064 11304845 := bstep (se 3 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 11304845 = 4239317) B4239317
theorem B3768241 : Blo 1488064 3768241 := bstep (se 2 (by rfl) ⟨1413090, by rfl⟩ : syracuseStep 3768241 = 2826181) B2826181
theorem B2547667 : Blo 1488064 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B9052145 : Blo 1488064 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B4530161 : Blo 1488064 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B7741457 : Blo 1488064 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B2826265 : Blo 1488064 2826265 := bstep (se 2 (by rfl) ⟨1059849, by rfl⟩ : syracuseStep 2826265 = 2119699) B2119699
theorem B5734475 : Blo 1488064 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B3350681 : Blo 1488064 3350681 := bstep (se 2 (by rfl) ⟨1256505, by rfl⟩ : syracuseStep 3350681 = 2513011) B2513011
theorem B3350771 : Blo 1488064 3350771 := bstep (se 1 (by rfl) ⟨2513078, by rfl⟩ : syracuseStep 3350771 = 5026157) B5026157
theorem B3350807 : Blo 1488064 3350807 := bstep (se 1 (by rfl) ⟨2513105, by rfl⟩ : syracuseStep 3350807 = 5026211) B5026211
theorem B5652787 : Blo 1488064 5652787 := bstep (se 1 (by rfl) ⟨4239590, by rfl⟩ : syracuseStep 5652787 = 8479181) B8479181
theorem B3440983 : Blo 1488064 3440983 := bstep (se 1 (by rfl) ⟨2580737, by rfl⟩ : syracuseStep 3440983 = 5161475) B5161475
theorem B3768727 : Blo 1488064 3768727 := bstep (se 1 (by rfl) ⟨2826545, by rfl⟩ : syracuseStep 3768727 = 5653091) B5653091
theorem B5366195 : Blo 1488064 5366195 := bstep (se 1 (by rfl) ⟨4024646, by rfl⟩ : syracuseStep 5366195 = 8049293) B8049293
theorem B3350987 : Blo 1488064 3350987 := bstep (se 1 (by rfl) ⟨2513240, by rfl⟩ : syracuseStep 3350987 = 5026481) B5026481
theorem B2826713 : Blo 1488064 2826713 := bstep (se 2 (by rfl) ⟨1060017, by rfl⟩ : syracuseStep 2826713 = 2120035) B2120035
theorem B3351041 : Blo 1488064 3351041 := bstep (se 2 (by rfl) ⟨1256640, by rfl⟩ : syracuseStep 3351041 = 2513281) B2513281
theorem B10740289 : Blo 1488064 10740289 := bstep (se 2 (by rfl) ⟨4027608, by rfl⟩ : syracuseStep 10740289 = 8055217) B8055217
theorem B8479363 : Blo 1488064 8479363 := bstep (se 1 (by rfl) ⟨6359522, by rfl⟩ : syracuseStep 8479363 = 12719045) B12719045
theorem B3351257 : Blo 1488064 3351257 := bstep (se 2 (by rfl) ⟨1256721, by rfl⟩ : syracuseStep 3351257 = 2513443) B2513443
theorem B3351347 : Blo 1488064 3351347 := bstep (se 1 (by rfl) ⟨2513510, by rfl⟩ : syracuseStep 3351347 = 5027021) B5027021
theorem B9544513 : Blo 1488064 9544513 := bstep (se 2 (by rfl) ⟨3579192, by rfl⟩ : syracuseStep 9544513 = 7158385) B7158385
theorem B5022539 : Blo 1488064 5022539 := bstep (se 1 (by rfl) ⟨3766904, by rfl⟩ : syracuseStep 5022539 = 7533809) B7533809
theorem B3769163 : Blo 1488064 3769163 := bstep (se 1 (by rfl) ⟨2826872, by rfl⟩ : syracuseStep 3769163 = 5653745) B5653745
theorem B3351383 : Blo 1488064 3351383 := bstep (se 1 (by rfl) ⟨2513537, by rfl⟩ : syracuseStep 3351383 = 5027075) B5027075
theorem B3351563 : Blo 1488064 3351563 := bstep (se 1 (by rfl) ⟨2513672, by rfl⟩ : syracuseStep 3351563 = 5027345) B5027345
theorem B3351617 : Blo 1488064 3351617 := bstep (se 2 (by rfl) ⟨1256856, by rfl⟩ : syracuseStep 3351617 = 2513713) B2513713
theorem B1590359 : Blo 1488064 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B5022809 : Blo 1488064 5022809 := bstep (se 2 (by rfl) ⟨1883553, by rfl⟩ : syracuseStep 5022809 = 3767107) B3767107
theorem B9053315 : Blo 1488064 9053315 := bstep (se 1 (by rfl) ⟨6789986, by rfl⟩ : syracuseStep 9053315 = 13579973) B13579973
theorem B42468533 : Blo 1488064 42468533 := bstep (se 5 (by rfl) ⟨1990712, by rfl⟩ : syracuseStep 42468533 = 3981425) B3981425
theorem B3769537 : Blo 1488064 3769537 := bstep (se 2 (by rfl) ⟨1413576, by rfl⟩ : syracuseStep 3769537 = 2827153) B2827153
theorem B2827457 : Blo 1488064 2827457 := bstep (se 2 (by rfl) ⟨1060296, by rfl⟩ : syracuseStep 2827457 = 2120593) B2120593
theorem B5367001 : Blo 1488064 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B3351833 : Blo 1488064 3351833 := bstep (se 2 (by rfl) ⟨1256937, by rfl⟩ : syracuseStep 3351833 = 2513875) B2513875
theorem B3179891 : Blo 1488064 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B3351923 : Blo 1488064 3351923 := bstep (se 1 (by rfl) ⟨2513942, by rfl⟩ : syracuseStep 3351923 = 5027885) B5027885
theorem B3351959 : Blo 1488064 3351959 := bstep (se 1 (by rfl) ⟨2513969, by rfl⟩ : syracuseStep 3351959 = 5027939) B5027939
theorem B16950707 : Blo 1488064 16950707 := bstep (se 1 (by rfl) ⟨12713030, by rfl⟩ : syracuseStep 16950707 = 25426061) B25426061
theorem B2827723 : Blo 1488064 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B5654033 : Blo 1488064 5654033 := bstep (se 2 (by rfl) ⟨2120262, by rfl⟩ : syracuseStep 5654033 = 4240525) B4240525
theorem B8480321 : Blo 1488064 8480321 := bstep (se 2 (by rfl) ⟨3180120, by rfl⟩ : syracuseStep 8480321 = 6360241) B6360241
theorem B3352139 : Blo 1488064 3352139 := bstep (se 1 (by rfl) ⟨2514104, by rfl⟩ : syracuseStep 3352139 = 5028209) B5028209
theorem B1885771 : Blo 1488064 1885771 := bstep (se 1 (by rfl) ⟨1414328, by rfl⟩ : syracuseStep 1885771 = 2828657) B2828657
theorem B3352193 : Blo 1488064 3352193 := bstep (se 2 (by rfl) ⟨1257072, by rfl⟩ : syracuseStep 3352193 = 2514145) B2514145
theorem B24495767 : Blo 1488064 24495767 := bstep (se 1 (by rfl) ⟨18371825, by rfl⟩ : syracuseStep 24495767 = 36743651) B36743651
theorem B5023511 : Blo 1488064 5023511 := bstep (se 1 (by rfl) ⟨3767633, by rfl⟩ : syracuseStep 5023511 = 7535267) B7535267
theorem B3770135 : Blo 1488064 3770135 := bstep (se 1 (by rfl) ⟨2827601, by rfl⟩ : syracuseStep 3770135 = 5655203) B5655203
theorem B7538507 : Blo 1488064 7538507 := bstep (se 1 (by rfl) ⟨5653880, by rfl⟩ : syracuseStep 7538507 = 11307761) B11307761
theorem B3180377 : Blo 1488064 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B3352409 : Blo 1488064 3352409 := bstep (se 2 (by rfl) ⟨1257153, by rfl⟩ : syracuseStep 3352409 = 2514307) B2514307
theorem B1509239 : Blo 1488064 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B2828171 : Blo 1488064 2828171 := bstep (se 1 (by rfl) ⟨2121128, by rfl⟩ : syracuseStep 2828171 = 4242257) B4242257
theorem B3352499 : Blo 1488064 3352499 := bstep (se 1 (by rfl) ⟨2514374, by rfl⟩ : syracuseStep 3352499 = 5028749) B5028749
theorem B3352535 : Blo 1488064 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B2828353 : Blo 1488064 2828353 := bstep (se 2 (by rfl) ⟨1060632, by rfl⟩ : syracuseStep 2828353 = 2121265) B2121265
theorem B5654731 : Blo 1488064 5654731 := bstep (se 1 (by rfl) ⟨4241048, by rfl⟩ : syracuseStep 5654731 = 8482097) B8482097
theorem B5024051 : Blo 1488064 5024051 := bstep (se 1 (by rfl) ⟨3768038, by rfl⟩ : syracuseStep 5024051 = 7536077) B7536077
theorem B6039953 : Blo 1488064 6039953 := bstep (se 2 (by rfl) ⟨2264982, by rfl⟩ : syracuseStep 6039953 = 4529965) B4529965
theorem B2828695 : Blo 1488064 2828695 := bstep (se 1 (by rfl) ⟨2121521, by rfl⟩ : syracuseStep 2828695 = 4243043) B4243043
theorem B2148811 : Blo 1488064 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B1509835 : Blo 1488064 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B5655005 : Blo 1488064 5655005 := bstep (se 3 (by rfl) ⟨1060313, by rfl⟩ : syracuseStep 5655005 = 2120627) B2120627
theorem B6040067 : Blo 1488064 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B5024321 : Blo 1488064 5024321 := bstep (se 2 (by rfl) ⟨1884120, by rfl⟩ : syracuseStep 5024321 = 3768241) B3768241
theorem B5368385 : Blo 1488064 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B3770945 : Blo 1488064 3770945 := bstep (se 2 (by rfl) ⟨1414104, by rfl⟩ : syracuseStep 3770945 = 2828209) B2828209
theorem B23538437 : Blo 1488064 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B16952165 : Blo 1488064 16952165 := bstep (se 4 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 16952165 = 3178531) B3178531
theorem B1674103 : Blo 1488064 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B12888983 : Blo 1488064 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B2681843 : Blo 1488064 2681843 := bstep (se 1 (by rfl) ⟨2011382, by rfl⟩ : syracuseStep 2681843 = 4022765) B4022765
theorem B5368835 : Blo 1488064 5368835 := bstep (se 1 (by rfl) ⟨4026626, by rfl⟩ : syracuseStep 5368835 = 8053253) B8053253
theorem B1674283 : Blo 1488064 1674283 := bstep (se 1 (by rfl) ⟨1255712, by rfl⟩ : syracuseStep 1674283 = 2511425) B2511425
theorem B3771481 : Blo 1488064 3771481 := bstep (se 2 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 3771481 = 2828611) B2828611
theorem B5024861 : Blo 1488064 5024861 := bstep (se 3 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 5024861 = 1884323) B1884323
theorem B5368963 : Blo 1488064 5368963 := bstep (se 1 (by rfl) ⟨4026722, by rfl⟩ : syracuseStep 5368963 = 8053445) B8053445
theorem B1674391 : Blo 1488064 1674391 := bstep (se 1 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 1674391 = 2511587) B2511587
theorem B3222679 : Blo 1488064 3222679 := bstep (se 1 (by rfl) ⟨2417009, by rfl⟩ : syracuseStep 3222679 = 4834019) B4834019
theorem B5655703 : Blo 1488064 5655703 := bstep (se 1 (by rfl) ⟨4241777, by rfl⟩ : syracuseStep 5655703 = 8483555) B8483555
theorem B1674571 : Blo 1488064 1674571 := bstep (se 1 (by rfl) ⟨1255928, by rfl⟩ : syracuseStep 1674571 = 2511857) B2511857
theorem B4025675 : Blo 1488064 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B1674679 : Blo 1488064 1674679 := bstep (se 1 (by rfl) ⟨1256009, by rfl⟩ : syracuseStep 1674679 = 2512019) B2512019
theorem B2682305 : Blo 1488064 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B3182017 : Blo 1488064 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B5443033 : Blo 1488064 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B7540289 : Blo 1488064 7540289 := bstep (se 2 (by rfl) ⟨2827608, by rfl⟩ : syracuseStep 7540289 = 5655217) B5655217
theorem B24161885 : Blo 1488064 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B1674859 : Blo 1488064 1674859 := bstep (se 1 (by rfl) ⟨1256144, by rfl⟩ : syracuseStep 1674859 = 2512289) B2512289
theorem B4238999 : Blo 1488064 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B1674967 : Blo 1488064 1674967 := bstep (se 1 (by rfl) ⟨1256225, by rfl⟩ : syracuseStep 1674967 = 2512451) B2512451
theorem B2232203 : Blo 1488064 2232203 := bstep (se 1 (by rfl) ⟨1674152, by rfl⟩ : syracuseStep 2232203 = 3348305) B3348305
theorem B1675147 : Blo 1488064 1675147 := bstep (se 1 (by rfl) ⟨1256360, by rfl⟩ : syracuseStep 1675147 = 2512721) B2512721
theorem B2232215 : Blo 1488064 2232215 := bstep (se 1 (by rfl) ⟨1674161, by rfl⟩ : syracuseStep 2232215 = 3348323) B3348323
theorem B3018647 : Blo 1488064 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B5656493 : Blo 1488064 5656493 := bstep (se 3 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 5656493 = 2121185) B2121185
theorem B27168691 : Blo 1488064 27168691 := bstep (se 1 (by rfl) ⟨20376518, by rfl⟩ : syracuseStep 27168691 = 40753037) B40753037
theorem B2232281 : Blo 1488064 2232281 := bstep (se 2 (by rfl) ⟨837105, by rfl⟩ : syracuseStep 2232281 = 1674211) B1674211
theorem B1675255 : Blo 1488064 1675255 := bstep (se 1 (by rfl) ⟨1256441, by rfl⟩ : syracuseStep 1675255 = 2512883) B2512883
theorem B24145937 : Blo 1488064 24145937 := bstep (se 2 (by rfl) ⟨9054726, by rfl⟩ : syracuseStep 24145937 = 18109453) B18109453
theorem B2232395 : Blo 1488064 2232395 := bstep (se 1 (by rfl) ⟨1674296, by rfl⟩ : syracuseStep 2232395 = 3348593) B3348593
theorem B6361163 : Blo 1488064 6361163 := bstep (se 1 (by rfl) ⟨4770872, by rfl⟩ : syracuseStep 6361163 = 9541745) B9541745
theorem B2232407 : Blo 1488064 2232407 := bstep (se 1 (by rfl) ⟨1674305, by rfl⟩ : syracuseStep 2232407 = 3348611) B3348611
theorem B11300957 : Blo 1488064 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B2232473 : Blo 1488064 2232473 := bstep (se 2 (by rfl) ⟨837177, by rfl⟩ : syracuseStep 2232473 = 1674355) B1674355
theorem B1675435 : Blo 1488064 1675435 := bstep (se 1 (by rfl) ⟨1256576, by rfl⟩ : syracuseStep 1675435 = 2513153) B2513153
theorem B5025995 : Blo 1488064 5025995 := bstep (se 1 (by rfl) ⟨3769496, by rfl⟩ : syracuseStep 5025995 = 7538993) B7538993
theorem B6033629 : Blo 1488064 6033629 := bstep (se 3 (by rfl) ⟨1131305, by rfl⟩ : syracuseStep 6033629 = 2262611) B2262611
theorem B2232587 : Blo 1488064 2232587 := bstep (se 1 (by rfl) ⟨1674440, by rfl⟩ : syracuseStep 2232587 = 3348881) B3348881
theorem B7155985 : Blo 1488064 7155985 := bstep (se 2 (by rfl) ⟨2683494, by rfl⟩ : syracuseStep 7155985 = 5366989) B5366989
theorem B2232599 : Blo 1488064 2232599 := bstep (se 1 (by rfl) ⟨1674449, by rfl⟩ : syracuseStep 2232599 = 3348899) B3348899
theorem B1675543 : Blo 1488064 1675543 := bstep (se 1 (by rfl) ⟨1256657, by rfl⟩ : syracuseStep 1675543 = 2513315) B2513315
theorem B2232665 : Blo 1488064 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B5517713 : Blo 1488064 5517713 := bstep (se 2 (by rfl) ⟨2069142, by rfl⟩ : syracuseStep 5517713 = 4138285) B4138285
theorem B2232779 : Blo 1488064 2232779 := bstep (se 1 (by rfl) ⟨1674584, by rfl⟩ : syracuseStep 2232779 = 3349169) B3349169
theorem B1675723 : Blo 1488064 1675723 := bstep (se 1 (by rfl) ⟨1256792, by rfl⟩ : syracuseStep 1675723 = 2513585) B2513585
theorem B2232791 : Blo 1488064 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B5026265 : Blo 1488064 5026265 := bstep (se 2 (by rfl) ⟨1884849, by rfl⟩ : syracuseStep 5026265 = 3769699) B3769699
theorem B6033923 : Blo 1488064 6033923 := bstep (se 1 (by rfl) ⟨4525442, by rfl⟩ : syracuseStep 6033923 = 9050885) B9050885
theorem B2511371 : Blo 1488064 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B3396107 : Blo 1488064 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2683415 : Blo 1488064 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B2232857 : Blo 1488064 2232857 := bstep (se 2 (by rfl) ⟨837321, by rfl⟩ : syracuseStep 2232857 = 1674643) B1674643
theorem B1675831 : Blo 1488064 1675831 := bstep (se 1 (by rfl) ⟨1256873, by rfl⟩ : syracuseStep 1675831 = 2513747) B2513747
theorem B3019393 : Blo 1488064 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B2511499 : Blo 1488064 2511499 := bstep (se 1 (by rfl) ⟨1883624, by rfl⟩ : syracuseStep 2511499 = 3767249) B3767249
theorem B2232971 : Blo 1488064 2232971 := bstep (se 1 (by rfl) ⟨1674728, by rfl⟩ : syracuseStep 2232971 = 3349457) B3349457
theorem B2232983 : Blo 1488064 2232983 := bstep (se 1 (by rfl) ⟨1674737, by rfl⟩ : syracuseStep 2232983 = 3349475) B3349475
theorem B2233049 : Blo 1488064 2233049 := bstep (se 2 (by rfl) ⟨837393, by rfl⟩ : syracuseStep 2233049 = 1674787) B1674787
theorem B1676011 : Blo 1488064 1676011 := bstep (se 1 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 1676011 = 2514017) B2514017
theorem B2511641 : Blo 1488064 2511641 := bstep (se 2 (by rfl) ⟨941865, by rfl⟩ : syracuseStep 2511641 = 1883731) B1883731
theorem B2233163 : Blo 1488064 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2233175 : Blo 1488064 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B1676119 : Blo 1488064 1676119 := bstep (se 1 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 1676119 = 2514179) B2514179
theorem B22926179 : Blo 1488064 22926179 := bstep (se 1 (by rfl) ⟨17194634, by rfl⟩ : syracuseStep 22926179 = 34389269) B34389269
theorem B2511769 : Blo 1488064 2511769 := bstep (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) B1883827
theorem B2233241 : Blo 1488064 2233241 := bstep (se 2 (by rfl) ⟨837465, by rfl⟩ : syracuseStep 2233241 = 1674931) B1674931
theorem B2864065 : Blo 1488064 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B3396545 : Blo 1488064 3396545 := bstep (se 2 (by rfl) ⟨1273704, by rfl⟩ : syracuseStep 3396545 = 2547409) B2547409
theorem B2012107 : Blo 1488064 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B2233355 : Blo 1488064 2233355 := bstep (se 1 (by rfl) ⟨1675016, by rfl⟩ : syracuseStep 2233355 = 3350033) B3350033
theorem B1676299 : Blo 1488064 1676299 := bstep (se 1 (by rfl) ⟨1257224, by rfl⟩ : syracuseStep 1676299 = 2514449) B2514449
theorem B10736657 : Blo 1488064 10736657 := bstep (se 2 (by rfl) ⟨4026246, by rfl⟩ : syracuseStep 10736657 = 8052493) B8052493
theorem B2233367 : Blo 1488064 2233367 := bstep (se 1 (by rfl) ⟨1675025, by rfl⟩ : syracuseStep 2233367 = 3350051) B3350051
theorem B3019799 : Blo 1488064 3019799 := bstep (se 1 (by rfl) ⟨2264849, by rfl⟩ : syracuseStep 3019799 = 4529699) B4529699
theorem B11457611 : Blo 1488064 11457611 := bstep (se 1 (by rfl) ⟨8593208, by rfl⟩ : syracuseStep 11457611 = 17186417) B17186417
theorem B4527193 : Blo 1488064 4527193 := bstep (se 2 (by rfl) ⟨1697697, by rfl⟩ : syracuseStep 4527193 = 3395395) B3395395
theorem B2233433 : Blo 1488064 2233433 := bstep (se 2 (by rfl) ⟨837537, by rfl⟩ : syracuseStep 2233433 = 1675075) B1675075
theorem B5026967 : Blo 1488064 5026967 := bstep (se 1 (by rfl) ⟨3770225, by rfl⟩ : syracuseStep 5026967 = 7540451) B7540451
theorem B14316695 : Blo 1488064 14316695 := bstep (se 1 (by rfl) ⟨10737521, by rfl⟩ : syracuseStep 14316695 = 21475043) B21475043
theorem B1488075 : Blo 1488064 1488075 := bstep (se 1 (by rfl) ⟨1116056, by rfl⟩ : syracuseStep 1488075 = 2232113) B2232113
theorem B2233547 : Blo 1488064 2233547 := bstep (se 1 (by rfl) ⟨1675160, by rfl⟩ : syracuseStep 2233547 = 3350321) B3350321
theorem B1488087 : Blo 1488064 1488087 := bstep (se 1 (by rfl) ⟨1116065, by rfl⟩ : syracuseStep 1488087 = 2232131) B2232131
theorem B2233559 : Blo 1488064 2233559 := bstep (se 1 (by rfl) ⟨1675169, by rfl⟩ : syracuseStep 2233559 = 3350339) B3350339
theorem B1488107 : Blo 1488064 1488107 := bstep (se 1 (by rfl) ⟨1116080, by rfl⟩ : syracuseStep 1488107 = 2232161) B2232161
theorem B1488119 : Blo 1488064 1488119 := bstep (se 1 (by rfl) ⟨1116089, by rfl⟩ : syracuseStep 1488119 = 2232179) B2232179
theorem B1488139 : Blo 1488064 1488139 := bstep (se 1 (by rfl) ⟨1116104, by rfl⟩ : syracuseStep 1488139 = 2232209) B2232209
theorem B1488151 : Blo 1488064 1488151 := bstep (se 1 (by rfl) ⟨1116113, by rfl⟩ : syracuseStep 1488151 = 2232227) B2232227
theorem B2233625 : Blo 1488064 2233625 := bstep (se 2 (by rfl) ⟨837609, by rfl⟩ : syracuseStep 2233625 = 1675219) B1675219
theorem B3396889 : Blo 1488064 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B1488171 : Blo 1488064 1488171 := bstep (se 1 (by rfl) ⟨1116128, by rfl⟩ : syracuseStep 1488171 = 2232257) B2232257
theorem B1488183 : Blo 1488064 1488183 := bstep (se 1 (by rfl) ⟨1116137, by rfl⟩ : syracuseStep 1488183 = 2232275) B2232275
theorem B1488203 : Blo 1488064 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B6034763 : Blo 1488064 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B3020107 : Blo 1488064 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B1488215 : Blo 1488064 1488215 := bstep (se 1 (by rfl) ⟨1116161, by rfl⟩ : syracuseStep 1488215 = 2232323) B2232323
theorem B26506595 : Blo 1488064 26506595 := bstep (se 1 (by rfl) ⟨19879946, by rfl⟩ : syracuseStep 26506595 = 39759893) B39759893
theorem B1488235 : Blo 1488064 1488235 := bstep (se 1 (by rfl) ⟨1116176, by rfl⟩ : syracuseStep 1488235 = 2232353) B2232353
theorem B1488247 : Blo 1488064 1488247 := bstep (se 1 (by rfl) ⟨1116185, by rfl⟩ : syracuseStep 1488247 = 2232371) B2232371
theorem B1488267 : Blo 1488064 1488267 := bstep (se 1 (by rfl) ⟨1116200, by rfl⟩ : syracuseStep 1488267 = 2232401) B2232401
theorem B2233739 : Blo 1488064 2233739 := bstep (se 1 (by rfl) ⟨1675304, by rfl⟩ : syracuseStep 2233739 = 3350609) B3350609
theorem B1488279 : Blo 1488064 1488279 := bstep (se 1 (by rfl) ⟨1116209, by rfl⟩ : syracuseStep 1488279 = 2232419) B2232419
theorem B2233751 : Blo 1488064 2233751 := bstep (se 1 (by rfl) ⟨1675313, by rfl⟩ : syracuseStep 2233751 = 3350627) B3350627
theorem B1488299 : Blo 1488064 1488299 := bstep (se 1 (by rfl) ⟨1116224, by rfl⟩ : syracuseStep 1488299 = 2232449) B2232449
theorem B3626419 : Blo 1488064 3626419 := bstep (se 1 (by rfl) ⟨2719814, by rfl⟩ : syracuseStep 3626419 = 5439629) B5439629
theorem B1488311 : Blo 1488064 1488311 := bstep (se 1 (by rfl) ⟨1116233, by rfl⟩ : syracuseStep 1488311 = 2232467) B2232467
theorem B1488331 : Blo 1488064 1488331 := bstep (se 1 (by rfl) ⟨1116248, by rfl⟩ : syracuseStep 1488331 = 2232497) B2232497
theorem B1488343 : Blo 1488064 1488343 := bstep (se 1 (by rfl) ⟨1116257, by rfl⟩ : syracuseStep 1488343 = 2232515) B2232515
theorem B2512343 : Blo 1488064 2512343 := bstep (se 1 (by rfl) ⟨1884257, by rfl⟩ : syracuseStep 2512343 = 3768515) B3768515
theorem B2233817 : Blo 1488064 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B7542233 : Blo 1488064 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B1488363 : Blo 1488064 1488363 := bstep (se 1 (by rfl) ⟨1116272, by rfl⟩ : syracuseStep 1488363 = 2232545) B2232545
theorem B1488375 : Blo 1488064 1488375 := bstep (se 1 (by rfl) ⟨1116281, by rfl⟩ : syracuseStep 1488375 = 2232563) B2232563
theorem B1488395 : Blo 1488064 1488395 := bstep (se 1 (by rfl) ⟨1116296, by rfl⟩ : syracuseStep 1488395 = 2232593) B2232593
theorem B1488407 : Blo 1488064 1488407 := bstep (se 1 (by rfl) ⟨1116305, by rfl⟩ : syracuseStep 1488407 = 2232611) B2232611
theorem B1488427 : Blo 1488064 1488427 := bstep (se 1 (by rfl) ⟨1116320, by rfl⟩ : syracuseStep 1488427 = 2232641) B2232641
theorem B1488439 : Blo 1488064 1488439 := bstep (se 1 (by rfl) ⟨1116329, by rfl⟩ : syracuseStep 1488439 = 2232659) B2232659
theorem B1488459 : Blo 1488064 1488459 := bstep (se 1 (by rfl) ⟨1116344, by rfl⟩ : syracuseStep 1488459 = 2232689) B2232689
theorem B2233931 : Blo 1488064 2233931 := bstep (se 1 (by rfl) ⟨1675448, by rfl⟩ : syracuseStep 2233931 = 3350897) B3350897
theorem B1488471 : Blo 1488064 1488471 := bstep (se 1 (by rfl) ⟨1116353, by rfl⟩ : syracuseStep 1488471 = 2232707) B2232707
theorem B2512471 : Blo 1488064 2512471 := bstep (se 1 (by rfl) ⟨1884353, by rfl⟩ : syracuseStep 2512471 = 3768707) B3768707
theorem B2233943 : Blo 1488064 2233943 := bstep (se 1 (by rfl) ⟨1675457, by rfl⟩ : syracuseStep 2233943 = 3350915) B3350915
theorem B1488491 : Blo 1488064 1488491 := bstep (se 1 (by rfl) ⟨1116368, by rfl⟩ : syracuseStep 1488491 = 2232737) B2232737
theorem B1488503 : Blo 1488064 1488503 := bstep (se 1 (by rfl) ⟨1116377, by rfl⟩ : syracuseStep 1488503 = 2232755) B2232755
theorem B1488523 : Blo 1488064 1488523 := bstep (se 1 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 1488523 = 2232785) B2232785
theorem B1488535 : Blo 1488064 1488535 := bstep (se 1 (by rfl) ⟨1116401, by rfl⟩ : syracuseStep 1488535 = 2232803) B2232803
theorem B2234009 : Blo 1488064 2234009 := bstep (se 2 (by rfl) ⟨837753, by rfl⟩ : syracuseStep 2234009 = 1675507) B1675507
theorem B1488555 : Blo 1488064 1488555 := bstep (se 1 (by rfl) ⟨1116416, by rfl⟩ : syracuseStep 1488555 = 2232833) B2232833
theorem B6362803 : Blo 1488064 6362803 := bstep (se 1 (by rfl) ⟨4772102, by rfl⟩ : syracuseStep 6362803 = 9544205) B9544205
theorem B5027507 : Blo 1488064 5027507 := bstep (se 1 (by rfl) ⟨3770630, by rfl⟩ : syracuseStep 5027507 = 7541261) B7541261
theorem B1488567 : Blo 1488064 1488567 := bstep (se 1 (by rfl) ⟨1116425, by rfl⟩ : syracuseStep 1488567 = 2232851) B2232851
theorem B3348161 : Blo 1488064 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B1488587 : Blo 1488064 1488587 := bstep (se 1 (by rfl) ⟨1116440, by rfl⟩ : syracuseStep 1488587 = 2232881) B2232881
theorem B32184013 : Blo 1488064 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B1488599 : Blo 1488064 1488599 := bstep (se 1 (by rfl) ⟨1116449, by rfl⟩ : syracuseStep 1488599 = 2232899) B2232899
theorem B1488619 : Blo 1488064 1488619 := bstep (se 1 (by rfl) ⟨1116464, by rfl⟩ : syracuseStep 1488619 = 2232929) B2232929
theorem B1488631 : Blo 1488064 1488631 := bstep (se 1 (by rfl) ⟨1116473, by rfl⟩ : syracuseStep 1488631 = 2232947) B2232947
theorem B1488651 : Blo 1488064 1488651 := bstep (se 1 (by rfl) ⟨1116488, by rfl⟩ : syracuseStep 1488651 = 2232977) B2232977
theorem B2234123 : Blo 1488064 2234123 := bstep (se 1 (by rfl) ⟨1675592, by rfl⟩ : syracuseStep 2234123 = 3351185) B3351185
theorem B1488663 : Blo 1488064 1488663 := bstep (se 1 (by rfl) ⟨1116497, by rfl⟩ : syracuseStep 1488663 = 2232995) B2232995
theorem B2234135 : Blo 1488064 2234135 := bstep (se 1 (by rfl) ⟨1675601, by rfl⟩ : syracuseStep 2234135 = 3351203) B3351203
theorem B1488683 : Blo 1488064 1488683 := bstep (se 1 (by rfl) ⟨1116512, by rfl⟩ : syracuseStep 1488683 = 2233025) B2233025
theorem B1488695 : Blo 1488064 1488695 := bstep (se 1 (by rfl) ⟨1116521, by rfl⟩ : syracuseStep 1488695 = 2233043) B2233043
theorem B1488715 : Blo 1488064 1488715 := bstep (se 1 (by rfl) ⟨1116536, by rfl⟩ : syracuseStep 1488715 = 2233073) B2233073
theorem B1488727 : Blo 1488064 1488727 := bstep (se 1 (by rfl) ⟨1116545, by rfl⟩ : syracuseStep 1488727 = 2233091) B2233091
theorem B2234201 : Blo 1488064 2234201 := bstep (se 2 (by rfl) ⟨837825, by rfl⟩ : syracuseStep 2234201 = 1675651) B1675651
theorem B40728419 : Blo 1488064 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B34363237 : Blo 1488064 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B1488747 : Blo 1488064 1488747 := bstep (se 1 (by rfl) ⟨1116560, by rfl⟩ : syracuseStep 1488747 = 2233121) B2233121
theorem B1488759 : Blo 1488064 1488759 := bstep (se 1 (by rfl) ⟨1116569, by rfl⟩ : syracuseStep 1488759 = 2233139) B2233139
theorem B1488779 : Blo 1488064 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B1488791 : Blo 1488064 1488791 := bstep (se 1 (by rfl) ⟨1116593, by rfl⟩ : syracuseStep 1488791 = 2233187) B2233187
theorem B3348377 : Blo 1488064 3348377 := bstep (se 2 (by rfl) ⟨1255641, by rfl⟩ : syracuseStep 3348377 = 2511283) B2511283
theorem B1488811 : Blo 1488064 1488811 := bstep (se 1 (by rfl) ⟨1116608, by rfl⟩ : syracuseStep 1488811 = 2233217) B2233217
theorem B1488823 : Blo 1488064 1488823 := bstep (se 1 (by rfl) ⟨1116617, by rfl⟩ : syracuseStep 1488823 = 2233235) B2233235
theorem B5027777 : Blo 1488064 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B1488843 : Blo 1488064 1488843 := bstep (se 1 (by rfl) ⟨1116632, by rfl⟩ : syracuseStep 1488843 = 2233265) B2233265
theorem B2234315 : Blo 1488064 2234315 := bstep (se 1 (by rfl) ⟨1675736, by rfl⟩ : syracuseStep 2234315 = 3351473) B3351473
theorem B1488855 : Blo 1488064 1488855 := bstep (se 1 (by rfl) ⟨1116641, by rfl⟩ : syracuseStep 1488855 = 2233283) B2233283
theorem B2234327 : Blo 1488064 2234327 := bstep (se 1 (by rfl) ⟨1675745, by rfl⟩ : syracuseStep 2234327 = 3351491) B3351491
theorem B1488875 : Blo 1488064 1488875 := bstep (se 1 (by rfl) ⟨1116656, by rfl⟩ : syracuseStep 1488875 = 2233313) B2233313
theorem B3348467 : Blo 1488064 3348467 := bstep (se 1 (by rfl) ⟨2511350, by rfl⟩ : syracuseStep 3348467 = 5022701) B5022701
theorem B1488887 : Blo 1488064 1488887 := bstep (se 1 (by rfl) ⟨1116665, by rfl⟩ : syracuseStep 1488887 = 2233331) B2233331
theorem B1488907 : Blo 1488064 1488907 := bstep (se 1 (by rfl) ⟨1116680, by rfl⟩ : syracuseStep 1488907 = 2233361) B2233361
theorem B3348503 : Blo 1488064 3348503 := bstep (se 1 (by rfl) ⟨2511377, by rfl⟩ : syracuseStep 3348503 = 5022755) B5022755
theorem B1488919 : Blo 1488064 1488919 := bstep (se 1 (by rfl) ⟨1116689, by rfl⟩ : syracuseStep 1488919 = 2233379) B2233379
theorem B2234393 : Blo 1488064 2234393 := bstep (se 2 (by rfl) ⟨837897, by rfl⟩ : syracuseStep 2234393 = 1675795) B1675795
theorem B1488939 : Blo 1488064 1488939 := bstep (se 1 (by rfl) ⟨1116704, by rfl⟩ : syracuseStep 1488939 = 2233409) B2233409
theorem B4241459 : Blo 1488064 4241459 := bstep (se 1 (by rfl) ⟨3181094, by rfl⟩ : syracuseStep 4241459 = 6362189) B6362189
theorem B1488951 : Blo 1488064 1488951 := bstep (se 1 (by rfl) ⟨1116713, by rfl⟩ : syracuseStep 1488951 = 2233427) B2233427
theorem B1488971 : Blo 1488064 1488971 := bstep (se 1 (by rfl) ⟨1116728, by rfl⟩ : syracuseStep 1488971 = 2233457) B2233457
theorem B1488983 : Blo 1488064 1488983 := bstep (se 1 (by rfl) ⟨1116737, by rfl⟩ : syracuseStep 1488983 = 2233475) B2233475
theorem B1489003 : Blo 1488064 1489003 := bstep (se 1 (by rfl) ⟨1116752, by rfl⟩ : syracuseStep 1489003 = 2233505) B2233505
theorem B1489015 : Blo 1488064 1489015 := bstep (se 1 (by rfl) ⟨1116761, by rfl⟩ : syracuseStep 1489015 = 2233523) B2233523
theorem B1489035 : Blo 1488064 1489035 := bstep (se 1 (by rfl) ⟨1116776, by rfl⟩ : syracuseStep 1489035 = 2233553) B2233553
theorem B2234507 : Blo 1488064 2234507 := bstep (se 1 (by rfl) ⟨1675880, by rfl⟩ : syracuseStep 2234507 = 3351761) B3351761
theorem B1489047 : Blo 1488064 1489047 := bstep (se 1 (by rfl) ⟨1116785, by rfl⟩ : syracuseStep 1489047 = 2233571) B2233571
theorem B2234519 : Blo 1488064 2234519 := bstep (se 1 (by rfl) ⟨1675889, by rfl⟩ : syracuseStep 2234519 = 3351779) B3351779
theorem B1489067 : Blo 1488064 1489067 := bstep (se 1 (by rfl) ⟨1116800, by rfl⟩ : syracuseStep 1489067 = 2233601) B2233601
theorem B1489079 : Blo 1488064 1489079 := bstep (se 1 (by rfl) ⟨1116809, by rfl⟩ : syracuseStep 1489079 = 2233619) B2233619
theorem B3348683 : Blo 1488064 3348683 := bstep (se 1 (by rfl) ⟨2511512, by rfl⟩ : syracuseStep 3348683 = 5023025) B5023025
theorem B1489099 : Blo 1488064 1489099 := bstep (se 1 (by rfl) ⟨1116824, by rfl⟩ : syracuseStep 1489099 = 2233649) B2233649
theorem B2513099 : Blo 1488064 2513099 := bstep (se 1 (by rfl) ⟨1884824, by rfl⟩ : syracuseStep 2513099 = 3769649) B3769649
theorem B1489111 : Blo 1488064 1489111 := bstep (se 1 (by rfl) ⟨1116833, by rfl⟩ : syracuseStep 1489111 = 2233667) B2233667
theorem B2234585 : Blo 1488064 2234585 := bstep (se 2 (by rfl) ⟨837969, by rfl⟩ : syracuseStep 2234585 = 1675939) B1675939
theorem B1489131 : Blo 1488064 1489131 := bstep (se 1 (by rfl) ⟨1116848, by rfl⟩ : syracuseStep 1489131 = 2233697) B2233697
theorem B1489143 : Blo 1488064 1489143 := bstep (se 1 (by rfl) ⟨1116857, by rfl⟩ : syracuseStep 1489143 = 2233715) B2233715
theorem B3348737 : Blo 1488064 3348737 := bstep (se 2 (by rfl) ⟨1255776, by rfl⟩ : syracuseStep 3348737 = 2511553) B2511553
theorem B1489163 : Blo 1488064 1489163 := bstep (se 1 (by rfl) ⟨1116872, by rfl⟩ : syracuseStep 1489163 = 2233745) B2233745
theorem B1489175 : Blo 1488064 1489175 := bstep (se 1 (by rfl) ⟨1116881, by rfl⟩ : syracuseStep 1489175 = 2233763) B2233763
theorem B1489195 : Blo 1488064 1489195 := bstep (se 1 (by rfl) ⟨1116896, by rfl⟩ : syracuseStep 1489195 = 2233793) B2233793
theorem B8476973 : Blo 1488064 8476973 := bstep (se 3 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 8476973 = 3178865) B3178865
theorem B1489207 : Blo 1488064 1489207 := bstep (se 1 (by rfl) ⟨1116905, by rfl⟩ : syracuseStep 1489207 = 2233811) B2233811
theorem B1489227 : Blo 1488064 1489227 := bstep (se 1 (by rfl) ⟨1116920, by rfl⟩ : syracuseStep 1489227 = 2233841) B2233841
theorem B2513227 : Blo 1488064 2513227 := bstep (se 1 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 2513227 = 3769841) B3769841
theorem B2234699 : Blo 1488064 2234699 := bstep (se 1 (by rfl) ⟨1676024, by rfl⟩ : syracuseStep 2234699 = 3352049) B3352049
theorem B8485195 : Blo 1488064 8485195 := bstep (se 1 (by rfl) ⟨6363896, by rfl⟩ : syracuseStep 8485195 = 12727793) B12727793
theorem B2120023 : Blo 1488064 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B1489239 : Blo 1488064 1489239 := bstep (se 1 (by rfl) ⟨1116929, by rfl⟩ : syracuseStep 1489239 = 2233859) B2233859
theorem B2234711 : Blo 1488064 2234711 := bstep (se 1 (by rfl) ⟨1676033, by rfl⟩ : syracuseStep 2234711 = 3352067) B3352067
theorem B1489259 : Blo 1488064 1489259 := bstep (se 1 (by rfl) ⟨1116944, by rfl⟩ : syracuseStep 1489259 = 2233889) B2233889
theorem B1489271 : Blo 1488064 1489271 := bstep (se 1 (by rfl) ⟨1116953, by rfl⟩ : syracuseStep 1489271 = 2233907) B2233907
theorem B1489291 : Blo 1488064 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B5364119 : Blo 1488064 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B1489303 : Blo 1488064 1489303 := bstep (se 1 (by rfl) ⟨1116977, by rfl⟩ : syracuseStep 1489303 = 2233955) B2233955
theorem B2234777 : Blo 1488064 2234777 := bstep (se 2 (by rfl) ⟨838041, by rfl⟩ : syracuseStep 2234777 = 1676083) B1676083
theorem B1489323 : Blo 1488064 1489323 := bstep (se 1 (by rfl) ⟨1116992, by rfl⟩ : syracuseStep 1489323 = 2233985) B2233985
theorem B1489335 : Blo 1488064 1489335 := bstep (se 1 (by rfl) ⟨1117001, by rfl⟩ : syracuseStep 1489335 = 2234003) B2234003
theorem B6035915 : Blo 1488064 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B1489355 : Blo 1488064 1489355 := bstep (se 1 (by rfl) ⟨1117016, by rfl⟩ : syracuseStep 1489355 = 2234033) B2234033
theorem B1489367 : Blo 1488064 1489367 := bstep (se 1 (by rfl) ⟨1117025, by rfl⟩ : syracuseStep 1489367 = 2234051) B2234051
theorem B3348953 : Blo 1488064 3348953 := bstep (se 2 (by rfl) ⟨1255857, by rfl⟩ : syracuseStep 3348953 = 2511715) B2511715
theorem B2513369 : Blo 1488064 2513369 := bstep (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) B1885027
theorem B7158233 : Blo 1488064 7158233 := bstep (se 2 (by rfl) ⟨2684337, by rfl⟩ : syracuseStep 7158233 = 5368675) B5368675
theorem B5028317 : Blo 1488064 5028317 := bstep (se 3 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 5028317 = 1885619) B1885619
theorem B1489387 : Blo 1488064 1489387 := bstep (se 1 (by rfl) ⟨1117040, by rfl⟩ : syracuseStep 1489387 = 2234081) B2234081
theorem B1489399 : Blo 1488064 1489399 := bstep (se 1 (by rfl) ⟨1117049, by rfl⟩ : syracuseStep 1489399 = 2234099) B2234099
theorem B1489419 : Blo 1488064 1489419 := bstep (se 1 (by rfl) ⟨1117064, by rfl⟩ : syracuseStep 1489419 = 2234129) B2234129
theorem B2234891 : Blo 1488064 2234891 := bstep (se 1 (by rfl) ⟨1676168, by rfl⟩ : syracuseStep 2234891 = 3352337) B3352337
theorem B2013707 : Blo 1488064 2013707 := bstep (se 1 (by rfl) ⟨1510280, by rfl⟩ : syracuseStep 2013707 = 3020561) B3020561
theorem B1489431 : Blo 1488064 1489431 := bstep (se 1 (by rfl) ⟨1117073, by rfl⟩ : syracuseStep 1489431 = 2234147) B2234147
theorem B2234903 : Blo 1488064 2234903 := bstep (se 1 (by rfl) ⟨1676177, by rfl⟩ : syracuseStep 2234903 = 3352355) B3352355
theorem B1489451 : Blo 1488064 1489451 := bstep (se 1 (by rfl) ⟨1117088, by rfl⟩ : syracuseStep 1489451 = 2234177) B2234177
theorem B12720685 : Blo 1488064 12720685 := bstep (se 3 (by rfl) ⟨2385128, by rfl⟩ : syracuseStep 12720685 = 4770257) B4770257
theorem B3349043 : Blo 1488064 3349043 := bstep (se 1 (by rfl) ⟨2511782, by rfl⟩ : syracuseStep 3349043 = 5023565) B5023565
theorem B1489463 : Blo 1488064 1489463 := bstep (se 1 (by rfl) ⟨1117097, by rfl⟩ : syracuseStep 1489463 = 2234195) B2234195
theorem B1489483 : Blo 1488064 1489483 := bstep (se 1 (by rfl) ⟨1117112, by rfl⟩ : syracuseStep 1489483 = 2234225) B2234225
theorem B3349079 : Blo 1488064 3349079 := bstep (se 1 (by rfl) ⟨2511809, by rfl⟩ : syracuseStep 3349079 = 5023619) B5023619
theorem B1489495 : Blo 1488064 1489495 := bstep (se 1 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 1489495 = 2234243) B2234243
theorem B2513497 : Blo 1488064 2513497 := bstep (se 2 (by rfl) ⟨942561, by rfl⟩ : syracuseStep 2513497 = 1885123) B1885123
theorem B2234969 : Blo 1488064 2234969 := bstep (se 2 (by rfl) ⟨838113, by rfl⟩ : syracuseStep 2234969 = 1676227) B1676227
theorem B8485469 : Blo 1488064 8485469 := bstep (se 3 (by rfl) ⟨1591025, by rfl⟩ : syracuseStep 8485469 = 3182051) B3182051
theorem B1489515 : Blo 1488064 1489515 := bstep (se 1 (by rfl) ⟨1117136, by rfl⟩ : syracuseStep 1489515 = 2234273) B2234273
theorem B1489527 : Blo 1488064 1489527 := bstep (se 1 (by rfl) ⟨1117145, by rfl⟩ : syracuseStep 1489527 = 2234291) B2234291
theorem B1489547 : Blo 1488064 1489547 := bstep (se 1 (by rfl) ⟨1117160, by rfl⟩ : syracuseStep 1489547 = 2234321) B2234321
theorem B1489559 : Blo 1488064 1489559 := bstep (se 1 (by rfl) ⟨1117169, by rfl⟩ : syracuseStep 1489559 = 2234339) B2234339
theorem B1489579 : Blo 1488064 1489579 := bstep (se 1 (by rfl) ⟨1117184, by rfl⟩ : syracuseStep 1489579 = 2234369) B2234369
theorem B5651117 : Blo 1488064 5651117 := bstep (se 3 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 5651117 = 2119169) B2119169
theorem B1489591 : Blo 1488064 1489591 := bstep (se 1 (by rfl) ⟨1117193, by rfl⟩ : syracuseStep 1489591 = 2234387) B2234387
theorem B5651147 : Blo 1488064 5651147 := bstep (se 1 (by rfl) ⟨4238360, by rfl⟩ : syracuseStep 5651147 = 8476721) B8476721
theorem B1489611 : Blo 1488064 1489611 := bstep (se 1 (by rfl) ⟨1117208, by rfl⟩ : syracuseStep 1489611 = 2234417) B2234417
theorem B2235083 : Blo 1488064 2235083 := bstep (se 1 (by rfl) ⟨1676312, by rfl⟩ : syracuseStep 2235083 = 3352625) B3352625
theorem B1489623 : Blo 1488064 1489623 := bstep (se 1 (by rfl) ⟨1117217, by rfl⟩ : syracuseStep 1489623 = 2234435) B2234435
theorem B2235095 : Blo 1488064 2235095 := bstep (se 1 (by rfl) ⟨1676321, by rfl⟩ : syracuseStep 2235095 = 3352643) B3352643
theorem B1489643 : Blo 1488064 1489643 := bstep (se 1 (by rfl) ⟨1117232, by rfl⟩ : syracuseStep 1489643 = 2234465) B2234465
theorem B1489655 : Blo 1488064 1489655 := bstep (se 1 (by rfl) ⟨1117241, by rfl⟩ : syracuseStep 1489655 = 2234483) B2234483
theorem B3349259 : Blo 1488064 3349259 := bstep (se 1 (by rfl) ⟨2511944, by rfl⟩ : syracuseStep 3349259 = 5023889) B5023889
theorem B1489675 : Blo 1488064 1489675 := bstep (se 1 (by rfl) ⟨1117256, by rfl⟩ : syracuseStep 1489675 = 2234513) B2234513
theorem B1489687 : Blo 1488064 1489687 := bstep (se 1 (by rfl) ⟨1117265, by rfl⟩ : syracuseStep 1489687 = 2234531) B2234531
theorem B1489707 : Blo 1488064 1489707 := bstep (se 1 (by rfl) ⟨1117280, by rfl⟩ : syracuseStep 1489707 = 2234561) B2234561
theorem B1489719 : Blo 1488064 1489719 := bstep (se 1 (by rfl) ⟨1117289, by rfl⟩ : syracuseStep 1489719 = 2234579) B2234579
theorem B3349313 : Blo 1488064 3349313 := bstep (se 2 (by rfl) ⟨1255992, by rfl⟩ : syracuseStep 3349313 = 2511985) B2511985
theorem B1489739 : Blo 1488064 1489739 := bstep (se 1 (by rfl) ⟨1117304, by rfl⟩ : syracuseStep 1489739 = 2234609) B2234609
theorem B1489751 : Blo 1488064 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B1489771 : Blo 1488064 1489771 := bstep (se 1 (by rfl) ⟨1117328, by rfl⟩ : syracuseStep 1489771 = 2234657) B2234657
theorem B1489783 : Blo 1488064 1489783 := bstep (se 1 (by rfl) ⟨1117337, by rfl⟩ : syracuseStep 1489783 = 2234675) B2234675
theorem B1489803 : Blo 1488064 1489803 := bstep (se 1 (by rfl) ⟨1117352, by rfl⟩ : syracuseStep 1489803 = 2234705) B2234705
theorem B2825111 : Blo 1488064 2825111 := bstep (se 1 (by rfl) ⟨2118833, by rfl⟩ : syracuseStep 2825111 = 4237667) B4237667
theorem B1489815 : Blo 1488064 1489815 := bstep (se 1 (by rfl) ⟨1117361, by rfl⟩ : syracuseStep 1489815 = 2234723) B2234723
theorem B1489835 : Blo 1488064 1489835 := bstep (se 1 (by rfl) ⟨1117376, by rfl⟩ : syracuseStep 1489835 = 2234753) B2234753
theorem B3767219 : Blo 1488064 3767219 := bstep (se 1 (by rfl) ⟨2825414, by rfl⟩ : syracuseStep 3767219 = 5650829) B5650829
theorem B1489847 : Blo 1488064 1489847 := bstep (se 1 (by rfl) ⟨1117385, by rfl⟩ : syracuseStep 1489847 = 2234771) B2234771
theorem B1489867 : Blo 1488064 1489867 := bstep (se 1 (by rfl) ⟨1117400, by rfl⟩ : syracuseStep 1489867 = 2234801) B2234801
theorem B1489879 : Blo 1488064 1489879 := bstep (se 1 (by rfl) ⟨1117409, by rfl⟩ : syracuseStep 1489879 = 2234819) B2234819
theorem B1489899 : Blo 1488064 1489899 := bstep (se 1 (by rfl) ⟨1117424, by rfl⟩ : syracuseStep 1489899 = 2234849) B2234849
theorem B1489911 : Blo 1488064 1489911 := bstep (se 1 (by rfl) ⟨1117433, by rfl⟩ : syracuseStep 1489911 = 2234867) B2234867
theorem B1489931 : Blo 1488064 1489931 := bstep (se 1 (by rfl) ⟨1117448, by rfl⟩ : syracuseStep 1489931 = 2234897) B2234897
theorem B1489943 : Blo 1488064 1489943 := bstep (se 1 (by rfl) ⟨1117457, by rfl⟩ : syracuseStep 1489943 = 2234915) B2234915
theorem B3349529 : Blo 1488064 3349529 := bstep (se 2 (by rfl) ⟨1256073, by rfl⟩ : syracuseStep 3349529 = 2512147) B2512147
theorem B45849635 : Blo 1488064 45849635 := bstep (se 1 (by rfl) ⟨34387226, by rfl⟩ : syracuseStep 45849635 = 68774453) B68774453
theorem B1489963 : Blo 1488064 1489963 := bstep (se 1 (by rfl) ⟨1117472, by rfl⟩ : syracuseStep 1489963 = 2234945) B2234945
theorem B1489975 : Blo 1488064 1489975 := bstep (se 1 (by rfl) ⟨1117481, by rfl⟩ : syracuseStep 1489975 = 2234963) B2234963
theorem B1489995 : Blo 1488064 1489995 := bstep (se 1 (by rfl) ⟨1117496, by rfl⟩ : syracuseStep 1489995 = 2234993) B2234993
theorem B1490007 : Blo 1488064 1490007 := bstep (se 1 (by rfl) ⟨1117505, by rfl⟩ : syracuseStep 1490007 = 2235011) B2235011
theorem B1490027 : Blo 1488064 1490027 := bstep (se 1 (by rfl) ⟨1117520, by rfl⟩ : syracuseStep 1490027 = 2235041) B2235041
theorem B3349619 : Blo 1488064 3349619 := bstep (se 1 (by rfl) ⟨2512214, by rfl⟩ : syracuseStep 3349619 = 5024429) B5024429
theorem B1490039 : Blo 1488064 1490039 := bstep (se 1 (by rfl) ⟨1117529, by rfl⟩ : syracuseStep 1490039 = 2235059) B2235059
theorem B27909251 : Blo 1488064 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B6364291 : Blo 1488064 6364291 := bstep (se 1 (by rfl) ⟨4773218, by rfl⟩ : syracuseStep 6364291 = 9546437) B9546437
theorem B1490059 : Blo 1488064 1490059 := bstep (se 1 (by rfl) ⟨1117544, by rfl⟩ : syracuseStep 1490059 = 2235089) B2235089
theorem B3349655 : Blo 1488064 3349655 := bstep (se 1 (by rfl) ⟨2512241, by rfl⟩ : syracuseStep 3349655 = 5024483) B5024483
theorem B2514071 : Blo 1488064 2514071 := bstep (se 1 (by rfl) ⟨1885553, by rfl⟩ : syracuseStep 2514071 = 3771107) B3771107
theorem B1883351 : Blo 1488064 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B9542873 : Blo 1488064 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B2514199 : Blo 1488064 2514199 := bstep (se 1 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 2514199 = 3771299) B3771299
theorem B3349835 : Blo 1488064 3349835 := bstep (se 1 (by rfl) ⟨2512376, by rfl⟩ : syracuseStep 3349835 = 5024753) B5024753
theorem B5651801 : Blo 1488064 5651801 := bstep (se 2 (by rfl) ⟨2119425, by rfl⟩ : syracuseStep 5651801 = 4238851) B4238851
theorem B3349889 : Blo 1488064 3349889 := bstep (se 2 (by rfl) ⟨1256208, by rfl⟩ : syracuseStep 3349889 = 2512417) B2512417
theorem B10190231 : Blo 1488064 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B16317875 : Blo 1488064 16317875 := bstep (se 1 (by rfl) ⟨12238406, by rfl⟩ : syracuseStep 16317875 = 24476813) B24476813
theorem B3767755 : Blo 1488064 3767755 := bstep (se 1 (by rfl) ⟨2825816, by rfl⟩ : syracuseStep 3767755 = 5651633) B5651633
theorem B28614161 : Blo 1488064 28614161 := bstep (se 2 (by rfl) ⟨10730310, by rfl⟩ : syracuseStep 28614161 = 21460621) B21460621
theorem B6037037 : Blo 1488064 6037037 := bstep (se 3 (by rfl) ⟨1131944, by rfl⟩ : syracuseStep 6037037 = 2263889) B2263889
theorem B2825779 : Blo 1488064 2825779 := bstep (se 1 (by rfl) ⟨2119334, by rfl⟩ : syracuseStep 2825779 = 4238669) B4238669
theorem B3767897 : Blo 1488064 3767897 := bstep (se 2 (by rfl) ⟨1412961, by rfl⟩ : syracuseStep 3767897 = 2825923) B2825923
theorem B3350105 : Blo 1488064 3350105 := bstep (se 2 (by rfl) ⟨1256289, by rfl⟩ : syracuseStep 3350105 = 2512579) B2512579
theorem B3579481 : Blo 1488064 3579481 := bstep (se 2 (by rfl) ⟨1342305, by rfl⟩ : syracuseStep 3579481 = 2684611) B2684611
theorem B5652119 : Blo 1488064 5652119 := bstep (se 1 (by rfl) ⟨4239089, by rfl⟩ : syracuseStep 5652119 = 8478179) B8478179
theorem B3350195 : Blo 1488064 3350195 := bstep (se 1 (by rfl) ⟨2512646, by rfl⟩ : syracuseStep 3350195 = 5025293) B5025293
theorem B3350231 : Blo 1488064 3350231 := bstep (se 1 (by rfl) ⟨2512673, by rfl⟩ : syracuseStep 3350231 = 5025347) B5025347
theorem B7536401 : Blo 1488064 7536401 := bstep (se 2 (by rfl) ⟨2826150, by rfl⟩ : syracuseStep 7536401 = 5652301) B5652301
theorem B6356825 : Blo 1488064 6356825 := bstep (se 2 (by rfl) ⟨2383809, by rfl⟩ : syracuseStep 6356825 = 4767619) B4767619
theorem B12722021 : Blo 1488064 12722021 := bstep (se 4 (by rfl) ⟨1192689, by rfl⟩ : syracuseStep 12722021 = 2385379) B2385379
theorem B3350411 : Blo 1488064 3350411 := bstep (se 1 (by rfl) ⟨2512808, by rfl⟩ : syracuseStep 3350411 = 5025617) B5025617
theorem B1884055 : Blo 1488064 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B34373555 : Blo 1488064 34373555 := bstep (se 1 (by rfl) ⟨25780166, by rfl⟩ : syracuseStep 34373555 = 51560333) B51560333
theorem B7536563 : Blo 1488064 7536563 := bstep (se 1 (by rfl) ⟨5652422, by rfl⟩ : syracuseStep 7536563 = 11304845) B11304845
theorem B3350465 : Blo 1488064 3350465 := bstep (se 2 (by rfl) ⟨1256424, by rfl⟩ : syracuseStep 3350465 = 2512849) B2512849
theorem B2826227 : Blo 1488064 2826227 := bstep (se 1 (by rfl) ⟨2119670, by rfl⟩ : syracuseStep 2826227 = 4239341) B4239341
theorem B5160971 : Blo 1488064 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B16097291 : Blo 1488064 16097291 := bstep (se 1 (by rfl) ⟨12072968, by rfl⟩ : syracuseStep 16097291 = 24145937) B24145937
theorem B3768353 : Blo 1488064 3768353 := bstep (se 2 (by rfl) ⟨1413132, by rfl⟩ : syracuseStep 3768353 = 2826265) B2826265
theorem B8052797 : Blo 1488064 8052797 := bstep (se 3 (by rfl) ⟨1509899, by rfl⟩ : syracuseStep 8052797 = 3019799) B3019799
theorem B3350663 : Blo 1488064 3350663 := bstep (se 1 (by rfl) ⟨2512997, by rfl⟩ : syracuseStep 3350663 = 5025995) B5025995
theorem B3678475 : Blo 1488064 3678475 := bstep (se 1 (by rfl) ⟨2758856, by rfl⟩ : syracuseStep 3678475 = 5517713) B5517713
theorem B1884475 : Blo 1488064 1884475 := bstep (se 1 (by rfl) ⟨1413356, by rfl⟩ : syracuseStep 1884475 = 2826713) B2826713
theorem B3350843 : Blo 1488064 3350843 := bstep (se 1 (by rfl) ⟨2513132, by rfl⟩ : syracuseStep 3350843 = 5026265) B5026265
theorem B4022615 : Blo 1488064 4022615 := bstep (se 1 (by rfl) ⟨3016961, by rfl⟩ : syracuseStep 4022615 = 6033923) B6033923
theorem B7537049 : Blo 1488064 7537049 := bstep (se 2 (by rfl) ⟨2826393, by rfl⟩ : syracuseStep 7537049 = 5652787) B5652787
theorem B3350969 : Blo 1488064 3350969 := bstep (se 2 (by rfl) ⟨1256613, by rfl⟩ : syracuseStep 3350969 = 2513227) B2513227
theorem B11313593 : Blo 1488064 11313593 := bstep (se 2 (by rfl) ⟨4242597, by rfl⟩ : syracuseStep 11313593 = 8485195) B8485195
theorem B4587977 : Blo 1488064 4587977 := bstep (se 2 (by rfl) ⟨1720491, by rfl⟩ : syracuseStep 4587977 = 3440983) B3440983
theorem B5022269 : Blo 1488064 5022269 := bstep (se 3 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 5022269 = 1883351) B1883351
theorem B16089677 : Blo 1488064 16089677 := bstep (se 3 (by rfl) ⟨3016814, by rfl⟩ : syracuseStep 16089677 = 6033629) B6033629
theorem B14320385 : Blo 1488064 14320385 := bstep (se 2 (by rfl) ⟨5370144, by rfl⟩ : syracuseStep 14320385 = 10740289) B10740289
theorem B3351311 : Blo 1488064 3351311 := bstep (se 1 (by rfl) ⟨2513483, by rfl⟩ : syracuseStep 3351311 = 5026967) B5026967
theorem B9544463 : Blo 1488064 9544463 := bstep (se 1 (by rfl) ⟨7158347, by rfl⟩ : syracuseStep 9544463 = 14316695) B14316695
theorem B3351329 : Blo 1488064 3351329 := bstep (se 2 (by rfl) ⟨1256748, by rfl⟩ : syracuseStep 3351329 = 2513497) B2513497
theorem B28312355 : Blo 1488064 28312355 := bstep (se 1 (by rfl) ⟨21234266, by rfl⟩ : syracuseStep 28312355 = 42468533) B42468533
theorem B1884971 : Blo 1488064 1884971 := bstep (se 1 (by rfl) ⟨1413728, by rfl⟩ : syracuseStep 1884971 = 2827457) B2827457
theorem B11305817 : Blo 1488064 11305817 := bstep (se 2 (by rfl) ⟨4239681, by rfl⟩ : syracuseStep 11305817 = 8479363) B8479363
theorem B4023175 : Blo 1488064 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B17671063 : Blo 1488064 17671063 := bstep (se 1 (by rfl) ⟨13253297, by rfl⟩ : syracuseStep 17671063 = 26506595) B26506595
theorem B3769355 : Blo 1488064 3769355 := bstep (se 1 (by rfl) ⟨2827016, by rfl⟩ : syracuseStep 3769355 = 5654033) B5654033
theorem B5653547 : Blo 1488064 5653547 := bstep (se 1 (by rfl) ⟨4240160, by rfl⟩ : syracuseStep 5653547 = 8480321) B8480321
theorem B3351671 : Blo 1488064 3351671 := bstep (se 1 (by rfl) ⟨2513753, by rfl⟩ : syracuseStep 3351671 = 5027507) B5027507
theorem B3818753 : Blo 1488064 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1885447 : Blo 1488064 1885447 := bstep (se 1 (by rfl) ⟨1414085, by rfl⟩ : syracuseStep 1885447 = 2828171) B2828171
theorem B3351851 : Blo 1488064 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B16106845 : Blo 1488064 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B2827639 : Blo 1488064 2827639 := bstep (se 1 (by rfl) ⟨2120729, by rfl⟩ : syracuseStep 2827639 = 4241459) B4241459
theorem B3770003 : Blo 1488064 3770003 := bstep (se 1 (by rfl) ⟨2827502, by rfl⟩ : syracuseStep 3770003 = 5655005) B5655005
theorem B3352211 : Blo 1488064 3352211 := bstep (se 1 (by rfl) ⟨2514158, by rfl⟩ : syracuseStep 3352211 = 5028317) B5028317
theorem B3352265 : Blo 1488064 3352265 := bstep (se 2 (by rfl) ⟨1257099, by rfl⟩ : syracuseStep 3352265 = 2514199) B2514199
theorem B11306789 : Blo 1488064 11306789 := bstep (se 4 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 11306789 = 2120023) B2120023
theorem B4835225 : Blo 1488064 4835225 := bstep (se 2 (by rfl) ⟨1813209, by rfl⟩ : syracuseStep 4835225 = 3626419) B3626419
theorem B5023673 : Blo 1488064 5023673 := bstep (se 2 (by rfl) ⟨1883877, by rfl⟩ : syracuseStep 5023673 = 3767755) B3767755
theorem B3770297 : Blo 1488064 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B30566423 : Blo 1488064 30566423 := bstep (se 1 (by rfl) ⟨22924817, by rfl⟩ : syracuseStep 30566423 = 45849635) B45849635
theorem B18606167 : Blo 1488064 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B6793487 : Blo 1488064 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B42912017 : Blo 1488064 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B1788203 : Blo 1488064 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B4024637 : Blo 1488064 4024637 := bstep (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) B1509239
theorem B4024691 : Blo 1488064 4024691 := bstep (se 1 (by rfl) ⟨3018518, by rfl⟩ : syracuseStep 4024691 = 6037037) B6037037
theorem B16107923 : Blo 1488064 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B5024267 : Blo 1488064 5024267 := bstep (se 1 (by rfl) ⟨3768200, by rfl⟩ : syracuseStep 5024267 = 7536401) B7536401
theorem B4237883 : Blo 1488064 4237883 := bstep (se 1 (by rfl) ⟨3178412, by rfl⟩ : syracuseStep 4237883 = 6356825) B6356825
theorem B8481347 : Blo 1488064 8481347 := bstep (se 1 (by rfl) ⟨6361010, by rfl⟩ : syracuseStep 8481347 = 12722021) B12722021
theorem B3770995 : Blo 1488064 3770995 := bstep (se 1 (by rfl) ⟨2828246, by rfl⟩ : syracuseStep 3770995 = 5656493) B5656493
theorem B22915703 : Blo 1488064 22915703 := bstep (se 1 (by rfl) ⟨17186777, by rfl⟩ : syracuseStep 22915703 = 34373555) B34373555
theorem B5024375 : Blo 1488064 5024375 := bstep (se 1 (by rfl) ⟨3768281, by rfl⟩ : syracuseStep 5024375 = 7536563) B7536563
theorem B3771137 : Blo 1488064 3771137 := bstep (se 2 (by rfl) ⟨1414176, by rfl⟩ : syracuseStep 3771137 = 2828353) B2828353
theorem B7539641 : Blo 1488064 7539641 := bstep (se 2 (by rfl) ⟨2827365, by rfl⟩ : syracuseStep 7539641 = 5654731) B5654731
theorem B1674247 : Blo 1488064 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B19090565 : Blo 1488064 19090565 := bstep (se 4 (by rfl) ⟨1789740, by rfl⟩ : syracuseStep 19090565 = 3579481) B3579481
theorem B1674427 : Blo 1488064 1674427 := bstep (se 1 (by rfl) ⟨1255820, by rfl⟩ : syracuseStep 1674427 = 2511641) B2511641
theorem B5024969 : Blo 1488064 5024969 := bstep (se 2 (by rfl) ⟨1884363, by rfl⟩ : syracuseStep 5024969 = 3768727) B3768727
theorem B3771593 : Blo 1488064 3771593 := bstep (se 2 (by rfl) ⟨1414347, by rfl⟩ : syracuseStep 3771593 = 2828695) B2828695
theorem B2264363 : Blo 1488064 2264363 := bstep (se 1 (by rfl) ⟨1698272, by rfl⟩ : syracuseStep 2264363 = 3396545) B3396545
theorem B7638407 : Blo 1488064 7638407 := bstep (se 1 (by rfl) ⟨5728805, by rfl⟩ : syracuseStep 7638407 = 11457611) B11457611
theorem B16960913 : Blo 1488064 16960913 := bstep (se 2 (by rfl) ⟨6360342, by rfl⟩ : syracuseStep 16960913 = 12720685) B12720685
theorem B4025857 : Blo 1488064 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B11300471 : Blo 1488064 11300471 := bstep (se 1 (by rfl) ⟨8475353, by rfl⟩ : syracuseStep 11300471 = 16950707) B16950707
theorem B1674895 : Blo 1488064 1674895 := bstep (se 1 (by rfl) ⟨1256171, by rfl⟩ : syracuseStep 1674895 = 2512343) B2512343
theorem B12726017 : Blo 1488064 12726017 := bstep (se 2 (by rfl) ⟨4772256, by rfl⟩ : syracuseStep 12726017 = 9544513) B9544513
theorem B16330511 : Blo 1488064 16330511 := bstep (se 1 (by rfl) ⟨12247883, by rfl⟩ : syracuseStep 16330511 = 24495767) B24495767
theorem B2232107 : Blo 1488064 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B2232137 : Blo 1488064 2232137 := bstep (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) B1674103
theorem B5025671 : Blo 1488064 5025671 := bstep (se 1 (by rfl) ⟨3769253, by rfl⟩ : syracuseStep 5025671 = 7538507) B7538507
theorem B27152279 : Blo 1488064 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B2682809 : Blo 1488064 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B2232251 : Blo 1488064 2232251 := bstep (se 1 (by rfl) ⟨1674188, by rfl⟩ : syracuseStep 2232251 = 3348377) B3348377
theorem B2232311 : Blo 1488064 2232311 := bstep (se 1 (by rfl) ⟨1674233, by rfl⟩ : syracuseStep 2232311 = 3348467) B3348467
theorem B2232335 : Blo 1488064 2232335 := bstep (se 1 (by rfl) ⟨1674251, by rfl⟩ : syracuseStep 2232335 = 3348503) B3348503
theorem B9056285 : Blo 1488064 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B5369885 : Blo 1488064 5369885 := bstep (se 3 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 5369885 = 2013707) B2013707
theorem B2232377 : Blo 1488064 2232377 := bstep (se 2 (by rfl) ⟨837141, by rfl⟩ : syracuseStep 2232377 = 1674283) B1674283
theorem B7155773 : Blo 1488064 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B18116741 : Blo 1488064 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B2232455 : Blo 1488064 2232455 := bstep (se 1 (by rfl) ⟨1674341, by rfl⟩ : syracuseStep 2232455 = 3348683) B3348683
theorem B1675399 : Blo 1488064 1675399 := bstep (se 1 (by rfl) ⟨1256549, by rfl⟩ : syracuseStep 1675399 = 2513099) B2513099
theorem B2232491 : Blo 1488064 2232491 := bstep (se 1 (by rfl) ⟨1674368, by rfl⟩ : syracuseStep 2232491 = 3348737) B3348737
theorem B2232521 : Blo 1488064 2232521 := bstep (se 2 (by rfl) ⟨837195, by rfl⟩ : syracuseStep 2232521 = 1674391) B1674391
theorem B4296905 : Blo 1488064 4296905 := bstep (se 2 (by rfl) ⟨1611339, by rfl⟩ : syracuseStep 4296905 = 3222679) B3222679
theorem B7540937 : Blo 1488064 7540937 := bstep (se 2 (by rfl) ⟨2827851, by rfl⟩ : syracuseStep 7540937 = 5655703) B5655703
theorem B5026049 : Blo 1488064 5026049 := bstep (se 2 (by rfl) ⟨1884768, by rfl⟩ : syracuseStep 5026049 = 3769537) B3769537
theorem B4026635 : Blo 1488064 4026635 := bstep (se 1 (by rfl) ⟨3019976, by rfl⟩ : syracuseStep 4026635 = 6039953) B6039953
theorem B3576079 : Blo 1488064 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B7156001 : Blo 1488064 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B2232635 : Blo 1488064 2232635 := bstep (se 1 (by rfl) ⟨1674476, by rfl⟩ : syracuseStep 2232635 = 3348953) B3348953
theorem B1675579 : Blo 1488064 1675579 := bstep (se 1 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 1675579 = 2513369) B2513369
theorem B4772155 : Blo 1488064 4772155 := bstep (se 1 (by rfl) ⟨3579116, by rfl⟩ : syracuseStep 4772155 = 7158233) B7158233
theorem B2232695 : Blo 1488064 2232695 := bstep (se 1 (by rfl) ⟨1674521, by rfl⟩ : syracuseStep 2232695 = 3349043) B3349043
theorem B2232719 : Blo 1488064 2232719 := bstep (se 1 (by rfl) ⟨1674539, by rfl⟩ : syracuseStep 2232719 = 3349079) B3349079
theorem B5656979 : Blo 1488064 5656979 := bstep (se 1 (by rfl) ⟨4242734, by rfl⟩ : syracuseStep 5656979 = 8485469) B8485469
theorem B2232761 : Blo 1488064 2232761 := bstep (se 2 (by rfl) ⟨837285, by rfl⟩ : syracuseStep 2232761 = 1674571) B1674571
theorem B4026809 : Blo 1488064 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B15692291 : Blo 1488064 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B2232839 : Blo 1488064 2232839 := bstep (se 1 (by rfl) ⟨1674629, by rfl⟩ : syracuseStep 2232839 = 3349259) B3349259
theorem B2232875 : Blo 1488064 2232875 := bstep (se 1 (by rfl) ⟨1674656, by rfl⟩ : syracuseStep 2232875 = 3349313) B3349313
theorem B11301443 : Blo 1488064 11301443 := bstep (se 1 (by rfl) ⟨8476082, by rfl⟩ : syracuseStep 11301443 = 16952165) B16952165
theorem B2232905 : Blo 1488064 2232905 := bstep (se 2 (by rfl) ⟨837339, by rfl⟩ : syracuseStep 2232905 = 1674679) B1674679
theorem B2511479 : Blo 1488064 2511479 := bstep (se 1 (by rfl) ⟨1883609, by rfl⟩ : syracuseStep 2511479 = 3767219) B3767219
theorem B2233019 : Blo 1488064 2233019 := bstep (se 1 (by rfl) ⟨1674764, by rfl⟩ : syracuseStep 2233019 = 3349529) B3349529
theorem B2233079 : Blo 1488064 2233079 := bstep (se 1 (by rfl) ⟨1674809, by rfl⟩ : syracuseStep 2233079 = 3349619) B3349619
theorem B2233103 : Blo 1488064 2233103 := bstep (se 1 (by rfl) ⟨1674827, by rfl⟩ : syracuseStep 2233103 = 3349655) B3349655
theorem B1676047 : Blo 1488064 1676047 := bstep (se 1 (by rfl) ⟨1257035, by rfl⟩ : syracuseStep 1676047 = 2514071) B2514071
theorem B2233145 : Blo 1488064 2233145 := bstep (se 2 (by rfl) ⟨837429, by rfl⟩ : syracuseStep 2233145 = 1674859) B1674859
theorem B6361915 : Blo 1488064 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B2233223 : Blo 1488064 2233223 := bstep (se 1 (by rfl) ⟨1674917, by rfl⟩ : syracuseStep 2233223 = 3349835) B3349835
theorem B2683783 : Blo 1488064 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B8483737 : Blo 1488064 8483737 := bstep (se 2 (by rfl) ⟨3181401, by rfl⟩ : syracuseStep 8483737 = 6362803) B6362803
theorem B2233259 : Blo 1488064 2233259 := bstep (se 1 (by rfl) ⟨1674944, by rfl⟩ : syracuseStep 2233259 = 3349889) B3349889
theorem B2233289 : Blo 1488064 2233289 := bstep (se 2 (by rfl) ⟨837483, by rfl⟩ : syracuseStep 2233289 = 1674967) B1674967
theorem B19076107 : Blo 1488064 19076107 := bstep (se 1 (by rfl) ⟨14307080, by rfl⟩ : syracuseStep 19076107 = 28614161) B28614161
theorem B5026859 : Blo 1488064 5026859 := bstep (se 1 (by rfl) ⟨3770144, by rfl⟩ : syracuseStep 5026859 = 7540289) B7540289
theorem B2511931 : Blo 1488064 2511931 := bstep (se 1 (by rfl) ⟨1883948, by rfl⟩ : syracuseStep 2511931 = 3767897) B3767897
theorem B2233403 : Blo 1488064 2233403 := bstep (se 1 (by rfl) ⟨1675052, by rfl⟩ : syracuseStep 2233403 = 3350105) B3350105
theorem B8049725 : Blo 1488064 8049725 := bstep (se 3 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 8049725 = 3018647) B3018647
theorem B2233463 : Blo 1488064 2233463 := bstep (se 1 (by rfl) ⟨1675097, by rfl⟩ : syracuseStep 2233463 = 3350195) B3350195
theorem B2233487 : Blo 1488064 2233487 := bstep (se 1 (by rfl) ⟨1675115, by rfl⟩ : syracuseStep 2233487 = 3350231) B3350231
theorem B2233529 : Blo 1488064 2233529 := bstep (se 2 (by rfl) ⟨837573, by rfl⟩ : syracuseStep 2233529 = 1675147) B1675147
theorem B2512073 : Blo 1488064 2512073 := bstep (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) B1884055
theorem B1488135 : Blo 1488064 1488135 := bstep (se 1 (by rfl) ⟨1116101, by rfl⟩ : syracuseStep 1488135 = 2232203) B2232203
theorem B2233607 : Blo 1488064 2233607 := bstep (se 1 (by rfl) ⟨1675205, by rfl⟩ : syracuseStep 2233607 = 3350411) B3350411
theorem B1488143 : Blo 1488064 1488143 := bstep (se 1 (by rfl) ⟨1116107, by rfl⟩ : syracuseStep 1488143 = 2232215) B2232215
theorem B2233643 : Blo 1488064 2233643 := bstep (se 1 (by rfl) ⟨1675232, by rfl⟩ : syracuseStep 2233643 = 3350465) B3350465
theorem B1488187 : Blo 1488064 1488187 := bstep (se 1 (by rfl) ⟨1116140, by rfl⟩ : syracuseStep 1488187 = 2232281) B2232281
theorem B2233673 : Blo 1488064 2233673 := bstep (se 2 (by rfl) ⟨837627, by rfl⟩ : syracuseStep 2233673 = 1675255) B1675255
theorem B1488263 : Blo 1488064 1488263 := bstep (se 1 (by rfl) ⟨1116197, by rfl⟩ : syracuseStep 1488263 = 2232395) B2232395
theorem B4240775 : Blo 1488064 4240775 := bstep (se 1 (by rfl) ⟨3180581, by rfl⟩ : syracuseStep 4240775 = 6361163) B6361163
theorem B3822983 : Blo 1488064 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B1488271 : Blo 1488064 1488271 := bstep (se 1 (by rfl) ⟨1116203, by rfl⟩ : syracuseStep 1488271 = 2232407) B2232407
theorem B7533971 : Blo 1488064 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B1488315 : Blo 1488064 1488315 := bstep (se 1 (by rfl) ⟨1116236, by rfl⟩ : syracuseStep 1488315 = 2232473) B2232473
theorem B2233787 : Blo 1488064 2233787 := bstep (se 1 (by rfl) ⟨1675340, by rfl⟩ : syracuseStep 2233787 = 3350681) B3350681
theorem B2233847 : Blo 1488064 2233847 := bstep (se 1 (by rfl) ⟨1675385, by rfl⟩ : syracuseStep 2233847 = 3350771) B3350771
theorem B1488391 : Blo 1488064 1488391 := bstep (se 1 (by rfl) ⟨1116293, by rfl⟩ : syracuseStep 1488391 = 2232587) B2232587
theorem B1488399 : Blo 1488064 1488399 := bstep (se 1 (by rfl) ⟨1116299, by rfl⟩ : syracuseStep 1488399 = 2232599) B2232599
theorem B2233871 : Blo 1488064 2233871 := bstep (se 1 (by rfl) ⟨1675403, by rfl⟩ : syracuseStep 2233871 = 3350807) B3350807
theorem B2233913 : Blo 1488064 2233913 := bstep (se 2 (by rfl) ⟨837717, by rfl⟩ : syracuseStep 2233913 = 1675435) B1675435
theorem B1488443 : Blo 1488064 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B3577463 : Blo 1488064 3577463 := bstep (se 1 (by rfl) ⟨2683097, by rfl⟩ : syracuseStep 3577463 = 5366195) B5366195
theorem B1488519 : Blo 1488064 1488519 := bstep (se 1 (by rfl) ⟨1116389, by rfl⟩ : syracuseStep 1488519 = 2232779) B2232779
theorem B2233991 : Blo 1488064 2233991 := bstep (se 1 (by rfl) ⟨1675493, by rfl⟩ : syracuseStep 2233991 = 3350987) B3350987
theorem B1488527 : Blo 1488064 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B2234027 : Blo 1488064 2234027 := bstep (se 1 (by rfl) ⟨1675520, by rfl⟩ : syracuseStep 2234027 = 3351041) B3351041
theorem B1488571 : Blo 1488064 1488571 := bstep (se 1 (by rfl) ⟨1116428, by rfl⟩ : syracuseStep 1488571 = 2232857) B2232857
theorem B9541313 : Blo 1488064 9541313 := bstep (se 2 (by rfl) ⟨3577992, by rfl⟩ : syracuseStep 9541313 = 7155985) B7155985
theorem B2234057 : Blo 1488064 2234057 := bstep (se 2 (by rfl) ⟨837771, by rfl⟩ : syracuseStep 2234057 = 1675543) B1675543
theorem B1488647 : Blo 1488064 1488647 := bstep (se 1 (by rfl) ⟨1116485, by rfl⟩ : syracuseStep 1488647 = 2232971) B2232971
theorem B1488655 : Blo 1488064 1488655 := bstep (se 1 (by rfl) ⟨1116491, by rfl⟩ : syracuseStep 1488655 = 2232983) B2232983
theorem B1488699 : Blo 1488064 1488699 := bstep (se 1 (by rfl) ⟨1116524, by rfl⟩ : syracuseStep 1488699 = 2233049) B2233049
theorem B2234171 : Blo 1488064 2234171 := bstep (se 1 (by rfl) ⟨1675628, by rfl⟩ : syracuseStep 2234171 = 3351257) B3351257
theorem B2234231 : Blo 1488064 2234231 := bstep (se 1 (by rfl) ⟨1675673, by rfl⟩ : syracuseStep 2234231 = 3351347) B3351347
theorem B3348359 : Blo 1488064 3348359 := bstep (se 1 (by rfl) ⟨2511269, by rfl⟩ : syracuseStep 3348359 = 5022539) B5022539
theorem B1488775 : Blo 1488064 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B2512775 : Blo 1488064 2512775 := bstep (se 1 (by rfl) ⟨1884581, by rfl⟩ : syracuseStep 2512775 = 3769163) B3769163
theorem B1488783 : Blo 1488064 1488783 := bstep (se 1 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 1488783 = 2233175) B2233175
theorem B2234255 : Blo 1488064 2234255 := bstep (se 1 (by rfl) ⟨1675691, by rfl⟩ : syracuseStep 2234255 = 3351383) B3351383
theorem B2013113 : Blo 1488064 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B2234297 : Blo 1488064 2234297 := bstep (se 2 (by rfl) ⟨837861, by rfl⟩ : syracuseStep 2234297 = 1675723) B1675723
theorem B1488827 : Blo 1488064 1488827 := bstep (se 1 (by rfl) ⟨1116620, by rfl⟩ : syracuseStep 1488827 = 2233241) B2233241
theorem B1488903 : Blo 1488064 1488903 := bstep (se 1 (by rfl) ⟨1116677, by rfl⟩ : syracuseStep 1488903 = 2233355) B2233355
theorem B2234375 : Blo 1488064 2234375 := bstep (se 1 (by rfl) ⟨1675781, by rfl⟩ : syracuseStep 2234375 = 3351563) B3351563
theorem B7157771 : Blo 1488064 7157771 := bstep (se 1 (by rfl) ⟨5368328, by rfl⟩ : syracuseStep 7157771 = 10736657) B10736657
theorem B1488911 : Blo 1488064 1488911 := bstep (se 1 (by rfl) ⟨1116683, by rfl⟩ : syracuseStep 1488911 = 2233367) B2233367
theorem B2234411 : Blo 1488064 2234411 := bstep (se 1 (by rfl) ⟨1675808, by rfl⟩ : syracuseStep 2234411 = 3351617) B3351617
theorem B3348539 : Blo 1488064 3348539 := bstep (se 1 (by rfl) ⟨2511404, by rfl⟩ : syracuseStep 3348539 = 5022809) B5022809
theorem B1488955 : Blo 1488064 1488955 := bstep (se 1 (by rfl) ⟨1116716, by rfl⟩ : syracuseStep 1488955 = 2233433) B2233433
theorem B2234441 : Blo 1488064 2234441 := bstep (se 2 (by rfl) ⟨837915, by rfl⟩ : syracuseStep 2234441 = 1675831) B1675831
theorem B6035543 : Blo 1488064 6035543 := bstep (se 1 (by rfl) ⟨4526657, by rfl⟩ : syracuseStep 6035543 = 9053315) B9053315
theorem B1489031 : Blo 1488064 1489031 := bstep (se 1 (by rfl) ⟨1116773, by rfl⟩ : syracuseStep 1489031 = 2233547) B2233547
theorem B1489039 : Blo 1488064 1489039 := bstep (se 1 (by rfl) ⟨1116779, by rfl⟩ : syracuseStep 1489039 = 2233559) B2233559
theorem B3348665 : Blo 1488064 3348665 := bstep (se 2 (by rfl) ⟨1255749, by rfl⟩ : syracuseStep 3348665 = 2511499) B2511499
theorem B1489083 : Blo 1488064 1489083 := bstep (se 1 (by rfl) ⟨1116812, by rfl⟩ : syracuseStep 1489083 = 2233625) B2233625
theorem B2234555 : Blo 1488064 2234555 := bstep (se 1 (by rfl) ⟨1675916, by rfl⟩ : syracuseStep 2234555 = 3351833) B3351833
theorem B16963829 : Blo 1488064 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B2119927 : Blo 1488064 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B2234615 : Blo 1488064 2234615 := bstep (se 1 (by rfl) ⟨1675961, by rfl⟩ : syracuseStep 2234615 = 3351923) B3351923
theorem B1489159 : Blo 1488064 1489159 := bstep (se 1 (by rfl) ⟨1116869, by rfl⟩ : syracuseStep 1489159 = 2233739) B2233739
theorem B1489167 : Blo 1488064 1489167 := bstep (se 1 (by rfl) ⟨1116875, by rfl⟩ : syracuseStep 1489167 = 2233751) B2233751
theorem B2234639 : Blo 1488064 2234639 := bstep (se 1 (by rfl) ⟨1675979, by rfl⟩ : syracuseStep 2234639 = 3351959) B3351959
theorem B2234681 : Blo 1488064 2234681 := bstep (se 2 (by rfl) ⟨838005, by rfl⟩ : syracuseStep 2234681 = 1676011) B1676011
theorem B1489211 : Blo 1488064 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B5028155 : Blo 1488064 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B1489287 : Blo 1488064 1489287 := bstep (se 1 (by rfl) ⟨1116965, by rfl⟩ : syracuseStep 1489287 = 2233931) B2233931
theorem B2234759 : Blo 1488064 2234759 := bstep (se 1 (by rfl) ⟨1676069, by rfl⟩ : syracuseStep 2234759 = 3352139) B3352139
theorem B1489295 : Blo 1488064 1489295 := bstep (se 1 (by rfl) ⟨1116971, by rfl⟩ : syracuseStep 1489295 = 2233943) B2233943
theorem B2234795 : Blo 1488064 2234795 := bstep (se 1 (by rfl) ⟨1676096, by rfl⟩ : syracuseStep 2234795 = 3352193) B3352193
theorem B1489339 : Blo 1488064 1489339 := bstep (se 1 (by rfl) ⟨1117004, by rfl⟩ : syracuseStep 1489339 = 2234009) B2234009
theorem B2234825 : Blo 1488064 2234825 := bstep (se 2 (by rfl) ⟨838059, by rfl⟩ : syracuseStep 2234825 = 1676119) B1676119
theorem B1489415 : Blo 1488064 1489415 := bstep (se 1 (by rfl) ⟨1117061, by rfl⟩ : syracuseStep 1489415 = 2234123) B2234123
theorem B3349007 : Blo 1488064 3349007 := bstep (se 1 (by rfl) ⟨2511755, by rfl⟩ : syracuseStep 3349007 = 5023511) B5023511
theorem B1489423 : Blo 1488064 1489423 := bstep (se 1 (by rfl) ⟨1117067, by rfl⟩ : syracuseStep 1489423 = 2234135) B2234135
theorem B2513423 : Blo 1488064 2513423 := bstep (se 1 (by rfl) ⟨1885067, by rfl⟩ : syracuseStep 2513423 = 3770135) B3770135
theorem B16095773 : Blo 1488064 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B3349025 : Blo 1488064 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B2120251 : Blo 1488064 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B1489467 : Blo 1488064 1489467 := bstep (se 1 (by rfl) ⟨1117100, by rfl⟩ : syracuseStep 1489467 = 2234201) B2234201
theorem B2234939 : Blo 1488064 2234939 := bstep (se 1 (by rfl) ⟨1676204, by rfl⟩ : syracuseStep 2234939 = 3352409) B3352409
theorem B2234999 : Blo 1488064 2234999 := bstep (se 1 (by rfl) ⟨1676249, by rfl⟩ : syracuseStep 2234999 = 3352499) B3352499
theorem B1489543 : Blo 1488064 1489543 := bstep (se 1 (by rfl) ⟨1117157, by rfl⟩ : syracuseStep 1489543 = 2234315) B2234315
theorem B1489551 : Blo 1488064 1489551 := bstep (se 1 (by rfl) ⟨1117163, by rfl⟩ : syracuseStep 1489551 = 2234327) B2234327
theorem B2235023 : Blo 1488064 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B2235065 : Blo 1488064 2235065 := bstep (se 2 (by rfl) ⟨838149, by rfl⟩ : syracuseStep 2235065 = 1676299) B1676299
theorem B1489595 : Blo 1488064 1489595 := bstep (se 1 (by rfl) ⟨1117196, by rfl⟩ : syracuseStep 1489595 = 2234393) B2234393
theorem B1489671 : Blo 1488064 1489671 := bstep (se 1 (by rfl) ⟨1117253, by rfl⟩ : syracuseStep 1489671 = 2234507) B2234507
theorem B1489679 : Blo 1488064 1489679 := bstep (se 1 (by rfl) ⟨1117259, by rfl⟩ : syracuseStep 1489679 = 2234519) B2234519
theorem B6036257 : Blo 1488064 6036257 := bstep (se 2 (by rfl) ⟨2263596, by rfl⟩ : syracuseStep 6036257 = 4527193) B4527193
theorem B5028641 : Blo 1488064 5028641 := bstep (se 2 (by rfl) ⟨1885740, by rfl⟩ : syracuseStep 5028641 = 3771481) B3771481
theorem B1489723 : Blo 1488064 1489723 := bstep (se 1 (by rfl) ⟨1117292, by rfl⟩ : syracuseStep 1489723 = 2234585) B2234585
theorem B7158617 : Blo 1488064 7158617 := bstep (se 2 (by rfl) ⟨2684481, by rfl⟩ : syracuseStep 7158617 = 5368963) B5368963
theorem B8485721 : Blo 1488064 8485721 := bstep (se 2 (by rfl) ⟨3182145, by rfl⟩ : syracuseStep 8485721 = 6364291) B6364291
theorem B5651315 : Blo 1488064 5651315 := bstep (se 1 (by rfl) ⟨4238486, by rfl⟩ : syracuseStep 5651315 = 8476973) B8476973
theorem B3349367 : Blo 1488064 3349367 := bstep (se 1 (by rfl) ⟨2512025, by rfl⟩ : syracuseStep 3349367 = 5024051) B5024051
theorem B1489799 : Blo 1488064 1489799 := bstep (se 1 (by rfl) ⟨1117349, by rfl⟩ : syracuseStep 1489799 = 2234699) B2234699
theorem B1489807 : Blo 1488064 1489807 := bstep (se 1 (by rfl) ⟨1117355, by rfl⟩ : syracuseStep 1489807 = 2234711) B2234711
theorem B1489851 : Blo 1488064 1489851 := bstep (se 1 (by rfl) ⟨1117388, by rfl⟩ : syracuseStep 1489851 = 2234777) B2234777
theorem B1489927 : Blo 1488064 1489927 := bstep (se 1 (by rfl) ⟨1117445, by rfl⟩ : syracuseStep 1489927 = 2234891) B2234891
theorem B1489935 : Blo 1488064 1489935 := bstep (se 1 (by rfl) ⟨1117451, by rfl⟩ : syracuseStep 1489935 = 2234903) B2234903
theorem B3349547 : Blo 1488064 3349547 := bstep (se 1 (by rfl) ⟨2512160, by rfl⟩ : syracuseStep 3349547 = 5024321) B5024321
theorem B3578923 : Blo 1488064 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B2513963 : Blo 1488064 2513963 := bstep (se 1 (by rfl) ⟨1885472, by rfl⟩ : syracuseStep 2513963 = 3770945) B3770945
theorem B1489979 : Blo 1488064 1489979 := bstep (se 1 (by rfl) ⟨1117484, by rfl⟩ : syracuseStep 1489979 = 2234969) B2234969
theorem B3767411 : Blo 1488064 3767411 := bstep (se 1 (by rfl) ⟨2825558, by rfl⟩ : syracuseStep 3767411 = 5651117) B5651117
theorem B3767431 : Blo 1488064 3767431 := bstep (se 1 (by rfl) ⟨2825573, by rfl⟩ : syracuseStep 3767431 = 5651147) B5651147
theorem B1490055 : Blo 1488064 1490055 := bstep (se 1 (by rfl) ⟨1117541, by rfl⟩ : syracuseStep 1490055 = 2235083) B2235083
theorem B1490063 : Blo 1488064 1490063 := bstep (se 1 (by rfl) ⟨1117547, by rfl⟩ : syracuseStep 1490063 = 2235095) B2235095
theorem B4242689 : Blo 1488064 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B1883407 : Blo 1488064 1883407 := bstep (se 1 (by rfl) ⟨1412555, by rfl⟩ : syracuseStep 1883407 = 2825111) B2825111
theorem B8592655 : Blo 1488064 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B7257377 : Blo 1488064 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B3579223 : Blo 1488064 3579223 := bstep (se 1 (by rfl) ⟨2684417, by rfl⟩ : syracuseStep 3579223 = 5368835) B5368835
theorem B3349907 : Blo 1488064 3349907 := bstep (se 1 (by rfl) ⟨2512430, by rfl⟩ : syracuseStep 3349907 = 5024861) B5024861
theorem B3767705 : Blo 1488064 3767705 := bstep (se 2 (by rfl) ⟨1412889, by rfl⟩ : syracuseStep 3767705 = 2825779) B2825779
theorem B2514361 : Blo 1488064 2514361 := bstep (se 2 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 2514361 = 1885771) B1885771
theorem B3349961 : Blo 1488064 3349961 := bstep (se 2 (by rfl) ⟨1256235, by rfl⟩ : syracuseStep 3349961 = 2512471) B2512471
theorem B3767867 : Blo 1488064 3767867 := bstep (se 1 (by rfl) ⟨2825900, by rfl⟩ : syracuseStep 3767867 = 5651801) B5651801
theorem B61136477 : Blo 1488064 61136477 := bstep (se 3 (by rfl) ⟨11463089, by rfl⟩ : syracuseStep 61136477 = 22926179) B22926179
theorem B10878583 : Blo 1488064 10878583 := bstep (se 1 (by rfl) ⟨8158937, by rfl⟩ : syracuseStep 10878583 = 16317875) B16317875
theorem B11460325 : Blo 1488064 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B2825999 : Blo 1488064 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B3768079 : Blo 1488064 3768079 := bstep (se 1 (by rfl) ⟨2826059, by rfl⟩ : syracuseStep 3768079 = 5652119) B5652119
theorem B45817649 : Blo 1488064 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B36224921 : Blo 1488064 36224921 := bstep (se 2 (by rfl) ⟨13584345, by rfl⟩ : syracuseStep 36224921 = 27168691) B27168691
theorem B7151581 : Blo 1488064 7151581 := bstep (se 3 (by rfl) ⟨1340921, by rfl⟩ : syracuseStep 7151581 = 2681843) B2681843
theorem B1884151 : Blo 1488064 1884151 := bstep (se 1 (by rfl) ⟨1413113, by rfl⟩ : syracuseStep 1884151 = 2826227) B2826227
theorem B3440647 : Blo 1488064 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B10731527 : Blo 1488064 10731527 := bstep (se 1 (by rfl) ⟨8048645, by rfl⟩ : syracuseStep 10731527 = 16097291) B16097291
theorem B6037523 : Blo 1488064 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B3579923 : Blo 1488064 3579923 := bstep (se 1 (by rfl) ⟨2684942, by rfl⟩ : syracuseStep 3579923 = 5369885) B5369885
theorem B81510461 : Blo 1488064 81510461 := bstep (se 3 (by rfl) ⟨15283211, by rfl⟩ : syracuseStep 81510461 = 30566423) B30566423
theorem B3350699 : Blo 1488064 3350699 := bstep (se 1 (by rfl) ⟨2513024, by rfl⟩ : syracuseStep 3350699 = 5026049) B5026049
theorem B19087589 : Blo 1488064 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B2826569 : Blo 1488064 2826569 := bstep (se 2 (by rfl) ⟨1059963, by rfl⟩ : syracuseStep 2826569 = 2119927) B2119927
theorem B10461527 : Blo 1488064 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B4768105 : Blo 1488064 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B7537211 : Blo 1488064 7537211 := bstep (se 1 (by rfl) ⟨5652908, by rfl⟩ : syracuseStep 7537211 = 11305817) B11305817
theorem B3769031 : Blo 1488064 3769031 := bstep (se 1 (by rfl) ⟨2826773, by rfl⟩ : syracuseStep 3769031 = 5653547) B5653547
theorem B3351239 : Blo 1488064 3351239 := bstep (se 1 (by rfl) ⟨2513429, by rfl⟩ : syracuseStep 3351239 = 5026859) B5026859
theorem B5366483 : Blo 1488064 5366483 := bstep (se 1 (by rfl) ⟨4024862, by rfl⟩ : syracuseStep 5366483 = 8049725) B8049725
theorem B2827001 : Blo 1488064 2827001 := bstep (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) B2120251
theorem B4768541 : Blo 1488064 4768541 := bstep (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) B1788203
theorem B2548655 : Blo 1488064 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B5022647 : Blo 1488064 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B2384975 : Blo 1488064 2384975 := bstep (se 1 (by rfl) ⟨1788731, by rfl⟩ : syracuseStep 2384975 = 3577463) B3577463
theorem B7537859 : Blo 1488064 7537859 := bstep (se 1 (by rfl) ⟨5653394, by rfl⟩ : syracuseStep 7537859 = 11306789) B11306789
theorem B23561417 : Blo 1488064 23561417 := bstep (se 2 (by rfl) ⟨8835531, by rfl⟩ : syracuseStep 23561417 = 17671063) B17671063
theorem B4023695 : Blo 1488064 4023695 := bstep (se 1 (by rfl) ⟨3017771, by rfl⟩ : syracuseStep 4023695 = 6035543) B6035543
theorem B12404111 : Blo 1488064 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B5023241 : Blo 1488064 5023241 := bstep (se 2 (by rfl) ⟨1883715, by rfl⟩ : syracuseStep 5023241 = 3767431) B3767431
theorem B28608011 : Blo 1488064 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B3352103 : Blo 1488064 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B5654231 : Blo 1488064 5654231 := bstep (se 1 (by rfl) ⟨4240673, by rfl⟩ : syracuseStep 5654231 = 8481347) B8481347
theorem B3770185 : Blo 1488064 3770185 := bstep (se 2 (by rfl) ⟨1413819, by rfl⟩ : syracuseStep 3770185 = 2827639) B2827639
theorem B4024171 : Blo 1488064 4024171 := bstep (se 1 (by rfl) ⟨3018128, by rfl⟩ : syracuseStep 4024171 = 6036257) B6036257
theorem B3352427 : Blo 1488064 3352427 := bstep (se 1 (by rfl) ⟨2514320, by rfl⟩ : syracuseStep 3352427 = 5028641) B5028641
theorem B3352481 : Blo 1488064 3352481 := bstep (se 2 (by rfl) ⟨1257180, by rfl⟩ : syracuseStep 3352481 = 2514361) B2514361
theorem B5367809 : Blo 1488064 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B75499613 : Blo 1488064 75499613 := bstep (se 3 (by rfl) ⟨14156177, by rfl⟩ : syracuseStep 75499613 = 28312355) B28312355
theorem B2828459 : Blo 1488064 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B1509575 : Blo 1488064 1509575 := bstep (se 1 (by rfl) ⟨1132181, by rfl⟩ : syracuseStep 1509575 = 2264363) B2264363
theorem B11307275 : Blo 1488064 11307275 := bstep (se 1 (by rfl) ⟨8480456, by rfl⟩ : syracuseStep 11307275 = 16960913) B16960913
theorem B15280433 : Blo 1488064 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B5024105 : Blo 1488064 5024105 := bstep (se 2 (by rfl) ⟨1884039, by rfl⟩ : syracuseStep 5024105 = 3768079) B3768079
theorem B40757651 : Blo 1488064 40757651 := bstep (se 1 (by rfl) ⟨30568238, by rfl⟩ : syracuseStep 40757651 = 61136477) B61136477
theorem B5368301 : Blo 1488064 5368301 := bstep (se 3 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 5368301 = 2013113) B2013113
theorem B1788539 : Blo 1488064 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B4770515 : Blo 1488064 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B5368531 : Blo 1488064 5368531 := bstep (se 1 (by rfl) ⟨4026398, by rfl⟩ : syracuseStep 5368531 = 8052797) B8052797
theorem B4770667 : Blo 1488064 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B2681743 : Blo 1488064 2681743 := bstep (se 1 (by rfl) ⟨2011307, by rfl⟩ : syracuseStep 2681743 = 4022615) B4022615
theorem B3771319 : Blo 1488064 3771319 := bstep (se 1 (by rfl) ⟨2828489, by rfl⟩ : syracuseStep 3771319 = 5656979) B5656979
theorem B5024699 : Blo 1488064 5024699 := bstep (se 1 (by rfl) ⟨3768524, by rfl⟩ : syracuseStep 5024699 = 7537049) B7537049
theorem B3058651 : Blo 1488064 3058651 := bstep (se 1 (by rfl) ⟨2293988, by rfl⟩ : syracuseStep 3058651 = 4587977) B4587977
theorem B48311309 : Blo 1488064 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B10726451 : Blo 1488064 10726451 := bstep (se 1 (by rfl) ⟨8044838, by rfl⟩ : syracuseStep 10726451 = 16089677) B16089677
theorem B1674319 : Blo 1488064 1674319 := bstep (se 1 (by rfl) ⟨1255739, by rfl⟩ : syracuseStep 1674319 = 2511479) B2511479
theorem B9546923 : Blo 1488064 9546923 := bstep (se 1 (by rfl) ⟨7160192, by rfl⟩ : syracuseStep 9546923 = 14320385) B14320385
theorem B1674715 : Blo 1488064 1674715 := bstep (se 1 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 1674715 = 2512073) B2512073
theorem B11308733 : Blo 1488064 11308733 := bstep (se 3 (by rfl) ⟨2120387, by rfl⟩ : syracuseStep 11308733 = 4240775) B4240775
theorem B8482553 : Blo 1488064 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B6360875 : Blo 1488064 6360875 := bstep (se 1 (by rfl) ⟨4770656, by rfl⟩ : syracuseStep 6360875 = 9541313) B9541313
theorem B2232239 : Blo 1488064 2232239 := bstep (se 1 (by rfl) ⟨1674179, by rfl⟩ : syracuseStep 2232239 = 3348359) B3348359
theorem B1675183 : Blo 1488064 1675183 := bstep (se 1 (by rfl) ⟨1256387, by rfl⟩ : syracuseStep 1675183 = 2512775) B2512775
theorem B3223483 : Blo 1488064 3223483 := bstep (se 1 (by rfl) ⟨2417612, by rfl⟩ : syracuseStep 3223483 = 4835225) B4835225
theorem B4771847 : Blo 1488064 4771847 := bstep (se 1 (by rfl) ⟨3578885, by rfl⟩ : syracuseStep 4771847 = 7157771) B7157771
theorem B2232329 : Blo 1488064 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B2232359 : Blo 1488064 2232359 := bstep (se 1 (by rfl) ⟨1674269, by rfl⟩ : syracuseStep 2232359 = 3348539) B3348539
theorem B42922061 : Blo 1488064 42922061 := bstep (se 3 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 42922061 = 16095773) B16095773
theorem B2232443 : Blo 1488064 2232443 := bstep (se 1 (by rfl) ⟨1674332, by rfl⟩ : syracuseStep 2232443 = 3348665) B3348665
theorem B11309219 : Blo 1488064 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B2683091 : Blo 1488064 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B2683127 : Blo 1488064 2683127 := bstep (se 1 (by rfl) ⟨2012345, by rfl⟩ : syracuseStep 2683127 = 4024691) B4024691
theorem B2232569 : Blo 1488064 2232569 := bstep (se 2 (by rfl) ⟨837213, by rfl⟩ : syracuseStep 2232569 = 1674427) B1674427
theorem B2232671 : Blo 1488064 2232671 := bstep (se 1 (by rfl) ⟨1674503, by rfl⟩ : syracuseStep 2232671 = 3349007) B3349007
theorem B1675615 : Blo 1488064 1675615 := bstep (se 1 (by rfl) ⟨1256711, by rfl⟩ : syracuseStep 1675615 = 2513423) B2513423
theorem B2511209 : Blo 1488064 2511209 := bstep (se 2 (by rfl) ⟨941703, by rfl⟩ : syracuseStep 2511209 = 1883407) B1883407
theorem B11456873 : Blo 1488064 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B2232683 : Blo 1488064 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B4772297 : Blo 1488064 4772297 := bstep (se 2 (by rfl) ⟨1789611, by rfl⟩ : syracuseStep 4772297 = 3579223) B3579223
theorem B21475793 : Blo 1488064 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B4772411 : Blo 1488064 4772411 := bstep (se 1 (by rfl) ⟨3579308, by rfl⟩ : syracuseStep 4772411 = 7158617) B7158617
theorem B5657147 : Blo 1488064 5657147 := bstep (se 1 (by rfl) ⟨4242860, by rfl⟩ : syracuseStep 5657147 = 8485721) B8485721
theorem B2232911 : Blo 1488064 2232911 := bstep (se 1 (by rfl) ⟨1674683, by rfl⟩ : syracuseStep 2232911 = 3349367) B3349367
theorem B5026427 : Blo 1488064 5026427 := bstep (se 1 (by rfl) ⟨3769820, by rfl⟩ : syracuseStep 5026427 = 7539641) B7539641
theorem B2233031 : Blo 1488064 2233031 := bstep (se 1 (by rfl) ⟨1674773, by rfl⟩ : syracuseStep 2233031 = 3349547) B3349547
theorem B1675975 : Blo 1488064 1675975 := bstep (se 1 (by rfl) ⟨1256981, by rfl⟩ : syracuseStep 1675975 = 2513963) B2513963
theorem B2511607 : Blo 1488064 2511607 := bstep (se 1 (by rfl) ⟨1883705, by rfl⟩ : syracuseStep 2511607 = 3767411) B3767411
theorem B12727043 : Blo 1488064 12727043 := bstep (se 1 (by rfl) ⟨9545282, by rfl⟩ : syracuseStep 12727043 = 19090565) B19090565
theorem B5026589 : Blo 1488064 5026589 := bstep (se 3 (by rfl) ⟨942485, by rfl⟩ : syracuseStep 5026589 = 1884971) B1884971
theorem B14504777 : Blo 1488064 14504777 := bstep (se 2 (by rfl) ⟨5439291, by rfl⟩ : syracuseStep 14504777 = 10878583) B10878583
theorem B2233193 : Blo 1488064 2233193 := bstep (se 2 (by rfl) ⟨837447, by rfl⟩ : syracuseStep 2233193 = 1674895) B1674895
theorem B4838251 : Blo 1488064 4838251 := bstep (se 1 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 4838251 = 7257377) B7257377
theorem B5092271 : Blo 1488064 5092271 := bstep (se 1 (by rfl) ⟨3819203, by rfl⟩ : syracuseStep 5092271 = 7638407) B7638407
theorem B2233271 : Blo 1488064 2233271 := bstep (se 1 (by rfl) ⟨1674953, by rfl⟩ : syracuseStep 2233271 = 3349907) B3349907
theorem B2511803 : Blo 1488064 2511803 := bstep (se 1 (by rfl) ⟨1883852, by rfl⟩ : syracuseStep 2511803 = 3767705) B3767705
theorem B2233307 : Blo 1488064 2233307 := bstep (se 1 (by rfl) ⟨1674980, by rfl⟩ : syracuseStep 2233307 = 3349961) B3349961
theorem B2511911 : Blo 1488064 2511911 := bstep (se 1 (by rfl) ⟨1883933, by rfl⟩ : syracuseStep 2511911 = 3767867) B3767867
theorem B7533647 : Blo 1488064 7533647 := bstep (se 1 (by rfl) ⟨5650235, by rfl⟩ : syracuseStep 7533647 = 11300471) B11300471
theorem B8484011 : Blo 1488064 8484011 := bstep (se 1 (by rfl) ⟨6363008, by rfl⟩ : syracuseStep 8484011 = 12726017) B12726017
theorem B1488071 : Blo 1488064 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B30545099 : Blo 1488064 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B1488091 : Blo 1488064 1488091 := bstep (se 1 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 1488091 = 2232137) B2232137
theorem B18101519 : Blo 1488064 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B1488167 : Blo 1488064 1488167 := bstep (se 1 (by rfl) ⟨1116125, by rfl⟩ : syracuseStep 1488167 = 2232251) B2232251
theorem B2512201 : Blo 1488064 2512201 := bstep (se 2 (by rfl) ⟨942075, by rfl⟩ : syracuseStep 2512201 = 1884151) B1884151
theorem B1488207 : Blo 1488064 1488207 := bstep (se 1 (by rfl) ⟨1116155, by rfl⟩ : syracuseStep 1488207 = 2232311) B2232311
theorem B1488223 : Blo 1488064 1488223 := bstep (se 1 (by rfl) ⟨1116167, by rfl⟩ : syracuseStep 1488223 = 2232335) B2232335
theorem B2512235 : Blo 1488064 2512235 := bstep (se 1 (by rfl) ⟨1884176, by rfl⟩ : syracuseStep 2512235 = 3768353) B3768353
theorem B1488251 : Blo 1488064 1488251 := bstep (se 1 (by rfl) ⟨1116188, by rfl⟩ : syracuseStep 1488251 = 2232377) B2232377
theorem B1488303 : Blo 1488064 1488303 := bstep (se 1 (by rfl) ⟨1116227, by rfl⟩ : syracuseStep 1488303 = 2232455) B2232455
theorem B2233775 : Blo 1488064 2233775 := bstep (se 1 (by rfl) ⟨1675331, by rfl⟩ : syracuseStep 2233775 = 3350663) B3350663
theorem B1488327 : Blo 1488064 1488327 := bstep (se 1 (by rfl) ⟨1116245, by rfl⟩ : syracuseStep 1488327 = 2232491) B2232491
theorem B1488347 : Blo 1488064 1488347 := bstep (se 1 (by rfl) ⟨1116260, by rfl⟩ : syracuseStep 1488347 = 2232521) B2232521
theorem B2864603 : Blo 1488064 2864603 := bstep (se 1 (by rfl) ⟨2148452, by rfl⟩ : syracuseStep 2864603 = 4296905) B4296905
theorem B5027291 : Blo 1488064 5027291 := bstep (se 1 (by rfl) ⟨3770468, by rfl⟩ : syracuseStep 5027291 = 7540937) B7540937
theorem B2684423 : Blo 1488064 2684423 := bstep (se 1 (by rfl) ⟨2013317, by rfl⟩ : syracuseStep 2684423 = 4026635) B4026635
theorem B2233865 : Blo 1488064 2233865 := bstep (se 2 (by rfl) ⟨837699, by rfl⟩ : syracuseStep 2233865 = 1675399) B1675399
theorem B1488423 : Blo 1488064 1488423 := bstep (se 1 (by rfl) ⟨1116317, by rfl⟩ : syracuseStep 1488423 = 2232635) B2232635
theorem B2233895 : Blo 1488064 2233895 := bstep (se 1 (by rfl) ⟨1675421, by rfl⟩ : syracuseStep 2233895 = 3350843) B3350843
theorem B1488463 : Blo 1488064 1488463 := bstep (se 1 (by rfl) ⟨1116347, by rfl⟩ : syracuseStep 1488463 = 2232695) B2232695
theorem B1488479 : Blo 1488064 1488479 := bstep (se 1 (by rfl) ⟨1116359, by rfl⟩ : syracuseStep 1488479 = 2232719) B2232719
theorem B1488507 : Blo 1488064 1488507 := bstep (se 1 (by rfl) ⟨1116380, by rfl⟩ : syracuseStep 1488507 = 2232761) B2232761
theorem B2233979 : Blo 1488064 2233979 := bstep (se 1 (by rfl) ⟨1675484, by rfl⟩ : syracuseStep 2233979 = 3350969) B3350969
theorem B2684539 : Blo 1488064 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B7542395 : Blo 1488064 7542395 := bstep (se 1 (by rfl) ⟨5656796, by rfl⟩ : syracuseStep 7542395 = 11313593) B11313593
theorem B1488559 : Blo 1488064 1488559 := bstep (se 1 (by rfl) ⟨1116419, by rfl⟩ : syracuseStep 1488559 = 2232839) B2232839
theorem B4904633 : Blo 1488064 4904633 := bstep (se 2 (by rfl) ⟨1839237, by rfl⟩ : syracuseStep 4904633 = 3678475) B3678475
theorem B1488583 : Blo 1488064 1488583 := bstep (se 1 (by rfl) ⟨1116437, by rfl⟩ : syracuseStep 1488583 = 2232875) B2232875
theorem B3348179 : Blo 1488064 3348179 := bstep (se 1 (by rfl) ⟨2511134, by rfl⟩ : syracuseStep 3348179 = 5022269) B5022269
theorem B7534295 : Blo 1488064 7534295 := bstep (se 1 (by rfl) ⟨5650721, by rfl⟩ : syracuseStep 7534295 = 11301443) B11301443
theorem B1488603 : Blo 1488064 1488603 := bstep (se 1 (by rfl) ⟨1116452, by rfl⟩ : syracuseStep 1488603 = 2232905) B2232905
theorem B2512633 : Blo 1488064 2512633 := bstep (se 2 (by rfl) ⟨942237, by rfl⟩ : syracuseStep 2512633 = 1884475) B1884475
theorem B2234105 : Blo 1488064 2234105 := bstep (se 2 (by rfl) ⟨837789, by rfl⟩ : syracuseStep 2234105 = 1675579) B1675579
theorem B6362873 : Blo 1488064 6362873 := bstep (se 2 (by rfl) ⟨2386077, by rfl⟩ : syracuseStep 6362873 = 4772155) B4772155
theorem B1488679 : Blo 1488064 1488679 := bstep (se 1 (by rfl) ⟨1116509, by rfl⟩ : syracuseStep 1488679 = 2233019) B2233019
theorem B1488719 : Blo 1488064 1488719 := bstep (se 1 (by rfl) ⟨1116539, by rfl⟩ : syracuseStep 1488719 = 2233079) B2233079
theorem B1488735 : Blo 1488064 1488735 := bstep (se 1 (by rfl) ⟨1116551, by rfl⟩ : syracuseStep 1488735 = 2233103) B2233103
theorem B2234207 : Blo 1488064 2234207 := bstep (se 1 (by rfl) ⟨1675655, by rfl⟩ : syracuseStep 2234207 = 3351311) B3351311
theorem B6362975 : Blo 1488064 6362975 := bstep (se 1 (by rfl) ⟨4772231, by rfl⟩ : syracuseStep 6362975 = 9544463) B9544463
theorem B2234219 : Blo 1488064 2234219 := bstep (se 1 (by rfl) ⟨1675664, by rfl⟩ : syracuseStep 2234219 = 3351329) B3351329
theorem B1488763 : Blo 1488064 1488763 := bstep (se 1 (by rfl) ⟨1116572, by rfl⟩ : syracuseStep 1488763 = 2233145) B2233145
theorem B1488815 : Blo 1488064 1488815 := bstep (se 1 (by rfl) ⟨1116611, by rfl⟩ : syracuseStep 1488815 = 2233223) B2233223
theorem B1488839 : Blo 1488064 1488839 := bstep (se 1 (by rfl) ⟨1116629, by rfl⟩ : syracuseStep 1488839 = 2233259) B2233259
theorem B1488859 : Blo 1488064 1488859 := bstep (se 1 (by rfl) ⟨1116644, by rfl⟩ : syracuseStep 1488859 = 2233289) B2233289
theorem B2512903 : Blo 1488064 2512903 := bstep (se 1 (by rfl) ⟨1884677, by rfl⟩ : syracuseStep 2512903 = 3769355) B3769355
theorem B1488935 : Blo 1488064 1488935 := bstep (se 1 (by rfl) ⟨1116701, by rfl⟩ : syracuseStep 1488935 = 2233403) B2233403
theorem B1488975 : Blo 1488064 1488975 := bstep (se 1 (by rfl) ⟨1116731, by rfl⟩ : syracuseStep 1488975 = 2233463) B2233463
theorem B2234447 : Blo 1488064 2234447 := bstep (se 1 (by rfl) ⟨1675835, by rfl⟩ : syracuseStep 2234447 = 3351671) B3351671
theorem B1488991 : Blo 1488064 1488991 := bstep (se 1 (by rfl) ⟨1116743, by rfl⟩ : syracuseStep 1488991 = 2233487) B2233487
theorem B1489019 : Blo 1488064 1489019 := bstep (se 1 (by rfl) ⟨1116764, by rfl⟩ : syracuseStep 1489019 = 2233529) B2233529
theorem B5027993 : Blo 1488064 5027993 := bstep (se 2 (by rfl) ⟨1885497, by rfl⟩ : syracuseStep 5027993 = 3770995) B3770995
theorem B2545835 : Blo 1488064 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B1489071 : Blo 1488064 1489071 := bstep (se 1 (by rfl) ⟨1116803, by rfl⟩ : syracuseStep 1489071 = 2233607) B2233607
theorem B1489095 : Blo 1488064 1489095 := bstep (se 1 (by rfl) ⟨1116821, by rfl⟩ : syracuseStep 1489095 = 2233643) B2233643
theorem B2234567 : Blo 1488064 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1489115 : Blo 1488064 1489115 := bstep (se 1 (by rfl) ⟨1116836, by rfl⟩ : syracuseStep 1489115 = 2233673) B2233673
theorem B1489191 : Blo 1488064 1489191 := bstep (se 1 (by rfl) ⟨1116893, by rfl⟩ : syracuseStep 1489191 = 2233787) B2233787
theorem B1489231 : Blo 1488064 1489231 := bstep (se 1 (by rfl) ⟨1116923, by rfl⟩ : syracuseStep 1489231 = 2233847) B2233847
theorem B1489247 : Blo 1488064 1489247 := bstep (se 1 (by rfl) ⟨1116935, by rfl⟩ : syracuseStep 1489247 = 2233871) B2233871
theorem B2234729 : Blo 1488064 2234729 := bstep (se 2 (by rfl) ⟨838023, by rfl⟩ : syracuseStep 2234729 = 1676047) B1676047
theorem B1489275 : Blo 1488064 1489275 := bstep (se 1 (by rfl) ⟨1116956, by rfl⟩ : syracuseStep 1489275 = 2233913) B2233913
theorem B1489327 : Blo 1488064 1489327 := bstep (se 1 (by rfl) ⟨1116995, by rfl⟩ : syracuseStep 1489327 = 2233991) B2233991
theorem B2513335 : Blo 1488064 2513335 := bstep (se 1 (by rfl) ⟨1885001, by rfl⟩ : syracuseStep 2513335 = 3770003) B3770003
theorem B2234807 : Blo 1488064 2234807 := bstep (se 1 (by rfl) ⟨1676105, by rfl⟩ : syracuseStep 2234807 = 3352211) B3352211
theorem B1489351 : Blo 1488064 1489351 := bstep (se 1 (by rfl) ⟨1117013, by rfl⟩ : syracuseStep 1489351 = 2234027) B2234027
theorem B1489371 : Blo 1488064 1489371 := bstep (se 1 (by rfl) ⟨1117028, by rfl⟩ : syracuseStep 1489371 = 2234057) B2234057
theorem B2234843 : Blo 1488064 2234843 := bstep (se 1 (by rfl) ⟨1676132, by rfl⟩ : syracuseStep 2234843 = 3352265) B3352265
theorem B5364233 : Blo 1488064 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B3578377 : Blo 1488064 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B11311649 : Blo 1488064 11311649 := bstep (se 2 (by rfl) ⟨4241868, by rfl⟩ : syracuseStep 11311649 = 8483737) B8483737
theorem B1489447 : Blo 1488064 1489447 := bstep (se 1 (by rfl) ⟨1117085, by rfl⟩ : syracuseStep 1489447 = 2234171) B2234171
theorem B1489487 : Blo 1488064 1489487 := bstep (se 1 (by rfl) ⟨1117115, by rfl⟩ : syracuseStep 1489487 = 2234231) B2234231
theorem B1489503 : Blo 1488064 1489503 := bstep (se 1 (by rfl) ⟨1117127, by rfl⟩ : syracuseStep 1489503 = 2234255) B2234255
theorem B3349115 : Blo 1488064 3349115 := bstep (se 1 (by rfl) ⟨2511836, by rfl⟩ : syracuseStep 3349115 = 5023673) B5023673
theorem B2513531 : Blo 1488064 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B1489531 : Blo 1488064 1489531 := bstep (se 1 (by rfl) ⟨1117148, by rfl⟩ : syracuseStep 1489531 = 2234297) B2234297
theorem B1489583 : Blo 1488064 1489583 := bstep (se 1 (by rfl) ⟨1117187, by rfl⟩ : syracuseStep 1489583 = 2234375) B2234375
theorem B25434809 : Blo 1488064 25434809 := bstep (se 2 (by rfl) ⟨9538053, by rfl⟩ : syracuseStep 25434809 = 19076107) B19076107
theorem B1489607 : Blo 1488064 1489607 := bstep (se 1 (by rfl) ⟨1117205, by rfl⟩ : syracuseStep 1489607 = 2234411) B2234411
theorem B1489627 : Blo 1488064 1489627 := bstep (se 1 (by rfl) ⟨1117220, by rfl⟩ : syracuseStep 1489627 = 2234441) B2234441
theorem B3349241 : Blo 1488064 3349241 := bstep (se 2 (by rfl) ⟨1255965, by rfl⟩ : syracuseStep 3349241 = 2511931) B2511931
theorem B1489703 : Blo 1488064 1489703 := bstep (se 1 (by rfl) ⟨1117277, by rfl⟩ : syracuseStep 1489703 = 2234555) B2234555
theorem B1489743 : Blo 1488064 1489743 := bstep (se 1 (by rfl) ⟨1117307, by rfl⟩ : syracuseStep 1489743 = 2234615) B2234615
theorem B4528991 : Blo 1488064 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B1489759 : Blo 1488064 1489759 := bstep (se 1 (by rfl) ⟨1117319, by rfl⟩ : syracuseStep 1489759 = 2234639) B2234639
theorem B1489787 : Blo 1488064 1489787 := bstep (se 1 (by rfl) ⟨1117340, by rfl⟩ : syracuseStep 1489787 = 2234681) B2234681
theorem B1489839 : Blo 1488064 1489839 := bstep (se 1 (by rfl) ⟨1117379, by rfl⟩ : syracuseStep 1489839 = 2234759) B2234759
theorem B10738615 : Blo 1488064 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B1489863 : Blo 1488064 1489863 := bstep (se 1 (by rfl) ⟨1117397, by rfl⟩ : syracuseStep 1489863 = 2234795) B2234795
theorem B1489883 : Blo 1488064 1489883 := bstep (se 1 (by rfl) ⟨1117412, by rfl⟩ : syracuseStep 1489883 = 2234825) B2234825
theorem B3349511 : Blo 1488064 3349511 := bstep (se 1 (by rfl) ⟨2512133, by rfl⟩ : syracuseStep 3349511 = 5024267) B5024267
theorem B2513929 : Blo 1488064 2513929 := bstep (se 2 (by rfl) ⟨942723, by rfl⟩ : syracuseStep 2513929 = 1885447) B1885447
theorem B2825255 : Blo 1488064 2825255 := bstep (se 1 (by rfl) ⟨2118941, by rfl⟩ : syracuseStep 2825255 = 4237883) B4237883
theorem B1489959 : Blo 1488064 1489959 := bstep (se 1 (by rfl) ⟨1117469, by rfl⟩ : syracuseStep 1489959 = 2234939) B2234939
theorem B15277135 : Blo 1488064 15277135 := bstep (se 1 (by rfl) ⟨11457851, by rfl⟩ : syracuseStep 15277135 = 22915703) B22915703
theorem B3349583 : Blo 1488064 3349583 := bstep (se 1 (by rfl) ⟨2512187, by rfl⟩ : syracuseStep 3349583 = 5024375) B5024375
theorem B1489999 : Blo 1488064 1489999 := bstep (se 1 (by rfl) ⟨1117499, by rfl⟩ : syracuseStep 1489999 = 2234999) B2234999
theorem B1490015 : Blo 1488064 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B1490043 : Blo 1488064 1490043 := bstep (se 1 (by rfl) ⟨1117532, by rfl⟩ : syracuseStep 1490043 = 2235065) B2235065
theorem B2514091 : Blo 1488064 2514091 := bstep (se 1 (by rfl) ⟨1885568, by rfl⟩ : syracuseStep 2514091 = 3771137) B3771137
theorem B3767543 : Blo 1488064 3767543 := bstep (se 1 (by rfl) ⟨2825657, by rfl⟩ : syracuseStep 3767543 = 5651315) B5651315
theorem B3349979 : Blo 1488064 3349979 := bstep (se 1 (by rfl) ⟨2512484, by rfl⟩ : syracuseStep 3349979 = 5024969) B5024969
theorem B2514395 : Blo 1488064 2514395 := bstep (se 1 (by rfl) ⟨1885796, by rfl⟩ : syracuseStep 2514395 = 3771593) B3771593
theorem B96599789 : Blo 1488064 96599789 := bstep (se 3 (by rfl) ⟨18112460, by rfl⟩ : syracuseStep 96599789 = 36224921) B36224921
theorem B1883999 : Blo 1488064 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B10887007 : Blo 1488064 10887007 := bstep (se 1 (by rfl) ⟨8165255, by rfl⟩ : syracuseStep 10887007 = 16330511) B16330511
theorem B3350447 : Blo 1488064 3350447 := bstep (se 1 (by rfl) ⟨2512835, by rfl⟩ : syracuseStep 3350447 = 5025671) B5025671
theorem B9535441 : Blo 1488064 9535441 := bstep (se 2 (by rfl) ⟨3575790, by rfl⟩ : syracuseStep 9535441 = 7151581) B7151581
theorem B4587529 : Blo 1488064 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B3350537 : Blo 1488064 3350537 := bstep (se 2 (by rfl) ⟨1256451, by rfl⟩ : syracuseStep 3350537 = 2512903) B2512903
theorem B28614707 : Blo 1488064 28614707 := bstep (se 1 (by rfl) ⟨21461030, by rfl⟩ : syracuseStep 28614707 = 42922061) B42922061
theorem B1884379 : Blo 1488064 1884379 := bstep (se 1 (by rfl) ⟨1413284, by rfl⟩ : syracuseStep 1884379 = 2826569) B2826569
theorem B3350951 : Blo 1488064 3350951 := bstep (se 1 (by rfl) ⟨2513213, by rfl⟩ : syracuseStep 3350951 = 5026427) B5026427
theorem B6357473 : Blo 1488064 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B3179027 : Blo 1488064 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B3351059 : Blo 1488064 3351059 := bstep (se 1 (by rfl) ⟨2513294, by rfl⟩ : syracuseStep 3351059 = 5026589) B5026589
theorem B3351113 : Blo 1488064 3351113 := bstep (se 2 (by rfl) ⟨1256667, by rfl⟩ : syracuseStep 3351113 = 2513335) B2513335
theorem B5022431 : Blo 1488064 5022431 := bstep (se 1 (by rfl) ⟨3766823, by rfl⟩ : syracuseStep 5022431 = 7533647) B7533647
theorem B12067679 : Blo 1488064 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B3351527 : Blo 1488064 3351527 := bstep (se 1 (by rfl) ⟨2513645, by rfl⟩ : syracuseStep 3351527 = 5027291) B5027291
theorem B19072007 : Blo 1488064 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B3269755 : Blo 1488064 3269755 := bstep (se 1 (by rfl) ⟨2452316, by rfl⟩ : syracuseStep 3269755 = 4904633) B4904633
theorem B5022863 : Blo 1488064 5022863 := bstep (se 1 (by rfl) ⟨3767147, by rfl⟩ : syracuseStep 5022863 = 7534295) B7534295
theorem B3769487 : Blo 1488064 3769487 := bstep (se 1 (by rfl) ⟨2827115, by rfl⟩ : syracuseStep 3769487 = 5654231) B5654231
theorem B3351905 : Blo 1488064 3351905 := bstep (se 2 (by rfl) ⟨1256964, by rfl⟩ : syracuseStep 3351905 = 2513929) B2513929
theorem B50333075 : Blo 1488064 50333075 := bstep (se 1 (by rfl) ⟨37749806, by rfl⟩ : syracuseStep 50333075 = 75499613) B75499613
theorem B3351995 : Blo 1488064 3351995 := bstep (se 1 (by rfl) ⟨2513996, by rfl⟩ : syracuseStep 3351995 = 5027993) B5027993
theorem B7538183 : Blo 1488064 7538183 := bstep (se 1 (by rfl) ⟨5653637, by rfl⟩ : syracuseStep 7538183 = 11307275) B11307275
theorem B3352121 : Blo 1488064 3352121 := bstep (se 2 (by rfl) ⟨1257045, by rfl⟩ : syracuseStep 3352121 = 2514091) B2514091
theorem B4769437 : Blo 1488064 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B3180343 : Blo 1488064 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B7538669 : Blo 1488064 7538669 := bstep (se 3 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 7538669 = 2827001) B2827001
theorem B5023997 : Blo 1488064 5023997 := bstep (se 3 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 5023997 = 1883999) B1883999
theorem B12077309 : Blo 1488064 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B7539155 : Blo 1488064 7539155 := bstep (se 1 (by rfl) ⟨5654366, by rfl⟩ : syracuseStep 7539155 = 11308733) B11308733
theorem B64399859 : Blo 1488064 64399859 := bstep (se 1 (by rfl) ⟨48299894, by rfl⟩ : syracuseStep 64399859 = 96599789) B96599789
theorem B5655035 : Blo 1488064 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B14314157 : Blo 1488064 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B7154351 : Blo 1488064 7154351 := bstep (se 1 (by rfl) ⟨5365763, by rfl⟩ : syracuseStep 7154351 = 10731527) B10731527
theorem B3181231 : Blo 1488064 3181231 := bstep (se 1 (by rfl) ⟨2385923, by rfl⟩ : syracuseStep 3181231 = 4771847) B4771847
theorem B4025015 : Blo 1488064 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B54340307 : Blo 1488064 54340307 := bstep (se 1 (by rfl) ⟨40755230, by rfl⟩ : syracuseStep 54340307 = 81510461) B81510461
theorem B9546461 : Blo 1488064 9546461 := bstep (se 3 (by rfl) ⟨1789961, by rfl⟩ : syracuseStep 9546461 = 3579923) B3579923
theorem B7539479 : Blo 1488064 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B1788727 : Blo 1488064 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B12725059 : Blo 1488064 12725059 := bstep (se 1 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 12725059 = 19087589) B19087589
theorem B1788751 : Blo 1488064 1788751 := bstep (se 1 (by rfl) ⟨1341563, by rfl⟩ : syracuseStep 1788751 = 2683127) B2683127
theorem B6359933 : Blo 1488064 6359933 := bstep (se 3 (by rfl) ⟨1192487, by rfl⟩ : syracuseStep 6359933 = 2384975) B2384975
theorem B6974351 : Blo 1488064 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B1674139 : Blo 1488064 1674139 := bstep (se 1 (by rfl) ⟨1255604, by rfl⟩ : syracuseStep 1674139 = 2511209) B2511209
theorem B7637915 : Blo 1488064 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B3181531 : Blo 1488064 3181531 := bstep (se 1 (by rfl) ⟨2386148, by rfl⟩ : syracuseStep 3181531 = 4772297) B4772297
theorem B5024807 : Blo 1488064 5024807 := bstep (se 1 (by rfl) ⟨3768605, by rfl⟩ : syracuseStep 5024807 = 7537211) B7537211
theorem B3181607 : Blo 1488064 3181607 := bstep (se 1 (by rfl) ⟨2386205, by rfl⟩ : syracuseStep 3181607 = 4772411) B4772411
theorem B3771431 : Blo 1488064 3771431 := bstep (se 1 (by rfl) ⟨2828573, by rfl⟩ : syracuseStep 3771431 = 5657147) B5657147
theorem B4025533 : Blo 1488064 4025533 := bstep (se 3 (by rfl) ⟨754787, by rfl⟩ : syracuseStep 4025533 = 1509575) B1509575
theorem B9669851 : Blo 1488064 9669851 := bstep (se 1 (by rfl) ⟨7252388, by rfl⟩ : syracuseStep 9669851 = 14504777) B14504777
theorem B3394847 : Blo 1488064 3394847 := bstep (se 1 (by rfl) ⟨2546135, by rfl⟩ : syracuseStep 3394847 = 5092271) B5092271
theorem B1699103 : Blo 1488064 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B1674535 : Blo 1488064 1674535 := bstep (se 1 (by rfl) ⟨1255901, by rfl⟩ : syracuseStep 1674535 = 2511803) B2511803
theorem B4771169 : Blo 1488064 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B1674607 : Blo 1488064 1674607 := bstep (se 1 (by rfl) ⟨1255955, by rfl⟩ : syracuseStep 1674607 = 2511911) B2511911
theorem B5656007 : Blo 1488064 5656007 := bstep (se 1 (by rfl) ⟨4242005, by rfl⟩ : syracuseStep 5656007 = 8484011) B8484011
theorem B5025239 : Blo 1488064 5025239 := bstep (se 1 (by rfl) ⟨3768929, by rfl⟩ : syracuseStep 5025239 = 7537859) B7537859
theorem B15707611 : Blo 1488064 15707611 := bstep (se 1 (by rfl) ⟨11780708, by rfl⟩ : syracuseStep 15707611 = 23561417) B23561417
theorem B1674823 : Blo 1488064 1674823 := bstep (se 1 (by rfl) ⟨1256117, by rfl⟩ : syracuseStep 1674823 = 2512235) B2512235
theorem B2682463 : Blo 1488064 2682463 := bstep (se 1 (by rfl) ⟨2011847, by rfl⟩ : syracuseStep 2682463 = 4023695) B4023695
theorem B2232119 : Blo 1488064 2232119 := bstep (se 1 (by rfl) ⟨1674089, by rfl⟩ : syracuseStep 2232119 = 3348179) B3348179
theorem B6451001 : Blo 1488064 6451001 := bstep (se 2 (by rfl) ⟨2419125, by rfl⟩ : syracuseStep 6451001 = 4838251) B4838251
theorem B3575657 : Blo 1488064 3575657 := bstep (se 2 (by rfl) ⟨1340871, by rfl⟩ : syracuseStep 3575657 = 2681743) B2681743
theorem B7638941 : Blo 1488064 7638941 := bstep (se 3 (by rfl) ⟨1432301, by rfl⟩ : syracuseStep 7638941 = 2864603) B2864603
theorem B2232425 : Blo 1488064 2232425 := bstep (se 2 (by rfl) ⟨837159, by rfl⟩ : syracuseStep 2232425 = 1674319) B1674319
theorem B20369513 : Blo 1488064 20369513 := bstep (se 2 (by rfl) ⟨7638567, by rfl⟩ : syracuseStep 20369513 = 15277135) B15277135
theorem B10186955 : Blo 1488064 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B3576155 : Blo 1488064 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B7541099 : Blo 1488064 7541099 := bstep (se 1 (by rfl) ⟨5655824, by rfl⟩ : syracuseStep 7541099 = 11311649) B11311649
theorem B2232743 : Blo 1488064 2232743 := bstep (se 1 (by rfl) ⟨1674557, by rfl⟩ : syracuseStep 2232743 = 3349115) B3349115
theorem B1675687 : Blo 1488064 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B2232827 : Blo 1488064 2232827 := bstep (se 1 (by rfl) ⟨1674620, by rfl⟩ : syracuseStep 2232827 = 3349241) B3349241
theorem B2232953 : Blo 1488064 2232953 := bstep (se 2 (by rfl) ⟨837357, by rfl⟩ : syracuseStep 2232953 = 1674715) B1674715
theorem B2233007 : Blo 1488064 2233007 := bstep (se 1 (by rfl) ⟨1674755, by rfl⟩ : syracuseStep 2233007 = 3349511) B3349511
theorem B32207539 : Blo 1488064 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B2233055 : Blo 1488064 2233055 := bstep (se 1 (by rfl) ⟨1674791, by rfl⟩ : syracuseStep 2233055 = 3349583) B3349583
theorem B2511695 : Blo 1488064 2511695 := bstep (se 1 (by rfl) ⟨1883771, by rfl⟩ : syracuseStep 2511695 = 3767543) B3767543
theorem B17191909 : Blo 1488064 17191909 := bstep (se 4 (by rfl) ⟨1611741, by rfl⟩ : syracuseStep 17191909 = 3223483) B3223483
theorem B2233319 : Blo 1488064 2233319 := bstep (se 1 (by rfl) ⟨1674989, by rfl⟩ : syracuseStep 2233319 = 3349979) B3349979
theorem B1676263 : Blo 1488064 1676263 := bstep (se 1 (by rfl) ⟨1257197, by rfl⟩ : syracuseStep 1676263 = 2514395) B2514395
theorem B5026913 : Blo 1488064 5026913 := bstep (se 2 (by rfl) ⟨1885092, by rfl⟩ : syracuseStep 5026913 = 3770185) B3770185
theorem B4240583 : Blo 1488064 4240583 := bstep (se 1 (by rfl) ⟨3180437, by rfl⟩ : syracuseStep 4240583 = 6360875) B6360875
theorem B2233577 : Blo 1488064 2233577 := bstep (se 2 (by rfl) ⟨837591, by rfl⟩ : syracuseStep 2233577 = 1675183) B1675183
theorem B1488159 : Blo 1488064 1488159 := bstep (se 1 (by rfl) ⟨1116119, by rfl⟩ : syracuseStep 1488159 = 2232239) B2232239
theorem B2233631 : Blo 1488064 2233631 := bstep (se 1 (by rfl) ⟨1675223, by rfl⟩ : syracuseStep 2233631 = 3350447) B3350447
theorem B1488219 : Blo 1488064 1488219 := bstep (se 1 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 1488219 = 2232329) B2232329
theorem B1488239 : Blo 1488064 1488239 := bstep (se 1 (by rfl) ⟨1116179, by rfl⟩ : syracuseStep 1488239 = 2232359) B2232359
theorem B1488295 : Blo 1488064 1488295 := bstep (se 1 (by rfl) ⟨1116221, by rfl⟩ : syracuseStep 1488295 = 2232443) B2232443
theorem B2233799 : Blo 1488064 2233799 := bstep (se 1 (by rfl) ⟨1675349, by rfl⟩ : syracuseStep 2233799 = 3350699) B3350699
theorem B1488379 : Blo 1488064 1488379 := bstep (se 1 (by rfl) ⟨1116284, by rfl⟩ : syracuseStep 1488379 = 2232569) B2232569
theorem B1488447 : Blo 1488064 1488447 := bstep (se 1 (by rfl) ⟨1116335, by rfl⟩ : syracuseStep 1488447 = 2232671) B2232671
theorem B1488455 : Blo 1488064 1488455 := bstep (se 1 (by rfl) ⟨1116341, by rfl⟩ : syracuseStep 1488455 = 2232683) B2232683
theorem B14317195 : Blo 1488064 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B1488607 : Blo 1488064 1488607 := bstep (se 1 (by rfl) ⟨1116455, by rfl⟩ : syracuseStep 1488607 = 2232911) B2232911
theorem B6788893 : Blo 1488064 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B7542557 : Blo 1488064 7542557 := bstep (se 3 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 7542557 = 2828459) B2828459
theorem B2234153 : Blo 1488064 2234153 := bstep (se 2 (by rfl) ⟨837807, by rfl⟩ : syracuseStep 2234153 = 1675615) B1675615
theorem B1488687 : Blo 1488064 1488687 := bstep (se 1 (by rfl) ⟨1116515, by rfl⟩ : syracuseStep 1488687 = 2233031) B2233031
theorem B2512687 : Blo 1488064 2512687 := bstep (se 1 (by rfl) ⟨1884515, by rfl⟩ : syracuseStep 2512687 = 3769031) B3769031
theorem B2234159 : Blo 1488064 2234159 := bstep (se 1 (by rfl) ⟨1675619, by rfl⟩ : syracuseStep 2234159 = 3351239) B3351239
theorem B3577655 : Blo 1488064 3577655 := bstep (se 1 (by rfl) ⟨2683241, by rfl⟩ : syracuseStep 3577655 = 5366483) B5366483
theorem B8484695 : Blo 1488064 8484695 := bstep (se 1 (by rfl) ⟨6363521, by rfl⟩ : syracuseStep 8484695 = 12727043) B12727043
theorem B1488795 : Blo 1488064 1488795 := bstep (se 1 (by rfl) ⟨1116596, by rfl⟩ : syracuseStep 1488795 = 2233193) B2233193
theorem B3348431 : Blo 1488064 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B1488847 : Blo 1488064 1488847 := bstep (se 1 (by rfl) ⟨1116635, by rfl⟩ : syracuseStep 1488847 = 2233271) B2233271
theorem B1488871 : Blo 1488064 1488871 := bstep (se 1 (by rfl) ⟨1116653, by rfl⟩ : syracuseStep 1488871 = 2233307) B2233307
theorem B20363399 : Blo 1488064 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B2234633 : Blo 1488064 2234633 := bstep (se 2 (by rfl) ⟨837987, by rfl⟩ : syracuseStep 2234633 = 1675975) B1675975
theorem B7158041 : Blo 1488064 7158041 := bstep (se 2 (by rfl) ⟨2684265, by rfl⟩ : syracuseStep 7158041 = 5368531) B5368531
theorem B1489183 : Blo 1488064 1489183 := bstep (se 1 (by rfl) ⟨1116887, by rfl⟩ : syracuseStep 1489183 = 2233775) B2233775
theorem B3348809 : Blo 1488064 3348809 := bstep (se 2 (by rfl) ⟨1255803, by rfl⟩ : syracuseStep 3348809 = 2511607) B2511607
theorem B3348827 : Blo 1488064 3348827 := bstep (se 1 (by rfl) ⟨2511620, by rfl⟩ : syracuseStep 3348827 = 5023241) B5023241
theorem B1489243 : Blo 1488064 1489243 := bstep (se 1 (by rfl) ⟨1116932, by rfl⟩ : syracuseStep 1489243 = 2233865) B2233865
theorem B1489263 : Blo 1488064 1489263 := bstep (se 1 (by rfl) ⟨1116947, by rfl⟩ : syracuseStep 1489263 = 2233895) B2233895
theorem B2234735 : Blo 1488064 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B33077629 : Blo 1488064 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B1489319 : Blo 1488064 1489319 := bstep (se 1 (by rfl) ⟨1116989, by rfl⟩ : syracuseStep 1489319 = 2233979) B2233979
theorem B5028263 : Blo 1488064 5028263 := bstep (se 1 (by rfl) ⟨3771197, by rfl⟩ : syracuseStep 5028263 = 7542395) B7542395
theorem B1489403 : Blo 1488064 1489403 := bstep (se 1 (by rfl) ⟨1117052, by rfl⟩ : syracuseStep 1489403 = 2234105) B2234105
theorem B4241915 : Blo 1488064 4241915 := bstep (se 1 (by rfl) ⟨3181436, by rfl⟩ : syracuseStep 4241915 = 6362873) B6362873
theorem B1489471 : Blo 1488064 1489471 := bstep (se 1 (by rfl) ⟨1117103, by rfl⟩ : syracuseStep 1489471 = 2234207) B2234207
theorem B4241983 : Blo 1488064 4241983 := bstep (se 1 (by rfl) ⟨3181487, by rfl⟩ : syracuseStep 4241983 = 6362975) B6362975
theorem B1489479 : Blo 1488064 1489479 := bstep (se 1 (by rfl) ⟨1117109, by rfl⟩ : syracuseStep 1489479 = 2234219) B2234219
theorem B14318153 : Blo 1488064 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B5028425 : Blo 1488064 5028425 := bstep (se 2 (by rfl) ⟨1885659, by rfl⟩ : syracuseStep 5028425 = 3771319) B3771319
theorem B2234951 : Blo 1488064 2234951 := bstep (se 1 (by rfl) ⟨1676213, by rfl⟩ : syracuseStep 2234951 = 3352427) B3352427
theorem B2234987 : Blo 1488064 2234987 := bstep (se 1 (by rfl) ⟨1676240, by rfl⟩ : syracuseStep 2234987 = 3352481) B3352481
theorem B4078201 : Blo 1488064 4078201 := bstep (se 2 (by rfl) ⟨1529325, by rfl⟩ : syracuseStep 4078201 = 3058651) B3058651
theorem B7158461 : Blo 1488064 7158461 := bstep (se 3 (by rfl) ⟨1342211, by rfl⟩ : syracuseStep 7158461 = 2684423) B2684423
theorem B1489631 : Blo 1488064 1489631 := bstep (se 1 (by rfl) ⟨1117223, by rfl⟩ : syracuseStep 1489631 = 2234447) B2234447
theorem B1489711 : Blo 1488064 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B3349403 : Blo 1488064 3349403 := bstep (se 1 (by rfl) ⟨2512052, by rfl⟩ : syracuseStep 3349403 = 5024105) B5024105
theorem B1489819 : Blo 1488064 1489819 := bstep (se 1 (by rfl) ⟨1117364, by rfl⟩ : syracuseStep 1489819 = 2234729) B2234729
theorem B27171767 : Blo 1488064 27171767 := bstep (se 1 (by rfl) ⟨20378825, by rfl⟩ : syracuseStep 27171767 = 40757651) B40757651
theorem B1489871 : Blo 1488064 1489871 := bstep (se 1 (by rfl) ⟨1117403, by rfl⟩ : syracuseStep 1489871 = 2234807) B2234807
theorem B1489895 : Blo 1488064 1489895 := bstep (se 1 (by rfl) ⟨1117421, by rfl⟩ : syracuseStep 1489895 = 2234843) B2234843
theorem B3578867 : Blo 1488064 3578867 := bstep (se 1 (by rfl) ⟨2684150, by rfl⟩ : syracuseStep 3578867 = 5368301) B5368301
theorem B3349601 : Blo 1488064 3349601 := bstep (se 2 (by rfl) ⟨1256100, by rfl⟩ : syracuseStep 3349601 = 2512201) B2512201
theorem B16956539 : Blo 1488064 16956539 := bstep (se 1 (by rfl) ⟨12717404, by rfl⟩ : syracuseStep 16956539 = 25434809) B25434809
theorem B25443557 : Blo 1488064 25443557 := bstep (se 4 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 25443557 = 4770667) B4770667
theorem B3349799 : Blo 1488064 3349799 := bstep (se 1 (by rfl) ⟨2512349, by rfl⟩ : syracuseStep 3349799 = 5024699) B5024699
theorem B1883503 : Blo 1488064 1883503 := bstep (se 1 (by rfl) ⟨1412627, by rfl⟩ : syracuseStep 1883503 = 2825255) B2825255
theorem B7150967 : Blo 1488064 7150967 := bstep (se 1 (by rfl) ⟨5363225, by rfl⟩ : syracuseStep 7150967 = 10726451) B10726451
theorem B6364615 : Blo 1488064 6364615 := bstep (se 1 (by rfl) ⟨4773461, by rfl⟩ : syracuseStep 6364615 = 9546923) B9546923
theorem B3579385 : Blo 1488064 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B3350177 : Blo 1488064 3350177 := bstep (se 2 (by rfl) ⟨1256316, by rfl⟩ : syracuseStep 3350177 = 2512633) B2512633
theorem B14516009 : Blo 1488064 14516009 := bstep (se 2 (by rfl) ⟨5443503, by rfl⟩ : syracuseStep 14516009 = 10887007) B10887007
theorem B5365561 : Blo 1488064 5365561 := bstep (se 2 (by rfl) ⟨2012085, by rfl⟩ : syracuseStep 5365561 = 4024171) B4024171
theorem B12713921 : Blo 1488064 12713921 := bstep (se 2 (by rfl) ⟨4767720, by rfl⟩ : syracuseStep 12713921 = 9535441) B9535441
theorem B6791303 : Blo 1488064 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B8045119 : Blo 1488064 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B12714671 : Blo 1488064 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B3351275 : Blo 1488064 3351275 := bstep (se 1 (by rfl) ⟨2513456, by rfl⟩ : syracuseStep 3351275 = 5026913) B5026913
theorem B4530941 : Blo 1488064 4530941 := bstep (se 3 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 4530941 = 1699103) B1699103
theorem B2827055 : Blo 1488064 2827055 := bstep (se 1 (by rfl) ⟨2120291, by rfl⟩ : syracuseStep 2827055 = 4240583) B4240583
theorem B42943385 : Blo 1488064 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B33555383 : Blo 1488064 33555383 := bstep (se 1 (by rfl) ⟨25166537, by rfl⟩ : syracuseStep 33555383 = 50333075) B50333075
theorem B2384969 : Blo 1488064 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B16966745 : Blo 1488064 16966745 := bstep (se 2 (by rfl) ⟨6362529, by rfl⟩ : syracuseStep 16966745 = 12725059) B12725059
theorem B2385001 : Blo 1488064 2385001 := bstep (se 2 (by rfl) ⟨894375, by rfl⟩ : syracuseStep 2385001 = 1788751) B1788751
theorem B13575599 : Blo 1488064 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B4359673 : Blo 1488064 4359673 := bstep (se 2 (by rfl) ⟨1634877, by rfl⟩ : syracuseStep 4359673 = 3269755) B3269755
theorem B5367377 : Blo 1488064 5367377 := bstep (se 2 (by rfl) ⟨2012766, by rfl⟩ : syracuseStep 5367377 = 4025533) B4025533
theorem B3352175 : Blo 1488064 3352175 := bstep (se 1 (by rfl) ⟨2514131, by rfl⟩ : syracuseStep 3352175 = 5028263) B5028263
theorem B3770023 : Blo 1488064 3770023 := bstep (se 1 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 3770023 = 5655035) B5655035
theorem B2827943 : Blo 1488064 2827943 := bstep (se 1 (by rfl) ⟨2120957, by rfl⟩ : syracuseStep 2827943 = 4241915) B4241915
theorem B9545435 : Blo 1488064 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B3352283 : Blo 1488064 3352283 := bstep (se 1 (by rfl) ⟨2514212, by rfl⟩ : syracuseStep 3352283 = 5028425) B5028425
theorem B4769567 : Blo 1488064 4769567 := bstep (se 1 (by rfl) ⟨3577175, by rfl⟩ : syracuseStep 4769567 = 7154351) B7154351
theorem B36226871 : Blo 1488064 36226871 := bstep (se 1 (by rfl) ⟨27170153, by rfl⟩ : syracuseStep 36226871 = 54340307) B54340307
theorem B19089229 : Blo 1488064 19089229 := bstep (se 3 (by rfl) ⟨3579230, by rfl⟩ : syracuseStep 19089229 = 7158461) B7158461
theorem B18114511 : Blo 1488064 18114511 := bstep (se 1 (by rfl) ⟨13585883, by rfl⟩ : syracuseStep 18114511 = 27171767) B27171767
theorem B2385911 : Blo 1488064 2385911 := bstep (se 1 (by rfl) ⟨1789433, by rfl⟩ : syracuseStep 2385911 = 3578867) B3578867
theorem B19089593 : Blo 1488064 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B2263231 : Blo 1488064 2263231 := bstep (se 1 (by rfl) ⟨1697423, by rfl⟩ : syracuseStep 2263231 = 3394847) B3394847
theorem B6359249 : Blo 1488064 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B3180779 : Blo 1488064 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B3770671 : Blo 1488064 3770671 := bstep (se 1 (by rfl) ⟨2828003, by rfl⟩ : syracuseStep 3770671 = 5656007) B5656007
theorem B20367773 : Blo 1488064 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B7154081 : Blo 1488064 7154081 := bstep (se 2 (by rfl) ⟨2682780, by rfl⟩ : syracuseStep 7154081 = 5365561) B5365561
theorem B83773925 : Blo 1488064 83773925 := bstep (se 4 (by rfl) ⟨7853805, by rfl⟩ : syracuseStep 83773925 = 15707611) B15707611
theorem B9677339 : Blo 1488064 9677339 := bstep (se 1 (by rfl) ⟨7258004, by rfl⟩ : syracuseStep 9677339 = 14516009) B14516009
theorem B4238315 : Blo 1488064 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B1674463 : Blo 1488064 1674463 := bstep (se 1 (by rfl) ⟨1255847, by rfl⟩ : syracuseStep 1674463 = 2511695) B2511695
theorem B32206157 : Blo 1488064 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B5655977 : Blo 1488064 5655977 := bstep (se 2 (by rfl) ⟨2120991, by rfl⟩ : syracuseStep 5655977 = 4241983) B4241983
theorem B38145653 : Blo 1488064 38145653 := bstep (se 5 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 38145653 = 3576155) B3576155
theorem B5025455 : Blo 1488064 5025455 := bstep (se 1 (by rfl) ⟨3769091, by rfl⟩ : syracuseStep 5025455 = 7538183) B7538183
theorem B2232185 : Blo 1488064 2232185 := bstep (se 2 (by rfl) ⟨837069, by rfl⟩ : syracuseStep 2232185 = 1674139) B1674139
theorem B5656463 : Blo 1488064 5656463 := bstep (se 1 (by rfl) ⟨4242347, by rfl⟩ : syracuseStep 5656463 = 8484695) B8484695
theorem B2232287 : Blo 1488064 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B5025779 : Blo 1488064 5025779 := bstep (se 1 (by rfl) ⟨3769334, by rfl⟩ : syracuseStep 5025779 = 7538669) B7538669
theorem B4772027 : Blo 1488064 4772027 := bstep (se 1 (by rfl) ⟨3579020, by rfl⟩ : syracuseStep 4772027 = 7158041) B7158041
theorem B2232539 : Blo 1488064 2232539 := bstep (se 1 (by rfl) ⟨1674404, by rfl⟩ : syracuseStep 2232539 = 3348809) B3348809
theorem B2232551 : Blo 1488064 2232551 := bstep (se 1 (by rfl) ⟨1674413, by rfl⟩ : syracuseStep 2232551 = 3348827) B3348827
theorem B5026103 : Blo 1488064 5026103 := bstep (se 1 (by rfl) ⟨3769577, by rfl⟩ : syracuseStep 5026103 = 7539155) B7539155
theorem B2232713 : Blo 1488064 2232713 := bstep (se 2 (by rfl) ⟨837267, by rfl⟩ : syracuseStep 2232713 = 1674535) B1674535
theorem B2683343 : Blo 1488064 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B2511337 : Blo 1488064 2511337 := bstep (se 2 (by rfl) ⟨941751, by rfl⟩ : syracuseStep 2511337 = 1883503) B1883503
theorem B2232809 : Blo 1488064 2232809 := bstep (se 2 (by rfl) ⟨837303, by rfl⟩ : syracuseStep 2232809 = 1674607) B1674607
theorem B5026319 : Blo 1488064 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B4239955 : Blo 1488064 4239955 := bstep (se 1 (by rfl) ⟨3179966, by rfl⟩ : syracuseStep 4239955 = 6359933) B6359933
theorem B4649567 : Blo 1488064 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B2232935 : Blo 1488064 2232935 := bstep (se 1 (by rfl) ⟨1674701, by rfl⟩ : syracuseStep 2232935 = 3349403) B3349403
theorem B4772513 : Blo 1488064 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B2233067 : Blo 1488064 2233067 := bstep (se 1 (by rfl) ⟨1674800, by rfl⟩ : syracuseStep 2233067 = 3349601) B3349601
theorem B2233097 : Blo 1488064 2233097 := bstep (se 2 (by rfl) ⟨837411, by rfl⟩ : syracuseStep 2233097 = 1674823) B1674823
theorem B3576617 : Blo 1488064 3576617 := bstep (se 2 (by rfl) ⟨1341231, by rfl⟩ : syracuseStep 3576617 = 2682463) B2682463
theorem B9540413 : Blo 1488064 9540413 := bstep (se 3 (by rfl) ⟨1788827, by rfl⟩ : syracuseStep 9540413 = 3577655) B3577655
theorem B16962371 : Blo 1488064 16962371 := bstep (se 1 (by rfl) ⟨12721778, by rfl⟩ : syracuseStep 16962371 = 25443557) B25443557
theorem B2233199 : Blo 1488064 2233199 := bstep (se 1 (by rfl) ⟨1674899, by rfl⟩ : syracuseStep 2233199 = 3349799) B3349799
theorem B4240457 : Blo 1488064 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2233451 : Blo 1488064 2233451 := bstep (se 1 (by rfl) ⟨1675088, by rfl⟩ : syracuseStep 2233451 = 3350177) B3350177
theorem B91690181 : Blo 1488064 91690181 := bstep (se 4 (by rfl) ⟨8595954, by rfl⟩ : syracuseStep 91690181 = 17191909) B17191909
theorem B1488079 : Blo 1488064 1488079 := bstep (se 1 (by rfl) ⟨1116059, by rfl⟩ : syracuseStep 1488079 = 2232119) B2232119
theorem B5092627 : Blo 1488064 5092627 := bstep (se 1 (by rfl) ⟨3819470, by rfl⟩ : syracuseStep 5092627 = 7638941) B7638941
theorem B8475947 : Blo 1488064 8475947 := bstep (se 1 (by rfl) ⟨6356960, by rfl⟩ : syracuseStep 8475947 = 12713921) B12713921
theorem B2233691 : Blo 1488064 2233691 := bstep (se 1 (by rfl) ⟨1675268, by rfl⟩ : syracuseStep 2233691 = 3350537) B3350537
theorem B6116705 : Blo 1488064 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B19076471 : Blo 1488064 19076471 := bstep (se 1 (by rfl) ⟨14307353, by rfl⟩ : syracuseStep 19076471 = 28614707) B28614707
theorem B1488283 : Blo 1488064 1488283 := bstep (se 1 (by rfl) ⟨1116212, by rfl⟩ : syracuseStep 1488283 = 2232425) B2232425
theorem B5027399 : Blo 1488064 5027399 := bstep (se 1 (by rfl) ⟨3770549, by rfl⟩ : syracuseStep 5027399 = 7541099) B7541099
theorem B54318701 : Blo 1488064 54318701 := bstep (se 3 (by rfl) ⟨10184756, by rfl⟩ : syracuseStep 54318701 = 20369513) B20369513
theorem B1488495 : Blo 1488064 1488495 := bstep (se 1 (by rfl) ⟨1116371, by rfl⟩ : syracuseStep 1488495 = 2232743) B2232743
theorem B2233967 : Blo 1488064 2233967 := bstep (se 1 (by rfl) ⟨1675475, by rfl⟩ : syracuseStep 2233967 = 3350951) B3350951
theorem B2512505 : Blo 1488064 2512505 := bstep (se 2 (by rfl) ⟨942189, by rfl⟩ : syracuseStep 2512505 = 1884379) B1884379
theorem B1488551 : Blo 1488064 1488551 := bstep (se 1 (by rfl) ⟨1116413, by rfl⟩ : syracuseStep 1488551 = 2232827) B2232827
theorem B2234039 : Blo 1488064 2234039 := bstep (se 1 (by rfl) ⟨1675529, by rfl⟩ : syracuseStep 2234039 = 3351059) B3351059
theorem B2234075 : Blo 1488064 2234075 := bstep (se 1 (by rfl) ⟨1675556, by rfl⟩ : syracuseStep 2234075 = 3351113) B3351113
theorem B1488635 : Blo 1488064 1488635 := bstep (se 1 (by rfl) ⟨1116476, by rfl⟩ : syracuseStep 1488635 = 2232953) B2232953
theorem B1488671 : Blo 1488064 1488671 := bstep (se 1 (by rfl) ⟨1116503, by rfl⟩ : syracuseStep 1488671 = 2233007) B2233007
theorem B3348287 : Blo 1488064 3348287 := bstep (se 1 (by rfl) ⟨2511215, by rfl⟩ : syracuseStep 3348287 = 5022431) B5022431
theorem B1488703 : Blo 1488064 1488703 := bstep (se 1 (by rfl) ⟨1116527, by rfl⟩ : syracuseStep 1488703 = 2233055) B2233055
theorem B2234249 : Blo 1488064 2234249 := bstep (se 2 (by rfl) ⟨837843, by rfl⟩ : syracuseStep 2234249 = 1675687) B1675687
theorem B1488879 : Blo 1488064 1488879 := bstep (se 1 (by rfl) ⟨1116659, by rfl⟩ : syracuseStep 1488879 = 2233319) B2233319
theorem B2234351 : Blo 1488064 2234351 := bstep (se 1 (by rfl) ⟨1675763, by rfl⟩ : syracuseStep 2234351 = 3351527) B3351527
theorem B3348575 : Blo 1488064 3348575 := bstep (se 1 (by rfl) ⟨2511431, by rfl⟩ : syracuseStep 3348575 = 5022863) B5022863
theorem B2512991 : Blo 1488064 2512991 := bstep (se 1 (by rfl) ⟨1884743, by rfl⟩ : syracuseStep 2512991 = 3769487) B3769487
theorem B1489051 : Blo 1488064 1489051 := bstep (se 1 (by rfl) ⟨1116788, by rfl⟩ : syracuseStep 1489051 = 2233577) B2233577
theorem B5437601 : Blo 1488064 5437601 := bstep (se 2 (by rfl) ⟨2039100, by rfl⟩ : syracuseStep 5437601 = 4078201) B4078201
theorem B1489087 : Blo 1488064 1489087 := bstep (se 1 (by rfl) ⟨1116815, by rfl⟩ : syracuseStep 1489087 = 2233631) B2233631
theorem B4241641 : Blo 1488064 4241641 := bstep (se 2 (by rfl) ⟨1590615, by rfl⟩ : syracuseStep 4241641 = 3181231) B3181231
theorem B2234603 : Blo 1488064 2234603 := bstep (se 1 (by rfl) ⟨1675952, by rfl⟩ : syracuseStep 2234603 = 3351905) B3351905
theorem B2234663 : Blo 1488064 2234663 := bstep (se 1 (by rfl) ⟨1675997, by rfl⟩ : syracuseStep 2234663 = 3351995) B3351995
theorem B1489199 : Blo 1488064 1489199 := bstep (se 1 (by rfl) ⟨1116899, by rfl⟩ : syracuseStep 1489199 = 2233799) B2233799
theorem B2234747 : Blo 1488064 2234747 := bstep (se 1 (by rfl) ⟨1676060, by rfl⟩ : syracuseStep 2234747 = 3352121) B3352121
theorem B5028371 : Blo 1488064 5028371 := bstep (se 1 (by rfl) ⟨3771278, by rfl⟩ : syracuseStep 5028371 = 7542557) B7542557
theorem B1489435 : Blo 1488064 1489435 := bstep (se 1 (by rfl) ⟨1117076, by rfl⟩ : syracuseStep 1489435 = 2234153) B2234153
theorem B1489439 : Blo 1488064 1489439 := bstep (se 1 (by rfl) ⟨1117079, by rfl⟩ : syracuseStep 1489439 = 2234159) B2234159
theorem B4242041 : Blo 1488064 4242041 := bstep (se 2 (by rfl) ⟨1590765, by rfl⟩ : syracuseStep 4242041 = 3181531) B3181531
theorem B2235017 : Blo 1488064 2235017 := bstep (se 2 (by rfl) ⟨838131, by rfl⟩ : syracuseStep 2235017 = 1676263) B1676263
theorem B8477405 : Blo 1488064 8477405 := bstep (se 3 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 8477405 = 3179027) B3179027
theorem B3349331 : Blo 1488064 3349331 := bstep (se 1 (by rfl) ⟨2511998, by rfl⟩ : syracuseStep 3349331 = 5023997) B5023997
theorem B1489755 : Blo 1488064 1489755 := bstep (se 1 (by rfl) ⟨1117316, by rfl⟩ : syracuseStep 1489755 = 2234633) B2234633
theorem B1489823 : Blo 1488064 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B42933239 : Blo 1488064 42933239 := bstep (se 1 (by rfl) ⟨32199929, by rfl⟩ : syracuseStep 42933239 = 64399859) B64399859
theorem B1489967 : Blo 1488064 1489967 := bstep (se 1 (by rfl) ⟨1117475, by rfl⟩ : syracuseStep 1489967 = 2234951) B2234951
theorem B1489991 : Blo 1488064 1489991 := bstep (se 1 (by rfl) ⟨1117493, by rfl⟩ : syracuseStep 1489991 = 2234987) B2234987
theorem B9542771 : Blo 1488064 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B6364307 : Blo 1488064 6364307 := bstep (se 1 (by rfl) ⟨4773230, by rfl⟩ : syracuseStep 6364307 = 9546461) B9546461
theorem B8486153 : Blo 1488064 8486153 := bstep (se 2 (by rfl) ⟨3182307, by rfl⟩ : syracuseStep 8486153 = 6364615) B6364615
theorem B176414021 : Blo 1488064 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B3349871 : Blo 1488064 3349871 := bstep (se 1 (by rfl) ⟨2512403, by rfl⟩ : syracuseStep 3349871 = 5024807) B5024807
theorem B2121071 : Blo 1488064 2121071 := bstep (se 1 (by rfl) ⟨1590803, by rfl⟩ : syracuseStep 2121071 = 3181607) B3181607
theorem B2514287 : Blo 1488064 2514287 := bstep (se 1 (by rfl) ⟨1885715, by rfl⟩ : syracuseStep 2514287 = 3771431) B3771431
theorem B11304359 : Blo 1488064 11304359 := bstep (se 1 (by rfl) ⟨8478269, by rfl⟩ : syracuseStep 11304359 = 16956539) B16956539
theorem B6446567 : Blo 1488064 6446567 := bstep (se 1 (by rfl) ⟨4834925, by rfl⟩ : syracuseStep 6446567 = 9669851) B9669851
theorem B4767311 : Blo 1488064 4767311 := bstep (se 1 (by rfl) ⟨3575483, by rfl⟩ : syracuseStep 4767311 = 7150967) B7150967
theorem B3350159 : Blo 1488064 3350159 := bstep (se 1 (by rfl) ⟨2512619, by rfl⟩ : syracuseStep 3350159 = 5025239) B5025239
theorem B9051857 : Blo 1488064 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B3350249 : Blo 1488064 3350249 := bstep (se 2 (by rfl) ⟨1256343, by rfl⟩ : syracuseStep 3350249 = 2512687) B2512687
theorem B4300667 : Blo 1488064 4300667 := bstep (se 1 (by rfl) ⟨3225500, by rfl⟩ : syracuseStep 4300667 = 6451001) B6451001
theorem B2383771 : Blo 1488064 2383771 := bstep (se 1 (by rfl) ⟨1787828, by rfl⟩ : syracuseStep 2383771 = 3575657) B3575657
theorem B3350735 : Blo 1488064 3350735 := bstep (se 1 (by rfl) ⟨2513051, by rfl⟩ : syracuseStep 3350735 = 5026103) B5026103
theorem B3350879 : Blo 1488064 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B2384411 : Blo 1488064 2384411 := bstep (se 1 (by rfl) ⟨1788308, by rfl⟩ : syracuseStep 2384411 = 3576617) B3576617
theorem B1884703 : Blo 1488064 1884703 := bstep (se 1 (by rfl) ⟨1413527, by rfl⟩ : syracuseStep 1884703 = 2827055) B2827055
theorem B16957997 : Blo 1488064 16957997 := bstep (se 3 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 16957997 = 6359249) B6359249
theorem B2826971 : Blo 1488064 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B5653273 : Blo 1488064 5653273 := bstep (se 2 (by rfl) ⟨2119977, by rfl⟩ : syracuseStep 5653273 = 4239955) B4239955
theorem B3351599 : Blo 1488064 3351599 := bstep (se 1 (by rfl) ⟨2513699, by rfl⟩ : syracuseStep 3351599 = 5027399) B5027399
theorem B1885295 : Blo 1488064 1885295 := bstep (se 1 (by rfl) ⟨1413971, by rfl⟩ : syracuseStep 1885295 = 2827943) B2827943
theorem B3179711 : Blo 1488064 3179711 := bstep (se 1 (by rfl) ⟨2384783, by rfl⟩ : syracuseStep 3179711 = 4769567) B4769567
theorem B24151247 : Blo 1488064 24151247 := bstep (se 1 (by rfl) ⟨18113435, by rfl⟩ : syracuseStep 24151247 = 36226871) B36226871
theorem B1590607 : Blo 1488064 1590607 := bstep (se 1 (by rfl) ⟨1192955, by rfl⟩ : syracuseStep 1590607 = 2385911) B2385911
theorem B3180001 : Blo 1488064 3180001 := bstep (se 2 (by rfl) ⟨1192500, by rfl⟩ : syracuseStep 3180001 = 2385001) B2385001
theorem B4769387 : Blo 1488064 4769387 := bstep (se 1 (by rfl) ⟨3577040, by rfl⟩ : syracuseStep 4769387 = 7154081) B7154081
theorem B3352247 : Blo 1488064 3352247 := bstep (se 1 (by rfl) ⟨2514185, by rfl⟩ : syracuseStep 3352247 = 5028371) B5028371
theorem B2828027 : Blo 1488064 2828027 := bstep (se 1 (by rfl) ⟨2121020, by rfl⟩ : syracuseStep 2828027 = 4242041) B4242041
theorem B3770651 : Blo 1488064 3770651 := bstep (se 1 (by rfl) ⟨2827988, by rfl⟩ : syracuseStep 3770651 = 5655977) B5655977
theorem B25430435 : Blo 1488064 25430435 := bstep (se 1 (by rfl) ⟨19072826, by rfl⟩ : syracuseStep 25430435 = 38145653) B38145653
theorem B3770975 : Blo 1488064 3770975 := bstep (se 1 (by rfl) ⟨2828231, by rfl⟩ : syracuseStep 3770975 = 5656463) B5656463
theorem B24152681 : Blo 1488064 24152681 := bstep (se 2 (by rfl) ⟨9057255, by rfl⟩ : syracuseStep 24152681 = 18114511) B18114511
theorem B3181351 : Blo 1488064 3181351 := bstep (se 1 (by rfl) ⟨2386013, by rfl⟩ : syracuseStep 3181351 = 4772027) B4772027
theorem B6359917 : Blo 1488064 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B3017641 : Blo 1488064 3017641 := bstep (se 2 (by rfl) ⟨1131615, by rfl⟩ : syracuseStep 3017641 = 2263231) B2263231
theorem B1788895 : Blo 1488064 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B5655521 : Blo 1488064 5655521 := bstep (se 2 (by rfl) ⟨2120820, by rfl⟩ : syracuseStep 5655521 = 4241641) B4241641
theorem B3181675 : Blo 1488064 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B6360275 : Blo 1488064 6360275 := bstep (se 1 (by rfl) ⟨4770206, by rfl⟩ : syracuseStep 6360275 = 9540413) B9540413
theorem B11308247 : Blo 1488064 11308247 := bstep (se 1 (by rfl) ⟨8481185, by rfl⟩ : syracuseStep 11308247 = 16962371) B16962371
theorem B10726825 : Blo 1488064 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B12717647 : Blo 1488064 12717647 := bstep (se 1 (by rfl) ⟨9538235, by rfl⟩ : syracuseStep 12717647 = 19076471) B19076471
theorem B5656189 : Blo 1488064 5656189 := bstep (se 3 (by rfl) ⟨1060535, by rfl⟩ : syracuseStep 5656189 = 2121071) B2121071
theorem B36212467 : Blo 1488064 36212467 := bstep (se 1 (by rfl) ⟨27159350, by rfl⟩ : syracuseStep 36212467 = 54318701) B54318701
theorem B1675003 : Blo 1488064 1675003 := bstep (se 1 (by rfl) ⟨1256252, by rfl⟩ : syracuseStep 1675003 = 2512505) B2512505
theorem B2232191 : Blo 1488064 2232191 := bstep (se 1 (by rfl) ⟨1674143, by rfl⟩ : syracuseStep 2232191 = 3348287) B3348287
theorem B2232383 : Blo 1488064 2232383 := bstep (se 1 (by rfl) ⟨1674287, by rfl⟩ : syracuseStep 2232383 = 3348575) B3348575
theorem B1675327 : Blo 1488064 1675327 := bstep (se 1 (by rfl) ⟨1256495, by rfl⟩ : syracuseStep 1675327 = 2512991) B2512991
theorem B3625067 : Blo 1488064 3625067 := bstep (se 1 (by rfl) ⟨2718800, by rfl⟩ : syracuseStep 3625067 = 5437601) B5437601
theorem B12726395 : Blo 1488064 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B12398845 : Blo 1488064 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B13578515 : Blo 1488064 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B2232617 : Blo 1488064 2232617 := bstep (se 2 (by rfl) ⟨837231, by rfl⟩ : syracuseStep 2232617 = 1674463) B1674463
theorem B55849283 : Blo 1488064 55849283 := bstep (se 1 (by rfl) ⟨41886962, by rfl⟩ : syracuseStep 55849283 = 83773925) B83773925
theorem B6451559 : Blo 1488064 6451559 := bstep (se 1 (by rfl) ⟨4838669, by rfl⟩ : syracuseStep 6451559 = 9677339) B9677339
theorem B2232887 : Blo 1488064 2232887 := bstep (se 1 (by rfl) ⟨1674665, by rfl⟩ : syracuseStep 2232887 = 3349331) B3349331
theorem B5812897 : Blo 1488064 5812897 := bstep (se 2 (by rfl) ⟨2179836, by rfl⟩ : syracuseStep 5812897 = 4359673) B4359673
theorem B6361847 : Blo 1488064 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B5657435 : Blo 1488064 5657435 := bstep (se 1 (by rfl) ⟨4243076, by rfl⟩ : syracuseStep 5657435 = 8486153) B8486153
theorem B117609347 : Blo 1488064 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B5026697 : Blo 1488064 5026697 := bstep (se 2 (by rfl) ⟨1885011, by rfl⟩ : syracuseStep 5026697 = 3770023) B3770023
theorem B2233247 : Blo 1488064 2233247 := bstep (se 1 (by rfl) ⟨1674935, by rfl⟩ : syracuseStep 2233247 = 3349871) B3349871
theorem B1676191 : Blo 1488064 1676191 := bstep (se 1 (by rfl) ⟨1257143, by rfl⟩ : syracuseStep 1676191 = 2514287) B2514287
theorem B4297711 : Blo 1488064 4297711 := bstep (se 1 (by rfl) ⟨3223283, by rfl⟩ : syracuseStep 4297711 = 6446567) B6446567
theorem B2233439 : Blo 1488064 2233439 := bstep (se 1 (by rfl) ⟨1675079, by rfl⟩ : syracuseStep 2233439 = 3350159) B3350159
theorem B6034571 : Blo 1488064 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B2233499 : Blo 1488064 2233499 := bstep (se 1 (by rfl) ⟨1675124, by rfl⟩ : syracuseStep 2233499 = 3350249) B3350249
theorem B1488123 : Blo 1488064 1488123 := bstep (se 1 (by rfl) ⟨1116092, by rfl⟩ : syracuseStep 1488123 = 2232185) B2232185
theorem B1488191 : Blo 1488064 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B4527535 : Blo 1488064 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B1488359 : Blo 1488064 1488359 := bstep (se 1 (by rfl) ⟨1116269, by rfl⟩ : syracuseStep 1488359 = 2232539) B2232539
theorem B1488367 : Blo 1488064 1488367 := bstep (se 1 (by rfl) ⟨1116275, by rfl⟩ : syracuseStep 1488367 = 2232551) B2232551
theorem B1488475 : Blo 1488064 1488475 := bstep (se 1 (by rfl) ⟨1116356, by rfl⟩ : syracuseStep 1488475 = 2232713) B2232713
theorem B1488539 : Blo 1488064 1488539 := bstep (se 1 (by rfl) ⟨1116404, by rfl⟩ : syracuseStep 1488539 = 2232809) B2232809
theorem B5027561 : Blo 1488064 5027561 := bstep (se 2 (by rfl) ⟨1885335, by rfl⟩ : syracuseStep 5027561 = 3770671) B3770671
theorem B1488623 : Blo 1488064 1488623 := bstep (se 1 (by rfl) ⟨1116467, by rfl⟩ : syracuseStep 1488623 = 2232935) B2232935
theorem B8476447 : Blo 1488064 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B1488711 : Blo 1488064 1488711 := bstep (se 1 (by rfl) ⟨1116533, by rfl⟩ : syracuseStep 1488711 = 2233067) B2233067
theorem B2234183 : Blo 1488064 2234183 := bstep (se 1 (by rfl) ⟨1675637, by rfl⟩ : syracuseStep 2234183 = 3351275) B3351275
theorem B3020627 : Blo 1488064 3020627 := bstep (se 1 (by rfl) ⟨2265470, by rfl⟩ : syracuseStep 3020627 = 4530941) B4530941
theorem B1488731 : Blo 1488064 1488731 := bstep (se 1 (by rfl) ⟨1116548, by rfl⟩ : syracuseStep 1488731 = 2233097) B2233097
theorem B1488799 : Blo 1488064 1488799 := bstep (se 1 (by rfl) ⟨1116599, by rfl⟩ : syracuseStep 1488799 = 2233199) B2233199
theorem B28628923 : Blo 1488064 28628923 := bstep (se 1 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 28628923 = 42943385) B42943385
theorem B22370255 : Blo 1488064 22370255 := bstep (se 1 (by rfl) ⟨16777691, by rfl⟩ : syracuseStep 22370255 = 33555383) B33555383
theorem B3348449 : Blo 1488064 3348449 := bstep (se 2 (by rfl) ⟨1255668, by rfl⟩ : syracuseStep 3348449 = 2511337) B2511337
theorem B11311163 : Blo 1488064 11311163 := bstep (se 1 (by rfl) ⟨8483372, by rfl⟩ : syracuseStep 11311163 = 16966745) B16966745
theorem B1488967 : Blo 1488064 1488967 := bstep (se 1 (by rfl) ⟨1116725, by rfl⟩ : syracuseStep 1488967 = 2233451) B2233451
theorem B61126787 : Blo 1488064 61126787 := bstep (se 1 (by rfl) ⟨45845090, by rfl⟩ : syracuseStep 61126787 = 91690181) B91690181
theorem B5650631 : Blo 1488064 5650631 := bstep (se 1 (by rfl) ⟨4237973, by rfl⟩ : syracuseStep 5650631 = 8475947) B8475947
theorem B3350519 : Blo 1488064 3350519 := bstep (se 1 (by rfl) ⟨2512889, by rfl⟩ : syracuseStep 3350519 = 5025779) B5025779
theorem B1489127 : Blo 1488064 1489127 := bstep (se 1 (by rfl) ⟨1116845, by rfl⟩ : syracuseStep 1489127 = 2233691) B2233691
theorem B4077803 : Blo 1488064 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B9050399 : Blo 1488064 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B3578251 : Blo 1488064 3578251 := bstep (se 1 (by rfl) ⟨2683688, by rfl⟩ : syracuseStep 3578251 = 5367377) B5367377
theorem B1489311 : Blo 1488064 1489311 := bstep (se 1 (by rfl) ⟨1116983, by rfl⟩ : syracuseStep 1489311 = 2233967) B2233967
theorem B2234783 : Blo 1488064 2234783 := bstep (se 1 (by rfl) ⟨1676087, by rfl⟩ : syracuseStep 2234783 = 3352175) B3352175
theorem B1489359 : Blo 1488064 1489359 := bstep (se 1 (by rfl) ⟨1117019, by rfl⟩ : syracuseStep 1489359 = 2234039) B2234039
theorem B1489383 : Blo 1488064 1489383 := bstep (se 1 (by rfl) ⟨1117037, by rfl⟩ : syracuseStep 1489383 = 2234075) B2234075
theorem B6363623 : Blo 1488064 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B2234855 : Blo 1488064 2234855 := bstep (se 1 (by rfl) ⟨1676141, by rfl⟩ : syracuseStep 2234855 = 3352283) B3352283
theorem B1489499 : Blo 1488064 1489499 := bstep (se 1 (by rfl) ⟨1117124, by rfl⟩ : syracuseStep 1489499 = 2234249) B2234249
theorem B1489567 : Blo 1488064 1489567 := bstep (se 1 (by rfl) ⟨1117175, by rfl⟩ : syracuseStep 1489567 = 2234351) B2234351
theorem B2120519 : Blo 1488064 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B1489735 : Blo 1488064 1489735 := bstep (se 1 (by rfl) ⟨1117301, by rfl⟩ : syracuseStep 1489735 = 2234603) B2234603
theorem B1489775 : Blo 1488064 1489775 := bstep (se 1 (by rfl) ⟨1117331, by rfl⟩ : syracuseStep 1489775 = 2234663) B2234663
theorem B1489831 : Blo 1488064 1489831 := bstep (se 1 (by rfl) ⟨1117373, by rfl⟩ : syracuseStep 1489831 = 2234747) B2234747
theorem B6790169 : Blo 1488064 6790169 := bstep (se 2 (by rfl) ⟨2546313, by rfl⟩ : syracuseStep 6790169 = 5092627) B5092627
theorem B1490011 : Blo 1488064 1490011 := bstep (se 1 (by rfl) ⟨1117508, by rfl⟩ : syracuseStep 1490011 = 2235017) B2235017
theorem B5651603 : Blo 1488064 5651603 := bstep (se 1 (by rfl) ⟨4238702, by rfl⟩ : syracuseStep 5651603 = 8477405) B8477405
theorem B2825543 : Blo 1488064 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B28622159 : Blo 1488064 28622159 := bstep (se 1 (by rfl) ⟨21466619, by rfl⟩ : syracuseStep 28622159 = 42933239) B42933239
theorem B4242871 : Blo 1488064 4242871 := bstep (se 1 (by rfl) ⟨3182153, by rfl⟩ : syracuseStep 4242871 = 6364307) B6364307
theorem B21470771 : Blo 1488064 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B7536239 : Blo 1488064 7536239 := bstep (se 1 (by rfl) ⟨5652179, by rfl⟩ : syracuseStep 7536239 = 11304359) B11304359
theorem B3178207 : Blo 1488064 3178207 := bstep (se 1 (by rfl) ⟨2383655, by rfl⟩ : syracuseStep 3178207 = 4767311) B4767311
theorem B25452305 : Blo 1488064 25452305 := bstep (se 2 (by rfl) ⟨9544614, by rfl⟩ : syracuseStep 25452305 = 19089229) B19089229
theorem B3350303 : Blo 1488064 3350303 := bstep (se 1 (by rfl) ⟨2512727, by rfl⟩ : syracuseStep 3350303 = 5025455) B5025455
theorem B3178361 : Blo 1488064 3178361 := bstep (se 2 (by rfl) ⟨1191885, by rfl⟩ : syracuseStep 3178361 = 2383771) B2383771
theorem B2867111 : Blo 1488064 2867111 := bstep (se 1 (by rfl) ⟨2150333, by rfl⟩ : syracuseStep 2867111 = 4300667) B4300667
theorem B2416711 : Blo 1488064 2416711 := bstep (se 1 (by rfl) ⟨1812533, by rfl⟩ : syracuseStep 2416711 = 3625067) B3625067
theorem B9052343 : Blo 1488064 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B37232855 : Blo 1488064 37232855 := bstep (se 1 (by rfl) ⟨27924641, by rfl⟩ : syracuseStep 37232855 = 55849283) B55849283
theorem B4301039 : Blo 1488064 4301039 := bstep (se 1 (by rfl) ⟨3225779, by rfl⟩ : syracuseStep 4301039 = 6451559) B6451559
theorem B16531793 : Blo 1488064 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B11305331 : Blo 1488064 11305331 := bstep (se 1 (by rfl) ⟨8478998, by rfl⟩ : syracuseStep 11305331 = 16957997) B16957997
theorem B1884647 : Blo 1488064 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B3351131 : Blo 1488064 3351131 := bstep (se 1 (by rfl) ⟨2513348, by rfl⟩ : syracuseStep 3351131 = 5026697) B5026697
theorem B4023047 : Blo 1488064 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B7750529 : Blo 1488064 7750529 := bstep (se 2 (by rfl) ⟨2906448, by rfl⟩ : syracuseStep 7750529 = 5812897) B5812897
theorem B7537697 : Blo 1488064 7537697 := bstep (se 2 (by rfl) ⟨2826636, by rfl⟩ : syracuseStep 7537697 = 5653273) B5653273
theorem B3179591 : Blo 1488064 3179591 := bstep (se 1 (by rfl) ⟨2384693, by rfl⟩ : syracuseStep 3179591 = 4769387) B4769387
theorem B8479889 : Blo 1488064 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B3351707 : Blo 1488064 3351707 := bstep (se 1 (by rfl) ⟨2513780, by rfl⟩ : syracuseStep 3351707 = 5027561) B5027561
theorem B1885351 : Blo 1488064 1885351 := bstep (se 1 (by rfl) ⟨1414013, by rfl⟩ : syracuseStep 1885351 = 2828027) B2828027
theorem B4023521 : Blo 1488064 4023521 := bstep (se 2 (by rfl) ⟨1508820, by rfl⟩ : syracuseStep 4023521 = 3017641) B3017641
theorem B6358429 : Blo 1488064 6358429 := bstep (se 3 (by rfl) ⟨1192205, by rfl⟩ : syracuseStep 6358429 = 2384411) B2384411
theorem B3770347 : Blo 1488064 3770347 := bstep (se 1 (by rfl) ⟨2827760, by rfl⟩ : syracuseStep 3770347 = 5655521) B5655521
theorem B7538831 : Blo 1488064 7538831 := bstep (se 1 (by rfl) ⟨5654123, by rfl⟩ : syracuseStep 7538831 = 11308247) B11308247
theorem B5654717 : Blo 1488064 5654717 := bstep (se 3 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 5654717 = 2120519) B2120519
theorem B19081439 : Blo 1488064 19081439 := bstep (se 1 (by rfl) ⟨14311079, by rfl⟩ : syracuseStep 19081439 = 28622159) B28622159
theorem B4237609 : Blo 1488064 4237609 := bstep (se 2 (by rfl) ⟨1589103, by rfl⟩ : syracuseStep 4237609 = 3178207) B3178207
theorem B313624925 : Blo 1488064 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B14313847 : Blo 1488064 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B5024159 : Blo 1488064 5024159 := bstep (se 1 (by rfl) ⟨3768119, by rfl⟩ : syracuseStep 5024159 = 7536239) B7536239
theorem B16968203 : Blo 1488064 16968203 := bstep (se 1 (by rfl) ⟨12726152, by rfl⟩ : syracuseStep 16968203 = 25452305) B25452305
theorem B1911407 : Blo 1488064 1911407 := bstep (se 1 (by rfl) ⟨1433555, by rfl⟩ : syracuseStep 1911407 = 2867111) B2867111
theorem B4771001 : Blo 1488064 4771001 := bstep (se 2 (by rfl) ⟨1789125, by rfl⟩ : syracuseStep 4771001 = 3578251) B3578251
theorem B3771623 : Blo 1488064 3771623 := bstep (se 1 (by rfl) ⟨2828717, by rfl⟩ : syracuseStep 3771623 = 5657435) B5657435
theorem B10874141 : Blo 1488064 10874141 := bstep (se 3 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 10874141 = 4077803) B4077803
theorem B16100831 : Blo 1488064 16100831 := bstep (se 1 (by rfl) ⟨12075623, by rfl⟩ : syracuseStep 16100831 = 24151247) B24151247
theorem B16969661 : Blo 1488064 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B14913503 : Blo 1488064 14913503 := bstep (se 1 (by rfl) ⟨11185127, by rfl⟩ : syracuseStep 14913503 = 22370255) B22370255
theorem B5730281 : Blo 1488064 5730281 := bstep (se 2 (by rfl) ⟨2148855, by rfl⟩ : syracuseStep 5730281 = 4297711) B4297711
theorem B2232299 : Blo 1488064 2232299 := bstep (se 1 (by rfl) ⟨1674224, by rfl⟩ : syracuseStep 2232299 = 3348449) B3348449
theorem B7540775 : Blo 1488064 7540775 := bstep (se 1 (by rfl) ⟨5655581, by rfl⟩ : syracuseStep 7540775 = 11311163) B11311163
theorem B40751191 : Blo 1488064 40751191 := bstep (se 1 (by rfl) ⟨30563393, by rfl⟩ : syracuseStep 40751191 = 61126787) B61126787
theorem B6033599 : Blo 1488064 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B16953623 : Blo 1488064 16953623 := bstep (se 1 (by rfl) ⟨12715217, by rfl⟩ : syracuseStep 16953623 = 25430435) B25430435
theorem B16101787 : Blo 1488064 16101787 := bstep (se 1 (by rfl) ⟨12076340, by rfl⟩ : syracuseStep 16101787 = 24152681) B24152681
theorem B8483237 : Blo 1488064 8483237 := bstep (se 4 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 8483237 = 1590607) B1590607
theorem B5657161 : Blo 1488064 5657161 := bstep (se 2 (by rfl) ⟨2121435, by rfl⟩ : syracuseStep 5657161 = 4242871) B4242871
theorem B4240001 : Blo 1488064 4240001 := bstep (se 2 (by rfl) ⟨1590000, by rfl⟩ : syracuseStep 4240001 = 3180001) B3180001
theorem B4526779 : Blo 1488064 4526779 := bstep (se 1 (by rfl) ⟨3395084, by rfl⟩ : syracuseStep 4526779 = 6790169) B6790169
theorem B4240183 : Blo 1488064 4240183 := bstep (se 1 (by rfl) ⟨3180137, by rfl⟩ : syracuseStep 4240183 = 6360275) B6360275
theorem B7541585 : Blo 1488064 7541585 := bstep (se 2 (by rfl) ⟨2828094, by rfl⟩ : syracuseStep 7541585 = 5656189) B5656189
theorem B2233337 : Blo 1488064 2233337 := bstep (se 2 (by rfl) ⟨837501, by rfl⟩ : syracuseStep 2233337 = 1675003) B1675003
theorem B11301929 : Blo 1488064 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B9540773 : Blo 1488064 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B2233535 : Blo 1488064 2233535 := bstep (se 1 (by rfl) ⟨1675151, by rfl⟩ : syracuseStep 2233535 = 3350303) B3350303
theorem B38171897 : Blo 1488064 38171897 := bstep (se 2 (by rfl) ⟨14314461, by rfl⟩ : syracuseStep 38171897 = 28628923) B28628923
theorem B2118907 : Blo 1488064 2118907 := bstep (se 1 (by rfl) ⟨1589180, by rfl⟩ : syracuseStep 2118907 = 3178361) B3178361
theorem B1488127 : Blo 1488064 1488127 := bstep (se 1 (by rfl) ⟨1116095, by rfl⟩ : syracuseStep 1488127 = 2232191) B2232191
theorem B2233679 : Blo 1488064 2233679 := bstep (se 1 (by rfl) ⟨1675259, by rfl⟩ : syracuseStep 2233679 = 3350519) B3350519
theorem B1488255 : Blo 1488064 1488255 := bstep (se 1 (by rfl) ⟨1116191, by rfl⟩ : syracuseStep 1488255 = 2232383) B2232383
theorem B8484263 : Blo 1488064 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B2233769 : Blo 1488064 2233769 := bstep (se 2 (by rfl) ⟨837663, by rfl⟩ : syracuseStep 2233769 = 1675327) B1675327
theorem B2233823 : Blo 1488064 2233823 := bstep (se 1 (by rfl) ⟨1675367, by rfl⟩ : syracuseStep 2233823 = 3350735) B3350735
theorem B1488411 : Blo 1488064 1488411 := bstep (se 1 (by rfl) ⟨1116308, by rfl⟩ : syracuseStep 1488411 = 2232617) B2232617
theorem B2233919 : Blo 1488064 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B5027453 : Blo 1488064 5027453 := bstep (se 3 (by rfl) ⟨942647, by rfl⟩ : syracuseStep 5027453 = 1885295) B1885295
theorem B1488591 : Blo 1488064 1488591 := bstep (se 1 (by rfl) ⟨1116443, by rfl⟩ : syracuseStep 1488591 = 2232887) B2232887
theorem B4241231 : Blo 1488064 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B1488831 : Blo 1488064 1488831 := bstep (se 1 (by rfl) ⟨1116623, by rfl⟩ : syracuseStep 1488831 = 2233247) B2233247
theorem B2234399 : Blo 1488064 2234399 := bstep (se 1 (by rfl) ⟨1675799, by rfl⟩ : syracuseStep 2234399 = 3351599) B3351599
theorem B2512937 : Blo 1488064 2512937 := bstep (se 2 (by rfl) ⟨942351, by rfl⟩ : syracuseStep 2512937 = 1884703) B1884703
theorem B1488959 : Blo 1488064 1488959 := bstep (se 1 (by rfl) ⟨1116719, by rfl⟩ : syracuseStep 1488959 = 2233439) B2233439
theorem B1488999 : Blo 1488064 1488999 := bstep (se 1 (by rfl) ⟨1116749, by rfl⟩ : syracuseStep 1488999 = 2233499) B2233499
theorem B2119807 : Blo 1488064 2119807 := bstep (se 1 (by rfl) ⟨1589855, by rfl⟩ : syracuseStep 2119807 = 3179711) B3179711
theorem B7534781 : Blo 1488064 7534781 := bstep (se 3 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 7534781 = 2825543) B2825543
theorem B4241801 : Blo 1488064 4241801 := bstep (se 2 (by rfl) ⟨1590675, by rfl⟩ : syracuseStep 4241801 = 3181351) B3181351
theorem B2234831 : Blo 1488064 2234831 := bstep (se 1 (by rfl) ⟨1676123, by rfl⟩ : syracuseStep 2234831 = 3352247) B3352247
theorem B2234921 : Blo 1488064 2234921 := bstep (se 2 (by rfl) ⟨838095, by rfl⟩ : syracuseStep 2234921 = 1676191) B1676191
theorem B1489455 : Blo 1488064 1489455 := bstep (se 1 (by rfl) ⟨1117091, by rfl⟩ : syracuseStep 1489455 = 2234183) B2234183
theorem B2013751 : Blo 1488064 2013751 := bstep (se 1 (by rfl) ⟨1510313, by rfl⟩ : syracuseStep 2013751 = 3020627) B3020627
theorem B3767087 : Blo 1488064 3767087 := bstep (se 1 (by rfl) ⟨2825315, by rfl⟩ : syracuseStep 3767087 = 5650631) B5650631
theorem B4242233 : Blo 1488064 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B2513767 : Blo 1488064 2513767 := bstep (se 1 (by rfl) ⟨1885325, by rfl⟩ : syracuseStep 2513767 = 3770651) B3770651
theorem B1489855 : Blo 1488064 1489855 := bstep (se 1 (by rfl) ⟨1117391, by rfl⟩ : syracuseStep 1489855 = 2234783) B2234783
theorem B1489903 : Blo 1488064 1489903 := bstep (se 1 (by rfl) ⟨1117427, by rfl⟩ : syracuseStep 1489903 = 2234855) B2234855
theorem B2513983 : Blo 1488064 2513983 := bstep (se 1 (by rfl) ⟨1885487, by rfl⟩ : syracuseStep 2513983 = 3770975) B3770975
theorem B14302433 : Blo 1488064 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B6036713 : Blo 1488064 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B3767735 : Blo 1488064 3767735 := bstep (se 1 (by rfl) ⟨2825801, by rfl⟩ : syracuseStep 3767735 = 5651603) B5651603
theorem B48283289 : Blo 1488064 48283289 := bstep (se 2 (by rfl) ⟨18106233, by rfl⟩ : syracuseStep 48283289 = 36212467) B36212467
theorem B8478431 : Blo 1488064 8478431 := bstep (se 1 (by rfl) ⟨6358823, by rfl⟩ : syracuseStep 8478431 = 12717647) B12717647
theorem B4022399 : Blo 1488064 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B24821903 : Blo 1488064 24821903 := bstep (se 1 (by rfl) ⟨18616427, by rfl⟩ : syracuseStep 24821903 = 37232855) B37232855
theorem B2867359 : Blo 1488064 2867359 := bstep (se 1 (by rfl) ⟨2150519, by rfl⟩ : syracuseStep 2867359 = 4301039) B4301039
theorem B2826409 : Blo 1488064 2826409 := bstep (se 2 (by rfl) ⟨1059903, by rfl⟩ : syracuseStep 2826409 = 2119807) B2119807
theorem B7536887 : Blo 1488064 7536887 := bstep (se 1 (by rfl) ⟨5652665, by rfl⟩ : syracuseStep 7536887 = 11305331) B11305331
theorem B2826667 : Blo 1488064 2826667 := bstep (se 1 (by rfl) ⟨2120000, by rfl⟩ : syracuseStep 2826667 = 4240001) B4240001
theorem B12722669 : Blo 1488064 12722669 := bstep (se 3 (by rfl) ⟨2385500, by rfl⟩ : syracuseStep 12722669 = 4771001) B4771001
theorem B5653259 : Blo 1488064 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B5653577 : Blo 1488064 5653577 := bstep (se 2 (by rfl) ⟨2120091, by rfl⟩ : syracuseStep 5653577 = 4240183) B4240183
theorem B3351635 : Blo 1488064 3351635 := bstep (se 1 (by rfl) ⟨2513726, by rfl⟩ : syracuseStep 3351635 = 5027453) B5027453
theorem B3351689 : Blo 1488064 3351689 := bstep (se 2 (by rfl) ⟨1256883, by rfl⟩ : syracuseStep 3351689 = 2513767) B2513767
theorem B2827487 : Blo 1488064 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B3351977 : Blo 1488064 3351977 := bstep (se 2 (by rfl) ⟨1256991, by rfl⟩ : syracuseStep 3351977 = 2513983) B2513983
theorem B5023187 : Blo 1488064 5023187 := bstep (se 1 (by rfl) ⟨3767390, by rfl⟩ : syracuseStep 5023187 = 7534781) B7534781
theorem B3769811 : Blo 1488064 3769811 := bstep (se 1 (by rfl) ⟨2827358, by rfl⟩ : syracuseStep 3769811 = 5654717) B5654717
theorem B2827867 : Blo 1488064 2827867 := bstep (se 1 (by rfl) ⟨2120900, by rfl⟩ : syracuseStep 2827867 = 4241801) B4241801
theorem B4024475 : Blo 1488064 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B10733887 : Blo 1488064 10733887 := bstep (se 1 (by rfl) ⟨8050415, by rfl⟩ : syracuseStep 10733887 = 16100831) B16100831
theorem B32188859 : Blo 1488064 32188859 := bstep (se 1 (by rfl) ⟨24141644, by rfl⟩ : syracuseStep 32188859 = 48283289) B48283289
theorem B3820187 : Blo 1488064 3820187 := bstep (se 1 (by rfl) ⟨2865140, by rfl⟩ : syracuseStep 3820187 = 5730281) B5730281
theorem B3222281 : Blo 1488064 3222281 := bstep (se 2 (by rfl) ⟨1208355, by rfl⟩ : syracuseStep 3222281 = 2416711) B2416711
theorem B11021195 : Blo 1488064 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B5655491 : Blo 1488064 5655491 := bstep (se 1 (by rfl) ⟨4241618, by rfl⟩ : syracuseStep 5655491 = 8483237) B8483237
theorem B5025131 : Blo 1488064 5025131 := bstep (se 1 (by rfl) ⟨3768848, by rfl⟩ : syracuseStep 5025131 = 7537697) B7537697
theorem B6360515 : Blo 1488064 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B2682347 : Blo 1488064 2682347 := bstep (se 1 (by rfl) ⟨2011760, by rfl⟩ : syracuseStep 2682347 = 4023521) B4023521
theorem B25447931 : Blo 1488064 25447931 := bstep (se 1 (by rfl) ⟨19085948, by rfl⟩ : syracuseStep 25447931 = 38171897) B38171897
theorem B5656175 : Blo 1488064 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B5025725 : Blo 1488064 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B1675291 : Blo 1488064 1675291 := bstep (se 1 (by rfl) ⟨1256468, by rfl⟩ : syracuseStep 1675291 = 2512937) B2512937
theorem B5025887 : Blo 1488064 5025887 := bstep (se 1 (by rfl) ⟨3769415, by rfl⟩ : syracuseStep 5025887 = 7538831) B7538831
theorem B2511391 : Blo 1488064 2511391 := bstep (se 1 (by rfl) ⟨1883543, by rfl⟩ : syracuseStep 2511391 = 3767087) B3767087
theorem B10728125 : Blo 1488064 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B2511823 : Blo 1488064 2511823 := bstep (se 1 (by rfl) ⟨1883867, by rfl⟩ : syracuseStep 2511823 = 3767735) B3767735
theorem B5027129 : Blo 1488064 5027129 := bstep (se 2 (by rfl) ⟨1885173, by rfl⟩ : syracuseStep 5027129 = 3770347) B3770347
theorem B9942335 : Blo 1488064 9942335 := bstep (se 1 (by rfl) ⟨7456751, by rfl⟩ : syracuseStep 9942335 = 14913503) B14913503
theorem B1488199 : Blo 1488064 1488199 := bstep (se 1 (by rfl) ⟨1116149, by rfl⟩ : syracuseStep 1488199 = 2232299) B2232299
theorem B5027183 : Blo 1488064 5027183 := bstep (se 1 (by rfl) ⟨3770387, by rfl⟩ : syracuseStep 5027183 = 7540775) B7540775
theorem B54334921 : Blo 1488064 54334921 := bstep (se 2 (by rfl) ⟨20375595, by rfl⟩ : syracuseStep 54334921 = 40751191) B40751191
theorem B6034895 : Blo 1488064 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B11302415 : Blo 1488064 11302415 := bstep (se 1 (by rfl) ⟨8476811, by rfl⟩ : syracuseStep 11302415 = 16953623) B16953623
theorem B5650145 : Blo 1488064 5650145 := bstep (se 2 (by rfl) ⟨2118804, by rfl⟩ : syracuseStep 5650145 = 4237609) B4237609
theorem B2234087 : Blo 1488064 2234087 := bstep (se 1 (by rfl) ⟨1675565, by rfl⟩ : syracuseStep 2234087 = 3351131) B3351131
theorem B19085129 : Blo 1488064 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B21469049 : Blo 1488064 21469049 := bstep (se 2 (by rfl) ⟨8050893, by rfl⟩ : syracuseStep 21469049 = 16101787) B16101787
theorem B5027723 : Blo 1488064 5027723 := bstep (se 1 (by rfl) ⟨3770792, by rfl⟩ : syracuseStep 5027723 = 7541585) B7541585
theorem B5167019 : Blo 1488064 5167019 := bstep (se 1 (by rfl) ⟨3875264, by rfl⟩ : syracuseStep 5167019 = 7750529) B7750529
theorem B1488891 : Blo 1488064 1488891 := bstep (se 1 (by rfl) ⟨1116668, by rfl⟩ : syracuseStep 1488891 = 2233337) B2233337
theorem B7534619 : Blo 1488064 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B2119727 : Blo 1488064 2119727 := bstep (se 1 (by rfl) ⟨1589795, by rfl⟩ : syracuseStep 2119727 = 3179591) B3179591
theorem B2685001 : Blo 1488064 2685001 := bstep (se 2 (by rfl) ⟨1006875, by rfl⟩ : syracuseStep 2685001 = 2013751) B2013751
theorem B7542881 : Blo 1488064 7542881 := bstep (se 2 (by rfl) ⟨2828580, by rfl⟩ : syracuseStep 7542881 = 5657161) B5657161
theorem B2234471 : Blo 1488064 2234471 := bstep (se 1 (by rfl) ⟨1675853, by rfl⟩ : syracuseStep 2234471 = 3351707) B3351707
theorem B1489023 : Blo 1488064 1489023 := bstep (se 1 (by rfl) ⟨1116767, by rfl⟩ : syracuseStep 1489023 = 2233535) B2233535
theorem B1489119 : Blo 1488064 1489119 := bstep (se 1 (by rfl) ⟨1116839, by rfl⟩ : syracuseStep 1489119 = 2233679) B2233679
theorem B6035705 : Blo 1488064 6035705 := bstep (se 2 (by rfl) ⟨2263389, by rfl⟩ : syracuseStep 6035705 = 4526779) B4526779
theorem B1489179 : Blo 1488064 1489179 := bstep (se 1 (by rfl) ⟨1116884, by rfl⟩ : syracuseStep 1489179 = 2233769) B2233769
theorem B1489215 : Blo 1488064 1489215 := bstep (se 1 (by rfl) ⟨1116911, by rfl⟩ : syracuseStep 1489215 = 2233823) B2233823
theorem B1489279 : Blo 1488064 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B20388341 : Blo 1488064 20388341 := bstep (se 5 (by rfl) ⟨955703, by rfl⟩ : syracuseStep 20388341 = 1911407) B1911407
theorem B1489599 : Blo 1488064 1489599 := bstep (se 1 (by rfl) ⟨1117199, by rfl⟩ : syracuseStep 1489599 = 2234399) B2234399
theorem B12720959 : Blo 1488064 12720959 := bstep (se 1 (by rfl) ⟨9540719, by rfl⟩ : syracuseStep 12720959 = 19081439) B19081439
theorem B2513801 : Blo 1488064 2513801 := bstep (se 2 (by rfl) ⟨942675, by rfl⟩ : syracuseStep 2513801 = 1885351) B1885351
theorem B209083283 : Blo 1488064 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B3349439 : Blo 1488064 3349439 := bstep (se 1 (by rfl) ⟨2512079, by rfl⟩ : syracuseStep 3349439 = 5024159) B5024159
theorem B1489887 : Blo 1488064 1489887 := bstep (se 1 (by rfl) ⟨1117415, by rfl⟩ : syracuseStep 1489887 = 2234831) B2234831
theorem B2825209 : Blo 1488064 2825209 := bstep (se 2 (by rfl) ⟨1059453, by rfl⟩ : syracuseStep 2825209 = 2118907) B2118907
theorem B11312135 : Blo 1488064 11312135 := bstep (se 1 (by rfl) ⟨8484101, by rfl⟩ : syracuseStep 11312135 = 16968203) B16968203
theorem B1489947 : Blo 1488064 1489947 := bstep (se 1 (by rfl) ⟨1117460, by rfl⟩ : syracuseStep 1489947 = 2234921) B2234921
theorem B8477905 : Blo 1488064 8477905 := bstep (se 2 (by rfl) ⟨3179214, by rfl⟩ : syracuseStep 8477905 = 6358429) B6358429
theorem B9534955 : Blo 1488064 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B11312621 : Blo 1488064 11312621 := bstep (se 3 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 11312621 = 4242233) B4242233
theorem B2514415 : Blo 1488064 2514415 := bstep (se 1 (by rfl) ⟨1885811, by rfl⟩ : syracuseStep 2514415 = 3771623) B3771623
theorem B7249427 : Blo 1488064 7249427 := bstep (se 1 (by rfl) ⟨5437070, by rfl⟩ : syracuseStep 7249427 = 10874141) B10874141
theorem B5652287 : Blo 1488064 5652287 := bstep (se 1 (by rfl) ⟨4239215, by rfl⟩ : syracuseStep 5652287 = 8478431) B8478431
theorem B11313107 : Blo 1488064 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B3350591 : Blo 1488064 3350591 := bstep (se 1 (by rfl) ⟨2512943, by rfl⟩ : syracuseStep 3350591 = 5025887) B5025887
theorem B16547935 : Blo 1488064 16547935 := bstep (se 1 (by rfl) ⟨12410951, by rfl⟩ : syracuseStep 16547935 = 24821903) B24821903
theorem B3580001 : Blo 1488064 3580001 := bstep (se 2 (by rfl) ⟨1342500, by rfl⟩ : syracuseStep 3580001 = 2685001) B2685001
theorem B5652605 : Blo 1488064 5652605 := bstep (se 3 (by rfl) ⟨1059863, by rfl⟩ : syracuseStep 5652605 = 2119727) B2119727
theorem B3768545 : Blo 1488064 3768545 := bstep (se 2 (by rfl) ⟨1413204, by rfl⟩ : syracuseStep 3768545 = 2826409) B2826409
theorem B14311849 : Blo 1488064 14311849 := bstep (se 2 (by rfl) ⟨5366943, by rfl⟩ : syracuseStep 14311849 = 10733887) B10733887
theorem B7152083 : Blo 1488064 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B3768839 : Blo 1488064 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B3768889 : Blo 1488064 3768889 := bstep (se 2 (by rfl) ⟨1413333, by rfl⟩ : syracuseStep 3768889 = 2826667) B2826667
theorem B3769051 : Blo 1488064 3769051 := bstep (se 1 (by rfl) ⟨2826788, by rfl⟩ : syracuseStep 3769051 = 5653577) B5653577
theorem B3351419 : Blo 1488064 3351419 := bstep (se 1 (by rfl) ⟨2513564, by rfl⟩ : syracuseStep 3351419 = 5027129) B5027129
theorem B6628223 : Blo 1488064 6628223 := bstep (se 1 (by rfl) ⟨4971167, by rfl⟩ : syracuseStep 6628223 = 9942335) B9942335
theorem B3351455 : Blo 1488064 3351455 := bstep (se 1 (by rfl) ⟨2513591, by rfl⟩ : syracuseStep 3351455 = 5027183) B5027183
theorem B4023263 : Blo 1488064 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B12723419 : Blo 1488064 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B14312699 : Blo 1488064 14312699 := bstep (se 1 (by rfl) ⟨10734524, by rfl⟩ : syracuseStep 14312699 = 21469049) B21469049
theorem B3351815 : Blo 1488064 3351815 := bstep (se 1 (by rfl) ⟨2513861, by rfl⟩ : syracuseStep 3351815 = 5027723) B5027723
theorem B5023079 : Blo 1488064 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B4023803 : Blo 1488064 4023803 := bstep (se 1 (by rfl) ⟨3017852, by rfl⟩ : syracuseStep 4023803 = 6035705) B6035705
theorem B13592227 : Blo 1488064 13592227 := bstep (se 1 (by rfl) ⟨10194170, by rfl⟩ : syracuseStep 13592227 = 20388341) B20388341
theorem B2148187 : Blo 1488064 2148187 := bstep (se 1 (by rfl) ⟨1611140, by rfl⟩ : syracuseStep 2148187 = 3222281) B3222281
theorem B8480639 : Blo 1488064 8480639 := bstep (se 1 (by rfl) ⟨6360479, by rfl⟩ : syracuseStep 8480639 = 12720959) B12720959
theorem B139388855 : Blo 1488064 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B3770327 : Blo 1488064 3770327 := bstep (se 1 (by rfl) ⟨2827745, by rfl⟩ : syracuseStep 3770327 = 5655491) B5655491
theorem B3352553 : Blo 1488064 3352553 := bstep (se 2 (by rfl) ⟨1257207, by rfl⟩ : syracuseStep 3352553 = 2514415) B2514415
theorem B3770489 : Blo 1488064 3770489 := bstep (se 2 (by rfl) ⟨1413933, by rfl⟩ : syracuseStep 3770489 = 2827867) B2827867
theorem B3770783 : Blo 1488064 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B2681599 : Blo 1488064 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B5024591 : Blo 1488064 5024591 := bstep (se 1 (by rfl) ⟨3768443, by rfl⟩ : syracuseStep 5024591 = 7536887) B7536887
theorem B8481779 : Blo 1488064 8481779 := bstep (se 1 (by rfl) ⟨6361334, by rfl⟩ : syracuseStep 8481779 = 12722669) B12722669
theorem B7539965 : Blo 1488064 7539965 := bstep (se 3 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 7539965 = 2827487) B2827487
theorem B3444679 : Blo 1488064 3444679 := bstep (se 1 (by rfl) ⟨2583509, by rfl⟩ : syracuseStep 3444679 = 5167019) B5167019
theorem B2682983 : Blo 1488064 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B21459239 : Blo 1488064 21459239 := bstep (se 1 (by rfl) ⟨16094429, by rfl⟩ : syracuseStep 21459239 = 32188859) B32188859
theorem B1675867 : Blo 1488064 1675867 := bstep (se 1 (by rfl) ⟨1256900, by rfl⟩ : syracuseStep 1675867 = 2513801) B2513801
theorem B72446561 : Blo 1488064 72446561 := bstep (se 2 (by rfl) ⟨27167460, by rfl⟩ : syracuseStep 72446561 = 54334921) B54334921
theorem B2232959 : Blo 1488064 2232959 := bstep (se 1 (by rfl) ⟨1674719, by rfl⟩ : syracuseStep 2232959 = 3349439) B3349439
theorem B7541423 : Blo 1488064 7541423 := bstep (se 1 (by rfl) ⟨5656067, by rfl⟩ : syracuseStep 7541423 = 11312135) B11312135
theorem B4240343 : Blo 1488064 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B7541747 : Blo 1488064 7541747 := bstep (se 1 (by rfl) ⟨5656310, by rfl⟩ : syracuseStep 7541747 = 11312621) B11312621
theorem B29389853 : Blo 1488064 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B28611701 : Blo 1488064 28611701 := bstep (se 5 (by rfl) ⟨1341173, by rfl⟩ : syracuseStep 28611701 = 2682347) B2682347
theorem B7542071 : Blo 1488064 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B2233721 : Blo 1488064 2233721 := bstep (se 2 (by rfl) ⟨837645, by rfl⟩ : syracuseStep 2233721 = 1675291) B1675291
theorem B3823145 : Blo 1488064 3823145 := bstep (se 2 (by rfl) ⟨1433679, by rfl⟩ : syracuseStep 3823145 = 2867359) B2867359
theorem B3348521 : Blo 1488064 3348521 := bstep (se 2 (by rfl) ⟨1255695, by rfl⟩ : syracuseStep 3348521 = 2511391) B2511391
theorem B2234423 : Blo 1488064 2234423 := bstep (se 1 (by rfl) ⟨1675817, by rfl⟩ : syracuseStep 2234423 = 3351635) B3351635
theorem B2234459 : Blo 1488064 2234459 := bstep (se 1 (by rfl) ⟨1675844, by rfl⟩ : syracuseStep 2234459 = 3351689) B3351689
theorem B2234651 : Blo 1488064 2234651 := bstep (se 1 (by rfl) ⟨1675988, by rfl⟩ : syracuseStep 2234651 = 3351977) B3351977
theorem B3348791 : Blo 1488064 3348791 := bstep (se 1 (by rfl) ⟨2511593, by rfl⟩ : syracuseStep 3348791 = 5023187) B5023187
theorem B2513207 : Blo 1488064 2513207 := bstep (se 1 (by rfl) ⟨1884905, by rfl⟩ : syracuseStep 2513207 = 3769811) B3769811
theorem B7534943 : Blo 1488064 7534943 := bstep (se 1 (by rfl) ⟨5651207, by rfl⟩ : syracuseStep 7534943 = 11302415) B11302415
theorem B3766763 : Blo 1488064 3766763 := bstep (se 1 (by rfl) ⟨2825072, by rfl⟩ : syracuseStep 3766763 = 5650145) B5650145
theorem B1489391 : Blo 1488064 1489391 := bstep (se 1 (by rfl) ⟨1117043, by rfl⟩ : syracuseStep 1489391 = 2234087) B2234087
theorem B3349097 : Blo 1488064 3349097 := bstep (se 2 (by rfl) ⟨1255911, by rfl⟩ : syracuseStep 3349097 = 2511823) B2511823
theorem B3766945 : Blo 1488064 3766945 := bstep (se 2 (by rfl) ⟨1412604, by rfl⟩ : syracuseStep 3766945 = 2825209) B2825209
theorem B5028587 : Blo 1488064 5028587 := bstep (se 1 (by rfl) ⟨3771440, by rfl⟩ : syracuseStep 5028587 = 7542881) B7542881
theorem B1489647 : Blo 1488064 1489647 := bstep (se 1 (by rfl) ⟨1117235, by rfl⟩ : syracuseStep 1489647 = 2234471) B2234471
theorem B11303873 : Blo 1488064 11303873 := bstep (se 2 (by rfl) ⟨4238952, by rfl⟩ : syracuseStep 11303873 = 8477905) B8477905
theorem B2546791 : Blo 1488064 2546791 := bstep (se 1 (by rfl) ⟨1910093, by rfl⟩ : syracuseStep 2546791 = 3820187) B3820187
theorem B12713273 : Blo 1488064 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B3350087 : Blo 1488064 3350087 := bstep (se 1 (by rfl) ⟨2512565, by rfl⟩ : syracuseStep 3350087 = 5025131) B5025131
theorem B16965287 : Blo 1488064 16965287 := bstep (se 1 (by rfl) ⟨12723965, by rfl⟩ : syracuseStep 16965287 = 25447931) B25447931
theorem B4832951 : Blo 1488064 4832951 := bstep (se 1 (by rfl) ⟨3624713, by rfl⟩ : syracuseStep 4832951 = 7249427) B7249427
theorem B3768191 : Blo 1488064 3768191 := bstep (se 1 (by rfl) ⟨2826143, by rfl⟩ : syracuseStep 3768191 = 5652287) B5652287
theorem B3350483 : Blo 1488064 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B3768403 : Blo 1488064 3768403 := bstep (se 1 (by rfl) ⟨2826302, by rfl⟩ : syracuseStep 3768403 = 5652605) B5652605
theorem B4768055 : Blo 1488064 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B13582885 : Blo 1488064 13582885 := bstep (se 4 (by rfl) ⟨1273395, by rfl⟩ : syracuseStep 13582885 = 2546791) B2546791
theorem B2826895 : Blo 1488064 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B5022593 : Blo 1488064 5022593 := bstep (se 2 (by rfl) ⟨1883472, by rfl⟩ : syracuseStep 5022593 = 3766945) B3766945
theorem B2548763 : Blo 1488064 2548763 := bstep (se 1 (by rfl) ⟨1911572, by rfl⟩ : syracuseStep 2548763 = 3823145) B3823145
theorem B5653759 : Blo 1488064 5653759 := bstep (se 1 (by rfl) ⟨4240319, by rfl⟩ : syracuseStep 5653759 = 8480639) B8480639
theorem B5023295 : Blo 1488064 5023295 := bstep (se 1 (by rfl) ⟨3767471, by rfl⟩ : syracuseStep 5023295 = 7534943) B7534943
theorem B12887869 : Blo 1488064 12887869 := bstep (se 3 (by rfl) ⟨2416475, by rfl⟩ : syracuseStep 12887869 = 4832951) B4832951
theorem B3352391 : Blo 1488064 3352391 := bstep (se 1 (by rfl) ⟨2514293, by rfl⟩ : syracuseStep 3352391 = 5028587) B5028587
theorem B5654519 : Blo 1488064 5654519 := bstep (se 1 (by rfl) ⟨4240889, by rfl⟩ : syracuseStep 5654519 = 8481779) B8481779
theorem B18122969 : Blo 1488064 18122969 := bstep (se 2 (by rfl) ⟨6796113, by rfl⟩ : syracuseStep 18122969 = 13592227) B13592227
theorem B2386667 : Blo 1488064 2386667 := bstep (se 1 (by rfl) ⟨1790000, by rfl⟩ : syracuseStep 2386667 = 3580001) B3580001
theorem B1788655 : Blo 1488064 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B22063913 : Blo 1488064 22063913 := bstep (se 2 (by rfl) ⟨8273967, by rfl⟩ : syracuseStep 22063913 = 16547935) B16547935
theorem B14306159 : Blo 1488064 14306159 := bstep (se 1 (by rfl) ⟨10729619, by rfl⟩ : syracuseStep 14306159 = 21459239) B21459239
theorem B19082465 : Blo 1488064 19082465 := bstep (se 2 (by rfl) ⟨7155924, by rfl⟩ : syracuseStep 19082465 = 14311849) B14311849
theorem B4418815 : Blo 1488064 4418815 := bstep (se 1 (by rfl) ⟨3314111, by rfl⟩ : syracuseStep 4418815 = 6628223) B6628223
theorem B2682175 : Blo 1488064 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B5025185 : Blo 1488064 5025185 := bstep (se 2 (by rfl) ⟨1884444, by rfl⟩ : syracuseStep 5025185 = 3768889) B3768889
theorem B19074467 : Blo 1488064 19074467 := bstep (se 1 (by rfl) ⟨14305850, by rfl⟩ : syracuseStep 19074467 = 28611701) B28611701
theorem B8482279 : Blo 1488064 8482279 := bstep (se 1 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 8482279 = 12723419) B12723419
theorem B5025401 : Blo 1488064 5025401 := bstep (se 2 (by rfl) ⟨1884525, by rfl⟩ : syracuseStep 5025401 = 3769051) B3769051
theorem B3575465 : Blo 1488064 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B2232347 : Blo 1488064 2232347 := bstep (se 1 (by rfl) ⟨1674260, by rfl⟩ : syracuseStep 2232347 = 3348521) B3348521
theorem B2232527 : Blo 1488064 2232527 := bstep (se 1 (by rfl) ⟨1674395, by rfl⟩ : syracuseStep 2232527 = 3348791) B3348791
theorem B1675471 : Blo 1488064 1675471 := bstep (se 1 (by rfl) ⟨1256603, by rfl⟩ : syracuseStep 1675471 = 2513207) B2513207
theorem B2511175 : Blo 1488064 2511175 := bstep (se 1 (by rfl) ⟨1883381, by rfl⟩ : syracuseStep 2511175 = 3766763) B3766763
theorem B2232731 : Blo 1488064 2232731 := bstep (se 1 (by rfl) ⟨1674548, by rfl⟩ : syracuseStep 2232731 = 3349097) B3349097
theorem B5026643 : Blo 1488064 5026643 := bstep (se 1 (by rfl) ⟨3769982, by rfl⟩ : syracuseStep 5026643 = 7539965) B7539965
theorem B8475515 : Blo 1488064 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B2233391 : Blo 1488064 2233391 := bstep (se 1 (by rfl) ⟨1675043, by rfl⟩ : syracuseStep 2233391 = 3350087) B3350087
theorem B11310191 : Blo 1488064 11310191 := bstep (se 1 (by rfl) ⟨8482643, by rfl⟩ : syracuseStep 11310191 = 16965287) B16965287
theorem B2864249 : Blo 1488064 2864249 := bstep (se 2 (by rfl) ⟨1074093, by rfl⟩ : syracuseStep 2864249 = 2148187) B2148187
theorem B2512127 : Blo 1488064 2512127 := bstep (se 1 (by rfl) ⟨1884095, by rfl⟩ : syracuseStep 2512127 = 3768191) B3768191
theorem B4592905 : Blo 1488064 4592905 := bstep (se 2 (by rfl) ⟨1722339, by rfl⟩ : syracuseStep 4592905 = 3444679) B3444679
theorem B2233655 : Blo 1488064 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B2233727 : Blo 1488064 2233727 := bstep (se 1 (by rfl) ⟨1675295, by rfl⟩ : syracuseStep 2233727 = 3350591) B3350591
theorem B2512363 : Blo 1488064 2512363 := bstep (se 1 (by rfl) ⟨1884272, by rfl⟩ : syracuseStep 2512363 = 3768545) B3768545
theorem B2512559 : Blo 1488064 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B48297707 : Blo 1488064 48297707 := bstep (se 1 (by rfl) ⟨36223280, by rfl⟩ : syracuseStep 48297707 = 72446561) B72446561
theorem B1488639 : Blo 1488064 1488639 := bstep (se 1 (by rfl) ⟨1116479, by rfl⟩ : syracuseStep 1488639 = 2232959) B2232959
theorem B5027615 : Blo 1488064 5027615 := bstep (se 1 (by rfl) ⟨3770711, by rfl⟩ : syracuseStep 5027615 = 7541423) B7541423
theorem B2234279 : Blo 1488064 2234279 := bstep (se 1 (by rfl) ⟨1675709, by rfl⟩ : syracuseStep 2234279 = 3351419) B3351419
theorem B2234303 : Blo 1488064 2234303 := bstep (se 1 (by rfl) ⟨1675727, by rfl⟩ : syracuseStep 2234303 = 3351455) B3351455
theorem B5027831 : Blo 1488064 5027831 := bstep (se 1 (by rfl) ⟨3770873, by rfl⟩ : syracuseStep 5027831 = 7541747) B7541747
theorem B19593235 : Blo 1488064 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B2234489 : Blo 1488064 2234489 := bstep (se 2 (by rfl) ⟨837933, by rfl⟩ : syracuseStep 2234489 = 1675867) B1675867
theorem B9541799 : Blo 1488064 9541799 := bstep (se 1 (by rfl) ⟨7156349, by rfl⟩ : syracuseStep 9541799 = 14312699) B14312699
theorem B2234543 : Blo 1488064 2234543 := bstep (se 1 (by rfl) ⟨1675907, by rfl⟩ : syracuseStep 2234543 = 3351815) B3351815
theorem B5028047 : Blo 1488064 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B3348719 : Blo 1488064 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B1489147 : Blo 1488064 1489147 := bstep (se 1 (by rfl) ⟨1116860, by rfl⟩ : syracuseStep 1489147 = 2233721) B2233721
theorem B2513551 : Blo 1488064 2513551 := bstep (se 1 (by rfl) ⟨1885163, by rfl⟩ : syracuseStep 2513551 = 3770327) B3770327
theorem B2235035 : Blo 1488064 2235035 := bstep (se 1 (by rfl) ⟨1676276, by rfl⟩ : syracuseStep 2235035 = 3352553) B3352553
theorem B10730141 : Blo 1488064 10730141 := bstep (se 3 (by rfl) ⟨2011901, by rfl⟩ : syracuseStep 10730141 = 4023803) B4023803
theorem B1489615 : Blo 1488064 1489615 := bstep (se 1 (by rfl) ⟨1117211, by rfl⟩ : syracuseStep 1489615 = 2234423) B2234423
theorem B1489639 : Blo 1488064 1489639 := bstep (se 1 (by rfl) ⟨1117229, by rfl⟩ : syracuseStep 1489639 = 2234459) B2234459
theorem B2513659 : Blo 1488064 2513659 := bstep (se 1 (by rfl) ⟨1885244, by rfl⟩ : syracuseStep 2513659 = 3770489) B3770489
theorem B1489767 : Blo 1488064 1489767 := bstep (se 1 (by rfl) ⟨1117325, by rfl⟩ : syracuseStep 1489767 = 2234651) B2234651
theorem B2513855 : Blo 1488064 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B3349727 : Blo 1488064 3349727 := bstep (se 1 (by rfl) ⟨2512295, by rfl⟩ : syracuseStep 3349727 = 5024591) B5024591
theorem B7535915 : Blo 1488064 7535915 := bstep (se 1 (by rfl) ⟨5651936, by rfl⟩ : syracuseStep 7535915 = 11303873) B11303873
theorem B371703613 : Blo 1488064 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B104497253 : Blo 1488064 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B3178703 : Blo 1488064 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B3351095 : Blo 1488064 3351095 := bstep (se 1 (by rfl) ⟨2513321, by rfl⟩ : syracuseStep 3351095 = 5026643) B5026643
theorem B1909499 : Blo 1488064 1909499 := bstep (se 1 (by rfl) ⟨1432124, by rfl⟩ : syracuseStep 1909499 = 2864249) B2864249
theorem B3769193 : Blo 1488064 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B3351401 : Blo 1488064 3351401 := bstep (se 2 (by rfl) ⟨1256775, by rfl⟩ : syracuseStep 3351401 = 2513551) B2513551
theorem B2384873 : Blo 1488064 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B3351545 : Blo 1488064 3351545 := bstep (se 2 (by rfl) ⟨1256829, by rfl⟩ : syracuseStep 3351545 = 2513659) B2513659
theorem B3351743 : Blo 1488064 3351743 := bstep (se 1 (by rfl) ⟨2513807, by rfl⟩ : syracuseStep 3351743 = 5027615) B5027615
theorem B3769679 : Blo 1488064 3769679 := bstep (se 1 (by rfl) ⟨2827259, by rfl⟩ : syracuseStep 3769679 = 5654519) B5654519
theorem B3351887 : Blo 1488064 3351887 := bstep (se 1 (by rfl) ⟨2513915, by rfl⟩ : syracuseStep 3351887 = 5027831) B5027831
theorem B3352031 : Blo 1488064 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B7538345 : Blo 1488064 7538345 := bstep (se 2 (by rfl) ⟨2826879, by rfl⟩ : syracuseStep 7538345 = 5653759) B5653759
theorem B5891753 : Blo 1488064 5891753 := bstep (se 2 (by rfl) ⟨2209407, by rfl⟩ : syracuseStep 5891753 = 4418815) B4418815
theorem B7153427 : Blo 1488064 7153427 := bstep (se 1 (by rfl) ⟨5365070, by rfl⟩ : syracuseStep 7153427 = 10730141) B10730141
theorem B1591111 : Blo 1488064 1591111 := bstep (se 1 (by rfl) ⟨1193333, by rfl⟩ : syracuseStep 1591111 = 2386667) B2386667
theorem B9537439 : Blo 1488064 9537439 := bstep (se 1 (by rfl) ⟨7153079, by rfl⟩ : syracuseStep 9537439 = 14306159) B14306159
theorem B5023943 : Blo 1488064 5023943 := bstep (se 1 (by rfl) ⟨3767957, by rfl⟩ : syracuseStep 5023943 = 7535915) B7535915
theorem B12716311 : Blo 1488064 12716311 := bstep (se 1 (by rfl) ⟨9537233, by rfl⟩ : syracuseStep 12716311 = 19074467) B19074467
theorem B5024537 : Blo 1488064 5024537 := bstep (se 2 (by rfl) ⟨1884201, by rfl⟩ : syracuseStep 5024537 = 3768403) B3768403
theorem B1699175 : Blo 1488064 1699175 := bstep (se 1 (by rfl) ⟨1274381, by rfl⟩ : syracuseStep 1699175 = 2548763) B2548763
theorem B7540127 : Blo 1488064 7540127 := bstep (se 1 (by rfl) ⟨5655095, by rfl⟩ : syracuseStep 7540127 = 11310191) B11310191
theorem B1674751 : Blo 1488064 1674751 := bstep (se 1 (by rfl) ⟨1256063, by rfl⟩ : syracuseStep 1674751 = 2512127) B2512127
theorem B1675039 : Blo 1488064 1675039 := bstep (se 1 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 1675039 = 2512559) B2512559
theorem B32198471 : Blo 1488064 32198471 := bstep (se 1 (by rfl) ⟨24148853, by rfl⟩ : syracuseStep 32198471 = 48297707) B48297707
theorem B6361199 : Blo 1488064 6361199 := bstep (se 1 (by rfl) ⟨4770899, by rfl⟩ : syracuseStep 6361199 = 9541799) B9541799
theorem B2232479 : Blo 1488064 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B3576233 : Blo 1488064 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B14709275 : Blo 1488064 14709275 := bstep (se 1 (by rfl) ⟨11031956, by rfl⟩ : syracuseStep 14709275 = 22063913) B22063913
theorem B1675903 : Blo 1488064 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B11309705 : Blo 1488064 11309705 := bstep (se 2 (by rfl) ⟨4241139, by rfl⟩ : syracuseStep 11309705 = 8482279) B8482279
theorem B2233151 : Blo 1488064 2233151 := bstep (se 1 (by rfl) ⟨1674863, by rfl⟩ : syracuseStep 2233151 = 3349727) B3349727
theorem B17183825 : Blo 1488064 17183825 := bstep (se 2 (by rfl) ⟨6443934, by rfl⟩ : syracuseStep 17183825 = 12887869) B12887869
theorem B495604817 : Blo 1488064 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B1488231 : Blo 1488064 1488231 := bstep (se 1 (by rfl) ⟨1116173, by rfl⟩ : syracuseStep 1488231 = 2232347) B2232347
theorem B1488351 : Blo 1488064 1488351 := bstep (se 1 (by rfl) ⟨1116263, by rfl⟩ : syracuseStep 1488351 = 2232527) B2232527
theorem B97981973 : Blo 1488064 97981973 := bstep (se 6 (by rfl) ⟨2296452, by rfl⟩ : syracuseStep 97981973 = 4592905) B4592905
theorem B1488487 : Blo 1488064 1488487 := bstep (se 1 (by rfl) ⟨1116365, by rfl⟩ : syracuseStep 1488487 = 2232731) B2232731
theorem B2233961 : Blo 1488064 2233961 := bstep (se 2 (by rfl) ⟨837735, by rfl⟩ : syracuseStep 2233961 = 1675471) B1675471
theorem B3348233 : Blo 1488064 3348233 := bstep (se 2 (by rfl) ⟨1255587, by rfl⟩ : syracuseStep 3348233 = 2511175) B2511175
theorem B5650343 : Blo 1488064 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B3348395 : Blo 1488064 3348395 := bstep (se 1 (by rfl) ⟨2511296, by rfl⟩ : syracuseStep 3348395 = 5022593) B5022593
theorem B1488927 : Blo 1488064 1488927 := bstep (se 1 (by rfl) ⟨1116695, by rfl⟩ : syracuseStep 1488927 = 2233391) B2233391
theorem B18110513 : Blo 1488064 18110513 := bstep (se 2 (by rfl) ⟨6791442, by rfl⟩ : syracuseStep 18110513 = 13582885) B13582885
theorem B1489103 : Blo 1488064 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B1489151 : Blo 1488064 1489151 := bstep (se 1 (by rfl) ⟨1116863, by rfl⟩ : syracuseStep 1489151 = 2233727) B2233727
theorem B3348863 : Blo 1488064 3348863 := bstep (se 1 (by rfl) ⟨2511647, by rfl⟩ : syracuseStep 3348863 = 5023295) B5023295
theorem B2234927 : Blo 1488064 2234927 := bstep (se 1 (by rfl) ⟨1676195, by rfl⟩ : syracuseStep 2234927 = 3352391) B3352391
theorem B1489519 : Blo 1488064 1489519 := bstep (se 1 (by rfl) ⟨1117139, by rfl⟩ : syracuseStep 1489519 = 2234279) B2234279
theorem B1489535 : Blo 1488064 1489535 := bstep (se 1 (by rfl) ⟨1117151, by rfl⟩ : syracuseStep 1489535 = 2234303) B2234303
theorem B1489659 : Blo 1488064 1489659 := bstep (se 1 (by rfl) ⟨1117244, by rfl⟩ : syracuseStep 1489659 = 2234489) B2234489
theorem B1489695 : Blo 1488064 1489695 := bstep (se 1 (by rfl) ⟨1117271, by rfl⟩ : syracuseStep 1489695 = 2234543) B2234543
theorem B12081979 : Blo 1488064 12081979 := bstep (se 1 (by rfl) ⟨9061484, by rfl⟩ : syracuseStep 12081979 = 18122969) B18122969
theorem B1490023 : Blo 1488064 1490023 := bstep (se 1 (by rfl) ⟨1117517, by rfl⟩ : syracuseStep 1490023 = 2235035) B2235035
theorem B3349817 : Blo 1488064 3349817 := bstep (se 2 (by rfl) ⟨1256181, by rfl⟩ : syracuseStep 3349817 = 2512363) B2512363
theorem B12721643 : Blo 1488064 12721643 := bstep (se 1 (by rfl) ⟨9541232, by rfl⟩ : syracuseStep 12721643 = 19082465) B19082465
theorem B3350123 : Blo 1488064 3350123 := bstep (se 1 (by rfl) ⟨2512592, by rfl⟩ : syracuseStep 3350123 = 5025185) B5025185
theorem B3350267 : Blo 1488064 3350267 := bstep (se 1 (by rfl) ⟨2512700, by rfl⟩ : syracuseStep 3350267 = 5025401) B5025401
theorem B2383643 : Blo 1488064 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B69664835 : Blo 1488064 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B2384155 : Blo 1488064 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B9806183 : Blo 1488064 9806183 := bstep (se 1 (by rfl) ⟨7354637, by rfl⟩ : syracuseStep 9806183 = 14709275) B14709275
theorem B1589915 : Blo 1488064 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B4531133 : Blo 1488064 4531133 := bstep (se 3 (by rfl) ⟨849587, by rfl⟩ : syracuseStep 4531133 = 1699175) B1699175
theorem B4768951 : Blo 1488064 4768951 := bstep (se 1 (by rfl) ⟨3576713, by rfl⟩ : syracuseStep 4768951 = 7153427) B7153427
theorem B8481095 : Blo 1488064 8481095 := bstep (se 1 (by rfl) ⟨6360821, by rfl⟩ : syracuseStep 8481095 = 12721643) B12721643
theorem B12716585 : Blo 1488064 12716585 := bstep (se 2 (by rfl) ⟨4768719, by rfl⟩ : syracuseStep 12716585 = 9537439) B9537439
theorem B21465647 : Blo 1488064 21465647 := bstep (se 1 (by rfl) ⟨16099235, by rfl⟩ : syracuseStep 21465647 = 32198471) B32198471
theorem B48294701 : Blo 1488064 48294701 := bstep (se 3 (by rfl) ⟨9055256, by rfl⟩ : syracuseStep 48294701 = 18110513) B18110513
theorem B7539803 : Blo 1488064 7539803 := bstep (se 1 (by rfl) ⟨5654852, by rfl⟩ : syracuseStep 7539803 = 11309705) B11309705
theorem B11455883 : Blo 1488064 11455883 := bstep (se 1 (by rfl) ⟨8591912, by rfl⟩ : syracuseStep 11455883 = 17183825) B17183825
theorem B330403211 : Blo 1488064 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B5025563 : Blo 1488064 5025563 := bstep (se 1 (by rfl) ⟨3769172, by rfl⟩ : syracuseStep 5025563 = 7538345) B7538345
theorem B3927835 : Blo 1488064 3927835 := bstep (se 1 (by rfl) ⟨2945876, by rfl⟩ : syracuseStep 3927835 = 5891753) B5891753
theorem B2232155 : Blo 1488064 2232155 := bstep (se 1 (by rfl) ⟨1674116, by rfl⟩ : syracuseStep 2232155 = 3348233) B3348233
theorem B2232263 : Blo 1488064 2232263 := bstep (se 1 (by rfl) ⟨1674197, by rfl⟩ : syracuseStep 2232263 = 3348395) B3348395
theorem B2232575 : Blo 1488064 2232575 := bstep (se 1 (by rfl) ⟨1674431, by rfl⟩ : syracuseStep 2232575 = 3348863) B3348863
theorem B5091997 : Blo 1488064 5091997 := bstep (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) B1909499
theorem B2233001 : Blo 1488064 2233001 := bstep (se 2 (by rfl) ⟨837375, by rfl⟩ : syracuseStep 2233001 = 1674751) B1674751
theorem B2233211 : Blo 1488064 2233211 := bstep (se 1 (by rfl) ⟨1674908, by rfl⟩ : syracuseStep 2233211 = 3349817) B3349817
theorem B5026751 : Blo 1488064 5026751 := bstep (se 1 (by rfl) ⟨3770063, by rfl⟩ : syracuseStep 5026751 = 7540127) B7540127
theorem B2233385 : Blo 1488064 2233385 := bstep (se 2 (by rfl) ⟨837519, by rfl⟩ : syracuseStep 2233385 = 1675039) B1675039
theorem B2233415 : Blo 1488064 2233415 := bstep (se 1 (by rfl) ⟨1675061, by rfl⟩ : syracuseStep 2233415 = 3350123) B3350123
theorem B2233511 : Blo 1488064 2233511 := bstep (se 1 (by rfl) ⟨1675133, by rfl⟩ : syracuseStep 2233511 = 3350267) B3350267
theorem B4240799 : Blo 1488064 4240799 := bstep (se 1 (by rfl) ⟨3180599, by rfl⟩ : syracuseStep 4240799 = 6361199) B6361199
theorem B1488319 : Blo 1488064 1488319 := bstep (se 1 (by rfl) ⟨1116239, by rfl⟩ : syracuseStep 1488319 = 2232479) B2232479
theorem B2119135 : Blo 1488064 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B16955081 : Blo 1488064 16955081 := bstep (se 2 (by rfl) ⟨6358155, by rfl⟩ : syracuseStep 16955081 = 12716311) B12716311
theorem B2234063 : Blo 1488064 2234063 := bstep (se 1 (by rfl) ⟨1675547, by rfl⟩ : syracuseStep 2234063 = 3351095) B3351095
theorem B1488767 : Blo 1488064 1488767 := bstep (se 1 (by rfl) ⟨1116575, by rfl⟩ : syracuseStep 1488767 = 2233151) B2233151
theorem B2512795 : Blo 1488064 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B2234267 : Blo 1488064 2234267 := bstep (se 1 (by rfl) ⟨1675700, by rfl⟩ : syracuseStep 2234267 = 3351401) B3351401
theorem B2234363 : Blo 1488064 2234363 := bstep (se 1 (by rfl) ⟨1675772, by rfl⟩ : syracuseStep 2234363 = 3351545) B3351545
theorem B2234495 : Blo 1488064 2234495 := bstep (se 1 (by rfl) ⟨1675871, by rfl⟩ : syracuseStep 2234495 = 3351743) B3351743
theorem B2234537 : Blo 1488064 2234537 := bstep (se 2 (by rfl) ⟨837951, by rfl⟩ : syracuseStep 2234537 = 1675903) B1675903
theorem B2513119 : Blo 1488064 2513119 := bstep (se 1 (by rfl) ⟨1884839, by rfl⟩ : syracuseStep 2513119 = 3769679) B3769679
theorem B2234591 : Blo 1488064 2234591 := bstep (se 1 (by rfl) ⟨1675943, by rfl⟩ : syracuseStep 2234591 = 3351887) B3351887
theorem B2234687 : Blo 1488064 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B65321315 : Blo 1488064 65321315 := bstep (se 1 (by rfl) ⟨48990986, by rfl⟩ : syracuseStep 65321315 = 97981973) B97981973
theorem B1489307 : Blo 1488064 1489307 := bstep (se 1 (by rfl) ⟨1116980, by rfl⟩ : syracuseStep 1489307 = 2233961) B2233961
theorem B3766895 : Blo 1488064 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B3349295 : Blo 1488064 3349295 := bstep (se 1 (by rfl) ⟨2511971, by rfl⟩ : syracuseStep 3349295 = 5023943) B5023943
theorem B64437221 : Blo 1488064 64437221 := bstep (se 4 (by rfl) ⟨6040989, by rfl⟩ : syracuseStep 64437221 = 12081979) B12081979
theorem B1489951 : Blo 1488064 1489951 := bstep (se 1 (by rfl) ⟨1117463, by rfl⟩ : syracuseStep 1489951 = 2234927) B2234927
theorem B3349691 : Blo 1488064 3349691 := bstep (se 1 (by rfl) ⟨2512268, by rfl⟩ : syracuseStep 3349691 = 5024537) B5024537
theorem B2121481 : Blo 1488064 2121481 := bstep (se 2 (by rfl) ⟨795555, by rfl⟩ : syracuseStep 2121481 = 1591111) B1591111
theorem B1589095 : Blo 1488064 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B6537455 : Blo 1488064 6537455 := bstep (se 1 (by rfl) ⟨4903091, by rfl⟩ : syracuseStep 6537455 = 9806183) B9806183
theorem B3350825 : Blo 1488064 3350825 := bstep (se 2 (by rfl) ⟨1256559, by rfl⟩ : syracuseStep 3350825 = 2513119) B2513119
theorem B3178873 : Blo 1488064 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B3351167 : Blo 1488064 3351167 := bstep (se 1 (by rfl) ⟨2513375, by rfl⟩ : syracuseStep 3351167 = 5026751) B5026751
theorem B2827199 : Blo 1488064 2827199 := bstep (se 1 (by rfl) ⟨2120399, by rfl⟩ : syracuseStep 2827199 = 4240799) B4240799
theorem B11314565 : Blo 1488064 11314565 := bstep (se 4 (by rfl) ⟨1060740, by rfl⟩ : syracuseStep 11314565 = 2121481) B2121481
theorem B20948453 : Blo 1488064 20948453 := bstep (se 4 (by rfl) ⟨1963917, by rfl⟩ : syracuseStep 20948453 = 3927835) B3927835
theorem B5654063 : Blo 1488064 5654063 := bstep (se 1 (by rfl) ⟨4240547, by rfl⟩ : syracuseStep 5654063 = 8481095) B8481095
theorem B6358601 : Blo 1488064 6358601 := bstep (se 2 (by rfl) ⟨2384475, by rfl⟩ : syracuseStep 6358601 = 4768951) B4768951
theorem B32196467 : Blo 1488064 32196467 := bstep (se 1 (by rfl) ⟨24147350, by rfl⟩ : syracuseStep 32196467 = 48294701) B48294701
theorem B7637255 : Blo 1488064 7637255 := bstep (se 1 (by rfl) ⟨5727941, by rfl⟩ : syracuseStep 7637255 = 11455883) B11455883
theorem B220268807 : Blo 1488064 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B46443223 : Blo 1488064 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B4239773 : Blo 1488064 4239773 := bstep (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) B1589915
theorem B2511263 : Blo 1488064 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B2232863 : Blo 1488064 2232863 := bstep (se 1 (by rfl) ⟨1674647, by rfl⟩ : syracuseStep 2232863 = 3349295) B3349295
theorem B5026535 : Blo 1488064 5026535 := bstep (se 1 (by rfl) ⟨3769901, by rfl⟩ : syracuseStep 5026535 = 7539803) B7539803
theorem B2233127 : Blo 1488064 2233127 := bstep (se 1 (by rfl) ⟨1674845, by rfl⟩ : syracuseStep 2233127 = 3349691) B3349691
theorem B2118793 : Blo 1488064 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B1488103 : Blo 1488064 1488103 := bstep (se 1 (by rfl) ⟨1116077, by rfl⟩ : syracuseStep 1488103 = 2232155) B2232155
theorem B1488175 : Blo 1488064 1488175 := bstep (se 1 (by rfl) ⟨1116131, by rfl⟩ : syracuseStep 1488175 = 2232263) B2232263
theorem B1488383 : Blo 1488064 1488383 := bstep (se 1 (by rfl) ⟨1116287, by rfl⟩ : syracuseStep 1488383 = 2232575) B2232575
theorem B1488667 : Blo 1488064 1488667 := bstep (se 1 (by rfl) ⟨1116500, by rfl⟩ : syracuseStep 1488667 = 2233001) B2233001
theorem B1488807 : Blo 1488064 1488807 := bstep (se 1 (by rfl) ⟨1116605, by rfl⟩ : syracuseStep 1488807 = 2233211) B2233211
theorem B3020755 : Blo 1488064 3020755 := bstep (se 1 (by rfl) ⟨2265566, by rfl⟩ : syracuseStep 3020755 = 4531133) B4531133
theorem B1488923 : Blo 1488064 1488923 := bstep (se 1 (by rfl) ⟨1116692, by rfl⟩ : syracuseStep 1488923 = 2233385) B2233385
theorem B1488943 : Blo 1488064 1488943 := bstep (se 1 (by rfl) ⟨1116707, by rfl⟩ : syracuseStep 1488943 = 2233415) B2233415
theorem B1489007 : Blo 1488064 1489007 := bstep (se 1 (by rfl) ⟨1116755, by rfl⟩ : syracuseStep 1489007 = 2233511) B2233511
theorem B6789329 : Blo 1488064 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B11303387 : Blo 1488064 11303387 := bstep (se 1 (by rfl) ⟨8477540, by rfl⟩ : syracuseStep 11303387 = 16955081) B16955081
theorem B1489375 : Blo 1488064 1489375 := bstep (se 1 (by rfl) ⟨1117031, by rfl⟩ : syracuseStep 1489375 = 2234063) B2234063
theorem B1489511 : Blo 1488064 1489511 := bstep (se 1 (by rfl) ⟨1117133, by rfl⟩ : syracuseStep 1489511 = 2234267) B2234267
theorem B1489575 : Blo 1488064 1489575 := bstep (se 1 (by rfl) ⟨1117181, by rfl⟩ : syracuseStep 1489575 = 2234363) B2234363
theorem B1489663 : Blo 1488064 1489663 := bstep (se 1 (by rfl) ⟨1117247, by rfl⟩ : syracuseStep 1489663 = 2234495) B2234495
theorem B1489691 : Blo 1488064 1489691 := bstep (se 1 (by rfl) ⟨1117268, by rfl⟩ : syracuseStep 1489691 = 2234537) B2234537
theorem B1489727 : Blo 1488064 1489727 := bstep (se 1 (by rfl) ⟨1117295, by rfl⟩ : syracuseStep 1489727 = 2234591) B2234591
theorem B1489791 : Blo 1488064 1489791 := bstep (se 1 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 1489791 = 2234687) B2234687
theorem B43547543 : Blo 1488064 43547543 := bstep (se 1 (by rfl) ⟨32660657, by rfl⟩ : syracuseStep 43547543 = 65321315) B65321315
theorem B8477723 : Blo 1488064 8477723 := bstep (se 1 (by rfl) ⟨6358292, by rfl⟩ : syracuseStep 8477723 = 12716585) B12716585
theorem B14310431 : Blo 1488064 14310431 := bstep (se 1 (by rfl) ⟨10732823, by rfl⟩ : syracuseStep 14310431 = 21465647) B21465647
theorem B2825513 : Blo 1488064 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B42958147 : Blo 1488064 42958147 := bstep (se 1 (by rfl) ⟨32218610, by rfl⟩ : syracuseStep 42958147 = 64437221) B64437221
theorem B3350375 : Blo 1488064 3350375 := bstep (se 1 (by rfl) ⟨2512781, by rfl⟩ : syracuseStep 3350375 = 5025563) B5025563
theorem B3350393 : Blo 1488064 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B4358303 : Blo 1488064 4358303 := bstep (se 1 (by rfl) ⟨3268727, by rfl⟩ : syracuseStep 4358303 = 6537455) B6537455
theorem B2826515 : Blo 1488064 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B3351023 : Blo 1488064 3351023 := bstep (se 1 (by rfl) ⟨2513267, by rfl⟩ : syracuseStep 3351023 = 5026535) B5026535
theorem B1884799 : Blo 1488064 1884799 := bstep (se 1 (by rfl) ⟨1413599, by rfl⟩ : syracuseStep 1884799 = 2827199) B2827199
theorem B61924297 : Blo 1488064 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B3769375 : Blo 1488064 3769375 := bstep (se 1 (by rfl) ⟨2827031, by rfl⟩ : syracuseStep 3769375 = 5654063) B5654063
theorem B1674175 : Blo 1488064 1674175 := bstep (se 1 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 1674175 = 2511263) B2511263
theorem B4238497 : Blo 1488064 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B4239067 : Blo 1488064 4239067 := bstep (se 1 (by rfl) ⟨3179300, by rfl⟩ : syracuseStep 4239067 = 6358601) B6358601
theorem B4526219 : Blo 1488064 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B5091503 : Blo 1488064 5091503 := bstep (se 1 (by rfl) ⟨3818627, by rfl⟩ : syracuseStep 5091503 = 7637255) B7637255
theorem B146845871 : Blo 1488064 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B9540287 : Blo 1488064 9540287 := bstep (se 1 (by rfl) ⟨7155215, by rfl⟩ : syracuseStep 9540287 = 14310431) B14310431
theorem B85857245 : Blo 1488064 85857245 := bstep (se 3 (by rfl) ⟨16098233, by rfl⟩ : syracuseStep 85857245 = 32196467) B32196467
theorem B2233583 : Blo 1488064 2233583 := bstep (se 1 (by rfl) ⟨1675187, by rfl⟩ : syracuseStep 2233583 = 3350375) B3350375
theorem B2233595 : Blo 1488064 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B4027673 : Blo 1488064 4027673 := bstep (se 2 (by rfl) ⟨1510377, by rfl⟩ : syracuseStep 4027673 = 3020755) B3020755
theorem B2233883 : Blo 1488064 2233883 := bstep (se 1 (by rfl) ⟨1675412, by rfl⟩ : syracuseStep 2233883 = 3350825) B3350825
theorem B1488575 : Blo 1488064 1488575 := bstep (se 1 (by rfl) ⟨1116431, by rfl⟩ : syracuseStep 1488575 = 2232863) B2232863
theorem B2234111 : Blo 1488064 2234111 := bstep (se 1 (by rfl) ⟨1675583, by rfl⟩ : syracuseStep 2234111 = 3351167) B3351167
theorem B1488751 : Blo 1488064 1488751 := bstep (se 1 (by rfl) ⟨1116563, by rfl⟩ : syracuseStep 1488751 = 2233127) B2233127
theorem B7543043 : Blo 1488064 7543043 := bstep (se 1 (by rfl) ⟨5657282, by rfl⟩ : syracuseStep 7543043 = 11314565) B11314565
theorem B13965635 : Blo 1488064 13965635 := bstep (se 1 (by rfl) ⟨10474226, by rfl⟩ : syracuseStep 13965635 = 20948453) B20948453
theorem B2825057 : Blo 1488064 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B7535591 : Blo 1488064 7535591 := bstep (se 1 (by rfl) ⟨5651693, by rfl⟩ : syracuseStep 7535591 = 11303387) B11303387
theorem B57277529 : Blo 1488064 57277529 := bstep (se 2 (by rfl) ⟨21479073, by rfl⟩ : syracuseStep 57277529 = 42958147) B42958147
theorem B29031695 : Blo 1488064 29031695 := bstep (se 1 (by rfl) ⟨21773771, by rfl⟩ : syracuseStep 29031695 = 43547543) B43547543
theorem B5651815 : Blo 1488064 5651815 := bstep (se 1 (by rfl) ⟨4238861, by rfl⟩ : syracuseStep 5651815 = 8477723) B8477723
theorem B1883675 : Blo 1488064 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B57238163 : Blo 1488064 57238163 := bstep (se 1 (by rfl) ⟨42928622, by rfl⟩ : syracuseStep 57238163 = 85857245) B85857245
theorem B7537373 : Blo 1488064 7537373 := bstep (se 3 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 7537373 = 2826515) B2826515
theorem B5023133 : Blo 1488064 5023133 := bstep (se 3 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 5023133 = 1883675) B1883675
theorem B5023727 : Blo 1488064 5023727 := bstep (se 1 (by rfl) ⟨3767795, by rfl⟩ : syracuseStep 5023727 = 7535591) B7535591
theorem B38185019 : Blo 1488064 38185019 := bstep (se 1 (by rfl) ⟨28638764, by rfl⟩ : syracuseStep 38185019 = 57277529) B57277529
theorem B97897247 : Blo 1488064 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B12069917 : Blo 1488064 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B13577341 : Blo 1488064 13577341 := bstep (se 3 (by rfl) ⟨2545751, by rfl⟩ : syracuseStep 13577341 = 5091503) B5091503
theorem B6360191 : Blo 1488064 6360191 := bstep (se 1 (by rfl) ⟨4770143, by rfl⟩ : syracuseStep 6360191 = 9540287) B9540287
theorem B2232233 : Blo 1488064 2232233 := bstep (se 2 (by rfl) ⟨837087, by rfl⟩ : syracuseStep 2232233 = 1674175) B1674175
theorem B5025833 : Blo 1488064 5025833 := bstep (se 2 (by rfl) ⟨1884687, by rfl⟩ : syracuseStep 5025833 = 3769375) B3769375
theorem B9310423 : Blo 1488064 9310423 := bstep (se 1 (by rfl) ⟨6982817, by rfl⟩ : syracuseStep 9310423 = 13965635) B13965635
theorem B19354463 : Blo 1488064 19354463 := bstep (se 1 (by rfl) ⟨14515847, by rfl⟩ : syracuseStep 19354463 = 29031695) B29031695
theorem B7533485 : Blo 1488064 7533485 := bstep (se 3 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 7533485 = 2825057) B2825057
theorem B2905535 : Blo 1488064 2905535 := bstep (se 1 (by rfl) ⟨2179151, by rfl⟩ : syracuseStep 2905535 = 4358303) B4358303
theorem B2234015 : Blo 1488064 2234015 := bstep (se 1 (by rfl) ⟨1675511, by rfl⟩ : syracuseStep 2234015 = 3351023) B3351023
theorem B1489055 : Blo 1488064 1489055 := bstep (se 1 (by rfl) ⟨1116791, by rfl⟩ : syracuseStep 1489055 = 2233583) B2233583
theorem B1489063 : Blo 1488064 1489063 := bstep (se 1 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 1489063 = 2233595) B2233595
theorem B2513065 : Blo 1488064 2513065 := bstep (se 2 (by rfl) ⟨942399, by rfl⟩ : syracuseStep 2513065 = 1884799) B1884799
theorem B2685115 : Blo 1488064 2685115 := bstep (se 1 (by rfl) ⟨2013836, by rfl⟩ : syracuseStep 2685115 = 4027673) B4027673
theorem B1489255 : Blo 1488064 1489255 := bstep (se 1 (by rfl) ⟨1116941, by rfl⟩ : syracuseStep 1489255 = 2233883) B2233883
theorem B1489407 : Blo 1488064 1489407 := bstep (se 1 (by rfl) ⟨1117055, by rfl⟩ : syracuseStep 1489407 = 2234111) B2234111
theorem B82565729 : Blo 1488064 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B5028695 : Blo 1488064 5028695 := bstep (se 1 (by rfl) ⟨3771521, by rfl⟩ : syracuseStep 5028695 = 7543043) B7543043
theorem B5651329 : Blo 1488064 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B7535753 : Blo 1488064 7535753 := bstep (se 2 (by rfl) ⟨2825907, by rfl⟩ : syracuseStep 7535753 = 5651815) B5651815
theorem B5652089 : Blo 1488064 5652089 := bstep (se 2 (by rfl) ⟨2119533, by rfl⟩ : syracuseStep 5652089 = 4239067) B4239067
theorem B3350555 : Blo 1488064 3350555 := bstep (se 1 (by rfl) ⟨2512916, by rfl⟩ : syracuseStep 3350555 = 5025833) B5025833
theorem B3350753 : Blo 1488064 3350753 := bstep (se 2 (by rfl) ⟨1256532, by rfl⟩ : syracuseStep 3350753 = 2513065) B2513065
theorem B38158775 : Blo 1488064 38158775 := bstep (se 1 (by rfl) ⟨28619081, by rfl⟩ : syracuseStep 38158775 = 57238163) B57238163
theorem B12902975 : Blo 1488064 12902975 := bstep (se 1 (by rfl) ⟨9677231, by rfl⟩ : syracuseStep 12902975 = 19354463) B19354463
theorem B5022323 : Blo 1488064 5022323 := bstep (se 1 (by rfl) ⟨3766742, by rfl⟩ : syracuseStep 5022323 = 7533485) B7533485
theorem B14320613 : Blo 1488064 14320613 := bstep (se 4 (by rfl) ⟨1342557, by rfl⟩ : syracuseStep 14320613 = 2685115) B2685115
theorem B55043819 : Blo 1488064 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B3352463 : Blo 1488064 3352463 := bstep (se 1 (by rfl) ⟨2514347, by rfl⟩ : syracuseStep 3352463 = 5028695) B5028695
theorem B8046611 : Blo 1488064 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B5023835 : Blo 1488064 5023835 := bstep (se 1 (by rfl) ⟨3767876, by rfl⟩ : syracuseStep 5023835 = 7535753) B7535753
theorem B12413897 : Blo 1488064 12413897 := bstep (se 2 (by rfl) ⟨4655211, by rfl⟩ : syracuseStep 12413897 = 9310423) B9310423
theorem B5024915 : Blo 1488064 5024915 := bstep (se 1 (by rfl) ⟨3768686, by rfl⟩ : syracuseStep 5024915 = 7537373) B7537373
theorem B25456679 : Blo 1488064 25456679 := bstep (se 1 (by rfl) ⟨19092509, by rfl⟩ : syracuseStep 25456679 = 38185019) B38185019
theorem B4240127 : Blo 1488064 4240127 := bstep (se 1 (by rfl) ⟨3180095, by rfl⟩ : syracuseStep 4240127 = 6360191) B6360191
theorem B1488155 : Blo 1488064 1488155 := bstep (se 1 (by rfl) ⟨1116116, by rfl⟩ : syracuseStep 1488155 = 2232233) B2232233
theorem B3348755 : Blo 1488064 3348755 := bstep (se 1 (by rfl) ⟨2511566, by rfl⟩ : syracuseStep 3348755 = 5023133) B5023133
theorem B1489343 : Blo 1488064 1489343 := bstep (se 1 (by rfl) ⟨1117007, by rfl⟩ : syracuseStep 1489343 = 2234015) B2234015
theorem B7748093 : Blo 1488064 7748093 := bstep (se 3 (by rfl) ⟨1452767, by rfl⟩ : syracuseStep 7748093 = 2905535) B2905535
theorem B7535105 : Blo 1488064 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B3349151 : Blo 1488064 3349151 := bstep (se 1 (by rfl) ⟨2511863, by rfl⟩ : syracuseStep 3349151 = 5023727) B5023727
theorem B18103121 : Blo 1488064 18103121 := bstep (se 2 (by rfl) ⟨6788670, by rfl⟩ : syracuseStep 18103121 = 13577341) B13577341
theorem B65264831 : Blo 1488064 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B3768059 : Blo 1488064 3768059 := bstep (se 1 (by rfl) ⟨2826044, by rfl⟩ : syracuseStep 3768059 = 5652089) B5652089
theorem B8601983 : Blo 1488064 8601983 := bstep (se 1 (by rfl) ⟨6451487, by rfl⟩ : syracuseStep 8601983 = 12902975) B12902975
theorem B2826751 : Blo 1488064 2826751 := bstep (se 1 (by rfl) ⟨2120063, by rfl⟩ : syracuseStep 2826751 = 4240127) B4240127
theorem B20661581 : Blo 1488064 20661581 := bstep (se 3 (by rfl) ⟨3874046, by rfl⟩ : syracuseStep 20661581 = 7748093) B7748093
theorem B5023403 : Blo 1488064 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B12068747 : Blo 1488064 12068747 := bstep (se 1 (by rfl) ⟨9051560, by rfl⟩ : syracuseStep 12068747 = 18103121) B18103121
theorem B8275931 : Blo 1488064 8275931 := bstep (se 1 (by rfl) ⟨6206948, by rfl⟩ : syracuseStep 8275931 = 12413897) B12413897
theorem B43509887 : Blo 1488064 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B25439183 : Blo 1488064 25439183 := bstep (se 1 (by rfl) ⟨19079387, by rfl⟩ : syracuseStep 25439183 = 38158775) B38158775
theorem B9547075 : Blo 1488064 9547075 := bstep (se 1 (by rfl) ⟨7160306, by rfl⟩ : syracuseStep 9547075 = 14320613) B14320613
theorem B36695879 : Blo 1488064 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B2232503 : Blo 1488064 2232503 := bstep (se 1 (by rfl) ⟨1674377, by rfl⟩ : syracuseStep 2232503 = 3348755) B3348755
theorem B2232767 : Blo 1488064 2232767 := bstep (se 1 (by rfl) ⟨1674575, by rfl⟩ : syracuseStep 2232767 = 3349151) B3349151
theorem B2512039 : Blo 1488064 2512039 := bstep (se 1 (by rfl) ⟨1884029, by rfl⟩ : syracuseStep 2512039 = 3768059) B3768059
theorem B2233703 : Blo 1488064 2233703 := bstep (se 1 (by rfl) ⟨1675277, by rfl⟩ : syracuseStep 2233703 = 3350555) B3350555
theorem B16971119 : Blo 1488064 16971119 := bstep (se 1 (by rfl) ⟨12728339, by rfl⟩ : syracuseStep 16971119 = 25456679) B25456679
theorem B2233835 : Blo 1488064 2233835 := bstep (se 1 (by rfl) ⟨1675376, by rfl⟩ : syracuseStep 2233835 = 3350753) B3350753
theorem B3348215 : Blo 1488064 3348215 := bstep (se 1 (by rfl) ⟨2511161, by rfl⟩ : syracuseStep 3348215 = 5022323) B5022323
theorem B2234975 : Blo 1488064 2234975 := bstep (se 1 (by rfl) ⟨1676231, by rfl⟩ : syracuseStep 2234975 = 3352463) B3352463
theorem B5364407 : Blo 1488064 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B3349223 : Blo 1488064 3349223 := bstep (se 1 (by rfl) ⟨2511917, by rfl⟩ : syracuseStep 3349223 = 5023835) B5023835
theorem B3349943 : Blo 1488064 3349943 := bstep (se 1 (by rfl) ⟨2512457, by rfl⟩ : syracuseStep 3349943 = 5024915) B5024915
theorem B5734655 : Blo 1488064 5734655 := bstep (se 1 (by rfl) ⟨4300991, by rfl⟩ : syracuseStep 5734655 = 8601983) B8601983
theorem B3769001 : Blo 1488064 3769001 := bstep (se 2 (by rfl) ⟨1413375, by rfl⟩ : syracuseStep 3769001 = 2826751) B2826751
theorem B11314079 : Blo 1488064 11314079 := bstep (se 1 (by rfl) ⟨8485559, by rfl⟩ : syracuseStep 11314079 = 16971119) B16971119
theorem B8045831 : Blo 1488064 8045831 := bstep (se 1 (by rfl) ⟨6034373, by rfl⟩ : syracuseStep 8045831 = 12068747) B12068747
theorem B14305085 : Blo 1488064 14305085 := bstep (se 3 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 14305085 = 5364407) B5364407
theorem B16959455 : Blo 1488064 16959455 := bstep (se 1 (by rfl) ⟨12719591, by rfl⟩ : syracuseStep 16959455 = 25439183) B25439183
theorem B24463919 : Blo 1488064 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B13774387 : Blo 1488064 13774387 := bstep (se 1 (by rfl) ⟨10330790, by rfl⟩ : syracuseStep 13774387 = 20661581) B20661581
theorem B2232143 : Blo 1488064 2232143 := bstep (se 1 (by rfl) ⟨1674107, by rfl⟩ : syracuseStep 2232143 = 3348215) B3348215
theorem B5517287 : Blo 1488064 5517287 := bstep (se 1 (by rfl) ⟨4137965, by rfl⟩ : syracuseStep 5517287 = 8275931) B8275931
theorem B2232815 : Blo 1488064 2232815 := bstep (se 1 (by rfl) ⟨1674611, by rfl⟩ : syracuseStep 2232815 = 3349223) B3349223
theorem B2233295 : Blo 1488064 2233295 := bstep (se 1 (by rfl) ⟨1674971, by rfl⟩ : syracuseStep 2233295 = 3349943) B3349943
theorem B1488335 : Blo 1488064 1488335 := bstep (se 1 (by rfl) ⟨1116251, by rfl⟩ : syracuseStep 1488335 = 2232503) B2232503
theorem B1488511 : Blo 1488064 1488511 := bstep (se 1 (by rfl) ⟨1116383, by rfl⟩ : syracuseStep 1488511 = 2232767) B2232767
theorem B1489135 : Blo 1488064 1489135 := bstep (se 1 (by rfl) ⟨1116851, by rfl⟩ : syracuseStep 1489135 = 2233703) B2233703
theorem B1489223 : Blo 1488064 1489223 := bstep (se 1 (by rfl) ⟨1116917, by rfl⟩ : syracuseStep 1489223 = 2233835) B2233835
theorem B3348935 : Blo 1488064 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B29006591 : Blo 1488064 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B3349385 : Blo 1488064 3349385 := bstep (se 2 (by rfl) ⟨1256019, by rfl⟩ : syracuseStep 3349385 = 2512039) B2512039
theorem B1489983 : Blo 1488064 1489983 := bstep (se 1 (by rfl) ⟨1117487, by rfl⟩ : syracuseStep 1489983 = 2234975) B2234975
theorem B12729433 : Blo 1488064 12729433 := bstep (se 2 (by rfl) ⟨4773537, by rfl⟩ : syracuseStep 12729433 = 9547075) B9547075
theorem B21455549 : Blo 1488064 21455549 := bstep (se 3 (by rfl) ⟨4022915, by rfl⟩ : syracuseStep 21455549 = 8045831) B8045831
theorem B9536723 : Blo 1488064 9536723 := bstep (se 1 (by rfl) ⟨7152542, by rfl⟩ : syracuseStep 9536723 = 14305085) B14305085
theorem B11306303 : Blo 1488064 11306303 := bstep (se 1 (by rfl) ⟨8479727, by rfl⟩ : syracuseStep 11306303 = 16959455) B16959455
theorem B77350909 : Blo 1488064 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B2232623 : Blo 1488064 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B2232923 : Blo 1488064 2232923 := bstep (se 1 (by rfl) ⟨1674692, by rfl⟩ : syracuseStep 2232923 = 3349385) B3349385
theorem B1488095 : Blo 1488064 1488095 := bstep (se 1 (by rfl) ⟨1116071, by rfl⟩ : syracuseStep 1488095 = 2232143) B2232143
theorem B3823103 : Blo 1488064 3823103 := bstep (se 1 (by rfl) ⟨2867327, by rfl⟩ : syracuseStep 3823103 = 5734655) B5734655
theorem B1488543 : Blo 1488064 1488543 := bstep (se 1 (by rfl) ⟨1116407, by rfl⟩ : syracuseStep 1488543 = 2232815) B2232815
theorem B2512667 : Blo 1488064 2512667 := bstep (se 1 (by rfl) ⟨1884500, by rfl⟩ : syracuseStep 2512667 = 3769001) B3769001
theorem B7542719 : Blo 1488064 7542719 := bstep (se 1 (by rfl) ⟨5657039, by rfl⟩ : syracuseStep 7542719 = 11314079) B11314079
theorem B1488863 : Blo 1488064 1488863 := bstep (se 1 (by rfl) ⟨1116647, by rfl⟩ : syracuseStep 1488863 = 2233295) B2233295
theorem B16972577 : Blo 1488064 16972577 := bstep (se 2 (by rfl) ⟨6364716, by rfl⟩ : syracuseStep 16972577 = 12729433) B12729433
theorem B16309279 : Blo 1488064 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B18365849 : Blo 1488064 18365849 := bstep (se 2 (by rfl) ⟨6887193, by rfl⟩ : syracuseStep 18365849 = 13774387) B13774387
theorem B3678191 : Blo 1488064 3678191 := bstep (se 1 (by rfl) ⟨2758643, by rfl⟩ : syracuseStep 3678191 = 5517287) B5517287
theorem B14303699 : Blo 1488064 14303699 := bstep (se 1 (by rfl) ⟨10727774, by rfl⟩ : syracuseStep 14303699 = 21455549) B21455549
theorem B6357815 : Blo 1488064 6357815 := bstep (se 1 (by rfl) ⟨4768361, by rfl⟩ : syracuseStep 6357815 = 9536723) B9536723
theorem B7537535 : Blo 1488064 7537535 := bstep (se 1 (by rfl) ⟨5653151, by rfl⟩ : syracuseStep 7537535 = 11306303) B11306303
theorem B2548735 : Blo 1488064 2548735 := bstep (se 1 (by rfl) ⟨1911551, by rfl⟩ : syracuseStep 2548735 = 3823103) B3823103
theorem B11315051 : Blo 1488064 11315051 := bstep (se 1 (by rfl) ⟨8486288, by rfl⟩ : syracuseStep 11315051 = 16972577) B16972577
theorem B2452127 : Blo 1488064 2452127 := bstep (se 1 (by rfl) ⟨1839095, by rfl⟩ : syracuseStep 2452127 = 3678191) B3678191
theorem B1675111 : Blo 1488064 1675111 := bstep (se 1 (by rfl) ⟨1256333, by rfl⟩ : syracuseStep 1675111 = 2512667) B2512667
theorem B21745705 : Blo 1488064 21745705 := bstep (se 2 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 21745705 = 16309279) B16309279
theorem B12243899 : Blo 1488064 12243899 := bstep (se 1 (by rfl) ⟨9182924, by rfl⟩ : syracuseStep 12243899 = 18365849) B18365849
theorem B103134545 : Blo 1488064 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B1488415 : Blo 1488064 1488415 := bstep (se 1 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 1488415 = 2232623) B2232623
theorem B1488615 : Blo 1488064 1488615 := bstep (se 1 (by rfl) ⟨1116461, by rfl⟩ : syracuseStep 1488615 = 2232923) B2232923
theorem B5028479 : Blo 1488064 5028479 := bstep (se 1 (by rfl) ⟨3771359, by rfl⟩ : syracuseStep 5028479 = 7542719) B7542719
theorem B9535799 : Blo 1488064 9535799 := bstep (se 1 (by rfl) ⟨7151849, by rfl⟩ : syracuseStep 9535799 = 14303699) B14303699
theorem B68756363 : Blo 1488064 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B6539005 : Blo 1488064 6539005 := bstep (se 3 (by rfl) ⟨1226063, by rfl⟩ : syracuseStep 6539005 = 2452127) B2452127
theorem B3352319 : Blo 1488064 3352319 := bstep (se 1 (by rfl) ⟨2514239, by rfl⟩ : syracuseStep 3352319 = 5028479) B5028479
theorem B13593253 : Blo 1488064 13593253 := bstep (se 4 (by rfl) ⟨1274367, by rfl⟩ : syracuseStep 13593253 = 2548735) B2548735
theorem B28994273 : Blo 1488064 28994273 := bstep (se 2 (by rfl) ⟨10872852, by rfl⟩ : syracuseStep 28994273 = 21745705) B21745705
theorem B4238543 : Blo 1488064 4238543 := bstep (se 1 (by rfl) ⟨3178907, by rfl⟩ : syracuseStep 4238543 = 6357815) B6357815
theorem B5025023 : Blo 1488064 5025023 := bstep (se 1 (by rfl) ⟨3768767, by rfl⟩ : syracuseStep 5025023 = 7537535) B7537535
theorem B2233481 : Blo 1488064 2233481 := bstep (se 2 (by rfl) ⟨837555, by rfl⟩ : syracuseStep 2233481 = 1675111) B1675111
theorem B32650397 : Blo 1488064 32650397 := bstep (se 3 (by rfl) ⟨6121949, by rfl⟩ : syracuseStep 32650397 = 12243899) B12243899
theorem B7543367 : Blo 1488064 7543367 := bstep (se 1 (by rfl) ⟨5657525, by rfl⟩ : syracuseStep 7543367 = 11315051) B11315051
theorem B6357199 : Blo 1488064 6357199 := bstep (se 1 (by rfl) ⟨4767899, by rfl⟩ : syracuseStep 6357199 = 9535799) B9535799
theorem B21766931 : Blo 1488064 21766931 := bstep (se 1 (by rfl) ⟨16325198, by rfl⟩ : syracuseStep 21766931 = 32650397) B32650397
theorem B8718673 : Blo 1488064 8718673 := bstep (se 2 (by rfl) ⟨3269502, by rfl⟩ : syracuseStep 8718673 = 6539005) B6539005
theorem B45837575 : Blo 1488064 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B18124337 : Blo 1488064 18124337 := bstep (se 2 (by rfl) ⟨6796626, by rfl⟩ : syracuseStep 18124337 = 13593253) B13593253
theorem B19329515 : Blo 1488064 19329515 := bstep (se 1 (by rfl) ⟨14497136, by rfl⟩ : syracuseStep 19329515 = 28994273) B28994273
theorem B1488987 : Blo 1488064 1488987 := bstep (se 1 (by rfl) ⟨1116740, by rfl⟩ : syracuseStep 1488987 = 2233481) B2233481
theorem B2234879 : Blo 1488064 2234879 := bstep (se 1 (by rfl) ⟨1676159, by rfl⟩ : syracuseStep 2234879 = 3352319) B3352319
theorem B5028911 : Blo 1488064 5028911 := bstep (se 1 (by rfl) ⟨3771683, by rfl⟩ : syracuseStep 5028911 = 7543367) B7543367
theorem B2825695 : Blo 1488064 2825695 := bstep (se 1 (by rfl) ⟨2119271, by rfl⟩ : syracuseStep 2825695 = 4238543) B4238543
theorem B3350015 : Blo 1488064 3350015 := bstep (se 1 (by rfl) ⟨2512511, by rfl⟩ : syracuseStep 3350015 = 5025023) B5025023
theorem B12886343 : Blo 1488064 12886343 := bstep (se 1 (by rfl) ⟨9664757, by rfl⟩ : syracuseStep 12886343 = 19329515) B19329515
theorem B11624897 : Blo 1488064 11624897 := bstep (se 2 (by rfl) ⟨4359336, by rfl⟩ : syracuseStep 11624897 = 8718673) B8718673
theorem B3352607 : Blo 1488064 3352607 := bstep (se 1 (by rfl) ⟨2514455, by rfl⟩ : syracuseStep 3352607 = 5028911) B5028911
theorem B30558383 : Blo 1488064 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B14511287 : Blo 1488064 14511287 := bstep (se 1 (by rfl) ⟨10883465, by rfl⟩ : syracuseStep 14511287 = 21766931) B21766931
theorem B2233343 : Blo 1488064 2233343 := bstep (se 1 (by rfl) ⟨1675007, by rfl⟩ : syracuseStep 2233343 = 3350015) B3350015
theorem B8476265 : Blo 1488064 8476265 := bstep (se 2 (by rfl) ⟨3178599, by rfl⟩ : syracuseStep 8476265 = 6357199) B6357199
theorem B1489919 : Blo 1488064 1489919 := bstep (se 1 (by rfl) ⟨1117439, by rfl⟩ : syracuseStep 1489919 = 2234879) B2234879
theorem B3767593 : Blo 1488064 3767593 := bstep (se 2 (by rfl) ⟨1412847, by rfl⟩ : syracuseStep 3767593 = 2825695) B2825695
theorem B12082891 : Blo 1488064 12082891 := bstep (se 1 (by rfl) ⟨9062168, by rfl⟩ : syracuseStep 12082891 = 18124337) B18124337
theorem B7749931 : Blo 1488064 7749931 := bstep (se 1 (by rfl) ⟨5812448, by rfl⟩ : syracuseStep 7749931 = 11624897) B11624897
theorem B5023457 : Blo 1488064 5023457 := bstep (se 2 (by rfl) ⟨1883796, by rfl⟩ : syracuseStep 5023457 = 3767593) B3767593
theorem B16110521 : Blo 1488064 16110521 := bstep (se 2 (by rfl) ⟨6041445, by rfl⟩ : syracuseStep 16110521 = 12082891) B12082891
theorem B8590895 : Blo 1488064 8590895 := bstep (se 1 (by rfl) ⟨6443171, by rfl⟩ : syracuseStep 8590895 = 12886343) B12886343
theorem B1488895 : Blo 1488064 1488895 := bstep (se 1 (by rfl) ⟨1116671, by rfl⟩ : syracuseStep 1488895 = 2233343) B2233343
theorem B5650843 : Blo 1488064 5650843 := bstep (se 1 (by rfl) ⟨4238132, by rfl⟩ : syracuseStep 5650843 = 8476265) B8476265
theorem B2235071 : Blo 1488064 2235071 := bstep (se 1 (by rfl) ⟨1676303, by rfl⟩ : syracuseStep 2235071 = 3352607) B3352607
theorem B20372255 : Blo 1488064 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B9674191 : Blo 1488064 9674191 := bstep (se 1 (by rfl) ⟨7255643, by rfl⟩ : syracuseStep 9674191 = 14511287) B14511287
theorem B10740347 : Blo 1488064 10740347 := bstep (se 1 (by rfl) ⟨8055260, by rfl⟩ : syracuseStep 10740347 = 16110521) B16110521
theorem B5727263 : Blo 1488064 5727263 := bstep (se 1 (by rfl) ⟨4295447, by rfl⟩ : syracuseStep 5727263 = 8590895) B8590895
theorem B10333241 : Blo 1488064 10333241 := bstep (se 2 (by rfl) ⟨3874965, by rfl⟩ : syracuseStep 10333241 = 7749931) B7749931
theorem B12898921 : Blo 1488064 12898921 := bstep (se 2 (by rfl) ⟨4837095, by rfl⟩ : syracuseStep 12898921 = 9674191) B9674191
theorem B7534457 : Blo 1488064 7534457 := bstep (se 2 (by rfl) ⟨2825421, by rfl⟩ : syracuseStep 7534457 = 5650843) B5650843
theorem B3348971 : Blo 1488064 3348971 := bstep (se 1 (by rfl) ⟨2511728, by rfl⟩ : syracuseStep 3348971 = 5023457) B5023457
theorem B1490047 : Blo 1488064 1490047 := bstep (se 1 (by rfl) ⟨1117535, by rfl⟩ : syracuseStep 1490047 = 2235071) B2235071
theorem B13581503 : Blo 1488064 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B7160231 : Blo 1488064 7160231 := bstep (se 1 (by rfl) ⟨5370173, by rfl⟩ : syracuseStep 7160231 = 10740347) B10740347
theorem B5022971 : Blo 1488064 5022971 := bstep (se 1 (by rfl) ⟨3767228, by rfl⟩ : syracuseStep 5022971 = 7534457) B7534457
theorem B9054335 : Blo 1488064 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B15272701 : Blo 1488064 15272701 := bstep (se 3 (by rfl) ⟨2863631, by rfl⟩ : syracuseStep 15272701 = 5727263) B5727263
theorem B17198561 : Blo 1488064 17198561 := bstep (se 2 (by rfl) ⟨6449460, by rfl⟩ : syracuseStep 17198561 = 12898921) B12898921
theorem B2232647 : Blo 1488064 2232647 := bstep (se 1 (by rfl) ⟨1674485, by rfl⟩ : syracuseStep 2232647 = 3348971) B3348971
theorem B6888827 : Blo 1488064 6888827 := bstep (se 1 (by rfl) ⟨5166620, by rfl⟩ : syracuseStep 6888827 = 10333241) B10333241
theorem B81454405 : Blo 1488064 81454405 := bstep (se 4 (by rfl) ⟨7636350, by rfl⟩ : syracuseStep 81454405 = 15272701) B15272701
theorem B4592551 : Blo 1488064 4592551 := bstep (se 1 (by rfl) ⟨3444413, by rfl⟩ : syracuseStep 4592551 = 6888827) B6888827
theorem B11465707 : Blo 1488064 11465707 := bstep (se 1 (by rfl) ⟨8599280, by rfl⟩ : syracuseStep 11465707 = 17198561) B17198561
theorem B1488431 : Blo 1488064 1488431 := bstep (se 1 (by rfl) ⟨1116323, by rfl⟩ : syracuseStep 1488431 = 2232647) B2232647
theorem B4773487 : Blo 1488064 4773487 := bstep (se 1 (by rfl) ⟨3580115, by rfl⟩ : syracuseStep 4773487 = 7160231) B7160231
theorem B3348647 : Blo 1488064 3348647 := bstep (se 1 (by rfl) ⟨2511485, by rfl⟩ : syracuseStep 3348647 = 5022971) B5022971
theorem B6036223 : Blo 1488064 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B15287609 : Blo 1488064 15287609 := bstep (se 2 (by rfl) ⟨5732853, by rfl⟩ : syracuseStep 15287609 = 11465707) B11465707
theorem B8048297 : Blo 1488064 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B6123401 : Blo 1488064 6123401 := bstep (se 2 (by rfl) ⟨2296275, by rfl⟩ : syracuseStep 6123401 = 4592551) B4592551
theorem B2232431 : Blo 1488064 2232431 := bstep (se 1 (by rfl) ⟨1674323, by rfl⟩ : syracuseStep 2232431 = 3348647) B3348647
theorem B108605873 : Blo 1488064 108605873 := bstep (se 2 (by rfl) ⟨40727202, by rfl⟩ : syracuseStep 108605873 = 81454405) B81454405
theorem B6364649 : Blo 1488064 6364649 := bstep (se 2 (by rfl) ⟨2386743, by rfl⟩ : syracuseStep 6364649 = 4773487) B4773487
theorem B10191739 : Blo 1488064 10191739 := bstep (se 1 (by rfl) ⟨7643804, by rfl⟩ : syracuseStep 10191739 = 15287609) B15287609
theorem B4082267 : Blo 1488064 4082267 := bstep (se 1 (by rfl) ⟨3061700, by rfl⟩ : syracuseStep 4082267 = 6123401) B6123401
theorem B72403915 : Blo 1488064 72403915 := bstep (se 1 (by rfl) ⟨54302936, by rfl⟩ : syracuseStep 72403915 = 108605873) B108605873
theorem B1488287 : Blo 1488064 1488287 := bstep (se 1 (by rfl) ⟨1116215, by rfl⟩ : syracuseStep 1488287 = 2232431) B2232431
theorem B4243099 : Blo 1488064 4243099 := bstep (se 1 (by rfl) ⟨3182324, by rfl⟩ : syracuseStep 4243099 = 6364649) B6364649
theorem B5365531 : Blo 1488064 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B28616165 : Blo 1488064 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B2721511 : Blo 1488064 2721511 := bstep (se 1 (by rfl) ⟨2041133, by rfl⟩ : syracuseStep 2721511 = 4082267) B4082267
theorem B96538553 : Blo 1488064 96538553 := bstep (se 2 (by rfl) ⟨36201957, by rfl⟩ : syracuseStep 96538553 = 72403915) B72403915
theorem B5657465 : Blo 1488064 5657465 := bstep (se 2 (by rfl) ⟨2121549, by rfl⟩ : syracuseStep 5657465 = 4243099) B4243099
theorem B13588985 : Blo 1488064 13588985 := bstep (se 2 (by rfl) ⟨5095869, by rfl⟩ : syracuseStep 13588985 = 10191739) B10191739
theorem B64359035 : Blo 1488064 64359035 := bstep (se 1 (by rfl) ⟨48269276, by rfl⟩ : syracuseStep 64359035 = 96538553) B96538553
theorem B3771643 : Blo 1488064 3771643 := bstep (se 1 (by rfl) ⟨2828732, by rfl⟩ : syracuseStep 3771643 = 5657465) B5657465
theorem B36237293 : Blo 1488064 36237293 := bstep (se 3 (by rfl) ⟨6794492, by rfl⟩ : syracuseStep 36237293 = 13588985) B13588985
theorem B19077443 : Blo 1488064 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B3628681 : Blo 1488064 3628681 := bstep (se 2 (by rfl) ⟨1360755, by rfl⟩ : syracuseStep 3628681 = 2721511) B2721511
theorem B19352965 : Blo 1488064 19352965 := bstep (se 4 (by rfl) ⟨1814340, by rfl⟩ : syracuseStep 19352965 = 3628681) B3628681
theorem B12718295 : Blo 1488064 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B42906023 : Blo 1488064 42906023 := bstep (se 1 (by rfl) ⟨32179517, by rfl⟩ : syracuseStep 42906023 = 64359035) B64359035
theorem B5028857 : Blo 1488064 5028857 := bstep (se 2 (by rfl) ⟨1885821, by rfl⟩ : syracuseStep 5028857 = 3771643) B3771643
theorem B24158195 : Blo 1488064 24158195 := bstep (se 1 (by rfl) ⟨18118646, by rfl⟩ : syracuseStep 24158195 = 36237293) B36237293
theorem B8478863 : Blo 1488064 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B3352571 : Blo 1488064 3352571 := bstep (se 1 (by rfl) ⟨2514428, by rfl⟩ : syracuseStep 3352571 = 5028857) B5028857
theorem B16105463 : Blo 1488064 16105463 := bstep (se 1 (by rfl) ⟨12079097, by rfl⟩ : syracuseStep 16105463 = 24158195) B24158195
theorem B28604015 : Blo 1488064 28604015 := bstep (se 1 (by rfl) ⟨21453011, by rfl⟩ : syracuseStep 28604015 = 42906023) B42906023
theorem B25803953 : Blo 1488064 25803953 := bstep (se 2 (by rfl) ⟨9676482, by rfl⟩ : syracuseStep 25803953 = 19352965) B19352965
theorem B5652575 : Blo 1488064 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B10736975 : Blo 1488064 10736975 := bstep (se 1 (by rfl) ⟨8052731, by rfl⟩ : syracuseStep 10736975 = 16105463) B16105463
theorem B19069343 : Blo 1488064 19069343 := bstep (se 1 (by rfl) ⟨14302007, by rfl⟩ : syracuseStep 19069343 = 28604015) B28604015
theorem B2235047 : Blo 1488064 2235047 := bstep (se 1 (by rfl) ⟨1676285, by rfl⟩ : syracuseStep 2235047 = 3352571) B3352571
theorem B17202635 : Blo 1488064 17202635 := bstep (se 1 (by rfl) ⟨12901976, by rfl⟩ : syracuseStep 17202635 = 25803953) B25803953
theorem B3768383 : Blo 1488064 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B7157983 : Blo 1488064 7157983 := bstep (se 1 (by rfl) ⟨5368487, by rfl⟩ : syracuseStep 7157983 = 10736975) B10736975
theorem B12712895 : Blo 1488064 12712895 := bstep (se 1 (by rfl) ⟨9534671, by rfl⟩ : syracuseStep 12712895 = 19069343) B19069343
theorem B1490031 : Blo 1488064 1490031 := bstep (se 1 (by rfl) ⟨1117523, by rfl⟩ : syracuseStep 1490031 = 2235047) B2235047
theorem B11468423 : Blo 1488064 11468423 := bstep (se 1 (by rfl) ⟨8601317, by rfl⟩ : syracuseStep 11468423 = 17202635) B17202635
theorem B9543977 : Blo 1488064 9543977 := bstep (se 2 (by rfl) ⟨3578991, by rfl⟩ : syracuseStep 9543977 = 7157983) B7157983
theorem B30582461 : Blo 1488064 30582461 := bstep (se 3 (by rfl) ⟨5734211, by rfl⟩ : syracuseStep 30582461 = 11468423) B11468423
theorem B8475263 : Blo 1488064 8475263 := bstep (se 1 (by rfl) ⟨6356447, by rfl⟩ : syracuseStep 8475263 = 12712895) B12712895
theorem B2512255 : Blo 1488064 2512255 := bstep (se 1 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 2512255 = 3768383) B3768383
theorem B6362651 : Blo 1488064 6362651 := bstep (se 1 (by rfl) ⟨4771988, by rfl⟩ : syracuseStep 6362651 = 9543977) B9543977
theorem B5650175 : Blo 1488064 5650175 := bstep (se 1 (by rfl) ⟨4237631, by rfl⟩ : syracuseStep 5650175 = 8475263) B8475263
theorem B20388307 : Blo 1488064 20388307 := bstep (se 1 (by rfl) ⟨15291230, by rfl⟩ : syracuseStep 20388307 = 30582461) B30582461
theorem B3349673 : Blo 1488064 3349673 := bstep (se 2 (by rfl) ⟨1256127, by rfl⟩ : syracuseStep 3349673 = 2512255) B2512255
theorem B27184409 : Blo 1488064 27184409 := bstep (se 2 (by rfl) ⟨10194153, by rfl⟩ : syracuseStep 27184409 = 20388307) B20388307
theorem B2233115 : Blo 1488064 2233115 := bstep (se 1 (by rfl) ⟨1674836, by rfl⟩ : syracuseStep 2233115 = 3349673) B3349673
theorem B4241767 : Blo 1488064 4241767 := bstep (se 1 (by rfl) ⟨3181325, by rfl⟩ : syracuseStep 4241767 = 6362651) B6362651
theorem B3766783 : Blo 1488064 3766783 := bstep (se 1 (by rfl) ⟨2825087, by rfl⟩ : syracuseStep 3766783 = 5650175) B5650175
theorem B5022377 : Blo 1488064 5022377 := bstep (se 2 (by rfl) ⟨1883391, by rfl⟩ : syracuseStep 5022377 = 3766783) B3766783
theorem B18122939 : Blo 1488064 18122939 := bstep (se 1 (by rfl) ⟨13592204, by rfl⟩ : syracuseStep 18122939 = 27184409) B27184409
theorem B5655689 : Blo 1488064 5655689 := bstep (se 2 (by rfl) ⟨2120883, by rfl⟩ : syracuseStep 5655689 = 4241767) B4241767
theorem B1488743 : Blo 1488064 1488743 := bstep (se 1 (by rfl) ⟨1116557, by rfl⟩ : syracuseStep 1488743 = 2233115) B2233115
theorem B3770459 : Blo 1488064 3770459 := bstep (se 1 (by rfl) ⟨2827844, by rfl⟩ : syracuseStep 3770459 = 5655689) B5655689
theorem B3348251 : Blo 1488064 3348251 := bstep (se 1 (by rfl) ⟨2511188, by rfl⟩ : syracuseStep 3348251 = 5022377) B5022377
theorem B12081959 : Blo 1488064 12081959 := bstep (se 1 (by rfl) ⟨9061469, by rfl⟩ : syracuseStep 12081959 = 18122939) B18122939
theorem B8054639 : Blo 1488064 8054639 := bstep (se 1 (by rfl) ⟨6040979, by rfl⟩ : syracuseStep 8054639 = 12081959) B12081959
theorem B2232167 : Blo 1488064 2232167 := bstep (se 1 (by rfl) ⟨1674125, by rfl⟩ : syracuseStep 2232167 = 3348251) B3348251
theorem B2513639 : Blo 1488064 2513639 := bstep (se 1 (by rfl) ⟨1885229, by rfl⟩ : syracuseStep 2513639 = 3770459) B3770459
theorem B5369759 : Blo 1488064 5369759 := bstep (se 1 (by rfl) ⟨4027319, by rfl⟩ : syracuseStep 5369759 = 8054639) B8054639
theorem B1675759 : Blo 1488064 1675759 := bstep (se 1 (by rfl) ⟨1256819, by rfl⟩ : syracuseStep 1675759 = 2513639) B2513639
theorem B1488111 : Blo 1488064 1488111 := bstep (se 1 (by rfl) ⟨1116083, by rfl⟩ : syracuseStep 1488111 = 2232167) B2232167
theorem B2234345 : Blo 1488064 2234345 := bstep (se 2 (by rfl) ⟨837879, by rfl⟩ : syracuseStep 2234345 = 1675759) B1675759
theorem B3579839 : Blo 1488064 3579839 := bstep (se 1 (by rfl) ⟨2684879, by rfl⟩ : syracuseStep 3579839 = 5369759) B5369759
theorem B2386559 : Blo 1488064 2386559 := bstep (se 1 (by rfl) ⟨1789919, by rfl⟩ : syracuseStep 2386559 = 3579839) B3579839
theorem B1489563 : Blo 1488064 1489563 := bstep (se 1 (by rfl) ⟨1117172, by rfl⟩ : syracuseStep 1489563 = 2234345) B2234345
theorem B1591039 : Blo 1488064 1591039 := bstep (se 1 (by rfl) ⟨1193279, by rfl⟩ : syracuseStep 1591039 = 2386559) B2386559
theorem B2121385 : Blo 1488064 2121385 := bstep (se 2 (by rfl) ⟨795519, by rfl⟩ : syracuseStep 2121385 = 1591039) B1591039
theorem B2828513 : Blo 1488064 2828513 := bstep (se 2 (by rfl) ⟨1060692, by rfl⟩ : syracuseStep 2828513 = 2121385) B2121385
theorem B1885675 : Blo 1488064 1885675 := bstep (se 1 (by rfl) ⟨1414256, by rfl⟩ : syracuseStep 1885675 = 2828513) B2828513
theorem B2514233 : Blo 1488064 2514233 := bstep (se 2 (by rfl) ⟨942837, by rfl⟩ : syracuseStep 2514233 = 1885675) B1885675
theorem B1676155 : Blo 1488064 1676155 := bstep (se 1 (by rfl) ⟨1257116, by rfl⟩ : syracuseStep 1676155 = 2514233) B2514233
theorem B2234873 : Blo 1488064 2234873 := bstep (se 2 (by rfl) ⟨838077, by rfl⟩ : syracuseStep 2234873 = 1676155) B1676155
theorem B1489915 : Blo 1488064 1489915 := bstep (se 1 (by rfl) ⟨1117436, by rfl⟩ : syracuseStep 1489915 = 2234873) B2234873

theorem C0 (j : ℕ) (h1 : 372016 ≤ j) (h2 : j ≤ 372515) : Blo 1488064 (4 * j + 3) := by
  interval_cases j
  · exact B1488067
  · exact B1488071
  · exact B1488075
  · exact B1488079
  · exact B1488083
  · exact B1488087
  · exact B1488091
  · exact B1488095
  · exact B1488099
  · exact B1488103
  · exact B1488107
  · exact B1488111
  · exact B1488115
  · exact B1488119
  · exact B1488123
  · exact B1488127
  · exact B1488131
  · exact B1488135
  · exact B1488139
  · exact B1488143
  · exact B1488147
  · exact B1488151
  · exact B1488155
  · exact B1488159
  · exact B1488163
  · exact B1488167
  · exact B1488171
  · exact B1488175
  · exact B1488179
  · exact B1488183
  · exact B1488187
  · exact B1488191
  · exact B1488195
  · exact B1488199
  · exact B1488203
  · exact B1488207
  · exact B1488211
  · exact B1488215
  · exact B1488219
  · exact B1488223
  · exact B1488227
  · exact B1488231
  · exact B1488235
  · exact B1488239
  · exact B1488243
  · exact B1488247
  · exact B1488251
  · exact B1488255
  · exact B1488259
  · exact B1488263
  · exact B1488267
  · exact B1488271
  · exact B1488275
  · exact B1488279
  · exact B1488283
  · exact B1488287
  · exact B1488291
  · exact B1488295
  · exact B1488299
  · exact B1488303
  · exact B1488307
  · exact B1488311
  · exact B1488315
  · exact B1488319
  · exact B1488323
  · exact B1488327
  · exact B1488331
  · exact B1488335
  · exact B1488339
  · exact B1488343
  · exact B1488347
  · exact B1488351
  · exact B1488355
  · exact B1488359
  · exact B1488363
  · exact B1488367
  · exact B1488371
  · exact B1488375
  · exact B1488379
  · exact B1488383
  · exact B1488387
  · exact B1488391
  · exact B1488395
  · exact B1488399
  · exact B1488403
  · exact B1488407
  · exact B1488411
  · exact B1488415
  · exact B1488419
  · exact B1488423
  · exact B1488427
  · exact B1488431
  · exact B1488435
  · exact B1488439
  · exact B1488443
  · exact B1488447
  · exact B1488451
  · exact B1488455
  · exact B1488459
  · exact B1488463
  · exact B1488467
  · exact B1488471
  · exact B1488475
  · exact B1488479
  · exact B1488483
  · exact B1488487
  · exact B1488491
  · exact B1488495
  · exact B1488499
  · exact B1488503
  · exact B1488507
  · exact B1488511
  · exact B1488515
  · exact B1488519
  · exact B1488523
  · exact B1488527
  · exact B1488531
  · exact B1488535
  · exact B1488539
  · exact B1488543
  · exact B1488547
  · exact B1488551
  · exact B1488555
  · exact B1488559
  · exact B1488563
  · exact B1488567
  · exact B1488571
  · exact B1488575
  · exact B1488579
  · exact B1488583
  · exact B1488587
  · exact B1488591
  · exact B1488595
  · exact B1488599
  · exact B1488603
  · exact B1488607
  · exact B1488611
  · exact B1488615
  · exact B1488619
  · exact B1488623
  · exact B1488627
  · exact B1488631
  · exact B1488635
  · exact B1488639
  · exact B1488643
  · exact B1488647
  · exact B1488651
  · exact B1488655
  · exact B1488659
  · exact B1488663
  · exact B1488667
  · exact B1488671
  · exact B1488675
  · exact B1488679
  · exact B1488683
  · exact B1488687
  · exact B1488691
  · exact B1488695
  · exact B1488699
  · exact B1488703
  · exact B1488707
  · exact B1488711
  · exact B1488715
  · exact B1488719
  · exact B1488723
  · exact B1488727
  · exact B1488731
  · exact B1488735
  · exact B1488739
  · exact B1488743
  · exact B1488747
  · exact B1488751
  · exact B1488755
  · exact B1488759
  · exact B1488763
  · exact B1488767
  · exact B1488771
  · exact B1488775
  · exact B1488779
  · exact B1488783
  · exact B1488787
  · exact B1488791
  · exact B1488795
  · exact B1488799
  · exact B1488803
  · exact B1488807
  · exact B1488811
  · exact B1488815
  · exact B1488819
  · exact B1488823
  · exact B1488827
  · exact B1488831
  · exact B1488835
  · exact B1488839
  · exact B1488843
  · exact B1488847
  · exact B1488851
  · exact B1488855
  · exact B1488859
  · exact B1488863
  · exact B1488867
  · exact B1488871
  · exact B1488875
  · exact B1488879
  · exact B1488883
  · exact B1488887
  · exact B1488891
  · exact B1488895
  · exact B1488899
  · exact B1488903
  · exact B1488907
  · exact B1488911
  · exact B1488915
  · exact B1488919
  · exact B1488923
  · exact B1488927
  · exact B1488931
  · exact B1488935
  · exact B1488939
  · exact B1488943
  · exact B1488947
  · exact B1488951
  · exact B1488955
  · exact B1488959
  · exact B1488963
  · exact B1488967
  · exact B1488971
  · exact B1488975
  · exact B1488979
  · exact B1488983
  · exact B1488987
  · exact B1488991
  · exact B1488995
  · exact B1488999
  · exact B1489003
  · exact B1489007
  · exact B1489011
  · exact B1489015
  · exact B1489019
  · exact B1489023
  · exact B1489027
  · exact B1489031
  · exact B1489035
  · exact B1489039
  · exact B1489043
  · exact B1489047
  · exact B1489051
  · exact B1489055
  · exact B1489059
  · exact B1489063
  · exact B1489067
  · exact B1489071
  · exact B1489075
  · exact B1489079
  · exact B1489083
  · exact B1489087
  · exact B1489091
  · exact B1489095
  · exact B1489099
  · exact B1489103
  · exact B1489107
  · exact B1489111
  · exact B1489115
  · exact B1489119
  · exact B1489123
  · exact B1489127
  · exact B1489131
  · exact B1489135
  · exact B1489139
  · exact B1489143
  · exact B1489147
  · exact B1489151
  · exact B1489155
  · exact B1489159
  · exact B1489163
  · exact B1489167
  · exact B1489171
  · exact B1489175
  · exact B1489179
  · exact B1489183
  · exact B1489187
  · exact B1489191
  · exact B1489195
  · exact B1489199
  · exact B1489203
  · exact B1489207
  · exact B1489211
  · exact B1489215
  · exact B1489219
  · exact B1489223
  · exact B1489227
  · exact B1489231
  · exact B1489235
  · exact B1489239
  · exact B1489243
  · exact B1489247
  · exact B1489251
  · exact B1489255
  · exact B1489259
  · exact B1489263
  · exact B1489267
  · exact B1489271
  · exact B1489275
  · exact B1489279
  · exact B1489283
  · exact B1489287
  · exact B1489291
  · exact B1489295
  · exact B1489299
  · exact B1489303
  · exact B1489307
  · exact B1489311
  · exact B1489315
  · exact B1489319
  · exact B1489323
  · exact B1489327
  · exact B1489331
  · exact B1489335
  · exact B1489339
  · exact B1489343
  · exact B1489347
  · exact B1489351
  · exact B1489355
  · exact B1489359
  · exact B1489363
  · exact B1489367
  · exact B1489371
  · exact B1489375
  · exact B1489379
  · exact B1489383
  · exact B1489387
  · exact B1489391
  · exact B1489395
  · exact B1489399
  · exact B1489403
  · exact B1489407
  · exact B1489411
  · exact B1489415
  · exact B1489419
  · exact B1489423
  · exact B1489427
  · exact B1489431
  · exact B1489435
  · exact B1489439
  · exact B1489443
  · exact B1489447
  · exact B1489451
  · exact B1489455
  · exact B1489459
  · exact B1489463
  · exact B1489467
  · exact B1489471
  · exact B1489475
  · exact B1489479
  · exact B1489483
  · exact B1489487
  · exact B1489491
  · exact B1489495
  · exact B1489499
  · exact B1489503
  · exact B1489507
  · exact B1489511
  · exact B1489515
  · exact B1489519
  · exact B1489523
  · exact B1489527
  · exact B1489531
  · exact B1489535
  · exact B1489539
  · exact B1489543
  · exact B1489547
  · exact B1489551
  · exact B1489555
  · exact B1489559
  · exact B1489563
  · exact B1489567
  · exact B1489571
  · exact B1489575
  · exact B1489579
  · exact B1489583
  · exact B1489587
  · exact B1489591
  · exact B1489595
  · exact B1489599
  · exact B1489603
  · exact B1489607
  · exact B1489611
  · exact B1489615
  · exact B1489619
  · exact B1489623
  · exact B1489627
  · exact B1489631
  · exact B1489635
  · exact B1489639
  · exact B1489643
  · exact B1489647
  · exact B1489651
  · exact B1489655
  · exact B1489659
  · exact B1489663
  · exact B1489667
  · exact B1489671
  · exact B1489675
  · exact B1489679
  · exact B1489683
  · exact B1489687
  · exact B1489691
  · exact B1489695
  · exact B1489699
  · exact B1489703
  · exact B1489707
  · exact B1489711
  · exact B1489715
  · exact B1489719
  · exact B1489723
  · exact B1489727
  · exact B1489731
  · exact B1489735
  · exact B1489739
  · exact B1489743
  · exact B1489747
  · exact B1489751
  · exact B1489755
  · exact B1489759
  · exact B1489763
  · exact B1489767
  · exact B1489771
  · exact B1489775
  · exact B1489779
  · exact B1489783
  · exact B1489787
  · exact B1489791
  · exact B1489795
  · exact B1489799
  · exact B1489803
  · exact B1489807
  · exact B1489811
  · exact B1489815
  · exact B1489819
  · exact B1489823
  · exact B1489827
  · exact B1489831
  · exact B1489835
  · exact B1489839
  · exact B1489843
  · exact B1489847
  · exact B1489851
  · exact B1489855
  · exact B1489859
  · exact B1489863
  · exact B1489867
  · exact B1489871
  · exact B1489875
  · exact B1489879
  · exact B1489883
  · exact B1489887
  · exact B1489891
  · exact B1489895
  · exact B1489899
  · exact B1489903
  · exact B1489907
  · exact B1489911
  · exact B1489915
  · exact B1489919
  · exact B1489923
  · exact B1489927
  · exact B1489931
  · exact B1489935
  · exact B1489939
  · exact B1489943
  · exact B1489947
  · exact B1489951
  · exact B1489955
  · exact B1489959
  · exact B1489963
  · exact B1489967
  · exact B1489971
  · exact B1489975
  · exact B1489979
  · exact B1489983
  · exact B1489987
  · exact B1489991
  · exact B1489995
  · exact B1489999
  · exact B1490003
  · exact B1490007
  · exact B1490011
  · exact B1490015
  · exact B1490019
  · exact B1490023
  · exact B1490027
  · exact B1490031
  · exact B1490035
  · exact B1490039
  · exact B1490043
  · exact B1490047
  · exact B1490051
  · exact B1490055
  · exact B1490059
  · exact B1490063

theorem solution (m : ℕ) (hlo : 1488064 ≤ m) (hhi : m ≤ 1490064) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 372016 ≤ j := by omega
    have hj2 : j ≤ 372515 := by omega
    have hb : Blo 1488064 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
