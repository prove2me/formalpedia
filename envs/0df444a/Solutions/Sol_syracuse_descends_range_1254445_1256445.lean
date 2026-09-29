-- Prove2me | solution 1 for syracuse_descends_range_1254445_1256445
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:18.977663+00:00
-- url     : https://prove2.me/submissions/45e796b0-230a-4ef4-87a5-4f0f822134e2

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


theorem B1884173 : Blo 1254445 1884173 := bbase (se 3 (by rfl) ⟨353282, by rfl⟩ : syracuseStep 1884173 = 706565) (by norm_num)
theorem B2826269 : Blo 1254445 2826269 := bbase (se 3 (by rfl) ⟨529925, by rfl⟩ : syracuseStep 2826269 = 1059851) (by norm_num)
theorem B4767781 : Blo 1254445 4767781 := bbase (se 4 (by rfl) ⟨446979, by rfl⟩ : syracuseStep 4767781 = 893959) (by norm_num)
theorem B1884197 : Blo 1254445 1884197 := bbase (se 4 (by rfl) ⟨176643, by rfl⟩ : syracuseStep 1884197 = 353287) (by norm_num)
theorem B3178541 : Blo 1254445 3178541 := bbase (se 3 (by rfl) ⟨595976, by rfl⟩ : syracuseStep 3178541 = 1191953) (by norm_num)
theorem B5161013 : Blo 1254445 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B1884221 : Blo 1254445 1884221 := bbase (se 3 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 1884221 = 706583) (by norm_num)
theorem B1589321 : Blo 1254445 1589321 := bbase (se 2 (by rfl) ⟨595995, by rfl⟩ : syracuseStep 1589321 = 1191991) (by norm_num)
theorem B1884245 : Blo 1254445 1884245 := bbase (se 8 (by rfl) ⟨11040, by rfl⟩ : syracuseStep 1884245 = 22081) (by norm_num)
theorem B1810525 : Blo 1254445 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B3014749 : Blo 1254445 3014749 := bbase (se 3 (by rfl) ⟨565265, by rfl⟩ : syracuseStep 3014749 = 1130531) (by norm_num)
theorem B2826341 : Blo 1254445 2826341 := bbase (se 4 (by rfl) ⟨264969, by rfl⟩ : syracuseStep 2826341 = 529939) (by norm_num)
theorem B1884269 : Blo 1254445 1884269 := bbase (se 3 (by rfl) ⟨353300, by rfl⟩ : syracuseStep 1884269 = 706601) (by norm_num)
theorem B4235381 : Blo 1254445 4235381 := bbase (se 5 (by rfl) ⟨198533, by rfl⟩ : syracuseStep 4235381 = 397067) (by norm_num)
theorem B1589377 : Blo 1254445 1589377 := bbase (se 2 (by rfl) ⟨596016, by rfl⟩ : syracuseStep 1589377 = 1192033) (by norm_num)
theorem B3219589 : Blo 1254445 3219589 := bbase (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) (by norm_num)
theorem B2384005 : Blo 1254445 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1884293 : Blo 1254445 1884293 := bbase (se 4 (by rfl) ⟨176652, by rfl⟩ : syracuseStep 1884293 = 353305) (by norm_num)
theorem B1884317 : Blo 1254445 1884317 := bbase (se 3 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 1884317 = 706619) (by norm_num)
theorem B2826413 : Blo 1254445 2826413 := bbase (se 3 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 2826413 = 1059905) (by norm_num)
theorem B1884341 : Blo 1254445 1884341 := bbase (se 5 (by rfl) ⟨88328, by rfl⟩ : syracuseStep 1884341 = 176657) (by norm_num)
theorem B6037685 : Blo 1254445 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B1884365 : Blo 1254445 1884365 := bbase (se 3 (by rfl) ⟨353318, by rfl⟩ : syracuseStep 1884365 = 706637) (by norm_num)
theorem B1589473 : Blo 1254445 1589473 := bbase (se 2 (by rfl) ⟨596052, by rfl⟩ : syracuseStep 1589473 = 1192105) (by norm_num)
theorem B1884389 : Blo 1254445 1884389 := bbase (se 4 (by rfl) ⟨176661, by rfl⟩ : syracuseStep 1884389 = 353323) (by norm_num)
theorem B2826485 : Blo 1254445 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B1884413 : Blo 1254445 1884413 := bbase (se 3 (by rfl) ⟨353327, by rfl⟩ : syracuseStep 1884413 = 706655) (by norm_num)
theorem B2384149 : Blo 1254445 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B1884437 : Blo 1254445 1884437 := bbase (se 6 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 1884437 = 88333) (by norm_num)
theorem B1786141 : Blo 1254445 1786141 := bbase (se 3 (by rfl) ⟨334901, by rfl⟩ : syracuseStep 1786141 = 669803) (by norm_num)
theorem B1884461 : Blo 1254445 1884461 := bbase (se 3 (by rfl) ⟨353336, by rfl⟩ : syracuseStep 1884461 = 706673) (by norm_num)
theorem B2826557 : Blo 1254445 2826557 := bbase (se 3 (by rfl) ⟨529979, by rfl⟩ : syracuseStep 2826557 = 1059959) (by norm_num)
theorem B1884485 : Blo 1254445 1884485 := bbase (se 4 (by rfl) ⟨176670, by rfl⟩ : syracuseStep 1884485 = 353341) (by norm_num)
theorem B1810765 : Blo 1254445 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B4768085 : Blo 1254445 4768085 := bbase (se 10 (by rfl) ⟨6984, by rfl⟩ : syracuseStep 4768085 = 13969) (by norm_num)
theorem B1884509 : Blo 1254445 1884509 := bbase (se 3 (by rfl) ⟨353345, by rfl⟩ : syracuseStep 1884509 = 706691) (by norm_num)
theorem B6357365 : Blo 1254445 6357365 := bbase (se 5 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 6357365 = 596003) (by norm_num)
theorem B1884533 : Blo 1254445 1884533 := bbase (se 5 (by rfl) ⟨88337, by rfl⟩ : syracuseStep 1884533 = 176675) (by norm_num)
theorem B3178885 : Blo 1254445 3178885 := bbase (se 4 (by rfl) ⟨298020, by rfl⟩ : syracuseStep 3178885 = 596041) (by norm_num)
theorem B2826629 : Blo 1254445 2826629 := bbase (se 4 (by rfl) ⟨264996, by rfl⟩ : syracuseStep 2826629 = 529993) (by norm_num)
theorem B1589645 : Blo 1254445 1589645 := bbase (se 3 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 1589645 = 596117) (by norm_num)
theorem B1884557 : Blo 1254445 1884557 := bbase (se 3 (by rfl) ⟨353354, by rfl⟩ : syracuseStep 1884557 = 706709) (by norm_num)
theorem B1884581 : Blo 1254445 1884581 := bbase (se 4 (by rfl) ⟨176679, by rfl⟩ : syracuseStep 1884581 = 353359) (by norm_num)
theorem B2384309 : Blo 1254445 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B1884605 : Blo 1254445 1884605 := bbase (se 3 (by rfl) ⟨353363, by rfl⟩ : syracuseStep 1884605 = 706727) (by norm_num)
theorem B6029765 : Blo 1254445 6029765 := bbase (se 4 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 6029765 = 1130581) (by norm_num)
theorem B1589701 : Blo 1254445 1589701 := bbase (se 4 (by rfl) ⟨149034, by rfl⟩ : syracuseStep 1589701 = 298069) (by norm_num)
theorem B2826701 : Blo 1254445 2826701 := bbase (se 3 (by rfl) ⟨530006, by rfl⟩ : syracuseStep 2826701 = 1060013) (by norm_num)
theorem B1884629 : Blo 1254445 1884629 := bbase (se 7 (by rfl) ⟨22085, by rfl⟩ : syracuseStep 1884629 = 44171) (by norm_num)
theorem B1884653 : Blo 1254445 1884653 := bbase (se 3 (by rfl) ⟨353372, by rfl⟩ : syracuseStep 1884653 = 706745) (by norm_num)
theorem B3178997 : Blo 1254445 3178997 := bbase (se 5 (by rfl) ⟨149015, by rfl⟩ : syracuseStep 3178997 = 298031) (by norm_num)
theorem B2826773 : Blo 1254445 2826773 := bbase (se 6 (by rfl) ⟨66252, by rfl⟩ : syracuseStep 2826773 = 132505) (by norm_num)
theorem B4235813 : Blo 1254445 4235813 := bbase (se 4 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 4235813 = 794215) (by norm_num)
theorem B1589797 : Blo 1254445 1589797 := bbase (se 4 (by rfl) ⟨149043, by rfl⟩ : syracuseStep 1589797 = 298087) (by norm_num)
theorem B2384453 : Blo 1254445 2384453 := bbase (se 4 (by rfl) ⟨223542, by rfl⟩ : syracuseStep 2384453 = 447085) (by norm_num)
theorem B2826845 : Blo 1254445 2826845 := bbase (se 3 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 2826845 = 1060067) (by norm_num)
theorem B2826917 : Blo 1254445 2826917 := bbase (se 4 (by rfl) ⟨265023, by rfl⟩ : syracuseStep 2826917 = 530047) (by norm_num)
theorem B3179189 : Blo 1254445 3179189 := bbase (se 5 (by rfl) ⟨149024, by rfl⟩ : syracuseStep 3179189 = 298049) (by norm_num)
theorem B2679485 : Blo 1254445 2679485 := bbase (se 3 (by rfl) ⟨502403, by rfl⟩ : syracuseStep 2679485 = 1004807) (by norm_num)
theorem B1589969 : Blo 1254445 1589969 := bbase (se 2 (by rfl) ⟨596238, by rfl⟩ : syracuseStep 1589969 = 1192477) (by norm_num)
theorem B2581229 : Blo 1254445 2581229 := bbase (se 3 (by rfl) ⟨483980, by rfl⟩ : syracuseStep 2581229 = 967961) (by norm_num)
theorem B2826989 : Blo 1254445 2826989 := bbase (se 3 (by rfl) ⟨530060, by rfl⟩ : syracuseStep 2826989 = 1060121) (by norm_num)
theorem B3015413 : Blo 1254445 3015413 := bbase (se 5 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 3015413 = 282695) (by norm_num)
theorem B5088005 : Blo 1254445 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B1508105 : Blo 1254445 1508105 := bbase (se 2 (by rfl) ⟨565539, by rfl⟩ : syracuseStep 1508105 = 1131079) (by norm_num)
theorem B1590025 : Blo 1254445 1590025 := bbase (se 2 (by rfl) ⟨596259, by rfl⟩ : syracuseStep 1590025 = 1192519) (by norm_num)
theorem B1786637 : Blo 1254445 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B2384741 : Blo 1254445 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B1590121 : Blo 1254445 1590121 := bbase (se 2 (by rfl) ⟨596295, by rfl⟩ : syracuseStep 1590121 = 1192591) (by norm_num)
theorem B5088133 : Blo 1254445 5088133 := bbase (se 4 (by rfl) ⟨477012, by rfl⟩ : syracuseStep 5088133 = 954025) (by norm_num)
theorem B2679725 : Blo 1254445 2679725 := bbase (se 3 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 2679725 = 1004897) (by norm_num)
theorem B2294701 : Blo 1254445 2294701 := bbase (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) (by norm_num)
theorem B1811389 : Blo 1254445 1811389 := bbase (se 3 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 1811389 = 679271) (by norm_num)
theorem B3572693 : Blo 1254445 3572693 := bbase (se 7 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 3572693 = 83735) (by norm_num)
theorem B4236245 : Blo 1254445 4236245 := bbase (se 7 (by rfl) ⟨49643, by rfl⟩ : syracuseStep 4236245 = 99287) (by norm_num)
theorem B3621877 : Blo 1254445 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B2384893 : Blo 1254445 2384893 := bbase (se 3 (by rfl) ⟨447167, by rfl⟩ : syracuseStep 2384893 = 894335) (by norm_num)
theorem B3179533 : Blo 1254445 3179533 := bbase (se 3 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 3179533 = 1192325) (by norm_num)
theorem B5358629 : Blo 1254445 5358629 := bbase (se 4 (by rfl) ⟨502371, by rfl⟩ : syracuseStep 5358629 = 1004743) (by norm_num)
theorem B10183765 : Blo 1254445 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B3179645 : Blo 1254445 3179645 := bbase (se 3 (by rfl) ⟨596183, by rfl⟩ : syracuseStep 3179645 = 1192367) (by norm_num)
theorem B10724501 : Blo 1254445 10724501 := bbase (se 6 (by rfl) ⟨251355, by rfl⟩ : syracuseStep 10724501 = 502711) (by norm_num)
theorem B1909973 : Blo 1254445 1909973 := bbase (se 7 (by rfl) ⟨22382, by rfl⟩ : syracuseStep 1909973 = 44765) (by norm_num)
theorem B1909997 : Blo 1254445 1909997 := bbase (se 3 (by rfl) ⟨358124, by rfl⟩ : syracuseStep 1909997 = 716249) (by norm_num)
theorem B5358869 : Blo 1254445 5358869 := bbase (se 6 (by rfl) ⟨125598, by rfl⟩ : syracuseStep 5358869 = 251197) (by norm_num)
theorem B2385197 : Blo 1254445 2385197 := bbase (se 3 (by rfl) ⟨447224, by rfl⟩ : syracuseStep 2385197 = 894449) (by norm_num)
theorem B1787189 : Blo 1254445 1787189 := bbase (se 5 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 1787189 = 167549) (by norm_num)
theorem B3179837 : Blo 1254445 3179837 := bbase (se 3 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 3179837 = 1192439) (by norm_num)
theorem B5432645 : Blo 1254445 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B4293989 : Blo 1254445 4293989 := bbase (se 4 (by rfl) ⟨402561, by rfl⟩ : syracuseStep 4293989 = 805123) (by norm_num)
theorem B1860989 : Blo 1254445 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B4236677 : Blo 1254445 4236677 := bbase (se 4 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 4236677 = 794377) (by norm_num)
theorem B2680229 : Blo 1254445 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B2680237 : Blo 1254445 2680237 := bbase (se 3 (by rfl) ⟨502544, by rfl⟩ : syracuseStep 2680237 = 1005089) (by norm_num)
theorem B1508797 : Blo 1254445 1508797 := bbase (se 3 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 1508797 = 565799) (by norm_num)
theorem B4294085 : Blo 1254445 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B7153109 : Blo 1254445 7153109 := bbase (se 7 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 7153109 = 167651) (by norm_num)
theorem B2942453 : Blo 1254445 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1697365 : Blo 1254445 1697365 := bbase (se 8 (by rfl) ⟨9945, by rfl⟩ : syracuseStep 1697365 = 19891) (by norm_num)
theorem B4023893 : Blo 1254445 4023893 := bbase (se 8 (by rfl) ⟨23577, by rfl⟩ : syracuseStep 4023893 = 47155) (by norm_num)
theorem B6358661 : Blo 1254445 6358661 := bbase (se 4 (by rfl) ⟨596124, by rfl⟩ : syracuseStep 6358661 = 1192249) (by norm_num)
theorem B1509013 : Blo 1254445 1509013 := bbase (se 6 (by rfl) ⟨35367, by rfl⟩ : syracuseStep 1509013 = 70735) (by norm_num)
theorem B3180181 : Blo 1254445 3180181 := bbase (se 6 (by rfl) ⟨74535, by rfl⟩ : syracuseStep 3180181 = 149071) (by norm_num)
theorem B1836805 : Blo 1254445 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B3180293 : Blo 1254445 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B4237109 : Blo 1254445 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B4835173 : Blo 1254445 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B1697645 : Blo 1254445 1697645 := bbase (se 3 (by rfl) ⟨318308, by rfl⟩ : syracuseStep 1697645 = 636617) (by norm_num)
theorem B9168821 : Blo 1254445 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B6031381 : Blo 1254445 6031381 := bbase (se 6 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 6031381 = 282721) (by norm_num)
theorem B6350885 : Blo 1254445 6350885 := bbase (se 4 (by rfl) ⟨595395, by rfl⟩ : syracuseStep 6350885 = 1190791) (by norm_num)
theorem B1787941 : Blo 1254445 1787941 := bbase (se 4 (by rfl) ⟨167619, by rfl⟩ : syracuseStep 1787941 = 335239) (by norm_num)
theorem B3573877 : Blo 1254445 3573877 := bbase (se 5 (by rfl) ⟨167525, by rfl⟩ : syracuseStep 3573877 = 335051) (by norm_num)
theorem B1411285 : Blo 1254445 1411285 := bbase (se 7 (by rfl) ⟨16538, by rfl⟩ : syracuseStep 1411285 = 33077) (by norm_num)
theorem B9537749 : Blo 1254445 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B4237541 : Blo 1254445 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B1411321 : Blo 1254445 1411321 := bbase (se 2 (by rfl) ⟨529245, by rfl⟩ : syracuseStep 1411321 = 1058491) (by norm_num)
theorem B3221765 : Blo 1254445 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B3574037 : Blo 1254445 3574037 := bbase (se 6 (by rfl) ⟨83766, by rfl⟩ : syracuseStep 3574037 = 167533) (by norm_num)
theorem B1411357 : Blo 1254445 1411357 := bbase (se 3 (by rfl) ⟨264629, by rfl⟩ : syracuseStep 1411357 = 529259) (by norm_num)
theorem B1411393 : Blo 1254445 1411393 := bbase (se 2 (by rfl) ⟨529272, by rfl⟩ : syracuseStep 1411393 = 1058545) (by norm_num)
theorem B1411429 : Blo 1254445 1411429 := bbase (se 4 (by rfl) ⟨132321, by rfl⟩ : syracuseStep 1411429 = 264643) (by norm_num)
theorem B2263405 : Blo 1254445 2263405 := bbase (se 3 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 2263405 = 848777) (by norm_num)
theorem B8046965 : Blo 1254445 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B1411465 : Blo 1254445 1411465 := bbase (se 2 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 1411465 = 1058599) (by norm_num)
theorem B4770197 : Blo 1254445 4770197 := bbase (se 6 (by rfl) ⟨111801, by rfl⟩ : syracuseStep 4770197 = 223603) (by norm_num)
theorem B1411501 : Blo 1254445 1411501 := bbase (se 3 (by rfl) ⟨264656, by rfl⟩ : syracuseStep 1411501 = 529313) (by norm_num)
theorem B1411537 : Blo 1254445 1411537 := bbase (se 2 (by rfl) ⟨529326, by rfl⟩ : syracuseStep 1411537 = 1058653) (by norm_num)
theorem B2009557 : Blo 1254445 2009557 := bbase (se 7 (by rfl) ⟨23549, by rfl⟩ : syracuseStep 2009557 = 47099) (by norm_num)
theorem B1272277 : Blo 1254445 1272277 := bbase (se 7 (by rfl) ⟨14909, by rfl⟩ : syracuseStep 1272277 = 29819) (by norm_num)
theorem B3017189 : Blo 1254445 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1411573 : Blo 1254445 1411573 := bbase (se 5 (by rfl) ⟨66167, by rfl⟩ : syracuseStep 1411573 = 132335) (by norm_num)
theorem B3394037 : Blo 1254445 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2206205 : Blo 1254445 2206205 := bbase (se 3 (by rfl) ⟨413663, by rfl⟩ : syracuseStep 2206205 = 827327) (by norm_num)
theorem B3574277 : Blo 1254445 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B2681365 : Blo 1254445 2681365 := bbase (se 6 (by rfl) ⟨62844, by rfl⟩ : syracuseStep 2681365 = 125689) (by norm_num)
theorem B1411609 : Blo 1254445 1411609 := bbase (se 2 (by rfl) ⟨529353, by rfl⟩ : syracuseStep 1411609 = 1058707) (by norm_num)
theorem B9054773 : Blo 1254445 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B1411645 : Blo 1254445 1411645 := bbase (se 3 (by rfl) ⟨264683, by rfl⟩ : syracuseStep 1411645 = 529367) (by norm_num)
theorem B1411681 : Blo 1254445 1411681 := bbase (se 2 (by rfl) ⟨529380, by rfl⟩ : syracuseStep 1411681 = 1058761) (by norm_num)
theorem B9529973 : Blo 1254445 9529973 := bbase (se 5 (by rfl) ⟨446717, by rfl⟩ : syracuseStep 9529973 = 893435) (by norm_num)
theorem B3394165 : Blo 1254445 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B1411717 : Blo 1254445 1411717 := bbase (se 4 (by rfl) ⟨132348, by rfl⟩ : syracuseStep 1411717 = 264697) (by norm_num)
theorem B4237973 : Blo 1254445 4237973 := bbase (se 6 (by rfl) ⟨99327, by rfl⟩ : syracuseStep 4237973 = 198655) (by norm_num)
theorem B1411753 : Blo 1254445 1411753 := bbase (se 2 (by rfl) ⟨529407, by rfl⟩ : syracuseStep 1411753 = 1058815) (by norm_num)
theorem B4770485 : Blo 1254445 4770485 := bbase (se 5 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 4770485 = 447233) (by norm_num)
theorem B3574469 : Blo 1254445 3574469 := bbase (se 4 (by rfl) ⟨335106, by rfl⟩ : syracuseStep 3574469 = 670213) (by norm_num)
theorem B1411789 : Blo 1254445 1411789 := bbase (se 3 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 1411789 = 529421) (by norm_num)
theorem B1411825 : Blo 1254445 1411825 := bbase (se 2 (by rfl) ⟨529434, by rfl⟩ : syracuseStep 1411825 = 1058869) (by norm_num)
theorem B1411861 : Blo 1254445 1411861 := bbase (se 6 (by rfl) ⟨33090, by rfl⟩ : syracuseStep 1411861 = 66181) (by norm_num)
theorem B1411897 : Blo 1254445 1411897 := bbase (se 2 (by rfl) ⟨529461, by rfl⟩ : syracuseStep 1411897 = 1058923) (by norm_num)
theorem B1788733 : Blo 1254445 1788733 := bbase (se 3 (by rfl) ⟨335387, by rfl⟩ : syracuseStep 1788733 = 670775) (by norm_num)
theorem B1411933 : Blo 1254445 1411933 := bbase (se 3 (by rfl) ⟨264737, by rfl⟩ : syracuseStep 1411933 = 529475) (by norm_num)
theorem B1411969 : Blo 1254445 1411969 := bbase (se 2 (by rfl) ⟨529488, by rfl⟩ : syracuseStep 1411969 = 1058977) (by norm_num)
theorem B2681741 : Blo 1254445 2681741 := bbase (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) (by norm_num)
theorem B5090197 : Blo 1254445 5090197 := bbase (se 6 (by rfl) ⟨119301, by rfl⟩ : syracuseStep 5090197 = 238603) (by norm_num)
theorem B6359957 : Blo 1254445 6359957 := bbase (se 6 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 6359957 = 298123) (by norm_num)
theorem B1412005 : Blo 1254445 1412005 := bbase (se 4 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 1412005 = 264751) (by norm_num)
theorem B1412041 : Blo 1254445 1412041 := bbase (se 2 (by rfl) ⟨529515, by rfl⟩ : syracuseStep 1412041 = 1059031) (by norm_num)
theorem B1412077 : Blo 1254445 1412077 := bbase (se 3 (by rfl) ⟨264764, by rfl⟩ : syracuseStep 1412077 = 529529) (by norm_num)
theorem B2264045 : Blo 1254445 2264045 := bbase (se 3 (by rfl) ⟨424508, by rfl⟩ : syracuseStep 2264045 = 849017) (by norm_num)
theorem B2010101 : Blo 1254445 2010101 := bbase (se 5 (by rfl) ⟨94223, by rfl⟩ : syracuseStep 2010101 = 188447) (by norm_num)
theorem B1412113 : Blo 1254445 1412113 := bbase (se 2 (by rfl) ⟨529542, by rfl⟩ : syracuseStep 1412113 = 1059085) (by norm_num)
theorem B1412149 : Blo 1254445 1412149 := bbase (se 5 (by rfl) ⟨66194, by rfl⟩ : syracuseStep 1412149 = 132389) (by norm_num)
theorem B4238405 : Blo 1254445 4238405 := bbase (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) (by norm_num)
theorem B15281237 : Blo 1254445 15281237 := bbase (se 8 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 15281237 = 179077) (by norm_num)
theorem B1412185 : Blo 1254445 1412185 := bbase (se 2 (by rfl) ⟨529569, by rfl⟩ : syracuseStep 1412185 = 1059139) (by norm_num)
theorem B1412221 : Blo 1254445 1412221 := bbase (se 3 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 1412221 = 529583) (by norm_num)
theorem B1412257 : Blo 1254445 1412257 := bbase (se 2 (by rfl) ⟨529596, by rfl⟩ : syracuseStep 1412257 = 1059193) (by norm_num)
theorem B4525237 : Blo 1254445 4525237 := bbase (se 5 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 4525237 = 424241) (by norm_num)
theorem B1412293 : Blo 1254445 1412293 := bbase (se 4 (by rfl) ⟨132402, by rfl⟩ : syracuseStep 1412293 = 264805) (by norm_num)
theorem B1412329 : Blo 1254445 1412329 := bbase (se 2 (by rfl) ⟨529623, by rfl⟩ : syracuseStep 1412329 = 1059247) (by norm_num)
theorem B1412365 : Blo 1254445 1412365 := bbase (se 3 (by rfl) ⟨264818, by rfl⟩ : syracuseStep 1412365 = 529637) (by norm_num)
theorem B2116901 : Blo 1254445 2116901 := bbase (se 4 (by rfl) ⟨198459, by rfl⟩ : syracuseStep 2116901 = 396919) (by norm_num)
theorem B1412401 : Blo 1254445 1412401 := bbase (se 2 (by rfl) ⟨529650, by rfl⟩ : syracuseStep 1412401 = 1059301) (by norm_num)
theorem B6352181 : Blo 1254445 6352181 := bbase (se 5 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 6352181 = 595517) (by norm_num)
theorem B1412437 : Blo 1254445 1412437 := bbase (se 11 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1412437 = 2069) (by norm_num)
theorem B1273201 : Blo 1254445 1273201 := bbase (se 2 (by rfl) ⟨477450, by rfl⟩ : syracuseStep 1273201 = 954901) (by norm_num)
theorem B1412473 : Blo 1254445 1412473 := bbase (se 2 (by rfl) ⟨529677, by rfl⟩ : syracuseStep 1412473 = 1059355) (by norm_num)
theorem B1412509 : Blo 1254445 1412509 := bbase (se 3 (by rfl) ⟨264845, by rfl⟩ : syracuseStep 1412509 = 529691) (by norm_num)
theorem B2117029 : Blo 1254445 2117029 := bbase (se 4 (by rfl) ⟨198471, by rfl⟩ : syracuseStep 2117029 = 396943) (by norm_num)
theorem B1412545 : Blo 1254445 1412545 := bbase (se 2 (by rfl) ⟨529704, by rfl⟩ : syracuseStep 1412545 = 1059409) (by norm_num)
theorem B1412581 : Blo 1254445 1412581 := bbase (se 4 (by rfl) ⟨132429, by rfl⟩ : syracuseStep 1412581 = 264859) (by norm_num)
theorem B4525541 : Blo 1254445 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B4238837 : Blo 1254445 4238837 := bbase (se 5 (by rfl) ⟨198695, by rfl⟩ : syracuseStep 4238837 = 397391) (by norm_num)
theorem B2117117 : Blo 1254445 2117117 := bbase (se 3 (by rfl) ⟨396959, by rfl⟩ : syracuseStep 2117117 = 793919) (by norm_num)
theorem B5361157 : Blo 1254445 5361157 := bbase (se 4 (by rfl) ⟨502608, by rfl⟩ : syracuseStep 5361157 = 1005217) (by norm_num)
theorem B1412617 : Blo 1254445 1412617 := bbase (se 2 (by rfl) ⟨529731, by rfl⟩ : syracuseStep 1412617 = 1059463) (by norm_num)
theorem B2010653 : Blo 1254445 2010653 := bbase (se 3 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 2010653 = 753995) (by norm_num)
theorem B1412653 : Blo 1254445 1412653 := bbase (se 3 (by rfl) ⟨264872, by rfl⟩ : syracuseStep 1412653 = 529745) (by norm_num)
theorem B2010685 : Blo 1254445 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B1412689 : Blo 1254445 1412689 := bbase (se 2 (by rfl) ⟨529758, by rfl⟩ : syracuseStep 1412689 = 1059517) (by norm_num)
theorem B1412725 : Blo 1254445 1412725 := bbase (se 5 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 1412725 = 132443) (by norm_num)
theorem B7155317 : Blo 1254445 7155317 := bbase (se 5 (by rfl) ⟨335405, by rfl⟩ : syracuseStep 7155317 = 670811) (by norm_num)
theorem B2117245 : Blo 1254445 2117245 := bbase (se 3 (by rfl) ⟨396983, by rfl⟩ : syracuseStep 2117245 = 793967) (by norm_num)
theorem B3059333 : Blo 1254445 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B1396373 : Blo 1254445 1396373 := bbase (se 6 (by rfl) ⟨32727, by rfl⟩ : syracuseStep 1396373 = 65455) (by norm_num)
theorem B1412761 : Blo 1254445 1412761 := bbase (se 2 (by rfl) ⟨529785, by rfl⟩ : syracuseStep 1412761 = 1059571) (by norm_num)
theorem B3575461 : Blo 1254445 3575461 := bbase (se 4 (by rfl) ⟨335199, by rfl⟩ : syracuseStep 3575461 = 670399) (by norm_num)
theorem B1412797 : Blo 1254445 1412797 := bbase (se 3 (by rfl) ⟨264899, by rfl⟩ : syracuseStep 1412797 = 529799) (by norm_num)
theorem B16076501 : Blo 1254445 16076501 := bbase (se 7 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 16076501 = 376793) (by norm_num)
theorem B2117333 : Blo 1254445 2117333 := bbase (se 7 (by rfl) ⟨24812, by rfl⟩ : syracuseStep 2117333 = 49625) (by norm_num)
theorem B1412833 : Blo 1254445 1412833 := bbase (se 2 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 1412833 = 1059625) (by norm_num)
theorem B1289981 : Blo 1254445 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1412869 : Blo 1254445 1412869 := bbase (se 4 (by rfl) ⟨132456, by rfl⟩ : syracuseStep 1412869 = 264913) (by norm_num)
theorem B1412905 : Blo 1254445 1412905 := bbase (se 2 (by rfl) ⟨529839, by rfl⟩ : syracuseStep 1412905 = 1059679) (by norm_num)
theorem B2862917 : Blo 1254445 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1412941 : Blo 1254445 1412941 := bbase (se 3 (by rfl) ⟨264926, by rfl⟩ : syracuseStep 1412941 = 529853) (by norm_num)
theorem B2117461 : Blo 1254445 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B1412977 : Blo 1254445 1412977 := bbase (se 2 (by rfl) ⟨529866, by rfl⟩ : syracuseStep 1412977 = 1059733) (by norm_num)
theorem B2543501 : Blo 1254445 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B1413013 : Blo 1254445 1413013 := bbase (se 6 (by rfl) ⟨33117, by rfl⟩ : syracuseStep 1413013 = 66235) (by norm_num)
theorem B4239269 : Blo 1254445 4239269 := bbase (se 4 (by rfl) ⟨397431, by rfl⟩ : syracuseStep 4239269 = 794863) (by norm_num)
theorem B2117549 : Blo 1254445 2117549 := bbase (se 3 (by rfl) ⟨397040, by rfl⟩ : syracuseStep 2117549 = 794081) (by norm_num)
theorem B1413049 : Blo 1254445 1413049 := bbase (se 2 (by rfl) ⟨529893, by rfl⟩ : syracuseStep 1413049 = 1059787) (by norm_num)
theorem B1413085 : Blo 1254445 1413085 := bbase (se 3 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 1413085 = 529907) (by norm_num)
theorem B2543605 : Blo 1254445 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B1413121 : Blo 1254445 1413121 := bbase (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) (by norm_num)
theorem B1413157 : Blo 1254445 1413157 := bbase (se 4 (by rfl) ⟨132483, by rfl⟩ : syracuseStep 1413157 = 264967) (by norm_num)
theorem B2117677 : Blo 1254445 2117677 := bbase (se 3 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 2117677 = 794129) (by norm_num)
theorem B10727477 : Blo 1254445 10727477 := bbase (se 5 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 10727477 = 1005701) (by norm_num)
theorem B1413193 : Blo 1254445 1413193 := bbase (se 2 (by rfl) ⟨529947, by rfl⟩ : syracuseStep 1413193 = 1059895) (by norm_num)
theorem B1413229 : Blo 1254445 1413229 := bbase (se 3 (by rfl) ⟨264980, by rfl⟩ : syracuseStep 1413229 = 529961) (by norm_num)
theorem B2117765 : Blo 1254445 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B1413265 : Blo 1254445 1413265 := bbase (se 2 (by rfl) ⟨529974, by rfl⟩ : syracuseStep 1413265 = 1059949) (by norm_num)
theorem B1413301 : Blo 1254445 1413301 := bbase (se 5 (by rfl) ⟨66248, by rfl⟩ : syracuseStep 1413301 = 132497) (by norm_num)
theorem B1339589 : Blo 1254445 1339589 := bbase (se 4 (by rfl) ⟨125586, by rfl⟩ : syracuseStep 1339589 = 251173) (by norm_num)
theorem B1413337 : Blo 1254445 1413337 := bbase (se 2 (by rfl) ⟨530001, by rfl⟩ : syracuseStep 1413337 = 1060003) (by norm_num)
theorem B4763893 : Blo 1254445 4763893 := bbase (se 5 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 4763893 = 446615) (by norm_num)
theorem B1413373 : Blo 1254445 1413373 := bbase (se 3 (by rfl) ⟨265007, by rfl⟩ : syracuseStep 1413373 = 530015) (by norm_num)
theorem B2117893 : Blo 1254445 2117893 := bbase (se 4 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 2117893 = 397105) (by norm_num)
theorem B1413409 : Blo 1254445 1413409 := bbase (se 2 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 1413409 = 1060057) (by norm_num)
theorem B1413445 : Blo 1254445 1413445 := bbase (se 4 (by rfl) ⟨132510, by rfl⟩ : syracuseStep 1413445 = 265021) (by norm_num)
theorem B4239701 : Blo 1254445 4239701 := bbase (se 10 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 4239701 = 12421) (by norm_num)
theorem B2117981 : Blo 1254445 2117981 := bbase (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) (by norm_num)
theorem B1413481 : Blo 1254445 1413481 := bbase (se 2 (by rfl) ⟨530055, by rfl⟩ : syracuseStep 1413481 = 1060111) (by norm_num)
theorem B2822525 : Blo 1254445 2822525 := bbase (se 3 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 2822525 = 1058447) (by norm_num)
theorem B1339777 : Blo 1254445 1339777 := bbase (se 2 (by rfl) ⟨502416, by rfl⟩ : syracuseStep 1339777 = 1004833) (by norm_num)
theorem B2822597 : Blo 1254445 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B2118109 : Blo 1254445 2118109 := bbase (se 3 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 2118109 = 794291) (by norm_num)
theorem B2011613 : Blo 1254445 2011613 := bbase (se 3 (by rfl) ⟨377177, by rfl⟩ : syracuseStep 2011613 = 754355) (by norm_num)
theorem B2683381 : Blo 1254445 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B2822669 : Blo 1254445 2822669 := bbase (se 3 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 2822669 = 1058501) (by norm_num)
theorem B4764197 : Blo 1254445 4764197 := bbase (se 4 (by rfl) ⟨446643, by rfl⟩ : syracuseStep 4764197 = 893287) (by norm_num)
theorem B2118197 : Blo 1254445 2118197 := bbase (se 5 (by rfl) ⟨99290, by rfl⟩ : syracuseStep 2118197 = 198581) (by norm_num)
theorem B6353477 : Blo 1254445 6353477 := bbase (se 4 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 6353477 = 1191277) (by norm_num)
theorem B2822741 : Blo 1254445 2822741 := bbase (se 8 (by rfl) ⟨16539, by rfl⟩ : syracuseStep 2822741 = 33079) (by norm_num)
theorem B2822813 : Blo 1254445 2822813 := bbase (se 3 (by rfl) ⟨529277, by rfl⟩ : syracuseStep 2822813 = 1058555) (by norm_num)
theorem B2118325 : Blo 1254445 2118325 := bbase (se 5 (by rfl) ⟨99296, by rfl⟩ : syracuseStep 2118325 = 198593) (by norm_num)
theorem B2822885 : Blo 1254445 2822885 := bbase (se 4 (by rfl) ⟨264645, by rfl⟩ : syracuseStep 2822885 = 529291) (by norm_num)
theorem B3576565 : Blo 1254445 3576565 := bbase (se 5 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 3576565 = 335303) (by norm_num)
theorem B4240133 : Blo 1254445 4240133 := bbase (se 4 (by rfl) ⟨397512, by rfl⟩ : syracuseStep 4240133 = 795025) (by norm_num)
theorem B2118413 : Blo 1254445 2118413 := bbase (se 3 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 2118413 = 794405) (by norm_num)
theorem B2822957 : Blo 1254445 2822957 := bbase (se 3 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 2822957 = 1058609) (by norm_num)
theorem B2823029 : Blo 1254445 2823029 := bbase (se 5 (by rfl) ⟨132329, by rfl⟩ : syracuseStep 2823029 = 264659) (by norm_num)
theorem B7246709 : Blo 1254445 7246709 := bbase (se 5 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 7246709 = 679379) (by norm_num)
theorem B2118541 : Blo 1254445 2118541 := bbase (se 3 (by rfl) ⟨397226, by rfl⟩ : syracuseStep 2118541 = 794453) (by norm_num)
theorem B2823101 : Blo 1254445 2823101 := bbase (se 3 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 2823101 = 1058663) (by norm_num)
theorem B5362645 : Blo 1254445 5362645 := bbase (se 7 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 5362645 = 125687) (by norm_num)
theorem B5362661 : Blo 1254445 5362661 := bbase (se 4 (by rfl) ⟨502749, by rfl⟩ : syracuseStep 5362661 = 1005499) (by norm_num)
theorem B2118629 : Blo 1254445 2118629 := bbase (se 4 (by rfl) ⟨198621, by rfl⟩ : syracuseStep 2118629 = 397243) (by norm_num)
theorem B2823173 : Blo 1254445 2823173 := bbase (se 4 (by rfl) ⟨264672, by rfl⟩ : syracuseStep 2823173 = 529345) (by norm_num)
theorem B4830245 : Blo 1254445 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B2823245 : Blo 1254445 2823245 := bbase (se 3 (by rfl) ⟨529358, by rfl⟩ : syracuseStep 2823245 = 1058717) (by norm_num)
theorem B2118757 : Blo 1254445 2118757 := bbase (se 4 (by rfl) ⟨198633, by rfl⟩ : syracuseStep 2118757 = 397267) (by norm_num)
theorem B2012293 : Blo 1254445 2012293 := bbase (se 4 (by rfl) ⟨188652, by rfl⟩ : syracuseStep 2012293 = 377305) (by norm_num)
theorem B2823317 : Blo 1254445 2823317 := bbase (se 6 (by rfl) ⟨66171, by rfl⟩ : syracuseStep 2823317 = 132343) (by norm_num)
theorem B1340597 : Blo 1254445 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B2118845 : Blo 1254445 2118845 := bbase (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) (by norm_num)
theorem B2012357 : Blo 1254445 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B3175645 : Blo 1254445 3175645 := bbase (se 3 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 3175645 = 1190867) (by norm_num)
theorem B2823389 : Blo 1254445 2823389 := bbase (se 3 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 2823389 = 1058771) (by norm_num)
theorem B1611037 : Blo 1254445 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B1471777 : Blo 1254445 1471777 := bbase (se 2 (by rfl) ⟨551916, by rfl⟩ : syracuseStep 1471777 = 1103833) (by norm_num)
theorem B2823461 : Blo 1254445 2823461 := bbase (se 4 (by rfl) ⟨264699, by rfl⟩ : syracuseStep 2823461 = 529399) (by norm_num)
theorem B6198581 : Blo 1254445 6198581 := bbase (se 5 (by rfl) ⟨290558, by rfl⟩ : syracuseStep 6198581 = 581117) (by norm_num)
theorem B2118973 : Blo 1254445 2118973 := bbase (se 3 (by rfl) ⟨397307, by rfl⟩ : syracuseStep 2118973 = 794615) (by norm_num)
theorem B3175757 : Blo 1254445 3175757 := bbase (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) (by norm_num)
theorem B2823533 : Blo 1254445 2823533 := bbase (se 3 (by rfl) ⟨529412, by rfl⟩ : syracuseStep 2823533 = 1058825) (by norm_num)
theorem B1611149 : Blo 1254445 1611149 := bbase (se 3 (by rfl) ⟨302090, by rfl⟩ : syracuseStep 1611149 = 604181) (by norm_num)
theorem B2119061 : Blo 1254445 2119061 := bbase (se 6 (by rfl) ⟨49665, by rfl⟩ : syracuseStep 2119061 = 99331) (by norm_num)
theorem B2823605 : Blo 1254445 2823605 := bbase (se 5 (by rfl) ⟨132356, by rfl⟩ : syracuseStep 2823605 = 264713) (by norm_num)
theorem B2823677 : Blo 1254445 2823677 := bbase (se 3 (by rfl) ⟨529439, by rfl⟩ : syracuseStep 2823677 = 1058879) (by norm_num)
theorem B3175949 : Blo 1254445 3175949 := bbase (se 3 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 3175949 = 1190981) (by norm_num)
theorem B3814933 : Blo 1254445 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B2119189 : Blo 1254445 2119189 := bbase (se 6 (by rfl) ⟨49668, by rfl⟩ : syracuseStep 2119189 = 99337) (by norm_num)
theorem B2823749 : Blo 1254445 2823749 := bbase (se 4 (by rfl) ⟨264726, by rfl⟩ : syracuseStep 2823749 = 529453) (by norm_num)
theorem B1881677 : Blo 1254445 1881677 := bbase (se 3 (by rfl) ⟨352814, by rfl⟩ : syracuseStep 1881677 = 705629) (by norm_num)
theorem B1881701 : Blo 1254445 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B2545253 : Blo 1254445 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B2119277 : Blo 1254445 2119277 := bbase (se 3 (by rfl) ⟨397364, by rfl⟩ : syracuseStep 2119277 = 794729) (by norm_num)
theorem B1341041 : Blo 1254445 1341041 := bbase (se 2 (by rfl) ⟨502890, by rfl⟩ : syracuseStep 1341041 = 1005781) (by norm_num)
theorem B1431157 : Blo 1254445 1431157 := bbase (se 5 (by rfl) ⟨67085, by rfl⟩ : syracuseStep 1431157 = 134171) (by norm_num)
theorem B1881725 : Blo 1254445 1881725 := bbase (se 3 (by rfl) ⟨352823, by rfl⟩ : syracuseStep 1881725 = 705647) (by norm_num)
theorem B2823821 : Blo 1254445 2823821 := bbase (se 3 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 2823821 = 1058933) (by norm_num)
theorem B1881749 : Blo 1254445 1881749 := bbase (se 6 (by rfl) ⟨44103, by rfl⟩ : syracuseStep 1881749 = 88207) (by norm_num)
theorem B1881773 : Blo 1254445 1881773 := bbase (se 3 (by rfl) ⟨352832, by rfl⟩ : syracuseStep 1881773 = 705665) (by norm_num)
theorem B1431217 : Blo 1254445 1431217 := bbase (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) (by norm_num)
theorem B1881797 : Blo 1254445 1881797 := bbase (se 4 (by rfl) ⟨176418, by rfl⟩ : syracuseStep 1881797 = 352837) (by norm_num)
theorem B2823893 : Blo 1254445 2823893 := bbase (se 7 (by rfl) ⟨33092, by rfl⟩ : syracuseStep 2823893 = 66185) (by norm_num)
theorem B1881821 : Blo 1254445 1881821 := bbase (se 3 (by rfl) ⟨352841, by rfl⟩ : syracuseStep 1881821 = 705683) (by norm_num)
theorem B2119405 : Blo 1254445 2119405 := bbase (se 3 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 2119405 = 794777) (by norm_num)
theorem B1881845 : Blo 1254445 1881845 := bbase (se 5 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 1881845 = 176423) (by norm_num)
theorem B1881869 : Blo 1254445 1881869 := bbase (se 3 (by rfl) ⟨352850, by rfl⟩ : syracuseStep 1881869 = 705701) (by norm_num)
theorem B2545429 : Blo 1254445 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B2823965 : Blo 1254445 2823965 := bbase (se 3 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 2823965 = 1058987) (by norm_num)
theorem B1881893 : Blo 1254445 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B1881917 : Blo 1254445 1881917 := bbase (se 3 (by rfl) ⟨352859, by rfl⟩ : syracuseStep 1881917 = 705719) (by norm_num)
theorem B2119493 : Blo 1254445 2119493 := bbase (se 4 (by rfl) ⟨198702, by rfl⟩ : syracuseStep 2119493 = 397405) (by norm_num)
theorem B1881941 : Blo 1254445 1881941 := bbase (se 9 (by rfl) ⟨5513, by rfl⟩ : syracuseStep 1881941 = 11027) (by norm_num)
theorem B6354773 : Blo 1254445 6354773 := bbase (se 9 (by rfl) ⟨18617, by rfl⟩ : syracuseStep 6354773 = 37235) (by norm_num)
theorem B3176293 : Blo 1254445 3176293 := bbase (se 4 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 3176293 = 595555) (by norm_num)
theorem B2824037 : Blo 1254445 2824037 := bbase (se 4 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 2824037 = 529507) (by norm_num)
theorem B1341289 : Blo 1254445 1341289 := bbase (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) (by norm_num)
theorem B1881965 : Blo 1254445 1881965 := bbase (se 3 (by rfl) ⟨352868, by rfl⟩ : syracuseStep 1881965 = 705737) (by norm_num)
theorem B1881989 : Blo 1254445 1881989 := bbase (se 4 (by rfl) ⟨176436, by rfl⟩ : syracuseStep 1881989 = 352873) (by norm_num)
theorem B4020101 : Blo 1254445 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B1882013 : Blo 1254445 1882013 := bbase (se 3 (by rfl) ⟨352877, by rfl⟩ : syracuseStep 1882013 = 705755) (by norm_num)
theorem B2824109 : Blo 1254445 2824109 := bbase (se 3 (by rfl) ⟨529520, by rfl⟩ : syracuseStep 2824109 = 1059041) (by norm_num)
theorem B1882037 : Blo 1254445 1882037 := bbase (se 5 (by rfl) ⟨88220, by rfl⟩ : syracuseStep 1882037 = 176441) (by norm_num)
theorem B7641013 : Blo 1254445 7641013 := bbase (se 5 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 7641013 = 716345) (by norm_num)
theorem B2119621 : Blo 1254445 2119621 := bbase (se 4 (by rfl) ⟨198714, by rfl⟩ : syracuseStep 2119621 = 397429) (by norm_num)
theorem B1882061 : Blo 1254445 1882061 := bbase (se 3 (by rfl) ⟨352886, by rfl⟩ : syracuseStep 1882061 = 705773) (by norm_num)
theorem B3176405 : Blo 1254445 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B9050069 : Blo 1254445 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B1882085 : Blo 1254445 1882085 := bbase (se 4 (by rfl) ⟨176445, by rfl⟩ : syracuseStep 1882085 = 352891) (by norm_num)
theorem B2824181 : Blo 1254445 2824181 := bbase (se 5 (by rfl) ⟨132383, by rfl⟩ : syracuseStep 2824181 = 264767) (by norm_num)
theorem B1882109 : Blo 1254445 1882109 := bbase (se 3 (by rfl) ⟨352895, by rfl⟩ : syracuseStep 1882109 = 705791) (by norm_num)
theorem B1882133 : Blo 1254445 1882133 := bbase (se 6 (by rfl) ⟨44112, by rfl⟩ : syracuseStep 1882133 = 88225) (by norm_num)
theorem B2119709 : Blo 1254445 2119709 := bbase (se 3 (by rfl) ⟨397445, by rfl⟩ : syracuseStep 2119709 = 794891) (by norm_num)
theorem B1882157 : Blo 1254445 1882157 := bbase (se 3 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 1882157 = 705809) (by norm_num)
theorem B2824253 : Blo 1254445 2824253 := bbase (se 3 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 2824253 = 1059095) (by norm_num)
theorem B1882181 : Blo 1254445 1882181 := bbase (se 4 (by rfl) ⟨176454, by rfl⟩ : syracuseStep 1882181 = 352909) (by norm_num)
theorem B1882205 : Blo 1254445 1882205 := bbase (se 3 (by rfl) ⟨352913, by rfl⟩ : syracuseStep 1882205 = 705827) (by norm_num)
theorem B1882229 : Blo 1254445 1882229 := bbase (se 5 (by rfl) ⟨88229, by rfl⟩ : syracuseStep 1882229 = 176459) (by norm_num)
theorem B2824325 : Blo 1254445 2824325 := bbase (se 4 (by rfl) ⟨264780, by rfl⟩ : syracuseStep 2824325 = 529561) (by norm_num)
theorem B1882253 : Blo 1254445 1882253 := bbase (se 3 (by rfl) ⟨352922, by rfl⟩ : syracuseStep 1882253 = 705845) (by norm_num)
theorem B3176597 : Blo 1254445 3176597 := bbase (se 6 (by rfl) ⟨74451, by rfl⟩ : syracuseStep 3176597 = 148903) (by norm_num)
theorem B2119837 : Blo 1254445 2119837 := bbase (se 3 (by rfl) ⟨397469, by rfl⟩ : syracuseStep 2119837 = 794939) (by norm_num)
theorem B1882277 : Blo 1254445 1882277 := bbase (se 4 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 1882277 = 352927) (by norm_num)
theorem B1882301 : Blo 1254445 1882301 := bbase (se 3 (by rfl) ⟨352931, by rfl⟩ : syracuseStep 1882301 = 705863) (by norm_num)
theorem B2824397 : Blo 1254445 2824397 := bbase (se 3 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 2824397 = 1059149) (by norm_num)
theorem B2578645 : Blo 1254445 2578645 := bbase (se 7 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 2578645 = 60437) (by norm_num)
theorem B1882325 : Blo 1254445 1882325 := bbase (se 7 (by rfl) ⟨22058, by rfl⟩ : syracuseStep 1882325 = 44117) (by norm_num)
theorem B2382061 : Blo 1254445 2382061 := bbase (se 3 (by rfl) ⟨446636, by rfl⟩ : syracuseStep 2382061 = 893273) (by norm_num)
theorem B1882349 : Blo 1254445 1882349 := bbase (se 3 (by rfl) ⟨352940, by rfl⟩ : syracuseStep 1882349 = 705881) (by norm_num)
theorem B2119925 : Blo 1254445 2119925 := bbase (se 5 (by rfl) ⟨99371, by rfl⟩ : syracuseStep 2119925 = 198743) (by norm_num)
theorem B1882373 : Blo 1254445 1882373 := bbase (se 4 (by rfl) ⟨176472, by rfl⟩ : syracuseStep 1882373 = 352945) (by norm_num)
theorem B2824469 : Blo 1254445 2824469 := bbase (se 6 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 2824469 = 132397) (by norm_num)
theorem B1341721 : Blo 1254445 1341721 := bbase (se 2 (by rfl) ⟨503145, by rfl⟩ : syracuseStep 1341721 = 1006291) (by norm_num)
theorem B1882397 : Blo 1254445 1882397 := bbase (se 3 (by rfl) ⟨352949, by rfl⟩ : syracuseStep 1882397 = 705899) (by norm_num)
theorem B1882421 : Blo 1254445 1882421 := bbase (se 5 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 1882421 = 176477) (by norm_num)
theorem B1882445 : Blo 1254445 1882445 := bbase (se 3 (by rfl) ⟨352958, by rfl⟩ : syracuseStep 1882445 = 705917) (by norm_num)
theorem B2824541 : Blo 1254445 2824541 := bbase (se 3 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 2824541 = 1059203) (by norm_num)
theorem B1882469 : Blo 1254445 1882469 := bbase (se 4 (by rfl) ⟨176481, by rfl⟩ : syracuseStep 1882469 = 352963) (by norm_num)
theorem B7149941 : Blo 1254445 7149941 := bbase (se 5 (by rfl) ⟨335153, by rfl⟩ : syracuseStep 7149941 = 670307) (by norm_num)
theorem B12073333 : Blo 1254445 12073333 := bbase (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) (by norm_num)
theorem B2120053 : Blo 1254445 2120053 := bbase (se 5 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 2120053 = 198755) (by norm_num)
theorem B2382205 : Blo 1254445 2382205 := bbase (se 3 (by rfl) ⟨446663, by rfl⟩ : syracuseStep 2382205 = 893327) (by norm_num)
theorem B1882493 : Blo 1254445 1882493 := bbase (se 3 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 1882493 = 705935) (by norm_num)
theorem B1882517 : Blo 1254445 1882517 := bbase (se 6 (by rfl) ⟨44121, by rfl⟩ : syracuseStep 1882517 = 88243) (by norm_num)
theorem B2824613 : Blo 1254445 2824613 := bbase (se 4 (by rfl) ⟨264807, by rfl⟩ : syracuseStep 2824613 = 529615) (by norm_num)
theorem B1882541 : Blo 1254445 1882541 := bbase (se 3 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 1882541 = 705953) (by norm_num)
theorem B1882565 : Blo 1254445 1882565 := bbase (se 4 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 1882565 = 352981) (by norm_num)
theorem B2120141 : Blo 1254445 2120141 := bbase (se 3 (by rfl) ⟨397526, by rfl⟩ : syracuseStep 2120141 = 795053) (by norm_num)
theorem B2038229 : Blo 1254445 2038229 := bbase (se 7 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 2038229 = 47771) (by norm_num)
theorem B1882589 : Blo 1254445 1882589 := bbase (se 3 (by rfl) ⟨352985, by rfl⟩ : syracuseStep 1882589 = 705971) (by norm_num)
theorem B3176941 : Blo 1254445 3176941 := bbase (se 3 (by rfl) ⟨595676, by rfl⟩ : syracuseStep 3176941 = 1191353) (by norm_num)
theorem B2824685 : Blo 1254445 2824685 := bbase (se 3 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 2824685 = 1059257) (by norm_num)
theorem B1587701 : Blo 1254445 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B1882613 : Blo 1254445 1882613 := bbase (se 5 (by rfl) ⟨88247, by rfl⟩ : syracuseStep 1882613 = 176495) (by norm_num)
theorem B1882637 : Blo 1254445 1882637 := bbase (se 3 (by rfl) ⟨352994, by rfl⟩ : syracuseStep 1882637 = 705989) (by norm_num)
theorem B2382365 : Blo 1254445 2382365 := bbase (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) (by norm_num)
theorem B1882661 : Blo 1254445 1882661 := bbase (se 4 (by rfl) ⟨176499, by rfl⟩ : syracuseStep 1882661 = 352999) (by norm_num)
theorem B1587757 : Blo 1254445 1587757 := bbase (se 3 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 1587757 = 595409) (by norm_num)
theorem B2824757 : Blo 1254445 2824757 := bbase (se 5 (by rfl) ⟨132410, by rfl⟩ : syracuseStep 2824757 = 264821) (by norm_num)
theorem B1882685 : Blo 1254445 1882685 := bbase (se 3 (by rfl) ⟨353003, by rfl⟩ : syracuseStep 1882685 = 706007) (by norm_num)
theorem B1882709 : Blo 1254445 1882709 := bbase (se 8 (by rfl) ⟨11031, by rfl⟩ : syracuseStep 1882709 = 22063) (by norm_num)
theorem B3177053 : Blo 1254445 3177053 := bbase (se 3 (by rfl) ⟨595697, by rfl⟩ : syracuseStep 3177053 = 1191395) (by norm_num)
theorem B4766309 : Blo 1254445 4766309 := bbase (se 4 (by rfl) ⟨446841, by rfl⟩ : syracuseStep 4766309 = 893683) (by norm_num)
theorem B1882733 : Blo 1254445 1882733 := bbase (se 3 (by rfl) ⟨353012, by rfl⟩ : syracuseStep 1882733 = 706025) (by norm_num)
theorem B2824829 : Blo 1254445 2824829 := bbase (se 3 (by rfl) ⟨529655, by rfl⟩ : syracuseStep 2824829 = 1059311) (by norm_num)
theorem B1882757 : Blo 1254445 1882757 := bbase (se 4 (by rfl) ⟨176508, by rfl⟩ : syracuseStep 1882757 = 353017) (by norm_num)
theorem B1587853 : Blo 1254445 1587853 := bbase (se 3 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 1587853 = 595445) (by norm_num)
theorem B1432205 : Blo 1254445 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1882781 : Blo 1254445 1882781 := bbase (se 3 (by rfl) ⟨353021, by rfl⟩ : syracuseStep 1882781 = 706043) (by norm_num)
theorem B2382509 : Blo 1254445 2382509 := bbase (se 3 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 2382509 = 893441) (by norm_num)
theorem B1882805 : Blo 1254445 1882805 := bbase (se 5 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 1882805 = 176513) (by norm_num)
theorem B2824901 : Blo 1254445 2824901 := bbase (se 4 (by rfl) ⟨264834, by rfl⟩ : syracuseStep 2824901 = 529669) (by norm_num)
theorem B1882829 : Blo 1254445 1882829 := bbase (se 3 (by rfl) ⟨353030, by rfl⟩ : syracuseStep 1882829 = 706061) (by norm_num)
theorem B1882853 : Blo 1254445 1882853 := bbase (se 4 (by rfl) ⟨176517, by rfl⟩ : syracuseStep 1882853 = 353035) (by norm_num)
theorem B1882877 : Blo 1254445 1882877 := bbase (se 3 (by rfl) ⟨353039, by rfl⟩ : syracuseStep 1882877 = 706079) (by norm_num)
theorem B4020997 : Blo 1254445 4020997 := bbase (se 4 (by rfl) ⟨376968, by rfl⟩ : syracuseStep 4020997 = 753937) (by norm_num)
theorem B2824973 : Blo 1254445 2824973 := bbase (se 3 (by rfl) ⟨529682, by rfl⟩ : syracuseStep 2824973 = 1059365) (by norm_num)
theorem B1882901 : Blo 1254445 1882901 := bbase (se 6 (by rfl) ⟨44130, by rfl⟩ : syracuseStep 1882901 = 88261) (by norm_num)
theorem B3177245 : Blo 1254445 3177245 := bbase (se 3 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 3177245 = 1191467) (by norm_num)
theorem B1882925 : Blo 1254445 1882925 := bbase (se 3 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 1882925 = 706097) (by norm_num)
theorem B1588025 : Blo 1254445 1588025 := bbase (se 2 (by rfl) ⟨595509, by rfl⟩ : syracuseStep 1588025 = 1191019) (by norm_num)
theorem B1882949 : Blo 1254445 1882949 := bbase (se 4 (by rfl) ⟨176526, by rfl⟩ : syracuseStep 1882949 = 353053) (by norm_num)
theorem B2825045 : Blo 1254445 2825045 := bbase (se 9 (by rfl) ⟨8276, by rfl⟩ : syracuseStep 2825045 = 16553) (by norm_num)
theorem B1882973 : Blo 1254445 1882973 := bbase (se 3 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 1882973 = 706115) (by norm_num)
theorem B4234085 : Blo 1254445 4234085 := bbase (se 4 (by rfl) ⟨396945, by rfl⟩ : syracuseStep 4234085 = 793891) (by norm_num)
theorem B1588081 : Blo 1254445 1588081 := bbase (se 2 (by rfl) ⟨595530, by rfl⟩ : syracuseStep 1588081 = 1191061) (by norm_num)
theorem B1882997 : Blo 1254445 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B4766597 : Blo 1254445 4766597 := bbase (se 4 (by rfl) ⟨446868, by rfl⟩ : syracuseStep 4766597 = 893737) (by norm_num)
theorem B1883021 : Blo 1254445 1883021 := bbase (se 3 (by rfl) ⟨353066, by rfl⟩ : syracuseStep 1883021 = 706133) (by norm_num)
theorem B2825117 : Blo 1254445 2825117 := bbase (se 3 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 2825117 = 1059419) (by norm_num)
theorem B1883045 : Blo 1254445 1883045 := bbase (se 4 (by rfl) ⟨176535, by rfl⟩ : syracuseStep 1883045 = 353071) (by norm_num)
theorem B1883069 : Blo 1254445 1883069 := bbase (se 3 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 1883069 = 706151) (by norm_num)
theorem B2382797 : Blo 1254445 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B1588177 : Blo 1254445 1588177 := bbase (se 2 (by rfl) ⟨595566, by rfl⟩ : syracuseStep 1588177 = 1191133) (by norm_num)
theorem B1883093 : Blo 1254445 1883093 := bbase (se 7 (by rfl) ⟨22067, by rfl⟩ : syracuseStep 1883093 = 44135) (by norm_num)
theorem B2825189 : Blo 1254445 2825189 := bbase (se 4 (by rfl) ⟨264861, by rfl⟩ : syracuseStep 2825189 = 529723) (by norm_num)
theorem B1883117 : Blo 1254445 1883117 := bbase (se 3 (by rfl) ⟨353084, by rfl⟩ : syracuseStep 1883117 = 706169) (by norm_num)
theorem B1883141 : Blo 1254445 1883141 := bbase (se 4 (by rfl) ⟨176544, by rfl⟩ : syracuseStep 1883141 = 353089) (by norm_num)
theorem B1883165 : Blo 1254445 1883165 := bbase (se 3 (by rfl) ⟨353093, by rfl⟩ : syracuseStep 1883165 = 706187) (by norm_num)
theorem B6446117 : Blo 1254445 6446117 := bbase (se 4 (by rfl) ⟨604323, by rfl⟩ : syracuseStep 6446117 = 1208647) (by norm_num)
theorem B2825261 : Blo 1254445 2825261 := bbase (se 3 (by rfl) ⟨529736, by rfl⟩ : syracuseStep 2825261 = 1059473) (by norm_num)
theorem B1883189 : Blo 1254445 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B1883213 : Blo 1254445 1883213 := bbase (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) (by norm_num)
theorem B2382949 : Blo 1254445 2382949 := bbase (se 4 (by rfl) ⟨223401, by rfl⟩ : syracuseStep 2382949 = 446803) (by norm_num)
theorem B1883237 : Blo 1254445 1883237 := bbase (se 4 (by rfl) ⟨176553, by rfl⟩ : syracuseStep 1883237 = 353107) (by norm_num)
theorem B6356069 : Blo 1254445 6356069 := bbase (se 4 (by rfl) ⟨595881, by rfl⟩ : syracuseStep 6356069 = 1191763) (by norm_num)
theorem B3177589 : Blo 1254445 3177589 := bbase (se 5 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 3177589 = 297899) (by norm_num)
theorem B2825333 : Blo 1254445 2825333 := bbase (se 5 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 2825333 = 264875) (by norm_num)
theorem B1588349 : Blo 1254445 1588349 := bbase (se 3 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 1588349 = 595631) (by norm_num)
theorem B1883261 : Blo 1254445 1883261 := bbase (se 3 (by rfl) ⟨353111, by rfl⟩ : syracuseStep 1883261 = 706223) (by norm_num)
theorem B1883285 : Blo 1254445 1883285 := bbase (se 6 (by rfl) ⟨44139, by rfl⟩ : syracuseStep 1883285 = 88279) (by norm_num)
theorem B1883309 : Blo 1254445 1883309 := bbase (se 3 (by rfl) ⟨353120, by rfl⟩ : syracuseStep 1883309 = 706241) (by norm_num)
theorem B1588405 : Blo 1254445 1588405 := bbase (se 5 (by rfl) ⟨74456, by rfl⟩ : syracuseStep 1588405 = 148913) (by norm_num)
theorem B5364917 : Blo 1254445 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B2825405 : Blo 1254445 2825405 := bbase (se 3 (by rfl) ⟨529763, by rfl⟩ : syracuseStep 2825405 = 1059527) (by norm_num)
theorem B1883333 : Blo 1254445 1883333 := bbase (se 4 (by rfl) ⟨176562, by rfl⟩ : syracuseStep 1883333 = 353125) (by norm_num)
theorem B1883357 : Blo 1254445 1883357 := bbase (se 3 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 1883357 = 706259) (by norm_num)
theorem B3177701 : Blo 1254445 3177701 := bbase (se 4 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 3177701 = 595819) (by norm_num)
theorem B1883381 : Blo 1254445 1883381 := bbase (se 5 (by rfl) ⟨88283, by rfl⟩ : syracuseStep 1883381 = 176567) (by norm_num)
theorem B2825477 : Blo 1254445 2825477 := bbase (se 4 (by rfl) ⟨264888, by rfl⟩ : syracuseStep 2825477 = 529777) (by norm_num)
theorem B1883405 : Blo 1254445 1883405 := bbase (se 3 (by rfl) ⟨353138, by rfl⟩ : syracuseStep 1883405 = 706277) (by norm_num)
theorem B4234517 : Blo 1254445 4234517 := bbase (se 6 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 4234517 = 198493) (by norm_num)
theorem B1588501 : Blo 1254445 1588501 := bbase (se 6 (by rfl) ⟨37230, by rfl⟩ : syracuseStep 1588501 = 74461) (by norm_num)
theorem B1883429 : Blo 1254445 1883429 := bbase (se 4 (by rfl) ⟨176571, by rfl⟩ : syracuseStep 1883429 = 353143) (by norm_num)
theorem B1883453 : Blo 1254445 1883453 := bbase (se 3 (by rfl) ⟨353147, by rfl⟩ : syracuseStep 1883453 = 706295) (by norm_num)
theorem B6446405 : Blo 1254445 6446405 := bbase (se 4 (by rfl) ⟨604350, by rfl⟩ : syracuseStep 6446405 = 1208701) (by norm_num)
theorem B2825549 : Blo 1254445 2825549 := bbase (se 3 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 2825549 = 1059581) (by norm_num)
theorem B1883477 : Blo 1254445 1883477 := bbase (se 11 (by rfl) ⟨1379, by rfl⟩ : syracuseStep 1883477 = 2759) (by norm_num)
theorem B1883501 : Blo 1254445 1883501 := bbase (se 3 (by rfl) ⟨353156, by rfl⟩ : syracuseStep 1883501 = 706313) (by norm_num)
theorem B2039165 : Blo 1254445 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1883525 : Blo 1254445 1883525 := bbase (se 4 (by rfl) ⟨176580, by rfl⟩ : syracuseStep 1883525 = 353161) (by norm_num)
theorem B2383253 : Blo 1254445 2383253 := bbase (se 6 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 2383253 = 111715) (by norm_num)
theorem B2825621 : Blo 1254445 2825621 := bbase (se 6 (by rfl) ⟨66225, by rfl⟩ : syracuseStep 2825621 = 132451) (by norm_num)
theorem B1883549 : Blo 1254445 1883549 := bbase (se 3 (by rfl) ⟨353165, by rfl⟩ : syracuseStep 1883549 = 706331) (by norm_num)
theorem B3177893 : Blo 1254445 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B1883573 : Blo 1254445 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B1588673 : Blo 1254445 1588673 := bbase (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) (by norm_num)
theorem B6438341 : Blo 1254445 6438341 := bbase (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) (by norm_num)
theorem B1883597 : Blo 1254445 1883597 := bbase (se 3 (by rfl) ⟨353174, by rfl⟩ : syracuseStep 1883597 = 706349) (by norm_num)
theorem B2825693 : Blo 1254445 2825693 := bbase (se 3 (by rfl) ⟨529817, by rfl⟩ : syracuseStep 2825693 = 1059635) (by norm_num)
theorem B1883621 : Blo 1254445 1883621 := bbase (se 4 (by rfl) ⟨176589, by rfl⟩ : syracuseStep 1883621 = 353179) (by norm_num)
theorem B1588729 : Blo 1254445 1588729 := bbase (se 2 (by rfl) ⟨595773, by rfl⟩ : syracuseStep 1588729 = 1191547) (by norm_num)
theorem B1883645 : Blo 1254445 1883645 := bbase (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) (by norm_num)
theorem B7151125 : Blo 1254445 7151125 := bbase (se 6 (by rfl) ⟨167604, by rfl⟩ : syracuseStep 7151125 = 335209) (by norm_num)
theorem B1883669 : Blo 1254445 1883669 := bbase (se 6 (by rfl) ⟨44148, by rfl⟩ : syracuseStep 1883669 = 88297) (by norm_num)
theorem B2825765 : Blo 1254445 2825765 := bbase (se 4 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 2825765 = 529831) (by norm_num)
theorem B1883693 : Blo 1254445 1883693 := bbase (se 3 (by rfl) ⟨353192, by rfl⟩ : syracuseStep 1883693 = 706385) (by norm_num)
theorem B1883717 : Blo 1254445 1883717 := bbase (se 4 (by rfl) ⟨176598, by rfl⟩ : syracuseStep 1883717 = 353197) (by norm_num)
theorem B1588825 : Blo 1254445 1588825 := bbase (se 2 (by rfl) ⟨595809, by rfl⟩ : syracuseStep 1588825 = 1191619) (by norm_num)
theorem B1883741 : Blo 1254445 1883741 := bbase (se 3 (by rfl) ⟨353201, by rfl⟩ : syracuseStep 1883741 = 706403) (by norm_num)
theorem B2825837 : Blo 1254445 2825837 := bbase (se 3 (by rfl) ⟨529844, by rfl⟩ : syracuseStep 2825837 = 1059689) (by norm_num)
theorem B1883765 : Blo 1254445 1883765 := bbase (se 5 (by rfl) ⟨88301, by rfl⟩ : syracuseStep 1883765 = 176603) (by norm_num)
theorem B1883789 : Blo 1254445 1883789 := bbase (se 3 (by rfl) ⟨353210, by rfl⟩ : syracuseStep 1883789 = 706421) (by norm_num)
theorem B2260637 : Blo 1254445 2260637 := bbase (se 3 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 2260637 = 847739) (by norm_num)
theorem B1883813 : Blo 1254445 1883813 := bbase (se 4 (by rfl) ⟨176607, by rfl⟩ : syracuseStep 1883813 = 353215) (by norm_num)
theorem B2825909 : Blo 1254445 2825909 := bbase (se 5 (by rfl) ⟨132464, by rfl⟩ : syracuseStep 2825909 = 264929) (by norm_num)
theorem B1883837 : Blo 1254445 1883837 := bbase (se 3 (by rfl) ⟨353219, by rfl⟩ : syracuseStep 1883837 = 706439) (by norm_num)
theorem B4234949 : Blo 1254445 4234949 := bbase (se 4 (by rfl) ⟨397026, by rfl⟩ : syracuseStep 4234949 = 794053) (by norm_num)
theorem B1720013 : Blo 1254445 1720013 := bbase (se 3 (by rfl) ⟨322502, by rfl⟩ : syracuseStep 1720013 = 645005) (by norm_num)
theorem B1883861 : Blo 1254445 1883861 := bbase (se 7 (by rfl) ⟨22076, by rfl⟩ : syracuseStep 1883861 = 44153) (by norm_num)
theorem B1883885 : Blo 1254445 1883885 := bbase (se 3 (by rfl) ⟨353228, by rfl⟩ : syracuseStep 1883885 = 706457) (by norm_num)
theorem B3178237 : Blo 1254445 3178237 := bbase (se 3 (by rfl) ⟨595919, by rfl⟩ : syracuseStep 3178237 = 1191839) (by norm_num)
theorem B2825981 : Blo 1254445 2825981 := bbase (se 3 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 2825981 = 1059743) (by norm_num)
theorem B1588997 : Blo 1254445 1588997 := bbase (se 4 (by rfl) ⟨148968, by rfl⟩ : syracuseStep 1588997 = 297937) (by norm_num)
theorem B1883909 : Blo 1254445 1883909 := bbase (se 4 (by rfl) ⟨176616, by rfl⟩ : syracuseStep 1883909 = 353233) (by norm_num)
theorem B1883933 : Blo 1254445 1883933 := bbase (se 3 (by rfl) ⟨353237, by rfl⟩ : syracuseStep 1883933 = 706475) (by norm_num)
theorem B1507105 : Blo 1254445 1507105 := bbase (se 2 (by rfl) ⟨565164, by rfl⟩ : syracuseStep 1507105 = 1130329) (by norm_num)
theorem B1883957 : Blo 1254445 1883957 := bbase (se 5 (by rfl) ⟨88310, by rfl⟩ : syracuseStep 1883957 = 176621) (by norm_num)
theorem B1589053 : Blo 1254445 1589053 := bbase (se 3 (by rfl) ⟨297947, by rfl⟩ : syracuseStep 1589053 = 595895) (by norm_num)
theorem B2826053 : Blo 1254445 2826053 := bbase (se 4 (by rfl) ⟨264942, by rfl⟩ : syracuseStep 2826053 = 529885) (by norm_num)
theorem B1883981 : Blo 1254445 1883981 := bbase (se 3 (by rfl) ⟨353246, by rfl⟩ : syracuseStep 1883981 = 706493) (by norm_num)
theorem B1884005 : Blo 1254445 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B3178349 : Blo 1254445 3178349 := bbase (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) (by norm_num)
theorem B1884029 : Blo 1254445 1884029 := bbase (se 3 (by rfl) ⟨353255, by rfl⟩ : syracuseStep 1884029 = 706511) (by norm_num)
theorem B2826125 : Blo 1254445 2826125 := bbase (se 3 (by rfl) ⟨529898, by rfl⟩ : syracuseStep 2826125 = 1059797) (by norm_num)
theorem B1884053 : Blo 1254445 1884053 := bbase (se 6 (by rfl) ⟨44157, by rfl⟩ : syracuseStep 1884053 = 88315) (by norm_num)
theorem B1589149 : Blo 1254445 1589149 := bbase (se 3 (by rfl) ⟨297965, by rfl⟩ : syracuseStep 1589149 = 595931) (by norm_num)
theorem B3391397 : Blo 1254445 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B1884077 : Blo 1254445 1884077 := bbase (se 3 (by rfl) ⟨353264, by rfl⟩ : syracuseStep 1884077 = 706529) (by norm_num)
theorem B1884101 : Blo 1254445 1884101 := bbase (se 4 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 1884101 = 353269) (by norm_num)
theorem B2826197 : Blo 1254445 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B1884125 : Blo 1254445 1884125 := bbase (se 3 (by rfl) ⟨353273, by rfl⟩ : syracuseStep 1884125 = 706547) (by norm_num)
theorem B1884149 : Blo 1254445 1884149 := bbase (se 5 (by rfl) ⟨88319, by rfl⟩ : syracuseStep 1884149 = 176639) (by norm_num)
theorem B1884161 : Blo 1254445 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B1884179 : Blo 1254445 1884179 := bstep (se 1 (by rfl) ⟨1413134, by rfl⟩ : syracuseStep 1884179 = 2826269) B2826269
theorem B7151651 : Blo 1254445 7151651 := bstep (se 1 (by rfl) ⟨5363738, by rfl⟩ : syracuseStep 7151651 = 10727477) B10727477
theorem B3440675 : Blo 1254445 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B6357041 : Blo 1254445 6357041 := bstep (se 2 (by rfl) ⟨2383890, by rfl⟩ : syracuseStep 6357041 = 4767781) B4767781
theorem B2383921 : Blo 1254445 2383921 := bstep (se 2 (by rfl) ⟨893970, by rfl⟩ : syracuseStep 2383921 = 1787941) B1787941
theorem B1884209 : Blo 1254445 1884209 := bstep (se 2 (by rfl) ⟨706578, by rfl⟩ : syracuseStep 1884209 = 1413157) B1413157
theorem B1884227 : Blo 1254445 1884227 := bstep (se 1 (by rfl) ⟨1413170, by rfl⟩ : syracuseStep 1884227 = 2826341) B2826341
theorem B1884257 : Blo 1254445 1884257 := bstep (se 2 (by rfl) ⟨706596, by rfl⟩ : syracuseStep 1884257 = 1413193) B1413193
theorem B1884275 : Blo 1254445 1884275 := bstep (se 1 (by rfl) ⟨1413206, by rfl⟩ : syracuseStep 1884275 = 2826413) B2826413
theorem B1884305 : Blo 1254445 1884305 := bstep (se 2 (by rfl) ⟨706614, by rfl⟩ : syracuseStep 1884305 = 1413229) B1413229
theorem B1884323 : Blo 1254445 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B4292785 : Blo 1254445 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B3178673 : Blo 1254445 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1884353 : Blo 1254445 1884353 := bstep (se 2 (by rfl) ⟨706632, by rfl⟩ : syracuseStep 1884353 = 1413265) B1413265
theorem B2826449 : Blo 1254445 2826449 := bstep (se 2 (by rfl) ⟨1059918, by rfl⟩ : syracuseStep 2826449 = 2119837) B2119837
theorem B1884371 : Blo 1254445 1884371 := bstep (se 1 (by rfl) ⟨1413278, by rfl⟩ : syracuseStep 1884371 = 2826557) B2826557
theorem B3178723 : Blo 1254445 3178723 := bstep (se 1 (by rfl) ⟨2384042, by rfl⟩ : syracuseStep 3178723 = 4768085) B4768085
theorem B2826467 : Blo 1254445 2826467 := bstep (se 1 (by rfl) ⟨2119850, by rfl⟩ : syracuseStep 2826467 = 4239701) B4239701
theorem B1884401 : Blo 1254445 1884401 := bstep (se 2 (by rfl) ⟨706650, by rfl⟩ : syracuseStep 1884401 = 1413301) B1413301
theorem B1884419 : Blo 1254445 1884419 := bstep (se 1 (by rfl) ⟨1413314, by rfl⟩ : syracuseStep 1884419 = 2826629) B2826629
theorem B1884449 : Blo 1254445 1884449 := bstep (se 2 (by rfl) ⟨706668, by rfl⟩ : syracuseStep 1884449 = 1413337) B1413337
theorem B1589539 : Blo 1254445 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B1884467 : Blo 1254445 1884467 := bstep (se 1 (by rfl) ⟨1413350, by rfl⟩ : syracuseStep 1884467 = 2826701) B2826701
theorem B4235597 : Blo 1254445 4235597 := bstep (se 3 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 4235597 = 1588349) B1588349
theorem B1884497 : Blo 1254445 1884497 := bstep (se 2 (by rfl) ⟨706686, by rfl⟩ : syracuseStep 1884497 = 1413373) B1413373
theorem B1884515 : Blo 1254445 1884515 := bstep (se 1 (by rfl) ⟨1413386, by rfl⟩ : syracuseStep 1884515 = 2826773) B2826773
theorem B3178865 : Blo 1254445 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B1884545 : Blo 1254445 1884545 := bstep (se 2 (by rfl) ⟨706704, by rfl⟩ : syracuseStep 1884545 = 1413409) B1413409
theorem B4235651 : Blo 1254445 4235651 := bstep (se 1 (by rfl) ⟨3176738, by rfl⟩ : syracuseStep 4235651 = 6353477) B6353477
theorem B1589635 : Blo 1254445 1589635 := bstep (se 1 (by rfl) ⟨1192226, by rfl⟩ : syracuseStep 1589635 = 2384453) B2384453
theorem B1884563 : Blo 1254445 1884563 := bstep (se 1 (by rfl) ⟨1413422, by rfl⟩ : syracuseStep 1884563 = 2826845) B2826845
theorem B1884593 : Blo 1254445 1884593 := bstep (se 2 (by rfl) ⟨706722, by rfl⟩ : syracuseStep 1884593 = 1413445) B1413445
theorem B1884611 : Blo 1254445 1884611 := bstep (se 1 (by rfl) ⟨1413458, by rfl⟩ : syracuseStep 1884611 = 2826917) B2826917
theorem B1884641 : Blo 1254445 1884641 := bstep (se 2 (by rfl) ⟨706740, by rfl⟩ : syracuseStep 1884641 = 1413481) B1413481
theorem B16097777 : Blo 1254445 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B1720819 : Blo 1254445 1720819 := bstep (se 1 (by rfl) ⟨1290614, by rfl⟩ : syracuseStep 1720819 = 2581229) B2581229
theorem B2826737 : Blo 1254445 2826737 := bstep (se 2 (by rfl) ⟨1060026, by rfl⟩ : syracuseStep 2826737 = 2120053) B2120053
theorem B1884659 : Blo 1254445 1884659 := bstep (se 1 (by rfl) ⟨1413494, by rfl⟩ : syracuseStep 1884659 = 2826989) B2826989
theorem B1786369 : Blo 1254445 1786369 := bstep (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) B1339777
theorem B3392003 : Blo 1254445 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B2826755 : Blo 1254445 2826755 := bstep (se 1 (by rfl) ⟨2120066, by rfl⟩ : syracuseStep 2826755 = 4240133) B4240133
theorem B3572237 : Blo 1254445 3572237 := bstep (se 3 (by rfl) ⟨669794, by rfl⟩ : syracuseStep 3572237 = 1339589) B1339589
theorem B2679409 : Blo 1254445 2679409 := bstep (se 2 (by rfl) ⟨1004778, by rfl⟩ : syracuseStep 2679409 = 2009557) B2009557
theorem B1786483 : Blo 1254445 1786483 := bstep (se 1 (by rfl) ⟨1339862, by rfl⟩ : syracuseStep 1786483 = 2679725) B2679725
theorem B4235921 : Blo 1254445 4235921 := bstep (se 2 (by rfl) ⟨1588470, by rfl⟩ : syracuseStep 4235921 = 3176941) B3176941
theorem B3572419 : Blo 1254445 3572419 := bstep (se 1 (by rfl) ⟨2679314, by rfl⟩ : syracuseStep 3572419 = 5358629) B5358629
theorem B3220163 : Blo 1254445 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B3572579 : Blo 1254445 3572579 := bstep (se 1 (by rfl) ⟨2679434, by rfl⟩ : syracuseStep 3572579 = 5358869) B5358869
theorem B1590131 : Blo 1254445 1590131 := bstep (se 1 (by rfl) ⟨1192598, by rfl⟩ : syracuseStep 1590131 = 2385197) B2385197
theorem B3621763 : Blo 1254445 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B4768739 : Blo 1254445 4768739 := bstep (se 1 (by rfl) ⟨3576554, by rfl⟩ : syracuseStep 4768739 = 7153109) B7153109
theorem B4768753 : Blo 1254445 4768753 := bstep (se 2 (by rfl) ⟨1788282, by rfl⟩ : syracuseStep 4768753 = 3576565) B3576565
theorem B1254451 : Blo 1254445 1254451 := bstep (se 1 (by rfl) ⟨940838, by rfl⟩ : syracuseStep 1254451 = 1881677) B1881677
theorem B1254467 : Blo 1254445 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B1696835 : Blo 1254445 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B2384977 : Blo 1254445 2384977 := bstep (se 2 (by rfl) ⟨894366, by rfl⟩ : syracuseStep 2384977 = 1788733) B1788733
theorem B1254483 : Blo 1254445 1254483 := bstep (se 1 (by rfl) ⟨940862, by rfl⟩ : syracuseStep 1254483 = 1881725) B1881725
theorem B1254499 : Blo 1254445 1254499 := bstep (se 1 (by rfl) ⟨940874, by rfl⟩ : syracuseStep 1254499 = 1881749) B1881749
theorem B1254515 : Blo 1254445 1254515 := bstep (se 1 (by rfl) ⟨940886, by rfl⟩ : syracuseStep 1254515 = 1881773) B1881773
theorem B1254531 : Blo 1254445 1254531 := bstep (se 1 (by rfl) ⟨940898, by rfl⟩ : syracuseStep 1254531 = 1881797) B1881797
theorem B1254547 : Blo 1254445 1254547 := bstep (se 1 (by rfl) ⟨940910, by rfl⟩ : syracuseStep 1254547 = 1881821) B1881821
theorem B1254563 : Blo 1254445 1254563 := bstep (se 1 (by rfl) ⟨940922, by rfl⟩ : syracuseStep 1254563 = 1881845) B1881845
theorem B4236461 : Blo 1254445 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B6784177 : Blo 1254445 6784177 := bstep (se 2 (by rfl) ⟨2544066, by rfl⟩ : syracuseStep 6784177 = 5088133) B5088133
theorem B1254579 : Blo 1254445 1254579 := bstep (se 1 (by rfl) ⟨940934, by rfl⟩ : syracuseStep 1254579 = 1881869) B1881869
theorem B14304437 : Blo 1254445 14304437 := bstep (se 5 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 14304437 = 1341041) B1341041
theorem B1254595 : Blo 1254445 1254595 := bstep (se 1 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 1254595 = 1881893) B1881893
theorem B1254611 : Blo 1254445 1254611 := bstep (se 1 (by rfl) ⟨940958, by rfl⟩ : syracuseStep 1254611 = 1881917) B1881917
theorem B1254627 : Blo 1254445 1254627 := bstep (se 1 (by rfl) ⟨940970, by rfl⟩ : syracuseStep 1254627 = 1881941) B1881941
theorem B4236515 : Blo 1254445 4236515 := bstep (se 1 (by rfl) ⟨3177386, by rfl⟩ : syracuseStep 4236515 = 6354773) B6354773
theorem B1254643 : Blo 1254445 1254643 := bstep (se 1 (by rfl) ⟨940982, by rfl⟩ : syracuseStep 1254643 = 1881965) B1881965
theorem B1254659 : Blo 1254445 1254659 := bstep (se 1 (by rfl) ⟨940994, by rfl⟩ : syracuseStep 1254659 = 1881989) B1881989
theorem B2680067 : Blo 1254445 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B8045837 : Blo 1254445 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B1254675 : Blo 1254445 1254675 := bstep (se 1 (by rfl) ⟨941006, by rfl⟩ : syracuseStep 1254675 = 1882013) B1882013
theorem B1254691 : Blo 1254445 1254691 := bstep (se 1 (by rfl) ⟨941018, by rfl⟩ : syracuseStep 1254691 = 1882037) B1882037
theorem B6112547 : Blo 1254445 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B1254707 : Blo 1254445 1254707 := bstep (se 1 (by rfl) ⟨941030, by rfl⟩ : syracuseStep 1254707 = 1882061) B1882061
theorem B1254723 : Blo 1254445 1254723 := bstep (se 1 (by rfl) ⟨941042, by rfl⟩ : syracuseStep 1254723 = 1882085) B1882085
theorem B3179857 : Blo 1254445 3179857 := bstep (se 2 (by rfl) ⟨1192446, by rfl⟩ : syracuseStep 3179857 = 2384893) B2384893
theorem B1254739 : Blo 1254445 1254739 := bstep (se 1 (by rfl) ⟨941054, by rfl⟩ : syracuseStep 1254739 = 1882109) B1882109
theorem B1254755 : Blo 1254445 1254755 := bstep (se 1 (by rfl) ⟨941066, by rfl⟩ : syracuseStep 1254755 = 1882133) B1882133
theorem B1254771 : Blo 1254445 1254771 := bstep (se 1 (by rfl) ⟨941078, by rfl⟩ : syracuseStep 1254771 = 1882157) B1882157
theorem B1254787 : Blo 1254445 1254787 := bstep (se 1 (by rfl) ⟨941090, by rfl⟩ : syracuseStep 1254787 = 1882181) B1882181
theorem B1254803 : Blo 1254445 1254803 := bstep (se 1 (by rfl) ⟨941102, by rfl⟩ : syracuseStep 1254803 = 1882205) B1882205
theorem B1254819 : Blo 1254445 1254819 := bstep (se 1 (by rfl) ⟨941114, by rfl⟩ : syracuseStep 1254819 = 1882229) B1882229
theorem B1254835 : Blo 1254445 1254835 := bstep (se 1 (by rfl) ⟨941126, by rfl⟩ : syracuseStep 1254835 = 1882253) B1882253
theorem B1254851 : Blo 1254445 1254851 := bstep (se 1 (by rfl) ⟨941138, by rfl⟩ : syracuseStep 1254851 = 1882277) B1882277
theorem B1254867 : Blo 1254445 1254867 := bstep (se 1 (by rfl) ⟨941150, by rfl⟩ : syracuseStep 1254867 = 1882301) B1882301
theorem B1254883 : Blo 1254445 1254883 := bstep (se 1 (by rfl) ⟨941162, by rfl⟩ : syracuseStep 1254883 = 1882325) B1882325
theorem B6358499 : Blo 1254445 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B4236785 : Blo 1254445 4236785 := bstep (se 2 (by rfl) ⟨1588794, by rfl⟩ : syracuseStep 4236785 = 3177589) B3177589
theorem B1254899 : Blo 1254445 1254899 := bstep (se 1 (by rfl) ⟨941174, by rfl⟩ : syracuseStep 1254899 = 1882349) B1882349
theorem B1254915 : Blo 1254445 1254915 := bstep (se 1 (by rfl) ⟨941186, by rfl⟩ : syracuseStep 1254915 = 1882373) B1882373
theorem B2147843 : Blo 1254445 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B8037893 : Blo 1254445 8037893 := bstep (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) B1507105
theorem B7849477 : Blo 1254445 7849477 := bstep (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) B1471777
theorem B1254931 : Blo 1254445 1254931 := bstep (se 1 (by rfl) ⟨941198, by rfl⟩ : syracuseStep 1254931 = 1882397) B1882397
theorem B1254947 : Blo 1254445 1254947 := bstep (se 1 (by rfl) ⟨941210, by rfl⟩ : syracuseStep 1254947 = 1882421) B1882421
theorem B1254963 : Blo 1254445 1254963 := bstep (se 1 (by rfl) ⟨941222, by rfl⟩ : syracuseStep 1254963 = 1882445) B1882445
theorem B1254979 : Blo 1254445 1254979 := bstep (se 1 (by rfl) ⟨941234, by rfl⟩ : syracuseStep 1254979 = 1882469) B1882469
theorem B1254995 : Blo 1254445 1254995 := bstep (se 1 (by rfl) ⟨941246, by rfl⟩ : syracuseStep 1254995 = 1882493) B1882493
theorem B1255011 : Blo 1254445 1255011 := bstep (se 1 (by rfl) ⟨941258, by rfl⟩ : syracuseStep 1255011 = 1882517) B1882517
theorem B3180131 : Blo 1254445 3180131 := bstep (se 1 (by rfl) ⟨2385098, by rfl⟩ : syracuseStep 3180131 = 4770197) B4770197
theorem B1255027 : Blo 1254445 1255027 := bstep (se 1 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 1255027 = 1882541) B1882541
theorem B1255043 : Blo 1254445 1255043 := bstep (se 1 (by rfl) ⟨941282, by rfl⟩ : syracuseStep 1255043 = 1882565) B1882565
theorem B1255059 : Blo 1254445 1255059 := bstep (se 1 (by rfl) ⟨941294, by rfl⟩ : syracuseStep 1255059 = 1882589) B1882589
theorem B1255075 : Blo 1254445 1255075 := bstep (se 1 (by rfl) ⟨941306, by rfl⟩ : syracuseStep 1255075 = 1882613) B1882613
theorem B2262691 : Blo 1254445 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B1255091 : Blo 1254445 1255091 := bstep (se 1 (by rfl) ⟨941318, by rfl⟩ : syracuseStep 1255091 = 1882637) B1882637
theorem B1255107 : Blo 1254445 1255107 := bstep (se 1 (by rfl) ⟨941330, by rfl⟩ : syracuseStep 1255107 = 1882661) B1882661
theorem B2148049 : Blo 1254445 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1255123 : Blo 1254445 1255123 := bstep (se 1 (by rfl) ⟨941342, by rfl⟩ : syracuseStep 1255123 = 1882685) B1882685
theorem B1255139 : Blo 1254445 1255139 := bstep (se 1 (by rfl) ⟨941354, by rfl⟩ : syracuseStep 1255139 = 1882709) B1882709
theorem B1255155 : Blo 1254445 1255155 := bstep (se 1 (by rfl) ⟨941366, by rfl⟩ : syracuseStep 1255155 = 1882733) B1882733
theorem B1255171 : Blo 1254445 1255171 := bstep (se 1 (by rfl) ⟨941378, by rfl⟩ : syracuseStep 1255171 = 1882757) B1882757
theorem B1255187 : Blo 1254445 1255187 := bstep (se 1 (by rfl) ⟨941390, by rfl⟩ : syracuseStep 1255187 = 1882781) B1882781
theorem B1255203 : Blo 1254445 1255203 := bstep (se 1 (by rfl) ⟨941402, by rfl⟩ : syracuseStep 1255203 = 1882805) B1882805
theorem B3180323 : Blo 1254445 3180323 := bstep (se 1 (by rfl) ⟨2385242, by rfl⟩ : syracuseStep 3180323 = 4770485) B4770485
theorem B1255219 : Blo 1254445 1255219 := bstep (se 1 (by rfl) ⟨941414, by rfl⟩ : syracuseStep 1255219 = 1882829) B1882829
theorem B1255235 : Blo 1254445 1255235 := bstep (se 1 (by rfl) ⟨941426, by rfl⟩ : syracuseStep 1255235 = 1882853) B1882853
theorem B7145293 : Blo 1254445 7145293 := bstep (se 3 (by rfl) ⟨1339742, by rfl⟩ : syracuseStep 7145293 = 2679485) B2679485
theorem B1255251 : Blo 1254445 1255251 := bstep (se 1 (by rfl) ⟨941438, by rfl⟩ : syracuseStep 1255251 = 1882877) B1882877
theorem B1255267 : Blo 1254445 1255267 := bstep (se 1 (by rfl) ⟨941450, by rfl⟩ : syracuseStep 1255267 = 1882901) B1882901
theorem B1255283 : Blo 1254445 1255283 := bstep (se 1 (by rfl) ⟨941462, by rfl⟩ : syracuseStep 1255283 = 1882925) B1882925
theorem B1255299 : Blo 1254445 1255299 := bstep (se 1 (by rfl) ⟨941474, by rfl⟩ : syracuseStep 1255299 = 1882949) B1882949
theorem B7153541 : Blo 1254445 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B3573649 : Blo 1254445 3573649 := bstep (se 2 (by rfl) ⟨1340118, by rfl⟩ : syracuseStep 3573649 = 2680237) B2680237
theorem B1255315 : Blo 1254445 1255315 := bstep (se 1 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 1255315 = 1882973) B1882973
theorem B1255331 : Blo 1254445 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B1255347 : Blo 1254445 1255347 := bstep (se 1 (by rfl) ⟨941510, by rfl⟩ : syracuseStep 1255347 = 1883021) B1883021
theorem B1787827 : Blo 1254445 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B1255363 : Blo 1254445 1255363 := bstep (se 1 (by rfl) ⟨941522, by rfl⟩ : syracuseStep 1255363 = 1883045) B1883045
theorem B1255379 : Blo 1254445 1255379 := bstep (se 1 (by rfl) ⟨941534, by rfl⟩ : syracuseStep 1255379 = 1883069) B1883069
theorem B1255395 : Blo 1254445 1255395 := bstep (se 1 (by rfl) ⟨941546, by rfl⟩ : syracuseStep 1255395 = 1883093) B1883093
theorem B1255411 : Blo 1254445 1255411 := bstep (se 1 (by rfl) ⟨941558, by rfl⟩ : syracuseStep 1255411 = 1883117) B1883117
theorem B1255427 : Blo 1254445 1255427 := bstep (se 1 (by rfl) ⟨941570, by rfl⟩ : syracuseStep 1255427 = 1883141) B1883141
theorem B4237325 : Blo 1254445 4237325 := bstep (se 3 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 4237325 = 1588997) B1588997
theorem B1255443 : Blo 1254445 1255443 := bstep (se 1 (by rfl) ⟨941582, by rfl⟩ : syracuseStep 1255443 = 1883165) B1883165
theorem B1255459 : Blo 1254445 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1255475 : Blo 1254445 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1255491 : Blo 1254445 1255491 := bstep (se 1 (by rfl) ⟨941618, by rfl⟩ : syracuseStep 1255491 = 1883237) B1883237
theorem B4237379 : Blo 1254445 4237379 := bstep (se 1 (by rfl) ⟨3178034, by rfl⟩ : syracuseStep 4237379 = 6356069) B6356069
theorem B2680913 : Blo 1254445 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B1255507 : Blo 1254445 1255507 := bstep (se 1 (by rfl) ⟨941630, by rfl⟩ : syracuseStep 1255507 = 1883261) B1883261
theorem B1255523 : Blo 1254445 1255523 := bstep (se 1 (by rfl) ⟨941642, by rfl⟩ : syracuseStep 1255523 = 1883285) B1883285
theorem B2263153 : Blo 1254445 2263153 := bstep (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) B1697365
theorem B1255539 : Blo 1254445 1255539 := bstep (se 1 (by rfl) ⟨941654, by rfl⟩ : syracuseStep 1255539 = 1883309) B1883309
theorem B1255555 : Blo 1254445 1255555 := bstep (se 1 (by rfl) ⟨941666, by rfl⟩ : syracuseStep 1255555 = 1883333) B1883333
theorem B1255571 : Blo 1254445 1255571 := bstep (se 1 (by rfl) ⟨941678, by rfl⟩ : syracuseStep 1255571 = 1883357) B1883357
theorem B1255587 : Blo 1254445 1255587 := bstep (se 1 (by rfl) ⟨941690, by rfl⟩ : syracuseStep 1255587 = 1883381) B1883381
theorem B1255603 : Blo 1254445 1255603 := bstep (se 1 (by rfl) ⟨941702, by rfl⟩ : syracuseStep 1255603 = 1883405) B1883405
theorem B1411267 : Blo 1254445 1411267 := bstep (se 1 (by rfl) ⟨1058450, by rfl⟩ : syracuseStep 1411267 = 2116901) B2116901
theorem B1255619 : Blo 1254445 1255619 := bstep (se 1 (by rfl) ⟨941714, by rfl⟩ : syracuseStep 1255619 = 1883429) B1883429
theorem B1255635 : Blo 1254445 1255635 := bstep (se 1 (by rfl) ⟨941726, by rfl⟩ : syracuseStep 1255635 = 1883453) B1883453
theorem B1255651 : Blo 1254445 1255651 := bstep (se 1 (by rfl) ⟨941738, by rfl⟩ : syracuseStep 1255651 = 1883477) B1883477
theorem B1255667 : Blo 1254445 1255667 := bstep (se 1 (by rfl) ⟨941750, by rfl⟩ : syracuseStep 1255667 = 1883501) B1883501
theorem B1255683 : Blo 1254445 1255683 := bstep (se 1 (by rfl) ⟨941762, by rfl⟩ : syracuseStep 1255683 = 1883525) B1883525
theorem B6359309 : Blo 1254445 6359309 := bstep (se 3 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 6359309 = 2384741) B2384741
theorem B1255699 : Blo 1254445 1255699 := bstep (se 1 (by rfl) ⟨941774, by rfl⟩ : syracuseStep 1255699 = 1883549) B1883549
theorem B1255715 : Blo 1254445 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B1255731 : Blo 1254445 1255731 := bstep (se 1 (by rfl) ⟨941798, by rfl⟩ : syracuseStep 1255731 = 1883597) B1883597
theorem B3017027 : Blo 1254445 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B1255747 : Blo 1254445 1255747 := bstep (se 1 (by rfl) ⟨941810, by rfl⟩ : syracuseStep 1255747 = 1883621) B1883621
theorem B4237649 : Blo 1254445 4237649 := bstep (se 2 (by rfl) ⟨1589118, by rfl⟩ : syracuseStep 4237649 = 3178237) B3178237
theorem B1411411 : Blo 1254445 1411411 := bstep (se 1 (by rfl) ⟨1058558, by rfl⟩ : syracuseStep 1411411 = 2117117) B2117117
theorem B1255763 : Blo 1254445 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1255779 : Blo 1254445 1255779 := bstep (se 1 (by rfl) ⟨941834, by rfl⟩ : syracuseStep 1255779 = 1883669) B1883669
theorem B3393905 : Blo 1254445 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B1255795 : Blo 1254445 1255795 := bstep (se 1 (by rfl) ⟨941846, by rfl⟩ : syracuseStep 1255795 = 1883693) B1883693
theorem B1255811 : Blo 1254445 1255811 := bstep (se 1 (by rfl) ⟨941858, by rfl⟩ : syracuseStep 1255811 = 1883717) B1883717
theorem B1255827 : Blo 1254445 1255827 := bstep (se 1 (by rfl) ⟨941870, by rfl⟩ : syracuseStep 1255827 = 1883741) B1883741
theorem B1255843 : Blo 1254445 1255843 := bstep (se 1 (by rfl) ⟨941882, by rfl⟩ : syracuseStep 1255843 = 1883765) B1883765
theorem B4770211 : Blo 1254445 4770211 := bstep (se 1 (by rfl) ⟨3577658, by rfl⟩ : syracuseStep 4770211 = 7155317) B7155317
theorem B1255859 : Blo 1254445 1255859 := bstep (se 1 (by rfl) ⟨941894, by rfl⟩ : syracuseStep 1255859 = 1883789) B1883789
theorem B1255875 : Blo 1254445 1255875 := bstep (se 1 (by rfl) ⟨941906, by rfl⟩ : syracuseStep 1255875 = 1883813) B1883813
theorem B6785477 : Blo 1254445 6785477 := bstep (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) B1272277
theorem B1255891 : Blo 1254445 1255891 := bstep (se 1 (by rfl) ⟨941918, by rfl⟩ : syracuseStep 1255891 = 1883837) B1883837
theorem B10717667 : Blo 1254445 10717667 := bstep (se 1 (by rfl) ⟨8038250, by rfl⟩ : syracuseStep 10717667 = 16076501) B16076501
theorem B1411555 : Blo 1254445 1411555 := bstep (se 1 (by rfl) ⟨1058666, by rfl⟩ : syracuseStep 1411555 = 2117333) B2117333
theorem B1255907 : Blo 1254445 1255907 := bstep (se 1 (by rfl) ⟨941930, by rfl⟩ : syracuseStep 1255907 = 1883861) B1883861
theorem B1255923 : Blo 1254445 1255923 := bstep (se 1 (by rfl) ⟨941942, by rfl⟩ : syracuseStep 1255923 = 1883885) B1883885
theorem B1255939 : Blo 1254445 1255939 := bstep (se 1 (by rfl) ⟨941954, by rfl⟩ : syracuseStep 1255939 = 1883909) B1883909
theorem B1255955 : Blo 1254445 1255955 := bstep (se 1 (by rfl) ⟨941966, by rfl⟩ : syracuseStep 1255955 = 1883933) B1883933
theorem B1255971 : Blo 1254445 1255971 := bstep (se 1 (by rfl) ⟨941978, by rfl⟩ : syracuseStep 1255971 = 1883957) B1883957
theorem B1255987 : Blo 1254445 1255987 := bstep (se 1 (by rfl) ⟨941990, by rfl⟩ : syracuseStep 1255987 = 1883981) B1883981
theorem B1256003 : Blo 1254445 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B1256019 : Blo 1254445 1256019 := bstep (se 1 (by rfl) ⟨942014, by rfl⟩ : syracuseStep 1256019 = 1884029) B1884029
theorem B1256035 : Blo 1254445 1256035 := bstep (se 1 (by rfl) ⟨942026, by rfl⟩ : syracuseStep 1256035 = 1884053) B1884053
theorem B1411699 : Blo 1254445 1411699 := bstep (se 1 (by rfl) ⟨1058774, by rfl⟩ : syracuseStep 1411699 = 2117549) B2117549
theorem B1256051 : Blo 1254445 1256051 := bstep (se 1 (by rfl) ⟨942038, by rfl⟩ : syracuseStep 1256051 = 1884077) B1884077
theorem B1256067 : Blo 1254445 1256067 := bstep (se 1 (by rfl) ⟨942050, by rfl⟩ : syracuseStep 1256067 = 1884101) B1884101
theorem B5360269 : Blo 1254445 5360269 := bstep (se 3 (by rfl) ⟨1005050, by rfl⟩ : syracuseStep 5360269 = 2010101) B2010101
theorem B1256083 : Blo 1254445 1256083 := bstep (se 1 (by rfl) ⟨942062, by rfl⟩ : syracuseStep 1256083 = 1884125) B1884125
theorem B1256099 : Blo 1254445 1256099 := bstep (se 1 (by rfl) ⟨942074, by rfl⟩ : syracuseStep 1256099 = 1884149) B1884149
theorem B1256115 : Blo 1254445 1256115 := bstep (se 1 (by rfl) ⟨942086, by rfl⟩ : syracuseStep 1256115 = 1884173) B1884173
theorem B1256131 : Blo 1254445 1256131 := bstep (se 1 (by rfl) ⟨942098, by rfl⟩ : syracuseStep 1256131 = 1884197) B1884197
theorem B1256147 : Blo 1254445 1256147 := bstep (se 1 (by rfl) ⟨942110, by rfl⟩ : syracuseStep 1256147 = 1884221) B1884221
theorem B1256163 : Blo 1254445 1256163 := bstep (se 1 (by rfl) ⟨942122, by rfl⟩ : syracuseStep 1256163 = 1884245) B1884245
theorem B1256179 : Blo 1254445 1256179 := bstep (se 1 (by rfl) ⟨942134, by rfl⟩ : syracuseStep 1256179 = 1884269) B1884269
theorem B1411843 : Blo 1254445 1411843 := bstep (se 1 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 1411843 = 2117765) B2117765
theorem B1256195 : Blo 1254445 1256195 := bstep (se 1 (by rfl) ⟨942146, by rfl⟩ : syracuseStep 1256195 = 1884293) B1884293
theorem B1256211 : Blo 1254445 1256211 := bstep (se 1 (by rfl) ⟨942158, by rfl⟩ : syracuseStep 1256211 = 1884317) B1884317
theorem B1256227 : Blo 1254445 1256227 := bstep (se 1 (by rfl) ⟨942170, by rfl⟩ : syracuseStep 1256227 = 1884341) B1884341
theorem B4025123 : Blo 1254445 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B1256243 : Blo 1254445 1256243 := bstep (se 1 (by rfl) ⟨942182, by rfl⟩ : syracuseStep 1256243 = 1884365) B1884365
theorem B1256259 : Blo 1254445 1256259 := bstep (se 1 (by rfl) ⟨942194, by rfl⟩ : syracuseStep 1256259 = 1884389) B1884389
theorem B1256275 : Blo 1254445 1256275 := bstep (se 1 (by rfl) ⟨942206, by rfl⟩ : syracuseStep 1256275 = 1884413) B1884413
theorem B1256291 : Blo 1254445 1256291 := bstep (se 1 (by rfl) ⟨942218, by rfl⟩ : syracuseStep 1256291 = 1884437) B1884437
theorem B4238189 : Blo 1254445 4238189 := bstep (se 3 (by rfl) ⟨794660, by rfl⟩ : syracuseStep 4238189 = 1589321) B1589321
theorem B1256307 : Blo 1254445 1256307 := bstep (se 1 (by rfl) ⟨942230, by rfl⟩ : syracuseStep 1256307 = 1884461) B1884461
theorem B1256323 : Blo 1254445 1256323 := bstep (se 1 (by rfl) ⟨942242, by rfl⟩ : syracuseStep 1256323 = 1884485) B1884485
theorem B1411987 : Blo 1254445 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B1256339 : Blo 1254445 1256339 := bstep (se 1 (by rfl) ⟨942254, by rfl⟩ : syracuseStep 1256339 = 1884509) B1884509
theorem B4238243 : Blo 1254445 4238243 := bstep (se 1 (by rfl) ⟨3178682, by rfl⟩ : syracuseStep 4238243 = 6357365) B6357365
theorem B1256355 : Blo 1254445 1256355 := bstep (se 1 (by rfl) ⟨942266, by rfl⟩ : syracuseStep 1256355 = 1884533) B1884533
theorem B1256371 : Blo 1254445 1256371 := bstep (se 1 (by rfl) ⟨942278, by rfl⟩ : syracuseStep 1256371 = 1884557) B1884557
theorem B1256387 : Blo 1254445 1256387 := bstep (se 1 (by rfl) ⟨942290, by rfl⟩ : syracuseStep 1256387 = 1884581) B1884581
theorem B1256403 : Blo 1254445 1256403 := bstep (se 1 (by rfl) ⟨942302, by rfl⟩ : syracuseStep 1256403 = 1884605) B1884605
theorem B1256419 : Blo 1254445 1256419 := bstep (se 1 (by rfl) ⟨942314, by rfl⟩ : syracuseStep 1256419 = 1884629) B1884629
theorem B6351857 : Blo 1254445 6351857 := bstep (se 2 (by rfl) ⟨2381946, by rfl⟩ : syracuseStep 6351857 = 4763893) B4763893
theorem B1256435 : Blo 1254445 1256435 := bstep (se 1 (by rfl) ⟨942326, by rfl⟩ : syracuseStep 1256435 = 1884653) B1884653
theorem B1788961 : Blo 1254445 1788961 := bstep (se 2 (by rfl) ⟨670860, by rfl⟩ : syracuseStep 1788961 = 1341721) B1341721
theorem B1412131 : Blo 1254445 1412131 := bstep (se 1 (by rfl) ⟨1059098, by rfl⟩ : syracuseStep 1412131 = 2118197) B2118197
theorem B3574925 : Blo 1254445 3574925 := bstep (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) B1340597
theorem B3017873 : Blo 1254445 3017873 := bstep (se 2 (by rfl) ⟨1131702, by rfl⟩ : syracuseStep 3017873 = 2263405) B2263405
theorem B2010275 : Blo 1254445 2010275 := bstep (se 1 (by rfl) ⟨1507706, by rfl⟩ : syracuseStep 2010275 = 3015413) B3015413
theorem B4238513 : Blo 1254445 4238513 := bstep (se 2 (by rfl) ⟨1589442, by rfl⟩ : syracuseStep 4238513 = 3178885) B3178885
theorem B1412275 : Blo 1254445 1412275 := bstep (se 1 (by rfl) ⟨1059206, by rfl⟩ : syracuseStep 1412275 = 2118413) B2118413
theorem B3575107 : Blo 1254445 3575107 := bstep (se 1 (by rfl) ⟨2681330, by rfl⟩ : syracuseStep 3575107 = 5362661) B5362661
theorem B1412419 : Blo 1254445 1412419 := bstep (se 1 (by rfl) ⟨1059314, by rfl⟩ : syracuseStep 1412419 = 2118629) B2118629
theorem B3575153 : Blo 1254445 3575153 := bstep (se 2 (by rfl) ⟨1340682, by rfl⟩ : syracuseStep 3575153 = 2681365) B2681365
theorem B2117009 : Blo 1254445 2117009 := bstep (se 2 (by rfl) ⟨793878, by rfl⟩ : syracuseStep 2117009 = 1587757) B1587757
theorem B8048069 : Blo 1254445 8048069 := bstep (se 4 (by rfl) ⟨754506, by rfl⟩ : syracuseStep 8048069 = 1509013) B1509013
theorem B1412563 : Blo 1254445 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B1273315 : Blo 1254445 1273315 := bstep (se 1 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 1273315 = 1909973) B1909973
theorem B4525553 : Blo 1254445 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B1273331 : Blo 1254445 1273331 := bstep (se 1 (by rfl) ⟨954998, by rfl⟩ : syracuseStep 1273331 = 1909997) B1909997
theorem B17190413 : Blo 1254445 17190413 := bstep (se 3 (by rfl) ⟨3223202, by rfl⟩ : syracuseStep 17190413 = 6446405) B6446405
theorem B2117137 : Blo 1254445 2117137 := bstep (se 2 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 2117137 = 1587853) B1587853
theorem B4132387 : Blo 1254445 4132387 := bstep (se 1 (by rfl) ⟨3099290, by rfl⟩ : syracuseStep 4132387 = 6198581) B6198581
theorem B2117171 : Blo 1254445 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B2862659 : Blo 1254445 2862659 := bstep (se 1 (by rfl) ⟨2146994, by rfl⟩ : syracuseStep 2862659 = 4293989) B4293989
theorem B1412707 : Blo 1254445 1412707 := bstep (se 1 (by rfl) ⟨1059530, by rfl⟩ : syracuseStep 1412707 = 2119061) B2119061
theorem B1961635 : Blo 1254445 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B5361329 : Blo 1254445 5361329 := bstep (se 2 (by rfl) ⟨2010498, by rfl⟩ : syracuseStep 5361329 = 4020997) B4020997
theorem B2117299 : Blo 1254445 2117299 := bstep (se 1 (by rfl) ⟨1587974, by rfl⟩ : syracuseStep 2117299 = 3175949) B3175949
theorem B4296397 : Blo 1254445 4296397 := bstep (se 3 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 4296397 = 1611149) B1611149
theorem B4239053 : Blo 1254445 4239053 := bstep (se 3 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 4239053 = 1589645) B1589645
theorem B2682595 : Blo 1254445 2682595 := bstep (se 1 (by rfl) ⟨2011946, by rfl⟩ : syracuseStep 2682595 = 4023893) B4023893
theorem B1412851 : Blo 1254445 1412851 := bstep (se 1 (by rfl) ⟨1059638, by rfl⟩ : syracuseStep 1412851 = 2119277) B2119277
theorem B4239107 : Blo 1254445 4239107 := bstep (se 1 (by rfl) ⟨3179330, by rfl⟩ : syracuseStep 4239107 = 6358661) B6358661
theorem B7147277 : Blo 1254445 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B2117441 : Blo 1254445 2117441 := bstep (se 2 (by rfl) ⟨794040, by rfl⟩ : syracuseStep 2117441 = 1588081) B1588081
theorem B6786929 : Blo 1254445 6786929 := bstep (se 2 (by rfl) ⟨2545098, by rfl⟩ : syracuseStep 6786929 = 5090197) B5090197
theorem B1412995 : Blo 1254445 1412995 := bstep (se 1 (by rfl) ⟨1059746, by rfl⟩ : syracuseStep 1412995 = 2119493) B2119493
theorem B2117569 : Blo 1254445 2117569 := bstep (se 2 (by rfl) ⟨794088, by rfl⟩ : syracuseStep 2117569 = 1588177) B1588177
theorem B2117603 : Blo 1254445 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B6033379 : Blo 1254445 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B4239377 : Blo 1254445 4239377 := bstep (se 2 (by rfl) ⟨1589766, by rfl⟩ : syracuseStep 4239377 = 3179533) B3179533
theorem B1413139 : Blo 1254445 1413139 := bstep (se 1 (by rfl) ⟨1059854, by rfl⟩ : syracuseStep 1413139 = 2119709) B2119709
theorem B2117731 : Blo 1254445 2117731 := bstep (se 1 (by rfl) ⟨1588298, by rfl⟩ : syracuseStep 2117731 = 3176597) B3176597
theorem B13578353 : Blo 1254445 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1413283 : Blo 1254445 1413283 := bstep (se 1 (by rfl) ⟨1059962, by rfl⟩ : syracuseStep 1413283 = 2119925) B2119925
theorem B2683057 : Blo 1254445 2683057 := bstep (se 2 (by rfl) ⟨1006146, by rfl⟩ : syracuseStep 2683057 = 2012293) B2012293
theorem B2117873 : Blo 1254445 2117873 := bstep (se 2 (by rfl) ⟨794202, by rfl⟩ : syracuseStep 2117873 = 1588405) B1588405
theorem B6033649 : Blo 1254445 6033649 := bstep (se 2 (by rfl) ⟨2262618, by rfl⟩ : syracuseStep 6033649 = 4525237) B4525237
theorem B1413427 : Blo 1254445 1413427 := bstep (se 1 (by rfl) ⟨1060070, by rfl⟩ : syracuseStep 1413427 = 2120141) B2120141
theorem B1470803 : Blo 1254445 1470803 := bstep (se 1 (by rfl) ⟨1103102, by rfl⟩ : syracuseStep 1470803 = 2206205) B2206205
theorem B2118001 : Blo 1254445 2118001 := bstep (se 2 (by rfl) ⟨794250, by rfl⟩ : syracuseStep 2118001 = 1588501) B1588501
theorem B3723661 : Blo 1254445 3723661 := bstep (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) B1396373
theorem B2118035 : Blo 1254445 2118035 := bstep (se 1 (by rfl) ⟨1588526, by rfl⟩ : syracuseStep 2118035 = 3177053) B3177053
theorem B6353315 : Blo 1254445 6353315 := bstep (se 1 (by rfl) ⟨4764986, by rfl⟩ : syracuseStep 6353315 = 9529973) B9529973
theorem B9531917 : Blo 1254445 9531917 := bstep (se 3 (by rfl) ⟨1787234, by rfl⟩ : syracuseStep 9531917 = 3574469) B3574469
theorem B2118163 : Blo 1254445 2118163 := bstep (se 1 (by rfl) ⟨1588622, by rfl⟩ : syracuseStep 2118163 = 3177245) B3177245
theorem B4239917 : Blo 1254445 4239917 := bstep (se 3 (by rfl) ⟨794984, by rfl⟩ : syracuseStep 4239917 = 1589969) B1589969
theorem B2822705 : Blo 1254445 2822705 := bstep (se 2 (by rfl) ⟨1058514, by rfl⟩ : syracuseStep 2822705 = 2117029) B2117029
theorem B2822723 : Blo 1254445 2822723 := bstep (se 1 (by rfl) ⟨2117042, by rfl⟩ : syracuseStep 2822723 = 4234085) B4234085
theorem B2011729 : Blo 1254445 2011729 := bstep (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) B1508797
theorem B4239971 : Blo 1254445 4239971 := bstep (se 1 (by rfl) ⟨3179978, by rfl⟩ : syracuseStep 4239971 = 6359957) B6359957
theorem B2118305 : Blo 1254445 2118305 := bstep (se 2 (by rfl) ⟨794364, by rfl⟩ : syracuseStep 2118305 = 1588729) B1588729
theorem B7148209 : Blo 1254445 7148209 := bstep (se 2 (by rfl) ⟨2680578, by rfl⟩ : syracuseStep 7148209 = 5361157) B5361157
theorem B4297411 : Blo 1254445 4297411 := bstep (se 1 (by rfl) ⟨3223058, by rfl⟩ : syracuseStep 4297411 = 6446117) B6446117
theorem B4764365 : Blo 1254445 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B10187491 : Blo 1254445 10187491 := bstep (se 1 (by rfl) ⟨7640618, by rfl⟩ : syracuseStep 10187491 = 15281237) B15281237
theorem B2118433 : Blo 1254445 2118433 := bstep (se 2 (by rfl) ⟨794412, by rfl⟩ : syracuseStep 2118433 = 1588825) B1588825
theorem B3576611 : Blo 1254445 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2118467 : Blo 1254445 2118467 := bstep (se 1 (by rfl) ⟨1588850, by rfl⟩ : syracuseStep 2118467 = 3177701) B3177701
theorem B2822993 : Blo 1254445 2822993 := bstep (se 2 (by rfl) ⟨1058622, by rfl⟩ : syracuseStep 2822993 = 2117245) B2117245
theorem B2823011 : Blo 1254445 2823011 := bstep (se 1 (by rfl) ⟨2117258, by rfl⟩ : syracuseStep 2823011 = 4234517) B4234517
theorem B4240241 : Blo 1254445 4240241 := bstep (se 2 (by rfl) ⟨1590090, by rfl⟩ : syracuseStep 4240241 = 3180181) B3180181
theorem B2118595 : Blo 1254445 2118595 := bstep (se 1 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 2118595 = 3177893) B3177893
theorem B4527053 : Blo 1254445 4527053 := bstep (se 3 (by rfl) ⟨848822, by rfl⟩ : syracuseStep 4527053 = 1697645) B1697645
theorem B1340435 : Blo 1254445 1340435 := bstep (se 1 (by rfl) ⟨1005326, by rfl⟩ : syracuseStep 1340435 = 2010653) B2010653
theorem B2118737 : Blo 1254445 2118737 := bstep (se 2 (by rfl) ⟨794526, by rfl⟩ : syracuseStep 2118737 = 1589053) B1589053
theorem B2823281 : Blo 1254445 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B2823299 : Blo 1254445 2823299 := bstep (se 1 (by rfl) ⟨2117474, by rfl⟩ : syracuseStep 2823299 = 4234949) B4234949
theorem B6354125 : Blo 1254445 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B2118865 : Blo 1254445 2118865 := bstep (se 2 (by rfl) ⟨794574, by rfl⟩ : syracuseStep 2118865 = 1589149) B1589149
theorem B10188017 : Blo 1254445 10188017 := bstep (se 2 (by rfl) ⟨3820506, by rfl⟩ : syracuseStep 10188017 = 7641013) B7641013
theorem B2118899 : Blo 1254445 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B8041841 : Blo 1254445 8041841 := bstep (se 2 (by rfl) ⟨3015690, by rfl⟩ : syracuseStep 8041841 = 6031381) B6031381
theorem B2119027 : Blo 1254445 2119027 := bstep (se 1 (by rfl) ⟨1589270, by rfl⟩ : syracuseStep 2119027 = 3178541) B3178541
theorem B2823569 : Blo 1254445 2823569 := bstep (se 2 (by rfl) ⟨1058838, by rfl⟩ : syracuseStep 2823569 = 2117677) B2117677
theorem B2823587 : Blo 1254445 2823587 := bstep (se 1 (by rfl) ⟨2117690, by rfl⟩ : syracuseStep 2823587 = 4235381) B4235381
theorem B2414033 : Blo 1254445 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B4019665 : Blo 1254445 4019665 := bstep (se 2 (by rfl) ⟨1507374, by rfl⟩ : syracuseStep 4019665 = 3014749) B3014749
theorem B4765169 : Blo 1254445 4765169 := bstep (se 2 (by rfl) ⟨1786938, by rfl⟩ : syracuseStep 4765169 = 3573877) B3573877
theorem B2119169 : Blo 1254445 2119169 := bstep (se 2 (by rfl) ⟨794688, by rfl⟩ : syracuseStep 2119169 = 1589377) B1589377
theorem B1881683 : Blo 1254445 1881683 := bstep (se 1 (by rfl) ⟨1411262, by rfl⟩ : syracuseStep 1881683 = 2822525) B2822525
theorem B1881713 : Blo 1254445 1881713 := bstep (se 2 (by rfl) ⟨705642, by rfl⟩ : syracuseStep 1881713 = 1411285) B1411285
theorem B2119297 : Blo 1254445 2119297 := bstep (se 2 (by rfl) ⟨794736, by rfl⟩ : syracuseStep 2119297 = 1589473) B1589473
theorem B1881731 : Blo 1254445 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B4019843 : Blo 1254445 4019843 := bstep (se 1 (by rfl) ⟨3014882, by rfl⟩ : syracuseStep 4019843 = 6029765) B6029765
theorem B3176081 : Blo 1254445 3176081 := bstep (se 2 (by rfl) ⟨1191030, by rfl⟩ : syracuseStep 3176081 = 2382061) B2382061
theorem B1881761 : Blo 1254445 1881761 := bstep (se 2 (by rfl) ⟨705660, by rfl⟩ : syracuseStep 1881761 = 1411321) B1411321
theorem B2119331 : Blo 1254445 2119331 := bstep (se 1 (by rfl) ⟨1589498, by rfl⟩ : syracuseStep 2119331 = 3178997) B3178997
theorem B2823857 : Blo 1254445 2823857 := bstep (se 2 (by rfl) ⟨1058946, by rfl⟩ : syracuseStep 2823857 = 2117893) B2117893
theorem B1881779 : Blo 1254445 1881779 := bstep (se 1 (by rfl) ⟨1411334, by rfl⟩ : syracuseStep 1881779 = 2822669) B2822669
theorem B3176131 : Blo 1254445 3176131 := bstep (se 1 (by rfl) ⟨2382098, by rfl⟩ : syracuseStep 3176131 = 4764197) B4764197
theorem B2823875 : Blo 1254445 2823875 := bstep (se 1 (by rfl) ⟨2117906, by rfl⟩ : syracuseStep 2823875 = 4235813) B4235813
theorem B1881809 : Blo 1254445 1881809 := bstep (se 2 (by rfl) ⟨705678, by rfl⟩ : syracuseStep 1881809 = 1411357) B1411357
theorem B1881827 : Blo 1254445 1881827 := bstep (se 1 (by rfl) ⟨1411370, by rfl⟩ : syracuseStep 1881827 = 2822741) B2822741
theorem B1881857 : Blo 1254445 1881857 := bstep (se 2 (by rfl) ⟨705696, by rfl⟩ : syracuseStep 1881857 = 1411393) B1411393
theorem B1881875 : Blo 1254445 1881875 := bstep (se 1 (by rfl) ⟨1411406, by rfl⟩ : syracuseStep 1881875 = 2822813) B2822813
theorem B2119459 : Blo 1254445 2119459 := bstep (se 1 (by rfl) ⟨1589594, by rfl⟩ : syracuseStep 2119459 = 3179189) B3179189
theorem B1881905 : Blo 1254445 1881905 := bstep (se 2 (by rfl) ⟨705714, by rfl⟩ : syracuseStep 1881905 = 1411429) B1411429
theorem B1881923 : Blo 1254445 1881923 := bstep (se 1 (by rfl) ⟨1411442, by rfl⟩ : syracuseStep 1881923 = 2822885) B2822885
theorem B3176273 : Blo 1254445 3176273 := bstep (se 2 (by rfl) ⟨1191102, by rfl⟩ : syracuseStep 3176273 = 2382205) B2382205
theorem B1881953 : Blo 1254445 1881953 := bstep (se 2 (by rfl) ⟨705732, by rfl⟩ : syracuseStep 1881953 = 1411465) B1411465
theorem B1881971 : Blo 1254445 1881971 := bstep (se 1 (by rfl) ⟨1411478, by rfl⟩ : syracuseStep 1881971 = 2822957) B2822957
theorem B1882001 : Blo 1254445 1882001 := bstep (se 2 (by rfl) ⟨705750, by rfl⟩ : syracuseStep 1882001 = 1411501) B1411501
theorem B1882019 : Blo 1254445 1882019 := bstep (se 1 (by rfl) ⟨1411514, by rfl⟩ : syracuseStep 1882019 = 2823029) B2823029
theorem B4831139 : Blo 1254445 4831139 := bstep (se 1 (by rfl) ⟨3623354, by rfl⟩ : syracuseStep 4831139 = 7246709) B7246709
theorem B2119601 : Blo 1254445 2119601 := bstep (se 2 (by rfl) ⟨794850, by rfl⟩ : syracuseStep 2119601 = 1589701) B1589701
theorem B1882049 : Blo 1254445 1882049 := bstep (se 2 (by rfl) ⟨705768, by rfl⟩ : syracuseStep 1882049 = 1411537) B1411537
theorem B2824145 : Blo 1254445 2824145 := bstep (se 2 (by rfl) ⟨1059054, by rfl⟩ : syracuseStep 2824145 = 2118109) B2118109
theorem B1882067 : Blo 1254445 1882067 := bstep (se 1 (by rfl) ⟨1411550, by rfl⟩ : syracuseStep 1882067 = 2823101) B2823101
theorem B2381795 : Blo 1254445 2381795 := bstep (se 1 (by rfl) ⟨1786346, by rfl⟩ : syracuseStep 2381795 = 3572693) B3572693
theorem B2824163 : Blo 1254445 2824163 := bstep (se 1 (by rfl) ⟨2118122, by rfl⟩ : syracuseStep 2824163 = 4236245) B4236245
theorem B1882097 : Blo 1254445 1882097 := bstep (se 2 (by rfl) ⟨705786, by rfl⟩ : syracuseStep 1882097 = 1411573) B1411573
theorem B3577841 : Blo 1254445 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B1882115 : Blo 1254445 1882115 := bstep (se 1 (by rfl) ⟨1411586, by rfl⟩ : syracuseStep 1882115 = 2823173) B2823173
theorem B1882145 : Blo 1254445 1882145 := bstep (se 2 (by rfl) ⟨705804, by rfl⟩ : syracuseStep 1882145 = 1411609) B1411609
theorem B2119729 : Blo 1254445 2119729 := bstep (se 2 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 2119729 = 1589797) B1589797
theorem B1882163 : Blo 1254445 1882163 := bstep (se 1 (by rfl) ⟨1411622, by rfl⟩ : syracuseStep 1882163 = 2823245) B2823245
theorem B1882193 : Blo 1254445 1882193 := bstep (se 2 (by rfl) ⟨705822, by rfl⟩ : syracuseStep 1882193 = 1411645) B1411645
theorem B2119763 : Blo 1254445 2119763 := bstep (se 1 (by rfl) ⟨1589822, by rfl⟩ : syracuseStep 2119763 = 3179645) B3179645
theorem B1882211 : Blo 1254445 1882211 := bstep (se 1 (by rfl) ⟨1411658, by rfl⟩ : syracuseStep 1882211 = 2823317) B2823317
theorem B7149667 : Blo 1254445 7149667 := bstep (se 1 (by rfl) ⟨5362250, by rfl⟩ : syracuseStep 7149667 = 10724501) B10724501
theorem B1882241 : Blo 1254445 1882241 := bstep (se 2 (by rfl) ⟨705840, by rfl⟩ : syracuseStep 1882241 = 1411681) B1411681
theorem B1341571 : Blo 1254445 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B4765837 : Blo 1254445 4765837 := bstep (se 3 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 4765837 = 1787189) B1787189
theorem B1882259 : Blo 1254445 1882259 := bstep (se 1 (by rfl) ⟨1411694, by rfl⟩ : syracuseStep 1882259 = 2823389) B2823389
theorem B1882289 : Blo 1254445 1882289 := bstep (se 2 (by rfl) ⟨705858, by rfl⟩ : syracuseStep 1882289 = 1411717) B1411717
theorem B1882307 : Blo 1254445 1882307 := bstep (se 1 (by rfl) ⟨1411730, by rfl⟩ : syracuseStep 1882307 = 2823461) B2823461
theorem B2119891 : Blo 1254445 2119891 := bstep (se 1 (by rfl) ⟨1589918, by rfl⟩ : syracuseStep 2119891 = 3179837) B3179837
theorem B1882337 : Blo 1254445 1882337 := bstep (se 2 (by rfl) ⟨705876, by rfl⟩ : syracuseStep 1882337 = 1411753) B1411753
theorem B2824433 : Blo 1254445 2824433 := bstep (se 2 (by rfl) ⟨1059162, by rfl⟩ : syracuseStep 2824433 = 2118325) B2118325
theorem B1882355 : Blo 1254445 1882355 := bstep (se 1 (by rfl) ⟨1411766, by rfl⟩ : syracuseStep 1882355 = 2823533) B2823533
theorem B2824451 : Blo 1254445 2824451 := bstep (se 1 (by rfl) ⟨2118338, by rfl⟩ : syracuseStep 2824451 = 4236677) B4236677
theorem B1882385 : Blo 1254445 1882385 := bstep (se 2 (by rfl) ⟨705894, by rfl⟩ : syracuseStep 1882385 = 1411789) B1411789
theorem B48953621 : Blo 1254445 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B1882403 : Blo 1254445 1882403 := bstep (se 1 (by rfl) ⟨1411802, by rfl⟩ : syracuseStep 1882403 = 2823605) B2823605
theorem B1882433 : Blo 1254445 1882433 := bstep (se 2 (by rfl) ⟨705912, by rfl⟩ : syracuseStep 1882433 = 1411825) B1411825
theorem B4962637 : Blo 1254445 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1882451 : Blo 1254445 1882451 := bstep (se 1 (by rfl) ⟨1411838, by rfl⟩ : syracuseStep 1882451 = 2823677) B2823677
theorem B2120033 : Blo 1254445 2120033 := bstep (se 2 (by rfl) ⟨795012, by rfl⟩ : syracuseStep 2120033 = 1590025) B1590025
theorem B1882481 : Blo 1254445 1882481 := bstep (se 2 (by rfl) ⟨705930, by rfl⟩ : syracuseStep 1882481 = 1411861) B1411861
theorem B1882499 : Blo 1254445 1882499 := bstep (se 1 (by rfl) ⟨1411874, by rfl⟩ : syracuseStep 1882499 = 2823749) B2823749
theorem B1882529 : Blo 1254445 1882529 := bstep (se 2 (by rfl) ⟨705948, by rfl⟩ : syracuseStep 1882529 = 1411897) B1411897
theorem B1882547 : Blo 1254445 1882547 := bstep (se 1 (by rfl) ⟨1411910, by rfl⟩ : syracuseStep 1882547 = 2823821) B2823821
theorem B13752773 : Blo 1254445 13752773 := bstep (se 4 (by rfl) ⟨1289322, by rfl⟩ : syracuseStep 13752773 = 2578645) B2578645
theorem B1882577 : Blo 1254445 1882577 := bstep (se 2 (by rfl) ⟨705966, by rfl⟩ : syracuseStep 1882577 = 1411933) B1411933
theorem B2120161 : Blo 1254445 2120161 := bstep (se 2 (by rfl) ⟨795060, by rfl⟩ : syracuseStep 2120161 = 1590121) B1590121
theorem B1882595 : Blo 1254445 1882595 := bstep (se 1 (by rfl) ⟨1411946, by rfl⟩ : syracuseStep 1882595 = 2823893) B2823893
theorem B1882625 : Blo 1254445 1882625 := bstep (se 2 (by rfl) ⟨705984, by rfl⟩ : syracuseStep 1882625 = 1411969) B1411969
theorem B2120195 : Blo 1254445 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B11450893 : Blo 1254445 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B2824721 : Blo 1254445 2824721 := bstep (se 2 (by rfl) ⟨1059270, by rfl⟩ : syracuseStep 2824721 = 2118541) B2118541
theorem B1882643 : Blo 1254445 1882643 := bstep (se 1 (by rfl) ⟨1411982, by rfl⟩ : syracuseStep 1882643 = 2823965) B2823965
theorem B2824739 : Blo 1254445 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B1882673 : Blo 1254445 1882673 := bstep (se 2 (by rfl) ⟨706002, by rfl⟩ : syracuseStep 1882673 = 1412005) B1412005
theorem B1882691 : Blo 1254445 1882691 := bstep (se 1 (by rfl) ⟨1412018, by rfl⟩ : syracuseStep 1882691 = 2824037) B2824037
theorem B5364301 : Blo 1254445 5364301 := bstep (se 3 (by rfl) ⟨1005806, by rfl⟩ : syracuseStep 5364301 = 2011613) B2011613
theorem B2415185 : Blo 1254445 2415185 := bstep (se 2 (by rfl) ⟨905694, by rfl⟩ : syracuseStep 2415185 = 1811389) B1811389
theorem B1882721 : Blo 1254445 1882721 := bstep (se 2 (by rfl) ⟨706020, by rfl⟩ : syracuseStep 1882721 = 1412041) B1412041
theorem B7150193 : Blo 1254445 7150193 := bstep (se 2 (by rfl) ⟨2681322, by rfl⟩ : syracuseStep 7150193 = 5362645) B5362645
theorem B1882739 : Blo 1254445 1882739 := bstep (se 1 (by rfl) ⟨1412054, by rfl⟩ : syracuseStep 1882739 = 2824109) B2824109
theorem B4233869 : Blo 1254445 4233869 := bstep (se 3 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 4233869 = 1587701) B1587701
theorem B1882769 : Blo 1254445 1882769 := bstep (se 2 (by rfl) ⟨706038, by rfl⟩ : syracuseStep 1882769 = 1412077) B1412077
theorem B1882787 : Blo 1254445 1882787 := bstep (se 1 (by rfl) ⟨1412090, by rfl⟩ : syracuseStep 1882787 = 2824181) B2824181
theorem B1882817 : Blo 1254445 1882817 := bstep (se 2 (by rfl) ⟨706056, by rfl⟩ : syracuseStep 1882817 = 1412113) B1412113
theorem B4233923 : Blo 1254445 4233923 := bstep (se 1 (by rfl) ⟨3175442, by rfl⟩ : syracuseStep 4233923 = 6350885) B6350885
theorem B1882835 : Blo 1254445 1882835 := bstep (se 1 (by rfl) ⟨1412126, by rfl⟩ : syracuseStep 1882835 = 2824253) B2824253
theorem B1882865 : Blo 1254445 1882865 := bstep (se 2 (by rfl) ⟨706074, by rfl⟩ : syracuseStep 1882865 = 1412149) B1412149
theorem B1882883 : Blo 1254445 1882883 := bstep (se 1 (by rfl) ⟨1412162, by rfl⟩ : syracuseStep 1882883 = 2824325) B2824325
theorem B1882913 : Blo 1254445 1882913 := bstep (se 2 (by rfl) ⟨706092, by rfl⟩ : syracuseStep 1882913 = 1412185) B1412185
theorem B3177265 : Blo 1254445 3177265 := bstep (se 2 (by rfl) ⟨1191474, by rfl⟩ : syracuseStep 3177265 = 2382949) B2382949
theorem B2825009 : Blo 1254445 2825009 := bstep (se 2 (by rfl) ⟨1059378, by rfl⟩ : syracuseStep 2825009 = 2118757) B2118757
theorem B1882931 : Blo 1254445 1882931 := bstep (se 1 (by rfl) ⟨1412198, by rfl⟩ : syracuseStep 1882931 = 2824397) B2824397
theorem B15276853 : Blo 1254445 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B2825027 : Blo 1254445 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B9526085 : Blo 1254445 9526085 := bstep (se 4 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 9526085 = 1786141) B1786141
theorem B1882961 : Blo 1254445 1882961 := bstep (se 2 (by rfl) ⟨706110, by rfl⟩ : syracuseStep 1882961 = 1412221) B1412221
theorem B2382691 : Blo 1254445 2382691 := bstep (se 1 (by rfl) ⟨1787018, by rfl⟩ : syracuseStep 2382691 = 3574037) B3574037
theorem B1882979 : Blo 1254445 1882979 := bstep (se 1 (by rfl) ⟨1412234, by rfl⟩ : syracuseStep 1882979 = 2824469) B2824469
theorem B1883009 : Blo 1254445 1883009 := bstep (se 2 (by rfl) ⟨706128, by rfl⟩ : syracuseStep 1883009 = 1412257) B1412257
theorem B1883027 : Blo 1254445 1883027 := bstep (se 1 (by rfl) ⟨1412270, by rfl⟩ : syracuseStep 1883027 = 2824541) B2824541
theorem B4766627 : Blo 1254445 4766627 := bstep (se 1 (by rfl) ⟨3574970, by rfl⟩ : syracuseStep 4766627 = 7149941) B7149941
theorem B5364643 : Blo 1254445 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B1883057 : Blo 1254445 1883057 := bstep (se 2 (by rfl) ⟨706146, by rfl⟩ : syracuseStep 1883057 = 1412293) B1412293
theorem B1883075 : Blo 1254445 1883075 := bstep (se 1 (by rfl) ⟨1412306, by rfl⟩ : syracuseStep 1883075 = 2824613) B2824613
theorem B4234193 : Blo 1254445 4234193 := bstep (se 2 (by rfl) ⟨1587822, by rfl⟩ : syracuseStep 4234193 = 3175645) B3175645
theorem B1883105 : Blo 1254445 1883105 := bstep (se 2 (by rfl) ⟨706164, by rfl⟩ : syracuseStep 1883105 = 1412329) B1412329
theorem B1358819 : Blo 1254445 1358819 := bstep (se 1 (by rfl) ⟨1019114, by rfl⟩ : syracuseStep 1358819 = 2038229) B2038229
theorem B1883123 : Blo 1254445 1883123 := bstep (se 1 (by rfl) ⟨1412342, by rfl⟩ : syracuseStep 1883123 = 2824685) B2824685
theorem B2382851 : Blo 1254445 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1883153 : Blo 1254445 1883153 := bstep (se 2 (by rfl) ⟨706182, by rfl⟩ : syracuseStep 1883153 = 1412365) B1412365
theorem B1588243 : Blo 1254445 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B1883171 : Blo 1254445 1883171 := bstep (se 1 (by rfl) ⟨1412378, by rfl⟩ : syracuseStep 1883171 = 2824757) B2824757
theorem B6036515 : Blo 1254445 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B1883201 : Blo 1254445 1883201 := bstep (se 2 (by rfl) ⟨706200, by rfl⟩ : syracuseStep 1883201 = 1412401) B1412401
theorem B3177539 : Blo 1254445 3177539 := bstep (se 1 (by rfl) ⟨2383154, by rfl⟩ : syracuseStep 3177539 = 4766309) B4766309
theorem B9657413 : Blo 1254445 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B2825297 : Blo 1254445 2825297 := bstep (se 2 (by rfl) ⟨1059486, by rfl⟩ : syracuseStep 2825297 = 2118973) B2118973
theorem B1883219 : Blo 1254445 1883219 := bstep (se 1 (by rfl) ⟨1412414, by rfl⟩ : syracuseStep 1883219 = 2824829) B2824829
theorem B2825315 : Blo 1254445 2825315 := bstep (se 1 (by rfl) ⟨2118986, by rfl⟩ : syracuseStep 2825315 = 4237973) B4237973
theorem B1883249 : Blo 1254445 1883249 := bstep (se 2 (by rfl) ⟨706218, by rfl⟩ : syracuseStep 1883249 = 1412437) B1412437
theorem B1588339 : Blo 1254445 1588339 := bstep (se 1 (by rfl) ⟨1191254, by rfl⟩ : syracuseStep 1588339 = 2382509) B2382509
theorem B1883267 : Blo 1254445 1883267 := bstep (se 1 (by rfl) ⟨1412450, by rfl⟩ : syracuseStep 1883267 = 2824901) B2824901
theorem B1883297 : Blo 1254445 1883297 := bstep (se 2 (by rfl) ⟨706236, by rfl⟩ : syracuseStep 1883297 = 1412473) B1412473
theorem B1883315 : Blo 1254445 1883315 := bstep (se 1 (by rfl) ⟨1412486, by rfl⟩ : syracuseStep 1883315 = 2824973) B2824973
theorem B4586701 : Blo 1254445 4586701 := bstep (se 3 (by rfl) ⟨860006, by rfl⟩ : syracuseStep 4586701 = 1720013) B1720013
theorem B1883345 : Blo 1254445 1883345 := bstep (se 2 (by rfl) ⟨706254, by rfl⟩ : syracuseStep 1883345 = 1412509) B1412509
theorem B1883363 : Blo 1254445 1883363 := bstep (se 1 (by rfl) ⟨1412522, by rfl⟩ : syracuseStep 1883363 = 2825045) B2825045
theorem B1883393 : Blo 1254445 1883393 := bstep (se 2 (by rfl) ⟨706272, by rfl⟩ : syracuseStep 1883393 = 1412545) B1412545
theorem B3177731 : Blo 1254445 3177731 := bstep (se 1 (by rfl) ⟨2383298, by rfl⟩ : syracuseStep 3177731 = 4766597) B4766597
theorem B6790405 : Blo 1254445 6790405 := bstep (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) B1273201
theorem B1883411 : Blo 1254445 1883411 := bstep (se 1 (by rfl) ⟨1412558, by rfl⟩ : syracuseStep 1883411 = 2825117) B2825117
theorem B1883441 : Blo 1254445 1883441 := bstep (se 2 (by rfl) ⟨706290, by rfl⟩ : syracuseStep 1883441 = 1412581) B1412581
theorem B1883459 : Blo 1254445 1883459 := bstep (se 1 (by rfl) ⟨1412594, by rfl⟩ : syracuseStep 1883459 = 2825189) B2825189
theorem B3439949 : Blo 1254445 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B1883489 : Blo 1254445 1883489 := bstep (se 2 (by rfl) ⟨706308, by rfl⟩ : syracuseStep 1883489 = 1412617) B1412617
theorem B4021613 : Blo 1254445 4021613 := bstep (se 3 (by rfl) ⟨754052, by rfl⟩ : syracuseStep 4021613 = 1508105) B1508105
theorem B5086577 : Blo 1254445 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B9534833 : Blo 1254445 9534833 := bstep (se 2 (by rfl) ⟨3575562, by rfl⟩ : syracuseStep 9534833 = 7151125) B7151125
theorem B1883507 : Blo 1254445 1883507 := bstep (se 1 (by rfl) ⟨1412630, by rfl⟩ : syracuseStep 1883507 = 2825261) B2825261
theorem B2825585 : Blo 1254445 2825585 := bstep (se 2 (by rfl) ⟨1059594, by rfl⟩ : syracuseStep 2825585 = 2119189) B2119189
theorem B2825603 : Blo 1254445 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B1883537 : Blo 1254445 1883537 := bstep (se 2 (by rfl) ⟨706326, by rfl⟩ : syracuseStep 1883537 = 1412653) B1412653
theorem B1883555 : Blo 1254445 1883555 := bstep (se 1 (by rfl) ⟨1412666, by rfl⟩ : syracuseStep 1883555 = 2825333) B2825333
theorem B1883585 : Blo 1254445 1883585 := bstep (se 2 (by rfl) ⟨706344, by rfl⟩ : syracuseStep 1883585 = 1412689) B1412689
theorem B1883603 : Blo 1254445 1883603 := bstep (se 1 (by rfl) ⟨1412702, by rfl⟩ : syracuseStep 1883603 = 2825405) B2825405
theorem B4234733 : Blo 1254445 4234733 := bstep (se 3 (by rfl) ⟨794012, by rfl⟩ : syracuseStep 4234733 = 1588025) B1588025
theorem B1908209 : Blo 1254445 1908209 := bstep (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) B1431157
theorem B1883633 : Blo 1254445 1883633 := bstep (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) B1412725
theorem B1883651 : Blo 1254445 1883651 := bstep (se 1 (by rfl) ⟨1412738, by rfl⟩ : syracuseStep 1883651 = 2825477) B2825477
theorem B1883681 : Blo 1254445 1883681 := bstep (se 2 (by rfl) ⟨706380, by rfl⟩ : syracuseStep 1883681 = 1412761) B1412761
theorem B4234787 : Blo 1254445 4234787 := bstep (se 1 (by rfl) ⟨3176090, by rfl⟩ : syracuseStep 4234787 = 6352181) B6352181
theorem B4767281 : Blo 1254445 4767281 := bstep (se 2 (by rfl) ⟨1787730, by rfl⟩ : syracuseStep 4767281 = 3575461) B3575461
theorem B1883699 : Blo 1254445 1883699 := bstep (se 1 (by rfl) ⟨1412774, by rfl⟩ : syracuseStep 1883699 = 2825549) B2825549
theorem B1908289 : Blo 1254445 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B1883729 : Blo 1254445 1883729 := bstep (se 2 (by rfl) ⟨706398, by rfl⟩ : syracuseStep 1883729 = 1412797) B1412797
theorem B1359443 : Blo 1254445 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B1588835 : Blo 1254445 1588835 := bstep (se 1 (by rfl) ⟨1191626, by rfl⟩ : syracuseStep 1588835 = 2383253) B2383253
theorem B1883747 : Blo 1254445 1883747 := bstep (se 1 (by rfl) ⟨1412810, by rfl⟩ : syracuseStep 1883747 = 2825621) B2825621
theorem B1883777 : Blo 1254445 1883777 := bstep (se 2 (by rfl) ⟨706416, by rfl⟩ : syracuseStep 1883777 = 1412833) B1412833
theorem B4292227 : Blo 1254445 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B2825873 : Blo 1254445 2825873 := bstep (se 2 (by rfl) ⟨1059702, by rfl⟩ : syracuseStep 2825873 = 2119405) B2119405
theorem B1883795 : Blo 1254445 1883795 := bstep (se 1 (by rfl) ⟨1412846, by rfl⟩ : syracuseStep 1883795 = 2825693) B2825693
theorem B2825891 : Blo 1254445 2825891 := bstep (se 1 (by rfl) ⟨2119418, by rfl⟩ : syracuseStep 2825891 = 4238837) B4238837
theorem B2449073 : Blo 1254445 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B1883825 : Blo 1254445 1883825 := bstep (se 2 (by rfl) ⟨706434, by rfl⟩ : syracuseStep 1883825 = 1412869) B1412869
theorem B1883843 : Blo 1254445 1883843 := bstep (se 1 (by rfl) ⟨1412882, by rfl⟩ : syracuseStep 1883843 = 2825765) B2825765
theorem B1883873 : Blo 1254445 1883873 := bstep (se 2 (by rfl) ⟨706452, by rfl⟩ : syracuseStep 1883873 = 1412905) B1412905
theorem B1883891 : Blo 1254445 1883891 := bstep (se 1 (by rfl) ⟨1412918, by rfl⟩ : syracuseStep 1883891 = 2825837) B2825837
theorem B2039555 : Blo 1254445 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B1883921 : Blo 1254445 1883921 := bstep (se 2 (by rfl) ⟨706470, by rfl⟩ : syracuseStep 1883921 = 1412941) B1412941
theorem B1507091 : Blo 1254445 1507091 := bstep (se 1 (by rfl) ⟨1130318, by rfl⟩ : syracuseStep 1507091 = 2260637) B2260637
theorem B1883939 : Blo 1254445 1883939 := bstep (se 1 (by rfl) ⟨1412954, by rfl⟩ : syracuseStep 1883939 = 2825909) B2825909
theorem B4235057 : Blo 1254445 4235057 := bstep (se 2 (by rfl) ⟨1588146, by rfl⟩ : syracuseStep 4235057 = 3176293) B3176293
theorem B6446897 : Blo 1254445 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B1883969 : Blo 1254445 1883969 := bstep (se 2 (by rfl) ⟨706488, by rfl⟩ : syracuseStep 1883969 = 1412977) B1412977
theorem B1883987 : Blo 1254445 1883987 := bstep (se 1 (by rfl) ⟨1412990, by rfl⟩ : syracuseStep 1883987 = 2825981) B2825981
theorem B1884017 : Blo 1254445 1884017 := bstep (se 2 (by rfl) ⟨706506, by rfl⟩ : syracuseStep 1884017 = 1413013) B1413013
theorem B1908611 : Blo 1254445 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B1884035 : Blo 1254445 1884035 := bstep (se 1 (by rfl) ⟨1413026, by rfl⟩ : syracuseStep 1884035 = 2826053) B2826053
theorem B1884065 : Blo 1254445 1884065 := bstep (se 2 (by rfl) ⟨706524, by rfl⟩ : syracuseStep 1884065 = 1413049) B1413049
theorem B1695667 : Blo 1254445 1695667 := bstep (se 1 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 1695667 = 2543501) B2543501
theorem B1884083 : Blo 1254445 1884083 := bstep (se 1 (by rfl) ⟨1413062, by rfl⟩ : syracuseStep 1884083 = 2826125) B2826125
theorem B2826161 : Blo 1254445 2826161 := bstep (se 2 (by rfl) ⟨1059810, by rfl⟩ : syracuseStep 2826161 = 2119621) B2119621
theorem B2260931 : Blo 1254445 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B2826179 : Blo 1254445 2826179 := bstep (se 1 (by rfl) ⟨2119634, by rfl⟩ : syracuseStep 2826179 = 4239269) B4239269
theorem B13565893 : Blo 1254445 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B19316677 : Blo 1254445 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B6037453 : Blo 1254445 6037453 := bstep (se 3 (by rfl) ⟨1132022, by rfl⟩ : syracuseStep 6037453 = 2264045) B2264045
theorem B1884113 : Blo 1254445 1884113 := bstep (se 2 (by rfl) ⟨706542, by rfl⟩ : syracuseStep 1884113 = 1413085) B1413085
theorem B1884131 : Blo 1254445 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B2826251 : Blo 1254445 2826251 := bstep (se 1 (by rfl) ⟨2119688, by rfl⟩ : syracuseStep 2826251 = 4239377) B4239377
theorem B4767767 : Blo 1254445 4767767 := bstep (se 1 (by rfl) ⟨3575825, by rfl⟩ : syracuseStep 4767767 = 7151651) B7151651
theorem B1884185 : Blo 1254445 1884185 := bstep (se 2 (by rfl) ⟨706569, by rfl⟩ : syracuseStep 1884185 = 1413139) B1413139
theorem B3178561 : Blo 1254445 3178561 := bstep (se 2 (by rfl) ⟨1191960, by rfl⟩ : syracuseStep 3178561 = 2383921) B2383921
theorem B2826305 : Blo 1254445 2826305 := bstep (se 2 (by rfl) ⟨1059864, by rfl⟩ : syracuseStep 2826305 = 2119729) B2119729
theorem B9052235 : Blo 1254445 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B9175133 : Blo 1254445 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B1884299 : Blo 1254445 1884299 := bstep (se 1 (by rfl) ⟨1413224, by rfl⟩ : syracuseStep 1884299 = 2826449) B2826449
theorem B1884311 : Blo 1254445 1884311 := bstep (se 1 (by rfl) ⟨1413233, by rfl⟩ : syracuseStep 1884311 = 2826467) B2826467
theorem B1884377 : Blo 1254445 1884377 := bstep (se 2 (by rfl) ⟨706641, by rfl⟩ : syracuseStep 1884377 = 1413283) B1413283
theorem B4235543 : Blo 1254445 4235543 := bstep (se 1 (by rfl) ⟨3176657, by rfl⟩ : syracuseStep 4235543 = 6353315) B6353315
theorem B2826521 : Blo 1254445 2826521 := bstep (se 2 (by rfl) ⟨1059945, by rfl⟩ : syracuseStep 2826521 = 2119891) B2119891
theorem B8044865 : Blo 1254445 8044865 := bstep (se 2 (by rfl) ⟨3016824, by rfl⟩ : syracuseStep 8044865 = 6033649) B6033649
theorem B10731851 : Blo 1254445 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B1884491 : Blo 1254445 1884491 := bstep (se 1 (by rfl) ⟨1413368, by rfl⟩ : syracuseStep 1884491 = 2826737) B2826737
theorem B1884503 : Blo 1254445 1884503 := bstep (se 1 (by rfl) ⟨1413377, by rfl⟩ : syracuseStep 1884503 = 2826755) B2826755
theorem B2826611 : Blo 1254445 2826611 := bstep (se 1 (by rfl) ⟨2119958, by rfl⟩ : syracuseStep 2826611 = 4239917) B4239917
theorem B2826647 : Blo 1254445 2826647 := bstep (se 1 (by rfl) ⟨2119985, by rfl⟩ : syracuseStep 2826647 = 4239971) B4239971
theorem B1884569 : Blo 1254445 1884569 := bstep (se 2 (by rfl) ⟨706713, by rfl⟩ : syracuseStep 1884569 = 1413427) B1413427
theorem B2146775 : Blo 1254445 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B2384407 : Blo 1254445 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B2826827 : Blo 1254445 2826827 := bstep (se 1 (by rfl) ⟨2120120, by rfl⟩ : syracuseStep 2826827 = 4240241) B4240241
theorem B2826881 : Blo 1254445 2826881 := bstep (se 2 (by rfl) ⟨1060080, by rfl⟩ : syracuseStep 2826881 = 2120161) B2120161
theorem B3179159 : Blo 1254445 3179159 := bstep (se 1 (by rfl) ⟨2384369, by rfl⟩ : syracuseStep 3179159 = 4768739) B4768739
theorem B2294425 : Blo 1254445 2294425 := bstep (se 2 (by rfl) ⟨860409, by rfl⟩ : syracuseStep 2294425 = 1720819) B1720819
theorem B7152401 : Blo 1254445 7152401 := bstep (se 2 (by rfl) ⟨2682150, by rfl⟩ : syracuseStep 7152401 = 5364301) B5364301
theorem B9536291 : Blo 1254445 9536291 := bstep (se 1 (by rfl) ⟨7152218, by rfl⟩ : syracuseStep 9536291 = 14304437) B14304437
theorem B4236083 : Blo 1254445 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B3572545 : Blo 1254445 3572545 := bstep (se 2 (by rfl) ⟨1339704, by rfl⟩ : syracuseStep 3572545 = 2679409) B2679409
theorem B6792011 : Blo 1254445 6792011 := bstep (se 1 (by rfl) ⟨5094008, by rfl⟩ : syracuseStep 6792011 = 10188017) B10188017
theorem B1786711 : Blo 1254445 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B8045405 : Blo 1254445 8045405 := bstep (se 3 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 8045405 = 3017027) B3017027
theorem B13583321 : Blo 1254445 13583321 := bstep (se 2 (by rfl) ⟨5093745, by rfl⟩ : syracuseStep 13583321 = 10187491) B10187491
theorem B5358595 : Blo 1254445 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B1254455 : Blo 1254445 1254455 := bstep (se 1 (by rfl) ⟨940841, by rfl⟩ : syracuseStep 1254455 = 1881683) B1881683
theorem B4236353 : Blo 1254445 4236353 := bstep (se 2 (by rfl) ⟨1588632, by rfl⟩ : syracuseStep 4236353 = 3177265) B3177265
theorem B1254475 : Blo 1254445 1254475 := bstep (se 1 (by rfl) ⟨940856, by rfl⟩ : syracuseStep 1254475 = 1881713) B1881713
theorem B1254487 : Blo 1254445 1254487 := bstep (se 1 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 1254487 = 1881731) B1881731
theorem B2679895 : Blo 1254445 2679895 := bstep (se 1 (by rfl) ⟨2009921, by rfl⟩ : syracuseStep 2679895 = 4019843) B4019843
theorem B1254507 : Blo 1254445 1254507 := bstep (se 1 (by rfl) ⟨940880, by rfl⟩ : syracuseStep 1254507 = 1881761) B1881761
theorem B1254519 : Blo 1254445 1254519 := bstep (se 1 (by rfl) ⟨940889, by rfl⟩ : syracuseStep 1254519 = 1881779) B1881779
theorem B1254539 : Blo 1254445 1254539 := bstep (se 1 (by rfl) ⟨940904, by rfl⟩ : syracuseStep 1254539 = 1881809) B1881809
theorem B1254551 : Blo 1254445 1254551 := bstep (se 1 (by rfl) ⟨940913, by rfl⟩ : syracuseStep 1254551 = 1881827) B1881827
theorem B1254571 : Blo 1254445 1254571 := bstep (se 1 (by rfl) ⟨940928, by rfl⟩ : syracuseStep 1254571 = 1881857) B1881857
theorem B36201653 : Blo 1254445 36201653 := bstep (se 5 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 36201653 = 3393905) B3393905
theorem B1254583 : Blo 1254445 1254583 := bstep (se 1 (by rfl) ⟨940937, by rfl⟩ : syracuseStep 1254583 = 1881875) B1881875
theorem B1254603 : Blo 1254445 1254603 := bstep (se 1 (by rfl) ⟨940952, by rfl⟩ : syracuseStep 1254603 = 1881905) B1881905
theorem B1254615 : Blo 1254445 1254615 := bstep (se 1 (by rfl) ⟨940961, by rfl⟩ : syracuseStep 1254615 = 1881923) B1881923
theorem B7152857 : Blo 1254445 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B1254635 : Blo 1254445 1254635 := bstep (se 1 (by rfl) ⟨940976, by rfl⟩ : syracuseStep 1254635 = 1881953) B1881953
theorem B1254647 : Blo 1254445 1254647 := bstep (se 1 (by rfl) ⟨940985, by rfl⟩ : syracuseStep 1254647 = 1881971) B1881971
theorem B4769027 : Blo 1254445 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B1254667 : Blo 1254445 1254667 := bstep (se 1 (by rfl) ⟨941000, by rfl⟩ : syracuseStep 1254667 = 1882001) B1882001
theorem B1254679 : Blo 1254445 1254679 := bstep (se 1 (by rfl) ⟨941009, by rfl⟩ : syracuseStep 1254679 = 1882019) B1882019
theorem B3220759 : Blo 1254445 3220759 := bstep (se 1 (by rfl) ⟨2415569, by rfl⟩ : syracuseStep 3220759 = 4831139) B4831139
theorem B1254699 : Blo 1254445 1254699 := bstep (se 1 (by rfl) ⟨941024, by rfl⟩ : syracuseStep 1254699 = 1882049) B1882049
theorem B5088557 : Blo 1254445 5088557 := bstep (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) B1908209
theorem B1254711 : Blo 1254445 1254711 := bstep (se 1 (by rfl) ⟨941033, by rfl⟩ : syracuseStep 1254711 = 1882067) B1882067
theorem B6358337 : Blo 1254445 6358337 := bstep (se 2 (by rfl) ⟨2384376, by rfl⟩ : syracuseStep 6358337 = 4768753) B4768753
theorem B1254731 : Blo 1254445 1254731 := bstep (se 1 (by rfl) ⟨941048, by rfl⟩ : syracuseStep 1254731 = 1882097) B1882097
theorem B2385227 : Blo 1254445 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B1254743 : Blo 1254445 1254743 := bstep (se 1 (by rfl) ⟨941057, by rfl⟩ : syracuseStep 1254743 = 1882115) B1882115
theorem B9045341 : Blo 1254445 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B5727581 : Blo 1254445 5727581 := bstep (se 3 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 5727581 = 2147843) B2147843
theorem B1254763 : Blo 1254445 1254763 := bstep (se 1 (by rfl) ⟨941072, by rfl⟩ : syracuseStep 1254763 = 1882145) B1882145
theorem B1254775 : Blo 1254445 1254775 := bstep (se 1 (by rfl) ⟨941081, by rfl⟩ : syracuseStep 1254775 = 1882163) B1882163
theorem B2385281 : Blo 1254445 2385281 := bstep (se 2 (by rfl) ⟨894480, by rfl⟩ : syracuseStep 2385281 = 1788961) B1788961
theorem B1254795 : Blo 1254445 1254795 := bstep (se 1 (by rfl) ⟨941096, by rfl⟩ : syracuseStep 1254795 = 1882193) B1882193
theorem B1787275 : Blo 1254445 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B1254807 : Blo 1254445 1254807 := bstep (se 1 (by rfl) ⟨941105, by rfl⟩ : syracuseStep 1254807 = 1882211) B1882211
theorem B1254827 : Blo 1254445 1254827 := bstep (se 1 (by rfl) ⟨941120, by rfl⟩ : syracuseStep 1254827 = 1882241) B1882241
theorem B1254839 : Blo 1254445 1254839 := bstep (se 1 (by rfl) ⟨941129, by rfl⟩ : syracuseStep 1254839 = 1882259) B1882259
theorem B3179969 : Blo 1254445 3179969 := bstep (se 2 (by rfl) ⟨1192488, by rfl⟩ : syracuseStep 3179969 = 2384977) B2384977
theorem B1254859 : Blo 1254445 1254859 := bstep (se 1 (by rfl) ⟨941144, by rfl⟩ : syracuseStep 1254859 = 1882289) B1882289
theorem B1254871 : Blo 1254445 1254871 := bstep (se 1 (by rfl) ⟨941153, by rfl⟩ : syracuseStep 1254871 = 1882307) B1882307
theorem B1254891 : Blo 1254445 1254891 := bstep (se 1 (by rfl) ⟨941168, by rfl⟩ : syracuseStep 1254891 = 1882337) B1882337
theorem B1254903 : Blo 1254445 1254903 := bstep (se 1 (by rfl) ⟨941177, by rfl⟩ : syracuseStep 1254903 = 1882355) B1882355
theorem B1254923 : Blo 1254445 1254923 := bstep (se 1 (by rfl) ⟨941192, by rfl⟩ : syracuseStep 1254923 = 1882385) B1882385
theorem B1254935 : Blo 1254445 1254935 := bstep (se 1 (by rfl) ⟨941201, by rfl⟩ : syracuseStep 1254935 = 1882403) B1882403
theorem B1254955 : Blo 1254445 1254955 := bstep (se 1 (by rfl) ⟨941216, by rfl⟩ : syracuseStep 1254955 = 1882433) B1882433
theorem B1254967 : Blo 1254445 1254967 := bstep (se 1 (by rfl) ⟨941225, by rfl⟩ : syracuseStep 1254967 = 1882451) B1882451
theorem B9045569 : Blo 1254445 9045569 := bstep (se 2 (by rfl) ⟨3392088, by rfl⟩ : syracuseStep 9045569 = 6784177) B6784177
theorem B1254987 : Blo 1254445 1254987 := bstep (se 1 (by rfl) ⟨941240, by rfl⟩ : syracuseStep 1254987 = 1882481) B1882481
theorem B1254999 : Blo 1254445 1254999 := bstep (se 1 (by rfl) ⟨941249, by rfl⟩ : syracuseStep 1254999 = 1882499) B1882499
theorem B4236893 : Blo 1254445 4236893 := bstep (se 3 (by rfl) ⟨794417, by rfl⟩ : syracuseStep 4236893 = 1588835) B1588835
theorem B1255019 : Blo 1254445 1255019 := bstep (se 1 (by rfl) ⟨941264, by rfl⟩ : syracuseStep 1255019 = 1882529) B1882529
theorem B1255031 : Blo 1254445 1255031 := bstep (se 1 (by rfl) ⟨941273, by rfl⟩ : syracuseStep 1255031 = 1882547) B1882547
theorem B9168515 : Blo 1254445 9168515 := bstep (se 1 (by rfl) ⟨6876386, by rfl⟩ : syracuseStep 9168515 = 13752773) B13752773
theorem B4523651 : Blo 1254445 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B1255051 : Blo 1254445 1255051 := bstep (se 1 (by rfl) ⟨941288, by rfl⟩ : syracuseStep 1255051 = 1882577) B1882577
theorem B7145111 : Blo 1254445 7145111 := bstep (se 1 (by rfl) ⟨5358833, by rfl⟩ : syracuseStep 7145111 = 10717667) B10717667
theorem B1255063 : Blo 1254445 1255063 := bstep (se 1 (by rfl) ⟨941297, by rfl⟩ : syracuseStep 1255063 = 1882595) B1882595
theorem B1255083 : Blo 1254445 1255083 := bstep (se 1 (by rfl) ⟨941312, by rfl⟩ : syracuseStep 1255083 = 1882625) B1882625
theorem B9053873 : Blo 1254445 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B1255095 : Blo 1254445 1255095 := bstep (se 1 (by rfl) ⟨941321, by rfl⟩ : syracuseStep 1255095 = 1882643) B1882643
theorem B1255115 : Blo 1254445 1255115 := bstep (se 1 (by rfl) ⟨941336, by rfl⟩ : syracuseStep 1255115 = 1882673) B1882673
theorem B1255127 : Blo 1254445 1255127 := bstep (se 1 (by rfl) ⟨941345, by rfl⟩ : syracuseStep 1255127 = 1882691) B1882691
theorem B1255147 : Blo 1254445 1255147 := bstep (se 1 (by rfl) ⟨941360, by rfl⟩ : syracuseStep 1255147 = 1882721) B1882721
theorem B1255159 : Blo 1254445 1255159 := bstep (se 1 (by rfl) ⟨941369, by rfl⟩ : syracuseStep 1255159 = 1882739) B1882739
theorem B1255179 : Blo 1254445 1255179 := bstep (se 1 (by rfl) ⟨941384, by rfl⟩ : syracuseStep 1255179 = 1882769) B1882769
theorem B1255191 : Blo 1254445 1255191 := bstep (se 1 (by rfl) ⟨941393, by rfl⟩ : syracuseStep 1255191 = 1882787) B1882787
theorem B1255211 : Blo 1254445 1255211 := bstep (se 1 (by rfl) ⟨941408, by rfl⟩ : syracuseStep 1255211 = 1882817) B1882817
theorem B6530861 : Blo 1254445 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B1255223 : Blo 1254445 1255223 := bstep (se 1 (by rfl) ⟨941417, by rfl⟩ : syracuseStep 1255223 = 1882835) B1882835
theorem B1255243 : Blo 1254445 1255243 := bstep (se 1 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 1255243 = 1882865) B1882865
theorem B1255255 : Blo 1254445 1255255 := bstep (se 1 (by rfl) ⟨941441, by rfl⟩ : syracuseStep 1255255 = 1882883) B1882883
theorem B1255275 : Blo 1254445 1255275 := bstep (se 1 (by rfl) ⟨941456, by rfl⟩ : syracuseStep 1255275 = 1882913) B1882913
theorem B1255287 : Blo 1254445 1255287 := bstep (se 1 (by rfl) ⟨941465, by rfl⟩ : syracuseStep 1255287 = 1882931) B1882931
theorem B6350723 : Blo 1254445 6350723 := bstep (se 1 (by rfl) ⟨4763042, by rfl⟩ : syracuseStep 6350723 = 9526085) B9526085
theorem B1255307 : Blo 1254445 1255307 := bstep (se 1 (by rfl) ⟨941480, by rfl⟩ : syracuseStep 1255307 = 1882961) B1882961
theorem B1255319 : Blo 1254445 1255319 := bstep (se 1 (by rfl) ⟨941489, by rfl⟩ : syracuseStep 1255319 = 1882979) B1882979
theorem B1255339 : Blo 1254445 1255339 := bstep (se 1 (by rfl) ⟨941504, by rfl⟩ : syracuseStep 1255339 = 1883009) B1883009
theorem B1255351 : Blo 1254445 1255351 := bstep (se 1 (by rfl) ⟨941513, by rfl⟩ : syracuseStep 1255351 = 1883027) B1883027
theorem B5359553 : Blo 1254445 5359553 := bstep (se 2 (by rfl) ⟨2009832, by rfl⟩ : syracuseStep 5359553 = 4019665) B4019665
theorem B1255371 : Blo 1254445 1255371 := bstep (se 1 (by rfl) ⟨941528, by rfl⟩ : syracuseStep 1255371 = 1883057) B1883057
theorem B1255383 : Blo 1254445 1255383 := bstep (se 1 (by rfl) ⟨941537, by rfl⟩ : syracuseStep 1255383 = 1883075) B1883075
theorem B1697753 : Blo 1254445 1697753 := bstep (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) B1273315
theorem B1255403 : Blo 1254445 1255403 := bstep (se 1 (by rfl) ⟨941552, by rfl⟩ : syracuseStep 1255403 = 1883105) B1883105
theorem B1255415 : Blo 1254445 1255415 := bstep (se 1 (by rfl) ⟨941561, by rfl⟩ : syracuseStep 1255415 = 1883123) B1883123
theorem B1255435 : Blo 1254445 1255435 := bstep (se 1 (by rfl) ⟨941576, by rfl⟩ : syracuseStep 1255435 = 1883153) B1883153
theorem B1255447 : Blo 1254445 1255447 := bstep (se 1 (by rfl) ⟨941585, by rfl⟩ : syracuseStep 1255447 = 1883171) B1883171
theorem B4024343 : Blo 1254445 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B1255467 : Blo 1254445 1255467 := bstep (se 1 (by rfl) ⟨941600, by rfl⟩ : syracuseStep 1255467 = 1883201) B1883201
theorem B1255479 : Blo 1254445 1255479 := bstep (se 1 (by rfl) ⟨941609, by rfl⟩ : syracuseStep 1255479 = 1883219) B1883219
theorem B19859525 : Blo 1254445 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B1255499 : Blo 1254445 1255499 := bstep (se 1 (by rfl) ⟨941624, by rfl⟩ : syracuseStep 1255499 = 1883249) B1883249
theorem B1255511 : Blo 1254445 1255511 := bstep (se 1 (by rfl) ⟨941633, by rfl⟩ : syracuseStep 1255511 = 1883267) B1883267
theorem B1255531 : Blo 1254445 1255531 := bstep (se 1 (by rfl) ⟨941648, by rfl⟩ : syracuseStep 1255531 = 1883297) B1883297
theorem B1255543 : Blo 1254445 1255543 := bstep (se 1 (by rfl) ⟨941657, by rfl⟩ : syracuseStep 1255543 = 1883315) B1883315
theorem B1255563 : Blo 1254445 1255563 := bstep (se 1 (by rfl) ⟨941672, by rfl⟩ : syracuseStep 1255563 = 1883345) B1883345
theorem B1255575 : Blo 1254445 1255575 := bstep (se 1 (by rfl) ⟨941681, by rfl⟩ : syracuseStep 1255575 = 1883363) B1883363
theorem B1255595 : Blo 1254445 1255595 := bstep (se 1 (by rfl) ⟨941696, by rfl⟩ : syracuseStep 1255595 = 1883393) B1883393
theorem B1255607 : Blo 1254445 1255607 := bstep (se 1 (by rfl) ⟨941705, by rfl⟩ : syracuseStep 1255607 = 1883411) B1883411
theorem B1255627 : Blo 1254445 1255627 := bstep (se 1 (by rfl) ⟨941720, by rfl⟩ : syracuseStep 1255627 = 1883441) B1883441
theorem B1255639 : Blo 1254445 1255639 := bstep (se 1 (by rfl) ⟨941729, by rfl⟩ : syracuseStep 1255639 = 1883459) B1883459
theorem B3016921 : Blo 1254445 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B2615513 : Blo 1254445 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B1255659 : Blo 1254445 1255659 := bstep (se 1 (by rfl) ⟨941744, by rfl⟩ : syracuseStep 1255659 = 1883489) B1883489
theorem B2681075 : Blo 1254445 2681075 := bstep (se 1 (by rfl) ⟨2010806, by rfl⟩ : syracuseStep 2681075 = 4021613) B4021613
theorem B1255671 : Blo 1254445 1255671 := bstep (se 1 (by rfl) ⟨941753, by rfl⟩ : syracuseStep 1255671 = 1883507) B1883507
theorem B1411339 : Blo 1254445 1411339 := bstep (se 1 (by rfl) ⟨1058504, by rfl⟩ : syracuseStep 1411339 = 2117009) B2117009
theorem B1255691 : Blo 1254445 1255691 := bstep (se 1 (by rfl) ⟨941768, by rfl⟩ : syracuseStep 1255691 = 1883537) B1883537
theorem B5728529 : Blo 1254445 5728529 := bstep (se 2 (by rfl) ⟨2148198, by rfl⟩ : syracuseStep 5728529 = 4296397) B4296397
theorem B1255703 : Blo 1254445 1255703 := bstep (se 1 (by rfl) ⟨941777, by rfl⟩ : syracuseStep 1255703 = 1883555) B1883555
theorem B1255723 : Blo 1254445 1255723 := bstep (se 1 (by rfl) ⟨941792, by rfl⟩ : syracuseStep 1255723 = 1883585) B1883585
theorem B1255735 : Blo 1254445 1255735 := bstep (se 1 (by rfl) ⟨941801, by rfl⟩ : syracuseStep 1255735 = 1883603) B1883603
theorem B3017035 : Blo 1254445 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B1255755 : Blo 1254445 1255755 := bstep (se 1 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 1255755 = 1883633) B1883633
theorem B1255767 : Blo 1254445 1255767 := bstep (se 1 (by rfl) ⟨941825, by rfl⟩ : syracuseStep 1255767 = 1883651) B1883651
theorem B1255787 : Blo 1254445 1255787 := bstep (se 1 (by rfl) ⟨941840, by rfl⟩ : syracuseStep 1255787 = 1883681) B1883681
theorem B14494069 : Blo 1254445 14494069 := bstep (se 5 (by rfl) ⟨679409, by rfl⟩ : syracuseStep 14494069 = 1358819) B1358819
theorem B1411447 : Blo 1254445 1411447 := bstep (se 1 (by rfl) ⟨1058585, by rfl⟩ : syracuseStep 1411447 = 2117171) B2117171
theorem B1255799 : Blo 1254445 1255799 := bstep (se 1 (by rfl) ⟨941849, by rfl⟩ : syracuseStep 1255799 = 1883699) B1883699
theorem B1255819 : Blo 1254445 1255819 := bstep (se 1 (by rfl) ⟨941864, by rfl⟩ : syracuseStep 1255819 = 1883729) B1883729
theorem B1255831 : Blo 1254445 1255831 := bstep (se 1 (by rfl) ⟨941873, by rfl⟩ : syracuseStep 1255831 = 1883747) B1883747
theorem B1255851 : Blo 1254445 1255851 := bstep (se 1 (by rfl) ⟨941888, by rfl⟩ : syracuseStep 1255851 = 1883777) B1883777
theorem B1255863 : Blo 1254445 1255863 := bstep (se 1 (by rfl) ⟨941897, by rfl⟩ : syracuseStep 1255863 = 1883795) B1883795
theorem B3574219 : Blo 1254445 3574219 := bstep (se 1 (by rfl) ⟨2680664, by rfl⟩ : syracuseStep 3574219 = 5361329) B5361329
theorem B1255883 : Blo 1254445 1255883 := bstep (se 1 (by rfl) ⟨941912, by rfl⟩ : syracuseStep 1255883 = 1883825) B1883825
theorem B1255895 : Blo 1254445 1255895 := bstep (se 1 (by rfl) ⟨941921, by rfl⟩ : syracuseStep 1255895 = 1883843) B1883843
theorem B1255915 : Blo 1254445 1255915 := bstep (se 1 (by rfl) ⟨941936, by rfl⟩ : syracuseStep 1255915 = 1883873) B1883873
theorem B1255927 : Blo 1254445 1255927 := bstep (se 1 (by rfl) ⟨941945, by rfl⟩ : syracuseStep 1255927 = 1883891) B1883891
theorem B1255947 : Blo 1254445 1255947 := bstep (se 1 (by rfl) ⟨941960, by rfl⟩ : syracuseStep 1255947 = 1883921) B1883921
theorem B1255959 : Blo 1254445 1255959 := bstep (se 1 (by rfl) ⟨941969, by rfl⟩ : syracuseStep 1255959 = 1883939) B1883939
theorem B1411627 : Blo 1254445 1411627 := bstep (se 1 (by rfl) ⟨1058720, by rfl⟩ : syracuseStep 1411627 = 2117441) B2117441
theorem B1255979 : Blo 1254445 1255979 := bstep (se 1 (by rfl) ⟨941984, by rfl⟩ : syracuseStep 1255979 = 1883969) B1883969
theorem B1255991 : Blo 1254445 1255991 := bstep (se 1 (by rfl) ⟨941993, by rfl⟩ : syracuseStep 1255991 = 1883987) B1883987
theorem B4524619 : Blo 1254445 4524619 := bstep (se 1 (by rfl) ⟨3393464, by rfl⟩ : syracuseStep 4524619 = 6786929) B6786929
theorem B1256011 : Blo 1254445 1256011 := bstep (se 1 (by rfl) ⟨942008, by rfl⟩ : syracuseStep 1256011 = 1884017) B1884017
theorem B1272407 : Blo 1254445 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B1256023 : Blo 1254445 1256023 := bstep (se 1 (by rfl) ⟨942017, by rfl⟩ : syracuseStep 1256023 = 1884035) B1884035
theorem B1256043 : Blo 1254445 1256043 := bstep (se 1 (by rfl) ⟨942032, by rfl⟩ : syracuseStep 1256043 = 1884065) B1884065
theorem B1256055 : Blo 1254445 1256055 := bstep (se 1 (by rfl) ⟨942041, by rfl⟩ : syracuseStep 1256055 = 1884083) B1884083
theorem B1256075 : Blo 1254445 1256075 := bstep (se 1 (by rfl) ⟨942056, by rfl⟩ : syracuseStep 1256075 = 1884113) B1884113
theorem B1411735 : Blo 1254445 1411735 := bstep (se 1 (by rfl) ⟨1058801, by rfl⟩ : syracuseStep 1411735 = 2117603) B2117603
theorem B1256087 : Blo 1254445 1256087 := bstep (se 1 (by rfl) ⟨942065, by rfl⟩ : syracuseStep 1256087 = 1884131) B1884131
theorem B1256107 : Blo 1254445 1256107 := bstep (se 1 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 1256107 = 1884161) B1884161
theorem B1256119 : Blo 1254445 1256119 := bstep (se 1 (by rfl) ⟨942089, by rfl⟩ : syracuseStep 1256119 = 1884179) B1884179
theorem B41863877 : Blo 1254445 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B4238027 : Blo 1254445 4238027 := bstep (se 1 (by rfl) ⟨3178520, by rfl⟩ : syracuseStep 4238027 = 6357041) B6357041
theorem B1256139 : Blo 1254445 1256139 := bstep (se 1 (by rfl) ⟨942104, by rfl⟩ : syracuseStep 1256139 = 1884209) B1884209
theorem B1256151 : Blo 1254445 1256151 := bstep (se 1 (by rfl) ⟨942113, by rfl⟩ : syracuseStep 1256151 = 1884227) B1884227
theorem B3574493 : Blo 1254445 3574493 := bstep (se 3 (by rfl) ⟨670217, by rfl⟩ : syracuseStep 3574493 = 1340435) B1340435
theorem B1256171 : Blo 1254445 1256171 := bstep (se 1 (by rfl) ⟨942128, by rfl⟩ : syracuseStep 1256171 = 1884257) B1884257
theorem B1256183 : Blo 1254445 1256183 := bstep (se 1 (by rfl) ⟨942137, by rfl⟩ : syracuseStep 1256183 = 1884275) B1884275
theorem B1256203 : Blo 1254445 1256203 := bstep (se 1 (by rfl) ⟨942152, by rfl⟩ : syracuseStep 1256203 = 1884305) B1884305
theorem B1256215 : Blo 1254445 1256215 := bstep (se 1 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 1256215 = 1884323) B1884323
theorem B1256235 : Blo 1254445 1256235 := bstep (se 1 (by rfl) ⟨942176, by rfl⟩ : syracuseStep 1256235 = 1884353) B1884353
theorem B1256247 : Blo 1254445 1256247 := bstep (se 1 (by rfl) ⟨942185, by rfl⟩ : syracuseStep 1256247 = 1884371) B1884371
theorem B3017537 : Blo 1254445 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B1411915 : Blo 1254445 1411915 := bstep (se 1 (by rfl) ⟨1058936, by rfl⟩ : syracuseStep 1411915 = 2117873) B2117873
theorem B1256267 : Blo 1254445 1256267 := bstep (se 1 (by rfl) ⟨942200, by rfl⟩ : syracuseStep 1256267 = 1884401) B1884401
theorem B1256279 : Blo 1254445 1256279 := bstep (se 1 (by rfl) ⟨942209, by rfl⟩ : syracuseStep 1256279 = 1884419) B1884419
theorem B1788761 : Blo 1254445 1788761 := bstep (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) B1341571
theorem B4524893 : Blo 1254445 4524893 := bstep (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) B1696835
theorem B1256299 : Blo 1254445 1256299 := bstep (se 1 (by rfl) ⟨942224, by rfl⟩ : syracuseStep 1256299 = 1884449) B1884449
theorem B1256311 : Blo 1254445 1256311 := bstep (se 1 (by rfl) ⟨942233, by rfl⟩ : syracuseStep 1256311 = 1884467) B1884467
theorem B1256331 : Blo 1254445 1256331 := bstep (se 1 (by rfl) ⟨942248, by rfl⟩ : syracuseStep 1256331 = 1884497) B1884497
theorem B1256343 : Blo 1254445 1256343 := bstep (se 1 (by rfl) ⟨942257, by rfl⟩ : syracuseStep 1256343 = 1884515) B1884515
theorem B1256363 : Blo 1254445 1256363 := bstep (se 1 (by rfl) ⟨942272, by rfl⟩ : syracuseStep 1256363 = 1884545) B1884545
theorem B1412023 : Blo 1254445 1412023 := bstep (se 1 (by rfl) ⟨1059017, by rfl⟩ : syracuseStep 1412023 = 2118035) B2118035
theorem B1256375 : Blo 1254445 1256375 := bstep (se 1 (by rfl) ⟨942281, by rfl⟩ : syracuseStep 1256375 = 1884563) B1884563
theorem B1256395 : Blo 1254445 1256395 := bstep (se 1 (by rfl) ⟨942296, by rfl⟩ : syracuseStep 1256395 = 1884593) B1884593
theorem B1256407 : Blo 1254445 1256407 := bstep (se 1 (by rfl) ⟨942305, by rfl⟩ : syracuseStep 1256407 = 1884611) B1884611
theorem B4238297 : Blo 1254445 4238297 := bstep (se 2 (by rfl) ⟨1589361, by rfl⟩ : syracuseStep 4238297 = 3178723) B3178723
theorem B1256427 : Blo 1254445 1256427 := bstep (se 1 (by rfl) ⟨942320, by rfl⟩ : syracuseStep 1256427 = 1884641) B1884641
theorem B1256439 : Blo 1254445 1256439 := bstep (se 1 (by rfl) ⟨942329, by rfl⟩ : syracuseStep 1256439 = 1884659) B1884659
theorem B1412203 : Blo 1254445 1412203 := bstep (se 1 (by rfl) ⟨1059152, by rfl⟩ : syracuseStep 1412203 = 2118305) B2118305
theorem B1412311 : Blo 1254445 1412311 := bstep (se 1 (by rfl) ⟨1059233, by rfl⟩ : syracuseStep 1412311 = 2118467) B2118467
theorem B6360281 : Blo 1254445 6360281 := bstep (se 2 (by rfl) ⟨2385105, by rfl⟩ : syracuseStep 6360281 = 4770211) B4770211
theorem B3018035 : Blo 1254445 3018035 := bstep (se 1 (by rfl) ⟨2263526, by rfl⟩ : syracuseStep 3018035 = 4527053) B4527053
theorem B1412491 : Blo 1254445 1412491 := bstep (se 1 (by rfl) ⟨1059368, by rfl⟩ : syracuseStep 1412491 = 2118737) B2118737
theorem B2682305 : Blo 1254445 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B1412599 : Blo 1254445 1412599 := bstep (se 1 (by rfl) ⟨1059449, by rfl⟩ : syracuseStep 1412599 = 2118899) B2118899
theorem B7147025 : Blo 1254445 7147025 := bstep (se 2 (by rfl) ⟨2680134, by rfl⟩ : syracuseStep 7147025 = 5360269) B5360269
theorem B4075031 : Blo 1254445 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B9530945 : Blo 1254445 9530945 := bstep (se 2 (by rfl) ⟨3574104, by rfl⟩ : syracuseStep 9530945 = 7148209) B7148209
theorem B5361227 : Blo 1254445 5361227 := bstep (se 1 (by rfl) ⟨4020920, by rfl⟩ : syracuseStep 5361227 = 8041841) B8041841
theorem B4763225 : Blo 1254445 4763225 := bstep (se 2 (by rfl) ⟨1786209, by rfl⟩ : syracuseStep 4763225 = 3572419) B3572419
theorem B5729881 : Blo 1254445 5729881 := bstep (se 2 (by rfl) ⟨2148705, by rfl⟩ : syracuseStep 5729881 = 4297411) B4297411
theorem B1609355 : Blo 1254445 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B4238999 : Blo 1254445 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B1412779 : Blo 1254445 1412779 := bstep (se 1 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 1412779 = 2119169) B2119169
theorem B2117387 : Blo 1254445 2117387 := bstep (se 1 (by rfl) ⟨1588040, by rfl⟩ : syracuseStep 2117387 = 3176081) B3176081
theorem B1412887 : Blo 1254445 1412887 := bstep (se 1 (by rfl) ⟨1059665, by rfl⟩ : syracuseStep 1412887 = 2119331) B2119331
theorem B4829017 : Blo 1254445 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B2117515 : Blo 1254445 2117515 := bstep (se 1 (by rfl) ⟨1588136, by rfl⟩ : syracuseStep 2117515 = 3176273) B3176273
theorem B1413067 : Blo 1254445 1413067 := bstep (se 1 (by rfl) ⟨1059800, by rfl⟩ : syracuseStep 1413067 = 2119601) B2119601
theorem B3395549 : Blo 1254445 3395549 := bstep (se 3 (by rfl) ⟨636665, by rfl⟩ : syracuseStep 3395549 = 1273331) B1273331
theorem B2117657 : Blo 1254445 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B1413175 : Blo 1254445 1413175 := bstep (se 1 (by rfl) ⟨1059881, by rfl⟩ : syracuseStep 1413175 = 2119763) B2119763
theorem B2117785 : Blo 1254445 2117785 := bstep (se 2 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 2117785 = 1588339) B1588339
theorem B4239539 : Blo 1254445 4239539 := bstep (se 1 (by rfl) ⟨3179654, by rfl⟩ : syracuseStep 4239539 = 6359309) B6359309
theorem B3625181 : Blo 1254445 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B1413355 : Blo 1254445 1413355 := bstep (se 1 (by rfl) ⟨1060016, by rfl⟩ : syracuseStep 1413355 = 2120033) B2120033
theorem B6115601 : Blo 1254445 6115601 := bstep (se 2 (by rfl) ⟨2293350, by rfl⟩ : syracuseStep 6115601 = 4586701) B4586701
theorem B1413463 : Blo 1254445 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B1610123 : Blo 1254445 1610123 := bstep (se 1 (by rfl) ⟨1207592, by rfl⟩ : syracuseStep 1610123 = 2415185) B2415185
theorem B2822579 : Blo 1254445 2822579 := bstep (se 1 (by rfl) ⟨2116934, by rfl⟩ : syracuseStep 2822579 = 4233869) B4233869
theorem B4239809 : Blo 1254445 4239809 := bstep (se 2 (by rfl) ⟨1589928, by rfl⟩ : syracuseStep 4239809 = 3179857) B3179857
theorem B2822615 : Blo 1254445 2822615 := bstep (se 1 (by rfl) ⟨2116961, by rfl⟩ : syracuseStep 2822615 = 4233923) B4233923
theorem B2683415 : Blo 1254445 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B2822795 : Blo 1254445 2822795 := bstep (se 1 (by rfl) ⟨2117096, by rfl⟩ : syracuseStep 2822795 = 4234193) B4234193
theorem B2822849 : Blo 1254445 2822849 := bstep (se 2 (by rfl) ⟨1058568, by rfl⟩ : syracuseStep 2822849 = 2117137) B2117137
theorem B2118359 : Blo 1254445 2118359 := bstep (se 1 (by rfl) ⟨1588769, by rfl⟩ : syracuseStep 2118359 = 3177539) B3177539
theorem B5509849 : Blo 1254445 5509849 := bstep (se 2 (by rfl) ⟨2066193, by rfl⟩ : syracuseStep 5509849 = 4132387) B4132387
theorem B4018909 : Blo 1254445 4018909 := bstep (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) B1507091
theorem B2544385 : Blo 1254445 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B2011915 : Blo 1254445 2011915 := bstep (se 1 (by rfl) ⟨1508936, by rfl⟩ : syracuseStep 2011915 = 3017873) B3017873
theorem B1340183 : Blo 1254445 1340183 := bstep (se 1 (by rfl) ⟨1005137, by rfl⟩ : syracuseStep 1340183 = 2010275) B2010275
theorem B2118487 : Blo 1254445 2118487 := bstep (se 1 (by rfl) ⟨1588865, by rfl⟩ : syracuseStep 2118487 = 3177731) B3177731
theorem B5722969 : Blo 1254445 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B2823065 : Blo 1254445 2823065 := bstep (se 2 (by rfl) ⟨1058649, by rfl⟩ : syracuseStep 2823065 = 2117299) B2117299
theorem B2864065 : Blo 1254445 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B3576793 : Blo 1254445 3576793 := bstep (se 2 (by rfl) ⟨1341297, by rfl⟩ : syracuseStep 3576793 = 2682595) B2682595
theorem B4240349 : Blo 1254445 4240349 := bstep (se 3 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 4240349 = 1590131) B1590131
theorem B2823155 : Blo 1254445 2823155 := bstep (se 1 (by rfl) ⟨2117366, by rfl⟩ : syracuseStep 2823155 = 4234733) B4234733
theorem B2823191 : Blo 1254445 2823191 := bstep (se 1 (by rfl) ⟨2117393, by rfl⟩ : syracuseStep 2823191 = 4234787) B4234787
theorem B4764851 : Blo 1254445 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B4764865 : Blo 1254445 4764865 := bstep (se 2 (by rfl) ⟨1786824, by rfl⟩ : syracuseStep 4764865 = 3573649) B3573649
theorem B2823371 : Blo 1254445 2823371 := bstep (se 1 (by rfl) ⟨2117528, by rfl⟩ : syracuseStep 2823371 = 4235057) B4235057
theorem B4297931 : Blo 1254445 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B2823425 : Blo 1254445 2823425 := bstep (se 2 (by rfl) ⟨1058784, by rfl⟩ : syracuseStep 2823425 = 2117569) B2117569
theorem B8049937 : Blo 1254445 8049937 := bstep (se 2 (by rfl) ⟨3018726, by rfl⟩ : syracuseStep 8049937 = 6037453) B6037453
theorem B2119115 : Blo 1254445 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B2823641 : Blo 1254445 2823641 := bstep (se 2 (by rfl) ⟨1058865, by rfl⟩ : syracuseStep 2823641 = 2117731) B2117731
theorem B9532889 : Blo 1254445 9532889 := bstep (se 2 (by rfl) ⟨3574833, by rfl⟩ : syracuseStep 9532889 = 7149667) B7149667
theorem B6354449 : Blo 1254445 6354449 := bstep (se 2 (by rfl) ⟨2382918, by rfl⟩ : syracuseStep 6354449 = 4765837) B4765837
theorem B2823731 : Blo 1254445 2823731 := bstep (se 1 (by rfl) ⟨2117798, by rfl⟩ : syracuseStep 2823731 = 4235597) B4235597
theorem B5723713 : Blo 1254445 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B3577409 : Blo 1254445 3577409 := bstep (se 2 (by rfl) ⟨1341528, by rfl⟩ : syracuseStep 3577409 = 2683057) B2683057
theorem B2119243 : Blo 1254445 2119243 := bstep (se 1 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 2119243 = 3178865) B3178865
theorem B2823767 : Blo 1254445 2823767 := bstep (se 1 (by rfl) ⟨2117825, by rfl⟩ : syracuseStep 2823767 = 4235651) B4235651
theorem B1881689 : Blo 1254445 1881689 := bstep (se 2 (by rfl) ⟨705633, by rfl⟩ : syracuseStep 1881689 = 1411267) B1411267
theorem B2381491 : Blo 1254445 2381491 := bstep (se 1 (by rfl) ⟨1786118, by rfl⟩ : syracuseStep 2381491 = 3572237) B3572237
theorem B6354611 : Blo 1254445 6354611 := bstep (se 1 (by rfl) ⟨4765958, by rfl⟩ : syracuseStep 6354611 = 9531917) B9531917
theorem B1881803 : Blo 1254445 1881803 := bstep (se 1 (by rfl) ⟨1411352, by rfl⟩ : syracuseStep 1881803 = 2822705) B2822705
theorem B1881815 : Blo 1254445 1881815 := bstep (se 1 (by rfl) ⟨1411361, by rfl⟩ : syracuseStep 1881815 = 2822723) B2822723
theorem B2119385 : Blo 1254445 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B2823947 : Blo 1254445 2823947 := bstep (se 1 (by rfl) ⟨2117960, by rfl⟩ : syracuseStep 2823947 = 4235921) B4235921
theorem B6616849 : Blo 1254445 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B1881881 : Blo 1254445 1881881 := bstep (se 2 (by rfl) ⟨705705, by rfl⟩ : syracuseStep 1881881 = 1411411) B1411411
theorem B3176243 : Blo 1254445 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B2824001 : Blo 1254445 2824001 := bstep (se 2 (by rfl) ⟨1059000, by rfl⟩ : syracuseStep 2824001 = 2118001) B2118001
theorem B2119513 : Blo 1254445 2119513 := bstep (se 2 (by rfl) ⟨794817, by rfl⟩ : syracuseStep 2119513 = 1589635) B1589635
theorem B1881995 : Blo 1254445 1881995 := bstep (se 1 (by rfl) ⟨1411496, by rfl⟩ : syracuseStep 1881995 = 2822993) B2822993
theorem B2381719 : Blo 1254445 2381719 := bstep (se 1 (by rfl) ⟨1786289, by rfl⟩ : syracuseStep 2381719 = 3572579) B3572579
theorem B1882007 : Blo 1254445 1882007 := bstep (se 1 (by rfl) ⟨1411505, by rfl⟩ : syracuseStep 1882007 = 2823011) B2823011
theorem B1882073 : Blo 1254445 1882073 := bstep (se 2 (by rfl) ⟨705777, by rfl⟩ : syracuseStep 1882073 = 1411555) B1411555
theorem B2381825 : Blo 1254445 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B15267857 : Blo 1254445 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B2824217 : Blo 1254445 2824217 := bstep (se 2 (by rfl) ⟨1059081, by rfl⟩ : syracuseStep 2824217 = 2118163) B2118163
theorem B1882187 : Blo 1254445 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B1882199 : Blo 1254445 1882199 := bstep (se 1 (by rfl) ⟨1411649, by rfl⟩ : syracuseStep 1882199 = 2823299) B2823299
theorem B2824307 : Blo 1254445 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B2824343 : Blo 1254445 2824343 := bstep (se 1 (by rfl) ⟨2118257, by rfl⟩ : syracuseStep 2824343 = 4236515) B4236515
theorem B2381977 : Blo 1254445 2381977 := bstep (se 2 (by rfl) ⟨893241, by rfl⟩ : syracuseStep 2381977 = 1786483) B1786483
theorem B1882265 : Blo 1254445 1882265 := bstep (se 2 (by rfl) ⟨705849, by rfl⟩ : syracuseStep 1882265 = 1411699) B1411699
theorem B5363891 : Blo 1254445 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B9173197 : Blo 1254445 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B3922141 : Blo 1254445 3922141 := bstep (se 3 (by rfl) ⟨735401, by rfl⟩ : syracuseStep 3922141 = 1470803) B1470803
theorem B1882379 : Blo 1254445 1882379 := bstep (se 1 (by rfl) ⟨1411784, by rfl⟩ : syracuseStep 1882379 = 2823569) B2823569
theorem B1882391 : Blo 1254445 1882391 := bstep (se 1 (by rfl) ⟨1411793, by rfl⟩ : syracuseStep 1882391 = 2823587) B2823587
theorem B3176779 : Blo 1254445 3176779 := bstep (se 1 (by rfl) ⟨2382584, by rfl⟩ : syracuseStep 3176779 = 4765169) B4765169
theorem B2824523 : Blo 1254445 2824523 := bstep (se 1 (by rfl) ⟨2118392, by rfl⟩ : syracuseStep 2824523 = 4236785) B4236785
theorem B1882457 : Blo 1254445 1882457 := bstep (se 2 (by rfl) ⟨705921, by rfl⟩ : syracuseStep 1882457 = 1411843) B1411843
theorem B2824577 : Blo 1254445 2824577 := bstep (se 2 (by rfl) ⟨1059216, by rfl⟩ : syracuseStep 2824577 = 2118433) B2118433
theorem B2120087 : Blo 1254445 2120087 := bstep (se 1 (by rfl) ⟨1590065, by rfl⟩ : syracuseStep 2120087 = 3180131) B3180131
theorem B1882571 : Blo 1254445 1882571 := bstep (se 1 (by rfl) ⟨1411928, by rfl⟩ : syracuseStep 1882571 = 2823857) B2823857
theorem B1882583 : Blo 1254445 1882583 := bstep (se 1 (by rfl) ⟨1411937, by rfl⟩ : syracuseStep 1882583 = 2823875) B2823875
theorem B3176921 : Blo 1254445 3176921 := bstep (se 2 (by rfl) ⟨1191345, by rfl⟩ : syracuseStep 3176921 = 2382691) B2382691
theorem B2120215 : Blo 1254445 2120215 := bstep (se 1 (by rfl) ⟨1590161, by rfl⟩ : syracuseStep 2120215 = 3180323) B3180323
theorem B1882649 : Blo 1254445 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B2824793 : Blo 1254445 2824793 := bstep (se 2 (by rfl) ⟨1059297, by rfl⟩ : syracuseStep 2824793 = 2118595) B2118595
theorem B1882763 : Blo 1254445 1882763 := bstep (se 1 (by rfl) ⟨1412072, by rfl⟩ : syracuseStep 1882763 = 2824145) B2824145
theorem B1587863 : Blo 1254445 1587863 := bstep (se 1 (by rfl) ⟨1190897, by rfl⟩ : syracuseStep 1587863 = 2381795) B2381795
theorem B1882775 : Blo 1254445 1882775 := bstep (se 1 (by rfl) ⟨1412081, by rfl⟩ : syracuseStep 1882775 = 2824163) B2824163
theorem B2824883 : Blo 1254445 2824883 := bstep (se 1 (by rfl) ⟨2118662, by rfl⟩ : syracuseStep 2824883 = 4237325) B4237325
theorem B2824919 : Blo 1254445 2824919 := bstep (se 1 (by rfl) ⟨2118689, by rfl⟩ : syracuseStep 2824919 = 4237379) B4237379
theorem B1882841 : Blo 1254445 1882841 := bstep (se 2 (by rfl) ⟨706065, by rfl⟩ : syracuseStep 1882841 = 1412131) B1412131
theorem B1882955 : Blo 1254445 1882955 := bstep (se 1 (by rfl) ⟨1412216, by rfl⟩ : syracuseStep 1882955 = 2824433) B2824433
theorem B1882967 : Blo 1254445 1882967 := bstep (se 1 (by rfl) ⟨1412225, by rfl⟩ : syracuseStep 1882967 = 2824451) B2824451
theorem B7633757 : Blo 1254445 7633757 := bstep (se 3 (by rfl) ⟨1431329, by rfl⟩ : syracuseStep 7633757 = 2862659) B2862659
theorem B32635747 : Blo 1254445 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B2825099 : Blo 1254445 2825099 := bstep (se 1 (by rfl) ⟨2118824, by rfl⟩ : syracuseStep 2825099 = 4237649) B4237649
theorem B1883033 : Blo 1254445 1883033 := bstep (se 2 (by rfl) ⟨706137, by rfl⟩ : syracuseStep 1883033 = 1412275) B1412275
theorem B2825153 : Blo 1254445 2825153 := bstep (se 2 (by rfl) ⟨1059432, by rfl⟩ : syracuseStep 2825153 = 2118865) B2118865
theorem B81476549 : Blo 1254445 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1883147 : Blo 1254445 1883147 := bstep (se 1 (by rfl) ⟨1412360, by rfl⟩ : syracuseStep 1883147 = 2824721) B2824721
theorem B1883159 : Blo 1254445 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B4766795 : Blo 1254445 4766795 := bstep (se 1 (by rfl) ⟨3575096, by rfl⟩ : syracuseStep 4766795 = 7150193) B7150193
theorem B4766809 : Blo 1254445 4766809 := bstep (se 2 (by rfl) ⟨1787553, by rfl⟩ : syracuseStep 4766809 = 3575107) B3575107
theorem B1883225 : Blo 1254445 1883225 := bstep (se 2 (by rfl) ⟨706209, by rfl⟩ : syracuseStep 1883225 = 1412419) B1412419
theorem B2825369 : Blo 1254445 2825369 := bstep (se 2 (by rfl) ⟨1059513, by rfl⟩ : syracuseStep 2825369 = 2119027) B2119027
theorem B1883339 : Blo 1254445 1883339 := bstep (se 1 (by rfl) ⟨1412504, by rfl⟩ : syracuseStep 1883339 = 2825009) B2825009
theorem B1883351 : Blo 1254445 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B2825459 : Blo 1254445 2825459 := bstep (se 1 (by rfl) ⟨2119094, by rfl⟩ : syracuseStep 2825459 = 4238189) B4238189
theorem B3177751 : Blo 1254445 3177751 := bstep (se 1 (by rfl) ⟨2383313, by rfl⟩ : syracuseStep 3177751 = 4766627) B4766627
theorem B2825495 : Blo 1254445 2825495 := bstep (se 1 (by rfl) ⟨2119121, by rfl⟩ : syracuseStep 2825495 = 4238243) B4238243
theorem B1883417 : Blo 1254445 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B4234571 : Blo 1254445 4234571 := bstep (se 1 (by rfl) ⟨3175928, by rfl⟩ : syracuseStep 4234571 = 6351857) B6351857
theorem B1588567 : Blo 1254445 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B6438275 : Blo 1254445 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B1883531 : Blo 1254445 1883531 := bstep (se 1 (by rfl) ⟨1412648, by rfl⟩ : syracuseStep 1883531 = 2825297) B2825297
theorem B1883543 : Blo 1254445 1883543 := bstep (se 1 (by rfl) ⟨1412657, by rfl⟩ : syracuseStep 1883543 = 2825315) B2825315
theorem B2383283 : Blo 1254445 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B2825675 : Blo 1254445 2825675 := bstep (se 1 (by rfl) ⟨2119256, by rfl⟩ : syracuseStep 2825675 = 4238513) B4238513
theorem B1883609 : Blo 1254445 1883609 := bstep (se 2 (by rfl) ⟨706353, by rfl⟩ : syracuseStep 1883609 = 1412707) B1412707
theorem B2825729 : Blo 1254445 2825729 := bstep (se 2 (by rfl) ⟨1059648, by rfl⟩ : syracuseStep 2825729 = 2119297) B2119297
theorem B3391051 : Blo 1254445 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B2383435 : Blo 1254445 2383435 := bstep (se 1 (by rfl) ⟨1787576, by rfl⟩ : syracuseStep 2383435 = 3575153) B3575153
theorem B6356555 : Blo 1254445 6356555 := bstep (se 1 (by rfl) ⟨4767416, by rfl⟩ : syracuseStep 6356555 = 9534833) B9534833
theorem B1883723 : Blo 1254445 1883723 := bstep (se 1 (by rfl) ⟨1412792, by rfl⟩ : syracuseStep 1883723 = 2825585) B2825585
theorem B1883735 : Blo 1254445 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B4234841 : Blo 1254445 4234841 := bstep (se 2 (by rfl) ⟨1588065, by rfl⟩ : syracuseStep 4234841 = 3176131) B3176131
theorem B5365379 : Blo 1254445 5365379 := bstep (se 1 (by rfl) ⟨4024034, by rfl⟩ : syracuseStep 5365379 = 8048069) B8048069
theorem B1883801 : Blo 1254445 1883801 := bstep (se 2 (by rfl) ⟨706425, by rfl⟩ : syracuseStep 1883801 = 1412851) B1412851
theorem B11460275 : Blo 1254445 11460275 := bstep (se 1 (by rfl) ⟨8595206, by rfl⟩ : syracuseStep 11460275 = 17190413) B17190413
theorem B3178187 : Blo 1254445 3178187 := bstep (se 1 (by rfl) ⟨2383640, by rfl⟩ : syracuseStep 3178187 = 4767281) B4767281
theorem B2825945 : Blo 1254445 2825945 := bstep (se 2 (by rfl) ⟨1059729, by rfl⟩ : syracuseStep 2825945 = 2119459) B2119459
theorem B1883915 : Blo 1254445 1883915 := bstep (se 1 (by rfl) ⟨1412936, by rfl⟩ : syracuseStep 1883915 = 2825873) B2825873
theorem B9527057 : Blo 1254445 9527057 := bstep (se 2 (by rfl) ⟨3572646, by rfl⟩ : syracuseStep 9527057 = 7145293) B7145293
theorem B1883927 : Blo 1254445 1883927 := bstep (se 1 (by rfl) ⟨1412945, by rfl⟩ : syracuseStep 1883927 = 2825891) B2825891
theorem B2826035 : Blo 1254445 2826035 := bstep (se 1 (by rfl) ⟨2119526, by rfl⟩ : syracuseStep 2826035 = 4239053) B4239053
theorem B2826071 : Blo 1254445 2826071 := bstep (se 1 (by rfl) ⟨2119553, by rfl⟩ : syracuseStep 2826071 = 4239107) B4239107
theorem B1883993 : Blo 1254445 1883993 := bstep (se 2 (by rfl) ⟨706497, by rfl⟩ : syracuseStep 1883993 = 1412995) B1412995
theorem B1359703 : Blo 1254445 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B6029149 : Blo 1254445 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B2260889 : Blo 1254445 2260889 := bstep (se 2 (by rfl) ⟨847833, by rfl⟩ : syracuseStep 2260889 = 1695667) B1695667
theorem B2383769 : Blo 1254445 2383769 := bstep (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) B1787827
theorem B18087857 : Blo 1254445 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B25755569 : Blo 1254445 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B1884107 : Blo 1254445 1884107 := bstep (se 1 (by rfl) ⟨1413080, by rfl⟩ : syracuseStep 1884107 = 2826161) B2826161
theorem B1884119 : Blo 1254445 1884119 := bstep (se 1 (by rfl) ⟨1413089, by rfl⟩ : syracuseStep 1884119 = 2826179) B2826179
theorem B8044505 : Blo 1254445 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B1884167 : Blo 1254445 1884167 := bstep (se 1 (by rfl) ⟨1413125, by rfl⟩ : syracuseStep 1884167 = 2826251) B2826251
theorem B3178511 : Blo 1254445 3178511 := bstep (se 1 (by rfl) ⟨2383883, by rfl⟩ : syracuseStep 3178511 = 4767767) B4767767
theorem B1884203 : Blo 1254445 1884203 := bstep (se 1 (by rfl) ⟨1413152, by rfl⟩ : syracuseStep 1884203 = 2826305) B2826305
theorem B40714285 : Blo 1254445 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B1884233 : Blo 1254445 1884233 := bstep (se 2 (by rfl) ⟨706587, by rfl⟩ : syracuseStep 1884233 = 1413175) B1413175
theorem B2826359 : Blo 1254445 2826359 := bstep (se 1 (by rfl) ⟨2119769, by rfl⟩ : syracuseStep 2826359 = 4239539) B4239539
theorem B2416787 : Blo 1254445 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1884347 : Blo 1254445 1884347 := bstep (se 1 (by rfl) ⟨1413260, by rfl⟩ : syracuseStep 1884347 = 2826521) B2826521
theorem B1884407 : Blo 1254445 1884407 := bstep (se 1 (by rfl) ⟨1413305, by rfl⟩ : syracuseStep 1884407 = 2826611) B2826611
theorem B1884431 : Blo 1254445 1884431 := bstep (se 1 (by rfl) ⟨1413323, by rfl⟩ : syracuseStep 1884431 = 2826647) B2826647
theorem B12230929 : Blo 1254445 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B4022561 : Blo 1254445 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B2826539 : Blo 1254445 2826539 := bstep (se 1 (by rfl) ⟨2119904, by rfl⟩ : syracuseStep 2826539 = 4239809) B4239809
theorem B1884473 : Blo 1254445 1884473 := bstep (se 2 (by rfl) ⟨706677, by rfl⟩ : syracuseStep 1884473 = 1413355) B1413355
theorem B1884551 : Blo 1254445 1884551 := bstep (se 1 (by rfl) ⟨1413413, by rfl⟩ : syracuseStep 1884551 = 2826827) B2826827
theorem B1884587 : Blo 1254445 1884587 := bstep (se 1 (by rfl) ⟨1413440, by rfl⟩ : syracuseStep 1884587 = 2826881) B2826881
theorem B4235705 : Blo 1254445 4235705 := bstep (se 2 (by rfl) ⟨1588389, by rfl⟩ : syracuseStep 4235705 = 3176779) B3176779
theorem B4022713 : Blo 1254445 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B1884617 : Blo 1254445 1884617 := bstep (se 2 (by rfl) ⟨706731, by rfl⟩ : syracuseStep 1884617 = 1413463) B1413463
theorem B19325425 : Blo 1254445 19325425 := bstep (se 2 (by rfl) ⟨7247034, by rfl⟩ : syracuseStep 19325425 = 14494069) B14494069
theorem B4768267 : Blo 1254445 4768267 := bstep (se 1 (by rfl) ⟨3576200, by rfl⟩ : syracuseStep 4768267 = 7152401) B7152401
theorem B6357527 : Blo 1254445 6357527 := bstep (se 1 (by rfl) ⟨4768145, by rfl⟩ : syracuseStep 6357527 = 9536291) B9536291
theorem B2826899 : Blo 1254445 2826899 := bstep (se 1 (by rfl) ⟨2120174, by rfl⟩ : syracuseStep 2826899 = 4240349) B4240349
theorem B3179209 : Blo 1254445 3179209 := bstep (se 2 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 3179209 = 2384407) B2384407
theorem B2826953 : Blo 1254445 2826953 := bstep (se 2 (by rfl) ⟨1060107, by rfl⟩ : syracuseStep 2826953 = 2120215) B2120215
theorem B24134435 : Blo 1254445 24134435 := bstep (se 1 (by rfl) ⟨18100826, by rfl⟩ : syracuseStep 24134435 = 36201653) B36201653
theorem B4768571 : Blo 1254445 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B3179351 : Blo 1254445 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B3392371 : Blo 1254445 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B6030227 : Blo 1254445 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B3818387 : Blo 1254445 3818387 := bstep (se 1 (by rfl) ⟨2863790, by rfl⟩ : syracuseStep 3818387 = 5727581) B5727581
theorem B1590187 : Blo 1254445 1590187 := bstep (se 1 (by rfl) ⟨1192640, by rfl⟩ : syracuseStep 1590187 = 2385281) B2385281
theorem B5358545 : Blo 1254445 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B3392513 : Blo 1254445 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B4236299 : Blo 1254445 4236299 := bstep (se 1 (by rfl) ⟨3177224, by rfl⟩ : syracuseStep 4236299 = 6354449) B6354449
theorem B4293661 : Blo 1254445 4293661 := bstep (se 3 (by rfl) ⟨805061, by rfl⟩ : syracuseStep 4293661 = 1610123) B1610123
theorem B6030379 : Blo 1254445 6030379 := bstep (se 1 (by rfl) ⟨4522784, by rfl⟩ : syracuseStep 6030379 = 9045569) B9045569
theorem B2384939 : Blo 1254445 2384939 := bstep (se 1 (by rfl) ⟨1788704, by rfl⟩ : syracuseStep 2384939 = 3577409) B3577409
theorem B1254459 : Blo 1254445 1254459 := bstep (se 1 (by rfl) ⟨940844, by rfl⟩ : syracuseStep 1254459 = 1881689) B1881689
theorem B6112343 : Blo 1254445 6112343 := bstep (se 1 (by rfl) ⟨4584257, by rfl⟩ : syracuseStep 6112343 = 9168515) B9168515
theorem B3015767 : Blo 1254445 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B4236407 : Blo 1254445 4236407 := bstep (se 1 (by rfl) ⟨3177305, by rfl⟩ : syracuseStep 4236407 = 6354611) B6354611
theorem B1254535 : Blo 1254445 1254535 := bstep (se 1 (by rfl) ⟨940901, by rfl⟩ : syracuseStep 1254535 = 1881803) B1881803
theorem B1254543 : Blo 1254445 1254543 := bstep (se 1 (by rfl) ⟨940907, by rfl⟩ : syracuseStep 1254543 = 1881815) B1881815
theorem B1254587 : Blo 1254445 1254587 := bstep (se 1 (by rfl) ⟨940940, by rfl⟩ : syracuseStep 1254587 = 1881881) B1881881
theorem B3818753 : Blo 1254445 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1254663 : Blo 1254445 1254663 := bstep (se 1 (by rfl) ⟨940997, by rfl⟩ : syracuseStep 1254663 = 1881995) B1881995
theorem B1254671 : Blo 1254445 1254671 := bstep (se 1 (by rfl) ⟨941003, by rfl⟩ : syracuseStep 1254671 = 1882007) B1882007
theorem B4769057 : Blo 1254445 4769057 := bstep (se 2 (by rfl) ⟨1788396, by rfl⟩ : syracuseStep 4769057 = 3576793) B3576793
theorem B3573035 : Blo 1254445 3573035 := bstep (se 1 (by rfl) ⟨2679776, by rfl⟩ : syracuseStep 3573035 = 5359553) B5359553
theorem B1254715 : Blo 1254445 1254715 := bstep (se 1 (by rfl) ⟨941036, by rfl⟩ : syracuseStep 1254715 = 1882073) B1882073
theorem B7144793 : Blo 1254445 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B13239683 : Blo 1254445 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B1254791 : Blo 1254445 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B1254799 : Blo 1254445 1254799 := bstep (se 1 (by rfl) ⟨941099, by rfl⟩ : syracuseStep 1254799 = 1882199) B1882199
theorem B1254843 : Blo 1254445 1254843 := bstep (se 1 (by rfl) ⟨941132, by rfl⟩ : syracuseStep 1254843 = 1882265) B1882265
theorem B1787383 : Blo 1254445 1787383 := bstep (se 1 (by rfl) ⟨1340537, by rfl⟩ : syracuseStep 1787383 = 2681075) B2681075
theorem B1254919 : Blo 1254445 1254919 := bstep (se 1 (by rfl) ⟨941189, by rfl⟩ : syracuseStep 1254919 = 1882379) B1882379
theorem B1254927 : Blo 1254445 1254927 := bstep (se 1 (by rfl) ⟨941195, by rfl⟩ : syracuseStep 1254927 = 1882391) B1882391
theorem B1254971 : Blo 1254445 1254971 := bstep (se 1 (by rfl) ⟨941228, by rfl⟩ : syracuseStep 1254971 = 1882457) B1882457
theorem B3393085 : Blo 1254445 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1255047 : Blo 1254445 1255047 := bstep (se 1 (by rfl) ⟨941285, by rfl⟩ : syracuseStep 1255047 = 1882571) B1882571
theorem B1255055 : Blo 1254445 1255055 := bstep (se 1 (by rfl) ⟨941291, by rfl⟩ : syracuseStep 1255055 = 1882583) B1882583
theorem B1255099 : Blo 1254445 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B10733249 : Blo 1254445 10733249 := bstep (se 2 (by rfl) ⟨4024968, by rfl⟩ : syracuseStep 10733249 = 8049937) B8049937
theorem B4294345 : Blo 1254445 4294345 := bstep (se 2 (by rfl) ⟨1610379, by rfl⟩ : syracuseStep 4294345 = 3220759) B3220759
theorem B4237001 : Blo 1254445 4237001 := bstep (se 2 (by rfl) ⟨1588875, by rfl⟩ : syracuseStep 4237001 = 3177751) B3177751
theorem B1255175 : Blo 1254445 1255175 := bstep (se 1 (by rfl) ⟨941381, by rfl⟩ : syracuseStep 1255175 = 1882763) B1882763
theorem B1255183 : Blo 1254445 1255183 := bstep (se 1 (by rfl) ⟨941387, by rfl⟩ : syracuseStep 1255183 = 1882775) B1882775
theorem B1255227 : Blo 1254445 1255227 := bstep (se 1 (by rfl) ⟨941420, by rfl⟩ : syracuseStep 1255227 = 1882841) B1882841
theorem B1255303 : Blo 1254445 1255303 := bstep (se 1 (by rfl) ⟨941477, by rfl⟩ : syracuseStep 1255303 = 1882955) B1882955
theorem B1255311 : Blo 1254445 1255311 := bstep (se 1 (by rfl) ⟨941483, by rfl⟩ : syracuseStep 1255311 = 1882967) B1882967
theorem B5089171 : Blo 1254445 5089171 := bstep (se 1 (by rfl) ⟨3816878, by rfl⟩ : syracuseStep 5089171 = 7633757) B7633757
theorem B3016595 : Blo 1254445 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B1255355 : Blo 1254445 1255355 := bstep (se 1 (by rfl) ⟨941516, by rfl⟩ : syracuseStep 1255355 = 1883033) B1883033
theorem B1255431 : Blo 1254445 1255431 := bstep (se 1 (by rfl) ⟨941573, by rfl⟩ : syracuseStep 1255431 = 1883147) B1883147
theorem B1255439 : Blo 1254445 1255439 := bstep (se 1 (by rfl) ⟨941579, by rfl⟩ : syracuseStep 1255439 = 1883159) B1883159
theorem B1255483 : Blo 1254445 1255483 := bstep (se 1 (by rfl) ⟨941612, by rfl⟩ : syracuseStep 1255483 = 1883225) B1883225
theorem B3573821 : Blo 1254445 3573821 := bstep (se 3 (by rfl) ⟨670091, by rfl⟩ : syracuseStep 3573821 = 1340183) B1340183
theorem B1255559 : Blo 1254445 1255559 := bstep (se 1 (by rfl) ⟨941669, by rfl⟩ : syracuseStep 1255559 = 1883339) B1883339
theorem B1255567 : Blo 1254445 1255567 := bstep (se 1 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 1255567 = 1883351) B1883351
theorem B1255611 : Blo 1254445 1255611 := bstep (se 1 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 1255611 = 1883417) B1883417
theorem B4770029 : Blo 1254445 4770029 := bstep (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) B1788761
theorem B22898933 : Blo 1254445 22898933 := bstep (se 5 (by rfl) ⟨1073387, by rfl⟩ : syracuseStep 22898933 = 2146775) B2146775
theorem B1255687 : Blo 1254445 1255687 := bstep (se 1 (by rfl) ⟨941765, by rfl⟩ : syracuseStep 1255687 = 1883531) B1883531
theorem B1255695 : Blo 1254445 1255695 := bstep (se 1 (by rfl) ⟨941771, by rfl⟩ : syracuseStep 1255695 = 1883543) B1883543
theorem B1788203 : Blo 1254445 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B1255739 : Blo 1254445 1255739 := bstep (se 1 (by rfl) ⟨941804, by rfl⟩ : syracuseStep 1255739 = 1883609) B1883609
theorem B3574151 : Blo 1254445 3574151 := bstep (se 1 (by rfl) ⟨2680613, by rfl⟩ : syracuseStep 3574151 = 5361227) B5361227
theorem B4237703 : Blo 1254445 4237703 := bstep (se 1 (by rfl) ⟨3178277, by rfl⟩ : syracuseStep 4237703 = 6356555) B6356555
theorem B1255815 : Blo 1254445 1255815 := bstep (se 1 (by rfl) ⟨941861, by rfl⟩ : syracuseStep 1255815 = 1883723) B1883723
theorem B1255823 : Blo 1254445 1255823 := bstep (se 1 (by rfl) ⟨941867, by rfl⟩ : syracuseStep 1255823 = 1883735) B1883735
theorem B1255867 : Blo 1254445 1255867 := bstep (se 1 (by rfl) ⟨941900, by rfl⟩ : syracuseStep 1255867 = 1883801) B1883801
theorem B1812937 : Blo 1254445 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B8038865 : Blo 1254445 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B1411591 : Blo 1254445 1411591 := bstep (se 1 (by rfl) ⟨1058693, by rfl⟩ : syracuseStep 1411591 = 2117387) B2117387
theorem B1255943 : Blo 1254445 1255943 := bstep (se 1 (by rfl) ⟨941957, by rfl⟩ : syracuseStep 1255943 = 1883915) B1883915
theorem B6351371 : Blo 1254445 6351371 := bstep (se 1 (by rfl) ⟨4763528, by rfl⟩ : syracuseStep 6351371 = 9527057) B9527057
theorem B1255951 : Blo 1254445 1255951 := bstep (se 1 (by rfl) ⟨941963, by rfl⟩ : syracuseStep 1255951 = 1883927) B1883927
theorem B1255995 : Blo 1254445 1255995 := bstep (se 1 (by rfl) ⟨941996, by rfl⟩ : syracuseStep 1255995 = 1883993) B1883993
theorem B1256071 : Blo 1254445 1256071 := bstep (se 1 (by rfl) ⟨942053, by rfl⟩ : syracuseStep 1256071 = 1884107) B1884107
theorem B1256079 : Blo 1254445 1256079 := bstep (se 1 (by rfl) ⟨942059, by rfl⟩ : syracuseStep 1256079 = 1884119) B1884119
theorem B2263699 : Blo 1254445 2263699 := bstep (se 1 (by rfl) ⟨1697774, by rfl⟩ : syracuseStep 2263699 = 3395549) B3395549
theorem B6351533 : Blo 1254445 6351533 := bstep (se 3 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 6351533 = 2381825) B2381825
theorem B1411771 : Blo 1254445 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B1256123 : Blo 1254445 1256123 := bstep (se 1 (by rfl) ⟨942092, by rfl⟩ : syracuseStep 1256123 = 1884185) B1884185
theorem B4238081 : Blo 1254445 4238081 := bstep (se 2 (by rfl) ⟨1589280, by rfl⟩ : syracuseStep 4238081 = 3178561) B3178561
theorem B1256199 : Blo 1254445 1256199 := bstep (se 1 (by rfl) ⟨942149, by rfl⟩ : syracuseStep 1256199 = 1884299) B1884299
theorem B1256207 : Blo 1254445 1256207 := bstep (se 1 (by rfl) ⟨942155, by rfl⟩ : syracuseStep 1256207 = 1884311) B1884311
theorem B1256251 : Blo 1254445 1256251 := bstep (se 1 (by rfl) ⟨942188, by rfl⟩ : syracuseStep 1256251 = 1884377) B1884377
theorem B7154567 : Blo 1254445 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B1256327 : Blo 1254445 1256327 := bstep (se 1 (by rfl) ⟨942245, by rfl⟩ : syracuseStep 1256327 = 1884491) B1884491
theorem B1256335 : Blo 1254445 1256335 := bstep (se 1 (by rfl) ⟨942251, by rfl⟩ : syracuseStep 1256335 = 1884503) B1884503
theorem B1256379 : Blo 1254445 1256379 := bstep (se 1 (by rfl) ⟨942284, by rfl⟩ : syracuseStep 1256379 = 1884569) B1884569
theorem B5229521 : Blo 1254445 5229521 := bstep (se 2 (by rfl) ⟨1961070, by rfl⟩ : syracuseStep 5229521 = 3922141) B3922141
theorem B1412239 : Blo 1254445 1412239 := bstep (se 1 (by rfl) ⟨1059179, by rfl⟩ : syracuseStep 1412239 = 2118359) B2118359
theorem B9055547 : Blo 1254445 9055547 := bstep (se 1 (by rfl) ⟨6791660, by rfl⟩ : syracuseStep 9055547 = 13583321) B13583321
theorem B6032825 : Blo 1254445 6032825 := bstep (se 2 (by rfl) ⟨2262309, by rfl⟩ : syracuseStep 6032825 = 4524619) B4524619
theorem B6360605 : Blo 1254445 6360605 := bstep (se 3 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 6360605 = 2385227) B2385227
theorem B4238891 : Blo 1254445 4238891 := bstep (se 1 (by rfl) ⟨3179168, by rfl⟩ : syracuseStep 4238891 = 6358337) B6358337
theorem B1412743 : Blo 1254445 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B2682553 : Blo 1254445 2682553 := bstep (se 2 (by rfl) ⟨1005957, by rfl⟩ : syracuseStep 2682553 = 2011915) B2011915
theorem B4763393 : Blo 1254445 4763393 := bstep (se 2 (by rfl) ⟨1786272, by rfl⟩ : syracuseStep 4763393 = 3572545) B3572545
theorem B4763407 : Blo 1254445 4763407 := bstep (se 1 (by rfl) ⟨3572555, by rfl⟩ : syracuseStep 4763407 = 7145111) B7145111
theorem B7630625 : Blo 1254445 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B1412923 : Blo 1254445 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B4353907 : Blo 1254445 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B2117495 : Blo 1254445 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B2682895 : Blo 1254445 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B7155773 : Blo 1254445 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B3575927 : Blo 1254445 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B6353153 : Blo 1254445 6353153 := bstep (se 2 (by rfl) ⟨2382432, by rfl⟩ : syracuseStep 6353153 = 4764865) B4764865
theorem B1413391 : Blo 1254445 1413391 := bstep (se 1 (by rfl) ⟨1060043, by rfl⟩ : syracuseStep 1413391 = 2120087) B2120087
theorem B2117947 : Blo 1254445 2117947 := bstep (se 1 (by rfl) ⟨1588460, by rfl⟩ : syracuseStep 2117947 = 3176921) B3176921
theorem B2118089 : Blo 1254445 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B2011691 : Blo 1254445 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B54317699 : Blo 1254445 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B7631617 : Blo 1254445 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B7639841 : Blo 1254445 7639841 := bstep (se 2 (by rfl) ⟨2864940, by rfl⟩ : syracuseStep 7639841 = 5729881) B5729881
theorem B4240187 : Blo 1254445 4240187 := bstep (se 1 (by rfl) ⟨3180140, by rfl⟩ : syracuseStep 4240187 = 6360281) B6360281
theorem B2012023 : Blo 1254445 2012023 := bstep (se 1 (by rfl) ⟨1509017, by rfl⟩ : syracuseStep 2012023 = 3018035) B3018035
theorem B2823047 : Blo 1254445 2823047 := bstep (se 1 (by rfl) ⟨2117285, by rfl⟩ : syracuseStep 2823047 = 4234571) B4234571
theorem B3175321 : Blo 1254445 3175321 := bstep (se 2 (by rfl) ⟨1190745, by rfl⟩ : syracuseStep 3175321 = 2381491) B2381491
theorem B27898805 : Blo 1254445 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B4764683 : Blo 1254445 4764683 := bstep (se 1 (by rfl) ⟨3573512, by rfl⟩ : syracuseStep 4764683 = 7147025) B7147025
theorem B2716687 : Blo 1254445 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B6353963 : Blo 1254445 6353963 := bstep (se 1 (by rfl) ⟨4765472, by rfl⟩ : syracuseStep 6353963 = 9530945) B9530945
theorem B3175483 : Blo 1254445 3175483 := bstep (se 1 (by rfl) ⟨2381612, by rfl⟩ : syracuseStep 3175483 = 4763225) B4763225
theorem B2823227 : Blo 1254445 2823227 := bstep (se 1 (by rfl) ⟨2117420, by rfl⟩ : syracuseStep 2823227 = 4234841) B4234841
theorem B3576919 : Blo 1254445 3576919 := bstep (se 1 (by rfl) ⟨2682689, by rfl⟩ : syracuseStep 3576919 = 5365379) B5365379
theorem B7640183 : Blo 1254445 7640183 := bstep (se 1 (by rfl) ⟨5730137, by rfl⟩ : syracuseStep 7640183 = 11460275) B11460275
theorem B2118791 : Blo 1254445 2118791 := bstep (se 1 (by rfl) ⟨1589093, by rfl⟩ : syracuseStep 2118791 = 3178187) B3178187
theorem B2823353 : Blo 1254445 2823353 := bstep (se 2 (by rfl) ⟨1058757, by rfl⟩ : syracuseStep 2823353 = 2117515) B2117515
theorem B3175625 : Blo 1254445 3175625 := bstep (se 2 (by rfl) ⟨1190859, by rfl⟩ : syracuseStep 3175625 = 2381719) B2381719
theorem B4527341 : Blo 1254445 4527341 := bstep (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) B1697753
theorem B5363003 : Blo 1254445 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B6034823 : Blo 1254445 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B6116755 : Blo 1254445 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B4077067 : Blo 1254445 4077067 := bstep (se 1 (by rfl) ⟨3057800, by rfl⟩ : syracuseStep 4077067 = 6115601) B6115601
theorem B2823695 : Blo 1254445 2823695 := bstep (se 1 (by rfl) ⟨2117771, by rfl⟩ : syracuseStep 2823695 = 4235543) B4235543
theorem B3175969 : Blo 1254445 3175969 := bstep (se 2 (by rfl) ⟨1190988, by rfl⟩ : syracuseStep 3175969 = 2381977) B2381977
theorem B2823713 : Blo 1254445 2823713 := bstep (se 2 (by rfl) ⟨1058892, by rfl⟩ : syracuseStep 2823713 = 2117785) B2117785
theorem B5363243 : Blo 1254445 5363243 := bstep (se 1 (by rfl) ⟨4022432, by rfl⟩ : syracuseStep 5363243 = 8044865) B8044865
theorem B1881719 : Blo 1254445 1881719 := bstep (se 1 (by rfl) ⟨1411289, by rfl⟩ : syracuseStep 1881719 = 2822579) B2822579
theorem B1881743 : Blo 1254445 1881743 := bstep (se 1 (by rfl) ⟨1411307, by rfl⟩ : syracuseStep 1881743 = 2822615) B2822615
theorem B1881785 : Blo 1254445 1881785 := bstep (se 2 (by rfl) ⟨705669, by rfl⟩ : syracuseStep 1881785 = 1411339) B1411339
theorem B1881863 : Blo 1254445 1881863 := bstep (se 1 (by rfl) ⟨1411397, by rfl⟩ : syracuseStep 1881863 = 2822795) B2822795
theorem B2119439 : Blo 1254445 2119439 := bstep (se 1 (by rfl) ⟨1589579, by rfl⟩ : syracuseStep 2119439 = 3179159) B3179159
theorem B14292773 : Blo 1254445 14292773 := bstep (se 4 (by rfl) ⟨1339947, by rfl⟩ : syracuseStep 14292773 = 2679895) B2679895
theorem B1881899 : Blo 1254445 1881899 := bstep (se 1 (by rfl) ⟨1411424, by rfl⟩ : syracuseStep 1881899 = 2822849) B2822849
theorem B1881929 : Blo 1254445 1881929 := bstep (se 2 (by rfl) ⟨705723, by rfl⟩ : syracuseStep 1881929 = 1411447) B1411447
theorem B2824055 : Blo 1254445 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B4528007 : Blo 1254445 4528007 := bstep (se 1 (by rfl) ⟨3396005, by rfl⟩ : syracuseStep 4528007 = 6792011) B6792011
theorem B5363603 : Blo 1254445 5363603 := bstep (se 1 (by rfl) ⟨4022702, by rfl⟩ : syracuseStep 5363603 = 8045405) B8045405
theorem B4765625 : Blo 1254445 4765625 := bstep (se 2 (by rfl) ⟨1787109, by rfl⟩ : syracuseStep 4765625 = 3574219) B3574219
theorem B1882043 : Blo 1254445 1882043 := bstep (se 1 (by rfl) ⟨1411532, by rfl⟩ : syracuseStep 1882043 = 2823065) B2823065
theorem B1882103 : Blo 1254445 1882103 := bstep (se 1 (by rfl) ⟨1411577, by rfl⟩ : syracuseStep 1882103 = 2823155) B2823155
theorem B1882127 : Blo 1254445 1882127 := bstep (se 1 (by rfl) ⟨1411595, by rfl⟩ : syracuseStep 1882127 = 2823191) B2823191
theorem B2824235 : Blo 1254445 2824235 := bstep (se 1 (by rfl) ⟨2118176, by rfl⟩ : syracuseStep 2824235 = 4236353) B4236353
theorem B15276077 : Blo 1254445 15276077 := bstep (se 3 (by rfl) ⟨2864264, by rfl⟩ : syracuseStep 15276077 = 5728529) B5728529
theorem B1882169 : Blo 1254445 1882169 := bstep (se 2 (by rfl) ⟨705813, by rfl⟩ : syracuseStep 1882169 = 1411627) B1411627
theorem B3176567 : Blo 1254445 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B12236933 : Blo 1254445 12236933 := bstep (se 4 (by rfl) ⟨1147212, by rfl⟩ : syracuseStep 12236933 = 2294425) B2294425
theorem B1882247 : Blo 1254445 1882247 := bstep (se 1 (by rfl) ⟨1411685, by rfl⟩ : syracuseStep 1882247 = 2823371) B2823371
theorem B2865287 : Blo 1254445 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B1882283 : Blo 1254445 1882283 := bstep (se 1 (by rfl) ⟨1411712, by rfl⟩ : syracuseStep 1882283 = 2823425) B2823425
theorem B1882313 : Blo 1254445 1882313 := bstep (se 2 (by rfl) ⟨705867, by rfl⟩ : syracuseStep 1882313 = 1411735) B1411735
theorem B7346465 : Blo 1254445 7346465 := bstep (se 2 (by rfl) ⟨2754924, by rfl⟩ : syracuseStep 7346465 = 5509849) B5509849
theorem B2119979 : Blo 1254445 2119979 := bstep (se 1 (by rfl) ⟨1589984, by rfl⟩ : syracuseStep 2119979 = 3179969) B3179969
theorem B1882427 : Blo 1254445 1882427 := bstep (se 1 (by rfl) ⟨1411820, by rfl⟩ : syracuseStep 1882427 = 2823641) B2823641
theorem B6355259 : Blo 1254445 6355259 := bstep (se 1 (by rfl) ⟨4766444, by rfl⟩ : syracuseStep 6355259 = 9532889) B9532889
theorem B1882487 : Blo 1254445 1882487 := bstep (se 1 (by rfl) ⟨1411865, by rfl⟩ : syracuseStep 1882487 = 2823731) B2823731
theorem B1882511 : Blo 1254445 1882511 := bstep (se 1 (by rfl) ⟨1411883, by rfl⟩ : syracuseStep 1882511 = 2823767) B2823767
theorem B2824595 : Blo 1254445 2824595 := bstep (se 1 (by rfl) ⟨2118446, by rfl⟩ : syracuseStep 2824595 = 4236893) B4236893
theorem B1882553 : Blo 1254445 1882553 := bstep (se 2 (by rfl) ⟨705957, by rfl⟩ : syracuseStep 1882553 = 1411915) B1411915
theorem B2382281 : Blo 1254445 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B2824649 : Blo 1254445 2824649 := bstep (se 2 (by rfl) ⟨1059243, by rfl⟩ : syracuseStep 2824649 = 2118487) B2118487
theorem B6035915 : Blo 1254445 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B43514329 : Blo 1254445 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B6355421 : Blo 1254445 6355421 := bstep (se 3 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 6355421 = 2383283) B2383283
theorem B1882631 : Blo 1254445 1882631 := bstep (se 1 (by rfl) ⟨1411973, by rfl⟩ : syracuseStep 1882631 = 2823947) B2823947
theorem B1882667 : Blo 1254445 1882667 := bstep (se 1 (by rfl) ⟨1412000, by rfl⟩ : syracuseStep 1882667 = 2824001) B2824001
theorem B1882697 : Blo 1254445 1882697 := bstep (se 2 (by rfl) ⟨706011, by rfl⟩ : syracuseStep 1882697 = 1412023) B1412023
theorem B4233815 : Blo 1254445 4233815 := bstep (se 1 (by rfl) ⟨3175361, by rfl⟩ : syracuseStep 4233815 = 6350723) B6350723
theorem B1882811 : Blo 1254445 1882811 := bstep (se 1 (by rfl) ⟨1412108, by rfl⟩ : syracuseStep 1882811 = 2824217) B2824217
theorem B1882871 : Blo 1254445 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B1882895 : Blo 1254445 1882895 := bstep (se 1 (by rfl) ⟨1412171, by rfl⟩ : syracuseStep 1882895 = 2824343) B2824343
theorem B6355745 : Blo 1254445 6355745 := bstep (se 2 (by rfl) ⟨2383404, by rfl⟩ : syracuseStep 6355745 = 4766809) B4766809
theorem B1882937 : Blo 1254445 1882937 := bstep (se 2 (by rfl) ⟨706101, by rfl⟩ : syracuseStep 1882937 = 1412203) B1412203
theorem B1883015 : Blo 1254445 1883015 := bstep (se 1 (by rfl) ⟨1412261, by rfl⟩ : syracuseStep 1883015 = 2824523) B2824523
theorem B1883051 : Blo 1254445 1883051 := bstep (se 1 (by rfl) ⟨1412288, by rfl⟩ : syracuseStep 1883051 = 2824577) B2824577
theorem B1883081 : Blo 1254445 1883081 := bstep (se 2 (by rfl) ⟨706155, by rfl⟩ : syracuseStep 1883081 = 1412311) B1412311
theorem B4291613 : Blo 1254445 4291613 := bstep (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) B1609355
theorem B1883195 : Blo 1254445 1883195 := bstep (se 1 (by rfl) ⟨1412396, by rfl⟩ : syracuseStep 1883195 = 2824793) B2824793
theorem B4234301 : Blo 1254445 4234301 := bstep (se 3 (by rfl) ⟨793931, by rfl⟩ : syracuseStep 4234301 = 1587863) B1587863
theorem B1883255 : Blo 1254445 1883255 := bstep (se 1 (by rfl) ⟨1412441, by rfl⟩ : syracuseStep 1883255 = 2824883) B2824883
theorem B27909251 : Blo 1254445 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B2825351 : Blo 1254445 2825351 := bstep (se 1 (by rfl) ⟨2119013, by rfl⟩ : syracuseStep 2825351 = 4238027) B4238027
theorem B1883279 : Blo 1254445 1883279 := bstep (se 1 (by rfl) ⟨1412459, by rfl⟩ : syracuseStep 1883279 = 2824919) B2824919
theorem B2382995 : Blo 1254445 2382995 := bstep (se 1 (by rfl) ⟨1787246, by rfl⟩ : syracuseStep 2382995 = 3574493) B3574493
theorem B2383033 : Blo 1254445 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B1883321 : Blo 1254445 1883321 := bstep (se 2 (by rfl) ⟨706245, by rfl⟩ : syracuseStep 1883321 = 1412491) B1412491
theorem B1883399 : Blo 1254445 1883399 := bstep (se 1 (by rfl) ⟨1412549, by rfl⟩ : syracuseStep 1883399 = 2825099) B2825099
theorem B1883435 : Blo 1254445 1883435 := bstep (se 1 (by rfl) ⟨1412576, by rfl⟩ : syracuseStep 1883435 = 2825153) B2825153
theorem B2825531 : Blo 1254445 2825531 := bstep (se 1 (by rfl) ⟨2119148, by rfl⟩ : syracuseStep 2825531 = 4238297) B4238297
theorem B1883465 : Blo 1254445 1883465 := bstep (se 2 (by rfl) ⟨706299, by rfl⟩ : syracuseStep 1883465 = 1412599) B1412599
theorem B3177863 : Blo 1254445 3177863 := bstep (se 1 (by rfl) ⟨2383397, by rfl⟩ : syracuseStep 3177863 = 4766795) B4766795
theorem B4521401 : Blo 1254445 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B3177913 : Blo 1254445 3177913 := bstep (se 2 (by rfl) ⟨1191717, by rfl⟩ : syracuseStep 3177913 = 2383435) B2383435
theorem B1883579 : Blo 1254445 1883579 := bstep (se 1 (by rfl) ⟨1412684, by rfl⟩ : syracuseStep 1883579 = 2825369) B2825369
theorem B2825657 : Blo 1254445 2825657 := bstep (se 2 (by rfl) ⟨1059621, by rfl⟩ : syracuseStep 2825657 = 2119243) B2119243
theorem B1883639 : Blo 1254445 1883639 := bstep (se 1 (by rfl) ⟨1412729, by rfl⟩ : syracuseStep 1883639 = 2825459) B2825459
theorem B1883663 : Blo 1254445 1883663 := bstep (se 1 (by rfl) ⟨1412747, by rfl⟩ : syracuseStep 1883663 = 2825495) B2825495
theorem B1883705 : Blo 1254445 1883705 := bstep (se 2 (by rfl) ⟨706389, by rfl⟩ : syracuseStep 1883705 = 1412779) B1412779
theorem B4292183 : Blo 1254445 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B1883783 : Blo 1254445 1883783 := bstep (se 1 (by rfl) ⟨1412837, by rfl⟩ : syracuseStep 1883783 = 2825675) B2825675
theorem B1883819 : Blo 1254445 1883819 := bstep (se 1 (by rfl) ⟨1412864, by rfl⟩ : syracuseStep 1883819 = 2825729) B2825729
theorem B8822465 : Blo 1254445 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1883849 : Blo 1254445 1883849 := bstep (se 2 (by rfl) ⟨706443, by rfl⟩ : syracuseStep 1883849 = 1412887) B1412887
theorem B6356717 : Blo 1254445 6356717 := bstep (se 3 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 6356717 = 2383769) B2383769
theorem B2825999 : Blo 1254445 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B6438689 : Blo 1254445 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B2826017 : Blo 1254445 2826017 := bstep (se 2 (by rfl) ⟨1059756, by rfl⟩ : syracuseStep 2826017 = 2119513) B2119513
theorem B1883963 : Blo 1254445 1883963 := bstep (se 1 (by rfl) ⟨1412972, by rfl⟩ : syracuseStep 1883963 = 2825945) B2825945
theorem B1884023 : Blo 1254445 1884023 := bstep (se 1 (by rfl) ⟨1413017, by rfl⟩ : syracuseStep 1884023 = 2826035) B2826035
theorem B1884047 : Blo 1254445 1884047 := bstep (se 1 (by rfl) ⟨1413035, by rfl⟩ : syracuseStep 1884047 = 2826071) B2826071
theorem B1884089 : Blo 1254445 1884089 := bstep (se 2 (by rfl) ⟨706533, by rfl⟩ : syracuseStep 1884089 = 1413067) B1413067
theorem B1507259 : Blo 1254445 1507259 := bstep (se 1 (by rfl) ⟨1130444, by rfl⟩ : syracuseStep 1507259 = 2260889) B2260889
theorem B12058571 : Blo 1254445 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B17170379 : Blo 1254445 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B1884239 : Blo 1254445 1884239 := bstep (se 1 (by rfl) ⟨1413179, by rfl⟩ : syracuseStep 1884239 = 2826359) B2826359
theorem B4235435 : Blo 1254445 4235435 := bstep (se 1 (by rfl) ⟨3176576, by rfl⟩ : syracuseStep 4235435 = 6353153) B6353153
theorem B1884359 : Blo 1254445 1884359 := bstep (se 1 (by rfl) ⟨1413269, by rfl⟩ : syracuseStep 1884359 = 2826539) B2826539
theorem B32162021 : Blo 1254445 32162021 := bstep (se 4 (by rfl) ⟨3015189, by rfl⟩ : syracuseStep 32162021 = 6030379) B6030379
theorem B9535805 : Blo 1254445 9535805 := bstep (se 3 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 9535805 = 3575927) B3575927
theorem B1884521 : Blo 1254445 1884521 := bstep (se 2 (by rfl) ⟨706695, by rfl⟩ : syracuseStep 1884521 = 1413391) B1413391
theorem B1884599 : Blo 1254445 1884599 := bstep (se 1 (by rfl) ⟨1413449, by rfl⟩ : syracuseStep 1884599 = 2826899) B2826899
theorem B1884635 : Blo 1254445 1884635 := bstep (se 1 (by rfl) ⟨1413476, by rfl⟩ : syracuseStep 1884635 = 2826953) B2826953
theorem B16089623 : Blo 1254445 16089623 := bstep (se 1 (by rfl) ⟨12067217, by rfl⟩ : syracuseStep 16089623 = 24134435) B24134435
theorem B3179047 : Blo 1254445 3179047 := bstep (se 1 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 3179047 = 4768571) B4768571
theorem B2826791 : Blo 1254445 2826791 := bstep (se 1 (by rfl) ⟨2120093, by rfl⟩ : syracuseStep 2826791 = 4240187) B4240187
theorem B2417249 : Blo 1254445 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B3572363 : Blo 1254445 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B2261675 : Blo 1254445 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B6357689 : Blo 1254445 6357689 := bstep (se 2 (by rfl) ⟨2384133, by rfl⟩ : syracuseStep 6357689 = 4768267) B4768267
theorem B4235975 : Blo 1254445 4235975 := bstep (se 1 (by rfl) ⟨3176981, by rfl⟩ : syracuseStep 4235975 = 6353963) B6353963
theorem B1589959 : Blo 1254445 1589959 := bstep (se 1 (by rfl) ⟨1192469, by rfl⟩ : syracuseStep 1589959 = 2384939) B2384939
theorem B4768541 : Blo 1254445 4768541 := bstep (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) B1788203
theorem B3179371 : Blo 1254445 3179371 := bstep (se 1 (by rfl) ⟨2384528, by rfl⟩ : syracuseStep 3179371 = 4769057) B4769057
theorem B4023215 : Blo 1254445 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B10175489 : Blo 1254445 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B1254479 : Blo 1254445 1254479 := bstep (se 1 (by rfl) ⟨940859, by rfl⟩ : syracuseStep 1254479 = 1881719) B1881719
theorem B1254495 : Blo 1254445 1254495 := bstep (se 1 (by rfl) ⟨940871, by rfl⟩ : syracuseStep 1254495 = 1881743) B1881743
theorem B1254523 : Blo 1254445 1254523 := bstep (se 1 (by rfl) ⟨940892, by rfl⟩ : syracuseStep 1254523 = 1881785) B1881785
theorem B4523161 : Blo 1254445 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B1254575 : Blo 1254445 1254575 := bstep (se 1 (by rfl) ⟨940931, by rfl⟩ : syracuseStep 1254575 = 1881863) B1881863
theorem B9528515 : Blo 1254445 9528515 := bstep (se 1 (by rfl) ⟨7146386, by rfl⟩ : syracuseStep 9528515 = 14292773) B14292773
theorem B1254599 : Blo 1254445 1254599 := bstep (se 1 (by rfl) ⟨940949, by rfl⟩ : syracuseStep 1254599 = 1881899) B1881899
theorem B1254619 : Blo 1254445 1254619 := bstep (se 1 (by rfl) ⟨940964, by rfl⟩ : syracuseStep 1254619 = 1881929) B1881929
theorem B1254695 : Blo 1254445 1254695 := bstep (se 1 (by rfl) ⟨941021, by rfl⟩ : syracuseStep 1254695 = 1882043) B1882043
theorem B1254735 : Blo 1254445 1254735 := bstep (se 1 (by rfl) ⟨941051, by rfl⟩ : syracuseStep 1254735 = 1882103) B1882103
theorem B1254751 : Blo 1254445 1254751 := bstep (se 1 (by rfl) ⟨941063, by rfl⟩ : syracuseStep 1254751 = 1882127) B1882127
theorem B3622249 : Blo 1254445 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B10184051 : Blo 1254445 10184051 := bstep (se 1 (by rfl) ⟨7638038, by rfl⟩ : syracuseStep 10184051 = 15276077) B15276077
theorem B1254779 : Blo 1254445 1254779 := bstep (se 1 (by rfl) ⟨941084, by rfl⟩ : syracuseStep 1254779 = 1882169) B1882169
theorem B1254831 : Blo 1254445 1254831 := bstep (se 1 (by rfl) ⟨941123, by rfl⟩ : syracuseStep 1254831 = 1882247) B1882247
theorem B1910191 : Blo 1254445 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B1254855 : Blo 1254445 1254855 := bstep (se 1 (by rfl) ⟨941141, by rfl⟩ : syracuseStep 1254855 = 1882283) B1882283
theorem B4769225 : Blo 1254445 4769225 := bstep (se 2 (by rfl) ⟨1788459, by rfl⟩ : syracuseStep 4769225 = 3576919) B3576919
theorem B1254875 : Blo 1254445 1254875 := bstep (se 1 (by rfl) ⟨941156, by rfl⟩ : syracuseStep 1254875 = 1882313) B1882313
theorem B3180019 : Blo 1254445 3180019 := bstep (se 1 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 3180019 = 4770029) B4770029
theorem B1254951 : Blo 1254445 1254951 := bstep (se 1 (by rfl) ⟨941213, by rfl⟩ : syracuseStep 1254951 = 1882427) B1882427
theorem B4236839 : Blo 1254445 4236839 := bstep (se 1 (by rfl) ⟨3177629, by rfl⟩ : syracuseStep 4236839 = 6355259) B6355259
theorem B1254991 : Blo 1254445 1254991 := bstep (se 1 (by rfl) ⟨941243, by rfl⟩ : syracuseStep 1254991 = 1882487) B1882487
theorem B1255007 : Blo 1254445 1255007 := bstep (se 1 (by rfl) ⟨941255, by rfl⟩ : syracuseStep 1255007 = 1882511) B1882511
theorem B1255035 : Blo 1254445 1255035 := bstep (se 1 (by rfl) ⟨941276, by rfl⟩ : syracuseStep 1255035 = 1882553) B1882553
theorem B4236947 : Blo 1254445 4236947 := bstep (se 1 (by rfl) ⟨3177710, by rfl⟩ : syracuseStep 4236947 = 6355421) B6355421
theorem B1255087 : Blo 1254445 1255087 := bstep (se 1 (by rfl) ⟨941315, by rfl⟩ : syracuseStep 1255087 = 1882631) B1882631
theorem B1255111 : Blo 1254445 1255111 := bstep (se 1 (by rfl) ⟨941333, by rfl⟩ : syracuseStep 1255111 = 1882667) B1882667
theorem B1255131 : Blo 1254445 1255131 := bstep (se 1 (by rfl) ⟨941348, by rfl⟩ : syracuseStep 1255131 = 1882697) B1882697
theorem B1255207 : Blo 1254445 1255207 := bstep (se 1 (by rfl) ⟨941405, by rfl⟩ : syracuseStep 1255207 = 1882811) B1882811
theorem B1255247 : Blo 1254445 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B1255263 : Blo 1254445 1255263 := bstep (se 1 (by rfl) ⟨941447, by rfl⟩ : syracuseStep 1255263 = 1882895) B1882895
theorem B4237163 : Blo 1254445 4237163 := bstep (se 1 (by rfl) ⟨3177872, by rfl⟩ : syracuseStep 4237163 = 6355745) B6355745
theorem B1255291 : Blo 1254445 1255291 := bstep (se 1 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 1255291 = 1882937) B1882937
theorem B4237217 : Blo 1254445 4237217 := bstep (se 2 (by rfl) ⟨1588956, by rfl⟩ : syracuseStep 4237217 = 3177913) B3177913
theorem B1255343 : Blo 1254445 1255343 := bstep (se 1 (by rfl) ⟨941507, by rfl⟩ : syracuseStep 1255343 = 1883015) B1883015
theorem B4769711 : Blo 1254445 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B1255367 : Blo 1254445 1255367 := bstep (se 1 (by rfl) ⟨941525, by rfl⟩ : syracuseStep 1255367 = 1883051) B1883051
theorem B1255387 : Blo 1254445 1255387 := bstep (se 1 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 1255387 = 1883081) B1883081
theorem B2861075 : Blo 1254445 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B1255463 : Blo 1254445 1255463 := bstep (se 1 (by rfl) ⟨941597, by rfl⟩ : syracuseStep 1255463 = 1883195) B1883195
theorem B1255503 : Blo 1254445 1255503 := bstep (se 1 (by rfl) ⟨941627, by rfl⟩ : syracuseStep 1255503 = 1883255) B1883255
theorem B4524113 : Blo 1254445 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B18606167 : Blo 1254445 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B1255519 : Blo 1254445 1255519 := bstep (se 1 (by rfl) ⟨941639, by rfl⟩ : syracuseStep 1255519 = 1883279) B1883279
theorem B1255547 : Blo 1254445 1255547 := bstep (se 1 (by rfl) ⟨941660, by rfl⟩ : syracuseStep 1255547 = 1883321) B1883321
theorem B1255599 : Blo 1254445 1255599 := bstep (se 1 (by rfl) ⟨941699, by rfl⟩ : syracuseStep 1255599 = 1883399) B1883399
theorem B1255623 : Blo 1254445 1255623 := bstep (se 1 (by rfl) ⟨941717, by rfl⟩ : syracuseStep 1255623 = 1883435) B1883435
theorem B1255643 : Blo 1254445 1255643 := bstep (se 1 (by rfl) ⟨941732, by rfl⟩ : syracuseStep 1255643 = 1883465) B1883465
theorem B1255719 : Blo 1254445 1255719 := bstep (se 1 (by rfl) ⟨941789, by rfl⟩ : syracuseStep 1255719 = 1883579) B1883579
theorem B1255759 : Blo 1254445 1255759 := bstep (se 1 (by rfl) ⟨941819, by rfl⟩ : syracuseStep 1255759 = 1883639) B1883639
theorem B1255775 : Blo 1254445 1255775 := bstep (se 1 (by rfl) ⟨941831, by rfl⟩ : syracuseStep 1255775 = 1883663) B1883663
theorem B6351209 : Blo 1254445 6351209 := bstep (se 2 (by rfl) ⟨2381703, by rfl⟩ : syracuseStep 6351209 = 4763407) B4763407
theorem B1255803 : Blo 1254445 1255803 := bstep (se 1 (by rfl) ⟨941852, by rfl⟩ : syracuseStep 1255803 = 1883705) B1883705
theorem B2861455 : Blo 1254445 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B1255855 : Blo 1254445 1255855 := bstep (se 1 (by rfl) ⟨941891, by rfl⟩ : syracuseStep 1255855 = 1883783) B1883783
theorem B1255879 : Blo 1254445 1255879 := bstep (se 1 (by rfl) ⟨941909, by rfl⟩ : syracuseStep 1255879 = 1883819) B1883819
theorem B1255899 : Blo 1254445 1255899 := bstep (se 1 (by rfl) ⟨941924, by rfl⟩ : syracuseStep 1255899 = 1883849) B1883849
theorem B4237811 : Blo 1254445 4237811 := bstep (se 1 (by rfl) ⟨3178358, by rfl⟩ : syracuseStep 4237811 = 6356717) B6356717
theorem B6785561 : Blo 1254445 6785561 := bstep (se 2 (by rfl) ⟨2544585, by rfl⟩ : syracuseStep 6785561 = 5089171) B5089171
theorem B1255975 : Blo 1254445 1255975 := bstep (se 1 (by rfl) ⟨941981, by rfl⟩ : syracuseStep 1255975 = 1883963) B1883963
theorem B1411663 : Blo 1254445 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B1256015 : Blo 1254445 1256015 := bstep (se 1 (by rfl) ⟨942011, by rfl⟩ : syracuseStep 1256015 = 1884023) B1884023
theorem B1256031 : Blo 1254445 1256031 := bstep (se 1 (by rfl) ⟨942023, by rfl⟩ : syracuseStep 1256031 = 1884047) B1884047
theorem B1256059 : Blo 1254445 1256059 := bstep (se 1 (by rfl) ⟨942044, by rfl⟩ : syracuseStep 1256059 = 1884089) B1884089
theorem B8039047 : Blo 1254445 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B11446919 : Blo 1254445 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B1256111 : Blo 1254445 1256111 := bstep (se 1 (by rfl) ⟨942083, by rfl⟩ : syracuseStep 1256111 = 1884167) B1884167
theorem B1256135 : Blo 1254445 1256135 := bstep (se 1 (by rfl) ⟨942101, by rfl⟩ : syracuseStep 1256135 = 1884203) B1884203
theorem B4770515 : Blo 1254445 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B1256155 : Blo 1254445 1256155 := bstep (se 1 (by rfl) ⟨942116, by rfl⟩ : syracuseStep 1256155 = 1884233) B1884233
theorem B1256231 : Blo 1254445 1256231 := bstep (se 1 (by rfl) ⟨942173, by rfl⟩ : syracuseStep 1256231 = 1884347) B1884347
theorem B1256271 : Blo 1254445 1256271 := bstep (se 1 (by rfl) ⟨942203, by rfl⟩ : syracuseStep 1256271 = 1884407) B1884407
theorem B1256287 : Blo 1254445 1256287 := bstep (se 1 (by rfl) ⟨942215, by rfl⟩ : syracuseStep 1256287 = 1884431) B1884431
theorem B2681707 : Blo 1254445 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B1256315 : Blo 1254445 1256315 := bstep (se 1 (by rfl) ⟨942236, by rfl⟩ : syracuseStep 1256315 = 1884473) B1884473
theorem B1256367 : Blo 1254445 1256367 := bstep (se 1 (by rfl) ⟨942275, by rfl⟩ : syracuseStep 1256367 = 1884551) B1884551
theorem B1256391 : Blo 1254445 1256391 := bstep (se 1 (by rfl) ⟨942293, by rfl⟩ : syracuseStep 1256391 = 1884587) B1884587
theorem B1412059 : Blo 1254445 1412059 := bstep (se 1 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 1412059 = 2118089) B2118089
theorem B1256411 : Blo 1254445 1256411 := bstep (se 1 (by rfl) ⟨942308, by rfl⟩ : syracuseStep 1256411 = 1884617) B1884617
theorem B4238351 : Blo 1254445 4238351 := bstep (se 1 (by rfl) ⟨3178763, by rfl⟩ : syracuseStep 4238351 = 6357527) B6357527
theorem B36211799 : Blo 1254445 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B58019105 : Blo 1254445 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B18599203 : Blo 1254445 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B25767233 : Blo 1254445 25767233 := bstep (se 2 (by rfl) ⟨9662712, by rfl⟩ : syracuseStep 25767233 = 19325425) B19325425
theorem B4074895 : Blo 1254445 4074895 := bstep (se 1 (by rfl) ⟨3056171, by rfl⟩ : syracuseStep 4074895 = 6112343) B6112343
theorem B2010511 : Blo 1254445 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B1412527 : Blo 1254445 1412527 := bstep (se 1 (by rfl) ⟨1059395, by rfl⟩ : syracuseStep 1412527 = 2118791) B2118791
theorem B2117083 : Blo 1254445 2117083 := bstep (se 1 (by rfl) ⟨1587812, by rfl⟩ : syracuseStep 2117083 = 3175625) B3175625
theorem B3018227 : Blo 1254445 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B3018265 : Blo 1254445 3018265 := bstep (se 2 (by rfl) ⟨1131849, by rfl⟩ : syracuseStep 3018265 = 2263699) B2263699
theorem B3575335 : Blo 1254445 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B4763195 : Blo 1254445 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B8826455 : Blo 1254445 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B4238945 : Blo 1254445 4238945 := bstep (se 2 (by rfl) ⟨1589604, by rfl⟩ : syracuseStep 4238945 = 3179209) B3179209
theorem B3575495 : Blo 1254445 3575495 := bstep (se 1 (by rfl) ⟨2681621, by rfl⟩ : syracuseStep 3575495 = 5363243) B5363243
theorem B7155499 : Blo 1254445 7155499 := bstep (se 1 (by rfl) ⟨5366624, by rfl⟩ : syracuseStep 7155499 = 10733249) B10733249
theorem B1412959 : Blo 1254445 1412959 := bstep (se 1 (by rfl) ⟨1059719, by rfl⟩ : syracuseStep 1412959 = 2119439) B2119439
theorem B3018671 : Blo 1254445 3018671 := bstep (se 1 (by rfl) ⟨2264003, by rfl⟩ : syracuseStep 3018671 = 4528007) B4528007
theorem B2011063 : Blo 1254445 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B3575735 : Blo 1254445 3575735 := bstep (se 1 (by rfl) ⟨2681801, by rfl⟩ : syracuseStep 3575735 = 5363603) B5363603
theorem B2117711 : Blo 1254445 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B15265955 : Blo 1254445 15265955 := bstep (se 1 (by rfl) ⟨11449466, by rfl⟩ : syracuseStep 15265955 = 22898933) B22898933
theorem B1413319 : Blo 1254445 1413319 := bstep (se 1 (by rfl) ⟨1059989, by rfl⟩ : syracuseStep 1413319 = 2119979) B2119979
theorem B2822543 : Blo 1254445 2822543 := bstep (se 1 (by rfl) ⟨2116907, by rfl⟩ : syracuseStep 2822543 = 4233815) B4233815
theorem B8155673 : Blo 1254445 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B3486347 : Blo 1254445 3486347 := bstep (se 1 (by rfl) ⟨2614760, by rfl⟩ : syracuseStep 3486347 = 5229521) B5229521
theorem B5436089 : Blo 1254445 5436089 := bstep (se 2 (by rfl) ⟨2038533, by rfl⟩ : syracuseStep 5436089 = 4077067) B4077067
theorem B2822867 : Blo 1254445 2822867 := bstep (se 1 (by rfl) ⟨2117150, by rfl⟩ : syracuseStep 2822867 = 4234301) B4234301
theorem B3576737 : Blo 1254445 3576737 := bstep (se 2 (by rfl) ⟨1341276, by rfl⟩ : syracuseStep 3576737 = 2682553) B2682553
theorem B2118575 : Blo 1254445 2118575 := bstep (se 1 (by rfl) ⟨1588931, by rfl⟩ : syracuseStep 2118575 = 3177863) B3177863
theorem B4240403 : Blo 1254445 4240403 := bstep (se 1 (by rfl) ⟨3180302, by rfl⟩ : syracuseStep 4240403 = 6360605) B6360605
theorem B5805209 : Blo 1254445 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B4019357 : Blo 1254445 4019357 := bstep (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) B1507259
theorem B3175595 : Blo 1254445 3175595 := bstep (se 1 (by rfl) ⟨2381696, by rfl⟩ : syracuseStep 3175595 = 4763393) B4763393
theorem B2119007 : Blo 1254445 2119007 := bstep (se 1 (by rfl) ⟨1589255, by rfl⟩ : syracuseStep 2119007 = 3178511) B3178511
theorem B3577193 : Blo 1254445 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B54285713 : Blo 1254445 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B1611191 : Blo 1254445 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B2823803 : Blo 1254445 2823803 := bstep (se 1 (by rfl) ⟨2117852, by rfl⟩ : syracuseStep 2823803 = 4235705) B4235705
theorem B16307905 : Blo 1254445 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B1341127 : Blo 1254445 1341127 := bstep (se 1 (by rfl) ⟨1005845, by rfl⟩ : syracuseStep 1341127 = 2011691) B2011691
theorem B2823929 : Blo 1254445 2823929 := bstep (se 2 (by rfl) ⟨1058973, by rfl⟩ : syracuseStep 2823929 = 2117947) B2117947
theorem B5093227 : Blo 1254445 5093227 := bstep (se 1 (by rfl) ⟨3819920, by rfl⟩ : syracuseStep 5093227 = 7639841) B7639841
theorem B2119567 : Blo 1254445 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B1882031 : Blo 1254445 1882031 := bstep (se 1 (by rfl) ⟨1411523, by rfl⟩ : syracuseStep 1882031 = 2823047) B2823047
theorem B4020151 : Blo 1254445 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B3176455 : Blo 1254445 3176455 := bstep (se 1 (by rfl) ⟨2382341, by rfl⟩ : syracuseStep 3176455 = 4764683) B4764683
theorem B2824199 : Blo 1254445 2824199 := bstep (se 1 (by rfl) ⟨2118149, by rfl⟩ : syracuseStep 2824199 = 4236299) B4236299
theorem B1882121 : Blo 1254445 1882121 := bstep (se 2 (by rfl) ⟨705795, by rfl⟩ : syracuseStep 1882121 = 1411591) B1411591
theorem B1882151 : Blo 1254445 1882151 := bstep (se 1 (by rfl) ⟨1411613, by rfl⟩ : syracuseStep 1882151 = 2823227) B2823227
theorem B2824271 : Blo 1254445 2824271 := bstep (se 1 (by rfl) ⟨2118203, by rfl⟩ : syracuseStep 2824271 = 4236407) B4236407
theorem B5093455 : Blo 1254445 5093455 := bstep (se 1 (by rfl) ⟨3820091, by rfl⟩ : syracuseStep 5093455 = 7640183) B7640183
theorem B1882235 : Blo 1254445 1882235 := bstep (se 1 (by rfl) ⟨1411676, by rfl⟩ : syracuseStep 1882235 = 2823353) B2823353
theorem B2545835 : Blo 1254445 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B2382023 : Blo 1254445 2382023 := bstep (se 1 (by rfl) ⟨1786517, by rfl⟩ : syracuseStep 2382023 = 3573035) B3573035
theorem B1882361 : Blo 1254445 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B1882463 : Blo 1254445 1882463 := bstep (se 1 (by rfl) ⟨1411847, by rfl⟩ : syracuseStep 1882463 = 2823695) B2823695
theorem B1882475 : Blo 1254445 1882475 := bstep (se 1 (by rfl) ⟨1411856, by rfl⟩ : syracuseStep 1882475 = 2823713) B2823713
theorem B2824667 : Blo 1254445 2824667 := bstep (se 1 (by rfl) ⟨2118500, by rfl⟩ : syracuseStep 2824667 = 4237001) B4237001
theorem B16095773 : Blo 1254445 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B4233761 : Blo 1254445 4233761 := bstep (se 2 (by rfl) ⟨1587660, by rfl⟩ : syracuseStep 4233761 = 3175321) B3175321
theorem B21436973 : Blo 1254445 21436973 := bstep (se 3 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 21436973 = 8038865) B8038865
theorem B2120249 : Blo 1254445 2120249 := bstep (se 2 (by rfl) ⟨795093, by rfl⟩ : syracuseStep 2120249 = 1590187) B1590187
theorem B1882703 : Blo 1254445 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B3177083 : Blo 1254445 3177083 := bstep (se 1 (by rfl) ⟨2382812, by rfl⟩ : syracuseStep 3177083 = 4765625) B4765625
theorem B1882823 : Blo 1254445 1882823 := bstep (se 1 (by rfl) ⟨1412117, by rfl⟩ : syracuseStep 1882823 = 2824235) B2824235
theorem B5724881 : Blo 1254445 5724881 := bstep (se 2 (by rfl) ⟨2146830, by rfl⟩ : syracuseStep 5724881 = 4293661) B4293661
theorem B2382547 : Blo 1254445 2382547 := bstep (se 1 (by rfl) ⟨1786910, by rfl⟩ : syracuseStep 2382547 = 3573821) B3573821
theorem B4233977 : Blo 1254445 4233977 := bstep (se 2 (by rfl) ⟨1587741, by rfl⟩ : syracuseStep 4233977 = 3175483) B3175483
theorem B8157955 : Blo 1254445 8157955 := bstep (se 1 (by rfl) ⟨6118466, by rfl⟩ : syracuseStep 8157955 = 12236933) B12236933
theorem B1882985 : Blo 1254445 1882985 := bstep (se 2 (by rfl) ⟨706119, by rfl⟩ : syracuseStep 1882985 = 1412239) B1412239
theorem B4897643 : Blo 1254445 4897643 := bstep (se 1 (by rfl) ⟨3673232, by rfl⟩ : syracuseStep 4897643 = 7346465) B7346465
theorem B3177377 : Blo 1254445 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B2382767 : Blo 1254445 2382767 := bstep (se 1 (by rfl) ⟨1787075, by rfl⟩ : syracuseStep 2382767 = 3574151) B3574151
theorem B2825135 : Blo 1254445 2825135 := bstep (se 1 (by rfl) ⟨2118851, by rfl⟩ : syracuseStep 2825135 = 4237703) B4237703
theorem B1883063 : Blo 1254445 1883063 := bstep (se 1 (by rfl) ⟨1412297, by rfl⟩ : syracuseStep 1883063 = 2824595) B2824595
theorem B1588187 : Blo 1254445 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B1883099 : Blo 1254445 1883099 := bstep (se 1 (by rfl) ⟨1412324, by rfl⟩ : syracuseStep 1883099 = 2824649) B2824649
theorem B4234247 : Blo 1254445 4234247 := bstep (se 1 (by rfl) ⟨3175685, by rfl⟩ : syracuseStep 4234247 = 6351371) B6351371
theorem B4234355 : Blo 1254445 4234355 := bstep (se 1 (by rfl) ⟨3175766, by rfl⟩ : syracuseStep 4234355 = 6351533) B6351533
theorem B2825387 : Blo 1254445 2825387 := bstep (se 1 (by rfl) ⟨2119040, by rfl⟩ : syracuseStep 2825387 = 4238081) B4238081
theorem B10730789 : Blo 1254445 10730789 := bstep (se 4 (by rfl) ⟨1006011, by rfl⟩ : syracuseStep 10730789 = 2012023) B2012023
theorem B2383177 : Blo 1254445 2383177 := bstep (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) B1787383
theorem B4234625 : Blo 1254445 4234625 := bstep (se 2 (by rfl) ⟨1587984, by rfl⟩ : syracuseStep 4234625 = 3175969) B3175969
theorem B1883567 : Blo 1254445 1883567 := bstep (se 1 (by rfl) ⟨1412675, by rfl⟩ : syracuseStep 1883567 = 2825351) B2825351
theorem B1588663 : Blo 1254445 1588663 := bstep (se 1 (by rfl) ⟨1191497, by rfl⟩ : syracuseStep 1588663 = 2382995) B2382995
theorem B1883657 : Blo 1254445 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1883687 : Blo 1254445 1883687 := bstep (se 1 (by rfl) ⟨1412765, by rfl⟩ : syracuseStep 1883687 = 2825531) B2825531
theorem B6037031 : Blo 1254445 6037031 := bstep (se 1 (by rfl) ⟨4527773, by rfl⟩ : syracuseStep 6037031 = 9055547) B9055547
theorem B5725793 : Blo 1254445 5725793 := bstep (se 2 (by rfl) ⟨2147172, by rfl⟩ : syracuseStep 5725793 = 4294345) B4294345
theorem B3014267 : Blo 1254445 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B4021883 : Blo 1254445 4021883 := bstep (se 1 (by rfl) ⟨3016412, by rfl⟩ : syracuseStep 4021883 = 6032825) B6032825
theorem B1883771 : Blo 1254445 1883771 := bstep (se 1 (by rfl) ⟨1412828, by rfl⟩ : syracuseStep 1883771 = 2825657) B2825657
theorem B21454469 : Blo 1254445 21454469 := bstep (se 4 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 21454469 = 4022713) B4022713
theorem B2825927 : Blo 1254445 2825927 := bstep (se 1 (by rfl) ⟨2119445, by rfl⟩ : syracuseStep 2825927 = 4238891) B4238891
theorem B10182365 : Blo 1254445 10182365 := bstep (se 3 (by rfl) ⟨1909193, by rfl⟩ : syracuseStep 10182365 = 3818387) B3818387
theorem B1883897 : Blo 1254445 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B5881643 : Blo 1254445 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1883999 : Blo 1254445 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B5087083 : Blo 1254445 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B4292459 : Blo 1254445 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B1884011 : Blo 1254445 1884011 := bstep (se 1 (by rfl) ⟨1413008, by rfl⟩ : syracuseStep 1884011 = 2826017) B2826017
theorem B4235273 : Blo 1254445 4235273 := bstep (se 2 (by rfl) ⟨1588227, by rfl⟩ : syracuseStep 4235273 = 3176455) B3176455
theorem B6791273 : Blo 1254445 6791273 := bstep (se 2 (by rfl) ⟨2546727, by rfl⟩ : syracuseStep 6791273 = 5093455) B5093455
theorem B16097413 : Blo 1254445 16097413 := bstep (se 4 (by rfl) ⟨1509132, by rfl⟩ : syracuseStep 16097413 = 3018265) B3018265
theorem B6357203 : Blo 1254445 6357203 := bstep (se 1 (by rfl) ⟨4767902, by rfl⟩ : syracuseStep 6357203 = 9535805) B9535805
theorem B1884425 : Blo 1254445 1884425 := bstep (se 2 (by rfl) ⟨706659, by rfl⟩ : syracuseStep 1884425 = 1413319) B1413319
theorem B1884527 : Blo 1254445 1884527 := bstep (se 1 (by rfl) ⟨1413395, by rfl⟩ : syracuseStep 1884527 = 2826791) B2826791
theorem B1507783 : Blo 1254445 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B148750805 : Blo 1254445 148750805 := bstep (se 7 (by rfl) ⟨1743173, by rfl⟩ : syracuseStep 148750805 = 3486347) B3486347
theorem B3179027 : Blo 1254445 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B2384491 : Blo 1254445 2384491 := bstep (se 1 (by rfl) ⟨1788368, by rfl⟩ : syracuseStep 2384491 = 3576737) B3576737
theorem B6783659 : Blo 1254445 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B2826935 : Blo 1254445 2826935 := bstep (se 1 (by rfl) ⟨2120201, by rfl⟩ : syracuseStep 2826935 = 4240403) B4240403
theorem B2679571 : Blo 1254445 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B2384795 : Blo 1254445 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B3179483 : Blo 1254445 3179483 := bstep (se 1 (by rfl) ⟨2384612, by rfl⟩ : syracuseStep 3179483 = 4769225) B4769225
theorem B1254687 : Blo 1254445 1254687 := bstep (se 1 (by rfl) ⟨941015, by rfl⟩ : syracuseStep 1254687 = 1882031) B1882031
theorem B3179807 : Blo 1254445 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B1254747 : Blo 1254445 1254747 := bstep (se 1 (by rfl) ⟨941060, by rfl⟩ : syracuseStep 1254747 = 1882121) B1882121
theorem B1254767 : Blo 1254445 1254767 := bstep (se 1 (by rfl) ⟨941075, by rfl⟩ : syracuseStep 1254767 = 1882151) B1882151
theorem B3016075 : Blo 1254445 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B12404111 : Blo 1254445 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B1254823 : Blo 1254445 1254823 := bstep (se 1 (by rfl) ⟨941117, by rfl⟩ : syracuseStep 1254823 = 1882235) B1882235
theorem B16098749 : Blo 1254445 16098749 := bstep (se 3 (by rfl) ⟨3018515, by rfl⟩ : syracuseStep 16098749 = 6037031) B6037031
theorem B1254907 : Blo 1254445 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B6030881 : Blo 1254445 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B23537213 : Blo 1254445 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B1254975 : Blo 1254445 1254975 := bstep (se 1 (by rfl) ⟨941231, by rfl⟩ : syracuseStep 1254975 = 1882463) B1882463
theorem B1254983 : Blo 1254445 1254983 := bstep (se 1 (by rfl) ⟨941237, by rfl⟩ : syracuseStep 1254983 = 1882475) B1882475
theorem B8038045 : Blo 1254445 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B4523707 : Blo 1254445 4523707 := bstep (se 1 (by rfl) ⟨3392780, by rfl⟩ : syracuseStep 4523707 = 6785561) B6785561
theorem B1255135 : Blo 1254445 1255135 := bstep (se 1 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 1255135 = 1882703) B1882703
theorem B1255215 : Blo 1254445 1255215 := bstep (se 1 (by rfl) ⟨941411, by rfl⟩ : syracuseStep 1255215 = 1882823) B1882823
theorem B3180343 : Blo 1254445 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B5433193 : Blo 1254445 5433193 := bstep (se 2 (by rfl) ⟨2037447, by rfl⟩ : syracuseStep 5433193 = 4074895) B4074895
theorem B19318661 : Blo 1254445 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B1255323 : Blo 1254445 1255323 := bstep (se 1 (by rfl) ⟨941492, by rfl⟩ : syracuseStep 1255323 = 1882985) B1882985
theorem B1255375 : Blo 1254445 1255375 := bstep (se 1 (by rfl) ⟨941531, by rfl⟩ : syracuseStep 1255375 = 1883063) B1883063
theorem B1255399 : Blo 1254445 1255399 := bstep (se 1 (by rfl) ⟨941549, by rfl⟩ : syracuseStep 1255399 = 1883099) B1883099
theorem B7153859 : Blo 1254445 7153859 := bstep (se 1 (by rfl) ⟨5365394, by rfl⟩ : syracuseStep 7153859 = 10730789) B10730789
theorem B21743873 : Blo 1254445 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1788169 : Blo 1254445 1788169 := bstep (se 2 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 1788169 = 1341127) B1341127
theorem B13060381 : Blo 1254445 13060381 := bstep (se 3 (by rfl) ⟨2448821, by rfl⟩ : syracuseStep 13060381 = 4897643) B4897643
theorem B1255711 : Blo 1254445 1255711 := bstep (se 1 (by rfl) ⟨941783, by rfl⟩ : syracuseStep 1255711 = 1883567) B1883567
theorem B1255771 : Blo 1254445 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B1255791 : Blo 1254445 1255791 := bstep (se 1 (by rfl) ⟨941843, by rfl⟩ : syracuseStep 1255791 = 1883687) B1883687
theorem B2681255 : Blo 1254445 2681255 := bstep (se 1 (by rfl) ⟨2010941, by rfl⟩ : syracuseStep 2681255 = 4021883) B4021883
theorem B1255847 : Blo 1254445 1255847 := bstep (se 1 (by rfl) ⟨941885, by rfl⟩ : syracuseStep 1255847 = 1883771) B1883771
theorem B1255931 : Blo 1254445 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B1255999 : Blo 1254445 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B2861639 : Blo 1254445 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B1256007 : Blo 1254445 1256007 := bstep (se 1 (by rfl) ⟨942005, by rfl⟩ : syracuseStep 1256007 = 1884011) B1884011
theorem B5360201 : Blo 1254445 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B2681417 : Blo 1254445 2681417 := bstep (se 2 (by rfl) ⟨1005531, by rfl⟩ : syracuseStep 2681417 = 2011063) B2011063
theorem B1411807 : Blo 1254445 1411807 := bstep (se 1 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 1411807 = 2117711) B2117711
theorem B1256159 : Blo 1254445 1256159 := bstep (se 1 (by rfl) ⟨942119, by rfl⟩ : syracuseStep 1256159 = 1884239) B1884239
theorem B1256239 : Blo 1254445 1256239 := bstep (se 1 (by rfl) ⟨942179, by rfl⟩ : syracuseStep 1256239 = 1884359) B1884359
theorem B21441347 : Blo 1254445 21441347 := bstep (se 1 (by rfl) ⟨16081010, by rfl⟩ : syracuseStep 21441347 = 32162021) B32162021
theorem B1256347 : Blo 1254445 1256347 := bstep (se 1 (by rfl) ⟨942260, by rfl⟩ : syracuseStep 1256347 = 1884521) B1884521
theorem B1256399 : Blo 1254445 1256399 := bstep (se 1 (by rfl) ⟨942299, by rfl⟩ : syracuseStep 1256399 = 1884599) B1884599
theorem B1256423 : Blo 1254445 1256423 := bstep (se 1 (by rfl) ⟨942317, by rfl⟩ : syracuseStep 1256423 = 1884635) B1884635
theorem B10726415 : Blo 1254445 10726415 := bstep (se 1 (by rfl) ⟨8044811, by rfl⟩ : syracuseStep 10726415 = 16089623) B16089623
theorem B40709213 : Blo 1254445 40709213 := bstep (se 3 (by rfl) ⟨7632977, by rfl⟩ : syracuseStep 40709213 = 15265955) B15265955
theorem B3624059 : Blo 1254445 3624059 := bstep (se 1 (by rfl) ⟨2718044, by rfl⟩ : syracuseStep 3624059 = 5436089) B5436089
theorem B4238459 : Blo 1254445 4238459 := bstep (se 1 (by rfl) ⟨3178844, by rfl⟩ : syracuseStep 4238459 = 6357689) B6357689
theorem B1412383 : Blo 1254445 1412383 := bstep (se 1 (by rfl) ⟨1059287, by rfl⟩ : syracuseStep 1412383 = 2118575) B2118575
theorem B2682143 : Blo 1254445 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B4238729 : Blo 1254445 4238729 := bstep (se 2 (by rfl) ⟨1589523, by rfl⟩ : syracuseStep 4238729 = 3179047) B3179047
theorem B2117063 : Blo 1254445 2117063 := bstep (se 1 (by rfl) ⟨1587797, by rfl⟩ : syracuseStep 2117063 = 3175595) B3175595
theorem B6352343 : Blo 1254445 6352343 := bstep (se 1 (by rfl) ⟨4764257, by rfl⟩ : syracuseStep 6352343 = 9528515) B9528515
theorem B10718729 : Blo 1254445 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B1412671 : Blo 1254445 1412671 := bstep (se 1 (by rfl) ⟨1059503, by rfl⟩ : syracuseStep 1412671 = 2119007) B2119007
theorem B3575609 : Blo 1254445 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B4296509 : Blo 1254445 4296509 := bstep (se 3 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 4296509 = 1611191) B1611191
theorem B4239161 : Blo 1254445 4239161 := bstep (se 2 (by rfl) ⟨1589685, by rfl⟩ : syracuseStep 4239161 = 3179371) B3179371
theorem B8048605 : Blo 1254445 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B2822507 : Blo 1254445 2822507 := bstep (se 1 (by rfl) ⟨2116880, by rfl⟩ : syracuseStep 2822507 = 4233761) B4233761
theorem B14291315 : Blo 1254445 14291315 := bstep (se 1 (by rfl) ⟨10718486, by rfl⟩ : syracuseStep 14291315 = 21436973) B21436973
theorem B1413499 : Blo 1254445 1413499 := bstep (se 1 (by rfl) ⟨1060124, by rfl⟩ : syracuseStep 1413499 = 2120249) B2120249
theorem B2118055 : Blo 1254445 2118055 := bstep (se 1 (by rfl) ⟨1588541, by rfl⟩ : syracuseStep 2118055 = 3177083) B3177083
theorem B7631279 : Blo 1254445 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B2822651 : Blo 1254445 2822651 := bstep (se 1 (by rfl) ⟨2116988, by rfl⟩ : syracuseStep 2822651 = 4233977) B4233977
theorem B2118217 : Blo 1254445 2118217 := bstep (se 2 (by rfl) ⟨794331, by rfl⟩ : syracuseStep 2118217 = 1588663) B1588663
theorem B2118251 : Blo 1254445 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B2822777 : Blo 1254445 2822777 := bstep (se 2 (by rfl) ⟨1058541, by rfl⟩ : syracuseStep 2822777 = 2117083) B2117083
theorem B4240025 : Blo 1254445 4240025 := bstep (se 2 (by rfl) ⟨1590009, by rfl⟩ : syracuseStep 4240025 = 3180019) B3180019
theorem B2822831 : Blo 1254445 2822831 := bstep (se 1 (by rfl) ⟨2117123, by rfl⟩ : syracuseStep 2822831 = 4234247) B4234247
theorem B2822903 : Blo 1254445 2822903 := bstep (se 1 (by rfl) ⟨2117177, by rfl⟩ : syracuseStep 2822903 = 4234355) B4234355
theorem B38679403 : Blo 1254445 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B2823083 : Blo 1254445 2823083 := bstep (se 1 (by rfl) ⟨2117312, by rfl⟩ : syracuseStep 2823083 = 4234625) B4234625
theorem B3175463 : Blo 1254445 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B9540665 : Blo 1254445 9540665 := bstep (se 2 (by rfl) ⟨3577749, by rfl⟩ : syracuseStep 9540665 = 7155499) B7155499
theorem B6788243 : Blo 1254445 6788243 := bstep (se 1 (by rfl) ⟨5091182, by rfl⟩ : syracuseStep 6788243 = 10182365) B10182365
theorem B3921095 : Blo 1254445 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2012447 : Blo 1254445 2012447 := bstep (se 1 (by rfl) ⟨1509335, by rfl⟩ : syracuseStep 2012447 = 3018671) B3018671
theorem B2823623 : Blo 1254445 2823623 := bstep (se 1 (by rfl) ⟨2117717, by rfl⟩ : syracuseStep 2823623 = 4235435) B4235435
theorem B1881695 : Blo 1254445 1881695 := bstep (se 1 (by rfl) ⟨1411271, by rfl⟩ : syracuseStep 1881695 = 2822543) B2822543
theorem B5437115 : Blo 1254445 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B1611499 : Blo 1254445 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B15480557 : Blo 1254445 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B2381575 : Blo 1254445 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B6788893 : Blo 1254445 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B2823983 : Blo 1254445 2823983 := bstep (se 1 (by rfl) ⟨2117987, by rfl⟩ : syracuseStep 2823983 = 4235975) B4235975
theorem B1881911 : Blo 1254445 1881911 := bstep (se 1 (by rfl) ⟨1411433, by rfl⟩ : syracuseStep 1881911 = 2822867) B2822867
theorem B3815273 : Blo 1254445 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B1882217 : Blo 1254445 1882217 := bstep (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) B1411663
theorem B6789367 : Blo 1254445 6789367 := bstep (se 1 (by rfl) ⟨5092025, by rfl⟩ : syracuseStep 6789367 = 10184051) B10184051
theorem B2119945 : Blo 1254445 2119945 := bstep (se 2 (by rfl) ⟨794979, by rfl⟩ : syracuseStep 2119945 = 1589959) B1589959
theorem B36190475 : Blo 1254445 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B3176729 : Blo 1254445 3176729 := bstep (se 2 (by rfl) ⟨1191273, by rfl⟩ : syracuseStep 3176729 = 2382547) B2382547
theorem B10877273 : Blo 1254445 10877273 := bstep (se 2 (by rfl) ⟨4078977, by rfl⟩ : syracuseStep 10877273 = 8157955) B8157955
theorem B2824559 : Blo 1254445 2824559 := bstep (se 1 (by rfl) ⟨2118419, by rfl⟩ : syracuseStep 2824559 = 4236839) B4236839
theorem B1882535 : Blo 1254445 1882535 := bstep (se 1 (by rfl) ⟨1411901, by rfl⟩ : syracuseStep 1882535 = 2823803) B2823803
theorem B2824631 : Blo 1254445 2824631 := bstep (se 1 (by rfl) ⟨2118473, by rfl⟩ : syracuseStep 2824631 = 4236947) B4236947
theorem B1882619 : Blo 1254445 1882619 := bstep (se 1 (by rfl) ⟨1411964, by rfl⟩ : syracuseStep 1882619 = 2823929) B2823929
theorem B2824775 : Blo 1254445 2824775 := bstep (se 1 (by rfl) ⟨2118581, by rfl⟩ : syracuseStep 2824775 = 4237163) B4237163
theorem B2824811 : Blo 1254445 2824811 := bstep (se 1 (by rfl) ⟨2118608, by rfl⟩ : syracuseStep 2824811 = 4237217) B4237217
theorem B1882745 : Blo 1254445 1882745 := bstep (se 2 (by rfl) ⟨706029, by rfl⟩ : syracuseStep 1882745 = 1412059) B1412059
theorem B1882799 : Blo 1254445 1882799 := bstep (se 1 (by rfl) ⟨1412099, by rfl⟩ : syracuseStep 1882799 = 2824199) B2824199
theorem B1907383 : Blo 1254445 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B1882847 : Blo 1254445 1882847 := bstep (se 1 (by rfl) ⟨1412135, by rfl⟩ : syracuseStep 1882847 = 2824271) B2824271
theorem B1588015 : Blo 1254445 1588015 := bstep (se 1 (by rfl) ⟨1191011, by rfl⟩ : syracuseStep 1588015 = 2382023) B2382023
theorem B99195749 : Blo 1254445 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B4234139 : Blo 1254445 4234139 := bstep (se 1 (by rfl) ⟨3175604, by rfl⟩ : syracuseStep 4234139 = 6351209) B6351209
theorem B1883111 : Blo 1254445 1883111 := bstep (se 1 (by rfl) ⟨1412333, by rfl⟩ : syracuseStep 1883111 = 2824667) B2824667
theorem B2825207 : Blo 1254445 2825207 := bstep (se 1 (by rfl) ⟨2118905, by rfl⟩ : syracuseStep 2825207 = 4237811) B4237811
theorem B10730515 : Blo 1254445 10730515 := bstep (se 1 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 10730515 = 16095773) B16095773
theorem B3177569 : Blo 1254445 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B3816587 : Blo 1254445 3816587 := bstep (se 1 (by rfl) ⟨2862440, by rfl⟩ : syracuseStep 3816587 = 5724881) B5724881
theorem B1883369 : Blo 1254445 1883369 := bstep (se 2 (by rfl) ⟨706263, by rfl⟩ : syracuseStep 1883369 = 1412527) B1412527
theorem B2546921 : Blo 1254445 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B1588511 : Blo 1254445 1588511 := bstep (se 1 (by rfl) ⟨1191383, by rfl⟩ : syracuseStep 1588511 = 2382767) B2382767
theorem B1883423 : Blo 1254445 1883423 := bstep (se 1 (by rfl) ⟨1412567, by rfl⟩ : syracuseStep 1883423 = 2825135) B2825135
theorem B2825567 : Blo 1254445 2825567 := bstep (se 1 (by rfl) ⟨2119175, by rfl⟩ : syracuseStep 2825567 = 4238351) B4238351
theorem B4767113 : Blo 1254445 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B24141199 : Blo 1254445 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B10722725 : Blo 1254445 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B1883591 : Blo 1254445 1883591 := bstep (se 1 (by rfl) ⟨1412693, by rfl⟩ : syracuseStep 1883591 = 2825387) B2825387
theorem B17178155 : Blo 1254445 17178155 := bstep (se 1 (by rfl) ⟨12883616, by rfl⟩ : syracuseStep 17178155 = 25767233) B25767233
theorem B3817195 : Blo 1254445 3817195 := bstep (se 1 (by rfl) ⟨2862896, by rfl⟩ : syracuseStep 3817195 = 5725793) B5725793
theorem B2825963 : Blo 1254445 2825963 := bstep (se 1 (by rfl) ⟨2119472, by rfl⟩ : syracuseStep 2825963 = 4238945) B4238945
theorem B14302979 : Blo 1254445 14302979 := bstep (se 1 (by rfl) ⟨10727234, by rfl⟩ : syracuseStep 14302979 = 21454469) B21454469
theorem B1883945 : Blo 1254445 1883945 := bstep (se 2 (by rfl) ⟨706479, by rfl⟩ : syracuseStep 1883945 = 1412959) B1412959
theorem B2383663 : Blo 1254445 2383663 := bstep (se 1 (by rfl) ⟨1787747, by rfl⟩ : syracuseStep 2383663 = 3575495) B3575495
theorem B1883951 : Blo 1254445 1883951 := bstep (se 1 (by rfl) ⟨1412963, by rfl⟩ : syracuseStep 1883951 = 2825927) B2825927
theorem B6782777 : Blo 1254445 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B6790969 : Blo 1254445 6790969 := bstep (se 2 (by rfl) ⟨2546613, by rfl⟩ : syracuseStep 6790969 = 5093227) B5093227
theorem B2826089 : Blo 1254445 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B4235165 : Blo 1254445 4235165 := bstep (se 3 (by rfl) ⟨794093, by rfl⟩ : syracuseStep 4235165 = 1588187) B1588187
theorem B2383823 : Blo 1254445 2383823 := bstep (se 1 (by rfl) ⟨1787867, by rfl⟩ : syracuseStep 2383823 = 3575735) B3575735
theorem B21463217 : Blo 1254445 21463217 := bstep (se 2 (by rfl) ⟨8048706, by rfl⟩ : syracuseStep 21463217 = 16097413) B16097413
theorem B9527543 : Blo 1254445 9527543 := bstep (se 1 (by rfl) ⟨7145657, by rfl⟩ : syracuseStep 9527543 = 14291315) B14291315
theorem B5087519 : Blo 1254445 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B9052489 : Blo 1254445 9052489 := bstep (se 2 (by rfl) ⟨3394683, by rfl⟩ : syracuseStep 9052489 = 6789367) B6789367
theorem B2384225 : Blo 1254445 2384225 := bstep (se 2 (by rfl) ⟨894084, by rfl⟩ : syracuseStep 2384225 = 1788169) B1788169
theorem B2826593 : Blo 1254445 2826593 := bstep (se 2 (by rfl) ⟨1059972, by rfl⟩ : syracuseStep 2826593 = 2119945) B2119945
theorem B2826683 : Blo 1254445 2826683 := bstep (se 1 (by rfl) ⟨2120012, by rfl⟩ : syracuseStep 2826683 = 4240025) B4240025
theorem B4522439 : Blo 1254445 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B1884623 : Blo 1254445 1884623 := bstep (se 1 (by rfl) ⟨1413467, by rfl⟩ : syracuseStep 1884623 = 2826935) B2826935
theorem B1884665 : Blo 1254445 1884665 := bstep (se 2 (by rfl) ⟨706749, by rfl⟩ : syracuseStep 1884665 = 1413499) B1413499
theorem B1589863 : Blo 1254445 1589863 := bstep (se 1 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 1589863 = 2384795) B2384795
theorem B6791789 : Blo 1254445 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B4236029 : Blo 1254445 4236029 := bstep (se 3 (by rfl) ⟨794255, by rfl⟩ : syracuseStep 4236029 = 1588511) B1588511
theorem B3179321 : Blo 1254445 3179321 := bstep (se 2 (by rfl) ⟨1192245, by rfl⟩ : syracuseStep 3179321 = 2384491) B2384491
theorem B10732499 : Blo 1254445 10732499 := bstep (se 1 (by rfl) ⟨8049374, by rfl⟩ : syracuseStep 10732499 = 16098749) B16098749
theorem B24126437 : Blo 1254445 24126437 := bstep (se 4 (by rfl) ⟨2261853, by rfl⟩ : syracuseStep 24126437 = 4523707) B4523707
theorem B3572761 : Blo 1254445 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B1254463 : Blo 1254445 1254463 := bstep (se 1 (by rfl) ⟨940847, by rfl⟩ : syracuseStep 1254463 = 1881695) B1881695
theorem B1254607 : Blo 1254445 1254607 := bstep (se 1 (by rfl) ⟨940955, by rfl⟩ : syracuseStep 1254607 = 1881911) B1881911
theorem B20358373 : Blo 1254445 20358373 := bstep (se 4 (by rfl) ⟨1908597, by rfl⟩ : syracuseStep 20358373 = 3817195) B3817195
theorem B12879107 : Blo 1254445 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B1254811 : Blo 1254445 1254811 := bstep (se 1 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 1254811 = 1882217) B1882217
theorem B4769239 : Blo 1254445 4769239 := bstep (se 1 (by rfl) ⟨3576929, by rfl⟩ : syracuseStep 4769239 = 7153859) B7153859
theorem B24126983 : Blo 1254445 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B7251515 : Blo 1254445 7251515 := bstep (se 1 (by rfl) ⟨5438636, by rfl⟩ : syracuseStep 7251515 = 10877273) B10877273
theorem B1255023 : Blo 1254445 1255023 := bstep (se 1 (by rfl) ⟨941267, by rfl⟩ : syracuseStep 1255023 = 1882535) B1882535
theorem B1787503 : Blo 1254445 1787503 := bstep (se 1 (by rfl) ⟨1340627, by rfl⟩ : syracuseStep 1787503 = 2681255) B2681255
theorem B1255079 : Blo 1254445 1255079 := bstep (se 1 (by rfl) ⟨941309, by rfl⟩ : syracuseStep 1255079 = 1882619) B1882619
theorem B3573467 : Blo 1254445 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B1787611 : Blo 1254445 1787611 := bstep (se 1 (by rfl) ⟨1340708, by rfl⟩ : syracuseStep 1787611 = 2681417) B2681417
theorem B1255163 : Blo 1254445 1255163 := bstep (se 1 (by rfl) ⟨941372, by rfl⟩ : syracuseStep 1255163 = 1882745) B1882745
theorem B1255199 : Blo 1254445 1255199 := bstep (se 1 (by rfl) ⟨941399, by rfl⟩ : syracuseStep 1255199 = 1882799) B1882799
theorem B1255231 : Blo 1254445 1255231 := bstep (se 1 (by rfl) ⟨941423, by rfl⟩ : syracuseStep 1255231 = 1882847) B1882847
theorem B32188265 : Blo 1254445 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B28977029 : Blo 1254445 28977029 := bstep (se 4 (by rfl) ⟨2716596, by rfl⟩ : syracuseStep 28977029 = 5433193) B5433193
theorem B1255407 : Blo 1254445 1255407 := bstep (se 1 (by rfl) ⟨941555, by rfl⟩ : syracuseStep 1255407 = 1883111) B1883111
theorem B1255579 : Blo 1254445 1255579 := bstep (se 1 (by rfl) ⟨941684, by rfl⟩ : syracuseStep 1255579 = 1883369) B1883369
theorem B1255615 : Blo 1254445 1255615 := bstep (se 1 (by rfl) ⟨941711, by rfl⟩ : syracuseStep 1255615 = 1883423) B1883423
theorem B1788095 : Blo 1254445 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B10717393 : Blo 1254445 10717393 := bstep (se 2 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 10717393 = 8038045) B8038045
theorem B1411375 : Blo 1254445 1411375 := bstep (se 1 (by rfl) ⟨1058531, by rfl⟩ : syracuseStep 1411375 = 2117063) B2117063
theorem B1255727 : Blo 1254445 1255727 := bstep (se 1 (by rfl) ⟨941795, by rfl⟩ : syracuseStep 1255727 = 1883591) B1883591
theorem B2148665 : Blo 1254445 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B7145819 : Blo 1254445 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B9054625 : Blo 1254445 9054625 := bstep (se 2 (by rfl) ⟨3395484, by rfl⟩ : syracuseStep 9054625 = 6790969) B6790969
theorem B1255963 : Blo 1254445 1255963 := bstep (se 1 (by rfl) ⟨941972, by rfl⟩ : syracuseStep 1255963 = 1883945) B1883945
theorem B1255967 : Blo 1254445 1255967 := bstep (se 1 (by rfl) ⟨941975, by rfl⟩ : syracuseStep 1255967 = 1883951) B1883951
theorem B4238135 : Blo 1254445 4238135 := bstep (se 1 (by rfl) ⟨3178601, by rfl⟩ : syracuseStep 4238135 = 6357203) B6357203
theorem B1256283 : Blo 1254445 1256283 := bstep (se 1 (by rfl) ⟨942212, by rfl⟩ : syracuseStep 1256283 = 1884425) B1884425
theorem B1256351 : Blo 1254445 1256351 := bstep (se 1 (by rfl) ⟨942263, by rfl⟩ : syracuseStep 1256351 = 1884527) B1884527
theorem B99167203 : Blo 1254445 99167203 := bstep (se 1 (by rfl) ⟨74375402, by rfl⟩ : syracuseStep 99167203 = 148750805) B148750805
theorem B1412167 : Blo 1254445 1412167 := bstep (se 1 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 1412167 = 2118251) B2118251
theorem B10456253 : Blo 1254445 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2010377 : Blo 1254445 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B2116975 : Blo 1254445 2116975 := bstep (se 1 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 2116975 = 3175463) B3175463
theorem B6360443 : Blo 1254445 6360443 := bstep (se 1 (by rfl) ⟨4770332, by rfl⟩ : syracuseStep 6360443 = 9540665) B9540665
theorem B2543177 : Blo 1254445 2543177 := bstep (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) B1907383
theorem B15691475 : Blo 1254445 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B2117353 : Blo 1254445 2117353 := bstep (se 2 (by rfl) ⟨794007, by rfl⟩ : syracuseStep 2117353 = 1588015) B1588015
theorem B3624743 : Blo 1254445 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B51572537 : Blo 1254445 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B14307353 : Blo 1254445 14307353 := bstep (se 2 (by rfl) ⟨5365257, by rfl⟩ : syracuseStep 14307353 = 10730515) B10730515
theorem B14495915 : Blo 1254445 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B2117819 : Blo 1254445 2117819 := bstep (se 1 (by rfl) ⟨1588364, by rfl⟩ : syracuseStep 2117819 = 3176729) B3176729
theorem B66130499 : Blo 1254445 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B2822759 : Blo 1254445 2822759 := bstep (se 1 (by rfl) ⟨2117069, by rfl⟩ : syracuseStep 2822759 = 4234139) B4234139
theorem B2118379 : Blo 1254445 2118379 := bstep (se 1 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 2118379 = 3177569) B3177569
theorem B2544391 : Blo 1254445 2544391 := bstep (se 1 (by rfl) ⟨1908293, by rfl⟩ : syracuseStep 2544391 = 3816587) B3816587
theorem B7148483 : Blo 1254445 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B3175433 : Blo 1254445 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B4240457 : Blo 1254445 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2864339 : Blo 1254445 2864339 := bstep (se 1 (by rfl) ⟨2148254, by rfl⟩ : syracuseStep 2864339 = 4296509) B4296509
theorem B2823443 : Blo 1254445 2823443 := bstep (se 1 (by rfl) ⟨2117582, by rfl⟩ : syracuseStep 2823443 = 4235165) B4235165
theorem B2823515 : Blo 1254445 2823515 := bstep (se 1 (by rfl) ⟨2117636, by rfl⟩ : syracuseStep 2823515 = 4235273) B4235273
theorem B4527515 : Blo 1254445 4527515 := bstep (se 1 (by rfl) ⟨3395636, by rfl⟩ : syracuseStep 4527515 = 6791273) B6791273
theorem B1881671 : Blo 1254445 1881671 := bstep (se 1 (by rfl) ⟨1411253, by rfl⟩ : syracuseStep 1881671 = 2822507) B2822507
theorem B9664157 : Blo 1254445 9664157 := bstep (se 3 (by rfl) ⟨1812029, by rfl⟩ : syracuseStep 9664157 = 3624059) B3624059
theorem B1881767 : Blo 1254445 1881767 := bstep (se 1 (by rfl) ⟨1411325, by rfl⟩ : syracuseStep 1881767 = 2822651) B2822651
theorem B2119351 : Blo 1254445 2119351 := bstep (se 1 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 2119351 = 3179027) B3179027
theorem B17413841 : Blo 1254445 17413841 := bstep (se 2 (by rfl) ⟨6530190, by rfl⟩ : syracuseStep 17413841 = 13060381) B13060381
theorem B18101981 : Blo 1254445 18101981 := bstep (se 3 (by rfl) ⟨3394121, by rfl⟩ : syracuseStep 18101981 = 6788243) B6788243
theorem B1881851 : Blo 1254445 1881851 := bstep (se 1 (by rfl) ⟨1411388, by rfl⟩ : syracuseStep 1881851 = 2822777) B2822777
theorem B1881887 : Blo 1254445 1881887 := bstep (se 1 (by rfl) ⟨1411415, by rfl⟩ : syracuseStep 1881887 = 2822831) B2822831
theorem B1881935 : Blo 1254445 1881935 := bstep (se 1 (by rfl) ⟨1411451, by rfl⟩ : syracuseStep 1881935 = 2822903) B2822903
theorem B2824073 : Blo 1254445 2824073 := bstep (se 2 (by rfl) ⟨1059027, by rfl⟩ : syracuseStep 2824073 = 2118055) B2118055
theorem B1882055 : Blo 1254445 1882055 := bstep (se 1 (by rfl) ⟨1411541, by rfl⟩ : syracuseStep 1882055 = 2823083) B2823083
theorem B2119655 : Blo 1254445 2119655 := bstep (se 1 (by rfl) ⟨1589741, by rfl⟩ : syracuseStep 2119655 = 3179483) B3179483
theorem B2824289 : Blo 1254445 2824289 := bstep (se 2 (by rfl) ⟨1059108, by rfl⟩ : syracuseStep 2824289 = 2118217) B2118217
theorem B2119871 : Blo 1254445 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B1341631 : Blo 1254445 1341631 := bstep (se 1 (by rfl) ⟨1006223, by rfl⟩ : syracuseStep 1341631 = 2012447) B2012447
theorem B1882409 : Blo 1254445 1882409 := bstep (se 2 (by rfl) ⟨705903, by rfl⟩ : syracuseStep 1882409 = 1411807) B1411807
theorem B1882415 : Blo 1254445 1882415 := bstep (se 1 (by rfl) ⟨1411811, by rfl⟩ : syracuseStep 1882415 = 2823623) B2823623
theorem B4020587 : Blo 1254445 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B33077629 : Blo 1254445 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B10320371 : Blo 1254445 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B1882655 : Blo 1254445 1882655 := bstep (se 1 (by rfl) ⟨1411991, by rfl⟩ : syracuseStep 1882655 = 2823983) B2823983
theorem B1883039 : Blo 1254445 1883039 := bstep (se 1 (by rfl) ⟨1412279, by rfl⟩ : syracuseStep 1883039 = 2824559) B2824559
theorem B1883087 : Blo 1254445 1883087 := bstep (se 1 (by rfl) ⟨1412315, by rfl⟩ : syracuseStep 1883087 = 2824631) B2824631
theorem B1883177 : Blo 1254445 1883177 := bstep (se 2 (by rfl) ⟨706191, by rfl⟩ : syracuseStep 1883177 = 1412383) B1412383
theorem B1907759 : Blo 1254445 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B1883183 : Blo 1254445 1883183 := bstep (se 1 (by rfl) ⟨1412387, by rfl⟩ : syracuseStep 1883183 = 2824775) B2824775
theorem B1883207 : Blo 1254445 1883207 := bstep (se 1 (by rfl) ⟨1412405, by rfl⟩ : syracuseStep 1883207 = 2824811) B2824811
theorem B4021433 : Blo 1254445 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B14294231 : Blo 1254445 14294231 := bstep (se 1 (by rfl) ⟨10720673, by rfl⟩ : syracuseStep 14294231 = 21441347) B21441347
theorem B1883471 : Blo 1254445 1883471 := bstep (se 1 (by rfl) ⟨1412603, by rfl⟩ : syracuseStep 1883471 = 2825207) B2825207
theorem B7150943 : Blo 1254445 7150943 := bstep (se 1 (by rfl) ⟨5363207, by rfl⟩ : syracuseStep 7150943 = 10726415) B10726415
theorem B27139475 : Blo 1254445 27139475 := bstep (se 1 (by rfl) ⟨20354606, by rfl⟩ : syracuseStep 27139475 = 40709213) B40709213
theorem B2825639 : Blo 1254445 2825639 := bstep (se 1 (by rfl) ⟨2119229, by rfl⟩ : syracuseStep 2825639 = 4238459) B4238459
theorem B1883561 : Blo 1254445 1883561 := bstep (se 2 (by rfl) ⟨706335, by rfl⟩ : syracuseStep 1883561 = 1412671) B1412671
theorem B1883711 : Blo 1254445 1883711 := bstep (se 1 (by rfl) ⟨1412783, by rfl⟩ : syracuseStep 1883711 = 2825567) B2825567
theorem B3178075 : Blo 1254445 3178075 := bstep (se 1 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 3178075 = 4767113) B4767113
theorem B2825819 : Blo 1254445 2825819 := bstep (se 1 (by rfl) ⟨2119364, by rfl⟩ : syracuseStep 2825819 = 4238729) B4238729
theorem B10174061 : Blo 1254445 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B4234895 : Blo 1254445 4234895 := bstep (se 1 (by rfl) ⟨3176171, by rfl⟩ : syracuseStep 4234895 = 6352343) B6352343
theorem B11452103 : Blo 1254445 11452103 := bstep (se 1 (by rfl) ⟨8589077, by rfl⟩ : syracuseStep 11452103 = 17178155) B17178155
theorem B9051857 : Blo 1254445 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B3178217 : Blo 1254445 3178217 := bstep (se 2 (by rfl) ⟨1191831, by rfl⟩ : syracuseStep 3178217 = 2383663) B2383663
theorem B1883975 : Blo 1254445 1883975 := bstep (se 1 (by rfl) ⟨1412981, by rfl⟩ : syracuseStep 1883975 = 2825963) B2825963
theorem B9535319 : Blo 1254445 9535319 := bstep (se 1 (by rfl) ⟨7151489, by rfl⟩ : syracuseStep 9535319 = 14302979) B14302979
theorem B4521851 : Blo 1254445 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B2383739 : Blo 1254445 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B2826107 : Blo 1254445 2826107 := bstep (se 1 (by rfl) ⟨2119580, by rfl⟩ : syracuseStep 2826107 = 4239161) B4239161
theorem B1884059 : Blo 1254445 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B10731473 : Blo 1254445 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B1589215 : Blo 1254445 1589215 := bstep (se 1 (by rfl) ⟨1191911, by rfl⟩ : syracuseStep 1589215 = 2383823) B2383823
theorem B5087357 : Blo 1254445 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B3391679 : Blo 1254445 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B1589483 : Blo 1254445 1589483 := bstep (se 1 (by rfl) ⟨1192112, by rfl⟩ : syracuseStep 1589483 = 2384225) B2384225
theorem B1884395 : Blo 1254445 1884395 := bstep (se 1 (by rfl) ⟨1413296, by rfl⟩ : syracuseStep 1884395 = 2826593) B2826593
theorem B1884455 : Blo 1254445 1884455 := bstep (se 1 (by rfl) ⟨1413341, by rfl⟩ : syracuseStep 1884455 = 2826683) B2826683
theorem B4768253 : Blo 1254445 4768253 := bstep (se 3 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 4768253 = 1788095) B1788095
theorem B2826971 : Blo 1254445 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1909559 : Blo 1254445 1909559 := bstep (se 1 (by rfl) ⟨1432169, by rfl⟩ : syracuseStep 1909559 = 2864339) B2864339
theorem B8586071 : Blo 1254445 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B4834343 : Blo 1254445 4834343 := bstep (se 1 (by rfl) ⟨3625757, by rfl⟩ : syracuseStep 4834343 = 7251515) B7251515
theorem B1254447 : Blo 1254445 1254447 := bstep (se 1 (by rfl) ⟨940835, by rfl⟩ : syracuseStep 1254447 = 1881671) B1881671
theorem B1254511 : Blo 1254445 1254511 := bstep (se 1 (by rfl) ⟨940883, by rfl⟩ : syracuseStep 1254511 = 1881767) B1881767
theorem B11609227 : Blo 1254445 11609227 := bstep (se 1 (by rfl) ⟨8706920, by rfl⟩ : syracuseStep 11609227 = 17413841) B17413841
theorem B12067987 : Blo 1254445 12067987 := bstep (se 1 (by rfl) ⟨9050990, by rfl⟩ : syracuseStep 12067987 = 18101981) B18101981
theorem B1254567 : Blo 1254445 1254567 := bstep (se 1 (by rfl) ⟨940925, by rfl⟩ : syracuseStep 1254567 = 1881851) B1881851
theorem B12059837 : Blo 1254445 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B1254591 : Blo 1254445 1254591 := bstep (se 1 (by rfl) ⟨940943, by rfl⟩ : syracuseStep 1254591 = 1881887) B1881887
theorem B1254623 : Blo 1254445 1254623 := bstep (se 1 (by rfl) ⟨940967, by rfl⟩ : syracuseStep 1254623 = 1881935) B1881935
theorem B19318019 : Blo 1254445 19318019 := bstep (se 1 (by rfl) ⟨14488514, by rfl⟩ : syracuseStep 19318019 = 28977029) B28977029
theorem B1254703 : Blo 1254445 1254703 := bstep (se 1 (by rfl) ⟨941027, by rfl⟩ : syracuseStep 1254703 = 1882055) B1882055
theorem B1254939 : Blo 1254445 1254939 := bstep (se 1 (by rfl) ⟨941204, by rfl⟩ : syracuseStep 1254939 = 1882409) B1882409
theorem B1254943 : Blo 1254445 1254943 := bstep (se 1 (by rfl) ⟨941207, by rfl⟩ : syracuseStep 1254943 = 1882415) B1882415
theorem B2680391 : Blo 1254445 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B1255103 : Blo 1254445 1255103 := bstep (se 1 (by rfl) ⟨941327, by rfl⟩ : syracuseStep 1255103 = 1882655) B1882655
theorem B1255359 : Blo 1254445 1255359 := bstep (se 1 (by rfl) ⟨941519, by rfl⟩ : syracuseStep 1255359 = 1883039) B1883039
theorem B6358985 : Blo 1254445 6358985 := bstep (se 2 (by rfl) ⟨2384619, by rfl⟩ : syracuseStep 6358985 = 4769239) B4769239
theorem B1255391 : Blo 1254445 1255391 := bstep (se 1 (by rfl) ⟨941543, by rfl⟩ : syracuseStep 1255391 = 1883087) B1883087
theorem B1255451 : Blo 1254445 1255451 := bstep (se 1 (by rfl) ⟨941588, by rfl⟩ : syracuseStep 1255451 = 1883177) B1883177
theorem B1255455 : Blo 1254445 1255455 := bstep (se 1 (by rfl) ⟨941591, by rfl⟩ : syracuseStep 1255455 = 1883183) B1883183
theorem B1255471 : Blo 1254445 1255471 := bstep (se 1 (by rfl) ⟨941603, by rfl⟩ : syracuseStep 1255471 = 1883207) B1883207
theorem B4237433 : Blo 1254445 4237433 := bstep (se 2 (by rfl) ⟨1589037, by rfl⟩ : syracuseStep 4237433 = 3178075) B3178075
theorem B2680955 : Blo 1254445 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B9529487 : Blo 1254445 9529487 := bstep (se 1 (by rfl) ⟨7147115, by rfl⟩ : syracuseStep 9529487 = 14294231) B14294231
theorem B1255647 : Blo 1254445 1255647 := bstep (se 1 (by rfl) ⟨941735, by rfl⟩ : syracuseStep 1255647 = 1883471) B1883471
theorem B1255707 : Blo 1254445 1255707 := bstep (se 1 (by rfl) ⟨941780, by rfl⟩ : syracuseStep 1255707 = 1883561) B1883561
theorem B1255807 : Blo 1254445 1255807 := bstep (se 1 (by rfl) ⟨941855, by rfl⟩ : syracuseStep 1255807 = 1883711) B1883711
theorem B1255983 : Blo 1254445 1255983 := bstep (se 1 (by rfl) ⟨941987, by rfl⟩ : syracuseStep 1255983 = 1883975) B1883975
theorem B1256039 : Blo 1254445 1256039 := bstep (se 1 (by rfl) ⟨942029, by rfl⟩ : syracuseStep 1256039 = 1884059) B1884059
theorem B7154315 : Blo 1254445 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B9538235 : Blo 1254445 9538235 := bstep (se 1 (by rfl) ⟨7153676, by rfl⟩ : syracuseStep 9538235 = 14307353) B14307353
theorem B1411879 : Blo 1254445 1411879 := bstep (se 1 (by rfl) ⟨1058909, by rfl⟩ : syracuseStep 1411879 = 2117819) B2117819
theorem B6351695 : Blo 1254445 6351695 := bstep (se 1 (by rfl) ⟨4763771, by rfl⟩ : syracuseStep 6351695 = 9527543) B9527543
theorem B1788841 : Blo 1254445 1788841 := bstep (se 2 (by rfl) ⟨670815, by rfl⟩ : syracuseStep 1788841 = 1341631) B1341631
theorem B14289857 : Blo 1254445 14289857 := bstep (se 2 (by rfl) ⟨5358696, by rfl⟩ : syracuseStep 14289857 = 10717393) B10717393
theorem B1256415 : Blo 1254445 1256415 := bstep (se 1 (by rfl) ⟨942311, by rfl⟩ : syracuseStep 1256415 = 1884623) B1884623
theorem B1256443 : Blo 1254445 1256443 := bstep (se 1 (by rfl) ⟨942332, by rfl⟩ : syracuseStep 1256443 = 1884665) B1884665
theorem B12069985 : Blo 1254445 12069985 := bstep (se 2 (by rfl) ⟨4526244, by rfl⟩ : syracuseStep 12069985 = 9052489) B9052489
theorem B7154999 : Blo 1254445 7154999 := bstep (se 1 (by rfl) ⟨5366249, by rfl⟩ : syracuseStep 7154999 = 10732499) B10732499
theorem B16084291 : Blo 1254445 16084291 := bstep (se 1 (by rfl) ⟨12063218, by rfl⟩ : syracuseStep 16084291 = 24126437) B24126437
theorem B2116955 : Blo 1254445 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B5361005 : Blo 1254445 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B5729773 : Blo 1254445 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B3018343 : Blo 1254445 3018343 := bstep (se 1 (by rfl) ⟨2263757, by rfl⟩ : syracuseStep 3018343 = 4527515) B4527515
theorem B16084655 : Blo 1254445 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B21458843 : Blo 1254445 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B132222937 : Blo 1254445 132222937 := bstep (se 2 (by rfl) ⟨49583601, by rfl⟩ : syracuseStep 132222937 = 99167203) B99167203
theorem B1413103 : Blo 1254445 1413103 := bstep (se 1 (by rfl) ⟨1059827, by rfl⟩ : syracuseStep 1413103 = 2119655) B2119655
theorem B4763681 : Blo 1254445 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B13570085 : Blo 1254445 13570085 := bstep (se 4 (by rfl) ⟨1272195, by rfl⟩ : syracuseStep 13570085 = 2544391) B2544391
theorem B1413247 : Blo 1254445 1413247 := bstep (se 1 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 1413247 = 2119871) B2119871
theorem B4763879 : Blo 1254445 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B27144497 : Blo 1254445 27144497 := bstep (se 2 (by rfl) ⟨10179186, by rfl⟩ : syracuseStep 27144497 = 20358373) B20358373
theorem B2822633 : Blo 1254445 2822633 := bstep (se 2 (by rfl) ⟨1058487, by rfl⟩ : syracuseStep 2822633 = 2116975) B2116975
theorem B4240295 : Blo 1254445 4240295 := bstep (se 1 (by rfl) ⟨3180221, by rfl⟩ : syracuseStep 4240295 = 6360443) B6360443
theorem B18092983 : Blo 1254445 18092983 := bstep (se 1 (by rfl) ⟨13569737, by rfl⟩ : syracuseStep 18092983 = 27139475) B27139475
theorem B2823137 : Blo 1254445 2823137 := bstep (se 2 (by rfl) ⟨1058676, by rfl⟩ : syracuseStep 2823137 = 2117353) B2117353
theorem B2823263 : Blo 1254445 2823263 := bstep (se 1 (by rfl) ⟨2117447, by rfl⟩ : syracuseStep 2823263 = 4234895) B4234895
theorem B6034571 : Blo 1254445 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B2118811 : Blo 1254445 2118811 := bstep (se 1 (by rfl) ⟨1589108, by rfl⟩ : syracuseStep 2118811 = 3178217) B3178217
theorem B2118953 : Blo 1254445 2118953 := bstep (se 2 (by rfl) ⟨794607, by rfl⟩ : syracuseStep 2118953 = 1589215) B1589215
theorem B9663943 : Blo 1254445 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B14308811 : Blo 1254445 14308811 := bstep (se 1 (by rfl) ⟨10731608, by rfl⟩ : syracuseStep 14308811 = 21463217) B21463217
theorem B44086999 : Blo 1254445 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B1881833 : Blo 1254445 1881833 := bstep (se 2 (by rfl) ⟨705687, by rfl⟩ : syracuseStep 1881833 = 1411375) B1411375
theorem B1881839 : Blo 1254445 1881839 := bstep (se 1 (by rfl) ⟨1411379, by rfl⟩ : syracuseStep 1881839 = 2822759) B2822759
theorem B2824019 : Blo 1254445 2824019 := bstep (se 1 (by rfl) ⟨2118014, by rfl⟩ : syracuseStep 2824019 = 4236029) B4236029
theorem B2119547 : Blo 1254445 2119547 := bstep (se 1 (by rfl) ⟨1589660, by rfl⟩ : syracuseStep 2119547 = 3179321) B3179321
theorem B12072833 : Blo 1254445 12072833 := bstep (se 2 (by rfl) ⟨4527312, by rfl⟩ : syracuseStep 12072833 = 9054625) B9054625
theorem B4765655 : Blo 1254445 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B2119817 : Blo 1254445 2119817 := bstep (se 2 (by rfl) ⟨794931, by rfl⟩ : syracuseStep 2119817 = 1589863) B1589863
theorem B1882295 : Blo 1254445 1882295 := bstep (se 1 (by rfl) ⟨1411721, by rfl⟩ : syracuseStep 1882295 = 2823443) B2823443
theorem B1882343 : Blo 1254445 1882343 := bstep (se 1 (by rfl) ⟨1411757, by rfl⟩ : syracuseStep 1882343 = 2823515) B2823515
theorem B2824505 : Blo 1254445 2824505 := bstep (se 2 (by rfl) ⟨1059189, by rfl⟩ : syracuseStep 2824505 = 2118379) B2118379
theorem B2382311 : Blo 1254445 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B1882715 : Blo 1254445 1882715 := bstep (se 1 (by rfl) ⟨1412036, by rfl⟩ : syracuseStep 1882715 = 2824073) B2824073
theorem B1882859 : Blo 1254445 1882859 := bstep (se 1 (by rfl) ⟨1412144, by rfl⟩ : syracuseStep 1882859 = 2824289) B2824289
theorem B1882889 : Blo 1254445 1882889 := bstep (se 2 (by rfl) ⟨706083, by rfl⟩ : syracuseStep 1882889 = 1412167) B1412167
theorem B6781805 : Blo 1254445 6781805 := bstep (se 3 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 6781805 = 2543177) B2543177
theorem B18111437 : Blo 1254445 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B6880247 : Blo 1254445 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B25771085 : Blo 1254445 25771085 := bstep (se 3 (by rfl) ⟨4832078, by rfl⟩ : syracuseStep 25771085 = 9664157) B9664157
theorem B2825423 : Blo 1254445 2825423 := bstep (se 1 (by rfl) ⟨2119067, by rfl⟩ : syracuseStep 2825423 = 4238135) B4238135
theorem B176414021 : Blo 1254445 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B6970835 : Blo 1254445 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B2383337 : Blo 1254445 2383337 := bstep (se 2 (by rfl) ⟨893751, by rfl⟩ : syracuseStep 2383337 = 1787503) B1787503
theorem B4767295 : Blo 1254445 4767295 := bstep (se 1 (by rfl) ⟨3575471, by rfl⟩ : syracuseStep 4767295 = 7150943) B7150943
theorem B2825801 : Blo 1254445 2825801 := bstep (se 2 (by rfl) ⟨1059675, by rfl⟩ : syracuseStep 2825801 = 2119351) B2119351
theorem B1883759 : Blo 1254445 1883759 := bstep (se 1 (by rfl) ⟨1412819, by rfl⟩ : syracuseStep 1883759 = 2825639) B2825639
theorem B2383481 : Blo 1254445 2383481 := bstep (se 2 (by rfl) ⟨893805, by rfl⟩ : syracuseStep 2383481 = 1787611) B1787611
theorem B1883879 : Blo 1254445 1883879 := bstep (se 1 (by rfl) ⟨1412909, by rfl⟩ : syracuseStep 1883879 = 2825819) B2825819
theorem B6782707 : Blo 1254445 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B7634735 : Blo 1254445 7634735 := bstep (se 1 (by rfl) ⟨5726051, by rfl⟩ : syracuseStep 7634735 = 11452103) B11452103
theorem B10460983 : Blo 1254445 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B2416495 : Blo 1254445 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B34381691 : Blo 1254445 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B6356879 : Blo 1254445 6356879 := bstep (se 1 (by rfl) ⟨4767659, by rfl⟩ : syracuseStep 6356879 = 9535319) B9535319
theorem B3014567 : Blo 1254445 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B1589159 : Blo 1254445 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B1884071 : Blo 1254445 1884071 := bstep (se 1 (by rfl) ⟨1413053, by rfl⟩ : syracuseStep 1884071 = 2826107) B2826107
theorem B3391571 : Blo 1254445 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2261119 : Blo 1254445 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B1884329 : Blo 1254445 1884329 := bstep (se 2 (by rfl) ⟨706623, by rfl⟩ : syracuseStep 1884329 = 1413247) B1413247
theorem B18096331 : Blo 1254445 18096331 := bstep (se 1 (by rfl) ⟨13572248, by rfl⟩ : syracuseStep 18096331 = 27144497) B27144497
theorem B3178835 : Blo 1254445 3178835 := bstep (se 1 (by rfl) ⟨2384126, by rfl⟩ : syracuseStep 3178835 = 4768253) B4768253
theorem B1884647 : Blo 1254445 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B2826863 : Blo 1254445 2826863 := bstep (se 1 (by rfl) ⟨2120147, by rfl⟩ : syracuseStep 2826863 = 4240295) B4240295
theorem B61915877 : Blo 1254445 61915877 := bstep (se 4 (by rfl) ⟨5804613, by rfl⟩ : syracuseStep 61915877 = 11609227) B11609227
theorem B4023047 : Blo 1254445 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B1254555 : Blo 1254445 1254555 := bstep (se 1 (by rfl) ⟨940916, by rfl⟩ : syracuseStep 1254555 = 1881833) B1881833
theorem B1254559 : Blo 1254445 1254559 := bstep (se 1 (by rfl) ⟨940919, by rfl⟩ : syracuseStep 1254559 = 1881839) B1881839
theorem B2385121 : Blo 1254445 2385121 := bstep (se 2 (by rfl) ⟨894420, by rfl⟩ : syracuseStep 2385121 = 1788841) B1788841
theorem B1787303 : Blo 1254445 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B1254863 : Blo 1254445 1254863 := bstep (se 1 (by rfl) ⟨941147, by rfl⟩ : syracuseStep 1254863 = 1882295) B1882295
theorem B1254895 : Blo 1254445 1254895 := bstep (se 1 (by rfl) ⟨941171, by rfl⟩ : syracuseStep 1254895 = 1882343) B1882343
theorem B16090649 : Blo 1254445 16090649 := bstep (se 2 (by rfl) ⟨6033993, by rfl⟩ : syracuseStep 16090649 = 12067987) B12067987
theorem B1255143 : Blo 1254445 1255143 := bstep (se 1 (by rfl) ⟨941357, by rfl⟩ : syracuseStep 1255143 = 1882715) B1882715
theorem B4769543 : Blo 1254445 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B6358823 : Blo 1254445 6358823 := bstep (se 1 (by rfl) ⟨4769117, by rfl⟩ : syracuseStep 6358823 = 9538235) B9538235
theorem B1255239 : Blo 1254445 1255239 := bstep (se 1 (by rfl) ⟨941429, by rfl⟩ : syracuseStep 1255239 = 1882859) B1882859
theorem B1255259 : Blo 1254445 1255259 := bstep (se 1 (by rfl) ⟨941444, by rfl⟩ : syracuseStep 1255259 = 1882889) B1882889
theorem B17180723 : Blo 1254445 17180723 := bstep (se 1 (by rfl) ⟨12885542, by rfl⟩ : syracuseStep 17180723 = 25771085) B25771085
theorem B4024457 : Blo 1254445 4024457 := bstep (se 2 (by rfl) ⟨1509171, by rfl⟩ : syracuseStep 4024457 = 3018343) B3018343
theorem B4769999 : Blo 1254445 4769999 := bstep (se 1 (by rfl) ⟨3577499, by rfl⟩ : syracuseStep 4769999 = 7154999) B7154999
theorem B1411303 : Blo 1254445 1411303 := bstep (se 1 (by rfl) ⟨1058477, by rfl⟩ : syracuseStep 1411303 = 2116955) B2116955
theorem B3574003 : Blo 1254445 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B4647223 : Blo 1254445 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1255839 : Blo 1254445 1255839 := bstep (se 1 (by rfl) ⟨941879, by rfl⟩ : syracuseStep 1255839 = 1883759) B1883759
theorem B4237757 : Blo 1254445 4237757 := bstep (se 3 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 4237757 = 1589159) B1589159
theorem B3221993 : Blo 1254445 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B1255919 : Blo 1254445 1255919 := bstep (se 1 (by rfl) ⟨941939, by rfl⟩ : syracuseStep 1255919 = 1883879) B1883879
theorem B5089823 : Blo 1254445 5089823 := bstep (se 1 (by rfl) ⟨3817367, by rfl⟩ : syracuseStep 5089823 = 7634735) B7634735
theorem B4237919 : Blo 1254445 4237919 := bstep (se 1 (by rfl) ⟨3178439, by rfl⟩ : syracuseStep 4237919 = 6356879) B6356879
theorem B14305895 : Blo 1254445 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B2009711 : Blo 1254445 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B1256047 : Blo 1254445 1256047 := bstep (se 1 (by rfl) ⟨942035, by rfl⟩ : syracuseStep 1256047 = 1884071) B1884071
theorem B9046723 : Blo 1254445 9046723 := bstep (se 1 (by rfl) ⟨6785042, by rfl⟩ : syracuseStep 9046723 = 13570085) B13570085
theorem B1256263 : Blo 1254445 1256263 := bstep (se 1 (by rfl) ⟨942197, by rfl⟩ : syracuseStep 1256263 = 1884395) B1884395
theorem B1256303 : Blo 1254445 1256303 := bstep (se 1 (by rfl) ⟨942227, by rfl⟩ : syracuseStep 1256303 = 1884455) B1884455
theorem B1273039 : Blo 1254445 1273039 := bstep (se 1 (by rfl) ⟨954779, by rfl⟩ : syracuseStep 1273039 = 1909559) B1909559
theorem B4238621 : Blo 1254445 4238621 := bstep (se 3 (by rfl) ⟨794741, by rfl⟩ : syracuseStep 4238621 = 1589483) B1589483
theorem B51514717 : Blo 1254445 51514717 := bstep (se 3 (by rfl) ⟨9659009, by rfl⟩ : syracuseStep 51514717 = 19318019) B19318019
theorem B8039891 : Blo 1254445 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B1412635 : Blo 1254445 1412635 := bstep (se 1 (by rfl) ⟨1059476, by rfl⟩ : syracuseStep 1412635 = 2118953) B2118953
theorem B9539207 : Blo 1254445 9539207 := bstep (se 1 (by rfl) ⟨7154405, by rfl⟩ : syracuseStep 9539207 = 14308811) B14308811
theorem B1413031 : Blo 1254445 1413031 := bstep (se 1 (by rfl) ⟨1059773, by rfl⟩ : syracuseStep 1413031 = 2119547) B2119547
theorem B8048555 : Blo 1254445 8048555 := bstep (se 1 (by rfl) ⟨6036416, by rfl⟩ : syracuseStep 8048555 = 12072833) B12072833
theorem B6352829 : Blo 1254445 6352829 := bstep (se 3 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 6352829 = 2382311) B2382311
theorem B4239323 : Blo 1254445 4239323 := bstep (se 1 (by rfl) ⟨3179492, by rfl⟩ : syracuseStep 4239323 = 6358985) B6358985
theorem B1413211 : Blo 1254445 1413211 := bstep (se 1 (by rfl) ⟨1059908, by rfl⟩ : syracuseStep 1413211 = 2119817) B2119817
theorem B6352991 : Blo 1254445 6352991 := bstep (se 1 (by rfl) ⟨4764743, by rfl⟩ : syracuseStep 6352991 = 9529487) B9529487
theorem B16093313 : Blo 1254445 16093313 := bstep (se 2 (by rfl) ⟨6034992, by rfl⟩ : syracuseStep 16093313 = 12069985) B12069985
theorem B7147709 : Blo 1254445 7147709 := bstep (se 3 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 7147709 = 2680391) B2680391
theorem B7639697 : Blo 1254445 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B117609347 : Blo 1254445 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B58782665 : Blo 1254445 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B13947977 : Blo 1254445 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B176297249 : Blo 1254445 176297249 := bstep (se 2 (by rfl) ⟨66111468, by rfl⟩ : syracuseStep 176297249 = 132222937) B132222937
theorem B3175787 : Blo 1254445 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B12891581 : Blo 1254445 12891581 := bstep (se 3 (by rfl) ⟨2417171, by rfl⟩ : syracuseStep 12891581 = 4834343) B4834343
theorem B3175919 : Blo 1254445 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B1881755 : Blo 1254445 1881755 := bstep (se 1 (by rfl) ⟨1411316, by rfl⟩ : syracuseStep 1881755 = 2822633) B2822633
theorem B5724047 : Blo 1254445 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B1882091 : Blo 1254445 1882091 := bstep (se 1 (by rfl) ⟨1411568, by rfl⟩ : syracuseStep 1882091 = 2823137) B2823137
theorem B1882175 : Blo 1254445 1882175 := bstep (se 1 (by rfl) ⟨1411631, by rfl⟩ : syracuseStep 1882175 = 2823263) B2823263
theorem B1882505 : Blo 1254445 1882505 := bstep (se 2 (by rfl) ⟨705939, by rfl⟩ : syracuseStep 1882505 = 1411879) B1411879
theorem B1882679 : Blo 1254445 1882679 := bstep (se 1 (by rfl) ⟨1412009, by rfl⟩ : syracuseStep 1882679 = 2824019) B2824019
theorem B24123977 : Blo 1254445 24123977 := bstep (se 2 (by rfl) ⟨9046491, by rfl⟩ : syracuseStep 24123977 = 18092983) B18092983
theorem B36174437 : Blo 1254445 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B3177103 : Blo 1254445 3177103 := bstep (se 1 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 3177103 = 4765655) B4765655
theorem B2824955 : Blo 1254445 2824955 := bstep (se 1 (by rfl) ⟨2118716, by rfl⟩ : syracuseStep 2824955 = 4237433) B4237433
theorem B2825081 : Blo 1254445 2825081 := bstep (se 2 (by rfl) ⟨1059405, by rfl⟩ : syracuseStep 2825081 = 2118811) B2118811
theorem B1883003 : Blo 1254445 1883003 := bstep (se 1 (by rfl) ⟨1412252, by rfl⟩ : syracuseStep 1883003 = 2824505) B2824505
theorem B21445721 : Blo 1254445 21445721 := bstep (se 2 (by rfl) ⟨8042145, by rfl⟩ : syracuseStep 21445721 = 16084291) B16084291
theorem B4234463 : Blo 1254445 4234463 := bstep (se 1 (by rfl) ⟨3175847, by rfl⟩ : syracuseStep 4234463 = 6351695) B6351695
theorem B4521203 : Blo 1254445 4521203 := bstep (se 1 (by rfl) ⟨3390902, by rfl⟩ : syracuseStep 4521203 = 6781805) B6781805
theorem B12885257 : Blo 1254445 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B9526571 : Blo 1254445 9526571 := bstep (se 1 (by rfl) ⟨7144928, by rfl⟩ : syracuseStep 9526571 = 14289857) B14289857
theorem B12074291 : Blo 1254445 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B4586831 : Blo 1254445 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B6356393 : Blo 1254445 6356393 := bstep (se 2 (by rfl) ⟨2383647, by rfl⟩ : syracuseStep 6356393 = 4767295) B4767295
theorem B1883615 : Blo 1254445 1883615 := bstep (se 1 (by rfl) ⟨1412711, by rfl⟩ : syracuseStep 1883615 = 2825423) B2825423
theorem B1588891 : Blo 1254445 1588891 := bstep (se 1 (by rfl) ⟨1191668, by rfl⟩ : syracuseStep 1588891 = 2383337) B2383337
theorem B1883867 : Blo 1254445 1883867 := bstep (se 1 (by rfl) ⟨1412900, by rfl⟩ : syracuseStep 1883867 = 2825801) B2825801
theorem B1588987 : Blo 1254445 1588987 := bstep (se 1 (by rfl) ⟨1191740, by rfl⟩ : syracuseStep 1588987 = 2383481) B2383481
theorem B10723103 : Blo 1254445 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B22921127 : Blo 1254445 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B1884137 : Blo 1254445 1884137 := bstep (se 2 (by rfl) ⟨706551, by rfl⟩ : syracuseStep 1884137 = 1413103) B1413103
theorem B2261047 : Blo 1254445 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B4235327 : Blo 1254445 4235327 := bstep (se 1 (by rfl) ⟨3176495, by rfl⟩ : syracuseStep 4235327 = 6352991) B6352991
theorem B1884281 : Blo 1254445 1884281 := bstep (se 2 (by rfl) ⟨706605, by rfl⟩ : syracuseStep 1884281 = 1413211) B1413211
theorem B3014825 : Blo 1254445 3014825 := bstep (se 2 (by rfl) ⟨1130559, by rfl⟩ : syracuseStep 3014825 = 2261119) B2261119
theorem B1884575 : Blo 1254445 1884575 := bstep (se 1 (by rfl) ⟨1413431, by rfl⟩ : syracuseStep 1884575 = 2826863) B2826863
theorem B9298651 : Blo 1254445 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B4236137 : Blo 1254445 4236137 := bstep (se 2 (by rfl) ⟨1588551, by rfl⟩ : syracuseStep 4236137 = 3177103) B3177103
theorem B117531499 : Blo 1254445 117531499 := bstep (se 1 (by rfl) ⟨88148624, by rfl⟩ : syracuseStep 117531499 = 176297249) B176297249
theorem B8594387 : Blo 1254445 8594387 := bstep (se 1 (by rfl) ⟨6445790, by rfl⟩ : syracuseStep 8594387 = 12891581) B12891581
theorem B1254503 : Blo 1254445 1254503 := bstep (se 1 (by rfl) ⟨940877, by rfl⟩ : syracuseStep 1254503 = 1881755) B1881755
theorem B3179695 : Blo 1254445 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B1254727 : Blo 1254445 1254727 := bstep (se 1 (by rfl) ⟨941045, by rfl⟩ : syracuseStep 1254727 = 1882091) B1882091
theorem B11453815 : Blo 1254445 11453815 := bstep (se 1 (by rfl) ⟨8590361, by rfl⟩ : syracuseStep 11453815 = 17180723) B17180723
theorem B1254783 : Blo 1254445 1254783 := bstep (se 1 (by rfl) ⟨941087, by rfl⟩ : syracuseStep 1254783 = 1882175) B1882175
theorem B3179999 : Blo 1254445 3179999 := bstep (se 1 (by rfl) ⟨2384999, by rfl⟩ : syracuseStep 3179999 = 4769999) B4769999
theorem B1255003 : Blo 1254445 1255003 := bstep (se 1 (by rfl) ⟨941252, by rfl⟩ : syracuseStep 1255003 = 1882505) B1882505
theorem B5359229 : Blo 1254445 5359229 := bstep (se 3 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 5359229 = 2009711) B2009711
theorem B3180161 : Blo 1254445 3180161 := bstep (se 2 (by rfl) ⟨1192560, by rfl⟩ : syracuseStep 3180161 = 2385121) B2385121
theorem B27158165 : Blo 1254445 27158165 := bstep (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) B1273039
theorem B2147995 : Blo 1254445 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B3393215 : Blo 1254445 3393215 := bstep (se 1 (by rfl) ⟨2544911, by rfl⟩ : syracuseStep 3393215 = 5089823) B5089823
theorem B1255119 : Blo 1254445 1255119 := bstep (se 1 (by rfl) ⟨941339, by rfl⟩ : syracuseStep 1255119 = 1882679) B1882679
theorem B16082651 : Blo 1254445 16082651 := bstep (se 1 (by rfl) ⟨12061988, by rfl⟩ : syracuseStep 16082651 = 24123977) B24123977
theorem B9537263 : Blo 1254445 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B1255335 : Blo 1254445 1255335 := bstep (se 1 (by rfl) ⟨941501, by rfl⟩ : syracuseStep 1255335 = 1883003) B1883003
theorem B14297147 : Blo 1254445 14297147 := bstep (se 1 (by rfl) ⟨10722860, by rfl⟩ : syracuseStep 14297147 = 21445721) B21445721
theorem B6351047 : Blo 1254445 6351047 := bstep (se 1 (by rfl) ⟨4763285, by rfl⟩ : syracuseStep 6351047 = 9526571) B9526571
theorem B3057887 : Blo 1254445 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B4237595 : Blo 1254445 4237595 := bstep (se 1 (by rfl) ⟨3178196, by rfl⟩ : syracuseStep 4237595 = 6356393) B6356393
theorem B5359927 : Blo 1254445 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B1255743 : Blo 1254445 1255743 := bstep (se 1 (by rfl) ⟨941807, by rfl⟩ : syracuseStep 1255743 = 1883615) B1883615
theorem B313624925 : Blo 1254445 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B6359471 : Blo 1254445 6359471 := bstep (se 1 (by rfl) ⟨4769603, by rfl⟩ : syracuseStep 6359471 = 9539207) B9539207
theorem B1255911 : Blo 1254445 1255911 := bstep (se 1 (by rfl) ⟨941933, by rfl⟩ : syracuseStep 1255911 = 1883867) B1883867
theorem B15280751 : Blo 1254445 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1256091 : Blo 1254445 1256091 := bstep (se 1 (by rfl) ⟨942068, by rfl⟩ : syracuseStep 1256091 = 1884137) B1884137
theorem B1256219 : Blo 1254445 1256219 := bstep (se 1 (by rfl) ⟨942164, by rfl⟩ : syracuseStep 1256219 = 1884329) B1884329
theorem B24128441 : Blo 1254445 24128441 := bstep (se 2 (by rfl) ⟨9048165, by rfl⟩ : syracuseStep 24128441 = 18096331) B18096331
theorem B1256431 : Blo 1254445 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B2117191 : Blo 1254445 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B12062297 : Blo 1254445 12062297 := bstep (se 2 (by rfl) ⟨4523361, by rfl⟩ : syracuseStep 12062297 = 9046723) B9046723
theorem B2117279 : Blo 1254445 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B10727099 : Blo 1254445 10727099 := bstep (se 1 (by rfl) ⟨8045324, by rfl⟩ : syracuseStep 10727099 = 16090649) B16090649
theorem B4239215 : Blo 1254445 4239215 := bstep (se 1 (by rfl) ⟨3179411, by rfl⟩ : syracuseStep 4239215 = 6358823) B6358823
theorem B2682971 : Blo 1254445 2682971 := bstep (se 1 (by rfl) ⟨2012228, by rfl⟩ : syracuseStep 2682971 = 4024457) B4024457
theorem B24785189 : Blo 1254445 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B68686289 : Blo 1254445 68686289 := bstep (se 2 (by rfl) ⟨25757358, by rfl⟩ : syracuseStep 68686289 = 51514717) B51514717
theorem B10728125 : Blo 1254445 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B2822975 : Blo 1254445 2822975 := bstep (se 1 (by rfl) ⟨2117231, by rfl⟩ : syracuseStep 2822975 = 4234463) B4234463
theorem B8590171 : Blo 1254445 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B8049527 : Blo 1254445 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B2118521 : Blo 1254445 2118521 := bstep (se 2 (by rfl) ⟨794445, by rfl⟩ : syracuseStep 2118521 = 1588891) B1588891
theorem B2118649 : Blo 1254445 2118649 := bstep (se 2 (by rfl) ⟨794493, by rfl⟩ : syracuseStep 2118649 = 1588987) B1588987
theorem B7148735 : Blo 1254445 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B10728875 : Blo 1254445 10728875 := bstep (se 1 (by rfl) ⟨8046656, by rfl⟩ : syracuseStep 10728875 = 16093313) B16093313
theorem B4765139 : Blo 1254445 4765139 := bstep (se 1 (by rfl) ⟨3573854, by rfl⟩ : syracuseStep 4765139 = 7147709) B7147709
theorem B2119223 : Blo 1254445 2119223 := bstep (se 1 (by rfl) ⟨1589417, by rfl⟩ : syracuseStep 2119223 = 3178835) B3178835
theorem B1881737 : Blo 1254445 1881737 := bstep (se 2 (by rfl) ⟨705651, by rfl⟩ : syracuseStep 1881737 = 1411303) B1411303
theorem B4765337 : Blo 1254445 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B5093131 : Blo 1254445 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B41277251 : Blo 1254445 41277251 := bstep (se 1 (by rfl) ⟨30957938, by rfl⟩ : syracuseStep 41277251 = 61915877) B61915877
theorem B39188443 : Blo 1254445 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B4766141 : Blo 1254445 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B3816031 : Blo 1254445 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B2825171 : Blo 1254445 2825171 := bstep (se 1 (by rfl) ⟨2118878, by rfl⟩ : syracuseStep 2825171 = 4237757) B4237757
theorem B2825279 : Blo 1254445 2825279 := bstep (se 1 (by rfl) ⟨2118959, by rfl⟩ : syracuseStep 2825279 = 4237919) B4237919
theorem B24116291 : Blo 1254445 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B1883303 : Blo 1254445 1883303 := bstep (se 1 (by rfl) ⟨1412477, by rfl⟩ : syracuseStep 1883303 = 2824955) B2824955
theorem B1883387 : Blo 1254445 1883387 := bstep (se 1 (by rfl) ⟨1412540, by rfl⟩ : syracuseStep 1883387 = 2825081) B2825081
theorem B1883513 : Blo 1254445 1883513 := bstep (se 2 (by rfl) ⟨706317, by rfl⟩ : syracuseStep 1883513 = 1412635) B1412635
theorem B3014135 : Blo 1254445 3014135 := bstep (se 1 (by rfl) ⟨2260601, by rfl⟩ : syracuseStep 3014135 = 4521203) B4521203
theorem B2825747 : Blo 1254445 2825747 := bstep (se 1 (by rfl) ⟨2119310, by rfl⟩ : syracuseStep 2825747 = 4238621) B4238621
theorem B1884041 : Blo 1254445 1884041 := bstep (se 2 (by rfl) ⟨706515, by rfl⟩ : syracuseStep 1884041 = 1413031) B1413031
theorem B5365703 : Blo 1254445 5365703 := bstep (se 1 (by rfl) ⟨4024277, by rfl⟩ : syracuseStep 5365703 = 8048555) B8048555
theorem B4235219 : Blo 1254445 4235219 := bstep (se 1 (by rfl) ⟨3176414, by rfl⟩ : syracuseStep 4235219 = 6352829) B6352829
theorem B2826215 : Blo 1254445 2826215 := bstep (se 1 (by rfl) ⟨2119661, by rfl⟩ : syracuseStep 2826215 = 4239323) B4239323
theorem B3014729 : Blo 1254445 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B16523459 : Blo 1254445 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B7152083 : Blo 1254445 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B5366351 : Blo 1254445 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B5088041 : Blo 1254445 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B7152583 : Blo 1254445 7152583 := bstep (se 1 (by rfl) ⟨5364437, by rfl⟩ : syracuseStep 7152583 = 10728875) B10728875
theorem B3572819 : Blo 1254445 3572819 := bstep (se 1 (by rfl) ⟨2679614, by rfl⟩ : syracuseStep 3572819 = 5359229) B5359229
theorem B1254491 : Blo 1254445 1254491 := bstep (se 1 (by rfl) ⟨940868, by rfl⟩ : syracuseStep 1254491 = 1881737) B1881737
theorem B18105443 : Blo 1254445 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B11453561 : Blo 1254445 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B2262143 : Blo 1254445 2262143 := bstep (se 1 (by rfl) ⟨1696607, by rfl⟩ : syracuseStep 2262143 = 3393215) B3393215
theorem B6358175 : Blo 1254445 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B27518167 : Blo 1254445 27518167 := bstep (se 1 (by rfl) ⟨20638625, by rfl⟩ : syracuseStep 27518167 = 41277251) B41277251
theorem B15271753 : Blo 1254445 15271753 := bstep (se 2 (by rfl) ⟨5726907, by rfl⟩ : syracuseStep 15271753 = 11453815) B11453815
theorem B1255535 : Blo 1254445 1255535 := bstep (se 1 (by rfl) ⟨941651, by rfl⟩ : syracuseStep 1255535 = 1883303) B1883303
theorem B1255591 : Blo 1254445 1255591 := bstep (se 1 (by rfl) ⟨941693, by rfl⟩ : syracuseStep 1255591 = 1883387) B1883387
theorem B1255675 : Blo 1254445 1255675 := bstep (se 1 (by rfl) ⟨941756, by rfl⟩ : syracuseStep 1255675 = 1883513) B1883513
theorem B2009423 : Blo 1254445 2009423 := bstep (se 1 (by rfl) ⟨1507067, by rfl⟩ : syracuseStep 2009423 = 3014135) B3014135
theorem B1411519 : Blo 1254445 1411519 := bstep (se 1 (by rfl) ⟨1058639, by rfl⟩ : syracuseStep 1411519 = 2117279) B2117279
theorem B1256027 : Blo 1254445 1256027 := bstep (se 1 (by rfl) ⟨942020, by rfl⟩ : syracuseStep 1256027 = 1884041) B1884041
theorem B52251257 : Blo 1254445 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B1788647 : Blo 1254445 1788647 := bstep (se 1 (by rfl) ⟨1341485, by rfl⟩ : syracuseStep 1788647 = 2682971) B2682971
theorem B1256187 : Blo 1254445 1256187 := bstep (se 1 (by rfl) ⟨942140, by rfl⟩ : syracuseStep 1256187 = 1884281) B1884281
theorem B1256383 : Blo 1254445 1256383 := bstep (se 1 (by rfl) ⟨942287, by rfl⟩ : syracuseStep 1256383 = 1884575) B1884575
theorem B7146569 : Blo 1254445 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B8039533 : Blo 1254445 8039533 := bstep (se 3 (by rfl) ⟨1507412, by rfl⟩ : syracuseStep 8039533 = 3014825) B3014825
theorem B1412347 : Blo 1254445 1412347 := bstep (se 1 (by rfl) ⟨1059260, by rfl⟩ : syracuseStep 1412347 = 2118521) B2118521
theorem B5729591 : Blo 1254445 5729591 := bstep (se 1 (by rfl) ⟨4297193, by rfl⟩ : syracuseStep 5729591 = 8594387) B8594387
theorem B12398201 : Blo 1254445 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B1412815 : Blo 1254445 1412815 := bstep (se 1 (by rfl) ⟨1059611, by rfl⟩ : syracuseStep 1412815 = 2119223) B2119223
theorem B156708665 : Blo 1254445 156708665 := bstep (se 2 (by rfl) ⟨58765749, by rfl⟩ : syracuseStep 156708665 = 117531499) B117531499
theorem B9531431 : Blo 1254445 9531431 := bstep (se 1 (by rfl) ⟨7148573, by rfl⟩ : syracuseStep 9531431 = 14297147) B14297147
theorem B4239593 : Blo 1254445 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B4239647 : Blo 1254445 4239647 := bstep (se 1 (by rfl) ⟨3179735, by rfl⟩ : syracuseStep 4239647 = 6359471) B6359471
theorem B10187167 : Blo 1254445 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B16085627 : Blo 1254445 16085627 := bstep (se 1 (by rfl) ⟨12064220, by rfl⟩ : syracuseStep 16085627 = 24128441) B24128441
theorem B16077527 : Blo 1254445 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B2822921 : Blo 1254445 2822921 := bstep (se 2 (by rfl) ⟨1058595, by rfl⟩ : syracuseStep 2822921 = 2117191) B2117191
theorem B2863993 : Blo 1254445 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B8041531 : Blo 1254445 8041531 := bstep (se 1 (by rfl) ⟨6031148, by rfl⟩ : syracuseStep 8041531 = 12062297) B12062297
theorem B3577135 : Blo 1254445 3577135 := bstep (se 1 (by rfl) ⟨2682851, by rfl⟩ : syracuseStep 3577135 = 5365703) B5365703
theorem B2823479 : Blo 1254445 2823479 := bstep (se 1 (by rfl) ⟨2117609, by rfl⟩ : syracuseStep 2823479 = 4235219) B4235219
theorem B2823551 : Blo 1254445 2823551 := bstep (se 1 (by rfl) ⟨2117663, by rfl⟩ : syracuseStep 2823551 = 4235327) B4235327
theorem B45790859 : Blo 1254445 45790859 := bstep (se 1 (by rfl) ⟨34343144, by rfl⟩ : syracuseStep 45790859 = 68686289) B68686289
theorem B1881983 : Blo 1254445 1881983 := bstep (se 1 (by rfl) ⟨1411487, by rfl⟩ : syracuseStep 1881983 = 2822975) B2822975
theorem B2824091 : Blo 1254445 2824091 := bstep (se 1 (by rfl) ⟨2118068, by rfl⟩ : syracuseStep 2824091 = 4236137) B4236137
theorem B4765823 : Blo 1254445 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B3176759 : Blo 1254445 3176759 := bstep (se 1 (by rfl) ⟨2382569, by rfl⟩ : syracuseStep 3176759 = 4765139) B4765139
theorem B2119999 : Blo 1254445 2119999 := bstep (se 1 (by rfl) ⟨1589999, by rfl⟩ : syracuseStep 2119999 = 3179999) B3179999
theorem B2120107 : Blo 1254445 2120107 := bstep (se 1 (by rfl) ⟨1590080, by rfl⟩ : syracuseStep 2120107 = 3180161) B3180161
theorem B3176891 : Blo 1254445 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B10721767 : Blo 1254445 10721767 := bstep (se 1 (by rfl) ⟨8041325, by rfl⟩ : syracuseStep 10721767 = 16082651) B16082651
theorem B2824865 : Blo 1254445 2824865 := bstep (se 2 (by rfl) ⟨1059324, by rfl⟩ : syracuseStep 2824865 = 2118649) B2118649
theorem B4234031 : Blo 1254445 4234031 := bstep (se 1 (by rfl) ⟨3175523, by rfl⟩ : syracuseStep 4234031 = 6351047) B6351047
theorem B2038591 : Blo 1254445 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B2825063 : Blo 1254445 2825063 := bstep (se 1 (by rfl) ⟨2118797, by rfl⟩ : syracuseStep 2825063 = 4237595) B4237595
theorem B209083283 : Blo 1254445 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B3177427 : Blo 1254445 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B1883447 : Blo 1254445 1883447 := bstep (se 1 (by rfl) ⟨1412585, by rfl⟩ : syracuseStep 1883447 = 2825171) B2825171
theorem B1883519 : Blo 1254445 1883519 := bstep (se 1 (by rfl) ⟨1412639, by rfl⟩ : syracuseStep 1883519 = 2825279) B2825279
theorem B1883831 : Blo 1254445 1883831 := bstep (se 1 (by rfl) ⟨1412873, by rfl⟩ : syracuseStep 1883831 = 2825747) B2825747
theorem B6790841 : Blo 1254445 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B7151399 : Blo 1254445 7151399 := bstep (se 1 (by rfl) ⟨5363549, by rfl⟩ : syracuseStep 7151399 = 10727099) B10727099
theorem B2826143 : Blo 1254445 2826143 := bstep (se 1 (by rfl) ⟨2119607, by rfl⟩ : syracuseStep 2826143 = 4239215) B4239215
theorem B1884143 : Blo 1254445 1884143 := bstep (se 1 (by rfl) ⟨1413107, by rfl⟩ : syracuseStep 1884143 = 2826215) B2826215
theorem B2826395 : Blo 1254445 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B2826431 : Blo 1254445 2826431 := bstep (se 1 (by rfl) ⟨2119823, by rfl⟩ : syracuseStep 2826431 = 4239647) B4239647
theorem B4768055 : Blo 1254445 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B10723751 : Blo 1254445 10723751 := bstep (se 1 (by rfl) ⟨8042813, by rfl⟩ : syracuseStep 10723751 = 16085627) B16085627
theorem B2826665 : Blo 1254445 2826665 := bstep (se 2 (by rfl) ⟨1059999, by rfl⟩ : syracuseStep 2826665 = 2119999) B2119999
theorem B3392027 : Blo 1254445 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B13582889 : Blo 1254445 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B2826809 : Blo 1254445 2826809 := bstep (se 2 (by rfl) ⟨1060053, by rfl⟩ : syracuseStep 2826809 = 2120107) B2120107
theorem B14295689 : Blo 1254445 14295689 := bstep (se 2 (by rfl) ⟨5360883, by rfl⟩ : syracuseStep 14295689 = 10721767) B10721767
theorem B7635707 : Blo 1254445 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1508095 : Blo 1254445 1508095 := bstep (se 1 (by rfl) ⟨1131071, by rfl⟩ : syracuseStep 1508095 = 2262143) B2262143
theorem B3818657 : Blo 1254445 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B1254655 : Blo 1254445 1254655 := bstep (se 1 (by rfl) ⟨940991, by rfl⟩ : syracuseStep 1254655 = 1881983) B1881983
theorem B9536777 : Blo 1254445 9536777 := bstep (se 2 (by rfl) ⟨3576291, by rfl⟩ : syracuseStep 9536777 = 7152583) B7152583
theorem B4236569 : Blo 1254445 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B10872485 : Blo 1254445 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B4769513 : Blo 1254445 4769513 := bstep (se 2 (by rfl) ⟨1788567, by rfl⟩ : syracuseStep 4769513 = 3577135) B3577135
theorem B34834171 : Blo 1254445 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B139388855 : Blo 1254445 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B4769725 : Blo 1254445 4769725 := bstep (se 3 (by rfl) ⟨894323, by rfl⟩ : syracuseStep 4769725 = 1788647) B1788647
theorem B1255631 : Blo 1254445 1255631 := bstep (se 1 (by rfl) ⟨941723, by rfl⟩ : syracuseStep 1255631 = 1883447) B1883447
theorem B3819727 : Blo 1254445 3819727 := bstep (se 1 (by rfl) ⟨2864795, by rfl⟩ : syracuseStep 3819727 = 5729591) B5729591
theorem B1255679 : Blo 1254445 1255679 := bstep (se 1 (by rfl) ⟨941759, by rfl⟩ : syracuseStep 1255679 = 1883519) B1883519
theorem B1255887 : Blo 1254445 1255887 := bstep (se 1 (by rfl) ⟨941915, by rfl⟩ : syracuseStep 1255887 = 1883831) B1883831
theorem B1256095 : Blo 1254445 1256095 := bstep (se 1 (by rfl) ⟨942071, by rfl⟩ : syracuseStep 1256095 = 1884143) B1884143
theorem B2009819 : Blo 1254445 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B10718351 : Blo 1254445 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B12070295 : Blo 1254445 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B4238783 : Blo 1254445 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B10719377 : Blo 1254445 10719377 := bstep (se 2 (by rfl) ⟨4019766, by rfl⟩ : syracuseStep 10719377 = 8039533) B8039533
theorem B2117839 : Blo 1254445 2117839 := bstep (se 1 (by rfl) ⟨1588379, by rfl⟩ : syracuseStep 2117839 = 3176759) B3176759
theorem B1339615 : Blo 1254445 1339615 := bstep (se 1 (by rfl) ⟨1004711, by rfl⟩ : syracuseStep 1339615 = 2009423) B2009423
theorem B2117927 : Blo 1254445 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B2822687 : Blo 1254445 2822687 := bstep (se 1 (by rfl) ⟨2117015, by rfl⟩ : syracuseStep 2822687 = 4234031) B4234031
theorem B4764379 : Blo 1254445 4764379 := bstep (se 1 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 4764379 = 7146569) B7146569
theorem B20362337 : Blo 1254445 20362337 := bstep (se 2 (by rfl) ⟨7635876, by rfl⟩ : syracuseStep 20362337 = 15271753) B15271753
theorem B4527227 : Blo 1254445 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B6354287 : Blo 1254445 6354287 := bstep (se 1 (by rfl) ⟨4765715, by rfl⟩ : syracuseStep 6354287 = 9531431) B9531431
theorem B11015639 : Blo 1254445 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B1881947 : Blo 1254445 1881947 := bstep (se 1 (by rfl) ⟨1411460, by rfl⟩ : syracuseStep 1881947 = 2822921) B2822921
theorem B1882025 : Blo 1254445 1882025 := bstep (se 2 (by rfl) ⟨705759, by rfl⟩ : syracuseStep 1882025 = 1411519) B1411519
theorem B2381879 : Blo 1254445 2381879 := bstep (se 1 (by rfl) ⟨1786409, by rfl⟩ : syracuseStep 2381879 = 3572819) B3572819
theorem B1882319 : Blo 1254445 1882319 := bstep (se 1 (by rfl) ⟨1411739, by rfl⟩ : syracuseStep 1882319 = 2823479) B2823479
theorem B1882367 : Blo 1254445 1882367 := bstep (se 1 (by rfl) ⟨1411775, by rfl⟩ : syracuseStep 1882367 = 2823551) B2823551
theorem B1882727 : Blo 1254445 1882727 := bstep (se 1 (by rfl) ⟨1412045, by rfl⟩ : syracuseStep 1882727 = 2824091) B2824091
theorem B10722041 : Blo 1254445 10722041 := bstep (se 2 (by rfl) ⟨4020765, by rfl⟩ : syracuseStep 10722041 = 8041531) B8041531
theorem B3177215 : Blo 1254445 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B14310269 : Blo 1254445 14310269 := bstep (se 3 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 14310269 = 5366351) B5366351
theorem B36690889 : Blo 1254445 36690889 := bstep (se 2 (by rfl) ⟨13759083, by rfl⟩ : syracuseStep 36690889 = 27518167) B27518167
theorem B1883129 : Blo 1254445 1883129 := bstep (se 2 (by rfl) ⟨706173, by rfl⟩ : syracuseStep 1883129 = 1412347) B1412347
theorem B122108957 : Blo 1254445 122108957 := bstep (se 3 (by rfl) ⟨22895429, by rfl⟩ : syracuseStep 122108957 = 45790859) B45790859
theorem B1883243 : Blo 1254445 1883243 := bstep (se 1 (by rfl) ⟨1412432, by rfl⟩ : syracuseStep 1883243 = 2824865) B2824865
theorem B1883375 : Blo 1254445 1883375 := bstep (se 1 (by rfl) ⟨1412531, by rfl⟩ : syracuseStep 1883375 = 2825063) B2825063
theorem B1883753 : Blo 1254445 1883753 := bstep (se 2 (by rfl) ⟨706407, by rfl⟩ : syracuseStep 1883753 = 1412815) B1412815
theorem B8265467 : Blo 1254445 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B4767599 : Blo 1254445 4767599 := bstep (se 1 (by rfl) ⟨3575699, by rfl⟩ : syracuseStep 4767599 = 7151399) B7151399
theorem B104472443 : Blo 1254445 104472443 := bstep (se 1 (by rfl) ⟨78354332, by rfl⟩ : syracuseStep 104472443 = 156708665) B156708665
theorem B1884095 : Blo 1254445 1884095 := bstep (se 1 (by rfl) ⟨1413071, by rfl⟩ : syracuseStep 1884095 = 2826143) B2826143
theorem B1884263 : Blo 1254445 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B1884287 : Blo 1254445 1884287 := bstep (se 1 (by rfl) ⟨1413215, by rfl⟩ : syracuseStep 1884287 = 2826431) B2826431
theorem B3178703 : Blo 1254445 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B1884443 : Blo 1254445 1884443 := bstep (se 1 (by rfl) ⟨1413332, by rfl⟩ : syracuseStep 1884443 = 2826665) B2826665
theorem B1786153 : Blo 1254445 1786153 := bstep (se 2 (by rfl) ⟨669807, by rfl⟩ : syracuseStep 1786153 = 1339615) B1339615
theorem B2261351 : Blo 1254445 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B1884539 : Blo 1254445 1884539 := bstep (se 1 (by rfl) ⟨1413404, by rfl⟩ : syracuseStep 1884539 = 2826809) B2826809
theorem B13574891 : Blo 1254445 13574891 := bstep (se 1 (by rfl) ⟨10181168, by rfl⟩ : syracuseStep 13574891 = 20362337) B20362337
theorem B6357851 : Blo 1254445 6357851 := bstep (se 1 (by rfl) ⟨4768388, by rfl⟩ : syracuseStep 6357851 = 9536777) B9536777
theorem B4236191 : Blo 1254445 4236191 := bstep (se 1 (by rfl) ⟨3177143, by rfl⟩ : syracuseStep 4236191 = 6354287) B6354287
theorem B3179675 : Blo 1254445 3179675 := bstep (se 1 (by rfl) ⟨2384756, by rfl⟩ : syracuseStep 3179675 = 4769513) B4769513
theorem B1254631 : Blo 1254445 1254631 := bstep (se 1 (by rfl) ⟨940973, by rfl⟩ : syracuseStep 1254631 = 1881947) B1881947
theorem B1254683 : Blo 1254445 1254683 := bstep (se 1 (by rfl) ⟨941012, by rfl⟩ : syracuseStep 1254683 = 1882025) B1882025
theorem B1254879 : Blo 1254445 1254879 := bstep (se 1 (by rfl) ⟨941159, by rfl⟩ : syracuseStep 1254879 = 1882319) B1882319
theorem B1254911 : Blo 1254445 1254911 := bstep (se 1 (by rfl) ⟨941183, by rfl⟩ : syracuseStep 1254911 = 1882367) B1882367
theorem B1255151 : Blo 1254445 1255151 := bstep (se 1 (by rfl) ⟨941363, by rfl⟩ : syracuseStep 1255151 = 1882727) B1882727
theorem B5359517 : Blo 1254445 5359517 := bstep (se 3 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 5359517 = 2009819) B2009819
theorem B1255419 : Blo 1254445 1255419 := bstep (se 1 (by rfl) ⟨941564, by rfl⟩ : syracuseStep 1255419 = 1883129) B1883129
theorem B81405971 : Blo 1254445 81405971 := bstep (se 1 (by rfl) ⟨61054478, by rfl⟩ : syracuseStep 81405971 = 122108957) B122108957
theorem B1255495 : Blo 1254445 1255495 := bstep (se 1 (by rfl) ⟨941621, by rfl⟩ : syracuseStep 1255495 = 1883243) B1883243
theorem B7145567 : Blo 1254445 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B1255583 : Blo 1254445 1255583 := bstep (se 1 (by rfl) ⟨941687, by rfl⟩ : syracuseStep 1255583 = 1883375) B1883375
theorem B8046863 : Blo 1254445 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B1255835 : Blo 1254445 1255835 := bstep (se 1 (by rfl) ⟨941876, by rfl⟩ : syracuseStep 1255835 = 1883753) B1883753
theorem B6359633 : Blo 1254445 6359633 := bstep (se 2 (by rfl) ⟨2384862, by rfl⟩ : syracuseStep 6359633 = 4769725) B4769725
theorem B1256063 : Blo 1254445 1256063 := bstep (se 1 (by rfl) ⟨942047, by rfl⟩ : syracuseStep 1256063 = 1884095) B1884095
theorem B7146251 : Blo 1254445 7146251 := bstep (se 1 (by rfl) ⟨5359688, by rfl⟩ : syracuseStep 7146251 = 10719377) B10719377
theorem B1411951 : Blo 1254445 1411951 := bstep (se 1 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 1411951 = 2117927) B2117927
theorem B9055259 : Blo 1254445 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B9530459 : Blo 1254445 9530459 := bstep (se 1 (by rfl) ⟨7147844, by rfl⟩ : syracuseStep 9530459 = 14295689) B14295689
theorem B5090471 : Blo 1254445 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B3018151 : Blo 1254445 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B6352505 : Blo 1254445 6352505 := bstep (se 2 (by rfl) ⟨2382189, by rfl⟩ : syracuseStep 6352505 = 4764379) B4764379
theorem B7343759 : Blo 1254445 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B2010793 : Blo 1254445 2010793 := bstep (se 2 (by rfl) ⟨754047, by rfl⟩ : syracuseStep 2010793 = 1508095) B1508095
theorem B7148027 : Blo 1254445 7148027 := bstep (se 1 (by rfl) ⟨5361020, by rfl⟩ : syracuseStep 7148027 = 10722041) B10722041
theorem B2118143 : Blo 1254445 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B9540179 : Blo 1254445 9540179 := bstep (se 1 (by rfl) ⟨7155134, by rfl⟩ : syracuseStep 9540179 = 14310269) B14310269
theorem B46445561 : Blo 1254445 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B5510311 : Blo 1254445 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B2823785 : Blo 1254445 2823785 := bstep (se 2 (by rfl) ⟨1058919, by rfl⟩ : syracuseStep 2823785 = 2117839) B2117839
theorem B5092969 : Blo 1254445 5092969 := bstep (se 2 (by rfl) ⟨1909863, by rfl⟩ : syracuseStep 5092969 = 3819727) B3819727
theorem B7149167 : Blo 1254445 7149167 := bstep (se 1 (by rfl) ⟨5361875, by rfl⟩ : syracuseStep 7149167 = 10723751) B10723751
theorem B1881791 : Blo 1254445 1881791 := bstep (se 1 (by rfl) ⟨1411343, by rfl⟩ : syracuseStep 1881791 = 2822687) B2822687
theorem B2545771 : Blo 1254445 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B2824379 : Blo 1254445 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B7248323 : Blo 1254445 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B48921185 : Blo 1254445 48921185 := bstep (se 2 (by rfl) ⟨18345444, by rfl⟩ : syracuseStep 48921185 = 36690889) B36690889
theorem B1587919 : Blo 1254445 1587919 := bstep (se 1 (by rfl) ⟨1190939, by rfl⟩ : syracuseStep 1587919 = 2381879) B2381879
theorem B2825855 : Blo 1254445 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B278593181 : Blo 1254445 278593181 := bstep (se 3 (by rfl) ⟨52236221, by rfl⟩ : syracuseStep 278593181 = 104472443) B104472443
theorem B371703613 : Blo 1254445 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B3178399 : Blo 1254445 3178399 := bstep (se 1 (by rfl) ⟨2383799, by rfl⟩ : syracuseStep 3178399 = 4767599) B4767599
theorem B1507567 : Blo 1254445 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B1254527 : Blo 1254445 1254527 := bstep (se 1 (by rfl) ⟨940895, by rfl⟩ : syracuseStep 1254527 = 1881791) B1881791
theorem B3573011 : Blo 1254445 3573011 := bstep (se 1 (by rfl) ⟨2679758, by rfl⟩ : syracuseStep 3573011 = 5359517) B5359517
theorem B32614123 : Blo 1254445 32614123 := bstep (se 1 (by rfl) ⟨24460592, by rfl⟩ : syracuseStep 32614123 = 48921185) B48921185
theorem B4024201 : Blo 1254445 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B3393647 : Blo 1254445 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B2681057 : Blo 1254445 2681057 := bstep (se 2 (by rfl) ⟨1005396, by rfl⟩ : syracuseStep 2681057 = 2010793) B2010793
theorem B4237865 : Blo 1254445 4237865 := bstep (se 2 (by rfl) ⟨1589199, by rfl⟩ : syracuseStep 4237865 = 3178399) B3178399
theorem B1256175 : Blo 1254445 1256175 := bstep (se 1 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 1256175 = 1884263) B1884263
theorem B1256191 : Blo 1254445 1256191 := bstep (se 1 (by rfl) ⟨942143, by rfl⟩ : syracuseStep 1256191 = 1884287) B1884287
theorem B3394361 : Blo 1254445 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B1256295 : Blo 1254445 1256295 := bstep (se 1 (by rfl) ⟨942221, by rfl⟩ : syracuseStep 1256295 = 1884443) B1884443
theorem B1256359 : Blo 1254445 1256359 := bstep (se 1 (by rfl) ⟨942269, by rfl⟩ : syracuseStep 1256359 = 1884539) B1884539
theorem B1412095 : Blo 1254445 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B6360119 : Blo 1254445 6360119 := bstep (se 1 (by rfl) ⟨4770089, by rfl⟩ : syracuseStep 6360119 = 9540179) B9540179
theorem B4238567 : Blo 1254445 4238567 := bstep (se 1 (by rfl) ⟨3178925, by rfl⟩ : syracuseStep 4238567 = 6357851) B6357851
theorem B2117225 : Blo 1254445 2117225 := bstep (se 2 (by rfl) ⟨793959, by rfl⟩ : syracuseStep 2117225 = 1587919) B1587919
theorem B19328861 : Blo 1254445 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B4763711 : Blo 1254445 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B4239755 : Blo 1254445 4239755 := bstep (se 1 (by rfl) ⟨3179816, by rfl⟩ : syracuseStep 4239755 = 6359633) B6359633
theorem B4764167 : Blo 1254445 4764167 := bstep (se 1 (by rfl) ⟨3573125, by rfl⟩ : syracuseStep 4764167 = 7146251) B7146251
theorem B6353639 : Blo 1254445 6353639 := bstep (se 1 (by rfl) ⟨4765229, by rfl⟩ : syracuseStep 6353639 = 9530459) B9530459
theorem B495604817 : Blo 1254445 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B4895839 : Blo 1254445 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B2119135 : Blo 1254445 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B4765351 : Blo 1254445 4765351 := bstep (se 1 (by rfl) ⟨3574013, by rfl⟩ : syracuseStep 4765351 = 7148027) B7148027
theorem B2381537 : Blo 1254445 2381537 := bstep (se 2 (by rfl) ⟨893076, by rfl⟩ : syracuseStep 2381537 = 1786153) B1786153
theorem B9049927 : Blo 1254445 9049927 := bstep (se 1 (by rfl) ⟨6787445, by rfl⟩ : syracuseStep 9049927 = 13574891) B13574891
theorem B2824127 : Blo 1254445 2824127 := bstep (se 1 (by rfl) ⟨2118095, by rfl⟩ : syracuseStep 2824127 = 4236191) B4236191
theorem B30963707 : Blo 1254445 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B2119783 : Blo 1254445 2119783 := bstep (se 1 (by rfl) ⟨1589837, by rfl⟩ : syracuseStep 2119783 = 3179675) B3179675
theorem B117553301 : Blo 1254445 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B1882523 : Blo 1254445 1882523 := bstep (se 1 (by rfl) ⟨1411892, by rfl⟩ : syracuseStep 1882523 = 2823785) B2823785
theorem B4766111 : Blo 1254445 4766111 := bstep (se 1 (by rfl) ⟨3574583, by rfl⟩ : syracuseStep 4766111 = 7149167) B7149167
theorem B1882601 : Blo 1254445 1882601 := bstep (se 2 (by rfl) ⟨705975, by rfl⟩ : syracuseStep 1882601 = 1411951) B1411951
theorem B54270647 : Blo 1254445 54270647 := bstep (se 1 (by rfl) ⟨40702985, by rfl⟩ : syracuseStep 54270647 = 81405971) B81405971
theorem B1882919 : Blo 1254445 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B5364575 : Blo 1254445 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B6036839 : Blo 1254445 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B6790625 : Blo 1254445 6790625 := bstep (se 2 (by rfl) ⟨2546484, by rfl⟩ : syracuseStep 6790625 = 5092969) B5092969
theorem B4235003 : Blo 1254445 4235003 := bstep (se 1 (by rfl) ⟨3176252, by rfl⟩ : syracuseStep 4235003 = 6352505) B6352505
theorem B1883903 : Blo 1254445 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B185728787 : Blo 1254445 185728787 := bstep (se 1 (by rfl) ⟨139296590, by rfl⟩ : syracuseStep 185728787 = 278593181) B278593181
theorem B2826377 : Blo 1254445 2826377 := bstep (se 2 (by rfl) ⟨1059891, by rfl⟩ : syracuseStep 2826377 = 2119783) B2119783
theorem B2826503 : Blo 1254445 2826503 := bstep (se 1 (by rfl) ⟨2119877, by rfl⟩ : syracuseStep 2826503 = 4239755) B4239755
theorem B4235759 : Blo 1254445 4235759 := bstep (se 1 (by rfl) ⟨3176819, by rfl⟩ : syracuseStep 4235759 = 6353639) B6353639
theorem B9528029 : Blo 1254445 9528029 := bstep (se 3 (by rfl) ⟨1786505, by rfl⟩ : syracuseStep 9528029 = 3573011) B3573011
theorem B2262431 : Blo 1254445 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B1255015 : Blo 1254445 1255015 := bstep (se 1 (by rfl) ⟨941261, by rfl⟩ : syracuseStep 1255015 = 1882523) B1882523
theorem B1255067 : Blo 1254445 1255067 := bstep (se 1 (by rfl) ⟨941300, by rfl⟩ : syracuseStep 1255067 = 1882601) B1882601
theorem B1255279 : Blo 1254445 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B2262907 : Blo 1254445 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B4024559 : Blo 1254445 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B43485497 : Blo 1254445 43485497 := bstep (se 2 (by rfl) ⟨16307061, by rfl⟩ : syracuseStep 43485497 = 32614123) B32614123
theorem B1411483 : Blo 1254445 1411483 := bstep (se 1 (by rfl) ⟨1058612, by rfl⟩ : syracuseStep 1411483 = 2117225) B2117225
theorem B1255935 : Blo 1254445 1255935 := bstep (se 1 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 1255935 = 1883903) B1883903
theorem B2010089 : Blo 1254445 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B330403211 : Blo 1254445 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B78368867 : Blo 1254445 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B36180431 : Blo 1254445 36180431 := bstep (se 1 (by rfl) ⟨27135323, by rfl⟩ : syracuseStep 36180431 = 54270647) B54270647
theorem B3576383 : Blo 1254445 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B4240079 : Blo 1254445 4240079 := bstep (se 1 (by rfl) ⟨3180059, by rfl⟩ : syracuseStep 4240079 = 6360119) B6360119
theorem B6353801 : Blo 1254445 6353801 := bstep (se 2 (by rfl) ⟨2382675, by rfl⟩ : syracuseStep 6353801 = 4765351) B4765351
theorem B4527083 : Blo 1254445 4527083 := bstep (se 1 (by rfl) ⟨3395312, by rfl⟩ : syracuseStep 4527083 = 6790625) B6790625
theorem B2823335 : Blo 1254445 2823335 := bstep (se 1 (by rfl) ⟨2117501, by rfl⟩ : syracuseStep 2823335 = 4235003) B4235003
theorem B123819191 : Blo 1254445 123819191 := bstep (se 1 (by rfl) ⟨92864393, by rfl⟩ : syracuseStep 123819191 = 185728787) B185728787
theorem B3175807 : Blo 1254445 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B3176111 : Blo 1254445 3176111 := bstep (se 1 (by rfl) ⟨2382083, by rfl⟩ : syracuseStep 3176111 = 4764167) B4764167
theorem B7149485 : Blo 1254445 7149485 := bstep (se 3 (by rfl) ⟨1340528, by rfl⟩ : syracuseStep 7149485 = 2681057) B2681057
theorem B1587691 : Blo 1254445 1587691 := bstep (se 1 (by rfl) ⟨1190768, by rfl⟩ : syracuseStep 1587691 = 2381537) B2381537
theorem B1882751 : Blo 1254445 1882751 := bstep (se 1 (by rfl) ⟨1412063, by rfl⟩ : syracuseStep 1882751 = 2824127) B2824127
theorem B20642471 : Blo 1254445 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B1882793 : Blo 1254445 1882793 := bstep (se 2 (by rfl) ⟨706047, by rfl⟩ : syracuseStep 1882793 = 1412095) B1412095
theorem B6527785 : Blo 1254445 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B3177407 : Blo 1254445 3177407 := bstep (se 1 (by rfl) ⟨2383055, by rfl⟩ : syracuseStep 3177407 = 4766111) B4766111
theorem B2825243 : Blo 1254445 2825243 := bstep (se 1 (by rfl) ⟨2118932, by rfl⟩ : syracuseStep 2825243 = 4237865) B4237865
theorem B2825513 : Blo 1254445 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B2825711 : Blo 1254445 2825711 := bstep (se 1 (by rfl) ⟨2119283, by rfl⟩ : syracuseStep 2825711 = 4238567) B4238567
theorem B12066569 : Blo 1254445 12066569 := bstep (se 2 (by rfl) ⟨4524963, by rfl⟩ : syracuseStep 12066569 = 9049927) B9049927
theorem B5365601 : Blo 1254445 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B12885907 : Blo 1254445 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B1884251 : Blo 1254445 1884251 := bstep (se 1 (by rfl) ⟨1413188, by rfl⟩ : syracuseStep 1884251 = 2826377) B2826377
theorem B1884335 : Blo 1254445 1884335 := bstep (se 1 (by rfl) ⟨1413251, by rfl⟩ : syracuseStep 1884335 = 2826503) B2826503
theorem B2384255 : Blo 1254445 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B2826719 : Blo 1254445 2826719 := bstep (se 1 (by rfl) ⟨2120039, by rfl⟩ : syracuseStep 2826719 = 4240079) B4240079
theorem B4235867 : Blo 1254445 4235867 := bstep (se 1 (by rfl) ⟨3176900, by rfl⟩ : syracuseStep 4235867 = 6353801) B6353801
theorem B1255167 : Blo 1254445 1255167 := bstep (se 1 (by rfl) ⟨941375, by rfl⟩ : syracuseStep 1255167 = 1882751) B1882751
theorem B1255195 : Blo 1254445 1255195 := bstep (se 1 (by rfl) ⟨941396, by rfl⟩ : syracuseStep 1255195 = 1882793) B1882793
theorem B12068837 : Blo 1254445 12068837 := bstep (se 4 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 12068837 = 2262907) B2262907
theorem B220268807 : Blo 1254445 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B17181209 : Blo 1254445 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B24120287 : Blo 1254445 24120287 := bstep (se 1 (by rfl) ⟨18090215, by rfl⟩ : syracuseStep 24120287 = 36180431) B36180431
theorem B6352019 : Blo 1254445 6352019 := bstep (se 1 (by rfl) ⟨4764014, by rfl⟩ : syracuseStep 6352019 = 9528029) B9528029
theorem B2116921 : Blo 1254445 2116921 := bstep (se 2 (by rfl) ⟨793845, by rfl⟩ : syracuseStep 2116921 = 1587691) B1587691
theorem B3018055 : Blo 1254445 3018055 := bstep (se 1 (by rfl) ⟨2263541, by rfl⟩ : syracuseStep 3018055 = 4527083) B4527083
theorem B82546127 : Blo 1254445 82546127 := bstep (se 1 (by rfl) ⟨61909595, by rfl⟩ : syracuseStep 82546127 = 123819191) B123819191
theorem B8703713 : Blo 1254445 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B6033149 : Blo 1254445 6033149 := bstep (se 3 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 6033149 = 2262431) B2262431
theorem B2117407 : Blo 1254445 2117407 := bstep (se 1 (by rfl) ⟨1588055, by rfl⟩ : syracuseStep 2117407 = 3176111) B3176111
theorem B2683039 : Blo 1254445 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B2118271 : Blo 1254445 2118271 := bstep (se 1 (by rfl) ⟨1588703, by rfl⟩ : syracuseStep 2118271 = 3177407) B3177407
theorem B1340059 : Blo 1254445 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B3577067 : Blo 1254445 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B52245911 : Blo 1254445 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B2823839 : Blo 1254445 2823839 := bstep (se 1 (by rfl) ⟨2117879, by rfl⟩ : syracuseStep 2823839 = 4235759) B4235759
theorem B1881977 : Blo 1254445 1881977 := bstep (se 2 (by rfl) ⟨705741, by rfl⟩ : syracuseStep 1881977 = 1411483) B1411483
theorem B1882223 : Blo 1254445 1882223 := bstep (se 1 (by rfl) ⟨1411667, by rfl⟩ : syracuseStep 1882223 = 2823335) B2823335
theorem B4766323 : Blo 1254445 4766323 := bstep (se 1 (by rfl) ⟨3574742, by rfl⟩ : syracuseStep 4766323 = 7149485) B7149485
theorem B28990331 : Blo 1254445 28990331 := bstep (se 1 (by rfl) ⟨21742748, by rfl⟩ : syracuseStep 28990331 = 43485497) B43485497
theorem B13761647 : Blo 1254445 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B4234409 : Blo 1254445 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B1883495 : Blo 1254445 1883495 := bstep (se 1 (by rfl) ⟨1412621, by rfl⟩ : syracuseStep 1883495 = 2825243) B2825243
theorem B1883675 : Blo 1254445 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B1883807 : Blo 1254445 1883807 := bstep (se 1 (by rfl) ⟨1412855, by rfl⟩ : syracuseStep 1883807 = 2825711) B2825711
theorem B8044379 : Blo 1254445 8044379 := bstep (se 1 (by rfl) ⟨6033284, by rfl⟩ : syracuseStep 8044379 = 12066569) B12066569
theorem B1884479 : Blo 1254445 1884479 := bstep (se 1 (by rfl) ⟨1413359, by rfl⟩ : syracuseStep 1884479 = 2826719) B2826719
theorem B2384711 : Blo 1254445 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B1786745 : Blo 1254445 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B6358013 : Blo 1254445 6358013 := bstep (se 3 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 6358013 = 2384255) B2384255
theorem B1254651 : Blo 1254445 1254651 := bstep (se 1 (by rfl) ⟨940988, by rfl⟩ : syracuseStep 1254651 = 1881977) B1881977
theorem B8045891 : Blo 1254445 8045891 := bstep (se 1 (by rfl) ⟨6034418, by rfl⟩ : syracuseStep 8045891 = 12068837) B12068837
theorem B1254815 : Blo 1254445 1254815 := bstep (se 1 (by rfl) ⟨941111, by rfl⟩ : syracuseStep 1254815 = 1882223) B1882223
theorem B11454139 : Blo 1254445 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B4024073 : Blo 1254445 4024073 := bstep (se 2 (by rfl) ⟨1509027, by rfl⟩ : syracuseStep 4024073 = 3018055) B3018055
theorem B19326887 : Blo 1254445 19326887 := bstep (se 1 (by rfl) ⟨14495165, by rfl⟩ : syracuseStep 19326887 = 28990331) B28990331
theorem B23209901 : Blo 1254445 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B1255663 : Blo 1254445 1255663 := bstep (se 1 (by rfl) ⟨941747, by rfl⟩ : syracuseStep 1255663 = 1883495) B1883495
theorem B1255783 : Blo 1254445 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B1255871 : Blo 1254445 1255871 := bstep (se 1 (by rfl) ⟨941903, by rfl⟩ : syracuseStep 1255871 = 1883807) B1883807
theorem B1256167 : Blo 1254445 1256167 := bstep (se 1 (by rfl) ⟨942125, by rfl⟩ : syracuseStep 1256167 = 1884251) B1884251
theorem B1256223 : Blo 1254445 1256223 := bstep (se 1 (by rfl) ⟨942167, by rfl⟩ : syracuseStep 1256223 = 1884335) B1884335
theorem B146845871 : Blo 1254445 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B2822561 : Blo 1254445 2822561 := bstep (se 2 (by rfl) ⟨1058460, by rfl⟩ : syracuseStep 2822561 = 2116921) B2116921
theorem B2822939 : Blo 1254445 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B55030751 : Blo 1254445 55030751 := bstep (se 1 (by rfl) ⟨41273063, by rfl⟩ : syracuseStep 55030751 = 82546127) B82546127
theorem B2823209 : Blo 1254445 2823209 := bstep (se 2 (by rfl) ⟨1058703, by rfl⟩ : syracuseStep 2823209 = 2117407) B2117407
theorem B5362919 : Blo 1254445 5362919 := bstep (se 1 (by rfl) ⟨4022189, by rfl⟩ : syracuseStep 5362919 = 8044379) B8044379
theorem B3577385 : Blo 1254445 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B2823911 : Blo 1254445 2823911 := bstep (se 1 (by rfl) ⟨2117933, by rfl⟩ : syracuseStep 2823911 = 4235867) B4235867
theorem B6355097 : Blo 1254445 6355097 := bstep (se 2 (by rfl) ⟨2383161, by rfl⟩ : syracuseStep 6355097 = 4766323) B4766323
theorem B2824361 : Blo 1254445 2824361 := bstep (se 2 (by rfl) ⟨1059135, by rfl⟩ : syracuseStep 2824361 = 2118271) B2118271
theorem B34830607 : Blo 1254445 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B1882559 : Blo 1254445 1882559 := bstep (se 1 (by rfl) ⟨1411919, by rfl⟩ : syracuseStep 1882559 = 2823839) B2823839
theorem B16080191 : Blo 1254445 16080191 := bstep (se 1 (by rfl) ⟨12060143, by rfl⟩ : syracuseStep 16080191 = 24120287) B24120287
theorem B9174431 : Blo 1254445 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B4234679 : Blo 1254445 4234679 := bstep (se 1 (by rfl) ⟨3176009, by rfl⟩ : syracuseStep 4234679 = 6352019) B6352019
theorem B4022099 : Blo 1254445 4022099 := bstep (se 1 (by rfl) ⟨3016574, by rfl⟩ : syracuseStep 4022099 = 6033149) B6033149
theorem B46440809 : Blo 1254445 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B1589807 : Blo 1254445 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B4236731 : Blo 1254445 4236731 := bstep (se 1 (by rfl) ⟨3177548, by rfl⟩ : syracuseStep 4236731 = 6355097) B6355097
theorem B1255039 : Blo 1254445 1255039 := bstep (se 1 (by rfl) ⟨941279, by rfl⟩ : syracuseStep 1255039 = 1882559) B1882559
theorem B15272185 : Blo 1254445 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B2681399 : Blo 1254445 2681399 := bstep (se 1 (by rfl) ⟨2011049, by rfl⟩ : syracuseStep 2681399 = 4022099) B4022099
theorem B97897247 : Blo 1254445 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B1256319 : Blo 1254445 1256319 := bstep (se 1 (by rfl) ⟨942239, by rfl⟩ : syracuseStep 1256319 = 1884479) B1884479
theorem B36687167 : Blo 1254445 36687167 := bstep (se 1 (by rfl) ⟨27515375, by rfl⟩ : syracuseStep 36687167 = 55030751) B55030751
theorem B4238675 : Blo 1254445 4238675 := bstep (se 1 (by rfl) ⟨3179006, by rfl⟩ : syracuseStep 4238675 = 6358013) B6358013
theorem B3575279 : Blo 1254445 3575279 := bstep (se 1 (by rfl) ⟨2681459, by rfl⟩ : syracuseStep 3575279 = 5362919) B5362919
theorem B24465149 : Blo 1254445 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B2682715 : Blo 1254445 2682715 := bstep (se 1 (by rfl) ⟨2012036, by rfl⟩ : syracuseStep 2682715 = 4024073) B4024073
theorem B9539693 : Blo 1254445 9539693 := bstep (se 3 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 9539693 = 3577385) B3577385
theorem B10720127 : Blo 1254445 10720127 := bstep (se 1 (by rfl) ⟨8040095, by rfl⟩ : syracuseStep 10720127 = 16080191) B16080191
theorem B2823119 : Blo 1254445 2823119 := bstep (se 1 (by rfl) ⟨2117339, by rfl⟩ : syracuseStep 2823119 = 4234679) B4234679
theorem B4764653 : Blo 1254445 4764653 := bstep (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) B1786745
theorem B1881707 : Blo 1254445 1881707 := bstep (se 1 (by rfl) ⟨1411280, by rfl⟩ : syracuseStep 1881707 = 2822561) B2822561
theorem B1881959 : Blo 1254445 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B1882139 : Blo 1254445 1882139 := bstep (se 1 (by rfl) ⟨1411604, by rfl⟩ : syracuseStep 1882139 = 2823209) B2823209
theorem B5363927 : Blo 1254445 5363927 := bstep (se 1 (by rfl) ⟨4022945, by rfl⟩ : syracuseStep 5363927 = 8045891) B8045891
theorem B1882607 : Blo 1254445 1882607 := bstep (se 1 (by rfl) ⟨1411955, by rfl⟩ : syracuseStep 1882607 = 2823911) B2823911
theorem B12884591 : Blo 1254445 12884591 := bstep (se 1 (by rfl) ⟨9663443, by rfl⟩ : syracuseStep 12884591 = 19326887) B19326887
theorem B15473267 : Blo 1254445 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B1882907 : Blo 1254445 1882907 := bstep (se 1 (by rfl) ⟨1412180, by rfl⟩ : syracuseStep 1882907 = 2824361) B2824361
theorem B1254471 : Blo 1254445 1254471 := bstep (se 1 (by rfl) ⟨940853, by rfl⟩ : syracuseStep 1254471 = 1881707) B1881707
theorem B1254639 : Blo 1254445 1254639 := bstep (se 1 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 1254639 = 1881959) B1881959
theorem B1254759 : Blo 1254445 1254759 := bstep (se 1 (by rfl) ⟨941069, by rfl⟩ : syracuseStep 1254759 = 1882139) B1882139
theorem B1255071 : Blo 1254445 1255071 := bstep (se 1 (by rfl) ⟨941303, by rfl⟩ : syracuseStep 1255071 = 1882607) B1882607
theorem B1787599 : Blo 1254445 1787599 := bstep (se 1 (by rfl) ⟨1340699, by rfl⟩ : syracuseStep 1787599 = 2681399) B2681399
theorem B10315511 : Blo 1254445 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1255271 : Blo 1254445 1255271 := bstep (se 1 (by rfl) ⟨941453, by rfl⟩ : syracuseStep 1255271 = 1882907) B1882907
theorem B6359795 : Blo 1254445 6359795 := bstep (se 1 (by rfl) ⟨4769846, by rfl⟩ : syracuseStep 6359795 = 9539693) B9539693
theorem B30960539 : Blo 1254445 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B7146751 : Blo 1254445 7146751 := bstep (se 1 (by rfl) ⟨5360063, by rfl⟩ : syracuseStep 7146751 = 10720127) B10720127
theorem B4239485 : Blo 1254445 4239485 := bstep (se 3 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 4239485 = 1589807) B1589807
theorem B3575951 : Blo 1254445 3575951 := bstep (se 1 (by rfl) ⟨2681963, by rfl⟩ : syracuseStep 3575951 = 5363927) B5363927
theorem B8589727 : Blo 1254445 8589727 := bstep (se 1 (by rfl) ⟨6442295, by rfl⟩ : syracuseStep 8589727 = 12884591) B12884591
theorem B24458111 : Blo 1254445 24458111 := bstep (se 1 (by rfl) ⟨18343583, by rfl⟩ : syracuseStep 24458111 = 36687167) B36687167
theorem B3576953 : Blo 1254445 3576953 := bstep (se 2 (by rfl) ⟨1341357, by rfl⟩ : syracuseStep 3576953 = 2682715) B2682715
theorem B20362913 : Blo 1254445 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B1882079 : Blo 1254445 1882079 := bstep (se 1 (by rfl) ⟨1411559, by rfl⟩ : syracuseStep 1882079 = 2823119) B2823119
theorem B3176435 : Blo 1254445 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B2824487 : Blo 1254445 2824487 := bstep (se 1 (by rfl) ⟨2118365, by rfl⟩ : syracuseStep 2824487 = 4236731) B4236731
theorem B65264831 : Blo 1254445 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B2825783 : Blo 1254445 2825783 := bstep (se 1 (by rfl) ⟨2119337, by rfl⟩ : syracuseStep 2825783 = 4238675) B4238675
theorem B2383519 : Blo 1254445 2383519 := bstep (se 1 (by rfl) ⟨1787639, by rfl⟩ : syracuseStep 2383519 = 3575279) B3575279
theorem B16310099 : Blo 1254445 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B2826323 : Blo 1254445 2826323 := bstep (se 1 (by rfl) ⟨2119742, by rfl⟩ : syracuseStep 2826323 = 4239485) B4239485
theorem B2383967 : Blo 1254445 2383967 := bstep (se 1 (by rfl) ⟨1787975, by rfl⟩ : syracuseStep 2383967 = 3575951) B3575951
theorem B11452969 : Blo 1254445 11452969 := bstep (se 2 (by rfl) ⟨4294863, by rfl⟩ : syracuseStep 11452969 = 8589727) B8589727
theorem B2384635 : Blo 1254445 2384635 := bstep (se 1 (by rfl) ⟨1788476, by rfl⟩ : syracuseStep 2384635 = 3576953) B3576953
theorem B13575275 : Blo 1254445 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B1254719 : Blo 1254445 1254719 := bstep (se 1 (by rfl) ⟨941039, by rfl⟩ : syracuseStep 1254719 = 1882079) B1882079
theorem B9529001 : Blo 1254445 9529001 := bstep (se 2 (by rfl) ⟨3573375, by rfl⟩ : syracuseStep 9529001 = 7146751) B7146751
theorem B43509887 : Blo 1254445 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B10873399 : Blo 1254445 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B16305407 : Blo 1254445 16305407 := bstep (se 1 (by rfl) ⟨12229055, by rfl⟩ : syracuseStep 16305407 = 24458111) B24458111
theorem B6877007 : Blo 1254445 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2117623 : Blo 1254445 2117623 := bstep (se 1 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 2117623 = 3176435) B3176435
theorem B4239863 : Blo 1254445 4239863 := bstep (se 1 (by rfl) ⟨3179897, by rfl⟩ : syracuseStep 4239863 = 6359795) B6359795
theorem B20640359 : Blo 1254445 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B9533861 : Blo 1254445 9533861 := bstep (se 4 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 9533861 = 1787599) B1787599
theorem B1882991 : Blo 1254445 1882991 := bstep (se 1 (by rfl) ⟨1412243, by rfl⟩ : syracuseStep 1882991 = 2824487) B2824487
theorem B3178025 : Blo 1254445 3178025 := bstep (se 2 (by rfl) ⟨1191759, by rfl⟩ : syracuseStep 3178025 = 2383519) B2383519
theorem B1883855 : Blo 1254445 1883855 := bstep (se 1 (by rfl) ⟨1412891, by rfl⟩ : syracuseStep 1883855 = 2825783) B2825783
theorem B1884215 : Blo 1254445 1884215 := bstep (se 1 (by rfl) ⟨1413161, by rfl⟩ : syracuseStep 1884215 = 2826323) B2826323
theorem B1589311 : Blo 1254445 1589311 := bstep (se 1 (by rfl) ⟨1191983, by rfl⟩ : syracuseStep 1589311 = 2383967) B2383967
theorem B2826575 : Blo 1254445 2826575 := bstep (se 1 (by rfl) ⟨2119931, by rfl⟩ : syracuseStep 2826575 = 4239863) B4239863
theorem B15270625 : Blo 1254445 15270625 := bstep (se 2 (by rfl) ⟨5726484, by rfl⟩ : syracuseStep 15270625 = 11452969) B11452969
theorem B3179513 : Blo 1254445 3179513 := bstep (se 2 (by rfl) ⟨1192317, by rfl⟩ : syracuseStep 3179513 = 2384635) B2384635
theorem B1255327 : Blo 1254445 1255327 := bstep (se 1 (by rfl) ⟨941495, by rfl⟩ : syracuseStep 1255327 = 1882991) B1882991
theorem B1255903 : Blo 1254445 1255903 := bstep (se 1 (by rfl) ⟨941927, by rfl⟩ : syracuseStep 1255903 = 1883855) B1883855
theorem B6352667 : Blo 1254445 6352667 := bstep (se 1 (by rfl) ⟨4764500, by rfl⟩ : syracuseStep 6352667 = 9529001) B9529001
theorem B2118683 : Blo 1254445 2118683 := bstep (se 1 (by rfl) ⟨1589012, by rfl⟩ : syracuseStep 2118683 = 3178025) B3178025
theorem B4584671 : Blo 1254445 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B2823497 : Blo 1254445 2823497 := bstep (se 2 (by rfl) ⟨1058811, by rfl⟩ : syracuseStep 2823497 = 2117623) B2117623
theorem B13760239 : Blo 1254445 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B9050183 : Blo 1254445 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B14497865 : Blo 1254445 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B29006591 : Blo 1254445 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B6355907 : Blo 1254445 6355907 := bstep (se 1 (by rfl) ⟨4766930, by rfl⟩ : syracuseStep 6355907 = 9533861) B9533861
theorem B10870271 : Blo 1254445 10870271 := bstep (se 1 (by rfl) ⟨8152703, by rfl⟩ : syracuseStep 10870271 = 16305407) B16305407
theorem B1884383 : Blo 1254445 1884383 := bstep (se 1 (by rfl) ⟨1413287, by rfl⟩ : syracuseStep 1884383 = 2826575) B2826575
theorem B3056447 : Blo 1254445 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B4237271 : Blo 1254445 4237271 := bstep (se 1 (by rfl) ⟨3177953, by rfl⟩ : syracuseStep 4237271 = 6355907) B6355907
theorem B77350909 : Blo 1254445 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B1256143 : Blo 1254445 1256143 := bstep (se 1 (by rfl) ⟨942107, by rfl⟩ : syracuseStep 1256143 = 1884215) B1884215
theorem B1412455 : Blo 1254445 1412455 := bstep (se 1 (by rfl) ⟨1059341, by rfl⟩ : syracuseStep 1412455 = 2118683) B2118683
theorem B6033455 : Blo 1254445 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B18346985 : Blo 1254445 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B7246847 : Blo 1254445 7246847 := bstep (se 1 (by rfl) ⟨5435135, by rfl⟩ : syracuseStep 7246847 = 10870271) B10870271
theorem B2119081 : Blo 1254445 2119081 := bstep (se 2 (by rfl) ⟨794655, by rfl⟩ : syracuseStep 2119081 = 1589311) B1589311
theorem B2119675 : Blo 1254445 2119675 := bstep (se 1 (by rfl) ⟨1589756, by rfl⟩ : syracuseStep 2119675 = 3179513) B3179513
theorem B1882331 : Blo 1254445 1882331 := bstep (se 1 (by rfl) ⟨1411748, by rfl⟩ : syracuseStep 1882331 = 2823497) B2823497
theorem B81443333 : Blo 1254445 81443333 := bstep (se 4 (by rfl) ⟨7635312, by rfl⟩ : syracuseStep 81443333 = 15270625) B15270625
theorem B9665243 : Blo 1254445 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B4235111 : Blo 1254445 4235111 := bstep (se 1 (by rfl) ⟨3176333, by rfl⟩ : syracuseStep 4235111 = 6352667) B6352667
theorem B4022303 : Blo 1254445 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B12231323 : Blo 1254445 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B1254887 : Blo 1254445 1254887 := bstep (se 1 (by rfl) ⟨941165, by rfl⟩ : syracuseStep 1254887 = 1882331) B1882331
theorem B1256255 : Blo 1254445 1256255 := bstep (se 1 (by rfl) ⟨942191, by rfl⟩ : syracuseStep 1256255 = 1884383) B1884383
theorem B6443495 : Blo 1254445 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B2823407 : Blo 1254445 2823407 := bstep (se 1 (by rfl) ⟨2117555, by rfl⟩ : syracuseStep 2823407 = 4235111) B4235111
theorem B103134545 : Blo 1254445 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B2037631 : Blo 1254445 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2824847 : Blo 1254445 2824847 := bstep (se 1 (by rfl) ⟨2118635, by rfl⟩ : syracuseStep 2824847 = 4237271) B4237271
theorem B54295555 : Blo 1254445 54295555 := bstep (se 1 (by rfl) ⟨40721666, by rfl⟩ : syracuseStep 54295555 = 81443333) B81443333
theorem B1883273 : Blo 1254445 1883273 := bstep (se 2 (by rfl) ⟨706227, by rfl⟩ : syracuseStep 1883273 = 1412455) B1412455
theorem B2825441 : Blo 1254445 2825441 := bstep (se 2 (by rfl) ⟨1059540, by rfl⟩ : syracuseStep 2825441 = 2119081) B2119081
theorem B2826233 : Blo 1254445 2826233 := bstep (se 2 (by rfl) ⟨1059837, by rfl⟩ : syracuseStep 2826233 = 2119675) B2119675
theorem B19324925 : Blo 1254445 19324925 := bstep (se 3 (by rfl) ⟨3623423, by rfl⟩ : syracuseStep 19324925 = 7246847) B7246847
theorem B68756363 : Blo 1254445 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B72394073 : Blo 1254445 72394073 := bstep (se 2 (by rfl) ⟨27147777, by rfl⟩ : syracuseStep 72394073 = 54295555) B54295555
theorem B1255515 : Blo 1254445 1255515 := bstep (se 1 (by rfl) ⟨941636, by rfl⟩ : syracuseStep 1255515 = 1883273) B1883273
theorem B10726141 : Blo 1254445 10726141 := bstep (se 3 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 10726141 = 4022303) B4022303
theorem B4295663 : Blo 1254445 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B8154215 : Blo 1254445 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B2716841 : Blo 1254445 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B12883283 : Blo 1254445 12883283 := bstep (se 1 (by rfl) ⟨9662462, by rfl⟩ : syracuseStep 12883283 = 19324925) B19324925
theorem B1882271 : Blo 1254445 1882271 := bstep (se 1 (by rfl) ⟨1411703, by rfl⟩ : syracuseStep 1882271 = 2823407) B2823407
theorem B1883231 : Blo 1254445 1883231 := bstep (se 1 (by rfl) ⟨1412423, by rfl⟩ : syracuseStep 1883231 = 2824847) B2824847
theorem B1883627 : Blo 1254445 1883627 := bstep (se 1 (by rfl) ⟨1412720, by rfl⟩ : syracuseStep 1883627 = 2825441) B2825441
theorem B1884155 : Blo 1254445 1884155 := bstep (se 1 (by rfl) ⟨1413116, by rfl⟩ : syracuseStep 1884155 = 2826233) B2826233
theorem B1254847 : Blo 1254445 1254847 := bstep (se 1 (by rfl) ⟨941135, by rfl⟩ : syracuseStep 1254847 = 1882271) B1882271
theorem B1255487 : Blo 1254445 1255487 := bstep (se 1 (by rfl) ⟨941615, by rfl⟩ : syracuseStep 1255487 = 1883231) B1883231
theorem B1255751 : Blo 1254445 1255751 := bstep (se 1 (by rfl) ⟨941813, by rfl⟩ : syracuseStep 1255751 = 1883627) B1883627
theorem B1256103 : Blo 1254445 1256103 := bstep (se 1 (by rfl) ⟨942077, by rfl⟩ : syracuseStep 1256103 = 1884155) B1884155
theorem B7244909 : Blo 1254445 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B45837575 : Blo 1254445 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B8588855 : Blo 1254445 8588855 := bstep (se 1 (by rfl) ⟨6441641, by rfl⟩ : syracuseStep 8588855 = 12883283) B12883283
theorem B48262715 : Blo 1254445 48262715 := bstep (se 1 (by rfl) ⟨36197036, by rfl⟩ : syracuseStep 48262715 = 72394073) B72394073
theorem B2863775 : Blo 1254445 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B5436143 : Blo 1254445 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B14301521 : Blo 1254445 14301521 := bstep (se 2 (by rfl) ⟨5363070, by rfl⟩ : syracuseStep 14301521 = 10726141) B10726141
theorem B1909183 : Blo 1254445 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B30558383 : Blo 1254445 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B3624095 : Blo 1254445 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B4829939 : Blo 1254445 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B32175143 : Blo 1254445 32175143 := bstep (se 1 (by rfl) ⟨24131357, by rfl⟩ : syracuseStep 32175143 = 48262715) B48262715
theorem B9534347 : Blo 1254445 9534347 := bstep (se 1 (by rfl) ⟨7150760, by rfl⟩ : syracuseStep 9534347 = 14301521) B14301521
theorem B5725903 : Blo 1254445 5725903 := bstep (se 1 (by rfl) ⟨4294427, by rfl⟩ : syracuseStep 5725903 = 8588855) B8588855
theorem B3219959 : Blo 1254445 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B21450095 : Blo 1254445 21450095 := bstep (se 1 (by rfl) ⟨16087571, by rfl⟩ : syracuseStep 21450095 = 32175143) B32175143
theorem B2545577 : Blo 1254445 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B20372255 : Blo 1254445 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B6356231 : Blo 1254445 6356231 := bstep (se 1 (by rfl) ⟨4767173, by rfl⟩ : syracuseStep 6356231 = 9534347) B9534347
theorem B2416063 : Blo 1254445 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B7634537 : Blo 1254445 7634537 := bstep (se 2 (by rfl) ⟨2862951, by rfl⟩ : syracuseStep 7634537 = 5725903) B5725903
theorem B2146639 : Blo 1254445 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B1697051 : Blo 1254445 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B3221417 : Blo 1254445 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B4237487 : Blo 1254445 4237487 := bstep (se 1 (by rfl) ⟨3178115, by rfl⟩ : syracuseStep 4237487 = 6356231) B6356231
theorem B5089691 : Blo 1254445 5089691 := bstep (se 1 (by rfl) ⟨3817268, by rfl⟩ : syracuseStep 5089691 = 7634537) B7634537
theorem B14300063 : Blo 1254445 14300063 := bstep (se 1 (by rfl) ⟨10725047, by rfl⟩ : syracuseStep 14300063 = 21450095) B21450095
theorem B13581503 : Blo 1254445 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B3393127 : Blo 1254445 3393127 := bstep (se 1 (by rfl) ⟨2544845, by rfl⟩ : syracuseStep 3393127 = 5089691) B5089691
theorem B9054335 : Blo 1254445 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B2862185 : Blo 1254445 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B4525469 : Blo 1254445 4525469 := bstep (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) B1697051
theorem B8590445 : Blo 1254445 8590445 := bstep (se 3 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 8590445 = 3221417) B3221417
theorem B9533375 : Blo 1254445 9533375 := bstep (se 1 (by rfl) ⟨7150031, by rfl⟩ : syracuseStep 9533375 = 14300063) B14300063
theorem B2824991 : Blo 1254445 2824991 := bstep (se 1 (by rfl) ⟨2118743, by rfl⟩ : syracuseStep 2824991 = 4237487) B4237487
theorem B5726963 : Blo 1254445 5726963 := bstep (se 1 (by rfl) ⟨4295222, by rfl⟩ : syracuseStep 5726963 = 8590445) B8590445
theorem B4524169 : Blo 1254445 4524169 := bstep (se 2 (by rfl) ⟨1696563, by rfl⟩ : syracuseStep 4524169 = 3393127) B3393127
theorem B3016979 : Blo 1254445 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B30529973 : Blo 1254445 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B6355583 : Blo 1254445 6355583 := bstep (se 1 (by rfl) ⟨4766687, by rfl⟩ : syracuseStep 6355583 = 9533375) B9533375
theorem B6036223 : Blo 1254445 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B1883327 : Blo 1254445 1883327 := bstep (se 1 (by rfl) ⟨1412495, by rfl⟩ : syracuseStep 1883327 = 2824991) B2824991
theorem B3817975 : Blo 1254445 3817975 := bstep (se 1 (by rfl) ⟨2863481, by rfl⟩ : syracuseStep 3817975 = 5726963) B5726963
theorem B4237055 : Blo 1254445 4237055 := bstep (se 1 (by rfl) ⟨3177791, by rfl⟩ : syracuseStep 4237055 = 6355583) B6355583
theorem B1255551 : Blo 1254445 1255551 := bstep (se 1 (by rfl) ⟨941663, by rfl⟩ : syracuseStep 1255551 = 1883327) B1883327
theorem B6032225 : Blo 1254445 6032225 := bstep (se 2 (by rfl) ⟨2262084, by rfl⟩ : syracuseStep 6032225 = 4524169) B4524169
theorem B8048297 : Blo 1254445 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B2011319 : Blo 1254445 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B20353315 : Blo 1254445 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B5090633 : Blo 1254445 5090633 := bstep (se 2 (by rfl) ⟨1908987, by rfl⟩ : syracuseStep 5090633 = 3817975) B3817975
theorem B1340879 : Blo 1254445 1340879 := bstep (se 1 (by rfl) ⟨1005659, by rfl⟩ : syracuseStep 1340879 = 2011319) B2011319
theorem B27137753 : Blo 1254445 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B2824703 : Blo 1254445 2824703 := bstep (se 1 (by rfl) ⟨2118527, by rfl⟩ : syracuseStep 2824703 = 4237055) B4237055
theorem B4021483 : Blo 1254445 4021483 := bstep (se 1 (by rfl) ⟨3016112, by rfl⟩ : syracuseStep 4021483 = 6032225) B6032225
theorem B5365531 : Blo 1254445 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B3393755 : Blo 1254445 3393755 := bstep (se 1 (by rfl) ⟨2545316, by rfl⟩ : syracuseStep 3393755 = 5090633) B5090633
theorem B7154041 : Blo 1254445 7154041 := bstep (se 2 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 7154041 = 5365531) B5365531
theorem B18091835 : Blo 1254445 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B3575677 : Blo 1254445 3575677 := bstep (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) B1340879
theorem B5361977 : Blo 1254445 5361977 := bstep (se 2 (by rfl) ⟨2010741, by rfl⟩ : syracuseStep 5361977 = 4021483) B4021483
theorem B1883135 : Blo 1254445 1883135 := bstep (se 1 (by rfl) ⟨1412351, by rfl⟩ : syracuseStep 1883135 = 2824703) B2824703
theorem B2262503 : Blo 1254445 2262503 := bstep (se 1 (by rfl) ⟨1696877, by rfl⟩ : syracuseStep 2262503 = 3393755) B3393755
theorem B1255423 : Blo 1254445 1255423 := bstep (se 1 (by rfl) ⟨941567, by rfl⟩ : syracuseStep 1255423 = 1883135) B1883135
theorem B12061223 : Blo 1254445 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B9538721 : Blo 1254445 9538721 := bstep (se 2 (by rfl) ⟨3577020, by rfl⟩ : syracuseStep 9538721 = 7154041) B7154041
theorem B14298605 : Blo 1254445 14298605 := bstep (se 3 (by rfl) ⟨2680988, by rfl⟩ : syracuseStep 14298605 = 5361977) B5361977
theorem B4767569 : Blo 1254445 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B6359147 : Blo 1254445 6359147 := bstep (se 1 (by rfl) ⟨4769360, by rfl⟩ : syracuseStep 6359147 = 9538721) B9538721
theorem B6033341 : Blo 1254445 6033341 := bstep (se 3 (by rfl) ⟨1131251, by rfl⟩ : syracuseStep 6033341 = 2262503) B2262503
theorem B8040815 : Blo 1254445 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B9532403 : Blo 1254445 9532403 := bstep (se 1 (by rfl) ⟨7149302, by rfl⟩ : syracuseStep 9532403 = 14298605) B14298605
theorem B3178379 : Blo 1254445 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B5360543 : Blo 1254445 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B4239431 : Blo 1254445 4239431 := bstep (se 1 (by rfl) ⟨3179573, by rfl⟩ : syracuseStep 4239431 = 6359147) B6359147
theorem B2118919 : Blo 1254445 2118919 := bstep (se 1 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 2118919 = 3178379) B3178379
theorem B6354935 : Blo 1254445 6354935 := bstep (se 1 (by rfl) ⟨4766201, by rfl⟩ : syracuseStep 6354935 = 9532403) B9532403
theorem B4022227 : Blo 1254445 4022227 := bstep (se 1 (by rfl) ⟨3016670, by rfl⟩ : syracuseStep 4022227 = 6033341) B6033341
theorem B2826287 : Blo 1254445 2826287 := bstep (se 1 (by rfl) ⟨2119715, by rfl⟩ : syracuseStep 2826287 = 4239431) B4239431
theorem B4236623 : Blo 1254445 4236623 := bstep (se 1 (by rfl) ⟨3177467, by rfl⟩ : syracuseStep 4236623 = 6354935) B6354935
theorem B3573695 : Blo 1254445 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B5362969 : Blo 1254445 5362969 := bstep (se 2 (by rfl) ⟨2011113, by rfl⟩ : syracuseStep 5362969 = 4022227) B4022227
theorem B2825225 : Blo 1254445 2825225 := bstep (se 2 (by rfl) ⟨1059459, by rfl⟩ : syracuseStep 2825225 = 2118919) B2118919
theorem B1884191 : Blo 1254445 1884191 := bstep (se 1 (by rfl) ⟨1413143, by rfl⟩ : syracuseStep 1884191 = 2826287) B2826287
theorem B2824415 : Blo 1254445 2824415 := bstep (se 1 (by rfl) ⟨2118311, by rfl⟩ : syracuseStep 2824415 = 4236623) B4236623
theorem B2382463 : Blo 1254445 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B7150625 : Blo 1254445 7150625 := bstep (se 2 (by rfl) ⟨2681484, by rfl⟩ : syracuseStep 7150625 = 5362969) B5362969
theorem B1883483 : Blo 1254445 1883483 := bstep (se 1 (by rfl) ⟨1412612, by rfl⟩ : syracuseStep 1883483 = 2825225) B2825225
theorem B1255655 : Blo 1254445 1255655 := bstep (se 1 (by rfl) ⟨941741, by rfl⟩ : syracuseStep 1255655 = 1883483) B1883483
theorem B1256127 : Blo 1254445 1256127 := bstep (se 1 (by rfl) ⟨942095, by rfl⟩ : syracuseStep 1256127 = 1884191) B1884191
theorem B3176617 : Blo 1254445 3176617 := bstep (se 2 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 3176617 = 2382463) B2382463
theorem B1882943 : Blo 1254445 1882943 := bstep (se 1 (by rfl) ⟨1412207, by rfl⟩ : syracuseStep 1882943 = 2824415) B2824415
theorem B4767083 : Blo 1254445 4767083 := bstep (se 1 (by rfl) ⟨3575312, by rfl⟩ : syracuseStep 4767083 = 7150625) B7150625
theorem B4235489 : Blo 1254445 4235489 := bstep (se 2 (by rfl) ⟨1588308, by rfl⟩ : syracuseStep 4235489 = 3176617) B3176617
theorem B1255295 : Blo 1254445 1255295 := bstep (se 1 (by rfl) ⟨941471, by rfl⟩ : syracuseStep 1255295 = 1882943) B1882943
theorem B3178055 : Blo 1254445 3178055 := bstep (se 1 (by rfl) ⟨2383541, by rfl⟩ : syracuseStep 3178055 = 4767083) B4767083
theorem B2118703 : Blo 1254445 2118703 := bstep (se 1 (by rfl) ⟨1589027, by rfl⟩ : syracuseStep 2118703 = 3178055) B3178055
theorem B2823659 : Blo 1254445 2823659 := bstep (se 1 (by rfl) ⟨2117744, by rfl⟩ : syracuseStep 2823659 = 4235489) B4235489
theorem B1882439 : Blo 1254445 1882439 := bstep (se 1 (by rfl) ⟨1411829, by rfl⟩ : syracuseStep 1882439 = 2823659) B2823659
theorem B2824937 : Blo 1254445 2824937 := bstep (se 2 (by rfl) ⟨1059351, by rfl⟩ : syracuseStep 2824937 = 2118703) B2118703
theorem B1254959 : Blo 1254445 1254959 := bstep (se 1 (by rfl) ⟨941219, by rfl⟩ : syracuseStep 1254959 = 1882439) B1882439
theorem B1883291 : Blo 1254445 1883291 := bstep (se 1 (by rfl) ⟨1412468, by rfl⟩ : syracuseStep 1883291 = 2824937) B2824937
theorem B1255527 : Blo 1254445 1255527 := bstep (se 1 (by rfl) ⟨941645, by rfl⟩ : syracuseStep 1255527 = 1883291) B1883291

theorem C0 (j : ℕ) (h1 : 313611 ≤ j) (h2 : j ≤ 314110) : Blo 1254445 (4 * j + 3) := by
  interval_cases j
  · exact B1254447
  · exact B1254451
  · exact B1254455
  · exact B1254459
  · exact B1254463
  · exact B1254467
  · exact B1254471
  · exact B1254475
  · exact B1254479
  · exact B1254483
  · exact B1254487
  · exact B1254491
  · exact B1254495
  · exact B1254499
  · exact B1254503
  · exact B1254507
  · exact B1254511
  · exact B1254515
  · exact B1254519
  · exact B1254523
  · exact B1254527
  · exact B1254531
  · exact B1254535
  · exact B1254539
  · exact B1254543
  · exact B1254547
  · exact B1254551
  · exact B1254555
  · exact B1254559
  · exact B1254563
  · exact B1254567
  · exact B1254571
  · exact B1254575
  · exact B1254579
  · exact B1254583
  · exact B1254587
  · exact B1254591
  · exact B1254595
  · exact B1254599
  · exact B1254603
  · exact B1254607
  · exact B1254611
  · exact B1254615
  · exact B1254619
  · exact B1254623
  · exact B1254627
  · exact B1254631
  · exact B1254635
  · exact B1254639
  · exact B1254643
  · exact B1254647
  · exact B1254651
  · exact B1254655
  · exact B1254659
  · exact B1254663
  · exact B1254667
  · exact B1254671
  · exact B1254675
  · exact B1254679
  · exact B1254683
  · exact B1254687
  · exact B1254691
  · exact B1254695
  · exact B1254699
  · exact B1254703
  · exact B1254707
  · exact B1254711
  · exact B1254715
  · exact B1254719
  · exact B1254723
  · exact B1254727
  · exact B1254731
  · exact B1254735
  · exact B1254739
  · exact B1254743
  · exact B1254747
  · exact B1254751
  · exact B1254755
  · exact B1254759
  · exact B1254763
  · exact B1254767
  · exact B1254771
  · exact B1254775
  · exact B1254779
  · exact B1254783
  · exact B1254787
  · exact B1254791
  · exact B1254795
  · exact B1254799
  · exact B1254803
  · exact B1254807
  · exact B1254811
  · exact B1254815
  · exact B1254819
  · exact B1254823
  · exact B1254827
  · exact B1254831
  · exact B1254835
  · exact B1254839
  · exact B1254843
  · exact B1254847
  · exact B1254851
  · exact B1254855
  · exact B1254859
  · exact B1254863
  · exact B1254867
  · exact B1254871
  · exact B1254875
  · exact B1254879
  · exact B1254883
  · exact B1254887
  · exact B1254891
  · exact B1254895
  · exact B1254899
  · exact B1254903
  · exact B1254907
  · exact B1254911
  · exact B1254915
  · exact B1254919
  · exact B1254923
  · exact B1254927
  · exact B1254931
  · exact B1254935
  · exact B1254939
  · exact B1254943
  · exact B1254947
  · exact B1254951
  · exact B1254955
  · exact B1254959
  · exact B1254963
  · exact B1254967
  · exact B1254971
  · exact B1254975
  · exact B1254979
  · exact B1254983
  · exact B1254987
  · exact B1254991
  · exact B1254995
  · exact B1254999
  · exact B1255003
  · exact B1255007
  · exact B1255011
  · exact B1255015
  · exact B1255019
  · exact B1255023
  · exact B1255027
  · exact B1255031
  · exact B1255035
  · exact B1255039
  · exact B1255043
  · exact B1255047
  · exact B1255051
  · exact B1255055
  · exact B1255059
  · exact B1255063
  · exact B1255067
  · exact B1255071
  · exact B1255075
  · exact B1255079
  · exact B1255083
  · exact B1255087
  · exact B1255091
  · exact B1255095
  · exact B1255099
  · exact B1255103
  · exact B1255107
  · exact B1255111
  · exact B1255115
  · exact B1255119
  · exact B1255123
  · exact B1255127
  · exact B1255131
  · exact B1255135
  · exact B1255139
  · exact B1255143
  · exact B1255147
  · exact B1255151
  · exact B1255155
  · exact B1255159
  · exact B1255163
  · exact B1255167
  · exact B1255171
  · exact B1255175
  · exact B1255179
  · exact B1255183
  · exact B1255187
  · exact B1255191
  · exact B1255195
  · exact B1255199
  · exact B1255203
  · exact B1255207
  · exact B1255211
  · exact B1255215
  · exact B1255219
  · exact B1255223
  · exact B1255227
  · exact B1255231
  · exact B1255235
  · exact B1255239
  · exact B1255243
  · exact B1255247
  · exact B1255251
  · exact B1255255
  · exact B1255259
  · exact B1255263
  · exact B1255267
  · exact B1255271
  · exact B1255275
  · exact B1255279
  · exact B1255283
  · exact B1255287
  · exact B1255291
  · exact B1255295
  · exact B1255299
  · exact B1255303
  · exact B1255307
  · exact B1255311
  · exact B1255315
  · exact B1255319
  · exact B1255323
  · exact B1255327
  · exact B1255331
  · exact B1255335
  · exact B1255339
  · exact B1255343
  · exact B1255347
  · exact B1255351
  · exact B1255355
  · exact B1255359
  · exact B1255363
  · exact B1255367
  · exact B1255371
  · exact B1255375
  · exact B1255379
  · exact B1255383
  · exact B1255387
  · exact B1255391
  · exact B1255395
  · exact B1255399
  · exact B1255403
  · exact B1255407
  · exact B1255411
  · exact B1255415
  · exact B1255419
  · exact B1255423
  · exact B1255427
  · exact B1255431
  · exact B1255435
  · exact B1255439
  · exact B1255443
  · exact B1255447
  · exact B1255451
  · exact B1255455
  · exact B1255459
  · exact B1255463
  · exact B1255467
  · exact B1255471
  · exact B1255475
  · exact B1255479
  · exact B1255483
  · exact B1255487
  · exact B1255491
  · exact B1255495
  · exact B1255499
  · exact B1255503
  · exact B1255507
  · exact B1255511
  · exact B1255515
  · exact B1255519
  · exact B1255523
  · exact B1255527
  · exact B1255531
  · exact B1255535
  · exact B1255539
  · exact B1255543
  · exact B1255547
  · exact B1255551
  · exact B1255555
  · exact B1255559
  · exact B1255563
  · exact B1255567
  · exact B1255571
  · exact B1255575
  · exact B1255579
  · exact B1255583
  · exact B1255587
  · exact B1255591
  · exact B1255595
  · exact B1255599
  · exact B1255603
  · exact B1255607
  · exact B1255611
  · exact B1255615
  · exact B1255619
  · exact B1255623
  · exact B1255627
  · exact B1255631
  · exact B1255635
  · exact B1255639
  · exact B1255643
  · exact B1255647
  · exact B1255651
  · exact B1255655
  · exact B1255659
  · exact B1255663
  · exact B1255667
  · exact B1255671
  · exact B1255675
  · exact B1255679
  · exact B1255683
  · exact B1255687
  · exact B1255691
  · exact B1255695
  · exact B1255699
  · exact B1255703
  · exact B1255707
  · exact B1255711
  · exact B1255715
  · exact B1255719
  · exact B1255723
  · exact B1255727
  · exact B1255731
  · exact B1255735
  · exact B1255739
  · exact B1255743
  · exact B1255747
  · exact B1255751
  · exact B1255755
  · exact B1255759
  · exact B1255763
  · exact B1255767
  · exact B1255771
  · exact B1255775
  · exact B1255779
  · exact B1255783
  · exact B1255787
  · exact B1255791
  · exact B1255795
  · exact B1255799
  · exact B1255803
  · exact B1255807
  · exact B1255811
  · exact B1255815
  · exact B1255819
  · exact B1255823
  · exact B1255827
  · exact B1255831
  · exact B1255835
  · exact B1255839
  · exact B1255843
  · exact B1255847
  · exact B1255851
  · exact B1255855
  · exact B1255859
  · exact B1255863
  · exact B1255867
  · exact B1255871
  · exact B1255875
  · exact B1255879
  · exact B1255883
  · exact B1255887
  · exact B1255891
  · exact B1255895
  · exact B1255899
  · exact B1255903
  · exact B1255907
  · exact B1255911
  · exact B1255915
  · exact B1255919
  · exact B1255923
  · exact B1255927
  · exact B1255931
  · exact B1255935
  · exact B1255939
  · exact B1255943
  · exact B1255947
  · exact B1255951
  · exact B1255955
  · exact B1255959
  · exact B1255963
  · exact B1255967
  · exact B1255971
  · exact B1255975
  · exact B1255979
  · exact B1255983
  · exact B1255987
  · exact B1255991
  · exact B1255995
  · exact B1255999
  · exact B1256003
  · exact B1256007
  · exact B1256011
  · exact B1256015
  · exact B1256019
  · exact B1256023
  · exact B1256027
  · exact B1256031
  · exact B1256035
  · exact B1256039
  · exact B1256043
  · exact B1256047
  · exact B1256051
  · exact B1256055
  · exact B1256059
  · exact B1256063
  · exact B1256067
  · exact B1256071
  · exact B1256075
  · exact B1256079
  · exact B1256083
  · exact B1256087
  · exact B1256091
  · exact B1256095
  · exact B1256099
  · exact B1256103
  · exact B1256107
  · exact B1256111
  · exact B1256115
  · exact B1256119
  · exact B1256123
  · exact B1256127
  · exact B1256131
  · exact B1256135
  · exact B1256139
  · exact B1256143
  · exact B1256147
  · exact B1256151
  · exact B1256155
  · exact B1256159
  · exact B1256163
  · exact B1256167
  · exact B1256171
  · exact B1256175
  · exact B1256179
  · exact B1256183
  · exact B1256187
  · exact B1256191
  · exact B1256195
  · exact B1256199
  · exact B1256203
  · exact B1256207
  · exact B1256211
  · exact B1256215
  · exact B1256219
  · exact B1256223
  · exact B1256227
  · exact B1256231
  · exact B1256235
  · exact B1256239
  · exact B1256243
  · exact B1256247
  · exact B1256251
  · exact B1256255
  · exact B1256259
  · exact B1256263
  · exact B1256267
  · exact B1256271
  · exact B1256275
  · exact B1256279
  · exact B1256283
  · exact B1256287
  · exact B1256291
  · exact B1256295
  · exact B1256299
  · exact B1256303
  · exact B1256307
  · exact B1256311
  · exact B1256315
  · exact B1256319
  · exact B1256323
  · exact B1256327
  · exact B1256331
  · exact B1256335
  · exact B1256339
  · exact B1256343
  · exact B1256347
  · exact B1256351
  · exact B1256355
  · exact B1256359
  · exact B1256363
  · exact B1256367
  · exact B1256371
  · exact B1256375
  · exact B1256379
  · exact B1256383
  · exact B1256387
  · exact B1256391
  · exact B1256395
  · exact B1256399
  · exact B1256403
  · exact B1256407
  · exact B1256411
  · exact B1256415
  · exact B1256419
  · exact B1256423
  · exact B1256427
  · exact B1256431
  · exact B1256435
  · exact B1256439
  · exact B1256443

theorem solution (m : ℕ) (hlo : 1254445 ≤ m) (hhi : m ≤ 1256445) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 313611 ≤ j := by omega
    have hj2 : j ≤ 314110 := by omega
    have hb : Blo 1254445 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
