-- Prove2me | solution 1 for syracuse_descends_range_1849626_1851626
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:06:41.719567+00:00
-- url     : https://prove2.me/submissions/2ea35c29-1571-4dd8-957c-ab7c7110cba9

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


theorem B2777093 : Blo 1849626 2777093 := bbase (se 4 (by rfl) ⟨260352, by rfl⟩ : syracuseStep 2777093 = 520705) (by norm_num)
theorem B3751957 : Blo 1849626 3751957 := bbase (se 6 (by rfl) ⟨87936, by rfl⟩ : syracuseStep 3751957 = 175873) (by norm_num)
theorem B2777117 : Blo 1849626 2777117 := bbase (se 3 (by rfl) ⟨520709, by rfl⟩ : syracuseStep 2777117 = 1041419) (by norm_num)
theorem B2342945 : Blo 1849626 2342945 := bbase (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) (by norm_num)
theorem B2777141 : Blo 1849626 2777141 := bbase (se 5 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 2777141 = 260357) (by norm_num)
theorem B2777165 : Blo 1849626 2777165 := bbase (se 3 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 2777165 = 1041437) (by norm_num)
theorem B2080849 : Blo 1849626 2080849 := bbase (se 2 (by rfl) ⟨780318, by rfl⟩ : syracuseStep 2080849 = 1560637) (by norm_num)
theorem B2343001 : Blo 1849626 2343001 := bbase (se 2 (by rfl) ⟨878625, by rfl⟩ : syracuseStep 2343001 = 1757251) (by norm_num)
theorem B2777189 : Blo 1849626 2777189 := bbase (se 4 (by rfl) ⟨260361, by rfl⟩ : syracuseStep 2777189 = 520723) (by norm_num)
theorem B2080885 : Blo 1849626 2080885 := bbase (se 5 (by rfl) ⟨97541, by rfl⟩ : syracuseStep 2080885 = 195083) (by norm_num)
theorem B2777213 : Blo 1849626 2777213 := bbase (se 3 (by rfl) ⟨520727, by rfl⟩ : syracuseStep 2777213 = 1041455) (by norm_num)
theorem B3121301 : Blo 1849626 3121301 := bbase (se 6 (by rfl) ⟨73155, by rfl⟩ : syracuseStep 3121301 = 146311) (by norm_num)
theorem B2777237 : Blo 1849626 2777237 := bbase (se 6 (by rfl) ⟨65091, by rfl⟩ : syracuseStep 2777237 = 130183) (by norm_num)
theorem B2080921 : Blo 1849626 2080921 := bbase (se 2 (by rfl) ⟨780345, by rfl⟩ : syracuseStep 2080921 = 1560691) (by norm_num)
theorem B2777261 : Blo 1849626 2777261 := bbase (se 3 (by rfl) ⟨520736, by rfl⟩ : syracuseStep 2777261 = 1041473) (by norm_num)
theorem B2343097 : Blo 1849626 2343097 := bbase (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) (by norm_num)
theorem B4161725 : Blo 1849626 4161725 := bbase (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) (by norm_num)
theorem B2080957 : Blo 1849626 2080957 := bbase (se 3 (by rfl) ⟨390179, by rfl⟩ : syracuseStep 2080957 = 780359) (by norm_num)
theorem B1876165 : Blo 1849626 1876165 := bbase (se 4 (by rfl) ⟨175890, by rfl⟩ : syracuseStep 1876165 = 351781) (by norm_num)
theorem B2777285 : Blo 1849626 2777285 := bbase (se 4 (by rfl) ⟨260370, by rfl⟩ : syracuseStep 2777285 = 520741) (by norm_num)
theorem B9371861 : Blo 1849626 9371861 := bbase (se 7 (by rfl) ⟨109826, by rfl⟩ : syracuseStep 9371861 = 219653) (by norm_num)
theorem B2777309 : Blo 1849626 2777309 := bbase (se 3 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 2777309 = 1041491) (by norm_num)
theorem B2080993 : Blo 1849626 2080993 := bbase (se 2 (by rfl) ⟨780372, by rfl⟩ : syracuseStep 2080993 = 1560745) (by norm_num)
theorem B2777333 : Blo 1849626 2777333 := bbase (se 5 (by rfl) ⟨130187, by rfl⟩ : syracuseStep 2777333 = 260375) (by norm_num)
theorem B4161797 : Blo 1849626 4161797 := bbase (se 4 (by rfl) ⟨390168, by rfl⟩ : syracuseStep 4161797 = 780337) (by norm_num)
theorem B2081029 : Blo 1849626 2081029 := bbase (se 4 (by rfl) ⟨195096, by rfl⟩ : syracuseStep 2081029 = 390193) (by norm_num)
theorem B2777357 : Blo 1849626 2777357 := bbase (se 3 (by rfl) ⟨520754, by rfl⟩ : syracuseStep 2777357 = 1041509) (by norm_num)
theorem B3121429 : Blo 1849626 3121429 := bbase (se 6 (by rfl) ⟨73158, by rfl⟩ : syracuseStep 3121429 = 146317) (by norm_num)
theorem B4448533 : Blo 1849626 4448533 := bbase (se 6 (by rfl) ⟨104262, by rfl⟩ : syracuseStep 4448533 = 208525) (by norm_num)
theorem B2138393 : Blo 1849626 2138393 := bbase (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) (by norm_num)
theorem B3514661 : Blo 1849626 3514661 := bbase (se 4 (by rfl) ⟨329499, by rfl⟩ : syracuseStep 3514661 = 658999) (by norm_num)
theorem B2777381 : Blo 1849626 2777381 := bbase (se 4 (by rfl) ⟨260379, by rfl⟩ : syracuseStep 2777381 = 520759) (by norm_num)
theorem B2081065 : Blo 1849626 2081065 := bbase (se 2 (by rfl) ⟨780399, by rfl⟩ : syracuseStep 2081065 = 1560799) (by norm_num)
theorem B4686133 : Blo 1849626 4686133 := bbase (se 5 (by rfl) ⟨219662, by rfl⟩ : syracuseStep 4686133 = 439325) (by norm_num)
theorem B2777405 : Blo 1849626 2777405 := bbase (se 3 (by rfl) ⟨520763, by rfl⟩ : syracuseStep 2777405 = 1041527) (by norm_num)
theorem B4161869 : Blo 1849626 4161869 := bbase (se 3 (by rfl) ⟨780350, by rfl⟩ : syracuseStep 4161869 = 1560701) (by norm_num)
theorem B2081101 : Blo 1849626 2081101 := bbase (se 3 (by rfl) ⟨390206, by rfl⟩ : syracuseStep 2081101 = 780413) (by norm_num)
theorem B8896853 : Blo 1849626 8896853 := bbase (se 10 (by rfl) ⟨13032, by rfl⟩ : syracuseStep 8896853 = 26065) (by norm_num)
theorem B2777429 : Blo 1849626 2777429 := bbase (se 10 (by rfl) ⟨4068, by rfl⟩ : syracuseStep 2777429 = 8137) (by norm_num)
theorem B2343269 : Blo 1849626 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B3121517 : Blo 1849626 3121517 := bbase (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) (by norm_num)
theorem B2081137 : Blo 1849626 2081137 := bbase (se 2 (by rfl) ⟨780426, by rfl⟩ : syracuseStep 2081137 = 1560853) (by norm_num)
theorem B5267845 : Blo 1849626 5267845 := bbase (se 4 (by rfl) ⟨493860, by rfl⟩ : syracuseStep 5267845 = 987721) (by norm_num)
theorem B7029125 : Blo 1849626 7029125 := bbase (se 4 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 7029125 = 1317961) (by norm_num)
theorem B4161941 : Blo 1849626 4161941 := bbase (se 6 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 4161941 = 195091) (by norm_num)
theorem B2081173 : Blo 1849626 2081173 := bbase (se 6 (by rfl) ⟨48777, by rfl⟩ : syracuseStep 2081173 = 97555) (by norm_num)
theorem B2343325 : Blo 1849626 2343325 := bbase (se 3 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 2343325 = 878747) (by norm_num)
theorem B4686245 : Blo 1849626 4686245 := bbase (se 4 (by rfl) ⟨439335, by rfl⟩ : syracuseStep 4686245 = 878671) (by norm_num)
theorem B1900969 : Blo 1849626 1900969 := bbase (se 2 (by rfl) ⟨712863, by rfl⟩ : syracuseStep 1900969 = 1425727) (by norm_num)
theorem B8896949 : Blo 1849626 8896949 := bbase (se 5 (by rfl) ⟨417044, by rfl⟩ : syracuseStep 8896949 = 834089) (by norm_num)
theorem B2081209 : Blo 1849626 2081209 := bbase (se 2 (by rfl) ⟨780453, by rfl⟩ : syracuseStep 2081209 = 1560907) (by norm_num)
theorem B4162013 : Blo 1849626 4162013 := bbase (se 3 (by rfl) ⟨780377, by rfl⟩ : syracuseStep 4162013 = 1560755) (by norm_num)
theorem B2081245 : Blo 1849626 2081245 := bbase (se 3 (by rfl) ⟨390233, by rfl⟩ : syracuseStep 2081245 = 780467) (by norm_num)
theorem B3121645 : Blo 1849626 3121645 := bbase (se 3 (by rfl) ⟨585308, by rfl⟩ : syracuseStep 3121645 = 1170617) (by norm_num)
theorem B2343421 : Blo 1849626 2343421 := bbase (se 3 (by rfl) ⟨439391, by rfl⟩ : syracuseStep 2343421 = 878783) (by norm_num)
theorem B2081281 : Blo 1849626 2081281 := bbase (se 2 (by rfl) ⟨780480, by rfl⟩ : syracuseStep 2081281 = 1560961) (by norm_num)
theorem B3752477 : Blo 1849626 3752477 := bbase (se 3 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 3752477 = 1407179) (by norm_num)
theorem B4162085 : Blo 1849626 4162085 := bbase (se 4 (by rfl) ⟨390195, by rfl⟩ : syracuseStep 4162085 = 780391) (by norm_num)
theorem B2081317 : Blo 1849626 2081317 := bbase (se 4 (by rfl) ⟨195123, by rfl⟩ : syracuseStep 2081317 = 390247) (by norm_num)
theorem B6668837 : Blo 1849626 6668837 := bbase (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) (by norm_num)
theorem B6242885 : Blo 1849626 6242885 := bbase (se 4 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 6242885 = 1170541) (by norm_num)
theorem B3121733 : Blo 1849626 3121733 := bbase (se 4 (by rfl) ⟨292662, by rfl⟩ : syracuseStep 3121733 = 585325) (by norm_num)
theorem B2081353 : Blo 1849626 2081353 := bbase (se 2 (by rfl) ⟨780507, by rfl⟩ : syracuseStep 2081353 = 1561015) (by norm_num)
theorem B4686437 : Blo 1849626 4686437 := bbase (se 4 (by rfl) ⟨439353, by rfl⟩ : syracuseStep 4686437 = 878707) (by norm_num)
theorem B4162157 : Blo 1849626 4162157 := bbase (se 3 (by rfl) ⟨780404, by rfl⟩ : syracuseStep 4162157 = 1560809) (by norm_num)
theorem B2081389 : Blo 1849626 2081389 := bbase (se 3 (by rfl) ⟨390260, by rfl⟩ : syracuseStep 2081389 = 780521) (by norm_num)
theorem B9364085 : Blo 1849626 9364085 := bbase (se 5 (by rfl) ⟨438941, by rfl⟩ : syracuseStep 9364085 = 877883) (by norm_num)
theorem B2081425 : Blo 1849626 2081425 := bbase (se 2 (by rfl) ⟨780534, by rfl⟩ : syracuseStep 2081425 = 1561069) (by norm_num)
theorem B7029413 : Blo 1849626 7029413 := bbase (se 4 (by rfl) ⟨659007, by rfl⟩ : syracuseStep 7029413 = 1318015) (by norm_num)
theorem B4162229 : Blo 1849626 4162229 := bbase (se 5 (by rfl) ⟨195104, by rfl⟩ : syracuseStep 4162229 = 390209) (by norm_num)
theorem B2081461 : Blo 1849626 2081461 := bbase (se 5 (by rfl) ⟨97568, by rfl⟩ : syracuseStep 2081461 = 195137) (by norm_num)
theorem B3121861 : Blo 1849626 3121861 := bbase (se 4 (by rfl) ⟨292674, by rfl⟩ : syracuseStep 3121861 = 585349) (by norm_num)
theorem B2081497 : Blo 1849626 2081497 := bbase (se 2 (by rfl) ⟨780561, by rfl⟩ : syracuseStep 2081497 = 1561123) (by norm_num)
theorem B1876717 : Blo 1849626 1876717 := bbase (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) (by norm_num)
theorem B10535669 : Blo 1849626 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B4162301 : Blo 1849626 4162301 := bbase (se 3 (by rfl) ⟨780431, by rfl⟩ : syracuseStep 4162301 = 1560863) (by norm_num)
theorem B2081533 : Blo 1849626 2081533 := bbase (se 3 (by rfl) ⟨390287, by rfl⟩ : syracuseStep 2081533 = 780575) (by norm_num)
theorem B7504645 : Blo 1849626 7504645 := bbase (se 4 (by rfl) ⟨703560, by rfl⟩ : syracuseStep 7504645 = 1407121) (by norm_num)
theorem B3121949 : Blo 1849626 3121949 := bbase (se 3 (by rfl) ⟨585365, by rfl⟩ : syracuseStep 3121949 = 1170731) (by norm_num)
theorem B2081569 : Blo 1849626 2081569 := bbase (se 2 (by rfl) ⟨780588, by rfl⟩ : syracuseStep 2081569 = 1561177) (by norm_num)
theorem B4162373 : Blo 1849626 4162373 := bbase (se 4 (by rfl) ⟨390222, by rfl⟩ : syracuseStep 4162373 = 780445) (by norm_num)
theorem B2081605 : Blo 1849626 2081605 := bbase (se 4 (by rfl) ⟨195150, by rfl⟩ : syracuseStep 2081605 = 390301) (by norm_num)
theorem B2081641 : Blo 1849626 2081641 := bbase (se 2 (by rfl) ⟨780615, by rfl⟩ : syracuseStep 2081641 = 1561231) (by norm_num)
theorem B4162445 : Blo 1849626 4162445 := bbase (se 3 (by rfl) ⟨780458, by rfl⟩ : syracuseStep 4162445 = 1560917) (by norm_num)
theorem B2081677 : Blo 1849626 2081677 := bbase (se 3 (by rfl) ⟨390314, by rfl⟩ : syracuseStep 2081677 = 780629) (by norm_num)
theorem B3122077 : Blo 1849626 3122077 := bbase (se 3 (by rfl) ⟨585389, by rfl⟩ : syracuseStep 3122077 = 1170779) (by norm_num)
theorem B2081713 : Blo 1849626 2081713 := bbase (se 2 (by rfl) ⟨780642, by rfl⟩ : syracuseStep 2081713 = 1561285) (by norm_num)
theorem B4686781 : Blo 1849626 4686781 := bbase (se 3 (by rfl) ⟨878771, by rfl⟩ : syracuseStep 4686781 = 1757543) (by norm_num)
theorem B4162517 : Blo 1849626 4162517 := bbase (se 7 (by rfl) ⟨48779, by rfl⟩ : syracuseStep 4162517 = 97559) (by norm_num)
theorem B2081749 : Blo 1849626 2081749 := bbase (se 7 (by rfl) ⟨24395, by rfl⟩ : syracuseStep 2081749 = 48791) (by norm_num)
theorem B6243317 : Blo 1849626 6243317 := bbase (se 5 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 6243317 = 585311) (by norm_num)
theorem B3122165 : Blo 1849626 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B10003445 : Blo 1849626 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B2081785 : Blo 1849626 2081785 := bbase (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) (by norm_num)
theorem B4162589 : Blo 1849626 4162589 := bbase (se 3 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 4162589 = 1560971) (by norm_num)
theorem B2081821 : Blo 1849626 2081821 := bbase (se 3 (by rfl) ⟨390341, by rfl⟩ : syracuseStep 2081821 = 780683) (by norm_num)
theorem B4686893 : Blo 1849626 4686893 := bbase (se 3 (by rfl) ⟨878792, by rfl⟩ : syracuseStep 4686893 = 1757585) (by norm_num)
theorem B1975357 : Blo 1849626 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B2081857 : Blo 1849626 2081857 := bbase (se 2 (by rfl) ⟨780696, by rfl⟩ : syracuseStep 2081857 = 1561393) (by norm_num)
theorem B4162661 : Blo 1849626 4162661 := bbase (se 4 (by rfl) ⟨390249, by rfl⟩ : syracuseStep 4162661 = 780499) (by norm_num)
theorem B2081893 : Blo 1849626 2081893 := bbase (se 4 (by rfl) ⟨195177, by rfl⟩ : syracuseStep 2081893 = 390355) (by norm_num)
theorem B3122293 : Blo 1849626 3122293 := bbase (se 5 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 3122293 = 292715) (by norm_num)
theorem B2081929 : Blo 1849626 2081929 := bbase (se 2 (by rfl) ⟨780723, by rfl⟩ : syracuseStep 2081929 = 1561447) (by norm_num)
theorem B4162733 : Blo 1849626 4162733 := bbase (se 3 (by rfl) ⟨780512, by rfl⟩ : syracuseStep 4162733 = 1561025) (by norm_num)
theorem B2081965 : Blo 1849626 2081965 := bbase (se 3 (by rfl) ⟨390368, by rfl⟩ : syracuseStep 2081965 = 780737) (by norm_num)
theorem B3122381 : Blo 1849626 3122381 := bbase (se 3 (by rfl) ⟨585446, by rfl⟩ : syracuseStep 3122381 = 1170893) (by norm_num)
theorem B2082001 : Blo 1849626 2082001 := bbase (se 2 (by rfl) ⟨780750, by rfl⟩ : syracuseStep 2082001 = 1561501) (by norm_num)
theorem B3753173 : Blo 1849626 3753173 := bbase (se 7 (by rfl) ⟨43982, by rfl⟩ : syracuseStep 3753173 = 87965) (by norm_num)
theorem B4162805 : Blo 1849626 4162805 := bbase (se 5 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 4162805 = 390263) (by norm_num)
theorem B2082037 : Blo 1849626 2082037 := bbase (se 5 (by rfl) ⟨97595, by rfl⟩ : syracuseStep 2082037 = 195191) (by norm_num)
theorem B2082073 : Blo 1849626 2082073 := bbase (se 2 (by rfl) ⟨780777, by rfl⟩ : syracuseStep 2082073 = 1561555) (by norm_num)
theorem B4162877 : Blo 1849626 4162877 := bbase (se 3 (by rfl) ⟨780539, by rfl⟩ : syracuseStep 4162877 = 1561079) (by norm_num)
theorem B2082109 : Blo 1849626 2082109 := bbase (se 3 (by rfl) ⟨390395, by rfl⟩ : syracuseStep 2082109 = 780791) (by norm_num)
theorem B3122509 : Blo 1849626 3122509 := bbase (se 3 (by rfl) ⟨585470, by rfl⟩ : syracuseStep 3122509 = 1170941) (by norm_num)
theorem B30000469 : Blo 1849626 30000469 := bbase (se 12 (by rfl) ⟨10986, by rfl⟩ : syracuseStep 30000469 = 21973) (by norm_num)
theorem B2082145 : Blo 1849626 2082145 := bbase (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) (by norm_num)
theorem B4162949 : Blo 1849626 4162949 := bbase (se 4 (by rfl) ⟨390276, by rfl⟩ : syracuseStep 4162949 = 780553) (by norm_num)
theorem B2082181 : Blo 1849626 2082181 := bbase (se 4 (by rfl) ⟨195204, by rfl⟩ : syracuseStep 2082181 = 390409) (by norm_num)
theorem B2254213 : Blo 1849626 2254213 := bbase (se 4 (by rfl) ⟨211332, by rfl⟩ : syracuseStep 2254213 = 422665) (by norm_num)
theorem B2672029 : Blo 1849626 2672029 := bbase (se 3 (by rfl) ⟨501005, by rfl⟩ : syracuseStep 2672029 = 1002011) (by norm_num)
theorem B6243749 : Blo 1849626 6243749 := bbase (se 4 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 6243749 = 1170703) (by norm_num)
theorem B3122597 : Blo 1849626 3122597 := bbase (se 4 (by rfl) ⟨292743, by rfl⟩ : syracuseStep 3122597 = 585487) (by norm_num)
theorem B2082217 : Blo 1849626 2082217 := bbase (se 2 (by rfl) ⟨780831, by rfl⟩ : syracuseStep 2082217 = 1561663) (by norm_num)
theorem B4163021 : Blo 1849626 4163021 := bbase (se 3 (by rfl) ⟨780566, by rfl⟩ : syracuseStep 4163021 = 1561133) (by norm_num)
theorem B2082253 : Blo 1849626 2082253 := bbase (se 3 (by rfl) ⟨390422, by rfl⟩ : syracuseStep 2082253 = 780845) (by norm_num)
theorem B11855317 : Blo 1849626 11855317 := bbase (se 7 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 11855317 = 277859) (by norm_num)
theorem B9373157 : Blo 1849626 9373157 := bbase (se 4 (by rfl) ⟨878733, by rfl⟩ : syracuseStep 9373157 = 1757467) (by norm_num)
theorem B2082289 : Blo 1849626 2082289 := bbase (se 2 (by rfl) ⟨780858, by rfl⟩ : syracuseStep 2082289 = 1561717) (by norm_num)
theorem B1975801 : Blo 1849626 1975801 := bbase (se 2 (by rfl) ⟨740925, by rfl⟩ : syracuseStep 1975801 = 1481851) (by norm_num)
theorem B4163093 : Blo 1849626 4163093 := bbase (se 6 (by rfl) ⟨97572, by rfl⟩ : syracuseStep 4163093 = 195145) (by norm_num)
theorem B2082325 : Blo 1849626 2082325 := bbase (se 6 (by rfl) ⟨48804, by rfl⟩ : syracuseStep 2082325 = 97609) (by norm_num)
theorem B3122725 : Blo 1849626 3122725 := bbase (se 4 (by rfl) ⟨292755, by rfl⟩ : syracuseStep 3122725 = 585511) (by norm_num)
theorem B1975861 : Blo 1849626 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B2082361 : Blo 1849626 2082361 := bbase (se 2 (by rfl) ⟨780885, by rfl⟩ : syracuseStep 2082361 = 1561771) (by norm_num)
theorem B4163165 : Blo 1849626 4163165 := bbase (se 3 (by rfl) ⟨780593, by rfl⟩ : syracuseStep 4163165 = 1561187) (by norm_num)
theorem B2082397 : Blo 1849626 2082397 := bbase (se 3 (by rfl) ⟨390449, by rfl⟩ : syracuseStep 2082397 = 780899) (by norm_num)
theorem B3122813 : Blo 1849626 3122813 := bbase (se 3 (by rfl) ⟨585527, by rfl⟩ : syracuseStep 3122813 = 1171055) (by norm_num)
theorem B2082433 : Blo 1849626 2082433 := bbase (se 2 (by rfl) ⟨780912, by rfl⟩ : syracuseStep 2082433 = 1561825) (by norm_num)
theorem B4163237 : Blo 1849626 4163237 := bbase (se 4 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 4163237 = 780607) (by norm_num)
theorem B2082469 : Blo 1849626 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B7906997 : Blo 1849626 7906997 := bbase (se 5 (by rfl) ⟨370640, by rfl⟩ : syracuseStep 7906997 = 741281) (by norm_num)
theorem B2082505 : Blo 1849626 2082505 := bbase (se 2 (by rfl) ⟨780939, by rfl⟩ : syracuseStep 2082505 = 1561879) (by norm_num)
theorem B4163309 : Blo 1849626 4163309 := bbase (se 3 (by rfl) ⟨780620, by rfl⟩ : syracuseStep 4163309 = 1561241) (by norm_num)
theorem B2082541 : Blo 1849626 2082541 := bbase (se 3 (by rfl) ⟨390476, by rfl⟩ : syracuseStep 2082541 = 780953) (by norm_num)
theorem B3122941 : Blo 1849626 3122941 := bbase (se 3 (by rfl) ⟨585551, by rfl⟩ : syracuseStep 3122941 = 1171103) (by norm_num)
theorem B4007693 : Blo 1849626 4007693 := bbase (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) (by norm_num)
theorem B2082577 : Blo 1849626 2082577 := bbase (se 2 (by rfl) ⟨780966, by rfl⟩ : syracuseStep 2082577 = 1561933) (by norm_num)
theorem B4163381 : Blo 1849626 4163381 := bbase (se 5 (by rfl) ⟨195158, by rfl⟩ : syracuseStep 4163381 = 390317) (by norm_num)
theorem B2082613 : Blo 1849626 2082613 := bbase (se 5 (by rfl) ⟨97622, by rfl⟩ : syracuseStep 2082613 = 195245) (by norm_num)
theorem B6244181 : Blo 1849626 6244181 := bbase (se 9 (by rfl) ⟨18293, by rfl⟩ : syracuseStep 6244181 = 36587) (by norm_num)
theorem B3123029 : Blo 1849626 3123029 := bbase (se 9 (by rfl) ⟨9149, by rfl⟩ : syracuseStep 3123029 = 18299) (by norm_num)
theorem B2082649 : Blo 1849626 2082649 := bbase (se 2 (by rfl) ⟨780993, by rfl⟩ : syracuseStep 2082649 = 1561987) (by norm_num)
theorem B5269349 : Blo 1849626 5269349 := bbase (se 4 (by rfl) ⟨494001, by rfl⟩ : syracuseStep 5269349 = 988003) (by norm_num)
theorem B1976177 : Blo 1849626 1976177 := bbase (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) (by norm_num)
theorem B4163453 : Blo 1849626 4163453 := bbase (se 3 (by rfl) ⟨780647, by rfl⟩ : syracuseStep 4163453 = 1561295) (by norm_num)
theorem B2082685 : Blo 1849626 2082685 := bbase (se 3 (by rfl) ⟨390503, by rfl⟩ : syracuseStep 2082685 = 781007) (by norm_num)
theorem B9365381 : Blo 1849626 9365381 := bbase (se 4 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 9365381 = 1756009) (by norm_num)
theorem B2082721 : Blo 1849626 2082721 := bbase (se 2 (by rfl) ⟨781020, by rfl⟩ : syracuseStep 2082721 = 1562041) (by norm_num)
theorem B4163525 : Blo 1849626 4163525 := bbase (se 4 (by rfl) ⟨390330, by rfl⟩ : syracuseStep 4163525 = 780661) (by norm_num)
theorem B2082757 : Blo 1849626 2082757 := bbase (se 4 (by rfl) ⟨195258, by rfl⟩ : syracuseStep 2082757 = 390517) (by norm_num)
theorem B3123157 : Blo 1849626 3123157 := bbase (se 7 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 3123157 = 73199) (by norm_num)
theorem B2082793 : Blo 1849626 2082793 := bbase (se 2 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 2082793 = 1562095) (by norm_num)
theorem B6334469 : Blo 1849626 6334469 := bbase (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) (by norm_num)
theorem B4163597 : Blo 1849626 4163597 := bbase (se 3 (by rfl) ⟨780674, by rfl⟩ : syracuseStep 4163597 = 1561349) (by norm_num)
theorem B2082829 : Blo 1849626 2082829 := bbase (se 3 (by rfl) ⟨390530, by rfl⟩ : syracuseStep 2082829 = 781061) (by norm_num)
theorem B3123245 : Blo 1849626 3123245 := bbase (se 3 (by rfl) ⟨585608, by rfl⟩ : syracuseStep 3123245 = 1171217) (by norm_num)
theorem B2082865 : Blo 1849626 2082865 := bbase (se 2 (by rfl) ⟨781074, by rfl⟩ : syracuseStep 2082865 = 1562149) (by norm_num)
theorem B7505989 : Blo 1849626 7505989 := bbase (se 4 (by rfl) ⟨703686, by rfl⟩ : syracuseStep 7505989 = 1407373) (by norm_num)
theorem B4163669 : Blo 1849626 4163669 := bbase (se 8 (by rfl) ⟨24396, by rfl⟩ : syracuseStep 4163669 = 48793) (by norm_num)
theorem B35571797 : Blo 1849626 35571797 := bbase (se 8 (by rfl) ⟨208428, by rfl⟩ : syracuseStep 35571797 = 416857) (by norm_num)
theorem B2082901 : Blo 1849626 2082901 := bbase (se 8 (by rfl) ⟨12204, by rfl⟩ : syracuseStep 2082901 = 24409) (by norm_num)
theorem B2082937 : Blo 1849626 2082937 := bbase (se 2 (by rfl) ⟨781101, by rfl⟩ : syracuseStep 2082937 = 1562203) (by norm_num)
theorem B4163741 : Blo 1849626 4163741 := bbase (se 3 (by rfl) ⟨780701, by rfl⟩ : syracuseStep 4163741 = 1561403) (by norm_num)
theorem B2082973 : Blo 1849626 2082973 := bbase (se 3 (by rfl) ⟨390557, by rfl⟩ : syracuseStep 2082973 = 781115) (by norm_num)
theorem B3950765 : Blo 1849626 3950765 := bbase (se 3 (by rfl) ⟨740768, by rfl⟩ : syracuseStep 3950765 = 1481537) (by norm_num)
theorem B3123373 : Blo 1849626 3123373 := bbase (se 3 (by rfl) ⟨585632, by rfl⟩ : syracuseStep 3123373 = 1171265) (by norm_num)
theorem B2083009 : Blo 1849626 2083009 := bbase (se 2 (by rfl) ⟨781128, by rfl⟩ : syracuseStep 2083009 = 1562257) (by norm_num)
theorem B8890565 : Blo 1849626 8890565 := bbase (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) (by norm_num)
theorem B15804629 : Blo 1849626 15804629 := bbase (se 7 (by rfl) ⟨185210, by rfl⟩ : syracuseStep 15804629 = 370421) (by norm_num)
theorem B7022821 : Blo 1849626 7022821 := bbase (se 4 (by rfl) ⟨658389, by rfl⟩ : syracuseStep 7022821 = 1316779) (by norm_num)
theorem B4163813 : Blo 1849626 4163813 := bbase (se 4 (by rfl) ⟨390357, by rfl⟩ : syracuseStep 4163813 = 780715) (by norm_num)
theorem B2083045 : Blo 1849626 2083045 := bbase (se 4 (by rfl) ⟨195285, by rfl⟩ : syracuseStep 2083045 = 390571) (by norm_num)
theorem B6244613 : Blo 1849626 6244613 := bbase (se 4 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 6244613 = 1170865) (by norm_num)
theorem B3123461 : Blo 1849626 3123461 := bbase (se 4 (by rfl) ⟨292824, by rfl⟩ : syracuseStep 3123461 = 585649) (by norm_num)
theorem B4163885 : Blo 1849626 4163885 := bbase (se 3 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 4163885 = 1561457) (by norm_num)
theorem B1976621 : Blo 1849626 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B34212181 : Blo 1849626 34212181 := bbase (se 10 (by rfl) ⟨50115, by rfl⟩ : syracuseStep 34212181 = 100231) (by norm_num)
theorem B1976681 : Blo 1849626 1976681 := bbase (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) (by norm_num)
theorem B3336557 : Blo 1849626 3336557 := bbase (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) (by norm_num)
theorem B4163957 : Blo 1849626 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B3123589 : Blo 1849626 3123589 := bbase (se 4 (by rfl) ⟨292836, by rfl⟩ : syracuseStep 3123589 = 585673) (by norm_num)
theorem B3951013 : Blo 1849626 3951013 := bbase (se 4 (by rfl) ⟨370407, by rfl⟩ : syracuseStep 3951013 = 740815) (by norm_num)
theorem B10004917 : Blo 1849626 10004917 := bbase (se 5 (by rfl) ⟨468980, by rfl⟩ : syracuseStep 10004917 = 937961) (by norm_num)
theorem B4164029 : Blo 1849626 4164029 := bbase (se 3 (by rfl) ⟨780755, by rfl⟩ : syracuseStep 4164029 = 1561511) (by norm_num)
theorem B4999637 : Blo 1849626 4999637 := bbase (se 7 (by rfl) ⟨58589, by rfl⟩ : syracuseStep 4999637 = 117179) (by norm_num)
theorem B3123677 : Blo 1849626 3123677 := bbase (se 3 (by rfl) ⟨585689, by rfl⟩ : syracuseStep 3123677 = 1171379) (by norm_num)
theorem B1976809 : Blo 1849626 1976809 := bbase (se 2 (by rfl) ⟨741303, by rfl⟩ : syracuseStep 1976809 = 1482607) (by norm_num)
theorem B4164101 : Blo 1849626 4164101 := bbase (se 4 (by rfl) ⟨390384, by rfl⟩ : syracuseStep 4164101 = 780769) (by norm_num)
theorem B7023125 : Blo 1849626 7023125 := bbase (se 6 (by rfl) ⟨164604, by rfl⟩ : syracuseStep 7023125 = 329209) (by norm_num)
theorem B4999733 : Blo 1849626 4999733 := bbase (se 5 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 4999733 = 468725) (by norm_num)
theorem B4164173 : Blo 1849626 4164173 := bbase (se 3 (by rfl) ⟨780782, by rfl⟩ : syracuseStep 4164173 = 1561565) (by norm_num)
theorem B3123805 : Blo 1849626 3123805 := bbase (se 3 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 3123805 = 1171427) (by norm_num)
theorem B4164245 : Blo 1849626 4164245 := bbase (se 6 (by rfl) ⟨97599, by rfl⟩ : syracuseStep 4164245 = 195199) (by norm_num)
theorem B6245045 : Blo 1849626 6245045 := bbase (se 5 (by rfl) ⟨292736, by rfl⟩ : syracuseStep 6245045 = 585473) (by norm_num)
theorem B3123893 : Blo 1849626 3123893 := bbase (se 5 (by rfl) ⟨146432, by rfl⟩ : syracuseStep 3123893 = 292865) (by norm_num)
theorem B4164317 : Blo 1849626 4164317 := bbase (se 3 (by rfl) ⟨780809, by rfl⟩ : syracuseStep 4164317 = 1561619) (by norm_num)
theorem B4164389 : Blo 1849626 4164389 := bbase (se 4 (by rfl) ⟨390411, by rfl⟩ : syracuseStep 4164389 = 780823) (by norm_num)
theorem B13519669 : Blo 1849626 13519669 := bbase (se 5 (by rfl) ⟨633734, by rfl⟩ : syracuseStep 13519669 = 1267469) (by norm_num)
theorem B3124021 : Blo 1849626 3124021 := bbase (se 5 (by rfl) ⟨146438, by rfl⟩ : syracuseStep 3124021 = 292877) (by norm_num)
theorem B4164461 : Blo 1849626 4164461 := bbase (se 3 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 4164461 = 1561673) (by norm_num)
theorem B3124109 : Blo 1849626 3124109 := bbase (se 3 (by rfl) ⟨585770, by rfl⟩ : syracuseStep 3124109 = 1171541) (by norm_num)
theorem B10537877 : Blo 1849626 10537877 := bbase (se 6 (by rfl) ⟨246981, by rfl⟩ : syracuseStep 10537877 = 493963) (by norm_num)
theorem B3951517 : Blo 1849626 3951517 := bbase (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) (by norm_num)
theorem B6671269 : Blo 1849626 6671269 := bbase (se 4 (by rfl) ⟨625431, by rfl⟩ : syracuseStep 6671269 = 1250863) (by norm_num)
theorem B1977253 : Blo 1849626 1977253 := bbase (se 4 (by rfl) ⟨185367, by rfl⟩ : syracuseStep 1977253 = 370735) (by norm_num)
theorem B4164533 : Blo 1849626 4164533 := bbase (se 5 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 4164533 = 390425) (by norm_num)
theorem B4164605 : Blo 1849626 4164605 := bbase (se 3 (by rfl) ⟨780863, by rfl⟩ : syracuseStep 4164605 = 1561727) (by norm_num)
theorem B3124237 : Blo 1849626 3124237 := bbase (se 3 (by rfl) ⟨585794, by rfl⟩ : syracuseStep 3124237 = 1171589) (by norm_num)
theorem B2223137 : Blo 1849626 2223137 := bbase (se 2 (by rfl) ⟨833676, by rfl⟩ : syracuseStep 2223137 = 1667353) (by norm_num)
theorem B4746293 : Blo 1849626 4746293 := bbase (se 5 (by rfl) ⟨222482, by rfl⟩ : syracuseStep 4746293 = 444965) (by norm_num)
theorem B4164677 : Blo 1849626 4164677 := bbase (se 4 (by rfl) ⟨390438, by rfl⟩ : syracuseStep 4164677 = 780877) (by norm_num)
theorem B3165277 : Blo 1849626 3165277 := bbase (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) (by norm_num)
theorem B6245477 : Blo 1849626 6245477 := bbase (se 4 (by rfl) ⟨585513, by rfl⟩ : syracuseStep 6245477 = 1171027) (by norm_num)
theorem B3124325 : Blo 1849626 3124325 := bbase (se 4 (by rfl) ⟨292905, by rfl⟩ : syracuseStep 3124325 = 585811) (by norm_num)
theorem B4164749 : Blo 1849626 4164749 := bbase (se 3 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 4164749 = 1561781) (by norm_num)
theorem B9366677 : Blo 1849626 9366677 := bbase (se 6 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 9366677 = 439063) (by norm_num)
theorem B4164821 : Blo 1849626 4164821 := bbase (se 7 (by rfl) ⟨48806, by rfl⟩ : syracuseStep 4164821 = 97613) (by norm_num)
theorem B3124453 : Blo 1849626 3124453 := bbase (se 4 (by rfl) ⟨292917, by rfl⟩ : syracuseStep 3124453 = 585835) (by norm_num)
theorem B4164893 : Blo 1849626 4164893 := bbase (se 3 (by rfl) ⟨780917, by rfl⟩ : syracuseStep 4164893 = 1561835) (by norm_num)
theorem B3124541 : Blo 1849626 3124541 := bbase (se 3 (by rfl) ⟨585851, by rfl⟩ : syracuseStep 3124541 = 1171703) (by norm_num)
theorem B2223445 : Blo 1849626 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B4164965 : Blo 1849626 4164965 := bbase (se 4 (by rfl) ⟨390465, by rfl⟩ : syracuseStep 4164965 = 780931) (by norm_num)
theorem B2502029 : Blo 1849626 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B5270933 : Blo 1849626 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B4165037 : Blo 1849626 4165037 := bbase (se 3 (by rfl) ⟨780944, by rfl⟩ : syracuseStep 4165037 = 1561889) (by norm_num)
theorem B2223545 : Blo 1849626 2223545 := bbase (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) (by norm_num)
theorem B4165109 : Blo 1849626 4165109 := bbase (se 5 (by rfl) ⟨195239, by rfl⟩ : syracuseStep 4165109 = 390479) (by norm_num)
theorem B6245909 : Blo 1849626 6245909 := bbase (se 6 (by rfl) ⟨146388, by rfl⟩ : syracuseStep 6245909 = 292777) (by norm_num)
theorem B2502181 : Blo 1849626 2502181 := bbase (se 4 (by rfl) ⟨234579, by rfl⟩ : syracuseStep 2502181 = 469159) (by norm_num)
theorem B4165181 : Blo 1849626 4165181 := bbase (se 3 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 4165181 = 1561943) (by norm_num)
theorem B4165253 : Blo 1849626 4165253 := bbase (se 4 (by rfl) ⟨390492, by rfl⟩ : syracuseStep 4165253 = 780985) (by norm_num)
theorem B4165325 : Blo 1849626 4165325 := bbase (se 3 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 4165325 = 1561997) (by norm_num)
theorem B3952405 : Blo 1849626 3952405 := bbase (se 6 (by rfl) ⟨92634, by rfl⟩ : syracuseStep 3952405 = 185269) (by norm_num)
theorem B3165973 : Blo 1849626 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B4165397 : Blo 1849626 4165397 := bbase (se 6 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 4165397 = 195253) (by norm_num)
theorem B2223949 : Blo 1849626 2223949 := bbase (se 3 (by rfl) ⟨416990, by rfl⟩ : syracuseStep 2223949 = 833981) (by norm_num)
theorem B4165469 : Blo 1849626 4165469 := bbase (se 3 (by rfl) ⟨781025, by rfl⟩ : syracuseStep 4165469 = 1562051) (by norm_num)
theorem B2633581 : Blo 1849626 2633581 := bbase (se 3 (by rfl) ⟨493796, by rfl⟩ : syracuseStep 2633581 = 987593) (by norm_num)
theorem B4165541 : Blo 1849626 4165541 := bbase (se 4 (by rfl) ⟨390519, by rfl⟩ : syracuseStep 4165541 = 781039) (by norm_num)
theorem B6246341 : Blo 1849626 6246341 := bbase (se 4 (by rfl) ⟨585594, by rfl⟩ : syracuseStep 6246341 = 1171189) (by norm_num)
theorem B4165613 : Blo 1849626 4165613 := bbase (se 3 (by rfl) ⟨781052, by rfl⟩ : syracuseStep 4165613 = 1562105) (by norm_num)
theorem B2109445 : Blo 1849626 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B13340693 : Blo 1849626 13340693 := bbase (se 6 (by rfl) ⟨312672, by rfl⟩ : syracuseStep 13340693 = 625345) (by norm_num)
theorem B7901221 : Blo 1849626 7901221 := bbase (se 4 (by rfl) ⟨740739, by rfl⟩ : syracuseStep 7901221 = 1481479) (by norm_num)
theorem B5271605 : Blo 1849626 5271605 := bbase (se 5 (by rfl) ⟨247106, by rfl⟩ : syracuseStep 5271605 = 494213) (by norm_num)
theorem B4165685 : Blo 1849626 4165685 := bbase (se 5 (by rfl) ⟨195266, by rfl⟩ : syracuseStep 4165685 = 390533) (by norm_num)
theorem B7499861 : Blo 1849626 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B4165757 : Blo 1849626 4165757 := bbase (se 3 (by rfl) ⟨781079, by rfl⟩ : syracuseStep 4165757 = 1562159) (by norm_num)
theorem B2109601 : Blo 1849626 2109601 := bbase (se 2 (by rfl) ⟨791100, by rfl⟩ : syracuseStep 2109601 = 1582201) (by norm_num)
theorem B4681901 : Blo 1849626 4681901 := bbase (se 3 (by rfl) ⟨877856, by rfl⟩ : syracuseStep 4681901 = 1755713) (by norm_num)
theorem B4165829 : Blo 1849626 4165829 := bbase (se 4 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 4165829 = 781093) (by norm_num)
theorem B2224333 : Blo 1849626 2224333 := bbase (se 3 (by rfl) ⟨417062, by rfl⟩ : syracuseStep 2224333 = 834125) (by norm_num)
theorem B3952901 : Blo 1849626 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B4444429 : Blo 1849626 4444429 := bbase (se 3 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 4444429 = 1666661) (by norm_num)
theorem B4165901 : Blo 1849626 4165901 := bbase (se 3 (by rfl) ⟨781106, by rfl⟩ : syracuseStep 4165901 = 1562213) (by norm_num)
theorem B4165973 : Blo 1849626 4165973 := bbase (se 10 (by rfl) ⟨6102, by rfl⟩ : syracuseStep 4165973 = 12205) (by norm_num)
theorem B6246773 : Blo 1849626 6246773 := bbase (se 5 (by rfl) ⟨292817, by rfl⟩ : syracuseStep 6246773 = 585635) (by norm_num)
theorem B4166045 : Blo 1849626 4166045 := bbase (se 3 (by rfl) ⟨781133, by rfl⟩ : syracuseStep 4166045 = 1562267) (by norm_num)
theorem B9367973 : Blo 1849626 9367973 := bbase (se 4 (by rfl) ⟨878247, by rfl⟩ : syracuseStep 9367973 = 1756495) (by norm_num)
theorem B5272037 : Blo 1849626 5272037 := bbase (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) (by norm_num)
theorem B4166117 : Blo 1849626 4166117 := bbase (se 4 (by rfl) ⟨390573, by rfl⟩ : syracuseStep 4166117 = 781147) (by norm_num)
theorem B2535925 : Blo 1849626 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B4682245 : Blo 1849626 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B6009365 : Blo 1849626 6009365 := bbase (se 6 (by rfl) ⟨140844, by rfl⟩ : syracuseStep 6009365 = 281689) (by norm_num)
theorem B3559997 : Blo 1849626 3559997 := bbase (se 3 (by rfl) ⟨667499, by rfl⟩ : syracuseStep 3559997 = 1334999) (by norm_num)
theorem B7025237 : Blo 1849626 7025237 := bbase (se 8 (by rfl) ⟨41163, by rfl⟩ : syracuseStep 7025237 = 82327) (by norm_num)
theorem B4682357 : Blo 1849626 4682357 := bbase (se 5 (by rfl) ⟨219485, by rfl⟩ : syracuseStep 4682357 = 438971) (by norm_num)
theorem B2634373 : Blo 1849626 2634373 := bbase (se 4 (by rfl) ⟨246972, by rfl⟩ : syracuseStep 2634373 = 493945) (by norm_num)
theorem B28488341 : Blo 1849626 28488341 := bbase (se 6 (by rfl) ⟨667695, by rfl⟩ : syracuseStep 28488341 = 1335391) (by norm_num)
theorem B3961541 : Blo 1849626 3961541 := bbase (se 4 (by rfl) ⟨371394, by rfl⟩ : syracuseStep 3961541 = 742789) (by norm_num)
theorem B2110193 : Blo 1849626 2110193 := bbase (se 2 (by rfl) ⟨791322, by rfl⟩ : syracuseStep 2110193 = 1582645) (by norm_num)
theorem B6247205 : Blo 1849626 6247205 := bbase (se 4 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 6247205 = 1171351) (by norm_num)
theorem B4682549 : Blo 1849626 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B3167029 : Blo 1849626 3167029 := bbase (se 5 (by rfl) ⟨148454, by rfl⟩ : syracuseStep 3167029 = 296909) (by norm_num)
theorem B7025525 : Blo 1849626 7025525 := bbase (se 5 (by rfl) ⟨329321, by rfl⟩ : syracuseStep 7025525 = 658643) (by norm_num)
theorem B3208061 : Blo 1849626 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B5927813 : Blo 1849626 5927813 := bbase (se 4 (by rfl) ⟨555732, by rfl⟩ : syracuseStep 5927813 = 1111465) (by norm_num)
theorem B5624725 : Blo 1849626 5624725 := bbase (se 6 (by rfl) ⟨131829, by rfl⟩ : syracuseStep 5624725 = 263659) (by norm_num)
theorem B28480405 : Blo 1849626 28480405 := bbase (se 6 (by rfl) ⟨667509, by rfl⟩ : syracuseStep 28480405 = 1335019) (by norm_num)
theorem B2110357 : Blo 1849626 2110357 := bbase (se 6 (by rfl) ⟨49461, by rfl⟩ : syracuseStep 2110357 = 98923) (by norm_num)
theorem B2634709 : Blo 1849626 2634709 := bbase (se 7 (by rfl) ⟨30875, by rfl⟩ : syracuseStep 2634709 = 61751) (by norm_num)
theorem B3953789 : Blo 1849626 3953789 := bbase (se 3 (by rfl) ⟨741335, by rfl⟩ : syracuseStep 3953789 = 1482671) (by norm_num)
theorem B4682893 : Blo 1849626 4682893 := bbase (se 3 (by rfl) ⟨878042, by rfl⟩ : syracuseStep 4682893 = 1756085) (by norm_num)
theorem B2634925 : Blo 1849626 2634925 := bbase (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) (by norm_num)
theorem B6247637 : Blo 1849626 6247637 := bbase (se 7 (by rfl) ⟨73214, by rfl⟩ : syracuseStep 6247637 = 146429) (by norm_num)
theorem B5272789 : Blo 1849626 5272789 := bbase (se 7 (by rfl) ⟨61790, by rfl⟩ : syracuseStep 5272789 = 123581) (by norm_num)
theorem B3511525 : Blo 1849626 3511525 := bbase (se 4 (by rfl) ⟨329205, by rfl⟩ : syracuseStep 3511525 = 658411) (by norm_num)
theorem B3953909 : Blo 1849626 3953909 := bbase (se 5 (by rfl) ⟨185339, by rfl⟩ : syracuseStep 3953909 = 370679) (by norm_num)
theorem B4683005 : Blo 1849626 4683005 := bbase (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) (by norm_num)
theorem B4445437 : Blo 1849626 4445437 := bbase (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) (by norm_num)
theorem B7501061 : Blo 1849626 7501061 := bbase (se 4 (by rfl) ⟨703224, by rfl⟩ : syracuseStep 7501061 = 1406449) (by norm_num)
theorem B5002501 : Blo 1849626 5002501 := bbase (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) (by norm_num)
theorem B4445533 : Blo 1849626 4445533 := bbase (se 3 (by rfl) ⟨833537, by rfl⟩ : syracuseStep 4445533 = 1667075) (by norm_num)
theorem B7501157 : Blo 1849626 7501157 := bbase (se 4 (by rfl) ⟨703233, by rfl⟩ : syracuseStep 7501157 = 1406467) (by norm_num)
theorem B3511669 : Blo 1849626 3511669 := bbase (se 5 (by rfl) ⟨164609, by rfl⟩ : syracuseStep 3511669 = 329219) (by norm_num)
theorem B11859317 : Blo 1849626 11859317 := bbase (se 5 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 11859317 = 1111811) (by norm_num)
theorem B2774453 : Blo 1849626 2774453 := bbase (se 5 (by rfl) ⟨130052, by rfl⟩ : syracuseStep 2774453 = 260105) (by norm_num)
theorem B4683197 : Blo 1849626 4683197 := bbase (se 3 (by rfl) ⟨878099, by rfl⟩ : syracuseStep 4683197 = 1756199) (by norm_num)
theorem B2774477 : Blo 1849626 2774477 := bbase (se 3 (by rfl) ⟨520214, by rfl⟩ : syracuseStep 2774477 = 1040429) (by norm_num)
theorem B2774501 : Blo 1849626 2774501 := bbase (se 4 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 2774501 = 520219) (by norm_num)
theorem B2774525 : Blo 1849626 2774525 := bbase (se 3 (by rfl) ⟨520223, by rfl⟩ : syracuseStep 2774525 = 1040447) (by norm_num)
theorem B4748797 : Blo 1849626 4748797 := bbase (se 3 (by rfl) ⟨890399, by rfl⟩ : syracuseStep 4748797 = 1780799) (by norm_num)
theorem B2110973 : Blo 1849626 2110973 := bbase (se 3 (by rfl) ⟨395807, by rfl⟩ : syracuseStep 2110973 = 791615) (by norm_num)
theorem B2774549 : Blo 1849626 2774549 := bbase (se 6 (by rfl) ⟨65028, by rfl⟩ : syracuseStep 2774549 = 130057) (by norm_num)
theorem B3511829 : Blo 1849626 3511829 := bbase (se 6 (by rfl) ⟨82308, by rfl⟩ : syracuseStep 3511829 = 164617) (by norm_num)
theorem B2635301 : Blo 1849626 2635301 := bbase (se 4 (by rfl) ⟨247059, by rfl⟩ : syracuseStep 2635301 = 494119) (by norm_num)
theorem B2774573 : Blo 1849626 2774573 := bbase (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) (by norm_num)
theorem B2774597 : Blo 1849626 2774597 := bbase (se 4 (by rfl) ⟨260118, by rfl⟩ : syracuseStep 2774597 = 520237) (by norm_num)
theorem B2774621 : Blo 1849626 2774621 := bbase (se 3 (by rfl) ⟨520241, by rfl⟩ : syracuseStep 2774621 = 1040483) (by norm_num)
theorem B2774645 : Blo 1849626 2774645 := bbase (se 5 (by rfl) ⟨130061, by rfl⟩ : syracuseStep 2774645 = 260123) (by norm_num)
theorem B6248069 : Blo 1849626 6248069 := bbase (se 4 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 6248069 = 1171513) (by norm_num)
theorem B2774669 : Blo 1849626 2774669 := bbase (se 3 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 2774669 = 1040501) (by norm_num)
theorem B2774693 : Blo 1849626 2774693 := bbase (se 4 (by rfl) ⟨260127, by rfl⟩ : syracuseStep 2774693 = 520255) (by norm_num)
theorem B3511973 : Blo 1849626 3511973 := bbase (se 4 (by rfl) ⟨329247, by rfl⟩ : syracuseStep 3511973 = 658495) (by norm_num)
theorem B9369269 : Blo 1849626 9369269 := bbase (se 5 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 9369269 = 878369) (by norm_num)
theorem B2774717 : Blo 1849626 2774717 := bbase (se 3 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 2774717 = 1040519) (by norm_num)
theorem B2774741 : Blo 1849626 2774741 := bbase (se 7 (by rfl) ⟨32516, by rfl⟩ : syracuseStep 2774741 = 65033) (by norm_num)
theorem B2774765 : Blo 1849626 2774765 := bbase (se 3 (by rfl) ⟨520268, by rfl⟩ : syracuseStep 2774765 = 1040537) (by norm_num)
theorem B2963189 : Blo 1849626 2963189 := bbase (se 5 (by rfl) ⟨138899, by rfl⟩ : syracuseStep 2963189 = 277799) (by norm_num)
theorem B2774789 : Blo 1849626 2774789 := bbase (se 4 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 2774789 = 520273) (by norm_num)
theorem B4683541 : Blo 1849626 4683541 := bbase (se 6 (by rfl) ⟨109770, by rfl⟩ : syracuseStep 4683541 = 219541) (by norm_num)
theorem B2774813 : Blo 1849626 2774813 := bbase (se 3 (by rfl) ⟨520277, by rfl⟩ : syracuseStep 2774813 = 1040555) (by norm_num)
theorem B2774837 : Blo 1849626 2774837 := bbase (se 5 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 2774837 = 260141) (by norm_num)
theorem B2774861 : Blo 1849626 2774861 := bbase (se 3 (by rfl) ⟨520286, by rfl⟩ : syracuseStep 2774861 = 1040573) (by norm_num)
theorem B2774885 : Blo 1849626 2774885 := bbase (se 4 (by rfl) ⟨260145, by rfl⟩ : syracuseStep 2774885 = 520291) (by norm_num)
theorem B4446053 : Blo 1849626 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B3954541 : Blo 1849626 3954541 := bbase (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) (by norm_num)
theorem B2774909 : Blo 1849626 2774909 := bbase (se 3 (by rfl) ⟨520295, by rfl⟩ : syracuseStep 2774909 = 1040591) (by norm_num)
theorem B4683653 : Blo 1849626 4683653 := bbase (se 4 (by rfl) ⟨439092, by rfl⟩ : syracuseStep 4683653 = 878185) (by norm_num)
theorem B2774933 : Blo 1849626 2774933 := bbase (se 6 (by rfl) ⟨65037, by rfl⟩ : syracuseStep 2774933 = 130075) (by norm_num)
theorem B2774957 : Blo 1849626 2774957 := bbase (se 3 (by rfl) ⟨520304, by rfl⟩ : syracuseStep 2774957 = 1040609) (by norm_num)
theorem B2774981 : Blo 1849626 2774981 := bbase (se 4 (by rfl) ⟨260154, by rfl⟩ : syracuseStep 2774981 = 520309) (by norm_num)
theorem B3512261 : Blo 1849626 3512261 := bbase (se 4 (by rfl) ⟨329274, by rfl⟩ : syracuseStep 3512261 = 658549) (by norm_num)
theorem B3381205 : Blo 1849626 3381205 := bbase (se 7 (by rfl) ⟨39623, by rfl⟩ : syracuseStep 3381205 = 79247) (by norm_num)
theorem B2775005 : Blo 1849626 2775005 := bbase (se 3 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 2775005 = 1040627) (by norm_num)
theorem B2775029 : Blo 1849626 2775029 := bbase (se 5 (by rfl) ⟨130079, by rfl⟩ : syracuseStep 2775029 = 260159) (by norm_num)
theorem B2775053 : Blo 1849626 2775053 := bbase (se 3 (by rfl) ⟨520322, by rfl⟩ : syracuseStep 2775053 = 1040645) (by norm_num)
theorem B7026709 : Blo 1849626 7026709 := bbase (se 6 (by rfl) ⟨164688, by rfl⟩ : syracuseStep 7026709 = 329377) (by norm_num)
theorem B2775077 : Blo 1849626 2775077 := bbase (se 4 (by rfl) ⟨260163, by rfl⟩ : syracuseStep 2775077 = 520327) (by norm_num)
theorem B5339189 : Blo 1849626 5339189 := bbase (se 5 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 5339189 = 500549) (by norm_num)
theorem B6248501 : Blo 1849626 6248501 := bbase (se 5 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 6248501 = 585797) (by norm_num)
theorem B2775101 : Blo 1849626 2775101 := bbase (se 3 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 2775101 = 1040663) (by norm_num)
theorem B4683845 : Blo 1849626 4683845 := bbase (se 4 (by rfl) ⟨439110, by rfl⟩ : syracuseStep 4683845 = 878221) (by norm_num)
theorem B2775125 : Blo 1849626 2775125 := bbase (se 8 (by rfl) ⟨16260, by rfl⟩ : syracuseStep 2775125 = 32521) (by norm_num)
theorem B14252117 : Blo 1849626 14252117 := bbase (se 8 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 14252117 = 167017) (by norm_num)
theorem B3512413 : Blo 1849626 3512413 := bbase (se 3 (by rfl) ⟨658577, by rfl⟩ : syracuseStep 3512413 = 1317155) (by norm_num)
theorem B2775149 : Blo 1849626 2775149 := bbase (se 3 (by rfl) ⟨520340, by rfl⟩ : syracuseStep 2775149 = 1040681) (by norm_num)
theorem B2775173 : Blo 1849626 2775173 := bbase (se 4 (by rfl) ⟨260172, by rfl⟩ : syracuseStep 2775173 = 520345) (by norm_num)
theorem B2341001 : Blo 1849626 2341001 := bbase (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) (by norm_num)
theorem B2775197 : Blo 1849626 2775197 := bbase (se 3 (by rfl) ⟨520349, by rfl⟩ : syracuseStep 2775197 = 1040699) (by norm_num)
theorem B2775221 : Blo 1849626 2775221 := bbase (se 5 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 2775221 = 260177) (by norm_num)
theorem B14055605 : Blo 1849626 14055605 := bbase (se 5 (by rfl) ⟨658856, by rfl⟩ : syracuseStep 14055605 = 1317713) (by norm_num)
theorem B2341057 : Blo 1849626 2341057 := bbase (se 2 (by rfl) ⟨877896, by rfl⟩ : syracuseStep 2341057 = 1755793) (by norm_num)
theorem B2775245 : Blo 1849626 2775245 := bbase (se 3 (by rfl) ⟨520358, by rfl⟩ : syracuseStep 2775245 = 1040717) (by norm_num)
theorem B17832149 : Blo 1849626 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B2775269 : Blo 1849626 2775269 := bbase (se 4 (by rfl) ⟨260181, by rfl⟩ : syracuseStep 2775269 = 520363) (by norm_num)
theorem B2775293 : Blo 1849626 2775293 := bbase (se 3 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 2775293 = 1040735) (by norm_num)
theorem B2775317 : Blo 1849626 2775317 := bbase (se 6 (by rfl) ⟨65046, by rfl⟩ : syracuseStep 2775317 = 130093) (by norm_num)
theorem B2341153 : Blo 1849626 2341153 := bbase (se 2 (by rfl) ⟨877932, by rfl⟩ : syracuseStep 2341153 = 1755865) (by norm_num)
theorem B2775341 : Blo 1849626 2775341 := bbase (se 3 (by rfl) ⟨520376, by rfl⟩ : syracuseStep 2775341 = 1040753) (by norm_num)
theorem B2775365 : Blo 1849626 2775365 := bbase (se 4 (by rfl) ⟨260190, by rfl⟩ : syracuseStep 2775365 = 520381) (by norm_num)
theorem B7027013 : Blo 1849626 7027013 := bbase (se 4 (by rfl) ⟨658782, by rfl⟩ : syracuseStep 7027013 = 1317565) (by norm_num)
theorem B2775389 : Blo 1849626 2775389 := bbase (se 3 (by rfl) ⟨520385, by rfl⟩ : syracuseStep 2775389 = 1040771) (by norm_num)
theorem B2029933 : Blo 1849626 2029933 := bbase (se 3 (by rfl) ⟨380612, by rfl⟩ : syracuseStep 2029933 = 761225) (by norm_num)
theorem B2775413 : Blo 1849626 2775413 := bbase (se 5 (by rfl) ⟨130097, by rfl⟩ : syracuseStep 2775413 = 260195) (by norm_num)
theorem B4446581 : Blo 1849626 4446581 := bbase (se 5 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 4446581 = 416867) (by norm_num)
theorem B2775437 : Blo 1849626 2775437 := bbase (se 3 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 2775437 = 1040789) (by norm_num)
theorem B3512717 : Blo 1849626 3512717 := bbase (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) (by norm_num)
theorem B6330773 : Blo 1849626 6330773 := bbase (se 6 (by rfl) ⟨148377, by rfl⟩ : syracuseStep 6330773 = 296755) (by norm_num)
theorem B5003669 : Blo 1849626 5003669 := bbase (se 6 (by rfl) ⟨117273, by rfl⟩ : syracuseStep 5003669 = 234547) (by norm_num)
theorem B4684189 : Blo 1849626 4684189 := bbase (se 3 (by rfl) ⟨878285, by rfl⟩ : syracuseStep 4684189 = 1756571) (by norm_num)
theorem B2775461 : Blo 1849626 2775461 := bbase (se 4 (by rfl) ⟨260199, by rfl⟩ : syracuseStep 2775461 = 520399) (by norm_num)
theorem B2775485 : Blo 1849626 2775485 := bbase (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) (by norm_num)
theorem B2341325 : Blo 1849626 2341325 := bbase (se 3 (by rfl) ⟨438998, by rfl⟩ : syracuseStep 2341325 = 877997) (by norm_num)
theorem B2775509 : Blo 1849626 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B6248933 : Blo 1849626 6248933 := bbase (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) (by norm_num)
theorem B2775533 : Blo 1849626 2775533 := bbase (se 3 (by rfl) ⟨520412, by rfl⟩ : syracuseStep 2775533 = 1040825) (by norm_num)
theorem B2341381 : Blo 1849626 2341381 := bbase (se 4 (by rfl) ⟨219504, by rfl⟩ : syracuseStep 2341381 = 439009) (by norm_num)
theorem B2775557 : Blo 1849626 2775557 := bbase (se 4 (by rfl) ⟨260208, by rfl⟩ : syracuseStep 2775557 = 520417) (by norm_num)
theorem B4684301 : Blo 1849626 4684301 := bbase (se 3 (by rfl) ⟨878306, by rfl⟩ : syracuseStep 4684301 = 1756613) (by norm_num)
theorem B12024341 : Blo 1849626 12024341 := bbase (se 6 (by rfl) ⟨281820, by rfl⟩ : syracuseStep 12024341 = 563641) (by norm_num)
theorem B2775581 : Blo 1849626 2775581 := bbase (se 3 (by rfl) ⟨520421, by rfl⟩ : syracuseStep 2775581 = 1040843) (by norm_num)
theorem B2775605 : Blo 1849626 2775605 := bbase (se 5 (by rfl) ⟨130106, by rfl⟩ : syracuseStep 2775605 = 260213) (by norm_num)
theorem B2775629 : Blo 1849626 2775629 := bbase (se 3 (by rfl) ⟨520430, by rfl⟩ : syracuseStep 2775629 = 1040861) (by norm_num)
theorem B14047829 : Blo 1849626 14047829 := bbase (se 8 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 14047829 = 164623) (by norm_num)
theorem B2341477 : Blo 1849626 2341477 := bbase (se 4 (by rfl) ⟨219513, by rfl⟩ : syracuseStep 2341477 = 439027) (by norm_num)
theorem B8010341 : Blo 1849626 8010341 := bbase (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) (by norm_num)
theorem B2775653 : Blo 1849626 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B4446821 : Blo 1849626 4446821 := bbase (se 4 (by rfl) ⟨416889, by rfl⟩ : syracuseStep 4446821 = 833779) (by norm_num)
theorem B2775677 : Blo 1849626 2775677 := bbase (se 3 (by rfl) ⟨520439, by rfl⟩ : syracuseStep 2775677 = 1040879) (by norm_num)
theorem B2775701 : Blo 1849626 2775701 := bbase (se 6 (by rfl) ⟨65055, by rfl⟩ : syracuseStep 2775701 = 130111) (by norm_num)
theorem B2775725 : Blo 1849626 2775725 := bbase (se 3 (by rfl) ⟨520448, by rfl⟩ : syracuseStep 2775725 = 1040897) (by norm_num)
theorem B6331061 : Blo 1849626 6331061 := bbase (se 5 (by rfl) ⟨296768, by rfl⟩ : syracuseStep 6331061 = 593537) (by norm_num)
theorem B2775749 : Blo 1849626 2775749 := bbase (se 4 (by rfl) ⟨260226, by rfl⟩ : syracuseStep 2775749 = 520453) (by norm_num)
theorem B4684493 : Blo 1849626 4684493 := bbase (se 3 (by rfl) ⟨878342, by rfl⟩ : syracuseStep 4684493 = 1756685) (by norm_num)
theorem B2775773 : Blo 1849626 2775773 := bbase (se 3 (by rfl) ⟨520457, by rfl⟩ : syracuseStep 2775773 = 1040915) (by norm_num)
theorem B2775797 : Blo 1849626 2775797 := bbase (se 5 (by rfl) ⟨130115, by rfl⟩ : syracuseStep 2775797 = 260231) (by norm_num)
theorem B2775821 : Blo 1849626 2775821 := bbase (se 3 (by rfl) ⟨520466, by rfl⟩ : syracuseStep 2775821 = 1040933) (by norm_num)
theorem B2341649 : Blo 1849626 2341649 := bbase (se 2 (by rfl) ⟨878118, by rfl⟩ : syracuseStep 2341649 = 1756237) (by norm_num)
theorem B18987797 : Blo 1849626 18987797 := bbase (se 6 (by rfl) ⟨445026, by rfl⟩ : syracuseStep 18987797 = 890053) (by norm_num)
theorem B8010533 : Blo 1849626 8010533 := bbase (se 4 (by rfl) ⟨750987, by rfl⟩ : syracuseStep 8010533 = 1501975) (by norm_num)
theorem B2775845 : Blo 1849626 2775845 := bbase (se 4 (by rfl) ⟨260235, by rfl⟩ : syracuseStep 2775845 = 520471) (by norm_num)
theorem B2775869 : Blo 1849626 2775869 := bbase (se 3 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 2775869 = 1040951) (by norm_num)
theorem B2341705 : Blo 1849626 2341705 := bbase (se 2 (by rfl) ⟨878139, by rfl⟩ : syracuseStep 2341705 = 1756279) (by norm_num)
theorem B2775893 : Blo 1849626 2775893 := bbase (se 9 (by rfl) ⟨8132, by rfl⟩ : syracuseStep 2775893 = 16265) (by norm_num)
theorem B2775917 : Blo 1849626 2775917 := bbase (se 3 (by rfl) ⟨520484, by rfl⟩ : syracuseStep 2775917 = 1040969) (by norm_num)
theorem B2775941 : Blo 1849626 2775941 := bbase (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) (by norm_num)
theorem B2775965 : Blo 1849626 2775965 := bbase (se 3 (by rfl) ⟨520493, by rfl⟩ : syracuseStep 2775965 = 1040987) (by norm_num)
theorem B2341801 : Blo 1849626 2341801 := bbase (se 2 (by rfl) ⟨878175, by rfl⟩ : syracuseStep 2341801 = 1756351) (by norm_num)
theorem B2775989 : Blo 1849626 2775989 := bbase (se 5 (by rfl) ⟨130124, by rfl⟩ : syracuseStep 2775989 = 260249) (by norm_num)
theorem B9370565 : Blo 1849626 9370565 := bbase (se 4 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 9370565 = 1756981) (by norm_num)
theorem B2776013 : Blo 1849626 2776013 := bbase (se 3 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 2776013 = 1041005) (by norm_num)
theorem B7904213 : Blo 1849626 7904213 := bbase (se 7 (by rfl) ⟨92627, by rfl⟩ : syracuseStep 7904213 = 185255) (by norm_num)
theorem B2776037 : Blo 1849626 2776037 := bbase (se 4 (by rfl) ⟨260253, by rfl⟩ : syracuseStep 2776037 = 520507) (by norm_num)
theorem B16251893 : Blo 1849626 16251893 := bbase (se 5 (by rfl) ⟨761807, by rfl⟩ : syracuseStep 16251893 = 1523615) (by norm_num)
theorem B2776061 : Blo 1849626 2776061 := bbase (se 3 (by rfl) ⟨520511, by rfl⟩ : syracuseStep 2776061 = 1041023) (by norm_num)
theorem B2776085 : Blo 1849626 2776085 := bbase (se 6 (by rfl) ⟨65064, by rfl⟩ : syracuseStep 2776085 = 130129) (by norm_num)
theorem B5930005 : Blo 1849626 5930005 := bbase (se 6 (by rfl) ⟨138984, by rfl⟩ : syracuseStep 5930005 = 277969) (by norm_num)
theorem B4684837 : Blo 1849626 4684837 := bbase (se 4 (by rfl) ⟨439203, by rfl⟩ : syracuseStep 4684837 = 878407) (by norm_num)
theorem B2776109 : Blo 1849626 2776109 := bbase (se 3 (by rfl) ⟨520520, by rfl⟩ : syracuseStep 2776109 = 1041041) (by norm_num)
theorem B2776133 : Blo 1849626 2776133 := bbase (se 4 (by rfl) ⟨260262, by rfl⟩ : syracuseStep 2776133 = 520525) (by norm_num)
theorem B2341973 : Blo 1849626 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B2776157 : Blo 1849626 2776157 := bbase (se 3 (by rfl) ⟨520529, by rfl⟩ : syracuseStep 2776157 = 1041059) (by norm_num)
theorem B2776181 : Blo 1849626 2776181 := bbase (se 5 (by rfl) ⟨130133, by rfl⟩ : syracuseStep 2776181 = 260267) (by norm_num)
theorem B3513469 : Blo 1849626 3513469 := bbase (se 3 (by rfl) ⟨658775, by rfl⟩ : syracuseStep 3513469 = 1317551) (by norm_num)
theorem B2342029 : Blo 1849626 2342029 := bbase (se 3 (by rfl) ⟨439130, by rfl⟩ : syracuseStep 2342029 = 878261) (by norm_num)
theorem B2776205 : Blo 1849626 2776205 := bbase (se 3 (by rfl) ⟨520538, by rfl⟩ : syracuseStep 2776205 = 1041077) (by norm_num)
theorem B4684949 : Blo 1849626 4684949 := bbase (se 6 (by rfl) ⟨109803, by rfl⟩ : syracuseStep 4684949 = 219607) (by norm_num)
theorem B2776229 : Blo 1849626 2776229 := bbase (se 4 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 2776229 = 520543) (by norm_num)
theorem B2776253 : Blo 1849626 2776253 := bbase (se 3 (by rfl) ⟨520547, by rfl⟩ : syracuseStep 2776253 = 1041095) (by norm_num)
theorem B2776277 : Blo 1849626 2776277 := bbase (se 7 (by rfl) ⟨32534, by rfl⟩ : syracuseStep 2776277 = 65069) (by norm_num)
theorem B2964701 : Blo 1849626 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B2342125 : Blo 1849626 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B2776301 : Blo 1849626 2776301 := bbase (se 3 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 2776301 = 1041113) (by norm_num)
theorem B2776325 : Blo 1849626 2776325 := bbase (se 4 (by rfl) ⟨260280, by rfl⟩ : syracuseStep 2776325 = 520561) (by norm_num)
theorem B3513613 : Blo 1849626 3513613 := bbase (se 3 (by rfl) ⟨658802, by rfl⟩ : syracuseStep 3513613 = 1317605) (by norm_num)
theorem B2776349 : Blo 1849626 2776349 := bbase (se 3 (by rfl) ⟨520565, by rfl⟩ : syracuseStep 2776349 = 1041131) (by norm_num)
theorem B2776373 : Blo 1849626 2776373 := bbase (se 5 (by rfl) ⟨130142, by rfl⟩ : syracuseStep 2776373 = 260285) (by norm_num)
theorem B2440513 : Blo 1849626 2440513 := bbase (se 2 (by rfl) ⟨915192, by rfl⟩ : syracuseStep 2440513 = 1830385) (by norm_num)
theorem B2776397 : Blo 1849626 2776397 := bbase (se 3 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 2776397 = 1041149) (by norm_num)
theorem B4685141 : Blo 1849626 4685141 := bbase (se 11 (by rfl) ⟨3431, by rfl⟩ : syracuseStep 4685141 = 6863) (by norm_num)
theorem B2776421 : Blo 1849626 2776421 := bbase (se 4 (by rfl) ⟨260289, by rfl⟩ : syracuseStep 2776421 = 520579) (by norm_num)
theorem B3751285 : Blo 1849626 3751285 := bbase (se 5 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 3751285 = 351683) (by norm_num)
theorem B2776445 : Blo 1849626 2776445 := bbase (se 3 (by rfl) ⟨520583, by rfl⟩ : syracuseStep 2776445 = 1041167) (by norm_num)
theorem B2776469 : Blo 1849626 2776469 := bbase (se 6 (by rfl) ⟨65073, by rfl⟩ : syracuseStep 2776469 = 130147) (by norm_num)
theorem B2342297 : Blo 1849626 2342297 := bbase (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) (by norm_num)
theorem B3513773 : Blo 1849626 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B2776493 : Blo 1849626 2776493 := bbase (se 3 (by rfl) ⟨520592, by rfl⟩ : syracuseStep 2776493 = 1041185) (by norm_num)
theorem B2776517 : Blo 1849626 2776517 := bbase (se 4 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 2776517 = 520597) (by norm_num)
theorem B2342353 : Blo 1849626 2342353 := bbase (se 2 (by rfl) ⟨878382, by rfl⟩ : syracuseStep 2342353 = 1756765) (by norm_num)
theorem B2776541 : Blo 1849626 2776541 := bbase (se 3 (by rfl) ⟨520601, by rfl⟩ : syracuseStep 2776541 = 1041203) (by norm_num)
theorem B2776565 : Blo 1849626 2776565 := bbase (se 5 (by rfl) ⟨130151, by rfl⟩ : syracuseStep 2776565 = 260303) (by norm_num)
theorem B2776589 : Blo 1849626 2776589 := bbase (se 3 (by rfl) ⟨520610, by rfl⟩ : syracuseStep 2776589 = 1041221) (by norm_num)
theorem B2776613 : Blo 1849626 2776613 := bbase (se 4 (by rfl) ⟨260307, by rfl⟩ : syracuseStep 2776613 = 520615) (by norm_num)
theorem B2342449 : Blo 1849626 2342449 := bbase (se 2 (by rfl) ⟨878418, by rfl⟩ : syracuseStep 2342449 = 1756837) (by norm_num)
theorem B15416885 : Blo 1849626 15416885 := bbase (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) (by norm_num)
theorem B3513917 : Blo 1849626 3513917 := bbase (se 3 (by rfl) ⟨658859, by rfl⟩ : syracuseStep 3513917 = 1317719) (by norm_num)
theorem B2776637 : Blo 1849626 2776637 := bbase (se 3 (by rfl) ⟨520619, by rfl⟩ : syracuseStep 2776637 = 1041239) (by norm_num)
theorem B3006029 : Blo 1849626 3006029 := bbase (se 3 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 3006029 = 1127261) (by norm_num)
theorem B2776661 : Blo 1849626 2776661 := bbase (se 8 (by rfl) ⟨16269, by rfl⟩ : syracuseStep 2776661 = 32539) (by norm_num)
theorem B2776685 : Blo 1849626 2776685 := bbase (se 3 (by rfl) ⟨520628, by rfl⟩ : syracuseStep 2776685 = 1041257) (by norm_num)
theorem B2776709 : Blo 1849626 2776709 := bbase (se 4 (by rfl) ⟨260316, by rfl⟩ : syracuseStep 2776709 = 520633) (by norm_num)
theorem B2670229 : Blo 1849626 2670229 := bbase (se 6 (by rfl) ⟨62583, by rfl⟩ : syracuseStep 2670229 = 125167) (by norm_num)
theorem B2776733 : Blo 1849626 2776733 := bbase (se 3 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 2776733 = 1041275) (by norm_num)
theorem B2965157 : Blo 1849626 2965157 := bbase (se 4 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 2965157 = 555967) (by norm_num)
theorem B4685485 : Blo 1849626 4685485 := bbase (se 3 (by rfl) ⟨878528, by rfl⟩ : syracuseStep 4685485 = 1757057) (by norm_num)
theorem B2776757 : Blo 1849626 2776757 := bbase (se 5 (by rfl) ⟨130160, by rfl⟩ : syracuseStep 2776757 = 260321) (by norm_num)
theorem B2776781 : Blo 1849626 2776781 := bbase (se 3 (by rfl) ⟨520646, by rfl⟩ : syracuseStep 2776781 = 1041293) (by norm_num)
theorem B2342621 : Blo 1849626 2342621 := bbase (se 3 (by rfl) ⟨439241, by rfl⟩ : syracuseStep 2342621 = 878483) (by norm_num)
theorem B2776805 : Blo 1849626 2776805 := bbase (se 4 (by rfl) ⟨260325, by rfl⟩ : syracuseStep 2776805 = 520651) (by norm_num)
theorem B2776829 : Blo 1849626 2776829 := bbase (se 3 (by rfl) ⟨520655, by rfl⟩ : syracuseStep 2776829 = 1041311) (by norm_num)
theorem B2342677 : Blo 1849626 2342677 := bbase (se 6 (by rfl) ⟨54906, by rfl⟩ : syracuseStep 2342677 = 109813) (by norm_num)
theorem B2776853 : Blo 1849626 2776853 := bbase (se 6 (by rfl) ⟨65082, by rfl⟩ : syracuseStep 2776853 = 130165) (by norm_num)
theorem B4685597 : Blo 1849626 4685597 := bbase (se 3 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 4685597 = 1757099) (by norm_num)
theorem B2776877 : Blo 1849626 2776877 := bbase (se 3 (by rfl) ⟨520664, by rfl⟩ : syracuseStep 2776877 = 1041329) (by norm_num)
theorem B2776901 : Blo 1849626 2776901 := bbase (se 4 (by rfl) ⟨260334, by rfl⟩ : syracuseStep 2776901 = 520669) (by norm_num)
theorem B5930837 : Blo 1849626 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B3514205 : Blo 1849626 3514205 := bbase (se 3 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 3514205 = 1317827) (by norm_num)
theorem B2776925 : Blo 1849626 2776925 := bbase (se 3 (by rfl) ⟨520673, by rfl⟩ : syracuseStep 2776925 = 1041347) (by norm_num)
theorem B2342773 : Blo 1849626 2342773 := bbase (se 5 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 2342773 = 219635) (by norm_num)
theorem B2776949 : Blo 1849626 2776949 := bbase (se 5 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 2776949 = 260339) (by norm_num)
theorem B2776973 : Blo 1849626 2776973 := bbase (se 3 (by rfl) ⟨520682, by rfl⟩ : syracuseStep 2776973 = 1041365) (by norm_num)
theorem B2776997 : Blo 1849626 2776997 := bbase (se 4 (by rfl) ⟨260343, by rfl⟩ : syracuseStep 2776997 = 520687) (by norm_num)
theorem B2777021 : Blo 1849626 2777021 := bbase (se 3 (by rfl) ⟨520691, by rfl⟩ : syracuseStep 2777021 = 1041383) (by norm_num)
theorem B7905221 : Blo 1849626 7905221 := bbase (se 4 (by rfl) ⟨741114, by rfl⟩ : syracuseStep 7905221 = 1482229) (by norm_num)
theorem B2777045 : Blo 1849626 2777045 := bbase (se 7 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 2777045 = 65087) (by norm_num)
theorem B4685789 : Blo 1849626 4685789 := bbase (se 3 (by rfl) ⟨878585, by rfl⟩ : syracuseStep 4685789 = 1757171) (by norm_num)
theorem B2777069 : Blo 1849626 2777069 := bbase (se 3 (by rfl) ⟨520700, by rfl⟩ : syracuseStep 2777069 = 1041401) (by norm_num)
theorem B17784821 : Blo 1849626 17784821 := bbase (se 5 (by rfl) ⟨833663, by rfl⟩ : syracuseStep 17784821 = 1667327) (by norm_num)
theorem B3514357 : Blo 1849626 3514357 := bbase (se 5 (by rfl) ⟨164735, by rfl⟩ : syracuseStep 3514357 = 329471) (by norm_num)
theorem B1851395 : Blo 1849626 1851395 := bstep (se 1 (by rfl) ⟨1388546, by rfl⟩ : syracuseStep 1851395 = 2777093) B2777093
theorem B2777105 : Blo 1849626 2777105 := bstep (se 2 (by rfl) ⟨1041414, by rfl⟩ : syracuseStep 2777105 = 2082829) B2082829
theorem B1851411 : Blo 1849626 1851411 := bstep (se 1 (by rfl) ⟨1388558, by rfl⟩ : syracuseStep 1851411 = 2777117) B2777117
theorem B3514403 : Blo 1849626 3514403 := bstep (se 1 (by rfl) ⟨2635802, by rfl⟩ : syracuseStep 3514403 = 5271605) B5271605
theorem B2777123 : Blo 1849626 2777123 := bstep (se 1 (by rfl) ⟨2082842, by rfl⟩ : syracuseStep 2777123 = 4165685) B4165685
theorem B1851427 : Blo 1849626 1851427 := bstep (se 1 (by rfl) ⟨1388570, by rfl⟩ : syracuseStep 1851427 = 2777141) B2777141
theorem B10534961 : Blo 1849626 10534961 := bstep (se 2 (by rfl) ⟨3950610, by rfl⟩ : syracuseStep 10534961 = 7901221) B7901221
theorem B1851443 : Blo 1849626 1851443 := bstep (se 1 (by rfl) ⟨1388582, by rfl⟩ : syracuseStep 1851443 = 2777165) B2777165
theorem B2777153 : Blo 1849626 2777153 := bstep (se 2 (by rfl) ⟨1041432, by rfl⟩ : syracuseStep 2777153 = 2082865) B2082865
theorem B1851459 : Blo 1849626 1851459 := bstep (se 1 (by rfl) ⟨1388594, by rfl⟩ : syracuseStep 1851459 = 2777189) B2777189
theorem B2777171 : Blo 1849626 2777171 := bstep (se 1 (by rfl) ⟨2082878, by rfl⟩ : syracuseStep 2777171 = 4165757) B4165757
theorem B1851475 : Blo 1849626 1851475 := bstep (se 1 (by rfl) ⟨1388606, by rfl⟩ : syracuseStep 1851475 = 2777213) B2777213
theorem B2080867 : Blo 1849626 2080867 := bstep (se 1 (by rfl) ⟨1560650, by rfl⟩ : syracuseStep 2080867 = 3121301) B3121301
theorem B1851491 : Blo 1849626 1851491 := bstep (se 1 (by rfl) ⟨1388618, by rfl⟩ : syracuseStep 1851491 = 2777237) B2777237
theorem B2777201 : Blo 1849626 2777201 := bstep (se 2 (by rfl) ⟨1041450, by rfl⟩ : syracuseStep 2777201 = 2082901) B2082901
theorem B3121267 : Blo 1849626 3121267 := bstep (se 1 (by rfl) ⟨2340950, by rfl⟩ : syracuseStep 3121267 = 4681901) B4681901
theorem B1851507 : Blo 1849626 1851507 := bstep (se 1 (by rfl) ⟨1388630, by rfl⟩ : syracuseStep 1851507 = 2777261) B2777261
theorem B2777219 : Blo 1849626 2777219 := bstep (se 1 (by rfl) ⟨2082914, by rfl⟩ : syracuseStep 2777219 = 4165829) B4165829
theorem B1851523 : Blo 1849626 1851523 := bstep (se 1 (by rfl) ⟨1388642, by rfl⟩ : syracuseStep 1851523 = 2777285) B2777285
theorem B1851539 : Blo 1849626 1851539 := bstep (se 1 (by rfl) ⟨1388654, by rfl⟩ : syracuseStep 1851539 = 2777309) B2777309
theorem B2777249 : Blo 1849626 2777249 := bstep (se 2 (by rfl) ⟨1041468, by rfl⟩ : syracuseStep 2777249 = 2082937) B2082937
theorem B1851555 : Blo 1849626 1851555 := bstep (se 1 (by rfl) ⟨1388666, by rfl⟩ : syracuseStep 1851555 = 2777333) B2777333
theorem B2777267 : Blo 1849626 2777267 := bstep (se 1 (by rfl) ⟨2082950, by rfl⟩ : syracuseStep 2777267 = 4165901) B4165901
theorem B1851571 : Blo 1849626 1851571 := bstep (se 1 (by rfl) ⟨1388678, by rfl⟩ : syracuseStep 1851571 = 2777357) B2777357
theorem B2343107 : Blo 1849626 2343107 := bstep (se 1 (by rfl) ⟨1757330, by rfl⟩ : syracuseStep 2343107 = 3514661) B3514661
theorem B1851587 : Blo 1849626 1851587 := bstep (se 1 (by rfl) ⟨1388690, by rfl⟩ : syracuseStep 1851587 = 2777381) B2777381
theorem B2777297 : Blo 1849626 2777297 := bstep (se 2 (by rfl) ⟨1041486, by rfl⟩ : syracuseStep 2777297 = 2082973) B2082973
theorem B1851603 : Blo 1849626 1851603 := bstep (se 1 (by rfl) ⟨1388702, by rfl⟩ : syracuseStep 1851603 = 2777405) B2777405
theorem B5931235 : Blo 1849626 5931235 := bstep (se 1 (by rfl) ⟨4448426, by rfl⟩ : syracuseStep 5931235 = 8896853) B8896853
theorem B2777315 : Blo 1849626 2777315 := bstep (se 1 (by rfl) ⟨2082986, by rfl⟩ : syracuseStep 2777315 = 4165973) B4165973
theorem B1851619 : Blo 1849626 1851619 := bstep (se 1 (by rfl) ⟨1388714, by rfl⟩ : syracuseStep 1851619 = 2777429) B2777429
theorem B2081011 : Blo 1849626 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B3121409 : Blo 1849626 3121409 := bstep (se 2 (by rfl) ⟨1170528, by rfl⟩ : syracuseStep 3121409 = 2341057) B2341057
theorem B4686083 : Blo 1849626 4686083 := bstep (se 1 (by rfl) ⟨3514562, by rfl⟩ : syracuseStep 4686083 = 7029125) B7029125
theorem B2777345 : Blo 1849626 2777345 := bstep (se 2 (by rfl) ⟨1041504, by rfl⟩ : syracuseStep 2777345 = 2083009) B2083009
theorem B2965777 : Blo 1849626 2965777 := bstep (se 2 (by rfl) ⟨1112166, by rfl⟩ : syracuseStep 2965777 = 2224333) B2224333
theorem B2777363 : Blo 1849626 2777363 := bstep (se 1 (by rfl) ⟨2083022, by rfl⟩ : syracuseStep 2777363 = 4166045) B4166045
theorem B5931299 : Blo 1849626 5931299 := bstep (se 1 (by rfl) ⟨4448474, by rfl⟩ : syracuseStep 5931299 = 8896949) B8896949
theorem B9363761 : Blo 1849626 9363761 := bstep (se 2 (by rfl) ⟨3511410, by rfl⟩ : syracuseStep 9363761 = 7022821) B7022821
theorem B2777393 : Blo 1849626 2777393 := bstep (se 2 (by rfl) ⟨1041522, by rfl⟩ : syracuseStep 2777393 = 2083045) B2083045
theorem B3514691 : Blo 1849626 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B2777411 : Blo 1849626 2777411 := bstep (se 1 (by rfl) ⟨2083058, by rfl⟩ : syracuseStep 2777411 = 4166117) B4166117
theorem B4006243 : Blo 1849626 4006243 := bstep (se 1 (by rfl) ⟨3004682, by rfl⟩ : syracuseStep 4006243 = 6009365) B6009365
theorem B6242669 : Blo 1849626 6242669 := bstep (se 3 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 6242669 = 2341001) B2341001
theorem B4161905 : Blo 1849626 4161905 := bstep (se 2 (by rfl) ⟨1560714, by rfl⟩ : syracuseStep 4161905 = 3121429) B3121429
theorem B5931377 : Blo 1849626 5931377 := bstep (se 2 (by rfl) ⟨2224266, by rfl⟩ : syracuseStep 5931377 = 4448533) B4448533
theorem B3121537 : Blo 1849626 3121537 := bstep (se 2 (by rfl) ⟨1170576, by rfl⟩ : syracuseStep 3121537 = 2341153) B2341153
theorem B4161923 : Blo 1849626 4161923 := bstep (se 1 (by rfl) ⟨3121442, by rfl⟩ : syracuseStep 4161923 = 6242885) B6242885
theorem B2081155 : Blo 1849626 2081155 := bstep (se 1 (by rfl) ⟨1560866, by rfl⟩ : syracuseStep 2081155 = 3121733) B3121733
theorem B6242723 : Blo 1849626 6242723 := bstep (se 1 (by rfl) ⟨4682042, by rfl⟩ : syracuseStep 6242723 = 9364085) B9364085
theorem B3121571 : Blo 1849626 3121571 := bstep (se 1 (by rfl) ⟨2341178, by rfl⟩ : syracuseStep 3121571 = 4682357) B4682357
theorem B4686275 : Blo 1849626 4686275 := bstep (se 1 (by rfl) ⟨3514706, by rfl⟩ : syracuseStep 4686275 = 7029413) B7029413
theorem B23708173 : Blo 1849626 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B2081299 : Blo 1849626 2081299 := bstep (se 1 (by rfl) ⟨1560974, by rfl⟩ : syracuseStep 2081299 = 3121949) B3121949
theorem B3121699 : Blo 1849626 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B5268017 : Blo 1849626 5268017 := bstep (se 2 (by rfl) ⟨1975506, by rfl⟩ : syracuseStep 5268017 = 3951013) B3951013
theorem B7905869 : Blo 1849626 7905869 := bstep (se 3 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 7905869 = 2964701) B2964701
theorem B2138707 : Blo 1849626 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B4162193 : Blo 1849626 4162193 := bstep (se 2 (by rfl) ⟨1560822, by rfl⟩ : syracuseStep 4162193 = 3121645) B3121645
theorem B4162211 : Blo 1849626 4162211 := bstep (se 1 (by rfl) ⟨3121658, by rfl⟩ : syracuseStep 4162211 = 6243317) B6243317
theorem B2081443 : Blo 1849626 2081443 := bstep (se 1 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 2081443 = 3122165) B3122165
theorem B6668963 : Blo 1849626 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B6242993 : Blo 1849626 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B3121841 : Blo 1849626 3121841 := bstep (se 2 (by rfl) ⟨1170690, by rfl⟩ : syracuseStep 3121841 = 2341381) B2341381
theorem B5702381 : Blo 1849626 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B3121969 : Blo 1849626 3121969 := bstep (se 2 (by rfl) ⟨1170738, by rfl⟩ : syracuseStep 3121969 = 2341477) B2341477
theorem B2081587 : Blo 1849626 2081587 := bstep (se 1 (by rfl) ⟨1561190, by rfl⟩ : syracuseStep 2081587 = 3122381) B3122381
theorem B3122003 : Blo 1849626 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B7906211 : Blo 1849626 7906211 := bstep (se 1 (by rfl) ⟨5929658, by rfl⟩ : syracuseStep 7906211 = 11859317) B11859317
theorem B4162481 : Blo 1849626 4162481 := bstep (se 2 (by rfl) ⟨1560930, by rfl⟩ : syracuseStep 4162481 = 3121861) B3121861
theorem B4162499 : Blo 1849626 4162499 := bstep (se 1 (by rfl) ⟨3121874, by rfl⟩ : syracuseStep 4162499 = 6243749) B6243749
theorem B2081731 : Blo 1849626 2081731 := bstep (se 1 (by rfl) ⟨1561298, by rfl⟩ : syracuseStep 2081731 = 3122597) B3122597
theorem B3122131 : Blo 1849626 3122131 := bstep (se 1 (by rfl) ⟨2341598, by rfl⟩ : syracuseStep 3122131 = 4683197) B4683197
theorem B2081875 : Blo 1849626 2081875 := bstep (se 1 (by rfl) ⟨1561406, by rfl⟩ : syracuseStep 2081875 = 3122813) B3122813
theorem B3122273 : Blo 1849626 3122273 := bstep (se 2 (by rfl) ⟨1170852, by rfl⟩ : syracuseStep 3122273 = 2341705) B2341705
theorem B2671795 : Blo 1849626 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B6243533 : Blo 1849626 6243533 := bstep (se 3 (by rfl) ⟨1170662, by rfl⟩ : syracuseStep 6243533 = 2341325) B2341325
theorem B4162769 : Blo 1849626 4162769 := bstep (se 2 (by rfl) ⟨1561038, by rfl⟩ : syracuseStep 4162769 = 3122077) B3122077
theorem B5268689 : Blo 1849626 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B3122401 : Blo 1849626 3122401 := bstep (se 2 (by rfl) ⟨1170900, by rfl⟩ : syracuseStep 3122401 = 2341801) B2341801
theorem B4162787 : Blo 1849626 4162787 := bstep (se 1 (by rfl) ⟨3122090, by rfl⟩ : syracuseStep 4162787 = 6244181) B6244181
theorem B2082019 : Blo 1849626 2082019 := bstep (se 1 (by rfl) ⟨1561514, by rfl⟩ : syracuseStep 2082019 = 3123029) B3123029
theorem B6243587 : Blo 1849626 6243587 := bstep (se 1 (by rfl) ⟨4682690, by rfl⟩ : syracuseStep 6243587 = 9365381) B9365381
theorem B3122435 : Blo 1849626 3122435 := bstep (se 1 (by rfl) ⟨2341826, by rfl⟩ : syracuseStep 3122435 = 4683653) B4683653
theorem B7906673 : Blo 1849626 7906673 := bstep (se 2 (by rfl) ⟨2965002, by rfl⟩ : syracuseStep 7906673 = 5930005) B5930005
theorem B2082163 : Blo 1849626 2082163 := bstep (se 1 (by rfl) ⟨1561622, by rfl⟩ : syracuseStep 2082163 = 3123245) B3123245
theorem B3122563 : Blo 1849626 3122563 := bstep (se 1 (by rfl) ⟨2341922, by rfl⟩ : syracuseStep 3122563 = 4683845) B4683845
theorem B16885189 : Blo 1849626 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B4220369 : Blo 1849626 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B10536419 : Blo 1849626 10536419 := bstep (se 1 (by rfl) ⟨7902314, by rfl⟩ : syracuseStep 10536419 = 15804629) B15804629
theorem B11888099 : Blo 1849626 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B4163057 : Blo 1849626 4163057 := bstep (se 2 (by rfl) ⟨1561146, by rfl⟩ : syracuseStep 4163057 = 3122293) B3122293
theorem B4163075 : Blo 1849626 4163075 := bstep (se 1 (by rfl) ⟨3122306, by rfl⟩ : syracuseStep 4163075 = 6244613) B6244613
theorem B2082307 : Blo 1849626 2082307 := bstep (se 1 (by rfl) ⟨1561730, by rfl⟩ : syracuseStep 2082307 = 3123461) B3123461
theorem B6243857 : Blo 1849626 6243857 := bstep (se 2 (by rfl) ⟨2341446, by rfl⟩ : syracuseStep 6243857 = 4682893) B4682893
theorem B3122705 : Blo 1849626 3122705 := bstep (se 2 (by rfl) ⟨1171014, by rfl⟩ : syracuseStep 3122705 = 2342029) B2342029
theorem B4220515 : Blo 1849626 4220515 := bstep (se 1 (by rfl) ⟨3165386, by rfl⟩ : syracuseStep 4220515 = 6330773) B6330773
theorem B3335779 : Blo 1849626 3335779 := bstep (se 1 (by rfl) ⟨2501834, by rfl⟩ : syracuseStep 3335779 = 5003669) B5003669
theorem B7030385 : Blo 1849626 7030385 := bstep (se 2 (by rfl) ⟨2636394, by rfl⟩ : syracuseStep 7030385 = 5272789) B5272789
theorem B3122833 : Blo 1849626 3122833 := bstep (se 2 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 3122833 = 2342125) B2342125
theorem B2082451 : Blo 1849626 2082451 := bstep (se 1 (by rfl) ⟨1561838, by rfl⟩ : syracuseStep 2082451 = 3123677) B3123677
theorem B6670001 : Blo 1849626 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B3122867 : Blo 1849626 3122867 := bstep (se 1 (by rfl) ⟨2342150, by rfl⟩ : syracuseStep 3122867 = 4684301) B4684301
theorem B9365219 : Blo 1849626 9365219 := bstep (se 1 (by rfl) ⟨7023914, by rfl⟩ : syracuseStep 9365219 = 14047829) B14047829
theorem B3254017 : Blo 1849626 3254017 := bstep (se 2 (by rfl) ⟨1220256, by rfl⟩ : syracuseStep 3254017 = 2440513) B2440513
theorem B4163345 : Blo 1849626 4163345 := bstep (se 2 (by rfl) ⟨1561254, by rfl⟩ : syracuseStep 4163345 = 3122509) B3122509
theorem B4163363 : Blo 1849626 4163363 := bstep (se 1 (by rfl) ⟨3122522, by rfl⟩ : syracuseStep 4163363 = 6245045) B6245045
theorem B2082595 : Blo 1849626 2082595 := bstep (se 1 (by rfl) ⟨1561946, by rfl⟩ : syracuseStep 2082595 = 3123893) B3123893
theorem B3122995 : Blo 1849626 3122995 := bstep (se 1 (by rfl) ⟨2342246, by rfl⟩ : syracuseStep 3122995 = 4684493) B4684493
theorem B23709509 : Blo 1849626 23709509 := bstep (se 4 (by rfl) ⟨2222766, by rfl⟩ : syracuseStep 23709509 = 4445533) B4445533
theorem B12658531 : Blo 1849626 12658531 := bstep (se 1 (by rfl) ⟨9493898, by rfl⟩ : syracuseStep 12658531 = 18987797) B18987797
theorem B2082739 : Blo 1849626 2082739 := bstep (se 1 (by rfl) ⟨1562054, by rfl⟩ : syracuseStep 2082739 = 3124109) B3124109
theorem B3123137 : Blo 1849626 3123137 := bstep (se 2 (by rfl) ⟨1171176, by rfl⟩ : syracuseStep 3123137 = 2342353) B2342353
theorem B5269475 : Blo 1849626 5269475 := bstep (se 1 (by rfl) ⟨3952106, by rfl⟩ : syracuseStep 5269475 = 7904213) B7904213
theorem B3164195 : Blo 1849626 3164195 := bstep (se 1 (by rfl) ⟨2373146, by rfl⟩ : syracuseStep 3164195 = 4746293) B4746293
theorem B6244397 : Blo 1849626 6244397 := bstep (se 3 (by rfl) ⟨1170824, by rfl⟩ : syracuseStep 6244397 = 2341649) B2341649
theorem B4163633 : Blo 1849626 4163633 := bstep (se 2 (by rfl) ⟨1561362, by rfl⟩ : syracuseStep 4163633 = 3122725) B3122725
theorem B3336241 : Blo 1849626 3336241 := bstep (se 2 (by rfl) ⟨1251090, by rfl⟩ : syracuseStep 3336241 = 2502181) B2502181
theorem B3123265 : Blo 1849626 3123265 := bstep (se 2 (by rfl) ⟨1171224, by rfl⟩ : syracuseStep 3123265 = 2342449) B2342449
theorem B4163651 : Blo 1849626 4163651 := bstep (se 1 (by rfl) ⟨3122738, by rfl⟩ : syracuseStep 4163651 = 6245477) B6245477
theorem B2082883 : Blo 1849626 2082883 := bstep (se 1 (by rfl) ⟨1562162, by rfl⟩ : syracuseStep 2082883 = 3124325) B3124325
theorem B6244451 : Blo 1849626 6244451 := bstep (se 1 (by rfl) ⟨4683338, by rfl⟩ : syracuseStep 6244451 = 9366677) B9366677
theorem B3123299 : Blo 1849626 3123299 := bstep (se 1 (by rfl) ⟨2342474, by rfl⟩ : syracuseStep 3123299 = 4684949) B4684949
theorem B10545349 : Blo 1849626 10545349 := bstep (se 4 (by rfl) ⟨988626, by rfl⟩ : syracuseStep 10545349 = 1977253) B1977253
theorem B2083027 : Blo 1849626 2083027 := bstep (se 1 (by rfl) ⟨1562270, by rfl⟩ : syracuseStep 2083027 = 3124541) B3124541
theorem B3123427 : Blo 1849626 3123427 := bstep (se 1 (by rfl) ⟨2342570, by rfl⟩ : syracuseStep 3123427 = 4685141) B4685141
theorem B5269805 : Blo 1849626 5269805 := bstep (se 3 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 5269805 = 1976177) B1976177
theorem B4163921 : Blo 1849626 4163921 := bstep (se 2 (by rfl) ⟨1561470, by rfl⟩ : syracuseStep 4163921 = 3122941) B3122941
theorem B4163939 : Blo 1849626 4163939 := bstep (se 1 (by rfl) ⟨3122954, by rfl⟩ : syracuseStep 4163939 = 6245909) B6245909
theorem B6244721 : Blo 1849626 6244721 := bstep (se 2 (by rfl) ⟨2341770, by rfl⟩ : syracuseStep 6244721 = 4683541) B4683541
theorem B5269873 : Blo 1849626 5269873 := bstep (se 2 (by rfl) ⟨1976202, by rfl⟩ : syracuseStep 5269873 = 3952405) B3952405
theorem B3123569 : Blo 1849626 3123569 := bstep (se 2 (by rfl) ⟨1171338, by rfl⟩ : syracuseStep 3123569 = 2342677) B2342677
theorem B1976771 : Blo 1849626 1976771 := bstep (se 1 (by rfl) ⟨1482578, by rfl⟩ : syracuseStep 1976771 = 2965157) B2965157
theorem B3123697 : Blo 1849626 3123697 := bstep (se 2 (by rfl) ⟨1171386, by rfl⟩ : syracuseStep 3123697 = 2342773) B2342773
theorem B9366029 : Blo 1849626 9366029 := bstep (se 3 (by rfl) ⟨1756130, by rfl⟩ : syracuseStep 9366029 = 3512261) B3512261
theorem B3123731 : Blo 1849626 3123731 := bstep (se 1 (by rfl) ⟨2342798, by rfl⟩ : syracuseStep 3123731 = 4685597) B4685597
theorem B4164209 : Blo 1849626 4164209 := bstep (se 2 (by rfl) ⟨1561578, by rfl⟩ : syracuseStep 4164209 = 3123157) B3123157
theorem B4508273 : Blo 1849626 4508273 := bstep (se 2 (by rfl) ⟨1690602, by rfl⟩ : syracuseStep 4508273 = 3381205) B3381205
theorem B5270147 : Blo 1849626 5270147 := bstep (se 1 (by rfl) ⟨3952610, by rfl⟩ : syracuseStep 5270147 = 7905221) B7905221
theorem B4164227 : Blo 1849626 4164227 := bstep (se 1 (by rfl) ⟨3123170, by rfl⟩ : syracuseStep 4164227 = 6246341) B6246341
theorem B3123859 : Blo 1849626 3123859 := bstep (se 1 (by rfl) ⟨2342894, by rfl⟩ : syracuseStep 3123859 = 4685789) B4685789
theorem B11856547 : Blo 1849626 11856547 := bstep (se 1 (by rfl) ⟨8892410, by rfl⟩ : syracuseStep 11856547 = 17784821) B17784821
theorem B11250373 : Blo 1849626 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B4999907 : Blo 1849626 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B3124001 : Blo 1849626 3124001 := bstep (se 2 (by rfl) ⟨1171500, by rfl⟩ : syracuseStep 3124001 = 2343001) B2343001
theorem B2812801 : Blo 1849626 2812801 := bstep (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) B2109601
theorem B6245261 : Blo 1849626 6245261 := bstep (se 3 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 6245261 = 2341973) B2341973
theorem B38005645 : Blo 1849626 38005645 := bstep (se 3 (by rfl) ⟨7126058, by rfl⟩ : syracuseStep 38005645 = 14252117) B14252117
theorem B4164497 : Blo 1849626 4164497 := bstep (se 2 (by rfl) ⟨1561686, by rfl⟩ : syracuseStep 4164497 = 3123373) B3123373
theorem B3124129 : Blo 1849626 3124129 := bstep (se 2 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 3124129 = 2343097) B2343097
theorem B4164515 : Blo 1849626 4164515 := bstep (se 1 (by rfl) ⟨3123386, by rfl⟩ : syracuseStep 4164515 = 6246773) B6246773
theorem B6245315 : Blo 1849626 6245315 := bstep (se 1 (by rfl) ⟨4683986, by rfl⟩ : syracuseStep 6245315 = 9367973) B9367973
theorem B3124163 : Blo 1849626 3124163 := bstep (se 1 (by rfl) ⟨2343122, by rfl⟩ : syracuseStep 3124163 = 4686245) B4686245
theorem B5925905 : Blo 1849626 5925905 := bstep (se 2 (by rfl) ⟨2222214, by rfl⟩ : syracuseStep 5925905 = 4444429) B4444429
theorem B2501651 : Blo 1849626 2501651 := bstep (se 1 (by rfl) ⟨1876238, by rfl⟩ : syracuseStep 2501651 = 3752477) B3752477
theorem B3124291 : Blo 1849626 3124291 := bstep (se 1 (by rfl) ⟨2343218, by rfl⟩ : syracuseStep 3124291 = 4686437) B4686437
theorem B18992227 : Blo 1849626 18992227 := bstep (se 1 (by rfl) ⟨14244170, by rfl⟩ : syracuseStep 18992227 = 28488341) B28488341
theorem B45616241 : Blo 1849626 45616241 := bstep (se 2 (by rfl) ⟨17106090, by rfl⟩ : syracuseStep 45616241 = 34212181) B34212181
theorem B2641027 : Blo 1849626 2641027 := bstep (se 1 (by rfl) ⟨1980770, by rfl⟩ : syracuseStep 2641027 = 3961541) B3961541
theorem B2706577 : Blo 1849626 2706577 := bstep (se 2 (by rfl) ⟨1014966, by rfl⟩ : syracuseStep 2706577 = 2029933) B2029933
theorem B7023779 : Blo 1849626 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B7023793 : Blo 1849626 7023793 := bstep (se 2 (by rfl) ⟨2633922, by rfl⟩ : syracuseStep 7023793 = 5267845) B5267845
theorem B4164785 : Blo 1849626 4164785 := bstep (se 2 (by rfl) ⟨1561794, by rfl⟩ : syracuseStep 4164785 = 3123589) B3123589
theorem B4164803 : Blo 1849626 4164803 := bstep (se 1 (by rfl) ⟨3123602, by rfl⟩ : syracuseStep 4164803 = 6247205) B6247205
theorem B6245585 : Blo 1849626 6245585 := bstep (se 2 (by rfl) ⟨2342094, by rfl⟩ : syracuseStep 6245585 = 4684189) B4684189
theorem B3124433 : Blo 1849626 3124433 := bstep (se 2 (by rfl) ⟨1171662, by rfl⟩ : syracuseStep 3124433 = 2343325) B2343325
theorem B13339889 : Blo 1849626 13339889 := bstep (se 2 (by rfl) ⟨5002458, by rfl⟩ : syracuseStep 13339889 = 10004917) B10004917
theorem B3951875 : Blo 1849626 3951875 := bstep (se 1 (by rfl) ⟨2963906, by rfl⟩ : syracuseStep 3951875 = 5927813) B5927813
theorem B3124561 : Blo 1849626 3124561 := bstep (se 2 (by rfl) ⟨1171710, by rfl⟩ : syracuseStep 3124561 = 2343421) B2343421
theorem B3124595 : Blo 1849626 3124595 := bstep (se 1 (by rfl) ⟨2343446, by rfl⟩ : syracuseStep 3124595 = 4686893) B4686893
theorem B14241221 : Blo 1849626 14241221 := bstep (se 4 (by rfl) ⟨1335114, by rfl⟩ : syracuseStep 14241221 = 2670229) B2670229
theorem B5270989 : Blo 1849626 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B4165073 : Blo 1849626 4165073 := bstep (se 2 (by rfl) ⟨1561902, by rfl⟩ : syracuseStep 4165073 = 3123805) B3123805
theorem B4165091 : Blo 1849626 4165091 := bstep (se 1 (by rfl) ⟨3123818, by rfl⟩ : syracuseStep 4165091 = 6247637) B6247637
theorem B5000707 : Blo 1849626 5000707 := bstep (se 1 (by rfl) ⟨3750530, by rfl⟩ : syracuseStep 5000707 = 7501061) B7501061
theorem B5000771 : Blo 1849626 5000771 := bstep (se 1 (by rfl) ⟨3750578, by rfl⟩ : syracuseStep 5000771 = 7501157) B7501157
theorem B5271149 : Blo 1849626 5271149 := bstep (se 3 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 5271149 = 1976681) B1976681
theorem B11857549 : Blo 1849626 11857549 := bstep (se 3 (by rfl) ⟨2223290, by rfl⟩ : syracuseStep 11857549 = 4446581) B4446581
theorem B2502289 : Blo 1849626 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B10006193 : Blo 1849626 10006193 := bstep (se 2 (by rfl) ⟨3752322, by rfl⟩ : syracuseStep 10006193 = 7504645) B7504645
theorem B10006213 : Blo 1849626 10006213 := bstep (se 4 (by rfl) ⟨938082, by rfl⟩ : syracuseStep 10006213 = 1876165) B1876165
theorem B6672077 : Blo 1849626 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B6246125 : Blo 1849626 6246125 := bstep (se 3 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 6246125 = 2342297) B2342297
theorem B18026225 : Blo 1849626 18026225 := bstep (se 2 (by rfl) ⟨6759834, by rfl⟩ : syracuseStep 18026225 = 13519669) B13519669
theorem B4165361 : Blo 1849626 4165361 := bstep (se 2 (by rfl) ⟨1562010, by rfl⟩ : syracuseStep 4165361 = 3124021) B3124021
theorem B4222705 : Blo 1849626 4222705 := bstep (se 2 (by rfl) ⟨1583514, by rfl⟩ : syracuseStep 4222705 = 3167029) B3167029
theorem B4165379 : Blo 1849626 4165379 := bstep (se 1 (by rfl) ⟨3124034, by rfl⟩ : syracuseStep 4165379 = 6248069) B6248069
theorem B6246179 : Blo 1849626 6246179 := bstep (se 1 (by rfl) ⟨4684634, by rfl⟩ : syracuseStep 6246179 = 9369269) B9369269
theorem B5271331 : Blo 1849626 5271331 := bstep (se 1 (by rfl) ⟨3953498, by rfl⟩ : syracuseStep 5271331 = 7906997) B7906997
theorem B35589941 : Blo 1849626 35589941 := bstep (se 5 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 35589941 = 3336557) B3336557
theorem B7499633 : Blo 1849626 7499633 := bstep (se 2 (by rfl) ⟨2812362, by rfl⟩ : syracuseStep 7499633 = 5624725) B5624725
theorem B37973873 : Blo 1849626 37973873 := bstep (se 2 (by rfl) ⟨14240202, by rfl⟩ : syracuseStep 37973873 = 28480405) B28480405
theorem B4222979 : Blo 1849626 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B4165649 : Blo 1849626 4165649 := bstep (se 2 (by rfl) ⟨1562118, by rfl⟩ : syracuseStep 4165649 = 3124237) B3124237
theorem B3559459 : Blo 1849626 3559459 := bstep (se 1 (by rfl) ⟨2669594, by rfl⟩ : syracuseStep 3559459 = 5339189) B5339189
theorem B4165667 : Blo 1849626 4165667 := bstep (se 1 (by rfl) ⟨3124250, by rfl⟩ : syracuseStep 4165667 = 6248501) B6248501
theorem B6246449 : Blo 1849626 6246449 := bstep (se 2 (by rfl) ⟨2342418, by rfl⟩ : syracuseStep 6246449 = 4684837) B4684837
theorem B2633809 : Blo 1849626 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B2633843 : Blo 1849626 2633843 := bstep (se 1 (by rfl) ⟨1975382, by rfl⟩ : syracuseStep 2633843 = 3950765) B3950765
theorem B8016077 : Blo 1849626 8016077 := bstep (se 3 (by rfl) ⟨1503014, by rfl⟩ : syracuseStep 8016077 = 3006029) B3006029
theorem B4682033 : Blo 1849626 4682033 := bstep (se 2 (by rfl) ⟨1755762, by rfl⟩ : syracuseStep 4682033 = 3511525) B3511525
theorem B4165937 : Blo 1849626 4165937 := bstep (se 2 (by rfl) ⟨1562226, by rfl⟩ : syracuseStep 4165937 = 3124453) B3124453
theorem B4165955 : Blo 1849626 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B5927249 : Blo 1849626 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B4682083 : Blo 1849626 4682083 := bstep (se 1 (by rfl) ⟨3511562, by rfl⟩ : syracuseStep 4682083 = 7023125) B7023125
theorem B8016227 : Blo 1849626 8016227 := bstep (se 1 (by rfl) ⟨6012170, by rfl⟩ : syracuseStep 8016227 = 12024341) B12024341
theorem B4682225 : Blo 1849626 4682225 := bstep (se 2 (by rfl) ⟨1755834, by rfl⟩ : syracuseStep 4682225 = 3511669) B3511669
theorem B5001713 : Blo 1849626 5001713 := bstep (se 2 (by rfl) ⟨1875642, by rfl⟩ : syracuseStep 5001713 = 3751285) B3751285
theorem B6246989 : Blo 1849626 6246989 := bstep (se 3 (by rfl) ⟨1171310, by rfl⟩ : syracuseStep 6246989 = 2342621) B2342621
theorem B7025251 : Blo 1849626 7025251 := bstep (se 1 (by rfl) ⟨5268938, by rfl⟩ : syracuseStep 7025251 = 10537877) B10537877
theorem B15807089 : Blo 1849626 15807089 := bstep (se 2 (by rfl) ⟨5927658, by rfl⟩ : syracuseStep 15807089 = 11855317) B11855317
theorem B6247043 : Blo 1849626 6247043 := bstep (se 1 (by rfl) ⟨4685282, by rfl⟩ : syracuseStep 6247043 = 9370565) B9370565
theorem B7901837 : Blo 1849626 7901837 := bstep (se 3 (by rfl) ⟨1481594, by rfl⟩ : syracuseStep 7901837 = 2963189) B2963189
theorem B2634401 : Blo 1849626 2634401 := bstep (se 2 (by rfl) ⟨987900, by rfl⟩ : syracuseStep 2634401 = 1975801) B1975801
theorem B10834595 : Blo 1849626 10834595 := bstep (se 1 (by rfl) ⟨8125946, by rfl⟩ : syracuseStep 10834595 = 16251893) B16251893
theorem B2634481 : Blo 1849626 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B21361421 : Blo 1849626 21361421 := bstep (se 3 (by rfl) ⟨4005266, by rfl⟩ : syracuseStep 21361421 = 8010533) B8010533
theorem B10138501 : Blo 1849626 10138501 := bstep (se 4 (by rfl) ⟨950484, by rfl⟩ : syracuseStep 10138501 = 1900969) B1900969
theorem B6247313 : Blo 1849626 6247313 := bstep (se 2 (by rfl) ⟨2342742, by rfl⟩ : syracuseStep 6247313 = 4685485) B4685485
theorem B10277923 : Blo 1849626 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B3511441 : Blo 1849626 3511441 := bstep (se 2 (by rfl) ⟨1316790, by rfl⟩ : syracuseStep 3511441 = 2633581) B2633581
theorem B5272721 : Blo 1849626 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B22508725 : Blo 1849626 22508725 := bstep (se 5 (by rfl) ⟨1055096, by rfl⟩ : syracuseStep 22508725 = 2110193) B2110193
theorem B3953891 : Blo 1849626 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B22517045 : Blo 1849626 22517045 := bstep (se 5 (by rfl) ⟨1055486, by rfl⟩ : syracuseStep 22517045 = 2110973) B2110973
theorem B8893795 : Blo 1849626 8893795 := bstep (se 1 (by rfl) ⟨6670346, by rfl⟩ : syracuseStep 8893795 = 13340693) B13340693
theorem B9368945 : Blo 1849626 9368945 := bstep (se 2 (by rfl) ⟨3513354, by rfl⟩ : syracuseStep 9368945 = 7026709) B7026709
theorem B5002609 : Blo 1849626 5002609 := bstep (se 2 (by rfl) ⟨1875978, by rfl⟩ : syracuseStep 5002609 = 3751957) B3751957
theorem B5928365 : Blo 1849626 5928365 := bstep (se 3 (by rfl) ⟨1111568, by rfl⟩ : syracuseStep 5928365 = 2223137) B2223137
theorem B6247853 : Blo 1849626 6247853 := bstep (se 3 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 6247853 = 2342945) B2342945
theorem B2774465 : Blo 1849626 2774465 := bstep (se 2 (by rfl) ⟨1040424, by rfl⟩ : syracuseStep 2774465 = 2080849) B2080849
theorem B4683217 : Blo 1849626 4683217 := bstep (se 2 (by rfl) ⟨1756206, by rfl⟩ : syracuseStep 4683217 = 3512413) B3512413
theorem B2774483 : Blo 1849626 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B6247907 : Blo 1849626 6247907 := bstep (se 1 (by rfl) ⟨4685930, by rfl⟩ : syracuseStep 6247907 = 9371861) B9371861
theorem B2774513 : Blo 1849626 2774513 := bstep (se 2 (by rfl) ⟨1040442, by rfl⟩ : syracuseStep 2774513 = 2080885) B2080885
theorem B2774531 : Blo 1849626 2774531 := bstep (se 1 (by rfl) ⟨2080898, by rfl⟩ : syracuseStep 2774531 = 4161797) B4161797
theorem B2635267 : Blo 1849626 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B2774561 : Blo 1849626 2774561 := bstep (se 2 (by rfl) ⟨1040460, by rfl⟩ : syracuseStep 2774561 = 2080921) B2080921
theorem B2774579 : Blo 1849626 2774579 := bstep (se 1 (by rfl) ⟨2080934, by rfl⟩ : syracuseStep 2774579 = 4161869) B4161869
theorem B2774609 : Blo 1849626 2774609 := bstep (se 2 (by rfl) ⟨1040478, by rfl⟩ : syracuseStep 2774609 = 2080957) B2080957
theorem B2774627 : Blo 1849626 2774627 := bstep (se 1 (by rfl) ⟨2080970, by rfl⟩ : syracuseStep 2774627 = 4161941) B4161941
theorem B2774657 : Blo 1849626 2774657 := bstep (se 2 (by rfl) ⟨1040496, by rfl⟩ : syracuseStep 2774657 = 2080993) B2080993
theorem B2774675 : Blo 1849626 2774675 := bstep (se 1 (by rfl) ⟨2081006, by rfl⟩ : syracuseStep 2774675 = 4162013) B4162013
theorem B2774705 : Blo 1849626 2774705 := bstep (se 2 (by rfl) ⟨1040514, by rfl⟩ : syracuseStep 2774705 = 2081029) B2081029
theorem B2774723 : Blo 1849626 2774723 := bstep (se 1 (by rfl) ⟨2081042, by rfl⟩ : syracuseStep 2774723 = 4162085) B4162085
theorem B4445891 : Blo 1849626 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B40031941 : Blo 1849626 40031941 := bstep (se 4 (by rfl) ⟨3752994, by rfl⟩ : syracuseStep 40031941 = 7505989) B7505989
theorem B2373331 : Blo 1849626 2373331 := bstep (se 1 (by rfl) ⟨1779998, by rfl⟩ : syracuseStep 2373331 = 3559997) B3559997
theorem B2774753 : Blo 1849626 2774753 := bstep (se 2 (by rfl) ⟨1040532, by rfl⟩ : syracuseStep 2774753 = 2081065) B2081065
theorem B4683491 : Blo 1849626 4683491 := bstep (se 1 (by rfl) ⟨3512618, by rfl⟩ : syracuseStep 4683491 = 7025237) B7025237
theorem B6248177 : Blo 1849626 6248177 := bstep (se 2 (by rfl) ⟨2343066, by rfl⟩ : syracuseStep 6248177 = 4686133) B4686133
theorem B2774771 : Blo 1849626 2774771 := bstep (se 1 (by rfl) ⟨2081078, by rfl⟩ : syracuseStep 2774771 = 4162157) B4162157
theorem B2774801 : Blo 1849626 2774801 := bstep (se 2 (by rfl) ⟨1040550, by rfl⟩ : syracuseStep 2774801 = 2081101) B2081101
theorem B2774819 : Blo 1849626 2774819 := bstep (se 1 (by rfl) ⟨2081114, by rfl⟩ : syracuseStep 2774819 = 4162229) B4162229
theorem B2774849 : Blo 1849626 2774849 := bstep (se 2 (by rfl) ⟨1040568, by rfl⟩ : syracuseStep 2774849 = 2081137) B2081137
theorem B2774867 : Blo 1849626 2774867 := bstep (se 1 (by rfl) ⟨2081150, by rfl⟩ : syracuseStep 2774867 = 4162301) B4162301
theorem B2774897 : Blo 1849626 2774897 := bstep (se 2 (by rfl) ⟨1040586, by rfl⟩ : syracuseStep 2774897 = 2081173) B2081173
theorem B2774915 : Blo 1849626 2774915 := bstep (se 1 (by rfl) ⟨2081186, by rfl⟩ : syracuseStep 2774915 = 4162373) B4162373
theorem B10008461 : Blo 1849626 10008461 := bstep (se 3 (by rfl) ⟨1876586, by rfl⟩ : syracuseStep 10008461 = 3753173) B3753173
theorem B2774945 : Blo 1849626 2774945 := bstep (se 2 (by rfl) ⟨1040604, by rfl⟩ : syracuseStep 2774945 = 2081209) B2081209
theorem B4683683 : Blo 1849626 4683683 := bstep (se 1 (by rfl) ⟨3512762, by rfl⟩ : syracuseStep 4683683 = 7025525) B7025525
theorem B2774963 : Blo 1849626 2774963 := bstep (se 1 (by rfl) ⟨2081222, by rfl⟩ : syracuseStep 2774963 = 4162445) B4162445
theorem B2774993 : Blo 1849626 2774993 := bstep (se 2 (by rfl) ⟨1040622, by rfl⟩ : syracuseStep 2774993 = 2081245) B2081245
theorem B2635745 : Blo 1849626 2635745 := bstep (se 2 (by rfl) ⟨988404, by rfl⟩ : syracuseStep 2635745 = 1976809) B1976809
theorem B2775011 : Blo 1849626 2775011 := bstep (se 1 (by rfl) ⟨2081258, by rfl⟩ : syracuseStep 2775011 = 4162517) B4162517
theorem B3381233 : Blo 1849626 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B2775041 : Blo 1849626 2775041 := bstep (se 2 (by rfl) ⟨1040640, by rfl⟩ : syracuseStep 2775041 = 2081281) B2081281
theorem B2775059 : Blo 1849626 2775059 := bstep (se 1 (by rfl) ⟨2081294, by rfl⟩ : syracuseStep 2775059 = 4162589) B4162589
theorem B2775089 : Blo 1849626 2775089 := bstep (se 2 (by rfl) ⟨1040658, by rfl⟩ : syracuseStep 2775089 = 2081317) B2081317
theorem B2775107 : Blo 1849626 2775107 := bstep (se 1 (by rfl) ⟨2081330, by rfl⟩ : syracuseStep 2775107 = 4162661) B4162661
theorem B2635859 : Blo 1849626 2635859 := bstep (se 1 (by rfl) ⟨1976894, by rfl⟩ : syracuseStep 2635859 = 3953789) B3953789
theorem B2775137 : Blo 1849626 2775137 := bstep (se 2 (by rfl) ⟨1040676, by rfl⟩ : syracuseStep 2775137 = 2081353) B2081353
theorem B2775155 : Blo 1849626 2775155 := bstep (se 1 (by rfl) ⟨2081366, by rfl⟩ : syracuseStep 2775155 = 4162733) B4162733
theorem B2775185 : Blo 1849626 2775185 := bstep (se 2 (by rfl) ⟨1040694, by rfl⟩ : syracuseStep 2775185 = 2081389) B2081389
theorem B2775203 : Blo 1849626 2775203 := bstep (se 1 (by rfl) ⟨2081402, by rfl⟩ : syracuseStep 2775203 = 4162805) B4162805
theorem B2635939 : Blo 1849626 2635939 := bstep (se 1 (by rfl) ⟨1976954, by rfl⟩ : syracuseStep 2635939 = 3953909) B3953909
theorem B3512497 : Blo 1849626 3512497 := bstep (se 2 (by rfl) ⟨1317186, by rfl⟩ : syracuseStep 3512497 = 2634373) B2634373
theorem B2775233 : Blo 1849626 2775233 := bstep (se 2 (by rfl) ⟨1040712, by rfl⟩ : syracuseStep 2775233 = 2081425) B2081425
theorem B2775251 : Blo 1849626 2775251 := bstep (se 1 (by rfl) ⟨2081438, by rfl⟩ : syracuseStep 2775251 = 4162877) B4162877
theorem B2775281 : Blo 1849626 2775281 := bstep (se 2 (by rfl) ⟨1040730, by rfl⟩ : syracuseStep 2775281 = 2081461) B2081461
theorem B2775299 : Blo 1849626 2775299 := bstep (se 1 (by rfl) ⟨2081474, by rfl⟩ : syracuseStep 2775299 = 4162949) B4162949
theorem B6248717 : Blo 1849626 6248717 := bstep (se 3 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 6248717 = 2343269) B2343269
theorem B2775329 : Blo 1849626 2775329 := bstep (se 2 (by rfl) ⟨1040748, by rfl⟩ : syracuseStep 2775329 = 2081497) B2081497
theorem B1849635 : Blo 1849626 1849635 := bstep (se 1 (by rfl) ⟨1387226, by rfl⟩ : syracuseStep 1849635 = 2774453) B2774453
theorem B1849651 : Blo 1849626 1849651 := bstep (se 1 (by rfl) ⟨1387238, by rfl⟩ : syracuseStep 1849651 = 2774477) B2774477
theorem B2775347 : Blo 1849626 2775347 := bstep (se 1 (by rfl) ⟨2081510, by rfl⟩ : syracuseStep 2775347 = 4163021) B4163021
theorem B1849667 : Blo 1849626 1849667 := bstep (se 1 (by rfl) ⟨1387250, by rfl⟩ : syracuseStep 1849667 = 2774501) B2774501
theorem B6248771 : Blo 1849626 6248771 := bstep (se 1 (by rfl) ⟨4686578, by rfl⟩ : syracuseStep 6248771 = 9373157) B9373157
theorem B2775377 : Blo 1849626 2775377 := bstep (se 2 (by rfl) ⟨1040766, by rfl⟩ : syracuseStep 2775377 = 2081533) B2081533
theorem B1849683 : Blo 1849626 1849683 := bstep (se 1 (by rfl) ⟨1387262, by rfl⟩ : syracuseStep 1849683 = 2774525) B2774525
theorem B1849699 : Blo 1849626 1849699 := bstep (se 1 (by rfl) ⟨1387274, by rfl⟩ : syracuseStep 1849699 = 2774549) B2774549
theorem B2341219 : Blo 1849626 2341219 := bstep (se 1 (by rfl) ⟨1755914, by rfl⟩ : syracuseStep 2341219 = 3511829) B3511829
theorem B2775395 : Blo 1849626 2775395 := bstep (se 1 (by rfl) ⟨2081546, by rfl⟩ : syracuseStep 2775395 = 4163093) B4163093
theorem B1849715 : Blo 1849626 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B2775425 : Blo 1849626 2775425 := bstep (se 2 (by rfl) ⟨1040784, by rfl⟩ : syracuseStep 2775425 = 2081569) B2081569
theorem B1849731 : Blo 1849626 1849731 := bstep (se 1 (by rfl) ⟨1387298, by rfl⟩ : syracuseStep 1849731 = 2774597) B2774597
theorem B1849747 : Blo 1849626 1849747 := bstep (se 1 (by rfl) ⟨1387310, by rfl⟩ : syracuseStep 1849747 = 2774621) B2774621
theorem B2775443 : Blo 1849626 2775443 := bstep (se 1 (by rfl) ⟨2081582, by rfl⟩ : syracuseStep 2775443 = 4163165) B4163165
theorem B1849763 : Blo 1849626 1849763 := bstep (se 1 (by rfl) ⟨1387322, by rfl⟩ : syracuseStep 1849763 = 2774645) B2774645
theorem B2775473 : Blo 1849626 2775473 := bstep (se 2 (by rfl) ⟨1040802, by rfl⟩ : syracuseStep 2775473 = 2081605) B2081605
theorem B1849779 : Blo 1849626 1849779 := bstep (se 1 (by rfl) ⟨1387334, by rfl⟩ : syracuseStep 1849779 = 2774669) B2774669
theorem B1849795 : Blo 1849626 1849795 := bstep (se 1 (by rfl) ⟨1387346, by rfl⟩ : syracuseStep 1849795 = 2774693) B2774693
theorem B2341315 : Blo 1849626 2341315 := bstep (se 1 (by rfl) ⟨1755986, by rfl⟩ : syracuseStep 2341315 = 3511973) B3511973
theorem B2775491 : Blo 1849626 2775491 := bstep (se 1 (by rfl) ⟨2081618, by rfl⟩ : syracuseStep 2775491 = 4163237) B4163237
theorem B1849811 : Blo 1849626 1849811 := bstep (se 1 (by rfl) ⟨1387358, by rfl⟩ : syracuseStep 1849811 = 2774717) B2774717
theorem B2775521 : Blo 1849626 2775521 := bstep (se 2 (by rfl) ⟨1040820, by rfl⟩ : syracuseStep 2775521 = 2081641) B2081641
theorem B1849827 : Blo 1849626 1849827 := bstep (se 1 (by rfl) ⟨1387370, by rfl⟩ : syracuseStep 1849827 = 2774741) B2774741
theorem B5929453 : Blo 1849626 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B1849843 : Blo 1849626 1849843 := bstep (se 1 (by rfl) ⟨1387382, by rfl⟩ : syracuseStep 1849843 = 2774765) B2774765
theorem B2775539 : Blo 1849626 2775539 := bstep (se 1 (by rfl) ⟨2081654, by rfl⟩ : syracuseStep 2775539 = 4163309) B4163309
theorem B1849859 : Blo 1849626 1849859 := bstep (se 1 (by rfl) ⟨1387394, by rfl⟩ : syracuseStep 1849859 = 2774789) B2774789
theorem B2775569 : Blo 1849626 2775569 := bstep (se 2 (by rfl) ⟨1040838, by rfl⟩ : syracuseStep 2775569 = 2081677) B2081677
theorem B1849875 : Blo 1849626 1849875 := bstep (se 1 (by rfl) ⟨1387406, by rfl⟩ : syracuseStep 1849875 = 2774813) B2774813
theorem B1849891 : Blo 1849626 1849891 := bstep (se 1 (by rfl) ⟨1387418, by rfl⟩ : syracuseStep 1849891 = 2774837) B2774837
theorem B2775587 : Blo 1849626 2775587 := bstep (se 1 (by rfl) ⟨2081690, by rfl⟩ : syracuseStep 2775587 = 4163381) B4163381
theorem B8895025 : Blo 1849626 8895025 := bstep (se 2 (by rfl) ⟨3335634, by rfl⟩ : syracuseStep 8895025 = 6671269) B6671269
theorem B1849907 : Blo 1849626 1849907 := bstep (se 1 (by rfl) ⟨1387430, by rfl⟩ : syracuseStep 1849907 = 2774861) B2774861
theorem B2775617 : Blo 1849626 2775617 := bstep (se 2 (by rfl) ⟨1040856, by rfl⟩ : syracuseStep 2775617 = 2081713) B2081713
theorem B1849923 : Blo 1849626 1849923 := bstep (se 1 (by rfl) ⟨1387442, by rfl⟩ : syracuseStep 1849923 = 2774885) B2774885
theorem B3512899 : Blo 1849626 3512899 := bstep (se 1 (by rfl) ⟨2634674, by rfl⟩ : syracuseStep 3512899 = 5269349) B5269349
theorem B2964035 : Blo 1849626 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B6249041 : Blo 1849626 6249041 := bstep (se 2 (by rfl) ⟨2343390, by rfl⟩ : syracuseStep 6249041 = 4686781) B4686781
theorem B1849939 : Blo 1849626 1849939 := bstep (se 1 (by rfl) ⟨1387454, by rfl⟩ : syracuseStep 1849939 = 2774909) B2774909
theorem B2775635 : Blo 1849626 2775635 := bstep (se 1 (by rfl) ⟨2081726, by rfl⟩ : syracuseStep 2775635 = 4163453) B4163453
theorem B1849955 : Blo 1849626 1849955 := bstep (se 1 (by rfl) ⟨1387466, by rfl⟩ : syracuseStep 1849955 = 2774933) B2774933
theorem B3512945 : Blo 1849626 3512945 := bstep (se 2 (by rfl) ⟨1317354, by rfl⟩ : syracuseStep 3512945 = 2634709) B2634709
theorem B2775665 : Blo 1849626 2775665 := bstep (se 2 (by rfl) ⟨1040874, by rfl⟩ : syracuseStep 2775665 = 2081749) B2081749
theorem B1849971 : Blo 1849626 1849971 := bstep (se 1 (by rfl) ⟨1387478, by rfl⟩ : syracuseStep 1849971 = 2774957) B2774957
theorem B1849987 : Blo 1849626 1849987 := bstep (se 1 (by rfl) ⟨1387490, by rfl⟩ : syracuseStep 1849987 = 2774981) B2774981
theorem B2775683 : Blo 1849626 2775683 := bstep (se 1 (by rfl) ⟨2081762, by rfl⟩ : syracuseStep 2775683 = 4163525) B4163525
theorem B1850003 : Blo 1849626 1850003 := bstep (se 1 (by rfl) ⟨1387502, by rfl⟩ : syracuseStep 1850003 = 2775005) B2775005
theorem B2775713 : Blo 1849626 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B1850019 : Blo 1849626 1850019 := bstep (se 1 (by rfl) ⟨1387514, by rfl⟩ : syracuseStep 1850019 = 2775029) B2775029
theorem B1850035 : Blo 1849626 1850035 := bstep (se 1 (by rfl) ⟨1387526, by rfl⟩ : syracuseStep 1850035 = 2775053) B2775053
theorem B2775731 : Blo 1849626 2775731 := bstep (se 1 (by rfl) ⟨2081798, by rfl⟩ : syracuseStep 2775731 = 4163597) B4163597
theorem B1850051 : Blo 1849626 1850051 := bstep (se 1 (by rfl) ⟨1387538, by rfl⟩ : syracuseStep 1850051 = 2775077) B2775077
theorem B2775761 : Blo 1849626 2775761 := bstep (se 2 (by rfl) ⟨1040910, by rfl⟩ : syracuseStep 2775761 = 2081821) B2081821
theorem B1850067 : Blo 1849626 1850067 := bstep (se 1 (by rfl) ⟨1387550, by rfl⟩ : syracuseStep 1850067 = 2775101) B2775101
theorem B1850083 : Blo 1849626 1850083 := bstep (se 1 (by rfl) ⟨1387562, by rfl⟩ : syracuseStep 1850083 = 2775125) B2775125
theorem B2775779 : Blo 1849626 2775779 := bstep (se 1 (by rfl) ⟨2081834, by rfl⟩ : syracuseStep 2775779 = 4163669) B4163669
theorem B23714531 : Blo 1849626 23714531 := bstep (se 1 (by rfl) ⟨17785898, by rfl⟩ : syracuseStep 23714531 = 35571797) B35571797
theorem B1850099 : Blo 1849626 1850099 := bstep (se 1 (by rfl) ⟨1387574, by rfl⟩ : syracuseStep 1850099 = 2775149) B2775149
theorem B2775809 : Blo 1849626 2775809 := bstep (se 2 (by rfl) ⟨1040928, by rfl⟩ : syracuseStep 2775809 = 2081857) B2081857
theorem B1850115 : Blo 1849626 1850115 := bstep (se 1 (by rfl) ⟨1387586, by rfl⟩ : syracuseStep 1850115 = 2775173) B2775173
theorem B7027469 : Blo 1849626 7027469 := bstep (se 3 (by rfl) ⟨1317650, by rfl⟩ : syracuseStep 7027469 = 2635301) B2635301
theorem B1850131 : Blo 1849626 1850131 := bstep (se 1 (by rfl) ⟨1387598, by rfl⟩ : syracuseStep 1850131 = 2775197) B2775197
theorem B2775827 : Blo 1849626 2775827 := bstep (se 1 (by rfl) ⟨2081870, by rfl⟩ : syracuseStep 2775827 = 4163741) B4163741
theorem B1850147 : Blo 1849626 1850147 := bstep (se 1 (by rfl) ⟨1387610, by rfl⟩ : syracuseStep 1850147 = 2775221) B2775221
theorem B9370403 : Blo 1849626 9370403 := bstep (se 1 (by rfl) ⟨7027802, by rfl⟩ : syracuseStep 9370403 = 14055605) B14055605
theorem B2775857 : Blo 1849626 2775857 := bstep (se 2 (by rfl) ⟨1040946, by rfl⟩ : syracuseStep 2775857 = 2081893) B2081893
theorem B1850163 : Blo 1849626 1850163 := bstep (se 1 (by rfl) ⟨1387622, by rfl⟩ : syracuseStep 1850163 = 2775245) B2775245
theorem B1850179 : Blo 1849626 1850179 := bstep (se 1 (by rfl) ⟨1387634, by rfl⟩ : syracuseStep 1850179 = 2775269) B2775269
theorem B2775875 : Blo 1849626 2775875 := bstep (se 1 (by rfl) ⟨2081906, by rfl⟩ : syracuseStep 2775875 = 4163813) B4163813
theorem B4684625 : Blo 1849626 4684625 := bstep (se 2 (by rfl) ⟨1756734, by rfl⟩ : syracuseStep 4684625 = 3513469) B3513469
theorem B1850195 : Blo 1849626 1850195 := bstep (se 1 (by rfl) ⟨1387646, by rfl⟩ : syracuseStep 1850195 = 2775293) B2775293
theorem B2775905 : Blo 1849626 2775905 := bstep (se 2 (by rfl) ⟨1040964, by rfl⟩ : syracuseStep 2775905 = 2081929) B2081929
theorem B1850211 : Blo 1849626 1850211 := bstep (se 1 (by rfl) ⟨1387658, by rfl⟩ : syracuseStep 1850211 = 2775317) B2775317
theorem B1850227 : Blo 1849626 1850227 := bstep (se 1 (by rfl) ⟨1387670, by rfl⟩ : syracuseStep 1850227 = 2775341) B2775341
theorem B2775923 : Blo 1849626 2775923 := bstep (se 1 (by rfl) ⟨2081942, by rfl⟩ : syracuseStep 2775923 = 4163885) B4163885
theorem B1850243 : Blo 1849626 1850243 := bstep (se 1 (by rfl) ⟨1387682, by rfl⟩ : syracuseStep 1850243 = 2775365) B2775365
theorem B4684675 : Blo 1849626 4684675 := bstep (se 1 (by rfl) ⟨3513506, by rfl⟩ : syracuseStep 4684675 = 7027013) B7027013
theorem B3513233 : Blo 1849626 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B2775953 : Blo 1849626 2775953 := bstep (se 2 (by rfl) ⟨1040982, by rfl⟩ : syracuseStep 2775953 = 2081965) B2081965
theorem B1850259 : Blo 1849626 1850259 := bstep (se 1 (by rfl) ⟨1387694, by rfl⟩ : syracuseStep 1850259 = 2775389) B2775389
theorem B1850275 : Blo 1849626 1850275 := bstep (se 1 (by rfl) ⟨1387706, by rfl⟩ : syracuseStep 1850275 = 2775413) B2775413
theorem B2775971 : Blo 1849626 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B1850291 : Blo 1849626 1850291 := bstep (se 1 (by rfl) ⟨1387718, by rfl⟩ : syracuseStep 1850291 = 2775437) B2775437
theorem B2341811 : Blo 1849626 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B2776001 : Blo 1849626 2776001 := bstep (se 2 (by rfl) ⟨1041000, by rfl⟩ : syracuseStep 2776001 = 2082001) B2082001
theorem B1850307 : Blo 1849626 1850307 := bstep (se 1 (by rfl) ⟨1387730, by rfl⟩ : syracuseStep 1850307 = 2775461) B2775461
theorem B1850323 : Blo 1849626 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B2776019 : Blo 1849626 2776019 := bstep (se 1 (by rfl) ⟨2082014, by rfl⟩ : syracuseStep 2776019 = 4164029) B4164029
theorem B3333091 : Blo 1849626 3333091 := bstep (se 1 (by rfl) ⟨2499818, by rfl⟩ : syracuseStep 3333091 = 4999637) B4999637
theorem B1850339 : Blo 1849626 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B2776049 : Blo 1849626 2776049 := bstep (se 2 (by rfl) ⟨1041018, by rfl⟩ : syracuseStep 2776049 = 2082037) B2082037
theorem B1850355 : Blo 1849626 1850355 := bstep (se 1 (by rfl) ⟨1387766, by rfl⟩ : syracuseStep 1850355 = 2775533) B2775533
theorem B1850371 : Blo 1849626 1850371 := bstep (se 1 (by rfl) ⟨1387778, by rfl⟩ : syracuseStep 1850371 = 2775557) B2775557
theorem B2776067 : Blo 1849626 2776067 := bstep (se 1 (by rfl) ⟨2082050, by rfl⟩ : syracuseStep 2776067 = 4164101) B4164101
theorem B4684817 : Blo 1849626 4684817 := bstep (se 2 (by rfl) ⟨1756806, by rfl⟩ : syracuseStep 4684817 = 3513613) B3513613
theorem B1850387 : Blo 1849626 1850387 := bstep (se 1 (by rfl) ⟨1387790, by rfl⟩ : syracuseStep 1850387 = 2775581) B2775581
theorem B2776097 : Blo 1849626 2776097 := bstep (se 2 (by rfl) ⟨1041036, by rfl⟩ : syracuseStep 2776097 = 2082073) B2082073
theorem B3333155 : Blo 1849626 3333155 := bstep (se 1 (by rfl) ⟨2499866, by rfl⟩ : syracuseStep 3333155 = 4999733) B4999733
theorem B1850403 : Blo 1849626 1850403 := bstep (se 1 (by rfl) ⟨1387802, by rfl⟩ : syracuseStep 1850403 = 2775605) B2775605
theorem B1850419 : Blo 1849626 1850419 := bstep (se 1 (by rfl) ⟨1387814, by rfl⟩ : syracuseStep 1850419 = 2775629) B2775629
theorem B2776115 : Blo 1849626 2776115 := bstep (se 1 (by rfl) ⟨2082086, by rfl⟩ : syracuseStep 2776115 = 4164173) B4164173
theorem B5340227 : Blo 1849626 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B1850435 : Blo 1849626 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B2964547 : Blo 1849626 2964547 := bstep (se 1 (by rfl) ⟨2223410, by rfl⟩ : syracuseStep 2964547 = 4446821) B4446821
theorem B2776145 : Blo 1849626 2776145 := bstep (se 2 (by rfl) ⟨1041054, by rfl⟩ : syracuseStep 2776145 = 2082109) B2082109
theorem B1850451 : Blo 1849626 1850451 := bstep (se 1 (by rfl) ⟨1387838, by rfl⟩ : syracuseStep 1850451 = 2775677) B2775677
theorem B1850467 : Blo 1849626 1850467 := bstep (se 1 (by rfl) ⟨1387850, by rfl⟩ : syracuseStep 1850467 = 2775701) B2775701
theorem B2776163 : Blo 1849626 2776163 := bstep (se 1 (by rfl) ⟨2082122, by rfl⟩ : syracuseStep 2776163 = 4164245) B4164245
theorem B40000625 : Blo 1849626 40000625 := bstep (se 2 (by rfl) ⟨15000234, by rfl⟩ : syracuseStep 40000625 = 30000469) B30000469
theorem B2964593 : Blo 1849626 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B1850483 : Blo 1849626 1850483 := bstep (se 1 (by rfl) ⟨1387862, by rfl⟩ : syracuseStep 1850483 = 2775725) B2775725
theorem B2776193 : Blo 1849626 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B1850499 : Blo 1849626 1850499 := bstep (se 1 (by rfl) ⟨1387874, by rfl⟩ : syracuseStep 1850499 = 2775749) B2775749
theorem B16882829 : Blo 1849626 16882829 := bstep (se 3 (by rfl) ⟨3165530, by rfl⟩ : syracuseStep 16882829 = 6331061) B6331061
theorem B1850515 : Blo 1849626 1850515 := bstep (se 1 (by rfl) ⟨1387886, by rfl⟩ : syracuseStep 1850515 = 2775773) B2775773
theorem B2776211 : Blo 1849626 2776211 := bstep (se 1 (by rfl) ⟨2082158, by rfl⟩ : syracuseStep 2776211 = 4164317) B4164317
theorem B1850531 : Blo 1849626 1850531 := bstep (se 1 (by rfl) ⟨1387898, by rfl⟩ : syracuseStep 1850531 = 2775797) B2775797
theorem B2776241 : Blo 1849626 2776241 := bstep (se 2 (by rfl) ⟨1041090, by rfl⟩ : syracuseStep 2776241 = 2082181) B2082181
theorem B3005617 : Blo 1849626 3005617 := bstep (se 2 (by rfl) ⟨1127106, by rfl⟩ : syracuseStep 3005617 = 2254213) B2254213
theorem B1850547 : Blo 1849626 1850547 := bstep (se 1 (by rfl) ⟨1387910, by rfl⟩ : syracuseStep 1850547 = 2775821) B2775821
theorem B1850563 : Blo 1849626 1850563 := bstep (se 1 (by rfl) ⟨1387922, by rfl⟩ : syracuseStep 1850563 = 2775845) B2775845
theorem B2776259 : Blo 1849626 2776259 := bstep (se 1 (by rfl) ⟨2082194, by rfl⟩ : syracuseStep 2776259 = 4164389) B4164389
theorem B3562705 : Blo 1849626 3562705 := bstep (se 2 (by rfl) ⟨1336014, by rfl⟩ : syracuseStep 3562705 = 2672029) B2672029
theorem B1850579 : Blo 1849626 1850579 := bstep (se 1 (by rfl) ⟨1387934, by rfl⟩ : syracuseStep 1850579 = 2775869) B2775869
theorem B2776289 : Blo 1849626 2776289 := bstep (se 2 (by rfl) ⟨1041108, by rfl⟩ : syracuseStep 2776289 = 2082217) B2082217
theorem B1850595 : Blo 1849626 1850595 := bstep (se 1 (by rfl) ⟨1387946, by rfl⟩ : syracuseStep 1850595 = 2775893) B2775893
theorem B1850611 : Blo 1849626 1850611 := bstep (se 1 (by rfl) ⟨1387958, by rfl⟩ : syracuseStep 1850611 = 2775917) B2775917
theorem B2776307 : Blo 1849626 2776307 := bstep (se 1 (by rfl) ⟨2082230, by rfl⟩ : syracuseStep 2776307 = 4164461) B4164461
theorem B1850627 : Blo 1849626 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B2776337 : Blo 1849626 2776337 := bstep (se 2 (by rfl) ⟨1041126, by rfl⟩ : syracuseStep 2776337 = 2082253) B2082253
theorem B1850643 : Blo 1849626 1850643 := bstep (se 1 (by rfl) ⟨1387982, by rfl⟩ : syracuseStep 1850643 = 2775965) B2775965
theorem B1850659 : Blo 1849626 1850659 := bstep (se 1 (by rfl) ⟨1387994, by rfl⟩ : syracuseStep 1850659 = 2775989) B2775989
theorem B2776355 : Blo 1849626 2776355 := bstep (se 1 (by rfl) ⟨2082266, by rfl⟩ : syracuseStep 2776355 = 4164533) B4164533
theorem B1850675 : Blo 1849626 1850675 := bstep (se 1 (by rfl) ⟨1388006, by rfl⟩ : syracuseStep 1850675 = 2776013) B2776013
theorem B2776385 : Blo 1849626 2776385 := bstep (se 2 (by rfl) ⟨1041144, by rfl⟩ : syracuseStep 2776385 = 2082289) B2082289
theorem B1850691 : Blo 1849626 1850691 := bstep (se 1 (by rfl) ⟨1388018, by rfl⟩ : syracuseStep 1850691 = 2776037) B2776037
theorem B6331729 : Blo 1849626 6331729 := bstep (se 2 (by rfl) ⟨2374398, by rfl⟩ : syracuseStep 6331729 = 4748797) B4748797
theorem B1850707 : Blo 1849626 1850707 := bstep (se 1 (by rfl) ⟨1388030, by rfl⟩ : syracuseStep 1850707 = 2776061) B2776061
theorem B2776403 : Blo 1849626 2776403 := bstep (se 1 (by rfl) ⟨2082302, by rfl⟩ : syracuseStep 2776403 = 4164605) B4164605
theorem B1850723 : Blo 1849626 1850723 := bstep (se 1 (by rfl) ⟨1388042, by rfl⟩ : syracuseStep 1850723 = 2776085) B2776085
theorem B2776433 : Blo 1849626 2776433 := bstep (se 2 (by rfl) ⟨1041162, by rfl⟩ : syracuseStep 2776433 = 2082325) B2082325
theorem B1850739 : Blo 1849626 1850739 := bstep (se 1 (by rfl) ⟨1388054, by rfl⟩ : syracuseStep 1850739 = 2776109) B2776109
theorem B1850755 : Blo 1849626 1850755 := bstep (se 1 (by rfl) ⟨1388066, by rfl⟩ : syracuseStep 1850755 = 2776133) B2776133
theorem B2776451 : Blo 1849626 2776451 := bstep (se 1 (by rfl) ⟨2082338, by rfl⟩ : syracuseStep 2776451 = 4164677) B4164677
theorem B1850771 : Blo 1849626 1850771 := bstep (se 1 (by rfl) ⟨1388078, by rfl⟩ : syracuseStep 1850771 = 2776157) B2776157
theorem B2776481 : Blo 1849626 2776481 := bstep (se 2 (by rfl) ⟨1041180, by rfl⟩ : syracuseStep 2776481 = 2082361) B2082361
theorem B1850787 : Blo 1849626 1850787 := bstep (se 1 (by rfl) ⟨1388090, by rfl⟩ : syracuseStep 1850787 = 2776181) B2776181
theorem B1850803 : Blo 1849626 1850803 := bstep (se 1 (by rfl) ⟨1388102, by rfl⟩ : syracuseStep 1850803 = 2776205) B2776205
theorem B2776499 : Blo 1849626 2776499 := bstep (se 1 (by rfl) ⟨2082374, by rfl⟩ : syracuseStep 2776499 = 4164749) B4164749
theorem B1850819 : Blo 1849626 1850819 := bstep (se 1 (by rfl) ⟨1388114, by rfl⟩ : syracuseStep 1850819 = 2776229) B2776229
theorem B11255237 : Blo 1849626 11255237 := bstep (se 4 (by rfl) ⟨1055178, by rfl⟩ : syracuseStep 11255237 = 2110357) B2110357
theorem B2776529 : Blo 1849626 2776529 := bstep (se 2 (by rfl) ⟨1041198, by rfl⟩ : syracuseStep 2776529 = 2082397) B2082397
theorem B1850835 : Blo 1849626 1850835 := bstep (se 1 (by rfl) ⟨1388126, by rfl⟩ : syracuseStep 1850835 = 2776253) B2776253
theorem B1850851 : Blo 1849626 1850851 := bstep (se 1 (by rfl) ⟨1388138, by rfl⟩ : syracuseStep 1850851 = 2776277) B2776277
theorem B2776547 : Blo 1849626 2776547 := bstep (se 1 (by rfl) ⟨2082410, by rfl⟩ : syracuseStep 2776547 = 4164821) B4164821
theorem B1850867 : Blo 1849626 1850867 := bstep (se 1 (by rfl) ⟨1388150, by rfl⟩ : syracuseStep 1850867 = 2776301) B2776301
theorem B2776577 : Blo 1849626 2776577 := bstep (se 2 (by rfl) ⟨1041216, by rfl⟩ : syracuseStep 2776577 = 2082433) B2082433
theorem B1850883 : Blo 1849626 1850883 := bstep (se 1 (by rfl) ⟨1388162, by rfl⟩ : syracuseStep 1850883 = 2776325) B2776325
theorem B1850899 : Blo 1849626 1850899 := bstep (se 1 (by rfl) ⟨1388174, by rfl⟩ : syracuseStep 1850899 = 2776349) B2776349
theorem B2776595 : Blo 1849626 2776595 := bstep (se 1 (by rfl) ⟨2082446, by rfl⟩ : syracuseStep 2776595 = 4164893) B4164893
theorem B1850915 : Blo 1849626 1850915 := bstep (se 1 (by rfl) ⟨1388186, by rfl⟩ : syracuseStep 1850915 = 2776373) B2776373
theorem B2776625 : Blo 1849626 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B1850931 : Blo 1849626 1850931 := bstep (se 1 (by rfl) ⟨1388198, by rfl⟩ : syracuseStep 1850931 = 2776397) B2776397
theorem B1850947 : Blo 1849626 1850947 := bstep (se 1 (by rfl) ⟨1388210, by rfl⟩ : syracuseStep 1850947 = 2776421) B2776421
theorem B2776643 : Blo 1849626 2776643 := bstep (se 1 (by rfl) ⟨2082482, by rfl⟩ : syracuseStep 2776643 = 4164965) B4164965
theorem B9371213 : Blo 1849626 9371213 := bstep (se 3 (by rfl) ⟨1757102, by rfl⟩ : syracuseStep 9371213 = 3514205) B3514205
theorem B1850963 : Blo 1849626 1850963 := bstep (se 1 (by rfl) ⟨1388222, by rfl⟩ : syracuseStep 1850963 = 2776445) B2776445
theorem B2776673 : Blo 1849626 2776673 := bstep (se 2 (by rfl) ⟨1041252, by rfl⟩ : syracuseStep 2776673 = 2082505) B2082505
theorem B3513955 : Blo 1849626 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1850979 : Blo 1849626 1850979 := bstep (se 1 (by rfl) ⟨1388234, by rfl⟩ : syracuseStep 1850979 = 2776469) B2776469
theorem B2342515 : Blo 1849626 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B1850995 : Blo 1849626 1850995 := bstep (se 1 (by rfl) ⟨1388246, by rfl⟩ : syracuseStep 1850995 = 2776493) B2776493
theorem B2776691 : Blo 1849626 2776691 := bstep (se 1 (by rfl) ⟨2082518, by rfl⟩ : syracuseStep 2776691 = 4165037) B4165037
theorem B1851011 : Blo 1849626 1851011 := bstep (se 1 (by rfl) ⟨1388258, by rfl⟩ : syracuseStep 1851011 = 2776517) B2776517
theorem B2776721 : Blo 1849626 2776721 := bstep (se 2 (by rfl) ⟨1041270, by rfl⟩ : syracuseStep 2776721 = 2082541) B2082541
theorem B1851027 : Blo 1849626 1851027 := bstep (se 1 (by rfl) ⟨1388270, by rfl⟩ : syracuseStep 1851027 = 2776541) B2776541
theorem B1851043 : Blo 1849626 1851043 := bstep (se 1 (by rfl) ⟨1388282, by rfl⟩ : syracuseStep 1851043 = 2776565) B2776565
theorem B2776739 : Blo 1849626 2776739 := bstep (se 1 (by rfl) ⟨2082554, by rfl⟩ : syracuseStep 2776739 = 4165109) B4165109
theorem B1851059 : Blo 1849626 1851059 := bstep (se 1 (by rfl) ⟨1388294, by rfl⟩ : syracuseStep 1851059 = 2776589) B2776589
theorem B2776769 : Blo 1849626 2776769 := bstep (se 2 (by rfl) ⟨1041288, by rfl⟩ : syracuseStep 2776769 = 2082577) B2082577
theorem B1851075 : Blo 1849626 1851075 := bstep (se 1 (by rfl) ⟨1388306, by rfl⟩ : syracuseStep 1851075 = 2776613) B2776613
theorem B2342611 : Blo 1849626 2342611 := bstep (se 1 (by rfl) ⟨1756958, by rfl⟩ : syracuseStep 2342611 = 3513917) B3513917
theorem B1851091 : Blo 1849626 1851091 := bstep (se 1 (by rfl) ⟨1388318, by rfl⟩ : syracuseStep 1851091 = 2776637) B2776637
theorem B2776787 : Blo 1849626 2776787 := bstep (se 1 (by rfl) ⟨2082590, by rfl⟩ : syracuseStep 2776787 = 4165181) B4165181
theorem B1851107 : Blo 1849626 1851107 := bstep (se 1 (by rfl) ⟨1388330, by rfl⟩ : syracuseStep 1851107 = 2776661) B2776661
theorem B2776817 : Blo 1849626 2776817 := bstep (se 2 (by rfl) ⟨1041306, by rfl⟩ : syracuseStep 2776817 = 2082613) B2082613
theorem B1851123 : Blo 1849626 1851123 := bstep (se 1 (by rfl) ⟨1388342, by rfl⟩ : syracuseStep 1851123 = 2776685) B2776685
theorem B1851139 : Blo 1849626 1851139 := bstep (se 1 (by rfl) ⟨1388354, by rfl⟩ : syracuseStep 1851139 = 2776709) B2776709
theorem B2776835 : Blo 1849626 2776835 := bstep (se 1 (by rfl) ⟨2082626, by rfl⟩ : syracuseStep 2776835 = 4165253) B4165253
theorem B2965265 : Blo 1849626 2965265 := bstep (se 2 (by rfl) ⟨1111974, by rfl⟩ : syracuseStep 2965265 = 2223949) B2223949
theorem B1851155 : Blo 1849626 1851155 := bstep (se 1 (by rfl) ⟨1388366, by rfl⟩ : syracuseStep 1851155 = 2776733) B2776733
theorem B2776865 : Blo 1849626 2776865 := bstep (se 2 (by rfl) ⟨1041324, by rfl⟩ : syracuseStep 2776865 = 2082649) B2082649
theorem B1851171 : Blo 1849626 1851171 := bstep (se 1 (by rfl) ⟨1388378, by rfl⟩ : syracuseStep 1851171 = 2776757) B2776757
theorem B1851187 : Blo 1849626 1851187 := bstep (se 1 (by rfl) ⟨1388390, by rfl⟩ : syracuseStep 1851187 = 2776781) B2776781
theorem B2776883 : Blo 1849626 2776883 := bstep (se 1 (by rfl) ⟨2082662, by rfl⟩ : syracuseStep 2776883 = 4165325) B4165325
theorem B1851203 : Blo 1849626 1851203 := bstep (se 1 (by rfl) ⟨1388402, by rfl⟩ : syracuseStep 1851203 = 2776805) B2776805
theorem B2776913 : Blo 1849626 2776913 := bstep (se 2 (by rfl) ⟨1041342, by rfl⟩ : syracuseStep 2776913 = 2082685) B2082685
theorem B1851219 : Blo 1849626 1851219 := bstep (se 1 (by rfl) ⟨1388414, by rfl⟩ : syracuseStep 1851219 = 2776829) B2776829
theorem B1851235 : Blo 1849626 1851235 := bstep (se 1 (by rfl) ⟨1388426, by rfl⟩ : syracuseStep 1851235 = 2776853) B2776853
theorem B2776931 : Blo 1849626 2776931 := bstep (se 1 (by rfl) ⟨2082698, by rfl⟩ : syracuseStep 2776931 = 4165397) B4165397
theorem B1851251 : Blo 1849626 1851251 := bstep (se 1 (by rfl) ⟨1388438, by rfl⟩ : syracuseStep 1851251 = 2776877) B2776877
theorem B2776961 : Blo 1849626 2776961 := bstep (se 2 (by rfl) ⟨1041360, by rfl⟩ : syracuseStep 2776961 = 2082721) B2082721
theorem B1851267 : Blo 1849626 1851267 := bstep (se 1 (by rfl) ⟨1388450, by rfl⟩ : syracuseStep 1851267 = 2776901) B2776901
theorem B1851283 : Blo 1849626 1851283 := bstep (se 1 (by rfl) ⟨1388462, by rfl⟩ : syracuseStep 1851283 = 2776925) B2776925
theorem B2776979 : Blo 1849626 2776979 := bstep (se 1 (by rfl) ⟨2082734, by rfl⟩ : syracuseStep 2776979 = 4165469) B4165469
theorem B1851299 : Blo 1849626 1851299 := bstep (se 1 (by rfl) ⟨1388474, by rfl⟩ : syracuseStep 1851299 = 2776949) B2776949
theorem B2777009 : Blo 1849626 2777009 := bstep (se 2 (by rfl) ⟨1041378, by rfl⟩ : syracuseStep 2777009 = 2082757) B2082757
theorem B1851315 : Blo 1849626 1851315 := bstep (se 1 (by rfl) ⟨1388486, by rfl⟩ : syracuseStep 1851315 = 2776973) B2776973
theorem B1851331 : Blo 1849626 1851331 := bstep (se 1 (by rfl) ⟨1388498, by rfl⟩ : syracuseStep 1851331 = 2776997) B2776997
theorem B2777027 : Blo 1849626 2777027 := bstep (se 1 (by rfl) ⟨2082770, by rfl⟩ : syracuseStep 2777027 = 4165541) B4165541
theorem B1851347 : Blo 1849626 1851347 := bstep (se 1 (by rfl) ⟨1388510, by rfl⟩ : syracuseStep 1851347 = 2777021) B2777021
theorem B2777057 : Blo 1849626 2777057 := bstep (se 2 (by rfl) ⟨1041396, by rfl⟩ : syracuseStep 2777057 = 2082793) B2082793
theorem B1851363 : Blo 1849626 1851363 := bstep (se 1 (by rfl) ⟨1388522, by rfl⟩ : syracuseStep 1851363 = 2777045) B2777045
theorem B4685809 : Blo 1849626 4685809 := bstep (se 2 (by rfl) ⟨1757178, by rfl⟩ : syracuseStep 4685809 = 3514357) B3514357
theorem B1851379 : Blo 1849626 1851379 := bstep (se 1 (by rfl) ⟨1388534, by rfl⟩ : syracuseStep 1851379 = 2777069) B2777069
theorem B2777075 : Blo 1849626 2777075 := bstep (se 1 (by rfl) ⟨2082806, by rfl⟩ : syracuseStep 2777075 = 4165613) B4165613
theorem B2777099 : Blo 1849626 2777099 := bstep (se 1 (by rfl) ⟨2082824, by rfl⟩ : syracuseStep 2777099 = 4165649) B4165649
theorem B1851403 : Blo 1849626 1851403 := bstep (se 1 (by rfl) ⟨1388552, by rfl⟩ : syracuseStep 1851403 = 2777105) B2777105
theorem B2342935 : Blo 1849626 2342935 := bstep (se 1 (by rfl) ⟨1757201, by rfl⟩ : syracuseStep 2342935 = 3514403) B3514403
theorem B2777111 : Blo 1849626 2777111 := bstep (se 1 (by rfl) ⟨2082833, by rfl⟩ : syracuseStep 2777111 = 4165667) B4165667
theorem B1851415 : Blo 1849626 1851415 := bstep (se 1 (by rfl) ⟨1388561, by rfl⟩ : syracuseStep 1851415 = 2777123) B2777123
theorem B1851435 : Blo 1849626 1851435 := bstep (se 1 (by rfl) ⟨1388576, by rfl⟩ : syracuseStep 1851435 = 2777153) B2777153
theorem B1851447 : Blo 1849626 1851447 := bstep (se 1 (by rfl) ⟨1388585, by rfl⟩ : syracuseStep 1851447 = 2777171) B2777171
theorem B4448321 : Blo 1849626 4448321 := bstep (se 2 (by rfl) ⟨1668120, by rfl⟩ : syracuseStep 4448321 = 3336241) B3336241
theorem B1851467 : Blo 1849626 1851467 := bstep (se 1 (by rfl) ⟨1388600, by rfl⟩ : syracuseStep 1851467 = 2777201) B2777201
theorem B1851479 : Blo 1849626 1851479 := bstep (se 1 (by rfl) ⟨1388609, by rfl⟩ : syracuseStep 1851479 = 2777219) B2777219
theorem B2777177 : Blo 1849626 2777177 := bstep (se 2 (by rfl) ⟨1041441, by rfl⟩ : syracuseStep 2777177 = 2082883) B2082883
theorem B8888413 : Blo 1849626 8888413 := bstep (se 3 (by rfl) ⟨1666577, by rfl⟩ : syracuseStep 8888413 = 3333155) B3333155
theorem B8437853 : Blo 1849626 8437853 := bstep (se 3 (by rfl) ⟨1582097, by rfl⟩ : syracuseStep 8437853 = 3164195) B3164195
theorem B1851499 : Blo 1849626 1851499 := bstep (se 1 (by rfl) ⟨1388624, by rfl⟩ : syracuseStep 1851499 = 2777249) B2777249
theorem B1851511 : Blo 1849626 1851511 := bstep (se 1 (by rfl) ⟨1388633, by rfl⟩ : syracuseStep 1851511 = 2777267) B2777267
theorem B1851531 : Blo 1849626 1851531 := bstep (se 1 (by rfl) ⟨1388648, by rfl⟩ : syracuseStep 1851531 = 2777297) B2777297
theorem B1851543 : Blo 1849626 1851543 := bstep (se 1 (by rfl) ⟨1388657, by rfl⟩ : syracuseStep 1851543 = 2777315) B2777315
theorem B4161689 : Blo 1849626 4161689 := bstep (se 2 (by rfl) ⟨1560633, by rfl⟩ : syracuseStep 4161689 = 3121267) B3121267
theorem B2080939 : Blo 1849626 2080939 := bstep (se 1 (by rfl) ⟨1560704, by rfl⟩ : syracuseStep 2080939 = 3121409) B3121409
theorem B1851563 : Blo 1849626 1851563 := bstep (se 1 (by rfl) ⟨1388672, by rfl⟩ : syracuseStep 1851563 = 2777345) B2777345
theorem B1851575 : Blo 1849626 1851575 := bstep (se 1 (by rfl) ⟨1388681, by rfl⟩ : syracuseStep 1851575 = 2777363) B2777363
theorem B6242507 : Blo 1849626 6242507 := bstep (se 1 (by rfl) ⟨4681880, by rfl⟩ : syracuseStep 6242507 = 9363761) B9363761
theorem B3121355 : Blo 1849626 3121355 := bstep (se 1 (by rfl) ⟨2341016, by rfl⟩ : syracuseStep 3121355 = 4682033) B4682033
theorem B2777291 : Blo 1849626 2777291 := bstep (se 1 (by rfl) ⟨2082968, by rfl⟩ : syracuseStep 2777291 = 4165937) B4165937
theorem B1851595 : Blo 1849626 1851595 := bstep (se 1 (by rfl) ⟨1388696, by rfl⟩ : syracuseStep 1851595 = 2777393) B2777393
theorem B2777303 : Blo 1849626 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B1851607 : Blo 1849626 1851607 := bstep (se 1 (by rfl) ⟨1388705, by rfl⟩ : syracuseStep 1851607 = 2777411) B2777411
theorem B3514585 : Blo 1849626 3514585 := bstep (se 2 (by rfl) ⟨1317969, by rfl⟩ : syracuseStep 3514585 = 2635939) B2635939
theorem B7028957 : Blo 1849626 7028957 := bstep (se 3 (by rfl) ⟨1317929, by rfl⟩ : syracuseStep 7028957 = 2635859) B2635859
theorem B4161779 : Blo 1849626 4161779 := bstep (se 1 (by rfl) ⟨3121334, by rfl⟩ : syracuseStep 4161779 = 6242669) B6242669
theorem B4161815 : Blo 1849626 4161815 := bstep (se 1 (by rfl) ⟨3121361, by rfl⟩ : syracuseStep 4161815 = 6242723) B6242723
theorem B2081047 : Blo 1849626 2081047 := bstep (se 1 (by rfl) ⟨1560785, by rfl⟩ : syracuseStep 2081047 = 3121571) B3121571
theorem B2777369 : Blo 1849626 2777369 := bstep (se 2 (by rfl) ⟨1041513, by rfl⟩ : syracuseStep 2777369 = 2083027) B2083027
theorem B121643309 : Blo 1849626 121643309 := bstep (se 3 (by rfl) ⟨22808120, by rfl⟩ : syracuseStep 121643309 = 45616241) B45616241
theorem B3121483 : Blo 1849626 3121483 := bstep (se 1 (by rfl) ⟨2341112, by rfl⟩ : syracuseStep 3121483 = 4682225) B4682225
theorem B3334475 : Blo 1849626 3334475 := bstep (se 1 (by rfl) ⟨2500856, by rfl⟩ : syracuseStep 3334475 = 5001713) B5001713
theorem B5267891 : Blo 1849626 5267891 := bstep (se 1 (by rfl) ⟨3950918, by rfl⟩ : syracuseStep 5267891 = 7901837) B7901837
theorem B4161995 : Blo 1849626 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B2081227 : Blo 1849626 2081227 := bstep (se 1 (by rfl) ⟨1560920, by rfl⟩ : syracuseStep 2081227 = 3121841) B3121841
theorem B3121625 : Blo 1849626 3121625 := bstep (se 2 (by rfl) ⟨1170609, by rfl⟩ : syracuseStep 3121625 = 2341219) B2341219
theorem B6242777 : Blo 1849626 6242777 := bstep (se 2 (by rfl) ⟨2341041, by rfl⟩ : syracuseStep 6242777 = 4682083) B4682083
theorem B3801587 : Blo 1849626 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B4162049 : Blo 1849626 4162049 := bstep (se 2 (by rfl) ⟨1560768, by rfl⟩ : syracuseStep 4162049 = 3121537) B3121537
theorem B2081335 : Blo 1849626 2081335 := bstep (se 1 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 2081335 = 3122003) B3122003
theorem B3121753 : Blo 1849626 3121753 := bstep (se 2 (by rfl) ⟨1170657, by rfl⟩ : syracuseStep 3121753 = 2341315) B2341315
theorem B10543709 : Blo 1849626 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B7905937 : Blo 1849626 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B4162265 : Blo 1849626 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B2081515 : Blo 1849626 2081515 := bstep (se 1 (by rfl) ⟨1561136, by rfl⟩ : syracuseStep 2081515 = 3122273) B3122273
theorem B3515147 : Blo 1849626 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B2851609 : Blo 1849626 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B4162355 : Blo 1849626 4162355 := bstep (se 1 (by rfl) ⟨3121766, by rfl⟩ : syracuseStep 4162355 = 6243533) B6243533
theorem B4162391 : Blo 1849626 4162391 := bstep (se 1 (by rfl) ⟨3121793, by rfl⟩ : syracuseStep 4162391 = 6243587) B6243587
theorem B2081623 : Blo 1849626 2081623 := bstep (se 1 (by rfl) ⟨1561217, by rfl⟩ : syracuseStep 2081623 = 3122435) B3122435
theorem B9372509 : Blo 1849626 9372509 := bstep (se 3 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 9372509 = 3514691) B3514691
theorem B15000497 : Blo 1849626 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B4162571 : Blo 1849626 4162571 := bstep (se 1 (by rfl) ⟨3121928, by rfl⟩ : syracuseStep 4162571 = 6243857) B6243857
theorem B2081803 : Blo 1849626 2081803 := bstep (se 1 (by rfl) ⟨1561352, by rfl⟩ : syracuseStep 2081803 = 3122705) B3122705
theorem B4162625 : Blo 1849626 4162625 := bstep (se 2 (by rfl) ⟨1560984, by rfl⟩ : syracuseStep 4162625 = 3121969) B3121969
theorem B4686923 : Blo 1849626 4686923 := bstep (se 1 (by rfl) ⟨3515192, by rfl⟩ : syracuseStep 4686923 = 7030385) B7030385
theorem B2081911 : Blo 1849626 2081911 := bstep (se 1 (by rfl) ⟨1561433, by rfl⟩ : syracuseStep 2081911 = 3122867) B3122867
theorem B6243479 : Blo 1849626 6243479 := bstep (se 1 (by rfl) ⟨4682609, by rfl⟩ : syracuseStep 6243479 = 9365219) B9365219
theorem B3122327 : Blo 1849626 3122327 := bstep (se 1 (by rfl) ⟨2341745, by rfl⟩ : syracuseStep 3122327 = 4683491) B4683491
theorem B13518001 : Blo 1849626 13518001 := bstep (se 2 (by rfl) ⟨5069250, by rfl⟩ : syracuseStep 13518001 = 10138501) B10138501
theorem B3122455 : Blo 1849626 3122455 := bstep (se 1 (by rfl) ⟨2341841, by rfl⟩ : syracuseStep 3122455 = 4683683) B4683683
theorem B4162841 : Blo 1849626 4162841 := bstep (se 2 (by rfl) ⟨1561065, by rfl⟩ : syracuseStep 4162841 = 3122131) B3122131
theorem B2082091 : Blo 1849626 2082091 := bstep (se 1 (by rfl) ⟨1561568, by rfl⟩ : syracuseStep 2082091 = 3123137) B3123137
theorem B4162931 : Blo 1849626 4162931 := bstep (se 1 (by rfl) ⟨3122198, by rfl⟩ : syracuseStep 4162931 = 6244397) B6244397
theorem B4162967 : Blo 1849626 4162967 := bstep (se 1 (by rfl) ⟨3122225, by rfl⟩ : syracuseStep 4162967 = 6244451) B6244451
theorem B2082199 : Blo 1849626 2082199 := bstep (se 1 (by rfl) ⟨1561649, by rfl⟩ : syracuseStep 2082199 = 3123299) B3123299
theorem B25322969 : Blo 1849626 25322969 := bstep (se 2 (by rfl) ⟨9496113, by rfl⟩ : syracuseStep 25322969 = 18992227) B18992227
theorem B9365057 : Blo 1849626 9365057 := bstep (se 2 (by rfl) ⟨3511896, by rfl⟩ : syracuseStep 9365057 = 7023793) B7023793
theorem B4007489 : Blo 1849626 4007489 := bstep (se 2 (by rfl) ⟨1502808, by rfl⟩ : syracuseStep 4007489 = 3005617) B3005617
theorem B4163147 : Blo 1849626 4163147 := bstep (se 1 (by rfl) ⟨3122360, by rfl⟩ : syracuseStep 4163147 = 6244721) B6244721
theorem B2082379 : Blo 1849626 2082379 := bstep (se 1 (by rfl) ⟨1561784, by rfl⟩ : syracuseStep 2082379 = 3123569) B3123569
theorem B4163201 : Blo 1849626 4163201 := bstep (se 2 (by rfl) ⟨1561200, by rfl⟩ : syracuseStep 4163201 = 3122401) B3122401
theorem B6244019 : Blo 1849626 6244019 := bstep (se 1 (by rfl) ⟨4683014, by rfl⟩ : syracuseStep 6244019 = 9366029) B9366029
theorem B2082487 : Blo 1849626 2082487 := bstep (se 1 (by rfl) ⟨1561865, by rfl⟩ : syracuseStep 2082487 = 3123731) B3123731
theorem B1976023 : Blo 1849626 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B6670145 : Blo 1849626 6670145 := bstep (se 2 (by rfl) ⟨2501304, by rfl⟩ : syracuseStep 6670145 = 5002609) B5002609
theorem B4163417 : Blo 1849626 4163417 := bstep (se 2 (by rfl) ⟨1561281, by rfl⟩ : syracuseStep 4163417 = 3122563) B3122563
theorem B21366629 : Blo 1849626 21366629 := bstep (se 4 (by rfl) ⟨2003121, by rfl⟩ : syracuseStep 21366629 = 4006243) B4006243
theorem B2082667 : Blo 1849626 2082667 := bstep (se 1 (by rfl) ⟨1562000, by rfl⟩ : syracuseStep 2082667 = 3124001) B3124001
theorem B3123083 : Blo 1849626 3123083 := bstep (se 1 (by rfl) ⟨2342312, by rfl⟩ : syracuseStep 3123083 = 4684625) B4684625
theorem B4163507 : Blo 1849626 4163507 := bstep (se 1 (by rfl) ⟨3122630, by rfl⟩ : syracuseStep 4163507 = 6245261) B6245261
theorem B6244289 : Blo 1849626 6244289 := bstep (se 2 (by rfl) ⟨2341608, by rfl⟩ : syracuseStep 6244289 = 4683217) B4683217
theorem B4163543 : Blo 1849626 4163543 := bstep (se 1 (by rfl) ⟨3122657, by rfl⟩ : syracuseStep 4163543 = 6245315) B6245315
theorem B2082775 : Blo 1849626 2082775 := bstep (se 1 (by rfl) ⟨1562081, by rfl⟩ : syracuseStep 2082775 = 3124163) B3124163
theorem B3950603 : Blo 1849626 3950603 := bstep (se 1 (by rfl) ⟨2962952, by rfl⟩ : syracuseStep 3950603 = 5925905) B5925905
theorem B3123211 : Blo 1849626 3123211 := bstep (se 1 (by rfl) ⟨2342408, by rfl⟩ : syracuseStep 3123211 = 4684817) B4684817
theorem B26667083 : Blo 1849626 26667083 := bstep (se 1 (by rfl) ⟨20000312, by rfl⟩ : syracuseStep 26667083 = 40000625) B40000625
theorem B1976395 : Blo 1849626 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B4163723 : Blo 1849626 4163723 := bstep (se 1 (by rfl) ⟨3122792, by rfl⟩ : syracuseStep 4163723 = 6245585) B6245585
theorem B2082955 : Blo 1849626 2082955 := bstep (se 1 (by rfl) ⟨1562216, by rfl⟩ : syracuseStep 2082955 = 3124433) B3124433
theorem B3123353 : Blo 1849626 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B4163777 : Blo 1849626 4163777 := bstep (se 2 (by rfl) ⟨1561416, by rfl⟩ : syracuseStep 4163777 = 3122833) B3122833
theorem B3336385 : Blo 1849626 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B2083063 : Blo 1849626 2083063 := bstep (se 1 (by rfl) ⟨1562297, by rfl⟩ : syracuseStep 2083063 = 3124595) B3124595
theorem B3164441 : Blo 1849626 3164441 := bstep (se 2 (by rfl) ⟨1186665, by rfl⟩ : syracuseStep 3164441 = 2373331) B2373331
theorem B3123481 : Blo 1849626 3123481 := bstep (se 2 (by rfl) ⟨1171305, by rfl⟩ : syracuseStep 3123481 = 2342611) B2342611
theorem B19999021 : Blo 1849626 19999021 := bstep (se 3 (by rfl) ⟨3749816, by rfl⟩ : syracuseStep 19999021 = 7499633) B7499633
theorem B5630273 : Blo 1849626 5630273 := bstep (se 2 (by rfl) ⟨2111352, by rfl⟩ : syracuseStep 5630273 = 4222705) B4222705
theorem B4163993 : Blo 1849626 4163993 := bstep (se 2 (by rfl) ⟨1561497, by rfl⟩ : syracuseStep 4163993 = 3122995) B3122995
theorem B6670795 : Blo 1849626 6670795 := bstep (se 1 (by rfl) ⟨5003096, by rfl⟩ : syracuseStep 6670795 = 10006193) B10006193
theorem B16878041 : Blo 1849626 16878041 := bstep (se 2 (by rfl) ⟨6329265, by rfl⟩ : syracuseStep 16878041 = 12658531) B12658531
theorem B6244829 : Blo 1849626 6244829 := bstep (se 3 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 6244829 = 2341811) B2341811
theorem B4164083 : Blo 1849626 4164083 := bstep (se 1 (by rfl) ⟨3123062, by rfl⟩ : syracuseStep 4164083 = 6246125) B6246125
theorem B1976843 : Blo 1849626 1976843 := bstep (se 1 (by rfl) ⟨1482632, by rfl⟩ : syracuseStep 1976843 = 2965265) B2965265
theorem B4164119 : Blo 1849626 4164119 := bstep (se 1 (by rfl) ⟨3123089, by rfl⟩ : syracuseStep 4164119 = 6246179) B6246179
theorem B23726627 : Blo 1849626 23726627 := bstep (se 1 (by rfl) ⟨17794970, by rfl⟩ : syracuseStep 23726627 = 35589941) B35589941
theorem B25315915 : Blo 1849626 25315915 := bstep (se 1 (by rfl) ⟨18986936, by rfl⟩ : syracuseStep 25315915 = 37973873) B37973873
theorem B7023307 : Blo 1849626 7023307 := bstep (se 1 (by rfl) ⟨5267480, by rfl⟩ : syracuseStep 7023307 = 10534961) B10534961
theorem B4164299 : Blo 1849626 4164299 := bstep (se 1 (by rfl) ⟨3123224, by rfl⟩ : syracuseStep 4164299 = 6246449) B6246449
theorem B4745945 : Blo 1849626 4745945 := bstep (se 2 (by rfl) ⟨1779729, by rfl⟩ : syracuseStep 4745945 = 3559459) B3559459
theorem B6671069 : Blo 1849626 6671069 := bstep (se 3 (by rfl) ⟨1250825, by rfl⟩ : syracuseStep 6671069 = 2501651) B2501651
theorem B4164353 : Blo 1849626 4164353 := bstep (se 2 (by rfl) ⟨1561632, by rfl⟩ : syracuseStep 4164353 = 3123265) B3123265
theorem B5344051 : Blo 1849626 5344051 := bstep (se 1 (by rfl) ⟨4008038, by rfl⟩ : syracuseStep 5344051 = 8016077) B8016077
theorem B3124055 : Blo 1849626 3124055 := bstep (se 1 (by rfl) ⟨2343041, by rfl⟩ : syracuseStep 3124055 = 4686083) B4686083
theorem B14240605 : Blo 1849626 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B3951499 : Blo 1849626 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B5344151 : Blo 1849626 5344151 := bstep (se 1 (by rfl) ⟨4008113, by rfl⟩ : syracuseStep 5344151 = 8016227) B8016227
theorem B14060465 : Blo 1849626 14060465 := bstep (se 2 (by rfl) ⟨5272674, by rfl⟩ : syracuseStep 14060465 = 10545349) B10545349
theorem B3124183 : Blo 1849626 3124183 := bstep (se 1 (by rfl) ⟨2343137, by rfl⟩ : syracuseStep 3124183 = 4686275) B4686275
theorem B4164569 : Blo 1849626 4164569 := bstep (se 2 (by rfl) ⟨1561713, by rfl⟩ : syracuseStep 4164569 = 3123427) B3123427
theorem B7908313 : Blo 1849626 7908313 := bstep (se 2 (by rfl) ⟨2965617, by rfl⟩ : syracuseStep 7908313 = 5931235) B5931235
theorem B7023581 : Blo 1849626 7023581 := bstep (se 3 (by rfl) ⟨1316921, by rfl⟩ : syracuseStep 7023581 = 2633843) B2633843
theorem B57740309 : Blo 1849626 57740309 := bstep (se 6 (by rfl) ⟨1353288, by rfl⟩ : syracuseStep 57740309 = 2706577) B2706577
theorem B5270579 : Blo 1849626 5270579 := bstep (se 1 (by rfl) ⟨3952934, by rfl⟩ : syracuseStep 5270579 = 7905869) B7905869
theorem B4164659 : Blo 1849626 4164659 := bstep (se 1 (by rfl) ⟨3123494, by rfl⟩ : syracuseStep 4164659 = 6246989) B6246989
theorem B10538059 : Blo 1849626 10538059 := bstep (se 1 (by rfl) ⟨7903544, by rfl⟩ : syracuseStep 10538059 = 15807089) B15807089
theorem B4164695 : Blo 1849626 4164695 := bstep (se 1 (by rfl) ⟨3123521, by rfl⟩ : syracuseStep 4164695 = 6247043) B6247043
theorem B14240947 : Blo 1849626 14240947 := bstep (se 1 (by rfl) ⟨10680710, by rfl⟩ : syracuseStep 14240947 = 21361421) B21361421
theorem B4164875 : Blo 1849626 4164875 := bstep (se 1 (by rfl) ⟨3123656, by rfl⟩ : syracuseStep 4164875 = 6247313) B6247313
theorem B5270807 : Blo 1849626 5270807 := bstep (se 1 (by rfl) ⟨3953105, by rfl⟩ : syracuseStep 5270807 = 7906211) B7906211
theorem B4164929 : Blo 1849626 4164929 := bstep (se 2 (by rfl) ⟨1561848, by rfl⟩ : syracuseStep 4164929 = 3123697) B3123697
theorem B10538333 : Blo 1849626 10538333 := bstep (se 3 (by rfl) ⟨1975937, by rfl⟩ : syracuseStep 10538333 = 3951875) B3951875
theorem B9367001 : Blo 1849626 9367001 := bstep (se 2 (by rfl) ⟨3512625, by rfl⟩ : syracuseStep 9367001 = 7025251) B7025251
theorem B4165145 : Blo 1849626 4165145 := bstep (se 2 (by rfl) ⟨1561929, by rfl⟩ : syracuseStep 4165145 = 3123859) B3123859
theorem B15011363 : Blo 1849626 15011363 := bstep (se 1 (by rfl) ⟨11258522, by rfl⟩ : syracuseStep 15011363 = 22517045) B22517045
theorem B6245963 : Blo 1849626 6245963 := bstep (se 1 (by rfl) ⟨4684472, by rfl⟩ : syracuseStep 6245963 = 9368945) B9368945
theorem B5271115 : Blo 1849626 5271115 := bstep (se 1 (by rfl) ⟨3953336, by rfl⟩ : syracuseStep 5271115 = 7906673) B7906673
theorem B3952243 : Blo 1849626 3952243 := bstep (se 1 (by rfl) ⟨2964182, by rfl⟩ : syracuseStep 3952243 = 5928365) B5928365
theorem B4165235 : Blo 1849626 4165235 := bstep (se 1 (by rfl) ⟨3123926, by rfl⟩ : syracuseStep 4165235 = 6247853) B6247853
theorem B2813579 : Blo 1849626 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B7024279 : Blo 1849626 7024279 := bstep (se 1 (by rfl) ⟨5268209, by rfl⟩ : syracuseStep 7024279 = 10536419) B10536419
theorem B4165271 : Blo 1849626 4165271 := bstep (se 1 (by rfl) ⟨3123953, by rfl⟩ : syracuseStep 4165271 = 6247907) B6247907
theorem B7925399 : Blo 1849626 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B4165451 : Blo 1849626 4165451 := bstep (se 1 (by rfl) ⟨3124088, by rfl⟩ : syracuseStep 4165451 = 6248177) B6248177
theorem B6246233 : Blo 1849626 6246233 := bstep (se 2 (by rfl) ⟨2342337, by rfl⟩ : syracuseStep 6246233 = 4684675) B4684675
theorem B5271389 : Blo 1849626 5271389 := bstep (se 3 (by rfl) ⟨988385, by rfl⟩ : syracuseStep 5271389 = 1976771) B1976771
theorem B4165505 : Blo 1849626 4165505 := bstep (se 2 (by rfl) ⟨1562064, by rfl⟩ : syracuseStep 4165505 = 3124129) B3124129
theorem B15806339 : Blo 1849626 15806339 := bstep (se 1 (by rfl) ⟨11854754, by rfl⟩ : syracuseStep 15806339 = 23709509) B23709509
theorem B6672307 : Blo 1849626 6672307 := bstep (se 1 (by rfl) ⟨5004230, by rfl⟩ : syracuseStep 6672307 = 10008461) B10008461
theorem B4444121 : Blo 1849626 4444121 := bstep (se 2 (by rfl) ⟨1666545, by rfl⟩ : syracuseStep 4444121 = 3333091) B3333091
theorem B3952729 : Blo 1849626 3952729 := bstep (se 2 (by rfl) ⟨1482273, by rfl⟩ : syracuseStep 3952729 = 2964547) B2964547
theorem B4165721 : Blo 1849626 4165721 := bstep (se 2 (by rfl) ⟨1562145, by rfl⟩ : syracuseStep 4165721 = 3124291) B3124291
theorem B4165811 : Blo 1849626 4165811 := bstep (se 1 (by rfl) ⟨3124358, by rfl⟩ : syracuseStep 4165811 = 6248717) B6248717
theorem B4681921 : Blo 1849626 4681921 := bstep (se 2 (by rfl) ⟨1755720, by rfl⟩ : syracuseStep 4681921 = 3511441) B3511441
theorem B4165847 : Blo 1849626 4165847 := bstep (se 1 (by rfl) ⟨3124385, by rfl⟩ : syracuseStep 4165847 = 6248771) B6248771
theorem B30011633 : Blo 1849626 30011633 := bstep (se 2 (by rfl) ⟨11254362, by rfl⟩ : syracuseStep 30011633 = 22508725) B22508725
theorem B4166027 : Blo 1849626 4166027 := bstep (se 1 (by rfl) ⟨3124520, by rfl⟩ : syracuseStep 4166027 = 6249041) B6249041
theorem B7025069 : Blo 1849626 7025069 := bstep (se 3 (by rfl) ⟨1317200, by rfl⟩ : syracuseStep 7025069 = 2634401) B2634401
theorem B8442305 : Blo 1849626 8442305 := bstep (se 2 (by rfl) ⟨3165864, by rfl⟩ : syracuseStep 8442305 = 6331729) B6331729
theorem B4166081 : Blo 1849626 4166081 := bstep (se 2 (by rfl) ⟨1562280, by rfl⟩ : syracuseStep 4166081 = 3124561) B3124561
theorem B11858393 : Blo 1849626 11858393 := bstep (se 2 (by rfl) ⟨4446897, by rfl⟩ : syracuseStep 11858393 = 8893795) B8893795
theorem B6246935 : Blo 1849626 6246935 := bstep (se 1 (by rfl) ⟨4685201, by rfl⟩ : syracuseStep 6246935 = 9370403) B9370403
theorem B4682519 : Blo 1849626 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B8893259 : Blo 1849626 8893259 := bstep (se 1 (by rfl) ⟨6669944, by rfl⟩ : syracuseStep 8893259 = 13339889) B13339889
theorem B13341617 : Blo 1849626 13341617 := bstep (se 2 (by rfl) ⟨5003106, by rfl⟩ : syracuseStep 13341617 = 10006213) B10006213
theorem B53375921 : Blo 1849626 53375921 := bstep (se 2 (by rfl) ⟨20015970, by rfl⟩ : syracuseStep 53375921 = 40031941) B40031941
theorem B4338689 : Blo 1849626 4338689 := bstep (se 2 (by rfl) ⟨1627008, by rfl⟩ : syracuseStep 4338689 = 3254017) B3254017
theorem B9368621 : Blo 1849626 9368621 := bstep (se 3 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 9368621 = 3513233) B3513233
theorem B6247475 : Blo 1849626 6247475 := bstep (se 1 (by rfl) ⟨4685606, by rfl⟩ : syracuseStep 6247475 = 9371213) B9371213
theorem B36066485 : Blo 1849626 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B6247745 : Blo 1849626 6247745 := bstep (se 2 (by rfl) ⟨2342904, by rfl⟩ : syracuseStep 6247745 = 4685809) B4685809
theorem B2815319 : Blo 1849626 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B3511745 : Blo 1849626 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B2774489 : Blo 1849626 2774489 := bstep (se 2 (by rfl) ⟨1040433, by rfl⟩ : syracuseStep 2774489 = 2080867) B2080867
theorem B3954199 : Blo 1849626 3954199 := bstep (se 1 (by rfl) ⟨2965649, by rfl⟩ : syracuseStep 3954199 = 5931299) B5931299
theorem B4683329 : Blo 1849626 4683329 := bstep (se 2 (by rfl) ⟨1756248, by rfl⟩ : syracuseStep 4683329 = 3512497) B3512497
theorem B2774603 : Blo 1849626 2774603 := bstep (se 1 (by rfl) ⟨2080952, by rfl⟩ : syracuseStep 2774603 = 4161905) B4161905
theorem B3954251 : Blo 1849626 3954251 := bstep (se 1 (by rfl) ⟨2965688, by rfl⟩ : syracuseStep 3954251 = 5931377) B5931377
theorem B2774615 : Blo 1849626 2774615 := bstep (se 1 (by rfl) ⟨2080961, by rfl⟩ : syracuseStep 2774615 = 4161923) B4161923
theorem B2774681 : Blo 1849626 2774681 := bstep (se 2 (by rfl) ⟨1040505, by rfl⟩ : syracuseStep 2774681 = 2081011) B2081011
theorem B3512011 : Blo 1849626 3512011 := bstep (se 1 (by rfl) ⟨2634008, by rfl⟩ : syracuseStep 3512011 = 5268017) B5268017
theorem B2774795 : Blo 1849626 2774795 := bstep (se 1 (by rfl) ⟨2081096, by rfl⟩ : syracuseStep 2774795 = 4162193) B4162193
theorem B2774807 : Blo 1849626 2774807 := bstep (se 1 (by rfl) ⟨2081105, by rfl⟩ : syracuseStep 2774807 = 4162211) B4162211
theorem B4445975 : Blo 1849626 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B7223063 : Blo 1849626 7223063 := bstep (se 1 (by rfl) ⟨5417297, by rfl⟩ : syracuseStep 7223063 = 10834595) B10834595
theorem B7026497 : Blo 1849626 7026497 := bstep (se 2 (by rfl) ⟨2634936, by rfl⟩ : syracuseStep 7026497 = 5269873) B5269873
theorem B2774873 : Blo 1849626 2774873 := bstep (se 2 (by rfl) ⟨1040577, by rfl⟩ : syracuseStep 2774873 = 2081155) B2081155
theorem B6248285 : Blo 1849626 6248285 := bstep (se 3 (by rfl) ⟨1171553, by rfl⟩ : syracuseStep 6248285 = 2343107) B2343107
theorem B2774987 : Blo 1849626 2774987 := bstep (se 1 (by rfl) ⟨2081240, by rfl⟩ : syracuseStep 2774987 = 4162481) B4162481
theorem B2774999 : Blo 1849626 2774999 := bstep (se 1 (by rfl) ⟨2081249, by rfl⟩ : syracuseStep 2774999 = 4162499) B4162499
theorem B31610897 : Blo 1849626 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B2775065 : Blo 1849626 2775065 := bstep (se 2 (by rfl) ⟨1040649, by rfl⟩ : syracuseStep 2775065 = 2081299) B2081299
theorem B11860033 : Blo 1849626 11860033 := bstep (se 2 (by rfl) ⟨4447512, by rfl⟩ : syracuseStep 11860033 = 8895025) B8895025
theorem B4683865 : Blo 1849626 4683865 := bstep (se 2 (by rfl) ⟨1756449, by rfl⟩ : syracuseStep 4683865 = 3512899) B3512899
theorem B2775179 : Blo 1849626 2775179 := bstep (se 1 (by rfl) ⟨2081384, by rfl⟩ : syracuseStep 2775179 = 4162769) B4162769
theorem B3512459 : Blo 1849626 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B2775191 : Blo 1849626 2775191 := bstep (se 1 (by rfl) ⟨2081393, by rfl⟩ : syracuseStep 2775191 = 4162787) B4162787
theorem B2775257 : Blo 1849626 2775257 := bstep (se 2 (by rfl) ⟨1040721, by rfl⟩ : syracuseStep 2775257 = 2081443) B2081443
theorem B15808729 : Blo 1849626 15808729 := bstep (se 2 (by rfl) ⟨5928273, by rfl⟩ : syracuseStep 15808729 = 11856547) B11856547
theorem B1849643 : Blo 1849626 1849643 := bstep (se 1 (by rfl) ⟨1387232, by rfl⟩ : syracuseStep 1849643 = 2774465) B2774465
theorem B1849655 : Blo 1849626 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B3512641 : Blo 1849626 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B1849675 : Blo 1849626 1849675 := bstep (se 1 (by rfl) ⟨1387256, by rfl⟩ : syracuseStep 1849675 = 2774513) B2774513
theorem B2775371 : Blo 1849626 2775371 := bstep (se 1 (by rfl) ⟨2081528, by rfl⟩ : syracuseStep 2775371 = 4163057) B4163057
theorem B1849687 : Blo 1849626 1849687 := bstep (se 1 (by rfl) ⟨1387265, by rfl⟩ : syracuseStep 1849687 = 2774531) B2774531
theorem B2775383 : Blo 1849626 2775383 := bstep (se 1 (by rfl) ⟨2081537, by rfl⟩ : syracuseStep 2775383 = 4163075) B4163075
theorem B1849707 : Blo 1849626 1849707 := bstep (se 1 (by rfl) ⟨1387280, by rfl⟩ : syracuseStep 1849707 = 2774561) B2774561
theorem B1849719 : Blo 1849626 1849719 := bstep (se 1 (by rfl) ⟨1387289, by rfl⟩ : syracuseStep 1849719 = 2774579) B2774579
theorem B1849739 : Blo 1849626 1849739 := bstep (se 1 (by rfl) ⟨1387304, by rfl⟩ : syracuseStep 1849739 = 2774609) B2774609
theorem B1849751 : Blo 1849626 1849751 := bstep (se 1 (by rfl) ⟨1387313, by rfl⟩ : syracuseStep 1849751 = 2774627) B2774627
theorem B2775449 : Blo 1849626 2775449 := bstep (se 2 (by rfl) ⟨1040793, by rfl⟩ : syracuseStep 2775449 = 2081587) B2081587
theorem B1849771 : Blo 1849626 1849771 := bstep (se 1 (by rfl) ⟨1387328, by rfl⟩ : syracuseStep 1849771 = 2774657) B2774657
theorem B1849783 : Blo 1849626 1849783 := bstep (se 1 (by rfl) ⟨1387337, by rfl⟩ : syracuseStep 1849783 = 2774675) B2774675
theorem B1849803 : Blo 1849626 1849803 := bstep (se 1 (by rfl) ⟨1387352, by rfl⟩ : syracuseStep 1849803 = 2774705) B2774705
theorem B4446667 : Blo 1849626 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B1849815 : Blo 1849626 1849815 := bstep (se 1 (by rfl) ⟨1387361, by rfl⟩ : syracuseStep 1849815 = 2774723) B2774723
theorem B2963927 : Blo 1849626 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1849835 : Blo 1849626 1849835 := bstep (se 1 (by rfl) ⟨1387376, by rfl⟩ : syracuseStep 1849835 = 2774753) B2774753
theorem B1849847 : Blo 1849626 1849847 := bstep (se 1 (by rfl) ⟨1387385, by rfl⟩ : syracuseStep 1849847 = 2774771) B2774771
theorem B3750401 : Blo 1849626 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B1849867 : Blo 1849626 1849867 := bstep (se 1 (by rfl) ⟨1387400, by rfl⟩ : syracuseStep 1849867 = 2774801) B2774801
theorem B2775563 : Blo 1849626 2775563 := bstep (se 1 (by rfl) ⟨2081672, by rfl⟩ : syracuseStep 2775563 = 4163345) B4163345
theorem B50674193 : Blo 1849626 50674193 := bstep (se 2 (by rfl) ⟨19002822, by rfl⟩ : syracuseStep 50674193 = 38005645) B38005645
theorem B1849879 : Blo 1849626 1849879 := bstep (se 1 (by rfl) ⟨1387409, by rfl⟩ : syracuseStep 1849879 = 2774819) B2774819
theorem B2775575 : Blo 1849626 2775575 := bstep (se 1 (by rfl) ⟨2081681, by rfl⟩ : syracuseStep 2775575 = 4163363) B4163363
theorem B1849899 : Blo 1849626 1849899 := bstep (se 1 (by rfl) ⟨1387424, by rfl⟩ : syracuseStep 1849899 = 2774849) B2774849
theorem B1849911 : Blo 1849626 1849911 := bstep (se 1 (by rfl) ⟨1387433, by rfl⟩ : syracuseStep 1849911 = 2774867) B2774867
theorem B1849931 : Blo 1849626 1849931 := bstep (se 1 (by rfl) ⟨1387448, by rfl⟩ : syracuseStep 1849931 = 2774897) B2774897
theorem B1849943 : Blo 1849626 1849943 := bstep (se 1 (by rfl) ⟨1387457, by rfl⟩ : syracuseStep 1849943 = 2774915) B2774915
theorem B2775641 : Blo 1849626 2775641 := bstep (se 2 (by rfl) ⟨1040865, by rfl⟩ : syracuseStep 2775641 = 2081731) B2081731
theorem B1849963 : Blo 1849626 1849963 := bstep (se 1 (by rfl) ⟨1387472, by rfl⟩ : syracuseStep 1849963 = 2774945) B2774945
theorem B1849975 : Blo 1849626 1849975 := bstep (se 1 (by rfl) ⟨1387481, by rfl⟩ : syracuseStep 1849975 = 2774963) B2774963
theorem B1849995 : Blo 1849626 1849995 := bstep (se 1 (by rfl) ⟨1387496, by rfl⟩ : syracuseStep 1849995 = 2774993) B2774993
theorem B1850007 : Blo 1849626 1850007 := bstep (se 1 (by rfl) ⟨1387505, by rfl⟩ : syracuseStep 1850007 = 2775011) B2775011
theorem B3512983 : Blo 1849626 3512983 := bstep (se 1 (by rfl) ⟨2634737, by rfl⟩ : syracuseStep 3512983 = 5269475) B5269475
theorem B1850027 : Blo 1849626 1850027 := bstep (se 1 (by rfl) ⟨1387520, by rfl⟩ : syracuseStep 1850027 = 2775041) B2775041
theorem B1850039 : Blo 1849626 1850039 := bstep (se 1 (by rfl) ⟨1387529, by rfl⟩ : syracuseStep 1850039 = 2775059) B2775059
theorem B1850059 : Blo 1849626 1850059 := bstep (se 1 (by rfl) ⟨1387544, by rfl⟩ : syracuseStep 1850059 = 2775089) B2775089
theorem B2775755 : Blo 1849626 2775755 := bstep (se 1 (by rfl) ⟨2081816, by rfl⟩ : syracuseStep 2775755 = 4163633) B4163633
theorem B1850071 : Blo 1849626 1850071 := bstep (se 1 (by rfl) ⟨1387553, by rfl⟩ : syracuseStep 1850071 = 2775107) B2775107
theorem B2775767 : Blo 1849626 2775767 := bstep (se 1 (by rfl) ⟨2081825, by rfl⟩ : syracuseStep 2775767 = 4163651) B4163651
theorem B13703897 : Blo 1849626 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B1850091 : Blo 1849626 1850091 := bstep (se 1 (by rfl) ⟨1387568, by rfl⟩ : syracuseStep 1850091 = 2775137) B2775137
theorem B1850103 : Blo 1849626 1850103 := bstep (se 1 (by rfl) ⟨1387577, by rfl⟩ : syracuseStep 1850103 = 2775155) B2775155
theorem B15817477 : Blo 1849626 15817477 := bstep (se 4 (by rfl) ⟨1482888, by rfl⟩ : syracuseStep 15817477 = 2965777) B2965777
theorem B1850123 : Blo 1849626 1850123 := bstep (se 1 (by rfl) ⟨1387592, by rfl⟩ : syracuseStep 1850123 = 2775185) B2775185
theorem B1850135 : Blo 1849626 1850135 := bstep (se 1 (by rfl) ⟨1387601, by rfl⟩ : syracuseStep 1850135 = 2775203) B2775203
theorem B2775833 : Blo 1849626 2775833 := bstep (se 2 (by rfl) ⟨1040937, by rfl⟩ : syracuseStep 2775833 = 2081875) B2081875
theorem B1850155 : Blo 1849626 1850155 := bstep (se 1 (by rfl) ⟨1387616, by rfl⟩ : syracuseStep 1850155 = 2775233) B2775233
theorem B1850167 : Blo 1849626 1850167 := bstep (se 1 (by rfl) ⟨1387625, by rfl⟩ : syracuseStep 1850167 = 2775251) B2775251
theorem B1850187 : Blo 1849626 1850187 := bstep (se 1 (by rfl) ⟨1387640, by rfl⟩ : syracuseStep 1850187 = 2775281) B2775281
theorem B1850199 : Blo 1849626 1850199 := bstep (se 1 (by rfl) ⟨1387649, by rfl⟩ : syracuseStep 1850199 = 2775299) B2775299
theorem B3521369 : Blo 1849626 3521369 := bstep (se 2 (by rfl) ⟨1320513, by rfl⟩ : syracuseStep 3521369 = 2641027) B2641027
theorem B1850219 : Blo 1849626 1850219 := bstep (se 1 (by rfl) ⟨1387664, by rfl⟩ : syracuseStep 1850219 = 2775329) B2775329
theorem B3513203 : Blo 1849626 3513203 := bstep (se 1 (by rfl) ⟨2634902, by rfl⟩ : syracuseStep 3513203 = 5269805) B5269805
theorem B1850231 : Blo 1849626 1850231 := bstep (se 1 (by rfl) ⟨1387673, by rfl⟩ : syracuseStep 1850231 = 2775347) B2775347
theorem B1850251 : Blo 1849626 1850251 := bstep (se 1 (by rfl) ⟨1387688, by rfl⟩ : syracuseStep 1850251 = 2775377) B2775377
theorem B2775947 : Blo 1849626 2775947 := bstep (se 1 (by rfl) ⟨2081960, by rfl⟩ : syracuseStep 2775947 = 4163921) B4163921
theorem B1850263 : Blo 1849626 1850263 := bstep (se 1 (by rfl) ⟨1387697, by rfl⟩ : syracuseStep 1850263 = 2775395) B2775395
theorem B2775959 : Blo 1849626 2775959 := bstep (se 1 (by rfl) ⟨2081969, by rfl⟩ : syracuseStep 2775959 = 4163939) B4163939
theorem B3562393 : Blo 1849626 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B1850283 : Blo 1849626 1850283 := bstep (se 1 (by rfl) ⟨1387712, by rfl⟩ : syracuseStep 1850283 = 2775425) B2775425
theorem B1850295 : Blo 1849626 1850295 := bstep (se 1 (by rfl) ⟨1387721, by rfl⟩ : syracuseStep 1850295 = 2775443) B2775443
theorem B4750273 : Blo 1849626 4750273 := bstep (se 2 (by rfl) ⟨1781352, by rfl⟩ : syracuseStep 4750273 = 3562705) B3562705
theorem B1850315 : Blo 1849626 1850315 := bstep (se 1 (by rfl) ⟨1387736, by rfl⟩ : syracuseStep 1850315 = 2775473) B2775473
theorem B1850327 : Blo 1849626 1850327 := bstep (se 1 (by rfl) ⟨1387745, by rfl⟩ : syracuseStep 1850327 = 2775491) B2775491
theorem B2776025 : Blo 1849626 2776025 := bstep (se 2 (by rfl) ⟨1041009, by rfl⟩ : syracuseStep 2776025 = 2082019) B2082019
theorem B1850347 : Blo 1849626 1850347 := bstep (se 1 (by rfl) ⟨1387760, by rfl⟩ : syracuseStep 1850347 = 2775521) B2775521
theorem B1850359 : Blo 1849626 1850359 := bstep (se 1 (by rfl) ⟨1387769, by rfl⟩ : syracuseStep 1850359 = 2775539) B2775539
theorem B1850379 : Blo 1849626 1850379 := bstep (se 1 (by rfl) ⟨1387784, by rfl⟩ : syracuseStep 1850379 = 2775569) B2775569
theorem B1850391 : Blo 1849626 1850391 := bstep (se 1 (by rfl) ⟨1387793, by rfl⟩ : syracuseStep 1850391 = 2775587) B2775587
theorem B1850411 : Blo 1849626 1850411 := bstep (se 1 (by rfl) ⟨1387808, by rfl⟩ : syracuseStep 1850411 = 2775617) B2775617
theorem B1850423 : Blo 1849626 1850423 := bstep (se 1 (by rfl) ⟨1387817, by rfl⟩ : syracuseStep 1850423 = 2775635) B2775635
theorem B2341963 : Blo 1849626 2341963 := bstep (se 1 (by rfl) ⟨1756472, by rfl⟩ : syracuseStep 2341963 = 3512945) B3512945
theorem B1850443 : Blo 1849626 1850443 := bstep (se 1 (by rfl) ⟨1387832, by rfl⟩ : syracuseStep 1850443 = 2775665) B2775665
theorem B2776139 : Blo 1849626 2776139 := bstep (se 1 (by rfl) ⟨2082104, by rfl⟩ : syracuseStep 2776139 = 4164209) B4164209
theorem B3005515 : Blo 1849626 3005515 := bstep (se 1 (by rfl) ⟨2254136, by rfl⟩ : syracuseStep 3005515 = 4508273) B4508273
theorem B1850455 : Blo 1849626 1850455 := bstep (se 1 (by rfl) ⟨1387841, by rfl⟩ : syracuseStep 1850455 = 2775683) B2775683
theorem B3513431 : Blo 1849626 3513431 := bstep (se 1 (by rfl) ⟨2635073, by rfl⟩ : syracuseStep 3513431 = 5270147) B5270147
theorem B2776151 : Blo 1849626 2776151 := bstep (se 1 (by rfl) ⟨2082113, by rfl⟩ : syracuseStep 2776151 = 4164227) B4164227
theorem B1850475 : Blo 1849626 1850475 := bstep (se 1 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 1850475 = 2775713) B2775713
theorem B1850487 : Blo 1849626 1850487 := bstep (se 1 (by rfl) ⟨1387865, by rfl⟩ : syracuseStep 1850487 = 2775731) B2775731
theorem B1850507 : Blo 1849626 1850507 := bstep (se 1 (by rfl) ⟨1387880, by rfl⟩ : syracuseStep 1850507 = 2775761) B2775761
theorem B3333271 : Blo 1849626 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B1850519 : Blo 1849626 1850519 := bstep (se 1 (by rfl) ⟨1387889, by rfl⟩ : syracuseStep 1850519 = 2775779) B2775779
theorem B15809687 : Blo 1849626 15809687 := bstep (se 1 (by rfl) ⟨11857265, by rfl⟩ : syracuseStep 15809687 = 23714531) B23714531
theorem B2776217 : Blo 1849626 2776217 := bstep (se 2 (by rfl) ⟨1041081, by rfl⟩ : syracuseStep 2776217 = 2082163) B2082163
theorem B1850539 : Blo 1849626 1850539 := bstep (se 1 (by rfl) ⟨1387904, by rfl⟩ : syracuseStep 1850539 = 2775809) B2775809
theorem B4684979 : Blo 1849626 4684979 := bstep (se 1 (by rfl) ⟨3513734, by rfl⟩ : syracuseStep 4684979 = 7027469) B7027469
theorem B1850551 : Blo 1849626 1850551 := bstep (se 1 (by rfl) ⟨1387913, by rfl⟩ : syracuseStep 1850551 = 2775827) B2775827
theorem B1850571 : Blo 1849626 1850571 := bstep (se 1 (by rfl) ⟨1387928, by rfl⟩ : syracuseStep 1850571 = 2775857) B2775857
theorem B1850583 : Blo 1849626 1850583 := bstep (se 1 (by rfl) ⟨1387937, by rfl⟩ : syracuseStep 1850583 = 2775875) B2775875
theorem B1850603 : Blo 1849626 1850603 := bstep (se 1 (by rfl) ⟨1387952, by rfl⟩ : syracuseStep 1850603 = 2775905) B2775905
theorem B1850615 : Blo 1849626 1850615 := bstep (se 1 (by rfl) ⟨1387961, by rfl⟩ : syracuseStep 1850615 = 2775923) B2775923
theorem B1850635 : Blo 1849626 1850635 := bstep (se 1 (by rfl) ⟨1387976, by rfl⟩ : syracuseStep 1850635 = 2775953) B2775953
theorem B2776331 : Blo 1849626 2776331 := bstep (se 1 (by rfl) ⟨2082248, by rfl⟩ : syracuseStep 2776331 = 4164497) B4164497
theorem B7027985 : Blo 1849626 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B1850647 : Blo 1849626 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B2776343 : Blo 1849626 2776343 := bstep (se 1 (by rfl) ⟨2082257, by rfl⟩ : syracuseStep 2776343 = 4164515) B4164515
theorem B1850667 : Blo 1849626 1850667 := bstep (se 1 (by rfl) ⟨1388000, by rfl⟩ : syracuseStep 1850667 = 2776001) B2776001
theorem B1850679 : Blo 1849626 1850679 := bstep (se 1 (by rfl) ⟨1388009, by rfl⟩ : syracuseStep 1850679 = 2776019) B2776019
theorem B1850699 : Blo 1849626 1850699 := bstep (se 1 (by rfl) ⟨1388024, by rfl⟩ : syracuseStep 1850699 = 2776049) B2776049
theorem B1850711 : Blo 1849626 1850711 := bstep (se 1 (by rfl) ⟨1388033, by rfl⟩ : syracuseStep 1850711 = 2776067) B2776067
theorem B6667609 : Blo 1849626 6667609 := bstep (se 2 (by rfl) ⟨2500353, by rfl⟩ : syracuseStep 6667609 = 5000707) B5000707
theorem B3513689 : Blo 1849626 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B2776409 : Blo 1849626 2776409 := bstep (se 2 (by rfl) ⟨1041153, by rfl⟩ : syracuseStep 2776409 = 2082307) B2082307
theorem B1850731 : Blo 1849626 1850731 := bstep (se 1 (by rfl) ⟨1388048, by rfl⟩ : syracuseStep 1850731 = 2776097) B2776097
theorem B1850743 : Blo 1849626 1850743 := bstep (se 1 (by rfl) ⟨1388057, by rfl⟩ : syracuseStep 1850743 = 2776115) B2776115
theorem B1850763 : Blo 1849626 1850763 := bstep (se 1 (by rfl) ⟨1388072, by rfl⟩ : syracuseStep 1850763 = 2776145) B2776145
theorem B1850775 : Blo 1849626 1850775 := bstep (se 1 (by rfl) ⟨1388081, by rfl⟩ : syracuseStep 1850775 = 2776163) B2776163
theorem B1850795 : Blo 1849626 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B11255219 : Blo 1849626 11255219 := bstep (se 1 (by rfl) ⟨8441414, by rfl⟩ : syracuseStep 11255219 = 16882829) B16882829
theorem B1850807 : Blo 1849626 1850807 := bstep (se 1 (by rfl) ⟨1388105, by rfl⟩ : syracuseStep 1850807 = 2776211) B2776211
theorem B1850827 : Blo 1849626 1850827 := bstep (se 1 (by rfl) ⟨1388120, by rfl⟩ : syracuseStep 1850827 = 2776241) B2776241
theorem B2776523 : Blo 1849626 2776523 := bstep (se 1 (by rfl) ⟨2082392, by rfl⟩ : syracuseStep 2776523 = 4164785) B4164785
theorem B1850839 : Blo 1849626 1850839 := bstep (se 1 (by rfl) ⟨1388129, by rfl⟩ : syracuseStep 1850839 = 2776259) B2776259
theorem B2776535 : Blo 1849626 2776535 := bstep (se 1 (by rfl) ⟨2082401, by rfl⟩ : syracuseStep 2776535 = 4164803) B4164803
theorem B5627353 : Blo 1849626 5627353 := bstep (se 2 (by rfl) ⟨2110257, by rfl⟩ : syracuseStep 5627353 = 4220515) B4220515
theorem B4685273 : Blo 1849626 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B4447705 : Blo 1849626 4447705 := bstep (se 2 (by rfl) ⟨1667889, by rfl⟩ : syracuseStep 4447705 = 3335779) B3335779
theorem B1850859 : Blo 1849626 1850859 := bstep (se 1 (by rfl) ⟨1388144, by rfl⟩ : syracuseStep 1850859 = 2776289) B2776289
theorem B1850871 : Blo 1849626 1850871 := bstep (se 1 (by rfl) ⟨1388153, by rfl⟩ : syracuseStep 1850871 = 2776307) B2776307
theorem B1850891 : Blo 1849626 1850891 := bstep (se 1 (by rfl) ⟨1388168, by rfl⟩ : syracuseStep 1850891 = 2776337) B2776337
theorem B15810065 : Blo 1849626 15810065 := bstep (se 2 (by rfl) ⟨5928774, by rfl⟩ : syracuseStep 15810065 = 11857549) B11857549
theorem B1850903 : Blo 1849626 1850903 := bstep (se 1 (by rfl) ⟨1388177, by rfl⟩ : syracuseStep 1850903 = 2776355) B2776355
theorem B2776601 : Blo 1849626 2776601 := bstep (se 2 (by rfl) ⟨1041225, by rfl⟩ : syracuseStep 2776601 = 2082451) B2082451
theorem B1850923 : Blo 1849626 1850923 := bstep (se 1 (by rfl) ⟨1388192, by rfl⟩ : syracuseStep 1850923 = 2776385) B2776385
theorem B1850935 : Blo 1849626 1850935 := bstep (se 1 (by rfl) ⟨1388201, by rfl⟩ : syracuseStep 1850935 = 2776403) B2776403
theorem B1850955 : Blo 1849626 1850955 := bstep (se 1 (by rfl) ⟨1388216, by rfl⟩ : syracuseStep 1850955 = 2776433) B2776433
theorem B1850967 : Blo 1849626 1850967 := bstep (se 1 (by rfl) ⟨1388225, by rfl⟩ : syracuseStep 1850967 = 2776451) B2776451
theorem B1850987 : Blo 1849626 1850987 := bstep (se 1 (by rfl) ⟨1388240, by rfl⟩ : syracuseStep 1850987 = 2776481) B2776481
theorem B1850999 : Blo 1849626 1850999 := bstep (se 1 (by rfl) ⟨1388249, by rfl⟩ : syracuseStep 1850999 = 2776499) B2776499
theorem B9494147 : Blo 1849626 9494147 := bstep (se 1 (by rfl) ⟨7120610, by rfl⟩ : syracuseStep 9494147 = 14241221) B14241221
theorem B7503491 : Blo 1849626 7503491 := bstep (se 1 (by rfl) ⟨5627618, by rfl⟩ : syracuseStep 7503491 = 11255237) B11255237
theorem B1851019 : Blo 1849626 1851019 := bstep (se 1 (by rfl) ⟨1388264, by rfl⟩ : syracuseStep 1851019 = 2776529) B2776529
theorem B2776715 : Blo 1849626 2776715 := bstep (se 1 (by rfl) ⟨2082536, by rfl⟩ : syracuseStep 2776715 = 4165073) B4165073
theorem B1851031 : Blo 1849626 1851031 := bstep (se 1 (by rfl) ⟨1388273, by rfl⟩ : syracuseStep 1851031 = 2776547) B2776547
theorem B2776727 : Blo 1849626 2776727 := bstep (se 1 (by rfl) ⟨2082545, by rfl⟩ : syracuseStep 2776727 = 4165091) B4165091
theorem B1851051 : Blo 1849626 1851051 := bstep (se 1 (by rfl) ⟨1388288, by rfl⟩ : syracuseStep 1851051 = 2776577) B2776577
theorem B1851063 : Blo 1849626 1851063 := bstep (se 1 (by rfl) ⟨1388297, by rfl⟩ : syracuseStep 1851063 = 2776595) B2776595
theorem B90054341 : Blo 1849626 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B1851083 : Blo 1849626 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B3333847 : Blo 1849626 3333847 := bstep (se 1 (by rfl) ⟨2500385, by rfl⟩ : syracuseStep 3333847 = 5000771) B5000771
theorem B1851095 : Blo 1849626 1851095 := bstep (se 1 (by rfl) ⟨1388321, by rfl⟩ : syracuseStep 1851095 = 2776643) B2776643
theorem B7028441 : Blo 1849626 7028441 := bstep (se 2 (by rfl) ⟨2635665, by rfl⟩ : syracuseStep 7028441 = 5271331) B5271331
theorem B2776793 : Blo 1849626 2776793 := bstep (se 2 (by rfl) ⟨1041297, by rfl⟩ : syracuseStep 2776793 = 2082595) B2082595
theorem B1851115 : Blo 1849626 1851115 := bstep (se 1 (by rfl) ⟨1388336, by rfl⟩ : syracuseStep 1851115 = 2776673) B2776673
theorem B3514099 : Blo 1849626 3514099 := bstep (se 1 (by rfl) ⟨2635574, by rfl⟩ : syracuseStep 3514099 = 5271149) B5271149
theorem B1851127 : Blo 1849626 1851127 := bstep (se 1 (by rfl) ⟨1388345, by rfl⟩ : syracuseStep 1851127 = 2776691) B2776691
theorem B1851147 : Blo 1849626 1851147 := bstep (se 1 (by rfl) ⟨1388360, by rfl⟩ : syracuseStep 1851147 = 2776721) B2776721
theorem B1851159 : Blo 1849626 1851159 := bstep (se 1 (by rfl) ⟨1388369, by rfl⟩ : syracuseStep 1851159 = 2776739) B2776739
theorem B1851179 : Blo 1849626 1851179 := bstep (se 1 (by rfl) ⟨1388384, by rfl⟩ : syracuseStep 1851179 = 2776769) B2776769
theorem B4448051 : Blo 1849626 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B1851191 : Blo 1849626 1851191 := bstep (se 1 (by rfl) ⟨1388393, by rfl⟩ : syracuseStep 1851191 = 2776787) B2776787
theorem B12017483 : Blo 1849626 12017483 := bstep (se 1 (by rfl) ⟨9013112, by rfl⟩ : syracuseStep 12017483 = 18026225) B18026225
theorem B1851211 : Blo 1849626 1851211 := bstep (se 1 (by rfl) ⟨1388408, by rfl⟩ : syracuseStep 1851211 = 2776817) B2776817
theorem B2776907 : Blo 1849626 2776907 := bstep (se 1 (by rfl) ⟨2082680, by rfl⟩ : syracuseStep 2776907 = 4165361) B4165361
theorem B1851223 : Blo 1849626 1851223 := bstep (se 1 (by rfl) ⟨1388417, by rfl⟩ : syracuseStep 1851223 = 2776835) B2776835
theorem B2776919 : Blo 1849626 2776919 := bstep (se 1 (by rfl) ⟨2082689, by rfl⟩ : syracuseStep 2776919 = 4165379) B4165379
theorem B1851243 : Blo 1849626 1851243 := bstep (se 1 (by rfl) ⟨1388432, by rfl⟩ : syracuseStep 1851243 = 2776865) B2776865
theorem B1851255 : Blo 1849626 1851255 := bstep (se 1 (by rfl) ⟨1388441, by rfl⟩ : syracuseStep 1851255 = 2776883) B2776883
theorem B1851275 : Blo 1849626 1851275 := bstep (se 1 (by rfl) ⟨1388456, by rfl⟩ : syracuseStep 1851275 = 2776913) B2776913
theorem B1851287 : Blo 1849626 1851287 := bstep (se 1 (by rfl) ⟨1388465, by rfl⟩ : syracuseStep 1851287 = 2776931) B2776931
theorem B2776985 : Blo 1849626 2776985 := bstep (se 2 (by rfl) ⟨1041369, by rfl⟩ : syracuseStep 2776985 = 2082739) B2082739
theorem B1851307 : Blo 1849626 1851307 := bstep (se 1 (by rfl) ⟨1388480, by rfl⟩ : syracuseStep 1851307 = 2776961) B2776961
theorem B7028653 : Blo 1849626 7028653 := bstep (se 3 (by rfl) ⟨1317872, by rfl⟩ : syracuseStep 7028653 = 2635745) B2635745
theorem B1851319 : Blo 1849626 1851319 := bstep (se 1 (by rfl) ⟨1388489, by rfl⟩ : syracuseStep 1851319 = 2776979) B2776979
theorem B1851339 : Blo 1849626 1851339 := bstep (se 1 (by rfl) ⟨1388504, by rfl⟩ : syracuseStep 1851339 = 2777009) B2777009
theorem B1851351 : Blo 1849626 1851351 := bstep (se 1 (by rfl) ⟨1388513, by rfl⟩ : syracuseStep 1851351 = 2777027) B2777027
theorem B1851371 : Blo 1849626 1851371 := bstep (se 1 (by rfl) ⟨1388528, by rfl⟩ : syracuseStep 1851371 = 2777057) B2777057
theorem B1851383 : Blo 1849626 1851383 := bstep (se 1 (by rfl) ⟨1388537, by rfl⟩ : syracuseStep 1851383 = 2777075) B2777075
theorem B1851399 : Blo 1849626 1851399 := bstep (se 1 (by rfl) ⟨1388549, by rfl⟩ : syracuseStep 1851399 = 2777099) B2777099
theorem B1851407 : Blo 1849626 1851407 := bstep (se 1 (by rfl) ⟨1388555, by rfl⟩ : syracuseStep 1851407 = 2777111) B2777111
theorem B2965547 : Blo 1849626 2965547 := bstep (se 1 (by rfl) ⟨2224160, by rfl⟩ : syracuseStep 2965547 = 4448321) B4448321
theorem B2777147 : Blo 1849626 2777147 := bstep (se 1 (by rfl) ⟨2082860, by rfl⟩ : syracuseStep 2777147 = 4165721) B4165721
theorem B1851451 : Blo 1849626 1851451 := bstep (se 1 (by rfl) ⟨1388588, by rfl⟩ : syracuseStep 1851451 = 2777177) B2777177
theorem B2777207 : Blo 1849626 2777207 := bstep (se 1 (by rfl) ⟨2082905, by rfl⟩ : syracuseStep 2777207 = 4165811) B4165811
theorem B4161671 : Blo 1849626 4161671 := bstep (se 1 (by rfl) ⟨3121253, by rfl⟩ : syracuseStep 4161671 = 6242507) B6242507
theorem B2080903 : Blo 1849626 2080903 := bstep (se 1 (by rfl) ⟨1560677, by rfl⟩ : syracuseStep 2080903 = 3121355) B3121355
theorem B1851527 : Blo 1849626 1851527 := bstep (se 1 (by rfl) ⟨1388645, by rfl⟩ : syracuseStep 1851527 = 2777291) B2777291
theorem B2777231 : Blo 1849626 2777231 := bstep (se 1 (by rfl) ⟨2082923, by rfl⟩ : syracuseStep 2777231 = 4165847) B4165847
theorem B1851535 : Blo 1849626 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B4685971 : Blo 1849626 4685971 := bstep (se 1 (by rfl) ⟨3514478, by rfl⟩ : syracuseStep 4685971 = 7028957) B7028957
theorem B2777273 : Blo 1849626 2777273 := bstep (se 2 (by rfl) ⟨1041477, by rfl⟩ : syracuseStep 2777273 = 2082955) B2082955
theorem B1851579 : Blo 1849626 1851579 := bstep (se 1 (by rfl) ⟨1388684, by rfl⟩ : syracuseStep 1851579 = 2777369) B2777369
theorem B77046005 : Blo 1849626 77046005 := bstep (se 5 (by rfl) ⟨3611531, by rfl⟩ : syracuseStep 77046005 = 7223063) B7223063
theorem B6242561 : Blo 1849626 6242561 := bstep (se 2 (by rfl) ⟨2340960, by rfl⟩ : syracuseStep 6242561 = 4681921) B4681921
theorem B4448513 : Blo 1849626 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B2777351 : Blo 1849626 2777351 := bstep (se 1 (by rfl) ⟨2083013, by rfl⟩ : syracuseStep 2777351 = 4166027) B4166027
theorem B21078305 : Blo 1849626 21078305 := bstep (se 2 (by rfl) ⟨7904364, by rfl⟩ : syracuseStep 21078305 = 15808729) B15808729
theorem B4686113 : Blo 1849626 4686113 := bstep (se 2 (by rfl) ⟨1757292, by rfl⟩ : syracuseStep 4686113 = 3514585) B3514585
theorem B5628203 : Blo 1849626 5628203 := bstep (se 1 (by rfl) ⟨4221152, by rfl⟩ : syracuseStep 5628203 = 8442305) B8442305
theorem B2777387 : Blo 1849626 2777387 := bstep (se 1 (by rfl) ⟨2083040, by rfl⟩ : syracuseStep 2777387 = 4166081) B4166081
theorem B4161851 : Blo 1849626 4161851 := bstep (se 1 (by rfl) ⟨3121388, by rfl⟩ : syracuseStep 4161851 = 6242777) B6242777
theorem B2081083 : Blo 1849626 2081083 := bstep (se 1 (by rfl) ⟨1560812, by rfl⟩ : syracuseStep 2081083 = 3121625) B3121625
theorem B7905595 : Blo 1849626 7905595 := bstep (se 1 (by rfl) ⟨5929196, by rfl⟩ : syracuseStep 7905595 = 11858393) B11858393
theorem B2777417 : Blo 1849626 2777417 := bstep (se 2 (by rfl) ⟨1041531, by rfl⟩ : syracuseStep 2777417 = 2083063) B2083063
theorem B26665361 : Blo 1849626 26665361 := bstep (se 2 (by rfl) ⟨9999510, by rfl⟩ : syracuseStep 26665361 = 19999021) B19999021
theorem B7029139 : Blo 1849626 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B4161977 : Blo 1849626 4161977 := bstep (se 2 (by rfl) ⟨1560741, by rfl⟩ : syracuseStep 4161977 = 3121483) B3121483
theorem B2343431 : Blo 1849626 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B3121679 : Blo 1849626 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B8438509 : Blo 1849626 8438509 := bstep (se 3 (by rfl) ⟨1582220, by rfl⟩ : syracuseStep 8438509 = 3164441) B3164441
theorem B4162319 : Blo 1849626 4162319 := bstep (se 1 (by rfl) ⟨3121739, by rfl⟩ : syracuseStep 4162319 = 6243479) B6243479
theorem B2081551 : Blo 1849626 2081551 := bstep (se 1 (by rfl) ⟨1561163, by rfl⟩ : syracuseStep 2081551 = 3122327) B3122327
theorem B4162337 : Blo 1849626 4162337 := bstep (se 2 (by rfl) ⟨1560876, by rfl⟩ : syracuseStep 4162337 = 3121753) B3121753
theorem B24044323 : Blo 1849626 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B1876879 : Blo 1849626 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B9364409 : Blo 1849626 9364409 := bstep (se 2 (by rfl) ⟨3511653, by rfl⟩ : syracuseStep 9364409 = 7023307) B7023307
theorem B3802145 : Blo 1849626 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B6243371 : Blo 1849626 6243371 := bstep (se 1 (by rfl) ⟨4682528, by rfl⟩ : syracuseStep 6243371 = 9365057) B9365057
theorem B3122219 : Blo 1849626 3122219 := bstep (se 1 (by rfl) ⟨2341664, by rfl⟩ : syracuseStep 3122219 = 4683329) B4683329
theorem B4162679 : Blo 1849626 4162679 := bstep (se 1 (by rfl) ⟨3122009, by rfl⟩ : syracuseStep 4162679 = 6244019) B6244019
theorem B5268665 : Blo 1849626 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B67527917 : Blo 1849626 67527917 := bstep (se 3 (by rfl) ⟨12661484, by rfl⟩ : syracuseStep 67527917 = 25322969) B25322969
theorem B2082055 : Blo 1849626 2082055 := bstep (se 1 (by rfl) ⟨1561541, by rfl⟩ : syracuseStep 2082055 = 3123083) B3123083
theorem B10544417 : Blo 1849626 10544417 := bstep (se 2 (by rfl) ⟨3954156, by rfl⟩ : syracuseStep 10544417 = 7908313) B7908313
theorem B4162859 : Blo 1849626 4162859 := bstep (se 1 (by rfl) ⟨3122144, by rfl⟩ : syracuseStep 4162859 = 6244289) B6244289
theorem B17778055 : Blo 1849626 17778055 := bstep (se 1 (by rfl) ⟨13333541, by rfl⟩ : syracuseStep 17778055 = 26667083) B26667083
theorem B3122617 : Blo 1849626 3122617 := bstep (se 2 (by rfl) ⟨1170981, by rfl⟩ : syracuseStep 3122617 = 2341963) B2341963
theorem B14050745 : Blo 1849626 14050745 := bstep (se 2 (by rfl) ⟨5269029, by rfl⟩ : syracuseStep 14050745 = 10538059) B10538059
theorem B2082235 : Blo 1849626 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B3753515 : Blo 1849626 3753515 := bstep (se 1 (by rfl) ⟨2815136, by rfl⟩ : syracuseStep 3753515 = 5630273) B5630273
theorem B18024001 : Blo 1849626 18024001 := bstep (se 2 (by rfl) ⟨6759000, by rfl⟩ : syracuseStep 18024001 = 13518001) B13518001
theorem B1975951 : Blo 1849626 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B4163219 : Blo 1849626 4163219 := bstep (se 1 (by rfl) ⟨3122414, by rfl⟩ : syracuseStep 4163219 = 6244829) B6244829
theorem B4163273 : Blo 1849626 4163273 := bstep (se 2 (by rfl) ⟨1561227, by rfl⟩ : syracuseStep 4163273 = 3122455) B3122455
theorem B8890145 : Blo 1849626 8890145 := bstep (se 2 (by rfl) ⟨3333804, by rfl⟩ : syracuseStep 8890145 = 6667609) B6667609
theorem B3163963 : Blo 1849626 3163963 := bstep (se 1 (by rfl) ⟨2372972, by rfl⟩ : syracuseStep 3163963 = 4745945) B4745945
theorem B9135931 : Blo 1849626 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B2082703 : Blo 1849626 2082703 := bstep (se 1 (by rfl) ⟨1562027, by rfl⟩ : syracuseStep 2082703 = 3124055) B3124055
theorem B9373643 : Blo 1849626 9373643 := bstep (se 1 (by rfl) ⟨7030232, by rfl⟩ : syracuseStep 9373643 = 14060465) B14060465
theorem B11855933 : Blo 1849626 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B3123319 : Blo 1849626 3123319 := bstep (se 1 (by rfl) ⟨2342489, by rfl⟩ : syracuseStep 3123319 = 4684979) B4684979
theorem B5269657 : Blo 1849626 5269657 := bstep (se 2 (by rfl) ⟨1976121, by rfl⟩ : syracuseStep 5269657 = 3952243) B3952243
theorem B17787053 : Blo 1849626 17787053 := bstep (se 3 (by rfl) ⟨3335072, by rfl⟩ : syracuseStep 17787053 = 6670145) B6670145
theorem B9365705 : Blo 1849626 9365705 := bstep (se 2 (by rfl) ⟨3512139, by rfl⟩ : syracuseStep 9365705 = 7024279) B7024279
theorem B6244667 : Blo 1849626 6244667 := bstep (se 1 (by rfl) ⟨4683500, by rfl⟩ : syracuseStep 6244667 = 9367001) B9367001
theorem B3123515 : Blo 1849626 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B4163975 : Blo 1849626 4163975 := bstep (se 1 (by rfl) ⟨3122981, by rfl⟩ : syracuseStep 4163975 = 6245963) B6245963
theorem B4164155 : Blo 1849626 4164155 := bstep (se 1 (by rfl) ⟨3123116, by rfl⟩ : syracuseStep 4164155 = 6246233) B6246233
theorem B10537559 : Blo 1849626 10537559 := bstep (se 1 (by rfl) ⟨7903169, by rfl⟩ : syracuseStep 10537559 = 15806339) B15806339
theorem B46279349 : Blo 1849626 46279349 := bstep (se 5 (by rfl) ⟨2169344, by rfl⟩ : syracuseStep 46279349 = 4338689) B4338689
theorem B4164281 : Blo 1849626 4164281 := bstep (se 2 (by rfl) ⟨1561605, by rfl⟩ : syracuseStep 4164281 = 3123211) B3123211
theorem B3123913 : Blo 1849626 3123913 := bstep (se 2 (by rfl) ⟨1171467, by rfl⟩ : syracuseStep 3123913 = 2342935) B2342935
theorem B15813377 : Blo 1849626 15813377 := bstep (se 2 (by rfl) ⟨5930016, by rfl⟩ : syracuseStep 15813377 = 11860033) B11860033
theorem B6245153 : Blo 1849626 6245153 := bstep (se 2 (by rfl) ⟨2341932, by rfl⟩ : syracuseStep 6245153 = 4683865) B4683865
theorem B20007755 : Blo 1849626 20007755 := bstep (se 1 (by rfl) ⟨15005816, by rfl⟩ : syracuseStep 20007755 = 30011633) B30011633
theorem B81095539 : Blo 1849626 81095539 := bstep (se 1 (by rfl) ⟨60821654, by rfl⟩ : syracuseStep 81095539 = 121643309) B121643309
theorem B2222983 : Blo 1849626 2222983 := bstep (se 1 (by rfl) ⟨1667237, by rfl⟩ : syracuseStep 2222983 = 3334475) B3334475
theorem B4164623 : Blo 1849626 4164623 := bstep (se 1 (by rfl) ⟨3123467, by rfl⟩ : syracuseStep 4164623 = 6246935) B6246935
theorem B4164641 : Blo 1849626 4164641 := bstep (se 2 (by rfl) ⟨1561740, by rfl⟩ : syracuseStep 4164641 = 3123481) B3123481
theorem B21081221 : Blo 1849626 21081221 := bstep (se 4 (by rfl) ⟨1976364, by rfl⟩ : syracuseStep 21081221 = 3952729) B3952729
theorem B6245747 : Blo 1849626 6245747 := bstep (se 1 (by rfl) ⟨4684310, by rfl⟩ : syracuseStep 6245747 = 9368621) B9368621
theorem B4164983 : Blo 1849626 4164983 := bstep (se 1 (by rfl) ⟨3123737, by rfl⟩ : syracuseStep 4164983 = 6247475) B6247475
theorem B3124615 : Blo 1849626 3124615 := bstep (se 1 (by rfl) ⟨2343461, by rfl⟩ : syracuseStep 3124615 = 4686923) B4686923
theorem B33754553 : Blo 1849626 33754553 := bstep (se 2 (by rfl) ⟨12657957, by rfl⟩ : syracuseStep 33754553 = 25315915) B25315915
theorem B4165163 : Blo 1849626 4165163 := bstep (se 1 (by rfl) ⟨3123872, by rfl⟩ : syracuseStep 4165163 = 6247745) B6247745
theorem B21089969 : Blo 1849626 21089969 := bstep (se 2 (by rfl) ⟨7908738, by rfl⟩ : syracuseStep 21089969 = 15817477) B15817477
theorem B150245077 : Blo 1849626 150245077 := bstep (se 7 (by rfl) ⟨1760684, by rfl⟩ : syracuseStep 150245077 = 3521369) B3521369
theorem B4165523 : Blo 1849626 4165523 := bstep (se 1 (by rfl) ⟨3124142, by rfl⟩ : syracuseStep 4165523 = 6248285) B6248285
theorem B4165577 : Blo 1849626 4165577 := bstep (se 2 (by rfl) ⟨1562091, by rfl⟩ : syracuseStep 4165577 = 3124183) B3124183
theorem B10137565 : Blo 1849626 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B2633735 : Blo 1849626 2633735 := bstep (se 1 (by rfl) ⟨1975301, by rfl⟩ : syracuseStep 2633735 = 3950603) B3950603
theorem B21073931 : Blo 1849626 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B5271581 : Blo 1849626 5271581 := bstep (se 3 (by rfl) ⟨988421, by rfl⟩ : syracuseStep 5271581 = 1976843) B1976843
theorem B40030301 : Blo 1849626 40030301 := bstep (se 3 (by rfl) ⟨7505681, by rfl⟩ : syracuseStep 40030301 = 15011363) B15011363
theorem B10686637 : Blo 1849626 10686637 := bstep (se 3 (by rfl) ⟨2003744, by rfl⟩ : syracuseStep 10686637 = 4007489) B4007489
theorem B4444361 : Blo 1849626 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B84537589 : Blo 1849626 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B11252027 : Blo 1849626 11252027 := bstep (se 1 (by rfl) ⟨8439020, by rfl⟩ : syracuseStep 11252027 = 16878041) B16878041
theorem B4682387 : Blo 1849626 4682387 := bstep (se 1 (by rfl) ⟨3511790, by rfl⟩ : syracuseStep 4682387 = 7023581) B7023581
theorem B5272265 : Blo 1849626 5272265 := bstep (se 2 (by rfl) ⟨1977099, by rfl⟩ : syracuseStep 5272265 = 3954199) B3954199
theorem B10539791 : Blo 1849626 10539791 := bstep (se 1 (by rfl) ⟨7904843, by rfl⟩ : syracuseStep 10539791 = 15809687) B15809687
theorem B7025555 : Blo 1849626 7025555 := bstep (se 1 (by rfl) ⟨5269166, by rfl⟩ : syracuseStep 7025555 = 10538333) B10538333
theorem B4682681 : Blo 1849626 4682681 := bstep (se 2 (by rfl) ⟨1756005, by rfl⟩ : syracuseStep 4682681 = 3512011) B3512011
theorem B4445129 : Blo 1849626 4445129 := bstep (se 2 (by rfl) ⟨1666923, by rfl⟩ : syracuseStep 4445129 = 3333847) B3333847
theorem B2634697 : Blo 1849626 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B25334789 : Blo 1849626 25334789 := bstep (se 4 (by rfl) ⟨2375136, by rfl⟩ : syracuseStep 25334789 = 4750273) B4750273
theorem B10540043 : Blo 1849626 10540043 := bstep (se 1 (by rfl) ⟨7905032, by rfl⟩ : syracuseStep 10540043 = 15810065) B15810065
theorem B14251069 : Blo 1849626 14251069 := bstep (se 3 (by rfl) ⟨2672075, by rfl⟩ : syracuseStep 14251069 = 5344151) B5344151
theorem B6329431 : Blo 1849626 6329431 := bstep (se 1 (by rfl) ⟨4747073, by rfl⟩ : syracuseStep 6329431 = 9494147) B9494147
theorem B5002327 : Blo 1849626 5002327 := bstep (se 1 (by rfl) ⟨3751745, by rfl⟩ : syracuseStep 5002327 = 7503491) B7503491
theorem B60036227 : Blo 1849626 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B2962747 : Blo 1849626 2962747 := bstep (se 1 (by rfl) ⟨2222060, by rfl⟩ : syracuseStep 2962747 = 4444121) B4444121
theorem B5625235 : Blo 1849626 5625235 := bstep (se 1 (by rfl) ⟨4218926, by rfl⟩ : syracuseStep 5625235 = 8437853) B8437853
theorem B2635193 : Blo 1849626 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B2774459 : Blo 1849626 2774459 := bstep (se 1 (by rfl) ⟨2080844, by rfl⟩ : syracuseStep 2774459 = 4161689) B4161689
theorem B11851217 : Blo 1849626 11851217 := bstep (se 2 (by rfl) ⟨4444206, by rfl⟩ : syracuseStep 11851217 = 8888413) B8888413
theorem B2774519 : Blo 1849626 2774519 := bstep (se 1 (by rfl) ⟨2080889, by rfl⟩ : syracuseStep 2774519 = 4161779) B4161779
theorem B2774543 : Blo 1849626 2774543 := bstep (se 1 (by rfl) ⟨2080907, by rfl⟩ : syracuseStep 2774543 = 4161815) B4161815
theorem B2774585 : Blo 1849626 2774585 := bstep (se 2 (by rfl) ⟨1040469, by rfl⟩ : syracuseStep 2774585 = 2080939) B2080939
theorem B4683379 : Blo 1849626 4683379 := bstep (se 1 (by rfl) ⟨3512534, by rfl⟩ : syracuseStep 4683379 = 7025069) B7025069
theorem B3511927 : Blo 1849626 3511927 := bstep (se 1 (by rfl) ⟨2633945, by rfl⟩ : syracuseStep 3511927 = 5267891) B5267891
theorem B2774663 : Blo 1849626 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B2774699 : Blo 1849626 2774699 := bstep (se 1 (by rfl) ⟨2081024, by rfl⟩ : syracuseStep 2774699 = 4162049) B4162049
theorem B2774729 : Blo 1849626 2774729 := bstep (se 2 (by rfl) ⟨1040523, by rfl⟩ : syracuseStep 2774729 = 2081047) B2081047
theorem B16029413 : Blo 1849626 16029413 := bstep (se 4 (by rfl) ⟨1502757, by rfl⟩ : syracuseStep 16029413 = 3005515) B3005515
theorem B4683521 : Blo 1849626 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B2774843 : Blo 1849626 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B2774903 : Blo 1849626 2774903 := bstep (se 1 (by rfl) ⟨2081177, by rfl⟩ : syracuseStep 2774903 = 4162355) B4162355
theorem B5928839 : Blo 1849626 5928839 := bstep (se 1 (by rfl) ⟨4446629, by rfl⟩ : syracuseStep 5928839 = 8893259) B8893259
theorem B2774927 : Blo 1849626 2774927 := bstep (se 1 (by rfl) ⟨2081195, by rfl⟩ : syracuseStep 2774927 = 4162391) B4162391
theorem B6248339 : Blo 1849626 6248339 := bstep (se 1 (by rfl) ⟨4686254, by rfl⟩ : syracuseStep 6248339 = 9372509) B9372509
theorem B2774969 : Blo 1849626 2774969 := bstep (se 2 (by rfl) ⟨1040613, by rfl⟩ : syracuseStep 2774969 = 2081227) B2081227
theorem B5928889 : Blo 1849626 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B8894393 : Blo 1849626 8894393 := bstep (se 2 (by rfl) ⟨3335397, by rfl⟩ : syracuseStep 8894393 = 6670795) B6670795
theorem B10000331 : Blo 1849626 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B8894411 : Blo 1849626 8894411 := bstep (se 1 (by rfl) ⟨6670808, by rfl⟩ : syracuseStep 8894411 = 13341617) B13341617
theorem B35583947 : Blo 1849626 35583947 := bstep (se 1 (by rfl) ⟨26687960, by rfl⟩ : syracuseStep 35583947 = 53375921) B53375921
theorem B2775047 : Blo 1849626 2775047 := bstep (se 1 (by rfl) ⟨2081285, by rfl⟩ : syracuseStep 2775047 = 4162571) B4162571
theorem B2775083 : Blo 1849626 2775083 := bstep (se 1 (by rfl) ⟨2081312, by rfl⟩ : syracuseStep 2775083 = 4162625) B4162625
theorem B2775113 : Blo 1849626 2775113 := bstep (se 2 (by rfl) ⟨1040667, by rfl⟩ : syracuseStep 2775113 = 2081335) B2081335
theorem B2775227 : Blo 1849626 2775227 := bstep (se 1 (by rfl) ⟨2081420, by rfl⟩ : syracuseStep 2775227 = 4162841) B4162841
theorem B10541249 : Blo 1849626 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B4683977 : Blo 1849626 4683977 := bstep (se 2 (by rfl) ⟨1756491, by rfl⟩ : syracuseStep 4683977 = 3512983) B3512983
theorem B2775287 : Blo 1849626 2775287 := bstep (se 1 (by rfl) ⟨2081465, by rfl⟩ : syracuseStep 2775287 = 4162931) B4162931
theorem B2775311 : Blo 1849626 2775311 := bstep (se 1 (by rfl) ⟨2081483, by rfl⟩ : syracuseStep 2775311 = 4162967) B4162967
theorem B2341163 : Blo 1849626 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B2775353 : Blo 1849626 2775353 := bstep (se 2 (by rfl) ⟨1040757, by rfl⟩ : syracuseStep 2775353 = 2081515) B2081515
theorem B1849659 : Blo 1849626 1849659 := bstep (se 1 (by rfl) ⟨1387244, by rfl⟩ : syracuseStep 1849659 = 2774489) B2774489
theorem B1849735 : Blo 1849626 1849735 := bstep (se 1 (by rfl) ⟨1387301, by rfl⟩ : syracuseStep 1849735 = 2774603) B2774603
theorem B2775431 : Blo 1849626 2775431 := bstep (se 1 (by rfl) ⟨2081573, by rfl⟩ : syracuseStep 2775431 = 4163147) B4163147
theorem B2636167 : Blo 1849626 2636167 := bstep (se 1 (by rfl) ⟨1977125, by rfl⟩ : syracuseStep 2636167 = 3954251) B3954251
theorem B1849743 : Blo 1849626 1849743 := bstep (se 1 (by rfl) ⟨1387307, by rfl⟩ : syracuseStep 1849743 = 2774615) B2774615
theorem B7125401 : Blo 1849626 7125401 := bstep (se 2 (by rfl) ⟨2672025, by rfl⟩ : syracuseStep 7125401 = 5344051) B5344051
theorem B2775467 : Blo 1849626 2775467 := bstep (se 1 (by rfl) ⟨2081600, by rfl⟩ : syracuseStep 2775467 = 4163201) B4163201
theorem B1849787 : Blo 1849626 1849787 := bstep (se 1 (by rfl) ⟨1387340, by rfl⟩ : syracuseStep 1849787 = 2774681) B2774681
theorem B2775497 : Blo 1849626 2775497 := bstep (se 2 (by rfl) ⟨1040811, by rfl⟩ : syracuseStep 2775497 = 2081623) B2081623
theorem B18987473 : Blo 1849626 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B1849863 : Blo 1849626 1849863 := bstep (se 1 (by rfl) ⟨1387397, by rfl⟩ : syracuseStep 1849863 = 2774795) B2774795
theorem B1849871 : Blo 1849626 1849871 := bstep (se 1 (by rfl) ⟨1387403, by rfl⟩ : syracuseStep 1849871 = 2774807) B2774807
theorem B4749857 : Blo 1849626 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B4684331 : Blo 1849626 4684331 := bstep (se 1 (by rfl) ⟨3513248, by rfl⟩ : syracuseStep 4684331 = 7026497) B7026497
theorem B1849915 : Blo 1849626 1849915 := bstep (se 1 (by rfl) ⟨1387436, by rfl⟩ : syracuseStep 1849915 = 2774873) B2774873
theorem B2775611 : Blo 1849626 2775611 := bstep (se 1 (by rfl) ⟨2081708, by rfl⟩ : syracuseStep 2775611 = 4163417) B4163417
theorem B14244419 : Blo 1849626 14244419 := bstep (se 1 (by rfl) ⟨10683314, by rfl⟩ : syracuseStep 14244419 = 21366629) B21366629
theorem B2775671 : Blo 1849626 2775671 := bstep (se 1 (by rfl) ⟨2081753, by rfl⟩ : syracuseStep 2775671 = 4163507) B4163507
theorem B1849991 : Blo 1849626 1849991 := bstep (se 1 (by rfl) ⟨1387493, by rfl⟩ : syracuseStep 1849991 = 2774987) B2774987
theorem B1849999 : Blo 1849626 1849999 := bstep (se 1 (by rfl) ⟨1387499, by rfl⟩ : syracuseStep 1849999 = 2774999) B2774999
theorem B2775695 : Blo 1849626 2775695 := bstep (se 1 (by rfl) ⟨2081771, by rfl⟩ : syracuseStep 2775695 = 4163543) B4163543
theorem B10001069 : Blo 1849626 10001069 := bstep (se 3 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 10001069 = 3750401) B3750401
theorem B2775737 : Blo 1849626 2775737 := bstep (se 2 (by rfl) ⟨1040901, by rfl⟩ : syracuseStep 2775737 = 2081803) B2081803
theorem B1850043 : Blo 1849626 1850043 := bstep (se 1 (by rfl) ⟨1387532, by rfl⟩ : syracuseStep 1850043 = 2775065) B2775065
theorem B1850119 : Blo 1849626 1850119 := bstep (se 1 (by rfl) ⟨1387589, by rfl⟩ : syracuseStep 1850119 = 2775179) B2775179
theorem B2341639 : Blo 1849626 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B2775815 : Blo 1849626 2775815 := bstep (se 1 (by rfl) ⟨2081861, by rfl⟩ : syracuseStep 2775815 = 4163723) B4163723
theorem B1850127 : Blo 1849626 1850127 := bstep (se 1 (by rfl) ⟨1387595, by rfl⟩ : syracuseStep 1850127 = 2775191) B2775191
theorem B2775851 : Blo 1849626 2775851 := bstep (se 1 (by rfl) ⟨2081888, by rfl⟩ : syracuseStep 2775851 = 4163777) B4163777
theorem B1850171 : Blo 1849626 1850171 := bstep (se 1 (by rfl) ⟨1387628, by rfl⟩ : syracuseStep 1850171 = 2775257) B2775257
theorem B2775881 : Blo 1849626 2775881 := bstep (se 2 (by rfl) ⟨1040955, by rfl⟩ : syracuseStep 2775881 = 2081911) B2081911
theorem B1850247 : Blo 1849626 1850247 := bstep (se 1 (by rfl) ⟨1387685, by rfl⟩ : syracuseStep 1850247 = 2775371) B2775371
theorem B1850255 : Blo 1849626 1850255 := bstep (se 1 (by rfl) ⟨1387691, by rfl⟩ : syracuseStep 1850255 = 2775383) B2775383
theorem B18987929 : Blo 1849626 18987929 := bstep (se 2 (by rfl) ⟨7120473, by rfl⟩ : syracuseStep 18987929 = 14240947) B14240947
theorem B1850299 : Blo 1849626 1850299 := bstep (se 1 (by rfl) ⟨1387724, by rfl⟩ : syracuseStep 1850299 = 2775449) B2775449
theorem B2775995 : Blo 1849626 2775995 := bstep (se 1 (by rfl) ⟨2081996, by rfl⟩ : syracuseStep 2775995 = 4163993) B4163993
theorem B2776055 : Blo 1849626 2776055 := bstep (se 1 (by rfl) ⟨2082041, by rfl⟩ : syracuseStep 2776055 = 4164083) B4164083
theorem B1850375 : Blo 1849626 1850375 := bstep (se 1 (by rfl) ⟨1387781, by rfl⟩ : syracuseStep 1850375 = 2775563) B2775563
theorem B33782795 : Blo 1849626 33782795 := bstep (se 1 (by rfl) ⟨25337096, by rfl⟩ : syracuseStep 33782795 = 50674193) B50674193
theorem B1850383 : Blo 1849626 1850383 := bstep (se 1 (by rfl) ⟨1387787, by rfl⟩ : syracuseStep 1850383 = 2775575) B2775575
theorem B2776079 : Blo 1849626 2776079 := bstep (se 1 (by rfl) ⟨2082059, by rfl⟩ : syracuseStep 2776079 = 4164119) B4164119
theorem B15817751 : Blo 1849626 15817751 := bstep (se 1 (by rfl) ⟨11863313, by rfl⟩ : syracuseStep 15817751 = 23726627) B23726627
theorem B2776121 : Blo 1849626 2776121 := bstep (se 2 (by rfl) ⟨1041045, by rfl⟩ : syracuseStep 2776121 = 2082091) B2082091
theorem B1850427 : Blo 1849626 1850427 := bstep (se 1 (by rfl) ⟨1387820, by rfl⟩ : syracuseStep 1850427 = 2775641) B2775641
theorem B1850503 : Blo 1849626 1850503 := bstep (se 1 (by rfl) ⟨1387877, by rfl⟩ : syracuseStep 1850503 = 2775755) B2775755
theorem B2776199 : Blo 1849626 2776199 := bstep (se 1 (by rfl) ⟨2082149, by rfl⟩ : syracuseStep 2776199 = 4164299) B4164299
theorem B1850511 : Blo 1849626 1850511 := bstep (se 1 (by rfl) ⟨1387883, by rfl⟩ : syracuseStep 1850511 = 2775767) B2775767
theorem B4447379 : Blo 1849626 4447379 := bstep (se 1 (by rfl) ⟨3335534, by rfl⟩ : syracuseStep 4447379 = 6671069) B6671069
theorem B2776235 : Blo 1849626 2776235 := bstep (se 1 (by rfl) ⟨2082176, by rfl⟩ : syracuseStep 2776235 = 4164353) B4164353
theorem B1850555 : Blo 1849626 1850555 := bstep (se 1 (by rfl) ⟨1387916, by rfl⟩ : syracuseStep 1850555 = 2775833) B2775833
theorem B2776265 : Blo 1849626 2776265 := bstep (se 2 (by rfl) ⟨1041099, by rfl⟩ : syracuseStep 2776265 = 2082199) B2082199
theorem B2342135 : Blo 1849626 2342135 := bstep (se 1 (by rfl) ⟨1756601, by rfl⟩ : syracuseStep 2342135 = 3513203) B3513203
theorem B1850631 : Blo 1849626 1850631 := bstep (se 1 (by rfl) ⟨1387973, by rfl⟩ : syracuseStep 1850631 = 2775947) B2775947
theorem B1850639 : Blo 1849626 1850639 := bstep (se 1 (by rfl) ⟨1387979, by rfl⟩ : syracuseStep 1850639 = 2775959) B2775959
theorem B7503137 : Blo 1849626 7503137 := bstep (se 2 (by rfl) ⟨2813676, by rfl⟩ : syracuseStep 7503137 = 5627353) B5627353
theorem B5930273 : Blo 1849626 5930273 := bstep (se 2 (by rfl) ⟨2223852, by rfl⟩ : syracuseStep 5930273 = 4447705) B4447705
theorem B1850683 : Blo 1849626 1850683 := bstep (se 1 (by rfl) ⟨1388012, by rfl⟩ : syracuseStep 1850683 = 2776025) B2776025
theorem B2776379 : Blo 1849626 2776379 := bstep (se 1 (by rfl) ⟨2082284, by rfl⟩ : syracuseStep 2776379 = 4164569) B4164569
theorem B38493539 : Blo 1849626 38493539 := bstep (se 1 (by rfl) ⟨28870154, by rfl⟩ : syracuseStep 38493539 = 57740309) B57740309
theorem B3513719 : Blo 1849626 3513719 := bstep (se 1 (by rfl) ⟨2635289, by rfl⟩ : syracuseStep 3513719 = 5270579) B5270579
theorem B2776439 : Blo 1849626 2776439 := bstep (se 1 (by rfl) ⟨2082329, by rfl⟩ : syracuseStep 2776439 = 4164659) B4164659
theorem B1850759 : Blo 1849626 1850759 := bstep (se 1 (by rfl) ⟨1388069, by rfl⟩ : syracuseStep 1850759 = 2776139) B2776139
theorem B2342287 : Blo 1849626 2342287 := bstep (se 1 (by rfl) ⟨1756715, by rfl⟩ : syracuseStep 2342287 = 3513431) B3513431
theorem B1850767 : Blo 1849626 1850767 := bstep (se 1 (by rfl) ⟨1388075, by rfl⟩ : syracuseStep 1850767 = 2776151) B2776151
theorem B2776463 : Blo 1849626 2776463 := bstep (se 1 (by rfl) ⟨2082347, by rfl⟩ : syracuseStep 2776463 = 4164695) B4164695
theorem B2776505 : Blo 1849626 2776505 := bstep (se 2 (by rfl) ⟨1041189, by rfl⟩ : syracuseStep 2776505 = 2082379) B2082379
theorem B7028153 : Blo 1849626 7028153 := bstep (se 2 (by rfl) ⟨2635557, by rfl⟩ : syracuseStep 7028153 = 5271115) B5271115
theorem B1850811 : Blo 1849626 1850811 := bstep (se 1 (by rfl) ⟨1388108, by rfl⟩ : syracuseStep 1850811 = 2776217) B2776217
theorem B1850887 : Blo 1849626 1850887 := bstep (se 1 (by rfl) ⟨1388165, by rfl⟩ : syracuseStep 1850887 = 2776331) B2776331
theorem B2776583 : Blo 1849626 2776583 := bstep (se 1 (by rfl) ⟨2082437, by rfl⟩ : syracuseStep 2776583 = 4164875) B4164875
theorem B4685323 : Blo 1849626 4685323 := bstep (se 1 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 4685323 = 7027985) B7027985
theorem B1850895 : Blo 1849626 1850895 := bstep (se 1 (by rfl) ⟨1388171, by rfl⟩ : syracuseStep 1850895 = 2776343) B2776343
theorem B3513871 : Blo 1849626 3513871 := bstep (se 1 (by rfl) ⟨2635403, by rfl⟩ : syracuseStep 3513871 = 5270807) B5270807
theorem B2776619 : Blo 1849626 2776619 := bstep (se 1 (by rfl) ⟨2082464, by rfl⟩ : syracuseStep 2776619 = 4164929) B4164929
theorem B2342459 : Blo 1849626 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B1850939 : Blo 1849626 1850939 := bstep (se 1 (by rfl) ⟨1388204, by rfl⟩ : syracuseStep 1850939 = 2776409) B2776409
theorem B2776649 : Blo 1849626 2776649 := bstep (se 2 (by rfl) ⟨1041243, by rfl⟩ : syracuseStep 2776649 = 2082487) B2082487
theorem B7503479 : Blo 1849626 7503479 := bstep (se 1 (by rfl) ⟨5627609, by rfl⟩ : syracuseStep 7503479 = 11255219) B11255219
theorem B1851015 : Blo 1849626 1851015 := bstep (se 1 (by rfl) ⟨1388261, by rfl⟩ : syracuseStep 1851015 = 2776523) B2776523
theorem B1851023 : Blo 1849626 1851023 := bstep (se 1 (by rfl) ⟨1388267, by rfl⟩ : syracuseStep 1851023 = 2776535) B2776535
theorem B4685465 : Blo 1849626 4685465 := bstep (se 2 (by rfl) ⟨1757049, by rfl⟩ : syracuseStep 4685465 = 3514099) B3514099
theorem B1851067 : Blo 1849626 1851067 := bstep (se 1 (by rfl) ⟨1388300, by rfl⟩ : syracuseStep 1851067 = 2776601) B2776601
theorem B2776763 : Blo 1849626 2776763 := bstep (se 1 (by rfl) ⟨2082572, by rfl⟩ : syracuseStep 2776763 = 4165145) B4165145
theorem B2776823 : Blo 1849626 2776823 := bstep (se 1 (by rfl) ⟨2082617, by rfl⟩ : syracuseStep 2776823 = 4165235) B4165235
theorem B1875719 : Blo 1849626 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B1851143 : Blo 1849626 1851143 := bstep (se 1 (by rfl) ⟨1388357, by rfl⟩ : syracuseStep 1851143 = 2776715) B2776715
theorem B1851151 : Blo 1849626 1851151 := bstep (se 1 (by rfl) ⟨1388363, by rfl⟩ : syracuseStep 1851151 = 2776727) B2776727
theorem B2776847 : Blo 1849626 2776847 := bstep (se 1 (by rfl) ⟨2082635, by rfl⟩ : syracuseStep 2776847 = 4165271) B4165271
theorem B2776889 : Blo 1849626 2776889 := bstep (se 2 (by rfl) ⟨1041333, by rfl⟩ : syracuseStep 2776889 = 2082667) B2082667
theorem B4685627 : Blo 1849626 4685627 := bstep (se 1 (by rfl) ⟨3514220, by rfl⟩ : syracuseStep 4685627 = 7028441) B7028441
theorem B1851195 : Blo 1849626 1851195 := bstep (se 1 (by rfl) ⟨1388396, by rfl⟩ : syracuseStep 1851195 = 2776793) B2776793
theorem B2965367 : Blo 1849626 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B8011655 : Blo 1849626 8011655 := bstep (se 1 (by rfl) ⟨6008741, by rfl⟩ : syracuseStep 8011655 = 12017483) B12017483
theorem B1851271 : Blo 1849626 1851271 := bstep (se 1 (by rfl) ⟨1388453, by rfl⟩ : syracuseStep 1851271 = 2776907) B2776907
theorem B2776967 : Blo 1849626 2776967 := bstep (se 1 (by rfl) ⟨2082725, by rfl⟩ : syracuseStep 2776967 = 4165451) B4165451
theorem B1851279 : Blo 1849626 1851279 := bstep (se 1 (by rfl) ⟨1388459, by rfl⟩ : syracuseStep 1851279 = 2776919) B2776919
theorem B9371537 : Blo 1849626 9371537 := bstep (se 2 (by rfl) ⟨3514326, by rfl⟩ : syracuseStep 9371537 = 7028653) B7028653
theorem B3514259 : Blo 1849626 3514259 := bstep (se 1 (by rfl) ⟨2635694, by rfl⟩ : syracuseStep 3514259 = 5271389) B5271389
theorem B8896409 : Blo 1849626 8896409 := bstep (se 2 (by rfl) ⟨3336153, by rfl⟩ : syracuseStep 8896409 = 6672307) B6672307
theorem B2777003 : Blo 1849626 2777003 := bstep (se 1 (by rfl) ⟨2082752, by rfl⟩ : syracuseStep 2777003 = 4165505) B4165505
theorem B1851323 : Blo 1849626 1851323 := bstep (se 1 (by rfl) ⟨1388492, by rfl⟩ : syracuseStep 1851323 = 2776985) B2776985
theorem B2777033 : Blo 1849626 2777033 := bstep (se 2 (by rfl) ⟨1041387, by rfl⟩ : syracuseStep 2777033 = 2082775) B2082775
theorem B14049287 : Blo 1849626 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B67559437 : Blo 1849626 67559437 := bstep (se 3 (by rfl) ⟨12667394, by rfl⟩ : syracuseStep 67559437 = 25334789) B25334789
theorem B1851431 : Blo 1849626 1851431 := bstep (se 1 (by rfl) ⟨1388573, by rfl⟩ : syracuseStep 1851431 = 2777147) B2777147
theorem B14057549 : Blo 1849626 14057549 := bstep (se 3 (by rfl) ⟨2635790, by rfl⟩ : syracuseStep 14057549 = 5271581) B5271581
theorem B1851471 : Blo 1849626 1851471 := bstep (se 1 (by rfl) ⟨1388603, by rfl⟩ : syracuseStep 1851471 = 2777207) B2777207
theorem B1851487 : Blo 1849626 1851487 := bstep (se 1 (by rfl) ⟨1388615, by rfl⟩ : syracuseStep 1851487 = 2777231) B2777231
theorem B1851515 : Blo 1849626 1851515 := bstep (se 1 (by rfl) ⟨1388636, by rfl⟩ : syracuseStep 1851515 = 2777273) B2777273
theorem B51364003 : Blo 1849626 51364003 := bstep (se 1 (by rfl) ⟨38523002, by rfl⟩ : syracuseStep 51364003 = 77046005) B77046005
theorem B4161707 : Blo 1849626 4161707 := bstep (se 1 (by rfl) ⟨3121280, by rfl⟩ : syracuseStep 4161707 = 6242561) B6242561
theorem B2965675 : Blo 1849626 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B1851567 : Blo 1849626 1851567 := bstep (se 1 (by rfl) ⟨1388675, by rfl⟩ : syracuseStep 1851567 = 2777351) B2777351
theorem B3752135 : Blo 1849626 3752135 := bstep (se 1 (by rfl) ⟨2814101, by rfl⟩ : syracuseStep 3752135 = 5628203) B5628203
theorem B1851591 : Blo 1849626 1851591 := bstep (se 1 (by rfl) ⟨1388693, by rfl⟩ : syracuseStep 1851591 = 2777387) B2777387
theorem B1851611 : Blo 1849626 1851611 := bstep (se 1 (by rfl) ⟨1388708, by rfl⟩ : syracuseStep 1851611 = 2777417) B2777417
theorem B17776907 : Blo 1849626 17776907 := bstep (se 1 (by rfl) ⟨13332680, by rfl⟩ : syracuseStep 17776907 = 26665361) B26665361
theorem B76005701 : Blo 1849626 76005701 := bstep (se 4 (by rfl) ⟨7125534, by rfl⟩ : syracuseStep 76005701 = 14251069) B14251069
theorem B2081119 : Blo 1849626 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B3121591 : Blo 1849626 3121591 := bstep (se 1 (by rfl) ⟨2341193, by rfl⟩ : syracuseStep 3121591 = 4682387) B4682387
theorem B3514843 : Blo 1849626 3514843 := bstep (se 1 (by rfl) ⟨2636132, by rfl⟩ : syracuseStep 3514843 = 5272265) B5272265
theorem B14049773 : Blo 1849626 14049773 := bstep (se 3 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 14049773 = 5268665) B5268665
theorem B3514889 : Blo 1849626 3514889 := bstep (se 2 (by rfl) ⟨1318083, by rfl⟩ : syracuseStep 3514889 = 2636167) B2636167
theorem B9372185 : Blo 1849626 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B6242939 : Blo 1849626 6242939 := bstep (se 1 (by rfl) ⟨4682204, by rfl⟩ : syracuseStep 6242939 = 9364409) B9364409
theorem B3121787 : Blo 1849626 3121787 := bstep (se 1 (by rfl) ⟨2341340, by rfl⟩ : syracuseStep 3121787 = 4682681) B4682681
theorem B4162247 : Blo 1849626 4162247 := bstep (se 1 (by rfl) ⟨3121685, by rfl⟩ : syracuseStep 4162247 = 6243371) B6243371
theorem B2081479 : Blo 1849626 2081479 := bstep (se 1 (by rfl) ⟨1561109, by rfl⟩ : syracuseStep 2081479 = 3122219) B3122219
theorem B6243101 : Blo 1849626 6243101 := bstep (se 3 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 6243101 = 2341163) B2341163
theorem B7029611 : Blo 1849626 7029611 := bstep (se 1 (by rfl) ⟨5272208, by rfl⟩ : syracuseStep 7029611 = 10544417) B10544417
theorem B3122185 : Blo 1849626 3122185 := bstep (se 2 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 3122185 = 2341639) B2341639
theorem B108127385 : Blo 1849626 108127385 := bstep (se 2 (by rfl) ⟨40547769, by rfl⟩ : syracuseStep 108127385 = 81095539) B81095539
theorem B3122347 : Blo 1849626 3122347 := bstep (se 1 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 3122347 = 4683521) B4683521
theorem B8439241 : Blo 1849626 8439241 := bstep (se 2 (by rfl) ⟨3164715, by rfl⟩ : syracuseStep 8439241 = 6329431) B6329431
theorem B6243803 : Blo 1849626 6243803 := bstep (se 1 (by rfl) ⟨4682852, by rfl⟩ : syracuseStep 6243803 = 9365705) B9365705
theorem B3122651 : Blo 1849626 3122651 := bstep (se 1 (by rfl) ⟨2341988, by rfl⟩ : syracuseStep 3122651 = 4683977) B4683977
theorem B4163111 : Blo 1849626 4163111 := bstep (se 1 (by rfl) ⟨3122333, by rfl⟩ : syracuseStep 4163111 = 6244667) B6244667
theorem B2082343 : Blo 1849626 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B12658315 : Blo 1849626 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B3122887 : Blo 1849626 3122887 := bstep (se 1 (by rfl) ⟨2342165, by rfl⟩ : syracuseStep 3122887 = 4684331) B4684331
theorem B9496279 : Blo 1849626 9496279 := bstep (se 1 (by rfl) ⟨7122209, by rfl⟩ : syracuseStep 9496279 = 14244419) B14244419
theorem B30852899 : Blo 1849626 30852899 := bstep (se 1 (by rfl) ⟨23139674, by rfl⟩ : syracuseStep 30852899 = 46279349) B46279349
theorem B3123049 : Blo 1849626 3123049 := bstep (se 2 (by rfl) ⟨1171143, by rfl⟩ : syracuseStep 3123049 = 2342287) B2342287
theorem B4163435 : Blo 1849626 4163435 := bstep (se 1 (by rfl) ⟨3122576, by rfl⟩ : syracuseStep 4163435 = 6245153) B6245153
theorem B13338503 : Blo 1849626 13338503 := bstep (se 1 (by rfl) ⟨10003877, by rfl⟩ : syracuseStep 13338503 = 20007755) B20007755
theorem B4163489 : Blo 1849626 4163489 := bstep (se 2 (by rfl) ⟨1561308, by rfl⟩ : syracuseStep 4163489 = 3122617) B3122617
theorem B12658619 : Blo 1849626 12658619 := bstep (se 1 (by rfl) ⟨9493964, by rfl⟩ : syracuseStep 12658619 = 18987929) B18987929
theorem B22521863 : Blo 1849626 22521863 := bstep (se 1 (by rfl) ⟨16891397, by rfl⟩ : syracuseStep 22521863 = 33782795) B33782795
theorem B10545167 : Blo 1849626 10545167 := bstep (se 1 (by rfl) ⟨7908875, by rfl⟩ : syracuseStep 10545167 = 15817751) B15817751
theorem B11855909 : Blo 1849626 11855909 := bstep (se 4 (by rfl) ⟨1111491, by rfl⟩ : syracuseStep 11855909 = 2222983) B2222983
theorem B6244505 : Blo 1849626 6244505 := bstep (se 2 (by rfl) ⟨2341689, by rfl⟩ : syracuseStep 6244505 = 4683379) B4683379
theorem B4163831 : Blo 1849626 4163831 := bstep (se 1 (by rfl) ⟨3122873, by rfl⟩ : syracuseStep 4163831 = 6245747) B6245747
theorem B7907645 : Blo 1849626 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B14051717 : Blo 1849626 14051717 := bstep (se 4 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 14051717 = 2634697) B2634697
theorem B3123643 : Blo 1849626 3123643 := bstep (se 1 (by rfl) ⟨2342732, by rfl⟩ : syracuseStep 3123643 = 4685465) B4685465
theorem B14059979 : Blo 1849626 14059979 := bstep (se 1 (by rfl) ⟨10544984, by rfl⟩ : syracuseStep 14059979 = 21089969) B21089969
theorem B3123751 : Blo 1849626 3123751 := bstep (se 1 (by rfl) ⟨2342813, by rfl⟩ : syracuseStep 3123751 = 4685627) B4685627
theorem B7023293 : Blo 1849626 7023293 := bstep (se 3 (by rfl) ⟨1316867, by rfl⟩ : syracuseStep 7023293 = 2633735) B2633735
theorem B1977031 : Blo 1849626 1977031 := bstep (se 1 (by rfl) ⟨1482773, by rfl⟩ : syracuseStep 1977031 = 2965547) B2965547
theorem B4164425 : Blo 1849626 4164425 := bstep (se 2 (by rfl) ⟨1561659, by rfl⟩ : syracuseStep 4164425 = 3123319) B3123319
theorem B14052203 : Blo 1849626 14052203 := bstep (se 1 (by rfl) ⟨10539152, by rfl⟩ : syracuseStep 14052203 = 21078305) B21078305
theorem B3124075 : Blo 1849626 3124075 := bstep (se 1 (by rfl) ⟨2343056, by rfl⟩ : syracuseStep 3124075 = 4686113) B4686113
theorem B112716785 : Blo 1849626 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B6245693 : Blo 1849626 6245693 := bstep (se 3 (by rfl) ⟨1171067, by rfl⟩ : syracuseStep 6245693 = 2342135) B2342135
theorem B15814061 : Blo 1849626 15814061 := bstep (se 3 (by rfl) ⟨2965136, by rfl⟩ : syracuseStep 15814061 = 5930273) B5930273
theorem B45018611 : Blo 1849626 45018611 := bstep (se 1 (by rfl) ⟨33763958, by rfl⟩ : syracuseStep 45018611 = 67527917) B67527917
theorem B56995397 : Blo 1849626 56995397 := bstep (se 4 (by rfl) ⟨5343318, by rfl⟩ : syracuseStep 56995397 = 10686637) B10686637
theorem B4165217 : Blo 1849626 4165217 := bstep (se 2 (by rfl) ⟨1561956, by rfl⟩ : syracuseStep 4165217 = 3123913) B3123913
theorem B9367163 : Blo 1849626 9367163 := bstep (se 1 (by rfl) ⟨7025372, by rfl⟩ : syracuseStep 9367163 = 14050745) B14050745
theorem B7900811 : Blo 1849626 7900811 := bstep (se 1 (by rfl) ⟨5925608, by rfl⟩ : syracuseStep 7900811 = 11851217) B11851217
theorem B11251345 : Blo 1849626 11251345 := bstep (se 2 (by rfl) ⟨4219254, by rfl⟩ : syracuseStep 11251345 = 8438509) B8438509
theorem B2502343 : Blo 1849626 2502343 := bstep (se 1 (by rfl) ⟨1876757, by rfl⟩ : syracuseStep 2502343 = 3753515) B3753515
theorem B32059097 : Blo 1849626 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B10686275 : Blo 1849626 10686275 := bstep (se 1 (by rfl) ⟨8014706, by rfl⟩ : syracuseStep 10686275 = 16029413) B16029413
theorem B2502505 : Blo 1849626 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B5926763 : Blo 1849626 5926763 := bstep (se 1 (by rfl) ⟨4445072, by rfl⟩ : syracuseStep 5926763 = 8890145) B8890145
theorem B3952559 : Blo 1849626 3952559 := bstep (se 1 (by rfl) ⟨2964419, by rfl⟩ : syracuseStep 3952559 = 5928839) B5928839
theorem B4165559 : Blo 1849626 4165559 := bstep (se 1 (by rfl) ⟨3124169, by rfl⟩ : syracuseStep 4165559 = 6248339) B6248339
theorem B384512021 : Blo 1849626 384512021 := bstep (se 6 (by rfl) ⟨9012000, by rfl⟩ : syracuseStep 384512021 = 18024001) B18024001
theorem B11858035 : Blo 1849626 11858035 := bstep (se 1 (by rfl) ⟨8893526, by rfl⟩ : syracuseStep 11858035 = 17787053) B17787053
theorem B6246557 : Blo 1849626 6246557 := bstep (se 3 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 6246557 = 2342459) B2342459
theorem B3166571 : Blo 1849626 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B7025039 : Blo 1849626 7025039 := bstep (se 1 (by rfl) ⟨5268779, by rfl⟩ : syracuseStep 7025039 = 10537559) B10537559
theorem B23704073 : Blo 1849626 23704073 := bstep (se 2 (by rfl) ⟨8889027, by rfl⟩ : syracuseStep 23704073 = 17778055) B17778055
theorem B4166153 : Blo 1849626 4166153 := bstep (se 2 (by rfl) ⟨1562307, by rfl⟩ : syracuseStep 4166153 = 3124615) B3124615
theorem B7500313 : Blo 1849626 7500313 := bstep (se 2 (by rfl) ⟨2812617, by rfl⟩ : syracuseStep 7500313 = 5625235) B5625235
theorem B6247097 : Blo 1849626 6247097 := bstep (se 2 (by rfl) ⟨2342661, by rfl⟩ : syracuseStep 6247097 = 4685323) B4685323
theorem B5001917 : Blo 1849626 5001917 := bstep (se 3 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 5001917 = 1875719) B1875719
theorem B14054147 : Blo 1849626 14054147 := bstep (se 1 (by rfl) ⟨10540610, by rfl⟩ : syracuseStep 14054147 = 21081221) B21081221
theorem B4682569 : Blo 1849626 4682569 := bstep (se 2 (by rfl) ⟨1755963, by rfl⟩ : syracuseStep 4682569 = 3511927) B3511927
theorem B2634601 : Blo 1849626 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B5002091 : Blo 1849626 5002091 := bstep (se 1 (by rfl) ⟨3751568, by rfl⟩ : syracuseStep 5002091 = 7503137) B7503137
theorem B25662359 : Blo 1849626 25662359 := bstep (se 1 (by rfl) ⟨19246769, by rfl⟩ : syracuseStep 25662359 = 38493539) B38493539
theorem B5002319 : Blo 1849626 5002319 := bstep (se 1 (by rfl) ⟨3751739, by rfl⟩ : syracuseStep 5002319 = 7503479) B7503479
theorem B6247691 : Blo 1849626 6247691 := bstep (se 1 (by rfl) ⟨4685768, by rfl⟩ : syracuseStep 6247691 = 9371537) B9371537
theorem B26686867 : Blo 1849626 26686867 := bstep (se 1 (by rfl) ⟨20015150, by rfl⟩ : syracuseStep 26686867 = 40030301) B40030301
theorem B10139053 : Blo 1849626 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B2774447 : Blo 1849626 2774447 := bstep (se 1 (by rfl) ⟨2080835, by rfl⟩ : syracuseStep 2774447 = 4161671) B4161671
theorem B2962907 : Blo 1849626 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B2774537 : Blo 1849626 2774537 := bstep (se 2 (by rfl) ⟨1040451, by rfl⟩ : syracuseStep 2774537 = 2080903) B2080903
theorem B6247961 : Blo 1849626 6247961 := bstep (se 2 (by rfl) ⟨2342985, by rfl⟩ : syracuseStep 6247961 = 4685971) B4685971
theorem B7026209 : Blo 1849626 7026209 := bstep (se 2 (by rfl) ⟨2634828, by rfl⟩ : syracuseStep 7026209 = 5269657) B5269657
theorem B2774567 : Blo 1849626 2774567 := bstep (se 1 (by rfl) ⟨2080925, by rfl⟩ : syracuseStep 2774567 = 4161851) B4161851
theorem B7501351 : Blo 1849626 7501351 := bstep (se 1 (by rfl) ⟨5626013, by rfl⟩ : syracuseStep 7501351 = 11252027) B11252027
theorem B2774651 : Blo 1849626 2774651 := bstep (se 1 (by rfl) ⟨2080988, by rfl⟩ : syracuseStep 2774651 = 4161977) B4161977
theorem B2774777 : Blo 1849626 2774777 := bstep (se 2 (by rfl) ⟨1040541, by rfl⟩ : syracuseStep 2774777 = 2081083) B2081083
theorem B10540793 : Blo 1849626 10540793 := bstep (se 2 (by rfl) ⟨3952797, by rfl⟩ : syracuseStep 10540793 = 7905595) B7905595
theorem B26679077 : Blo 1849626 26679077 := bstep (se 4 (by rfl) ⟨2501163, by rfl⟩ : syracuseStep 26679077 = 5002327) B5002327
theorem B2774879 : Blo 1849626 2774879 := bstep (se 1 (by rfl) ⟨2081159, by rfl⟩ : syracuseStep 2774879 = 4162319) B4162319
theorem B7026527 : Blo 1849626 7026527 := bstep (se 1 (by rfl) ⟨5269895, by rfl⟩ : syracuseStep 7026527 = 10539791) B10539791
theorem B2774891 : Blo 1849626 2774891 := bstep (se 1 (by rfl) ⟨2081168, by rfl⟩ : syracuseStep 2774891 = 4162337) B4162337
theorem B4683703 : Blo 1849626 4683703 := bstep (se 1 (by rfl) ⟨3512777, by rfl⟩ : syracuseStep 4683703 = 7025555) B7025555
theorem B7026695 : Blo 1849626 7026695 := bstep (se 1 (by rfl) ⟨5270021, by rfl⟩ : syracuseStep 7026695 = 10540043) B10540043
theorem B2775119 : Blo 1849626 2775119 := bstep (se 1 (by rfl) ⟨2081339, by rfl⟩ : syracuseStep 2775119 = 4162679) B4162679
theorem B40024151 : Blo 1849626 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B2775239 : Blo 1849626 2775239 := bstep (se 1 (by rfl) ⟨2081429, by rfl⟩ : syracuseStep 2775239 = 4162859) B4162859
theorem B1849639 : Blo 1849626 1849639 := bstep (se 1 (by rfl) ⟨1387229, by rfl⟩ : syracuseStep 1849639 = 2774459) B2774459
theorem B9369917 : Blo 1849626 9369917 := bstep (se 3 (by rfl) ⟨1756859, by rfl⟩ : syracuseStep 9369917 = 3513719) B3513719
theorem B1849679 : Blo 1849626 1849679 := bstep (se 1 (by rfl) ⟨1387259, by rfl⟩ : syracuseStep 1849679 = 2774519) B2774519
theorem B1849695 : Blo 1849626 1849695 := bstep (se 1 (by rfl) ⟨1387271, by rfl⟩ : syracuseStep 1849695 = 2774543) B2774543
theorem B2775401 : Blo 1849626 2775401 := bstep (se 2 (by rfl) ⟨1040775, by rfl⟩ : syracuseStep 2775401 = 2081551) B2081551
theorem B1849723 : Blo 1849626 1849723 := bstep (se 1 (by rfl) ⟨1387292, by rfl⟩ : syracuseStep 1849723 = 2774585) B2774585
theorem B1849775 : Blo 1849626 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B2775479 : Blo 1849626 2775479 := bstep (se 1 (by rfl) ⟨2081609, by rfl⟩ : syracuseStep 2775479 = 4163219) B4163219
theorem B1849799 : Blo 1849626 1849799 := bstep (se 1 (by rfl) ⟨1387349, by rfl⟩ : syracuseStep 1849799 = 2774699) B2774699
theorem B1849819 : Blo 1849626 1849819 := bstep (se 1 (by rfl) ⟨1387364, by rfl⟩ : syracuseStep 1849819 = 2774729) B2774729
theorem B2775515 : Blo 1849626 2775515 := bstep (se 1 (by rfl) ⟨2081636, by rfl⟩ : syracuseStep 2775515 = 4163273) B4163273
theorem B7027181 : Blo 1849626 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B1849895 : Blo 1849626 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B1849935 : Blo 1849626 1849935 := bstep (se 1 (by rfl) ⟨1387451, by rfl⟩ : syracuseStep 1849935 = 2774903) B2774903
theorem B1849951 : Blo 1849626 1849951 := bstep (se 1 (by rfl) ⟨1387463, by rfl⟩ : syracuseStep 1849951 = 2774927) B2774927
theorem B1849979 : Blo 1849626 1849979 := bstep (se 1 (by rfl) ⟨1387484, by rfl⟩ : syracuseStep 1849979 = 2774969) B2774969
theorem B5929595 : Blo 1849626 5929595 := bstep (se 1 (by rfl) ⟨4447196, by rfl⟩ : syracuseStep 5929595 = 8894393) B8894393
theorem B6666887 : Blo 1849626 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B5929607 : Blo 1849626 5929607 := bstep (se 1 (by rfl) ⟨4447205, by rfl⟩ : syracuseStep 5929607 = 8894411) B8894411
theorem B23722631 : Blo 1849626 23722631 := bstep (se 1 (by rfl) ⟨17791973, by rfl⟩ : syracuseStep 23722631 = 35583947) B35583947
theorem B6249095 : Blo 1849626 6249095 := bstep (se 1 (by rfl) ⟨4686821, by rfl⟩ : syracuseStep 6249095 = 9373643) B9373643
theorem B1850031 : Blo 1849626 1850031 := bstep (se 1 (by rfl) ⟨1387523, by rfl⟩ : syracuseStep 1850031 = 2775047) B2775047
theorem B6249149 : Blo 1849626 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B1850055 : Blo 1849626 1850055 := bstep (se 1 (by rfl) ⟨1387541, by rfl⟩ : syracuseStep 1850055 = 2775083) B2775083
theorem B7903955 : Blo 1849626 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B1850075 : Blo 1849626 1850075 := bstep (se 1 (by rfl) ⟨1387556, by rfl⟩ : syracuseStep 1850075 = 2775113) B2775113
theorem B1850151 : Blo 1849626 1850151 := bstep (se 1 (by rfl) ⟨1387613, by rfl⟩ : syracuseStep 1850151 = 2775227) B2775227
theorem B7027499 : Blo 1849626 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B1850191 : Blo 1849626 1850191 := bstep (se 1 (by rfl) ⟨1387643, by rfl⟩ : syracuseStep 1850191 = 2775287) B2775287
theorem B1850207 : Blo 1849626 1850207 := bstep (se 1 (by rfl) ⟨1387655, by rfl⟩ : syracuseStep 1850207 = 2775311) B2775311
theorem B1850235 : Blo 1849626 1850235 := bstep (se 1 (by rfl) ⟨1387676, by rfl⟩ : syracuseStep 1850235 = 2775353) B2775353
theorem B1850287 : Blo 1849626 1850287 := bstep (se 1 (by rfl) ⟨1387715, by rfl⟩ : syracuseStep 1850287 = 2775431) B2775431
theorem B2775983 : Blo 1849626 2775983 := bstep (se 1 (by rfl) ⟨2081987, by rfl⟩ : syracuseStep 2775983 = 4163975) B4163975
theorem B4750267 : Blo 1849626 4750267 := bstep (se 1 (by rfl) ⟨3562700, by rfl⟩ : syracuseStep 4750267 = 7125401) B7125401
theorem B1850311 : Blo 1849626 1850311 := bstep (se 1 (by rfl) ⟨1387733, by rfl⟩ : syracuseStep 1850311 = 2775467) B2775467
theorem B1850331 : Blo 1849626 1850331 := bstep (se 1 (by rfl) ⟨1387748, by rfl⟩ : syracuseStep 1850331 = 2775497) B2775497
theorem B15801317 : Blo 1849626 15801317 := bstep (se 4 (by rfl) ⟨1481373, by rfl⟩ : syracuseStep 15801317 = 2962747) B2962747
theorem B2776073 : Blo 1849626 2776073 := bstep (se 2 (by rfl) ⟨1041027, by rfl⟩ : syracuseStep 2776073 = 2082055) B2082055
theorem B1850407 : Blo 1849626 1850407 := bstep (se 1 (by rfl) ⟨1387805, by rfl⟩ : syracuseStep 1850407 = 2775611) B2775611
theorem B2776103 : Blo 1849626 2776103 := bstep (se 1 (by rfl) ⟨2082077, by rfl⟩ : syracuseStep 2776103 = 4164155) B4164155
theorem B1850447 : Blo 1849626 1850447 := bstep (se 1 (by rfl) ⟨1387835, by rfl⟩ : syracuseStep 1850447 = 2775671) B2775671
theorem B1850463 : Blo 1849626 1850463 := bstep (se 1 (by rfl) ⟨1387847, by rfl⟩ : syracuseStep 1850463 = 2775695) B2775695
theorem B6667379 : Blo 1849626 6667379 := bstep (se 1 (by rfl) ⟨5000534, by rfl⟩ : syracuseStep 6667379 = 10001069) B10001069
theorem B1850491 : Blo 1849626 1850491 := bstep (se 1 (by rfl) ⟨1387868, by rfl⟩ : syracuseStep 1850491 = 2775737) B2775737
theorem B2776187 : Blo 1849626 2776187 := bstep (se 1 (by rfl) ⟨2082140, by rfl⟩ : syracuseStep 2776187 = 4164281) B4164281
theorem B10542251 : Blo 1849626 10542251 := bstep (se 1 (by rfl) ⟨7906688, by rfl⟩ : syracuseStep 10542251 = 15813377) B15813377
theorem B1850543 : Blo 1849626 1850543 := bstep (se 1 (by rfl) ⟨1387907, by rfl⟩ : syracuseStep 1850543 = 2775815) B2775815
theorem B1850567 : Blo 1849626 1850567 := bstep (se 1 (by rfl) ⟨1387925, by rfl⟩ : syracuseStep 1850567 = 2775851) B2775851
theorem B1850587 : Blo 1849626 1850587 := bstep (se 1 (by rfl) ⟨1387940, by rfl⟩ : syracuseStep 1850587 = 2775881) B2775881
theorem B2776313 : Blo 1849626 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B1850663 : Blo 1849626 1850663 := bstep (se 1 (by rfl) ⟨1387997, by rfl⟩ : syracuseStep 1850663 = 2775995) B2775995
theorem B1850703 : Blo 1849626 1850703 := bstep (se 1 (by rfl) ⟨1388027, by rfl⟩ : syracuseStep 1850703 = 2776055) B2776055
theorem B1850719 : Blo 1849626 1850719 := bstep (se 1 (by rfl) ⟨1388039, by rfl⟩ : syracuseStep 1850719 = 2776079) B2776079
theorem B2776415 : Blo 1849626 2776415 := bstep (se 1 (by rfl) ⟨2082311, by rfl⟩ : syracuseStep 2776415 = 4164623) B4164623
theorem B4685161 : Blo 1849626 4685161 := bstep (se 2 (by rfl) ⟨1756935, by rfl⟩ : syracuseStep 4685161 = 3513871) B3513871
theorem B2776427 : Blo 1849626 2776427 := bstep (se 1 (by rfl) ⟨2082320, by rfl⟩ : syracuseStep 2776427 = 4164641) B4164641
theorem B1850747 : Blo 1849626 1850747 := bstep (se 1 (by rfl) ⟨1388060, by rfl⟩ : syracuseStep 1850747 = 2776121) B2776121
theorem B1850799 : Blo 1849626 1850799 := bstep (se 1 (by rfl) ⟨1388099, by rfl⟩ : syracuseStep 1850799 = 2776199) B2776199
theorem B2964919 : Blo 1849626 2964919 := bstep (se 1 (by rfl) ⟨2223689, by rfl⟩ : syracuseStep 2964919 = 4447379) B4447379
theorem B1850823 : Blo 1849626 1850823 := bstep (se 1 (by rfl) ⟨1388117, by rfl⟩ : syracuseStep 1850823 = 2776235) B2776235
theorem B1850843 : Blo 1849626 1850843 := bstep (se 1 (by rfl) ⟨1388132, by rfl⟩ : syracuseStep 1850843 = 2776265) B2776265
theorem B1850919 : Blo 1849626 1850919 := bstep (se 1 (by rfl) ⟨1388189, by rfl⟩ : syracuseStep 1850919 = 2776379) B2776379
theorem B1850959 : Blo 1849626 1850959 := bstep (se 1 (by rfl) ⟨1388219, by rfl⟩ : syracuseStep 1850959 = 2776439) B2776439
theorem B2776655 : Blo 1849626 2776655 := bstep (se 1 (by rfl) ⟨2082491, by rfl⟩ : syracuseStep 2776655 = 4164983) B4164983
theorem B1850975 : Blo 1849626 1850975 := bstep (se 1 (by rfl) ⟨1388231, by rfl⟩ : syracuseStep 1850975 = 2776463) B2776463
theorem B200326769 : Blo 1849626 200326769 := bstep (se 2 (by rfl) ⟨75122538, by rfl⟩ : syracuseStep 200326769 = 150245077) B150245077
theorem B22503035 : Blo 1849626 22503035 := bstep (se 1 (by rfl) ⟨16877276, by rfl⟩ : syracuseStep 22503035 = 33754553) B33754553
theorem B1851003 : Blo 1849626 1851003 := bstep (se 1 (by rfl) ⟨1388252, by rfl⟩ : syracuseStep 1851003 = 2776505) B2776505
theorem B4685435 : Blo 1849626 4685435 := bstep (se 1 (by rfl) ⟨3514076, by rfl⟩ : syracuseStep 4685435 = 7028153) B7028153
theorem B1851055 : Blo 1849626 1851055 := bstep (se 1 (by rfl) ⟨1388291, by rfl⟩ : syracuseStep 1851055 = 2776583) B2776583
theorem B1851079 : Blo 1849626 1851079 := bstep (se 1 (by rfl) ⟨1388309, by rfl⟩ : syracuseStep 1851079 = 2776619) B2776619
theorem B2776775 : Blo 1849626 2776775 := bstep (se 1 (by rfl) ⟨2082581, by rfl⟩ : syracuseStep 2776775 = 4165163) B4165163
theorem B1851099 : Blo 1849626 1851099 := bstep (se 1 (by rfl) ⟨1388324, by rfl⟩ : syracuseStep 1851099 = 2776649) B2776649
theorem B4218617 : Blo 1849626 4218617 := bstep (se 2 (by rfl) ⟨1581981, by rfl⟩ : syracuseStep 4218617 = 3163963) B3163963
theorem B12181241 : Blo 1849626 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B1851175 : Blo 1849626 1851175 := bstep (se 1 (by rfl) ⟨1388381, by rfl⟩ : syracuseStep 1851175 = 2776763) B2776763
theorem B1851215 : Blo 1849626 1851215 := bstep (se 1 (by rfl) ⟨1388411, by rfl⟩ : syracuseStep 1851215 = 2776823) B2776823
theorem B1851231 : Blo 1849626 1851231 := bstep (se 1 (by rfl) ⟨1388423, by rfl⟩ : syracuseStep 1851231 = 2776847) B2776847
theorem B2776937 : Blo 1849626 2776937 := bstep (se 2 (by rfl) ⟨1041351, by rfl⟩ : syracuseStep 2776937 = 2082703) B2082703
theorem B11853677 : Blo 1849626 11853677 := bstep (se 3 (by rfl) ⟨2222564, by rfl⟩ : syracuseStep 11853677 = 4445129) B4445129
theorem B1851259 : Blo 1849626 1851259 := bstep (se 1 (by rfl) ⟨1388444, by rfl⟩ : syracuseStep 1851259 = 2776889) B2776889
theorem B7905185 : Blo 1849626 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B5341103 : Blo 1849626 5341103 := bstep (se 1 (by rfl) ⟨4005827, by rfl⟩ : syracuseStep 5341103 = 8011655) B8011655
theorem B1851311 : Blo 1849626 1851311 := bstep (se 1 (by rfl) ⟨1388483, by rfl⟩ : syracuseStep 1851311 = 2776967) B2776967
theorem B2342839 : Blo 1849626 2342839 := bstep (se 1 (by rfl) ⟨1757129, by rfl⟩ : syracuseStep 2342839 = 3514259) B3514259
theorem B2777015 : Blo 1849626 2777015 := bstep (se 1 (by rfl) ⟨2082761, by rfl⟩ : syracuseStep 2777015 = 4165523) B4165523
theorem B5930939 : Blo 1849626 5930939 := bstep (se 1 (by rfl) ⟨4448204, by rfl⟩ : syracuseStep 5930939 = 8896409) B8896409
theorem B1851335 : Blo 1849626 1851335 := bstep (se 1 (by rfl) ⟨1388501, by rfl⟩ : syracuseStep 1851335 = 2777003) B2777003
theorem B13516753 : Blo 1849626 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B1851355 : Blo 1849626 1851355 := bstep (se 1 (by rfl) ⟨1388516, by rfl⟩ : syracuseStep 1851355 = 2777033) B2777033
theorem B2777051 : Blo 1849626 2777051 := bstep (se 1 (by rfl) ⟨2082788, by rfl⟩ : syracuseStep 2777051 = 4165577) B4165577
theorem B9371699 : Blo 1849626 9371699 := bstep (se 1 (by rfl) ⟨7028774, by rfl⟩ : syracuseStep 9371699 = 14057549) B14057549
theorem B360316997 : Blo 1849626 360316997 := bstep (se 4 (by rfl) ⟨33779718, by rfl⟩ : syracuseStep 360316997 = 67559437) B67559437
theorem B15810713 : Blo 1849626 15810713 := bstep (se 2 (by rfl) ⟨5929017, by rfl⟩ : syracuseStep 15810713 = 11858035) B11858035
theorem B68485337 : Blo 1849626 68485337 := bstep (se 2 (by rfl) ⟨25682001, by rfl⟩ : syracuseStep 68485337 = 51364003) B51364003
theorem B15802715 : Blo 1849626 15802715 := bstep (se 1 (by rfl) ⟨11852036, by rfl⟩ : syracuseStep 15802715 = 23704073) B23704073
theorem B2343259 : Blo 1849626 2343259 := bstep (se 1 (by rfl) ⟨1757444, by rfl⟩ : syracuseStep 2343259 = 3514889) B3514889
theorem B2777435 : Blo 1849626 2777435 := bstep (se 1 (by rfl) ⟨2083076, by rfl⟩ : syracuseStep 2777435 = 4166153) B4166153
theorem B4161959 : Blo 1849626 4161959 := bstep (se 1 (by rfl) ⟨3121469, by rfl⟩ : syracuseStep 4161959 = 6242939) B6242939
theorem B2081191 : Blo 1849626 2081191 := bstep (se 1 (by rfl) ⟨1560893, by rfl⟩ : syracuseStep 2081191 = 3121787) B3121787
theorem B4162067 : Blo 1849626 4162067 := bstep (se 1 (by rfl) ⟨3121550, by rfl⟩ : syracuseStep 4162067 = 6243101) B6243101
theorem B3334727 : Blo 1849626 3334727 := bstep (se 1 (by rfl) ⟨2501045, by rfl⟩ : syracuseStep 3334727 = 5002091) B5002091
theorem B4686407 : Blo 1849626 4686407 := bstep (se 1 (by rfl) ⟨3514805, by rfl⟩ : syracuseStep 4686407 = 7029611) B7029611
theorem B4162121 : Blo 1849626 4162121 := bstep (se 2 (by rfl) ⟨1560795, by rfl⟩ : syracuseStep 4162121 = 3121591) B3121591
theorem B4686457 : Blo 1849626 4686457 := bstep (se 2 (by rfl) ⟨1757421, by rfl⟩ : syracuseStep 4686457 = 3514843) B3514843
theorem B3334879 : Blo 1849626 3334879 := bstep (se 1 (by rfl) ⟨2501159, by rfl⟩ : syracuseStep 3334879 = 5002319) B5002319
theorem B21087053 : Blo 1849626 21087053 := bstep (se 3 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 21087053 = 7907645) B7907645
theorem B1975271 : Blo 1849626 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B4162535 : Blo 1849626 4162535 := bstep (se 1 (by rfl) ⟨3121901, by rfl⟩ : syracuseStep 4162535 = 6243803) B6243803
theorem B2081767 : Blo 1849626 2081767 := bstep (se 1 (by rfl) ⟨1561325, by rfl⟩ : syracuseStep 2081767 = 3122651) B3122651
theorem B10544165 : Blo 1849626 10544165 := bstep (se 4 (by rfl) ⟨988515, by rfl⟩ : syracuseStep 10544165 = 1977031) B1977031
theorem B6243425 : Blo 1849626 6243425 := bstep (se 2 (by rfl) ⟨2341284, by rfl⟩ : syracuseStep 6243425 = 4682569) B4682569
theorem B17786051 : Blo 1849626 17786051 := bstep (se 1 (by rfl) ⟨13339538, by rfl⟩ : syracuseStep 17786051 = 26679077) B26679077
theorem B6333689 : Blo 1849626 6333689 := bstep (se 2 (by rfl) ⟨2375133, by rfl⟩ : syracuseStep 6333689 = 4750267) B4750267
theorem B8439079 : Blo 1849626 8439079 := bstep (se 1 (by rfl) ⟨6329309, by rfl⟩ : syracuseStep 8439079 = 12658619) B12658619
theorem B7030111 : Blo 1849626 7030111 := bstep (se 1 (by rfl) ⟨5272583, by rfl⟩ : syracuseStep 7030111 = 10545167) B10545167
theorem B4162913 : Blo 1849626 4162913 := bstep (se 2 (by rfl) ⟨1561092, by rfl⟩ : syracuseStep 4162913 = 3122185) B3122185
theorem B26682767 : Blo 1849626 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B4163003 : Blo 1849626 4163003 := bstep (se 1 (by rfl) ⟨3122252, by rfl⟩ : syracuseStep 4163003 = 6244505) B6244505
theorem B4163129 : Blo 1849626 4163129 := bstep (se 2 (by rfl) ⟨1561173, by rfl⟩ : syracuseStep 4163129 = 3122347) B3122347
theorem B9373319 : Blo 1849626 9373319 := bstep (se 1 (by rfl) ⟨7029989, by rfl⟩ : syracuseStep 9373319 = 14059979) B14059979
theorem B17778365 : Blo 1849626 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B5269303 : Blo 1849626 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B13338445 : Blo 1849626 13338445 := bstep (se 3 (by rfl) ⟨2500958, by rfl⟩ : syracuseStep 13338445 = 5001917) B5001917
theorem B13346693 : Blo 1849626 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B13518737 : Blo 1849626 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B16877753 : Blo 1849626 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B15001793 : Blo 1849626 15001793 := bstep (se 2 (by rfl) ⟨5625672, by rfl⟩ : syracuseStep 15001793 = 11251345) B11251345
theorem B4163795 : Blo 1849626 4163795 := bstep (se 1 (by rfl) ⟨3122846, by rfl⟩ : syracuseStep 4163795 = 6245693) B6245693
theorem B4163849 : Blo 1849626 4163849 := bstep (se 2 (by rfl) ⟨1561443, by rfl⟩ : syracuseStep 4163849 = 3122887) B3122887
theorem B3336457 : Blo 1849626 3336457 := bstep (se 2 (by rfl) ⟨1251171, by rfl⟩ : syracuseStep 3336457 = 2502343) B2502343
theorem B37996931 : Blo 1849626 37996931 := bstep (se 1 (by rfl) ⟨28497698, by rfl⟩ : syracuseStep 37996931 = 56995397) B56995397
theorem B15002023 : Blo 1849626 15002023 := bstep (se 1 (by rfl) ⟨11251517, by rfl⟩ : syracuseStep 15002023 = 22503035) B22503035
theorem B6244775 : Blo 1849626 6244775 := bstep (se 1 (by rfl) ⟨4683581, by rfl⟩ : syracuseStep 6244775 = 9367163) B9367163
theorem B3123623 : Blo 1849626 3123623 := bstep (se 1 (by rfl) ⟨2342717, by rfl⟩ : syracuseStep 3123623 = 4685435) B4685435
theorem B4164065 : Blo 1849626 4164065 := bstep (se 2 (by rfl) ⟨1561524, by rfl⟩ : syracuseStep 4164065 = 3123049) B3123049
theorem B2812411 : Blo 1849626 2812411 := bstep (se 1 (by rfl) ⟨2109308, by rfl⟩ : syracuseStep 2812411 = 4218617) B4218617
theorem B8120827 : Blo 1849626 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B3951175 : Blo 1849626 3951175 := bstep (se 1 (by rfl) ⟨2963381, by rfl⟩ : syracuseStep 3951175 = 5926763) B5926763
theorem B6244937 : Blo 1849626 6244937 := bstep (se 2 (by rfl) ⟨2341851, by rfl⟩ : syracuseStep 6244937 = 4683703) B4683703
theorem B3123785 : Blo 1849626 3123785 := bstep (se 2 (by rfl) ⟨1171419, by rfl⟩ : syracuseStep 3123785 = 2342839) B2342839
theorem B5270123 : Blo 1849626 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B9366191 : Blo 1849626 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B4164371 : Blo 1849626 4164371 := bstep (se 1 (by rfl) ⟨3123278, by rfl⟩ : syracuseStep 4164371 = 6246557) B6246557
theorem B2501423 : Blo 1849626 2501423 := bstep (se 1 (by rfl) ⟨1876067, by rfl⟩ : syracuseStep 2501423 = 3752135) B3752135
theorem B50670467 : Blo 1849626 50670467 := bstep (se 1 (by rfl) ⟨38002850, by rfl⟩ : syracuseStep 50670467 = 76005701) B76005701
theorem B9366515 : Blo 1849626 9366515 := bstep (se 1 (by rfl) ⟨7024886, by rfl⟩ : syracuseStep 9366515 = 14049773) B14049773
theorem B4164731 : Blo 1849626 4164731 := bstep (se 1 (by rfl) ⟨3123548, by rfl⟩ : syracuseStep 4164731 = 6247097) B6247097
theorem B4164857 : Blo 1849626 4164857 := bstep (se 2 (by rfl) ⟨1561821, by rfl⟩ : syracuseStep 4164857 = 3123643) B3123643
theorem B4165001 : Blo 1849626 4165001 := bstep (se 2 (by rfl) ⟨1561875, by rfl⟩ : syracuseStep 4165001 = 3123751) B3123751
theorem B72084923 : Blo 1849626 72084923 := bstep (se 1 (by rfl) ⟨54063692, by rfl⟩ : syracuseStep 72084923 = 108127385) B108127385
theorem B4165127 : Blo 1849626 4165127 := bstep (se 1 (by rfl) ⟨3123845, by rfl⟩ : syracuseStep 4165127 = 6247691) B6247691
theorem B4165307 : Blo 1849626 4165307 := bstep (se 1 (by rfl) ⟨3123980, by rfl⟩ : syracuseStep 4165307 = 6247961) B6247961
theorem B4165433 : Blo 1849626 4165433 := bstep (se 2 (by rfl) ⟨1562037, by rfl⟩ : syracuseStep 4165433 = 3124075) B3124075
theorem B8892335 : Blo 1849626 8892335 := bstep (se 1 (by rfl) ⟨6669251, by rfl⟩ : syracuseStep 8892335 = 13338503) B13338503
theorem B6246611 : Blo 1849626 6246611 := bstep (se 1 (by rfl) ⟨4684958, by rfl⟩ : syracuseStep 6246611 = 9369917) B9369917
theorem B9367811 : Blo 1849626 9367811 := bstep (se 1 (by rfl) ⟨7025858, by rfl⟩ : syracuseStep 9367811 = 14051717) B14051717
theorem B3953063 : Blo 1849626 3953063 := bstep (se 1 (by rfl) ⟨2964797, by rfl⟩ : syracuseStep 3953063 = 5929595) B5929595
theorem B3953071 : Blo 1849626 3953071 := bstep (se 1 (by rfl) ⟨2964803, by rfl⟩ : syracuseStep 3953071 = 5929607) B5929607
theorem B15815087 : Blo 1849626 15815087 := bstep (se 1 (by rfl) ⟨11861315, by rfl⟩ : syracuseStep 15815087 = 23722631) B23722631
theorem B4166063 : Blo 1849626 4166063 := bstep (se 1 (by rfl) ⟨3124547, by rfl⟩ : syracuseStep 4166063 = 6249095) B6249095
theorem B4682195 : Blo 1849626 4682195 := bstep (se 1 (by rfl) ⟨3511646, by rfl⟩ : syracuseStep 4682195 = 7023293) B7023293
theorem B4166099 : Blo 1849626 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B6246881 : Blo 1849626 6246881 := bstep (se 2 (by rfl) ⟨2342580, by rfl⟩ : syracuseStep 6246881 = 4685161) B4685161
theorem B35582489 : Blo 1849626 35582489 := bstep (se 2 (by rfl) ⟨13343433, by rfl⟩ : syracuseStep 35582489 = 26686867) B26686867
theorem B9368135 : Blo 1849626 9368135 := bstep (se 1 (by rfl) ⟨7026101, by rfl⟩ : syracuseStep 9368135 = 14052203) B14052203
theorem B3953225 : Blo 1849626 3953225 := bstep (se 2 (by rfl) ⟨1482459, by rfl⟩ : syracuseStep 3953225 = 2964919) B2964919
theorem B11252321 : Blo 1849626 11252321 := bstep (se 2 (by rfl) ⟨4219620, by rfl⟩ : syracuseStep 11252321 = 8439241) B8439241
theorem B4444919 : Blo 1849626 4444919 := bstep (se 1 (by rfl) ⟨3333689, by rfl⟩ : syracuseStep 4444919 = 6667379) B6667379
theorem B12661705 : Blo 1849626 12661705 := bstep (se 2 (by rfl) ⟨4748139, by rfl⟩ : syracuseStep 12661705 = 9496279) B9496279
theorem B30012407 : Blo 1849626 30012407 := bstep (se 1 (by rfl) ⟨22509305, by rfl⟩ : syracuseStep 30012407 = 45018611) B45018611
theorem B68432957 : Blo 1849626 68432957 := bstep (se 3 (by rfl) ⟨12831179, by rfl⟩ : syracuseStep 68432957 = 25662359) B25662359
theorem B133551179 : Blo 1849626 133551179 := bstep (se 1 (by rfl) ⟨100163384, by rfl⟩ : syracuseStep 133551179 = 200326769) B200326769
theorem B15815837 : Blo 1849626 15815837 := bstep (se 3 (by rfl) ⟨2965469, by rfl⟩ : syracuseStep 15815837 = 5930939) B5930939
theorem B7124183 : Blo 1849626 7124183 := bstep (se 1 (by rfl) ⟨5343137, by rfl⟩ : syracuseStep 7124183 = 10686275) B10686275
theorem B7902451 : Blo 1849626 7902451 := bstep (se 1 (by rfl) ⟨5926838, by rfl⟩ : syracuseStep 7902451 = 11853677) B11853677
theorem B3560735 : Blo 1849626 3560735 := bstep (se 1 (by rfl) ⟨2670551, by rfl⟩ : syracuseStep 3560735 = 5341103) B5341103
theorem B2635039 : Blo 1849626 2635039 := bstep (se 1 (by rfl) ⟨1976279, by rfl⟩ : syracuseStep 2635039 = 3952559) B3952559
theorem B256341347 : Blo 1849626 256341347 := bstep (se 1 (by rfl) ⟨192256010, by rfl⟩ : syracuseStep 256341347 = 384512021) B384512021
theorem B2774471 : Blo 1849626 2774471 := bstep (se 1 (by rfl) ⟨2080853, by rfl⟩ : syracuseStep 2774471 = 4161707) B4161707
theorem B11851271 : Blo 1849626 11851271 := bstep (se 1 (by rfl) ⟨8888453, by rfl⟩ : syracuseStep 11851271 = 17776907) B17776907
theorem B3954233 : Blo 1849626 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B4683359 : Blo 1849626 4683359 := bstep (se 1 (by rfl) ⟨3512519, by rfl⟩ : syracuseStep 4683359 = 7025039) B7025039
theorem B6248123 : Blo 1849626 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B2774825 : Blo 1849626 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B2774831 : Blo 1849626 2774831 := bstep (se 1 (by rfl) ⟨2081123, by rfl⟩ : syracuseStep 2774831 = 4162247) B4162247
theorem B9369431 : Blo 1849626 9369431 := bstep (se 1 (by rfl) ⟨7027073, by rfl⟩ : syracuseStep 9369431 = 14054147) B14054147
theorem B10000417 : Blo 1849626 10000417 := bstep (se 2 (by rfl) ⟨3750156, by rfl⟩ : syracuseStep 10000417 = 7500313) B7500313
theorem B2775305 : Blo 1849626 2775305 := bstep (se 2 (by rfl) ⟨1040739, by rfl⟩ : syracuseStep 2775305 = 2081479) B2081479
theorem B1849631 : Blo 1849626 1849631 := bstep (se 1 (by rfl) ⟨1387223, by rfl⟩ : syracuseStep 1849631 = 2774447) B2774447
theorem B8444189 : Blo 1849626 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1849691 : Blo 1849626 1849691 := bstep (se 1 (by rfl) ⟨1387268, by rfl⟩ : syracuseStep 1849691 = 2774537) B2774537
theorem B4684139 : Blo 1849626 4684139 := bstep (se 1 (by rfl) ⟨3513104, by rfl⟩ : syracuseStep 4684139 = 7026209) B7026209
theorem B1849711 : Blo 1849626 1849711 := bstep (se 1 (by rfl) ⟨1387283, by rfl⟩ : syracuseStep 1849711 = 2774567) B2774567
theorem B2775407 : Blo 1849626 2775407 := bstep (se 1 (by rfl) ⟨2081555, by rfl⟩ : syracuseStep 2775407 = 4163111) B4163111
theorem B1849767 : Blo 1849626 1849767 := bstep (se 1 (by rfl) ⟨1387325, by rfl⟩ : syracuseStep 1849767 = 2774651) B2774651
theorem B3512801 : Blo 1849626 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B1849851 : Blo 1849626 1849851 := bstep (se 1 (by rfl) ⟨1387388, by rfl⟩ : syracuseStep 1849851 = 2774777) B2774777
theorem B7027195 : Blo 1849626 7027195 := bstep (se 1 (by rfl) ⟨5270396, by rfl⟩ : syracuseStep 7027195 = 10540793) B10540793
theorem B20568599 : Blo 1849626 20568599 := bstep (se 1 (by rfl) ⟨15426449, by rfl⟩ : syracuseStep 20568599 = 30852899) B30852899
theorem B1849919 : Blo 1849626 1849919 := bstep (se 1 (by rfl) ⟨1387439, by rfl⟩ : syracuseStep 1849919 = 2774879) B2774879
theorem B4684351 : Blo 1849626 4684351 := bstep (se 1 (by rfl) ⟨3513263, by rfl⟩ : syracuseStep 4684351 = 7026527) B7026527
theorem B1849927 : Blo 1849626 1849927 := bstep (se 1 (by rfl) ⟨1387445, by rfl⟩ : syracuseStep 1849927 = 2774891) B2774891
theorem B2775623 : Blo 1849626 2775623 := bstep (se 1 (by rfl) ⟨2081717, by rfl⟩ : syracuseStep 2775623 = 4163435) B4163435
theorem B2775659 : Blo 1849626 2775659 := bstep (se 1 (by rfl) ⟨2081744, by rfl⟩ : syracuseStep 2775659 = 4163489) B4163489
theorem B4684463 : Blo 1849626 4684463 := bstep (se 1 (by rfl) ⟨3513347, by rfl⟩ : syracuseStep 4684463 = 7026695) B7026695
theorem B15014575 : Blo 1849626 15014575 := bstep (se 1 (by rfl) ⟨11260931, by rfl⟩ : syracuseStep 15014575 = 22521863) B22521863
theorem B7903939 : Blo 1849626 7903939 := bstep (se 1 (by rfl) ⟨5927954, by rfl⟩ : syracuseStep 7903939 = 11855909) B11855909
theorem B1850079 : Blo 1849626 1850079 := bstep (se 1 (by rfl) ⟨1387559, by rfl⟩ : syracuseStep 1850079 = 2775119) B2775119
theorem B1850159 : Blo 1849626 1850159 := bstep (se 1 (by rfl) ⟨1387619, by rfl⟩ : syracuseStep 1850159 = 2775239) B2775239
theorem B2775887 : Blo 1849626 2775887 := bstep (se 1 (by rfl) ⟨2081915, by rfl⟩ : syracuseStep 2775887 = 4163831) B4163831
theorem B1850267 : Blo 1849626 1850267 := bstep (se 1 (by rfl) ⟨1387700, by rfl⟩ : syracuseStep 1850267 = 2775401) B2775401
theorem B1850319 : Blo 1849626 1850319 := bstep (se 1 (by rfl) ⟨1387739, by rfl⟩ : syracuseStep 1850319 = 2775479) B2775479
theorem B1850343 : Blo 1849626 1850343 := bstep (se 1 (by rfl) ⟨1387757, by rfl⟩ : syracuseStep 1850343 = 2775515) B2775515
theorem B4684787 : Blo 1849626 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B4684999 : Blo 1849626 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B2776283 : Blo 1849626 2776283 := bstep (se 1 (by rfl) ⟨2082212, by rfl⟩ : syracuseStep 2776283 = 4164425) B4164425
theorem B1850655 : Blo 1849626 1850655 := bstep (se 1 (by rfl) ⟨1387991, by rfl⟩ : syracuseStep 1850655 = 2775983) B2775983
theorem B10534211 : Blo 1849626 10534211 := bstep (se 1 (by rfl) ⟨7900658, by rfl⟩ : syracuseStep 10534211 = 15801317) B15801317
theorem B75144523 : Blo 1849626 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B1850715 : Blo 1849626 1850715 := bstep (se 1 (by rfl) ⟨1388036, by rfl⟩ : syracuseStep 1850715 = 2776073) B2776073
theorem B1850735 : Blo 1849626 1850735 := bstep (se 1 (by rfl) ⟨1388051, by rfl⟩ : syracuseStep 1850735 = 2776103) B2776103
theorem B10001801 : Blo 1849626 10001801 := bstep (se 2 (by rfl) ⟨3750675, by rfl⟩ : syracuseStep 10001801 = 7501351) B7501351
theorem B2776457 : Blo 1849626 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B1850791 : Blo 1849626 1850791 := bstep (se 1 (by rfl) ⟨1388093, by rfl⟩ : syracuseStep 1850791 = 2776187) B2776187
theorem B7028167 : Blo 1849626 7028167 := bstep (se 1 (by rfl) ⟨5271125, by rfl⟩ : syracuseStep 7028167 = 10542251) B10542251
theorem B1850875 : Blo 1849626 1850875 := bstep (se 1 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 1850875 = 2776313) B2776313
theorem B1850943 : Blo 1849626 1850943 := bstep (se 1 (by rfl) ⟨1388207, by rfl⟩ : syracuseStep 1850943 = 2776415) B2776415
theorem B1850951 : Blo 1849626 1850951 := bstep (se 1 (by rfl) ⟨1388213, by rfl⟩ : syracuseStep 1850951 = 2776427) B2776427
theorem B10542707 : Blo 1849626 10542707 := bstep (se 1 (by rfl) ⟨7907030, by rfl⟩ : syracuseStep 10542707 = 15814061) B15814061
theorem B1851103 : Blo 1849626 1851103 := bstep (se 1 (by rfl) ⟨1388327, by rfl⟩ : syracuseStep 1851103 = 2776655) B2776655
theorem B2776811 : Blo 1849626 2776811 := bstep (se 1 (by rfl) ⟨2082608, by rfl⟩ : syracuseStep 2776811 = 4165217) B4165217
theorem B5267207 : Blo 1849626 5267207 := bstep (se 1 (by rfl) ⟨3950405, by rfl⟩ : syracuseStep 5267207 = 7900811) B7900811
theorem B1851183 : Blo 1849626 1851183 := bstep (se 1 (by rfl) ⟨1388387, by rfl⟩ : syracuseStep 1851183 = 2776775) B2776775
theorem B21372731 : Blo 1849626 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B1851291 : Blo 1849626 1851291 := bstep (se 1 (by rfl) ⟨1388468, by rfl⟩ : syracuseStep 1851291 = 2776937) B2776937
theorem B18022337 : Blo 1849626 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B1851343 : Blo 1849626 1851343 := bstep (se 1 (by rfl) ⟨1388507, by rfl⟩ : syracuseStep 1851343 = 2777015) B2777015
theorem B2777039 : Blo 1849626 2777039 := bstep (se 1 (by rfl) ⟨2082779, by rfl⟩ : syracuseStep 2777039 = 4165559) B4165559
theorem B1851367 : Blo 1849626 1851367 := bstep (se 1 (by rfl) ⟨1388525, by rfl⟩ : syracuseStep 1851367 = 2777051) B2777051
theorem B10535143 : Blo 1849626 10535143 := bstep (se 1 (by rfl) ⟨7901357, by rfl⟩ : syracuseStep 10535143 = 15802715) B15802715
theorem B1851623 : Blo 1849626 1851623 := bstep (se 1 (by rfl) ⟨1388717, by rfl⟩ : syracuseStep 1851623 = 2777435) B2777435
theorem B10543391 : Blo 1849626 10543391 := bstep (se 1 (by rfl) ⟨7907543, by rfl⟩ : syracuseStep 10543391 = 15815087) B15815087
theorem B2777375 : Blo 1849626 2777375 := bstep (se 1 (by rfl) ⟨2083031, by rfl⟩ : syracuseStep 2777375 = 4166063) B4166063
theorem B3121463 : Blo 1849626 3121463 := bstep (se 1 (by rfl) ⟨2341097, by rfl⟩ : syracuseStep 3121463 = 4682195) B4682195
theorem B2777399 : Blo 1849626 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B4448609 : Blo 1849626 4448609 := bstep (se 2 (by rfl) ⟨1668228, by rfl⟩ : syracuseStep 4448609 = 3336457) B3336457
theorem B26681845 : Blo 1849626 26681845 := bstep (se 5 (by rfl) ⟨1250711, by rfl⟩ : syracuseStep 26681845 = 2501423) B2501423
theorem B14058035 : Blo 1849626 14058035 := bstep (se 1 (by rfl) ⟨10543526, by rfl⟩ : syracuseStep 14058035 = 21087053) B21087053
theorem B7029443 : Blo 1849626 7029443 := bstep (se 1 (by rfl) ⟨5272082, by rfl⟩ : syracuseStep 7029443 = 10544165) B10544165
theorem B45621971 : Blo 1849626 45621971 := bstep (se 1 (by rfl) ⟨34216478, by rfl⟩ : syracuseStep 45621971 = 68432957) B68432957
theorem B4162283 : Blo 1849626 4162283 := bstep (se 1 (by rfl) ⟨3121712, by rfl⟩ : syracuseStep 4162283 = 6243425) B6243425
theorem B5268233 : Blo 1849626 5268233 := bstep (se 2 (by rfl) ⟨1975587, by rfl⟩ : syracuseStep 5268233 = 3951175) B3951175
theorem B10543891 : Blo 1849626 10543891 := bstep (se 1 (by rfl) ⟨7907918, by rfl⟩ : syracuseStep 10543891 = 15815837) B15815837
theorem B170894231 : Blo 1849626 170894231 := bstep (se 1 (by rfl) ⟨128170673, by rfl⟩ : syracuseStep 170894231 = 256341347) B256341347
theorem B3122239 : Blo 1849626 3122239 := bstep (se 1 (by rfl) ⟨2341679, by rfl⟩ : syracuseStep 3122239 = 4683359) B4683359
theorem B8897795 : Blo 1849626 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B9012491 : Blo 1849626 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B5629459 : Blo 1849626 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B3122759 : Blo 1849626 3122759 := bstep (se 1 (by rfl) ⟨2342069, by rfl⟩ : syracuseStep 3122759 = 4684139) B4684139
theorem B25331287 : Blo 1849626 25331287 := bstep (se 1 (by rfl) ⟨18998465, by rfl⟩ : syracuseStep 25331287 = 37996931) B37996931
theorem B4163183 : Blo 1849626 4163183 := bstep (se 1 (by rfl) ⟨3122387, by rfl⟩ : syracuseStep 4163183 = 6244775) B6244775
theorem B2082415 : Blo 1849626 2082415 := bstep (se 1 (by rfl) ⟨1561811, by rfl⟩ : syracuseStep 2082415 = 3123623) B3123623
theorem B10536601 : Blo 1849626 10536601 := bstep (se 2 (by rfl) ⟨3951225, by rfl⟩ : syracuseStep 10536601 = 7902451) B7902451
theorem B4163291 : Blo 1849626 4163291 := bstep (se 1 (by rfl) ⟨3122468, by rfl⟩ : syracuseStep 4163291 = 6244937) B6244937
theorem B2082523 : Blo 1849626 2082523 := bstep (se 1 (by rfl) ⟨1561892, by rfl⟩ : syracuseStep 2082523 = 3123785) B3123785
theorem B6244127 : Blo 1849626 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B3122975 : Blo 1849626 3122975 := bstep (se 1 (by rfl) ⟨2342231, by rfl⟩ : syracuseStep 3122975 = 4684463) B4684463
theorem B9373481 : Blo 1849626 9373481 := bstep (se 2 (by rfl) ⟨3515055, by rfl⟩ : syracuseStep 9373481 = 7030111) B7030111
theorem B6244343 : Blo 1849626 6244343 := bstep (se 1 (by rfl) ⟨4683257, by rfl⟩ : syracuseStep 6244343 = 9366515) B9366515
theorem B3123191 : Blo 1849626 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B7022807 : Blo 1849626 7022807 := bstep (se 1 (by rfl) ⟨5267105, by rfl⟩ : syracuseStep 7022807 = 10534211) B10534211
theorem B48056615 : Blo 1849626 48056615 := bstep (se 1 (by rfl) ⟨36042461, by rfl⟩ : syracuseStep 48056615 = 72084923) B72084923
theorem B14248487 : Blo 1849626 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B4164407 : Blo 1849626 4164407 := bstep (se 1 (by rfl) ⟨3123305, by rfl⟩ : syracuseStep 4164407 = 6246611) B6246611
theorem B45656891 : Blo 1849626 45656891 := bstep (se 1 (by rfl) ⟨34242668, by rfl⟩ : syracuseStep 45656891 = 68485337) B68485337
theorem B6245207 : Blo 1849626 6245207 := bstep (se 1 (by rfl) ⟨4683905, by rfl⟩ : syracuseStep 6245207 = 9367811) B9367811
theorem B4164587 : Blo 1849626 4164587 := bstep (se 1 (by rfl) ⟨3123440, by rfl⟩ : syracuseStep 4164587 = 6246881) B6246881
theorem B6245423 : Blo 1849626 6245423 := bstep (se 1 (by rfl) ⟨4684067, by rfl⟩ : syracuseStep 6245423 = 9368135) B9368135
theorem B3124271 : Blo 1849626 3124271 := bstep (se 1 (by rfl) ⟨2343203, by rfl⟩ : syracuseStep 3124271 = 4686407) B4686407
theorem B3124345 : Blo 1849626 3124345 := bstep (se 2 (by rfl) ⟨1171629, by rfl⟩ : syracuseStep 3124345 = 2343259) B2343259
theorem B5270761 : Blo 1849626 5270761 := bstep (se 2 (by rfl) ⟨1976535, by rfl⟩ : syracuseStep 5270761 = 3953071) B3953071
theorem B20008271 : Blo 1849626 20008271 := bstep (se 1 (by rfl) ⟨15006203, by rfl⟩ : syracuseStep 20008271 = 30012407) B30012407
theorem B89034119 : Blo 1849626 89034119 := bstep (se 1 (by rfl) ⟨66775589, by rfl⟩ : syracuseStep 89034119 = 133551179) B133551179
theorem B6245801 : Blo 1849626 6245801 := bstep (se 2 (by rfl) ⟨2342175, by rfl⟩ : syracuseStep 6245801 = 4684351) B4684351
theorem B11857367 : Blo 1849626 11857367 := bstep (se 1 (by rfl) ⟨8893025, by rfl⟩ : syracuseStep 11857367 = 17786051) B17786051
theorem B4222459 : Blo 1849626 4222459 := bstep (se 1 (by rfl) ⟨3166844, by rfl⟩ : syracuseStep 4222459 = 6333689) B6333689
theorem B10538585 : Blo 1849626 10538585 := bstep (se 2 (by rfl) ⟨3951969, by rfl⟩ : syracuseStep 10538585 = 7903939) B7903939
theorem B17788511 : Blo 1849626 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B7900847 : Blo 1849626 7900847 := bstep (se 1 (by rfl) ⟨5925635, by rfl⟩ : syracuseStep 7900847 = 11851271) B11851271
theorem B4165415 : Blo 1849626 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B6246287 : Blo 1849626 6246287 := bstep (se 1 (by rfl) ⟨4684715, by rfl⟩ : syracuseStep 6246287 = 9369431) B9369431
theorem B11251835 : Blo 1849626 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B8892605 : Blo 1849626 8892605 := bstep (se 3 (by rfl) ⟨1667363, by rfl⟩ : syracuseStep 8892605 = 3334727) B3334727
theorem B6246665 : Blo 1849626 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B14053661 : Blo 1849626 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B11252105 : Blo 1849626 11252105 := bstep (se 2 (by rfl) ⟨4219539, by rfl⟩ : syracuseStep 11252105 = 8439079) B8439079
theorem B100192697 : Blo 1849626 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B33780311 : Blo 1849626 33780311 := bstep (se 1 (by rfl) ⟨25335233, by rfl⟩ : syracuseStep 33780311 = 50670467) B50670467
theorem B14045885 : Blo 1849626 14045885 := bstep (se 3 (by rfl) ⟨2633603, by rfl⟩ : syracuseStep 14045885 = 5267207) B5267207
theorem B7025737 : Blo 1849626 7025737 := bstep (se 2 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 7025737 = 5269303) B5269303
theorem B5928223 : Blo 1849626 5928223 := bstep (se 1 (by rfl) ⟨4446167, by rfl⟩ : syracuseStep 5928223 = 8892335) B8892335
theorem B12014891 : Blo 1849626 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B6247799 : Blo 1849626 6247799 := bstep (se 1 (by rfl) ⟨4685849, by rfl⟩ : syracuseStep 6247799 = 9371699) B9371699
theorem B13333889 : Blo 1849626 13333889 := bstep (se 2 (by rfl) ⟨5000208, by rfl⟩ : syracuseStep 13333889 = 10000417) B10000417
theorem B240211331 : Blo 1849626 240211331 := bstep (se 1 (by rfl) ⟨180158498, by rfl⟩ : syracuseStep 240211331 = 360316997) B360316997
theorem B10540475 : Blo 1849626 10540475 := bstep (se 1 (by rfl) ⟨7905356, by rfl⟩ : syracuseStep 10540475 = 15810713) B15810713
theorem B2774639 : Blo 1849626 2774639 := bstep (se 1 (by rfl) ⟨2080979, by rfl⟩ : syracuseStep 2774639 = 4161959) B4161959
theorem B2774711 : Blo 1849626 2774711 := bstep (se 1 (by rfl) ⟨2081033, by rfl⟩ : syracuseStep 2774711 = 4162067) B4162067
theorem B23721659 : Blo 1849626 23721659 := bstep (se 1 (by rfl) ⟨17791244, by rfl⟩ : syracuseStep 23721659 = 35582489) B35582489
theorem B2774747 : Blo 1849626 2774747 := bstep (se 1 (by rfl) ⟨2081060, by rfl⟩ : syracuseStep 2774747 = 4162121) B4162121
theorem B7501547 : Blo 1849626 7501547 := bstep (se 1 (by rfl) ⟨5626160, by rfl⟩ : syracuseStep 7501547 = 11252321) B11252321
theorem B2963279 : Blo 1849626 2963279 := bstep (se 1 (by rfl) ⟨2222459, by rfl⟩ : syracuseStep 2963279 = 4444919) B4444919
theorem B2774921 : Blo 1849626 2774921 := bstep (se 2 (by rfl) ⟨1040595, by rfl⟩ : syracuseStep 2774921 = 2081191) B2081191
theorem B20002697 : Blo 1849626 20002697 := bstep (se 2 (by rfl) ⟨7501011, by rfl⟩ : syracuseStep 20002697 = 15002023) B15002023
theorem B2775023 : Blo 1849626 2775023 := bstep (se 1 (by rfl) ⟨2081267, by rfl⟩ : syracuseStep 2775023 = 4162535) B4162535
theorem B10827769 : Blo 1849626 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B9369593 : Blo 1849626 9369593 := bstep (se 2 (by rfl) ⟨3513597, by rfl⟩ : syracuseStep 9369593 = 7027195) B7027195
theorem B4749455 : Blo 1849626 4749455 := bstep (se 1 (by rfl) ⟨3562091, by rfl⟩ : syracuseStep 4749455 = 7124183) B7124183
theorem B6248609 : Blo 1849626 6248609 := bstep (se 2 (by rfl) ⟨2343228, by rfl⟩ : syracuseStep 6248609 = 4686457) B4686457
theorem B2373823 : Blo 1849626 2373823 := bstep (se 1 (by rfl) ⟨1780367, by rfl⟩ : syracuseStep 2373823 = 3560735) B3560735
theorem B20019433 : Blo 1849626 20019433 := bstep (se 2 (by rfl) ⟨7507287, by rfl⟩ : syracuseStep 20019433 = 15014575) B15014575
theorem B2775275 : Blo 1849626 2775275 := bstep (se 1 (by rfl) ⟨2081456, by rfl⟩ : syracuseStep 2775275 = 4162913) B4162913
theorem B2775335 : Blo 1849626 2775335 := bstep (se 1 (by rfl) ⟨2081501, by rfl⟩ : syracuseStep 2775335 = 4163003) B4163003
theorem B4446505 : Blo 1849626 4446505 := bstep (se 2 (by rfl) ⟨1667439, by rfl⟩ : syracuseStep 4446505 = 3334879) B3334879
theorem B1849647 : Blo 1849626 1849647 := bstep (se 1 (by rfl) ⟨1387235, by rfl⟩ : syracuseStep 1849647 = 2774471) B2774471
theorem B2775419 : Blo 1849626 2775419 := bstep (se 1 (by rfl) ⟨2081564, by rfl⟩ : syracuseStep 2775419 = 4163129) B4163129
theorem B2636155 : Blo 1849626 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B6248879 : Blo 1849626 6248879 := bstep (se 1 (by rfl) ⟨4686659, by rfl⟩ : syracuseStep 6248879 = 9373319) B9373319
theorem B10541501 : Blo 1849626 10541501 := bstep (se 3 (by rfl) ⟨1976531, by rfl⟩ : syracuseStep 10541501 = 3953063) B3953063
theorem B11852243 : Blo 1849626 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B1849883 : Blo 1849626 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B1849887 : Blo 1849626 1849887 := bstep (se 1 (by rfl) ⟨1387415, by rfl⟩ : syracuseStep 1849887 = 2774831) B2774831
theorem B16882273 : Blo 1849626 16882273 := bstep (se 2 (by rfl) ⟨6330852, by rfl⟩ : syracuseStep 16882273 = 12661705) B12661705
theorem B2775689 : Blo 1849626 2775689 := bstep (se 2 (by rfl) ⟨1040883, by rfl⟩ : syracuseStep 2775689 = 2081767) B2081767
theorem B10001195 : Blo 1849626 10001195 := bstep (se 1 (by rfl) ⟨7500896, by rfl⟩ : syracuseStep 10001195 = 15001793) B15001793
theorem B2775863 : Blo 1849626 2775863 := bstep (se 1 (by rfl) ⟨2081897, by rfl⟩ : syracuseStep 2775863 = 4163795) B4163795
theorem B1850203 : Blo 1849626 1850203 := bstep (se 1 (by rfl) ⟨1387652, by rfl⟩ : syracuseStep 1850203 = 2775305) B2775305
theorem B2775899 : Blo 1849626 2775899 := bstep (se 1 (by rfl) ⟨2081924, by rfl⟩ : syracuseStep 2775899 = 4163849) B4163849
theorem B10541933 : Blo 1849626 10541933 := bstep (se 3 (by rfl) ⟨1976612, by rfl⟩ : syracuseStep 10541933 = 3953225) B3953225
theorem B1850271 : Blo 1849626 1850271 := bstep (se 1 (by rfl) ⟨1387703, by rfl⟩ : syracuseStep 1850271 = 2775407) B2775407
theorem B2341867 : Blo 1849626 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B2776043 : Blo 1849626 2776043 := bstep (se 1 (by rfl) ⟨2082032, by rfl⟩ : syracuseStep 2776043 = 4164065) B4164065
theorem B13712399 : Blo 1849626 13712399 := bstep (se 1 (by rfl) ⟨10284299, by rfl⟩ : syracuseStep 13712399 = 20568599) B20568599
theorem B3513385 : Blo 1849626 3513385 := bstep (se 2 (by rfl) ⟨1317519, by rfl⟩ : syracuseStep 3513385 = 2635039) B2635039
theorem B1850415 : Blo 1849626 1850415 := bstep (se 1 (by rfl) ⟨1387811, by rfl⟩ : syracuseStep 1850415 = 2775623) B2775623
theorem B1850439 : Blo 1849626 1850439 := bstep (se 1 (by rfl) ⟨1387829, by rfl⟩ : syracuseStep 1850439 = 2775659) B2775659
theorem B2776247 : Blo 1849626 2776247 := bstep (se 1 (by rfl) ⟨2082185, by rfl⟩ : syracuseStep 2776247 = 4164371) B4164371
theorem B1850591 : Blo 1849626 1850591 := bstep (se 1 (by rfl) ⟨1387943, by rfl⟩ : syracuseStep 1850591 = 2775887) B2775887
theorem B9370889 : Blo 1849626 9370889 := bstep (se 2 (by rfl) ⟨3514083, by rfl⟩ : syracuseStep 9370889 = 7028167) B7028167
theorem B2776487 : Blo 1849626 2776487 := bstep (se 1 (by rfl) ⟨2082365, by rfl⟩ : syracuseStep 2776487 = 4164731) B4164731
theorem B1850855 : Blo 1849626 1850855 := bstep (se 1 (by rfl) ⟨1388141, by rfl⟩ : syracuseStep 1850855 = 2776283) B2776283
theorem B2776571 : Blo 1849626 2776571 := bstep (se 1 (by rfl) ⟨2082428, by rfl⟩ : syracuseStep 2776571 = 4164857) B4164857
theorem B6667867 : Blo 1849626 6667867 := bstep (se 1 (by rfl) ⟨5000900, by rfl⟩ : syracuseStep 6667867 = 10001801) B10001801
theorem B1850971 : Blo 1849626 1850971 := bstep (se 1 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 1850971 = 2776457) B2776457
theorem B2776667 : Blo 1849626 2776667 := bstep (se 1 (by rfl) ⟨2082500, by rfl⟩ : syracuseStep 2776667 = 4165001) B4165001
theorem B2776751 : Blo 1849626 2776751 := bstep (se 1 (by rfl) ⟨2082563, by rfl⟩ : syracuseStep 2776751 = 4165127) B4165127
theorem B21069557 : Blo 1849626 21069557 := bstep (se 5 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 21069557 = 1975271) B1975271
theorem B7028471 : Blo 1849626 7028471 := bstep (se 1 (by rfl) ⟨5271353, by rfl⟩ : syracuseStep 7028471 = 10542707) B10542707
theorem B17784593 : Blo 1849626 17784593 := bstep (se 2 (by rfl) ⟨6669222, by rfl⟩ : syracuseStep 17784593 = 13338445) B13338445
theorem B2776871 : Blo 1849626 2776871 := bstep (se 1 (by rfl) ⟨2082653, by rfl⟩ : syracuseStep 2776871 = 4165307) B4165307
theorem B1851207 : Blo 1849626 1851207 := bstep (se 1 (by rfl) ⟨1388405, by rfl⟩ : syracuseStep 1851207 = 2776811) B2776811
theorem B2776955 : Blo 1849626 2776955 := bstep (se 1 (by rfl) ⟨2082716, by rfl⟩ : syracuseStep 2776955 = 4165433) B4165433
theorem B1851359 : Blo 1849626 1851359 := bstep (se 1 (by rfl) ⟨1388519, by rfl⟩ : syracuseStep 1851359 = 2777039) B2777039
theorem B14999525 : Blo 1849626 14999525 := bstep (se 4 (by rfl) ⟨1406205, by rfl⟩ : syracuseStep 14999525 = 2812411) B2812411
theorem B7028927 : Blo 1849626 7028927 := bstep (se 1 (by rfl) ⟨5271695, by rfl⟩ : syracuseStep 7028927 = 10543391) B10543391
theorem B1851583 : Blo 1849626 1851583 := bstep (se 1 (by rfl) ⟨1388687, by rfl⟩ : syracuseStep 1851583 = 2777375) B2777375
theorem B2080975 : Blo 1849626 2080975 := bstep (se 1 (by rfl) ⟨1560731, by rfl⟩ : syracuseStep 2080975 = 3121463) B3121463
theorem B1851599 : Blo 1849626 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B2965739 : Blo 1849626 2965739 := bstep (se 1 (by rfl) ⟨2224304, by rfl⟩ : syracuseStep 2965739 = 4448609) B4448609
theorem B9372023 : Blo 1849626 9372023 := bstep (se 1 (by rfl) ⟨7029017, by rfl⟩ : syracuseStep 9372023 = 14058035) B14058035
theorem B22520207 : Blo 1849626 22520207 := bstep (se 1 (by rfl) ⟨16890155, by rfl⟩ : syracuseStep 22520207 = 33780311) B33780311
theorem B9363923 : Blo 1849626 9363923 := bstep (se 1 (by rfl) ⟨7022942, by rfl⟩ : syracuseStep 9363923 = 14045885) B14045885
theorem B4686295 : Blo 1849626 4686295 := bstep (se 1 (by rfl) ⟨3514721, by rfl⟩ : syracuseStep 4686295 = 7029443) B7029443
theorem B5931863 : Blo 1849626 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B8889259 : Blo 1849626 8889259 := bstep (se 1 (by rfl) ⟨6666944, by rfl⟩ : syracuseStep 8889259 = 13333889) B13333889
theorem B14058521 : Blo 1849626 14058521 := bstep (se 2 (by rfl) ⟨5271945, by rfl⟩ : syracuseStep 14058521 = 10543891) B10543891
theorem B2081839 : Blo 1849626 2081839 := bstep (se 1 (by rfl) ⟨1561379, by rfl⟩ : syracuseStep 2081839 = 3122759) B3122759
theorem B4162751 : Blo 1849626 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B2081983 : Blo 1849626 2081983 := bstep (se 1 (by rfl) ⟨1561487, by rfl⟩ : syracuseStep 2081983 = 3122975) B3122975
theorem B1975519 : Blo 1849626 1975519 := bstep (se 1 (by rfl) ⟨1481639, by rfl⟩ : syracuseStep 1975519 = 2963279) B2963279
theorem B3122489 : Blo 1849626 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B4162895 : Blo 1849626 4162895 := bstep (se 1 (by rfl) ⟨3122171, by rfl⟩ : syracuseStep 4162895 = 6244343) B6244343
theorem B2082127 : Blo 1849626 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B4162985 : Blo 1849626 4162985 := bstep (se 2 (by rfl) ⟨1561119, by rfl⟩ : syracuseStep 4162985 = 3122239) B3122239
theorem B4163471 : Blo 1849626 4163471 := bstep (se 1 (by rfl) ⟨3122603, by rfl⟩ : syracuseStep 4163471 = 6245207) B6245207
theorem B14059493 : Blo 1849626 14059493 := bstep (se 4 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 14059493 = 2636155) B2636155
theorem B7505945 : Blo 1849626 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B4163615 : Blo 1849626 4163615 := bstep (se 1 (by rfl) ⟨3122711, by rfl⟩ : syracuseStep 4163615 = 6245423) B6245423
theorem B2082847 : Blo 1849626 2082847 := bstep (se 1 (by rfl) ⟨1562135, by rfl⟩ : syracuseStep 2082847 = 3124271) B3124271
theorem B8890489 : Blo 1849626 8890489 := bstep (se 2 (by rfl) ⟨3333933, by rfl⟩ : syracuseStep 8890489 = 6667867) B6667867
theorem B13338847 : Blo 1849626 13338847 := bstep (se 1 (by rfl) ⟨10004135, by rfl⟩ : syracuseStep 13338847 = 20008271) B20008271
theorem B4163867 : Blo 1849626 4163867 := bstep (se 1 (by rfl) ⟨3122900, by rfl⟩ : syracuseStep 4163867 = 6245801) B6245801
theorem B11856395 : Blo 1849626 11856395 := bstep (se 1 (by rfl) ⟨8892296, by rfl⟩ : syracuseStep 11856395 = 17784593) B17784593
theorem B4164191 : Blo 1849626 4164191 := bstep (se 1 (by rfl) ⟨3123143, by rfl⟩ : syracuseStep 4164191 = 6246287) B6246287
theorem B14437025 : Blo 1849626 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B4164443 : Blo 1849626 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B26692577 : Blo 1849626 26692577 := bstep (se 2 (by rfl) ⟨10009716, by rfl⟩ : syracuseStep 26692577 = 20019433) B20019433
theorem B113929487 : Blo 1849626 113929487 := bstep (se 1 (by rfl) ⟨85447115, by rfl⟩ : syracuseStep 113929487 = 170894231) B170894231
theorem B6008327 : Blo 1849626 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B4165199 : Blo 1849626 4165199 := bstep (se 1 (by rfl) ⟨3123899, by rfl⟩ : syracuseStep 4165199 = 6247799) B6247799
theorem B160140887 : Blo 1849626 160140887 := bstep (se 1 (by rfl) ⟨120105665, by rfl⟩ : syracuseStep 160140887 = 240211331) B240211331
theorem B12660389 : Blo 1849626 12660389 := bstep (se 4 (by rfl) ⟨1186911, by rfl⟩ : syracuseStep 12660389 = 2373823) B2373823
theorem B15814439 : Blo 1849626 15814439 := bstep (se 1 (by rfl) ⟨11860829, by rfl⟩ : syracuseStep 15814439 = 23721659) B23721659
theorem B5001031 : Blo 1849626 5001031 := bstep (se 1 (by rfl) ⟨3750773, by rfl⟩ : syracuseStep 5001031 = 7501547) B7501547
theorem B6246395 : Blo 1849626 6246395 := bstep (se 1 (by rfl) ⟨4684796, by rfl⟩ : syracuseStep 6246395 = 9369593) B9369593
theorem B3166303 : Blo 1849626 3166303 := bstep (se 1 (by rfl) ⟨2374727, by rfl⟩ : syracuseStep 3166303 = 4749455) B4749455
theorem B9367649 : Blo 1849626 9367649 := bstep (se 2 (by rfl) ⟨3512868, by rfl⟩ : syracuseStep 9367649 = 7025737) B7025737
theorem B4165739 : Blo 1849626 4165739 := bstep (se 1 (by rfl) ⟨3124304, by rfl⟩ : syracuseStep 4165739 = 6248609) B6248609
theorem B4681871 : Blo 1849626 4681871 := bstep (se 1 (by rfl) ⟨3511403, by rfl⟩ : syracuseStep 4681871 = 7022807) B7022807
theorem B4165793 : Blo 1849626 4165793 := bstep (se 2 (by rfl) ⟨1562172, by rfl⟩ : syracuseStep 4165793 = 3124345) B3124345
theorem B47436029 : Blo 1849626 47436029 := bstep (se 3 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 47436029 = 17788511) B17788511
theorem B4165919 : Blo 1849626 4165919 := bstep (se 1 (by rfl) ⟨3124439, by rfl⟩ : syracuseStep 4165919 = 6248879) B6248879
theorem B7901495 : Blo 1849626 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B9498991 : Blo 1849626 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B30437927 : Blo 1849626 30437927 := bstep (se 1 (by rfl) ⟨22828445, by rfl⟩ : syracuseStep 30437927 = 45656891) B45656891
theorem B6247259 : Blo 1849626 6247259 := bstep (se 1 (by rfl) ⟨4685444, by rfl⟩ : syracuseStep 6247259 = 9370889) B9370889
theorem B59356079 : Blo 1849626 59356079 := bstep (se 1 (by rfl) ⟨44517059, by rfl⟩ : syracuseStep 59356079 = 89034119) B89034119
theorem B7025723 : Blo 1849626 7025723 := bstep (se 1 (by rfl) ⟨5269292, by rfl⟩ : syracuseStep 7025723 = 10538585) B10538585
theorem B14046371 : Blo 1849626 14046371 := bstep (se 1 (by rfl) ⟨10534778, by rfl⟩ : syracuseStep 14046371 = 21069557) B21069557
theorem B9999683 : Blo 1849626 9999683 := bstep (se 1 (by rfl) ⟨7499762, by rfl⟩ : syracuseStep 9999683 = 14999525) B14999525
theorem B7501223 : Blo 1849626 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B5928403 : Blo 1849626 5928403 := bstep (se 1 (by rfl) ⟨4446302, by rfl⟩ : syracuseStep 5928403 = 8892605) B8892605
theorem B9369107 : Blo 1849626 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B7501403 : Blo 1849626 7501403 := bstep (se 1 (by rfl) ⟨5626052, by rfl⟩ : syracuseStep 7501403 = 11252105) B11252105
theorem B66795131 : Blo 1849626 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B14046857 : Blo 1849626 14046857 := bstep (se 2 (by rfl) ⟨5267571, by rfl⟩ : syracuseStep 14046857 = 10535143) B10535143
theorem B5928673 : Blo 1849626 5928673 := bstep (se 2 (by rfl) ⟨2223252, by rfl⟩ : syracuseStep 5928673 = 4446505) B4446505
theorem B30414647 : Blo 1849626 30414647 := bstep (se 1 (by rfl) ⟨22810985, by rfl⟩ : syracuseStep 30414647 = 45621971) B45621971
theorem B2774855 : Blo 1849626 2774855 := bstep (se 1 (by rfl) ⟨2081141, by rfl⟩ : syracuseStep 2774855 = 4162283) B4162283
theorem B3512155 : Blo 1849626 3512155 := bstep (se 1 (by rfl) ⟨2634116, by rfl⟩ : syracuseStep 3512155 = 5268233) B5268233
theorem B35575793 : Blo 1849626 35575793 := bstep (se 2 (by rfl) ⟨13340922, by rfl⟩ : syracuseStep 35575793 = 26681845) B26681845
theorem B22509697 : Blo 1849626 22509697 := bstep (se 2 (by rfl) ⟨8441136, by rfl⟩ : syracuseStep 22509697 = 16882273) B16882273
theorem B8009927 : Blo 1849626 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B7026983 : Blo 1849626 7026983 := bstep (se 1 (by rfl) ⟨5270237, by rfl⟩ : syracuseStep 7026983 = 10540475) B10540475
theorem B1849759 : Blo 1849626 1849759 := bstep (se 1 (by rfl) ⟨1387319, by rfl⟩ : syracuseStep 1849759 = 2774639) B2774639
theorem B2775455 : Blo 1849626 2775455 := bstep (se 1 (by rfl) ⟨2081591, by rfl⟩ : syracuseStep 2775455 = 4163183) B4163183
theorem B1849807 : Blo 1849626 1849807 := bstep (se 1 (by rfl) ⟨1387355, by rfl⟩ : syracuseStep 1849807 = 2774711) B2774711
theorem B1849831 : Blo 1849626 1849831 := bstep (se 1 (by rfl) ⟨1387373, by rfl⟩ : syracuseStep 1849831 = 2774747) B2774747
theorem B2775527 : Blo 1849626 2775527 := bstep (se 1 (by rfl) ⟨2081645, by rfl⟩ : syracuseStep 2775527 = 4163291) B4163291
theorem B6248987 : Blo 1849626 6248987 := bstep (se 1 (by rfl) ⟨4686740, by rfl⟩ : syracuseStep 6248987 = 9373481) B9373481
theorem B31619645 : Blo 1849626 31619645 := bstep (se 3 (by rfl) ⟨5928683, by rfl⟩ : syracuseStep 31619645 = 11857367) B11857367
theorem B1849947 : Blo 1849626 1849947 := bstep (se 1 (by rfl) ⟨1387460, by rfl⟩ : syracuseStep 1849947 = 2774921) B2774921
theorem B13335131 : Blo 1849626 13335131 := bstep (se 1 (by rfl) ⟨10001348, by rfl⟩ : syracuseStep 13335131 = 20002697) B20002697
theorem B1850015 : Blo 1849626 1850015 := bstep (se 1 (by rfl) ⟨1387511, by rfl⟩ : syracuseStep 1850015 = 2775023) B2775023
theorem B4684513 : Blo 1849626 4684513 := bstep (se 2 (by rfl) ⟨1756692, by rfl⟩ : syracuseStep 4684513 = 3513385) B3513385
theorem B1850183 : Blo 1849626 1850183 := bstep (se 1 (by rfl) ⟨1387637, by rfl⟩ : syracuseStep 1850183 = 2775275) B2775275
theorem B32037743 : Blo 1849626 32037743 := bstep (se 1 (by rfl) ⟨24028307, by rfl⟩ : syracuseStep 32037743 = 48056615) B48056615
theorem B1850223 : Blo 1849626 1850223 := bstep (se 1 (by rfl) ⟨1387667, by rfl⟩ : syracuseStep 1850223 = 2775335) B2775335
theorem B1850279 : Blo 1849626 1850279 := bstep (se 1 (by rfl) ⟨1387709, by rfl⟩ : syracuseStep 1850279 = 2775419) B2775419
theorem B7027667 : Blo 1849626 7027667 := bstep (se 1 (by rfl) ⟨5270750, by rfl⟩ : syracuseStep 7027667 = 10541501) B10541501
theorem B7027681 : Blo 1849626 7027681 := bstep (se 2 (by rfl) ⟨2635380, by rfl⟩ : syracuseStep 7027681 = 5270761) B5270761
theorem B7904297 : Blo 1849626 7904297 := bstep (se 2 (by rfl) ⟨2964111, by rfl⟩ : syracuseStep 7904297 = 5928223) B5928223
theorem B1850459 : Blo 1849626 1850459 := bstep (se 1 (by rfl) ⟨1387844, by rfl⟩ : syracuseStep 1850459 = 2775689) B2775689
theorem B6667463 : Blo 1849626 6667463 := bstep (se 1 (by rfl) ⟨5000597, by rfl⟩ : syracuseStep 6667463 = 10001195) B10001195
theorem B1850575 : Blo 1849626 1850575 := bstep (se 1 (by rfl) ⟨1387931, by rfl⟩ : syracuseStep 1850575 = 2775863) B2775863
theorem B2776271 : Blo 1849626 2776271 := bstep (se 1 (by rfl) ⟨2082203, by rfl⟩ : syracuseStep 2776271 = 4164407) B4164407
theorem B1850599 : Blo 1849626 1850599 := bstep (se 1 (by rfl) ⟨1387949, by rfl⟩ : syracuseStep 1850599 = 2775899) B2775899
theorem B7027955 : Blo 1849626 7027955 := bstep (se 1 (by rfl) ⟨5270966, by rfl⟩ : syracuseStep 7027955 = 10541933) B10541933
theorem B1850695 : Blo 1849626 1850695 := bstep (se 1 (by rfl) ⟨1388021, by rfl⟩ : syracuseStep 1850695 = 2776043) B2776043
theorem B2776391 : Blo 1849626 2776391 := bstep (se 1 (by rfl) ⟨2082293, by rfl⟩ : syracuseStep 2776391 = 4164587) B4164587
theorem B9141599 : Blo 1849626 9141599 := bstep (se 1 (by rfl) ⟨6856199, by rfl⟩ : syracuseStep 9141599 = 13712399) B13712399
theorem B33775049 : Blo 1849626 33775049 := bstep (se 2 (by rfl) ⟨12665643, by rfl⟩ : syracuseStep 33775049 = 25331287) B25331287
theorem B1850831 : Blo 1849626 1850831 := bstep (se 1 (by rfl) ⟨1388123, by rfl⟩ : syracuseStep 1850831 = 2776247) B2776247
theorem B2776553 : Blo 1849626 2776553 := bstep (se 2 (by rfl) ⟨1041207, by rfl⟩ : syracuseStep 2776553 = 2082415) B2082415
theorem B14048801 : Blo 1849626 14048801 := bstep (se 2 (by rfl) ⟨5268300, by rfl⟩ : syracuseStep 14048801 = 10536601) B10536601
theorem B1850991 : Blo 1849626 1850991 := bstep (se 1 (by rfl) ⟨1388243, by rfl⟩ : syracuseStep 1850991 = 2776487) B2776487
theorem B2776697 : Blo 1849626 2776697 := bstep (se 2 (by rfl) ⟨1041261, by rfl⟩ : syracuseStep 2776697 = 2082523) B2082523
theorem B1851047 : Blo 1849626 1851047 := bstep (se 1 (by rfl) ⟨1388285, by rfl⟩ : syracuseStep 1851047 = 2776571) B2776571
theorem B1851111 : Blo 1849626 1851111 := bstep (se 1 (by rfl) ⟨1388333, by rfl⟩ : syracuseStep 1851111 = 2776667) B2776667
theorem B5267231 : Blo 1849626 5267231 := bstep (se 1 (by rfl) ⟨3950423, by rfl⟩ : syracuseStep 5267231 = 7900847) B7900847
theorem B1851167 : Blo 1849626 1851167 := bstep (se 1 (by rfl) ⟨1388375, by rfl⟩ : syracuseStep 1851167 = 2776751) B2776751
theorem B4685647 : Blo 1849626 4685647 := bstep (se 1 (by rfl) ⟨3514235, by rfl⟩ : syracuseStep 4685647 = 7028471) B7028471
theorem B1851247 : Blo 1849626 1851247 := bstep (se 1 (by rfl) ⟨1388435, by rfl⟩ : syracuseStep 1851247 = 2776871) B2776871
theorem B2776943 : Blo 1849626 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B1851303 : Blo 1849626 1851303 := bstep (se 1 (by rfl) ⟨1388477, by rfl⟩ : syracuseStep 1851303 = 2776955) B2776955
theorem B22519781 : Blo 1849626 22519781 := bstep (se 4 (by rfl) ⟨2111229, by rfl⟩ : syracuseStep 22519781 = 4222459) B4222459
theorem B2777129 : Blo 1849626 2777129 := bstep (se 2 (by rfl) ⟨1041423, by rfl⟩ : syracuseStep 2777129 = 2082847) B2082847
theorem B2777159 : Blo 1849626 2777159 := bstep (se 1 (by rfl) ⟨2082869, by rfl⟩ : syracuseStep 2777159 = 4165739) B4165739
theorem B3121247 : Blo 1849626 3121247 := bstep (se 1 (by rfl) ⟨2340935, by rfl⟩ : syracuseStep 3121247 = 4681871) B4681871
theorem B2777195 : Blo 1849626 2777195 := bstep (se 1 (by rfl) ⟨2082896, by rfl⟩ : syracuseStep 2777195 = 4165793) B4165793
theorem B4685951 : Blo 1849626 4685951 := bstep (se 1 (by rfl) ⟨3514463, by rfl⟩ : syracuseStep 4685951 = 7028927) B7028927
theorem B11853985 : Blo 1849626 11853985 := bstep (se 2 (by rfl) ⟨4445244, by rfl⟩ : syracuseStep 11853985 = 8890489) B8890489
theorem B2777279 : Blo 1849626 2777279 := bstep (se 1 (by rfl) ⟨2082959, by rfl⟩ : syracuseStep 2777279 = 4165919) B4165919
theorem B5267663 : Blo 1849626 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B17785129 : Blo 1849626 17785129 := bstep (se 2 (by rfl) ⟨6669423, by rfl⟩ : syracuseStep 17785129 = 13338847) B13338847
theorem B6242615 : Blo 1849626 6242615 := bstep (se 1 (by rfl) ⟨4681961, by rfl⟩ : syracuseStep 6242615 = 9363923) B9363923
theorem B20291951 : Blo 1849626 20291951 := bstep (se 1 (by rfl) ⟨15218963, by rfl⟩ : syracuseStep 20291951 = 30437927) B30437927
theorem B12665321 : Blo 1849626 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B9372347 : Blo 1849626 9372347 := bstep (se 1 (by rfl) ⟨7029260, by rfl⟩ : syracuseStep 9372347 = 14058521) B14058521
theorem B9364247 : Blo 1849626 9364247 := bstep (se 1 (by rfl) ⟨7023185, by rfl⟩ : syracuseStep 9364247 = 14046371) B14046371
theorem B2081659 : Blo 1849626 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B9364571 : Blo 1849626 9364571 := bstep (se 1 (by rfl) ⟨7023428, by rfl⟩ : syracuseStep 9364571 = 14046857) B14046857
theorem B10536101 : Blo 1849626 10536101 := bstep (se 4 (by rfl) ⟨987759, by rfl⟩ : syracuseStep 10536101 = 1975519) B1975519
theorem B9372995 : Blo 1849626 9372995 := bstep (se 1 (by rfl) ⟨7029746, by rfl⟩ : syracuseStep 9372995 = 14059493) B14059493
theorem B23717195 : Blo 1849626 23717195 := bstep (se 1 (by rfl) ⟨17787896, by rfl⟩ : syracuseStep 23717195 = 35575793) B35575793
theorem B178120349 : Blo 1849626 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B21079763 : Blo 1849626 21079763 := bstep (se 1 (by rfl) ⟨15809822, by rfl⟩ : syracuseStep 21079763 = 31619645) B31619645
theorem B8890087 : Blo 1849626 8890087 := bstep (se 1 (by rfl) ⟨6667565, by rfl⟩ : syracuseStep 8890087 = 13335131) B13335131
theorem B21358495 : Blo 1849626 21358495 := bstep (se 1 (by rfl) ⟨16018871, by rfl⟩ : syracuseStep 21358495 = 32037743) B32037743
theorem B2532526037 : Blo 1849626 2532526037 := bstep (se 7 (by rfl) ⟨29678039, by rfl⟩ : syracuseStep 2532526037 = 59356079) B59356079
theorem B17795051 : Blo 1849626 17795051 := bstep (se 1 (by rfl) ⟨13346288, by rfl⟩ : syracuseStep 17795051 = 26692577) B26692577
theorem B5269531 : Blo 1849626 5269531 := bstep (se 1 (by rfl) ⟨3952148, by rfl⟩ : syracuseStep 5269531 = 7904297) B7904297
theorem B9365867 : Blo 1849626 9365867 := bstep (se 1 (by rfl) ⟨7024400, by rfl⟩ : syracuseStep 9365867 = 14048801) B14048801
theorem B106760591 : Blo 1849626 106760591 := bstep (se 1 (by rfl) ⟨80070443, by rfl⟩ : syracuseStep 106760591 = 160140887) B160140887
theorem B8440259 : Blo 1849626 8440259 := bstep (se 1 (by rfl) ⟨6330194, by rfl⟩ : syracuseStep 8440259 = 12660389) B12660389
theorem B4164263 : Blo 1849626 4164263 := bstep (se 1 (by rfl) ⟨3123197, by rfl⟩ : syracuseStep 4164263 = 6246395) B6246395
theorem B6245099 : Blo 1849626 6245099 := bstep (se 1 (by rfl) ⟨4683824, by rfl⟩ : syracuseStep 6245099 = 9367649) B9367649
theorem B4221737 : Blo 1849626 4221737 := bstep (se 2 (by rfl) ⟨1583151, by rfl⟩ : syracuseStep 4221737 = 3166303) B3166303
theorem B31624019 : Blo 1849626 31624019 := bstep (se 1 (by rfl) ⟨23718014, by rfl⟩ : syracuseStep 31624019 = 47436029) B47436029
theorem B4164839 : Blo 1849626 4164839 := bstep (se 1 (by rfl) ⟨3123629, by rfl⟩ : syracuseStep 4164839 = 6247259) B6247259
theorem B7908637 : Blo 1849626 7908637 := bstep (se 3 (by rfl) ⟨1482869, by rfl⟩ : syracuseStep 7908637 = 2965739) B2965739
theorem B5000815 : Blo 1849626 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B6246017 : Blo 1849626 6246017 := bstep (se 2 (by rfl) ⟨2342256, by rfl⟩ : syracuseStep 6246017 = 4684513) B4684513
theorem B6246071 : Blo 1849626 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B5000935 : Blo 1849626 5000935 := bstep (se 1 (by rfl) ⟨3750701, by rfl⟩ : syracuseStep 5000935 = 7501403) B7501403
theorem B4165991 : Blo 1849626 4165991 := bstep (se 1 (by rfl) ⟨3124493, by rfl⟩ : syracuseStep 4165991 = 6248987) B6248987
theorem B4444975 : Blo 1849626 4444975 := bstep (se 1 (by rfl) ⟨3333731, by rfl⟩ : syracuseStep 4444975 = 6667463) B6667463
theorem B81105725 : Blo 1849626 81105725 := bstep (se 3 (by rfl) ⟨15207323, by rfl⟩ : syracuseStep 81105725 = 30414647) B30414647
theorem B75952991 : Blo 1849626 75952991 := bstep (se 1 (by rfl) ⟨56964743, by rfl⟩ : syracuseStep 75952991 = 113929487) B113929487
theorem B22516699 : Blo 1849626 22516699 := bstep (se 1 (by rfl) ⟨16887524, by rfl⟩ : syracuseStep 22516699 = 33775049) B33775049
theorem B6247529 : Blo 1849626 6247529 := bstep (se 2 (by rfl) ⟨2342823, by rfl⟩ : syracuseStep 6247529 = 4685647) B4685647
theorem B4682873 : Blo 1849626 4682873 := bstep (se 2 (by rfl) ⟨1756077, by rfl⟩ : syracuseStep 4682873 = 3512155) B3512155
theorem B3511487 : Blo 1849626 3511487 := bstep (se 1 (by rfl) ⟨2633615, by rfl⟩ : syracuseStep 3511487 = 5267231) B5267231
theorem B15013187 : Blo 1849626 15013187 := bstep (se 1 (by rfl) ⟨11259890, by rfl⟩ : syracuseStep 15013187 = 22519781) B22519781
theorem B30012929 : Blo 1849626 30012929 := bstep (se 2 (by rfl) ⟨11254848, by rfl⟩ : syracuseStep 30012929 = 22509697) B22509697
theorem B6248015 : Blo 1849626 6248015 := bstep (se 1 (by rfl) ⟨4686011, by rfl⟩ : syracuseStep 6248015 = 9372023) B9372023
theorem B15013471 : Blo 1849626 15013471 := bstep (se 1 (by rfl) ⟨11260103, by rfl⟩ : syracuseStep 15013471 = 22520207) B22520207
theorem B2774633 : Blo 1849626 2774633 := bstep (se 2 (by rfl) ⟨1040487, by rfl⟩ : syracuseStep 2774633 = 2080975) B2080975
theorem B3954575 : Blo 1849626 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B6248393 : Blo 1849626 6248393 := bstep (se 2 (by rfl) ⟨2343147, by rfl⟩ : syracuseStep 6248393 = 4686295) B4686295
theorem B4683815 : Blo 1849626 4683815 := bstep (se 1 (by rfl) ⟨3512861, by rfl⟩ : syracuseStep 4683815 = 7025723) B7025723
theorem B2775167 : Blo 1849626 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B6666455 : Blo 1849626 6666455 := bstep (se 1 (by rfl) ⟨4999841, by rfl⟩ : syracuseStep 6666455 = 9999683) B9999683
theorem B2775263 : Blo 1849626 2775263 := bstep (se 1 (by rfl) ⟨2081447, by rfl⟩ : syracuseStep 2775263 = 4162895) B4162895
theorem B2775323 : Blo 1849626 2775323 := bstep (se 1 (by rfl) ⟨2081492, by rfl⟩ : syracuseStep 2775323 = 4162985) B4162985
theorem B1849903 : Blo 1849626 1849903 := bstep (se 1 (by rfl) ⟨1387427, by rfl⟩ : syracuseStep 1849903 = 2774855) B2774855
theorem B11852345 : Blo 1849626 11852345 := bstep (se 2 (by rfl) ⟨4444629, by rfl⟩ : syracuseStep 11852345 = 8889259) B8889259
theorem B2775647 : Blo 1849626 2775647 := bstep (se 1 (by rfl) ⟨2081735, by rfl⟩ : syracuseStep 2775647 = 4163471) B4163471
theorem B9370241 : Blo 1849626 9370241 := bstep (se 2 (by rfl) ⟨3513840, by rfl⟩ : syracuseStep 9370241 = 7027681) B7027681
theorem B5003963 : Blo 1849626 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B2775743 : Blo 1849626 2775743 := bstep (se 1 (by rfl) ⟨2081807, by rfl⟩ : syracuseStep 2775743 = 4163615) B4163615
theorem B2775785 : Blo 1849626 2775785 := bstep (se 2 (by rfl) ⟨1040919, by rfl⟩ : syracuseStep 2775785 = 2081839) B2081839
theorem B5339951 : Blo 1849626 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B2775911 : Blo 1849626 2775911 := bstep (se 1 (by rfl) ⟨2081933, by rfl⟩ : syracuseStep 2775911 = 4163867) B4163867
theorem B4684655 : Blo 1849626 4684655 := bstep (se 1 (by rfl) ⟨3513491, by rfl⟩ : syracuseStep 4684655 = 7026983) B7026983
theorem B2775977 : Blo 1849626 2775977 := bstep (se 2 (by rfl) ⟨1040991, by rfl⟩ : syracuseStep 2775977 = 2081983) B2081983
theorem B1850303 : Blo 1849626 1850303 := bstep (se 1 (by rfl) ⟨1387727, by rfl⟩ : syracuseStep 1850303 = 2775455) B2775455
theorem B1850351 : Blo 1849626 1850351 := bstep (se 1 (by rfl) ⟨1387763, by rfl⟩ : syracuseStep 1850351 = 2775527) B2775527
theorem B7904263 : Blo 1849626 7904263 := bstep (se 1 (by rfl) ⟨5928197, by rfl⟩ : syracuseStep 7904263 = 11856395) B11856395
theorem B2776127 : Blo 1849626 2776127 := bstep (se 1 (by rfl) ⟨2082095, by rfl⟩ : syracuseStep 2776127 = 4164191) B4164191
theorem B2776169 : Blo 1849626 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B9624683 : Blo 1849626 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B2776295 : Blo 1849626 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B7904537 : Blo 1849626 7904537 := bstep (se 2 (by rfl) ⟨2964201, by rfl⟩ : syracuseStep 7904537 = 5928403) B5928403
theorem B4685111 : Blo 1849626 4685111 := bstep (se 1 (by rfl) ⟨3513833, by rfl⟩ : syracuseStep 4685111 = 7027667) B7027667
theorem B1850847 : Blo 1849626 1850847 := bstep (se 1 (by rfl) ⟨1388135, by rfl⟩ : syracuseStep 1850847 = 2776271) B2776271
theorem B4685303 : Blo 1849626 4685303 := bstep (se 1 (by rfl) ⟨3513977, by rfl⟩ : syracuseStep 4685303 = 7027955) B7027955
theorem B1850927 : Blo 1849626 1850927 := bstep (se 1 (by rfl) ⟨1388195, by rfl⟩ : syracuseStep 1850927 = 2776391) B2776391
theorem B6094399 : Blo 1849626 6094399 := bstep (se 1 (by rfl) ⟨4570799, by rfl⟩ : syracuseStep 6094399 = 9141599) B9141599
theorem B7904897 : Blo 1849626 7904897 := bstep (se 2 (by rfl) ⟨2964336, by rfl⟩ : syracuseStep 7904897 = 5928673) B5928673
theorem B1851035 : Blo 1849626 1851035 := bstep (se 1 (by rfl) ⟨1388276, by rfl⟩ : syracuseStep 1851035 = 2776553) B2776553
theorem B4005551 : Blo 1849626 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B2776799 : Blo 1849626 2776799 := bstep (se 1 (by rfl) ⟨2082599, by rfl⟩ : syracuseStep 2776799 = 4165199) B4165199
theorem B1851131 : Blo 1849626 1851131 := bstep (se 1 (by rfl) ⟨1388348, by rfl⟩ : syracuseStep 1851131 = 2776697) B2776697
theorem B6668041 : Blo 1849626 6668041 := bstep (se 2 (by rfl) ⟨2500515, by rfl⟩ : syracuseStep 6668041 = 5001031) B5001031
theorem B10542959 : Blo 1849626 10542959 := bstep (se 1 (by rfl) ⟨7907219, by rfl⟩ : syracuseStep 10542959 = 15814439) B15814439
theorem B1851295 : Blo 1849626 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B1851419 : Blo 1849626 1851419 := bstep (se 1 (by rfl) ⟨1388564, by rfl⟩ : syracuseStep 1851419 = 2777129) B2777129
theorem B1851439 : Blo 1849626 1851439 := bstep (se 1 (by rfl) ⟨1388579, by rfl⟩ : syracuseStep 1851439 = 2777159) B2777159
theorem B2080831 : Blo 1849626 2080831 := bstep (se 1 (by rfl) ⟨1560623, by rfl⟩ : syracuseStep 2080831 = 3121247) B3121247
theorem B1851463 : Blo 1849626 1851463 := bstep (se 1 (by rfl) ⟨1388597, by rfl⟩ : syracuseStep 1851463 = 2777195) B2777195
theorem B1851519 : Blo 1849626 1851519 := bstep (se 1 (by rfl) ⟨1388639, by rfl⟩ : syracuseStep 1851519 = 2777279) B2777279
theorem B4161743 : Blo 1849626 4161743 := bstep (se 1 (by rfl) ⟨3121307, by rfl⟩ : syracuseStep 4161743 = 6242615) B6242615
theorem B2777327 : Blo 1849626 2777327 := bstep (se 1 (by rfl) ⟨2082995, by rfl⟩ : syracuseStep 2777327 = 4165991) B4165991
theorem B25665821 : Blo 1849626 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B6242831 : Blo 1849626 6242831 := bstep (se 1 (by rfl) ⟨4682123, by rfl⟩ : syracuseStep 6242831 = 9364247) B9364247
theorem B50635327 : Blo 1849626 50635327 := bstep (se 1 (by rfl) ⟨37976495, by rfl⟩ : syracuseStep 50635327 = 75952991) B75952991
theorem B6243047 : Blo 1849626 6243047 := bstep (se 1 (by rfl) ⟨4682285, by rfl⟩ : syracuseStep 6243047 = 9364571) B9364571
theorem B3121915 : Blo 1849626 3121915 := bstep (se 1 (by rfl) ⟨2341436, by rfl⟩ : syracuseStep 3121915 = 4682873) B4682873
theorem B15811463 : Blo 1849626 15811463 := bstep (se 1 (by rfl) ⟨11858597, by rfl⟩ : syracuseStep 15811463 = 23717195) B23717195
theorem B11863367 : Blo 1849626 11863367 := bstep (se 1 (by rfl) ⟨8897525, by rfl⟩ : syracuseStep 11863367 = 17795051) B17795051
theorem B3122543 : Blo 1849626 3122543 := bstep (se 1 (by rfl) ⟨2341907, by rfl⟩ : syracuseStep 3122543 = 4683815) B4683815
theorem B6243911 : Blo 1849626 6243911 := bstep (se 1 (by rfl) ⟨4682933, by rfl⟩ : syracuseStep 6243911 = 9365867) B9365867
theorem B71173727 : Blo 1849626 71173727 := bstep (se 1 (by rfl) ⟨53380295, by rfl⟩ : syracuseStep 71173727 = 106760591) B106760591
theorem B10544849 : Blo 1849626 10544849 := bstep (se 2 (by rfl) ⟨3954318, by rfl⟩ : syracuseStep 10544849 = 7908637) B7908637
theorem B3335975 : Blo 1849626 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B4163399 : Blo 1849626 4163399 := bstep (se 1 (by rfl) ⟨3122549, by rfl⟩ : syracuseStep 4163399 = 6245099) B6245099
theorem B3123103 : Blo 1849626 3123103 := bstep (se 1 (by rfl) ⟨2342327, by rfl⟩ : syracuseStep 3123103 = 4684655) B4684655
theorem B5269691 : Blo 1849626 5269691 := bstep (se 1 (by rfl) ⟨3952268, by rfl⟩ : syracuseStep 5269691 = 7904537) B7904537
theorem B3123407 : Blo 1849626 3123407 := bstep (se 1 (by rfl) ⟨2342555, by rfl⟩ : syracuseStep 3123407 = 4685111) B4685111
theorem B3123535 : Blo 1849626 3123535 := bstep (se 1 (by rfl) ⟨2342651, by rfl⟩ : syracuseStep 3123535 = 4685303) B4685303
theorem B8890721 : Blo 1849626 8890721 := bstep (se 2 (by rfl) ⟨3334020, by rfl⟩ : syracuseStep 8890721 = 6668041) B6668041
theorem B5269931 : Blo 1849626 5269931 := bstep (se 1 (by rfl) ⟨3952448, by rfl⟩ : syracuseStep 5269931 = 7904897) B7904897
theorem B4164011 : Blo 1849626 4164011 := bstep (se 1 (by rfl) ⟨3123008, by rfl⟩ : syracuseStep 4164011 = 6246017) B6246017
theorem B4164047 : Blo 1849626 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B28477993 : Blo 1849626 28477993 := bstep (se 2 (by rfl) ⟨10679247, by rfl⟩ : syracuseStep 28477993 = 21358495) B21358495
theorem B3123967 : Blo 1849626 3123967 := bstep (se 1 (by rfl) ⟨2342975, by rfl⟩ : syracuseStep 3123967 = 4685951) B4685951
theorem B15805313 : Blo 1849626 15805313 := bstep (se 2 (by rfl) ⟨5926992, by rfl⟩ : syracuseStep 15805313 = 11853985) B11853985
theorem B13527967 : Blo 1849626 13527967 := bstep (se 1 (by rfl) ⟨10145975, by rfl⟩ : syracuseStep 13527967 = 20291951) B20291951
theorem B54070483 : Blo 1849626 54070483 := bstep (se 1 (by rfl) ⟨40552862, by rfl⟩ : syracuseStep 54070483 = 81105725) B81105725
theorem B4165019 : Blo 1849626 4165019 := bstep (se 1 (by rfl) ⟨3123764, by rfl⟩ : syracuseStep 4165019 = 6247529) B6247529
theorem B7024067 : Blo 1849626 7024067 := bstep (se 1 (by rfl) ⟨5268050, by rfl⟩ : syracuseStep 7024067 = 10536101) B10536101
theorem B20008619 : Blo 1849626 20008619 := bstep (se 1 (by rfl) ⟨15006464, by rfl⟩ : syracuseStep 20008619 = 30012929) B30012929
theorem B4165343 : Blo 1849626 4165343 := bstep (se 1 (by rfl) ⟨3124007, by rfl⟩ : syracuseStep 4165343 = 6248015) B6248015
theorem B118746899 : Blo 1849626 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B14053175 : Blo 1849626 14053175 := bstep (se 1 (by rfl) ⟨10539881, by rfl⟩ : syracuseStep 14053175 = 21079763) B21079763
theorem B22507357 : Blo 1849626 22507357 := bstep (se 3 (by rfl) ⟨4220129, by rfl⟩ : syracuseStep 22507357 = 8440259) B8440259
theorem B4165595 : Blo 1849626 4165595 := bstep (se 1 (by rfl) ⟨3124196, by rfl⟩ : syracuseStep 4165595 = 6248393) B6248393
theorem B1688350691 : Blo 1849626 1688350691 := bstep (se 1 (by rfl) ⟨1266263018, by rfl⟩ : syracuseStep 1688350691 = 2532526037) B2532526037
theorem B10539017 : Blo 1849626 10539017 := bstep (se 2 (by rfl) ⟨3952131, by rfl⟩ : syracuseStep 10539017 = 7904263) B7904263
theorem B4444303 : Blo 1849626 4444303 := bstep (se 1 (by rfl) ⟨3333227, by rfl⟩ : syracuseStep 4444303 = 6666455) B6666455
theorem B7901563 : Blo 1849626 7901563 := bstep (se 1 (by rfl) ⟨5926172, by rfl⟩ : syracuseStep 7901563 = 11852345) B11852345
theorem B6246827 : Blo 1849626 6246827 := bstep (se 1 (by rfl) ⟨4685120, by rfl⟩ : syracuseStep 6246827 = 9370241) B9370241
theorem B2814491 : Blo 1849626 2814491 := bstep (se 1 (by rfl) ⟨2110868, by rfl⟩ : syracuseStep 2814491 = 4221737) B4221737
theorem B3559967 : Blo 1849626 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B21082679 : Blo 1849626 21082679 := bstep (se 1 (by rfl) ⟨15812009, by rfl⟩ : syracuseStep 21082679 = 31624019) B31624019
theorem B20017961 : Blo 1849626 20017961 := bstep (se 2 (by rfl) ⟨7506735, by rfl⟩ : syracuseStep 20017961 = 15013471) B15013471
theorem B7026041 : Blo 1849626 7026041 := bstep (se 2 (by rfl) ⟨2634765, by rfl⟩ : syracuseStep 7026041 = 5269531) B5269531
theorem B3511775 : Blo 1849626 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B8443547 : Blo 1849626 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B23713505 : Blo 1849626 23713505 := bstep (se 2 (by rfl) ⟨8892564, by rfl⟩ : syracuseStep 23713505 = 17785129) B17785129
theorem B6248231 : Blo 1849626 6248231 := bstep (se 1 (by rfl) ⟨4686173, by rfl⟩ : syracuseStep 6248231 = 9372347) B9372347
theorem B2340991 : Blo 1849626 2340991 := bstep (se 1 (by rfl) ⟨1755743, by rfl⟩ : syracuseStep 2340991 = 3511487) B3511487
theorem B10008791 : Blo 1849626 10008791 := bstep (se 1 (by rfl) ⟨7506593, by rfl⟩ : syracuseStep 10008791 = 15013187) B15013187
theorem B6248663 : Blo 1849626 6248663 := bstep (se 1 (by rfl) ⟨4686497, by rfl⟩ : syracuseStep 6248663 = 9372995) B9372995
theorem B1849755 : Blo 1849626 1849755 := bstep (se 1 (by rfl) ⟨1387316, by rfl⟩ : syracuseStep 1849755 = 2774633) B2774633
theorem B2775545 : Blo 1849626 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B2636383 : Blo 1849626 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B30022265 : Blo 1849626 30022265 := bstep (se 2 (by rfl) ⟨11258349, by rfl⟩ : syracuseStep 30022265 = 22516699) B22516699
theorem B1850111 : Blo 1849626 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B1850175 : Blo 1849626 1850175 := bstep (se 1 (by rfl) ⟨1387631, by rfl⟩ : syracuseStep 1850175 = 2775263) B2775263
theorem B1850215 : Blo 1849626 1850215 := bstep (se 1 (by rfl) ⟨1387661, by rfl⟩ : syracuseStep 1850215 = 2775323) B2775323
theorem B23706533 : Blo 1849626 23706533 := bstep (se 4 (by rfl) ⟨2222487, by rfl⟩ : syracuseStep 23706533 = 4444975) B4444975
theorem B1850431 : Blo 1849626 1850431 := bstep (se 1 (by rfl) ⟨1387823, by rfl⟩ : syracuseStep 1850431 = 2775647) B2775647
theorem B2776175 : Blo 1849626 2776175 := bstep (se 1 (by rfl) ⟨2082131, by rfl⟩ : syracuseStep 2776175 = 4164263) B4164263
theorem B10681469 : Blo 1849626 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B1850495 : Blo 1849626 1850495 := bstep (se 1 (by rfl) ⟨1387871, by rfl⟩ : syracuseStep 1850495 = 2775743) B2775743
theorem B1850523 : Blo 1849626 1850523 := bstep (se 1 (by rfl) ⟨1387892, by rfl⟩ : syracuseStep 1850523 = 2775785) B2775785
theorem B1850607 : Blo 1849626 1850607 := bstep (se 1 (by rfl) ⟨1387955, by rfl⟩ : syracuseStep 1850607 = 2775911) B2775911
theorem B1850651 : Blo 1849626 1850651 := bstep (se 1 (by rfl) ⟨1387988, by rfl⟩ : syracuseStep 1850651 = 2775977) B2775977
theorem B1850751 : Blo 1849626 1850751 := bstep (se 1 (by rfl) ⟨1388063, by rfl⟩ : syracuseStep 1850751 = 2776127) B2776127
theorem B1850779 : Blo 1849626 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B8125865 : Blo 1849626 8125865 := bstep (se 2 (by rfl) ⟨3047199, by rfl⟩ : syracuseStep 8125865 = 6094399) B6094399
theorem B6667753 : Blo 1849626 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B1850863 : Blo 1849626 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B2776559 : Blo 1849626 2776559 := bstep (se 1 (by rfl) ⟨2082419, by rfl⟩ : syracuseStep 2776559 = 4164839) B4164839
theorem B11853449 : Blo 1849626 11853449 := bstep (se 2 (by rfl) ⟨4445043, by rfl⟩ : syracuseStep 11853449 = 8890087) B8890087
theorem B6667913 : Blo 1849626 6667913 := bstep (se 2 (by rfl) ⟨2500467, by rfl⟩ : syracuseStep 6667913 = 5000935) B5000935
theorem B1851199 : Blo 1849626 1851199 := bstep (se 1 (by rfl) ⟨1388399, by rfl⟩ : syracuseStep 1851199 = 2776799) B2776799
theorem B7028639 : Blo 1849626 7028639 := bstep (se 1 (by rfl) ⟨5271479, by rfl⟩ : syracuseStep 7028639 = 10542959) B10542959
theorem B1851551 : Blo 1849626 1851551 := bstep (se 1 (by rfl) ⟨1388663, by rfl⟩ : syracuseStep 1851551 = 2777327) B2777327
theorem B3121321 : Blo 1849626 3121321 := bstep (se 2 (by rfl) ⟨1170495, by rfl⟩ : syracuseStep 3121321 = 2340991) B2340991
theorem B4161887 : Blo 1849626 4161887 := bstep (se 1 (by rfl) ⟨3121415, by rfl⟩ : syracuseStep 4161887 = 6242831) B6242831
theorem B1876327 : Blo 1849626 1876327 := bstep (se 1 (by rfl) ⟨1407245, by rfl⟩ : syracuseStep 1876327 = 2814491) B2814491
theorem B4162031 : Blo 1849626 4162031 := bstep (se 1 (by rfl) ⟨3121523, by rfl⟩ : syracuseStep 4162031 = 6243047) B6243047
theorem B10535417 : Blo 1849626 10535417 := bstep (se 2 (by rfl) ⟨3950781, by rfl⟩ : syracuseStep 10535417 = 7901563) B7901563
theorem B13345307 : Blo 1849626 13345307 := bstep (se 1 (by rfl) ⟨10008980, by rfl⟩ : syracuseStep 13345307 = 20017961) B20017961
theorem B37970657 : Blo 1849626 37970657 := bstep (se 2 (by rfl) ⟨14238996, by rfl⟩ : syracuseStep 37970657 = 28477993) B28477993
theorem B3515177 : Blo 1849626 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B2081695 : Blo 1849626 2081695 := bstep (se 1 (by rfl) ⟨1561271, by rfl⟩ : syracuseStep 2081695 = 3122543) B3122543
theorem B4162553 : Blo 1849626 4162553 := bstep (se 2 (by rfl) ⟨1560957, by rfl⟩ : syracuseStep 4162553 = 3121915) B3121915
theorem B4162607 : Blo 1849626 4162607 := bstep (se 1 (by rfl) ⟨3121955, by rfl⟩ : syracuseStep 4162607 = 6243911) B6243911
theorem B47449151 : Blo 1849626 47449151 := bstep (se 1 (by rfl) ⟨35586863, by rfl⟩ : syracuseStep 47449151 = 71173727) B71173727
theorem B5629031 : Blo 1849626 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B7029899 : Blo 1849626 7029899 := bstep (se 1 (by rfl) ⟨5272424, by rfl⟩ : syracuseStep 7029899 = 10544849) B10544849
theorem B9364733 : Blo 1849626 9364733 := bstep (se 3 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 9364733 = 3511775) B3511775
theorem B2082271 : Blo 1849626 2082271 := bstep (se 1 (by rfl) ⟨1561703, by rfl⟩ : syracuseStep 2082271 = 3123407) B3123407
theorem B10536875 : Blo 1849626 10536875 := bstep (se 1 (by rfl) ⟨7902656, by rfl⟩ : syracuseStep 10536875 = 15805313) B15805313
theorem B15804355 : Blo 1849626 15804355 := bstep (se 1 (by rfl) ⟨11853266, by rfl⟩ : syracuseStep 15804355 = 23706533) B23706533
theorem B8890337 : Blo 1849626 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B7120979 : Blo 1849626 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B5417243 : Blo 1849626 5417243 := bstep (se 1 (by rfl) ⟨4062932, by rfl⟩ : syracuseStep 5417243 = 8125865) B8125865
theorem B13339079 : Blo 1849626 13339079 := bstep (se 1 (by rfl) ⟨10004309, by rfl⟩ : syracuseStep 13339079 = 20008619) B20008619
theorem B30009809 : Blo 1849626 30009809 := bstep (se 2 (by rfl) ⟨11253678, by rfl⟩ : syracuseStep 30009809 = 22507357) B22507357
theorem B4164137 : Blo 1849626 4164137 := bstep (se 2 (by rfl) ⟨1561551, by rfl⟩ : syracuseStep 4164137 = 3123103) B3123103
theorem B1125567127 : Blo 1849626 1125567127 := bstep (se 1 (by rfl) ⟨844175345, by rfl⟩ : syracuseStep 1125567127 = 1688350691) B1688350691
theorem B5925737 : Blo 1849626 5925737 := bstep (se 2 (by rfl) ⟨2222151, by rfl⟩ : syracuseStep 5925737 = 4444303) B4444303
theorem B4164551 : Blo 1849626 4164551 := bstep (se 1 (by rfl) ⟨3123413, by rfl⟩ : syracuseStep 4164551 = 6246827) B6246827
theorem B4164713 : Blo 1849626 4164713 := bstep (se 2 (by rfl) ⟨1561767, by rfl⟩ : syracuseStep 4164713 = 3123535) B3123535
theorem B67513769 : Blo 1849626 67513769 := bstep (se 2 (by rfl) ⟨25317663, by rfl⟩ : syracuseStep 67513769 = 50635327) B50635327
theorem B7908911 : Blo 1849626 7908911 := bstep (se 1 (by rfl) ⟨5931683, by rfl⟩ : syracuseStep 7908911 = 11863367) B11863367
theorem B4165289 : Blo 1849626 4165289 := bstep (se 2 (by rfl) ⟨1561983, by rfl⟩ : syracuseStep 4165289 = 3123967) B3123967
theorem B2223983 : Blo 1849626 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B4165487 : Blo 1849626 4165487 := bstep (se 1 (by rfl) ⟨3124115, by rfl⟩ : syracuseStep 4165487 = 6248231) B6248231
theorem B6672527 : Blo 1849626 6672527 := bstep (se 1 (by rfl) ⟨5004395, by rfl⟩ : syracuseStep 6672527 = 10008791) B10008791
theorem B4165775 : Blo 1849626 4165775 := bstep (se 1 (by rfl) ⟨3124331, by rfl⟩ : syracuseStep 4165775 = 6248663) B6248663
theorem B5927147 : Blo 1849626 5927147 := bstep (se 1 (by rfl) ⟨4445360, by rfl⟩ : syracuseStep 5927147 = 8890721) B8890721
theorem B72093977 : Blo 1849626 72093977 := bstep (se 2 (by rfl) ⟨27035241, by rfl⟩ : syracuseStep 72093977 = 54070483) B54070483
theorem B4682711 : Blo 1849626 4682711 := bstep (se 1 (by rfl) ⟨3512033, by rfl⟩ : syracuseStep 4682711 = 7024067) B7024067
theorem B7902299 : Blo 1849626 7902299 := bstep (se 1 (by rfl) ⟨5926724, by rfl⟩ : syracuseStep 7902299 = 11853449) B11853449
theorem B4445275 : Blo 1849626 4445275 := bstep (se 1 (by rfl) ⟨3333956, by rfl⟩ : syracuseStep 4445275 = 6667913) B6667913
theorem B79164599 : Blo 1849626 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B9368783 : Blo 1849626 9368783 := bstep (se 1 (by rfl) ⟨7026587, by rfl⟩ : syracuseStep 9368783 = 14053175) B14053175
theorem B7026011 : Blo 1849626 7026011 := bstep (se 1 (by rfl) ⟨5269508, by rfl⟩ : syracuseStep 7026011 = 10539017) B10539017
theorem B2774441 : Blo 1849626 2774441 := bstep (se 2 (by rfl) ⟨1040415, by rfl⟩ : syracuseStep 2774441 = 2080831) B2080831
theorem B2774495 : Blo 1849626 2774495 := bstep (se 1 (by rfl) ⟨2080871, by rfl⟩ : syracuseStep 2774495 = 4161743) B4161743
theorem B17110547 : Blo 1849626 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B2373311 : Blo 1849626 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B14055119 : Blo 1849626 14055119 := bstep (se 1 (by rfl) ⟨10541339, by rfl⟩ : syracuseStep 14055119 = 21082679) B21082679
theorem B10540975 : Blo 1849626 10540975 := bstep (se 1 (by rfl) ⟨7905731, by rfl⟩ : syracuseStep 10540975 = 15811463) B15811463
theorem B4684027 : Blo 1849626 4684027 := bstep (se 1 (by rfl) ⟨3513020, by rfl⟩ : syracuseStep 4684027 = 7026041) B7026041
theorem B15809003 : Blo 1849626 15809003 := bstep (se 1 (by rfl) ⟨11856752, by rfl⟩ : syracuseStep 15809003 = 23713505) B23713505
theorem B18037289 : Blo 1849626 18037289 := bstep (se 2 (by rfl) ⟨6763983, by rfl⟩ : syracuseStep 18037289 = 13527967) B13527967
theorem B2775599 : Blo 1849626 2775599 := bstep (se 1 (by rfl) ⟨2081699, by rfl⟩ : syracuseStep 2775599 = 4163399) B4163399
theorem B3513127 : Blo 1849626 3513127 := bstep (se 1 (by rfl) ⟨2634845, by rfl⟩ : syracuseStep 3513127 = 5269691) B5269691
theorem B3513287 : Blo 1849626 3513287 := bstep (se 1 (by rfl) ⟨2634965, by rfl⟩ : syracuseStep 3513287 = 5269931) B5269931
theorem B2776007 : Blo 1849626 2776007 := bstep (se 1 (by rfl) ⟨2082005, by rfl⟩ : syracuseStep 2776007 = 4164011) B4164011
theorem B2776031 : Blo 1849626 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B80059373 : Blo 1849626 80059373 := bstep (se 3 (by rfl) ⟨15011132, by rfl⟩ : syracuseStep 80059373 = 30022265) B30022265
theorem B1850363 : Blo 1849626 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B1850783 : Blo 1849626 1850783 := bstep (se 1 (by rfl) ⟨1388087, by rfl⟩ : syracuseStep 1850783 = 2776175) B2776175
theorem B2776679 : Blo 1849626 2776679 := bstep (se 1 (by rfl) ⟨2082509, by rfl⟩ : syracuseStep 2776679 = 4165019) B4165019
theorem B1851039 : Blo 1849626 1851039 := bstep (se 1 (by rfl) ⟨1388279, by rfl⟩ : syracuseStep 1851039 = 2776559) B2776559
theorem B2776895 : Blo 1849626 2776895 := bstep (se 1 (by rfl) ⟨2082671, by rfl⟩ : syracuseStep 2776895 = 4165343) B4165343
theorem B4685759 : Blo 1849626 4685759 := bstep (se 1 (by rfl) ⟨3514319, by rfl⟩ : syracuseStep 4685759 = 7028639) B7028639
theorem B2777063 : Blo 1849626 2777063 := bstep (se 1 (by rfl) ⟨2082797, by rfl⟩ : syracuseStep 2777063 = 4165595) B4165595
theorem B4448351 : Blo 1849626 4448351 := bstep (se 1 (by rfl) ⟨3336263, by rfl⟩ : syracuseStep 4448351 = 6672527) B6672527
theorem B2777183 : Blo 1849626 2777183 := bstep (se 1 (by rfl) ⟨2082887, by rfl⟩ : syracuseStep 2777183 = 4165775) B4165775
theorem B48062651 : Blo 1849626 48062651 := bstep (se 1 (by rfl) ⟨36046988, by rfl⟩ : syracuseStep 48062651 = 72093977) B72093977
theorem B4161761 : Blo 1849626 4161761 := bstep (se 2 (by rfl) ⟨1560660, by rfl⟩ : syracuseStep 4161761 = 3121321) B3121321
theorem B8896871 : Blo 1849626 8896871 := bstep (se 1 (by rfl) ⟨6672653, by rfl⟩ : syracuseStep 8896871 = 13345307) B13345307
theorem B25313771 : Blo 1849626 25313771 := bstep (se 1 (by rfl) ⟨18985328, by rfl⟩ : syracuseStep 25313771 = 37970657) B37970657
theorem B3121807 : Blo 1849626 3121807 := bstep (se 1 (by rfl) ⟨2341355, by rfl⟩ : syracuseStep 3121807 = 4682711) B4682711
theorem B5268199 : Blo 1849626 5268199 := bstep (se 1 (by rfl) ⟨3951149, by rfl⟩ : syracuseStep 5268199 = 7902299) B7902299
theorem B3752687 : Blo 1849626 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B4686599 : Blo 1849626 4686599 := bstep (se 1 (by rfl) ⟨3514949, by rfl⟩ : syracuseStep 4686599 = 7029899) B7029899
theorem B6243155 : Blo 1849626 6243155 := bstep (se 1 (by rfl) ⟨4682366, by rfl⟩ : syracuseStep 6243155 = 9364733) B9364733
theorem B53372915 : Blo 1849626 53372915 := bstep (se 1 (by rfl) ⟨40029686, by rfl⟩ : syracuseStep 53372915 = 80059373) B80059373
theorem B9373805 : Blo 1849626 9373805 := bstep (se 3 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 9373805 = 3515177) B3515177
theorem B45009179 : Blo 1849626 45009179 := bstep (se 1 (by rfl) ⟨33756884, by rfl⟩ : syracuseStep 45009179 = 67513769) B67513769
theorem B21072473 : Blo 1849626 21072473 := bstep (se 2 (by rfl) ⟨7902177, by rfl⟩ : syracuseStep 21072473 = 15804355) B15804355
theorem B3123839 : Blo 1849626 3123839 := bstep (se 1 (by rfl) ⟨2342879, by rfl⟩ : syracuseStep 3123839 = 4685759) B4685759
theorem B3951431 : Blo 1849626 3951431 := bstep (se 1 (by rfl) ⟨2963573, by rfl⟩ : syracuseStep 3951431 = 5927147) B5927147
theorem B6245369 : Blo 1849626 6245369 := bstep (se 2 (by rfl) ⟨2342013, by rfl⟩ : syracuseStep 6245369 = 4684027) B4684027
theorem B7023611 : Blo 1849626 7023611 := bstep (se 1 (by rfl) ⟨5267708, by rfl⟩ : syracuseStep 7023611 = 10535417) B10535417
theorem B31632767 : Blo 1849626 31632767 := bstep (se 1 (by rfl) ⟨23724575, by rfl⟩ : syracuseStep 31632767 = 47449151) B47449151
theorem B6245855 : Blo 1849626 6245855 := bstep (se 1 (by rfl) ⟨4684391, by rfl⟩ : syracuseStep 6245855 = 9368783) B9368783
theorem B11407031 : Blo 1849626 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B7024583 : Blo 1849626 7024583 := bstep (se 1 (by rfl) ⟨5268437, by rfl⟩ : syracuseStep 7024583 = 10536875) B10536875
theorem B5926891 : Blo 1849626 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B4747319 : Blo 1849626 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B5927033 : Blo 1849626 5927033 := bstep (se 2 (by rfl) ⟨2222637, by rfl⟩ : syracuseStep 5927033 = 4445275) B4445275
theorem B8892719 : Blo 1849626 8892719 := bstep (se 1 (by rfl) ⟨6669539, by rfl⟩ : syracuseStep 8892719 = 13339079) B13339079
theorem B10539335 : Blo 1849626 10539335 := bstep (se 1 (by rfl) ⟨7904501, by rfl⟩ : syracuseStep 10539335 = 15809003) B15809003
theorem B6328829 : Blo 1849626 6328829 := bstep (se 3 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 6328829 = 2373311) B2373311
theorem B10007077 : Blo 1849626 10007077 := bstep (se 4 (by rfl) ⟨938163, by rfl⟩ : syracuseStep 10007077 = 1876327) B1876327
theorem B5272607 : Blo 1849626 5272607 := bstep (se 1 (by rfl) ⟨3954455, by rfl⟩ : syracuseStep 5272607 = 7908911) B7908911
theorem B14054633 : Blo 1849626 14054633 := bstep (se 2 (by rfl) ⟨5270487, by rfl⟩ : syracuseStep 14054633 = 10540975) B10540975
theorem B2774591 : Blo 1849626 2774591 := bstep (se 1 (by rfl) ⟨2080943, by rfl⟩ : syracuseStep 2774591 = 4161887) B4161887
theorem B2774687 : Blo 1849626 2774687 := bstep (se 1 (by rfl) ⟨2081015, by rfl⟩ : syracuseStep 2774687 = 4162031) B4162031
theorem B211105597 : Blo 1849626 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B2775035 : Blo 1849626 2775035 := bstep (se 1 (by rfl) ⟨2081276, by rfl⟩ : syracuseStep 2775035 = 4162553) B4162553
theorem B2775071 : Blo 1849626 2775071 := bstep (se 1 (by rfl) ⟨2081303, by rfl⟩ : syracuseStep 2775071 = 4162607) B4162607
theorem B1500756169 : Blo 1849626 1500756169 := bstep (se 2 (by rfl) ⟨562783563, by rfl⟩ : syracuseStep 1500756169 = 1125567127) B1125567127
theorem B4684007 : Blo 1849626 4684007 := bstep (se 1 (by rfl) ⟨3513005, by rfl⟩ : syracuseStep 4684007 = 7026011) B7026011
theorem B1849627 : Blo 1849626 1849627 := bstep (se 1 (by rfl) ⟨1387220, by rfl⟩ : syracuseStep 1849627 = 2774441) B2774441
theorem B1849663 : Blo 1849626 1849663 := bstep (se 1 (by rfl) ⟨1387247, by rfl⟩ : syracuseStep 1849663 = 2774495) B2774495
theorem B4684169 : Blo 1849626 4684169 := bstep (se 2 (by rfl) ⟨1756563, by rfl⟩ : syracuseStep 4684169 = 3513127) B3513127
theorem B9370079 : Blo 1849626 9370079 := bstep (se 1 (by rfl) ⟨7027559, by rfl⟩ : syracuseStep 9370079 = 14055119) B14055119
theorem B2775593 : Blo 1849626 2775593 := bstep (se 2 (by rfl) ⟨1040847, by rfl⟩ : syracuseStep 2775593 = 2081695) B2081695
theorem B80026157 : Blo 1849626 80026157 := bstep (se 3 (by rfl) ⟨15004904, by rfl⟩ : syracuseStep 80026157 = 30009809) B30009809
theorem B3611495 : Blo 1849626 3611495 := bstep (se 1 (by rfl) ⟨2708621, by rfl⟩ : syracuseStep 3611495 = 5417243) B5417243
theorem B2776091 : Blo 1849626 2776091 := bstep (se 1 (by rfl) ⟨2082068, by rfl⟩ : syracuseStep 2776091 = 4164137) B4164137
theorem B12024859 : Blo 1849626 12024859 := bstep (se 1 (by rfl) ⟨9018644, by rfl⟩ : syracuseStep 12024859 = 18037289) B18037289
theorem B1850399 : Blo 1849626 1850399 := bstep (se 1 (by rfl) ⟨1387799, by rfl⟩ : syracuseStep 1850399 = 2775599) B2775599
theorem B2776361 : Blo 1849626 2776361 := bstep (se 2 (by rfl) ⟨1041135, by rfl⟩ : syracuseStep 2776361 = 2082271) B2082271
theorem B2342191 : Blo 1849626 2342191 := bstep (se 1 (by rfl) ⟨1756643, by rfl⟩ : syracuseStep 2342191 = 3513287) B3513287
theorem B1850671 : Blo 1849626 1850671 := bstep (se 1 (by rfl) ⟨1388003, by rfl⟩ : syracuseStep 1850671 = 2776007) B2776007
theorem B2776367 : Blo 1849626 2776367 := bstep (se 1 (by rfl) ⟨2082275, by rfl⟩ : syracuseStep 2776367 = 4164551) B4164551
theorem B1850687 : Blo 1849626 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B2776475 : Blo 1849626 2776475 := bstep (se 1 (by rfl) ⟨2082356, by rfl⟩ : syracuseStep 2776475 = 4164713) B4164713
theorem B15801965 : Blo 1849626 15801965 := bstep (se 3 (by rfl) ⟨2962868, by rfl⟩ : syracuseStep 15801965 = 5925737) B5925737
theorem B5930621 : Blo 1849626 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B1851119 : Blo 1849626 1851119 := bstep (se 1 (by rfl) ⟨1388339, by rfl⟩ : syracuseStep 1851119 = 2776679) B2776679
theorem B2776859 : Blo 1849626 2776859 := bstep (se 1 (by rfl) ⟨2082644, by rfl⟩ : syracuseStep 2776859 = 4165289) B4165289
theorem B1851263 : Blo 1849626 1851263 := bstep (se 1 (by rfl) ⟨1388447, by rfl⟩ : syracuseStep 1851263 = 2776895) B2776895
theorem B2776991 : Blo 1849626 2776991 := bstep (se 1 (by rfl) ⟨2082743, by rfl⟩ : syracuseStep 2776991 = 4165487) B4165487
theorem B1851375 : Blo 1849626 1851375 := bstep (se 1 (by rfl) ⟨1388531, by rfl⟩ : syracuseStep 1851375 = 2777063) B2777063
theorem B2965567 : Blo 1849626 2965567 := bstep (se 1 (by rfl) ⟨2224175, by rfl⟩ : syracuseStep 2965567 = 4448351) B4448351
theorem B1851455 : Blo 1849626 1851455 := bstep (se 1 (by rfl) ⟨1388591, by rfl⟩ : syracuseStep 1851455 = 2777183) B2777183
theorem B5931247 : Blo 1849626 5931247 := bstep (se 1 (by rfl) ⟨4448435, by rfl⟩ : syracuseStep 5931247 = 8896871) B8896871
theorem B16875847 : Blo 1849626 16875847 := bstep (se 1 (by rfl) ⟨12656885, by rfl⟩ : syracuseStep 16875847 = 25313771) B25313771
theorem B4219219 : Blo 1849626 4219219 := bstep (se 1 (by rfl) ⟨3164414, by rfl⟩ : syracuseStep 4219219 = 6328829) B6328829
theorem B4162103 : Blo 1849626 4162103 := bstep (se 1 (by rfl) ⟨3121577, by rfl⟩ : syracuseStep 4162103 = 6243155) B6243155
theorem B3515071 : Blo 1849626 3515071 := bstep (se 1 (by rfl) ⟨2636303, by rfl⟩ : syracuseStep 3515071 = 5272607) B5272607
theorem B4162409 : Blo 1849626 4162409 := bstep (se 2 (by rfl) ⟨1560903, by rfl⟩ : syracuseStep 4162409 = 3121807) B3121807
theorem B16033145 : Blo 1849626 16033145 := bstep (se 2 (by rfl) ⟨6012429, by rfl⟩ : syracuseStep 16033145 = 12024859) B12024859
theorem B3122671 : Blo 1849626 3122671 := bstep (se 1 (by rfl) ⟨2342003, by rfl⟩ : syracuseStep 3122671 = 4684007) B4684007
theorem B3122779 : Blo 1849626 3122779 := bstep (se 1 (by rfl) ⟨2342084, by rfl⟩ : syracuseStep 3122779 = 4684169) B4684169
theorem B3122921 : Blo 1849626 3122921 := bstep (se 2 (by rfl) ⟨1171095, by rfl⟩ : syracuseStep 3122921 = 2342191) B2342191
theorem B2082559 : Blo 1849626 2082559 := bstep (se 1 (by rfl) ⟨1561919, by rfl⟩ : syracuseStep 2082559 = 3123839) B3123839
theorem B4163579 : Blo 1849626 4163579 := bstep (se 1 (by rfl) ⟨3122684, by rfl⟩ : syracuseStep 4163579 = 6245369) B6245369
theorem B21088511 : Blo 1849626 21088511 := bstep (se 1 (by rfl) ⟨15816383, by rfl⟩ : syracuseStep 21088511 = 31632767) B31632767
theorem B4163903 : Blo 1849626 4163903 := bstep (se 1 (by rfl) ⟨3122927, by rfl⟩ : syracuseStep 4163903 = 6245855) B6245855
theorem B7604687 : Blo 1849626 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B3164879 : Blo 1849626 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B3951355 : Blo 1849626 3951355 := bstep (se 1 (by rfl) ⟨2963516, by rfl⟩ : syracuseStep 3951355 = 5927033) B5927033
theorem B128167069 : Blo 1849626 128167069 := bstep (se 3 (by rfl) ⟨24031325, by rfl⟩ : syracuseStep 128167069 = 48062651) B48062651
theorem B3124399 : Blo 1849626 3124399 := bstep (se 1 (by rfl) ⟨2343299, by rfl⟩ : syracuseStep 3124399 = 4686599) B4686599
theorem B7024265 : Blo 1849626 7024265 := bstep (se 2 (by rfl) ⟨2634099, by rfl⟩ : syracuseStep 7024265 = 5268199) B5268199
theorem B35581943 : Blo 1849626 35581943 := bstep (se 1 (by rfl) ⟨26686457, by rfl⟩ : syracuseStep 35581943 = 53372915) B53372915
theorem B6246719 : Blo 1849626 6246719 := bstep (se 1 (by rfl) ⟨4685039, by rfl⟩ : syracuseStep 6246719 = 9370079) B9370079
theorem B53350771 : Blo 1849626 53350771 := bstep (se 1 (by rfl) ⟨40013078, by rfl⟩ : syracuseStep 53350771 = 80026157) B80026157
theorem B2634287 : Blo 1849626 2634287 := bstep (se 1 (by rfl) ⟨1975715, by rfl⟩ : syracuseStep 2634287 = 3951431) B3951431
theorem B10007165 : Blo 1849626 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B4682407 : Blo 1849626 4682407 := bstep (se 1 (by rfl) ⟨3511805, by rfl⟩ : syracuseStep 4682407 = 7023611) B7023611
theorem B281474129 : Blo 1849626 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B3953747 : Blo 1849626 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B4683055 : Blo 1849626 4683055 := bstep (se 1 (by rfl) ⟨3512291, by rfl⟩ : syracuseStep 4683055 = 7024583) B7024583
theorem B7902521 : Blo 1849626 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B2774507 : Blo 1849626 2774507 := bstep (se 1 (by rfl) ⟨2080880, by rfl⟩ : syracuseStep 2774507 = 4161761) B4161761
theorem B5928479 : Blo 1849626 5928479 := bstep (se 1 (by rfl) ⟨4446359, by rfl⟩ : syracuseStep 5928479 = 8892719) B8892719
theorem B7026223 : Blo 1849626 7026223 := bstep (se 1 (by rfl) ⟨5269667, by rfl⟩ : syracuseStep 7026223 = 10539335) B10539335
theorem B2001008225 : Blo 1849626 2001008225 := bstep (se 2 (by rfl) ⟨750378084, by rfl⟩ : syracuseStep 2001008225 = 1500756169) B1500756169
theorem B13342769 : Blo 1849626 13342769 := bstep (se 2 (by rfl) ⟨5003538, by rfl⟩ : syracuseStep 13342769 = 10007077) B10007077
theorem B9369755 : Blo 1849626 9369755 := bstep (se 1 (by rfl) ⟨7027316, by rfl⟩ : syracuseStep 9369755 = 14054633) B14054633
theorem B1849727 : Blo 1849626 1849727 := bstep (se 1 (by rfl) ⟨1387295, by rfl⟩ : syracuseStep 1849727 = 2774591) B2774591
theorem B1849791 : Blo 1849626 1849791 := bstep (se 1 (by rfl) ⟨1387343, by rfl⟩ : syracuseStep 1849791 = 2774687) B2774687
theorem B1850023 : Blo 1849626 1850023 := bstep (se 1 (by rfl) ⟨1387517, by rfl⟩ : syracuseStep 1850023 = 2775035) B2775035
theorem B1850047 : Blo 1849626 1850047 := bstep (se 1 (by rfl) ⟨1387535, by rfl⟩ : syracuseStep 1850047 = 2775071) B2775071
theorem B6249203 : Blo 1849626 6249203 := bstep (se 1 (by rfl) ⟨4686902, by rfl⟩ : syracuseStep 6249203 = 9373805) B9373805
theorem B30006119 : Blo 1849626 30006119 := bstep (se 1 (by rfl) ⟨22504589, by rfl⟩ : syracuseStep 30006119 = 45009179) B45009179
theorem B1850395 : Blo 1849626 1850395 := bstep (se 1 (by rfl) ⟨1387796, by rfl⟩ : syracuseStep 1850395 = 2775593) B2775593
theorem B14048315 : Blo 1849626 14048315 := bstep (se 1 (by rfl) ⟨10536236, by rfl⟩ : syracuseStep 14048315 = 21072473) B21072473
theorem B2407663 : Blo 1849626 2407663 := bstep (se 1 (by rfl) ⟨1805747, by rfl⟩ : syracuseStep 2407663 = 3611495) B3611495
theorem B1850727 : Blo 1849626 1850727 := bstep (se 1 (by rfl) ⟨1388045, by rfl⟩ : syracuseStep 1850727 = 2776091) B2776091
theorem B1850907 : Blo 1849626 1850907 := bstep (se 1 (by rfl) ⟨1388180, by rfl⟩ : syracuseStep 1850907 = 2776361) B2776361
theorem B1850911 : Blo 1849626 1850911 := bstep (se 1 (by rfl) ⟨1388183, by rfl⟩ : syracuseStep 1850911 = 2776367) B2776367
theorem B1850983 : Blo 1849626 1850983 := bstep (se 1 (by rfl) ⟨1388237, by rfl⟩ : syracuseStep 1850983 = 2776475) B2776475
theorem B10534643 : Blo 1849626 10534643 := bstep (se 1 (by rfl) ⟨7900982, by rfl⟩ : syracuseStep 10534643 = 15801965) B15801965
theorem B1851239 : Blo 1849626 1851239 := bstep (se 1 (by rfl) ⟨1388429, by rfl⟩ : syracuseStep 1851239 = 2776859) B2776859
theorem B1851327 : Blo 1849626 1851327 := bstep (se 1 (by rfl) ⟨1388495, by rfl⟩ : syracuseStep 1851327 = 2776991) B2776991
theorem B5268347 : Blo 1849626 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B6243209 : Blo 1849626 6243209 := bstep (se 2 (by rfl) ⟨2341203, by rfl⟩ : syracuseStep 6243209 = 4682407) B4682407
theorem B4686761 : Blo 1849626 4686761 := bstep (se 2 (by rfl) ⟨1757535, by rfl⟩ : syracuseStep 4686761 = 3515071) B3515071
theorem B42755053 : Blo 1849626 42755053 := bstep (se 3 (by rfl) ⟨8016572, by rfl⟩ : syracuseStep 42755053 = 16033145) B16033145
theorem B5268473 : Blo 1849626 5268473 := bstep (se 2 (by rfl) ⟨1975677, by rfl⟩ : syracuseStep 5268473 = 3951355) B3951355
theorem B2081947 : Blo 1849626 2081947 := bstep (se 1 (by rfl) ⟨1561460, by rfl⟩ : syracuseStep 2081947 = 3122921) B3122921
theorem B14059007 : Blo 1849626 14059007 := bstep (se 1 (by rfl) ⟨10544255, by rfl⟩ : syracuseStep 14059007 = 21088511) B21088511
theorem B6244073 : Blo 1849626 6244073 := bstep (se 2 (by rfl) ⟨2341527, by rfl⟩ : syracuseStep 6244073 = 4683055) B4683055
theorem B8439677 : Blo 1849626 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B4163561 : Blo 1849626 4163561 := bstep (se 2 (by rfl) ⟨1561335, by rfl⟩ : syracuseStep 4163561 = 3122671) B3122671
theorem B9365543 : Blo 1849626 9365543 := bstep (se 1 (by rfl) ⟨7024157, by rfl⟩ : syracuseStep 9365543 = 14048315) B14048315
theorem B4163705 : Blo 1849626 4163705 := bstep (se 2 (by rfl) ⟨1561389, by rfl⟩ : syracuseStep 4163705 = 3122779) B3122779
theorem B7023095 : Blo 1849626 7023095 := bstep (se 1 (by rfl) ⟨5267321, by rfl⟩ : syracuseStep 7023095 = 10534643) B10534643
theorem B4164479 : Blo 1849626 4164479 := bstep (se 1 (by rfl) ⟨3123359, by rfl⟩ : syracuseStep 4164479 = 6246719) B6246719
theorem B7908329 : Blo 1849626 7908329 := bstep (se 2 (by rfl) ⟨2965623, by rfl⟩ : syracuseStep 7908329 = 5931247) B5931247
theorem B71134361 : Blo 1849626 71134361 := bstep (se 2 (by rfl) ⟨26675385, by rfl⟩ : syracuseStep 71134361 = 53350771) B53350771
theorem B187649419 : Blo 1849626 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B3952319 : Blo 1849626 3952319 := bstep (se 1 (by rfl) ⟨2964239, by rfl⟩ : syracuseStep 3952319 = 5928479) B5928479
theorem B1334005483 : Blo 1849626 1334005483 := bstep (se 1 (by rfl) ⟨1000504112, by rfl⟩ : syracuseStep 1334005483 = 2001008225) B2001008225
theorem B12840869 : Blo 1849626 12840869 := bstep (se 4 (by rfl) ⟨1203831, by rfl⟩ : syracuseStep 12840869 = 2407663) B2407663
theorem B6246503 : Blo 1849626 6246503 := bstep (se 1 (by rfl) ⟨4684877, by rfl⟩ : syracuseStep 6246503 = 9369755) B9369755
theorem B7024765 : Blo 1849626 7024765 := bstep (se 3 (by rfl) ⟨1317143, by rfl⟩ : syracuseStep 7024765 = 2634287) B2634287
theorem B170889425 : Blo 1849626 170889425 := bstep (se 2 (by rfl) ⟨64083534, by rfl⟩ : syracuseStep 170889425 = 128167069) B128167069
theorem B4165865 : Blo 1849626 4165865 := bstep (se 2 (by rfl) ⟨1562199, by rfl⟩ : syracuseStep 4165865 = 3124399) B3124399
theorem B26685773 : Blo 1849626 26685773 := bstep (se 3 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 26685773 = 10007165) B10007165
theorem B4166135 : Blo 1849626 4166135 := bstep (se 1 (by rfl) ⟨3124601, by rfl⟩ : syracuseStep 4166135 = 6249203) B6249203
theorem B9368297 : Blo 1849626 9368297 := bstep (se 2 (by rfl) ⟨3513111, by rfl⟩ : syracuseStep 9368297 = 7026223) B7026223
theorem B4682843 : Blo 1849626 4682843 := bstep (se 1 (by rfl) ⟨3512132, by rfl⟩ : syracuseStep 4682843 = 7024265) B7024265
theorem B23721295 : Blo 1849626 23721295 := bstep (se 1 (by rfl) ⟨17790971, by rfl⟩ : syracuseStep 23721295 = 35581943) B35581943
theorem B3954089 : Blo 1849626 3954089 := bstep (se 2 (by rfl) ⟨1482783, by rfl⟩ : syracuseStep 3954089 = 2965567) B2965567
theorem B2774735 : Blo 1849626 2774735 := bstep (se 1 (by rfl) ⟨2081051, by rfl⟩ : syracuseStep 2774735 = 4162103) B4162103
theorem B5625625 : Blo 1849626 5625625 := bstep (se 2 (by rfl) ⟨2109609, by rfl⟩ : syracuseStep 5625625 = 4219219) B4219219
theorem B2774939 : Blo 1849626 2774939 := bstep (se 1 (by rfl) ⟨2081204, by rfl⟩ : syracuseStep 2774939 = 4162409) B4162409
theorem B2635831 : Blo 1849626 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B1849671 : Blo 1849626 1849671 := bstep (se 1 (by rfl) ⟨1387253, by rfl⟩ : syracuseStep 1849671 = 2774507) B2774507
theorem B2775719 : Blo 1849626 2775719 := bstep (se 1 (by rfl) ⟨2081789, by rfl⟩ : syracuseStep 2775719 = 4163579) B4163579
theorem B8895179 : Blo 1849626 8895179 := bstep (se 1 (by rfl) ⟨6671384, by rfl⟩ : syracuseStep 8895179 = 13342769) B13342769
theorem B2775935 : Blo 1849626 2775935 := bstep (se 1 (by rfl) ⟨2081951, by rfl⟩ : syracuseStep 2775935 = 4163903) B4163903
theorem B5069791 : Blo 1849626 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B90004517 : Blo 1849626 90004517 := bstep (se 4 (by rfl) ⟨8437923, by rfl⟩ : syracuseStep 90004517 = 16875847) B16875847
theorem B20004079 : Blo 1849626 20004079 := bstep (se 1 (by rfl) ⟨15003059, by rfl⟩ : syracuseStep 20004079 = 30006119) B30006119
theorem B2776745 : Blo 1849626 2776745 := bstep (se 2 (by rfl) ⟨1041279, by rfl⟩ : syracuseStep 2776745 = 2082559) B2082559
theorem B3514441 : Blo 1849626 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B113926283 : Blo 1849626 113926283 := bstep (se 1 (by rfl) ⟨85444712, by rfl⟩ : syracuseStep 113926283 = 170889425) B170889425
theorem B2777243 : Blo 1849626 2777243 := bstep (se 1 (by rfl) ⟨2082932, by rfl⟩ : syracuseStep 2777243 = 4165865) B4165865
theorem B2777423 : Blo 1849626 2777423 := bstep (se 1 (by rfl) ⟨2083067, by rfl⟩ : syracuseStep 2777423 = 4166135) B4166135
theorem B4162139 : Blo 1849626 4162139 := bstep (se 1 (by rfl) ⟨3121604, by rfl⟩ : syracuseStep 4162139 = 6243209) B6243209
theorem B3121895 : Blo 1849626 3121895 := bstep (se 1 (by rfl) ⟨2341421, by rfl⟩ : syracuseStep 3121895 = 4682843) B4682843
theorem B9372671 : Blo 1849626 9372671 := bstep (se 1 (by rfl) ⟨7029503, by rfl⟩ : syracuseStep 9372671 = 14059007) B14059007
theorem B4162715 : Blo 1849626 4162715 := bstep (se 1 (by rfl) ⟨3122036, by rfl⟩ : syracuseStep 4162715 = 6244073) B6244073
theorem B6759721 : Blo 1849626 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B6243695 : Blo 1849626 6243695 := bstep (se 1 (by rfl) ⟨4682771, by rfl⟩ : syracuseStep 6243695 = 9365543) B9365543
theorem B1778673977 : Blo 1849626 1778673977 := bstep (se 2 (by rfl) ⟨667002741, by rfl⟩ : syracuseStep 1778673977 = 1334005483) B1334005483
theorem B4164335 : Blo 1849626 4164335 := bstep (se 1 (by rfl) ⟨3123251, by rfl⟩ : syracuseStep 4164335 = 6246503) B6246503
theorem B9366353 : Blo 1849626 9366353 := bstep (se 2 (by rfl) ⟨3512382, by rfl⟩ : syracuseStep 9366353 = 7024765) B7024765
theorem B6245531 : Blo 1849626 6245531 := bstep (se 1 (by rfl) ⟨4684148, by rfl⟩ : syracuseStep 6245531 = 9368297) B9368297
theorem B3124507 : Blo 1849626 3124507 := bstep (se 1 (by rfl) ⟨2343380, by rfl⟩ : syracuseStep 3124507 = 4686761) B4686761
theorem B4682063 : Blo 1849626 4682063 := bstep (se 1 (by rfl) ⟨3511547, by rfl⟩ : syracuseStep 4682063 = 7023095) B7023095
theorem B10539517 : Blo 1849626 10539517 := bstep (se 3 (by rfl) ⟨1976159, by rfl⟩ : syracuseStep 10539517 = 3952319) B3952319
theorem B5272219 : Blo 1849626 5272219 := bstep (se 1 (by rfl) ⟨3954164, by rfl⟩ : syracuseStep 5272219 = 7908329) B7908329
theorem B60003011 : Blo 1849626 60003011 := bstep (se 1 (by rfl) ⟨45002258, by rfl⟩ : syracuseStep 60003011 = 90004517) B90004517
theorem B7500833 : Blo 1849626 7500833 := bstep (se 2 (by rfl) ⟨2812812, by rfl⟩ : syracuseStep 7500833 = 5625625) B5625625
theorem B17790515 : Blo 1849626 17790515 := bstep (se 1 (by rfl) ⟨13342886, by rfl⟩ : syracuseStep 17790515 = 26685773) B26685773
theorem B3512231 : Blo 1849626 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B3512315 : Blo 1849626 3512315 := bstep (se 1 (by rfl) ⟨2634236, by rfl⟩ : syracuseStep 3512315 = 5268473) B5268473
theorem B2636059 : Blo 1849626 2636059 := bstep (se 1 (by rfl) ⟨1977044, by rfl⟩ : syracuseStep 2636059 = 3954089) B3954089
theorem B1849823 : Blo 1849626 1849823 := bstep (se 1 (by rfl) ⟨1387367, by rfl⟩ : syracuseStep 1849823 = 2774735) B2774735
theorem B5626451 : Blo 1849626 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B1849959 : Blo 1849626 1849959 := bstep (se 1 (by rfl) ⟨1387469, by rfl⟩ : syracuseStep 1849959 = 2774939) B2774939
theorem B57006737 : Blo 1849626 57006737 := bstep (se 2 (by rfl) ⟨21377526, by rfl⟩ : syracuseStep 57006737 = 42755053) B42755053
theorem B2775707 : Blo 1849626 2775707 := bstep (se 1 (by rfl) ⟨2081780, by rfl⟩ : syracuseStep 2775707 = 4163561) B4163561
theorem B2775803 : Blo 1849626 2775803 := bstep (se 1 (by rfl) ⟨2081852, by rfl⟩ : syracuseStep 2775803 = 4163705) B4163705
theorem B2775929 : Blo 1849626 2775929 := bstep (se 2 (by rfl) ⟨1040973, by rfl⟩ : syracuseStep 2775929 = 2081947) B2081947
theorem B26672105 : Blo 1849626 26672105 := bstep (se 2 (by rfl) ⟨10002039, by rfl⟩ : syracuseStep 26672105 = 20004079) B20004079
theorem B31628393 : Blo 1849626 31628393 := bstep (se 2 (by rfl) ⟨11860647, by rfl⟩ : syracuseStep 31628393 = 23721295) B23721295
theorem B1850479 : Blo 1849626 1850479 := bstep (se 1 (by rfl) ⟨1387859, by rfl⟩ : syracuseStep 1850479 = 2775719) B2775719
theorem B5930119 : Blo 1849626 5930119 := bstep (se 1 (by rfl) ⟨4447589, by rfl⟩ : syracuseStep 5930119 = 8895179) B8895179
theorem B250199225 : Blo 1849626 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B1850623 : Blo 1849626 1850623 := bstep (se 1 (by rfl) ⟨1387967, by rfl⟩ : syracuseStep 1850623 = 2775935) B2775935
theorem B2776319 : Blo 1849626 2776319 := bstep (se 1 (by rfl) ⟨2082239, by rfl⟩ : syracuseStep 2776319 = 4164479) B4164479
theorem B47422907 : Blo 1849626 47422907 := bstep (se 1 (by rfl) ⟨35567180, by rfl⟩ : syracuseStep 47422907 = 71134361) B71134361
theorem B1851163 : Blo 1849626 1851163 := bstep (se 1 (by rfl) ⟨1388372, by rfl⟩ : syracuseStep 1851163 = 2776745) B2776745
theorem B8560579 : Blo 1849626 8560579 := bstep (se 1 (by rfl) ⟨6420434, by rfl⟩ : syracuseStep 8560579 = 12840869) B12840869
theorem B4685921 : Blo 1849626 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B1851495 : Blo 1849626 1851495 := bstep (se 1 (by rfl) ⟨1388621, by rfl⟩ : syracuseStep 1851495 = 2777243) B2777243
theorem B3121375 : Blo 1849626 3121375 := bstep (se 1 (by rfl) ⟨2341031, by rfl⟩ : syracuseStep 3121375 = 4682063) B4682063
theorem B1851615 : Blo 1849626 1851615 := bstep (se 1 (by rfl) ⟨1388711, by rfl⟩ : syracuseStep 1851615 = 2777423) B2777423
theorem B3514745 : Blo 1849626 3514745 := bstep (se 2 (by rfl) ⟨1318029, by rfl⟩ : syracuseStep 3514745 = 2636059) B2636059
theorem B40002007 : Blo 1849626 40002007 := bstep (se 1 (by rfl) ⟨30001505, by rfl⟩ : syracuseStep 40002007 = 60003011) B60003011
theorem B2081263 : Blo 1849626 2081263 := bstep (se 1 (by rfl) ⟨1560947, by rfl⟩ : syracuseStep 2081263 = 3121895) B3121895
theorem B7029625 : Blo 1849626 7029625 := bstep (se 2 (by rfl) ⟨2636109, by rfl⟩ : syracuseStep 7029625 = 5272219) B5272219
theorem B4162463 : Blo 1849626 4162463 := bstep (se 1 (by rfl) ⟨3121847, by rfl⟩ : syracuseStep 4162463 = 6243695) B6243695
theorem B7906825 : Blo 1849626 7906825 := bstep (se 2 (by rfl) ⟨2965059, by rfl⟩ : syracuseStep 7906825 = 5930119) B5930119
theorem B9012961 : Blo 1849626 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B38004491 : Blo 1849626 38004491 := bstep (se 1 (by rfl) ⟨28503368, by rfl⟩ : syracuseStep 38004491 = 57006737) B57006737
theorem B6244235 : Blo 1849626 6244235 := bstep (se 1 (by rfl) ⟨4683176, by rfl⟩ : syracuseStep 6244235 = 9366353) B9366353
theorem B4163687 : Blo 1849626 4163687 := bstep (se 1 (by rfl) ⟨3122765, by rfl⟩ : syracuseStep 4163687 = 6245531) B6245531
theorem B166799483 : Blo 1849626 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B31615271 : Blo 1849626 31615271 := bstep (se 1 (by rfl) ⟨23711453, by rfl⟩ : syracuseStep 31615271 = 47422907) B47422907
theorem B11414105 : Blo 1849626 11414105 := bstep (se 2 (by rfl) ⟨4280289, by rfl⟩ : syracuseStep 11414105 = 8560579) B8560579
theorem B75950855 : Blo 1849626 75950855 := bstep (se 1 (by rfl) ⟨56963141, by rfl⟩ : syracuseStep 75950855 = 113926283) B113926283
theorem B14052689 : Blo 1849626 14052689 := bstep (se 2 (by rfl) ⟨5269758, by rfl⟩ : syracuseStep 14052689 = 10539517) B10539517
theorem B5000555 : Blo 1849626 5000555 := bstep (se 1 (by rfl) ⟨3750416, by rfl⟩ : syracuseStep 5000555 = 7500833) B7500833
theorem B4166009 : Blo 1849626 4166009 := bstep (se 2 (by rfl) ⟨1562253, by rfl⟩ : syracuseStep 4166009 = 3124507) B3124507
theorem B17781403 : Blo 1849626 17781403 := bstep (se 1 (by rfl) ⟨13336052, by rfl⟩ : syracuseStep 17781403 = 26672105) B26672105
theorem B2774759 : Blo 1849626 2774759 := bstep (se 1 (by rfl) ⟨2081069, by rfl⟩ : syracuseStep 2774759 = 4162139) B4162139
theorem B6248447 : Blo 1849626 6248447 := bstep (se 1 (by rfl) ⟨4686335, by rfl⟩ : syracuseStep 6248447 = 9372671) B9372671
theorem B2775143 : Blo 1849626 2775143 := bstep (se 1 (by rfl) ⟨2081357, by rfl⟩ : syracuseStep 2775143 = 4162715) B4162715
theorem B11860343 : Blo 1849626 11860343 := bstep (se 1 (by rfl) ⟨8895257, by rfl⟩ : syracuseStep 11860343 = 17790515) B17790515
theorem B2341487 : Blo 1849626 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B2341543 : Blo 1849626 2341543 := bstep (se 1 (by rfl) ⟨1756157, by rfl⟩ : syracuseStep 2341543 = 3512315) B3512315
theorem B1185782651 : Blo 1849626 1185782651 := bstep (se 1 (by rfl) ⟨889336988, by rfl⟩ : syracuseStep 1185782651 = 1778673977) B1778673977
theorem B3750967 : Blo 1849626 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B1850471 : Blo 1849626 1850471 := bstep (se 1 (by rfl) ⟨1387853, by rfl⟩ : syracuseStep 1850471 = 2775707) B2775707
theorem B2776223 : Blo 1849626 2776223 := bstep (se 1 (by rfl) ⟨2082167, by rfl⟩ : syracuseStep 2776223 = 4164335) B4164335
theorem B1850535 : Blo 1849626 1850535 := bstep (se 1 (by rfl) ⟨1387901, by rfl⟩ : syracuseStep 1850535 = 2775803) B2775803
theorem B1850619 : Blo 1849626 1850619 := bstep (se 1 (by rfl) ⟨1387964, by rfl⟩ : syracuseStep 1850619 = 2775929) B2775929
theorem B21085595 : Blo 1849626 21085595 := bstep (se 1 (by rfl) ⟨15814196, by rfl⟩ : syracuseStep 21085595 = 31628393) B31628393
theorem B1850879 : Blo 1849626 1850879 := bstep (se 1 (by rfl) ⟨1388159, by rfl⟩ : syracuseStep 1850879 = 2776319) B2776319
theorem B2343163 : Blo 1849626 2343163 := bstep (se 1 (by rfl) ⟨1757372, by rfl⟩ : syracuseStep 2343163 = 3514745) B3514745
theorem B2777339 : Blo 1849626 2777339 := bstep (se 1 (by rfl) ⟨2083004, by rfl⟩ : syracuseStep 2777339 = 4166009) B4166009
theorem B20005157 : Blo 1849626 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B4161833 : Blo 1849626 4161833 := bstep (se 2 (by rfl) ⟨1560687, by rfl⟩ : syracuseStep 4161833 = 3121375) B3121375
theorem B23708537 : Blo 1849626 23708537 := bstep (se 2 (by rfl) ⟨8890701, by rfl⟩ : syracuseStep 23708537 = 17781403) B17781403
theorem B3122057 : Blo 1849626 3122057 := bstep (se 2 (by rfl) ⟨1170771, by rfl⟩ : syracuseStep 3122057 = 2341543) B2341543
theorem B9372833 : Blo 1849626 9372833 := bstep (se 2 (by rfl) ⟨3514812, by rfl⟩ : syracuseStep 9372833 = 7029625) B7029625
theorem B4162823 : Blo 1849626 4162823 := bstep (se 1 (by rfl) ⟨3122117, by rfl⟩ : syracuseStep 4162823 = 6244235) B6244235
theorem B111199655 : Blo 1849626 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B7906895 : Blo 1849626 7906895 := bstep (se 1 (by rfl) ⟨5930171, by rfl⟩ : syracuseStep 7906895 = 11860343) B11860343
theorem B6243965 : Blo 1849626 6243965 := bstep (se 3 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 6243965 = 2341487) B2341487
theorem B790521767 : Blo 1849626 790521767 := bstep (se 1 (by rfl) ⟨592891325, by rfl⟩ : syracuseStep 790521767 = 1185782651) B1185782651
theorem B3123947 : Blo 1849626 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B4165631 : Blo 1849626 4165631 := bstep (se 1 (by rfl) ⟨3124223, by rfl⟩ : syracuseStep 4165631 = 6248447) B6248447
theorem B9368459 : Blo 1849626 9368459 := bstep (se 1 (by rfl) ⟨7026344, by rfl⟩ : syracuseStep 9368459 = 14052689) B14052689
theorem B2774975 : Blo 1849626 2774975 := bstep (se 1 (by rfl) ⟨2081231, by rfl⟩ : syracuseStep 2774975 = 4162463) B4162463
theorem B53336009 : Blo 1849626 53336009 := bstep (se 2 (by rfl) ⟨20001003, by rfl⟩ : syracuseStep 53336009 = 40002007) B40002007
theorem B2775017 : Blo 1849626 2775017 := bstep (se 2 (by rfl) ⟨1040631, by rfl⟩ : syracuseStep 2775017 = 2081263) B2081263
theorem B13334813 : Blo 1849626 13334813 := bstep (se 3 (by rfl) ⟨2500277, by rfl⟩ : syracuseStep 13334813 = 5000555) B5000555
theorem B1849839 : Blo 1849626 1849839 := bstep (se 1 (by rfl) ⟨1387379, by rfl⟩ : syracuseStep 1849839 = 2774759) B2774759
theorem B25336327 : Blo 1849626 25336327 := bstep (se 1 (by rfl) ⟨19002245, by rfl⟩ : syracuseStep 25336327 = 38004491) B38004491
theorem B1850095 : Blo 1849626 1850095 := bstep (se 1 (by rfl) ⟨1387571, by rfl⟩ : syracuseStep 1850095 = 2775143) B2775143
theorem B2775791 : Blo 1849626 2775791 := bstep (se 1 (by rfl) ⟨2081843, by rfl⟩ : syracuseStep 2775791 = 4163687) B4163687
theorem B21076847 : Blo 1849626 21076847 := bstep (se 1 (by rfl) ⟨15807635, by rfl⟩ : syracuseStep 21076847 = 31615271) B31615271
theorem B7609403 : Blo 1849626 7609403 := bstep (se 1 (by rfl) ⟨5707052, by rfl⟩ : syracuseStep 7609403 = 11414105) B11414105
theorem B50633903 : Blo 1849626 50633903 := bstep (se 1 (by rfl) ⟨37975427, by rfl⟩ : syracuseStep 50633903 = 75950855) B75950855
theorem B10542433 : Blo 1849626 10542433 := bstep (se 2 (by rfl) ⟨3953412, by rfl⟩ : syracuseStep 10542433 = 7906825) B7906825
theorem B1850815 : Blo 1849626 1850815 := bstep (se 1 (by rfl) ⟨1388111, by rfl⟩ : syracuseStep 1850815 = 2776223) B2776223
theorem B14057063 : Blo 1849626 14057063 := bstep (se 1 (by rfl) ⟨10542797, by rfl⟩ : syracuseStep 14057063 = 21085595) B21085595
theorem B12017281 : Blo 1849626 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B1851559 : Blo 1849626 1851559 := bstep (se 1 (by rfl) ⟨1388669, by rfl⟩ : syracuseStep 1851559 = 2777339) B2777339
theorem B13336771 : Blo 1849626 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B2081371 : Blo 1849626 2081371 := bstep (se 1 (by rfl) ⟨1561028, by rfl⟩ : syracuseStep 2081371 = 3122057) B3122057
theorem B4162643 : Blo 1849626 4162643 := bstep (se 1 (by rfl) ⟨3121982, by rfl⟩ : syracuseStep 4162643 = 6243965) B6243965
theorem B8889875 : Blo 1849626 8889875 := bstep (se 1 (by rfl) ⟨6667406, by rfl⟩ : syracuseStep 8889875 = 13334813) B13334813
theorem B2082631 : Blo 1849626 2082631 := bstep (se 1 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 2082631 = 3123947) B3123947
theorem B14051231 : Blo 1849626 14051231 := bstep (se 1 (by rfl) ⟨10538423, by rfl⟩ : syracuseStep 14051231 = 21076847) B21076847
theorem B5072935 : Blo 1849626 5072935 := bstep (se 1 (by rfl) ⟨3804701, by rfl⟩ : syracuseStep 5072935 = 7609403) B7609403
theorem B3124217 : Blo 1849626 3124217 := bstep (se 2 (by rfl) ⟨1171581, by rfl⟩ : syracuseStep 3124217 = 2343163) B2343163
theorem B15805691 : Blo 1849626 15805691 := bstep (se 1 (by rfl) ⟨11854268, by rfl⟩ : syracuseStep 15805691 = 23708537) B23708537
theorem B6245639 : Blo 1849626 6245639 := bstep (se 1 (by rfl) ⟨4684229, by rfl⟩ : syracuseStep 6245639 = 9368459) B9368459
theorem B5271263 : Blo 1849626 5271263 := bstep (se 1 (by rfl) ⟨3953447, by rfl⟩ : syracuseStep 5271263 = 7906895) B7906895
theorem B35557339 : Blo 1849626 35557339 := bstep (se 1 (by rfl) ⟨26668004, by rfl⟩ : syracuseStep 35557339 = 53336009) B53336009
theorem B2777087 : Blo 1849626 2777087 := bstep (se 1 (by rfl) ⟨2082815, by rfl⟩ : syracuseStep 2777087 = 4165631) B4165631
theorem B33755935 : Blo 1849626 33755935 := bstep (se 1 (by rfl) ⟨25316951, by rfl⟩ : syracuseStep 33755935 = 50633903) B50633903
theorem B2774555 : Blo 1849626 2774555 := bstep (se 1 (by rfl) ⟨2080916, by rfl⟩ : syracuseStep 2774555 = 4161833) B4161833
theorem B33781769 : Blo 1849626 33781769 := bstep (se 2 (by rfl) ⟨12668163, by rfl⟩ : syracuseStep 33781769 = 25336327) B25336327
theorem B6248555 : Blo 1849626 6248555 := bstep (se 1 (by rfl) ⟨4686416, by rfl⟩ : syracuseStep 6248555 = 9372833) B9372833
theorem B2775215 : Blo 1849626 2775215 := bstep (se 1 (by rfl) ⟨2081411, by rfl⟩ : syracuseStep 2775215 = 4162823) B4162823
theorem B296532413 : Blo 1849626 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B527014511 : Blo 1849626 527014511 := bstep (se 1 (by rfl) ⟨395260883, by rfl⟩ : syracuseStep 527014511 = 790521767) B790521767
theorem B1849983 : Blo 1849626 1849983 := bstep (se 1 (by rfl) ⟨1387487, by rfl⟩ : syracuseStep 1849983 = 2774975) B2774975
theorem B1850011 : Blo 1849626 1850011 := bstep (se 1 (by rfl) ⟨1387508, by rfl⟩ : syracuseStep 1850011 = 2775017) B2775017
theorem B14056577 : Blo 1849626 14056577 := bstep (se 2 (by rfl) ⟨5271216, by rfl⟩ : syracuseStep 14056577 = 10542433) B10542433
theorem B1850527 : Blo 1849626 1850527 := bstep (se 1 (by rfl) ⟨1387895, by rfl⟩ : syracuseStep 1850527 = 2775791) B2775791
theorem B16023041 : Blo 1849626 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B9371375 : Blo 1849626 9371375 := bstep (se 1 (by rfl) ⟨7028531, by rfl⟩ : syracuseStep 9371375 = 14057063) B14057063
theorem B45007913 : Blo 1849626 45007913 := bstep (se 2 (by rfl) ⟨16877967, by rfl⟩ : syracuseStep 45007913 = 33755935) B33755935
theorem B22521179 : Blo 1849626 22521179 := bstep (se 1 (by rfl) ⟨16890884, by rfl⟩ : syracuseStep 22521179 = 33781769) B33781769
theorem B2082811 : Blo 1849626 2082811 := bstep (se 1 (by rfl) ⟨1562108, by rfl⟩ : syracuseStep 2082811 = 3124217) B3124217
theorem B10537127 : Blo 1849626 10537127 := bstep (se 1 (by rfl) ⟨7902845, by rfl⟩ : syracuseStep 10537127 = 15805691) B15805691
theorem B4163759 : Blo 1849626 4163759 := bstep (se 1 (by rfl) ⟨3122819, by rfl⟩ : syracuseStep 4163759 = 6245639) B6245639
theorem B47409785 : Blo 1849626 47409785 := bstep (se 2 (by rfl) ⟨17778669, by rfl⟩ : syracuseStep 47409785 = 35557339) B35557339
theorem B5926583 : Blo 1849626 5926583 := bstep (se 1 (by rfl) ⟨4444937, by rfl⟩ : syracuseStep 5926583 = 8889875) B8889875
theorem B9367487 : Blo 1849626 9367487 := bstep (se 1 (by rfl) ⟨7025615, by rfl⟩ : syracuseStep 9367487 = 14051231) B14051231
theorem B4165703 : Blo 1849626 4165703 := bstep (se 1 (by rfl) ⟨3124277, by rfl⟩ : syracuseStep 4165703 = 6248555) B6248555
theorem B351343007 : Blo 1849626 351343007 := bstep (se 1 (by rfl) ⟨263507255, by rfl⟩ : syracuseStep 351343007 = 527014511) B527014511
theorem B6247583 : Blo 1849626 6247583 := bstep (se 1 (by rfl) ⟨4685687, by rfl⟩ : syracuseStep 6247583 = 9371375) B9371375
theorem B6763913 : Blo 1849626 6763913 := bstep (se 2 (by rfl) ⟨2536467, by rfl⟩ : syracuseStep 6763913 = 5072935) B5072935
theorem B17782361 : Blo 1849626 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B2775095 : Blo 1849626 2775095 := bstep (se 1 (by rfl) ⟨2081321, by rfl⟩ : syracuseStep 2775095 = 4162643) B4162643
theorem B2775161 : Blo 1849626 2775161 := bstep (se 2 (by rfl) ⟨1040685, by rfl⟩ : syracuseStep 2775161 = 2081371) B2081371
theorem B1849703 : Blo 1849626 1849703 := bstep (se 1 (by rfl) ⟨1387277, by rfl⟩ : syracuseStep 1849703 = 2774555) B2774555
theorem B1850143 : Blo 1849626 1850143 := bstep (se 1 (by rfl) ⟨1387607, by rfl⟩ : syracuseStep 1850143 = 2775215) B2775215
theorem B197688275 : Blo 1849626 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B9371051 : Blo 1849626 9371051 := bstep (se 1 (by rfl) ⟨7028288, by rfl⟩ : syracuseStep 9371051 = 14056577) B14056577
theorem B10682027 : Blo 1849626 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B2776841 : Blo 1849626 2776841 := bstep (se 2 (by rfl) ⟨1041315, by rfl⟩ : syracuseStep 2776841 = 2082631) B2082631
theorem B3514175 : Blo 1849626 3514175 := bstep (se 1 (by rfl) ⟨2635631, by rfl⟩ : syracuseStep 3514175 = 5271263) B5271263
theorem B1851391 : Blo 1849626 1851391 := bstep (se 1 (by rfl) ⟨1388543, by rfl⟩ : syracuseStep 1851391 = 2777087) B2777087
theorem B2777135 : Blo 1849626 2777135 := bstep (se 1 (by rfl) ⟨2082851, by rfl⟩ : syracuseStep 2777135 = 4165703) B4165703
theorem B60056477 : Blo 1849626 60056477 := bstep (se 3 (by rfl) ⟨11260589, by rfl⟩ : syracuseStep 60056477 = 22521179) B22521179
theorem B11854907 : Blo 1849626 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B31606523 : Blo 1849626 31606523 := bstep (se 1 (by rfl) ⟨23704892, by rfl⟩ : syracuseStep 31606523 = 47409785) B47409785
theorem B7121351 : Blo 1849626 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B3951055 : Blo 1849626 3951055 := bstep (se 1 (by rfl) ⟨2963291, by rfl⟩ : syracuseStep 3951055 = 5926583) B5926583
theorem B6244991 : Blo 1849626 6244991 := bstep (se 1 (by rfl) ⟨4683743, by rfl⟩ : syracuseStep 6244991 = 9367487) B9367487
theorem B234228671 : Blo 1849626 234228671 := bstep (se 1 (by rfl) ⟨175671503, by rfl⟩ : syracuseStep 234228671 = 351343007) B351343007
theorem B4165055 : Blo 1849626 4165055 := bstep (se 1 (by rfl) ⟨3123791, by rfl⟩ : syracuseStep 4165055 = 6247583) B6247583
theorem B4509275 : Blo 1849626 4509275 := bstep (se 1 (by rfl) ⟨3381956, by rfl⟩ : syracuseStep 4509275 = 6763913) B6763913
theorem B7024751 : Blo 1849626 7024751 := bstep (se 1 (by rfl) ⟨5268563, by rfl⟩ : syracuseStep 7024751 = 10537127) B10537127
theorem B6247367 : Blo 1849626 6247367 := bstep (se 1 (by rfl) ⟨4685525, by rfl⟩ : syracuseStep 6247367 = 9371051) B9371051
theorem B30005275 : Blo 1849626 30005275 := bstep (se 1 (by rfl) ⟨22503956, by rfl⟩ : syracuseStep 30005275 = 45007913) B45007913
theorem B1850063 : Blo 1849626 1850063 := bstep (se 1 (by rfl) ⟨1387547, by rfl⟩ : syracuseStep 1850063 = 2775095) B2775095
theorem B1850107 : Blo 1849626 1850107 := bstep (se 1 (by rfl) ⟨1387580, by rfl⟩ : syracuseStep 1850107 = 2775161) B2775161
theorem B2775839 : Blo 1849626 2775839 := bstep (se 1 (by rfl) ⟨2081879, by rfl⟩ : syracuseStep 2775839 = 4163759) B4163759
theorem B131792183 : Blo 1849626 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B1851227 : Blo 1849626 1851227 := bstep (se 1 (by rfl) ⟨1388420, by rfl⟩ : syracuseStep 1851227 = 2776841) B2776841
theorem B2342783 : Blo 1849626 2342783 := bstep (se 1 (by rfl) ⟨1757087, by rfl⟩ : syracuseStep 2342783 = 3514175) B3514175
theorem B2777081 : Blo 1849626 2777081 := bstep (se 2 (by rfl) ⟨1041405, by rfl⟩ : syracuseStep 2777081 = 2082811) B2082811
theorem B1851423 : Blo 1849626 1851423 := bstep (se 1 (by rfl) ⟨1388567, by rfl⟩ : syracuseStep 1851423 = 2777135) B2777135
theorem B5268073 : Blo 1849626 5268073 := bstep (se 2 (by rfl) ⟨1975527, by rfl⟩ : syracuseStep 5268073 = 3951055) B3951055
theorem B21071015 : Blo 1849626 21071015 := bstep (se 1 (by rfl) ⟨15803261, by rfl⟩ : syracuseStep 21071015 = 31606523) B31606523
theorem B4163327 : Blo 1849626 4163327 := bstep (se 1 (by rfl) ⟨3122495, by rfl⟩ : syracuseStep 4163327 = 6244991) B6244991
theorem B87861455 : Blo 1849626 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B40037651 : Blo 1849626 40037651 := bstep (se 1 (by rfl) ⟨30028238, by rfl⟩ : syracuseStep 40037651 = 60056477) B60056477
theorem B4164911 : Blo 1849626 4164911 := bstep (se 1 (by rfl) ⟨3123683, by rfl⟩ : syracuseStep 4164911 = 6247367) B6247367
theorem B48098933 : Blo 1849626 48098933 := bstep (se 5 (by rfl) ⟨2254637, by rfl⟩ : syracuseStep 48098933 = 4509275) B4509275
theorem B4747567 : Blo 1849626 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B156152447 : Blo 1849626 156152447 := bstep (se 1 (by rfl) ⟨117114335, by rfl⟩ : syracuseStep 156152447 = 234228671) B234228671
theorem B6247421 : Blo 1849626 6247421 := bstep (se 3 (by rfl) ⟨1171391, by rfl⟩ : syracuseStep 6247421 = 2342783) B2342783
theorem B40007033 : Blo 1849626 40007033 := bstep (se 2 (by rfl) ⟨15002637, by rfl⟩ : syracuseStep 40007033 = 30005275) B30005275
theorem B4683167 : Blo 1849626 4683167 := bstep (se 1 (by rfl) ⟨3512375, by rfl⟩ : syracuseStep 4683167 = 7024751) B7024751
theorem B7903271 : Blo 1849626 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B1850559 : Blo 1849626 1850559 := bstep (se 1 (by rfl) ⟨1387919, by rfl⟩ : syracuseStep 1850559 = 2775839) B2775839
theorem B2776703 : Blo 1849626 2776703 := bstep (se 1 (by rfl) ⟨2082527, by rfl⟩ : syracuseStep 2776703 = 4165055) B4165055
theorem B1851387 : Blo 1849626 1851387 := bstep (se 1 (by rfl) ⟨1388540, by rfl⟩ : syracuseStep 1851387 = 2777081) B2777081
theorem B3122111 : Blo 1849626 3122111 := bstep (se 1 (by rfl) ⟨2341583, by rfl⟩ : syracuseStep 3122111 = 4683167) B4683167
theorem B58574303 : Blo 1849626 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B26691767 : Blo 1849626 26691767 := bstep (se 1 (by rfl) ⟨20018825, by rfl⟩ : syracuseStep 26691767 = 40037651) B40037651
theorem B32065955 : Blo 1849626 32065955 := bstep (se 1 (by rfl) ⟨24049466, by rfl⟩ : syracuseStep 32065955 = 48098933) B48098933
theorem B4164947 : Blo 1849626 4164947 := bstep (se 1 (by rfl) ⟨3123710, by rfl⟩ : syracuseStep 4164947 = 6247421) B6247421
theorem B7024097 : Blo 1849626 7024097 := bstep (se 2 (by rfl) ⟨2634036, by rfl⟩ : syracuseStep 7024097 = 5268073) B5268073
theorem B21075389 : Blo 1849626 21075389 := bstep (se 3 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 21075389 = 7903271) B7903271
theorem B6330089 : Blo 1849626 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B104101631 : Blo 1849626 104101631 := bstep (se 1 (by rfl) ⟨78076223, by rfl⟩ : syracuseStep 104101631 = 156152447) B156152447
theorem B14047343 : Blo 1849626 14047343 := bstep (se 1 (by rfl) ⟨10535507, by rfl⟩ : syracuseStep 14047343 = 21071015) B21071015
theorem B26671355 : Blo 1849626 26671355 := bstep (se 1 (by rfl) ⟨20003516, by rfl⟩ : syracuseStep 26671355 = 40007033) B40007033
theorem B2775551 : Blo 1849626 2775551 := bstep (se 1 (by rfl) ⟨2081663, by rfl⟩ : syracuseStep 2775551 = 4163327) B4163327
theorem B2776607 : Blo 1849626 2776607 := bstep (se 1 (by rfl) ⟨2082455, by rfl⟩ : syracuseStep 2776607 = 4164911) B4164911
theorem B1851135 : Blo 1849626 1851135 := bstep (se 1 (by rfl) ⟨1388351, by rfl⟩ : syracuseStep 1851135 = 2776703) B2776703
theorem B2081407 : Blo 1849626 2081407 := bstep (se 1 (by rfl) ⟨1561055, by rfl⟩ : syracuseStep 2081407 = 3122111) B3122111
theorem B14050259 : Blo 1849626 14050259 := bstep (se 1 (by rfl) ⟨10537694, by rfl⟩ : syracuseStep 14050259 = 21075389) B21075389
theorem B9364895 : Blo 1849626 9364895 := bstep (se 1 (by rfl) ⟨7023671, by rfl⟩ : syracuseStep 9364895 = 14047343) B14047343
theorem B17794511 : Blo 1849626 17794511 := bstep (se 1 (by rfl) ⟨13345883, by rfl⟩ : syracuseStep 17794511 = 26691767) B26691767
theorem B17780903 : Blo 1849626 17780903 := bstep (se 1 (by rfl) ⟨13335677, by rfl⟩ : syracuseStep 17780903 = 26671355) B26671355
theorem B21377303 : Blo 1849626 21377303 := bstep (se 1 (by rfl) ⟨16032977, by rfl⟩ : syracuseStep 21377303 = 32065955) B32065955
theorem B16880237 : Blo 1849626 16880237 := bstep (se 3 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 16880237 = 6330089) B6330089
theorem B4682731 : Blo 1849626 4682731 := bstep (se 1 (by rfl) ⟨3512048, by rfl⟩ : syracuseStep 4682731 = 7024097) B7024097
theorem B39049535 : Blo 1849626 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B69401087 : Blo 1849626 69401087 := bstep (se 1 (by rfl) ⟨52050815, by rfl⟩ : syracuseStep 69401087 = 104101631) B104101631
theorem B1850367 : Blo 1849626 1850367 := bstep (se 1 (by rfl) ⟨1387775, by rfl⟩ : syracuseStep 1850367 = 2775551) B2775551
theorem B2776631 : Blo 1849626 2776631 := bstep (se 1 (by rfl) ⟨2082473, by rfl⟩ : syracuseStep 2776631 = 4164947) B4164947
theorem B1851071 : Blo 1849626 1851071 := bstep (se 1 (by rfl) ⟨1388303, by rfl⟩ : syracuseStep 1851071 = 2776607) B2776607
theorem B11853935 : Blo 1849626 11853935 := bstep (se 1 (by rfl) ⟨8890451, by rfl⟩ : syracuseStep 11853935 = 17780903) B17780903
theorem B6243263 : Blo 1849626 6243263 := bstep (se 1 (by rfl) ⟨4682447, by rfl⟩ : syracuseStep 6243263 = 9364895) B9364895
theorem B11863007 : Blo 1849626 11863007 := bstep (se 1 (by rfl) ⟨8897255, by rfl⟩ : syracuseStep 11863007 = 17794511) B17794511
theorem B6243641 : Blo 1849626 6243641 := bstep (se 2 (by rfl) ⟨2341365, by rfl⟩ : syracuseStep 6243641 = 4682731) B4682731
theorem B9366839 : Blo 1849626 9366839 := bstep (se 1 (by rfl) ⟨7025129, by rfl⟩ : syracuseStep 9366839 = 14050259) B14050259
theorem B14251535 : Blo 1849626 14251535 := bstep (se 1 (by rfl) ⟨10688651, by rfl⟩ : syracuseStep 14251535 = 21377303) B21377303
theorem B11253491 : Blo 1849626 11253491 := bstep (se 1 (by rfl) ⟨8440118, by rfl⟩ : syracuseStep 11253491 = 16880237) B16880237
theorem B2775209 : Blo 1849626 2775209 := bstep (se 2 (by rfl) ⟨1040703, by rfl⟩ : syracuseStep 2775209 = 2081407) B2081407
theorem B26033023 : Blo 1849626 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B46267391 : Blo 1849626 46267391 := bstep (se 1 (by rfl) ⟨34700543, by rfl⟩ : syracuseStep 46267391 = 69401087) B69401087
theorem B1851087 : Blo 1849626 1851087 := bstep (se 1 (by rfl) ⟨1388315, by rfl⟩ : syracuseStep 1851087 = 2776631) B2776631
theorem B4162175 : Blo 1849626 4162175 := bstep (se 1 (by rfl) ⟨3121631, by rfl⟩ : syracuseStep 4162175 = 6243263) B6243263
theorem B4162427 : Blo 1849626 4162427 := bstep (se 1 (by rfl) ⟨3121820, by rfl⟩ : syracuseStep 4162427 = 6243641) B6243641
theorem B34710697 : Blo 1849626 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B30844927 : Blo 1849626 30844927 := bstep (se 1 (by rfl) ⟨23133695, by rfl⟩ : syracuseStep 30844927 = 46267391) B46267391
theorem B6244559 : Blo 1849626 6244559 := bstep (se 1 (by rfl) ⟨4683419, by rfl⟩ : syracuseStep 6244559 = 9366839) B9366839
theorem B7908671 : Blo 1849626 7908671 := bstep (se 1 (by rfl) ⟨5931503, by rfl⟩ : syracuseStep 7908671 = 11863007) B11863007
theorem B7902623 : Blo 1849626 7902623 := bstep (se 1 (by rfl) ⟨5926967, by rfl⟩ : syracuseStep 7902623 = 11853935) B11853935
theorem B9501023 : Blo 1849626 9501023 := bstep (se 1 (by rfl) ⟨7125767, by rfl⟩ : syracuseStep 9501023 = 14251535) B14251535
theorem B7502327 : Blo 1849626 7502327 := bstep (se 1 (by rfl) ⟨5626745, by rfl⟩ : syracuseStep 7502327 = 11253491) B11253491
theorem B1850139 : Blo 1849626 1850139 := bstep (se 1 (by rfl) ⟨1387604, by rfl⟩ : syracuseStep 1850139 = 2775209) B2775209
theorem B5268415 : Blo 1849626 5268415 := bstep (se 1 (by rfl) ⟨3951311, by rfl⟩ : syracuseStep 5268415 = 7902623) B7902623
theorem B4163039 : Blo 1849626 4163039 := bstep (se 1 (by rfl) ⟨3122279, by rfl⟩ : syracuseStep 4163039 = 6244559) B6244559
theorem B164506277 : Blo 1849626 164506277 := bstep (se 4 (by rfl) ⟨15422463, by rfl⟩ : syracuseStep 164506277 = 30844927) B30844927
theorem B46280929 : Blo 1849626 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B5001551 : Blo 1849626 5001551 := bstep (se 1 (by rfl) ⟨3751163, by rfl⟩ : syracuseStep 5001551 = 7502327) B7502327
theorem B5272447 : Blo 1849626 5272447 := bstep (se 1 (by rfl) ⟨3954335, by rfl⟩ : syracuseStep 5272447 = 7908671) B7908671
theorem B2774783 : Blo 1849626 2774783 := bstep (se 1 (by rfl) ⟨2081087, by rfl⟩ : syracuseStep 2774783 = 4162175) B4162175
theorem B2774951 : Blo 1849626 2774951 := bstep (se 1 (by rfl) ⟨2081213, by rfl⟩ : syracuseStep 2774951 = 4162427) B4162427
theorem B25336061 : Blo 1849626 25336061 := bstep (se 3 (by rfl) ⟨4750511, by rfl⟩ : syracuseStep 25336061 = 9501023) B9501023
theorem B3334367 : Blo 1849626 3334367 := bstep (se 1 (by rfl) ⟨2500775, by rfl⟩ : syracuseStep 3334367 = 5001551) B5001551
theorem B7029929 : Blo 1849626 7029929 := bstep (se 2 (by rfl) ⟨2636223, by rfl⟩ : syracuseStep 7029929 = 5272447) B5272447
theorem B7024553 : Blo 1849626 7024553 := bstep (se 2 (by rfl) ⟨2634207, by rfl⟩ : syracuseStep 7024553 = 5268415) B5268415
theorem B109670851 : Blo 1849626 109670851 := bstep (se 1 (by rfl) ⟨82253138, by rfl⟩ : syracuseStep 109670851 = 164506277) B164506277
theorem B61707905 : Blo 1849626 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B2775359 : Blo 1849626 2775359 := bstep (se 1 (by rfl) ⟨2081519, by rfl⟩ : syracuseStep 2775359 = 4163039) B4163039
theorem B1849855 : Blo 1849626 1849855 := bstep (se 1 (by rfl) ⟨1387391, by rfl⟩ : syracuseStep 1849855 = 2774783) B2774783
theorem B1849967 : Blo 1849626 1849967 := bstep (se 1 (by rfl) ⟨1387475, by rfl⟩ : syracuseStep 1849967 = 2774951) B2774951
theorem B16890707 : Blo 1849626 16890707 := bstep (se 1 (by rfl) ⟨12668030, by rfl⟩ : syracuseStep 16890707 = 25336061) B25336061
theorem B4686619 : Blo 1849626 4686619 := bstep (se 1 (by rfl) ⟨3514964, by rfl⟩ : syracuseStep 4686619 = 7029929) B7029929
theorem B584911205 : Blo 1849626 584911205 := bstep (se 4 (by rfl) ⟨54835425, by rfl⟩ : syracuseStep 584911205 = 109670851) B109670851
theorem B2222911 : Blo 1849626 2222911 := bstep (se 1 (by rfl) ⟨1667183, by rfl⟩ : syracuseStep 2222911 = 3334367) B3334367
theorem B11260471 : Blo 1849626 11260471 := bstep (se 1 (by rfl) ⟨8445353, by rfl⟩ : syracuseStep 11260471 = 16890707) B16890707
theorem B4683035 : Blo 1849626 4683035 := bstep (se 1 (by rfl) ⟨3512276, by rfl⟩ : syracuseStep 4683035 = 7024553) B7024553
theorem B41138603 : Blo 1849626 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B1850239 : Blo 1849626 1850239 := bstep (se 1 (by rfl) ⟨1387679, by rfl⟩ : syracuseStep 1850239 = 2775359) B2775359
theorem B3122023 : Blo 1849626 3122023 := bstep (se 1 (by rfl) ⟨2341517, by rfl⟩ : syracuseStep 3122023 = 4683035) B4683035
theorem B389940803 : Blo 1849626 389940803 := bstep (se 1 (by rfl) ⟨292455602, by rfl⟩ : syracuseStep 389940803 = 584911205) B584911205
theorem B15013961 : Blo 1849626 15013961 := bstep (se 2 (by rfl) ⟨5630235, by rfl⟩ : syracuseStep 15013961 = 11260471) B11260471
theorem B6248825 : Blo 1849626 6248825 := bstep (se 2 (by rfl) ⟨2343309, by rfl⟩ : syracuseStep 6248825 = 4686619) B4686619
theorem B2963881 : Blo 1849626 2963881 := bstep (se 2 (by rfl) ⟨1111455, by rfl⟩ : syracuseStep 2963881 = 2222911) B2222911
theorem B27425735 : Blo 1849626 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B4162697 : Blo 1849626 4162697 := bstep (se 2 (by rfl) ⟨1561011, by rfl⟩ : syracuseStep 4162697 = 3122023) B3122023
theorem B3951841 : Blo 1849626 3951841 := bstep (se 2 (by rfl) ⟨1481940, by rfl⟩ : syracuseStep 3951841 = 2963881) B2963881
theorem B259960535 : Blo 1849626 259960535 := bstep (se 1 (by rfl) ⟨194970401, by rfl⟩ : syracuseStep 259960535 = 389940803) B389940803
theorem B4165883 : Blo 1849626 4165883 := bstep (se 1 (by rfl) ⟨3124412, by rfl⟩ : syracuseStep 4165883 = 6248825) B6248825
theorem B10009307 : Blo 1849626 10009307 := bstep (se 1 (by rfl) ⟨7506980, by rfl⟩ : syracuseStep 10009307 = 15013961) B15013961
theorem B18283823 : Blo 1849626 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B2777255 : Blo 1849626 2777255 := bstep (se 1 (by rfl) ⟨2082941, by rfl⟩ : syracuseStep 2777255 = 4165883) B4165883
theorem B5269121 : Blo 1849626 5269121 := bstep (se 2 (by rfl) ⟨1975920, by rfl⟩ : syracuseStep 5269121 = 3951841) B3951841
theorem B6672871 : Blo 1849626 6672871 := bstep (se 1 (by rfl) ⟨5004653, by rfl⟩ : syracuseStep 6672871 = 10009307) B10009307
theorem B173307023 : Blo 1849626 173307023 := bstep (se 1 (by rfl) ⟨129980267, by rfl⟩ : syracuseStep 173307023 = 259960535) B259960535
theorem B2775131 : Blo 1849626 2775131 := bstep (se 1 (by rfl) ⟨2081348, by rfl⟩ : syracuseStep 2775131 = 4162697) B4162697
theorem B12189215 : Blo 1849626 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B1851503 : Blo 1849626 1851503 := bstep (se 1 (by rfl) ⟨1388627, by rfl⟩ : syracuseStep 1851503 = 2777255) B2777255
theorem B8897161 : Blo 1849626 8897161 := bstep (se 2 (by rfl) ⟨3336435, by rfl⟩ : syracuseStep 8897161 = 6672871) B6672871
theorem B115538015 : Blo 1849626 115538015 := bstep (se 1 (by rfl) ⟨86653511, by rfl⟩ : syracuseStep 115538015 = 173307023) B173307023
theorem B3512747 : Blo 1849626 3512747 := bstep (se 1 (by rfl) ⟨2634560, by rfl⟩ : syracuseStep 3512747 = 5269121) B5269121
theorem B1850087 : Blo 1849626 1850087 := bstep (se 1 (by rfl) ⟨1387565, by rfl⟩ : syracuseStep 1850087 = 2775131) B2775131
theorem B8126143 : Blo 1849626 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B11862881 : Blo 1849626 11862881 := bstep (se 2 (by rfl) ⟨4448580, by rfl⟩ : syracuseStep 11862881 = 8897161) B8897161
theorem B43339429 : Blo 1849626 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B9367325 : Blo 1849626 9367325 := bstep (se 3 (by rfl) ⟨1756373, by rfl⟩ : syracuseStep 9367325 = 3512747) B3512747
theorem B77025343 : Blo 1849626 77025343 := bstep (se 1 (by rfl) ⟨57769007, by rfl⟩ : syracuseStep 77025343 = 115538015) B115538015
theorem B6244883 : Blo 1849626 6244883 := bstep (se 1 (by rfl) ⟨4683662, by rfl⟩ : syracuseStep 6244883 = 9367325) B9367325
theorem B7908587 : Blo 1849626 7908587 := bstep (se 1 (by rfl) ⟨5931440, by rfl⟩ : syracuseStep 7908587 = 11862881) B11862881
theorem B102700457 : Blo 1849626 102700457 := bstep (se 2 (by rfl) ⟨38512671, by rfl⟩ : syracuseStep 102700457 = 77025343) B77025343
theorem B57785905 : Blo 1849626 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 1849626 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B4163255 : Blo 1849626 4163255 := bstep (se 1 (by rfl) ⟨3122441, by rfl⟩ : syracuseStep 4163255 = 6244883) B6244883
theorem B5272391 : Blo 1849626 5272391 := bstep (se 1 (by rfl) ⟨3954293, by rfl⟩ : syracuseStep 5272391 = 7908587) B7908587
theorem B68466971 : Blo 1849626 68466971 := bstep (se 1 (by rfl) ⟨51350228, by rfl⟩ : syracuseStep 68466971 = 102700457) B102700457
theorem B3514927 : Blo 1849626 3514927 := bstep (se 1 (by rfl) ⟨2636195, by rfl⟩ : syracuseStep 3514927 = 5272391) B5272391
theorem B205460995 : Blo 1849626 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B2775503 : Blo 1849626 2775503 := bstep (se 1 (by rfl) ⟨2081627, by rfl⟩ : syracuseStep 2775503 = 4163255) B4163255
theorem B45644647 : Blo 1849626 45644647 := bstep (se 1 (by rfl) ⟨34233485, by rfl⟩ : syracuseStep 45644647 = 68466971) B68466971
theorem B4686569 : Blo 1849626 4686569 := bstep (se 2 (by rfl) ⟨1757463, by rfl⟩ : syracuseStep 4686569 = 3514927) B3514927
theorem B60859529 : Blo 1849626 60859529 := bstep (se 2 (by rfl) ⟨22822323, by rfl⟩ : syracuseStep 60859529 = 45644647) B45644647
theorem B1850335 : Blo 1849626 1850335 := bstep (se 1 (by rfl) ⟨1387751, by rfl⟩ : syracuseStep 1850335 = 2775503) B2775503
theorem B273947993 : Blo 1849626 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B3124379 : Blo 1849626 3124379 := bstep (se 1 (by rfl) ⟨2343284, by rfl⟩ : syracuseStep 3124379 = 4686569) B4686569
theorem B40573019 : Blo 1849626 40573019 := bstep (se 1 (by rfl) ⟨30429764, by rfl⟩ : syracuseStep 40573019 = 60859529) B60859529
theorem B182631995 : Blo 1849626 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B2082919 : Blo 1849626 2082919 := bstep (se 1 (by rfl) ⟨1562189, by rfl⟩ : syracuseStep 2082919 = 3124379) B3124379
theorem B108194717 : Blo 1849626 108194717 := bstep (se 3 (by rfl) ⟨20286509, by rfl⟩ : syracuseStep 108194717 = 40573019) B40573019
theorem B121754663 : Blo 1849626 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B2777225 : Blo 1849626 2777225 := bstep (se 2 (by rfl) ⟨1041459, by rfl⟩ : syracuseStep 2777225 = 2082919) B2082919
theorem B81169775 : Blo 1849626 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B288519245 : Blo 1849626 288519245 := bstep (se 3 (by rfl) ⟨54097358, by rfl⟩ : syracuseStep 288519245 = 108194717) B108194717
theorem B1851483 : Blo 1849626 1851483 := bstep (se 1 (by rfl) ⟨1388612, by rfl⟩ : syracuseStep 1851483 = 2777225) B2777225
theorem B54113183 : Blo 1849626 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B192346163 : Blo 1849626 192346163 := bstep (se 1 (by rfl) ⟨144259622, by rfl⟩ : syracuseStep 192346163 = 288519245) B288519245
theorem B128230775 : Blo 1849626 128230775 := bstep (se 1 (by rfl) ⟨96173081, by rfl⟩ : syracuseStep 128230775 = 192346163) B192346163
theorem B36075455 : Blo 1849626 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B85487183 : Blo 1849626 85487183 := bstep (se 1 (by rfl) ⟨64115387, by rfl⟩ : syracuseStep 85487183 = 128230775) B128230775
theorem B24050303 : Blo 1849626 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B16033535 : Blo 1849626 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B56991455 : Blo 1849626 56991455 := bstep (se 1 (by rfl) ⟨42743591, by rfl⟩ : syracuseStep 56991455 = 85487183) B85487183
theorem B10689023 : Blo 1849626 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B37994303 : Blo 1849626 37994303 := bstep (se 1 (by rfl) ⟨28495727, by rfl⟩ : syracuseStep 37994303 = 56991455) B56991455
theorem B28504061 : Blo 1849626 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B101318141 : Blo 1849626 101318141 := bstep (se 3 (by rfl) ⟨18997151, by rfl⟩ : syracuseStep 101318141 = 37994303) B37994303
theorem B67545427 : Blo 1849626 67545427 := bstep (se 1 (by rfl) ⟨50659070, by rfl⟩ : syracuseStep 67545427 = 101318141) B101318141
theorem B19002707 : Blo 1849626 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B12668471 : Blo 1849626 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B90060569 : Blo 1849626 90060569 := bstep (se 2 (by rfl) ⟨33772713, by rfl⟩ : syracuseStep 90060569 = 67545427) B67545427
theorem B60040379 : Blo 1849626 60040379 := bstep (se 1 (by rfl) ⟨45030284, by rfl⟩ : syracuseStep 60040379 = 90060569) B90060569
theorem B8445647 : Blo 1849626 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B40026919 : Blo 1849626 40026919 := bstep (se 1 (by rfl) ⟨30020189, by rfl⟩ : syracuseStep 40026919 = 60040379) B60040379
theorem B22521725 : Blo 1849626 22521725 := bstep (se 3 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 22521725 = 8445647) B8445647
theorem B53369225 : Blo 1849626 53369225 := bstep (se 2 (by rfl) ⟨20013459, by rfl⟩ : syracuseStep 53369225 = 40026919) B40026919
theorem B15014483 : Blo 1849626 15014483 := bstep (se 1 (by rfl) ⟨11260862, by rfl⟩ : syracuseStep 15014483 = 22521725) B22521725
theorem B35579483 : Blo 1849626 35579483 := bstep (se 1 (by rfl) ⟨26684612, by rfl⟩ : syracuseStep 35579483 = 53369225) B53369225
theorem B10009655 : Blo 1849626 10009655 := bstep (se 1 (by rfl) ⟨7507241, by rfl⟩ : syracuseStep 10009655 = 15014483) B15014483
theorem B23719655 : Blo 1849626 23719655 := bstep (se 1 (by rfl) ⟨17789741, by rfl⟩ : syracuseStep 23719655 = 35579483) B35579483
theorem B6673103 : Blo 1849626 6673103 := bstep (se 1 (by rfl) ⟨5004827, by rfl⟩ : syracuseStep 6673103 = 10009655) B10009655
theorem B4448735 : Blo 1849626 4448735 := bstep (se 1 (by rfl) ⟨3336551, by rfl⟩ : syracuseStep 4448735 = 6673103) B6673103
theorem B15813103 : Blo 1849626 15813103 := bstep (se 1 (by rfl) ⟨11859827, by rfl⟩ : syracuseStep 15813103 = 23719655) B23719655
theorem B2965823 : Blo 1849626 2965823 := bstep (se 1 (by rfl) ⟨2224367, by rfl⟩ : syracuseStep 2965823 = 4448735) B4448735
theorem B21084137 : Blo 1849626 21084137 := bstep (se 2 (by rfl) ⟨7906551, by rfl⟩ : syracuseStep 21084137 = 15813103) B15813103
theorem B1977215 : Blo 1849626 1977215 := bstep (se 1 (by rfl) ⟨1482911, by rfl⟩ : syracuseStep 1977215 = 2965823) B2965823
theorem B14056091 : Blo 1849626 14056091 := bstep (se 1 (by rfl) ⟨10542068, by rfl⟩ : syracuseStep 14056091 = 21084137) B21084137
theorem B5272573 : Blo 1849626 5272573 := bstep (se 3 (by rfl) ⟨988607, by rfl⟩ : syracuseStep 5272573 = 1977215) B1977215
theorem B9370727 : Blo 1849626 9370727 := bstep (se 1 (by rfl) ⟨7028045, by rfl⟩ : syracuseStep 9370727 = 14056091) B14056091
theorem B7030097 : Blo 1849626 7030097 := bstep (se 2 (by rfl) ⟨2636286, by rfl⟩ : syracuseStep 7030097 = 5272573) B5272573
theorem B6247151 : Blo 1849626 6247151 := bstep (se 1 (by rfl) ⟨4685363, by rfl⟩ : syracuseStep 6247151 = 9370727) B9370727
theorem B4686731 : Blo 1849626 4686731 := bstep (se 1 (by rfl) ⟨3515048, by rfl⟩ : syracuseStep 4686731 = 7030097) B7030097
theorem B4164767 : Blo 1849626 4164767 := bstep (se 1 (by rfl) ⟨3123575, by rfl⟩ : syracuseStep 4164767 = 6247151) B6247151
theorem B3124487 : Blo 1849626 3124487 := bstep (se 1 (by rfl) ⟨2343365, by rfl⟩ : syracuseStep 3124487 = 4686731) B4686731
theorem B2776511 : Blo 1849626 2776511 := bstep (se 1 (by rfl) ⟨2082383, by rfl⟩ : syracuseStep 2776511 = 4164767) B4164767
theorem B2082991 : Blo 1849626 2082991 := bstep (se 1 (by rfl) ⟨1562243, by rfl⟩ : syracuseStep 2082991 = 3124487) B3124487
theorem B1851007 : Blo 1849626 1851007 := bstep (se 1 (by rfl) ⟨1388255, by rfl⟩ : syracuseStep 1851007 = 2776511) B2776511
theorem B2777321 : Blo 1849626 2777321 := bstep (se 2 (by rfl) ⟨1041495, by rfl⟩ : syracuseStep 2777321 = 2082991) B2082991
theorem B1851547 : Blo 1849626 1851547 := bstep (se 1 (by rfl) ⟨1388660, by rfl⟩ : syracuseStep 1851547 = 2777321) B2777321

theorem C0 (j : ℕ) (h1 : 462406 ≤ j) (h2 : j ≤ 462905) : Blo 1849626 (4 * j + 3) := by
  interval_cases j
  · exact B1849627
  · exact B1849631
  · exact B1849635
  · exact B1849639
  · exact B1849643
  · exact B1849647
  · exact B1849651
  · exact B1849655
  · exact B1849659
  · exact B1849663
  · exact B1849667
  · exact B1849671
  · exact B1849675
  · exact B1849679
  · exact B1849683
  · exact B1849687
  · exact B1849691
  · exact B1849695
  · exact B1849699
  · exact B1849703
  · exact B1849707
  · exact B1849711
  · exact B1849715
  · exact B1849719
  · exact B1849723
  · exact B1849727
  · exact B1849731
  · exact B1849735
  · exact B1849739
  · exact B1849743
  · exact B1849747
  · exact B1849751
  · exact B1849755
  · exact B1849759
  · exact B1849763
  · exact B1849767
  · exact B1849771
  · exact B1849775
  · exact B1849779
  · exact B1849783
  · exact B1849787
  · exact B1849791
  · exact B1849795
  · exact B1849799
  · exact B1849803
  · exact B1849807
  · exact B1849811
  · exact B1849815
  · exact B1849819
  · exact B1849823
  · exact B1849827
  · exact B1849831
  · exact B1849835
  · exact B1849839
  · exact B1849843
  · exact B1849847
  · exact B1849851
  · exact B1849855
  · exact B1849859
  · exact B1849863
  · exact B1849867
  · exact B1849871
  · exact B1849875
  · exact B1849879
  · exact B1849883
  · exact B1849887
  · exact B1849891
  · exact B1849895
  · exact B1849899
  · exact B1849903
  · exact B1849907
  · exact B1849911
  · exact B1849915
  · exact B1849919
  · exact B1849923
  · exact B1849927
  · exact B1849931
  · exact B1849935
  · exact B1849939
  · exact B1849943
  · exact B1849947
  · exact B1849951
  · exact B1849955
  · exact B1849959
  · exact B1849963
  · exact B1849967
  · exact B1849971
  · exact B1849975
  · exact B1849979
  · exact B1849983
  · exact B1849987
  · exact B1849991
  · exact B1849995
  · exact B1849999
  · exact B1850003
  · exact B1850007
  · exact B1850011
  · exact B1850015
  · exact B1850019
  · exact B1850023
  · exact B1850027
  · exact B1850031
  · exact B1850035
  · exact B1850039
  · exact B1850043
  · exact B1850047
  · exact B1850051
  · exact B1850055
  · exact B1850059
  · exact B1850063
  · exact B1850067
  · exact B1850071
  · exact B1850075
  · exact B1850079
  · exact B1850083
  · exact B1850087
  · exact B1850091
  · exact B1850095
  · exact B1850099
  · exact B1850103
  · exact B1850107
  · exact B1850111
  · exact B1850115
  · exact B1850119
  · exact B1850123
  · exact B1850127
  · exact B1850131
  · exact B1850135
  · exact B1850139
  · exact B1850143
  · exact B1850147
  · exact B1850151
  · exact B1850155
  · exact B1850159
  · exact B1850163
  · exact B1850167
  · exact B1850171
  · exact B1850175
  · exact B1850179
  · exact B1850183
  · exact B1850187
  · exact B1850191
  · exact B1850195
  · exact B1850199
  · exact B1850203
  · exact B1850207
  · exact B1850211
  · exact B1850215
  · exact B1850219
  · exact B1850223
  · exact B1850227
  · exact B1850231
  · exact B1850235
  · exact B1850239
  · exact B1850243
  · exact B1850247
  · exact B1850251
  · exact B1850255
  · exact B1850259
  · exact B1850263
  · exact B1850267
  · exact B1850271
  · exact B1850275
  · exact B1850279
  · exact B1850283
  · exact B1850287
  · exact B1850291
  · exact B1850295
  · exact B1850299
  · exact B1850303
  · exact B1850307
  · exact B1850311
  · exact B1850315
  · exact B1850319
  · exact B1850323
  · exact B1850327
  · exact B1850331
  · exact B1850335
  · exact B1850339
  · exact B1850343
  · exact B1850347
  · exact B1850351
  · exact B1850355
  · exact B1850359
  · exact B1850363
  · exact B1850367
  · exact B1850371
  · exact B1850375
  · exact B1850379
  · exact B1850383
  · exact B1850387
  · exact B1850391
  · exact B1850395
  · exact B1850399
  · exact B1850403
  · exact B1850407
  · exact B1850411
  · exact B1850415
  · exact B1850419
  · exact B1850423
  · exact B1850427
  · exact B1850431
  · exact B1850435
  · exact B1850439
  · exact B1850443
  · exact B1850447
  · exact B1850451
  · exact B1850455
  · exact B1850459
  · exact B1850463
  · exact B1850467
  · exact B1850471
  · exact B1850475
  · exact B1850479
  · exact B1850483
  · exact B1850487
  · exact B1850491
  · exact B1850495
  · exact B1850499
  · exact B1850503
  · exact B1850507
  · exact B1850511
  · exact B1850515
  · exact B1850519
  · exact B1850523
  · exact B1850527
  · exact B1850531
  · exact B1850535
  · exact B1850539
  · exact B1850543
  · exact B1850547
  · exact B1850551
  · exact B1850555
  · exact B1850559
  · exact B1850563
  · exact B1850567
  · exact B1850571
  · exact B1850575
  · exact B1850579
  · exact B1850583
  · exact B1850587
  · exact B1850591
  · exact B1850595
  · exact B1850599
  · exact B1850603
  · exact B1850607
  · exact B1850611
  · exact B1850615
  · exact B1850619
  · exact B1850623
  · exact B1850627
  · exact B1850631
  · exact B1850635
  · exact B1850639
  · exact B1850643
  · exact B1850647
  · exact B1850651
  · exact B1850655
  · exact B1850659
  · exact B1850663
  · exact B1850667
  · exact B1850671
  · exact B1850675
  · exact B1850679
  · exact B1850683
  · exact B1850687
  · exact B1850691
  · exact B1850695
  · exact B1850699
  · exact B1850703
  · exact B1850707
  · exact B1850711
  · exact B1850715
  · exact B1850719
  · exact B1850723
  · exact B1850727
  · exact B1850731
  · exact B1850735
  · exact B1850739
  · exact B1850743
  · exact B1850747
  · exact B1850751
  · exact B1850755
  · exact B1850759
  · exact B1850763
  · exact B1850767
  · exact B1850771
  · exact B1850775
  · exact B1850779
  · exact B1850783
  · exact B1850787
  · exact B1850791
  · exact B1850795
  · exact B1850799
  · exact B1850803
  · exact B1850807
  · exact B1850811
  · exact B1850815
  · exact B1850819
  · exact B1850823
  · exact B1850827
  · exact B1850831
  · exact B1850835
  · exact B1850839
  · exact B1850843
  · exact B1850847
  · exact B1850851
  · exact B1850855
  · exact B1850859
  · exact B1850863
  · exact B1850867
  · exact B1850871
  · exact B1850875
  · exact B1850879
  · exact B1850883
  · exact B1850887
  · exact B1850891
  · exact B1850895
  · exact B1850899
  · exact B1850903
  · exact B1850907
  · exact B1850911
  · exact B1850915
  · exact B1850919
  · exact B1850923
  · exact B1850927
  · exact B1850931
  · exact B1850935
  · exact B1850939
  · exact B1850943
  · exact B1850947
  · exact B1850951
  · exact B1850955
  · exact B1850959
  · exact B1850963
  · exact B1850967
  · exact B1850971
  · exact B1850975
  · exact B1850979
  · exact B1850983
  · exact B1850987
  · exact B1850991
  · exact B1850995
  · exact B1850999
  · exact B1851003
  · exact B1851007
  · exact B1851011
  · exact B1851015
  · exact B1851019
  · exact B1851023
  · exact B1851027
  · exact B1851031
  · exact B1851035
  · exact B1851039
  · exact B1851043
  · exact B1851047
  · exact B1851051
  · exact B1851055
  · exact B1851059
  · exact B1851063
  · exact B1851067
  · exact B1851071
  · exact B1851075
  · exact B1851079
  · exact B1851083
  · exact B1851087
  · exact B1851091
  · exact B1851095
  · exact B1851099
  · exact B1851103
  · exact B1851107
  · exact B1851111
  · exact B1851115
  · exact B1851119
  · exact B1851123
  · exact B1851127
  · exact B1851131
  · exact B1851135
  · exact B1851139
  · exact B1851143
  · exact B1851147
  · exact B1851151
  · exact B1851155
  · exact B1851159
  · exact B1851163
  · exact B1851167
  · exact B1851171
  · exact B1851175
  · exact B1851179
  · exact B1851183
  · exact B1851187
  · exact B1851191
  · exact B1851195
  · exact B1851199
  · exact B1851203
  · exact B1851207
  · exact B1851211
  · exact B1851215
  · exact B1851219
  · exact B1851223
  · exact B1851227
  · exact B1851231
  · exact B1851235
  · exact B1851239
  · exact B1851243
  · exact B1851247
  · exact B1851251
  · exact B1851255
  · exact B1851259
  · exact B1851263
  · exact B1851267
  · exact B1851271
  · exact B1851275
  · exact B1851279
  · exact B1851283
  · exact B1851287
  · exact B1851291
  · exact B1851295
  · exact B1851299
  · exact B1851303
  · exact B1851307
  · exact B1851311
  · exact B1851315
  · exact B1851319
  · exact B1851323
  · exact B1851327
  · exact B1851331
  · exact B1851335
  · exact B1851339
  · exact B1851343
  · exact B1851347
  · exact B1851351
  · exact B1851355
  · exact B1851359
  · exact B1851363
  · exact B1851367
  · exact B1851371
  · exact B1851375
  · exact B1851379
  · exact B1851383
  · exact B1851387
  · exact B1851391
  · exact B1851395
  · exact B1851399
  · exact B1851403
  · exact B1851407
  · exact B1851411
  · exact B1851415
  · exact B1851419
  · exact B1851423
  · exact B1851427
  · exact B1851431
  · exact B1851435
  · exact B1851439
  · exact B1851443
  · exact B1851447
  · exact B1851451
  · exact B1851455
  · exact B1851459
  · exact B1851463
  · exact B1851467
  · exact B1851471
  · exact B1851475
  · exact B1851479
  · exact B1851483
  · exact B1851487
  · exact B1851491
  · exact B1851495
  · exact B1851499
  · exact B1851503
  · exact B1851507
  · exact B1851511
  · exact B1851515
  · exact B1851519
  · exact B1851523
  · exact B1851527
  · exact B1851531
  · exact B1851535
  · exact B1851539
  · exact B1851543
  · exact B1851547
  · exact B1851551
  · exact B1851555
  · exact B1851559
  · exact B1851563
  · exact B1851567
  · exact B1851571
  · exact B1851575
  · exact B1851579
  · exact B1851583
  · exact B1851587
  · exact B1851591
  · exact B1851595
  · exact B1851599
  · exact B1851603
  · exact B1851607
  · exact B1851611
  · exact B1851615
  · exact B1851619
  · exact B1851623

theorem solution (m : ℕ) (hlo : 1849626 ≤ m) (hhi : m ≤ 1851626) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 462406 ≤ j := by omega
    have hj2 : j ≤ 462905 := by omega
    have hb : Blo 1849626 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
