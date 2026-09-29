-- Prove2me | solution 1 for syracuse_descends_range_295830_299830
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:18.649655+00:00
-- url     : https://prove2.me/submissions/637471a9-0afc-4952-9d12-254a0a0ac14d

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


theorem B753725 : Blo 295830 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B852133 : Blo 295830 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B2162933 : Blo 295830 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B1507733 : Blo 295830 1507733 := bbase (se 6 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 1507733 = 70675) (by norm_num)
theorem B754069 : Blo 295830 754069 := bbase (se 6 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 754069 = 35347) (by norm_num)
theorem B426397 : Blo 295830 426397 := bbase (se 3 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 426397 = 159899) (by norm_num)
theorem B688589 : Blo 295830 688589 := bbase (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) (by norm_num)
theorem B557533 : Blo 295830 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B754181 : Blo 295830 754181 := bbase (se 4 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 754181 = 141409) (by norm_num)
theorem B950885 : Blo 295830 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B754373 : Blo 295830 754373 := bbase (se 4 (by rfl) ⟨70722, by rfl⟩ : syracuseStep 754373 = 141445) (by norm_num)
theorem B754717 : Blo 295830 754717 := bbase (se 3 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 754717 = 283019) (by norm_num)
theorem B754829 : Blo 295830 754829 := bbase (se 3 (by rfl) ⟨141530, by rfl⟩ : syracuseStep 754829 = 283061) (by norm_num)
theorem B722117 : Blo 295830 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B755021 : Blo 295830 755021 := bbase (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) (by norm_num)
theorem B2557493 : Blo 295830 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B1509029 : Blo 295830 1509029 := bbase (se 4 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 1509029 = 282943) (by norm_num)
theorem B755365 : Blo 295830 755365 := bbase (se 4 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 755365 = 141631) (by norm_num)
theorem B755477 : Blo 295830 755477 := bbase (se 6 (by rfl) ⟨17706, by rfl⟩ : syracuseStep 755477 = 35413) (by norm_num)
theorem B952165 : Blo 295830 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B755669 : Blo 295830 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B526357 : Blo 295830 526357 := bbase (se 6 (by rfl) ⟨12336, by rfl⟩ : syracuseStep 526357 = 24673) (by norm_num)
theorem B756013 : Blo 295830 756013 := bbase (se 3 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 756013 = 283505) (by norm_num)
theorem B3410261 : Blo 295830 3410261 := bbase (se 10 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 3410261 = 9991) (by norm_num)
theorem B756125 : Blo 295830 756125 := bbase (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) (by norm_num)
theorem B1018325 : Blo 295830 1018325 := bbase (se 7 (by rfl) ⟨11933, by rfl⟩ : syracuseStep 1018325 = 23867) (by norm_num)
theorem B1706453 : Blo 295830 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B756317 : Blo 295830 756317 := bbase (se 3 (by rfl) ⟨141809, by rfl⟩ : syracuseStep 756317 = 283619) (by norm_num)
theorem B1510325 : Blo 295830 1510325 := bbase (se 5 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 1510325 = 141593) (by norm_num)
theorem B756661 : Blo 295830 756661 := bbase (se 5 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 756661 = 70937) (by norm_num)
theorem B756773 : Blo 295830 756773 := bbase (se 4 (by rfl) ⟨70947, by rfl⟩ : syracuseStep 756773 = 141895) (by norm_num)
theorem B953525 : Blo 295830 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B756965 : Blo 295830 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B953653 : Blo 295830 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B953909 : Blo 295830 953909 := bbase (se 5 (by rfl) ⟨44714, by rfl⟩ : syracuseStep 953909 = 89429) (by norm_num)
theorem B757309 : Blo 295830 757309 := bbase (se 3 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 757309 = 283991) (by norm_num)
theorem B757421 : Blo 295830 757421 := bbase (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) (by norm_num)
theorem B1904309 : Blo 295830 1904309 := bbase (se 5 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 1904309 = 178529) (by norm_num)
theorem B757613 : Blo 295830 757613 := bbase (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) (by norm_num)
theorem B856165 : Blo 295830 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B1511621 : Blo 295830 1511621 := bbase (se 4 (by rfl) ⟨141714, by rfl⟩ : syracuseStep 1511621 = 283429) (by norm_num)
theorem B757957 : Blo 295830 757957 := bbase (se 4 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 757957 = 142117) (by norm_num)
theorem B758069 : Blo 295830 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B758261 : Blo 295830 758261 := bbase (se 5 (by rfl) ⟨35543, by rfl⟩ : syracuseStep 758261 = 71087) (by norm_num)
theorem B1282565 : Blo 295830 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B561725 : Blo 295830 561725 := bbase (se 3 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 561725 = 210647) (by norm_num)
theorem B1151653 : Blo 295830 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B725701 : Blo 295830 725701 := bbase (se 4 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 725701 = 136069) (by norm_num)
theorem B758605 : Blo 295830 758605 := bbase (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) (by norm_num)
theorem B758717 : Blo 295830 758717 := bbase (se 3 (by rfl) ⟨142259, by rfl⟩ : syracuseStep 758717 = 284519) (by norm_num)
theorem B726013 : Blo 295830 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B332833 : Blo 295830 332833 := bbase (se 2 (by rfl) ⟨124812, by rfl⟩ : syracuseStep 332833 = 249625) (by norm_num)
theorem B332869 : Blo 295830 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B300133 : Blo 295830 300133 := bbase (se 4 (by rfl) ⟨28137, by rfl⟩ : syracuseStep 300133 = 56275) (by norm_num)
theorem B332905 : Blo 295830 332905 := bbase (se 2 (by rfl) ⟨124839, by rfl⟩ : syracuseStep 332905 = 249679) (by norm_num)
theorem B758909 : Blo 295830 758909 := bbase (se 3 (by rfl) ⟨142295, by rfl⟩ : syracuseStep 758909 = 284591) (by norm_num)
theorem B332941 : Blo 295830 332941 := bbase (se 3 (by rfl) ⟨62426, by rfl⟩ : syracuseStep 332941 = 124853) (by norm_num)
theorem B332977 : Blo 295830 332977 := bbase (se 2 (by rfl) ⟨124866, by rfl⟩ : syracuseStep 332977 = 249733) (by norm_num)
theorem B300217 : Blo 295830 300217 := bbase (se 2 (by rfl) ⟨112581, by rfl⟩ : syracuseStep 300217 = 225163) (by norm_num)
theorem B333013 : Blo 295830 333013 := bbase (se 7 (by rfl) ⟨3902, by rfl⟩ : syracuseStep 333013 = 7805) (by norm_num)
theorem B333049 : Blo 295830 333049 := bbase (se 2 (by rfl) ⟨124893, by rfl⟩ : syracuseStep 333049 = 249787) (by norm_num)
theorem B333085 : Blo 295830 333085 := bbase (se 3 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 333085 = 124907) (by norm_num)
theorem B562477 : Blo 295830 562477 := bbase (se 3 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 562477 = 210929) (by norm_num)
theorem B333121 : Blo 295830 333121 := bbase (se 2 (by rfl) ⟨124920, by rfl⟩ : syracuseStep 333121 = 249841) (by norm_num)
theorem B333157 : Blo 295830 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B333193 : Blo 295830 333193 := bbase (se 2 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 333193 = 249895) (by norm_num)
theorem B333229 : Blo 295830 333229 := bbase (se 3 (by rfl) ⟨62480, by rfl⟩ : syracuseStep 333229 = 124961) (by norm_num)
theorem B562621 : Blo 295830 562621 := bbase (se 3 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 562621 = 210983) (by norm_num)
theorem B300493 : Blo 295830 300493 := bbase (se 3 (by rfl) ⟨56342, by rfl⟩ : syracuseStep 300493 = 112685) (by norm_num)
theorem B333265 : Blo 295830 333265 := bbase (se 2 (by rfl) ⟨124974, by rfl⟩ : syracuseStep 333265 = 249949) (by norm_num)
theorem B1512917 : Blo 295830 1512917 := bbase (se 7 (by rfl) ⟨17729, by rfl⟩ : syracuseStep 1512917 = 35459) (by norm_num)
theorem B333301 : Blo 295830 333301 := bbase (se 5 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 333301 = 31247) (by norm_num)
theorem B333337 : Blo 295830 333337 := bbase (se 2 (by rfl) ⟨125001, by rfl⟩ : syracuseStep 333337 = 250003) (by norm_num)
theorem B333373 : Blo 295830 333373 := bbase (se 3 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 333373 = 125015) (by norm_num)
theorem B562781 : Blo 295830 562781 := bbase (se 3 (by rfl) ⟨105521, by rfl⟩ : syracuseStep 562781 = 211043) (by norm_num)
theorem B333409 : Blo 295830 333409 := bbase (se 2 (by rfl) ⟨125028, by rfl⟩ : syracuseStep 333409 = 250057) (by norm_num)
theorem B333445 : Blo 295830 333445 := bbase (se 4 (by rfl) ⟨31260, by rfl⟩ : syracuseStep 333445 = 62521) (by norm_num)
theorem B333481 : Blo 295830 333481 := bbase (se 2 (by rfl) ⟨125055, by rfl⟩ : syracuseStep 333481 = 250111) (by norm_num)
theorem B333517 : Blo 295830 333517 := bbase (se 3 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 333517 = 125069) (by norm_num)
theorem B1218277 : Blo 295830 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B562925 : Blo 295830 562925 := bbase (se 3 (by rfl) ⟨105548, by rfl⟩ : syracuseStep 562925 = 211097) (by norm_num)
theorem B333553 : Blo 295830 333553 := bbase (se 2 (by rfl) ⟨125082, by rfl⟩ : syracuseStep 333553 = 250165) (by norm_num)
theorem B333589 : Blo 295830 333589 := bbase (se 6 (by rfl) ⟨7818, by rfl⟩ : syracuseStep 333589 = 15637) (by norm_num)
theorem B333625 : Blo 295830 333625 := bbase (se 2 (by rfl) ⟨125109, by rfl⟩ : syracuseStep 333625 = 250219) (by norm_num)
theorem B333661 : Blo 295830 333661 := bbase (se 3 (by rfl) ⟨62561, by rfl⟩ : syracuseStep 333661 = 125123) (by norm_num)
theorem B333697 : Blo 295830 333697 := bbase (se 2 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 333697 = 250273) (by norm_num)
theorem B333733 : Blo 295830 333733 := bbase (se 4 (by rfl) ⟨31287, by rfl⟩ : syracuseStep 333733 = 62575) (by norm_num)
theorem B956357 : Blo 295830 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B333769 : Blo 295830 333769 := bbase (se 2 (by rfl) ⟨125163, by rfl⟩ : syracuseStep 333769 = 250327) (by norm_num)
theorem B366557 : Blo 295830 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B333805 : Blo 295830 333805 := bbase (se 3 (by rfl) ⟨62588, by rfl⟩ : syracuseStep 333805 = 125177) (by norm_num)
theorem B563213 : Blo 295830 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B333841 : Blo 295830 333841 := bbase (se 2 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 333841 = 250381) (by norm_num)
theorem B333877 : Blo 295830 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B2267189 : Blo 295830 2267189 := bbase (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) (by norm_num)
theorem B333913 : Blo 295830 333913 := bbase (se 2 (by rfl) ⟨125217, by rfl⟩ : syracuseStep 333913 = 250435) (by norm_num)
theorem B333949 : Blo 295830 333949 := bbase (se 3 (by rfl) ⟨62615, by rfl⟩ : syracuseStep 333949 = 125231) (by norm_num)
theorem B333985 : Blo 295830 333985 := bbase (se 2 (by rfl) ⟨125244, by rfl⟩ : syracuseStep 333985 = 250489) (by norm_num)
theorem B563365 : Blo 295830 563365 := bbase (se 4 (by rfl) ⟨52815, by rfl⟩ : syracuseStep 563365 = 105631) (by norm_num)
theorem B334021 : Blo 295830 334021 := bbase (se 4 (by rfl) ⟨31314, by rfl⟩ : syracuseStep 334021 = 62629) (by norm_num)
theorem B334057 : Blo 295830 334057 := bbase (se 2 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 334057 = 250543) (by norm_num)
theorem B334093 : Blo 295830 334093 := bbase (se 3 (by rfl) ⟨62642, by rfl⟩ : syracuseStep 334093 = 125285) (by norm_num)
theorem B334129 : Blo 295830 334129 := bbase (se 2 (by rfl) ⟨125298, by rfl⟩ : syracuseStep 334129 = 250597) (by norm_num)
theorem B334165 : Blo 295830 334165 := bbase (se 10 (by rfl) ⟨489, by rfl⟩ : syracuseStep 334165 = 979) (by norm_num)
theorem B432469 : Blo 295830 432469 := bbase (se 10 (by rfl) ⟨633, by rfl⟩ : syracuseStep 432469 = 1267) (by norm_num)
theorem B334201 : Blo 295830 334201 := bbase (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) (by norm_num)
theorem B334237 : Blo 295830 334237 := bbase (se 3 (by rfl) ⟨62669, by rfl⟩ : syracuseStep 334237 = 125339) (by norm_num)
theorem B334273 : Blo 295830 334273 := bbase (se 2 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 334273 = 250705) (by norm_num)
theorem B563669 : Blo 295830 563669 := bbase (se 7 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 563669 = 13211) (by norm_num)
theorem B334309 : Blo 295830 334309 := bbase (se 4 (by rfl) ⟨31341, by rfl⟩ : syracuseStep 334309 = 62683) (by norm_num)
theorem B334345 : Blo 295830 334345 := bbase (se 2 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 334345 = 250759) (by norm_num)
theorem B334381 : Blo 295830 334381 := bbase (se 3 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 334381 = 125393) (by norm_num)
theorem B301645 : Blo 295830 301645 := bbase (se 3 (by rfl) ⟨56558, by rfl⟩ : syracuseStep 301645 = 113117) (by norm_num)
theorem B334417 : Blo 295830 334417 := bbase (se 2 (by rfl) ⟨125406, by rfl⟩ : syracuseStep 334417 = 250813) (by norm_num)
theorem B334453 : Blo 295830 334453 := bbase (se 5 (by rfl) ⟨15677, by rfl⟩ : syracuseStep 334453 = 31355) (by norm_num)
theorem B334489 : Blo 295830 334489 := bbase (se 2 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 334489 = 250867) (by norm_num)
theorem B1612469 : Blo 295830 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B334525 : Blo 295830 334525 := bbase (se 3 (by rfl) ⟨62723, by rfl⟩ : syracuseStep 334525 = 125447) (by norm_num)
theorem B334561 : Blo 295830 334561 := bbase (se 2 (by rfl) ⟨125460, by rfl⟩ : syracuseStep 334561 = 250921) (by norm_num)
theorem B1514213 : Blo 295830 1514213 := bbase (se 4 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 1514213 = 283915) (by norm_num)
theorem B334597 : Blo 295830 334597 := bbase (se 4 (by rfl) ⟨31368, by rfl⟩ : syracuseStep 334597 = 62737) (by norm_num)
theorem B334633 : Blo 295830 334633 := bbase (se 2 (by rfl) ⟨125487, by rfl⟩ : syracuseStep 334633 = 250975) (by norm_num)
theorem B1907509 : Blo 295830 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B334669 : Blo 295830 334669 := bbase (se 3 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 334669 = 125501) (by norm_num)
theorem B334705 : Blo 295830 334705 := bbase (se 2 (by rfl) ⟨125514, by rfl⟩ : syracuseStep 334705 = 251029) (by norm_num)
theorem B334741 : Blo 295830 334741 := bbase (se 6 (by rfl) ⟨7845, by rfl⟩ : syracuseStep 334741 = 15691) (by norm_num)
theorem B334777 : Blo 295830 334777 := bbase (se 2 (by rfl) ⟨125541, by rfl⟩ : syracuseStep 334777 = 251083) (by norm_num)
theorem B334813 : Blo 295830 334813 := bbase (se 3 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 334813 = 125555) (by norm_num)
theorem B695285 : Blo 295830 695285 := bbase (se 5 (by rfl) ⟨32591, by rfl⟩ : syracuseStep 695285 = 65183) (by norm_num)
theorem B334849 : Blo 295830 334849 := bbase (se 2 (by rfl) ⟨125568, by rfl⟩ : syracuseStep 334849 = 251137) (by norm_num)
theorem B334885 : Blo 295830 334885 := bbase (se 4 (by rfl) ⟨31395, by rfl⟩ : syracuseStep 334885 = 62791) (by norm_num)
theorem B334921 : Blo 295830 334921 := bbase (se 2 (by rfl) ⟨125595, by rfl⟩ : syracuseStep 334921 = 251191) (by norm_num)
theorem B334957 : Blo 295830 334957 := bbase (se 3 (by rfl) ⟨62804, by rfl⟩ : syracuseStep 334957 = 125609) (by norm_num)
theorem B302221 : Blo 295830 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B334993 : Blo 295830 334993 := bbase (se 2 (by rfl) ⟨125622, by rfl⟩ : syracuseStep 334993 = 251245) (by norm_num)
theorem B335029 : Blo 295830 335029 := bbase (se 5 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 335029 = 31409) (by norm_num)
theorem B564421 : Blo 295830 564421 := bbase (se 4 (by rfl) ⟨52914, by rfl⟩ : syracuseStep 564421 = 105829) (by norm_num)
theorem B302293 : Blo 295830 302293 := bbase (se 7 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 302293 = 7085) (by norm_num)
theorem B335065 : Blo 295830 335065 := bbase (se 2 (by rfl) ⟨125649, by rfl⟩ : syracuseStep 335065 = 251299) (by norm_num)
theorem B335101 : Blo 295830 335101 := bbase (se 3 (by rfl) ⟨62831, by rfl⟩ : syracuseStep 335101 = 125663) (by norm_num)
theorem B957701 : Blo 295830 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B335137 : Blo 295830 335137 := bbase (se 2 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 335137 = 251353) (by norm_num)
theorem B335173 : Blo 295830 335173 := bbase (se 4 (by rfl) ⟨31422, by rfl⟩ : syracuseStep 335173 = 62845) (by norm_num)
theorem B564565 : Blo 295830 564565 := bbase (se 11 (by rfl) ⟨413, by rfl⟩ : syracuseStep 564565 = 827) (by norm_num)
theorem B335209 : Blo 295830 335209 := bbase (se 2 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 335209 = 251407) (by norm_num)
theorem B335245 : Blo 295830 335245 := bbase (se 3 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 335245 = 125717) (by norm_num)
theorem B335281 : Blo 295830 335281 := bbase (se 2 (by rfl) ⟨125730, by rfl⟩ : syracuseStep 335281 = 251461) (by norm_num)
theorem B335317 : Blo 295830 335317 := bbase (se 7 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 335317 = 7859) (by norm_num)
theorem B2137589 : Blo 295830 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B564725 : Blo 295830 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B335353 : Blo 295830 335353 := bbase (se 2 (by rfl) ⟨125757, by rfl⟩ : syracuseStep 335353 = 251515) (by norm_num)
theorem B335389 : Blo 295830 335389 := bbase (se 3 (by rfl) ⟨62885, by rfl⟩ : syracuseStep 335389 = 125771) (by norm_num)
theorem B335425 : Blo 295830 335425 := bbase (se 2 (by rfl) ⟨125784, by rfl⟩ : syracuseStep 335425 = 251569) (by norm_num)
theorem B499277 : Blo 295830 499277 := bbase (se 3 (by rfl) ⟨93614, by rfl⟩ : syracuseStep 499277 = 187229) (by norm_num)
theorem B335461 : Blo 295830 335461 := bbase (se 4 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 335461 = 62899) (by norm_num)
theorem B564869 : Blo 295830 564869 := bbase (se 4 (by rfl) ⟨52956, by rfl⟩ : syracuseStep 564869 = 105913) (by norm_num)
theorem B335497 : Blo 295830 335497 := bbase (se 2 (by rfl) ⟨125811, by rfl⟩ : syracuseStep 335497 = 251623) (by norm_num)
theorem B1023637 : Blo 295830 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B335533 : Blo 295830 335533 := bbase (se 3 (by rfl) ⟨62912, by rfl⟩ : syracuseStep 335533 = 125825) (by norm_num)
theorem B499405 : Blo 295830 499405 := bbase (se 3 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 499405 = 187277) (by norm_num)
theorem B335569 : Blo 295830 335569 := bbase (se 2 (by rfl) ⟨125838, by rfl⟩ : syracuseStep 335569 = 251677) (by norm_num)
theorem B335605 : Blo 295830 335605 := bbase (se 5 (by rfl) ⟨15731, by rfl⟩ : syracuseStep 335605 = 31463) (by norm_num)
theorem B335641 : Blo 295830 335641 := bbase (se 2 (by rfl) ⟨125865, by rfl⟩ : syracuseStep 335641 = 251731) (by norm_num)
theorem B499493 : Blo 295830 499493 := bbase (se 4 (by rfl) ⟨46827, by rfl⟩ : syracuseStep 499493 = 93655) (by norm_num)
theorem B335677 : Blo 295830 335677 := bbase (se 3 (by rfl) ⟨62939, by rfl⟩ : syracuseStep 335677 = 125879) (by norm_num)
theorem B335713 : Blo 295830 335713 := bbase (se 2 (by rfl) ⟨125892, by rfl⟩ : syracuseStep 335713 = 251785) (by norm_num)
theorem B335749 : Blo 295830 335749 := bbase (se 4 (by rfl) ⟨31476, by rfl⟩ : syracuseStep 335749 = 62953) (by norm_num)
theorem B499621 : Blo 295830 499621 := bbase (se 4 (by rfl) ⟨46839, by rfl⟩ : syracuseStep 499621 = 93679) (by norm_num)
theorem B565157 : Blo 295830 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B335785 : Blo 295830 335785 := bbase (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) (by norm_num)
theorem B335821 : Blo 295830 335821 := bbase (se 3 (by rfl) ⟨62966, by rfl⟩ : syracuseStep 335821 = 125933) (by norm_num)
theorem B335857 : Blo 295830 335857 := bbase (se 2 (by rfl) ⟨125946, by rfl⟩ : syracuseStep 335857 = 251893) (by norm_num)
theorem B1515509 : Blo 295830 1515509 := bbase (se 5 (by rfl) ⟨71039, by rfl⟩ : syracuseStep 1515509 = 142079) (by norm_num)
theorem B499709 : Blo 295830 499709 := bbase (se 3 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 499709 = 187391) (by norm_num)
theorem B335893 : Blo 295830 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B335929 : Blo 295830 335929 := bbase (se 2 (by rfl) ⟨125973, by rfl⟩ : syracuseStep 335929 = 251947) (by norm_num)
theorem B565309 : Blo 295830 565309 := bbase (se 3 (by rfl) ⟨105995, by rfl⟩ : syracuseStep 565309 = 211991) (by norm_num)
theorem B335965 : Blo 295830 335965 := bbase (se 3 (by rfl) ⟨62993, by rfl⟩ : syracuseStep 335965 = 125987) (by norm_num)
theorem B1351781 : Blo 295830 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B499837 : Blo 295830 499837 := bbase (se 3 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 499837 = 187439) (by norm_num)
theorem B336001 : Blo 295830 336001 := bbase (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) (by norm_num)
theorem B336037 : Blo 295830 336037 := bbase (se 4 (by rfl) ⟨31503, by rfl⟩ : syracuseStep 336037 = 63007) (by norm_num)
theorem B336073 : Blo 295830 336073 := bbase (se 2 (by rfl) ⟨126027, by rfl⟩ : syracuseStep 336073 = 252055) (by norm_num)
theorem B499925 : Blo 295830 499925 := bbase (se 7 (by rfl) ⟨5858, by rfl⟩ : syracuseStep 499925 = 11717) (by norm_num)
theorem B4923605 : Blo 295830 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B336109 : Blo 295830 336109 := bbase (se 3 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 336109 = 126041) (by norm_num)
theorem B336145 : Blo 295830 336145 := bbase (se 2 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 336145 = 252109) (by norm_num)
theorem B336181 : Blo 295830 336181 := bbase (se 5 (by rfl) ⟨15758, by rfl⟩ : syracuseStep 336181 = 31517) (by norm_num)
theorem B303421 : Blo 295830 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B500053 : Blo 295830 500053 := bbase (se 10 (by rfl) ⟨732, by rfl⟩ : syracuseStep 500053 = 1465) (by norm_num)
theorem B336217 : Blo 295830 336217 := bbase (se 2 (by rfl) ⟨126081, by rfl⟩ : syracuseStep 336217 = 252163) (by norm_num)
theorem B565613 : Blo 295830 565613 := bbase (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) (by norm_num)
theorem B336253 : Blo 295830 336253 := bbase (se 3 (by rfl) ⟨63047, by rfl⟩ : syracuseStep 336253 = 126095) (by norm_num)
theorem B336289 : Blo 295830 336289 := bbase (se 2 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 336289 = 252217) (by norm_num)
theorem B500141 : Blo 295830 500141 := bbase (se 3 (by rfl) ⟨93776, by rfl⟩ : syracuseStep 500141 = 187553) (by norm_num)
theorem B860597 : Blo 295830 860597 := bbase (se 5 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 860597 = 80681) (by norm_num)
theorem B336325 : Blo 295830 336325 := bbase (se 4 (by rfl) ⟨31530, by rfl⟩ : syracuseStep 336325 = 63061) (by norm_num)
theorem B5743061 : Blo 295830 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B336361 : Blo 295830 336361 := bbase (se 2 (by rfl) ⟨126135, by rfl⟩ : syracuseStep 336361 = 252271) (by norm_num)
theorem B336397 : Blo 295830 336397 := bbase (se 3 (by rfl) ⟨63074, by rfl⟩ : syracuseStep 336397 = 126149) (by norm_num)
theorem B500269 : Blo 295830 500269 := bbase (se 3 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 500269 = 187601) (by norm_num)
theorem B336433 : Blo 295830 336433 := bbase (se 2 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 336433 = 252325) (by norm_num)
theorem B336469 : Blo 295830 336469 := bbase (se 8 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 336469 = 3943) (by norm_num)
theorem B336505 : Blo 295830 336505 := bbase (se 2 (by rfl) ⟨126189, by rfl⟩ : syracuseStep 336505 = 252379) (by norm_num)
theorem B500357 : Blo 295830 500357 := bbase (se 4 (by rfl) ⟨46908, by rfl⟩ : syracuseStep 500357 = 93817) (by norm_num)
theorem B303769 : Blo 295830 303769 := bbase (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) (by norm_num)
theorem B336541 : Blo 295830 336541 := bbase (se 3 (by rfl) ⟨63101, by rfl⟩ : syracuseStep 336541 = 126203) (by norm_num)
theorem B336577 : Blo 295830 336577 := bbase (se 2 (by rfl) ⟨126216, by rfl⟩ : syracuseStep 336577 = 252433) (by norm_num)
theorem B336613 : Blo 295830 336613 := bbase (se 4 (by rfl) ⟨31557, by rfl⟩ : syracuseStep 336613 = 63115) (by norm_num)
theorem B500485 : Blo 295830 500485 := bbase (se 4 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 500485 = 93841) (by norm_num)
theorem B336649 : Blo 295830 336649 := bbase (se 2 (by rfl) ⟨126243, by rfl⟩ : syracuseStep 336649 = 252487) (by norm_num)
theorem B2564885 : Blo 295830 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B336685 : Blo 295830 336685 := bbase (se 3 (by rfl) ⟨63128, by rfl⟩ : syracuseStep 336685 = 126257) (by norm_num)
theorem B336721 : Blo 295830 336721 := bbase (se 2 (by rfl) ⟨126270, by rfl⟩ : syracuseStep 336721 = 252541) (by norm_num)
theorem B500573 : Blo 295830 500573 := bbase (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) (by norm_num)
theorem B336757 : Blo 295830 336757 := bbase (se 5 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 336757 = 31571) (by norm_num)
theorem B336793 : Blo 295830 336793 := bbase (se 2 (by rfl) ⟨126297, by rfl⟩ : syracuseStep 336793 = 252595) (by norm_num)
theorem B1123253 : Blo 295830 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B336829 : Blo 295830 336829 := bbase (se 3 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 336829 = 126311) (by norm_num)
theorem B1352645 : Blo 295830 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B500701 : Blo 295830 500701 := bbase (se 3 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 500701 = 187763) (by norm_num)
theorem B336865 : Blo 295830 336865 := bbase (se 2 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 336865 = 252649) (by norm_num)
theorem B336901 : Blo 295830 336901 := bbase (se 4 (by rfl) ⟨31584, by rfl⟩ : syracuseStep 336901 = 63169) (by norm_num)
theorem B336937 : Blo 295830 336937 := bbase (se 2 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 336937 = 252703) (by norm_num)
theorem B500789 : Blo 295830 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B336973 : Blo 295830 336973 := bbase (se 3 (by rfl) ⟨63182, by rfl⟩ : syracuseStep 336973 = 126365) (by norm_num)
theorem B566365 : Blo 295830 566365 := bbase (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) (by norm_num)
theorem B337009 : Blo 295830 337009 := bbase (se 2 (by rfl) ⟨126378, by rfl⟩ : syracuseStep 337009 = 252757) (by norm_num)
theorem B337045 : Blo 295830 337045 := bbase (se 6 (by rfl) ⟨7899, by rfl⟩ : syracuseStep 337045 = 15799) (by norm_num)
theorem B500917 : Blo 295830 500917 := bbase (se 5 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 500917 = 46961) (by norm_num)
theorem B337081 : Blo 295830 337081 := bbase (se 2 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 337081 = 252811) (by norm_num)
theorem B1123541 : Blo 295830 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B959701 : Blo 295830 959701 := bbase (se 7 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 959701 = 22493) (by norm_num)
theorem B337117 : Blo 295830 337117 := bbase (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) (by norm_num)
theorem B1352933 : Blo 295830 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B566509 : Blo 295830 566509 := bbase (se 3 (by rfl) ⟨106220, by rfl⟩ : syracuseStep 566509 = 212441) (by norm_num)
theorem B337153 : Blo 295830 337153 := bbase (se 2 (by rfl) ⟨126432, by rfl⟩ : syracuseStep 337153 = 252865) (by norm_num)
theorem B1516805 : Blo 295830 1516805 := bbase (se 4 (by rfl) ⟨142200, by rfl⟩ : syracuseStep 1516805 = 284401) (by norm_num)
theorem B501005 : Blo 295830 501005 := bbase (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) (by norm_num)
theorem B337189 : Blo 295830 337189 := bbase (se 4 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 337189 = 63223) (by norm_num)
theorem B337225 : Blo 295830 337225 := bbase (se 2 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 337225 = 252919) (by norm_num)
theorem B337261 : Blo 295830 337261 := bbase (se 3 (by rfl) ⟨63236, by rfl⟩ : syracuseStep 337261 = 126473) (by norm_num)
theorem B501133 : Blo 295830 501133 := bbase (se 3 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 501133 = 187925) (by norm_num)
theorem B566669 : Blo 295830 566669 := bbase (se 3 (by rfl) ⟨106250, by rfl⟩ : syracuseStep 566669 = 212501) (by norm_num)
theorem B337297 : Blo 295830 337297 := bbase (se 2 (by rfl) ⟨126486, by rfl⟩ : syracuseStep 337297 = 252973) (by norm_num)
theorem B2139605 : Blo 295830 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2041301 : Blo 295830 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B501221 : Blo 295830 501221 := bbase (se 4 (by rfl) ⟨46989, by rfl⟩ : syracuseStep 501221 = 93979) (by norm_num)
theorem B5416469 : Blo 295830 5416469 := bbase (se 6 (by rfl) ⟨126948, by rfl⟩ : syracuseStep 5416469 = 253897) (by norm_num)
theorem B566813 : Blo 295830 566813 := bbase (se 3 (by rfl) ⟨106277, by rfl⟩ : syracuseStep 566813 = 212555) (by norm_num)
theorem B501349 : Blo 295830 501349 := bbase (se 4 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 501349 = 94003) (by norm_num)
theorem B632453 : Blo 295830 632453 := bbase (se 4 (by rfl) ⟨59292, by rfl⟩ : syracuseStep 632453 = 118585) (by norm_num)
theorem B534181 : Blo 295830 534181 := bbase (se 4 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 534181 = 100159) (by norm_num)
theorem B501437 : Blo 295830 501437 := bbase (se 3 (by rfl) ⟨94019, by rfl⟩ : syracuseStep 501437 = 188039) (by norm_num)
theorem B861941 : Blo 295830 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B501565 : Blo 295830 501565 := bbase (se 3 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 501565 = 188087) (by norm_num)
theorem B567101 : Blo 295830 567101 := bbase (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) (by norm_num)
theorem B632693 : Blo 295830 632693 := bbase (se 5 (by rfl) ⟨29657, by rfl⟩ : syracuseStep 632693 = 59315) (by norm_num)
theorem B501653 : Blo 295830 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B600005 : Blo 295830 600005 := bbase (se 4 (by rfl) ⟨56250, by rfl⟩ : syracuseStep 600005 = 112501) (by norm_num)
theorem B567253 : Blo 295830 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B665621 : Blo 295830 665621 := bbase (se 6 (by rfl) ⟨15600, by rfl⟩ : syracuseStep 665621 = 31201) (by norm_num)
theorem B501781 : Blo 295830 501781 := bbase (se 6 (by rfl) ⟨11760, by rfl⟩ : syracuseStep 501781 = 23521) (by norm_num)
theorem B665693 : Blo 295830 665693 := bbase (se 3 (by rfl) ⟨124817, by rfl⟩ : syracuseStep 665693 = 249635) (by norm_num)
theorem B501869 : Blo 295830 501869 := bbase (se 3 (by rfl) ⟨94100, by rfl⟩ : syracuseStep 501869 = 188201) (by norm_num)
theorem B665765 : Blo 295830 665765 := bbase (se 4 (by rfl) ⟨62415, by rfl⟩ : syracuseStep 665765 = 124831) (by norm_num)
theorem B665837 : Blo 295830 665837 := bbase (se 3 (by rfl) ⟨124844, by rfl⟩ : syracuseStep 665837 = 249689) (by norm_num)
theorem B501997 : Blo 295830 501997 := bbase (se 3 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 501997 = 188249) (by norm_num)
theorem B567557 : Blo 295830 567557 := bbase (se 4 (by rfl) ⟨53208, by rfl⟩ : syracuseStep 567557 = 106417) (by norm_num)
theorem B665909 : Blo 295830 665909 := bbase (se 5 (by rfl) ⟨31214, by rfl⟩ : syracuseStep 665909 = 62429) (by norm_num)
theorem B502085 : Blo 295830 502085 := bbase (se 4 (by rfl) ⟨47070, by rfl⟩ : syracuseStep 502085 = 94141) (by norm_num)
theorem B633197 : Blo 295830 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B1124725 : Blo 295830 1124725 := bbase (se 5 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 1124725 = 105443) (by norm_num)
theorem B633205 : Blo 295830 633205 := bbase (se 5 (by rfl) ⟨29681, by rfl⟩ : syracuseStep 633205 = 59363) (by norm_num)
theorem B665981 : Blo 295830 665981 := bbase (se 3 (by rfl) ⟨124871, by rfl⟩ : syracuseStep 665981 = 249743) (by norm_num)
theorem B666053 : Blo 295830 666053 := bbase (se 4 (by rfl) ⟨62442, by rfl⟩ : syracuseStep 666053 = 124885) (by norm_num)
theorem B502213 : Blo 295830 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B666125 : Blo 295830 666125 := bbase (se 3 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 666125 = 249797) (by norm_num)
theorem B502301 : Blo 295830 502301 := bbase (se 3 (by rfl) ⟨94181, by rfl⟩ : syracuseStep 502301 = 188363) (by norm_num)
theorem B666197 : Blo 295830 666197 := bbase (se 8 (by rfl) ⟨3903, by rfl⟩ : syracuseStep 666197 = 7807) (by norm_num)
theorem B666269 : Blo 295830 666269 := bbase (se 3 (by rfl) ⟨124925, by rfl⟩ : syracuseStep 666269 = 249851) (by norm_num)
theorem B502429 : Blo 295830 502429 := bbase (se 3 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 502429 = 188411) (by norm_num)
theorem B1125029 : Blo 295830 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B1452725 : Blo 295830 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B2730709 : Blo 295830 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B666341 : Blo 295830 666341 := bbase (se 4 (by rfl) ⟨62469, by rfl⟩ : syracuseStep 666341 = 124939) (by norm_num)
theorem B502517 : Blo 295830 502517 := bbase (se 5 (by rfl) ⟨23555, by rfl⟩ : syracuseStep 502517 = 47111) (by norm_num)
theorem B666413 : Blo 295830 666413 := bbase (se 3 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 666413 = 249905) (by norm_num)
theorem B404333 : Blo 295830 404333 := bbase (se 3 (by rfl) ⟨75812, by rfl⟩ : syracuseStep 404333 = 151625) (by norm_num)
theorem B666485 : Blo 295830 666485 := bbase (se 5 (by rfl) ⟨31241, by rfl⟩ : syracuseStep 666485 = 62483) (by norm_num)
theorem B502645 : Blo 295830 502645 := bbase (se 5 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 502645 = 47123) (by norm_num)
theorem B666557 : Blo 295830 666557 := bbase (se 3 (by rfl) ⟨124979, by rfl⟩ : syracuseStep 666557 = 249959) (by norm_num)
theorem B502733 : Blo 295830 502733 := bbase (se 3 (by rfl) ⟨94262, by rfl⟩ : syracuseStep 502733 = 188525) (by norm_num)
theorem B568309 : Blo 295830 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B666629 : Blo 295830 666629 := bbase (se 4 (by rfl) ⟨62496, by rfl⟩ : syracuseStep 666629 = 124993) (by norm_num)
theorem B666701 : Blo 295830 666701 := bbase (se 3 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 666701 = 250013) (by norm_num)
theorem B502861 : Blo 295830 502861 := bbase (se 3 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 502861 = 188573) (by norm_num)
theorem B568453 : Blo 295830 568453 := bbase (se 4 (by rfl) ⟨53292, by rfl⟩ : syracuseStep 568453 = 106585) (by norm_num)
theorem B666773 : Blo 295830 666773 := bbase (se 6 (by rfl) ⟨15627, by rfl⟩ : syracuseStep 666773 = 31255) (by norm_num)
theorem B535709 : Blo 295830 535709 := bbase (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) (by norm_num)
theorem B339109 : Blo 295830 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B502949 : Blo 295830 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B765101 : Blo 295830 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B666845 : Blo 295830 666845 := bbase (se 3 (by rfl) ⟨125033, by rfl⟩ : syracuseStep 666845 = 250067) (by norm_num)
theorem B535781 : Blo 295830 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B666917 : Blo 295830 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B503077 : Blo 295830 503077 := bbase (se 4 (by rfl) ⟨47163, by rfl⟩ : syracuseStep 503077 = 94327) (by norm_num)
theorem B568613 : Blo 295830 568613 := bbase (se 4 (by rfl) ⟨53307, by rfl⟩ : syracuseStep 568613 = 106615) (by norm_num)
theorem B666989 : Blo 295830 666989 := bbase (se 3 (by rfl) ⟨125060, by rfl⟩ : syracuseStep 666989 = 250121) (by norm_num)
theorem B503165 : Blo 295830 503165 := bbase (se 3 (by rfl) ⟨94343, by rfl⟩ : syracuseStep 503165 = 188687) (by norm_num)
theorem B667061 : Blo 295830 667061 := bbase (se 5 (by rfl) ⟨31268, by rfl⟩ : syracuseStep 667061 = 62537) (by norm_num)
theorem B568757 : Blo 295830 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B339401 : Blo 295830 339401 := bbase (se 2 (by rfl) ⟨127275, by rfl⟩ : syracuseStep 339401 = 254551) (by norm_num)
theorem B634333 : Blo 295830 634333 := bbase (se 3 (by rfl) ⟨118937, by rfl⟩ : syracuseStep 634333 = 237875) (by norm_num)
theorem B667133 : Blo 295830 667133 := bbase (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) (by norm_num)
theorem B503293 : Blo 295830 503293 := bbase (se 3 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 503293 = 188735) (by norm_num)
theorem B405037 : Blo 295830 405037 := bbase (se 3 (by rfl) ⟨75944, by rfl⟩ : syracuseStep 405037 = 151889) (by norm_num)
theorem B667205 : Blo 295830 667205 := bbase (se 4 (by rfl) ⟨62550, by rfl⟩ : syracuseStep 667205 = 125101) (by norm_num)
theorem B503381 : Blo 295830 503381 := bbase (se 8 (by rfl) ⟨2949, by rfl⟩ : syracuseStep 503381 = 5899) (by norm_num)
theorem B667277 : Blo 295830 667277 := bbase (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) (by norm_num)
theorem B306829 : Blo 295830 306829 := bbase (se 3 (by rfl) ⟨57530, by rfl⟩ : syracuseStep 306829 = 115061) (by norm_num)
theorem B667349 : Blo 295830 667349 := bbase (se 7 (by rfl) ⟨7820, by rfl⟩ : syracuseStep 667349 = 15641) (by norm_num)
theorem B503509 : Blo 295830 503509 := bbase (se 7 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 503509 = 11801) (by norm_num)
theorem B569045 : Blo 295830 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B536285 : Blo 295830 536285 := bbase (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) (by norm_num)
theorem B339733 : Blo 295830 339733 := bbase (se 6 (by rfl) ⟨7962, by rfl⟩ : syracuseStep 339733 = 15925) (by norm_num)
theorem B667421 : Blo 295830 667421 := bbase (se 3 (by rfl) ⟨125141, by rfl⟩ : syracuseStep 667421 = 250283) (by norm_num)
theorem B503597 : Blo 295830 503597 := bbase (se 3 (by rfl) ⟨94424, by rfl⟩ : syracuseStep 503597 = 188849) (by norm_num)
theorem B634709 : Blo 295830 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B667493 : Blo 295830 667493 := bbase (se 4 (by rfl) ⟨62577, by rfl⟩ : syracuseStep 667493 = 125155) (by norm_num)
theorem B569197 : Blo 295830 569197 := bbase (se 3 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 569197 = 213449) (by norm_num)
theorem B667565 : Blo 295830 667565 := bbase (se 3 (by rfl) ⟨125168, by rfl⟩ : syracuseStep 667565 = 250337) (by norm_num)
theorem B503725 : Blo 295830 503725 := bbase (se 3 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 503725 = 188897) (by norm_num)
theorem B667637 : Blo 295830 667637 := bbase (se 5 (by rfl) ⟨31295, by rfl⟩ : syracuseStep 667637 = 62591) (by norm_num)
theorem B503813 : Blo 295830 503813 := bbase (se 4 (by rfl) ⟨47232, by rfl⟩ : syracuseStep 503813 = 94465) (by norm_num)
theorem B339985 : Blo 295830 339985 := bbase (se 2 (by rfl) ⟨127494, by rfl⟩ : syracuseStep 339985 = 254989) (by norm_num)
theorem B667709 : Blo 295830 667709 := bbase (se 3 (by rfl) ⟨125195, by rfl⟩ : syracuseStep 667709 = 250391) (by norm_num)
theorem B667781 : Blo 295830 667781 := bbase (se 4 (by rfl) ⟨62604, by rfl⟩ : syracuseStep 667781 = 125209) (by norm_num)
theorem B503941 : Blo 295830 503941 := bbase (se 4 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 503941 = 94489) (by norm_num)
theorem B667853 : Blo 295830 667853 := bbase (se 3 (by rfl) ⟨125222, by rfl⟩ : syracuseStep 667853 = 250445) (by norm_num)
theorem B2699477 : Blo 295830 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B504029 : Blo 295830 504029 := bbase (se 3 (by rfl) ⟨94505, by rfl⟩ : syracuseStep 504029 = 189011) (by norm_num)
theorem B602365 : Blo 295830 602365 := bbase (se 3 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 602365 = 225887) (by norm_num)
theorem B667925 : Blo 295830 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B2896181 : Blo 295830 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B667997 : Blo 295830 667997 := bbase (se 3 (by rfl) ⟨125249, by rfl⟩ : syracuseStep 667997 = 250499) (by norm_num)
theorem B504157 : Blo 295830 504157 := bbase (se 3 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 504157 = 189059) (by norm_num)
theorem B668069 : Blo 295830 668069 := bbase (se 4 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 668069 = 125263) (by norm_num)
theorem B504245 : Blo 295830 504245 := bbase (se 5 (by rfl) ⟨23636, by rfl⟩ : syracuseStep 504245 = 47273) (by norm_num)
theorem B340445 : Blo 295830 340445 := bbase (se 3 (by rfl) ⟨63833, by rfl⟩ : syracuseStep 340445 = 127667) (by norm_num)
theorem B668141 : Blo 295830 668141 := bbase (se 3 (by rfl) ⟨125276, by rfl⟩ : syracuseStep 668141 = 250553) (by norm_num)
theorem B668213 : Blo 295830 668213 := bbase (se 5 (by rfl) ⟨31322, by rfl⟩ : syracuseStep 668213 = 62645) (by norm_num)
theorem B504373 : Blo 295830 504373 := bbase (se 5 (by rfl) ⟨23642, by rfl⟩ : syracuseStep 504373 = 47285) (by norm_num)
theorem B668285 : Blo 295830 668285 := bbase (se 3 (by rfl) ⟨125303, by rfl⟩ : syracuseStep 668285 = 250607) (by norm_num)
theorem B504461 : Blo 295830 504461 := bbase (se 3 (by rfl) ⟨94586, by rfl⟩ : syracuseStep 504461 = 189173) (by norm_num)
theorem B668357 : Blo 295830 668357 := bbase (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) (by norm_num)
theorem B1913557 : Blo 295830 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B1127141 : Blo 295830 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B668429 : Blo 295830 668429 := bbase (se 3 (by rfl) ⟨125330, by rfl⟩ : syracuseStep 668429 = 250661) (by norm_num)
theorem B504589 : Blo 295830 504589 := bbase (se 3 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 504589 = 189221) (by norm_num)
theorem B1815317 : Blo 295830 1815317 := bbase (se 6 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 1815317 = 85093) (by norm_num)
theorem B668501 : Blo 295830 668501 := bbase (se 9 (by rfl) ⟨1958, by rfl⟩ : syracuseStep 668501 = 3917) (by norm_num)
theorem B504677 : Blo 295830 504677 := bbase (se 4 (by rfl) ⟨47313, by rfl⟩ : syracuseStep 504677 = 94627) (by norm_num)
theorem B668573 : Blo 295830 668573 := bbase (se 3 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 668573 = 250715) (by norm_num)
theorem B2536373 : Blo 295830 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B603061 : Blo 295830 603061 := bbase (se 5 (by rfl) ⟨28268, by rfl⟩ : syracuseStep 603061 = 56537) (by norm_num)
theorem B668645 : Blo 295830 668645 := bbase (se 4 (by rfl) ⟨62685, by rfl⟩ : syracuseStep 668645 = 125371) (by norm_num)
theorem B504805 : Blo 295830 504805 := bbase (se 4 (by rfl) ⟨47325, by rfl⟩ : syracuseStep 504805 = 94651) (by norm_num)
theorem B1127429 : Blo 295830 1127429 := bbase (se 4 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 1127429 = 211393) (by norm_num)
theorem B668717 : Blo 295830 668717 := bbase (se 3 (by rfl) ⟨125384, by rfl⟩ : syracuseStep 668717 = 250769) (by norm_num)
theorem B504893 : Blo 295830 504893 := bbase (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) (by norm_num)
theorem B341057 : Blo 295830 341057 := bbase (se 2 (by rfl) ⟨127896, by rfl⟩ : syracuseStep 341057 = 255793) (by norm_num)
theorem B668789 : Blo 295830 668789 := bbase (se 5 (by rfl) ⟨31349, by rfl⟩ : syracuseStep 668789 = 62699) (by norm_num)
theorem B668861 : Blo 295830 668861 := bbase (se 3 (by rfl) ⟨125411, by rfl⟩ : syracuseStep 668861 = 250823) (by norm_num)
theorem B505021 : Blo 295830 505021 := bbase (se 3 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 505021 = 189383) (by norm_num)
theorem B668933 : Blo 295830 668933 := bbase (se 4 (by rfl) ⟨62712, by rfl⟩ : syracuseStep 668933 = 125425) (by norm_num)
theorem B505109 : Blo 295830 505109 := bbase (se 6 (by rfl) ⟨11838, by rfl⟩ : syracuseStep 505109 = 23677) (by norm_num)
theorem B669005 : Blo 295830 669005 := bbase (se 3 (by rfl) ⟨125438, by rfl⟩ : syracuseStep 669005 = 250877) (by norm_num)
theorem B865637 : Blo 295830 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B603533 : Blo 295830 603533 := bbase (se 3 (by rfl) ⟨113162, by rfl⟩ : syracuseStep 603533 = 226325) (by norm_num)
theorem B669077 : Blo 295830 669077 := bbase (se 6 (by rfl) ⟨15681, by rfl⟩ : syracuseStep 669077 = 31363) (by norm_num)
theorem B505237 : Blo 295830 505237 := bbase (se 6 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 505237 = 23683) (by norm_num)
theorem B636349 : Blo 295830 636349 := bbase (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) (by norm_num)
theorem B669149 : Blo 295830 669149 := bbase (se 3 (by rfl) ⟨125465, by rfl⟩ : syracuseStep 669149 = 250931) (by norm_num)
theorem B505325 : Blo 295830 505325 := bbase (se 3 (by rfl) ⟨94748, by rfl⟩ : syracuseStep 505325 = 189497) (by norm_num)
theorem B669221 : Blo 295830 669221 := bbase (se 4 (by rfl) ⟨62739, by rfl⟩ : syracuseStep 669221 = 125479) (by norm_num)
theorem B669293 : Blo 295830 669293 := bbase (se 3 (by rfl) ⟨125492, by rfl⟩ : syracuseStep 669293 = 250985) (by norm_num)
theorem B505453 : Blo 295830 505453 := bbase (se 3 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 505453 = 189545) (by norm_num)
theorem B2274965 : Blo 295830 2274965 := bbase (se 6 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 2274965 = 106639) (by norm_num)
theorem B669365 : Blo 295830 669365 := bbase (se 5 (by rfl) ⟨31376, by rfl⟩ : syracuseStep 669365 = 62753) (by norm_num)
theorem B505541 : Blo 295830 505541 := bbase (se 4 (by rfl) ⟨47394, by rfl⟩ : syracuseStep 505541 = 94789) (by norm_num)
theorem B374473 : Blo 295830 374473 := bbase (se 2 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 374473 = 280855) (by norm_num)
theorem B669437 : Blo 295830 669437 := bbase (se 3 (by rfl) ⟨125519, by rfl⟩ : syracuseStep 669437 = 251039) (by norm_num)
theorem B341777 : Blo 295830 341777 := bbase (se 2 (by rfl) ⟨128166, by rfl⟩ : syracuseStep 341777 = 256333) (by norm_num)
theorem B3094325 : Blo 295830 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B669509 : Blo 295830 669509 := bbase (se 4 (by rfl) ⟨62766, by rfl⟩ : syracuseStep 669509 = 125533) (by norm_num)
theorem B505669 : Blo 295830 505669 := bbase (se 4 (by rfl) ⟨47406, by rfl⟩ : syracuseStep 505669 = 94813) (by norm_num)
theorem B374645 : Blo 295830 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B669581 : Blo 295830 669581 := bbase (se 3 (by rfl) ⟨125546, by rfl⟩ : syracuseStep 669581 = 251093) (by norm_num)
theorem B505757 : Blo 295830 505757 := bbase (se 3 (by rfl) ⟨94829, by rfl⟩ : syracuseStep 505757 = 189659) (by norm_num)
theorem B374701 : Blo 295830 374701 := bbase (se 3 (by rfl) ⟨70256, by rfl⟩ : syracuseStep 374701 = 140513) (by norm_num)
theorem B669653 : Blo 295830 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B604157 : Blo 295830 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B604165 : Blo 295830 604165 := bbase (se 4 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 604165 = 113281) (by norm_num)
theorem B374797 : Blo 295830 374797 := bbase (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) (by norm_num)
theorem B669725 : Blo 295830 669725 := bbase (se 3 (by rfl) ⟨125573, by rfl⟩ : syracuseStep 669725 = 251147) (by norm_num)
theorem B505885 : Blo 295830 505885 := bbase (se 3 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 505885 = 189707) (by norm_num)
theorem B669797 : Blo 295830 669797 := bbase (se 4 (by rfl) ⟨62793, by rfl⟩ : syracuseStep 669797 = 125587) (by norm_num)
theorem B1128613 : Blo 295830 1128613 := bbase (se 4 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 1128613 = 211615) (by norm_num)
theorem B669869 : Blo 295830 669869 := bbase (se 3 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 669869 = 251201) (by norm_num)
theorem B374969 : Blo 295830 374969 := bbase (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) (by norm_num)
theorem B375025 : Blo 295830 375025 := bbase (se 2 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 375025 = 281269) (by norm_num)
theorem B669941 : Blo 295830 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B637237 : Blo 295830 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B670013 : Blo 295830 670013 := bbase (se 3 (by rfl) ⟨125627, by rfl⟩ : syracuseStep 670013 = 251255) (by norm_num)
theorem B375121 : Blo 295830 375121 := bbase (se 2 (by rfl) ⟨140670, by rfl⟩ : syracuseStep 375121 = 281341) (by norm_num)
theorem B670085 : Blo 295830 670085 := bbase (se 4 (by rfl) ⟨62820, by rfl⟩ : syracuseStep 670085 = 125641) (by norm_num)
theorem B506261 : Blo 295830 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B670157 : Blo 295830 670157 := bbase (se 3 (by rfl) ⟨125654, by rfl⟩ : syracuseStep 670157 = 251309) (by norm_num)
theorem B1128917 : Blo 295830 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B375293 : Blo 295830 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B670229 : Blo 295830 670229 := bbase (se 6 (by rfl) ⟨15708, by rfl⟩ : syracuseStep 670229 = 31417) (by norm_num)
theorem B375349 : Blo 295830 375349 := bbase (se 5 (by rfl) ⟨17594, by rfl⟩ : syracuseStep 375349 = 35189) (by norm_num)
theorem B1620533 : Blo 295830 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B670301 : Blo 295830 670301 := bbase (se 3 (by rfl) ⟨125681, by rfl⟩ : syracuseStep 670301 = 251363) (by norm_num)
theorem B375445 : Blo 295830 375445 := bbase (se 6 (by rfl) ⟨8799, by rfl⟩ : syracuseStep 375445 = 17599) (by norm_num)
theorem B670373 : Blo 295830 670373 := bbase (se 4 (by rfl) ⟨62847, by rfl⟩ : syracuseStep 670373 = 125695) (by norm_num)
theorem B670445 : Blo 295830 670445 := bbase (se 3 (by rfl) ⟨125708, by rfl⟩ : syracuseStep 670445 = 251417) (by norm_num)
theorem B637733 : Blo 295830 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B670517 : Blo 295830 670517 := bbase (se 5 (by rfl) ⟨31430, by rfl⟩ : syracuseStep 670517 = 62861) (by norm_num)
theorem B375617 : Blo 295830 375617 := bbase (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) (by norm_num)
theorem B375673 : Blo 295830 375673 := bbase (se 2 (by rfl) ⟨140877, by rfl⟩ : syracuseStep 375673 = 281755) (by norm_num)
theorem B670589 : Blo 295830 670589 := bbase (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) (by norm_num)
theorem B670661 : Blo 295830 670661 := bbase (se 4 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 670661 = 125749) (by norm_num)
theorem B375769 : Blo 295830 375769 := bbase (se 2 (by rfl) ⟨140913, by rfl⟩ : syracuseStep 375769 = 281827) (by norm_num)
theorem B670733 : Blo 295830 670733 := bbase (se 3 (by rfl) ⟨125762, by rfl⟩ : syracuseStep 670733 = 251525) (by norm_num)
theorem B1424405 : Blo 295830 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B474149 : Blo 295830 474149 := bbase (se 4 (by rfl) ⟨44451, by rfl⟩ : syracuseStep 474149 = 88903) (by norm_num)
theorem B670805 : Blo 295830 670805 := bbase (se 8 (by rfl) ⟨3930, by rfl⟩ : syracuseStep 670805 = 7861) (by norm_num)
theorem B375941 : Blo 295830 375941 := bbase (se 4 (by rfl) ⟨35244, by rfl⟩ : syracuseStep 375941 = 70489) (by norm_num)
theorem B539797 : Blo 295830 539797 := bbase (se 6 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 539797 = 25303) (by norm_num)
theorem B670877 : Blo 295830 670877 := bbase (se 3 (by rfl) ⟨125789, by rfl⟩ : syracuseStep 670877 = 251579) (by norm_num)
theorem B375997 : Blo 295830 375997 := bbase (se 3 (by rfl) ⟨70499, by rfl⟩ : syracuseStep 375997 = 140999) (by norm_num)
theorem B670949 : Blo 295830 670949 := bbase (se 4 (by rfl) ⟨62901, by rfl⟩ : syracuseStep 670949 = 125803) (by norm_num)
theorem B376093 : Blo 295830 376093 := bbase (se 3 (by rfl) ⟨70517, by rfl⟩ : syracuseStep 376093 = 141035) (by norm_num)
theorem B671021 : Blo 295830 671021 := bbase (se 3 (by rfl) ⟨125816, by rfl⟩ : syracuseStep 671021 = 251633) (by norm_num)
theorem B474437 : Blo 295830 474437 := bbase (se 4 (by rfl) ⟨44478, by rfl⟩ : syracuseStep 474437 = 88957) (by norm_num)
theorem B671093 : Blo 295830 671093 := bbase (se 5 (by rfl) ⟨31457, by rfl⟩ : syracuseStep 671093 = 62915) (by norm_num)
theorem B998837 : Blo 295830 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B671165 : Blo 295830 671165 := bbase (se 3 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 671165 = 251687) (by norm_num)
theorem B376265 : Blo 295830 376265 := bbase (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) (by norm_num)
theorem B1916405 : Blo 295830 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B376321 : Blo 295830 376321 := bbase (se 2 (by rfl) ⟨141120, by rfl⟩ : syracuseStep 376321 = 282241) (by norm_num)
theorem B671237 : Blo 295830 671237 := bbase (se 4 (by rfl) ⟨62928, by rfl⟩ : syracuseStep 671237 = 125857) (by norm_num)
theorem B900629 : Blo 295830 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B671309 : Blo 295830 671309 := bbase (se 3 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 671309 = 251741) (by norm_num)
theorem B376417 : Blo 295830 376417 := bbase (se 2 (by rfl) ⟨141156, by rfl⟩ : syracuseStep 376417 = 282313) (by norm_num)
theorem B638597 : Blo 295830 638597 := bbase (se 4 (by rfl) ⟨59868, by rfl⟩ : syracuseStep 638597 = 119737) (by norm_num)
theorem B671381 : Blo 295830 671381 := bbase (se 6 (by rfl) ⟨15735, by rfl⟩ : syracuseStep 671381 = 31471) (by norm_num)
theorem B573149 : Blo 295830 573149 := bbase (se 3 (by rfl) ⟨107465, by rfl⟩ : syracuseStep 573149 = 214931) (by norm_num)
theorem B671453 : Blo 295830 671453 := bbase (se 3 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 671453 = 251795) (by norm_num)
theorem B376589 : Blo 295830 376589 := bbase (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) (by norm_num)
theorem B638741 : Blo 295830 638741 := bbase (se 6 (by rfl) ⟨14970, by rfl⟩ : syracuseStep 638741 = 29941) (by norm_num)
theorem B671525 : Blo 295830 671525 := bbase (se 4 (by rfl) ⟨62955, by rfl⟩ : syracuseStep 671525 = 125911) (by norm_num)
theorem B376645 : Blo 295830 376645 := bbase (se 4 (by rfl) ⟨35310, by rfl⟩ : syracuseStep 376645 = 70621) (by norm_num)
theorem B2539349 : Blo 295830 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B999269 : Blo 295830 999269 := bbase (se 4 (by rfl) ⟨93681, by rfl⟩ : syracuseStep 999269 = 187363) (by norm_num)
theorem B671597 : Blo 295830 671597 := bbase (se 3 (by rfl) ⟨125924, by rfl⟩ : syracuseStep 671597 = 251849) (by norm_num)
theorem B376741 : Blo 295830 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B671669 : Blo 295830 671669 := bbase (se 5 (by rfl) ⟨31484, by rfl⟩ : syracuseStep 671669 = 62969) (by norm_num)
theorem B671741 : Blo 295830 671741 := bbase (se 3 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 671741 = 251903) (by norm_num)
theorem B671813 : Blo 295830 671813 := bbase (se 4 (by rfl) ⟨62982, by rfl⟩ : syracuseStep 671813 = 125965) (by norm_num)
theorem B376913 : Blo 295830 376913 := bbase (se 2 (by rfl) ⟨141342, by rfl⟩ : syracuseStep 376913 = 282685) (by norm_num)
theorem B475237 : Blo 295830 475237 := bbase (se 4 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 475237 = 89107) (by norm_num)
theorem B376969 : Blo 295830 376969 := bbase (se 2 (by rfl) ⟨141363, by rfl⟩ : syracuseStep 376969 = 282727) (by norm_num)
theorem B671885 : Blo 295830 671885 := bbase (se 3 (by rfl) ⟨125978, by rfl⟩ : syracuseStep 671885 = 251957) (by norm_num)
theorem B671957 : Blo 295830 671957 := bbase (se 7 (by rfl) ⟨7874, by rfl⟩ : syracuseStep 671957 = 15749) (by norm_num)
theorem B377065 : Blo 295830 377065 := bbase (se 2 (by rfl) ⟨141399, by rfl⟩ : syracuseStep 377065 = 282799) (by norm_num)
theorem B999701 : Blo 295830 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B672029 : Blo 295830 672029 := bbase (se 3 (by rfl) ⟨126005, by rfl⟩ : syracuseStep 672029 = 252011) (by norm_num)
theorem B672101 : Blo 295830 672101 := bbase (se 4 (by rfl) ⟨63009, by rfl⟩ : syracuseStep 672101 = 126019) (by norm_num)
theorem B377237 : Blo 295830 377237 := bbase (se 6 (by rfl) ⟨8841, by rfl⟩ : syracuseStep 377237 = 17683) (by norm_num)
theorem B672173 : Blo 295830 672173 := bbase (se 3 (by rfl) ⟨126032, by rfl⟩ : syracuseStep 672173 = 252065) (by norm_num)
theorem B377293 : Blo 295830 377293 := bbase (se 3 (by rfl) ⟨70742, by rfl⟩ : syracuseStep 377293 = 141485) (by norm_num)
theorem B672245 : Blo 295830 672245 := bbase (se 5 (by rfl) ⟨31511, by rfl⟩ : syracuseStep 672245 = 63023) (by norm_num)
theorem B639485 : Blo 295830 639485 := bbase (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) (by norm_num)
theorem B1131029 : Blo 295830 1131029 := bbase (se 6 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 1131029 = 53017) (by norm_num)
theorem B377389 : Blo 295830 377389 := bbase (se 3 (by rfl) ⟨70760, by rfl⟩ : syracuseStep 377389 = 141521) (by norm_num)
theorem B672317 : Blo 295830 672317 := bbase (se 3 (by rfl) ⟨126059, by rfl⟩ : syracuseStep 672317 = 252119) (by norm_num)
theorem B672389 : Blo 295830 672389 := bbase (se 4 (by rfl) ⟨63036, by rfl⟩ : syracuseStep 672389 = 126073) (by norm_num)
theorem B475789 : Blo 295830 475789 := bbase (se 3 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 475789 = 178421) (by norm_num)
theorem B1000133 : Blo 295830 1000133 := bbase (se 4 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 1000133 = 187525) (by norm_num)
theorem B541381 : Blo 295830 541381 := bbase (se 4 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 541381 = 101509) (by norm_num)
theorem B672461 : Blo 295830 672461 := bbase (se 3 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 672461 = 252173) (by norm_num)
theorem B377561 : Blo 295830 377561 := bbase (se 2 (by rfl) ⟨141585, by rfl⟩ : syracuseStep 377561 = 283171) (by norm_num)
theorem B377617 : Blo 295830 377617 := bbase (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) (by norm_num)
theorem B672533 : Blo 295830 672533 := bbase (se 6 (by rfl) ⟨15762, by rfl⟩ : syracuseStep 672533 = 31525) (by norm_num)
theorem B1131317 : Blo 295830 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B672605 : Blo 295830 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B377713 : Blo 295830 377713 := bbase (se 2 (by rfl) ⟨141642, by rfl⟩ : syracuseStep 377713 = 283285) (by norm_num)
theorem B476045 : Blo 295830 476045 := bbase (se 3 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 476045 = 178517) (by norm_num)
theorem B672677 : Blo 295830 672677 := bbase (se 4 (by rfl) ⟨63063, by rfl⟩ : syracuseStep 672677 = 126127) (by norm_num)
theorem B607181 : Blo 295830 607181 := bbase (se 3 (by rfl) ⟨113846, by rfl⟩ : syracuseStep 607181 = 227693) (by norm_num)
theorem B672749 : Blo 295830 672749 := bbase (se 3 (by rfl) ⟨126140, by rfl⟩ : syracuseStep 672749 = 252281) (by norm_num)
theorem B607213 : Blo 295830 607213 := bbase (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) (by norm_num)
theorem B1295365 : Blo 295830 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B377885 : Blo 295830 377885 := bbase (se 3 (by rfl) ⟨70853, by rfl⟩ : syracuseStep 377885 = 141707) (by norm_num)
theorem B672821 : Blo 295830 672821 := bbase (se 5 (by rfl) ⟨31538, by rfl⟩ : syracuseStep 672821 = 63077) (by norm_num)
theorem B803909 : Blo 295830 803909 := bbase (se 4 (by rfl) ⟨75366, by rfl⟩ : syracuseStep 803909 = 150733) (by norm_num)
theorem B377941 : Blo 295830 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B1000565 : Blo 295830 1000565 := bbase (se 5 (by rfl) ⟨46901, by rfl⟩ : syracuseStep 1000565 = 93803) (by norm_num)
theorem B672893 : Blo 295830 672893 := bbase (se 3 (by rfl) ⟨126167, by rfl⟩ : syracuseStep 672893 = 252335) (by norm_num)
theorem B378037 : Blo 295830 378037 := bbase (se 5 (by rfl) ⟨17720, by rfl⟩ : syracuseStep 378037 = 35441) (by norm_num)
theorem B672965 : Blo 295830 672965 := bbase (se 4 (by rfl) ⟨63090, by rfl⟩ : syracuseStep 672965 = 126181) (by norm_num)
theorem B640237 : Blo 295830 640237 := bbase (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) (by norm_num)
theorem B1066229 : Blo 295830 1066229 := bbase (se 5 (by rfl) ⟨49979, by rfl⟩ : syracuseStep 1066229 = 99959) (by norm_num)
theorem B673037 : Blo 295830 673037 := bbase (se 3 (by rfl) ⟨126194, by rfl⟩ : syracuseStep 673037 = 252389) (by norm_num)
theorem B673109 : Blo 295830 673109 := bbase (se 12 (by rfl) ⟨246, by rfl⟩ : syracuseStep 673109 = 493) (by norm_num)
theorem B378209 : Blo 295830 378209 := bbase (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) (by norm_num)
theorem B443765 : Blo 295830 443765 := bbase (se 5 (by rfl) ⟨20801, by rfl⟩ : syracuseStep 443765 = 41603) (by norm_num)
theorem B443789 : Blo 295830 443789 := bbase (se 3 (by rfl) ⟨83210, by rfl⟩ : syracuseStep 443789 = 166421) (by norm_num)
theorem B607637 : Blo 295830 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B378265 : Blo 295830 378265 := bbase (se 2 (by rfl) ⟨141849, by rfl⟩ : syracuseStep 378265 = 283699) (by norm_num)
theorem B673181 : Blo 295830 673181 := bbase (se 3 (by rfl) ⟨126221, by rfl⟩ : syracuseStep 673181 = 252443) (by norm_num)
theorem B443813 : Blo 295830 443813 := bbase (se 4 (by rfl) ⟨41607, by rfl⟩ : syracuseStep 443813 = 83215) (by norm_num)
theorem B443837 : Blo 295830 443837 := bbase (se 3 (by rfl) ⟨83219, by rfl⟩ : syracuseStep 443837 = 166439) (by norm_num)
theorem B443861 : Blo 295830 443861 := bbase (se 7 (by rfl) ⟨5201, by rfl⟩ : syracuseStep 443861 = 10403) (by norm_num)
theorem B673253 : Blo 295830 673253 := bbase (se 4 (by rfl) ⟨63117, by rfl⟩ : syracuseStep 673253 = 126235) (by norm_num)
theorem B443885 : Blo 295830 443885 := bbase (se 3 (by rfl) ⟨83228, by rfl⟩ : syracuseStep 443885 = 166457) (by norm_num)
theorem B378361 : Blo 295830 378361 := bbase (se 2 (by rfl) ⟨141885, by rfl⟩ : syracuseStep 378361 = 283771) (by norm_num)
theorem B443909 : Blo 295830 443909 := bbase (se 4 (by rfl) ⟨41616, by rfl⟩ : syracuseStep 443909 = 83233) (by norm_num)
theorem B1066517 : Blo 295830 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B443933 : Blo 295830 443933 := bbase (se 3 (by rfl) ⟨83237, by rfl⟩ : syracuseStep 443933 = 166475) (by norm_num)
theorem B1000997 : Blo 295830 1000997 := bbase (se 4 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 1000997 = 187687) (by norm_num)
theorem B673325 : Blo 295830 673325 := bbase (se 3 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 673325 = 252497) (by norm_num)
theorem B443957 : Blo 295830 443957 := bbase (se 5 (by rfl) ⟨20810, by rfl⟩ : syracuseStep 443957 = 41621) (by norm_num)
theorem B443981 : Blo 295830 443981 := bbase (se 3 (by rfl) ⟨83246, by rfl⟩ : syracuseStep 443981 = 166493) (by norm_num)
theorem B476749 : Blo 295830 476749 := bbase (se 3 (by rfl) ⟨89390, by rfl⟩ : syracuseStep 476749 = 178781) (by norm_num)
theorem B444005 : Blo 295830 444005 := bbase (se 4 (by rfl) ⟨41625, by rfl⟩ : syracuseStep 444005 = 83251) (by norm_num)
theorem B673397 : Blo 295830 673397 := bbase (se 5 (by rfl) ⟨31565, by rfl⟩ : syracuseStep 673397 = 63131) (by norm_num)
theorem B444029 : Blo 295830 444029 := bbase (se 3 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 444029 = 166511) (by norm_num)
theorem B444053 : Blo 295830 444053 := bbase (se 6 (by rfl) ⟨10407, by rfl⟩ : syracuseStep 444053 = 20815) (by norm_num)
theorem B378533 : Blo 295830 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B444077 : Blo 295830 444077 := bbase (se 3 (by rfl) ⟨83264, by rfl⟩ : syracuseStep 444077 = 166529) (by norm_num)
theorem B673469 : Blo 295830 673469 := bbase (se 3 (by rfl) ⟨126275, by rfl⟩ : syracuseStep 673469 = 252551) (by norm_num)
theorem B444101 : Blo 295830 444101 := bbase (se 4 (by rfl) ⟨41634, by rfl⟩ : syracuseStep 444101 = 83269) (by norm_num)
theorem B444125 : Blo 295830 444125 := bbase (se 3 (by rfl) ⟨83273, by rfl⟩ : syracuseStep 444125 = 166547) (by norm_num)
theorem B378589 : Blo 295830 378589 := bbase (se 3 (by rfl) ⟨70985, by rfl⟩ : syracuseStep 378589 = 141971) (by norm_num)
theorem B444149 : Blo 295830 444149 := bbase (se 5 (by rfl) ⟨20819, by rfl⟩ : syracuseStep 444149 = 41639) (by norm_num)
theorem B1623797 : Blo 295830 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B673541 : Blo 295830 673541 := bbase (se 4 (by rfl) ⟨63144, by rfl⟩ : syracuseStep 673541 = 126289) (by norm_num)
theorem B444173 : Blo 295830 444173 := bbase (se 3 (by rfl) ⟨83282, by rfl⟩ : syracuseStep 444173 = 166565) (by norm_num)
theorem B444197 : Blo 295830 444197 := bbase (se 4 (by rfl) ⟨41643, by rfl⟩ : syracuseStep 444197 = 83287) (by norm_num)
theorem B444221 : Blo 295830 444221 := bbase (se 3 (by rfl) ⟨83291, by rfl⟩ : syracuseStep 444221 = 166583) (by norm_num)
theorem B378685 : Blo 295830 378685 := bbase (se 3 (by rfl) ⟨71003, by rfl⟩ : syracuseStep 378685 = 142007) (by norm_num)
theorem B673613 : Blo 295830 673613 := bbase (se 3 (by rfl) ⟨126302, by rfl⟩ : syracuseStep 673613 = 252605) (by norm_num)
theorem B444245 : Blo 295830 444245 := bbase (se 9 (by rfl) ⟨1301, by rfl⟩ : syracuseStep 444245 = 2603) (by norm_num)
theorem B444269 : Blo 295830 444269 := bbase (se 3 (by rfl) ⟨83300, by rfl⟩ : syracuseStep 444269 = 166601) (by norm_num)
theorem B444293 : Blo 295830 444293 := bbase (se 4 (by rfl) ⟨41652, by rfl⟩ : syracuseStep 444293 = 83305) (by norm_num)
theorem B673685 : Blo 295830 673685 := bbase (se 6 (by rfl) ⟨15789, by rfl⟩ : syracuseStep 673685 = 31579) (by norm_num)
theorem B444317 : Blo 295830 444317 := bbase (se 3 (by rfl) ⟨83309, by rfl⟩ : syracuseStep 444317 = 166619) (by norm_num)
theorem B444341 : Blo 295830 444341 := bbase (se 5 (by rfl) ⟨20828, by rfl⟩ : syracuseStep 444341 = 41657) (by norm_num)
theorem B1066949 : Blo 295830 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B444365 : Blo 295830 444365 := bbase (se 3 (by rfl) ⟨83318, by rfl⟩ : syracuseStep 444365 = 166637) (by norm_num)
theorem B1001429 : Blo 295830 1001429 := bbase (se 7 (by rfl) ⟨11735, by rfl⟩ : syracuseStep 1001429 = 23471) (by norm_num)
theorem B1132501 : Blo 295830 1132501 := bbase (se 7 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 1132501 = 26543) (by norm_num)
theorem B673757 : Blo 295830 673757 := bbase (se 3 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 673757 = 252659) (by norm_num)
theorem B444389 : Blo 295830 444389 := bbase (se 4 (by rfl) ⟨41661, by rfl⟩ : syracuseStep 444389 = 83323) (by norm_num)
theorem B378857 : Blo 295830 378857 := bbase (se 2 (by rfl) ⟨142071, by rfl⟩ : syracuseStep 378857 = 284143) (by norm_num)
theorem B477173 : Blo 295830 477173 := bbase (se 5 (by rfl) ⟨22367, by rfl⟩ : syracuseStep 477173 = 44735) (by norm_num)
theorem B444413 : Blo 295830 444413 := bbase (se 3 (by rfl) ⟨83327, by rfl⟩ : syracuseStep 444413 = 166655) (by norm_num)
theorem B444437 : Blo 295830 444437 := bbase (se 6 (by rfl) ⟨10416, by rfl⟩ : syracuseStep 444437 = 20833) (by norm_num)
theorem B378913 : Blo 295830 378913 := bbase (se 2 (by rfl) ⟨142092, by rfl⟩ : syracuseStep 378913 = 284185) (by norm_num)
theorem B673829 : Blo 295830 673829 := bbase (se 4 (by rfl) ⟨63171, by rfl⟩ : syracuseStep 673829 = 126343) (by norm_num)
theorem B444461 : Blo 295830 444461 := bbase (se 3 (by rfl) ⟨83336, by rfl⟩ : syracuseStep 444461 = 166673) (by norm_num)
theorem B444485 : Blo 295830 444485 := bbase (se 4 (by rfl) ⟨41670, by rfl⟩ : syracuseStep 444485 = 83341) (by norm_num)
theorem B444509 : Blo 295830 444509 := bbase (se 3 (by rfl) ⟨83345, by rfl⟩ : syracuseStep 444509 = 166691) (by norm_num)
theorem B1427557 : Blo 295830 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B673901 : Blo 295830 673901 := bbase (se 3 (by rfl) ⟨126356, by rfl⟩ : syracuseStep 673901 = 252713) (by norm_num)
theorem B444533 : Blo 295830 444533 := bbase (se 5 (by rfl) ⟨20837, by rfl⟩ : syracuseStep 444533 = 41675) (by norm_num)
theorem B379009 : Blo 295830 379009 := bbase (se 2 (by rfl) ⟨142128, by rfl⟩ : syracuseStep 379009 = 284257) (by norm_num)
theorem B444557 : Blo 295830 444557 := bbase (se 3 (by rfl) ⟨83354, by rfl⟩ : syracuseStep 444557 = 166709) (by norm_num)
theorem B444581 : Blo 295830 444581 := bbase (se 4 (by rfl) ⟨41679, by rfl⟩ : syracuseStep 444581 = 83359) (by norm_num)
theorem B673973 : Blo 295830 673973 := bbase (se 5 (by rfl) ⟨31592, by rfl⟩ : syracuseStep 673973 = 63185) (by norm_num)
theorem B444605 : Blo 295830 444605 := bbase (se 3 (by rfl) ⟨83363, by rfl⟩ : syracuseStep 444605 = 166727) (by norm_num)
theorem B444629 : Blo 295830 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B444653 : Blo 295830 444653 := bbase (se 3 (by rfl) ⟨83372, by rfl⟩ : syracuseStep 444653 = 166745) (by norm_num)
theorem B674045 : Blo 295830 674045 := bbase (se 3 (by rfl) ⟨126383, by rfl⟩ : syracuseStep 674045 = 252767) (by norm_num)
theorem B444677 : Blo 295830 444677 := bbase (se 4 (by rfl) ⟨41688, by rfl⟩ : syracuseStep 444677 = 83377) (by norm_num)
theorem B1132805 : Blo 295830 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B477461 : Blo 295830 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B444701 : Blo 295830 444701 := bbase (se 3 (by rfl) ⟨83381, by rfl⟩ : syracuseStep 444701 = 166763) (by norm_num)
theorem B379181 : Blo 295830 379181 := bbase (se 3 (by rfl) ⟨71096, by rfl⟩ : syracuseStep 379181 = 142193) (by norm_num)
theorem B444725 : Blo 295830 444725 := bbase (se 5 (by rfl) ⟨20846, by rfl⟩ : syracuseStep 444725 = 41693) (by norm_num)
theorem B674117 : Blo 295830 674117 := bbase (se 4 (by rfl) ⟨63198, by rfl⟩ : syracuseStep 674117 = 126397) (by norm_num)
theorem B444749 : Blo 295830 444749 := bbase (se 3 (by rfl) ⟨83390, by rfl⟩ : syracuseStep 444749 = 166781) (by norm_num)
theorem B444773 : Blo 295830 444773 := bbase (se 4 (by rfl) ⟨41697, by rfl⟩ : syracuseStep 444773 = 83395) (by norm_num)
theorem B379237 : Blo 295830 379237 := bbase (se 4 (by rfl) ⟨35553, by rfl⟩ : syracuseStep 379237 = 71107) (by norm_num)
theorem B444797 : Blo 295830 444797 := bbase (se 3 (by rfl) ⟨83399, by rfl⟩ : syracuseStep 444797 = 166799) (by norm_num)
theorem B1001861 : Blo 295830 1001861 := bbase (se 4 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 1001861 = 187849) (by norm_num)
theorem B674189 : Blo 295830 674189 := bbase (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) (by norm_num)
theorem B444821 : Blo 295830 444821 := bbase (se 6 (by rfl) ⟨10425, by rfl⟩ : syracuseStep 444821 = 20851) (by norm_num)
theorem B444845 : Blo 295830 444845 := bbase (se 3 (by rfl) ⟨83408, by rfl⟩ : syracuseStep 444845 = 166817) (by norm_num)
theorem B444869 : Blo 295830 444869 := bbase (se 4 (by rfl) ⟨41706, by rfl⟩ : syracuseStep 444869 = 83413) (by norm_num)
theorem B379333 : Blo 295830 379333 := bbase (se 4 (by rfl) ⟨35562, by rfl⟩ : syracuseStep 379333 = 71125) (by norm_num)
theorem B3230165 : Blo 295830 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B674261 : Blo 295830 674261 := bbase (se 7 (by rfl) ⟨7901, by rfl⟩ : syracuseStep 674261 = 15803) (by norm_num)
theorem B444893 : Blo 295830 444893 := bbase (se 3 (by rfl) ⟨83417, by rfl⟩ : syracuseStep 444893 = 166835) (by norm_num)
theorem B444917 : Blo 295830 444917 := bbase (se 5 (by rfl) ⟨20855, by rfl⟩ : syracuseStep 444917 = 41711) (by norm_num)
theorem B477685 : Blo 295830 477685 := bbase (se 5 (by rfl) ⟨22391, by rfl⟩ : syracuseStep 477685 = 44783) (by norm_num)
theorem B444941 : Blo 295830 444941 := bbase (se 3 (by rfl) ⟨83426, by rfl⟩ : syracuseStep 444941 = 166853) (by norm_num)
theorem B674333 : Blo 295830 674333 := bbase (se 3 (by rfl) ⟨126437, by rfl⟩ : syracuseStep 674333 = 252875) (by norm_num)
theorem B444965 : Blo 295830 444965 := bbase (se 4 (by rfl) ⟨41715, by rfl⟩ : syracuseStep 444965 = 83431) (by norm_num)
theorem B444989 : Blo 295830 444989 := bbase (se 3 (by rfl) ⟨83435, by rfl⟩ : syracuseStep 444989 = 166871) (by norm_num)
theorem B445013 : Blo 295830 445013 := bbase (se 8 (by rfl) ⟨2607, by rfl⟩ : syracuseStep 445013 = 5215) (by norm_num)
theorem B674405 : Blo 295830 674405 := bbase (se 4 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 674405 = 126451) (by norm_num)
theorem B445037 : Blo 295830 445037 := bbase (se 3 (by rfl) ⟨83444, by rfl⟩ : syracuseStep 445037 = 166889) (by norm_num)
theorem B445061 : Blo 295830 445061 := bbase (se 4 (by rfl) ⟨41724, by rfl⟩ : syracuseStep 445061 = 83449) (by norm_num)
theorem B445085 : Blo 295830 445085 := bbase (se 3 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 445085 = 166907) (by norm_num)
theorem B674477 : Blo 295830 674477 := bbase (se 3 (by rfl) ⟨126464, by rfl⟩ : syracuseStep 674477 = 252929) (by norm_num)
theorem B445109 : Blo 295830 445109 := bbase (se 5 (by rfl) ⟨20864, by rfl⟩ : syracuseStep 445109 = 41729) (by norm_num)
theorem B445133 : Blo 295830 445133 := bbase (se 3 (by rfl) ⟨83462, by rfl⟩ : syracuseStep 445133 = 166925) (by norm_num)
theorem B7785173 : Blo 295830 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B445157 : Blo 295830 445157 := bbase (se 4 (by rfl) ⟨41733, by rfl⟩ : syracuseStep 445157 = 83467) (by norm_num)
theorem B674549 : Blo 295830 674549 := bbase (se 5 (by rfl) ⟨31619, by rfl⟩ : syracuseStep 674549 = 63239) (by norm_num)
theorem B445181 : Blo 295830 445181 := bbase (se 3 (by rfl) ⟨83471, by rfl⟩ : syracuseStep 445181 = 166943) (by norm_num)
theorem B445205 : Blo 295830 445205 := bbase (se 6 (by rfl) ⟨10434, by rfl⟩ : syracuseStep 445205 = 20869) (by norm_num)
theorem B445229 : Blo 295830 445229 := bbase (se 3 (by rfl) ⟨83480, by rfl⟩ : syracuseStep 445229 = 166961) (by norm_num)
theorem B1002293 : Blo 295830 1002293 := bbase (se 5 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 1002293 = 93965) (by norm_num)
theorem B445253 : Blo 295830 445253 := bbase (se 4 (by rfl) ⟨41742, by rfl⟩ : syracuseStep 445253 = 83485) (by norm_num)
theorem B445277 : Blo 295830 445277 := bbase (se 3 (by rfl) ⟨83489, by rfl⟩ : syracuseStep 445277 = 166979) (by norm_num)
theorem B445301 : Blo 295830 445301 := bbase (se 5 (by rfl) ⟨20873, by rfl⟩ : syracuseStep 445301 = 41747) (by norm_num)
theorem B510853 : Blo 295830 510853 := bbase (se 4 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 510853 = 95785) (by norm_num)
theorem B445325 : Blo 295830 445325 := bbase (se 3 (by rfl) ⟨83498, by rfl⟩ : syracuseStep 445325 = 166997) (by norm_num)
theorem B445349 : Blo 295830 445349 := bbase (se 4 (by rfl) ⟨41751, by rfl⟩ : syracuseStep 445349 = 83503) (by norm_num)
theorem B1264565 : Blo 295830 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B445373 : Blo 295830 445373 := bbase (se 3 (by rfl) ⟨83507, by rfl⟩ : syracuseStep 445373 = 167015) (by norm_num)
theorem B445397 : Blo 295830 445397 := bbase (se 7 (by rfl) ⟨5219, by rfl⟩ : syracuseStep 445397 = 10439) (by norm_num)
theorem B445421 : Blo 295830 445421 := bbase (se 3 (by rfl) ⟨83516, by rfl⟩ : syracuseStep 445421 = 167033) (by norm_num)
theorem B642053 : Blo 295830 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B445445 : Blo 295830 445445 := bbase (se 4 (by rfl) ⟨41760, by rfl⟩ : syracuseStep 445445 = 83521) (by norm_num)
theorem B445469 : Blo 295830 445469 := bbase (se 3 (by rfl) ⟨83525, by rfl⟩ : syracuseStep 445469 = 167051) (by norm_num)
theorem B445493 : Blo 295830 445493 := bbase (se 5 (by rfl) ⟨20882, by rfl⟩ : syracuseStep 445493 = 41765) (by norm_num)
theorem B445517 : Blo 295830 445517 := bbase (se 3 (by rfl) ⟨83534, by rfl⟩ : syracuseStep 445517 = 167069) (by norm_num)
theorem B445541 : Blo 295830 445541 := bbase (se 4 (by rfl) ⟨41769, by rfl⟩ : syracuseStep 445541 = 83539) (by norm_num)
theorem B674941 : Blo 295830 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B445565 : Blo 295830 445565 := bbase (se 3 (by rfl) ⟨83543, by rfl⟩ : syracuseStep 445565 = 167087) (by norm_num)
theorem B445589 : Blo 295830 445589 := bbase (se 6 (by rfl) ⟨10443, by rfl⟩ : syracuseStep 445589 = 20887) (by norm_num)
theorem B1264805 : Blo 295830 1264805 := bbase (se 4 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 1264805 = 237151) (by norm_num)
theorem B445613 : Blo 295830 445613 := bbase (se 3 (by rfl) ⟨83552, by rfl⟩ : syracuseStep 445613 = 167105) (by norm_num)
theorem B445637 : Blo 295830 445637 := bbase (se 4 (by rfl) ⟨41778, by rfl⟩ : syracuseStep 445637 = 83557) (by norm_num)
theorem B445661 : Blo 295830 445661 := bbase (se 3 (by rfl) ⟨83561, by rfl⟩ : syracuseStep 445661 = 167123) (by norm_num)
theorem B1002725 : Blo 295830 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B445685 : Blo 295830 445685 := bbase (se 5 (by rfl) ⟨20891, by rfl⟩ : syracuseStep 445685 = 41783) (by norm_num)
theorem B806149 : Blo 295830 806149 := bbase (se 4 (by rfl) ⟨75576, by rfl⟩ : syracuseStep 806149 = 151153) (by norm_num)
theorem B445709 : Blo 295830 445709 := bbase (se 3 (by rfl) ⟨83570, by rfl⟩ : syracuseStep 445709 = 167141) (by norm_num)
theorem B445733 : Blo 295830 445733 := bbase (se 4 (by rfl) ⟨41787, by rfl⟩ : syracuseStep 445733 = 83575) (by norm_num)
theorem B445757 : Blo 295830 445757 := bbase (se 3 (by rfl) ⟨83579, by rfl⟩ : syracuseStep 445757 = 167159) (by norm_num)
theorem B445781 : Blo 295830 445781 := bbase (se 11 (by rfl) ⟨326, by rfl⟩ : syracuseStep 445781 = 653) (by norm_num)
theorem B445805 : Blo 295830 445805 := bbase (se 3 (by rfl) ⟨83588, by rfl⟩ : syracuseStep 445805 = 167177) (by norm_num)
theorem B445829 : Blo 295830 445829 := bbase (se 4 (by rfl) ⟨41796, by rfl⟩ : syracuseStep 445829 = 83593) (by norm_num)
theorem B445853 : Blo 295830 445853 := bbase (se 3 (by rfl) ⟨83597, by rfl⟩ : syracuseStep 445853 = 167195) (by norm_num)
theorem B445877 : Blo 295830 445877 := bbase (se 5 (by rfl) ⟨20900, by rfl⟩ : syracuseStep 445877 = 41801) (by norm_num)
theorem B445901 : Blo 295830 445901 := bbase (se 3 (by rfl) ⟨83606, by rfl⟩ : syracuseStep 445901 = 167213) (by norm_num)
theorem B445925 : Blo 295830 445925 := bbase (se 4 (by rfl) ⟨41805, by rfl⟩ : syracuseStep 445925 = 83611) (by norm_num)
theorem B445949 : Blo 295830 445949 := bbase (se 3 (by rfl) ⟨83615, by rfl⟩ : syracuseStep 445949 = 167231) (by norm_num)
theorem B445973 : Blo 295830 445973 := bbase (se 6 (by rfl) ⟨10452, by rfl⟩ : syracuseStep 445973 = 20905) (by norm_num)
theorem B511517 : Blo 295830 511517 := bbase (se 3 (by rfl) ⟨95909, by rfl⟩ : syracuseStep 511517 = 191819) (by norm_num)
theorem B445997 : Blo 295830 445997 := bbase (se 3 (by rfl) ⟨83624, by rfl⟩ : syracuseStep 445997 = 167249) (by norm_num)
theorem B1691189 : Blo 295830 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B446021 : Blo 295830 446021 := bbase (se 4 (by rfl) ⟨41814, by rfl⟩ : syracuseStep 446021 = 83629) (by norm_num)
theorem B446045 : Blo 295830 446045 := bbase (se 3 (by rfl) ⟨83633, by rfl⟩ : syracuseStep 446045 = 167267) (by norm_num)
theorem B478813 : Blo 295830 478813 := bbase (se 3 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 478813 = 179555) (by norm_num)
theorem B446069 : Blo 295830 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B446093 : Blo 295830 446093 := bbase (se 3 (by rfl) ⟨83642, by rfl⟩ : syracuseStep 446093 = 167285) (by norm_num)
theorem B1003157 : Blo 295830 1003157 := bbase (se 6 (by rfl) ⟨23511, by rfl⟩ : syracuseStep 1003157 = 47023) (by norm_num)
theorem B446117 : Blo 295830 446117 := bbase (se 4 (by rfl) ⟨41823, by rfl⟩ : syracuseStep 446117 = 83647) (by norm_num)
theorem B446141 : Blo 295830 446141 := bbase (se 3 (by rfl) ⟨83651, by rfl⟩ : syracuseStep 446141 = 167303) (by norm_num)
theorem B446165 : Blo 295830 446165 := bbase (se 7 (by rfl) ⟨5228, by rfl⟩ : syracuseStep 446165 = 10457) (by norm_num)
theorem B446189 : Blo 295830 446189 := bbase (se 3 (by rfl) ⟨83660, by rfl⟩ : syracuseStep 446189 = 167321) (by norm_num)
theorem B446213 : Blo 295830 446213 := bbase (se 4 (by rfl) ⟨41832, by rfl⟩ : syracuseStep 446213 = 83665) (by norm_num)
theorem B446237 : Blo 295830 446237 := bbase (se 3 (by rfl) ⟨83669, by rfl⟩ : syracuseStep 446237 = 167339) (by norm_num)
theorem B446261 : Blo 295830 446261 := bbase (se 5 (by rfl) ⟨20918, by rfl⟩ : syracuseStep 446261 = 41837) (by norm_num)
theorem B872245 : Blo 295830 872245 := bbase (se 5 (by rfl) ⟨40886, by rfl⟩ : syracuseStep 872245 = 81773) (by norm_num)
theorem B446285 : Blo 295830 446285 := bbase (se 3 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 446285 = 167357) (by norm_num)
theorem B446309 : Blo 295830 446309 := bbase (se 4 (by rfl) ⟨41841, by rfl⟩ : syracuseStep 446309 = 83683) (by norm_num)
theorem B446333 : Blo 295830 446333 := bbase (se 3 (by rfl) ⟨83687, by rfl⟩ : syracuseStep 446333 = 167375) (by norm_num)
theorem B446357 : Blo 295830 446357 := bbase (se 6 (by rfl) ⟨10461, by rfl⟩ : syracuseStep 446357 = 20923) (by norm_num)
theorem B446381 : Blo 295830 446381 := bbase (se 3 (by rfl) ⟨83696, by rfl⟩ : syracuseStep 446381 = 167393) (by norm_num)
theorem B380857 : Blo 295830 380857 := bbase (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) (by norm_num)
theorem B446405 : Blo 295830 446405 := bbase (se 4 (by rfl) ⟨41850, by rfl⟩ : syracuseStep 446405 = 83701) (by norm_num)
theorem B446429 : Blo 295830 446429 := bbase (se 3 (by rfl) ⟨83705, by rfl⟩ : syracuseStep 446429 = 167411) (by norm_num)
theorem B2543605 : Blo 295830 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B446453 : Blo 295830 446453 := bbase (se 5 (by rfl) ⟨20927, by rfl⟩ : syracuseStep 446453 = 41855) (by norm_num)
theorem B446477 : Blo 295830 446477 := bbase (se 3 (by rfl) ⟨83714, by rfl⟩ : syracuseStep 446477 = 167429) (by norm_num)
theorem B479261 : Blo 295830 479261 := bbase (se 3 (by rfl) ⟨89861, by rfl⟩ : syracuseStep 479261 = 179723) (by norm_num)
theorem B380965 : Blo 295830 380965 := bbase (se 4 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 380965 = 71431) (by norm_num)
theorem B446501 : Blo 295830 446501 := bbase (se 4 (by rfl) ⟨41859, by rfl⟩ : syracuseStep 446501 = 83719) (by norm_num)
theorem B446525 : Blo 295830 446525 := bbase (se 3 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 446525 = 167447) (by norm_num)
theorem B1003589 : Blo 295830 1003589 := bbase (se 4 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 1003589 = 188173) (by norm_num)
theorem B446549 : Blo 295830 446549 := bbase (se 8 (by rfl) ⟨2616, by rfl⟩ : syracuseStep 446549 = 5233) (by norm_num)
theorem B446573 : Blo 295830 446573 := bbase (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) (by norm_num)
theorem B446597 : Blo 295830 446597 := bbase (se 4 (by rfl) ⟨41868, by rfl⟩ : syracuseStep 446597 = 83737) (by norm_num)
theorem B446621 : Blo 295830 446621 := bbase (se 3 (by rfl) ⟨83741, by rfl⟩ : syracuseStep 446621 = 167483) (by norm_num)
theorem B512173 : Blo 295830 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B446645 : Blo 295830 446645 := bbase (se 5 (by rfl) ⟨20936, by rfl⟩ : syracuseStep 446645 = 41873) (by norm_num)
theorem B446669 : Blo 295830 446669 := bbase (se 3 (by rfl) ⟨83750, by rfl⟩ : syracuseStep 446669 = 167501) (by norm_num)
theorem B446693 : Blo 295830 446693 := bbase (se 4 (by rfl) ⟨41877, by rfl⟩ : syracuseStep 446693 = 83755) (by norm_num)
theorem B446717 : Blo 295830 446717 := bbase (se 3 (by rfl) ⟨83759, by rfl⟩ : syracuseStep 446717 = 167519) (by norm_num)
theorem B446741 : Blo 295830 446741 := bbase (se 6 (by rfl) ⟨10470, by rfl⟩ : syracuseStep 446741 = 20941) (by norm_num)
theorem B446765 : Blo 295830 446765 := bbase (se 3 (by rfl) ⟨83768, by rfl⟩ : syracuseStep 446765 = 167537) (by norm_num)
theorem B446789 : Blo 295830 446789 := bbase (se 4 (by rfl) ⟨41886, by rfl⟩ : syracuseStep 446789 = 83773) (by norm_num)
theorem B1134917 : Blo 295830 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B381277 : Blo 295830 381277 := bbase (se 3 (by rfl) ⟨71489, by rfl⟩ : syracuseStep 381277 = 142979) (by norm_num)
theorem B446813 : Blo 295830 446813 := bbase (se 3 (by rfl) ⟨83777, by rfl⟩ : syracuseStep 446813 = 167555) (by norm_num)
theorem B446837 : Blo 295830 446837 := bbase (se 5 (by rfl) ⟨20945, by rfl⟩ : syracuseStep 446837 = 41891) (by norm_num)
theorem B446861 : Blo 295830 446861 := bbase (se 3 (by rfl) ⟨83786, by rfl⟩ : syracuseStep 446861 = 167573) (by norm_num)
theorem B446885 : Blo 295830 446885 := bbase (se 4 (by rfl) ⟨41895, by rfl⟩ : syracuseStep 446885 = 83791) (by norm_num)
theorem B446909 : Blo 295830 446909 := bbase (se 3 (by rfl) ⟨83795, by rfl⟩ : syracuseStep 446909 = 167591) (by norm_num)
theorem B446933 : Blo 295830 446933 := bbase (se 7 (by rfl) ⟨5237, by rfl⟩ : syracuseStep 446933 = 10475) (by norm_num)
theorem B446957 : Blo 295830 446957 := bbase (se 3 (by rfl) ⟨83804, by rfl⟩ : syracuseStep 446957 = 167609) (by norm_num)
theorem B1004021 : Blo 295830 1004021 := bbase (se 5 (by rfl) ⟨47063, by rfl⟩ : syracuseStep 1004021 = 94127) (by norm_num)
theorem B807413 : Blo 295830 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B446981 : Blo 295830 446981 := bbase (se 4 (by rfl) ⟨41904, by rfl⟩ : syracuseStep 446981 = 83809) (by norm_num)
theorem B447005 : Blo 295830 447005 := bbase (se 3 (by rfl) ⟨83813, by rfl⟩ : syracuseStep 447005 = 167627) (by norm_num)
theorem B1921589 : Blo 295830 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B447029 : Blo 295830 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B447053 : Blo 295830 447053 := bbase (se 3 (by rfl) ⟨83822, by rfl⟩ : syracuseStep 447053 = 167645) (by norm_num)
theorem B447077 : Blo 295830 447077 := bbase (se 4 (by rfl) ⟨41913, by rfl⟩ : syracuseStep 447077 = 83827) (by norm_num)
theorem B1135205 : Blo 295830 1135205 := bbase (se 4 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 1135205 = 212851) (by norm_num)
theorem B447101 : Blo 295830 447101 := bbase (se 3 (by rfl) ⟨83831, by rfl⟩ : syracuseStep 447101 = 167663) (by norm_num)
theorem B447125 : Blo 295830 447125 := bbase (se 6 (by rfl) ⟨10479, by rfl⟩ : syracuseStep 447125 = 20959) (by norm_num)
theorem B316073 : Blo 295830 316073 := bbase (se 2 (by rfl) ⟨118527, by rfl⟩ : syracuseStep 316073 = 237055) (by norm_num)
theorem B447149 : Blo 295830 447149 := bbase (se 3 (by rfl) ⟨83840, by rfl⟩ : syracuseStep 447149 = 167681) (by norm_num)
theorem B447173 : Blo 295830 447173 := bbase (se 4 (by rfl) ⟨41922, by rfl⟩ : syracuseStep 447173 = 83845) (by norm_num)
theorem B1692373 : Blo 295830 1692373 := bbase (se 7 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 1692373 = 39665) (by norm_num)
theorem B447197 : Blo 295830 447197 := bbase (se 3 (by rfl) ⟨83849, by rfl⟩ : syracuseStep 447197 = 167699) (by norm_num)
theorem B447221 : Blo 295830 447221 := bbase (se 5 (by rfl) ⟨20963, by rfl⟩ : syracuseStep 447221 = 41927) (by norm_num)
theorem B447245 : Blo 295830 447245 := bbase (se 3 (by rfl) ⟨83858, by rfl⟩ : syracuseStep 447245 = 167717) (by norm_num)
theorem B447269 : Blo 295830 447269 := bbase (se 4 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 447269 = 83863) (by norm_num)
theorem B447293 : Blo 295830 447293 := bbase (se 3 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 447293 = 167735) (by norm_num)
theorem B447317 : Blo 295830 447317 := bbase (se 9 (by rfl) ⟨1310, by rfl⟩ : syracuseStep 447317 = 2621) (by norm_num)
theorem B316261 : Blo 295830 316261 := bbase (se 4 (by rfl) ⟨29649, by rfl⟩ : syracuseStep 316261 = 59299) (by norm_num)
theorem B447341 : Blo 295830 447341 := bbase (se 3 (by rfl) ⟨83876, by rfl⟩ : syracuseStep 447341 = 167753) (by norm_num)
theorem B447365 : Blo 295830 447365 := bbase (se 4 (by rfl) ⟨41940, by rfl⟩ : syracuseStep 447365 = 83881) (by norm_num)
theorem B676757 : Blo 295830 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B447389 : Blo 295830 447389 := bbase (se 3 (by rfl) ⟨83885, by rfl⟩ : syracuseStep 447389 = 167771) (by norm_num)
theorem B1004453 : Blo 295830 1004453 := bbase (se 4 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 1004453 = 188335) (by norm_num)
theorem B906149 : Blo 295830 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B447413 : Blo 295830 447413 := bbase (se 5 (by rfl) ⟨20972, by rfl⟩ : syracuseStep 447413 = 41945) (by norm_num)
theorem B447437 : Blo 295830 447437 := bbase (se 3 (by rfl) ⟨83894, by rfl⟩ : syracuseStep 447437 = 167789) (by norm_num)
theorem B447461 : Blo 295830 447461 := bbase (se 4 (by rfl) ⟨41949, by rfl⟩ : syracuseStep 447461 = 83899) (by norm_num)
theorem B447485 : Blo 295830 447485 := bbase (se 3 (by rfl) ⟨83903, by rfl⟩ : syracuseStep 447485 = 167807) (by norm_num)
theorem B447509 : Blo 295830 447509 := bbase (se 6 (by rfl) ⟨10488, by rfl⟩ : syracuseStep 447509 = 20977) (by norm_num)
theorem B447533 : Blo 295830 447533 := bbase (se 3 (by rfl) ⟨83912, by rfl⟩ : syracuseStep 447533 = 167825) (by norm_num)
theorem B447557 : Blo 295830 447557 := bbase (se 4 (by rfl) ⟨41958, by rfl⟩ : syracuseStep 447557 = 83917) (by norm_num)
theorem B447581 : Blo 295830 447581 := bbase (se 3 (by rfl) ⟨83921, by rfl⟩ : syracuseStep 447581 = 167843) (by norm_num)
theorem B447605 : Blo 295830 447605 := bbase (se 5 (by rfl) ⟨20981, by rfl⟩ : syracuseStep 447605 = 41963) (by norm_num)
theorem B447629 : Blo 295830 447629 := bbase (se 3 (by rfl) ⟨83930, by rfl⟩ : syracuseStep 447629 = 167861) (by norm_num)
theorem B1430693 : Blo 295830 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B447653 : Blo 295830 447653 := bbase (se 4 (by rfl) ⟨41967, by rfl⟩ : syracuseStep 447653 = 83935) (by norm_num)
theorem B447677 : Blo 295830 447677 := bbase (se 3 (by rfl) ⟨83939, by rfl⟩ : syracuseStep 447677 = 167879) (by norm_num)
theorem B447701 : Blo 295830 447701 := bbase (se 7 (by rfl) ⟨5246, by rfl⟩ : syracuseStep 447701 = 10493) (by norm_num)
theorem B447725 : Blo 295830 447725 := bbase (se 3 (by rfl) ⟨83948, by rfl⟩ : syracuseStep 447725 = 167897) (by norm_num)
theorem B447749 : Blo 295830 447749 := bbase (se 4 (by rfl) ⟨41976, by rfl⟩ : syracuseStep 447749 = 83953) (by norm_num)
theorem B447773 : Blo 295830 447773 := bbase (se 3 (by rfl) ⟨83957, by rfl⟩ : syracuseStep 447773 = 167915) (by norm_num)
theorem B447797 : Blo 295830 447797 := bbase (se 5 (by rfl) ⟨20990, by rfl⟩ : syracuseStep 447797 = 41981) (by norm_num)
theorem B447821 : Blo 295830 447821 := bbase (se 3 (by rfl) ⟨83966, by rfl⟩ : syracuseStep 447821 = 167933) (by norm_num)
theorem B1004885 : Blo 295830 1004885 := bbase (se 17 (by rfl) ⟨11, by rfl⟩ : syracuseStep 1004885 = 23) (by norm_num)
theorem B447845 : Blo 295830 447845 := bbase (se 4 (by rfl) ⟨41985, by rfl⟩ : syracuseStep 447845 = 83971) (by norm_num)
theorem B447869 : Blo 295830 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B1267093 : Blo 295830 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B447893 : Blo 295830 447893 := bbase (se 6 (by rfl) ⟨10497, by rfl⟩ : syracuseStep 447893 = 20995) (by norm_num)
theorem B447917 : Blo 295830 447917 := bbase (se 3 (by rfl) ⟨83984, by rfl⟩ : syracuseStep 447917 = 167969) (by norm_num)
theorem B447941 : Blo 295830 447941 := bbase (se 4 (by rfl) ⟨41994, by rfl⟩ : syracuseStep 447941 = 83989) (by norm_num)
theorem B447965 : Blo 295830 447965 := bbase (se 3 (by rfl) ⟨83993, by rfl⟩ : syracuseStep 447965 = 167987) (by norm_num)
theorem B447989 : Blo 295830 447989 := bbase (se 5 (by rfl) ⟨20999, by rfl⟩ : syracuseStep 447989 = 41999) (by norm_num)
theorem B1070597 : Blo 295830 1070597 := bbase (se 4 (by rfl) ⟨100368, by rfl⟩ : syracuseStep 1070597 = 200737) (by norm_num)
theorem B448013 : Blo 295830 448013 := bbase (se 3 (by rfl) ⟨84002, by rfl⟩ : syracuseStep 448013 = 168005) (by norm_num)
theorem B448037 : Blo 295830 448037 := bbase (se 4 (by rfl) ⟨42003, by rfl⟩ : syracuseStep 448037 = 84007) (by norm_num)
theorem B448061 : Blo 295830 448061 := bbase (se 3 (by rfl) ⟨84011, by rfl⟩ : syracuseStep 448061 = 168023) (by norm_num)
theorem B382529 : Blo 295830 382529 := bbase (se 2 (by rfl) ⟨143448, by rfl⟩ : syracuseStep 382529 = 286897) (by norm_num)
theorem B448085 : Blo 295830 448085 := bbase (se 8 (by rfl) ⟨2625, by rfl⟩ : syracuseStep 448085 = 5251) (by norm_num)
theorem B448109 : Blo 295830 448109 := bbase (se 3 (by rfl) ⟨84020, by rfl⟩ : syracuseStep 448109 = 168041) (by norm_num)
theorem B1070725 : Blo 295830 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B448133 : Blo 295830 448133 := bbase (se 4 (by rfl) ⟨42012, by rfl⟩ : syracuseStep 448133 = 84025) (by norm_num)
theorem B317081 : Blo 295830 317081 := bbase (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) (by norm_num)
theorem B448157 : Blo 295830 448157 := bbase (se 3 (by rfl) ⟨84029, by rfl⟩ : syracuseStep 448157 = 168059) (by norm_num)
theorem B448181 : Blo 295830 448181 := bbase (se 5 (by rfl) ⟨21008, by rfl⟩ : syracuseStep 448181 = 42017) (by norm_num)
theorem B448205 : Blo 295830 448205 := bbase (se 3 (by rfl) ⟨84038, by rfl⟩ : syracuseStep 448205 = 168077) (by norm_num)
theorem B448229 : Blo 295830 448229 := bbase (se 4 (by rfl) ⟨42021, by rfl⟩ : syracuseStep 448229 = 84043) (by norm_num)
theorem B448253 : Blo 295830 448253 := bbase (se 3 (by rfl) ⟨84047, by rfl⟩ : syracuseStep 448253 = 168095) (by norm_num)
theorem B1005317 : Blo 295830 1005317 := bbase (se 4 (by rfl) ⟨94248, by rfl⟩ : syracuseStep 1005317 = 188497) (by norm_num)
theorem B1136389 : Blo 295830 1136389 := bbase (se 4 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 1136389 = 213073) (by norm_num)
theorem B448277 : Blo 295830 448277 := bbase (se 6 (by rfl) ⟨10506, by rfl⟩ : syracuseStep 448277 = 21013) (by norm_num)
theorem B448301 : Blo 295830 448301 := bbase (se 3 (by rfl) ⟨84056, by rfl⟩ : syracuseStep 448301 = 168113) (by norm_num)
theorem B448325 : Blo 295830 448325 := bbase (se 4 (by rfl) ⟨42030, by rfl⟩ : syracuseStep 448325 = 84061) (by norm_num)
theorem B448349 : Blo 295830 448349 := bbase (se 3 (by rfl) ⟨84065, by rfl⟩ : syracuseStep 448349 = 168131) (by norm_num)
theorem B448373 : Blo 295830 448373 := bbase (se 5 (by rfl) ⟨21017, by rfl⟩ : syracuseStep 448373 = 42035) (by norm_num)
theorem B448397 : Blo 295830 448397 := bbase (se 3 (by rfl) ⟨84074, by rfl⟩ : syracuseStep 448397 = 168149) (by norm_num)
theorem B448421 : Blo 295830 448421 := bbase (se 4 (by rfl) ⟨42039, by rfl⟩ : syracuseStep 448421 = 84079) (by norm_num)
theorem B448445 : Blo 295830 448445 := bbase (se 3 (by rfl) ⟨84083, by rfl⟩ : syracuseStep 448445 = 168167) (by norm_num)
theorem B448469 : Blo 295830 448469 := bbase (se 7 (by rfl) ⟨5255, by rfl⟩ : syracuseStep 448469 = 10511) (by norm_num)
theorem B448493 : Blo 295830 448493 := bbase (se 3 (by rfl) ⟨84092, by rfl⟩ : syracuseStep 448493 = 168185) (by norm_num)
theorem B448517 : Blo 295830 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B448541 : Blo 295830 448541 := bbase (se 3 (by rfl) ⟨84101, by rfl⟩ : syracuseStep 448541 = 168203) (by norm_num)
theorem B448565 : Blo 295830 448565 := bbase (se 5 (by rfl) ⟨21026, by rfl⟩ : syracuseStep 448565 = 42053) (by norm_num)
theorem B1136693 : Blo 295830 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B448589 : Blo 295830 448589 := bbase (se 3 (by rfl) ⟨84110, by rfl⟩ : syracuseStep 448589 = 168221) (by norm_num)
theorem B317525 : Blo 295830 317525 := bbase (se 8 (by rfl) ⟨1860, by rfl⟩ : syracuseStep 317525 = 3721) (by norm_num)
theorem B448613 : Blo 295830 448613 := bbase (se 4 (by rfl) ⟨42057, by rfl⟩ : syracuseStep 448613 = 84115) (by norm_num)
theorem B448637 : Blo 295830 448637 := bbase (se 3 (by rfl) ⟨84119, by rfl⟩ : syracuseStep 448637 = 168239) (by norm_num)
theorem B448661 : Blo 295830 448661 := bbase (se 6 (by rfl) ⟨10515, by rfl⟩ : syracuseStep 448661 = 21031) (by norm_num)
theorem B448685 : Blo 295830 448685 := bbase (se 3 (by rfl) ⟨84128, by rfl⟩ : syracuseStep 448685 = 168257) (by norm_num)
theorem B1005749 : Blo 295830 1005749 := bbase (se 5 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 1005749 = 94289) (by norm_num)
theorem B448709 : Blo 295830 448709 := bbase (se 4 (by rfl) ⟨42066, by rfl⟩ : syracuseStep 448709 = 84133) (by norm_num)
theorem B547021 : Blo 295830 547021 := bbase (se 3 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 547021 = 205133) (by norm_num)
theorem B448733 : Blo 295830 448733 := bbase (se 3 (by rfl) ⟨84137, by rfl⟩ : syracuseStep 448733 = 168275) (by norm_num)
theorem B448757 : Blo 295830 448757 := bbase (se 5 (by rfl) ⟨21035, by rfl⟩ : syracuseStep 448757 = 42071) (by norm_num)
theorem B448781 : Blo 295830 448781 := bbase (se 3 (by rfl) ⟨84146, by rfl⟩ : syracuseStep 448781 = 168293) (by norm_num)
theorem B448805 : Blo 295830 448805 := bbase (se 4 (by rfl) ⟨42075, by rfl⟩ : syracuseStep 448805 = 84151) (by norm_num)
theorem B448829 : Blo 295830 448829 := bbase (se 3 (by rfl) ⟨84155, by rfl⟩ : syracuseStep 448829 = 168311) (by norm_num)
theorem B317773 : Blo 295830 317773 := bbase (se 3 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 317773 = 119165) (by norm_num)
theorem B18340181 : Blo 295830 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B448853 : Blo 295830 448853 := bbase (se 10 (by rfl) ⟨657, by rfl⟩ : syracuseStep 448853 = 1315) (by norm_num)
theorem B448877 : Blo 295830 448877 := bbase (se 3 (by rfl) ⟨84164, by rfl⟩ : syracuseStep 448877 = 168329) (by norm_num)
theorem B448901 : Blo 295830 448901 := bbase (se 4 (by rfl) ⟨42084, by rfl⟩ : syracuseStep 448901 = 84169) (by norm_num)
theorem B448925 : Blo 295830 448925 := bbase (se 3 (by rfl) ⟨84173, by rfl⟩ : syracuseStep 448925 = 168347) (by norm_num)
theorem B383401 : Blo 295830 383401 := bbase (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) (by norm_num)
theorem B448949 : Blo 295830 448949 := bbase (se 5 (by rfl) ⟨21044, by rfl⟩ : syracuseStep 448949 = 42089) (by norm_num)
theorem B448973 : Blo 295830 448973 := bbase (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) (by norm_num)
theorem B448997 : Blo 295830 448997 := bbase (se 4 (by rfl) ⟨42093, by rfl⟩ : syracuseStep 448997 = 84187) (by norm_num)
theorem B449021 : Blo 295830 449021 := bbase (se 3 (by rfl) ⟨84191, by rfl⟩ : syracuseStep 449021 = 168383) (by norm_num)
theorem B449045 : Blo 295830 449045 := bbase (se 6 (by rfl) ⟨10524, by rfl⟩ : syracuseStep 449045 = 21049) (by norm_num)
theorem B449069 : Blo 295830 449069 := bbase (se 3 (by rfl) ⟨84200, by rfl⟩ : syracuseStep 449069 = 168401) (by norm_num)
theorem B449093 : Blo 295830 449093 := bbase (se 4 (by rfl) ⟨42102, by rfl⟩ : syracuseStep 449093 = 84205) (by norm_num)
theorem B449117 : Blo 295830 449117 := bbase (se 3 (by rfl) ⟨84209, by rfl⟩ : syracuseStep 449117 = 168419) (by norm_num)
theorem B1006181 : Blo 295830 1006181 := bbase (se 4 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 1006181 = 188659) (by norm_num)
theorem B449141 : Blo 295830 449141 := bbase (se 5 (by rfl) ⟨21053, by rfl⟩ : syracuseStep 449141 = 42107) (by norm_num)
theorem B449165 : Blo 295830 449165 := bbase (se 3 (by rfl) ⟨84218, by rfl⟩ : syracuseStep 449165 = 168437) (by norm_num)
theorem B1694357 : Blo 295830 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B613021 : Blo 295830 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B940709 : Blo 295830 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B449189 : Blo 295830 449189 := bbase (se 4 (by rfl) ⟨42111, by rfl⟩ : syracuseStep 449189 = 84223) (by norm_num)
theorem B449213 : Blo 295830 449213 := bbase (se 3 (by rfl) ⟨84227, by rfl⟩ : syracuseStep 449213 = 168455) (by norm_num)
theorem B449237 : Blo 295830 449237 := bbase (se 7 (by rfl) ⟨5264, by rfl⟩ : syracuseStep 449237 = 10529) (by norm_num)
theorem B449261 : Blo 295830 449261 := bbase (se 3 (by rfl) ⟨84236, by rfl⟩ : syracuseStep 449261 = 168473) (by norm_num)
theorem B318205 : Blo 295830 318205 := bbase (se 3 (by rfl) ⟨59663, by rfl⟩ : syracuseStep 318205 = 119327) (by norm_num)
theorem B449285 : Blo 295830 449285 := bbase (se 4 (by rfl) ⟨42120, by rfl⟩ : syracuseStep 449285 = 84241) (by norm_num)
theorem B449309 : Blo 295830 449309 := bbase (se 3 (by rfl) ⟨84245, by rfl⟩ : syracuseStep 449309 = 168491) (by norm_num)
theorem B449333 : Blo 295830 449333 := bbase (se 5 (by rfl) ⟨21062, by rfl⟩ : syracuseStep 449333 = 42125) (by norm_num)
theorem B318277 : Blo 295830 318277 := bbase (se 4 (by rfl) ⟨29838, by rfl⟩ : syracuseStep 318277 = 59677) (by norm_num)
theorem B449357 : Blo 295830 449357 := bbase (se 3 (by rfl) ⟨84254, by rfl⟩ : syracuseStep 449357 = 168509) (by norm_num)
theorem B1268581 : Blo 295830 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B449381 : Blo 295830 449381 := bbase (se 4 (by rfl) ⟨42129, by rfl⟩ : syracuseStep 449381 = 84259) (by norm_num)
theorem B2251637 : Blo 295830 2251637 := bbase (se 5 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 2251637 = 211091) (by norm_num)
theorem B1268597 : Blo 295830 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B449405 : Blo 295830 449405 := bbase (se 3 (by rfl) ⟨84263, by rfl⟩ : syracuseStep 449405 = 168527) (by norm_num)
theorem B449429 : Blo 295830 449429 := bbase (se 6 (by rfl) ⟨10533, by rfl⟩ : syracuseStep 449429 = 21067) (by norm_num)
theorem B449453 : Blo 295830 449453 := bbase (se 3 (by rfl) ⟨84272, by rfl⟩ : syracuseStep 449453 = 168545) (by norm_num)
theorem B449477 : Blo 295830 449477 := bbase (se 4 (by rfl) ⟨42138, by rfl⟩ : syracuseStep 449477 = 84277) (by norm_num)
theorem B449501 : Blo 295830 449501 := bbase (se 3 (by rfl) ⟨84281, by rfl⟩ : syracuseStep 449501 = 168563) (by norm_num)
theorem B449525 : Blo 295830 449525 := bbase (se 5 (by rfl) ⟨21071, by rfl⟩ : syracuseStep 449525 = 42143) (by norm_num)
theorem B449549 : Blo 295830 449549 := bbase (se 3 (by rfl) ⟨84290, by rfl⟩ : syracuseStep 449549 = 168581) (by norm_num)
theorem B1006613 : Blo 295830 1006613 := bbase (se 6 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 1006613 = 47185) (by norm_num)
theorem B449573 : Blo 295830 449573 := bbase (se 4 (by rfl) ⟨42147, by rfl⟩ : syracuseStep 449573 = 84295) (by norm_num)
theorem B449597 : Blo 295830 449597 := bbase (se 3 (by rfl) ⟨84299, by rfl⟩ : syracuseStep 449597 = 168599) (by norm_num)
theorem B449621 : Blo 295830 449621 := bbase (se 8 (by rfl) ⟨2634, by rfl⟩ : syracuseStep 449621 = 5269) (by norm_num)
theorem B449645 : Blo 295830 449645 := bbase (se 3 (by rfl) ⟨84308, by rfl⟩ : syracuseStep 449645 = 168617) (by norm_num)
theorem B449669 : Blo 295830 449669 := bbase (se 4 (by rfl) ⟨42156, by rfl⟩ : syracuseStep 449669 = 84313) (by norm_num)
theorem B908437 : Blo 295830 908437 := bbase (se 6 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 908437 = 42583) (by norm_num)
theorem B449693 : Blo 295830 449693 := bbase (se 3 (by rfl) ⟨84317, by rfl⟩ : syracuseStep 449693 = 168635) (by norm_num)
theorem B449717 : Blo 295830 449717 := bbase (se 5 (by rfl) ⟨21080, by rfl⟩ : syracuseStep 449717 = 42161) (by norm_num)
theorem B318649 : Blo 295830 318649 := bbase (se 2 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 318649 = 238987) (by norm_num)
theorem B449741 : Blo 295830 449741 := bbase (se 3 (by rfl) ⟨84326, by rfl⟩ : syracuseStep 449741 = 168653) (by norm_num)
theorem B1007045 : Blo 295830 1007045 := bbase (se 4 (by rfl) ⟨94410, by rfl⟩ : syracuseStep 1007045 = 188821) (by norm_num)
theorem B712165 : Blo 295830 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B1498661 : Blo 295830 1498661 := bbase (se 4 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 1498661 = 280999) (by norm_num)
theorem B319025 : Blo 295830 319025 := bbase (se 2 (by rfl) ⟨119634, by rfl⟩ : syracuseStep 319025 = 239269) (by norm_num)
theorem B843317 : Blo 295830 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B319097 : Blo 295830 319097 := bbase (se 2 (by rfl) ⟨119661, by rfl⟩ : syracuseStep 319097 = 239323) (by norm_num)
theorem B319285 : Blo 295830 319285 := bbase (se 5 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 319285 = 29933) (by norm_num)
theorem B1007477 : Blo 295830 1007477 := bbase (se 5 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 1007477 = 94451) (by norm_num)
theorem B1433477 : Blo 295830 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B450461 : Blo 295830 450461 := bbase (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) (by norm_num)
theorem B319469 : Blo 295830 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B712837 : Blo 295830 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B647317 : Blo 295830 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B1007909 : Blo 295830 1007909 := bbase (se 4 (by rfl) ⟨94491, by rfl⟩ : syracuseStep 1007909 = 188983) (by norm_num)
theorem B909605 : Blo 295830 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B713069 : Blo 295830 713069 := bbase (se 3 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 713069 = 267401) (by norm_num)
theorem B713117 : Blo 295830 713117 := bbase (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) (by norm_num)
theorem B582061 : Blo 295830 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B844501 : Blo 295830 844501 := bbase (se 7 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 844501 = 19793) (by norm_num)
theorem B1008341 : Blo 295830 1008341 := bbase (se 7 (by rfl) ⟨11816, by rfl⟩ : syracuseStep 1008341 = 23633) (by norm_num)
theorem B1499957 : Blo 295830 1499957 := bbase (se 5 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 1499957 = 140621) (by norm_num)
theorem B1696565 : Blo 295830 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B844661 : Blo 295830 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B1369045 : Blo 295830 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B1270853 : Blo 295830 1270853 := bbase (se 4 (by rfl) ⟨119142, by rfl⟩ : syracuseStep 1270853 = 238285) (by norm_num)
theorem B844901 : Blo 295830 844901 := bbase (se 4 (by rfl) ⟨79209, by rfl⟩ : syracuseStep 844901 = 158419) (by norm_num)
theorem B1008773 : Blo 295830 1008773 := bbase (se 4 (by rfl) ⟨94572, by rfl⟩ : syracuseStep 1008773 = 189145) (by norm_num)
theorem B845093 : Blo 295830 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B1009205 : Blo 295830 1009205 := bbase (se 5 (by rfl) ⟨47306, by rfl⟩ : syracuseStep 1009205 = 94613) (by norm_num)
theorem B452261 : Blo 295830 452261 := bbase (se 4 (by rfl) ⟨42399, by rfl⟩ : syracuseStep 452261 = 84799) (by norm_num)
theorem B714509 : Blo 295830 714509 := bbase (se 3 (by rfl) ⟨133970, by rfl⟩ : syracuseStep 714509 = 267941) (by norm_num)
theorem B4351765 : Blo 295830 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B714701 : Blo 295830 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B485333 : Blo 295830 485333 := bbase (se 7 (by rfl) ⟨5687, by rfl⟩ : syracuseStep 485333 = 11375) (by norm_num)
theorem B1009637 : Blo 295830 1009637 := bbase (se 4 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 1009637 = 189307) (by norm_num)
theorem B1501253 : Blo 295830 1501253 := bbase (se 4 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 1501253 = 281485) (by norm_num)
theorem B846085 : Blo 295830 846085 := bbase (se 4 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 846085 = 158641) (by norm_num)
theorem B1010069 : Blo 295830 1010069 := bbase (se 6 (by rfl) ⟨23673, by rfl⟩ : syracuseStep 1010069 = 47347) (by norm_num)
theorem B682597 : Blo 295830 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B1010501 : Blo 295830 1010501 := bbase (se 4 (by rfl) ⟨94734, by rfl⟩ : syracuseStep 1010501 = 189469) (by norm_num)
theorem B2616533 : Blo 295830 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B453853 : Blo 295830 453853 := bbase (se 3 (by rfl) ⟨85097, by rfl⟩ : syracuseStep 453853 = 170195) (by norm_num)
theorem B1010933 : Blo 295830 1010933 := bbase (se 5 (by rfl) ⟨47387, by rfl⟩ : syracuseStep 1010933 = 94775) (by norm_num)
theorem B748885 : Blo 295830 748885 := bbase (se 11 (by rfl) ⟨548, by rfl⟩ : syracuseStep 748885 = 1097) (by norm_num)
theorem B1502549 : Blo 295830 1502549 := bbase (se 11 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 1502549 = 2201) (by norm_num)
theorem B847189 : Blo 295830 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B421237 : Blo 295830 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B748997 : Blo 295830 748997 := bbase (se 4 (by rfl) ⟨70218, by rfl⟩ : syracuseStep 748997 = 140437) (by norm_num)
theorem B421357 : Blo 295830 421357 := bbase (se 3 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 421357 = 158009) (by norm_num)
theorem B355909 : Blo 295830 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B421453 : Blo 295830 421453 := bbase (se 3 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 421453 = 158045) (by norm_num)
theorem B355957 : Blo 295830 355957 := bbase (se 5 (by rfl) ⟨16685, by rfl⟩ : syracuseStep 355957 = 33371) (by norm_num)
theorem B749189 : Blo 295830 749189 := bbase (se 4 (by rfl) ⟨70236, by rfl⟩ : syracuseStep 749189 = 140473) (by norm_num)
theorem B1011365 : Blo 295830 1011365 := bbase (se 4 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 1011365 = 189631) (by norm_num)
theorem B683765 : Blo 295830 683765 := bbase (se 5 (by rfl) ⟨32051, by rfl⟩ : syracuseStep 683765 = 64103) (by norm_num)
theorem B323357 : Blo 295830 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B716701 : Blo 295830 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B749533 : Blo 295830 749533 := bbase (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) (by norm_num)
theorem B421949 : Blo 295830 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B749645 : Blo 295830 749645 := bbase (se 3 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 749645 = 281117) (by norm_num)
theorem B1011797 : Blo 295830 1011797 := bbase (se 8 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 1011797 = 11857) (by norm_num)
theorem B749837 : Blo 295830 749837 := bbase (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) (by norm_num)
theorem B3207509 : Blo 295830 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B454997 : Blo 295830 454997 := bbase (se 10 (by rfl) ⟨666, by rfl⟩ : syracuseStep 454997 = 1333) (by norm_num)
theorem B717277 : Blo 295830 717277 := bbase (se 3 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 717277 = 268979) (by norm_num)
theorem B1896949 : Blo 295830 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B750181 : Blo 295830 750181 := bbase (se 4 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 750181 = 140659) (by norm_num)
theorem B422501 : Blo 295830 422501 := bbase (se 4 (by rfl) ⟨39609, by rfl⟩ : syracuseStep 422501 = 79219) (by norm_num)
theorem B1503845 : Blo 295830 1503845 := bbase (se 4 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 1503845 = 281971) (by norm_num)
theorem B357005 : Blo 295830 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B750293 : Blo 295830 750293 := bbase (se 7 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 750293 = 17585) (by norm_num)
theorem B389873 : Blo 295830 389873 := bbase (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) (by norm_num)
theorem B717605 : Blo 295830 717605 := bbase (se 4 (by rfl) ⟨67275, by rfl⟩ : syracuseStep 717605 = 134551) (by norm_num)
theorem B848693 : Blo 295830 848693 := bbase (se 5 (by rfl) ⟨39782, by rfl⟩ : syracuseStep 848693 = 79565) (by norm_num)
theorem B717661 : Blo 295830 717661 := bbase (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) (by norm_num)
theorem B750485 : Blo 295830 750485 := bbase (se 6 (by rfl) ⟨17589, by rfl⟩ : syracuseStep 750485 = 35179) (by norm_num)
theorem B357313 : Blo 295830 357313 := bbase (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) (by norm_num)
theorem B1274885 : Blo 295830 1274885 := bbase (se 4 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 1274885 = 239041) (by norm_num)
theorem B717893 : Blo 295830 717893 := bbase (se 4 (by rfl) ⟨67302, by rfl⟩ : syracuseStep 717893 = 134605) (by norm_num)
theorem B357481 : Blo 295830 357481 := bbase (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) (by norm_num)
theorem B750829 : Blo 295830 750829 := bbase (se 3 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 750829 = 281561) (by norm_num)
theorem B718085 : Blo 295830 718085 := bbase (se 4 (by rfl) ⟨67320, by rfl⟩ : syracuseStep 718085 = 134641) (by norm_num)
theorem B3241237 : Blo 295830 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B357677 : Blo 295830 357677 := bbase (se 3 (by rfl) ⟨67064, by rfl⟩ : syracuseStep 357677 = 134129) (by norm_num)
theorem B423253 : Blo 295830 423253 := bbase (se 13 (by rfl) ⟨77, by rfl⟩ : syracuseStep 423253 = 155) (by norm_num)
theorem B3437909 : Blo 295830 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B750941 : Blo 295830 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B751133 : Blo 295830 751133 := bbase (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) (by norm_num)
theorem B1210085 : Blo 295830 1210085 := bbase (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) (by norm_num)
theorem B751477 : Blo 295830 751477 := bbase (se 5 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 751477 = 70451) (by norm_num)
theorem B1505141 : Blo 295830 1505141 := bbase (se 5 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 1505141 = 141107) (by norm_num)
theorem B751589 : Blo 295830 751589 := bbase (se 4 (by rfl) ⟨70461, by rfl⟩ : syracuseStep 751589 = 140923) (by norm_num)
theorem B1439765 : Blo 295830 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B424045 : Blo 295830 424045 := bbase (se 3 (by rfl) ⟨79508, by rfl⟩ : syracuseStep 424045 = 159017) (by norm_num)
theorem B751781 : Blo 295830 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B719045 : Blo 295830 719045 := bbase (se 4 (by rfl) ⟨67410, by rfl⟩ : syracuseStep 719045 = 134821) (by norm_num)
theorem B850277 : Blo 295830 850277 := bbase (se 4 (by rfl) ⟨79713, by rfl⟩ : syracuseStep 850277 = 159427) (by norm_num)
theorem B424381 : Blo 295830 424381 := bbase (se 3 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 424381 = 159143) (by norm_num)
theorem B2259413 : Blo 295830 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B752125 : Blo 295830 752125 := bbase (se 3 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 752125 = 282047) (by norm_num)
theorem B752237 : Blo 295830 752237 := bbase (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) (by norm_num)
theorem B424597 : Blo 295830 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B457445 : Blo 295830 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B1276661 : Blo 295830 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B752429 : Blo 295830 752429 := bbase (se 3 (by rfl) ⟨141080, by rfl⟩ : syracuseStep 752429 = 282161) (by norm_num)
theorem B359249 : Blo 295830 359249 := bbase (se 2 (by rfl) ⟨134718, by rfl⟩ : syracuseStep 359249 = 269437) (by norm_num)
theorem B359273 : Blo 295830 359273 := bbase (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) (by norm_num)
theorem B850949 : Blo 295830 850949 := bbase (se 4 (by rfl) ⟨79776, by rfl⟩ : syracuseStep 850949 = 159553) (by norm_num)
theorem B424973 : Blo 295830 424973 := bbase (se 3 (by rfl) ⟨79682, by rfl⟩ : syracuseStep 424973 = 159365) (by norm_num)
theorem B326741 : Blo 295830 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B752773 : Blo 295830 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B1506437 : Blo 295830 1506437 := bbase (se 4 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 1506437 = 282457) (by norm_num)
theorem B359581 : Blo 295830 359581 := bbase (se 3 (by rfl) ⟨67421, by rfl⟩ : syracuseStep 359581 = 134843) (by norm_num)
theorem B752885 : Blo 295830 752885 := bbase (se 5 (by rfl) ⟨35291, by rfl⟩ : syracuseStep 752885 = 70583) (by norm_num)
theorem B359753 : Blo 295830 359753 := bbase (se 2 (by rfl) ⟨134907, by rfl⟩ : syracuseStep 359753 = 269815) (by norm_num)
theorem B753077 : Blo 295830 753077 := bbase (se 5 (by rfl) ⟨35300, by rfl⟩ : syracuseStep 753077 = 70601) (by norm_num)
theorem B851381 : Blo 295830 851381 := bbase (se 5 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 851381 = 79817) (by norm_num)
theorem B359869 : Blo 295830 359869 := bbase (se 3 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 359869 = 134951) (by norm_num)
theorem B359965 : Blo 295830 359965 := bbase (se 3 (by rfl) ⟨67493, by rfl⟩ : syracuseStep 359965 = 134987) (by norm_num)
theorem B2555509 : Blo 295830 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B491165 : Blo 295830 491165 := bbase (se 3 (by rfl) ⟨92093, by rfl⟩ : syracuseStep 491165 = 184187) (by norm_num)
theorem B360109 : Blo 295830 360109 := bbase (se 3 (by rfl) ⟨67520, by rfl⟩ : syracuseStep 360109 = 135041) (by norm_num)
theorem B1277653 : Blo 295830 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B753421 : Blo 295830 753421 := bbase (se 3 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 753421 = 282533) (by norm_num)
theorem B753533 : Blo 295830 753533 := bbase (se 3 (by rfl) ⟨141287, by rfl⟩ : syracuseStep 753533 = 282575) (by norm_num)
theorem B753745 : Blo 295830 753745 := bstep (se 2 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 753745 = 565309) B565309
theorem B1441955 : Blo 295830 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B950449 : Blo 295830 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B459059 : Blo 295830 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B426323 : Blo 295830 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B754019 : Blo 295830 754019 := bstep (se 1 (by rfl) ⟨565514, by rfl⟩ : syracuseStep 754019 = 1131029) B1131029
theorem B754211 : Blo 295830 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B1213325 : Blo 295830 1213325 := bstep (se 3 (by rfl) ⟨227498, by rfl⟩ : syracuseStep 1213325 = 454997) B454997
theorem B295843 : Blo 295830 295843 := bstep (se 1 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 295843 = 443765) B443765
theorem B721841 : Blo 295830 721841 := bstep (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) B541381
theorem B295859 : Blo 295830 295859 := bstep (se 1 (by rfl) ⟨221894, by rfl⟩ : syracuseStep 295859 = 443789) B443789
theorem B295875 : Blo 295830 295875 := bstep (se 1 (by rfl) ⟨221906, by rfl⟩ : syracuseStep 295875 = 443813) B443813
theorem B295891 : Blo 295830 295891 := bstep (se 1 (by rfl) ⟨221918, by rfl⟩ : syracuseStep 295891 = 443837) B443837
theorem B295907 : Blo 295830 295907 := bstep (se 1 (by rfl) ⟨221930, by rfl⟩ : syracuseStep 295907 = 443861) B443861
theorem B295923 : Blo 295830 295923 := bstep (se 1 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 295923 = 443885) B443885
theorem B295939 : Blo 295830 295939 := bstep (se 1 (by rfl) ⟨221954, by rfl⟩ : syracuseStep 295939 = 443909) B443909
theorem B295955 : Blo 295830 295955 := bstep (se 1 (by rfl) ⟨221966, by rfl⟩ : syracuseStep 295955 = 443933) B443933
theorem B295971 : Blo 295830 295971 := bstep (se 1 (by rfl) ⟨221978, by rfl⟩ : syracuseStep 295971 = 443957) B443957
theorem B1704995 : Blo 295830 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B295987 : Blo 295830 295987 := bstep (se 1 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 295987 = 443981) B443981
theorem B296003 : Blo 295830 296003 := bstep (se 1 (by rfl) ⟨222002, by rfl⟩ : syracuseStep 296003 = 444005) B444005
theorem B296019 : Blo 295830 296019 := bstep (se 1 (by rfl) ⟨222014, by rfl⟩ : syracuseStep 296019 = 444029) B444029
theorem B296035 : Blo 295830 296035 := bstep (se 1 (by rfl) ⟨222026, by rfl⟩ : syracuseStep 296035 = 444053) B444053
theorem B296051 : Blo 295830 296051 := bstep (se 1 (by rfl) ⟨222038, by rfl⟩ : syracuseStep 296051 = 444077) B444077
theorem B296067 : Blo 295830 296067 := bstep (se 1 (by rfl) ⟨222050, by rfl⟩ : syracuseStep 296067 = 444101) B444101
theorem B296083 : Blo 295830 296083 := bstep (se 1 (by rfl) ⟨222062, by rfl⟩ : syracuseStep 296083 = 444125) B444125
theorem B296099 : Blo 295830 296099 := bstep (se 1 (by rfl) ⟨222074, by rfl⟩ : syracuseStep 296099 = 444149) B444149
theorem B1082531 : Blo 295830 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B296115 : Blo 295830 296115 := bstep (se 1 (by rfl) ⟨222086, by rfl⟩ : syracuseStep 296115 = 444173) B444173
theorem B296131 : Blo 295830 296131 := bstep (se 1 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 296131 = 444197) B444197
theorem B296147 : Blo 295830 296147 := bstep (se 1 (by rfl) ⟨222110, by rfl⟩ : syracuseStep 296147 = 444221) B444221
theorem B296163 : Blo 295830 296163 := bstep (se 1 (by rfl) ⟨222122, by rfl⟩ : syracuseStep 296163 = 444245) B444245
theorem B296179 : Blo 295830 296179 := bstep (se 1 (by rfl) ⟨222134, by rfl⟩ : syracuseStep 296179 = 444269) B444269
theorem B296195 : Blo 295830 296195 := bstep (se 1 (by rfl) ⟨222146, by rfl⟩ : syracuseStep 296195 = 444293) B444293
theorem B296211 : Blo 295830 296211 := bstep (se 1 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 296211 = 444317) B444317
theorem B296227 : Blo 295830 296227 := bstep (se 1 (by rfl) ⟨222170, by rfl⟩ : syracuseStep 296227 = 444341) B444341
theorem B296243 : Blo 295830 296243 := bstep (se 1 (by rfl) ⟨222182, by rfl⟩ : syracuseStep 296243 = 444365) B444365
theorem B296259 : Blo 295830 296259 := bstep (se 1 (by rfl) ⟨222194, by rfl⟩ : syracuseStep 296259 = 444389) B444389
theorem B296275 : Blo 295830 296275 := bstep (se 1 (by rfl) ⟨222206, by rfl⟩ : syracuseStep 296275 = 444413) B444413
theorem B296291 : Blo 295830 296291 := bstep (se 1 (by rfl) ⟨222218, by rfl⟩ : syracuseStep 296291 = 444437) B444437
theorem B296307 : Blo 295830 296307 := bstep (se 1 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 296307 = 444461) B444461
theorem B296323 : Blo 295830 296323 := bstep (se 1 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 296323 = 444485) B444485
theorem B296339 : Blo 295830 296339 := bstep (se 1 (by rfl) ⟨222254, by rfl⟩ : syracuseStep 296339 = 444509) B444509
theorem B296355 : Blo 295830 296355 := bstep (se 1 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 296355 = 444533) B444533
theorem B296371 : Blo 295830 296371 := bstep (se 1 (by rfl) ⟨222278, by rfl⟩ : syracuseStep 296371 = 444557) B444557
theorem B296387 : Blo 295830 296387 := bstep (se 1 (by rfl) ⟨222290, by rfl⟩ : syracuseStep 296387 = 444581) B444581
theorem B755153 : Blo 295830 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B296403 : Blo 295830 296403 := bstep (se 1 (by rfl) ⟨222302, by rfl⟩ : syracuseStep 296403 = 444605) B444605
theorem B296419 : Blo 295830 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B296435 : Blo 295830 296435 := bstep (se 1 (by rfl) ⟨222326, by rfl⟩ : syracuseStep 296435 = 444653) B444653
theorem B296451 : Blo 295830 296451 := bstep (se 1 (by rfl) ⟨222338, by rfl⟩ : syracuseStep 296451 = 444677) B444677
theorem B755203 : Blo 295830 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B296467 : Blo 295830 296467 := bstep (se 1 (by rfl) ⟨222350, by rfl⟩ : syracuseStep 296467 = 444701) B444701
theorem B296483 : Blo 295830 296483 := bstep (se 1 (by rfl) ⟨222362, by rfl⟩ : syracuseStep 296483 = 444725) B444725
theorem B296499 : Blo 295830 296499 := bstep (se 1 (by rfl) ⟨222374, by rfl⟩ : syracuseStep 296499 = 444749) B444749
theorem B296515 : Blo 295830 296515 := bstep (se 1 (by rfl) ⟨222386, by rfl⟩ : syracuseStep 296515 = 444773) B444773
theorem B296531 : Blo 295830 296531 := bstep (se 1 (by rfl) ⟨222398, by rfl⟩ : syracuseStep 296531 = 444797) B444797
theorem B296547 : Blo 295830 296547 := bstep (se 1 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 296547 = 444821) B444821
theorem B1279601 : Blo 295830 1279601 := bstep (se 2 (by rfl) ⟨479850, by rfl⟩ : syracuseStep 1279601 = 959701) B959701
theorem B296563 : Blo 295830 296563 := bstep (se 1 (by rfl) ⟨222422, by rfl⟩ : syracuseStep 296563 = 444845) B444845
theorem B296579 : Blo 295830 296579 := bstep (se 1 (by rfl) ⟨222434, by rfl⟩ : syracuseStep 296579 = 444869) B444869
theorem B755345 : Blo 295830 755345 := bstep (se 2 (by rfl) ⟨283254, by rfl⟩ : syracuseStep 755345 = 566509) B566509
theorem B853649 : Blo 295830 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B296595 : Blo 295830 296595 := bstep (se 1 (by rfl) ⟨222446, by rfl⟩ : syracuseStep 296595 = 444893) B444893
theorem B296611 : Blo 295830 296611 := bstep (se 1 (by rfl) ⟨222458, by rfl⟩ : syracuseStep 296611 = 444917) B444917
theorem B296627 : Blo 295830 296627 := bstep (se 1 (by rfl) ⟨222470, by rfl⟩ : syracuseStep 296627 = 444941) B444941
theorem B296643 : Blo 295830 296643 := bstep (se 1 (by rfl) ⟨222482, by rfl⟩ : syracuseStep 296643 = 444965) B444965
theorem B952013 : Blo 295830 952013 := bstep (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) B357005
theorem B296659 : Blo 295830 296659 := bstep (se 1 (by rfl) ⟨222494, by rfl⟩ : syracuseStep 296659 = 444989) B444989
theorem B296675 : Blo 295830 296675 := bstep (se 1 (by rfl) ⟨222506, by rfl⟩ : syracuseStep 296675 = 445013) B445013
theorem B296691 : Blo 295830 296691 := bstep (se 1 (by rfl) ⟨222518, by rfl⟩ : syracuseStep 296691 = 445037) B445037
theorem B296707 : Blo 295830 296707 := bstep (se 1 (by rfl) ⟨222530, by rfl⟩ : syracuseStep 296707 = 445061) B445061
theorem B296723 : Blo 295830 296723 := bstep (se 1 (by rfl) ⟨222542, by rfl⟩ : syracuseStep 296723 = 445085) B445085
theorem B296739 : Blo 295830 296739 := bstep (se 1 (by rfl) ⟨222554, by rfl⟩ : syracuseStep 296739 = 445109) B445109
theorem B296755 : Blo 295830 296755 := bstep (se 1 (by rfl) ⟨222566, by rfl⟩ : syracuseStep 296755 = 445133) B445133
theorem B296771 : Blo 295830 296771 := bstep (se 1 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 296771 = 445157) B445157
theorem B296787 : Blo 295830 296787 := bstep (se 1 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 296787 = 445181) B445181
theorem B296803 : Blo 295830 296803 := bstep (se 1 (by rfl) ⟨222602, by rfl⟩ : syracuseStep 296803 = 445205) B445205
theorem B296819 : Blo 295830 296819 := bstep (se 1 (by rfl) ⟨222614, by rfl⟩ : syracuseStep 296819 = 445229) B445229
theorem B296835 : Blo 295830 296835 := bstep (se 1 (by rfl) ⟨222626, by rfl⟩ : syracuseStep 296835 = 445253) B445253
theorem B296851 : Blo 295830 296851 := bstep (se 1 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 296851 = 445277) B445277
theorem B296867 : Blo 295830 296867 := bstep (se 1 (by rfl) ⟨222650, by rfl⟩ : syracuseStep 296867 = 445301) B445301
theorem B296883 : Blo 295830 296883 := bstep (se 1 (by rfl) ⟨222662, by rfl⟩ : syracuseStep 296883 = 445325) B445325
theorem B296899 : Blo 295830 296899 := bstep (se 1 (by rfl) ⟨222674, by rfl⟩ : syracuseStep 296899 = 445349) B445349
theorem B296915 : Blo 295830 296915 := bstep (se 1 (by rfl) ⟨222686, by rfl⟩ : syracuseStep 296915 = 445373) B445373
theorem B296931 : Blo 295830 296931 := bstep (se 1 (by rfl) ⟨222698, by rfl⟩ : syracuseStep 296931 = 445397) B445397
theorem B296947 : Blo 295830 296947 := bstep (se 1 (by rfl) ⟨222710, by rfl⟩ : syracuseStep 296947 = 445421) B445421
theorem B296963 : Blo 295830 296963 := bstep (se 1 (by rfl) ⟨222722, by rfl⟩ : syracuseStep 296963 = 445445) B445445
theorem B296979 : Blo 295830 296979 := bstep (se 1 (by rfl) ⟨222734, by rfl⟩ : syracuseStep 296979 = 445469) B445469
theorem B296995 : Blo 295830 296995 := bstep (se 1 (by rfl) ⟨222746, by rfl⟩ : syracuseStep 296995 = 445493) B445493
theorem B297011 : Blo 295830 297011 := bstep (se 1 (by rfl) ⟨222758, by rfl⟩ : syracuseStep 297011 = 445517) B445517
theorem B297027 : Blo 295830 297027 := bstep (se 1 (by rfl) ⟨222770, by rfl⟩ : syracuseStep 297027 = 445541) B445541
theorem B297043 : Blo 295830 297043 := bstep (se 1 (by rfl) ⟨222782, by rfl⟩ : syracuseStep 297043 = 445565) B445565
theorem B297059 : Blo 295830 297059 := bstep (se 1 (by rfl) ⟨222794, by rfl⟩ : syracuseStep 297059 = 445589) B445589
theorem B297075 : Blo 295830 297075 := bstep (se 1 (by rfl) ⟨222806, by rfl⟩ : syracuseStep 297075 = 445613) B445613
theorem B297091 : Blo 295830 297091 := bstep (se 1 (by rfl) ⟨222818, by rfl⟩ : syracuseStep 297091 = 445637) B445637
theorem B297107 : Blo 295830 297107 := bstep (se 1 (by rfl) ⟨222830, by rfl⟩ : syracuseStep 297107 = 445661) B445661
theorem B297123 : Blo 295830 297123 := bstep (se 1 (by rfl) ⟨222842, by rfl⟩ : syracuseStep 297123 = 445685) B445685
theorem B297139 : Blo 295830 297139 := bstep (se 1 (by rfl) ⟨222854, by rfl⟩ : syracuseStep 297139 = 445709) B445709
theorem B297155 : Blo 295830 297155 := bstep (se 1 (by rfl) ⟨222866, by rfl⟩ : syracuseStep 297155 = 445733) B445733
theorem B297171 : Blo 295830 297171 := bstep (se 1 (by rfl) ⟨222878, by rfl⟩ : syracuseStep 297171 = 445757) B445757
theorem B297187 : Blo 295830 297187 := bstep (se 1 (by rfl) ⟨222890, by rfl⟩ : syracuseStep 297187 = 445781) B445781
theorem B297203 : Blo 295830 297203 := bstep (se 1 (by rfl) ⟨222902, by rfl⟩ : syracuseStep 297203 = 445805) B445805
theorem B297219 : Blo 295830 297219 := bstep (se 1 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 297219 = 445829) B445829
theorem B297235 : Blo 295830 297235 := bstep (se 1 (by rfl) ⟨222926, by rfl⟩ : syracuseStep 297235 = 445853) B445853
theorem B297251 : Blo 295830 297251 := bstep (se 1 (by rfl) ⟨222938, by rfl⟩ : syracuseStep 297251 = 445877) B445877
theorem B297267 : Blo 295830 297267 := bstep (se 1 (by rfl) ⟨222950, by rfl⟩ : syracuseStep 297267 = 445901) B445901
theorem B297283 : Blo 295830 297283 := bstep (se 1 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 297283 = 445925) B445925
theorem B297299 : Blo 295830 297299 := bstep (se 1 (by rfl) ⟨222974, by rfl⟩ : syracuseStep 297299 = 445949) B445949
theorem B297315 : Blo 295830 297315 := bstep (se 1 (by rfl) ⟨222986, by rfl⟩ : syracuseStep 297315 = 445973) B445973
theorem B5802353 : Blo 295830 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B297331 : Blo 295830 297331 := bstep (se 1 (by rfl) ⟨222998, by rfl⟩ : syracuseStep 297331 = 445997) B445997
theorem B297347 : Blo 295830 297347 := bstep (se 1 (by rfl) ⟨223010, by rfl⟩ : syracuseStep 297347 = 446021) B446021
theorem B1804685 : Blo 295830 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B297363 : Blo 295830 297363 := bstep (se 1 (by rfl) ⟨223022, by rfl⟩ : syracuseStep 297363 = 446045) B446045
theorem B297379 : Blo 295830 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B297395 : Blo 295830 297395 := bstep (se 1 (by rfl) ⟨223046, by rfl⟩ : syracuseStep 297395 = 446093) B446093
theorem B297411 : Blo 295830 297411 := bstep (se 1 (by rfl) ⟨223058, by rfl⟩ : syracuseStep 297411 = 446117) B446117
theorem B297427 : Blo 295830 297427 := bstep (se 1 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 297427 = 446141) B446141
theorem B297443 : Blo 295830 297443 := bstep (se 1 (by rfl) ⟨223082, by rfl⟩ : syracuseStep 297443 = 446165) B446165
theorem B297459 : Blo 295830 297459 := bstep (se 1 (by rfl) ⟨223094, by rfl⟩ : syracuseStep 297459 = 446189) B446189
theorem B297475 : Blo 295830 297475 := bstep (se 1 (by rfl) ⟨223106, by rfl⟩ : syracuseStep 297475 = 446213) B446213
theorem B297491 : Blo 295830 297491 := bstep (se 1 (by rfl) ⟨223118, by rfl⟩ : syracuseStep 297491 = 446237) B446237
theorem B297507 : Blo 295830 297507 := bstep (se 1 (by rfl) ⟨223130, by rfl⟩ : syracuseStep 297507 = 446261) B446261
theorem B297523 : Blo 295830 297523 := bstep (se 1 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 297523 = 446285) B446285
theorem B297539 : Blo 295830 297539 := bstep (se 1 (by rfl) ⟨223154, by rfl⟩ : syracuseStep 297539 = 446309) B446309
theorem B297555 : Blo 295830 297555 := bstep (se 1 (by rfl) ⟨223166, by rfl⟩ : syracuseStep 297555 = 446333) B446333
theorem B297571 : Blo 295830 297571 := bstep (se 1 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 297571 = 446357) B446357
theorem B1510001 : Blo 295830 1510001 := bstep (se 2 (by rfl) ⟨566250, by rfl⟩ : syracuseStep 1510001 = 1132501) B1132501
theorem B756337 : Blo 295830 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B297587 : Blo 295830 297587 := bstep (se 1 (by rfl) ⟨223190, by rfl⟩ : syracuseStep 297587 = 446381) B446381
theorem B297603 : Blo 295830 297603 := bstep (se 1 (by rfl) ⟨223202, by rfl⟩ : syracuseStep 297603 = 446405) B446405
theorem B297619 : Blo 295830 297619 := bstep (se 1 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 297619 = 446429) B446429
theorem B297635 : Blo 295830 297635 := bstep (se 1 (by rfl) ⟨223226, by rfl⟩ : syracuseStep 297635 = 446453) B446453
theorem B297651 : Blo 295830 297651 := bstep (se 1 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 297651 = 446477) B446477
theorem B297667 : Blo 295830 297667 := bstep (se 1 (by rfl) ⟨223250, by rfl⟩ : syracuseStep 297667 = 446501) B446501
theorem B297683 : Blo 295830 297683 := bstep (se 1 (by rfl) ⟨223262, by rfl⟩ : syracuseStep 297683 = 446525) B446525
theorem B297699 : Blo 295830 297699 := bstep (se 1 (by rfl) ⟨223274, by rfl⟩ : syracuseStep 297699 = 446549) B446549
theorem B297715 : Blo 295830 297715 := bstep (se 1 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 297715 = 446573) B446573
theorem B297731 : Blo 295830 297731 := bstep (se 1 (by rfl) ⟨223298, by rfl⟩ : syracuseStep 297731 = 446597) B446597
theorem B297747 : Blo 295830 297747 := bstep (se 1 (by rfl) ⟨223310, by rfl⟩ : syracuseStep 297747 = 446621) B446621
theorem B297763 : Blo 295830 297763 := bstep (se 1 (by rfl) ⟨223322, by rfl⟩ : syracuseStep 297763 = 446645) B446645
theorem B1903409 : Blo 295830 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B297779 : Blo 295830 297779 := bstep (se 1 (by rfl) ⟨223334, by rfl⟩ : syracuseStep 297779 = 446669) B446669
theorem B297795 : Blo 295830 297795 := bstep (se 1 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 297795 = 446693) B446693
theorem B297811 : Blo 295830 297811 := bstep (se 1 (by rfl) ⟨223358, by rfl⟩ : syracuseStep 297811 = 446717) B446717
theorem B297827 : Blo 295830 297827 := bstep (se 1 (by rfl) ⟨223370, by rfl⟩ : syracuseStep 297827 = 446741) B446741
theorem B297843 : Blo 295830 297843 := bstep (se 1 (by rfl) ⟨223382, by rfl⟩ : syracuseStep 297843 = 446765) B446765
theorem B297859 : Blo 295830 297859 := bstep (se 1 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 297859 = 446789) B446789
theorem B756611 : Blo 295830 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B297875 : Blo 295830 297875 := bstep (se 1 (by rfl) ⟨223406, by rfl⟩ : syracuseStep 297875 = 446813) B446813
theorem B297891 : Blo 295830 297891 := bstep (se 1 (by rfl) ⟨223418, by rfl⟩ : syracuseStep 297891 = 446837) B446837
theorem B297907 : Blo 295830 297907 := bstep (se 1 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 297907 = 446861) B446861
theorem B297923 : Blo 295830 297923 := bstep (se 1 (by rfl) ⟨223442, by rfl⟩ : syracuseStep 297923 = 446885) B446885
theorem B297939 : Blo 295830 297939 := bstep (se 1 (by rfl) ⟨223454, by rfl⟩ : syracuseStep 297939 = 446909) B446909
theorem B297955 : Blo 295830 297955 := bstep (se 1 (by rfl) ⟨223466, by rfl⟩ : syracuseStep 297955 = 446933) B446933
theorem B297971 : Blo 295830 297971 := bstep (se 1 (by rfl) ⟨223478, by rfl⟩ : syracuseStep 297971 = 446957) B446957
theorem B855043 : Blo 295830 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B297987 : Blo 295830 297987 := bstep (se 1 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 297987 = 446981) B446981
theorem B298003 : Blo 295830 298003 := bstep (se 1 (by rfl) ⟨223502, by rfl⟩ : syracuseStep 298003 = 447005) B447005
theorem B1281059 : Blo 295830 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B298019 : Blo 295830 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B298035 : Blo 295830 298035 := bstep (se 1 (by rfl) ⟨223526, by rfl⟩ : syracuseStep 298035 = 447053) B447053
theorem B298051 : Blo 295830 298051 := bstep (se 1 (by rfl) ⟨223538, by rfl⟩ : syracuseStep 298051 = 447077) B447077
theorem B756803 : Blo 295830 756803 := bstep (se 1 (by rfl) ⟨567602, by rfl⟩ : syracuseStep 756803 = 1135205) B1135205
theorem B298067 : Blo 295830 298067 := bstep (se 1 (by rfl) ⟨223550, by rfl⟩ : syracuseStep 298067 = 447101) B447101
theorem B298083 : Blo 295830 298083 := bstep (se 1 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 298083 = 447125) B447125
theorem B298099 : Blo 295830 298099 := bstep (se 1 (by rfl) ⟨223574, by rfl⟩ : syracuseStep 298099 = 447149) B447149
theorem B298115 : Blo 295830 298115 := bstep (se 1 (by rfl) ⟨223586, by rfl⟩ : syracuseStep 298115 = 447173) B447173
theorem B298131 : Blo 295830 298131 := bstep (se 1 (by rfl) ⟨223598, by rfl⟩ : syracuseStep 298131 = 447197) B447197
theorem B298147 : Blo 295830 298147 := bstep (se 1 (by rfl) ⟨223610, by rfl⟩ : syracuseStep 298147 = 447221) B447221
theorem B298163 : Blo 295830 298163 := bstep (se 1 (by rfl) ⟨223622, by rfl⟩ : syracuseStep 298163 = 447245) B447245
theorem B298179 : Blo 295830 298179 := bstep (se 1 (by rfl) ⟨223634, by rfl⟩ : syracuseStep 298179 = 447269) B447269
theorem B298195 : Blo 295830 298195 := bstep (se 1 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 298195 = 447293) B447293
theorem B298211 : Blo 295830 298211 := bstep (se 1 (by rfl) ⟨223658, by rfl⟩ : syracuseStep 298211 = 447317) B447317
theorem B298227 : Blo 295830 298227 := bstep (se 1 (by rfl) ⟨223670, by rfl⟩ : syracuseStep 298227 = 447341) B447341
theorem B298243 : Blo 295830 298243 := bstep (se 1 (by rfl) ⟨223682, by rfl⟩ : syracuseStep 298243 = 447365) B447365
theorem B298259 : Blo 295830 298259 := bstep (se 1 (by rfl) ⟨223694, by rfl⟩ : syracuseStep 298259 = 447389) B447389
theorem B298275 : Blo 295830 298275 := bstep (se 1 (by rfl) ⟨223706, by rfl⟩ : syracuseStep 298275 = 447413) B447413
theorem B298291 : Blo 295830 298291 := bstep (se 1 (by rfl) ⟨223718, by rfl⟩ : syracuseStep 298291 = 447437) B447437
theorem B298307 : Blo 295830 298307 := bstep (se 1 (by rfl) ⟨223730, by rfl⟩ : syracuseStep 298307 = 447461) B447461
theorem B298323 : Blo 295830 298323 := bstep (se 1 (by rfl) ⟨223742, by rfl⟩ : syracuseStep 298323 = 447485) B447485
theorem B298339 : Blo 295830 298339 := bstep (se 1 (by rfl) ⟨223754, by rfl⟩ : syracuseStep 298339 = 447509) B447509
theorem B298355 : Blo 295830 298355 := bstep (se 1 (by rfl) ⟨223766, by rfl⟩ : syracuseStep 298355 = 447533) B447533
theorem B298371 : Blo 295830 298371 := bstep (se 1 (by rfl) ⟨223778, by rfl⟩ : syracuseStep 298371 = 447557) B447557
theorem B298387 : Blo 295830 298387 := bstep (se 1 (by rfl) ⟨223790, by rfl⟩ : syracuseStep 298387 = 447581) B447581
theorem B298403 : Blo 295830 298403 := bstep (se 1 (by rfl) ⟨223802, by rfl⟩ : syracuseStep 298403 = 447605) B447605
theorem B298419 : Blo 295830 298419 := bstep (se 1 (by rfl) ⟨223814, by rfl⟩ : syracuseStep 298419 = 447629) B447629
theorem B3837365 : Blo 295830 3837365 := bstep (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) B359753
theorem B953795 : Blo 295830 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B298435 : Blo 295830 298435 := bstep (se 1 (by rfl) ⟨223826, by rfl⟩ : syracuseStep 298435 = 447653) B447653
theorem B298451 : Blo 295830 298451 := bstep (se 1 (by rfl) ⟨223838, by rfl⟩ : syracuseStep 298451 = 447677) B447677
theorem B298467 : Blo 295830 298467 := bstep (se 1 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 298467 = 447701) B447701
theorem B298483 : Blo 295830 298483 := bstep (se 1 (by rfl) ⟨223862, by rfl⟩ : syracuseStep 298483 = 447725) B447725
theorem B298499 : Blo 295830 298499 := bstep (se 1 (by rfl) ⟨223874, by rfl⟩ : syracuseStep 298499 = 447749) B447749
theorem B298515 : Blo 295830 298515 := bstep (se 1 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 298515 = 447773) B447773
theorem B298531 : Blo 295830 298531 := bstep (se 1 (by rfl) ⟨223898, by rfl⟩ : syracuseStep 298531 = 447797) B447797
theorem B298547 : Blo 295830 298547 := bstep (se 1 (by rfl) ⟨223910, by rfl⟩ : syracuseStep 298547 = 447821) B447821
theorem B298563 : Blo 295830 298563 := bstep (se 1 (by rfl) ⟨223922, by rfl⟩ : syracuseStep 298563 = 447845) B447845
theorem B298579 : Blo 295830 298579 := bstep (se 1 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 298579 = 447869) B447869
theorem B298595 : Blo 295830 298595 := bstep (se 1 (by rfl) ⟨223946, by rfl⟩ : syracuseStep 298595 = 447893) B447893
theorem B3640945 : Blo 295830 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B298611 : Blo 295830 298611 := bstep (se 1 (by rfl) ⟨223958, by rfl⟩ : syracuseStep 298611 = 447917) B447917
theorem B298627 : Blo 295830 298627 := bstep (se 1 (by rfl) ⟨223970, by rfl⟩ : syracuseStep 298627 = 447941) B447941
theorem B298643 : Blo 295830 298643 := bstep (se 1 (by rfl) ⟨223982, by rfl⟩ : syracuseStep 298643 = 447965) B447965
theorem B298659 : Blo 295830 298659 := bstep (se 1 (by rfl) ⟨223994, by rfl⟩ : syracuseStep 298659 = 447989) B447989
theorem B298675 : Blo 295830 298675 := bstep (se 1 (by rfl) ⟨224006, by rfl⟩ : syracuseStep 298675 = 448013) B448013
theorem B298691 : Blo 295830 298691 := bstep (se 1 (by rfl) ⟨224018, by rfl⟩ : syracuseStep 298691 = 448037) B448037
theorem B298707 : Blo 295830 298707 := bstep (se 1 (by rfl) ⟨224030, by rfl⟩ : syracuseStep 298707 = 448061) B448061
theorem B298723 : Blo 295830 298723 := bstep (se 1 (by rfl) ⟨224042, by rfl⟩ : syracuseStep 298723 = 448085) B448085
theorem B298739 : Blo 295830 298739 := bstep (se 1 (by rfl) ⟨224054, by rfl⟩ : syracuseStep 298739 = 448109) B448109
theorem B298755 : Blo 295830 298755 := bstep (se 1 (by rfl) ⟨224066, by rfl⟩ : syracuseStep 298755 = 448133) B448133
theorem B298771 : Blo 295830 298771 := bstep (se 1 (by rfl) ⟨224078, by rfl⟩ : syracuseStep 298771 = 448157) B448157
theorem B298787 : Blo 295830 298787 := bstep (se 1 (by rfl) ⟨224090, by rfl⟩ : syracuseStep 298787 = 448181) B448181
theorem B298803 : Blo 295830 298803 := bstep (se 1 (by rfl) ⟨224102, by rfl⟩ : syracuseStep 298803 = 448205) B448205
theorem B298819 : Blo 295830 298819 := bstep (se 1 (by rfl) ⟨224114, by rfl⟩ : syracuseStep 298819 = 448229) B448229
theorem B298835 : Blo 295830 298835 := bstep (se 1 (by rfl) ⟨224126, by rfl⟩ : syracuseStep 298835 = 448253) B448253
theorem B298851 : Blo 295830 298851 := bstep (se 1 (by rfl) ⟨224138, by rfl⟩ : syracuseStep 298851 = 448277) B448277
theorem B298867 : Blo 295830 298867 := bstep (se 1 (by rfl) ⟨224150, by rfl⟩ : syracuseStep 298867 = 448301) B448301
theorem B298883 : Blo 295830 298883 := bstep (se 1 (by rfl) ⟨224162, by rfl⟩ : syracuseStep 298883 = 448325) B448325
theorem B298899 : Blo 295830 298899 := bstep (se 1 (by rfl) ⟨224174, by rfl⟩ : syracuseStep 298899 = 448349) B448349
theorem B298915 : Blo 295830 298915 := bstep (se 1 (by rfl) ⟨224186, by rfl⟩ : syracuseStep 298915 = 448373) B448373
theorem B298931 : Blo 295830 298931 := bstep (se 1 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 298931 = 448397) B448397
theorem B298947 : Blo 295830 298947 := bstep (se 1 (by rfl) ⟨224210, by rfl⟩ : syracuseStep 298947 = 448421) B448421
theorem B298963 : Blo 295830 298963 := bstep (se 1 (by rfl) ⟨224222, by rfl⟩ : syracuseStep 298963 = 448445) B448445
theorem B298979 : Blo 295830 298979 := bstep (se 1 (by rfl) ⟨224234, by rfl⟩ : syracuseStep 298979 = 448469) B448469
theorem B757745 : Blo 295830 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B298995 : Blo 295830 298995 := bstep (se 1 (by rfl) ⟨224246, by rfl⟩ : syracuseStep 298995 = 448493) B448493
theorem B299011 : Blo 295830 299011 := bstep (se 1 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 299011 = 448517) B448517
theorem B2854925 : Blo 295830 2854925 := bstep (se 3 (by rfl) ⟨535298, by rfl⟩ : syracuseStep 2854925 = 1070597) B1070597
theorem B299027 : Blo 295830 299027 := bstep (se 1 (by rfl) ⟨224270, by rfl⟩ : syracuseStep 299027 = 448541) B448541
theorem B1511459 : Blo 295830 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B299043 : Blo 295830 299043 := bstep (se 1 (by rfl) ⟨224282, by rfl⟩ : syracuseStep 299043 = 448565) B448565
theorem B757795 : Blo 295830 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B299059 : Blo 295830 299059 := bstep (se 1 (by rfl) ⟨224294, by rfl⟩ : syracuseStep 299059 = 448589) B448589
theorem B299075 : Blo 295830 299075 := bstep (se 1 (by rfl) ⟨224306, by rfl⟩ : syracuseStep 299075 = 448613) B448613
theorem B299091 : Blo 295830 299091 := bstep (se 1 (by rfl) ⟨224318, by rfl⟩ : syracuseStep 299091 = 448637) B448637
theorem B299107 : Blo 295830 299107 := bstep (se 1 (by rfl) ⟨224330, by rfl⟩ : syracuseStep 299107 = 448661) B448661
theorem B299123 : Blo 295830 299123 := bstep (se 1 (by rfl) ⟨224342, by rfl⟩ : syracuseStep 299123 = 448685) B448685
theorem B299139 : Blo 295830 299139 := bstep (se 1 (by rfl) ⟨224354, by rfl⟩ : syracuseStep 299139 = 448709) B448709
theorem B299155 : Blo 295830 299155 := bstep (se 1 (by rfl) ⟨224366, by rfl⟩ : syracuseStep 299155 = 448733) B448733
theorem B299171 : Blo 295830 299171 := bstep (se 1 (by rfl) ⟨224378, by rfl⟩ : syracuseStep 299171 = 448757) B448757
theorem B1020077 : Blo 295830 1020077 := bstep (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) B382529
theorem B757937 : Blo 295830 757937 := bstep (se 2 (by rfl) ⟨284226, by rfl⟩ : syracuseStep 757937 = 568453) B568453
theorem B299187 : Blo 295830 299187 := bstep (se 1 (by rfl) ⟨224390, by rfl⟩ : syracuseStep 299187 = 448781) B448781
theorem B299203 : Blo 295830 299203 := bstep (se 1 (by rfl) ⟨224402, by rfl⟩ : syracuseStep 299203 = 448805) B448805
theorem B299219 : Blo 295830 299219 := bstep (se 1 (by rfl) ⟨224414, by rfl⟩ : syracuseStep 299219 = 448829) B448829
theorem B12226787 : Blo 295830 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B299235 : Blo 295830 299235 := bstep (se 1 (by rfl) ⟨224426, by rfl⟩ : syracuseStep 299235 = 448853) B448853
theorem B299251 : Blo 295830 299251 := bstep (se 1 (by rfl) ⟨224438, by rfl⟩ : syracuseStep 299251 = 448877) B448877
theorem B299267 : Blo 295830 299267 := bstep (se 1 (by rfl) ⟨224450, by rfl⟩ : syracuseStep 299267 = 448901) B448901
theorem B299283 : Blo 295830 299283 := bstep (se 1 (by rfl) ⟨224462, by rfl⟩ : syracuseStep 299283 = 448925) B448925
theorem B299299 : Blo 295830 299299 := bstep (se 1 (by rfl) ⟨224474, by rfl⟩ : syracuseStep 299299 = 448949) B448949
theorem B299315 : Blo 295830 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B299331 : Blo 295830 299331 := bstep (se 1 (by rfl) ⟨224498, by rfl⟩ : syracuseStep 299331 = 448997) B448997
theorem B299347 : Blo 295830 299347 := bstep (se 1 (by rfl) ⟨224510, by rfl⟩ : syracuseStep 299347 = 449021) B449021
theorem B299363 : Blo 295830 299363 := bstep (se 1 (by rfl) ⟨224522, by rfl⟩ : syracuseStep 299363 = 449045) B449045
theorem B299379 : Blo 295830 299379 := bstep (se 1 (by rfl) ⟨224534, by rfl⟩ : syracuseStep 299379 = 449069) B449069
theorem B299395 : Blo 295830 299395 := bstep (se 1 (by rfl) ⟨224546, by rfl⟩ : syracuseStep 299395 = 449093) B449093
theorem B299411 : Blo 295830 299411 := bstep (se 1 (by rfl) ⟨224558, by rfl⟩ : syracuseStep 299411 = 449117) B449117
theorem B299427 : Blo 295830 299427 := bstep (se 1 (by rfl) ⟨224570, by rfl⟩ : syracuseStep 299427 = 449141) B449141
theorem B299443 : Blo 295830 299443 := bstep (se 1 (by rfl) ⟨224582, by rfl⟩ : syracuseStep 299443 = 449165) B449165
theorem B627139 : Blo 295830 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B299459 : Blo 295830 299459 := bstep (se 1 (by rfl) ⟨224594, by rfl⟩ : syracuseStep 299459 = 449189) B449189
theorem B299475 : Blo 295830 299475 := bstep (se 1 (by rfl) ⟨224606, by rfl⟩ : syracuseStep 299475 = 449213) B449213
theorem B299491 : Blo 295830 299491 := bstep (se 1 (by rfl) ⟨224618, by rfl⟩ : syracuseStep 299491 = 449237) B449237
theorem B561649 : Blo 295830 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B299507 : Blo 295830 299507 := bstep (se 1 (by rfl) ⟨224630, by rfl⟩ : syracuseStep 299507 = 449261) B449261
theorem B299523 : Blo 295830 299523 := bstep (se 1 (by rfl) ⟨224642, by rfl⟩ : syracuseStep 299523 = 449285) B449285
theorem B299539 : Blo 295830 299539 := bstep (se 1 (by rfl) ⟨224654, by rfl⟩ : syracuseStep 299539 = 449309) B449309
theorem B299555 : Blo 295830 299555 := bstep (se 1 (by rfl) ⟨224666, by rfl⟩ : syracuseStep 299555 = 449333) B449333
theorem B299571 : Blo 295830 299571 := bstep (se 1 (by rfl) ⟨224678, by rfl⟩ : syracuseStep 299571 = 449357) B449357
theorem B299587 : Blo 295830 299587 := bstep (se 1 (by rfl) ⟨224690, by rfl⟩ : syracuseStep 299587 = 449381) B449381
theorem B299603 : Blo 295830 299603 := bstep (se 1 (by rfl) ⟨224702, by rfl⟩ : syracuseStep 299603 = 449405) B449405
theorem B299619 : Blo 295830 299619 := bstep (se 1 (by rfl) ⟨224714, by rfl⟩ : syracuseStep 299619 = 449429) B449429
theorem B299635 : Blo 295830 299635 := bstep (se 1 (by rfl) ⟨224726, by rfl⟩ : syracuseStep 299635 = 449453) B449453
theorem B299651 : Blo 295830 299651 := bstep (se 1 (by rfl) ⟨224738, by rfl⟩ : syracuseStep 299651 = 449477) B449477
theorem B561809 : Blo 295830 561809 := bstep (se 2 (by rfl) ⟨210678, by rfl⟩ : syracuseStep 561809 = 421357) B421357
theorem B299667 : Blo 295830 299667 := bstep (se 1 (by rfl) ⟨224750, by rfl⟩ : syracuseStep 299667 = 449501) B449501
theorem B463523 : Blo 295830 463523 := bstep (se 1 (by rfl) ⟨347642, by rfl⟩ : syracuseStep 463523 = 695285) B695285
theorem B299683 : Blo 295830 299683 := bstep (se 1 (by rfl) ⟨224762, by rfl⟩ : syracuseStep 299683 = 449525) B449525
theorem B299699 : Blo 295830 299699 := bstep (se 1 (by rfl) ⟨224774, by rfl⟩ : syracuseStep 299699 = 449549) B449549
theorem B299715 : Blo 295830 299715 := bstep (se 1 (by rfl) ⟨224786, by rfl⟩ : syracuseStep 299715 = 449573) B449573
theorem B299731 : Blo 295830 299731 := bstep (se 1 (by rfl) ⟨224798, by rfl⟩ : syracuseStep 299731 = 449597) B449597
theorem B299747 : Blo 295830 299747 := bstep (se 1 (by rfl) ⟨224810, by rfl⟩ : syracuseStep 299747 = 449621) B449621
theorem B299763 : Blo 295830 299763 := bstep (se 1 (by rfl) ⟨224822, by rfl⟩ : syracuseStep 299763 = 449645) B449645
theorem B299779 : Blo 295830 299779 := bstep (se 1 (by rfl) ⟨224834, by rfl⟩ : syracuseStep 299779 = 449669) B449669
theorem B299795 : Blo 295830 299795 := bstep (se 1 (by rfl) ⟨224846, by rfl⟩ : syracuseStep 299795 = 449693) B449693
theorem B299811 : Blo 295830 299811 := bstep (se 1 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 299811 = 449717) B449717
theorem B299827 : Blo 295830 299827 := bstep (se 1 (by rfl) ⟨224870, by rfl⟩ : syracuseStep 299827 = 449741) B449741
theorem B1512269 : Blo 295830 1512269 := bstep (se 3 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 1512269 = 567101) B567101
theorem B562211 : Blo 295830 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B332851 : Blo 295830 332851 := bstep (se 1 (by rfl) ⟨249638, by rfl⟩ : syracuseStep 332851 = 499277) B499277
theorem B758929 : Blo 295830 758929 := bstep (se 2 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 758929 = 569197) B569197
theorem B332995 : Blo 295830 332995 := bstep (se 1 (by rfl) ⟨249746, by rfl⟩ : syracuseStep 332995 = 499493) B499493
theorem B1905869 : Blo 295830 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B955601 : Blo 295830 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B955651 : Blo 295830 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B3872069 : Blo 295830 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B1611085 : Blo 295830 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B333139 : Blo 295830 333139 := bstep (se 1 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 333139 = 499709) B499709
theorem B333283 : Blo 295830 333283 := bstep (se 1 (by rfl) ⟨249962, by rfl⟩ : syracuseStep 333283 = 499925) B499925
theorem B3282403 : Blo 295830 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B333427 : Blo 295830 333427 := bstep (se 1 (by rfl) ⟨250070, by rfl⟩ : syracuseStep 333427 = 500141) B500141
theorem B333571 : Blo 295830 333571 := bstep (se 1 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 333571 = 500357) B500357
theorem B1709923 : Blo 295830 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B333715 : Blo 295830 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B563107 : Blo 295830 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B956369 : Blo 295830 956369 := bstep (se 2 (by rfl) ⟨358638, by rfl⟩ : syracuseStep 956369 = 717277) B717277
theorem B2529265 : Blo 295830 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B333859 : Blo 295830 333859 := bstep (se 1 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 333859 = 500789) B500789
theorem B563267 : Blo 295830 563267 := bstep (se 1 (by rfl) ⟨422450, by rfl⟩ : syracuseStep 563267 = 844901) B844901
theorem B334003 : Blo 295830 334003 := bstep (se 1 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 334003 = 501005) B501005
theorem B1808581 : Blo 295830 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B334147 : Blo 295830 334147 := bstep (se 1 (by rfl) ⟨250610, by rfl⟩ : syracuseStep 334147 = 501221) B501221
theorem B3610979 : Blo 295830 3610979 := bstep (se 1 (by rfl) ⟨2708234, by rfl⟩ : syracuseStep 3610979 = 5416469) B5416469
theorem B1350029 : Blo 295830 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B1612229 : Blo 295830 1612229 := bstep (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) B302293
theorem B956881 : Blo 295830 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B334291 : Blo 295830 334291 := bstep (se 1 (by rfl) ⟨250718, by rfl⟩ : syracuseStep 334291 = 501437) B501437
theorem B334435 : Blo 295830 334435 := bstep (se 1 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 334435 = 501653) B501653
theorem B334579 : Blo 295830 334579 := bstep (se 1 (by rfl) ⟨250934, by rfl⟩ : syracuseStep 334579 = 501869) B501869
theorem B400177 : Blo 295830 400177 := bstep (se 2 (by rfl) ⟨150066, by rfl⟩ : syracuseStep 400177 = 300133) B300133
theorem B334723 : Blo 295830 334723 := bstep (se 1 (by rfl) ⟨251042, by rfl⟩ : syracuseStep 334723 = 502085) B502085
theorem B334867 : Blo 295830 334867 := bstep (se 1 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 334867 = 502301) B502301
theorem B564337 : Blo 295830 564337 := bstep (se 2 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 564337 = 423253) B423253
theorem B335011 : Blo 295830 335011 := bstep (se 1 (by rfl) ⟨251258, by rfl⟩ : syracuseStep 335011 = 502517) B502517
theorem B1219853 : Blo 295830 1219853 := bstep (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) B457445
theorem B400657 : Blo 295830 400657 := bstep (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) B300493
theorem B335155 : Blo 295830 335155 := bstep (se 1 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 335155 = 502733) B502733
theorem B335299 : Blo 295830 335299 := bstep (se 1 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 335299 = 502949) B502949
theorem B1744355 : Blo 295830 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B957997 : Blo 295830 957997 := bstep (se 3 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 957997 = 359249) B359249
theorem B335443 : Blo 295830 335443 := bstep (se 1 (by rfl) ⟨251582, by rfl⟩ : syracuseStep 335443 = 503165) B503165
theorem B499297 : Blo 295830 499297 := bstep (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) B374473
theorem B958061 : Blo 295830 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B499331 : Blo 295830 499331 := bstep (se 1 (by rfl) ⟨374498, by rfl⟩ : syracuseStep 499331 = 748997) B748997
theorem B1515185 : Blo 295830 1515185 := bstep (se 2 (by rfl) ⟨568194, by rfl⟩ : syracuseStep 1515185 = 1136389) B1136389
theorem B335587 : Blo 295830 335587 := bstep (se 1 (by rfl) ⟨251690, by rfl⟩ : syracuseStep 335587 = 503381) B503381
theorem B499459 : Blo 295830 499459 := bstep (se 1 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 499459 = 749189) B749189
theorem B335731 : Blo 295830 335731 := bstep (se 1 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 335731 = 503597) B503597
theorem B499601 : Blo 295830 499601 := bstep (se 2 (by rfl) ⟨187350, by rfl⟩ : syracuseStep 499601 = 374701) B374701
theorem B335875 : Blo 295830 335875 := bstep (se 1 (by rfl) ⟨251906, by rfl⟩ : syracuseStep 335875 = 503813) B503813
theorem B1712141 : Blo 295830 1712141 := bstep (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) B642053
theorem B499729 : Blo 295830 499729 := bstep (se 2 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 499729 = 374797) B374797
theorem B499763 : Blo 295830 499763 := bstep (se 1 (by rfl) ⟨374822, by rfl⟩ : syracuseStep 499763 = 749645) B749645
theorem B565393 : Blo 295830 565393 := bstep (se 2 (by rfl) ⟨212022, by rfl⟩ : syracuseStep 565393 = 424045) B424045
theorem B336019 : Blo 295830 336019 := bstep (se 1 (by rfl) ⟨252014, by rfl⟩ : syracuseStep 336019 = 504029) B504029
theorem B499891 : Blo 295830 499891 := bstep (se 1 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 499891 = 749837) B749837
theorem B2138339 : Blo 295830 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B729361 : Blo 295830 729361 := bstep (se 2 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 729361 = 547021) B547021
theorem B336163 : Blo 295830 336163 := bstep (se 1 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 336163 = 504245) B504245
theorem B3449141 : Blo 295830 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B500033 : Blo 295830 500033 := bstep (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) B375025
theorem B336307 : Blo 295830 336307 := bstep (se 1 (by rfl) ⟨252230, by rfl⟩ : syracuseStep 336307 = 504461) B504461
theorem B500161 : Blo 295830 500161 := bstep (se 2 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 500161 = 375121) B375121
theorem B500195 : Blo 295830 500195 := bstep (se 1 (by rfl) ⟨375146, by rfl⟩ : syracuseStep 500195 = 750293) B750293
theorem B565795 : Blo 295830 565795 := bstep (se 1 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 565795 = 848693) B848693
theorem B336451 : Blo 295830 336451 := bstep (se 1 (by rfl) ⟨252338, by rfl⟩ : syracuseStep 336451 = 504677) B504677
theorem B565841 : Blo 295830 565841 := bstep (se 2 (by rfl) ⟨212190, by rfl⟩ : syracuseStep 565841 = 424381) B424381
theorem B500323 : Blo 295830 500323 := bstep (se 1 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 500323 = 750485) B750485
theorem B336595 : Blo 295830 336595 := bstep (se 1 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 336595 = 504893) B504893
theorem B500465 : Blo 295830 500465 := bstep (se 2 (by rfl) ⟨187674, by rfl⟩ : syracuseStep 500465 = 375349) B375349
theorem B402193 : Blo 295830 402193 := bstep (se 2 (by rfl) ⟨150822, by rfl⟩ : syracuseStep 402193 = 301645) B301645
theorem B336739 : Blo 295830 336739 := bstep (se 1 (by rfl) ⟨252554, by rfl⟩ : syracuseStep 336739 = 505109) B505109
theorem B500593 : Blo 295830 500593 := bstep (se 2 (by rfl) ⟨187722, by rfl⟩ : syracuseStep 500593 = 375445) B375445
theorem B566129 : Blo 295830 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B500627 : Blo 295830 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B402355 : Blo 295830 402355 := bstep (se 1 (by rfl) ⟨301766, by rfl⟩ : syracuseStep 402355 = 603533) B603533
theorem B336883 : Blo 295830 336883 := bstep (se 1 (by rfl) ⟨252662, by rfl⟩ : syracuseStep 336883 = 505325) B505325
theorem B500755 : Blo 295830 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B1516643 : Blo 295830 1516643 := bstep (se 1 (by rfl) ⟨1137482, by rfl⟩ : syracuseStep 1516643 = 2274965) B2274965
theorem B337027 : Blo 295830 337027 := bstep (se 1 (by rfl) ⟨252770, by rfl⟩ : syracuseStep 337027 = 505541) B505541
theorem B500897 : Blo 295830 500897 := bstep (se 2 (by rfl) ⟨187836, by rfl⟩ : syracuseStep 500897 = 375673) B375673
theorem B337171 : Blo 295830 337171 := bstep (se 1 (by rfl) ⟨252878, by rfl⟩ : syracuseStep 337171 = 505757) B505757
theorem B501025 : Blo 295830 501025 := bstep (se 2 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 501025 = 375769) B375769
theorem B501059 : Blo 295830 501059 := bstep (se 1 (by rfl) ⟨375794, by rfl⟩ : syracuseStep 501059 = 751589) B751589
theorem B959843 : Blo 295830 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B501187 : Blo 295830 501187 := bstep (se 1 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 501187 = 751781) B751781
theorem B1811909 : Blo 295830 1811909 := bstep (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) B339733
theorem B402961 : Blo 295830 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B566851 : Blo 295830 566851 := bstep (se 1 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 566851 = 850277) B850277
theorem B501329 : Blo 295830 501329 := bstep (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) B375997
theorem B501457 : Blo 295830 501457 := bstep (se 2 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 501457 = 376093) B376093
theorem B501491 : Blo 295830 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B501619 : Blo 295830 501619 := bstep (se 1 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 501619 = 752429) B752429
theorem B1517453 : Blo 295830 1517453 := bstep (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) B569045
theorem B501761 : Blo 295830 501761 := bstep (se 2 (by rfl) ⟨188160, by rfl⟩ : syracuseStep 501761 = 376321) B376321
theorem B567299 : Blo 295830 567299 := bstep (se 1 (by rfl) ⟨425474, by rfl⟩ : syracuseStep 567299 = 850949) B850949
theorem B501889 : Blo 295830 501889 := bstep (se 2 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 501889 = 376417) B376417
theorem B501923 : Blo 295830 501923 := bstep (se 1 (by rfl) ⟨376442, by rfl⟩ : syracuseStep 501923 = 752885) B752885
theorem B665873 : Blo 295830 665873 := bstep (se 2 (by rfl) ⟨249702, by rfl⟩ : syracuseStep 665873 = 499405) B499405
theorem B665891 : Blo 295830 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B502051 : Blo 295830 502051 := bstep (se 1 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 502051 = 753077) B753077
theorem B567587 : Blo 295830 567587 := bstep (se 1 (by rfl) ⟨425690, by rfl⟩ : syracuseStep 567587 = 851381) B851381
theorem B3909941 : Blo 295830 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B600419 : Blo 295830 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B502193 : Blo 295830 502193 := bstep (se 2 (by rfl) ⟨188322, by rfl⟩ : syracuseStep 502193 = 376645) B376645
theorem B666161 : Blo 295830 666161 := bstep (se 2 (by rfl) ⟨249810, by rfl⟩ : syracuseStep 666161 = 499621) B499621
theorem B502321 : Blo 295830 502321 := bstep (se 2 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 502321 = 376741) B376741
theorem B666179 : Blo 295830 666179 := bstep (se 1 (by rfl) ⟨499634, by rfl⟩ : syracuseStep 666179 = 999269) B999269
theorem B502355 : Blo 295830 502355 := bstep (se 1 (by rfl) ⟨376766, by rfl⟩ : syracuseStep 502355 = 753533) B753533
theorem B502483 : Blo 295830 502483 := bstep (se 1 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 502483 = 753725) B753725
theorem B1125197 : Blo 295830 1125197 := bstep (se 3 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 1125197 = 421949) B421949
theorem B666449 : Blo 295830 666449 := bstep (se 2 (by rfl) ⟨249918, by rfl⟩ : syracuseStep 666449 = 499837) B499837
theorem B502625 : Blo 295830 502625 := bstep (se 2 (by rfl) ⟨188484, by rfl⟩ : syracuseStep 502625 = 376969) B376969
theorem B666467 : Blo 295830 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B502753 : Blo 295830 502753 := bstep (se 2 (by rfl) ⟨188532, by rfl⟩ : syracuseStep 502753 = 377065) B377065
theorem B502787 : Blo 295830 502787 := bstep (se 1 (by rfl) ⟨377090, by rfl⟩ : syracuseStep 502787 = 754181) B754181
theorem B633923 : Blo 295830 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B404561 : Blo 295830 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B666737 : Blo 295830 666737 := bstep (se 2 (by rfl) ⟨250026, by rfl⟩ : syracuseStep 666737 = 500053) B500053
theorem B666755 : Blo 295830 666755 := bstep (se 1 (by rfl) ⟨500066, by rfl⟩ : syracuseStep 666755 = 1000133) B1000133
theorem B502915 : Blo 295830 502915 := bstep (se 1 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 502915 = 754373) B754373
theorem B2534597 : Blo 295830 2534597 := bstep (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) B475237
theorem B568529 : Blo 295830 568529 := bstep (se 2 (by rfl) ⟨213198, by rfl⟩ : syracuseStep 568529 = 426397) B426397
theorem B503057 : Blo 295830 503057 := bstep (se 2 (by rfl) ⟨188646, by rfl⟩ : syracuseStep 503057 = 377293) B377293
theorem B535939 : Blo 295830 535939 := bstep (se 1 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 535939 = 803909) B803909
theorem B667025 : Blo 295830 667025 := bstep (se 2 (by rfl) ⟨250134, by rfl⟩ : syracuseStep 667025 = 500269) B500269
theorem B503185 : Blo 295830 503185 := bstep (se 2 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 503185 = 377389) B377389
theorem B667043 : Blo 295830 667043 := bstep (se 1 (by rfl) ⟨500282, by rfl⟩ : syracuseStep 667043 = 1000565) B1000565
theorem B503219 : Blo 295830 503219 := bstep (se 1 (by rfl) ⟨377414, by rfl⟩ : syracuseStep 503219 = 754829) B754829
theorem B3452357 : Blo 295830 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B634385 : Blo 295830 634385 := bstep (se 2 (by rfl) ⟨237894, by rfl⟩ : syracuseStep 634385 = 475789) B475789
theorem B503347 : Blo 295830 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B3386933 : Blo 295830 3386933 := bstep (se 5 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 3386933 = 317525) B317525
theorem B405091 : Blo 295830 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B1126001 : Blo 295830 1126001 := bstep (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) B844501
theorem B667313 : Blo 295830 667313 := bstep (se 2 (by rfl) ⟨250242, by rfl⟩ : syracuseStep 667313 = 500485) B500485
theorem B503489 : Blo 295830 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B667331 : Blo 295830 667331 := bstep (se 1 (by rfl) ⟨500498, by rfl⟩ : syracuseStep 667331 = 1000997) B1000997
theorem B503617 : Blo 295830 503617 := bstep (se 2 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 503617 = 377713) B377713
theorem B503651 : Blo 295830 503651 := bstep (se 1 (by rfl) ⟨377738, by rfl⟩ : syracuseStep 503651 = 755477) B755477
theorem B667601 : Blo 295830 667601 := bstep (se 2 (by rfl) ⟨250350, by rfl⟩ : syracuseStep 667601 = 500701) B500701
theorem B667619 : Blo 295830 667619 := bstep (se 1 (by rfl) ⟨500714, by rfl⟩ : syracuseStep 667619 = 1001429) B1001429
theorem B503779 : Blo 295830 503779 := bstep (se 1 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 503779 = 755669) B755669
theorem B503921 : Blo 295830 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B2273507 : Blo 295830 2273507 := bstep (se 1 (by rfl) ⟨1705130, by rfl⟩ : syracuseStep 2273507 = 3410261) B3410261
theorem B667889 : Blo 295830 667889 := bstep (se 2 (by rfl) ⟨250458, by rfl⟩ : syracuseStep 667889 = 500917) B500917
theorem B504049 : Blo 295830 504049 := bstep (se 2 (by rfl) ⟨189018, by rfl⟩ : syracuseStep 504049 = 378037) B378037
theorem B667907 : Blo 295830 667907 := bstep (se 1 (by rfl) ⟨500930, by rfl⟩ : syracuseStep 667907 = 1001861) B1001861
theorem B1126669 : Blo 295830 1126669 := bstep (se 3 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 1126669 = 422501) B422501
theorem B504083 : Blo 295830 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B504211 : Blo 295830 504211 := bstep (se 1 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 504211 = 756317) B756317
theorem B2306501 : Blo 295830 2306501 := bstep (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) B432469
theorem B668177 : Blo 295830 668177 := bstep (se 2 (by rfl) ⟨250566, by rfl⟩ : syracuseStep 668177 = 501133) B501133
theorem B504353 : Blo 295830 504353 := bstep (se 2 (by rfl) ⟨189132, by rfl⟩ : syracuseStep 504353 = 378265) B378265
theorem B668195 : Blo 295830 668195 := bstep (se 1 (by rfl) ⟨501146, by rfl⟩ : syracuseStep 668195 = 1002293) B1002293
theorem B504481 : Blo 295830 504481 := bstep (se 2 (by rfl) ⟨189180, by rfl⟩ : syracuseStep 504481 = 378361) B378361
theorem B504515 : Blo 295830 504515 := bstep (se 1 (by rfl) ⟨378386, by rfl⟩ : syracuseStep 504515 = 756773) B756773
theorem B635683 : Blo 295830 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B668465 : Blo 295830 668465 := bstep (se 2 (by rfl) ⟨250674, by rfl⟩ : syracuseStep 668465 = 501349) B501349
theorem B668483 : Blo 295830 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B504643 : Blo 295830 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B504785 : Blo 295830 504785 := bstep (se 2 (by rfl) ⟨189294, by rfl⟩ : syracuseStep 504785 = 378589) B378589
theorem B341011 : Blo 295830 341011 := bstep (se 1 (by rfl) ⟨255758, by rfl⟩ : syracuseStep 341011 = 511517) B511517
theorem B1127459 : Blo 295830 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B635939 : Blo 295830 635939 := bstep (se 1 (by rfl) ⟨476954, by rfl⟩ : syracuseStep 635939 = 953909) B953909
theorem B668753 : Blo 295830 668753 := bstep (se 2 (by rfl) ⟨250782, by rfl⟩ : syracuseStep 668753 = 501565) B501565
theorem B504913 : Blo 295830 504913 := bstep (se 2 (by rfl) ⟨189342, by rfl⟩ : syracuseStep 504913 = 378685) B378685
theorem B668771 : Blo 295830 668771 := bstep (se 1 (by rfl) ⟨501578, by rfl⟩ : syracuseStep 668771 = 1003157) B1003157
theorem B504947 : Blo 295830 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B505075 : Blo 295830 505075 := bstep (se 1 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 505075 = 757613) B757613
theorem B669041 : Blo 295830 669041 := bstep (se 2 (by rfl) ⟨250890, by rfl⟩ : syracuseStep 669041 = 501781) B501781
theorem B505217 : Blo 295830 505217 := bstep (se 2 (by rfl) ⟨189456, by rfl⟩ : syracuseStep 505217 = 378913) B378913
theorem B669059 : Blo 295830 669059 := bstep (se 1 (by rfl) ⟨501794, by rfl⟩ : syracuseStep 669059 = 1003589) B1003589
theorem B505345 : Blo 295830 505345 := bstep (se 2 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 505345 = 379009) B379009
theorem B505379 : Blo 295830 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B669329 : Blo 295830 669329 := bstep (se 2 (by rfl) ⟨250998, by rfl⟩ : syracuseStep 669329 = 501997) B501997
theorem B669347 : Blo 295830 669347 := bstep (se 1 (by rfl) ⟨502010, by rfl⟩ : syracuseStep 669347 = 1004021) B1004021
theorem B505507 : Blo 295830 505507 := bstep (se 1 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 505507 = 758261) B758261
theorem B1128113 : Blo 295830 1128113 := bstep (se 2 (by rfl) ⟨423042, by rfl⟩ : syracuseStep 1128113 = 846085) B846085
theorem B374483 : Blo 295830 374483 := bstep (se 1 (by rfl) ⟨280862, by rfl⟩ : syracuseStep 374483 = 561725) B561725
theorem B505649 : Blo 295830 505649 := bstep (se 2 (by rfl) ⟨189618, by rfl⟩ : syracuseStep 505649 = 379237) B379237
theorem B3815221 : Blo 295830 3815221 := bstep (se 5 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 3815221 = 357677) B357677
theorem B669617 : Blo 295830 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B505777 : Blo 295830 505777 := bstep (se 2 (by rfl) ⟨189666, by rfl⟩ : syracuseStep 505777 = 379333) B379333
theorem B669635 : Blo 295830 669635 := bstep (se 1 (by rfl) ⟨502226, by rfl⟩ : syracuseStep 669635 = 1004453) B1004453
theorem B604099 : Blo 295830 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B505811 : Blo 295830 505811 := bstep (se 1 (by rfl) ⟨379358, by rfl⟩ : syracuseStep 505811 = 758717) B758717
theorem B636913 : Blo 295830 636913 := bstep (se 2 (by rfl) ⟨238842, by rfl⟩ : syracuseStep 636913 = 477685) B477685
theorem B505939 : Blo 295830 505939 := bstep (se 1 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 505939 = 758909) B758909
theorem B1620101 : Blo 295830 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B669905 : Blo 295830 669905 := bstep (se 2 (by rfl) ⟨251214, by rfl⟩ : syracuseStep 669905 = 502429) B502429
theorem B669923 : Blo 295830 669923 := bstep (se 1 (by rfl) ⟨502442, by rfl⟩ : syracuseStep 669923 = 1004885) B1004885
theorem B375187 : Blo 295830 375187 := bstep (se 1 (by rfl) ⟨281390, by rfl⟩ : syracuseStep 375187 = 562781) B562781
theorem B670193 : Blo 295830 670193 := bstep (se 2 (by rfl) ⟨251322, by rfl⟩ : syracuseStep 670193 = 502645) B502645
theorem B375283 : Blo 295830 375283 := bstep (se 1 (by rfl) ⟨281462, by rfl⟩ : syracuseStep 375283 = 562925) B562925
theorem B670211 : Blo 295830 670211 := bstep (se 1 (by rfl) ⟨502658, by rfl⟩ : syracuseStep 670211 = 1005317) B1005317
theorem B6404629 : Blo 295830 6404629 := bstep (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) B300217
theorem B637571 : Blo 295830 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B670481 : Blo 295830 670481 := bstep (se 2 (by rfl) ⟨251430, by rfl⟩ : syracuseStep 670481 = 502861) B502861
theorem B670499 : Blo 295830 670499 := bstep (se 1 (by rfl) ⟨502874, by rfl⟩ : syracuseStep 670499 = 1005749) B1005749
theorem B899921 : Blo 295830 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B375779 : Blo 295830 375779 := bstep (se 1 (by rfl) ⟨281834, by rfl⟩ : syracuseStep 375779 = 563669) B563669
theorem B1686541 : Blo 295830 1686541 := bstep (se 3 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 1686541 = 632453) B632453
theorem B670769 : Blo 295830 670769 := bstep (se 2 (by rfl) ⟨251538, by rfl⟩ : syracuseStep 670769 = 503077) B503077
theorem B670787 : Blo 295830 670787 := bstep (se 1 (by rfl) ⟨503090, by rfl⟩ : syracuseStep 670787 = 1006181) B1006181
theorem B1129571 : Blo 295830 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B998513 : Blo 295830 998513 := bstep (se 2 (by rfl) ⟨374442, by rfl⟩ : syracuseStep 998513 = 748885) B748885
theorem B1129585 : Blo 295830 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B671057 : Blo 295830 671057 := bstep (se 2 (by rfl) ⟨251646, by rfl⟩ : syracuseStep 671057 = 503293) B503293
theorem B671075 : Blo 295830 671075 := bstep (se 1 (by rfl) ⟨503306, by rfl⟩ : syracuseStep 671075 = 1006613) B1006613
theorem B540049 : Blo 295830 540049 := bstep (se 2 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 540049 = 405037) B405037
theorem B474545 : Blo 295830 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B638417 : Blo 295830 638417 := bstep (se 2 (by rfl) ⟨239406, by rfl⟩ : syracuseStep 638417 = 478813) B478813
theorem B409105 : Blo 295830 409105 := bstep (se 2 (by rfl) ⟨153414, by rfl⟩ : syracuseStep 409105 = 306829) B306829
theorem B671345 : Blo 295830 671345 := bstep (se 2 (by rfl) ⟨251754, by rfl⟩ : syracuseStep 671345 = 503509) B503509
theorem B671363 : Blo 295830 671363 := bstep (se 1 (by rfl) ⟨503522, by rfl⟩ : syracuseStep 671363 = 1007045) B1007045
theorem B999053 : Blo 295830 999053 := bstep (se 3 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 999053 = 374645) B374645
theorem B1425059 : Blo 295830 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B376483 : Blo 295830 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B999107 : Blo 295830 999107 := bstep (se 1 (by rfl) ⟨749330, by rfl⟩ : syracuseStep 999107 = 1498661) B1498661
theorem B1162993 : Blo 295830 1162993 := bstep (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) B872245
theorem B376579 : Blo 295830 376579 := bstep (se 1 (by rfl) ⟨282434, by rfl⟩ : syracuseStep 376579 = 564869) B564869
theorem B671633 : Blo 295830 671633 := bstep (se 2 (by rfl) ⟨251862, by rfl⟩ : syracuseStep 671633 = 503725) B503725
theorem B507809 : Blo 295830 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B671651 : Blo 295830 671651 := bstep (se 1 (by rfl) ⟨503738, by rfl⟩ : syracuseStep 671651 = 1007477) B1007477
theorem B999377 : Blo 295830 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B507953 : Blo 295830 507953 := bstep (se 2 (by rfl) ⟨190482, by rfl⟩ : syracuseStep 507953 = 380965) B380965
theorem B901187 : Blo 295830 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B671921 : Blo 295830 671921 := bstep (se 2 (by rfl) ⟨251970, by rfl⟩ : syracuseStep 671921 = 503941) B503941
theorem B671939 : Blo 295830 671939 := bstep (se 1 (by rfl) ⟨503954, by rfl⟩ : syracuseStep 671939 = 1007909) B1007909
theorem B606403 : Blo 295830 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B475379 : Blo 295830 475379 := bstep (se 1 (by rfl) ⟨356534, by rfl⟩ : syracuseStep 475379 = 713069) B713069
theorem B377075 : Blo 295830 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B475411 : Blo 295830 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B573731 : Blo 295830 573731 := bstep (se 1 (by rfl) ⟨430298, by rfl⟩ : syracuseStep 573731 = 860597) B860597
theorem B803153 : Blo 295830 803153 := bstep (se 2 (by rfl) ⟨301182, by rfl⟩ : syracuseStep 803153 = 602365) B602365
theorem B508369 : Blo 295830 508369 := bstep (se 2 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 508369 = 381277) B381277
theorem B672209 : Blo 295830 672209 := bstep (se 2 (by rfl) ⟨252078, by rfl⟩ : syracuseStep 672209 = 504157) B504157
theorem B672227 : Blo 295830 672227 := bstep (se 1 (by rfl) ⟨504170, by rfl⟩ : syracuseStep 672227 = 1008341) B1008341
theorem B999917 : Blo 295830 999917 := bstep (se 3 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 999917 = 374969) B374969
theorem B999971 : Blo 295830 999971 := bstep (se 1 (by rfl) ⟨749978, by rfl⟩ : syracuseStep 999971 = 1499957) B1499957
theorem B1131043 : Blo 295830 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B901763 : Blo 295830 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B672497 : Blo 295830 672497 := bstep (se 2 (by rfl) ⟨252186, by rfl⟩ : syracuseStep 672497 = 504373) B504373
theorem B672515 : Blo 295830 672515 := bstep (se 1 (by rfl) ⟨504386, by rfl⟩ : syracuseStep 672515 = 1008773) B1008773
theorem B1000241 : Blo 295830 1000241 := bstep (se 2 (by rfl) ⟨375090, by rfl⟩ : syracuseStep 1000241 = 750181) B750181
theorem B901955 : Blo 295830 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B967601 : Blo 295830 967601 := bstep (se 2 (by rfl) ⟨362850, by rfl⟩ : syracuseStep 967601 = 725701) B725701
theorem B377779 : Blo 295830 377779 := bstep (se 1 (by rfl) ⟨283334, by rfl⟩ : syracuseStep 377779 = 566669) B566669
theorem B1688525 : Blo 295830 1688525 := bstep (se 3 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 1688525 = 633197) B633197
theorem B1426403 : Blo 295830 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1360867 : Blo 295830 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B672785 : Blo 295830 672785 := bstep (se 2 (by rfl) ⟨252294, by rfl⟩ : syracuseStep 672785 = 504589) B504589
theorem B377875 : Blo 295830 377875 := bstep (se 1 (by rfl) ⟨283406, by rfl⟩ : syracuseStep 377875 = 566813) B566813
theorem B672803 : Blo 295830 672803 := bstep (se 1 (by rfl) ⟨504602, by rfl⟩ : syracuseStep 672803 = 1009205) B1009205
theorem B574627 : Blo 295830 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B476339 : Blo 295830 476339 := bstep (se 1 (by rfl) ⟨357254, by rfl⟩ : syracuseStep 476339 = 714509) B714509
theorem B476417 : Blo 295830 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B673073 : Blo 295830 673073 := bstep (se 2 (by rfl) ⟨252402, by rfl⟩ : syracuseStep 673073 = 504805) B504805
theorem B673091 : Blo 295830 673091 := bstep (se 1 (by rfl) ⟨504818, by rfl⟩ : syracuseStep 673091 = 1009637) B1009637
theorem B1000781 : Blo 295830 1000781 := bstep (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) B375293
theorem B443747 : Blo 295830 443747 := bstep (se 1 (by rfl) ⟨332810, by rfl⟩ : syracuseStep 443747 = 665621) B665621
theorem B443777 : Blo 295830 443777 := bstep (se 2 (by rfl) ⟨166416, by rfl⟩ : syracuseStep 443777 = 332833) B332833
theorem B1000835 : Blo 295830 1000835 := bstep (se 1 (by rfl) ⟨750626, by rfl⟩ : syracuseStep 1000835 = 1501253) B1501253
theorem B443795 : Blo 295830 443795 := bstep (se 1 (by rfl) ⟨332846, by rfl⟩ : syracuseStep 443795 = 665693) B665693
theorem B443825 : Blo 295830 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B443843 : Blo 295830 443843 := bstep (se 1 (by rfl) ⟨332882, by rfl⟩ : syracuseStep 443843 = 665765) B665765
theorem B443873 : Blo 295830 443873 := bstep (se 2 (by rfl) ⟨166452, by rfl⟩ : syracuseStep 443873 = 332905) B332905
theorem B476641 : Blo 295830 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B443891 : Blo 295830 443891 := bstep (se 1 (by rfl) ⟨332918, by rfl⟩ : syracuseStep 443891 = 665837) B665837
theorem B378371 : Blo 295830 378371 := bstep (se 1 (by rfl) ⟨283778, by rfl⟩ : syracuseStep 378371 = 567557) B567557
theorem B443921 : Blo 295830 443921 := bstep (se 2 (by rfl) ⟨166470, by rfl⟩ : syracuseStep 443921 = 332941) B332941
theorem B443939 : Blo 295830 443939 := bstep (se 1 (by rfl) ⟨332954, by rfl⟩ : syracuseStep 443939 = 665909) B665909
theorem B443969 : Blo 295830 443969 := bstep (se 2 (by rfl) ⟨166488, by rfl⟩ : syracuseStep 443969 = 332977) B332977
theorem B673361 : Blo 295830 673361 := bstep (se 2 (by rfl) ⟨252510, by rfl⟩ : syracuseStep 673361 = 505021) B505021
theorem B443987 : Blo 295830 443987 := bstep (se 1 (by rfl) ⟨332990, by rfl⟩ : syracuseStep 443987 = 665981) B665981
theorem B673379 : Blo 295830 673379 := bstep (se 1 (by rfl) ⟨505034, by rfl⟩ : syracuseStep 673379 = 1010069) B1010069
theorem B444017 : Blo 295830 444017 := bstep (se 2 (by rfl) ⟨166506, by rfl⟩ : syracuseStep 444017 = 333013) B333013
theorem B444035 : Blo 295830 444035 := bstep (se 1 (by rfl) ⟨333026, by rfl⟩ : syracuseStep 444035 = 666053) B666053
theorem B1001105 : Blo 295830 1001105 := bstep (se 2 (by rfl) ⟨375414, by rfl⟩ : syracuseStep 1001105 = 750829) B750829
theorem B444065 : Blo 295830 444065 := bstep (se 2 (by rfl) ⟨166524, by rfl⟩ : syracuseStep 444065 = 333049) B333049
theorem B444083 : Blo 295830 444083 := bstep (se 1 (by rfl) ⟨333062, by rfl⟩ : syracuseStep 444083 = 666125) B666125
theorem B444113 : Blo 295830 444113 := bstep (se 2 (by rfl) ⟨166542, by rfl⟩ : syracuseStep 444113 = 333085) B333085
theorem B444131 : Blo 295830 444131 := bstep (se 1 (by rfl) ⟨333098, by rfl⟩ : syracuseStep 444131 = 666197) B666197
theorem B444161 : Blo 295830 444161 := bstep (se 2 (by rfl) ⟨166560, by rfl⟩ : syracuseStep 444161 = 333121) B333121
theorem B444179 : Blo 295830 444179 := bstep (se 1 (by rfl) ⟨333134, by rfl⟩ : syracuseStep 444179 = 666269) B666269
theorem B968483 : Blo 295830 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B444209 : Blo 295830 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B444227 : Blo 295830 444227 := bstep (se 1 (by rfl) ⟨333170, by rfl⟩ : syracuseStep 444227 = 666341) B666341
theorem B444257 : Blo 295830 444257 := bstep (se 2 (by rfl) ⟨166596, by rfl⟩ : syracuseStep 444257 = 333193) B333193
theorem B1689457 : Blo 295830 1689457 := bstep (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) B1267093
theorem B673649 : Blo 295830 673649 := bstep (se 2 (by rfl) ⟨252618, by rfl⟩ : syracuseStep 673649 = 505237) B505237
theorem B444275 : Blo 295830 444275 := bstep (se 1 (by rfl) ⟨333206, by rfl⟩ : syracuseStep 444275 = 666413) B666413
theorem B673667 : Blo 295830 673667 := bstep (se 1 (by rfl) ⟨505250, by rfl⟩ : syracuseStep 673667 = 1010501) B1010501
theorem B20760461 : Blo 295830 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B444305 : Blo 295830 444305 := bstep (se 2 (by rfl) ⟨166614, by rfl⟩ : syracuseStep 444305 = 333229) B333229
theorem B444323 : Blo 295830 444323 := bstep (se 1 (by rfl) ⟨333242, by rfl⟩ : syracuseStep 444323 = 666485) B666485
theorem B444353 : Blo 295830 444353 := bstep (se 2 (by rfl) ⟨166632, by rfl⟩ : syracuseStep 444353 = 333265) B333265
theorem B444371 : Blo 295830 444371 := bstep (se 1 (by rfl) ⟨333278, by rfl⟩ : syracuseStep 444371 = 666557) B666557
theorem B444401 : Blo 295830 444401 := bstep (se 2 (by rfl) ⟨166650, by rfl⟩ : syracuseStep 444401 = 333301) B333301
theorem B444419 : Blo 295830 444419 := bstep (se 1 (by rfl) ⟨333314, by rfl⟩ : syracuseStep 444419 = 666629) B666629
theorem B444449 : Blo 295830 444449 := bstep (se 2 (by rfl) ⟨166668, by rfl⟩ : syracuseStep 444449 = 333337) B333337
theorem B444467 : Blo 295830 444467 := bstep (se 1 (by rfl) ⟨333350, by rfl⟩ : syracuseStep 444467 = 666701) B666701
theorem B444497 : Blo 295830 444497 := bstep (se 2 (by rfl) ⟨166686, by rfl⟩ : syracuseStep 444497 = 333373) B333373
theorem B444515 : Blo 295830 444515 := bstep (se 1 (by rfl) ⟨333386, by rfl⟩ : syracuseStep 444515 = 666773) B666773
theorem B510067 : Blo 295830 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B444545 : Blo 295830 444545 := bstep (se 2 (by rfl) ⟨166704, by rfl⟩ : syracuseStep 444545 = 333409) B333409
theorem B673937 : Blo 295830 673937 := bstep (se 2 (by rfl) ⟨252726, by rfl⟩ : syracuseStep 673937 = 505453) B505453
theorem B444563 : Blo 295830 444563 := bstep (se 1 (by rfl) ⟨333422, by rfl⟩ : syracuseStep 444563 = 666845) B666845
theorem B673955 : Blo 295830 673955 := bstep (se 1 (by rfl) ⟨505466, by rfl⟩ : syracuseStep 673955 = 1010933) B1010933
theorem B1001645 : Blo 295830 1001645 := bstep (se 3 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 1001645 = 375617) B375617
theorem B444593 : Blo 295830 444593 := bstep (se 2 (by rfl) ⟨166722, by rfl⟩ : syracuseStep 444593 = 333445) B333445
theorem B1427633 : Blo 295830 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B444611 : Blo 295830 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B379075 : Blo 295830 379075 := bstep (se 1 (by rfl) ⟨284306, by rfl⟩ : syracuseStep 379075 = 568613) B568613
theorem B444641 : Blo 295830 444641 := bstep (se 2 (by rfl) ⟨166740, by rfl⟩ : syracuseStep 444641 = 333481) B333481
theorem B1001699 : Blo 295830 1001699 := bstep (se 1 (by rfl) ⟨751274, by rfl⟩ : syracuseStep 1001699 = 1502549) B1502549
theorem B444659 : Blo 295830 444659 := bstep (se 1 (by rfl) ⟨333494, by rfl⟩ : syracuseStep 444659 = 666989) B666989
theorem B444689 : Blo 295830 444689 := bstep (se 2 (by rfl) ⟨166758, by rfl⟩ : syracuseStep 444689 = 333517) B333517
theorem B444707 : Blo 295830 444707 := bstep (se 1 (by rfl) ⟨333530, by rfl⟩ : syracuseStep 444707 = 667061) B667061
theorem B379171 : Blo 295830 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B1624369 : Blo 295830 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B444737 : Blo 295830 444737 := bstep (se 2 (by rfl) ⟨166776, by rfl⟩ : syracuseStep 444737 = 333553) B333553
theorem B444755 : Blo 295830 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B444785 : Blo 295830 444785 := bstep (se 2 (by rfl) ⟨166794, by rfl⟩ : syracuseStep 444785 = 333589) B333589
theorem B444803 : Blo 295830 444803 := bstep (se 1 (by rfl) ⟨333602, by rfl⟩ : syracuseStep 444803 = 667205) B667205
theorem B444833 : Blo 295830 444833 := bstep (se 2 (by rfl) ⟨166812, by rfl⟩ : syracuseStep 444833 = 333625) B333625
theorem B674225 : Blo 295830 674225 := bstep (se 2 (by rfl) ⟨252834, by rfl⟩ : syracuseStep 674225 = 505669) B505669
theorem B444851 : Blo 295830 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B674243 : Blo 295830 674243 := bstep (se 1 (by rfl) ⟨505682, by rfl⟩ : syracuseStep 674243 = 1011365) B1011365
theorem B444881 : Blo 295830 444881 := bstep (se 2 (by rfl) ⟨166830, by rfl⟩ : syracuseStep 444881 = 333661) B333661
theorem B444899 : Blo 295830 444899 := bstep (se 1 (by rfl) ⟨333674, by rfl⟩ : syracuseStep 444899 = 667349) B667349
theorem B1001969 : Blo 295830 1001969 := bstep (se 2 (by rfl) ⟨375738, by rfl⟩ : syracuseStep 1001969 = 751477) B751477
theorem B444929 : Blo 295830 444929 := bstep (se 2 (by rfl) ⟨166848, by rfl⟩ : syracuseStep 444929 = 333697) B333697
theorem B444947 : Blo 295830 444947 := bstep (se 1 (by rfl) ⟨333710, by rfl⟩ : syracuseStep 444947 = 667421) B667421
theorem B444977 : Blo 295830 444977 := bstep (se 2 (by rfl) ⟨166866, by rfl⟩ : syracuseStep 444977 = 333733) B333733
theorem B444995 : Blo 295830 444995 := bstep (se 1 (by rfl) ⟨333746, by rfl⟩ : syracuseStep 444995 = 667493) B667493
theorem B445025 : Blo 295830 445025 := bstep (se 2 (by rfl) ⟨166884, by rfl⟩ : syracuseStep 445025 = 333769) B333769
theorem B445043 : Blo 295830 445043 := bstep (se 1 (by rfl) ⟨333782, by rfl⟩ : syracuseStep 445043 = 667565) B667565
theorem B445073 : Blo 295830 445073 := bstep (se 2 (by rfl) ⟨166902, by rfl⟩ : syracuseStep 445073 = 333805) B333805
theorem B445091 : Blo 295830 445091 := bstep (se 1 (by rfl) ⟨333818, by rfl⟩ : syracuseStep 445091 = 667637) B667637
theorem B805553 : Blo 295830 805553 := bstep (se 2 (by rfl) ⟨302082, by rfl⟩ : syracuseStep 805553 = 604165) B604165
theorem B445121 : Blo 295830 445121 := bstep (se 2 (by rfl) ⟨166920, by rfl⟩ : syracuseStep 445121 = 333841) B333841
theorem B1133261 : Blo 295830 1133261 := bstep (se 3 (by rfl) ⟨212486, by rfl⟩ : syracuseStep 1133261 = 424973) B424973
theorem B674513 : Blo 295830 674513 := bstep (se 2 (by rfl) ⟨252942, by rfl⟩ : syracuseStep 674513 = 505885) B505885
theorem B445139 : Blo 295830 445139 := bstep (se 1 (by rfl) ⟨333854, by rfl⟩ : syracuseStep 445139 = 667709) B667709
theorem B674531 : Blo 295830 674531 := bstep (se 1 (by rfl) ⟨505898, by rfl⟩ : syracuseStep 674531 = 1011797) B1011797
theorem B445169 : Blo 295830 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B445187 : Blo 295830 445187 := bstep (se 1 (by rfl) ⟨333890, by rfl⟩ : syracuseStep 445187 = 667781) B667781
theorem B445217 : Blo 295830 445217 := bstep (se 2 (by rfl) ⟨166956, by rfl⟩ : syracuseStep 445217 = 333913) B333913
theorem B445235 : Blo 295830 445235 := bstep (se 1 (by rfl) ⟨333926, by rfl⟩ : syracuseStep 445235 = 667853) B667853
theorem B445265 : Blo 295830 445265 := bstep (se 2 (by rfl) ⟨166974, by rfl⟩ : syracuseStep 445265 = 333949) B333949
theorem B445283 : Blo 295830 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B445313 : Blo 295830 445313 := bstep (se 2 (by rfl) ⟨166992, by rfl⟩ : syracuseStep 445313 = 333985) B333985
theorem B871309 : Blo 295830 871309 := bstep (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) B326741
theorem B445331 : Blo 295830 445331 := bstep (se 1 (by rfl) ⟨333998, by rfl⟩ : syracuseStep 445331 = 667997) B667997
theorem B445361 : Blo 295830 445361 := bstep (se 2 (by rfl) ⟨167010, by rfl⟩ : syracuseStep 445361 = 334021) B334021
theorem B445379 : Blo 295830 445379 := bstep (se 1 (by rfl) ⟨334034, by rfl⟩ : syracuseStep 445379 = 668069) B668069
theorem B445409 : Blo 295830 445409 := bstep (se 2 (by rfl) ⟨167028, by rfl⟩ : syracuseStep 445409 = 334057) B334057
theorem B445427 : Blo 295830 445427 := bstep (se 1 (by rfl) ⟨334070, by rfl⟩ : syracuseStep 445427 = 668141) B668141
theorem B1002509 : Blo 295830 1002509 := bstep (se 3 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 1002509 = 375941) B375941
theorem B445457 : Blo 295830 445457 := bstep (se 2 (by rfl) ⟨167046, by rfl⟩ : syracuseStep 445457 = 334093) B334093
theorem B445475 : Blo 295830 445475 := bstep (se 1 (by rfl) ⟨334106, by rfl⟩ : syracuseStep 445475 = 668213) B668213
theorem B445505 : Blo 295830 445505 := bstep (se 2 (by rfl) ⟨167064, by rfl⟩ : syracuseStep 445505 = 334129) B334129
theorem B1002563 : Blo 295830 1002563 := bstep (se 1 (by rfl) ⟨751922, by rfl⟩ : syracuseStep 1002563 = 1503845) B1503845
theorem B2247749 : Blo 295830 2247749 := bstep (se 4 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 2247749 = 421453) B421453
theorem B2542661 : Blo 295830 2542661 := bstep (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) B476749
theorem B445523 : Blo 295830 445523 := bstep (se 1 (by rfl) ⟨334142, by rfl⟩ : syracuseStep 445523 = 668285) B668285
theorem B445553 : Blo 295830 445553 := bstep (se 2 (by rfl) ⟨167082, by rfl⟩ : syracuseStep 445553 = 334165) B334165
theorem B445571 : Blo 295830 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B445601 : Blo 295830 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B445619 : Blo 295830 445619 := bstep (se 1 (by rfl) ⟨334214, by rfl⟩ : syracuseStep 445619 = 668429) B668429
theorem B478403 : Blo 295830 478403 := bstep (se 1 (by rfl) ⟨358802, by rfl⟩ : syracuseStep 478403 = 717605) B717605
theorem B445649 : Blo 295830 445649 := bstep (se 2 (by rfl) ⟨167118, by rfl⟩ : syracuseStep 445649 = 334237) B334237
theorem B511201 : Blo 295830 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B445667 : Blo 295830 445667 := bstep (se 1 (by rfl) ⟨334250, by rfl⟩ : syracuseStep 445667 = 668501) B668501
theorem B445697 : Blo 295830 445697 := bstep (se 2 (by rfl) ⟨167136, by rfl⟩ : syracuseStep 445697 = 334273) B334273
theorem B1428749 : Blo 295830 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B445715 : Blo 295830 445715 := bstep (se 1 (by rfl) ⟨334286, by rfl⟩ : syracuseStep 445715 = 668573) B668573
theorem B1690915 : Blo 295830 1690915 := bstep (se 1 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 1690915 = 2536373) B2536373
theorem B445745 : Blo 295830 445745 := bstep (se 2 (by rfl) ⟨167154, by rfl⟩ : syracuseStep 445745 = 334309) B334309
theorem B445763 : Blo 295830 445763 := bstep (se 1 (by rfl) ⟨334322, by rfl⟩ : syracuseStep 445763 = 668645) B668645
theorem B1002833 : Blo 295830 1002833 := bstep (se 2 (by rfl) ⟨376062, by rfl⟩ : syracuseStep 1002833 = 752125) B752125
theorem B445793 : Blo 295830 445793 := bstep (se 2 (by rfl) ⟨167172, by rfl⟩ : syracuseStep 445793 = 334345) B334345
theorem B445811 : Blo 295830 445811 := bstep (se 1 (by rfl) ⟨334358, by rfl⟩ : syracuseStep 445811 = 668717) B668717
theorem B478595 : Blo 295830 478595 := bstep (se 1 (by rfl) ⟨358946, by rfl⟩ : syracuseStep 478595 = 717893) B717893
theorem B445841 : Blo 295830 445841 := bstep (se 2 (by rfl) ⟨167190, by rfl⟩ : syracuseStep 445841 = 334381) B334381
theorem B445859 : Blo 295830 445859 := bstep (se 1 (by rfl) ⟨334394, by rfl⟩ : syracuseStep 445859 = 668789) B668789
theorem B445889 : Blo 295830 445889 := bstep (se 2 (by rfl) ⟨167208, by rfl⟩ : syracuseStep 445889 = 334417) B334417
theorem B445907 : Blo 295830 445907 := bstep (se 1 (by rfl) ⟨334430, by rfl⟩ : syracuseStep 445907 = 668861) B668861
theorem B445937 : Blo 295830 445937 := bstep (se 2 (by rfl) ⟨167226, by rfl⟩ : syracuseStep 445937 = 334453) B334453
theorem B445955 : Blo 295830 445955 := bstep (se 1 (by rfl) ⟨334466, by rfl⟩ : syracuseStep 445955 = 668933) B668933
theorem B478723 : Blo 295830 478723 := bstep (se 1 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 478723 = 718085) B718085
theorem B1265165 : Blo 295830 1265165 := bstep (se 3 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 1265165 = 474437) B474437
theorem B445985 : Blo 295830 445985 := bstep (se 2 (by rfl) ⟨167244, by rfl⟩ : syracuseStep 445985 = 334489) B334489
theorem B446003 : Blo 295830 446003 := bstep (se 1 (by rfl) ⟨334502, by rfl⟩ : syracuseStep 446003 = 669005) B669005
theorem B577091 : Blo 295830 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1920581 : Blo 295830 1920581 := bstep (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) B360109
theorem B446033 : Blo 295830 446033 := bstep (se 2 (by rfl) ⟨167262, by rfl⟩ : syracuseStep 446033 = 334525) B334525
theorem B446051 : Blo 295830 446051 := bstep (se 1 (by rfl) ⟨334538, by rfl⟩ : syracuseStep 446051 = 669077) B669077
theorem B446081 : Blo 295830 446081 := bstep (se 2 (by rfl) ⟨167280, by rfl⟩ : syracuseStep 446081 = 334561) B334561
theorem B446099 : Blo 295830 446099 := bstep (se 1 (by rfl) ⟨334574, by rfl⟩ : syracuseStep 446099 = 669149) B669149
theorem B446129 : Blo 295830 446129 := bstep (se 2 (by rfl) ⟨167298, by rfl⟩ : syracuseStep 446129 = 334597) B334597
theorem B446147 : Blo 295830 446147 := bstep (se 1 (by rfl) ⟨334610, by rfl⟩ : syracuseStep 446147 = 669221) B669221
theorem B446177 : Blo 295830 446177 := bstep (se 2 (by rfl) ⟨167316, by rfl⟩ : syracuseStep 446177 = 334633) B334633
theorem B2543345 : Blo 295830 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B446195 : Blo 295830 446195 := bstep (se 1 (by rfl) ⟨334646, by rfl⟩ : syracuseStep 446195 = 669293) B669293
theorem B446225 : Blo 295830 446225 := bstep (se 2 (by rfl) ⟨167334, by rfl⟩ : syracuseStep 446225 = 334669) B334669
theorem B12865301 : Blo 295830 12865301 := bstep (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) B603061
theorem B446243 : Blo 295830 446243 := bstep (se 1 (by rfl) ⟨334682, by rfl⟩ : syracuseStep 446243 = 669365) B669365
theorem B1691441 : Blo 295830 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B4312885 : Blo 295830 4312885 := bstep (se 5 (by rfl) ⟨202166, by rfl⟩ : syracuseStep 4312885 = 404333) B404333
theorem B446273 : Blo 295830 446273 := bstep (se 2 (by rfl) ⟨167352, by rfl⟩ : syracuseStep 446273 = 334705) B334705
theorem B806723 : Blo 295830 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B446291 : Blo 295830 446291 := bstep (se 1 (by rfl) ⟨334718, by rfl⟩ : syracuseStep 446291 = 669437) B669437
theorem B1003373 : Blo 295830 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B905069 : Blo 295830 905069 := bstep (se 3 (by rfl) ⟨169700, by rfl⟩ : syracuseStep 905069 = 339401) B339401
theorem B446321 : Blo 295830 446321 := bstep (se 2 (by rfl) ⟨167370, by rfl⟩ : syracuseStep 446321 = 334741) B334741
theorem B446339 : Blo 295830 446339 := bstep (se 1 (by rfl) ⟨334754, by rfl⟩ : syracuseStep 446339 = 669509) B669509
theorem B446369 : Blo 295830 446369 := bstep (se 2 (by rfl) ⟨167388, by rfl⟩ : syracuseStep 446369 = 334777) B334777
theorem B1003427 : Blo 295830 1003427 := bstep (se 1 (by rfl) ⟨752570, by rfl⟩ : syracuseStep 1003427 = 1505141) B1505141
theorem B446387 : Blo 295830 446387 := bstep (se 1 (by rfl) ⟨334790, by rfl⟩ : syracuseStep 446387 = 669581) B669581
theorem B446417 : Blo 295830 446417 := bstep (se 2 (by rfl) ⟨167406, by rfl⟩ : syracuseStep 446417 = 334813) B334813
theorem B446435 : Blo 295830 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B446465 : Blo 295830 446465 := bstep (se 2 (by rfl) ⟨167424, by rfl⟩ : syracuseStep 446465 = 334849) B334849
theorem B446483 : Blo 295830 446483 := bstep (se 1 (by rfl) ⟨334862, by rfl⟩ : syracuseStep 446483 = 669725) B669725
theorem B446513 : Blo 295830 446513 := bstep (se 2 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 446513 = 334885) B334885
theorem B446531 : Blo 295830 446531 := bstep (se 1 (by rfl) ⟨334898, by rfl⟩ : syracuseStep 446531 = 669797) B669797
theorem B446561 : Blo 295830 446561 := bstep (se 2 (by rfl) ⟨167460, by rfl⟩ : syracuseStep 446561 = 334921) B334921
theorem B446579 : Blo 295830 446579 := bstep (se 1 (by rfl) ⟨334934, by rfl⟩ : syracuseStep 446579 = 669869) B669869
theorem B479363 : Blo 295830 479363 := bstep (se 1 (by rfl) ⟨359522, by rfl⟩ : syracuseStep 479363 = 719045) B719045
theorem B446609 : Blo 295830 446609 := bstep (se 2 (by rfl) ⟨167478, by rfl⟩ : syracuseStep 446609 = 334957) B334957
theorem B446627 : Blo 295830 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B1003697 : Blo 295830 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B446657 : Blo 295830 446657 := bstep (se 2 (by rfl) ⟨167496, by rfl⟩ : syracuseStep 446657 = 334993) B334993
theorem B479441 : Blo 295830 479441 := bstep (se 2 (by rfl) ⟨179790, by rfl⟩ : syracuseStep 479441 = 359581) B359581
theorem B446675 : Blo 295830 446675 := bstep (se 1 (by rfl) ⟨335006, by rfl⟩ : syracuseStep 446675 = 670013) B670013
theorem B446705 : Blo 295830 446705 := bstep (se 2 (by rfl) ⟨167514, by rfl⟩ : syracuseStep 446705 = 335029) B335029
theorem B446723 : Blo 295830 446723 := bstep (se 1 (by rfl) ⟨335042, by rfl⟩ : syracuseStep 446723 = 670085) B670085
theorem B446753 : Blo 295830 446753 := bstep (se 2 (by rfl) ⟨167532, by rfl⟩ : syracuseStep 446753 = 335065) B335065
theorem B446771 : Blo 295830 446771 := bstep (se 1 (by rfl) ⟨335078, by rfl⟩ : syracuseStep 446771 = 670157) B670157
theorem B446801 : Blo 295830 446801 := bstep (se 2 (by rfl) ⟨167550, by rfl⟩ : syracuseStep 446801 = 335101) B335101
theorem B446819 : Blo 295830 446819 := bstep (se 1 (by rfl) ⟨335114, by rfl⟩ : syracuseStep 446819 = 670229) B670229
theorem B446849 : Blo 295830 446849 := bstep (se 2 (by rfl) ⟨167568, by rfl⟩ : syracuseStep 446849 = 335137) B335137
theorem B446867 : Blo 295830 446867 := bstep (se 1 (by rfl) ⟨335150, by rfl⟩ : syracuseStep 446867 = 670301) B670301
theorem B446897 : Blo 295830 446897 := bstep (se 2 (by rfl) ⟨167586, by rfl⟩ : syracuseStep 446897 = 335173) B335173
theorem B446915 : Blo 295830 446915 := bstep (se 1 (by rfl) ⟨335186, by rfl⟩ : syracuseStep 446915 = 670373) B670373
theorem B446945 : Blo 295830 446945 := bstep (se 2 (by rfl) ⟨167604, by rfl⟩ : syracuseStep 446945 = 335209) B335209
theorem B446963 : Blo 295830 446963 := bstep (se 1 (by rfl) ⟨335222, by rfl⟩ : syracuseStep 446963 = 670445) B670445
theorem B446993 : Blo 295830 446993 := bstep (se 2 (by rfl) ⟨167622, by rfl⟩ : syracuseStep 446993 = 335245) B335245
theorem B447011 : Blo 295830 447011 := bstep (se 1 (by rfl) ⟨335258, by rfl⟩ : syracuseStep 447011 = 670517) B670517
theorem B447041 : Blo 295830 447041 := bstep (se 2 (by rfl) ⟨167640, by rfl⟩ : syracuseStep 447041 = 335281) B335281
theorem B1430093 : Blo 295830 1430093 := bstep (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) B536285
theorem B479825 : Blo 295830 479825 := bstep (se 2 (by rfl) ⟨179934, by rfl⟩ : syracuseStep 479825 = 359869) B359869
theorem B447059 : Blo 295830 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B447089 : Blo 295830 447089 := bstep (se 2 (by rfl) ⟨167658, by rfl⟩ : syracuseStep 447089 = 335317) B335317
theorem B447107 : Blo 295830 447107 := bstep (se 1 (by rfl) ⟨335330, by rfl⟩ : syracuseStep 447107 = 670661) B670661
theorem B447137 : Blo 295830 447137 := bstep (se 2 (by rfl) ⟨167676, by rfl⟩ : syracuseStep 447137 = 335353) B335353
theorem B447155 : Blo 295830 447155 := bstep (se 1 (by rfl) ⟨335366, by rfl⟩ : syracuseStep 447155 = 670733) B670733
theorem B316099 : Blo 295830 316099 := bstep (se 1 (by rfl) ⟨237074, by rfl⟩ : syracuseStep 316099 = 474149) B474149
theorem B1004237 : Blo 295830 1004237 := bstep (se 3 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 1004237 = 376589) B376589
theorem B447185 : Blo 295830 447185 := bstep (se 2 (by rfl) ⟨167694, by rfl⟩ : syracuseStep 447185 = 335389) B335389
theorem B479953 : Blo 295830 479953 := bstep (se 2 (by rfl) ⟨179982, by rfl⟩ : syracuseStep 479953 = 359965) B359965
theorem B447203 : Blo 295830 447203 := bstep (se 1 (by rfl) ⟨335402, by rfl⟩ : syracuseStep 447203 = 670805) B670805
theorem B447233 : Blo 295830 447233 := bstep (se 2 (by rfl) ⟨167712, by rfl⟩ : syracuseStep 447233 = 335425) B335425
theorem B1004291 : Blo 295830 1004291 := bstep (se 1 (by rfl) ⟨753218, by rfl⟩ : syracuseStep 1004291 = 1506437) B1506437
theorem B447251 : Blo 295830 447251 := bstep (se 1 (by rfl) ⟨335438, by rfl⟩ : syracuseStep 447251 = 670877) B670877
theorem B447281 : Blo 295830 447281 := bstep (se 2 (by rfl) ⟨167730, by rfl⟩ : syracuseStep 447281 = 335461) B335461
theorem B6476597 : Blo 295830 6476597 := bstep (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) B607181
theorem B447299 : Blo 295830 447299 := bstep (se 1 (by rfl) ⟨335474, by rfl⟩ : syracuseStep 447299 = 670949) B670949
theorem B447329 : Blo 295830 447329 := bstep (se 2 (by rfl) ⟨167748, by rfl⟩ : syracuseStep 447329 = 335497) B335497
theorem B1364849 : Blo 295830 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B447347 : Blo 295830 447347 := bstep (se 1 (by rfl) ⟨335510, by rfl⟩ : syracuseStep 447347 = 671021) B671021
theorem B447377 : Blo 295830 447377 := bstep (se 2 (by rfl) ⟨167766, by rfl⟩ : syracuseStep 447377 = 335533) B335533
theorem B447395 : Blo 295830 447395 := bstep (se 1 (by rfl) ⟨335546, by rfl⟩ : syracuseStep 447395 = 671093) B671093
theorem B447425 : Blo 295830 447425 := bstep (se 2 (by rfl) ⟨167784, by rfl⟩ : syracuseStep 447425 = 335569) B335569
theorem B447443 : Blo 295830 447443 := bstep (se 1 (by rfl) ⟨335582, by rfl⟩ : syracuseStep 447443 = 671165) B671165
theorem B447473 : Blo 295830 447473 := bstep (se 2 (by rfl) ⟨167802, by rfl⟩ : syracuseStep 447473 = 335605) B335605
theorem B447491 : Blo 295830 447491 := bstep (se 1 (by rfl) ⟨335618, by rfl⟩ : syracuseStep 447491 = 671237) B671237
theorem B1004561 : Blo 295830 1004561 := bstep (se 2 (by rfl) ⟨376710, by rfl⟩ : syracuseStep 1004561 = 753421) B753421
theorem B447521 : Blo 295830 447521 := bstep (se 2 (by rfl) ⟨167820, by rfl⟩ : syracuseStep 447521 = 335641) B335641
theorem B447539 : Blo 295830 447539 := bstep (se 1 (by rfl) ⟨335654, by rfl⟩ : syracuseStep 447539 = 671309) B671309
theorem B1201229 : Blo 295830 1201229 := bstep (se 3 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 1201229 = 450461) B450461
theorem B447569 : Blo 295830 447569 := bstep (se 2 (by rfl) ⟨167838, by rfl⟩ : syracuseStep 447569 = 335677) B335677
theorem B447587 : Blo 295830 447587 := bstep (se 1 (by rfl) ⟨335690, by rfl⟩ : syracuseStep 447587 = 671381) B671381
theorem B447617 : Blo 295830 447617 := bstep (se 2 (by rfl) ⟨167856, by rfl⟩ : syracuseStep 447617 = 335713) B335713
theorem B382099 : Blo 295830 382099 := bstep (se 1 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 382099 = 573149) B573149
theorem B447635 : Blo 295830 447635 := bstep (se 1 (by rfl) ⟨335726, by rfl⟩ : syracuseStep 447635 = 671453) B671453
theorem B447665 : Blo 295830 447665 := bstep (se 2 (by rfl) ⟨167874, by rfl⟩ : syracuseStep 447665 = 335749) B335749
theorem B447683 : Blo 295830 447683 := bstep (se 1 (by rfl) ⟨335762, by rfl⟩ : syracuseStep 447683 = 671525) B671525
theorem B447713 : Blo 295830 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B1692899 : Blo 295830 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B447731 : Blo 295830 447731 := bstep (se 1 (by rfl) ⟨335798, by rfl⟩ : syracuseStep 447731 = 671597) B671597
theorem B447761 : Blo 295830 447761 := bstep (se 2 (by rfl) ⟨167910, by rfl⟩ : syracuseStep 447761 = 335821) B335821
theorem B447779 : Blo 295830 447779 := bstep (se 1 (by rfl) ⟨335834, by rfl⟩ : syracuseStep 447779 = 671669) B671669
theorem B447809 : Blo 295830 447809 := bstep (se 2 (by rfl) ⟨167928, by rfl⟩ : syracuseStep 447809 = 335857) B335857
theorem B447827 : Blo 295830 447827 := bstep (se 1 (by rfl) ⟨335870, by rfl⟩ : syracuseStep 447827 = 671741) B671741
theorem B447857 : Blo 295830 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B447875 : Blo 295830 447875 := bstep (se 1 (by rfl) ⟨335906, by rfl⟩ : syracuseStep 447875 = 671813) B671813
theorem B447905 : Blo 295830 447905 := bstep (se 2 (by rfl) ⟨167964, by rfl⟩ : syracuseStep 447905 = 335929) B335929
theorem B447923 : Blo 295830 447923 := bstep (se 1 (by rfl) ⟨335942, by rfl⟩ : syracuseStep 447923 = 671885) B671885
theorem B2807237 : Blo 295830 2807237 := bstep (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) B526357
theorem B447953 : Blo 295830 447953 := bstep (se 2 (by rfl) ⟨167982, by rfl⟩ : syracuseStep 447953 = 335965) B335965
theorem B447971 : Blo 295830 447971 := bstep (se 1 (by rfl) ⟨335978, by rfl⟩ : syracuseStep 447971 = 671957) B671957
theorem B448001 : Blo 295830 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B448019 : Blo 295830 448019 := bstep (se 1 (by rfl) ⟨336014, by rfl⟩ : syracuseStep 448019 = 672029) B672029
theorem B1005101 : Blo 295830 1005101 := bstep (se 3 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 1005101 = 376913) B376913
theorem B448049 : Blo 295830 448049 := bstep (se 2 (by rfl) ⟨168018, by rfl⟩ : syracuseStep 448049 = 336037) B336037
theorem B1136177 : Blo 295830 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B448067 : Blo 295830 448067 := bstep (se 1 (by rfl) ⟨336050, by rfl⟩ : syracuseStep 448067 = 672101) B672101
theorem B448097 : Blo 295830 448097 := bstep (se 2 (by rfl) ⟨168036, by rfl⟩ : syracuseStep 448097 = 336073) B336073
theorem B1005155 : Blo 295830 1005155 := bstep (se 1 (by rfl) ⟨753866, by rfl⟩ : syracuseStep 1005155 = 1507733) B1507733
theorem B448115 : Blo 295830 448115 := bstep (se 1 (by rfl) ⟨336086, by rfl⟩ : syracuseStep 448115 = 672173) B672173
theorem B448145 : Blo 295830 448145 := bstep (se 2 (by rfl) ⟨168054, by rfl⟩ : syracuseStep 448145 = 336109) B336109
theorem B448163 : Blo 295830 448163 := bstep (se 1 (by rfl) ⟨336122, by rfl⟩ : syracuseStep 448163 = 672245) B672245
theorem B448193 : Blo 295830 448193 := bstep (se 2 (by rfl) ⟨168072, by rfl⟩ : syracuseStep 448193 = 336145) B336145
theorem B448211 : Blo 295830 448211 := bstep (se 1 (by rfl) ⟨336158, by rfl⟩ : syracuseStep 448211 = 672317) B672317
theorem B448241 : Blo 295830 448241 := bstep (se 2 (by rfl) ⟨168090, by rfl⟩ : syracuseStep 448241 = 336181) B336181
theorem B448259 : Blo 295830 448259 := bstep (se 1 (by rfl) ⟨336194, by rfl⟩ : syracuseStep 448259 = 672389) B672389
theorem B448289 : Blo 295830 448289 := bstep (se 2 (by rfl) ⟨168108, by rfl⟩ : syracuseStep 448289 = 336217) B336217
theorem B448307 : Blo 295830 448307 := bstep (se 1 (by rfl) ⟨336230, by rfl⟩ : syracuseStep 448307 = 672461) B672461
theorem B448337 : Blo 295830 448337 := bstep (se 2 (by rfl) ⟨168126, by rfl⟩ : syracuseStep 448337 = 336253) B336253
theorem B448355 : Blo 295830 448355 := bstep (se 1 (by rfl) ⟨336266, by rfl⟩ : syracuseStep 448355 = 672533) B672533
theorem B1005425 : Blo 295830 1005425 := bstep (se 2 (by rfl) ⟨377034, by rfl⟩ : syracuseStep 1005425 = 754069) B754069
theorem B448385 : Blo 295830 448385 := bstep (se 2 (by rfl) ⟨168144, by rfl⟩ : syracuseStep 448385 = 336289) B336289
theorem B776081 : Blo 295830 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B448403 : Blo 295830 448403 := bstep (se 1 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 448403 = 672605) B672605
theorem B448433 : Blo 295830 448433 := bstep (se 2 (by rfl) ⟨168162, by rfl⟩ : syracuseStep 448433 = 336325) B336325
theorem B317363 : Blo 295830 317363 := bstep (se 1 (by rfl) ⟨238022, by rfl⟩ : syracuseStep 317363 = 476045) B476045
theorem B448451 : Blo 295830 448451 := bstep (se 1 (by rfl) ⟨336338, by rfl⟩ : syracuseStep 448451 = 672677) B672677
theorem B448481 : Blo 295830 448481 := bstep (se 2 (by rfl) ⟨168180, by rfl⟩ : syracuseStep 448481 = 336361) B336361
theorem B448499 : Blo 295830 448499 := bstep (se 1 (by rfl) ⟨336374, by rfl⟩ : syracuseStep 448499 = 672749) B672749
theorem B448529 : Blo 295830 448529 := bstep (se 2 (by rfl) ⟨168198, by rfl⟩ : syracuseStep 448529 = 336397) B336397
theorem B448547 : Blo 295830 448547 := bstep (se 1 (by rfl) ⟨336410, by rfl⟩ : syracuseStep 448547 = 672821) B672821
theorem B448577 : Blo 295830 448577 := bstep (se 2 (by rfl) ⟨168216, by rfl⟩ : syracuseStep 448577 = 336433) B336433
theorem B448595 : Blo 295830 448595 := bstep (se 1 (by rfl) ⟨336446, by rfl⟩ : syracuseStep 448595 = 672893) B672893
theorem B448625 : Blo 295830 448625 := bstep (se 2 (by rfl) ⟨168234, by rfl⟩ : syracuseStep 448625 = 336469) B336469
theorem B481411 : Blo 295830 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B448643 : Blo 295830 448643 := bstep (se 1 (by rfl) ⟨336482, by rfl⟩ : syracuseStep 448643 = 672965) B672965
theorem B448673 : Blo 295830 448673 := bstep (se 2 (by rfl) ⟨168252, by rfl⟩ : syracuseStep 448673 = 336505) B336505
theorem B710819 : Blo 295830 710819 := bstep (se 1 (by rfl) ⟨533114, by rfl⟩ : syracuseStep 710819 = 1066229) B1066229
theorem B448691 : Blo 295830 448691 := bstep (se 1 (by rfl) ⟨336518, by rfl⟩ : syracuseStep 448691 = 673037) B673037
theorem B448721 : Blo 295830 448721 := bstep (se 2 (by rfl) ⟨168270, by rfl⟩ : syracuseStep 448721 = 336541) B336541
theorem B448739 : Blo 295830 448739 := bstep (se 1 (by rfl) ⟨336554, by rfl⟩ : syracuseStep 448739 = 673109) B673109
theorem B448769 : Blo 295830 448769 := bstep (se 2 (by rfl) ⟨168288, by rfl⟩ : syracuseStep 448769 = 336577) B336577
theorem B448787 : Blo 295830 448787 := bstep (se 1 (by rfl) ⟨336590, by rfl⟩ : syracuseStep 448787 = 673181) B673181
theorem B448817 : Blo 295830 448817 := bstep (se 2 (by rfl) ⟨168306, by rfl⟩ : syracuseStep 448817 = 336613) B336613
theorem B448835 : Blo 295830 448835 := bstep (se 1 (by rfl) ⟨336626, by rfl⟩ : syracuseStep 448835 = 673253) B673253
theorem B448865 : Blo 295830 448865 := bstep (se 2 (by rfl) ⟨168324, by rfl⟩ : syracuseStep 448865 = 336649) B336649
theorem B711011 : Blo 295830 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B448883 : Blo 295830 448883 := bstep (se 1 (by rfl) ⟨336662, by rfl⟩ : syracuseStep 448883 = 673325) B673325
theorem B1005965 : Blo 295830 1005965 := bstep (se 3 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 1005965 = 377237) B377237
theorem B448913 : Blo 295830 448913 := bstep (se 2 (by rfl) ⟨168342, by rfl⟩ : syracuseStep 448913 = 336685) B336685
theorem B448931 : Blo 295830 448931 := bstep (se 1 (by rfl) ⟨336698, by rfl⟩ : syracuseStep 448931 = 673397) B673397
theorem B448961 : Blo 295830 448961 := bstep (se 2 (by rfl) ⟨168360, by rfl⟩ : syracuseStep 448961 = 336721) B336721
theorem B1006019 : Blo 295830 1006019 := bstep (se 1 (by rfl) ⟨754514, by rfl⟩ : syracuseStep 1006019 = 1509029) B1509029
theorem B448979 : Blo 295830 448979 := bstep (se 1 (by rfl) ⟨336734, by rfl⟩ : syracuseStep 448979 = 673469) B673469
theorem B449009 : Blo 295830 449009 := bstep (se 2 (by rfl) ⟨168378, by rfl⟩ : syracuseStep 449009 = 336757) B336757
theorem B449027 : Blo 295830 449027 := bstep (se 1 (by rfl) ⟨336770, by rfl⟩ : syracuseStep 449027 = 673541) B673541
theorem B449057 : Blo 295830 449057 := bstep (se 2 (by rfl) ⟨168396, by rfl⟩ : syracuseStep 449057 = 336793) B336793
theorem B449075 : Blo 295830 449075 := bstep (se 1 (by rfl) ⟨336806, by rfl⟩ : syracuseStep 449075 = 673613) B673613
theorem B907853 : Blo 295830 907853 := bstep (se 3 (by rfl) ⟨170222, by rfl⟩ : syracuseStep 907853 = 340445) B340445
theorem B449105 : Blo 295830 449105 := bstep (se 2 (by rfl) ⟨168414, by rfl⟩ : syracuseStep 449105 = 336829) B336829
theorem B449123 : Blo 295830 449123 := bstep (se 1 (by rfl) ⟨336842, by rfl⟩ : syracuseStep 449123 = 673685) B673685
theorem B449153 : Blo 295830 449153 := bstep (se 2 (by rfl) ⟨168432, by rfl⟩ : syracuseStep 449153 = 336865) B336865
theorem B711299 : Blo 295830 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B2153101 : Blo 295830 2153101 := bstep (se 3 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 2153101 = 807413) B807413
theorem B449171 : Blo 295830 449171 := bstep (se 1 (by rfl) ⟨336878, by rfl⟩ : syracuseStep 449171 = 673757) B673757
theorem B318115 : Blo 295830 318115 := bstep (se 1 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 318115 = 477173) B477173
theorem B1727153 : Blo 295830 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B449201 : Blo 295830 449201 := bstep (se 2 (by rfl) ⟨168450, by rfl⟩ : syracuseStep 449201 = 336901) B336901
theorem B449219 : Blo 295830 449219 := bstep (se 1 (by rfl) ⟨336914, by rfl⟩ : syracuseStep 449219 = 673829) B673829
theorem B1006289 : Blo 295830 1006289 := bstep (se 2 (by rfl) ⟨377358, by rfl⟩ : syracuseStep 1006289 = 754717) B754717
theorem B449249 : Blo 295830 449249 := bstep (se 2 (by rfl) ⟨168468, by rfl⟩ : syracuseStep 449249 = 336937) B336937
theorem B449267 : Blo 295830 449267 := bstep (se 1 (by rfl) ⟨336950, by rfl⟩ : syracuseStep 449267 = 673901) B673901
theorem B449297 : Blo 295830 449297 := bstep (se 2 (by rfl) ⟨168486, by rfl⟩ : syracuseStep 449297 = 336973) B336973
theorem B449315 : Blo 295830 449315 := bstep (se 1 (by rfl) ⟨336986, by rfl⟩ : syracuseStep 449315 = 673973) B673973
theorem B449345 : Blo 295830 449345 := bstep (se 2 (by rfl) ⟨168504, by rfl⟩ : syracuseStep 449345 = 337009) B337009
theorem B449363 : Blo 295830 449363 := bstep (se 1 (by rfl) ⟨337022, by rfl⟩ : syracuseStep 449363 = 674045) B674045
theorem B449393 : Blo 295830 449393 := bstep (se 2 (by rfl) ⟨168522, by rfl⟩ : syracuseStep 449393 = 337045) B337045
theorem B449411 : Blo 295830 449411 := bstep (se 1 (by rfl) ⟨337058, by rfl⟩ : syracuseStep 449411 = 674117) B674117
theorem B449441 : Blo 295830 449441 := bstep (se 2 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 449441 = 337081) B337081
theorem B449459 : Blo 295830 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B3398597 : Blo 295830 3398597 := bstep (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) B637237
theorem B449489 : Blo 295830 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B678883 : Blo 295830 678883 := bstep (se 1 (by rfl) ⟨509162, by rfl⟩ : syracuseStep 678883 = 1018325) B1018325
theorem B1137635 : Blo 295830 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B449507 : Blo 295830 449507 := bstep (se 1 (by rfl) ⟨337130, by rfl⟩ : syracuseStep 449507 = 674261) B674261
theorem B449537 : Blo 295830 449537 := bstep (se 2 (by rfl) ⟨168576, by rfl⟩ : syracuseStep 449537 = 337153) B337153
theorem B449555 : Blo 295830 449555 := bstep (se 1 (by rfl) ⟨337166, by rfl⟩ : syracuseStep 449555 = 674333) B674333
theorem B449585 : Blo 295830 449585 := bstep (se 2 (by rfl) ⟨168594, by rfl⟩ : syracuseStep 449585 = 337189) B337189
theorem B449603 : Blo 295830 449603 := bstep (se 1 (by rfl) ⟨337202, by rfl⟩ : syracuseStep 449603 = 674405) B674405
theorem B1694789 : Blo 295830 1694789 := bstep (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) B317773
theorem B449633 : Blo 295830 449633 := bstep (se 2 (by rfl) ⟨168612, by rfl⟩ : syracuseStep 449633 = 337225) B337225
theorem B842861 : Blo 295830 842861 := bstep (se 3 (by rfl) ⟨158036, by rfl⟩ : syracuseStep 842861 = 316073) B316073
theorem B449651 : Blo 295830 449651 := bstep (se 1 (by rfl) ⟨337238, by rfl⟩ : syracuseStep 449651 = 674477) B674477
theorem B449681 : Blo 295830 449681 := bstep (se 2 (by rfl) ⟨168630, by rfl⟩ : syracuseStep 449681 = 337261) B337261
theorem B449699 : Blo 295830 449699 := bstep (se 1 (by rfl) ⟨337274, by rfl⟩ : syracuseStep 449699 = 674549) B674549
theorem B449729 : Blo 295830 449729 := bstep (se 2 (by rfl) ⟨168648, by rfl⟩ : syracuseStep 449729 = 337297) B337297
theorem B1006829 : Blo 295830 1006829 := bstep (se 3 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 1006829 = 377561) B377561
theorem B843043 : Blo 295830 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B1006883 : Blo 295830 1006883 := bstep (se 1 (by rfl) ⟨755162, by rfl⟩ : syracuseStep 1006883 = 1510325) B1510325
theorem B1039661 : Blo 295830 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B843203 : Blo 295830 843203 := bstep (se 1 (by rfl) ⟨632402, by rfl⟩ : syracuseStep 843203 = 1264805) B1264805
theorem B712241 : Blo 295830 712241 := bstep (se 2 (by rfl) ⟨267090, by rfl⟩ : syracuseStep 712241 = 534181) B534181
theorem B1007153 : Blo 295830 1007153 := bstep (se 2 (by rfl) ⟨377682, by rfl⟩ : syracuseStep 1007153 = 755365) B755365
theorem B1269539 : Blo 295830 1269539 := bstep (se 1 (by rfl) ⟨952154, by rfl⟩ : syracuseStep 1269539 = 1904309) B1904309
theorem B2973509 : Blo 295830 2973509 := bstep (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) B557533
theorem B319507 : Blo 295830 319507 := bstep (se 1 (by rfl) ⟨239630, by rfl⟩ : syracuseStep 319507 = 479261) B479261
theorem B1007693 : Blo 295830 1007693 := bstep (se 3 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 1007693 = 377885) B377885
theorem B1007747 : Blo 295830 1007747 := bstep (se 1 (by rfl) ⟨755810, by rfl⟩ : syracuseStep 1007747 = 1511621) B1511621
theorem B909485 : Blo 295830 909485 := bstep (se 3 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 909485 = 341057) B341057
theorem B1008017 : Blo 295830 1008017 := bstep (se 2 (by rfl) ⟨378006, by rfl⟩ : syracuseStep 1008017 = 756013) B756013
theorem B1499633 : Blo 295830 1499633 := bstep (se 2 (by rfl) ⟨562362, by rfl⟩ : syracuseStep 1499633 = 1124725) B1124725
theorem B844273 : Blo 295830 844273 := bstep (se 2 (by rfl) ⟨316602, by rfl⟩ : syracuseStep 844273 = 633205) B633205
theorem B2253581 : Blo 295830 2253581 := bstep (se 3 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 2253581 = 845093) B845093
theorem B910129 : Blo 295830 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B1008557 : Blo 295830 1008557 := bstep (se 3 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 1008557 = 378209) B378209
theorem B1008611 : Blo 295830 1008611 := bstep (se 1 (by rfl) ⟨756458, by rfl⟩ : syracuseStep 1008611 = 1512917) B1512917
theorem B681137 : Blo 295830 681137 := bstep (se 2 (by rfl) ⟨255426, by rfl⟩ : syracuseStep 681137 = 510853) B510853
theorem B1008881 : Blo 295830 1008881 := bstep (se 2 (by rfl) ⟨378330, by rfl⟩ : syracuseStep 1008881 = 756661) B756661
theorem B1074865 : Blo 295830 1074865 := bstep (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) B806149
theorem B845549 : Blo 295830 845549 := bstep (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) B317081
theorem B1271537 : Blo 295830 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B1206029 : Blo 295830 1206029 := bstep (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) B452261
theorem B1009421 : Blo 295830 1009421 := bstep (se 3 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 1009421 = 378533) B378533
theorem B1074979 : Blo 295830 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B1009475 : Blo 295830 1009475 := bstep (se 1 (by rfl) ⟨757106, by rfl⟩ : syracuseStep 1009475 = 1514213) B1514213
theorem B1501091 : Blo 295830 1501091 := bstep (se 1 (by rfl) ⟨1125818, by rfl⟩ : syracuseStep 1501091 = 2251637) B2251637
theorem B845731 : Blo 295830 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B845777 : Blo 295830 845777 := bstep (se 2 (by rfl) ⟨317166, by rfl⟩ : syracuseStep 845777 = 634333) B634333
theorem B911405 : Blo 295830 911405 := bstep (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) B341777
theorem B1009745 : Blo 295830 1009745 := bstep (se 2 (by rfl) ⟨378654, by rfl⟩ : syracuseStep 1009745 = 757309) B757309
theorem B7301573 : Blo 295830 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B1600013 : Blo 295830 1600013 := bstep (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) B600005
theorem B3238469 : Blo 295830 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B1010285 : Blo 295830 1010285 := bstep (se 3 (by rfl) ⟨189428, by rfl⟩ : syracuseStep 1010285 = 378857) B378857
theorem B1010339 : Blo 295830 1010339 := bstep (se 1 (by rfl) ⟨757754, by rfl⟩ : syracuseStep 1010339 = 1515509) B1515509
theorem B453313 : Blo 295830 453313 := bstep (se 2 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 453313 = 339985) B339985
theorem B1501901 : Blo 295830 1501901 := bstep (se 3 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 1501901 = 563213) B563213
theorem B1141553 : Blo 295830 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B682897 : Blo 295830 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B1010609 : Blo 295830 1010609 := bstep (se 2 (by rfl) ⟨378978, by rfl⟩ : syracuseStep 1010609 = 757957) B757957
theorem B3828707 : Blo 295830 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B748835 : Blo 295830 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B847235 : Blo 295830 847235 := bstep (se 1 (by rfl) ⟨635426, by rfl⟩ : syracuseStep 847235 = 1270853) B1270853
theorem B1273229 : Blo 295830 1273229 := bstep (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) B477461
theorem B1011149 : Blo 295830 1011149 := bstep (se 3 (by rfl) ⟨189590, by rfl⟩ : syracuseStep 1011149 = 379181) B379181
theorem B749027 : Blo 295830 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B1011203 : Blo 295830 1011203 := bstep (se 1 (by rfl) ⟨758402, by rfl⟩ : syracuseStep 1011203 = 1516805) B1516805
theorem B1535537 : Blo 295830 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B2256497 : Blo 295830 2256497 := bstep (se 2 (by rfl) ⟨846186, by rfl⟩ : syracuseStep 2256497 = 1692373) B1692373
theorem B2551409 : Blo 295830 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B1011473 : Blo 295830 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B421681 : Blo 295830 421681 := bstep (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) B316261
theorem B2420549 : Blo 295830 2420549 := bstep (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) B453853
theorem B8613773 : Blo 295830 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B421795 : Blo 295830 421795 := bstep (se 1 (by rfl) ⟨316346, by rfl⟩ : syracuseStep 421795 = 632693) B632693
theorem B323555 : Blo 295830 323555 := bstep (se 1 (by rfl) ⟨242666, by rfl⟩ : syracuseStep 323555 = 485333) B485333
theorem B4321421 : Blo 295830 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B4321649 : Blo 295830 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B749969 : Blo 295830 749969 := bstep (se 2 (by rfl) ⟨281238, by rfl⟩ : syracuseStep 749969 = 562477) B562477
theorem B750019 : Blo 295830 750019 := bstep (se 1 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 750019 = 1125029) B1125029
theorem B750161 : Blo 295830 750161 := bstep (se 2 (by rfl) ⟨281310, by rfl⟩ : syracuseStep 750161 = 562621) B562621
theorem B848465 : Blo 295830 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B3404429 : Blo 295830 3404429 := bstep (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) B1276661
theorem B1700621 : Blo 295830 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B357139 : Blo 295830 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B455843 : Blo 295830 455843 := bstep (se 1 (by rfl) ⟨341882, by rfl⟩ : syracuseStep 455843 = 683765) B683765
theorem B423139 : Blo 295830 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B1799651 : Blo 295830 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B1930787 : Blo 295830 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B751153 : Blo 295830 751153 := bstep (se 2 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 751153 = 563365) B563365
theorem B1504817 : Blo 295830 1504817 := bstep (se 2 (by rfl) ⟨564306, by rfl⟩ : syracuseStep 1504817 = 1128613) B1128613
theorem B751427 : Blo 295830 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B1210211 : Blo 295830 1210211 := bstep (se 1 (by rfl) ⟨907658, by rfl⟩ : syracuseStep 1210211 = 1815317) B1815317
theorem B1898437 : Blo 295830 1898437 := bstep (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) B355957
theorem B751619 : Blo 295830 751619 := bstep (se 1 (by rfl) ⟨563714, by rfl⟩ : syracuseStep 751619 = 1127429) B1127429
theorem B849923 : Blo 295830 849923 := bstep (se 1 (by rfl) ⟨637442, by rfl⟩ : syracuseStep 849923 = 1274885) B1274885
theorem B2553869 : Blo 295830 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B817361 : Blo 295830 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B2291939 : Blo 295830 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B424273 : Blo 295830 424273 := bstep (se 2 (by rfl) ⟨159102, by rfl⟩ : syracuseStep 424273 = 318205) B318205
theorem B424369 : Blo 295830 424369 := bstep (se 2 (by rfl) ⟨159138, by rfl⟩ : syracuseStep 424369 = 318277) B318277
theorem B2062883 : Blo 295830 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B850733 : Blo 295830 850733 := bstep (se 3 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 850733 = 319025) B319025
theorem B1211249 : Blo 295830 1211249 := bstep (se 2 (by rfl) ⟨454218, by rfl⟩ : syracuseStep 1211249 = 908437) B908437
theorem B719729 : Blo 295830 719729 := bstep (se 2 (by rfl) ⟨269898, by rfl⟩ : syracuseStep 719729 = 539797) B539797
theorem B424865 : Blo 295830 424865 := bstep (se 2 (by rfl) ⟨159324, by rfl⟩ : syracuseStep 424865 = 318649) B318649
theorem B752561 : Blo 295830 752561 := bstep (se 2 (by rfl) ⟨282210, by rfl⟩ : syracuseStep 752561 = 564421) B564421
theorem B1702853 : Blo 295830 1702853 := bstep (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) B319285
theorem B752611 : Blo 295830 752611 := bstep (se 1 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 752611 = 1128917) B1128917
theorem B1506275 : Blo 295830 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B850925 : Blo 295830 850925 := bstep (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) B319097
theorem B752753 : Blo 295830 752753 := bstep (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) B564565
theorem B5078213 : Blo 295830 5078213 := bstep (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) B952165
theorem B949553 : Blo 295830 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B949603 : Blo 295830 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B3407345 : Blo 295830 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B1703537 : Blo 295830 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1277603 : Blo 295830 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B425731 : Blo 295830 425731 := bstep (se 1 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 425731 = 638597) B638597
theorem B1507085 : Blo 295830 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B327443 : Blo 295830 327443 := bstep (se 1 (by rfl) ⟨245582, by rfl⟩ : syracuseStep 327443 = 491165) B491165
theorem B425827 : Blo 295830 425827 := bstep (se 1 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 425827 = 638741) B638741
theorem B13565893 : Blo 295830 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B851917 : Blo 295830 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B1704037 : Blo 295830 1704037 := bstep (se 4 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 1704037 = 319507) B319507
theorem B753857 : Blo 295830 753857 := bstep (se 2 (by rfl) ⟨282696, by rfl⟩ : syracuseStep 753857 = 565393) B565393
theorem B950935 : Blo 295830 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B1508057 : Blo 295830 1508057 := bstep (se 2 (by rfl) ⟨565521, by rfl⟩ : syracuseStep 1508057 = 1131043) B1131043
theorem B754393 : Blo 295830 754393 := bstep (se 2 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 754393 = 565795) B565795
theorem B295831 : Blo 295830 295831 := bstep (se 1 (by rfl) ⟨221873, by rfl⟩ : syracuseStep 295831 = 443747) B443747
theorem B295851 : Blo 295830 295851 := bstep (se 1 (by rfl) ⟨221888, by rfl⟩ : syracuseStep 295851 = 443777) B443777
theorem B295863 : Blo 295830 295863 := bstep (se 1 (by rfl) ⟨221897, by rfl⟩ : syracuseStep 295863 = 443795) B443795
theorem B295883 : Blo 295830 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B295895 : Blo 295830 295895 := bstep (se 1 (by rfl) ⟨221921, by rfl⟩ : syracuseStep 295895 = 443843) B443843
theorem B295915 : Blo 295830 295915 := bstep (se 1 (by rfl) ⟨221936, by rfl⟩ : syracuseStep 295915 = 443873) B443873
theorem B295927 : Blo 295830 295927 := bstep (se 1 (by rfl) ⟨221945, by rfl⟩ : syracuseStep 295927 = 443891) B443891
theorem B295947 : Blo 295830 295947 := bstep (se 1 (by rfl) ⟨221960, by rfl⟩ : syracuseStep 295947 = 443921) B443921
theorem B295959 : Blo 295830 295959 := bstep (se 1 (by rfl) ⟨221969, by rfl⟩ : syracuseStep 295959 = 443939) B443939
theorem B295979 : Blo 295830 295979 := bstep (se 1 (by rfl) ⟨221984, by rfl⟩ : syracuseStep 295979 = 443969) B443969
theorem B295991 : Blo 295830 295991 := bstep (se 1 (by rfl) ⟨221993, by rfl⟩ : syracuseStep 295991 = 443987) B443987
theorem B1213505 : Blo 295830 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B296011 : Blo 295830 296011 := bstep (se 1 (by rfl) ⟨222008, by rfl⟩ : syracuseStep 296011 = 444017) B444017
theorem B853067 : Blo 295830 853067 := bstep (se 1 (by rfl) ⟨639800, by rfl⟩ : syracuseStep 853067 = 1279601) B1279601
theorem B296023 : Blo 295830 296023 := bstep (se 1 (by rfl) ⟨222017, by rfl⟩ : syracuseStep 296023 = 444035) B444035
theorem B296043 : Blo 295830 296043 := bstep (se 1 (by rfl) ⟨222032, by rfl⟩ : syracuseStep 296043 = 444065) B444065
theorem B296055 : Blo 295830 296055 := bstep (se 1 (by rfl) ⟨222041, by rfl⟩ : syracuseStep 296055 = 444083) B444083
theorem B296075 : Blo 295830 296075 := bstep (se 1 (by rfl) ⟨222056, by rfl⟩ : syracuseStep 296075 = 444113) B444113
theorem B296087 : Blo 295830 296087 := bstep (se 1 (by rfl) ⟨222065, by rfl⟩ : syracuseStep 296087 = 444131) B444131
theorem B296107 : Blo 295830 296107 := bstep (se 1 (by rfl) ⟨222080, by rfl⟩ : syracuseStep 296107 = 444161) B444161
theorem B296119 : Blo 295830 296119 := bstep (se 1 (by rfl) ⟨222089, by rfl⟩ : syracuseStep 296119 = 444179) B444179
theorem B296139 : Blo 295830 296139 := bstep (se 1 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 296139 = 444209) B444209
theorem B296151 : Blo 295830 296151 := bstep (se 1 (by rfl) ⟨222113, by rfl⟩ : syracuseStep 296151 = 444227) B444227
theorem B296171 : Blo 295830 296171 := bstep (se 1 (by rfl) ⟨222128, by rfl⟩ : syracuseStep 296171 = 444257) B444257
theorem B296183 : Blo 295830 296183 := bstep (se 1 (by rfl) ⟨222137, by rfl⟩ : syracuseStep 296183 = 444275) B444275
theorem B296203 : Blo 295830 296203 := bstep (se 1 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 296203 = 444305) B444305
theorem B296215 : Blo 295830 296215 := bstep (se 1 (by rfl) ⟨222161, by rfl⟩ : syracuseStep 296215 = 444323) B444323
theorem B296235 : Blo 295830 296235 := bstep (se 1 (by rfl) ⟨222176, by rfl⟩ : syracuseStep 296235 = 444353) B444353
theorem B296247 : Blo 295830 296247 := bstep (se 1 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 296247 = 444371) B444371
theorem B296267 : Blo 295830 296267 := bstep (se 1 (by rfl) ⟨222200, by rfl⟩ : syracuseStep 296267 = 444401) B444401
theorem B296279 : Blo 295830 296279 := bstep (se 1 (by rfl) ⟨222209, by rfl⟩ : syracuseStep 296279 = 444419) B444419
theorem B296299 : Blo 295830 296299 := bstep (se 1 (by rfl) ⟨222224, by rfl⟩ : syracuseStep 296299 = 444449) B444449
theorem B5113205 : Blo 295830 5113205 := bstep (se 5 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 5113205 = 479363) B479363
theorem B296311 : Blo 295830 296311 := bstep (se 1 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 296311 = 444467) B444467
theorem B296331 : Blo 295830 296331 := bstep (se 1 (by rfl) ⟨222248, by rfl⟩ : syracuseStep 296331 = 444497) B444497
theorem B296343 : Blo 295830 296343 := bstep (se 1 (by rfl) ⟨222257, by rfl⟩ : syracuseStep 296343 = 444515) B444515
theorem B296363 : Blo 295830 296363 := bstep (se 1 (by rfl) ⟨222272, by rfl⟩ : syracuseStep 296363 = 444545) B444545
theorem B296375 : Blo 295830 296375 := bstep (se 1 (by rfl) ⟨222281, by rfl⟩ : syracuseStep 296375 = 444563) B444563
theorem B296395 : Blo 295830 296395 := bstep (se 1 (by rfl) ⟨222296, by rfl⟩ : syracuseStep 296395 = 444593) B444593
theorem B951755 : Blo 295830 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B296407 : Blo 295830 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B296427 : Blo 295830 296427 := bstep (se 1 (by rfl) ⟨222320, by rfl⟩ : syracuseStep 296427 = 444641) B444641
theorem B296439 : Blo 295830 296439 := bstep (se 1 (by rfl) ⟨222329, by rfl⟩ : syracuseStep 296439 = 444659) B444659
theorem B296459 : Blo 295830 296459 := bstep (se 1 (by rfl) ⟨222344, by rfl⟩ : syracuseStep 296459 = 444689) B444689
theorem B296471 : Blo 295830 296471 := bstep (se 1 (by rfl) ⟨222353, by rfl⟩ : syracuseStep 296471 = 444707) B444707
theorem B296491 : Blo 295830 296491 := bstep (se 1 (by rfl) ⟨222368, by rfl⟩ : syracuseStep 296491 = 444737) B444737
theorem B296503 : Blo 295830 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B296523 : Blo 295830 296523 := bstep (se 1 (by rfl) ⟨222392, by rfl⟩ : syracuseStep 296523 = 444785) B444785
theorem B3868235 : Blo 295830 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B296535 : Blo 295830 296535 := bstep (se 1 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 296535 = 444803) B444803
theorem B296555 : Blo 295830 296555 := bstep (se 1 (by rfl) ⟨222416, by rfl⟩ : syracuseStep 296555 = 444833) B444833
theorem B296567 : Blo 295830 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B296587 : Blo 295830 296587 := bstep (se 1 (by rfl) ⟨222440, by rfl⟩ : syracuseStep 296587 = 444881) B444881
theorem B296599 : Blo 295830 296599 := bstep (se 1 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 296599 = 444899) B444899
theorem B296619 : Blo 295830 296619 := bstep (se 1 (by rfl) ⟨222464, by rfl⟩ : syracuseStep 296619 = 444929) B444929
theorem B296631 : Blo 295830 296631 := bstep (se 1 (by rfl) ⟨222473, by rfl⟩ : syracuseStep 296631 = 444947) B444947
theorem B296651 : Blo 295830 296651 := bstep (se 1 (by rfl) ⟨222488, by rfl⟩ : syracuseStep 296651 = 444977) B444977
theorem B296663 : Blo 295830 296663 := bstep (se 1 (by rfl) ⟨222497, by rfl⟩ : syracuseStep 296663 = 444995) B444995
theorem B296683 : Blo 295830 296683 := bstep (se 1 (by rfl) ⟨222512, by rfl⟩ : syracuseStep 296683 = 445025) B445025
theorem B296695 : Blo 295830 296695 := bstep (se 1 (by rfl) ⟨222521, by rfl⟩ : syracuseStep 296695 = 445043) B445043
theorem B296715 : Blo 295830 296715 := bstep (se 1 (by rfl) ⟨222536, by rfl⟩ : syracuseStep 296715 = 445073) B445073
theorem B296727 : Blo 295830 296727 := bstep (se 1 (by rfl) ⟨222545, by rfl⟩ : syracuseStep 296727 = 445091) B445091
theorem B296747 : Blo 295830 296747 := bstep (se 1 (by rfl) ⟨222560, by rfl⟩ : syracuseStep 296747 = 445121) B445121
theorem B755507 : Blo 295830 755507 := bstep (se 1 (by rfl) ⟨566630, by rfl⟩ : syracuseStep 755507 = 1133261) B1133261
theorem B296759 : Blo 295830 296759 := bstep (se 1 (by rfl) ⟨222569, by rfl⟩ : syracuseStep 296759 = 445139) B445139
theorem B296779 : Blo 295830 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B296791 : Blo 295830 296791 := bstep (se 1 (by rfl) ⟨222593, by rfl⟩ : syracuseStep 296791 = 445187) B445187
theorem B296811 : Blo 295830 296811 := bstep (se 1 (by rfl) ⟨222608, by rfl⟩ : syracuseStep 296811 = 445217) B445217
theorem B296823 : Blo 295830 296823 := bstep (se 1 (by rfl) ⟨222617, by rfl⟩ : syracuseStep 296823 = 445235) B445235
theorem B296843 : Blo 295830 296843 := bstep (se 1 (by rfl) ⟨222632, by rfl⟩ : syracuseStep 296843 = 445265) B445265
theorem B296855 : Blo 295830 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B296875 : Blo 295830 296875 := bstep (se 1 (by rfl) ⟨222656, by rfl⟩ : syracuseStep 296875 = 445313) B445313
theorem B296887 : Blo 295830 296887 := bstep (se 1 (by rfl) ⟨222665, by rfl⟩ : syracuseStep 296887 = 445331) B445331
theorem B296907 : Blo 295830 296907 := bstep (se 1 (by rfl) ⟨222680, by rfl⟩ : syracuseStep 296907 = 445361) B445361
theorem B296919 : Blo 295830 296919 := bstep (se 1 (by rfl) ⟨222689, by rfl⟩ : syracuseStep 296919 = 445379) B445379
theorem B296939 : Blo 295830 296939 := bstep (se 1 (by rfl) ⟨222704, by rfl⟩ : syracuseStep 296939 = 445409) B445409
theorem B296951 : Blo 295830 296951 := bstep (se 1 (by rfl) ⟨222713, by rfl⟩ : syracuseStep 296951 = 445427) B445427
theorem B296971 : Blo 295830 296971 := bstep (se 1 (by rfl) ⟨222728, by rfl⟩ : syracuseStep 296971 = 445457) B445457
theorem B854039 : Blo 295830 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B296983 : Blo 295830 296983 := bstep (se 1 (by rfl) ⟨222737, by rfl⟩ : syracuseStep 296983 = 445475) B445475
theorem B297003 : Blo 295830 297003 := bstep (se 1 (by rfl) ⟨222752, by rfl⟩ : syracuseStep 297003 = 445505) B445505
theorem B297015 : Blo 295830 297015 := bstep (se 1 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 297015 = 445523) B445523
theorem B297035 : Blo 295830 297035 := bstep (se 1 (by rfl) ⟨222776, by rfl⟩ : syracuseStep 297035 = 445553) B445553
theorem B297047 : Blo 295830 297047 := bstep (se 1 (by rfl) ⟨222785, by rfl⟩ : syracuseStep 297047 = 445571) B445571
theorem B755801 : Blo 295830 755801 := bstep (se 2 (by rfl) ⟨283425, by rfl⟩ : syracuseStep 755801 = 566851) B566851
theorem B297067 : Blo 295830 297067 := bstep (se 1 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 297067 = 445601) B445601
theorem B297079 : Blo 295830 297079 := bstep (se 1 (by rfl) ⟨222809, by rfl⟩ : syracuseStep 297079 = 445619) B445619
theorem B297099 : Blo 295830 297099 := bstep (se 1 (by rfl) ⟨222824, by rfl⟩ : syracuseStep 297099 = 445649) B445649
theorem B297111 : Blo 295830 297111 := bstep (se 1 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 297111 = 445667) B445667
theorem B297131 : Blo 295830 297131 := bstep (se 1 (by rfl) ⟨222848, by rfl⟩ : syracuseStep 297131 = 445697) B445697
theorem B952499 : Blo 295830 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B297143 : Blo 295830 297143 := bstep (se 1 (by rfl) ⟨222857, by rfl⟩ : syracuseStep 297143 = 445715) B445715
theorem B297163 : Blo 295830 297163 := bstep (se 1 (by rfl) ⟨222872, by rfl⟩ : syracuseStep 297163 = 445745) B445745
theorem B297175 : Blo 295830 297175 := bstep (se 1 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 297175 = 445763) B445763
theorem B297195 : Blo 295830 297195 := bstep (se 1 (by rfl) ⟨222896, by rfl⟩ : syracuseStep 297195 = 445793) B445793
theorem B297207 : Blo 295830 297207 := bstep (se 1 (by rfl) ⟨222905, by rfl⟩ : syracuseStep 297207 = 445811) B445811
theorem B2263301 : Blo 295830 2263301 := bstep (se 4 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 2263301 = 424369) B424369
theorem B297227 : Blo 295830 297227 := bstep (se 1 (by rfl) ⟨222920, by rfl⟩ : syracuseStep 297227 = 445841) B445841
theorem B297239 : Blo 295830 297239 := bstep (se 1 (by rfl) ⟨222929, by rfl⟩ : syracuseStep 297239 = 445859) B445859
theorem B2558243 : Blo 295830 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B297259 : Blo 295830 297259 := bstep (se 1 (by rfl) ⟨222944, by rfl⟩ : syracuseStep 297259 = 445889) B445889
theorem B1509677 : Blo 295830 1509677 := bstep (se 3 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 1509677 = 566129) B566129
theorem B297271 : Blo 295830 297271 := bstep (se 1 (by rfl) ⟨222953, by rfl⟩ : syracuseStep 297271 = 445907) B445907
theorem B297291 : Blo 295830 297291 := bstep (se 1 (by rfl) ⟨222968, by rfl⟩ : syracuseStep 297291 = 445937) B445937
theorem B297303 : Blo 295830 297303 := bstep (se 1 (by rfl) ⟨222977, by rfl⟩ : syracuseStep 297303 = 445955) B445955
theorem B297323 : Blo 295830 297323 := bstep (se 1 (by rfl) ⟨222992, by rfl⟩ : syracuseStep 297323 = 445985) B445985
theorem B297335 : Blo 295830 297335 := bstep (se 1 (by rfl) ⟨223001, by rfl⟩ : syracuseStep 297335 = 446003) B446003
theorem B1280387 : Blo 295830 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B297355 : Blo 295830 297355 := bstep (se 1 (by rfl) ⟨223016, by rfl⟩ : syracuseStep 297355 = 446033) B446033
theorem B297367 : Blo 295830 297367 := bstep (se 1 (by rfl) ⟨223025, by rfl⟩ : syracuseStep 297367 = 446051) B446051
theorem B297387 : Blo 295830 297387 := bstep (se 1 (by rfl) ⟨223040, by rfl⟩ : syracuseStep 297387 = 446081) B446081
theorem B297399 : Blo 295830 297399 := bstep (se 1 (by rfl) ⟨223049, by rfl⟩ : syracuseStep 297399 = 446099) B446099
theorem B297419 : Blo 295830 297419 := bstep (se 1 (by rfl) ⟨223064, by rfl⟩ : syracuseStep 297419 = 446129) B446129
theorem B297431 : Blo 295830 297431 := bstep (se 1 (by rfl) ⟨223073, by rfl⟩ : syracuseStep 297431 = 446147) B446147
theorem B297451 : Blo 295830 297451 := bstep (se 1 (by rfl) ⟨223088, by rfl⟩ : syracuseStep 297451 = 446177) B446177
theorem B297463 : Blo 295830 297463 := bstep (se 1 (by rfl) ⟨223097, by rfl⟩ : syracuseStep 297463 = 446195) B446195
theorem B297483 : Blo 295830 297483 := bstep (se 1 (by rfl) ⟨223112, by rfl⟩ : syracuseStep 297483 = 446225) B446225
theorem B297495 : Blo 295830 297495 := bstep (se 1 (by rfl) ⟨223121, by rfl⟩ : syracuseStep 297495 = 446243) B446243
theorem B297515 : Blo 295830 297515 := bstep (se 1 (by rfl) ⟨223136, by rfl⟩ : syracuseStep 297515 = 446273) B446273
theorem B297527 : Blo 295830 297527 := bstep (se 1 (by rfl) ⟨223145, by rfl⟩ : syracuseStep 297527 = 446291) B446291
theorem B297547 : Blo 295830 297547 := bstep (se 1 (by rfl) ⟨223160, by rfl⟩ : syracuseStep 297547 = 446321) B446321
theorem B297559 : Blo 295830 297559 := bstep (se 1 (by rfl) ⟨223169, by rfl⟩ : syracuseStep 297559 = 446339) B446339
theorem B297579 : Blo 295830 297579 := bstep (se 1 (by rfl) ⟨223184, by rfl⟩ : syracuseStep 297579 = 446369) B446369
theorem B297591 : Blo 295830 297591 := bstep (se 1 (by rfl) ⟨223193, by rfl⟩ : syracuseStep 297591 = 446387) B446387
theorem B297611 : Blo 295830 297611 := bstep (se 1 (by rfl) ⟨223208, by rfl⟩ : syracuseStep 297611 = 446417) B446417
theorem B297623 : Blo 295830 297623 := bstep (se 1 (by rfl) ⟨223217, by rfl⟩ : syracuseStep 297623 = 446435) B446435
theorem B297643 : Blo 295830 297643 := bstep (se 1 (by rfl) ⟨223232, by rfl⟩ : syracuseStep 297643 = 446465) B446465
theorem B1903283 : Blo 295830 1903283 := bstep (se 1 (by rfl) ⟨1427462, by rfl⟩ : syracuseStep 1903283 = 2854925) B2854925
theorem B297655 : Blo 295830 297655 := bstep (se 1 (by rfl) ⟨223241, by rfl⟩ : syracuseStep 297655 = 446483) B446483
theorem B297675 : Blo 295830 297675 := bstep (se 1 (by rfl) ⟨223256, by rfl⟩ : syracuseStep 297675 = 446513) B446513
theorem B297687 : Blo 295830 297687 := bstep (se 1 (by rfl) ⟨223265, by rfl⟩ : syracuseStep 297687 = 446531) B446531
theorem B297707 : Blo 295830 297707 := bstep (se 1 (by rfl) ⟨223280, by rfl⟩ : syracuseStep 297707 = 446561) B446561
theorem B297719 : Blo 295830 297719 := bstep (se 1 (by rfl) ⟨223289, by rfl⟩ : syracuseStep 297719 = 446579) B446579
theorem B297739 : Blo 295830 297739 := bstep (se 1 (by rfl) ⟨223304, by rfl⟩ : syracuseStep 297739 = 446609) B446609
theorem B297751 : Blo 295830 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B297771 : Blo 295830 297771 := bstep (se 1 (by rfl) ⟨223328, by rfl⟩ : syracuseStep 297771 = 446657) B446657
theorem B297783 : Blo 295830 297783 := bstep (se 1 (by rfl) ⟨223337, by rfl⟩ : syracuseStep 297783 = 446675) B446675
theorem B297803 : Blo 295830 297803 := bstep (se 1 (by rfl) ⟨223352, by rfl⟩ : syracuseStep 297803 = 446705) B446705
theorem B297815 : Blo 295830 297815 := bstep (se 1 (by rfl) ⟨223361, by rfl⟩ : syracuseStep 297815 = 446723) B446723
theorem B297835 : Blo 295830 297835 := bstep (se 1 (by rfl) ⟨223376, by rfl⟩ : syracuseStep 297835 = 446753) B446753
theorem B297847 : Blo 295830 297847 := bstep (se 1 (by rfl) ⟨223385, by rfl⟩ : syracuseStep 297847 = 446771) B446771
theorem B297867 : Blo 295830 297867 := bstep (se 1 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 297867 = 446801) B446801
theorem B297879 : Blo 295830 297879 := bstep (se 1 (by rfl) ⟨223409, by rfl⟩ : syracuseStep 297879 = 446819) B446819
theorem B297899 : Blo 295830 297899 := bstep (se 1 (by rfl) ⟨223424, by rfl⟩ : syracuseStep 297899 = 446849) B446849
theorem B297911 : Blo 295830 297911 := bstep (se 1 (by rfl) ⟨223433, by rfl⟩ : syracuseStep 297911 = 446867) B446867
theorem B297931 : Blo 295830 297931 := bstep (se 1 (by rfl) ⟨223448, by rfl⟩ : syracuseStep 297931 = 446897) B446897
theorem B297943 : Blo 295830 297943 := bstep (se 1 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 297943 = 446915) B446915
theorem B297963 : Blo 295830 297963 := bstep (se 1 (by rfl) ⟨223472, by rfl⟩ : syracuseStep 297963 = 446945) B446945
theorem B297975 : Blo 295830 297975 := bstep (se 1 (by rfl) ⟨223481, by rfl⟩ : syracuseStep 297975 = 446963) B446963
theorem B297995 : Blo 295830 297995 := bstep (se 1 (by rfl) ⟨223496, by rfl⟩ : syracuseStep 297995 = 446993) B446993
theorem B298007 : Blo 295830 298007 := bstep (se 1 (by rfl) ⟨223505, by rfl⟩ : syracuseStep 298007 = 447011) B447011
theorem B298027 : Blo 295830 298027 := bstep (se 1 (by rfl) ⟨223520, by rfl⟩ : syracuseStep 298027 = 447041) B447041
theorem B298039 : Blo 295830 298039 := bstep (se 1 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 298039 = 447059) B447059
theorem B2165825 : Blo 295830 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B298059 : Blo 295830 298059 := bstep (se 1 (by rfl) ⟨223544, by rfl⟩ : syracuseStep 298059 = 447089) B447089
theorem B298071 : Blo 295830 298071 := bstep (se 1 (by rfl) ⟨223553, by rfl⟩ : syracuseStep 298071 = 447107) B447107
theorem B2886749 : Blo 295830 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B298091 : Blo 295830 298091 := bstep (se 1 (by rfl) ⟨223568, by rfl⟩ : syracuseStep 298091 = 447137) B447137
theorem B298103 : Blo 295830 298103 := bstep (se 1 (by rfl) ⟨223577, by rfl⟩ : syracuseStep 298103 = 447155) B447155
theorem B298123 : Blo 295830 298123 := bstep (se 1 (by rfl) ⟨223592, by rfl⟩ : syracuseStep 298123 = 447185) B447185
theorem B298135 : Blo 295830 298135 := bstep (se 1 (by rfl) ⟨223601, by rfl⟩ : syracuseStep 298135 = 447203) B447203
theorem B298155 : Blo 295830 298155 := bstep (se 1 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 298155 = 447233) B447233
theorem B298167 : Blo 295830 298167 := bstep (se 1 (by rfl) ⟨223625, by rfl⟩ : syracuseStep 298167 = 447251) B447251
theorem B298187 : Blo 295830 298187 := bstep (se 1 (by rfl) ⟨223640, by rfl⟩ : syracuseStep 298187 = 447281) B447281
theorem B298199 : Blo 295830 298199 := bstep (se 1 (by rfl) ⟨223649, by rfl⟩ : syracuseStep 298199 = 447299) B447299
theorem B298219 : Blo 295830 298219 := bstep (se 1 (by rfl) ⟨223664, by rfl⟩ : syracuseStep 298219 = 447329) B447329
theorem B298231 : Blo 295830 298231 := bstep (se 1 (by rfl) ⟨223673, by rfl⟩ : syracuseStep 298231 = 447347) B447347
theorem B298251 : Blo 295830 298251 := bstep (se 1 (by rfl) ⟨223688, by rfl⟩ : syracuseStep 298251 = 447377) B447377
theorem B298263 : Blo 295830 298263 := bstep (se 1 (by rfl) ⟨223697, by rfl⟩ : syracuseStep 298263 = 447395) B447395
theorem B298283 : Blo 295830 298283 := bstep (se 1 (by rfl) ⟨223712, by rfl⟩ : syracuseStep 298283 = 447425) B447425
theorem B298295 : Blo 295830 298295 := bstep (se 1 (by rfl) ⟨223721, by rfl⟩ : syracuseStep 298295 = 447443) B447443
theorem B298315 : Blo 295830 298315 := bstep (se 1 (by rfl) ⟨223736, by rfl⟩ : syracuseStep 298315 = 447473) B447473
theorem B298327 : Blo 295830 298327 := bstep (se 1 (by rfl) ⟨223745, by rfl⟩ : syracuseStep 298327 = 447491) B447491
theorem B298347 : Blo 295830 298347 := bstep (se 1 (by rfl) ⟨223760, by rfl⟩ : syracuseStep 298347 = 447521) B447521
theorem B298359 : Blo 295830 298359 := bstep (se 1 (by rfl) ⟨223769, by rfl⟩ : syracuseStep 298359 = 447539) B447539
theorem B298379 : Blo 295830 298379 := bstep (se 1 (by rfl) ⟨223784, by rfl⟩ : syracuseStep 298379 = 447569) B447569
theorem B298391 : Blo 295830 298391 := bstep (se 1 (by rfl) ⟨223793, by rfl⟩ : syracuseStep 298391 = 447587) B447587
theorem B298411 : Blo 295830 298411 := bstep (se 1 (by rfl) ⟨223808, by rfl⟩ : syracuseStep 298411 = 447617) B447617
theorem B298423 : Blo 295830 298423 := bstep (se 1 (by rfl) ⟨223817, by rfl⟩ : syracuseStep 298423 = 447635) B447635
theorem B298443 : Blo 295830 298443 := bstep (se 1 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 298443 = 447665) B447665
theorem B298455 : Blo 295830 298455 := bstep (se 1 (by rfl) ⟨223841, by rfl⟩ : syracuseStep 298455 = 447683) B447683
theorem B298475 : Blo 295830 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B298487 : Blo 295830 298487 := bstep (se 1 (by rfl) ⟨223865, by rfl⟩ : syracuseStep 298487 = 447731) B447731
theorem B298507 : Blo 295830 298507 := bstep (se 1 (by rfl) ⟨223880, by rfl⟩ : syracuseStep 298507 = 447761) B447761
theorem B298519 : Blo 295830 298519 := bstep (se 1 (by rfl) ⟨223889, by rfl⟩ : syracuseStep 298519 = 447779) B447779
theorem B298539 : Blo 295830 298539 := bstep (se 1 (by rfl) ⟨223904, by rfl⟩ : syracuseStep 298539 = 447809) B447809
theorem B298551 : Blo 295830 298551 := bstep (se 1 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 298551 = 447827) B447827
theorem B298571 : Blo 295830 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B298583 : Blo 295830 298583 := bstep (se 1 (by rfl) ⟨223937, by rfl⟩ : syracuseStep 298583 = 447875) B447875
theorem B298603 : Blo 295830 298603 := bstep (se 1 (by rfl) ⟨223952, by rfl⟩ : syracuseStep 298603 = 447905) B447905
theorem B298615 : Blo 295830 298615 := bstep (se 1 (by rfl) ⟨223961, by rfl⟩ : syracuseStep 298615 = 447923) B447923
theorem B298635 : Blo 295830 298635 := bstep (se 1 (by rfl) ⟨223976, by rfl⟩ : syracuseStep 298635 = 447953) B447953
theorem B298647 : Blo 295830 298647 := bstep (se 1 (by rfl) ⟨223985, by rfl⟩ : syracuseStep 298647 = 447971) B447971
theorem B298667 : Blo 295830 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B298679 : Blo 295830 298679 := bstep (se 1 (by rfl) ⟨224009, by rfl⟩ : syracuseStep 298679 = 448019) B448019
theorem B298699 : Blo 295830 298699 := bstep (se 1 (by rfl) ⟨224024, by rfl⟩ : syracuseStep 298699 = 448049) B448049
theorem B757451 : Blo 295830 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B298711 : Blo 295830 298711 := bstep (se 1 (by rfl) ⟨224033, by rfl⟩ : syracuseStep 298711 = 448067) B448067
theorem B298731 : Blo 295830 298731 := bstep (se 1 (by rfl) ⟨224048, by rfl⟩ : syracuseStep 298731 = 448097) B448097
theorem B298743 : Blo 295830 298743 := bstep (se 1 (by rfl) ⟨224057, by rfl⟩ : syracuseStep 298743 = 448115) B448115
theorem B298763 : Blo 295830 298763 := bstep (se 1 (by rfl) ⟨224072, by rfl⟩ : syracuseStep 298763 = 448145) B448145
theorem B298775 : Blo 295830 298775 := bstep (se 1 (by rfl) ⟨224081, by rfl⟩ : syracuseStep 298775 = 448163) B448163
theorem B298795 : Blo 295830 298795 := bstep (se 1 (by rfl) ⟨224096, by rfl⟩ : syracuseStep 298795 = 448193) B448193
theorem B298807 : Blo 295830 298807 := bstep (se 1 (by rfl) ⟨224105, by rfl⟩ : syracuseStep 298807 = 448211) B448211
theorem B298827 : Blo 295830 298827 := bstep (se 1 (by rfl) ⟨224120, by rfl⟩ : syracuseStep 298827 = 448241) B448241
theorem B298839 : Blo 295830 298839 := bstep (se 1 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 298839 = 448259) B448259
theorem B298859 : Blo 295830 298859 := bstep (se 1 (by rfl) ⟨224144, by rfl⟩ : syracuseStep 298859 = 448289) B448289
theorem B298871 : Blo 295830 298871 := bstep (se 1 (by rfl) ⟨224153, by rfl⟩ : syracuseStep 298871 = 448307) B448307
theorem B298891 : Blo 295830 298891 := bstep (se 1 (by rfl) ⟨224168, by rfl⟩ : syracuseStep 298891 = 448337) B448337
theorem B298903 : Blo 295830 298903 := bstep (se 1 (by rfl) ⟨224177, by rfl⟩ : syracuseStep 298903 = 448355) B448355
theorem B298923 : Blo 295830 298923 := bstep (se 1 (by rfl) ⟨224192, by rfl⟩ : syracuseStep 298923 = 448385) B448385
theorem B298935 : Blo 295830 298935 := bstep (se 1 (by rfl) ⟨224201, by rfl⟩ : syracuseStep 298935 = 448403) B448403
theorem B298955 : Blo 295830 298955 := bstep (se 1 (by rfl) ⟨224216, by rfl⟩ : syracuseStep 298955 = 448433) B448433
theorem B298967 : Blo 295830 298967 := bstep (se 1 (by rfl) ⟨224225, by rfl⟩ : syracuseStep 298967 = 448451) B448451
theorem B298987 : Blo 295830 298987 := bstep (se 1 (by rfl) ⟨224240, by rfl⟩ : syracuseStep 298987 = 448481) B448481
theorem B298999 : Blo 295830 298999 := bstep (se 1 (by rfl) ⟨224249, by rfl⟩ : syracuseStep 298999 = 448499) B448499
theorem B299019 : Blo 295830 299019 := bstep (se 1 (by rfl) ⟨224264, by rfl⟩ : syracuseStep 299019 = 448529) B448529
theorem B299031 : Blo 295830 299031 := bstep (se 1 (by rfl) ⟨224273, by rfl⟩ : syracuseStep 299031 = 448547) B448547
theorem B299051 : Blo 295830 299051 := bstep (se 1 (by rfl) ⟨224288, by rfl⟩ : syracuseStep 299051 = 448577) B448577
theorem B299063 : Blo 295830 299063 := bstep (se 1 (by rfl) ⟨224297, by rfl⟩ : syracuseStep 299063 = 448595) B448595
theorem B299083 : Blo 295830 299083 := bstep (se 1 (by rfl) ⟨224312, by rfl⟩ : syracuseStep 299083 = 448625) B448625
theorem B299095 : Blo 295830 299095 := bstep (se 1 (by rfl) ⟨224321, by rfl⟩ : syracuseStep 299095 = 448643) B448643
theorem B1904741 : Blo 295830 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B299115 : Blo 295830 299115 := bstep (se 1 (by rfl) ⟨224336, by rfl⟩ : syracuseStep 299115 = 448673) B448673
theorem B299127 : Blo 295830 299127 := bstep (se 1 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 299127 = 448691) B448691
theorem B299147 : Blo 295830 299147 := bstep (se 1 (by rfl) ⟨224360, by rfl⟩ : syracuseStep 299147 = 448721) B448721
theorem B299159 : Blo 295830 299159 := bstep (se 1 (by rfl) ⟨224369, by rfl⟩ : syracuseStep 299159 = 448739) B448739
theorem B299179 : Blo 295830 299179 := bstep (se 1 (by rfl) ⟨224384, by rfl⟩ : syracuseStep 299179 = 448769) B448769
theorem B299191 : Blo 295830 299191 := bstep (se 1 (by rfl) ⟨224393, by rfl⟩ : syracuseStep 299191 = 448787) B448787
theorem B299211 : Blo 295830 299211 := bstep (se 1 (by rfl) ⟨224408, by rfl⟩ : syracuseStep 299211 = 448817) B448817
theorem B299223 : Blo 295830 299223 := bstep (se 1 (by rfl) ⟨224417, by rfl⟩ : syracuseStep 299223 = 448835) B448835
theorem B299243 : Blo 295830 299243 := bstep (se 1 (by rfl) ⟨224432, by rfl⟩ : syracuseStep 299243 = 448865) B448865
theorem B299255 : Blo 295830 299255 := bstep (se 1 (by rfl) ⟨224441, by rfl⟩ : syracuseStep 299255 = 448883) B448883
theorem B299275 : Blo 295830 299275 := bstep (se 1 (by rfl) ⟨224456, by rfl⟩ : syracuseStep 299275 = 448913) B448913
theorem B299287 : Blo 295830 299287 := bstep (se 1 (by rfl) ⟨224465, by rfl⟩ : syracuseStep 299287 = 448931) B448931
theorem B299307 : Blo 295830 299307 := bstep (se 1 (by rfl) ⟨224480, by rfl⟩ : syracuseStep 299307 = 448961) B448961
theorem B299319 : Blo 295830 299319 := bstep (se 1 (by rfl) ⟨224489, by rfl⟩ : syracuseStep 299319 = 448979) B448979
theorem B299339 : Blo 295830 299339 := bstep (se 1 (by rfl) ⟨224504, by rfl⟩ : syracuseStep 299339 = 449009) B449009
theorem B299351 : Blo 295830 299351 := bstep (se 1 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 299351 = 449027) B449027
theorem B299371 : Blo 295830 299371 := bstep (se 1 (by rfl) ⟨224528, by rfl⟩ : syracuseStep 299371 = 449057) B449057
theorem B299383 : Blo 295830 299383 := bstep (se 1 (by rfl) ⟨224537, by rfl⟩ : syracuseStep 299383 = 449075) B449075
theorem B299403 : Blo 295830 299403 := bstep (se 1 (by rfl) ⟨224552, by rfl⟩ : syracuseStep 299403 = 449105) B449105
theorem B299415 : Blo 295830 299415 := bstep (se 1 (by rfl) ⟨224561, by rfl⟩ : syracuseStep 299415 = 449123) B449123
theorem B299435 : Blo 295830 299435 := bstep (se 1 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 299435 = 449153) B449153
theorem B299447 : Blo 295830 299447 := bstep (se 1 (by rfl) ⟨224585, by rfl⟩ : syracuseStep 299447 = 449171) B449171
theorem B1151435 : Blo 295830 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B299467 : Blo 295830 299467 := bstep (se 1 (by rfl) ⟨224600, by rfl⟩ : syracuseStep 299467 = 449201) B449201
theorem B299479 : Blo 295830 299479 := bstep (se 1 (by rfl) ⟨224609, by rfl⟩ : syracuseStep 299479 = 449219) B449219
theorem B299499 : Blo 295830 299499 := bstep (se 1 (by rfl) ⟨224624, by rfl⟩ : syracuseStep 299499 = 449249) B449249
theorem B299511 : Blo 295830 299511 := bstep (se 1 (by rfl) ⟨224633, by rfl⟩ : syracuseStep 299511 = 449267) B449267
theorem B299531 : Blo 295830 299531 := bstep (se 1 (by rfl) ⟨224648, by rfl⟩ : syracuseStep 299531 = 449297) B449297
theorem B299543 : Blo 295830 299543 := bstep (se 1 (by rfl) ⟨224657, by rfl⟩ : syracuseStep 299543 = 449315) B449315
theorem B299563 : Blo 295830 299563 := bstep (se 1 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 299563 = 449345) B449345
theorem B299575 : Blo 295830 299575 := bstep (se 1 (by rfl) ⟨224681, by rfl⟩ : syracuseStep 299575 = 449363) B449363
theorem B299595 : Blo 295830 299595 := bstep (se 1 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 299595 = 449393) B449393
theorem B299607 : Blo 295830 299607 := bstep (se 1 (by rfl) ⟨224705, by rfl⟩ : syracuseStep 299607 = 449411) B449411
theorem B299627 : Blo 295830 299627 := bstep (se 1 (by rfl) ⟨224720, by rfl⟩ : syracuseStep 299627 = 449441) B449441
theorem B299639 : Blo 295830 299639 := bstep (se 1 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 299639 = 449459) B449459
theorem B2265731 : Blo 295830 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B299659 : Blo 295830 299659 := bstep (se 1 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 299659 = 449489) B449489
theorem B758423 : Blo 295830 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B299671 : Blo 295830 299671 := bstep (se 1 (by rfl) ⟨224753, by rfl⟩ : syracuseStep 299671 = 449507) B449507
theorem B299691 : Blo 295830 299691 := bstep (se 1 (by rfl) ⟨224768, by rfl⟩ : syracuseStep 299691 = 449537) B449537
theorem B299703 : Blo 295830 299703 := bstep (se 1 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 299703 = 449555) B449555
theorem B299723 : Blo 295830 299723 := bstep (se 1 (by rfl) ⟨224792, by rfl⟩ : syracuseStep 299723 = 449585) B449585
theorem B299735 : Blo 295830 299735 := bstep (se 1 (by rfl) ⟨224801, by rfl⟩ : syracuseStep 299735 = 449603) B449603
theorem B299755 : Blo 295830 299755 := bstep (se 1 (by rfl) ⟨224816, by rfl⟩ : syracuseStep 299755 = 449633) B449633
theorem B561907 : Blo 295830 561907 := bstep (se 1 (by rfl) ⟨421430, by rfl⟩ : syracuseStep 561907 = 842861) B842861
theorem B299767 : Blo 295830 299767 := bstep (se 1 (by rfl) ⟨224825, by rfl⟩ : syracuseStep 299767 = 449651) B449651
theorem B299787 : Blo 295830 299787 := bstep (se 1 (by rfl) ⟨224840, by rfl⟩ : syracuseStep 299787 = 449681) B449681
theorem B299799 : Blo 295830 299799 := bstep (se 1 (by rfl) ⟨224849, by rfl⟩ : syracuseStep 299799 = 449699) B449699
theorem B299819 : Blo 295830 299819 := bstep (se 1 (by rfl) ⟨224864, by rfl⟩ : syracuseStep 299819 = 449729) B449729
theorem B4854593 : Blo 295830 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B693107 : Blo 295830 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B562135 : Blo 295830 562135 := bstep (se 1 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 562135 = 843203) B843203
theorem B562241 : Blo 295830 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B332887 : Blo 295830 332887 := bstep (se 1 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 332887 = 499331) B499331
theorem B562393 : Blo 295830 562393 := bstep (se 2 (by rfl) ⟨210897, by rfl⟩ : syracuseStep 562393 = 421795) B421795
theorem B333067 : Blo 295830 333067 := bstep (se 1 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 333067 = 499601) B499601
theorem B4560229 : Blo 295830 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B333175 : Blo 295830 333175 := bstep (se 1 (by rfl) ⟨249881, by rfl⟩ : syracuseStep 333175 = 499763) B499763
theorem B2299427 : Blo 295830 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B333355 : Blo 295830 333355 := bstep (se 1 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 333355 = 500033) B500033
theorem B333463 : Blo 295830 333463 := bstep (se 1 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 333463 = 500195) B500195
theorem B333643 : Blo 295830 333643 := bstep (se 1 (by rfl) ⟨250232, by rfl⟩ : syracuseStep 333643 = 500465) B500465
theorem B333751 : Blo 295830 333751 := bstep (se 1 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 333751 = 500627) B500627
theorem B1513565 : Blo 295830 1513565 := bstep (se 3 (by rfl) ⟨283793, by rfl⟩ : syracuseStep 1513565 = 567587) B567587
theorem B333931 : Blo 295830 333931 := bstep (se 1 (by rfl) ⟨250448, by rfl⟩ : syracuseStep 333931 = 500897) B500897
theorem B334039 : Blo 295830 334039 := bstep (se 1 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 334039 = 501059) B501059
theorem B334219 : Blo 295830 334219 := bstep (se 1 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 334219 = 501329) B501329
theorem B563699 : Blo 295830 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B334327 : Blo 295830 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B4299277 : Blo 295830 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B563851 : Blo 295830 563851 := bstep (se 1 (by rfl) ⟨422888, by rfl⟩ : syracuseStep 563851 = 845777) B845777
theorem B334507 : Blo 295830 334507 := bstep (se 1 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 334507 = 501761) B501761
theorem B4266701 : Blo 295830 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B334615 : Blo 295830 334615 := bstep (se 1 (by rfl) ⟨250961, by rfl⟩ : syracuseStep 334615 = 501923) B501923
theorem B334795 : Blo 295830 334795 := bstep (se 1 (by rfl) ⟨251096, by rfl⟩ : syracuseStep 334795 = 502193) B502193
theorem B564185 : Blo 295830 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B334903 : Blo 295830 334903 := bstep (se 1 (by rfl) ⟨251177, by rfl⟩ : syracuseStep 334903 = 502355) B502355
theorem B761035 : Blo 295830 761035 := bstep (se 1 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 761035 = 1141553) B1141553
theorem B335083 : Blo 295830 335083 := bstep (se 1 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 335083 = 502625) B502625
theorem B335191 : Blo 295830 335191 := bstep (se 1 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 335191 = 502787) B502787
theorem B2858341 : Blo 295830 2858341 := bstep (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) B535939
theorem B335371 : Blo 295830 335371 := bstep (se 1 (by rfl) ⟨251528, by rfl⟩ : syracuseStep 335371 = 503057) B503057
theorem B499223 : Blo 295830 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B2399789 : Blo 295830 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B564823 : Blo 295830 564823 := bstep (se 1 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 564823 = 847235) B847235
theorem B335479 : Blo 295830 335479 := bstep (se 1 (by rfl) ⟨251609, by rfl⟩ : syracuseStep 335479 = 503219) B503219
theorem B2301571 : Blo 295830 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B499351 : Blo 295830 499351 := bstep (se 1 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 499351 = 749027) B749027
theorem B1023691 : Blo 295830 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B5086961 : Blo 295830 5086961 := bstep (se 2 (by rfl) ⟨1907610, by rfl⟩ : syracuseStep 5086961 = 3815221) B3815221
theorem B335659 : Blo 295830 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B1613699 : Blo 295830 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B335767 : Blo 295830 335767 := bstep (se 1 (by rfl) ⟨251825, by rfl⟩ : syracuseStep 335767 = 503651) B503651
theorem B2531249 : Blo 295830 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B5742515 : Blo 295830 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B2269133 : Blo 295830 2269133 := bstep (se 3 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 2269133 = 850925) B850925
theorem B335947 : Blo 295830 335947 := bstep (se 1 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 335947 = 503921) B503921
theorem B1515671 : Blo 295830 1515671 := bstep (se 1 (by rfl) ⟨1136753, by rfl⟩ : syracuseStep 1515671 = 2273507) B2273507
theorem B336055 : Blo 295830 336055 := bstep (se 1 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 336055 = 504083) B504083
theorem B499979 : Blo 295830 499979 := bstep (se 1 (by rfl) ⟨374984, by rfl⟩ : syracuseStep 499979 = 749969) B749969
theorem B336235 : Blo 295830 336235 := bstep (se 1 (by rfl) ⟨252176, by rfl⟩ : syracuseStep 336235 = 504353) B504353
theorem B500107 : Blo 295830 500107 := bstep (se 1 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 500107 = 750161) B750161
theorem B565643 : Blo 295830 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B2269619 : Blo 295830 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B565697 : Blo 295830 565697 := bstep (se 2 (by rfl) ⟨212136, by rfl⟩ : syracuseStep 565697 = 424273) B424273
theorem B336343 : Blo 295830 336343 := bstep (se 1 (by rfl) ⟨252257, by rfl⟩ : syracuseStep 336343 = 504515) B504515
theorem B500249 : Blo 295830 500249 := bstep (se 2 (by rfl) ⟨187593, by rfl⟩ : syracuseStep 500249 = 375187) B375187
theorem B336523 : Blo 295830 336523 := bstep (se 1 (by rfl) ⟨252392, by rfl⟩ : syracuseStep 336523 = 504785) B504785
theorem B500377 : Blo 295830 500377 := bstep (se 2 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 500377 = 375283) B375283
theorem B336631 : Blo 295830 336631 := bstep (se 1 (by rfl) ⟨252473, by rfl⟩ : syracuseStep 336631 = 504947) B504947
theorem B303895 : Blo 295830 303895 := bstep (se 1 (by rfl) ⟨227921, by rfl⟩ : syracuseStep 303895 = 455843) B455843
theorem B336811 : Blo 295830 336811 := bstep (se 1 (by rfl) ⟨252608, by rfl⟩ : syracuseStep 336811 = 505217) B505217
theorem B1287191 : Blo 295830 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B336919 : Blo 295830 336919 := bstep (se 1 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 336919 = 505379) B505379
theorem B533569 : Blo 295830 533569 := bstep (se 2 (by rfl) ⟨200088, by rfl⟩ : syracuseStep 533569 = 400177) B400177
theorem B337099 : Blo 295830 337099 := bstep (se 1 (by rfl) ⟨252824, by rfl⟩ : syracuseStep 337099 = 505649) B505649
theorem B500951 : Blo 295830 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B337207 : Blo 295830 337207 := bstep (se 1 (by rfl) ⟨252905, by rfl⟩ : syracuseStep 337207 = 505811) B505811
theorem B501079 : Blo 295830 501079 := bstep (se 1 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 501079 = 751619) B751619
theorem B566615 : Blo 295830 566615 := bstep (se 1 (by rfl) ⟨424961, by rfl⟩ : syracuseStep 566615 = 849923) B849923
theorem B534209 : Blo 295830 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B1124057 : Blo 295830 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B2271077 : Blo 295830 2271077 := bstep (se 4 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 2271077 = 425827) B425827
theorem B567155 : Blo 295830 567155 := bstep (se 1 (by rfl) ⟨425366, by rfl⟩ : syracuseStep 567155 = 850733) B850733
theorem B501707 : Blo 295830 501707 := bstep (se 1 (by rfl) ⟨376280, by rfl⟩ : syracuseStep 501707 = 752561) B752561
theorem B665675 : Blo 295830 665675 := bstep (se 1 (by rfl) ⟨499256, by rfl⟩ : syracuseStep 665675 = 998513) B998513
theorem B501835 : Blo 295830 501835 := bstep (se 1 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 501835 = 752753) B752753
theorem B665729 : Blo 295830 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B3385475 : Blo 295830 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B633035 : Blo 295830 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B501977 : Blo 295830 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B1550657 : Blo 295830 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B2271563 : Blo 295830 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B665945 : Blo 295830 665945 := bstep (se 2 (by rfl) ⟨249729, by rfl⟩ : syracuseStep 665945 = 499459) B499459
theorem B502105 : Blo 295830 502105 := bstep (se 2 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 502105 = 376579) B376579
theorem B567641 : Blo 295830 567641 := bstep (se 2 (by rfl) ⟨212865, by rfl⟩ : syracuseStep 567641 = 425731) B425731
theorem B3221861 : Blo 295830 3221861 := bstep (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) B604099
theorem B3451253 : Blo 295830 3451253 := bstep (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) B323555
theorem B1354157 : Blo 295830 1354157 := bstep (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) B507809
theorem B666035 : Blo 295830 666035 := bstep (se 1 (by rfl) ⟨499526, by rfl⟩ : syracuseStep 666035 = 999053) B999053
theorem B666071 : Blo 295830 666071 := bstep (se 1 (by rfl) ⟨499553, by rfl⟩ : syracuseStep 666071 = 999107) B999107
theorem B666251 : Blo 295830 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B666305 : Blo 295830 666305 := bstep (se 2 (by rfl) ⟨249864, by rfl⟩ : syracuseStep 666305 = 499729) B499729
theorem B338635 : Blo 295830 338635 := bstep (se 1 (by rfl) ⟨253976, by rfl⟩ : syracuseStep 338635 = 507953) B507953
theorem B600791 : Blo 295830 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B961303 : Blo 295830 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B502679 : Blo 295830 502679 := bstep (se 1 (by rfl) ⟨377009, by rfl⟩ : syracuseStep 502679 = 754019) B754019
theorem B666521 : Blo 295830 666521 := bstep (se 2 (by rfl) ⟨249945, by rfl⟩ : syracuseStep 666521 = 499891) B499891
theorem B666611 : Blo 295830 666611 := bstep (se 1 (by rfl) ⟨499958, by rfl⟩ : syracuseStep 666611 = 999917) B999917
theorem B666647 : Blo 295830 666647 := bstep (se 1 (by rfl) ⟨499985, by rfl⟩ : syracuseStep 666647 = 999971) B999971
theorem B502807 : Blo 295830 502807 := bstep (se 1 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 502807 = 754211) B754211
theorem B633881 : Blo 295830 633881 := bstep (se 2 (by rfl) ⟨237705, by rfl⟩ : syracuseStep 633881 = 475411) B475411
theorem B601175 : Blo 295830 601175 := bstep (se 1 (by rfl) ⟨450881, by rfl⟩ : syracuseStep 601175 = 901763) B901763
theorem B666827 : Blo 295830 666827 := bstep (se 1 (by rfl) ⟨500120, by rfl⟩ : syracuseStep 666827 = 1000241) B1000241
theorem B666881 : Blo 295830 666881 := bstep (se 2 (by rfl) ⟨250080, by rfl⟩ : syracuseStep 666881 = 500161) B500161
theorem B1125683 : Blo 295830 1125683 := bstep (se 1 (by rfl) ⟨844262, by rfl⟩ : syracuseStep 1125683 = 1688525) B1688525
theorem B1125697 : Blo 295830 1125697 := bstep (se 2 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 1125697 = 844273) B844273
theorem B667097 : Blo 295830 667097 := bstep (se 2 (by rfl) ⟨250161, by rfl⟩ : syracuseStep 667097 = 500323) B500323
theorem B1224157 : Blo 295830 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B2141741 : Blo 295830 2141741 := bstep (se 3 (by rfl) ⟨401576, by rfl⟩ : syracuseStep 2141741 = 803153) B803153
theorem B667187 : Blo 295830 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B667223 : Blo 295830 667223 := bstep (se 1 (by rfl) ⟨500417, by rfl⟩ : syracuseStep 667223 = 1000835) B1000835
theorem B503435 : Blo 295830 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B536257 : Blo 295830 536257 := bstep (se 2 (by rfl) ⟨201096, by rfl⟩ : syracuseStep 536257 = 402193) B402193
theorem B667403 : Blo 295830 667403 := bstep (se 1 (by rfl) ⟨500552, by rfl⟩ : syracuseStep 667403 = 1001105) B1001105
theorem B503563 : Blo 295830 503563 := bstep (se 1 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 503563 = 755345) B755345
theorem B569099 : Blo 295830 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B634675 : Blo 295830 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B667457 : Blo 295830 667457 := bstep (se 2 (by rfl) ⟨250296, by rfl⟩ : syracuseStep 667457 = 500593) B500593
theorem B536473 : Blo 295830 536473 := bstep (se 2 (by rfl) ⟨201177, by rfl⟩ : syracuseStep 536473 = 402355) B402355
theorem B503705 : Blo 295830 503705 := bstep (se 2 (by rfl) ⟨188889, by rfl⟩ : syracuseStep 503705 = 377779) B377779
theorem B13840307 : Blo 295830 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1814489 : Blo 295830 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B667673 : Blo 295830 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B503833 : Blo 295830 503833 := bstep (se 2 (by rfl) ⟨188937, by rfl⟩ : syracuseStep 503833 = 377875) B377875
theorem B667763 : Blo 295830 667763 := bstep (se 1 (by rfl) ⟨500822, by rfl⟩ : syracuseStep 667763 = 1001645) B1001645
theorem B667799 : Blo 295830 667799 := bstep (se 1 (by rfl) ⟨500849, by rfl⟩ : syracuseStep 667799 = 1001699) B1001699
theorem B3813581 : Blo 295830 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B766169 : Blo 295830 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B667979 : Blo 295830 667979 := bstep (se 1 (by rfl) ⟨500984, by rfl⟩ : syracuseStep 667979 = 1001969) B1001969
theorem B668033 : Blo 295830 668033 := bstep (se 2 (by rfl) ⟨250512, by rfl⟩ : syracuseStep 668033 = 501025) B501025
theorem B537035 : Blo 295830 537035 := bstep (se 1 (by rfl) ⟨402776, by rfl⟩ : syracuseStep 537035 = 805553) B805553
theorem B504407 : Blo 295830 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B668249 : Blo 295830 668249 := bstep (se 2 (by rfl) ⟨250593, by rfl⟩ : syracuseStep 668249 = 501187) B501187
theorem B635521 : Blo 295830 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B668339 : Blo 295830 668339 := bstep (se 1 (by rfl) ⟨501254, by rfl⟩ : syracuseStep 668339 = 1002509) B1002509
theorem B537281 : Blo 295830 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B668375 : Blo 295830 668375 := bstep (se 1 (by rfl) ⟨501281, by rfl⟩ : syracuseStep 668375 = 1002563) B1002563
theorem B504535 : Blo 295830 504535 := bstep (se 1 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 504535 = 756803) B756803
theorem B2405213 : Blo 295830 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B668555 : Blo 295830 668555 := bstep (se 1 (by rfl) ⟨501416, by rfl⟩ : syracuseStep 668555 = 1002833) B1002833
theorem B668609 : Blo 295830 668609 := bstep (se 2 (by rfl) ⟨250728, by rfl⟩ : syracuseStep 668609 = 501457) B501457
theorem B635863 : Blo 295830 635863 := bstep (se 1 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 635863 = 953795) B953795
theorem B668825 : Blo 295830 668825 := bstep (se 2 (by rfl) ⟨250809, by rfl⟩ : syracuseStep 668825 = 501619) B501619
theorem B1127627 : Blo 295830 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B537815 : Blo 295830 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B1127641 : Blo 295830 1127641 := bstep (se 2 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 1127641 = 845731) B845731
theorem B668915 : Blo 295830 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B603379 : Blo 295830 603379 := bstep (se 1 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 603379 = 905069) B905069
theorem B668951 : Blo 295830 668951 := bstep (se 1 (by rfl) ⟨501713, by rfl⟩ : syracuseStep 668951 = 1003427) B1003427
theorem B505163 : Blo 295830 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B669131 : Blo 295830 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B505291 : Blo 295830 505291 := bstep (se 1 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 505291 = 757937) B757937
theorem B669185 : Blo 295830 669185 := bstep (se 2 (by rfl) ⟨250944, by rfl⟩ : syracuseStep 669185 = 501889) B501889
theorem B505433 : Blo 295830 505433 := bstep (se 2 (by rfl) ⟨189537, by rfl⟩ : syracuseStep 505433 = 379075) B379075
theorem B669401 : Blo 295830 669401 := bstep (se 2 (by rfl) ⟨251025, by rfl⟩ : syracuseStep 669401 = 502051) B502051
theorem B505561 : Blo 295830 505561 := bstep (se 2 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 505561 = 379171) B379171
theorem B374539 : Blo 295830 374539 := bstep (se 1 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 374539 = 561809) B561809
theorem B669491 : Blo 295830 669491 := bstep (se 1 (by rfl) ⟨502118, by rfl⟩ : syracuseStep 669491 = 1004237) B1004237
theorem B669527 : Blo 295830 669527 := bstep (se 1 (by rfl) ⟨502145, by rfl⟩ : syracuseStep 669527 = 1004291) B1004291
theorem B669707 : Blo 295830 669707 := bstep (se 1 (by rfl) ⟨502280, by rfl⟩ : syracuseStep 669707 = 1004561) B1004561
theorem B374807 : Blo 295830 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B800819 : Blo 295830 800819 := bstep (se 1 (by rfl) ⟨600614, by rfl⟩ : syracuseStep 800819 = 1201229) B1201229
theorem B669761 : Blo 295830 669761 := bstep (se 2 (by rfl) ⟨251160, by rfl⟩ : syracuseStep 669761 = 502321) B502321
theorem B637067 : Blo 295830 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B1128599 : Blo 295830 1128599 := bstep (se 1 (by rfl) ⟨846449, by rfl⟩ : syracuseStep 1128599 = 1692899) B1692899
theorem B604417 : Blo 295830 604417 := bstep (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) B453313
theorem B669977 : Blo 295830 669977 := bstep (se 2 (by rfl) ⟨251241, by rfl⟩ : syracuseStep 669977 = 502483) B502483
theorem B670067 : Blo 295830 670067 := bstep (se 1 (by rfl) ⟨502550, by rfl⟩ : syracuseStep 670067 = 1005101) B1005101
theorem B670103 : Blo 295830 670103 := bstep (se 1 (by rfl) ⟨502577, by rfl⟩ : syracuseStep 670103 = 1005155) B1005155
theorem B4831757 : Blo 295830 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B7485965 : Blo 295830 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B1161745 : Blo 295830 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B670283 : Blo 295830 670283 := bstep (se 1 (by rfl) ⟨502712, by rfl⟩ : syracuseStep 670283 = 1005425) B1005425
theorem B670337 : Blo 295830 670337 := bstep (se 2 (by rfl) ⟨251376, by rfl⟩ : syracuseStep 670337 = 502753) B502753
theorem B637579 : Blo 295830 637579 := bstep (se 1 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 637579 = 956369) B956369
theorem B375511 : Blo 295830 375511 := bstep (se 1 (by rfl) ⟨281633, by rfl⟩ : syracuseStep 375511 = 563267) B563267
theorem B473879 : Blo 295830 473879 := bstep (se 1 (by rfl) ⟨355409, by rfl⟩ : syracuseStep 473879 = 710819) B710819
theorem B19249973 : Blo 295830 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B670553 : Blo 295830 670553 := bstep (se 2 (by rfl) ⟨251457, by rfl⟩ : syracuseStep 670553 = 502915) B502915
theorem B474007 : Blo 295830 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B2407319 : Blo 295830 2407319 := bstep (se 1 (by rfl) ⟨1805489, by rfl⟩ : syracuseStep 2407319 = 3610979) B3610979
theorem B900019 : Blo 295830 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B670643 : Blo 295830 670643 := bstep (se 1 (by rfl) ⟨502982, by rfl⟩ : syracuseStep 670643 = 1005965) B1005965
theorem B670679 : Blo 295830 670679 := bstep (se 1 (by rfl) ⟨503009, by rfl⟩ : syracuseStep 670679 = 1006019) B1006019
theorem B670859 : Blo 295830 670859 := bstep (se 1 (by rfl) ⟨503144, by rfl⟩ : syracuseStep 670859 = 1006289) B1006289
theorem B670913 : Blo 295830 670913 := bstep (se 2 (by rfl) ⟨251592, by rfl⟩ : syracuseStep 670913 = 503185) B503185
theorem B998621 : Blo 295830 998621 := bstep (se 3 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 998621 = 374483) B374483
theorem B638297 : Blo 295830 638297 := bstep (se 2 (by rfl) ⟨239361, by rfl⟩ : syracuseStep 638297 = 478723) B478723
theorem B1129859 : Blo 295830 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B671129 : Blo 295830 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B540121 : Blo 295830 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B671219 : Blo 295830 671219 := bstep (se 1 (by rfl) ⟨503414, by rfl⟩ : syracuseStep 671219 = 1006829) B1006829
theorem B671255 : Blo 295830 671255 := bstep (se 1 (by rfl) ⟨503441, by rfl⟩ : syracuseStep 671255 = 1006883) B1006883
theorem B474827 : Blo 295830 474827 := bstep (se 1 (by rfl) ⟨356120, by rfl⟩ : syracuseStep 474827 = 712241) B712241
theorem B671435 : Blo 295830 671435 := bstep (se 1 (by rfl) ⟨503576, by rfl⟩ : syracuseStep 671435 = 1007153) B1007153
theorem B5750513 : Blo 295830 5750513 := bstep (se 2 (by rfl) ⟨2156442, by rfl⟩ : syracuseStep 5750513 = 4312885) B4312885
theorem B638707 : Blo 295830 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B671489 : Blo 295830 671489 := bstep (se 2 (by rfl) ⟨251808, by rfl⟩ : syracuseStep 671489 = 503617) B503617
theorem B1982339 : Blo 295830 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B671705 : Blo 295830 671705 := bstep (se 2 (by rfl) ⟨251889, by rfl⟩ : syracuseStep 671705 = 503779) B503779
theorem B671795 : Blo 295830 671795 := bstep (se 1 (by rfl) ⟨503846, by rfl⟩ : syracuseStep 671795 = 1007693) B1007693
theorem B671831 : Blo 295830 671831 := bstep (se 1 (by rfl) ⟨503873, by rfl⟩ : syracuseStep 671831 = 1007747) B1007747
theorem B606323 : Blo 295830 606323 := bstep (se 1 (by rfl) ⟨454742, by rfl⟩ : syracuseStep 606323 = 909485) B909485
theorem B1425559 : Blo 295830 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B672011 : Blo 295830 672011 := bstep (se 1 (by rfl) ⟨504008, by rfl⟩ : syracuseStep 672011 = 1008017) B1008017
theorem B672065 : Blo 295830 672065 := bstep (se 2 (by rfl) ⟨252024, by rfl⟩ : syracuseStep 672065 = 504049) B504049
theorem B999755 : Blo 295830 999755 := bstep (se 1 (by rfl) ⟨749816, by rfl⟩ : syracuseStep 999755 = 1499633) B1499633
theorem B377227 : Blo 295830 377227 := bstep (se 1 (by rfl) ⟨282920, by rfl⟩ : syracuseStep 377227 = 565841) B565841
theorem B672281 : Blo 295830 672281 := bstep (se 2 (by rfl) ⟨252105, by rfl⟩ : syracuseStep 672281 = 504211) B504211
theorem B1000025 : Blo 295830 1000025 := bstep (se 2 (by rfl) ⟨375009, by rfl⟩ : syracuseStep 1000025 = 750019) B750019
theorem B836185 : Blo 295830 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B672371 : Blo 295830 672371 := bstep (se 1 (by rfl) ⟨504278, by rfl⟩ : syracuseStep 672371 = 1008557) B1008557
theorem B672407 : Blo 295830 672407 := bstep (se 1 (by rfl) ⟨504305, by rfl⟩ : syracuseStep 672407 = 1008611) B1008611
theorem B672587 : Blo 295830 672587 := bstep (se 1 (by rfl) ⟨504440, by rfl⟩ : syracuseStep 672587 = 1008881) B1008881
theorem B672641 : Blo 295830 672641 := bstep (se 2 (by rfl) ⟨252240, by rfl⟩ : syracuseStep 672641 = 504481) B504481
theorem B639895 : Blo 295830 639895 := bstep (se 1 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 639895 = 959843) B959843
theorem B639937 : Blo 295830 639937 := bstep (se 2 (by rfl) ⟨239976, by rfl⟩ : syracuseStep 639937 = 479953) B479953
theorem B672857 : Blo 295830 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B804019 : Blo 295830 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B672947 : Blo 295830 672947 := bstep (se 1 (by rfl) ⟨504710, by rfl⟩ : syracuseStep 672947 = 1009421) B1009421
theorem B672983 : Blo 295830 672983 := bstep (se 1 (by rfl) ⟨504737, by rfl⟩ : syracuseStep 672983 = 1009475) B1009475
theorem B1000727 : Blo 295830 1000727 := bstep (se 1 (by rfl) ⟨750545, by rfl⟩ : syracuseStep 1000727 = 1501091) B1501091
theorem B378199 : Blo 295830 378199 := bstep (se 1 (by rfl) ⟨283649, by rfl⟩ : syracuseStep 378199 = 567299) B567299
theorem B607603 : Blo 295830 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B673163 : Blo 295830 673163 := bstep (se 1 (by rfl) ⟨504872, by rfl⟩ : syracuseStep 673163 = 1009745) B1009745
theorem B443801 : Blo 295830 443801 := bstep (se 2 (by rfl) ⟨166425, by rfl⟩ : syracuseStep 443801 = 332851) B332851
theorem B673217 : Blo 295830 673217 := bstep (se 2 (by rfl) ⟨252456, by rfl⟩ : syracuseStep 673217 = 504913) B504913
theorem B443915 : Blo 295830 443915 := bstep (se 1 (by rfl) ⟨332936, by rfl⟩ : syracuseStep 443915 = 665873) B665873
theorem B443927 : Blo 295830 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B509465 : Blo 295830 509465 := bstep (se 2 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 509465 = 382099) B382099
theorem B2606627 : Blo 295830 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B443993 : Blo 295830 443993 := bstep (se 2 (by rfl) ⟨166497, by rfl⟩ : syracuseStep 443993 = 332995) B332995
theorem B4867715 : Blo 295830 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B673433 : Blo 295830 673433 := bstep (se 2 (by rfl) ⟨252537, by rfl⟩ : syracuseStep 673433 = 505075) B505075
theorem B444107 : Blo 295830 444107 := bstep (se 1 (by rfl) ⟨333080, by rfl⟩ : syracuseStep 444107 = 666161) B666161
theorem B444119 : Blo 295830 444119 := bstep (se 1 (by rfl) ⟨333089, by rfl⟩ : syracuseStep 444119 = 666179) B666179
theorem B673523 : Blo 295830 673523 := bstep (se 1 (by rfl) ⟨505142, by rfl⟩ : syracuseStep 673523 = 1010285) B1010285
theorem B2148113 : Blo 295830 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B673559 : Blo 295830 673559 := bstep (se 1 (by rfl) ⟨505169, by rfl⟩ : syracuseStep 673559 = 1010339) B1010339
theorem B444185 : Blo 295830 444185 := bstep (se 2 (by rfl) ⟨166569, by rfl⟩ : syracuseStep 444185 = 333139) B333139
theorem B1001267 : Blo 295830 1001267 := bstep (se 1 (by rfl) ⟨750950, by rfl⟩ : syracuseStep 1001267 = 1501901) B1501901
theorem B444299 : Blo 295830 444299 := bstep (se 1 (by rfl) ⟨333224, by rfl⟩ : syracuseStep 444299 = 666449) B666449
theorem B444311 : Blo 295830 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B673739 : Blo 295830 673739 := bstep (se 1 (by rfl) ⟨505304, by rfl⟩ : syracuseStep 673739 = 1010609) B1010609
theorem B444377 : Blo 295830 444377 := bstep (se 2 (by rfl) ⟨166641, by rfl⟩ : syracuseStep 444377 = 333283) B333283
theorem B4376537 : Blo 295830 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B673793 : Blo 295830 673793 := bstep (se 2 (by rfl) ⟨252672, by rfl⟩ : syracuseStep 673793 = 505345) B505345
theorem B1001537 : Blo 295830 1001537 := bstep (se 2 (by rfl) ⟨375576, by rfl⟩ : syracuseStep 1001537 = 751153) B751153
theorem B444491 : Blo 295830 444491 := bstep (se 1 (by rfl) ⟨333368, by rfl⟩ : syracuseStep 444491 = 666737) B666737
theorem B444503 : Blo 295830 444503 := bstep (se 1 (by rfl) ⟨333377, by rfl⟩ : syracuseStep 444503 = 666755) B666755
theorem B1689731 : Blo 295830 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B379019 : Blo 295830 379019 := bstep (se 1 (by rfl) ⟨284264, by rfl⟩ : syracuseStep 379019 = 568529) B568529
theorem B444569 : Blo 295830 444569 := bstep (se 2 (by rfl) ⟨166713, by rfl⟩ : syracuseStep 444569 = 333427) B333427
theorem B674009 : Blo 295830 674009 := bstep (se 2 (by rfl) ⟨252753, by rfl⟩ : syracuseStep 674009 = 505507) B505507
theorem B444683 : Blo 295830 444683 := bstep (se 1 (by rfl) ⟨333512, by rfl⟩ : syracuseStep 444683 = 667025) B667025
theorem B444695 : Blo 295830 444695 := bstep (se 1 (by rfl) ⟨333521, by rfl⟩ : syracuseStep 444695 = 667043) B667043
theorem B674099 : Blo 295830 674099 := bstep (se 1 (by rfl) ⟨505574, by rfl⟩ : syracuseStep 674099 = 1011149) B1011149
theorem B674135 : Blo 295830 674135 := bstep (se 1 (by rfl) ⟨505601, by rfl⟩ : syracuseStep 674135 = 1011203) B1011203
theorem B444761 : Blo 295830 444761 := bstep (se 2 (by rfl) ⟨166785, by rfl⟩ : syracuseStep 444761 = 333571) B333571
theorem B1132973 : Blo 295830 1132973 := bstep (se 3 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 1132973 = 424865) B424865
theorem B444875 : Blo 295830 444875 := bstep (se 1 (by rfl) ⟨333656, by rfl⟩ : syracuseStep 444875 = 667313) B667313
theorem B444887 : Blo 295830 444887 := bstep (se 1 (by rfl) ⟨333665, by rfl⟩ : syracuseStep 444887 = 667331) B667331
theorem B2279897 : Blo 295830 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B674315 : Blo 295830 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B444953 : Blo 295830 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B674369 : Blo 295830 674369 := bstep (se 2 (by rfl) ⟨252888, by rfl⟩ : syracuseStep 674369 = 505777) B505777
theorem B1002077 : Blo 295830 1002077 := bstep (se 3 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 1002077 = 375779) B375779
theorem B445067 : Blo 295830 445067 := bstep (se 1 (by rfl) ⟨333800, by rfl⟩ : syracuseStep 445067 = 667601) B667601
theorem B445079 : Blo 295830 445079 := bstep (se 1 (by rfl) ⟨333809, by rfl⟩ : syracuseStep 445079 = 667619) B667619
theorem B445145 : Blo 295830 445145 := bstep (se 2 (by rfl) ⟨166929, by rfl⟩ : syracuseStep 445145 = 333859) B333859
theorem B674585 : Blo 295830 674585 := bstep (se 2 (by rfl) ⟨252969, by rfl⟩ : syracuseStep 674585 = 505939) B505939
theorem B445259 : Blo 295830 445259 := bstep (se 1 (by rfl) ⟨333944, by rfl⟩ : syracuseStep 445259 = 667889) B667889
theorem B445271 : Blo 295830 445271 := bstep (se 1 (by rfl) ⟨333953, by rfl⟩ : syracuseStep 445271 = 667907) B667907
theorem B641881 : Blo 295830 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B445337 : Blo 295830 445337 := bstep (se 2 (by rfl) ⟨167001, by rfl⟩ : syracuseStep 445337 = 334003) B334003
theorem B2411441 : Blo 295830 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B445451 : Blo 295830 445451 := bstep (se 1 (by rfl) ⟨334088, by rfl⟩ : syracuseStep 445451 = 668177) B668177
theorem B445463 : Blo 295830 445463 := bstep (se 1 (by rfl) ⟨334097, by rfl⟩ : syracuseStep 445463 = 668195) B668195
theorem B445529 : Blo 295830 445529 := bstep (se 2 (by rfl) ⟨167073, by rfl⟩ : syracuseStep 445529 = 334147) B334147
theorem B1133747 : Blo 295830 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B445643 : Blo 295830 445643 := bstep (se 1 (by rfl) ⟨334232, by rfl⟩ : syracuseStep 445643 = 668465) B668465
theorem B445655 : Blo 295830 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B445721 : Blo 295830 445721 := bstep (se 2 (by rfl) ⟨167145, by rfl⟩ : syracuseStep 445721 = 334291) B334291
theorem B8539505 : Blo 295830 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B445835 : Blo 295830 445835 := bstep (se 1 (by rfl) ⟨334376, by rfl⟩ : syracuseStep 445835 = 668753) B668753
theorem B445847 : Blo 295830 445847 := bstep (se 1 (by rfl) ⟨334385, by rfl⟩ : syracuseStep 445847 = 668771) B668771
theorem B445913 : Blo 295830 445913 := bstep (se 2 (by rfl) ⟨167217, by rfl⟩ : syracuseStep 445913 = 334435) B334435
theorem B2870801 : Blo 295830 2870801 := bstep (se 2 (by rfl) ⟨1076550, by rfl⟩ : syracuseStep 2870801 = 2153101) B2153101
theorem B446027 : Blo 295830 446027 := bstep (se 1 (by rfl) ⟨334520, by rfl⟩ : syracuseStep 446027 = 669041) B669041
theorem B446039 : Blo 295830 446039 := bstep (se 1 (by rfl) ⟨334529, by rfl⟩ : syracuseStep 446039 = 669059) B669059
theorem B1199767 : Blo 295830 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B446105 : Blo 295830 446105 := bstep (se 2 (by rfl) ⟨167289, by rfl⟩ : syracuseStep 446105 = 334579) B334579
theorem B1003211 : Blo 295830 1003211 := bstep (se 1 (by rfl) ⟨752408, by rfl⟩ : syracuseStep 1003211 = 1504817) B1504817
theorem B446219 : Blo 295830 446219 := bstep (se 1 (by rfl) ⟨334664, by rfl⟩ : syracuseStep 446219 = 669329) B669329
theorem B446231 : Blo 295830 446231 := bstep (se 1 (by rfl) ⟨334673, by rfl⟩ : syracuseStep 446231 = 669347) B669347
theorem B1265453 : Blo 295830 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B446297 : Blo 295830 446297 := bstep (se 2 (by rfl) ⟨167361, by rfl⟩ : syracuseStep 446297 = 334723) B334723
theorem B806807 : Blo 295830 806807 := bstep (se 1 (by rfl) ⟨605105, by rfl⟩ : syracuseStep 806807 = 1210211) B1210211
theorem B446411 : Blo 295830 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B446423 : Blo 295830 446423 := bstep (se 1 (by rfl) ⟨334817, by rfl⟩ : syracuseStep 446423 = 669635) B669635
theorem B1003481 : Blo 295830 1003481 := bstep (se 2 (by rfl) ⟨376305, by rfl⟩ : syracuseStep 1003481 = 752611) B752611
theorem B905177 : Blo 295830 905177 := bstep (se 2 (by rfl) ⟨339441, by rfl⟩ : syracuseStep 905177 = 678883) B678883
theorem B2248721 : Blo 295830 2248721 := bstep (se 2 (by rfl) ⟨843270, by rfl⟩ : syracuseStep 2248721 = 1686541) B1686541
theorem B446489 : Blo 295830 446489 := bstep (se 2 (by rfl) ⟨167433, by rfl⟩ : syracuseStep 446489 = 334867) B334867
theorem B446603 : Blo 295830 446603 := bstep (se 1 (by rfl) ⟨334952, by rfl⟩ : syracuseStep 446603 = 669905) B669905
theorem B544907 : Blo 295830 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B446615 : Blo 295830 446615 := bstep (se 1 (by rfl) ⟨334961, by rfl⟩ : syracuseStep 446615 = 669923) B669923
theorem B1527959 : Blo 295830 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B446681 : Blo 295830 446681 := bstep (se 2 (by rfl) ⟨167505, by rfl⟩ : syracuseStep 446681 = 335011) B335011
theorem B446795 : Blo 295830 446795 := bstep (se 1 (by rfl) ⟨335096, by rfl⟩ : syracuseStep 446795 = 670193) B670193
theorem B446807 : Blo 295830 446807 := bstep (se 1 (by rfl) ⟨335105, by rfl⟩ : syracuseStep 446807 = 670211) B670211
theorem B446873 : Blo 295830 446873 := bstep (se 2 (by rfl) ⟨167577, by rfl⟩ : syracuseStep 446873 = 335155) B335155
theorem B1266137 : Blo 295830 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B446987 : Blo 295830 446987 := bstep (se 1 (by rfl) ⟨335240, by rfl⟩ : syracuseStep 446987 = 670481) B670481
theorem B446999 : Blo 295830 446999 := bstep (se 1 (by rfl) ⟨335249, by rfl⟩ : syracuseStep 446999 = 670499) B670499
theorem B807499 : Blo 295830 807499 := bstep (se 1 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 807499 = 1211249) B1211249
theorem B479819 : Blo 295830 479819 := bstep (se 1 (by rfl) ⟨359864, by rfl⟩ : syracuseStep 479819 = 719729) B719729
theorem B447065 : Blo 295830 447065 := bstep (se 2 (by rfl) ⟨167649, by rfl⟩ : syracuseStep 447065 = 335299) B335299
theorem B1135235 : Blo 295830 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B1004183 : Blo 295830 1004183 := bstep (se 1 (by rfl) ⟨753137, by rfl⟩ : syracuseStep 1004183 = 1506275) B1506275
theorem B545473 : Blo 295830 545473 := bstep (se 2 (by rfl) ⟨204552, by rfl⟩ : syracuseStep 545473 = 409105) B409105
theorem B447179 : Blo 295830 447179 := bstep (se 1 (by rfl) ⟨335384, by rfl⟩ : syracuseStep 447179 = 670769) B670769
theorem B447191 : Blo 295830 447191 := bstep (se 1 (by rfl) ⟨335393, by rfl⟩ : syracuseStep 447191 = 670787) B670787
theorem B873181 : Blo 295830 873181 := bstep (se 3 (by rfl) ⟨163721, by rfl⟩ : syracuseStep 873181 = 327443) B327443
theorem B447257 : Blo 295830 447257 := bstep (se 2 (by rfl) ⟨167721, by rfl⟩ : syracuseStep 447257 = 335443) B335443
theorem B447371 : Blo 295830 447371 := bstep (se 1 (by rfl) ⟨335528, by rfl⟩ : syracuseStep 447371 = 671057) B671057
theorem B447383 : Blo 295830 447383 := bstep (se 1 (by rfl) ⟨335537, by rfl⟩ : syracuseStep 447383 = 671075) B671075
theorem B447449 : Blo 295830 447449 := bstep (se 2 (by rfl) ⟨167793, by rfl⟩ : syracuseStep 447449 = 335587) B335587
theorem B447563 : Blo 295830 447563 := bstep (se 1 (by rfl) ⟨335672, by rfl⟩ : syracuseStep 447563 = 671345) B671345
theorem B1135691 : Blo 295830 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B447575 : Blo 295830 447575 := bstep (se 1 (by rfl) ⟨335681, by rfl⟩ : syracuseStep 447575 = 671363) B671363
theorem B447641 : Blo 295830 447641 := bstep (se 2 (by rfl) ⟨167865, by rfl⟩ : syracuseStep 447641 = 335731) B335731
theorem B1004723 : Blo 295830 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B447755 : Blo 295830 447755 := bstep (se 1 (by rfl) ⟨335816, by rfl⟩ : syracuseStep 447755 = 671633) B671633
theorem B1135889 : Blo 295830 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B447767 : Blo 295830 447767 := bstep (se 1 (by rfl) ⟨335825, by rfl⟩ : syracuseStep 447767 = 671651) B671651
theorem B447833 : Blo 295830 447833 := bstep (se 2 (by rfl) ⟨167937, by rfl⟩ : syracuseStep 447833 = 335875) B335875
theorem B1004993 : Blo 295830 1004993 := bstep (se 2 (by rfl) ⟨376872, by rfl⟩ : syracuseStep 1004993 = 753745) B753745
theorem B447947 : Blo 295830 447947 := bstep (se 1 (by rfl) ⟨335960, by rfl⟩ : syracuseStep 447947 = 671921) B671921
theorem B447959 : Blo 295830 447959 := bstep (se 1 (by rfl) ⟨335969, by rfl⟩ : syracuseStep 447959 = 671939) B671939
theorem B316919 : Blo 295830 316919 := bstep (se 1 (by rfl) ⟨237689, by rfl⟩ : syracuseStep 316919 = 475379) B475379
theorem B382487 : Blo 295830 382487 := bstep (se 1 (by rfl) ⟨286865, by rfl⟩ : syracuseStep 382487 = 573731) B573731
theorem B448025 : Blo 295830 448025 := bstep (se 2 (by rfl) ⟨168009, by rfl⟩ : syracuseStep 448025 = 336019) B336019
theorem B1267265 : Blo 295830 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B808537 : Blo 295830 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B448139 : Blo 295830 448139 := bstep (se 1 (by rfl) ⟨336104, by rfl⟩ : syracuseStep 448139 = 672209) B672209
theorem B448151 : Blo 295830 448151 := bstep (se 1 (by rfl) ⟨336113, by rfl⟩ : syracuseStep 448151 = 672227) B672227
theorem B972481 : Blo 295830 972481 := bstep (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) B729361
theorem B448217 : Blo 295830 448217 := bstep (se 2 (by rfl) ⟨168081, by rfl⟩ : syracuseStep 448217 = 336163) B336163
theorem B448331 : Blo 295830 448331 := bstep (se 1 (by rfl) ⟨336248, by rfl⟩ : syracuseStep 448331 = 672497) B672497
theorem B448343 : Blo 295830 448343 := bstep (se 1 (by rfl) ⟨336257, by rfl⟩ : syracuseStep 448343 = 672515) B672515
theorem B448409 : Blo 295830 448409 := bstep (se 2 (by rfl) ⟨168153, by rfl⟩ : syracuseStep 448409 = 336307) B336307
theorem B808883 : Blo 295830 808883 := bstep (se 1 (by rfl) ⟨606662, by rfl⟩ : syracuseStep 808883 = 1213325) B1213325
theorem B677825 : Blo 295830 677825 := bstep (se 2 (by rfl) ⟨254184, by rfl⟩ : syracuseStep 677825 = 508369) B508369
theorem B645067 : Blo 295830 645067 := bstep (se 1 (by rfl) ⟨483800, by rfl⟩ : syracuseStep 645067 = 967601) B967601
theorem B1005533 : Blo 295830 1005533 := bstep (se 3 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 1005533 = 377075) B377075
theorem B448523 : Blo 295830 448523 := bstep (se 1 (by rfl) ⟨336392, by rfl⟩ : syracuseStep 448523 = 672785) B672785
theorem B448535 : Blo 295830 448535 := bstep (se 1 (by rfl) ⟨336401, by rfl⟩ : syracuseStep 448535 = 672803) B672803
theorem B1136663 : Blo 295830 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B448601 : Blo 295830 448601 := bstep (se 2 (by rfl) ⟨168225, by rfl⟩ : syracuseStep 448601 = 336451) B336451
theorem B317611 : Blo 295830 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B448715 : Blo 295830 448715 := bstep (se 1 (by rfl) ⟨336536, by rfl⟩ : syracuseStep 448715 = 673073) B673073
theorem B448727 : Blo 295830 448727 := bstep (se 1 (by rfl) ⟨336545, by rfl⟩ : syracuseStep 448727 = 673091) B673091
theorem B1136861 : Blo 295830 1136861 := bstep (se 3 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 1136861 = 426323) B426323
theorem B448793 : Blo 295830 448793 := bstep (se 2 (by rfl) ⟨168297, by rfl⟩ : syracuseStep 448793 = 336595) B336595
theorem B448907 : Blo 295830 448907 := bstep (se 1 (by rfl) ⟨336680, by rfl⟩ : syracuseStep 448907 = 673361) B673361
theorem B448919 : Blo 295830 448919 := bstep (se 1 (by rfl) ⟨336689, by rfl⟩ : syracuseStep 448919 = 673379) B673379
theorem B448985 : Blo 295830 448985 := bstep (se 2 (by rfl) ⟨168369, by rfl⟩ : syracuseStep 448985 = 336739) B336739
theorem B645655 : Blo 295830 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B449099 : Blo 295830 449099 := bstep (se 1 (by rfl) ⟨336824, by rfl⟩ : syracuseStep 449099 = 673649) B673649
theorem B449111 : Blo 295830 449111 := bstep (se 1 (by rfl) ⟨336833, by rfl⟩ : syracuseStep 449111 = 673667) B673667
theorem B449177 : Blo 295830 449177 := bstep (se 2 (by rfl) ⟨168441, by rfl⟩ : syracuseStep 449177 = 336883) B336883
theorem B449291 : Blo 295830 449291 := bstep (se 1 (by rfl) ⟨336968, by rfl⟩ : syracuseStep 449291 = 673937) B673937
theorem B449303 : Blo 295830 449303 := bstep (se 1 (by rfl) ⟨336977, by rfl⟩ : syracuseStep 449303 = 673955) B673955
theorem B449369 : Blo 295830 449369 := bstep (se 2 (by rfl) ⟨168513, by rfl⟩ : syracuseStep 449369 = 337027) B337027
theorem B449483 : Blo 295830 449483 := bstep (se 1 (by rfl) ⟨337112, by rfl⟩ : syracuseStep 449483 = 674225) B674225
theorem B449495 : Blo 295830 449495 := bstep (se 1 (by rfl) ⟨337121, by rfl⟩ : syracuseStep 449495 = 674243) B674243
theorem B449561 : Blo 295830 449561 := bstep (se 2 (by rfl) ⟨168585, by rfl⟩ : syracuseStep 449561 = 337171) B337171
theorem B1006667 : Blo 295830 1006667 := bstep (se 1 (by rfl) ⟨755000, by rfl⟩ : syracuseStep 1006667 = 1510001) B1510001
theorem B1236061 : Blo 295830 1236061 := bstep (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) B463523
theorem B449675 : Blo 295830 449675 := bstep (se 1 (by rfl) ⟨337256, by rfl⟩ : syracuseStep 449675 = 674513) B674513
theorem B449687 : Blo 295830 449687 := bstep (se 1 (by rfl) ⟨337265, by rfl⟩ : syracuseStep 449687 = 674531) B674531
theorem B1268939 : Blo 295830 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1006937 : Blo 295830 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B1498499 : Blo 295830 1498499 := bstep (se 1 (by rfl) ⟨1123874, by rfl⟩ : syracuseStep 1498499 = 2247749) B2247749
theorem B1695107 : Blo 295830 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B318935 : Blo 295830 318935 := bstep (se 1 (by rfl) ⟨239201, by rfl⟩ : syracuseStep 318935 = 478403) B478403
theorem B1433153 : Blo 295830 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B319063 : Blo 295830 319063 := bstep (se 1 (by rfl) ⟨239297, by rfl⟩ : syracuseStep 319063 = 478595) B478595
theorem B843443 : Blo 295830 843443 := bstep (se 1 (by rfl) ⟨632582, by rfl⟩ : syracuseStep 843443 = 1265165) B1265165
theorem B1433305 : Blo 295830 1433305 := bstep (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) B1074979
theorem B2252609 : Blo 295830 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B1695563 : Blo 295830 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B8576867 : Blo 295830 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B1007639 : Blo 295830 1007639 := bstep (se 1 (by rfl) ⟨755729, by rfl⟩ : syracuseStep 1007639 = 1511459) B1511459
theorem B680051 : Blo 295830 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B319627 : Blo 295830 319627 := bstep (se 1 (by rfl) ⟨239720, by rfl⟩ : syracuseStep 319627 = 479441) B479441
theorem B8151191 : Blo 295830 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B680089 : Blo 295830 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B319883 : Blo 295830 319883 := bstep (se 1 (by rfl) ⟨239912, by rfl⟩ : syracuseStep 319883 = 479825) B479825
theorem B1270237 : Blo 295830 1270237 := bstep (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) B476339
theorem B4317731 : Blo 295830 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1008179 : Blo 295830 1008179 := bstep (se 1 (by rfl) ⟨756134, by rfl⟩ : syracuseStep 1008179 = 1512269) B1512269
theorem B909899 : Blo 295830 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B1270579 : Blo 295830 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1008449 : Blo 295830 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B2581379 : Blo 295830 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B910529 : Blo 295830 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B517387 : Blo 295830 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B1008989 : Blo 295830 1008989 := bstep (se 3 (by rfl) ⟨189185, by rfl⟩ : syracuseStep 1008989 = 378371) B378371
theorem B681601 : Blo 295830 681601 := bstep (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) B511201
theorem B2254553 : Blo 295830 2254553 := bstep (se 2 (by rfl) ⟨845457, by rfl⟩ : syracuseStep 2254553 = 1690915) B1690915
theorem B813235 : Blo 295830 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B1010123 : Blo 295830 1010123 := bstep (se 1 (by rfl) ⟨757592, by rfl⟩ : syracuseStep 1010123 = 1515185) B1515185
theorem B846301 : Blo 295830 846301 := bstep (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) B317363
theorem B846359 : Blo 295830 846359 := bstep (se 1 (by rfl) ⟨634769, by rfl⟩ : syracuseStep 846359 = 1269539) B1269539
theorem B1141427 : Blo 295830 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B1010393 : Blo 295830 1010393 := bstep (se 2 (by rfl) ⟨378897, by rfl⟩ : syracuseStep 1010393 = 757795) B757795
theorem B1502225 : Blo 295830 1502225 := bstep (se 2 (by rfl) ⟨563334, by rfl⟩ : syracuseStep 1502225 = 1126669) B1126669
theorem B1502387 : Blo 295830 1502387 := bstep (se 1 (by rfl) ⟨1126790, by rfl⟩ : syracuseStep 1502387 = 2253581) B2253581
theorem B748865 : Blo 295830 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B1011095 : Blo 295830 1011095 := bstep (se 1 (by rfl) ⟨758321, by rfl⟩ : syracuseStep 1011095 = 1516643) B1516643
theorem B454091 : Blo 295830 454091 := bstep (se 1 (by rfl) ⟨340568, by rfl⟩ : syracuseStep 454091 = 681137) B681137
theorem B421465 : Blo 295830 421465 := bstep (se 2 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 421465 = 316099) B316099
theorem B1601117 : Blo 295830 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B847577 : Blo 295830 847577 := bstep (se 2 (by rfl) ⟨317841, by rfl⟩ : syracuseStep 847577 = 635683) B635683
theorem B847691 : Blo 295830 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B1011635 : Blo 295830 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B454681 : Blo 295830 454681 := bstep (se 2 (by rfl) ⟨170505, by rfl⟩ : syracuseStep 454681 = 341011) B341011
theorem B1011905 : Blo 295830 1011905 := bstep (se 2 (by rfl) ⟨379464, by rfl⟩ : syracuseStep 1011905 = 758929) B758929
theorem B2420941 : Blo 295830 2420941 := bstep (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) B907853
theorem B1274201 : Blo 295830 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1896797 : Blo 295830 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B1700189 : Blo 295830 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B2158979 : Blo 295830 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B750131 : Blo 295830 750131 := bstep (se 1 (by rfl) ⟨562598, by rfl⟩ : syracuseStep 750131 = 1125197) B1125197
theorem B2552471 : Blo 295830 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B422615 : Blo 295830 422615 := bstep (se 1 (by rfl) ⟨316961, by rfl⟩ : syracuseStep 422615 = 633923) B633923
theorem B848819 : Blo 295830 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B422923 : Blo 295830 422923 := bstep (se 1 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 422923 = 634385) B634385
theorem B2257955 : Blo 295830 2257955 := bstep (se 1 (by rfl) ⟨1693466, by rfl⟩ : syracuseStep 2257955 = 3386933) B3386933
theorem B750667 : Blo 295830 750667 := bstep (se 1 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 750667 = 1126001) B1126001
theorem B1504331 : Blo 295830 1504331 := bstep (se 1 (by rfl) ⟨1128248, by rfl⟩ : syracuseStep 1504331 = 2256497) B2256497
theorem B1700939 : Blo 295830 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B750809 : Blo 295830 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B3372353 : Blo 295830 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B849217 : Blo 295830 849217 := bstep (se 2 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 849217 = 636913) B636913
theorem B2880947 : Blo 295830 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1078829 : Blo 295830 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B2881099 : Blo 295830 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B1537667 : Blo 295830 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B1275841 : Blo 295830 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B751639 : Blo 295830 751639 := bstep (se 1 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 751639 = 1127459) B1127459
theorem B423959 : Blo 295830 423959 := bstep (se 1 (by rfl) ⟨317969, by rfl⟩ : syracuseStep 423959 = 635939) B635939
theorem B424153 : Blo 295830 424153 := bstep (se 2 (by rfl) ⟨159057, by rfl⟩ : syracuseStep 424153 = 318115) B318115
theorem B752075 : Blo 295830 752075 := bstep (se 1 (by rfl) ⟨564056, by rfl⟩ : syracuseStep 752075 = 1128113) B1128113
theorem B4651613 : Blo 295830 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B1702579 : Blo 295830 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B1080067 : Blo 295830 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B752449 : Blo 295830 752449 := bstep (se 2 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 752449 = 564337) B564337
theorem B1506113 : Blo 295830 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B1538909 : Blo 295830 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B1375255 : Blo 295830 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B7699637 : Blo 295830 7699637 := bstep (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) B721841
theorem B720065 : Blo 295830 720065 := bstep (se 2 (by rfl) ⟨270024, by rfl⟩ : syracuseStep 720065 = 540049) B540049
theorem B1277329 : Blo 295830 1277329 := bstep (se 2 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 1277329 = 957997) B957997
theorem B753047 : Blo 295830 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B425611 : Blo 295830 425611 := bstep (se 1 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 425611 = 638417) B638417
theorem B950039 : Blo 295830 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B851735 : Blo 295830 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B18087857 : Blo 295830 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B426169 : Blo 295830 426169 := bstep (se 2 (by rfl) ⟨159813, by rfl⟩ : syracuseStep 426169 = 319627) B319627
theorem B1900745 : Blo 295830 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B1114913 : Blo 295830 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B3408803 : Blo 295830 3408803 := bstep (se 1 (by rfl) ⟨2556602, by rfl⟩ : syracuseStep 3408803 = 5113205) B5113205
theorem B295867 : Blo 295830 295867 := bstep (se 1 (by rfl) ⟨221900, by rfl⟩ : syracuseStep 295867 = 443801) B443801
theorem B295943 : Blo 295830 295943 := bstep (se 1 (by rfl) ⟨221957, by rfl⟩ : syracuseStep 295943 = 443915) B443915
theorem B295951 : Blo 295830 295951 := bstep (se 1 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 295951 = 443927) B443927
theorem B1508381 : Blo 295830 1508381 := bstep (se 3 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 1508381 = 565643) B565643
theorem B853021 : Blo 295830 853021 := bstep (se 3 (by rfl) ⟨159941, by rfl⟩ : syracuseStep 853021 = 319883) B319883
theorem B295995 : Blo 295830 295995 := bstep (se 1 (by rfl) ⟨221996, by rfl⟩ : syracuseStep 295995 = 443993) B443993
theorem B3245143 : Blo 295830 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B296071 : Blo 295830 296071 := bstep (se 1 (by rfl) ⟨222053, by rfl⟩ : syracuseStep 296071 = 444107) B444107
theorem B296079 : Blo 295830 296079 := bstep (se 1 (by rfl) ⟨222059, by rfl⟩ : syracuseStep 296079 = 444119) B444119
theorem B296123 : Blo 295830 296123 := bstep (se 1 (by rfl) ⟨222092, by rfl⟩ : syracuseStep 296123 = 444185) B444185
theorem B853193 : Blo 295830 853193 := bstep (se 2 (by rfl) ⟨319947, by rfl⟩ : syracuseStep 853193 = 639895) B639895
theorem B853249 : Blo 295830 853249 := bstep (se 2 (by rfl) ⟨319968, by rfl⟩ : syracuseStep 853249 = 639937) B639937
theorem B296199 : Blo 295830 296199 := bstep (se 1 (by rfl) ⟨222149, by rfl⟩ : syracuseStep 296199 = 444299) B444299
theorem B296207 : Blo 295830 296207 := bstep (se 1 (by rfl) ⟨222155, by rfl⟩ : syracuseStep 296207 = 444311) B444311
theorem B296251 : Blo 295830 296251 := bstep (se 1 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 296251 = 444377) B444377
theorem B2917691 : Blo 295830 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B296327 : Blo 295830 296327 := bstep (se 1 (by rfl) ⟨222245, by rfl⟩ : syracuseStep 296327 = 444491) B444491
theorem B296335 : Blo 295830 296335 := bstep (se 1 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 296335 = 444503) B444503
theorem B296379 : Blo 295830 296379 := bstep (se 1 (by rfl) ⟨222284, by rfl⟩ : syracuseStep 296379 = 444569) B444569
theorem B1508867 : Blo 295830 1508867 := bstep (se 1 (by rfl) ⟨1131650, by rfl⟩ : syracuseStep 1508867 = 2263301) B2263301
theorem B296455 : Blo 295830 296455 := bstep (se 1 (by rfl) ⟨222341, by rfl⟩ : syracuseStep 296455 = 444683) B444683
theorem B296463 : Blo 295830 296463 := bstep (se 1 (by rfl) ⟨222347, by rfl⟩ : syracuseStep 296463 = 444695) B444695
theorem B1705495 : Blo 295830 1705495 := bstep (se 1 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 1705495 = 2558243) B2558243
theorem B296507 : Blo 295830 296507 := bstep (se 1 (by rfl) ⟨222380, by rfl⟩ : syracuseStep 296507 = 444761) B444761
theorem B853591 : Blo 295830 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B755315 : Blo 295830 755315 := bstep (se 1 (by rfl) ⟨566486, by rfl⟩ : syracuseStep 755315 = 1132973) B1132973
theorem B296583 : Blo 295830 296583 := bstep (se 1 (by rfl) ⟨222437, by rfl⟩ : syracuseStep 296583 = 444875) B444875
theorem B296591 : Blo 295830 296591 := bstep (se 1 (by rfl) ⟨222443, by rfl⟩ : syracuseStep 296591 = 444887) B444887
theorem B689849 : Blo 295830 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B296635 : Blo 295830 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B296711 : Blo 295830 296711 := bstep (se 1 (by rfl) ⟨222533, by rfl⟩ : syracuseStep 296711 = 445067) B445067
theorem B296719 : Blo 295830 296719 := bstep (se 1 (by rfl) ⟨222539, by rfl⟩ : syracuseStep 296719 = 445079) B445079
theorem B296763 : Blo 295830 296763 := bstep (se 1 (by rfl) ⟨222572, by rfl⟩ : syracuseStep 296763 = 445145) B445145
theorem B296839 : Blo 295830 296839 := bstep (se 1 (by rfl) ⟨222629, by rfl⟩ : syracuseStep 296839 = 445259) B445259
theorem B296847 : Blo 295830 296847 := bstep (se 1 (by rfl) ⟨222635, by rfl⟩ : syracuseStep 296847 = 445271) B445271
theorem B296891 : Blo 295830 296891 := bstep (se 1 (by rfl) ⟨222668, by rfl⟩ : syracuseStep 296891 = 445337) B445337
theorem B1607627 : Blo 295830 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B296967 : Blo 295830 296967 := bstep (se 1 (by rfl) ⟨222725, by rfl⟩ : syracuseStep 296967 = 445451) B445451
theorem B296975 : Blo 295830 296975 := bstep (se 1 (by rfl) ⟨222731, by rfl⟩ : syracuseStep 296975 = 445463) B445463
theorem B297019 : Blo 295830 297019 := bstep (se 1 (by rfl) ⟨222764, by rfl⟩ : syracuseStep 297019 = 445529) B445529
theorem B755831 : Blo 295830 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B297095 : Blo 295830 297095 := bstep (se 1 (by rfl) ⟨222821, by rfl⟩ : syracuseStep 297095 = 445643) B445643
theorem B297103 : Blo 295830 297103 := bstep (se 1 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 297103 = 445655) B445655
theorem B297147 : Blo 295830 297147 := bstep (se 1 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 297147 = 445721) B445721
theorem B297223 : Blo 295830 297223 := bstep (se 1 (by rfl) ⟨222917, by rfl⟩ : syracuseStep 297223 = 445835) B445835
theorem B297231 : Blo 295830 297231 := bstep (se 1 (by rfl) ⟨222923, by rfl⟩ : syracuseStep 297231 = 445847) B445847
theorem B297275 : Blo 295830 297275 := bstep (se 1 (by rfl) ⟨222956, by rfl⟩ : syracuseStep 297275 = 445913) B445913
theorem B297351 : Blo 295830 297351 := bstep (se 1 (by rfl) ⟨223013, by rfl⟩ : syracuseStep 297351 = 446027) B446027
theorem B297359 : Blo 295830 297359 := bstep (se 1 (by rfl) ⟨223019, by rfl⟩ : syracuseStep 297359 = 446039) B446039
theorem B297403 : Blo 295830 297403 := bstep (se 1 (by rfl) ⟨223052, by rfl⟩ : syracuseStep 297403 = 446105) B446105
theorem B297479 : Blo 295830 297479 := bstep (se 1 (by rfl) ⟨223109, by rfl⟩ : syracuseStep 297479 = 446219) B446219
theorem B297487 : Blo 295830 297487 := bstep (se 1 (by rfl) ⟨223115, by rfl⟩ : syracuseStep 297487 = 446231) B446231
theorem B297531 : Blo 295830 297531 := bstep (se 1 (by rfl) ⟨223148, by rfl⟩ : syracuseStep 297531 = 446297) B446297
theorem B297607 : Blo 295830 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B297615 : Blo 295830 297615 := bstep (se 1 (by rfl) ⟨223211, by rfl⟩ : syracuseStep 297615 = 446423) B446423
theorem B297659 : Blo 295830 297659 := bstep (se 1 (by rfl) ⟨223244, by rfl⟩ : syracuseStep 297659 = 446489) B446489
theorem B6195973 : Blo 295830 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B297735 : Blo 295830 297735 := bstep (se 1 (by rfl) ⟨223301, by rfl⟩ : syracuseStep 297735 = 446603) B446603
theorem B297743 : Blo 295830 297743 := bstep (se 1 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 297743 = 446615) B446615
theorem B1018639 : Blo 295830 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B297787 : Blo 295830 297787 := bstep (se 1 (by rfl) ⟨223340, by rfl⟩ : syracuseStep 297787 = 446681) B446681
theorem B297863 : Blo 295830 297863 := bstep (se 1 (by rfl) ⟨223397, by rfl⟩ : syracuseStep 297863 = 446795) B446795
theorem B297871 : Blo 295830 297871 := bstep (se 1 (by rfl) ⟨223403, by rfl⟩ : syracuseStep 297871 = 446807) B446807
theorem B1084313 : Blo 295830 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B297915 : Blo 295830 297915 := bstep (se 1 (by rfl) ⟨223436, by rfl⟩ : syracuseStep 297915 = 446873) B446873
theorem B297991 : Blo 295830 297991 := bstep (se 1 (by rfl) ⟨223493, by rfl⟩ : syracuseStep 297991 = 446987) B446987
theorem B297999 : Blo 295830 297999 := bstep (se 1 (by rfl) ⟨223499, by rfl⟩ : syracuseStep 297999 = 446999) B446999
theorem B298043 : Blo 295830 298043 := bstep (se 1 (by rfl) ⟨223532, by rfl⟩ : syracuseStep 298043 = 447065) B447065
theorem B1510487 : Blo 295830 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B756823 : Blo 295830 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B298119 : Blo 295830 298119 := bstep (se 1 (by rfl) ⟨223589, by rfl⟩ : syracuseStep 298119 = 447179) B447179
theorem B298127 : Blo 295830 298127 := bstep (se 1 (by rfl) ⟨223595, by rfl⟩ : syracuseStep 298127 = 447191) B447191
theorem B298171 : Blo 295830 298171 := bstep (se 1 (by rfl) ⟨223628, by rfl⟩ : syracuseStep 298171 = 447257) B447257
theorem B462071 : Blo 295830 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B298247 : Blo 295830 298247 := bstep (se 1 (by rfl) ⟨223685, by rfl⟩ : syracuseStep 298247 = 447371) B447371
theorem B298255 : Blo 295830 298255 := bstep (se 1 (by rfl) ⟨223691, by rfl⟩ : syracuseStep 298255 = 447383) B447383
theorem B298299 : Blo 295830 298299 := bstep (se 1 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 298299 = 447449) B447449
theorem B298375 : Blo 295830 298375 := bstep (se 1 (by rfl) ⟨223781, by rfl⟩ : syracuseStep 298375 = 447563) B447563
theorem B757127 : Blo 295830 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B298383 : Blo 295830 298383 := bstep (se 1 (by rfl) ⟨223787, by rfl⟩ : syracuseStep 298383 = 447575) B447575
theorem B298427 : Blo 295830 298427 := bstep (se 1 (by rfl) ⟨223820, by rfl⟩ : syracuseStep 298427 = 447641) B447641
theorem B298503 : Blo 295830 298503 := bstep (se 1 (by rfl) ⟨223877, by rfl⟩ : syracuseStep 298503 = 447755) B447755
theorem B757259 : Blo 295830 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B298511 : Blo 295830 298511 := bstep (se 1 (by rfl) ⟨223883, by rfl⟩ : syracuseStep 298511 = 447767) B447767
theorem B298555 : Blo 295830 298555 := bstep (se 1 (by rfl) ⟨223916, by rfl⟩ : syracuseStep 298555 = 447833) B447833
theorem B1510973 : Blo 295830 1510973 := bstep (se 3 (by rfl) ⟨283307, by rfl⟩ : syracuseStep 1510973 = 566615) B566615
theorem B298631 : Blo 295830 298631 := bstep (se 1 (by rfl) ⟨223973, by rfl⟩ : syracuseStep 298631 = 447947) B447947
theorem B298639 : Blo 295830 298639 := bstep (se 1 (by rfl) ⟨223979, by rfl⟩ : syracuseStep 298639 = 447959) B447959
theorem B298683 : Blo 295830 298683 := bstep (se 1 (by rfl) ⟨224012, by rfl⟩ : syracuseStep 298683 = 448025) B448025
theorem B1281737 : Blo 295830 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B298759 : Blo 295830 298759 := bstep (se 1 (by rfl) ⟨224069, by rfl⟩ : syracuseStep 298759 = 448139) B448139
theorem B298767 : Blo 295830 298767 := bstep (se 1 (by rfl) ⟨224075, by rfl⟩ : syracuseStep 298767 = 448151) B448151
theorem B855841 : Blo 295830 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B298811 : Blo 295830 298811 := bstep (se 1 (by rfl) ⟨224108, by rfl⟩ : syracuseStep 298811 = 448217) B448217
theorem B298887 : Blo 295830 298887 := bstep (se 1 (by rfl) ⟨224165, by rfl⟩ : syracuseStep 298887 = 448331) B448331
theorem B298895 : Blo 295830 298895 := bstep (se 1 (by rfl) ⟨224171, by rfl⟩ : syracuseStep 298895 = 448343) B448343
theorem B298939 : Blo 295830 298939 := bstep (se 1 (by rfl) ⟨224204, by rfl⟩ : syracuseStep 298939 = 448409) B448409
theorem B299015 : Blo 295830 299015 := bstep (se 1 (by rfl) ⟨224261, by rfl⟩ : syracuseStep 299015 = 448523) B448523
theorem B299023 : Blo 295830 299023 := bstep (se 1 (by rfl) ⟨224267, by rfl⟩ : syracuseStep 299023 = 448535) B448535
theorem B757775 : Blo 295830 757775 := bstep (se 1 (by rfl) ⟨568331, by rfl⟩ : syracuseStep 757775 = 1136663) B1136663
theorem B299067 : Blo 295830 299067 := bstep (se 1 (by rfl) ⟨224300, by rfl⟩ : syracuseStep 299067 = 448601) B448601
theorem B6951005 : Blo 295830 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B299143 : Blo 295830 299143 := bstep (se 1 (by rfl) ⟨224357, by rfl⟩ : syracuseStep 299143 = 448715) B448715
theorem B299151 : Blo 295830 299151 := bstep (se 1 (by rfl) ⟨224363, by rfl⟩ : syracuseStep 299151 = 448727) B448727
theorem B757907 : Blo 295830 757907 := bstep (se 1 (by rfl) ⟨568430, by rfl⟩ : syracuseStep 757907 = 1136861) B1136861
theorem B299195 : Blo 295830 299195 := bstep (se 1 (by rfl) ⟨224396, by rfl⟩ : syracuseStep 299195 = 448793) B448793
theorem B299271 : Blo 295830 299271 := bstep (se 1 (by rfl) ⟨224453, by rfl⟩ : syracuseStep 299271 = 448907) B448907
theorem B299279 : Blo 295830 299279 := bstep (se 1 (by rfl) ⟨224459, by rfl⟩ : syracuseStep 299279 = 448919) B448919
theorem B299323 : Blo 295830 299323 := bstep (se 1 (by rfl) ⟨224492, by rfl⟩ : syracuseStep 299323 = 448985) B448985
theorem B299399 : Blo 295830 299399 := bstep (se 1 (by rfl) ⟨224549, by rfl⟩ : syracuseStep 299399 = 449099) B449099
theorem B299407 : Blo 295830 299407 := bstep (se 1 (by rfl) ⟨224555, by rfl⟩ : syracuseStep 299407 = 449111) B449111
theorem B299451 : Blo 295830 299451 := bstep (se 1 (by rfl) ⟨224588, by rfl⟩ : syracuseStep 299451 = 449177) B449177
theorem B299527 : Blo 295830 299527 := bstep (se 1 (by rfl) ⟨224645, by rfl⟩ : syracuseStep 299527 = 449291) B449291
theorem B299535 : Blo 295830 299535 := bstep (se 1 (by rfl) ⟨224651, by rfl⟩ : syracuseStep 299535 = 449303) B449303
theorem B299579 : Blo 295830 299579 := bstep (se 1 (by rfl) ⟨224684, by rfl⟩ : syracuseStep 299579 = 449369) B449369
theorem B299655 : Blo 295830 299655 := bstep (se 1 (by rfl) ⟨224741, by rfl⟩ : syracuseStep 299655 = 449483) B449483
theorem B299663 : Blo 295830 299663 := bstep (se 1 (by rfl) ⟨224747, by rfl⟩ : syracuseStep 299663 = 449495) B449495
theorem B299707 : Blo 295830 299707 := bstep (se 1 (by rfl) ⟨224780, by rfl⟩ : syracuseStep 299707 = 449561) B449561
theorem B299783 : Blo 295830 299783 := bstep (se 1 (by rfl) ⟨224837, by rfl⟩ : syracuseStep 299783 = 449675) B449675
theorem B299791 : Blo 295830 299791 := bstep (se 1 (by rfl) ⟨224843, by rfl⟩ : syracuseStep 299791 = 449687) B449687
theorem B561953 : Blo 295830 561953 := bstep (se 2 (by rfl) ⟨210732, by rfl⟩ : syracuseStep 561953 = 421465) B421465
theorem B332815 : Blo 295830 332815 := bstep (se 1 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 332815 = 499223) B499223
theorem B955435 : Blo 295830 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B562295 : Blo 295830 562295 := bstep (se 1 (by rfl) ⟨421721, by rfl⟩ : syracuseStep 562295 = 843443) B843443
theorem B1512755 : Blo 295830 1512755 := bstep (se 1 (by rfl) ⟨1134566, by rfl⟩ : syracuseStep 1512755 = 2269133) B2269133
theorem B333319 : Blo 295830 333319 := bstep (se 1 (by rfl) ⟨249989, by rfl⟩ : syracuseStep 333319 = 499979) B499979
theorem B1513079 : Blo 295830 1513079 := bstep (se 1 (by rfl) ⟨1134809, by rfl⟩ : syracuseStep 1513079 = 2269619) B2269619
theorem B333499 : Blo 295830 333499 := bstep (se 1 (by rfl) ⟨250124, by rfl⟩ : syracuseStep 333499 = 500249) B500249
theorem B858127 : Blo 295830 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B333967 : Blo 295830 333967 := bstep (se 1 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 333967 = 500951) B500951
theorem B8591629 : Blo 295830 8591629 := bstep (se 3 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 8591629 = 3221861) B3221861
theorem B1514051 : Blo 295830 1514051 := bstep (se 1 (by rfl) ⟨1135538, by rfl⟩ : syracuseStep 1514051 = 2271077) B2271077
theorem B334471 : Blo 295830 334471 := bstep (se 1 (by rfl) ⟨250853, by rfl⟩ : syracuseStep 334471 = 501707) B501707
theorem B563897 : Blo 295830 563897 := bstep (se 2 (by rfl) ⟨211461, by rfl⟩ : syracuseStep 563897 = 422923) B422923
theorem B334651 : Blo 295830 334651 := bstep (se 1 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 334651 = 501977) B501977
theorem B1514375 : Blo 295830 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B564239 : Blo 295830 564239 := bstep (se 1 (by rfl) ⟨423179, by rfl⟩ : syracuseStep 564239 = 846359) B846359
theorem B760951 : Blo 295830 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B335119 : Blo 295830 335119 := bstep (se 1 (by rfl) ⟨251339, by rfl⟩ : syracuseStep 335119 = 502679) B502679
theorem B400783 : Blo 295830 400783 := bstep (se 1 (by rfl) ⟨300587, by rfl⟩ : syracuseStep 400783 = 601175) B601175
theorem B3841465 : Blo 295830 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B499243 : Blo 295830 499243 := bstep (se 1 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 499243 = 748865) B748865
theorem B499385 : Blo 295830 499385 := bstep (se 2 (by rfl) ⟨187269, by rfl⟩ : syracuseStep 499385 = 374539) B374539
theorem B335623 : Blo 295830 335623 := bstep (se 1 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 335623 = 503435) B503435
theorem B565051 : Blo 295830 565051 := bstep (se 1 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 565051 = 847577) B847577
theorem B565127 : Blo 295830 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B335803 : Blo 295830 335803 := bstep (se 1 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 335803 = 503705) B503705
theorem B5775533 : Blo 295830 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B565537 : Blo 295830 565537 := bstep (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) B424153
theorem B500087 : Blo 295830 500087 := bstep (se 1 (by rfl) ⟨375065, by rfl⟩ : syracuseStep 500087 = 750131) B750131
theorem B336271 : Blo 295830 336271 := bstep (se 1 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 336271 = 504407) B504407
theorem B565879 : Blo 295830 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B860873 : Blo 295830 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B500539 : Blo 295830 500539 := bstep (se 1 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 500539 = 750809) B750809
theorem B336775 : Blo 295830 336775 := bstep (se 1 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 336775 = 505163) B505163
theorem B2270105 : Blo 295830 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B500681 : Blo 295830 500681 := bstep (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) B375511
theorem B336955 : Blo 295830 336955 := bstep (se 1 (by rfl) ⟨252716, by rfl⟩ : syracuseStep 336955 = 505433) B505433
theorem B1025111 : Blo 295830 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B632009 : Blo 295830 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B533879 : Blo 295830 533879 := bstep (se 1 (by rfl) ⟨400409, by rfl⟩ : syracuseStep 533879 = 800819) B800819
theorem B1648081 : Blo 295830 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B501383 : Blo 295830 501383 := bstep (se 1 (by rfl) ⟨376037, by rfl⟩ : syracuseStep 501383 = 752075) B752075
theorem B3221171 : Blo 295830 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B4990643 : Blo 295830 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B3811121 : Blo 295830 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B1025939 : Blo 295830 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B2861189 : Blo 295830 2861189 := bstep (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) B536473
theorem B665747 : Blo 295830 665747 := bstep (se 1 (by rfl) ⟨499310, by rfl⟩ : syracuseStep 665747 = 998621) B998621
theorem B567481 : Blo 295830 567481 := bstep (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) B425611
theorem B665801 : Blo 295830 665801 := bstep (se 2 (by rfl) ⟨249675, by rfl⟩ : syracuseStep 665801 = 499351) B499351
theorem B502031 : Blo 295830 502031 := bstep (se 1 (by rfl) ⟨376523, by rfl⟩ : syracuseStep 502031 = 753047) B753047
theorem B1911073 : Blo 295830 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B633359 : Blo 295830 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B567823 : Blo 295830 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B1321559 : Blo 295830 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B502571 : Blo 295830 502571 := bstep (se 1 (by rfl) ⟨376928, by rfl⟩ : syracuseStep 502571 = 753857) B753857
theorem B2272049 : Blo 295830 2272049 := bstep (se 2 (by rfl) ⟨852018, by rfl⟩ : syracuseStep 2272049 = 1704037) B1704037
theorem B666503 : Blo 295830 666503 := bstep (se 1 (by rfl) ⟨499877, by rfl⟩ : syracuseStep 666503 = 999755) B999755
theorem B1616861 : Blo 295830 1616861 := bstep (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) B606323
theorem B1453085 : Blo 295830 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B666683 : Blo 295830 666683 := bstep (se 1 (by rfl) ⟨500012, by rfl⟩ : syracuseStep 666683 = 1000025) B1000025
theorem B666809 : Blo 295830 666809 := bstep (se 2 (by rfl) ⟨250053, by rfl⟩ : syracuseStep 666809 = 500107) B500107
theorem B502969 : Blo 295830 502969 := bstep (se 2 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 502969 = 377227) B377227
theorem B568711 : Blo 295830 568711 := bstep (se 1 (by rfl) ⟨426533, by rfl⟩ : syracuseStep 568711 = 853067) B853067
theorem B667151 : Blo 295830 667151 := bstep (se 1 (by rfl) ⟨500363, by rfl⟩ : syracuseStep 667151 = 1000727) B1000727
theorem B667169 : Blo 295830 667169 := bstep (se 2 (by rfl) ⟨250188, by rfl⟩ : syracuseStep 667169 = 500377) B500377
theorem B339643 : Blo 295830 339643 := bstep (se 1 (by rfl) ⟨254732, by rfl⟩ : syracuseStep 339643 = 509465) B509465
theorem B667511 : Blo 295830 667511 := bstep (se 1 (by rfl) ⟨500633, by rfl⟩ : syracuseStep 667511 = 1001267) B1001267
theorem B503671 : Blo 295830 503671 := bstep (se 1 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 503671 = 755507) B755507
theorem B569359 : Blo 295830 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B667691 : Blo 295830 667691 := bstep (se 1 (by rfl) ⟨500768, by rfl⟩ : syracuseStep 667691 = 1001537) B1001537
theorem B503867 : Blo 295830 503867 := bstep (se 1 (by rfl) ⟨377900, by rfl⟩ : syracuseStep 503867 = 755801) B755801
theorem B1126487 : Blo 295830 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B1519931 : Blo 295830 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B668051 : Blo 295830 668051 := bstep (se 1 (by rfl) ⟨501038, by rfl⟩ : syracuseStep 668051 = 1002077) B1002077
theorem B668105 : Blo 295830 668105 := bstep (se 2 (by rfl) ⟨250539, by rfl⟩ : syracuseStep 668105 = 501079) B501079
theorem B504265 : Blo 295830 504265 := bstep (se 2 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 504265 = 378199) B378199
theorem B1126973 : Blo 295830 1126973 := bstep (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) B422615
theorem B1913867 : Blo 295830 1913867 := bstep (se 1 (by rfl) ⟨1435400, by rfl⟩ : syracuseStep 1913867 = 2870801) B2870801
theorem B668807 : Blo 295830 668807 := bstep (se 1 (by rfl) ⟨501605, by rfl⟩ : syracuseStep 668807 = 1003211) B1003211
theorem B504967 : Blo 295830 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B668987 : Blo 295830 668987 := bstep (se 1 (by rfl) ⟨501740, by rfl⟩ : syracuseStep 668987 = 1003481) B1003481
theorem B603451 : Blo 295830 603451 := bstep (se 1 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 603451 = 905177) B905177
theorem B669113 : Blo 295830 669113 := bstep (se 2 (by rfl) ⟨250917, by rfl⟩ : syracuseStep 669113 = 501835) B501835
theorem B669455 : Blo 295830 669455 := bstep (se 1 (by rfl) ⟨502091, by rfl⟩ : syracuseStep 669455 = 1004183) B1004183
theorem B505615 : Blo 295830 505615 := bstep (se 1 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 505615 = 758423) B758423
theorem B669473 : Blo 295830 669473 := bstep (se 2 (by rfl) ⟨251052, by rfl⟩ : syracuseStep 669473 = 502105) B502105
theorem B1128401 : Blo 295830 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B669815 : Blo 295830 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B669995 : Blo 295830 669995 := bstep (se 1 (by rfl) ⟨502496, by rfl⟩ : syracuseStep 669995 = 1004993) B1004993
theorem B2538013 : Blo 295830 2538013 := bstep (se 3 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 2538013 = 951755) B951755
theorem B539255 : Blo 295830 539255 := bstep (se 1 (by rfl) ⟨404441, by rfl⟩ : syracuseStep 539255 = 808883) B808883
theorem B670355 : Blo 295830 670355 := bstep (se 1 (by rfl) ⟨502766, by rfl⟩ : syracuseStep 670355 = 1005533) B1005533
theorem B670409 : Blo 295830 670409 := bstep (se 2 (by rfl) ⟨251403, by rfl⟩ : syracuseStep 670409 = 502807) B502807
theorem B1620773 : Blo 295830 1620773 := bstep (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) B303895
theorem B1424557 : Blo 295830 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B671111 : Blo 295830 671111 := bstep (se 1 (by rfl) ⟨503333, by rfl⟩ : syracuseStep 671111 = 1006667) B1006667
theorem B671291 : Blo 295830 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B998999 : Blo 295830 998999 := bstep (se 1 (by rfl) ⟨749249, by rfl⟩ : syracuseStep 998999 = 1498499) B1498499
theorem B1130071 : Blo 295830 1130071 := bstep (se 1 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 1130071 = 1695107) B1695107
theorem B671417 : Blo 295830 671417 := bstep (se 2 (by rfl) ⟨251781, by rfl⟩ : syracuseStep 671417 = 503563) B503563
theorem B3391307 : Blo 295830 3391307 := bstep (se 1 (by rfl) ⟨2543480, by rfl⟩ : syracuseStep 3391307 = 5086961) B5086961
theorem B1130375 : Blo 295830 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B5717911 : Blo 295830 5717911 := bstep (se 1 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 5717911 = 8576867) B8576867
theorem B1687499 : Blo 295830 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B671759 : Blo 295830 671759 := bstep (se 1 (by rfl) ⟨503819, by rfl⟩ : syracuseStep 671759 = 1007639) B1007639
theorem B671777 : Blo 295830 671777 := bstep (se 2 (by rfl) ⟨251916, by rfl⟩ : syracuseStep 671777 = 503833) B503833
theorem B606241 : Blo 295830 606241 := bstep (se 2 (by rfl) ⟨227340, by rfl⟩ : syracuseStep 606241 = 454681) B454681
theorem B999485 : Blo 295830 999485 := bstep (se 3 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 999485 = 374807) B374807
theorem B1130557 : Blo 295830 1130557 := bstep (se 3 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 1130557 = 423959) B423959
theorem B4079861 : Blo 295830 4079861 := bstep (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) B382487
theorem B3227921 : Blo 295830 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B377131 : Blo 295830 377131 := bstep (se 1 (by rfl) ⟨282848, by rfl⟩ : syracuseStep 377131 = 565697) B565697
theorem B672119 : Blo 295830 672119 := bstep (se 1 (by rfl) ⟨504089, by rfl⟩ : syracuseStep 672119 = 1008179) B1008179
theorem B606599 : Blo 295830 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B2539997 : Blo 295830 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B672299 : Blo 295830 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B1720919 : Blo 295830 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B607019 : Blo 295830 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B672659 : Blo 295830 672659 := bstep (se 1 (by rfl) ⟨504494, by rfl⟩ : syracuseStep 672659 = 1008989) B1008989
theorem B672713 : Blo 295830 672713 := bstep (se 2 (by rfl) ⟨252267, by rfl⟩ : syracuseStep 672713 = 504535) B504535
theorem B1164241 : Blo 295830 1164241 := bstep (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) B873181
theorem B378103 : Blo 295830 378103 := bstep (se 1 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 378103 = 567155) B567155
theorem B443783 : Blo 295830 443783 := bstep (se 1 (by rfl) ⟨332837, by rfl⟩ : syracuseStep 443783 = 665675) B665675
theorem B443819 : Blo 295830 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B1000889 : Blo 295830 1000889 := bstep (se 2 (by rfl) ⟨375333, by rfl⟩ : syracuseStep 1000889 = 750667) B750667
theorem B443849 : Blo 295830 443849 := bstep (se 2 (by rfl) ⟨166443, by rfl⟩ : syracuseStep 443849 = 332887) B332887
theorem B1033771 : Blo 295830 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B443963 : Blo 295830 443963 := bstep (se 1 (by rfl) ⟨332972, by rfl⟩ : syracuseStep 443963 = 665945) B665945
theorem B378427 : Blo 295830 378427 := bstep (se 1 (by rfl) ⟨283820, by rfl⟩ : syracuseStep 378427 = 567641) B567641
theorem B902771 : Blo 295830 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B444023 : Blo 295830 444023 := bstep (se 1 (by rfl) ⟨333017, by rfl⟩ : syracuseStep 444023 = 666035) B666035
theorem B673415 : Blo 295830 673415 := bstep (se 1 (by rfl) ⟨505061, by rfl⟩ : syracuseStep 673415 = 1010123) B1010123
theorem B444047 : Blo 295830 444047 := bstep (se 1 (by rfl) ⟨333035, by rfl⟩ : syracuseStep 444047 = 666071) B666071
theorem B804505 : Blo 295830 804505 := bstep (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) B603379
theorem B444089 : Blo 295830 444089 := bstep (se 2 (by rfl) ⟨166533, by rfl⟩ : syracuseStep 444089 = 333067) B333067
theorem B1132289 : Blo 295830 1132289 := bstep (se 2 (by rfl) ⟨424608, by rfl⟩ : syracuseStep 1132289 = 849217) B849217
theorem B444167 : Blo 295830 444167 := bstep (se 1 (by rfl) ⟨333125, by rfl⟩ : syracuseStep 444167 = 666251) B666251
theorem B444203 : Blo 295830 444203 := bstep (se 1 (by rfl) ⟨333152, by rfl⟩ : syracuseStep 444203 = 666305) B666305
theorem B6080305 : Blo 295830 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B673595 : Blo 295830 673595 := bstep (se 1 (by rfl) ⟨505196, by rfl⟩ : syracuseStep 673595 = 1010393) B1010393
theorem B444233 : Blo 295830 444233 := bstep (se 2 (by rfl) ⟨166587, by rfl⟩ : syracuseStep 444233 = 333175) B333175
theorem B673721 : Blo 295830 673721 := bstep (se 2 (by rfl) ⟨252645, by rfl⟩ : syracuseStep 673721 = 505291) B505291
theorem B444347 : Blo 295830 444347 := bstep (se 1 (by rfl) ⟨333260, by rfl⟩ : syracuseStep 444347 = 666521) B666521
theorem B444407 : Blo 295830 444407 := bstep (se 1 (by rfl) ⟨333305, by rfl⟩ : syracuseStep 444407 = 666611) B666611
theorem B1001483 : Blo 295830 1001483 := bstep (se 1 (by rfl) ⟨751112, by rfl⟩ : syracuseStep 1001483 = 1502225) B1502225
theorem B444431 : Blo 295830 444431 := bstep (se 1 (by rfl) ⟨333323, by rfl⟩ : syracuseStep 444431 = 666647) B666647
theorem B444473 : Blo 295830 444473 := bstep (se 2 (by rfl) ⟨166677, by rfl⟩ : syracuseStep 444473 = 333355) B333355
theorem B1001591 : Blo 295830 1001591 := bstep (se 1 (by rfl) ⟨751193, by rfl⟩ : syracuseStep 1001591 = 1502387) B1502387
theorem B444551 : Blo 295830 444551 := bstep (se 1 (by rfl) ⟨333413, by rfl⟩ : syracuseStep 444551 = 666827) B666827
theorem B444587 : Blo 295830 444587 := bstep (se 1 (by rfl) ⟨333440, by rfl⟩ : syracuseStep 444587 = 666881) B666881
theorem B444617 : Blo 295830 444617 := bstep (se 2 (by rfl) ⟨166731, by rfl⟩ : syracuseStep 444617 = 333463) B333463
theorem B1296641 : Blo 295830 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B674063 : Blo 295830 674063 := bstep (se 1 (by rfl) ⟨505547, by rfl⟩ : syracuseStep 674063 = 1011095) B1011095
theorem B674081 : Blo 295830 674081 := bstep (se 2 (by rfl) ⟨252780, by rfl⟩ : syracuseStep 674081 = 505561) B505561
theorem B444731 : Blo 295830 444731 := bstep (se 1 (by rfl) ⟨333548, by rfl⟩ : syracuseStep 444731 = 667097) B667097
theorem B1427827 : Blo 295830 1427827 := bstep (se 1 (by rfl) ⟨1070870, by rfl⟩ : syracuseStep 1427827 = 2141741) B2141741
theorem B444791 : Blo 295830 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B444815 : Blo 295830 444815 := bstep (se 1 (by rfl) ⟨333611, by rfl⟩ : syracuseStep 444815 = 667223) B667223
theorem B1067411 : Blo 295830 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B444857 : Blo 295830 444857 := bstep (se 2 (by rfl) ⟨166821, by rfl⟩ : syracuseStep 444857 = 333643) B333643
theorem B444935 : Blo 295830 444935 := bstep (se 1 (by rfl) ⟨333701, by rfl⟩ : syracuseStep 444935 = 667403) B667403
theorem B379399 : Blo 295830 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B444971 : Blo 295830 444971 := bstep (se 1 (by rfl) ⟨333728, by rfl⟩ : syracuseStep 444971 = 667457) B667457
theorem B445001 : Blo 295830 445001 := bstep (se 2 (by rfl) ⟨166875, by rfl⟩ : syracuseStep 445001 = 333751) B333751
theorem B9226871 : Blo 295830 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B674423 : Blo 295830 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B445115 : Blo 295830 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B1002185 : Blo 295830 1002185 := bstep (se 2 (by rfl) ⟨375819, by rfl⟩ : syracuseStep 1002185 = 751639) B751639
theorem B445175 : Blo 295830 445175 := bstep (se 1 (by rfl) ⟨333881, by rfl⟩ : syracuseStep 445175 = 667763) B667763
theorem B445199 : Blo 295830 445199 := bstep (se 1 (by rfl) ⟨333899, by rfl⟩ : syracuseStep 445199 = 667799) B667799
theorem B674603 : Blo 295830 674603 := bstep (se 1 (by rfl) ⟨505952, by rfl⟩ : syracuseStep 674603 = 1011905) B1011905
theorem B2542387 : Blo 295830 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B445241 : Blo 295830 445241 := bstep (se 2 (by rfl) ⟨166965, by rfl⟩ : syracuseStep 445241 = 333931) B333931
theorem B510779 : Blo 295830 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B445319 : Blo 295830 445319 := bstep (se 1 (by rfl) ⟨333989, by rfl⟩ : syracuseStep 445319 = 667979) B667979
theorem B1264531 : Blo 295830 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B1133459 : Blo 295830 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B445355 : Blo 295830 445355 := bstep (se 1 (by rfl) ⟨334016, by rfl⟩ : syracuseStep 445355 = 668033) B668033
theorem B445385 : Blo 295830 445385 := bstep (se 2 (by rfl) ⟨167019, by rfl⟩ : syracuseStep 445385 = 334039) B334039
theorem B805889 : Blo 295830 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B445499 : Blo 295830 445499 := bstep (se 1 (by rfl) ⟨334124, by rfl⟩ : syracuseStep 445499 = 668249) B668249
theorem B445559 : Blo 295830 445559 := bstep (se 1 (by rfl) ⟨334169, by rfl⟩ : syracuseStep 445559 = 668339) B668339
theorem B445583 : Blo 295830 445583 := bstep (se 1 (by rfl) ⟨334187, by rfl⟩ : syracuseStep 445583 = 668375) B668375
theorem B445625 : Blo 295830 445625 := bstep (se 2 (by rfl) ⟨167109, by rfl⟩ : syracuseStep 445625 = 334219) B334219
theorem B445703 : Blo 295830 445703 := bstep (se 1 (by rfl) ⟨334277, by rfl⟩ : syracuseStep 445703 = 668555) B668555
theorem B445739 : Blo 295830 445739 := bstep (se 1 (by rfl) ⟨334304, by rfl⟩ : syracuseStep 445739 = 668609) B668609
theorem B445769 : Blo 295830 445769 := bstep (se 2 (by rfl) ⟨167163, by rfl⟩ : syracuseStep 445769 = 334327) B334327
theorem B1002887 : Blo 295830 1002887 := bstep (se 1 (by rfl) ⟨752165, by rfl⟩ : syracuseStep 1002887 = 1504331) B1504331
theorem B1133959 : Blo 295830 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B445883 : Blo 295830 445883 := bstep (se 1 (by rfl) ⟨334412, by rfl⟩ : syracuseStep 445883 = 668825) B668825
theorem B445943 : Blo 295830 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B445967 : Blo 295830 445967 := bstep (se 1 (by rfl) ⟨334475, by rfl⟩ : syracuseStep 445967 = 668951) B668951
theorem B2248235 : Blo 295830 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B446009 : Blo 295830 446009 := bstep (se 2 (by rfl) ⟨167253, by rfl⟩ : syracuseStep 446009 = 334507) B334507
theorem B1920631 : Blo 295830 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B446087 : Blo 295830 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B446123 : Blo 295830 446123 := bstep (se 1 (by rfl) ⟨334592, by rfl⟩ : syracuseStep 446123 = 669185) B669185
theorem B446153 : Blo 295830 446153 := bstep (se 2 (by rfl) ⟨167307, by rfl⟩ : syracuseStep 446153 = 334615) B334615
theorem B1003265 : Blo 295830 1003265 := bstep (se 2 (by rfl) ⟨376224, by rfl⟩ : syracuseStep 1003265 = 752449) B752449
theorem B446267 : Blo 295830 446267 := bstep (se 1 (by rfl) ⟨334700, by rfl⟩ : syracuseStep 446267 = 669401) B669401
theorem B446327 : Blo 295830 446327 := bstep (se 1 (by rfl) ⟨334745, by rfl⟩ : syracuseStep 446327 = 669491) B669491
theorem B446351 : Blo 295830 446351 := bstep (se 1 (by rfl) ⟨334763, by rfl⟩ : syracuseStep 446351 = 669527) B669527
theorem B1200025 : Blo 295830 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B446393 : Blo 295830 446393 := bstep (se 2 (by rfl) ⟨167397, by rfl⟩ : syracuseStep 446393 = 334795) B334795
theorem B446471 : Blo 295830 446471 := bstep (se 1 (by rfl) ⟨334853, by rfl⟩ : syracuseStep 446471 = 669707) B669707
theorem B446507 : Blo 295830 446507 := bstep (se 1 (by rfl) ⟨334880, by rfl⟩ : syracuseStep 446507 = 669761) B669761
theorem B446537 : Blo 295830 446537 := bstep (se 2 (by rfl) ⟨167451, by rfl⟩ : syracuseStep 446537 = 334903) B334903
theorem B446651 : Blo 295830 446651 := bstep (se 1 (by rfl) ⟨334988, by rfl⟩ : syracuseStep 446651 = 669977) B669977
theorem B446711 : Blo 295830 446711 := bstep (se 1 (by rfl) ⟨335033, by rfl⟩ : syracuseStep 446711 = 670067) B670067
theorem B446735 : Blo 295830 446735 := bstep (se 1 (by rfl) ⟨335051, by rfl⟩ : syracuseStep 446735 = 670103) B670103
theorem B446777 : Blo 295830 446777 := bstep (se 2 (by rfl) ⟨167541, by rfl⟩ : syracuseStep 446777 = 335083) B335083
theorem B446855 : Blo 295830 446855 := bstep (se 1 (by rfl) ⟨335141, by rfl⟩ : syracuseStep 446855 = 670283) B670283
theorem B3101075 : Blo 295830 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B446891 : Blo 295830 446891 := bstep (se 1 (by rfl) ⟨335168, by rfl⟩ : syracuseStep 446891 = 670337) B670337
theorem B446921 : Blo 295830 446921 := bstep (se 2 (by rfl) ⟨167595, by rfl⟩ : syracuseStep 446921 = 335191) B335191
theorem B315919 : Blo 295830 315919 := bstep (se 1 (by rfl) ⟨236939, by rfl⟩ : syracuseStep 315919 = 473879) B473879
theorem B1266205 : Blo 295830 1266205 := bstep (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) B474827
theorem B12833315 : Blo 295830 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B1004075 : Blo 295830 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B447035 : Blo 295830 447035 := bstep (se 1 (by rfl) ⟨335276, by rfl⟩ : syracuseStep 447035 = 670553) B670553
theorem B447095 : Blo 295830 447095 := bstep (se 1 (by rfl) ⟨335321, by rfl⟩ : syracuseStep 447095 = 670643) B670643
theorem B447119 : Blo 295830 447119 := bstep (se 1 (by rfl) ⟨335339, by rfl⟩ : syracuseStep 447119 = 670679) B670679
theorem B447161 : Blo 295830 447161 := bstep (se 2 (by rfl) ⟨167685, by rfl⟩ : syracuseStep 447161 = 335371) B335371
theorem B447239 : Blo 295830 447239 := bstep (se 1 (by rfl) ⟨335429, by rfl⟩ : syracuseStep 447239 = 670859) B670859
theorem B5133091 : Blo 295830 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B447275 : Blo 295830 447275 := bstep (se 1 (by rfl) ⟨335456, by rfl⟩ : syracuseStep 447275 = 670913) B670913
theorem B480043 : Blo 295830 480043 := bstep (se 1 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 480043 = 720065) B720065
theorem B447305 : Blo 295830 447305 := bstep (se 2 (by rfl) ⟨167739, by rfl⟩ : syracuseStep 447305 = 335479) B335479
theorem B3068761 : Blo 295830 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B1364921 : Blo 295830 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B447419 : Blo 295830 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B447479 : Blo 295830 447479 := bstep (se 1 (by rfl) ⟨335609, by rfl⟩ : syracuseStep 447479 = 671219) B671219
theorem B447503 : Blo 295830 447503 := bstep (se 1 (by rfl) ⟨335627, by rfl⟩ : syracuseStep 447503 = 671255) B671255
theorem B447545 : Blo 295830 447545 := bstep (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) B335659
theorem B2151485 : Blo 295830 2151485 := bstep (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) B806807
theorem B447623 : Blo 295830 447623 := bstep (se 1 (by rfl) ⟨335717, by rfl⟩ : syracuseStep 447623 = 671435) B671435
theorem B447659 : Blo 295830 447659 := bstep (se 1 (by rfl) ⟨335744, by rfl⟩ : syracuseStep 447659 = 671489) B671489
theorem B447689 : Blo 295830 447689 := bstep (se 2 (by rfl) ⟨167883, by rfl⟩ : syracuseStep 447689 = 335767) B335767
theorem B447803 : Blo 295830 447803 := bstep (se 1 (by rfl) ⟨335852, by rfl⟩ : syracuseStep 447803 = 671705) B671705
theorem B447863 : Blo 295830 447863 := bstep (se 1 (by rfl) ⟨335897, by rfl⟩ : syracuseStep 447863 = 671795) B671795
theorem B447887 : Blo 295830 447887 := bstep (se 1 (by rfl) ⟨335915, by rfl⟩ : syracuseStep 447887 = 671831) B671831
theorem B447929 : Blo 295830 447929 := bstep (se 2 (by rfl) ⟨167973, by rfl⟩ : syracuseStep 447929 = 335947) B335947
theorem B448007 : Blo 295830 448007 := bstep (se 1 (by rfl) ⟨336005, by rfl⟩ : syracuseStep 448007 = 672011) B672011
theorem B906785 : Blo 295830 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B448043 : Blo 295830 448043 := bstep (se 1 (by rfl) ⟨336032, by rfl⟩ : syracuseStep 448043 = 672065) B672065
theorem B448073 : Blo 295830 448073 := bstep (se 2 (by rfl) ⟨168027, by rfl⟩ : syracuseStep 448073 = 336055) B336055
theorem B448187 : Blo 295830 448187 := bstep (se 1 (by rfl) ⟨336140, by rfl⟩ : syracuseStep 448187 = 672281) B672281
theorem B448247 : Blo 295830 448247 := bstep (se 1 (by rfl) ⟨336185, by rfl⟩ : syracuseStep 448247 = 672371) B672371
theorem B448271 : Blo 295830 448271 := bstep (se 1 (by rfl) ⟨336203, by rfl⟩ : syracuseStep 448271 = 672407) B672407
theorem B448313 : Blo 295830 448313 := bstep (se 2 (by rfl) ⟨168117, by rfl⟩ : syracuseStep 448313 = 336235) B336235
theorem B1005371 : Blo 295830 1005371 := bstep (se 1 (by rfl) ⟨754028, by rfl⟩ : syracuseStep 1005371 = 1508057) B1508057
theorem B448391 : Blo 295830 448391 := bstep (se 1 (by rfl) ⟨336293, by rfl⟩ : syracuseStep 448391 = 672587) B672587
theorem B448427 : Blo 295830 448427 := bstep (se 1 (by rfl) ⟨336320, by rfl⟩ : syracuseStep 448427 = 672641) B672641
theorem B448457 : Blo 295830 448457 := bstep (se 2 (by rfl) ⟨168171, by rfl⟩ : syracuseStep 448457 = 336343) B336343
theorem B1693649 : Blo 295830 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B809003 : Blo 295830 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B448571 : Blo 295830 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B448631 : Blo 295830 448631 := bstep (se 1 (by rfl) ⟨336473, by rfl⟩ : syracuseStep 448631 = 672947) B672947
theorem B448655 : Blo 295830 448655 := bstep (se 1 (by rfl) ⟨336491, by rfl⟩ : syracuseStep 448655 = 672983) B672983
theorem B448697 : Blo 295830 448697 := bstep (se 2 (by rfl) ⟨168261, by rfl⟩ : syracuseStep 448697 = 336523) B336523
theorem B1267913 : Blo 295830 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B448775 : Blo 295830 448775 := bstep (se 1 (by rfl) ⟨336581, by rfl⟩ : syracuseStep 448775 = 673163) B673163
theorem B1005857 : Blo 295830 1005857 := bstep (se 2 (by rfl) ⟨377196, by rfl⟩ : syracuseStep 1005857 = 754393) B754393
theorem B448811 : Blo 295830 448811 := bstep (se 1 (by rfl) ⟨336608, by rfl⟩ : syracuseStep 448811 = 673217) B673217
theorem B448841 : Blo 295830 448841 := bstep (se 2 (by rfl) ⟨168315, by rfl⟩ : syracuseStep 448841 = 336631) B336631
theorem B5757277 : Blo 295830 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B2578823 : Blo 295830 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B1694105 : Blo 295830 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B448955 : Blo 295830 448955 := bstep (se 1 (by rfl) ⟨336716, by rfl⟩ : syracuseStep 448955 = 673433) B673433
theorem B449015 : Blo 295830 449015 := bstep (se 1 (by rfl) ⟨336761, by rfl⟩ : syracuseStep 449015 = 673523) B673523
theorem B1432075 : Blo 295830 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B449039 : Blo 295830 449039 := bstep (se 1 (by rfl) ⟨336779, by rfl⟩ : syracuseStep 449039 = 673559) B673559
theorem B1432093 : Blo 295830 1432093 := bstep (se 3 (by rfl) ⟨268517, by rfl⟩ : syracuseStep 1432093 = 537035) B537035
theorem B3070493 : Blo 295830 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B449081 : Blo 295830 449081 := bstep (se 2 (by rfl) ⟨168405, by rfl⟩ : syracuseStep 449081 = 336811) B336811
theorem B449159 : Blo 295830 449159 := bstep (se 1 (by rfl) ⟨336869, by rfl⟩ : syracuseStep 449159 = 673739) B673739
theorem B449195 : Blo 295830 449195 := bstep (se 1 (by rfl) ⟨336896, by rfl⟩ : syracuseStep 449195 = 673793) B673793
theorem B449225 : Blo 295830 449225 := bstep (se 2 (by rfl) ⟨168459, by rfl⟩ : syracuseStep 449225 = 336919) B336919
theorem B711425 : Blo 295830 711425 := bstep (se 2 (by rfl) ⟨266784, by rfl⟩ : syracuseStep 711425 = 533569) B533569
theorem B449339 : Blo 295830 449339 := bstep (se 1 (by rfl) ⟨337004, by rfl⟩ : syracuseStep 449339 = 674009) B674009
theorem B1006451 : Blo 295830 1006451 := bstep (se 1 (by rfl) ⟨754838, by rfl⟩ : syracuseStep 1006451 = 1509677) B1509677
theorem B449399 : Blo 295830 449399 := bstep (se 1 (by rfl) ⟨337049, by rfl⟩ : syracuseStep 449399 = 674099) B674099
theorem B449423 : Blo 295830 449423 := bstep (se 1 (by rfl) ⟨337067, by rfl⟩ : syracuseStep 449423 = 674135) B674135
theorem B1072025 : Blo 295830 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B449465 : Blo 295830 449465 := bstep (se 2 (by rfl) ⟨168549, by rfl⟩ : syracuseStep 449465 = 337099) B337099
theorem B449543 : Blo 295830 449543 := bstep (se 1 (by rfl) ⟨337157, by rfl⟩ : syracuseStep 449543 = 674315) B674315
theorem B449579 : Blo 295830 449579 := bstep (se 1 (by rfl) ⟨337184, by rfl⟩ : syracuseStep 449579 = 674369) B674369
theorem B449609 : Blo 295830 449609 := bstep (se 2 (by rfl) ⟨168603, by rfl⟩ : syracuseStep 449609 = 337207) B337207
theorem B1268855 : Blo 295830 1268855 := bstep (se 1 (by rfl) ⟨951641, by rfl⟩ : syracuseStep 1268855 = 1903283) B1903283
theorem B810137 : Blo 295830 810137 := bstep (se 2 (by rfl) ⟨303801, by rfl⟩ : syracuseStep 810137 = 607603) B607603
theorem B449723 : Blo 295830 449723 := bstep (se 1 (by rfl) ⟨337292, by rfl⟩ : syracuseStep 449723 = 674585) B674585
theorem B1924499 : Blo 295830 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B908801 : Blo 295830 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B5693003 : Blo 295830 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B843635 : Blo 295830 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B1499147 : Blo 295830 1499147 := bstep (se 1 (by rfl) ⟨1124360, by rfl⟩ : syracuseStep 1499147 = 2248721) B2248721
theorem B1269827 : Blo 295830 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B1499309 : Blo 295830 1499309 := bstep (se 3 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 1499309 = 562241) B562241
theorem B844091 : Blo 295830 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B319879 : Blo 295830 319879 := bstep (se 1 (by rfl) ⟨239909, by rfl⟩ : syracuseStep 319879 = 479819) B479819
theorem B3236395 : Blo 295830 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B451513 : Blo 295830 451513 := bstep (se 2 (by rfl) ⟨169317, by rfl⟩ : syracuseStep 451513 = 338635) B338635
theorem B2909189 : Blo 295830 2909189 := bstep (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) B545473
theorem B1532951 : Blo 295830 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B844843 : Blo 295830 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B451883 : Blo 295830 451883 := bstep (se 1 (by rfl) ⟨338912, by rfl⟩ : syracuseStep 451883 = 677825) B677825
theorem B845117 : Blo 295830 845117 := bstep (se 3 (by rfl) ⟨158459, by rfl⟩ : syracuseStep 845117 = 316919) B316919
theorem B1009043 : Blo 295830 1009043 := bstep (se 1 (by rfl) ⟨756782, by rfl⟩ : syracuseStep 1009043 = 1513565) B1513565
theorem B1500929 : Blo 295830 1500929 := bstep (se 2 (by rfl) ⟨562848, by rfl⟩ : syracuseStep 1500929 = 1125697) B1125697
theorem B2844467 : Blo 295830 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B1632209 : Blo 295830 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B4843637 : Blo 295830 4843637 := bstep (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) B454091
theorem B845959 : Blo 295830 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1599689 : Blo 295830 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B715009 : Blo 295830 715009 := bstep (se 2 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 715009 = 536257) B536257
theorem B1599859 : Blo 295830 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B846233 : Blo 295830 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B1501739 : Blo 295830 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B1075799 : Blo 295830 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B3828343 : Blo 295830 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B453367 : Blo 295830 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B5434127 : Blo 295830 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B1010447 : Blo 295830 1010447 := bstep (se 1 (by rfl) ⟨757835, by rfl⟩ : syracuseStep 1010447 = 1515671) B1515671
theorem B2878487 : Blo 295830 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1010717 : Blo 295830 1010717 := bstep (se 3 (by rfl) ⟨189509, by rfl⟩ : syracuseStep 1010717 = 379019) B379019
theorem B1076665 : Blo 295830 1076665 := bstep (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) B807499
theorem B847361 : Blo 295830 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B9203341 : Blo 295830 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B749209 : Blo 295830 749209 := bstep (se 2 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 749209 = 561907) B561907
theorem B749371 : Blo 295830 749371 := bstep (se 1 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 749371 = 1124057) B1124057
theorem B1503035 : Blo 295830 1503035 := bstep (se 1 (by rfl) ⟨1127276, by rfl⟩ : syracuseStep 1503035 = 2254553) B2254553
theorem B749513 : Blo 295830 749513 := bstep (se 2 (by rfl) ⟨281067, by rfl⟩ : syracuseStep 749513 = 562135) B562135
theorem B847817 : Blo 295830 847817 := bstep (se 2 (by rfl) ⟨317931, by rfl⟩ : syracuseStep 847817 = 635863) B635863
theorem B1503197 : Blo 295830 1503197 := bstep (se 3 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 1503197 = 563699) B563699
theorem B2256983 : Blo 295830 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B422023 : Blo 295830 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B749857 : Blo 295830 749857 := bstep (se 2 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 749857 = 562393) B562393
theorem B1503521 : Blo 295830 1503521 := bstep (se 2 (by rfl) ⟨563820, by rfl⟩ : syracuseStep 1503521 = 1127641) B1127641
theorem B1602109 : Blo 295830 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B422587 : Blo 295830 422587 := bstep (se 1 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 422587 = 633881) B633881
theorem B1078049 : Blo 295830 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B750455 : Blo 295830 750455 := bstep (se 1 (by rfl) ⟨562841, by rfl⟩ : syracuseStep 750455 = 1125683) B1125683
theorem B1504493 : Blo 295830 1504493 := bstep (se 3 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 1504493 = 564185) B564185
theorem B1701121 : Blo 295830 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B1209659 : Blo 295830 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B423481 : Blo 295830 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B849467 : Blo 295830 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B1701647 : Blo 295830 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B358187 : Blo 295830 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B1603475 : Blo 295830 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B5732369 : Blo 295830 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B1505303 : Blo 295830 1505303 := bstep (se 1 (by rfl) ⟨1128977, by rfl⟩ : syracuseStep 1505303 = 2257955) B2257955
theorem B751751 : Blo 295830 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B358543 : Blo 295830 358543 := bstep (se 1 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 358543 = 537815) B537815
theorem B751801 : Blo 295830 751801 := bstep (se 2 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 751801 = 563851) B563851
theorem B850105 : Blo 295830 850105 := bstep (se 2 (by rfl) ⟨318789, by rfl⟩ : syracuseStep 850105 = 637579) B637579
theorem B1440089 : Blo 295830 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B719219 : Blo 295830 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B850493 : Blo 295830 850493 := bstep (se 3 (by rfl) ⟨159467, by rfl⟩ : syracuseStep 850493 = 318935) B318935
theorem B1833673 : Blo 295830 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B424711 : Blo 295830 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B752399 : Blo 295830 752399 := bstep (se 1 (by rfl) ⟨564299, by rfl⟩ : syracuseStep 752399 = 1128599) B1128599
theorem B1014713 : Blo 295830 1014713 := bstep (se 2 (by rfl) ⟨380517, by rfl⟩ : syracuseStep 1014713 = 761035) B761035
theorem B1703105 : Blo 295830 1703105 := bstep (se 2 (by rfl) ⟨638664, by rfl⟩ : syracuseStep 1703105 = 1277329) B1277329
theorem B1604879 : Blo 295830 1604879 := bstep (se 1 (by rfl) ⟨1203659, by rfl⟩ : syracuseStep 1604879 = 2407319) B2407319
theorem B720161 : Blo 295830 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B753097 : Blo 295830 753097 := bstep (se 2 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 753097 = 564823) B564823
theorem B425417 : Blo 295830 425417 := bstep (se 2 (by rfl) ⟨159531, by rfl⟩ : syracuseStep 425417 = 319063) B319063
theorem B425531 : Blo 295830 425531 := bstep (se 1 (by rfl) ⟨319148, by rfl⟩ : syracuseStep 425531 = 638297) B638297
theorem B753239 : Blo 295830 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B851609 : Blo 295830 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B3440357 : Blo 295830 3440357 := bstep (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) B645067
theorem B3833675 : Blo 295830 3833675 := bstep (se 1 (by rfl) ⟨2875256, by rfl⟩ : syracuseStep 3833675 = 5750513) B5750513
theorem B12058571 : Blo 295830 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B1507409 : Blo 295830 1507409 := bstep (se 2 (by rfl) ⟨565278, by rfl⟩ : syracuseStep 1507409 = 1130557) B1130557
theorem B2719907 : Blo 295830 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B754049 : Blo 295830 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B1147279 : Blo 295830 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B754505 : Blo 295830 754505 := bstep (se 2 (by rfl) ⟨282939, by rfl⟩ : syracuseStep 754505 = 565879) B565879
theorem B295855 : Blo 295830 295855 := bstep (se 1 (by rfl) ⟨221891, by rfl⟩ : syracuseStep 295855 = 443783) B443783
theorem B295879 : Blo 295830 295879 := bstep (se 1 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 295879 = 443819) B443819
theorem B295899 : Blo 295830 295899 := bstep (se 1 (by rfl) ⟨221924, by rfl⟩ : syracuseStep 295899 = 443849) B443849
theorem B295975 : Blo 295830 295975 := bstep (se 1 (by rfl) ⟨221981, by rfl⟩ : syracuseStep 295975 = 443963) B443963
theorem B296015 : Blo 295830 296015 := bstep (se 1 (by rfl) ⟨222011, by rfl⟩ : syracuseStep 296015 = 444023) B444023
theorem B296031 : Blo 295830 296031 := bstep (se 1 (by rfl) ⟨222023, by rfl⟩ : syracuseStep 296031 = 444047) B444047
theorem B296059 : Blo 295830 296059 := bstep (se 1 (by rfl) ⟨222044, by rfl⟩ : syracuseStep 296059 = 444089) B444089
theorem B459899 : Blo 295830 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B754859 : Blo 295830 754859 := bstep (se 1 (by rfl) ⟨566144, by rfl⟩ : syracuseStep 754859 = 1132289) B1132289
theorem B296111 : Blo 295830 296111 := bstep (se 1 (by rfl) ⟨222083, by rfl⟩ : syracuseStep 296111 = 444167) B444167
theorem B296135 : Blo 295830 296135 := bstep (se 1 (by rfl) ⟨222101, by rfl⟩ : syracuseStep 296135 = 444203) B444203
theorem B296155 : Blo 295830 296155 := bstep (se 1 (by rfl) ⟨222116, by rfl⟩ : syracuseStep 296155 = 444233) B444233
theorem B296231 : Blo 295830 296231 := bstep (se 1 (by rfl) ⟨222173, by rfl⟩ : syracuseStep 296231 = 444347) B444347
theorem B296271 : Blo 295830 296271 := bstep (se 1 (by rfl) ⟨222203, by rfl⟩ : syracuseStep 296271 = 444407) B444407
theorem B296287 : Blo 295830 296287 := bstep (se 1 (by rfl) ⟨222215, by rfl⟩ : syracuseStep 296287 = 444431) B444431
theorem B296315 : Blo 295830 296315 := bstep (se 1 (by rfl) ⟨222236, by rfl⟩ : syracuseStep 296315 = 444473) B444473
theorem B296367 : Blo 295830 296367 := bstep (se 1 (by rfl) ⟨222275, by rfl⟩ : syracuseStep 296367 = 444551) B444551
theorem B296391 : Blo 295830 296391 := bstep (se 1 (by rfl) ⟨222293, by rfl⟩ : syracuseStep 296391 = 444587) B444587
theorem B4326857 : Blo 295830 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B296411 : Blo 295830 296411 := bstep (se 1 (by rfl) ⟨222308, by rfl⟩ : syracuseStep 296411 = 444617) B444617
theorem B296487 : Blo 295830 296487 := bstep (se 1 (by rfl) ⟨222365, by rfl⟩ : syracuseStep 296487 = 444731) B444731
theorem B296527 : Blo 295830 296527 := bstep (se 1 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 296527 = 444791) B444791
theorem B296543 : Blo 295830 296543 := bstep (se 1 (by rfl) ⟨222407, by rfl⟩ : syracuseStep 296543 = 444815) B444815
theorem B296571 : Blo 295830 296571 := bstep (se 1 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 296571 = 444857) B444857
theorem B296623 : Blo 295830 296623 := bstep (se 1 (by rfl) ⟨222467, by rfl⟩ : syracuseStep 296623 = 444935) B444935
theorem B296647 : Blo 295830 296647 := bstep (se 1 (by rfl) ⟨222485, by rfl⟩ : syracuseStep 296647 = 444971) B444971
theorem B296667 : Blo 295830 296667 := bstep (se 1 (by rfl) ⟨222500, by rfl⟩ : syracuseStep 296667 = 445001) B445001
theorem B296743 : Blo 295830 296743 := bstep (se 1 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 296743 = 445115) B445115
theorem B296783 : Blo 295830 296783 := bstep (se 1 (by rfl) ⟨222587, by rfl⟩ : syracuseStep 296783 = 445175) B445175
theorem B296799 : Blo 295830 296799 := bstep (se 1 (by rfl) ⟨222599, by rfl⟩ : syracuseStep 296799 = 445199) B445199
theorem B296827 : Blo 295830 296827 := bstep (se 1 (by rfl) ⟨222620, by rfl⟩ : syracuseStep 296827 = 445241) B445241
theorem B296879 : Blo 295830 296879 := bstep (se 1 (by rfl) ⟨222659, by rfl⟩ : syracuseStep 296879 = 445319) B445319
theorem B755639 : Blo 295830 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B722875 : Blo 295830 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B2197441 : Blo 295830 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B296903 : Blo 295830 296903 := bstep (se 1 (by rfl) ⟨222677, by rfl⟩ : syracuseStep 296903 = 445355) B445355
theorem B296923 : Blo 295830 296923 := bstep (se 1 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 296923 = 445385) B445385
theorem B1706021 : Blo 295830 1706021 := bstep (se 4 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 1706021 = 319879) B319879
theorem B296999 : Blo 295830 296999 := bstep (se 1 (by rfl) ⟨222749, by rfl⟩ : syracuseStep 296999 = 445499) B445499
theorem B1378361 : Blo 295830 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B297039 : Blo 295830 297039 := bstep (se 1 (by rfl) ⟨222779, by rfl⟩ : syracuseStep 297039 = 445559) B445559
theorem B297055 : Blo 295830 297055 := bstep (se 1 (by rfl) ⟨222791, by rfl⟩ : syracuseStep 297055 = 445583) B445583
theorem B297083 : Blo 295830 297083 := bstep (se 1 (by rfl) ⟨222812, by rfl⟩ : syracuseStep 297083 = 445625) B445625
theorem B297135 : Blo 295830 297135 := bstep (se 1 (by rfl) ⟨222851, by rfl⟩ : syracuseStep 297135 = 445703) B445703
theorem B297159 : Blo 295830 297159 := bstep (se 1 (by rfl) ⟨222869, by rfl⟩ : syracuseStep 297159 = 445739) B445739
theorem B297179 : Blo 295830 297179 := bstep (se 1 (by rfl) ⟨222884, by rfl⟩ : syracuseStep 297179 = 445769) B445769
theorem B297255 : Blo 295830 297255 := bstep (se 1 (by rfl) ⟨222941, by rfl⟩ : syracuseStep 297255 = 445883) B445883
theorem B297295 : Blo 295830 297295 := bstep (se 1 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 297295 = 445943) B445943
theorem B297311 : Blo 295830 297311 := bstep (se 1 (by rfl) ⟨222983, by rfl⟩ : syracuseStep 297311 = 445967) B445967
theorem B297339 : Blo 295830 297339 := bstep (se 1 (by rfl) ⟨223004, by rfl⟩ : syracuseStep 297339 = 446009) B446009
theorem B297391 : Blo 295830 297391 := bstep (se 1 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 297391 = 446087) B446087
theorem B297415 : Blo 295830 297415 := bstep (se 1 (by rfl) ⟨223061, by rfl⟩ : syracuseStep 297415 = 446123) B446123
theorem B854491 : Blo 295830 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B297435 : Blo 295830 297435 := bstep (se 1 (by rfl) ⟨223076, by rfl⟩ : syracuseStep 297435 = 446153) B446153
theorem B297511 : Blo 295830 297511 := bstep (se 1 (by rfl) ⟨223133, by rfl⟩ : syracuseStep 297511 = 446267) B446267
theorem B297551 : Blo 295830 297551 := bstep (se 1 (by rfl) ⟨223163, by rfl⟩ : syracuseStep 297551 = 446327) B446327
theorem B297567 : Blo 295830 297567 := bstep (se 1 (by rfl) ⟨223175, by rfl⟩ : syracuseStep 297567 = 446351) B446351
theorem B297595 : Blo 295830 297595 := bstep (se 1 (by rfl) ⟨223196, by rfl⟩ : syracuseStep 297595 = 446393) B446393
theorem B297647 : Blo 295830 297647 := bstep (se 1 (by rfl) ⟨223235, by rfl⟩ : syracuseStep 297647 = 446471) B446471
theorem B297671 : Blo 295830 297671 := bstep (se 1 (by rfl) ⟨223253, by rfl⟩ : syracuseStep 297671 = 446507) B446507
theorem B297691 : Blo 295830 297691 := bstep (se 1 (by rfl) ⟨223268, by rfl⟩ : syracuseStep 297691 = 446537) B446537
theorem B297767 : Blo 295830 297767 := bstep (se 1 (by rfl) ⟨223325, by rfl⟩ : syracuseStep 297767 = 446651) B446651
theorem B297807 : Blo 295830 297807 := bstep (se 1 (by rfl) ⟨223355, by rfl⟩ : syracuseStep 297807 = 446711) B446711
theorem B297823 : Blo 295830 297823 := bstep (se 1 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 297823 = 446735) B446735
theorem B297851 : Blo 295830 297851 := bstep (se 1 (by rfl) ⟨223388, by rfl⟩ : syracuseStep 297851 = 446777) B446777
theorem B756641 : Blo 295830 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B297903 : Blo 295830 297903 := bstep (se 1 (by rfl) ⟨223427, by rfl⟩ : syracuseStep 297903 = 446855) B446855
theorem B2067383 : Blo 295830 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B297927 : Blo 295830 297927 := bstep (se 1 (by rfl) ⟨223445, by rfl⟩ : syracuseStep 297927 = 446891) B446891
theorem B297947 : Blo 295830 297947 := bstep (se 1 (by rfl) ⟨223460, by rfl⟩ : syracuseStep 297947 = 446921) B446921
theorem B953345 : Blo 295830 953345 := bstep (se 2 (by rfl) ⟨357504, by rfl⟩ : syracuseStep 953345 = 715009) B715009
theorem B8555543 : Blo 295830 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B298023 : Blo 295830 298023 := bstep (se 1 (by rfl) ⟨223517, by rfl⟩ : syracuseStep 298023 = 447035) B447035
theorem B298063 : Blo 295830 298063 := bstep (se 1 (by rfl) ⟨223547, by rfl⟩ : syracuseStep 298063 = 447095) B447095
theorem B298079 : Blo 295830 298079 := bstep (se 1 (by rfl) ⟨223559, by rfl⟩ : syracuseStep 298079 = 447119) B447119
theorem B298107 : Blo 295830 298107 := bstep (se 1 (by rfl) ⟨223580, by rfl⟩ : syracuseStep 298107 = 447161) B447161
theorem B2133145 : Blo 295830 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B1903769 : Blo 295830 1903769 := bstep (se 2 (by rfl) ⟨713913, by rfl⟩ : syracuseStep 1903769 = 1427827) B1427827
theorem B298159 : Blo 295830 298159 := bstep (se 1 (by rfl) ⟨223619, by rfl⟩ : syracuseStep 298159 = 447239) B447239
theorem B298183 : Blo 295830 298183 := bstep (se 1 (by rfl) ⟨223637, by rfl⟩ : syracuseStep 298183 = 447275) B447275
theorem B298203 : Blo 295830 298203 := bstep (se 1 (by rfl) ⟨223652, by rfl⟩ : syracuseStep 298203 = 447305) B447305
theorem B298279 : Blo 295830 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B298319 : Blo 295830 298319 := bstep (se 1 (by rfl) ⟨223739, by rfl⟩ : syracuseStep 298319 = 447479) B447479
theorem B298335 : Blo 295830 298335 := bstep (se 1 (by rfl) ⟨223751, by rfl⟩ : syracuseStep 298335 = 447503) B447503
theorem B757097 : Blo 295830 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B298363 : Blo 295830 298363 := bstep (se 1 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 298363 = 447545) B447545
theorem B298415 : Blo 295830 298415 := bstep (se 1 (by rfl) ⟨223811, by rfl⟩ : syracuseStep 298415 = 447623) B447623
theorem B298439 : Blo 295830 298439 := bstep (se 1 (by rfl) ⟨223829, by rfl⟩ : syracuseStep 298439 = 447659) B447659
theorem B298459 : Blo 295830 298459 := bstep (se 1 (by rfl) ⟨223844, by rfl⟩ : syracuseStep 298459 = 447689) B447689
theorem B298535 : Blo 295830 298535 := bstep (se 1 (by rfl) ⟨223901, by rfl⟩ : syracuseStep 298535 = 447803) B447803
theorem B298575 : Blo 295830 298575 := bstep (se 1 (by rfl) ⟨223931, by rfl⟩ : syracuseStep 298575 = 447863) B447863
theorem B298591 : Blo 295830 298591 := bstep (se 1 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 298591 = 447887) B447887
theorem B298619 : Blo 295830 298619 := bstep (se 1 (by rfl) ⟨223964, by rfl⟩ : syracuseStep 298619 = 447929) B447929
theorem B298671 : Blo 295830 298671 := bstep (se 1 (by rfl) ⟨224003, by rfl⟩ : syracuseStep 298671 = 448007) B448007
theorem B8261297 : Blo 295830 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B298695 : Blo 295830 298695 := bstep (se 1 (by rfl) ⟨224021, by rfl⟩ : syracuseStep 298695 = 448043) B448043
theorem B298715 : Blo 295830 298715 := bstep (se 1 (by rfl) ⟨224036, by rfl⟩ : syracuseStep 298715 = 448073) B448073
theorem B298791 : Blo 295830 298791 := bstep (se 1 (by rfl) ⟨224093, by rfl⟩ : syracuseStep 298791 = 448187) B448187
theorem B298831 : Blo 295830 298831 := bstep (se 1 (by rfl) ⟨224123, by rfl⟩ : syracuseStep 298831 = 448247) B448247
theorem B298847 : Blo 295830 298847 := bstep (se 1 (by rfl) ⟨224135, by rfl⟩ : syracuseStep 298847 = 448271) B448271
theorem B298875 : Blo 295830 298875 := bstep (se 1 (by rfl) ⟨224156, by rfl⟩ : syracuseStep 298875 = 448313) B448313
theorem B298927 : Blo 295830 298927 := bstep (se 1 (by rfl) ⟨224195, by rfl⟩ : syracuseStep 298927 = 448391) B448391
theorem B298951 : Blo 295830 298951 := bstep (se 1 (by rfl) ⟨224213, by rfl⟩ : syracuseStep 298951 = 448427) B448427
theorem B298971 : Blo 295830 298971 := bstep (se 1 (by rfl) ⟨224228, by rfl⟩ : syracuseStep 298971 = 448457) B448457
theorem B299047 : Blo 295830 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B299087 : Blo 295830 299087 := bstep (se 1 (by rfl) ⟨224315, by rfl⟩ : syracuseStep 299087 = 448631) B448631
theorem B299103 : Blo 295830 299103 := bstep (se 1 (by rfl) ⟨224327, by rfl⟩ : syracuseStep 299103 = 448655) B448655
theorem B299131 : Blo 295830 299131 := bstep (se 1 (by rfl) ⟨224348, by rfl⟩ : syracuseStep 299131 = 448697) B448697
theorem B2265245 : Blo 295830 2265245 := bstep (se 3 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 2265245 = 849467) B849467
theorem B299183 : Blo 295830 299183 := bstep (se 1 (by rfl) ⟨224387, by rfl⟩ : syracuseStep 299183 = 448775) B448775
theorem B299207 : Blo 295830 299207 := bstep (se 1 (by rfl) ⟨224405, by rfl⟩ : syracuseStep 299207 = 448811) B448811
theorem B299227 : Blo 295830 299227 := bstep (se 1 (by rfl) ⟨224420, by rfl⟩ : syracuseStep 299227 = 448841) B448841
theorem B299303 : Blo 295830 299303 := bstep (se 1 (by rfl) ⟨224477, by rfl⟩ : syracuseStep 299303 = 448955) B448955
theorem B299343 : Blo 295830 299343 := bstep (se 1 (by rfl) ⟨224507, by rfl⟩ : syracuseStep 299343 = 449015) B449015
theorem B299359 : Blo 295830 299359 := bstep (se 1 (by rfl) ⟨224519, by rfl⟩ : syracuseStep 299359 = 449039) B449039
theorem B299387 : Blo 295830 299387 := bstep (se 1 (by rfl) ⟨224540, by rfl⟩ : syracuseStep 299387 = 449081) B449081
theorem B299439 : Blo 295830 299439 := bstep (se 1 (by rfl) ⟨224579, by rfl⟩ : syracuseStep 299439 = 449159) B449159
theorem B299463 : Blo 295830 299463 := bstep (se 1 (by rfl) ⟨224597, by rfl⟩ : syracuseStep 299463 = 449195) B449195
theorem B299483 : Blo 295830 299483 := bstep (se 1 (by rfl) ⟨224612, by rfl⟩ : syracuseStep 299483 = 449225) B449225
theorem B1511945 : Blo 295830 1511945 := bstep (se 2 (by rfl) ⟨566979, by rfl⟩ : syracuseStep 1511945 = 1133959) B1133959
theorem B758281 : Blo 295830 758281 := bstep (se 2 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 758281 = 568711) B568711
theorem B299559 : Blo 295830 299559 := bstep (se 1 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 299559 = 449339) B449339
theorem B299599 : Blo 295830 299599 := bstep (se 1 (by rfl) ⟨224699, by rfl⟩ : syracuseStep 299599 = 449399) B449399
theorem B299615 : Blo 295830 299615 := bstep (se 1 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 299615 = 449423) B449423
theorem B299643 : Blo 295830 299643 := bstep (se 1 (by rfl) ⟨224732, by rfl⟩ : syracuseStep 299643 = 449465) B449465
theorem B299695 : Blo 295830 299695 := bstep (se 1 (by rfl) ⟨224771, by rfl⟩ : syracuseStep 299695 = 449543) B449543
theorem B299719 : Blo 295830 299719 := bstep (se 1 (by rfl) ⟨224789, by rfl⟩ : syracuseStep 299719 = 449579) B449579
theorem B299739 : Blo 295830 299739 := bstep (se 1 (by rfl) ⟨224804, by rfl⟩ : syracuseStep 299739 = 449609) B449609
theorem B955165 : Blo 295830 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B299815 : Blo 295830 299815 := bstep (se 1 (by rfl) ⟨224861, by rfl⟩ : syracuseStep 299815 = 449723) B449723
theorem B2560841 : Blo 295830 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B1282999 : Blo 295830 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B332923 : Blo 295830 332923 := bstep (se 1 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 332923 = 499385) B499385
theorem B759145 : Blo 295830 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B562697 : Blo 295830 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B562727 : Blo 295830 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B333391 : Blo 295830 333391 := bstep (se 1 (by rfl) ⟨250043, by rfl⟩ : syracuseStep 333391 = 500087) B500087
theorem B3381101 : Blo 295830 3381101 := bstep (se 3 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 3381101 = 1267913) B1267913
theorem B1513403 : Blo 295830 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B333787 : Blo 295830 333787 := bstep (se 1 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 333787 = 500681) B500681
theorem B1939459 : Blo 295830 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1021967 : Blo 295830 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B2136145 : Blo 295830 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B301255 : Blo 295830 301255 := bstep (se 1 (by rfl) ⟨225941, by rfl⟩ : syracuseStep 301255 = 451883) B451883
theorem B563411 : Blo 295830 563411 := bstep (se 1 (by rfl) ⟨422558, by rfl⟩ : syracuseStep 563411 = 845117) B845117
theorem B563449 : Blo 295830 563449 := bstep (se 2 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 563449 = 422587) B422587
theorem B334255 : Blo 295830 334255 := bstep (se 1 (by rfl) ⟨250691, by rfl⟩ : syracuseStep 334255 = 501383) B501383
theorem B1907459 : Blo 295830 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B334687 : Blo 295830 334687 := bstep (se 1 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 334687 = 502031) B502031
theorem B564155 : Blo 295830 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B2268161 : Blo 295830 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B335047 : Blo 295830 335047 := bstep (se 1 (by rfl) ⟨251285, by rfl⟩ : syracuseStep 335047 = 502571) B502571
theorem B1514699 : Blo 295830 1514699 := bstep (se 1 (by rfl) ⟨1136024, by rfl⟩ : syracuseStep 1514699 = 2272049) B2272049
theorem B564641 : Blo 295830 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B9182645 : Blo 295830 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B564907 : Blo 295830 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B499675 : Blo 295830 499675 := bstep (se 1 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 499675 = 749513) B749513
theorem B565211 : Blo 295830 565211 := bstep (se 1 (by rfl) ⟨423908, by rfl⟩ : syracuseStep 565211 = 847817) B847817
theorem B335911 : Blo 295830 335911 := bstep (se 1 (by rfl) ⟨251933, by rfl⟩ : syracuseStep 335911 = 503867) B503867
theorem B7676369 : Blo 295830 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B500303 : Blo 295830 500303 := bstep (se 1 (by rfl) ⟨375227, by rfl⟩ : syracuseStep 500303 = 750455) B750455
theorem B1909433 : Blo 295830 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B3384017 : Blo 295830 3384017 := bstep (se 2 (by rfl) ⟨1269006, by rfl⟩ : syracuseStep 3384017 = 2538013) B2538013
theorem B1909457 : Blo 295830 1909457 := bstep (se 2 (by rfl) ⟨716046, by rfl⟩ : syracuseStep 1909457 = 1432093) B1432093
theorem B1811429 : Blo 295830 1811429 := bstep (se 4 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 1811429 = 339643) B339643
theorem B566281 : Blo 295830 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B501167 : Blo 295830 501167 := bstep (se 1 (by rfl) ⟨375875, by rfl⟩ : syracuseStep 501167 = 751751) B751751
theorem B960059 : Blo 295830 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B566995 : Blo 295830 566995 := bstep (se 1 (by rfl) ⟨425246, by rfl⟩ : syracuseStep 566995 = 850493) B850493
theorem B501599 : Blo 295830 501599 := bstep (se 1 (by rfl) ⟨376199, by rfl⟩ : syracuseStep 501599 = 752399) B752399
theorem B534377 : Blo 295830 534377 := bstep (se 2 (by rfl) ⟨200391, by rfl⟩ : syracuseStep 534377 = 400783) B400783
theorem B5121953 : Blo 295830 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B665657 : Blo 295830 665657 := bstep (se 2 (by rfl) ⟨249621, by rfl⟩ : syracuseStep 665657 = 499243) B499243
theorem B6400133 : Blo 295830 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B17410229 : Blo 295830 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B665999 : Blo 295830 665999 := bstep (se 1 (by rfl) ⟨499499, by rfl⟩ : syracuseStep 665999 = 998999) B998999
theorem B502159 : Blo 295830 502159 := bstep (se 1 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 502159 = 753239) B753239
theorem B567739 : Blo 295830 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B32156189 : Blo 295830 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B1124999 : Blo 295830 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B666323 : Blo 295830 666323 := bstep (se 1 (by rfl) ⟨499742, by rfl⟩ : syracuseStep 666323 = 999485) B999485
theorem B568225 : Blo 295830 568225 := bstep (se 2 (by rfl) ⟨213084, by rfl⟩ : syracuseStep 568225 = 426169) B426169
theorem B404399 : Blo 295830 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B502841 : Blo 295830 502841 := bstep (se 2 (by rfl) ⟨188565, by rfl⟩ : syracuseStep 502841 = 377131) B377131
theorem B2272535 : Blo 295830 2272535 := bstep (se 1 (by rfl) ⟨1704401, by rfl⟩ : syracuseStep 2272535 = 3408803) B3408803
theorem B568795 : Blo 295830 568795 := bstep (se 1 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 568795 = 853193) B853193
theorem B1945127 : Blo 295830 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B667259 : Blo 295830 667259 := bstep (se 1 (by rfl) ⟨500444, by rfl⟩ : syracuseStep 667259 = 1000889) B1000889
theorem B601847 : Blo 295830 601847 := bstep (se 1 (by rfl) ⟨451385, by rfl⟩ : syracuseStep 601847 = 902771) B902771
theorem B503543 : Blo 295830 503543 := bstep (se 1 (by rfl) ⟨377657, by rfl⟩ : syracuseStep 503543 = 755315) B755315
theorem B667385 : Blo 295830 667385 := bstep (se 2 (by rfl) ⟨250269, by rfl⟩ : syracuseStep 667385 = 500539) B500539
theorem B1552321 : Blo 295830 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B667655 : Blo 295830 667655 := bstep (se 1 (by rfl) ⟨500741, by rfl⟩ : syracuseStep 667655 = 1001483) B1001483
theorem B1126457 : Blo 295830 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B667727 : Blo 295830 667727 := bstep (se 1 (by rfl) ⟨500795, by rfl⟩ : syracuseStep 667727 = 1001591) B1001591
theorem B503887 : Blo 295830 503887 := bstep (se 1 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 503887 = 755831) B755831
theorem B864427 : Blo 295830 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B504137 : Blo 295830 504137 := bstep (se 2 (by rfl) ⟨189051, by rfl⟩ : syracuseStep 504137 = 378103) B378103
theorem B668123 : Blo 295830 668123 := bstep (se 1 (by rfl) ⟨501092, by rfl⟩ : syracuseStep 668123 = 1002185) B1002185
theorem B340519 : Blo 295830 340519 := bstep (se 1 (by rfl) ⟨255389, by rfl⟩ : syracuseStep 340519 = 510779) B510779
theorem B2273993 : Blo 295830 2273993 := bstep (se 2 (by rfl) ⟨852747, by rfl⟩ : syracuseStep 2273993 = 1705495) B1705495
theorem B504569 : Blo 295830 504569 := bstep (se 2 (by rfl) ⟨189213, by rfl⟩ : syracuseStep 504569 = 378427) B378427
theorem B1618717 : Blo 295830 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B308047 : Blo 295830 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B668591 : Blo 295830 668591 := bstep (se 1 (by rfl) ⟨501443, by rfl⟩ : syracuseStep 668591 = 1002887) B1002887
theorem B504751 : Blo 295830 504751 := bstep (se 1 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 504751 = 757127) B757127
theorem B504839 : Blo 295830 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B8107073 : Blo 295830 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B668843 : Blo 295830 668843 := bstep (se 1 (by rfl) ⟨501632, by rfl⟩ : syracuseStep 668843 = 1003265) B1003265
theorem B505183 : Blo 295830 505183 := bstep (se 1 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 505183 = 757775) B757775
theorem B4634003 : Blo 295830 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B1684901 : Blo 295830 1684901 := bstep (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) B315919
theorem B505271 : Blo 295830 505271 := bstep (se 1 (by rfl) ⟨378953, by rfl⟩ : syracuseStep 505271 = 757907) B757907
theorem B1127945 : Blo 295830 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B669383 : Blo 295830 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B374635 : Blo 295830 374635 := bstep (se 1 (by rfl) ⟨280976, by rfl⟩ : syracuseStep 374635 = 561953) B561953
theorem B1685357 : Blo 295830 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B505865 : Blo 295830 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B374863 : Blo 295830 374863 := bstep (se 1 (by rfl) ⟨281147, by rfl⟩ : syracuseStep 374863 = 562295) B562295
theorem B3225757 : Blo 295830 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B604523 : Blo 295830 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B3389849 : Blo 295830 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B1686041 : Blo 295830 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B670247 : Blo 295830 670247 := bstep (se 1 (by rfl) ⟨502685, by rfl⟩ : syracuseStep 670247 = 1005371) B1005371
theorem B1129099 : Blo 295830 1129099 := bstep (se 1 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 1129099 = 1693649) B1693649
theorem B539335 : Blo 295830 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B670571 : Blo 295830 670571 := bstep (se 1 (by rfl) ⟨502928, by rfl⟩ : syracuseStep 670571 = 1005857) B1005857
theorem B670625 : Blo 295830 670625 := bstep (se 2 (by rfl) ⟨251484, by rfl⟩ : syracuseStep 670625 = 502969) B502969
theorem B1719215 : Blo 295830 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B1129403 : Blo 295830 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B2046995 : Blo 295830 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B375931 : Blo 295830 375931 := bstep (se 1 (by rfl) ⟨281948, by rfl⟩ : syracuseStep 375931 = 563897) B563897
theorem B474283 : Blo 295830 474283 := bstep (se 1 (by rfl) ⟨355712, by rfl⟩ : syracuseStep 474283 = 711425) B711425
theorem B670967 : Blo 295830 670967 := bstep (se 1 (by rfl) ⟨503225, by rfl⟩ : syracuseStep 670967 = 1006451) B1006451
theorem B376159 : Blo 295830 376159 := bstep (se 1 (by rfl) ⟨282119, by rfl⟩ : syracuseStep 376159 = 564239) B564239
theorem B540091 : Blo 295830 540091 := bstep (se 1 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 540091 = 810137) B810137
theorem B12271121 : Blo 295830 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B998945 : Blo 295830 998945 := bstep (se 2 (by rfl) ⟨374604, by rfl⟩ : syracuseStep 998945 = 749209) B749209
theorem B2408069 : Blo 295830 2408069 := bstep (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) B451513
theorem B999161 : Blo 295830 999161 := bstep (se 2 (by rfl) ⟨374685, by rfl⟩ : syracuseStep 999161 = 749371) B749371
theorem B671561 : Blo 295830 671561 := bstep (se 2 (by rfl) ⟨251835, by rfl⟩ : syracuseStep 671561 = 503671) B503671
theorem B376751 : Blo 295830 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B999431 : Blo 295830 999431 := bstep (se 1 (by rfl) ⟨749573, by rfl⟩ : syracuseStep 999431 = 1499147) B1499147
theorem B999539 : Blo 295830 999539 := bstep (se 1 (by rfl) ⟨749654, by rfl⟩ : syracuseStep 999539 = 1499309) B1499309
theorem B3850355 : Blo 295830 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B999809 : Blo 295830 999809 := bstep (se 2 (by rfl) ⟨374928, by rfl⟩ : syracuseStep 999809 = 749857) B749857
theorem B672353 : Blo 295830 672353 := bstep (se 2 (by rfl) ⟨252132, by rfl⟩ : syracuseStep 672353 = 504265) B504265
theorem B1688273 : Blo 295830 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B672695 : Blo 295830 672695 := bstep (se 1 (by rfl) ⟨504521, by rfl⟩ : syracuseStep 672695 = 1009043) B1009043
theorem B1917917 : Blo 295830 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B640057 : Blo 295830 640057 := bstep (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) B480043
theorem B2147447 : Blo 295830 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B3327095 : Blo 295830 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1000619 : Blo 295830 1000619 := bstep (se 1 (by rfl) ⟨750464, by rfl⟩ : syracuseStep 1000619 = 1500929) B1500929
theorem B2540747 : Blo 295830 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B443753 : Blo 295830 443753 := bstep (se 2 (by rfl) ⟨166407, by rfl⟩ : syracuseStep 443753 = 332815) B332815
theorem B1688957 : Blo 295830 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B3229091 : Blo 295830 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B443831 : Blo 295830 443831 := bstep (se 1 (by rfl) ⟨332873, by rfl⟩ : syracuseStep 443831 = 665747) B665747
theorem B1066459 : Blo 295830 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B443867 : Blo 295830 443867 := bstep (se 1 (by rfl) ⟨332900, by rfl⟩ : syracuseStep 443867 = 665801) B665801
theorem B673289 : Blo 295830 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B2868797 : Blo 295830 2868797 := bstep (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) B1075799
theorem B1001159 : Blo 295830 1001159 := bstep (se 1 (by rfl) ⟨750869, by rfl⟩ : syracuseStep 1001159 = 1501739) B1501739
theorem B804601 : Blo 295830 804601 := bstep (se 2 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 804601 = 603451) B603451
theorem B3622751 : Blo 295830 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B673631 : Blo 295830 673631 := bstep (se 1 (by rfl) ⟨505223, by rfl⟩ : syracuseStep 673631 = 1010447) B1010447
theorem B444335 : Blo 295830 444335 := bstep (se 1 (by rfl) ⟨333251, by rfl⟩ : syracuseStep 444335 = 666503) B666503
theorem B444425 : Blo 295830 444425 := bstep (se 2 (by rfl) ⟨166659, by rfl⟩ : syracuseStep 444425 = 333319) B333319
theorem B1918991 : Blo 295830 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B968723 : Blo 295830 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B673811 : Blo 295830 673811 := bstep (se 1 (by rfl) ⟨505358, by rfl⟩ : syracuseStep 673811 = 1010717) B1010717
theorem B444455 : Blo 295830 444455 := bstep (se 1 (by rfl) ⟨333341, by rfl⟩ : syracuseStep 444455 = 666683) B666683
theorem B444539 : Blo 295830 444539 := bstep (se 1 (by rfl) ⟨333404, by rfl⟩ : syracuseStep 444539 = 666809) B666809
theorem B444665 : Blo 295830 444665 := bstep (se 2 (by rfl) ⟨166749, by rfl⟩ : syracuseStep 444665 = 333499) B333499
theorem B444767 : Blo 295830 444767 := bstep (se 1 (by rfl) ⟨333575, by rfl⟩ : syracuseStep 444767 = 667151) B667151
theorem B674153 : Blo 295830 674153 := bstep (se 2 (by rfl) ⟨252807, by rfl⟩ : syracuseStep 674153 = 505615) B505615
theorem B444779 : Blo 295830 444779 := bstep (se 1 (by rfl) ⟨333584, by rfl⟩ : syracuseStep 444779 = 667169) B667169
theorem B1002023 : Blo 295830 1002023 := bstep (se 1 (by rfl) ⟨751517, by rfl⟩ : syracuseStep 1002023 = 1503035) B1503035
theorem B445007 : Blo 295830 445007 := bstep (se 1 (by rfl) ⟨333755, by rfl⟩ : syracuseStep 445007 = 667511) B667511
theorem B1002131 : Blo 295830 1002131 := bstep (se 1 (by rfl) ⟨751598, by rfl⟩ : syracuseStep 1002131 = 1503197) B1503197
theorem B2149037 : Blo 295830 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B445127 : Blo 295830 445127 := bstep (se 1 (by rfl) ⟨333845, by rfl⟩ : syracuseStep 445127 = 667691) B667691
theorem B445289 : Blo 295830 445289 := bstep (se 2 (by rfl) ⟨166983, by rfl⟩ : syracuseStep 445289 = 333967) B333967
theorem B478057 : Blo 295830 478057 := bstep (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) B358543
theorem B1002347 : Blo 295830 1002347 := bstep (se 1 (by rfl) ⟨751760, by rfl⟩ : syracuseStep 1002347 = 1503521) B1503521
theorem B1002401 : Blo 295830 1002401 := bstep (se 2 (by rfl) ⟨375900, by rfl⟩ : syracuseStep 1002401 = 751801) B751801
theorem B1133473 : Blo 295830 1133473 := bstep (se 2 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 1133473 = 850105) B850105
theorem B445367 : Blo 295830 445367 := bstep (se 1 (by rfl) ⟨334025, by rfl⟩ : syracuseStep 445367 = 668051) B668051
theorem B445403 : Blo 295830 445403 := bstep (se 1 (by rfl) ⟨334052, by rfl⟩ : syracuseStep 445403 = 668105) B668105
theorem B11455505 : Blo 295830 11455505 := bstep (se 2 (by rfl) ⟨4295814, by rfl⟩ : syracuseStep 11455505 = 8591629) B8591629
theorem B445871 : Blo 295830 445871 := bstep (se 1 (by rfl) ⟨334403, by rfl⟩ : syracuseStep 445871 = 668807) B668807
theorem B1002995 : Blo 295830 1002995 := bstep (se 1 (by rfl) ⟨752246, by rfl⟩ : syracuseStep 1002995 = 1504493) B1504493
theorem B445961 : Blo 295830 445961 := bstep (se 2 (by rfl) ⟨167235, by rfl⟩ : syracuseStep 445961 = 334471) B334471
theorem B445991 : Blo 295830 445991 := bstep (se 1 (by rfl) ⟨334493, by rfl⟩ : syracuseStep 445991 = 668987) B668987
theorem B2444897 : Blo 295830 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B446075 : Blo 295830 446075 := bstep (se 1 (by rfl) ⟨334556, by rfl⟩ : syracuseStep 446075 = 669113) B669113
theorem B446201 : Blo 295830 446201 := bstep (se 2 (by rfl) ⟨167325, by rfl⟩ : syracuseStep 446201 = 334651) B334651
theorem B446303 : Blo 295830 446303 := bstep (se 1 (by rfl) ⟨334727, by rfl⟩ : syracuseStep 446303 = 669455) B669455
theorem B1134431 : Blo 295830 1134431 := bstep (se 1 (by rfl) ⟨850823, by rfl⟩ : syracuseStep 1134431 = 1701647) B1701647
theorem B446315 : Blo 295830 446315 := bstep (se 1 (by rfl) ⟨334736, by rfl⟩ : syracuseStep 446315 = 669473) B669473
theorem B1134445 : Blo 295830 1134445 := bstep (se 3 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 1134445 = 425417) B425417
theorem B1068983 : Blo 295830 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B3821579 : Blo 295830 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B1003535 : Blo 295830 1003535 := bstep (se 1 (by rfl) ⟨752651, by rfl⟩ : syracuseStep 1003535 = 1505303) B1505303
theorem B446543 : Blo 295830 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B1134749 : Blo 295830 1134749 := bstep (se 3 (by rfl) ⟨212765, by rfl⟩ : syracuseStep 1134749 = 425531) B425531
theorem B446663 : Blo 295830 446663 := bstep (se 1 (by rfl) ⟨334997, by rfl⟩ : syracuseStep 446663 = 669995) B669995
theorem B446825 : Blo 295830 446825 := bstep (se 2 (by rfl) ⟨167559, by rfl⟩ : syracuseStep 446825 = 335119) B335119
theorem B446903 : Blo 295830 446903 := bstep (se 1 (by rfl) ⟨335177, by rfl⟩ : syracuseStep 446903 = 670355) B670355
theorem B446939 : Blo 295830 446939 := bstep (se 1 (by rfl) ⟨335204, by rfl⟩ : syracuseStep 446939 = 670409) B670409
theorem B1004129 : Blo 295830 1004129 := bstep (se 2 (by rfl) ⟨376548, by rfl⟩ : syracuseStep 1004129 = 753097) B753097
theorem B676475 : Blo 295830 676475 := bstep (se 1 (by rfl) ⟨507356, by rfl⟩ : syracuseStep 676475 = 1014713) B1014713
theorem B1135403 : Blo 295830 1135403 := bstep (se 1 (by rfl) ⟨851552, by rfl⟩ : syracuseStep 1135403 = 1703105) B1703105
theorem B1069919 : Blo 295830 1069919 := bstep (se 1 (by rfl) ⟨802439, by rfl⟩ : syracuseStep 1069919 = 1604879) B1604879
theorem B480107 : Blo 295830 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B447407 : Blo 295830 447407 := bstep (se 1 (by rfl) ⟨335555, by rfl⟩ : syracuseStep 447407 = 671111) B671111
theorem B2249693 : Blo 295830 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B447497 : Blo 295830 447497 := bstep (se 2 (by rfl) ⟨167811, by rfl⟩ : syracuseStep 447497 = 335623) B335623
theorem B447527 : Blo 295830 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B447611 : Blo 295830 447611 := bstep (se 1 (by rfl) ⟨335708, by rfl⟩ : syracuseStep 447611 = 671417) B671417
theorem B7623881 : Blo 295830 7623881 := bstep (se 2 (by rfl) ⟨2858955, by rfl⟩ : syracuseStep 7623881 = 5717911) B5717911
theorem B447737 : Blo 295830 447737 := bstep (se 2 (by rfl) ⟨167901, by rfl⟩ : syracuseStep 447737 = 335803) B335803
theorem B447839 : Blo 295830 447839 := bstep (se 1 (by rfl) ⟨335879, by rfl⟩ : syracuseStep 447839 = 671759) B671759
theorem B447851 : Blo 295830 447851 := bstep (se 1 (by rfl) ⟨335888, by rfl⟩ : syracuseStep 447851 = 671777) B671777
theorem B808321 : Blo 295830 808321 := bstep (se 2 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 808321 = 606241) B606241
theorem B1267163 : Blo 295830 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B2151947 : Blo 295830 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B448079 : Blo 295830 448079 := bstep (se 1 (by rfl) ⟨336059, by rfl⟩ : syracuseStep 448079 = 672119) B672119
theorem B1693331 : Blo 295830 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B448199 : Blo 295830 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B448361 : Blo 295830 448361 := bstep (se 2 (by rfl) ⟨168135, by rfl⟩ : syracuseStep 448361 = 336271) B336271
theorem B743275 : Blo 295830 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B448439 : Blo 295830 448439 := bstep (se 1 (by rfl) ⟨336329, by rfl⟩ : syracuseStep 448439 = 672659) B672659
theorem B448475 : Blo 295830 448475 := bstep (se 1 (by rfl) ⟨336356, by rfl⟩ : syracuseStep 448475 = 672713) B672713
theorem B1005587 : Blo 295830 1005587 := bstep (se 1 (by rfl) ⟨754190, by rfl⟩ : syracuseStep 1005587 = 1508381) B1508381
theorem B4315193 : Blo 295830 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B4053149 : Blo 295830 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1005911 : Blo 295830 1005911 := bstep (se 1 (by rfl) ⟨754433, by rfl⟩ : syracuseStep 1005911 = 1508867) B1508867
theorem B448943 : Blo 295830 448943 := bstep (se 1 (by rfl) ⟨336707, by rfl⟩ : syracuseStep 448943 = 673415) B673415
theorem B449033 : Blo 295830 449033 := bstep (se 2 (by rfl) ⟨168387, by rfl⟩ : syracuseStep 449033 = 336775) B336775
theorem B449063 : Blo 295830 449063 := bstep (se 1 (by rfl) ⟨336797, by rfl⟩ : syracuseStep 449063 = 673595) B673595
theorem B449147 : Blo 295830 449147 := bstep (se 1 (by rfl) ⟨336860, by rfl⟩ : syracuseStep 449147 = 673721) B673721
theorem B1071751 : Blo 295830 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1137361 : Blo 295830 1137361 := bstep (se 2 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 1137361 = 853021) B853021
theorem B449273 : Blo 295830 449273 := bstep (se 2 (by rfl) ⟨168477, by rfl⟩ : syracuseStep 449273 = 336955) B336955
theorem B449375 : Blo 295830 449375 := bstep (se 1 (by rfl) ⟨337031, by rfl⟩ : syracuseStep 449375 = 674063) B674063
theorem B449387 : Blo 295830 449387 := bstep (se 1 (by rfl) ⟨337040, by rfl⟩ : syracuseStep 449387 = 674081) B674081
theorem B711607 : Blo 295830 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B1137665 : Blo 295830 1137665 := bstep (se 2 (by rfl) ⟨426624, by rfl⟩ : syracuseStep 1137665 = 853249) B853249
theorem B6151247 : Blo 295830 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B449615 : Blo 295830 449615 := bstep (se 1 (by rfl) ⟨337211, by rfl⟩ : syracuseStep 449615 = 674423) B674423
theorem B449735 : Blo 295830 449735 := bstep (se 1 (by rfl) ⟨337301, by rfl⟩ : syracuseStep 449735 = 674603) B674603
theorem B1006991 : Blo 295830 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B2874797 : Blo 295830 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B1138121 : Blo 295830 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B1072673 : Blo 295830 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1498823 : Blo 295830 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B1007315 : Blo 295830 1007315 := bstep (se 1 (by rfl) ⟨755486, by rfl⟩ : syracuseStep 1007315 = 1510973) B1510973
theorem B2548097 : Blo 295830 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B909947 : Blo 295830 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B1434323 : Blo 295830 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B5104457 : Blo 295830 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B1008503 : Blo 295830 1008503 := bstep (se 1 (by rfl) ⟨756377, by rfl⟩ : syracuseStep 1008503 = 1512755) B1512755
theorem B1008719 : Blo 295830 1008719 := bstep (se 1 (by rfl) ⟨756539, by rfl⟩ : syracuseStep 1008719 = 1513079) B1513079
theorem B2417957 : Blo 295830 2417957 := bstep (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) B453367
theorem B5432741 : Blo 295830 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1009097 : Blo 295830 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B1009367 : Blo 295830 1009367 := bstep (se 1 (by rfl) ⟨757025, by rfl⟩ : syracuseStep 1009367 = 1514051) B1514051
theorem B1435553 : Blo 295830 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1009583 : Blo 295830 1009583 := bstep (se 1 (by rfl) ⟨757187, by rfl⟩ : syracuseStep 1009583 = 1514375) B1514375
theorem B714683 : Blo 295830 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B845903 : Blo 295830 845903 := bstep (se 1 (by rfl) ⟨634427, by rfl⟩ : syracuseStep 845903 = 1268855) B1268855
theorem B1141121 : Blo 295830 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B3795335 : Blo 295830 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B9693877 : Blo 295830 9693877 := bstep (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) B908801
theorem B846551 : Blo 295830 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B683407 : Blo 295830 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B7597637 : Blo 295830 7597637 := bstep (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) B1424557
theorem B355919 : Blo 295830 355919 := bstep (se 1 (by rfl) ⟨266939, by rfl⟩ : syracuseStep 355919 = 533879) B533879
theorem B6844121 : Blo 295830 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B4091681 : Blo 295830 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B1896311 : Blo 295830 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B683959 : Blo 295830 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1273913 : Blo 295830 1273913 := bstep (se 2 (by rfl) ⟨477717, by rfl⟩ : syracuseStep 1273913 = 955435) B955435
theorem B1438013 : Blo 295830 1438013 := bstep (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) B539255
theorem B881039 : Blo 295830 881039 := bstep (se 1 (by rfl) ⟨660779, by rfl⟩ : syracuseStep 881039 = 1321559) B1321559
theorem B1077907 : Blo 295830 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B1144169 : Blo 295830 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B750991 : Blo 295830 750991 := bstep (se 1 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 750991 = 1126487) B1126487
theorem B1504655 : Blo 295830 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B751315 : Blo 295830 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B1275911 : Blo 295830 1275911 := bstep (se 1 (by rfl) ⟨956933, by rfl⟩ : syracuseStep 1275911 = 1913867) B1913867
theorem B752267 : Blo 295830 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B1014601 : Blo 295830 1014601 := bstep (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) B760951
theorem B1080515 : Blo 295830 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B1506761 : Blo 295830 1506761 := bstep (se 2 (by rfl) ⟨565035, by rfl⟩ : syracuseStep 1506761 = 1130071) B1130071
theorem B753401 : Blo 295830 753401 := bstep (se 2 (by rfl) ⟨282525, by rfl⟩ : syracuseStep 753401 = 565051) B565051
theorem B2293571 : Blo 295830 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B2260871 : Blo 295830 2260871 := bstep (se 1 (by rfl) ⟨1695653, by rfl⟩ : syracuseStep 2260871 = 3391307) B3391307
theorem B2555783 : Blo 295830 2555783 := bstep (se 1 (by rfl) ⟨1916837, by rfl⟩ : syracuseStep 2555783 = 3833675) B3833675
theorem B753583 : Blo 295830 753583 := bstep (se 1 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 753583 = 1130375) B1130375
theorem B1278611 : Blo 295830 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B3834701 : Blo 295830 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B295835 : Blo 295830 295835 := bstep (se 1 (by rfl) ⟨221876, by rfl⟩ : syracuseStep 295835 = 443753) B443753
theorem B295887 : Blo 295830 295887 := bstep (se 1 (by rfl) ⟨221915, by rfl⟩ : syracuseStep 295887 = 443831) B443831
theorem B2884571 : Blo 295830 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B295911 : Blo 295830 295911 := bstep (se 1 (by rfl) ⟨221933, by rfl⟩ : syracuseStep 295911 = 443867) B443867
theorem B296223 : Blo 295830 296223 := bstep (se 1 (by rfl) ⟨222167, by rfl⟩ : syracuseStep 296223 = 444335) B444335
theorem B296283 : Blo 295830 296283 := bstep (se 1 (by rfl) ⟨222212, by rfl⟩ : syracuseStep 296283 = 444425) B444425
theorem B755041 : Blo 295830 755041 := bstep (se 2 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 755041 = 566281) B566281
theorem B1279327 : Blo 295830 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B296303 : Blo 295830 296303 := bstep (se 1 (by rfl) ⟨222227, by rfl⟩ : syracuseStep 296303 = 444455) B444455
theorem B918907 : Blo 295830 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B853409 : Blo 295830 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B296359 : Blo 295830 296359 := bstep (se 1 (by rfl) ⟨222269, by rfl⟩ : syracuseStep 296359 = 444539) B444539
theorem B296443 : Blo 295830 296443 := bstep (se 1 (by rfl) ⟨222332, by rfl⟩ : syracuseStep 296443 = 444665) B444665
theorem B296511 : Blo 295830 296511 := bstep (se 1 (by rfl) ⟨222383, by rfl⟩ : syracuseStep 296511 = 444767) B444767
theorem B296519 : Blo 295830 296519 := bstep (se 1 (by rfl) ⟨222389, by rfl⟩ : syracuseStep 296519 = 444779) B444779
theorem B296671 : Blo 295830 296671 := bstep (se 1 (by rfl) ⟨222503, by rfl⟩ : syracuseStep 296671 = 445007) B445007
theorem B296751 : Blo 295830 296751 := bstep (se 1 (by rfl) ⟨222563, by rfl⟩ : syracuseStep 296751 = 445127) B445127
theorem B296859 : Blo 295830 296859 := bstep (se 1 (by rfl) ⟨222644, by rfl⟩ : syracuseStep 296859 = 445289) B445289
theorem B296911 : Blo 295830 296911 := bstep (se 1 (by rfl) ⟨222683, by rfl⟩ : syracuseStep 296911 = 445367) B445367
theorem B1378255 : Blo 295830 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B296935 : Blo 295830 296935 := bstep (se 1 (by rfl) ⟨222701, by rfl⟩ : syracuseStep 296935 = 445403) B445403
theorem B7637003 : Blo 295830 7637003 := bstep (se 1 (by rfl) ⟨5727752, by rfl⟩ : syracuseStep 7637003 = 11455505) B11455505
theorem B5703695 : Blo 295830 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B755993 : Blo 295830 755993 := bstep (se 2 (by rfl) ⟨283497, by rfl⟩ : syracuseStep 755993 = 566995) B566995
theorem B1280285 : Blo 295830 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B297247 : Blo 295830 297247 := bstep (se 1 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 297247 = 445871) B445871
theorem B297307 : Blo 295830 297307 := bstep (se 1 (by rfl) ⟨222980, by rfl⟩ : syracuseStep 297307 = 445961) B445961
theorem B297327 : Blo 295830 297327 := bstep (se 1 (by rfl) ⟨222995, by rfl⟩ : syracuseStep 297327 = 445991) B445991
theorem B297383 : Blo 295830 297383 := bstep (se 1 (by rfl) ⟨223037, by rfl⟩ : syracuseStep 297383 = 446075) B446075
theorem B5507531 : Blo 295830 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B297467 : Blo 295830 297467 := bstep (se 1 (by rfl) ⟨223100, by rfl⟩ : syracuseStep 297467 = 446201) B446201
theorem B297535 : Blo 295830 297535 := bstep (se 1 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 297535 = 446303) B446303
theorem B756287 : Blo 295830 756287 := bstep (se 1 (by rfl) ⟨567215, by rfl⟩ : syracuseStep 756287 = 1134431) B1134431
theorem B297543 : Blo 295830 297543 := bstep (se 1 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 297543 = 446315) B446315
theorem B297695 : Blo 295830 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B1510163 : Blo 295830 1510163 := bstep (se 1 (by rfl) ⟨1132622, by rfl⟩ : syracuseStep 1510163 = 2265245) B2265245
theorem B756499 : Blo 295830 756499 := bstep (se 1 (by rfl) ⟨567374, by rfl⟩ : syracuseStep 756499 = 1134749) B1134749
theorem B297775 : Blo 295830 297775 := bstep (se 1 (by rfl) ⟨223331, by rfl⟩ : syracuseStep 297775 = 446663) B446663
theorem B297883 : Blo 295830 297883 := bstep (se 1 (by rfl) ⟨223412, by rfl⟩ : syracuseStep 297883 = 446825) B446825
theorem B297935 : Blo 295830 297935 := bstep (se 1 (by rfl) ⟨223451, by rfl⟩ : syracuseStep 297935 = 446903) B446903
theorem B297959 : Blo 295830 297959 := bstep (se 1 (by rfl) ⟨223469, by rfl⟩ : syracuseStep 297959 = 446939) B446939
theorem B756935 : Blo 295830 756935 := bstep (se 1 (by rfl) ⟨567701, by rfl⟩ : syracuseStep 756935 = 1135403) B1135403
theorem B1707227 : Blo 295830 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B756985 : Blo 295830 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B298271 : Blo 295830 298271 := bstep (se 1 (by rfl) ⟨223703, by rfl⟩ : syracuseStep 298271 = 447407) B447407
theorem B298331 : Blo 295830 298331 := bstep (se 1 (by rfl) ⟨223748, by rfl⟩ : syracuseStep 298331 = 447497) B447497
theorem B298351 : Blo 295830 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B298407 : Blo 295830 298407 := bstep (se 1 (by rfl) ⟨223805, by rfl⟩ : syracuseStep 298407 = 447611) B447611
theorem B5082587 : Blo 295830 5082587 := bstep (se 1 (by rfl) ⟨3811940, by rfl⟩ : syracuseStep 5082587 = 7623881) B7623881
theorem B298491 : Blo 295830 298491 := bstep (se 1 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 298491 = 447737) B447737
theorem B298559 : Blo 295830 298559 := bstep (se 1 (by rfl) ⟨223919, by rfl⟩ : syracuseStep 298559 = 447839) B447839
theorem B298567 : Blo 295830 298567 := bstep (se 1 (by rfl) ⟨223925, by rfl⟩ : syracuseStep 298567 = 447851) B447851
theorem B298719 : Blo 295830 298719 := bstep (se 1 (by rfl) ⟨224039, by rfl⟩ : syracuseStep 298719 = 448079) B448079
theorem B298799 : Blo 295830 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B1511297 : Blo 295830 1511297 := bstep (se 2 (by rfl) ⟨566736, by rfl⟩ : syracuseStep 1511297 = 1133473) B1133473
theorem B757633 : Blo 295830 757633 := bstep (se 2 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 757633 = 568225) B568225
theorem B298907 : Blo 295830 298907 := bstep (se 1 (by rfl) ⟨224180, by rfl⟩ : syracuseStep 298907 = 448361) B448361
theorem B298959 : Blo 295830 298959 := bstep (se 1 (by rfl) ⟨224219, by rfl⟩ : syracuseStep 298959 = 448439) B448439
theorem B298983 : Blo 295830 298983 := bstep (se 1 (by rfl) ⟨224237, by rfl⟩ : syracuseStep 298983 = 448475) B448475
theorem B6426773 : Blo 295830 6426773 := bstep (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) B301255
theorem B2560157 : Blo 295830 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B299295 : Blo 295830 299295 := bstep (se 1 (by rfl) ⟨224471, by rfl⟩ : syracuseStep 299295 = 448943) B448943
theorem B299355 : Blo 295830 299355 := bstep (se 1 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 299355 = 449033) B449033
theorem B299375 : Blo 295830 299375 := bstep (se 1 (by rfl) ⟨224531, by rfl⟩ : syracuseStep 299375 = 449063) B449063
theorem B299431 : Blo 295830 299431 := bstep (se 1 (by rfl) ⟨224573, by rfl⟩ : syracuseStep 299431 = 449147) B449147
theorem B299515 : Blo 295830 299515 := bstep (se 1 (by rfl) ⟨224636, by rfl⟩ : syracuseStep 299515 = 449273) B449273
theorem B299583 : Blo 295830 299583 := bstep (se 1 (by rfl) ⟨224687, by rfl⟩ : syracuseStep 299583 = 449375) B449375
theorem B299591 : Blo 295830 299591 := bstep (se 1 (by rfl) ⟨224693, by rfl⟩ : syracuseStep 299591 = 449387) B449387
theorem B758393 : Blo 295830 758393 := bstep (se 2 (by rfl) ⟨284397, by rfl⟩ : syracuseStep 758393 = 568795) B568795
theorem B1512107 : Blo 295830 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B758443 : Blo 295830 758443 := bstep (se 1 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 758443 = 1137665) B1137665
theorem B4100831 : Blo 295830 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B299743 : Blo 295830 299743 := bstep (se 1 (by rfl) ⟨224807, by rfl⟩ : syracuseStep 299743 = 449615) B449615
theorem B299823 : Blo 295830 299823 := bstep (se 1 (by rfl) ⟨224867, by rfl⟩ : syracuseStep 299823 = 449735) B449735
theorem B758747 : Blo 295830 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B1512593 : Blo 295830 1512593 := bstep (se 2 (by rfl) ⟨567222, by rfl⟩ : syracuseStep 1512593 = 1134445) B1134445
theorem B2069761 : Blo 295830 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1152569 : Blo 295830 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B5117579 : Blo 295830 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B333535 : Blo 295830 333535 := bstep (se 1 (by rfl) ⟨250151, by rfl⟩ : syracuseStep 333535 = 500303) B500303
theorem B956215 : Blo 295830 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B11376773 : Blo 295830 11376773 := bstep (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) B2133145
theorem B1611971 : Blo 295830 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B1612061 : Blo 295830 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B334111 : Blo 295830 334111 := bstep (se 1 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 334111 = 501167) B501167
theorem B334399 : Blo 295830 334399 := bstep (se 1 (by rfl) ⟨250799, by rfl⟩ : syracuseStep 334399 = 501599) B501599
theorem B1710665 : Blo 295830 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B957035 : Blo 295830 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B3414635 : Blo 295830 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B563935 : Blo 295830 563935 := bstep (se 1 (by rfl) ⟨422951, by rfl⟩ : syracuseStep 563935 = 845903) B845903
theorem B4266755 : Blo 295830 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B11606819 : Blo 295830 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B760747 : Blo 295830 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B2530223 : Blo 295830 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B21437459 : Blo 295830 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B335227 : Blo 295830 335227 := bstep (se 1 (by rfl) ⟨251420, by rfl⟩ : syracuseStep 335227 = 502841) B502841
theorem B3644837 : Blo 295830 3644837 := bstep (se 4 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 3644837 = 683407) B683407
theorem B1515023 : Blo 295830 1515023 := bstep (se 1 (by rfl) ⟨1136267, by rfl⟩ : syracuseStep 1515023 = 2272535) B2272535
theorem B499513 : Blo 295830 499513 := bstep (se 2 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 499513 = 374635) B374635
theorem B991033 : Blo 295830 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B4562747 : Blo 295830 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B401231 : Blo 295830 401231 := bstep (se 1 (by rfl) ⟨300923, by rfl⟩ : syracuseStep 401231 = 601847) B601847
theorem B335695 : Blo 295830 335695 := bstep (se 1 (by rfl) ⟨251771, by rfl⟩ : syracuseStep 335695 = 503543) B503543
theorem B499817 : Blo 295830 499817 := bstep (se 2 (by rfl) ⟨187431, by rfl⟩ : syracuseStep 499817 = 374863) B374863
theorem B4301009 : Blo 295830 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B336091 : Blo 295830 336091 := bstep (se 1 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 336091 = 504137) B504137
theorem B1515995 : Blo 295830 1515995 := bstep (se 1 (by rfl) ⟨1136996, by rfl⟩ : syracuseStep 1515995 = 2273993) B2273993
theorem B336379 : Blo 295830 336379 := bstep (se 1 (by rfl) ⟨252284, by rfl⟩ : syracuseStep 336379 = 504569) B504569
theorem B336559 : Blo 295830 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B762779 : Blo 295830 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B3089335 : Blo 295830 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1516481 : Blo 295830 1516481 := bstep (se 2 (by rfl) ⟨568680, by rfl⟩ : syracuseStep 1516481 = 1137361) B1137361
theorem B1123267 : Blo 295830 1123267 := bstep (se 1 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 1123267 = 1684901) B1684901
theorem B336847 : Blo 295830 336847 := bstep (se 1 (by rfl) ⟨252635, by rfl⟩ : syracuseStep 336847 = 505271) B505271
theorem B1352801 : Blo 295830 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B1123571 : Blo 295830 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B337243 : Blo 295830 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B501241 : Blo 295830 501241 := bstep (se 2 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 501241 = 375931) B375931
theorem B632377 : Blo 295830 632377 := bstep (se 2 (by rfl) ⟨237141, by rfl⟩ : syracuseStep 632377 = 474283) B474283
theorem B1124027 : Blo 295830 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B501511 : Blo 295830 501511 := bstep (se 1 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 501511 = 752267) B752267
theorem B501545 : Blo 295830 501545 := bstep (se 2 (by rfl) ⟨188079, by rfl⟩ : syracuseStep 501545 = 376159) B376159
theorem B665963 : Blo 295830 665963 := bstep (se 1 (by rfl) ⟨499472, by rfl⟩ : syracuseStep 665963 = 998945) B998945
theorem B666107 : Blo 295830 666107 := bstep (se 1 (by rfl) ⟨499580, by rfl⟩ : syracuseStep 666107 = 999161) B999161
theorem B502267 : Blo 295830 502267 := bstep (se 1 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 502267 = 753401) B753401
theorem B666233 : Blo 295830 666233 := bstep (se 2 (by rfl) ⟨249837, by rfl⟩ : syracuseStep 666233 = 499675) B499675
theorem B666287 : Blo 295830 666287 := bstep (se 1 (by rfl) ⟨499715, by rfl⟩ : syracuseStep 666287 = 999431) B999431
theorem B666359 : Blo 295830 666359 := bstep (se 1 (by rfl) ⟨499769, by rfl⟩ : syracuseStep 666359 = 999539) B999539
theorem B2566903 : Blo 295830 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B1813271 : Blo 295830 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B666539 : Blo 295830 666539 := bstep (se 1 (by rfl) ⟨499904, by rfl⟩ : syracuseStep 666539 = 999809) B999809
theorem B502699 : Blo 295830 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B1125515 : Blo 295830 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B503003 : Blo 295830 503003 := bstep (se 1 (by rfl) ⟨377252, by rfl⟩ : syracuseStep 503003 = 754505) B754505
theorem B306599 : Blo 295830 306599 := bstep (se 1 (by rfl) ⟨229949, by rfl⟩ : syracuseStep 306599 = 459899) B459899
theorem B667079 : Blo 295830 667079 := bstep (se 1 (by rfl) ⟨500309, by rfl⟩ : syracuseStep 667079 = 1000619) B1000619
theorem B503239 : Blo 295830 503239 := bstep (se 1 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 503239 = 754859) B754859
theorem B1125971 : Blo 295830 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B667439 : Blo 295830 667439 := bstep (se 1 (by rfl) ⟨500579, by rfl⟩ : syracuseStep 667439 = 1001159) B1001159
theorem B503759 : Blo 295830 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B668015 : Blo 295830 668015 := bstep (se 1 (by rfl) ⟨501011, by rfl⟩ : syracuseStep 668015 = 1002023) B1002023
theorem B668087 : Blo 295830 668087 := bstep (se 1 (by rfl) ⟨501065, by rfl⟩ : syracuseStep 668087 = 1002131) B1002131
theorem B668231 : Blo 295830 668231 := bstep (se 1 (by rfl) ⟨501173, by rfl⟩ : syracuseStep 668231 = 1002347) B1002347
theorem B668267 : Blo 295830 668267 := bstep (se 1 (by rfl) ⟨501200, by rfl⟩ : syracuseStep 668267 = 1002401) B1002401
theorem B504427 : Blo 295830 504427 := bstep (se 1 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 504427 = 756641) B756641
theorem B1421945 : Blo 295830 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B635563 : Blo 295830 635563 := bstep (se 1 (by rfl) ⟨476672, by rfl⟩ : syracuseStep 635563 = 953345) B953345
theorem B504731 : Blo 295830 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B668663 : Blo 295830 668663 := bstep (se 1 (by rfl) ⟨501497, by rfl⟩ : syracuseStep 668663 = 1002995) B1002995
theorem B963833 : Blo 295830 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B669023 : Blo 295830 669023 := bstep (se 1 (by rfl) ⟨501767, by rfl⟩ : syracuseStep 669023 = 1003535) B1003535
theorem B669419 : Blo 295830 669419 := bstep (se 1 (by rfl) ⟨502064, by rfl⟩ : syracuseStep 669419 = 1004129) B1004129
theorem B669545 : Blo 295830 669545 := bstep (se 2 (by rfl) ⟨251079, by rfl⟩ : syracuseStep 669545 = 502159) B502159
theorem B12925169 : Blo 295830 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B375131 : Blo 295830 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B1128887 : Blo 295830 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B637409 : Blo 295830 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B670391 : Blo 295830 670391 := bstep (se 1 (by rfl) ⟨502793, by rfl⟩ : syracuseStep 670391 = 1005587) B1005587
theorem B2702099 : Blo 295830 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B375607 : Blo 295830 375607 := bstep (se 1 (by rfl) ⟨281705, by rfl⟩ : syracuseStep 375607 = 563411) B563411
theorem B7650125 : Blo 295830 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B670607 : Blo 295830 670607 := bstep (se 1 (by rfl) ⟨502955, by rfl⟩ : syracuseStep 670607 = 1005911) B1005911
theorem B376103 : Blo 295830 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B671327 : Blo 295830 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B376427 : Blo 295830 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B1916531 : Blo 295830 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B999215 : Blo 295830 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B671543 : Blo 295830 671543 := bstep (se 1 (by rfl) ⟨503657, by rfl⟩ : syracuseStep 671543 = 1007315) B1007315
theorem B376807 : Blo 295830 376807 := bstep (se 1 (by rfl) ⟨282605, by rfl⟩ : syracuseStep 376807 = 565211) B565211
theorem B671849 : Blo 295830 671849 := bstep (se 2 (by rfl) ⟨251943, by rfl⟩ : syracuseStep 671849 = 503887) B503887
theorem B606631 : Blo 295830 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B672335 : Blo 295830 672335 := bstep (se 1 (by rfl) ⟨504251, by rfl⟩ : syracuseStep 672335 = 1008503) B1008503
theorem B672479 : Blo 295830 672479 := bstep (se 1 (by rfl) ⟨504359, by rfl⟩ : syracuseStep 672479 = 1008719) B1008719
theorem B3621827 : Blo 295830 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B672731 : Blo 295830 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B410729 : Blo 295830 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B672911 : Blo 295830 672911 := bstep (se 1 (by rfl) ⟨504683, by rfl⟩ : syracuseStep 672911 = 1009367) B1009367
theorem B673001 : Blo 295830 673001 := bstep (se 2 (by rfl) ⟨252375, by rfl⟩ : syracuseStep 673001 = 504751) B504751
theorem B673055 : Blo 295830 673055 := bstep (se 1 (by rfl) ⟨504791, by rfl⟩ : syracuseStep 673055 = 1009583) B1009583
theorem B476455 : Blo 295830 476455 := bstep (se 1 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 476455 = 714683) B714683
theorem B443771 : Blo 295830 443771 := bstep (se 1 (by rfl) ⟨332828, by rfl⟩ : syracuseStep 443771 = 665657) B665657
theorem B443897 : Blo 295830 443897 := bstep (se 2 (by rfl) ⟨166461, by rfl⟩ : syracuseStep 443897 = 332923) B332923
theorem B443999 : Blo 295830 443999 := bstep (se 1 (by rfl) ⟨332999, by rfl⟩ : syracuseStep 443999 = 665999) B665999
theorem B673577 : Blo 295830 673577 := bstep (se 2 (by rfl) ⟨252591, by rfl⟩ : syracuseStep 673577 = 505183) B505183
theorem B444215 : Blo 295830 444215 := bstep (se 1 (by rfl) ⟨333161, by rfl⟩ : syracuseStep 444215 = 666323) B666323
theorem B1001321 : Blo 295830 1001321 := bstep (se 2 (by rfl) ⟨375495, by rfl⟩ : syracuseStep 1001321 = 750991) B750991
theorem B444521 : Blo 295830 444521 := bstep (se 2 (by rfl) ⟨166695, by rfl⟩ : syracuseStep 444521 = 333391) B333391
theorem B1001753 : Blo 295830 1001753 := bstep (se 2 (by rfl) ⟨375657, by rfl⟩ : syracuseStep 1001753 = 751315) B751315
theorem B1296751 : Blo 295830 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B5065091 : Blo 295830 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B444839 : Blo 295830 444839 := bstep (se 1 (by rfl) ⟨333629, by rfl⟩ : syracuseStep 444839 = 667259) B667259
theorem B444923 : Blo 295830 444923 := bstep (se 1 (by rfl) ⟨333692, by rfl⟩ : syracuseStep 444923 = 667385) B667385
theorem B1264207 : Blo 295830 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B445049 : Blo 295830 445049 := bstep (se 2 (by rfl) ⟨166893, by rfl⟩ : syracuseStep 445049 = 333787) B333787
theorem B445103 : Blo 295830 445103 := bstep (se 1 (by rfl) ⟨333827, by rfl⟩ : syracuseStep 445103 = 667655) B667655
theorem B445151 : Blo 295830 445151 := bstep (se 1 (by rfl) ⟨333863, by rfl⟩ : syracuseStep 445151 = 667727) B667727
theorem B445415 : Blo 295830 445415 := bstep (se 1 (by rfl) ⟨334061, by rfl⟩ : syracuseStep 445415 = 668123) B668123
theorem B445673 : Blo 295830 445673 := bstep (se 2 (by rfl) ⟨167127, by rfl⟩ : syracuseStep 445673 = 334255) B334255
theorem B445727 : Blo 295830 445727 := bstep (se 1 (by rfl) ⟨334295, by rfl⟩ : syracuseStep 445727 = 668591) B668591
theorem B445895 : Blo 295830 445895 := bstep (se 1 (by rfl) ⟨334421, by rfl⟩ : syracuseStep 445895 = 668843) B668843
theorem B1429001 : Blo 295830 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1003103 : Blo 295830 1003103 := bstep (se 1 (by rfl) ⟨752327, by rfl⟩ : syracuseStep 1003103 = 1504655) B1504655
theorem B446249 : Blo 295830 446249 := bstep (se 2 (by rfl) ⟨167343, by rfl⟩ : syracuseStep 446249 = 334687) B334687
theorem B446255 : Blo 295830 446255 := bstep (se 1 (by rfl) ⟨334691, by rfl⟩ : syracuseStep 446255 = 669383) B669383
theorem B446729 : Blo 295830 446729 := bstep (se 2 (by rfl) ⟨167523, by rfl⟩ : syracuseStep 446729 = 335047) B335047
theorem B446831 : Blo 295830 446831 := bstep (se 1 (by rfl) ⟨335123, by rfl⟩ : syracuseStep 446831 = 670247) B670247
theorem B447047 : Blo 295830 447047 := bstep (se 1 (by rfl) ⟨335285, by rfl⟩ : syracuseStep 447047 = 670571) B670571
theorem B447083 : Blo 295830 447083 := bstep (se 1 (by rfl) ⟨335312, by rfl⟩ : syracuseStep 447083 = 670625) B670625
theorem B1364663 : Blo 295830 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B447311 : Blo 295830 447311 := bstep (se 1 (by rfl) ⟨335483, by rfl⟩ : syracuseStep 447311 = 670967) B670967
theorem B1004507 : Blo 295830 1004507 := bstep (se 1 (by rfl) ⟨753380, by rfl⟩ : syracuseStep 1004507 = 1506761) B1506761
theorem B11719685 : Blo 295830 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B8180747 : Blo 295830 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B1004669 : Blo 295830 1004669 := bstep (se 3 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 1004669 = 376751) B376751
theorem B1529047 : Blo 295830 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B447707 : Blo 295830 447707 := bstep (se 1 (by rfl) ⟨335780, by rfl⟩ : syracuseStep 447707 = 671561) B671561
theorem B1004777 : Blo 295830 1004777 := bstep (se 2 (by rfl) ⟨376791, by rfl⟩ : syracuseStep 1004777 = 753583) B753583
theorem B447881 : Blo 295830 447881 := bstep (se 2 (by rfl) ⟨167955, by rfl⟩ : syracuseStep 447881 = 335911) B335911
theorem B1004939 : Blo 295830 1004939 := bstep (se 1 (by rfl) ⟨753704, by rfl⟩ : syracuseStep 1004939 = 1507409) B1507409
theorem B448235 : Blo 295830 448235 := bstep (se 1 (by rfl) ⟨336176, by rfl⟩ : syracuseStep 448235 = 672353) B672353
theorem B1529705 : Blo 295830 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B448463 : Blo 295830 448463 := bstep (se 1 (by rfl) ⟨336347, by rfl⟩ : syracuseStep 448463 = 672695) B672695
theorem B1431631 : Blo 295830 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B2218063 : Blo 295830 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B1693831 : Blo 295830 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B2152727 : Blo 295830 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B448859 : Blo 295830 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B2415167 : Blo 295830 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B449087 : Blo 295830 449087 := bstep (se 1 (by rfl) ⟨336815, by rfl⟩ : syracuseStep 449087 = 673631) B673631
theorem B645815 : Blo 295830 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B449207 : Blo 295830 449207 := bstep (se 1 (by rfl) ⟨336905, by rfl⟩ : syracuseStep 449207 = 673811) B673811
theorem B1137347 : Blo 295830 1137347 := bstep (se 1 (by rfl) ⟨853010, by rfl⟩ : syracuseStep 1137347 = 1706021) B1706021
theorem B449435 : Blo 295830 449435 := bstep (se 1 (by rfl) ⟨337076, by rfl⟩ : syracuseStep 449435 = 674153) B674153
theorem B1432691 : Blo 295830 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1269179 : Blo 295830 1269179 := bstep (se 1 (by rfl) ⟨951884, by rfl⟩ : syracuseStep 1269179 = 1903769) B1903769
theorem B1072801 : Blo 295830 1072801 := bstep (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) B804601
theorem B1629931 : Blo 295830 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B712655 : Blo 295830 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B2547719 : Blo 295830 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B1007963 : Blo 295830 1007963 := bstep (se 1 (by rfl) ⟨755972, by rfl⟩ : syracuseStep 1007963 = 1511945) B1511945
theorem B450983 : Blo 295830 450983 := bstep (se 1 (by rfl) ⟨338237, by rfl⟩ : syracuseStep 450983 = 676475) B676475
theorem B713279 : Blo 295830 713279 := bstep (se 1 (by rfl) ⟨534959, by rfl⟩ : syracuseStep 713279 = 1069919) B1069919
theorem B1139321 : Blo 295830 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1499795 : Blo 295830 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B844775 : Blo 295830 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B1434631 : Blo 295830 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B2254067 : Blo 295830 2254067 := bstep (se 1 (by rfl) ⟨1690550, by rfl⟩ : syracuseStep 2254067 = 3381101) B3381101
theorem B1008935 : Blo 295830 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B681311 : Blo 295830 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B2876795 : Blo 295830 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B1500605 : Blo 295830 1500605 := bstep (se 3 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 1500605 = 562727) B562727
theorem B1271639 : Blo 295830 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B1009799 : Blo 295830 1009799 := bstep (se 1 (by rfl) ⟨757349, by rfl⟩ : syracuseStep 1009799 = 1514699) B1514699
theorem B6121763 : Blo 295830 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B715115 : Blo 295830 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B911945 : Blo 295830 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1698731 : Blo 295830 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B1272955 : Blo 295830 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B2256011 : Blo 295830 2256011 := bstep (se 1 (by rfl) ⟨1692008, by rfl⟩ : syracuseStep 2256011 = 3384017) B3384017
theorem B1272971 : Blo 295830 1272971 := bstep (se 1 (by rfl) ⟨954728, by rfl⟩ : syracuseStep 1272971 = 1909457) B1909457
theorem B3402971 : Blo 295830 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B1207619 : Blo 295830 1207619 := bstep (se 1 (by rfl) ⟨905714, by rfl⟩ : syracuseStep 1207619 = 1811429) B1811429
theorem B1011041 : Blo 295830 1011041 := bstep (se 2 (by rfl) ⟨379140, by rfl⟩ : syracuseStep 1011041 = 758281) B758281
theorem B454025 : Blo 295830 454025 := bstep (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) B340519
theorem B1437209 : Blo 295830 1437209 := bstep (se 2 (by rfl) ⟨538953, by rfl⟩ : syracuseStep 1437209 = 1077907) B1077907
theorem B1273553 : Blo 295830 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B2158289 : Blo 295830 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B356251 : Blo 295830 356251 := bstep (se 1 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 356251 = 534377) B534377
theorem B749999 : Blo 295830 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B1012193 : Blo 295830 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B1077761 : Blo 295830 1077761 := bstep (se 2 (by rfl) ⟨404160, by rfl⟩ : syracuseStep 1077761 = 808321) B808321
theorem B2257469 : Blo 295830 2257469 := bstep (se 3 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 2257469 = 846551) B846551
theorem B2880485 : Blo 295830 2880485 := bstep (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) B540091
theorem B1078397 : Blo 295830 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B2585945 : Blo 295830 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B750971 : Blo 295830 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B849275 : Blo 295830 849275 := bstep (se 1 (by rfl) ⟨636956, by rfl⟩ : syracuseStep 849275 = 1273913) B1273913
theorem B2848193 : Blo 295830 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B587359 : Blo 295830 587359 := bstep (se 1 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 587359 = 881039) B881039
theorem B751265 : Blo 295830 751265 := bstep (se 2 (by rfl) ⟨281724, by rfl⟩ : syracuseStep 751265 = 563449) B563449
theorem B5404715 : Blo 295830 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B1505465 : Blo 295830 1505465 := bstep (se 2 (by rfl) ⟨564549, by rfl⟩ : syracuseStep 1505465 = 1129099) B1129099
theorem B719113 : Blo 295830 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B751963 : Blo 295830 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B948809 : Blo 295830 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B850607 : Blo 295830 850607 := bstep (se 1 (by rfl) ⟨637955, by rfl⟩ : syracuseStep 850607 = 1275911) B1275911
theorem B949117 : Blo 295830 949117 := bstep (se 3 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 949117 = 355919) B355919
theorem B2259899 : Blo 295830 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B1146143 : Blo 295830 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B752935 : Blo 295830 752935 := bstep (se 1 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 752935 = 1129403) B1129403
theorem B10911149 : Blo 295830 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B720343 : Blo 295830 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B753209 : Blo 295830 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B1605379 : Blo 295830 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B1507247 : Blo 295830 1507247 := bstep (se 1 (by rfl) ⟨1130435, by rfl⟩ : syracuseStep 1507247 = 2260871) B2260871
theorem B1703855 : Blo 295830 1703855 := bstep (se 1 (by rfl) ⟨1277891, by rfl⟩ : syracuseStep 1703855 = 2555783) B2555783
theorem B852407 : Blo 295830 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B2556467 : Blo 295830 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B295847 : Blo 295830 295847 := bstep (se 1 (by rfl) ⟨221885, by rfl⟩ : syracuseStep 295847 = 443771) B443771
theorem B295931 : Blo 295830 295931 := bstep (se 1 (by rfl) ⟨221948, by rfl⟩ : syracuseStep 295931 = 443897) B443897
theorem B295999 : Blo 295830 295999 := bstep (se 1 (by rfl) ⟨221999, by rfl⟩ : syracuseStep 295999 = 443999) B443999
theorem B296143 : Blo 295830 296143 := bstep (se 1 (by rfl) ⟨222107, by rfl⟩ : syracuseStep 296143 = 444215) B444215
theorem B3802463 : Blo 295830 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B296347 : Blo 295830 296347 := bstep (se 1 (by rfl) ⟨222260, by rfl⟩ : syracuseStep 296347 = 444521) B444521
theorem B853523 : Blo 295830 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B3376727 : Blo 295830 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B296559 : Blo 295830 296559 := bstep (se 1 (by rfl) ⟨222419, by rfl⟩ : syracuseStep 296559 = 444839) B444839
theorem B3671687 : Blo 295830 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B296615 : Blo 295830 296615 := bstep (se 1 (by rfl) ⟨222461, by rfl⟩ : syracuseStep 296615 = 444923) B444923
theorem B296699 : Blo 295830 296699 := bstep (se 1 (by rfl) ⟨222524, by rfl⟩ : syracuseStep 296699 = 445049) B445049
theorem B296735 : Blo 295830 296735 := bstep (se 1 (by rfl) ⟨222551, by rfl⟩ : syracuseStep 296735 = 445103) B445103
theorem B1705769 : Blo 295830 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B296767 : Blo 295830 296767 := bstep (se 1 (by rfl) ⟨222575, by rfl⟩ : syracuseStep 296767 = 445151) B445151
theorem B296943 : Blo 295830 296943 := bstep (se 1 (by rfl) ⟨222707, by rfl⟩ : syracuseStep 296943 = 445415) B445415
theorem B297115 : Blo 295830 297115 := bstep (se 1 (by rfl) ⟨222836, by rfl⟩ : syracuseStep 297115 = 445673) B445673
theorem B297151 : Blo 295830 297151 := bstep (se 1 (by rfl) ⟨222863, by rfl⟩ : syracuseStep 297151 = 445727) B445727
theorem B297263 : Blo 295830 297263 := bstep (se 1 (by rfl) ⟨222947, by rfl⟩ : syracuseStep 297263 = 445895) B445895
theorem B952667 : Blo 295830 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B2034077 : Blo 295830 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B297499 : Blo 295830 297499 := bstep (se 1 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 297499 = 446249) B446249
theorem B297503 : Blo 295830 297503 := bstep (se 1 (by rfl) ⟨223127, by rfl⟩ : syracuseStep 297503 = 446255) B446255
theorem B1837673 : Blo 295830 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B1706771 : Blo 295830 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B297819 : Blo 295830 297819 := bstep (se 1 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 297819 = 446729) B446729
theorem B297887 : Blo 295830 297887 := bstep (se 1 (by rfl) ⟨223415, by rfl⟩ : syracuseStep 297887 = 446831) B446831
theorem B3607469 : Blo 295830 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B298031 : Blo 295830 298031 := bstep (se 1 (by rfl) ⟨223523, by rfl⟩ : syracuseStep 298031 = 447047) B447047
theorem B298055 : Blo 295830 298055 := bstep (se 1 (by rfl) ⟨223541, by rfl⟩ : syracuseStep 298055 = 447083) B447083
theorem B298207 : Blo 295830 298207 := bstep (se 1 (by rfl) ⟨223655, by rfl⟩ : syracuseStep 298207 = 447311) B447311
theorem B298471 : Blo 295830 298471 := bstep (se 1 (by rfl) ⟨223853, by rfl⟩ : syracuseStep 298471 = 447707) B447707
theorem B298587 : Blo 295830 298587 := bstep (se 1 (by rfl) ⟨223940, by rfl⟩ : syracuseStep 298587 = 447881) B447881
theorem B3411719 : Blo 295830 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B298823 : Blo 295830 298823 := bstep (se 1 (by rfl) ⟨224117, by rfl⟩ : syracuseStep 298823 = 448235) B448235
theorem B1019803 : Blo 295830 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B298975 : Blo 295830 298975 := bstep (se 1 (by rfl) ⟨224231, by rfl⟩ : syracuseStep 298975 = 448463) B448463
theorem B299239 : Blo 295830 299239 := bstep (se 1 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 299239 = 448859) B448859
theorem B1610111 : Blo 295830 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B299391 : Blo 295830 299391 := bstep (se 1 (by rfl) ⟨224543, by rfl⟩ : syracuseStep 299391 = 449087) B449087
theorem B430543 : Blo 295830 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B299471 : Blo 295830 299471 := bstep (se 1 (by rfl) ⟨224603, by rfl⟩ : syracuseStep 299471 = 449207) B449207
theorem B758231 : Blo 295830 758231 := bstep (se 1 (by rfl) ⟨568673, by rfl⟩ : syracuseStep 758231 = 1137347) B1137347
theorem B299623 : Blo 295830 299623 := bstep (se 1 (by rfl) ⟨224717, by rfl⟩ : syracuseStep 299623 = 449435) B449435
theorem B14291639 : Blo 295830 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B955127 : Blo 295830 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B2429891 : Blo 295830 2429891 := bstep (se 1 (by rfl) ⟨1822418, by rfl⟩ : syracuseStep 2429891 = 3644837) B3644837
theorem B333211 : Blo 295830 333211 := bstep (se 1 (by rfl) ⟨249908, by rfl⟩ : syracuseStep 333211 = 499817) B499817
theorem B300655 : Blo 295830 300655 := bstep (se 1 (by rfl) ⟨225491, by rfl⟩ : syracuseStep 300655 = 450983) B450983
theorem B759547 : Blo 295830 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B563183 : Blo 295830 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B1906973 : Blo 295830 1906973 := bstep (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) B715115
theorem B21142037 : Blo 295830 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B334363 : Blo 295830 334363 := bstep (se 1 (by rfl) ⟨250772, by rfl⟩ : syracuseStep 334363 = 501545) B501545
theorem B2431853 : Blo 295830 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2038729 : Blo 295830 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B2759681 : Blo 295830 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B335335 : Blo 295830 335335 := bstep (se 1 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 335335 = 503003) B503003
theorem B2268647 : Blo 295830 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B958139 : Blo 295830 958139 := bstep (se 1 (by rfl) ⟨718604, by rfl⟩ : syracuseStep 958139 = 1437209) B1437209
theorem B3841829 : Blo 295830 3841829 := bstep (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) B720343
theorem B335839 : Blo 295830 335839 := bstep (se 1 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 335839 = 503759) B503759
theorem B1908841 : Blo 295830 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B2957417 : Blo 295830 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B499999 : Blo 295830 499999 := bstep (se 1 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 499999 = 749999) B749999
theorem B958817 : Blo 295830 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B336487 : Blo 295830 336487 := bstep (se 1 (by rfl) ⟨252365, by rfl⟩ : syracuseStep 336487 = 504731) B504731
theorem B500647 : Blo 295830 500647 := bstep (se 1 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 500647 = 750971) B750971
theorem B566183 : Blo 295830 566183 := bstep (se 1 (by rfl) ⟨424637, by rfl⟩ : syracuseStep 566183 = 849275) B849275
theorem B500809 : Blo 295830 500809 := bstep (se 2 (by rfl) ⟨187803, by rfl⟩ : syracuseStep 500809 = 375607) B375607
theorem B500843 : Blo 295830 500843 := bstep (se 1 (by rfl) ⟨375632, by rfl⟩ : syracuseStep 500843 = 751265) B751265
theorem B632539 : Blo 295830 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B567071 : Blo 295830 567071 := bstep (se 1 (by rfl) ⟨425303, by rfl⟩ : syracuseStep 567071 = 850607) B850607
theorem B764095 : Blo 295830 764095 := bstep (se 1 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 764095 = 1146143) B1146143
theorem B2173241 : Blo 295830 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B2140505 : Blo 295830 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B502139 : Blo 295830 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B666017 : Blo 295830 666017 := bstep (se 2 (by rfl) ⟨249756, by rfl⟩ : syracuseStep 666017 = 499513) B499513
theorem B666143 : Blo 295830 666143 := bstep (se 1 (by rfl) ⟨499607, by rfl⟩ : syracuseStep 666143 = 999215) B999215
theorem B502409 : Blo 295830 502409 := bstep (se 2 (by rfl) ⟨188403, by rfl⟩ : syracuseStep 502409 = 376807) B376807
theorem B568939 : Blo 295830 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B667547 : Blo 295830 667547 := bstep (se 1 (by rfl) ⟨500660, by rfl⟩ : syracuseStep 667547 = 1001321) B1001321
theorem B5091335 : Blo 295830 5091335 := bstep (se 1 (by rfl) ⟨3818501, by rfl⟩ : syracuseStep 5091335 = 7637003) B7637003
theorem B1912841 : Blo 295830 1912841 := bstep (se 2 (by rfl) ⟨717315, by rfl⟩ : syracuseStep 1912841 = 1434631) B1434631
theorem B667835 : Blo 295830 667835 := bstep (se 1 (by rfl) ⟨500876, by rfl⟩ : syracuseStep 667835 = 1001753) B1001753
theorem B503995 : Blo 295830 503995 := bstep (se 1 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 503995 = 755993) B755993
theorem B504191 : Blo 295830 504191 := bstep (se 1 (by rfl) ⟨378143, by rfl⟩ : syracuseStep 504191 = 756287) B756287
theorem B635273 : Blo 295830 635273 := bstep (se 2 (by rfl) ⟨238227, by rfl⟩ : syracuseStep 635273 = 476455) B476455
theorem B668321 : Blo 295830 668321 := bstep (se 2 (by rfl) ⟨250620, by rfl⟩ : syracuseStep 668321 = 501241) B501241
theorem B504623 : Blo 295830 504623 := bstep (se 1 (by rfl) ⟨378467, by rfl⟩ : syracuseStep 504623 = 756935) B756935
theorem B3388391 : Blo 295830 3388391 := bstep (se 1 (by rfl) ⟨2541293, by rfl⟩ : syracuseStep 3388391 = 5082587) B5082587
theorem B668681 : Blo 295830 668681 := bstep (se 2 (by rfl) ⟨250755, by rfl⟩ : syracuseStep 668681 = 501511) B501511
theorem B668735 : Blo 295830 668735 := bstep (se 1 (by rfl) ⟨501551, by rfl⟩ : syracuseStep 668735 = 1003103) B1003103
theorem B1095277 : Blo 295830 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B505595 : Blo 295830 505595 := bstep (se 1 (by rfl) ⟨379196, by rfl⟩ : syracuseStep 505595 = 758393) B758393
theorem B2733887 : Blo 295830 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B669671 : Blo 295830 669671 := bstep (se 1 (by rfl) ⟨502253, by rfl⟩ : syracuseStep 669671 = 1004507) B1004507
theorem B505831 : Blo 295830 505831 := bstep (se 1 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 505831 = 758747) B758747
theorem B2570221 : Blo 295830 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B669689 : Blo 295830 669689 := bstep (se 2 (by rfl) ⟨251133, by rfl⟩ : syracuseStep 669689 = 502267) B502267
theorem B5453831 : Blo 295830 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B669779 : Blo 295830 669779 := bstep (se 1 (by rfl) ⟨502334, by rfl⟩ : syracuseStep 669779 = 1004669) B1004669
theorem B1685609 : Blo 295830 1685609 := bstep (se 2 (by rfl) ⟨632103, by rfl⟩ : syracuseStep 1685609 = 1264207) B1264207
theorem B669851 : Blo 295830 669851 := bstep (se 1 (by rfl) ⟨502388, by rfl⟩ : syracuseStep 669851 = 1004777) B1004777
theorem B6895853 : Blo 295830 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B1816829 : Blo 295830 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B669959 : Blo 295830 669959 := bstep (se 1 (by rfl) ⟨502469, by rfl⟩ : syracuseStep 669959 = 1004939) B1004939
theorem B3422537 : Blo 295830 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B768379 : Blo 295830 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B670265 : Blo 295830 670265 := bstep (se 2 (by rfl) ⟨251349, by rfl⟩ : syracuseStep 670265 = 502699) B502699
theorem B7584515 : Blo 295830 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B2276423 : Blo 295830 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B670985 : Blo 295830 670985 := bstep (se 2 (by rfl) ⟨251619, by rfl⟩ : syracuseStep 670985 = 503239) B503239
theorem B1686815 : Blo 295830 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B475001 : Blo 295830 475001 := bstep (se 2 (by rfl) ⟨178125, by rfl⟩ : syracuseStep 475001 = 356251) B356251
theorem B475103 : Blo 295830 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B2867339 : Blo 295830 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B671975 : Blo 295830 671975 := bstep (se 1 (by rfl) ⟨503981, by rfl⟩ : syracuseStep 671975 = 1007963) B1007963
theorem B475519 : Blo 295830 475519 := bstep (se 1 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 475519 = 713279) B713279
theorem B999863 : Blo 295830 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B672569 : Blo 295830 672569 := bstep (se 2 (by rfl) ⟨252213, by rfl⟩ : syracuseStep 672569 = 504427) B504427
theorem B672623 : Blo 295830 672623 := bstep (se 1 (by rfl) ⟨504467, by rfl⟩ : syracuseStep 672623 = 1008935) B1008935
theorem B1000349 : Blo 295830 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B1917863 : Blo 295830 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B1000403 : Blo 295830 1000403 := bstep (se 1 (by rfl) ⟨750302, by rfl⟩ : syracuseStep 1000403 = 1500605) B1500605
theorem B673199 : Blo 295830 673199 := bstep (se 1 (by rfl) ⟨504899, by rfl⟩ : syracuseStep 673199 = 1009799) B1009799
theorem B4081175 : Blo 295830 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B443975 : Blo 295830 443975 := bstep (se 1 (by rfl) ⟨332981, by rfl⟩ : syracuseStep 443975 = 665963) B665963
theorem B444071 : Blo 295830 444071 := bstep (se 1 (by rfl) ⟨333053, by rfl⟩ : syracuseStep 444071 = 666107) B666107
theorem B444155 : Blo 295830 444155 := bstep (se 1 (by rfl) ⟨333116, by rfl⟩ : syracuseStep 444155 = 666233) B666233
theorem B444191 : Blo 295830 444191 := bstep (se 1 (by rfl) ⟨333143, by rfl⟩ : syracuseStep 444191 = 666287) B666287
theorem B444239 : Blo 295830 444239 := bstep (se 1 (by rfl) ⟨333179, by rfl⟩ : syracuseStep 444239 = 666359) B666359
theorem B444359 : Blo 295830 444359 := bstep (se 1 (by rfl) ⟨333269, by rfl⟩ : syracuseStep 444359 = 666539) B666539
theorem B1132487 : Blo 295830 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B4900837 : Blo 295830 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B4835389 : Blo 295830 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B30951517 : Blo 295830 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B805079 : Blo 295830 805079 := bstep (se 1 (by rfl) ⟨603809, by rfl⟩ : syracuseStep 805079 = 1207619) B1207619
theorem B674027 : Blo 295830 674027 := bstep (se 1 (by rfl) ⟨505520, by rfl⟩ : syracuseStep 674027 = 1011041) B1011041
theorem B444713 : Blo 295830 444713 := bstep (se 2 (by rfl) ⟨166767, by rfl⟩ : syracuseStep 444713 = 333535) B333535
theorem B444719 : Blo 295830 444719 := bstep (se 1 (by rfl) ⟨333539, by rfl⟩ : syracuseStep 444719 = 667079) B667079
theorem B444959 : Blo 295830 444959 := bstep (se 1 (by rfl) ⟨333719, by rfl⟩ : syracuseStep 444959 = 667439) B667439
theorem B445343 : Blo 295830 445343 := bstep (se 1 (by rfl) ⟨334007, by rfl⟩ : syracuseStep 445343 = 668015) B668015
theorem B445391 : Blo 295830 445391 := bstep (se 1 (by rfl) ⟨334043, by rfl⟩ : syracuseStep 445391 = 668087) B668087
theorem B674795 : Blo 295830 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B445481 : Blo 295830 445481 := bstep (se 2 (by rfl) ⟨167055, by rfl⟩ : syracuseStep 445481 = 334111) B334111
theorem B445487 : Blo 295830 445487 := bstep (se 1 (by rfl) ⟨334115, by rfl⟩ : syracuseStep 445487 = 668231) B668231
theorem B445511 : Blo 295830 445511 := bstep (se 1 (by rfl) ⟨334133, by rfl⟩ : syracuseStep 445511 = 668267) B668267
theorem B1002617 : Blo 295830 1002617 := bstep (se 2 (by rfl) ⟨375981, by rfl⟩ : syracuseStep 1002617 = 751963) B751963
theorem B1920323 : Blo 295830 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B445775 : Blo 295830 445775 := bstep (se 1 (by rfl) ⟨334331, by rfl⟩ : syracuseStep 445775 = 668663) B668663
theorem B445865 : Blo 295830 445865 := bstep (se 2 (by rfl) ⟨167199, by rfl⟩ : syracuseStep 445865 = 334399) B334399
theorem B1002941 : Blo 295830 1002941 := bstep (se 3 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 1002941 = 376103) B376103
theorem B446015 : Blo 295830 446015 := bstep (se 1 (by rfl) ⟨334511, by rfl⟩ : syracuseStep 446015 = 669023) B669023
theorem B446279 : Blo 295830 446279 := bstep (se 1 (by rfl) ⟨334709, by rfl⟩ : syracuseStep 446279 = 669419) B669419
theorem B1265489 : Blo 295830 1265489 := bstep (se 2 (by rfl) ⟨474558, by rfl⟩ : syracuseStep 1265489 = 949117) B949117
theorem B446363 : Blo 295830 446363 := bstep (se 1 (by rfl) ⟨334772, by rfl⟩ : syracuseStep 446363 = 669545) B669545
theorem B1003643 : Blo 295830 1003643 := bstep (se 1 (by rfl) ⟨752732, by rfl⟩ : syracuseStep 1003643 = 1505465) B1505465
theorem B1003805 : Blo 295830 1003805 := bstep (se 3 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 1003805 = 376427) B376427
theorem B1003913 : Blo 295830 1003913 := bstep (se 2 (by rfl) ⟨376467, by rfl⟩ : syracuseStep 1003913 = 752935) B752935
theorem B446927 : Blo 295830 446927 := bstep (se 1 (by rfl) ⟨335195, by rfl⟩ : syracuseStep 446927 = 670391) B670391
theorem B446969 : Blo 295830 446969 := bstep (se 2 (by rfl) ⟨167613, by rfl⟩ : syracuseStep 446969 = 335227) B335227
theorem B5100083 : Blo 295830 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B447071 : Blo 295830 447071 := bstep (se 1 (by rfl) ⟨335303, by rfl⟩ : syracuseStep 447071 = 670607) B670607
theorem B1069949 : Blo 295830 1069949 := bstep (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) B401231
theorem B1430401 : Blo 295830 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B447551 : Blo 295830 447551 := bstep (se 1 (by rfl) ⟨335663, by rfl⟩ : syracuseStep 447551 = 671327) B671327
theorem B447593 : Blo 295830 447593 := bstep (se 2 (by rfl) ⟨167847, by rfl⟩ : syracuseStep 447593 = 335695) B335695
theorem B447695 : Blo 295830 447695 := bstep (se 1 (by rfl) ⟨335771, by rfl⟩ : syracuseStep 447695 = 671543) B671543
theorem B1004831 : Blo 295830 1004831 := bstep (se 1 (by rfl) ⟨753623, by rfl⟩ : syracuseStep 1004831 = 1507247) B1507247
theorem B1135903 : Blo 295830 1135903 := bstep (se 1 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 1135903 = 1703855) B1703855
theorem B447899 : Blo 295830 447899 := bstep (se 1 (by rfl) ⟨335924, by rfl⟩ : syracuseStep 447899 = 671849) B671849
theorem B448121 : Blo 295830 448121 := bstep (se 2 (by rfl) ⟨168045, by rfl⟩ : syracuseStep 448121 = 336091) B336091
theorem B448223 : Blo 295830 448223 := bstep (se 1 (by rfl) ⟨336167, by rfl⟩ : syracuseStep 448223 = 672335) B672335
theorem B448319 : Blo 295830 448319 := bstep (se 1 (by rfl) ⟨336239, by rfl⟩ : syracuseStep 448319 = 672479) B672479
theorem B808841 : Blo 295830 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B2414551 : Blo 295830 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B1923047 : Blo 295830 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B448487 : Blo 295830 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B448505 : Blo 295830 448505 := bstep (se 2 (by rfl) ⟨168189, by rfl⟩ : syracuseStep 448505 = 336379) B336379
theorem B448607 : Blo 295830 448607 := bstep (se 1 (by rfl) ⟨336455, by rfl⟩ : syracuseStep 448607 = 672911) B672911
theorem B448667 : Blo 295830 448667 := bstep (se 1 (by rfl) ⟨336500, by rfl⟩ : syracuseStep 448667 = 673001) B673001
theorem B448703 : Blo 295830 448703 := bstep (se 1 (by rfl) ⟨336527, by rfl⟩ : syracuseStep 448703 = 673055) B673055
theorem B448745 : Blo 295830 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B449051 : Blo 295830 449051 := bstep (se 1 (by rfl) ⟨336788, by rfl⟩ : syracuseStep 449051 = 673577) B673577
theorem B4119113 : Blo 295830 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1497689 : Blo 295830 1497689 := bstep (se 2 (by rfl) ⟨561633, by rfl⟩ : syracuseStep 1497689 = 1123267) B1123267
theorem B449129 : Blo 295830 449129 := bstep (se 2 (by rfl) ⟨168423, by rfl⟩ : syracuseStep 449129 = 336847) B336847
theorem B449657 : Blo 295830 449657 := bstep (se 2 (by rfl) ⟨168621, by rfl⟩ : syracuseStep 449657 = 337243) B337243
theorem B1006721 : Blo 295830 1006721 := bstep (se 2 (by rfl) ⟨377520, by rfl⟩ : syracuseStep 1006721 = 755041) B755041
theorem B1006775 : Blo 295830 1006775 := bstep (se 1 (by rfl) ⟨755081, by rfl⟩ : syracuseStep 1006775 = 1510163) B1510163
theorem B843169 : Blo 295830 843169 := bstep (se 2 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 843169 = 632377) B632377
theorem B1138151 : Blo 295830 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B1007531 : Blo 295830 1007531 := bstep (se 1 (by rfl) ⟨755648, by rfl⟩ : syracuseStep 1007531 = 1511297) B1511297
theorem B31252493 : Blo 295830 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B4284515 : Blo 295830 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1008071 : Blo 295830 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B909775 : Blo 295830 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B1729001 : Blo 295830 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B1008395 : Blo 295830 1008395 := bstep (se 1 (by rfl) ⟨756296, by rfl⟩ : syracuseStep 1008395 = 1512593) B1512593
theorem B1008665 : Blo 295830 1008665 := bstep (se 2 (by rfl) ⟨378249, by rfl⟩ : syracuseStep 1008665 = 756499) B756499
theorem B1074647 : Blo 295830 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B1697273 : Blo 295830 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B1435151 : Blo 295830 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B1074707 : Blo 295830 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B1009313 : Blo 295830 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B1140443 : Blo 295830 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B2844503 : Blo 295830 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B846119 : Blo 295830 846119 := bstep (se 1 (by rfl) ⟨634589, by rfl⟩ : syracuseStep 846119 = 1269179) B1269179
theorem B1010015 : Blo 295830 1010015 := bstep (se 1 (by rfl) ⟨757511, by rfl⟩ : syracuseStep 1010015 = 1515023) B1515023
theorem B1010177 : Blo 295830 1010177 := bstep (se 2 (by rfl) ⟨378816, by rfl⟩ : syracuseStep 1010177 = 757633) B757633
theorem B3041831 : Blo 295830 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B1698479 : Blo 295830 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1010663 : Blo 295830 1010663 := bstep (se 1 (by rfl) ⟨757997, by rfl⟩ : syracuseStep 1010663 = 1515995) B1515995
theorem B1010987 : Blo 295830 1010987 := bstep (se 1 (by rfl) ⟨758240, by rfl⟩ : syracuseStep 1010987 = 1516481) B1516481
theorem B749047 : Blo 295830 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B1502711 : Blo 295830 1502711 := bstep (se 1 (by rfl) ⟨1127033, by rfl⟩ : syracuseStep 1502711 = 2254067) B2254067
theorem B847417 : Blo 295830 847417 := bstep (se 2 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 847417 = 635563) B635563
theorem B1011257 : Blo 295830 1011257 := bstep (se 2 (by rfl) ⟨379221, by rfl⟩ : syracuseStep 1011257 = 758443) B758443
theorem B749351 : Blo 295830 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B847759 : Blo 295830 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B2552093 : Blo 295830 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B7205597 : Blo 295830 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B750343 : Blo 295830 750343 := bstep (se 1 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 750343 = 1125515) B1125515
theorem B1504007 : Blo 295830 1504007 := bstep (se 1 (by rfl) ⟨1128005, by rfl⟩ : syracuseStep 1504007 = 2256011) B2256011
theorem B848647 : Blo 295830 848647 := bstep (se 1 (by rfl) ⟨636485, by rfl⟩ : syracuseStep 848647 = 1272971) B1272971
theorem B783145 : Blo 295830 783145 := bstep (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) B587359
theorem B750647 : Blo 295830 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B1274953 : Blo 295830 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B849035 : Blo 295830 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B1438859 : Blo 295830 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B2258441 : Blo 295830 2258441 := bstep (se 2 (by rfl) ⟨846915, by rfl⟩ : syracuseStep 2258441 = 1693831) B1693831
theorem B718507 : Blo 295830 718507 := bstep (se 1 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 718507 = 1077761) B1077761
theorem B1504979 : Blo 295830 1504979 := bstep (se 1 (by rfl) ⟨1128734, by rfl⟩ : syracuseStep 1504979 = 2257469) B2257469
theorem B947963 : Blo 295830 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B718931 : Blo 295830 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B751913 : Blo 295830 751913 := bstep (se 2 (by rfl) ⟨281967, by rfl⟩ : syracuseStep 751913 = 563935) B563935
theorem B1898795 : Blo 295830 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B1210733 : Blo 295830 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B817597 : Blo 295830 817597 := bstep (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) B306599
theorem B1014329 : Blo 295830 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B3603143 : Blo 295830 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B8616779 : Blo 295830 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B752591 : Blo 295830 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B424939 : Blo 295830 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B1506599 : Blo 295830 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B7274099 : Blo 295830 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B1277687 : Blo 295830 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1704311 : Blo 295830 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B1278575 : Blo 295830 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2556845 : Blo 295830 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B2720783 : Blo 295830 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B295983 : Blo 295830 295983 := bstep (se 1 (by rfl) ⟨221987, by rfl⟩ : syracuseStep 295983 = 443975) B443975
theorem B296047 : Blo 295830 296047 := bstep (se 1 (by rfl) ⟨222035, by rfl⟩ : syracuseStep 296047 = 444071) B444071
theorem B296103 : Blo 295830 296103 := bstep (se 1 (by rfl) ⟨222077, by rfl⟩ : syracuseStep 296103 = 444155) B444155
theorem B296127 : Blo 295830 296127 := bstep (se 1 (by rfl) ⟨222095, by rfl⟩ : syracuseStep 296127 = 444191) B444191
theorem B296159 : Blo 295830 296159 := bstep (se 1 (by rfl) ⟨222119, by rfl⟩ : syracuseStep 296159 = 444239) B444239
theorem B296239 : Blo 295830 296239 := bstep (se 1 (by rfl) ⟨222179, by rfl⟩ : syracuseStep 296239 = 444359) B444359
theorem B754991 : Blo 295830 754991 := bstep (se 1 (by rfl) ⟨566243, by rfl⟩ : syracuseStep 754991 = 1132487) B1132487
theorem B296475 : Blo 295830 296475 := bstep (se 1 (by rfl) ⟨222356, by rfl⟩ : syracuseStep 296475 = 444713) B444713
theorem B296479 : Blo 295830 296479 := bstep (se 1 (by rfl) ⟨222359, by rfl⟩ : syracuseStep 296479 = 444719) B444719
theorem B296639 : Blo 295830 296639 := bstep (se 1 (by rfl) ⟨222479, by rfl⟩ : syracuseStep 296639 = 444959) B444959
theorem B296895 : Blo 295830 296895 := bstep (se 1 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 296895 = 445343) B445343
theorem B296927 : Blo 295830 296927 := bstep (se 1 (by rfl) ⟨222695, by rfl⟩ : syracuseStep 296927 = 445391) B445391
theorem B296987 : Blo 295830 296987 := bstep (se 1 (by rfl) ⟨222740, by rfl⟩ : syracuseStep 296987 = 445481) B445481
theorem B296991 : Blo 295830 296991 := bstep (se 1 (by rfl) ⟨222743, by rfl⟩ : syracuseStep 296991 = 445487) B445487
theorem B297007 : Blo 295830 297007 := bstep (se 1 (by rfl) ⟨222755, by rfl⟩ : syracuseStep 297007 = 445511) B445511
theorem B1280215 : Blo 295830 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B297183 : Blo 295830 297183 := bstep (se 1 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 297183 = 445775) B445775
theorem B297243 : Blo 295830 297243 := bstep (se 1 (by rfl) ⟨222932, by rfl⟩ : syracuseStep 297243 = 445865) B445865
theorem B4360517 : Blo 295830 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B297343 : Blo 295830 297343 := bstep (se 1 (by rfl) ⟨223007, by rfl⟩ : syracuseStep 297343 = 446015) B446015
theorem B4852133 : Blo 295830 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B297519 : Blo 295830 297519 := bstep (se 1 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 297519 = 446279) B446279
theorem B297575 : Blo 295830 297575 := bstep (se 1 (by rfl) ⟨223181, by rfl⟩ : syracuseStep 297575 = 446363) B446363
theorem B1018793 : Blo 295830 1018793 := bstep (se 2 (by rfl) ⟨382047, by rfl⟩ : syracuseStep 1018793 = 764095) B764095
theorem B297951 : Blo 295830 297951 := bstep (se 1 (by rfl) ⟨223463, by rfl⟩ : syracuseStep 297951 = 446927) B446927
theorem B297979 : Blo 295830 297979 := bstep (se 1 (by rfl) ⟨223484, by rfl⟩ : syracuseStep 297979 = 446969) B446969
theorem B298047 : Blo 295830 298047 := bstep (se 1 (by rfl) ⟨223535, by rfl⟩ : syracuseStep 298047 = 447071) B447071
theorem B298367 : Blo 295830 298367 := bstep (se 1 (by rfl) ⟨223775, by rfl⟩ : syracuseStep 298367 = 447551) B447551
theorem B298395 : Blo 295830 298395 := bstep (se 1 (by rfl) ⟨223796, by rfl⟩ : syracuseStep 298395 = 447593) B447593
theorem B298463 : Blo 295830 298463 := bstep (se 1 (by rfl) ⟨223847, by rfl⟩ : syracuseStep 298463 = 447695) B447695
theorem B298599 : Blo 295830 298599 := bstep (se 1 (by rfl) ⟨223949, by rfl⟩ : syracuseStep 298599 = 447899) B447899
theorem B298747 : Blo 295830 298747 := bstep (se 1 (by rfl) ⟨224060, by rfl⟩ : syracuseStep 298747 = 448121) B448121
theorem B298815 : Blo 295830 298815 := bstep (se 1 (by rfl) ⟨224111, by rfl⟩ : syracuseStep 298815 = 448223) B448223
theorem B298879 : Blo 295830 298879 := bstep (se 1 (by rfl) ⟨224159, by rfl⟩ : syracuseStep 298879 = 448319) B448319
theorem B1282031 : Blo 295830 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B298991 : Blo 295830 298991 := bstep (se 1 (by rfl) ⟨224243, by rfl⟩ : syracuseStep 298991 = 448487) B448487
theorem B299003 : Blo 295830 299003 := bstep (se 1 (by rfl) ⟨224252, by rfl⟩ : syracuseStep 299003 = 448505) B448505
theorem B299071 : Blo 295830 299071 := bstep (se 1 (by rfl) ⟨224303, by rfl⟩ : syracuseStep 299071 = 448607) B448607
theorem B299111 : Blo 295830 299111 := bstep (se 1 (by rfl) ⟨224333, by rfl⟩ : syracuseStep 299111 = 448667) B448667
theorem B299135 : Blo 295830 299135 := bstep (se 1 (by rfl) ⟨224351, by rfl⟩ : syracuseStep 299135 = 448703) B448703
theorem B299163 : Blo 295830 299163 := bstep (se 1 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 299163 = 448745) B448745
theorem B14094691 : Blo 295830 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B299367 : Blo 295830 299367 := bstep (se 1 (by rfl) ⟨224525, by rfl⟩ : syracuseStep 299367 = 449051) B449051
theorem B299419 : Blo 295830 299419 := bstep (se 1 (by rfl) ⟨224564, by rfl⟩ : syracuseStep 299419 = 449129) B449129
theorem B299771 : Blo 295830 299771 := bstep (se 1 (by rfl) ⟨224828, by rfl⟩ : syracuseStep 299771 = 449657) B449657
theorem B758585 : Blo 295830 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B1512431 : Blo 295830 1512431 := bstep (se 1 (by rfl) ⟨1134323, by rfl⟩ : syracuseStep 1512431 = 2268647) B2268647
theorem B758767 : Blo 295830 758767 := bstep (se 1 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 758767 = 1138151) B1138151
theorem B2561219 : Blo 295830 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B2856343 : Blo 295830 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B1971611 : Blo 295830 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B1152667 : Blo 295830 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B333895 : Blo 295830 333895 := bstep (se 1 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 333895 = 500843) B500843
theorem B956767 : Blo 295830 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B760295 : Blo 295830 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B1907201 : Blo 295830 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B564079 : Blo 295830 564079 := bstep (se 1 (by rfl) ⟨423059, by rfl⟩ : syracuseStep 564079 = 846119) B846119
theorem B334759 : Blo 295830 334759 := bstep (se 1 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 334759 = 502139) B502139
theorem B1514537 : Blo 295830 1514537 := bstep (se 2 (by rfl) ⟨567951, by rfl⟩ : syracuseStep 1514537 = 1135903) B1135903
theorem B334939 : Blo 295830 334939 := bstep (se 1 (by rfl) ⟨251204, by rfl⟩ : syracuseStep 334939 = 502409) B502409
theorem B9608381 : Blo 295830 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B958009 : Blo 295830 958009 := bstep (se 2 (by rfl) ⟨359253, by rfl⟩ : syracuseStep 958009 = 718507) B718507
theorem B499567 : Blo 295830 499567 := bstep (se 1 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 499567 = 749351) B749351
theorem B3219401 : Blo 295830 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B336127 : Blo 295830 336127 := bstep (se 1 (by rfl) ⟨252095, by rfl⟩ : syracuseStep 336127 = 504191) B504191
theorem B1024505 : Blo 295830 1024505 := bstep (se 2 (by rfl) ⟨384189, by rfl⟩ : syracuseStep 1024505 = 768379) B768379
theorem B336415 : Blo 295830 336415 := bstep (se 1 (by rfl) ⟨252311, by rfl⟩ : syracuseStep 336415 = 504623) B504623
theorem B500431 : Blo 295830 500431 := bstep (se 1 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 500431 = 750647) B750647
theorem B566023 : Blo 295830 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B959239 : Blo 295830 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B631975 : Blo 295830 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B337063 : Blo 295830 337063 := bstep (se 1 (by rfl) ⟨252797, by rfl⟩ : syracuseStep 337063 = 505595) B505595
theorem B566585 : Blo 295830 566585 := bstep (se 2 (by rfl) ⟨212469, by rfl⟩ : syracuseStep 566585 = 424939) B424939
theorem B1123739 : Blo 295830 1123739 := bstep (se 1 (by rfl) ⟨842804, by rfl⟩ : syracuseStep 1123739 = 1685609) B1685609
theorem B4597235 : Blo 295830 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B501275 : Blo 295830 501275 := bstep (se 1 (by rfl) ⟨375956, by rfl⟩ : syracuseStep 501275 = 751913) B751913
theorem B5056343 : Blo 295830 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B1124225 : Blo 295830 1124225 := bstep (se 2 (by rfl) ⟨421584, by rfl⟩ : syracuseStep 1124225 = 843169) B843169
theorem B5744519 : Blo 295830 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B501727 : Blo 295830 501727 := bstep (se 1 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 501727 = 752591) B752591
theorem B1517615 : Blo 295830 1517615 := bstep (se 1 (by rfl) ⟨1138211, by rfl⟩ : syracuseStep 1517615 = 2276423) B2276423
theorem B1124543 : Blo 295830 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B1911559 : Blo 295830 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B666575 : Blo 295830 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B568271 : Blo 295830 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B666665 : Blo 295830 666665 := bstep (se 2 (by rfl) ⟨249999, by rfl⟩ : syracuseStep 666665 = 499999) B499999
theorem B634025 : Blo 295830 634025 := bstep (se 2 (by rfl) ⟨237759, by rfl⟩ : syracuseStep 634025 = 475519) B475519
theorem B666899 : Blo 295830 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B666935 : Blo 295830 666935 := bstep (se 1 (by rfl) ⟨500201, by rfl⟩ : syracuseStep 666935 = 1000403) B1000403
theorem B2534975 : Blo 295830 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B569015 : Blo 295830 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B667529 : Blo 295830 667529 := bstep (se 2 (by rfl) ⟨250323, by rfl⟩ : syracuseStep 667529 = 500647) B500647
theorem B667745 : Blo 295830 667745 := bstep (se 2 (by rfl) ⟨250404, by rfl⟩ : syracuseStep 667745 = 500809) B500809
theorem B536719 : Blo 295830 536719 := bstep (se 1 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 536719 = 805079) B805079
theorem B635111 : Blo 295830 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B1225115 : Blo 295830 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B2404979 : Blo 295830 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B668411 : Blo 295830 668411 := bstep (se 1 (by rfl) ⟨501308, by rfl⟩ : syracuseStep 668411 = 1002617) B1002617
theorem B668627 : Blo 295830 668627 := bstep (se 1 (by rfl) ⟨501470, by rfl⟩ : syracuseStep 668627 = 1002941) B1002941
theorem B2274479 : Blo 295830 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B6534449 : Blo 295830 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B669095 : Blo 295830 669095 := bstep (se 1 (by rfl) ⟨501821, by rfl⟩ : syracuseStep 669095 = 1003643) B1003643
theorem B41268689 : Blo 295830 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B669203 : Blo 295830 669203 := bstep (se 1 (by rfl) ⟨501902, by rfl⟩ : syracuseStep 669203 = 1003805) B1003805
theorem B669275 : Blo 295830 669275 := bstep (se 1 (by rfl) ⟨501956, by rfl⟩ : syracuseStep 669275 = 1003913) B1003913
theorem B505487 : Blo 295830 505487 := bstep (se 1 (by rfl) ⟨379115, by rfl⟩ : syracuseStep 505487 = 758231) B758231
theorem B636751 : Blo 295830 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B1619927 : Blo 295830 1619927 := bstep (se 1 (by rfl) ⟨1214945, by rfl⟩ : syracuseStep 1619927 = 2429891) B2429891
theorem B669887 : Blo 295830 669887 := bstep (se 1 (by rfl) ⟨502415, by rfl⟩ : syracuseStep 669887 = 1004831) B1004831
theorem B539227 : Blo 295830 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B375455 : Blo 295830 375455 := bstep (se 1 (by rfl) ⟨281591, by rfl⟩ : syracuseStep 375455 = 563183) B563183
theorem B998459 : Blo 295830 998459 := bstep (se 1 (by rfl) ⟨748844, by rfl⟩ : syracuseStep 998459 = 1497689) B1497689
theorem B1621235 : Blo 295830 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B998729 : Blo 295830 998729 := bstep (se 2 (by rfl) ⟨374523, by rfl⟩ : syracuseStep 998729 = 749047) B749047
theorem B1129889 : Blo 295830 1129889 := bstep (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) B847417
theorem B671147 : Blo 295830 671147 := bstep (se 1 (by rfl) ⟨503360, by rfl⟩ : syracuseStep 671147 = 1006721) B1006721
theorem B671183 : Blo 295830 671183 := bstep (se 1 (by rfl) ⟨503387, by rfl⟩ : syracuseStep 671183 = 1006775) B1006775
theorem B638759 : Blo 295830 638759 := bstep (se 1 (by rfl) ⟨479069, by rfl⟩ : syracuseStep 638759 = 958139) B958139
theorem B1130345 : Blo 295830 1130345 := bstep (se 2 (by rfl) ⟨423879, by rfl⟩ : syracuseStep 1130345 = 847759) B847759
theorem B1359737 : Blo 295830 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B671687 : Blo 295830 671687 := bstep (se 1 (by rfl) ⟨503765, by rfl⟩ : syracuseStep 671687 = 1007531) B1007531
theorem B671993 : Blo 295830 671993 := bstep (se 2 (by rfl) ⟨251997, by rfl⟩ : syracuseStep 671993 = 503995) B503995
theorem B672047 : Blo 295830 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B672263 : Blo 295830 672263 := bstep (se 1 (by rfl) ⟨504197, by rfl⟩ : syracuseStep 672263 = 1008395) B1008395
theorem B574057 : Blo 295830 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B377455 : Blo 295830 377455 := bstep (se 1 (by rfl) ⟨283091, by rfl⟩ : syracuseStep 377455 = 566183) B566183
theorem B672443 : Blo 295830 672443 := bstep (se 1 (by rfl) ⟨504332, by rfl⟩ : syracuseStep 672443 = 1008665) B1008665
theorem B1131515 : Blo 295830 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B1000457 : Blo 295830 1000457 := bstep (se 2 (by rfl) ⟨375171, by rfl⟩ : syracuseStep 1000457 = 750343) B750343
theorem B1131529 : Blo 295830 1131529 := bstep (se 2 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 1131529 = 848647) B848647
theorem B5424205 : Blo 295830 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B672875 : Blo 295830 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B378047 : Blo 295830 378047 := bstep (se 1 (by rfl) ⟨283535, by rfl⟩ : syracuseStep 378047 = 567071) B567071
theorem B8111549 : Blo 295830 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B1427003 : Blo 295830 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B673343 : Blo 295830 673343 := bstep (se 1 (by rfl) ⟨505007, by rfl⟩ : syracuseStep 673343 = 1010015) B1010015
theorem B444011 : Blo 295830 444011 := bstep (se 1 (by rfl) ⟨333008, by rfl⟩ : syracuseStep 444011 = 666017) B666017
theorem B673451 : Blo 295830 673451 := bstep (se 1 (by rfl) ⟨505088, by rfl⟩ : syracuseStep 673451 = 1010177) B1010177
theorem B444095 : Blo 295830 444095 := bstep (se 1 (by rfl) ⟨333071, by rfl⟩ : syracuseStep 444095 = 666143) B666143
theorem B1132319 : Blo 295830 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B444281 : Blo 295830 444281 := bstep (se 2 (by rfl) ⟨166605, by rfl⟩ : syracuseStep 444281 = 333211) B333211
theorem B673775 : Blo 295830 673775 := bstep (se 1 (by rfl) ⟨505331, by rfl⟩ : syracuseStep 673775 = 1010663) B1010663
theorem B1460369 : Blo 295830 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B673991 : Blo 295830 673991 := bstep (se 1 (by rfl) ⟨505493, by rfl⟩ : syracuseStep 673991 = 1010987) B1010987
theorem B1001807 : Blo 295830 1001807 := bstep (se 1 (by rfl) ⟨751355, by rfl⟩ : syracuseStep 1001807 = 1502711) B1502711
theorem B674171 : Blo 295830 674171 := bstep (se 1 (by rfl) ⟨505628, by rfl⟩ : syracuseStep 674171 = 1011257) B1011257
theorem B445031 : Blo 295830 445031 := bstep (se 1 (by rfl) ⟨333773, by rfl⟩ : syracuseStep 445031 = 667547) B667547
theorem B674441 : Blo 295830 674441 := bstep (se 2 (by rfl) ⟨252915, by rfl⟩ : syracuseStep 674441 = 505831) B505831
theorem B3426961 : Blo 295830 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B7359149 : Blo 295830 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B3394223 : Blo 295830 3394223 := bstep (se 1 (by rfl) ⟨2545667, by rfl⟩ : syracuseStep 3394223 = 5091335) B5091335
theorem B445223 : Blo 295830 445223 := bstep (se 1 (by rfl) ⟨333917, by rfl⟩ : syracuseStep 445223 = 667835) B667835
theorem B445547 : Blo 295830 445547 := bstep (se 1 (by rfl) ⟨334160, by rfl⟩ : syracuseStep 445547 = 668321) B668321
theorem B4803731 : Blo 295830 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B1002671 : Blo 295830 1002671 := bstep (se 1 (by rfl) ⟨752003, by rfl⟩ : syracuseStep 1002671 = 1504007) B1504007
theorem B445787 : Blo 295830 445787 := bstep (se 1 (by rfl) ⟨334340, by rfl⟩ : syracuseStep 445787 = 668681) B668681
theorem B445817 : Blo 295830 445817 := bstep (se 2 (by rfl) ⟨167181, by rfl⟩ : syracuseStep 445817 = 334363) B334363
theorem B445823 : Blo 295830 445823 := bstep (se 1 (by rfl) ⟨334367, by rfl⟩ : syracuseStep 445823 = 668735) B668735
theorem B1003319 : Blo 295830 1003319 := bstep (se 1 (by rfl) ⟨752489, by rfl⟩ : syracuseStep 1003319 = 1504979) B1504979
theorem B1822591 : Blo 295830 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B4050917 : Blo 295830 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B446447 : Blo 295830 446447 := bstep (se 1 (by rfl) ⟨334835, by rfl⟩ : syracuseStep 446447 = 669671) B669671
theorem B446459 : Blo 295830 446459 := bstep (se 1 (by rfl) ⟨334844, by rfl⟩ : syracuseStep 446459 = 669689) B669689
theorem B446519 : Blo 295830 446519 := bstep (se 1 (by rfl) ⟨334889, by rfl⟩ : syracuseStep 446519 = 669779) B669779
theorem B479287 : Blo 295830 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B446567 : Blo 295830 446567 := bstep (se 1 (by rfl) ⟨334925, by rfl⟩ : syracuseStep 446567 = 669851) B669851
theorem B446639 : Blo 295830 446639 := bstep (se 1 (by rfl) ⟨334979, by rfl⟩ : syracuseStep 446639 = 669959) B669959
theorem B1265863 : Blo 295830 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B2281691 : Blo 295830 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B807155 : Blo 295830 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B676219 : Blo 295830 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B446843 : Blo 295830 446843 := bstep (se 1 (by rfl) ⟨335132, by rfl⟩ : syracuseStep 446843 = 670265) B670265
theorem B447113 : Blo 295830 447113 := bstep (se 2 (by rfl) ⟨167667, by rfl⟩ : syracuseStep 447113 = 335335) B335335
theorem B447323 : Blo 295830 447323 := bstep (se 1 (by rfl) ⟨335492, by rfl⟩ : syracuseStep 447323 = 670985) B670985
theorem B1004399 : Blo 295830 1004399 := bstep (se 1 (by rfl) ⟨753299, by rfl⟩ : syracuseStep 1004399 = 1506599) B1506599
theorem B316667 : Blo 295830 316667 := bstep (se 1 (by rfl) ⟨237500, by rfl⟩ : syracuseStep 316667 = 475001) B475001
theorem B1266941 : Blo 295830 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B447785 : Blo 295830 447785 := bstep (se 2 (by rfl) ⟨167919, by rfl⟩ : syracuseStep 447785 = 335839) B335839
theorem B2545121 : Blo 295830 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B447983 : Blo 295830 447983 := bstep (se 1 (by rfl) ⟨335987, by rfl⟩ : syracuseStep 447983 = 671975) B671975
theorem B448379 : Blo 295830 448379 := bstep (se 1 (by rfl) ⟨336284, by rfl⟩ : syracuseStep 448379 = 672569) B672569
theorem B448415 : Blo 295830 448415 := bstep (se 1 (by rfl) ⟨336311, by rfl⟩ : syracuseStep 448415 = 672623) B672623
theorem B448649 : Blo 295830 448649 := bstep (se 2 (by rfl) ⟨168243, by rfl⟩ : syracuseStep 448649 = 336487) B336487
theorem B448799 : Blo 295830 448799 := bstep (se 1 (by rfl) ⟨336599, by rfl⟩ : syracuseStep 448799 = 673199) B673199
theorem B2251151 : Blo 295830 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B1137179 : Blo 295830 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B449351 : Blo 295830 449351 := bstep (se 1 (by rfl) ⟨337013, by rfl⟩ : syracuseStep 449351 = 674027) B674027
theorem B1137847 : Blo 295830 1137847 := bstep (se 1 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 1137847 = 1706771) B1706771
theorem B843385 : Blo 295830 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B843659 : Blo 295830 843659 := bstep (se 1 (by rfl) ⟨632744, by rfl⟩ : syracuseStep 843659 = 1265489) B1265489
theorem B6447185 : Blo 295830 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B1073407 : Blo 295830 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B3400055 : Blo 295830 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B9527759 : Blo 295830 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B713299 : Blo 295830 713299 := bstep (se 1 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 713299 = 1069949) B1069949
theorem B1271315 : Blo 295830 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B9791165 : Blo 295830 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B2746075 : Blo 295830 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B20834995 : Blo 295830 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B5795309 : Blo 295830 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B716431 : Blo 295830 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B716471 : Blo 295830 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B1044193 : Blo 295830 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B1896335 : Blo 295830 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B1699937 : Blo 295830 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B1799453 : Blo 295830 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B1275227 : Blo 295830 1275227 := bstep (se 1 (by rfl) ⟨956420, by rfl⟩ : syracuseStep 1275227 = 1912841) B1912841
theorem B1701395 : Blo 295830 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B423515 : Blo 295830 423515 := bstep (se 1 (by rfl) ⟨317636, by rfl⟩ : syracuseStep 423515 = 635273) B635273
theorem B1603493 : Blo 295830 1603493 := bstep (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) B300655
theorem B2258927 : Blo 295830 2258927 := bstep (se 1 (by rfl) ⟨1694195, by rfl⟩ : syracuseStep 2258927 = 3388391) B3388391
theorem B1505627 : Blo 295830 1505627 := bstep (se 1 (by rfl) ⟨1129220, by rfl⟩ : syracuseStep 1505627 = 2258441) B2258441
theorem B2718305 : Blo 295830 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B3635887 : Blo 295830 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B1211219 : Blo 295830 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B4849399 : Blo 295830 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B851791 : Blo 295830 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B852383 : Blo 295830 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1704563 : Blo 295830 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B754343 : Blo 295830 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B951065 : Blo 295830 951065 := bstep (se 2 (by rfl) ⟨356649, by rfl⟩ : syracuseStep 951065 = 713299) B713299
theorem B754697 : Blo 295830 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B1278985 : Blo 295830 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B951335 : Blo 295830 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B296007 : Blo 295830 296007 := bstep (se 1 (by rfl) ⟨222005, by rfl⟩ : syracuseStep 296007 = 444011) B444011
theorem B296063 : Blo 295830 296063 := bstep (se 1 (by rfl) ⟨222047, by rfl⟩ : syracuseStep 296063 = 444095) B444095
theorem B754879 : Blo 295830 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B296187 : Blo 295830 296187 := bstep (se 1 (by rfl) ⟨222140, by rfl⟩ : syracuseStep 296187 = 444281) B444281
theorem B1508705 : Blo 295830 1508705 := bstep (se 2 (by rfl) ⟨565764, by rfl⟩ : syracuseStep 1508705 = 1131529) B1131529
theorem B296687 : Blo 295830 296687 := bstep (se 1 (by rfl) ⟨222515, by rfl⟩ : syracuseStep 296687 = 445031) B445031
theorem B2262815 : Blo 295830 2262815 := bstep (se 1 (by rfl) ⟨1697111, by rfl⟩ : syracuseStep 2262815 = 3394223) B3394223
theorem B75171685 : Blo 295830 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B296815 : Blo 295830 296815 := bstep (se 1 (by rfl) ⟨222611, by rfl⟩ : syracuseStep 296815 = 445223) B445223
theorem B297031 : Blo 295830 297031 := bstep (se 1 (by rfl) ⟨222773, by rfl⟩ : syracuseStep 297031 = 445547) B445547
theorem B297191 : Blo 295830 297191 := bstep (se 1 (by rfl) ⟨222893, by rfl⟩ : syracuseStep 297191 = 445787) B445787
theorem B297211 : Blo 295830 297211 := bstep (se 1 (by rfl) ⟨222908, by rfl⟩ : syracuseStep 297211 = 445817) B445817
theorem B297215 : Blo 295830 297215 := bstep (se 1 (by rfl) ⟨222911, by rfl⟩ : syracuseStep 297215 = 445823) B445823
theorem B854687 : Blo 295830 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B297631 : Blo 295830 297631 := bstep (se 1 (by rfl) ⟨223223, by rfl⟩ : syracuseStep 297631 = 446447) B446447
theorem B297639 : Blo 295830 297639 := bstep (se 1 (by rfl) ⟨223229, by rfl⟩ : syracuseStep 297639 = 446459) B446459
theorem B297679 : Blo 295830 297679 := bstep (se 1 (by rfl) ⟨223259, by rfl⟩ : syracuseStep 297679 = 446519) B446519
theorem B297711 : Blo 295830 297711 := bstep (se 1 (by rfl) ⟨223283, by rfl⟩ : syracuseStep 297711 = 446567) B446567
theorem B297759 : Blo 295830 297759 := bstep (se 1 (by rfl) ⟨223319, by rfl⟩ : syracuseStep 297759 = 446639) B446639
theorem B297895 : Blo 295830 297895 := bstep (se 1 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 297895 = 446843) B446843
theorem B1706953 : Blo 295830 1706953 := bstep (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) B1280215
theorem B298075 : Blo 295830 298075 := bstep (se 1 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 298075 = 447113) B447113
theorem B298215 : Blo 295830 298215 := bstep (se 1 (by rfl) ⟨223661, by rfl⟩ : syracuseStep 298215 = 447323) B447323
theorem B1707479 : Blo 295830 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B298523 : Blo 295830 298523 := bstep (se 1 (by rfl) ⟨223892, by rfl⟩ : syracuseStep 298523 = 447785) B447785
theorem B1314407 : Blo 295830 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B298655 : Blo 295830 298655 := bstep (se 1 (by rfl) ⟨223991, by rfl⟩ : syracuseStep 298655 = 447983) B447983
theorem B21630797 : Blo 295830 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B298919 : Blo 295830 298919 := bstep (se 1 (by rfl) ⟨224189, by rfl⟩ : syracuseStep 298919 = 448379) B448379
theorem B298943 : Blo 295830 298943 := bstep (se 1 (by rfl) ⟨224207, by rfl⟩ : syracuseStep 298943 = 448415) B448415
theorem B299099 : Blo 295830 299099 := bstep (se 1 (by rfl) ⟨224324, by rfl⟩ : syracuseStep 299099 = 448649) B448649
theorem B299199 : Blo 295830 299199 := bstep (se 1 (by rfl) ⟨224399, by rfl⟩ : syracuseStep 299199 = 448799) B448799
theorem B758119 : Blo 295830 758119 := bstep (se 1 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 758119 = 1137179) B1137179
theorem B299567 : Blo 295830 299567 := bstep (se 1 (by rfl) ⟨224675, by rfl⟩ : syracuseStep 299567 = 449351) B449351
theorem B955241 : Blo 295830 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B562439 : Blo 295830 562439 := bstep (se 1 (by rfl) ⟨421829, by rfl⟩ : syracuseStep 562439 = 843659) B843659
theorem B4298123 : Blo 295830 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B2266703 : Blo 295830 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B334183 : Blo 295830 334183 := bstep (se 1 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 334183 = 501275) B501275
theorem B3808457 : Blo 295830 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B1516319 : Blo 295830 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B336991 : Blo 295830 336991 := bstep (se 1 (by rfl) ⟨252743, by rfl⟩ : syracuseStep 336991 = 505487) B505487
theorem B25863461 : Blo 295830 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B1517129 : Blo 295830 1517129 := bstep (se 2 (by rfl) ⟨568923, by rfl⟩ : syracuseStep 1517129 = 1137847) B1137847
theorem B1812203 : Blo 295830 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B665639 : Blo 295830 665639 := bstep (se 1 (by rfl) ⟨499229, by rfl⟩ : syracuseStep 665639 = 998459) B998459
theorem B1124513 : Blo 295830 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B665819 : Blo 295830 665819 := bstep (se 1 (by rfl) ⟨499364, by rfl⟩ : syracuseStep 665819 = 998729) B998729
theorem B666089 : Blo 295830 666089 := bstep (se 2 (by rfl) ⟨249783, by rfl⟩ : syracuseStep 666089 = 499567) B499567
theorem B666971 : Blo 295830 666971 := bstep (se 1 (by rfl) ⟨500228, by rfl⟩ : syracuseStep 666971 = 1000457) B1000457
theorem B1813855 : Blo 295830 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B765409 : Blo 295830 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B503273 : Blo 295830 503273 := bstep (se 2 (by rfl) ⟨188727, by rfl⟩ : syracuseStep 503273 = 377455) B377455
theorem B503327 : Blo 295830 503327 := bstep (se 1 (by rfl) ⟨377495, by rfl⟩ : syracuseStep 503327 = 754991) B754991
theorem B667241 : Blo 295830 667241 := bstep (se 2 (by rfl) ⟨250215, by rfl⟩ : syracuseStep 667241 = 500431) B500431
theorem B667871 : Blo 295830 667871 := bstep (se 1 (by rfl) ⟨500903, by rfl⟩ : syracuseStep 667871 = 1001807) B1001807
theorem B668447 : Blo 295830 668447 := bstep (se 1 (by rfl) ⟨501335, by rfl⟩ : syracuseStep 668447 = 1002671) B1002671
theorem B668879 : Blo 295830 668879 := bstep (se 1 (by rfl) ⟨501659, by rfl⟩ : syracuseStep 668879 = 1003319) B1003319
theorem B668969 : Blo 295830 668969 := bstep (se 2 (by rfl) ⟨250863, by rfl⟩ : syracuseStep 668969 = 501727) B501727
theorem B2700611 : Blo 295830 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1521127 : Blo 295830 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B538103 : Blo 295830 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B505723 : Blo 295830 505723 := bstep (se 1 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 505723 = 758585) B758585
theorem B669599 : Blo 295830 669599 := bstep (se 1 (by rfl) ⟨502199, by rfl⟩ : syracuseStep 669599 = 1004399) B1004399
theorem B4798541 : Blo 295830 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B4569281 : Blo 295830 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B1129373 : Blo 295830 1129373 := bstep (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) B423515
theorem B506863 : Blo 295830 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B6405587 : Blo 295830 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1392257 : Blo 295830 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B2146267 : Blo 295830 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B639049 : Blo 295830 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B1687817 : Blo 295830 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B901625 : Blo 295830 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B377723 : Blo 295830 377723 := bstep (se 1 (by rfl) ⟨283292, by rfl⟩ : syracuseStep 377723 = 566585) B566585
theorem B3064823 : Blo 295830 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B1001213 : Blo 295830 1001213 := bstep (se 3 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 1001213 = 375455) B375455
theorem B444383 : Blo 295830 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B378847 : Blo 295830 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B444443 : Blo 295830 444443 := bstep (se 1 (by rfl) ⟨333332, by rfl⟩ : syracuseStep 444443 = 666665) B666665
theorem B444599 : Blo 295830 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B444623 : Blo 295830 444623 := bstep (se 1 (by rfl) ⟨333467, by rfl⟩ : syracuseStep 444623 = 666935) B666935
theorem B1689983 : Blo 295830 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B477647 : Blo 295830 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B379343 : Blo 295830 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B445019 : Blo 295830 445019 := bstep (se 1 (by rfl) ⟨333764, by rfl⟩ : syracuseStep 445019 = 667529) B667529
theorem B1264223 : Blo 295830 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B445163 : Blo 295830 445163 := bstep (se 1 (by rfl) ⟨333872, by rfl⟩ : syracuseStep 445163 = 667745) B667745
theorem B1133291 : Blo 295830 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B445193 : Blo 295830 445193 := bstep (se 2 (by rfl) ⟨166947, by rfl⟩ : syracuseStep 445193 = 333895) B333895
theorem B1690733 : Blo 295830 1690733 := bstep (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) B634025
theorem B445607 : Blo 295830 445607 := bstep (se 1 (by rfl) ⟨334205, by rfl⟩ : syracuseStep 445607 = 668411) B668411
theorem B445751 : Blo 295830 445751 := bstep (se 1 (by rfl) ⟨334313, by rfl⟩ : syracuseStep 445751 = 668627) B668627
theorem B446063 : Blo 295830 446063 := bstep (se 1 (by rfl) ⟨334547, by rfl⟩ : syracuseStep 446063 = 669095) B669095
theorem B27512459 : Blo 295830 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B446135 : Blo 295830 446135 := bstep (se 1 (by rfl) ⟨334601, by rfl⟩ : syracuseStep 446135 = 669203) B669203
theorem B1134263 : Blo 295830 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B446183 : Blo 295830 446183 := bstep (se 1 (by rfl) ⟨334637, by rfl⟩ : syracuseStep 446183 = 669275) B669275
theorem B446345 : Blo 295830 446345 := bstep (se 2 (by rfl) ⟨167379, by rfl⟩ : syracuseStep 446345 = 334759) B334759
theorem B1068995 : Blo 295830 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B446585 : Blo 295830 446585 := bstep (se 2 (by rfl) ⟨167469, by rfl⟩ : syracuseStep 446585 = 334939) B334939
theorem B446591 : Blo 295830 446591 := bstep (se 1 (by rfl) ⟨334943, by rfl⟩ : syracuseStep 446591 = 669887) B669887
theorem B1003751 : Blo 295830 1003751 := bstep (se 1 (by rfl) ⟨752813, by rfl⟩ : syracuseStep 1003751 = 1505627) B1505627
theorem B807479 : Blo 295830 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B9720485 : Blo 295830 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B447431 : Blo 295830 447431 := bstep (se 1 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 447431 = 671147) B671147
theorem B447455 : Blo 295830 447455 := bstep (se 1 (by rfl) ⟨335591, by rfl⟩ : syracuseStep 447455 = 671183) B671183
theorem B1135721 : Blo 295830 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B906491 : Blo 295830 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B447791 : Blo 295830 447791 := bstep (se 1 (by rfl) ⟨335843, by rfl⟩ : syracuseStep 447791 = 671687) B671687
theorem B447995 : Blo 295830 447995 := bstep (se 1 (by rfl) ⟨335996, by rfl⟩ : syracuseStep 447995 = 671993) B671993
theorem B448031 : Blo 295830 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B1136207 : Blo 295830 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B1431209 : Blo 295830 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B448169 : Blo 295830 448169 := bstep (se 2 (by rfl) ⟨168063, by rfl⟩ : syracuseStep 448169 = 336127) B336127
theorem B448175 : Blo 295830 448175 := bstep (se 1 (by rfl) ⟨336131, by rfl⟩ : syracuseStep 448175 = 672263) B672263
theorem B448295 : Blo 295830 448295 := bstep (se 1 (by rfl) ⟨336221, by rfl⟩ : syracuseStep 448295 = 672443) B672443
theorem B448553 : Blo 295830 448553 := bstep (se 2 (by rfl) ⟨168207, by rfl⟩ : syracuseStep 448553 = 336415) B336415
theorem B448583 : Blo 295830 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B448895 : Blo 295830 448895 := bstep (se 1 (by rfl) ⟨336671, by rfl⟩ : syracuseStep 448895 = 673343) B673343
theorem B448967 : Blo 295830 448967 := bstep (se 1 (by rfl) ⟨336725, by rfl⟩ : syracuseStep 448967 = 673451) B673451
theorem B449183 : Blo 295830 449183 := bstep (se 1 (by rfl) ⟨336887, by rfl⟩ : syracuseStep 449183 = 673775) B673775
theorem B7232273 : Blo 295830 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B449327 : Blo 295830 449327 := bstep (se 1 (by rfl) ⟨336995, by rfl⟩ : syracuseStep 449327 = 673991) B673991
theorem B2907011 : Blo 295830 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B842633 : Blo 295830 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B449417 : Blo 295830 449417 := bstep (se 2 (by rfl) ⟨168531, by rfl⟩ : syracuseStep 449417 = 337063) B337063
theorem B449447 : Blo 295830 449447 := bstep (se 1 (by rfl) ⟨337085, by rfl⟩ : syracuseStep 449447 = 674171) B674171
theorem B3234755 : Blo 295830 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B449627 : Blo 295830 449627 := bstep (se 1 (by rfl) ⟨337220, by rfl⟩ : syracuseStep 449627 = 674441) B674441
theorem B4906099 : Blo 295830 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B679195 : Blo 295830 679195 := bstep (se 1 (by rfl) ⟨509396, by rfl⟩ : syracuseStep 679195 = 1018793) B1018793
theorem B3202487 : Blo 295830 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B3661433 : Blo 295830 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1008125 : Blo 295830 1008125 := bstep (se 3 (by rfl) ⟨189023, by rfl⟩ : syracuseStep 1008125 = 378047) B378047
theorem B844445 : Blo 295830 844445 := bstep (se 3 (by rfl) ⟨158333, by rfl⟩ : syracuseStep 844445 = 316667) B316667
theorem B1008287 : Blo 295830 1008287 := bstep (se 1 (by rfl) ⟨756215, by rfl⟩ : syracuseStep 1008287 = 1512431) B1512431
theorem B844627 : Blo 295830 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B27779993 : Blo 295830 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B1696747 : Blo 295830 1696747 := bstep (se 1 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 1696747 = 2545121) B2545121
theorem B2548745 : Blo 295830 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B1500767 : Blo 295830 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B1271467 : Blo 295830 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B26109773 : Blo 295830 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1009691 : Blo 295830 1009691 := bstep (se 1 (by rfl) ⟨757268, by rfl⟩ : syracuseStep 1009691 = 1514537) B1514537
theorem B715625 : Blo 295830 715625 := bstep (se 2 (by rfl) ⟨268359, by rfl⟩ : syracuseStep 715625 = 536719) B536719
theorem B6351839 : Blo 295830 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B683003 : Blo 295830 683003 := bstep (se 1 (by rfl) ⟨512252, by rfl⟩ : syracuseStep 683003 = 1024505) B1024505
theorem B3894317 : Blo 295830 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B749159 : Blo 295830 749159 := bstep (se 1 (by rfl) ⟨561869, by rfl⟩ : syracuseStep 749159 = 1123739) B1123739
theorem B847543 : Blo 295830 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B3370895 : Blo 295830 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B749483 : Blo 295830 749483 := bstep (se 1 (by rfl) ⟨562112, by rfl⟩ : syracuseStep 749483 = 1124225) B1124225
theorem B3829679 : Blo 295830 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B1011689 : Blo 295830 1011689 := bstep (se 2 (by rfl) ⟨379383, by rfl⟩ : syracuseStep 1011689 = 758767) B758767
theorem B1011743 : Blo 295830 1011743 := bstep (se 1 (by rfl) ⟨758807, by rfl⟩ : syracuseStep 1011743 = 1517615) B1517615
theorem B749695 : Blo 295830 749695 := bstep (se 1 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 749695 = 1124543) B1124543
theorem B1536889 : Blo 295830 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B3863539 : Blo 295830 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B849001 : Blo 295830 849001 := bstep (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) B636751
theorem B423407 : Blo 295830 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B816743 : Blo 295830 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1603319 : Blo 295830 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1275689 : Blo 295830 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B718969 : Blo 295830 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B4356299 : Blo 295830 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B850151 : Blo 295830 850151 := bstep (se 1 (by rfl) ⟨637613, by rfl⟩ : syracuseStep 850151 = 1275227) B1275227
theorem B4847849 : Blo 295830 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B752105 : Blo 295830 752105 := bstep (se 2 (by rfl) ⟨282039, by rfl⟩ : syracuseStep 752105 = 564079) B564079
theorem B1079951 : Blo 295830 1079951 := bstep (se 1 (by rfl) ⟨809963, by rfl⟩ : syracuseStep 1079951 = 1619927) B1619927
theorem B1505951 : Blo 295830 1505951 := bstep (se 1 (by rfl) ⟨1129463, by rfl⟩ : syracuseStep 1505951 = 2258927) B2258927
theorem B1277345 : Blo 295830 1277345 := bstep (se 2 (by rfl) ⟨479004, by rfl⟩ : syracuseStep 1277345 = 958009) B958009
theorem B1080823 : Blo 295830 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B753259 : Blo 295830 753259 := bstep (se 1 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 753259 = 1129889) B1129889
theorem B425839 : Blo 295830 425839 := bstep (se 1 (by rfl) ⟨319379, by rfl⟩ : syracuseStep 425839 = 638759) B638759
theorem B753563 : Blo 295830 753563 := bstep (se 1 (by rfl) ⟨565172, by rfl⟩ : syracuseStep 753563 = 1130345) B1130345
theorem B852065 : Blo 295830 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B1508543 : Blo 295830 1508543 := bstep (se 1 (by rfl) ⟨1131407, by rfl⟩ : syracuseStep 1508543 = 2262815) B2262815
theorem B2262329 : Blo 295830 2262329 := bstep (se 2 (by rfl) ⟨848373, by rfl⟩ : syracuseStep 2262329 = 1696747) B1696747
theorem B296255 : Blo 295830 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B1705313 : Blo 295830 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B296295 : Blo 295830 296295 := bstep (se 1 (by rfl) ⟨222221, by rfl⟩ : syracuseStep 296295 = 444443) B444443
theorem B296399 : Blo 295830 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B296415 : Blo 295830 296415 := bstep (se 1 (by rfl) ⟨222311, by rfl⟩ : syracuseStep 296415 = 444623) B444623
theorem B296679 : Blo 295830 296679 := bstep (se 1 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 296679 = 445019) B445019
theorem B296775 : Blo 295830 296775 := bstep (se 1 (by rfl) ⟨222581, by rfl⟩ : syracuseStep 296775 = 445163) B445163
theorem B755527 : Blo 295830 755527 := bstep (se 1 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 755527 = 1133291) B1133291
theorem B296795 : Blo 295830 296795 := bstep (se 1 (by rfl) ⟨222596, by rfl⟩ : syracuseStep 296795 = 445193) B445193
theorem B297071 : Blo 295830 297071 := bstep (se 1 (by rfl) ⟨222803, by rfl⟩ : syracuseStep 297071 = 445607) B445607
theorem B297167 : Blo 295830 297167 := bstep (se 1 (by rfl) ⟨222875, by rfl⟩ : syracuseStep 297167 = 445751) B445751
theorem B297375 : Blo 295830 297375 := bstep (se 1 (by rfl) ⟨223031, by rfl⟩ : syracuseStep 297375 = 446063) B446063
theorem B297423 : Blo 295830 297423 := bstep (se 1 (by rfl) ⟨223067, by rfl⟩ : syracuseStep 297423 = 446135) B446135
theorem B756175 : Blo 295830 756175 := bstep (se 1 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 756175 = 1134263) B1134263
theorem B297455 : Blo 295830 297455 := bstep (se 1 (by rfl) ⟨223091, by rfl⟩ : syracuseStep 297455 = 446183) B446183
theorem B14420531 : Blo 295830 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B297563 : Blo 295830 297563 := bstep (se 1 (by rfl) ⟨223172, by rfl⟩ : syracuseStep 297563 = 446345) B446345
theorem B297723 : Blo 295830 297723 := bstep (se 1 (by rfl) ⟨223292, by rfl⟩ : syracuseStep 297723 = 446585) B446585
theorem B297727 : Blo 295830 297727 := bstep (se 1 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 297727 = 446591) B446591
theorem B298287 : Blo 295830 298287 := bstep (se 1 (by rfl) ⟨223715, by rfl⟩ : syracuseStep 298287 = 447431) B447431
theorem B298303 : Blo 295830 298303 := bstep (se 1 (by rfl) ⟨223727, by rfl⟩ : syracuseStep 298303 = 447455) B447455
theorem B757147 : Blo 295830 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B298527 : Blo 295830 298527 := bstep (se 1 (by rfl) ⟨223895, by rfl⟩ : syracuseStep 298527 = 447791) B447791
theorem B298663 : Blo 295830 298663 := bstep (se 1 (by rfl) ⟨223997, by rfl⟩ : syracuseStep 298663 = 447995) B447995
theorem B298687 : Blo 295830 298687 := bstep (se 1 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 298687 = 448031) B448031
theorem B1511135 : Blo 295830 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B757471 : Blo 295830 757471 := bstep (se 1 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 757471 = 1136207) B1136207
theorem B298779 : Blo 295830 298779 := bstep (se 1 (by rfl) ⟨224084, by rfl⟩ : syracuseStep 298779 = 448169) B448169
theorem B298783 : Blo 295830 298783 := bstep (se 1 (by rfl) ⟨224087, by rfl⟩ : syracuseStep 298783 = 448175) B448175
theorem B298863 : Blo 295830 298863 := bstep (se 1 (by rfl) ⟨224147, by rfl⟩ : syracuseStep 298863 = 448295) B448295
theorem B299035 : Blo 295830 299035 := bstep (se 1 (by rfl) ⟨224276, by rfl⟩ : syracuseStep 299035 = 448553) B448553
theorem B299055 : Blo 295830 299055 := bstep (se 1 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 299055 = 448583) B448583
theorem B299263 : Blo 295830 299263 := bstep (se 1 (by rfl) ⟨224447, by rfl⟩ : syracuseStep 299263 = 448895) B448895
theorem B299311 : Blo 295830 299311 := bstep (se 1 (by rfl) ⟨224483, by rfl⟩ : syracuseStep 299311 = 448967) B448967
theorem B299455 : Blo 295830 299455 := bstep (se 1 (by rfl) ⟨224591, by rfl⟩ : syracuseStep 299455 = 449183) B449183
theorem B4821515 : Blo 295830 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B299551 : Blo 295830 299551 := bstep (se 1 (by rfl) ⟨224663, by rfl⟩ : syracuseStep 299551 = 449327) B449327
theorem B1938007 : Blo 295830 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B561755 : Blo 295830 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B299611 : Blo 295830 299611 := bstep (se 1 (by rfl) ⟨224708, by rfl⟩ : syracuseStep 299611 = 449417) B449417
theorem B299631 : Blo 295830 299631 := bstep (se 1 (by rfl) ⟨224723, by rfl⟩ : syracuseStep 299631 = 449447) B449447
theorem B1020545 : Blo 295830 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B299751 : Blo 295830 299751 := bstep (se 1 (by rfl) ⟨224813, by rfl⟩ : syracuseStep 299751 = 449627) B449627
theorem B2134991 : Blo 295830 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B562963 : Blo 295830 562963 := bstep (se 1 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 562963 = 844445) B844445
theorem B18519995 : Blo 295830 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B17242307 : Blo 295830 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B17406515 : Blo 295830 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B5151385 : Blo 295830 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B4234559 : Blo 295830 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B2596211 : Blo 295830 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B335515 : Blo 295830 335515 := bstep (se 1 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 335515 = 503273) B503273
theorem B335551 : Blo 295830 335551 := bstep (se 1 (by rfl) ⟨251663, by rfl⟩ : syracuseStep 335551 = 503327) B503327
theorem B499439 : Blo 295830 499439 := bstep (se 1 (by rfl) ⟨374579, by rfl⟩ : syracuseStep 499439 = 749159) B749159
theorem B499655 : Blo 295830 499655 := bstep (se 1 (by rfl) ⟨374741, by rfl⟩ : syracuseStep 499655 = 749483) B749483
theorem B958625 : Blo 295830 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B566767 : Blo 295830 566767 := bstep (se 1 (by rfl) ⟨425075, by rfl⟩ : syracuseStep 566767 = 850151) B850151
theorem B501403 : Blo 295830 501403 := bstep (se 1 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 501403 = 752105) B752105
theorem B4270391 : Blo 295830 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B928171 : Blo 295830 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B567785 : Blo 295830 567785 := bstep (se 2 (by rfl) ⟨212919, by rfl⟩ : syracuseStep 567785 = 425839) B425839
theorem B502375 : Blo 295830 502375 := bstep (se 1 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 502375 = 753563) B753563
theorem B2861689 : Blo 295830 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B1125211 : Blo 295830 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B502895 : Blo 295830 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B634043 : Blo 295830 634043 := bstep (se 1 (by rfl) ⟨475532, by rfl⟩ : syracuseStep 634043 = 951065) B951065
theorem B2043215 : Blo 295830 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B503131 : Blo 295830 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B634223 : Blo 295830 634223 := bstep (se 1 (by rfl) ⟨475667, by rfl⟩ : syracuseStep 634223 = 951335) B951335
theorem B2273021 : Blo 295830 2273021 := bstep (se 3 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 2273021 = 852383) B852383
theorem B1126169 : Blo 295830 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B667475 : Blo 295830 667475 := bstep (se 1 (by rfl) ⟨500606, by rfl⟩ : syracuseStep 667475 = 1001213) B1001213
theorem B2404333 : Blo 295830 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B1126655 : Blo 295830 1126655 := bstep (se 1 (by rfl) ⟨844991, by rfl⟩ : syracuseStep 1126655 = 1689983) B1689983
theorem B569791 : Blo 295830 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B1127155 : Blo 295830 1127155 := bstep (se 1 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 1127155 = 1690733) B1690733
theorem B505129 : Blo 295830 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B669167 : Blo 295830 669167 := bstep (se 1 (by rfl) ⟨501875, by rfl⟩ : syracuseStep 669167 = 1003751) B1003751
theorem B538319 : Blo 295830 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B636827 : Blo 295830 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B374959 : Blo 295830 374959 := bstep (se 1 (by rfl) ⟨281219, by rfl⟩ : syracuseStep 374959 = 562439) B562439
theorem B2865415 : Blo 295830 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B2275937 : Blo 295830 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B1129085 : Blo 295830 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B3816557 : Blo 295830 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B4275517 : Blo 295830 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B2538971 : Blo 295830 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B1130057 : Blo 295830 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B2440955 : Blo 295830 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B2703269 : Blo 295830 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B999593 : Blo 295830 999593 := bstep (se 2 (by rfl) ⟨374847, by rfl⟩ : syracuseStep 999593 = 749695) B749695
theorem B672083 : Blo 295830 672083 := bstep (se 1 (by rfl) ⟨504062, by rfl⟩ : syracuseStep 672083 = 1008125) B1008125
theorem B672191 : Blo 295830 672191 := bstep (se 1 (by rfl) ⟨504143, by rfl⟩ : syracuseStep 672191 = 1008287) B1008287
theorem B11616797 : Blo 295830 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B26165861 : Blo 295830 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B1000511 : Blo 295830 1000511 := bstep (se 1 (by rfl) ⟨750383, by rfl⟩ : syracuseStep 1000511 = 1500767) B1500767
theorem B2049185 : Blo 295830 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B673127 : Blo 295830 673127 := bstep (se 1 (by rfl) ⟨504845, by rfl⟩ : syracuseStep 673127 = 1009691) B1009691
theorem B443759 : Blo 295830 443759 := bstep (se 1 (by rfl) ⟨332819, by rfl⟩ : syracuseStep 443759 = 665639) B665639
theorem B1132001 : Blo 295830 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B443879 : Blo 295830 443879 := bstep (se 1 (by rfl) ⟨332909, by rfl⟩ : syracuseStep 443879 = 665819) B665819
theorem B444059 : Blo 295830 444059 := bstep (se 1 (by rfl) ⟨333044, by rfl⟩ : syracuseStep 444059 = 666089) B666089
theorem B477083 : Blo 295830 477083 := bstep (se 1 (by rfl) ⟨357812, by rfl⟩ : syracuseStep 477083 = 715625) B715625
theorem B444647 : Blo 295830 444647 := bstep (se 1 (by rfl) ⟨333485, by rfl⟩ : syracuseStep 444647 = 666971) B666971
theorem B444827 : Blo 295830 444827 := bstep (se 1 (by rfl) ⟨333620, by rfl⟩ : syracuseStep 444827 = 667241) B667241
theorem B674297 : Blo 295830 674297 := bstep (se 2 (by rfl) ⟨252861, by rfl⟩ : syracuseStep 674297 = 505723) B505723
theorem B2247263 : Blo 295830 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B674459 : Blo 295830 674459 := bstep (se 1 (by rfl) ⟨505844, by rfl⟩ : syracuseStep 674459 = 1011689) B1011689
theorem B674495 : Blo 295830 674495 := bstep (se 1 (by rfl) ⟨505871, by rfl⟩ : syracuseStep 674495 = 1011743) B1011743
theorem B445247 : Blo 295830 445247 := bstep (se 1 (by rfl) ⟨333935, by rfl⟩ : syracuseStep 445247 = 667871) B667871
theorem B445577 : Blo 295830 445577 := bstep (se 2 (by rfl) ⟨167091, by rfl⟩ : syracuseStep 445577 = 334183) B334183
theorem B445631 : Blo 295830 445631 := bstep (se 1 (by rfl) ⟨334223, by rfl⟩ : syracuseStep 445631 = 668447) B668447
theorem B445919 : Blo 295830 445919 := bstep (se 1 (by rfl) ⟨334439, by rfl⟩ : syracuseStep 445919 = 668879) B668879
theorem B445979 : Blo 295830 445979 := bstep (se 1 (by rfl) ⟨334484, by rfl⟩ : syracuseStep 445979 = 668969) B668969
theorem B544495 : Blo 295830 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B446399 : Blo 295830 446399 := bstep (se 1 (by rfl) ⟨334799, by rfl⟩ : syracuseStep 446399 = 669599) B669599
theorem B3199027 : Blo 295830 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B3231899 : Blo 295830 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B905593 : Blo 295830 905593 := bstep (se 2 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 905593 = 679195) B679195
theorem B1003967 : Blo 295830 1003967 := bstep (se 1 (by rfl) ⟨752975, by rfl⟩ : syracuseStep 1003967 = 1505951) B1505951
theorem B1004345 : Blo 295830 1004345 := bstep (se 2 (by rfl) ⟨376629, by rfl⟩ : syracuseStep 1004345 = 753259) B753259
theorem B1136375 : Blo 295830 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B1005803 : Blo 295830 1005803 := bstep (se 1 (by rfl) ⟨754352, by rfl⟩ : syracuseStep 1005803 = 1508705) B1508705
theorem B449321 : Blo 295830 449321 := bstep (se 2 (by rfl) ⟨168495, by rfl⟩ : syracuseStep 449321 = 336991) B336991
theorem B1006505 : Blo 295830 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B318431 : Blo 295830 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B842815 : Blo 295830 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B1695289 : Blo 295830 1695289 := bstep (se 2 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 1695289 = 1271467) B1271467
theorem B1138319 : Blo 295830 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B1007261 : Blo 295830 1007261 := bstep (se 3 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 1007261 = 377723) B377723
theorem B876271 : Blo 295830 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B18341639 : Blo 295830 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B100228913 : Blo 295830 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B6480323 : Blo 295830 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B2417309 : Blo 295830 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B2418473 : Blo 295830 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B2156503 : Blo 295830 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B1010825 : Blo 295830 1010825 := bstep (se 2 (by rfl) ⟨379059, by rfl⟩ : syracuseStep 1010825 = 758119) B758119
theorem B1010879 : Blo 295830 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B1699163 : Blo 295830 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B1011419 : Blo 295830 1011419 := bstep (se 1 (by rfl) ⟨758564, by rfl⟩ : syracuseStep 1011419 = 1517129) B1517129
theorem B1208135 : Blo 295830 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B1011581 : Blo 295830 1011581 := bstep (se 3 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 1011581 = 379343) B379343
theorem B749675 : Blo 295830 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B2879869 : Blo 295830 2879869 := bstep (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) B1079951
theorem B2028169 : Blo 295830 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B455335 : Blo 295830 455335 := bstep (se 1 (by rfl) ⟨341501, by rfl⟩ : syracuseStep 455335 = 683003) B683003
theorem B2553119 : Blo 295830 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B1800407 : Blo 295830 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B358735 : Blo 295830 358735 := bstep (se 1 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 358735 = 538103) B538103
theorem B850459 : Blo 295830 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B3046187 : Blo 295830 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B752915 : Blo 295830 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B1441097 : Blo 295830 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B851563 : Blo 295830 851563 := bstep (se 1 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 851563 = 1277345) B1277345
theorem B2850653 : Blo 295830 2850653 := bstep (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) B1068995
theorem B1508219 : Blo 295830 1508219 := bstep (se 1 (by rfl) ⟨1131164, by rfl⟩ : syracuseStep 1508219 = 2262329) B2262329
theorem B295839 : Blo 295830 295839 := bstep (se 1 (by rfl) ⟨221879, by rfl⟩ : syracuseStep 295839 = 443759) B443759
theorem B754667 : Blo 295830 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B295919 : Blo 295830 295919 := bstep (se 1 (by rfl) ⟨221939, by rfl⟩ : syracuseStep 295919 = 443879) B443879
theorem B296039 : Blo 295830 296039 := bstep (se 1 (by rfl) ⟨222029, by rfl⟩ : syracuseStep 296039 = 444059) B444059
theorem B296431 : Blo 295830 296431 := bstep (se 1 (by rfl) ⟨222323, by rfl⟩ : syracuseStep 296431 = 444647) B444647
theorem B296551 : Blo 295830 296551 := bstep (se 1 (by rfl) ⟨222413, by rfl⟩ : syracuseStep 296551 = 444827) B444827
theorem B296831 : Blo 295830 296831 := bstep (se 1 (by rfl) ⟨222623, by rfl⟩ : syracuseStep 296831 = 445247) B445247
theorem B755689 : Blo 295830 755689 := bstep (se 2 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 755689 = 566767) B566767
theorem B297051 : Blo 295830 297051 := bstep (se 1 (by rfl) ⟨222788, by rfl⟩ : syracuseStep 297051 = 445577) B445577
theorem B297087 : Blo 295830 297087 := bstep (se 1 (by rfl) ⟨222815, by rfl⟩ : syracuseStep 297087 = 445631) B445631
theorem B4950245 : Blo 295830 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B297279 : Blo 295830 297279 := bstep (se 1 (by rfl) ⟨222959, by rfl⟩ : syracuseStep 297279 = 445919) B445919
theorem B297319 : Blo 295830 297319 := bstep (se 1 (by rfl) ⟨222989, by rfl⟩ : syracuseStep 297319 = 445979) B445979
theorem B297599 : Blo 295830 297599 := bstep (se 1 (by rfl) ⟨223199, by rfl⟩ : syracuseStep 297599 = 446399) B446399
theorem B3214343 : Blo 295830 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B2428453 : Blo 295830 2428453 := bstep (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) B455335
theorem B757583 : Blo 295830 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B11604343 : Blo 295830 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B299547 : Blo 295830 299547 := bstep (se 1 (by rfl) ⟨224660, by rfl⟩ : syracuseStep 299547 = 449321) B449321
theorem B725993 : Blo 295830 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B758879 : Blo 295830 758879 := bstep (se 1 (by rfl) ⟨569159, by rfl⟩ : syracuseStep 758879 = 1138319) B1138319
theorem B332959 : Blo 295830 332959 := bstep (se 1 (by rfl) ⟨249719, by rfl⟩ : syracuseStep 332959 = 499439) B499439
theorem B12227759 : Blo 295830 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B66819275 : Blo 295830 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B333103 : Blo 295830 333103 := bstep (se 1 (by rfl) ⟨249827, by rfl⟩ : syracuseStep 333103 = 499655) B499655
theorem B4265369 : Blo 295830 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1611539 : Blo 295830 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B3839825 : Blo 295830 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B759721 : Blo 295830 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B1612315 : Blo 295830 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B335263 : Blo 295830 335263 := bstep (se 1 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 335263 = 502895) B502895
theorem B1515347 : Blo 295830 1515347 := bstep (se 1 (by rfl) ⟨1136510, by rfl⟩ : syracuseStep 1515347 = 2273021) B2273021
theorem B499783 : Blo 295830 499783 := bstep (se 1 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 499783 = 749675) B749675
theorem B499945 : Blo 295830 499945 := bstep (se 2 (by rfl) ⟨187479, by rfl⟩ : syracuseStep 499945 = 374959) B374959
theorem B1123753 : Blo 295830 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B1517291 : Blo 295830 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B501943 : Blo 295830 501943 := bstep (se 1 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 501943 = 752915) B752915
theorem B3221693 : Blo 295830 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B960731 : Blo 295830 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B568043 : Blo 295830 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B666395 : Blo 295830 666395 := bstep (se 1 (by rfl) ⟨499796, by rfl⟩ : syracuseStep 666395 = 999593) B999593
theorem B17443907 : Blo 295830 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B667007 : Blo 295830 667007 := bstep (se 1 (by rfl) ⟨500255, by rfl⟩ : syracuseStep 667007 = 1000511) B1000511
theorem B30978125 : Blo 295830 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B9613687 : Blo 295830 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B668537 : Blo 295830 668537 := bstep (se 2 (by rfl) ⟨250701, by rfl⟩ : syracuseStep 668537 = 501403) B501403
theorem B669311 : Blo 295830 669311 := bstep (se 1 (by rfl) ⟨501983, by rfl⟩ : syracuseStep 669311 = 1003967) B1003967
theorem B669563 : Blo 295830 669563 := bstep (se 1 (by rfl) ⟨502172, by rfl⟩ : syracuseStep 669563 = 1004345) B1004345
theorem B1423327 : Blo 295830 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B669833 : Blo 295830 669833 := bstep (se 2 (by rfl) ⟨251187, by rfl⟩ : syracuseStep 669833 = 502375) B502375
theorem B3815585 : Blo 295830 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B670535 : Blo 295830 670535 := bstep (se 1 (by rfl) ⟨502901, by rfl⟩ : syracuseStep 670535 = 1005803) B1005803
theorem B670841 : Blo 295830 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B671003 : Blo 295830 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B671507 : Blo 295830 671507 := bstep (se 1 (by rfl) ⟨503630, by rfl⟩ : syracuseStep 671507 = 1007261) B1007261
theorem B639083 : Blo 295830 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B2704225 : Blo 295830 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B378523 : Blo 295830 378523 := bstep (se 1 (by rfl) ⟨283892, by rfl⟩ : syracuseStep 378523 = 567785) B567785
theorem B673505 : Blo 295830 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B673883 : Blo 295830 673883 := bstep (se 1 (by rfl) ⟨505412, by rfl⟩ : syracuseStep 673883 = 1010825) B1010825
theorem B673919 : Blo 295830 673919 := bstep (se 1 (by rfl) ⟨505439, by rfl⟩ : syracuseStep 673919 = 1010879) B1010879
theorem B1362143 : Blo 295830 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B1132775 : Blo 295830 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B674279 : Blo 295830 674279 := bstep (se 1 (by rfl) ⟨505709, by rfl⟩ : syracuseStep 674279 = 1011419) B1011419
theorem B444983 : Blo 295830 444983 := bstep (se 1 (by rfl) ⟨333737, by rfl⟩ : syracuseStep 444983 = 667475) B667475
theorem B674387 : Blo 295830 674387 := bstep (se 1 (by rfl) ⟨505790, by rfl⟩ : syracuseStep 674387 = 1011581) B1011581
theorem B3820553 : Blo 295830 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B478313 : Blo 295830 478313 := bstep (se 2 (by rfl) ⟨179367, by rfl⟩ : syracuseStep 478313 = 358735) B358735
theorem B1133945 : Blo 295830 1133945 := bstep (se 2 (by rfl) ⟨425229, by rfl⟩ : syracuseStep 1133945 = 850459) B850459
theorem B11292157 : Blo 295830 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B6868513 : Blo 295830 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B446111 : Blo 295830 446111 := bstep (se 1 (by rfl) ⟨334583, by rfl⟩ : syracuseStep 446111 = 669167) B669167
theorem B1200271 : Blo 295830 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B2544371 : Blo 295830 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B1135417 : Blo 295830 1135417 := bstep (se 2 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 1135417 = 851563) B851563
theorem B447353 : Blo 295830 447353 := bstep (se 2 (by rfl) ⟨167757, by rfl⟩ : syracuseStep 447353 = 335515) B335515
theorem B447401 : Blo 295830 447401 := bstep (se 2 (by rfl) ⟨167775, by rfl⟩ : syracuseStep 447401 = 335551) B335551
theorem B1692647 : Blo 295830 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B1168361 : Blo 295830 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B1627303 : Blo 295830 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B448055 : Blo 295830 448055 := bstep (se 1 (by rfl) ⟨336041, by rfl⟩ : syracuseStep 448055 = 672083) B672083
theorem B448127 : Blo 295830 448127 := bstep (se 1 (by rfl) ⟨336095, by rfl⟩ : syracuseStep 448127 = 672191) B672191
theorem B1005695 : Blo 295830 1005695 := bstep (se 1 (by rfl) ⟨754271, by rfl⟩ : syracuseStep 1005695 = 1508543) B1508543
theorem B1136875 : Blo 295830 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B448751 : Blo 295830 448751 := bstep (se 1 (by rfl) ⟨336563, by rfl⟩ : syracuseStep 448751 = 673127) B673127
theorem B318055 : Blo 295830 318055 := bstep (se 1 (by rfl) ⟨238541, by rfl⟩ : syracuseStep 318055 = 477083) B477083
theorem B1498013 : Blo 295830 1498013 := bstep (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) B561755
theorem B449531 : Blo 295830 449531 := bstep (se 1 (by rfl) ⟨337148, by rfl⟩ : syracuseStep 449531 = 674297) B674297
theorem B1498175 : Blo 295830 1498175 := bstep (se 1 (by rfl) ⟨1123631, by rfl⟩ : syracuseStep 1498175 = 2247263) B2247263
theorem B449639 : Blo 295830 449639 := bstep (se 1 (by rfl) ⟨337229, by rfl⟩ : syracuseStep 449639 = 674459) B674459
theorem B449663 : Blo 295830 449663 := bstep (se 1 (by rfl) ⟨337247, by rfl⟩ : syracuseStep 449663 = 674495) B674495
theorem B1007369 : Blo 295830 1007369 := bstep (se 2 (by rfl) ⟨377763, by rfl⟩ : syracuseStep 1007369 = 755527) B755527
theorem B1007423 : Blo 295830 1007423 := bstep (se 1 (by rfl) ⟨755567, by rfl⟩ : syracuseStep 1007423 = 1511135) B1511135
theorem B2875337 : Blo 295830 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B2154599 : Blo 295830 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B680363 : Blo 295830 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B5464493 : Blo 295830 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B1008233 : Blo 295830 1008233 := bstep (se 2 (by rfl) ⟨378087, by rfl⟩ : syracuseStep 1008233 = 756175) B756175
theorem B1500281 : Blo 295830 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B12346663 : Blo 295830 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B11494871 : Blo 295830 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B1009529 : Blo 295830 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B1730807 : Blo 295830 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1009961 : Blo 295830 1009961 := bstep (se 2 (by rfl) ⟨378735, by rfl⟩ : syracuseStep 1009961 = 757471) B757471
theorem B1698205 : Blo 295830 1698205 := bstep (se 3 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 1698205 = 636827) B636827
theorem B3205777 : Blo 295830 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B4320215 : Blo 295830 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B1207457 : Blo 295830 1207457 := bstep (se 2 (by rfl) ⟨452796, by rfl⟩ : syracuseStep 1207457 = 905593) B905593
theorem B2584009 : Blo 295830 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B1502873 : Blo 295830 1502873 := bstep (se 2 (by rfl) ⟨563577, by rfl⟩ : syracuseStep 1502873 = 1127155) B1127155
theorem B2846927 : Blo 295830 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B422695 : Blo 295830 422695 := bstep (se 1 (by rfl) ⟨317021, by rfl⟩ : syracuseStep 422695 = 634043) B634043
theorem B422815 : Blo 295830 422815 := bstep (se 1 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 422815 = 634223) B634223
theorem B750617 : Blo 295830 750617 := bstep (se 2 (by rfl) ⟨281481, by rfl⟩ : syracuseStep 750617 = 562963) B562963
theorem B750779 : Blo 295830 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B849149 : Blo 295830 849149 := bstep (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) B318431
theorem B751103 : Blo 295830 751103 := bstep (se 1 (by rfl) ⟨563327, by rfl⟩ : syracuseStep 751103 = 1126655) B1126655
theorem B1702079 : Blo 295830 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B358879 : Blo 295830 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B5700689 : Blo 295830 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B752723 : Blo 295830 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B2030791 : Blo 295830 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B2260385 : Blo 295830 2260385 := bstep (se 2 (by rfl) ⟨847644, by rfl⟩ : syracuseStep 2260385 = 1695289) B1695289
theorem B753371 : Blo 295830 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B1900435 : Blo 295830 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B1802179 : Blo 295830 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B426055 : Blo 295830 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B3605633 : Blo 295830 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B755183 : Blo 295830 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B296655 : Blo 295830 296655 := bstep (se 1 (by rfl) ⟨222491, by rfl⟩ : syracuseStep 296655 = 444983) B444983
theorem B755963 : Blo 295830 755963 := bstep (se 1 (by rfl) ⟨566972, by rfl⟩ : syracuseStep 755963 = 1133945) B1133945
theorem B297407 : Blo 295830 297407 := bstep (se 1 (by rfl) ⟨223055, by rfl⟩ : syracuseStep 297407 = 446111) B446111
theorem B2264273 : Blo 295830 2264273 := bstep (se 2 (by rfl) ⟨849102, by rfl⟩ : syracuseStep 2264273 = 1698205) B1698205
theorem B298235 : Blo 295830 298235 := bstep (se 1 (by rfl) ⟨223676, by rfl⟩ : syracuseStep 298235 = 447353) B447353
theorem B298267 : Blo 295830 298267 := bstep (se 1 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 298267 = 447401) B447401
theorem B298703 : Blo 295830 298703 := bstep (se 1 (by rfl) ⟨224027, by rfl⟩ : syracuseStep 298703 = 448055) B448055
theorem B298751 : Blo 295830 298751 := bstep (se 1 (by rfl) ⟨224063, by rfl⟩ : syracuseStep 298751 = 448127) B448127
theorem B2559883 : Blo 295830 2559883 := bstep (se 1 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 2559883 = 3839825) B3839825
theorem B299167 : Blo 295830 299167 := bstep (se 1 (by rfl) ⟨224375, by rfl⟩ : syracuseStep 299167 = 448751) B448751
theorem B3445345 : Blo 295830 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B299687 : Blo 295830 299687 := bstep (se 1 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 299687 = 449531) B449531
theorem B299759 : Blo 295830 299759 := bstep (se 1 (by rfl) ⟨224819, by rfl⟩ : syracuseStep 299759 = 449639) B449639
theorem B299775 : Blo 295830 299775 := bstep (se 1 (by rfl) ⟨224831, by rfl⟩ : syracuseStep 299775 = 449663) B449663
theorem B3642995 : Blo 295830 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B12818249 : Blo 295830 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B15472457 : Blo 295830 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B563593 : Blo 295830 563593 := bstep (se 2 (by rfl) ⟨211347, by rfl⟩ : syracuseStep 563593 = 422695) B422695
theorem B1513889 : Blo 295830 1513889 := bstep (se 2 (by rfl) ⟨567708, by rfl⟩ : syracuseStep 1513889 = 1135417) B1135417
theorem B563753 : Blo 295830 563753 := bstep (se 2 (by rfl) ⟨211407, by rfl⟩ : syracuseStep 563753 = 422815) B422815
theorem B1153871 : Blo 295830 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B2169737 : Blo 295830 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B20652083 : Blo 295830 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B1515833 : Blo 295830 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B500411 : Blo 295830 500411 := bstep (se 1 (by rfl) ⟨375308, by rfl⟩ : syracuseStep 500411 = 750617) B750617
theorem B500519 : Blo 295830 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B566099 : Blo 295830 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B500735 : Blo 295830 500735 := bstep (se 1 (by rfl) ⟨375551, by rfl⟩ : syracuseStep 500735 = 751103) B751103
theorem B501815 : Blo 295830 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B502247 : Blo 295830 502247 := bstep (se 1 (by rfl) ⟨376685, by rfl⟩ : syracuseStep 502247 = 753371) B753371
theorem B2533913 : Blo 295830 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B2402905 : Blo 295830 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B666377 : Blo 295830 666377 := bstep (se 2 (by rfl) ⟨249891, by rfl⟩ : syracuseStep 666377 = 499783) B499783
theorem B666593 : Blo 295830 666593 := bstep (se 2 (by rfl) ⟨249972, by rfl⟩ : syracuseStep 666593 = 499945) B499945
theorem B503111 : Blo 295830 503111 := bstep (se 1 (by rfl) ⟨377333, by rfl⟩ : syracuseStep 503111 = 754667) B754667
theorem B16462217 : Blo 295830 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B2142895 : Blo 295830 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B504697 : Blo 295830 504697 := bstep (se 2 (by rfl) ⟨189261, by rfl⟩ : syracuseStep 504697 = 378523) B378523
theorem B505055 : Blo 295830 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B669257 : Blo 295830 669257 := bstep (se 2 (by rfl) ⟨250971, by rfl⟩ : syracuseStep 669257 = 501943) B501943
theorem B1128431 : Blo 295830 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B505919 : Blo 295830 505919 := bstep (se 1 (by rfl) ⟨379439, by rfl⟩ : syracuseStep 505919 = 758879) B758879
theorem B44546183 : Blo 295830 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B4274369 : Blo 295830 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B670463 : Blo 295830 670463 := bstep (se 1 (by rfl) ⟨502847, by rfl⟩ : syracuseStep 670463 = 1005695) B1005695
theorem B998675 : Blo 295830 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B15056209 : Blo 295830 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B998783 : Blo 295830 998783 := bstep (se 1 (by rfl) ⟨749087, by rfl⟩ : syracuseStep 998783 = 1498175) B1498175
theorem B9158017 : Blo 295830 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B671579 : Blo 295830 671579 := bstep (se 1 (by rfl) ⟨503684, by rfl⟩ : syracuseStep 671579 = 1007369) B1007369
theorem B671615 : Blo 295830 671615 := bstep (se 1 (by rfl) ⟨503711, by rfl⟩ : syracuseStep 671615 = 1007423) B1007423
theorem B1916891 : Blo 295830 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B672155 : Blo 295830 672155 := bstep (se 1 (by rfl) ⟨504116, by rfl⟩ : syracuseStep 672155 = 1008233) B1008233
theorem B1000187 : Blo 295830 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B673019 : Blo 295830 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B2147795 : Blo 295830 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B640487 : Blo 295830 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B673307 : Blo 295830 673307 := bstep (se 1 (by rfl) ⟨504980, by rfl⟩ : syracuseStep 673307 = 1009961) B1009961
theorem B443945 : Blo 295830 443945 := bstep (se 2 (by rfl) ⟨166479, by rfl⟩ : syracuseStep 443945 = 332959) B332959
theorem B444137 : Blo 295830 444137 := bstep (se 2 (by rfl) ⟨166551, by rfl⟩ : syracuseStep 444137 = 333103) B333103
theorem B378695 : Blo 295830 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B444263 : Blo 295830 444263 := bstep (se 1 (by rfl) ⟨333197, by rfl⟩ : syracuseStep 444263 = 666395) B666395
theorem B804971 : Blo 295830 804971 := bstep (se 1 (by rfl) ⟨603728, by rfl⟩ : syracuseStep 804971 = 1207457) B1207457
theorem B444671 : Blo 295830 444671 := bstep (se 1 (by rfl) ⟨333503, by rfl⟩ : syracuseStep 444671 = 667007) B667007
theorem B1001915 : Blo 295830 1001915 := bstep (se 1 (by rfl) ⟨751436, by rfl⟩ : syracuseStep 1001915 = 1502873) B1502873
theorem B445691 : Blo 295830 445691 := bstep (se 1 (by rfl) ⟨334268, by rfl⟩ : syracuseStep 445691 = 668537) B668537
theorem B478505 : Blo 295830 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B2149753 : Blo 295830 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B446207 : Blo 295830 446207 := bstep (se 1 (by rfl) ⟨334655, by rfl⟩ : syracuseStep 446207 = 669311) B669311
theorem B446375 : Blo 295830 446375 := bstep (se 1 (by rfl) ⟨334781, by rfl⟩ : syracuseStep 446375 = 669563) B669563
theorem B446555 : Blo 295830 446555 := bstep (se 1 (by rfl) ⟨334916, by rfl⟩ : syracuseStep 446555 = 669833) B669833
theorem B2543723 : Blo 295830 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B1134719 : Blo 295830 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B2707721 : Blo 295830 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B447017 : Blo 295830 447017 := bstep (se 2 (by rfl) ⟨167631, by rfl⟩ : syracuseStep 447017 = 335263) B335263
theorem B447023 : Blo 295830 447023 := bstep (se 1 (by rfl) ⟨335267, by rfl⟩ : syracuseStep 447023 = 670535) B670535
theorem B447227 : Blo 295830 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B447335 : Blo 295830 447335 := bstep (se 1 (by rfl) ⟨335501, by rfl⟩ : syracuseStep 447335 = 671003) B671003
theorem B447671 : Blo 295830 447671 := bstep (se 1 (by rfl) ⟨335753, by rfl⟩ : syracuseStep 447671 = 671507) B671507
theorem B1005479 : Blo 295830 1005479 := bstep (se 1 (by rfl) ⟨754109, by rfl⟩ : syracuseStep 1005479 = 1508219) B1508219
theorem B449003 : Blo 295830 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B449255 : Blo 295830 449255 := bstep (se 1 (by rfl) ⟨336941, by rfl⟩ : syracuseStep 449255 = 673883) B673883
theorem B449279 : Blo 295830 449279 := bstep (se 1 (by rfl) ⟨336959, by rfl⟩ : syracuseStep 449279 = 673919) B673919
theorem B908095 : Blo 295830 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B449519 : Blo 295830 449519 := bstep (se 1 (by rfl) ⟨337139, by rfl⟩ : syracuseStep 449519 = 674279) B674279
theorem B449591 : Blo 295830 449591 := bstep (se 1 (by rfl) ⟨337193, by rfl⟩ : syracuseStep 449591 = 674387) B674387
theorem B1498337 : Blo 295830 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B2547035 : Blo 295830 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B318875 : Blo 295830 318875 := bstep (se 1 (by rfl) ⟨239156, by rfl⟩ : syracuseStep 318875 = 478313) B478313
theorem B1007585 : Blo 295830 1007585 := bstep (se 2 (by rfl) ⟨377844, by rfl⟩ : syracuseStep 1007585 = 755689) B755689
theorem B1696247 : Blo 295830 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B483995 : Blo 295830 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B778907 : Blo 295830 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B8151839 : Blo 295830 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B2843579 : Blo 295830 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1074359 : Blo 295830 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B3237937 : Blo 295830 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1010231 : Blo 295830 1010231 := bstep (se 1 (by rfl) ⟨757673, by rfl⟩ : syracuseStep 1010231 = 1515347) B1515347
theorem B1436399 : Blo 295830 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B1600361 : Blo 295830 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B453575 : Blo 295830 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B13200653 : Blo 295830 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B7663247 : Blo 295830 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B1011527 : Blo 295830 1011527 := bstep (se 1 (by rfl) ⟨758645, by rfl⟩ : syracuseStep 1011527 = 1517291) B1517291
theorem B2880143 : Blo 295830 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B11629271 : Blo 295830 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B1012961 : Blo 295830 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B1897769 : Blo 295830 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B1897951 : Blo 295830 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B424073 : Blo 295830 424073 := bstep (se 2 (by rfl) ⟨159027, by rfl⟩ : syracuseStep 424073 = 318055) B318055
theorem B3800459 : Blo 295830 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B1506923 : Blo 295830 1506923 := bstep (se 1 (by rfl) ⟨1130192, by rfl⟩ : syracuseStep 1506923 = 2260385) B2260385
theorem B17268997 : Blo 295830 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B295963 : Blo 295830 295963 := bstep (se 1 (by rfl) ⟨221972, by rfl⟩ : syracuseStep 295963 = 443945) B443945
theorem B296091 : Blo 295830 296091 := bstep (se 1 (by rfl) ⟨222068, by rfl⟩ : syracuseStep 296091 = 444137) B444137
theorem B296175 : Blo 295830 296175 := bstep (se 1 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 296175 = 444263) B444263
theorem B296447 : Blo 295830 296447 := bstep (se 1 (by rfl) ⟨222335, by rfl⟩ : syracuseStep 296447 = 444671) B444671
theorem B1509515 : Blo 295830 1509515 := bstep (se 1 (by rfl) ⟨1132136, by rfl⟩ : syracuseStep 1509515 = 2264273) B2264273
theorem B297127 : Blo 295830 297127 := bstep (se 1 (by rfl) ⟨222845, by rfl⟩ : syracuseStep 297127 = 445691) B445691
theorem B297471 : Blo 295830 297471 := bstep (se 1 (by rfl) ⟨223103, by rfl⟩ : syracuseStep 297471 = 446207) B446207
theorem B297583 : Blo 295830 297583 := bstep (se 1 (by rfl) ⟨223187, by rfl⟩ : syracuseStep 297583 = 446375) B446375
theorem B297703 : Blo 295830 297703 := bstep (se 1 (by rfl) ⟨223277, by rfl⟩ : syracuseStep 297703 = 446555) B446555
theorem B756479 : Blo 295830 756479 := bstep (se 1 (by rfl) ⟨567359, by rfl⟩ : syracuseStep 756479 = 1134719) B1134719
theorem B1805147 : Blo 295830 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B298011 : Blo 295830 298011 := bstep (se 1 (by rfl) ⟨223508, by rfl⟩ : syracuseStep 298011 = 447017) B447017
theorem B298015 : Blo 295830 298015 := bstep (se 1 (by rfl) ⟨223511, by rfl⟩ : syracuseStep 298015 = 447023) B447023
theorem B298151 : Blo 295830 298151 := bstep (se 1 (by rfl) ⟨223613, by rfl⟩ : syracuseStep 298151 = 447227) B447227
theorem B298223 : Blo 295830 298223 := bstep (se 1 (by rfl) ⟨223667, by rfl⟩ : syracuseStep 298223 = 447335) B447335
theorem B298447 : Blo 295830 298447 := bstep (se 1 (by rfl) ⟨223835, by rfl⟩ : syracuseStep 298447 = 447671) B447671
theorem B2428663 : Blo 295830 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B1707965 : Blo 295830 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B299335 : Blo 295830 299335 := bstep (se 1 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 299335 = 449003) B449003
theorem B299503 : Blo 295830 299503 := bstep (se 1 (by rfl) ⟨224627, by rfl⟩ : syracuseStep 299503 = 449255) B449255
theorem B299519 : Blo 295830 299519 := bstep (se 1 (by rfl) ⟨224639, by rfl⟩ : syracuseStep 299519 = 449279) B449279
theorem B1446491 : Blo 295830 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B299679 : Blo 295830 299679 := bstep (se 1 (by rfl) ⟨224759, by rfl⟩ : syracuseStep 299679 = 449519) B449519
theorem B299727 : Blo 295830 299727 := bstep (se 1 (by rfl) ⟨224795, by rfl⟩ : syracuseStep 299727 = 449591) B449591
theorem B3413177 : Blo 295830 3413177 := bstep (se 2 (by rfl) ⟨1279941, by rfl⟩ : syracuseStep 3413177 = 2559883) B2559883
theorem B13768055 : Blo 295830 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B333607 : Blo 295830 333607 := bstep (se 1 (by rfl) ⟨250205, by rfl⟩ : syracuseStep 333607 = 500411) B500411
theorem B333679 : Blo 295830 333679 := bstep (se 1 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 333679 = 500519) B500519
theorem B333823 : Blo 295830 333823 := bstep (se 1 (by rfl) ⟨250367, by rfl⟩ : syracuseStep 333823 = 500735) B500735
theorem B4593793 : Blo 295830 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B2857193 : Blo 295830 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B334543 : Blo 295830 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B334831 : Blo 295830 334831 := bstep (se 1 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 334831 = 502247) B502247
theorem B957599 : Blo 295830 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B2530601 : Blo 295830 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B302383 : Blo 295830 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B335407 : Blo 295830 335407 := bstep (se 1 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 335407 = 503111) B503111
theorem B336703 : Blo 295830 336703 := bstep (se 1 (by rfl) ⟨252527, by rfl⟩ : syracuseStep 336703 = 505055) B505055
theorem B337279 : Blo 295830 337279 := bstep (se 1 (by rfl) ⟨252959, by rfl⟩ : syracuseStep 337279 = 505919) B505919
theorem B29697455 : Blo 295830 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B665783 : Blo 295830 665783 := bstep (se 1 (by rfl) ⟨499337, by rfl⟩ : syracuseStep 665783 = 998675) B998675
theorem B665855 : Blo 295830 665855 := bstep (se 1 (by rfl) ⟨499391, by rfl⟩ : syracuseStep 665855 = 998783) B998783
theorem B2533639 : Blo 295830 2533639 := bstep (se 1 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 2533639 = 3800459) B3800459
theorem B568073 : Blo 295830 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B666791 : Blo 295830 666791 := bstep (se 1 (by rfl) ⟨500093, by rfl⟩ : syracuseStep 666791 = 1000187) B1000187
theorem B2403755 : Blo 295830 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B503455 : Blo 295830 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B536647 : Blo 295830 536647 := bstep (se 1 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 536647 = 804971) B804971
theorem B503975 : Blo 295830 503975 := bstep (se 1 (by rfl) ⟨377981, by rfl⟩ : syracuseStep 503975 = 755963) B755963
theorem B667943 : Blo 295830 667943 := bstep (se 1 (by rfl) ⟨500957, by rfl⟩ : syracuseStep 667943 = 1001915) B1001915
theorem B1290653 : Blo 295830 1290653 := bstep (se 3 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 1290653 = 483995) B483995
theorem B2077085 : Blo 295830 2077085 := bstep (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) B778907
theorem B5060717 : Blo 295830 5060717 := bstep (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) B1897769
theorem B670319 : Blo 295830 670319 := bstep (se 1 (by rfl) ⟨502739, by rfl⟩ : syracuseStep 670319 = 1005479) B1005479
theorem B375835 : Blo 295830 375835 := bstep (se 1 (by rfl) ⟨281876, by rfl⟩ : syracuseStep 375835 = 563753) B563753
theorem B2866337 : Blo 295830 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B769247 : Blo 295830 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B998891 : Blo 295830 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B671723 : Blo 295830 671723 := bstep (se 1 (by rfl) ⟨503792, by rfl⟩ : syracuseStep 671723 = 1007585) B1007585
theorem B1130831 : Blo 295830 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B1130861 : Blo 295830 1130861 := bstep (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) B424073
theorem B377399 : Blo 295830 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B672929 : Blo 295830 672929 := bstep (se 2 (by rfl) ⟨252348, by rfl⟩ : syracuseStep 672929 = 504697) B504697
theorem B1689275 : Blo 295830 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B673487 : Blo 295830 673487 := bstep (se 1 (by rfl) ⟨505115, by rfl⟩ : syracuseStep 673487 = 1010231) B1010231
theorem B80299781 : Blo 295830 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B444251 : Blo 295830 444251 := bstep (se 1 (by rfl) ⟨333188, by rfl⟩ : syracuseStep 444251 = 666377) B666377
theorem B1066907 : Blo 295830 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B444395 : Blo 295830 444395 := bstep (se 1 (by rfl) ⟨333296, by rfl⟩ : syracuseStep 444395 = 666593) B666593
theorem B8800435 : Blo 295830 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B674351 : Blo 295830 674351 := bstep (se 1 (by rfl) ⟨505763, by rfl⟩ : syracuseStep 674351 = 1011527) B1011527
theorem B1920095 : Blo 295830 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B7752847 : Blo 295830 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B675307 : Blo 295830 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B446171 : Blo 295830 446171 := bstep (se 1 (by rfl) ⟨334628, by rfl⟩ : syracuseStep 446171 = 669257) B669257
theorem B446975 : Blo 295830 446975 := bstep (se 1 (by rfl) ⟨335231, by rfl⟩ : syracuseStep 446975 = 670463) B670463
theorem B12210689 : Blo 295830 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1004615 : Blo 295830 1004615 := bstep (se 1 (by rfl) ⟨753461, by rfl⟩ : syracuseStep 1004615 = 1506923) B1506923
theorem B447719 : Blo 295830 447719 := bstep (se 1 (by rfl) ⟨335789, by rfl⟩ : syracuseStep 447719 = 671579) B671579
theorem B447743 : Blo 295830 447743 := bstep (se 1 (by rfl) ⟨335807, by rfl⟩ : syracuseStep 447743 = 671615) B671615
theorem B448103 : Blo 295830 448103 := bstep (se 1 (by rfl) ⟨336077, by rfl⟩ : syracuseStep 448103 = 672155) B672155
theorem B448679 : Blo 295830 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B1431863 : Blo 295830 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B448871 : Blo 295830 448871 := bstep (se 1 (by rfl) ⟨336653, by rfl⟩ : syracuseStep 448871 = 673307) B673307
theorem B1695815 : Blo 295830 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B3203873 : Blo 295830 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B8545499 : Blo 295830 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B10314971 : Blo 295830 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B1009259 : Blo 295830 1009259 := bstep (se 1 (by rfl) ⟨756944, by rfl⟩ : syracuseStep 1009259 = 1513889) B1513889
theorem B1009853 : Blo 295830 1009853 := bstep (se 3 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 1009853 = 378695) B378695
theorem B1698023 : Blo 295830 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B1010555 : Blo 295830 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B5434559 : Blo 295830 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1895719 : Blo 295830 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B716239 : Blo 295830 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B5108831 : Blo 295830 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B10974811 : Blo 295830 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B751457 : Blo 295830 751457 := bstep (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) B563593
theorem B1276013 : Blo 295830 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B850333 : Blo 295830 850333 := bstep (se 3 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 850333 = 318875) B318875
theorem B1210793 : Blo 295830 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B752287 : Blo 295830 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B2849579 : Blo 295830 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B1277927 : Blo 295830 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B753887 : Blo 295830 753887 := bstep (se 1 (by rfl) ⟨565415, by rfl⟩ : syracuseStep 753887 = 1130831) B1130831
theorem B753907 : Blo 295830 753907 := bstep (se 1 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 753907 = 1130861) B1130861
theorem B5538893 : Blo 295830 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B296167 : Blo 295830 296167 := bstep (se 1 (by rfl) ⟨222125, by rfl⟩ : syracuseStep 296167 = 444251) B444251
theorem B296263 : Blo 295830 296263 := bstep (se 1 (by rfl) ⟨222197, by rfl⟩ : syracuseStep 296263 = 444395) B444395
theorem B1280063 : Blo 295830 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B297447 : Blo 295830 297447 := bstep (se 1 (by rfl) ⟨223085, by rfl⟩ : syracuseStep 297447 = 446171) B446171
theorem B11733913 : Blo 295830 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B297983 : Blo 295830 297983 := bstep (se 1 (by rfl) ⟨223487, by rfl⟩ : syracuseStep 297983 = 446975) B446975
theorem B3378185 : Blo 295830 3378185 := bstep (se 2 (by rfl) ⟨1266819, by rfl⟩ : syracuseStep 3378185 = 2533639) B2533639
theorem B298479 : Blo 295830 298479 := bstep (se 1 (by rfl) ⟨223859, by rfl⟩ : syracuseStep 298479 = 447719) B447719
theorem B298495 : Blo 295830 298495 := bstep (se 1 (by rfl) ⟨223871, by rfl⟩ : syracuseStep 298495 = 447743) B447743
theorem B9178703 : Blo 295830 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B298735 : Blo 295830 298735 := bstep (se 1 (by rfl) ⟨224051, by rfl⟩ : syracuseStep 298735 = 448103) B448103
theorem B299119 : Blo 295830 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B1904795 : Blo 295830 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B954575 : Blo 295830 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B299247 : Blo 295830 299247 := bstep (se 1 (by rfl) ⟨224435, by rfl⟩ : syracuseStep 299247 = 448871) B448871
theorem B2527625 : Blo 295830 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B12915125 : Blo 295830 12915125 := bstep (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) B1210793
theorem B954985 : Blo 295830 954985 := bstep (se 2 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 954985 = 716239) B716239
theorem B2135915 : Blo 295830 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B1612709 : Blo 295830 1612709 := bstep (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) B302383
theorem B1514861 : Blo 295830 1514861 := bstep (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) B568073
theorem B335983 : Blo 295830 335983 := bstep (se 1 (by rfl) ⟨251987, by rfl⟩ : syracuseStep 335983 = 503975) B503975
theorem B860435 : Blo 295830 860435 := bstep (se 1 (by rfl) ⟨645326, by rfl⟩ : syracuseStep 860435 = 1290653) B1290653
theorem B500971 : Blo 295830 500971 := bstep (se 1 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 500971 = 751457) B751457
theorem B501113 : Blo 295830 501113 := bstep (se 2 (by rfl) ⟨187917, by rfl⟩ : syracuseStep 501113 = 375835) B375835
theorem B1910891 : Blo 295830 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B665927 : Blo 295830 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B1126183 : Blo 295830 1126183 := bstep (se 1 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 1126183 = 1689275) B1689275
theorem B504319 : Blo 295830 504319 := bstep (se 1 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 504319 = 756479) B756479
theorem B8140459 : Blo 295830 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B964327 : Blo 295830 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B669743 : Blo 295830 669743 := bstep (se 1 (by rfl) ⟨502307, by rfl⟩ : syracuseStep 669743 = 1004615) B1004615
theorem B2275451 : Blo 295830 2275451 := bstep (se 1 (by rfl) ⟨1706588, by rfl⟩ : syracuseStep 2275451 = 3413177) B3413177
theorem B10337129 : Blo 295830 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B900409 : Blo 295830 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B638399 : Blo 295830 638399 := bstep (se 1 (by rfl) ⟨478799, by rfl⟩ : syracuseStep 638399 = 957599) B957599
theorem B1687067 : Blo 295830 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B671273 : Blo 295830 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B1130543 : Blo 295830 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B672839 : Blo 295830 672839 := bstep (se 1 (by rfl) ⟨504629, by rfl⟩ : syracuseStep 672839 = 1009259) B1009259
theorem B443855 : Blo 295830 443855 := bstep (se 1 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 443855 = 665783) B665783
theorem B673235 : Blo 295830 673235 := bstep (se 1 (by rfl) ⟨504926, by rfl⟩ : syracuseStep 673235 = 1009853) B1009853
theorem B1132015 : Blo 295830 1132015 := bstep (se 1 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 1132015 = 1698023) B1698023
theorem B443903 : Blo 295830 443903 := bstep (se 1 (by rfl) ⟨332927, by rfl⟩ : syracuseStep 443903 = 665855) B665855
theorem B673703 : Blo 295830 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B444527 : Blo 295830 444527 := bstep (se 1 (by rfl) ⟨333395, by rfl⟩ : syracuseStep 444527 = 666791) B666791
theorem B14633081 : Blo 295830 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B3623039 : Blo 295830 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B444809 : Blo 295830 444809 := bstep (se 2 (by rfl) ⟨166803, by rfl⟩ : syracuseStep 444809 = 333607) B333607
theorem B444905 : Blo 295830 444905 := bstep (se 2 (by rfl) ⟨166839, by rfl⟩ : syracuseStep 444905 = 333679) B333679
theorem B445097 : Blo 295830 445097 := bstep (se 2 (by rfl) ⟨166911, by rfl⟩ : syracuseStep 445097 = 333823) B333823
theorem B445295 : Blo 295830 445295 := bstep (se 1 (by rfl) ⟨333971, by rfl⟩ : syracuseStep 445295 = 667943) B667943
theorem B1133777 : Blo 295830 1133777 := bstep (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) B850333
theorem B1003049 : Blo 295830 1003049 := bstep (se 2 (by rfl) ⟨376143, by rfl⟩ : syracuseStep 1003049 = 752287) B752287
theorem B446057 : Blo 295830 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B446441 : Blo 295830 446441 := bstep (se 2 (by rfl) ⟨167415, by rfl⟩ : syracuseStep 446441 = 334831) B334831
theorem B446879 : Blo 295830 446879 := bstep (se 1 (by rfl) ⟨335159, by rfl⟩ : syracuseStep 446879 = 670319) B670319
theorem B447209 : Blo 295830 447209 := bstep (se 2 (by rfl) ⟨167703, by rfl⟩ : syracuseStep 447209 = 335407) B335407
theorem B512831 : Blo 295830 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B447815 : Blo 295830 447815 := bstep (se 1 (by rfl) ⟨335861, by rfl⟩ : syracuseStep 447815 = 671723) B671723
theorem B23025329 : Blo 295830 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B448619 : Blo 295830 448619 := bstep (se 1 (by rfl) ⟨336464, by rfl⟩ : syracuseStep 448619 = 672929) B672929
theorem B448937 : Blo 295830 448937 := bstep (se 2 (by rfl) ⟨168351, by rfl⟩ : syracuseStep 448937 = 336703) B336703
theorem B448991 : Blo 295830 448991 := bstep (se 1 (by rfl) ⟨336743, by rfl⟩ : syracuseStep 448991 = 673487) B673487
theorem B53533187 : Blo 295830 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B711271 : Blo 295830 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1006343 : Blo 295830 1006343 := bstep (se 1 (by rfl) ⟨754757, by rfl⟩ : syracuseStep 1006343 = 1509515) B1509515
theorem B1006397 : Blo 295830 1006397 := bstep (se 3 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 1006397 = 377399) B377399
theorem B449567 : Blo 295830 449567 := bstep (se 1 (by rfl) ⟨337175, by rfl⟩ : syracuseStep 449567 = 674351) B674351
theorem B449705 : Blo 295830 449705 := bstep (se 2 (by rfl) ⟨168639, by rfl⟩ : syracuseStep 449705 = 337279) B337279
theorem B1203431 : Blo 295830 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1138643 : Blo 295830 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B79193213 : Blo 295830 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B3238217 : Blo 295830 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B715529 : Blo 295830 715529 := bstep (se 2 (by rfl) ⟨268323, by rfl⟩ : syracuseStep 715529 = 536647) B536647
theorem B5696999 : Blo 295830 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B6876647 : Blo 295830 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B1602503 : Blo 295830 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B6125057 : Blo 295830 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B3405887 : Blo 295830 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B3373811 : Blo 295830 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B850675 : Blo 295830 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1899719 : Blo 295830 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B851951 : Blo 295830 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B753695 : Blo 295830 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B59081525 : Blo 295830 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B295903 : Blo 295830 295903 := bstep (se 1 (by rfl) ⟨221927, by rfl⟩ : syracuseStep 295903 = 443855) B443855
theorem B295935 : Blo 295830 295935 := bstep (se 1 (by rfl) ⟨221951, by rfl⟩ : syracuseStep 295935 = 443903) B443903
theorem B853375 : Blo 295830 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B296351 : Blo 295830 296351 := bstep (se 1 (by rfl) ⟨222263, by rfl⟩ : syracuseStep 296351 = 444527) B444527
theorem B296539 : Blo 295830 296539 := bstep (se 1 (by rfl) ⟨222404, by rfl⟩ : syracuseStep 296539 = 444809) B444809
theorem B296603 : Blo 295830 296603 := bstep (se 1 (by rfl) ⟨222452, by rfl⟩ : syracuseStep 296603 = 444905) B444905
theorem B296731 : Blo 295830 296731 := bstep (se 1 (by rfl) ⟨222548, by rfl⟩ : syracuseStep 296731 = 445097) B445097
theorem B296863 : Blo 295830 296863 := bstep (se 1 (by rfl) ⟨222647, by rfl⟩ : syracuseStep 296863 = 445295) B445295
theorem B1509353 : Blo 295830 1509353 := bstep (se 2 (by rfl) ⟨566007, by rfl⟩ : syracuseStep 1509353 = 1132015) B1132015
theorem B755851 : Blo 295830 755851 := bstep (se 1 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 755851 = 1133777) B1133777
theorem B297371 : Blo 295830 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B297627 : Blo 295830 297627 := bstep (se 1 (by rfl) ⟨223220, by rfl⟩ : syracuseStep 297627 = 446441) B446441
theorem B297919 : Blo 295830 297919 := bstep (se 1 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 297919 = 446879) B446879
theorem B298139 : Blo 295830 298139 := bstep (se 1 (by rfl) ⟨223604, by rfl⟩ : syracuseStep 298139 = 447209) B447209
theorem B298543 : Blo 295830 298543 := bstep (se 1 (by rfl) ⟨223907, by rfl⟩ : syracuseStep 298543 = 447815) B447815
theorem B299079 : Blo 295830 299079 := bstep (se 1 (by rfl) ⟨224309, by rfl⟩ : syracuseStep 299079 = 448619) B448619
theorem B299291 : Blo 295830 299291 := bstep (se 1 (by rfl) ⟨224468, by rfl⟩ : syracuseStep 299291 = 448937) B448937
theorem B299327 : Blo 295830 299327 := bstep (se 1 (by rfl) ⟨224495, by rfl⟩ : syracuseStep 299327 = 448991) B448991
theorem B35688791 : Blo 295830 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B299711 : Blo 295830 299711 := bstep (se 1 (by rfl) ⟨224783, by rfl⟩ : syracuseStep 299711 = 449567) B449567
theorem B299803 : Blo 295830 299803 := bstep (se 1 (by rfl) ⟨224852, by rfl⟩ : syracuseStep 299803 = 449705) B449705
theorem B759095 : Blo 295830 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B52795475 : Blo 295830 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B334075 : Blo 295830 334075 := bstep (se 1 (by rfl) ⟨250556, by rfl⟩ : syracuseStep 334075 = 501113) B501113
theorem B10853945 : Blo 295830 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B1285769 : Blo 295830 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B2270591 : Blo 295830 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B1516967 : Blo 295830 1516967 := bstep (se 1 (by rfl) ⟨1137725, by rfl⟩ : syracuseStep 1516967 = 2275451) B2275451
theorem B6891419 : Blo 295830 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B1124711 : Blo 295830 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B567967 : Blo 295830 567967 := bstep (se 1 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 567967 = 851951) B851951
theorem B502591 : Blo 295830 502591 := bstep (se 1 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 502591 = 753887) B753887
theorem B667961 : Blo 295830 667961 := bstep (se 2 (by rfl) ⟨250485, by rfl⟩ : syracuseStep 667961 = 500971) B500971
theorem B668699 : Blo 295830 668699 := bstep (se 1 (by rfl) ⟨501524, by rfl⟩ : syracuseStep 668699 = 1003049) B1003049
theorem B636383 : Blo 295830 636383 := bstep (se 1 (by rfl) ⟨477287, by rfl⟩ : syracuseStep 636383 = 954575) B954575
theorem B1685083 : Blo 295830 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B15350219 : Blo 295830 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1423943 : Blo 295830 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B670895 : Blo 295830 670895 := bstep (se 1 (by rfl) ⟨503171, by rfl⟩ : syracuseStep 670895 = 1006343) B1006343
theorem B670931 : Blo 295830 670931 := bstep (se 1 (by rfl) ⟨503198, by rfl⟩ : syracuseStep 670931 = 1006397) B1006397
theorem B573623 : Blo 295830 573623 := bstep (se 1 (by rfl) ⟨430217, by rfl⟩ : syracuseStep 573623 = 860435) B860435
theorem B5095709 : Blo 295830 5095709 := bstep (se 3 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 5095709 = 1910891) B1910891
theorem B672425 : Blo 295830 672425 := bstep (se 2 (by rfl) ⟨252159, by rfl⟩ : syracuseStep 672425 = 504319) B504319
theorem B443951 : Blo 295830 443951 := bstep (se 1 (by rfl) ⟨332963, by rfl⟩ : syracuseStep 443951 = 665927) B665927
theorem B477019 : Blo 295830 477019 := bstep (se 1 (by rfl) ⟨357764, by rfl⟩ : syracuseStep 477019 = 715529) B715529
theorem B1068335 : Blo 295830 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B1134233 : Blo 295830 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B4083371 : Blo 295830 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B446495 : Blo 295830 446495 := bstep (se 1 (by rfl) ⟨334871, by rfl⟩ : syracuseStep 446495 = 669743) B669743
theorem B1200545 : Blo 295830 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B2249207 : Blo 295830 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B1266479 : Blo 295830 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B447515 : Blo 295830 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B447977 : Blo 295830 447977 := bstep (se 2 (by rfl) ⟨167991, by rfl⟩ : syracuseStep 447977 = 335983) B335983
theorem B1005209 : Blo 295830 1005209 := bstep (se 2 (by rfl) ⟨376953, by rfl⟩ : syracuseStep 1005209 = 753907) B753907
theorem B448559 : Blo 295830 448559 := bstep (se 1 (by rfl) ⟨336419, by rfl⟩ : syracuseStep 448559 = 672839) B672839
theorem B448823 : Blo 295830 448823 := bstep (se 1 (by rfl) ⟨336617, by rfl⟩ : syracuseStep 448823 = 673235) B673235
theorem B449135 : Blo 295830 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B9755387 : Blo 295830 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B2415359 : Blo 295830 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B2252123 : Blo 295830 2252123 := bstep (se 1 (by rfl) ⟨1689092, by rfl⟩ : syracuseStep 2252123 = 3378185) B3378185
theorem B1367549 : Blo 295830 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B6119135 : Blo 295830 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B1269863 : Blo 295830 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B8610083 : Blo 295830 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B1075139 : Blo 295830 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B62580869 : Blo 295830 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B1009907 : Blo 295830 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B1501577 : Blo 295830 1501577 := bstep (se 2 (by rfl) ⟨563091, by rfl⟩ : syracuseStep 1501577 = 1126183) B1126183
theorem B1273313 : Blo 295830 1273313 := bstep (se 2 (by rfl) ⟨477492, by rfl⟩ : syracuseStep 1273313 = 954985) B954985
theorem B2158811 : Blo 295830 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B3797999 : Blo 295830 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B4584431 : Blo 295830 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B3209149 : Blo 295830 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B948361 : Blo 295830 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B1702397 : Blo 295830 1702397 := bstep (se 3 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 1702397 = 638399) B638399
theorem B39387683 : Blo 295830 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B295967 : Blo 295830 295967 := bstep (se 1 (by rfl) ⟨221975, by rfl⟩ : syracuseStep 295967 = 443951) B443951
theorem B756155 : Blo 295830 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B2722247 : Blo 295830 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B297663 : Blo 295830 297663 := bstep (se 1 (by rfl) ⟨223247, by rfl⟩ : syracuseStep 297663 = 446495) B446495
theorem B23792527 : Blo 295830 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B298343 : Blo 295830 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B757289 : Blo 295830 757289 := bstep (se 2 (by rfl) ⟨283983, by rfl⟩ : syracuseStep 757289 = 567967) B567967
theorem B298651 : Blo 295830 298651 := bstep (se 1 (by rfl) ⟨223988, by rfl⟩ : syracuseStep 298651 = 447977) B447977
theorem B299039 : Blo 295830 299039 := bstep (se 1 (by rfl) ⟨224279, by rfl⟩ : syracuseStep 299039 = 448559) B448559
theorem B35196983 : Blo 295830 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B299215 : Blo 295830 299215 := bstep (se 1 (by rfl) ⟨224411, by rfl⟩ : syracuseStep 299215 = 448823) B448823
theorem B299423 : Blo 295830 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B857179 : Blo 295830 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B5740055 : Blo 295830 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B1513727 : Blo 295830 1513727 := bstep (se 1 (by rfl) ⟨1135295, by rfl⟩ : syracuseStep 1513727 = 2270591) B2270591
theorem B4594279 : Blo 295830 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B41720579 : Blo 295830 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B2531999 : Blo 295830 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B3056287 : Blo 295830 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B10233479 : Blo 295830 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B502463 : Blo 295830 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B636025 : Blo 295830 636025 := bstep (se 2 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 636025 = 477019) B477019
theorem B800363 : Blo 295830 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B506063 : Blo 295830 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B670121 : Blo 295830 670121 := bstep (se 2 (by rfl) ⟨251295, by rfl⟩ : syracuseStep 670121 = 502591) B502591
theorem B670139 : Blo 295830 670139 := bstep (se 1 (by rfl) ⟨502604, by rfl⟩ : syracuseStep 670139 = 1005209) B1005209
theorem B6503591 : Blo 295830 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B4079423 : Blo 295830 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B673271 : Blo 295830 673271 := bstep (se 1 (by rfl) ⟨504953, by rfl⟩ : syracuseStep 673271 = 1009907) B1009907
theorem B1001051 : Blo 295830 1001051 := bstep (se 1 (by rfl) ⟨750788, by rfl⟩ : syracuseStep 1001051 = 1501577) B1501577
theorem B6440957 : Blo 295830 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B2246777 : Blo 295830 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B4278865 : Blo 295830 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B1264481 : Blo 295830 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B445307 : Blo 295830 445307 := bstep (se 1 (by rfl) ⟨333980, by rfl⟩ : syracuseStep 445307 = 667961) B667961
theorem B445433 : Blo 295830 445433 := bstep (se 2 (by rfl) ⟨167037, by rfl⟩ : syracuseStep 445433 = 334075) B334075
theorem B445799 : Blo 295830 445799 := bstep (se 1 (by rfl) ⟨334349, by rfl⟩ : syracuseStep 445799 = 668699) B668699
theorem B1134931 : Blo 295830 1134931 := bstep (se 1 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 1134931 = 1702397) B1702397
theorem B447263 : Blo 295830 447263 := bstep (se 1 (by rfl) ⟨335447, by rfl⟩ : syracuseStep 447263 = 670895) B670895
theorem B447287 : Blo 295830 447287 := bstep (se 1 (by rfl) ⟨335465, by rfl⟩ : syracuseStep 447287 = 670931) B670931
theorem B3397139 : Blo 295830 3397139 := bstep (se 1 (by rfl) ⟨2547854, by rfl⟩ : syracuseStep 3397139 = 5095709) B5095709
theorem B448283 : Blo 295830 448283 := bstep (se 1 (by rfl) ⟨336212, by rfl⟩ : syracuseStep 448283 = 672425) B672425
theorem B1006235 : Blo 295830 1006235 := bstep (se 1 (by rfl) ⟨754676, by rfl⟩ : syracuseStep 1006235 = 1509353) B1509353
theorem B1137833 : Blo 295830 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B712223 : Blo 295830 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B1007801 : Blo 295830 1007801 := bstep (se 2 (by rfl) ⟨377925, by rfl⟩ : syracuseStep 1007801 = 755851) B755851
theorem B1499471 : Blo 295830 1499471 := bstep (se 1 (by rfl) ⟨1124603, by rfl⟩ : syracuseStep 1499471 = 2249207) B2249207
theorem B844319 : Blo 295830 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B1697021 : Blo 295830 1697021 := bstep (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) B636383
theorem B1501415 : Blo 295830 1501415 := bstep (se 1 (by rfl) ⟨1126061, by rfl⟩ : syracuseStep 1501415 = 2252123) B2252123
theorem B911699 : Blo 295830 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B7235963 : Blo 295830 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B846575 : Blo 295830 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B1011311 : Blo 295830 1011311 := bstep (se 1 (by rfl) ⟨758483, by rfl⟩ : syracuseStep 1011311 = 1516967) B1516967
theorem B716759 : Blo 295830 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B749807 : Blo 295830 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B24474581 : Blo 295830 24474581 := bstep (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) B573623
theorem B848875 : Blo 295830 848875 := bstep (se 1 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 848875 = 1273313) B1273313
theorem B1439207 : Blo 295830 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B949295 : Blo 295830 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B4293971 : Blo 295830 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B296871 : Blo 295830 296871 := bstep (se 1 (by rfl) ⟨222653, by rfl⟩ : syracuseStep 296871 = 445307) B445307
theorem B296955 : Blo 295830 296955 := bstep (se 1 (by rfl) ⟨222716, by rfl⟩ : syracuseStep 296955 = 445433) B445433
theorem B297199 : Blo 295830 297199 := bstep (se 1 (by rfl) ⟨222899, by rfl⟩ : syracuseStep 297199 = 445799) B445799
theorem B23464655 : Blo 295830 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B298175 : Blo 295830 298175 := bstep (se 1 (by rfl) ⟨223631, by rfl⟩ : syracuseStep 298175 = 447263) B447263
theorem B298191 : Blo 295830 298191 := bstep (se 1 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 298191 = 447287) B447287
theorem B5705153 : Blo 295830 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B2264759 : Blo 295830 2264759 := bstep (se 1 (by rfl) ⟨1698569, by rfl⟩ : syracuseStep 2264759 = 3397139) B3397139
theorem B298855 : Blo 295830 298855 := bstep (se 1 (by rfl) ⟨224141, by rfl⟩ : syracuseStep 298855 = 448283) B448283
theorem B31723369 : Blo 295830 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B758555 : Blo 295830 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B562879 : Blo 295830 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B1513241 : Blo 295830 1513241 := bstep (se 2 (by rfl) ⟨567465, by rfl⟩ : syracuseStep 1513241 = 1134931) B1134931
theorem B6822319 : Blo 295830 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B4823975 : Blo 295830 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B334975 : Blo 295830 334975 := bstep (se 1 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 334975 = 502463) B502463
theorem B564383 : Blo 295830 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B499871 : Blo 295830 499871 := bstep (se 1 (by rfl) ⟨374903, by rfl⟩ : syracuseStep 499871 = 749807) B749807
theorem B17342909 : Blo 295830 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B959471 : Blo 295830 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B533575 : Blo 295830 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B337375 : Blo 295830 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B632863 : Blo 295830 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B26258455 : Blo 295830 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B4075049 : Blo 295830 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B667367 : Blo 295830 667367 := bstep (se 1 (by rfl) ⟨500525, by rfl⟩ : syracuseStep 667367 = 1001051) B1001051
theorem B504103 : Blo 295830 504103 := bstep (se 1 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 504103 = 756155) B756155
theorem B1814831 : Blo 295830 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B504859 : Blo 295830 504859 := bstep (se 1 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 504859 = 757289) B757289
theorem B670823 : Blo 295830 670823 := bstep (se 1 (by rfl) ⟨503117, by rfl⟩ : syracuseStep 670823 = 1006235) B1006235
theorem B474815 : Blo 295830 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B671867 : Blo 295830 671867 := bstep (se 1 (by rfl) ⟨503900, by rfl⟩ : syracuseStep 671867 = 1007801) B1007801
theorem B999647 : Blo 295830 999647 := bstep (se 1 (by rfl) ⟨749735, by rfl⟩ : syracuseStep 999647 = 1499471) B1499471
theorem B1687999 : Blo 295830 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B1131347 : Blo 295830 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B1131833 : Blo 295830 1131833 := bstep (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) B848875
theorem B1000943 : Blo 295830 1000943 := bstep (se 1 (by rfl) ⟨750707, by rfl⟩ : syracuseStep 1000943 = 1501415) B1501415
theorem B607799 : Blo 295830 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B674207 : Blo 295830 674207 := bstep (se 1 (by rfl) ⟨505655, by rfl⟩ : syracuseStep 674207 = 1011311) B1011311
theorem B477839 : Blo 295830 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B446747 : Blo 295830 446747 := bstep (se 1 (by rfl) ⟨335060, by rfl⟩ : syracuseStep 446747 = 670121) B670121
theorem B446759 : Blo 295830 446759 := bstep (se 1 (by rfl) ⟨335069, by rfl⟩ : syracuseStep 446759 = 670139) B670139
theorem B448847 : Blo 295830 448847 := bstep (se 1 (by rfl) ⟨336635, by rfl⟩ : syracuseStep 448847 = 673271) B673271
theorem B1497851 : Blo 295830 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B842987 : Blo 295830 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B3826703 : Blo 295830 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B1009151 : Blo 295830 1009151 := bstep (se 1 (by rfl) ⟨756863, by rfl⟩ : syracuseStep 1009151 = 1513727) B1513727
theorem B27813719 : Blo 295830 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1142905 : Blo 295830 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B848033 : Blo 295830 848033 := bstep (se 2 (by rfl) ⟨318012, by rfl⟩ : syracuseStep 848033 = 636025) B636025
theorem B16316387 : Blo 295830 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B6125705 : Blo 295830 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B2719615 : Blo 295830 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B3375269 : Blo 295830 3375269 := bstep (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) B632863
theorem B754231 : Blo 295830 754231 := bstep (se 1 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 754231 = 1131347) B1131347
theorem B754555 : Blo 295830 754555 := bstep (se 1 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 754555 = 1131833) B1131833
theorem B3803435 : Blo 295830 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1509839 : Blo 295830 1509839 := bstep (se 1 (by rfl) ⟨1132379, by rfl⟩ : syracuseStep 1509839 = 2264759) B2264759
theorem B297831 : Blo 295830 297831 := bstep (se 1 (by rfl) ⟨223373, by rfl⟩ : syracuseStep 297831 = 446747) B446747
theorem B297839 : Blo 295830 297839 := bstep (se 1 (by rfl) ⟨223379, by rfl⟩ : syracuseStep 297839 = 446759) B446759
theorem B299231 : Blo 295830 299231 := bstep (se 1 (by rfl) ⟨224423, by rfl⟩ : syracuseStep 299231 = 448847) B448847
theorem B3215983 : Blo 295830 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B561991 : Blo 295830 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B333247 : Blo 295830 333247 := bstep (se 1 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 333247 = 499871) B499871
theorem B676765205 : Blo 295830 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B565355 : Blo 295830 565355 := bstep (se 1 (by rfl) ⟨424016, by rfl⟩ : syracuseStep 565355 = 848033) B848033
theorem B666431 : Blo 295830 666431 := bstep (se 1 (by rfl) ⟨499823, by rfl⟩ : syracuseStep 666431 = 999647) B999647
theorem B2862647 : Blo 295830 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B667295 : Blo 295830 667295 := bstep (se 1 (by rfl) ⟨500471, by rfl⟩ : syracuseStep 667295 = 1000943) B1000943
theorem B405199 : Blo 295830 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B15643103 : Blo 295830 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B505703 : Blo 295830 505703 := bstep (se 1 (by rfl) ⟨379277, by rfl⟩ : syracuseStep 505703 = 758555) B758555
theorem B35011273 : Blo 295830 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B998567 : Blo 295830 998567 := bstep (se 1 (by rfl) ⟨748925, by rfl⟩ : syracuseStep 998567 = 1497851) B1497851
theorem B376255 : Blo 295830 376255 := bstep (se 1 (by rfl) ⟨282191, by rfl⟩ : syracuseStep 376255 = 564383) B564383
theorem B1523873 : Blo 295830 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B672137 : Blo 295830 672137 := bstep (se 2 (by rfl) ⟨252051, by rfl⟩ : syracuseStep 672137 = 504103) B504103
theorem B639647 : Blo 295830 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B672767 : Blo 295830 672767 := bstep (se 1 (by rfl) ⟨504575, by rfl⟩ : syracuseStep 672767 = 1009151) B1009151
theorem B673145 : Blo 295830 673145 := bstep (se 2 (by rfl) ⟨252429, by rfl⟩ : syracuseStep 673145 = 504859) B504859
theorem B444911 : Blo 295830 444911 := bstep (se 1 (by rfl) ⟨333683, by rfl⟩ : syracuseStep 444911 = 667367) B667367
theorem B9096425 : Blo 295830 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B4083803 : Blo 295830 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B446633 : Blo 295830 446633 := bstep (se 2 (by rfl) ⟨167487, by rfl⟩ : syracuseStep 446633 = 334975) B334975
theorem B447215 : Blo 295830 447215 := bstep (se 1 (by rfl) ⟨335411, by rfl⟩ : syracuseStep 447215 = 670823) B670823
theorem B316543 : Blo 295830 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B3626153 : Blo 295830 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B447911 : Blo 295830 447911 := bstep (se 1 (by rfl) ⟨335933, by rfl⟩ : syracuseStep 447911 = 671867) B671867
theorem B2250665 : Blo 295830 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B711433 : Blo 295830 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B449471 : Blo 295830 449471 := bstep (se 1 (by rfl) ⟨337103, by rfl⟩ : syracuseStep 449471 = 674207) B674207
theorem B1008827 : Blo 295830 1008827 := bstep (se 1 (by rfl) ⟨756620, by rfl⟩ : syracuseStep 1008827 = 1513241) B1513241
theorem B11561939 : Blo 295830 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B2551135 : Blo 295830 2551135 := bstep (se 1 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 2551135 = 3826703) B3826703
theorem B18542479 : Blo 295830 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1274237 : Blo 295830 1274237 := bstep (se 3 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 1274237 = 477839) B477839
theorem B750505 : Blo 295830 750505 := bstep (se 2 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 750505 = 562879) B562879
theorem B2716699 : Blo 295830 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B1799333 : Blo 295830 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B1209887 : Blo 295830 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B10877591 : Blo 295830 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B1015915 : Blo 295830 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B426431 : Blo 295830 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B41714941 : Blo 295830 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B296607 : Blo 295830 296607 := bstep (se 1 (by rfl) ⟨222455, by rfl⟩ : syracuseStep 296607 = 444911) B444911
theorem B6064283 : Blo 295830 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B2722535 : Blo 295830 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B297755 : Blo 295830 297755 := bstep (se 1 (by rfl) ⟨223316, by rfl⟩ : syracuseStep 297755 = 446633) B446633
theorem B298143 : Blo 295830 298143 := bstep (se 1 (by rfl) ⟨223607, by rfl⟩ : syracuseStep 298143 = 447215) B447215
theorem B298607 : Blo 295830 298607 := bstep (se 1 (by rfl) ⟨223955, by rfl⟩ : syracuseStep 298607 = 447911) B447911
theorem B299647 : Blo 295830 299647 := bstep (se 1 (by rfl) ⟨224735, by rfl⟩ : syracuseStep 299647 = 449471) B449471
theorem B7707959 : Blo 295830 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B1908431 : Blo 295830 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B337135 : Blo 295830 337135 := bstep (se 1 (by rfl) ⟨252851, by rfl⟩ : syracuseStep 337135 = 505703) B505703
theorem B7251727 : Blo 295830 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B501673 : Blo 295830 501673 := bstep (se 2 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 501673 = 376255) B376255
theorem B665711 : Blo 295830 665711 := bstep (se 1 (by rfl) ⟨499283, by rfl⟩ : syracuseStep 665711 = 998567) B998567
theorem B2535623 : Blo 295830 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B540265 : Blo 295830 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B24723305 : Blo 295830 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B376903 : Blo 295830 376903 := bstep (se 1 (by rfl) ⟨282677, by rfl⟩ : syracuseStep 376903 = 565355) B565355
theorem B672551 : Blo 295830 672551 := bstep (se 1 (by rfl) ⟨504413, by rfl⟩ : syracuseStep 672551 = 1008827) B1008827
theorem B1000673 : Blo 295830 1000673 := bstep (se 2 (by rfl) ⟨375252, by rfl⟩ : syracuseStep 1000673 = 750505) B750505
theorem B3622265 : Blo 295830 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B444287 : Blo 295830 444287 := bstep (se 1 (by rfl) ⟨333215, by rfl⟩ : syracuseStep 444287 = 666431) B666431
theorem B444329 : Blo 295830 444329 := bstep (se 2 (by rfl) ⟨166623, by rfl⟩ : syracuseStep 444329 = 333247) B333247
theorem B444863 : Blo 295830 444863 := bstep (se 1 (by rfl) ⟨333647, by rfl⟩ : syracuseStep 444863 = 667295) B667295
theorem B1199555 : Blo 295830 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B46681697 : Blo 295830 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B806591 : Blo 295830 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B2250179 : Blo 295830 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B448091 : Blo 295830 448091 := bstep (se 1 (by rfl) ⟨336068, by rfl⟩ : syracuseStep 448091 = 672137) B672137
theorem B448511 : Blo 295830 448511 := bstep (se 1 (by rfl) ⟨336383, by rfl⟩ : syracuseStep 448511 = 672767) B672767
theorem B1005641 : Blo 295830 1005641 := bstep (se 2 (by rfl) ⟨377115, by rfl⟩ : syracuseStep 1005641 = 754231) B754231
theorem B448763 : Blo 295830 448763 := bstep (se 1 (by rfl) ⟨336572, by rfl⟩ : syracuseStep 448763 = 673145) B673145
theorem B1006073 : Blo 295830 1006073 := bstep (se 2 (by rfl) ⟨377277, by rfl⟩ : syracuseStep 1006073 = 754555) B754555
theorem B1006559 : Blo 295830 1006559 := bstep (se 1 (by rfl) ⟨754919, by rfl⟩ : syracuseStep 1006559 = 1509839) B1509839
theorem B2417435 : Blo 295830 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B1500443 : Blo 295830 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B3794309 : Blo 295830 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B3401513 : Blo 295830 3401513 := bstep (se 2 (by rfl) ⟨1275567, by rfl⟩ : syracuseStep 3401513 = 2551135) B2551135
theorem B451176803 : Blo 295830 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B4287977 : Blo 295830 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B749321 : Blo 295830 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B422057 : Blo 295830 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B849491 : Blo 295830 849491 := bstep (se 1 (by rfl) ⟨637118, by rfl⟩ : syracuseStep 849491 = 1274237) B1274237
theorem B296191 : Blo 295830 296191 := bstep (se 1 (by rfl) ⟨222143, by rfl⟩ : syracuseStep 296191 = 444287) B444287
theorem B296219 : Blo 295830 296219 := bstep (se 1 (by rfl) ⟨222164, by rfl⟩ : syracuseStep 296219 = 444329) B444329
theorem B296575 : Blo 295830 296575 := bstep (se 1 (by rfl) ⟨222431, by rfl⟩ : syracuseStep 296575 = 444863) B444863
theorem B9668969 : Blo 295830 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B298727 : Blo 295830 298727 := bstep (se 1 (by rfl) ⟨224045, by rfl⟩ : syracuseStep 298727 = 448091) B448091
theorem B299007 : Blo 295830 299007 := bstep (se 1 (by rfl) ⟨224255, by rfl⟩ : syracuseStep 299007 = 448511) B448511
theorem B299175 : Blo 295830 299175 := bstep (se 1 (by rfl) ⟨224381, by rfl⟩ : syracuseStep 299175 = 448763) B448763
theorem B1611623 : Blo 295830 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B2529539 : Blo 295830 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B2267675 : Blo 295830 2267675 := bstep (se 1 (by rfl) ⟨1700756, by rfl⟩ : syracuseStep 2267675 = 3401513) B3401513
theorem B300784535 : Blo 295830 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B2858651 : Blo 295830 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B499547 : Blo 295830 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B566327 : Blo 295830 566327 := bstep (se 1 (by rfl) ⟨424745, by rfl⟩ : syracuseStep 566327 = 849491) B849491
theorem B502537 : Blo 295830 502537 := bstep (se 2 (by rfl) ⟨188451, by rfl⟩ : syracuseStep 502537 = 376903) B376903
theorem B1354553 : Blo 295830 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B1125485 : Blo 295830 1125485 := bstep (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) B422057
theorem B667115 : Blo 295830 667115 := bstep (se 1 (by rfl) ⟨500336, by rfl⟩ : syracuseStep 667115 = 1000673) B1000673
theorem B4042855 : Blo 295830 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B55619921 : Blo 295830 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1815023 : Blo 295830 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B799703 : Blo 295830 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B537727 : Blo 295830 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B668897 : Blo 295830 668897 := bstep (se 2 (by rfl) ⟨250836, by rfl⟩ : syracuseStep 668897 = 501673) B501673
theorem B670427 : Blo 295830 670427 := bstep (se 1 (by rfl) ⟨502820, by rfl⟩ : syracuseStep 670427 = 1005641) B1005641
theorem B670715 : Blo 295830 670715 := bstep (se 1 (by rfl) ⟨503036, by rfl⟩ : syracuseStep 670715 = 1006073) B1006073
theorem B671039 : Blo 295830 671039 := bstep (se 1 (by rfl) ⟨503279, by rfl⟩ : syracuseStep 671039 = 1006559) B1006559
theorem B1000295 : Blo 295830 1000295 := bstep (se 1 (by rfl) ⟨750221, by rfl⟩ : syracuseStep 1000295 = 1500443) B1500443
theorem B443807 : Blo 295830 443807 := bstep (se 1 (by rfl) ⟨332855, by rfl⟩ : syracuseStep 443807 = 665711) B665711
theorem B1690415 : Blo 295830 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B448367 : Blo 295830 448367 := bstep (se 1 (by rfl) ⟨336275, by rfl⟩ : syracuseStep 448367 = 672551) B672551
theorem B2414843 : Blo 295830 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1137149 : Blo 295830 1137149 := bstep (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) B426431
theorem B449513 : Blo 295830 449513 := bstep (se 2 (by rfl) ⟨168567, by rfl⟩ : syracuseStep 449513 = 337135) B337135
theorem B31121131 : Blo 295830 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B1500119 : Blo 295830 1500119 := bstep (se 1 (by rfl) ⟨1125089, by rfl⟩ : syracuseStep 1500119 = 2250179) B2250179
theorem B5138639 : Blo 295830 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B1272287 : Blo 295830 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B720353 : Blo 295830 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B16482203 : Blo 295830 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B295871 : Blo 295830 295871 := bstep (se 1 (by rfl) ⟨221903, by rfl⟩ : syracuseStep 295871 = 443807) B443807
theorem B298911 : Blo 295830 298911 := bstep (se 1 (by rfl) ⟨224183, by rfl⟩ : syracuseStep 298911 = 448367) B448367
theorem B1609895 : Blo 295830 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B758099 : Blo 295830 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B1511783 : Blo 295830 1511783 := bstep (se 1 (by rfl) ⟨1133837, by rfl⟩ : syracuseStep 1511783 = 2267675) B2267675
theorem B299675 : Blo 295830 299675 := bstep (se 1 (by rfl) ⟨224756, by rfl⟩ : syracuseStep 299675 = 449513) B449513
theorem B4297661 : Blo 295830 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B1905767 : Blo 295830 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B333031 : Blo 295830 333031 := bstep (se 1 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 333031 = 499547) B499547
theorem B533135 : Blo 295830 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B41494841 : Blo 295830 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B10988135 : Blo 295830 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B666863 : Blo 295830 666863 := bstep (se 1 (by rfl) ⟨500147, by rfl⟩ : syracuseStep 666863 = 1000295) B1000295
theorem B1126943 : Blo 295830 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B670049 : Blo 295830 670049 := bstep (se 2 (by rfl) ⟨251268, by rfl⟩ : syracuseStep 670049 = 502537) B502537
theorem B1686359 : Blo 295830 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B200523023 : Blo 295830 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B5390473 : Blo 295830 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B1000079 : Blo 295830 1000079 := bstep (se 1 (by rfl) ⟨750059, by rfl⟩ : syracuseStep 1000079 = 1500119) B1500119
theorem B377551 : Blo 295830 377551 := bstep (se 1 (by rfl) ⟨283163, by rfl⟩ : syracuseStep 377551 = 566327) B566327
theorem B3392765 : Blo 295830 3392765 := bstep (se 3 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 3392765 = 1272287) B1272287
theorem B3425759 : Blo 295830 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B903035 : Blo 295830 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B444743 : Blo 295830 444743 := bstep (se 1 (by rfl) ⟨333557, by rfl⟩ : syracuseStep 444743 = 667115) B667115
theorem B37079947 : Blo 295830 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B445931 : Blo 295830 445931 := bstep (se 1 (by rfl) ⟨334448, by rfl⟩ : syracuseStep 445931 = 668897) B668897
theorem B446951 : Blo 295830 446951 := bstep (se 1 (by rfl) ⟨335213, by rfl⟩ : syracuseStep 446951 = 670427) B670427
theorem B447143 : Blo 295830 447143 := bstep (se 1 (by rfl) ⟨335357, by rfl⟩ : syracuseStep 447143 = 670715) B670715
theorem B447359 : Blo 295830 447359 := bstep (se 1 (by rfl) ⟨335519, by rfl⟩ : syracuseStep 447359 = 671039) B671039
theorem B480235 : Blo 295830 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B6445979 : Blo 295830 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B716969 : Blo 295830 716969 := bstep (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) B537727
theorem B750323 : Blo 295830 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B1210015 : Blo 295830 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B2261843 : Blo 295830 2261843 := bstep (se 1 (by rfl) ⟨1696382, by rfl⟩ : syracuseStep 2261843 = 3392765) B3392765
theorem B296495 : Blo 295830 296495 := bstep (se 1 (by rfl) ⟨222371, by rfl⟩ : syracuseStep 296495 = 444743) B444743
theorem B297287 : Blo 295830 297287 := bstep (se 1 (by rfl) ⟨222965, by rfl⟩ : syracuseStep 297287 = 445931) B445931
theorem B297967 : Blo 295830 297967 := bstep (se 1 (by rfl) ⟨223475, by rfl⟩ : syracuseStep 297967 = 446951) B446951
theorem B298095 : Blo 295830 298095 := bstep (se 1 (by rfl) ⟨223571, by rfl⟩ : syracuseStep 298095 = 447143) B447143
theorem B298239 : Blo 295830 298239 := bstep (se 1 (by rfl) ⟨223679, by rfl⟩ : syracuseStep 298239 = 447359) B447359
theorem B4297319 : Blo 295830 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B197759717 : Blo 295830 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B27663227 : Blo 295830 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B1613353 : Blo 295830 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B500215 : Blo 295830 500215 := bstep (se 1 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 500215 = 750323) B750323
theorem B1124239 : Blo 295830 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B7187297 : Blo 295830 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B666719 : Blo 295830 666719 := bstep (se 1 (by rfl) ⟨500039, by rfl⟩ : syracuseStep 666719 = 1000079) B1000079
theorem B1911917 : Blo 295830 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B503401 : Blo 295830 503401 := bstep (se 2 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 503401 = 377551) B377551
theorem B602023 : Blo 295830 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B505399 : Blo 295830 505399 := bstep (se 1 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 505399 = 758099) B758099
theorem B2865107 : Blo 295830 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B640313 : Blo 295830 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B444041 : Blo 295830 444041 := bstep (se 2 (by rfl) ⟨166515, by rfl⟩ : syracuseStep 444041 = 333031) B333031
theorem B7325423 : Blo 295830 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B444575 : Blo 295830 444575 := bstep (se 1 (by rfl) ⟨333431, by rfl⟩ : syracuseStep 444575 = 666863) B666863
theorem B446699 : Blo 295830 446699 := bstep (se 1 (by rfl) ⟨335024, by rfl⟩ : syracuseStep 446699 = 670049) B670049
theorem B133682015 : Blo 295830 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B2283839 : Blo 295830 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B1073263 : Blo 295830 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B1007855 : Blo 295830 1007855 := bstep (se 1 (by rfl) ⟨755891, by rfl⟩ : syracuseStep 1007855 = 1511783) B1511783
theorem B1270511 : Blo 295830 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B355423 : Blo 295830 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B751295 : Blo 295830 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B1507895 : Blo 295830 1507895 := bstep (se 1 (by rfl) ⟨1130921, by rfl⟩ : syracuseStep 1507895 = 2261843) B2261843
theorem B426875 : Blo 295830 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B296027 : Blo 295830 296027 := bstep (se 1 (by rfl) ⟨222020, by rfl⟩ : syracuseStep 296027 = 444041) B444041
theorem B4883615 : Blo 295830 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B296383 : Blo 295830 296383 := bstep (se 1 (by rfl) ⟨222287, by rfl⟩ : syracuseStep 296383 = 444575) B444575
theorem B297799 : Blo 295830 297799 := bstep (se 1 (by rfl) ⟨223349, by rfl⟩ : syracuseStep 297799 = 446699) B446699
theorem B500863 : Blo 295830 500863 := bstep (se 1 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 500863 = 751295) B751295
theorem B1910071 : Blo 295830 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B666953 : Blo 295830 666953 := bstep (se 2 (by rfl) ⟨250107, by rfl⟩ : syracuseStep 666953 = 500215) B500215
theorem B2864879 : Blo 295830 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B131839811 : Blo 295830 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B473897 : Blo 295830 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B1522559 : Blo 295830 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B671201 : Blo 295830 671201 := bstep (se 2 (by rfl) ⟨251700, by rfl⟩ : syracuseStep 671201 = 503401) B503401
theorem B671903 : Blo 295830 671903 := bstep (se 1 (by rfl) ⟨503927, by rfl⟩ : syracuseStep 671903 = 1007855) B1007855
theorem B444479 : Blo 295830 444479 := bstep (se 1 (by rfl) ⟨333359, by rfl⟩ : syracuseStep 444479 = 666719) B666719
theorem B673865 : Blo 295830 673865 := bstep (se 2 (by rfl) ⟨252699, by rfl⟩ : syracuseStep 673865 = 505399) B505399
theorem B76664501 : Blo 295830 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B2151137 : Blo 295830 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B1431017 : Blo 295830 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B1498985 : Blo 295830 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B89121343 : Blo 295830 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B18442151 : Blo 295830 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B847007 : Blo 295830 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B1274611 : Blo 295830 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B12843157 : Blo 295830 12843157 := bstep (se 6 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 12843157 = 602023) B602023
theorem B296319 : Blo 295830 296319 := bstep (se 1 (by rfl) ⟨222239, by rfl⟩ : syracuseStep 296319 = 444479) B444479
theorem B5736365 : Blo 295830 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B954011 : Blo 295830 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B12294767 : Blo 295830 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B564671 : Blo 295830 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B1909919 : Blo 295830 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B87893207 : Blo 295830 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B118828457 : Blo 295830 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B3255743 : Blo 295830 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B667817 : Blo 295830 667817 := bstep (se 2 (by rfl) ⟨250431, by rfl⟩ : syracuseStep 667817 = 500863) B500863
theorem B999323 : Blo 295830 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B1263725 : Blo 295830 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B444635 : Blo 295830 444635 := bstep (se 1 (by rfl) ⟨333476, by rfl⟩ : syracuseStep 444635 = 666953) B666953
theorem B17124209 : Blo 295830 17124209 := bstep (se 2 (by rfl) ⟨6421578, by rfl⟩ : syracuseStep 17124209 = 12843157) B12843157
theorem B447467 : Blo 295830 447467 := bstep (se 1 (by rfl) ⟨335600, by rfl⟩ : syracuseStep 447467 = 671201) B671201
theorem B447935 : Blo 295830 447935 := bstep (se 1 (by rfl) ⟨335951, by rfl⟩ : syracuseStep 447935 = 671903) B671903
theorem B1005263 : Blo 295830 1005263 := bstep (se 1 (by rfl) ⟨753947, by rfl⟩ : syracuseStep 1005263 = 1507895) B1507895
theorem B449243 : Blo 295830 449243 := bstep (se 1 (by rfl) ⟨336932, by rfl⟩ : syracuseStep 449243 = 673865) B673865
theorem B2546761 : Blo 295830 2546761 := bstep (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) B1910071
theorem B1138333 : Blo 295830 1138333 := bstep (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) B426875
theorem B51109667 : Blo 295830 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B1699481 : Blo 295830 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B1015039 : Blo 295830 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B296423 : Blo 295830 296423 := bstep (se 1 (by rfl) ⟨222317, by rfl⟩ : syracuseStep 296423 = 444635) B444635
theorem B298311 : Blo 295830 298311 := bstep (se 1 (by rfl) ⟨223733, by rfl⟩ : syracuseStep 298311 = 447467) B447467
theorem B298623 : Blo 295830 298623 := bstep (se 1 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 298623 = 447935) B447935
theorem B8196511 : Blo 295830 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B299495 : Blo 295830 299495 := bstep (se 1 (by rfl) ⟨224621, by rfl⟩ : syracuseStep 299495 = 449243) B449243
theorem B58595471 : Blo 295830 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B2170495 : Blo 295830 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B1353385 : Blo 295830 1353385 := bstep (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) B1015039
theorem B1517777 : Blo 295830 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B666215 : Blo 295830 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B11416139 : Blo 295830 11416139 := bstep (se 1 (by rfl) ⟨8562104, by rfl⟩ : syracuseStep 11416139 = 17124209) B17124209
theorem B636007 : Blo 295830 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B670175 : Blo 295830 670175 := bstep (se 1 (by rfl) ⟨502631, by rfl⟩ : syracuseStep 670175 = 1005263) B1005263
theorem B79218971 : Blo 295830 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B1132987 : Blo 295830 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B445211 : Blo 295830 445211 := bstep (se 1 (by rfl) ⟨333908, by rfl⟩ : syracuseStep 445211 = 667817) B667817
theorem B3395681 : Blo 295830 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B3824243 : Blo 295830 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B842483 : Blo 295830 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B34073111 : Blo 295830 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B1273279 : Blo 295830 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B1505789 : Blo 295830 1505789 := bstep (se 3 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 1505789 = 564671) B564671
theorem B296807 : Blo 295830 296807 := bstep (se 1 (by rfl) ⟨222605, by rfl⟩ : syracuseStep 296807 = 445211) B445211
theorem B1804513 : Blo 295830 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B2263787 : Blo 295830 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B1510649 : Blo 295830 1510649 := bstep (se 2 (by rfl) ⟨566493, by rfl⟩ : syracuseStep 1510649 = 1132987) B1132987
theorem B39063647 : Blo 295830 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B561655 : Blo 295830 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B22715407 : Blo 295830 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B7610759 : Blo 295830 7610759 := bstep (se 1 (by rfl) ⟨5708069, by rfl⟩ : syracuseStep 7610759 = 11416139) B11416139
theorem B11575973 : Blo 295830 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B10928681 : Blo 295830 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B444143 : Blo 295830 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B446783 : Blo 295830 446783 := bstep (se 1 (by rfl) ⟨335087, by rfl⟩ : syracuseStep 446783 = 670175) B670175
theorem B1003859 : Blo 295830 1003859 := bstep (se 1 (by rfl) ⟨752894, by rfl⟩ : syracuseStep 1003859 = 1505789) B1505789
theorem B52812647 : Blo 295830 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B2549495 : Blo 295830 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B1697705 : Blo 295830 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B848009 : Blo 295830 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B1011851 : Blo 295830 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B2261357 : Blo 295830 2261357 := bstep (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) B848009
theorem B296095 : Blo 295830 296095 := bstep (se 1 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 296095 = 444143) B444143
theorem B1509191 : Blo 295830 1509191 := bstep (se 1 (by rfl) ⟨1131893, by rfl⟩ : syracuseStep 1509191 = 2263787) B2263787
theorem B297855 : Blo 295830 297855 := bstep (se 1 (by rfl) ⟨223391, by rfl⟩ : syracuseStep 297855 = 446783) B446783
theorem B30287209 : Blo 295830 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B7285787 : Blo 295830 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B669239 : Blo 295830 669239 := bstep (se 1 (by rfl) ⟨501929, by rfl⟩ : syracuseStep 669239 = 1003859) B1003859
theorem B2406017 : Blo 295830 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B35208431 : Blo 295830 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B7717315 : Blo 295830 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1131803 : Blo 295830 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B674567 : Blo 295830 674567 := bstep (se 1 (by rfl) ⟨505925, by rfl⟩ : syracuseStep 674567 = 1011851) B1011851
theorem B1007099 : Blo 295830 1007099 := bstep (se 1 (by rfl) ⟨755324, by rfl⟩ : syracuseStep 1007099 = 1510649) B1510649
theorem B26042431 : Blo 295830 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B5073839 : Blo 295830 5073839 := bstep (se 1 (by rfl) ⟨3805379, by rfl⟩ : syracuseStep 5073839 = 7610759) B7610759
theorem B748873 : Blo 295830 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B1699663 : Blo 295830 1699663 := bstep (se 1 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 1699663 = 2549495) B2549495
theorem B1507571 : Blo 295830 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B10289753 : Blo 295830 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B754535 : Blo 295830 754535 := bstep (se 1 (by rfl) ⟨565901, by rfl⟩ : syracuseStep 754535 = 1131803) B1131803
theorem B2266217 : Blo 295830 2266217 := bstep (se 2 (by rfl) ⟨849831, by rfl⟩ : syracuseStep 2266217 = 1699663) B1699663
theorem B3382559 : Blo 295830 3382559 := bstep (se 1 (by rfl) ⟨2536919, by rfl⟩ : syracuseStep 3382559 = 5073839) B5073839
theorem B4857191 : Blo 295830 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B23472287 : Blo 295830 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B40382945 : Blo 295830 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B998497 : Blo 295830 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B671399 : Blo 295830 671399 := bstep (se 1 (by rfl) ⟨503549, by rfl⟩ : syracuseStep 671399 = 1007099) B1007099
theorem B446159 : Blo 295830 446159 := bstep (se 1 (by rfl) ⟨334619, by rfl⟩ : syracuseStep 446159 = 669239) B669239
theorem B34723241 : Blo 295830 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1006127 : Blo 295830 1006127 := bstep (se 1 (by rfl) ⟨754595, by rfl⟩ : syracuseStep 1006127 = 1509191) B1509191
theorem B449711 : Blo 295830 449711 := bstep (se 1 (by rfl) ⟨337283, by rfl⟩ : syracuseStep 449711 = 674567) B674567
theorem B1604011 : Blo 295830 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B297439 : Blo 295830 297439 := bstep (se 1 (by rfl) ⟨223079, by rfl⟩ : syracuseStep 297439 = 446159) B446159
theorem B1510811 : Blo 295830 1510811 := bstep (se 1 (by rfl) ⟨1133108, by rfl⟩ : syracuseStep 1510811 = 2266217) B2266217
theorem B299807 : Blo 295830 299807 := bstep (se 1 (by rfl) ⟨224855, by rfl⟩ : syracuseStep 299807 = 449711) B449711
theorem B2138681 : Blo 295830 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B6859835 : Blo 295830 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B503023 : Blo 295830 503023 := bstep (se 1 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 503023 = 754535) B754535
theorem B23148827 : Blo 295830 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B670751 : Blo 295830 670751 := bstep (se 1 (by rfl) ⟨503063, by rfl⟩ : syracuseStep 670751 = 1006127) B1006127
theorem B15648191 : Blo 295830 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B26921963 : Blo 295830 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1331329 : Blo 295830 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B447599 : Blo 295830 447599 := bstep (se 1 (by rfl) ⟨335699, by rfl⟩ : syracuseStep 447599 = 671399) B671399
theorem B1005047 : Blo 295830 1005047 := bstep (se 1 (by rfl) ⟨753785, by rfl⟩ : syracuseStep 1005047 = 1507571) B1507571
theorem B2255039 : Blo 295830 2255039 := bstep (se 1 (by rfl) ⟨1691279, by rfl⟩ : syracuseStep 2255039 = 3382559) B3382559
theorem B3238127 : Blo 295830 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B5703149 : Blo 295830 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B298399 : Blo 295830 298399 := bstep (se 1 (by rfl) ⟨223799, by rfl⟩ : syracuseStep 298399 = 447599) B447599
theorem B1775105 : Blo 295830 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B10432127 : Blo 295830 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B670031 : Blo 295830 670031 := bstep (se 1 (by rfl) ⟨502523, by rfl⟩ : syracuseStep 670031 = 1005047) B1005047
theorem B670697 : Blo 295830 670697 := bstep (se 2 (by rfl) ⟨251511, by rfl⟩ : syracuseStep 670697 = 503023) B503023
theorem B4573223 : Blo 295830 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B447167 : Blo 295830 447167 := bstep (se 1 (by rfl) ⟨335375, by rfl⟩ : syracuseStep 447167 = 670751) B670751
theorem B17947975 : Blo 295830 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1007207 : Blo 295830 1007207 := bstep (se 1 (by rfl) ⟨755405, by rfl⟩ : syracuseStep 1007207 = 1510811) B1510811
theorem B1503359 : Blo 295830 1503359 := bstep (se 1 (by rfl) ⟨1127519, by rfl⟩ : syracuseStep 1503359 = 2255039) B2255039
theorem B2158751 : Blo 295830 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B15432551 : Blo 295830 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B3802099 : Blo 295830 3802099 := bstep (se 1 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 3802099 = 5703149) B5703149
theorem B3048815 : Blo 295830 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B298111 : Blo 295830 298111 := bstep (se 1 (by rfl) ⟨223583, by rfl⟩ : syracuseStep 298111 = 447167) B447167
theorem B1183403 : Blo 295830 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B6954751 : Blo 295830 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B23930633 : Blo 295830 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B671471 : Blo 295830 671471 := bstep (se 1 (by rfl) ⟨503603, by rfl⟩ : syracuseStep 671471 = 1007207) B1007207
theorem B1002239 : Blo 295830 1002239 := bstep (se 1 (by rfl) ⟨751679, by rfl⟩ : syracuseStep 1002239 = 1503359) B1503359
theorem B446687 : Blo 295830 446687 := bstep (se 1 (by rfl) ⟨335015, by rfl⟩ : syracuseStep 446687 = 670031) B670031
theorem B447131 : Blo 295830 447131 := bstep (se 1 (by rfl) ⟨335348, by rfl⟩ : syracuseStep 447131 = 670697) B670697
theorem B1439167 : Blo 295830 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B10288367 : Blo 295830 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B2032543 : Blo 295830 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B788935 : Blo 295830 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B297791 : Blo 295830 297791 := bstep (se 1 (by rfl) ⟨223343, by rfl⟩ : syracuseStep 297791 = 446687) B446687
theorem B298087 : Blo 295830 298087 := bstep (se 1 (by rfl) ⟨223565, by rfl⟩ : syracuseStep 298087 = 447131) B447131
theorem B6858911 : Blo 295830 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B668159 : Blo 295830 668159 := bstep (se 1 (by rfl) ⟨501119, by rfl⟩ : syracuseStep 668159 = 1002239) B1002239
theorem B1918889 : Blo 295830 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B447647 : Blo 295830 447647 := bstep (se 1 (by rfl) ⟨335735, by rfl⟩ : syracuseStep 447647 = 671471) B671471
theorem B5069465 : Blo 295830 5069465 := bstep (se 2 (by rfl) ⟨1901049, by rfl⟩ : syracuseStep 5069465 = 3802099) B3802099
theorem B15953755 : Blo 295830 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B9273001 : Blo 295830 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B1279259 : Blo 295830 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B1051913 : Blo 295830 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B298431 : Blo 295830 298431 := bstep (se 1 (by rfl) ⟨223823, by rfl⟩ : syracuseStep 298431 = 447647) B447647
theorem B3379643 : Blo 295830 3379643 := bstep (se 1 (by rfl) ⟨2534732, by rfl⟩ : syracuseStep 3379643 = 5069465) B5069465
theorem B21271673 : Blo 295830 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B12364001 : Blo 295830 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B4572607 : Blo 295830 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B445439 : Blo 295830 445439 := bstep (se 1 (by rfl) ⟨334079, by rfl⟩ : syracuseStep 445439 = 668159) B668159
theorem B10840229 : Blo 295830 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B852839 : Blo 295830 852839 := bstep (se 1 (by rfl) ⟨639629, by rfl⟩ : syracuseStep 852839 = 1279259) B1279259
theorem B6096809 : Blo 295830 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B296959 : Blo 295830 296959 := bstep (se 1 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 296959 = 445439) B445439
theorem B56724461 : Blo 295830 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B7226819 : Blo 295830 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B8242667 : Blo 295830 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B2805101 : Blo 295830 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B2253095 : Blo 295830 2253095 := bstep (se 1 (by rfl) ⟨1689821, by rfl⟩ : syracuseStep 2253095 = 3379643) B3379643
theorem B4817879 : Blo 295830 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B37816307 : Blo 295830 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B1870067 : Blo 295830 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B16258157 : Blo 295830 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B568559 : Blo 295830 568559 := bstep (se 1 (by rfl) ⟨426419, by rfl⟩ : syracuseStep 568559 = 852839) B852839
theorem B5495111 : Blo 295830 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B1502063 : Blo 295830 1502063 := bstep (se 1 (by rfl) ⟨1126547, by rfl⟩ : syracuseStep 1502063 = 2253095) B2253095
theorem B3211919 : Blo 295830 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B4986845 : Blo 295830 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B1516157 : Blo 295830 1516157 := bstep (se 3 (by rfl) ⟨284279, by rfl⟩ : syracuseStep 1516157 = 568559) B568559
theorem B25210871 : Blo 295830 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B1001375 : Blo 295830 1001375 := bstep (se 1 (by rfl) ⟨751031, by rfl⟩ : syracuseStep 1001375 = 1502063) B1502063
theorem B10838771 : Blo 295830 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B3663407 : Blo 295830 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B2141279 : Blo 295830 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B667583 : Blo 295830 667583 := bstep (se 1 (by rfl) ⟨500687, by rfl⟩ : syracuseStep 667583 = 1001375) B1001375
theorem B3324563 : Blo 295830 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B7225847 : Blo 295830 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B2442271 : Blo 295830 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B1010771 : Blo 295830 1010771 := bstep (se 1 (by rfl) ⟨758078, by rfl⟩ : syracuseStep 1010771 = 1516157) B1516157
theorem B16807247 : Blo 295830 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B4817231 : Blo 295830 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B3256361 : Blo 295830 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B673847 : Blo 295830 673847 := bstep (se 1 (by rfl) ⟨505385, by rfl⟩ : syracuseStep 673847 = 1010771) B1010771
theorem B1427519 : Blo 295830 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B445055 : Blo 295830 445055 := bstep (se 1 (by rfl) ⟨333791, by rfl⟩ : syracuseStep 445055 = 667583) B667583
theorem B2216375 : Blo 295830 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B11204831 : Blo 295830 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B3211487 : Blo 295830 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B951679 : Blo 295830 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B296703 : Blo 295830 296703 := bstep (se 1 (by rfl) ⟨222527, by rfl⟩ : syracuseStep 296703 = 445055) B445055
theorem B2170907 : Blo 295830 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B449231 : Blo 295830 449231 := bstep (se 1 (by rfl) ⟨336923, by rfl⟩ : syracuseStep 449231 = 673847) B673847
theorem B94565333 : Blo 295830 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B7469887 : Blo 295830 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B299487 : Blo 295830 299487 := bstep (se 1 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 299487 = 449231) B449231
theorem B1447271 : Blo 295830 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B2140991 : Blo 295830 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B1268905 : Blo 295830 1268905 := bstep (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) B951679
theorem B252174221 : Blo 295830 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B9959849 : Blo 295830 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B964847 : Blo 295830 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B168116147 : Blo 295830 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B1427327 : Blo 295830 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B1691873 : Blo 295830 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B6639899 : Blo 295830 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B951551 : Blo 295830 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B112077431 : Blo 295830 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B17706397 : Blo 295830 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B1127915 : Blo 295830 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B643231 : Blo 295830 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B857641 : Blo 295830 857641 := bstep (se 2 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 857641 = 643231) B643231
theorem B74718287 : Blo 295830 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B634367 : Blo 295830 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B23608529 : Blo 295830 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B751943 : Blo 295830 751943 := bstep (se 1 (by rfl) ⟨563957, by rfl⟩ : syracuseStep 751943 = 1127915) B1127915
theorem B49812191 : Blo 295830 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B501295 : Blo 295830 501295 := bstep (se 1 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 501295 = 751943) B751943
theorem B15739019 : Blo 295830 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B1143521 : Blo 295830 1143521 := bstep (se 2 (by rfl) ⟨428820, by rfl⟩ : syracuseStep 1143521 = 857641) B857641
theorem B422911 : Blo 295830 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B10492679 : Blo 295830 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B762347 : Blo 295830 762347 := bstep (se 1 (by rfl) ⟨571760, by rfl⟩ : syracuseStep 762347 = 1143521) B1143521
theorem B668393 : Blo 295830 668393 := bstep (se 2 (by rfl) ⟨250647, by rfl⟩ : syracuseStep 668393 = 501295) B501295
theorem B33208127 : Blo 295830 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B2255525 : Blo 295830 2255525 := bstep (se 4 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 2255525 = 422911) B422911
theorem B6995119 : Blo 295830 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B508231 : Blo 295830 508231 := bstep (se 1 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 508231 = 762347) B762347
theorem B445595 : Blo 295830 445595 := bstep (se 1 (by rfl) ⟨334196, by rfl⟩ : syracuseStep 445595 = 668393) B668393
theorem B22138751 : Blo 295830 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B1503683 : Blo 295830 1503683 := bstep (se 1 (by rfl) ⟨1127762, by rfl⟩ : syracuseStep 1503683 = 2255525) B2255525
theorem B297063 : Blo 295830 297063 := bstep (se 1 (by rfl) ⟨222797, by rfl⟩ : syracuseStep 297063 = 445595) B445595
theorem B14759167 : Blo 295830 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B1002455 : Blo 295830 1002455 := bstep (se 1 (by rfl) ⟨751841, by rfl⟩ : syracuseStep 1002455 = 1503683) B1503683
theorem B9326825 : Blo 295830 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B2710565 : Blo 295830 2710565 := bstep (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) B508231
theorem B1807043 : Blo 295830 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B668303 : Blo 295830 668303 := bstep (se 1 (by rfl) ⟨501227, by rfl⟩ : syracuseStep 668303 = 1002455) B1002455
theorem B19678889 : Blo 295830 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B6217883 : Blo 295830 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B4818781 : Blo 295830 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B13119259 : Blo 295830 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B4145255 : Blo 295830 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B445535 : Blo 295830 445535 := bstep (se 1 (by rfl) ⟨334151, by rfl⟩ : syracuseStep 445535 = 668303) B668303
theorem B297023 : Blo 295830 297023 := bstep (se 1 (by rfl) ⟨222767, by rfl⟩ : syracuseStep 297023 = 445535) B445535
theorem B6425041 : Blo 295830 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B2763503 : Blo 295830 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B17492345 : Blo 295830 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1842335 : Blo 295830 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B8566721 : Blo 295830 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B11661563 : Blo 295830 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B7774375 : Blo 295830 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B5711147 : Blo 295830 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B1228223 : Blo 295830 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B3807431 : Blo 295830 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B10365833 : Blo 295830 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B3275261 : Blo 295830 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2538287 : Blo 295830 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B2183507 : Blo 295830 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B6910555 : Blo 295830 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B9214073 : Blo 295830 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B1455671 : Blo 295830 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1692191 : Blo 295830 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1128127 : Blo 295830 1128127 := bstep (se 1 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 1128127 = 1692191) B1692191
theorem B6142715 : Blo 295830 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B3881789 : Blo 295830 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B1504169 : Blo 295830 1504169 := bstep (se 2 (by rfl) ⟨564063, by rfl⟩ : syracuseStep 1504169 = 1128127) B1128127
theorem B4095143 : Blo 295830 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2587859 : Blo 295830 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B2730095 : Blo 295830 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B1002779 : Blo 295830 1002779 := bstep (se 1 (by rfl) ⟨752084, by rfl⟩ : syracuseStep 1002779 = 1504169) B1504169
theorem B1725239 : Blo 295830 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B4600637 : Blo 295830 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B668519 : Blo 295830 668519 := bstep (se 1 (by rfl) ⟨501389, by rfl⟩ : syracuseStep 668519 = 1002779) B1002779
theorem B1820063 : Blo 295830 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1213375 : Blo 295830 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B3067091 : Blo 295830 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B445679 : Blo 295830 445679 := bstep (se 1 (by rfl) ⟨334259, by rfl⟩ : syracuseStep 445679 = 668519) B668519
theorem B297119 : Blo 295830 297119 := bstep (se 1 (by rfl) ⟨222839, by rfl⟩ : syracuseStep 297119 = 445679) B445679
theorem B1617833 : Blo 295830 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B2044727 : Blo 295830 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B1363151 : Blo 295830 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B4314221 : Blo 295830 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B908767 : Blo 295830 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B2876147 : Blo 295830 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B1917431 : Blo 295830 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B1211689 : Blo 295830 1211689 := bstep (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) B908767
theorem B1278287 : Blo 295830 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B1615585 : Blo 295830 1615585 := bstep (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) B1211689
theorem B852191 : Blo 295830 852191 := bstep (se 1 (by rfl) ⟨639143, by rfl⟩ : syracuseStep 852191 = 1278287) B1278287
theorem B2154113 : Blo 295830 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B568127 : Blo 295830 568127 := bstep (se 1 (by rfl) ⟨426095, by rfl⟩ : syracuseStep 568127 = 852191) B852191
theorem B1436075 : Blo 295830 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B957383 : Blo 295830 957383 := bstep (se 1 (by rfl) ⟨718037, by rfl⟩ : syracuseStep 957383 = 1436075) B1436075
theorem B378751 : Blo 295830 378751 := bstep (se 1 (by rfl) ⟨284063, by rfl⟩ : syracuseStep 378751 = 568127) B568127
theorem B505001 : Blo 295830 505001 := bstep (se 2 (by rfl) ⟨189375, by rfl⟩ : syracuseStep 505001 = 378751) B378751
theorem B638255 : Blo 295830 638255 := bstep (se 1 (by rfl) ⟨478691, by rfl⟩ : syracuseStep 638255 = 957383) B957383
theorem B336667 : Blo 295830 336667 := bstep (se 1 (by rfl) ⟨252500, by rfl⟩ : syracuseStep 336667 = 505001) B505001
theorem B425503 : Blo 295830 425503 := bstep (se 1 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 425503 = 638255) B638255
theorem B567337 : Blo 295830 567337 := bstep (se 2 (by rfl) ⟨212751, by rfl⟩ : syracuseStep 567337 = 425503) B425503
theorem B448889 : Blo 295830 448889 := bstep (se 2 (by rfl) ⟨168333, by rfl⟩ : syracuseStep 448889 = 336667) B336667
theorem B756449 : Blo 295830 756449 := bstep (se 2 (by rfl) ⟨283668, by rfl⟩ : syracuseStep 756449 = 567337) B567337
theorem B299259 : Blo 295830 299259 := bstep (se 1 (by rfl) ⟨224444, by rfl⟩ : syracuseStep 299259 = 448889) B448889
theorem B504299 : Blo 295830 504299 := bstep (se 1 (by rfl) ⟨378224, by rfl⟩ : syracuseStep 504299 = 756449) B756449
theorem B336199 : Blo 295830 336199 := bstep (se 1 (by rfl) ⟨252149, by rfl⟩ : syracuseStep 336199 = 504299) B504299
theorem B448265 : Blo 295830 448265 := bstep (se 2 (by rfl) ⟨168099, by rfl⟩ : syracuseStep 448265 = 336199) B336199
theorem B298843 : Blo 295830 298843 := bstep (se 1 (by rfl) ⟨224132, by rfl⟩ : syracuseStep 298843 = 448265) B448265

theorem C0 (j : ℕ) (h1 : 73957 ≤ j) (h2 : j ≤ 74656) : Blo 295830 (4 * j + 3) := by
  interval_cases j
  · exact B295831
  · exact B295835
  · exact B295839
  · exact B295843
  · exact B295847
  · exact B295851
  · exact B295855
  · exact B295859
  · exact B295863
  · exact B295867
  · exact B295871
  · exact B295875
  · exact B295879
  · exact B295883
  · exact B295887
  · exact B295891
  · exact B295895
  · exact B295899
  · exact B295903
  · exact B295907
  · exact B295911
  · exact B295915
  · exact B295919
  · exact B295923
  · exact B295927
  · exact B295931
  · exact B295935
  · exact B295939
  · exact B295943
  · exact B295947
  · exact B295951
  · exact B295955
  · exact B295959
  · exact B295963
  · exact B295967
  · exact B295971
  · exact B295975
  · exact B295979
  · exact B295983
  · exact B295987
  · exact B295991
  · exact B295995
  · exact B295999
  · exact B296003
  · exact B296007
  · exact B296011
  · exact B296015
  · exact B296019
  · exact B296023
  · exact B296027
  · exact B296031
  · exact B296035
  · exact B296039
  · exact B296043
  · exact B296047
  · exact B296051
  · exact B296055
  · exact B296059
  · exact B296063
  · exact B296067
  · exact B296071
  · exact B296075
  · exact B296079
  · exact B296083
  · exact B296087
  · exact B296091
  · exact B296095
  · exact B296099
  · exact B296103
  · exact B296107
  · exact B296111
  · exact B296115
  · exact B296119
  · exact B296123
  · exact B296127
  · exact B296131
  · exact B296135
  · exact B296139
  · exact B296143
  · exact B296147
  · exact B296151
  · exact B296155
  · exact B296159
  · exact B296163
  · exact B296167
  · exact B296171
  · exact B296175
  · exact B296179
  · exact B296183
  · exact B296187
  · exact B296191
  · exact B296195
  · exact B296199
  · exact B296203
  · exact B296207
  · exact B296211
  · exact B296215
  · exact B296219
  · exact B296223
  · exact B296227
  · exact B296231
  · exact B296235
  · exact B296239
  · exact B296243
  · exact B296247
  · exact B296251
  · exact B296255
  · exact B296259
  · exact B296263
  · exact B296267
  · exact B296271
  · exact B296275
  · exact B296279
  · exact B296283
  · exact B296287
  · exact B296291
  · exact B296295
  · exact B296299
  · exact B296303
  · exact B296307
  · exact B296311
  · exact B296315
  · exact B296319
  · exact B296323
  · exact B296327
  · exact B296331
  · exact B296335
  · exact B296339
  · exact B296343
  · exact B296347
  · exact B296351
  · exact B296355
  · exact B296359
  · exact B296363
  · exact B296367
  · exact B296371
  · exact B296375
  · exact B296379
  · exact B296383
  · exact B296387
  · exact B296391
  · exact B296395
  · exact B296399
  · exact B296403
  · exact B296407
  · exact B296411
  · exact B296415
  · exact B296419
  · exact B296423
  · exact B296427
  · exact B296431
  · exact B296435
  · exact B296439
  · exact B296443
  · exact B296447
  · exact B296451
  · exact B296455
  · exact B296459
  · exact B296463
  · exact B296467
  · exact B296471
  · exact B296475
  · exact B296479
  · exact B296483
  · exact B296487
  · exact B296491
  · exact B296495
  · exact B296499
  · exact B296503
  · exact B296507
  · exact B296511
  · exact B296515
  · exact B296519
  · exact B296523
  · exact B296527
  · exact B296531
  · exact B296535
  · exact B296539
  · exact B296543
  · exact B296547
  · exact B296551
  · exact B296555
  · exact B296559
  · exact B296563
  · exact B296567
  · exact B296571
  · exact B296575
  · exact B296579
  · exact B296583
  · exact B296587
  · exact B296591
  · exact B296595
  · exact B296599
  · exact B296603
  · exact B296607
  · exact B296611
  · exact B296615
  · exact B296619
  · exact B296623
  · exact B296627
  · exact B296631
  · exact B296635
  · exact B296639
  · exact B296643
  · exact B296647
  · exact B296651
  · exact B296655
  · exact B296659
  · exact B296663
  · exact B296667
  · exact B296671
  · exact B296675
  · exact B296679
  · exact B296683
  · exact B296687
  · exact B296691
  · exact B296695
  · exact B296699
  · exact B296703
  · exact B296707
  · exact B296711
  · exact B296715
  · exact B296719
  · exact B296723
  · exact B296727
  · exact B296731
  · exact B296735
  · exact B296739
  · exact B296743
  · exact B296747
  · exact B296751
  · exact B296755
  · exact B296759
  · exact B296763
  · exact B296767
  · exact B296771
  · exact B296775
  · exact B296779
  · exact B296783
  · exact B296787
  · exact B296791
  · exact B296795
  · exact B296799
  · exact B296803
  · exact B296807
  · exact B296811
  · exact B296815
  · exact B296819
  · exact B296823
  · exact B296827
  · exact B296831
  · exact B296835
  · exact B296839
  · exact B296843
  · exact B296847
  · exact B296851
  · exact B296855
  · exact B296859
  · exact B296863
  · exact B296867
  · exact B296871
  · exact B296875
  · exact B296879
  · exact B296883
  · exact B296887
  · exact B296891
  · exact B296895
  · exact B296899
  · exact B296903
  · exact B296907
  · exact B296911
  · exact B296915
  · exact B296919
  · exact B296923
  · exact B296927
  · exact B296931
  · exact B296935
  · exact B296939
  · exact B296943
  · exact B296947
  · exact B296951
  · exact B296955
  · exact B296959
  · exact B296963
  · exact B296967
  · exact B296971
  · exact B296975
  · exact B296979
  · exact B296983
  · exact B296987
  · exact B296991
  · exact B296995
  · exact B296999
  · exact B297003
  · exact B297007
  · exact B297011
  · exact B297015
  · exact B297019
  · exact B297023
  · exact B297027
  · exact B297031
  · exact B297035
  · exact B297039
  · exact B297043
  · exact B297047
  · exact B297051
  · exact B297055
  · exact B297059
  · exact B297063
  · exact B297067
  · exact B297071
  · exact B297075
  · exact B297079
  · exact B297083
  · exact B297087
  · exact B297091
  · exact B297095
  · exact B297099
  · exact B297103
  · exact B297107
  · exact B297111
  · exact B297115
  · exact B297119
  · exact B297123
  · exact B297127
  · exact B297131
  · exact B297135
  · exact B297139
  · exact B297143
  · exact B297147
  · exact B297151
  · exact B297155
  · exact B297159
  · exact B297163
  · exact B297167
  · exact B297171
  · exact B297175
  · exact B297179
  · exact B297183
  · exact B297187
  · exact B297191
  · exact B297195
  · exact B297199
  · exact B297203
  · exact B297207
  · exact B297211
  · exact B297215
  · exact B297219
  · exact B297223
  · exact B297227
  · exact B297231
  · exact B297235
  · exact B297239
  · exact B297243
  · exact B297247
  · exact B297251
  · exact B297255
  · exact B297259
  · exact B297263
  · exact B297267
  · exact B297271
  · exact B297275
  · exact B297279
  · exact B297283
  · exact B297287
  · exact B297291
  · exact B297295
  · exact B297299
  · exact B297303
  · exact B297307
  · exact B297311
  · exact B297315
  · exact B297319
  · exact B297323
  · exact B297327
  · exact B297331
  · exact B297335
  · exact B297339
  · exact B297343
  · exact B297347
  · exact B297351
  · exact B297355
  · exact B297359
  · exact B297363
  · exact B297367
  · exact B297371
  · exact B297375
  · exact B297379
  · exact B297383
  · exact B297387
  · exact B297391
  · exact B297395
  · exact B297399
  · exact B297403
  · exact B297407
  · exact B297411
  · exact B297415
  · exact B297419
  · exact B297423
  · exact B297427
  · exact B297431
  · exact B297435
  · exact B297439
  · exact B297443
  · exact B297447
  · exact B297451
  · exact B297455
  · exact B297459
  · exact B297463
  · exact B297467
  · exact B297471
  · exact B297475
  · exact B297479
  · exact B297483
  · exact B297487
  · exact B297491
  · exact B297495
  · exact B297499
  · exact B297503
  · exact B297507
  · exact B297511
  · exact B297515
  · exact B297519
  · exact B297523
  · exact B297527
  · exact B297531
  · exact B297535
  · exact B297539
  · exact B297543
  · exact B297547
  · exact B297551
  · exact B297555
  · exact B297559
  · exact B297563
  · exact B297567
  · exact B297571
  · exact B297575
  · exact B297579
  · exact B297583
  · exact B297587
  · exact B297591
  · exact B297595
  · exact B297599
  · exact B297603
  · exact B297607
  · exact B297611
  · exact B297615
  · exact B297619
  · exact B297623
  · exact B297627
  · exact B297631
  · exact B297635
  · exact B297639
  · exact B297643
  · exact B297647
  · exact B297651
  · exact B297655
  · exact B297659
  · exact B297663
  · exact B297667
  · exact B297671
  · exact B297675
  · exact B297679
  · exact B297683
  · exact B297687
  · exact B297691
  · exact B297695
  · exact B297699
  · exact B297703
  · exact B297707
  · exact B297711
  · exact B297715
  · exact B297719
  · exact B297723
  · exact B297727
  · exact B297731
  · exact B297735
  · exact B297739
  · exact B297743
  · exact B297747
  · exact B297751
  · exact B297755
  · exact B297759
  · exact B297763
  · exact B297767
  · exact B297771
  · exact B297775
  · exact B297779
  · exact B297783
  · exact B297787
  · exact B297791
  · exact B297795
  · exact B297799
  · exact B297803
  · exact B297807
  · exact B297811
  · exact B297815
  · exact B297819
  · exact B297823
  · exact B297827
  · exact B297831
  · exact B297835
  · exact B297839
  · exact B297843
  · exact B297847
  · exact B297851
  · exact B297855
  · exact B297859
  · exact B297863
  · exact B297867
  · exact B297871
  · exact B297875
  · exact B297879
  · exact B297883
  · exact B297887
  · exact B297891
  · exact B297895
  · exact B297899
  · exact B297903
  · exact B297907
  · exact B297911
  · exact B297915
  · exact B297919
  · exact B297923
  · exact B297927
  · exact B297931
  · exact B297935
  · exact B297939
  · exact B297943
  · exact B297947
  · exact B297951
  · exact B297955
  · exact B297959
  · exact B297963
  · exact B297967
  · exact B297971
  · exact B297975
  · exact B297979
  · exact B297983
  · exact B297987
  · exact B297991
  · exact B297995
  · exact B297999
  · exact B298003
  · exact B298007
  · exact B298011
  · exact B298015
  · exact B298019
  · exact B298023
  · exact B298027
  · exact B298031
  · exact B298035
  · exact B298039
  · exact B298043
  · exact B298047
  · exact B298051
  · exact B298055
  · exact B298059
  · exact B298063
  · exact B298067
  · exact B298071
  · exact B298075
  · exact B298079
  · exact B298083
  · exact B298087
  · exact B298091
  · exact B298095
  · exact B298099
  · exact B298103
  · exact B298107
  · exact B298111
  · exact B298115
  · exact B298119
  · exact B298123
  · exact B298127
  · exact B298131
  · exact B298135
  · exact B298139
  · exact B298143
  · exact B298147
  · exact B298151
  · exact B298155
  · exact B298159
  · exact B298163
  · exact B298167
  · exact B298171
  · exact B298175
  · exact B298179
  · exact B298183
  · exact B298187
  · exact B298191
  · exact B298195
  · exact B298199
  · exact B298203
  · exact B298207
  · exact B298211
  · exact B298215
  · exact B298219
  · exact B298223
  · exact B298227
  · exact B298231
  · exact B298235
  · exact B298239
  · exact B298243
  · exact B298247
  · exact B298251
  · exact B298255
  · exact B298259
  · exact B298263
  · exact B298267
  · exact B298271
  · exact B298275
  · exact B298279
  · exact B298283
  · exact B298287
  · exact B298291
  · exact B298295
  · exact B298299
  · exact B298303
  · exact B298307
  · exact B298311
  · exact B298315
  · exact B298319
  · exact B298323
  · exact B298327
  · exact B298331
  · exact B298335
  · exact B298339
  · exact B298343
  · exact B298347
  · exact B298351
  · exact B298355
  · exact B298359
  · exact B298363
  · exact B298367
  · exact B298371
  · exact B298375
  · exact B298379
  · exact B298383
  · exact B298387
  · exact B298391
  · exact B298395
  · exact B298399
  · exact B298403
  · exact B298407
  · exact B298411
  · exact B298415
  · exact B298419
  · exact B298423
  · exact B298427
  · exact B298431
  · exact B298435
  · exact B298439
  · exact B298443
  · exact B298447
  · exact B298451
  · exact B298455
  · exact B298459
  · exact B298463
  · exact B298467
  · exact B298471
  · exact B298475
  · exact B298479
  · exact B298483
  · exact B298487
  · exact B298491
  · exact B298495
  · exact B298499
  · exact B298503
  · exact B298507
  · exact B298511
  · exact B298515
  · exact B298519
  · exact B298523
  · exact B298527
  · exact B298531
  · exact B298535
  · exact B298539
  · exact B298543
  · exact B298547
  · exact B298551
  · exact B298555
  · exact B298559
  · exact B298563
  · exact B298567
  · exact B298571
  · exact B298575
  · exact B298579
  · exact B298583
  · exact B298587
  · exact B298591
  · exact B298595
  · exact B298599
  · exact B298603
  · exact B298607
  · exact B298611
  · exact B298615
  · exact B298619
  · exact B298623
  · exact B298627

theorem C1 (j : ℕ) (h1 : 74657 ≤ j) (h2 : j ≤ 74956) : Blo 295830 (4 * j + 3) := by
  interval_cases j
  · exact B298631
  · exact B298635
  · exact B298639
  · exact B298643
  · exact B298647
  · exact B298651
  · exact B298655
  · exact B298659
  · exact B298663
  · exact B298667
  · exact B298671
  · exact B298675
  · exact B298679
  · exact B298683
  · exact B298687
  · exact B298691
  · exact B298695
  · exact B298699
  · exact B298703
  · exact B298707
  · exact B298711
  · exact B298715
  · exact B298719
  · exact B298723
  · exact B298727
  · exact B298731
  · exact B298735
  · exact B298739
  · exact B298743
  · exact B298747
  · exact B298751
  · exact B298755
  · exact B298759
  · exact B298763
  · exact B298767
  · exact B298771
  · exact B298775
  · exact B298779
  · exact B298783
  · exact B298787
  · exact B298791
  · exact B298795
  · exact B298799
  · exact B298803
  · exact B298807
  · exact B298811
  · exact B298815
  · exact B298819
  · exact B298823
  · exact B298827
  · exact B298831
  · exact B298835
  · exact B298839
  · exact B298843
  · exact B298847
  · exact B298851
  · exact B298855
  · exact B298859
  · exact B298863
  · exact B298867
  · exact B298871
  · exact B298875
  · exact B298879
  · exact B298883
  · exact B298887
  · exact B298891
  · exact B298895
  · exact B298899
  · exact B298903
  · exact B298907
  · exact B298911
  · exact B298915
  · exact B298919
  · exact B298923
  · exact B298927
  · exact B298931
  · exact B298935
  · exact B298939
  · exact B298943
  · exact B298947
  · exact B298951
  · exact B298955
  · exact B298959
  · exact B298963
  · exact B298967
  · exact B298971
  · exact B298975
  · exact B298979
  · exact B298983
  · exact B298987
  · exact B298991
  · exact B298995
  · exact B298999
  · exact B299003
  · exact B299007
  · exact B299011
  · exact B299015
  · exact B299019
  · exact B299023
  · exact B299027
  · exact B299031
  · exact B299035
  · exact B299039
  · exact B299043
  · exact B299047
  · exact B299051
  · exact B299055
  · exact B299059
  · exact B299063
  · exact B299067
  · exact B299071
  · exact B299075
  · exact B299079
  · exact B299083
  · exact B299087
  · exact B299091
  · exact B299095
  · exact B299099
  · exact B299103
  · exact B299107
  · exact B299111
  · exact B299115
  · exact B299119
  · exact B299123
  · exact B299127
  · exact B299131
  · exact B299135
  · exact B299139
  · exact B299143
  · exact B299147
  · exact B299151
  · exact B299155
  · exact B299159
  · exact B299163
  · exact B299167
  · exact B299171
  · exact B299175
  · exact B299179
  · exact B299183
  · exact B299187
  · exact B299191
  · exact B299195
  · exact B299199
  · exact B299203
  · exact B299207
  · exact B299211
  · exact B299215
  · exact B299219
  · exact B299223
  · exact B299227
  · exact B299231
  · exact B299235
  · exact B299239
  · exact B299243
  · exact B299247
  · exact B299251
  · exact B299255
  · exact B299259
  · exact B299263
  · exact B299267
  · exact B299271
  · exact B299275
  · exact B299279
  · exact B299283
  · exact B299287
  · exact B299291
  · exact B299295
  · exact B299299
  · exact B299303
  · exact B299307
  · exact B299311
  · exact B299315
  · exact B299319
  · exact B299323
  · exact B299327
  · exact B299331
  · exact B299335
  · exact B299339
  · exact B299343
  · exact B299347
  · exact B299351
  · exact B299355
  · exact B299359
  · exact B299363
  · exact B299367
  · exact B299371
  · exact B299375
  · exact B299379
  · exact B299383
  · exact B299387
  · exact B299391
  · exact B299395
  · exact B299399
  · exact B299403
  · exact B299407
  · exact B299411
  · exact B299415
  · exact B299419
  · exact B299423
  · exact B299427
  · exact B299431
  · exact B299435
  · exact B299439
  · exact B299443
  · exact B299447
  · exact B299451
  · exact B299455
  · exact B299459
  · exact B299463
  · exact B299467
  · exact B299471
  · exact B299475
  · exact B299479
  · exact B299483
  · exact B299487
  · exact B299491
  · exact B299495
  · exact B299499
  · exact B299503
  · exact B299507
  · exact B299511
  · exact B299515
  · exact B299519
  · exact B299523
  · exact B299527
  · exact B299531
  · exact B299535
  · exact B299539
  · exact B299543
  · exact B299547
  · exact B299551
  · exact B299555
  · exact B299559
  · exact B299563
  · exact B299567
  · exact B299571
  · exact B299575
  · exact B299579
  · exact B299583
  · exact B299587
  · exact B299591
  · exact B299595
  · exact B299599
  · exact B299603
  · exact B299607
  · exact B299611
  · exact B299615
  · exact B299619
  · exact B299623
  · exact B299627
  · exact B299631
  · exact B299635
  · exact B299639
  · exact B299643
  · exact B299647
  · exact B299651
  · exact B299655
  · exact B299659
  · exact B299663
  · exact B299667
  · exact B299671
  · exact B299675
  · exact B299679
  · exact B299683
  · exact B299687
  · exact B299691
  · exact B299695
  · exact B299699
  · exact B299703
  · exact B299707
  · exact B299711
  · exact B299715
  · exact B299719
  · exact B299723
  · exact B299727
  · exact B299731
  · exact B299735
  · exact B299739
  · exact B299743
  · exact B299747
  · exact B299751
  · exact B299755
  · exact B299759
  · exact B299763
  · exact B299767
  · exact B299771
  · exact B299775
  · exact B299779
  · exact B299783
  · exact B299787
  · exact B299791
  · exact B299795
  · exact B299799
  · exact B299803
  · exact B299807
  · exact B299811
  · exact B299815
  · exact B299819
  · exact B299823
  · exact B299827

theorem solution (m : ℕ) (hlo : 295830 ≤ m) (hhi : m ≤ 299830) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 73957 ≤ j := by omega
    have hj2 : j ≤ 74956 := by omega
    have hb : Blo 295830 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 74657 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
