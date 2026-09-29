-- Prove2me | solution 1 for syracuse_descends_range_1464552_1466552
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:32.779538+00:00
-- url     : https://prove2.me/submissions/056e7999-4646-48e7-8b57-e9443ea8941f

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


theorem B3711005 : Blo 1464552 3711005 := bbase (se 3 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 3711005 = 1391627) (by norm_num)
theorem B1564705 : Blo 1464552 1564705 := bbase (se 2 (by rfl) ⟨586764, by rfl⟩ : syracuseStep 1564705 = 1173529) (by norm_num)
theorem B2474077 : Blo 1464552 2474077 := bbase (se 3 (by rfl) ⟨463889, by rfl⟩ : syracuseStep 2474077 = 927779) (by norm_num)
theorem B2474165 : Blo 1464552 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B4948181 : Blo 1464552 4948181 := bbase (se 7 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 4948181 = 115973) (by norm_num)
theorem B2859229 : Blo 1464552 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B3711197 : Blo 1464552 3711197 := bbase (se 3 (by rfl) ⟨695849, by rfl⟩ : syracuseStep 3711197 = 1391699) (by norm_num)
theorem B3522797 : Blo 1464552 3522797 := bbase (se 3 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 3522797 = 1321049) (by norm_num)
theorem B2474293 : Blo 1464552 2474293 := bbase (se 5 (by rfl) ⟨115982, by rfl⟩ : syracuseStep 2474293 = 231965) (by norm_num)
theorem B1761625 : Blo 1464552 1761625 := bbase (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) (by norm_num)
theorem B1565021 : Blo 1464552 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B2474381 : Blo 1464552 2474381 := bbase (se 3 (by rfl) ⟨463946, by rfl⟩ : syracuseStep 2474381 = 927893) (by norm_num)
theorem B6685109 : Blo 1464552 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B8028629 : Blo 1464552 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B2474509 : Blo 1464552 2474509 := bbase (se 3 (by rfl) ⟨463970, by rfl⟩ : syracuseStep 2474509 = 927941) (by norm_num)
theorem B1761817 : Blo 1464552 1761817 := bbase (se 2 (by rfl) ⟨660681, by rfl⟩ : syracuseStep 1761817 = 1321363) (by norm_num)
theorem B3711541 : Blo 1464552 3711541 := bbase (se 5 (by rfl) ⟨173978, by rfl⟩ : syracuseStep 3711541 = 347957) (by norm_num)
theorem B26731093 : Blo 1464552 26731093 := bbase (se 8 (by rfl) ⟨156627, by rfl⟩ : syracuseStep 26731093 = 313255) (by norm_num)
theorem B2474597 : Blo 1464552 2474597 := bbase (se 4 (by rfl) ⟨231993, by rfl⟩ : syracuseStep 2474597 = 463987) (by norm_num)
theorem B2712197 : Blo 1464552 2712197 := bbase (se 4 (by rfl) ⟨254268, by rfl⟩ : syracuseStep 2712197 = 508537) (by norm_num)
theorem B4948613 : Blo 1464552 4948613 := bbase (se 4 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 4948613 = 927865) (by norm_num)
theorem B3711653 : Blo 1464552 3711653 := bbase (se 4 (by rfl) ⟨347967, by rfl⟩ : syracuseStep 3711653 = 695935) (by norm_num)
theorem B7922357 : Blo 1464552 7922357 := bbase (se 5 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 7922357 = 742721) (by norm_num)
theorem B7422677 : Blo 1464552 7422677 := bbase (se 7 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 7422677 = 173969) (by norm_num)
theorem B2474725 : Blo 1464552 2474725 := bbase (se 4 (by rfl) ⟨232005, by rfl⟩ : syracuseStep 2474725 = 464011) (by norm_num)
theorem B3130093 : Blo 1464552 3130093 := bbase (se 3 (by rfl) ⟨586892, by rfl⟩ : syracuseStep 3130093 = 1173785) (by norm_num)
theorem B1565465 : Blo 1464552 1565465 := bbase (se 2 (by rfl) ⟨587049, by rfl⟩ : syracuseStep 1565465 = 1174099) (by norm_num)
theorem B7922485 : Blo 1464552 7922485 := bbase (se 5 (by rfl) ⟨371366, by rfl⟩ : syracuseStep 7922485 = 742733) (by norm_num)
theorem B1565525 : Blo 1464552 1565525 := bbase (se 9 (by rfl) ⟨4586, by rfl⟩ : syracuseStep 1565525 = 9173) (by norm_num)
theorem B3711845 : Blo 1464552 3711845 := bbase (se 4 (by rfl) ⟨347985, by rfl⟩ : syracuseStep 3711845 = 695971) (by norm_num)
theorem B6259589 : Blo 1464552 6259589 := bbase (se 4 (by rfl) ⟨586836, by rfl⟩ : syracuseStep 6259589 = 1173673) (by norm_num)
theorem B2114461 : Blo 1464552 2114461 := bbase (se 3 (by rfl) ⟨396461, by rfl⟩ : syracuseStep 2114461 = 792923) (by norm_num)
theorem B3343285 : Blo 1464552 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B5563349 : Blo 1464552 5563349 := bbase (se 7 (by rfl) ⟨65195, by rfl⟩ : syracuseStep 5563349 = 130391) (by norm_num)
theorem B1565653 : Blo 1464552 1565653 := bbase (se 7 (by rfl) ⟨18347, by rfl⟩ : syracuseStep 1565653 = 36695) (by norm_num)
theorem B3523565 : Blo 1464552 3523565 := bbase (se 3 (by rfl) ⟨660668, by rfl⟩ : syracuseStep 3523565 = 1321337) (by norm_num)
theorem B1885189 : Blo 1464552 1885189 := bbase (se 4 (by rfl) ⟨176736, by rfl⟩ : syracuseStep 1885189 = 353473) (by norm_num)
theorem B1647625 : Blo 1464552 1647625 := bbase (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) (by norm_num)
theorem B1647661 : Blo 1464552 1647661 := bbase (se 3 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 1647661 = 617873) (by norm_num)
theorem B4949045 : Blo 1464552 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B1647697 : Blo 1464552 1647697 := bbase (se 2 (by rfl) ⟨617886, by rfl⟩ : syracuseStep 1647697 = 1235773) (by norm_num)
theorem B9520213 : Blo 1464552 9520213 := bbase (se 8 (by rfl) ⟨55782, by rfl⟩ : syracuseStep 9520213 = 111565) (by norm_num)
theorem B1647733 : Blo 1464552 1647733 := bbase (se 5 (by rfl) ⟨77237, by rfl⟩ : syracuseStep 1647733 = 154475) (by norm_num)
theorem B7414901 : Blo 1464552 7414901 := bbase (se 5 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 7414901 = 695147) (by norm_num)
theorem B1647769 : Blo 1464552 1647769 := bbase (se 2 (by rfl) ⟨617913, by rfl⟩ : syracuseStep 1647769 = 1235827) (by norm_num)
theorem B4695205 : Blo 1464552 4695205 := bbase (se 4 (by rfl) ⟨440175, by rfl⟩ : syracuseStep 4695205 = 880351) (by norm_num)
theorem B1647805 : Blo 1464552 1647805 := bbase (se 3 (by rfl) ⟨308963, by rfl⟩ : syracuseStep 1647805 = 617927) (by norm_num)
theorem B3712189 : Blo 1464552 3712189 := bbase (se 3 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 3712189 = 1392071) (by norm_num)
theorem B3130589 : Blo 1464552 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B1647841 : Blo 1464552 1647841 := bbase (se 2 (by rfl) ⟨617940, by rfl⟩ : syracuseStep 1647841 = 1235881) (by norm_num)
theorem B5563637 : Blo 1464552 5563637 := bbase (se 5 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 5563637 = 521591) (by norm_num)
theorem B1647877 : Blo 1464552 1647877 := bbase (se 4 (by rfl) ⟨154488, by rfl⟩ : syracuseStep 1647877 = 308977) (by norm_num)
theorem B1647913 : Blo 1464552 1647913 := bbase (se 2 (by rfl) ⟨617967, by rfl⟩ : syracuseStep 1647913 = 1235935) (by norm_num)
theorem B2819389 : Blo 1464552 2819389 := bbase (se 3 (by rfl) ⟨528635, by rfl⟩ : syracuseStep 2819389 = 1057271) (by norm_num)
theorem B1647949 : Blo 1464552 1647949 := bbase (se 3 (by rfl) ⟨308990, by rfl⟩ : syracuseStep 1647949 = 617981) (by norm_num)
theorem B2196845 : Blo 1464552 2196845 := bbase (se 3 (by rfl) ⟨411908, by rfl⟩ : syracuseStep 2196845 = 823817) (by norm_num)
theorem B1647985 : Blo 1464552 1647985 := bbase (se 2 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 1647985 = 1235989) (by norm_num)
theorem B2196869 : Blo 1464552 2196869 := bbase (se 4 (by rfl) ⟨205956, by rfl⟩ : syracuseStep 2196869 = 411913) (by norm_num)
theorem B1648021 : Blo 1464552 1648021 := bbase (se 6 (by rfl) ⟨38625, by rfl⟩ : syracuseStep 1648021 = 77251) (by norm_num)
theorem B2196893 : Blo 1464552 2196893 := bbase (se 3 (by rfl) ⟨411917, by rfl⟩ : syracuseStep 2196893 = 823835) (by norm_num)
theorem B2196917 : Blo 1464552 2196917 := bbase (se 5 (by rfl) ⟨102980, by rfl⟩ : syracuseStep 2196917 = 205961) (by norm_num)
theorem B2860469 : Blo 1464552 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1648057 : Blo 1464552 1648057 := bbase (se 2 (by rfl) ⟨618021, by rfl⟩ : syracuseStep 1648057 = 1236043) (by norm_num)
theorem B2196941 : Blo 1464552 2196941 := bbase (se 3 (by rfl) ⟨411926, by rfl⟩ : syracuseStep 2196941 = 823853) (by norm_num)
theorem B1648093 : Blo 1464552 1648093 := bbase (se 3 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 1648093 = 618035) (by norm_num)
theorem B2196965 : Blo 1464552 2196965 := bbase (se 4 (by rfl) ⟨205965, by rfl⟩ : syracuseStep 2196965 = 411931) (by norm_num)
theorem B4949477 : Blo 1464552 4949477 := bbase (se 4 (by rfl) ⟨464013, by rfl⟩ : syracuseStep 4949477 = 928027) (by norm_num)
theorem B2196989 : Blo 1464552 2196989 := bbase (se 3 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 2196989 = 823871) (by norm_num)
theorem B1648129 : Blo 1464552 1648129 := bbase (se 2 (by rfl) ⟨618048, by rfl⟩ : syracuseStep 1648129 = 1236097) (by norm_num)
theorem B2197013 : Blo 1464552 2197013 := bbase (se 6 (by rfl) ⟨51492, by rfl⟩ : syracuseStep 2197013 = 102985) (by norm_num)
theorem B1648165 : Blo 1464552 1648165 := bbase (se 4 (by rfl) ⟨154515, by rfl⟩ : syracuseStep 1648165 = 309031) (by norm_num)
theorem B2197037 : Blo 1464552 2197037 := bbase (se 3 (by rfl) ⟨411944, by rfl⟩ : syracuseStep 2197037 = 823889) (by norm_num)
theorem B2229805 : Blo 1464552 2229805 := bbase (se 3 (by rfl) ⟨418088, by rfl⟩ : syracuseStep 2229805 = 836177) (by norm_num)
theorem B2197061 : Blo 1464552 2197061 := bbase (se 4 (by rfl) ⟨205974, by rfl⟩ : syracuseStep 2197061 = 411949) (by norm_num)
theorem B4458053 : Blo 1464552 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B1648201 : Blo 1464552 1648201 := bbase (se 2 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 1648201 = 1236151) (by norm_num)
theorem B2197085 : Blo 1464552 2197085 := bbase (se 3 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 2197085 = 823907) (by norm_num)
theorem B1648237 : Blo 1464552 1648237 := bbase (se 3 (by rfl) ⟨309044, by rfl⟩ : syracuseStep 1648237 = 618089) (by norm_num)
theorem B2197109 : Blo 1464552 2197109 := bbase (se 5 (by rfl) ⟨102989, by rfl⟩ : syracuseStep 2197109 = 205979) (by norm_num)
theorem B8914549 : Blo 1464552 8914549 := bbase (se 5 (by rfl) ⟨417869, by rfl⟩ : syracuseStep 8914549 = 835739) (by norm_num)
theorem B3343997 : Blo 1464552 3343997 := bbase (se 3 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 3343997 = 1253999) (by norm_num)
theorem B2197133 : Blo 1464552 2197133 := bbase (se 3 (by rfl) ⟨411962, by rfl⟩ : syracuseStep 2197133 = 823925) (by norm_num)
theorem B1648273 : Blo 1464552 1648273 := bbase (se 2 (by rfl) ⟨618102, by rfl⟩ : syracuseStep 1648273 = 1236205) (by norm_num)
theorem B2197157 : Blo 1464552 2197157 := bbase (se 4 (by rfl) ⟨205983, by rfl⟩ : syracuseStep 2197157 = 411967) (by norm_num)
theorem B4171429 : Blo 1464552 4171429 := bbase (se 4 (by rfl) ⟨391071, by rfl⟩ : syracuseStep 4171429 = 782143) (by norm_num)
theorem B1648309 : Blo 1464552 1648309 := bbase (se 5 (by rfl) ⟨77264, by rfl⟩ : syracuseStep 1648309 = 154529) (by norm_num)
theorem B2197181 : Blo 1464552 2197181 := bbase (se 3 (by rfl) ⟨411971, by rfl⟩ : syracuseStep 2197181 = 823943) (by norm_num)
theorem B2197205 : Blo 1464552 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B1648345 : Blo 1464552 1648345 := bbase (se 2 (by rfl) ⟨618129, by rfl⟩ : syracuseStep 1648345 = 1236259) (by norm_num)
theorem B2197229 : Blo 1464552 2197229 := bbase (se 3 (by rfl) ⟨411980, by rfl⟩ : syracuseStep 2197229 = 823961) (by norm_num)
theorem B1648381 : Blo 1464552 1648381 := bbase (se 3 (by rfl) ⟨309071, by rfl⟩ : syracuseStep 1648381 = 618143) (by norm_num)
theorem B3344125 : Blo 1464552 3344125 := bbase (se 3 (by rfl) ⟨627023, by rfl⟩ : syracuseStep 3344125 = 1254047) (by norm_num)
theorem B2197253 : Blo 1464552 2197253 := bbase (se 4 (by rfl) ⟨205992, by rfl⟩ : syracuseStep 2197253 = 411985) (by norm_num)
theorem B2197277 : Blo 1464552 2197277 := bbase (se 3 (by rfl) ⟨411989, by rfl⟩ : syracuseStep 2197277 = 823979) (by norm_num)
theorem B1648417 : Blo 1464552 1648417 := bbase (se 2 (by rfl) ⟨618156, by rfl⟩ : syracuseStep 1648417 = 1236313) (by norm_num)
theorem B2197301 : Blo 1464552 2197301 := bbase (se 5 (by rfl) ⟨102998, by rfl⟩ : syracuseStep 2197301 = 205997) (by norm_num)
theorem B1648453 : Blo 1464552 1648453 := bbase (se 4 (by rfl) ⟨154542, by rfl⟩ : syracuseStep 1648453 = 309085) (by norm_num)
theorem B2197325 : Blo 1464552 2197325 := bbase (se 3 (by rfl) ⟨411998, by rfl⟩ : syracuseStep 2197325 = 823997) (by norm_num)
theorem B2197349 : Blo 1464552 2197349 := bbase (se 4 (by rfl) ⟨206001, by rfl⟩ : syracuseStep 2197349 = 412003) (by norm_num)
theorem B1648489 : Blo 1464552 1648489 := bbase (se 2 (by rfl) ⟨618183, by rfl⟩ : syracuseStep 1648489 = 1236367) (by norm_num)
theorem B6260597 : Blo 1464552 6260597 := bbase (se 5 (by rfl) ⟨293465, by rfl⟩ : syracuseStep 6260597 = 586931) (by norm_num)
theorem B2197373 : Blo 1464552 2197373 := bbase (se 3 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 2197373 = 824015) (by norm_num)
theorem B1648525 : Blo 1464552 1648525 := bbase (se 3 (by rfl) ⟨309098, by rfl⟩ : syracuseStep 1648525 = 618197) (by norm_num)
theorem B2197397 : Blo 1464552 2197397 := bbase (se 6 (by rfl) ⟨51501, by rfl⟩ : syracuseStep 2197397 = 103003) (by norm_num)
theorem B2197421 : Blo 1464552 2197421 := bbase (se 3 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 2197421 = 824033) (by norm_num)
theorem B1648561 : Blo 1464552 1648561 := bbase (se 2 (by rfl) ⟨618210, by rfl⟩ : syracuseStep 1648561 = 1236421) (by norm_num)
theorem B2197445 : Blo 1464552 2197445 := bbase (se 4 (by rfl) ⟨206010, by rfl⟩ : syracuseStep 2197445 = 412021) (by norm_num)
theorem B1648597 : Blo 1464552 1648597 := bbase (se 7 (by rfl) ⟨19319, by rfl⟩ : syracuseStep 1648597 = 38639) (by norm_num)
theorem B2197469 : Blo 1464552 2197469 := bbase (se 3 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 2197469 = 824051) (by norm_num)
theorem B7423973 : Blo 1464552 7423973 := bbase (se 4 (by rfl) ⟨695997, by rfl⟩ : syracuseStep 7423973 = 1391995) (by norm_num)
theorem B2197493 : Blo 1464552 2197493 := bbase (se 5 (by rfl) ⟨103007, by rfl⟩ : syracuseStep 2197493 = 206015) (by norm_num)
theorem B1648633 : Blo 1464552 1648633 := bbase (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) (by norm_num)
theorem B2197517 : Blo 1464552 2197517 := bbase (se 3 (by rfl) ⟨412034, by rfl⟩ : syracuseStep 2197517 = 824069) (by norm_num)
theorem B1648669 : Blo 1464552 1648669 := bbase (se 3 (by rfl) ⟨309125, by rfl⟩ : syracuseStep 1648669 = 618251) (by norm_num)
theorem B2197541 : Blo 1464552 2197541 := bbase (se 4 (by rfl) ⟨206019, by rfl⟩ : syracuseStep 2197541 = 412039) (by norm_num)
theorem B3295277 : Blo 1464552 3295277 := bbase (se 3 (by rfl) ⟨617864, by rfl⟩ : syracuseStep 3295277 = 1235729) (by norm_num)
theorem B3762221 : Blo 1464552 3762221 := bbase (se 3 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 3762221 = 1410833) (by norm_num)
theorem B2197565 : Blo 1464552 2197565 := bbase (se 3 (by rfl) ⟨412043, by rfl⟩ : syracuseStep 2197565 = 824087) (by norm_num)
theorem B1648705 : Blo 1464552 1648705 := bbase (se 2 (by rfl) ⟨618264, by rfl⟩ : syracuseStep 1648705 = 1236529) (by norm_num)
theorem B2639957 : Blo 1464552 2639957 := bbase (se 8 (by rfl) ⟨15468, by rfl⟩ : syracuseStep 2639957 = 30937) (by norm_num)
theorem B2197589 : Blo 1464552 2197589 := bbase (se 8 (by rfl) ⟨12876, by rfl⟩ : syracuseStep 2197589 = 25753) (by norm_num)
theorem B3131477 : Blo 1464552 3131477 := bbase (se 8 (by rfl) ⟨18348, by rfl⟩ : syracuseStep 3131477 = 36697) (by norm_num)
theorem B1648741 : Blo 1464552 1648741 := bbase (se 4 (by rfl) ⟨154569, by rfl⟩ : syracuseStep 1648741 = 309139) (by norm_num)
theorem B2197613 : Blo 1464552 2197613 := bbase (se 3 (by rfl) ⟨412052, by rfl⟩ : syracuseStep 2197613 = 824105) (by norm_num)
theorem B3295349 : Blo 1464552 3295349 := bbase (se 5 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 3295349 = 308939) (by norm_num)
theorem B2197637 : Blo 1464552 2197637 := bbase (se 4 (by rfl) ⟨206028, by rfl⟩ : syracuseStep 2197637 = 412057) (by norm_num)
theorem B1648777 : Blo 1464552 1648777 := bbase (se 2 (by rfl) ⟨618291, by rfl⟩ : syracuseStep 1648777 = 1236583) (by norm_num)
theorem B2197661 : Blo 1464552 2197661 := bbase (se 3 (by rfl) ⟨412061, by rfl⟩ : syracuseStep 2197661 = 824123) (by norm_num)
theorem B1648813 : Blo 1464552 1648813 := bbase (se 3 (by rfl) ⟨309152, by rfl⟩ : syracuseStep 1648813 = 618305) (by norm_num)
theorem B2197685 : Blo 1464552 2197685 := bbase (se 5 (by rfl) ⟨103016, by rfl⟩ : syracuseStep 2197685 = 206033) (by norm_num)
theorem B3295421 : Blo 1464552 3295421 := bbase (se 3 (by rfl) ⟨617891, by rfl⟩ : syracuseStep 3295421 = 1235783) (by norm_num)
theorem B2197709 : Blo 1464552 2197709 := bbase (se 3 (by rfl) ⟨412070, by rfl⟩ : syracuseStep 2197709 = 824141) (by norm_num)
theorem B3131597 : Blo 1464552 3131597 := bbase (se 3 (by rfl) ⟨587174, by rfl⟩ : syracuseStep 3131597 = 1174349) (by norm_num)
theorem B1648849 : Blo 1464552 1648849 := bbase (se 2 (by rfl) ⟨618318, by rfl⟩ : syracuseStep 1648849 = 1236637) (by norm_num)
theorem B2197733 : Blo 1464552 2197733 := bbase (se 4 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 2197733 = 412075) (by norm_num)
theorem B1648885 : Blo 1464552 1648885 := bbase (se 5 (by rfl) ⟨77291, by rfl⟩ : syracuseStep 1648885 = 154583) (by norm_num)
theorem B2197757 : Blo 1464552 2197757 := bbase (se 3 (by rfl) ⟨412079, by rfl⟩ : syracuseStep 2197757 = 824159) (by norm_num)
theorem B3295493 : Blo 1464552 3295493 := bbase (se 4 (by rfl) ⟨308952, by rfl⟩ : syracuseStep 3295493 = 617905) (by norm_num)
theorem B1853705 : Blo 1464552 1853705 := bbase (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) (by norm_num)
theorem B2197781 : Blo 1464552 2197781 := bbase (se 6 (by rfl) ⟨51510, by rfl⟩ : syracuseStep 2197781 = 103021) (by norm_num)
theorem B1648921 : Blo 1464552 1648921 := bbase (se 2 (by rfl) ⟨618345, by rfl⟩ : syracuseStep 1648921 = 1236691) (by norm_num)
theorem B2197805 : Blo 1464552 2197805 := bbase (se 3 (by rfl) ⟨412088, by rfl⟩ : syracuseStep 2197805 = 824177) (by norm_num)
theorem B1648957 : Blo 1464552 1648957 := bbase (se 3 (by rfl) ⟨309179, by rfl⟩ : syracuseStep 1648957 = 618359) (by norm_num)
theorem B1853761 : Blo 1464552 1853761 := bbase (se 2 (by rfl) ⟨695160, by rfl⟩ : syracuseStep 1853761 = 1390321) (by norm_num)
theorem B2197829 : Blo 1464552 2197829 := bbase (se 4 (by rfl) ⟨206046, by rfl⟩ : syracuseStep 2197829 = 412093) (by norm_num)
theorem B3295565 : Blo 1464552 3295565 := bbase (se 3 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 3295565 = 1235837) (by norm_num)
theorem B2197853 : Blo 1464552 2197853 := bbase (se 3 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 2197853 = 824195) (by norm_num)
theorem B1648993 : Blo 1464552 1648993 := bbase (se 2 (by rfl) ⟨618372, by rfl⟩ : syracuseStep 1648993 = 1236745) (by norm_num)
theorem B2197877 : Blo 1464552 2197877 := bbase (se 5 (by rfl) ⟨103025, by rfl⟩ : syracuseStep 2197877 = 206051) (by norm_num)
theorem B7416197 : Blo 1464552 7416197 := bbase (se 4 (by rfl) ⟨695268, by rfl⟩ : syracuseStep 7416197 = 1390537) (by norm_num)
theorem B1649029 : Blo 1464552 1649029 := bbase (se 4 (by rfl) ⟨154596, by rfl⟩ : syracuseStep 1649029 = 309193) (by norm_num)
theorem B2197901 : Blo 1464552 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B3295637 : Blo 1464552 3295637 := bbase (se 6 (by rfl) ⟨77241, by rfl⟩ : syracuseStep 3295637 = 154483) (by norm_num)
theorem B5564821 : Blo 1464552 5564821 := bbase (se 6 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 5564821 = 260851) (by norm_num)
theorem B1853857 : Blo 1464552 1853857 := bbase (se 2 (by rfl) ⟨695196, by rfl⟩ : syracuseStep 1853857 = 1390393) (by norm_num)
theorem B2197925 : Blo 1464552 2197925 := bbase (se 4 (by rfl) ⟨206055, by rfl⟩ : syracuseStep 2197925 = 412111) (by norm_num)
theorem B1649065 : Blo 1464552 1649065 := bbase (se 2 (by rfl) ⟨618399, by rfl⟩ : syracuseStep 1649065 = 1236799) (by norm_num)
theorem B2197949 : Blo 1464552 2197949 := bbase (se 3 (by rfl) ⟨412115, by rfl⟩ : syracuseStep 2197949 = 824231) (by norm_num)
theorem B1649101 : Blo 1464552 1649101 := bbase (se 3 (by rfl) ⟨309206, by rfl⟩ : syracuseStep 1649101 = 618413) (by norm_num)
theorem B2197973 : Blo 1464552 2197973 := bbase (se 7 (by rfl) ⟨25757, by rfl⟩ : syracuseStep 2197973 = 51515) (by norm_num)
theorem B3295709 : Blo 1464552 3295709 := bbase (se 3 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 3295709 = 1235891) (by norm_num)
theorem B2197997 : Blo 1464552 2197997 := bbase (se 3 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 2197997 = 824249) (by norm_num)
theorem B1649137 : Blo 1464552 1649137 := bbase (se 2 (by rfl) ⟨618426, by rfl⟩ : syracuseStep 1649137 = 1236853) (by norm_num)
theorem B2198021 : Blo 1464552 2198021 := bbase (se 4 (by rfl) ⟨206064, by rfl⟩ : syracuseStep 2198021 = 412129) (by norm_num)
theorem B9390613 : Blo 1464552 9390613 := bbase (se 6 (by rfl) ⟨220092, by rfl⟩ : syracuseStep 9390613 = 440185) (by norm_num)
theorem B1649173 : Blo 1464552 1649173 := bbase (se 6 (by rfl) ⟨38652, by rfl⟩ : syracuseStep 1649173 = 77305) (by norm_num)
theorem B2198045 : Blo 1464552 2198045 := bbase (se 3 (by rfl) ⟨412133, by rfl⟩ : syracuseStep 2198045 = 824267) (by norm_num)
theorem B3295781 : Blo 1464552 3295781 := bbase (se 4 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 3295781 = 617959) (by norm_num)
theorem B2198069 : Blo 1464552 2198069 := bbase (se 5 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 2198069 = 206069) (by norm_num)
theorem B1649209 : Blo 1464552 1649209 := bbase (se 2 (by rfl) ⟨618453, by rfl⟩ : syracuseStep 1649209 = 1236907) (by norm_num)
theorem B1854029 : Blo 1464552 1854029 := bbase (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) (by norm_num)
theorem B2198093 : Blo 1464552 2198093 := bbase (se 3 (by rfl) ⟨412142, by rfl⟩ : syracuseStep 2198093 = 824285) (by norm_num)
theorem B1649245 : Blo 1464552 1649245 := bbase (se 3 (by rfl) ⟨309233, by rfl⟩ : syracuseStep 1649245 = 618467) (by norm_num)
theorem B2198117 : Blo 1464552 2198117 := bbase (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) (by norm_num)
theorem B3295853 : Blo 1464552 3295853 := bbase (se 3 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 3295853 = 1235945) (by norm_num)
theorem B14084725 : Blo 1464552 14084725 := bbase (se 5 (by rfl) ⟨660221, by rfl⟩ : syracuseStep 14084725 = 1320443) (by norm_num)
theorem B2198141 : Blo 1464552 2198141 := bbase (se 3 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 2198141 = 824303) (by norm_num)
theorem B1649281 : Blo 1464552 1649281 := bbase (se 2 (by rfl) ⟨618480, by rfl⟩ : syracuseStep 1649281 = 1236961) (by norm_num)
theorem B1854085 : Blo 1464552 1854085 := bbase (se 4 (by rfl) ⟨173820, by rfl⟩ : syracuseStep 1854085 = 347641) (by norm_num)
theorem B2198165 : Blo 1464552 2198165 := bbase (se 6 (by rfl) ⟨51519, by rfl⟩ : syracuseStep 2198165 = 103039) (by norm_num)
theorem B2640541 : Blo 1464552 2640541 := bbase (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) (by norm_num)
theorem B1649317 : Blo 1464552 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B2198189 : Blo 1464552 2198189 := bbase (se 3 (by rfl) ⟨412160, by rfl⟩ : syracuseStep 2198189 = 824321) (by norm_num)
theorem B3295925 : Blo 1464552 3295925 := bbase (se 5 (by rfl) ⟨154496, by rfl⟩ : syracuseStep 3295925 = 308993) (by norm_num)
theorem B4229813 : Blo 1464552 4229813 := bbase (se 5 (by rfl) ⟨198272, by rfl⟩ : syracuseStep 4229813 = 396545) (by norm_num)
theorem B2198213 : Blo 1464552 2198213 := bbase (se 4 (by rfl) ⟨206082, by rfl⟩ : syracuseStep 2198213 = 412165) (by norm_num)
theorem B5565125 : Blo 1464552 5565125 := bbase (se 4 (by rfl) ⟨521730, by rfl⟩ : syracuseStep 5565125 = 1043461) (by norm_num)
theorem B1649353 : Blo 1464552 1649353 := bbase (se 2 (by rfl) ⟨618507, by rfl⟩ : syracuseStep 1649353 = 1237015) (by norm_num)
theorem B2198237 : Blo 1464552 2198237 := bbase (se 3 (by rfl) ⟨412169, by rfl⟩ : syracuseStep 2198237 = 824339) (by norm_num)
theorem B1854181 : Blo 1464552 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B4696805 : Blo 1464552 4696805 := bbase (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) (by norm_num)
theorem B1649389 : Blo 1464552 1649389 := bbase (se 3 (by rfl) ⟨309260, by rfl⟩ : syracuseStep 1649389 = 618521) (by norm_num)
theorem B2198261 : Blo 1464552 2198261 := bbase (se 5 (by rfl) ⟨103043, by rfl⟩ : syracuseStep 2198261 = 206087) (by norm_num)
theorem B3295997 : Blo 1464552 3295997 := bbase (se 3 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 3295997 = 1235999) (by norm_num)
theorem B2198285 : Blo 1464552 2198285 := bbase (se 3 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 2198285 = 824357) (by norm_num)
theorem B1649425 : Blo 1464552 1649425 := bbase (se 2 (by rfl) ⟨618534, by rfl⟩ : syracuseStep 1649425 = 1237069) (by norm_num)
theorem B2198309 : Blo 1464552 2198309 := bbase (se 4 (by rfl) ⟨206091, by rfl⟩ : syracuseStep 2198309 = 412183) (by norm_num)
theorem B1649461 : Blo 1464552 1649461 := bbase (se 5 (by rfl) ⟨77318, by rfl⟩ : syracuseStep 1649461 = 154637) (by norm_num)
theorem B2198333 : Blo 1464552 2198333 := bbase (se 3 (by rfl) ⟨412187, by rfl⟩ : syracuseStep 2198333 = 824375) (by norm_num)
theorem B3296069 : Blo 1464552 3296069 := bbase (se 4 (by rfl) ⟨309006, by rfl⟩ : syracuseStep 3296069 = 618013) (by norm_num)
theorem B2198357 : Blo 1464552 2198357 := bbase (se 9 (by rfl) ⟨6440, by rfl⟩ : syracuseStep 2198357 = 12881) (by norm_num)
theorem B1649497 : Blo 1464552 1649497 := bbase (se 2 (by rfl) ⟨618561, by rfl⟩ : syracuseStep 1649497 = 1237123) (by norm_num)
theorem B2198381 : Blo 1464552 2198381 := bbase (se 3 (by rfl) ⟨412196, by rfl⟩ : syracuseStep 2198381 = 824393) (by norm_num)
theorem B1649533 : Blo 1464552 1649533 := bbase (se 3 (by rfl) ⟨309287, by rfl⟩ : syracuseStep 1649533 = 618575) (by norm_num)
theorem B2198405 : Blo 1464552 2198405 := bbase (se 4 (by rfl) ⟨206100, by rfl⟩ : syracuseStep 2198405 = 412201) (by norm_num)
theorem B3296141 : Blo 1464552 3296141 := bbase (se 3 (by rfl) ⟨618026, by rfl⟩ : syracuseStep 3296141 = 1236053) (by norm_num)
theorem B1854353 : Blo 1464552 1854353 := bbase (se 2 (by rfl) ⟨695382, by rfl⟩ : syracuseStep 1854353 = 1390765) (by norm_num)
theorem B2198429 : Blo 1464552 2198429 := bbase (se 3 (by rfl) ⟨412205, by rfl⟩ : syracuseStep 2198429 = 824411) (by norm_num)
theorem B1649569 : Blo 1464552 1649569 := bbase (se 2 (by rfl) ⟨618588, by rfl⟩ : syracuseStep 1649569 = 1237177) (by norm_num)
theorem B2198453 : Blo 1464552 2198453 := bbase (se 5 (by rfl) ⟨103052, by rfl⟩ : syracuseStep 2198453 = 206105) (by norm_num)
theorem B5721013 : Blo 1464552 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B1878977 : Blo 1464552 1878977 := bbase (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) (by norm_num)
theorem B1649605 : Blo 1464552 1649605 := bbase (se 4 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 1649605 = 309301) (by norm_num)
theorem B1854409 : Blo 1464552 1854409 := bbase (se 2 (by rfl) ⟨695403, by rfl⟩ : syracuseStep 1854409 = 1390807) (by norm_num)
theorem B2198477 : Blo 1464552 2198477 := bbase (se 3 (by rfl) ⟨412214, by rfl⟩ : syracuseStep 2198477 = 824429) (by norm_num)
theorem B3296213 : Blo 1464552 3296213 := bbase (se 7 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 3296213 = 77255) (by norm_num)
theorem B2198501 : Blo 1464552 2198501 := bbase (se 4 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 2198501 = 412219) (by norm_num)
theorem B1649641 : Blo 1464552 1649641 := bbase (se 2 (by rfl) ⟨618615, by rfl⟩ : syracuseStep 1649641 = 1237231) (by norm_num)
theorem B2198525 : Blo 1464552 2198525 := bbase (se 3 (by rfl) ⟨412223, by rfl⟩ : syracuseStep 2198525 = 824447) (by norm_num)
theorem B1649677 : Blo 1464552 1649677 := bbase (se 3 (by rfl) ⟨309314, by rfl⟩ : syracuseStep 1649677 = 618629) (by norm_num)
theorem B2198549 : Blo 1464552 2198549 := bbase (se 6 (by rfl) ⟨51528, by rfl⟩ : syracuseStep 2198549 = 103057) (by norm_num)
theorem B2346013 : Blo 1464552 2346013 := bbase (se 3 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 2346013 = 879755) (by norm_num)
theorem B3296285 : Blo 1464552 3296285 := bbase (se 3 (by rfl) ⟨618053, by rfl⟩ : syracuseStep 3296285 = 1236107) (by norm_num)
theorem B1854505 : Blo 1464552 1854505 := bbase (se 2 (by rfl) ⟨695439, by rfl⟩ : syracuseStep 1854505 = 1390879) (by norm_num)
theorem B2198573 : Blo 1464552 2198573 := bbase (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) (by norm_num)
theorem B1649713 : Blo 1464552 1649713 := bbase (se 2 (by rfl) ⟨618642, by rfl⟩ : syracuseStep 1649713 = 1237285) (by norm_num)
theorem B2198597 : Blo 1464552 2198597 := bbase (se 4 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 2198597 = 412237) (by norm_num)
theorem B1649749 : Blo 1464552 1649749 := bbase (se 8 (by rfl) ⟨9666, by rfl⟩ : syracuseStep 1649749 = 19333) (by norm_num)
theorem B2198621 : Blo 1464552 2198621 := bbase (se 3 (by rfl) ⟨412241, by rfl⟩ : syracuseStep 2198621 = 824483) (by norm_num)
theorem B3296357 : Blo 1464552 3296357 := bbase (se 4 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 3296357 = 618067) (by norm_num)
theorem B2198645 : Blo 1464552 2198645 := bbase (se 5 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 2198645 = 206123) (by norm_num)
theorem B1649785 : Blo 1464552 1649785 := bbase (se 2 (by rfl) ⟨618669, by rfl⟩ : syracuseStep 1649785 = 1237339) (by norm_num)
theorem B4172933 : Blo 1464552 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B2198669 : Blo 1464552 2198669 := bbase (se 3 (by rfl) ⟨412250, by rfl⟩ : syracuseStep 2198669 = 824501) (by norm_num)
theorem B4942997 : Blo 1464552 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1649821 : Blo 1464552 1649821 := bbase (se 3 (by rfl) ⟨309341, by rfl⟩ : syracuseStep 1649821 = 618683) (by norm_num)
theorem B2198693 : Blo 1464552 2198693 := bbase (se 4 (by rfl) ⟨206127, by rfl⟩ : syracuseStep 2198693 = 412255) (by norm_num)
theorem B3296429 : Blo 1464552 3296429 := bbase (se 3 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 3296429 = 1236161) (by norm_num)
theorem B2346173 : Blo 1464552 2346173 := bbase (se 3 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 2346173 = 879815) (by norm_num)
theorem B2198717 : Blo 1464552 2198717 := bbase (se 3 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 2198717 = 824519) (by norm_num)
theorem B1649857 : Blo 1464552 1649857 := bbase (se 2 (by rfl) ⟨618696, by rfl⟩ : syracuseStep 1649857 = 1237393) (by norm_num)
theorem B1854677 : Blo 1464552 1854677 := bbase (se 7 (by rfl) ⟨21734, by rfl⟩ : syracuseStep 1854677 = 43469) (by norm_num)
theorem B2198741 : Blo 1464552 2198741 := bbase (se 7 (by rfl) ⟨25766, by rfl⟩ : syracuseStep 2198741 = 51533) (by norm_num)
theorem B2198765 : Blo 1464552 2198765 := bbase (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) (by norm_num)
theorem B3296501 : Blo 1464552 3296501 := bbase (se 5 (by rfl) ⟨154523, by rfl⟩ : syracuseStep 3296501 = 309047) (by norm_num)
theorem B2198789 : Blo 1464552 2198789 := bbase (se 4 (by rfl) ⟨206136, by rfl⟩ : syracuseStep 2198789 = 412273) (by norm_num)
theorem B1854733 : Blo 1464552 1854733 := bbase (se 3 (by rfl) ⟨347762, by rfl⟩ : syracuseStep 1854733 = 695525) (by norm_num)
theorem B2198813 : Blo 1464552 2198813 := bbase (se 3 (by rfl) ⟨412277, by rfl⟩ : syracuseStep 2198813 = 824555) (by norm_num)
theorem B8342837 : Blo 1464552 8342837 := bbase (se 5 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 8342837 = 782141) (by norm_num)
theorem B2198837 : Blo 1464552 2198837 := bbase (se 5 (by rfl) ⟨103070, by rfl⟩ : syracuseStep 2198837 = 206141) (by norm_num)
theorem B3296573 : Blo 1464552 3296573 := bbase (se 3 (by rfl) ⟨618107, by rfl⟩ : syracuseStep 3296573 = 1236215) (by norm_num)
theorem B2198861 : Blo 1464552 2198861 := bbase (se 3 (by rfl) ⟨412286, by rfl⟩ : syracuseStep 2198861 = 824573) (by norm_num)
theorem B2198885 : Blo 1464552 2198885 := bbase (se 4 (by rfl) ⟨206145, by rfl⟩ : syracuseStep 2198885 = 412291) (by norm_num)
theorem B1854829 : Blo 1464552 1854829 := bbase (se 3 (by rfl) ⟨347780, by rfl⟩ : syracuseStep 1854829 = 695561) (by norm_num)
theorem B5942645 : Blo 1464552 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B2198909 : Blo 1464552 2198909 := bbase (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) (by norm_num)
theorem B3960197 : Blo 1464552 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B3296645 : Blo 1464552 3296645 := bbase (se 4 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 3296645 = 618121) (by norm_num)
theorem B2198933 : Blo 1464552 2198933 := bbase (se 6 (by rfl) ⟨51537, by rfl⟩ : syracuseStep 2198933 = 103075) (by norm_num)
theorem B2780581 : Blo 1464552 2780581 := bbase (se 4 (by rfl) ⟨260679, by rfl⟩ : syracuseStep 2780581 = 521359) (by norm_num)
theorem B2198957 : Blo 1464552 2198957 := bbase (se 3 (by rfl) ⟨412304, by rfl⟩ : syracuseStep 2198957 = 824609) (by norm_num)
theorem B2198981 : Blo 1464552 2198981 := bbase (se 4 (by rfl) ⟨206154, by rfl⟩ : syracuseStep 2198981 = 412309) (by norm_num)
theorem B3296717 : Blo 1464552 3296717 := bbase (se 3 (by rfl) ⟨618134, by rfl⟩ : syracuseStep 3296717 = 1236269) (by norm_num)
theorem B2199005 : Blo 1464552 2199005 := bbase (se 3 (by rfl) ⟨412313, by rfl⟩ : syracuseStep 2199005 = 824627) (by norm_num)
theorem B2199029 : Blo 1464552 2199029 := bbase (se 5 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 2199029 = 206159) (by norm_num)
theorem B2199053 : Blo 1464552 2199053 := bbase (se 3 (by rfl) ⟨412322, by rfl⟩ : syracuseStep 2199053 = 824645) (by norm_num)
theorem B3296789 : Blo 1464552 3296789 := bbase (se 6 (by rfl) ⟨77268, by rfl⟩ : syracuseStep 3296789 = 154537) (by norm_num)
theorem B1855001 : Blo 1464552 1855001 := bbase (se 2 (by rfl) ⟨695625, by rfl⟩ : syracuseStep 1855001 = 1391251) (by norm_num)
theorem B2199077 : Blo 1464552 2199077 := bbase (se 4 (by rfl) ⟨206163, by rfl⟩ : syracuseStep 2199077 = 412327) (by norm_num)
theorem B2780725 : Blo 1464552 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B2199101 : Blo 1464552 2199101 := bbase (se 3 (by rfl) ⟨412331, by rfl⟩ : syracuseStep 2199101 = 824663) (by norm_num)
theorem B4943429 : Blo 1464552 4943429 := bbase (se 4 (by rfl) ⟨463446, by rfl⟩ : syracuseStep 4943429 = 926893) (by norm_num)
theorem B1855057 : Blo 1464552 1855057 := bbase (se 2 (by rfl) ⟨695646, by rfl⟩ : syracuseStep 1855057 = 1391293) (by norm_num)
theorem B2199125 : Blo 1464552 2199125 := bbase (se 8 (by rfl) ⟨12885, by rfl⟩ : syracuseStep 2199125 = 25771) (by norm_num)
theorem B3296861 : Blo 1464552 3296861 := bbase (se 3 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 3296861 = 1236323) (by norm_num)
theorem B6262373 : Blo 1464552 6262373 := bbase (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) (by norm_num)
theorem B2199149 : Blo 1464552 2199149 := bbase (se 3 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 2199149 = 824681) (by norm_num)
theorem B2199173 : Blo 1464552 2199173 := bbase (se 4 (by rfl) ⟨206172, by rfl⟩ : syracuseStep 2199173 = 412345) (by norm_num)
theorem B7417493 : Blo 1464552 7417493 := bbase (se 6 (by rfl) ⟨173847, by rfl⟩ : syracuseStep 7417493 = 347695) (by norm_num)
theorem B3526301 : Blo 1464552 3526301 := bbase (se 3 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 3526301 = 1322363) (by norm_num)
theorem B2199197 : Blo 1464552 2199197 := bbase (se 3 (by rfl) ⟨412349, by rfl⟩ : syracuseStep 2199197 = 824699) (by norm_num)
theorem B3296933 : Blo 1464552 3296933 := bbase (se 4 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 3296933 = 618175) (by norm_num)
theorem B1855153 : Blo 1464552 1855153 := bbase (se 2 (by rfl) ⟨695682, by rfl⟩ : syracuseStep 1855153 = 1391365) (by norm_num)
theorem B2199221 : Blo 1464552 2199221 := bbase (se 5 (by rfl) ⟨103088, by rfl⟩ : syracuseStep 2199221 = 206177) (by norm_num)
theorem B2199245 : Blo 1464552 2199245 := bbase (se 3 (by rfl) ⟨412358, by rfl⟩ : syracuseStep 2199245 = 824717) (by norm_num)
theorem B2780885 : Blo 1464552 2780885 := bbase (se 7 (by rfl) ⟨32588, by rfl⟩ : syracuseStep 2780885 = 65177) (by norm_num)
theorem B2199269 : Blo 1464552 2199269 := bbase (se 4 (by rfl) ⟨206181, by rfl⟩ : syracuseStep 2199269 = 412363) (by norm_num)
theorem B3297005 : Blo 1464552 3297005 := bbase (se 3 (by rfl) ⟨618188, by rfl⟩ : syracuseStep 3297005 = 1236377) (by norm_num)
theorem B2199293 : Blo 1464552 2199293 := bbase (se 3 (by rfl) ⟨412367, by rfl⟩ : syracuseStep 2199293 = 824735) (by norm_num)
theorem B2199317 : Blo 1464552 2199317 := bbase (se 6 (by rfl) ⟨51546, by rfl⟩ : syracuseStep 2199317 = 103093) (by norm_num)
theorem B5279525 : Blo 1464552 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B2641709 : Blo 1464552 2641709 := bbase (se 3 (by rfl) ⟨495320, by rfl⟩ : syracuseStep 2641709 = 990641) (by norm_num)
theorem B2199341 : Blo 1464552 2199341 := bbase (se 3 (by rfl) ⟨412376, by rfl⟩ : syracuseStep 2199341 = 824753) (by norm_num)
theorem B3297077 : Blo 1464552 3297077 := bbase (se 5 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 3297077 = 309101) (by norm_num)
theorem B4697909 : Blo 1464552 4697909 := bbase (se 5 (by rfl) ⟨220214, by rfl⟩ : syracuseStep 4697909 = 440429) (by norm_num)
theorem B2199365 : Blo 1464552 2199365 := bbase (se 4 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 2199365 = 412381) (by norm_num)
theorem B1855325 : Blo 1464552 1855325 := bbase (se 3 (by rfl) ⟨347873, by rfl⟩ : syracuseStep 1855325 = 695747) (by norm_num)
theorem B2199389 : Blo 1464552 2199389 := bbase (se 3 (by rfl) ⟨412385, by rfl⟩ : syracuseStep 2199389 = 824771) (by norm_num)
theorem B2781029 : Blo 1464552 2781029 := bbase (se 4 (by rfl) ⟨260721, by rfl⟩ : syracuseStep 2781029 = 521443) (by norm_num)
theorem B2199413 : Blo 1464552 2199413 := bbase (se 5 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 2199413 = 206195) (by norm_num)
theorem B3297149 : Blo 1464552 3297149 := bbase (se 3 (by rfl) ⟨618215, by rfl⟩ : syracuseStep 3297149 = 1236431) (by norm_num)
theorem B2199437 : Blo 1464552 2199437 := bbase (se 3 (by rfl) ⟨412394, by rfl⟩ : syracuseStep 2199437 = 824789) (by norm_num)
theorem B1855381 : Blo 1464552 1855381 := bbase (se 6 (by rfl) ⟨43485, by rfl⟩ : syracuseStep 1855381 = 86971) (by norm_num)
theorem B2199461 : Blo 1464552 2199461 := bbase (se 4 (by rfl) ⟨206199, by rfl⟩ : syracuseStep 2199461 = 412399) (by norm_num)
theorem B2199485 : Blo 1464552 2199485 := bbase (se 3 (by rfl) ⟨412403, by rfl⟩ : syracuseStep 2199485 = 824807) (by norm_num)
theorem B3297221 : Blo 1464552 3297221 := bbase (se 4 (by rfl) ⟨309114, by rfl⟩ : syracuseStep 3297221 = 618229) (by norm_num)
theorem B2199509 : Blo 1464552 2199509 := bbase (se 7 (by rfl) ⟨25775, by rfl⟩ : syracuseStep 2199509 = 51551) (by norm_num)
theorem B2199533 : Blo 1464552 2199533 := bbase (se 3 (by rfl) ⟨412412, by rfl⟩ : syracuseStep 2199533 = 824825) (by norm_num)
theorem B4943861 : Blo 1464552 4943861 := bbase (se 5 (by rfl) ⟨231743, by rfl⟩ : syracuseStep 4943861 = 463487) (by norm_num)
theorem B1855477 : Blo 1464552 1855477 := bbase (se 5 (by rfl) ⟨86975, by rfl⟩ : syracuseStep 1855477 = 173951) (by norm_num)
theorem B2199557 : Blo 1464552 2199557 := bbase (se 4 (by rfl) ⟨206208, by rfl⟩ : syracuseStep 2199557 = 412417) (by norm_num)
theorem B3297293 : Blo 1464552 3297293 := bbase (se 3 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 3297293 = 1236485) (by norm_num)
theorem B10563605 : Blo 1464552 10563605 := bbase (se 6 (by rfl) ⟨247584, by rfl⟩ : syracuseStep 10563605 = 495169) (by norm_num)
theorem B2199581 : Blo 1464552 2199581 := bbase (se 3 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 2199581 = 824843) (by norm_num)
theorem B2199605 : Blo 1464552 2199605 := bbase (se 5 (by rfl) ⟨103106, by rfl⟩ : syracuseStep 2199605 = 206213) (by norm_num)
theorem B2199629 : Blo 1464552 2199629 := bbase (se 3 (by rfl) ⟨412430, by rfl⟩ : syracuseStep 2199629 = 824861) (by norm_num)
theorem B3297365 : Blo 1464552 3297365 := bbase (se 8 (by rfl) ⟨19320, by rfl⟩ : syracuseStep 3297365 = 38641) (by norm_num)
theorem B2199653 : Blo 1464552 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B2199677 : Blo 1464552 2199677 := bbase (se 3 (by rfl) ⟨412439, by rfl⟩ : syracuseStep 2199677 = 824879) (by norm_num)
theorem B2781317 : Blo 1464552 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B2199701 : Blo 1464552 2199701 := bbase (se 6 (by rfl) ⟨51555, by rfl⟩ : syracuseStep 2199701 = 103111) (by norm_num)
theorem B3297437 : Blo 1464552 3297437 := bbase (se 3 (by rfl) ⟨618269, by rfl⟩ : syracuseStep 3297437 = 1236539) (by norm_num)
theorem B1855649 : Blo 1464552 1855649 := bbase (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) (by norm_num)
theorem B2379949 : Blo 1464552 2379949 := bbase (se 3 (by rfl) ⟨446240, by rfl⟩ : syracuseStep 2379949 = 892481) (by norm_num)
theorem B2199725 : Blo 1464552 2199725 := bbase (se 3 (by rfl) ⟨412448, by rfl⟩ : syracuseStep 2199725 = 824897) (by norm_num)
theorem B2199749 : Blo 1464552 2199749 := bbase (se 4 (by rfl) ⟨206226, by rfl⟩ : syracuseStep 2199749 = 412453) (by norm_num)
theorem B1855705 : Blo 1464552 1855705 := bbase (se 2 (by rfl) ⟨695889, by rfl⟩ : syracuseStep 1855705 = 1391779) (by norm_num)
theorem B2199773 : Blo 1464552 2199773 := bbase (se 3 (by rfl) ⟨412457, by rfl⟩ : syracuseStep 2199773 = 824915) (by norm_num)
theorem B3297509 : Blo 1464552 3297509 := bbase (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) (by norm_num)
theorem B2642149 : Blo 1464552 2642149 := bbase (se 4 (by rfl) ⟨247701, by rfl⟩ : syracuseStep 2642149 = 495403) (by norm_num)
theorem B2199797 : Blo 1464552 2199797 := bbase (se 5 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 2199797 = 206231) (by norm_num)
theorem B2199821 : Blo 1464552 2199821 := bbase (se 3 (by rfl) ⟨412466, by rfl⟩ : syracuseStep 2199821 = 824933) (by norm_num)
theorem B1880341 : Blo 1464552 1880341 := bbase (se 6 (by rfl) ⟨44070, by rfl⟩ : syracuseStep 1880341 = 88141) (by norm_num)
theorem B2781469 : Blo 1464552 2781469 := bbase (se 3 (by rfl) ⟨521525, by rfl⟩ : syracuseStep 2781469 = 1043051) (by norm_num)
theorem B2347301 : Blo 1464552 2347301 := bbase (se 4 (by rfl) ⟨220059, by rfl⟩ : syracuseStep 2347301 = 440119) (by norm_num)
theorem B2642213 : Blo 1464552 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B3297581 : Blo 1464552 3297581 := bbase (se 3 (by rfl) ⟨618296, by rfl⟩ : syracuseStep 3297581 = 1236593) (by norm_num)
theorem B1855801 : Blo 1464552 1855801 := bbase (se 2 (by rfl) ⟨695925, by rfl⟩ : syracuseStep 1855801 = 1391851) (by norm_num)
theorem B3297653 : Blo 1464552 3297653 := bbase (se 5 (by rfl) ⟨154577, by rfl⟩ : syracuseStep 3297653 = 309155) (by norm_num)
theorem B3567997 : Blo 1464552 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B4944293 : Blo 1464552 4944293 := bbase (se 4 (by rfl) ⟨463527, by rfl⟩ : syracuseStep 4944293 = 927055) (by norm_num)
theorem B3707309 : Blo 1464552 3707309 := bbase (se 3 (by rfl) ⟨695120, by rfl⟩ : syracuseStep 3707309 = 1390241) (by norm_num)
theorem B3297725 : Blo 1464552 3297725 := bbase (se 3 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 3297725 = 1236647) (by norm_num)
theorem B1855973 : Blo 1464552 1855973 := bbase (se 4 (by rfl) ⟨173997, by rfl⟩ : syracuseStep 1855973 = 347995) (by norm_num)
theorem B2085373 : Blo 1464552 2085373 := bbase (se 3 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 2085373 = 782015) (by norm_num)
theorem B3297797 : Blo 1464552 3297797 := bbase (se 4 (by rfl) ⟨309168, by rfl⟩ : syracuseStep 3297797 = 618337) (by norm_num)
theorem B1856029 : Blo 1464552 1856029 := bbase (se 3 (by rfl) ⟨348005, by rfl⟩ : syracuseStep 1856029 = 696011) (by norm_num)
theorem B7524917 : Blo 1464552 7524917 := bbase (se 5 (by rfl) ⟨352730, by rfl⟩ : syracuseStep 7524917 = 705461) (by norm_num)
theorem B2642501 : Blo 1464552 2642501 := bbase (se 4 (by rfl) ⟨247734, by rfl⟩ : syracuseStep 2642501 = 495469) (by norm_num)
theorem B2781773 : Blo 1464552 2781773 := bbase (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) (by norm_num)
theorem B3297869 : Blo 1464552 3297869 := bbase (se 3 (by rfl) ⟨618350, by rfl⟩ : syracuseStep 3297869 = 1236701) (by norm_num)
theorem B3297941 : Blo 1464552 3297941 := bbase (se 6 (by rfl) ⟨77295, by rfl⟩ : syracuseStep 3297941 = 154591) (by norm_num)
theorem B2257565 : Blo 1464552 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B4174517 : Blo 1464552 4174517 := bbase (se 5 (by rfl) ⟨195680, by rfl⟩ : syracuseStep 4174517 = 391361) (by norm_num)
theorem B3298013 : Blo 1464552 3298013 := bbase (se 3 (by rfl) ⟨618377, by rfl⟩ : syracuseStep 3298013 = 1236755) (by norm_num)
theorem B3707653 : Blo 1464552 3707653 := bbase (se 4 (by rfl) ⟨347592, by rfl⟩ : syracuseStep 3707653 = 695185) (by norm_num)
theorem B5567237 : Blo 1464552 5567237 := bbase (se 4 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 5567237 = 1043857) (by norm_num)
theorem B2347813 : Blo 1464552 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B3298085 : Blo 1464552 3298085 := bbase (se 4 (by rfl) ⟨309195, by rfl⟩ : syracuseStep 3298085 = 618391) (by norm_num)
theorem B4944725 : Blo 1464552 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B3298157 : Blo 1464552 3298157 := bbase (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) (by norm_num)
theorem B3707765 : Blo 1464552 3707765 := bbase (se 5 (by rfl) ⟨173801, by rfl⟩ : syracuseStep 3707765 = 347603) (by norm_num)
theorem B7418789 : Blo 1464552 7418789 := bbase (se 4 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 7418789 = 1391023) (by norm_num)
theorem B3298229 : Blo 1464552 3298229 := bbase (se 5 (by rfl) ⟨154604, by rfl⟩ : syracuseStep 3298229 = 309209) (by norm_num)
theorem B1979389 : Blo 1464552 1979389 := bbase (se 3 (by rfl) ⟨371135, by rfl⟩ : syracuseStep 1979389 = 742271) (by norm_num)
theorem B3298301 : Blo 1464552 3298301 := bbase (se 3 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 3298301 = 1236863) (by norm_num)
theorem B5567525 : Blo 1464552 5567525 := bbase (se 4 (by rfl) ⟨521955, by rfl⟩ : syracuseStep 5567525 = 1043911) (by norm_num)
theorem B3707957 : Blo 1464552 3707957 := bbase (se 5 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 3707957 = 347621) (by norm_num)
theorem B3298373 : Blo 1464552 3298373 := bbase (se 4 (by rfl) ⟨309222, by rfl⟩ : syracuseStep 3298373 = 618445) (by norm_num)
theorem B7042133 : Blo 1464552 7042133 := bbase (se 8 (by rfl) ⟨41262, by rfl⟩ : syracuseStep 7042133 = 82525) (by norm_num)
theorem B3298445 : Blo 1464552 3298445 := bbase (se 3 (by rfl) ⟨618458, by rfl⟩ : syracuseStep 3298445 = 1236917) (by norm_num)
theorem B5280965 : Blo 1464552 5280965 := bbase (se 4 (by rfl) ⟨495090, by rfl⟩ : syracuseStep 5280965 = 990181) (by norm_num)
theorem B27112661 : Blo 1464552 27112661 := bbase (se 7 (by rfl) ⟨317726, by rfl⟩ : syracuseStep 27112661 = 635453) (by norm_num)
theorem B3298517 : Blo 1464552 3298517 := bbase (se 7 (by rfl) ⟨38654, by rfl⟩ : syracuseStep 3298517 = 77309) (by norm_num)
theorem B4945157 : Blo 1464552 4945157 := bbase (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) (by norm_num)
theorem B2086165 : Blo 1464552 2086165 := bbase (se 6 (by rfl) ⟨48894, by rfl⟩ : syracuseStep 2086165 = 97789) (by norm_num)
theorem B3298589 : Blo 1464552 3298589 := bbase (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) (by norm_num)
theorem B2782525 : Blo 1464552 2782525 := bbase (se 3 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 2782525 = 1043447) (by norm_num)
theorem B4175189 : Blo 1464552 4175189 := bbase (se 13 (by rfl) ⟨764, by rfl⟩ : syracuseStep 4175189 = 1529) (by norm_num)
theorem B3298661 : Blo 1464552 3298661 := bbase (se 4 (by rfl) ⟨309249, by rfl⟩ : syracuseStep 3298661 = 618499) (by norm_num)
theorem B3708301 : Blo 1464552 3708301 := bbase (se 3 (by rfl) ⟨695306, by rfl⟩ : syracuseStep 3708301 = 1390613) (by norm_num)
theorem B3298733 : Blo 1464552 3298733 := bbase (se 3 (by rfl) ⟨618512, by rfl⟩ : syracuseStep 3298733 = 1237025) (by norm_num)
theorem B2782669 : Blo 1464552 2782669 := bbase (se 3 (by rfl) ⟨521750, by rfl⟩ : syracuseStep 2782669 = 1043501) (by norm_num)
theorem B8345045 : Blo 1464552 8345045 := bbase (se 7 (by rfl) ⟨97793, by rfl⟩ : syracuseStep 8345045 = 195587) (by norm_num)
theorem B7042517 : Blo 1464552 7042517 := bbase (se 7 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 7042517 = 165059) (by norm_num)
theorem B3298805 : Blo 1464552 3298805 := bbase (se 5 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 3298805 = 309263) (by norm_num)
theorem B3708413 : Blo 1464552 3708413 := bbase (se 3 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 3708413 = 1390655) (by norm_num)
theorem B1504813 : Blo 1464552 1504813 := bbase (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) (by norm_num)
theorem B2471485 : Blo 1464552 2471485 := bbase (se 3 (by rfl) ⟨463403, by rfl⟩ : syracuseStep 2471485 = 926807) (by norm_num)
theorem B3298877 : Blo 1464552 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B2086501 : Blo 1464552 2086501 := bbase (se 4 (by rfl) ⟨195609, by rfl⟩ : syracuseStep 2086501 = 391219) (by norm_num)
theorem B2782829 : Blo 1464552 2782829 := bbase (se 3 (by rfl) ⟨521780, by rfl⟩ : syracuseStep 2782829 = 1043561) (by norm_num)
theorem B3298949 : Blo 1464552 3298949 := bbase (se 4 (by rfl) ⟨309276, by rfl⟩ : syracuseStep 3298949 = 618553) (by norm_num)
theorem B2471573 : Blo 1464552 2471573 := bbase (se 6 (by rfl) ⟨57927, by rfl⟩ : syracuseStep 2471573 = 115855) (by norm_num)
theorem B4945589 : Blo 1464552 4945589 := bbase (se 5 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 4945589 = 463649) (by norm_num)
theorem B3708605 : Blo 1464552 3708605 := bbase (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) (by norm_num)
theorem B3299021 : Blo 1464552 3299021 := bbase (se 3 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 3299021 = 1237133) (by norm_num)
theorem B2782973 : Blo 1464552 2782973 := bbase (se 3 (by rfl) ⟨521807, by rfl⟩ : syracuseStep 2782973 = 1043615) (by norm_num)
theorem B4888325 : Blo 1464552 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B4175621 : Blo 1464552 4175621 := bbase (se 4 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 4175621 = 782929) (by norm_num)
theorem B2348813 : Blo 1464552 2348813 := bbase (se 3 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 2348813 = 880805) (by norm_num)
theorem B2471701 : Blo 1464552 2471701 := bbase (se 6 (by rfl) ⟨57930, by rfl⟩ : syracuseStep 2471701 = 115861) (by norm_num)
theorem B3299093 : Blo 1464552 3299093 := bbase (se 6 (by rfl) ⟨77322, by rfl⟩ : syracuseStep 3299093 = 154645) (by norm_num)
theorem B2086717 : Blo 1464552 2086717 := bbase (se 3 (by rfl) ⟨391259, by rfl⟩ : syracuseStep 2086717 = 782519) (by norm_num)
theorem B3299165 : Blo 1464552 3299165 := bbase (se 3 (by rfl) ⟨618593, by rfl⟩ : syracuseStep 3299165 = 1237187) (by norm_num)
theorem B2471789 : Blo 1464552 2471789 := bbase (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) (by norm_num)
theorem B2348941 : Blo 1464552 2348941 := bbase (se 3 (by rfl) ⟨440426, by rfl⟩ : syracuseStep 2348941 = 880853) (by norm_num)
theorem B3299237 : Blo 1464552 3299237 := bbase (se 4 (by rfl) ⟨309303, by rfl⟩ : syracuseStep 3299237 = 618607) (by norm_num)
theorem B2349005 : Blo 1464552 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B6256597 : Blo 1464552 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B22566869 : Blo 1464552 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2471917 : Blo 1464552 2471917 := bbase (se 3 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 2471917 = 926969) (by norm_num)
theorem B3299309 : Blo 1464552 3299309 := bbase (se 3 (by rfl) ⟨618620, by rfl⟩ : syracuseStep 3299309 = 1237241) (by norm_num)
theorem B4454405 : Blo 1464552 4454405 := bbase (se 4 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 4454405 = 835201) (by norm_num)
theorem B3708949 : Blo 1464552 3708949 := bbase (se 6 (by rfl) ⟨86928, by rfl⟩ : syracuseStep 3708949 = 173857) (by norm_num)
theorem B1980445 : Blo 1464552 1980445 := bbase (se 3 (by rfl) ⟨371333, by rfl⟩ : syracuseStep 1980445 = 742667) (by norm_num)
theorem B2783261 : Blo 1464552 2783261 := bbase (se 3 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 2783261 = 1043723) (by norm_num)
theorem B12515381 : Blo 1464552 12515381 := bbase (se 5 (by rfl) ⟨586658, by rfl⟩ : syracuseStep 12515381 = 1173317) (by norm_num)
theorem B3299381 : Blo 1464552 3299381 := bbase (se 5 (by rfl) ⟨154658, by rfl⟩ : syracuseStep 3299381 = 309317) (by norm_num)
theorem B2472005 : Blo 1464552 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B3962965 : Blo 1464552 3962965 := bbase (se 8 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 3962965 = 46441) (by norm_num)
theorem B4946021 : Blo 1464552 4946021 := bbase (se 4 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 4946021 = 927379) (by norm_num)
theorem B12384373 : Blo 1464552 12384373 := bbase (se 5 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 12384373 = 1161035) (by norm_num)
theorem B3299453 : Blo 1464552 3299453 := bbase (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) (by norm_num)
theorem B3340421 : Blo 1464552 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B3709061 : Blo 1464552 3709061 := bbase (se 4 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 3709061 = 695449) (by norm_num)
theorem B7420085 : Blo 1464552 7420085 := bbase (se 5 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 7420085 = 695633) (by norm_num)
theorem B2087093 : Blo 1464552 2087093 := bbase (se 5 (by rfl) ⟨97832, by rfl⟩ : syracuseStep 2087093 = 195665) (by norm_num)
theorem B2783413 : Blo 1464552 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B2472133 : Blo 1464552 2472133 := bbase (se 4 (by rfl) ⟨231762, by rfl⟩ : syracuseStep 2472133 = 463525) (by norm_num)
theorem B3299525 : Blo 1464552 3299525 := bbase (se 4 (by rfl) ⟨309330, by rfl⟩ : syracuseStep 3299525 = 618661) (by norm_num)
theorem B1808605 : Blo 1464552 1808605 := bbase (se 3 (by rfl) ⟨339113, by rfl⟩ : syracuseStep 1808605 = 678227) (by norm_num)
theorem B3299597 : Blo 1464552 3299597 := bbase (se 3 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 3299597 = 1237349) (by norm_num)
theorem B2472221 : Blo 1464552 2472221 := bbase (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) (by norm_num)
theorem B3709253 : Blo 1464552 3709253 := bbase (se 4 (by rfl) ⟨347742, by rfl⟩ : syracuseStep 3709253 = 695485) (by norm_num)
theorem B3299669 : Blo 1464552 3299669 := bbase (se 10 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 3299669 = 9667) (by norm_num)
theorem B2677093 : Blo 1464552 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1759601 : Blo 1464552 1759601 := bbase (se 2 (by rfl) ⟨659850, by rfl⟩ : syracuseStep 1759601 = 1319701) (by norm_num)
theorem B3340693 : Blo 1464552 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B2472349 : Blo 1464552 2472349 := bbase (se 3 (by rfl) ⟨463565, by rfl⟩ : syracuseStep 2472349 = 927131) (by norm_num)
theorem B3299741 : Blo 1464552 3299741 := bbase (se 3 (by rfl) ⟨618701, by rfl⟩ : syracuseStep 3299741 = 1237403) (by norm_num)
theorem B4692437 : Blo 1464552 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B2783717 : Blo 1464552 2783717 := bbase (se 4 (by rfl) ⟨260973, by rfl⟩ : syracuseStep 2783717 = 521947) (by norm_num)
theorem B2472437 : Blo 1464552 2472437 := bbase (se 5 (by rfl) ⟨115895, by rfl⟩ : syracuseStep 2472437 = 231791) (by norm_num)
theorem B5282293 : Blo 1464552 5282293 := bbase (se 5 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 5282293 = 495215) (by norm_num)
theorem B5011973 : Blo 1464552 5011973 := bbase (se 4 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 5011973 = 939745) (by norm_num)
theorem B4946453 : Blo 1464552 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B15039029 : Blo 1464552 15039029 := bbase (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) (by norm_num)
theorem B5560933 : Blo 1464552 5560933 := bbase (se 4 (by rfl) ⟨521337, by rfl⟩ : syracuseStep 5560933 = 1042675) (by norm_num)
theorem B2472565 : Blo 1464552 2472565 := bbase (se 5 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 2472565 = 231803) (by norm_num)
theorem B3521173 : Blo 1464552 3521173 := bbase (se 6 (by rfl) ⟨82527, by rfl⟩ : syracuseStep 3521173 = 165055) (by norm_num)
theorem B3709597 : Blo 1464552 3709597 := bbase (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) (by norm_num)
theorem B1759909 : Blo 1464552 1759909 := bbase (se 4 (by rfl) ⟨164991, by rfl⟩ : syracuseStep 1759909 = 329983) (by norm_num)
theorem B1759937 : Blo 1464552 1759937 := bbase (se 2 (by rfl) ⟨659976, by rfl⟩ : syracuseStep 1759937 = 1319953) (by norm_num)
theorem B2472653 : Blo 1464552 2472653 := bbase (se 3 (by rfl) ⟨463622, by rfl⟩ : syracuseStep 2472653 = 927245) (by norm_num)
theorem B9386741 : Blo 1464552 9386741 := bbase (se 5 (by rfl) ⟨440003, by rfl⟩ : syracuseStep 9386741 = 880007) (by norm_num)
theorem B3709709 : Blo 1464552 3709709 := bbase (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) (by norm_num)
theorem B2472781 : Blo 1464552 2472781 := bbase (se 3 (by rfl) ⟨463646, by rfl⟩ : syracuseStep 2472781 = 927293) (by norm_num)
theorem B5561237 : Blo 1464552 5561237 := bbase (se 6 (by rfl) ⟨130341, by rfl⟩ : syracuseStep 5561237 = 260683) (by norm_num)
theorem B2472869 : Blo 1464552 2472869 := bbase (se 4 (by rfl) ⟨231831, by rfl⟩ : syracuseStep 2472869 = 463663) (by norm_num)
theorem B11131829 : Blo 1464552 11131829 := bbase (se 5 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 11131829 = 1043609) (by norm_num)
theorem B4946885 : Blo 1464552 4946885 := bbase (se 4 (by rfl) ⟨463770, by rfl⟩ : syracuseStep 4946885 = 927541) (by norm_num)
theorem B3709901 : Blo 1464552 3709901 := bbase (se 3 (by rfl) ⟨695606, by rfl⟩ : syracuseStep 3709901 = 1391213) (by norm_num)
theorem B1694689 : Blo 1464552 1694689 := bbase (se 2 (by rfl) ⟨635508, by rfl⟩ : syracuseStep 1694689 = 1271017) (by norm_num)
theorem B2472997 : Blo 1464552 2472997 := bbase (se 4 (by rfl) ⟨231843, by rfl⟩ : syracuseStep 2472997 = 463687) (by norm_num)
theorem B3570773 : Blo 1464552 3570773 := bbase (se 8 (by rfl) ⟨20922, by rfl⟩ : syracuseStep 3570773 = 41845) (by norm_num)
theorem B2473085 : Blo 1464552 2473085 := bbase (se 3 (by rfl) ⟨463703, by rfl⟩ : syracuseStep 2473085 = 927407) (by norm_num)
theorem B3128453 : Blo 1464552 3128453 := bbase (se 4 (by rfl) ⟨293292, by rfl⟩ : syracuseStep 3128453 = 586585) (by norm_num)
theorem B1760437 : Blo 1464552 1760437 := bbase (se 5 (by rfl) ⟨82520, by rfl⟩ : syracuseStep 1760437 = 165041) (by norm_num)
theorem B3054773 : Blo 1464552 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B2227397 : Blo 1464552 2227397 := bbase (se 4 (by rfl) ⟨208818, by rfl⟩ : syracuseStep 2227397 = 417637) (by norm_num)
theorem B2473213 : Blo 1464552 2473213 := bbase (se 3 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 2473213 = 927455) (by norm_num)
theorem B3521789 : Blo 1464552 3521789 := bbase (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) (by norm_num)
theorem B3710245 : Blo 1464552 3710245 := bbase (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) (by norm_num)
theorem B11124053 : Blo 1464552 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B2473301 : Blo 1464552 2473301 := bbase (se 11 (by rfl) ⟨1811, by rfl⟩ : syracuseStep 2473301 = 3623) (by norm_num)
theorem B5283157 : Blo 1464552 5283157 := bbase (se 11 (by rfl) ⟨3869, by rfl⟩ : syracuseStep 5283157 = 7739) (by norm_num)
theorem B13557077 : Blo 1464552 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B4947317 : Blo 1464552 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B3128701 : Blo 1464552 3128701 := bbase (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) (by norm_num)
theorem B3710357 : Blo 1464552 3710357 := bbase (se 6 (by rfl) ⟨86961, by rfl⟩ : syracuseStep 3710357 = 173923) (by norm_num)
theorem B3521989 : Blo 1464552 3521989 := bbase (se 4 (by rfl) ⟨330186, by rfl⟩ : syracuseStep 3521989 = 660373) (by norm_num)
theorem B7421381 : Blo 1464552 7421381 := bbase (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) (by norm_num)
theorem B2473429 : Blo 1464552 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B1564201 : Blo 1464552 1564201 := bbase (se 2 (by rfl) ⟨586575, by rfl⟩ : syracuseStep 1564201 = 1173151) (by norm_num)
theorem B2473517 : Blo 1464552 2473517 := bbase (se 3 (by rfl) ⟨463784, by rfl⟩ : syracuseStep 2473517 = 927569) (by norm_num)
theorem B18775637 : Blo 1464552 18775637 := bbase (se 8 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 18775637 = 220027) (by norm_num)
theorem B3710549 : Blo 1464552 3710549 := bbase (se 8 (by rfl) ⟨21741, by rfl⟩ : syracuseStep 3710549 = 43483) (by norm_num)
theorem B2473645 : Blo 1464552 2473645 := bbase (se 3 (by rfl) ⟨463808, by rfl⟩ : syracuseStep 2473645 = 927617) (by norm_num)
theorem B2473733 : Blo 1464552 2473733 := bbase (se 4 (by rfl) ⟨231912, by rfl⟩ : syracuseStep 2473733 = 463825) (by norm_num)
theorem B2227981 : Blo 1464552 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B4693781 : Blo 1464552 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B5283605 : Blo 1464552 5283605 := bbase (se 6 (by rfl) ⟨123834, by rfl⟩ : syracuseStep 5283605 = 247669) (by norm_num)
theorem B4947749 : Blo 1464552 4947749 := bbase (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) (by norm_num)
theorem B3129205 : Blo 1464552 3129205 := bbase (se 5 (by rfl) ⟨146681, by rfl⟩ : syracuseStep 3129205 = 293363) (by norm_num)
theorem B2473861 : Blo 1464552 2473861 := bbase (se 4 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 2473861 = 463849) (by norm_num)
theorem B5283733 : Blo 1464552 5283733 := bbase (se 6 (by rfl) ⟨123837, by rfl⟩ : syracuseStep 5283733 = 247675) (by norm_num)
theorem B3710893 : Blo 1464552 3710893 := bbase (se 3 (by rfl) ⟨695792, by rfl⟩ : syracuseStep 3710893 = 1391585) (by norm_num)
theorem B2473949 : Blo 1464552 2473949 := bbase (se 3 (by rfl) ⟨463865, by rfl⟩ : syracuseStep 2473949 = 927731) (by norm_num)
theorem B1564645 : Blo 1464552 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B1466371 : Blo 1464552 1466371 := bstep (se 1 (by rfl) ⟨1099778, by rfl⟩ : syracuseStep 1466371 = 2199557) B2199557
theorem B2474003 : Blo 1464552 2474003 := bstep (se 1 (by rfl) ⟨1855502, by rfl⟩ : syracuseStep 2474003 = 3711005) B3711005
theorem B1466387 : Blo 1464552 1466387 := bstep (se 1 (by rfl) ⟨1099790, by rfl⟩ : syracuseStep 1466387 = 2199581) B2199581
theorem B1466403 : Blo 1464552 1466403 := bstep (se 1 (by rfl) ⟨1099802, by rfl⟩ : syracuseStep 1466403 = 2199605) B2199605
theorem B1466419 : Blo 1464552 1466419 := bstep (se 1 (by rfl) ⟨1099814, by rfl⟩ : syracuseStep 1466419 = 2199629) B2199629
theorem B1466435 : Blo 1464552 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B7422029 : Blo 1464552 7422029 := bstep (se 3 (by rfl) ⟨1391630, by rfl⟩ : syracuseStep 7422029 = 2783261) B2783261
theorem B1466451 : Blo 1464552 1466451 := bstep (se 1 (by rfl) ⟨1099838, by rfl⟩ : syracuseStep 1466451 = 2199677) B2199677
theorem B1466467 : Blo 1464552 1466467 := bstep (se 1 (by rfl) ⟨1099850, by rfl⟩ : syracuseStep 1466467 = 2199701) B2199701
theorem B5283953 : Blo 1464552 5283953 := bstep (se 2 (by rfl) ⟨1981482, by rfl⟩ : syracuseStep 5283953 = 3962965) B3962965
theorem B1466483 : Blo 1464552 1466483 := bstep (se 1 (by rfl) ⟨1099862, by rfl⟩ : syracuseStep 1466483 = 2199725) B2199725
theorem B1466499 : Blo 1464552 1466499 := bstep (se 1 (by rfl) ⟨1099874, by rfl⟩ : syracuseStep 1466499 = 2199749) B2199749
theorem B2474131 : Blo 1464552 2474131 := bstep (se 1 (by rfl) ⟨1855598, by rfl⟩ : syracuseStep 2474131 = 3711197) B3711197
theorem B1466515 : Blo 1464552 1466515 := bstep (se 1 (by rfl) ⟨1099886, by rfl⟩ : syracuseStep 1466515 = 2199773) B2199773
theorem B1466531 : Blo 1464552 1466531 := bstep (se 1 (by rfl) ⟨1099898, by rfl⟩ : syracuseStep 1466531 = 2199797) B2199797
theorem B1466547 : Blo 1464552 1466547 := bstep (se 1 (by rfl) ⟨1099910, by rfl⟩ : syracuseStep 1466547 = 2199821) B2199821
theorem B1564867 : Blo 1464552 1564867 := bstep (se 1 (by rfl) ⟨1173650, by rfl⟩ : syracuseStep 1564867 = 2347301) B2347301
theorem B1761475 : Blo 1464552 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B3711217 : Blo 1464552 3711217 := bstep (se 2 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 3711217 = 2783413) B2783413
theorem B2474273 : Blo 1464552 2474273 := bstep (se 2 (by rfl) ⟨927852, by rfl⟩ : syracuseStep 2474273 = 1855705) B1855705
theorem B4456739 : Blo 1464552 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B3522865 : Blo 1464552 3522865 := bstep (se 2 (by rfl) ⟨1321074, by rfl⟩ : syracuseStep 3522865 = 2642149) B2642149
theorem B2474401 : Blo 1464552 2474401 := bstep (se 2 (by rfl) ⟨927900, by rfl⟩ : syracuseStep 2474401 = 1855801) B1855801
theorem B4948397 : Blo 1464552 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B2474435 : Blo 1464552 2474435 := bstep (se 1 (by rfl) ⟨1855826, by rfl⟩ : syracuseStep 2474435 = 3711653) B3711653
theorem B4948451 : Blo 1464552 4948451 := bstep (se 1 (by rfl) ⟨3711338, by rfl⟩ : syracuseStep 4948451 = 7422677) B7422677
theorem B3711491 : Blo 1464552 3711491 := bstep (se 1 (by rfl) ⟨2783618, by rfl⟩ : syracuseStep 3711491 = 5567237) B5567237
theorem B5939725 : Blo 1464552 5939725 := bstep (se 3 (by rfl) ⟨1113698, by rfl⟩ : syracuseStep 5939725 = 2227397) B2227397
theorem B2474563 : Blo 1464552 2474563 := bstep (se 1 (by rfl) ⟨1855922, by rfl⟩ : syracuseStep 2474563 = 3711845) B3711845
theorem B3711683 : Blo 1464552 3711683 := bstep (se 1 (by rfl) ⟨2783762, by rfl⟩ : syracuseStep 3711683 = 5567525) B5567525
theorem B2474705 : Blo 1464552 2474705 := bstep (se 2 (by rfl) ⟨928014, by rfl⟩ : syracuseStep 2474705 = 1856029) B1856029
theorem B4694755 : Blo 1464552 4694755 := bstep (se 1 (by rfl) ⟨3521066, by rfl⟩ : syracuseStep 4694755 = 7042133) B7042133
theorem B4948721 : Blo 1464552 4948721 := bstep (se 2 (by rfl) ⟨1855770, by rfl⟩ : syracuseStep 4948721 = 3711541) B3711541
theorem B7414577 : Blo 1464552 7414577 := bstep (se 2 (by rfl) ⟨2780466, by rfl⟩ : syracuseStep 7414577 = 5560933) B5560933
theorem B4694897 : Blo 1464552 4694897 := bstep (se 2 (by rfl) ⟨1760586, by rfl⟩ : syracuseStep 4694897 = 3521173) B3521173
theorem B9388997 : Blo 1464552 9388997 := bstep (se 4 (by rfl) ⟨880218, by rfl⟩ : syracuseStep 9388997 = 1760437) B1760437
theorem B5563363 : Blo 1464552 5563363 := bstep (se 1 (by rfl) ⟨4172522, by rfl⟩ : syracuseStep 5563363 = 8345045) B8345045
theorem B4695011 : Blo 1464552 4695011 := bstep (se 1 (by rfl) ⟨3521258, by rfl⟩ : syracuseStep 4695011 = 7042517) B7042517
theorem B3130417 : Blo 1464552 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B2229331 : Blo 1464552 2229331 := bstep (se 1 (by rfl) ⟨1671998, by rfl⟩ : syracuseStep 2229331 = 3343997) B3343997
theorem B1647715 : Blo 1464552 1647715 := bstep (se 1 (by rfl) ⟨1235786, by rfl⟩ : syracuseStep 1647715 = 2471573) B2471573
theorem B1565875 : Blo 1464552 1565875 := bstep (se 1 (by rfl) ⟨1174406, by rfl⟩ : syracuseStep 1565875 = 2348813) B2348813
theorem B2819281 : Blo 1464552 2819281 := bstep (se 2 (by rfl) ⟨1057230, by rfl⟩ : syracuseStep 2819281 = 2114461) B2114461
theorem B7628017 : Blo 1464552 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B1647859 : Blo 1464552 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B4949261 : Blo 1464552 4949261 := bstep (se 3 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 4949261 = 1855973) B1855973
theorem B4949315 : Blo 1464552 4949315 := bstep (se 1 (by rfl) ⟨3711986, by rfl⟩ : syracuseStep 4949315 = 7423973) B7423973
theorem B2639185 : Blo 1464552 2639185 := bstep (se 2 (by rfl) ⟨989694, by rfl⟩ : syracuseStep 2639185 = 1979389) B1979389
theorem B2196833 : Blo 1464552 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B2196851 : Blo 1464552 2196851 := bstep (se 1 (by rfl) ⟨1647638, by rfl⟩ : syracuseStep 2196851 = 3295277) B3295277
theorem B1648003 : Blo 1464552 1648003 := bstep (se 1 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 1648003 = 2472005) B2472005
theorem B2196881 : Blo 1464552 2196881 := bstep (se 2 (by rfl) ⟨823830, by rfl⟩ : syracuseStep 2196881 = 1647661) B1647661
theorem B2196899 : Blo 1464552 2196899 := bstep (se 1 (by rfl) ⟨1647674, by rfl⟩ : syracuseStep 2196899 = 3295349) B3295349
theorem B2196929 : Blo 1464552 2196929 := bstep (se 2 (by rfl) ⟨823848, by rfl⟩ : syracuseStep 2196929 = 1647697) B1647697
theorem B10028485 : Blo 1464552 10028485 := bstep (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) B1880341
theorem B2196947 : Blo 1464552 2196947 := bstep (se 1 (by rfl) ⟨1647710, by rfl⟩ : syracuseStep 2196947 = 3295421) B3295421
theorem B2196977 : Blo 1464552 2196977 := bstep (se 2 (by rfl) ⟨823866, by rfl⟩ : syracuseStep 2196977 = 1647733) B1647733
theorem B2196995 : Blo 1464552 2196995 := bstep (se 1 (by rfl) ⟨1647746, by rfl⟩ : syracuseStep 2196995 = 3295493) B3295493
theorem B7046669 : Blo 1464552 7046669 := bstep (se 3 (by rfl) ⟨1321250, by rfl⟩ : syracuseStep 7046669 = 2642501) B2642501
theorem B1648147 : Blo 1464552 1648147 := bstep (se 1 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 1648147 = 2472221) B2472221
theorem B2197025 : Blo 1464552 2197025 := bstep (se 2 (by rfl) ⟨823884, by rfl⟩ : syracuseStep 2197025 = 1647769) B1647769
theorem B6260273 : Blo 1464552 6260273 := bstep (se 2 (by rfl) ⟨2347602, by rfl⟩ : syracuseStep 6260273 = 4695205) B4695205
theorem B2197043 : Blo 1464552 2197043 := bstep (se 1 (by rfl) ⟨1647782, by rfl⟩ : syracuseStep 2197043 = 3295565) B3295565
theorem B2197073 : Blo 1464552 2197073 := bstep (se 2 (by rfl) ⟨823902, by rfl⟩ : syracuseStep 2197073 = 1647805) B1647805
theorem B4949585 : Blo 1464552 4949585 := bstep (se 2 (by rfl) ⟨1856094, by rfl⟩ : syracuseStep 4949585 = 3712189) B3712189
theorem B2197091 : Blo 1464552 2197091 := bstep (se 1 (by rfl) ⟨1647818, by rfl⟩ : syracuseStep 2197091 = 3295637) B3295637
theorem B2197121 : Blo 1464552 2197121 := bstep (se 2 (by rfl) ⟨823920, by rfl⟩ : syracuseStep 2197121 = 1647841) B1647841
theorem B2197139 : Blo 1464552 2197139 := bstep (se 1 (by rfl) ⟨1647854, by rfl⟩ : syracuseStep 2197139 = 3295709) B3295709
theorem B1648291 : Blo 1464552 1648291 := bstep (se 1 (by rfl) ⟨1236218, by rfl⟩ : syracuseStep 1648291 = 2472437) B2472437
theorem B2197169 : Blo 1464552 2197169 := bstep (se 2 (by rfl) ⟨823938, by rfl⟩ : syracuseStep 2197169 = 1647877) B1647877
theorem B2197187 : Blo 1464552 2197187 := bstep (se 1 (by rfl) ⟨1647890, by rfl⟩ : syracuseStep 2197187 = 3295781) B3295781
theorem B2197217 : Blo 1464552 2197217 := bstep (se 2 (by rfl) ⟨823956, by rfl⟩ : syracuseStep 2197217 = 1647913) B1647913
theorem B2197235 : Blo 1464552 2197235 := bstep (se 1 (by rfl) ⟨1647926, by rfl⟩ : syracuseStep 2197235 = 3295853) B3295853
theorem B2197265 : Blo 1464552 2197265 := bstep (se 2 (by rfl) ⟨823974, by rfl⟩ : syracuseStep 2197265 = 1647949) B1647949
theorem B2197283 : Blo 1464552 2197283 := bstep (se 1 (by rfl) ⟨1647962, by rfl⟩ : syracuseStep 2197283 = 3295925) B3295925
theorem B2819875 : Blo 1464552 2819875 := bstep (se 1 (by rfl) ⟨2114906, by rfl⟩ : syracuseStep 2819875 = 4229813) B4229813
theorem B1648435 : Blo 1464552 1648435 := bstep (se 1 (by rfl) ⟨1236326, by rfl⟩ : syracuseStep 1648435 = 2472653) B2472653
theorem B2197313 : Blo 1464552 2197313 := bstep (se 2 (by rfl) ⟨823992, by rfl⟩ : syracuseStep 2197313 = 1647985) B1647985
theorem B4171601 : Blo 1464552 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B2197331 : Blo 1464552 2197331 := bstep (se 1 (by rfl) ⟨1647998, by rfl⟩ : syracuseStep 2197331 = 3295997) B3295997
theorem B2197361 : Blo 1464552 2197361 := bstep (se 2 (by rfl) ⟨824010, by rfl⟩ : syracuseStep 2197361 = 1648021) B1648021
theorem B2197379 : Blo 1464552 2197379 := bstep (se 1 (by rfl) ⟨1648034, by rfl⟩ : syracuseStep 2197379 = 3296069) B3296069
theorem B2197409 : Blo 1464552 2197409 := bstep (se 2 (by rfl) ⟨824028, by rfl⟩ : syracuseStep 2197409 = 1648057) B1648057
theorem B2197427 : Blo 1464552 2197427 := bstep (se 1 (by rfl) ⟨1648070, by rfl⟩ : syracuseStep 2197427 = 3296141) B3296141
theorem B4695985 : Blo 1464552 4695985 := bstep (se 2 (by rfl) ⟨1760994, by rfl⟩ : syracuseStep 4695985 = 3521989) B3521989
theorem B1648579 : Blo 1464552 1648579 := bstep (se 1 (by rfl) ⟨1236434, by rfl⟩ : syracuseStep 1648579 = 2472869) B2472869
theorem B2197457 : Blo 1464552 2197457 := bstep (se 2 (by rfl) ⟨824046, by rfl⟩ : syracuseStep 2197457 = 1648093) B1648093
theorem B2197475 : Blo 1464552 2197475 := bstep (se 1 (by rfl) ⟨1648106, by rfl⟩ : syracuseStep 2197475 = 3296213) B3296213
theorem B2197505 : Blo 1464552 2197505 := bstep (se 2 (by rfl) ⟨824064, by rfl⟩ : syracuseStep 2197505 = 1648129) B1648129
theorem B2197523 : Blo 1464552 2197523 := bstep (se 1 (by rfl) ⟨1648142, by rfl⟩ : syracuseStep 2197523 = 3296285) B3296285
theorem B2197553 : Blo 1464552 2197553 := bstep (se 2 (by rfl) ⟨824082, by rfl⟩ : syracuseStep 2197553 = 1648165) B1648165
theorem B2197571 : Blo 1464552 2197571 := bstep (se 1 (by rfl) ⟨1648178, by rfl⟩ : syracuseStep 2197571 = 3296357) B3296357
theorem B3295313 : Blo 1464552 3295313 := bstep (se 2 (by rfl) ⟨1235742, by rfl⟩ : syracuseStep 3295313 = 2471485) B2471485
theorem B1648723 : Blo 1464552 1648723 := bstep (se 1 (by rfl) ⟨1236542, by rfl⟩ : syracuseStep 1648723 = 2473085) B2473085
theorem B2197601 : Blo 1464552 2197601 := bstep (se 2 (by rfl) ⟨824100, by rfl⟩ : syracuseStep 2197601 = 1648201) B1648201
theorem B3295331 : Blo 1464552 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2197619 : Blo 1464552 2197619 := bstep (se 1 (by rfl) ⟨1648214, by rfl⟩ : syracuseStep 2197619 = 3296429) B3296429
theorem B2197649 : Blo 1464552 2197649 := bstep (se 2 (by rfl) ⟨824118, by rfl⟩ : syracuseStep 2197649 = 1648237) B1648237
theorem B2197667 : Blo 1464552 2197667 := bstep (se 1 (by rfl) ⟨1648250, by rfl⟩ : syracuseStep 2197667 = 3296501) B3296501
theorem B2197697 : Blo 1464552 2197697 := bstep (se 2 (by rfl) ⟨824136, by rfl⟩ : syracuseStep 2197697 = 1648273) B1648273
theorem B2197715 : Blo 1464552 2197715 := bstep (se 1 (by rfl) ⟨1648286, by rfl⟩ : syracuseStep 2197715 = 3296573) B3296573
theorem B7416035 : Blo 1464552 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B1648867 : Blo 1464552 1648867 := bstep (se 1 (by rfl) ⟨1236650, by rfl⟩ : syracuseStep 1648867 = 2473301) B2473301
theorem B9038051 : Blo 1464552 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B2197745 : Blo 1464552 2197745 := bstep (se 2 (by rfl) ⟨824154, by rfl⟩ : syracuseStep 2197745 = 1648309) B1648309
theorem B2640131 : Blo 1464552 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B2197763 : Blo 1464552 2197763 := bstep (se 1 (by rfl) ⟨1648322, by rfl⟩ : syracuseStep 2197763 = 3296645) B3296645
theorem B2197793 : Blo 1464552 2197793 := bstep (se 2 (by rfl) ⟨824172, by rfl⟩ : syracuseStep 2197793 = 1648345) B1648345
theorem B2197811 : Blo 1464552 2197811 := bstep (se 1 (by rfl) ⟨1648358, by rfl⟩ : syracuseStep 2197811 = 3296717) B3296717
theorem B2197841 : Blo 1464552 2197841 := bstep (se 2 (by rfl) ⟨824190, by rfl⟩ : syracuseStep 2197841 = 1648381) B1648381
theorem B4458833 : Blo 1464552 4458833 := bstep (se 2 (by rfl) ⟨1672062, by rfl⟩ : syracuseStep 4458833 = 3344125) B3344125
theorem B2197859 : Blo 1464552 2197859 := bstep (se 1 (by rfl) ⟨1648394, by rfl⟩ : syracuseStep 2197859 = 3296789) B3296789
theorem B3295601 : Blo 1464552 3295601 := bstep (se 2 (by rfl) ⟨1235850, by rfl⟩ : syracuseStep 3295601 = 2471701) B2471701
theorem B1649011 : Blo 1464552 1649011 := bstep (se 1 (by rfl) ⟨1236758, by rfl⟩ : syracuseStep 1649011 = 2473517) B2473517
theorem B2197889 : Blo 1464552 2197889 := bstep (se 2 (by rfl) ⟨824208, by rfl⟩ : syracuseStep 2197889 = 1648417) B1648417
theorem B3295619 : Blo 1464552 3295619 := bstep (se 1 (by rfl) ⟨2471714, by rfl⟩ : syracuseStep 3295619 = 4943429) B4943429
theorem B2197907 : Blo 1464552 2197907 := bstep (se 1 (by rfl) ⟨1648430, by rfl⟩ : syracuseStep 2197907 = 3296861) B3296861
theorem B2197937 : Blo 1464552 2197937 := bstep (se 2 (by rfl) ⟨824226, by rfl⟩ : syracuseStep 2197937 = 1648453) B1648453
theorem B2197955 : Blo 1464552 2197955 := bstep (se 1 (by rfl) ⟨1648466, by rfl⟩ : syracuseStep 2197955 = 3296933) B3296933
theorem B2197985 : Blo 1464552 2197985 := bstep (se 2 (by rfl) ⟨824244, by rfl⟩ : syracuseStep 2197985 = 1648489) B1648489
theorem B1853923 : Blo 1464552 1853923 := bstep (se 1 (by rfl) ⟨1390442, by rfl⟩ : syracuseStep 1853923 = 2780885) B2780885
theorem B4172273 : Blo 1464552 4172273 := bstep (se 2 (by rfl) ⟨1564602, by rfl⟩ : syracuseStep 4172273 = 3129205) B3129205
theorem B2198003 : Blo 1464552 2198003 := bstep (se 1 (by rfl) ⟨1648502, by rfl⟩ : syracuseStep 2198003 = 3297005) B3297005
theorem B1649155 : Blo 1464552 1649155 := bstep (se 1 (by rfl) ⟨1236866, by rfl⟩ : syracuseStep 1649155 = 2473733) B2473733
theorem B9038341 : Blo 1464552 9038341 := bstep (se 4 (by rfl) ⟨847344, by rfl⟩ : syracuseStep 9038341 = 1694689) B1694689
theorem B2198033 : Blo 1464552 2198033 := bstep (se 2 (by rfl) ⟨824262, by rfl⟩ : syracuseStep 2198033 = 1648525) B1648525
theorem B3131921 : Blo 1464552 3131921 := bstep (se 2 (by rfl) ⟨1174470, by rfl⟩ : syracuseStep 3131921 = 2348941) B2348941
theorem B2198051 : Blo 1464552 2198051 := bstep (se 1 (by rfl) ⟨1648538, by rfl⟩ : syracuseStep 2198051 = 3297077) B3297077
theorem B3131939 : Blo 1464552 3131939 := bstep (se 1 (by rfl) ⟨2348954, by rfl⟩ : syracuseStep 3131939 = 4697909) B4697909
theorem B2198081 : Blo 1464552 2198081 := bstep (se 2 (by rfl) ⟨824280, by rfl⟩ : syracuseStep 2198081 = 1648561) B1648561
theorem B1854019 : Blo 1464552 1854019 := bstep (se 1 (by rfl) ⟨1390514, by rfl⟩ : syracuseStep 1854019 = 2781029) B2781029
theorem B2198099 : Blo 1464552 2198099 := bstep (se 1 (by rfl) ⟨1648574, by rfl⟩ : syracuseStep 2198099 = 3297149) B3297149
theorem B8342129 : Blo 1464552 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B2198129 : Blo 1464552 2198129 := bstep (se 2 (by rfl) ⟨824298, by rfl⟩ : syracuseStep 2198129 = 1648597) B1648597
theorem B2198147 : Blo 1464552 2198147 := bstep (se 1 (by rfl) ⟨1648610, by rfl⟩ : syracuseStep 2198147 = 3297221) B3297221
theorem B3295889 : Blo 1464552 3295889 := bstep (se 2 (by rfl) ⟨1235958, by rfl⟩ : syracuseStep 3295889 = 2471917) B2471917
theorem B1649299 : Blo 1464552 1649299 := bstep (se 1 (by rfl) ⟨1236974, by rfl⟩ : syracuseStep 1649299 = 2473949) B2473949
theorem B2198177 : Blo 1464552 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B3295907 : Blo 1464552 3295907 := bstep (se 1 (by rfl) ⟨2471930, by rfl⟩ : syracuseStep 3295907 = 4943861) B4943861
theorem B2198195 : Blo 1464552 2198195 := bstep (se 1 (by rfl) ⟨1648646, by rfl⟩ : syracuseStep 2198195 = 3297293) B3297293
theorem B2640593 : Blo 1464552 2640593 := bstep (se 2 (by rfl) ⟨990222, by rfl⟩ : syracuseStep 2640593 = 1980445) B1980445
theorem B2198225 : Blo 1464552 2198225 := bstep (se 2 (by rfl) ⟨824334, by rfl⟩ : syracuseStep 2198225 = 1648669) B1648669
theorem B2198243 : Blo 1464552 2198243 := bstep (se 1 (by rfl) ⟨1648682, by rfl⟩ : syracuseStep 2198243 = 3297365) B3297365
theorem B2198273 : Blo 1464552 2198273 := bstep (se 2 (by rfl) ⟨824352, by rfl⟩ : syracuseStep 2198273 = 1648705) B1648705
theorem B2198291 : Blo 1464552 2198291 := bstep (se 1 (by rfl) ⟨1648718, by rfl⟩ : syracuseStep 2198291 = 3297437) B3297437
theorem B1649443 : Blo 1464552 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B2198321 : Blo 1464552 2198321 := bstep (se 2 (by rfl) ⟨824370, by rfl⟩ : syracuseStep 2198321 = 1648741) B1648741
theorem B2198339 : Blo 1464552 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B12512069 : Blo 1464552 12512069 := bstep (se 4 (by rfl) ⟨1173006, by rfl⟩ : syracuseStep 12512069 = 2346013) B2346013
theorem B2198369 : Blo 1464552 2198369 := bstep (se 2 (by rfl) ⟨824388, by rfl⟩ : syracuseStep 2198369 = 1648777) B1648777
theorem B2198387 : Blo 1464552 2198387 := bstep (se 1 (by rfl) ⟨1648790, by rfl⟩ : syracuseStep 2198387 = 3297581) B3297581
theorem B7039885 : Blo 1464552 7039885 := bstep (se 3 (by rfl) ⟨1319978, by rfl⟩ : syracuseStep 7039885 = 2639957) B2639957
theorem B2198417 : Blo 1464552 2198417 := bstep (se 2 (by rfl) ⟨824406, by rfl⟩ : syracuseStep 2198417 = 1648813) B1648813
theorem B2198435 : Blo 1464552 2198435 := bstep (se 1 (by rfl) ⟨1648826, by rfl⟩ : syracuseStep 2198435 = 3297653) B3297653
theorem B3296177 : Blo 1464552 3296177 := bstep (se 2 (by rfl) ⟨1236066, by rfl⟩ : syracuseStep 3296177 = 2472133) B2472133
theorem B1649587 : Blo 1464552 1649587 := bstep (se 1 (by rfl) ⟨1237190, by rfl⟩ : syracuseStep 1649587 = 2474381) B2474381
theorem B2198465 : Blo 1464552 2198465 := bstep (se 2 (by rfl) ⟨824424, by rfl⟩ : syracuseStep 2198465 = 1648849) B1648849
theorem B3296195 : Blo 1464552 3296195 := bstep (se 1 (by rfl) ⟨2472146, by rfl⟩ : syracuseStep 3296195 = 4944293) B4944293
theorem B2411473 : Blo 1464552 2411473 := bstep (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) B1808605
theorem B2198483 : Blo 1464552 2198483 := bstep (se 1 (by rfl) ⟨1648862, by rfl⟩ : syracuseStep 2198483 = 3297725) B3297725
theorem B5352419 : Blo 1464552 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B2198513 : Blo 1464552 2198513 := bstep (se 2 (by rfl) ⟨824442, by rfl⟩ : syracuseStep 2198513 = 1648885) B1648885
theorem B2198531 : Blo 1464552 2198531 := bstep (se 1 (by rfl) ⟨1648898, by rfl⟩ : syracuseStep 2198531 = 3297797) B3297797
theorem B7416845 : Blo 1464552 7416845 := bstep (se 3 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 7416845 = 2781317) B2781317
theorem B2198561 : Blo 1464552 2198561 := bstep (se 2 (by rfl) ⟨824460, by rfl⟩ : syracuseStep 2198561 = 1648921) B1648921
theorem B5016611 : Blo 1464552 5016611 := bstep (se 1 (by rfl) ⟨3762458, by rfl⟩ : syracuseStep 5016611 = 7524917) B7524917
theorem B1854515 : Blo 1464552 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B2198579 : Blo 1464552 2198579 := bstep (se 1 (by rfl) ⟨1648934, by rfl⟩ : syracuseStep 2198579 = 3297869) B3297869
theorem B1649731 : Blo 1464552 1649731 := bstep (se 1 (by rfl) ⟨1237298, by rfl⟩ : syracuseStep 1649731 = 2474597) B2474597
theorem B2198609 : Blo 1464552 2198609 := bstep (se 2 (by rfl) ⟨824478, by rfl⟩ : syracuseStep 2198609 = 1648957) B1648957
theorem B2198627 : Blo 1464552 2198627 := bstep (se 1 (by rfl) ⟨1648970, by rfl⟩ : syracuseStep 2198627 = 3297941) B3297941
theorem B2198657 : Blo 1464552 2198657 := bstep (se 2 (by rfl) ⟨824496, by rfl⟩ : syracuseStep 2198657 = 1648993) B1648993
theorem B5565581 : Blo 1464552 5565581 := bstep (se 3 (by rfl) ⟨1043546, by rfl⟩ : syracuseStep 5565581 = 2087093) B2087093
theorem B8146061 : Blo 1464552 8146061 := bstep (se 3 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 8146061 = 3054773) B3054773
theorem B2198675 : Blo 1464552 2198675 := bstep (se 1 (by rfl) ⟨1649006, by rfl⟩ : syracuseStep 2198675 = 3298013) B3298013
theorem B2198705 : Blo 1464552 2198705 := bstep (se 2 (by rfl) ⟨824514, by rfl⟩ : syracuseStep 2198705 = 1649029) B1649029
theorem B2198723 : Blo 1464552 2198723 := bstep (se 1 (by rfl) ⟨1649042, by rfl⟩ : syracuseStep 2198723 = 3298085) B3298085
theorem B3296465 : Blo 1464552 3296465 := bstep (se 2 (by rfl) ⟨1236174, by rfl⟩ : syracuseStep 3296465 = 2472349) B2472349
theorem B2198753 : Blo 1464552 2198753 := bstep (se 2 (by rfl) ⟨824532, by rfl⟩ : syracuseStep 2198753 = 1649065) B1649065
theorem B3296483 : Blo 1464552 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B2198771 : Blo 1464552 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B4173059 : Blo 1464552 4173059 := bstep (se 1 (by rfl) ⟨3129794, by rfl⟩ : syracuseStep 4173059 = 6259589) B6259589
theorem B2198801 : Blo 1464552 2198801 := bstep (se 2 (by rfl) ⟨824550, by rfl⟩ : syracuseStep 2198801 = 1649101) B1649101
theorem B2198819 : Blo 1464552 2198819 := bstep (se 1 (by rfl) ⟨1649114, by rfl⟩ : syracuseStep 2198819 = 3298229) B3298229
theorem B2198849 : Blo 1464552 2198849 := bstep (se 2 (by rfl) ⟨824568, by rfl⟩ : syracuseStep 2198849 = 1649137) B1649137
theorem B2780497 : Blo 1464552 2780497 := bstep (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) B2085373
theorem B2198867 : Blo 1464552 2198867 := bstep (se 1 (by rfl) ⟨1649150, by rfl⟩ : syracuseStep 2198867 = 3298301) B3298301
theorem B4943213 : Blo 1464552 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B12520817 : Blo 1464552 12520817 := bstep (se 2 (by rfl) ⟨4695306, by rfl⟩ : syracuseStep 12520817 = 9390613) B9390613
theorem B2198897 : Blo 1464552 2198897 := bstep (se 2 (by rfl) ⟨824586, by rfl⟩ : syracuseStep 2198897 = 1649173) B1649173
theorem B2198915 : Blo 1464552 2198915 := bstep (se 1 (by rfl) ⟨1649186, by rfl⟩ : syracuseStep 2198915 = 3298373) B3298373
theorem B2198945 : Blo 1464552 2198945 := bstep (se 2 (by rfl) ⟨824604, by rfl⟩ : syracuseStep 2198945 = 1649209) B1649209
theorem B4943267 : Blo 1464552 4943267 := bstep (se 1 (by rfl) ⟨3707450, by rfl⟩ : syracuseStep 4943267 = 7414901) B7414901
theorem B2198963 : Blo 1464552 2198963 := bstep (se 1 (by rfl) ⟨1649222, by rfl⟩ : syracuseStep 2198963 = 3298445) B3298445
theorem B2198993 : Blo 1464552 2198993 := bstep (se 2 (by rfl) ⟨824622, by rfl⟩ : syracuseStep 2198993 = 1649245) B1649245
theorem B18075107 : Blo 1464552 18075107 := bstep (se 1 (by rfl) ⟨13556330, by rfl⟩ : syracuseStep 18075107 = 27112661) B27112661
theorem B2199011 : Blo 1464552 2199011 := bstep (se 1 (by rfl) ⟨1649258, by rfl⟩ : syracuseStep 2199011 = 3298517) B3298517
theorem B3296753 : Blo 1464552 3296753 := bstep (se 2 (by rfl) ⟨1236282, by rfl⟩ : syracuseStep 3296753 = 2472565) B2472565
theorem B18779633 : Blo 1464552 18779633 := bstep (se 2 (by rfl) ⟨7042362, by rfl⟩ : syracuseStep 18779633 = 14084725) B14084725
theorem B2199041 : Blo 1464552 2199041 := bstep (se 2 (by rfl) ⟨824640, by rfl⟩ : syracuseStep 2199041 = 1649281) B1649281
theorem B3296771 : Blo 1464552 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B2199059 : Blo 1464552 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B2346545 : Blo 1464552 2346545 := bstep (se 2 (by rfl) ⟨879954, by rfl⟩ : syracuseStep 2346545 = 1759909) B1759909
theorem B2199089 : Blo 1464552 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B38088245 : Blo 1464552 38088245 := bstep (se 5 (by rfl) ⟨1785386, by rfl⟩ : syracuseStep 38088245 = 3570773) B3570773
theorem B2199107 : Blo 1464552 2199107 := bstep (se 1 (by rfl) ⟨1649330, by rfl⟩ : syracuseStep 2199107 = 3298661) B3298661
theorem B12693061 : Blo 1464552 12693061 := bstep (se 4 (by rfl) ⟨1189974, by rfl⟩ : syracuseStep 12693061 = 2379949) B2379949
theorem B4173389 : Blo 1464552 4173389 := bstep (se 3 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 4173389 = 1565021) B1565021
theorem B2199137 : Blo 1464552 2199137 := bstep (se 2 (by rfl) ⟨824676, by rfl⟩ : syracuseStep 2199137 = 1649353) B1649353
theorem B2199155 : Blo 1464552 2199155 := bstep (se 1 (by rfl) ⟨1649366, by rfl⟩ : syracuseStep 2199155 = 3298733) B3298733
theorem B4173457 : Blo 1464552 4173457 := bstep (se 2 (by rfl) ⟨1565046, by rfl⟩ : syracuseStep 4173457 = 3130093) B3130093
theorem B2199185 : Blo 1464552 2199185 := bstep (se 2 (by rfl) ⟨824694, by rfl⟩ : syracuseStep 2199185 = 1649389) B1649389
theorem B2199203 : Blo 1464552 2199203 := bstep (se 1 (by rfl) ⟨1649402, by rfl⟩ : syracuseStep 2199203 = 3298805) B3298805
theorem B4943537 : Blo 1464552 4943537 := bstep (se 2 (by rfl) ⟨1853826, by rfl⟩ : syracuseStep 4943537 = 3707653) B3707653
theorem B2199233 : Blo 1464552 2199233 := bstep (se 2 (by rfl) ⟨824712, by rfl⟩ : syracuseStep 2199233 = 1649425) B1649425
theorem B2199251 : Blo 1464552 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B10563313 : Blo 1464552 10563313 := bstep (se 2 (by rfl) ⟨3961242, by rfl⟩ : syracuseStep 10563313 = 7922485) B7922485
theorem B2199281 : Blo 1464552 2199281 := bstep (se 2 (by rfl) ⟨824730, by rfl⟩ : syracuseStep 2199281 = 1649461) B1649461
theorem B1855219 : Blo 1464552 1855219 := bstep (se 1 (by rfl) ⟨1391414, by rfl⟩ : syracuseStep 1855219 = 2782829) B2782829
theorem B2199299 : Blo 1464552 2199299 := bstep (se 1 (by rfl) ⟨1649474, by rfl⟩ : syracuseStep 2199299 = 3298949) B3298949
theorem B3297041 : Blo 1464552 3297041 := bstep (se 2 (by rfl) ⟨1236390, by rfl⟩ : syracuseStep 3297041 = 2472781) B2472781
theorem B2199329 : Blo 1464552 2199329 := bstep (se 2 (by rfl) ⟨824748, by rfl⟩ : syracuseStep 2199329 = 1649497) B1649497
theorem B3297059 : Blo 1464552 3297059 := bstep (se 1 (by rfl) ⟨2472794, by rfl⟩ : syracuseStep 3297059 = 4945589) B4945589
theorem B2199347 : Blo 1464552 2199347 := bstep (se 1 (by rfl) ⟨1649510, by rfl⟩ : syracuseStep 2199347 = 3299021) B3299021
theorem B15249221 : Blo 1464552 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2199377 : Blo 1464552 2199377 := bstep (se 2 (by rfl) ⟨824766, by rfl⟩ : syracuseStep 2199377 = 1649533) B1649533
theorem B1855315 : Blo 1464552 1855315 := bstep (se 1 (by rfl) ⟨1391486, by rfl⟩ : syracuseStep 1855315 = 2782973) B2782973
theorem B2199395 : Blo 1464552 2199395 := bstep (se 1 (by rfl) ⟨1649546, by rfl⟩ : syracuseStep 2199395 = 3299093) B3299093
theorem B2199425 : Blo 1464552 2199425 := bstep (se 2 (by rfl) ⟨824784, by rfl⟩ : syracuseStep 2199425 = 1649569) B1649569
theorem B2199443 : Blo 1464552 2199443 := bstep (se 1 (by rfl) ⟨1649582, by rfl⟩ : syracuseStep 2199443 = 3299165) B3299165
theorem B4173731 : Blo 1464552 4173731 := bstep (se 1 (by rfl) ⟨3130298, by rfl⟩ : syracuseStep 4173731 = 6260597) B6260597
theorem B2199473 : Blo 1464552 2199473 := bstep (se 2 (by rfl) ⟨824802, by rfl⟩ : syracuseStep 2199473 = 1649605) B1649605
theorem B2199491 : Blo 1464552 2199491 := bstep (se 1 (by rfl) ⟨1649618, by rfl⟩ : syracuseStep 2199491 = 3299237) B3299237
theorem B2199521 : Blo 1464552 2199521 := bstep (se 2 (by rfl) ⟨824820, by rfl⟩ : syracuseStep 2199521 = 1649641) B1649641
theorem B15044579 : Blo 1464552 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B2199539 : Blo 1464552 2199539 := bstep (se 1 (by rfl) ⟨1649654, by rfl⟩ : syracuseStep 2199539 = 3299309) B3299309
theorem B2969603 : Blo 1464552 2969603 := bstep (se 1 (by rfl) ⟨2227202, by rfl⟩ : syracuseStep 2969603 = 4454405) B4454405
theorem B2199569 : Blo 1464552 2199569 := bstep (se 2 (by rfl) ⟨824838, by rfl⟩ : syracuseStep 2199569 = 1649677) B1649677
theorem B8343587 : Blo 1464552 8343587 := bstep (se 1 (by rfl) ⟨6257690, by rfl⟩ : syracuseStep 8343587 = 12515381) B12515381
theorem B2199587 : Blo 1464552 2199587 := bstep (se 1 (by rfl) ⟨1649690, by rfl⟩ : syracuseStep 2199587 = 3299381) B3299381
theorem B3297329 : Blo 1464552 3297329 := bstep (se 2 (by rfl) ⟨1236498, by rfl⟩ : syracuseStep 3297329 = 2472997) B2472997
theorem B2199617 : Blo 1464552 2199617 := bstep (se 2 (by rfl) ⟨824856, by rfl⟩ : syracuseStep 2199617 = 1649713) B1649713
theorem B3297347 : Blo 1464552 3297347 := bstep (se 1 (by rfl) ⟨2473010, by rfl⟩ : syracuseStep 3297347 = 4946021) B4946021
theorem B2199635 : Blo 1464552 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B12693617 : Blo 1464552 12693617 := bstep (se 2 (by rfl) ⟨4760106, by rfl⟩ : syracuseStep 12693617 = 9520213) B9520213
theorem B2199665 : Blo 1464552 2199665 := bstep (se 2 (by rfl) ⟨824874, by rfl⟩ : syracuseStep 2199665 = 1649749) B1649749
theorem B2199683 : Blo 1464552 2199683 := bstep (se 1 (by rfl) ⟨1649762, by rfl⟩ : syracuseStep 2199683 = 3299525) B3299525
theorem B2199713 : Blo 1464552 2199713 := bstep (se 2 (by rfl) ⟨824892, by rfl⟩ : syracuseStep 2199713 = 1649785) B1649785
theorem B2199731 : Blo 1464552 2199731 := bstep (se 1 (by rfl) ⟨1649798, by rfl⟩ : syracuseStep 2199731 = 3299597) B3299597
theorem B4944077 : Blo 1464552 4944077 := bstep (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) B1854029
theorem B2199761 : Blo 1464552 2199761 := bstep (se 2 (by rfl) ⟨824910, by rfl⟩ : syracuseStep 2199761 = 1649821) B1649821
theorem B2199779 : Blo 1464552 2199779 := bstep (se 1 (by rfl) ⟨1649834, by rfl⟩ : syracuseStep 2199779 = 3299669) B3299669
theorem B2199809 : Blo 1464552 2199809 := bstep (se 2 (by rfl) ⟨824928, by rfl⟩ : syracuseStep 2199809 = 1649857) B1649857
theorem B4944131 : Blo 1464552 4944131 := bstep (se 1 (by rfl) ⟨3708098, by rfl⟩ : syracuseStep 4944131 = 7416197) B7416197
theorem B2199827 : Blo 1464552 2199827 := bstep (se 1 (by rfl) ⟨1649870, by rfl⟩ : syracuseStep 2199827 = 3299741) B3299741
theorem B1855811 : Blo 1464552 1855811 := bstep (se 1 (by rfl) ⟨1391858, by rfl⟩ : syracuseStep 1855811 = 2783717) B2783717
theorem B3297617 : Blo 1464552 3297617 := bstep (se 2 (by rfl) ⟨1236606, by rfl⟩ : syracuseStep 3297617 = 2473213) B2473213
theorem B3297635 : Blo 1464552 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B2781553 : Blo 1464552 2781553 := bstep (se 2 (by rfl) ⟨1043082, by rfl⟩ : syracuseStep 2781553 = 2086165) B2086165
theorem B4944401 : Blo 1464552 4944401 := bstep (se 2 (by rfl) ⟨1854150, by rfl⟩ : syracuseStep 4944401 = 3708301) B3708301
theorem B3707441 : Blo 1464552 3707441 := bstep (se 2 (by rfl) ⟨1390290, by rfl⟩ : syracuseStep 3707441 = 2780581) B2780581
theorem B30511669 : Blo 1464552 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B3707491 : Blo 1464552 3707491 := bstep (se 1 (by rfl) ⟨2780618, by rfl⟩ : syracuseStep 3707491 = 5561237) B5561237
theorem B3297905 : Blo 1464552 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B3297923 : Blo 1464552 3297923 := bstep (se 1 (by rfl) ⟨2473442, by rfl⟩ : syracuseStep 3297923 = 4946885) B4946885
theorem B18772661 : Blo 1464552 18772661 := bstep (se 5 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 18772661 = 1759937) B1759937
theorem B2085601 : Blo 1464552 2085601 := bstep (se 2 (by rfl) ⟨782100, by rfl⟩ : syracuseStep 2085601 = 1564201) B1564201
theorem B4174573 : Blo 1464552 4174573 := bstep (se 3 (by rfl) ⟨782732, by rfl⟩ : syracuseStep 4174573 = 1565465) B1565465
theorem B3707633 : Blo 1464552 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B2085635 : Blo 1464552 2085635 := bstep (se 1 (by rfl) ⟨1564226, by rfl⟩ : syracuseStep 2085635 = 3128453) B3128453
theorem B2781955 : Blo 1464552 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B2782001 : Blo 1464552 2782001 := bstep (se 2 (by rfl) ⟨1043250, by rfl⟩ : syracuseStep 2782001 = 2086501) B2086501
theorem B2347859 : Blo 1464552 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B4174733 : Blo 1464552 4174733 := bstep (se 3 (by rfl) ⟨782762, by rfl⟩ : syracuseStep 4174733 = 1565525) B1565525
theorem B3298193 : Blo 1464552 3298193 := bstep (se 2 (by rfl) ⟨1236822, by rfl⟩ : syracuseStep 3298193 = 2473645) B2473645
theorem B3961763 : Blo 1464552 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B3298211 : Blo 1464552 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B17830853 : Blo 1464552 17830853 := bstep (se 4 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 17830853 = 3343285) B3343285
theorem B2970641 : Blo 1464552 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B4944941 : Blo 1464552 4944941 := bstep (se 3 (by rfl) ⟨927176, by rfl⟩ : syracuseStep 4944941 = 1854353) B1854353
theorem B4174915 : Blo 1464552 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B2782289 : Blo 1464552 2782289 := bstep (se 2 (by rfl) ⟨1043358, by rfl⟩ : syracuseStep 2782289 = 2086717) B2086717
theorem B4944995 : Blo 1464552 4944995 := bstep (se 1 (by rfl) ⟨3708746, by rfl⟩ : syracuseStep 4944995 = 7417493) B7417493
theorem B5010605 : Blo 1464552 5010605 := bstep (se 3 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 5010605 = 1878977) B1878977
theorem B3298481 : Blo 1464552 3298481 := bstep (se 2 (by rfl) ⟨1236930, by rfl⟩ : syracuseStep 3298481 = 2473861) B2473861
theorem B3519683 : Blo 1464552 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B3298499 : Blo 1464552 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B6264013 : Blo 1464552 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B2086193 : Blo 1464552 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B7042403 : Blo 1464552 7042403 := bstep (se 1 (by rfl) ⟨5281802, by rfl⟩ : syracuseStep 7042403 = 10563605) B10563605
theorem B4945265 : Blo 1464552 4945265 := bstep (se 2 (by rfl) ⟨1854474, by rfl⟩ : syracuseStep 4945265 = 3708949) B3708949
theorem B2086273 : Blo 1464552 2086273 := bstep (se 2 (by rfl) ⟨782352, by rfl⟩ : syracuseStep 2086273 = 1564705) B1564705
theorem B10032589 : Blo 1464552 10032589 := bstep (se 3 (by rfl) ⟨1881110, by rfl⟩ : syracuseStep 10032589 = 3762221) B3762221
theorem B3298769 : Blo 1464552 3298769 := bstep (se 2 (by rfl) ⟨1237038, by rfl⟩ : syracuseStep 3298769 = 2474077) B2474077
theorem B3298787 : Blo 1464552 3298787 := bstep (se 1 (by rfl) ⟨2474090, by rfl⟩ : syracuseStep 3298787 = 4948181) B4948181
theorem B16512497 : Blo 1464552 16512497 := bstep (se 2 (by rfl) ⟨6192186, by rfl⟩ : syracuseStep 16512497 = 12384373) B12384373
theorem B2348531 : Blo 1464552 2348531 := bstep (se 1 (by rfl) ⟨1761398, by rfl⟩ : syracuseStep 2348531 = 3522797) B3522797
theorem B2471539 : Blo 1464552 2471539 := bstep (se 1 (by rfl) ⟨1853654, by rfl⟩ : syracuseStep 2471539 = 3707309) B3707309
theorem B3708625 : Blo 1464552 3708625 := bstep (se 2 (by rfl) ⟨1390734, by rfl⟩ : syracuseStep 3708625 = 2781469) B2781469
theorem B3299057 : Blo 1464552 3299057 := bstep (se 2 (by rfl) ⟨1237146, by rfl⟩ : syracuseStep 3299057 = 2474293) B2474293
theorem B2471681 : Blo 1464552 2471681 := bstep (se 2 (by rfl) ⟨926880, by rfl⟩ : syracuseStep 2471681 = 1853761) B1853761
theorem B1808131 : Blo 1464552 1808131 := bstep (se 1 (by rfl) ⟨1356098, by rfl⟩ : syracuseStep 1808131 = 2712197) B2712197
theorem B3299075 : Blo 1464552 3299075 := bstep (se 1 (by rfl) ⟨2474306, by rfl⟩ : syracuseStep 3299075 = 4948613) B4948613
theorem B2348833 : Blo 1464552 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B5281571 : Blo 1464552 5281571 := bstep (se 1 (by rfl) ⟨3961178, by rfl⟩ : syracuseStep 5281571 = 7922357) B7922357
theorem B2783011 : Blo 1464552 2783011 := bstep (se 1 (by rfl) ⟨2087258, by rfl⟩ : syracuseStep 2783011 = 4174517) B4174517
theorem B4757329 : Blo 1464552 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B7419761 : Blo 1464552 7419761 := bstep (se 2 (by rfl) ⟨2782410, by rfl⟩ : syracuseStep 7419761 = 5564821) B5564821
theorem B2471809 : Blo 1464552 2471809 := bstep (se 2 (by rfl) ⟨926928, by rfl⟩ : syracuseStep 2471809 = 1853857) B1853857
theorem B4945805 : Blo 1464552 4945805 := bstep (se 3 (by rfl) ⟨927338, by rfl⟩ : syracuseStep 4945805 = 1854677) B1854677
theorem B2471843 : Blo 1464552 2471843 := bstep (se 1 (by rfl) ⟨1853882, by rfl⟩ : syracuseStep 2471843 = 3707765) B3707765
theorem B4945859 : Blo 1464552 4945859 := bstep (se 1 (by rfl) ⟨3709394, by rfl⟩ : syracuseStep 4945859 = 7418789) B7418789
theorem B3708899 : Blo 1464552 3708899 := bstep (se 1 (by rfl) ⟨2781674, by rfl⟩ : syracuseStep 3708899 = 5563349) B5563349
theorem B7043057 : Blo 1464552 7043057 := bstep (se 2 (by rfl) ⟨2641146, by rfl⟩ : syracuseStep 7043057 = 5282293) B5282293
theorem B2349043 : Blo 1464552 2349043 := bstep (se 1 (by rfl) ⟨1761782, by rfl⟩ : syracuseStep 2349043 = 3523565) B3523565
theorem B3299345 : Blo 1464552 3299345 := bstep (se 2 (by rfl) ⟨1237254, by rfl⟩ : syracuseStep 3299345 = 2474509) B2474509
theorem B2349089 : Blo 1464552 2349089 := bstep (se 2 (by rfl) ⟨880908, by rfl⟩ : syracuseStep 2349089 = 1761817) B1761817
theorem B2471971 : Blo 1464552 2471971 := bstep (se 1 (by rfl) ⟨1853978, by rfl⟩ : syracuseStep 2471971 = 3707957) B3707957
theorem B3299363 : Blo 1464552 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B35641457 : Blo 1464552 35641457 := bstep (se 2 (by rfl) ⟨13365546, by rfl⟩ : syracuseStep 35641457 = 26731093) B26731093
theorem B3520643 : Blo 1464552 3520643 := bstep (se 1 (by rfl) ⟨2640482, by rfl⟩ : syracuseStep 3520643 = 5280965) B5280965
theorem B2087059 : Blo 1464552 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B3709091 : Blo 1464552 3709091 := bstep (se 1 (by rfl) ⟨2781818, by rfl⟩ : syracuseStep 3709091 = 5563637) B5563637
theorem B2472113 : Blo 1464552 2472113 := bstep (se 2 (by rfl) ⟨927042, by rfl⟩ : syracuseStep 2472113 = 1854085) B1854085
theorem B3520721 : Blo 1464552 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B4946129 : Blo 1464552 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B2783459 : Blo 1464552 2783459 := bstep (se 1 (by rfl) ⟨2087594, by rfl⟩ : syracuseStep 2783459 = 4175189) B4175189
theorem B1464563 : Blo 1464552 1464563 := bstep (se 1 (by rfl) ⟨1098422, by rfl⟩ : syracuseStep 1464563 = 2196845) B2196845
theorem B1464579 : Blo 1464552 1464579 := bstep (se 1 (by rfl) ⟨1098434, by rfl⟩ : syracuseStep 1464579 = 2196869) B2196869
theorem B1464595 : Blo 1464552 1464595 := bstep (se 1 (by rfl) ⟨1098446, by rfl⟩ : syracuseStep 1464595 = 2196893) B2196893
theorem B1464611 : Blo 1464552 1464611 := bstep (se 1 (by rfl) ⟨1098458, by rfl⟩ : syracuseStep 1464611 = 2196917) B2196917
theorem B4692269 : Blo 1464552 4692269 := bstep (se 3 (by rfl) ⟨879800, by rfl⟩ : syracuseStep 4692269 = 1759601) B1759601
theorem B2472241 : Blo 1464552 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B3299633 : Blo 1464552 3299633 := bstep (se 2 (by rfl) ⟨1237362, by rfl⟩ : syracuseStep 3299633 = 2474725) B2474725
theorem B1464627 : Blo 1464552 1464627 := bstep (se 1 (by rfl) ⟨1098470, by rfl⟩ : syracuseStep 1464627 = 2196941) B2196941
theorem B1464643 : Blo 1464552 1464643 := bstep (se 1 (by rfl) ⟨1098482, by rfl⟩ : syracuseStep 1464643 = 2196965) B2196965
theorem B3299651 : Blo 1464552 3299651 := bstep (se 1 (by rfl) ⟨2474738, by rfl⟩ : syracuseStep 3299651 = 4949477) B4949477
theorem B1464659 : Blo 1464552 1464659 := bstep (se 1 (by rfl) ⟨1098494, by rfl⟩ : syracuseStep 1464659 = 2196989) B2196989
theorem B2472275 : Blo 1464552 2472275 := bstep (se 1 (by rfl) ⟨1854206, by rfl⟩ : syracuseStep 2472275 = 3708413) B3708413
theorem B1464675 : Blo 1464552 1464675 := bstep (se 1 (by rfl) ⟨1098506, by rfl⟩ : syracuseStep 1464675 = 2197013) B2197013
theorem B1464691 : Blo 1464552 1464691 := bstep (se 1 (by rfl) ⟨1098518, by rfl⟩ : syracuseStep 1464691 = 2197037) B2197037
theorem B1464707 : Blo 1464552 1464707 := bstep (se 1 (by rfl) ⟨1098530, by rfl⟩ : syracuseStep 1464707 = 2197061) B2197061
theorem B2972035 : Blo 1464552 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B1464723 : Blo 1464552 1464723 := bstep (se 1 (by rfl) ⟨1098542, by rfl⟩ : syracuseStep 1464723 = 2197085) B2197085
theorem B1464739 : Blo 1464552 1464739 := bstep (se 1 (by rfl) ⟨1098554, by rfl⟩ : syracuseStep 1464739 = 2197109) B2197109
theorem B1464755 : Blo 1464552 1464755 := bstep (se 1 (by rfl) ⟨1098566, by rfl⟩ : syracuseStep 1464755 = 2197133) B2197133
theorem B1464771 : Blo 1464552 1464771 := bstep (se 1 (by rfl) ⟨1098578, by rfl⟩ : syracuseStep 1464771 = 2197157) B2197157
theorem B1464787 : Blo 1464552 1464787 := bstep (se 1 (by rfl) ⟨1098590, by rfl⟩ : syracuseStep 1464787 = 2197181) B2197181
theorem B2472403 : Blo 1464552 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B1464803 : Blo 1464552 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B1464819 : Blo 1464552 1464819 := bstep (se 1 (by rfl) ⟨1098614, by rfl⟩ : syracuseStep 1464819 = 2197229) B2197229
theorem B1464835 : Blo 1464552 1464835 := bstep (se 1 (by rfl) ⟨1098626, by rfl⟩ : syracuseStep 1464835 = 2197253) B2197253
theorem B3258883 : Blo 1464552 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B2783747 : Blo 1464552 2783747 := bstep (se 1 (by rfl) ⟨2087810, by rfl⟩ : syracuseStep 2783747 = 4175621) B4175621
theorem B1464851 : Blo 1464552 1464851 := bstep (se 1 (by rfl) ⟨1098638, by rfl⟩ : syracuseStep 1464851 = 2197277) B2197277
theorem B1464867 : Blo 1464552 1464867 := bstep (se 1 (by rfl) ⟨1098650, by rfl⟩ : syracuseStep 1464867 = 2197301) B2197301
theorem B1464883 : Blo 1464552 1464883 := bstep (se 1 (by rfl) ⟨1098662, by rfl⟩ : syracuseStep 1464883 = 2197325) B2197325
theorem B1464899 : Blo 1464552 1464899 := bstep (se 1 (by rfl) ⟨1098674, by rfl⟩ : syracuseStep 1464899 = 2197349) B2197349
theorem B1464915 : Blo 1464552 1464915 := bstep (se 1 (by rfl) ⟨1098686, by rfl⟩ : syracuseStep 1464915 = 2197373) B2197373
theorem B2472545 : Blo 1464552 2472545 := bstep (se 2 (by rfl) ⟨927204, by rfl⟩ : syracuseStep 2472545 = 1854409) B1854409
theorem B1464931 : Blo 1464552 1464931 := bstep (se 1 (by rfl) ⟨1098698, by rfl⟩ : syracuseStep 1464931 = 2197397) B2197397
theorem B2087537 : Blo 1464552 2087537 := bstep (se 2 (by rfl) ⟨782826, by rfl⟩ : syracuseStep 2087537 = 1565653) B1565653
theorem B1464947 : Blo 1464552 1464947 := bstep (se 1 (by rfl) ⟨1098710, by rfl⟩ : syracuseStep 1464947 = 2197421) B2197421
theorem B1464963 : Blo 1464552 1464963 := bstep (se 1 (by rfl) ⟨1098722, by rfl⟩ : syracuseStep 1464963 = 2197445) B2197445
theorem B1464979 : Blo 1464552 1464979 := bstep (se 1 (by rfl) ⟨1098734, by rfl⟩ : syracuseStep 1464979 = 2197469) B2197469
theorem B1464995 : Blo 1464552 1464995 := bstep (se 1 (by rfl) ⟨1098746, by rfl⟩ : syracuseStep 1464995 = 2197493) B2197493
theorem B2513585 : Blo 1464552 2513585 := bstep (se 2 (by rfl) ⟨942594, by rfl⟩ : syracuseStep 2513585 = 1885189) B1885189
theorem B1465011 : Blo 1464552 1465011 := bstep (se 1 (by rfl) ⟨1098758, by rfl⟩ : syracuseStep 1465011 = 2197517) B2197517
theorem B1465027 : Blo 1464552 1465027 := bstep (se 1 (by rfl) ⟨1098770, by rfl⟩ : syracuseStep 1465027 = 2197541) B2197541
theorem B1465043 : Blo 1464552 1465043 := bstep (se 1 (by rfl) ⟨1098782, by rfl⟩ : syracuseStep 1465043 = 2197565) B2197565
theorem B2472673 : Blo 1464552 2472673 := bstep (se 2 (by rfl) ⟨927252, by rfl⟩ : syracuseStep 2472673 = 1854505) B1854505
theorem B1465059 : Blo 1464552 1465059 := bstep (se 1 (by rfl) ⟨1098794, by rfl⟩ : syracuseStep 1465059 = 2197589) B2197589
theorem B2087651 : Blo 1464552 2087651 := bstep (se 1 (by rfl) ⟨1565738, by rfl⟩ : syracuseStep 2087651 = 3131477) B3131477
theorem B4946669 : Blo 1464552 4946669 := bstep (se 3 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 4946669 = 1855001) B1855001
theorem B1465075 : Blo 1464552 1465075 := bstep (se 1 (by rfl) ⟨1098806, by rfl⟩ : syracuseStep 1465075 = 2197613) B2197613
theorem B2226947 : Blo 1464552 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B1465091 : Blo 1464552 1465091 := bstep (se 1 (by rfl) ⟨1098818, by rfl⟩ : syracuseStep 1465091 = 2197637) B2197637
theorem B2472707 : Blo 1464552 2472707 := bstep (se 1 (by rfl) ⟨1854530, by rfl⟩ : syracuseStep 2472707 = 3709061) B3709061
theorem B1465107 : Blo 1464552 1465107 := bstep (se 1 (by rfl) ⟨1098830, by rfl⟩ : syracuseStep 1465107 = 2197661) B2197661
theorem B1465123 : Blo 1464552 1465123 := bstep (se 1 (by rfl) ⟨1098842, by rfl⟩ : syracuseStep 1465123 = 2197685) B2197685
theorem B4946723 : Blo 1464552 4946723 := bstep (se 1 (by rfl) ⟨3710042, by rfl⟩ : syracuseStep 4946723 = 7420085) B7420085
theorem B1465139 : Blo 1464552 1465139 := bstep (se 1 (by rfl) ⟨1098854, by rfl⟩ : syracuseStep 1465139 = 2197709) B2197709
theorem B2087731 : Blo 1464552 2087731 := bstep (se 1 (by rfl) ⟨1565798, by rfl⟩ : syracuseStep 2087731 = 3131597) B3131597
theorem B1465155 : Blo 1464552 1465155 := bstep (se 1 (by rfl) ⟨1098866, by rfl⟩ : syracuseStep 1465155 = 2197733) B2197733
theorem B1465171 : Blo 1464552 1465171 := bstep (se 1 (by rfl) ⟨1098878, by rfl⟩ : syracuseStep 1465171 = 2197757) B2197757
theorem B1465187 : Blo 1464552 1465187 := bstep (se 1 (by rfl) ⟨1098890, by rfl⟩ : syracuseStep 1465187 = 2197781) B2197781
theorem B1465203 : Blo 1464552 1465203 := bstep (se 1 (by rfl) ⟨1098902, by rfl⟩ : syracuseStep 1465203 = 2197805) B2197805
theorem B1465219 : Blo 1464552 1465219 := bstep (se 1 (by rfl) ⟨1098914, by rfl⟩ : syracuseStep 1465219 = 2197829) B2197829
theorem B2472835 : Blo 1464552 2472835 := bstep (se 1 (by rfl) ⟨1854626, by rfl⟩ : syracuseStep 2472835 = 3709253) B3709253
theorem B1465235 : Blo 1464552 1465235 := bstep (se 1 (by rfl) ⟨1098926, by rfl⟩ : syracuseStep 1465235 = 2197853) B2197853
theorem B1465251 : Blo 1464552 1465251 := bstep (se 1 (by rfl) ⟨1098938, by rfl⟩ : syracuseStep 1465251 = 2197877) B2197877
theorem B1465267 : Blo 1464552 1465267 := bstep (se 1 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 1465267 = 2197901) B2197901
theorem B1465283 : Blo 1464552 1465283 := bstep (se 1 (by rfl) ⟨1098962, by rfl⟩ : syracuseStep 1465283 = 2197925) B2197925
theorem B1465299 : Blo 1464552 1465299 := bstep (se 1 (by rfl) ⟨1098974, by rfl⟩ : syracuseStep 1465299 = 2197949) B2197949
theorem B3128291 : Blo 1464552 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B1465315 : Blo 1464552 1465315 := bstep (se 1 (by rfl) ⟨1098986, by rfl⟩ : syracuseStep 1465315 = 2197973) B2197973
theorem B1465331 : Blo 1464552 1465331 := bstep (se 1 (by rfl) ⟨1098998, by rfl⟩ : syracuseStep 1465331 = 2197997) B2197997
theorem B3341315 : Blo 1464552 3341315 := bstep (se 1 (by rfl) ⟨2505986, by rfl⟩ : syracuseStep 3341315 = 5011973) B5011973
theorem B1465347 : Blo 1464552 1465347 := bstep (se 1 (by rfl) ⟨1099010, by rfl⟩ : syracuseStep 1465347 = 2198021) B2198021
theorem B2472977 : Blo 1464552 2472977 := bstep (se 2 (by rfl) ⟨927366, by rfl⟩ : syracuseStep 2472977 = 1854733) B1854733
theorem B1465363 : Blo 1464552 1465363 := bstep (se 1 (by rfl) ⟨1099022, by rfl⟩ : syracuseStep 1465363 = 2198045) B2198045
theorem B10026019 : Blo 1464552 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B1465379 : Blo 1464552 1465379 := bstep (se 1 (by rfl) ⟨1099034, by rfl⟩ : syracuseStep 1465379 = 2198069) B2198069
theorem B4946993 : Blo 1464552 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B1465395 : Blo 1464552 1465395 := bstep (se 1 (by rfl) ⟨1099046, by rfl⟩ : syracuseStep 1465395 = 2198093) B2198093
theorem B1465411 : Blo 1464552 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B9403469 : Blo 1464552 9403469 := bstep (se 3 (by rfl) ⟨1763150, by rfl⟩ : syracuseStep 9403469 = 3526301) B3526301
theorem B6020173 : Blo 1464552 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B3759185 : Blo 1464552 3759185 := bstep (se 2 (by rfl) ⟨1409694, by rfl⟩ : syracuseStep 3759185 = 2819389) B2819389
theorem B3710033 : Blo 1464552 3710033 := bstep (se 2 (by rfl) ⟨1391262, by rfl⟩ : syracuseStep 3710033 = 2782525) B2782525
theorem B1465427 : Blo 1464552 1465427 := bstep (se 1 (by rfl) ⟨1099070, by rfl⟩ : syracuseStep 1465427 = 2198141) B2198141
theorem B1465443 : Blo 1464552 1465443 := bstep (se 1 (by rfl) ⟨1099082, by rfl⟩ : syracuseStep 1465443 = 2198165) B2198165
theorem B1465459 : Blo 1464552 1465459 := bstep (se 1 (by rfl) ⟨1099094, by rfl⟩ : syracuseStep 1465459 = 2198189) B2198189
theorem B7044209 : Blo 1464552 7044209 := bstep (se 2 (by rfl) ⟨2641578, by rfl⟩ : syracuseStep 7044209 = 5283157) B5283157
theorem B1465475 : Blo 1464552 1465475 := bstep (se 1 (by rfl) ⟨1099106, by rfl⟩ : syracuseStep 1465475 = 2198213) B2198213
theorem B3710083 : Blo 1464552 3710083 := bstep (se 1 (by rfl) ⟨2782562, by rfl⟩ : syracuseStep 3710083 = 5565125) B5565125
theorem B2473105 : Blo 1464552 2473105 := bstep (se 2 (by rfl) ⟨927414, by rfl⟩ : syracuseStep 2473105 = 1854829) B1854829
theorem B1465491 : Blo 1464552 1465491 := bstep (se 1 (by rfl) ⟨1099118, by rfl⟩ : syracuseStep 1465491 = 2198237) B2198237
theorem B6257827 : Blo 1464552 6257827 := bstep (se 1 (by rfl) ⟨4693370, by rfl⟩ : syracuseStep 6257827 = 9386741) B9386741
theorem B1465507 : Blo 1464552 1465507 := bstep (se 1 (by rfl) ⟨1099130, by rfl⟩ : syracuseStep 1465507 = 2198261) B2198261
theorem B1465523 : Blo 1464552 1465523 := bstep (se 1 (by rfl) ⟨1099142, by rfl⟩ : syracuseStep 1465523 = 2198285) B2198285
theorem B2473139 : Blo 1464552 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B1465539 : Blo 1464552 1465539 := bstep (se 1 (by rfl) ⟨1099154, by rfl⟩ : syracuseStep 1465539 = 2198309) B2198309
theorem B14277829 : Blo 1464552 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1465555 : Blo 1464552 1465555 := bstep (se 1 (by rfl) ⟨1099166, by rfl⟩ : syracuseStep 1465555 = 2198333) B2198333
theorem B1465571 : Blo 1464552 1465571 := bstep (se 1 (by rfl) ⟨1099178, by rfl⟩ : syracuseStep 1465571 = 2198357) B2198357
theorem B1465587 : Blo 1464552 1465587 := bstep (se 1 (by rfl) ⟨1099190, by rfl⟩ : syracuseStep 1465587 = 2198381) B2198381
theorem B1465603 : Blo 1464552 1465603 := bstep (se 1 (by rfl) ⟨1099202, by rfl⟩ : syracuseStep 1465603 = 2198405) B2198405
theorem B12524813 : Blo 1464552 12524813 := bstep (se 3 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 12524813 = 4696805) B4696805
theorem B3710225 : Blo 1464552 3710225 := bstep (se 2 (by rfl) ⟨1391334, by rfl⟩ : syracuseStep 3710225 = 2782669) B2782669
theorem B1465619 : Blo 1464552 1465619 := bstep (se 1 (by rfl) ⟨1099214, by rfl⟩ : syracuseStep 1465619 = 2198429) B2198429
theorem B1465635 : Blo 1464552 1465635 := bstep (se 1 (by rfl) ⟨1099226, by rfl⟩ : syracuseStep 1465635 = 2198453) B2198453
theorem B7421219 : Blo 1464552 7421219 := bstep (se 1 (by rfl) ⟨5565914, by rfl⟩ : syracuseStep 7421219 = 11131829) B11131829
theorem B2473267 : Blo 1464552 2473267 := bstep (se 1 (by rfl) ⟨1854950, by rfl⟩ : syracuseStep 2473267 = 3709901) B3709901
theorem B1465651 : Blo 1464552 1465651 := bstep (se 1 (by rfl) ⟨1099238, by rfl⟩ : syracuseStep 1465651 = 2198477) B2198477
theorem B1465667 : Blo 1464552 1465667 := bstep (se 1 (by rfl) ⟨1099250, by rfl⟩ : syracuseStep 1465667 = 2198501) B2198501
theorem B1465683 : Blo 1464552 1465683 := bstep (se 1 (by rfl) ⟨1099262, by rfl⟩ : syracuseStep 1465683 = 2198525) B2198525
theorem B1465699 : Blo 1464552 1465699 := bstep (se 1 (by rfl) ⟨1099274, by rfl⟩ : syracuseStep 1465699 = 2198549) B2198549
theorem B1465715 : Blo 1464552 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B1465731 : Blo 1464552 1465731 := bstep (se 1 (by rfl) ⟨1099298, by rfl⟩ : syracuseStep 1465731 = 2198597) B2198597
theorem B2006417 : Blo 1464552 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B2973073 : Blo 1464552 2973073 := bstep (se 2 (by rfl) ⟨1114902, by rfl⟩ : syracuseStep 2973073 = 2229805) B2229805
theorem B1465747 : Blo 1464552 1465747 := bstep (se 1 (by rfl) ⟨1099310, by rfl⟩ : syracuseStep 1465747 = 2198621) B2198621
theorem B1465763 : Blo 1464552 1465763 := bstep (se 1 (by rfl) ⟨1099322, by rfl⟩ : syracuseStep 1465763 = 2198645) B2198645
theorem B1465779 : Blo 1464552 1465779 := bstep (se 1 (by rfl) ⟨1099334, by rfl⟩ : syracuseStep 1465779 = 2198669) B2198669
theorem B2473409 : Blo 1464552 2473409 := bstep (se 2 (by rfl) ⟨927528, by rfl⟩ : syracuseStep 2473409 = 1855057) B1855057
theorem B1465795 : Blo 1464552 1465795 := bstep (se 1 (by rfl) ⟨1099346, by rfl⟩ : syracuseStep 1465795 = 2198693) B2198693
theorem B17817029 : Blo 1464552 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B1564115 : Blo 1464552 1564115 := bstep (se 1 (by rfl) ⟨1173086, by rfl⟩ : syracuseStep 1564115 = 2346173) B2346173
theorem B1465811 : Blo 1464552 1465811 := bstep (se 1 (by rfl) ⟨1099358, by rfl⟩ : syracuseStep 1465811 = 2198717) B2198717
theorem B1465827 : Blo 1464552 1465827 := bstep (se 1 (by rfl) ⟨1099370, by rfl⟩ : syracuseStep 1465827 = 2198741) B2198741
theorem B11886065 : Blo 1464552 11886065 := bstep (se 2 (by rfl) ⟨4457274, by rfl⟩ : syracuseStep 11886065 = 8914549) B8914549
theorem B1465843 : Blo 1464552 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B1465859 : Blo 1464552 1465859 := bstep (se 1 (by rfl) ⟨1099394, by rfl⟩ : syracuseStep 1465859 = 2198789) B2198789
theorem B1465875 : Blo 1464552 1465875 := bstep (se 1 (by rfl) ⟨1099406, by rfl⟩ : syracuseStep 1465875 = 2198813) B2198813
theorem B5561891 : Blo 1464552 5561891 := bstep (se 1 (by rfl) ⟨4171418, by rfl⟩ : syracuseStep 5561891 = 8342837) B8342837
theorem B1465891 : Blo 1464552 1465891 := bstep (se 1 (by rfl) ⟨1099418, by rfl⟩ : syracuseStep 1465891 = 2198837) B2198837
theorem B5561905 : Blo 1464552 5561905 := bstep (se 2 (by rfl) ⟨2085714, by rfl⟩ : syracuseStep 5561905 = 4171429) B4171429
theorem B1465907 : Blo 1464552 1465907 := bstep (se 1 (by rfl) ⟨1099430, by rfl⟩ : syracuseStep 1465907 = 2198861) B2198861
theorem B2473537 : Blo 1464552 2473537 := bstep (se 2 (by rfl) ⟨927576, by rfl⟩ : syracuseStep 2473537 = 1855153) B1855153
theorem B1465923 : Blo 1464552 1465923 := bstep (se 1 (by rfl) ⟨1099442, by rfl⟩ : syracuseStep 1465923 = 2198885) B2198885
theorem B4947533 : Blo 1464552 4947533 := bstep (se 3 (by rfl) ⟨927662, by rfl⟩ : syracuseStep 4947533 = 1855325) B1855325
theorem B1465939 : Blo 1464552 1465939 := bstep (se 1 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 1465939 = 2198909) B2198909
theorem B2473571 : Blo 1464552 2473571 := bstep (se 1 (by rfl) ⟨1855178, by rfl⟩ : syracuseStep 2473571 = 3710357) B3710357
theorem B1465955 : Blo 1464552 1465955 := bstep (se 1 (by rfl) ⟨1099466, by rfl⟩ : syracuseStep 1465955 = 2198933) B2198933
theorem B1465971 : Blo 1464552 1465971 := bstep (se 1 (by rfl) ⟨1099478, by rfl⟩ : syracuseStep 1465971 = 2198957) B2198957
theorem B4947587 : Blo 1464552 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B1465987 : Blo 1464552 1465987 := bstep (se 1 (by rfl) ⟨1099490, by rfl⟩ : syracuseStep 1465987 = 2198981) B2198981
theorem B1466003 : Blo 1464552 1466003 := bstep (se 1 (by rfl) ⟨1099502, by rfl⟩ : syracuseStep 1466003 = 2199005) B2199005
theorem B1466019 : Blo 1464552 1466019 := bstep (se 1 (by rfl) ⟨1099514, by rfl⟩ : syracuseStep 1466019 = 2199029) B2199029
theorem B1466035 : Blo 1464552 1466035 := bstep (se 1 (by rfl) ⟨1099526, by rfl⟩ : syracuseStep 1466035 = 2199053) B2199053
theorem B1466051 : Blo 1464552 1466051 := bstep (se 1 (by rfl) ⟨1099538, by rfl⟩ : syracuseStep 1466051 = 2199077) B2199077
theorem B1466067 : Blo 1464552 1466067 := bstep (se 1 (by rfl) ⟨1099550, by rfl⟩ : syracuseStep 1466067 = 2199101) B2199101
theorem B12517091 : Blo 1464552 12517091 := bstep (se 1 (by rfl) ⟨9387818, by rfl⟩ : syracuseStep 12517091 = 18775637) B18775637
theorem B2473699 : Blo 1464552 2473699 := bstep (se 1 (by rfl) ⟨1855274, by rfl⟩ : syracuseStep 2473699 = 3710549) B3710549
theorem B1466083 : Blo 1464552 1466083 := bstep (se 1 (by rfl) ⟨1099562, by rfl⟩ : syracuseStep 1466083 = 2199125) B2199125
theorem B1466099 : Blo 1464552 1466099 := bstep (se 1 (by rfl) ⟨1099574, by rfl⟩ : syracuseStep 1466099 = 2199149) B2199149
theorem B1466115 : Blo 1464552 1466115 := bstep (se 1 (by rfl) ⟨1099586, by rfl⟩ : syracuseStep 1466115 = 2199173) B2199173
theorem B1466131 : Blo 1464552 1466131 := bstep (se 1 (by rfl) ⟨1099598, by rfl⟩ : syracuseStep 1466131 = 2199197) B2199197
theorem B1466147 : Blo 1464552 1466147 := bstep (se 1 (by rfl) ⟨1099610, by rfl⟩ : syracuseStep 1466147 = 2199221) B2199221
theorem B1466163 : Blo 1464552 1466163 := bstep (se 1 (by rfl) ⟨1099622, by rfl⟩ : syracuseStep 1466163 = 2199245) B2199245
theorem B1466179 : Blo 1464552 1466179 := bstep (se 1 (by rfl) ⟨1099634, by rfl⟩ : syracuseStep 1466179 = 2199269) B2199269
theorem B1466195 : Blo 1464552 1466195 := bstep (se 1 (by rfl) ⟨1099646, by rfl⟩ : syracuseStep 1466195 = 2199293) B2199293
theorem B3129187 : Blo 1464552 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B3522403 : Blo 1464552 3522403 := bstep (se 1 (by rfl) ⟨2641802, by rfl⟩ : syracuseStep 3522403 = 5283605) B5283605
theorem B1466211 : Blo 1464552 1466211 := bstep (se 1 (by rfl) ⟨1099658, by rfl⟩ : syracuseStep 1466211 = 2199317) B2199317
theorem B2473841 : Blo 1464552 2473841 := bstep (se 2 (by rfl) ⟨927690, by rfl⟩ : syracuseStep 2473841 = 1855381) B1855381
theorem B7044977 : Blo 1464552 7044977 := bstep (se 2 (by rfl) ⟨2641866, by rfl⟩ : syracuseStep 7044977 = 5283733) B5283733
theorem B1761139 : Blo 1464552 1761139 := bstep (se 1 (by rfl) ⟨1320854, by rfl⟩ : syracuseStep 1761139 = 2641709) B2641709
theorem B1466227 : Blo 1464552 1466227 := bstep (se 1 (by rfl) ⟨1099670, by rfl⟩ : syracuseStep 1466227 = 2199341) B2199341
theorem B1466243 : Blo 1464552 1466243 := bstep (se 1 (by rfl) ⟨1099682, by rfl⟩ : syracuseStep 1466243 = 2199365) B2199365
theorem B4947857 : Blo 1464552 4947857 := bstep (se 2 (by rfl) ⟨1855446, by rfl⟩ : syracuseStep 4947857 = 3710893) B3710893
theorem B1466259 : Blo 1464552 1466259 := bstep (se 1 (by rfl) ⟨1099694, by rfl⟩ : syracuseStep 1466259 = 2199389) B2199389
theorem B1466275 : Blo 1464552 1466275 := bstep (se 1 (by rfl) ⟨1099706, by rfl⟩ : syracuseStep 1466275 = 2199413) B2199413
theorem B1466291 : Blo 1464552 1466291 := bstep (se 1 (by rfl) ⟨1099718, by rfl⟩ : syracuseStep 1466291 = 2199437) B2199437
theorem B1466307 : Blo 1464552 1466307 := bstep (se 1 (by rfl) ⟨1099730, by rfl⟩ : syracuseStep 1466307 = 2199461) B2199461
theorem B1466323 : Blo 1464552 1466323 := bstep (se 1 (by rfl) ⟨1099742, by rfl⟩ : syracuseStep 1466323 = 2199485) B2199485
theorem B1466339 : Blo 1464552 1466339 := bstep (se 1 (by rfl) ⟨1099754, by rfl⟩ : syracuseStep 1466339 = 2199509) B2199509
theorem B2473969 : Blo 1464552 2473969 := bstep (se 2 (by rfl) ⟨927738, by rfl⟩ : syracuseStep 2473969 = 1855477) B1855477
theorem B1466355 : Blo 1464552 1466355 := bstep (se 1 (by rfl) ⟨1099766, by rfl⟩ : syracuseStep 1466355 = 2199533) B2199533
theorem B1466379 : Blo 1464552 1466379 := bstep (se 1 (by rfl) ⟨1099784, by rfl⟩ : syracuseStep 1466379 = 2199569) B2199569
theorem B5562391 : Blo 1464552 5562391 := bstep (se 1 (by rfl) ⟨4171793, by rfl⟩ : syracuseStep 5562391 = 8343587) B8343587
theorem B1466391 : Blo 1464552 1466391 := bstep (se 1 (by rfl) ⟨1099793, by rfl⟩ : syracuseStep 1466391 = 2199587) B2199587
theorem B1466411 : Blo 1464552 1466411 := bstep (se 1 (by rfl) ⟨1099808, by rfl⟩ : syracuseStep 1466411 = 2199617) B2199617
theorem B7921709 : Blo 1464552 7921709 := bstep (se 3 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 7921709 = 2970641) B2970641
theorem B4948019 : Blo 1464552 4948019 := bstep (se 1 (by rfl) ⟨3711014, by rfl⟩ : syracuseStep 4948019 = 7422029) B7422029
theorem B1466423 : Blo 1464552 1466423 := bstep (se 1 (by rfl) ⟨1099817, by rfl⟩ : syracuseStep 1466423 = 2199635) B2199635
theorem B8462411 : Blo 1464552 8462411 := bstep (se 1 (by rfl) ⟨6346808, by rfl⟩ : syracuseStep 8462411 = 12693617) B12693617
theorem B3522635 : Blo 1464552 3522635 := bstep (se 1 (by rfl) ⟨2641976, by rfl⟩ : syracuseStep 3522635 = 5283953) B5283953
theorem B1466443 : Blo 1464552 1466443 := bstep (se 1 (by rfl) ⟨1099832, by rfl⟩ : syracuseStep 1466443 = 2199665) B2199665
theorem B1466455 : Blo 1464552 1466455 := bstep (se 1 (by rfl) ⟨1099841, by rfl⟩ : syracuseStep 1466455 = 2199683) B2199683
theorem B13377629 : Blo 1464552 13377629 := bstep (se 3 (by rfl) ⟨2508305, by rfl⟩ : syracuseStep 13377629 = 5016611) B5016611
theorem B1466475 : Blo 1464552 1466475 := bstep (se 1 (by rfl) ⟨1099856, by rfl⟩ : syracuseStep 1466475 = 2199713) B2199713
theorem B1466487 : Blo 1464552 1466487 := bstep (se 1 (by rfl) ⟨1099865, by rfl⟩ : syracuseStep 1466487 = 2199731) B2199731
theorem B1466507 : Blo 1464552 1466507 := bstep (se 1 (by rfl) ⟨1099880, by rfl⟩ : syracuseStep 1466507 = 2199761) B2199761
theorem B1466519 : Blo 1464552 1466519 := bstep (se 1 (by rfl) ⟨1099889, by rfl⟩ : syracuseStep 1466519 = 2199779) B2199779
theorem B1466539 : Blo 1464552 1466539 := bstep (se 1 (by rfl) ⟨1099904, by rfl⟩ : syracuseStep 1466539 = 2199809) B2199809
theorem B1466551 : Blo 1464552 1466551 := bstep (se 1 (by rfl) ⟨1099913, by rfl⟩ : syracuseStep 1466551 = 2199827) B2199827
theorem B16695557 : Blo 1464552 16695557 := bstep (se 4 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 16695557 = 3130417) B3130417
theorem B4948289 : Blo 1464552 4948289 := bstep (se 2 (by rfl) ⟨1855608, by rfl⟩ : syracuseStep 4948289 = 3711217) B3711217
theorem B2474327 : Blo 1464552 2474327 := bstep (se 1 (by rfl) ⟨1855745, by rfl⟩ : syracuseStep 2474327 = 3711491) B3711491
theorem B9388381 : Blo 1464552 9388381 := bstep (se 3 (by rfl) ⟨1760321, by rfl⟩ : syracuseStep 9388381 = 3520643) B3520643
theorem B2474455 : Blo 1464552 2474455 := bstep (se 1 (by rfl) ⟨1855841, by rfl⟩ : syracuseStep 2474455 = 3711683) B3711683
theorem B1565239 : Blo 1464552 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B3129931 : Blo 1464552 3129931 := bstep (se 1 (by rfl) ⟨2347448, by rfl⟩ : syracuseStep 3129931 = 4694897) B4694897
theorem B6259331 : Blo 1464552 6259331 := bstep (se 1 (by rfl) ⟨4694498, by rfl⟩ : syracuseStep 6259331 = 9388997) B9388997
theorem B11887235 : Blo 1464552 11887235 := bstep (se 1 (by rfl) ⟨8915426, by rfl⟩ : syracuseStep 11887235 = 17830853) B17830853
theorem B3130007 : Blo 1464552 3130007 := bstep (se 1 (by rfl) ⟨2347505, by rfl⟩ : syracuseStep 3130007 = 4695011) B4695011
theorem B40682225 : Blo 1464552 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B5563181 : Blo 1464552 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B4948829 : Blo 1464552 4948829 := bstep (se 3 (by rfl) ⟨927905, by rfl⟩ : syracuseStep 4948829 = 1855811) B1855811
theorem B4694935 : Blo 1464552 4694935 := bstep (se 1 (by rfl) ⟨3521201, by rfl⟩ : syracuseStep 4694935 = 7042403) B7042403
theorem B6259673 : Blo 1464552 6259673 := bstep (se 2 (by rfl) ⟨2347377, by rfl⟩ : syracuseStep 6259673 = 4694755) B4694755
theorem B1565687 : Blo 1464552 1565687 := bstep (se 1 (by rfl) ⟨1174265, by rfl⟩ : syracuseStep 1565687 = 2348531) B2348531
theorem B5350445 : Blo 1464552 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B1647787 : Blo 1464552 1647787 := bstep (se 1 (by rfl) ⟨1235840, by rfl⟩ : syracuseStep 1647787 = 2471681) B2471681
theorem B1647895 : Blo 1464552 1647895 := bstep (se 1 (by rfl) ⟨1235921, by rfl⟩ : syracuseStep 1647895 = 2471843) B2471843
theorem B4695371 : Blo 1464552 4695371 := bstep (se 1 (by rfl) ⟨3521528, by rfl⟩ : syracuseStep 4695371 = 7043057) B7043057
theorem B7423325 : Blo 1464552 7423325 := bstep (se 3 (by rfl) ⟨1391873, by rfl⟩ : syracuseStep 7423325 = 2783747) B2783747
theorem B1566059 : Blo 1464552 1566059 := bstep (se 1 (by rfl) ⟨1174544, by rfl⟩ : syracuseStep 1566059 = 2349089) B2349089
theorem B2196875 : Blo 1464552 2196875 := bstep (se 1 (by rfl) ⟨1647656, by rfl⟩ : syracuseStep 2196875 = 3295313) B3295313
theorem B2196887 : Blo 1464552 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1648075 : Blo 1464552 1648075 := bstep (se 1 (by rfl) ⟨1236056, by rfl⟩ : syracuseStep 1648075 = 2472113) B2472113
theorem B2196953 : Blo 1464552 2196953 := bstep (se 2 (by rfl) ⟨823857, by rfl⟩ : syracuseStep 2196953 = 1647715) B1647715
theorem B1648183 : Blo 1464552 1648183 := bstep (se 1 (by rfl) ⟨1236137, by rfl⟩ : syracuseStep 1648183 = 2472275) B2472275
theorem B2197067 : Blo 1464552 2197067 := bstep (se 1 (by rfl) ⟨1647800, by rfl⟩ : syracuseStep 2197067 = 3295601) B3295601
theorem B2197079 : Blo 1464552 2197079 := bstep (se 1 (by rfl) ⟨1647809, by rfl⟩ : syracuseStep 2197079 = 3295619) B3295619
theorem B2197145 : Blo 1464552 2197145 := bstep (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) B1647859
theorem B1648363 : Blo 1464552 1648363 := bstep (se 1 (by rfl) ⟨1236272, by rfl⟩ : syracuseStep 1648363 = 2472545) B2472545
theorem B14075653 : Blo 1464552 14075653 := bstep (se 4 (by rfl) ⟨1319592, by rfl⟩ : syracuseStep 14075653 = 2639185) B2639185
theorem B2197259 : Blo 1464552 2197259 := bstep (se 1 (by rfl) ⟨1647944, by rfl⟩ : syracuseStep 2197259 = 3295889) B3295889
theorem B2197271 : Blo 1464552 2197271 := bstep (se 1 (by rfl) ⟨1647953, by rfl⟩ : syracuseStep 2197271 = 3295907) B3295907
theorem B1648471 : Blo 1464552 1648471 := bstep (se 1 (by rfl) ⟨1236353, by rfl⟩ : syracuseStep 1648471 = 2472707) B2472707
theorem B2197337 : Blo 1464552 2197337 := bstep (se 2 (by rfl) ⟨824001, by rfl⟩ : syracuseStep 2197337 = 1648003) B1648003
theorem B8341379 : Blo 1464552 8341379 := bstep (se 1 (by rfl) ⟨6256034, by rfl⟩ : syracuseStep 8341379 = 12512069) B12512069
theorem B13371313 : Blo 1464552 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B2197451 : Blo 1464552 2197451 := bstep (se 1 (by rfl) ⟨1648088, by rfl⟩ : syracuseStep 2197451 = 3296177) B3296177
theorem B2197463 : Blo 1464552 2197463 := bstep (se 1 (by rfl) ⟨1648097, by rfl⟩ : syracuseStep 2197463 = 3296195) B3296195
theorem B1648651 : Blo 1464552 1648651 := bstep (se 1 (by rfl) ⟨1236488, by rfl⟩ : syracuseStep 1648651 = 2472977) B2472977
theorem B2197529 : Blo 1464552 2197529 := bstep (se 2 (by rfl) ⟨824073, by rfl⟩ : syracuseStep 2197529 = 1648147) B1648147
theorem B6268979 : Blo 1464552 6268979 := bstep (se 1 (by rfl) ⟨4701734, by rfl⟩ : syracuseStep 6268979 = 9403469) B9403469
theorem B7415873 : Blo 1464552 7415873 := bstep (se 2 (by rfl) ⟨2780952, by rfl⟩ : syracuseStep 7415873 = 5561905) B5561905
theorem B4696139 : Blo 1464552 4696139 := bstep (se 1 (by rfl) ⟨3522104, by rfl⟩ : syracuseStep 4696139 = 7044209) B7044209
theorem B14084189 : Blo 1464552 14084189 := bstep (se 3 (by rfl) ⟨2640785, by rfl⟩ : syracuseStep 14084189 = 5281571) B5281571
theorem B1648759 : Blo 1464552 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B2197643 : Blo 1464552 2197643 := bstep (se 1 (by rfl) ⟨1648232, by rfl⟩ : syracuseStep 2197643 = 3296465) B3296465
theorem B2197655 : Blo 1464552 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B3295385 : Blo 1464552 3295385 := bstep (se 2 (by rfl) ⟨1235769, by rfl⟩ : syracuseStep 3295385 = 2471539) B2471539
theorem B8349875 : Blo 1464552 8349875 := bstep (se 1 (by rfl) ⟨6262406, by rfl⟩ : syracuseStep 8349875 = 12524813) B12524813
theorem B5564609 : Blo 1464552 5564609 := bstep (se 2 (by rfl) ⟨2086728, by rfl⟩ : syracuseStep 5564609 = 4173457) B4173457
theorem B2197721 : Blo 1464552 2197721 := bstep (se 2 (by rfl) ⟨824145, by rfl⟩ : syracuseStep 2197721 = 1648291) B1648291
theorem B3295475 : Blo 1464552 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B3295511 : Blo 1464552 3295511 := bstep (se 1 (by rfl) ⟨2471633, by rfl⟩ : syracuseStep 3295511 = 4943267) B4943267
theorem B1648939 : Blo 1464552 1648939 := bstep (se 1 (by rfl) ⟨1236704, by rfl⟩ : syracuseStep 1648939 = 2473409) B2473409
theorem B14084417 : Blo 1464552 14084417 := bstep (se 2 (by rfl) ⟨5281656, by rfl⟩ : syracuseStep 14084417 = 10563313) B10563313
theorem B2197835 : Blo 1464552 2197835 := bstep (se 1 (by rfl) ⟨1648376, by rfl⟩ : syracuseStep 2197835 = 3296753) B3296753
theorem B12519755 : Blo 1464552 12519755 := bstep (se 1 (by rfl) ⟨9389816, by rfl⟩ : syracuseStep 12519755 = 18779633) B18779633
theorem B7924043 : Blo 1464552 7924043 := bstep (se 1 (by rfl) ⟨5943032, by rfl⟩ : syracuseStep 7924043 = 11886065) B11886065
theorem B2197847 : Blo 1464552 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B2410841 : Blo 1464552 2410841 := bstep (se 2 (by rfl) ⟨904065, by rfl⟩ : syracuseStep 2410841 = 1808131) B1808131
theorem B3131777 : Blo 1464552 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B1649047 : Blo 1464552 1649047 := bstep (se 1 (by rfl) ⟨1236785, by rfl⟩ : syracuseStep 1649047 = 2473571) B2473571
theorem B2197913 : Blo 1464552 2197913 := bstep (se 2 (by rfl) ⟨824217, by rfl⟩ : syracuseStep 2197913 = 1648435) B1648435
theorem B6343105 : Blo 1464552 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B3295691 : Blo 1464552 3295691 := bstep (se 1 (by rfl) ⟨2471768, by rfl⟩ : syracuseStep 3295691 = 4943537) B4943537
theorem B4172249 : Blo 1464552 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B4696537 : Blo 1464552 4696537 := bstep (se 2 (by rfl) ⟨1761201, by rfl⟩ : syracuseStep 4696537 = 3522403) B3522403
theorem B3295745 : Blo 1464552 3295745 := bstep (se 2 (by rfl) ⟨1235904, by rfl⟩ : syracuseStep 3295745 = 2471809) B2471809
theorem B2198027 : Blo 1464552 2198027 := bstep (se 1 (by rfl) ⟨1648520, by rfl⟩ : syracuseStep 2198027 = 3297041) B3297041
theorem B2198039 : Blo 1464552 2198039 := bstep (se 1 (by rfl) ⟨1648529, by rfl⟩ : syracuseStep 2198039 = 3297059) B3297059
theorem B6261313 : Blo 1464552 6261313 := bstep (se 2 (by rfl) ⟨2347992, by rfl⟩ : syracuseStep 6261313 = 4695985) B4695985
theorem B1649227 : Blo 1464552 1649227 := bstep (se 1 (by rfl) ⟨1236920, by rfl⟩ : syracuseStep 1649227 = 2473841) B2473841
theorem B4696651 : Blo 1464552 4696651 := bstep (se 1 (by rfl) ⟨3522488, by rfl⟩ : syracuseStep 4696651 = 7044977) B7044977
theorem B2198105 : Blo 1464552 2198105 := bstep (se 2 (by rfl) ⟨824289, by rfl⟩ : syracuseStep 2198105 = 1648579) B1648579
theorem B12528229 : Blo 1464552 12528229 := bstep (se 4 (by rfl) ⟨1174521, by rfl⟩ : syracuseStep 12528229 = 2349043) B2349043
theorem B10029719 : Blo 1464552 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B1649335 : Blo 1464552 1649335 := bstep (se 1 (by rfl) ⟨1237001, by rfl⟩ : syracuseStep 1649335 = 2474003) B2474003
theorem B48204485 : Blo 1464552 48204485 := bstep (se 4 (by rfl) ⟨4519170, by rfl⟩ : syracuseStep 48204485 = 9038341) B9038341
theorem B2198219 : Blo 1464552 2198219 := bstep (se 1 (by rfl) ⟨1648664, by rfl⟩ : syracuseStep 2198219 = 3297329) B3297329
theorem B2198231 : Blo 1464552 2198231 := bstep (se 1 (by rfl) ⟨1648673, by rfl⟩ : syracuseStep 2198231 = 3297347) B3297347
theorem B3295961 : Blo 1464552 3295961 := bstep (se 2 (by rfl) ⟨1235985, by rfl⟩ : syracuseStep 3295961 = 2471971) B2471971
theorem B2198297 : Blo 1464552 2198297 := bstep (se 2 (by rfl) ⟨824361, by rfl⟩ : syracuseStep 2198297 = 1648723) B1648723
theorem B3296051 : Blo 1464552 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B3296087 : Blo 1464552 3296087 := bstep (se 1 (by rfl) ⟨2472065, by rfl⟩ : syracuseStep 3296087 = 4944131) B4944131
theorem B1649515 : Blo 1464552 1649515 := bstep (se 1 (by rfl) ⟨1237136, by rfl⟩ : syracuseStep 1649515 = 2474273) B2474273
theorem B2198411 : Blo 1464552 2198411 := bstep (se 1 (by rfl) ⟨1648808, by rfl⟩ : syracuseStep 2198411 = 3297617) B3297617
theorem B2198423 : Blo 1464552 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B1649623 : Blo 1464552 1649623 := bstep (se 1 (by rfl) ⟨1237217, by rfl⟩ : syracuseStep 1649623 = 2474435) B2474435
theorem B2198489 : Blo 1464552 2198489 := bstep (se 2 (by rfl) ⟨824433, by rfl⟩ : syracuseStep 2198489 = 1648867) B1648867
theorem B3296267 : Blo 1464552 3296267 := bstep (se 1 (by rfl) ⟨2472200, by rfl⟩ : syracuseStep 3296267 = 4944401) B4944401
theorem B3296321 : Blo 1464552 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B4697153 : Blo 1464552 4697153 := bstep (se 2 (by rfl) ⟨1761432, by rfl⟩ : syracuseStep 4697153 = 3522865) B3522865
theorem B32107589 : Blo 1464552 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B2198603 : Blo 1464552 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2198615 : Blo 1464552 2198615 := bstep (se 1 (by rfl) ⟨1648961, by rfl⟩ : syracuseStep 2198615 = 3297923) B3297923
theorem B1649803 : Blo 1464552 1649803 := bstep (se 1 (by rfl) ⟨1237352, by rfl⟩ : syracuseStep 1649803 = 2474705) B2474705
theorem B2198681 : Blo 1464552 2198681 := bstep (se 2 (by rfl) ⟨824505, by rfl⟩ : syracuseStep 2198681 = 1649011) B1649011
theorem B4943051 : Blo 1464552 4943051 := bstep (se 1 (by rfl) ⟨3707288, by rfl⟩ : syracuseStep 4943051 = 7414577) B7414577
theorem B1854667 : Blo 1464552 1854667 := bstep (se 1 (by rfl) ⟨1391000, by rfl⟩ : syracuseStep 1854667 = 2782001) B2782001
theorem B2198795 : Blo 1464552 2198795 := bstep (se 1 (by rfl) ⟨1649096, by rfl⟩ : syracuseStep 2198795 = 3298193) B3298193
theorem B2641175 : Blo 1464552 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B2198807 : Blo 1464552 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B3296537 : Blo 1464552 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B4345177 : Blo 1464552 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B2198873 : Blo 1464552 2198873 := bstep (se 2 (by rfl) ⟨824577, by rfl⟩ : syracuseStep 2198873 = 1649155) B1649155
theorem B3296627 : Blo 1464552 3296627 := bstep (se 1 (by rfl) ⟨2472470, by rfl⟩ : syracuseStep 3296627 = 4944941) B4944941
theorem B3296663 : Blo 1464552 3296663 := bstep (se 1 (by rfl) ⟨2472497, by rfl⟩ : syracuseStep 3296663 = 4944995) B4944995
theorem B2198987 : Blo 1464552 2198987 := bstep (se 1 (by rfl) ⟨1649240, by rfl⟩ : syracuseStep 2198987 = 3298481) B3298481
theorem B12512717 : Blo 1464552 12512717 := bstep (se 3 (by rfl) ⟨2346134, by rfl⟩ : syracuseStep 12512717 = 4692269) B4692269
theorem B2346455 : Blo 1464552 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B2198999 : Blo 1464552 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B4943321 : Blo 1464552 4943321 := bstep (se 2 (by rfl) ⟨1853745, by rfl⟩ : syracuseStep 4943321 = 3707491) B3707491
theorem B2199065 : Blo 1464552 2199065 := bstep (se 2 (by rfl) ⟨824649, by rfl⟩ : syracuseStep 2199065 = 1649299) B1649299
theorem B3296843 : Blo 1464552 3296843 := bstep (se 1 (by rfl) ⟨2472632, by rfl⟩ : syracuseStep 3296843 = 4945265) B4945265
theorem B8351333 : Blo 1464552 8351333 := bstep (se 4 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 8351333 = 1565875) B1565875
theorem B2780801 : Blo 1464552 2780801 := bstep (se 2 (by rfl) ⟨1042800, by rfl⟩ : syracuseStep 2780801 = 2085601) B2085601
theorem B3296897 : Blo 1464552 3296897 := bstep (se 2 (by rfl) ⟨1236336, by rfl⟩ : syracuseStep 3296897 = 2472673) B2472673
theorem B2199179 : Blo 1464552 2199179 := bstep (se 1 (by rfl) ⟨1649384, by rfl⟩ : syracuseStep 2199179 = 3298769) B3298769
theorem B5566097 : Blo 1464552 5566097 := bstep (se 2 (by rfl) ⟨2087286, by rfl⟩ : syracuseStep 5566097 = 4174573) B4174573
theorem B2199191 : Blo 1464552 2199191 := bstep (se 1 (by rfl) ⟨1649393, by rfl⟩ : syracuseStep 2199191 = 3298787) B3298787
theorem B4697779 : Blo 1464552 4697779 := bstep (se 1 (by rfl) ⟨3523334, by rfl⟩ : syracuseStep 4697779 = 7046669) B7046669
theorem B4173515 : Blo 1464552 4173515 := bstep (se 1 (by rfl) ⟨3130136, by rfl⟩ : syracuseStep 4173515 = 6260273) B6260273
theorem B2199257 : Blo 1464552 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B2199371 : Blo 1464552 2199371 := bstep (se 1 (by rfl) ⟨1649528, by rfl⟩ : syracuseStep 2199371 = 3299057) B3299057
theorem B2199383 : Blo 1464552 2199383 := bstep (se 1 (by rfl) ⟨1649537, by rfl⟩ : syracuseStep 2199383 = 3299075) B3299075
theorem B3297113 : Blo 1464552 3297113 := bstep (se 2 (by rfl) ⟨1236417, by rfl⟩ : syracuseStep 3297113 = 2472835) B2472835
theorem B2781067 : Blo 1464552 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B2199449 : Blo 1464552 2199449 := bstep (se 2 (by rfl) ⟨824793, by rfl⟩ : syracuseStep 2199449 = 1649587) B1649587
theorem B3297203 : Blo 1464552 3297203 := bstep (se 1 (by rfl) ⟨2472902, by rfl⟩ : syracuseStep 3297203 = 4945805) B4945805
theorem B3215297 : Blo 1464552 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B3297239 : Blo 1464552 3297239 := bstep (se 1 (by rfl) ⟨2472929, by rfl⟩ : syracuseStep 3297239 = 4945859) B4945859
theorem B7417817 : Blo 1464552 7417817 := bstep (se 2 (by rfl) ⟨2781681, by rfl⟩ : syracuseStep 7417817 = 5563363) B5563363
theorem B2199563 : Blo 1464552 2199563 := bstep (se 1 (by rfl) ⟨1649672, by rfl⟩ : syracuseStep 2199563 = 3299345) B3299345
theorem B2199575 : Blo 1464552 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B23760971 : Blo 1464552 23760971 := bstep (se 1 (by rfl) ⟨17820728, by rfl⟩ : syracuseStep 23760971 = 35641457) B35641457
theorem B5566553 : Blo 1464552 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B2199641 : Blo 1464552 2199641 := bstep (se 2 (by rfl) ⟨824865, by rfl⟩ : syracuseStep 2199641 = 1649731) B1649731
theorem B2347147 : Blo 1464552 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B3297419 : Blo 1464552 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B4944023 : Blo 1464552 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B6025367 : Blo 1464552 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B1855639 : Blo 1464552 1855639 := bstep (se 1 (by rfl) ⟨1391729, by rfl⟩ : syracuseStep 1855639 = 2783459) B2783459
theorem B3297473 : Blo 1464552 3297473 := bstep (se 2 (by rfl) ⟨1236552, by rfl⟩ : syracuseStep 3297473 = 2473105) B2473105
theorem B2199755 : Blo 1464552 2199755 := bstep (se 1 (by rfl) ⟨1649816, by rfl⟩ : syracuseStep 2199755 = 3299633) B3299633
theorem B2199767 : Blo 1464552 2199767 := bstep (se 1 (by rfl) ⟨1649825, by rfl⟩ : syracuseStep 2199767 = 3299651) B3299651
theorem B8343769 : Blo 1464552 8343769 := bstep (se 2 (by rfl) ⟨3128913, by rfl⟩ : syracuseStep 8343769 = 6257827) B6257827
theorem B8352017 : Blo 1464552 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B5566765 : Blo 1464552 5566765 := bstep (se 3 (by rfl) ⟨1043768, by rfl⟩ : syracuseStep 5566765 = 2087537) B2087537
theorem B10170689 : Blo 1464552 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B2781515 : Blo 1464552 2781515 := bstep (se 1 (by rfl) ⟨2086136, by rfl⟩ : syracuseStep 2781515 = 4172273) B4172273
theorem B3297689 : Blo 1464552 3297689 := bstep (se 2 (by rfl) ⟨1236633, by rfl⟩ : syracuseStep 3297689 = 2473267) B2473267
theorem B3707329 : Blo 1464552 3707329 := bstep (se 2 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 3707329 = 2780497) B2780497
theorem B1675723 : Blo 1464552 1675723 := bstep (se 1 (by rfl) ⟨1256792, by rfl⟩ : syracuseStep 1675723 = 2513585) B2513585
theorem B3297779 : Blo 1464552 3297779 := bstep (se 1 (by rfl) ⟨2473334, by rfl⟩ : syracuseStep 3297779 = 4946669) B4946669
theorem B2781697 : Blo 1464552 2781697 := bstep (se 2 (by rfl) ⟨1043136, by rfl⟩ : syracuseStep 2781697 = 2086273) B2086273
theorem B3297815 : Blo 1464552 3297815 := bstep (se 1 (by rfl) ⟨2473361, by rfl⟩ : syracuseStep 3297815 = 4946723) B4946723
theorem B5567069 : Blo 1464552 5567069 := bstep (se 3 (by rfl) ⟨1043825, by rfl⟩ : syracuseStep 5567069 = 2087651) B2087651
theorem B2085527 : Blo 1464552 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B3568279 : Blo 1464552 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B4944563 : Blo 1464552 4944563 := bstep (se 1 (by rfl) ⟨3708422, by rfl⟩ : syracuseStep 4944563 = 7416845) B7416845
theorem B3297995 : Blo 1464552 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B3298049 : Blo 1464552 3298049 := bstep (se 2 (by rfl) ⟨1236768, by rfl⟩ : syracuseStep 3298049 = 2473537) B2473537
theorem B2782039 : Blo 1464552 2782039 := bstep (se 1 (by rfl) ⟨2086529, by rfl⟩ : syracuseStep 2782039 = 4173059) B4173059
theorem B16683893 : Blo 1464552 16683893 := bstep (se 5 (by rfl) ⟨782057, by rfl⟩ : syracuseStep 16683893 = 1564115) B1564115
theorem B4944833 : Blo 1464552 4944833 := bstep (se 2 (by rfl) ⟨1854312, by rfl⟩ : syracuseStep 4944833 = 3708625) B3708625
theorem B3298265 : Blo 1464552 3298265 := bstep (se 2 (by rfl) ⟨1236849, by rfl⟩ : syracuseStep 3298265 = 2473699) B2473699
theorem B3707927 : Blo 1464552 3707927 := bstep (se 1 (by rfl) ⟨2780945, by rfl⟩ : syracuseStep 3707927 = 5561891) B5561891
theorem B25392163 : Blo 1464552 25392163 := bstep (se 1 (by rfl) ⟨19044122, by rfl⟩ : syracuseStep 25392163 = 38088245) B38088245
theorem B2782259 : Blo 1464552 2782259 := bstep (se 1 (by rfl) ⟨2086694, by rfl⟩ : syracuseStep 2782259 = 4173389) B4173389
theorem B3298355 : Blo 1464552 3298355 := bstep (se 1 (by rfl) ⟨2473766, by rfl⟩ : syracuseStep 3298355 = 4947533) B4947533
theorem B53507141 : Blo 1464552 53507141 := bstep (se 4 (by rfl) ⟨5016294, by rfl⟩ : syracuseStep 53507141 = 10032589) B10032589
theorem B3298391 : Blo 1464552 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B8344727 : Blo 1464552 8344727 := bstep (se 1 (by rfl) ⟨6258545, by rfl⟩ : syracuseStep 8344727 = 12517091) B12517091
theorem B2348185 : Blo 1464552 2348185 := bstep (se 2 (by rfl) ⟨880569, by rfl⟩ : syracuseStep 2348185 = 1761139) B1761139
theorem B3298571 : Blo 1464552 3298571 := bstep (se 1 (by rfl) ⟨2473928, by rfl⟩ : syracuseStep 3298571 = 4947857) B4947857
theorem B2782487 : Blo 1464552 2782487 := bstep (se 1 (by rfl) ⟨2086865, by rfl⟩ : syracuseStep 2782487 = 4173731) B4173731
theorem B3298625 : Blo 1464552 3298625 := bstep (se 2 (by rfl) ⟨1236984, by rfl⟩ : syracuseStep 3298625 = 2473969) B2473969
theorem B1979735 : Blo 1464552 1979735 := bstep (se 1 (by rfl) ⟨1484801, by rfl⟩ : syracuseStep 1979735 = 2969603) B2969603
theorem B4945373 : Blo 1464552 4945373 := bstep (se 3 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 4945373 = 1854515) B1854515
theorem B2782745 : Blo 1464552 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B3298841 : Blo 1464552 3298841 := bstep (se 2 (by rfl) ⟨1237065, by rfl⟩ : syracuseStep 3298841 = 2474131) B2474131
theorem B7419437 : Blo 1464552 7419437 := bstep (se 3 (by rfl) ⟨1391144, by rfl⟩ : syracuseStep 7419437 = 2782289) B2782289
theorem B2086489 : Blo 1464552 2086489 := bstep (se 2 (by rfl) ⟨782433, by rfl⟩ : syracuseStep 2086489 = 1564867) B1564867
theorem B2348633 : Blo 1464552 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B3298931 : Blo 1464552 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B3298967 : Blo 1464552 3298967 := bstep (se 1 (by rfl) ⟨2474225, by rfl⟩ : syracuseStep 3298967 = 4948451) B4948451
theorem B2471627 : Blo 1464552 2471627 := bstep (se 1 (by rfl) ⟨1853720, by rfl⟩ : syracuseStep 2471627 = 3707441) B3707441
theorem B12515107 : Blo 1464552 12515107 := bstep (se 1 (by rfl) ⟨9386330, by rfl⟩ : syracuseStep 12515107 = 18772661) B18772661
theorem B3708737 : Blo 1464552 3708737 := bstep (se 2 (by rfl) ⟨1390776, by rfl⟩ : syracuseStep 3708737 = 2781553) B2781553
theorem B2471755 : Blo 1464552 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B3299147 : Blo 1464552 3299147 := bstep (se 1 (by rfl) ⟨2474360, by rfl⟩ : syracuseStep 3299147 = 4948721) B4948721
theorem B3299201 : Blo 1464552 3299201 := bstep (se 2 (by rfl) ⟨1237200, by rfl⟩ : syracuseStep 3299201 = 2474401) B2474401
theorem B2783155 : Blo 1464552 2783155 := bstep (se 1 (by rfl) ⟨2087366, by rfl⟩ : syracuseStep 2783155 = 4174733) B4174733
theorem B2471897 : Blo 1464552 2471897 := bstep (se 2 (by rfl) ⟨926961, by rfl⟩ : syracuseStep 2471897 = 1853923) B1853923
theorem B7919633 : Blo 1464552 7919633 := bstep (se 2 (by rfl) ⟨2969862, by rfl⟩ : syracuseStep 7919633 = 5939725) B5939725
theorem B2472025 : Blo 1464552 2472025 := bstep (se 2 (by rfl) ⟨927009, by rfl⟩ : syracuseStep 2472025 = 1854019) B1854019
theorem B3299417 : Blo 1464552 3299417 := bstep (se 2 (by rfl) ⟨1237281, by rfl⟩ : syracuseStep 3299417 = 2474563) B2474563
theorem B11884637 : Blo 1464552 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B3340403 : Blo 1464552 3340403 := bstep (se 1 (by rfl) ⟨2505302, by rfl⟩ : syracuseStep 3340403 = 5010605) B5010605
theorem B3299507 : Blo 1464552 3299507 := bstep (se 1 (by rfl) ⟨2474630, by rfl⟩ : syracuseStep 3299507 = 4949261) B4949261
theorem B3299543 : Blo 1464552 3299543 := bstep (se 1 (by rfl) ⟨2474657, by rfl⟩ : syracuseStep 3299543 = 4949315) B4949315
theorem B1464555 : Blo 1464552 1464555 := bstep (se 1 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 1464555 = 2196833) B2196833
theorem B1464567 : Blo 1464552 1464567 := bstep (se 1 (by rfl) ⟨1098425, by rfl⟩ : syracuseStep 1464567 = 2196851) B2196851
theorem B1464587 : Blo 1464552 1464587 := bstep (se 1 (by rfl) ⟨1098440, by rfl⟩ : syracuseStep 1464587 = 2196881) B2196881
theorem B1464599 : Blo 1464552 1464599 := bstep (se 1 (by rfl) ⟨1098449, by rfl⟩ : syracuseStep 1464599 = 2196899) B2196899
theorem B1464619 : Blo 1464552 1464619 := bstep (se 1 (by rfl) ⟨1098464, by rfl⟩ : syracuseStep 1464619 = 2196929) B2196929
theorem B1464631 : Blo 1464552 1464631 := bstep (se 1 (by rfl) ⟨1098473, by rfl⟩ : syracuseStep 1464631 = 2196947) B2196947
theorem B1464651 : Blo 1464552 1464651 := bstep (se 1 (by rfl) ⟨1098488, by rfl⟩ : syracuseStep 1464651 = 2196977) B2196977
theorem B11008331 : Blo 1464552 11008331 := bstep (se 1 (by rfl) ⟨8256248, by rfl⟩ : syracuseStep 11008331 = 16512497) B16512497
theorem B1464663 : Blo 1464552 1464663 := bstep (se 1 (by rfl) ⟨1098497, by rfl⟩ : syracuseStep 1464663 = 2196995) B2196995
theorem B3709273 : Blo 1464552 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B1464683 : Blo 1464552 1464683 := bstep (se 1 (by rfl) ⟨1098512, by rfl⟩ : syracuseStep 1464683 = 2197025) B2197025
theorem B1464695 : Blo 1464552 1464695 := bstep (se 1 (by rfl) ⟨1098521, by rfl⟩ : syracuseStep 1464695 = 2197043) B2197043
theorem B1464715 : Blo 1464552 1464715 := bstep (se 1 (by rfl) ⟨1098536, by rfl⟩ : syracuseStep 1464715 = 2197073) B2197073
theorem B3299723 : Blo 1464552 3299723 := bstep (se 1 (by rfl) ⟨2474792, by rfl⟩ : syracuseStep 3299723 = 4949585) B4949585
theorem B1464727 : Blo 1464552 1464727 := bstep (se 1 (by rfl) ⟨1098545, by rfl⟩ : syracuseStep 1464727 = 2197091) B2197091
theorem B2783641 : Blo 1464552 2783641 := bstep (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) B2087731
theorem B1464747 : Blo 1464552 1464747 := bstep (se 1 (by rfl) ⟨1098560, by rfl⟩ : syracuseStep 1464747 = 2197121) B2197121
theorem B1464759 : Blo 1464552 1464759 := bstep (se 1 (by rfl) ⟨1098569, by rfl⟩ : syracuseStep 1464759 = 2197139) B2197139
theorem B1464779 : Blo 1464552 1464779 := bstep (se 1 (by rfl) ⟨1098584, by rfl⟩ : syracuseStep 1464779 = 2197169) B2197169
theorem B1464791 : Blo 1464552 1464791 := bstep (se 1 (by rfl) ⟨1098593, by rfl⟩ : syracuseStep 1464791 = 2197187) B2197187
theorem B1464811 : Blo 1464552 1464811 := bstep (se 1 (by rfl) ⟨1098608, by rfl⟩ : syracuseStep 1464811 = 2197217) B2197217
theorem B1464823 : Blo 1464552 1464823 := bstep (se 1 (by rfl) ⟨1098617, by rfl⟩ : syracuseStep 1464823 = 2197235) B2197235
theorem B1464843 : Blo 1464552 1464843 := bstep (se 1 (by rfl) ⟨1098632, by rfl⟩ : syracuseStep 1464843 = 2197265) B2197265
theorem B9386513 : Blo 1464552 9386513 := bstep (se 2 (by rfl) ⟨3519942, by rfl⟩ : syracuseStep 9386513 = 7039885) B7039885
theorem B1464855 : Blo 1464552 1464855 := bstep (se 1 (by rfl) ⟨1098641, by rfl⟩ : syracuseStep 1464855 = 2197283) B2197283
theorem B1464875 : Blo 1464552 1464875 := bstep (se 1 (by rfl) ⟨1098656, by rfl⟩ : syracuseStep 1464875 = 2197313) B2197313
theorem B1464887 : Blo 1464552 1464887 := bstep (se 1 (by rfl) ⟨1098665, by rfl⟩ : syracuseStep 1464887 = 2197331) B2197331
theorem B1464907 : Blo 1464552 1464907 := bstep (se 1 (by rfl) ⟨1098680, by rfl⟩ : syracuseStep 1464907 = 2197361) B2197361
theorem B4946507 : Blo 1464552 4946507 := bstep (se 1 (by rfl) ⟨3709880, by rfl⟩ : syracuseStep 4946507 = 7419761) B7419761
theorem B1464919 : Blo 1464552 1464919 := bstep (se 1 (by rfl) ⟨1098689, by rfl⟩ : syracuseStep 1464919 = 2197379) B2197379
theorem B48200285 : Blo 1464552 48200285 := bstep (se 3 (by rfl) ⟨9037553, by rfl⟩ : syracuseStep 48200285 = 18075107) B18075107
theorem B1464939 : Blo 1464552 1464939 := bstep (se 1 (by rfl) ⟨1098704, by rfl⟩ : syracuseStep 1464939 = 2197409) B2197409
theorem B1464951 : Blo 1464552 1464951 := bstep (se 1 (by rfl) ⟨1098713, by rfl⟩ : syracuseStep 1464951 = 2197427) B2197427
theorem B1464971 : Blo 1464552 1464971 := bstep (se 1 (by rfl) ⟨1098728, by rfl⟩ : syracuseStep 1464971 = 2197457) B2197457
theorem B1464983 : Blo 1464552 1464983 := bstep (se 1 (by rfl) ⟨1098737, by rfl⟩ : syracuseStep 1464983 = 2197475) B2197475
theorem B2472599 : Blo 1464552 2472599 := bstep (se 1 (by rfl) ⟨1854449, by rfl⟩ : syracuseStep 2472599 = 3708899) B3708899
theorem B1465003 : Blo 1464552 1465003 := bstep (se 1 (by rfl) ⟨1098752, by rfl⟩ : syracuseStep 1465003 = 2197505) B2197505
theorem B1465015 : Blo 1464552 1465015 := bstep (se 1 (by rfl) ⟨1098761, by rfl⟩ : syracuseStep 1465015 = 2197523) B2197523
theorem B1465035 : Blo 1464552 1465035 := bstep (se 1 (by rfl) ⟨1098776, by rfl⟩ : syracuseStep 1465035 = 2197553) B2197553
theorem B1465047 : Blo 1464552 1465047 := bstep (se 1 (by rfl) ⟨1098785, by rfl⟩ : syracuseStep 1465047 = 2197571) B2197571
theorem B13368025 : Blo 1464552 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B1465067 : Blo 1464552 1465067 := bstep (se 1 (by rfl) ⟨1098800, by rfl⟩ : syracuseStep 1465067 = 2197601) B2197601
theorem B1465079 : Blo 1464552 1465079 := bstep (se 1 (by rfl) ⟨1098809, by rfl⟩ : syracuseStep 1465079 = 2197619) B2197619
theorem B1465099 : Blo 1464552 1465099 := bstep (se 1 (by rfl) ⟨1098824, by rfl⟩ : syracuseStep 1465099 = 2197649) B2197649
theorem B1465111 : Blo 1464552 1465111 := bstep (se 1 (by rfl) ⟨1098833, by rfl⟩ : syracuseStep 1465111 = 2197667) B2197667
theorem B2472727 : Blo 1464552 2472727 := bstep (se 1 (by rfl) ⟨1854545, by rfl⟩ : syracuseStep 2472727 = 3709091) B3709091
theorem B2972441 : Blo 1464552 2972441 := bstep (se 2 (by rfl) ⟨1114665, by rfl⟩ : syracuseStep 2972441 = 2229331) B2229331
theorem B1465131 : Blo 1464552 1465131 := bstep (se 1 (by rfl) ⟨1098848, by rfl⟩ : syracuseStep 1465131 = 2197697) B2197697
theorem B1465143 : Blo 1464552 1465143 := bstep (se 1 (by rfl) ⟨1098857, by rfl⟩ : syracuseStep 1465143 = 2197715) B2197715
theorem B1465163 : Blo 1464552 1465163 := bstep (se 1 (by rfl) ⟨1098872, by rfl⟩ : syracuseStep 1465163 = 2197745) B2197745
theorem B1760087 : Blo 1464552 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B1465175 : Blo 1464552 1465175 := bstep (se 1 (by rfl) ⟨1098881, by rfl⟩ : syracuseStep 1465175 = 2197763) B2197763
theorem B4946777 : Blo 1464552 4946777 := bstep (se 2 (by rfl) ⟨1855041, by rfl⟩ : syracuseStep 4946777 = 3710083) B3710083
theorem B1465195 : Blo 1464552 1465195 := bstep (se 1 (by rfl) ⟨1098896, by rfl⟩ : syracuseStep 1465195 = 2197793) B2197793
theorem B1465207 : Blo 1464552 1465207 := bstep (se 1 (by rfl) ⟨1098905, by rfl⟩ : syracuseStep 1465207 = 2197811) B2197811
theorem B1465227 : Blo 1464552 1465227 := bstep (se 1 (by rfl) ⟨1098920, by rfl⟩ : syracuseStep 1465227 = 2197841) B2197841
theorem B2972555 : Blo 1464552 2972555 := bstep (se 1 (by rfl) ⟨2229416, by rfl⟩ : syracuseStep 2972555 = 4458833) B4458833
theorem B1465239 : Blo 1464552 1465239 := bstep (se 1 (by rfl) ⟨1098929, by rfl⟩ : syracuseStep 1465239 = 2197859) B2197859
theorem B1465259 : Blo 1464552 1465259 := bstep (se 1 (by rfl) ⟨1098944, by rfl⟩ : syracuseStep 1465259 = 2197889) B2197889
theorem B19037105 : Blo 1464552 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1465271 : Blo 1464552 1465271 := bstep (se 1 (by rfl) ⟨1098953, by rfl⟩ : syracuseStep 1465271 = 2197907) B2197907
theorem B3759041 : Blo 1464552 3759041 := bstep (se 2 (by rfl) ⟨1409640, by rfl⟩ : syracuseStep 3759041 = 2819281) B2819281
theorem B1465291 : Blo 1464552 1465291 := bstep (se 1 (by rfl) ⟨1098968, by rfl⟩ : syracuseStep 1465291 = 2197937) B2197937
theorem B1465303 : Blo 1464552 1465303 := bstep (se 1 (by rfl) ⟨1098977, by rfl⟩ : syracuseStep 1465303 = 2197955) B2197955
theorem B1465323 : Blo 1464552 1465323 := bstep (se 1 (by rfl) ⟨1098992, by rfl⟩ : syracuseStep 1465323 = 2197985) B2197985
theorem B1465335 : Blo 1464552 1465335 := bstep (se 1 (by rfl) ⟨1099001, by rfl⟩ : syracuseStep 1465335 = 2198003) B2198003
theorem B1465355 : Blo 1464552 1465355 := bstep (se 1 (by rfl) ⟨1099016, by rfl⟩ : syracuseStep 1465355 = 2198033) B2198033
theorem B2087947 : Blo 1464552 2087947 := bstep (se 1 (by rfl) ⟨1565960, by rfl⟩ : syracuseStep 2087947 = 3131921) B3131921
theorem B1465367 : Blo 1464552 1465367 := bstep (se 1 (by rfl) ⟨1099025, by rfl⟩ : syracuseStep 1465367 = 2198051) B2198051
theorem B2087959 : Blo 1464552 2087959 := bstep (se 1 (by rfl) ⟨1565969, by rfl⟩ : syracuseStep 2087959 = 3131939) B3131939
theorem B1465387 : Blo 1464552 1465387 := bstep (se 1 (by rfl) ⟨1099040, by rfl⟩ : syracuseStep 1465387 = 2198081) B2198081
theorem B1465399 : Blo 1464552 1465399 := bstep (se 1 (by rfl) ⟨1099049, by rfl⟩ : syracuseStep 1465399 = 2198099) B2198099
theorem B5561419 : Blo 1464552 5561419 := bstep (se 1 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 5561419 = 8342129) B8342129
theorem B1465419 : Blo 1464552 1465419 := bstep (se 1 (by rfl) ⟨1099064, by rfl⟩ : syracuseStep 1465419 = 2198129) B2198129
theorem B1465431 : Blo 1464552 1465431 := bstep (se 1 (by rfl) ⟨1099073, by rfl⟩ : syracuseStep 1465431 = 2198147) B2198147
theorem B1465451 : Blo 1464552 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B1465463 : Blo 1464552 1465463 := bstep (se 1 (by rfl) ⟨1099097, by rfl⟩ : syracuseStep 1465463 = 2198195) B2198195
theorem B1760395 : Blo 1464552 1760395 := bstep (se 1 (by rfl) ⟨1320296, by rfl⟩ : syracuseStep 1760395 = 2640593) B2640593
theorem B1465483 : Blo 1464552 1465483 := bstep (se 1 (by rfl) ⟨1099112, by rfl⟩ : syracuseStep 1465483 = 2198225) B2198225
theorem B1465495 : Blo 1464552 1465495 := bstep (se 1 (by rfl) ⟨1099121, by rfl⟩ : syracuseStep 1465495 = 2198243) B2198243
theorem B1465515 : Blo 1464552 1465515 := bstep (se 1 (by rfl) ⟨1099136, by rfl⟩ : syracuseStep 1465515 = 2198273) B2198273
theorem B1465527 : Blo 1464552 1465527 := bstep (se 1 (by rfl) ⟨1099145, by rfl⟩ : syracuseStep 1465527 = 2198291) B2198291
theorem B3964097 : Blo 1464552 3964097 := bstep (se 2 (by rfl) ⟨1486536, by rfl⟩ : syracuseStep 3964097 = 2973073) B2973073
theorem B1465547 : Blo 1464552 1465547 := bstep (se 1 (by rfl) ⟨1099160, by rfl⟩ : syracuseStep 1465547 = 2198321) B2198321
theorem B1465559 : Blo 1464552 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B1465579 : Blo 1464552 1465579 := bstep (se 1 (by rfl) ⟨1099184, by rfl⟩ : syracuseStep 1465579 = 2198369) B2198369
theorem B1465591 : Blo 1464552 1465591 := bstep (se 1 (by rfl) ⟨1099193, by rfl⟩ : syracuseStep 1465591 = 2198387) B2198387
theorem B1465611 : Blo 1464552 1465611 := bstep (se 1 (by rfl) ⟨1099208, by rfl⟩ : syracuseStep 1465611 = 2198417) B2198417
theorem B1465623 : Blo 1464552 1465623 := bstep (se 1 (by rfl) ⟨1099217, by rfl⟩ : syracuseStep 1465623 = 2198435) B2198435
theorem B1465643 : Blo 1464552 1465643 := bstep (se 1 (by rfl) ⟨1099232, by rfl⟩ : syracuseStep 1465643 = 2198465) B2198465
theorem B1465655 : Blo 1464552 1465655 := bstep (se 1 (by rfl) ⟨1099241, by rfl⟩ : syracuseStep 1465655 = 2198483) B2198483
theorem B1465675 : Blo 1464552 1465675 := bstep (se 1 (by rfl) ⟨1099256, by rfl⟩ : syracuseStep 1465675 = 2198513) B2198513
theorem B2227543 : Blo 1464552 2227543 := bstep (se 1 (by rfl) ⟨1670657, by rfl⟩ : syracuseStep 2227543 = 3341315) B3341315
theorem B1465687 : Blo 1464552 1465687 := bstep (se 1 (by rfl) ⟨1099265, by rfl⟩ : syracuseStep 1465687 = 2198531) B2198531
theorem B5938525 : Blo 1464552 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B5561693 : Blo 1464552 5561693 := bstep (se 3 (by rfl) ⟨1042817, by rfl⟩ : syracuseStep 5561693 = 2085635) B2085635
theorem B15850853 : Blo 1464552 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B1465707 : Blo 1464552 1465707 := bstep (se 1 (by rfl) ⟨1099280, by rfl⟩ : syracuseStep 1465707 = 2198561) B2198561
theorem B1465719 : Blo 1464552 1465719 := bstep (se 1 (by rfl) ⟨1099289, by rfl⟩ : syracuseStep 1465719 = 2198579) B2198579
theorem B2506123 : Blo 1464552 2506123 := bstep (se 1 (by rfl) ⟨1879592, by rfl⟩ : syracuseStep 2506123 = 3759185) B3759185
theorem B2473355 : Blo 1464552 2473355 := bstep (se 1 (by rfl) ⟨1855016, by rfl⟩ : syracuseStep 2473355 = 3710033) B3710033
theorem B1465739 : Blo 1464552 1465739 := bstep (se 1 (by rfl) ⟨1099304, by rfl⟩ : syracuseStep 1465739 = 2198609) B2198609
theorem B1465751 : Blo 1464552 1465751 := bstep (se 1 (by rfl) ⟨1099313, by rfl⟩ : syracuseStep 1465751 = 2198627) B2198627
theorem B1465771 : Blo 1464552 1465771 := bstep (se 1 (by rfl) ⟨1099328, by rfl⟩ : syracuseStep 1465771 = 2198657) B2198657
theorem B16924081 : Blo 1464552 16924081 := bstep (se 2 (by rfl) ⟨6346530, by rfl⟩ : syracuseStep 16924081 = 12693061) B12693061
theorem B3710387 : Blo 1464552 3710387 := bstep (se 1 (by rfl) ⟨2782790, by rfl⟩ : syracuseStep 3710387 = 5565581) B5565581
theorem B5430707 : Blo 1464552 5430707 := bstep (se 1 (by rfl) ⟨4073030, by rfl⟩ : syracuseStep 5430707 = 8146061) B8146061
theorem B1465783 : Blo 1464552 1465783 := bstep (se 1 (by rfl) ⟨1099337, by rfl⟩ : syracuseStep 1465783 = 2198675) B2198675
theorem B1465803 : Blo 1464552 1465803 := bstep (se 1 (by rfl) ⟨1099352, by rfl⟩ : syracuseStep 1465803 = 2198705) B2198705
theorem B1465815 : Blo 1464552 1465815 := bstep (se 1 (by rfl) ⟨1099361, by rfl⟩ : syracuseStep 1465815 = 2198723) B2198723
theorem B1465835 : Blo 1464552 1465835 := bstep (se 1 (by rfl) ⟨1099376, by rfl⟩ : syracuseStep 1465835 = 2198753) B2198753
theorem B1465847 : Blo 1464552 1465847 := bstep (se 1 (by rfl) ⟨1099385, by rfl⟩ : syracuseStep 1465847 = 2198771) B2198771
theorem B2473483 : Blo 1464552 2473483 := bstep (se 1 (by rfl) ⟨1855112, by rfl⟩ : syracuseStep 2473483 = 3710225) B3710225
theorem B1465867 : Blo 1464552 1465867 := bstep (se 1 (by rfl) ⟨1099400, by rfl⟩ : syracuseStep 1465867 = 2198801) B2198801
theorem B1465879 : Blo 1464552 1465879 := bstep (se 1 (by rfl) ⟨1099409, by rfl⟩ : syracuseStep 1465879 = 2198819) B2198819
theorem B4947479 : Blo 1464552 4947479 := bstep (se 1 (by rfl) ⟨3710609, by rfl⟩ : syracuseStep 4947479 = 7421219) B7421219
theorem B1465899 : Blo 1464552 1465899 := bstep (se 1 (by rfl) ⟨1099424, by rfl⟩ : syracuseStep 1465899 = 2198849) B2198849
theorem B1465911 : Blo 1464552 1465911 := bstep (se 1 (by rfl) ⟨1099433, by rfl⟩ : syracuseStep 1465911 = 2198867) B2198867
theorem B8347211 : Blo 1464552 8347211 := bstep (se 1 (by rfl) ⟨6260408, by rfl⟩ : syracuseStep 8347211 = 12520817) B12520817
theorem B1465931 : Blo 1464552 1465931 := bstep (se 1 (by rfl) ⟨1099448, by rfl⟩ : syracuseStep 1465931 = 2198897) B2198897
theorem B1465943 : Blo 1464552 1465943 := bstep (se 1 (by rfl) ⟨1099457, by rfl⟩ : syracuseStep 1465943 = 2198915) B2198915
theorem B1465963 : Blo 1464552 1465963 := bstep (se 1 (by rfl) ⟨1099472, by rfl⟩ : syracuseStep 1465963 = 2198945) B2198945
theorem B1465975 : Blo 1464552 1465975 := bstep (se 1 (by rfl) ⟨1099481, by rfl⟩ : syracuseStep 1465975 = 2198963) B2198963
theorem B11878019 : Blo 1464552 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B1465995 : Blo 1464552 1465995 := bstep (se 1 (by rfl) ⟨1099496, by rfl⟩ : syracuseStep 1465995 = 2198993) B2198993
theorem B1466007 : Blo 1464552 1466007 := bstep (se 1 (by rfl) ⟨1099505, by rfl⟩ : syracuseStep 1466007 = 2199011) B2199011
theorem B2473625 : Blo 1464552 2473625 := bstep (se 2 (by rfl) ⟨927609, by rfl⟩ : syracuseStep 2473625 = 1855219) B1855219
theorem B1466027 : Blo 1464552 1466027 := bstep (se 1 (by rfl) ⟨1099520, by rfl⟩ : syracuseStep 1466027 = 2199041) B2199041
theorem B1466039 : Blo 1464552 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B1564363 : Blo 1464552 1564363 := bstep (se 1 (by rfl) ⟨1173272, by rfl⟩ : syracuseStep 1564363 = 2346545) B2346545
theorem B1466059 : Blo 1464552 1466059 := bstep (se 1 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 1466059 = 2199089) B2199089
theorem B1466071 : Blo 1464552 1466071 := bstep (se 1 (by rfl) ⟨1099553, by rfl⟩ : syracuseStep 1466071 = 2199107) B2199107
theorem B3759833 : Blo 1464552 3759833 := bstep (se 2 (by rfl) ⟨1409937, by rfl⟩ : syracuseStep 3759833 = 2819875) B2819875
theorem B3710681 : Blo 1464552 3710681 := bstep (se 2 (by rfl) ⟨1391505, by rfl⟩ : syracuseStep 3710681 = 2783011) B2783011
theorem B1466091 : Blo 1464552 1466091 := bstep (se 1 (by rfl) ⟨1099568, by rfl⟩ : syracuseStep 1466091 = 2199137) B2199137
theorem B1466103 : Blo 1464552 1466103 := bstep (se 1 (by rfl) ⟨1099577, by rfl⟩ : syracuseStep 1466103 = 2199155) B2199155
theorem B1466123 : Blo 1464552 1466123 := bstep (se 1 (by rfl) ⟨1099592, by rfl⟩ : syracuseStep 1466123 = 2199185) B2199185
theorem B1466135 : Blo 1464552 1466135 := bstep (se 1 (by rfl) ⟨1099601, by rfl⟩ : syracuseStep 1466135 = 2199203) B2199203
theorem B2473753 : Blo 1464552 2473753 := bstep (se 2 (by rfl) ⟨927657, by rfl⟩ : syracuseStep 2473753 = 1855315) B1855315
theorem B1466155 : Blo 1464552 1466155 := bstep (se 1 (by rfl) ⟨1099616, by rfl⟩ : syracuseStep 1466155 = 2199233) B2199233
theorem B1466167 : Blo 1464552 1466167 := bstep (se 1 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 1466167 = 2199251) B2199251
theorem B1466187 : Blo 1464552 1466187 := bstep (se 1 (by rfl) ⟨1099640, by rfl⟩ : syracuseStep 1466187 = 2199281) B2199281
theorem B1466199 : Blo 1464552 1466199 := bstep (se 1 (by rfl) ⟨1099649, by rfl⟩ : syracuseStep 1466199 = 2199299) B2199299
theorem B1466219 : Blo 1464552 1466219 := bstep (se 1 (by rfl) ⟨1099664, by rfl⟩ : syracuseStep 1466219 = 2199329) B2199329
theorem B1466231 : Blo 1464552 1466231 := bstep (se 1 (by rfl) ⟨1099673, by rfl⟩ : syracuseStep 1466231 = 2199347) B2199347
theorem B10166147 : Blo 1464552 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B1466251 : Blo 1464552 1466251 := bstep (se 1 (by rfl) ⟨1099688, by rfl⟩ : syracuseStep 1466251 = 2199377) B2199377
theorem B1466263 : Blo 1464552 1466263 := bstep (se 1 (by rfl) ⟨1099697, by rfl⟩ : syracuseStep 1466263 = 2199395) B2199395
theorem B1466283 : Blo 1464552 1466283 := bstep (se 1 (by rfl) ⟨1099712, by rfl⟩ : syracuseStep 1466283 = 2199425) B2199425
theorem B1466295 : Blo 1464552 1466295 := bstep (se 1 (by rfl) ⟨1099721, by rfl⟩ : syracuseStep 1466295 = 2199443) B2199443
theorem B1466315 : Blo 1464552 1466315 := bstep (se 1 (by rfl) ⟨1099736, by rfl⟩ : syracuseStep 1466315 = 2199473) B2199473
theorem B1466327 : Blo 1464552 1466327 := bstep (se 1 (by rfl) ⟨1099745, by rfl⟩ : syracuseStep 1466327 = 2199491) B2199491
theorem B1466347 : Blo 1464552 1466347 := bstep (se 1 (by rfl) ⟨1099760, by rfl⟩ : syracuseStep 1466347 = 2199521) B2199521
theorem B1466359 : Blo 1464552 1466359 := bstep (se 1 (by rfl) ⟨1099769, by rfl⟩ : syracuseStep 1466359 = 2199539) B2199539
theorem B1466375 : Blo 1464552 1466375 := bstep (se 1 (by rfl) ⟨1099781, by rfl⟩ : syracuseStep 1466375 = 2199563) B2199563
theorem B1466383 : Blo 1464552 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B3711035 : Blo 1464552 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B1466427 : Blo 1464552 1466427 := bstep (se 1 (by rfl) ⟨1099820, by rfl⟩ : syracuseStep 1466427 = 2199641) B2199641
theorem B1466503 : Blo 1464552 1466503 := bstep (se 1 (by rfl) ⟨1099877, by rfl⟩ : syracuseStep 1466503 = 2199755) B2199755
theorem B1466511 : Blo 1464552 1466511 := bstep (se 1 (by rfl) ⟨1099883, by rfl⟩ : syracuseStep 1466511 = 2199767) B2199767
theorem B3129529 : Blo 1464552 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B2474185 : Blo 1464552 2474185 := bstep (se 2 (by rfl) ⟨927819, by rfl⟩ : syracuseStep 2474185 = 1855639) B1855639
theorem B11125025 : Blo 1464552 11125025 := bstep (se 2 (by rfl) ⟨4171884, by rfl⟩ : syracuseStep 11125025 = 8343769) B8343769
theorem B7422353 : Blo 1464552 7422353 := bstep (se 2 (by rfl) ⟨2783382, by rfl⟩ : syracuseStep 7422353 = 5566765) B5566765
theorem B3711379 : Blo 1464552 3711379 := bstep (se 1 (by rfl) ⟨2783534, by rfl⟩ : syracuseStep 3711379 = 5567069) B5567069
theorem B12517841 : Blo 1464552 12517841 := bstep (se 2 (by rfl) ⟨4694190, by rfl⟩ : syracuseStep 12517841 = 9388381) B9388381
theorem B3711521 : Blo 1464552 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B8348417 : Blo 1464552 8348417 := bstep (se 2 (by rfl) ⟨3130656, by rfl⟩ : syracuseStep 8348417 = 6261313) B6261313
theorem B5563151 : Blo 1464552 5563151 := bstep (se 1 (by rfl) ⟨4172363, by rfl⟩ : syracuseStep 5563151 = 8344727) B8344727
theorem B16704305 : Blo 1464552 16704305 := bstep (se 2 (by rfl) ⟨6264114, by rfl⟩ : syracuseStep 16704305 = 12528229) B12528229
theorem B3130247 : Blo 1464552 3130247 := bstep (se 1 (by rfl) ⟨2347685, by rfl⟩ : syracuseStep 3130247 = 4695371) B4695371
theorem B4948883 : Blo 1464552 4948883 := bstep (se 1 (by rfl) ⟨3711662, by rfl⟩ : syracuseStep 4948883 = 7423325) B7423325
theorem B1647751 : Blo 1464552 1647751 := bstep (se 1 (by rfl) ⟨1235813, by rfl⟩ : syracuseStep 1647751 = 2471627) B2471627
theorem B6259913 : Blo 1464552 6259913 := bstep (se 2 (by rfl) ⟨2347467, by rfl⟩ : syracuseStep 6259913 = 4694935) B4694935
theorem B11125997 : Blo 1464552 11125997 := bstep (se 3 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 11125997 = 4172249) B4172249
theorem B1647931 : Blo 1464552 1647931 := bstep (se 1 (by rfl) ⟨1235948, by rfl⟩ : syracuseStep 1647931 = 2471897) B2471897
theorem B4179319 : Blo 1464552 4179319 := bstep (se 1 (by rfl) ⟨3134489, by rfl⟩ : syracuseStep 4179319 = 6268979) B6268979
theorem B3130759 : Blo 1464552 3130759 := bstep (se 1 (by rfl) ⟨2348069, by rfl⟩ : syracuseStep 3130759 = 4696139) B4696139
theorem B9389459 : Blo 1464552 9389459 := bstep (se 1 (by rfl) ⟨7042094, by rfl⟩ : syracuseStep 9389459 = 14084189) B14084189
theorem B7923091 : Blo 1464552 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B7415225 : Blo 1464552 7415225 := bstep (se 2 (by rfl) ⟨2780709, by rfl⟩ : syracuseStep 7415225 = 5561419) B5561419
theorem B2196923 : Blo 1464552 2196923 := bstep (se 1 (by rfl) ⟨1647692, by rfl⟩ : syracuseStep 2196923 = 3295385) B3295385
theorem B2196983 : Blo 1464552 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B2197007 : Blo 1464552 2197007 := bstep (se 1 (by rfl) ⟨1647755, by rfl⟩ : syracuseStep 2197007 = 3295511) B3295511
theorem B3130913 : Blo 1464552 3130913 := bstep (se 2 (by rfl) ⟨1174092, by rfl⟩ : syracuseStep 3130913 = 2348185) B2348185
theorem B9389611 : Blo 1464552 9389611 := bstep (se 1 (by rfl) ⟨7042208, by rfl⟩ : syracuseStep 9389611 = 14084417) B14084417
theorem B2197049 : Blo 1464552 2197049 := bstep (se 2 (by rfl) ⟨823893, by rfl⟩ : syracuseStep 2197049 = 1647787) B1647787
theorem B2197127 : Blo 1464552 2197127 := bstep (se 1 (by rfl) ⟨1647845, by rfl⟩ : syracuseStep 2197127 = 3295691) B3295691
theorem B2197163 : Blo 1464552 2197163 := bstep (se 1 (by rfl) ⟨1647872, by rfl⟩ : syracuseStep 2197163 = 3295745) B3295745
theorem B2197193 : Blo 1464552 2197193 := bstep (se 2 (by rfl) ⟨823947, by rfl⟩ : syracuseStep 2197193 = 1647895) B1647895
theorem B1648399 : Blo 1464552 1648399 := bstep (se 1 (by rfl) ⟨1236299, by rfl⟩ : syracuseStep 1648399 = 2472599) B2472599
theorem B6686479 : Blo 1464552 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B5793569 : Blo 1464552 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B11880229 : Blo 1464552 11880229 := bstep (se 4 (by rfl) ⟨1113771, by rfl⟩ : syracuseStep 11880229 = 2227543) B2227543
theorem B2197307 : Blo 1464552 2197307 := bstep (se 1 (by rfl) ⟨1647980, by rfl⟩ : syracuseStep 2197307 = 3295961) B3295961
theorem B31672133 : Blo 1464552 31672133 := bstep (se 4 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 31672133 = 5938525) B5938525
theorem B2197367 : Blo 1464552 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B2197391 : Blo 1464552 2197391 := bstep (se 1 (by rfl) ⟨1648043, by rfl⟩ : syracuseStep 2197391 = 3296087) B3296087
theorem B2197433 : Blo 1464552 2197433 := bstep (se 2 (by rfl) ⟨824037, by rfl⟩ : syracuseStep 2197433 = 1648075) B1648075
theorem B12691403 : Blo 1464552 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B2197511 : Blo 1464552 2197511 := bstep (se 1 (by rfl) ⟨1648133, by rfl⟩ : syracuseStep 2197511 = 3296267) B3296267
theorem B2197547 : Blo 1464552 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B3131435 : Blo 1464552 3131435 := bstep (se 1 (by rfl) ⟨2348576, by rfl⟩ : syracuseStep 3131435 = 4697153) B4697153
theorem B2197577 : Blo 1464552 2197577 := bstep (se 2 (by rfl) ⟨824091, by rfl⟩ : syracuseStep 2197577 = 1648183) B1648183
theorem B3295367 : Blo 1464552 3295367 := bstep (se 1 (by rfl) ⟨2471525, by rfl⟩ : syracuseStep 3295367 = 4943051) B4943051
theorem B2197691 : Blo 1464552 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B2197751 : Blo 1464552 2197751 := bstep (se 1 (by rfl) ⟨1648313, by rfl⟩ : syracuseStep 2197751 = 3296627) B3296627
theorem B1648903 : Blo 1464552 1648903 := bstep (se 1 (by rfl) ⟨1236677, by rfl⟩ : syracuseStep 1648903 = 2473355) B2473355
theorem B2197775 : Blo 1464552 2197775 := bstep (se 1 (by rfl) ⟨1648331, by rfl⟩ : syracuseStep 2197775 = 3296663) B3296663
theorem B8341811 : Blo 1464552 8341811 := bstep (se 1 (by rfl) ⟨6256358, by rfl⟩ : syracuseStep 8341811 = 12512717) B12512717
theorem B2197817 : Blo 1464552 2197817 := bstep (se 2 (by rfl) ⟨824181, by rfl⟩ : syracuseStep 2197817 = 1648363) B1648363
theorem B3295547 : Blo 1464552 3295547 := bstep (se 1 (by rfl) ⟨2471660, by rfl⟩ : syracuseStep 3295547 = 4943321) B4943321
theorem B2197895 : Blo 1464552 2197895 := bstep (se 1 (by rfl) ⟨1648421, by rfl⟩ : syracuseStep 2197895 = 3296843) B3296843
theorem B5564807 : Blo 1464552 5564807 := bstep (se 1 (by rfl) ⟨4173605, by rfl⟩ : syracuseStep 5564807 = 8347211) B8347211
theorem B1853867 : Blo 1464552 1853867 := bstep (se 1 (by rfl) ⟨1390400, by rfl⟩ : syracuseStep 1853867 = 2780801) B2780801
theorem B2197931 : Blo 1464552 2197931 := bstep (se 1 (by rfl) ⟨1648448, by rfl⟩ : syracuseStep 2197931 = 3296897) B3296897
theorem B3295673 : Blo 1464552 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B1649083 : Blo 1464552 1649083 := bstep (se 1 (by rfl) ⟨1236812, by rfl⟩ : syracuseStep 1649083 = 2473625) B2473625
theorem B2197961 : Blo 1464552 2197961 := bstep (se 2 (by rfl) ⟨824235, by rfl⟩ : syracuseStep 2197961 = 1648471) B1648471
theorem B2198075 : Blo 1464552 2198075 := bstep (se 1 (by rfl) ⟨1648556, by rfl⟩ : syracuseStep 2198075 = 3297113) B3297113
theorem B17828417 : Blo 1464552 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B6777431 : Blo 1464552 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B2198135 : Blo 1464552 2198135 := bstep (se 1 (by rfl) ⟨1648601, by rfl⟩ : syracuseStep 2198135 = 3297203) B3297203
theorem B2198159 : Blo 1464552 2198159 := bstep (se 1 (by rfl) ⟨1648619, by rfl⟩ : syracuseStep 2198159 = 3297239) B3297239
theorem B2198201 : Blo 1464552 2198201 := bstep (se 2 (by rfl) ⟨824325, by rfl⟩ : syracuseStep 2198201 = 1648651) B1648651
theorem B7416521 : Blo 1464552 7416521 := bstep (se 2 (by rfl) ⟨2781195, by rfl⟩ : syracuseStep 7416521 = 5562391) B5562391
theorem B11135717 : Blo 1464552 11135717 := bstep (se 4 (by rfl) ⟨1043973, by rfl⟩ : syracuseStep 11135717 = 2087947) B2087947
theorem B2198279 : Blo 1464552 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B3296015 : Blo 1464552 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B3296033 : Blo 1464552 3296033 := bstep (se 2 (by rfl) ⟨1236012, by rfl⟩ : syracuseStep 3296033 = 2472025) B2472025
theorem B2198315 : Blo 1464552 2198315 := bstep (se 1 (by rfl) ⟨1648736, by rfl⟩ : syracuseStep 2198315 = 3297473) B3297473
theorem B2198345 : Blo 1464552 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B1854343 : Blo 1464552 1854343 := bstep (se 1 (by rfl) ⟨1390757, by rfl⟩ : syracuseStep 1854343 = 2781515) B2781515
theorem B1649551 : Blo 1464552 1649551 := bstep (se 1 (by rfl) ⟨1237163, by rfl⟩ : syracuseStep 1649551 = 2474327) B2474327
theorem B2198459 : Blo 1464552 2198459 := bstep (se 1 (by rfl) ⟨1648844, by rfl⟩ : syracuseStep 2198459 = 3297689) B3297689
theorem B2198519 : Blo 1464552 2198519 := bstep (se 1 (by rfl) ⟨1648889, by rfl⟩ : syracuseStep 2198519 = 3297779) B3297779
theorem B2198543 : Blo 1464552 2198543 := bstep (se 1 (by rfl) ⟨1648907, by rfl⟩ : syracuseStep 2198543 = 3297815) B3297815
theorem B2198585 : Blo 1464552 2198585 := bstep (se 2 (by rfl) ⟨824469, by rfl⟩ : syracuseStep 2198585 = 1648939) B1648939
theorem B16067645 : Blo 1464552 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B4172887 : Blo 1464552 4172887 := bstep (se 1 (by rfl) ⟨3129665, by rfl⟩ : syracuseStep 4172887 = 6259331) B6259331
theorem B7924823 : Blo 1464552 7924823 := bstep (se 1 (by rfl) ⟨5943617, by rfl⟩ : syracuseStep 7924823 = 11887235) B11887235
theorem B3296375 : Blo 1464552 3296375 := bstep (se 1 (by rfl) ⟨2472281, by rfl⟩ : syracuseStep 3296375 = 4944563) B4944563
theorem B11127941 : Blo 1464552 11127941 := bstep (se 4 (by rfl) ⟨1043244, by rfl⟩ : syracuseStep 11127941 = 2086489) B2086489
theorem B2198663 : Blo 1464552 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B2198699 : Blo 1464552 2198699 := bstep (se 1 (by rfl) ⟨1649024, by rfl⟩ : syracuseStep 2198699 = 3298049) B3298049
theorem B10570925 : Blo 1464552 10570925 := bstep (se 3 (by rfl) ⟨1982048, by rfl⟩ : syracuseStep 10570925 = 3964097) B3964097
theorem B2198729 : Blo 1464552 2198729 := bstep (se 2 (by rfl) ⟨824523, by rfl⟩ : syracuseStep 2198729 = 1649047) B1649047
theorem B4943105 : Blo 1464552 4943105 := bstep (se 2 (by rfl) ⟨1853664, by rfl⟩ : syracuseStep 4943105 = 3707329) B3707329
theorem B8457473 : Blo 1464552 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B6262049 : Blo 1464552 6262049 := bstep (se 2 (by rfl) ⟨2348268, by rfl⟩ : syracuseStep 6262049 = 4696537) B4696537
theorem B3296555 : Blo 1464552 3296555 := bstep (se 1 (by rfl) ⟨2472416, by rfl⟩ : syracuseStep 3296555 = 4944833) B4944833
theorem B4173115 : Blo 1464552 4173115 := bstep (se 1 (by rfl) ⟨3129836, by rfl⟩ : syracuseStep 4173115 = 6259673) B6259673
theorem B2198843 : Blo 1464552 2198843 := bstep (se 1 (by rfl) ⟨1649132, by rfl⟩ : syracuseStep 2198843 = 3298265) B3298265
theorem B3566963 : Blo 1464552 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B1854839 : Blo 1464552 1854839 := bstep (se 1 (by rfl) ⟨1391129, by rfl⟩ : syracuseStep 1854839 = 2782259) B2782259
theorem B2198903 : Blo 1464552 2198903 := bstep (se 1 (by rfl) ⟨1649177, by rfl⟩ : syracuseStep 2198903 = 3298355) B3298355
theorem B35671427 : Blo 1464552 35671427 := bstep (se 1 (by rfl) ⟨26753570, by rfl⟩ : syracuseStep 35671427 = 53507141) B53507141
theorem B2198927 : Blo 1464552 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B4173241 : Blo 1464552 4173241 := bstep (se 2 (by rfl) ⟨1564965, by rfl⟩ : syracuseStep 4173241 = 3129931) B3129931
theorem B2198969 : Blo 1464552 2198969 := bstep (se 2 (by rfl) ⟨824613, by rfl⟩ : syracuseStep 2198969 = 1649227) B1649227
theorem B6262201 : Blo 1464552 6262201 := bstep (se 2 (by rfl) ⟨2348325, by rfl⟩ : syracuseStep 6262201 = 4696651) B4696651
theorem B2199047 : Blo 1464552 2199047 := bstep (se 1 (by rfl) ⟨1649285, by rfl⟩ : syracuseStep 2199047 = 3298571) B3298571
theorem B1854991 : Blo 1464552 1854991 := bstep (se 1 (by rfl) ⟨1391243, by rfl⟩ : syracuseStep 1854991 = 2782487) B2782487
theorem B2199083 : Blo 1464552 2199083 := bstep (se 1 (by rfl) ⟨1649312, by rfl⟩ : syracuseStep 2199083 = 3298625) B3298625
theorem B5279293 : Blo 1464552 5279293 := bstep (se 3 (by rfl) ⟨989867, by rfl⟩ : syracuseStep 5279293 = 1979735) B1979735
theorem B2199113 : Blo 1464552 2199113 := bstep (se 2 (by rfl) ⟨824667, by rfl⟩ : syracuseStep 2199113 = 1649335) B1649335
theorem B3296915 : Blo 1464552 3296915 := bstep (se 1 (by rfl) ⟨2472686, by rfl⟩ : syracuseStep 3296915 = 4945373) B4945373
theorem B1855163 : Blo 1464552 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B2199227 : Blo 1464552 2199227 := bstep (se 1 (by rfl) ⟨1649420, by rfl⟩ : syracuseStep 2199227 = 3298841) B3298841
theorem B3296969 : Blo 1464552 3296969 := bstep (se 2 (by rfl) ⟨1236363, by rfl⟩ : syracuseStep 3296969 = 2472727) B2472727
theorem B8343269 : Blo 1464552 8343269 := bstep (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) B1564363
theorem B2199287 : Blo 1464552 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B2199311 : Blo 1464552 2199311 := bstep (se 1 (by rfl) ⟨1649483, by rfl⟩ : syracuseStep 2199311 = 3298967) B3298967
theorem B2199353 : Blo 1464552 2199353 := bstep (se 2 (by rfl) ⟨824757, by rfl⟩ : syracuseStep 2199353 = 1649515) B1649515
theorem B2199431 : Blo 1464552 2199431 := bstep (se 1 (by rfl) ⟨1649573, by rfl⟩ : syracuseStep 2199431 = 3299147) B3299147
theorem B2199467 : Blo 1464552 2199467 := bstep (se 1 (by rfl) ⟨1649600, by rfl⟩ : syracuseStep 2199467 = 3299201) B3299201
theorem B2199497 : Blo 1464552 2199497 := bstep (se 2 (by rfl) ⟨824811, by rfl⟩ : syracuseStep 2199497 = 1649623) B1649623
theorem B5279755 : Blo 1464552 5279755 := bstep (se 1 (by rfl) ⟨3959816, by rfl⟩ : syracuseStep 5279755 = 7919633) B7919633
theorem B4943915 : Blo 1464552 4943915 := bstep (se 1 (by rfl) ⟨3707936, by rfl⟩ : syracuseStep 4943915 = 7415873) B7415873
theorem B2199611 : Blo 1464552 2199611 := bstep (se 1 (by rfl) ⟨1649708, by rfl⟩ : syracuseStep 2199611 = 3299417) B3299417
theorem B5566583 : Blo 1464552 5566583 := bstep (se 1 (by rfl) ⟨4174937, by rfl⟩ : syracuseStep 5566583 = 8349875) B8349875
theorem B2199671 : Blo 1464552 2199671 := bstep (se 1 (by rfl) ⟨1649753, by rfl⟩ : syracuseStep 2199671 = 3299507) B3299507
theorem B2199695 : Blo 1464552 2199695 := bstep (se 1 (by rfl) ⟨1649771, by rfl⟩ : syracuseStep 2199695 = 3299543) B3299543
theorem B2347193 : Blo 1464552 2347193 := bstep (se 2 (by rfl) ⟨880197, by rfl⟩ : syracuseStep 2347193 = 1760395) B1760395
theorem B2199737 : Blo 1464552 2199737 := bstep (se 2 (by rfl) ⟨824901, by rfl⟩ : syracuseStep 2199737 = 1649803) B1649803
theorem B6263021 : Blo 1464552 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B2199815 : Blo 1464552 2199815 := bstep (se 1 (by rfl) ⟨1649861, by rfl⟩ : syracuseStep 2199815 = 3299723) B3299723
theorem B3297671 : Blo 1464552 3297671 := bstep (se 1 (by rfl) ⟨2473253, by rfl⟩ : syracuseStep 3297671 = 4946507) B4946507
theorem B32133523 : Blo 1464552 32133523 := bstep (se 1 (by rfl) ⟨24100142, by rfl⟩ : syracuseStep 32133523 = 48200285) B48200285
theorem B3297851 : Blo 1464552 3297851 := bstep (se 1 (by rfl) ⟨2473388, by rfl⟩ : syracuseStep 3297851 = 4946777) B4946777
theorem B22565441 : Blo 1464552 22565441 := bstep (se 2 (by rfl) ⟨8462040, by rfl⟩ : syracuseStep 22565441 = 16924081) B16924081
theorem B3297977 : Blo 1464552 3297977 := bstep (se 2 (by rfl) ⟨1236741, by rfl⟩ : syracuseStep 3297977 = 2473483) B2473483
theorem B3707795 : Blo 1464552 3707795 := bstep (se 1 (by rfl) ⟨2780846, by rfl⟩ : syracuseStep 3707795 = 5561693) B5561693
theorem B6263705 : Blo 1464552 6263705 := bstep (se 2 (by rfl) ⟨2348889, by rfl⟩ : syracuseStep 6263705 = 4697779) B4697779
theorem B3298319 : Blo 1464552 3298319 := bstep (se 1 (by rfl) ⟨2473739, by rfl⟩ : syracuseStep 3298319 = 4947479) B4947479
theorem B3298337 : Blo 1464552 3298337 := bstep (se 2 (by rfl) ⟨1236876, by rfl⟩ : syracuseStep 3298337 = 2473753) B2473753
theorem B5567555 : Blo 1464552 5567555 := bstep (se 1 (by rfl) ⟨4175666, by rfl⟩ : syracuseStep 5567555 = 8351333) B8351333
theorem B7918679 : Blo 1464552 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B2782343 : Blo 1464552 2782343 := bstep (se 1 (by rfl) ⟨2086757, by rfl⟩ : syracuseStep 2782343 = 4173515) B4173515
theorem B8574125 : Blo 1464552 8574125 := bstep (se 3 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 8574125 = 3215297) B3215297
theorem B3708089 : Blo 1464552 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B4945211 : Blo 1464552 4945211 := bstep (se 1 (by rfl) ⟨3708908, by rfl⟩ : syracuseStep 4945211 = 7417817) B7417817
theorem B4175165 : Blo 1464552 4175165 := bstep (se 3 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 4175165 = 1565687) B1565687
theorem B5281139 : Blo 1464552 5281139 := bstep (se 1 (by rfl) ⟨3960854, by rfl⟩ : syracuseStep 5281139 = 7921709) B7921709
theorem B3298679 : Blo 1464552 3298679 := bstep (se 1 (by rfl) ⟨2474009, by rfl⟩ : syracuseStep 3298679 = 4948019) B4948019
theorem B15840647 : Blo 1464552 15840647 := bstep (se 1 (by rfl) ⟨11880485, by rfl⟩ : syracuseStep 15840647 = 23760971) B23760971
theorem B5641607 : Blo 1464552 5641607 := bstep (se 1 (by rfl) ⟨4231205, by rfl⟩ : syracuseStep 5641607 = 8462411) B8462411
theorem B2348423 : Blo 1464552 2348423 := bstep (se 1 (by rfl) ⟨1761317, by rfl⟩ : syracuseStep 2348423 = 3522635) B3522635
theorem B8918419 : Blo 1464552 8918419 := bstep (se 1 (by rfl) ⟨6688814, by rfl⟩ : syracuseStep 8918419 = 13377629) B13377629
theorem B11130371 : Blo 1464552 11130371 := bstep (se 1 (by rfl) ⟨8347778, by rfl⟩ : syracuseStep 11130371 = 16695557) B16695557
theorem B5568011 : Blo 1464552 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3298859 : Blo 1464552 3298859 := bstep (se 1 (by rfl) ⟨2474144, by rfl⟩ : syracuseStep 3298859 = 4948289) B4948289
theorem B4945697 : Blo 1464552 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B27121483 : Blo 1464552 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B3708787 : Blo 1464552 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B3299219 : Blo 1464552 3299219 := bstep (se 1 (by rfl) ⟨2474414, by rfl⟩ : syracuseStep 3299219 = 4948829) B4948829
theorem B11122595 : Blo 1464552 11122595 := bstep (se 1 (by rfl) ⟨8341946, by rfl⟩ : syracuseStep 11122595 = 16683893) B16683893
theorem B2234297 : Blo 1464552 2234297 := bstep (se 2 (by rfl) ⟨837861, by rfl⟩ : syracuseStep 2234297 = 1675723) B1675723
theorem B3299273 : Blo 1464552 3299273 := bstep (se 2 (by rfl) ⟨1237227, by rfl⟩ : syracuseStep 3299273 = 2474455) B2474455
theorem B3708929 : Blo 1464552 3708929 := bstep (se 2 (by rfl) ⟨1390848, by rfl⟩ : syracuseStep 3708929 = 2781697) B2781697
theorem B2471951 : Blo 1464552 2471951 := bstep (se 1 (by rfl) ⟨1853963, by rfl⟩ : syracuseStep 2471951 = 3707927) B3707927
theorem B2086985 : Blo 1464552 2086985 := bstep (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) B1565239
theorem B27121837 : Blo 1464552 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B4757705 : Blo 1464552 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B6428909 : Blo 1464552 6428909 := bstep (se 3 (by rfl) ⟨1205420, by rfl⟩ : syracuseStep 6428909 = 2410841) B2410841
theorem B1464583 : Blo 1464552 1464583 := bstep (se 1 (by rfl) ⟨1098437, by rfl⟩ : syracuseStep 1464583 = 2196875) B2196875
theorem B1464591 : Blo 1464552 1464591 := bstep (se 1 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 1464591 = 2196887) B2196887
theorem B17824033 : Blo 1464552 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B4176157 : Blo 1464552 4176157 := bstep (se 3 (by rfl) ⟨783029, by rfl⟩ : syracuseStep 4176157 = 1566059) B1566059
theorem B1464635 : Blo 1464552 1464635 := bstep (se 1 (by rfl) ⟨1098476, by rfl⟩ : syracuseStep 1464635 = 2196953) B2196953
theorem B4946291 : Blo 1464552 4946291 := bstep (se 1 (by rfl) ⟨3709718, by rfl⟩ : syracuseStep 4946291 = 7419437) B7419437
theorem B1464711 : Blo 1464552 1464711 := bstep (se 1 (by rfl) ⟨1098533, by rfl⟩ : syracuseStep 1464711 = 2197067) B2197067
theorem B1464719 : Blo 1464552 1464719 := bstep (se 1 (by rfl) ⟨1098539, by rfl⟩ : syracuseStep 1464719 = 2197079) B2197079
theorem B1464763 : Blo 1464552 1464763 := bstep (se 1 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 1464763 = 2197145) B2197145
theorem B3709385 : Blo 1464552 3709385 := bstep (se 2 (by rfl) ⟨1391019, by rfl⟩ : syracuseStep 3709385 = 2782039) B2782039
theorem B1464839 : Blo 1464552 1464839 := bstep (se 1 (by rfl) ⟨1098629, by rfl⟩ : syracuseStep 1464839 = 2197259) B2197259
theorem B1464847 : Blo 1464552 1464847 := bstep (se 1 (by rfl) ⟨1098635, by rfl⟩ : syracuseStep 1464847 = 2197271) B2197271
theorem B2472491 : Blo 1464552 2472491 := bstep (se 1 (by rfl) ⟨1854368, by rfl⟩ : syracuseStep 2472491 = 3708737) B3708737
theorem B1464891 : Blo 1464552 1464891 := bstep (se 1 (by rfl) ⟨1098668, by rfl⟩ : syracuseStep 1464891 = 2197337) B2197337
theorem B6257213 : Blo 1464552 6257213 := bstep (se 3 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 6257213 = 2346455) B2346455
theorem B5560919 : Blo 1464552 5560919 := bstep (se 1 (by rfl) ⟨4170689, by rfl⟩ : syracuseStep 5560919 = 8341379) B8341379
theorem B1464967 : Blo 1464552 1464967 := bstep (se 1 (by rfl) ⟨1098725, by rfl⟩ : syracuseStep 1464967 = 2197451) B2197451
theorem B1464975 : Blo 1464552 1464975 := bstep (se 1 (by rfl) ⟨1098731, by rfl⟩ : syracuseStep 1464975 = 2197463) B2197463
theorem B1465019 : Blo 1464552 1465019 := bstep (se 1 (by rfl) ⟨1098764, by rfl⟩ : syracuseStep 1465019 = 2197529) B2197529
theorem B2783945 : Blo 1464552 2783945 := bstep (se 2 (by rfl) ⟨1043979, by rfl⟩ : syracuseStep 2783945 = 2087959) B2087959
theorem B33856217 : Blo 1464552 33856217 := bstep (se 2 (by rfl) ⟨12696081, by rfl⟩ : syracuseStep 33856217 = 25392163) B25392163
theorem B2226935 : Blo 1464552 2226935 := bstep (se 1 (by rfl) ⟨1670201, by rfl⟩ : syracuseStep 2226935 = 3340403) B3340403
theorem B1465095 : Blo 1464552 1465095 := bstep (se 1 (by rfl) ⟨1098821, by rfl⟩ : syracuseStep 1465095 = 2197643) B2197643
theorem B1465103 : Blo 1464552 1465103 := bstep (se 1 (by rfl) ⟨1098827, by rfl⟩ : syracuseStep 1465103 = 2197655) B2197655
theorem B3709739 : Blo 1464552 3709739 := bstep (se 1 (by rfl) ⟨2782304, by rfl⟩ : syracuseStep 3709739 = 5564609) B5564609
theorem B1465147 : Blo 1464552 1465147 := bstep (se 1 (by rfl) ⟨1098860, by rfl⟩ : syracuseStep 1465147 = 2197721) B2197721
theorem B1465223 : Blo 1464552 1465223 := bstep (se 1 (by rfl) ⟨1098917, by rfl⟩ : syracuseStep 1465223 = 2197835) B2197835
theorem B8346503 : Blo 1464552 8346503 := bstep (se 1 (by rfl) ⟨6259877, by rfl⟩ : syracuseStep 8346503 = 12519755) B12519755
theorem B5282695 : Blo 1464552 5282695 := bstep (se 1 (by rfl) ⟨3962021, by rfl⟩ : syracuseStep 5282695 = 7924043) B7924043
theorem B7338887 : Blo 1464552 7338887 := bstep (se 1 (by rfl) ⟨5504165, by rfl⟩ : syracuseStep 7338887 = 11008331) B11008331
theorem B1465231 : Blo 1464552 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B2087851 : Blo 1464552 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B2472889 : Blo 1464552 2472889 := bstep (se 2 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 2472889 = 1854667) B1854667
theorem B1465275 : Blo 1464552 1465275 := bstep (se 1 (by rfl) ⟨1098956, by rfl⟩ : syracuseStep 1465275 = 2197913) B2197913
theorem B1465351 : Blo 1464552 1465351 := bstep (se 1 (by rfl) ⟨1099013, by rfl⟩ : syracuseStep 1465351 = 2198027) B2198027
theorem B6257675 : Blo 1464552 6257675 := bstep (se 1 (by rfl) ⟨4693256, by rfl⟩ : syracuseStep 6257675 = 9386513) B9386513
theorem B1465359 : Blo 1464552 1465359 := bstep (se 1 (by rfl) ⟨1099019, by rfl⟩ : syracuseStep 1465359 = 2198039) B2198039
theorem B1465403 : Blo 1464552 1465403 := bstep (se 1 (by rfl) ⟨1099052, by rfl⟩ : syracuseStep 1465403 = 2198105) B2198105
theorem B5561405 : Blo 1464552 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B8346685 : Blo 1464552 8346685 := bstep (se 3 (by rfl) ⟨1565003, by rfl⟩ : syracuseStep 8346685 = 3130007) B3130007
theorem B32136323 : Blo 1464552 32136323 := bstep (se 1 (by rfl) ⟨24102242, by rfl⟩ : syracuseStep 32136323 = 48204485) B48204485
theorem B1465479 : Blo 1464552 1465479 := bstep (se 1 (by rfl) ⟨1099109, by rfl⟩ : syracuseStep 1465479 = 2198219) B2198219
theorem B1465487 : Blo 1464552 1465487 := bstep (se 1 (by rfl) ⟨1099115, by rfl⟩ : syracuseStep 1465487 = 2198231) B2198231
theorem B3341497 : Blo 1464552 3341497 := bstep (se 2 (by rfl) ⟨1253061, by rfl⟩ : syracuseStep 3341497 = 2506123) B2506123
theorem B1465531 : Blo 1464552 1465531 := bstep (se 1 (by rfl) ⟨1099148, by rfl⟩ : syracuseStep 1465531 = 2198297) B2198297
theorem B1981627 : Blo 1464552 1981627 := bstep (se 1 (by rfl) ⟨1486220, by rfl⟩ : syracuseStep 1981627 = 2972441) B2972441
theorem B1465607 : Blo 1464552 1465607 := bstep (se 1 (by rfl) ⟨1099205, by rfl⟩ : syracuseStep 1465607 = 2198411) B2198411
theorem B1981703 : Blo 1464552 1981703 := bstep (se 1 (by rfl) ⟨1486277, by rfl⟩ : syracuseStep 1981703 = 2972555) B2972555
theorem B1465615 : Blo 1464552 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B2506027 : Blo 1464552 2506027 := bstep (se 1 (by rfl) ⟨1879520, by rfl⟩ : syracuseStep 2506027 = 3759041) B3759041
theorem B1465659 : Blo 1464552 1465659 := bstep (se 1 (by rfl) ⟨1099244, by rfl⟩ : syracuseStep 1465659 = 2198489) B2198489
theorem B21405059 : Blo 1464552 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B1465735 : Blo 1464552 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B1465743 : Blo 1464552 1465743 := bstep (se 1 (by rfl) ⟨1099307, by rfl⟩ : syracuseStep 1465743 = 2198615) B2198615
theorem B1465787 : Blo 1464552 1465787 := bstep (se 1 (by rfl) ⟨1099340, by rfl⟩ : syracuseStep 1465787 = 2198681) B2198681
theorem B1465863 : Blo 1464552 1465863 := bstep (se 1 (by rfl) ⟨1099397, by rfl⟩ : syracuseStep 1465863 = 2198795) B2198795
theorem B1760783 : Blo 1464552 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B1465871 : Blo 1464552 1465871 := bstep (se 1 (by rfl) ⟨1099403, by rfl⟩ : syracuseStep 1465871 = 2198807) B2198807
theorem B1465915 : Blo 1464552 1465915 := bstep (se 1 (by rfl) ⟨1099436, by rfl⟩ : syracuseStep 1465915 = 2198873) B2198873
theorem B4693565 : Blo 1464552 4693565 := bstep (se 3 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 4693565 = 1760087) B1760087
theorem B10567235 : Blo 1464552 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B2473591 : Blo 1464552 2473591 := bstep (se 1 (by rfl) ⟨1855193, by rfl⟩ : syracuseStep 2473591 = 3710387) B3710387
theorem B3620471 : Blo 1464552 3620471 := bstep (se 1 (by rfl) ⟨2715353, by rfl⟩ : syracuseStep 3620471 = 5430707) B5430707
theorem B1465991 : Blo 1464552 1465991 := bstep (se 1 (by rfl) ⟨1099493, by rfl⟩ : syracuseStep 1465991 = 2198987) B2198987
theorem B1465999 : Blo 1464552 1465999 := bstep (se 1 (by rfl) ⟨1099499, by rfl⟩ : syracuseStep 1465999 = 2198999) B2198999
theorem B18767537 : Blo 1464552 18767537 := bstep (se 2 (by rfl) ⟨7037826, by rfl⟩ : syracuseStep 18767537 = 14075653) B14075653
theorem B1466043 : Blo 1464552 1466043 := bstep (se 1 (by rfl) ⟨1099532, by rfl⟩ : syracuseStep 1466043 = 2199065) B2199065
theorem B16686809 : Blo 1464552 16686809 := bstep (se 2 (by rfl) ⟨6257553, by rfl⟩ : syracuseStep 16686809 = 12515107) B12515107
theorem B1466119 : Blo 1464552 1466119 := bstep (se 1 (by rfl) ⟨1099589, by rfl⟩ : syracuseStep 1466119 = 2199179) B2199179
theorem B3710731 : Blo 1464552 3710731 := bstep (se 1 (by rfl) ⟨2783048, by rfl⟩ : syracuseStep 3710731 = 5566097) B5566097
theorem B1466127 : Blo 1464552 1466127 := bstep (se 1 (by rfl) ⟨1099595, by rfl⟩ : syracuseStep 1466127 = 2199191) B2199191
theorem B2506555 : Blo 1464552 2506555 := bstep (se 1 (by rfl) ⟨1879916, by rfl⟩ : syracuseStep 2506555 = 3759833) B3759833
theorem B2473787 : Blo 1464552 2473787 := bstep (se 1 (by rfl) ⟨1855340, by rfl⟩ : syracuseStep 2473787 = 3710681) B3710681
theorem B1466171 : Blo 1464552 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B1466247 : Blo 1464552 1466247 := bstep (se 1 (by rfl) ⟨1099685, by rfl⟩ : syracuseStep 1466247 = 2199371) B2199371
theorem B1466255 : Blo 1464552 1466255 := bstep (se 1 (by rfl) ⟨1099691, by rfl⟩ : syracuseStep 1466255 = 2199383) B2199383
theorem B3710873 : Blo 1464552 3710873 := bstep (se 2 (by rfl) ⟨1391577, by rfl⟩ : syracuseStep 3710873 = 2783155) B2783155
theorem B1466299 : Blo 1464552 1466299 := bstep (se 1 (by rfl) ⟨1099724, by rfl⟩ : syracuseStep 1466299 = 2199449) B2199449
theorem B2474023 : Blo 1464552 2474023 := bstep (se 1 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 2474023 = 3711035) B3711035
theorem B1466407 : Blo 1464552 1466407 := bstep (se 1 (by rfl) ⟨1099805, by rfl⟩ : syracuseStep 1466407 = 2199611) B2199611
theorem B3711055 : Blo 1464552 3711055 := bstep (se 1 (by rfl) ⟨2783291, by rfl⟩ : syracuseStep 3711055 = 5566583) B5566583
theorem B1466447 : Blo 1464552 1466447 := bstep (se 1 (by rfl) ⟨1099835, by rfl⟩ : syracuseStep 1466447 = 2199671) B2199671
theorem B1466463 : Blo 1464552 1466463 := bstep (se 1 (by rfl) ⟨1099847, by rfl⟩ : syracuseStep 1466463 = 2199695) B2199695
theorem B1564795 : Blo 1464552 1564795 := bstep (se 1 (by rfl) ⟨1173596, by rfl⟩ : syracuseStep 1564795 = 2347193) B2347193
theorem B1466491 : Blo 1464552 1466491 := bstep (se 1 (by rfl) ⟨1099868, by rfl⟩ : syracuseStep 1466491 = 2199737) B2199737
theorem B1466543 : Blo 1464552 1466543 := bstep (se 1 (by rfl) ⟨1099907, by rfl⟩ : syracuseStep 1466543 = 2199815) B2199815
theorem B4948235 : Blo 1464552 4948235 := bstep (se 1 (by rfl) ⟨3711176, by rfl⟩ : syracuseStep 4948235 = 7422353) B7422353
theorem B85696861 : Blo 1464552 85696861 := bstep (se 3 (by rfl) ⟨16068161, by rfl⟩ : syracuseStep 85696861 = 32136323) B32136323
theorem B2474347 : Blo 1464552 2474347 := bstep (se 1 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 2474347 = 3711521) B3711521
theorem B28189133 : Blo 1464552 28189133 := bstep (se 3 (by rfl) ⟨5285462, by rfl⟩ : syracuseStep 28189133 = 10570925) B10570925
theorem B42844697 : Blo 1464552 42844697 := bstep (se 2 (by rfl) ⟨16066761, by rfl⟩ : syracuseStep 42844697 = 32133523) B32133523
theorem B4948505 : Blo 1464552 4948505 := bstep (se 2 (by rfl) ⟨1855689, by rfl⟩ : syracuseStep 4948505 = 3711379) B3711379
theorem B22553261 : Blo 1464552 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B5284541 : Blo 1464552 5284541 := bstep (se 3 (by rfl) ⟨990851, by rfl⟩ : syracuseStep 5284541 = 1981703) B1981703
theorem B3711703 : Blo 1464552 3711703 := bstep (se 1 (by rfl) ⟨2783777, by rfl⟩ : syracuseStep 3711703 = 5567555) B5567555
theorem B11133773 : Blo 1464552 11133773 := bstep (se 3 (by rfl) ⟨2087582, by rfl⟩ : syracuseStep 11133773 = 4175165) B4175165
theorem B10560431 : Blo 1464552 10560431 := bstep (se 1 (by rfl) ⟨7920323, by rfl⟩ : syracuseStep 10560431 = 15840647) B15840647
theorem B1565615 : Blo 1464552 1565615 := bstep (se 1 (by rfl) ⟨1174211, by rfl⟩ : syracuseStep 1565615 = 2348423) B2348423
theorem B6259639 : Blo 1464552 6259639 := bstep (se 1 (by rfl) ⟨4694729, by rfl⟩ : syracuseStep 6259639 = 9389459) B9389459
theorem B9511901 : Blo 1464552 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B3712007 : Blo 1464552 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B7415063 : Blo 1464552 7415063 := bstep (se 1 (by rfl) ⟨5561297, by rfl⟩ : syracuseStep 7415063 = 11122595) B11122595
theorem B1647967 : Blo 1464552 1647967 := bstep (se 1 (by rfl) ⟨1235975, by rfl⟩ : syracuseStep 1647967 = 2471951) B2471951
theorem B4695421 : Blo 1464552 4695421 := bstep (se 3 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 4695421 = 1760783) B1760783
theorem B35661221 : Blo 1464552 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B8349101 : Blo 1464552 8349101 := bstep (se 3 (by rfl) ⟨1565456, by rfl⟩ : syracuseStep 8349101 = 3130913) B3130913
theorem B2196911 : Blo 1464552 2196911 := bstep (se 1 (by rfl) ⟨1647683, by rfl⟩ : syracuseStep 2196911 = 3295367) B3295367
theorem B5563849 : Blo 1464552 5563849 := bstep (se 2 (by rfl) ⟨2086443, by rfl⟩ : syracuseStep 5563849 = 4172887) B4172887
theorem B3171803 : Blo 1464552 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B95061509 : Blo 1464552 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B2197001 : Blo 1464552 2197001 := bstep (se 2 (by rfl) ⟨823875, by rfl⟩ : syracuseStep 2197001 = 1647751) B1647751
theorem B2197031 : Blo 1464552 2197031 := bstep (se 1 (by rfl) ⟨1647773, by rfl⟩ : syracuseStep 2197031 = 3295547) B3295547
theorem B2197115 : Blo 1464552 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B1648327 : Blo 1464552 1648327 := bstep (se 1 (by rfl) ⟨1236245, by rfl⟩ : syracuseStep 1648327 = 2472491) B2472491
theorem B4171475 : Blo 1464552 4171475 := bstep (se 1 (by rfl) ⟨3128606, by rfl⟩ : syracuseStep 4171475 = 6257213) B6257213
theorem B2197241 : Blo 1464552 2197241 := bstep (se 2 (by rfl) ⟨823965, by rfl⟩ : syracuseStep 2197241 = 1647931) B1647931
theorem B5564153 : Blo 1464552 5564153 := bstep (se 2 (by rfl) ⟨2086557, by rfl⟩ : syracuseStep 5564153 = 4173115) B4173115
theorem B91457333 : Blo 1464552 91457333 := bstep (se 5 (by rfl) ⟨4287062, by rfl⟩ : syracuseStep 91457333 = 8574125) B8574125
theorem B22570811 : Blo 1464552 22570811 := bstep (se 1 (by rfl) ⟨16928108, by rfl⟩ : syracuseStep 22570811 = 33856217) B33856217
theorem B7423811 : Blo 1464552 7423811 := bstep (se 1 (by rfl) ⟨5567858, by rfl⟩ : syracuseStep 7423811 = 11135717) B11135717
theorem B1484623 : Blo 1464552 1484623 := bstep (se 1 (by rfl) ⟨1113467, by rfl⟩ : syracuseStep 1484623 = 2226935) B2226935
theorem B2197343 : Blo 1464552 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B2197355 : Blo 1464552 2197355 := bstep (se 1 (by rfl) ⟨1648016, by rfl⟩ : syracuseStep 2197355 = 3296033) B3296033
theorem B5564321 : Blo 1464552 5564321 := bstep (se 2 (by rfl) ⟨2086620, by rfl⟩ : syracuseStep 5564321 = 4173241) B4173241
theorem B8349601 : Blo 1464552 8349601 := bstep (se 2 (by rfl) ⟨3131100, by rfl⟩ : syracuseStep 8349601 = 6262201) B6262201
theorem B5564335 : Blo 1464552 5564335 := bstep (se 1 (by rfl) ⟨4173251, by rfl⟩ : syracuseStep 5564335 = 8346503) B8346503
theorem B4892591 : Blo 1464552 4892591 := bstep (se 1 (by rfl) ⟨3669443, by rfl⟩ : syracuseStep 4892591 = 7338887) B7338887
theorem B4171783 : Blo 1464552 4171783 := bstep (se 1 (by rfl) ⟨3128837, by rfl⟩ : syracuseStep 4171783 = 6257675) B6257675
theorem B12519481 : Blo 1464552 12519481 := bstep (se 2 (by rfl) ⟨4694805, by rfl⟩ : syracuseStep 12519481 = 9389611) B9389611
theorem B2197583 : Blo 1464552 2197583 := bstep (se 1 (by rfl) ⟨1648187, by rfl⟩ : syracuseStep 2197583 = 3296375) B3296375
theorem B7039057 : Blo 1464552 7039057 := bstep (se 2 (by rfl) ⟨2639646, by rfl⟩ : syracuseStep 7039057 = 5279293) B5279293
theorem B3295403 : Blo 1464552 3295403 := bstep (se 1 (by rfl) ⟨2471552, by rfl⟩ : syracuseStep 3295403 = 4943105) B4943105
theorem B2197703 : Blo 1464552 2197703 := bstep (se 1 (by rfl) ⟨1648277, by rfl⟩ : syracuseStep 2197703 = 3296555) B3296555
theorem B2197865 : Blo 1464552 2197865 := bstep (se 2 (by rfl) ⟨824199, by rfl⟩ : syracuseStep 2197865 = 1648399) B1648399
theorem B2197943 : Blo 1464552 2197943 := bstep (se 1 (by rfl) ⟨1648457, by rfl⟩ : syracuseStep 2197943 = 3296915) B3296915
theorem B36161977 : Blo 1464552 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B12511691 : Blo 1464552 12511691 := bstep (se 1 (by rfl) ⟨9383768, by rfl⟩ : syracuseStep 12511691 = 18767537) B18767537
theorem B2197979 : Blo 1464552 2197979 := bstep (se 1 (by rfl) ⟨1648484, by rfl⟩ : syracuseStep 2197979 = 3296969) B3296969
theorem B5958125 : Blo 1464552 5958125 := bstep (se 3 (by rfl) ⟨1117148, by rfl⟩ : syracuseStep 5958125 = 2234297) B2234297
theorem B1649191 : Blo 1464552 1649191 := bstep (se 1 (by rfl) ⟨1236893, by rfl⟩ : syracuseStep 1649191 = 2473787) B2473787
theorem B7039673 : Blo 1464552 7039673 := bstep (se 2 (by rfl) ⟨2639877, by rfl⟩ : syracuseStep 7039673 = 5279755) B5279755
theorem B3295943 : Blo 1464552 3295943 := bstep (se 1 (by rfl) ⟨2471957, by rfl⟩ : syracuseStep 3295943 = 4943915) B4943915
theorem B7416683 : Blo 1464552 7416683 := bstep (se 1 (by rfl) ⟨5562512, by rfl⟩ : syracuseStep 7416683 = 11125025) B11125025
theorem B5565293 : Blo 1464552 5565293 := bstep (se 3 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 5565293 = 2086985) B2086985
theorem B36162449 : Blo 1464552 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B4172705 : Blo 1464552 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B2198447 : Blo 1464552 2198447 := bstep (se 1 (by rfl) ⟨1648835, by rfl⟩ : syracuseStep 2198447 = 3297671) B3297671
theorem B2198537 : Blo 1464552 2198537 := bstep (se 2 (by rfl) ⟨824451, by rfl⟩ : syracuseStep 2198537 = 1648903) B1648903
theorem B2198567 : Blo 1464552 2198567 := bstep (se 1 (by rfl) ⟨1648925, by rfl⟩ : syracuseStep 2198567 = 3297851) B3297851
theorem B15043627 : Blo 1464552 15043627 := bstep (se 1 (by rfl) ⟨11282720, by rfl⟩ : syracuseStep 15043627 = 22565441) B22565441
theorem B2198651 : Blo 1464552 2198651 := bstep (se 1 (by rfl) ⟨1648988, by rfl⟩ : syracuseStep 2198651 = 3297977) B3297977
theorem B5565611 : Blo 1464552 5565611 := bstep (se 1 (by rfl) ⟨4174208, by rfl⟩ : syracuseStep 5565611 = 8348417) B8348417
theorem B11136203 : Blo 1464552 11136203 := bstep (se 1 (by rfl) ⟨8352152, by rfl⟩ : syracuseStep 11136203 = 16704305) B16704305
theorem B2198777 : Blo 1464552 2198777 := bstep (se 2 (by rfl) ⟨824541, by rfl⟩ : syracuseStep 2198777 = 1649083) B1649083
theorem B2198879 : Blo 1464552 2198879 := bstep (se 1 (by rfl) ⟨1649159, by rfl⟩ : syracuseStep 2198879 = 3298319) B3298319
theorem B2198891 : Blo 1464552 2198891 := bstep (se 1 (by rfl) ⟨1649168, by rfl⟩ : syracuseStep 2198891 = 3298337) B3298337
theorem B1854895 : Blo 1464552 1854895 := bstep (se 1 (by rfl) ⟨1391171, by rfl⟩ : syracuseStep 1854895 = 2782343) B2782343
theorem B4173275 : Blo 1464552 4173275 := bstep (se 1 (by rfl) ⟨3129956, by rfl⟩ : syracuseStep 4173275 = 6259913) B6259913
theorem B7417331 : Blo 1464552 7417331 := bstep (se 1 (by rfl) ⟨5562998, by rfl⟩ : syracuseStep 7417331 = 11125997) B11125997
theorem B3296807 : Blo 1464552 3296807 := bstep (se 1 (by rfl) ⟨2472605, by rfl⟩ : syracuseStep 3296807 = 4945211) B4945211
theorem B2199119 : Blo 1464552 2199119 := bstep (se 1 (by rfl) ⟨1649339, by rfl⟩ : syracuseStep 2199119 = 3298679) B3298679
theorem B4943483 : Blo 1464552 4943483 := bstep (se 1 (by rfl) ⟨3707612, by rfl⟩ : syracuseStep 4943483 = 7415225) B7415225
theorem B15044285 : Blo 1464552 15044285 := bstep (se 3 (by rfl) ⟨2820803, by rfl⟩ : syracuseStep 15044285 = 5641607) B5641607
theorem B2199239 : Blo 1464552 2199239 := bstep (se 1 (by rfl) ⟨1649429, by rfl⟩ : syracuseStep 2199239 = 3298859) B3298859
theorem B4943645 : Blo 1464552 4943645 := bstep (se 3 (by rfl) ⟨926933, by rfl⟩ : syracuseStep 4943645 = 1853867) B1853867
theorem B2199401 : Blo 1464552 2199401 := bstep (se 2 (by rfl) ⟨824775, by rfl⟩ : syracuseStep 2199401 = 1649551) B1649551
theorem B3862379 : Blo 1464552 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B3297131 : Blo 1464552 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B21114755 : Blo 1464552 21114755 := bstep (se 1 (by rfl) ⟨15836066, by rfl⟩ : syracuseStep 21114755 = 31672133) B31672133
theorem B42274709 : Blo 1464552 42274709 := bstep (se 6 (by rfl) ⟨990813, by rfl⟩ : syracuseStep 42274709 = 1981627) B1981627
theorem B3297185 : Blo 1464552 3297185 := bstep (se 2 (by rfl) ⟨1236444, by rfl⟩ : syracuseStep 3297185 = 2472889) B2472889
theorem B2199479 : Blo 1464552 2199479 := bstep (se 1 (by rfl) ⟨1649609, by rfl⟩ : syracuseStep 2199479 = 3299219) B3299219
theorem B2199515 : Blo 1464552 2199515 := bstep (se 1 (by rfl) ⟨1649636, by rfl⟩ : syracuseStep 2199515 = 3299273) B3299273
theorem B11128913 : Blo 1464552 11128913 := bstep (se 2 (by rfl) ⟨4173342, by rfl⟩ : syracuseStep 11128913 = 8346685) B8346685
theorem B3297527 : Blo 1464552 3297527 := bstep (se 1 (by rfl) ⟨2473145, by rfl⟩ : syracuseStep 3297527 = 4946291) B4946291
theorem B9654589 : Blo 1464552 9654589 := bstep (se 3 (by rfl) ⟨1810235, by rfl⟩ : syracuseStep 9654589 = 3620471) B3620471
theorem B3707279 : Blo 1464552 3707279 := bstep (se 1 (by rfl) ⟨2780459, by rfl⟩ : syracuseStep 3707279 = 5560919) B5560919
theorem B4518287 : Blo 1464552 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B4944347 : Blo 1464552 4944347 := bstep (se 1 (by rfl) ⟨3708260, by rfl⟩ : syracuseStep 4944347 = 7416521) B7416521
theorem B1855963 : Blo 1464552 1855963 := bstep (se 1 (by rfl) ⟨1391972, by rfl⟩ : syracuseStep 1855963 = 2783945) B2783945
theorem B4174345 : Blo 1464552 4174345 := bstep (se 2 (by rfl) ⟨1565379, by rfl⟩ : syracuseStep 4174345 = 3130759) B3130759
theorem B10564121 : Blo 1464552 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B11891225 : Blo 1464552 11891225 := bstep (se 2 (by rfl) ⟨4459209, by rfl⟩ : syracuseStep 11891225 = 8918419) B8918419
theorem B3707603 : Blo 1464552 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B10711763 : Blo 1464552 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B7418627 : Blo 1464552 7418627 := bstep (se 1 (by rfl) ⟨5563970, by rfl⟩ : syracuseStep 7418627 = 11127941) B11127941
theorem B3298121 : Blo 1464552 3298121 := bstep (se 2 (by rfl) ⟨1236795, by rfl⟩ : syracuseStep 3298121 = 2473591) B2473591
theorem B4174699 : Blo 1464552 4174699 := bstep (se 1 (by rfl) ⟨3131024, by rfl⟩ : syracuseStep 4174699 = 6262049) B6262049
theorem B15840305 : Blo 1464552 15840305 := bstep (se 2 (by rfl) ⟨5940114, by rfl⟩ : syracuseStep 15840305 = 11880229) B11880229
theorem B89158805 : Blo 1464552 89158805 := bstep (se 6 (by rfl) ⟨2089659, by rfl⟩ : syracuseStep 89158805 = 4179319) B4179319
theorem B4945049 : Blo 1464552 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B21116477 : Blo 1464552 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B3298913 : Blo 1464552 3298913 := bstep (se 2 (by rfl) ⟨1237092, by rfl⟩ : syracuseStep 3298913 = 2474185) B2474185
theorem B8345227 : Blo 1464552 8345227 := bstep (se 1 (by rfl) ⟨6258920, by rfl⟩ : syracuseStep 8345227 = 12517841) B12517841
theorem B5568209 : Blo 1464552 5568209 := bstep (se 2 (by rfl) ⟨2088078, by rfl⟩ : syracuseStep 5568209 = 4176157) B4176157
theorem B3708767 : Blo 1464552 3708767 := bstep (se 1 (by rfl) ⟨2781575, by rfl⟩ : syracuseStep 3708767 = 5563151) B5563151
theorem B2086831 : Blo 1464552 2086831 := bstep (se 1 (by rfl) ⟨1565123, by rfl⟩ : syracuseStep 2086831 = 3130247) B3130247
theorem B2471863 : Blo 1464552 2471863 := bstep (se 1 (by rfl) ⟨1853897, by rfl⟩ : syracuseStep 2471863 = 3707795) B3707795
theorem B3299255 : Blo 1464552 3299255 := bstep (se 1 (by rfl) ⟨2474441, by rfl⟩ : syracuseStep 3299255 = 4948883) B4948883
theorem B4175803 : Blo 1464552 4175803 := bstep (se 1 (by rfl) ⟨3131852, by rfl⟩ : syracuseStep 4175803 = 6263705) B6263705
theorem B17143757 : Blo 1464552 17143757 := bstep (se 3 (by rfl) ⟨3214454, by rfl⟩ : syracuseStep 17143757 = 6428909) B6428909
theorem B16701389 : Blo 1464552 16701389 := bstep (se 3 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 16701389 = 6263021) B6263021
theorem B2472059 : Blo 1464552 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B3520759 : Blo 1464552 3520759 := bstep (se 1 (by rfl) ⟨2640569, by rfl⟩ : syracuseStep 3520759 = 5281139) B5281139
theorem B1464615 : Blo 1464552 1464615 := bstep (se 1 (by rfl) ⟨1098461, by rfl⟩ : syracuseStep 1464615 = 2196923) B2196923
theorem B4946237 : Blo 1464552 4946237 := bstep (se 3 (by rfl) ⟨927419, by rfl⟩ : syracuseStep 4946237 = 1854839) B1854839
theorem B1464655 : Blo 1464552 1464655 := bstep (se 1 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 1464655 = 2196983) B2196983
theorem B7420247 : Blo 1464552 7420247 := bstep (se 1 (by rfl) ⟨5565185, by rfl⟩ : syracuseStep 7420247 = 11130371) B11130371
theorem B1464671 : Blo 1464552 1464671 := bstep (se 1 (by rfl) ⟨1098503, by rfl⟩ : syracuseStep 1464671 = 2197007) B2197007
theorem B1464699 : Blo 1464552 1464699 := bstep (se 1 (by rfl) ⟨1098524, by rfl⟩ : syracuseStep 1464699 = 2197049) B2197049
theorem B1464751 : Blo 1464552 1464751 := bstep (se 1 (by rfl) ⟨1098563, by rfl⟩ : syracuseStep 1464751 = 2197127) B2197127
theorem B1464775 : Blo 1464552 1464775 := bstep (se 1 (by rfl) ⟨1098581, by rfl⟩ : syracuseStep 1464775 = 2197163) B2197163
theorem B1464795 : Blo 1464552 1464795 := bstep (se 1 (by rfl) ⟨1098596, by rfl⟩ : syracuseStep 1464795 = 2197193) B2197193
theorem B2472457 : Blo 1464552 2472457 := bstep (se 2 (by rfl) ⟨927171, by rfl⟩ : syracuseStep 2472457 = 1854343) B1854343
theorem B7043593 : Blo 1464552 7043593 := bstep (se 2 (by rfl) ⟨2641347, by rfl⟩ : syracuseStep 7043593 = 5282695) B5282695
theorem B1464871 : Blo 1464552 1464871 := bstep (se 1 (by rfl) ⟨1098653, by rfl⟩ : syracuseStep 1464871 = 2197307) B2197307
theorem B2783801 : Blo 1464552 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B1464911 : Blo 1464552 1464911 := bstep (se 1 (by rfl) ⟨1098683, by rfl⟩ : syracuseStep 1464911 = 2197367) B2197367
theorem B1464927 : Blo 1464552 1464927 := bstep (se 1 (by rfl) ⟨1098695, by rfl⟩ : syracuseStep 1464927 = 2197391) B2197391
theorem B1464955 : Blo 1464552 1464955 := bstep (se 1 (by rfl) ⟨1098716, by rfl⟩ : syracuseStep 1464955 = 2197433) B2197433
theorem B8460935 : Blo 1464552 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B2472619 : Blo 1464552 2472619 := bstep (se 1 (by rfl) ⟨1854464, by rfl⟩ : syracuseStep 2472619 = 3708929) B3708929
theorem B1465007 : Blo 1464552 1465007 := bstep (se 1 (by rfl) ⟨1098755, by rfl⟩ : syracuseStep 1465007 = 2197511) B2197511
theorem B1465031 : Blo 1464552 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B2087623 : Blo 1464552 2087623 := bstep (se 1 (by rfl) ⟨1565717, by rfl⟩ : syracuseStep 2087623 = 3131435) B3131435
theorem B1465051 : Blo 1464552 1465051 := bstep (se 1 (by rfl) ⟨1098788, by rfl⟩ : syracuseStep 1465051 = 2197577) B2197577
theorem B1465127 : Blo 1464552 1465127 := bstep (se 1 (by rfl) ⟨1098845, by rfl⟩ : syracuseStep 1465127 = 2197691) B2197691
theorem B1465167 : Blo 1464552 1465167 := bstep (se 1 (by rfl) ⟨1098875, by rfl⟩ : syracuseStep 1465167 = 2197751) B2197751
theorem B1465183 : Blo 1464552 1465183 := bstep (se 1 (by rfl) ⟨1098887, by rfl⟩ : syracuseStep 1465183 = 2197775) B2197775
theorem B5561207 : Blo 1464552 5561207 := bstep (se 1 (by rfl) ⟨4170905, by rfl⟩ : syracuseStep 5561207 = 8341811) B8341811
theorem B1465211 : Blo 1464552 1465211 := bstep (se 1 (by rfl) ⟨1098908, by rfl⟩ : syracuseStep 1465211 = 2197817) B2197817
theorem B4455329 : Blo 1464552 4455329 := bstep (se 2 (by rfl) ⟨1670748, by rfl⟩ : syracuseStep 4455329 = 3341497) B3341497
theorem B1465263 : Blo 1464552 1465263 := bstep (se 1 (by rfl) ⟨1098947, by rfl⟩ : syracuseStep 1465263 = 2197895) B2197895
theorem B3709871 : Blo 1464552 3709871 := bstep (se 1 (by rfl) ⟨2782403, by rfl⟩ : syracuseStep 3709871 = 5564807) B5564807
theorem B1465287 : Blo 1464552 1465287 := bstep (se 1 (by rfl) ⟨1098965, by rfl⟩ : syracuseStep 1465287 = 2197931) B2197931
theorem B1465307 : Blo 1464552 1465307 := bstep (se 1 (by rfl) ⟨1098980, by rfl⟩ : syracuseStep 1465307 = 2197961) B2197961
theorem B2472923 : Blo 1464552 2472923 := bstep (se 1 (by rfl) ⟨1854692, by rfl⟩ : syracuseStep 2472923 = 3709385) B3709385
theorem B1465383 : Blo 1464552 1465383 := bstep (se 1 (by rfl) ⟨1099037, by rfl⟩ : syracuseStep 1465383 = 2198075) B2198075
theorem B11885611 : Blo 1464552 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B3341369 : Blo 1464552 3341369 := bstep (se 2 (by rfl) ⟨1253013, by rfl⟩ : syracuseStep 3341369 = 2506027) B2506027
theorem B1465423 : Blo 1464552 1465423 := bstep (se 1 (by rfl) ⟨1099067, by rfl⟩ : syracuseStep 1465423 = 2198135) B2198135
theorem B1465439 : Blo 1464552 1465439 := bstep (se 1 (by rfl) ⟨1099079, by rfl⟩ : syracuseStep 1465439 = 2198159) B2198159
theorem B1465467 : Blo 1464552 1465467 := bstep (se 1 (by rfl) ⟨1099100, by rfl⟩ : syracuseStep 1465467 = 2198201) B2198201
theorem B4947101 : Blo 1464552 4947101 := bstep (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) B1855163
theorem B1465519 : Blo 1464552 1465519 := bstep (se 1 (by rfl) ⟨1099139, by rfl⟩ : syracuseStep 1465519 = 2198279) B2198279
theorem B1465543 : Blo 1464552 1465543 := bstep (se 1 (by rfl) ⟨1099157, by rfl⟩ : syracuseStep 1465543 = 2198315) B2198315
theorem B2473159 : Blo 1464552 2473159 := bstep (se 1 (by rfl) ⟨1854869, by rfl⟩ : syracuseStep 2473159 = 3709739) B3709739
theorem B1465563 : Blo 1464552 1465563 := bstep (se 1 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 1465563 = 2198345) B2198345
theorem B1465639 : Blo 1464552 1465639 := bstep (se 1 (by rfl) ⟨1099229, by rfl⟩ : syracuseStep 1465639 = 2198459) B2198459
theorem B1465679 : Blo 1464552 1465679 := bstep (se 1 (by rfl) ⟨1099259, by rfl⟩ : syracuseStep 1465679 = 2198519) B2198519
theorem B1465695 : Blo 1464552 1465695 := bstep (se 1 (by rfl) ⟨1099271, by rfl⟩ : syracuseStep 1465695 = 2198543) B2198543
theorem B2473321 : Blo 1464552 2473321 := bstep (se 2 (by rfl) ⟨927495, by rfl⟩ : syracuseStep 2473321 = 1854991) B1854991
theorem B1465723 : Blo 1464552 1465723 := bstep (se 1 (by rfl) ⟨1099292, by rfl⟩ : syracuseStep 1465723 = 2198585) B2198585
theorem B5283215 : Blo 1464552 5283215 := bstep (se 1 (by rfl) ⟨3962411, by rfl⟩ : syracuseStep 5283215 = 7924823) B7924823
theorem B1465775 : Blo 1464552 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B1465799 : Blo 1464552 1465799 := bstep (se 1 (by rfl) ⟨1099349, by rfl⟩ : syracuseStep 1465799 = 2198699) B2198699
theorem B1465819 : Blo 1464552 1465819 := bstep (se 1 (by rfl) ⟨1099364, by rfl⟩ : syracuseStep 1465819 = 2198729) B2198729
theorem B1465895 : Blo 1464552 1465895 := bstep (se 1 (by rfl) ⟨1099421, by rfl⟩ : syracuseStep 1465895 = 2198843) B2198843
theorem B1465935 : Blo 1464552 1465935 := bstep (se 1 (by rfl) ⟨1099451, by rfl⟩ : syracuseStep 1465935 = 2198903) B2198903
theorem B14270039 : Blo 1464552 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B23780951 : Blo 1464552 23780951 := bstep (se 1 (by rfl) ⟨17835713, by rfl⟩ : syracuseStep 23780951 = 35671427) B35671427
theorem B1465951 : Blo 1464552 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B1465979 : Blo 1464552 1465979 := bstep (se 1 (by rfl) ⟨1099484, by rfl⟩ : syracuseStep 1465979 = 2198969) B2198969
theorem B1466031 : Blo 1464552 1466031 := bstep (se 1 (by rfl) ⟨1099523, by rfl⟩ : syracuseStep 1466031 = 2199047) B2199047
theorem B4947641 : Blo 1464552 4947641 := bstep (se 2 (by rfl) ⟨1855365, by rfl⟩ : syracuseStep 4947641 = 3710731) B3710731
theorem B1466055 : Blo 1464552 1466055 := bstep (se 1 (by rfl) ⟨1099541, by rfl⟩ : syracuseStep 1466055 = 2199083) B2199083
theorem B3129043 : Blo 1464552 3129043 := bstep (se 1 (by rfl) ⟨2346782, by rfl⟩ : syracuseStep 3129043 = 4693565) B4693565
theorem B7044823 : Blo 1464552 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B1466075 : Blo 1464552 1466075 := bstep (se 1 (by rfl) ⟨1099556, by rfl⟩ : syracuseStep 1466075 = 2199113) B2199113
theorem B3342073 : Blo 1464552 3342073 := bstep (se 2 (by rfl) ⟨1253277, by rfl⟩ : syracuseStep 3342073 = 2506555) B2506555
theorem B1466151 : Blo 1464552 1466151 := bstep (se 1 (by rfl) ⟨1099613, by rfl⟩ : syracuseStep 1466151 = 2199227) B2199227
theorem B11124539 : Blo 1464552 11124539 := bstep (se 1 (by rfl) ⟨8343404, by rfl⟩ : syracuseStep 11124539 = 16686809) B16686809
theorem B5562179 : Blo 1464552 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B1466191 : Blo 1464552 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B1466207 : Blo 1464552 1466207 := bstep (se 1 (by rfl) ⟨1099655, by rfl⟩ : syracuseStep 1466207 = 2199311) B2199311
theorem B1466235 : Blo 1464552 1466235 := bstep (se 1 (by rfl) ⟨1099676, by rfl⟩ : syracuseStep 1466235 = 2199353) B2199353
theorem B1466287 : Blo 1464552 1466287 := bstep (se 1 (by rfl) ⟨1099715, by rfl⟩ : syracuseStep 1466287 = 2199431) B2199431
theorem B2473915 : Blo 1464552 2473915 := bstep (se 1 (by rfl) ⟨1855436, by rfl⟩ : syracuseStep 2473915 = 3710873) B3710873
theorem B1466311 : Blo 1464552 1466311 := bstep (se 1 (by rfl) ⟨1099733, by rfl⟩ : syracuseStep 1466311 = 2199467) B2199467
theorem B1466331 : Blo 1464552 1466331 := bstep (se 1 (by rfl) ⟨1099748, by rfl⟩ : syracuseStep 1466331 = 2199497) B2199497
theorem B5562377 : Blo 1464552 5562377 := bstep (se 2 (by rfl) ⟨2085891, by rfl⟩ : syracuseStep 5562377 = 4171783) B4171783
theorem B4948073 : Blo 1464552 4948073 := bstep (se 2 (by rfl) ⟨1855527, by rfl⟩ : syracuseStep 4948073 = 3711055) B3711055
theorem B80232677 : Blo 1464552 80232677 := bstep (se 4 (by rfl) ⟨7521813, by rfl⟩ : syracuseStep 80232677 = 15043627) B15043627
theorem B18792755 : Blo 1464552 18792755 := bstep (se 1 (by rfl) ⟨14094566, by rfl⟩ : syracuseStep 18792755 = 28189133) B28189133
theorem B4694345 : Blo 1464552 4694345 := bstep (se 2 (by rfl) ⟨1760379, by rfl⟩ : syracuseStep 4694345 = 3520759) B3520759
theorem B114262481 : Blo 1464552 114262481 := bstep (se 2 (by rfl) ⟨42848430, by rfl⟩ : syracuseStep 114262481 = 85696861) B85696861
theorem B3523027 : Blo 1464552 3523027 := bstep (se 1 (by rfl) ⟨2642270, by rfl⟩ : syracuseStep 3523027 = 5284541) B5284541
theorem B7422515 : Blo 1464552 7422515 := bstep (se 1 (by rfl) ⟨5566886, by rfl⟩ : syracuseStep 7422515 = 11133773) B11133773
theorem B2474617 : Blo 1464552 2474617 := bstep (se 2 (by rfl) ⟨927981, by rfl⟩ : syracuseStep 2474617 = 1855963) B1855963
theorem B6341267 : Blo 1464552 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B2474671 : Blo 1464552 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B10560203 : Blo 1464552 10560203 := bstep (se 1 (by rfl) ⟨7920152, by rfl⟩ : syracuseStep 10560203 = 15840305) B15840305
theorem B23774147 : Blo 1464552 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B4948937 : Blo 1464552 4948937 := bstep (se 2 (by rfl) ⟨1855851, by rfl⟩ : syracuseStep 4948937 = 3711703) B3711703
theorem B63374339 : Blo 1464552 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B3712139 : Blo 1464552 3712139 := bstep (se 1 (by rfl) ⟨2784104, by rfl⟩ : syracuseStep 3712139 = 5568209) B5568209
theorem B4949207 : Blo 1464552 4949207 := bstep (se 1 (by rfl) ⟨3711905, by rfl⟩ : syracuseStep 4949207 = 7423811) B7423811
theorem B3261727 : Blo 1464552 3261727 := bstep (se 1 (by rfl) ⟨2446295, by rfl⟩ : syracuseStep 3261727 = 4892591) B4892591
theorem B11429171 : Blo 1464552 11429171 := bstep (se 1 (by rfl) ⟨8571878, by rfl⟩ : syracuseStep 11429171 = 17143757) B17143757
theorem B11134259 : Blo 1464552 11134259 := bstep (se 1 (by rfl) ⟨8350694, by rfl⟩ : syracuseStep 11134259 = 16701389) B16701389
theorem B1648039 : Blo 1464552 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B2196935 : Blo 1464552 2196935 := bstep (se 1 (by rfl) ⟨1647701, by rfl⟩ : syracuseStep 2196935 = 3295403) B3295403
theorem B8341127 : Blo 1464552 8341127 := bstep (se 1 (by rfl) ⟨6255845, by rfl⟩ : syracuseStep 8341127 = 12511691) B12511691
theorem B2197289 : Blo 1464552 2197289 := bstep (se 2 (by rfl) ⟨823983, by rfl⟩ : syracuseStep 2197289 = 1647967) B1647967
theorem B2197295 : Blo 1464552 2197295 := bstep (se 1 (by rfl) ⟨1647971, by rfl⟩ : syracuseStep 2197295 = 3295943) B3295943
theorem B6260561 : Blo 1464552 6260561 := bstep (se 2 (by rfl) ⟨2347710, by rfl⟩ : syracuseStep 6260561 = 4695421) B4695421
theorem B1648615 : Blo 1464552 1648615 := bstep (se 1 (by rfl) ⟨1236461, by rfl⟩ : syracuseStep 1648615 = 2472923) B2472923
theorem B7424135 : Blo 1464552 7424135 := bstep (se 1 (by rfl) ⟨5568101, by rfl⟩ : syracuseStep 7424135 = 11136203) B11136203
theorem B11126969 : Blo 1464552 11126969 := bstep (se 2 (by rfl) ⟨4172613, by rfl⟩ : syracuseStep 11126969 = 8345227) B8345227
theorem B2197769 : Blo 1464552 2197769 := bstep (se 2 (by rfl) ⟨824163, by rfl⟩ : syracuseStep 2197769 = 1648327) B1648327
theorem B4172057 : Blo 1464552 4172057 := bstep (se 2 (by rfl) ⟨1564521, by rfl⟩ : syracuseStep 4172057 = 3129043) B3129043
theorem B2197871 : Blo 1464552 2197871 := bstep (se 1 (by rfl) ⟨1648403, by rfl⟩ : syracuseStep 2197871 = 3296807) B3296807
theorem B9513359 : Blo 1464552 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B15853967 : Blo 1464552 15853967 := bstep (se 1 (by rfl) ⟨11890475, by rfl⟩ : syracuseStep 15853967 = 23780951) B23780951
theorem B3295655 : Blo 1464552 3295655 := bstep (se 1 (by rfl) ⟨2471741, by rfl⟩ : syracuseStep 3295655 = 4943483) B4943483
theorem B11880877 : Blo 1464552 11880877 := bstep (se 3 (by rfl) ⟨2227664, by rfl⟩ : syracuseStep 11880877 = 4455329) B4455329
theorem B10029523 : Blo 1464552 10029523 := bstep (se 1 (by rfl) ⟨7522142, by rfl⟩ : syracuseStep 10029523 = 15044285) B15044285
theorem B3295763 : Blo 1464552 3295763 := bstep (se 1 (by rfl) ⟨2471822, by rfl⟩ : syracuseStep 3295763 = 4943645) B4943645
theorem B7416359 : Blo 1464552 7416359 := bstep (se 1 (by rfl) ⟨5562269, by rfl⟩ : syracuseStep 7416359 = 11124539) B11124539
theorem B2574919 : Blo 1464552 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B2198087 : Blo 1464552 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B3295817 : Blo 1464552 3295817 := bstep (se 2 (by rfl) ⟨1235931, by rfl⟩ : syracuseStep 3295817 = 2471863) B2471863
theorem B14076503 : Blo 1464552 14076503 := bstep (se 1 (by rfl) ⟨10557377, by rfl⟩ : syracuseStep 14076503 = 21114755) B21114755
theorem B28183139 : Blo 1464552 28183139 := bstep (se 1 (by rfl) ⟨21137354, by rfl⟩ : syracuseStep 28183139 = 42274709) B42274709
theorem B2198123 : Blo 1464552 2198123 := bstep (se 1 (by rfl) ⟨1648592, by rfl⟩ : syracuseStep 2198123 = 3297185) B3297185
theorem B2198351 : Blo 1464552 2198351 := bstep (se 1 (by rfl) ⟨1648763, by rfl⟩ : syracuseStep 2198351 = 3297527) B3297527
theorem B3296231 : Blo 1464552 3296231 := bstep (se 1 (by rfl) ⟨2472173, by rfl⟩ : syracuseStep 3296231 = 4944347) B4944347
theorem B12872785 : Blo 1464552 12872785 := bstep (se 2 (by rfl) ⟨4827294, by rfl⟩ : syracuseStep 12872785 = 9654589) B9654589
theorem B15035507 : Blo 1464552 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B2198747 : Blo 1464552 2198747 := bstep (se 1 (by rfl) ⟨1649060, by rfl⟩ : syracuseStep 2198747 = 3298121) B3298121
theorem B7040287 : Blo 1464552 7040287 := bstep (se 1 (by rfl) ⟨5280215, by rfl⟩ : syracuseStep 7040287 = 10560431) B10560431
theorem B3296609 : Blo 1464552 3296609 := bstep (se 2 (by rfl) ⟨1236228, by rfl⟩ : syracuseStep 3296609 = 2472457) B2472457
theorem B9391457 : Blo 1464552 9391457 := bstep (se 2 (by rfl) ⟨3521796, by rfl⟩ : syracuseStep 9391457 = 7043593) B7043593
theorem B5565793 : Blo 1464552 5565793 := bstep (se 2 (by rfl) ⟨2087172, by rfl⟩ : syracuseStep 5565793 = 4174345) B4174345
theorem B2198921 : Blo 1464552 2198921 := bstep (se 2 (by rfl) ⟨824595, by rfl⟩ : syracuseStep 2198921 = 1649191) B1649191
theorem B3296699 : Blo 1464552 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B4943375 : Blo 1464552 4943375 := bstep (se 1 (by rfl) ⟨3707531, by rfl⟩ : syracuseStep 4943375 = 7415063) B7415063
theorem B3296825 : Blo 1464552 3296825 := bstep (se 2 (by rfl) ⟨1236309, by rfl⟩ : syracuseStep 3296825 = 2472619) B2472619
theorem B5566067 : Blo 1464552 5566067 := bstep (se 1 (by rfl) ⟨4174550, by rfl⟩ : syracuseStep 5566067 = 8349101) B8349101
theorem B14077651 : Blo 1464552 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B2199275 : Blo 1464552 2199275 := bstep (se 1 (by rfl) ⟨1649456, by rfl⟩ : syracuseStep 2199275 = 3298913) B3298913
theorem B2780983 : Blo 1464552 2780983 := bstep (se 1 (by rfl) ⟨2085737, by rfl⟩ : syracuseStep 2780983 = 4171475) B4171475
theorem B5566265 : Blo 1464552 5566265 := bstep (se 2 (by rfl) ⟨2087349, by rfl⟩ : syracuseStep 5566265 = 4174699) B4174699
theorem B8458141 : Blo 1464552 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B2199503 : Blo 1464552 2199503 := bstep (se 1 (by rfl) ⟨1649627, by rfl⟩ : syracuseStep 2199503 = 3299255) B3299255
theorem B15847481 : Blo 1464552 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B3297491 : Blo 1464552 3297491 := bstep (se 1 (by rfl) ⟨2473118, by rfl⟩ : syracuseStep 3297491 = 4946237) B4946237
theorem B3297545 : Blo 1464552 3297545 := bstep (se 2 (by rfl) ⟨1236579, by rfl⟩ : syracuseStep 3297545 = 2473159) B2473159
theorem B1855867 : Blo 1464552 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B5640623 : Blo 1464552 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B3297761 : Blo 1464552 3297761 := bstep (se 2 (by rfl) ⟨1236660, by rfl⟩ : syracuseStep 3297761 = 2473321) B2473321
theorem B4944455 : Blo 1464552 4944455 := bstep (se 1 (by rfl) ⟨3708341, by rfl⟩ : syracuseStep 4944455 = 7416683) B7416683
theorem B3707471 : Blo 1464552 3707471 := bstep (se 1 (by rfl) ⟨2780603, by rfl⟩ : syracuseStep 3707471 = 5561207) B5561207
theorem B7418465 : Blo 1464552 7418465 := bstep (se 2 (by rfl) ⟨2781924, by rfl⟩ : syracuseStep 7418465 = 5563849) B5563849
theorem B2781803 : Blo 1464552 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B3298067 : Blo 1464552 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B9393097 : Blo 1464552 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B2782183 : Blo 1464552 2782183 := bstep (se 1 (by rfl) ⟨2086637, by rfl⟩ : syracuseStep 2782183 = 4173275) B4173275
theorem B4944887 : Blo 1464552 4944887 := bstep (se 1 (by rfl) ⟨3708665, by rfl⟩ : syracuseStep 4944887 = 7417331) B7417331
theorem B1979497 : Blo 1464552 1979497 := bstep (se 2 (by rfl) ⟨742311, by rfl⟩ : syracuseStep 1979497 = 1484623) B1484623
theorem B3298427 : Blo 1464552 3298427 := bstep (se 1 (by rfl) ⟨2473820, by rfl⟩ : syracuseStep 3298427 = 4947641) B4947641
theorem B4174973 : Blo 1464552 4174973 := bstep (se 3 (by rfl) ⟨782807, by rfl⟩ : syracuseStep 4174973 = 1565615) B1565615
theorem B3708119 : Blo 1464552 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B7419113 : Blo 1464552 7419113 := bstep (se 2 (by rfl) ⟨2782167, by rfl⟩ : syracuseStep 7419113 = 5564335) B5564335
theorem B2782441 : Blo 1464552 2782441 := bstep (se 2 (by rfl) ⟨1043415, by rfl⟩ : syracuseStep 2782441 = 2086831) B2086831
theorem B3298553 : Blo 1464552 3298553 := bstep (se 2 (by rfl) ⟨1236957, by rfl⟩ : syracuseStep 3298553 = 2473915) B2473915
theorem B5567737 : Blo 1464552 5567737 := bstep (se 2 (by rfl) ⟨2087901, by rfl⟩ : syracuseStep 5567737 = 4175803) B4175803
theorem B3298697 : Blo 1464552 3298697 := bstep (se 2 (by rfl) ⟨1237011, by rfl⟩ : syracuseStep 3298697 = 2474023) B2474023
theorem B7419275 : Blo 1464552 7419275 := bstep (se 1 (by rfl) ⟨5564456, by rfl⟩ : syracuseStep 7419275 = 11128913) B11128913
theorem B16692641 : Blo 1464552 16692641 := bstep (se 2 (by rfl) ⟨6259740, by rfl⟩ : syracuseStep 16692641 = 12519481) B12519481
theorem B9385409 : Blo 1464552 9385409 := bstep (se 2 (by rfl) ⟨3519528, by rfl⟩ : syracuseStep 9385409 = 7039057) B7039057
theorem B8910317 : Blo 1464552 8910317 := bstep (se 3 (by rfl) ⟨1670684, by rfl⟩ : syracuseStep 8910317 = 3341369) B3341369
theorem B2086393 : Blo 1464552 2086393 := bstep (se 2 (by rfl) ⟨782397, by rfl⟩ : syracuseStep 2086393 = 1564795) B1564795
theorem B3298823 : Blo 1464552 3298823 := bstep (se 1 (by rfl) ⟨2474117, by rfl⟩ : syracuseStep 3298823 = 4948235) B4948235
theorem B2471519 : Blo 1464552 2471519 := bstep (se 1 (by rfl) ⟨1853639, by rfl⟩ : syracuseStep 2471519 = 3707279) B3707279
theorem B3012191 : Blo 1464552 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B28563131 : Blo 1464552 28563131 := bstep (se 1 (by rfl) ⟨21422348, by rfl⟩ : syracuseStep 28563131 = 42844697) B42844697
theorem B3299003 : Blo 1464552 3299003 := bstep (se 1 (by rfl) ⟨2474252, by rfl⟩ : syracuseStep 3299003 = 4948505) B4948505
theorem B7927483 : Blo 1464552 7927483 := bstep (se 1 (by rfl) ⟨5945612, by rfl⟩ : syracuseStep 7927483 = 11891225) B11891225
theorem B2471735 : Blo 1464552 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B7141175 : Blo 1464552 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B3299129 : Blo 1464552 3299129 := bstep (se 2 (by rfl) ⟨1237173, by rfl⟩ : syracuseStep 3299129 = 2474347) B2474347
theorem B4945751 : Blo 1464552 4945751 := bstep (se 1 (by rfl) ⟨3709313, by rfl⟩ : syracuseStep 4945751 = 7418627) B7418627
theorem B48215969 : Blo 1464552 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B59439203 : Blo 1464552 59439203 := bstep (se 1 (by rfl) ⟨44579402, by rfl⟩ : syracuseStep 59439203 = 89158805) B89158805
theorem B2783497 : Blo 1464552 2783497 := bstep (se 2 (by rfl) ⟨1043811, by rfl⟩ : syracuseStep 2783497 = 2087623) B2087623
theorem B1464607 : Blo 1464552 1464607 := bstep (se 1 (by rfl) ⟨1098455, by rfl⟩ : syracuseStep 1464607 = 2196911) B2196911
theorem B1464667 : Blo 1464552 1464667 := bstep (se 1 (by rfl) ⟨1098500, by rfl⟩ : syracuseStep 1464667 = 2197001) B2197001
theorem B1464687 : Blo 1464552 1464687 := bstep (se 1 (by rfl) ⟨1098515, by rfl⟩ : syracuseStep 1464687 = 2197031) B2197031
theorem B1464743 : Blo 1464552 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1464827 : Blo 1464552 1464827 := bstep (se 1 (by rfl) ⟨1098620, by rfl⟩ : syracuseStep 1464827 = 2197241) B2197241
theorem B3709435 : Blo 1464552 3709435 := bstep (se 1 (by rfl) ⟨2782076, by rfl⟩ : syracuseStep 3709435 = 5564153) B5564153
theorem B60971555 : Blo 1464552 60971555 := bstep (se 1 (by rfl) ⟨45728666, by rfl⟩ : syracuseStep 60971555 = 91457333) B91457333
theorem B15047207 : Blo 1464552 15047207 := bstep (se 1 (by rfl) ⟨11285405, by rfl⟩ : syracuseStep 15047207 = 22570811) B22570811
theorem B1464895 : Blo 1464552 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B2472511 : Blo 1464552 2472511 := bstep (se 1 (by rfl) ⟨1854383, by rfl⟩ : syracuseStep 2472511 = 3708767) B3708767
theorem B1464903 : Blo 1464552 1464903 := bstep (se 1 (by rfl) ⟨1098677, by rfl⟩ : syracuseStep 1464903 = 2197355) B2197355
theorem B8346185 : Blo 1464552 8346185 := bstep (se 2 (by rfl) ⟨3129819, by rfl⟩ : syracuseStep 8346185 = 6259639) B6259639
theorem B3709547 : Blo 1464552 3709547 := bstep (se 1 (by rfl) ⟨2782160, by rfl⟩ : syracuseStep 3709547 = 5564321) B5564321
theorem B1465055 : Blo 1464552 1465055 := bstep (se 1 (by rfl) ⟨1098791, by rfl⟩ : syracuseStep 1465055 = 2197583) B2197583
theorem B28170989 : Blo 1464552 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B1465135 : Blo 1464552 1465135 := bstep (se 1 (by rfl) ⟨1098851, by rfl⟩ : syracuseStep 1465135 = 2197703) B2197703
theorem B4946831 : Blo 1464552 4946831 := bstep (se 1 (by rfl) ⟨3710123, by rfl⟩ : syracuseStep 4946831 = 7420247) B7420247
theorem B1465243 : Blo 1464552 1465243 := bstep (se 1 (by rfl) ⟨1098932, by rfl⟩ : syracuseStep 1465243 = 2197865) B2197865
theorem B1465295 : Blo 1464552 1465295 := bstep (se 1 (by rfl) ⟨1098971, by rfl⟩ : syracuseStep 1465295 = 2197943) B2197943
theorem B1465319 : Blo 1464552 1465319 := bstep (se 1 (by rfl) ⟨1098989, by rfl⟩ : syracuseStep 1465319 = 2197979) B2197979
theorem B3972083 : Blo 1464552 3972083 := bstep (se 1 (by rfl) ⟨2979062, by rfl⟩ : syracuseStep 3972083 = 5958125) B5958125
theorem B4693115 : Blo 1464552 4693115 := bstep (se 1 (by rfl) ⟨3519836, by rfl⟩ : syracuseStep 4693115 = 7039673) B7039673
theorem B2473193 : Blo 1464552 2473193 := bstep (se 2 (by rfl) ⟨927447, by rfl⟩ : syracuseStep 2473193 = 1854895) B1854895
theorem B3710195 : Blo 1464552 3710195 := bstep (se 1 (by rfl) ⟨2782646, by rfl⟩ : syracuseStep 3710195 = 5565293) B5565293
theorem B24108299 : Blo 1464552 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B2473247 : Blo 1464552 2473247 := bstep (se 1 (by rfl) ⟨1854935, by rfl⟩ : syracuseStep 2473247 = 3709871) B3709871
theorem B1465631 : Blo 1464552 1465631 := bstep (se 1 (by rfl) ⟨1099223, by rfl⟩ : syracuseStep 1465631 = 2198447) B2198447
theorem B1465691 : Blo 1464552 1465691 := bstep (se 1 (by rfl) ⟨1099268, by rfl⟩ : syracuseStep 1465691 = 2198537) B2198537
theorem B1465711 : Blo 1464552 1465711 := bstep (se 1 (by rfl) ⟨1099283, by rfl⟩ : syracuseStep 1465711 = 2198567) B2198567
theorem B1465767 : Blo 1464552 1465767 := bstep (se 1 (by rfl) ⟨1099325, by rfl⟩ : syracuseStep 1465767 = 2198651) B2198651
theorem B3710407 : Blo 1464552 3710407 := bstep (se 1 (by rfl) ⟨2782805, by rfl⟩ : syracuseStep 3710407 = 5565611) B5565611
theorem B1465851 : Blo 1464552 1465851 := bstep (se 1 (by rfl) ⟨1099388, by rfl⟩ : syracuseStep 1465851 = 2198777) B2198777
theorem B1465919 : Blo 1464552 1465919 := bstep (se 1 (by rfl) ⟨1099439, by rfl⟩ : syracuseStep 1465919 = 2198879) B2198879
theorem B1465927 : Blo 1464552 1465927 := bstep (se 1 (by rfl) ⟨1099445, by rfl⟩ : syracuseStep 1465927 = 2198891) B2198891
theorem B3522143 : Blo 1464552 3522143 := bstep (se 1 (by rfl) ⟨2641607, by rfl⟩ : syracuseStep 3522143 = 5283215) B5283215
theorem B4456097 : Blo 1464552 4456097 := bstep (se 2 (by rfl) ⟨1671036, by rfl⟩ : syracuseStep 4456097 = 3342073) B3342073
theorem B1466079 : Blo 1464552 1466079 := bstep (se 1 (by rfl) ⟨1099559, by rfl⟩ : syracuseStep 1466079 = 2199119) B2199119
theorem B1466159 : Blo 1464552 1466159 := bstep (se 1 (by rfl) ⟨1099619, by rfl⟩ : syracuseStep 1466159 = 2199239) B2199239
theorem B11132801 : Blo 1464552 11132801 := bstep (se 2 (by rfl) ⟨4174800, by rfl⟩ : syracuseStep 11132801 = 8349601) B8349601
theorem B1466267 : Blo 1464552 1466267 := bstep (se 1 (by rfl) ⟨1099700, by rfl⟩ : syracuseStep 1466267 = 2199401) B2199401
theorem B1466319 : Blo 1464552 1466319 := bstep (se 1 (by rfl) ⟨1099739, by rfl⟩ : syracuseStep 1466319 = 2199479) B2199479
theorem B1466343 : Blo 1464552 1466343 := bstep (se 1 (by rfl) ⟨1099757, by rfl⟩ : syracuseStep 1466343 = 2199515) B2199515
theorem B3129563 : Blo 1464552 3129563 := bstep (se 1 (by rfl) ⟨2347172, by rfl⟩ : syracuseStep 3129563 = 4694345) B4694345
theorem B3760415 : Blo 1464552 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B3711329 : Blo 1464552 3711329 := bstep (se 2 (by rfl) ⟨1391748, by rfl⟩ : syracuseStep 3711329 = 2783497) B2783497
theorem B4948343 : Blo 1464552 4948343 := bstep (se 1 (by rfl) ⟨3711257, by rfl⟩ : syracuseStep 4948343 = 7422515) B7422515
theorem B2474489 : Blo 1464552 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B2474759 : Blo 1464552 2474759 := bstep (se 1 (by rfl) ⟨1856069, by rfl⟩ : syracuseStep 2474759 = 3712139) B3712139
theorem B7619447 : Blo 1464552 7619447 := bstep (se 1 (by rfl) ⟨5714585, by rfl⟩ : syracuseStep 7619447 = 11429171) B11429171
theorem B7422839 : Blo 1464552 7422839 := bstep (se 1 (by rfl) ⟨5567129, by rfl⟩ : syracuseStep 7422839 = 11134259) B11134259
theorem B5940211 : Blo 1464552 5940211 := bstep (se 1 (by rfl) ⟨4455158, by rfl⟩ : syracuseStep 5940211 = 8910317) B8910317
theorem B1647679 : Blo 1464552 1647679 := bstep (se 1 (by rfl) ⟨1235759, by rfl⟩ : syracuseStep 1647679 = 2471519) B2471519
theorem B2008127 : Blo 1464552 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B1647823 : Blo 1464552 1647823 := bstep (se 1 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 1647823 = 2471735) B2471735
theorem B4760783 : Blo 1464552 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B39626135 : Blo 1464552 39626135 := bstep (se 1 (by rfl) ⟨29719601, by rfl⟩ : syracuseStep 39626135 = 59439203) B59439203
theorem B4949423 : Blo 1464552 4949423 := bstep (se 1 (by rfl) ⟨3712067, by rfl⟩ : syracuseStep 4949423 = 7424135) B7424135
theorem B17163713 : Blo 1464552 17163713 := bstep (se 2 (by rfl) ⟨6436392, by rfl⟩ : syracuseStep 17163713 = 12872785) B12872785
theorem B6342239 : Blo 1464552 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B10569311 : Blo 1464552 10569311 := bstep (se 1 (by rfl) ⟨7926983, by rfl⟩ : syracuseStep 10569311 = 15853967) B15853967
theorem B2197103 : Blo 1464552 2197103 := bstep (se 1 (by rfl) ⟨1647827, by rfl⟩ : syracuseStep 2197103 = 3295655) B3295655
theorem B7423649 : Blo 1464552 7423649 := bstep (se 2 (by rfl) ⟨2783868, by rfl⟩ : syracuseStep 7423649 = 5567737) B5567737
theorem B2197175 : Blo 1464552 2197175 := bstep (se 1 (by rfl) ⟨1647881, by rfl⟩ : syracuseStep 2197175 = 3295763) B3295763
theorem B2197211 : Blo 1464552 2197211 := bstep (se 1 (by rfl) ⟨1647908, by rfl⟩ : syracuseStep 2197211 = 3295817) B3295817
theorem B5564123 : Blo 1464552 5564123 := bstep (se 1 (by rfl) ⟨4173092, by rfl⟩ : syracuseStep 5564123 = 8346185) B8346185
theorem B16910045 : Blo 1464552 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B2197385 : Blo 1464552 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B2197487 : Blo 1464552 2197487 := bstep (se 1 (by rfl) ⟨1648115, by rfl⟩ : syracuseStep 2197487 = 3296231) B3296231
theorem B1648795 : Blo 1464552 1648795 := bstep (se 1 (by rfl) ⟨1236596, by rfl⟩ : syracuseStep 1648795 = 2473193) B2473193
theorem B1648831 : Blo 1464552 1648831 := bstep (se 1 (by rfl) ⟨1236623, by rfl⟩ : syracuseStep 1648831 = 2473247) B2473247
theorem B2197739 : Blo 1464552 2197739 := bstep (se 1 (by rfl) ⟨1648304, by rfl⟩ : syracuseStep 2197739 = 3296609) B3296609
theorem B6260971 : Blo 1464552 6260971 := bstep (se 1 (by rfl) ⟨4695728, by rfl⟩ : syracuseStep 6260971 = 9391457) B9391457
theorem B10569977 : Blo 1464552 10569977 := bstep (se 2 (by rfl) ⟨3963741, by rfl⟩ : syracuseStep 10569977 = 7927483) B7927483
theorem B18770201 : Blo 1464552 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B2197799 : Blo 1464552 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B3295583 : Blo 1464552 3295583 := bstep (se 1 (by rfl) ⟨2471687, by rfl⟩ : syracuseStep 3295583 = 4943375) B4943375
theorem B2197883 : Blo 1464552 2197883 := bstep (se 1 (by rfl) ⟨1648412, by rfl⟩ : syracuseStep 2197883 = 3296825) B3296825
theorem B2198153 : Blo 1464552 2198153 := bstep (se 2 (by rfl) ⟨824307, by rfl⟩ : syracuseStep 2198153 = 1648615) B1648615
theorem B2198327 : Blo 1464552 2198327 := bstep (se 1 (by rfl) ⟨1648745, by rfl⟩ : syracuseStep 2198327 = 3297491) B3297491
theorem B53488451 : Blo 1464552 53488451 := bstep (se 1 (by rfl) ⟨40116338, by rfl⟩ : syracuseStep 53488451 = 80232677) B80232677
theorem B2198363 : Blo 1464552 2198363 := bstep (se 1 (by rfl) ⟨1648772, by rfl⟩ : syracuseStep 2198363 = 3297545) B3297545
theorem B12528503 : Blo 1464552 12528503 := bstep (se 1 (by rfl) ⟨9396377, by rfl⟩ : syracuseStep 12528503 = 18792755) B18792755
theorem B2198507 : Blo 1464552 2198507 := bstep (se 1 (by rfl) ⟨1648880, by rfl⟩ : syracuseStep 2198507 = 3297761) B3297761
theorem B13732901 : Blo 1464552 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B3296303 : Blo 1464552 3296303 := bstep (se 1 (by rfl) ⟨2472227, by rfl⟩ : syracuseStep 3296303 = 4944455) B4944455
theorem B7040135 : Blo 1464552 7040135 := bstep (se 1 (by rfl) ⟨5280101, by rfl⟩ : syracuseStep 7040135 = 10560203) B10560203
theorem B2198711 : Blo 1464552 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B13372697 : Blo 1464552 13372697 := bstep (se 2 (by rfl) ⟨5014761, by rfl⟩ : syracuseStep 13372697 = 10029523) B10029523
theorem B4697369 : Blo 1464552 4697369 := bstep (se 2 (by rfl) ⟨1761513, by rfl⟩ : syracuseStep 4697369 = 3523027) B3523027
theorem B3296591 : Blo 1464552 3296591 := bstep (se 1 (by rfl) ⟨2472443, by rfl⟩ : syracuseStep 3296591 = 4944887) B4944887
theorem B42249559 : Blo 1464552 42249559 := bstep (se 1 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 42249559 = 63374339) B63374339
theorem B2198951 : Blo 1464552 2198951 := bstep (se 1 (by rfl) ⟨1649213, by rfl⟩ : syracuseStep 2198951 = 3298427) B3298427
theorem B3296681 : Blo 1464552 3296681 := bstep (se 2 (by rfl) ⟨1236255, by rfl⟩ : syracuseStep 3296681 = 2472511) B2472511
theorem B2199035 : Blo 1464552 2199035 := bstep (se 1 (by rfl) ⟨1649276, by rfl⟩ : syracuseStep 2199035 = 3298553) B3298553
theorem B2199131 : Blo 1464552 2199131 := bstep (se 1 (by rfl) ⟨1649348, by rfl⟩ : syracuseStep 2199131 = 3298697) B3298697
theorem B11128427 : Blo 1464552 11128427 := bstep (se 1 (by rfl) ⟨8346320, by rfl⟩ : syracuseStep 11128427 = 16692641) B16692641
theorem B2199215 : Blo 1464552 2199215 := bstep (se 1 (by rfl) ⟨1649411, by rfl⟩ : syracuseStep 2199215 = 3298823) B3298823
theorem B19042087 : Blo 1464552 19042087 := bstep (se 1 (by rfl) ⟨14281565, by rfl⟩ : syracuseStep 19042087 = 28563131) B28563131
theorem B2199335 : Blo 1464552 2199335 := bstep (se 1 (by rfl) ⟨1649501, by rfl⟩ : syracuseStep 2199335 = 3299003) B3299003
theorem B2199419 : Blo 1464552 2199419 := bstep (se 1 (by rfl) ⟨1649564, by rfl⟩ : syracuseStep 2199419 = 3299129) B3299129
theorem B4173707 : Blo 1464552 4173707 := bstep (se 1 (by rfl) ⟨3130280, by rfl⟩ : syracuseStep 4173707 = 6260561) B6260561
theorem B3297167 : Blo 1464552 3297167 := bstep (se 1 (by rfl) ⟨2472875, by rfl⟩ : syracuseStep 3297167 = 4945751) B4945751
theorem B7417979 : Blo 1464552 7417979 := bstep (se 1 (by rfl) ⟨5563484, by rfl⟩ : syracuseStep 7417979 = 11126969) B11126969
theorem B17395877 : Blo 1464552 17395877 := bstep (se 4 (by rfl) ⟨1630863, by rfl⟩ : syracuseStep 17395877 = 3261727) B3261727
theorem B2781371 : Blo 1464552 2781371 := bstep (se 1 (by rfl) ⟨2086028, by rfl⟩ : syracuseStep 2781371 = 4172057) B4172057
theorem B9392381 : Blo 1464552 9392381 := bstep (se 3 (by rfl) ⟨1761071, by rfl⟩ : syracuseStep 9392381 = 3522143) B3522143
theorem B7418141 : Blo 1464552 7418141 := bstep (se 3 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 7418141 = 2781803) B2781803
theorem B4944239 : Blo 1464552 4944239 := bstep (se 1 (by rfl) ⟨3708179, by rfl⟩ : syracuseStep 4944239 = 7416359) B7416359
theorem B10031471 : Blo 1464552 10031471 := bstep (se 1 (by rfl) ⟨7523603, by rfl⟩ : syracuseStep 10031471 = 15047207) B15047207
theorem B9384335 : Blo 1464552 9384335 := bstep (se 1 (by rfl) ⟨7038251, by rfl⟩ : syracuseStep 9384335 = 14076503) B14076503
theorem B18788759 : Blo 1464552 18788759 := bstep (se 1 (by rfl) ⟨14091569, by rfl⟩ : syracuseStep 18788759 = 28183139) B28183139
theorem B18780659 : Blo 1464552 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B3297887 : Blo 1464552 3297887 := bstep (se 1 (by rfl) ⟨2473415, by rfl⟩ : syracuseStep 3297887 = 4946831) B4946831
theorem B2781857 : Blo 1464552 2781857 := bstep (se 2 (by rfl) ⟨1043196, by rfl⟩ : syracuseStep 2781857 = 2086393) B2086393
theorem B10023671 : Blo 1464552 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B3707977 : Blo 1464552 3707977 := bstep (se 2 (by rfl) ⟨1390491, by rfl⟩ : syracuseStep 3707977 = 2780983) B2780983
theorem B2970731 : Blo 1464552 2970731 := bstep (se 1 (by rfl) ⟨2228048, by rfl⟩ : syracuseStep 2970731 = 4456097) B4456097
theorem B11277521 : Blo 1464552 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B3708251 : Blo 1464552 3708251 := bstep (se 1 (by rfl) ⟨2781188, by rfl⟩ : syracuseStep 3708251 = 5562377) B5562377
theorem B10564987 : Blo 1464552 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B3298715 : Blo 1464552 3298715 := bstep (se 1 (by rfl) ⟨2474036, by rfl⟩ : syracuseStep 3298715 = 4948073) B4948073
theorem B76174987 : Blo 1464552 76174987 := bstep (se 1 (by rfl) ⟨57131240, by rfl⟩ : syracuseStep 76174987 = 114262481) B114262481
theorem B2471647 : Blo 1464552 2471647 := bstep (se 1 (by rfl) ⟨1853735, by rfl⟩ : syracuseStep 2471647 = 3707471) B3707471
theorem B4945643 : Blo 1464552 4945643 := bstep (se 1 (by rfl) ⟨3709232, by rfl⟩ : syracuseStep 4945643 = 7418465) B7418465
theorem B10557317 : Blo 1464552 10557317 := bstep (se 4 (by rfl) ⟨989748, by rfl⟩ : syracuseStep 10557317 = 1979497) B1979497
theorem B15841169 : Blo 1464552 15841169 := bstep (se 2 (by rfl) ⟨5940438, by rfl⟩ : syracuseStep 15841169 = 11880877) B11880877
theorem B15849431 : Blo 1464552 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B3299291 : Blo 1464552 3299291 := bstep (se 1 (by rfl) ⟨2474468, by rfl⟩ : syracuseStep 3299291 = 4948937) B4948937
theorem B4945913 : Blo 1464552 4945913 := bstep (se 2 (by rfl) ⟨1854717, by rfl⟩ : syracuseStep 4945913 = 3709435) B3709435
theorem B2783315 : Blo 1464552 2783315 := bstep (se 1 (by rfl) ⟨2087486, by rfl⟩ : syracuseStep 2783315 = 4174973) B4174973
theorem B2472079 : Blo 1464552 2472079 := bstep (se 1 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 2472079 = 3708119) B3708119
theorem B3299471 : Blo 1464552 3299471 := bstep (se 1 (by rfl) ⟨2474603, by rfl⟩ : syracuseStep 3299471 = 4949207) B4949207
theorem B4946075 : Blo 1464552 4946075 := bstep (se 1 (by rfl) ⟨3709556, by rfl⟩ : syracuseStep 4946075 = 7419113) B7419113
theorem B3299489 : Blo 1464552 3299489 := bstep (se 2 (by rfl) ⟨1237308, by rfl⟩ : syracuseStep 3299489 = 2474617) B2474617
theorem B3299561 : Blo 1464552 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B4946183 : Blo 1464552 4946183 := bstep (se 1 (by rfl) ⟨3709637, by rfl⟩ : syracuseStep 4946183 = 7419275) B7419275
theorem B6256939 : Blo 1464552 6256939 := bstep (se 1 (by rfl) ⟨4692704, by rfl⟩ : syracuseStep 6256939 = 9385409) B9385409
theorem B1464623 : Blo 1464552 1464623 := bstep (se 1 (by rfl) ⟨1098467, by rfl⟩ : syracuseStep 1464623 = 2196935) B2196935
theorem B5560751 : Blo 1464552 5560751 := bstep (se 1 (by rfl) ⟨4170563, by rfl⟩ : syracuseStep 5560751 = 8341127) B8341127
theorem B1464859 : Blo 1464552 1464859 := bstep (se 1 (by rfl) ⟨1098644, by rfl⟩ : syracuseStep 1464859 = 2197289) B2197289
theorem B1464863 : Blo 1464552 1464863 := bstep (se 1 (by rfl) ⟨1098647, by rfl⟩ : syracuseStep 1464863 = 2197295) B2197295
theorem B12524129 : Blo 1464552 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B32143979 : Blo 1464552 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B3709577 : Blo 1464552 3709577 := bstep (se 2 (by rfl) ⟨1391091, by rfl⟩ : syracuseStep 3709577 = 2782183) B2782183
theorem B1465179 : Blo 1464552 1465179 := bstep (se 1 (by rfl) ⟨1098884, by rfl⟩ : syracuseStep 1465179 = 2197769) B2197769
theorem B1465247 : Blo 1464552 1465247 := bstep (se 1 (by rfl) ⟨1098935, by rfl⟩ : syracuseStep 1465247 = 2197871) B2197871
theorem B3709921 : Blo 1464552 3709921 := bstep (se 2 (by rfl) ⟨1391220, by rfl⟩ : syracuseStep 3709921 = 2782441) B2782441
theorem B40647703 : Blo 1464552 40647703 := bstep (se 1 (by rfl) ⟨30485777, by rfl⟩ : syracuseStep 40647703 = 60971555) B60971555
theorem B9387049 : Blo 1464552 9387049 := bstep (se 2 (by rfl) ⟨3520143, by rfl⟩ : syracuseStep 9387049 = 7040287) B7040287
theorem B1465391 : Blo 1464552 1465391 := bstep (se 1 (by rfl) ⟨1099043, by rfl⟩ : syracuseStep 1465391 = 2198087) B2198087
theorem B1465415 : Blo 1464552 1465415 := bstep (se 1 (by rfl) ⟨1099061, by rfl⟩ : syracuseStep 1465415 = 2198123) B2198123
theorem B2473031 : Blo 1464552 2473031 := bstep (se 1 (by rfl) ⟨1854773, by rfl⟩ : syracuseStep 2473031 = 3709547) B3709547
theorem B7421057 : Blo 1464552 7421057 := bstep (se 2 (by rfl) ⟨2782896, by rfl⟩ : syracuseStep 7421057 = 5565793) B5565793
theorem B1465567 : Blo 1464552 1465567 := bstep (se 1 (by rfl) ⟨1099175, by rfl⟩ : syracuseStep 1465567 = 2198351) B2198351
theorem B4947209 : Blo 1464552 4947209 := bstep (se 2 (by rfl) ⟨1855203, by rfl⟩ : syracuseStep 4947209 = 3710407) B3710407
theorem B3128743 : Blo 1464552 3128743 := bstep (se 1 (by rfl) ⟨2346557, by rfl⟩ : syracuseStep 3128743 = 4693115) B4693115
theorem B1465831 : Blo 1464552 1465831 := bstep (se 1 (by rfl) ⟨1099373, by rfl⟩ : syracuseStep 1465831 = 2198747) B2198747
theorem B2473463 : Blo 1464552 2473463 := bstep (se 1 (by rfl) ⟨1855097, by rfl⟩ : syracuseStep 2473463 = 3710195) B3710195
theorem B16072199 : Blo 1464552 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B1465947 : Blo 1464552 1465947 := bstep (se 1 (by rfl) ⟨1099460, by rfl⟩ : syracuseStep 1465947 = 2198921) B2198921
theorem B3710711 : Blo 1464552 3710711 := bstep (se 1 (by rfl) ⟨2783033, by rfl⟩ : syracuseStep 3710711 = 5566067) B5566067
theorem B1466183 : Blo 1464552 1466183 := bstep (se 1 (by rfl) ⟨1099637, by rfl⟩ : syracuseStep 1466183 = 2199275) B2199275
theorem B42368885 : Blo 1464552 42368885 := bstep (se 5 (by rfl) ⟨1986041, by rfl⟩ : syracuseStep 42368885 = 3972083) B3972083
theorem B3710843 : Blo 1464552 3710843 := bstep (se 1 (by rfl) ⟨2783132, by rfl⟩ : syracuseStep 3710843 = 5566265) B5566265
theorem B7421867 : Blo 1464552 7421867 := bstep (se 1 (by rfl) ⟨5566400, by rfl⟩ : syracuseStep 7421867 = 11132801) B11132801
theorem B1466335 : Blo 1464552 1466335 := bstep (se 1 (by rfl) ⟨1099751, by rfl⟩ : syracuseStep 1466335 = 2199503) B2199503
theorem B2506943 : Blo 1464552 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B2474219 : Blo 1464552 2474219 := bstep (se 1 (by rfl) ⟨1855664, by rfl⟩ : syracuseStep 2474219 = 3711329) B3711329
theorem B12525839 : Blo 1464552 12525839 := bstep (se 1 (by rfl) ⟨9394379, by rfl⟩ : syracuseStep 12525839 = 18788759) B18788759
theorem B8347961 : Blo 1464552 8347961 := bstep (se 2 (by rfl) ⟨3130485, by rfl⟩ : syracuseStep 8347961 = 6260971) B6260971
theorem B5079631 : Blo 1464552 5079631 := bstep (se 1 (by rfl) ⟨3809723, by rfl⟩ : syracuseStep 5079631 = 7619447) B7619447
theorem B4948559 : Blo 1464552 4948559 := bstep (se 1 (by rfl) ⟨3711419, by rfl⟩ : syracuseStep 4948559 = 7422839) B7422839
theorem B4228159 : Blo 1464552 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B7046207 : Blo 1464552 7046207 := bstep (se 1 (by rfl) ⟨5284655, by rfl⟩ : syracuseStep 7046207 = 10569311) B10569311
theorem B4949099 : Blo 1464552 4949099 := bstep (se 1 (by rfl) ⟨3711824, by rfl⟩ : syracuseStep 4949099 = 7423649) B7423649
theorem B11273363 : Blo 1464552 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B7038211 : Blo 1464552 7038211 := bstep (se 1 (by rfl) ⟨5278658, by rfl⟩ : syracuseStep 7038211 = 10557317) B10557317
theorem B10560779 : Blo 1464552 10560779 := bstep (se 1 (by rfl) ⟨7920584, by rfl⟩ : syracuseStep 10560779 = 15841169) B15841169
theorem B2196905 : Blo 1464552 2196905 := bstep (se 2 (by rfl) ⟨823839, by rfl⟩ : syracuseStep 2196905 = 1647679) B1647679
theorem B7046651 : Blo 1464552 7046651 := bstep (se 1 (by rfl) ⟨5284988, by rfl⟩ : syracuseStep 7046651 = 10569977) B10569977
theorem B2197055 : Blo 1464552 2197055 := bstep (se 1 (by rfl) ⟨1647791, by rfl⟩ : syracuseStep 2197055 = 3295583) B3295583
theorem B2197097 : Blo 1464552 2197097 := bstep (se 2 (by rfl) ⟨823911, by rfl⟩ : syracuseStep 2197097 = 1647823) B1647823
theorem B8349419 : Blo 1464552 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B4171657 : Blo 1464552 4171657 := bstep (se 2 (by rfl) ⟨1564371, by rfl⟩ : syracuseStep 4171657 = 3128743) B3128743
theorem B2197535 : Blo 1464552 2197535 := bstep (se 1 (by rfl) ⟨1648151, by rfl⟩ : syracuseStep 2197535 = 3296303) B3296303
theorem B1648687 : Blo 1464552 1648687 := bstep (se 1 (by rfl) ⟨1236515, by rfl⟩ : syracuseStep 1648687 = 2473031) B2473031
theorem B101566649 : Blo 1464552 101566649 := bstep (se 2 (by rfl) ⟨38087493, by rfl⟩ : syracuseStep 101566649 = 76174987) B76174987
theorem B8915131 : Blo 1464552 8915131 := bstep (se 1 (by rfl) ⟨6686348, by rfl⟩ : syracuseStep 8915131 = 13372697) B13372697
theorem B3131579 : Blo 1464552 3131579 := bstep (se 1 (by rfl) ⟨2348684, by rfl⟩ : syracuseStep 3131579 = 4697369) B4697369
theorem B2197727 : Blo 1464552 2197727 := bstep (se 1 (by rfl) ⟨1648295, by rfl⟩ : syracuseStep 2197727 = 3296591) B3296591
theorem B2197787 : Blo 1464552 2197787 := bstep (se 1 (by rfl) ⟨1648340, by rfl⟩ : syracuseStep 2197787 = 3296681) B3296681
theorem B3295529 : Blo 1464552 3295529 := bstep (se 2 (by rfl) ⟨1235823, by rfl⟩ : syracuseStep 3295529 = 2471647) B2471647
theorem B1648975 : Blo 1464552 1648975 := bstep (se 1 (by rfl) ⟨1236731, by rfl⟩ : syracuseStep 1648975 = 2473463) B2473463
theorem B25389449 : Blo 1464552 25389449 := bstep (se 2 (by rfl) ⟨9521043, by rfl⟩ : syracuseStep 25389449 = 19042087) B19042087
theorem B2198111 : Blo 1464552 2198111 := bstep (se 1 (by rfl) ⟨1648583, by rfl⟩ : syracuseStep 2198111 = 3297167) B3297167
theorem B1854247 : Blo 1464552 1854247 := bstep (se 1 (by rfl) ⟨1390685, by rfl⟩ : syracuseStep 1854247 = 2781371) B2781371
theorem B6261587 : Blo 1464552 6261587 := bstep (se 1 (by rfl) ⟨4696190, by rfl⟩ : syracuseStep 6261587 = 9392381) B9392381
theorem B3296105 : Blo 1464552 3296105 := bstep (se 2 (by rfl) ⟨1236039, by rfl⟩ : syracuseStep 3296105 = 2472079) B2472079
theorem B2198393 : Blo 1464552 2198393 := bstep (se 2 (by rfl) ⟨824397, by rfl⟩ : syracuseStep 2198393 = 1648795) B1648795
theorem B3296159 : Blo 1464552 3296159 := bstep (se 1 (by rfl) ⟨2472119, by rfl⟩ : syracuseStep 3296159 = 4944239) B4944239
theorem B6687647 : Blo 1464552 6687647 := bstep (se 1 (by rfl) ⟨5015735, by rfl⟩ : syracuseStep 6687647 = 10031471) B10031471
theorem B2198441 : Blo 1464552 2198441 := bstep (se 2 (by rfl) ⟨824415, by rfl⟩ : syracuseStep 2198441 = 1648831) B1648831
theorem B12520439 : Blo 1464552 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B1649659 : Blo 1464552 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B8342585 : Blo 1464552 8342585 := bstep (se 2 (by rfl) ⟨3128469, by rfl⟩ : syracuseStep 8342585 = 6256939) B6256939
theorem B2198591 : Blo 1464552 2198591 := bstep (se 1 (by rfl) ⟨1648943, by rfl⟩ : syracuseStep 2198591 = 3297887) B3297887
theorem B1854571 : Blo 1464552 1854571 := bstep (se 1 (by rfl) ⟨1390928, by rfl⟩ : syracuseStep 1854571 = 2781857) B2781857
theorem B1649839 : Blo 1464552 1649839 := bstep (se 1 (by rfl) ⟨1237379, by rfl⟩ : syracuseStep 1649839 = 2474759) B2474759
theorem B3173855 : Blo 1464552 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B2199143 : Blo 1464552 2199143 := bstep (se 1 (by rfl) ⟨1649357, by rfl⟩ : syracuseStep 2199143 = 3298715) B3298715
theorem B3297095 : Blo 1464552 3297095 := bstep (se 1 (by rfl) ⟨2472821, by rfl⟩ : syracuseStep 3297095 = 4945643) B4945643
theorem B2199527 : Blo 1464552 2199527 := bstep (se 1 (by rfl) ⟨1649645, by rfl⟩ : syracuseStep 2199527 = 3299291) B3299291
theorem B3297275 : Blo 1464552 3297275 := bstep (se 1 (by rfl) ⟨2472956, by rfl⟩ : syracuseStep 3297275 = 4945913) B4945913
theorem B1855543 : Blo 1464552 1855543 := bstep (se 1 (by rfl) ⟨1391657, by rfl⟩ : syracuseStep 1855543 = 2783315) B2783315
theorem B2199647 : Blo 1464552 2199647 := bstep (se 1 (by rfl) ⟨1649735, by rfl⟩ : syracuseStep 2199647 = 3299471) B3299471
theorem B4943969 : Blo 1464552 4943969 := bstep (se 2 (by rfl) ⟨1853988, by rfl⟩ : syracuseStep 4943969 = 3707977) B3707977
theorem B3297383 : Blo 1464552 3297383 := bstep (se 1 (by rfl) ⟨2473037, by rfl⟩ : syracuseStep 3297383 = 4946075) B4946075
theorem B2199659 : Blo 1464552 2199659 := bstep (se 1 (by rfl) ⟨1649744, by rfl⟩ : syracuseStep 2199659 = 3299489) B3299489
theorem B2199707 : Blo 1464552 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B3297455 : Blo 1464552 3297455 := bstep (se 1 (by rfl) ⟨2473091, by rfl⟩ : syracuseStep 3297455 = 4946183) B4946183
theorem B12513467 : Blo 1464552 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B3707167 : Blo 1464552 3707167 := bstep (se 1 (by rfl) ⟨2780375, by rfl⟩ : syracuseStep 3707167 = 5560751) B5560751
theorem B56332745 : Blo 1464552 56332745 := bstep (se 2 (by rfl) ⟨21124779, by rfl⟩ : syracuseStep 56332745 = 42249559) B42249559
theorem B14086649 : Blo 1464552 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B8352335 : Blo 1464552 8352335 := bstep (se 1 (by rfl) ⟨6264251, by rfl⟩ : syracuseStep 8352335 = 12528503) B12528503
theorem B9155267 : Blo 1464552 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B3298139 : Blo 1464552 3298139 := bstep (se 1 (by rfl) ⟨2473604, by rfl⟩ : syracuseStep 3298139 = 4947209) B4947209
theorem B11129885 : Blo 1464552 11129885 := bstep (se 3 (by rfl) ⟨2086853, by rfl⟩ : syracuseStep 11129885 = 4173707) B4173707
theorem B7418951 : Blo 1464552 7418951 := bstep (se 1 (by rfl) ⟨5564213, by rfl⟩ : syracuseStep 7418951 = 11128427) B11128427
theorem B4945319 : Blo 1464552 4945319 := bstep (se 1 (by rfl) ⟨3708989, by rfl⟩ : syracuseStep 4945319 = 7417979) B7417979
theorem B11597251 : Blo 1464552 11597251 := bstep (se 1 (by rfl) ⟨8697938, by rfl⟩ : syracuseStep 11597251 = 17395877) B17395877
theorem B5355005 : Blo 1464552 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B4945427 : Blo 1464552 4945427 := bstep (se 1 (by rfl) ⟨3709070, by rfl⟩ : syracuseStep 4945427 = 7418141) B7418141
theorem B3298895 : Blo 1464552 3298895 := bstep (se 1 (by rfl) ⟨2474171, by rfl⟩ : syracuseStep 3298895 = 4948343) B4948343
theorem B6256223 : Blo 1464552 6256223 := bstep (se 1 (by rfl) ⟨4692167, by rfl⟩ : syracuseStep 6256223 = 9384335) B9384335
theorem B6682447 : Blo 1464552 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B8345501 : Blo 1464552 8345501 := bstep (se 3 (by rfl) ⟨1564781, by rfl⟩ : syracuseStep 8345501 = 3129563) B3129563
theorem B1980487 : Blo 1464552 1980487 := bstep (se 1 (by rfl) ⟨1485365, by rfl⟩ : syracuseStep 1980487 = 2970731) B2970731
theorem B7518347 : Blo 1464552 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B2472167 : Blo 1464552 2472167 := bstep (se 1 (by rfl) ⟨1854125, by rfl⟩ : syracuseStep 2472167 = 3708251) B3708251
theorem B26417423 : Blo 1464552 26417423 := bstep (se 1 (by rfl) ⟨19813067, by rfl⟩ : syracuseStep 26417423 = 39626135) B39626135
theorem B3299615 : Blo 1464552 3299615 := bstep (se 1 (by rfl) ⟨2474711, by rfl⟩ : syracuseStep 3299615 = 4949423) B4949423
theorem B11442475 : Blo 1464552 11442475 := bstep (se 1 (by rfl) ⟨8581856, by rfl⟩ : syracuseStep 11442475 = 17163713) B17163713
theorem B1464735 : Blo 1464552 1464735 := bstep (se 1 (by rfl) ⟨1098551, by rfl⟩ : syracuseStep 1464735 = 2197103) B2197103
theorem B1464783 : Blo 1464552 1464783 := bstep (se 1 (by rfl) ⟨1098587, by rfl⟩ : syracuseStep 1464783 = 2197175) B2197175
theorem B1464807 : Blo 1464552 1464807 := bstep (se 1 (by rfl) ⟨1098605, by rfl⟩ : syracuseStep 1464807 = 2197211) B2197211
theorem B3709415 : Blo 1464552 3709415 := bstep (se 1 (by rfl) ⟨2782061, by rfl⟩ : syracuseStep 3709415 = 5564123) B5564123
theorem B1464923 : Blo 1464552 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B4946561 : Blo 1464552 4946561 := bstep (se 2 (by rfl) ⟨1854960, by rfl⟩ : syracuseStep 4946561 = 3709921) B3709921
theorem B10566287 : Blo 1464552 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B7920281 : Blo 1464552 7920281 := bstep (se 2 (by rfl) ⟨2970105, by rfl⟩ : syracuseStep 7920281 = 5940211) B5940211
theorem B1464991 : Blo 1464552 1464991 := bstep (se 1 (by rfl) ⟨1098743, by rfl⟩ : syracuseStep 1464991 = 2197487) B2197487
theorem B54196937 : Blo 1464552 54196937 := bstep (se 2 (by rfl) ⟨20323851, by rfl⟩ : syracuseStep 54196937 = 40647703) B40647703
theorem B12516065 : Blo 1464552 12516065 := bstep (se 2 (by rfl) ⟨4693524, by rfl⟩ : syracuseStep 12516065 = 9387049) B9387049
theorem B1465159 : Blo 1464552 1465159 := bstep (se 1 (by rfl) ⟨1098869, by rfl⟩ : syracuseStep 1465159 = 2197739) B2197739
theorem B1465199 : Blo 1464552 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B1465255 : Blo 1464552 1465255 := bstep (se 1 (by rfl) ⟨1098941, by rfl⟩ : syracuseStep 1465255 = 2197883) B2197883
theorem B21429319 : Blo 1464552 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B1465435 : Blo 1464552 1465435 := bstep (se 1 (by rfl) ⟨1099076, by rfl⟩ : syracuseStep 1465435 = 2198153) B2198153
theorem B2473051 : Blo 1464552 2473051 := bstep (se 1 (by rfl) ⟨1854788, by rfl⟩ : syracuseStep 2473051 = 3709577) B3709577
theorem B1465551 : Blo 1464552 1465551 := bstep (se 1 (by rfl) ⟨1099163, by rfl⟩ : syracuseStep 1465551 = 2198327) B2198327
theorem B35658967 : Blo 1464552 35658967 := bstep (se 1 (by rfl) ⟨26744225, by rfl⟩ : syracuseStep 35658967 = 53488451) B53488451
theorem B1465575 : Blo 1464552 1465575 := bstep (se 1 (by rfl) ⟨1099181, by rfl⟩ : syracuseStep 1465575 = 2198363) B2198363
theorem B1465671 : Blo 1464552 1465671 := bstep (se 1 (by rfl) ⟨1099253, by rfl⟩ : syracuseStep 1465671 = 2198507) B2198507
theorem B4947371 : Blo 1464552 4947371 := bstep (se 1 (by rfl) ⟨3710528, by rfl⟩ : syracuseStep 4947371 = 7421057) B7421057
theorem B4693423 : Blo 1464552 4693423 := bstep (se 1 (by rfl) ⟨3520067, by rfl⟩ : syracuseStep 4693423 = 7040135) B7040135
theorem B1465807 : Blo 1464552 1465807 := bstep (se 1 (by rfl) ⟨1099355, by rfl⟩ : syracuseStep 1465807 = 2198711) B2198711
theorem B1465967 : Blo 1464552 1465967 := bstep (se 1 (by rfl) ⟨1099475, by rfl⟩ : syracuseStep 1465967 = 2198951) B2198951
theorem B1466023 : Blo 1464552 1466023 := bstep (se 1 (by rfl) ⟨1099517, by rfl⟩ : syracuseStep 1466023 = 2199035) B2199035
theorem B10714799 : Blo 1464552 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B1466087 : Blo 1464552 1466087 := bstep (se 1 (by rfl) ⟨1099565, by rfl⟩ : syracuseStep 1466087 = 2199131) B2199131
theorem B1466143 : Blo 1464552 1466143 := bstep (se 1 (by rfl) ⟨1099607, by rfl⟩ : syracuseStep 1466143 = 2199215) B2199215
theorem B2473807 : Blo 1464552 2473807 := bstep (se 1 (by rfl) ⟨1855355, by rfl⟩ : syracuseStep 2473807 = 3710711) B3710711
theorem B1466223 : Blo 1464552 1466223 := bstep (se 1 (by rfl) ⟨1099667, by rfl⟩ : syracuseStep 1466223 = 2199335) B2199335
theorem B28245923 : Blo 1464552 28245923 := bstep (se 1 (by rfl) ⟨21184442, by rfl⟩ : syracuseStep 28245923 = 42368885) B42368885
theorem B2473895 : Blo 1464552 2473895 := bstep (se 1 (by rfl) ⟨1855421, by rfl⟩ : syracuseStep 2473895 = 3710843) B3710843
theorem B1466279 : Blo 1464552 1466279 := bstep (se 1 (by rfl) ⟨1099709, by rfl⟩ : syracuseStep 1466279 = 2199419) B2199419
theorem B4947911 : Blo 1464552 4947911 := bstep (se 1 (by rfl) ⟨3710933, by rfl⟩ : syracuseStep 4947911 = 7421867) B7421867
theorem B1466431 : Blo 1464552 1466431 := bstep (se 1 (by rfl) ⟨1099823, by rfl⟩ : syracuseStep 1466431 = 2199647) B2199647
theorem B1466439 : Blo 1464552 1466439 := bstep (se 1 (by rfl) ⟨1099829, by rfl⟩ : syracuseStep 1466439 = 2199659) B2199659
theorem B2474057 : Blo 1464552 2474057 := bstep (se 2 (by rfl) ⟨927771, by rfl⟩ : syracuseStep 2474057 = 1855543) B1855543
theorem B1466471 : Blo 1464552 1466471 := bstep (se 1 (by rfl) ⟨1099853, by rfl⟩ : syracuseStep 1466471 = 2199707) B2199707
theorem B11886841 : Blo 1464552 11886841 := bstep (se 2 (by rfl) ⟨4457565, by rfl⟩ : syracuseStep 11886841 = 8915131) B8915131
theorem B6103511 : Blo 1464552 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B6685181 : Blo 1464552 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B4170815 : Blo 1464552 4170815 := bstep (se 1 (by rfl) ⟨3128111, by rfl⟩ : syracuseStep 4170815 = 6256223) B6256223
theorem B5563667 : Blo 1464552 5563667 := bstep (se 1 (by rfl) ⟨4172750, by rfl⟩ : syracuseStep 5563667 = 8345501) B8345501
theorem B14280013 : Blo 1464552 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B5637545 : Blo 1464552 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B1648111 : Blo 1464552 1648111 := bstep (se 1 (by rfl) ⟨1236083, by rfl⟩ : syracuseStep 1648111 = 2472167) B2472167
theorem B2197019 : Blo 1464552 2197019 := bstep (se 1 (by rfl) ⟨1647764, by rfl⟩ : syracuseStep 2197019 = 3295529) B3295529
theorem B16926299 : Blo 1464552 16926299 := bstep (se 1 (by rfl) ⟨12694724, by rfl⟩ : syracuseStep 16926299 = 25389449) B25389449
theorem B21120749 : Blo 1464552 21120749 := bstep (se 3 (by rfl) ⟨3960140, by rfl⟩ : syracuseStep 21120749 = 7920281) B7920281
theorem B2197403 : Blo 1464552 2197403 := bstep (se 1 (by rfl) ⟨1648052, by rfl⟩ : syracuseStep 2197403 = 3296105) B3296105
theorem B2197439 : Blo 1464552 2197439 := bstep (se 1 (by rfl) ⟨1648079, by rfl⟩ : syracuseStep 2197439 = 3296159) B3296159
theorem B4458431 : Blo 1464552 4458431 := bstep (se 1 (by rfl) ⟨3343823, by rfl⟩ : syracuseStep 4458431 = 6687647) B6687647
theorem B2198063 : Blo 1464552 2198063 := bstep (se 1 (by rfl) ⟨1648547, by rfl⟩ : syracuseStep 2198063 = 3297095) B3297095
theorem B1649263 : Blo 1464552 1649263 := bstep (se 1 (by rfl) ⟨1236947, by rfl⟩ : syracuseStep 1649263 = 2473895) B2473895
theorem B2198183 : Blo 1464552 2198183 := bstep (se 1 (by rfl) ⟨1648637, by rfl⟩ : syracuseStep 2198183 = 3297275) B3297275
theorem B2198249 : Blo 1464552 2198249 := bstep (se 2 (by rfl) ⟨824343, by rfl⟩ : syracuseStep 2198249 = 1648687) B1648687
theorem B3295979 : Blo 1464552 3295979 := bstep (se 1 (by rfl) ⟨2471984, by rfl⟩ : syracuseStep 3295979 = 4943969) B4943969
theorem B2198255 : Blo 1464552 2198255 := bstep (se 1 (by rfl) ⟨1648691, by rfl⟩ : syracuseStep 2198255 = 3297383) B3297383
theorem B2640649 : Blo 1464552 2640649 := bstep (se 2 (by rfl) ⟨990243, by rfl⟩ : syracuseStep 2640649 = 1980487) B1980487
theorem B2198303 : Blo 1464552 2198303 := bstep (se 1 (by rfl) ⟨1648727, by rfl⟩ : syracuseStep 2198303 = 3297455) B3297455
theorem B8342311 : Blo 1464552 8342311 := bstep (se 1 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 8342311 = 12513467) B12513467
theorem B1649479 : Blo 1464552 1649479 := bstep (se 1 (by rfl) ⟨1237109, by rfl⟩ : syracuseStep 1649479 = 2474219) B2474219
theorem B8350559 : Blo 1464552 8350559 := bstep (se 1 (by rfl) ⟨6262919, by rfl⟩ : syracuseStep 8350559 = 12525839) B12525839
theorem B5565307 : Blo 1464552 5565307 := bstep (se 1 (by rfl) ⟨4173980, by rfl⟩ : syracuseStep 5565307 = 8347961) B8347961
theorem B37555163 : Blo 1464552 37555163 := bstep (se 1 (by rfl) ⟨28166372, by rfl⟩ : syracuseStep 37555163 = 56332745) B56332745
theorem B9391099 : Blo 1464552 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B4942889 : Blo 1464552 4942889 := bstep (se 2 (by rfl) ⟨1853583, by rfl⟩ : syracuseStep 4942889 = 3707167) B3707167
theorem B15256633 : Blo 1464552 15256633 := bstep (se 2 (by rfl) ⟨5721237, by rfl⟩ : syracuseStep 15256633 = 11442475) B11442475
theorem B2198633 : Blo 1464552 2198633 := bstep (se 2 (by rfl) ⟨824487, by rfl⟩ : syracuseStep 2198633 = 1648975) B1648975
theorem B8350877 : Blo 1464552 8350877 := bstep (se 3 (by rfl) ⟨1565789, by rfl⟩ : syracuseStep 8350877 = 3131579) B3131579
theorem B2198759 : Blo 1464552 2198759 := bstep (se 1 (by rfl) ⟨1649069, by rfl⟩ : syracuseStep 2198759 = 3298139) B3298139
theorem B4697471 : Blo 1464552 4697471 := bstep (se 1 (by rfl) ⟨3523103, by rfl⟩ : syracuseStep 4697471 = 7046207) B7046207
theorem B7515575 : Blo 1464552 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B7040519 : Blo 1464552 7040519 := bstep (se 1 (by rfl) ⟨5280389, by rfl⟩ : syracuseStep 7040519 = 10560779) B10560779
theorem B3296879 : Blo 1464552 3296879 := bstep (se 1 (by rfl) ⟨2472659, by rfl⟩ : syracuseStep 3296879 = 4945319) B4945319
theorem B4697767 : Blo 1464552 4697767 := bstep (se 1 (by rfl) ⟨3523325, by rfl⟩ : syracuseStep 4697767 = 7046651) B7046651
theorem B3296951 : Blo 1464552 3296951 := bstep (se 1 (by rfl) ⟨2472713, by rfl⟩ : syracuseStep 3296951 = 4945427) B4945427
theorem B2199263 : Blo 1464552 2199263 := bstep (se 1 (by rfl) ⟨1649447, by rfl⟩ : syracuseStep 2199263 = 3298895) B3298895
theorem B5566279 : Blo 1464552 5566279 := bstep (se 1 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 5566279 = 8349419) B8349419
theorem B2199545 : Blo 1464552 2199545 := bstep (se 2 (by rfl) ⟨824829, by rfl⟩ : syracuseStep 2199545 = 1649659) B1649659
theorem B3297401 : Blo 1464552 3297401 := bstep (se 2 (by rfl) ⟨1236525, by rfl⟩ : syracuseStep 3297401 = 2473051) B2473051
theorem B67711099 : Blo 1464552 67711099 := bstep (se 1 (by rfl) ⟨50783324, by rfl⟩ : syracuseStep 67711099 = 101566649) B101566649
theorem B2199743 : Blo 1464552 2199743 := bstep (se 1 (by rfl) ⟨1649807, by rfl⟩ : syracuseStep 2199743 = 3299615) B3299615
theorem B2199785 : Blo 1464552 2199785 := bstep (se 2 (by rfl) ⟨824919, by rfl⟩ : syracuseStep 2199785 = 1649839) B1649839
theorem B9384281 : Blo 1464552 9384281 := bstep (se 2 (by rfl) ⟨3519105, by rfl⟩ : syracuseStep 9384281 = 7038211) B7038211
theorem B3297707 : Blo 1464552 3297707 := bstep (se 1 (by rfl) ⟨2473280, by rfl⟩ : syracuseStep 3297707 = 4946561) B4946561
theorem B36131291 : Blo 1464552 36131291 := bstep (se 1 (by rfl) ⟨27098468, by rfl⟩ : syracuseStep 36131291 = 54196937) B54196937
theorem B8344043 : Blo 1464552 8344043 := bstep (se 1 (by rfl) ⟨6258032, by rfl⟩ : syracuseStep 8344043 = 12516065) B12516065
theorem B4174391 : Blo 1464552 4174391 := bstep (se 1 (by rfl) ⟨3130793, by rfl⟩ : syracuseStep 4174391 = 6261587) B6261587
theorem B15463001 : Blo 1464552 15463001 := bstep (se 2 (by rfl) ⟨5798625, by rfl⟩ : syracuseStep 15463001 = 11597251) B11597251
theorem B3298247 : Blo 1464552 3298247 := bstep (se 1 (by rfl) ⟨2473685, by rfl⟩ : syracuseStep 3298247 = 4947371) B4947371
theorem B33854453 : Blo 1464552 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B8909929 : Blo 1464552 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B3298409 : Blo 1464552 3298409 := bstep (se 2 (by rfl) ⟨1236903, by rfl⟩ : syracuseStep 3298409 = 2473807) B2473807
theorem B18830615 : Blo 1464552 18830615 := bstep (se 1 (by rfl) ⟨14122961, by rfl⟩ : syracuseStep 18830615 = 28245923) B28245923
theorem B3298607 : Blo 1464552 3298607 := bstep (se 1 (by rfl) ⟨2473955, by rfl⟩ : syracuseStep 3298607 = 4947911) B4947911
theorem B3299039 : Blo 1464552 3299039 := bstep (se 1 (by rfl) ⟨2474279, by rfl⟩ : syracuseStep 3299039 = 4948559) B4948559
theorem B5568223 : Blo 1464552 5568223 := bstep (se 1 (by rfl) ⟨4176167, by rfl⟩ : syracuseStep 5568223 = 8352335) B8352335
theorem B7419923 : Blo 1464552 7419923 := bstep (se 1 (by rfl) ⟨5564942, by rfl⟩ : syracuseStep 7419923 = 11129885) B11129885
theorem B4945967 : Blo 1464552 4945967 := bstep (se 1 (by rfl) ⟨3709475, by rfl⟩ : syracuseStep 4945967 = 7418951) B7418951
theorem B3299399 : Blo 1464552 3299399 := bstep (se 1 (by rfl) ⟨2474549, by rfl⟩ : syracuseStep 3299399 = 4949099) B4949099
theorem B6772841 : Blo 1464552 6772841 := bstep (se 2 (by rfl) ⟨2539815, by rfl⟩ : syracuseStep 6772841 = 5079631) B5079631
theorem B1464603 : Blo 1464552 1464603 := bstep (se 1 (by rfl) ⟨1098452, by rfl⟩ : syracuseStep 1464603 = 2196905) B2196905
theorem B1464703 : Blo 1464552 1464703 := bstep (se 1 (by rfl) ⟨1098527, by rfl⟩ : syracuseStep 1464703 = 2197055) B2197055
theorem B2472329 : Blo 1464552 2472329 := bstep (se 2 (by rfl) ⟨927123, by rfl⟩ : syracuseStep 2472329 = 1854247) B1854247
theorem B1464731 : Blo 1464552 1464731 := bstep (se 1 (by rfl) ⟨1098548, by rfl⟩ : syracuseStep 1464731 = 2197097) B2197097
theorem B1465023 : Blo 1464552 1465023 := bstep (se 1 (by rfl) ⟨1098767, by rfl⟩ : syracuseStep 1465023 = 2197535) B2197535
theorem B5012231 : Blo 1464552 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B28572425 : Blo 1464552 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B2472761 : Blo 1464552 2472761 := bstep (se 2 (by rfl) ⟨927285, by rfl⟩ : syracuseStep 2472761 = 1854571) B1854571
theorem B1465151 : Blo 1464552 1465151 := bstep (se 1 (by rfl) ⟨1098863, by rfl⟩ : syracuseStep 1465151 = 2197727) B2197727
theorem B17611615 : Blo 1464552 17611615 := bstep (se 1 (by rfl) ⟨13208711, by rfl⟩ : syracuseStep 17611615 = 26417423) B26417423
theorem B1465191 : Blo 1464552 1465191 := bstep (se 1 (by rfl) ⟨1098893, by rfl⟩ : syracuseStep 1465191 = 2197787) B2197787
theorem B47545289 : Blo 1464552 47545289 := bstep (se 2 (by rfl) ⟨17829483, by rfl⟩ : syracuseStep 47545289 = 35658967) B35658967
theorem B2472943 : Blo 1464552 2472943 := bstep (se 1 (by rfl) ⟨1854707, by rfl⟩ : syracuseStep 2472943 = 3709415) B3709415
theorem B1465407 : Blo 1464552 1465407 := bstep (se 1 (by rfl) ⟨1099055, by rfl⟩ : syracuseStep 1465407 = 2198111) B2198111
theorem B7044191 : Blo 1464552 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B28572797 : Blo 1464552 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B6257897 : Blo 1464552 6257897 := bstep (se 2 (by rfl) ⟨2346711, by rfl⟩ : syracuseStep 6257897 = 4693423) B4693423
theorem B1465595 : Blo 1464552 1465595 := bstep (se 1 (by rfl) ⟨1099196, by rfl⟩ : syracuseStep 1465595 = 2198393) B2198393
theorem B1465627 : Blo 1464552 1465627 := bstep (se 1 (by rfl) ⟨1099220, by rfl⟩ : syracuseStep 1465627 = 2198441) B2198441
theorem B8346959 : Blo 1464552 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B5561723 : Blo 1464552 5561723 := bstep (se 1 (by rfl) ⟨4171292, by rfl⟩ : syracuseStep 5561723 = 8342585) B8342585
theorem B1465727 : Blo 1464552 1465727 := bstep (se 1 (by rfl) ⟨1099295, by rfl⟩ : syracuseStep 1465727 = 2198591) B2198591
theorem B1466095 : Blo 1464552 1466095 := bstep (se 1 (by rfl) ⟨1099571, by rfl⟩ : syracuseStep 1466095 = 2199143) B2199143
theorem B5562209 : Blo 1464552 5562209 := bstep (se 2 (by rfl) ⟨2085828, by rfl⟩ : syracuseStep 5562209 = 4171657) B4171657
theorem B1466351 : Blo 1464552 1466351 := bstep (se 1 (by rfl) ⟨1099763, by rfl⟩ : syracuseStep 1466351 = 2199527) B2199527
theorem B1466495 : Blo 1464552 1466495 := bstep (se 1 (by rfl) ⟨1099871, by rfl⟩ : syracuseStep 1466495 = 2199743) B2199743
theorem B1466523 : Blo 1464552 1466523 := bstep (se 1 (by rfl) ⟨1099892, by rfl⟩ : syracuseStep 1466523 = 2199785) B2199785
theorem B5562695 : Blo 1464552 5562695 := bstep (se 1 (by rfl) ⟨4172021, by rfl⟩ : syracuseStep 5562695 = 8344043) B8344043
theorem B4456787 : Blo 1464552 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B22569635 : Blo 1464552 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B12526589 : Blo 1464552 12526589 := bstep (se 3 (by rfl) ⟨2348735, by rfl⟩ : syracuseStep 12526589 = 4697471) B4697471
theorem B4515227 : Blo 1464552 4515227 := bstep (se 1 (by rfl) ⟨3386420, by rfl⟩ : syracuseStep 4515227 = 6772841) B6772841
theorem B20342177 : Blo 1464552 20342177 := bstep (se 2 (by rfl) ⟨7628316, by rfl⟩ : syracuseStep 20342177 = 15256633) B15256633
theorem B11879905 : Blo 1464552 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B1648219 : Blo 1464552 1648219 := bstep (se 1 (by rfl) ⟨1236164, by rfl⟩ : syracuseStep 1648219 = 2472329) B2472329
theorem B19040017 : Blo 1464552 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B2197319 : Blo 1464552 2197319 := bstep (se 1 (by rfl) ⟨1647989, by rfl⟩ : syracuseStep 2197319 = 3295979) B3295979
theorem B19048283 : Blo 1464552 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B1648507 : Blo 1464552 1648507 := bstep (se 1 (by rfl) ⟨1236380, by rfl⟩ : syracuseStep 1648507 = 2472761) B2472761
theorem B31696859 : Blo 1464552 31696859 := bstep (se 1 (by rfl) ⟨23772644, by rfl⟩ : syracuseStep 31696859 = 47545289) B47545289
theorem B25036775 : Blo 1464552 25036775 := bstep (se 1 (by rfl) ⟨18777581, by rfl⟩ : syracuseStep 25036775 = 37555163) B37555163
theorem B2197481 : Blo 1464552 2197481 := bstep (se 2 (by rfl) ⟨824055, by rfl⟩ : syracuseStep 2197481 = 1648111) B1648111
theorem B3295259 : Blo 1464552 3295259 := bstep (se 1 (by rfl) ⟨2471444, by rfl⟩ : syracuseStep 3295259 = 4942889) B4942889
theorem B4696127 : Blo 1464552 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B19048531 : Blo 1464552 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B4171931 : Blo 1464552 4171931 := bstep (se 1 (by rfl) ⟨3128948, by rfl⟩ : syracuseStep 4171931 = 6257897) B6257897
theorem B5564639 : Blo 1464552 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B7424297 : Blo 1464552 7424297 := bstep (se 2 (by rfl) ⟨2784111, by rfl⟩ : syracuseStep 7424297 = 5568223) B5568223
theorem B2197919 : Blo 1464552 2197919 := bstep (se 1 (by rfl) ⟨1648439, by rfl⟩ : syracuseStep 2197919 = 3296879) B3296879
theorem B2197967 : Blo 1464552 2197967 := bstep (se 1 (by rfl) ⟨1648475, by rfl⟩ : syracuseStep 2197967 = 3296951) B3296951
theorem B1649371 : Blo 1464552 1649371 := bstep (se 1 (by rfl) ⟨1237028, by rfl⟩ : syracuseStep 1649371 = 2474057) B2474057
theorem B53463797 : Blo 1464552 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B2198267 : Blo 1464552 2198267 := bstep (se 1 (by rfl) ⟨1648700, by rfl⟩ : syracuseStep 2198267 = 3297401) B3297401
theorem B2198471 : Blo 1464552 2198471 := bstep (se 1 (by rfl) ⟨1648853, by rfl⟩ : syracuseStep 2198471 = 3297707) B3297707
theorem B24087527 : Blo 1464552 24087527 := bstep (se 1 (by rfl) ⟨18065645, by rfl⟩ : syracuseStep 24087527 = 36131291) B36131291
theorem B2198831 : Blo 1464552 2198831 := bstep (se 1 (by rfl) ⟨1649123, by rfl⟩ : syracuseStep 2198831 = 3298247) B3298247
theorem B2780543 : Blo 1464552 2780543 := bstep (se 1 (by rfl) ⟨2085407, by rfl⟩ : syracuseStep 2780543 = 4170815) B4170815
theorem B2198939 : Blo 1464552 2198939 := bstep (se 1 (by rfl) ⟨1649204, by rfl⟩ : syracuseStep 2198939 = 3298409) B3298409
theorem B2199017 : Blo 1464552 2199017 := bstep (se 2 (by rfl) ⟨824631, by rfl⟩ : syracuseStep 2199017 = 1649263) B1649263
theorem B2199071 : Blo 1464552 2199071 := bstep (se 1 (by rfl) ⟨1649303, by rfl⟩ : syracuseStep 2199071 = 3298607) B3298607
theorem B11284199 : Blo 1464552 11284199 := bstep (se 1 (by rfl) ⟨8463149, by rfl⟩ : syracuseStep 11284199 = 16926299) B16926299
theorem B2199305 : Blo 1464552 2199305 := bstep (se 2 (by rfl) ⟨824739, by rfl⟩ : syracuseStep 2199305 = 1649479) B1649479
theorem B23482153 : Blo 1464552 23482153 := bstep (se 2 (by rfl) ⟨8805807, by rfl⟩ : syracuseStep 23482153 = 17611615) B17611615
theorem B2199359 : Blo 1464552 2199359 := bstep (se 1 (by rfl) ⟨1649519, by rfl⟩ : syracuseStep 2199359 = 3299039) B3299039
theorem B3297257 : Blo 1464552 3297257 := bstep (se 2 (by rfl) ⟨1236471, by rfl⟩ : syracuseStep 3297257 = 2472943) B2472943
theorem B12521465 : Blo 1464552 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B3297311 : Blo 1464552 3297311 := bstep (se 1 (by rfl) ⟨2472983, by rfl⟩ : syracuseStep 3297311 = 4945967) B4945967
theorem B2199599 : Blo 1464552 2199599 := bstep (se 1 (by rfl) ⟨1649699, by rfl⟩ : syracuseStep 2199599 = 3299399) B3299399
theorem B41234669 : Blo 1464552 41234669 := bstep (se 3 (by rfl) ⟨7731500, by rfl⟩ : syracuseStep 41234669 = 15463001) B15463001
theorem B5567039 : Blo 1464552 5567039 := bstep (se 1 (by rfl) ⟨4175279, by rfl⟩ : syracuseStep 5567039 = 8350559) B8350559
theorem B1466363 : Blo 1464552 1466363 := bstep (se 1 (by rfl) ⟨1099772, by rfl⟩ : syracuseStep 1466363 = 2199545) B2199545
theorem B5567251 : Blo 1464552 5567251 := bstep (se 1 (by rfl) ⟨4175438, by rfl⟩ : syracuseStep 5567251 = 8350877) B8350877
theorem B6263689 : Blo 1464552 6263689 := bstep (se 2 (by rfl) ⟨2348883, by rfl⟩ : syracuseStep 6263689 = 4697767) B4697767
theorem B3707815 : Blo 1464552 3707815 := bstep (se 1 (by rfl) ⟨2780861, by rfl⟩ : syracuseStep 3707815 = 5561723) B5561723
theorem B5010383 : Blo 1464552 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B3708139 : Blo 1464552 3708139 := bstep (se 1 (by rfl) ⟨2781104, by rfl⟩ : syracuseStep 3708139 = 5562209) B5562209
theorem B90281465 : Blo 1464552 90281465 := bstep (se 2 (by rfl) ⟨33855549, by rfl⟩ : syracuseStep 90281465 = 67711099) B67711099
theorem B6256187 : Blo 1464552 6256187 := bstep (se 1 (by rfl) ⟨4692140, by rfl⟩ : syracuseStep 6256187 = 9384281) B9384281
theorem B4069007 : Blo 1464552 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B15849121 : Blo 1464552 15849121 := bstep (se 2 (by rfl) ⟨5943420, by rfl⟩ : syracuseStep 15849121 = 11886841) B11886841
theorem B2782927 : Blo 1464552 2782927 := bstep (se 1 (by rfl) ⟨2087195, by rfl⟩ : syracuseStep 2782927 = 4174391) B4174391
theorem B50214973 : Blo 1464552 50214973 := bstep (se 3 (by rfl) ⟨9415307, by rfl⟩ : syracuseStep 50214973 = 18830615) B18830615
theorem B3709111 : Blo 1464552 3709111 := bstep (se 1 (by rfl) ⟨2781833, by rfl⟩ : syracuseStep 3709111 = 5563667) B5563667
theorem B3758363 : Blo 1464552 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B3520865 : Blo 1464552 3520865 := bstep (se 2 (by rfl) ⟨1320324, by rfl⟩ : syracuseStep 3520865 = 2640649) B2640649
theorem B1464679 : Blo 1464552 1464679 := bstep (se 1 (by rfl) ⟨1098509, by rfl⟩ : syracuseStep 1464679 = 2197019) B2197019
theorem B11123081 : Blo 1464552 11123081 := bstep (se 2 (by rfl) ⟨4171155, by rfl⟩ : syracuseStep 11123081 = 8342311) B8342311
theorem B14080499 : Blo 1464552 14080499 := bstep (se 1 (by rfl) ⟨10560374, by rfl⟩ : syracuseStep 14080499 = 21120749) B21120749
theorem B7420409 : Blo 1464552 7420409 := bstep (se 2 (by rfl) ⟨2782653, by rfl⟩ : syracuseStep 7420409 = 5565307) B5565307
theorem B1464935 : Blo 1464552 1464935 := bstep (se 1 (by rfl) ⟨1098701, by rfl⟩ : syracuseStep 1464935 = 2197403) B2197403
theorem B1464959 : Blo 1464552 1464959 := bstep (se 1 (by rfl) ⟨1098719, by rfl⟩ : syracuseStep 1464959 = 2197439) B2197439
theorem B2972287 : Blo 1464552 2972287 := bstep (se 1 (by rfl) ⟨2229215, by rfl⟩ : syracuseStep 2972287 = 4458431) B4458431
theorem B4946615 : Blo 1464552 4946615 := bstep (se 1 (by rfl) ⟨3709961, by rfl⟩ : syracuseStep 4946615 = 7419923) B7419923
theorem B1465375 : Blo 1464552 1465375 := bstep (se 1 (by rfl) ⟨1099031, by rfl⟩ : syracuseStep 1465375 = 2198063) B2198063
theorem B1465455 : Blo 1464552 1465455 := bstep (se 1 (by rfl) ⟨1099091, by rfl⟩ : syracuseStep 1465455 = 2198183) B2198183
theorem B1465499 : Blo 1464552 1465499 := bstep (se 1 (by rfl) ⟨1099124, by rfl⟩ : syracuseStep 1465499 = 2198249) B2198249
theorem B1465503 : Blo 1464552 1465503 := bstep (se 1 (by rfl) ⟨1099127, by rfl⟩ : syracuseStep 1465503 = 2198255) B2198255
theorem B1465535 : Blo 1464552 1465535 := bstep (se 1 (by rfl) ⟨1099151, by rfl⟩ : syracuseStep 1465535 = 2198303) B2198303
theorem B1465755 : Blo 1464552 1465755 := bstep (se 1 (by rfl) ⟨1099316, by rfl⟩ : syracuseStep 1465755 = 2198633) B2198633
theorem B1465839 : Blo 1464552 1465839 := bstep (se 1 (by rfl) ⟨1099379, by rfl⟩ : syracuseStep 1465839 = 2198759) B2198759
theorem B4693679 : Blo 1464552 4693679 := bstep (se 1 (by rfl) ⟨3520259, by rfl⟩ : syracuseStep 4693679 = 7040519) B7040519
theorem B7421705 : Blo 1464552 7421705 := bstep (se 2 (by rfl) ⟨2783139, by rfl⟩ : syracuseStep 7421705 = 5566279) B5566279
theorem B1466175 : Blo 1464552 1466175 := bstep (se 1 (by rfl) ⟨1099631, by rfl⟩ : syracuseStep 1466175 = 2199263) B2199263
theorem B1466399 : Blo 1464552 1466399 := bstep (se 1 (by rfl) ⟨1099799, by rfl⟩ : syracuseStep 1466399 = 2199599) B2199599
theorem B66953297 : Blo 1464552 66953297 := bstep (se 2 (by rfl) ⟨25107486, by rfl⟩ : syracuseStep 66953297 = 50214973) B50214973
theorem B3711359 : Blo 1464552 3711359 := bstep (se 1 (by rfl) ⟨2783519, by rfl⟩ : syracuseStep 3711359 = 5567039) B5567039
theorem B47539061 : Blo 1464552 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B9388973 : Blo 1464552 9388973 := bstep (se 3 (by rfl) ⟨1760432, by rfl⟩ : syracuseStep 9388973 = 3520865) B3520865
theorem B60187643 : Blo 1464552 60187643 := bstep (se 1 (by rfl) ⟨45140732, by rfl⟩ : syracuseStep 60187643 = 90281465) B90281465
theorem B7423001 : Blo 1464552 7423001 := bstep (se 2 (by rfl) ⟨2783625, by rfl⟩ : syracuseStep 7423001 = 5567251) B5567251
theorem B4170791 : Blo 1464552 4170791 := bstep (se 1 (by rfl) ⟨3128093, by rfl⟩ : syracuseStep 4170791 = 6256187) B6256187
theorem B2712671 : Blo 1464552 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B12698855 : Blo 1464552 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2196839 : Blo 1464552 2196839 := bstep (se 1 (by rfl) ⟨1647629, by rfl⟩ : syracuseStep 2196839 = 3295259) B3295259
theorem B3130751 : Blo 1464552 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B4949531 : Blo 1464552 4949531 := bstep (se 1 (by rfl) ⟨3712148, by rfl⟩ : syracuseStep 4949531 = 7424297) B7424297
theorem B7415387 : Blo 1464552 7415387 := bstep (se 1 (by rfl) ⟨5561540, by rfl⟩ : syracuseStep 7415387 = 11123081) B11123081
theorem B16058351 : Blo 1464552 16058351 := bstep (se 1 (by rfl) ⟨12043763, by rfl⟩ : syracuseStep 16058351 = 24087527) B24087527
theorem B2197625 : Blo 1464552 2197625 := bstep (se 2 (by rfl) ⟨824109, by rfl⟩ : syracuseStep 2197625 = 1648219) B1648219
theorem B1853695 : Blo 1464552 1853695 := bstep (se 1 (by rfl) ⟨1390271, by rfl⟩ : syracuseStep 1853695 = 2780543) B2780543
theorem B7522799 : Blo 1464552 7522799 := bstep (se 1 (by rfl) ⟨5642099, by rfl⟩ : syracuseStep 7522799 = 11284199) B11284199
theorem B2198009 : Blo 1464552 2198009 := bstep (se 2 (by rfl) ⟨824253, by rfl⟩ : syracuseStep 2198009 = 1648507) B1648507
theorem B2198171 : Blo 1464552 2198171 := bstep (se 1 (by rfl) ⟨1648628, by rfl⟩ : syracuseStep 2198171 = 3297257) B3297257
theorem B2198207 : Blo 1464552 2198207 := bstep (se 1 (by rfl) ⟨1648655, by rfl⟩ : syracuseStep 2198207 = 3297311) B3297311
theorem B25398041 : Blo 1464552 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B8351059 : Blo 1464552 8351059 := bstep (se 1 (by rfl) ⟨6263294, by rfl⟩ : syracuseStep 8351059 = 12526589) B12526589
theorem B3010151 : Blo 1464552 3010151 := bstep (se 1 (by rfl) ⟨2257613, by rfl⟩ : syracuseStep 3010151 = 4515227) B4515227
theorem B13561451 : Blo 1464552 13561451 := bstep (se 1 (by rfl) ⟨10171088, by rfl⟩ : syracuseStep 13561451 = 20342177) B20342177
theorem B2199161 : Blo 1464552 2199161 := bstep (se 2 (by rfl) ⟨824685, by rfl⟩ : syracuseStep 2199161 = 1649371) B1649371
theorem B8351585 : Blo 1464552 8351585 := bstep (se 2 (by rfl) ⟨3131844, by rfl⟩ : syracuseStep 8351585 = 6263689) B6263689
theorem B4943753 : Blo 1464552 4943753 := bstep (se 2 (by rfl) ⟨1853907, by rfl⟩ : syracuseStep 4943753 = 3707815) B3707815
theorem B21131239 : Blo 1464552 21131239 := bstep (se 1 (by rfl) ⟨15848429, by rfl⟩ : syracuseStep 21131239 = 31696859) B31696859
theorem B16691183 : Blo 1464552 16691183 := bstep (se 1 (by rfl) ⟨12518387, by rfl⟩ : syracuseStep 16691183 = 25036775) B25036775
theorem B2781287 : Blo 1464552 2781287 := bstep (se 1 (by rfl) ⟨2085965, by rfl⟩ : syracuseStep 2781287 = 4171931) B4171931
theorem B4944185 : Blo 1464552 4944185 := bstep (se 2 (by rfl) ⟨1854069, by rfl⟩ : syracuseStep 4944185 = 3708139) B3708139
theorem B3297743 : Blo 1464552 3297743 := bstep (se 1 (by rfl) ⟨2473307, by rfl⟩ : syracuseStep 3297743 = 4946615) B4946615
theorem B15839873 : Blo 1464552 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B21132161 : Blo 1464552 21132161 := bstep (se 2 (by rfl) ⟨7924560, by rfl⟩ : syracuseStep 21132161 = 15849121) B15849121
theorem B27489779 : Blo 1464552 27489779 := bstep (se 1 (by rfl) ⟨20617334, by rfl⟩ : syracuseStep 27489779 = 41234669) B41234669
theorem B3708463 : Blo 1464552 3708463 := bstep (se 1 (by rfl) ⟨2781347, by rfl⟩ : syracuseStep 3708463 = 5562695) B5562695
theorem B4945481 : Blo 1464552 4945481 := bstep (se 2 (by rfl) ⟨1854555, by rfl⟩ : syracuseStep 4945481 = 3709111) B3709111
theorem B3963049 : Blo 1464552 3963049 := bstep (se 2 (by rfl) ⟨1486143, by rfl⟩ : syracuseStep 3963049 = 2972287) B2972287
theorem B1464879 : Blo 1464552 1464879 := bstep (se 1 (by rfl) ⟨1098659, by rfl⟩ : syracuseStep 1464879 = 2197319) B2197319
theorem B1464987 : Blo 1464552 1464987 := bstep (se 1 (by rfl) ⟨1098740, by rfl⟩ : syracuseStep 1464987 = 2197481) B2197481
theorem B3709759 : Blo 1464552 3709759 := bstep (se 1 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 3709759 = 5564639) B5564639
theorem B2505575 : Blo 1464552 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B1465279 : Blo 1464552 1465279 := bstep (se 1 (by rfl) ⟨1098959, by rfl⟩ : syracuseStep 1465279 = 2197919) B2197919
theorem B1465311 : Blo 1464552 1465311 := bstep (se 1 (by rfl) ⟨1098983, by rfl⟩ : syracuseStep 1465311 = 2197967) B2197967
theorem B9386999 : Blo 1464552 9386999 := bstep (se 1 (by rfl) ⟨7040249, by rfl⟩ : syracuseStep 9386999 = 14080499) B14080499
theorem B4946939 : Blo 1464552 4946939 := bstep (se 1 (by rfl) ⟨3710204, by rfl⟩ : syracuseStep 4946939 = 7420409) B7420409
theorem B60185693 : Blo 1464552 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B35642531 : Blo 1464552 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B1465511 : Blo 1464552 1465511 := bstep (se 1 (by rfl) ⟨1099133, by rfl⟩ : syracuseStep 1465511 = 2198267) B2198267
theorem B1465647 : Blo 1464552 1465647 := bstep (se 1 (by rfl) ⟨1099235, by rfl⟩ : syracuseStep 1465647 = 2198471) B2198471
theorem B1465887 : Blo 1464552 1465887 := bstep (se 1 (by rfl) ⟨1099415, by rfl⟩ : syracuseStep 1465887 = 2198831) B2198831
theorem B1465959 : Blo 1464552 1465959 := bstep (se 1 (by rfl) ⟨1099469, by rfl⟩ : syracuseStep 1465959 = 2198939) B2198939
theorem B3710569 : Blo 1464552 3710569 := bstep (se 2 (by rfl) ⟨1391463, by rfl⟩ : syracuseStep 3710569 = 2782927) B2782927
theorem B1466011 : Blo 1464552 1466011 := bstep (se 1 (by rfl) ⟨1099508, by rfl⟩ : syracuseStep 1466011 = 2199017) B2199017
theorem B1466047 : Blo 1464552 1466047 := bstep (se 1 (by rfl) ⟨1099535, by rfl⟩ : syracuseStep 1466047 = 2199071) B2199071
theorem B25386689 : Blo 1464552 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B31309537 : Blo 1464552 31309537 := bstep (se 2 (by rfl) ⟨11741076, by rfl⟩ : syracuseStep 31309537 = 23482153) B23482153
theorem B3129119 : Blo 1464552 3129119 := bstep (se 1 (by rfl) ⟨2346839, by rfl⟩ : syracuseStep 3129119 = 4693679) B4693679
theorem B4947803 : Blo 1464552 4947803 := bstep (se 1 (by rfl) ⟨3710852, by rfl⟩ : syracuseStep 4947803 = 7421705) B7421705
theorem B1466203 : Blo 1464552 1466203 := bstep (se 1 (by rfl) ⟨1099652, by rfl⟩ : syracuseStep 1466203 = 2199305) B2199305
theorem B13361021 : Blo 1464552 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B1466239 : Blo 1464552 1466239 := bstep (se 1 (by rfl) ⟨1099679, by rfl⟩ : syracuseStep 1466239 = 2199359) B2199359
theorem B8347643 : Blo 1464552 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B2474239 : Blo 1464552 2474239 := bstep (se 1 (by rfl) ⟨1855679, by rfl⟩ : syracuseStep 2474239 = 3711359) B3711359
theorem B10559915 : Blo 1464552 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B6259315 : Blo 1464552 6259315 := bstep (se 1 (by rfl) ⟨4694486, by rfl⟩ : syracuseStep 6259315 = 9388973) B9388973
theorem B40125095 : Blo 1464552 40125095 := bstep (se 1 (by rfl) ⟨30093821, by rfl⟩ : syracuseStep 40125095 = 60187643) B60187643
theorem B4948667 : Blo 1464552 4948667 := bstep (se 1 (by rfl) ⟨3711500, by rfl⟩ : syracuseStep 4948667 = 7423001) B7423001
theorem B21136261 : Blo 1464552 21136261 := bstep (se 4 (by rfl) ⟨1981524, by rfl⟩ : syracuseStep 21136261 = 3963049) B3963049
theorem B18326519 : Blo 1464552 18326519 := bstep (se 1 (by rfl) ⟨13744889, by rfl⟩ : syracuseStep 18326519 = 27489779) B27489779
theorem B8348669 : Blo 1464552 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B11134745 : Blo 1464552 11134745 := bstep (se 2 (by rfl) ⟨4175529, by rfl⟩ : syracuseStep 11134745 = 8351059) B8351059
theorem B8907347 : Blo 1464552 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B3295835 : Blo 1464552 3295835 := bstep (se 1 (by rfl) ⟨2471876, by rfl⟩ : syracuseStep 3295835 = 4943753) B4943753
theorem B28174985 : Blo 1464552 28174985 := bstep (se 2 (by rfl) ⟨10565619, by rfl⟩ : syracuseStep 28174985 = 21131239) B21131239
theorem B11127455 : Blo 1464552 11127455 := bstep (se 1 (by rfl) ⟨8345591, by rfl⟩ : syracuseStep 11127455 = 16691183) B16691183
theorem B5565095 : Blo 1464552 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B1854191 : Blo 1464552 1854191 := bstep (se 1 (by rfl) ⟨1390643, by rfl⟩ : syracuseStep 1854191 = 2781287) B2781287
theorem B3296123 : Blo 1464552 3296123 := bstep (se 1 (by rfl) ⟨2472092, by rfl⟩ : syracuseStep 3296123 = 4944185) B4944185
theorem B270912437 : Blo 1464552 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B2198495 : Blo 1464552 2198495 := bstep (se 1 (by rfl) ⟨1648871, by rfl⟩ : syracuseStep 2198495 = 3297743) B3297743
theorem B8465903 : Blo 1464552 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B3296987 : Blo 1464552 3296987 := bstep (se 1 (by rfl) ⟨2472740, by rfl⟩ : syracuseStep 3296987 = 4945481) B4945481
theorem B4943591 : Blo 1464552 4943591 := bstep (se 1 (by rfl) ⟨3707693, by rfl⟩ : syracuseStep 4943591 = 7415387) B7415387
theorem B3297959 : Blo 1464552 3297959 := bstep (se 1 (by rfl) ⟨2473469, by rfl⟩ : syracuseStep 3297959 = 4946939) B4946939
theorem B4944617 : Blo 1464552 4944617 := bstep (se 2 (by rfl) ⟨1854231, by rfl⟩ : syracuseStep 4944617 = 3708463) B3708463
theorem B23761687 : Blo 1464552 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B6681533 : Blo 1464552 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B9040967 : Blo 1464552 9040967 := bstep (se 1 (by rfl) ⟨6780725, by rfl⟩ : syracuseStep 9040967 = 13561451) B13561451
theorem B2086079 : Blo 1464552 2086079 := bstep (se 1 (by rfl) ⟨1564559, by rfl⟩ : syracuseStep 2086079 = 3129119) B3129119
theorem B3298535 : Blo 1464552 3298535 := bstep (se 1 (by rfl) ⟨2473901, by rfl⟩ : syracuseStep 3298535 = 4947803) B4947803
theorem B5567723 : Blo 1464552 5567723 := bstep (se 1 (by rfl) ⟨4175792, by rfl⟩ : syracuseStep 5567723 = 8351585) B8351585
theorem B44635531 : Blo 1464552 44635531 := bstep (se 1 (by rfl) ⟨33476648, by rfl⟩ : syracuseStep 44635531 = 66953297) B66953297
theorem B11122109 : Blo 1464552 11122109 := bstep (se 3 (by rfl) ⟨2085395, by rfl⟩ : syracuseStep 11122109 = 4170791) B4170791
theorem B160495181 : Blo 1464552 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B2471593 : Blo 1464552 2471593 := bstep (se 2 (by rfl) ⟨926847, by rfl⟩ : syracuseStep 2471593 = 1853695) B1853695
theorem B31692707 : Blo 1464552 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B14088107 : Blo 1464552 14088107 := bstep (se 1 (by rfl) ⟨10566080, by rfl⟩ : syracuseStep 14088107 = 21132161) B21132161
theorem B1808447 : Blo 1464552 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B1464559 : Blo 1464552 1464559 := bstep (se 1 (by rfl) ⟨1098419, by rfl⟩ : syracuseStep 1464559 = 2196839) B2196839
theorem B3299687 : Blo 1464552 3299687 := bstep (se 1 (by rfl) ⟨2474765, by rfl⟩ : syracuseStep 3299687 = 4949531) B4949531
theorem B4946345 : Blo 1464552 4946345 := bstep (se 2 (by rfl) ⟨1854879, by rfl⟩ : syracuseStep 4946345 = 3709759) B3709759
theorem B20060797 : Blo 1464552 20060797 := bstep (se 3 (by rfl) ⟨3761399, by rfl⟩ : syracuseStep 20060797 = 7522799) B7522799
theorem B10705567 : Blo 1464552 10705567 := bstep (se 1 (by rfl) ⟨8029175, by rfl⟩ : syracuseStep 10705567 = 16058351) B16058351
theorem B1465083 : Blo 1464552 1465083 := bstep (se 1 (by rfl) ⟨1098812, by rfl⟩ : syracuseStep 1465083 = 2197625) B2197625
theorem B1465339 : Blo 1464552 1465339 := bstep (se 1 (by rfl) ⟨1099004, by rfl⟩ : syracuseStep 1465339 = 2198009) B2198009
theorem B1465447 : Blo 1464552 1465447 := bstep (se 1 (by rfl) ⟨1099085, by rfl⟩ : syracuseStep 1465447 = 2198171) B2198171
theorem B1465471 : Blo 1464552 1465471 := bstep (se 1 (by rfl) ⟨1099103, by rfl⟩ : syracuseStep 1465471 = 2198207) B2198207
theorem B6257999 : Blo 1464552 6257999 := bstep (se 1 (by rfl) ⟨4693499, by rfl⟩ : syracuseStep 6257999 = 9386999) B9386999
theorem B4947425 : Blo 1464552 4947425 := bstep (se 2 (by rfl) ⟨1855284, by rfl⟩ : syracuseStep 4947425 = 3710569) B3710569
theorem B41746049 : Blo 1464552 41746049 := bstep (se 2 (by rfl) ⟨15654768, by rfl⟩ : syracuseStep 41746049 = 31309537) B31309537
theorem B2006767 : Blo 1464552 2006767 := bstep (se 1 (by rfl) ⟨1505075, by rfl⟩ : syracuseStep 2006767 = 3010151) B3010151
theorem B1466107 : Blo 1464552 1466107 := bstep (se 1 (by rfl) ⟨1099580, by rfl⟩ : syracuseStep 1466107 = 2199161) B2199161
theorem B16924459 : Blo 1464552 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B5562877 : Blo 1464552 5562877 := bstep (se 3 (by rfl) ⟨1043039, by rfl⟩ : syracuseStep 5562877 = 2086079) B2086079
theorem B3711815 : Blo 1464552 3711815 := bstep (se 1 (by rfl) ⟨2783861, by rfl⟩ : syracuseStep 3711815 = 5567723) B5567723
theorem B26747729 : Blo 1464552 26747729 := bstep (se 2 (by rfl) ⟨10030398, by rfl⟩ : syracuseStep 26747729 = 20060797) B20060797
theorem B7414739 : Blo 1464552 7414739 := bstep (se 1 (by rfl) ⟨5561054, by rfl⟩ : syracuseStep 7414739 = 11122109) B11122109
theorem B106996787 : Blo 1464552 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B28181681 : Blo 1464552 28181681 := bstep (se 2 (by rfl) ⟨10568130, by rfl⟩ : syracuseStep 28181681 = 21136261) B21136261
theorem B7423163 : Blo 1464552 7423163 := bstep (se 1 (by rfl) ⟨5567372, by rfl⟩ : syracuseStep 7423163 = 11134745) B11134745
theorem B21128471 : Blo 1464552 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B2197223 : Blo 1464552 2197223 := bstep (se 1 (by rfl) ⟨1647917, by rfl⟩ : syracuseStep 2197223 = 3295835) B3295835
theorem B2197415 : Blo 1464552 2197415 := bstep (se 1 (by rfl) ⟨1648061, by rfl⟩ : syracuseStep 2197415 = 3296123) B3296123
theorem B4171999 : Blo 1464552 4171999 := bstep (se 1 (by rfl) ⟨3128999, by rfl⟩ : syracuseStep 4171999 = 6257999) B6257999
theorem B3295457 : Blo 1464552 3295457 := bstep (se 2 (by rfl) ⟨1235796, by rfl⟩ : syracuseStep 3295457 = 2471593) B2471593
theorem B27830699 : Blo 1464552 27830699 := bstep (se 1 (by rfl) ⟨20873024, by rfl⟩ : syracuseStep 27830699 = 41746049) B41746049
theorem B2197991 : Blo 1464552 2197991 := bstep (se 1 (by rfl) ⟨1648493, by rfl⟩ : syracuseStep 2197991 = 3296987) B3296987
theorem B3295727 : Blo 1464552 3295727 := bstep (se 1 (by rfl) ⟨2471795, by rfl⟩ : syracuseStep 3295727 = 4943591) B4943591
theorem B7039943 : Blo 1464552 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B2198639 : Blo 1464552 2198639 := bstep (se 1 (by rfl) ⟨1648979, by rfl⟩ : syracuseStep 2198639 = 3297959) B3297959
theorem B26750063 : Blo 1464552 26750063 := bstep (se 1 (by rfl) ⟨20062547, by rfl⟩ : syracuseStep 26750063 = 40125095) B40125095
theorem B3296411 : Blo 1464552 3296411 := bstep (se 1 (by rfl) ⟨2472308, by rfl⟩ : syracuseStep 3296411 = 4944617) B4944617
theorem B12217679 : Blo 1464552 12217679 := bstep (se 1 (by rfl) ⟨9163259, by rfl⟩ : syracuseStep 12217679 = 18326519) B18326519
theorem B5565779 : Blo 1464552 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B2199023 : Blo 1464552 2199023 := bstep (se 1 (by rfl) ⟨1649267, by rfl⟩ : syracuseStep 2199023 = 3298535) B3298535
theorem B14274089 : Blo 1464552 14274089 := bstep (se 2 (by rfl) ⟨5352783, by rfl⟩ : syracuseStep 14274089 = 10705567) B10705567
theorem B31682249 : Blo 1464552 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B10702757 : Blo 1464552 10702757 := bstep (se 4 (by rfl) ⟨1003383, by rfl⟩ : syracuseStep 10702757 = 2006767) B2006767
theorem B23752925 : Blo 1464552 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B2199791 : Blo 1464552 2199791 := bstep (se 1 (by rfl) ⟨1649843, by rfl⟩ : syracuseStep 2199791 = 3299687) B3299687
theorem B3297563 : Blo 1464552 3297563 := bstep (se 1 (by rfl) ⟨2473172, by rfl⟩ : syracuseStep 3297563 = 4946345) B4946345
theorem B7418303 : Blo 1464552 7418303 := bstep (se 1 (by rfl) ⟨5563727, by rfl⟩ : syracuseStep 7418303 = 11127455) B11127455
theorem B4944509 : Blo 1464552 4944509 := bstep (se 3 (by rfl) ⟨927095, by rfl⟩ : syracuseStep 4944509 = 1854191) B1854191
theorem B3298283 : Blo 1464552 3298283 := bstep (se 1 (by rfl) ⟨2473712, by rfl⟩ : syracuseStep 3298283 = 4947425) B4947425
theorem B22565945 : Blo 1464552 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B4822525 : Blo 1464552 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B3298985 : Blo 1464552 3298985 := bstep (se 2 (by rfl) ⟨1237119, by rfl⟩ : syracuseStep 3298985 = 2474239) B2474239
theorem B3299111 : Blo 1464552 3299111 := bstep (se 1 (by rfl) ⟨2474333, by rfl⟩ : syracuseStep 3299111 = 4948667) B4948667
theorem B6027311 : Blo 1464552 6027311 := bstep (se 1 (by rfl) ⟨4520483, by rfl⟩ : syracuseStep 6027311 = 9040967) B9040967
theorem B8345753 : Blo 1464552 8345753 := bstep (se 2 (by rfl) ⟨3129657, by rfl⟩ : syracuseStep 8345753 = 6259315) B6259315
theorem B18783323 : Blo 1464552 18783323 := bstep (se 1 (by rfl) ⟨14087492, by rfl⟩ : syracuseStep 18783323 = 28174985) B28174985
theorem B3710063 : Blo 1464552 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B59514041 : Blo 1464552 59514041 := bstep (se 2 (by rfl) ⟨22317765, by rfl⟩ : syracuseStep 59514041 = 44635531) B44635531
theorem B180608291 : Blo 1464552 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B1465663 : Blo 1464552 1465663 := bstep (se 1 (by rfl) ⟨1099247, by rfl⟩ : syracuseStep 1465663 = 2198495) B2198495
theorem B5643935 : Blo 1464552 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B37568285 : Blo 1464552 37568285 := bstep (se 3 (by rfl) ⟨7044053, by rfl⟩ : syracuseStep 37568285 = 14088107) B14088107
theorem B17817421 : Blo 1464552 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B15835283 : Blo 1464552 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B1466527 : Blo 1464552 1466527 := bstep (se 1 (by rfl) ⟨1099895, by rfl⟩ : syracuseStep 1466527 = 2199791) B2199791
theorem B5562665 : Blo 1464552 5562665 := bstep (se 2 (by rfl) ⟨2085999, by rfl⟩ : syracuseStep 5562665 = 4171999) B4171999
theorem B2474543 : Blo 1464552 2474543 := bstep (se 1 (by rfl) ⟨1855907, by rfl⟩ : syracuseStep 2474543 = 3711815) B3711815
theorem B4948775 : Blo 1464552 4948775 := bstep (se 1 (by rfl) ⟨3711581, by rfl⟩ : syracuseStep 4948775 = 7423163) B7423163
theorem B5563835 : Blo 1464552 5563835 := bstep (se 1 (by rfl) ⟨4172876, by rfl⟩ : syracuseStep 5563835 = 8345753) B8345753
theorem B2196971 : Blo 1464552 2196971 := bstep (se 1 (by rfl) ⟨1647728, by rfl⟩ : syracuseStep 2196971 = 3295457) B3295457
theorem B2197151 : Blo 1464552 2197151 := bstep (se 1 (by rfl) ⟨1647863, by rfl⟩ : syracuseStep 2197151 = 3295727) B3295727
theorem B2197607 : Blo 1464552 2197607 := bstep (se 1 (by rfl) ⟨1648205, by rfl⟩ : syracuseStep 2197607 = 3296411) B3296411
theorem B39676027 : Blo 1464552 39676027 := bstep (se 1 (by rfl) ⟨29757020, by rfl⟩ : syracuseStep 39676027 = 59514041) B59514041
theorem B8145119 : Blo 1464552 8145119 := bstep (se 1 (by rfl) ⟨6108839, by rfl⟩ : syracuseStep 8145119 = 12217679) B12217679
theorem B3762623 : Blo 1464552 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B21121499 : Blo 1464552 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B25045523 : Blo 1464552 25045523 := bstep (se 1 (by rfl) ⟨18784142, by rfl⟩ : syracuseStep 25045523 = 37568285) B37568285
theorem B2198375 : Blo 1464552 2198375 := bstep (se 1 (by rfl) ⟨1648781, by rfl⟩ : syracuseStep 2198375 = 3297563) B3297563
theorem B3296339 : Blo 1464552 3296339 := bstep (se 1 (by rfl) ⟨2472254, by rfl⟩ : syracuseStep 3296339 = 4944509) B4944509
theorem B4943159 : Blo 1464552 4943159 := bstep (se 1 (by rfl) ⟨3707369, by rfl⟩ : syracuseStep 4943159 = 7414739) B7414739
theorem B2198855 : Blo 1464552 2198855 := bstep (se 1 (by rfl) ⟨1649141, by rfl⟩ : syracuseStep 2198855 = 3298283) B3298283
theorem B7417169 : Blo 1464552 7417169 := bstep (se 2 (by rfl) ⟨2781438, by rfl⟩ : syracuseStep 7417169 = 5562877) B5562877
theorem B71331191 : Blo 1464552 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B15043963 : Blo 1464552 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B18787787 : Blo 1464552 18787787 := bstep (se 1 (by rfl) ⟨14090840, by rfl⟩ : syracuseStep 18787787 = 28181681) B28181681
theorem B14085647 : Blo 1464552 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B2199323 : Blo 1464552 2199323 := bstep (se 1 (by rfl) ⟨1649492, by rfl⟩ : syracuseStep 2199323 = 3298985) B3298985
theorem B2199407 : Blo 1464552 2199407 := bstep (se 1 (by rfl) ⟨1649555, by rfl⟩ : syracuseStep 2199407 = 3299111) B3299111
theorem B4018207 : Blo 1464552 4018207 := bstep (se 1 (by rfl) ⟨3013655, by rfl⟩ : syracuseStep 4018207 = 6027311) B6027311
theorem B12522215 : Blo 1464552 12522215 := bstep (se 1 (by rfl) ⟨9391661, by rfl⟩ : syracuseStep 12522215 = 18783323) B18783323
theorem B9516059 : Blo 1464552 9516059 := bstep (se 1 (by rfl) ⟨7137044, by rfl⟩ : syracuseStep 9516059 = 14274089) B14274089
theorem B4945535 : Blo 1464552 4945535 := bstep (se 1 (by rfl) ⟨3709151, by rfl⟩ : syracuseStep 4945535 = 7418303) B7418303
theorem B17831819 : Blo 1464552 17831819 := bstep (se 1 (by rfl) ⟨13373864, by rfl⟩ : syracuseStep 17831819 = 26747729) B26747729
theorem B1464815 : Blo 1464552 1464815 := bstep (se 1 (by rfl) ⟨1098611, by rfl⟩ : syracuseStep 1464815 = 2197223) B2197223
theorem B1464943 : Blo 1464552 1464943 := bstep (se 1 (by rfl) ⟨1098707, by rfl⟩ : syracuseStep 1464943 = 2197415) B2197415
theorem B18553799 : Blo 1464552 18553799 := bstep (se 1 (by rfl) ⟨13915349, by rfl⟩ : syracuseStep 18553799 = 27830699) B27830699
theorem B1465327 : Blo 1464552 1465327 := bstep (se 1 (by rfl) ⟨1098995, by rfl⟩ : syracuseStep 1465327 = 2197991) B2197991
theorem B4693295 : Blo 1464552 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B6430033 : Blo 1464552 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B2473375 : Blo 1464552 2473375 := bstep (se 1 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 2473375 = 3710063) B3710063
theorem B1465759 : Blo 1464552 1465759 := bstep (se 1 (by rfl) ⟨1099319, by rfl⟩ : syracuseStep 1465759 = 2198639) B2198639
theorem B17833375 : Blo 1464552 17833375 := bstep (se 1 (by rfl) ⟨13375031, by rfl⟩ : syracuseStep 17833375 = 26750063) B26750063
theorem B120405527 : Blo 1464552 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B3710519 : Blo 1464552 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B1466015 : Blo 1464552 1466015 := bstep (se 1 (by rfl) ⟨1099511, by rfl⟩ : syracuseStep 1466015 = 2199023) B2199023
theorem B23756561 : Blo 1464552 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B7135171 : Blo 1464552 7135171 := bstep (se 1 (by rfl) ⟨5351378, by rfl⟩ : syracuseStep 7135171 = 10702757) B10702757
theorem B5357609 : Blo 1464552 5357609 := bstep (se 2 (by rfl) ⟨2009103, by rfl⟩ : syracuseStep 5357609 = 4018207) B4018207
theorem B8348143 : Blo 1464552 8348143 := bstep (se 1 (by rfl) ⟨6261107, by rfl⟩ : syracuseStep 8348143 = 12522215) B12522215
theorem B11887879 : Blo 1464552 11887879 := bstep (se 1 (by rfl) ⟨8915909, by rfl⟩ : syracuseStep 11887879 = 17831819) B17831819
theorem B2508415 : Blo 1464552 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B16697015 : Blo 1464552 16697015 := bstep (se 1 (by rfl) ⟨12522761, by rfl⟩ : syracuseStep 16697015 = 25045523) B25045523
theorem B2197559 : Blo 1464552 2197559 := bstep (se 1 (by rfl) ⟨1648169, by rfl⟩ : syracuseStep 2197559 = 3296339) B3296339
theorem B95111333 : Blo 1464552 95111333 := bstep (se 4 (by rfl) ⟨8916687, by rfl⟩ : syracuseStep 95111333 = 17833375) B17833375
theorem B3295439 : Blo 1464552 3295439 := bstep (se 1 (by rfl) ⟨2471579, by rfl⟩ : syracuseStep 3295439 = 4943159) B4943159
theorem B9390431 : Blo 1464552 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B38054245 : Blo 1464552 38054245 := bstep (se 4 (by rfl) ⟨3567585, by rfl⟩ : syracuseStep 38054245 = 7135171) B7135171
theorem B15837707 : Blo 1464552 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B1649695 : Blo 1464552 1649695 := bstep (se 1 (by rfl) ⟨1237271, by rfl⟩ : syracuseStep 1649695 = 2474543) B2474543
theorem B6344039 : Blo 1464552 6344039 := bstep (se 1 (by rfl) ⟨4758029, by rfl⟩ : syracuseStep 6344039 = 9516059) B9516059
theorem B3297023 : Blo 1464552 3297023 := bstep (se 1 (by rfl) ⟨2472767, by rfl⟩ : syracuseStep 3297023 = 4945535) B4945535
theorem B8573377 : Blo 1464552 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B20058617 : Blo 1464552 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B3297833 : Blo 1464552 3297833 := bstep (se 2 (by rfl) ⟨1236687, by rfl⟩ : syracuseStep 3297833 = 2473375) B2473375
theorem B4944779 : Blo 1464552 4944779 := bstep (se 1 (by rfl) ⟨3708584, by rfl⟩ : syracuseStep 4944779 = 7417169) B7417169
theorem B80270351 : Blo 1464552 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B10556855 : Blo 1464552 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B52901369 : Blo 1464552 52901369 := bstep (se 2 (by rfl) ⟨19838013, by rfl⟩ : syracuseStep 52901369 = 39676027) B39676027
theorem B3708443 : Blo 1464552 3708443 := bstep (se 1 (by rfl) ⟨2781332, by rfl⟩ : syracuseStep 3708443 = 5562665) B5562665
theorem B3299183 : Blo 1464552 3299183 := bstep (se 1 (by rfl) ⟨2474387, by rfl⟩ : syracuseStep 3299183 = 4948775) B4948775
theorem B3709223 : Blo 1464552 3709223 := bstep (se 1 (by rfl) ⟨2781917, by rfl⟩ : syracuseStep 3709223 = 5563835) B5563835
theorem B1464647 : Blo 1464552 1464647 := bstep (se 1 (by rfl) ⟨1098485, by rfl⟩ : syracuseStep 1464647 = 2196971) B2196971
theorem B1464767 : Blo 1464552 1464767 := bstep (se 1 (by rfl) ⟨1098575, by rfl⟩ : syracuseStep 1464767 = 2197151) B2197151
theorem B1465071 : Blo 1464552 1465071 := bstep (se 1 (by rfl) ⟨1098803, by rfl⟩ : syracuseStep 1465071 = 2197607) B2197607
theorem B5430079 : Blo 1464552 5430079 := bstep (se 1 (by rfl) ⟨4072559, by rfl⟩ : syracuseStep 5430079 = 8145119) B8145119
theorem B14080999 : Blo 1464552 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B1465583 : Blo 1464552 1465583 := bstep (se 1 (by rfl) ⟨1099187, by rfl⟩ : syracuseStep 1465583 = 2198375) B2198375
theorem B12369199 : Blo 1464552 12369199 := bstep (se 1 (by rfl) ⟨9276899, by rfl⟩ : syracuseStep 12369199 = 18553799) B18553799
theorem B3128863 : Blo 1464552 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B1465903 : Blo 1464552 1465903 := bstep (se 1 (by rfl) ⟨1099427, by rfl⟩ : syracuseStep 1465903 = 2198855) B2198855
theorem B47554127 : Blo 1464552 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B12525191 : Blo 1464552 12525191 := bstep (se 1 (by rfl) ⟨9393893, by rfl⟩ : syracuseStep 12525191 = 18787787) B18787787
theorem B2473679 : Blo 1464552 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B1466215 : Blo 1464552 1466215 := bstep (se 1 (by rfl) ⟨1099661, by rfl⟩ : syracuseStep 1466215 = 2199323) B2199323
theorem B1466271 : Blo 1464552 1466271 := bstep (se 1 (by rfl) ⟨1099703, by rfl⟩ : syracuseStep 1466271 = 2199407) B2199407
theorem B3571739 : Blo 1464552 3571739 := bstep (se 1 (by rfl) ⟨2678804, by rfl⟩ : syracuseStep 3571739 = 5357609) B5357609
theorem B13378213 : Blo 1464552 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B16917437 : Blo 1464552 16917437 := bstep (se 3 (by rfl) ⟨3172019, by rfl⟩ : syracuseStep 16917437 = 6344039) B6344039
theorem B7037903 : Blo 1464552 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B35267579 : Blo 1464552 35267579 := bstep (se 1 (by rfl) ⟨26450684, by rfl⟩ : syracuseStep 35267579 = 52901369) B52901369
theorem B63407555 : Blo 1464552 63407555 := bstep (se 1 (by rfl) ⟨47555666, by rfl⟩ : syracuseStep 63407555 = 95111333) B95111333
theorem B2196959 : Blo 1464552 2196959 := bstep (se 1 (by rfl) ⟨1647719, by rfl⟩ : syracuseStep 2196959 = 3295439) B3295439
theorem B28960421 : Blo 1464552 28960421 := bstep (se 4 (by rfl) ⟨2715039, by rfl⟩ : syracuseStep 28960421 = 5430079) B5430079
theorem B16492265 : Blo 1464552 16492265 := bstep (se 2 (by rfl) ⟨6184599, by rfl⟩ : syracuseStep 16492265 = 12369199) B12369199
theorem B4171817 : Blo 1464552 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B8350127 : Blo 1464552 8350127 := bstep (se 1 (by rfl) ⟨6262595, by rfl⟩ : syracuseStep 8350127 = 12525191) B12525191
theorem B1649119 : Blo 1464552 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B2198015 : Blo 1464552 2198015 := bstep (se 1 (by rfl) ⟨1648511, by rfl⟩ : syracuseStep 2198015 = 3297023) B3297023
theorem B13372411 : Blo 1464552 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B2198555 : Blo 1464552 2198555 := bstep (se 1 (by rfl) ⟨1648916, by rfl⟩ : syracuseStep 2198555 = 3297833) B3297833
theorem B11431169 : Blo 1464552 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B3296519 : Blo 1464552 3296519 := bstep (se 1 (by rfl) ⟨2472389, by rfl⟩ : syracuseStep 3296519 = 4944779) B4944779
theorem B53513567 : Blo 1464552 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B2199455 : Blo 1464552 2199455 := bstep (se 1 (by rfl) ⟨1649591, by rfl⟩ : syracuseStep 2199455 = 3299183) B3299183
theorem B2199593 : Blo 1464552 2199593 := bstep (se 2 (by rfl) ⟨824847, by rfl⟩ : syracuseStep 2199593 = 1649695) B1649695
theorem B50738993 : Blo 1464552 50738993 := bstep (se 2 (by rfl) ⟨19027122, by rfl⟩ : syracuseStep 50738993 = 38054245) B38054245
theorem B11130857 : Blo 1464552 11130857 := bstep (se 2 (by rfl) ⟨4174071, by rfl⟩ : syracuseStep 11130857 = 8348143) B8348143
theorem B25041149 : Blo 1464552 25041149 := bstep (se 3 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 25041149 = 9390431) B9390431
theorem B2472295 : Blo 1464552 2472295 := bstep (se 1 (by rfl) ⟨1854221, by rfl⟩ : syracuseStep 2472295 = 3708443) B3708443
theorem B11131343 : Blo 1464552 11131343 := bstep (se 1 (by rfl) ⟨8348507, by rfl⟩ : syracuseStep 11131343 = 16697015) B16697015
theorem B18774665 : Blo 1464552 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B1465039 : Blo 1464552 1465039 := bstep (se 1 (by rfl) ⟨1098779, by rfl⟩ : syracuseStep 1465039 = 2197559) B2197559
theorem B2472815 : Blo 1464552 2472815 := bstep (se 1 (by rfl) ⟨1854611, by rfl⟩ : syracuseStep 2472815 = 3709223) B3709223
theorem B10558471 : Blo 1464552 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B15850505 : Blo 1464552 15850505 := bstep (se 2 (by rfl) ⟨5943939, by rfl⟩ : syracuseStep 15850505 = 11887879) B11887879
theorem B31702751 : Blo 1464552 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B1466395 : Blo 1464552 1466395 := bstep (se 1 (by rfl) ⟨1099796, by rfl⟩ : syracuseStep 1466395 = 2199593) B2199593
theorem B23511719 : Blo 1464552 23511719 := bstep (se 1 (by rfl) ⟨17633789, by rfl⟩ : syracuseStep 23511719 = 35267579) B35267579
theorem B42271703 : Blo 1464552 42271703 := bstep (se 1 (by rfl) ⟨31703777, by rfl⟩ : syracuseStep 42271703 = 63407555) B63407555
theorem B33825995 : Blo 1464552 33825995 := bstep (se 1 (by rfl) ⟨25369496, by rfl⟩ : syracuseStep 33825995 = 50738993) B50738993
theorem B77227789 : Blo 1464552 77227789 := bstep (se 3 (by rfl) ⟨14480210, by rfl⟩ : syracuseStep 77227789 = 28960421) B28960421
theorem B1648543 : Blo 1464552 1648543 := bstep (se 1 (by rfl) ⟨1236407, by rfl⟩ : syracuseStep 1648543 = 2472815) B2472815
theorem B7620779 : Blo 1464552 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B2197679 : Blo 1464552 2197679 := bstep (se 1 (by rfl) ⟨1648259, by rfl⟩ : syracuseStep 2197679 = 3296519) B3296519
theorem B175917493 : Blo 1464552 175917493 := bstep (se 5 (by rfl) ⟨8246132, by rfl⟩ : syracuseStep 175917493 = 16492265) B16492265
theorem B3296393 : Blo 1464552 3296393 := bstep (se 2 (by rfl) ⟨1236147, by rfl⟩ : syracuseStep 3296393 = 2472295) B2472295
theorem B2198825 : Blo 1464552 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B17837617 : Blo 1464552 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B17829881 : Blo 1464552 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B14077961 : Blo 1464552 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B2781211 : Blo 1464552 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B5566751 : Blo 1464552 5566751 := bstep (se 1 (by rfl) ⟨4175063, by rfl⟩ : syracuseStep 5566751 = 8350127) B8350127
theorem B2381159 : Blo 1464552 2381159 := bstep (se 1 (by rfl) ⟨1785869, by rfl⟩ : syracuseStep 2381159 = 3571739) B3571739
theorem B42268013 : Blo 1464552 42268013 := bstep (se 3 (by rfl) ⟨7925252, by rfl⟩ : syracuseStep 42268013 = 15850505) B15850505
theorem B11278291 : Blo 1464552 11278291 := bstep (se 1 (by rfl) ⟨8458718, by rfl⟩ : syracuseStep 11278291 = 16917437) B16917437
theorem B4691935 : Blo 1464552 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B1464639 : Blo 1464552 1464639 := bstep (se 1 (by rfl) ⟨1098479, by rfl⟩ : syracuseStep 1464639 = 2196959) B2196959
theorem B7420571 : Blo 1464552 7420571 := bstep (se 1 (by rfl) ⟨5565428, by rfl⟩ : syracuseStep 7420571 = 11130857) B11130857
theorem B16694099 : Blo 1464552 16694099 := bstep (se 1 (by rfl) ⟨12520574, by rfl⟩ : syracuseStep 16694099 = 25041149) B25041149
theorem B7420895 : Blo 1464552 7420895 := bstep (se 1 (by rfl) ⟨5565671, by rfl⟩ : syracuseStep 7420895 = 11131343) B11131343
theorem B1465343 : Blo 1464552 1465343 := bstep (se 1 (by rfl) ⟨1099007, by rfl⟩ : syracuseStep 1465343 = 2198015) B2198015
theorem B12516443 : Blo 1464552 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B1465703 : Blo 1464552 1465703 := bstep (se 1 (by rfl) ⟨1099277, by rfl⟩ : syracuseStep 1465703 = 2198555) B2198555
theorem B35675711 : Blo 1464552 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B21135167 : Blo 1464552 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B1466303 : Blo 1464552 1466303 := bstep (se 1 (by rfl) ⟨1099727, by rfl⟩ : syracuseStep 1466303 = 2199455) B2199455
theorem B3711167 : Blo 1464552 3711167 := bstep (se 1 (by rfl) ⟨2783375, by rfl⟩ : syracuseStep 3711167 = 5566751) B5566751
theorem B28181135 : Blo 1464552 28181135 := bstep (se 1 (by rfl) ⟨21135851, by rfl⟩ : syracuseStep 28181135 = 42271703) B42271703
theorem B5080519 : Blo 1464552 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B23783489 : Blo 1464552 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B2197595 : Blo 1464552 2197595 := bstep (se 1 (by rfl) ⟨1648196, by rfl⟩ : syracuseStep 2197595 = 3296393) B3296393
theorem B23783807 : Blo 1464552 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B2198057 : Blo 1464552 2198057 := bstep (se 2 (by rfl) ⟨824271, by rfl⟩ : syracuseStep 2198057 = 1648543) B1648543
theorem B11886587 : Blo 1464552 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B234556657 : Blo 1464552 234556657 := bstep (se 2 (by rfl) ⟨87958746, by rfl⟩ : syracuseStep 234556657 = 175917493) B175917493
theorem B62697917 : Blo 1464552 62697917 := bstep (se 3 (by rfl) ⟨11755859, by rfl⟩ : syracuseStep 62697917 = 23511719) B23511719
theorem B11129399 : Blo 1464552 11129399 := bstep (se 1 (by rfl) ⟨8347049, by rfl⟩ : syracuseStep 11129399 = 16694099) B16694099
theorem B8344295 : Blo 1464552 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B102970385 : Blo 1464552 102970385 := bstep (se 2 (by rfl) ⟨38613894, by rfl⟩ : syracuseStep 102970385 = 77227789) B77227789
theorem B25023653 : Blo 1464552 25023653 := bstep (se 4 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 25023653 = 4691935) B4691935
theorem B15037721 : Blo 1464552 15037721 := bstep (se 2 (by rfl) ⟨5639145, by rfl⟩ : syracuseStep 15037721 = 11278291) B11278291
theorem B9385307 : Blo 1464552 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B3708281 : Blo 1464552 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B22550663 : Blo 1464552 22550663 := bstep (se 1 (by rfl) ⟨16912997, by rfl⟩ : syracuseStep 22550663 = 33825995) B33825995
theorem B1587439 : Blo 1464552 1587439 := bstep (se 1 (by rfl) ⟨1190579, by rfl⟩ : syracuseStep 1587439 = 2381159) B2381159
theorem B28178675 : Blo 1464552 28178675 := bstep (se 1 (by rfl) ⟨21134006, by rfl⟩ : syracuseStep 28178675 = 42268013) B42268013
theorem B1465119 : Blo 1464552 1465119 := bstep (se 1 (by rfl) ⟨1098839, by rfl⟩ : syracuseStep 1465119 = 2197679) B2197679
theorem B4947047 : Blo 1464552 4947047 := bstep (se 1 (by rfl) ⟨3710285, by rfl⟩ : syracuseStep 4947047 = 7420571) B7420571
theorem B4947263 : Blo 1464552 4947263 := bstep (se 1 (by rfl) ⟨3710447, by rfl⟩ : syracuseStep 4947263 = 7420895) B7420895
theorem B1465883 : Blo 1464552 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B14090111 : Blo 1464552 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B2474111 : Blo 1464552 2474111 := bstep (se 1 (by rfl) ⟨1855583, by rfl⟩ : syracuseStep 2474111 = 3711167) B3711167
theorem B5562863 : Blo 1464552 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B15033775 : Blo 1464552 15033775 := bstep (se 1 (by rfl) ⟨11275331, by rfl⟩ : syracuseStep 15033775 = 22550663) B22550663
theorem B18785783 : Blo 1464552 18785783 := bstep (se 1 (by rfl) ⟨14089337, by rfl⟩ : syracuseStep 18785783 = 28178675) B28178675
theorem B7924391 : Blo 1464552 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B41798611 : Blo 1464552 41798611 := bstep (se 1 (by rfl) ⟨31348958, by rfl⟩ : syracuseStep 41798611 = 62697917) B62697917
theorem B2116585 : Blo 1464552 2116585 := bstep (se 2 (by rfl) ⟨793719, by rfl⟩ : syracuseStep 2116585 = 1587439) B1587439
theorem B18787423 : Blo 1464552 18787423 := bstep (se 1 (by rfl) ⟨14090567, by rfl⟩ : syracuseStep 18787423 = 28181135) B28181135
theorem B16682435 : Blo 1464552 16682435 := bstep (se 1 (by rfl) ⟨12511826, by rfl⟩ : syracuseStep 16682435 = 25023653) B25023653
theorem B15855659 : Blo 1464552 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B15855871 : Blo 1464552 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B3298031 : Blo 1464552 3298031 := bstep (se 1 (by rfl) ⟨2473523, by rfl⟩ : syracuseStep 3298031 = 4947047) B4947047
theorem B3298175 : Blo 1464552 3298175 := bstep (se 1 (by rfl) ⟨2473631, by rfl⟩ : syracuseStep 3298175 = 4947263) B4947263
theorem B5003875349 : Blo 1464552 5003875349 := bstep (se 6 (by rfl) ⟨117278328, by rfl⟩ : syracuseStep 5003875349 = 234556657) B234556657
theorem B9393407 : Blo 1464552 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B7419599 : Blo 1464552 7419599 := bstep (se 1 (by rfl) ⟨5564699, by rfl⟩ : syracuseStep 7419599 = 11129399) B11129399
theorem B68646923 : Blo 1464552 68646923 := bstep (se 1 (by rfl) ⟨51485192, by rfl⟩ : syracuseStep 68646923 = 102970385) B102970385
theorem B10025147 : Blo 1464552 10025147 := bstep (se 1 (by rfl) ⟨7518860, by rfl⟩ : syracuseStep 10025147 = 15037721) B15037721
theorem B6256871 : Blo 1464552 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B2472187 : Blo 1464552 2472187 := bstep (se 1 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 2472187 = 3708281) B3708281
theorem B1465063 : Blo 1464552 1465063 := bstep (se 1 (by rfl) ⟨1098797, by rfl⟩ : syracuseStep 1465063 = 2197595) B2197595
theorem B1465371 : Blo 1464552 1465371 := bstep (se 1 (by rfl) ⟨1099028, by rfl⟩ : syracuseStep 1465371 = 2198057) B2198057
theorem B6774025 : Blo 1464552 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B4171247 : Blo 1464552 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B10570439 : Blo 1464552 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B1649407 : Blo 1464552 1649407 := bstep (se 1 (by rfl) ⟨1237055, by rfl⟩ : syracuseStep 1649407 = 2474111) B2474111
theorem B3296249 : Blo 1464552 3296249 := bstep (se 2 (by rfl) ⟨1236093, by rfl⟩ : syracuseStep 3296249 = 2472187) B2472187
theorem B2198687 : Blo 1464552 2198687 := bstep (se 1 (by rfl) ⟨1649015, by rfl⟩ : syracuseStep 2198687 = 3298031) B3298031
theorem B2198783 : Blo 1464552 2198783 := bstep (se 1 (by rfl) ⟨1649087, by rfl⟩ : syracuseStep 2198783 = 3298175) B3298175
theorem B3335916899 : Blo 1464552 3335916899 := bstep (se 1 (by rfl) ⟨2501937674, by rfl⟩ : syracuseStep 3335916899 = 5003875349) B5003875349
theorem B6262271 : Blo 1464552 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B2822113 : Blo 1464552 2822113 := bstep (se 2 (by rfl) ⟨1058292, by rfl⟩ : syracuseStep 2822113 = 2116585) B2116585
theorem B45764615 : Blo 1464552 45764615 := bstep (se 1 (by rfl) ⟨34323461, by rfl⟩ : syracuseStep 45764615 = 68646923) B68646923
theorem B9032033 : Blo 1464552 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B11121623 : Blo 1464552 11121623 := bstep (se 1 (by rfl) ⟨8341217, by rfl⟩ : syracuseStep 11121623 = 16682435) B16682435
theorem B222925925 : Blo 1464552 222925925 := bstep (se 4 (by rfl) ⟨20899305, by rfl⟩ : syracuseStep 222925925 = 41798611) B41798611
theorem B3708575 : Blo 1464552 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B21141161 : Blo 1464552 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B12523855 : Blo 1464552 12523855 := bstep (se 1 (by rfl) ⟨9392891, by rfl⟩ : syracuseStep 12523855 = 18785783) B18785783
theorem B4946399 : Blo 1464552 4946399 := bstep (se 1 (by rfl) ⟨3709799, by rfl⟩ : syracuseStep 4946399 = 7419599) B7419599
theorem B6683431 : Blo 1464552 6683431 := bstep (se 1 (by rfl) ⟨5012573, by rfl⟩ : syracuseStep 6683431 = 10025147) B10025147
theorem B25049897 : Blo 1464552 25049897 := bstep (se 2 (by rfl) ⟨9393711, by rfl⟩ : syracuseStep 25049897 = 18787423) B18787423
theorem B5282927 : Blo 1464552 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B20045033 : Blo 1464552 20045033 := bstep (se 2 (by rfl) ⟨7516887, by rfl⟩ : syracuseStep 20045033 = 15033775) B15033775
theorem B7414415 : Blo 1464552 7414415 := bstep (se 1 (by rfl) ⟨5560811, by rfl⟩ : syracuseStep 7414415 = 11121623) B11121623
theorem B24085421 : Blo 1464552 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B7046959 : Blo 1464552 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B2197499 : Blo 1464552 2197499 := bstep (se 1 (by rfl) ⟨1648124, by rfl⟩ : syracuseStep 2197499 = 3296249) B3296249
theorem B13363355 : Blo 1464552 13363355 := bstep (se 1 (by rfl) ⟨10022516, by rfl⟩ : syracuseStep 13363355 = 20045033) B20045033
theorem B3762817 : Blo 1464552 3762817 := bstep (se 2 (by rfl) ⟨1411056, by rfl⟩ : syracuseStep 3762817 = 2822113) B2822113
theorem B30509743 : Blo 1464552 30509743 := bstep (se 1 (by rfl) ⟨22882307, by rfl⟩ : syracuseStep 30509743 = 45764615) B45764615
theorem B16698473 : Blo 1464552 16698473 := bstep (se 2 (by rfl) ⟨6261927, by rfl⟩ : syracuseStep 16698473 = 12523855) B12523855
theorem B2780831 : Blo 1464552 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B2199209 : Blo 1464552 2199209 := bstep (se 2 (by rfl) ⟨824703, by rfl⟩ : syracuseStep 2199209 = 1649407) B1649407
theorem B14094107 : Blo 1464552 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B3297599 : Blo 1464552 3297599 := bstep (se 1 (by rfl) ⟨2473199, by rfl⟩ : syracuseStep 3297599 = 4946399) B4946399
theorem B16699931 : Blo 1464552 16699931 := bstep (se 1 (by rfl) ⟨12524948, by rfl⟩ : syracuseStep 16699931 = 25049897) B25049897
theorem B2223944599 : Blo 1464552 2223944599 := bstep (se 1 (by rfl) ⟨1667958449, by rfl⟩ : syracuseStep 2223944599 = 3335916899) B3335916899
theorem B4174847 : Blo 1464552 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B148617283 : Blo 1464552 148617283 := bstep (se 1 (by rfl) ⟨111462962, by rfl⟩ : syracuseStep 148617283 = 222925925) B222925925
theorem B8911241 : Blo 1464552 8911241 := bstep (se 2 (by rfl) ⟨3341715, by rfl⟩ : syracuseStep 8911241 = 6683431) B6683431
theorem B2472383 : Blo 1464552 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B3521951 : Blo 1464552 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B1465791 : Blo 1464552 1465791 := bstep (se 1 (by rfl) ⟨1099343, by rfl⟩ : syracuseStep 1465791 = 2198687) B2198687
theorem B1465855 : Blo 1464552 1465855 := bstep (se 1 (by rfl) ⟨1099391, by rfl⟩ : syracuseStep 1465855 = 2198783) B2198783
theorem B198156377 : Blo 1464552 198156377 := bstep (se 2 (by rfl) ⟨74308641, by rfl⟩ : syracuseStep 198156377 = 148617283) B148617283
theorem B11133287 : Blo 1464552 11133287 := bstep (se 1 (by rfl) ⟨8349965, by rfl⟩ : syracuseStep 11133287 = 16699931) B16699931
theorem B16056947 : Blo 1464552 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B2965259465 : Blo 1464552 2965259465 := bstep (se 2 (by rfl) ⟨1111972299, by rfl⟩ : syracuseStep 2965259465 = 2223944599) B2223944599
theorem B5940827 : Blo 1464552 5940827 := bstep (se 1 (by rfl) ⟨4455620, by rfl⟩ : syracuseStep 5940827 = 8911241) B8911241
theorem B1648255 : Blo 1464552 1648255 := bstep (se 1 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 1648255 = 2472383) B2472383
theorem B7415549 : Blo 1464552 7415549 := bstep (se 3 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 7415549 = 2780831) B2780831
theorem B2198399 : Blo 1464552 2198399 := bstep (se 1 (by rfl) ⟨1648799, by rfl⟩ : syracuseStep 2198399 = 3297599) B3297599
theorem B4942943 : Blo 1464552 4942943 := bstep (se 1 (by rfl) ⟨3707207, by rfl⟩ : syracuseStep 4942943 = 7414415) B7414415
theorem B8908903 : Blo 1464552 8908903 := bstep (se 1 (by rfl) ⟨6681677, by rfl⟩ : syracuseStep 8908903 = 13363355) B13363355
theorem B2347967 : Blo 1464552 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B2783231 : Blo 1464552 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B20068357 : Blo 1464552 20068357 := bstep (se 4 (by rfl) ⟨1881408, by rfl⟩ : syracuseStep 20068357 = 3762817) B3762817
theorem B40679657 : Blo 1464552 40679657 := bstep (se 2 (by rfl) ⟨15254871, by rfl⟩ : syracuseStep 40679657 = 30509743) B30509743
theorem B1464999 : Blo 1464552 1464999 := bstep (se 1 (by rfl) ⟨1098749, by rfl⟩ : syracuseStep 1464999 = 2197499) B2197499
theorem B11132315 : Blo 1464552 11132315 := bstep (se 1 (by rfl) ⟨8349236, by rfl⟩ : syracuseStep 11132315 = 16698473) B16698473
theorem B9395945 : Blo 1464552 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B1466139 : Blo 1464552 1466139 := bstep (se 1 (by rfl) ⟨1099604, by rfl⟩ : syracuseStep 1466139 = 2199209) B2199209
theorem B9396071 : Blo 1464552 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B132104251 : Blo 1464552 132104251 := bstep (se 1 (by rfl) ⟨99078188, by rfl⟩ : syracuseStep 132104251 = 198156377) B198156377
theorem B11878537 : Blo 1464552 11878537 := bstep (se 2 (by rfl) ⟨4454451, by rfl⟩ : syracuseStep 11878537 = 8908903) B8908903
theorem B7422191 : Blo 1464552 7422191 := bstep (se 1 (by rfl) ⟨5566643, by rfl⟩ : syracuseStep 7422191 = 11133287) B11133287
theorem B3295295 : Blo 1464552 3295295 := bstep (se 1 (by rfl) ⟨2471471, by rfl⟩ : syracuseStep 3295295 = 4942943) B4942943
theorem B2197673 : Blo 1464552 2197673 := bstep (se 2 (by rfl) ⟨824127, by rfl⟩ : syracuseStep 2197673 = 1648255) B1648255
theorem B6261245 : Blo 1464552 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B26757809 : Blo 1464552 26757809 := bstep (se 2 (by rfl) ⟨10034178, by rfl⟩ : syracuseStep 26757809 = 20068357) B20068357
theorem B1976839643 : Blo 1464552 1976839643 := bstep (se 1 (by rfl) ⟨1482629732, by rfl⟩ : syracuseStep 1976839643 = 2965259465) B2965259465
theorem B3960551 : Blo 1464552 3960551 := bstep (se 1 (by rfl) ⟨2970413, by rfl⟩ : syracuseStep 3960551 = 5940827) B5940827
theorem B4943699 : Blo 1464552 4943699 := bstep (se 1 (by rfl) ⟨3707774, by rfl⟩ : syracuseStep 4943699 = 7415549) B7415549
theorem B1855487 : Blo 1464552 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B27119771 : Blo 1464552 27119771 := bstep (se 1 (by rfl) ⟨20339828, by rfl⟩ : syracuseStep 27119771 = 40679657) B40679657
theorem B6263963 : Blo 1464552 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B6264047 : Blo 1464552 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B10704631 : Blo 1464552 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B1465599 : Blo 1464552 1465599 := bstep (se 1 (by rfl) ⟨1099199, by rfl⟩ : syracuseStep 1465599 = 2198399) B2198399
theorem B7421543 : Blo 1464552 7421543 := bstep (se 1 (by rfl) ⟨5566157, by rfl⟩ : syracuseStep 7421543 = 11132315) B11132315
theorem B18079847 : Blo 1464552 18079847 := bstep (se 1 (by rfl) ⟨13559885, by rfl⟩ : syracuseStep 18079847 = 27119771) B27119771
theorem B4948127 : Blo 1464552 4948127 := bstep (se 1 (by rfl) ⟨3711095, by rfl⟩ : syracuseStep 4948127 = 7422191) B7422191
theorem B2196863 : Blo 1464552 2196863 := bstep (se 1 (by rfl) ⟨1647647, by rfl⟩ : syracuseStep 2196863 = 3295295) B3295295
theorem B14272841 : Blo 1464552 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B2640367 : Blo 1464552 2640367 := bstep (se 1 (by rfl) ⟨1980275, by rfl⟩ : syracuseStep 2640367 = 3960551) B3960551
theorem B3295799 : Blo 1464552 3295799 := bstep (se 1 (by rfl) ⟨2471849, by rfl⟩ : syracuseStep 3295799 = 4943699) B4943699
theorem B176139001 : Blo 1464552 176139001 := bstep (se 2 (by rfl) ⟨66052125, by rfl⟩ : syracuseStep 176139001 = 132104251) B132104251
theorem B15838049 : Blo 1464552 15838049 := bstep (se 2 (by rfl) ⟨5939268, by rfl⟩ : syracuseStep 15838049 = 11878537) B11878537
theorem B4174163 : Blo 1464552 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B17838539 : Blo 1464552 17838539 := bstep (se 1 (by rfl) ⟨13378904, by rfl⟩ : syracuseStep 17838539 = 26757809) B26757809
theorem B1317893095 : Blo 1464552 1317893095 := bstep (se 1 (by rfl) ⟨988419821, by rfl⟩ : syracuseStep 1317893095 = 1976839643) B1976839643
theorem B4175975 : Blo 1464552 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B4176031 : Blo 1464552 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B1465115 : Blo 1464552 1465115 := bstep (se 1 (by rfl) ⟨1098836, by rfl⟩ : syracuseStep 1465115 = 2197673) B2197673
theorem B4947695 : Blo 1464552 4947695 := bstep (se 1 (by rfl) ⟨3710771, by rfl⟩ : syracuseStep 4947695 = 7421543) B7421543
theorem B4947965 : Blo 1464552 4947965 := bstep (se 3 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 4947965 = 1855487) B1855487
theorem B2197199 : Blo 1464552 2197199 := bstep (se 1 (by rfl) ⟨1647899, by rfl⟩ : syracuseStep 2197199 = 3295799) B3295799
theorem B12053231 : Blo 1464552 12053231 := bstep (se 1 (by rfl) ⟨9039923, by rfl⟩ : syracuseStep 12053231 = 18079847) B18079847
theorem B9515227 : Blo 1464552 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B42234797 : Blo 1464552 42234797 := bstep (se 3 (by rfl) ⟨7919024, by rfl⟩ : syracuseStep 42234797 = 15838049) B15838049
theorem B3298463 : Blo 1464552 3298463 := bstep (se 1 (by rfl) ⟨2473847, by rfl⟩ : syracuseStep 3298463 = 4947695) B4947695
theorem B3298643 : Blo 1464552 3298643 := bstep (se 1 (by rfl) ⟨2473982, by rfl⟩ : syracuseStep 3298643 = 4947965) B4947965
theorem B3298751 : Blo 1464552 3298751 := bstep (se 1 (by rfl) ⟨2474063, by rfl⟩ : syracuseStep 3298751 = 4948127) B4948127
theorem B5568041 : Blo 1464552 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B2782775 : Blo 1464552 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B11892359 : Blo 1464552 11892359 := bstep (se 1 (by rfl) ⟨8919269, by rfl⟩ : syracuseStep 11892359 = 17838539) B17838539
theorem B1464575 : Blo 1464552 1464575 := bstep (se 1 (by rfl) ⟨1098431, by rfl⟩ : syracuseStep 1464575 = 2196863) B2196863
theorem B939408005 : Blo 1464552 939408005 := bstep (se 4 (by rfl) ⟨88069500, by rfl⟩ : syracuseStep 939408005 = 176139001) B176139001
theorem B1757190793 : Blo 1464552 1757190793 := bstep (se 2 (by rfl) ⟨658946547, by rfl⟩ : syracuseStep 1757190793 = 1317893095) B1317893095
theorem B2783983 : Blo 1464552 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B14081957 : Blo 1464552 14081957 := bstep (se 4 (by rfl) ⟨1320183, by rfl⟩ : syracuseStep 14081957 = 2640367) B2640367
theorem B28156531 : Blo 1464552 28156531 := bstep (se 1 (by rfl) ⟨21117398, by rfl⟩ : syracuseStep 28156531 = 42234797) B42234797
theorem B2342921057 : Blo 1464552 2342921057 := bstep (se 2 (by rfl) ⟨878595396, by rfl⟩ : syracuseStep 2342921057 = 1757190793) B1757190793
theorem B3711977 : Blo 1464552 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B3712027 : Blo 1464552 3712027 := bstep (se 1 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 3712027 = 5568041) B5568041
theorem B31712957 : Blo 1464552 31712957 := bstep (se 3 (by rfl) ⟨5946179, by rfl⟩ : syracuseStep 31712957 = 11892359) B11892359
theorem B626272003 : Blo 1464552 626272003 := bstep (se 1 (by rfl) ⟨469704002, by rfl⟩ : syracuseStep 626272003 = 939408005) B939408005
theorem B2198975 : Blo 1464552 2198975 := bstep (se 1 (by rfl) ⟨1649231, by rfl⟩ : syracuseStep 2198975 = 3298463) B3298463
theorem B2199095 : Blo 1464552 2199095 := bstep (se 1 (by rfl) ⟨1649321, by rfl⟩ : syracuseStep 2199095 = 3298643) B3298643
theorem B2199167 : Blo 1464552 2199167 := bstep (se 1 (by rfl) ⟨1649375, by rfl⟩ : syracuseStep 2199167 = 3298751) B3298751
theorem B12686969 : Blo 1464552 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B1464799 : Blo 1464552 1464799 := bstep (se 1 (by rfl) ⟨1098599, by rfl⟩ : syracuseStep 1464799 = 2197199) B2197199
theorem B7420733 : Blo 1464552 7420733 := bstep (se 3 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 7420733 = 2782775) B2782775
theorem B8035487 : Blo 1464552 8035487 := bstep (se 1 (by rfl) ⟨6026615, by rfl⟩ : syracuseStep 8035487 = 12053231) B12053231
theorem B9387971 : Blo 1464552 9387971 := bstep (se 1 (by rfl) ⟨7040978, by rfl⟩ : syracuseStep 9387971 = 14081957) B14081957
theorem B2474651 : Blo 1464552 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B4949369 : Blo 1464552 4949369 := bstep (se 2 (by rfl) ⟨1856013, by rfl⟩ : syracuseStep 4949369 = 3712027) B3712027
theorem B835029337 : Blo 1464552 835029337 := bstep (se 2 (by rfl) ⟨313136001, by rfl⟩ : syracuseStep 835029337 = 626272003) B626272003
theorem B1561947371 : Blo 1464552 1561947371 := bstep (se 1 (by rfl) ⟨1171460528, by rfl⟩ : syracuseStep 1561947371 = 2342921057) B2342921057
theorem B8457979 : Blo 1464552 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B37542041 : Blo 1464552 37542041 := bstep (se 2 (by rfl) ⟨14078265, by rfl⟩ : syracuseStep 37542041 = 28156531) B28156531
theorem B21141971 : Blo 1464552 21141971 := bstep (se 1 (by rfl) ⟨15856478, by rfl⟩ : syracuseStep 21141971 = 31712957) B31712957
theorem B4947155 : Blo 1464552 4947155 := bstep (se 1 (by rfl) ⟨3710366, by rfl⟩ : syracuseStep 4947155 = 7420733) B7420733
theorem B5356991 : Blo 1464552 5356991 := bstep (se 1 (by rfl) ⟨4017743, by rfl⟩ : syracuseStep 5356991 = 8035487) B8035487
theorem B1465983 : Blo 1464552 1465983 := bstep (se 1 (by rfl) ⟨1099487, by rfl⟩ : syracuseStep 1465983 = 2198975) B2198975
theorem B1466063 : Blo 1464552 1466063 := bstep (se 1 (by rfl) ⟨1099547, by rfl⟩ : syracuseStep 1466063 = 2199095) B2199095
theorem B1466111 : Blo 1464552 1466111 := bstep (se 1 (by rfl) ⟨1099583, by rfl⟩ : syracuseStep 1466111 = 2199167) B2199167
theorem B6258647 : Blo 1464552 6258647 := bstep (se 1 (by rfl) ⟨4693985, by rfl⟩ : syracuseStep 6258647 = 9387971) B9387971
theorem B25028027 : Blo 1464552 25028027 := bstep (se 1 (by rfl) ⟨18771020, by rfl⟩ : syracuseStep 25028027 = 37542041) B37542041
theorem B16689725 : Blo 1464552 16689725 := bstep (se 3 (by rfl) ⟨3129323, by rfl⟩ : syracuseStep 16689725 = 6258647) B6258647
theorem B1649767 : Blo 1464552 1649767 := bstep (se 1 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 1649767 = 2474651) B2474651
theorem B14094647 : Blo 1464552 14094647 := bstep (se 1 (by rfl) ⟨10570985, by rfl⟩ : syracuseStep 14094647 = 21141971) B21141971
theorem B3298103 : Blo 1464552 3298103 := bstep (se 1 (by rfl) ⟨2473577, by rfl⟩ : syracuseStep 3298103 = 4947155) B4947155
theorem B1041298247 : Blo 1464552 1041298247 := bstep (se 1 (by rfl) ⟨780973685, by rfl⟩ : syracuseStep 1041298247 = 1561947371) B1561947371
theorem B11277305 : Blo 1464552 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B1113372449 : Blo 1464552 1113372449 := bstep (se 2 (by rfl) ⟨417514668, by rfl⟩ : syracuseStep 1113372449 = 835029337) B835029337
theorem B3299579 : Blo 1464552 3299579 := bstep (se 1 (by rfl) ⟨2474684, by rfl⟩ : syracuseStep 3299579 = 4949369) B4949369
theorem B3571327 : Blo 1464552 3571327 := bstep (se 1 (by rfl) ⟨2678495, by rfl⟩ : syracuseStep 3571327 = 5356991) B5356991
theorem B9396431 : Blo 1464552 9396431 := bstep (se 1 (by rfl) ⟨7047323, by rfl⟩ : syracuseStep 9396431 = 14094647) B14094647
theorem B694198831 : Blo 1464552 694198831 := bstep (se 1 (by rfl) ⟨520649123, by rfl⟩ : syracuseStep 694198831 = 1041298247) B1041298247
theorem B11126483 : Blo 1464552 11126483 := bstep (se 1 (by rfl) ⟨8344862, by rfl⟩ : syracuseStep 11126483 = 16689725) B16689725
theorem B4761769 : Blo 1464552 4761769 := bstep (se 2 (by rfl) ⟨1785663, by rfl⟩ : syracuseStep 4761769 = 3571327) B3571327
theorem B2198735 : Blo 1464552 2198735 := bstep (se 1 (by rfl) ⟨1649051, by rfl⟩ : syracuseStep 2198735 = 3298103) B3298103
theorem B742248299 : Blo 1464552 742248299 := bstep (se 1 (by rfl) ⟨556686224, by rfl⟩ : syracuseStep 742248299 = 1113372449) B1113372449
theorem B2199689 : Blo 1464552 2199689 := bstep (se 2 (by rfl) ⟨824883, by rfl⟩ : syracuseStep 2199689 = 1649767) B1649767
theorem B2199719 : Blo 1464552 2199719 := bstep (se 1 (by rfl) ⟨1649789, by rfl⟩ : syracuseStep 2199719 = 3299579) B3299579
theorem B7518203 : Blo 1464552 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B16685351 : Blo 1464552 16685351 := bstep (se 1 (by rfl) ⟨12514013, by rfl⟩ : syracuseStep 16685351 = 25028027) B25028027
theorem B1466459 : Blo 1464552 1466459 := bstep (se 1 (by rfl) ⟨1099844, by rfl⟩ : syracuseStep 1466459 = 2199689) B2199689
theorem B1466479 : Blo 1464552 1466479 := bstep (se 1 (by rfl) ⟨1099859, by rfl⟩ : syracuseStep 1466479 = 2199719) B2199719
theorem B6349025 : Blo 1464552 6349025 := bstep (se 2 (by rfl) ⟨2380884, by rfl⟩ : syracuseStep 6349025 = 4761769) B4761769
theorem B925598441 : Blo 1464552 925598441 := bstep (se 2 (by rfl) ⟨347099415, by rfl⟩ : syracuseStep 925598441 = 694198831) B694198831
theorem B494832199 : Blo 1464552 494832199 := bstep (se 1 (by rfl) ⟨371124149, by rfl⟩ : syracuseStep 494832199 = 742248299) B742248299
theorem B7417655 : Blo 1464552 7417655 := bstep (se 1 (by rfl) ⟨5563241, by rfl⟩ : syracuseStep 7417655 = 11126483) B11126483
theorem B6264287 : Blo 1464552 6264287 := bstep (se 1 (by rfl) ⟨4698215, by rfl⟩ : syracuseStep 6264287 = 9396431) B9396431
theorem B5012135 : Blo 1464552 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B11123567 : Blo 1464552 11123567 := bstep (se 1 (by rfl) ⟨8342675, by rfl⟩ : syracuseStep 11123567 = 16685351) B16685351
theorem B1465823 : Blo 1464552 1465823 := bstep (se 1 (by rfl) ⟨1099367, by rfl⟩ : syracuseStep 1465823 = 2198735) B2198735
theorem B659776265 : Blo 1464552 659776265 := bstep (se 2 (by rfl) ⟨247416099, by rfl⟩ : syracuseStep 659776265 = 494832199) B494832199
theorem B7415711 : Blo 1464552 7415711 := bstep (se 1 (by rfl) ⟨5561783, by rfl⟩ : syracuseStep 7415711 = 11123567) B11123567
theorem B617065627 : Blo 1464552 617065627 := bstep (se 1 (by rfl) ⟨462799220, by rfl⟩ : syracuseStep 617065627 = 925598441) B925598441
theorem B4945103 : Blo 1464552 4945103 := bstep (se 1 (by rfl) ⟨3708827, by rfl⟩ : syracuseStep 4945103 = 7417655) B7417655
theorem B4232683 : Blo 1464552 4232683 := bstep (se 1 (by rfl) ⟨3174512, by rfl⟩ : syracuseStep 4232683 = 6349025) B6349025
theorem B4176191 : Blo 1464552 4176191 := bstep (se 1 (by rfl) ⟨3132143, by rfl⟩ : syracuseStep 4176191 = 6264287) B6264287
theorem B3341423 : Blo 1464552 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B3296735 : Blo 1464552 3296735 := bstep (se 1 (by rfl) ⟨2472551, by rfl⟩ : syracuseStep 3296735 = 4945103) B4945103
theorem B4943807 : Blo 1464552 4943807 := bstep (se 1 (by rfl) ⟨3707855, by rfl⟩ : syracuseStep 4943807 = 7415711) B7415711
theorem B8910461 : Blo 1464552 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B439850843 : Blo 1464552 439850843 := bstep (se 1 (by rfl) ⟨329888132, by rfl⟩ : syracuseStep 439850843 = 659776265) B659776265
theorem B822754169 : Blo 1464552 822754169 := bstep (se 2 (by rfl) ⟨308532813, by rfl⟩ : syracuseStep 822754169 = 617065627) B617065627
theorem B2784127 : Blo 1464552 2784127 := bstep (se 1 (by rfl) ⟨2088095, by rfl⟩ : syracuseStep 2784127 = 4176191) B4176191
theorem B5643577 : Blo 1464552 5643577 := bstep (se 2 (by rfl) ⟨2116341, by rfl⟩ : syracuseStep 5643577 = 4232683) B4232683
theorem B5940307 : Blo 1464552 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B3712169 : Blo 1464552 3712169 := bstep (se 2 (by rfl) ⟨1392063, by rfl⟩ : syracuseStep 3712169 = 2784127) B2784127
theorem B293233895 : Blo 1464552 293233895 := bstep (se 1 (by rfl) ⟨219925421, by rfl⟩ : syracuseStep 293233895 = 439850843) B439850843
theorem B2197823 : Blo 1464552 2197823 := bstep (se 1 (by rfl) ⟨1648367, by rfl⟩ : syracuseStep 2197823 = 3296735) B3296735
theorem B3295871 : Blo 1464552 3295871 := bstep (se 1 (by rfl) ⟨2471903, by rfl⟩ : syracuseStep 3295871 = 4943807) B4943807
theorem B7524769 : Blo 1464552 7524769 := bstep (se 2 (by rfl) ⟨2821788, by rfl⟩ : syracuseStep 7524769 = 5643577) B5643577
theorem B548502779 : Blo 1464552 548502779 := bstep (se 1 (by rfl) ⟨411377084, by rfl⟩ : syracuseStep 548502779 = 822754169) B822754169
theorem B2474779 : Blo 1464552 2474779 := bstep (se 1 (by rfl) ⟨1856084, by rfl⟩ : syracuseStep 2474779 = 3712169) B3712169
theorem B2197247 : Blo 1464552 2197247 := bstep (se 1 (by rfl) ⟨1647935, by rfl⟩ : syracuseStep 2197247 = 3295871) B3295871
theorem B365668519 : Blo 1464552 365668519 := bstep (se 1 (by rfl) ⟨274251389, by rfl⟩ : syracuseStep 365668519 = 548502779) B548502779
theorem B195489263 : Blo 1464552 195489263 := bstep (se 1 (by rfl) ⟨146616947, by rfl⟩ : syracuseStep 195489263 = 293233895) B293233895
theorem B10033025 : Blo 1464552 10033025 := bstep (se 2 (by rfl) ⟨3762384, by rfl⟩ : syracuseStep 10033025 = 7524769) B7524769
theorem B7920409 : Blo 1464552 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B1465215 : Blo 1464552 1465215 := bstep (se 1 (by rfl) ⟨1098911, by rfl⟩ : syracuseStep 1465215 = 2197823) B2197823
theorem B10560545 : Blo 1464552 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B487558025 : Blo 1464552 487558025 := bstep (se 2 (by rfl) ⟨182834259, by rfl⟩ : syracuseStep 487558025 = 365668519) B365668519
theorem B3299705 : Blo 1464552 3299705 := bstep (se 2 (by rfl) ⟨1237389, by rfl⟩ : syracuseStep 3299705 = 2474779) B2474779
theorem B1464831 : Blo 1464552 1464831 := bstep (se 1 (by rfl) ⟨1098623, by rfl⟩ : syracuseStep 1464831 = 2197247) B2197247
theorem B130326175 : Blo 1464552 130326175 := bstep (se 1 (by rfl) ⟨97744631, by rfl⟩ : syracuseStep 130326175 = 195489263) B195489263
theorem B26754733 : Blo 1464552 26754733 := bstep (se 3 (by rfl) ⟨5016512, by rfl⟩ : syracuseStep 26754733 = 10033025) B10033025
theorem B7040363 : Blo 1464552 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B2199803 : Blo 1464552 2199803 := bstep (se 1 (by rfl) ⟨1649852, by rfl⟩ : syracuseStep 2199803 = 3299705) B3299705
theorem B325038683 : Blo 1464552 325038683 := bstep (se 1 (by rfl) ⟨243779012, by rfl⟩ : syracuseStep 325038683 = 487558025) B487558025
theorem B35672977 : Blo 1464552 35672977 := bstep (se 2 (by rfl) ⟨13377366, by rfl⟩ : syracuseStep 35672977 = 26754733) B26754733
theorem B695072933 : Blo 1464552 695072933 := bstep (se 4 (by rfl) ⟨65163087, by rfl⟩ : syracuseStep 695072933 = 130326175) B130326175
theorem B1466535 : Blo 1464552 1466535 := bstep (se 1 (by rfl) ⟨1099901, by rfl⟩ : syracuseStep 1466535 = 2199803) B2199803
theorem B463381955 : Blo 1464552 463381955 := bstep (se 1 (by rfl) ⟨347536466, by rfl⟩ : syracuseStep 463381955 = 695072933) B695072933
theorem B190255877 : Blo 1464552 190255877 := bstep (se 4 (by rfl) ⟨17836488, by rfl⟩ : syracuseStep 190255877 = 35672977) B35672977
theorem B216692455 : Blo 1464552 216692455 := bstep (se 1 (by rfl) ⟨162519341, by rfl⟩ : syracuseStep 216692455 = 325038683) B325038683
theorem B18774301 : Blo 1464552 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B126837251 : Blo 1464552 126837251 := bstep (se 1 (by rfl) ⟨95127938, by rfl⟩ : syracuseStep 126837251 = 190255877) B190255877
theorem B308921303 : Blo 1464552 308921303 := bstep (se 1 (by rfl) ⟨231690977, by rfl⟩ : syracuseStep 308921303 = 463381955) B463381955
theorem B25032401 : Blo 1464552 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B288923273 : Blo 1464552 288923273 := bstep (se 2 (by rfl) ⟨108346227, by rfl⟩ : syracuseStep 288923273 = 216692455) B216692455
theorem B84558167 : Blo 1464552 84558167 := bstep (se 1 (by rfl) ⟨63418625, by rfl⟩ : syracuseStep 84558167 = 126837251) B126837251
theorem B205947535 : Blo 1464552 205947535 := bstep (se 1 (by rfl) ⟨154460651, by rfl⟩ : syracuseStep 205947535 = 308921303) B308921303
theorem B16688267 : Blo 1464552 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B192615515 : Blo 1464552 192615515 := bstep (se 1 (by rfl) ⟨144461636, by rfl⟩ : syracuseStep 192615515 = 288923273) B288923273
theorem B128410343 : Blo 1464552 128410343 := bstep (se 1 (by rfl) ⟨96307757, by rfl⟩ : syracuseStep 128410343 = 192615515) B192615515
theorem B11125511 : Blo 1464552 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B274596713 : Blo 1464552 274596713 := bstep (se 2 (by rfl) ⟨102973767, by rfl⟩ : syracuseStep 274596713 = 205947535) B205947535
theorem B56372111 : Blo 1464552 56372111 := bstep (se 1 (by rfl) ⟨42279083, by rfl⟩ : syracuseStep 56372111 = 84558167) B84558167
theorem B85606895 : Blo 1464552 85606895 := bstep (se 1 (by rfl) ⟨64205171, by rfl⟩ : syracuseStep 85606895 = 128410343) B128410343
theorem B7417007 : Blo 1464552 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B37581407 : Blo 1464552 37581407 := bstep (se 1 (by rfl) ⟨28186055, by rfl⟩ : syracuseStep 37581407 = 56372111) B56372111
theorem B183064475 : Blo 1464552 183064475 := bstep (se 1 (by rfl) ⟨137298356, by rfl⟩ : syracuseStep 183064475 = 274596713) B274596713
theorem B25054271 : Blo 1464552 25054271 := bstep (se 1 (by rfl) ⟨18790703, by rfl⟩ : syracuseStep 25054271 = 37581407) B37581407
theorem B4944671 : Blo 1464552 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B122042983 : Blo 1464552 122042983 := bstep (se 1 (by rfl) ⟨91532237, by rfl⟩ : syracuseStep 122042983 = 183064475) B183064475
theorem B228285053 : Blo 1464552 228285053 := bstep (se 3 (by rfl) ⟨42803447, by rfl⟩ : syracuseStep 228285053 = 85606895) B85606895
theorem B3296447 : Blo 1464552 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B162723977 : Blo 1464552 162723977 := bstep (se 2 (by rfl) ⟨61021491, by rfl⟩ : syracuseStep 162723977 = 122042983) B122042983
theorem B152190035 : Blo 1464552 152190035 := bstep (se 1 (by rfl) ⟨114142526, by rfl⟩ : syracuseStep 152190035 = 228285053) B228285053
theorem B16702847 : Blo 1464552 16702847 := bstep (se 1 (by rfl) ⟨12527135, by rfl⟩ : syracuseStep 16702847 = 25054271) B25054271
theorem B101460023 : Blo 1464552 101460023 := bstep (se 1 (by rfl) ⟨76095017, by rfl⟩ : syracuseStep 101460023 = 152190035) B152190035
theorem B2197631 : Blo 1464552 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B11135231 : Blo 1464552 11135231 := bstep (se 1 (by rfl) ⟨8351423, by rfl⟩ : syracuseStep 11135231 = 16702847) B16702847
theorem B108482651 : Blo 1464552 108482651 := bstep (se 1 (by rfl) ⟨81361988, by rfl⟩ : syracuseStep 108482651 = 162723977) B162723977
theorem B7423487 : Blo 1464552 7423487 := bstep (se 1 (by rfl) ⟨5567615, by rfl⟩ : syracuseStep 7423487 = 11135231) B11135231
theorem B72321767 : Blo 1464552 72321767 := bstep (se 1 (by rfl) ⟨54241325, by rfl⟩ : syracuseStep 72321767 = 108482651) B108482651
theorem B67640015 : Blo 1464552 67640015 := bstep (se 1 (by rfl) ⟨50730011, by rfl⟩ : syracuseStep 67640015 = 101460023) B101460023
theorem B1465087 : Blo 1464552 1465087 := bstep (se 1 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 1465087 = 2197631) B2197631
theorem B4948991 : Blo 1464552 4948991 := bstep (se 1 (by rfl) ⟨3711743, by rfl⟩ : syracuseStep 4948991 = 7423487) B7423487
theorem B45093343 : Blo 1464552 45093343 := bstep (se 1 (by rfl) ⟨33820007, by rfl⟩ : syracuseStep 45093343 = 67640015) B67640015
theorem B48214511 : Blo 1464552 48214511 := bstep (se 1 (by rfl) ⟨36160883, by rfl⟩ : syracuseStep 48214511 = 72321767) B72321767
theorem B60124457 : Blo 1464552 60124457 := bstep (se 2 (by rfl) ⟨22546671, by rfl⟩ : syracuseStep 60124457 = 45093343) B45093343
theorem B32143007 : Blo 1464552 32143007 := bstep (se 1 (by rfl) ⟨24107255, by rfl⟩ : syracuseStep 32143007 = 48214511) B48214511
theorem B3299327 : Blo 1464552 3299327 := bstep (se 1 (by rfl) ⟨2474495, by rfl⟩ : syracuseStep 3299327 = 4948991) B4948991
theorem B2199551 : Blo 1464552 2199551 := bstep (se 1 (by rfl) ⟨1649663, by rfl⟩ : syracuseStep 2199551 = 3299327) B3299327
theorem B21428671 : Blo 1464552 21428671 := bstep (se 1 (by rfl) ⟨16071503, by rfl⟩ : syracuseStep 21428671 = 32143007) B32143007
theorem B40082971 : Blo 1464552 40082971 := bstep (se 1 (by rfl) ⟨30062228, by rfl⟩ : syracuseStep 40082971 = 60124457) B60124457
theorem B28571561 : Blo 1464552 28571561 := bstep (se 2 (by rfl) ⟨10714335, by rfl⟩ : syracuseStep 28571561 = 21428671) B21428671
theorem B53443961 : Blo 1464552 53443961 := bstep (se 2 (by rfl) ⟨20041485, by rfl⟩ : syracuseStep 53443961 = 40082971) B40082971
theorem B1466367 : Blo 1464552 1466367 := bstep (se 1 (by rfl) ⟨1099775, by rfl⟩ : syracuseStep 1466367 = 2199551) B2199551
theorem B19047707 : Blo 1464552 19047707 := bstep (se 1 (by rfl) ⟨14285780, by rfl⟩ : syracuseStep 19047707 = 28571561) B28571561
theorem B35629307 : Blo 1464552 35629307 := bstep (se 1 (by rfl) ⟨26721980, by rfl⟩ : syracuseStep 35629307 = 53443961) B53443961
theorem B12698471 : Blo 1464552 12698471 := bstep (se 1 (by rfl) ⟨9523853, by rfl⟩ : syracuseStep 12698471 = 19047707) B19047707
theorem B23752871 : Blo 1464552 23752871 := bstep (se 1 (by rfl) ⟨17814653, by rfl⟩ : syracuseStep 23752871 = 35629307) B35629307
theorem B15835247 : Blo 1464552 15835247 := bstep (se 1 (by rfl) ⟨11876435, by rfl⟩ : syracuseStep 15835247 = 23752871) B23752871
theorem B8465647 : Blo 1464552 8465647 := bstep (se 1 (by rfl) ⟨6349235, by rfl⟩ : syracuseStep 8465647 = 12698471) B12698471
theorem B10556831 : Blo 1464552 10556831 := bstep (se 1 (by rfl) ⟨7917623, by rfl⟩ : syracuseStep 10556831 = 15835247) B15835247
theorem B11287529 : Blo 1464552 11287529 := bstep (se 2 (by rfl) ⟨4232823, by rfl⟩ : syracuseStep 11287529 = 8465647) B8465647
theorem B7037887 : Blo 1464552 7037887 := bstep (se 1 (by rfl) ⟨5278415, by rfl⟩ : syracuseStep 7037887 = 10556831) B10556831
theorem B7525019 : Blo 1464552 7525019 := bstep (se 1 (by rfl) ⟨5643764, by rfl⟩ : syracuseStep 7525019 = 11287529) B11287529
theorem B9383849 : Blo 1464552 9383849 := bstep (se 2 (by rfl) ⟨3518943, by rfl⟩ : syracuseStep 9383849 = 7037887) B7037887
theorem B20066717 : Blo 1464552 20066717 := bstep (se 3 (by rfl) ⟨3762509, by rfl⟩ : syracuseStep 20066717 = 7525019) B7525019
theorem B13377811 : Blo 1464552 13377811 := bstep (se 1 (by rfl) ⟨10033358, by rfl⟩ : syracuseStep 13377811 = 20066717) B20066717
theorem B6255899 : Blo 1464552 6255899 := bstep (se 1 (by rfl) ⟨4691924, by rfl⟩ : syracuseStep 6255899 = 9383849) B9383849
theorem B4170599 : Blo 1464552 4170599 := bstep (se 1 (by rfl) ⟨3127949, by rfl⟩ : syracuseStep 4170599 = 6255899) B6255899
theorem B17837081 : Blo 1464552 17837081 := bstep (se 2 (by rfl) ⟨6688905, by rfl⟩ : syracuseStep 17837081 = 13377811) B13377811
theorem B2780399 : Blo 1464552 2780399 := bstep (se 1 (by rfl) ⟨2085299, by rfl⟩ : syracuseStep 2780399 = 4170599) B4170599
theorem B11891387 : Blo 1464552 11891387 := bstep (se 1 (by rfl) ⟨8918540, by rfl⟩ : syracuseStep 11891387 = 17837081) B17837081
theorem B1853599 : Blo 1464552 1853599 := bstep (se 1 (by rfl) ⟨1390199, by rfl⟩ : syracuseStep 1853599 = 2780399) B2780399
theorem B7927591 : Blo 1464552 7927591 := bstep (se 1 (by rfl) ⟨5945693, by rfl⟩ : syracuseStep 7927591 = 11891387) B11891387
theorem B10570121 : Blo 1464552 10570121 := bstep (se 2 (by rfl) ⟨3963795, by rfl⟩ : syracuseStep 10570121 = 7927591) B7927591
theorem B2471465 : Blo 1464552 2471465 := bstep (se 2 (by rfl) ⟨926799, by rfl⟩ : syracuseStep 2471465 = 1853599) B1853599
theorem B1647643 : Blo 1464552 1647643 := bstep (se 1 (by rfl) ⟨1235732, by rfl⟩ : syracuseStep 1647643 = 2471465) B2471465
theorem B7046747 : Blo 1464552 7046747 := bstep (se 1 (by rfl) ⟨5285060, by rfl⟩ : syracuseStep 7046747 = 10570121) B10570121
theorem B2196857 : Blo 1464552 2196857 := bstep (se 2 (by rfl) ⟨823821, by rfl⟩ : syracuseStep 2196857 = 1647643) B1647643
theorem B4697831 : Blo 1464552 4697831 := bstep (se 1 (by rfl) ⟨3523373, by rfl⟩ : syracuseStep 4697831 = 7046747) B7046747
theorem B3131887 : Blo 1464552 3131887 := bstep (se 1 (by rfl) ⟨2348915, by rfl⟩ : syracuseStep 3131887 = 4697831) B4697831
theorem B1464571 : Blo 1464552 1464571 := bstep (se 1 (by rfl) ⟨1098428, by rfl⟩ : syracuseStep 1464571 = 2196857) B2196857
theorem B4175849 : Blo 1464552 4175849 := bstep (se 2 (by rfl) ⟨1565943, by rfl⟩ : syracuseStep 4175849 = 3131887) B3131887
theorem B2783899 : Blo 1464552 2783899 := bstep (se 1 (by rfl) ⟨2087924, by rfl⟩ : syracuseStep 2783899 = 4175849) B4175849
theorem B3711865 : Blo 1464552 3711865 := bstep (se 2 (by rfl) ⟨1391949, by rfl⟩ : syracuseStep 3711865 = 2783899) B2783899
theorem B4949153 : Blo 1464552 4949153 := bstep (se 2 (by rfl) ⟨1855932, by rfl⟩ : syracuseStep 4949153 = 3711865) B3711865
theorem B3299435 : Blo 1464552 3299435 := bstep (se 1 (by rfl) ⟨2474576, by rfl⟩ : syracuseStep 3299435 = 4949153) B4949153
theorem B2199623 : Blo 1464552 2199623 := bstep (se 1 (by rfl) ⟨1649717, by rfl⟩ : syracuseStep 2199623 = 3299435) B3299435
theorem B1466415 : Blo 1464552 1466415 := bstep (se 1 (by rfl) ⟨1099811, by rfl⟩ : syracuseStep 1466415 = 2199623) B2199623

theorem C0 (j : ℕ) (h1 : 366138 ≤ j) (h2 : j ≤ 366637) : Blo 1464552 (4 * j + 3) := by
  interval_cases j
  · exact B1464555
  · exact B1464559
  · exact B1464563
  · exact B1464567
  · exact B1464571
  · exact B1464575
  · exact B1464579
  · exact B1464583
  · exact B1464587
  · exact B1464591
  · exact B1464595
  · exact B1464599
  · exact B1464603
  · exact B1464607
  · exact B1464611
  · exact B1464615
  · exact B1464619
  · exact B1464623
  · exact B1464627
  · exact B1464631
  · exact B1464635
  · exact B1464639
  · exact B1464643
  · exact B1464647
  · exact B1464651
  · exact B1464655
  · exact B1464659
  · exact B1464663
  · exact B1464667
  · exact B1464671
  · exact B1464675
  · exact B1464679
  · exact B1464683
  · exact B1464687
  · exact B1464691
  · exact B1464695
  · exact B1464699
  · exact B1464703
  · exact B1464707
  · exact B1464711
  · exact B1464715
  · exact B1464719
  · exact B1464723
  · exact B1464727
  · exact B1464731
  · exact B1464735
  · exact B1464739
  · exact B1464743
  · exact B1464747
  · exact B1464751
  · exact B1464755
  · exact B1464759
  · exact B1464763
  · exact B1464767
  · exact B1464771
  · exact B1464775
  · exact B1464779
  · exact B1464783
  · exact B1464787
  · exact B1464791
  · exact B1464795
  · exact B1464799
  · exact B1464803
  · exact B1464807
  · exact B1464811
  · exact B1464815
  · exact B1464819
  · exact B1464823
  · exact B1464827
  · exact B1464831
  · exact B1464835
  · exact B1464839
  · exact B1464843
  · exact B1464847
  · exact B1464851
  · exact B1464855
  · exact B1464859
  · exact B1464863
  · exact B1464867
  · exact B1464871
  · exact B1464875
  · exact B1464879
  · exact B1464883
  · exact B1464887
  · exact B1464891
  · exact B1464895
  · exact B1464899
  · exact B1464903
  · exact B1464907
  · exact B1464911
  · exact B1464915
  · exact B1464919
  · exact B1464923
  · exact B1464927
  · exact B1464931
  · exact B1464935
  · exact B1464939
  · exact B1464943
  · exact B1464947
  · exact B1464951
  · exact B1464955
  · exact B1464959
  · exact B1464963
  · exact B1464967
  · exact B1464971
  · exact B1464975
  · exact B1464979
  · exact B1464983
  · exact B1464987
  · exact B1464991
  · exact B1464995
  · exact B1464999
  · exact B1465003
  · exact B1465007
  · exact B1465011
  · exact B1465015
  · exact B1465019
  · exact B1465023
  · exact B1465027
  · exact B1465031
  · exact B1465035
  · exact B1465039
  · exact B1465043
  · exact B1465047
  · exact B1465051
  · exact B1465055
  · exact B1465059
  · exact B1465063
  · exact B1465067
  · exact B1465071
  · exact B1465075
  · exact B1465079
  · exact B1465083
  · exact B1465087
  · exact B1465091
  · exact B1465095
  · exact B1465099
  · exact B1465103
  · exact B1465107
  · exact B1465111
  · exact B1465115
  · exact B1465119
  · exact B1465123
  · exact B1465127
  · exact B1465131
  · exact B1465135
  · exact B1465139
  · exact B1465143
  · exact B1465147
  · exact B1465151
  · exact B1465155
  · exact B1465159
  · exact B1465163
  · exact B1465167
  · exact B1465171
  · exact B1465175
  · exact B1465179
  · exact B1465183
  · exact B1465187
  · exact B1465191
  · exact B1465195
  · exact B1465199
  · exact B1465203
  · exact B1465207
  · exact B1465211
  · exact B1465215
  · exact B1465219
  · exact B1465223
  · exact B1465227
  · exact B1465231
  · exact B1465235
  · exact B1465239
  · exact B1465243
  · exact B1465247
  · exact B1465251
  · exact B1465255
  · exact B1465259
  · exact B1465263
  · exact B1465267
  · exact B1465271
  · exact B1465275
  · exact B1465279
  · exact B1465283
  · exact B1465287
  · exact B1465291
  · exact B1465295
  · exact B1465299
  · exact B1465303
  · exact B1465307
  · exact B1465311
  · exact B1465315
  · exact B1465319
  · exact B1465323
  · exact B1465327
  · exact B1465331
  · exact B1465335
  · exact B1465339
  · exact B1465343
  · exact B1465347
  · exact B1465351
  · exact B1465355
  · exact B1465359
  · exact B1465363
  · exact B1465367
  · exact B1465371
  · exact B1465375
  · exact B1465379
  · exact B1465383
  · exact B1465387
  · exact B1465391
  · exact B1465395
  · exact B1465399
  · exact B1465403
  · exact B1465407
  · exact B1465411
  · exact B1465415
  · exact B1465419
  · exact B1465423
  · exact B1465427
  · exact B1465431
  · exact B1465435
  · exact B1465439
  · exact B1465443
  · exact B1465447
  · exact B1465451
  · exact B1465455
  · exact B1465459
  · exact B1465463
  · exact B1465467
  · exact B1465471
  · exact B1465475
  · exact B1465479
  · exact B1465483
  · exact B1465487
  · exact B1465491
  · exact B1465495
  · exact B1465499
  · exact B1465503
  · exact B1465507
  · exact B1465511
  · exact B1465515
  · exact B1465519
  · exact B1465523
  · exact B1465527
  · exact B1465531
  · exact B1465535
  · exact B1465539
  · exact B1465543
  · exact B1465547
  · exact B1465551
  · exact B1465555
  · exact B1465559
  · exact B1465563
  · exact B1465567
  · exact B1465571
  · exact B1465575
  · exact B1465579
  · exact B1465583
  · exact B1465587
  · exact B1465591
  · exact B1465595
  · exact B1465599
  · exact B1465603
  · exact B1465607
  · exact B1465611
  · exact B1465615
  · exact B1465619
  · exact B1465623
  · exact B1465627
  · exact B1465631
  · exact B1465635
  · exact B1465639
  · exact B1465643
  · exact B1465647
  · exact B1465651
  · exact B1465655
  · exact B1465659
  · exact B1465663
  · exact B1465667
  · exact B1465671
  · exact B1465675
  · exact B1465679
  · exact B1465683
  · exact B1465687
  · exact B1465691
  · exact B1465695
  · exact B1465699
  · exact B1465703
  · exact B1465707
  · exact B1465711
  · exact B1465715
  · exact B1465719
  · exact B1465723
  · exact B1465727
  · exact B1465731
  · exact B1465735
  · exact B1465739
  · exact B1465743
  · exact B1465747
  · exact B1465751
  · exact B1465755
  · exact B1465759
  · exact B1465763
  · exact B1465767
  · exact B1465771
  · exact B1465775
  · exact B1465779
  · exact B1465783
  · exact B1465787
  · exact B1465791
  · exact B1465795
  · exact B1465799
  · exact B1465803
  · exact B1465807
  · exact B1465811
  · exact B1465815
  · exact B1465819
  · exact B1465823
  · exact B1465827
  · exact B1465831
  · exact B1465835
  · exact B1465839
  · exact B1465843
  · exact B1465847
  · exact B1465851
  · exact B1465855
  · exact B1465859
  · exact B1465863
  · exact B1465867
  · exact B1465871
  · exact B1465875
  · exact B1465879
  · exact B1465883
  · exact B1465887
  · exact B1465891
  · exact B1465895
  · exact B1465899
  · exact B1465903
  · exact B1465907
  · exact B1465911
  · exact B1465915
  · exact B1465919
  · exact B1465923
  · exact B1465927
  · exact B1465931
  · exact B1465935
  · exact B1465939
  · exact B1465943
  · exact B1465947
  · exact B1465951
  · exact B1465955
  · exact B1465959
  · exact B1465963
  · exact B1465967
  · exact B1465971
  · exact B1465975
  · exact B1465979
  · exact B1465983
  · exact B1465987
  · exact B1465991
  · exact B1465995
  · exact B1465999
  · exact B1466003
  · exact B1466007
  · exact B1466011
  · exact B1466015
  · exact B1466019
  · exact B1466023
  · exact B1466027
  · exact B1466031
  · exact B1466035
  · exact B1466039
  · exact B1466043
  · exact B1466047
  · exact B1466051
  · exact B1466055
  · exact B1466059
  · exact B1466063
  · exact B1466067
  · exact B1466071
  · exact B1466075
  · exact B1466079
  · exact B1466083
  · exact B1466087
  · exact B1466091
  · exact B1466095
  · exact B1466099
  · exact B1466103
  · exact B1466107
  · exact B1466111
  · exact B1466115
  · exact B1466119
  · exact B1466123
  · exact B1466127
  · exact B1466131
  · exact B1466135
  · exact B1466139
  · exact B1466143
  · exact B1466147
  · exact B1466151
  · exact B1466155
  · exact B1466159
  · exact B1466163
  · exact B1466167
  · exact B1466171
  · exact B1466175
  · exact B1466179
  · exact B1466183
  · exact B1466187
  · exact B1466191
  · exact B1466195
  · exact B1466199
  · exact B1466203
  · exact B1466207
  · exact B1466211
  · exact B1466215
  · exact B1466219
  · exact B1466223
  · exact B1466227
  · exact B1466231
  · exact B1466235
  · exact B1466239
  · exact B1466243
  · exact B1466247
  · exact B1466251
  · exact B1466255
  · exact B1466259
  · exact B1466263
  · exact B1466267
  · exact B1466271
  · exact B1466275
  · exact B1466279
  · exact B1466283
  · exact B1466287
  · exact B1466291
  · exact B1466295
  · exact B1466299
  · exact B1466303
  · exact B1466307
  · exact B1466311
  · exact B1466315
  · exact B1466319
  · exact B1466323
  · exact B1466327
  · exact B1466331
  · exact B1466335
  · exact B1466339
  · exact B1466343
  · exact B1466347
  · exact B1466351
  · exact B1466355
  · exact B1466359
  · exact B1466363
  · exact B1466367
  · exact B1466371
  · exact B1466375
  · exact B1466379
  · exact B1466383
  · exact B1466387
  · exact B1466391
  · exact B1466395
  · exact B1466399
  · exact B1466403
  · exact B1466407
  · exact B1466411
  · exact B1466415
  · exact B1466419
  · exact B1466423
  · exact B1466427
  · exact B1466431
  · exact B1466435
  · exact B1466439
  · exact B1466443
  · exact B1466447
  · exact B1466451
  · exact B1466455
  · exact B1466459
  · exact B1466463
  · exact B1466467
  · exact B1466471
  · exact B1466475
  · exact B1466479
  · exact B1466483
  · exact B1466487
  · exact B1466491
  · exact B1466495
  · exact B1466499
  · exact B1466503
  · exact B1466507
  · exact B1466511
  · exact B1466515
  · exact B1466519
  · exact B1466523
  · exact B1466527
  · exact B1466531
  · exact B1466535
  · exact B1466539
  · exact B1466543
  · exact B1466547
  · exact B1466551

theorem solution (m : ℕ) (hlo : 1464552 ≤ m) (hhi : m ≤ 1466552) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 366138 ≤ j := by omega
    have hj2 : j ≤ 366637 := by omega
    have hb : Blo 1464552 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
