-- Prove2me | solution 1 for syracuse_descends_range_546805_550805
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:34.142001+00:00
-- url     : https://prove2.me/submissions/3fb2fb81-c50d-410d-8fa6-ba9981be5814

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


theorem B1802549 : Blo 546805 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B2785589 : Blo 546805 2785589 := bbase (se 5 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 2785589 = 261149) (by norm_num)
theorem B10584533 : Blo 546805 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B1409501 : Blo 546805 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1114717 : Blo 546805 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B721829 : Blo 546805 721829 := bbase (se 4 (by rfl) ⟨67671, by rfl⟩ : syracuseStep 721829 = 135343) (by norm_num)
theorem B623561 : Blo 546805 623561 := bbase (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) (by norm_num)
theorem B820229 : Blo 546805 820229 := bbase (se 4 (by rfl) ⟨76896, by rfl⟩ : syracuseStep 820229 = 153793) (by norm_num)
theorem B820253 : Blo 546805 820253 := bbase (se 3 (by rfl) ⟨153797, by rfl⟩ : syracuseStep 820253 = 307595) (by norm_num)
theorem B558121 : Blo 546805 558121 := bbase (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) (by norm_num)
theorem B820277 : Blo 546805 820277 := bbase (se 5 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 820277 = 76901) (by norm_num)
theorem B820301 : Blo 546805 820301 := bbase (se 3 (by rfl) ⟨153806, by rfl⟩ : syracuseStep 820301 = 307613) (by norm_num)
theorem B820325 : Blo 546805 820325 := bbase (se 4 (by rfl) ⟨76905, by rfl⟩ : syracuseStep 820325 = 153811) (by norm_num)
theorem B820349 : Blo 546805 820349 := bbase (se 3 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 820349 = 307631) (by norm_num)
theorem B820373 : Blo 546805 820373 := bbase (se 6 (by rfl) ⟨19227, by rfl⟩ : syracuseStep 820373 = 38455) (by norm_num)
theorem B820397 : Blo 546805 820397 := bbase (se 3 (by rfl) ⟨153824, by rfl⟩ : syracuseStep 820397 = 307649) (by norm_num)
theorem B820421 : Blo 546805 820421 := bbase (se 4 (by rfl) ⟨76914, by rfl⟩ : syracuseStep 820421 = 153829) (by norm_num)
theorem B820445 : Blo 546805 820445 := bbase (se 3 (by rfl) ⟨153833, by rfl⟩ : syracuseStep 820445 = 307667) (by norm_num)
theorem B820469 : Blo 546805 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B820493 : Blo 546805 820493 := bbase (se 3 (by rfl) ⟨153842, by rfl⟩ : syracuseStep 820493 = 307685) (by norm_num)
theorem B820517 : Blo 546805 820517 := bbase (se 4 (by rfl) ⟨76923, by rfl⟩ : syracuseStep 820517 = 153847) (by norm_num)
theorem B820541 : Blo 546805 820541 := bbase (se 3 (by rfl) ⟨153851, by rfl⟩ : syracuseStep 820541 = 307703) (by norm_num)
theorem B820565 : Blo 546805 820565 := bbase (se 12 (by rfl) ⟨300, by rfl⟩ : syracuseStep 820565 = 601) (by norm_num)
theorem B820589 : Blo 546805 820589 := bbase (se 3 (by rfl) ⟨153860, by rfl⟩ : syracuseStep 820589 = 307721) (by norm_num)
theorem B820613 : Blo 546805 820613 := bbase (se 4 (by rfl) ⟨76932, by rfl⟩ : syracuseStep 820613 = 153865) (by norm_num)
theorem B820637 : Blo 546805 820637 := bbase (se 3 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 820637 = 307739) (by norm_num)
theorem B820661 : Blo 546805 820661 := bbase (se 5 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 820661 = 76937) (by norm_num)
theorem B820685 : Blo 546805 820685 := bbase (se 3 (by rfl) ⟨153878, by rfl⟩ : syracuseStep 820685 = 307757) (by norm_num)
theorem B820709 : Blo 546805 820709 := bbase (se 4 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 820709 = 153883) (by norm_num)
theorem B624109 : Blo 546805 624109 := bbase (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) (by norm_num)
theorem B820733 : Blo 546805 820733 := bbase (se 3 (by rfl) ⟨153887, by rfl⟩ : syracuseStep 820733 = 307775) (by norm_num)
theorem B820757 : Blo 546805 820757 := bbase (se 6 (by rfl) ⟨19236, by rfl⟩ : syracuseStep 820757 = 38473) (by norm_num)
theorem B820781 : Blo 546805 820781 := bbase (se 3 (by rfl) ⟨153896, by rfl⟩ : syracuseStep 820781 = 307793) (by norm_num)
theorem B820805 : Blo 546805 820805 := bbase (se 4 (by rfl) ⟨76950, by rfl⟩ : syracuseStep 820805 = 153901) (by norm_num)
theorem B2786885 : Blo 546805 2786885 := bbase (se 4 (by rfl) ⟨261270, by rfl⟩ : syracuseStep 2786885 = 522541) (by norm_num)
theorem B820829 : Blo 546805 820829 := bbase (se 3 (by rfl) ⟨153905, by rfl⟩ : syracuseStep 820829 = 307811) (by norm_num)
theorem B820853 : Blo 546805 820853 := bbase (se 5 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 820853 = 76955) (by norm_num)
theorem B820877 : Blo 546805 820877 := bbase (se 3 (by rfl) ⟨153914, by rfl⟩ : syracuseStep 820877 = 307829) (by norm_num)
theorem B820901 : Blo 546805 820901 := bbase (se 4 (by rfl) ⟨76959, by rfl⟩ : syracuseStep 820901 = 153919) (by norm_num)
theorem B820925 : Blo 546805 820925 := bbase (se 3 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 820925 = 307847) (by norm_num)
theorem B820949 : Blo 546805 820949 := bbase (se 7 (by rfl) ⟨9620, by rfl⟩ : syracuseStep 820949 = 19241) (by norm_num)
theorem B820973 : Blo 546805 820973 := bbase (se 3 (by rfl) ⟨153932, by rfl⟩ : syracuseStep 820973 = 307865) (by norm_num)
theorem B820997 : Blo 546805 820997 := bbase (se 4 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 820997 = 153937) (by norm_num)
theorem B821021 : Blo 546805 821021 := bbase (se 3 (by rfl) ⟨153941, by rfl⟩ : syracuseStep 821021 = 307883) (by norm_num)
theorem B821045 : Blo 546805 821045 := bbase (se 5 (by rfl) ⟨38486, by rfl⟩ : syracuseStep 821045 = 76973) (by norm_num)
theorem B821069 : Blo 546805 821069 := bbase (se 3 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 821069 = 307901) (by norm_num)
theorem B821093 : Blo 546805 821093 := bbase (se 4 (by rfl) ⟨76977, by rfl⟩ : syracuseStep 821093 = 153955) (by norm_num)
theorem B3508085 : Blo 546805 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B821117 : Blo 546805 821117 := bbase (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) (by norm_num)
theorem B821141 : Blo 546805 821141 := bbase (se 6 (by rfl) ⟨19245, by rfl⟩ : syracuseStep 821141 = 38491) (by norm_num)
theorem B821165 : Blo 546805 821165 := bbase (se 3 (by rfl) ⟨153968, by rfl⟩ : syracuseStep 821165 = 307937) (by norm_num)
theorem B821189 : Blo 546805 821189 := bbase (se 4 (by rfl) ⟨76986, by rfl⟩ : syracuseStep 821189 = 153973) (by norm_num)
theorem B657353 : Blo 546805 657353 := bbase (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) (by norm_num)
theorem B821213 : Blo 546805 821213 := bbase (se 3 (by rfl) ⟨153977, by rfl⟩ : syracuseStep 821213 = 307955) (by norm_num)
theorem B821237 : Blo 546805 821237 := bbase (se 5 (by rfl) ⟨38495, by rfl⟩ : syracuseStep 821237 = 76991) (by norm_num)
theorem B821261 : Blo 546805 821261 := bbase (se 3 (by rfl) ⟨153986, by rfl⟩ : syracuseStep 821261 = 307973) (by norm_num)
theorem B821285 : Blo 546805 821285 := bbase (se 4 (by rfl) ⟨76995, by rfl⟩ : syracuseStep 821285 = 153991) (by norm_num)
theorem B2820149 : Blo 546805 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B821309 : Blo 546805 821309 := bbase (se 3 (by rfl) ⟨153995, by rfl⟩ : syracuseStep 821309 = 307991) (by norm_num)
theorem B821333 : Blo 546805 821333 := bbase (se 8 (by rfl) ⟨4812, by rfl⟩ : syracuseStep 821333 = 9625) (by norm_num)
theorem B821357 : Blo 546805 821357 := bbase (se 3 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 821357 = 308009) (by norm_num)
theorem B821381 : Blo 546805 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B821405 : Blo 546805 821405 := bbase (se 3 (by rfl) ⟨154013, by rfl⟩ : syracuseStep 821405 = 308027) (by norm_num)
theorem B821429 : Blo 546805 821429 := bbase (se 5 (by rfl) ⟨38504, by rfl⟩ : syracuseStep 821429 = 77009) (by norm_num)
theorem B821453 : Blo 546805 821453 := bbase (se 3 (by rfl) ⟨154022, by rfl⟩ : syracuseStep 821453 = 308045) (by norm_num)
theorem B821477 : Blo 546805 821477 := bbase (se 4 (by rfl) ⟨77013, by rfl⟩ : syracuseStep 821477 = 154027) (by norm_num)
theorem B657661 : Blo 546805 657661 := bbase (se 3 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 657661 = 246623) (by norm_num)
theorem B821501 : Blo 546805 821501 := bbase (se 3 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 821501 = 308063) (by norm_num)
theorem B821525 : Blo 546805 821525 := bbase (se 6 (by rfl) ⟨19254, by rfl⟩ : syracuseStep 821525 = 38509) (by norm_num)
theorem B657689 : Blo 546805 657689 := bbase (se 2 (by rfl) ⟨246633, by rfl⟩ : syracuseStep 657689 = 493267) (by norm_num)
theorem B821549 : Blo 546805 821549 := bbase (se 3 (by rfl) ⟨154040, by rfl⟩ : syracuseStep 821549 = 308081) (by norm_num)
theorem B821573 : Blo 546805 821573 := bbase (se 4 (by rfl) ⟨77022, by rfl⟩ : syracuseStep 821573 = 154045) (by norm_num)
theorem B821597 : Blo 546805 821597 := bbase (se 3 (by rfl) ⟨154049, by rfl⟩ : syracuseStep 821597 = 308099) (by norm_num)
theorem B3115381 : Blo 546805 3115381 := bbase (se 5 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 3115381 = 292067) (by norm_num)
theorem B821621 : Blo 546805 821621 := bbase (se 5 (by rfl) ⟨38513, by rfl⟩ : syracuseStep 821621 = 77027) (by norm_num)
theorem B821645 : Blo 546805 821645 := bbase (se 3 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 821645 = 308117) (by norm_num)
theorem B821669 : Blo 546805 821669 := bbase (se 4 (by rfl) ⟨77031, by rfl⟩ : syracuseStep 821669 = 154063) (by norm_num)
theorem B821693 : Blo 546805 821693 := bbase (se 3 (by rfl) ⟨154067, by rfl⟩ : syracuseStep 821693 = 308135) (by norm_num)
theorem B821717 : Blo 546805 821717 := bbase (se 7 (by rfl) ⟨9629, by rfl⟩ : syracuseStep 821717 = 19259) (by norm_num)
theorem B821741 : Blo 546805 821741 := bbase (se 3 (by rfl) ⟨154076, by rfl⟩ : syracuseStep 821741 = 308153) (by norm_num)
theorem B821765 : Blo 546805 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B821789 : Blo 546805 821789 := bbase (se 3 (by rfl) ⟨154085, by rfl⟩ : syracuseStep 821789 = 308171) (by norm_num)
theorem B821813 : Blo 546805 821813 := bbase (se 5 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 821813 = 77045) (by norm_num)
theorem B821837 : Blo 546805 821837 := bbase (se 3 (by rfl) ⟨154094, by rfl⟩ : syracuseStep 821837 = 308189) (by norm_num)
theorem B821861 : Blo 546805 821861 := bbase (se 4 (by rfl) ⟨77049, by rfl⟩ : syracuseStep 821861 = 154099) (by norm_num)
theorem B821885 : Blo 546805 821885 := bbase (se 3 (by rfl) ⟨154103, by rfl⟩ : syracuseStep 821885 = 308207) (by norm_num)
theorem B625277 : Blo 546805 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B821909 : Blo 546805 821909 := bbase (se 6 (by rfl) ⟨19263, by rfl⟩ : syracuseStep 821909 = 38527) (by norm_num)
theorem B821933 : Blo 546805 821933 := bbase (se 3 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 821933 = 308225) (by norm_num)
theorem B821957 : Blo 546805 821957 := bbase (se 4 (by rfl) ⟨77058, by rfl⟩ : syracuseStep 821957 = 154117) (by norm_num)
theorem B985813 : Blo 546805 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B821981 : Blo 546805 821981 := bbase (se 3 (by rfl) ⟨154121, by rfl⟩ : syracuseStep 821981 = 308243) (by norm_num)
theorem B822005 : Blo 546805 822005 := bbase (se 5 (by rfl) ⟨38531, by rfl⟩ : syracuseStep 822005 = 77063) (by norm_num)
theorem B658189 : Blo 546805 658189 := bbase (se 3 (by rfl) ⟨123410, by rfl⟩ : syracuseStep 658189 = 246821) (by norm_num)
theorem B822029 : Blo 546805 822029 := bbase (se 3 (by rfl) ⟨154130, by rfl⟩ : syracuseStep 822029 = 308261) (by norm_num)
theorem B822053 : Blo 546805 822053 := bbase (se 4 (by rfl) ⟨77067, by rfl⟩ : syracuseStep 822053 = 154135) (by norm_num)
theorem B4000565 : Blo 546805 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B822077 : Blo 546805 822077 := bbase (se 3 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 822077 = 308279) (by norm_num)
theorem B822101 : Blo 546805 822101 := bbase (se 9 (by rfl) ⟨2408, by rfl⟩ : syracuseStep 822101 = 4817) (by norm_num)
theorem B2788181 : Blo 546805 2788181 := bbase (se 9 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 2788181 = 16337) (by norm_num)
theorem B822125 : Blo 546805 822125 := bbase (se 3 (by rfl) ⟨154148, by rfl⟩ : syracuseStep 822125 = 308297) (by norm_num)
theorem B822149 : Blo 546805 822149 := bbase (se 4 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 822149 = 154153) (by norm_num)
theorem B822173 : Blo 546805 822173 := bbase (se 3 (by rfl) ⟨154157, by rfl⟩ : syracuseStep 822173 = 308315) (by norm_num)
theorem B822197 : Blo 546805 822197 := bbase (se 5 (by rfl) ⟨38540, by rfl⟩ : syracuseStep 822197 = 77081) (by norm_num)
theorem B4164533 : Blo 546805 4164533 := bbase (se 5 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 4164533 = 390425) (by norm_num)
theorem B822221 : Blo 546805 822221 := bbase (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) (by norm_num)
theorem B822245 : Blo 546805 822245 := bbase (se 4 (by rfl) ⟨77085, by rfl⟩ : syracuseStep 822245 = 154171) (by norm_num)
theorem B822269 : Blo 546805 822269 := bbase (se 3 (by rfl) ⟨154175, by rfl⟩ : syracuseStep 822269 = 308351) (by norm_num)
theorem B822293 : Blo 546805 822293 := bbase (se 6 (by rfl) ⟨19272, by rfl⟩ : syracuseStep 822293 = 38545) (by norm_num)
theorem B822317 : Blo 546805 822317 := bbase (se 3 (by rfl) ⟨154184, by rfl⟩ : syracuseStep 822317 = 308369) (by norm_num)
theorem B822341 : Blo 546805 822341 := bbase (se 4 (by rfl) ⟨77094, by rfl⟩ : syracuseStep 822341 = 154189) (by norm_num)
theorem B822365 : Blo 546805 822365 := bbase (se 3 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 822365 = 308387) (by norm_num)
theorem B1313909 : Blo 546805 1313909 := bbase (se 5 (by rfl) ⟨61589, by rfl⟩ : syracuseStep 1313909 = 123179) (by norm_num)
theorem B822389 : Blo 546805 822389 := bbase (se 5 (by rfl) ⟨38549, by rfl⟩ : syracuseStep 822389 = 77099) (by norm_num)
theorem B822413 : Blo 546805 822413 := bbase (se 3 (by rfl) ⟨154202, by rfl⟩ : syracuseStep 822413 = 308405) (by norm_num)
theorem B1313957 : Blo 546805 1313957 := bbase (se 4 (by rfl) ⟨123183, by rfl⟩ : syracuseStep 1313957 = 246367) (by norm_num)
theorem B822437 : Blo 546805 822437 := bbase (se 4 (by rfl) ⟨77103, by rfl⟩ : syracuseStep 822437 = 154207) (by norm_num)
theorem B822461 : Blo 546805 822461 := bbase (se 3 (by rfl) ⟨154211, by rfl⟩ : syracuseStep 822461 = 308423) (by norm_num)
theorem B822485 : Blo 546805 822485 := bbase (se 7 (by rfl) ⟨9638, by rfl⟩ : syracuseStep 822485 = 19277) (by norm_num)
theorem B822509 : Blo 546805 822509 := bbase (se 3 (by rfl) ⟨154220, by rfl⟩ : syracuseStep 822509 = 308441) (by norm_num)
theorem B822533 : Blo 546805 822533 := bbase (se 4 (by rfl) ⟨77112, by rfl⟩ : syracuseStep 822533 = 154225) (by norm_num)
theorem B822557 : Blo 546805 822557 := bbase (se 3 (by rfl) ⟨154229, by rfl⟩ : syracuseStep 822557 = 308459) (by norm_num)
theorem B822581 : Blo 546805 822581 := bbase (se 5 (by rfl) ⟨38558, by rfl⟩ : syracuseStep 822581 = 77117) (by norm_num)
theorem B822605 : Blo 546805 822605 := bbase (se 3 (by rfl) ⟨154238, by rfl⟩ : syracuseStep 822605 = 308477) (by norm_num)
theorem B822629 : Blo 546805 822629 := bbase (se 4 (by rfl) ⟨77121, by rfl⟩ : syracuseStep 822629 = 154243) (by norm_num)
theorem B822653 : Blo 546805 822653 := bbase (se 3 (by rfl) ⟨154247, by rfl⟩ : syracuseStep 822653 = 308495) (by norm_num)
theorem B822677 : Blo 546805 822677 := bbase (se 6 (by rfl) ⟨19281, by rfl⟩ : syracuseStep 822677 = 38563) (by norm_num)
theorem B822701 : Blo 546805 822701 := bbase (se 3 (by rfl) ⟨154256, by rfl⟩ : syracuseStep 822701 = 308513) (by norm_num)
theorem B1314245 : Blo 546805 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B822725 : Blo 546805 822725 := bbase (se 4 (by rfl) ⟨77130, by rfl⟩ : syracuseStep 822725 = 154261) (by norm_num)
theorem B822749 : Blo 546805 822749 := bbase (se 3 (by rfl) ⟨154265, by rfl⟩ : syracuseStep 822749 = 308531) (by norm_num)
theorem B822773 : Blo 546805 822773 := bbase (se 5 (by rfl) ⟨38567, by rfl⟩ : syracuseStep 822773 = 77135) (by norm_num)
theorem B626185 : Blo 546805 626185 := bbase (se 2 (by rfl) ⟨234819, by rfl⟩ : syracuseStep 626185 = 469639) (by norm_num)
theorem B822797 : Blo 546805 822797 := bbase (se 3 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 822797 = 308549) (by norm_num)
theorem B822821 : Blo 546805 822821 := bbase (se 4 (by rfl) ⟨77139, by rfl⟩ : syracuseStep 822821 = 154279) (by norm_num)
theorem B1248821 : Blo 546805 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B822845 : Blo 546805 822845 := bbase (se 3 (by rfl) ⟨154283, by rfl⟩ : syracuseStep 822845 = 308567) (by norm_num)
theorem B822869 : Blo 546805 822869 := bbase (se 8 (by rfl) ⟨4821, by rfl⟩ : syracuseStep 822869 = 9643) (by norm_num)
theorem B1478245 : Blo 546805 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B822893 : Blo 546805 822893 := bbase (se 3 (by rfl) ⟨154292, by rfl⟩ : syracuseStep 822893 = 308585) (by norm_num)
theorem B822917 : Blo 546805 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B822941 : Blo 546805 822941 := bbase (se 3 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 822941 = 308603) (by norm_num)
theorem B822965 : Blo 546805 822965 := bbase (se 5 (by rfl) ⟨38576, by rfl⟩ : syracuseStep 822965 = 77153) (by norm_num)
theorem B822989 : Blo 546805 822989 := bbase (se 3 (by rfl) ⟨154310, by rfl⟩ : syracuseStep 822989 = 308621) (by norm_num)
theorem B823013 : Blo 546805 823013 := bbase (se 4 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 823013 = 154315) (by norm_num)
theorem B823037 : Blo 546805 823037 := bbase (se 3 (by rfl) ⟨154319, by rfl⟩ : syracuseStep 823037 = 308639) (by norm_num)
theorem B823061 : Blo 546805 823061 := bbase (se 6 (by rfl) ⟨19290, by rfl⟩ : syracuseStep 823061 = 38581) (by norm_num)
theorem B823085 : Blo 546805 823085 := bbase (se 3 (by rfl) ⟨154328, by rfl⟩ : syracuseStep 823085 = 308657) (by norm_num)
theorem B823109 : Blo 546805 823109 := bbase (se 4 (by rfl) ⟨77166, by rfl⟩ : syracuseStep 823109 = 154333) (by norm_num)
theorem B823133 : Blo 546805 823133 := bbase (se 3 (by rfl) ⟨154337, by rfl⟩ : syracuseStep 823133 = 308675) (by norm_num)
theorem B823157 : Blo 546805 823157 := bbase (se 5 (by rfl) ⟨38585, by rfl⟩ : syracuseStep 823157 = 77171) (by norm_num)
theorem B823181 : Blo 546805 823181 := bbase (se 3 (by rfl) ⟨154346, by rfl⟩ : syracuseStep 823181 = 308693) (by norm_num)
theorem B823205 : Blo 546805 823205 := bbase (se 4 (by rfl) ⟨77175, by rfl⟩ : syracuseStep 823205 = 154351) (by norm_num)
theorem B659377 : Blo 546805 659377 := bbase (se 2 (by rfl) ⟨247266, by rfl⟩ : syracuseStep 659377 = 494533) (by norm_num)
theorem B823229 : Blo 546805 823229 := bbase (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) (by norm_num)
theorem B692165 : Blo 546805 692165 := bbase (se 4 (by rfl) ⟨64890, by rfl⟩ : syracuseStep 692165 = 129781) (by norm_num)
theorem B823253 : Blo 546805 823253 := bbase (se 7 (by rfl) ⟨9647, by rfl⟩ : syracuseStep 823253 = 19295) (by norm_num)
theorem B823277 : Blo 546805 823277 := bbase (se 3 (by rfl) ⟨154364, by rfl⟩ : syracuseStep 823277 = 308729) (by norm_num)
theorem B692221 : Blo 546805 692221 := bbase (se 3 (by rfl) ⟨129791, by rfl⟩ : syracuseStep 692221 = 259583) (by norm_num)
theorem B823301 : Blo 546805 823301 := bbase (se 4 (by rfl) ⟨77184, by rfl⟩ : syracuseStep 823301 = 154369) (by norm_num)
theorem B823325 : Blo 546805 823325 := bbase (se 3 (by rfl) ⟨154373, by rfl⟩ : syracuseStep 823325 = 308747) (by norm_num)
theorem B823349 : Blo 546805 823349 := bbase (se 5 (by rfl) ⟨38594, by rfl⟩ : syracuseStep 823349 = 77189) (by norm_num)
theorem B823373 : Blo 546805 823373 := bbase (se 3 (by rfl) ⟨154382, by rfl⟩ : syracuseStep 823373 = 308765) (by norm_num)
theorem B1413197 : Blo 546805 1413197 := bbase (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) (by norm_num)
theorem B987221 : Blo 546805 987221 := bbase (se 8 (by rfl) ⟨5784, by rfl⟩ : syracuseStep 987221 = 11569) (by norm_num)
theorem B21139541 : Blo 546805 21139541 := bbase (se 8 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 21139541 = 247729) (by norm_num)
theorem B692317 : Blo 546805 692317 := bbase (se 3 (by rfl) ⟨129809, by rfl⟩ : syracuseStep 692317 = 259619) (by norm_num)
theorem B823397 : Blo 546805 823397 := bbase (se 4 (by rfl) ⟨77193, by rfl⟩ : syracuseStep 823397 = 154387) (by norm_num)
theorem B659569 : Blo 546805 659569 := bbase (se 2 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 659569 = 494677) (by norm_num)
theorem B823421 : Blo 546805 823421 := bbase (se 3 (by rfl) ⟨154391, by rfl⟩ : syracuseStep 823421 = 308783) (by norm_num)
theorem B987277 : Blo 546805 987277 := bbase (se 3 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 987277 = 370229) (by norm_num)
theorem B823445 : Blo 546805 823445 := bbase (se 6 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 823445 = 38599) (by norm_num)
theorem B823469 : Blo 546805 823469 := bbase (se 3 (by rfl) ⟨154400, by rfl⟩ : syracuseStep 823469 = 308801) (by norm_num)
theorem B823493 : Blo 546805 823493 := bbase (se 4 (by rfl) ⟨77202, by rfl⟩ : syracuseStep 823493 = 154405) (by norm_num)
theorem B659669 : Blo 546805 659669 := bbase (se 7 (by rfl) ⟨7730, by rfl⟩ : syracuseStep 659669 = 15461) (by norm_num)
theorem B823517 : Blo 546805 823517 := bbase (se 3 (by rfl) ⟨154409, by rfl⟩ : syracuseStep 823517 = 308819) (by norm_num)
theorem B823541 : Blo 546805 823541 := bbase (se 5 (by rfl) ⟨38603, by rfl⟩ : syracuseStep 823541 = 77207) (by norm_num)
theorem B889093 : Blo 546805 889093 := bbase (se 4 (by rfl) ⟨83352, by rfl⟩ : syracuseStep 889093 = 166705) (by norm_num)
theorem B692489 : Blo 546805 692489 := bbase (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) (by norm_num)
theorem B823565 : Blo 546805 823565 := bbase (se 3 (by rfl) ⟨154418, by rfl⟩ : syracuseStep 823565 = 308837) (by norm_num)
theorem B823589 : Blo 546805 823589 := bbase (se 4 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 823589 = 154423) (by norm_num)
theorem B3117365 : Blo 546805 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B823613 : Blo 546805 823613 := bbase (se 3 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 823613 = 308855) (by norm_num)
theorem B692545 : Blo 546805 692545 := bbase (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) (by norm_num)
theorem B823637 : Blo 546805 823637 := bbase (se 10 (by rfl) ⟨1206, by rfl⟩ : syracuseStep 823637 = 2413) (by norm_num)
theorem B823661 : Blo 546805 823661 := bbase (se 3 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 823661 = 308873) (by norm_num)
theorem B823685 : Blo 546805 823685 := bbase (se 4 (by rfl) ⟨77220, by rfl⟩ : syracuseStep 823685 = 154441) (by norm_num)
theorem B823709 : Blo 546805 823709 := bbase (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) (by norm_num)
theorem B692641 : Blo 546805 692641 := bbase (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) (by norm_num)
theorem B823733 : Blo 546805 823733 := bbase (se 5 (by rfl) ⟨38612, by rfl⟩ : syracuseStep 823733 = 77225) (by norm_num)
theorem B2822597 : Blo 546805 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B823757 : Blo 546805 823757 := bbase (se 3 (by rfl) ⟨154454, by rfl⟩ : syracuseStep 823757 = 308909) (by norm_num)
theorem B823781 : Blo 546805 823781 := bbase (se 4 (by rfl) ⟨77229, by rfl⟩ : syracuseStep 823781 = 154459) (by norm_num)
theorem B594421 : Blo 546805 594421 := bbase (se 5 (by rfl) ⟨27863, by rfl⟩ : syracuseStep 594421 = 55727) (by norm_num)
theorem B823805 : Blo 546805 823805 := bbase (se 3 (by rfl) ⟨154463, by rfl⟩ : syracuseStep 823805 = 308927) (by norm_num)
theorem B823829 : Blo 546805 823829 := bbase (se 6 (by rfl) ⟨19308, by rfl⟩ : syracuseStep 823829 = 38617) (by norm_num)
theorem B823853 : Blo 546805 823853 := bbase (se 3 (by rfl) ⟨154472, by rfl⟩ : syracuseStep 823853 = 308945) (by norm_num)
theorem B823877 : Blo 546805 823877 := bbase (se 4 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 823877 = 154477) (by norm_num)
theorem B692813 : Blo 546805 692813 := bbase (se 3 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 692813 = 259805) (by norm_num)
theorem B823901 : Blo 546805 823901 := bbase (se 3 (by rfl) ⟨154481, by rfl⟩ : syracuseStep 823901 = 308963) (by norm_num)
theorem B823925 : Blo 546805 823925 := bbase (se 5 (by rfl) ⟨38621, by rfl⟩ : syracuseStep 823925 = 77243) (by norm_num)
theorem B692869 : Blo 546805 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B823949 : Blo 546805 823949 := bbase (se 3 (by rfl) ⟨154490, by rfl⟩ : syracuseStep 823949 = 308981) (by norm_num)
theorem B823973 : Blo 546805 823973 := bbase (se 4 (by rfl) ⟨77247, by rfl⟩ : syracuseStep 823973 = 154495) (by norm_num)
theorem B823997 : Blo 546805 823997 := bbase (se 3 (by rfl) ⟨154499, by rfl⟩ : syracuseStep 823997 = 308999) (by norm_num)
theorem B824021 : Blo 546805 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B692965 : Blo 546805 692965 := bbase (se 4 (by rfl) ⟨64965, by rfl⟩ : syracuseStep 692965 = 129931) (by norm_num)
theorem B824045 : Blo 546805 824045 := bbase (se 3 (by rfl) ⟨154508, by rfl⟩ : syracuseStep 824045 = 309017) (by norm_num)
theorem B824069 : Blo 546805 824069 := bbase (se 4 (by rfl) ⟨77256, by rfl⟩ : syracuseStep 824069 = 154513) (by norm_num)
theorem B824093 : Blo 546805 824093 := bbase (se 3 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 824093 = 309035) (by norm_num)
theorem B824117 : Blo 546805 824117 := bbase (se 5 (by rfl) ⟨38630, by rfl⟩ : syracuseStep 824117 = 77261) (by norm_num)
theorem B824141 : Blo 546805 824141 := bbase (se 3 (by rfl) ⟨154526, by rfl⟩ : syracuseStep 824141 = 309053) (by norm_num)
theorem B824165 : Blo 546805 824165 := bbase (se 4 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 824165 = 154531) (by norm_num)
theorem B824189 : Blo 546805 824189 := bbase (se 3 (by rfl) ⟨154535, by rfl⟩ : syracuseStep 824189 = 309071) (by norm_num)
theorem B693137 : Blo 546805 693137 := bbase (se 2 (by rfl) ⟨259926, by rfl⟩ : syracuseStep 693137 = 519853) (by norm_num)
theorem B824213 : Blo 546805 824213 := bbase (se 6 (by rfl) ⟨19317, by rfl⟩ : syracuseStep 824213 = 38635) (by norm_num)
theorem B824237 : Blo 546805 824237 := bbase (se 3 (by rfl) ⟨154544, by rfl⟩ : syracuseStep 824237 = 309089) (by norm_num)
theorem B1872821 : Blo 546805 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B824261 : Blo 546805 824261 := bbase (se 4 (by rfl) ⟨77274, by rfl⟩ : syracuseStep 824261 = 154549) (by norm_num)
theorem B693193 : Blo 546805 693193 := bbase (se 2 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 693193 = 519895) (by norm_num)
theorem B824285 : Blo 546805 824285 := bbase (se 3 (by rfl) ⟨154553, by rfl⟩ : syracuseStep 824285 = 309107) (by norm_num)
theorem B660457 : Blo 546805 660457 := bbase (se 2 (by rfl) ⟨247671, by rfl⟩ : syracuseStep 660457 = 495343) (by norm_num)
theorem B824309 : Blo 546805 824309 := bbase (se 5 (by rfl) ⟨38639, by rfl⟩ : syracuseStep 824309 = 77279) (by norm_num)
theorem B824333 : Blo 546805 824333 := bbase (se 3 (by rfl) ⟨154562, by rfl⟩ : syracuseStep 824333 = 309125) (by norm_num)
theorem B824357 : Blo 546805 824357 := bbase (se 4 (by rfl) ⟨77283, by rfl⟩ : syracuseStep 824357 = 154567) (by norm_num)
theorem B693289 : Blo 546805 693289 := bbase (se 2 (by rfl) ⟨259983, by rfl⟩ : syracuseStep 693289 = 519967) (by norm_num)
theorem B824381 : Blo 546805 824381 := bbase (se 3 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 824381 = 309143) (by norm_num)
theorem B824405 : Blo 546805 824405 := bbase (se 8 (by rfl) ⟨4830, by rfl⟩ : syracuseStep 824405 = 9661) (by norm_num)
theorem B824429 : Blo 546805 824429 := bbase (se 3 (by rfl) ⟨154580, by rfl⟩ : syracuseStep 824429 = 309161) (by norm_num)
theorem B824453 : Blo 546805 824453 := bbase (se 4 (by rfl) ⟨77292, by rfl⟩ : syracuseStep 824453 = 154585) (by norm_num)
theorem B922765 : Blo 546805 922765 := bbase (se 3 (by rfl) ⟨173018, by rfl⟩ : syracuseStep 922765 = 346037) (by norm_num)
theorem B824477 : Blo 546805 824477 := bbase (se 3 (by rfl) ⟨154589, by rfl⟩ : syracuseStep 824477 = 309179) (by norm_num)
theorem B824501 : Blo 546805 824501 := bbase (se 5 (by rfl) ⟨38648, by rfl⟩ : syracuseStep 824501 = 77297) (by norm_num)
theorem B824525 : Blo 546805 824525 := bbase (se 3 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 824525 = 309197) (by norm_num)
theorem B693461 : Blo 546805 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B922853 : Blo 546805 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B824549 : Blo 546805 824549 := bbase (se 4 (by rfl) ⟨77301, by rfl⟩ : syracuseStep 824549 = 154603) (by norm_num)
theorem B824573 : Blo 546805 824573 := bbase (se 3 (by rfl) ⟨154607, by rfl⟩ : syracuseStep 824573 = 309215) (by norm_num)
theorem B693517 : Blo 546805 693517 := bbase (se 3 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 693517 = 260069) (by norm_num)
theorem B824597 : Blo 546805 824597 := bbase (se 6 (by rfl) ⟨19326, by rfl⟩ : syracuseStep 824597 = 38653) (by norm_num)
theorem B824621 : Blo 546805 824621 := bbase (se 3 (by rfl) ⟨154616, by rfl⟩ : syracuseStep 824621 = 309233) (by norm_num)
theorem B824645 : Blo 546805 824645 := bbase (se 4 (by rfl) ⟨77310, by rfl⟩ : syracuseStep 824645 = 154621) (by norm_num)
theorem B824669 : Blo 546805 824669 := bbase (se 3 (by rfl) ⟨154625, by rfl⟩ : syracuseStep 824669 = 309251) (by norm_num)
theorem B922981 : Blo 546805 922981 := bbase (se 4 (by rfl) ⟨86529, by rfl⟩ : syracuseStep 922981 = 173059) (by norm_num)
theorem B628069 : Blo 546805 628069 := bbase (se 4 (by rfl) ⟨58881, by rfl⟩ : syracuseStep 628069 = 117763) (by norm_num)
theorem B693613 : Blo 546805 693613 := bbase (se 3 (by rfl) ⟨130052, by rfl⟩ : syracuseStep 693613 = 260105) (by norm_num)
theorem B824693 : Blo 546805 824693 := bbase (se 5 (by rfl) ⟨38657, by rfl⟩ : syracuseStep 824693 = 77315) (by norm_num)
theorem B824717 : Blo 546805 824717 := bbase (se 3 (by rfl) ⟨154634, by rfl⟩ : syracuseStep 824717 = 309269) (by norm_num)
theorem B824741 : Blo 546805 824741 := bbase (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) (by norm_num)
theorem B923069 : Blo 546805 923069 := bbase (se 3 (by rfl) ⟨173075, by rfl⟩ : syracuseStep 923069 = 346151) (by norm_num)
theorem B824765 : Blo 546805 824765 := bbase (se 3 (by rfl) ⟨154643, by rfl⟩ : syracuseStep 824765 = 309287) (by norm_num)
theorem B824789 : Blo 546805 824789 := bbase (se 7 (by rfl) ⟨9665, by rfl⟩ : syracuseStep 824789 = 19331) (by norm_num)
theorem B824813 : Blo 546805 824813 := bbase (se 3 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 824813 = 309305) (by norm_num)
theorem B824837 : Blo 546805 824837 := bbase (se 4 (by rfl) ⟨77328, by rfl⟩ : syracuseStep 824837 = 154657) (by norm_num)
theorem B693785 : Blo 546805 693785 := bbase (se 2 (by rfl) ⟨260169, by rfl⟩ : syracuseStep 693785 = 520339) (by norm_num)
theorem B824861 : Blo 546805 824861 := bbase (se 3 (by rfl) ⟨154661, by rfl⟩ : syracuseStep 824861 = 309323) (by norm_num)
theorem B824885 : Blo 546805 824885 := bbase (se 5 (by rfl) ⟨38666, by rfl⟩ : syracuseStep 824885 = 77333) (by norm_num)
theorem B923197 : Blo 546805 923197 := bbase (se 3 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 923197 = 346199) (by norm_num)
theorem B824909 : Blo 546805 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B693841 : Blo 546805 693841 := bbase (se 2 (by rfl) ⟨260190, by rfl⟩ : syracuseStep 693841 = 520381) (by norm_num)
theorem B824933 : Blo 546805 824933 := bbase (se 4 (by rfl) ⟨77337, by rfl⟩ : syracuseStep 824933 = 154675) (by norm_num)
theorem B824957 : Blo 546805 824957 := bbase (se 3 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 824957 = 309359) (by norm_num)
theorem B923285 : Blo 546805 923285 := bbase (se 6 (by rfl) ⟨21639, by rfl⟩ : syracuseStep 923285 = 43279) (by norm_num)
theorem B3511957 : Blo 546805 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B824981 : Blo 546805 824981 := bbase (se 6 (by rfl) ⟨19335, by rfl⟩ : syracuseStep 824981 = 38671) (by norm_num)
theorem B825005 : Blo 546805 825005 := bbase (se 3 (by rfl) ⟨154688, by rfl⟩ : syracuseStep 825005 = 309377) (by norm_num)
theorem B693937 : Blo 546805 693937 := bbase (se 2 (by rfl) ⟨260226, by rfl⟩ : syracuseStep 693937 = 520453) (by norm_num)
theorem B661169 : Blo 546805 661169 := bbase (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) (by norm_num)
theorem B825029 : Blo 546805 825029 := bbase (se 4 (by rfl) ⟨77346, by rfl⟩ : syracuseStep 825029 = 154693) (by norm_num)
theorem B825053 : Blo 546805 825053 := bbase (se 3 (by rfl) ⟨154697, by rfl⟩ : syracuseStep 825053 = 309395) (by norm_num)
theorem B825077 : Blo 546805 825077 := bbase (se 5 (by rfl) ⟨38675, by rfl⟩ : syracuseStep 825077 = 77351) (by norm_num)
theorem B825101 : Blo 546805 825101 := bbase (se 3 (by rfl) ⟨154706, by rfl⟩ : syracuseStep 825101 = 309413) (by norm_num)
theorem B923413 : Blo 546805 923413 := bbase (se 6 (by rfl) ⟨21642, by rfl⟩ : syracuseStep 923413 = 43285) (by norm_num)
theorem B825125 : Blo 546805 825125 := bbase (se 4 (by rfl) ⟨77355, by rfl⟩ : syracuseStep 825125 = 154711) (by norm_num)
theorem B890677 : Blo 546805 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B825149 : Blo 546805 825149 := bbase (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) (by norm_num)
theorem B1316677 : Blo 546805 1316677 := bbase (se 4 (by rfl) ⟨123438, by rfl⟩ : syracuseStep 1316677 = 246877) (by norm_num)
theorem B7018325 : Blo 546805 7018325 := bbase (se 9 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 7018325 = 41123) (by norm_num)
theorem B825173 : Blo 546805 825173 := bbase (se 9 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 825173 = 4835) (by norm_num)
theorem B694109 : Blo 546805 694109 := bbase (se 3 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 694109 = 260291) (by norm_num)
theorem B923501 : Blo 546805 923501 := bbase (se 3 (by rfl) ⟨173156, by rfl⟩ : syracuseStep 923501 = 346313) (by norm_num)
theorem B825197 : Blo 546805 825197 := bbase (se 3 (by rfl) ⟨154724, by rfl⟩ : syracuseStep 825197 = 309449) (by norm_num)
theorem B825221 : Blo 546805 825221 := bbase (se 4 (by rfl) ⟨77364, by rfl⟩ : syracuseStep 825221 = 154729) (by norm_num)
theorem B694165 : Blo 546805 694165 := bbase (se 6 (by rfl) ⟨16269, by rfl⟩ : syracuseStep 694165 = 32539) (by norm_num)
theorem B825245 : Blo 546805 825245 := bbase (se 3 (by rfl) ⟨154733, by rfl⟩ : syracuseStep 825245 = 309467) (by norm_num)
theorem B825269 : Blo 546805 825269 := bbase (se 5 (by rfl) ⟨38684, by rfl⟩ : syracuseStep 825269 = 77369) (by norm_num)
theorem B825293 : Blo 546805 825293 := bbase (se 3 (by rfl) ⟨154742, by rfl⟩ : syracuseStep 825293 = 309485) (by norm_num)
theorem B9050069 : Blo 546805 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B825317 : Blo 546805 825317 := bbase (se 4 (by rfl) ⟨77373, by rfl⟩ : syracuseStep 825317 = 154747) (by norm_num)
theorem B923629 : Blo 546805 923629 := bbase (se 3 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 923629 = 346361) (by norm_num)
theorem B595949 : Blo 546805 595949 := bbase (se 3 (by rfl) ⟨111740, by rfl⟩ : syracuseStep 595949 = 223481) (by norm_num)
theorem B694261 : Blo 546805 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B825341 : Blo 546805 825341 := bbase (se 3 (by rfl) ⟨154751, by rfl⟩ : syracuseStep 825341 = 309503) (by norm_num)
theorem B661505 : Blo 546805 661505 := bbase (se 2 (by rfl) ⟨248064, by rfl⟩ : syracuseStep 661505 = 496129) (by norm_num)
theorem B825365 : Blo 546805 825365 := bbase (se 6 (by rfl) ⟨19344, by rfl⟩ : syracuseStep 825365 = 38689) (by norm_num)
theorem B825389 : Blo 546805 825389 := bbase (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) (by norm_num)
theorem B923717 : Blo 546805 923717 := bbase (se 4 (by rfl) ⟨86598, by rfl⟩ : syracuseStep 923717 = 173197) (by norm_num)
theorem B825413 : Blo 546805 825413 := bbase (se 4 (by rfl) ⟨77382, by rfl⟩ : syracuseStep 825413 = 154765) (by norm_num)
theorem B825437 : Blo 546805 825437 := bbase (se 3 (by rfl) ⟨154769, by rfl⟩ : syracuseStep 825437 = 309539) (by norm_num)
theorem B825461 : Blo 546805 825461 := bbase (se 5 (by rfl) ⟨38693, by rfl⟩ : syracuseStep 825461 = 77387) (by norm_num)
theorem B661621 : Blo 546805 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B825485 : Blo 546805 825485 := bbase (se 3 (by rfl) ⟨154778, by rfl⟩ : syracuseStep 825485 = 309557) (by norm_num)
theorem B661645 : Blo 546805 661645 := bbase (se 3 (by rfl) ⟨124058, by rfl⟩ : syracuseStep 661645 = 248117) (by norm_num)
theorem B694433 : Blo 546805 694433 := bbase (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) (by norm_num)
theorem B825509 : Blo 546805 825509 := bbase (se 4 (by rfl) ⟨77391, by rfl⟩ : syracuseStep 825509 = 154783) (by norm_num)
theorem B825533 : Blo 546805 825533 := bbase (se 3 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 825533 = 309575) (by norm_num)
theorem B923845 : Blo 546805 923845 := bbase (se 4 (by rfl) ⟨86610, by rfl⟩ : syracuseStep 923845 = 173221) (by norm_num)
theorem B825557 : Blo 546805 825557 := bbase (se 7 (by rfl) ⟨9674, by rfl⟩ : syracuseStep 825557 = 19349) (by norm_num)
theorem B694489 : Blo 546805 694489 := bbase (se 2 (by rfl) ⟨260433, by rfl⟩ : syracuseStep 694489 = 520867) (by norm_num)
theorem B825581 : Blo 546805 825581 := bbase (se 3 (by rfl) ⟨154796, by rfl⟩ : syracuseStep 825581 = 309593) (by norm_num)
theorem B825605 : Blo 546805 825605 := bbase (se 4 (by rfl) ⟨77400, by rfl⟩ : syracuseStep 825605 = 154801) (by norm_num)
theorem B923933 : Blo 546805 923933 := bbase (se 3 (by rfl) ⟨173237, by rfl⟩ : syracuseStep 923933 = 346475) (by norm_num)
theorem B825629 : Blo 546805 825629 := bbase (se 3 (by rfl) ⟨154805, by rfl⟩ : syracuseStep 825629 = 309611) (by norm_num)
theorem B825653 : Blo 546805 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B694585 : Blo 546805 694585 := bbase (se 2 (by rfl) ⟨260469, by rfl⟩ : syracuseStep 694585 = 520939) (by norm_num)
theorem B1972549 : Blo 546805 1972549 := bbase (se 4 (by rfl) ⟨184926, by rfl⟩ : syracuseStep 1972549 = 369853) (by norm_num)
theorem B825677 : Blo 546805 825677 := bbase (se 3 (by rfl) ⟨154814, by rfl⟩ : syracuseStep 825677 = 309629) (by norm_num)
theorem B825701 : Blo 546805 825701 := bbase (se 4 (by rfl) ⟨77409, by rfl⟩ : syracuseStep 825701 = 154819) (by norm_num)
theorem B825725 : Blo 546805 825725 := bbase (se 3 (by rfl) ⟨154823, by rfl⟩ : syracuseStep 825725 = 309647) (by norm_num)
theorem B825749 : Blo 546805 825749 := bbase (se 6 (by rfl) ⟨19353, by rfl⟩ : syracuseStep 825749 = 38707) (by norm_num)
theorem B924061 : Blo 546805 924061 := bbase (se 3 (by rfl) ⟨173261, by rfl⟩ : syracuseStep 924061 = 346523) (by norm_num)
theorem B1317293 : Blo 546805 1317293 := bbase (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) (by norm_num)
theorem B825773 : Blo 546805 825773 := bbase (se 3 (by rfl) ⟨154832, by rfl⟩ : syracuseStep 825773 = 309665) (by norm_num)
theorem B825797 : Blo 546805 825797 := bbase (se 4 (by rfl) ⟨77418, by rfl⟩ : syracuseStep 825797 = 154837) (by norm_num)
theorem B3119573 : Blo 546805 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B825821 : Blo 546805 825821 := bbase (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) (by norm_num)
theorem B694757 : Blo 546805 694757 := bbase (se 4 (by rfl) ⟨65133, by rfl⟩ : syracuseStep 694757 = 130267) (by norm_num)
theorem B924149 : Blo 546805 924149 := bbase (se 5 (by rfl) ⟨43319, by rfl⟩ : syracuseStep 924149 = 86639) (by norm_num)
theorem B825845 : Blo 546805 825845 := bbase (se 5 (by rfl) ⟨38711, by rfl⟩ : syracuseStep 825845 = 77423) (by norm_num)
theorem B825869 : Blo 546805 825869 := bbase (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) (by norm_num)
theorem B694813 : Blo 546805 694813 := bbase (se 3 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 694813 = 260555) (by norm_num)
theorem B825893 : Blo 546805 825893 := bbase (se 4 (by rfl) ⟨77427, by rfl⟩ : syracuseStep 825893 = 154855) (by norm_num)
theorem B825917 : Blo 546805 825917 := bbase (se 3 (by rfl) ⟨154859, by rfl⟩ : syracuseStep 825917 = 309719) (by norm_num)
theorem B825941 : Blo 546805 825941 := bbase (se 8 (by rfl) ⟨4839, by rfl⟩ : syracuseStep 825941 = 9679) (by norm_num)
theorem B825965 : Blo 546805 825965 := bbase (se 3 (by rfl) ⟨154868, by rfl⟩ : syracuseStep 825965 = 309737) (by norm_num)
theorem B924277 : Blo 546805 924277 := bbase (se 5 (by rfl) ⟨43325, by rfl⟩ : syracuseStep 924277 = 86651) (by norm_num)
theorem B1317493 : Blo 546805 1317493 := bbase (se 5 (by rfl) ⟨61757, by rfl⟩ : syracuseStep 1317493 = 123515) (by norm_num)
theorem B694909 : Blo 546805 694909 := bbase (se 3 (by rfl) ⟨130295, by rfl⟩ : syracuseStep 694909 = 260591) (by norm_num)
theorem B989821 : Blo 546805 989821 := bbase (se 3 (by rfl) ⟨185591, by rfl⟩ : syracuseStep 989821 = 371183) (by norm_num)
theorem B825989 : Blo 546805 825989 := bbase (se 4 (by rfl) ⟨77436, by rfl⟩ : syracuseStep 825989 = 154873) (by norm_num)
theorem B826013 : Blo 546805 826013 := bbase (se 3 (by rfl) ⟨154877, by rfl⟩ : syracuseStep 826013 = 309755) (by norm_num)
theorem B826037 : Blo 546805 826037 := bbase (se 5 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 826037 = 77441) (by norm_num)
theorem B924365 : Blo 546805 924365 := bbase (se 3 (by rfl) ⟨173318, by rfl⟩ : syracuseStep 924365 = 346637) (by norm_num)
theorem B826061 : Blo 546805 826061 := bbase (se 3 (by rfl) ⟨154886, by rfl⟩ : syracuseStep 826061 = 309773) (by norm_num)
theorem B826085 : Blo 546805 826085 := bbase (se 4 (by rfl) ⟨77445, by rfl⟩ : syracuseStep 826085 = 154891) (by norm_num)
theorem B826109 : Blo 546805 826109 := bbase (se 3 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 826109 = 309791) (by norm_num)
theorem B989965 : Blo 546805 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B826133 : Blo 546805 826133 := bbase (se 6 (by rfl) ⟨19362, by rfl⟩ : syracuseStep 826133 = 38725) (by norm_num)
theorem B695081 : Blo 546805 695081 := bbase (se 2 (by rfl) ⟨260655, by rfl⟩ : syracuseStep 695081 = 521311) (by norm_num)
theorem B826157 : Blo 546805 826157 := bbase (se 3 (by rfl) ⟨154904, by rfl⟩ : syracuseStep 826157 = 309809) (by norm_num)
theorem B2497349 : Blo 546805 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B826181 : Blo 546805 826181 := bbase (se 4 (by rfl) ⟨77454, by rfl⟩ : syracuseStep 826181 = 154909) (by norm_num)
theorem B924493 : Blo 546805 924493 := bbase (se 3 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 924493 = 346685) (by norm_num)
theorem B826205 : Blo 546805 826205 := bbase (se 3 (by rfl) ⟨154913, by rfl⟩ : syracuseStep 826205 = 309827) (by norm_num)
theorem B695137 : Blo 546805 695137 := bbase (se 2 (by rfl) ⟨260676, by rfl⟩ : syracuseStep 695137 = 521353) (by norm_num)
theorem B924581 : Blo 546805 924581 := bbase (se 4 (by rfl) ⟨86679, by rfl⟩ : syracuseStep 924581 = 173359) (by norm_num)
theorem B695233 : Blo 546805 695233 := bbase (se 2 (by rfl) ⟨260712, by rfl⟩ : syracuseStep 695233 = 521425) (by norm_num)
theorem B924709 : Blo 546805 924709 := bbase (se 4 (by rfl) ⟨86691, by rfl⟩ : syracuseStep 924709 = 173383) (by norm_num)
theorem B695405 : Blo 546805 695405 := bbase (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) (by norm_num)
theorem B924797 : Blo 546805 924797 := bbase (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) (by norm_num)
theorem B695461 : Blo 546805 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B924925 : Blo 546805 924925 := bbase (se 3 (by rfl) ⟨173423, by rfl⟩ : syracuseStep 924925 = 346847) (by norm_num)
theorem B695557 : Blo 546805 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B925013 : Blo 546805 925013 := bbase (se 11 (by rfl) ⟨677, by rfl⟩ : syracuseStep 925013 = 1355) (by norm_num)
theorem B10722709 : Blo 546805 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B1318301 : Blo 546805 1318301 := bbase (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) (by norm_num)
theorem B695729 : Blo 546805 695729 := bbase (se 2 (by rfl) ⟨260898, by rfl⟩ : syracuseStep 695729 = 521797) (by norm_num)
theorem B925141 : Blo 546805 925141 := bbase (se 7 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 925141 = 21683) (by norm_num)
theorem B695785 : Blo 546805 695785 := bbase (se 2 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 695785 = 521839) (by norm_num)
theorem B925229 : Blo 546805 925229 := bbase (se 3 (by rfl) ⟨173480, by rfl⟩ : syracuseStep 925229 = 346961) (by norm_num)
theorem B695881 : Blo 546805 695881 := bbase (se 2 (by rfl) ⟨260955, by rfl⟩ : syracuseStep 695881 = 521911) (by norm_num)
theorem B925357 : Blo 546805 925357 := bbase (se 3 (by rfl) ⟨173504, by rfl⟩ : syracuseStep 925357 = 347009) (by norm_num)
theorem B696053 : Blo 546805 696053 := bbase (se 5 (by rfl) ⟨32627, by rfl⟩ : syracuseStep 696053 = 65255) (by norm_num)
theorem B925445 : Blo 546805 925445 := bbase (se 4 (by rfl) ⟨86760, by rfl⟩ : syracuseStep 925445 = 173521) (by norm_num)
theorem B1384229 : Blo 546805 1384229 := bbase (se 4 (by rfl) ⟨129771, by rfl⟩ : syracuseStep 1384229 = 259543) (by norm_num)
theorem B696109 : Blo 546805 696109 := bbase (se 3 (by rfl) ⟨130520, by rfl⟩ : syracuseStep 696109 = 261041) (by norm_num)
theorem B794437 : Blo 546805 794437 := bbase (se 4 (by rfl) ⟨74478, by rfl⟩ : syracuseStep 794437 = 148957) (by norm_num)
theorem B4988789 : Blo 546805 4988789 := bbase (se 5 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 4988789 = 467699) (by norm_num)
theorem B925573 : Blo 546805 925573 := bbase (se 4 (by rfl) ⟨86772, by rfl⟩ : syracuseStep 925573 = 173545) (by norm_num)
theorem B696205 : Blo 546805 696205 := bbase (se 3 (by rfl) ⟨130538, by rfl⟩ : syracuseStep 696205 = 261077) (by norm_num)
theorem B2957269 : Blo 546805 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B925661 : Blo 546805 925661 := bbase (se 3 (by rfl) ⟨173561, by rfl⟩ : syracuseStep 925661 = 347123) (by norm_num)
theorem B991205 : Blo 546805 991205 := bbase (se 4 (by rfl) ⟨92925, by rfl⟩ : syracuseStep 991205 = 185851) (by norm_num)
theorem B696377 : Blo 546805 696377 := bbase (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) (by norm_num)
theorem B925789 : Blo 546805 925789 := bbase (se 3 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 925789 = 347171) (by norm_num)
theorem B696433 : Blo 546805 696433 := bbase (se 2 (by rfl) ⟨261162, by rfl⟩ : syracuseStep 696433 = 522325) (by norm_num)
theorem B1384573 : Blo 546805 1384573 := bbase (se 3 (by rfl) ⟨259607, by rfl⟩ : syracuseStep 1384573 = 519215) (by norm_num)
theorem B1319069 : Blo 546805 1319069 := bbase (se 3 (by rfl) ⟨247325, by rfl⟩ : syracuseStep 1319069 = 494651) (by norm_num)
theorem B925877 : Blo 546805 925877 := bbase (se 5 (by rfl) ⟨43400, by rfl⟩ : syracuseStep 925877 = 86801) (by norm_num)
theorem B696529 : Blo 546805 696529 := bbase (se 2 (by rfl) ⟨261198, by rfl⟩ : syracuseStep 696529 = 522397) (by norm_num)
theorem B1384685 : Blo 546805 1384685 := bbase (se 3 (by rfl) ⟨259628, by rfl⟩ : syracuseStep 1384685 = 519257) (by norm_num)
theorem B926005 : Blo 546805 926005 := bbase (se 5 (by rfl) ⟨43406, by rfl⟩ : syracuseStep 926005 = 86813) (by norm_num)
theorem B1253693 : Blo 546805 1253693 := bbase (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) (by norm_num)
theorem B696701 : Blo 546805 696701 := bbase (se 3 (by rfl) ⟨130631, by rfl⟩ : syracuseStep 696701 = 261263) (by norm_num)
theorem B926093 : Blo 546805 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B1384877 : Blo 546805 1384877 := bbase (se 3 (by rfl) ⟨259664, by rfl⟩ : syracuseStep 1384877 = 519329) (by norm_num)
theorem B696757 : Blo 546805 696757 := bbase (se 5 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 696757 = 65321) (by norm_num)
theorem B926221 : Blo 546805 926221 := bbase (se 3 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 926221 = 347333) (by norm_num)
theorem B696853 : Blo 546805 696853 := bbase (se 6 (by rfl) ⟨16332, by rfl⟩ : syracuseStep 696853 = 32665) (by norm_num)
theorem B926309 : Blo 546805 926309 := bbase (se 4 (by rfl) ⟨86841, by rfl⟩ : syracuseStep 926309 = 173683) (by norm_num)
theorem B697025 : Blo 546805 697025 := bbase (se 2 (by rfl) ⟨261384, by rfl⟩ : syracuseStep 697025 = 522769) (by norm_num)
theorem B926437 : Blo 546805 926437 := bbase (se 4 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 926437 = 173707) (by norm_num)
theorem B697081 : Blo 546805 697081 := bbase (se 2 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 697081 = 522811) (by norm_num)
theorem B1385221 : Blo 546805 1385221 := bbase (se 4 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 1385221 = 259729) (by norm_num)
theorem B926525 : Blo 546805 926525 := bbase (se 3 (by rfl) ⟨173723, by rfl⟩ : syracuseStep 926525 = 347447) (by norm_num)
theorem B1385333 : Blo 546805 1385333 := bbase (se 5 (by rfl) ⟨64937, by rfl⟩ : syracuseStep 1385333 = 129875) (by norm_num)
theorem B926653 : Blo 546805 926653 := bbase (se 3 (by rfl) ⟨173747, by rfl⟩ : syracuseStep 926653 = 347495) (by norm_num)
theorem B926741 : Blo 546805 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B1385525 : Blo 546805 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B926869 : Blo 546805 926869 := bbase (se 6 (by rfl) ⟨21723, by rfl⟩ : syracuseStep 926869 = 43447) (by norm_num)
theorem B2368693 : Blo 546805 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B926957 : Blo 546805 926957 := bbase (se 3 (by rfl) ⟨173804, by rfl⟩ : syracuseStep 926957 = 347609) (by norm_num)
theorem B927085 : Blo 546805 927085 := bbase (se 3 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 927085 = 347657) (by norm_num)
theorem B1385869 : Blo 546805 1385869 := bbase (se 3 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 1385869 = 519701) (by norm_num)
theorem B927173 : Blo 546805 927173 := bbase (se 4 (by rfl) ⟨86922, by rfl⟩ : syracuseStep 927173 = 173845) (by norm_num)
theorem B1385981 : Blo 546805 1385981 := bbase (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) (by norm_num)
theorem B927301 : Blo 546805 927301 := bbase (se 4 (by rfl) ⟨86934, by rfl⟩ : syracuseStep 927301 = 173869) (by norm_num)
theorem B927389 : Blo 546805 927389 := bbase (se 3 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 927389 = 347771) (by norm_num)
theorem B1386173 : Blo 546805 1386173 := bbase (se 3 (by rfl) ⟨259907, by rfl⟩ : syracuseStep 1386173 = 519815) (by norm_num)
theorem B927517 : Blo 546805 927517 := bbase (se 3 (by rfl) ⟨173909, by rfl⟩ : syracuseStep 927517 = 347819) (by norm_num)
theorem B1484581 : Blo 546805 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B1320781 : Blo 546805 1320781 := bbase (se 3 (by rfl) ⟨247646, by rfl⟩ : syracuseStep 1320781 = 495293) (by norm_num)
theorem B927605 : Blo 546805 927605 := bbase (se 5 (by rfl) ⟨43481, by rfl⟩ : syracuseStep 927605 = 86963) (by norm_num)
theorem B927733 : Blo 546805 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B1386517 : Blo 546805 1386517 := bbase (se 6 (by rfl) ⟨32496, by rfl⟩ : syracuseStep 1386517 = 64993) (by norm_num)
theorem B927821 : Blo 546805 927821 := bbase (se 3 (by rfl) ⟨173966, by rfl⟩ : syracuseStep 927821 = 347933) (by norm_num)
theorem B1386629 : Blo 546805 1386629 := bbase (se 4 (by rfl) ⟨129996, by rfl⟩ : syracuseStep 1386629 = 259993) (by norm_num)
theorem B927949 : Blo 546805 927949 := bbase (se 3 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 927949 = 347981) (by norm_num)
theorem B1583381 : Blo 546805 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B928037 : Blo 546805 928037 := bbase (se 4 (by rfl) ⟨87003, by rfl⟩ : syracuseStep 928037 = 174007) (by norm_num)
theorem B1845557 : Blo 546805 1845557 := bbase (se 5 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 1845557 = 173021) (by norm_num)
theorem B1386821 : Blo 546805 1386821 := bbase (se 4 (by rfl) ⟨130014, by rfl⟩ : syracuseStep 1386821 = 260029) (by norm_num)
theorem B9382229 : Blo 546805 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B928165 : Blo 546805 928165 := bbase (se 4 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 928165 = 174031) (by norm_num)
theorem B1321397 : Blo 546805 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B928253 : Blo 546805 928253 := bbase (se 3 (by rfl) ⟨174047, by rfl⟩ : syracuseStep 928253 = 348095) (by norm_num)
theorem B4172309 : Blo 546805 4172309 := bbase (se 6 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 4172309 = 195577) (by norm_num)
theorem B928381 : Blo 546805 928381 := bbase (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) (by norm_num)
theorem B1387165 : Blo 546805 1387165 := bbase (se 3 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 1387165 = 520187) (by norm_num)
theorem B2337493 : Blo 546805 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B928469 : Blo 546805 928469 := bbase (se 7 (by rfl) ⟨10880, by rfl⟩ : syracuseStep 928469 = 21761) (by norm_num)
theorem B1845989 : Blo 546805 1845989 := bbase (se 4 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 1845989 = 346123) (by norm_num)
theorem B1780469 : Blo 546805 1780469 := bbase (se 5 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 1780469 = 166919) (by norm_num)
theorem B1387277 : Blo 546805 1387277 := bbase (se 3 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 1387277 = 520229) (by norm_num)
theorem B928597 : Blo 546805 928597 := bbase (se 9 (by rfl) ⟨2720, by rfl⟩ : syracuseStep 928597 = 5441) (by norm_num)
theorem B1321829 : Blo 546805 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B928685 : Blo 546805 928685 := bbase (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) (by norm_num)
theorem B1387469 : Blo 546805 1387469 := bbase (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) (by norm_num)
theorem B928813 : Blo 546805 928813 := bbase (se 3 (by rfl) ⟨174152, by rfl⟩ : syracuseStep 928813 = 348305) (by norm_num)
theorem B928901 : Blo 546805 928901 := bbase (se 4 (by rfl) ⟨87084, by rfl⟩ : syracuseStep 928901 = 174169) (by norm_num)
theorem B1846421 : Blo 546805 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B929029 : Blo 546805 929029 := bbase (se 4 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 929029 = 174193) (by norm_num)
theorem B1387813 : Blo 546805 1387813 := bbase (se 4 (by rfl) ⟨130107, by rfl⟩ : syracuseStep 1387813 = 260215) (by norm_num)
theorem B929117 : Blo 546805 929117 := bbase (se 3 (by rfl) ⟨174209, by rfl⟩ : syracuseStep 929117 = 348419) (by norm_num)
theorem B3943829 : Blo 546805 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B1387925 : Blo 546805 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B2633141 : Blo 546805 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1977797 : Blo 546805 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B601553 : Blo 546805 601553 := bbase (se 2 (by rfl) ⟨225582, by rfl⟩ : syracuseStep 601553 = 451165) (by norm_num)
theorem B929245 : Blo 546805 929245 := bbase (se 3 (by rfl) ⟨174233, by rfl⟩ : syracuseStep 929245 = 348467) (by norm_num)
theorem B6696469 : Blo 546805 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B929333 : Blo 546805 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B1846853 : Blo 546805 1846853 := bbase (se 4 (by rfl) ⟨173142, by rfl⟩ : syracuseStep 1846853 = 346285) (by norm_num)
theorem B1388117 : Blo 546805 1388117 := bbase (se 8 (by rfl) ⟨8133, by rfl⟩ : syracuseStep 1388117 = 16267) (by norm_num)
theorem B929461 : Blo 546805 929461 := bbase (se 5 (by rfl) ⟨43568, by rfl⟩ : syracuseStep 929461 = 87137) (by norm_num)
theorem B1781509 : Blo 546805 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B2633525 : Blo 546805 2633525 := bbase (se 5 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 2633525 = 246893) (by norm_num)
theorem B1388461 : Blo 546805 1388461 := bbase (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) (by norm_num)
theorem B1847285 : Blo 546805 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B2109445 : Blo 546805 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B1323029 : Blo 546805 1323029 := bbase (se 6 (by rfl) ⟨31008, by rfl⟩ : syracuseStep 1323029 = 62017) (by norm_num)
theorem B1388573 : Blo 546805 1388573 := bbase (se 3 (by rfl) ⟨260357, by rfl⟩ : syracuseStep 1388573 = 520715) (by norm_num)
theorem B1781813 : Blo 546805 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B2535509 : Blo 546805 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B1388765 : Blo 546805 1388765 := bbase (se 3 (by rfl) ⟨260393, by rfl⟩ : syracuseStep 1388765 = 520787) (by norm_num)
theorem B1847717 : Blo 546805 1847717 := bbase (se 4 (by rfl) ⟨173223, by rfl⟩ : syracuseStep 1847717 = 346447) (by norm_num)
theorem B3748373 : Blo 546805 3748373 := bbase (se 6 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 3748373 = 175705) (by norm_num)
theorem B1389109 : Blo 546805 1389109 := bbase (se 5 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 1389109 = 130229) (by norm_num)
theorem B1487413 : Blo 546805 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B2077285 : Blo 546805 2077285 := bbase (se 4 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 2077285 = 389491) (by norm_num)
theorem B1585781 : Blo 546805 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B1389221 : Blo 546805 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B668377 : Blo 546805 668377 := bbase (se 2 (by rfl) ⟨250641, by rfl⟩ : syracuseStep 668377 = 501283) (by norm_num)
theorem B1848149 : Blo 546805 1848149 := bbase (se 9 (by rfl) ⟨5414, by rfl⟩ : syracuseStep 1848149 = 10829) (by norm_num)
theorem B8926037 : Blo 546805 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B1389413 : Blo 546805 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1487717 : Blo 546805 1487717 := bbase (se 4 (by rfl) ⟨139473, by rfl⟩ : syracuseStep 1487717 = 278947) (by norm_num)
theorem B2077589 : Blo 546805 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B5288885 : Blo 546805 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B12530645 : Blo 546805 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1389757 : Blo 546805 1389757 := bbase (se 3 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 1389757 = 521159) (by norm_num)
theorem B1848581 : Blo 546805 1848581 := bbase (se 4 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 1848581 = 346609) (by norm_num)
theorem B1389869 : Blo 546805 1389869 := bbase (se 3 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 1389869 = 521201) (by norm_num)
theorem B832925 : Blo 546805 832925 := bbase (se 3 (by rfl) ⟨156173, by rfl⟩ : syracuseStep 832925 = 312347) (by norm_num)
theorem B1390061 : Blo 546805 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B669313 : Blo 546805 669313 := bbase (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) (by norm_num)
theorem B2340485 : Blo 546805 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B1849013 : Blo 546805 1849013 := bbase (se 5 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 1849013 = 173345) (by norm_num)
theorem B1390405 : Blo 546805 1390405 := bbase (se 4 (by rfl) ⟨130350, by rfl⟩ : syracuseStep 1390405 = 260701) (by norm_num)
theorem B4437845 : Blo 546805 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B1390517 : Blo 546805 1390517 := bbase (se 5 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 1390517 = 130361) (by norm_num)
theorem B1849445 : Blo 546805 1849445 := bbase (se 4 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 1849445 = 346771) (by norm_num)
theorem B1390709 : Blo 546805 1390709 := bbase (se 5 (by rfl) ⟨65189, by rfl⟩ : syracuseStep 1390709 = 130379) (by norm_num)
theorem B17742037 : Blo 546805 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B669917 : Blo 546805 669917 := bbase (se 3 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 669917 = 251219) (by norm_num)
theorem B833989 : Blo 546805 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B1391053 : Blo 546805 1391053 := bbase (se 3 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 1391053 = 521645) (by norm_num)
theorem B702985 : Blo 546805 702985 := bbase (se 2 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 702985 = 527239) (by norm_num)
theorem B1849877 : Blo 546805 1849877 := bbase (se 6 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 1849877 = 86713) (by norm_num)
theorem B703037 : Blo 546805 703037 := bbase (se 3 (by rfl) ⟨131819, by rfl⟩ : syracuseStep 703037 = 263639) (by norm_num)
theorem B1391165 : Blo 546805 1391165 := bbase (se 3 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 1391165 = 521687) (by norm_num)
theorem B2341493 : Blo 546805 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B1391357 : Blo 546805 1391357 := bbase (se 3 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 1391357 = 521759) (by norm_num)
theorem B1850309 : Blo 546805 1850309 := bbase (se 4 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 1850309 = 346933) (by norm_num)
theorem B2079701 : Blo 546805 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B703477 : Blo 546805 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B1391701 : Blo 546805 1391701 := bbase (se 8 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 1391701 = 16309) (by norm_num)
theorem B1752197 : Blo 546805 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B1391813 : Blo 546805 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B2079989 : Blo 546805 2079989 := bbase (se 5 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 2079989 = 194999) (by norm_num)
theorem B1850741 : Blo 546805 1850741 := bbase (se 5 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 1850741 = 173507) (by norm_num)
theorem B1392005 : Blo 546805 1392005 := bbase (se 4 (by rfl) ⟨130500, by rfl⟩ : syracuseStep 1392005 = 261001) (by norm_num)
theorem B998821 : Blo 546805 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B835157 : Blo 546805 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B2375333 : Blo 546805 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B1392349 : Blo 546805 1392349 := bbase (se 3 (by rfl) ⟨261065, by rfl⟩ : syracuseStep 1392349 = 522131) (by norm_num)
theorem B1851173 : Blo 546805 1851173 := bbase (se 4 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 1851173 = 347095) (by norm_num)
theorem B835381 : Blo 546805 835381 := bbase (se 5 (by rfl) ⟨39158, by rfl⟩ : syracuseStep 835381 = 78317) (by norm_num)
theorem B1392461 : Blo 546805 1392461 := bbase (se 3 (by rfl) ⟨261086, by rfl⟩ : syracuseStep 1392461 = 522173) (by norm_num)
theorem B2768741 : Blo 546805 2768741 := bbase (se 4 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 2768741 = 519139) (by norm_num)
theorem B1392653 : Blo 546805 1392653 := bbase (se 3 (by rfl) ⟨261122, by rfl⟩ : syracuseStep 1392653 = 522245) (by norm_num)
theorem B1753109 : Blo 546805 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B835661 : Blo 546805 835661 := bbase (se 3 (by rfl) ⟨156686, by rfl⟩ : syracuseStep 835661 = 313373) (by norm_num)
theorem B3129461 : Blo 546805 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B1851605 : Blo 546805 1851605 := bbase (se 7 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 1851605 = 43397) (by norm_num)
theorem B2343269 : Blo 546805 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B1392997 : Blo 546805 1392997 := bbase (se 4 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 1392997 = 261187) (by norm_num)
theorem B2081173 : Blo 546805 2081173 := bbase (se 6 (by rfl) ⟨48777, by rfl⟩ : syracuseStep 2081173 = 97555) (by norm_num)
theorem B1393109 : Blo 546805 1393109 := bbase (se 7 (by rfl) ⟨16325, by rfl⟩ : syracuseStep 1393109 = 32651) (by norm_num)
theorem B1852037 : Blo 546805 1852037 := bbase (se 4 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 1852037 = 347257) (by norm_num)
theorem B1393301 : Blo 546805 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B2081477 : Blo 546805 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B2900821 : Blo 546805 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B836573 : Blo 546805 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B1393645 : Blo 546805 1393645 := bbase (se 3 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 1393645 = 522617) (by norm_num)
theorem B1852469 : Blo 546805 1852469 := bbase (se 5 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 1852469 = 173669) (by norm_num)
theorem B705613 : Blo 546805 705613 := bbase (se 3 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 705613 = 264605) (by norm_num)
theorem B1557589 : Blo 546805 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B1393757 : Blo 546805 1393757 := bbase (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) (by norm_num)
theorem B2770037 : Blo 546805 2770037 := bbase (se 5 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 2770037 = 259691) (by norm_num)
theorem B1000669 : Blo 546805 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B1393949 : Blo 546805 1393949 := bbase (se 3 (by rfl) ⟨261365, by rfl⟩ : syracuseStep 1393949 = 522731) (by norm_num)
theorem B1754453 : Blo 546805 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B3523925 : Blo 546805 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B1852901 : Blo 546805 1852901 := bbase (se 4 (by rfl) ⟨173709, by rfl⟩ : syracuseStep 1852901 = 347419) (by norm_num)
theorem B1230317 : Blo 546805 1230317 := bbase (se 3 (by rfl) ⟨230684, by rfl⟩ : syracuseStep 1230317 = 461369) (by norm_num)
theorem B1230389 : Blo 546805 1230389 := bbase (se 5 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 1230389 = 115349) (by norm_num)
theorem B1230461 : Blo 546805 1230461 := bbase (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) (by norm_num)
theorem B1230533 : Blo 546805 1230533 := bbase (se 4 (by rfl) ⟨115362, by rfl⟩ : syracuseStep 1230533 = 230725) (by norm_num)
theorem B1230605 : Blo 546805 1230605 := bbase (se 3 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 1230605 = 461477) (by norm_num)
theorem B1230677 : Blo 546805 1230677 := bbase (se 9 (by rfl) ⟨3605, by rfl⟩ : syracuseStep 1230677 = 7211) (by norm_num)
theorem B1853333 : Blo 546805 1853333 := bbase (se 6 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 1853333 = 86875) (by norm_num)
theorem B1230749 : Blo 546805 1230749 := bbase (se 3 (by rfl) ⟨230765, by rfl⟩ : syracuseStep 1230749 = 461531) (by norm_num)
theorem B706469 : Blo 546805 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B1230821 : Blo 546805 1230821 := bbase (se 4 (by rfl) ⟨115389, by rfl⟩ : syracuseStep 1230821 = 230779) (by norm_num)
theorem B1230893 : Blo 546805 1230893 := bbase (se 3 (by rfl) ⟨230792, by rfl⟩ : syracuseStep 1230893 = 461585) (by norm_num)
theorem B1230965 : Blo 546805 1230965 := bbase (se 5 (by rfl) ⟨57701, by rfl⟩ : syracuseStep 1230965 = 115403) (by norm_num)
theorem B4180085 : Blo 546805 4180085 := bbase (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) (by norm_num)
theorem B1558693 : Blo 546805 1558693 := bbase (se 4 (by rfl) ⟨146127, by rfl⟩ : syracuseStep 1558693 = 292255) (by norm_num)
theorem B1231037 : Blo 546805 1231037 := bbase (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) (by norm_num)
theorem B1231109 : Blo 546805 1231109 := bbase (se 4 (by rfl) ⟨115416, by rfl⟩ : syracuseStep 1231109 = 230833) (by norm_num)
theorem B1853765 : Blo 546805 1853765 := bbase (se 4 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 1853765 = 347581) (by norm_num)
theorem B1231181 : Blo 546805 1231181 := bbase (se 3 (by rfl) ⟨230846, by rfl⟩ : syracuseStep 1231181 = 461693) (by norm_num)
theorem B2771333 : Blo 546805 2771333 := bbase (se 4 (by rfl) ⟨259812, by rfl⟩ : syracuseStep 2771333 = 519625) (by norm_num)
theorem B1231253 : Blo 546805 1231253 := bbase (se 6 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 1231253 = 57715) (by norm_num)
theorem B1231325 : Blo 546805 1231325 := bbase (se 3 (by rfl) ⟨230873, by rfl⟩ : syracuseStep 1231325 = 461747) (by norm_num)
theorem B1231397 : Blo 546805 1231397 := bbase (se 4 (by rfl) ⟨115443, by rfl⟩ : syracuseStep 1231397 = 230887) (by norm_num)
theorem B1231469 : Blo 546805 1231469 := bbase (se 3 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 1231469 = 461801) (by norm_num)
theorem B1231541 : Blo 546805 1231541 := bbase (se 5 (by rfl) ⟨57728, by rfl⟩ : syracuseStep 1231541 = 115457) (by norm_num)
theorem B1755877 : Blo 546805 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B1854197 : Blo 546805 1854197 := bbase (se 5 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 1854197 = 173831) (by norm_num)
theorem B1231613 : Blo 546805 1231613 := bbase (se 3 (by rfl) ⟨230927, by rfl⟩ : syracuseStep 1231613 = 461855) (by norm_num)
theorem B2083589 : Blo 546805 2083589 := bbase (se 4 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 2083589 = 390673) (by norm_num)
theorem B1231685 : Blo 546805 1231685 := bbase (se 4 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 1231685 = 230941) (by norm_num)
theorem B1428317 : Blo 546805 1428317 := bbase (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) (by norm_num)
theorem B2116469 : Blo 546805 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B1231757 : Blo 546805 1231757 := bbase (se 3 (by rfl) ⟨230954, by rfl⟩ : syracuseStep 1231757 = 461909) (by norm_num)
theorem B904133 : Blo 546805 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B1231829 : Blo 546805 1231829 := bbase (se 7 (by rfl) ⟨14435, by rfl⟩ : syracuseStep 1231829 = 28871) (by norm_num)
theorem B740333 : Blo 546805 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B1231901 : Blo 546805 1231901 := bbase (se 3 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 1231901 = 461963) (by norm_num)
theorem B2083877 : Blo 546805 2083877 := bbase (se 4 (by rfl) ⟨195363, by rfl⟩ : syracuseStep 2083877 = 390727) (by norm_num)
theorem B1231973 : Blo 546805 1231973 := bbase (se 4 (by rfl) ⟨115497, by rfl⟩ : syracuseStep 1231973 = 230995) (by norm_num)
theorem B1854629 : Blo 546805 1854629 := bbase (se 4 (by rfl) ⟨173871, by rfl⟩ : syracuseStep 1854629 = 347743) (by norm_num)
theorem B1232045 : Blo 546805 1232045 := bbase (se 3 (by rfl) ⟨231008, by rfl⟩ : syracuseStep 1232045 = 462017) (by norm_num)
theorem B1232117 : Blo 546805 1232117 := bbase (se 5 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 1232117 = 115511) (by norm_num)
theorem B1232189 : Blo 546805 1232189 := bbase (se 3 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 1232189 = 462071) (by norm_num)
theorem B1232261 : Blo 546805 1232261 := bbase (se 4 (by rfl) ⟨115524, by rfl⟩ : syracuseStep 1232261 = 231049) (by norm_num)
theorem B2641349 : Blo 546805 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B1232333 : Blo 546805 1232333 := bbase (se 3 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 1232333 = 462125) (by norm_num)
theorem B1232405 : Blo 546805 1232405 := bbase (se 6 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 1232405 = 57769) (by norm_num)
theorem B1855061 : Blo 546805 1855061 := bbase (se 8 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 1855061 = 21739) (by norm_num)
theorem B1232477 : Blo 546805 1232477 := bbase (se 3 (by rfl) ⟨231089, by rfl⟩ : syracuseStep 1232477 = 462179) (by norm_num)
theorem B1560197 : Blo 546805 1560197 := bbase (se 4 (by rfl) ⟨146268, by rfl⟩ : syracuseStep 1560197 = 292537) (by norm_num)
theorem B9981589 : Blo 546805 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B2772629 : Blo 546805 2772629 := bbase (se 6 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 2772629 = 129967) (by norm_num)
theorem B1232549 : Blo 546805 1232549 := bbase (se 4 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 1232549 = 231103) (by norm_num)
theorem B1232621 : Blo 546805 1232621 := bbase (se 3 (by rfl) ⟨231116, by rfl⟩ : syracuseStep 1232621 = 462233) (by norm_num)
theorem B1232693 : Blo 546805 1232693 := bbase (se 5 (by rfl) ⟨57782, by rfl⟩ : syracuseStep 1232693 = 115565) (by norm_num)
theorem B1232765 : Blo 546805 1232765 := bbase (se 3 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 1232765 = 462287) (by norm_num)
theorem B741253 : Blo 546805 741253 := bbase (se 4 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 741253 = 138985) (by norm_num)
theorem B1232837 : Blo 546805 1232837 := bbase (se 4 (by rfl) ⟨115578, by rfl⟩ : syracuseStep 1232837 = 231157) (by norm_num)
theorem B1855493 : Blo 546805 1855493 := bbase (se 4 (by rfl) ⟨173952, by rfl⟩ : syracuseStep 1855493 = 347905) (by norm_num)
theorem B1232909 : Blo 546805 1232909 := bbase (se 3 (by rfl) ⟨231170, by rfl⟩ : syracuseStep 1232909 = 462341) (by norm_num)
theorem B1232981 : Blo 546805 1232981 := bbase (se 8 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 1232981 = 14449) (by norm_num)
theorem B1233053 : Blo 546805 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B2085061 : Blo 546805 2085061 := bbase (se 4 (by rfl) ⟨195474, by rfl⟩ : syracuseStep 2085061 = 390949) (by norm_num)
theorem B1233125 : Blo 546805 1233125 := bbase (se 4 (by rfl) ⟨115605, by rfl⟩ : syracuseStep 1233125 = 231211) (by norm_num)
theorem B1757477 : Blo 546805 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B1233197 : Blo 546805 1233197 := bbase (se 3 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 1233197 = 462449) (by norm_num)
theorem B1233269 : Blo 546805 1233269 := bbase (se 5 (by rfl) ⟨57809, by rfl⟩ : syracuseStep 1233269 = 115619) (by norm_num)
theorem B1855925 : Blo 546805 1855925 := bbase (se 5 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 1855925 = 173993) (by norm_num)
theorem B1233341 : Blo 546805 1233341 := bbase (se 3 (by rfl) ⟨231251, by rfl⟩ : syracuseStep 1233341 = 462503) (by norm_num)
theorem B2085365 : Blo 546805 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B1233413 : Blo 546805 1233413 := bbase (se 4 (by rfl) ⟨115632, by rfl⟩ : syracuseStep 1233413 = 231265) (by norm_num)
theorem B2347541 : Blo 546805 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B2544149 : Blo 546805 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B1233485 : Blo 546805 1233485 := bbase (se 3 (by rfl) ⟨231278, by rfl⟩ : syracuseStep 1233485 = 462557) (by norm_num)
theorem B1168013 : Blo 546805 1168013 := bbase (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) (by norm_num)
theorem B1233557 : Blo 546805 1233557 := bbase (se 6 (by rfl) ⟨28911, by rfl⟩ : syracuseStep 1233557 = 57823) (by norm_num)
theorem B1233629 : Blo 546805 1233629 := bbase (se 3 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 1233629 = 462611) (by norm_num)
theorem B2806501 : Blo 546805 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B2249461 : Blo 546805 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B1233701 : Blo 546805 1233701 := bbase (se 4 (by rfl) ⟨115659, by rfl⟩ : syracuseStep 1233701 = 231319) (by norm_num)
theorem B1856357 : Blo 546805 1856357 := bbase (se 4 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 1856357 = 348067) (by norm_num)
theorem B1233773 : Blo 546805 1233773 := bbase (se 3 (by rfl) ⟨231332, by rfl⟩ : syracuseStep 1233773 = 462665) (by norm_num)
theorem B3756917 : Blo 546805 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B2773925 : Blo 546805 2773925 := bbase (se 4 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 2773925 = 520111) (by norm_num)
theorem B1233845 : Blo 546805 1233845 := bbase (se 5 (by rfl) ⟨57836, by rfl⟩ : syracuseStep 1233845 = 115673) (by norm_num)
theorem B1233917 : Blo 546805 1233917 := bbase (se 3 (by rfl) ⟨231359, by rfl⟩ : syracuseStep 1233917 = 462719) (by norm_num)
theorem B939037 : Blo 546805 939037 := bbase (se 3 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 939037 = 352139) (by norm_num)
theorem B1233989 : Blo 546805 1233989 := bbase (se 4 (by rfl) ⟨115686, by rfl⟩ : syracuseStep 1233989 = 231373) (by norm_num)
theorem B939133 : Blo 546805 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1234061 : Blo 546805 1234061 := bbase (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) (by norm_num)
theorem B1561781 : Blo 546805 1561781 := bbase (se 5 (by rfl) ⟨73208, by rfl⟩ : syracuseStep 1561781 = 146417) (by norm_num)
theorem B1234133 : Blo 546805 1234133 := bbase (se 7 (by rfl) ⟨14462, by rfl⟩ : syracuseStep 1234133 = 28925) (by norm_num)
theorem B742621 : Blo 546805 742621 := bbase (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) (by norm_num)
theorem B1856789 : Blo 546805 1856789 := bbase (se 6 (by rfl) ⟨43518, by rfl⟩ : syracuseStep 1856789 = 87037) (by norm_num)
theorem B1234205 : Blo 546805 1234205 := bbase (se 3 (by rfl) ⟨231413, by rfl⟩ : syracuseStep 1234205 = 462827) (by norm_num)
theorem B1234277 : Blo 546805 1234277 := bbase (se 4 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 1234277 = 231427) (by norm_num)
theorem B1758581 : Blo 546805 1758581 := bbase (se 5 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 1758581 = 164867) (by norm_num)
theorem B1234349 : Blo 546805 1234349 := bbase (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) (by norm_num)
theorem B1005037 : Blo 546805 1005037 := bbase (se 3 (by rfl) ⟨188444, by rfl⟩ : syracuseStep 1005037 = 376889) (by norm_num)
theorem B1234421 : Blo 546805 1234421 := bbase (se 5 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 1234421 = 115727) (by norm_num)
theorem B1168901 : Blo 546805 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B1234493 : Blo 546805 1234493 := bbase (se 3 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 1234493 = 462935) (by norm_num)
theorem B1234565 : Blo 546805 1234565 := bbase (se 4 (by rfl) ⟨115740, by rfl⟩ : syracuseStep 1234565 = 231481) (by norm_num)
theorem B1857221 : Blo 546805 1857221 := bbase (se 4 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 1857221 = 348229) (by norm_num)
theorem B1234637 : Blo 546805 1234637 := bbase (se 3 (by rfl) ⟨231494, by rfl⟩ : syracuseStep 1234637 = 462989) (by norm_num)
theorem B2971349 : Blo 546805 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B1169149 : Blo 546805 1169149 := bbase (se 3 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 1169149 = 438431) (by norm_num)
theorem B1234709 : Blo 546805 1234709 := bbase (se 6 (by rfl) ⟨28938, by rfl⟩ : syracuseStep 1234709 = 57877) (by norm_num)
theorem B612145 : Blo 546805 612145 := bbase (se 2 (by rfl) ⟨229554, by rfl⟩ : syracuseStep 612145 = 459109) (by norm_num)
theorem B1562453 : Blo 546805 1562453 := bbase (se 9 (by rfl) ⟨4577, by rfl⟩ : syracuseStep 1562453 = 9155) (by norm_num)
theorem B1234781 : Blo 546805 1234781 := bbase (se 3 (by rfl) ⟨231521, by rfl⟩ : syracuseStep 1234781 = 463043) (by norm_num)
theorem B1234853 : Blo 546805 1234853 := bbase (se 4 (by rfl) ⟨115767, by rfl⟩ : syracuseStep 1234853 = 231535) (by norm_num)
theorem B939989 : Blo 546805 939989 := bbase (se 7 (by rfl) ⟨11015, by rfl⟩ : syracuseStep 939989 = 22031) (by norm_num)
theorem B1234925 : Blo 546805 1234925 := bbase (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) (by norm_num)
theorem B1234997 : Blo 546805 1234997 := bbase (se 5 (by rfl) ⟨57890, by rfl⟩ : syracuseStep 1234997 = 115781) (by norm_num)
theorem B1857653 : Blo 546805 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B1235069 : Blo 546805 1235069 := bbase (se 3 (by rfl) ⟨231575, by rfl⟩ : syracuseStep 1235069 = 463151) (by norm_num)
theorem B2775221 : Blo 546805 2775221 := bbase (se 5 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 2775221 = 260177) (by norm_num)
theorem B1235141 : Blo 546805 1235141 := bbase (se 4 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 1235141 = 231589) (by norm_num)
theorem B1169653 : Blo 546805 1169653 := bbase (se 5 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 1169653 = 109655) (by norm_num)
theorem B1562885 : Blo 546805 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B2349317 : Blo 546805 2349317 := bbase (se 4 (by rfl) ⟨220248, by rfl⟩ : syracuseStep 2349317 = 440497) (by norm_num)
theorem B1235213 : Blo 546805 1235213 := bbase (se 3 (by rfl) ⟨231602, by rfl⟩ : syracuseStep 1235213 = 463205) (by norm_num)
theorem B1235285 : Blo 546805 1235285 := bbase (se 10 (by rfl) ⟨1809, by rfl⟩ : syracuseStep 1235285 = 3619) (by norm_num)
theorem B5003669 : Blo 546805 5003669 := bbase (se 6 (by rfl) ⟨117273, by rfl⟩ : syracuseStep 5003669 = 234547) (by norm_num)
theorem B1235357 : Blo 546805 1235357 := bbase (se 3 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 1235357 = 463259) (by norm_num)
theorem B1038757 : Blo 546805 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B1235429 : Blo 546805 1235429 := bbase (se 4 (by rfl) ⟨115821, by rfl⟩ : syracuseStep 1235429 = 231643) (by norm_num)
theorem B2349557 : Blo 546805 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B1858085 : Blo 546805 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B1235501 : Blo 546805 1235501 := bbase (se 3 (by rfl) ⟨231656, by rfl⟩ : syracuseStep 1235501 = 463313) (by norm_num)
theorem B1038901 : Blo 546805 1038901 := bbase (se 5 (by rfl) ⟨48698, by rfl⟩ : syracuseStep 1038901 = 97397) (by norm_num)
theorem B2087477 : Blo 546805 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B744005 : Blo 546805 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B940645 : Blo 546805 940645 := bbase (se 4 (by rfl) ⟨88185, by rfl⟩ : syracuseStep 940645 = 176371) (by norm_num)
theorem B1235573 : Blo 546805 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B1235645 : Blo 546805 1235645 := bbase (se 3 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 1235645 = 463367) (by norm_num)
theorem B1039061 : Blo 546805 1039061 := bbase (se 7 (by rfl) ⟨12176, by rfl⟩ : syracuseStep 1039061 = 24353) (by norm_num)
theorem B1235717 : Blo 546805 1235717 := bbase (se 4 (by rfl) ⟨115848, by rfl⟩ : syracuseStep 1235717 = 231697) (by norm_num)
theorem B1235789 : Blo 546805 1235789 := bbase (se 3 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 1235789 = 463421) (by norm_num)
theorem B4447061 : Blo 546805 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2087765 : Blo 546805 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1039205 : Blo 546805 1039205 := bbase (se 4 (by rfl) ⟨97425, by rfl⟩ : syracuseStep 1039205 = 194851) (by norm_num)
theorem B1235861 : Blo 546805 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B1858517 : Blo 546805 1858517 := bbase (se 7 (by rfl) ⟨21779, by rfl⟩ : syracuseStep 1858517 = 43559) (by norm_num)
theorem B1235933 : Blo 546805 1235933 := bbase (se 3 (by rfl) ⟨231737, by rfl⟩ : syracuseStep 1235933 = 463475) (by norm_num)
theorem B1563637 : Blo 546805 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B1236005 : Blo 546805 1236005 := bbase (se 4 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 1236005 = 231751) (by norm_num)
theorem B1170541 : Blo 546805 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B1236077 : Blo 546805 1236077 := bbase (se 3 (by rfl) ⟨231764, by rfl⟩ : syracuseStep 1236077 = 463529) (by norm_num)
theorem B1039493 : Blo 546805 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B842933 : Blo 546805 842933 := bbase (se 5 (by rfl) ⟨39512, by rfl⟩ : syracuseStep 842933 = 79025) (by norm_num)
theorem B1236149 : Blo 546805 1236149 := bbase (se 5 (by rfl) ⟨57944, by rfl⟩ : syracuseStep 1236149 = 115889) (by norm_num)
theorem B1760501 : Blo 546805 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1236221 : Blo 546805 1236221 := bbase (se 3 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 1236221 = 463583) (by norm_num)
theorem B1039645 : Blo 546805 1039645 := bbase (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) (by norm_num)
theorem B5266741 : Blo 546805 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B1236293 : Blo 546805 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B1858949 : Blo 546805 1858949 := bbase (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) (by norm_num)
theorem B1236365 : Blo 546805 1236365 := bbase (se 3 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 1236365 = 463637) (by norm_num)
theorem B2776517 : Blo 546805 2776517 := bbase (se 4 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 2776517 = 520597) (by norm_num)
theorem B1236437 : Blo 546805 1236437 := bbase (se 7 (by rfl) ⟨14489, by rfl⟩ : syracuseStep 1236437 = 28979) (by norm_num)
theorem B1269245 : Blo 546805 1269245 := bbase (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) (by norm_num)
theorem B1236509 : Blo 546805 1236509 := bbase (se 3 (by rfl) ⟨231845, by rfl⟩ : syracuseStep 1236509 = 463691) (by norm_num)
theorem B4677173 : Blo 546805 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B1334845 : Blo 546805 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B1039949 : Blo 546805 1039949 := bbase (se 3 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 1039949 = 389981) (by norm_num)
theorem B1171037 : Blo 546805 1171037 := bbase (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) (by norm_num)
theorem B1236581 : Blo 546805 1236581 := bbase (se 4 (by rfl) ⟨115929, by rfl⟩ : syracuseStep 1236581 = 231859) (by norm_num)
theorem B1236653 : Blo 546805 1236653 := bbase (se 3 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 1236653 = 463745) (by norm_num)
theorem B876253 : Blo 546805 876253 := bbase (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) (by norm_num)
theorem B1335005 : Blo 546805 1335005 := bbase (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) (by norm_num)
theorem B1236725 : Blo 546805 1236725 := bbase (se 5 (by rfl) ⟨57971, by rfl⟩ : syracuseStep 1236725 = 115943) (by norm_num)
theorem B876349 : Blo 546805 876349 := bbase (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) (by norm_num)
theorem B1236797 : Blo 546805 1236797 := bbase (se 3 (by rfl) ⟨231899, by rfl⟩ : syracuseStep 1236797 = 463799) (by norm_num)
theorem B1236869 : Blo 546805 1236869 := bbase (se 4 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 1236869 = 231913) (by norm_num)
theorem B1236941 : Blo 546805 1236941 := bbase (se 3 (by rfl) ⟨231926, by rfl⟩ : syracuseStep 1236941 = 463853) (by norm_num)
theorem B876509 : Blo 546805 876509 := bbase (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) (by norm_num)
theorem B2088949 : Blo 546805 2088949 := bbase (se 5 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 2088949 = 195839) (by norm_num)
theorem B1237013 : Blo 546805 1237013 := bbase (se 6 (by rfl) ⟨28992, by rfl⟩ : syracuseStep 1237013 = 57985) (by norm_num)
theorem B1237085 : Blo 546805 1237085 := bbase (se 3 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 1237085 = 463907) (by norm_num)
theorem B1237157 : Blo 546805 1237157 := bbase (se 4 (by rfl) ⟨115983, by rfl⟩ : syracuseStep 1237157 = 231967) (by norm_num)
theorem B1237229 : Blo 546805 1237229 := bbase (se 3 (by rfl) ⟨231980, by rfl⟩ : syracuseStep 1237229 = 463961) (by norm_num)
theorem B2089253 : Blo 546805 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B1237301 : Blo 546805 1237301 := bbase (se 5 (by rfl) ⟨57998, by rfl⟩ : syracuseStep 1237301 = 115997) (by norm_num)
theorem B1040701 : Blo 546805 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B1237373 : Blo 546805 1237373 := bbase (se 3 (by rfl) ⟨232007, by rfl⟩ : syracuseStep 1237373 = 464015) (by norm_num)
theorem B2974133 : Blo 546805 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B1237445 : Blo 546805 1237445 := bbase (se 4 (by rfl) ⟨116010, by rfl⟩ : syracuseStep 1237445 = 232021) (by norm_num)
theorem B1040845 : Blo 546805 1040845 := bbase (se 3 (by rfl) ⟨195158, by rfl⟩ : syracuseStep 1040845 = 390317) (by norm_num)
theorem B1171925 : Blo 546805 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B1237517 : Blo 546805 1237517 := bbase (se 3 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 1237517 = 464069) (by norm_num)
theorem B1172045 : Blo 546805 1172045 := bbase (se 3 (by rfl) ⟨219758, by rfl⟩ : syracuseStep 1172045 = 439517) (by norm_num)
theorem B1237589 : Blo 546805 1237589 := bbase (se 8 (by rfl) ⟨7251, by rfl⟩ : syracuseStep 1237589 = 14503) (by norm_num)
theorem B1041005 : Blo 546805 1041005 := bbase (se 3 (by rfl) ⟨195188, by rfl⟩ : syracuseStep 1041005 = 390377) (by norm_num)
theorem B1761925 : Blo 546805 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B1237661 : Blo 546805 1237661 := bbase (se 3 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 1237661 = 464123) (by norm_num)
theorem B2777813 : Blo 546805 2777813 := bbase (se 7 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 2777813 = 65105) (by norm_num)
theorem B1237733 : Blo 546805 1237733 := bbase (se 4 (by rfl) ⟨116037, by rfl⟩ : syracuseStep 1237733 = 232075) (by norm_num)
theorem B2351845 : Blo 546805 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B779005 : Blo 546805 779005 := bbase (se 3 (by rfl) ⟨146063, by rfl⟩ : syracuseStep 779005 = 292127) (by norm_num)
theorem B1041149 : Blo 546805 1041149 := bbase (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) (by norm_num)
theorem B615181 : Blo 546805 615181 := bbase (se 3 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 615181 = 230693) (by norm_num)
theorem B1237805 : Blo 546805 1237805 := bbase (se 3 (by rfl) ⟨232088, by rfl⟩ : syracuseStep 1237805 = 464177) (by norm_num)
theorem B615217 : Blo 546805 615217 := bbase (se 2 (by rfl) ⟨230706, by rfl⟩ : syracuseStep 615217 = 461413) (by norm_num)
theorem B615253 : Blo 546805 615253 := bbase (se 9 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 615253 = 3605) (by norm_num)
theorem B1663829 : Blo 546805 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B1270613 : Blo 546805 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B1237877 : Blo 546805 1237877 := bbase (se 5 (by rfl) ⟨58025, by rfl⟩ : syracuseStep 1237877 = 116051) (by norm_num)
theorem B615289 : Blo 546805 615289 := bbase (se 2 (by rfl) ⟨230733, by rfl⟩ : syracuseStep 615289 = 461467) (by norm_num)
theorem B615325 : Blo 546805 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B1237949 : Blo 546805 1237949 := bbase (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) (by norm_num)
theorem B615361 : Blo 546805 615361 := bbase (se 2 (by rfl) ⟨230760, by rfl⟩ : syracuseStep 615361 = 461521) (by norm_num)
theorem B615397 : Blo 546805 615397 := bbase (se 4 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 615397 = 115387) (by norm_num)
theorem B1238021 : Blo 546805 1238021 := bbase (se 4 (by rfl) ⟨116064, by rfl⟩ : syracuseStep 1238021 = 232129) (by norm_num)
theorem B615433 : Blo 546805 615433 := bbase (se 2 (by rfl) ⟨230787, by rfl⟩ : syracuseStep 615433 = 461575) (by norm_num)
theorem B1041437 : Blo 546805 1041437 := bbase (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) (by norm_num)
theorem B615469 : Blo 546805 615469 := bbase (se 3 (by rfl) ⟨115400, by rfl⟩ : syracuseStep 615469 = 230801) (by norm_num)
theorem B877637 : Blo 546805 877637 := bbase (se 4 (by rfl) ⟨82278, by rfl⟩ : syracuseStep 877637 = 164557) (by norm_num)
theorem B1762373 : Blo 546805 1762373 := bbase (se 4 (by rfl) ⟨165222, by rfl⟩ : syracuseStep 1762373 = 330445) (by norm_num)
theorem B1238093 : Blo 546805 1238093 := bbase (se 3 (by rfl) ⟨232142, by rfl⟩ : syracuseStep 1238093 = 464285) (by norm_num)
theorem B615505 : Blo 546805 615505 := bbase (se 2 (by rfl) ⟨230814, by rfl⟩ : syracuseStep 615505 = 461629) (by norm_num)
theorem B615541 : Blo 546805 615541 := bbase (se 5 (by rfl) ⟨28853, by rfl⟩ : syracuseStep 615541 = 57707) (by norm_num)
theorem B1238165 : Blo 546805 1238165 := bbase (se 6 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 1238165 = 58039) (by norm_num)
theorem B615577 : Blo 546805 615577 := bbase (se 2 (by rfl) ⟨230841, by rfl⟩ : syracuseStep 615577 = 461683) (by norm_num)
theorem B1041589 : Blo 546805 1041589 := bbase (se 5 (by rfl) ⟨48824, by rfl⟩ : syracuseStep 1041589 = 97649) (by norm_num)
theorem B615613 : Blo 546805 615613 := bbase (se 3 (by rfl) ⟨115427, by rfl⟩ : syracuseStep 615613 = 230855) (by norm_num)
theorem B1172677 : Blo 546805 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B1238237 : Blo 546805 1238237 := bbase (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) (by norm_num)
theorem B615649 : Blo 546805 615649 := bbase (se 2 (by rfl) ⟨230868, by rfl⟩ : syracuseStep 615649 = 461737) (by norm_num)
theorem B615685 : Blo 546805 615685 := bbase (se 4 (by rfl) ⟨57720, by rfl⟩ : syracuseStep 615685 = 115441) (by norm_num)
theorem B1238309 : Blo 546805 1238309 := bbase (se 4 (by rfl) ⟨116091, by rfl⟩ : syracuseStep 1238309 = 232183) (by norm_num)
theorem B615721 : Blo 546805 615721 := bbase (se 2 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 615721 = 461791) (by norm_num)
theorem B615757 : Blo 546805 615757 := bbase (se 3 (by rfl) ⟨115454, by rfl⟩ : syracuseStep 615757 = 230909) (by norm_num)
theorem B1238381 : Blo 546805 1238381 := bbase (se 3 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 1238381 = 464393) (by norm_num)
theorem B615793 : Blo 546805 615793 := bbase (se 2 (by rfl) ⟨230922, by rfl⟩ : syracuseStep 615793 = 461845) (by norm_num)
theorem B615829 : Blo 546805 615829 := bbase (se 6 (by rfl) ⟨14433, by rfl⟩ : syracuseStep 615829 = 28867) (by norm_num)
theorem B1238453 : Blo 546805 1238453 := bbase (se 5 (by rfl) ⟨58052, by rfl⟩ : syracuseStep 1238453 = 116105) (by norm_num)
theorem B615865 : Blo 546805 615865 := bbase (se 2 (by rfl) ⟨230949, by rfl⟩ : syracuseStep 615865 = 461899) (by norm_num)
theorem B714169 : Blo 546805 714169 := bbase (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) (by norm_num)
theorem B615901 : Blo 546805 615901 := bbase (se 3 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 615901 = 230963) (by norm_num)
theorem B1041893 : Blo 546805 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B1238525 : Blo 546805 1238525 := bbase (se 3 (by rfl) ⟨232223, by rfl⟩ : syracuseStep 1238525 = 464447) (by norm_num)
theorem B615937 : Blo 546805 615937 := bbase (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) (by norm_num)
theorem B779797 : Blo 546805 779797 := bbase (se 6 (by rfl) ⟨18276, by rfl⟩ : syracuseStep 779797 = 36553) (by norm_num)
theorem B615973 : Blo 546805 615973 := bbase (se 4 (by rfl) ⟨57747, by rfl⟩ : syracuseStep 615973 = 115495) (by norm_num)
theorem B878149 : Blo 546805 878149 := bbase (se 4 (by rfl) ⟨82326, by rfl⟩ : syracuseStep 878149 = 164653) (by norm_num)
theorem B1238597 : Blo 546805 1238597 := bbase (se 4 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 1238597 = 232237) (by norm_num)
theorem B616009 : Blo 546805 616009 := bbase (se 2 (by rfl) ⟨231003, by rfl⟩ : syracuseStep 616009 = 462007) (by norm_num)
theorem B616045 : Blo 546805 616045 := bbase (se 3 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 616045 = 231017) (by norm_num)
theorem B1238669 : Blo 546805 1238669 := bbase (se 3 (by rfl) ⟨232250, by rfl⟩ : syracuseStep 1238669 = 464501) (by norm_num)
theorem B616081 : Blo 546805 616081 := bbase (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) (by norm_num)
theorem B1926805 : Blo 546805 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B1336981 : Blo 546805 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B616117 : Blo 546805 616117 := bbase (se 5 (by rfl) ⟨28880, by rfl⟩ : syracuseStep 616117 = 57761) (by norm_num)
theorem B1238741 : Blo 546805 1238741 := bbase (se 7 (by rfl) ⟨14516, by rfl⟩ : syracuseStep 1238741 = 29033) (by norm_num)
theorem B616153 : Blo 546805 616153 := bbase (se 2 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 616153 = 462115) (by norm_num)
theorem B616189 : Blo 546805 616189 := bbase (se 3 (by rfl) ⟨115535, by rfl⟩ : syracuseStep 616189 = 231071) (by norm_num)
theorem B1566485 : Blo 546805 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B1238813 : Blo 546805 1238813 := bbase (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) (by norm_num)
theorem B616225 : Blo 546805 616225 := bbase (se 2 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 616225 = 462169) (by norm_num)
theorem B616261 : Blo 546805 616261 := bbase (se 4 (by rfl) ⟨57774, by rfl⟩ : syracuseStep 616261 = 115549) (by norm_num)
theorem B780133 : Blo 546805 780133 := bbase (se 4 (by rfl) ⟨73137, by rfl⟩ : syracuseStep 780133 = 146275) (by norm_num)
theorem B1238885 : Blo 546805 1238885 := bbase (se 4 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 1238885 = 232291) (by norm_num)
theorem B616297 : Blo 546805 616297 := bbase (se 2 (by rfl) ⟨231111, by rfl⟩ : syracuseStep 616297 = 462223) (by norm_num)
theorem B616333 : Blo 546805 616333 := bbase (se 3 (by rfl) ⟨115562, by rfl⟩ : syracuseStep 616333 = 231125) (by norm_num)
theorem B1238957 : Blo 546805 1238957 := bbase (se 3 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 1238957 = 464609) (by norm_num)
theorem B616369 : Blo 546805 616369 := bbase (se 2 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 616369 = 462277) (by norm_num)
theorem B616405 : Blo 546805 616405 := bbase (se 7 (by rfl) ⟨7223, by rfl⟩ : syracuseStep 616405 = 14447) (by norm_num)
theorem B15820757 : Blo 546805 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B2779109 : Blo 546805 2779109 := bbase (se 4 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 2779109 = 521083) (by norm_num)
theorem B1239029 : Blo 546805 1239029 := bbase (se 5 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 1239029 = 116159) (by norm_num)
theorem B616441 : Blo 546805 616441 := bbase (se 2 (by rfl) ⟨231165, by rfl⟩ : syracuseStep 616441 = 462331) (by norm_num)
theorem B616477 : Blo 546805 616477 := bbase (se 3 (by rfl) ⟨115589, by rfl⟩ : syracuseStep 616477 = 231179) (by norm_num)
theorem B780349 : Blo 546805 780349 := bbase (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) (by norm_num)
theorem B1173565 : Blo 546805 1173565 := bbase (se 3 (by rfl) ⟨220043, by rfl⟩ : syracuseStep 1173565 = 440087) (by norm_num)
theorem B1239101 : Blo 546805 1239101 := bbase (se 3 (by rfl) ⟨232331, by rfl⟩ : syracuseStep 1239101 = 464663) (by norm_num)
theorem B616513 : Blo 546805 616513 := bbase (se 2 (by rfl) ⟨231192, by rfl⟩ : syracuseStep 616513 = 462385) (by norm_num)
theorem B616549 : Blo 546805 616549 := bbase (se 4 (by rfl) ⟨57801, by rfl⟩ : syracuseStep 616549 = 115603) (by norm_num)
theorem B1665157 : Blo 546805 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B1239173 : Blo 546805 1239173 := bbase (se 4 (by rfl) ⟨116172, by rfl⟩ : syracuseStep 1239173 = 232345) (by norm_num)
theorem B616585 : Blo 546805 616585 := bbase (se 2 (by rfl) ⟨231219, by rfl⟩ : syracuseStep 616585 = 462439) (by norm_num)
theorem B616621 : Blo 546805 616621 := bbase (se 3 (by rfl) ⟨115616, by rfl⟩ : syracuseStep 616621 = 231233) (by norm_num)
theorem B1173685 : Blo 546805 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1239245 : Blo 546805 1239245 := bbase (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) (by norm_num)
theorem B616657 : Blo 546805 616657 := bbase (se 2 (by rfl) ⟨231246, by rfl⟩ : syracuseStep 616657 = 462493) (by norm_num)
theorem B1042645 : Blo 546805 1042645 := bbase (se 7 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 1042645 = 24437) (by norm_num)
theorem B616693 : Blo 546805 616693 := bbase (se 5 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 616693 = 57815) (by norm_num)
theorem B616729 : Blo 546805 616729 := bbase (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) (by norm_num)
theorem B616765 : Blo 546805 616765 := bbase (se 3 (by rfl) ⟨115643, by rfl⟩ : syracuseStep 616765 = 231287) (by norm_num)
theorem B616801 : Blo 546805 616801 := bbase (se 2 (by rfl) ⟨231300, by rfl⟩ : syracuseStep 616801 = 462601) (by norm_num)
theorem B1042789 : Blo 546805 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B616837 : Blo 546805 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B616873 : Blo 546805 616873 := bbase (se 2 (by rfl) ⟨231327, by rfl⟩ : syracuseStep 616873 = 462655) (by norm_num)
theorem B780725 : Blo 546805 780725 := bbase (se 5 (by rfl) ⟨36596, by rfl⟩ : syracuseStep 780725 = 73193) (by norm_num)
theorem B1173941 : Blo 546805 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B616909 : Blo 546805 616909 := bbase (se 3 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 616909 = 231341) (by norm_num)
theorem B584177 : Blo 546805 584177 := bbase (se 2 (by rfl) ⟨219066, by rfl⟩ : syracuseStep 584177 = 438133) (by norm_num)
theorem B616945 : Blo 546805 616945 := bbase (se 2 (by rfl) ⟨231354, by rfl⟩ : syracuseStep 616945 = 462709) (by norm_num)
theorem B1042949 : Blo 546805 1042949 := bbase (se 4 (by rfl) ⟨97776, by rfl⟩ : syracuseStep 1042949 = 195553) (by norm_num)
theorem B616981 : Blo 546805 616981 := bbase (se 6 (by rfl) ⟨14460, by rfl⟩ : syracuseStep 616981 = 28921) (by norm_num)
theorem B879149 : Blo 546805 879149 := bbase (se 3 (by rfl) ⟨164840, by rfl⟩ : syracuseStep 879149 = 329681) (by norm_num)
theorem B617017 : Blo 546805 617017 := bbase (se 2 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 617017 = 462763) (by norm_num)
theorem B617053 : Blo 546805 617053 := bbase (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) (by norm_num)
theorem B617089 : Blo 546805 617089 := bbase (se 2 (by rfl) ⟨231408, by rfl⟩ : syracuseStep 617089 = 462817) (by norm_num)
theorem B1043093 : Blo 546805 1043093 := bbase (se 6 (by rfl) ⟨24447, by rfl⟩ : syracuseStep 1043093 = 48895) (by norm_num)
theorem B617125 : Blo 546805 617125 := bbase (se 4 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 617125 = 115711) (by norm_num)
theorem B879277 : Blo 546805 879277 := bbase (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) (by norm_num)
theorem B617161 : Blo 546805 617161 := bbase (se 2 (by rfl) ⟨231435, by rfl⟩ : syracuseStep 617161 = 462871) (by norm_num)
theorem B584425 : Blo 546805 584425 := bbase (se 2 (by rfl) ⟨219159, by rfl⟩ : syracuseStep 584425 = 438319) (by norm_num)
theorem B617197 : Blo 546805 617197 := bbase (se 3 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 617197 = 231449) (by norm_num)
theorem B879341 : Blo 546805 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B617233 : Blo 546805 617233 := bbase (se 2 (by rfl) ⟨231462, by rfl⟩ : syracuseStep 617233 = 462925) (by norm_num)
theorem B1108765 : Blo 546805 1108765 := bbase (se 3 (by rfl) ⟨207893, by rfl⟩ : syracuseStep 1108765 = 415787) (by norm_num)
theorem B617269 : Blo 546805 617269 := bbase (se 5 (by rfl) ⟨28934, by rfl⟩ : syracuseStep 617269 = 57869) (by norm_num)
theorem B617305 : Blo 546805 617305 := bbase (se 2 (by rfl) ⟨231489, by rfl⟩ : syracuseStep 617305 = 462979) (by norm_num)
theorem B617341 : Blo 546805 617341 := bbase (se 3 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 617341 = 231503) (by norm_num)
theorem B617377 : Blo 546805 617377 := bbase (se 2 (by rfl) ⟨231516, by rfl⟩ : syracuseStep 617377 = 463033) (by norm_num)
theorem B1043381 : Blo 546805 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B1567669 : Blo 546805 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B617413 : Blo 546805 617413 := bbase (se 4 (by rfl) ⟨57882, by rfl⟩ : syracuseStep 617413 = 115765) (by norm_num)
theorem B617449 : Blo 546805 617449 := bbase (se 2 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 617449 = 463087) (by norm_num)
theorem B617485 : Blo 546805 617485 := bbase (se 3 (by rfl) ⟨115778, by rfl⟩ : syracuseStep 617485 = 231557) (by norm_num)
theorem B617521 : Blo 546805 617521 := bbase (se 2 (by rfl) ⟨231570, by rfl⟩ : syracuseStep 617521 = 463141) (by norm_num)
theorem B1043533 : Blo 546805 1043533 := bbase (se 3 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 1043533 = 391325) (by norm_num)
theorem B617557 : Blo 546805 617557 := bbase (se 8 (by rfl) ⟨3618, by rfl⟩ : syracuseStep 617557 = 7237) (by norm_num)
theorem B1567829 : Blo 546805 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B617593 : Blo 546805 617593 := bbase (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) (by norm_num)
theorem B617629 : Blo 546805 617629 := bbase (se 3 (by rfl) ⟨115805, by rfl⟩ : syracuseStep 617629 = 231611) (by norm_num)
theorem B584869 : Blo 546805 584869 := bbase (se 4 (by rfl) ⟨54831, by rfl⟩ : syracuseStep 584869 = 109663) (by norm_num)
theorem B617665 : Blo 546805 617665 := bbase (se 2 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 617665 = 463249) (by norm_num)
theorem B1666261 : Blo 546805 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B584929 : Blo 546805 584929 := bbase (se 2 (by rfl) ⟨219348, by rfl⟩ : syracuseStep 584929 = 438697) (by norm_num)
theorem B617701 : Blo 546805 617701 := bbase (se 4 (by rfl) ⟨57909, by rfl⟩ : syracuseStep 617701 = 115819) (by norm_num)
theorem B2780405 : Blo 546805 2780405 := bbase (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) (by norm_num)
theorem B617737 : Blo 546805 617737 := bbase (se 2 (by rfl) ⟨231651, by rfl⟩ : syracuseStep 617737 = 463303) (by norm_num)
theorem B617773 : Blo 546805 617773 := bbase (se 3 (by rfl) ⟨115832, by rfl⟩ : syracuseStep 617773 = 231665) (by norm_num)
theorem B1174829 : Blo 546805 1174829 := bbase (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) (by norm_num)
theorem B1568069 : Blo 546805 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B617809 : Blo 546805 617809 := bbase (se 2 (by rfl) ⟨231678, by rfl⟩ : syracuseStep 617809 = 463357) (by norm_num)
theorem B4156757 : Blo 546805 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B617845 : Blo 546805 617845 := bbase (se 5 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 617845 = 57923) (by norm_num)
theorem B1043837 : Blo 546805 1043837 := bbase (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) (by norm_num)
theorem B7925141 : Blo 546805 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B617881 : Blo 546805 617881 := bbase (se 2 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 617881 = 463411) (by norm_num)
theorem B617917 : Blo 546805 617917 := bbase (se 3 (by rfl) ⟨115859, by rfl⟩ : syracuseStep 617917 = 231719) (by norm_num)
theorem B617953 : Blo 546805 617953 := bbase (se 2 (by rfl) ⟨231732, by rfl⟩ : syracuseStep 617953 = 463465) (by norm_num)
theorem B1338853 : Blo 546805 1338853 := bbase (se 4 (by rfl) ⟨125517, by rfl⟩ : syracuseStep 1338853 = 251035) (by norm_num)
theorem B617989 : Blo 546805 617989 := bbase (se 4 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 617989 = 115873) (by norm_num)
theorem B1568261 : Blo 546805 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B585245 : Blo 546805 585245 := bbase (se 3 (by rfl) ⟨109733, by rfl⟩ : syracuseStep 585245 = 219467) (by norm_num)
theorem B1175069 : Blo 546805 1175069 := bbase (se 3 (by rfl) ⟨220325, by rfl⟩ : syracuseStep 1175069 = 440651) (by norm_num)
theorem B847397 : Blo 546805 847397 := bbase (se 4 (by rfl) ⟨79443, by rfl⟩ : syracuseStep 847397 = 158887) (by norm_num)
theorem B618025 : Blo 546805 618025 := bbase (se 2 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 618025 = 463519) (by norm_num)
theorem B618061 : Blo 546805 618061 := bbase (se 3 (by rfl) ⟨115886, by rfl⟩ : syracuseStep 618061 = 231773) (by norm_num)
theorem B618097 : Blo 546805 618097 := bbase (se 2 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 618097 = 463573) (by norm_num)
theorem B618133 : Blo 546805 618133 := bbase (se 6 (by rfl) ⟨14487, by rfl⟩ : syracuseStep 618133 = 28975) (by norm_num)
theorem B1502885 : Blo 546805 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B618169 : Blo 546805 618169 := bbase (se 2 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 618169 = 463627) (by norm_num)
theorem B618205 : Blo 546805 618205 := bbase (se 3 (by rfl) ⟨115913, by rfl⟩ : syracuseStep 618205 = 231827) (by norm_num)
theorem B618241 : Blo 546805 618241 := bbase (se 2 (by rfl) ⟨231840, by rfl⟩ : syracuseStep 618241 = 463681) (by norm_num)
theorem B618277 : Blo 546805 618277 := bbase (se 4 (by rfl) ⟨57963, by rfl⟩ : syracuseStep 618277 = 115927) (by norm_num)
theorem B782149 : Blo 546805 782149 := bbase (se 4 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 782149 = 146653) (by norm_num)
theorem B618313 : Blo 546805 618313 := bbase (se 2 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 618313 = 463735) (by norm_num)
theorem B618349 : Blo 546805 618349 := bbase (se 3 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 618349 = 231881) (by norm_num)
theorem B618385 : Blo 546805 618385 := bbase (se 2 (by rfl) ⟨231894, by rfl⟩ : syracuseStep 618385 = 463789) (by norm_num)
theorem B1109909 : Blo 546805 1109909 := bbase (se 6 (by rfl) ⟨26013, by rfl⟩ : syracuseStep 1109909 = 52027) (by norm_num)
theorem B4747157 : Blo 546805 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B618421 : Blo 546805 618421 := bbase (se 5 (by rfl) ⟨28988, by rfl⟩ : syracuseStep 618421 = 57977) (by norm_num)
theorem B585689 : Blo 546805 585689 := bbase (se 2 (by rfl) ⟨219633, by rfl⟩ : syracuseStep 585689 = 439267) (by norm_num)
theorem B618457 : Blo 546805 618457 := bbase (se 2 (by rfl) ⟨231921, by rfl⟩ : syracuseStep 618457 = 463843) (by norm_num)
theorem B618493 : Blo 546805 618493 := bbase (se 3 (by rfl) ⟨115967, by rfl⟩ : syracuseStep 618493 = 231935) (by norm_num)
theorem B585749 : Blo 546805 585749 := bbase (se 6 (by rfl) ⟨13728, by rfl⟩ : syracuseStep 585749 = 27457) (by norm_num)
theorem B880661 : Blo 546805 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B1175573 : Blo 546805 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B1175581 : Blo 546805 1175581 := bbase (se 3 (by rfl) ⟨220421, by rfl⟩ : syracuseStep 1175581 = 440843) (by norm_num)
theorem B618529 : Blo 546805 618529 := bbase (se 2 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 618529 = 463897) (by norm_num)
theorem B618565 : Blo 546805 618565 := bbase (se 4 (by rfl) ⟨57990, by rfl⟩ : syracuseStep 618565 = 115981) (by norm_num)
theorem B913493 : Blo 546805 913493 := bbase (se 8 (by rfl) ⟨5352, by rfl⟩ : syracuseStep 913493 = 10705) (by norm_num)
theorem B618601 : Blo 546805 618601 := bbase (se 2 (by rfl) ⟨231975, by rfl⟩ : syracuseStep 618601 = 463951) (by norm_num)
theorem B1044589 : Blo 546805 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B618637 : Blo 546805 618637 := bbase (se 3 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 618637 = 231989) (by norm_num)
theorem B585877 : Blo 546805 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B880789 : Blo 546805 880789 := bbase (se 6 (by rfl) ⟨20643, by rfl⟩ : syracuseStep 880789 = 41287) (by norm_num)
theorem B618673 : Blo 546805 618673 := bbase (se 2 (by rfl) ⟨232002, by rfl⟩ : syracuseStep 618673 = 464005) (by norm_num)
theorem B618709 : Blo 546805 618709 := bbase (se 7 (by rfl) ⟨7250, by rfl⟩ : syracuseStep 618709 = 14501) (by norm_num)
theorem B618745 : Blo 546805 618745 := bbase (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) (by norm_num)
theorem B1044733 : Blo 546805 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B618781 : Blo 546805 618781 := bbase (se 3 (by rfl) ⟨116021, by rfl⟩ : syracuseStep 618781 = 232043) (by norm_num)
theorem B618817 : Blo 546805 618817 := bbase (se 2 (by rfl) ⟨232056, by rfl⟩ : syracuseStep 618817 = 464113) (by norm_num)
theorem B618853 : Blo 546805 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B618889 : Blo 546805 618889 := bbase (se 2 (by rfl) ⟨232083, by rfl⟩ : syracuseStep 618889 = 464167) (by norm_num)
theorem B782741 : Blo 546805 782741 := bbase (se 6 (by rfl) ⟨18345, by rfl⟩ : syracuseStep 782741 = 36691) (by norm_num)
theorem B1044893 : Blo 546805 1044893 := bbase (se 3 (by rfl) ⟨195917, by rfl⟩ : syracuseStep 1044893 = 391835) (by norm_num)
theorem B618925 : Blo 546805 618925 := bbase (se 3 (by rfl) ⟨116048, by rfl⟩ : syracuseStep 618925 = 232097) (by norm_num)
theorem B618961 : Blo 546805 618961 := bbase (se 2 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 618961 = 464221) (by norm_num)
theorem B782821 : Blo 546805 782821 := bbase (se 4 (by rfl) ⟨73389, by rfl⟩ : syracuseStep 782821 = 146779) (by norm_num)
theorem B618997 : Blo 546805 618997 := bbase (se 5 (by rfl) ⟨29015, by rfl⟩ : syracuseStep 618997 = 58031) (by norm_num)
theorem B2781701 : Blo 546805 2781701 := bbase (se 4 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 2781701 = 521569) (by norm_num)
theorem B619033 : Blo 546805 619033 := bbase (se 2 (by rfl) ⟨232137, by rfl⟩ : syracuseStep 619033 = 464275) (by norm_num)
theorem B1045037 : Blo 546805 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B619069 : Blo 546805 619069 := bbase (se 3 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 619069 = 232151) (by norm_num)
theorem B586321 : Blo 546805 586321 := bbase (se 2 (by rfl) ⟨219870, by rfl⟩ : syracuseStep 586321 = 439741) (by norm_num)
theorem B782941 : Blo 546805 782941 := bbase (se 3 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 782941 = 293603) (by norm_num)
theorem B619105 : Blo 546805 619105 := bbase (se 2 (by rfl) ⟨232164, by rfl⟩ : syracuseStep 619105 = 464329) (by norm_num)
theorem B619141 : Blo 546805 619141 := bbase (se 4 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 619141 = 116089) (by norm_num)
theorem B619177 : Blo 546805 619177 := bbase (se 2 (by rfl) ⟨232191, by rfl⟩ : syracuseStep 619177 = 464383) (by norm_num)
theorem B783037 : Blo 546805 783037 := bbase (se 3 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 783037 = 293639) (by norm_num)
theorem B586441 : Blo 546805 586441 := bbase (se 2 (by rfl) ⟨219915, by rfl⟩ : syracuseStep 586441 = 439831) (by norm_num)
theorem B619213 : Blo 546805 619213 := bbase (se 3 (by rfl) ⟨116102, by rfl⟩ : syracuseStep 619213 = 232205) (by norm_num)
theorem B619249 : Blo 546805 619249 := bbase (se 2 (by rfl) ⟨232218, by rfl⟩ : syracuseStep 619249 = 464437) (by norm_num)
theorem B619285 : Blo 546805 619285 := bbase (se 6 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 619285 = 29029) (by norm_num)
theorem B619321 : Blo 546805 619321 := bbase (se 2 (by rfl) ⟨232245, by rfl⟩ : syracuseStep 619321 = 464491) (by norm_num)
theorem B1045325 : Blo 546805 1045325 := bbase (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) (by norm_num)
theorem B619357 : Blo 546805 619357 := bbase (se 3 (by rfl) ⟨116129, by rfl⟩ : syracuseStep 619357 = 232259) (by norm_num)
theorem B619393 : Blo 546805 619393 := bbase (se 2 (by rfl) ⟨232272, by rfl⟩ : syracuseStep 619393 = 464545) (by norm_num)
theorem B619429 : Blo 546805 619429 := bbase (se 4 (by rfl) ⟨58071, by rfl⟩ : syracuseStep 619429 = 116143) (by norm_num)
theorem B881597 : Blo 546805 881597 := bbase (se 3 (by rfl) ⟨165299, by rfl⟩ : syracuseStep 881597 = 330599) (by norm_num)
theorem B586693 : Blo 546805 586693 := bbase (se 4 (by rfl) ⟨55002, by rfl⟩ : syracuseStep 586693 = 110005) (by norm_num)
theorem B586697 : Blo 546805 586697 := bbase (se 2 (by rfl) ⟨220011, by rfl⟩ : syracuseStep 586697 = 440023) (by norm_num)
theorem B619465 : Blo 546805 619465 := bbase (se 2 (by rfl) ⟨232299, by rfl⟩ : syracuseStep 619465 = 464599) (by norm_num)
theorem B1045477 : Blo 546805 1045477 := bbase (se 4 (by rfl) ⟨98013, by rfl⟩ : syracuseStep 1045477 = 196027) (by norm_num)
theorem B619501 : Blo 546805 619501 := bbase (se 3 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 619501 = 232313) (by norm_num)
theorem B619537 : Blo 546805 619537 := bbase (se 2 (by rfl) ⟨232326, by rfl⟩ : syracuseStep 619537 = 464653) (by norm_num)
theorem B619573 : Blo 546805 619573 := bbase (se 5 (by rfl) ⟨29042, by rfl⟩ : syracuseStep 619573 = 58085) (by norm_num)
theorem B619609 : Blo 546805 619609 := bbase (se 2 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 619609 = 464707) (by norm_num)
theorem B619645 : Blo 546805 619645 := bbase (se 3 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 619645 = 232367) (by norm_num)
theorem B783533 : Blo 546805 783533 := bbase (se 3 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 783533 = 293825) (by norm_num)
theorem B881885 : Blo 546805 881885 := bbase (se 3 (by rfl) ⟨165353, by rfl⟩ : syracuseStep 881885 = 330707) (by norm_num)
theorem B2258405 : Blo 546805 2258405 := bbase (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) (by norm_num)
theorem B587261 : Blo 546805 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B6256277 : Blo 546805 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B1111733 : Blo 546805 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B587449 : Blo 546805 587449 := bbase (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) (by norm_num)
theorem B784085 : Blo 546805 784085 := bbase (se 7 (by rfl) ⟨9188, by rfl⟩ : syracuseStep 784085 = 18377) (by norm_num)
theorem B2782997 : Blo 546805 2782997 := bbase (se 6 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 2782997 = 130453) (by norm_num)
theorem B554845 : Blo 546805 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B1341373 : Blo 546805 1341373 := bbase (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) (by norm_num)
theorem B1669157 : Blo 546805 1669157 := bbase (se 4 (by rfl) ⟨156483, by rfl⟩ : syracuseStep 1669157 = 312967) (by norm_num)
theorem B4454453 : Blo 546805 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B1669205 : Blo 546805 1669205 := bbase (se 8 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 1669205 = 19561) (by norm_num)
theorem B555185 : Blo 546805 555185 := bbase (se 2 (by rfl) ⟨208194, by rfl⟩ : syracuseStep 555185 = 416389) (by norm_num)
theorem B751837 : Blo 546805 751837 := bbase (se 3 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 751837 = 281939) (by norm_num)
theorem B19003733 : Blo 546805 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B2784293 : Blo 546805 2784293 := bbase (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) (by norm_num)
theorem B3211093 : Blo 546805 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B557107 : Blo 546805 557107 := bstep (se 1 (by rfl) ⟨417830, by rfl⟩ : syracuseStep 557107 = 835661) B835661
theorem B4686605 : Blo 546805 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B820211 : Blo 546805 820211 := bstep (se 1 (by rfl) ⟨615158, by rfl⟩ : syracuseStep 820211 = 1230317) B1230317
theorem B820241 : Blo 546805 820241 := bstep (se 2 (by rfl) ⟨307590, by rfl⟩ : syracuseStep 820241 = 615181) B615181
theorem B820259 : Blo 546805 820259 := bstep (se 1 (by rfl) ⟨615194, by rfl⟩ : syracuseStep 820259 = 1230389) B1230389
theorem B820289 : Blo 546805 820289 := bstep (se 2 (by rfl) ⟨307608, by rfl⟩ : syracuseStep 820289 = 615217) B615217
theorem B820307 : Blo 546805 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B820337 : Blo 546805 820337 := bstep (se 2 (by rfl) ⟨307626, by rfl⟩ : syracuseStep 820337 = 615253) B615253
theorem B3867761 : Blo 546805 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B820355 : Blo 546805 820355 := bstep (se 1 (by rfl) ⟨615266, by rfl⟩ : syracuseStep 820355 = 1230533) B1230533
theorem B820385 : Blo 546805 820385 := bstep (se 2 (by rfl) ⟨307644, by rfl⟩ : syracuseStep 820385 = 615289) B615289
theorem B820403 : Blo 546805 820403 := bstep (se 1 (by rfl) ⟨615302, by rfl⟩ : syracuseStep 820403 = 1230605) B1230605
theorem B820433 : Blo 546805 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B820451 : Blo 546805 820451 := bstep (se 1 (by rfl) ⟨615338, by rfl⟩ : syracuseStep 820451 = 1230677) B1230677
theorem B820481 : Blo 546805 820481 := bstep (se 2 (by rfl) ⟨307680, by rfl⟩ : syracuseStep 820481 = 615361) B615361
theorem B820499 : Blo 546805 820499 := bstep (se 1 (by rfl) ⟨615374, by rfl⟩ : syracuseStep 820499 = 1230749) B1230749
theorem B820529 : Blo 546805 820529 := bstep (se 2 (by rfl) ⟨307698, by rfl⟩ : syracuseStep 820529 = 615397) B615397
theorem B820547 : Blo 546805 820547 := bstep (se 1 (by rfl) ⟨615410, by rfl⟩ : syracuseStep 820547 = 1230821) B1230821
theorem B820577 : Blo 546805 820577 := bstep (se 2 (by rfl) ⟨307716, by rfl⟩ : syracuseStep 820577 = 615433) B615433
theorem B820595 : Blo 546805 820595 := bstep (se 1 (by rfl) ⟨615446, by rfl⟩ : syracuseStep 820595 = 1230893) B1230893
theorem B820625 : Blo 546805 820625 := bstep (se 2 (by rfl) ⟨307734, by rfl⟩ : syracuseStep 820625 = 615469) B615469
theorem B820643 : Blo 546805 820643 := bstep (se 1 (by rfl) ⟨615482, by rfl⟩ : syracuseStep 820643 = 1230965) B1230965
theorem B2786723 : Blo 546805 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B820673 : Blo 546805 820673 := bstep (se 2 (by rfl) ⟨307752, by rfl⟩ : syracuseStep 820673 = 615505) B615505
theorem B820691 : Blo 546805 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B820721 : Blo 546805 820721 := bstep (se 2 (by rfl) ⟨307770, by rfl⟩ : syracuseStep 820721 = 615541) B615541
theorem B820739 : Blo 546805 820739 := bstep (se 1 (by rfl) ⟨615554, by rfl⟩ : syracuseStep 820739 = 1231109) B1231109
theorem B820769 : Blo 546805 820769 := bstep (se 2 (by rfl) ⟨307788, by rfl⟩ : syracuseStep 820769 = 615577) B615577
theorem B820787 : Blo 546805 820787 := bstep (se 1 (by rfl) ⟨615590, by rfl⟩ : syracuseStep 820787 = 1231181) B1231181
theorem B820817 : Blo 546805 820817 := bstep (se 2 (by rfl) ⟨307806, by rfl⟩ : syracuseStep 820817 = 615613) B615613
theorem B820835 : Blo 546805 820835 := bstep (se 1 (by rfl) ⟨615626, by rfl⟩ : syracuseStep 820835 = 1231253) B1231253
theorem B820865 : Blo 546805 820865 := bstep (se 2 (by rfl) ⟨307824, by rfl⟩ : syracuseStep 820865 = 615649) B615649
theorem B820883 : Blo 546805 820883 := bstep (se 1 (by rfl) ⟨615662, by rfl⟩ : syracuseStep 820883 = 1231325) B1231325
theorem B820913 : Blo 546805 820913 := bstep (se 2 (by rfl) ⟨307842, by rfl⟩ : syracuseStep 820913 = 615685) B615685
theorem B820931 : Blo 546805 820931 := bstep (se 1 (by rfl) ⟨615698, by rfl⟩ : syracuseStep 820931 = 1231397) B1231397
theorem B820961 : Blo 546805 820961 := bstep (se 2 (by rfl) ⟨307860, by rfl⟩ : syracuseStep 820961 = 615721) B615721
theorem B820979 : Blo 546805 820979 := bstep (se 1 (by rfl) ⟨615734, by rfl⟩ : syracuseStep 820979 = 1231469) B1231469
theorem B821009 : Blo 546805 821009 := bstep (se 2 (by rfl) ⟨307878, by rfl⟩ : syracuseStep 821009 = 615757) B615757
theorem B821027 : Blo 546805 821027 := bstep (se 1 (by rfl) ⟨615770, by rfl⟩ : syracuseStep 821027 = 1231541) B1231541
theorem B821057 : Blo 546805 821057 := bstep (se 2 (by rfl) ⟨307896, by rfl⟩ : syracuseStep 821057 = 615793) B615793
theorem B821075 : Blo 546805 821075 := bstep (se 1 (by rfl) ⟨615806, by rfl⟩ : syracuseStep 821075 = 1231613) B1231613
theorem B821105 : Blo 546805 821105 := bstep (se 2 (by rfl) ⟨307914, by rfl⟩ : syracuseStep 821105 = 615829) B615829
theorem B821123 : Blo 546805 821123 := bstep (se 1 (by rfl) ⟨615842, by rfl⟩ : syracuseStep 821123 = 1231685) B1231685
theorem B952211 : Blo 546805 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B821153 : Blo 546805 821153 := bstep (se 2 (by rfl) ⟨307932, by rfl⟩ : syracuseStep 821153 = 615865) B615865
theorem B952225 : Blo 546805 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B1410979 : Blo 546805 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B821171 : Blo 546805 821171 := bstep (se 1 (by rfl) ⟨615878, by rfl⟩ : syracuseStep 821171 = 1231757) B1231757
theorem B821201 : Blo 546805 821201 := bstep (se 2 (by rfl) ⟨307950, by rfl⟩ : syracuseStep 821201 = 615901) B615901
theorem B821219 : Blo 546805 821219 := bstep (se 1 (by rfl) ⟨615914, by rfl⟩ : syracuseStep 821219 = 1231829) B1231829
theorem B821249 : Blo 546805 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B821267 : Blo 546805 821267 := bstep (se 1 (by rfl) ⟨615950, by rfl⟩ : syracuseStep 821267 = 1231901) B1231901
theorem B821297 : Blo 546805 821297 := bstep (se 2 (by rfl) ⟨307986, by rfl⟩ : syracuseStep 821297 = 615973) B615973
theorem B821315 : Blo 546805 821315 := bstep (se 1 (by rfl) ⟨615986, by rfl⟩ : syracuseStep 821315 = 1231973) B1231973
theorem B821345 : Blo 546805 821345 := bstep (se 2 (by rfl) ⟨308004, by rfl⟩ : syracuseStep 821345 = 616009) B616009
theorem B821363 : Blo 546805 821363 := bstep (se 1 (by rfl) ⟨616022, by rfl⟩ : syracuseStep 821363 = 1232045) B1232045
theorem B821393 : Blo 546805 821393 := bstep (se 2 (by rfl) ⟨308022, by rfl⟩ : syracuseStep 821393 = 616045) B616045
theorem B821411 : Blo 546805 821411 := bstep (se 1 (by rfl) ⟨616058, by rfl⟩ : syracuseStep 821411 = 1232117) B1232117
theorem B821441 : Blo 546805 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B2787533 : Blo 546805 2787533 := bstep (se 3 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 2787533 = 1045325) B1045325
theorem B821459 : Blo 546805 821459 := bstep (se 1 (by rfl) ⟨616094, by rfl⟩ : syracuseStep 821459 = 1232189) B1232189
theorem B821489 : Blo 546805 821489 := bstep (se 2 (by rfl) ⟨308058, by rfl⟩ : syracuseStep 821489 = 616117) B616117
theorem B821507 : Blo 546805 821507 := bstep (se 1 (by rfl) ⟨616130, by rfl⟩ : syracuseStep 821507 = 1232261) B1232261
theorem B821537 : Blo 546805 821537 := bstep (se 2 (by rfl) ⟨308076, by rfl⟩ : syracuseStep 821537 = 616153) B616153
theorem B821555 : Blo 546805 821555 := bstep (se 1 (by rfl) ⟨616166, by rfl⟩ : syracuseStep 821555 = 1232333) B1232333
theorem B821585 : Blo 546805 821585 := bstep (se 2 (by rfl) ⟨308094, by rfl⟩ : syracuseStep 821585 = 616189) B616189
theorem B821603 : Blo 546805 821603 := bstep (se 1 (by rfl) ⟨616202, by rfl⟩ : syracuseStep 821603 = 1232405) B1232405
theorem B821633 : Blo 546805 821633 := bstep (se 2 (by rfl) ⟨308112, by rfl⟩ : syracuseStep 821633 = 616225) B616225
theorem B821651 : Blo 546805 821651 := bstep (se 1 (by rfl) ⟨616238, by rfl⟩ : syracuseStep 821651 = 1232477) B1232477
theorem B821681 : Blo 546805 821681 := bstep (se 2 (by rfl) ⟨308130, by rfl⟩ : syracuseStep 821681 = 616261) B616261
theorem B821699 : Blo 546805 821699 := bstep (se 1 (by rfl) ⟨616274, by rfl⟩ : syracuseStep 821699 = 1232549) B1232549
theorem B821729 : Blo 546805 821729 := bstep (se 2 (by rfl) ⟨308148, by rfl⟩ : syracuseStep 821729 = 616297) B616297
theorem B821747 : Blo 546805 821747 := bstep (se 1 (by rfl) ⟨616310, by rfl⟩ : syracuseStep 821747 = 1232621) B1232621
theorem B821777 : Blo 546805 821777 := bstep (se 2 (by rfl) ⟨308166, by rfl⟩ : syracuseStep 821777 = 616333) B616333
theorem B821795 : Blo 546805 821795 := bstep (se 1 (by rfl) ⟨616346, by rfl⟩ : syracuseStep 821795 = 1232693) B1232693
theorem B821825 : Blo 546805 821825 := bstep (se 2 (by rfl) ⟨308184, by rfl⟩ : syracuseStep 821825 = 616369) B616369
theorem B2230861 : Blo 546805 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B821843 : Blo 546805 821843 := bstep (se 1 (by rfl) ⟨616382, by rfl⟩ : syracuseStep 821843 = 1232765) B1232765
theorem B821873 : Blo 546805 821873 := bstep (se 2 (by rfl) ⟨308202, by rfl⟩ : syracuseStep 821873 = 616405) B616405
theorem B821891 : Blo 546805 821891 := bstep (se 1 (by rfl) ⟨616418, by rfl⟩ : syracuseStep 821891 = 1232837) B1232837
theorem B821921 : Blo 546805 821921 := bstep (se 2 (by rfl) ⟨308220, by rfl⟩ : syracuseStep 821921 = 616441) B616441
theorem B821939 : Blo 546805 821939 := bstep (se 1 (by rfl) ⟨616454, by rfl⟩ : syracuseStep 821939 = 1232909) B1232909
theorem B821969 : Blo 546805 821969 := bstep (se 2 (by rfl) ⟨308238, by rfl⟩ : syracuseStep 821969 = 616477) B616477
theorem B658147 : Blo 546805 658147 := bstep (se 1 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 658147 = 987221) B987221
theorem B821987 : Blo 546805 821987 := bstep (se 1 (by rfl) ⟨616490, by rfl⟩ : syracuseStep 821987 = 1232981) B1232981
theorem B14093027 : Blo 546805 14093027 := bstep (se 1 (by rfl) ⟨10569770, by rfl⟩ : syracuseStep 14093027 = 21139541) B21139541
theorem B822017 : Blo 546805 822017 := bstep (se 2 (by rfl) ⟨308256, by rfl⟩ : syracuseStep 822017 = 616513) B616513
theorem B822035 : Blo 546805 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B822065 : Blo 546805 822065 := bstep (se 2 (by rfl) ⟨308274, by rfl⟩ : syracuseStep 822065 = 616549) B616549
theorem B822083 : Blo 546805 822083 := bstep (se 1 (by rfl) ⟨616562, by rfl⟩ : syracuseStep 822083 = 1233125) B1233125
theorem B822113 : Blo 546805 822113 := bstep (se 2 (by rfl) ⟨308292, by rfl⟩ : syracuseStep 822113 = 616585) B616585
theorem B822131 : Blo 546805 822131 := bstep (se 1 (by rfl) ⟨616598, by rfl⟩ : syracuseStep 822131 = 1233197) B1233197
theorem B822161 : Blo 546805 822161 := bstep (se 2 (by rfl) ⟨308310, by rfl⟩ : syracuseStep 822161 = 616621) B616621
theorem B822179 : Blo 546805 822179 := bstep (se 1 (by rfl) ⟨616634, by rfl⟩ : syracuseStep 822179 = 1233269) B1233269
theorem B7015349 : Blo 546805 7015349 := bstep (se 5 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 7015349 = 657689) B657689
theorem B822209 : Blo 546805 822209 := bstep (se 2 (by rfl) ⟨308328, by rfl⟩ : syracuseStep 822209 = 616657) B616657
theorem B822227 : Blo 546805 822227 := bstep (se 1 (by rfl) ⟨616670, by rfl⟩ : syracuseStep 822227 = 1233341) B1233341
theorem B822257 : Blo 546805 822257 := bstep (se 2 (by rfl) ⟨308346, by rfl⟩ : syracuseStep 822257 = 616693) B616693
theorem B822275 : Blo 546805 822275 := bstep (se 1 (by rfl) ⟨616706, by rfl⟩ : syracuseStep 822275 = 1233413) B1233413
theorem B822305 : Blo 546805 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B822323 : Blo 546805 822323 := bstep (se 1 (by rfl) ⟨616742, by rfl⟩ : syracuseStep 822323 = 1233485) B1233485
theorem B822353 : Blo 546805 822353 := bstep (se 2 (by rfl) ⟨308382, by rfl⟩ : syracuseStep 822353 = 616765) B616765
theorem B822371 : Blo 546805 822371 := bstep (se 1 (by rfl) ⟨616778, by rfl⟩ : syracuseStep 822371 = 1233557) B1233557
theorem B822401 : Blo 546805 822401 := bstep (se 2 (by rfl) ⟨308400, by rfl⟩ : syracuseStep 822401 = 616801) B616801
theorem B822419 : Blo 546805 822419 := bstep (se 1 (by rfl) ⟨616814, by rfl⟩ : syracuseStep 822419 = 1233629) B1233629
theorem B822449 : Blo 546805 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B822467 : Blo 546805 822467 := bstep (se 1 (by rfl) ⟨616850, by rfl⟩ : syracuseStep 822467 = 1233701) B1233701
theorem B5016773 : Blo 546805 5016773 := bstep (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) B940645
theorem B822497 : Blo 546805 822497 := bstep (se 2 (by rfl) ⟨308436, by rfl⟩ : syracuseStep 822497 = 616873) B616873
theorem B822515 : Blo 546805 822515 := bstep (se 1 (by rfl) ⟨616886, by rfl⟩ : syracuseStep 822515 = 1233773) B1233773
theorem B822545 : Blo 546805 822545 := bstep (se 2 (by rfl) ⟨308454, by rfl⟩ : syracuseStep 822545 = 616909) B616909
theorem B1248547 : Blo 546805 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B822563 : Blo 546805 822563 := bstep (se 1 (by rfl) ⟨616922, by rfl⟩ : syracuseStep 822563 = 1233845) B1233845
theorem B822593 : Blo 546805 822593 := bstep (se 2 (by rfl) ⟨308472, by rfl⟩ : syracuseStep 822593 = 616945) B616945
theorem B822611 : Blo 546805 822611 := bstep (se 1 (by rfl) ⟨616958, by rfl⟩ : syracuseStep 822611 = 1233917) B1233917
theorem B822641 : Blo 546805 822641 := bstep (se 2 (by rfl) ⟨308490, by rfl⟩ : syracuseStep 822641 = 616981) B616981
theorem B822659 : Blo 546805 822659 := bstep (se 1 (by rfl) ⟨616994, by rfl⟩ : syracuseStep 822659 = 1233989) B1233989
theorem B822689 : Blo 546805 822689 := bstep (se 2 (by rfl) ⟨308508, by rfl⟩ : syracuseStep 822689 = 617017) B617017
theorem B822707 : Blo 546805 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B822737 : Blo 546805 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B822755 : Blo 546805 822755 := bstep (se 1 (by rfl) ⟨617066, by rfl⟩ : syracuseStep 822755 = 1234133) B1234133
theorem B822785 : Blo 546805 822785 := bstep (se 2 (by rfl) ⟨308544, by rfl⟩ : syracuseStep 822785 = 617089) B617089
theorem B822803 : Blo 546805 822803 := bstep (se 1 (by rfl) ⟨617102, by rfl⟩ : syracuseStep 822803 = 1234205) B1234205
theorem B822833 : Blo 546805 822833 := bstep (se 2 (by rfl) ⟨308562, by rfl⟩ : syracuseStep 822833 = 617125) B617125
theorem B822851 : Blo 546805 822851 := bstep (se 1 (by rfl) ⟨617138, by rfl⟩ : syracuseStep 822851 = 1234277) B1234277
theorem B822881 : Blo 546805 822881 := bstep (se 2 (by rfl) ⟨308580, by rfl⟩ : syracuseStep 822881 = 617161) B617161
theorem B3116657 : Blo 546805 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B822899 : Blo 546805 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B822929 : Blo 546805 822929 := bstep (se 2 (by rfl) ⟨308598, by rfl⟩ : syracuseStep 822929 = 617197) B617197
theorem B822947 : Blo 546805 822947 := bstep (se 1 (by rfl) ⟨617210, by rfl⟩ : syracuseStep 822947 = 1234421) B1234421
theorem B822977 : Blo 546805 822977 := bstep (se 2 (by rfl) ⟨308616, by rfl⟩ : syracuseStep 822977 = 617233) B617233
theorem B1478353 : Blo 546805 1478353 := bstep (se 2 (by rfl) ⟨554382, by rfl⟩ : syracuseStep 1478353 = 1108765) B1108765
theorem B822995 : Blo 546805 822995 := bstep (se 1 (by rfl) ⟨617246, by rfl⟩ : syracuseStep 822995 = 1234493) B1234493
theorem B823025 : Blo 546805 823025 := bstep (se 2 (by rfl) ⟨308634, by rfl⟩ : syracuseStep 823025 = 617269) B617269
theorem B823043 : Blo 546805 823043 := bstep (se 1 (by rfl) ⟨617282, by rfl⟩ : syracuseStep 823043 = 1234565) B1234565
theorem B823073 : Blo 546805 823073 := bstep (se 2 (by rfl) ⟨308652, by rfl⟩ : syracuseStep 823073 = 617305) B617305
theorem B823091 : Blo 546805 823091 := bstep (se 1 (by rfl) ⟨617318, by rfl⟩ : syracuseStep 823091 = 1234637) B1234637
theorem B823121 : Blo 546805 823121 := bstep (se 2 (by rfl) ⟨308670, by rfl⟩ : syracuseStep 823121 = 617341) B617341
theorem B823139 : Blo 546805 823139 := bstep (se 1 (by rfl) ⟨617354, by rfl⟩ : syracuseStep 823139 = 1234709) B1234709
theorem B823169 : Blo 546805 823169 := bstep (se 2 (by rfl) ⟨308688, by rfl⟩ : syracuseStep 823169 = 617377) B617377
theorem B823187 : Blo 546805 823187 := bstep (se 1 (by rfl) ⟨617390, by rfl⟩ : syracuseStep 823187 = 1234781) B1234781
theorem B823217 : Blo 546805 823217 := bstep (se 2 (by rfl) ⟨308706, by rfl⟩ : syracuseStep 823217 = 617413) B617413
theorem B823235 : Blo 546805 823235 := bstep (se 1 (by rfl) ⟨617426, by rfl⟩ : syracuseStep 823235 = 1234853) B1234853
theorem B823265 : Blo 546805 823265 := bstep (se 2 (by rfl) ⟨308724, by rfl⟩ : syracuseStep 823265 = 617449) B617449
theorem B626659 : Blo 546805 626659 := bstep (se 1 (by rfl) ⟨469994, by rfl⟩ : syracuseStep 626659 = 939989) B939989
theorem B6033379 : Blo 546805 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B823283 : Blo 546805 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B823313 : Blo 546805 823313 := bstep (se 2 (by rfl) ⟨308742, by rfl⟩ : syracuseStep 823313 = 617485) B617485
theorem B823331 : Blo 546805 823331 := bstep (se 1 (by rfl) ⟨617498, by rfl⟩ : syracuseStep 823331 = 1234997) B1234997
theorem B823361 : Blo 546805 823361 := bstep (se 2 (by rfl) ⟨308760, by rfl⟩ : syracuseStep 823361 = 617521) B617521
theorem B3510341 : Blo 546805 3510341 := bstep (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) B658189
theorem B5279813 : Blo 546805 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B823379 : Blo 546805 823379 := bstep (se 1 (by rfl) ⟨617534, by rfl⟩ : syracuseStep 823379 = 1235069) B1235069
theorem B823409 : Blo 546805 823409 := bstep (se 2 (by rfl) ⟨308778, by rfl⟩ : syracuseStep 823409 = 617557) B617557
theorem B823427 : Blo 546805 823427 := bstep (se 1 (by rfl) ⟨617570, by rfl⟩ : syracuseStep 823427 = 1235141) B1235141
theorem B823457 : Blo 546805 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B823475 : Blo 546805 823475 := bstep (se 1 (by rfl) ⟨617606, by rfl⟩ : syracuseStep 823475 = 1235213) B1235213
theorem B823505 : Blo 546805 823505 := bstep (se 2 (by rfl) ⟨308814, by rfl⟩ : syracuseStep 823505 = 617629) B617629
theorem B823523 : Blo 546805 823523 := bstep (se 1 (by rfl) ⟨617642, by rfl⟩ : syracuseStep 823523 = 1235285) B1235285
theorem B823553 : Blo 546805 823553 := bstep (se 2 (by rfl) ⟨308832, by rfl⟩ : syracuseStep 823553 = 617665) B617665
theorem B823571 : Blo 546805 823571 := bstep (se 1 (by rfl) ⟨617678, by rfl⟩ : syracuseStep 823571 = 1235357) B1235357
theorem B823601 : Blo 546805 823601 := bstep (se 2 (by rfl) ⟨308850, by rfl⟩ : syracuseStep 823601 = 617701) B617701
theorem B823619 : Blo 546805 823619 := bstep (se 1 (by rfl) ⟨617714, by rfl⟩ : syracuseStep 823619 = 1235429) B1235429
theorem B823649 : Blo 546805 823649 := bstep (se 2 (by rfl) ⟨308868, by rfl⟩ : syracuseStep 823649 = 617737) B617737
theorem B823667 : Blo 546805 823667 := bstep (se 1 (by rfl) ⟨617750, by rfl⟩ : syracuseStep 823667 = 1235501) B1235501
theorem B823697 : Blo 546805 823697 := bstep (se 2 (by rfl) ⟨308886, by rfl⟩ : syracuseStep 823697 = 617773) B617773
theorem B823715 : Blo 546805 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B823745 : Blo 546805 823745 := bstep (se 2 (by rfl) ⟨308904, by rfl⟩ : syracuseStep 823745 = 617809) B617809
theorem B823763 : Blo 546805 823763 := bstep (se 1 (by rfl) ⟨617822, by rfl⟩ : syracuseStep 823763 = 1235645) B1235645
theorem B692707 : Blo 546805 692707 := bstep (se 1 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 692707 = 1039061) B1039061
theorem B823793 : Blo 546805 823793 := bstep (se 2 (by rfl) ⟨308922, by rfl⟩ : syracuseStep 823793 = 617845) B617845
theorem B823811 : Blo 546805 823811 := bstep (se 1 (by rfl) ⟨617858, by rfl⟩ : syracuseStep 823811 = 1235717) B1235717
theorem B823841 : Blo 546805 823841 := bstep (se 2 (by rfl) ⟨308940, by rfl⟩ : syracuseStep 823841 = 617881) B617881
theorem B823859 : Blo 546805 823859 := bstep (se 1 (by rfl) ⟨617894, by rfl⟩ : syracuseStep 823859 = 1235789) B1235789
theorem B692803 : Blo 546805 692803 := bstep (se 1 (by rfl) ⟨519602, by rfl⟩ : syracuseStep 692803 = 1039205) B1039205
theorem B823889 : Blo 546805 823889 := bstep (se 2 (by rfl) ⟨308958, by rfl⟩ : syracuseStep 823889 = 617917) B617917
theorem B823907 : Blo 546805 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B823937 : Blo 546805 823937 := bstep (se 2 (by rfl) ⟨308976, by rfl⟩ : syracuseStep 823937 = 617953) B617953
theorem B823955 : Blo 546805 823955 := bstep (se 1 (by rfl) ⟨617966, by rfl⟩ : syracuseStep 823955 = 1235933) B1235933
theorem B823985 : Blo 546805 823985 := bstep (se 2 (by rfl) ⟨308994, by rfl⟩ : syracuseStep 823985 = 617989) B617989
theorem B824003 : Blo 546805 824003 := bstep (se 1 (by rfl) ⟨618002, by rfl⟩ : syracuseStep 824003 = 1236005) B1236005
theorem B824033 : Blo 546805 824033 := bstep (se 2 (by rfl) ⟨309012, by rfl⟩ : syracuseStep 824033 = 618025) B618025
theorem B824051 : Blo 546805 824051 := bstep (se 1 (by rfl) ⟨618038, by rfl⟩ : syracuseStep 824051 = 1236077) B1236077
theorem B824081 : Blo 546805 824081 := bstep (se 2 (by rfl) ⟨309030, by rfl⟩ : syracuseStep 824081 = 618061) B618061
theorem B824099 : Blo 546805 824099 := bstep (se 1 (by rfl) ⟨618074, by rfl⟩ : syracuseStep 824099 = 1236149) B1236149
theorem B1970993 : Blo 546805 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B824129 : Blo 546805 824129 := bstep (se 2 (by rfl) ⟨309048, by rfl⟩ : syracuseStep 824129 = 618097) B618097
theorem B824147 : Blo 546805 824147 := bstep (se 1 (by rfl) ⟨618110, by rfl⟩ : syracuseStep 824147 = 1236221) B1236221
theorem B13308785 : Blo 546805 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B824177 : Blo 546805 824177 := bstep (se 2 (by rfl) ⟨309066, by rfl⟩ : syracuseStep 824177 = 618133) B618133
theorem B824195 : Blo 546805 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B824225 : Blo 546805 824225 := bstep (se 2 (by rfl) ⟨309084, by rfl⟩ : syracuseStep 824225 = 618169) B618169
theorem B824243 : Blo 546805 824243 := bstep (se 1 (by rfl) ⟨618182, by rfl⟩ : syracuseStep 824243 = 1236365) B1236365
theorem B824273 : Blo 546805 824273 := bstep (se 2 (by rfl) ⟨309102, by rfl⟩ : syracuseStep 824273 = 618205) B618205
theorem B824291 : Blo 546805 824291 := bstep (se 1 (by rfl) ⟨618218, by rfl⟩ : syracuseStep 824291 = 1236437) B1236437
theorem B824321 : Blo 546805 824321 := bstep (se 2 (by rfl) ⟨309120, by rfl⟩ : syracuseStep 824321 = 618241) B618241
theorem B824339 : Blo 546805 824339 := bstep (se 1 (by rfl) ⟨618254, by rfl⟩ : syracuseStep 824339 = 1236509) B1236509
theorem B3118115 : Blo 546805 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B824369 : Blo 546805 824369 := bstep (se 2 (by rfl) ⟨309138, by rfl⟩ : syracuseStep 824369 = 618277) B618277
theorem B693299 : Blo 546805 693299 := bstep (se 1 (by rfl) ⟨519974, by rfl⟩ : syracuseStep 693299 = 1039949) B1039949
theorem B824387 : Blo 546805 824387 := bstep (se 1 (by rfl) ⟨618290, by rfl⟩ : syracuseStep 824387 = 1236581) B1236581
theorem B824417 : Blo 546805 824417 := bstep (se 2 (by rfl) ⟨309156, by rfl⟩ : syracuseStep 824417 = 618313) B618313
theorem B824435 : Blo 546805 824435 := bstep (se 1 (by rfl) ⟨618326, by rfl⟩ : syracuseStep 824435 = 1236653) B1236653
theorem B824465 : Blo 546805 824465 := bstep (se 2 (by rfl) ⟨309174, by rfl⟩ : syracuseStep 824465 = 618349) B618349
theorem B890003 : Blo 546805 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B824483 : Blo 546805 824483 := bstep (se 1 (by rfl) ⟨618362, by rfl⟩ : syracuseStep 824483 = 1236725) B1236725
theorem B988337 : Blo 546805 988337 := bstep (se 2 (by rfl) ⟨370626, by rfl⟩ : syracuseStep 988337 = 741253) B741253
theorem B824513 : Blo 546805 824513 := bstep (se 2 (by rfl) ⟨309192, by rfl⟩ : syracuseStep 824513 = 618385) B618385
theorem B922819 : Blo 546805 922819 := bstep (se 1 (by rfl) ⟨692114, by rfl⟩ : syracuseStep 922819 = 1384229) B1384229
theorem B824531 : Blo 546805 824531 := bstep (se 1 (by rfl) ⟨618398, by rfl⟩ : syracuseStep 824531 = 1236797) B1236797
theorem B824561 : Blo 546805 824561 := bstep (se 2 (by rfl) ⟨309210, by rfl⟩ : syracuseStep 824561 = 618421) B618421
theorem B824579 : Blo 546805 824579 := bstep (se 1 (by rfl) ⟨618434, by rfl⟩ : syracuseStep 824579 = 1236869) B1236869
theorem B824609 : Blo 546805 824609 := bstep (se 2 (by rfl) ⟨309228, by rfl⟩ : syracuseStep 824609 = 618457) B618457
theorem B824627 : Blo 546805 824627 := bstep (se 1 (by rfl) ⟨618470, by rfl⟩ : syracuseStep 824627 = 1236941) B1236941
theorem B660803 : Blo 546805 660803 := bstep (se 1 (by rfl) ⟨495602, by rfl⟩ : syracuseStep 660803 = 991205) B991205
theorem B922961 : Blo 546805 922961 := bstep (se 2 (by rfl) ⟨346110, by rfl⟩ : syracuseStep 922961 = 692221) B692221
theorem B824657 : Blo 546805 824657 := bstep (se 2 (by rfl) ⟨309246, by rfl⟩ : syracuseStep 824657 = 618493) B618493
theorem B824675 : Blo 546805 824675 := bstep (se 1 (by rfl) ⟨618506, by rfl⟩ : syracuseStep 824675 = 1237013) B1237013
theorem B824705 : Blo 546805 824705 := bstep (se 2 (by rfl) ⟨309264, by rfl⟩ : syracuseStep 824705 = 618529) B618529
theorem B824723 : Blo 546805 824723 := bstep (se 1 (by rfl) ⟨618542, by rfl⟩ : syracuseStep 824723 = 1237085) B1237085
theorem B824753 : Blo 546805 824753 := bstep (se 2 (by rfl) ⟨309282, by rfl⟩ : syracuseStep 824753 = 618565) B618565
theorem B824771 : Blo 546805 824771 := bstep (se 1 (by rfl) ⟨618578, by rfl⟩ : syracuseStep 824771 = 1237157) B1237157
theorem B923089 : Blo 546805 923089 := bstep (se 2 (by rfl) ⟨346158, by rfl⟩ : syracuseStep 923089 = 692317) B692317
theorem B824801 : Blo 546805 824801 := bstep (se 2 (by rfl) ⟨309300, by rfl⟩ : syracuseStep 824801 = 618601) B618601
theorem B923123 : Blo 546805 923123 := bstep (se 1 (by rfl) ⟨692342, by rfl⟩ : syracuseStep 923123 = 1384685) B1384685
theorem B824819 : Blo 546805 824819 := bstep (se 1 (by rfl) ⟨618614, by rfl⟩ : syracuseStep 824819 = 1237229) B1237229
theorem B1316369 : Blo 546805 1316369 := bstep (se 2 (by rfl) ⟨493638, by rfl⟩ : syracuseStep 1316369 = 987277) B987277
theorem B824849 : Blo 546805 824849 := bstep (se 2 (by rfl) ⟨309318, by rfl⟩ : syracuseStep 824849 = 618637) B618637
theorem B824867 : Blo 546805 824867 := bstep (se 1 (by rfl) ⟨618650, by rfl⟩ : syracuseStep 824867 = 1237301) B1237301
theorem B824897 : Blo 546805 824897 := bstep (se 2 (by rfl) ⟨309336, by rfl⟩ : syracuseStep 824897 = 618673) B618673
theorem B824915 : Blo 546805 824915 := bstep (se 1 (by rfl) ⟨618686, by rfl⟩ : syracuseStep 824915 = 1237373) B1237373
theorem B824945 : Blo 546805 824945 := bstep (se 2 (by rfl) ⟨309354, by rfl⟩ : syracuseStep 824945 = 618709) B618709
theorem B923251 : Blo 546805 923251 := bstep (se 1 (by rfl) ⟨692438, by rfl⟩ : syracuseStep 923251 = 1384877) B1384877
theorem B824963 : Blo 546805 824963 := bstep (se 1 (by rfl) ⟨618722, by rfl⟩ : syracuseStep 824963 = 1237445) B1237445
theorem B824993 : Blo 546805 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B1185457 : Blo 546805 1185457 := bstep (se 2 (by rfl) ⟨444546, by rfl⟩ : syracuseStep 1185457 = 889093) B889093
theorem B825011 : Blo 546805 825011 := bstep (se 1 (by rfl) ⟨618758, by rfl⟩ : syracuseStep 825011 = 1237517) B1237517
theorem B825041 : Blo 546805 825041 := bstep (se 2 (by rfl) ⟨309390, by rfl⟩ : syracuseStep 825041 = 618781) B618781
theorem B825059 : Blo 546805 825059 := bstep (se 1 (by rfl) ⟨618794, by rfl⟩ : syracuseStep 825059 = 1237589) B1237589
theorem B694003 : Blo 546805 694003 := bstep (se 1 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 694003 = 1041005) B1041005
theorem B923393 : Blo 546805 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B825089 : Blo 546805 825089 := bstep (se 2 (by rfl) ⟨309408, by rfl⟩ : syracuseStep 825089 = 618817) B618817
theorem B825107 : Blo 546805 825107 := bstep (se 1 (by rfl) ⟨618830, by rfl⟩ : syracuseStep 825107 = 1237661) B1237661
theorem B1480493 : Blo 546805 1480493 := bstep (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) B555185
theorem B825137 : Blo 546805 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B825155 : Blo 546805 825155 := bstep (se 1 (by rfl) ⟨618866, by rfl⟩ : syracuseStep 825155 = 1237733) B1237733
theorem B694099 : Blo 546805 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B825185 : Blo 546805 825185 := bstep (se 2 (by rfl) ⟨309444, by rfl⟩ : syracuseStep 825185 = 618889) B618889
theorem B825203 : Blo 546805 825203 := bstep (se 1 (by rfl) ⟨618902, by rfl⟩ : syracuseStep 825203 = 1237805) B1237805
theorem B923521 : Blo 546805 923521 := bstep (se 2 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 923521 = 692641) B692641
theorem B825233 : Blo 546805 825233 := bstep (se 2 (by rfl) ⟨309462, by rfl⟩ : syracuseStep 825233 = 618925) B618925
theorem B923555 : Blo 546805 923555 := bstep (se 1 (by rfl) ⟨692666, by rfl⟩ : syracuseStep 923555 = 1385333) B1385333
theorem B825251 : Blo 546805 825251 := bstep (se 1 (by rfl) ⟨618938, by rfl⟩ : syracuseStep 825251 = 1237877) B1237877
theorem B825281 : Blo 546805 825281 := bstep (se 2 (by rfl) ⟨309480, by rfl⟩ : syracuseStep 825281 = 618961) B618961
theorem B825299 : Blo 546805 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B825329 : Blo 546805 825329 := bstep (se 2 (by rfl) ⟨309498, by rfl⟩ : syracuseStep 825329 = 618997) B618997
theorem B825347 : Blo 546805 825347 := bstep (se 1 (by rfl) ⟨619010, by rfl⟩ : syracuseStep 825347 = 1238021) B1238021
theorem B825377 : Blo 546805 825377 := bstep (se 2 (by rfl) ⟨309516, by rfl⟩ : syracuseStep 825377 = 619033) B619033
theorem B923683 : Blo 546805 923683 := bstep (se 1 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 923683 = 1385525) B1385525
theorem B825395 : Blo 546805 825395 := bstep (se 1 (by rfl) ⟨619046, by rfl⟩ : syracuseStep 825395 = 1238093) B1238093
theorem B825425 : Blo 546805 825425 := bstep (se 2 (by rfl) ⟨309534, by rfl⟩ : syracuseStep 825425 = 619069) B619069
theorem B825443 : Blo 546805 825443 := bstep (se 1 (by rfl) ⟨619082, by rfl⟩ : syracuseStep 825443 = 1238165) B1238165
theorem B825473 : Blo 546805 825473 := bstep (se 2 (by rfl) ⟨309552, by rfl⟩ : syracuseStep 825473 = 619105) B619105
theorem B825491 : Blo 546805 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B923825 : Blo 546805 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B825521 : Blo 546805 825521 := bstep (se 2 (by rfl) ⟨309570, by rfl⟩ : syracuseStep 825521 = 619141) B619141
theorem B825539 : Blo 546805 825539 := bstep (se 1 (by rfl) ⟨619154, by rfl⟩ : syracuseStep 825539 = 1238309) B1238309
theorem B825569 : Blo 546805 825569 := bstep (se 2 (by rfl) ⟨309588, by rfl⟩ : syracuseStep 825569 = 619177) B619177
theorem B825587 : Blo 546805 825587 := bstep (se 1 (by rfl) ⟨619190, by rfl⟩ : syracuseStep 825587 = 1238381) B1238381
theorem B825617 : Blo 546805 825617 := bstep (se 2 (by rfl) ⟨309606, by rfl⟩ : syracuseStep 825617 = 619213) B619213
theorem B891169 : Blo 546805 891169 := bstep (se 2 (by rfl) ⟨334188, by rfl⟩ : syracuseStep 891169 = 668377) B668377
theorem B825635 : Blo 546805 825635 := bstep (se 1 (by rfl) ⟨619226, by rfl⟩ : syracuseStep 825635 = 1238453) B1238453
theorem B3742001 : Blo 546805 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B923953 : Blo 546805 923953 := bstep (se 2 (by rfl) ⟨346482, by rfl⟩ : syracuseStep 923953 = 692965) B692965
theorem B825665 : Blo 546805 825665 := bstep (se 2 (by rfl) ⟨309624, by rfl⟩ : syracuseStep 825665 = 619249) B619249
theorem B694595 : Blo 546805 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B923987 : Blo 546805 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B825683 : Blo 546805 825683 := bstep (se 1 (by rfl) ⟨619262, by rfl⟩ : syracuseStep 825683 = 1238525) B1238525
theorem B825713 : Blo 546805 825713 := bstep (se 2 (by rfl) ⟨309642, by rfl⟩ : syracuseStep 825713 = 619285) B619285
theorem B825731 : Blo 546805 825731 := bstep (se 1 (by rfl) ⟨619298, by rfl⟩ : syracuseStep 825731 = 1238597) B1238597
theorem B825761 : Blo 546805 825761 := bstep (se 2 (by rfl) ⟨309660, by rfl⟩ : syracuseStep 825761 = 619321) B619321
theorem B825779 : Blo 546805 825779 := bstep (se 1 (by rfl) ⟨619334, by rfl⟩ : syracuseStep 825779 = 1238669) B1238669
theorem B825809 : Blo 546805 825809 := bstep (se 2 (by rfl) ⟨309678, by rfl⟩ : syracuseStep 825809 = 619357) B619357
theorem B924115 : Blo 546805 924115 := bstep (se 1 (by rfl) ⟨693086, by rfl⟩ : syracuseStep 924115 = 1386173) B1386173
theorem B825827 : Blo 546805 825827 := bstep (se 1 (by rfl) ⟨619370, by rfl⟩ : syracuseStep 825827 = 1238741) B1238741
theorem B825857 : Blo 546805 825857 := bstep (se 2 (by rfl) ⟨309696, by rfl⟩ : syracuseStep 825857 = 619393) B619393
theorem B825875 : Blo 546805 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B825905 : Blo 546805 825905 := bstep (se 2 (by rfl) ⟨309714, by rfl⟩ : syracuseStep 825905 = 619429) B619429
theorem B825923 : Blo 546805 825923 := bstep (se 1 (by rfl) ⟨619442, by rfl⟩ : syracuseStep 825923 = 1238885) B1238885
theorem B924257 : Blo 546805 924257 := bstep (se 2 (by rfl) ⟨346596, by rfl⟩ : syracuseStep 924257 = 693193) B693193
theorem B825953 : Blo 546805 825953 := bstep (se 2 (by rfl) ⟨309732, by rfl⟩ : syracuseStep 825953 = 619465) B619465
theorem B825971 : Blo 546805 825971 := bstep (se 1 (by rfl) ⟨619478, by rfl⟩ : syracuseStep 825971 = 1238957) B1238957
theorem B826001 : Blo 546805 826001 := bstep (se 2 (by rfl) ⟨309750, by rfl⟩ : syracuseStep 826001 = 619501) B619501
theorem B826019 : Blo 546805 826019 := bstep (se 1 (by rfl) ⟨619514, by rfl⟩ : syracuseStep 826019 = 1239029) B1239029
theorem B826049 : Blo 546805 826049 := bstep (se 2 (by rfl) ⟨309768, by rfl⟩ : syracuseStep 826049 = 619537) B619537
theorem B1252049 : Blo 546805 1252049 := bstep (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) B939037
theorem B826067 : Blo 546805 826067 := bstep (se 1 (by rfl) ⟨619550, by rfl⟩ : syracuseStep 826067 = 1239101) B1239101
theorem B924385 : Blo 546805 924385 := bstep (se 2 (by rfl) ⟨346644, by rfl⟩ : syracuseStep 924385 = 693289) B693289
theorem B826097 : Blo 546805 826097 := bstep (se 2 (by rfl) ⟨309786, by rfl⟩ : syracuseStep 826097 = 619573) B619573
theorem B924419 : Blo 546805 924419 := bstep (se 1 (by rfl) ⟨693314, by rfl⟩ : syracuseStep 924419 = 1386629) B1386629
theorem B826115 : Blo 546805 826115 := bstep (se 1 (by rfl) ⟨619586, by rfl⟩ : syracuseStep 826115 = 1239173) B1239173
theorem B826145 : Blo 546805 826145 := bstep (se 2 (by rfl) ⟨309804, by rfl⟩ : syracuseStep 826145 = 619609) B619609
theorem B826163 : Blo 546805 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B1874765 : Blo 546805 1874765 := bstep (se 3 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 1874765 = 703037) B703037
theorem B826193 : Blo 546805 826193 := bstep (se 2 (by rfl) ⟨309822, by rfl⟩ : syracuseStep 826193 = 619645) B619645
theorem B1055587 : Blo 546805 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B924547 : Blo 546805 924547 := bstep (se 1 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 924547 = 1386821) B1386821
theorem B990161 : Blo 546805 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B695299 : Blo 546805 695299 := bstep (se 1 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 695299 = 1042949) B1042949
theorem B924689 : Blo 546805 924689 := bstep (se 2 (by rfl) ⟨346758, by rfl⟩ : syracuseStep 924689 = 693517) B693517
theorem B695395 : Blo 546805 695395 := bstep (se 1 (by rfl) ⟨521546, by rfl⟩ : syracuseStep 695395 = 1043093) B1043093
theorem B924817 : Blo 546805 924817 := bstep (se 2 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 924817 = 693613) B693613
theorem B1186979 : Blo 546805 1186979 := bstep (se 1 (by rfl) ⟨890234, by rfl⟩ : syracuseStep 1186979 = 1780469) B1780469
theorem B924851 : Blo 546805 924851 := bstep (se 1 (by rfl) ⟨693638, by rfl⟩ : syracuseStep 924851 = 1387277) B1387277
theorem B924979 : Blo 546805 924979 := bstep (se 1 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 924979 = 1387469) B1387469
theorem B925121 : Blo 546805 925121 := bstep (se 2 (by rfl) ⟨346920, by rfl⟩ : syracuseStep 925121 = 693841) B693841
theorem B57187781 : Blo 546805 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B6659597 : Blo 546805 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B925249 : Blo 546805 925249 := bstep (se 2 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 925249 = 693937) B693937
theorem B695891 : Blo 546805 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B2629219 : Blo 546805 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B925283 : Blo 546805 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B5283427 : Blo 546805 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B1318531 : Blo 546805 1318531 := bstep (se 1 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 1318531 = 1977797) B1977797
theorem B564931 : Blo 546805 564931 := bstep (se 1 (by rfl) ⟨423698, by rfl⟩ : syracuseStep 564931 = 847397) B847397
theorem B925411 : Blo 546805 925411 := bstep (se 1 (by rfl) ⟨694058, by rfl⟩ : syracuseStep 925411 = 1388117) B1388117
theorem B1187569 : Blo 546805 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B925553 : Blo 546805 925553 := bstep (se 2 (by rfl) ⟨347082, by rfl⟩ : syracuseStep 925553 = 694165) B694165
theorem B1974221 : Blo 546805 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B925681 : Blo 546805 925681 := bstep (se 2 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 925681 = 694261) B694261
theorem B925715 : Blo 546805 925715 := bstep (se 1 (by rfl) ⟨694286, by rfl⟩ : syracuseStep 925715 = 1388573) B1388573
theorem B1187875 : Blo 546805 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B925843 : Blo 546805 925843 := bstep (se 1 (by rfl) ⟨694382, by rfl⟩ : syracuseStep 925843 = 1388765) B1388765
theorem B696595 : Blo 546805 696595 := bstep (se 1 (by rfl) ⟨522446, by rfl⟩ : syracuseStep 696595 = 1044893) B1044893
theorem B925985 : Blo 546805 925985 := bstep (se 2 (by rfl) ⟨347244, by rfl⟩ : syracuseStep 925985 = 694489) B694489
theorem B7119173 : Blo 546805 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B2498915 : Blo 546805 2498915 := bstep (se 1 (by rfl) ⟨1874186, by rfl⟩ : syracuseStep 2498915 = 3748373) B3748373
theorem B696691 : Blo 546805 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B926113 : Blo 546805 926113 := bstep (se 2 (by rfl) ⟨347292, by rfl⟩ : syracuseStep 926113 = 694585) B694585
theorem B1057187 : Blo 546805 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B2630065 : Blo 546805 2630065 := bstep (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) B1972549
theorem B926147 : Blo 546805 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B1385009 : Blo 546805 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B926275 : Blo 546805 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B991811 : Blo 546805 991811 := bstep (se 1 (by rfl) ⟨743858, by rfl⟩ : syracuseStep 991811 = 1487717) B1487717
theorem B1385059 : Blo 546805 1385059 := bstep (se 1 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 1385059 = 2077589) B2077589
theorem B4694669 : Blo 546805 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B926417 : Blo 546805 926417 := bstep (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) B694813
theorem B1385201 : Blo 546805 1385201 := bstep (se 2 (by rfl) ⟨519450, by rfl⟩ : syracuseStep 1385201 = 1038901) B1038901
theorem B926545 : Blo 546805 926545 := bstep (se 2 (by rfl) ⟨347454, by rfl⟩ : syracuseStep 926545 = 694909) B694909
theorem B1319761 : Blo 546805 1319761 := bstep (se 2 (by rfl) ⟨494910, by rfl⟩ : syracuseStep 1319761 = 989821) B989821
theorem B307635029 : Blo 546805 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B926579 : Blo 546805 926579 := bstep (se 1 (by rfl) ⟨694934, by rfl⟩ : syracuseStep 926579 = 1389869) B1389869
theorem B926707 : Blo 546805 926707 := bstep (se 1 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 926707 = 1390061) B1390061
theorem B4170851 : Blo 546805 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B926849 : Blo 546805 926849 := bstep (se 2 (by rfl) ⟨347568, by rfl⟩ : syracuseStep 926849 = 695137) B695137
theorem B2958563 : Blo 546805 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B926977 : Blo 546805 926977 := bstep (se 2 (by rfl) ⟨347616, by rfl⟩ : syracuseStep 926977 = 695233) B695233
theorem B927011 : Blo 546805 927011 := bstep (se 1 (by rfl) ⟨695258, by rfl⟩ : syracuseStep 927011 = 1390517) B1390517
theorem B927139 : Blo 546805 927139 := bstep (se 1 (by rfl) ⟨695354, by rfl⟩ : syracuseStep 927139 = 1390709) B1390709
theorem B927281 : Blo 546805 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B927409 : Blo 546805 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B4236997 : Blo 546805 4236997 := bstep (se 4 (by rfl) ⟨397218, by rfl⟩ : syracuseStep 4236997 = 794437) B794437
theorem B1386193 : Blo 546805 1386193 := bstep (se 2 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 1386193 = 1039645) B1039645
theorem B927443 : Blo 546805 927443 := bstep (se 1 (by rfl) ⟨695582, by rfl⟩ : syracuseStep 927443 = 1391165) B1391165
theorem B7022321 : Blo 546805 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B4007693 : Blo 546805 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B927571 : Blo 546805 927571 := bstep (se 1 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 927571 = 1391357) B1391357
theorem B927713 : Blo 546805 927713 := bstep (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) B695785
theorem B1386467 : Blo 546805 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B927841 : Blo 546805 927841 := bstep (se 2 (by rfl) ⟨347940, by rfl⟩ : syracuseStep 927841 = 695881) B695881
theorem B927875 : Blo 546805 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B1386659 : Blo 546805 1386659 := bstep (se 1 (by rfl) ⟨1039994, by rfl⟩ : syracuseStep 1386659 = 2079989) B2079989
theorem B928003 : Blo 546805 928003 := bstep (se 1 (by rfl) ⟨696002, by rfl⟩ : syracuseStep 928003 = 1392005) B1392005
theorem B928145 : Blo 546805 928145 := bstep (se 2 (by rfl) ⟨348054, by rfl⟩ : syracuseStep 928145 = 696109) B696109
theorem B1583555 : Blo 546805 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B1845773 : Blo 546805 1845773 := bstep (se 3 (by rfl) ⟨346082, by rfl⟩ : syracuseStep 1845773 = 692165) B692165
theorem B928273 : Blo 546805 928273 := bstep (se 2 (by rfl) ⟨348102, by rfl⟩ : syracuseStep 928273 = 696205) B696205
theorem B928307 : Blo 546805 928307 := bstep (se 1 (by rfl) ⟨696230, by rfl⟩ : syracuseStep 928307 = 1392461) B1392461
theorem B1845827 : Blo 546805 1845827 := bstep (se 1 (by rfl) ⟨1384370, by rfl⟩ : syracuseStep 1845827 = 2768741) B2768741
theorem B3943025 : Blo 546805 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B928435 : Blo 546805 928435 := bstep (se 1 (by rfl) ⟨696326, by rfl⟩ : syracuseStep 928435 = 1392653) B1392653
theorem B11250373 : Blo 546805 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B928577 : Blo 546805 928577 := bstep (se 2 (by rfl) ⟨348216, by rfl⟩ : syracuseStep 928577 = 696433) B696433
theorem B1846097 : Blo 546805 1846097 := bstep (se 2 (by rfl) ⟨692286, by rfl⟩ : syracuseStep 1846097 = 1384573) B1384573
theorem B6761357 : Blo 546805 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B928705 : Blo 546805 928705 := bstep (se 2 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 928705 = 696529) B696529
theorem B928739 : Blo 546805 928739 := bstep (se 1 (by rfl) ⟨696554, by rfl⟩ : syracuseStep 928739 = 1393109) B1393109
theorem B7056355 : Blo 546805 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B1387601 : Blo 546805 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B928867 : Blo 546805 928867 := bstep (se 1 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 928867 = 1393301) B1393301
theorem B1387651 : Blo 546805 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B929009 : Blo 546805 929009 := bstep (se 2 (by rfl) ⟨348378, by rfl⟩ : syracuseStep 929009 = 696757) B696757
theorem B1387793 : Blo 546805 1387793 := bstep (se 2 (by rfl) ⟨520422, by rfl⟩ : syracuseStep 1387793 = 1040845) B1040845
theorem B1846637 : Blo 546805 1846637 := bstep (se 3 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 1846637 = 692489) B692489
theorem B929137 : Blo 546805 929137 := bstep (se 2 (by rfl) ⟨348426, by rfl⟩ : syracuseStep 929137 = 696853) B696853
theorem B929171 : Blo 546805 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B1846691 : Blo 546805 1846691 := bstep (se 1 (by rfl) ⟨1385018, by rfl⟩ : syracuseStep 1846691 = 2770037) B2770037
theorem B1486289 : Blo 546805 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B929299 : Blo 546805 929299 := bstep (se 1 (by rfl) ⟨696974, by rfl⟩ : syracuseStep 929299 = 1393949) B1393949
theorem B929441 : Blo 546805 929441 := bstep (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) B697081
theorem B1846961 : Blo 546805 1846961 := bstep (se 2 (by rfl) ⟨692610, by rfl⟩ : syracuseStep 1846961 = 1385221) B1385221
theorem B2338723 : Blo 546805 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1880099 : Blo 546805 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B2076785 : Blo 546805 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B1847501 : Blo 546805 1847501 := bstep (se 3 (by rfl) ⟨346406, by rfl⟩ : syracuseStep 1847501 = 692813) B692813
theorem B1388785 : Blo 546805 1388785 := bstep (se 2 (by rfl) ⟨520794, by rfl⟩ : syracuseStep 1388785 = 1041589) B1041589
theorem B1847555 : Blo 546805 1847555 := bstep (se 1 (by rfl) ⟨1385666, by rfl⟩ : syracuseStep 1847555 = 2771333) B2771333
theorem B1389059 : Blo 546805 1389059 := bstep (se 1 (by rfl) ⟨1041794, by rfl⟩ : syracuseStep 1389059 = 2083589) B2083589
theorem B1847825 : Blo 546805 1847825 := bstep (se 2 (by rfl) ⟨692934, by rfl⟩ : syracuseStep 1847825 = 1385869) B1385869
theorem B2667043 : Blo 546805 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B832145 : Blo 546805 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B1389251 : Blo 546805 1389251 := bstep (se 1 (by rfl) ⟨1041938, by rfl⟩ : syracuseStep 1389251 = 2083877) B2083877
theorem B2569073 : Blo 546805 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B1782641 : Blo 546805 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B3388301 : Blo 546805 3388301 := bstep (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) B1270613
theorem B832547 : Blo 546805 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B1848365 : Blo 546805 1848365 := bstep (se 3 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 1848365 = 693137) B693137
theorem B1979441 : Blo 546805 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B1848419 : Blo 546805 1848419 := bstep (se 1 (by rfl) ⟨1386314, by rfl⟩ : syracuseStep 1848419 = 2772629) B2772629
theorem B1848689 : Blo 546805 1848689 := bstep (se 2 (by rfl) ⟨693258, by rfl⟩ : syracuseStep 1848689 = 1386517) B1386517
theorem B2078243 : Blo 546805 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B2078257 : Blo 546805 2078257 := bstep (se 2 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 2078257 = 1558693) B1558693
theorem B1390193 : Blo 546805 1390193 := bstep (se 2 (by rfl) ⟨521322, by rfl⟩ : syracuseStep 1390193 = 1042645) B1042645
theorem B1881731 : Blo 546805 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B1390243 : Blo 546805 1390243 := bstep (se 1 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 1390243 = 2085365) B2085365
theorem B3127045 : Blo 546805 3127045 := bstep (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) B586321
theorem B1390385 : Blo 546805 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B1849229 : Blo 546805 1849229 := bstep (se 3 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 1849229 = 693461) B693461
theorem B2504611 : Blo 546805 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1849283 : Blo 546805 1849283 := bstep (se 1 (by rfl) ⟨1386962, by rfl⟩ : syracuseStep 1849283 = 2773925) B2773925
theorem B1849553 : Blo 546805 1849553 := bstep (se 2 (by rfl) ⟨693582, by rfl⟩ : syracuseStep 1849553 = 1387165) B1387165
theorem B2341169 : Blo 546805 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B4176197 : Blo 546805 4176197 := bstep (se 4 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 4176197 = 783037) B783037
theorem B5257669 : Blo 546805 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B1980899 : Blo 546805 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B1850093 : Blo 546805 1850093 := bstep (se 3 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 1850093 = 693785) B693785
theorem B1391377 : Blo 546805 1391377 := bstep (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) B1043533
theorem B1850147 : Blo 546805 1850147 := bstep (se 1 (by rfl) ⟨1387610, by rfl⟩ : syracuseStep 1850147 = 2775221) B2775221
theorem B2079715 : Blo 546805 2079715 := bstep (se 1 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 2079715 = 3119573) B3119573
theorem B1391651 : Blo 546805 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B1850417 : Blo 546805 1850417 := bstep (se 2 (by rfl) ⟨693906, by rfl⟩ : syracuseStep 1850417 = 1387813) B1387813
theorem B2964707 : Blo 546805 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1391843 : Blo 546805 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1785137 : Blo 546805 1785137 := bstep (se 2 (by rfl) ⟨669426, by rfl⟩ : syracuseStep 1785137 = 1338853) B1338853
theorem B834913 : Blo 546805 834913 := bstep (se 2 (by rfl) ⟨313092, by rfl⟩ : syracuseStep 834913 = 626185) B626185
theorem B8928625 : Blo 546805 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1850957 : Blo 546805 1850957 := bstep (se 3 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 1850957 = 694109) B694109
theorem B1851011 : Blo 546805 1851011 := bstep (se 1 (by rfl) ⟨1388258, by rfl⟩ : syracuseStep 1851011 = 2776517) B2776517
theorem B2375345 : Blo 546805 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B3129029 : Blo 546805 3129029 := bstep (se 4 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 3129029 = 586693) B586693
theorem B1883917 : Blo 546805 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B1752941 : Blo 546805 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B3522437 : Blo 546805 3522437 := bstep (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) B660457
theorem B1851281 : Blo 546805 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B3325859 : Blo 546805 3325859 := bstep (se 1 (by rfl) ⟨2494394, by rfl⟩ : syracuseStep 3325859 = 4988789) B4988789
theorem B1392785 : Blo 546805 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B1392835 : Blo 546805 1392835 := bstep (se 1 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 1392835 = 2089253) B2089253
theorem B835795 : Blo 546805 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B1982755 : Blo 546805 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B1392977 : Blo 546805 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B1851821 : Blo 546805 1851821 := bstep (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) B694433
theorem B1851875 : Blo 546805 1851875 := bstep (se 1 (by rfl) ⟨1388906, by rfl⟩ : syracuseStep 1851875 = 2777813) B2777813
theorem B1786445 : Blo 546805 1786445 := bstep (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) B669917
theorem B1852145 : Blo 546805 1852145 := bstep (se 2 (by rfl) ⟨694554, by rfl⟩ : syracuseStep 1852145 = 1389109) B1389109
theorem B1983217 : Blo 546805 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B2769713 : Blo 546805 2769713 := bstep (se 2 (by rfl) ⟨1038642, by rfl⟩ : syracuseStep 2769713 = 2077285) B2077285
theorem B12633029 : Blo 546805 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B2999281 : Blo 546805 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B2081933 : Blo 546805 2081933 := bstep (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) B780725
theorem B1852685 : Blo 546805 1852685 := bstep (se 3 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 1852685 = 694757) B694757
theorem B1557805 : Blo 546805 1557805 := bstep (se 3 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 1557805 = 584177) B584177
theorem B1393969 : Blo 546805 1393969 := bstep (se 2 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 1393969 = 1045477) B1045477
theorem B1852739 : Blo 546805 1852739 := bstep (se 1 (by rfl) ⟨1389554, by rfl⟩ : syracuseStep 1852739 = 2779109) B2779109
theorem B1984013 : Blo 546805 1984013 := bstep (se 3 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 1984013 = 744005) B744005
theorem B1230353 : Blo 546805 1230353 := bstep (se 2 (by rfl) ⟨461382, by rfl⟩ : syracuseStep 1230353 = 922765) B922765
theorem B1230371 : Blo 546805 1230371 := bstep (se 1 (by rfl) ⟨922778, by rfl⟩ : syracuseStep 1230371 = 1845557) B1845557
theorem B1853009 : Blo 546805 1853009 := bstep (se 2 (by rfl) ⟨694878, by rfl⟩ : syracuseStep 1853009 = 1389757) B1389757
theorem B1230641 : Blo 546805 1230641 := bstep (se 2 (by rfl) ⟨461490, by rfl⟩ : syracuseStep 1230641 = 922981) B922981
theorem B837425 : Blo 546805 837425 := bstep (se 2 (by rfl) ⟨314034, by rfl⟩ : syracuseStep 837425 = 628069) B628069
theorem B1230659 : Blo 546805 1230659 := bstep (se 1 (by rfl) ⟨922994, by rfl⟩ : syracuseStep 1230659 = 1845989) B1845989
theorem B2344909 : Blo 546805 2344909 := bstep (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) B879341
theorem B1230929 : Blo 546805 1230929 := bstep (se 2 (by rfl) ⟨461598, by rfl⟩ : syracuseStep 1230929 = 923197) B923197
theorem B1230947 : Blo 546805 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B1853549 : Blo 546805 1853549 := bstep (se 3 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 1853549 = 695081) B695081
theorem B1853603 : Blo 546805 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B5327045 : Blo 546805 5327045 := bstep (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) B998821
theorem B2771171 : Blo 546805 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B1755427 : Blo 546805 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B1558865 : Blo 546805 1558865 := bstep (se 2 (by rfl) ⟨584574, by rfl⟩ : syracuseStep 1558865 = 1169149) B1169149
theorem B1231217 : Blo 546805 1231217 := bstep (se 2 (by rfl) ⟨461706, by rfl⟩ : syracuseStep 1231217 = 923413) B923413
theorem B1231235 : Blo 546805 1231235 := bstep (se 1 (by rfl) ⟨923426, by rfl⟩ : syracuseStep 1231235 = 1846853) B1846853
theorem B1755569 : Blo 546805 1755569 := bstep (se 2 (by rfl) ⟨658338, by rfl⟩ : syracuseStep 1755569 = 1316677) B1316677
theorem B1853873 : Blo 546805 1853873 := bstep (se 2 (by rfl) ⟨695202, by rfl⟩ : syracuseStep 1853873 = 1390405) B1390405
theorem B739793 : Blo 546805 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B2411021 : Blo 546805 2411021 := bstep (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) B904133
theorem B1755683 : Blo 546805 1755683 := bstep (se 1 (by rfl) ⟨1316762, by rfl⟩ : syracuseStep 1755683 = 2633525) B2633525
theorem B5360197 : Blo 546805 5360197 := bstep (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) B1005037
theorem B1788497 : Blo 546805 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B739939 : Blo 546805 739939 := bstep (se 1 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 739939 = 1109909) B1109909
theorem B3164771 : Blo 546805 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B1231505 : Blo 546805 1231505 := bstep (se 2 (by rfl) ⟨461814, by rfl⟩ : syracuseStep 1231505 = 923629) B923629
theorem B1231523 : Blo 546805 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B608995 : Blo 546805 608995 := bstep (se 1 (by rfl) ⟨456746, by rfl⟩ : syracuseStep 608995 = 913493) B913493
theorem B1231793 : Blo 546805 1231793 := bstep (se 2 (by rfl) ⟨461922, by rfl⟩ : syracuseStep 1231793 = 923845) B923845
theorem B1231811 : Blo 546805 1231811 := bstep (se 1 (by rfl) ⟨923858, by rfl⟩ : syracuseStep 1231811 = 1847717) B1847717
theorem B1854413 : Blo 546805 1854413 := bstep (se 3 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 1854413 = 695405) B695405
theorem B1002449 : Blo 546805 1002449 := bstep (se 2 (by rfl) ⟨375918, by rfl⟩ : syracuseStep 1002449 = 751837) B751837
theorem B1559537 : Blo 546805 1559537 := bstep (se 2 (by rfl) ⟨584826, by rfl⟩ : syracuseStep 1559537 = 1169653) B1169653
theorem B1854467 : Blo 546805 1854467 := bstep (se 1 (by rfl) ⟨1390850, by rfl⟩ : syracuseStep 1854467 = 2781701) B2781701
theorem B4672525 : Blo 546805 4672525 := bstep (se 3 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 4672525 = 1752197) B1752197
theorem B2771981 : Blo 546805 2771981 := bstep (se 3 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 2771981 = 1039493) B1039493
theorem B2247821 : Blo 546805 2247821 := bstep (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) B842933
theorem B1232081 : Blo 546805 1232081 := bstep (se 2 (by rfl) ⟨462030, by rfl⟩ : syracuseStep 1232081 = 924061) B924061
theorem B1232099 : Blo 546805 1232099 := bstep (se 1 (by rfl) ⟨924074, by rfl⟩ : syracuseStep 1232099 = 1848149) B1848149
theorem B5950691 : Blo 546805 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B1854737 : Blo 546805 1854737 := bstep (se 2 (by rfl) ⟨695526, by rfl⟩ : syracuseStep 1854737 = 1391053) B1391053
theorem B3525923 : Blo 546805 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B937313 : Blo 546805 937313 := bstep (se 2 (by rfl) ⟨351492, by rfl⟩ : syracuseStep 937313 = 702985) B702985
theorem B3132877 : Blo 546805 3132877 := bstep (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) B1174829
theorem B1232369 : Blo 546805 1232369 := bstep (se 2 (by rfl) ⟨462138, by rfl⟩ : syracuseStep 1232369 = 924277) B924277
theorem B1756657 : Blo 546805 1756657 := bstep (se 2 (by rfl) ⟨658746, by rfl⟩ : syracuseStep 1756657 = 1317493) B1317493
theorem B1232387 : Blo 546805 1232387 := bstep (se 1 (by rfl) ⟨924290, by rfl⟩ : syracuseStep 1232387 = 1848581) B1848581
theorem B1560323 : Blo 546805 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1232657 : Blo 546805 1232657 := bstep (se 2 (by rfl) ⟨462246, by rfl⟩ : syracuseStep 1232657 = 924493) B924493
theorem B1232675 : Blo 546805 1232675 := bstep (se 1 (by rfl) ⟨924506, by rfl⟩ : syracuseStep 1232675 = 1849013) B1849013
theorem B741155 : Blo 546805 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B1855277 : Blo 546805 1855277 := bstep (se 3 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 1855277 = 695729) B695729
theorem B1855331 : Blo 546805 1855331 := bstep (se 1 (by rfl) ⟨1391498, by rfl⟩ : syracuseStep 1855331 = 2782997) B2782997
theorem B937969 : Blo 546805 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B2084849 : Blo 546805 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B4182029 : Blo 546805 4182029 := bstep (se 3 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 4182029 = 1568261) B1568261
theorem B2969635 : Blo 546805 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1232945 : Blo 546805 1232945 := bstep (se 2 (by rfl) ⟨462354, by rfl⟩ : syracuseStep 1232945 = 924709) B924709
theorem B1232963 : Blo 546805 1232963 := bstep (se 1 (by rfl) ⟨924722, by rfl⟩ : syracuseStep 1232963 = 1849445) B1849445
theorem B1560653 : Blo 546805 1560653 := bstep (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) B585245
theorem B1855601 : Blo 546805 1855601 := bstep (se 2 (by rfl) ⟨695850, by rfl⟩ : syracuseStep 1855601 = 1391701) B1391701
theorem B1560721 : Blo 546805 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B12669155 : Blo 546805 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B4673861 : Blo 546805 4673861 := bstep (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) B876349
theorem B1233233 : Blo 546805 1233233 := bstep (se 2 (by rfl) ⟨462462, by rfl⟩ : syracuseStep 1233233 = 924925) B924925
theorem B1233251 : Blo 546805 1233251 := bstep (se 1 (by rfl) ⟨924938, by rfl⟩ : syracuseStep 1233251 = 1849877) B1849877
theorem B1560995 : Blo 546805 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B17125829 : Blo 546805 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B1233521 : Blo 546805 1233521 := bstep (se 2 (by rfl) ⟨462570, by rfl⟩ : syracuseStep 1233521 = 925141) B925141
theorem B1233539 : Blo 546805 1233539 := bstep (se 1 (by rfl) ⟨925154, by rfl⟩ : syracuseStep 1233539 = 1850309) B1850309
theorem B1856141 : Blo 546805 1856141 := bstep (se 3 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 1856141 = 696053) B696053
theorem B1856195 : Blo 546805 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1233809 : Blo 546805 1233809 := bstep (se 2 (by rfl) ⟨462678, by rfl⟩ : syracuseStep 1233809 = 925357) B925357
theorem B1233827 : Blo 546805 1233827 := bstep (se 1 (by rfl) ⟨925370, by rfl⟩ : syracuseStep 1233827 = 1850741) B1850741
theorem B1168337 : Blo 546805 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B1856465 : Blo 546805 1856465 := bstep (se 2 (by rfl) ⟨696174, by rfl⟩ : syracuseStep 1856465 = 1392349) B1392349
theorem B1234097 : Blo 546805 1234097 := bstep (se 2 (by rfl) ⟨462786, by rfl⟩ : syracuseStep 1234097 = 925573) B925573
theorem B1234115 : Blo 546805 1234115 := bstep (se 1 (by rfl) ⟨925586, by rfl⟩ : syracuseStep 1234115 = 1851173) B1851173
theorem B1561837 : Blo 546805 1561837 := bstep (se 3 (by rfl) ⟨292844, by rfl⟩ : syracuseStep 1561837 = 585689) B585689
theorem B1168739 : Blo 546805 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B1561997 : Blo 546805 1561997 := bstep (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) B585749
theorem B3134861 : Blo 546805 3134861 := bstep (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) B1175573
theorem B2086307 : Blo 546805 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B1234385 : Blo 546805 1234385 := bstep (se 2 (by rfl) ⟨462894, by rfl⟩ : syracuseStep 1234385 = 925789) B925789
theorem B1234403 : Blo 546805 1234403 := bstep (se 1 (by rfl) ⟨925802, by rfl⟩ : syracuseStep 1234403 = 1851605) B1851605
theorem B1857005 : Blo 546805 1857005 := bstep (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) B696377
theorem B1857059 : Blo 546805 1857059 := bstep (se 1 (by rfl) ⟨1392794, by rfl⟩ : syracuseStep 1857059 = 2785589) B2785589
theorem B1562179 : Blo 546805 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B1234673 : Blo 546805 1234673 := bstep (se 2 (by rfl) ⟨463002, by rfl⟩ : syracuseStep 1234673 = 926005) B926005
theorem B1234691 : Blo 546805 1234691 := bstep (se 1 (by rfl) ⟨926018, by rfl⟩ : syracuseStep 1234691 = 1852037) B1852037
theorem B1857329 : Blo 546805 1857329 := bstep (se 2 (by rfl) ⟨696498, by rfl⟩ : syracuseStep 1857329 = 1392997) B1392997
theorem B2774897 : Blo 546805 2774897 := bstep (se 2 (by rfl) ⟨1040586, by rfl⟩ : syracuseStep 2774897 = 2081173) B2081173
theorem B546819 : Blo 546805 546819 := bstep (se 1 (by rfl) ⟨410114, by rfl⟩ : syracuseStep 546819 = 820229) B820229
theorem B1234961 : Blo 546805 1234961 := bstep (se 2 (by rfl) ⟨463110, by rfl⟩ : syracuseStep 1234961 = 926221) B926221
theorem B546835 : Blo 546805 546835 := bstep (se 1 (by rfl) ⟨410126, by rfl⟩ : syracuseStep 546835 = 820253) B820253
theorem B546851 : Blo 546805 546851 := bstep (se 1 (by rfl) ⟨410138, by rfl⟩ : syracuseStep 546851 = 820277) B820277
theorem B1234979 : Blo 546805 1234979 := bstep (se 1 (by rfl) ⟨926234, by rfl⟩ : syracuseStep 1234979 = 1852469) B1852469
theorem B546867 : Blo 546805 546867 := bstep (se 1 (by rfl) ⟨410150, by rfl⟩ : syracuseStep 546867 = 820301) B820301
theorem B546883 : Blo 546805 546883 := bstep (se 1 (by rfl) ⟨410162, by rfl⟩ : syracuseStep 546883 = 820325) B820325
theorem B546899 : Blo 546805 546899 := bstep (se 1 (by rfl) ⟨410174, by rfl⟩ : syracuseStep 546899 = 820349) B820349
theorem B546915 : Blo 546805 546915 := bstep (se 1 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 546915 = 820373) B820373
theorem B546931 : Blo 546805 546931 := bstep (se 1 (by rfl) ⟨410198, by rfl⟩ : syracuseStep 546931 = 820397) B820397
theorem B546947 : Blo 546805 546947 := bstep (se 1 (by rfl) ⟨410210, by rfl⟩ : syracuseStep 546947 = 820421) B820421
theorem B546963 : Blo 546805 546963 := bstep (se 1 (by rfl) ⟨410222, by rfl⟩ : syracuseStep 546963 = 820445) B820445
theorem B546979 : Blo 546805 546979 := bstep (se 1 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 546979 = 820469) B820469
theorem B2349233 : Blo 546805 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B546995 : Blo 546805 546995 := bstep (se 1 (by rfl) ⟨410246, by rfl⟩ : syracuseStep 546995 = 820493) B820493
theorem B547011 : Blo 546805 547011 := bstep (se 1 (by rfl) ⟨410258, by rfl⟩ : syracuseStep 547011 = 820517) B820517
theorem B547027 : Blo 546805 547027 := bstep (se 1 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 547027 = 820541) B820541
theorem B547043 : Blo 546805 547043 := bstep (se 1 (by rfl) ⟨410282, by rfl⟩ : syracuseStep 547043 = 820565) B820565
theorem B1169635 : Blo 546805 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B2349283 : Blo 546805 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B547059 : Blo 546805 547059 := bstep (se 1 (by rfl) ⟨410294, by rfl⟩ : syracuseStep 547059 = 820589) B820589
theorem B547075 : Blo 546805 547075 := bstep (se 1 (by rfl) ⟨410306, by rfl⟩ : syracuseStep 547075 = 820613) B820613
theorem B547091 : Blo 546805 547091 := bstep (se 1 (by rfl) ⟨410318, by rfl⟩ : syracuseStep 547091 = 820637) B820637
theorem B547107 : Blo 546805 547107 := bstep (se 1 (by rfl) ⟨410330, by rfl⟩ : syracuseStep 547107 = 820661) B820661
theorem B1235249 : Blo 546805 1235249 := bstep (se 2 (by rfl) ⟨463218, by rfl⟩ : syracuseStep 1235249 = 926437) B926437
theorem B3135793 : Blo 546805 3135793 := bstep (se 2 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 3135793 = 2351845) B2351845
theorem B547123 : Blo 546805 547123 := bstep (se 1 (by rfl) ⟨410342, by rfl⟩ : syracuseStep 547123 = 820685) B820685
theorem B547139 : Blo 546805 547139 := bstep (se 1 (by rfl) ⟨410354, by rfl⟩ : syracuseStep 547139 = 820709) B820709
theorem B1235267 : Blo 546805 1235267 := bstep (se 1 (by rfl) ⟨926450, by rfl⟩ : syracuseStep 1235267 = 1852901) B1852901
theorem B1857869 : Blo 546805 1857869 := bstep (se 3 (by rfl) ⟨348350, by rfl⟩ : syracuseStep 1857869 = 696701) B696701
theorem B1038673 : Blo 546805 1038673 := bstep (se 2 (by rfl) ⟨389502, by rfl⟩ : syracuseStep 1038673 = 779005) B779005
theorem B547155 : Blo 546805 547155 := bstep (se 1 (by rfl) ⟨410366, by rfl⟩ : syracuseStep 547155 = 820733) B820733
theorem B547171 : Blo 546805 547171 := bstep (se 1 (by rfl) ⟨410378, by rfl⟩ : syracuseStep 547171 = 820757) B820757
theorem B547187 : Blo 546805 547187 := bstep (se 1 (by rfl) ⟨410390, by rfl⟩ : syracuseStep 547187 = 820781) B820781
theorem B547203 : Blo 546805 547203 := bstep (se 1 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 547203 = 820805) B820805
theorem B1857923 : Blo 546805 1857923 := bstep (se 1 (by rfl) ⟨1393442, by rfl⟩ : syracuseStep 1857923 = 2786885) B2786885
theorem B2087309 : Blo 546805 2087309 := bstep (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) B782741
theorem B547219 : Blo 546805 547219 := bstep (se 1 (by rfl) ⟨410414, by rfl⟩ : syracuseStep 547219 = 820829) B820829
theorem B547235 : Blo 546805 547235 := bstep (se 1 (by rfl) ⟨410426, by rfl⟩ : syracuseStep 547235 = 820853) B820853
theorem B547251 : Blo 546805 547251 := bstep (se 1 (by rfl) ⟨410438, by rfl⟩ : syracuseStep 547251 = 820877) B820877
theorem B547267 : Blo 546805 547267 := bstep (se 1 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 547267 = 820901) B820901
theorem B547283 : Blo 546805 547283 := bstep (se 1 (by rfl) ⟨410462, by rfl⟩ : syracuseStep 547283 = 820925) B820925
theorem B547299 : Blo 546805 547299 := bstep (se 1 (by rfl) ⟨410474, by rfl⟩ : syracuseStep 547299 = 820949) B820949
theorem B547315 : Blo 546805 547315 := bstep (se 1 (by rfl) ⟨410486, by rfl⟩ : syracuseStep 547315 = 820973) B820973
theorem B547331 : Blo 546805 547331 := bstep (se 1 (by rfl) ⟨410498, by rfl⟩ : syracuseStep 547331 = 820997) B820997
theorem B547347 : Blo 546805 547347 := bstep (se 1 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 547347 = 821021) B821021
theorem B547363 : Blo 546805 547363 := bstep (se 1 (by rfl) ⟨410522, by rfl⟩ : syracuseStep 547363 = 821045) B821045
theorem B547379 : Blo 546805 547379 := bstep (se 1 (by rfl) ⟨410534, by rfl⟩ : syracuseStep 547379 = 821069) B821069
theorem B547395 : Blo 546805 547395 := bstep (se 1 (by rfl) ⟨410546, by rfl⟩ : syracuseStep 547395 = 821093) B821093
theorem B3758669 : Blo 546805 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1235537 : Blo 546805 1235537 := bstep (se 2 (by rfl) ⟨463326, by rfl⟩ : syracuseStep 1235537 = 926653) B926653
theorem B547411 : Blo 546805 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B547427 : Blo 546805 547427 := bstep (se 1 (by rfl) ⟨410570, by rfl⟩ : syracuseStep 547427 = 821141) B821141
theorem B1235555 : Blo 546805 1235555 := bstep (se 1 (by rfl) ⟨926666, by rfl⟩ : syracuseStep 1235555 = 1853333) B1853333
theorem B547443 : Blo 546805 547443 := bstep (se 1 (by rfl) ⟨410582, by rfl⟩ : syracuseStep 547443 = 821165) B821165
theorem B547459 : Blo 546805 547459 := bstep (se 1 (by rfl) ⟨410594, by rfl⟩ : syracuseStep 547459 = 821189) B821189
theorem B1858193 : Blo 546805 1858193 := bstep (se 2 (by rfl) ⟨696822, by rfl⟩ : syracuseStep 1858193 = 1393645) B1393645
theorem B547475 : Blo 546805 547475 := bstep (se 1 (by rfl) ⟨410606, by rfl⟩ : syracuseStep 547475 = 821213) B821213
theorem B547491 : Blo 546805 547491 := bstep (se 1 (by rfl) ⟨410618, by rfl⟩ : syracuseStep 547491 = 821237) B821237
theorem B547507 : Blo 546805 547507 := bstep (se 1 (by rfl) ⟨410630, by rfl⟩ : syracuseStep 547507 = 821261) B821261
theorem B547523 : Blo 546805 547523 := bstep (se 1 (by rfl) ⟨410642, by rfl⟩ : syracuseStep 547523 = 821285) B821285
theorem B547539 : Blo 546805 547539 := bstep (se 1 (by rfl) ⟨410654, by rfl⟩ : syracuseStep 547539 = 821309) B821309
theorem B744161 : Blo 546805 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B547555 : Blo 546805 547555 := bstep (se 1 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 547555 = 821333) B821333
theorem B547571 : Blo 546805 547571 := bstep (se 1 (by rfl) ⟨410678, by rfl⟩ : syracuseStep 547571 = 821357) B821357
theorem B547587 : Blo 546805 547587 := bstep (se 1 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 547587 = 821381) B821381
theorem B940817 : Blo 546805 940817 := bstep (se 2 (by rfl) ⟨352806, by rfl⟩ : syracuseStep 940817 = 705613) B705613
theorem B547603 : Blo 546805 547603 := bstep (se 1 (by rfl) ⟨410702, by rfl⟩ : syracuseStep 547603 = 821405) B821405
theorem B547619 : Blo 546805 547619 := bstep (se 1 (by rfl) ⟨410714, by rfl⟩ : syracuseStep 547619 = 821429) B821429
theorem B547635 : Blo 546805 547635 := bstep (se 1 (by rfl) ⟨410726, by rfl⟩ : syracuseStep 547635 = 821453) B821453
theorem B547651 : Blo 546805 547651 := bstep (se 1 (by rfl) ⟨410738, by rfl⟩ : syracuseStep 547651 = 821477) B821477
theorem B547667 : Blo 546805 547667 := bstep (se 1 (by rfl) ⟨410750, by rfl⟩ : syracuseStep 547667 = 821501) B821501
theorem B547683 : Blo 546805 547683 := bstep (se 1 (by rfl) ⟨410762, by rfl⟩ : syracuseStep 547683 = 821525) B821525
theorem B1235825 : Blo 546805 1235825 := bstep (se 2 (by rfl) ⟨463434, by rfl⟩ : syracuseStep 1235825 = 926869) B926869
theorem B547699 : Blo 546805 547699 := bstep (se 1 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 547699 = 821549) B821549
theorem B547715 : Blo 546805 547715 := bstep (se 1 (by rfl) ⟨410786, by rfl⟩ : syracuseStep 547715 = 821573) B821573
theorem B1235843 : Blo 546805 1235843 := bstep (se 1 (by rfl) ⟨926882, by rfl⟩ : syracuseStep 1235843 = 1853765) B1853765
theorem B547731 : Blo 546805 547731 := bstep (se 1 (by rfl) ⟨410798, by rfl⟩ : syracuseStep 547731 = 821597) B821597
theorem B547747 : Blo 546805 547747 := bstep (se 1 (by rfl) ⟨410810, by rfl⟩ : syracuseStep 547747 = 821621) B821621
theorem B1563569 : Blo 546805 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B547763 : Blo 546805 547763 := bstep (se 1 (by rfl) ⟨410822, by rfl⟩ : syracuseStep 547763 = 821645) B821645
theorem B547779 : Blo 546805 547779 := bstep (se 1 (by rfl) ⟨410834, by rfl⟩ : syracuseStep 547779 = 821669) B821669
theorem B1334225 : Blo 546805 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B547795 : Blo 546805 547795 := bstep (se 1 (by rfl) ⟨410846, by rfl⟩ : syracuseStep 547795 = 821693) B821693
theorem B547811 : Blo 546805 547811 := bstep (se 1 (by rfl) ⟨410858, by rfl⟩ : syracuseStep 547811 = 821717) B821717
theorem B547827 : Blo 546805 547827 := bstep (se 1 (by rfl) ⟨410870, by rfl⟩ : syracuseStep 547827 = 821741) B821741
theorem B547843 : Blo 546805 547843 := bstep (se 1 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 547843 = 821765) B821765
theorem B547859 : Blo 546805 547859 := bstep (se 1 (by rfl) ⟨410894, by rfl⟩ : syracuseStep 547859 = 821789) B821789
theorem B547875 : Blo 546805 547875 := bstep (se 1 (by rfl) ⟨410906, by rfl⟩ : syracuseStep 547875 = 821813) B821813
theorem B547891 : Blo 546805 547891 := bstep (se 1 (by rfl) ⟨410918, by rfl⟩ : syracuseStep 547891 = 821837) B821837
theorem B547907 : Blo 546805 547907 := bstep (se 1 (by rfl) ⟨410930, by rfl⟩ : syracuseStep 547907 = 821861) B821861
theorem B547923 : Blo 546805 547923 := bstep (se 1 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 547923 = 821885) B821885
theorem B547939 : Blo 546805 547939 := bstep (se 1 (by rfl) ⟨410954, by rfl⟩ : syracuseStep 547939 = 821909) B821909
theorem B547955 : Blo 546805 547955 := bstep (se 1 (by rfl) ⟨410966, by rfl⟩ : syracuseStep 547955 = 821933) B821933
theorem B547971 : Blo 546805 547971 := bstep (se 1 (by rfl) ⟨410978, by rfl⟩ : syracuseStep 547971 = 821957) B821957
theorem B1236113 : Blo 546805 1236113 := bstep (se 2 (by rfl) ⟨463542, by rfl⟩ : syracuseStep 1236113 = 927085) B927085
theorem B547987 : Blo 546805 547987 := bstep (se 1 (by rfl) ⟨410990, by rfl⟩ : syracuseStep 547987 = 821981) B821981
theorem B548003 : Blo 546805 548003 := bstep (se 1 (by rfl) ⟨411002, by rfl⟩ : syracuseStep 548003 = 822005) B822005
theorem B1236131 : Blo 546805 1236131 := bstep (se 1 (by rfl) ⟨927098, by rfl⟩ : syracuseStep 1236131 = 1854197) B1854197
theorem B1858733 : Blo 546805 1858733 := bstep (se 3 (by rfl) ⟨348512, by rfl⟩ : syracuseStep 1858733 = 697025) B697025
theorem B548019 : Blo 546805 548019 := bstep (se 1 (by rfl) ⟨411014, by rfl⟩ : syracuseStep 548019 = 822029) B822029
theorem B548035 : Blo 546805 548035 := bstep (se 1 (by rfl) ⟨411026, by rfl⟩ : syracuseStep 548035 = 822053) B822053
theorem B548051 : Blo 546805 548051 := bstep (se 1 (by rfl) ⟨411038, by rfl⟩ : syracuseStep 548051 = 822077) B822077
theorem B548067 : Blo 546805 548067 := bstep (se 1 (by rfl) ⟨411050, by rfl⟩ : syracuseStep 548067 = 822101) B822101
theorem B1858787 : Blo 546805 1858787 := bstep (se 1 (by rfl) ⟨1394090, by rfl⟩ : syracuseStep 1858787 = 2788181) B2788181
theorem B548083 : Blo 546805 548083 := bstep (se 1 (by rfl) ⟨411062, by rfl⟩ : syracuseStep 548083 = 822125) B822125
theorem B548099 : Blo 546805 548099 := bstep (se 1 (by rfl) ⟨411074, by rfl⟩ : syracuseStep 548099 = 822149) B822149
theorem B548115 : Blo 546805 548115 := bstep (se 1 (by rfl) ⟨411086, by rfl⟩ : syracuseStep 548115 = 822173) B822173
theorem B548131 : Blo 546805 548131 := bstep (se 1 (by rfl) ⟨411098, by rfl⟩ : syracuseStep 548131 = 822197) B822197
theorem B2776355 : Blo 546805 2776355 := bstep (se 1 (by rfl) ⟨2082266, by rfl⟩ : syracuseStep 2776355 = 4164533) B4164533
theorem B548147 : Blo 546805 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B548163 : Blo 546805 548163 := bstep (se 1 (by rfl) ⟨411122, by rfl⟩ : syracuseStep 548163 = 822245) B822245
theorem B548179 : Blo 546805 548179 := bstep (se 1 (by rfl) ⟨411134, by rfl⟩ : syracuseStep 548179 = 822269) B822269
theorem B548195 : Blo 546805 548195 := bstep (se 1 (by rfl) ⟨411146, by rfl⟩ : syracuseStep 548195 = 822293) B822293
theorem B1039729 : Blo 546805 1039729 := bstep (se 2 (by rfl) ⟨389898, by rfl⟩ : syracuseStep 1039729 = 779797) B779797
theorem B548211 : Blo 546805 548211 := bstep (se 1 (by rfl) ⟨411158, by rfl⟩ : syracuseStep 548211 = 822317) B822317
theorem B548227 : Blo 546805 548227 := bstep (se 1 (by rfl) ⟨411170, by rfl⟩ : syracuseStep 548227 = 822341) B822341
theorem B548243 : Blo 546805 548243 := bstep (se 1 (by rfl) ⟨411182, by rfl⟩ : syracuseStep 548243 = 822365) B822365
theorem B875939 : Blo 546805 875939 := bstep (se 1 (by rfl) ⟨656954, by rfl⟩ : syracuseStep 875939 = 1313909) B1313909
theorem B548259 : Blo 546805 548259 := bstep (se 1 (by rfl) ⟨411194, by rfl⟩ : syracuseStep 548259 = 822389) B822389
theorem B1170865 : Blo 546805 1170865 := bstep (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) B878149
theorem B548275 : Blo 546805 548275 := bstep (se 1 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 548275 = 822413) B822413
theorem B1236401 : Blo 546805 1236401 := bstep (se 2 (by rfl) ⟨463650, by rfl⟩ : syracuseStep 1236401 = 927301) B927301
theorem B875971 : Blo 546805 875971 := bstep (se 1 (by rfl) ⟨656978, by rfl⟩ : syracuseStep 875971 = 1313957) B1313957
theorem B548291 : Blo 546805 548291 := bstep (se 1 (by rfl) ⟨411218, by rfl⟩ : syracuseStep 548291 = 822437) B822437
theorem B1236419 : Blo 546805 1236419 := bstep (se 1 (by rfl) ⟨927314, by rfl⟩ : syracuseStep 1236419 = 1854629) B1854629
theorem B548307 : Blo 546805 548307 := bstep (se 1 (by rfl) ⟨411230, by rfl⟩ : syracuseStep 548307 = 822461) B822461
theorem B548323 : Blo 546805 548323 := bstep (se 1 (by rfl) ⟨411242, by rfl⟩ : syracuseStep 548323 = 822485) B822485
theorem B548339 : Blo 546805 548339 := bstep (se 1 (by rfl) ⟨411254, by rfl⟩ : syracuseStep 548339 = 822509) B822509
theorem B548355 : Blo 546805 548355 := bstep (se 1 (by rfl) ⟨411266, by rfl⟩ : syracuseStep 548355 = 822533) B822533
theorem B548371 : Blo 546805 548371 := bstep (se 1 (by rfl) ⟨411278, by rfl⟩ : syracuseStep 548371 = 822557) B822557
theorem B548387 : Blo 546805 548387 := bstep (se 1 (by rfl) ⟨411290, by rfl⟩ : syracuseStep 548387 = 822581) B822581
theorem B548403 : Blo 546805 548403 := bstep (se 1 (by rfl) ⟨411302, by rfl⟩ : syracuseStep 548403 = 822605) B822605
theorem B7036469 : Blo 546805 7036469 := bstep (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) B659669
theorem B548419 : Blo 546805 548419 := bstep (se 1 (by rfl) ⟨411314, by rfl⟩ : syracuseStep 548419 = 822629) B822629
theorem B548435 : Blo 546805 548435 := bstep (se 1 (by rfl) ⟨411326, by rfl⟩ : syracuseStep 548435 = 822653) B822653
theorem B548451 : Blo 546805 548451 := bstep (se 1 (by rfl) ⟨411338, by rfl⟩ : syracuseStep 548451 = 822677) B822677
theorem B548467 : Blo 546805 548467 := bstep (se 1 (by rfl) ⟨411350, by rfl⟩ : syracuseStep 548467 = 822701) B822701
theorem B548483 : Blo 546805 548483 := bstep (se 1 (by rfl) ⟨411362, by rfl⟩ : syracuseStep 548483 = 822725) B822725
theorem B548499 : Blo 546805 548499 := bstep (se 1 (by rfl) ⟨411374, by rfl⟩ : syracuseStep 548499 = 822749) B822749
theorem B548515 : Blo 546805 548515 := bstep (se 1 (by rfl) ⟨411386, by rfl⟩ : syracuseStep 548515 = 822773) B822773
theorem B548531 : Blo 546805 548531 := bstep (se 1 (by rfl) ⟨411398, by rfl⟩ : syracuseStep 548531 = 822797) B822797
theorem B548547 : Blo 546805 548547 := bstep (se 1 (by rfl) ⟨411410, by rfl⟩ : syracuseStep 548547 = 822821) B822821
theorem B1236689 : Blo 546805 1236689 := bstep (se 2 (by rfl) ⟨463758, by rfl⟩ : syracuseStep 1236689 = 927517) B927517
theorem B548563 : Blo 546805 548563 := bstep (se 1 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 548563 = 822845) B822845
theorem B548579 : Blo 546805 548579 := bstep (se 1 (by rfl) ⟨411434, by rfl⟩ : syracuseStep 548579 = 822869) B822869
theorem B1236707 : Blo 546805 1236707 := bstep (se 1 (by rfl) ⟨927530, by rfl⟩ : syracuseStep 1236707 = 1855061) B1855061
theorem B548595 : Blo 546805 548595 := bstep (se 1 (by rfl) ⟨411446, by rfl⟩ : syracuseStep 548595 = 822893) B822893
theorem B1040131 : Blo 546805 1040131 := bstep (se 1 (by rfl) ⟨780098, by rfl⟩ : syracuseStep 1040131 = 1560197) B1560197
theorem B548611 : Blo 546805 548611 := bstep (se 1 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 548611 = 822917) B822917
theorem B1924877 : Blo 546805 1924877 := bstep (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) B721829
theorem B1761041 : Blo 546805 1761041 := bstep (se 2 (by rfl) ⟨660390, by rfl⟩ : syracuseStep 1761041 = 1320781) B1320781
theorem B548627 : Blo 546805 548627 := bstep (se 1 (by rfl) ⟨411470, by rfl⟩ : syracuseStep 548627 = 822941) B822941
theorem B548643 : Blo 546805 548643 := bstep (se 1 (by rfl) ⟨411482, by rfl⟩ : syracuseStep 548643 = 822965) B822965
theorem B1040177 : Blo 546805 1040177 := bstep (se 2 (by rfl) ⟨390066, by rfl⟩ : syracuseStep 1040177 = 780133) B780133
theorem B548659 : Blo 546805 548659 := bstep (se 1 (by rfl) ⟨411494, by rfl⟩ : syracuseStep 548659 = 822989) B822989
theorem B548675 : Blo 546805 548675 := bstep (se 1 (by rfl) ⟨411506, by rfl⟩ : syracuseStep 548675 = 823013) B823013
theorem B548691 : Blo 546805 548691 := bstep (se 1 (by rfl) ⟨411518, by rfl⟩ : syracuseStep 548691 = 823037) B823037
theorem B548707 : Blo 546805 548707 := bstep (se 1 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 548707 = 823061) B823061
theorem B1564525 : Blo 546805 1564525 := bstep (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) B586697
theorem B548723 : Blo 546805 548723 := bstep (se 1 (by rfl) ⟨411542, by rfl⟩ : syracuseStep 548723 = 823085) B823085
theorem B548739 : Blo 546805 548739 := bstep (se 1 (by rfl) ⟨411554, by rfl⟩ : syracuseStep 548739 = 823109) B823109
theorem B548755 : Blo 546805 548755 := bstep (se 1 (by rfl) ⟨411566, by rfl⟩ : syracuseStep 548755 = 823133) B823133
theorem B548771 : Blo 546805 548771 := bstep (se 1 (by rfl) ⟨411578, by rfl⟩ : syracuseStep 548771 = 823157) B823157
theorem B548787 : Blo 546805 548787 := bstep (se 1 (by rfl) ⟨411590, by rfl⟩ : syracuseStep 548787 = 823181) B823181
theorem B548803 : Blo 546805 548803 := bstep (se 1 (by rfl) ⟨411602, by rfl⟩ : syracuseStep 548803 = 823205) B823205
theorem B3170245 : Blo 546805 3170245 := bstep (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) B594421
theorem B548819 : Blo 546805 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B548835 : Blo 546805 548835 := bstep (se 1 (by rfl) ⟨411626, by rfl⟩ : syracuseStep 548835 = 823253) B823253
theorem B1236977 : Blo 546805 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B548851 : Blo 546805 548851 := bstep (se 1 (by rfl) ⟨411638, by rfl⟩ : syracuseStep 548851 = 823277) B823277
theorem B548867 : Blo 546805 548867 := bstep (se 1 (by rfl) ⟨411650, by rfl⟩ : syracuseStep 548867 = 823301) B823301
theorem B1236995 : Blo 546805 1236995 := bstep (se 1 (by rfl) ⟨927746, by rfl⟩ : syracuseStep 1236995 = 1855493) B1855493
theorem B548883 : Blo 546805 548883 := bstep (se 1 (by rfl) ⟨411662, by rfl⟩ : syracuseStep 548883 = 823325) B823325
theorem B548899 : Blo 546805 548899 := bstep (se 1 (by rfl) ⟨411674, by rfl⟩ : syracuseStep 548899 = 823349) B823349
theorem B548915 : Blo 546805 548915 := bstep (se 1 (by rfl) ⟨411686, by rfl⟩ : syracuseStep 548915 = 823373) B823373
theorem B942131 : Blo 546805 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B548931 : Blo 546805 548931 := bstep (se 1 (by rfl) ⟨411698, by rfl⟩ : syracuseStep 548931 = 823397) B823397
theorem B2777165 : Blo 546805 2777165 := bstep (se 3 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 2777165 = 1041437) B1041437
theorem B1040465 : Blo 546805 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B1564753 : Blo 546805 1564753 := bstep (se 2 (by rfl) ⟨586782, by rfl⟩ : syracuseStep 1564753 = 1173565) B1173565
theorem B548947 : Blo 546805 548947 := bstep (se 1 (by rfl) ⟨411710, by rfl⟩ : syracuseStep 548947 = 823421) B823421
theorem B548963 : Blo 546805 548963 := bstep (se 1 (by rfl) ⟨411722, by rfl⟩ : syracuseStep 548963 = 823445) B823445
theorem B548979 : Blo 546805 548979 := bstep (se 1 (by rfl) ⟨411734, by rfl⟩ : syracuseStep 548979 = 823469) B823469
theorem B548995 : Blo 546805 548995 := bstep (se 1 (by rfl) ⟨411746, by rfl⟩ : syracuseStep 548995 = 823493) B823493
theorem B549011 : Blo 546805 549011 := bstep (se 1 (by rfl) ⟨411758, by rfl⟩ : syracuseStep 549011 = 823517) B823517
theorem B549027 : Blo 546805 549027 := bstep (se 1 (by rfl) ⟨411770, by rfl⟩ : syracuseStep 549027 = 823541) B823541
theorem B2220209 : Blo 546805 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B549043 : Blo 546805 549043 := bstep (se 1 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 549043 = 823565) B823565
theorem B549059 : Blo 546805 549059 := bstep (se 1 (by rfl) ⟨411794, by rfl⟩ : syracuseStep 549059 = 823589) B823589
theorem B549075 : Blo 546805 549075 := bstep (se 1 (by rfl) ⟨411806, by rfl⟩ : syracuseStep 549075 = 823613) B823613
theorem B549091 : Blo 546805 549091 := bstep (se 1 (by rfl) ⟨411818, by rfl⟩ : syracuseStep 549091 = 823637) B823637
theorem B1564913 : Blo 546805 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B549107 : Blo 546805 549107 := bstep (se 1 (by rfl) ⟨411830, by rfl⟩ : syracuseStep 549107 = 823661) B823661
theorem B549123 : Blo 546805 549123 := bstep (se 1 (by rfl) ⟨411842, by rfl⟩ : syracuseStep 549123 = 823685) B823685
theorem B1237265 : Blo 546805 1237265 := bstep (se 2 (by rfl) ⟨463974, by rfl⟩ : syracuseStep 1237265 = 927949) B927949
theorem B549139 : Blo 546805 549139 := bstep (se 1 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 549139 = 823709) B823709
theorem B549155 : Blo 546805 549155 := bstep (se 1 (by rfl) ⟨411866, by rfl⟩ : syracuseStep 549155 = 823733) B823733
theorem B1237283 : Blo 546805 1237283 := bstep (se 1 (by rfl) ⟨927962, by rfl⟩ : syracuseStep 1237283 = 1855925) B1855925
theorem B549171 : Blo 546805 549171 := bstep (se 1 (by rfl) ⟨411878, by rfl⟩ : syracuseStep 549171 = 823757) B823757
theorem B549187 : Blo 546805 549187 := bstep (se 1 (by rfl) ⟨411890, by rfl⟩ : syracuseStep 549187 = 823781) B823781
theorem B876881 : Blo 546805 876881 := bstep (se 2 (by rfl) ⟨328830, by rfl⟩ : syracuseStep 876881 = 657661) B657661
theorem B549203 : Blo 546805 549203 := bstep (se 1 (by rfl) ⟨411902, by rfl⟩ : syracuseStep 549203 = 823805) B823805
theorem B549219 : Blo 546805 549219 := bstep (se 1 (by rfl) ⟨411914, by rfl⟩ : syracuseStep 549219 = 823829) B823829
theorem B1565027 : Blo 546805 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B1696099 : Blo 546805 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B549235 : Blo 546805 549235 := bstep (se 1 (by rfl) ⟨411926, by rfl⟩ : syracuseStep 549235 = 823853) B823853
theorem B549251 : Blo 546805 549251 := bstep (se 1 (by rfl) ⟨411938, by rfl⟩ : syracuseStep 549251 = 823877) B823877
theorem B549267 : Blo 546805 549267 := bstep (se 1 (by rfl) ⟨411950, by rfl⟩ : syracuseStep 549267 = 823901) B823901
theorem B549283 : Blo 546805 549283 := bstep (se 1 (by rfl) ⟨411962, by rfl⟩ : syracuseStep 549283 = 823925) B823925
theorem B778675 : Blo 546805 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B549299 : Blo 546805 549299 := bstep (se 1 (by rfl) ⟨411974, by rfl⟩ : syracuseStep 549299 = 823949) B823949
theorem B549315 : Blo 546805 549315 := bstep (se 1 (by rfl) ⟨411986, by rfl⟩ : syracuseStep 549315 = 823973) B823973
theorem B2089421 : Blo 546805 2089421 := bstep (se 3 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 2089421 = 783533) B783533
theorem B549331 : Blo 546805 549331 := bstep (se 1 (by rfl) ⟨411998, by rfl⟩ : syracuseStep 549331 = 823997) B823997
theorem B549347 : Blo 546805 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B4153841 : Blo 546805 4153841 := bstep (se 2 (by rfl) ⟨1557690, by rfl⟩ : syracuseStep 4153841 = 3115381) B3115381
theorem B549363 : Blo 546805 549363 := bstep (se 1 (by rfl) ⟨412022, by rfl⟩ : syracuseStep 549363 = 824045) B824045
theorem B549379 : Blo 546805 549379 := bstep (se 1 (by rfl) ⟨412034, by rfl⟩ : syracuseStep 549379 = 824069) B824069
theorem B549395 : Blo 546805 549395 := bstep (se 1 (by rfl) ⟨412046, by rfl⟩ : syracuseStep 549395 = 824093) B824093
theorem B549411 : Blo 546805 549411 := bstep (se 1 (by rfl) ⟨412058, by rfl⟩ : syracuseStep 549411 = 824117) B824117
theorem B1237553 : Blo 546805 1237553 := bstep (se 2 (by rfl) ⟨464082, by rfl⟩ : syracuseStep 1237553 = 928165) B928165
theorem B549427 : Blo 546805 549427 := bstep (se 1 (by rfl) ⟨412070, by rfl⟩ : syracuseStep 549427 = 824141) B824141
theorem B549443 : Blo 546805 549443 := bstep (se 1 (by rfl) ⟨412082, by rfl⟩ : syracuseStep 549443 = 824165) B824165
theorem B1237571 : Blo 546805 1237571 := bstep (se 1 (by rfl) ⟨928178, by rfl⟩ : syracuseStep 1237571 = 1856357) B1856357
theorem B2351693 : Blo 546805 2351693 := bstep (se 3 (by rfl) ⟨440942, by rfl⟩ : syracuseStep 2351693 = 881885) B881885
theorem B549459 : Blo 546805 549459 := bstep (se 1 (by rfl) ⟨412094, by rfl⟩ : syracuseStep 549459 = 824189) B824189
theorem B549475 : Blo 546805 549475 := bstep (se 1 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 549475 = 824213) B824213
theorem B549491 : Blo 546805 549491 := bstep (se 1 (by rfl) ⟨412118, by rfl⟩ : syracuseStep 549491 = 824237) B824237
theorem B549507 : Blo 546805 549507 := bstep (se 1 (by rfl) ⟨412130, by rfl⟩ : syracuseStep 549507 = 824261) B824261
theorem B549523 : Blo 546805 549523 := bstep (se 1 (by rfl) ⟨412142, by rfl⟩ : syracuseStep 549523 = 824285) B824285
theorem B549539 : Blo 546805 549539 := bstep (se 1 (by rfl) ⟨412154, by rfl⟩ : syracuseStep 549539 = 824309) B824309
theorem B549555 : Blo 546805 549555 := bstep (se 1 (by rfl) ⟨412166, by rfl⟩ : syracuseStep 549555 = 824333) B824333
theorem B549571 : Blo 546805 549571 := bstep (se 1 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 549571 = 824357) B824357
theorem B549587 : Blo 546805 549587 := bstep (se 1 (by rfl) ⟨412190, by rfl⟩ : syracuseStep 549587 = 824381) B824381
theorem B549603 : Blo 546805 549603 := bstep (se 1 (by rfl) ⟨412202, by rfl⟩ : syracuseStep 549603 = 824405) B824405
theorem B549619 : Blo 546805 549619 := bstep (se 1 (by rfl) ⟨412214, by rfl⟩ : syracuseStep 549619 = 824429) B824429
theorem B549635 : Blo 546805 549635 := bstep (se 1 (by rfl) ⟨412226, by rfl⟩ : syracuseStep 549635 = 824453) B824453
theorem B549651 : Blo 546805 549651 := bstep (se 1 (by rfl) ⟨412238, by rfl⟩ : syracuseStep 549651 = 824477) B824477
theorem B1041187 : Blo 546805 1041187 := bstep (se 1 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 1041187 = 1561781) B1561781
theorem B549667 : Blo 546805 549667 := bstep (se 1 (by rfl) ⟨412250, by rfl⟩ : syracuseStep 549667 = 824501) B824501
theorem B549683 : Blo 546805 549683 := bstep (se 1 (by rfl) ⟨412262, by rfl⟩ : syracuseStep 549683 = 824525) B824525
theorem B615235 : Blo 546805 615235 := bstep (se 1 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 615235 = 922853) B922853
theorem B549699 : Blo 546805 549699 := bstep (se 1 (by rfl) ⟨412274, by rfl⟩ : syracuseStep 549699 = 824549) B824549
theorem B1237841 : Blo 546805 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B549715 : Blo 546805 549715 := bstep (se 1 (by rfl) ⟨412286, by rfl⟩ : syracuseStep 549715 = 824573) B824573
theorem B549731 : Blo 546805 549731 := bstep (se 1 (by rfl) ⟨412298, by rfl⟩ : syracuseStep 549731 = 824597) B824597
theorem B1237859 : Blo 546805 1237859 := bstep (se 1 (by rfl) ⟨928394, by rfl⟩ : syracuseStep 1237859 = 1856789) B1856789
theorem B549747 : Blo 546805 549747 := bstep (se 1 (by rfl) ⟨412310, by rfl⟩ : syracuseStep 549747 = 824621) B824621
theorem B549763 : Blo 546805 549763 := bstep (se 1 (by rfl) ⟨412322, by rfl⟩ : syracuseStep 549763 = 824645) B824645
theorem B1172369 : Blo 546805 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B549779 : Blo 546805 549779 := bstep (se 1 (by rfl) ⟨412334, by rfl⟩ : syracuseStep 549779 = 824669) B824669
theorem B1172387 : Blo 546805 1172387 := bstep (se 1 (by rfl) ⟨879290, by rfl⟩ : syracuseStep 1172387 = 1758581) B1758581
theorem B549795 : Blo 546805 549795 := bstep (se 1 (by rfl) ⟨412346, by rfl⟩ : syracuseStep 549795 = 824693) B824693
theorem B549811 : Blo 546805 549811 := bstep (se 1 (by rfl) ⟨412358, by rfl⟩ : syracuseStep 549811 = 824717) B824717
theorem B549827 : Blo 546805 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B615379 : Blo 546805 615379 := bstep (se 1 (by rfl) ⟨461534, by rfl⟩ : syracuseStep 615379 = 923069) B923069
theorem B549843 : Blo 546805 549843 := bstep (se 1 (by rfl) ⟨412382, by rfl⟩ : syracuseStep 549843 = 824765) B824765
theorem B779233 : Blo 546805 779233 := bstep (se 2 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 779233 = 584425) B584425
theorem B549859 : Blo 546805 549859 := bstep (se 1 (by rfl) ⟨412394, by rfl⟩ : syracuseStep 549859 = 824789) B824789
theorem B549875 : Blo 546805 549875 := bstep (se 1 (by rfl) ⟨412406, by rfl⟩ : syracuseStep 549875 = 824813) B824813
theorem B779267 : Blo 546805 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B549891 : Blo 546805 549891 := bstep (se 1 (by rfl) ⟨412418, by rfl⟩ : syracuseStep 549891 = 824837) B824837
theorem B549907 : Blo 546805 549907 := bstep (se 1 (by rfl) ⟨412430, by rfl⟩ : syracuseStep 549907 = 824861) B824861
theorem B549923 : Blo 546805 549923 := bstep (se 1 (by rfl) ⟨412442, by rfl⟩ : syracuseStep 549923 = 824885) B824885
theorem B549939 : Blo 546805 549939 := bstep (se 1 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 549939 = 824909) B824909
theorem B549955 : Blo 546805 549955 := bstep (se 1 (by rfl) ⟨412466, by rfl⟩ : syracuseStep 549955 = 824933) B824933
theorem B549971 : Blo 546805 549971 := bstep (se 1 (by rfl) ⟨412478, by rfl⟩ : syracuseStep 549971 = 824957) B824957
theorem B615523 : Blo 546805 615523 := bstep (se 1 (by rfl) ⟨461642, by rfl⟩ : syracuseStep 615523 = 923285) B923285
theorem B549987 : Blo 546805 549987 := bstep (se 1 (by rfl) ⟨412490, by rfl⟩ : syracuseStep 549987 = 824981) B824981
theorem B1238129 : Blo 546805 1238129 := bstep (se 2 (by rfl) ⟨464298, by rfl⟩ : syracuseStep 1238129 = 928597) B928597
theorem B550003 : Blo 546805 550003 := bstep (se 1 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 550003 = 825005) B825005
theorem B550019 : Blo 546805 550019 := bstep (se 1 (by rfl) ⟨412514, by rfl⟩ : syracuseStep 550019 = 825029) B825029
theorem B1238147 : Blo 546805 1238147 := bstep (se 1 (by rfl) ⟨928610, by rfl⟩ : syracuseStep 1238147 = 1857221) B1857221
theorem B550035 : Blo 546805 550035 := bstep (se 1 (by rfl) ⟨412526, by rfl⟩ : syracuseStep 550035 = 825053) B825053
theorem B550051 : Blo 546805 550051 := bstep (se 1 (by rfl) ⟨412538, by rfl⟩ : syracuseStep 550051 = 825077) B825077
theorem B550067 : Blo 546805 550067 := bstep (se 1 (by rfl) ⟨412550, by rfl⟩ : syracuseStep 550067 = 825101) B825101
theorem B550083 : Blo 546805 550083 := bstep (se 1 (by rfl) ⟨412562, by rfl⟩ : syracuseStep 550083 = 825125) B825125
theorem B550099 : Blo 546805 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B4678883 : Blo 546805 4678883 := bstep (se 1 (by rfl) ⟨3509162, by rfl⟩ : syracuseStep 4678883 = 7018325) B7018325
theorem B1041635 : Blo 546805 1041635 := bstep (se 1 (by rfl) ⟨781226, by rfl⟩ : syracuseStep 1041635 = 1562453) B1562453
theorem B550115 : Blo 546805 550115 := bstep (se 1 (by rfl) ⟨412586, by rfl⟩ : syracuseStep 550115 = 825173) B825173
theorem B2090225 : Blo 546805 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B615667 : Blo 546805 615667 := bstep (se 1 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 615667 = 923501) B923501
theorem B550131 : Blo 546805 550131 := bstep (se 1 (by rfl) ⟨412598, by rfl⟩ : syracuseStep 550131 = 825197) B825197
theorem B550147 : Blo 546805 550147 := bstep (se 1 (by rfl) ⟨412610, by rfl⟩ : syracuseStep 550147 = 825221) B825221
theorem B550163 : Blo 546805 550163 := bstep (se 1 (by rfl) ⟨412622, by rfl⟩ : syracuseStep 550163 = 825245) B825245
theorem B550179 : Blo 546805 550179 := bstep (se 1 (by rfl) ⟨412634, by rfl⟩ : syracuseStep 550179 = 825269) B825269
theorem B550195 : Blo 546805 550195 := bstep (se 1 (by rfl) ⟨412646, by rfl⟩ : syracuseStep 550195 = 825293) B825293
theorem B550211 : Blo 546805 550211 := bstep (se 1 (by rfl) ⟨412658, by rfl⟩ : syracuseStep 550211 = 825317) B825317
theorem B1566029 : Blo 546805 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B550227 : Blo 546805 550227 := bstep (se 1 (by rfl) ⟨412670, by rfl⟩ : syracuseStep 550227 = 825341) B825341
theorem B550243 : Blo 546805 550243 := bstep (se 1 (by rfl) ⟨412682, by rfl⟩ : syracuseStep 550243 = 825365) B825365
theorem B550259 : Blo 546805 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B615811 : Blo 546805 615811 := bstep (se 1 (by rfl) ⟨461858, by rfl⟩ : syracuseStep 615811 = 923717) B923717
theorem B550275 : Blo 546805 550275 := bstep (se 1 (by rfl) ⟨412706, by rfl⟩ : syracuseStep 550275 = 825413) B825413
theorem B1238417 : Blo 546805 1238417 := bstep (se 2 (by rfl) ⟨464406, by rfl⟩ : syracuseStep 1238417 = 928813) B928813
theorem B550291 : Blo 546805 550291 := bstep (se 1 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 550291 = 825437) B825437
theorem B550307 : Blo 546805 550307 := bstep (se 1 (by rfl) ⟨412730, by rfl⟩ : syracuseStep 550307 = 825461) B825461
theorem B1238435 : Blo 546805 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B550323 : Blo 546805 550323 := bstep (se 1 (by rfl) ⟨412742, by rfl⟩ : syracuseStep 550323 = 825485) B825485
theorem B550339 : Blo 546805 550339 := bstep (se 1 (by rfl) ⟨412754, by rfl⟩ : syracuseStep 550339 = 825509) B825509
theorem B550355 : Blo 546805 550355 := bstep (se 1 (by rfl) ⟨412766, by rfl⟩ : syracuseStep 550355 = 825533) B825533
theorem B550371 : Blo 546805 550371 := bstep (se 1 (by rfl) ⟨412778, by rfl⟩ : syracuseStep 550371 = 825557) B825557
theorem B550387 : Blo 546805 550387 := bstep (se 1 (by rfl) ⟨412790, by rfl⟩ : syracuseStep 550387 = 825581) B825581
theorem B1041923 : Blo 546805 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B1566211 : Blo 546805 1566211 := bstep (se 1 (by rfl) ⟨1174658, by rfl⟩ : syracuseStep 1566211 = 2349317) B2349317
theorem B550403 : Blo 546805 550403 := bstep (se 1 (by rfl) ⟨412802, by rfl⟩ : syracuseStep 550403 = 825605) B825605
theorem B615955 : Blo 546805 615955 := bstep (se 1 (by rfl) ⟨461966, by rfl⟩ : syracuseStep 615955 = 923933) B923933
theorem B550419 : Blo 546805 550419 := bstep (se 1 (by rfl) ⟨412814, by rfl⟩ : syracuseStep 550419 = 825629) B825629
theorem B550435 : Blo 546805 550435 := bstep (se 1 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 550435 = 825653) B825653
theorem B779825 : Blo 546805 779825 := bstep (se 2 (by rfl) ⟨292434, by rfl⟩ : syracuseStep 779825 = 584869) B584869
theorem B550451 : Blo 546805 550451 := bstep (se 1 (by rfl) ⟨412838, by rfl⟩ : syracuseStep 550451 = 825677) B825677
theorem B550467 : Blo 546805 550467 := bstep (se 1 (by rfl) ⟨412850, by rfl⟩ : syracuseStep 550467 = 825701) B825701
theorem B550483 : Blo 546805 550483 := bstep (se 1 (by rfl) ⟨412862, by rfl⟩ : syracuseStep 550483 = 825725) B825725
theorem B3335779 : Blo 546805 3335779 := bstep (se 1 (by rfl) ⟨2501834, by rfl⟩ : syracuseStep 3335779 = 5003669) B5003669
theorem B550499 : Blo 546805 550499 := bstep (se 1 (by rfl) ⟨412874, by rfl⟩ : syracuseStep 550499 = 825749) B825749
theorem B2221681 : Blo 546805 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B878195 : Blo 546805 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B550515 : Blo 546805 550515 := bstep (se 1 (by rfl) ⟨412886, by rfl⟩ : syracuseStep 550515 = 825773) B825773
theorem B779905 : Blo 546805 779905 := bstep (se 2 (by rfl) ⟨292464, by rfl⟩ : syracuseStep 779905 = 584929) B584929
theorem B550531 : Blo 546805 550531 := bstep (se 1 (by rfl) ⟨412898, by rfl⟩ : syracuseStep 550531 = 825797) B825797
theorem B550547 : Blo 546805 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B616099 : Blo 546805 616099 := bstep (se 1 (by rfl) ⟨462074, by rfl⟩ : syracuseStep 616099 = 924149) B924149
theorem B1566371 : Blo 546805 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B550563 : Blo 546805 550563 := bstep (se 1 (by rfl) ⟨412922, by rfl⟩ : syracuseStep 550563 = 825845) B825845
theorem B1238705 : Blo 546805 1238705 := bstep (se 2 (by rfl) ⟨464514, by rfl⟩ : syracuseStep 1238705 = 929029) B929029
theorem B550579 : Blo 546805 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B1238723 : Blo 546805 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B550595 : Blo 546805 550595 := bstep (se 1 (by rfl) ⟨412946, by rfl⟩ : syracuseStep 550595 = 825893) B825893
theorem B550611 : Blo 546805 550611 := bstep (se 1 (by rfl) ⟨412958, by rfl⟩ : syracuseStep 550611 = 825917) B825917
theorem B550627 : Blo 546805 550627 := bstep (se 1 (by rfl) ⟨412970, by rfl⟩ : syracuseStep 550627 = 825941) B825941
theorem B550643 : Blo 546805 550643 := bstep (se 1 (by rfl) ⟨412982, by rfl⟩ : syracuseStep 550643 = 825965) B825965
theorem B550659 : Blo 546805 550659 := bstep (se 1 (by rfl) ⟨412994, by rfl⟩ : syracuseStep 550659 = 825989) B825989
theorem B550675 : Blo 546805 550675 := bstep (se 1 (by rfl) ⟨413006, by rfl⟩ : syracuseStep 550675 = 826013) B826013
theorem B550691 : Blo 546805 550691 := bstep (se 1 (by rfl) ⟨413018, by rfl⟩ : syracuseStep 550691 = 826037) B826037
theorem B1763117 : Blo 546805 1763117 := bstep (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) B661169
theorem B616243 : Blo 546805 616243 := bstep (se 1 (by rfl) ⟨462182, by rfl⟩ : syracuseStep 616243 = 924365) B924365
theorem B550707 : Blo 546805 550707 := bstep (se 1 (by rfl) ⟨413030, by rfl⟩ : syracuseStep 550707 = 826061) B826061
theorem B550723 : Blo 546805 550723 := bstep (se 1 (by rfl) ⟨413042, by rfl⟩ : syracuseStep 550723 = 826085) B826085
theorem B550739 : Blo 546805 550739 := bstep (se 1 (by rfl) ⟨413054, by rfl⟩ : syracuseStep 550739 = 826109) B826109
theorem B550755 : Blo 546805 550755 := bstep (se 1 (by rfl) ⟨413066, by rfl⟩ : syracuseStep 550755 = 826133) B826133
theorem B550771 : Blo 546805 550771 := bstep (se 1 (by rfl) ⟨413078, by rfl⟩ : syracuseStep 550771 = 826157) B826157
theorem B550787 : Blo 546805 550787 := bstep (se 1 (by rfl) ⟨413090, by rfl⟩ : syracuseStep 550787 = 826181) B826181
theorem B2090893 : Blo 546805 2090893 := bstep (se 3 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 2090893 = 784085) B784085
theorem B550803 : Blo 546805 550803 := bstep (se 1 (by rfl) ⟨413102, by rfl⟩ : syracuseStep 550803 = 826205) B826205
theorem B616387 : Blo 546805 616387 := bstep (se 1 (by rfl) ⟨462290, by rfl⟩ : syracuseStep 616387 = 924581) B924581
theorem B1238993 : Blo 546805 1238993 := bstep (se 2 (by rfl) ⟨464622, by rfl⟩ : syracuseStep 1238993 = 929245) B929245
theorem B1239011 : Blo 546805 1239011 := bstep (se 1 (by rfl) ⟨929258, by rfl⟩ : syracuseStep 1239011 = 1858517) B1858517
theorem B616531 : Blo 546805 616531 := bstep (se 1 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 616531 = 924797) B924797
theorem B616675 : Blo 546805 616675 := bstep (se 1 (by rfl) ⟨462506, by rfl⟩ : syracuseStep 616675 = 925013) B925013
theorem B1239281 : Blo 546805 1239281 := bstep (se 2 (by rfl) ⟨464730, by rfl⟩ : syracuseStep 1239281 = 929461) B929461
theorem B1239299 : Blo 546805 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B878867 : Blo 546805 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B846163 : Blo 546805 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B616819 : Blo 546805 616819 := bstep (se 1 (by rfl) ⟨462614, by rfl⟩ : syracuseStep 616819 = 925229) B925229
theorem B780691 : Blo 546805 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B1042865 : Blo 546805 1042865 := bstep (se 2 (by rfl) ⟨391074, by rfl⟩ : syracuseStep 1042865 = 782149) B782149
theorem B616963 : Blo 546805 616963 := bstep (se 1 (by rfl) ⟨462722, by rfl⟩ : syracuseStep 616963 = 925445) B925445
theorem B879169 : Blo 546805 879169 := bstep (se 2 (by rfl) ⟨329688, by rfl⟩ : syracuseStep 879169 = 659377) B659377
theorem B584339 : Blo 546805 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B617107 : Blo 546805 617107 := bstep (se 1 (by rfl) ⟨462830, by rfl⟩ : syracuseStep 617107 = 925661) B925661
theorem B1764013 : Blo 546805 1764013 := bstep (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) B661505
theorem B1567441 : Blo 546805 1567441 := bstep (se 2 (by rfl) ⟨587790, by rfl⟩ : syracuseStep 1567441 = 1175581) B1175581
theorem B879379 : Blo 546805 879379 := bstep (se 1 (by rfl) ⟨659534, by rfl⟩ : syracuseStep 879379 = 1319069) B1319069
theorem B617251 : Blo 546805 617251 := bstep (se 1 (by rfl) ⟨462938, by rfl⟩ : syracuseStep 617251 = 925877) B925877
theorem B879425 : Blo 546805 879425 := bstep (se 2 (by rfl) ⟨329784, by rfl⟩ : syracuseStep 879425 = 659569) B659569
theorem B781169 : Blo 546805 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B1174385 : Blo 546805 1174385 := bstep (se 2 (by rfl) ⟨440394, by rfl⟩ : syracuseStep 1174385 = 880789) B880789
theorem B4451213 : Blo 546805 4451213 := bstep (se 3 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 4451213 = 1669205) B1669205
theorem B2780081 : Blo 546805 2780081 := bstep (se 2 (by rfl) ⟨1042530, by rfl⟩ : syracuseStep 2780081 = 2085061) B2085061
theorem B617395 : Blo 546805 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B781283 : Blo 546805 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B781363 : Blo 546805 781363 := bstep (se 1 (by rfl) ⟨586022, by rfl⟩ : syracuseStep 781363 = 1172045) B1172045
theorem B617539 : Blo 546805 617539 := bstep (se 1 (by rfl) ⟨463154, by rfl⟩ : syracuseStep 617539 = 926309) B926309
theorem B617683 : Blo 546805 617683 := bstep (se 1 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 617683 = 926525) B926525
theorem B1109219 : Blo 546805 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1043761 : Blo 546805 1043761 := bstep (se 2 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 1043761 = 782821) B782821
theorem B5008709 : Blo 546805 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B617827 : Blo 546805 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B585091 : Blo 546805 585091 := bstep (se 1 (by rfl) ⟨438818, by rfl⟩ : syracuseStep 585091 = 877637) B877637
theorem B1174915 : Blo 546805 1174915 := bstep (se 1 (by rfl) ⟨881186, by rfl⟩ : syracuseStep 1174915 = 1762373) B1762373
theorem B1043921 : Blo 546805 1043921 := bstep (se 2 (by rfl) ⟨391470, by rfl⟩ : syracuseStep 1043921 = 782941) B782941
theorem B617971 : Blo 546805 617971 := bstep (se 1 (by rfl) ⟨463478, by rfl⟩ : syracuseStep 617971 = 926957) B926957
theorem B781921 : Blo 546805 781921 := bstep (se 2 (by rfl) ⟨293220, by rfl⟩ : syracuseStep 781921 = 586441) B586441
theorem B618115 : Blo 546805 618115 := bstep (se 1 (by rfl) ⟨463586, by rfl⟩ : syracuseStep 618115 = 927173) B927173
theorem B618259 : Blo 546805 618259 := bstep (se 1 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 618259 = 927389) B927389
theorem B1044323 : Blo 546805 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B618403 : Blo 546805 618403 := bstep (se 1 (by rfl) ⟨463802, by rfl⟩ : syracuseStep 618403 = 927605) B927605
theorem B10547171 : Blo 546805 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B618547 : Blo 546805 618547 := bstep (se 1 (by rfl) ⟨463910, by rfl⟩ : syracuseStep 618547 = 927821) B927821
theorem B618691 : Blo 546805 618691 := bstep (se 1 (by rfl) ⟨464018, by rfl⟩ : syracuseStep 618691 = 928037) B928037
theorem B6254819 : Blo 546805 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B782627 : Blo 546805 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B880931 : Blo 546805 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B1667405 : Blo 546805 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B618835 : Blo 546805 618835 := bstep (se 1 (by rfl) ⟨464126, by rfl⟩ : syracuseStep 618835 = 928253) B928253
theorem B2781539 : Blo 546805 2781539 := bstep (se 1 (by rfl) ⟨2086154, by rfl⟩ : syracuseStep 2781539 = 4172309) B4172309
theorem B586099 : Blo 546805 586099 := bstep (se 1 (by rfl) ⟨439574, by rfl⟩ : syracuseStep 586099 = 879149) B879149
theorem B618979 : Blo 546805 618979 := bstep (se 1 (by rfl) ⟨464234, by rfl⟩ : syracuseStep 618979 = 928469) B928469
theorem B881219 : Blo 546805 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B619123 : Blo 546805 619123 := bstep (se 1 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 619123 = 928685) B928685
theorem B1045219 : Blo 546805 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B619267 : Blo 546805 619267 := bstep (se 1 (by rfl) ⟨464450, by rfl⟩ : syracuseStep 619267 = 928901) B928901
theorem B4682609 : Blo 546805 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B1045379 : Blo 546805 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B619411 : Blo 546805 619411 := bstep (se 1 (by rfl) ⟨464558, by rfl⟩ : syracuseStep 619411 = 929117) B929117
theorem B783265 : Blo 546805 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B783379 : Blo 546805 783379 := bstep (se 1 (by rfl) ⟨587534, by rfl⟩ : syracuseStep 783379 = 1175069) B1175069
theorem B619555 : Blo 546805 619555 := bstep (se 1 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 619555 = 929333) B929333
theorem B816193 : Blo 546805 816193 := bstep (se 2 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 816193 = 612145) B612145
theorem B2782349 : Blo 546805 2782349 := bstep (se 3 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 2782349 = 1043381) B1043381
theorem B587107 : Blo 546805 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B882019 : Blo 546805 882019 := bstep (se 1 (by rfl) ⟨661514, by rfl⟩ : syracuseStep 882019 = 1323029) B1323029
theorem B882161 : Blo 546805 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B882193 : Blo 546805 882193 := bstep (se 2 (by rfl) ⟨330822, by rfl⟩ : syracuseStep 882193 = 661645) B661645
theorem B23656049 : Blo 546805 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B1111985 : Blo 546805 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B587731 : Blo 546805 587731 := bstep (se 1 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 587731 = 881597) B881597
theorem B8353763 : Blo 546805 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B3569669 : Blo 546805 3569669 := bstep (se 4 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 3569669 = 669313) B669313
theorem B555283 : Blo 546805 555283 := bstep (se 1 (by rfl) ⟨416462, by rfl⟩ : syracuseStep 555283 = 832925) B832925
theorem B1505603 : Blo 546805 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B3504653 : Blo 546805 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B7043597 : Blo 546805 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B1604141 : Blo 546805 1604141 := bstep (se 3 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 1604141 = 601553) B601553
theorem B1112771 : Blo 546805 1112771 := bstep (se 1 (by rfl) ⟨834578, by rfl⟩ : syracuseStep 1112771 = 1669157) B1669157
theorem B2227085 : Blo 546805 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B6651317 : Blo 546805 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B1113841 : Blo 546805 1113841 := bstep (se 2 (by rfl) ⟨417690, by rfl⟩ : syracuseStep 1113841 = 835381) B835381
theorem B6356789 : Blo 546805 6356789 := bstep (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) B595949
theorem B2785265 : Blo 546805 2785265 := bstep (se 2 (by rfl) ⟨1044474, by rfl⟩ : syracuseStep 2785265 = 2088949) B2088949
theorem B1114393 : Blo 546805 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B2261465 : Blo 546805 2261465 := bstep (se 2 (by rfl) ⟨848049, by rfl⟩ : syracuseStep 2261465 = 1696099) B1696099
theorem B3506753 : Blo 546805 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B8422019 : Blo 546805 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B820235 : Blo 546805 820235 := bstep (se 1 (by rfl) ⟨615176, by rfl⟩ : syracuseStep 820235 = 1230353) B1230353
theorem B820247 : Blo 546805 820247 := bstep (se 1 (by rfl) ⟨615185, by rfl⟩ : syracuseStep 820247 = 1230371) B1230371
theorem B820313 : Blo 546805 820313 := bstep (se 2 (by rfl) ⟨307617, by rfl⟩ : syracuseStep 820313 = 615235) B615235
theorem B820427 : Blo 546805 820427 := bstep (se 1 (by rfl) ⟨615320, by rfl⟩ : syracuseStep 820427 = 1230641) B1230641
theorem B820439 : Blo 546805 820439 := bstep (se 1 (by rfl) ⟨615329, by rfl⟩ : syracuseStep 820439 = 1230659) B1230659
theorem B820505 : Blo 546805 820505 := bstep (se 2 (by rfl) ⟨307689, by rfl⟩ : syracuseStep 820505 = 615379) B615379
theorem B3999041 : Blo 546805 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B820619 : Blo 546805 820619 := bstep (se 1 (by rfl) ⟨615464, by rfl⟩ : syracuseStep 820619 = 1230929) B1230929
theorem B820631 : Blo 546805 820631 := bstep (se 1 (by rfl) ⟨615473, by rfl⟩ : syracuseStep 820631 = 1230947) B1230947
theorem B820697 : Blo 546805 820697 := bstep (se 2 (by rfl) ⟨307761, by rfl⟩ : syracuseStep 820697 = 615523) B615523
theorem B4752901 : Blo 546805 4752901 := bstep (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) B891169
theorem B820811 : Blo 546805 820811 := bstep (se 1 (by rfl) ⟨615608, by rfl⟩ : syracuseStep 820811 = 1231217) B1231217
theorem B820823 : Blo 546805 820823 := bstep (se 1 (by rfl) ⟨615617, by rfl⟩ : syracuseStep 820823 = 1231235) B1231235
theorem B820889 : Blo 546805 820889 := bstep (se 2 (by rfl) ⟨307833, by rfl⟩ : syracuseStep 820889 = 615667) B615667
theorem B1607347 : Blo 546805 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B821003 : Blo 546805 821003 := bstep (se 1 (by rfl) ⟨615752, by rfl⟩ : syracuseStep 821003 = 1231505) B1231505
theorem B821015 : Blo 546805 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B821081 : Blo 546805 821081 := bstep (se 2 (by rfl) ⟨307905, by rfl⟩ : syracuseStep 821081 = 615811) B615811
theorem B821195 : Blo 546805 821195 := bstep (se 1 (by rfl) ⟨615896, by rfl⟩ : syracuseStep 821195 = 1231793) B1231793
theorem B821207 : Blo 546805 821207 := bstep (se 1 (by rfl) ⟨615905, by rfl⟩ : syracuseStep 821207 = 1231811) B1231811
theorem B821273 : Blo 546805 821273 := bstep (se 2 (by rfl) ⟨307977, by rfl⟩ : syracuseStep 821273 = 615955) B615955
theorem B821387 : Blo 546805 821387 := bstep (se 1 (by rfl) ⟨616040, by rfl⟩ : syracuseStep 821387 = 1232081) B1232081
theorem B821399 : Blo 546805 821399 := bstep (se 1 (by rfl) ⟨616049, by rfl⟩ : syracuseStep 821399 = 1232099) B1232099
theorem B3967127 : Blo 546805 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B821465 : Blo 546805 821465 := bstep (se 2 (by rfl) ⟨308049, by rfl⟩ : syracuseStep 821465 = 616099) B616099
theorem B624875 : Blo 546805 624875 := bstep (se 1 (by rfl) ⟨468656, by rfl⟩ : syracuseStep 624875 = 937313) B937313
theorem B6850861 : Blo 546805 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B821579 : Blo 546805 821579 := bstep (se 1 (by rfl) ⟨616184, by rfl⟩ : syracuseStep 821579 = 1232369) B1232369
theorem B821591 : Blo 546805 821591 := bstep (se 1 (by rfl) ⟨616193, by rfl⟩ : syracuseStep 821591 = 1232387) B1232387
theorem B11831669 : Blo 546805 11831669 := bstep (se 5 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 11831669 = 1109219) B1109219
theorem B821657 : Blo 546805 821657 := bstep (se 2 (by rfl) ⟨308121, by rfl⟩ : syracuseStep 821657 = 616243) B616243
theorem B821771 : Blo 546805 821771 := bstep (se 1 (by rfl) ⟨616328, by rfl⟩ : syracuseStep 821771 = 1232657) B1232657
theorem B2787857 : Blo 546805 2787857 := bstep (se 2 (by rfl) ⟨1045446, by rfl⟩ : syracuseStep 2787857 = 2090893) B2090893
theorem B821783 : Blo 546805 821783 := bstep (se 1 (by rfl) ⟨616337, by rfl⟩ : syracuseStep 821783 = 1232675) B1232675
theorem B821849 : Blo 546805 821849 := bstep (se 2 (by rfl) ⟨308193, by rfl⟩ : syracuseStep 821849 = 616387) B616387
theorem B2788019 : Blo 546805 2788019 := bstep (se 1 (by rfl) ⟨2091014, by rfl⟩ : syracuseStep 2788019 = 4182029) B4182029
theorem B821963 : Blo 546805 821963 := bstep (se 1 (by rfl) ⟨616472, by rfl⟩ : syracuseStep 821963 = 1232945) B1232945
theorem B821975 : Blo 546805 821975 := bstep (se 1 (by rfl) ⟨616481, by rfl⟩ : syracuseStep 821975 = 1232963) B1232963
theorem B822041 : Blo 546805 822041 := bstep (se 2 (by rfl) ⟨308265, by rfl⟩ : syracuseStep 822041 = 616531) B616531
theorem B3115907 : Blo 546805 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B822155 : Blo 546805 822155 := bstep (se 1 (by rfl) ⟨616616, by rfl⟩ : syracuseStep 822155 = 1233233) B1233233
theorem B822167 : Blo 546805 822167 := bstep (se 1 (by rfl) ⟨616625, by rfl⟩ : syracuseStep 822167 = 1233251) B1233251
theorem B822233 : Blo 546805 822233 := bstep (se 2 (by rfl) ⟨308337, by rfl⟩ : syracuseStep 822233 = 616675) B616675
theorem B822347 : Blo 546805 822347 := bstep (se 1 (by rfl) ⟨616760, by rfl⟩ : syracuseStep 822347 = 1233521) B1233521
theorem B822359 : Blo 546805 822359 := bstep (se 1 (by rfl) ⟨616769, by rfl⟩ : syracuseStep 822359 = 1233539) B1233539
theorem B822425 : Blo 546805 822425 := bstep (se 2 (by rfl) ⟨308409, by rfl⟩ : syracuseStep 822425 = 616819) B616819
theorem B1313995 : Blo 546805 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B822539 : Blo 546805 822539 := bstep (se 1 (by rfl) ⟨616904, by rfl⟩ : syracuseStep 822539 = 1233809) B1233809
theorem B822551 : Blo 546805 822551 := bstep (se 1 (by rfl) ⟨616913, by rfl⟩ : syracuseStep 822551 = 1233827) B1233827
theorem B822617 : Blo 546805 822617 := bstep (se 2 (by rfl) ⟨308481, by rfl⟩ : syracuseStep 822617 = 616963) B616963
theorem B7048565 : Blo 546805 7048565 := bstep (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) B660803
theorem B7146929 : Blo 546805 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B593335 : Blo 546805 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B658891 : Blo 546805 658891 := bstep (se 1 (by rfl) ⟨494168, by rfl⟩ : syracuseStep 658891 = 988337) B988337
theorem B822731 : Blo 546805 822731 := bstep (se 1 (by rfl) ⟨617048, by rfl⟩ : syracuseStep 822731 = 1234097) B1234097
theorem B822743 : Blo 546805 822743 := bstep (se 1 (by rfl) ⟨617057, by rfl⟩ : syracuseStep 822743 = 1234115) B1234115
theorem B986585 : Blo 546805 986585 := bstep (se 2 (by rfl) ⟨369969, by rfl⟩ : syracuseStep 986585 = 739939) B739939
theorem B822809 : Blo 546805 822809 := bstep (se 2 (by rfl) ⟨308553, by rfl⟩ : syracuseStep 822809 = 617107) B617107
theorem B822923 : Blo 546805 822923 := bstep (se 1 (by rfl) ⟨617192, by rfl⟩ : syracuseStep 822923 = 1234385) B1234385
theorem B822935 : Blo 546805 822935 := bstep (se 1 (by rfl) ⟨617201, by rfl⟩ : syracuseStep 822935 = 1234403) B1234403
theorem B823001 : Blo 546805 823001 := bstep (se 2 (by rfl) ⟨308625, by rfl⟩ : syracuseStep 823001 = 617251) B617251
theorem B823115 : Blo 546805 823115 := bstep (se 1 (by rfl) ⟨617336, by rfl⟩ : syracuseStep 823115 = 1234673) B1234673
theorem B823127 : Blo 546805 823127 := bstep (se 1 (by rfl) ⟨617345, by rfl⟩ : syracuseStep 823127 = 1234691) B1234691
theorem B986995 : Blo 546805 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B823193 : Blo 546805 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B9408473 : Blo 546805 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B823307 : Blo 546805 823307 := bstep (se 1 (by rfl) ⟨617480, by rfl⟩ : syracuseStep 823307 = 1234961) B1234961
theorem B6230033 : Blo 546805 6230033 := bstep (se 2 (by rfl) ⟨2336262, by rfl⟩ : syracuseStep 6230033 = 4672525) B4672525
theorem B823319 : Blo 546805 823319 := bstep (se 1 (by rfl) ⟨617489, by rfl⟩ : syracuseStep 823319 = 1234979) B1234979
theorem B3510317 : Blo 546805 3510317 := bstep (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) B1316369
theorem B823385 : Blo 546805 823385 := bstep (se 2 (by rfl) ⟨308769, by rfl⟩ : syracuseStep 823385 = 617539) B617539
theorem B4690021 : Blo 546805 4690021 := bstep (se 4 (by rfl) ⟨439689, by rfl⟩ : syracuseStep 4690021 = 879379) B879379
theorem B2494667 : Blo 546805 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B823499 : Blo 546805 823499 := bstep (se 1 (by rfl) ⟨617624, by rfl⟩ : syracuseStep 823499 = 1235249) B1235249
theorem B823511 : Blo 546805 823511 := bstep (se 1 (by rfl) ⟨617633, by rfl⟩ : syracuseStep 823511 = 1235267) B1235267
theorem B823577 : Blo 546805 823577 := bstep (se 2 (by rfl) ⟨308841, by rfl⟩ : syracuseStep 823577 = 617683) B617683
theorem B5017949 : Blo 546805 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B823691 : Blo 546805 823691 := bstep (se 1 (by rfl) ⟨617768, by rfl⟩ : syracuseStep 823691 = 1235537) B1235537
theorem B823703 : Blo 546805 823703 := bstep (se 1 (by rfl) ⟨617777, by rfl⟩ : syracuseStep 823703 = 1235555) B1235555
theorem B823769 : Blo 546805 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B627211 : Blo 546805 627211 := bstep (se 1 (by rfl) ⟨470408, by rfl⟩ : syracuseStep 627211 = 940817) B940817
theorem B1249843 : Blo 546805 1249843 := bstep (se 1 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 1249843 = 1874765) B1874765
theorem B823883 : Blo 546805 823883 := bstep (se 1 (by rfl) ⟨617912, by rfl⟩ : syracuseStep 823883 = 1235825) B1235825
theorem B823895 : Blo 546805 823895 := bstep (se 1 (by rfl) ⟨617921, by rfl⟩ : syracuseStep 823895 = 1235843) B1235843
theorem B889483 : Blo 546805 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B660107 : Blo 546805 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B823961 : Blo 546805 823961 := bstep (se 2 (by rfl) ⟨308985, by rfl⟩ : syracuseStep 823961 = 617971) B617971
theorem B824075 : Blo 546805 824075 := bstep (se 1 (by rfl) ⟨618056, by rfl⟩ : syracuseStep 824075 = 1236113) B1236113
theorem B824087 : Blo 546805 824087 := bstep (se 1 (by rfl) ⟨618065, by rfl⟩ : syracuseStep 824087 = 1236131) B1236131
theorem B2233133 : Blo 546805 2233133 := bstep (se 3 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 2233133 = 837425) B837425
theorem B824153 : Blo 546805 824153 := bstep (se 2 (by rfl) ⟨309057, by rfl⟩ : syracuseStep 824153 = 618115) B618115
theorem B1971137 : Blo 546805 1971137 := bstep (se 2 (by rfl) ⟨739176, by rfl⟩ : syracuseStep 1971137 = 1478353) B1478353
theorem B824267 : Blo 546805 824267 := bstep (se 1 (by rfl) ⟨618200, by rfl⟩ : syracuseStep 824267 = 1236401) B1236401
theorem B824279 : Blo 546805 824279 := bstep (se 1 (by rfl) ⟨618209, by rfl⟩ : syracuseStep 824279 = 1236419) B1236419
theorem B824345 : Blo 546805 824345 := bstep (se 2 (by rfl) ⟨309129, by rfl⟩ : syracuseStep 824345 = 618259) B618259
theorem B4690979 : Blo 546805 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B824459 : Blo 546805 824459 := bstep (se 1 (by rfl) ⟨618344, by rfl⟩ : syracuseStep 824459 = 1236689) B1236689
theorem B824471 : Blo 546805 824471 := bstep (se 1 (by rfl) ⟨618353, by rfl⟩ : syracuseStep 824471 = 1236707) B1236707
theorem B1283251 : Blo 546805 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B693451 : Blo 546805 693451 := bstep (se 1 (by rfl) ⟨520088, by rfl⟩ : syracuseStep 693451 = 1040177) B1040177
theorem B3118297 : Blo 546805 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B824537 : Blo 546805 824537 := bstep (se 2 (by rfl) ⟨309201, by rfl⟩ : syracuseStep 824537 = 618403) B618403
theorem B1316147 : Blo 546805 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B824651 : Blo 546805 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B824663 : Blo 546805 824663 := bstep (se 1 (by rfl) ⟨618497, by rfl⟩ : syracuseStep 824663 = 1236995) B1236995
theorem B628087 : Blo 546805 628087 := bstep (se 1 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 628087 = 942131) B942131
theorem B824729 : Blo 546805 824729 := bstep (se 2 (by rfl) ⟨309273, by rfl⟩ : syracuseStep 824729 = 618547) B618547
theorem B1480139 : Blo 546805 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B824843 : Blo 546805 824843 := bstep (se 1 (by rfl) ⟨618632, by rfl⟩ : syracuseStep 824843 = 1237265) B1237265
theorem B824855 : Blo 546805 824855 := bstep (se 1 (by rfl) ⟨618641, by rfl⟩ : syracuseStep 824855 = 1237283) B1237283
theorem B824921 : Blo 546805 824921 := bstep (se 2 (by rfl) ⟨309345, by rfl⟩ : syracuseStep 824921 = 618691) B618691
theorem B923339 : Blo 546805 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B825035 : Blo 546805 825035 := bstep (se 1 (by rfl) ⟨618776, by rfl⟩ : syracuseStep 825035 = 1237553) B1237553
theorem B825047 : Blo 546805 825047 := bstep (se 1 (by rfl) ⟨618785, by rfl⟩ : syracuseStep 825047 = 1237571) B1237571
theorem B661207 : Blo 546805 661207 := bstep (se 1 (by rfl) ⟨495905, by rfl⟩ : syracuseStep 661207 = 991811) B991811
theorem B825113 : Blo 546805 825113 := bstep (se 2 (by rfl) ⟨309417, by rfl⟩ : syracuseStep 825113 = 618835) B618835
theorem B923467 : Blo 546805 923467 := bstep (se 1 (by rfl) ⟨692600, by rfl⟩ : syracuseStep 923467 = 1385201) B1385201
theorem B825227 : Blo 546805 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B825239 : Blo 546805 825239 := bstep (se 1 (by rfl) ⟨618929, by rfl⟩ : syracuseStep 825239 = 1237859) B1237859
theorem B923609 : Blo 546805 923609 := bstep (se 2 (by rfl) ⟨346353, by rfl⟩ : syracuseStep 923609 = 692707) B692707
theorem B825305 : Blo 546805 825305 := bstep (se 2 (by rfl) ⟨309489, by rfl⟩ : syracuseStep 825305 = 618979) B618979
theorem B825419 : Blo 546805 825419 := bstep (se 1 (by rfl) ⟨619064, by rfl⟩ : syracuseStep 825419 = 1238129) B1238129
theorem B825431 : Blo 546805 825431 := bstep (se 1 (by rfl) ⟨619073, by rfl⟩ : syracuseStep 825431 = 1238147) B1238147
theorem B923737 : Blo 546805 923737 := bstep (se 2 (by rfl) ⟨346401, by rfl⟩ : syracuseStep 923737 = 692803) B692803
theorem B3119255 : Blo 546805 3119255 := bstep (se 1 (by rfl) ⟨2339441, by rfl⟩ : syracuseStep 3119255 = 4678883) B4678883
theorem B694423 : Blo 546805 694423 := bstep (se 1 (by rfl) ⟨520817, by rfl⟩ : syracuseStep 694423 = 1041635) B1041635
theorem B825497 : Blo 546805 825497 := bstep (se 2 (by rfl) ⟨309561, by rfl⟩ : syracuseStep 825497 = 619123) B619123
theorem B825611 : Blo 546805 825611 := bstep (se 1 (by rfl) ⟨619208, by rfl⟩ : syracuseStep 825611 = 1238417) B1238417
theorem B825623 : Blo 546805 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B825689 : Blo 546805 825689 := bstep (se 2 (by rfl) ⟨309633, by rfl⟩ : syracuseStep 825689 = 619267) B619267
theorem B825803 : Blo 546805 825803 := bstep (se 1 (by rfl) ⟨619352, by rfl⟩ : syracuseStep 825803 = 1238705) B1238705
theorem B825815 : Blo 546805 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B825881 : Blo 546805 825881 := bstep (se 2 (by rfl) ⟨309705, by rfl⟩ : syracuseStep 825881 = 619411) B619411
theorem B1972781 : Blo 546805 1972781 := bstep (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) B739793
theorem B825995 : Blo 546805 825995 := bstep (se 1 (by rfl) ⟨619496, by rfl⟩ : syracuseStep 825995 = 1238993) B1238993
theorem B924311 : Blo 546805 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B826007 : Blo 546805 826007 := bstep (se 1 (by rfl) ⟨619505, by rfl⟩ : syracuseStep 826007 = 1239011) B1239011
theorem B826073 : Blo 546805 826073 := bstep (se 2 (by rfl) ⟨309777, by rfl⟩ : syracuseStep 826073 = 619555) B619555
theorem B1088257 : Blo 546805 1088257 := bstep (se 2 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 1088257 = 816193) B816193
theorem B924439 : Blo 546805 924439 := bstep (se 1 (by rfl) ⟨693329, by rfl⟩ : syracuseStep 924439 = 1386659) B1386659
theorem B826187 : Blo 546805 826187 := bstep (se 1 (by rfl) ⟨619640, by rfl⟩ : syracuseStep 826187 = 1239281) B1239281
theorem B826199 : Blo 546805 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B6232949 : Blo 546805 6232949 := bstep (se 5 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 6232949 = 584339) B584339
theorem B695243 : Blo 546805 695243 := bstep (se 1 (by rfl) ⟨521432, by rfl⟩ : syracuseStep 695243 = 1042865) B1042865
theorem B2628683 : Blo 546805 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B925067 : Blo 546805 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B925195 : Blo 546805 925195 := bstep (se 1 (by rfl) ⟨693896, by rfl⟩ : syracuseStep 925195 = 1387793) B1387793
theorem B1580609 : Blo 546805 1580609 := bstep (se 2 (by rfl) ⟨592728, by rfl⟩ : syracuseStep 1580609 = 1185457) B1185457
theorem B695947 : Blo 546805 695947 := bstep (se 1 (by rfl) ⟨521960, by rfl⟩ : syracuseStep 695947 = 1043921) B1043921
theorem B925337 : Blo 546805 925337 := bstep (se 2 (by rfl) ⟨347001, by rfl⟩ : syracuseStep 925337 = 694003) B694003
theorem B4169393 : Blo 546805 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B925465 : Blo 546805 925465 := bstep (se 2 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 925465 = 694099) B694099
theorem B696215 : Blo 546805 696215 := bstep (se 1 (by rfl) ⟨522161, by rfl⟩ : syracuseStep 696215 = 1044323) B1044323
theorem B1253399 : Blo 546805 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B1384523 : Blo 546805 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B4169879 : Blo 546805 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B926039 : Blo 546805 926039 := bstep (se 1 (by rfl) ⟨694529, by rfl⟩ : syracuseStep 926039 = 1389059) B1389059
theorem B1384897 : Blo 546805 1384897 := bstep (se 2 (by rfl) ⟨519336, by rfl⟩ : syracuseStep 1384897 = 1038673) B1038673
theorem B926167 : Blo 546805 926167 := bstep (se 1 (by rfl) ⟨694625, by rfl⟩ : syracuseStep 926167 = 1389251) B1389251
theorem B13378061 : Blo 546805 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B3121739 : Blo 546805 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B1188427 : Blo 546805 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B696919 : Blo 546805 696919 := bstep (se 1 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 696919 = 1045379) B1045379
theorem B1319627 : Blo 546805 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B4760365 : Blo 546805 4760365 := bstep (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) B1785137
theorem B1385495 : Blo 546805 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B15770699 : Blo 546805 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B926795 : Blo 546805 926795 := bstep (se 1 (by rfl) ⟨695096, by rfl⟩ : syracuseStep 926795 = 1390193) B1390193
theorem B2335837 : Blo 546805 2335837 := bstep (se 3 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 2335837 = 875939) B875939
theorem B926923 : Blo 546805 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B5940485 : Blo 546805 5940485 := bstep (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) B1113841
theorem B927065 : Blo 546805 927065 := bstep (se 2 (by rfl) ⟨347649, by rfl⟩ : syracuseStep 927065 = 695299) B695299
theorem B927193 : Blo 546805 927193 := bstep (se 2 (by rfl) ⟨347697, by rfl⟩ : syracuseStep 927193 = 695395) B695395
theorem B1320599 : Blo 546805 1320599 := bstep (se 1 (by rfl) ⟨990449, by rfl⟩ : syracuseStep 1320599 = 1980899) B1980899
theorem B2336435 : Blo 546805 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B4695731 : Blo 546805 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B1386305 : Blo 546805 1386305 := bstep (se 2 (by rfl) ⟨519864, by rfl⟩ : syracuseStep 1386305 = 1039729) B1039729
theorem B11904833 : Blo 546805 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B1484723 : Blo 546805 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B927767 : Blo 546805 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B1976413 : Blo 546805 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B1976471 : Blo 546805 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B927895 : Blo 546805 927895 := bstep (se 1 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 927895 = 1391843) B1391843
theorem B4434211 : Blo 546805 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1583425 : Blo 546805 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B1386841 : Blo 546805 1386841 := bstep (se 2 (by rfl) ⟨520065, by rfl⟩ : syracuseStep 1386841 = 1040131) B1040131
theorem B1583563 : Blo 546805 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B4237859 : Blo 546805 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B1583833 : Blo 546805 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B928523 : Blo 546805 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B928651 : Blo 546805 928651 := bstep (se 1 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 928651 = 1392977) B1392977
theorem B928793 : Blo 546805 928793 := bstep (se 2 (by rfl) ⟨348297, by rfl⟩ : syracuseStep 928793 = 696595) B696595
theorem B1190963 : Blo 546805 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B928921 : Blo 546805 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B3124403 : Blo 546805 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B1846475 : Blo 546805 1846475 := bstep (se 1 (by rfl) ⟨1384856, by rfl⟩ : syracuseStep 1846475 = 2769713) B2769713
theorem B1387955 : Blo 546805 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B1846745 : Blo 546805 1846745 := bstep (se 2 (by rfl) ⟨692529, by rfl⟩ : syracuseStep 1846745 = 1385059) B1385059
theorem B1322675 : Blo 546805 1322675 := bstep (se 1 (by rfl) ⟨992006, by rfl⟩ : syracuseStep 1322675 = 1984013) B1984013
theorem B1388249 : Blo 546805 1388249 := bstep (se 2 (by rfl) ⟨520593, by rfl⟩ : syracuseStep 1388249 = 1041187) B1041187
theorem B634807 : Blo 546805 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B3551363 : Blo 546805 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B1847447 : Blo 546805 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B1192331 : Blo 546805 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B2077073 : Blo 546805 2077073 := bstep (se 2 (by rfl) ⟨778902, by rfl⟩ : syracuseStep 2077073 = 1557805) B1557805
theorem B3125861 : Blo 546805 3125861 := bstep (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) B586099
theorem B1847987 : Blo 546805 1847987 := bstep (se 1 (by rfl) ⟨1385990, by rfl⟩ : syracuseStep 1847987 = 2771981) B2771981
theorem B2962241 : Blo 546805 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B5649329 : Blo 546805 5649329 := bstep (se 2 (by rfl) ⟨2118498, by rfl⟩ : syracuseStep 5649329 = 4236997) B4236997
theorem B1848257 : Blo 546805 1848257 := bstep (se 2 (by rfl) ⟨693096, by rfl⟩ : syracuseStep 1848257 = 1386193) B1386193
theorem B2077771 : Blo 546805 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B1881305 : Blo 546805 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B3126545 : Blo 546805 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B1389899 : Blo 546805 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B2078045 : Blo 546805 2078045 := bstep (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) B779267
theorem B2340227 : Blo 546805 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B3519875 : Blo 546805 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B1848797 : Blo 546805 1848797 := bstep (se 3 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 1848797 = 693299) B693299
theorem B11417219 : Blo 546805 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B2340569 : Blo 546805 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B1128217 : Blo 546805 1128217 := bstep (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) B846163
theorem B2078743 : Blo 546805 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B1390871 : Blo 546805 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B1849931 : Blo 546805 1849931 := bstep (se 1 (by rfl) ⟨1387448, by rfl⟩ : syracuseStep 1849931 = 2774897) B2774897
theorem B2079533 : Blo 546805 2079533 := bstep (se 3 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 2079533 = 779825) B779825
theorem B1850201 : Blo 546805 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B1391539 : Blo 546805 1391539 := bstep (se 1 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 1391539 = 2087309) B2087309
theorem B2505779 : Blo 546805 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1391681 : Blo 546805 1391681 := bstep (se 2 (by rfl) ⟨521880, by rfl⟩ : syracuseStep 1391681 = 1043761) B1043761
theorem B4177169 : Blo 546805 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B2342209 : Blo 546805 2342209 := bstep (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) B1756657
theorem B1850903 : Blo 546805 1850903 := bstep (se 1 (by rfl) ⟨1388177, by rfl⟩ : syracuseStep 1850903 = 2776355) B2776355
theorem B38125187 : Blo 546805 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B4439731 : Blo 546805 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B8044505 : Blo 546805 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B1851443 : Blo 546805 1851443 := bstep (se 1 (by rfl) ⟨1388582, by rfl⟩ : syracuseStep 1851443 = 2777165) B2777165
theorem B2080961 : Blo 546805 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B704791 : Blo 546805 704791 := bstep (se 1 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 704791 = 1057187) B1057187
theorem B1392947 : Blo 546805 1392947 := bstep (se 1 (by rfl) ⟨1044710, by rfl⟩ : syracuseStep 1392947 = 2089421) B2089421
theorem B1851713 : Blo 546805 1851713 := bstep (se 2 (by rfl) ⟨694392, by rfl⟩ : syracuseStep 1851713 = 1388785) B1388785
theorem B2769227 : Blo 546805 2769227 := bstep (se 1 (by rfl) ⟨2076920, by rfl⟩ : syracuseStep 2769227 = 4153841) B4153841
theorem B3129779 : Blo 546805 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B3556057 : Blo 546805 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B1393483 : Blo 546805 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B1852253 : Blo 546805 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B1393625 : Blo 546805 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B2671795 : Blo 546805 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1230425 : Blo 546805 1230425 := bstep (se 2 (by rfl) ⟨461409, by rfl⟩ : syracuseStep 1230425 = 922819) B922819
theorem B8439389 : Blo 546805 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B2082449 : Blo 546805 2082449 := bstep (se 2 (by rfl) ⟨780918, by rfl⟩ : syracuseStep 2082449 = 1561837) B1561837
theorem B1230515 : Blo 546805 1230515 := bstep (se 1 (by rfl) ⟨922886, by rfl⟩ : syracuseStep 1230515 = 1845773) B1845773
theorem B1230551 : Blo 546805 1230551 := bstep (se 1 (by rfl) ⟨922913, by rfl⟩ : syracuseStep 1230551 = 1845827) B1845827
theorem B3131237 : Blo 546805 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B4704101 : Blo 546805 4704101 := bstep (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) B882019
theorem B1230731 : Blo 546805 1230731 := bstep (se 1 (by rfl) ⟨923048, by rfl⟩ : syracuseStep 1230731 = 1846097) B1846097
theorem B1984429 : Blo 546805 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B4507571 : Blo 546805 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B2967475 : Blo 546805 2967475 := bstep (se 1 (by rfl) ⟨2225606, by rfl⟩ : syracuseStep 2967475 = 4451213) B4451213
theorem B1230785 : Blo 546805 1230785 := bstep (se 2 (by rfl) ⟨461544, by rfl⟩ : syracuseStep 1230785 = 923089) B923089
theorem B1853387 : Blo 546805 1853387 := bstep (se 1 (by rfl) ⟨1390040, by rfl⟩ : syracuseStep 1853387 = 2780081) B2780081
theorem B2771009 : Blo 546805 2771009 := bstep (se 2 (by rfl) ⟨1039128, by rfl⟩ : syracuseStep 2771009 = 2078257) B2078257
theorem B2082905 : Blo 546805 2082905 := bstep (se 2 (by rfl) ⟨781089, by rfl⟩ : syracuseStep 2082905 = 1562179) B1562179
theorem B1231001 : Blo 546805 1231001 := bstep (se 2 (by rfl) ⟨461625, by rfl⟩ : syracuseStep 1231001 = 923251) B923251
theorem B13355189 : Blo 546805 13355189 := bstep (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) B1252049
theorem B1853657 : Blo 546805 1853657 := bstep (se 2 (by rfl) ⟨695121, by rfl⟩ : syracuseStep 1853657 = 1390243) B1390243
theorem B1231091 : Blo 546805 1231091 := bstep (se 1 (by rfl) ⟨923318, by rfl⟩ : syracuseStep 1231091 = 1846637) B1846637
theorem B6244613 : Blo 546805 6244613 := bstep (se 4 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 6244613 = 1170865) B1170865
theorem B1231127 : Blo 546805 1231127 := bstep (se 1 (by rfl) ⟨923345, by rfl⟩ : syracuseStep 1231127 = 1846691) B1846691
theorem B2083117 : Blo 546805 2083117 := bstep (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) B781169
theorem B3131693 : Blo 546805 3131693 := bstep (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) B1174385
theorem B1231307 : Blo 546805 1231307 := bstep (se 1 (by rfl) ⟨923480, by rfl⟩ : syracuseStep 1231307 = 1846961) B1846961
theorem B1231361 : Blo 546805 1231361 := bstep (se 2 (by rfl) ⟨461760, by rfl⟩ : syracuseStep 1231361 = 923521) B923521
theorem B2673197 : Blo 546805 2673197 := bstep (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) B1002449
theorem B2083421 : Blo 546805 2083421 := bstep (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) B781283
theorem B7031447 : Blo 546805 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B1231577 : Blo 546805 1231577 := bstep (se 2 (by rfl) ⟨461841, by rfl⟩ : syracuseStep 1231577 = 923683) B923683
theorem B1231667 : Blo 546805 1231667 := bstep (se 1 (by rfl) ⟨923750, by rfl⟩ : syracuseStep 1231667 = 1847501) B1847501
theorem B1231703 : Blo 546805 1231703 := bstep (se 1 (by rfl) ⟨923777, by rfl⟩ : syracuseStep 1231703 = 1847555) B1847555
theorem B1854359 : Blo 546805 1854359 := bstep (se 1 (by rfl) ⟨1390769, by rfl⟩ : syracuseStep 1854359 = 2781539) B2781539
theorem B1559513 : Blo 546805 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B3132377 : Blo 546805 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B1231883 : Blo 546805 1231883 := bstep (se 1 (by rfl) ⟨923912, by rfl⟩ : syracuseStep 1231883 = 1847825) B1847825
theorem B740377 : Blo 546805 740377 := bstep (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) B555283
theorem B1231937 : Blo 546805 1231937 := bstep (se 2 (by rfl) ⟨461976, by rfl⟩ : syracuseStep 1231937 = 923953) B923953
theorem B4181057 : Blo 546805 4181057 := bstep (se 2 (by rfl) ⟨1567896, by rfl⟩ : syracuseStep 4181057 = 3135793) B3135793
theorem B3165277 : Blo 546805 3165277 := bstep (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) B1186979
theorem B1232153 : Blo 546805 1232153 := bstep (se 2 (by rfl) ⟨462057, by rfl⟩ : syracuseStep 1232153 = 924115) B924115
theorem B1232243 : Blo 546805 1232243 := bstep (se 1 (by rfl) ⟨924182, by rfl⟩ : syracuseStep 1232243 = 1848365) B1848365
theorem B1232279 : Blo 546805 1232279 := bstep (se 1 (by rfl) ⟨924209, by rfl⟩ : syracuseStep 1232279 = 1848419) B1848419
theorem B1854899 : Blo 546805 1854899 := bstep (se 1 (by rfl) ⟨1391174, by rfl⟩ : syracuseStep 1854899 = 2782349) B2782349
theorem B1232459 : Blo 546805 1232459 := bstep (se 1 (by rfl) ⟨924344, by rfl⟩ : syracuseStep 1232459 = 1848689) B1848689
theorem B1232513 : Blo 546805 1232513 := bstep (se 2 (by rfl) ⟨462192, by rfl⟩ : syracuseStep 1232513 = 924385) B924385
theorem B1855169 : Blo 546805 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B1232729 : Blo 546805 1232729 := bstep (se 2 (by rfl) ⟨462273, by rfl⟩ : syracuseStep 1232729 = 924547) B924547
theorem B1232819 : Blo 546805 1232819 := bstep (se 1 (by rfl) ⟨924614, by rfl⟩ : syracuseStep 1232819 = 1849229) B1849229
theorem B741323 : Blo 546805 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B1232855 : Blo 546805 1232855 := bstep (se 1 (by rfl) ⟨924641, by rfl⟩ : syracuseStep 1232855 = 1849283) B1849283
theorem B2772953 : Blo 546805 2772953 := bstep (se 2 (by rfl) ⟨1039857, by rfl⟩ : syracuseStep 2772953 = 2079715) B2079715
theorem B2379779 : Blo 546805 2379779 := bstep (se 1 (by rfl) ⟨1784834, by rfl⟩ : syracuseStep 2379779 = 3569669) B3569669
theorem B10047557 : Blo 546805 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B1233035 : Blo 546805 1233035 := bstep (se 1 (by rfl) ⟨924776, by rfl⟩ : syracuseStep 1233035 = 1849553) B1849553
theorem B1233089 : Blo 546805 1233089 := bstep (se 2 (by rfl) ⟨462408, by rfl⟩ : syracuseStep 1233089 = 924817) B924817
theorem B1560779 : Blo 546805 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B1003735 : Blo 546805 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B1855709 : Blo 546805 1855709 := bstep (se 3 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 1855709 = 695891) B695891
theorem B1069427 : Blo 546805 1069427 := bstep (se 1 (by rfl) ⟨802070, by rfl⟩ : syracuseStep 1069427 = 1604141) B1604141
theorem B1233305 : Blo 546805 1233305 := bstep (se 2 (by rfl) ⟨462489, by rfl⟩ : syracuseStep 1233305 = 924979) B924979
theorem B741847 : Blo 546805 741847 := bstep (se 1 (by rfl) ⟨556385, by rfl⟩ : syracuseStep 741847 = 1112771) B1112771
theorem B1233395 : Blo 546805 1233395 := bstep (se 1 (by rfl) ⟨925046, by rfl⟩ : syracuseStep 1233395 = 1850093) B1850093
theorem B1233431 : Blo 546805 1233431 := bstep (se 1 (by rfl) ⟨925073, by rfl⟩ : syracuseStep 1233431 = 1850147) B1850147
theorem B1167961 : Blo 546805 1167961 := bstep (se 2 (by rfl) ⟨437985, by rfl⟩ : syracuseStep 1167961 = 875971) B875971
theorem B1233611 : Blo 546805 1233611 := bstep (se 1 (by rfl) ⟨925208, by rfl⟩ : syracuseStep 1233611 = 1850417) B1850417
theorem B1233665 : Blo 546805 1233665 := bstep (se 2 (by rfl) ⟨462624, by rfl⟩ : syracuseStep 1233665 = 925249) B925249
theorem B1758041 : Blo 546805 1758041 := bstep (se 2 (by rfl) ⟨659265, by rfl⟩ : syracuseStep 1758041 = 1318531) B1318531
theorem B4674509 : Blo 546805 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B1233881 : Blo 546805 1233881 := bstep (se 2 (by rfl) ⟨462705, by rfl⟩ : syracuseStep 1233881 = 925411) B925411
theorem B1233971 : Blo 546805 1233971 := bstep (se 1 (by rfl) ⟨925478, by rfl⟩ : syracuseStep 1233971 = 1850957) B1850957
theorem B1234007 : Blo 546805 1234007 := bstep (se 1 (by rfl) ⟨925505, by rfl⟩ : syracuseStep 1234007 = 1851011) B1851011
theorem B2086019 : Blo 546805 2086019 := bstep (se 1 (by rfl) ⟨1564514, by rfl⟩ : syracuseStep 2086019 = 3129029) B3129029
theorem B2086033 : Blo 546805 2086033 := bstep (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) B1564525
theorem B2348291 : Blo 546805 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B5002501 : Blo 546805 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B1234187 : Blo 546805 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B2217239 : Blo 546805 2217239 := bstep (se 1 (by rfl) ⟨1662929, by rfl⟩ : syracuseStep 2217239 = 3325859) B3325859
theorem B1234241 : Blo 546805 1234241 := bstep (se 2 (by rfl) ⟨462840, by rfl⟩ : syracuseStep 1234241 = 925681) B925681
theorem B1856843 : Blo 546805 1856843 := bstep (se 1 (by rfl) ⟨1392632, by rfl⟩ : syracuseStep 1856843 = 2785265) B2785265
theorem B2086337 : Blo 546805 2086337 := bstep (se 2 (by rfl) ⟨782376, by rfl⟩ : syracuseStep 2086337 = 1564753) B1564753
theorem B1234457 : Blo 546805 1234457 := bstep (se 2 (by rfl) ⟨462921, by rfl⟩ : syracuseStep 1234457 = 925843) B925843
theorem B2774573 : Blo 546805 2774573 := bstep (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) B1040465
theorem B1857113 : Blo 546805 1857113 := bstep (se 2 (by rfl) ⟨696417, by rfl⟩ : syracuseStep 1857113 = 1392835) B1392835
theorem B2971237 : Blo 546805 2971237 := bstep (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) B557107
theorem B1234547 : Blo 546805 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B1234583 : Blo 546805 1234583 := bstep (se 1 (by rfl) ⟨925937, by rfl⟩ : syracuseStep 1234583 = 1851875) B1851875
theorem B2643673 : Blo 546805 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B1234763 : Blo 546805 1234763 := bstep (se 1 (by rfl) ⟨926072, by rfl⟩ : syracuseStep 1234763 = 1852145) B1852145
theorem B1234817 : Blo 546805 1234817 := bstep (se 2 (by rfl) ⟨463056, by rfl⟩ : syracuseStep 1234817 = 926113) B926113
theorem B1038233 : Blo 546805 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B546807 : Blo 546805 546807 := bstep (se 1 (by rfl) ⟨410105, by rfl⟩ : syracuseStep 546807 = 820211) B820211
theorem B546827 : Blo 546805 546827 := bstep (se 1 (by rfl) ⟨410120, by rfl⟩ : syracuseStep 546827 = 820241) B820241
theorem B546839 : Blo 546805 546839 := bstep (se 1 (by rfl) ⟨410129, by rfl⟩ : syracuseStep 546839 = 820259) B820259
theorem B546859 : Blo 546805 546859 := bstep (se 1 (by rfl) ⟨410144, by rfl⟩ : syracuseStep 546859 = 820289) B820289
theorem B546871 : Blo 546805 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B546891 : Blo 546805 546891 := bstep (se 1 (by rfl) ⟨410168, by rfl⟩ : syracuseStep 546891 = 820337) B820337
theorem B546903 : Blo 546805 546903 := bstep (se 1 (by rfl) ⟨410177, by rfl⟩ : syracuseStep 546903 = 820355) B820355
theorem B1235033 : Blo 546805 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B2087005 : Blo 546805 2087005 := bstep (se 3 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 2087005 = 782627) B782627
theorem B546923 : Blo 546805 546923 := bstep (se 1 (by rfl) ⟨410192, by rfl⟩ : syracuseStep 546923 = 820385) B820385
theorem B546935 : Blo 546805 546935 := bstep (se 1 (by rfl) ⟨410201, by rfl⟩ : syracuseStep 546935 = 820403) B820403
theorem B546955 : Blo 546805 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B546967 : Blo 546805 546967 := bstep (se 1 (by rfl) ⟨410225, by rfl⟩ : syracuseStep 546967 = 820451) B820451
theorem B546987 : Blo 546805 546987 := bstep (se 1 (by rfl) ⟨410240, by rfl⟩ : syracuseStep 546987 = 820481) B820481
theorem B1235123 : Blo 546805 1235123 := bstep (se 1 (by rfl) ⟨926342, by rfl⟩ : syracuseStep 1235123 = 1852685) B1852685
theorem B546999 : Blo 546805 546999 := bstep (se 1 (by rfl) ⟨410249, by rfl⟩ : syracuseStep 546999 = 820499) B820499
theorem B547019 : Blo 546805 547019 := bstep (se 1 (by rfl) ⟨410264, by rfl⟩ : syracuseStep 547019 = 820529) B820529
theorem B4446413 : Blo 546805 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B547031 : Blo 546805 547031 := bstep (se 1 (by rfl) ⟨410273, by rfl⟩ : syracuseStep 547031 = 820547) B820547
theorem B1235159 : Blo 546805 1235159 := bstep (se 1 (by rfl) ⟨926369, by rfl⟩ : syracuseStep 1235159 = 1852739) B1852739
theorem B547051 : Blo 546805 547051 := bstep (se 1 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 547051 = 820577) B820577
theorem B547063 : Blo 546805 547063 := bstep (se 1 (by rfl) ⟨410297, by rfl⟩ : syracuseStep 547063 = 820595) B820595
theorem B547083 : Blo 546805 547083 := bstep (se 1 (by rfl) ⟨410312, by rfl⟩ : syracuseStep 547083 = 820625) B820625
theorem B547095 : Blo 546805 547095 := bstep (se 1 (by rfl) ⟨410321, by rfl⟩ : syracuseStep 547095 = 820643) B820643
theorem B1857815 : Blo 546805 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B547115 : Blo 546805 547115 := bstep (se 1 (by rfl) ⟨410336, by rfl⟩ : syracuseStep 547115 = 820673) B820673
theorem B547127 : Blo 546805 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B2644289 : Blo 546805 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B547147 : Blo 546805 547147 := bstep (se 1 (by rfl) ⟨410360, by rfl⟩ : syracuseStep 547147 = 820721) B820721
theorem B547159 : Blo 546805 547159 := bstep (se 1 (by rfl) ⟨410369, by rfl⟩ : syracuseStep 547159 = 820739) B820739
theorem B547179 : Blo 546805 547179 := bstep (se 1 (by rfl) ⟨410384, by rfl⟩ : syracuseStep 547179 = 820769) B820769
theorem B547191 : Blo 546805 547191 := bstep (se 1 (by rfl) ⟨410393, by rfl⟩ : syracuseStep 547191 = 820787) B820787
theorem B547211 : Blo 546805 547211 := bstep (se 1 (by rfl) ⟨410408, by rfl⟩ : syracuseStep 547211 = 820817) B820817
theorem B1235339 : Blo 546805 1235339 := bstep (se 1 (by rfl) ⟨926504, by rfl⟩ : syracuseStep 1235339 = 1853009) B1853009
theorem B547223 : Blo 546805 547223 := bstep (se 1 (by rfl) ⟨410417, by rfl⟩ : syracuseStep 547223 = 820835) B820835
theorem B547243 : Blo 546805 547243 := bstep (se 1 (by rfl) ⟨410432, by rfl⟩ : syracuseStep 547243 = 820865) B820865
theorem B547255 : Blo 546805 547255 := bstep (se 1 (by rfl) ⟨410441, by rfl⟩ : syracuseStep 547255 = 820883) B820883
theorem B1235393 : Blo 546805 1235393 := bstep (se 2 (by rfl) ⟨463272, by rfl⟩ : syracuseStep 1235393 = 926545) B926545
theorem B1759681 : Blo 546805 1759681 := bstep (se 2 (by rfl) ⟨659880, by rfl⟩ : syracuseStep 1759681 = 1319761) B1319761
theorem B547275 : Blo 546805 547275 := bstep (se 1 (by rfl) ⟨410456, by rfl⟩ : syracuseStep 547275 = 820913) B820913
theorem B547287 : Blo 546805 547287 := bstep (se 1 (by rfl) ⟨410465, by rfl⟩ : syracuseStep 547287 = 820931) B820931
theorem B547307 : Blo 546805 547307 := bstep (se 1 (by rfl) ⟨410480, by rfl⟩ : syracuseStep 547307 = 820961) B820961
theorem B547319 : Blo 546805 547319 := bstep (se 1 (by rfl) ⟨410489, by rfl⟩ : syracuseStep 547319 = 820979) B820979
theorem B547339 : Blo 546805 547339 := bstep (se 1 (by rfl) ⟨410504, by rfl⟩ : syracuseStep 547339 = 821009) B821009
theorem B547351 : Blo 546805 547351 := bstep (se 1 (by rfl) ⟨410513, by rfl⟩ : syracuseStep 547351 = 821027) B821027
theorem B547371 : Blo 546805 547371 := bstep (se 1 (by rfl) ⟨410528, by rfl⟩ : syracuseStep 547371 = 821057) B821057
theorem B547383 : Blo 546805 547383 := bstep (se 1 (by rfl) ⟨410537, by rfl⟩ : syracuseStep 547383 = 821075) B821075
theorem B547403 : Blo 546805 547403 := bstep (se 1 (by rfl) ⟨410552, by rfl⟩ : syracuseStep 547403 = 821105) B821105
theorem B547415 : Blo 546805 547415 := bstep (se 1 (by rfl) ⟨410561, by rfl⟩ : syracuseStep 547415 = 821123) B821123
theorem B547435 : Blo 546805 547435 := bstep (se 1 (by rfl) ⟨410576, by rfl⟩ : syracuseStep 547435 = 821153) B821153
theorem B547447 : Blo 546805 547447 := bstep (se 1 (by rfl) ⟨410585, by rfl⟩ : syracuseStep 547447 = 821171) B821171
theorem B1038977 : Blo 546805 1038977 := bstep (se 2 (by rfl) ⟨389616, by rfl⟩ : syracuseStep 1038977 = 779233) B779233
theorem B547467 : Blo 546805 547467 := bstep (se 1 (by rfl) ⟨410600, by rfl⟩ : syracuseStep 547467 = 821201) B821201
theorem B547479 : Blo 546805 547479 := bstep (se 1 (by rfl) ⟨410609, by rfl⟩ : syracuseStep 547479 = 821219) B821219
theorem B1235609 : Blo 546805 1235609 := bstep (se 2 (by rfl) ⟨463353, by rfl⟩ : syracuseStep 1235609 = 926707) B926707
theorem B547499 : Blo 546805 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B547511 : Blo 546805 547511 := bstep (se 1 (by rfl) ⟨410633, by rfl⟩ : syracuseStep 547511 = 821267) B821267
theorem B547531 : Blo 546805 547531 := bstep (se 1 (by rfl) ⟨410648, by rfl⟩ : syracuseStep 547531 = 821297) B821297
theorem B547543 : Blo 546805 547543 := bstep (se 1 (by rfl) ⟨410657, by rfl⟩ : syracuseStep 547543 = 821315) B821315
theorem B547563 : Blo 546805 547563 := bstep (se 1 (by rfl) ⟨410672, by rfl⟩ : syracuseStep 547563 = 821345) B821345
theorem B1235699 : Blo 546805 1235699 := bstep (se 1 (by rfl) ⟨926774, by rfl⟩ : syracuseStep 1235699 = 1853549) B1853549
theorem B547575 : Blo 546805 547575 := bstep (se 1 (by rfl) ⟨410681, by rfl⟩ : syracuseStep 547575 = 821363) B821363
theorem B547595 : Blo 546805 547595 := bstep (se 1 (by rfl) ⟨410696, by rfl⟩ : syracuseStep 547595 = 821393) B821393
theorem B547607 : Blo 546805 547607 := bstep (se 1 (by rfl) ⟨410705, by rfl⟩ : syracuseStep 547607 = 821411) B821411
theorem B1235735 : Blo 546805 1235735 := bstep (se 1 (by rfl) ⟨926801, by rfl⟩ : syracuseStep 1235735 = 1853603) B1853603
theorem B547627 : Blo 546805 547627 := bstep (se 1 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 547627 = 821441) B821441
theorem B1858355 : Blo 546805 1858355 := bstep (se 1 (by rfl) ⟨1393766, by rfl⟩ : syracuseStep 1858355 = 2787533) B2787533
theorem B547639 : Blo 546805 547639 := bstep (se 1 (by rfl) ⟨410729, by rfl⟩ : syracuseStep 547639 = 821459) B821459
theorem B547659 : Blo 546805 547659 := bstep (se 1 (by rfl) ⟨410744, by rfl⟩ : syracuseStep 547659 = 821489) B821489
theorem B547671 : Blo 546805 547671 := bstep (se 1 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 547671 = 821507) B821507
theorem B2349917 : Blo 546805 2349917 := bstep (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) B881219
theorem B547691 : Blo 546805 547691 := bstep (se 1 (by rfl) ⟨410768, by rfl⟩ : syracuseStep 547691 = 821537) B821537
theorem B547703 : Blo 546805 547703 := bstep (se 1 (by rfl) ⟨410777, by rfl⟩ : syracuseStep 547703 = 821555) B821555
theorem B1039243 : Blo 546805 1039243 := bstep (se 1 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 1039243 = 1558865) B1558865
theorem B547723 : Blo 546805 547723 := bstep (se 1 (by rfl) ⟨410792, by rfl⟩ : syracuseStep 547723 = 821585) B821585
theorem B547735 : Blo 546805 547735 := bstep (se 1 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 547735 = 821603) B821603
theorem B547755 : Blo 546805 547755 := bstep (se 1 (by rfl) ⟨410816, by rfl⟩ : syracuseStep 547755 = 821633) B821633
theorem B547767 : Blo 546805 547767 := bstep (se 1 (by rfl) ⟨410825, by rfl⟩ : syracuseStep 547767 = 821651) B821651
theorem B547787 : Blo 546805 547787 := bstep (se 1 (by rfl) ⟨410840, by rfl⟩ : syracuseStep 547787 = 821681) B821681
theorem B1170379 : Blo 546805 1170379 := bstep (se 1 (by rfl) ⟨877784, by rfl⟩ : syracuseStep 1170379 = 1755569) B1755569
theorem B1235915 : Blo 546805 1235915 := bstep (se 1 (by rfl) ⟨926936, by rfl⟩ : syracuseStep 1235915 = 1853873) B1853873
theorem B547799 : Blo 546805 547799 := bstep (se 1 (by rfl) ⟨410849, by rfl⟩ : syracuseStep 547799 = 821699) B821699
theorem B547819 : Blo 546805 547819 := bstep (se 1 (by rfl) ⟨410864, by rfl⟩ : syracuseStep 547819 = 821729) B821729
theorem B547831 : Blo 546805 547831 := bstep (se 1 (by rfl) ⟨410873, by rfl⟩ : syracuseStep 547831 = 821747) B821747
theorem B1235969 : Blo 546805 1235969 := bstep (se 2 (by rfl) ⟨463488, by rfl⟩ : syracuseStep 1235969 = 926977) B926977
theorem B547851 : Blo 546805 547851 := bstep (se 1 (by rfl) ⟨410888, by rfl⟩ : syracuseStep 547851 = 821777) B821777
theorem B547863 : Blo 546805 547863 := bstep (se 1 (by rfl) ⟨410897, by rfl⟩ : syracuseStep 547863 = 821795) B821795
theorem B1170455 : Blo 546805 1170455 := bstep (se 1 (by rfl) ⟨877841, by rfl⟩ : syracuseStep 1170455 = 1755683) B1755683
theorem B547883 : Blo 546805 547883 := bstep (se 1 (by rfl) ⟨410912, by rfl⟩ : syracuseStep 547883 = 821825) B821825
theorem B547895 : Blo 546805 547895 := bstep (se 1 (by rfl) ⟨410921, by rfl⟩ : syracuseStep 547895 = 821843) B821843
theorem B1858625 : Blo 546805 1858625 := bstep (se 2 (by rfl) ⟨696984, by rfl⟩ : syracuseStep 1858625 = 1393969) B1393969
theorem B547915 : Blo 546805 547915 := bstep (se 1 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 547915 = 821873) B821873
theorem B547927 : Blo 546805 547927 := bstep (se 1 (by rfl) ⟨410945, by rfl⟩ : syracuseStep 547927 = 821891) B821891
theorem B547947 : Blo 546805 547947 := bstep (se 1 (by rfl) ⟨410960, by rfl⟩ : syracuseStep 547947 = 821921) B821921
theorem B547959 : Blo 546805 547959 := bstep (se 1 (by rfl) ⟨410969, by rfl⟩ : syracuseStep 547959 = 821939) B821939
theorem B547979 : Blo 546805 547979 := bstep (se 1 (by rfl) ⟨410984, by rfl⟩ : syracuseStep 547979 = 821969) B821969
theorem B547991 : Blo 546805 547991 := bstep (se 1 (by rfl) ⟨410993, by rfl⟩ : syracuseStep 547991 = 821987) B821987
theorem B9395351 : Blo 546805 9395351 := bstep (se 1 (by rfl) ⟨7046513, by rfl⟩ : syracuseStep 9395351 = 14093027) B14093027
theorem B548011 : Blo 546805 548011 := bstep (se 1 (by rfl) ⟨411008, by rfl⟩ : syracuseStep 548011 = 822017) B822017
theorem B548023 : Blo 546805 548023 := bstep (se 1 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 548023 = 822035) B822035
theorem B548043 : Blo 546805 548043 := bstep (se 1 (by rfl) ⟨411032, by rfl⟩ : syracuseStep 548043 = 822065) B822065
theorem B548055 : Blo 546805 548055 := bstep (se 1 (by rfl) ⟨411041, by rfl⟩ : syracuseStep 548055 = 822083) B822083
theorem B1236185 : Blo 546805 1236185 := bstep (se 2 (by rfl) ⟨463569, by rfl⟩ : syracuseStep 1236185 = 927139) B927139
theorem B548075 : Blo 546805 548075 := bstep (se 1 (by rfl) ⟨411056, by rfl⟩ : syracuseStep 548075 = 822113) B822113
theorem B548087 : Blo 546805 548087 := bstep (se 1 (by rfl) ⟨411065, by rfl⟩ : syracuseStep 548087 = 822131) B822131
theorem B548107 : Blo 546805 548107 := bstep (se 1 (by rfl) ⟨411080, by rfl⟩ : syracuseStep 548107 = 822161) B822161
theorem B548119 : Blo 546805 548119 := bstep (se 1 (by rfl) ⟨411089, by rfl⟩ : syracuseStep 548119 = 822179) B822179
theorem B4676899 : Blo 546805 4676899 := bstep (se 1 (by rfl) ⟨3507674, by rfl⟩ : syracuseStep 4676899 = 7015349) B7015349
theorem B548139 : Blo 546805 548139 := bstep (se 1 (by rfl) ⟨411104, by rfl⟩ : syracuseStep 548139 = 822209) B822209
theorem B1236275 : Blo 546805 1236275 := bstep (se 1 (by rfl) ⟨927206, by rfl⟩ : syracuseStep 1236275 = 1854413) B1854413
theorem B548151 : Blo 546805 548151 := bstep (se 1 (by rfl) ⟨411113, by rfl⟩ : syracuseStep 548151 = 822227) B822227
theorem B1039691 : Blo 546805 1039691 := bstep (se 1 (by rfl) ⟨779768, by rfl⟩ : syracuseStep 1039691 = 1559537) B1559537
theorem B548171 : Blo 546805 548171 := bstep (se 1 (by rfl) ⟨411128, by rfl⟩ : syracuseStep 548171 = 822257) B822257
theorem B548183 : Blo 546805 548183 := bstep (se 1 (by rfl) ⟨411137, by rfl⟩ : syracuseStep 548183 = 822275) B822275
theorem B1236311 : Blo 546805 1236311 := bstep (se 1 (by rfl) ⟨927233, by rfl⟩ : syracuseStep 1236311 = 1854467) B1854467
theorem B2088281 : Blo 546805 2088281 := bstep (se 2 (by rfl) ⟨783105, by rfl⟩ : syracuseStep 2088281 = 1566211) B1566211
theorem B548203 : Blo 546805 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B548215 : Blo 546805 548215 := bstep (se 1 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 548215 = 822323) B822323
theorem B548235 : Blo 546805 548235 := bstep (se 1 (by rfl) ⟨411176, by rfl⟩ : syracuseStep 548235 = 822353) B822353
theorem B548247 : Blo 546805 548247 := bstep (se 1 (by rfl) ⟨411185, by rfl⟩ : syracuseStep 548247 = 822371) B822371
theorem B548267 : Blo 546805 548267 := bstep (se 1 (by rfl) ⟨411200, by rfl⟩ : syracuseStep 548267 = 822401) B822401
theorem B1498547 : Blo 546805 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B548279 : Blo 546805 548279 := bstep (se 1 (by rfl) ⟨411209, by rfl⟩ : syracuseStep 548279 = 822419) B822419
theorem B548299 : Blo 546805 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B548311 : Blo 546805 548311 := bstep (se 1 (by rfl) ⟨411233, by rfl⟩ : syracuseStep 548311 = 822467) B822467
theorem B4447705 : Blo 546805 4447705 := bstep (se 2 (by rfl) ⟨1667889, by rfl⟩ : syracuseStep 4447705 = 3335779) B3335779
theorem B548331 : Blo 546805 548331 := bstep (se 1 (by rfl) ⟨411248, by rfl⟩ : syracuseStep 548331 = 822497) B822497
theorem B548343 : Blo 546805 548343 := bstep (se 1 (by rfl) ⟨411257, by rfl⟩ : syracuseStep 548343 = 822515) B822515
theorem B1039873 : Blo 546805 1039873 := bstep (se 2 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 1039873 = 779905) B779905
theorem B548363 : Blo 546805 548363 := bstep (se 1 (by rfl) ⟨411272, by rfl⟩ : syracuseStep 548363 = 822545) B822545
theorem B1236491 : Blo 546805 1236491 := bstep (se 1 (by rfl) ⟨927368, by rfl⟩ : syracuseStep 1236491 = 1854737) B1854737
theorem B548375 : Blo 546805 548375 := bstep (se 1 (by rfl) ⟨411281, by rfl⟩ : syracuseStep 548375 = 822563) B822563
theorem B2350615 : Blo 546805 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B548395 : Blo 546805 548395 := bstep (se 1 (by rfl) ⟨411296, by rfl⟩ : syracuseStep 548395 = 822593) B822593
theorem B548407 : Blo 546805 548407 := bstep (se 1 (by rfl) ⟨411305, by rfl⟩ : syracuseStep 548407 = 822611) B822611
theorem B1236545 : Blo 546805 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B548427 : Blo 546805 548427 := bstep (se 1 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 548427 = 822641) B822641
theorem B548439 : Blo 546805 548439 := bstep (se 1 (by rfl) ⟨411329, by rfl⟩ : syracuseStep 548439 = 822659) B822659
theorem B548459 : Blo 546805 548459 := bstep (se 1 (by rfl) ⟨411344, by rfl⟩ : syracuseStep 548459 = 822689) B822689
theorem B548471 : Blo 546805 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B548491 : Blo 546805 548491 := bstep (se 1 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 548491 = 822737) B822737
theorem B548503 : Blo 546805 548503 := bstep (se 1 (by rfl) ⟨411377, by rfl⟩ : syracuseStep 548503 = 822755) B822755
theorem B548523 : Blo 546805 548523 := bstep (se 1 (by rfl) ⟨411392, by rfl⟩ : syracuseStep 548523 = 822785) B822785
theorem B548535 : Blo 546805 548535 := bstep (se 1 (by rfl) ⟨411401, by rfl⟩ : syracuseStep 548535 = 822803) B822803
theorem B548555 : Blo 546805 548555 := bstep (se 1 (by rfl) ⟨411416, by rfl⟩ : syracuseStep 548555 = 822833) B822833
theorem B548567 : Blo 546805 548567 := bstep (se 1 (by rfl) ⟨411425, by rfl⟩ : syracuseStep 548567 = 822851) B822851
theorem B548587 : Blo 546805 548587 := bstep (se 1 (by rfl) ⟨411440, by rfl⟩ : syracuseStep 548587 = 822881) B822881
theorem B548599 : Blo 546805 548599 := bstep (se 1 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 548599 = 822899) B822899
theorem B548619 : Blo 546805 548619 := bstep (se 1 (by rfl) ⟨411464, by rfl⟩ : syracuseStep 548619 = 822929) B822929
theorem B548631 : Blo 546805 548631 := bstep (se 1 (by rfl) ⟨411473, by rfl⟩ : syracuseStep 548631 = 822947) B822947
theorem B1236761 : Blo 546805 1236761 := bstep (se 2 (by rfl) ⟨463785, by rfl⟩ : syracuseStep 1236761 = 927571) B927571
theorem B548651 : Blo 546805 548651 := bstep (se 1 (by rfl) ⟨411488, by rfl⟩ : syracuseStep 548651 = 822977) B822977
theorem B548663 : Blo 546805 548663 := bstep (se 1 (by rfl) ⟨411497, by rfl⟩ : syracuseStep 548663 = 822995) B822995
theorem B548683 : Blo 546805 548683 := bstep (se 1 (by rfl) ⟨411512, by rfl⟩ : syracuseStep 548683 = 823025) B823025
theorem B1040215 : Blo 546805 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B548695 : Blo 546805 548695 := bstep (se 1 (by rfl) ⟨411521, by rfl⟩ : syracuseStep 548695 = 823043) B823043
theorem B548715 : Blo 546805 548715 := bstep (se 1 (by rfl) ⟨411536, by rfl⟩ : syracuseStep 548715 = 823073) B823073
theorem B1236851 : Blo 546805 1236851 := bstep (se 1 (by rfl) ⟨927638, by rfl⟩ : syracuseStep 1236851 = 1855277) B1855277
theorem B548727 : Blo 546805 548727 := bstep (se 1 (by rfl) ⟨411545, by rfl⟩ : syracuseStep 548727 = 823091) B823091
theorem B548747 : Blo 546805 548747 := bstep (se 1 (by rfl) ⟨411560, by rfl⟩ : syracuseStep 548747 = 823121) B823121
theorem B548759 : Blo 546805 548759 := bstep (se 1 (by rfl) ⟨411569, by rfl⟩ : syracuseStep 548759 = 823139) B823139
theorem B1236887 : Blo 546805 1236887 := bstep (se 1 (by rfl) ⟨927665, by rfl⟩ : syracuseStep 1236887 = 1855331) B1855331
theorem B548779 : Blo 546805 548779 := bstep (se 1 (by rfl) ⟨411584, by rfl⟩ : syracuseStep 548779 = 823169) B823169
theorem B548791 : Blo 546805 548791 := bstep (se 1 (by rfl) ⟨411593, by rfl⟩ : syracuseStep 548791 = 823187) B823187
theorem B548811 : Blo 546805 548811 := bstep (se 1 (by rfl) ⟨411608, by rfl⟩ : syracuseStep 548811 = 823217) B823217
theorem B548823 : Blo 546805 548823 := bstep (se 1 (by rfl) ⟨411617, by rfl⟩ : syracuseStep 548823 = 823235) B823235
theorem B548843 : Blo 546805 548843 := bstep (se 1 (by rfl) ⟨411632, by rfl⟩ : syracuseStep 548843 = 823265) B823265
theorem B548855 : Blo 546805 548855 := bstep (se 1 (by rfl) ⟨411641, by rfl⟩ : syracuseStep 548855 = 823283) B823283
theorem B548875 : Blo 546805 548875 := bstep (se 1 (by rfl) ⟨411656, by rfl⟩ : syracuseStep 548875 = 823313) B823313
theorem B548887 : Blo 546805 548887 := bstep (se 1 (by rfl) ⟨411665, by rfl⟩ : syracuseStep 548887 = 823331) B823331
theorem B548907 : Blo 546805 548907 := bstep (se 1 (by rfl) ⟨411680, by rfl⟩ : syracuseStep 548907 = 823361) B823361
theorem B1040435 : Blo 546805 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B548919 : Blo 546805 548919 := bstep (se 1 (by rfl) ⟨411689, by rfl⟩ : syracuseStep 548919 = 823379) B823379
theorem B548939 : Blo 546805 548939 := bstep (se 1 (by rfl) ⟨411704, by rfl⟩ : syracuseStep 548939 = 823409) B823409
theorem B1237067 : Blo 546805 1237067 := bstep (se 1 (by rfl) ⟨927800, by rfl⟩ : syracuseStep 1237067 = 1855601) B1855601
theorem B548951 : Blo 546805 548951 := bstep (se 1 (by rfl) ⟨411713, by rfl⟩ : syracuseStep 548951 = 823427) B823427
theorem B548971 : Blo 546805 548971 := bstep (se 1 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 548971 = 823457) B823457
theorem B548983 : Blo 546805 548983 := bstep (se 1 (by rfl) ⟨411737, by rfl⟩ : syracuseStep 548983 = 823475) B823475
theorem B1237121 : Blo 546805 1237121 := bstep (se 2 (by rfl) ⟨463920, by rfl⟩ : syracuseStep 1237121 = 927841) B927841
theorem B549003 : Blo 546805 549003 := bstep (se 1 (by rfl) ⟨411752, by rfl⟩ : syracuseStep 549003 = 823505) B823505
theorem B8446103 : Blo 546805 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B549015 : Blo 546805 549015 := bstep (se 1 (by rfl) ⟨411761, by rfl⟩ : syracuseStep 549015 = 823523) B823523
theorem B549035 : Blo 546805 549035 := bstep (se 1 (by rfl) ⟨411776, by rfl⟩ : syracuseStep 549035 = 823553) B823553
theorem B549047 : Blo 546805 549047 := bstep (se 1 (by rfl) ⟨411785, by rfl⟩ : syracuseStep 549047 = 823571) B823571
theorem B549067 : Blo 546805 549067 := bstep (se 1 (by rfl) ⟨411800, by rfl⟩ : syracuseStep 549067 = 823601) B823601
theorem B549079 : Blo 546805 549079 := bstep (se 1 (by rfl) ⟨411809, by rfl⟩ : syracuseStep 549079 = 823619) B823619
theorem B549099 : Blo 546805 549099 := bstep (se 1 (by rfl) ⟨411824, by rfl⟩ : syracuseStep 549099 = 823649) B823649
theorem B549111 : Blo 546805 549111 := bstep (se 1 (by rfl) ⟨411833, by rfl⟩ : syracuseStep 549111 = 823667) B823667
theorem B549131 : Blo 546805 549131 := bstep (se 1 (by rfl) ⟨411848, by rfl⟩ : syracuseStep 549131 = 823697) B823697
theorem B1040663 : Blo 546805 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B549143 : Blo 546805 549143 := bstep (se 1 (by rfl) ⟨411857, by rfl⟩ : syracuseStep 549143 = 823715) B823715
theorem B549163 : Blo 546805 549163 := bstep (se 1 (by rfl) ⟨411872, by rfl⟩ : syracuseStep 549163 = 823745) B823745
theorem B10314029 : Blo 546805 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B549175 : Blo 546805 549175 := bstep (se 1 (by rfl) ⟨411881, by rfl⟩ : syracuseStep 549175 = 823763) B823763
theorem B549195 : Blo 546805 549195 := bstep (se 1 (by rfl) ⟨411896, by rfl⟩ : syracuseStep 549195 = 823793) B823793
theorem B549207 : Blo 546805 549207 := bstep (se 1 (by rfl) ⟨411905, by rfl⟩ : syracuseStep 549207 = 823811) B823811
theorem B1237337 : Blo 546805 1237337 := bstep (se 2 (by rfl) ⟨464001, by rfl⟩ : syracuseStep 1237337 = 928003) B928003
theorem B549227 : Blo 546805 549227 := bstep (se 1 (by rfl) ⟨411920, by rfl⟩ : syracuseStep 549227 = 823841) B823841
theorem B549239 : Blo 546805 549239 := bstep (se 1 (by rfl) ⟨411929, by rfl⟩ : syracuseStep 549239 = 823859) B823859
theorem B549259 : Blo 546805 549259 := bstep (se 1 (by rfl) ⟨411944, by rfl⟩ : syracuseStep 549259 = 823889) B823889
theorem B549271 : Blo 546805 549271 := bstep (se 1 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 549271 = 823907) B823907
theorem B549291 : Blo 546805 549291 := bstep (se 1 (by rfl) ⟨411968, by rfl⟩ : syracuseStep 549291 = 823937) B823937
theorem B1237427 : Blo 546805 1237427 := bstep (se 1 (by rfl) ⟨928070, by rfl⟩ : syracuseStep 1237427 = 1856141) B1856141
theorem B549303 : Blo 546805 549303 := bstep (se 1 (by rfl) ⟨411977, by rfl⟩ : syracuseStep 549303 = 823955) B823955
theorem B549323 : Blo 546805 549323 := bstep (se 1 (by rfl) ⟨411992, by rfl⟩ : syracuseStep 549323 = 823985) B823985
theorem B549335 : Blo 546805 549335 := bstep (se 1 (by rfl) ⟨412001, by rfl⟩ : syracuseStep 549335 = 824003) B824003
theorem B1237463 : Blo 546805 1237463 := bstep (se 1 (by rfl) ⟨928097, by rfl⟩ : syracuseStep 1237463 = 1856195) B1856195
theorem B549355 : Blo 546805 549355 := bstep (se 1 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 549355 = 824033) B824033
theorem B549367 : Blo 546805 549367 := bstep (se 1 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 549367 = 824051) B824051
theorem B549387 : Blo 546805 549387 := bstep (se 1 (by rfl) ⟨412040, by rfl⟩ : syracuseStep 549387 = 824081) B824081
theorem B549399 : Blo 546805 549399 := bstep (se 1 (by rfl) ⟨412049, by rfl⟩ : syracuseStep 549399 = 824099) B824099
theorem B1040921 : Blo 546805 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B549419 : Blo 546805 549419 := bstep (se 1 (by rfl) ⟨412064, by rfl⟩ : syracuseStep 549419 = 824129) B824129
theorem B549431 : Blo 546805 549431 := bstep (se 1 (by rfl) ⟨412073, by rfl⟩ : syracuseStep 549431 = 824147) B824147
theorem B8872523 : Blo 546805 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B549451 : Blo 546805 549451 := bstep (se 1 (by rfl) ⟨412088, by rfl⟩ : syracuseStep 549451 = 824177) B824177
theorem B549463 : Blo 546805 549463 := bstep (se 1 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 549463 = 824195) B824195
theorem B7889501 : Blo 546805 7889501 := bstep (se 3 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 7889501 = 2958563) B2958563
theorem B549483 : Blo 546805 549483 := bstep (se 1 (by rfl) ⟨412112, by rfl⟩ : syracuseStep 549483 = 824225) B824225
theorem B549495 : Blo 546805 549495 := bstep (se 1 (by rfl) ⟨412121, by rfl⟩ : syracuseStep 549495 = 824243) B824243
theorem B778891 : Blo 546805 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B549515 : Blo 546805 549515 := bstep (se 1 (by rfl) ⟨412136, by rfl⟩ : syracuseStep 549515 = 824273) B824273
theorem B1237643 : Blo 546805 1237643 := bstep (se 1 (by rfl) ⟨928232, by rfl⟩ : syracuseStep 1237643 = 1856465) B1856465
theorem B549527 : Blo 546805 549527 := bstep (se 1 (by rfl) ⟨412145, by rfl⟩ : syracuseStep 549527 = 824291) B824291
theorem B549547 : Blo 546805 549547 := bstep (se 1 (by rfl) ⟨412160, by rfl⟩ : syracuseStep 549547 = 824321) B824321
theorem B549559 : Blo 546805 549559 := bstep (se 1 (by rfl) ⟨412169, by rfl⟩ : syracuseStep 549559 = 824339) B824339
theorem B1237697 : Blo 546805 1237697 := bstep (se 2 (by rfl) ⟨464136, by rfl⟩ : syracuseStep 1237697 = 928273) B928273
theorem B549579 : Blo 546805 549579 := bstep (se 1 (by rfl) ⟨412184, by rfl⟩ : syracuseStep 549579 = 824369) B824369
theorem B549591 : Blo 546805 549591 := bstep (se 1 (by rfl) ⟨412193, by rfl⟩ : syracuseStep 549591 = 824387) B824387
theorem B549611 : Blo 546805 549611 := bstep (se 1 (by rfl) ⟨412208, by rfl⟩ : syracuseStep 549611 = 824417) B824417
theorem B549623 : Blo 546805 549623 := bstep (se 1 (by rfl) ⟨412217, by rfl⟩ : syracuseStep 549623 = 824435) B824435
theorem B1172225 : Blo 546805 1172225 := bstep (se 2 (by rfl) ⟨439584, by rfl⟩ : syracuseStep 1172225 = 879169) B879169
theorem B549643 : Blo 546805 549643 := bstep (se 1 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 549643 = 824465) B824465
theorem B2974481 : Blo 546805 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B549655 : Blo 546805 549655 := bstep (se 1 (by rfl) ⟨412241, by rfl⟩ : syracuseStep 549655 = 824483) B824483
theorem B549675 : Blo 546805 549675 := bstep (se 1 (by rfl) ⟨412256, by rfl⟩ : syracuseStep 549675 = 824513) B824513
theorem B549687 : Blo 546805 549687 := bstep (se 1 (by rfl) ⟨412265, by rfl⟩ : syracuseStep 549687 = 824531) B824531
theorem B549707 : Blo 546805 549707 := bstep (se 1 (by rfl) ⟨412280, by rfl⟩ : syracuseStep 549707 = 824561) B824561
theorem B549719 : Blo 546805 549719 := bstep (se 1 (by rfl) ⟨412289, by rfl⟩ : syracuseStep 549719 = 824579) B824579
theorem B549739 : Blo 546805 549739 := bstep (se 1 (by rfl) ⟨412304, by rfl⟩ : syracuseStep 549739 = 824609) B824609
theorem B549751 : Blo 546805 549751 := bstep (se 1 (by rfl) ⟨412313, by rfl⟩ : syracuseStep 549751 = 824627) B824627
theorem B615307 : Blo 546805 615307 := bstep (se 1 (by rfl) ⟨461480, by rfl⟩ : syracuseStep 615307 = 922961) B922961
theorem B549771 : Blo 546805 549771 := bstep (se 1 (by rfl) ⟨412328, by rfl⟩ : syracuseStep 549771 = 824657) B824657
theorem B2352017 : Blo 546805 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B779159 : Blo 546805 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B549783 : Blo 546805 549783 := bstep (se 1 (by rfl) ⟨412337, by rfl⟩ : syracuseStep 549783 = 824675) B824675
theorem B1237913 : Blo 546805 1237913 := bstep (se 2 (by rfl) ⟨464217, by rfl⟩ : syracuseStep 1237913 = 928435) B928435
theorem B549803 : Blo 546805 549803 := bstep (se 1 (by rfl) ⟨412352, by rfl⟩ : syracuseStep 549803 = 824705) B824705
theorem B15000497 : Blo 546805 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B1041331 : Blo 546805 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B2089907 : Blo 546805 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B549815 : Blo 546805 549815 := bstep (se 1 (by rfl) ⟨412361, by rfl⟩ : syracuseStep 549815 = 824723) B824723
theorem B2089921 : Blo 546805 2089921 := bstep (se 2 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 2089921 = 1567441) B1567441
theorem B549835 : Blo 546805 549835 := bstep (se 1 (by rfl) ⟨412376, by rfl⟩ : syracuseStep 549835 = 824753) B824753
theorem B549847 : Blo 546805 549847 := bstep (se 1 (by rfl) ⟨412385, by rfl⟩ : syracuseStep 549847 = 824771) B824771
theorem B811993 : Blo 546805 811993 := bstep (se 2 (by rfl) ⟨304497, by rfl⟩ : syracuseStep 811993 = 608995) B608995
theorem B877529 : Blo 546805 877529 := bstep (se 2 (by rfl) ⟨329073, by rfl⟩ : syracuseStep 877529 = 658147) B658147
theorem B549867 : Blo 546805 549867 := bstep (se 1 (by rfl) ⟨412400, by rfl⟩ : syracuseStep 549867 = 824801) B824801
theorem B1238003 : Blo 546805 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B615415 : Blo 546805 615415 := bstep (se 1 (by rfl) ⟨461561, by rfl⟩ : syracuseStep 615415 = 923123) B923123
theorem B549879 : Blo 546805 549879 := bstep (se 1 (by rfl) ⟨412409, by rfl⟩ : syracuseStep 549879 = 824819) B824819
theorem B549899 : Blo 546805 549899 := bstep (se 1 (by rfl) ⟨412424, by rfl⟩ : syracuseStep 549899 = 824849) B824849
theorem B549911 : Blo 546805 549911 := bstep (se 1 (by rfl) ⟨412433, by rfl⟩ : syracuseStep 549911 = 824867) B824867
theorem B1238039 : Blo 546805 1238039 := bstep (se 1 (by rfl) ⟨928529, by rfl⟩ : syracuseStep 1238039 = 1857059) B1857059
theorem B549931 : Blo 546805 549931 := bstep (se 1 (by rfl) ⟨412448, by rfl⟩ : syracuseStep 549931 = 824897) B824897
theorem B549943 : Blo 546805 549943 := bstep (se 1 (by rfl) ⟨412457, by rfl⟩ : syracuseStep 549943 = 824915) B824915
theorem B549963 : Blo 546805 549963 := bstep (se 1 (by rfl) ⟨412472, by rfl⟩ : syracuseStep 549963 = 824945) B824945
theorem B549975 : Blo 546805 549975 := bstep (se 1 (by rfl) ⟨412481, by rfl⟩ : syracuseStep 549975 = 824963) B824963
theorem B549995 : Blo 546805 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B550007 : Blo 546805 550007 := bstep (se 1 (by rfl) ⟨412505, by rfl⟩ : syracuseStep 550007 = 825011) B825011
theorem B550027 : Blo 546805 550027 := bstep (se 1 (by rfl) ⟨412520, by rfl⟩ : syracuseStep 550027 = 825041) B825041
theorem B550039 : Blo 546805 550039 := bstep (se 1 (by rfl) ⟨412529, by rfl⟩ : syracuseStep 550039 = 825059) B825059
theorem B615595 : Blo 546805 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B550059 : Blo 546805 550059 := bstep (se 1 (by rfl) ⟨412544, by rfl⟩ : syracuseStep 550059 = 825089) B825089
theorem B550071 : Blo 546805 550071 := bstep (se 1 (by rfl) ⟨412553, by rfl⟩ : syracuseStep 550071 = 825107) B825107
theorem B550091 : Blo 546805 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B1238219 : Blo 546805 1238219 := bstep (se 1 (by rfl) ⟨928664, by rfl⟩ : syracuseStep 1238219 = 1857329) B1857329
theorem B550103 : Blo 546805 550103 := bstep (se 1 (by rfl) ⟨412577, by rfl⟩ : syracuseStep 550103 = 825155) B825155
theorem B550123 : Blo 546805 550123 := bstep (se 1 (by rfl) ⟨412592, by rfl⟩ : syracuseStep 550123 = 825185) B825185
theorem B550135 : Blo 546805 550135 := bstep (se 1 (by rfl) ⟨412601, by rfl⟩ : syracuseStep 550135 = 825203) B825203
theorem B1238273 : Blo 546805 1238273 := bstep (se 2 (by rfl) ⟨464352, by rfl⟩ : syracuseStep 1238273 = 928705) B928705
theorem B550155 : Blo 546805 550155 := bstep (se 1 (by rfl) ⟨412616, by rfl⟩ : syracuseStep 550155 = 825233) B825233
theorem B615703 : Blo 546805 615703 := bstep (se 1 (by rfl) ⟨461777, by rfl⟩ : syracuseStep 615703 = 923555) B923555
theorem B550167 : Blo 546805 550167 := bstep (se 1 (by rfl) ⟨412625, by rfl⟩ : syracuseStep 550167 = 825251) B825251
theorem B550187 : Blo 546805 550187 := bstep (se 1 (by rfl) ⟨412640, by rfl⟩ : syracuseStep 550187 = 825281) B825281
theorem B550199 : Blo 546805 550199 := bstep (se 1 (by rfl) ⟨412649, by rfl⟩ : syracuseStep 550199 = 825299) B825299
theorem B550219 : Blo 546805 550219 := bstep (se 1 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 550219 = 825329) B825329
theorem B550231 : Blo 546805 550231 := bstep (se 1 (by rfl) ⟨412673, by rfl⟩ : syracuseStep 550231 = 825347) B825347
theorem B2778461 : Blo 546805 2778461 := bstep (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) B1041923
theorem B550251 : Blo 546805 550251 := bstep (se 1 (by rfl) ⟨412688, by rfl⟩ : syracuseStep 550251 = 825377) B825377
theorem B550263 : Blo 546805 550263 := bstep (se 1 (by rfl) ⟨412697, by rfl⟩ : syracuseStep 550263 = 825395) B825395
theorem B550283 : Blo 546805 550283 := bstep (se 1 (by rfl) ⟨412712, by rfl⟩ : syracuseStep 550283 = 825425) B825425
theorem B550295 : Blo 546805 550295 := bstep (se 1 (by rfl) ⟨412721, by rfl⟩ : syracuseStep 550295 = 825443) B825443
theorem B1041817 : Blo 546805 1041817 := bstep (se 2 (by rfl) ⟨390681, by rfl⟩ : syracuseStep 1041817 = 781363) B781363
theorem B550315 : Blo 546805 550315 := bstep (se 1 (by rfl) ⟨412736, by rfl⟩ : syracuseStep 550315 = 825473) B825473
theorem B550327 : Blo 546805 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B615883 : Blo 546805 615883 := bstep (se 1 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 615883 = 923825) B923825
theorem B1566155 : Blo 546805 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B550347 : Blo 546805 550347 := bstep (se 1 (by rfl) ⟨412760, by rfl⟩ : syracuseStep 550347 = 825521) B825521
theorem B550359 : Blo 546805 550359 := bstep (se 1 (by rfl) ⟨412769, by rfl⟩ : syracuseStep 550359 = 825539) B825539
theorem B1238489 : Blo 546805 1238489 := bstep (se 2 (by rfl) ⟨464433, by rfl⟩ : syracuseStep 1238489 = 928867) B928867
theorem B550379 : Blo 546805 550379 := bstep (se 1 (by rfl) ⟨412784, by rfl⟩ : syracuseStep 550379 = 825569) B825569
theorem B550391 : Blo 546805 550391 := bstep (se 1 (by rfl) ⟨412793, by rfl⟩ : syracuseStep 550391 = 825587) B825587
theorem B550411 : Blo 546805 550411 := bstep (se 1 (by rfl) ⟨412808, by rfl⟩ : syracuseStep 550411 = 825617) B825617
theorem B550423 : Blo 546805 550423 := bstep (se 1 (by rfl) ⟨412817, by rfl⟩ : syracuseStep 550423 = 825635) B825635
theorem B550443 : Blo 546805 550443 := bstep (se 1 (by rfl) ⟨412832, by rfl⟩ : syracuseStep 550443 = 825665) B825665
theorem B1238579 : Blo 546805 1238579 := bstep (se 1 (by rfl) ⟨928934, by rfl⟩ : syracuseStep 1238579 = 1857869) B1857869
theorem B615991 : Blo 546805 615991 := bstep (se 1 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 615991 = 923987) B923987
theorem B550455 : Blo 546805 550455 := bstep (se 1 (by rfl) ⟨412841, by rfl⟩ : syracuseStep 550455 = 825683) B825683
theorem B550475 : Blo 546805 550475 := bstep (se 1 (by rfl) ⟨412856, by rfl⟩ : syracuseStep 550475 = 825713) B825713
theorem B550487 : Blo 546805 550487 := bstep (se 1 (by rfl) ⟨412865, by rfl⟩ : syracuseStep 550487 = 825731) B825731
theorem B1238615 : Blo 546805 1238615 := bstep (se 1 (by rfl) ⟨928961, by rfl⟩ : syracuseStep 1238615 = 1857923) B1857923
theorem B550507 : Blo 546805 550507 := bstep (se 1 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 550507 = 825761) B825761
theorem B550519 : Blo 546805 550519 := bstep (se 1 (by rfl) ⟨412889, by rfl⟩ : syracuseStep 550519 = 825779) B825779
theorem B550539 : Blo 546805 550539 := bstep (se 1 (by rfl) ⟨412904, by rfl⟩ : syracuseStep 550539 = 825809) B825809
theorem B550551 : Blo 546805 550551 := bstep (se 1 (by rfl) ⟨412913, by rfl⟩ : syracuseStep 550551 = 825827) B825827
theorem B550571 : Blo 546805 550571 := bstep (se 1 (by rfl) ⟨412928, by rfl⟩ : syracuseStep 550571 = 825857) B825857
theorem B550583 : Blo 546805 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B550603 : Blo 546805 550603 := bstep (se 1 (by rfl) ⟨412952, by rfl⟩ : syracuseStep 550603 = 825905) B825905
theorem B550615 : Blo 546805 550615 := bstep (se 1 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 550615 = 825923) B825923
theorem B1664729 : Blo 546805 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B616171 : Blo 546805 616171 := bstep (se 1 (by rfl) ⟨462128, by rfl⟩ : syracuseStep 616171 = 924257) B924257
theorem B550635 : Blo 546805 550635 := bstep (se 1 (by rfl) ⟨412976, by rfl⟩ : syracuseStep 550635 = 825953) B825953
theorem B550647 : Blo 546805 550647 := bstep (se 1 (by rfl) ⟨412985, by rfl⟩ : syracuseStep 550647 = 825971) B825971
theorem B1238795 : Blo 546805 1238795 := bstep (se 1 (by rfl) ⟨929096, by rfl⟩ : syracuseStep 1238795 = 1858193) B1858193
theorem B550667 : Blo 546805 550667 := bstep (se 1 (by rfl) ⟨413000, by rfl⟩ : syracuseStep 550667 = 826001) B826001
theorem B550679 : Blo 546805 550679 := bstep (se 1 (by rfl) ⟨413009, by rfl⟩ : syracuseStep 550679 = 826019) B826019
theorem B550699 : Blo 546805 550699 := bstep (se 1 (by rfl) ⟨413024, by rfl⟩ : syracuseStep 550699 = 826049) B826049
theorem B550711 : Blo 546805 550711 := bstep (se 1 (by rfl) ⟨413033, by rfl⟩ : syracuseStep 550711 = 826067) B826067
theorem B1238849 : Blo 546805 1238849 := bstep (se 2 (by rfl) ⟨464568, by rfl⟩ : syracuseStep 1238849 = 929137) B929137
theorem B550731 : Blo 546805 550731 := bstep (se 1 (by rfl) ⟨413048, by rfl⟩ : syracuseStep 550731 = 826097) B826097
theorem B616279 : Blo 546805 616279 := bstep (se 1 (by rfl) ⟨462209, by rfl⟩ : syracuseStep 616279 = 924419) B924419
theorem B550743 : Blo 546805 550743 := bstep (se 1 (by rfl) ⟨413057, by rfl⟩ : syracuseStep 550743 = 826115) B826115
theorem B780121 : Blo 546805 780121 := bstep (se 2 (by rfl) ⟨292545, by rfl⟩ : syracuseStep 780121 = 585091) B585091
theorem B1566553 : Blo 546805 1566553 := bstep (se 2 (by rfl) ⟨587457, by rfl⟩ : syracuseStep 1566553 = 1174915) B1174915
theorem B550763 : Blo 546805 550763 := bstep (se 1 (by rfl) ⟨413072, by rfl⟩ : syracuseStep 550763 = 826145) B826145
theorem B550775 : Blo 546805 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B550795 : Blo 546805 550795 := bstep (se 1 (by rfl) ⟨413096, by rfl⟩ : syracuseStep 550795 = 826193) B826193
theorem B1042379 : Blo 546805 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B616459 : Blo 546805 616459 := bstep (se 1 (by rfl) ⟨462344, by rfl⟩ : syracuseStep 616459 = 924689) B924689
theorem B1239065 : Blo 546805 1239065 := bstep (se 2 (by rfl) ⟨464649, by rfl⟩ : syracuseStep 1239065 = 929299) B929299
theorem B1239155 : Blo 546805 1239155 := bstep (se 1 (by rfl) ⟨929366, by rfl⟩ : syracuseStep 1239155 = 1858733) B1858733
theorem B616567 : Blo 546805 616567 := bstep (se 1 (by rfl) ⟨462425, by rfl⟩ : syracuseStep 616567 = 924851) B924851
theorem B1042561 : Blo 546805 1042561 := bstep (se 2 (by rfl) ⟨390960, by rfl⟩ : syracuseStep 1042561 = 781921) B781921
theorem B1239191 : Blo 546805 1239191 := bstep (se 1 (by rfl) ⟨929393, by rfl⟩ : syracuseStep 1239191 = 1858787) B1858787
theorem B616747 : Blo 546805 616747 := bstep (se 1 (by rfl) ⟨462560, by rfl⟩ : syracuseStep 616747 = 925121) B925121
theorem B616855 : Blo 546805 616855 := bstep (se 1 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 616855 = 925283) B925283
theorem B1174027 : Blo 546805 1174027 := bstep (se 1 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 1174027 = 1761041) B1761041
theorem B617035 : Blo 546805 617035 := bstep (se 1 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 617035 = 925553) B925553
theorem B617143 : Blo 546805 617143 := bstep (se 1 (by rfl) ⟨462857, by rfl⟩ : syracuseStep 617143 = 925715) B925715
theorem B3959513 : Blo 546805 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B1043275 : Blo 546805 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B617323 : Blo 546805 617323 := bstep (se 1 (by rfl) ⟨462992, by rfl⟩ : syracuseStep 617323 = 925985) B925985
theorem B4746115 : Blo 546805 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B584587 : Blo 546805 584587 := bstep (se 1 (by rfl) ⟨438440, by rfl⟩ : syracuseStep 584587 = 876881) B876881
theorem B1665943 : Blo 546805 1665943 := bstep (se 1 (by rfl) ⟨1249457, by rfl⟩ : syracuseStep 1665943 = 2498915) B2498915
theorem B1043351 : Blo 546805 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B617431 : Blo 546805 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B1567795 : Blo 546805 1567795 := bstep (se 1 (by rfl) ⟨1175846, by rfl⟩ : syracuseStep 1567795 = 2351693) B2351693
theorem B617611 : Blo 546805 617611 := bstep (se 1 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 617611 = 926417) B926417
theorem B205090019 : Blo 546805 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B617719 : Blo 546805 617719 := bstep (se 1 (by rfl) ⟨463289, by rfl⟩ : syracuseStep 617719 = 926579) B926579
theorem B781579 : Blo 546805 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B781591 : Blo 546805 781591 := bstep (se 1 (by rfl) ⟨586193, by rfl⟩ : syracuseStep 781591 = 1172387) B1172387
theorem B2780567 : Blo 546805 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B617899 : Blo 546805 617899 := bstep (se 1 (by rfl) ⟨463424, by rfl⟩ : syracuseStep 617899 = 926849) B926849
theorem B618007 : Blo 546805 618007 := bstep (se 1 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 618007 = 927011) B927011
theorem B1044019 : Blo 546805 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B618187 : Blo 546805 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B585463 : Blo 546805 585463 := bstep (se 1 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 585463 = 878195) B878195
theorem B1044247 : Blo 546805 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B618295 : Blo 546805 618295 := bstep (se 1 (by rfl) ⟨463721, by rfl⟩ : syracuseStep 618295 = 927443) B927443
theorem B4681547 : Blo 546805 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B4222813 : Blo 546805 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B1175411 : Blo 546805 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B1044353 : Blo 546805 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B618475 : Blo 546805 618475 := bstep (se 1 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 618475 = 927713) B927713
theorem B1044505 : Blo 546805 1044505 := bstep (se 2 (by rfl) ⟨391689, by rfl⟩ : syracuseStep 1044505 = 783379) B783379
theorem B618583 : Blo 546805 618583 := bstep (se 1 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 618583 = 927875) B927875
theorem B8876213 : Blo 546805 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B585911 : Blo 546805 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B618763 : Blo 546805 618763 := bstep (se 1 (by rfl) ⟨464072, by rfl⟩ : syracuseStep 618763 = 928145) B928145
theorem B618871 : Blo 546805 618871 := bstep (se 1 (by rfl) ⟨464153, by rfl⟩ : syracuseStep 618871 = 928307) B928307
theorem B4452869 : Blo 546805 4452869 := bstep (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) B834913
theorem B586283 : Blo 546805 586283 := bstep (se 1 (by rfl) ⟨439712, by rfl⟩ : syracuseStep 586283 = 879425) B879425
theorem B619051 : Blo 546805 619051 := bstep (se 1 (by rfl) ⟨464288, by rfl⟩ : syracuseStep 619051 = 928577) B928577
theorem B619159 : Blo 546805 619159 := bstep (se 1 (by rfl) ⟨464369, by rfl⟩ : syracuseStep 619159 = 928739) B928739
theorem B1176257 : Blo 546805 1176257 := bstep (se 2 (by rfl) ⟨441096, by rfl⟩ : syracuseStep 1176257 = 882193) B882193
theorem B619339 : Blo 546805 619339 := bstep (se 1 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 619339 = 929009) B929009
theorem B3339139 : Blo 546805 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B619447 : Blo 546805 619447 := bstep (se 1 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 619447 = 929171) B929171
theorem B619627 : Blo 546805 619627 := bstep (se 1 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 619627 = 929441) B929441
theorem B3339481 : Blo 546805 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B783641 : Blo 546805 783641 := bstep (se 2 (by rfl) ⟨293865, by rfl⟩ : syracuseStep 783641 = 587731) B587731
theorem B587287 : Blo 546805 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B7010225 : Blo 546805 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B2258867 : Blo 546805 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B555031 : Blo 546805 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B588107 : Blo 546805 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B1407449 : Blo 546805 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B3963437 : Blo 546805 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B5569175 : Blo 546805 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B2784131 : Blo 546805 2784131 := bstep (se 1 (by rfl) ⟨2088098, by rfl⟩ : syracuseStep 2784131 = 4176197) B4176197
theorem B3505625 : Blo 546805 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B7044569 : Blo 546805 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B5078533 : Blo 546805 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B753241 : Blo 546805 753241 := bstep (se 2 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 753241 = 564931) B564931
theorem B3342181 : Blo 546805 3342181 := bstep (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) B626659
theorem B4226993 : Blo 546805 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B3342397 : Blo 546805 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B1507643 : Blo 546805 1507643 := bstep (se 1 (by rfl) ⟨1130732, by rfl⟩ : syracuseStep 1507643 = 2261465) B2261465
theorem B820283 : Blo 546805 820283 := bstep (se 1 (by rfl) ⟨615212, by rfl⟩ : syracuseStep 820283 = 1230425) B1230425
theorem B820343 : Blo 546805 820343 := bstep (se 1 (by rfl) ⟨615257, by rfl⟩ : syracuseStep 820343 = 1230515) B1230515
theorem B820367 : Blo 546805 820367 := bstep (se 1 (by rfl) ⟨615275, by rfl⟩ : syracuseStep 820367 = 1230551) B1230551
theorem B820409 : Blo 546805 820409 := bstep (se 2 (by rfl) ⟨307653, by rfl⟩ : syracuseStep 820409 = 615307) B615307
theorem B2786561 : Blo 546805 2786561 := bstep (se 2 (by rfl) ⟨1044960, by rfl⟩ : syracuseStep 2786561 = 2089921) B2089921
theorem B820487 : Blo 546805 820487 := bstep (se 1 (by rfl) ⟨615365, by rfl⟩ : syracuseStep 820487 = 1230731) B1230731
theorem B1082657 : Blo 546805 1082657 := bstep (se 2 (by rfl) ⟨405996, by rfl⟩ : syracuseStep 1082657 = 811993) B811993
theorem B820523 : Blo 546805 820523 := bstep (se 1 (by rfl) ⟨615392, by rfl⟩ : syracuseStep 820523 = 1230785) B1230785
theorem B820553 : Blo 546805 820553 := bstep (se 2 (by rfl) ⟨307707, by rfl⟩ : syracuseStep 820553 = 615415) B615415
theorem B820667 : Blo 546805 820667 := bstep (se 1 (by rfl) ⟨615500, by rfl⟩ : syracuseStep 820667 = 1231001) B1231001
theorem B3114449 : Blo 546805 3114449 := bstep (se 2 (by rfl) ⟨1167918, by rfl⟩ : syracuseStep 3114449 = 2335837) B2335837
theorem B820727 : Blo 546805 820727 := bstep (se 1 (by rfl) ⟨615545, by rfl⟩ : syracuseStep 820727 = 1231091) B1231091
theorem B4163075 : Blo 546805 4163075 := bstep (se 1 (by rfl) ⟨3122306, by rfl⟩ : syracuseStep 4163075 = 6244613) B6244613
theorem B820751 : Blo 546805 820751 := bstep (se 1 (by rfl) ⟨615563, by rfl⟩ : syracuseStep 820751 = 1231127) B1231127
theorem B820793 : Blo 546805 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B36537925 : Blo 546805 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B820871 : Blo 546805 820871 := bstep (se 1 (by rfl) ⟨615653, by rfl⟩ : syracuseStep 820871 = 1231307) B1231307
theorem B820907 : Blo 546805 820907 := bstep (se 1 (by rfl) ⟨615680, by rfl⟩ : syracuseStep 820907 = 1231361) B1231361
theorem B820937 : Blo 546805 820937 := bstep (se 2 (by rfl) ⟨307851, by rfl⟩ : syracuseStep 820937 = 615703) B615703
theorem B4687631 : Blo 546805 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B821051 : Blo 546805 821051 := bstep (se 1 (by rfl) ⟨615788, by rfl⟩ : syracuseStep 821051 = 1231577) B1231577
theorem B821111 : Blo 546805 821111 := bstep (se 1 (by rfl) ⟨615833, by rfl⟩ : syracuseStep 821111 = 1231667) B1231667
theorem B821135 : Blo 546805 821135 := bstep (se 1 (by rfl) ⟨615851, by rfl⟩ : syracuseStep 821135 = 1231703) B1231703
theorem B821177 : Blo 546805 821177 := bstep (se 2 (by rfl) ⟨307941, by rfl⟩ : syracuseStep 821177 = 615883) B615883
theorem B821255 : Blo 546805 821255 := bstep (se 1 (by rfl) ⟨615941, by rfl⟩ : syracuseStep 821255 = 1231883) B1231883
theorem B821291 : Blo 546805 821291 := bstep (se 1 (by rfl) ⟨615968, by rfl⟩ : syracuseStep 821291 = 1231937) B1231937
theorem B2787371 : Blo 546805 2787371 := bstep (se 1 (by rfl) ⟨2090528, by rfl⟩ : syracuseStep 2787371 = 4181057) B4181057
theorem B821321 : Blo 546805 821321 := bstep (se 2 (by rfl) ⟨307995, by rfl⟩ : syracuseStep 821321 = 615991) B615991
theorem B821435 : Blo 546805 821435 := bstep (se 1 (by rfl) ⟨616076, by rfl⟩ : syracuseStep 821435 = 1232153) B1232153
theorem B821495 : Blo 546805 821495 := bstep (se 1 (by rfl) ⟨616121, by rfl⟩ : syracuseStep 821495 = 1232243) B1232243
theorem B821519 : Blo 546805 821519 := bstep (se 1 (by rfl) ⟨616139, by rfl⟩ : syracuseStep 821519 = 1232279) B1232279
theorem B821561 : Blo 546805 821561 := bstep (se 2 (by rfl) ⟨308085, by rfl⟩ : syracuseStep 821561 = 616171) B616171
theorem B821639 : Blo 546805 821639 := bstep (se 1 (by rfl) ⟨616229, by rfl⟩ : syracuseStep 821639 = 1232459) B1232459
theorem B821675 : Blo 546805 821675 := bstep (se 1 (by rfl) ⟨616256, by rfl⟩ : syracuseStep 821675 = 1232513) B1232513
theorem B821705 : Blo 546805 821705 := bstep (se 2 (by rfl) ⟨308139, by rfl⟩ : syracuseStep 821705 = 616279) B616279
theorem B821819 : Blo 546805 821819 := bstep (se 1 (by rfl) ⟨616364, by rfl⟩ : syracuseStep 821819 = 1232729) B1232729
theorem B821879 : Blo 546805 821879 := bstep (se 1 (by rfl) ⟨616409, by rfl⟩ : syracuseStep 821879 = 1232819) B1232819
theorem B821903 : Blo 546805 821903 := bstep (se 1 (by rfl) ⟨616427, by rfl⟩ : syracuseStep 821903 = 1232855) B1232855
theorem B821945 : Blo 546805 821945 := bstep (se 2 (by rfl) ⟨308229, by rfl⟩ : syracuseStep 821945 = 616459) B616459
theorem B822023 : Blo 546805 822023 := bstep (se 1 (by rfl) ⟨616517, by rfl⟩ : syracuseStep 822023 = 1233035) B1233035
theorem B822059 : Blo 546805 822059 := bstep (se 1 (by rfl) ⟨616544, by rfl⟩ : syracuseStep 822059 = 1233089) B1233089
theorem B822089 : Blo 546805 822089 := bstep (se 2 (by rfl) ⟨308283, by rfl⟩ : syracuseStep 822089 = 616567) B616567
theorem B3345299 : Blo 546805 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B822203 : Blo 546805 822203 := bstep (se 1 (by rfl) ⟨616652, by rfl⟩ : syracuseStep 822203 = 1233305) B1233305
theorem B822263 : Blo 546805 822263 := bstep (se 1 (by rfl) ⟨616697, by rfl⟩ : syracuseStep 822263 = 1233395) B1233395
theorem B822287 : Blo 546805 822287 := bstep (se 1 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 822287 = 1233431) B1233431
theorem B822329 : Blo 546805 822329 := bstep (se 2 (by rfl) ⟨308373, by rfl⟩ : syracuseStep 822329 = 616747) B616747
theorem B822407 : Blo 546805 822407 := bstep (se 1 (by rfl) ⟨616805, by rfl⟩ : syracuseStep 822407 = 1233611) B1233611
theorem B822443 : Blo 546805 822443 := bstep (se 1 (by rfl) ⟨616832, by rfl⟩ : syracuseStep 822443 = 1233665) B1233665
theorem B822473 : Blo 546805 822473 := bstep (se 2 (by rfl) ⟨308427, by rfl⟩ : syracuseStep 822473 = 616855) B616855
theorem B1314091 : Blo 546805 1314091 := bstep (se 1 (by rfl) ⟨985568, by rfl⟩ : syracuseStep 1314091 = 1971137) B1971137
theorem B3116339 : Blo 546805 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B822587 : Blo 546805 822587 := bstep (se 1 (by rfl) ⟨616940, by rfl⟩ : syracuseStep 822587 = 1233881) B1233881
theorem B6262109 : Blo 546805 6262109 := bstep (se 3 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 6262109 = 2348291) B2348291
theorem B822647 : Blo 546805 822647 := bstep (se 1 (by rfl) ⟨616985, by rfl⟩ : syracuseStep 822647 = 1233971) B1233971
theorem B822671 : Blo 546805 822671 := bstep (se 1 (by rfl) ⟨617003, by rfl⟩ : syracuseStep 822671 = 1234007) B1234007
theorem B822713 : Blo 546805 822713 := bstep (se 2 (by rfl) ⟨308517, by rfl⟩ : syracuseStep 822713 = 617035) B617035
theorem B3509725 : Blo 546805 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B822791 : Blo 546805 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B1478159 : Blo 546805 1478159 := bstep (se 1 (by rfl) ⟨1108619, by rfl⟩ : syracuseStep 1478159 = 2217239) B2217239
theorem B822827 : Blo 546805 822827 := bstep (se 1 (by rfl) ⟨617120, by rfl⟩ : syracuseStep 822827 = 1234241) B1234241
theorem B822857 : Blo 546805 822857 := bstep (se 2 (by rfl) ⟨308571, by rfl⟩ : syracuseStep 822857 = 617143) B617143
theorem B986759 : Blo 546805 986759 := bstep (se 1 (by rfl) ⟨740069, by rfl⟩ : syracuseStep 986759 = 1480139) B1480139
theorem B822971 : Blo 546805 822971 := bstep (se 1 (by rfl) ⟨617228, by rfl⟩ : syracuseStep 822971 = 1234457) B1234457
theorem B823031 : Blo 546805 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B823055 : Blo 546805 823055 := bstep (se 1 (by rfl) ⟨617291, by rfl⟩ : syracuseStep 823055 = 1234583) B1234583
theorem B823097 : Blo 546805 823097 := bstep (se 2 (by rfl) ⟨308661, by rfl⟩ : syracuseStep 823097 = 617323) B617323
theorem B6328153 : Blo 546805 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B823175 : Blo 546805 823175 := bstep (se 1 (by rfl) ⟨617381, by rfl⟩ : syracuseStep 823175 = 1234763) B1234763
theorem B823211 : Blo 546805 823211 := bstep (se 1 (by rfl) ⟨617408, by rfl⟩ : syracuseStep 823211 = 1234817) B1234817
theorem B692155 : Blo 546805 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B823241 : Blo 546805 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B987169 : Blo 546805 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B823355 : Blo 546805 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B823415 : Blo 546805 823415 := bstep (se 1 (by rfl) ⟨617561, by rfl⟩ : syracuseStep 823415 = 1235123) B1235123
theorem B823439 : Blo 546805 823439 := bstep (se 1 (by rfl) ⟨617579, by rfl⟩ : syracuseStep 823439 = 1235159) B1235159
theorem B823481 : Blo 546805 823481 := bstep (se 2 (by rfl) ⟨308805, by rfl⟩ : syracuseStep 823481 = 617611) B617611
theorem B823559 : Blo 546805 823559 := bstep (se 1 (by rfl) ⟨617669, by rfl⟩ : syracuseStep 823559 = 1235339) B1235339
theorem B823595 : Blo 546805 823595 := bstep (se 1 (by rfl) ⟨617696, by rfl⟩ : syracuseStep 823595 = 1235393) B1235393
theorem B823625 : Blo 546805 823625 := bstep (se 2 (by rfl) ⟨308859, by rfl⟩ : syracuseStep 823625 = 617719) B617719
theorem B1315187 : Blo 546805 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B692651 : Blo 546805 692651 := bstep (se 1 (by rfl) ⟨519488, by rfl⟩ : syracuseStep 692651 = 1038977) B1038977
theorem B823739 : Blo 546805 823739 := bstep (se 1 (by rfl) ⟨617804, by rfl⟩ : syracuseStep 823739 = 1235609) B1235609
theorem B823799 : Blo 546805 823799 := bstep (se 1 (by rfl) ⟨617849, by rfl⟩ : syracuseStep 823799 = 1235699) B1235699
theorem B823823 : Blo 546805 823823 := bstep (se 1 (by rfl) ⟨617867, by rfl⟩ : syracuseStep 823823 = 1235735) B1235735
theorem B823865 : Blo 546805 823865 := bstep (se 2 (by rfl) ⟨308949, by rfl⟩ : syracuseStep 823865 = 617899) B617899
theorem B823943 : Blo 546805 823943 := bstep (se 1 (by rfl) ⟨617957, by rfl⟩ : syracuseStep 823943 = 1235915) B1235915
theorem B823979 : Blo 546805 823979 := bstep (se 1 (by rfl) ⟨617984, by rfl⟩ : syracuseStep 823979 = 1235969) B1235969
theorem B824009 : Blo 546805 824009 := bstep (se 2 (by rfl) ⟨309003, by rfl⟩ : syracuseStep 824009 = 618007) B618007
theorem B3117797 : Blo 546805 3117797 := bstep (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) B584587
theorem B6263567 : Blo 546805 6263567 := bstep (se 1 (by rfl) ⟨4697675, by rfl⟩ : syracuseStep 6263567 = 9395351) B9395351
theorem B824123 : Blo 546805 824123 := bstep (se 1 (by rfl) ⟨618092, by rfl⟩ : syracuseStep 824123 = 1236185) B1236185
theorem B824183 : Blo 546805 824183 := bstep (se 1 (by rfl) ⟨618137, by rfl⟩ : syracuseStep 824183 = 1236275) B1236275
theorem B693127 : Blo 546805 693127 := bstep (se 1 (by rfl) ⟨519845, by rfl⟩ : syracuseStep 693127 = 1039691) B1039691
theorem B824207 : Blo 546805 824207 := bstep (se 1 (by rfl) ⟨618155, by rfl⟩ : syracuseStep 824207 = 1236311) B1236311
theorem B824249 : Blo 546805 824249 := bstep (se 2 (by rfl) ⟨309093, by rfl⟩ : syracuseStep 824249 = 618187) B618187
theorem B824327 : Blo 546805 824327 := bstep (se 1 (by rfl) ⟨618245, by rfl⟩ : syracuseStep 824327 = 1236491) B1236491
theorem B1053739 : Blo 546805 1053739 := bstep (se 1 (by rfl) ⟨790304, by rfl⟩ : syracuseStep 1053739 = 1580609) B1580609
theorem B824363 : Blo 546805 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B824393 : Blo 546805 824393 := bstep (se 2 (by rfl) ⟨309147, by rfl⟩ : syracuseStep 824393 = 618295) B618295
theorem B824507 : Blo 546805 824507 := bstep (se 1 (by rfl) ⟨618380, by rfl⟩ : syracuseStep 824507 = 1236761) B1236761
theorem B824567 : Blo 546805 824567 := bstep (se 1 (by rfl) ⟨618425, by rfl⟩ : syracuseStep 824567 = 1236851) B1236851
theorem B824591 : Blo 546805 824591 := bstep (se 1 (by rfl) ⟨618443, by rfl⟩ : syracuseStep 824591 = 1236887) B1236887
theorem B824633 : Blo 546805 824633 := bstep (se 2 (by rfl) ⟨309237, by rfl⟩ : syracuseStep 824633 = 618475) B618475
theorem B693623 : Blo 546805 693623 := bstep (se 1 (by rfl) ⟨520217, by rfl⟩ : syracuseStep 693623 = 1040435) B1040435
theorem B923015 : Blo 546805 923015 := bstep (se 1 (by rfl) ⟨692261, by rfl⟩ : syracuseStep 923015 = 1384523) B1384523
theorem B824711 : Blo 546805 824711 := bstep (se 1 (by rfl) ⟨618533, by rfl⟩ : syracuseStep 824711 = 1237067) B1237067
theorem B824747 : Blo 546805 824747 := bstep (se 1 (by rfl) ⟨618560, by rfl⟩ : syracuseStep 824747 = 1237121) B1237121
theorem B824777 : Blo 546805 824777 := bstep (se 2 (by rfl) ⟨309291, by rfl⟩ : syracuseStep 824777 = 618583) B618583
theorem B693775 : Blo 546805 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B824891 : Blo 546805 824891 := bstep (se 1 (by rfl) ⟨618668, by rfl⟩ : syracuseStep 824891 = 1237337) B1237337
theorem B824951 : Blo 546805 824951 := bstep (se 1 (by rfl) ⟨618713, by rfl⟩ : syracuseStep 824951 = 1237427) B1237427
theorem B824975 : Blo 546805 824975 := bstep (se 1 (by rfl) ⟨618731, by rfl⟩ : syracuseStep 824975 = 1237463) B1237463
theorem B8918707 : Blo 546805 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B825017 : Blo 546805 825017 := bstep (se 2 (by rfl) ⟨309381, by rfl⟩ : syracuseStep 825017 = 618763) B618763
theorem B693947 : Blo 546805 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B825095 : Blo 546805 825095 := bstep (se 1 (by rfl) ⟨618821, by rfl⟩ : syracuseStep 825095 = 1237643) B1237643
theorem B825131 : Blo 546805 825131 := bstep (se 1 (by rfl) ⟨618848, by rfl⟩ : syracuseStep 825131 = 1237697) B1237697
theorem B825161 : Blo 546805 825161 := bstep (se 2 (by rfl) ⟨309435, by rfl⟩ : syracuseStep 825161 = 618871) B618871
theorem B825275 : Blo 546805 825275 := bstep (se 1 (by rfl) ⟨618956, by rfl⟩ : syracuseStep 825275 = 1237913) B1237913
theorem B989129 : Blo 546805 989129 := bstep (se 2 (by rfl) ⟨370923, by rfl⟩ : syracuseStep 989129 = 741847) B741847
theorem B10000331 : Blo 546805 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B825335 : Blo 546805 825335 := bstep (se 1 (by rfl) ⟨619001, by rfl⟩ : syracuseStep 825335 = 1238003) B1238003
theorem B923663 : Blo 546805 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B825359 : Blo 546805 825359 := bstep (se 1 (by rfl) ⟨619019, by rfl⟩ : syracuseStep 825359 = 1238039) B1238039
theorem B825401 : Blo 546805 825401 := bstep (se 2 (by rfl) ⟨309525, by rfl⟩ : syracuseStep 825401 = 619051) B619051
theorem B825479 : Blo 546805 825479 := bstep (se 1 (by rfl) ⟨619109, by rfl⟩ : syracuseStep 825479 = 1238219) B1238219
theorem B825515 : Blo 546805 825515 := bstep (se 1 (by rfl) ⟨619136, by rfl⟩ : syracuseStep 825515 = 1238273) B1238273
theorem B1185977 : Blo 546805 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B825545 : Blo 546805 825545 := bstep (se 2 (by rfl) ⟨309579, by rfl⟩ : syracuseStep 825545 = 619159) B619159
theorem B825659 : Blo 546805 825659 := bstep (se 1 (by rfl) ⟨619244, by rfl⟩ : syracuseStep 825659 = 1238489) B1238489
theorem B825719 : Blo 546805 825719 := bstep (se 1 (by rfl) ⟨619289, by rfl⟩ : syracuseStep 825719 = 1238579) B1238579
theorem B825743 : Blo 546805 825743 := bstep (se 1 (by rfl) ⟨619307, by rfl⟩ : syracuseStep 825743 = 1238615) B1238615
theorem B825785 : Blo 546805 825785 := bstep (se 2 (by rfl) ⟨309669, by rfl⟩ : syracuseStep 825785 = 619339) B619339
theorem B825863 : Blo 546805 825863 := bstep (se 1 (by rfl) ⟨619397, by rfl⟩ : syracuseStep 825863 = 1238795) B1238795
theorem B924203 : Blo 546805 924203 := bstep (se 1 (by rfl) ⟨693152, by rfl⟩ : syracuseStep 924203 = 1386305) B1386305
theorem B7936555 : Blo 546805 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B825899 : Blo 546805 825899 := bstep (se 1 (by rfl) ⟨619424, by rfl⟩ : syracuseStep 825899 = 1238849) B1238849
theorem B825929 : Blo 546805 825929 := bstep (se 2 (by rfl) ⟨309723, by rfl⟩ : syracuseStep 825929 = 619447) B619447
theorem B989815 : Blo 546805 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B694919 : Blo 546805 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B826043 : Blo 546805 826043 := bstep (se 1 (by rfl) ⟨619532, by rfl⟩ : syracuseStep 826043 = 1239065) B1239065
theorem B4168421 : Blo 546805 4168421 := bstep (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) B781579
theorem B826103 : Blo 546805 826103 := bstep (se 1 (by rfl) ⟨619577, by rfl⟩ : syracuseStep 826103 = 1239155) B1239155
theorem B1317647 : Blo 546805 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B826127 : Blo 546805 826127 := bstep (se 1 (by rfl) ⟨619595, by rfl⟩ : syracuseStep 826127 = 1239191) B1239191
theorem B826169 : Blo 546805 826169 := bstep (se 2 (by rfl) ⟨309813, by rfl⟩ : syracuseStep 826169 = 619627) B619627
theorem B1711001 : Blo 546805 1711001 := bstep (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) B1283251
theorem B924601 : Blo 546805 924601 := bstep (se 2 (by rfl) ⟨346725, by rfl⟩ : syracuseStep 924601 = 693451) B693451
theorem B14851133 : Blo 546805 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B695567 : Blo 546805 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B925303 : Blo 546805 925303 := bstep (se 1 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 925303 = 1387955) B1387955
theorem B925499 : Blo 546805 925499 := bstep (se 1 (by rfl) ⟨694124, by rfl⟩ : syracuseStep 925499 = 1388249) B1388249
theorem B3121031 : Blo 546805 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B3121213 : Blo 546805 3121213 := bstep (se 3 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 3121213 = 1170455) B1170455
theorem B2367575 : Blo 546805 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B925897 : Blo 546805 925897 := bstep (se 2 (by rfl) ⟨347211, by rfl⟩ : syracuseStep 925897 = 694423) B694423
theorem B794887 : Blo 546805 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1384715 : Blo 546805 1384715 := bstep (se 1 (by rfl) ⟨1038536, by rfl⟩ : syracuseStep 1384715 = 2077073) B2077073
theorem B1974827 : Blo 546805 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B1254203 : Blo 546805 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B926599 : Blo 546805 926599 := bstep (se 1 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 926599 = 1389899) B1389899
theorem B1385363 : Blo 546805 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B1451009 : Blo 546805 1451009 := bstep (se 2 (by rfl) ⟨544128, by rfl⟩ : syracuseStep 1451009 = 1088257) B1088257
theorem B7611479 : Blo 546805 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1385657 : Blo 546805 1385657 := bstep (se 2 (by rfl) ⟨519621, by rfl⟩ : syracuseStep 1385657 = 1039243) B1039243
theorem B2630893 : Blo 546805 2630893 := bstep (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) B986585
theorem B927247 : Blo 546805 927247 := bstep (se 1 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 927247 = 1390871) B1390871
theorem B6235865 : Blo 546805 6235865 := bstep (se 2 (by rfl) ⟨2338449, by rfl⟩ : syracuseStep 6235865 = 4676899) B4676899
theorem B3122945 : Blo 546805 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B1386355 : Blo 546805 1386355 := bstep (se 1 (by rfl) ⟨1039766, by rfl⟩ : syracuseStep 1386355 = 2079533) B2079533
theorem B1386497 : Blo 546805 1386497 := bstep (se 2 (by rfl) ⟨519936, by rfl⟩ : syracuseStep 1386497 = 1039873) B1039873
theorem B927787 : Blo 546805 927787 := bstep (se 1 (by rfl) ⟨695840, by rfl⟩ : syracuseStep 927787 = 1391681) B1391681
theorem B927929 : Blo 546805 927929 := bstep (se 2 (by rfl) ⟨347973, by rfl⟩ : syracuseStep 927929 = 695947) B695947
theorem B3385637 : Blo 546805 3385637 := bstep (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) B634807
theorem B2337083 : Blo 546805 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B4696379 : Blo 546805 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B1386953 : Blo 546805 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B1976861 : Blo 546805 1976861 := bstep (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) B741323
theorem B2960165 : Blo 546805 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B1387307 : Blo 546805 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B928631 : Blo 546805 928631 := bstep (se 1 (by rfl) ⟨696473, by rfl⟩ : syracuseStep 928631 = 1392947) B1392947
theorem B1846151 : Blo 546805 1846151 := bstep (se 1 (by rfl) ⟨1384613, by rfl⟩ : syracuseStep 1846151 = 2769227) B2769227
theorem B1485857 : Blo 546805 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B2337835 : Blo 546805 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B5614679 : Blo 546805 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B1846529 : Blo 546805 1846529 := bstep (se 2 (by rfl) ⟨692448, by rfl⟩ : syracuseStep 1846529 = 1384897) B1384897
theorem B929083 : Blo 546805 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B1584569 : Blo 546805 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B929225 : Blo 546805 929225 := bstep (se 2 (by rfl) ⟨348459, by rfl⟩ : syracuseStep 929225 = 696919) B696919
theorem B2666027 : Blo 546805 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B1388299 : Blo 546805 1388299 := bstep (se 1 (by rfl) ⟨1041224, by rfl⟩ : syracuseStep 1388299 = 2082449) B2082449
theorem B5353253 : Blo 546805 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B1388441 : Blo 546805 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B1847339 : Blo 546805 1847339 := bstep (se 1 (by rfl) ⟨1385504, by rfl⟩ : syracuseStep 1847339 = 2771009) B2771009
theorem B1388603 : Blo 546805 1388603 := bstep (se 1 (by rfl) ⟨1041452, by rfl⟩ : syracuseStep 1388603 = 2082905) B2082905
theorem B1782131 : Blo 546805 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1388947 : Blo 546805 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B1389089 : Blo 546805 1389089 := bstep (se 2 (by rfl) ⟨520908, by rfl⟩ : syracuseStep 1389089 = 1041817) B1041817
theorem B2077271 : Blo 546805 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B6337201 : Blo 546805 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B4699043 : Blo 546805 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B4764619 : Blo 546805 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B2077757 : Blo 546805 2077757 := bstep (se 3 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 2077757 = 779159) B779159
theorem B1848635 : Blo 546805 1848635 := bstep (se 1 (by rfl) ⟨1386476, by rfl⟩ : syracuseStep 1848635 = 2772953) B2772953
theorem B6272315 : Blo 546805 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B1586519 : Blo 546805 1586519 := bstep (se 1 (by rfl) ⟨1189889, by rfl⟩ : syracuseStep 1586519 = 2379779) B2379779
theorem B2340211 : Blo 546805 2340211 := bstep (se 1 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 2340211 = 3510317) B3510317
theorem B6698371 : Blo 546805 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B2635217 : Blo 546805 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B1390081 : Blo 546805 1390081 := bstep (se 2 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 1390081 = 1042561) B1042561
theorem B5912281 : Blo 546805 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B2111233 : Blo 546805 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B1849121 : Blo 546805 1849121 := bstep (se 2 (by rfl) ⟨693420, by rfl⟩ : syracuseStep 1849121 = 1386841) B1386841
theorem B1488755 : Blo 546805 1488755 := bstep (se 1 (by rfl) ⟨1116566, by rfl⟩ : syracuseStep 1488755 = 2233133) B2233133
theorem B2111417 : Blo 546805 2111417 := bstep (se 2 (by rfl) ⟨791781, by rfl⟩ : syracuseStep 2111417 = 1583563) B1583563
theorem B3127319 : Blo 546805 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B1390679 : Blo 546805 1390679 := bstep (se 1 (by rfl) ⟨1043009, by rfl⟩ : syracuseStep 1390679 = 2086019) B2086019
theorem B2111777 : Blo 546805 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B1390891 : Blo 546805 1390891 := bstep (se 1 (by rfl) ⟨1043168, by rfl⟩ : syracuseStep 1390891 = 2086337) B2086337
theorem B1849715 : Blo 546805 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B1391033 : Blo 546805 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B2079503 : Blo 546805 2079503 := bstep (se 1 (by rfl) ⟨1559627, by rfl⟩ : syracuseStep 2079503 = 3119255) B3119255
theorem B2964275 : Blo 546805 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1751993 : Blo 546805 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B1752455 : Blo 546805 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B1392025 : Blo 546805 1392025 := bstep (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) B1044019
theorem B1392187 : Blo 546805 1392187 := bstep (se 1 (by rfl) ⟨1044140, by rfl⟩ : syracuseStep 1392187 = 2088281) B2088281
theorem B1392329 : Blo 546805 1392329 := bstep (se 2 (by rfl) ⟨522123, by rfl⟩ : syracuseStep 1392329 = 1044247) B1044247
theorem B1392673 : Blo 546805 1392673 := bstep (se 2 (by rfl) ⟨522252, by rfl⟩ : syracuseStep 1392673 = 1044505) B1044505
theorem B5915015 : Blo 546805 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B2081159 : Blo 546805 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B5259667 : Blo 546805 5259667 := bstep (se 1 (by rfl) ⟨3944750, by rfl⟩ : syracuseStep 5259667 = 7889501) B7889501
theorem B1982987 : Blo 546805 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B1393271 : Blo 546805 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B836281 : Blo 546805 836281 := bstep (se 2 (by rfl) ⟨313605, by rfl⟩ : syracuseStep 836281 = 627211) B627211
theorem B1557281 : Blo 546805 1557281 := bstep (se 2 (by rfl) ⟨583980, by rfl⟩ : syracuseStep 1557281 = 1167961) B1167961
theorem B1852307 : Blo 546805 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B1557623 : Blo 546805 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B3130487 : Blo 546805 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2770361 : Blo 546805 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B6670001 : Blo 546805 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B2639675 : Blo 546805 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B837449 : Blo 546805 837449 := bstep (se 2 (by rfl) ⟨314043, by rfl⟩ : syracuseStep 837449 = 628087) B628087
theorem B2082935 : Blo 546805 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B1230983 : Blo 546805 1230983 := bstep (se 1 (by rfl) ⟨923237, by rfl⟩ : syracuseStep 1230983 = 1846475) B1846475
theorem B136726679 : Blo 546805 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B1853711 : Blo 546805 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B3524897 : Blo 546805 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B3164453 : Blo 546805 3164453 := bstep (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) B593335
theorem B1231163 : Blo 546805 1231163 := bstep (se 1 (by rfl) ⟨923372, by rfl⟩ : syracuseStep 1231163 = 1846745) B1846745
theorem B1231289 : Blo 546805 1231289 := bstep (se 2 (by rfl) ⟨461733, by rfl⟩ : syracuseStep 1231289 = 923467) B923467
theorem B1853981 : Blo 546805 1853981 := bstep (se 3 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 1853981 = 695243) B695243
theorem B2771657 : Blo 546805 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B1231631 : Blo 546805 1231631 := bstep (se 1 (by rfl) ⟨923723, by rfl⟩ : syracuseStep 1231631 = 1847447) B1847447
theorem B1231649 : Blo 546805 1231649 := bstep (se 2 (by rfl) ⟨461868, by rfl⟩ : syracuseStep 1231649 = 923737) B923737
theorem B5917475 : Blo 546805 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B2968579 : Blo 546805 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B2083907 : Blo 546805 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B1231991 : Blo 546805 1231991 := bstep (se 1 (by rfl) ⟨923993, by rfl⟩ : syracuseStep 1231991 = 1847987) B1847987
theorem B35540117 : Blo 546805 35540117 := bstep (se 6 (by rfl) ⟨832971, by rfl⟩ : syracuseStep 35540117 = 1665943) B1665943
theorem B2346241 : Blo 546805 2346241 := bstep (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) B1759681
theorem B1232171 : Blo 546805 1232171 := bstep (se 1 (by rfl) ⟨924128, by rfl⟩ : syracuseStep 1232171 = 1848257) B1848257
theorem B2084363 : Blo 546805 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B1560151 : Blo 546805 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B2346583 : Blo 546805 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B8572517 : Blo 546805 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B1232531 : Blo 546805 1232531 := bstep (se 1 (by rfl) ⟨924398, by rfl⟩ : syracuseStep 1232531 = 1848797) B1848797
theorem B1232585 : Blo 546805 1232585 := bstep (se 2 (by rfl) ⟨462219, by rfl⟩ : syracuseStep 1232585 = 924439) B924439
theorem B1560379 : Blo 546805 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B1855385 : Blo 546805 1855385 := bstep (se 2 (by rfl) ⟨695769, by rfl⟩ : syracuseStep 1855385 = 1391539) B1391539
theorem B1560505 : Blo 546805 1560505 := bstep (se 2 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 1560505 = 1170379) B1170379
theorem B4673483 : Blo 546805 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B938299 : Blo 546805 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B2642291 : Blo 546805 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B1233287 : Blo 546805 1233287 := bstep (se 1 (by rfl) ⟨924965, by rfl⟩ : syracuseStep 1233287 = 1849931) B1849931
theorem B1233467 : Blo 546805 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B1856087 : Blo 546805 1856087 := bstep (se 1 (by rfl) ⟨1392065, by rfl⟩ : syracuseStep 1856087 = 2784131) B2784131
theorem B5263973 : Blo 546805 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B6771377 : Blo 546805 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B1233593 : Blo 546805 1233593 := bstep (se 2 (by rfl) ⟨462597, by rfl⟩ : syracuseStep 1233593 = 925195) B925195
theorem B3134153 : Blo 546805 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B1004321 : Blo 546805 1004321 := bstep (se 2 (by rfl) ⟨376620, by rfl⟩ : syracuseStep 1004321 = 753241) B753241
theorem B5919641 : Blo 546805 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B1233935 : Blo 546805 1233935 := bstep (se 1 (by rfl) ⟨925451, by rfl⟩ : syracuseStep 1233935 = 1850903) B1850903
theorem B1233953 : Blo 546805 1233953 := bstep (se 2 (by rfl) ⟨462732, by rfl⟩ : syracuseStep 1233953 = 925465) B925465
theorem B1856573 : Blo 546805 1856573 := bstep (se 3 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 1856573 = 696215) B696215
theorem B25416791 : Blo 546805 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B5363003 : Blo 546805 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B1234295 : Blo 546805 1234295 := bstep (se 1 (by rfl) ⟨925721, by rfl⟩ : syracuseStep 1234295 = 1851443) B1851443
theorem B1234475 : Blo 546805 1234475 := bstep (se 1 (by rfl) ⟨925856, by rfl⟩ : syracuseStep 1234475 = 1851713) B1851713
theorem B2086519 : Blo 546805 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B939721 : Blo 546805 939721 := bstep (se 2 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 939721 = 704791) B704791
theorem B1562429 : Blo 546805 1562429 := bstep (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) B585911
theorem B1234835 : Blo 546805 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B1234889 : Blo 546805 1234889 := bstep (se 2 (by rfl) ⟨463083, by rfl⟩ : syracuseStep 1234889 = 926167) B926167
theorem B546823 : Blo 546805 546823 := bstep (se 1 (by rfl) ⟨410117, by rfl⟩ : syracuseStep 546823 = 820235) B820235
theorem B546831 : Blo 546805 546831 := bstep (se 1 (by rfl) ⟨410123, by rfl⟩ : syracuseStep 546831 = 820247) B820247
theorem B546875 : Blo 546805 546875 := bstep (se 1 (by rfl) ⟨410156, by rfl⟩ : syracuseStep 546875 = 820313) B820313
theorem B546951 : Blo 546805 546951 := bstep (se 1 (by rfl) ⟨410213, by rfl⟩ : syracuseStep 546951 = 820427) B820427
theorem B546959 : Blo 546805 546959 := bstep (se 1 (by rfl) ⟨410219, by rfl⟩ : syracuseStep 546959 = 820439) B820439
theorem B1038521 : Blo 546805 1038521 := bstep (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) B778891
theorem B547003 : Blo 546805 547003 := bstep (se 1 (by rfl) ⟨410252, by rfl⟩ : syracuseStep 547003 = 820505) B820505
theorem B547079 : Blo 546805 547079 := bstep (se 1 (by rfl) ⟨410309, by rfl⟩ : syracuseStep 547079 = 820619) B820619
theorem B547087 : Blo 546805 547087 := bstep (se 1 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 547087 = 820631) B820631
theorem B4741409 : Blo 546805 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B547131 : Blo 546805 547131 := bstep (se 1 (by rfl) ⟨410348, by rfl⟩ : syracuseStep 547131 = 820697) B820697
theorem B547207 : Blo 546805 547207 := bstep (se 1 (by rfl) ⟨410405, by rfl⟩ : syracuseStep 547207 = 820811) B820811
theorem B547215 : Blo 546805 547215 := bstep (se 1 (by rfl) ⟨410411, by rfl⟩ : syracuseStep 547215 = 820823) B820823
theorem B6347153 : Blo 546805 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B5626259 : Blo 546805 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B1857977 : Blo 546805 1857977 := bstep (se 2 (by rfl) ⟨696741, by rfl⟩ : syracuseStep 1857977 = 1393483) B1393483
theorem B547259 : Blo 546805 547259 := bstep (se 1 (by rfl) ⟨410444, by rfl⟩ : syracuseStep 547259 = 820889) B820889
theorem B547335 : Blo 546805 547335 := bstep (se 1 (by rfl) ⟨410501, by rfl⟩ : syracuseStep 547335 = 821003) B821003
theorem B547343 : Blo 546805 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B547387 : Blo 546805 547387 := bstep (se 1 (by rfl) ⟨410540, by rfl⟩ : syracuseStep 547387 = 821081) B821081
theorem B2087491 : Blo 546805 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B3136067 : Blo 546805 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B3005047 : Blo 546805 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B547463 : Blo 546805 547463 := bstep (se 1 (by rfl) ⟨410597, by rfl⟩ : syracuseStep 547463 = 821195) B821195
theorem B1235591 : Blo 546805 1235591 := bstep (se 1 (by rfl) ⟨926693, by rfl⟩ : syracuseStep 1235591 = 1853387) B1853387
theorem B547471 : Blo 546805 547471 := bstep (se 1 (by rfl) ⟨410603, by rfl⟩ : syracuseStep 547471 = 821207) B821207
theorem B547515 : Blo 546805 547515 := bstep (se 1 (by rfl) ⟨410636, by rfl⟩ : syracuseStep 547515 = 821273) B821273
theorem B547591 : Blo 546805 547591 := bstep (se 1 (by rfl) ⟨410693, by rfl⟩ : syracuseStep 547591 = 821387) B821387
theorem B547599 : Blo 546805 547599 := bstep (se 1 (by rfl) ⟨410699, by rfl⟩ : syracuseStep 547599 = 821399) B821399
theorem B2644751 : Blo 546805 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B1563421 : Blo 546805 1563421 := bstep (se 3 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 1563421 = 586283) B586283
theorem B8903459 : Blo 546805 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B547643 : Blo 546805 547643 := bstep (se 1 (by rfl) ⟨410732, by rfl⟩ : syracuseStep 547643 = 821465) B821465
theorem B1235771 : Blo 546805 1235771 := bstep (se 1 (by rfl) ⟨926828, by rfl⟩ : syracuseStep 1235771 = 1853657) B1853657
theorem B2087795 : Blo 546805 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B547719 : Blo 546805 547719 := bstep (se 1 (by rfl) ⟨410789, by rfl⟩ : syracuseStep 547719 = 821579) B821579
theorem B547727 : Blo 546805 547727 := bstep (se 1 (by rfl) ⟨410795, by rfl⟩ : syracuseStep 547727 = 821591) B821591
theorem B3562393 : Blo 546805 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B7887779 : Blo 546805 7887779 := bstep (se 1 (by rfl) ⟨5915834, by rfl⟩ : syracuseStep 7887779 = 11831669) B11831669
theorem B1235897 : Blo 546805 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B547771 : Blo 546805 547771 := bstep (se 1 (by rfl) ⟨410828, by rfl⟩ : syracuseStep 547771 = 821657) B821657
theorem B547847 : Blo 546805 547847 := bstep (se 1 (by rfl) ⟨410885, by rfl⟩ : syracuseStep 547847 = 821771) B821771
theorem B1858571 : Blo 546805 1858571 := bstep (se 1 (by rfl) ⟨1393928, by rfl⟩ : syracuseStep 1858571 = 2787857) B2787857
theorem B547855 : Blo 546805 547855 := bstep (se 1 (by rfl) ⟨410891, by rfl⟩ : syracuseStep 547855 = 821783) B821783
theorem B1760285 : Blo 546805 1760285 := bstep (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) B660107
theorem B547899 : Blo 546805 547899 := bstep (se 1 (by rfl) ⟨410924, by rfl⟩ : syracuseStep 547899 = 821849) B821849
theorem B1858679 : Blo 546805 1858679 := bstep (se 1 (by rfl) ⟨1394009, by rfl⟩ : syracuseStep 1858679 = 2788019) B2788019
theorem B547975 : Blo 546805 547975 := bstep (se 1 (by rfl) ⟨410981, by rfl⟩ : syracuseStep 547975 = 821963) B821963
theorem B547983 : Blo 546805 547983 := bstep (se 1 (by rfl) ⟨410987, by rfl⟩ : syracuseStep 547983 = 821975) B821975
theorem B548027 : Blo 546805 548027 := bstep (se 1 (by rfl) ⟨411020, by rfl⟩ : syracuseStep 548027 = 822041) B822041
theorem B548103 : Blo 546805 548103 := bstep (se 1 (by rfl) ⟨411077, by rfl⟩ : syracuseStep 548103 = 822155) B822155
theorem B548111 : Blo 546805 548111 := bstep (se 1 (by rfl) ⟨411083, by rfl⟩ : syracuseStep 548111 = 822167) B822167
theorem B1236239 : Blo 546805 1236239 := bstep (se 1 (by rfl) ⟨927179, by rfl⟩ : syracuseStep 1236239 = 1854359) B1854359
theorem B1236257 : Blo 546805 1236257 := bstep (se 2 (by rfl) ⟨463596, by rfl⟩ : syracuseStep 1236257 = 927193) B927193
theorem B548155 : Blo 546805 548155 := bstep (se 1 (by rfl) ⟨411116, by rfl⟩ : syracuseStep 548155 = 822233) B822233
theorem B2088251 : Blo 546805 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B548231 : Blo 546805 548231 := bstep (se 1 (by rfl) ⟨411173, by rfl⟩ : syracuseStep 548231 = 822347) B822347
theorem B548239 : Blo 546805 548239 := bstep (se 1 (by rfl) ⟨411179, by rfl⟩ : syracuseStep 548239 = 822359) B822359
theorem B548283 : Blo 546805 548283 := bstep (se 1 (by rfl) ⟨411212, by rfl⟩ : syracuseStep 548283 = 822425) B822425
theorem B548359 : Blo 546805 548359 := bstep (se 1 (by rfl) ⟨411269, by rfl⟩ : syracuseStep 548359 = 822539) B822539
theorem B548367 : Blo 546805 548367 := bstep (se 1 (by rfl) ⟨411275, by rfl⟩ : syracuseStep 548367 = 822551) B822551
theorem B548411 : Blo 546805 548411 := bstep (se 1 (by rfl) ⟨411308, by rfl⟩ : syracuseStep 548411 = 822617) B822617
theorem B1236599 : Blo 546805 1236599 := bstep (se 1 (by rfl) ⟨927449, by rfl⟩ : syracuseStep 1236599 = 1854899) B1854899
theorem B548487 : Blo 546805 548487 := bstep (se 1 (by rfl) ⟨411365, by rfl⟩ : syracuseStep 548487 = 822731) B822731
theorem B548495 : Blo 546805 548495 := bstep (se 1 (by rfl) ⟨411371, by rfl⟩ : syracuseStep 548495 = 822743) B822743
theorem B548539 : Blo 546805 548539 := bstep (se 1 (by rfl) ⟨411404, by rfl⟩ : syracuseStep 548539 = 822809) B822809
theorem B548615 : Blo 546805 548615 := bstep (se 1 (by rfl) ⟨411461, by rfl⟩ : syracuseStep 548615 = 822923) B822923
theorem B548623 : Blo 546805 548623 := bstep (se 1 (by rfl) ⟨411467, by rfl⟩ : syracuseStep 548623 = 822935) B822935
theorem B2088737 : Blo 546805 2088737 := bstep (se 2 (by rfl) ⟨783276, by rfl⟩ : syracuseStep 2088737 = 1566553) B1566553
theorem B1236779 : Blo 546805 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B548667 : Blo 546805 548667 := bstep (se 1 (by rfl) ⟨411500, by rfl⟩ : syracuseStep 548667 = 823001) B823001
theorem B548743 : Blo 546805 548743 := bstep (se 1 (by rfl) ⟨411557, by rfl⟩ : syracuseStep 548743 = 823115) B823115
theorem B548751 : Blo 546805 548751 := bstep (se 1 (by rfl) ⟨411563, by rfl⟩ : syracuseStep 548751 = 823127) B823127
theorem B2645905 : Blo 546805 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B3956633 : Blo 546805 3956633 := bstep (se 2 (by rfl) ⟨1483737, by rfl⟩ : syracuseStep 3956633 = 2967475) B2967475
theorem B548795 : Blo 546805 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B548871 : Blo 546805 548871 := bstep (se 1 (by rfl) ⟨411653, by rfl⟩ : syracuseStep 548871 = 823307) B823307
theorem B4153355 : Blo 546805 4153355 := bstep (se 1 (by rfl) ⟨3115016, by rfl⟩ : syracuseStep 4153355 = 6230033) B6230033
theorem B548879 : Blo 546805 548879 := bstep (se 1 (by rfl) ⟨411659, by rfl⟩ : syracuseStep 548879 = 823319) B823319
theorem B548923 : Blo 546805 548923 := bstep (se 1 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 548923 = 823385) B823385
theorem B1663111 : Blo 546805 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1040519 : Blo 546805 1040519 := bstep (se 1 (by rfl) ⟨780389, by rfl⟩ : syracuseStep 1040519 = 1560779) B1560779
theorem B548999 : Blo 546805 548999 := bstep (se 1 (by rfl) ⟨411749, by rfl⟩ : syracuseStep 548999 = 823499) B823499
theorem B549007 : Blo 546805 549007 := bstep (se 1 (by rfl) ⟨411755, by rfl⟩ : syracuseStep 549007 = 823511) B823511
theorem B1237139 : Blo 546805 1237139 := bstep (se 1 (by rfl) ⟨927854, by rfl⟩ : syracuseStep 1237139 = 1855709) B1855709
theorem B549051 : Blo 546805 549051 := bstep (se 1 (by rfl) ⟨411788, by rfl⟩ : syracuseStep 549051 = 823577) B823577
theorem B1237193 : Blo 546805 1237193 := bstep (se 2 (by rfl) ⟨463947, by rfl⟩ : syracuseStep 1237193 = 927895) B927895
theorem B712951 : Blo 546805 712951 := bstep (se 1 (by rfl) ⟨534713, by rfl⟩ : syracuseStep 712951 = 1069427) B1069427
theorem B549127 : Blo 546805 549127 := bstep (se 1 (by rfl) ⟨411845, by rfl⟩ : syracuseStep 549127 = 823691) B823691
theorem B549135 : Blo 546805 549135 := bstep (se 1 (by rfl) ⟨411851, by rfl⟩ : syracuseStep 549135 = 823703) B823703
theorem B549179 : Blo 546805 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B549255 : Blo 546805 549255 := bstep (se 1 (by rfl) ⟨411941, by rfl⟩ : syracuseStep 549255 = 823883) B823883
theorem B549263 : Blo 546805 549263 := bstep (se 1 (by rfl) ⟨411947, by rfl⟩ : syracuseStep 549263 = 823895) B823895
theorem B2777489 : Blo 546805 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B549307 : Blo 546805 549307 := bstep (se 1 (by rfl) ⟨411980, by rfl⟩ : syracuseStep 549307 = 823961) B823961
theorem B549383 : Blo 546805 549383 := bstep (se 1 (by rfl) ⟨412037, by rfl⟩ : syracuseStep 549383 = 824075) B824075
theorem B549391 : Blo 546805 549391 := bstep (se 1 (by rfl) ⟨412043, by rfl⟩ : syracuseStep 549391 = 824087) B824087
theorem B1172027 : Blo 546805 1172027 := bstep (se 1 (by rfl) ⟨879020, by rfl⟩ : syracuseStep 1172027 = 1758041) B1758041
theorem B549435 : Blo 546805 549435 := bstep (se 1 (by rfl) ⟨412076, by rfl⟩ : syracuseStep 549435 = 824153) B824153
theorem B549511 : Blo 546805 549511 := bstep (se 1 (by rfl) ⟨412133, by rfl⟩ : syracuseStep 549511 = 824267) B824267
theorem B549519 : Blo 546805 549519 := bstep (se 1 (by rfl) ⟨412139, by rfl⟩ : syracuseStep 549519 = 824279) B824279
theorem B1565369 : Blo 546805 1565369 := bstep (se 2 (by rfl) ⟨587013, by rfl⟩ : syracuseStep 1565369 = 1174027) B1174027
theorem B549563 : Blo 546805 549563 := bstep (se 1 (by rfl) ⟨412172, by rfl⟩ : syracuseStep 549563 = 824345) B824345
theorem B2089709 : Blo 546805 2089709 := bstep (se 3 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 2089709 = 783641) B783641
theorem B549639 : Blo 546805 549639 := bstep (se 1 (by rfl) ⟨412229, by rfl⟩ : syracuseStep 549639 = 824459) B824459
theorem B549647 : Blo 546805 549647 := bstep (se 1 (by rfl) ⟨412235, by rfl⟩ : syracuseStep 549647 = 824471) B824471
theorem B549691 : Blo 546805 549691 := bstep (se 1 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 549691 = 824537) B824537
theorem B549767 : Blo 546805 549767 := bstep (se 1 (by rfl) ⟨412325, by rfl⟩ : syracuseStep 549767 = 824651) B824651
theorem B1237895 : Blo 546805 1237895 := bstep (se 1 (by rfl) ⟨928421, by rfl⟩ : syracuseStep 1237895 = 1856843) B1856843
theorem B549775 : Blo 546805 549775 := bstep (se 1 (by rfl) ⟨412331, by rfl⟩ : syracuseStep 549775 = 824663) B824663
theorem B549819 : Blo 546805 549819 := bstep (se 1 (by rfl) ⟨412364, by rfl⟩ : syracuseStep 549819 = 824729) B824729
theorem B549895 : Blo 546805 549895 := bstep (se 1 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 549895 = 824843) B824843
theorem B549903 : Blo 546805 549903 := bstep (se 1 (by rfl) ⟨412427, by rfl⟩ : syracuseStep 549903 = 824855) B824855
theorem B549947 : Blo 546805 549947 := bstep (se 1 (by rfl) ⟨412460, by rfl⟩ : syracuseStep 549947 = 824921) B824921
theorem B1238075 : Blo 546805 1238075 := bstep (se 1 (by rfl) ⟨928556, by rfl⟩ : syracuseStep 1238075 = 1857113) B1857113
theorem B615559 : Blo 546805 615559 := bstep (se 1 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 615559 = 923339) B923339
theorem B550023 : Blo 546805 550023 := bstep (se 1 (by rfl) ⟨412517, by rfl⟩ : syracuseStep 550023 = 825035) B825035
theorem B550031 : Blo 546805 550031 := bstep (se 1 (by rfl) ⟨412523, by rfl⟩ : syracuseStep 550031 = 825047) B825047
theorem B1238201 : Blo 546805 1238201 := bstep (se 2 (by rfl) ⟨464325, by rfl⟩ : syracuseStep 1238201 = 928651) B928651
theorem B550075 : Blo 546805 550075 := bstep (se 1 (by rfl) ⟨412556, by rfl⟩ : syracuseStep 550075 = 825113) B825113
theorem B550151 : Blo 546805 550151 := bstep (se 1 (by rfl) ⟨412613, by rfl⟩ : syracuseStep 550151 = 825227) B825227
theorem B550159 : Blo 546805 550159 := bstep (se 1 (by rfl) ⟨412619, by rfl⟩ : syracuseStep 550159 = 825239) B825239
theorem B615739 : Blo 546805 615739 := bstep (se 1 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 615739 = 923609) B923609
theorem B550203 : Blo 546805 550203 := bstep (se 1 (by rfl) ⟨412652, by rfl⟩ : syracuseStep 550203 = 825305) B825305
theorem B550279 : Blo 546805 550279 := bstep (se 1 (by rfl) ⟨412709, by rfl⟩ : syracuseStep 550279 = 825419) B825419
theorem B550287 : Blo 546805 550287 := bstep (se 1 (by rfl) ⟨412715, by rfl⟩ : syracuseStep 550287 = 825431) B825431
theorem B2090393 : Blo 546805 2090393 := bstep (se 2 (by rfl) ⟨783897, by rfl⟩ : syracuseStep 2090393 = 1567795) B1567795
theorem B550331 : Blo 546805 550331 := bstep (se 1 (by rfl) ⟨412748, by rfl⟩ : syracuseStep 550331 = 825497) B825497
theorem B4220369 : Blo 546805 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B550407 : Blo 546805 550407 := bstep (se 1 (by rfl) ⟨412805, by rfl⟩ : syracuseStep 550407 = 825611) B825611
theorem B550415 : Blo 546805 550415 := bstep (se 1 (by rfl) ⟨412811, by rfl⟩ : syracuseStep 550415 = 825623) B825623
theorem B1238543 : Blo 546805 1238543 := bstep (se 1 (by rfl) ⟨928907, by rfl⟩ : syracuseStep 1238543 = 1857815) B1857815
theorem B1238561 : Blo 546805 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B1762859 : Blo 546805 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B550459 : Blo 546805 550459 := bstep (se 1 (by rfl) ⟨412844, by rfl⟩ : syracuseStep 550459 = 825689) B825689
theorem B550535 : Blo 546805 550535 := bstep (se 1 (by rfl) ⟨412901, by rfl⟩ : syracuseStep 550535 = 825803) B825803
theorem B550543 : Blo 546805 550543 := bstep (se 1 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 550543 = 825815) B825815
theorem B550587 : Blo 546805 550587 := bstep (se 1 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 550587 = 825881) B825881
theorem B1042121 : Blo 546805 1042121 := bstep (se 2 (by rfl) ⟨390795, by rfl⟩ : syracuseStep 1042121 = 781591) B781591
theorem B550663 : Blo 546805 550663 := bstep (se 1 (by rfl) ⟨412997, by rfl⟩ : syracuseStep 550663 = 825995) B825995
theorem B616207 : Blo 546805 616207 := bstep (se 1 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 616207 = 924311) B924311
theorem B550671 : Blo 546805 550671 := bstep (se 1 (by rfl) ⟨413003, by rfl⟩ : syracuseStep 550671 = 826007) B826007
theorem B550715 : Blo 546805 550715 := bstep (se 1 (by rfl) ⟨413036, by rfl⟩ : syracuseStep 550715 = 826073) B826073
theorem B1238903 : Blo 546805 1238903 := bstep (se 1 (by rfl) ⟨929177, by rfl⟩ : syracuseStep 1238903 = 1858355) B1858355
theorem B550791 : Blo 546805 550791 := bstep (se 1 (by rfl) ⟨413093, by rfl⟩ : syracuseStep 550791 = 826187) B826187
theorem B550799 : Blo 546805 550799 := bstep (se 1 (by rfl) ⟨413099, by rfl⟩ : syracuseStep 550799 = 826199) B826199
theorem B1566611 : Blo 546805 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B4155299 : Blo 546805 4155299 := bstep (se 1 (by rfl) ⟨3116474, by rfl⟩ : syracuseStep 4155299 = 6232949) B6232949
theorem B878521 : Blo 546805 878521 := bstep (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) B658891
theorem B1239083 : Blo 546805 1239083 := bstep (se 1 (by rfl) ⟨929312, by rfl⟩ : syracuseStep 1239083 = 1858625) B1858625
theorem B616711 : Blo 546805 616711 := bstep (se 1 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 616711 = 925067) B925067
theorem B780617 : Blo 546805 780617 := bstep (se 2 (by rfl) ⟨292731, by rfl⟩ : syracuseStep 780617 = 585463) B585463
theorem B616891 : Blo 546805 616891 := bstep (se 1 (by rfl) ⟨462668, by rfl⟩ : syracuseStep 616891 = 925337) B925337
theorem B2779595 : Blo 546805 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B5630417 : Blo 546805 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B5630735 : Blo 546805 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B2779919 : Blo 546805 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B6253361 : Blo 546805 6253361 := bstep (se 2 (by rfl) ⟨2345010, by rfl⟩ : syracuseStep 6253361 = 4690021) B4690021
theorem B6876019 : Blo 546805 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B617359 : Blo 546805 617359 := bstep (se 1 (by rfl) ⟨463019, by rfl⟩ : syracuseStep 617359 = 926039) B926039
theorem B879751 : Blo 546805 879751 := bstep (se 1 (by rfl) ⟨659813, by rfl⟩ : syracuseStep 879751 = 1319627) B1319627
theorem B781483 : Blo 546805 781483 := bstep (se 1 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 781483 = 1172225) B1172225
theorem B1568011 : Blo 546805 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B1666333 : Blo 546805 1666333 := bstep (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) B624875
theorem B585019 : Blo 546805 585019 := bstep (se 1 (by rfl) ⟨438764, by rfl⟩ : syracuseStep 585019 = 877529) B877529
theorem B10513799 : Blo 546805 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B617863 : Blo 546805 617863 := bstep (se 1 (by rfl) ⟨463397, by rfl⟩ : syracuseStep 617863 = 926795) B926795
theorem B1666457 : Blo 546805 1666457 := bstep (se 2 (by rfl) ⟨624921, by rfl⟩ : syracuseStep 1666457 = 1249843) B1249843
theorem B3960323 : Blo 546805 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B1568285 : Blo 546805 1568285 := bstep (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) B588107
theorem B618043 : Blo 546805 618043 := bstep (se 1 (by rfl) ⟨463532, by rfl⟩ : syracuseStep 618043 = 927065) B927065
theorem B1044103 : Blo 546805 1044103 := bstep (se 1 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 1044103 = 1566155) B1566155
theorem B880399 : Blo 546805 880399 := bstep (se 1 (by rfl) ⟨660299, by rfl⟩ : syracuseStep 880399 = 1320599) B1320599
theorem B1109819 : Blo 546805 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B4452185 : Blo 546805 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B618511 : Blo 546805 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B11300957 : Blo 546805 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B2781377 : Blo 546805 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B4157729 : Blo 546805 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B4452641 : Blo 546805 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B619015 : Blo 546805 619015 := bstep (se 1 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 619015 = 928523) B928523
theorem B619195 : Blo 546805 619195 := bstep (se 1 (by rfl) ⟨464396, by rfl⟩ : syracuseStep 619195 = 928793) B928793
theorem B783049 : Blo 546805 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B3961649 : Blo 546805 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B881609 : Blo 546805 881609 := bstep (se 2 (by rfl) ⟨330603, by rfl⟩ : syracuseStep 881609 = 661207) B661207
theorem B1504289 : Blo 546805 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B881783 : Blo 546805 881783 := bstep (se 1 (by rfl) ⟨661337, by rfl⟩ : syracuseStep 881783 = 1322675) B1322675
theorem B4158701 : Blo 546805 4158701 := bstep (se 3 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 4158701 = 1559513) B1559513
theorem B783607 : Blo 546805 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B2782673 : Blo 546805 2782673 := bstep (se 2 (by rfl) ⟨1043502, by rfl⟩ : syracuseStep 2782673 = 2087005) B2087005
theorem B3175901 : Blo 546805 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B784171 : Blo 546805 784171 := bstep (se 1 (by rfl) ⟨588128, by rfl⟩ : syracuseStep 784171 = 1176257) B1176257
theorem B3766219 : Blo 546805 3766219 := bstep (se 1 (by rfl) ⟨2824664, by rfl⟩ : syracuseStep 3766219 = 5649329) B5649329
theorem B3996125 : Blo 546805 3996125 := bstep (se 3 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 3996125 = 1498547) B1498547
theorem B1505911 : Blo 546805 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B4160645 : Blo 546805 4160645 := bstep (se 4 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 4160645 = 780121) B780121
theorem B5930273 : Blo 546805 5930273 := bstep (se 2 (by rfl) ⟨2223852, by rfl⟩ : syracuseStep 5930273 = 4447705) B4447705
theorem B1670519 : Blo 546805 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B2784779 : Blo 546805 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B2784941 : Blo 546805 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B4456241 : Blo 546805 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B2817995 : Blo 546805 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B4161617 : Blo 546805 4161617 := bstep (se 2 (by rfl) ⟨1560606, by rfl⟩ : syracuseStep 4161617 = 3121213) B3121213
theorem B4456529 : Blo 546805 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B7012889 : Blo 546805 7012889 := bstep (se 2 (by rfl) ⟨2629833, by rfl⟩ : syracuseStep 7012889 = 5259667) B5259667
theorem B721771 : Blo 546805 721771 := bstep (se 1 (by rfl) ⟨541328, by rfl⟩ : syracuseStep 721771 = 1082657) B1082657
theorem B1115041 : Blo 546805 1115041 := bstep (se 2 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 1115041 = 836281) B836281
theorem B558299 : Blo 546805 558299 := bstep (se 1 (by rfl) ⟨418724, by rfl⟩ : syracuseStep 558299 = 837449) B837449
theorem B3802405 : Blo 546805 3802405 := bstep (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) B712951
theorem B820655 : Blo 546805 820655 := bstep (se 1 (by rfl) ⟨615491, by rfl⟩ : syracuseStep 820655 = 1230983) B1230983
theorem B820745 : Blo 546805 820745 := bstep (se 2 (by rfl) ⟨307779, by rfl⟩ : syracuseStep 820745 = 615559) B615559
theorem B820775 : Blo 546805 820775 := bstep (se 1 (by rfl) ⟨615581, by rfl⟩ : syracuseStep 820775 = 1231163) B1231163
theorem B820859 : Blo 546805 820859 := bstep (se 1 (by rfl) ⟨615644, by rfl⟩ : syracuseStep 820859 = 1231289) B1231289
theorem B3507857 : Blo 546805 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B820985 : Blo 546805 820985 := bstep (se 2 (by rfl) ⟨307869, by rfl⟩ : syracuseStep 820985 = 615739) B615739
theorem B821087 : Blo 546805 821087 := bstep (se 1 (by rfl) ⟨615815, by rfl⟩ : syracuseStep 821087 = 1231631) B1231631
theorem B821099 : Blo 546805 821099 := bstep (se 1 (by rfl) ⟨615824, by rfl⟩ : syracuseStep 821099 = 1231649) B1231649
theorem B2230199 : Blo 546805 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B821327 : Blo 546805 821327 := bstep (se 1 (by rfl) ⟨615995, by rfl⟩ : syracuseStep 821327 = 1231991) B1231991
theorem B23693411 : Blo 546805 23693411 := bstep (se 1 (by rfl) ⟨17770058, by rfl⟩ : syracuseStep 23693411 = 35540117) B35540117
theorem B821447 : Blo 546805 821447 := bstep (se 1 (by rfl) ⟨616085, by rfl⟩ : syracuseStep 821447 = 1232171) B1232171
theorem B985439 : Blo 546805 985439 := bstep (se 1 (by rfl) ⟨739079, by rfl⟩ : syracuseStep 985439 = 1478159) B1478159
theorem B821609 : Blo 546805 821609 := bstep (se 2 (by rfl) ⟨308103, by rfl⟩ : syracuseStep 821609 = 616207) B616207
theorem B657839 : Blo 546805 657839 := bstep (se 1 (by rfl) ⟨493379, by rfl⟩ : syracuseStep 657839 = 986759) B986759
theorem B821687 : Blo 546805 821687 := bstep (se 1 (by rfl) ⟨616265, by rfl⟩ : syracuseStep 821687 = 1232531) B1232531
theorem B821723 : Blo 546805 821723 := bstep (se 1 (by rfl) ⟨616292, by rfl⟩ : syracuseStep 821723 = 1232585) B1232585
theorem B3115655 : Blo 546805 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B822191 : Blo 546805 822191 := bstep (se 1 (by rfl) ⟨616643, by rfl⟩ : syracuseStep 822191 = 1233287) B1233287
theorem B822281 : Blo 546805 822281 := bstep (se 2 (by rfl) ⟨308355, by rfl⟩ : syracuseStep 822281 = 616711) B616711
theorem B822311 : Blo 546805 822311 := bstep (se 1 (by rfl) ⟨616733, by rfl⟩ : syracuseStep 822311 = 1233467) B1233467
theorem B3509315 : Blo 546805 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B822395 : Blo 546805 822395 := bstep (se 1 (by rfl) ⟨616796, by rfl⟩ : syracuseStep 822395 = 1233593) B1233593
theorem B822521 : Blo 546805 822521 := bstep (se 2 (by rfl) ⟨308445, by rfl⟩ : syracuseStep 822521 = 616891) B616891
theorem B16026917 : Blo 546805 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B822623 : Blo 546805 822623 := bstep (se 1 (by rfl) ⟨616967, by rfl⟩ : syracuseStep 822623 = 1233935) B1233935
theorem B822635 : Blo 546805 822635 := bstep (se 1 (by rfl) ⟨616976, by rfl⟩ : syracuseStep 822635 = 1233953) B1233953
theorem B16944527 : Blo 546805 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B3575335 : Blo 546805 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B822863 : Blo 546805 822863 := bstep (se 1 (by rfl) ⟨617147, by rfl⟩ : syracuseStep 822863 = 1234295) B1234295
theorem B822983 : Blo 546805 822983 := bstep (se 1 (by rfl) ⟨617237, by rfl⟩ : syracuseStep 822983 = 1234475) B1234475
theorem B823145 : Blo 546805 823145 := bstep (se 2 (by rfl) ⟨308679, by rfl⟩ : syracuseStep 823145 = 617359) B617359
theorem B19009397 : Blo 546805 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B823223 : Blo 546805 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B823259 : Blo 546805 823259 := bstep (se 1 (by rfl) ⟨617444, by rfl⟩ : syracuseStep 823259 = 1234889) B1234889
theorem B3117113 : Blo 546805 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B790651 : Blo 546805 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B4231435 : Blo 546805 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B823727 : Blo 546805 823727 := bstep (se 1 (by rfl) ⟨617795, by rfl⟩ : syracuseStep 823727 = 1235591) B1235591
theorem B823817 : Blo 546805 823817 := bstep (se 2 (by rfl) ⟨308931, by rfl⟩ : syracuseStep 823817 = 617863) B617863
theorem B5935639 : Blo 546805 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B823847 : Blo 546805 823847 := bstep (se 1 (by rfl) ⟨617885, by rfl⟩ : syracuseStep 823847 = 1235771) B1235771
theorem B823931 : Blo 546805 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B9900755 : Blo 546805 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B824057 : Blo 546805 824057 := bstep (se 2 (by rfl) ⟨309021, by rfl⟩ : syracuseStep 824057 = 618043) B618043
theorem B4166477 : Blo 546805 4166477 := bstep (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) B1562429
theorem B824159 : Blo 546805 824159 := bstep (se 1 (by rfl) ⟨618119, by rfl⟩ : syracuseStep 824159 = 1236239) B1236239
theorem B824171 : Blo 546805 824171 := bstep (se 1 (by rfl) ⟨618128, by rfl⟩ : syracuseStep 824171 = 1236257) B1236257
theorem B824399 : Blo 546805 824399 := bstep (se 1 (by rfl) ⟨618299, by rfl⟩ : syracuseStep 824399 = 1236599) B1236599
theorem B824519 : Blo 546805 824519 := bstep (se 1 (by rfl) ⟨618389, by rfl⟩ : syracuseStep 824519 = 1236779) B1236779
theorem B922873 : Blo 546805 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B824681 : Blo 546805 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B1316225 : Blo 546805 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B1578383 : Blo 546805 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B693679 : Blo 546805 693679 := bstep (se 1 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 693679 = 1040519) B1040519
theorem B824759 : Blo 546805 824759 := bstep (se 1 (by rfl) ⟨618569, by rfl⟩ : syracuseStep 824759 = 1237139) B1237139
theorem B824795 : Blo 546805 824795 := bstep (se 1 (by rfl) ⟨618596, by rfl⟩ : syracuseStep 824795 = 1237193) B1237193
theorem B923143 : Blo 546805 923143 := bstep (se 1 (by rfl) ⟨692357, by rfl⟩ : syracuseStep 923143 = 1384715) B1384715
theorem B1251065 : Blo 546805 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B825263 : Blo 546805 825263 := bstep (se 1 (by rfl) ⟨618947, by rfl⟩ : syracuseStep 825263 = 1237895) B1237895
theorem B923575 : Blo 546805 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B825353 : Blo 546805 825353 := bstep (se 2 (by rfl) ⟨309507, by rfl⟩ : syracuseStep 825353 = 619015) B619015
theorem B4692005 : Blo 546805 4692005 := bstep (se 4 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 4692005 = 879751) B879751
theorem B825383 : Blo 546805 825383 := bstep (se 1 (by rfl) ⟨619037, by rfl⟩ : syracuseStep 825383 = 1238075) B1238075
theorem B923771 : Blo 546805 923771 := bstep (se 1 (by rfl) ⟨692828, by rfl⟩ : syracuseStep 923771 = 1385657) B1385657
theorem B825467 : Blo 546805 825467 := bstep (se 1 (by rfl) ⟨619100, by rfl⟩ : syracuseStep 825467 = 1238201) B1238201
theorem B825593 : Blo 546805 825593 := bstep (se 2 (by rfl) ⟨309597, by rfl⟩ : syracuseStep 825593 = 619195) B619195
theorem B825695 : Blo 546805 825695 := bstep (se 1 (by rfl) ⟨619271, by rfl⟩ : syracuseStep 825695 = 1238543) B1238543
theorem B825707 : Blo 546805 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B694747 : Blo 546805 694747 := bstep (se 1 (by rfl) ⟨521060, by rfl⟩ : syracuseStep 694747 = 1042121) B1042121
theorem B924169 : Blo 546805 924169 := bstep (se 2 (by rfl) ⟨346563, by rfl⟩ : syracuseStep 924169 = 693127) B693127
theorem B825935 : Blo 546805 825935 := bstep (se 1 (by rfl) ⟨619451, by rfl⟩ : syracuseStep 825935 = 1238903) B1238903
theorem B924331 : Blo 546805 924331 := bstep (se 1 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 924331 = 1386497) B1386497
theorem B826055 : Blo 546805 826055 := bstep (se 1 (by rfl) ⟨619541, by rfl⟩ : syracuseStep 826055 = 1239083) B1239083
theorem B924635 : Blo 546805 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B1317907 : Blo 546805 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B3120281 : Blo 546805 3120281 := bstep (se 2 (by rfl) ⟨1170105, by rfl⟩ : syracuseStep 3120281 = 2340211) B2340211
theorem B924871 : Blo 546805 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B4168907 : Blo 546805 4168907 := bstep (se 1 (by rfl) ⟨3126680, by rfl⟩ : syracuseStep 4168907 = 6253361) B6253361
theorem B925033 : Blo 546805 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B990571 : Blo 546805 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B3513725 : Blo 546805 3513725 := bstep (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) B1317647
theorem B3743119 : Blo 546805 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B1252961 : Blo 546805 1252961 := bstep (se 2 (by rfl) ⟨469860, by rfl⟩ : syracuseStep 1252961 = 939721) B939721
theorem B1777351 : Blo 546805 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B4562669 : Blo 546805 4562669 := bstep (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) B1711001
theorem B925627 : Blo 546805 925627 := bstep (se 1 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 925627 = 1388441) B1388441
theorem B925735 : Blo 546805 925735 := bstep (se 1 (by rfl) ⟨694301, by rfl⟩ : syracuseStep 925735 = 1388603) B1388603
theorem B926059 : Blo 546805 926059 := bstep (se 1 (by rfl) ⟨694544, by rfl⟩ : syracuseStep 926059 = 1389089) B1389089
theorem B1384847 : Blo 546805 1384847 := bstep (se 1 (by rfl) ⟨1038635, by rfl⟩ : syracuseStep 1384847 = 2077271) B2077271
theorem B1385171 : Blo 546805 1385171 := bstep (se 1 (by rfl) ⟨1038878, by rfl⟩ : syracuseStep 1385171 = 2077757) B2077757
theorem B1319753 : Blo 546805 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B2007881 : Blo 546805 2007881 := bstep (se 2 (by rfl) ⟨752955, by rfl⟩ : syracuseStep 2007881 = 1505911) B1505911
theorem B1057679 : Blo 546805 1057679 := bstep (se 1 (by rfl) ⟨793259, by rfl⟩ : syracuseStep 1057679 = 1586519) B1586519
theorem B31532165 : Blo 546805 31532165 := bstep (se 4 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 31532165 = 5912281) B5912281
theorem B992503 : Blo 546805 992503 := bstep (se 1 (by rfl) ⟨744377, by rfl⟩ : syracuseStep 992503 = 1488755) B1488755
theorem B927119 : Blo 546805 927119 := bstep (se 1 (by rfl) ⟨695339, by rfl⟩ : syracuseStep 927119 = 1390679) B1390679
theorem B927355 : Blo 546805 927355 := bstep (se 1 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 927355 = 1391033) B1391033
theorem B2664083 : Blo 546805 2664083 := bstep (se 1 (by rfl) ⟨1998062, by rfl⟩ : syracuseStep 2664083 = 3996125) B3996125
theorem B1386335 : Blo 546805 1386335 := bstep (se 1 (by rfl) ⟨1039751, by rfl⟩ : syracuseStep 1386335 = 2079503) B2079503
theorem B1976183 : Blo 546805 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B2959517 : Blo 546805 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B11872493 : Blo 546805 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B928219 : Blo 546805 928219 := bstep (se 1 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 928219 = 1392329) B1392329
theorem B7514653 : Blo 546805 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B3943343 : Blo 546805 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B1387439 : Blo 546805 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B1321991 : Blo 546805 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B928847 : Blo 546805 928847 := bstep (se 1 (by rfl) ⟨696635, by rfl⟩ : syracuseStep 928847 = 1393271) B1393271
theorem B1846907 : Blo 546805 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B2076299 : Blo 546805 2076299 := bstep (se 1 (by rfl) ⟨1557224, by rfl⟩ : syracuseStep 2076299 = 3114449) B3114449
theorem B1847069 : Blo 546805 1847069 := bstep (se 3 (by rfl) ⟨346325, by rfl⟩ : syracuseStep 1847069 = 692651) B692651
theorem B3125087 : Blo 546805 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B4239397 : Blo 546805 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B1388623 : Blo 546805 1388623 := bstep (se 1 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 1388623 = 2082935) B2082935
theorem B3125405 : Blo 546805 3125405 := bstep (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) B1172027
theorem B2109635 : Blo 546805 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B1847771 : Blo 546805 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B3944983 : Blo 546805 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B1389271 : Blo 546805 1389271 := bstep (se 1 (by rfl) ⟨1041953, by rfl⟩ : syracuseStep 1389271 = 2083907) B2083907
theorem B2077559 : Blo 546805 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B4174739 : Blo 546805 4174739 := bstep (se 1 (by rfl) ⟨3131054, by rfl⟩ : syracuseStep 4174739 = 6262109) B6262109
theorem B1389575 : Blo 546805 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B5715011 : Blo 546805 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B1848473 : Blo 546805 1848473 := bstep (se 2 (by rfl) ⟨693177, by rfl⟩ : syracuseStep 1848473 = 1386355) B1386355
theorem B4011437 : Blo 546805 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B2078531 : Blo 546805 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B4175711 : Blo 546805 4175711 := bstep (se 1 (by rfl) ⟨3131783, by rfl⟩ : syracuseStep 4175711 = 6263567) B6263567
theorem B669547 : Blo 546805 669547 := bstep (se 1 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 669547 = 1004321) B1004321
theorem B3946427 : Blo 546805 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B1849661 : Blo 546805 1849661 := bstep (se 3 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 1849661 = 693623) B693623
theorem B6666887 : Blo 546805 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B3160939 : Blo 546805 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B3750839 : Blo 546805 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B3128321 : Blo 546805 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B1752121 : Blo 546805 1752121 := bstep (se 2 (by rfl) ⟨657045, by rfl⟩ : syracuseStep 1752121 = 1314091) B1314091
theorem B1850525 : Blo 546805 1850525 := bstep (se 3 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 1850525 = 693947) B693947
theorem B1391863 : Blo 546805 1391863 := bstep (se 1 (by rfl) ⟨1043897, by rfl⟩ : syracuseStep 1391863 = 2087795) B2087795
theorem B5258519 : Blo 546805 5258519 := bstep (se 1 (by rfl) ⟨3943889, by rfl⟩ : syracuseStep 5258519 = 7887779) B7887779
theorem B2080201 : Blo 546805 2080201 := bstep (se 2 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 2080201 = 1560151) B1560151
theorem B3128777 : Blo 546805 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B1392137 : Blo 546805 1392137 := bstep (se 2 (by rfl) ⟨522051, by rfl⟩ : syracuseStep 1392137 = 1044103) B1044103
theorem B1392167 : Blo 546805 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B1851065 : Blo 546805 1851065 := bstep (se 2 (by rfl) ⟨694149, by rfl⟩ : syracuseStep 1851065 = 1388299) B1388299
theorem B2080505 : Blo 546805 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B8437537 : Blo 546805 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1392491 : Blo 546805 1392491 := bstep (se 1 (by rfl) ⟨1044368, by rfl⟩ : syracuseStep 1392491 = 2088737) B2088737
theorem B2637677 : Blo 546805 2637677 := bstep (se 3 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 2637677 = 989129) B989129
theorem B2080673 : Blo 546805 2080673 := bstep (se 2 (by rfl) ⟨780252, by rfl⟩ : syracuseStep 2080673 = 1560505) B1560505
theorem B2080687 : Blo 546805 2080687 := bstep (se 1 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 2080687 = 3121031) B3121031
theorem B2637755 : Blo 546805 2637755 := bstep (se 1 (by rfl) ⟨1978316, by rfl⟩ : syracuseStep 2637755 = 3956633) B3956633
theorem B2768903 : Blo 546805 2768903 := bstep (se 1 (by rfl) ⟨2076677, by rfl⟩ : syracuseStep 2768903 = 4153355) B4153355
theorem B1851659 : Blo 546805 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B2769389 : Blo 546805 2769389 := bstep (se 3 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 2769389 = 1038521) B1038521
theorem B1393139 : Blo 546805 1393139 := bstep (se 1 (by rfl) ⟨1044854, by rfl⟩ : syracuseStep 1393139 = 2089709) B2089709
theorem B1851929 : Blo 546805 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B836135 : Blo 546805 836135 := bstep (se 1 (by rfl) ⟨627101, by rfl⟩ : syracuseStep 836135 = 1254203) B1254203
theorem B967339 : Blo 546805 967339 := bstep (se 1 (by rfl) ⟨725504, by rfl⟩ : syracuseStep 967339 = 1451009) B1451009
theorem B2081645 : Blo 546805 2081645 := bstep (se 3 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 2081645 = 780617) B780617
theorem B1393595 : Blo 546805 1393595 := bstep (se 1 (by rfl) ⟨1045196, by rfl⟩ : syracuseStep 1393595 = 2090393) B2090393
theorem B2081963 : Blo 546805 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B2770199 : Blo 546805 2770199 := bstep (se 1 (by rfl) ⟨2077649, by rfl⟩ : syracuseStep 2770199 = 4155299) B4155299
theorem B1558055 : Blo 546805 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B3130919 : Blo 546805 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B1853063 : Blo 546805 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B3753611 : Blo 546805 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B1853117 : Blo 546805 1853117 := bstep (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) B694919
theorem B8931161 : Blo 546805 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B3753823 : Blo 546805 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B1853279 : Blo 546805 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B1230767 : Blo 546805 1230767 := bstep (se 1 (by rfl) ⟨923075, by rfl⟩ : syracuseStep 1230767 = 1846151) B1846151
theorem B1853441 : Blo 546805 1853441 := bstep (se 2 (by rfl) ⟨695040, by rfl⟩ : syracuseStep 1853441 = 1390081) B1390081
theorem B1231019 : Blo 546805 1231019 := bstep (se 1 (by rfl) ⟨923264, by rfl⟩ : syracuseStep 1231019 = 1846529) B1846529
theorem B2640215 : Blo 546805 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B1231559 : Blo 546805 1231559 := bstep (se 1 (by rfl) ⟨923669, by rfl⟩ : syracuseStep 1231559 = 1847339) B1847339
theorem B1854251 : Blo 546805 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B2771819 : Blo 546805 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B2968427 : Blo 546805 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B1854521 : Blo 546805 1854521 := bstep (se 2 (by rfl) ⟨695445, by rfl⟩ : syracuseStep 1854521 = 1390891) B1390891
theorem B2641099 : Blo 546805 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B3132695 : Blo 546805 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B1854845 : Blo 546805 1854845 := bstep (se 3 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 1854845 = 695567) B695567
theorem B15814061 : Blo 546805 15814061 := bstep (se 3 (by rfl) ⟨2965136, by rfl⟩ : syracuseStep 15814061 = 5930273) B5930273
theorem B2772467 : Blo 546805 2772467 := bstep (se 1 (by rfl) ⟨2079350, by rfl⟩ : syracuseStep 2772467 = 4158701) B4158701
theorem B1232423 : Blo 546805 1232423 := bstep (se 1 (by rfl) ⟨924317, by rfl⟩ : syracuseStep 1232423 = 1848635) B1848635
theorem B4181543 : Blo 546805 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B1756811 : Blo 546805 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B1855115 : Blo 546805 1855115 := bstep (se 1 (by rfl) ⟨1391336, by rfl⟩ : syracuseStep 1855115 = 2782673) B2782673
theorem B2117267 : Blo 546805 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B2084561 : Blo 546805 2084561 := bstep (se 2 (by rfl) ⟨781710, by rfl⟩ : syracuseStep 2084561 = 1563421) B1563421
theorem B1232747 : Blo 546805 1232747 := bstep (se 1 (by rfl) ⟨924560, by rfl⟩ : syracuseStep 1232747 = 1849121) B1849121
theorem B1232801 : Blo 546805 1232801 := bstep (se 2 (by rfl) ⟨462300, by rfl⟩ : syracuseStep 1232801 = 924601) B924601
theorem B2084879 : Blo 546805 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B1233143 : Blo 546805 1233143 := bstep (se 1 (by rfl) ⟨924857, by rfl⟩ : syracuseStep 1233143 = 1849715) B1849715
theorem B1856033 : Blo 546805 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B1167995 : Blo 546805 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B1856249 : Blo 546805 1856249 := bstep (se 2 (by rfl) ⟨696093, by rfl⟩ : syracuseStep 1856249 = 1392187) B1392187
theorem B2773763 : Blo 546805 2773763 := bstep (se 1 (by rfl) ⟨2080322, by rfl⟩ : syracuseStep 2773763 = 4160645) B4160645
theorem B1233737 : Blo 546805 1233737 := bstep (se 2 (by rfl) ⟨462651, by rfl⟩ : syracuseStep 1233737 = 925303) B925303
theorem B1168303 : Blo 546805 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B1856519 : Blo 546805 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B1856627 : Blo 546805 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B3527873 : Blo 546805 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B2970827 : Blo 546805 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B1856897 : Blo 546805 1856897 := bstep (se 2 (by rfl) ⟨696336, by rfl⟩ : syracuseStep 1856897 = 1392673) B1392673
theorem B1005095 : Blo 546805 1005095 := bstep (se 1 (by rfl) ⟨753821, by rfl⟩ : syracuseStep 1005095 = 1507643) B1507643
theorem B1234529 : Blo 546805 1234529 := bstep (se 2 (by rfl) ⟨462948, by rfl⟩ : syracuseStep 1234529 = 925897) B925897
theorem B1038187 : Blo 546805 1038187 := bstep (se 1 (by rfl) ⟨778640, by rfl⟩ : syracuseStep 1038187 = 1557281) B1557281
theorem B1234871 : Blo 546805 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B8869925 : Blo 546805 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B546855 : Blo 546805 546855 := bstep (se 1 (by rfl) ⟨410141, by rfl⟩ : syracuseStep 546855 = 820283) B820283
theorem B546895 : Blo 546805 546895 := bstep (se 1 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 546895 = 820343) B820343
theorem B1038415 : Blo 546805 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B2086991 : Blo 546805 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B546911 : Blo 546805 546911 := bstep (se 1 (by rfl) ⟨410183, by rfl⟩ : syracuseStep 546911 = 820367) B820367
theorem B546939 : Blo 546805 546939 := bstep (se 1 (by rfl) ⟨410204, by rfl⟩ : syracuseStep 546939 = 820409) B820409
theorem B1857707 : Blo 546805 1857707 := bstep (se 1 (by rfl) ⟨1393280, by rfl⟩ : syracuseStep 1857707 = 2786561) B2786561
theorem B546991 : Blo 546805 546991 := bstep (se 1 (by rfl) ⟨410243, by rfl⟩ : syracuseStep 546991 = 820487) B820487
theorem B547015 : Blo 546805 547015 := bstep (se 1 (by rfl) ⟨410261, by rfl⟩ : syracuseStep 547015 = 820523) B820523
theorem B547035 : Blo 546805 547035 := bstep (se 1 (by rfl) ⟨410276, by rfl⟩ : syracuseStep 547035 = 820553) B820553
theorem B547111 : Blo 546805 547111 := bstep (se 1 (by rfl) ⟨410333, by rfl⟩ : syracuseStep 547111 = 820667) B820667
theorem B547151 : Blo 546805 547151 := bstep (se 1 (by rfl) ⟨410363, by rfl⟩ : syracuseStep 547151 = 820727) B820727
theorem B2775383 : Blo 546805 2775383 := bstep (se 1 (by rfl) ⟨2081537, by rfl⟩ : syracuseStep 2775383 = 4163075) B4163075
theorem B547167 : Blo 546805 547167 := bstep (se 1 (by rfl) ⟨410375, by rfl⟩ : syracuseStep 547167 = 820751) B820751
theorem B547195 : Blo 546805 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B547247 : Blo 546805 547247 := bstep (se 1 (by rfl) ⟨410435, by rfl⟩ : syracuseStep 547247 = 820871) B820871
theorem B547271 : Blo 546805 547271 := bstep (se 1 (by rfl) ⟨410453, by rfl⟩ : syracuseStep 547271 = 820907) B820907
theorem B4446667 : Blo 546805 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B547291 : Blo 546805 547291 := bstep (se 1 (by rfl) ⟨410468, by rfl⟩ : syracuseStep 547291 = 820937) B820937
theorem B1235465 : Blo 546805 1235465 := bstep (se 2 (by rfl) ⟨463299, by rfl⟩ : syracuseStep 1235465 = 926599) B926599
theorem B547367 : Blo 546805 547367 := bstep (se 1 (by rfl) ⟨410525, by rfl⟩ : syracuseStep 547367 = 821051) B821051
theorem B547407 : Blo 546805 547407 := bstep (se 1 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 547407 = 821111) B821111
theorem B547423 : Blo 546805 547423 := bstep (se 1 (by rfl) ⟨410567, by rfl⟩ : syracuseStep 547423 = 821135) B821135
theorem B547451 : Blo 546805 547451 := bstep (se 1 (by rfl) ⟨410588, by rfl⟩ : syracuseStep 547451 = 821177) B821177
theorem B547503 : Blo 546805 547503 := bstep (se 1 (by rfl) ⟨410627, by rfl⟩ : syracuseStep 547503 = 821255) B821255
theorem B547527 : Blo 546805 547527 := bstep (se 1 (by rfl) ⟨410645, by rfl⟩ : syracuseStep 547527 = 821291) B821291
theorem B1858247 : Blo 546805 1858247 := bstep (se 1 (by rfl) ⟨1393685, by rfl⟩ : syracuseStep 1858247 = 2787371) B2787371
theorem B547547 : Blo 546805 547547 := bstep (se 1 (by rfl) ⟨410660, by rfl⟩ : syracuseStep 547547 = 821321) B821321
theorem B91151119 : Blo 546805 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B5266205 : Blo 546805 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B547623 : Blo 546805 547623 := bstep (se 1 (by rfl) ⟨410717, by rfl⟩ : syracuseStep 547623 = 821435) B821435
theorem B547663 : Blo 546805 547663 := bstep (se 1 (by rfl) ⟨410747, by rfl⟩ : syracuseStep 547663 = 821495) B821495
theorem B547679 : Blo 546805 547679 := bstep (se 1 (by rfl) ⟨410759, by rfl⟩ : syracuseStep 547679 = 821519) B821519
theorem B1235807 : Blo 546805 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B547707 : Blo 546805 547707 := bstep (se 1 (by rfl) ⟨410780, by rfl⟩ : syracuseStep 547707 = 821561) B821561
theorem B547759 : Blo 546805 547759 := bstep (se 1 (by rfl) ⟨410819, by rfl⟩ : syracuseStep 547759 = 821639) B821639
theorem B547783 : Blo 546805 547783 := bstep (se 1 (by rfl) ⟨410837, by rfl⟩ : syracuseStep 547783 = 821675) B821675
theorem B547803 : Blo 546805 547803 := bstep (se 1 (by rfl) ⟨410852, by rfl⟩ : syracuseStep 547803 = 821705) B821705
theorem B1235987 : Blo 546805 1235987 := bstep (se 1 (by rfl) ⟨926990, by rfl⟩ : syracuseStep 1235987 = 1853981) B1853981
theorem B547879 : Blo 546805 547879 := bstep (se 1 (by rfl) ⟨410909, by rfl⟩ : syracuseStep 547879 = 821819) B821819
theorem B547919 : Blo 546805 547919 := bstep (se 1 (by rfl) ⟨410939, by rfl⟩ : syracuseStep 547919 = 821879) B821879
theorem B547935 : Blo 546805 547935 := bstep (se 1 (by rfl) ⟨410951, by rfl⟩ : syracuseStep 547935 = 821903) B821903
theorem B547963 : Blo 546805 547963 := bstep (se 1 (by rfl) ⟨410972, by rfl⟩ : syracuseStep 547963 = 821945) B821945
theorem B548015 : Blo 546805 548015 := bstep (se 1 (by rfl) ⟨411011, by rfl⟩ : syracuseStep 548015 = 822023) B822023
theorem B548039 : Blo 546805 548039 := bstep (se 1 (by rfl) ⟨411029, by rfl⟩ : syracuseStep 548039 = 822059) B822059
theorem B548059 : Blo 546805 548059 := bstep (se 1 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 548059 = 822089) B822089
theorem B548135 : Blo 546805 548135 := bstep (se 1 (by rfl) ⟨411101, by rfl⟩ : syracuseStep 548135 = 822203) B822203
theorem B548175 : Blo 546805 548175 := bstep (se 1 (by rfl) ⟨411131, by rfl⟩ : syracuseStep 548175 = 822263) B822263
theorem B548191 : Blo 546805 548191 := bstep (se 1 (by rfl) ⟨411143, by rfl⟩ : syracuseStep 548191 = 822287) B822287
theorem B1236329 : Blo 546805 1236329 := bstep (se 2 (by rfl) ⟨463623, by rfl⟩ : syracuseStep 1236329 = 927247) B927247
theorem B548219 : Blo 546805 548219 := bstep (se 1 (by rfl) ⟨411164, by rfl⟩ : syracuseStep 548219 = 822329) B822329
theorem B548271 : Blo 546805 548271 := bstep (se 1 (by rfl) ⟨411203, by rfl⟩ : syracuseStep 548271 = 822407) B822407
theorem B48717233 : Blo 546805 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B548295 : Blo 546805 548295 := bstep (se 1 (by rfl) ⟨411221, by rfl⟩ : syracuseStep 548295 = 822443) B822443
theorem B548315 : Blo 546805 548315 := bstep (se 1 (by rfl) ⟨411236, by rfl⟩ : syracuseStep 548315 = 822473) B822473
theorem B548391 : Blo 546805 548391 := bstep (se 1 (by rfl) ⟨411293, by rfl⟩ : syracuseStep 548391 = 822587) B822587
theorem B548431 : Blo 546805 548431 := bstep (se 1 (by rfl) ⟨411323, by rfl⟩ : syracuseStep 548431 = 822647) B822647
theorem B548447 : Blo 546805 548447 := bstep (se 1 (by rfl) ⟨411335, by rfl⟩ : syracuseStep 548447 = 822671) B822671
theorem B548475 : Blo 546805 548475 := bstep (se 1 (by rfl) ⟨411356, by rfl⟩ : syracuseStep 548475 = 822713) B822713
theorem B548527 : Blo 546805 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B548551 : Blo 546805 548551 := bstep (se 1 (by rfl) ⟨411413, by rfl⟩ : syracuseStep 548551 = 822827) B822827
theorem B548571 : Blo 546805 548571 := bstep (se 1 (by rfl) ⟨411428, by rfl⟩ : syracuseStep 548571 = 822857) B822857
theorem B548647 : Blo 546805 548647 := bstep (se 1 (by rfl) ⟨411485, by rfl⟩ : syracuseStep 548647 = 822971) B822971
theorem B548687 : Blo 546805 548687 := bstep (se 1 (by rfl) ⟨411515, by rfl⟩ : syracuseStep 548687 = 823031) B823031
theorem B548703 : Blo 546805 548703 := bstep (se 1 (by rfl) ⟨411527, by rfl⟩ : syracuseStep 548703 = 823055) B823055
theorem B2350957 : Blo 546805 2350957 := bstep (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) B881609
theorem B548731 : Blo 546805 548731 := bstep (se 1 (by rfl) ⟨411548, by rfl⟩ : syracuseStep 548731 = 823097) B823097
theorem B1171361 : Blo 546805 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B548783 : Blo 546805 548783 := bstep (se 1 (by rfl) ⟨411587, by rfl⟩ : syracuseStep 548783 = 823175) B823175
theorem B1236923 : Blo 546805 1236923 := bstep (se 1 (by rfl) ⟨927692, by rfl⟩ : syracuseStep 1236923 = 1855385) B1855385
theorem B548807 : Blo 546805 548807 := bstep (se 1 (by rfl) ⟨411605, by rfl⟩ : syracuseStep 548807 = 823211) B823211
theorem B548827 : Blo 546805 548827 := bstep (se 1 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 548827 = 823241) B823241
theorem B548903 : Blo 546805 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B1237049 : Blo 546805 1237049 := bstep (se 2 (by rfl) ⟨463893, by rfl⟩ : syracuseStep 1237049 = 927787) B927787
theorem B548943 : Blo 546805 548943 := bstep (se 1 (by rfl) ⟨411707, by rfl⟩ : syracuseStep 548943 = 823415) B823415
theorem B548959 : Blo 546805 548959 := bstep (se 1 (by rfl) ⟨411719, by rfl⟩ : syracuseStep 548959 = 823439) B823439
theorem B548987 : Blo 546805 548987 := bstep (se 1 (by rfl) ⟨411740, by rfl⟩ : syracuseStep 548987 = 823481) B823481
theorem B549039 : Blo 546805 549039 := bstep (se 1 (by rfl) ⟨411779, by rfl⟩ : syracuseStep 549039 = 823559) B823559
theorem B549063 : Blo 546805 549063 := bstep (se 1 (by rfl) ⟨411797, by rfl⟩ : syracuseStep 549063 = 823595) B823595
theorem B549083 : Blo 546805 549083 := bstep (se 1 (by rfl) ⟨411812, by rfl⟩ : syracuseStep 549083 = 823625) B823625
theorem B876791 : Blo 546805 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B1761527 : Blo 546805 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B549159 : Blo 546805 549159 := bstep (se 1 (by rfl) ⟨411869, by rfl⟩ : syracuseStep 549159 = 823739) B823739
theorem B549199 : Blo 546805 549199 := bstep (se 1 (by rfl) ⟨411899, by rfl⟩ : syracuseStep 549199 = 823799) B823799
theorem B549215 : Blo 546805 549215 := bstep (se 1 (by rfl) ⟨411911, by rfl⟩ : syracuseStep 549215 = 823823) B823823
theorem B549243 : Blo 546805 549243 := bstep (se 1 (by rfl) ⟨411932, by rfl⟩ : syracuseStep 549243 = 823865) B823865
theorem B1237391 : Blo 546805 1237391 := bstep (se 1 (by rfl) ⟨928043, by rfl⟩ : syracuseStep 1237391 = 1856087) B1856087
theorem B549295 : Blo 546805 549295 := bstep (se 1 (by rfl) ⟨411971, by rfl⟩ : syracuseStep 549295 = 823943) B823943
theorem B549319 : Blo 546805 549319 := bstep (se 1 (by rfl) ⟨411989, by rfl⟩ : syracuseStep 549319 = 823979) B823979
theorem B4514251 : Blo 546805 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B549339 : Blo 546805 549339 := bstep (se 1 (by rfl) ⟨412004, by rfl⟩ : syracuseStep 549339 = 824009) B824009
theorem B2089435 : Blo 546805 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem B549415 : Blo 546805 549415 := bstep (se 1 (by rfl) ⟨412061, by rfl⟩ : syracuseStep 549415 = 824123) B824123
theorem B549455 : Blo 546805 549455 := bstep (se 1 (by rfl) ⟨412091, by rfl⟩ : syracuseStep 549455 = 824183) B824183
theorem B549471 : Blo 546805 549471 := bstep (se 1 (by rfl) ⟨412103, by rfl⟩ : syracuseStep 549471 = 824207) B824207
theorem B549499 : Blo 546805 549499 := bstep (se 1 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 549499 = 824249) B824249
theorem B549551 : Blo 546805 549551 := bstep (se 1 (by rfl) ⟨412163, by rfl⟩ : syracuseStep 549551 = 824327) B824327
theorem B549575 : Blo 546805 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B1237715 : Blo 546805 1237715 := bstep (se 1 (by rfl) ⟨928286, by rfl⟩ : syracuseStep 1237715 = 1856573) B1856573
theorem B549595 : Blo 546805 549595 := bstep (se 1 (by rfl) ⟨412196, by rfl⟩ : syracuseStep 549595 = 824393) B824393
theorem B549671 : Blo 546805 549671 := bstep (se 1 (by rfl) ⟨412253, by rfl⟩ : syracuseStep 549671 = 824507) B824507
theorem B549711 : Blo 546805 549711 := bstep (se 1 (by rfl) ⟨412283, by rfl⟩ : syracuseStep 549711 = 824567) B824567
theorem B549727 : Blo 546805 549727 := bstep (se 1 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 549727 = 824591) B824591
theorem B549755 : Blo 546805 549755 := bstep (se 1 (by rfl) ⟨412316, by rfl⟩ : syracuseStep 549755 = 824633) B824633
theorem B615343 : Blo 546805 615343 := bstep (se 1 (by rfl) ⟨461507, by rfl⟩ : syracuseStep 615343 = 923015) B923015
theorem B549807 : Blo 546805 549807 := bstep (se 1 (by rfl) ⟨412355, by rfl⟩ : syracuseStep 549807 = 824711) B824711
theorem B549831 : Blo 546805 549831 := bstep (se 1 (by rfl) ⟨412373, by rfl⟩ : syracuseStep 549831 = 824747) B824747
theorem B549851 : Blo 546805 549851 := bstep (se 1 (by rfl) ⟨412388, by rfl⟩ : syracuseStep 549851 = 824777) B824777
theorem B549927 : Blo 546805 549927 := bstep (se 1 (by rfl) ⟨412445, by rfl⟩ : syracuseStep 549927 = 824891) B824891
theorem B549967 : Blo 546805 549967 := bstep (se 1 (by rfl) ⟨412475, by rfl⟩ : syracuseStep 549967 = 824951) B824951
theorem B549983 : Blo 546805 549983 := bstep (se 1 (by rfl) ⟨412487, by rfl⟩ : syracuseStep 549983 = 824975) B824975
theorem B550011 : Blo 546805 550011 := bstep (se 1 (by rfl) ⟨412508, by rfl⟩ : syracuseStep 550011 = 825017) B825017
theorem B9168025 : Blo 546805 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B550063 : Blo 546805 550063 := bstep (se 1 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 550063 = 825095) B825095
theorem B550087 : Blo 546805 550087 := bstep (se 1 (by rfl) ⟨412565, by rfl⟩ : syracuseStep 550087 = 825131) B825131
theorem B550107 : Blo 546805 550107 := bstep (se 1 (by rfl) ⟨412580, by rfl⟩ : syracuseStep 550107 = 825161) B825161
theorem B550183 : Blo 546805 550183 := bstep (se 1 (by rfl) ⟨412637, by rfl⟩ : syracuseStep 550183 = 825275) B825275
theorem B550223 : Blo 546805 550223 := bstep (se 1 (by rfl) ⟨412667, by rfl⟩ : syracuseStep 550223 = 825335) B825335
theorem B3958105 : Blo 546805 3958105 := bstep (se 2 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 3958105 = 2968579) B2968579
theorem B615775 : Blo 546805 615775 := bstep (se 1 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 615775 = 923663) B923663
theorem B550239 : Blo 546805 550239 := bstep (se 1 (by rfl) ⟨412679, by rfl⟩ : syracuseStep 550239 = 825359) B825359
theorem B550267 : Blo 546805 550267 := bstep (se 1 (by rfl) ⟨412700, by rfl⟩ : syracuseStep 550267 = 825401) B825401
theorem B550319 : Blo 546805 550319 := bstep (se 1 (by rfl) ⟨412739, by rfl⟩ : syracuseStep 550319 = 825479) B825479
theorem B550343 : Blo 546805 550343 := bstep (se 1 (by rfl) ⟨412757, by rfl⟩ : syracuseStep 550343 = 825515) B825515
theorem B550363 : Blo 546805 550363 := bstep (se 1 (by rfl) ⟨412772, by rfl⟩ : syracuseStep 550363 = 825545) B825545
theorem B550439 : Blo 546805 550439 := bstep (se 1 (by rfl) ⟨412829, by rfl⟩ : syracuseStep 550439 = 825659) B825659
theorem B1041977 : Blo 546805 1041977 := bstep (se 2 (by rfl) ⟨390741, by rfl⟩ : syracuseStep 1041977 = 781483) B781483
theorem B550479 : Blo 546805 550479 := bstep (se 1 (by rfl) ⟨412859, by rfl⟩ : syracuseStep 550479 = 825719) B825719
theorem B550495 : Blo 546805 550495 := bstep (se 1 (by rfl) ⟨412871, by rfl⟩ : syracuseStep 550495 = 825743) B825743
theorem B1238651 : Blo 546805 1238651 := bstep (se 1 (by rfl) ⟨928988, by rfl⟩ : syracuseStep 1238651 = 1857977) B1857977
theorem B550523 : Blo 546805 550523 := bstep (se 1 (by rfl) ⟨412892, by rfl⟩ : syracuseStep 550523 = 825785) B825785
theorem B550575 : Blo 546805 550575 := bstep (se 1 (by rfl) ⟨412931, by rfl⟩ : syracuseStep 550575 = 825863) B825863
theorem B2090681 : Blo 546805 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B616135 : Blo 546805 616135 := bstep (se 1 (by rfl) ⟨462101, by rfl⟩ : syracuseStep 616135 = 924203) B924203
theorem B550599 : Blo 546805 550599 := bstep (se 1 (by rfl) ⟨412949, by rfl⟩ : syracuseStep 550599 = 825899) B825899
theorem B2221777 : Blo 546805 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B2090711 : Blo 546805 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B550619 : Blo 546805 550619 := bstep (se 1 (by rfl) ⟨412964, by rfl⟩ : syracuseStep 550619 = 825929) B825929
theorem B780025 : Blo 546805 780025 := bstep (se 2 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 780025 = 585019) B585019
theorem B1238777 : Blo 546805 1238777 := bstep (se 2 (by rfl) ⟨464541, by rfl⟩ : syracuseStep 1238777 = 929083) B929083
theorem B550695 : Blo 546805 550695 := bstep (se 1 (by rfl) ⟨413021, by rfl⟩ : syracuseStep 550695 = 826043) B826043
theorem B2778947 : Blo 546805 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B550735 : Blo 546805 550735 := bstep (se 1 (by rfl) ⟨413051, by rfl⟩ : syracuseStep 550735 = 826103) B826103
theorem B1763167 : Blo 546805 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B550751 : Blo 546805 550751 := bstep (se 1 (by rfl) ⟨413063, by rfl⟩ : syracuseStep 550751 = 826127) B826127
theorem B550779 : Blo 546805 550779 := bstep (se 1 (by rfl) ⟨413084, by rfl⟩ : syracuseStep 550779 = 826169) B826169
theorem B4679633 : Blo 546805 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B1239047 : Blo 546805 1239047 := bstep (se 1 (by rfl) ⟨929285, by rfl⟩ : syracuseStep 1239047 = 1858571) B1858571
theorem B1173523 : Blo 546805 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1239119 : Blo 546805 1239119 := bstep (se 1 (by rfl) ⟨929339, by rfl⟩ : syracuseStep 1239119 = 1858679) B1858679
theorem B7039133 : Blo 546805 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B1173865 : Blo 546805 1173865 := bstep (se 2 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 1173865 = 880399) B880399
theorem B616999 : Blo 546805 616999 := bstep (se 1 (by rfl) ⟨462749, by rfl⟩ : syracuseStep 616999 = 925499) B925499
theorem B1043579 : Blo 546805 1043579 := bstep (se 1 (by rfl) ⟨782684, by rfl⟩ : syracuseStep 1043579 = 1565369) B1565369
theorem B5074319 : Blo 546805 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B9399725 : Blo 546805 9399725 := bstep (se 3 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 9399725 = 3524897) B3524897
theorem B8449601 : Blo 546805 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B1044065 : Blo 546805 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B2813579 : Blo 546805 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B1175239 : Blo 546805 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B4157243 : Blo 546805 4157243 := bstep (se 1 (by rfl) ⟨3117932, by rfl⟩ : syracuseStep 4157243 = 6235865) B6235865
theorem B1044407 : Blo 546805 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B6352825 : Blo 546805 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B1404985 : Blo 546805 1404985 := bstep (se 2 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 1404985 = 1053739) B1053739
theorem B618619 : Blo 546805 618619 := bstep (se 1 (by rfl) ⟨463964, by rfl⟩ : syracuseStep 618619 = 927929) B927929
theorem B2257091 : Blo 546805 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B1044809 : Blo 546805 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B619087 : Blo 546805 619087 := bstep (se 1 (by rfl) ⟨464315, by rfl⟩ : syracuseStep 619087 = 928631) B928631
theorem B7893773 : Blo 546805 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B2782025 : Blo 546805 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B11891609 : Blo 546805 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B7009199 : Blo 546805 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B1110971 : Blo 546805 1110971 := bstep (se 1 (by rfl) ⟨833228, by rfl⟩ : syracuseStep 1110971 = 1666457) B1666457
theorem B619483 : Blo 546805 619483 := bstep (se 1 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 619483 = 929225) B929225
theorem B2814977 : Blo 546805 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1045523 : Blo 546805 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B1045561 : Blo 546805 1045561 := bstep (se 2 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 1045561 = 784171) B784171
theorem B3568835 : Blo 546805 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B7533971 : Blo 546805 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B10582073 : Blo 546805 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B587855 : Blo 546805 587855 := bstep (se 1 (by rfl) ⟨440891, by rfl⟩ : syracuseStep 587855 = 881783) B881783
theorem B2783321 : Blo 546805 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B4225517 : Blo 546805 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B4749857 : Blo 546805 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1407611 : Blo 546805 1407611 := bstep (se 1 (by rfl) ⟨1055708, by rfl⟩ : syracuseStep 1407611 = 2111417) B2111417
theorem B1407851 : Blo 546805 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B1113679 : Blo 546805 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B20086501 : Blo 546805 20086501 := bstep (se 4 (by rfl) ⟨1883109, by rfl⟩ : syracuseStep 20086501 = 3766219) B3766219
theorem B22610117 : Blo 546805 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B557423 : Blo 546805 557423 := bstep (se 1 (by rfl) ⟨418067, by rfl⟩ : syracuseStep 557423 = 836135) B836135
theorem B2785913 : Blo 546805 2785913 := bstep (se 2 (by rfl) ⟨1044717, by rfl⟩ : syracuseStep 2785913 = 2089435) B2089435
theorem B820457 : Blo 546805 820457 := bstep (se 2 (by rfl) ⟨307671, by rfl⟩ : syracuseStep 820457 = 615343) B615343
theorem B820511 : Blo 546805 820511 := bstep (se 1 (by rfl) ⟨615383, by rfl⟩ : syracuseStep 820511 = 1230767) B1230767
theorem B15795607 : Blo 546805 15795607 := bstep (se 1 (by rfl) ⟨11846705, by rfl⟩ : syracuseStep 15795607 = 23693411) B23693411
theorem B820679 : Blo 546805 820679 := bstep (se 1 (by rfl) ⟨615509, by rfl⟩ : syracuseStep 820679 = 1231019) B1231019
theorem B12224033 : Blo 546805 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B656959 : Blo 546805 656959 := bstep (se 1 (by rfl) ⟨492719, by rfl⟩ : syracuseStep 656959 = 985439) B985439
theorem B5277473 : Blo 546805 5277473 := bstep (se 2 (by rfl) ⟨1979052, by rfl⟩ : syracuseStep 5277473 = 3958105) B3958105
theorem B821033 : Blo 546805 821033 := bstep (se 2 (by rfl) ⟨307887, by rfl⟩ : syracuseStep 821033 = 615775) B615775
theorem B821039 : Blo 546805 821039 := bstep (se 1 (by rfl) ⟨615779, by rfl⟩ : syracuseStep 821039 = 1231559) B1231559
theorem B821513 : Blo 546805 821513 := bstep (se 2 (by rfl) ⟨308067, by rfl⟩ : syracuseStep 821513 = 616135) B616135
theorem B821615 : Blo 546805 821615 := bstep (se 1 (by rfl) ⟨616211, by rfl⟩ : syracuseStep 821615 = 1232423) B1232423
theorem B2787695 : Blo 546805 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B1411511 : Blo 546805 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B821831 : Blo 546805 821831 := bstep (se 1 (by rfl) ⟨616373, by rfl⟩ : syracuseStep 821831 = 1232747) B1232747
theorem B821867 : Blo 546805 821867 := bstep (se 1 (by rfl) ⟨616400, by rfl⟩ : syracuseStep 821867 = 1232801) B1232801
theorem B822095 : Blo 546805 822095 := bstep (se 1 (by rfl) ⟨616571, by rfl⟩ : syracuseStep 822095 = 1233143) B1233143
theorem B822491 : Blo 546805 822491 := bstep (se 1 (by rfl) ⟨616868, by rfl⟩ : syracuseStep 822491 = 1233737) B1233737
theorem B822665 : Blo 546805 822665 := bstep (se 2 (by rfl) ⟨308499, by rfl⟩ : syracuseStep 822665 = 616999) B616999
theorem B1052255 : Blo 546805 1052255 := bstep (se 1 (by rfl) ⟨789191, by rfl⟩ : syracuseStep 1052255 = 1578383) B1578383
theorem B823019 : Blo 546805 823019 := bstep (se 1 (by rfl) ⟨617264, by rfl⟩ : syracuseStep 823019 = 1234529) B1234529
theorem B823247 : Blo 546805 823247 := bstep (se 1 (by rfl) ⟨617435, by rfl⟩ : syracuseStep 823247 = 1234871) B1234871
theorem B823643 : Blo 546805 823643 := bstep (se 1 (by rfl) ⟨617732, by rfl⟩ : syracuseStep 823643 = 1235465) B1235465
theorem B3510803 : Blo 546805 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B823871 : Blo 546805 823871 := bstep (se 1 (by rfl) ⟨617903, by rfl⟩ : syracuseStep 823871 = 1235807) B1235807
theorem B823991 : Blo 546805 823991 := bstep (se 1 (by rfl) ⟨617993, by rfl⟩ : syracuseStep 823991 = 1235987) B1235987
theorem B824219 : Blo 546805 824219 := bstep (se 1 (by rfl) ⟨618164, by rfl⟩ : syracuseStep 824219 = 1236329) B1236329
theorem B32478155 : Blo 546805 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B824615 : Blo 546805 824615 := bstep (se 1 (by rfl) ⟨618461, by rfl⟩ : syracuseStep 824615 = 1236923) B1236923
theorem B824699 : Blo 546805 824699 := bstep (se 1 (by rfl) ⟨618524, by rfl⟩ : syracuseStep 824699 = 1237049) B1237049
theorem B1873313 : Blo 546805 1873313 := bstep (se 2 (by rfl) ⟨702492, by rfl⟩ : syracuseStep 1873313 = 1404985) B1404985
theorem B1054201 : Blo 546805 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B824825 : Blo 546805 824825 := bstep (se 2 (by rfl) ⟨309309, by rfl⟩ : syracuseStep 824825 = 618619) B618619
theorem B923231 : Blo 546805 923231 := bstep (se 1 (by rfl) ⟨692423, by rfl⟩ : syracuseStep 923231 = 1384847) B1384847
theorem B824927 : Blo 546805 824927 := bstep (se 1 (by rfl) ⟨618695, by rfl⟩ : syracuseStep 824927 = 1237391) B1237391
theorem B5641913 : Blo 546805 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B923447 : Blo 546805 923447 := bstep (se 1 (by rfl) ⟨692585, by rfl⟩ : syracuseStep 923447 = 1385171) B1385171
theorem B825143 : Blo 546805 825143 := bstep (se 1 (by rfl) ⟨618857, by rfl⟩ : syracuseStep 825143 = 1237715) B1237715
theorem B825449 : Blo 546805 825449 := bstep (se 2 (by rfl) ⟨309543, by rfl⟩ : syracuseStep 825449 = 619087) B619087
theorem B694651 : Blo 546805 694651 := bstep (se 1 (by rfl) ⟨520988, by rfl⟩ : syracuseStep 694651 = 1041977) B1041977
theorem B825767 : Blo 546805 825767 := bstep (se 1 (by rfl) ⟨619325, by rfl⟩ : syracuseStep 825767 = 1238651) B1238651
theorem B1776055 : Blo 546805 1776055 := bstep (se 1 (by rfl) ⟨1332041, by rfl⟩ : syracuseStep 1776055 = 2664083) B2664083
theorem B825851 : Blo 546805 825851 := bstep (se 1 (by rfl) ⟨619388, by rfl⟩ : syracuseStep 825851 = 1238777) B1238777
theorem B924223 : Blo 546805 924223 := bstep (se 1 (by rfl) ⟨693167, by rfl⟩ : syracuseStep 924223 = 1386335) B1386335
theorem B1317455 : Blo 546805 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B825977 : Blo 546805 825977 := bstep (se 2 (by rfl) ⟨309741, by rfl⟩ : syracuseStep 825977 = 619483) B619483
theorem B3119755 : Blo 546805 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B826031 : Blo 546805 826031 := bstep (se 1 (by rfl) ⟨619523, by rfl⟩ : syracuseStep 826031 = 1239047) B1239047
theorem B826079 : Blo 546805 826079 := bstep (se 1 (by rfl) ⟨619559, by rfl⟩ : syracuseStep 826079 = 1239119) B1239119
theorem B1973011 : Blo 546805 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B4692755 : Blo 546805 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B924905 : Blo 546805 924905 := bstep (se 2 (by rfl) ⟨346839, by rfl⟩ : syracuseStep 924905 = 693679) B693679
theorem B2628895 : Blo 546805 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B924959 : Blo 546805 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B695719 : Blo 546805 695719 := bstep (se 1 (by rfl) ⟨521789, by rfl⟩ : syracuseStep 695719 = 1043579) B1043579
theorem B3382879 : Blo 546805 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B6266483 : Blo 546805 6266483 := bstep (se 1 (by rfl) ⟨4699862, by rfl⟩ : syracuseStep 6266483 = 9399725) B9399725
theorem B696043 : Blo 546805 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B1384199 : Blo 546805 1384199 := bstep (se 1 (by rfl) ⟨1038149, by rfl⟩ : syracuseStep 1384199 = 2076299) B2076299
theorem B1875719 : Blo 546805 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B1384249 : Blo 546805 1384249 := bstep (se 2 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 1384249 = 1038187) B1038187
theorem B892729 : Blo 546805 892729 := bstep (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) B669547
theorem B696271 : Blo 546805 696271 := bstep (se 1 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 696271 = 1044407) B1044407
theorem B1384553 : Blo 546805 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B696539 : Blo 546805 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B1385039 : Blo 546805 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B926329 : Blo 546805 926329 := bstep (se 2 (by rfl) ⟨347373, by rfl⟩ : syracuseStep 926329 = 694747) B694747
theorem B1876651 : Blo 546805 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B926383 : Blo 546805 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B697015 : Blo 546805 697015 := bstep (se 1 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 697015 = 1045523) B1045523
theorem B3810007 : Blo 546805 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B42738445 : Blo 546805 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B5022647 : Blo 546805 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B6267941 : Blo 546805 6267941 := bstep (se 4 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 6267941 = 1175239) B1175239
theorem B1385687 : Blo 546805 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B2630951 : Blo 546805 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B7054715 : Blo 546805 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B2336161 : Blo 546805 2336161 := bstep (se 2 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 2336161 = 1752121) B1752121
theorem B1320761 : Blo 546805 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B4990825 : Blo 546805 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B12167117 : Blo 546805 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B2500559 : Blo 546805 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B1484905 : Blo 546805 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B2369801 : Blo 546805 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B26782001 : Blo 546805 26782001 := bstep (se 2 (by rfl) ⟨10043250, by rfl⟩ : syracuseStep 26782001 = 20086501) B20086501
theorem B928091 : Blo 546805 928091 := bstep (se 1 (by rfl) ⟨696068, by rfl⟩ : syracuseStep 928091 = 1392137) B1392137
theorem B928111 : Blo 546805 928111 := bstep (se 1 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 928111 = 1392167) B1392167
theorem B11250049 : Blo 546805 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B3123629 : Blo 546805 3123629 := bstep (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) B1171361
theorem B1387003 : Blo 546805 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B928327 : Blo 546805 928327 := bstep (se 1 (by rfl) ⟨696245, by rfl⟩ : syracuseStep 928327 = 1392491) B1392491
theorem B1387115 : Blo 546805 1387115 := bstep (se 1 (by rfl) ⟨1040336, by rfl⟩ : syracuseStep 1387115 = 2080673) B2080673
theorem B1845935 : Blo 546805 1845935 := bstep (se 1 (by rfl) ⟨1384451, by rfl⟩ : syracuseStep 1845935 = 2768903) B2768903
theorem B1846259 : Blo 546805 1846259 := bstep (se 1 (by rfl) ⟨1384694, by rfl⟩ : syracuseStep 1846259 = 2769389) B2769389
theorem B928759 : Blo 546805 928759 := bstep (se 1 (by rfl) ⟨696569, by rfl⟩ : syracuseStep 928759 = 1393139) B1393139
theorem B1387763 : Blo 546805 1387763 := bstep (se 1 (by rfl) ⟨1040822, by rfl⟩ : syracuseStep 1387763 = 2081645) B2081645
theorem B929063 : Blo 546805 929063 := bstep (se 1 (by rfl) ⟨696797, by rfl⟩ : syracuseStep 929063 = 1393595) B1393595
theorem B2338109 : Blo 546805 2338109 := bstep (se 3 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 2338109 = 876791) B876791
theorem B1387975 : Blo 546805 1387975 := bstep (se 1 (by rfl) ⟨1040981, by rfl⟩ : syracuseStep 1387975 = 2081963) B2081963
theorem B1846799 : Blo 546805 1846799 := bstep (se 1 (by rfl) ⟨1385099, by rfl⟩ : syracuseStep 1846799 = 2770199) B2770199
theorem B1289785 : Blo 546805 1289785 := bstep (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) B967339
theorem B2502407 : Blo 546805 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B2338571 : Blo 546805 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B1486721 : Blo 546805 1486721 := bstep (se 2 (by rfl) ⟨557520, by rfl⟩ : syracuseStep 1486721 = 1115041) B1115041
theorem B1486799 : Blo 546805 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B1323337 : Blo 546805 1323337 := bstep (se 2 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 1323337 = 992503) B992503
theorem B2077103 : Blo 546805 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B1847879 : Blo 546805 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1978951 : Blo 546805 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B2339543 : Blo 546805 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B2962369 : Blo 546805 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B1848311 : Blo 546805 1848311 := bstep (se 1 (by rfl) ⟨1386233, by rfl⟩ : syracuseStep 1848311 = 2772467) B2772467
theorem B1389707 : Blo 546805 1389707 := bstep (se 1 (by rfl) ⟨1042280, by rfl⟩ : syracuseStep 1389707 = 2084561) B2084561
theorem B1389919 : Blo 546805 1389919 := bstep (se 1 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 1389919 = 2084879) B2084879
theorem B2078075 : Blo 546805 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B6600503 : Blo 546805 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B1849175 : Blo 546805 1849175 := bstep (se 1 (by rfl) ⟨1386881, by rfl⟩ : syracuseStep 1849175 = 2773763) B2773763
theorem B1488797 : Blo 546805 1488797 := bstep (se 3 (by rfl) ⟨279149, by rfl⟩ : syracuseStep 1488797 = 558299) B558299
theorem B1980551 : Blo 546805 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B670063 : Blo 546805 670063 := bstep (se 1 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 670063 = 1005095) B1005095
theorem B834043 : Blo 546805 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B5913283 : Blo 546805 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B3128003 : Blo 546805 3128003 := bstep (se 1 (by rfl) ⟨2346002, by rfl⟩ : syracuseStep 3128003 = 4692005) B4692005
theorem B1391327 : Blo 546805 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B1850255 : Blo 546805 1850255 := bstep (se 1 (by rfl) ⟨1387691, by rfl⟩ : syracuseStep 1850255 = 2775383) B2775383
theorem B3521465 : Blo 546805 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B3849445 : Blo 546805 3849445 := bstep (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) B721771
theorem B4767113 : Blo 546805 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B2080187 : Blo 546805 2080187 := bstep (se 1 (by rfl) ⟨1560140, by rfl⟩ : syracuseStep 2080187 = 3120281) B3120281
theorem B2342483 : Blo 546805 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B835307 : Blo 546805 835307 := bstep (se 1 (by rfl) ⟨626480, by rfl⟩ : syracuseStep 835307 = 1252961) B1252961
theorem B8470433 : Blo 546805 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B1851497 : Blo 546805 1851497 := bstep (se 2 (by rfl) ⟨694311, by rfl⟩ : syracuseStep 1851497 = 1388623) B1388623
theorem B705119 : Blo 546805 705119 := bstep (se 1 (by rfl) ⟨528839, by rfl⟩ : syracuseStep 705119 = 1057679) B1057679
theorem B5259977 : Blo 546805 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B7914185 : Blo 546805 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B21021443 : Blo 546805 21021443 := bstep (se 1 (by rfl) ⟨15766082, by rfl⟩ : syracuseStep 21021443 = 31532165) B31532165
theorem B1852361 : Blo 546805 1852361 := bstep (se 2 (by rfl) ⟨694635, by rfl⟩ : syracuseStep 1852361 = 1389271) B1389271
theorem B1393787 : Blo 546805 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B1754237 : Blo 546805 1754237 := bstep (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) B657839
theorem B1393807 : Blo 546805 1393807 := bstep (se 1 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 1393807 = 2090711) B2090711
theorem B1852631 : Blo 546805 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B1557737 : Blo 546805 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B1394081 : Blo 546805 1394081 := bstep (se 2 (by rfl) ⟨522780, by rfl⟩ : syracuseStep 1394081 = 1045561) B1045561
theorem B7914995 : Blo 546805 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B1230497 : Blo 546805 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B17778365 : Blo 546805 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B1230857 : Blo 546805 1230857 := bstep (se 2 (by rfl) ⟨461571, by rfl⟩ : syracuseStep 1230857 = 923143) B923143
theorem B1231271 : Blo 546805 1231271 := bstep (se 1 (by rfl) ⟨923453, by rfl⟩ : syracuseStep 1231271 = 1846907) B1846907
theorem B1231379 : Blo 546805 1231379 := bstep (se 1 (by rfl) ⟨923534, by rfl⟩ : syracuseStep 1231379 = 1847069) B1847069
theorem B2771495 : Blo 546805 2771495 := bstep (se 1 (by rfl) ⟨2078621, by rfl⟩ : syracuseStep 2771495 = 4157243) B4157243
theorem B2083391 : Blo 546805 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B1231433 : Blo 546805 1231433 := bstep (se 2 (by rfl) ⟨461787, by rfl⟩ : syracuseStep 1231433 = 923575) B923575
theorem B2083603 : Blo 546805 2083603 := bstep (se 1 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 2083603 = 3125405) B3125405
theorem B1231847 : Blo 546805 1231847 := bstep (se 1 (by rfl) ⟨923885, by rfl⟩ : syracuseStep 1231847 = 1847771) B1847771
theorem B5262515 : Blo 546805 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B1854683 : Blo 546805 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B4672799 : Blo 546805 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B740647 : Blo 546805 740647 := bstep (se 1 (by rfl) ⟨555485, by rfl⟩ : syracuseStep 740647 = 1110971) B1110971
theorem B1232225 : Blo 546805 1232225 := bstep (se 2 (by rfl) ⟨462084, by rfl⟩ : syracuseStep 1232225 = 924169) B924169
theorem B1232315 : Blo 546805 1232315 := bstep (se 1 (by rfl) ⟨924236, by rfl⟩ : syracuseStep 1232315 = 1848473) B1848473
theorem B2379223 : Blo 546805 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1232441 : Blo 546805 1232441 := bstep (se 2 (by rfl) ⟨462165, by rfl⟩ : syracuseStep 1232441 = 924331) B924331
theorem B2674291 : Blo 546805 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B4214585 : Blo 546805 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B1757209 : Blo 546805 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B1855547 : Blo 546805 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B22532269 : Blo 546805 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B1233107 : Blo 546805 1233107 := bstep (se 1 (by rfl) ⟨924830, by rfl⟩ : syracuseStep 1233107 = 1849661) B1849661
theorem B1233161 : Blo 546805 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B1855817 : Blo 546805 1855817 := bstep (se 2 (by rfl) ⟨695931, by rfl⟩ : syracuseStep 1855817 = 1391863) B1391863
theorem B3166571 : Blo 546805 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B938407 : Blo 546805 938407 := bstep (se 1 (by rfl) ⟨703805, by rfl⟩ : syracuseStep 938407 = 1407611) B1407611
theorem B1233377 : Blo 546805 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B938567 : Blo 546805 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B2773601 : Blo 546805 2773601 := bstep (se 2 (by rfl) ⟨1040100, by rfl⟩ : syracuseStep 2773601 = 2080201) B2080201
theorem B2085547 : Blo 546805 2085547 := bstep (se 1 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 2085547 = 3128321) B3128321
theorem B1233683 : Blo 546805 1233683 := bstep (se 1 (by rfl) ⟨925262, by rfl⟩ : syracuseStep 1233683 = 1850525) B1850525
theorem B2085851 : Blo 546805 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B1234043 : Blo 546805 1234043 := bstep (se 1 (by rfl) ⟨925532, by rfl⟩ : syracuseStep 1234043 = 1851065) B1851065
theorem B3134609 : Blo 546805 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B2774249 : Blo 546805 2774249 := bstep (se 2 (by rfl) ⟨1040343, by rfl⟩ : syracuseStep 2774249 = 2080687) B2080687
theorem B1758451 : Blo 546805 1758451 := bstep (se 1 (by rfl) ⟨1318838, by rfl⟩ : syracuseStep 1758451 = 2637677) B2637677
theorem B1234169 : Blo 546805 1234169 := bstep (se 2 (by rfl) ⟨462813, by rfl⟩ : syracuseStep 1234169 = 925627) B925627
theorem B1758503 : Blo 546805 1758503 := bstep (se 1 (by rfl) ⟨1318877, by rfl⟩ : syracuseStep 1758503 = 2637755) B2637755
theorem B1234313 : Blo 546805 1234313 := bstep (se 2 (by rfl) ⟨462867, by rfl⟩ : syracuseStep 1234313 = 925735) B925735
theorem B2774411 : Blo 546805 2774411 := bstep (se 1 (by rfl) ⟨2080808, by rfl⟩ : syracuseStep 2774411 = 4161617) B4161617
theorem B2971019 : Blo 546805 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B1234439 : Blo 546805 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B4675259 : Blo 546805 4675259 := bstep (se 1 (by rfl) ⟨3506444, by rfl⟩ : syracuseStep 4675259 = 7012889) B7012889
theorem B1234619 : Blo 546805 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B1234745 : Blo 546805 1234745 := bstep (se 2 (by rfl) ⟨463029, by rfl⟩ : syracuseStep 1234745 = 926059) B926059
theorem B6019001 : Blo 546805 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B547103 : Blo 546805 547103 := bstep (se 1 (by rfl) ⟨410327, by rfl⟩ : syracuseStep 547103 = 820655) B820655
theorem B547163 : Blo 546805 547163 := bstep (se 1 (by rfl) ⟨410372, by rfl⟩ : syracuseStep 547163 = 820745) B820745
theorem B547183 : Blo 546805 547183 := bstep (se 1 (by rfl) ⟨410387, by rfl⟩ : syracuseStep 547183 = 820775) B820775
theorem B2087279 : Blo 546805 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B547239 : Blo 546805 547239 := bstep (se 1 (by rfl) ⟨410429, by rfl⟩ : syracuseStep 547239 = 820859) B820859
theorem B1235375 : Blo 546805 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B1235411 : Blo 546805 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B547323 : Blo 546805 547323 := bstep (se 1 (by rfl) ⟨410492, by rfl⟩ : syracuseStep 547323 = 820985) B820985
theorem B547391 : Blo 546805 547391 := bstep (se 1 (by rfl) ⟨410543, by rfl⟩ : syracuseStep 547391 = 821087) B821087
theorem B1235519 : Blo 546805 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B547399 : Blo 546805 547399 := bstep (se 1 (by rfl) ⟨410549, by rfl⟩ : syracuseStep 547399 = 821099) B821099
theorem B1235627 : Blo 546805 1235627 := bstep (se 1 (by rfl) ⟨926720, by rfl⟩ : syracuseStep 1235627 = 1853441) B1853441
theorem B547551 : Blo 546805 547551 := bstep (se 1 (by rfl) ⟨410663, by rfl⟩ : syracuseStep 547551 = 821327) B821327
theorem B547631 : Blo 546805 547631 := bstep (se 1 (by rfl) ⟨410723, by rfl⟩ : syracuseStep 547631 = 821447) B821447
theorem B1760143 : Blo 546805 1760143 := bstep (se 1 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 1760143 = 2640215) B2640215
theorem B547739 : Blo 546805 547739 := bstep (se 1 (by rfl) ⟨410804, by rfl⟩ : syracuseStep 547739 = 821609) B821609
theorem B547791 : Blo 546805 547791 := bstep (se 1 (by rfl) ⟨410843, by rfl⟩ : syracuseStep 547791 = 821687) B821687
theorem B547815 : Blo 546805 547815 := bstep (se 1 (by rfl) ⟨410861, by rfl⟩ : syracuseStep 547815 = 821723) B821723
theorem B5069873 : Blo 546805 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1236167 : Blo 546805 1236167 := bstep (se 1 (by rfl) ⟨927125, by rfl⟩ : syracuseStep 1236167 = 1854251) B1854251
theorem B548127 : Blo 546805 548127 := bstep (se 1 (by rfl) ⟨411095, by rfl⟩ : syracuseStep 548127 = 822191) B822191
theorem B548187 : Blo 546805 548187 := bstep (se 1 (by rfl) ⟨411140, by rfl⟩ : syracuseStep 548187 = 822281) B822281
theorem B548207 : Blo 546805 548207 := bstep (se 1 (by rfl) ⟨411155, by rfl⟩ : syracuseStep 548207 = 822311) B822311
theorem B1236347 : Blo 546805 1236347 := bstep (se 1 (by rfl) ⟨927260, by rfl⟩ : syracuseStep 1236347 = 1854521) B1854521
theorem B548263 : Blo 546805 548263 := bstep (se 1 (by rfl) ⟨411197, by rfl⟩ : syracuseStep 548263 = 822395) B822395
theorem B1236473 : Blo 546805 1236473 := bstep (se 2 (by rfl) ⟨463677, by rfl⟩ : syracuseStep 1236473 = 927355) B927355
theorem B548347 : Blo 546805 548347 := bstep (se 1 (by rfl) ⟨411260, by rfl⟩ : syracuseStep 548347 = 822521) B822521
theorem B2088463 : Blo 546805 2088463 := bstep (se 1 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 2088463 = 3132695) B3132695
theorem B548415 : Blo 546805 548415 := bstep (se 1 (by rfl) ⟨411311, by rfl⟩ : syracuseStep 548415 = 822623) B822623
theorem B548423 : Blo 546805 548423 := bstep (se 1 (by rfl) ⟨411317, by rfl⟩ : syracuseStep 548423 = 822635) B822635
theorem B1236563 : Blo 546805 1236563 := bstep (se 1 (by rfl) ⟨927422, by rfl⟩ : syracuseStep 1236563 = 1854845) B1854845
theorem B11296351 : Blo 546805 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B10542707 : Blo 546805 10542707 := bstep (se 1 (by rfl) ⟨7907030, by rfl⟩ : syracuseStep 10542707 = 15814061) B15814061
theorem B1040033 : Blo 546805 1040033 := bstep (se 2 (by rfl) ⟨390012, by rfl⟩ : syracuseStep 1040033 = 780025) B780025
theorem B548575 : Blo 546805 548575 := bstep (se 1 (by rfl) ⟨411431, by rfl⟩ : syracuseStep 548575 = 822863) B822863
theorem B1171207 : Blo 546805 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B1236743 : Blo 546805 1236743 := bstep (se 1 (by rfl) ⟨927557, by rfl⟩ : syracuseStep 1236743 = 1855115) B1855115
theorem B5005097 : Blo 546805 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B2350889 : Blo 546805 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B548655 : Blo 546805 548655 := bstep (se 1 (by rfl) ⟨411491, by rfl⟩ : syracuseStep 548655 = 822983) B822983
theorem B548763 : Blo 546805 548763 := bstep (se 1 (by rfl) ⟨411572, by rfl⟩ : syracuseStep 548763 = 823145) B823145
theorem B12672931 : Blo 546805 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B548815 : Blo 546805 548815 := bstep (se 1 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 548815 = 823223) B823223
theorem B548839 : Blo 546805 548839 := bstep (se 1 (by rfl) ⟨411629, by rfl⟩ : syracuseStep 548839 = 823259) B823259
theorem B1564697 : Blo 546805 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B549151 : Blo 546805 549151 := bstep (se 1 (by rfl) ⟨411863, by rfl⟩ : syracuseStep 549151 = 823727) B823727
theorem B549211 : Blo 546805 549211 := bstep (se 1 (by rfl) ⟨411908, by rfl⟩ : syracuseStep 549211 = 823817) B823817
theorem B1237355 : Blo 546805 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B549231 : Blo 546805 549231 := bstep (se 1 (by rfl) ⟨411923, by rfl⟩ : syracuseStep 549231 = 823847) B823847
theorem B778663 : Blo 546805 778663 := bstep (se 1 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 778663 = 1167995) B1167995
theorem B549287 : Blo 546805 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B1565153 : Blo 546805 1565153 := bstep (se 2 (by rfl) ⟨586932, by rfl⟩ : syracuseStep 1565153 = 1173865) B1173865
theorem B549371 : Blo 546805 549371 := bstep (se 1 (by rfl) ⟨412028, by rfl⟩ : syracuseStep 549371 = 824057) B824057
theorem B1237499 : Blo 546805 1237499 := bstep (se 1 (by rfl) ⟨928124, by rfl⟩ : syracuseStep 1237499 = 1856249) B1856249
theorem B2777651 : Blo 546805 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B549439 : Blo 546805 549439 := bstep (se 1 (by rfl) ⟨412079, by rfl⟩ : syracuseStep 549439 = 824159) B824159
theorem B549447 : Blo 546805 549447 := bstep (se 1 (by rfl) ⟨412085, by rfl⟩ : syracuseStep 549447 = 824171) B824171
theorem B1237625 : Blo 546805 1237625 := bstep (se 2 (by rfl) ⟨464109, by rfl⟩ : syracuseStep 1237625 = 928219) B928219
theorem B1237679 : Blo 546805 1237679 := bstep (se 1 (by rfl) ⟨928259, by rfl⟩ : syracuseStep 1237679 = 1856519) B1856519
theorem B10019537 : Blo 546805 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B549599 : Blo 546805 549599 := bstep (se 1 (by rfl) ⟨412199, by rfl⟩ : syracuseStep 549599 = 824399) B824399
theorem B1237751 : Blo 546805 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B2351915 : Blo 546805 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B549679 : Blo 546805 549679 := bstep (se 1 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 549679 = 824519) B824519
theorem B549787 : Blo 546805 549787 := bstep (se 1 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 549787 = 824681) B824681
theorem B877483 : Blo 546805 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B1237931 : Blo 546805 1237931 := bstep (se 1 (by rfl) ⟨928448, by rfl⟩ : syracuseStep 1237931 = 1856897) B1856897
theorem B549839 : Blo 546805 549839 := bstep (se 1 (by rfl) ⟨412379, by rfl⟩ : syracuseStep 549839 = 824759) B824759
theorem B549863 : Blo 546805 549863 := bstep (se 1 (by rfl) ⟨412397, by rfl⟩ : syracuseStep 549863 = 824795) B824795
theorem B550175 : Blo 546805 550175 := bstep (se 1 (by rfl) ⟨412631, by rfl⟩ : syracuseStep 550175 = 825263) B825263
theorem B550235 : Blo 546805 550235 := bstep (se 1 (by rfl) ⟨412676, by rfl⟩ : syracuseStep 550235 = 825353) B825353
theorem B550255 : Blo 546805 550255 := bstep (se 1 (by rfl) ⟨412691, by rfl⟩ : syracuseStep 550255 = 825383) B825383
theorem B615847 : Blo 546805 615847 := bstep (se 1 (by rfl) ⟨461885, by rfl⟩ : syracuseStep 615847 = 923771) B923771
theorem B550311 : Blo 546805 550311 := bstep (se 1 (by rfl) ⟨412733, by rfl⟩ : syracuseStep 550311 = 825467) B825467
theorem B4154813 : Blo 546805 4154813 := bstep (se 3 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 4154813 = 1558055) B1558055
theorem B1238471 : Blo 546805 1238471 := bstep (se 1 (by rfl) ⟨928853, by rfl⟩ : syracuseStep 1238471 = 1857707) B1857707
theorem B550395 : Blo 546805 550395 := bstep (se 1 (by rfl) ⟨412796, by rfl⟩ : syracuseStep 550395 = 825593) B825593
theorem B550463 : Blo 546805 550463 := bstep (se 1 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 550463 = 825695) B825695
theorem B550471 : Blo 546805 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B550623 : Blo 546805 550623 := bstep (se 1 (by rfl) ⟨412967, by rfl⟩ : syracuseStep 550623 = 825935) B825935
theorem B1238831 : Blo 546805 1238831 := bstep (se 1 (by rfl) ⟨929123, by rfl⟩ : syracuseStep 1238831 = 1858247) B1858247
theorem B550703 : Blo 546805 550703 := bstep (se 1 (by rfl) ⟨413027, by rfl⟩ : syracuseStep 550703 = 826055) B826055
theorem B616423 : Blo 546805 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B2779271 : Blo 546805 2779271 := bstep (se 1 (by rfl) ⟨2084453, by rfl⟩ : syracuseStep 2779271 = 4168907) B4168907
theorem B23816429 : Blo 546805 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B1174351 : Blo 546805 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1567613 : Blo 546805 1567613 := bstep (se 3 (by rfl) ⟨293927, by rfl⟩ : syracuseStep 1567613 = 587855) B587855
theorem B879835 : Blo 546805 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B1338587 : Blo 546805 1338587 := bstep (se 1 (by rfl) ⟨1003940, by rfl⟩ : syracuseStep 1338587 = 2007881) B2007881
theorem B618079 : Blo 546805 618079 := bstep (se 1 (by rfl) ⟨463559, by rfl⟩ : syracuseStep 618079 = 927119) B927119
theorem B881327 : Blo 546805 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B619231 : Blo 546805 619231 := bstep (se 1 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 619231 = 928847) B928847
theorem B1406423 : Blo 546805 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1504727 : Blo 546805 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B2783159 : Blo 546805 2783159 := bstep (se 1 (by rfl) ⟨2087369, by rfl⟩ : syracuseStep 2783159 = 4174739) B4174739
theorem B5928889 : Blo 546805 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B7927739 : Blo 546805 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B121534825 : Blo 546805 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B2783807 : Blo 546805 2783807 := bstep (se 1 (by rfl) ⟨2087855, by rfl⟩ : syracuseStep 2783807 = 4175711) B4175711
theorem B2817011 : Blo 546805 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B3505679 : Blo 546805 3505679 := bstep (se 1 (by rfl) ⟨2629259, by rfl⟩ : syracuseStep 3505679 = 5258519) B5258519
theorem B3506651 : Blo 546805 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B5276123 : Blo 546805 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B60293645 : Blo 546805 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B5080009 : Blo 546805 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B5276663 : Blo 546805 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B56984593 : Blo 546805 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B820331 : Blo 546805 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B820571 : Blo 546805 820571 := bstep (se 1 (by rfl) ⟨615428, by rfl⟩ : syracuseStep 820571 = 1230857) B1230857
theorem B820847 : Blo 546805 820847 := bstep (se 1 (by rfl) ⟨615635, by rfl⟩ : syracuseStep 820847 = 1231271) B1231271
theorem B820919 : Blo 546805 820919 := bstep (se 1 (by rfl) ⟨615689, by rfl⟩ : syracuseStep 820919 = 1231379) B1231379
theorem B820955 : Blo 546805 820955 := bstep (se 1 (by rfl) ⟨615716, by rfl⟩ : syracuseStep 820955 = 1231433) B1231433
theorem B3114881 : Blo 546805 3114881 := bstep (se 2 (by rfl) ⟨1168080, by rfl⟩ : syracuseStep 3114881 = 2336161) B2336161
theorem B821129 : Blo 546805 821129 := bstep (se 2 (by rfl) ⟨307923, by rfl⟩ : syracuseStep 821129 = 615847) B615847
theorem B821231 : Blo 546805 821231 := bstep (se 1 (by rfl) ⟨615923, by rfl⟩ : syracuseStep 821231 = 1231847) B1231847
theorem B3508343 : Blo 546805 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B3115199 : Blo 546805 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B821483 : Blo 546805 821483 := bstep (se 1 (by rfl) ⟨616112, by rfl⟩ : syracuseStep 821483 = 1232225) B1232225
theorem B821543 : Blo 546805 821543 := bstep (se 1 (by rfl) ⟨616157, by rfl⟩ : syracuseStep 821543 = 1232315) B1232315
theorem B821627 : Blo 546805 821627 := bstep (se 1 (by rfl) ⟨616220, by rfl⟩ : syracuseStep 821627 = 1232441) B1232441
theorem B6654433 : Blo 546805 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B821897 : Blo 546805 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B822071 : Blo 546805 822071 := bstep (se 1 (by rfl) ⟨616553, by rfl⟩ : syracuseStep 822071 = 1233107) B1233107
theorem B822107 : Blo 546805 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B822251 : Blo 546805 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B822455 : Blo 546805 822455 := bstep (se 1 (by rfl) ⟨616841, by rfl⟩ : syracuseStep 822455 = 1233683) B1233683
theorem B822695 : Blo 546805 822695 := bstep (se 1 (by rfl) ⟨617021, by rfl⟩ : syracuseStep 822695 = 1234043) B1234043
theorem B822779 : Blo 546805 822779 := bstep (se 1 (by rfl) ⟨617084, by rfl⟩ : syracuseStep 822779 = 1234169) B1234169
theorem B822875 : Blo 546805 822875 := bstep (se 1 (by rfl) ⟨617156, by rfl⟩ : syracuseStep 822875 = 1234313) B1234313
theorem B1248875 : Blo 546805 1248875 := bstep (se 1 (by rfl) ⟨936656, by rfl⟩ : syracuseStep 1248875 = 1873313) B1873313
theorem B822959 : Blo 546805 822959 := bstep (se 1 (by rfl) ⟨617219, by rfl⟩ : syracuseStep 822959 = 1234439) B1234439
theorem B3116839 : Blo 546805 3116839 := bstep (se 1 (by rfl) ⟨2337629, by rfl⟩ : syracuseStep 3116839 = 4675259) B4675259
theorem B823079 : Blo 546805 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B823163 : Blo 546805 823163 := bstep (se 1 (by rfl) ⟨617372, by rfl⟩ : syracuseStep 823163 = 1234745) B1234745
theorem B823583 : Blo 546805 823583 := bstep (se 1 (by rfl) ⟨617687, by rfl⟩ : syracuseStep 823583 = 1235375) B1235375
theorem B823607 : Blo 546805 823607 := bstep (se 1 (by rfl) ⟨617705, by rfl⟩ : syracuseStep 823607 = 1235411) B1235411
theorem B823679 : Blo 546805 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B823751 : Blo 546805 823751 := bstep (se 1 (by rfl) ⟨617813, by rfl⟩ : syracuseStep 823751 = 1235627) B1235627
theorem B3379915 : Blo 546805 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B824105 : Blo 546805 824105 := bstep (se 2 (by rfl) ⟨309039, by rfl⟩ : syracuseStep 824105 = 618079) B618079
theorem B824111 : Blo 546805 824111 := bstep (se 1 (by rfl) ⟨618083, by rfl⟩ : syracuseStep 824111 = 1236167) B1236167
theorem B824231 : Blo 546805 824231 := bstep (se 1 (by rfl) ⟨618173, by rfl⟩ : syracuseStep 824231 = 1236347) B1236347
theorem B824315 : Blo 546805 824315 := bstep (se 1 (by rfl) ⟨618236, by rfl⟩ : syracuseStep 824315 = 1236473) B1236473
theorem B824375 : Blo 546805 824375 := bstep (se 1 (by rfl) ⟨618281, by rfl⟩ : syracuseStep 824375 = 1236563) B1236563
theorem B693355 : Blo 546805 693355 := bstep (se 1 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 693355 = 1040033) B1040033
theorem B922799 : Blo 546805 922799 := bstep (se 1 (by rfl) ⟨692099, by rfl⟩ : syracuseStep 922799 = 1384199) B1384199
theorem B824495 : Blo 546805 824495 := bstep (se 1 (by rfl) ⟨618371, by rfl⟩ : syracuseStep 824495 = 1236743) B1236743
theorem B923035 : Blo 546805 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B824903 : Blo 546805 824903 := bstep (se 1 (by rfl) ⟨618677, by rfl⟩ : syracuseStep 824903 = 1237355) B1237355
theorem B824999 : Blo 546805 824999 := bstep (se 1 (by rfl) ⟨618749, by rfl⟩ : syracuseStep 824999 = 1237499) B1237499
theorem B5281469 : Blo 546805 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B923359 : Blo 546805 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B825083 : Blo 546805 825083 := bstep (se 1 (by rfl) ⟨618812, by rfl⟩ : syracuseStep 825083 = 1237625) B1237625
theorem B825119 : Blo 546805 825119 := bstep (se 1 (by rfl) ⟨618839, by rfl⟩ : syracuseStep 825119 = 1237679) B1237679
theorem B825167 : Blo 546805 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B1251209 : Blo 546805 1251209 := bstep (se 2 (by rfl) ⟨469203, by rfl⟩ : syracuseStep 1251209 = 938407) B938407
theorem B825287 : Blo 546805 825287 := bstep (se 1 (by rfl) ⟨618965, by rfl⟩ : syracuseStep 825287 = 1237931) B1237931
theorem B3348431 : Blo 546805 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B923791 : Blo 546805 923791 := bstep (se 1 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 923791 = 1385687) B1385687
theorem B825641 : Blo 546805 825641 := bstep (se 2 (by rfl) ⟨309615, by rfl⟩ : syracuseStep 825641 = 619231) B619231
theorem B825647 : Blo 546805 825647 := bstep (se 1 (by rfl) ⟨619235, by rfl⟩ : syracuseStep 825647 = 1238471) B1238471
theorem B825887 : Blo 546805 825887 := bstep (se 1 (by rfl) ⟨619415, by rfl⟩ : syracuseStep 825887 = 1238831) B1238831
theorem B1579867 : Blo 546805 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B924743 : Blo 546805 924743 := bstep (se 1 (by rfl) ⟨693557, by rfl⟩ : syracuseStep 924743 = 1387115) B1387115
theorem B892391 : Blo 546805 892391 := bstep (se 1 (by rfl) ⟨669293, by rfl⟩ : syracuseStep 892391 = 1338587) B1338587
theorem B925175 : Blo 546805 925175 := bstep (se 1 (by rfl) ⟨693881, by rfl⟩ : syracuseStep 925175 = 1387763) B1387763
theorem B14294677 : Blo 546805 14294677 := bstep (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) B670063
theorem B7905185 : Blo 546805 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B991147 : Blo 546805 991147 := bstep (se 1 (by rfl) ⟨743360, by rfl⟩ : syracuseStep 991147 = 1486721) B1486721
theorem B991199 : Blo 546805 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B1384735 : Blo 546805 1384735 := bstep (se 1 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 1384735 = 2077103) B2077103
theorem B162046433 : Blo 546805 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B926201 : Blo 546805 926201 := bstep (se 2 (by rfl) ⟨347325, by rfl⟩ : syracuseStep 926201 = 694651) B694651
theorem B2368073 : Blo 546805 2368073 := bstep (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) B1776055
theorem B926471 : Blo 546805 926471 := bstep (se 1 (by rfl) ⟨694853, by rfl⟩ : syracuseStep 926471 = 1389707) B1389707
theorem B1385383 : Blo 546805 1385383 := bstep (se 1 (by rfl) ⟨1039037, by rfl⟩ : syracuseStep 1385383 = 2078075) B2078075
theorem B2630681 : Blo 546805 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B4400335 : Blo 546805 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B992531 : Blo 546805 992531 := bstep (se 1 (by rfl) ⟨744398, by rfl⟩ : syracuseStep 992531 = 1488797) B1488797
theorem B5285159 : Blo 546805 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B927551 : Blo 546805 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B927625 : Blo 546805 927625 := bstep (se 2 (by rfl) ⟨347859, by rfl⟩ : syracuseStep 927625 = 695719) B695719
theorem B1878007 : Blo 546805 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B1386791 : Blo 546805 1386791 := bstep (se 1 (by rfl) ⟨1040093, by rfl⟩ : syracuseStep 1386791 = 2080187) B2080187
theorem B928057 : Blo 546805 928057 := bstep (se 2 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 928057 = 696043) B696043
theorem B2337119 : Blo 546805 2337119 := bstep (se 1 (by rfl) ⟨1752839, by rfl⟩ : syracuseStep 2337119 = 3505679) B3505679
theorem B1845665 : Blo 546805 1845665 := bstep (se 2 (by rfl) ⟨692124, by rfl⟩ : syracuseStep 1845665 = 1384249) B1384249
theorem B1190305 : Blo 546805 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B928361 : Blo 546805 928361 := bstep (se 2 (by rfl) ⟨348135, by rfl⟩ : syracuseStep 928361 = 696271) B696271
theorem B5646955 : Blo 546805 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B929191 : Blo 546805 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B929353 : Blo 546805 929353 := bstep (se 2 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 929353 = 697015) B697015
theorem B929387 : Blo 546805 929387 := bstep (se 1 (by rfl) ⟨697040, by rfl⟩ : syracuseStep 929387 = 1394081) B1394081
theorem B3518315 : Blo 546805 3518315 := bstep (se 1 (by rfl) ⟨2638736, by rfl⟩ : syracuseStep 3518315 = 5277473) B5277473
theorem B2502845 : Blo 546805 2502845 := bstep (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) B938567
theorem B1880317 : Blo 546805 1880317 := bstep (se 3 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 1880317 = 705119) B705119
theorem B1847663 : Blo 546805 1847663 := bstep (se 1 (by rfl) ⟨1385747, by rfl⟩ : syracuseStep 1847663 = 2771495) B2771495
theorem B1388927 : Blo 546805 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B6238781 : Blo 546805 6238781 := bstep (se 3 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 6238781 = 2339543) B2339543
theorem B701503 : Blo 546805 701503 := bstep (se 1 (by rfl) ⟨526127, by rfl⟩ : syracuseStep 701503 = 1052255) B1052255
theorem B1979873 : Blo 546805 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B2340535 : Blo 546805 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B1849067 : Blo 546805 1849067 := bstep (se 1 (by rfl) ⟨1386800, by rfl⟩ : syracuseStep 1849067 = 2773601) B2773601
theorem B1390567 : Blo 546805 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B1849337 : Blo 546805 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B1849499 : Blo 546805 1849499 := bstep (se 1 (by rfl) ⟨1387124, by rfl⟩ : syracuseStep 1849499 = 2774249) B2774249
theorem B1849607 : Blo 546805 1849607 := bstep (se 1 (by rfl) ⟨1387205, by rfl⟩ : syracuseStep 1849607 = 2774411) B2774411
theorem B5945845 : Blo 546805 5945845 := bstep (se 5 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 5945845 = 557423) B557423
theorem B3750461 : Blo 546805 3750461 := bstep (se 3 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 3750461 = 1406423) B1406423
theorem B4012667 : Blo 546805 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B1391519 : Blo 546805 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B3128503 : Blo 546805 3128503 := bstep (se 1 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 3128503 = 4692755) B4692755
theorem B1850633 : Blo 546805 1850633 := bstep (se 2 (by rfl) ⟨693987, by rfl⟩ : syracuseStep 1850633 = 1387975) B1387975
theorem B1719713 : Blo 546805 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B7028471 : Blo 546805 7028471 := bstep (se 1 (by rfl) ⟨5271353, by rfl⟩ : syracuseStep 7028471 = 10542707) B10542707
theorem B4177655 : Blo 546805 4177655 := bstep (se 1 (by rfl) ⟨3133241, by rfl⟩ : syracuseStep 4177655 = 6266483) B6266483
theorem B2342945 : Blo 546805 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B1851767 : Blo 546805 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B4178627 : Blo 546805 4178627 := bstep (se 1 (by rfl) ⟨3133970, by rfl⟩ : syracuseStep 4178627 = 6267941) B6267941
theorem B2638601 : Blo 546805 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B1753967 : Blo 546805 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B4703143 : Blo 546805 4703143 := bstep (se 1 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 4703143 = 7054715) B7054715
theorem B2769875 : Blo 546805 2769875 := bstep (se 1 (by rfl) ⟨2077406, by rfl⟩ : syracuseStep 2769875 = 4154813) B4154813
theorem B3949825 : Blo 546805 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B8111411 : Blo 546805 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B1852847 : Blo 546805 1852847 := bstep (se 1 (by rfl) ⟨1389635, by rfl⟩ : syracuseStep 1852847 = 2779271) B2779271
theorem B15877619 : Blo 546805 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B3950117 : Blo 546805 3950117 := bstep (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) B740647
theorem B2082419 : Blo 546805 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B2344601 : Blo 546805 2344601 := bstep (se 2 (by rfl) ⟨879225, by rfl⟩ : syracuseStep 2344601 = 1758451) B1758451
theorem B1230623 : Blo 546805 1230623 := bstep (se 1 (by rfl) ⟨922967, by rfl⟩ : syracuseStep 1230623 = 1845935) B1845935
theorem B1853225 : Blo 546805 1853225 := bstep (se 2 (by rfl) ⟨694959, by rfl⟩ : syracuseStep 1853225 = 1389919) B1389919
theorem B1230839 : Blo 546805 1230839 := bstep (se 1 (by rfl) ⟨923129, by rfl⟩ : syracuseStep 1230839 = 1846259) B1846259
theorem B1558739 : Blo 546805 1558739 := bstep (se 1 (by rfl) ⟨1169054, by rfl⟩ : syracuseStep 1558739 = 2338109) B2338109
theorem B1231199 : Blo 546805 1231199 := bstep (se 1 (by rfl) ⟨923399, by rfl⟩ : syracuseStep 1231199 = 1846799) B1846799
theorem B1559047 : Blo 546805 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B1231919 : Blo 546805 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B1232207 : Blo 546805 1232207 := bstep (se 1 (by rfl) ⟨924155, by rfl⟩ : syracuseStep 1232207 = 1848311) B1848311
theorem B1232297 : Blo 546805 1232297 := bstep (se 2 (by rfl) ⟨462111, by rfl⟩ : syracuseStep 1232297 = 924223) B924223
theorem B7884377 : Blo 546805 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B1003151 : Blo 546805 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B2346857 : Blo 546805 2346857 := bstep (se 2 (by rfl) ⟨880071, by rfl⟩ : syracuseStep 2346857 = 1760143) B1760143
theorem B1232783 : Blo 546805 1232783 := bstep (se 1 (by rfl) ⟨924587, by rfl⟩ : syracuseStep 1232783 = 1849175) B1849175
theorem B1855439 : Blo 546805 1855439 := bstep (se 1 (by rfl) ⟨1391579, by rfl⟩ : syracuseStep 1855439 = 2783159) B2783159
theorem B5132593 : Blo 546805 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B1855871 : Blo 546805 1855871 := bstep (se 1 (by rfl) ⟨1391903, by rfl⟩ : syracuseStep 1855871 = 2783807) B2783807
theorem B2085335 : Blo 546805 2085335 := bstep (se 1 (by rfl) ⟨1564001, by rfl⟩ : syracuseStep 2085335 = 3128003) B3128003
theorem B1233503 : Blo 546805 1233503 := bstep (se 1 (by rfl) ⟨925127, by rfl⟩ : syracuseStep 1233503 = 1850255) B1850255
theorem B2347643 : Blo 546805 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B5001917 : Blo 546805 5001917 := bstep (se 3 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 5001917 = 1875719) B1875719
theorem B4510505 : Blo 546805 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B15061801 : Blo 546805 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B1561609 : Blo 546805 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B1561655 : Blo 546805 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B16897241 : Blo 546805 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B1234331 : Blo 546805 1234331 := bstep (se 1 (by rfl) ⟨925748, by rfl⟩ : syracuseStep 1234331 = 1851497) B1851497
theorem B1857275 : Blo 546805 1857275 := bstep (se 1 (by rfl) ⟨1392956, by rfl⟩ : syracuseStep 1857275 = 2785913) B2785913
theorem B14014295 : Blo 546805 14014295 := bstep (se 1 (by rfl) ⟨10510721, by rfl⟩ : syracuseStep 14014295 = 21021443) B21021443
theorem B1857437 : Blo 546805 1857437 := bstep (se 3 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 1857437 = 696539) B696539
theorem B1234907 : Blo 546805 1234907 := bstep (se 1 (by rfl) ⟨926180, by rfl⟩ : syracuseStep 1234907 = 1852361) B1852361
theorem B1169491 : Blo 546805 1169491 := bstep (se 1 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 1169491 = 1754237) B1754237
theorem B1235087 : Blo 546805 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B546971 : Blo 546805 546971 := bstep (se 1 (by rfl) ⟨410228, by rfl⟩ : syracuseStep 546971 = 820457) B820457
theorem B1038491 : Blo 546805 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B1235105 : Blo 546805 1235105 := bstep (se 2 (by rfl) ⟨463164, by rfl⟩ : syracuseStep 1235105 = 926329) B926329
theorem B547007 : Blo 546805 547007 := bstep (se 1 (by rfl) ⟨410255, by rfl⟩ : syracuseStep 547007 = 820511) B820511
theorem B1235177 : Blo 546805 1235177 := bstep (se 2 (by rfl) ⟨463191, by rfl⟩ : syracuseStep 1235177 = 926383) B926383
theorem B8444189 : Blo 546805 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B547119 : Blo 546805 547119 := bstep (se 1 (by rfl) ⟨410339, by rfl⟩ : syracuseStep 547119 = 820679) B820679
theorem B8149355 : Blo 546805 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B11852243 : Blo 546805 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B547355 : Blo 546805 547355 := bstep (se 1 (by rfl) ⟨410516, by rfl⟩ : syracuseStep 547355 = 821033) B821033
theorem B547359 : Blo 546805 547359 := bstep (se 1 (by rfl) ⟨410519, by rfl⟩ : syracuseStep 547359 = 821039) B821039
theorem B1169977 : Blo 546805 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B547675 : Blo 546805 547675 := bstep (se 1 (by rfl) ⟨410756, by rfl⟩ : syracuseStep 547675 = 821513) B821513
theorem B1858409 : Blo 546805 1858409 := bstep (se 2 (by rfl) ⟨696903, by rfl⟩ : syracuseStep 1858409 = 1393807) B1393807
theorem B547743 : Blo 546805 547743 := bstep (se 1 (by rfl) ⟨410807, by rfl⟩ : syracuseStep 547743 = 821615) B821615
theorem B1858463 : Blo 546805 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B547887 : Blo 546805 547887 := bstep (se 1 (by rfl) ⟨410915, by rfl⟩ : syracuseStep 547887 = 821831) B821831
theorem B547911 : Blo 546805 547911 := bstep (se 1 (by rfl) ⟨410933, by rfl⟩ : syracuseStep 547911 = 821867) B821867
theorem B2350205 : Blo 546805 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B21060809 : Blo 546805 21060809 := bstep (se 2 (by rfl) ⟨7897803, by rfl⟩ : syracuseStep 21060809 = 15795607) B15795607
theorem B548063 : Blo 546805 548063 := bstep (se 1 (by rfl) ⟨411047, by rfl⟩ : syracuseStep 548063 = 822095) B822095
theorem B875945 : Blo 546805 875945 := bstep (se 2 (by rfl) ⟨328479, by rfl⟩ : syracuseStep 875945 = 656959) B656959
theorem B548327 : Blo 546805 548327 := bstep (se 1 (by rfl) ⟨411245, by rfl⟩ : syracuseStep 548327 = 822491) B822491
theorem B1236455 : Blo 546805 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B4152869 : Blo 546805 4152869 := bstep (se 4 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 4152869 = 778663) B778663
theorem B548443 : Blo 546805 548443 := bstep (se 1 (by rfl) ⟨411332, by rfl⟩ : syracuseStep 548443 = 822665) B822665
theorem B548679 : Blo 546805 548679 := bstep (se 1 (by rfl) ⟨411509, by rfl⟩ : syracuseStep 548679 = 823019) B823019
theorem B2809723 : Blo 546805 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B548831 : Blo 546805 548831 := bstep (se 1 (by rfl) ⟨411623, by rfl⟩ : syracuseStep 548831 = 823247) B823247
theorem B1237031 : Blo 546805 1237031 := bstep (se 1 (by rfl) ⟨927773, by rfl⟩ : syracuseStep 1237031 = 1855547) B1855547
theorem B1237211 : Blo 546805 1237211 := bstep (se 1 (by rfl) ⟨927908, by rfl⟩ : syracuseStep 1237211 = 1855817) B1855817
theorem B549095 : Blo 546805 549095 := bstep (se 1 (by rfl) ⟨411821, by rfl⟩ : syracuseStep 549095 = 823643) B823643
theorem B549247 : Blo 546805 549247 := bstep (se 1 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 549247 = 823871) B823871
theorem B549327 : Blo 546805 549327 := bstep (se 1 (by rfl) ⟨411995, by rfl⟩ : syracuseStep 549327 = 823991) B823991
theorem B1237481 : Blo 546805 1237481 := bstep (se 2 (by rfl) ⟨464055, by rfl⟩ : syracuseStep 1237481 = 928111) B928111
theorem B15000065 : Blo 546805 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B549479 : Blo 546805 549479 := bstep (se 1 (by rfl) ⟨412109, by rfl⟩ : syracuseStep 549479 = 824219) B824219
theorem B21652103 : Blo 546805 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B1237769 : Blo 546805 1237769 := bstep (se 2 (by rfl) ⟨464163, by rfl⟩ : syracuseStep 1237769 = 928327) B928327
theorem B2089739 : Blo 546805 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1172335 : Blo 546805 1172335 := bstep (se 1 (by rfl) ⟨879251, by rfl⟩ : syracuseStep 1172335 = 1758503) B1758503
theorem B549743 : Blo 546805 549743 := bstep (se 1 (by rfl) ⟨412307, by rfl⟩ : syracuseStep 549743 = 824615) B824615
theorem B40035221 : Blo 546805 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B549799 : Blo 546805 549799 := bstep (se 1 (by rfl) ⟨412349, by rfl⟩ : syracuseStep 549799 = 824699) B824699
theorem B549883 : Blo 546805 549883 := bstep (se 1 (by rfl) ⟨412412, by rfl⟩ : syracuseStep 549883 = 824825) B824825
theorem B2778137 : Blo 546805 2778137 := bstep (se 2 (by rfl) ⟨1041801, by rfl⟩ : syracuseStep 2778137 = 2083603) B2083603
theorem B7922717 : Blo 546805 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B615487 : Blo 546805 615487 := bstep (se 1 (by rfl) ⟨461615, by rfl⟩ : syracuseStep 615487 = 923231) B923231
theorem B549951 : Blo 546805 549951 := bstep (se 1 (by rfl) ⟨412463, by rfl⟩ : syracuseStep 549951 = 824927) B824927
theorem B1565801 : Blo 546805 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B3761275 : Blo 546805 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B615631 : Blo 546805 615631 := bstep (se 1 (by rfl) ⟨461723, by rfl⟩ : syracuseStep 615631 = 923447) B923447
theorem B550095 : Blo 546805 550095 := bstep (se 1 (by rfl) ⟨412571, by rfl⟩ : syracuseStep 550095 = 825143) B825143
theorem B1238345 : Blo 546805 1238345 := bstep (se 2 (by rfl) ⟨464379, by rfl⟩ : syracuseStep 1238345 = 928759) B928759
theorem B550299 : Blo 546805 550299 := bstep (se 1 (by rfl) ⟨412724, by rfl⟩ : syracuseStep 550299 = 825449) B825449
theorem B550511 : Blo 546805 550511 := bstep (se 1 (by rfl) ⟨412883, by rfl⟩ : syracuseStep 550511 = 825767) B825767
theorem B1173113 : Blo 546805 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B550567 : Blo 546805 550567 := bstep (se 1 (by rfl) ⟨412925, by rfl⟩ : syracuseStep 550567 = 825851) B825851
theorem B878303 : Blo 546805 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B550651 : Blo 546805 550651 := bstep (se 1 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 550651 = 825977) B825977
theorem B550687 : Blo 546805 550687 := bstep (se 1 (by rfl) ⟨413015, by rfl⟩ : syracuseStep 550687 = 826031) B826031
theorem B550719 : Blo 546805 550719 := bstep (se 1 (by rfl) ⟨413039, by rfl⟩ : syracuseStep 550719 = 826079) B826079
theorem B3172297 : Blo 546805 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B3565721 : Blo 546805 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B616603 : Blo 546805 616603 := bstep (se 1 (by rfl) ⟨462452, by rfl⟩ : syracuseStep 616603 = 924905) B924905
theorem B616639 : Blo 546805 616639 := bstep (se 1 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 616639 = 924959) B924959
theorem B3336731 : Blo 546805 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B1567259 : Blo 546805 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B1043131 : Blo 546805 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B30043025 : Blo 546805 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B1043435 : Blo 546805 1043435 := bstep (se 1 (by rfl) ⟨782576, by rfl⟩ : syracuseStep 1043435 = 1565153) B1565153
theorem B1764449 : Blo 546805 1764449 := bstep (se 2 (by rfl) ⟨661668, by rfl⟩ : syracuseStep 1764449 = 1323337) B1323337
theorem B6679691 : Blo 546805 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B1567943 : Blo 546805 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B2780729 : Blo 546805 2780729 := bstep (se 2 (by rfl) ⟨1042773, by rfl⟩ : syracuseStep 2780729 = 2085547) B2085547
theorem B3764029 : Blo 546805 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B880507 : Blo 546805 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B1667039 : Blo 546805 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B17854667 : Blo 546805 17854667 := bstep (se 1 (by rfl) ⟨13391000, by rfl⟩ : syracuseStep 17854667 = 26782001) B26782001
theorem B618727 : Blo 546805 618727 := bstep (se 1 (by rfl) ⟨464045, by rfl⟩ : syracuseStep 618727 = 928091) B928091
theorem B1045075 : Blo 546805 1045075 := bstep (se 1 (by rfl) ⟨783806, by rfl⟩ : syracuseStep 1045075 = 1567613) B1567613
theorem B1405601 : Blo 546805 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B619375 : Blo 546805 619375 := bstep (se 1 (by rfl) ⟨464531, by rfl⟩ : syracuseStep 619375 = 929063) B929063
theorem B8909941 : Blo 546805 8909941 := bstep (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) B835307
theorem B1668271 : Blo 546805 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B1112057 : Blo 546805 1112057 := bstep (se 2 (by rfl) ⟨417021, by rfl⟩ : syracuseStep 1112057 = 834043) B834043
theorem B4159673 : Blo 546805 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B12712301 : Blo 546805 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B3505193 : Blo 546805 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B2784617 : Blo 546805 2784617 := bstep (se 2 (by rfl) ⟨1044231, by rfl⟩ : syracuseStep 2784617 = 2088463) B2088463
theorem B2785751 : Blo 546805 2785751 := bstep (se 1 (by rfl) ⟨2089313, by rfl⟩ : syracuseStep 2785751 = 4178627) B4178627
theorem B5407607 : Blo 546805 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B10585079 : Blo 546805 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B820415 : Blo 546805 820415 := bstep (se 1 (by rfl) ⟨615311, by rfl⟩ : syracuseStep 820415 = 1230623) B1230623
theorem B10028357 : Blo 546805 10028357 := bstep (se 4 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 10028357 = 1880317) B1880317
theorem B820559 : Blo 546805 820559 := bstep (se 1 (by rfl) ⟨615419, by rfl⟩ : syracuseStep 820559 = 1230839) B1230839
theorem B820649 : Blo 546805 820649 := bstep (se 2 (by rfl) ⟨307743, by rfl⟩ : syracuseStep 820649 = 615487) B615487
theorem B5015033 : Blo 546805 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B820799 : Blo 546805 820799 := bstep (se 1 (by rfl) ⟨615599, by rfl⟩ : syracuseStep 820799 = 1231199) B1231199
theorem B820841 : Blo 546805 820841 := bstep (se 2 (by rfl) ⟨307815, by rfl⟩ : syracuseStep 820841 = 615631) B615631
theorem B5867113 : Blo 546805 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B13338445 : Blo 546805 13338445 := bstep (se 3 (by rfl) ⟨2500958, by rfl⟩ : syracuseStep 13338445 = 5001917) B5001917
theorem B821279 : Blo 546805 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B821471 : Blo 546805 821471 := bstep (se 1 (by rfl) ⟨616103, by rfl⟩ : syracuseStep 821471 = 1232207) B1232207
theorem B821531 : Blo 546805 821531 := bstep (se 1 (by rfl) ⟨616148, by rfl⟩ : syracuseStep 821531 = 1232297) B1232297
theorem B821855 : Blo 546805 821855 := bstep (se 1 (by rfl) ⟨616391, by rfl⟩ : syracuseStep 821855 = 1232783) B1232783
theorem B4229729 : Blo 546805 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B822137 : Blo 546805 822137 := bstep (se 2 (by rfl) ⟨308301, by rfl⟩ : syracuseStep 822137 = 616603) B616603
theorem B822185 : Blo 546805 822185 := bstep (se 2 (by rfl) ⟨308319, by rfl⟩ : syracuseStep 822185 = 616639) B616639
theorem B822335 : Blo 546805 822335 := bstep (se 1 (by rfl) ⟨616751, by rfl⟩ : syracuseStep 822335 = 1233503) B1233503
theorem B822887 : Blo 546805 822887 := bstep (se 1 (by rfl) ⟨617165, by rfl⟩ : syracuseStep 822887 = 1234331) B1234331
theorem B9342863 : Blo 546805 9342863 := bstep (se 1 (by rfl) ⟨7007147, by rfl⟩ : syracuseStep 9342863 = 14014295) B14014295
theorem B2232287 : Blo 546805 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B823271 : Blo 546805 823271 := bstep (se 1 (by rfl) ⟨617453, by rfl⟩ : syracuseStep 823271 = 1234907) B1234907
theorem B823391 : Blo 546805 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B692327 : Blo 546805 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B823403 : Blo 546805 823403 := bstep (se 1 (by rfl) ⟨617552, by rfl⟩ : syracuseStep 823403 = 1235105) B1235105
theorem B823451 : Blo 546805 823451 := bstep (se 1 (by rfl) ⟨617588, by rfl⟩ : syracuseStep 823451 = 1235177) B1235177
theorem B7901495 : Blo 546805 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B8425957 : Blo 546805 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B824303 : Blo 546805 824303 := bstep (se 1 (by rfl) ⟨618227, by rfl⟩ : syracuseStep 824303 = 1236455) B1236455
theorem B5018705 : Blo 546805 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B660799 : Blo 546805 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B824687 : Blo 546805 824687 := bstep (se 1 (by rfl) ⟨618515, by rfl⟩ : syracuseStep 824687 = 1237031) B1237031
theorem B824807 : Blo 546805 824807 := bstep (se 1 (by rfl) ⟨618605, by rfl⟩ : syracuseStep 824807 = 1237211) B1237211
theorem B824969 : Blo 546805 824969 := bstep (se 2 (by rfl) ⟨309363, by rfl⟩ : syracuseStep 824969 = 618727) B618727
theorem B824987 : Blo 546805 824987 := bstep (se 1 (by rfl) ⟨618740, by rfl⟩ : syracuseStep 824987 = 1237481) B1237481
theorem B3741349 : Blo 546805 3741349 := bstep (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) B701503
theorem B10000043 : Blo 546805 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B825179 : Blo 546805 825179 := bstep (se 1 (by rfl) ⟨618884, by rfl⟩ : syracuseStep 825179 = 1237769) B1237769
theorem B5281811 : Blo 546805 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B825563 : Blo 546805 825563 := bstep (se 1 (by rfl) ⟨619172, by rfl⟩ : syracuseStep 825563 = 1238345) B1238345
theorem B825833 : Blo 546805 825833 := bstep (se 2 (by rfl) ⟨309687, by rfl⟩ : syracuseStep 825833 = 619375) B619375
theorem B924473 : Blo 546805 924473 := bstep (se 2 (by rfl) ⟨346677, by rfl⟩ : syracuseStep 924473 = 693355) B693355
theorem B924527 : Blo 546805 924527 := bstep (se 1 (by rfl) ⟨693395, by rfl⟩ : syracuseStep 924527 = 1386791) B1386791
theorem B20028683 : Blo 546805 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B695623 : Blo 546805 695623 := bstep (se 1 (by rfl) ⟨521717, by rfl⟩ : syracuseStep 695623 = 1043435) B1043435
theorem B3120713 : Blo 546805 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B11903111 : Blo 546805 11903111 := bstep (se 1 (by rfl) ⟨8927333, by rfl⟩ : syracuseStep 11903111 = 17854667) B17854667
theorem B925951 : Blo 546805 925951 := bstep (se 1 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 925951 = 1388927) B1388927
theorem B1319915 : Blo 546805 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B2335853 : Blo 546805 2335853 := bstep (se 3 (by rfl) ⟨437972, by rfl⟩ : syracuseStep 2335853 = 875945) B875945
theorem B4171337 : Blo 546805 4171337 := bstep (se 2 (by rfl) ⟨1564251, by rfl⟩ : syracuseStep 4171337 = 3128503) B3128503
theorem B2500307 : Blo 546805 2500307 := bstep (se 1 (by rfl) ⟨1875230, by rfl⟩ : syracuseStep 2500307 = 3750461) B3750461
theorem B927679 : Blo 546805 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B2336795 : Blo 546805 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B3746297 : Blo 546805 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B1321529 : Blo 546805 1321529 := bstep (se 2 (by rfl) ⟨495573, by rfl⟩ : syracuseStep 1321529 = 991147) B991147
theorem B2337767 : Blo 546805 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B3517415 : Blo 546805 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B1846313 : Blo 546805 1846313 := bstep (se 2 (by rfl) ⟨692367, by rfl⟩ : syracuseStep 1846313 = 1384735) B1384735
theorem B1846583 : Blo 546805 1846583 := bstep (se 1 (by rfl) ⟨1384937, by rfl⟩ : syracuseStep 1846583 = 2769875) B2769875
theorem B3517775 : Blo 546805 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B2633411 : Blo 546805 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B1388279 : Blo 546805 1388279 := bstep (se 1 (by rfl) ⟨1041209, by rfl⟩ : syracuseStep 1388279 = 2082419) B2082419
theorem B1847177 : Blo 546805 1847177 := bstep (se 2 (by rfl) ⟨692691, by rfl⟩ : syracuseStep 1847177 = 1385383) B1385383
theorem B6270857 : Blo 546805 6270857 := bstep (se 2 (by rfl) ⟨2351571, by rfl⟩ : syracuseStep 6270857 = 4703143) B4703143
theorem B2076587 : Blo 546805 2076587 := bstep (se 1 (by rfl) ⟨1557440, by rfl⟩ : syracuseStep 2076587 = 3114881) B3114881
theorem B2338895 : Blo 546805 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B2076799 : Blo 546805 2076799 := bstep (se 1 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 2076799 = 3115199) B3115199
theorem B5256251 : Blo 546805 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B832583 : Blo 546805 832583 := bstep (se 1 (by rfl) ⟨624437, by rfl⟩ : syracuseStep 832583 = 1248875) B1248875
theorem B2504009 : Blo 546805 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B1390223 : Blo 546805 1390223 := bstep (se 1 (by rfl) ⟨1042667, by rfl⟩ : syracuseStep 1390223 = 2085335) B2085335
theorem B1587073 : Blo 546805 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B2078729 : Blo 546805 2078729 := bstep (se 2 (by rfl) ⟨779523, by rfl⟩ : syracuseStep 2078729 = 1559047) B1559047
theorem B1390841 : Blo 546805 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B3520979 : Blo 546805 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B2342141 : Blo 546805 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B14040539 : Blo 546805 14040539 := bstep (se 1 (by rfl) ⟨10530404, by rfl⟩ : syracuseStep 14040539 = 21060809) B21060809
theorem B2768579 : Blo 546805 2768579 := bstep (se 1 (by rfl) ⟨2076434, by rfl⟩ : syracuseStep 2768579 = 4152869) B4152869
theorem B14434735 : Blo 546805 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B1393159 : Blo 546805 1393159 := bstep (se 1 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 1393159 = 2089739) B2089739
theorem B26690147 : Blo 546805 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B1753787 : Blo 546805 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B1852091 : Blo 546805 1852091 := bstep (se 1 (by rfl) ⟨1389068, by rfl⟩ : syracuseStep 1852091 = 2778137) B2778137
theorem B1393433 : Blo 546805 1393433 := bstep (se 2 (by rfl) ⟨522537, by rfl⟩ : syracuseStep 1393433 = 1045075) B1045075
theorem B3523439 : Blo 546805 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B4506553 : Blo 546805 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B2082145 : Blo 546805 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B2377147 : Blo 546805 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B11879921 : Blo 546805 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1558079 : Blo 546805 1558079 := bstep (se 1 (by rfl) ⟨1168559, by rfl⟩ : syracuseStep 1558079 = 2337119) B2337119
theorem B1230443 : Blo 546805 1230443 := bstep (se 1 (by rfl) ⟨922832, by rfl⟩ : syracuseStep 1230443 = 1845665) B1845665
theorem B1230713 : Blo 546805 1230713 := bstep (se 2 (by rfl) ⟨461517, by rfl⟩ : syracuseStep 1230713 = 923035) B923035
theorem B1231145 : Blo 546805 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B1853819 : Blo 546805 1853819 := bstep (se 1 (by rfl) ⟨1390364, by rfl⟩ : syracuseStep 1853819 = 2780729) B2780729
theorem B2345543 : Blo 546805 2345543 := bstep (se 1 (by rfl) ⟨1759157, by rfl⟩ : syracuseStep 2345543 = 3518315) B3518315
theorem B1854089 : Blo 546805 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B1559321 : Blo 546805 1559321 := bstep (se 2 (by rfl) ⟨584745, by rfl⟩ : syracuseStep 1559321 = 1169491) B1169491
theorem B1231721 : Blo 546805 1231721 := bstep (se 2 (by rfl) ⟨461895, by rfl⟩ : syracuseStep 1231721 = 923791) B923791
theorem B1231775 : Blo 546805 1231775 := bstep (se 1 (by rfl) ⟨923831, by rfl⟩ : syracuseStep 1231775 = 1847663) B1847663
theorem B937067 : Blo 546805 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B1559969 : Blo 546805 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B1232711 : Blo 546805 1232711 := bstep (se 1 (by rfl) ⟨924533, by rfl⟩ : syracuseStep 1232711 = 1849067) B1849067
theorem B2379709 : Blo 546805 2379709 := bstep (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) B892391
theorem B1232891 : Blo 546805 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B741371 : Blo 546805 741371 := bstep (se 1 (by rfl) ⟨556028, by rfl⟩ : syracuseStep 741371 = 1112057) B1112057
theorem B1232999 : Blo 546805 1232999 := bstep (se 1 (by rfl) ⟨924749, by rfl⟩ : syracuseStep 1232999 = 1849499) B1849499
theorem B2773115 : Blo 546805 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B1233071 : Blo 546805 1233071 := bstep (se 1 (by rfl) ⟨924803, by rfl⟩ : syracuseStep 1233071 = 1849607) B1849607
theorem B8474867 : Blo 546805 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B2675069 : Blo 546805 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B2675111 : Blo 546805 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B1233755 : Blo 546805 1233755 := bstep (se 1 (by rfl) ⟨925316, by rfl⟩ : syracuseStep 1233755 = 1850633) B1850633
theorem B19059569 : Blo 546805 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1856411 : Blo 546805 1856411 := bstep (se 1 (by rfl) ⟨1392308, by rfl⟩ : syracuseStep 1856411 = 2784617) B2784617
theorem B4445437 : Blo 546805 4445437 := bstep (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) B1667039
theorem B1561963 : Blo 546805 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B1234511 : Blo 546805 1234511 := bstep (se 1 (by rfl) ⟨925883, by rfl⟩ : syracuseStep 1234511 = 1851767) B1851767
theorem B40195763 : Blo 546805 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1759067 : Blo 546805 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B1169311 : Blo 546805 1169311 := bstep (se 1 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 1169311 = 1753967) B1753967
theorem B546887 : Blo 546805 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B547047 : Blo 546805 547047 := bstep (se 1 (by rfl) ⟨410285, by rfl⟩ : syracuseStep 547047 = 820571) B820571
theorem B1235231 : Blo 546805 1235231 := bstep (se 1 (by rfl) ⟨926423, by rfl⟩ : syracuseStep 1235231 = 1852847) B1852847
theorem B547231 : Blo 546805 547231 := bstep (se 1 (by rfl) ⟨410423, by rfl⟩ : syracuseStep 547231 = 820847) B820847
theorem B1563067 : Blo 546805 1563067 := bstep (se 1 (by rfl) ⟨1172300, by rfl⟩ : syracuseStep 1563067 = 2344601) B2344601
theorem B547279 : Blo 546805 547279 := bstep (se 1 (by rfl) ⟨410459, by rfl⟩ : syracuseStep 547279 = 820919) B820919
theorem B547303 : Blo 546805 547303 := bstep (se 1 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 547303 = 820955) B820955
theorem B1563113 : Blo 546805 1563113 := bstep (se 2 (by rfl) ⟨586167, by rfl⟩ : syracuseStep 1563113 = 1172335) B1172335
theorem B1235483 : Blo 546805 1235483 := bstep (se 1 (by rfl) ⟨926612, by rfl⟩ : syracuseStep 1235483 = 1853225) B1853225
theorem B547419 : Blo 546805 547419 := bstep (se 1 (by rfl) ⟨410564, by rfl⟩ : syracuseStep 547419 = 821129) B821129
theorem B6773345 : Blo 546805 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B547487 : Blo 546805 547487 := bstep (se 1 (by rfl) ⟨410615, by rfl⟩ : syracuseStep 547487 = 821231) B821231
theorem B75979457 : Blo 546805 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1039159 : Blo 546805 1039159 := bstep (se 1 (by rfl) ⟨779369, by rfl⟩ : syracuseStep 1039159 = 1558739) B1558739
theorem B547655 : Blo 546805 547655 := bstep (se 1 (by rfl) ⟨410741, by rfl⟩ : syracuseStep 547655 = 821483) B821483
theorem B6314861 : Blo 546805 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B547695 : Blo 546805 547695 := bstep (se 1 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 547695 = 821543) B821543
theorem B547751 : Blo 546805 547751 := bstep (se 1 (by rfl) ⟨410813, by rfl⟩ : syracuseStep 547751 = 821627) B821627
theorem B5266433 : Blo 546805 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B547931 : Blo 546805 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B548047 : Blo 546805 548047 := bstep (se 1 (by rfl) ⟨411035, by rfl⟩ : syracuseStep 548047 = 822071) B822071
theorem B548071 : Blo 546805 548071 := bstep (se 1 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 548071 = 822107) B822107
theorem B548167 : Blo 546805 548167 := bstep (se 1 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 548167 = 822251) B822251
theorem B548303 : Blo 546805 548303 := bstep (se 1 (by rfl) ⟨411227, by rfl⟩ : syracuseStep 548303 = 822455) B822455
theorem B548463 : Blo 546805 548463 := bstep (se 1 (by rfl) ⟨411347, by rfl⟩ : syracuseStep 548463 = 822695) B822695
theorem B548519 : Blo 546805 548519 := bstep (se 1 (by rfl) ⟨411389, by rfl⟩ : syracuseStep 548519 = 822779) B822779
theorem B548583 : Blo 546805 548583 := bstep (se 1 (by rfl) ⟨411437, by rfl⟩ : syracuseStep 548583 = 822875) B822875
theorem B548639 : Blo 546805 548639 := bstep (se 1 (by rfl) ⟨411479, by rfl⟩ : syracuseStep 548639 = 822959) B822959
theorem B1236833 : Blo 546805 1236833 := bstep (se 2 (by rfl) ⟨463812, by rfl⟩ : syracuseStep 1236833 = 927625) B927625
theorem B548719 : Blo 546805 548719 := bstep (se 1 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 548719 = 823079) B823079
theorem B1564571 : Blo 546805 1564571 := bstep (se 1 (by rfl) ⟨1173428, by rfl⟩ : syracuseStep 1564571 = 2346857) B2346857
theorem B548775 : Blo 546805 548775 := bstep (se 1 (by rfl) ⟨411581, by rfl⟩ : syracuseStep 548775 = 823163) B823163
theorem B1236959 : Blo 546805 1236959 := bstep (se 1 (by rfl) ⟨927719, by rfl⟩ : syracuseStep 1236959 = 1855439) B1855439
theorem B549055 : Blo 546805 549055 := bstep (se 1 (by rfl) ⟨411791, by rfl⟩ : syracuseStep 549055 = 823583) B823583
theorem B549071 : Blo 546805 549071 := bstep (se 1 (by rfl) ⟨411803, by rfl⟩ : syracuseStep 549071 = 823607) B823607
theorem B549119 : Blo 546805 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B1237247 : Blo 546805 1237247 := bstep (se 1 (by rfl) ⟨927935, by rfl⟩ : syracuseStep 1237247 = 1855871) B1855871
theorem B549167 : Blo 546805 549167 := bstep (se 1 (by rfl) ⟨411875, by rfl⟩ : syracuseStep 549167 = 823751) B823751
theorem B1237409 : Blo 546805 1237409 := bstep (se 2 (by rfl) ⟨464028, by rfl⟩ : syracuseStep 1237409 = 928057) B928057
theorem B1565095 : Blo 546805 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B3007003 : Blo 546805 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B549403 : Blo 546805 549403 := bstep (se 1 (by rfl) ⟨412052, by rfl⟩ : syracuseStep 549403 = 824105) B824105
theorem B549407 : Blo 546805 549407 := bstep (se 1 (by rfl) ⟨412055, by rfl⟩ : syracuseStep 549407 = 824111) B824111
theorem B549487 : Blo 546805 549487 := bstep (se 1 (by rfl) ⟨412115, by rfl⟩ : syracuseStep 549487 = 824231) B824231
theorem B8872577 : Blo 546805 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B549543 : Blo 546805 549543 := bstep (se 1 (by rfl) ⟨412157, by rfl⟩ : syracuseStep 549543 = 824315) B824315
theorem B1041103 : Blo 546805 1041103 := bstep (se 1 (by rfl) ⟨780827, by rfl⟩ : syracuseStep 1041103 = 1561655) B1561655
theorem B549583 : Blo 546805 549583 := bstep (se 1 (by rfl) ⟨412187, by rfl⟩ : syracuseStep 549583 = 824375) B824375
theorem B2646749 : Blo 546805 2646749 := bstep (se 3 (by rfl) ⟨496265, by rfl⟩ : syracuseStep 2646749 = 992531) B992531
theorem B615199 : Blo 546805 615199 := bstep (se 1 (by rfl) ⟨461399, by rfl⟩ : syracuseStep 615199 = 922799) B922799
theorem B549663 : Blo 546805 549663 := bstep (se 1 (by rfl) ⟨412247, by rfl⟩ : syracuseStep 549663 = 824495) B824495
theorem B7529273 : Blo 546805 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B11264827 : Blo 546805 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B549935 : Blo 546805 549935 := bstep (se 1 (by rfl) ⟨412451, by rfl⟩ : syracuseStep 549935 = 824903) B824903
theorem B549999 : Blo 546805 549999 := bstep (se 1 (by rfl) ⟨412499, by rfl⟩ : syracuseStep 549999 = 824999) B824999
theorem B550055 : Blo 546805 550055 := bstep (se 1 (by rfl) ⟨412541, by rfl⟩ : syracuseStep 550055 = 825083) B825083
theorem B1238183 : Blo 546805 1238183 := bstep (se 1 (by rfl) ⟨928637, by rfl⟩ : syracuseStep 1238183 = 1857275) B1857275
theorem B550079 : Blo 546805 550079 := bstep (se 1 (by rfl) ⟨412559, by rfl⟩ : syracuseStep 550079 = 825119) B825119
theorem B550111 : Blo 546805 550111 := bstep (se 1 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 550111 = 825167) B825167
theorem B1238291 : Blo 546805 1238291 := bstep (se 1 (by rfl) ⟨928718, by rfl⟩ : syracuseStep 1238291 = 1857437) B1857437
theorem B550191 : Blo 546805 550191 := bstep (se 1 (by rfl) ⟨412643, by rfl⟩ : syracuseStep 550191 = 825287) B825287
theorem B5629459 : Blo 546805 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B550427 : Blo 546805 550427 := bstep (se 1 (by rfl) ⟨412820, by rfl⟩ : syracuseStep 550427 = 825641) B825641
theorem B550431 : Blo 546805 550431 := bstep (se 1 (by rfl) ⟨412823, by rfl⟩ : syracuseStep 550431 = 825647) B825647
theorem B5432903 : Blo 546805 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B550591 : Blo 546805 550591 := bstep (se 1 (by rfl) ⟨412943, by rfl⟩ : syracuseStep 550591 = 825887) B825887
theorem B1238921 : Blo 546805 1238921 := bstep (se 2 (by rfl) ⟨464595, by rfl⟩ : syracuseStep 1238921 = 929191) B929191
theorem B1238939 : Blo 546805 1238939 := bstep (se 1 (by rfl) ⟨929204, by rfl⟩ : syracuseStep 1238939 = 1858409) B1858409
theorem B1238975 : Blo 546805 1238975 := bstep (se 1 (by rfl) ⟨929231, by rfl⟩ : syracuseStep 1238975 = 1858463) B1858463
theorem B616495 : Blo 546805 616495 := bstep (se 1 (by rfl) ⟨462371, by rfl⟩ : syracuseStep 616495 = 924743) B924743
theorem B1566803 : Blo 546805 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1239137 : Blo 546805 1239137 := bstep (se 2 (by rfl) ⟨464676, by rfl⟩ : syracuseStep 1239137 = 929353) B929353
theorem B616783 : Blo 546805 616783 := bstep (se 1 (by rfl) ⟨462587, by rfl⟩ : syracuseStep 616783 = 925175) B925175
theorem B3336557 : Blo 546805 3336557 := bstep (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) B1251209
theorem B4155785 : Blo 546805 4155785 := bstep (se 2 (by rfl) ⟨1558419, by rfl⟩ : syracuseStep 4155785 = 3116839) B3116839
theorem B1174009 : Blo 546805 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B5270123 : Blo 546805 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B108030955 : Blo 546805 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B617467 : Blo 546805 617467 := bstep (se 1 (by rfl) ⟨463100, by rfl⟩ : syracuseStep 617467 = 926201) B926201
theorem B6843457 : Blo 546805 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B617647 : Blo 546805 617647 := bstep (se 1 (by rfl) ⟨463235, by rfl⟩ : syracuseStep 617647 = 926471) B926471
theorem B1043867 : Blo 546805 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B20082401 : Blo 546805 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B782075 : Blo 546805 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B618367 : Blo 546805 618367 := bstep (se 1 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 618367 = 927551) B927551
theorem B2224361 : Blo 546805 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B2224487 : Blo 546805 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B1044839 : Blo 546805 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B618907 : Blo 546805 618907 := bstep (se 1 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 618907 = 928361) B928361
theorem B1176299 : Blo 546805 1176299 := bstep (se 1 (by rfl) ⟨882224, by rfl⟩ : syracuseStep 1176299 = 1764449) B1764449
theorem B4453127 : Blo 546805 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B1045295 : Blo 546805 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B619591 : Blo 546805 619591 := bstep (se 1 (by rfl) ⟨464693, by rfl⟩ : syracuseStep 619591 = 929387) B929387
theorem B1668563 : Blo 546805 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B4159187 : Blo 546805 4159187 := bstep (se 1 (by rfl) ⟨3119390, by rfl⟩ : syracuseStep 4159187 = 6238781) B6238781
theorem B7927793 : Blo 546805 7927793 := bstep (se 2 (by rfl) ⟨2972922, by rfl⟩ : syracuseStep 7927793 = 5945845) B5945845
theorem B1146475 : Blo 546805 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B4685647 : Blo 546805 4685647 := bstep (se 1 (by rfl) ⟨3514235, by rfl⟩ : syracuseStep 4685647 = 7028471) B7028471
theorem B2785103 : Blo 546805 2785103 := bstep (se 1 (by rfl) ⟨2088827, by rfl⟩ : syracuseStep 2785103 = 4177655) B4177655
theorem B17793431 : Blo 546805 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B6685571 : Blo 546805 6685571 := bstep (se 1 (by rfl) ⟨5014178, by rfl⟩ : syracuseStep 6685571 = 10028357) B10028357
theorem B2786237 : Blo 546805 2786237 := bstep (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) B1044839
theorem B3343355 : Blo 546805 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B820265 : Blo 546805 820265 := bstep (se 2 (by rfl) ⟨307599, by rfl⟩ : syracuseStep 820265 = 615199) B615199
theorem B820295 : Blo 546805 820295 := bstep (se 1 (by rfl) ⟨615221, by rfl⟩ : syracuseStep 820295 = 1230443) B1230443
theorem B820475 : Blo 546805 820475 := bstep (se 1 (by rfl) ⟨615356, by rfl⟩ : syracuseStep 820475 = 1230713) B1230713
theorem B820763 : Blo 546805 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B2819819 : Blo 546805 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B821147 : Blo 546805 821147 := bstep (se 1 (by rfl) ⟨615860, by rfl⟩ : syracuseStep 821147 = 1231721) B1231721
theorem B821183 : Blo 546805 821183 := bstep (se 1 (by rfl) ⟨615887, by rfl⟩ : syracuseStep 821183 = 1231775) B1231775
theorem B7505945 : Blo 546805 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B14420285 : Blo 546805 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B821807 : Blo 546805 821807 := bstep (se 1 (by rfl) ⟨616355, by rfl⟩ : syracuseStep 821807 = 1232711) B1232711
theorem B6228575 : Blo 546805 6228575 := bstep (se 1 (by rfl) ⟨4671431, by rfl⟩ : syracuseStep 6228575 = 9342863) B9342863
theorem B821927 : Blo 546805 821927 := bstep (se 1 (by rfl) ⟨616445, by rfl⟩ : syracuseStep 821927 = 1232891) B1232891
theorem B821993 : Blo 546805 821993 := bstep (se 2 (by rfl) ⟨308247, by rfl⟩ : syracuseStep 821993 = 616495) B616495
theorem B821999 : Blo 546805 821999 := bstep (se 1 (by rfl) ⟨616499, by rfl⟩ : syracuseStep 821999 = 1232999) B1232999
theorem B822047 : Blo 546805 822047 := bstep (se 1 (by rfl) ⟨616535, by rfl⟩ : syracuseStep 822047 = 1233071) B1233071
theorem B822377 : Blo 546805 822377 := bstep (se 2 (by rfl) ⟨308391, by rfl⟩ : syracuseStep 822377 = 616783) B616783
theorem B822503 : Blo 546805 822503 := bstep (se 1 (by rfl) ⟨616877, by rfl⟩ : syracuseStep 822503 = 1233755) B1233755
theorem B3345803 : Blo 546805 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B823007 : Blo 546805 823007 := bstep (se 1 (by rfl) ⟨617255, by rfl⟩ : syracuseStep 823007 = 1234511) B1234511
theorem B35589941 : Blo 546805 35589941 := bstep (se 5 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 35589941 = 3336557) B3336557
theorem B823289 : Blo 546805 823289 := bstep (se 2 (by rfl) ⟨308733, by rfl⟩ : syracuseStep 823289 = 617467) B617467
theorem B823487 : Blo 546805 823487 := bstep (se 1 (by rfl) ⟨617615, by rfl⟩ : syracuseStep 823487 = 1235231) B1235231
theorem B823529 : Blo 546805 823529 := bstep (se 2 (by rfl) ⟨308823, by rfl⟩ : syracuseStep 823529 = 617647) B617647
theorem B823655 : Blo 546805 823655 := bstep (se 1 (by rfl) ⟨617741, by rfl⟩ : syracuseStep 823655 = 1235483) B1235483
theorem B3510955 : Blo 546805 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B824489 : Blo 546805 824489 := bstep (se 2 (by rfl) ⟨309183, by rfl⟩ : syracuseStep 824489 = 618367) B618367
theorem B824555 : Blo 546805 824555 := bstep (se 1 (by rfl) ⟨618416, by rfl⟩ : syracuseStep 824555 = 1236833) B1236833
theorem B824639 : Blo 546805 824639 := bstep (se 1 (by rfl) ⟨618479, by rfl⟩ : syracuseStep 824639 = 1236959) B1236959
theorem B7935407 : Blo 546805 7935407 := bstep (se 1 (by rfl) ⟨5951555, by rfl⟩ : syracuseStep 7935407 = 11903111) B11903111
theorem B824831 : Blo 546805 824831 := bstep (se 1 (by rfl) ⟨618623, by rfl⟩ : syracuseStep 824831 = 1237247) B1237247
theorem B824939 : Blo 546805 824939 := bstep (se 1 (by rfl) ⟨618704, by rfl⟩ : syracuseStep 824939 = 1237409) B1237409
theorem B825209 : Blo 546805 825209 := bstep (se 2 (by rfl) ⟨309453, by rfl⟩ : syracuseStep 825209 = 618907) B618907
theorem B5019515 : Blo 546805 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B825455 : Blo 546805 825455 := bstep (se 1 (by rfl) ⟨619091, by rfl⟩ : syracuseStep 825455 = 1238183) B1238183
theorem B825527 : Blo 546805 825527 := bstep (se 1 (by rfl) ⟨619145, by rfl⟩ : syracuseStep 825527 = 1238291) B1238291
theorem B825947 : Blo 546805 825947 := bstep (se 1 (by rfl) ⟨619460, by rfl⟩ : syracuseStep 825947 = 1238921) B1238921
theorem B825959 : Blo 546805 825959 := bstep (se 1 (by rfl) ⟨619469, by rfl⟩ : syracuseStep 825959 = 1238939) B1238939
theorem B825983 : Blo 546805 825983 := bstep (se 1 (by rfl) ⟨619487, by rfl⟩ : syracuseStep 825983 = 1238975) B1238975
theorem B826091 : Blo 546805 826091 := bstep (se 1 (by rfl) ⟨619568, by rfl⟩ : syracuseStep 826091 = 1239137) B1239137
theorem B826121 : Blo 546805 826121 := bstep (se 2 (by rfl) ⟨309795, by rfl⟩ : syracuseStep 826121 = 619591) B619591
theorem B4988465 : Blo 546805 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B925519 : Blo 546805 925519 := bstep (se 1 (by rfl) ⟨694139, by rfl⟩ : syracuseStep 925519 = 1388279) B1388279
theorem B1384391 : Blo 546805 1384391 := bstep (se 1 (by rfl) ⟨1038293, by rfl⟩ : syracuseStep 1384391 = 2076587) B2076587
theorem B1482907 : Blo 546805 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B1482991 : Blo 546805 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B2498845 : Blo 546805 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B696863 : Blo 546805 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B1385545 : Blo 546805 1385545 := bstep (se 2 (by rfl) ⟨519579, by rfl⟩ : syracuseStep 1385545 = 1039159) B1039159
theorem B926815 : Blo 546805 926815 := bstep (se 1 (by rfl) ⟨695111, by rfl⟩ : syracuseStep 926815 = 1390223) B1390223
theorem B5285195 : Blo 546805 5285195 := bstep (se 1 (by rfl) ⟨3963896, by rfl⟩ : syracuseStep 5285195 = 7927793) B7927793
theorem B1385819 : Blo 546805 1385819 := bstep (se 1 (by rfl) ⟨1039364, by rfl⟩ : syracuseStep 1385819 = 2078729) B2078729
theorem B927227 : Blo 546805 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B927497 : Blo 546805 927497 := bstep (se 2 (by rfl) ⟨347811, by rfl⟩ : syracuseStep 927497 = 695623) B695623
theorem B1845719 : Blo 546805 1845719 := bstep (se 1 (by rfl) ⟨1384289, by rfl⟩ : syracuseStep 1845719 = 2768579) B2768579
theorem B1976989 : Blo 546805 1976989 := bstep (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) B741371
theorem B1846205 : Blo 546805 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B928955 : Blo 546805 928955 := bstep (se 1 (by rfl) ⟨696716, by rfl⟩ : syracuseStep 928955 = 1393433) B1393433
theorem B19246313 : Blo 546805 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B7056719 : Blo 546805 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B4009337 : Blo 546805 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1388137 : Blo 546805 1388137 := bstep (se 2 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 1388137 = 1041103) B1041103
theorem B15019769 : Blo 546805 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B6008737 : Blo 546805 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B3519773 : Blo 546805 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1488191 : Blo 546805 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B1848743 : Blo 546805 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B5649911 : Blo 546805 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1783379 : Blo 546805 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B6666695 : Blo 546805 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B3521207 : Blo 546805 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B9124609 : Blo 546805 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B4209907 : Blo 546805 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B13352455 : Blo 546805 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B2080475 : Blo 546805 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B2769065 : Blo 546805 2769065 := bstep (se 2 (by rfl) ⟨1038399, by rfl⟩ : syracuseStep 2769065 = 2076799) B2076799
theorem B4178141 : Blo 546805 4178141 := bstep (se 3 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 4178141 = 1566803) B1566803
theorem B5915051 : Blo 546805 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B1557235 : Blo 546805 1557235 := bstep (se 1 (by rfl) ⟨1167926, by rfl⟩ : syracuseStep 1557235 = 2335853) B2335853
theorem B3621935 : Blo 546805 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B1557863 : Blo 546805 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B3524077 : Blo 546805 3524077 := bstep (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) B1321529
theorem B2770523 : Blo 546805 2770523 := bstep (se 1 (by rfl) ⟨2077892, by rfl⟩ : syracuseStep 2770523 = 4155785) B4155785
theorem B2082617 : Blo 546805 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B1558511 : Blo 546805 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B2344943 : Blo 546805 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B1230875 : Blo 546805 1230875 := bstep (se 1 (by rfl) ⟨923156, by rfl⟩ : syracuseStep 1230875 = 1846313) B1846313
theorem B1231055 : Blo 546805 1231055 := bstep (se 1 (by rfl) ⟨923291, by rfl⟩ : syracuseStep 1231055 = 1846583) B1846583
theorem B2345183 : Blo 546805 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B1755607 : Blo 546805 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B13388267 : Blo 546805 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B2116097 : Blo 546805 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B1559081 : Blo 546805 1559081 := bstep (se 2 (by rfl) ⟨584655, by rfl⟩ : syracuseStep 1559081 = 1169311) B1169311
theorem B1231451 : Blo 546805 1231451 := bstep (se 1 (by rfl) ⟨923588, by rfl⟩ : syracuseStep 1231451 = 1847177) B1847177
theorem B4180571 : Blo 546805 4180571 := bstep (se 1 (by rfl) ⟨3135428, by rfl⟩ : syracuseStep 4180571 = 6270857) B6270857
theorem B1559263 : Blo 546805 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B2968751 : Blo 546805 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B2084089 : Blo 546805 2084089 := bstep (se 2 (by rfl) ⟨781533, by rfl⟩ : syracuseStep 2084089 = 1563067) B1563067
theorem B2772791 : Blo 546805 2772791 := bstep (se 1 (by rfl) ⟨2079593, by rfl⟩ : syracuseStep 2772791 = 4159187) B4159187
theorem B2347319 : Blo 546805 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B2085533 : Blo 546805 2085533 := bstep (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) B782075
theorem B1528633 : Blo 546805 1528633 := bstep (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) B1146475
theorem B1561427 : Blo 546805 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B9360359 : Blo 546805 9360359 := bstep (se 1 (by rfl) ⟨7020269, by rfl⟩ : syracuseStep 9360359 = 14040539) B14040539
theorem B6247529 : Blo 546805 6247529 := bstep (se 2 (by rfl) ⟨2342823, by rfl⟩ : syracuseStep 6247529 = 4685647) B4685647
theorem B1856735 : Blo 546805 1856735 := bstep (se 1 (by rfl) ⟨1392551, by rfl⟩ : syracuseStep 1856735 = 2785103) B2785103
theorem B1857167 : Blo 546805 1857167 := bstep (se 1 (by rfl) ⟨1392875, by rfl⟩ : syracuseStep 1857167 = 2785751) B2785751
theorem B1234601 : Blo 546805 1234601 := bstep (se 2 (by rfl) ⟨462975, by rfl⟩ : syracuseStep 1234601 = 925951) B925951
theorem B1169191 : Blo 546805 1169191 := bstep (se 1 (by rfl) ⟨876893, by rfl⟩ : syracuseStep 1169191 = 1753787) B1753787
theorem B1234727 : Blo 546805 1234727 := bstep (se 1 (by rfl) ⟨926045, by rfl⟩ : syracuseStep 1234727 = 1852091) B1852091
theorem B2086793 : Blo 546805 2086793 := bstep (se 2 (by rfl) ⟨782547, by rfl⟩ : syracuseStep 2086793 = 1565095) B1565095
theorem B2348959 : Blo 546805 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B1857545 : Blo 546805 1857545 := bstep (se 2 (by rfl) ⟨696579, by rfl⟩ : syracuseStep 1857545 = 1393159) B1393159
theorem B546943 : Blo 546805 546943 := bstep (se 1 (by rfl) ⟨410207, by rfl⟩ : syracuseStep 546943 = 820415) B820415
theorem B547039 : Blo 546805 547039 := bstep (se 1 (by rfl) ⟨410279, by rfl⟩ : syracuseStep 547039 = 820559) B820559
theorem B547099 : Blo 546805 547099 := bstep (se 1 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 547099 = 820649) B820649
theorem B7919947 : Blo 546805 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1038719 : Blo 546805 1038719 := bstep (se 1 (by rfl) ⟨779039, by rfl⟩ : syracuseStep 1038719 = 1558079) B1558079
theorem B547199 : Blo 546805 547199 := bstep (se 1 (by rfl) ⟨410399, by rfl⟩ : syracuseStep 547199 = 820799) B820799
theorem B547227 : Blo 546805 547227 := bstep (se 1 (by rfl) ⟨410420, by rfl⟩ : syracuseStep 547227 = 820841) B820841
theorem B7133629 : Blo 546805 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B547519 : Blo 546805 547519 := bstep (se 1 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 547519 = 821279) B821279
theorem B547647 : Blo 546805 547647 := bstep (se 1 (by rfl) ⟨410735, by rfl⟩ : syracuseStep 547647 = 821471) B821471
theorem B547687 : Blo 546805 547687 := bstep (se 1 (by rfl) ⟨410765, by rfl⟩ : syracuseStep 547687 = 821531) B821531
theorem B1235879 : Blo 546805 1235879 := bstep (se 1 (by rfl) ⟨926909, by rfl⟩ : syracuseStep 1235879 = 1853819) B1853819
theorem B1563695 : Blo 546805 1563695 := bstep (se 1 (by rfl) ⟨1172771, by rfl⟩ : syracuseStep 1563695 = 2345543) B2345543
theorem B547903 : Blo 546805 547903 := bstep (se 1 (by rfl) ⟨410927, by rfl⟩ : syracuseStep 547903 = 821855) B821855
theorem B1236059 : Blo 546805 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B2776193 : Blo 546805 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B1039547 : Blo 546805 1039547 := bstep (se 1 (by rfl) ⟨779660, by rfl⟩ : syracuseStep 1039547 = 1559321) B1559321
theorem B3169529 : Blo 546805 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B548091 : Blo 546805 548091 := bstep (se 1 (by rfl) ⟨411068, by rfl⟩ : syracuseStep 548091 = 822137) B822137
theorem B548123 : Blo 546805 548123 := bstep (se 1 (by rfl) ⟨411092, by rfl⟩ : syracuseStep 548123 = 822185) B822185
theorem B548223 : Blo 546805 548223 := bstep (se 1 (by rfl) ⟨411167, by rfl⟩ : syracuseStep 548223 = 822335) B822335
theorem B7822817 : Blo 546805 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B1039979 : Blo 546805 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B548591 : Blo 546805 548591 := bstep (se 1 (by rfl) ⟨411443, by rfl⟩ : syracuseStep 548591 = 822887) B822887
theorem B17784593 : Blo 546805 17784593 := bstep (se 2 (by rfl) ⟨6669222, by rfl⟩ : syracuseStep 17784593 = 13338445) B13338445
theorem B1236905 : Blo 546805 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B548847 : Blo 546805 548847 := bstep (se 1 (by rfl) ⟨411635, by rfl⟩ : syracuseStep 548847 = 823271) B823271
theorem B548927 : Blo 546805 548927 := bstep (se 1 (by rfl) ⟨411695, by rfl⟩ : syracuseStep 548927 = 823391) B823391
theorem B548935 : Blo 546805 548935 := bstep (se 1 (by rfl) ⟨411701, by rfl⟩ : syracuseStep 548935 = 823403) B823403
theorem B548967 : Blo 546805 548967 := bstep (se 1 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 548967 = 823451) B823451
theorem B5267663 : Blo 546805 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B12706379 : Blo 546805 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B1237607 : Blo 546805 1237607 := bstep (se 1 (by rfl) ⟨928205, by rfl⟩ : syracuseStep 1237607 = 1856411) B1856411
theorem B549535 : Blo 546805 549535 := bstep (se 1 (by rfl) ⟨412151, by rfl⟩ : syracuseStep 549535 = 824303) B824303
theorem B1565345 : Blo 546805 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B549791 : Blo 546805 549791 := bstep (se 1 (by rfl) ⟨412343, by rfl⟩ : syracuseStep 549791 = 824687) B824687
theorem B549871 : Blo 546805 549871 := bstep (se 1 (by rfl) ⟨412403, by rfl⟩ : syracuseStep 549871 = 824807) B824807
theorem B549979 : Blo 546805 549979 := bstep (se 1 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 549979 = 824969) B824969
theorem B549991 : Blo 546805 549991 := bstep (se 1 (by rfl) ⟨412493, by rfl⟩ : syracuseStep 549991 = 824987) B824987
theorem B26797175 : Blo 546805 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1172711 : Blo 546805 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B550119 : Blo 546805 550119 := bstep (se 1 (by rfl) ⟨412589, by rfl⟩ : syracuseStep 550119 = 825179) B825179
theorem B144041273 : Blo 546805 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B550375 : Blo 546805 550375 := bstep (se 1 (by rfl) ⟨412781, by rfl⟩ : syracuseStep 550375 = 825563) B825563
theorem B1042075 : Blo 546805 1042075 := bstep (se 1 (by rfl) ⟨781556, by rfl⟩ : syracuseStep 1042075 = 1563113) B1563113
theorem B550555 : Blo 546805 550555 := bstep (se 1 (by rfl) ⟨412916, by rfl⟩ : syracuseStep 550555 = 825833) B825833
theorem B4515563 : Blo 546805 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B50652971 : Blo 546805 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B616315 : Blo 546805 616315 := bstep (se 1 (by rfl) ⟨462236, by rfl⟩ : syracuseStep 616315 = 924473) B924473
theorem B616351 : Blo 546805 616351 := bstep (se 1 (by rfl) ⟨462263, by rfl⟩ : syracuseStep 616351 = 924527) B924527
theorem B3172945 : Blo 546805 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B1043047 : Blo 546805 1043047 := bstep (se 1 (by rfl) ⟨782285, by rfl⟩ : syracuseStep 1043047 = 1564571) B1564571
theorem B1764499 : Blo 546805 1764499 := bstep (se 1 (by rfl) ⟨1323374, by rfl⟩ : syracuseStep 1764499 = 2646749) B2646749
theorem B11234609 : Blo 546805 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B2780891 : Blo 546805 2780891 := bstep (se 1 (by rfl) ⟨2085668, by rfl⟩ : syracuseStep 2780891 = 4171337) B4171337
theorem B1666871 : Blo 546805 1666871 := bstep (se 1 (by rfl) ⟨1250153, by rfl⟩ : syracuseStep 1666871 = 2500307) B2500307
theorem B9990125 : Blo 546805 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B14053661 : Blo 546805 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B5927249 : Blo 546805 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B881065 : Blo 546805 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B784199 : Blo 546805 784199 := bstep (se 1 (by rfl) ⟨588149, by rfl⟩ : syracuseStep 784199 = 1176299) B1176299
theorem B3504167 : Blo 546805 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B555055 : Blo 546805 555055 := bstep (se 1 (by rfl) ⟨416291, by rfl⟩ : syracuseStep 555055 = 832583) B832583
theorem B1669339 : Blo 546805 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B1112375 : Blo 546805 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B2783645 : Blo 546805 2783645 := bstep (se 3 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 2783645 = 1043867) B1043867
theorem B2785427 : Blo 546805 2785427 := bstep (se 1 (by rfl) ⟨2089070, by rfl⟩ : syracuseStep 2785427 = 4178141) B4178141
theorem B11862287 : Blo 546805 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B4457047 : Blo 546805 4457047 := bstep (se 1 (by rfl) ⟨3342785, by rfl⟩ : syracuseStep 4457047 = 6685571) B6685571
theorem B2228903 : Blo 546805 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B820583 : Blo 546805 820583 := bstep (se 1 (by rfl) ⟨615437, by rfl⟩ : syracuseStep 820583 = 1230875) B1230875
theorem B820703 : Blo 546805 820703 := bstep (se 1 (by rfl) ⟨615527, by rfl⟩ : syracuseStep 820703 = 1231055) B1231055
theorem B1410731 : Blo 546805 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B820967 : Blo 546805 820967 := bstep (se 1 (by rfl) ⟨615725, by rfl⟩ : syracuseStep 820967 = 1231451) B1231451
theorem B2787047 : Blo 546805 2787047 := bstep (se 1 (by rfl) ⟨2090285, by rfl⟩ : syracuseStep 2787047 = 4180571) B4180571
theorem B2230535 : Blo 546805 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B821753 : Blo 546805 821753 := bstep (se 2 (by rfl) ⟨308157, by rfl⟩ : syracuseStep 821753 = 616315) B616315
theorem B23726627 : Blo 546805 23726627 := bstep (se 1 (by rfl) ⟨17794970, by rfl⟩ : syracuseStep 23726627 = 35589941) B35589941
theorem B821801 : Blo 546805 821801 := bstep (se 2 (by rfl) ⟨308175, by rfl⟩ : syracuseStep 821801 = 616351) B616351
theorem B4165019 : Blo 546805 4165019 := bstep (se 1 (by rfl) ⟨3123764, by rfl⟩ : syracuseStep 4165019 = 6247529) B6247529
theorem B4230593 : Blo 546805 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B3968509 : Blo 546805 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B823067 : Blo 546805 823067 := bstep (se 1 (by rfl) ⟨617300, by rfl⟩ : syracuseStep 823067 = 1234601) B1234601
theorem B823151 : Blo 546805 823151 := bstep (se 1 (by rfl) ⟨617363, by rfl⟩ : syracuseStep 823151 = 1234727) B1234727
theorem B3346343 : Blo 546805 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B692479 : Blo 546805 692479 := bstep (se 1 (by rfl) ⟨519359, by rfl⟩ : syracuseStep 692479 = 1038719) B1038719
theorem B823919 : Blo 546805 823919 := bstep (se 1 (by rfl) ⟨617939, by rfl⟩ : syracuseStep 823919 = 1235879) B1235879
theorem B824039 : Blo 546805 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B693031 : Blo 546805 693031 := bstep (se 1 (by rfl) ⟨519773, by rfl⟩ : syracuseStep 693031 = 1039547) B1039547
theorem B5215211 : Blo 546805 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B824603 : Blo 546805 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B922927 : Blo 546805 922927 := bstep (se 1 (by rfl) ⟨692195, by rfl⟩ : syracuseStep 922927 = 1384391) B1384391
theorem B3511775 : Blo 546805 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B825071 : Blo 546805 825071 := bstep (se 1 (by rfl) ⟨618803, by rfl⟩ : syracuseStep 825071 = 1237607) B1237607
theorem B17864783 : Blo 546805 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B923879 : Blo 546805 923879 := bstep (se 1 (by rfl) ⟨692909, by rfl⟩ : syracuseStep 923879 = 1385819) B1385819
theorem B6660083 : Blo 546805 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B71213093 : Blo 546805 71213093 := bstep (se 4 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 71213093 = 13352455) B13352455
theorem B10559929 : Blo 546805 10559929 := bstep (se 2 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 10559929 = 7919947) B7919947
theorem B9511505 : Blo 546805 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B12166145 : Blo 546805 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B1188919 : Blo 546805 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B2336111 : Blo 546805 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B5613209 : Blo 546805 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B1386983 : Blo 546805 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B1846043 : Blo 546805 1846043 := bstep (se 1 (by rfl) ⟨1384532, by rfl⟩ : syracuseStep 1846043 = 2769065) B2769065
theorem B1977209 : Blo 546805 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B2960293 : Blo 546805 2960293 := bstep (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) B555055
theorem B3943367 : Blo 546805 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B2076313 : Blo 546805 2076313 := bstep (se 2 (by rfl) ⟨778617, by rfl⟩ : syracuseStep 2076313 = 1557235) B1557235
theorem B1847015 : Blo 546805 1847015 := bstep (se 1 (by rfl) ⟨1385261, by rfl⟩ : syracuseStep 1847015 = 2770523) B2770523
theorem B1388411 : Blo 546805 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B7909285 : Blo 546805 7909285 := bstep (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) B1482991
theorem B1847393 : Blo 546805 1847393 := bstep (se 2 (by rfl) ⟨692772, by rfl⟩ : syracuseStep 1847393 = 1385545) B1385545
theorem B9613523 : Blo 546805 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B4174253 : Blo 546805 4174253 := bstep (se 3 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 4174253 = 1565345) B1565345
theorem B4698769 : Blo 546805 4698769 := bstep (se 2 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 4698769 = 3524077) B3524077
theorem B1979167 : Blo 546805 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1389433 : Blo 546805 1389433 := bstep (se 2 (by rfl) ⟨521037, by rfl⟩ : syracuseStep 1389433 = 1042075) B1042075
theorem B1848527 : Blo 546805 1848527 := bstep (se 1 (by rfl) ⟨1386395, by rfl⟩ : syracuseStep 1848527 = 2772791) B2772791
theorem B1390355 : Blo 546805 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B2340809 : Blo 546805 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B6240239 : Blo 546805 6240239 := bstep (se 1 (by rfl) ⟨4680179, by rfl⟩ : syracuseStep 6240239 = 9360359) B9360359
theorem B1390729 : Blo 546805 1390729 := bstep (se 2 (by rfl) ⟨521523, by rfl⟩ : syracuseStep 1390729 = 1043047) B1043047
theorem B2635985 : Blo 546805 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B5290271 : Blo 546805 5290271 := bstep (se 1 (by rfl) ⟨3967703, by rfl⟩ : syracuseStep 5290271 = 7935407) B7935407
theorem B2079017 : Blo 546805 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B1391195 : Blo 546805 1391195 := bstep (se 1 (by rfl) ⟨1043396, by rfl⟩ : syracuseStep 1391195 = 2086793) B2086793
theorem B7519517 : Blo 546805 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B1850795 : Blo 546805 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B1850849 : Blo 546805 1850849 := bstep (se 2 (by rfl) ⟨694068, by rfl⟩ : syracuseStep 1850849 = 1388137) B1388137
theorem B2113019 : Blo 546805 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B3325643 : Blo 546805 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B8011649 : Blo 546805 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B8470919 : Blo 546805 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B96027515 : Blo 546805 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B3523463 : Blo 546805 3523463 := bstep (se 1 (by rfl) ⟨2642597, by rfl⟩ : syracuseStep 3523463 = 5285195) B5285195
theorem B33768647 : Blo 546805 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B35702045 : Blo 546805 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B1230479 : Blo 546805 1230479 := bstep (se 1 (by rfl) ⟨922859, by rfl⟩ : syracuseStep 1230479 = 1845719) B1845719
theorem B1230803 : Blo 546805 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B12830875 : Blo 546805 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B7489739 : Blo 546805 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B4704479 : Blo 546805 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B2672891 : Blo 546805 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B1558921 : Blo 546805 1558921 := bstep (se 2 (by rfl) ⟨584595, by rfl⟩ : syracuseStep 1558921 = 1169191) B1169191
theorem B1853927 : Blo 546805 1853927 := bstep (se 1 (by rfl) ⟨1390445, by rfl⟩ : syracuseStep 1853927 = 2780891) B2780891
theorem B10013179 : Blo 546805 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B3131945 : Blo 546805 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B3951499 : Blo 546805 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B2346515 : Blo 546805 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B1232495 : Blo 546805 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B741583 : Blo 546805 741583 := bstep (se 1 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 741583 = 1112375) B1112375
theorem B1855763 : Blo 546805 1855763 := bstep (se 1 (by rfl) ⟨1391822, by rfl⟩ : syracuseStep 1855763 = 2783645) B2783645
theorem B2773277 : Blo 546805 2773277 := bstep (se 3 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 2773277 = 1039979) B1039979
theorem B4444463 : Blo 546805 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B2347471 : Blo 546805 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B1234025 : Blo 546805 1234025 := bstep (se 2 (by rfl) ⟨462759, by rfl⟩ : syracuseStep 1234025 = 925519) B925519
theorem B3331793 : Blo 546805 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1857491 : Blo 546805 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B546843 : Blo 546805 546843 := bstep (se 1 (by rfl) ⟨410132, by rfl⟩ : syracuseStep 546843 = 820265) B820265
theorem B2414623 : Blo 546805 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B546863 : Blo 546805 546863 := bstep (se 1 (by rfl) ⟨410147, by rfl⟩ : syracuseStep 546863 = 820295) B820295
theorem B546983 : Blo 546805 546983 := bstep (se 1 (by rfl) ⟨410237, by rfl⟩ : syracuseStep 546983 = 820475) B820475
theorem B1038575 : Blo 546805 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B547175 : Blo 546805 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B8903141 : Blo 546805 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B547431 : Blo 546805 547431 := bstep (se 1 (by rfl) ⟨410573, by rfl⟩ : syracuseStep 547431 = 821147) B821147
theorem B547455 : Blo 546805 547455 := bstep (se 1 (by rfl) ⟨410591, by rfl⟩ : syracuseStep 547455 = 821183) B821183
theorem B1039007 : Blo 546805 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B1563295 : Blo 546805 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B5003963 : Blo 546805 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1858301 : Blo 546805 1858301 := bstep (se 3 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 1858301 = 696863) B696863
theorem B1235753 : Blo 546805 1235753 := bstep (se 2 (by rfl) ⟨463407, by rfl⟩ : syracuseStep 1235753 = 926815) B926815
theorem B1563455 : Blo 546805 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B1039387 : Blo 546805 1039387 := bstep (se 1 (by rfl) ⟨779540, by rfl⟩ : syracuseStep 1039387 = 1559081) B1559081
theorem B547871 : Blo 546805 547871 := bstep (se 1 (by rfl) ⟨410903, by rfl⟩ : syracuseStep 547871 = 821807) B821807
theorem B4152383 : Blo 546805 4152383 := bstep (se 1 (by rfl) ⟨3114287, by rfl⟩ : syracuseStep 4152383 = 6228575) B6228575
theorem B547951 : Blo 546805 547951 := bstep (se 1 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 547951 = 821927) B821927
theorem B547995 : Blo 546805 547995 := bstep (se 1 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 547995 = 821993) B821993
theorem B547999 : Blo 546805 547999 := bstep (se 1 (by rfl) ⟨410999, by rfl⟩ : syracuseStep 547999 = 821999) B821999
theorem B548031 : Blo 546805 548031 := bstep (se 1 (by rfl) ⟨411023, by rfl⟩ : syracuseStep 548031 = 822047) B822047
theorem B548251 : Blo 546805 548251 := bstep (se 1 (by rfl) ⟨411188, by rfl⟩ : syracuseStep 548251 = 822377) B822377
theorem B548335 : Blo 546805 548335 := bstep (se 1 (by rfl) ⟨411251, by rfl⟩ : syracuseStep 548335 = 822503) B822503
theorem B548671 : Blo 546805 548671 := bstep (se 1 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 548671 = 823007) B823007
theorem B548859 : Blo 546805 548859 := bstep (se 1 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 548859 = 823289) B823289
theorem B548991 : Blo 546805 548991 := bstep (se 1 (by rfl) ⟨411743, by rfl⟩ : syracuseStep 548991 = 823487) B823487
theorem B549019 : Blo 546805 549019 := bstep (se 1 (by rfl) ⟨411764, by rfl⟩ : syracuseStep 549019 = 823529) B823529
theorem B1564879 : Blo 546805 1564879 := bstep (se 1 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 1564879 = 2347319) B2347319
theorem B549103 : Blo 546805 549103 := bstep (se 1 (by rfl) ⟨411827, by rfl⟩ : syracuseStep 549103 = 823655) B823655
theorem B1040951 : Blo 546805 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B549659 : Blo 546805 549659 := bstep (se 1 (by rfl) ⟨412244, by rfl⟩ : syracuseStep 549659 = 824489) B824489
theorem B1237823 : Blo 546805 1237823 := bstep (se 1 (by rfl) ⟨928367, by rfl⟩ : syracuseStep 1237823 = 1856735) B1856735
theorem B549703 : Blo 546805 549703 := bstep (se 1 (by rfl) ⟨412277, by rfl⟩ : syracuseStep 549703 = 824555) B824555
theorem B549759 : Blo 546805 549759 := bstep (se 1 (by rfl) ⟨412319, by rfl⟩ : syracuseStep 549759 = 824639) B824639
theorem B549887 : Blo 546805 549887 := bstep (se 1 (by rfl) ⟨412415, by rfl⟩ : syracuseStep 549887 = 824831) B824831
theorem B549959 : Blo 546805 549959 := bstep (se 1 (by rfl) ⟨412469, by rfl⟩ : syracuseStep 549959 = 824939) B824939
theorem B1238111 : Blo 546805 1238111 := bstep (se 1 (by rfl) ⟨928583, by rfl⟩ : syracuseStep 1238111 = 1857167) B1857167
theorem B550139 : Blo 546805 550139 := bstep (se 1 (by rfl) ⟨412604, by rfl⟩ : syracuseStep 550139 = 825209) B825209
theorem B1238363 : Blo 546805 1238363 := bstep (se 1 (by rfl) ⟨928772, by rfl⟩ : syracuseStep 1238363 = 1857545) B1857545
theorem B550303 : Blo 546805 550303 := bstep (se 1 (by rfl) ⟨412727, by rfl⟩ : syracuseStep 550303 = 825455) B825455
theorem B550351 : Blo 546805 550351 := bstep (se 1 (by rfl) ⟨412763, by rfl⟩ : syracuseStep 550351 = 825527) B825527
theorem B2352665 : Blo 546805 2352665 := bstep (se 2 (by rfl) ⟨882249, by rfl⟩ : syracuseStep 2352665 = 1764499) B1764499
theorem B8152709 : Blo 546805 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B2778785 : Blo 546805 2778785 := bstep (se 2 (by rfl) ⟨1042044, by rfl⟩ : syracuseStep 2778785 = 2084089) B2084089
theorem B550631 : Blo 546805 550631 := bstep (se 1 (by rfl) ⟨412973, by rfl⟩ : syracuseStep 550631 = 825947) B825947
theorem B550639 : Blo 546805 550639 := bstep (se 1 (by rfl) ⟨412979, by rfl⟩ : syracuseStep 550639 = 825959) B825959
theorem B550655 : Blo 546805 550655 := bstep (se 1 (by rfl) ⟨412991, by rfl⟩ : syracuseStep 550655 = 825983) B825983
theorem B550727 : Blo 546805 550727 := bstep (se 1 (by rfl) ⟨413045, by rfl⟩ : syracuseStep 550727 = 826091) B826091
theorem B550747 : Blo 546805 550747 := bstep (se 1 (by rfl) ⟨413060, by rfl⟩ : syracuseStep 550747 = 826121) B826121
theorem B1042463 : Blo 546805 1042463 := bstep (se 1 (by rfl) ⟨781847, by rfl⟩ : syracuseStep 1042463 = 1563695) B1563695
theorem B2091197 : Blo 546805 2091197 := bstep (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) B784199
theorem B11856395 : Blo 546805 11856395 := bstep (se 1 (by rfl) ⟨8892296, by rfl⟩ : syracuseStep 11856395 = 17784593) B17784593
theorem B1174753 : Blo 546805 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B781807 : Blo 546805 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B4681273 : Blo 546805 4681273 := bstep (se 2 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 4681273 = 3510955) B3510955
theorem B618151 : Blo 546805 618151 := bstep (se 1 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 618151 = 927227) B927227
theorem B3010375 : Blo 546805 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B618331 : Blo 546805 618331 := bstep (se 1 (by rfl) ⟨463748, by rfl⟩ : syracuseStep 618331 = 927497) B927497
theorem B619303 : Blo 546805 619303 := bstep (se 1 (by rfl) ⟨464477, by rfl⟩ : syracuseStep 619303 = 928955) B928955
theorem B1111247 : Blo 546805 1111247 := bstep (se 1 (by rfl) ⟨833435, by rfl⟩ : syracuseStep 1111247 = 1666871) B1666871
theorem B9369107 : Blo 546805 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B3766607 : Blo 546805 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B22512431 : Blo 546805 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B820319 : Blo 546805 820319 := bstep (se 1 (by rfl) ⟨615239, by rfl⟩ : syracuseStep 820319 = 1230479) B1230479
theorem B820535 : Blo 546805 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B2820395 : Blo 546805 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B821663 : Blo 546805 821663 := bstep (se 1 (by rfl) ⟨616247, by rfl⟩ : syracuseStep 821663 = 1232495) B1232495
theorem B2230895 : Blo 546805 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B3476807 : Blo 546805 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B822683 : Blo 546805 822683 := bstep (se 1 (by rfl) ⟨617012, by rfl⟩ : syracuseStep 822683 = 1234025) B1234025
theorem B692383 : Blo 546805 692383 := bstep (se 1 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 692383 = 1038575) B1038575
theorem B5935427 : Blo 546805 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B823835 : Blo 546805 823835 := bstep (se 1 (by rfl) ⟨617876, by rfl⟩ : syracuseStep 823835 = 1235753) B1235753
theorem B824201 : Blo 546805 824201 := bstep (se 2 (by rfl) ⟨309075, by rfl⟩ : syracuseStep 824201 = 618151) B618151
theorem B824441 : Blo 546805 824441 := bstep (se 2 (by rfl) ⟨309165, by rfl⟩ : syracuseStep 824441 = 618331) B618331
theorem B988777 : Blo 546805 988777 := bstep (se 2 (by rfl) ⟨370791, by rfl⟩ : syracuseStep 988777 = 741583) B741583
theorem B923305 : Blo 546805 923305 := bstep (se 2 (by rfl) ⟨346239, by rfl⟩ : syracuseStep 923305 = 692479) B692479
theorem B825215 : Blo 546805 825215 := bstep (se 1 (by rfl) ⟨618911, by rfl⟩ : syracuseStep 825215 = 1237823) B1237823
theorem B825407 : Blo 546805 825407 := bstep (se 1 (by rfl) ⟨619055, by rfl⟩ : syracuseStep 825407 = 1238111) B1238111
theorem B6265025 : Blo 546805 6265025 := bstep (se 2 (by rfl) ⟨2349384, by rfl⟩ : syracuseStep 6265025 = 4698769) B4698769
theorem B825575 : Blo 546805 825575 := bstep (se 1 (by rfl) ⟨619181, by rfl⟩ : syracuseStep 825575 = 1238363) B1238363
theorem B924041 : Blo 546805 924041 := bstep (se 2 (by rfl) ⟨346515, by rfl⟩ : syracuseStep 924041 = 693031) B693031
theorem B825737 : Blo 546805 825737 := bstep (se 2 (by rfl) ⟨309651, by rfl⟩ : syracuseStep 825737 = 619303) B619303
theorem B3742139 : Blo 546805 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B694975 : Blo 546805 694975 := bstep (se 1 (by rfl) ⟨521231, by rfl⟩ : syracuseStep 694975 = 1042463) B1042463
theorem B924655 : Blo 546805 924655 := bstep (se 1 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 924655 = 1386983) B1386983
theorem B7904263 : Blo 546805 7904263 := bstep (se 1 (by rfl) ⟨5928197, by rfl⟩ : syracuseStep 7904263 = 11856395) B11856395
theorem B1318139 : Blo 546805 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B2628911 : Blo 546805 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B925607 : Blo 546805 925607 := bstep (se 1 (by rfl) ⟨694205, by rfl⟩ : syracuseStep 925607 = 1388411) B1388411
theorem B3219497 : Blo 546805 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B926903 : Blo 546805 926903 := bstep (se 1 (by rfl) ⟨695177, by rfl⟩ : syracuseStep 926903 = 1390355) B1390355
theorem B1385849 : Blo 546805 1385849 := bstep (se 2 (by rfl) ⟨519693, by rfl⟩ : syracuseStep 1385849 = 1039387) B1039387
theorem B1386011 : Blo 546805 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B927463 : Blo 546805 927463 := bstep (se 1 (by rfl) ⟨695597, by rfl⟩ : syracuseStep 927463 = 1391195) B1391195
theorem B7908191 : Blo 546805 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B5647279 : Blo 546805 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B1485935 : Blo 546805 1485935 := bstep (se 1 (by rfl) ⟨1114451, by rfl⟩ : syracuseStep 1485935 = 2228903) B2228903
theorem B25636061 : Blo 546805 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B5942729 : Blo 546805 5942729 := bstep (se 2 (by rfl) ⟨2228523, by rfl⟩ : syracuseStep 5942729 = 4457047) B4457047
theorem B68431333 : Blo 546805 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B23801363 : Blo 546805 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B1585225 : Blo 546805 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B4993159 : Blo 546805 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B1781927 : Blo 546805 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B1848851 : Blo 546805 1848851 := bstep (se 1 (by rfl) ⟨1386638, by rfl⟩ : syracuseStep 1848851 = 2773277) B2773277
theorem B2962975 : Blo 546805 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2078561 : Blo 546805 2078561 := bstep (se 2 (by rfl) ⟨779460, by rfl⟩ : syracuseStep 2078561 = 1558921) B1558921
theorem B13350905 : Blo 546805 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B3947057 : Blo 546805 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B11909855 : Blo 546805 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B6273773 : Blo 546805 6273773 := bstep (se 3 (by rfl) ⟨1176332, by rfl⟩ : syracuseStep 6273773 = 2352665) B2352665
theorem B21740557 : Blo 546805 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B5291345 : Blo 546805 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B2768255 : Blo 546805 2768255 := bstep (se 1 (by rfl) ⟨2076191, by rfl⟩ : syracuseStep 2768255 = 4152383) B4152383
theorem B6241697 : Blo 546805 6241697 := bstep (se 2 (by rfl) ⟨2340636, by rfl⟩ : syracuseStep 6241697 = 4681273) B4681273
theorem B2768417 : Blo 546805 2768417 := bstep (se 2 (by rfl) ⟨1038156, by rfl⟩ : syracuseStep 2768417 = 2076313) B2076313
theorem B4440055 : Blo 546805 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B6341003 : Blo 546805 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B3129961 : Blo 546805 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B8110763 : Blo 546805 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B5948093 : Blo 546805 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B1557407 : Blo 546805 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B2638889 : Blo 546805 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B1852523 : Blo 546805 1852523 := bstep (se 1 (by rfl) ⟨1389392, by rfl⟩ : syracuseStep 1852523 = 2778785) B2778785
theorem B1852577 : Blo 546805 1852577 := bstep (se 2 (by rfl) ⟨694716, by rfl⟩ : syracuseStep 1852577 = 1389433) B1389433
theorem B1394131 : Blo 546805 1394131 := bstep (se 1 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 1394131 = 2091197) B2091197
theorem B1230569 : Blo 546805 1230569 := bstep (se 2 (by rfl) ⟨461463, by rfl⟩ : syracuseStep 1230569 = 922927) B922927
theorem B2770685 : Blo 546805 2770685 := bstep (se 3 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 2770685 = 1039007) B1039007
theorem B1230695 : Blo 546805 1230695 := bstep (se 1 (by rfl) ⟨923021, by rfl⟩ : syracuseStep 1230695 = 1846043) B1846043
theorem B1231343 : Blo 546805 1231343 := bstep (se 1 (by rfl) ⟨923507, by rfl⟩ : syracuseStep 1231343 = 1847015) B1847015
theorem B1231595 : Blo 546805 1231595 := bstep (se 1 (by rfl) ⟨923696, by rfl⟩ : syracuseStep 1231595 = 1847393) B1847393
theorem B1854305 : Blo 546805 1854305 := bstep (se 2 (by rfl) ⟨695364, by rfl⟩ : syracuseStep 1854305 = 1390729) B1390729
theorem B1232351 : Blo 546805 1232351 := bstep (se 1 (by rfl) ⟨924263, by rfl⟩ : syracuseStep 1232351 = 1848527) B1848527
theorem B740831 : Blo 546805 740831 := bstep (se 1 (by rfl) ⟨555623, by rfl⟩ : syracuseStep 740831 = 1111247) B1111247
theorem B2084393 : Blo 546805 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B6246071 : Blo 546805 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B1560539 : Blo 546805 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B1757323 : Blo 546805 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B3526847 : Blo 546805 3526847 := bstep (se 1 (by rfl) ⟨2645135, by rfl⟩ : syracuseStep 3526847 = 5290271) B5290271
theorem B2511071 : Blo 546805 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B1233863 : Blo 546805 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1233899 : Blo 546805 1233899 := bstep (se 1 (by rfl) ⟨925424, by rfl⟩ : syracuseStep 1233899 = 1850849) B1850849
theorem B2217095 : Blo 546805 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B1856951 : Blo 546805 1856951 := bstep (se 1 (by rfl) ⟨1392713, by rfl⟩ : syracuseStep 1856951 = 2785427) B2785427
theorem B2086505 : Blo 546805 2086505 := bstep (se 2 (by rfl) ⟨782439, by rfl⟩ : syracuseStep 2086505 = 1564879) B1564879
theorem B14079905 : Blo 546805 14079905 := bstep (se 2 (by rfl) ⟨5279964, by rfl⟩ : syracuseStep 14079905 = 10559929) B10559929
theorem B64018343 : Blo 546805 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B2348975 : Blo 546805 2348975 := bstep (se 1 (by rfl) ⟨1761731, by rfl⟩ : syracuseStep 2348975 = 3523463) B3523463
theorem B547055 : Blo 546805 547055 := bstep (se 1 (by rfl) ⟨410291, by rfl⟩ : syracuseStep 547055 = 820583) B820583
theorem B547135 : Blo 546805 547135 := bstep (se 1 (by rfl) ⟨410351, by rfl⟩ : syracuseStep 547135 = 820703) B820703
theorem B940487 : Blo 546805 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B547311 : Blo 546805 547311 := bstep (se 1 (by rfl) ⟨410483, by rfl⟩ : syracuseStep 547311 = 820967) B820967
theorem B1858031 : Blo 546805 1858031 := bstep (se 1 (by rfl) ⟨1393523, by rfl⟩ : syracuseStep 1858031 = 2787047) B2787047
theorem B2775869 : Blo 546805 2775869 := bstep (se 3 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 2775869 = 1040951) B1040951
theorem B3136319 : Blo 546805 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B1235951 : Blo 546805 1235951 := bstep (se 1 (by rfl) ⟨926963, by rfl⟩ : syracuseStep 1235951 = 1853927) B1853927
theorem B547835 : Blo 546805 547835 := bstep (se 1 (by rfl) ⟨410876, by rfl⟩ : syracuseStep 547835 = 821753) B821753
theorem B15817751 : Blo 546805 15817751 := bstep (se 1 (by rfl) ⟨11863313, by rfl⟩ : syracuseStep 15817751 = 23726627) B23726627
theorem B547867 : Blo 546805 547867 := bstep (se 1 (by rfl) ⟨410900, by rfl⟩ : syracuseStep 547867 = 821801) B821801
theorem B2087963 : Blo 546805 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B2776679 : Blo 546805 2776679 := bstep (se 1 (by rfl) ⟨2082509, by rfl⟩ : syracuseStep 2776679 = 4165019) B4165019
theorem B1564343 : Blo 546805 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B548711 : Blo 546805 548711 := bstep (se 1 (by rfl) ⟨411533, by rfl⟩ : syracuseStep 548711 = 823067) B823067
theorem B548767 : Blo 546805 548767 := bstep (se 1 (by rfl) ⟨411575, by rfl⟩ : syracuseStep 548767 = 823151) B823151
theorem B1237175 : Blo 546805 1237175 := bstep (se 1 (by rfl) ⟨927881, by rfl⟩ : syracuseStep 1237175 = 1855763) B1855763
theorem B549279 : Blo 546805 549279 := bstep (se 1 (by rfl) ⟨411959, by rfl⟩ : syracuseStep 549279 = 823919) B823919
theorem B549359 : Blo 546805 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B549735 : Blo 546805 549735 := bstep (se 1 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 549735 = 824603) B824603
theorem B2221195 : Blo 546805 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B550047 : Blo 546805 550047 := bstep (se 1 (by rfl) ⟨412535, by rfl⟩ : syracuseStep 550047 = 825071) B825071
theorem B5268665 : Blo 546805 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B9364733 : Blo 546805 9364733 := bstep (se 3 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 9364733 = 3511775) B3511775
theorem B1238327 : Blo 546805 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B615919 : Blo 546805 615919 := bstep (se 1 (by rfl) ⟨461939, by rfl⟩ : syracuseStep 615919 = 923879) B923879
theorem B1566337 : Blo 546805 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B3335975 : Blo 546805 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B1238867 : Blo 546805 1238867 := bstep (se 1 (by rfl) ⟨929150, by rfl⟩ : syracuseStep 1238867 = 1858301) B1858301
theorem B1042303 : Blo 546805 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B1042409 : Blo 546805 1042409 := bstep (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) B781807
theorem B10545713 : Blo 546805 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B47475395 : Blo 546805 47475395 := bstep (se 1 (by rfl) ⟨35606546, by rfl⟩ : syracuseStep 47475395 = 71213093) B71213093
theorem B2782835 : Blo 546805 2782835 := bstep (se 1 (by rfl) ⟨2087126, by rfl⟩ : syracuseStep 2782835 = 4174253) B4174253
theorem B4160159 : Blo 546805 4160159 := bstep (se 1 (by rfl) ⟨3120119, by rfl⟩ : syracuseStep 4160159 = 6240239) B6240239
theorem B16055333 : Blo 546805 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B5013011 : Blo 546805 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B1408679 : Blo 546805 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B5341099 : Blo 546805 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B4227335 : Blo 546805 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B5407175 : Blo 546805 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B15008287 : Blo 546805 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B820379 : Blo 546805 820379 := bstep (se 1 (by rfl) ⟨615284, by rfl⟩ : syracuseStep 820379 = 1230569) B1230569
theorem B820463 : Blo 546805 820463 := bstep (se 1 (by rfl) ⟨615347, by rfl⟩ : syracuseStep 820463 = 1230695) B1230695
theorem B820895 : Blo 546805 820895 := bstep (se 1 (by rfl) ⟨615671, by rfl⟩ : syracuseStep 820895 = 1231343) B1231343
theorem B821063 : Blo 546805 821063 := bstep (se 1 (by rfl) ⟨615797, by rfl⟩ : syracuseStep 821063 = 1231595) B1231595
theorem B15861581 : Blo 546805 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B821225 : Blo 546805 821225 := bstep (se 2 (by rfl) ⟨307959, by rfl⟩ : syracuseStep 821225 = 615919) B615919
theorem B821567 : Blo 546805 821567 := bstep (se 1 (by rfl) ⟨616175, by rfl⟩ : syracuseStep 821567 = 1232351) B1232351
theorem B4164047 : Blo 546805 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B1674047 : Blo 546805 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B822575 : Blo 546805 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B822599 : Blo 546805 822599 := bstep (se 1 (by rfl) ⟨616949, by rfl⟩ : syracuseStep 822599 = 1233899) B1233899
theorem B1478063 : Blo 546805 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B2494759 : Blo 546805 2494759 := bstep (se 1 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 2494759 = 3742139) B3742139
theorem B823967 : Blo 546805 823967 := bstep (se 1 (by rfl) ⟨617975, by rfl⟩ : syracuseStep 823967 = 1235951) B1235951
theorem B824783 : Blo 546805 824783 := bstep (se 1 (by rfl) ⟨618587, by rfl⟩ : syracuseStep 824783 = 1237175) B1237175
theorem B6657545 : Blo 546805 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B923177 : Blo 546805 923177 := bstep (se 2 (by rfl) ⟨346191, by rfl⟩ : syracuseStep 923177 = 692383) B692383
theorem B3512443 : Blo 546805 3512443 := bstep (se 1 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 3512443 = 5268665) B5268665
theorem B825551 : Blo 546805 825551 := bstep (se 1 (by rfl) ⟨619163, by rfl⟩ : syracuseStep 825551 = 1238327) B1238327
theorem B923899 : Blo 546805 923899 := bstep (se 1 (by rfl) ⟨692924, by rfl⟩ : syracuseStep 923899 = 1385849) B1385849
theorem B924007 : Blo 546805 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B825911 : Blo 546805 825911 := bstep (se 1 (by rfl) ⟨619433, by rfl⟩ : syracuseStep 825911 = 1238867) B1238867
theorem B990623 : Blo 546805 990623 := bstep (se 1 (by rfl) ⟨742967, by rfl⟩ : syracuseStep 990623 = 1485935) B1485935
theorem B1318369 : Blo 546805 1318369 := bstep (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) B988777
theorem B15867575 : Blo 546805 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B1187951 : Blo 546805 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B926633 : Blo 546805 926633 := bstep (se 2 (by rfl) ⟨347487, by rfl⟩ : syracuseStep 926633 = 694975) B694975
theorem B1385707 : Blo 546805 1385707 := bstep (se 1 (by rfl) ⟨1039280, by rfl⟩ : syracuseStep 1385707 = 2078561) B2078561
theorem B1975549 : Blo 546805 1975549 := bstep (se 3 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 1975549 = 740831) B740831
theorem B2631371 : Blo 546805 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B7939903 : Blo 546805 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B1845503 : Blo 546805 1845503 := bstep (se 1 (by rfl) ⟨1384127, by rfl⟩ : syracuseStep 1845503 = 2768255) B2768255
theorem B1845611 : Blo 546805 1845611 := bstep (se 1 (by rfl) ⟨1384208, by rfl⟩ : syracuseStep 1845611 = 2768417) B2768417
theorem B7121465 : Blo 546805 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B4173281 : Blo 546805 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B1847123 : Blo 546805 1847123 := bstep (se 1 (by rfl) ⟨1385342, by rfl⟩ : syracuseStep 1847123 = 2770685) B2770685
theorem B2961593 : Blo 546805 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1880263 : Blo 546805 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B1487263 : Blo 546805 1487263 := bstep (se 1 (by rfl) ⟨1115447, by rfl⟩ : syracuseStep 1487263 = 2230895) B2230895
theorem B1389595 : Blo 546805 1389595 := bstep (se 1 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 1389595 = 2084393) B2084393
theorem B1389737 : Blo 546805 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B1391003 : Blo 546805 1391003 := bstep (se 1 (by rfl) ⟨1043252, by rfl⟩ : syracuseStep 1391003 = 2086505) B2086505
theorem B9386603 : Blo 546805 9386603 := bstep (se 1 (by rfl) ⟨7039952, by rfl⟩ : syracuseStep 9386603 = 14079905) B14079905
theorem B42678895 : Blo 546805 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B4176683 : Blo 546805 4176683 := bstep (se 1 (by rfl) ⟨3132512, by rfl⟩ : syracuseStep 4176683 = 6265025) B6265025
theorem B1850579 : Blo 546805 1850579 := bstep (se 1 (by rfl) ⟨1387934, by rfl⟩ : syracuseStep 1850579 = 2775869) B2775869
theorem B91241777 : Blo 546805 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B1391975 : Blo 546805 1391975 := bstep (se 1 (by rfl) ⟨1043981, by rfl⟩ : syracuseStep 1391975 = 2087963) B2087963
theorem B1752607 : Blo 546805 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B1851119 : Blo 546805 1851119 := bstep (se 1 (by rfl) ⟨1388339, by rfl⟩ : syracuseStep 1851119 = 2776679) B2776679
theorem B2146331 : Blo 546805 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B2113633 : Blo 546805 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B2343097 : Blo 546805 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B6243155 : Blo 546805 6243155 := bstep (se 1 (by rfl) ⟨4682366, by rfl⟩ : syracuseStep 6243155 = 9364733) B9364733
theorem B2507965 : Blo 546805 2507965 := bstep (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) B940487
theorem B7030475 : Blo 546805 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B3950633 : Blo 546805 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B17090707 : Blo 546805 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B1231073 : Blo 546805 1231073 := bstep (se 2 (by rfl) ⟨461652, by rfl⟩ : syracuseStep 1231073 = 923305) B923305
theorem B1232567 : Blo 546805 1232567 := bstep (se 1 (by rfl) ⟨924425, by rfl⟩ : syracuseStep 1232567 = 1848851) B1848851
theorem B1855223 : Blo 546805 1855223 := bstep (se 1 (by rfl) ⟨1391417, by rfl⟩ : syracuseStep 1855223 = 2782835) B2782835
theorem B1232873 : Blo 546805 1232873 := bstep (se 2 (by rfl) ⟨462327, by rfl⟩ : syracuseStep 1232873 = 924655) B924655
theorem B8900603 : Blo 546805 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B10539017 : Blo 546805 10539017 := bstep (se 2 (by rfl) ⟨3952131, by rfl⟩ : syracuseStep 10539017 = 7904263) B7904263
theorem B28987409 : Blo 546805 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B2773439 : Blo 546805 2773439 := bstep (se 1 (by rfl) ⟨2080079, by rfl⟩ : syracuseStep 2773439 = 4160159) B4160159
theorem B4182515 : Blo 546805 4182515 := bstep (se 1 (by rfl) ⟨3136886, by rfl⟩ : syracuseStep 4182515 = 6273773) B6273773
theorem B10703555 : Blo 546805 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B3527563 : Blo 546805 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B939119 : Blo 546805 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B5920073 : Blo 546805 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B1038271 : Blo 546805 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B1759259 : Blo 546805 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B546879 : Blo 546805 546879 := bstep (se 1 (by rfl) ⟨410159, by rfl⟩ : syracuseStep 546879 = 820319) B820319
theorem B1235015 : Blo 546805 1235015 := bstep (se 1 (by rfl) ⟨926261, by rfl⟩ : syracuseStep 1235015 = 1852523) B1852523
theorem B1235051 : Blo 546805 1235051 := bstep (se 1 (by rfl) ⟨926288, by rfl⟩ : syracuseStep 1235051 = 1852577) B1852577
theorem B547023 : Blo 546805 547023 := bstep (se 1 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 547023 = 820535) B820535
theorem B547775 : Blo 546805 547775 := bstep (se 1 (by rfl) ⟨410831, by rfl⟩ : syracuseStep 547775 = 821663) B821663
theorem B1236203 : Blo 546805 1236203 := bstep (se 1 (by rfl) ⟨927152, by rfl⟩ : syracuseStep 1236203 = 1854305) B1854305
theorem B1858841 : Blo 546805 1858841 := bstep (se 2 (by rfl) ⟨697065, by rfl⟩ : syracuseStep 1858841 = 1394131) B1394131
theorem B2088449 : Blo 546805 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B2317871 : Blo 546805 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B548455 : Blo 546805 548455 := bstep (se 1 (by rfl) ⟨411341, by rfl⟩ : syracuseStep 548455 = 822683) B822683
theorem B1236617 : Blo 546805 1236617 := bstep (se 2 (by rfl) ⟨463731, by rfl⟩ : syracuseStep 1236617 = 927463) B927463
theorem B1040359 : Blo 546805 1040359 := bstep (se 1 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 1040359 = 1560539) B1560539
theorem B2351231 : Blo 546805 2351231 := bstep (se 1 (by rfl) ⟨1763423, by rfl⟩ : syracuseStep 2351231 = 3526847) B3526847
theorem B3956951 : Blo 546805 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B549223 : Blo 546805 549223 := bstep (se 1 (by rfl) ⟨411917, by rfl⟩ : syracuseStep 549223 = 823835) B823835
theorem B549467 : Blo 546805 549467 := bstep (se 1 (by rfl) ⟨412100, by rfl⟩ : syracuseStep 549467 = 824201) B824201
theorem B549627 : Blo 546805 549627 := bstep (se 1 (by rfl) ⟨412220, by rfl⟩ : syracuseStep 549627 = 824441) B824441
theorem B1237967 : Blo 546805 1237967 := bstep (se 1 (by rfl) ⟨928475, by rfl⟩ : syracuseStep 1237967 = 1856951) B1856951
theorem B7529705 : Blo 546805 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B550143 : Blo 546805 550143 := bstep (se 1 (by rfl) ⟨412607, by rfl⟩ : syracuseStep 550143 = 825215) B825215
theorem B1565983 : Blo 546805 1565983 := bstep (se 1 (by rfl) ⟨1174487, by rfl⟩ : syracuseStep 1565983 = 2348975) B2348975
theorem B550271 : Blo 546805 550271 := bstep (se 1 (by rfl) ⟨412703, by rfl⟩ : syracuseStep 550271 = 825407) B825407
theorem B550383 : Blo 546805 550383 := bstep (se 1 (by rfl) ⟨412787, by rfl⟩ : syracuseStep 550383 = 825575) B825575
theorem B616027 : Blo 546805 616027 := bstep (se 1 (by rfl) ⟨462020, by rfl⟩ : syracuseStep 616027 = 924041) B924041
theorem B550491 : Blo 546805 550491 := bstep (se 1 (by rfl) ⟨412868, by rfl⟩ : syracuseStep 550491 = 825737) B825737
theorem B1238687 : Blo 546805 1238687 := bstep (se 1 (by rfl) ⟨929015, by rfl⟩ : syracuseStep 1238687 = 1858031) B1858031
theorem B2090879 : Blo 546805 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B10545167 : Blo 546805 10545167 := bstep (se 1 (by rfl) ⟨7908875, by rfl⟩ : syracuseStep 10545167 = 15817751) B15817751
theorem B878759 : Blo 546805 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B1042895 : Blo 546805 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B2779757 : Blo 546805 2779757 := bstep (se 3 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 2779757 = 1042409) B1042409
theorem B617071 : Blo 546805 617071 := bstep (se 1 (by rfl) ⟨462803, by rfl⟩ : syracuseStep 617071 = 925607) B925607
theorem B617935 : Blo 546805 617935 := bstep (se 1 (by rfl) ⟨463451, by rfl⟩ : syracuseStep 617935 = 926903) B926903
theorem B2223983 : Blo 546805 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B31650263 : Blo 546805 31650263 := bstep (se 1 (by rfl) ⟨23737697, by rfl⟩ : syracuseStep 31650263 = 47475395) B47475395
theorem B5272127 : Blo 546805 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B3961819 : Blo 546805 3961819 := bstep (se 1 (by rfl) ⟨2971364, by rfl⟩ : syracuseStep 3961819 = 5942729) B5942729
theorem B4161131 : Blo 546805 4161131 := bstep (se 1 (by rfl) ⟨3120848, by rfl⟩ : syracuseStep 4161131 = 6241697) B6241697
theorem B3342007 : Blo 546805 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B77299757 : Blo 546805 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B2818223 : Blo 546805 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B11272709 : Blo 546805 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B4162103 : Blo 546805 4162103 := bstep (se 1 (by rfl) ⟨3121577, by rfl⟩ : syracuseStep 4162103 = 6243155) B6243155
theorem B10028069 : Blo 546805 10028069 := bstep (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) B1880263
theorem B4686983 : Blo 546805 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B14419133 : Blo 546805 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B820715 : Blo 546805 820715 := bstep (se 1 (by rfl) ⟨615536, by rfl⟩ : syracuseStep 820715 = 1231073) B1231073
theorem B1116031 : Blo 546805 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B821369 : Blo 546805 821369 := bstep (se 2 (by rfl) ⟨308013, by rfl⟩ : syracuseStep 821369 = 616027) B616027
theorem B985375 : Blo 546805 985375 := bstep (se 1 (by rfl) ⟨739031, by rfl⟩ : syracuseStep 985375 = 1478063) B1478063
theorem B10586537 : Blo 546805 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B821711 : Blo 546805 821711 := bstep (se 1 (by rfl) ⟨616283, by rfl⟩ : syracuseStep 821711 = 1232567) B1232567
theorem B821915 : Blo 546805 821915 := bstep (se 1 (by rfl) ⟨616436, by rfl⟩ : syracuseStep 821915 = 1232873) B1232873
theorem B5933735 : Blo 546805 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B2788343 : Blo 546805 2788343 := bstep (se 1 (by rfl) ⟨2091257, by rfl⟩ : syracuseStep 2788343 = 4182515) B4182515
theorem B822761 : Blo 546805 822761 := bstep (se 2 (by rfl) ⟨308535, by rfl⟩ : syracuseStep 822761 = 617071) B617071
theorem B823343 : Blo 546805 823343 := bstep (se 1 (by rfl) ⟨617507, by rfl⟩ : syracuseStep 823343 = 1235015) B1235015
theorem B823367 : Blo 546805 823367 := bstep (se 1 (by rfl) ⟨617525, by rfl⟩ : syracuseStep 823367 = 1235051) B1235051
theorem B7016989 : Blo 546805 7016989 := bstep (se 3 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 7016989 = 2631371) B2631371
theorem B823913 : Blo 546805 823913 := bstep (se 2 (by rfl) ⟨308967, by rfl⟩ : syracuseStep 823913 = 617935) B617935
theorem B824135 : Blo 546805 824135 := bstep (se 1 (by rfl) ⟨618101, by rfl⟩ : syracuseStep 824135 = 1236203) B1236203
theorem B660415 : Blo 546805 660415 := bstep (se 1 (by rfl) ⟨495311, by rfl⟩ : syracuseStep 660415 = 990623) B990623
theorem B1545247 : Blo 546805 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B824411 : Blo 546805 824411 := bstep (se 1 (by rfl) ⟨618308, by rfl⟩ : syracuseStep 824411 = 1236617) B1236617
theorem B4691357 : Blo 546805 4691357 := bstep (se 3 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 4691357 = 1759259) B1759259
theorem B825311 : Blo 546805 825311 := bstep (se 1 (by rfl) ⟨618983, by rfl⟩ : syracuseStep 825311 = 1237967) B1237967
theorem B5019803 : Blo 546805 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B13375813 : Blo 546805 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B825791 : Blo 546805 825791 := bstep (se 1 (by rfl) ⟨619343, by rfl⟩ : syracuseStep 825791 = 1238687) B1238687
theorem B5282425 : Blo 546805 5282425 := bstep (se 2 (by rfl) ⟨1980909, by rfl⟩ : syracuseStep 5282425 = 3961819) B3961819
theorem B1384361 : Blo 546805 1384361 := bstep (se 2 (by rfl) ⟨519135, by rfl⟩ : syracuseStep 1384361 = 1038271) B1038271
theorem B1974395 : Blo 546805 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B9347237 : Blo 546805 9347237 := bstep (se 4 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 9347237 = 1752607) B1752607
theorem B3514751 : Blo 546805 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B926491 : Blo 546805 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B927335 : Blo 546805 927335 := bstep (se 1 (by rfl) ⟨695501, by rfl⟩ : syracuseStep 927335 = 1391003) B1391003
theorem B60827851 : Blo 546805 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B927983 : Blo 546805 927983 := bstep (se 1 (by rfl) ⟨695987, by rfl⟩ : syracuseStep 927983 = 1391975) B1391975
theorem B1387145 : Blo 546805 1387145 := bstep (se 2 (by rfl) ⟨520179, by rfl⟩ : syracuseStep 1387145 = 1040359) B1040359
theorem B3124129 : Blo 546805 3124129 := bstep (se 2 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 3124129 = 2343097) B2343097
theorem B1847609 : Blo 546805 1847609 := bstep (se 2 (by rfl) ⟨692853, by rfl⟩ : syracuseStep 1847609 = 1385707) B1385707
theorem B2634065 : Blo 546805 2634065 := bstep (se 2 (by rfl) ⟨987774, by rfl⟩ : syracuseStep 2634065 = 1975549) B1975549
theorem B7026011 : Blo 546805 7026011 := bstep (se 1 (by rfl) ⟨5269508, by rfl⟩ : syracuseStep 7026011 = 10539017) B10539017
theorem B22787609 : Blo 546805 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B2504317 : Blo 546805 2504317 := bstep (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) B939119
theorem B1848959 : Blo 546805 1848959 := bstep (se 1 (by rfl) ⟨1386719, by rfl⟩ : syracuseStep 1848959 = 2773439) B2773439
theorem B3946715 : Blo 546805 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B4438363 : Blo 546805 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B1392299 : Blo 546805 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B10535021 : Blo 546805 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B2637967 : Blo 546805 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B3326345 : Blo 546805 3326345 := bstep (se 2 (by rfl) ⟨1247379, by rfl⟩ : syracuseStep 3326345 = 2494759) B2494759
theorem B1983017 : Blo 546805 1983017 := bstep (se 2 (by rfl) ⟨743631, by rfl⟩ : syracuseStep 1983017 = 1487263) B1487263
theorem B4703417 : Blo 546805 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B1393919 : Blo 546805 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B7030111 : Blo 546805 7030111 := bstep (se 1 (by rfl) ⟨5272583, by rfl⟩ : syracuseStep 7030111 = 10545167) B10545167
theorem B1852793 : Blo 546805 1852793 := bstep (se 2 (by rfl) ⟨694797, by rfl⟩ : syracuseStep 1852793 = 1389595) B1389595
theorem B1230335 : Blo 546805 1230335 := bstep (se 1 (by rfl) ⟨922751, by rfl⟩ : syracuseStep 1230335 = 1845503) B1845503
theorem B1230407 : Blo 546805 1230407 := bstep (se 1 (by rfl) ⟨922805, by rfl⟩ : syracuseStep 1230407 = 1845611) B1845611
theorem B1853171 : Blo 546805 1853171 := bstep (se 1 (by rfl) ⟨1389878, by rfl⟩ : syracuseStep 1853171 = 2779757) B2779757
theorem B1231415 : Blo 546805 1231415 := bstep (se 1 (by rfl) ⟨923561, by rfl⟩ : syracuseStep 1231415 = 1847123) B1847123
theorem B1231865 : Blo 546805 1231865 := bstep (se 2 (by rfl) ⟨461949, by rfl⟩ : syracuseStep 1231865 = 923899) B923899
theorem B1232009 : Blo 546805 1232009 := bstep (se 2 (by rfl) ⟨462003, by rfl⟩ : syracuseStep 1232009 = 924007) B924007
theorem B56905193 : Blo 546805 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B1757825 : Blo 546805 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B1233719 : Blo 546805 1233719 := bstep (se 1 (by rfl) ⟨925289, by rfl⟩ : syracuseStep 1233719 = 1850579) B1850579
theorem B2774087 : Blo 546805 2774087 := bstep (se 1 (by rfl) ⟨2080565, by rfl⟩ : syracuseStep 2774087 = 4161131) B4161131
theorem B1234079 : Blo 546805 1234079 := bstep (se 1 (by rfl) ⟨925559, by rfl⟩ : syracuseStep 1234079 = 1851119) B1851119
theorem B1430887 : Blo 546805 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B20011049 : Blo 546805 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B546919 : Blo 546805 546919 := bstep (se 1 (by rfl) ⟨410189, by rfl⟩ : syracuseStep 546919 = 820379) B820379
theorem B546975 : Blo 546805 546975 := bstep (se 1 (by rfl) ⟨410231, by rfl⟩ : syracuseStep 546975 = 820463) B820463
theorem B547263 : Blo 546805 547263 := bstep (se 1 (by rfl) ⟨410447, by rfl⟩ : syracuseStep 547263 = 820895) B820895
theorem B12671477 : Blo 546805 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B547375 : Blo 546805 547375 := bstep (se 1 (by rfl) ⟨410531, by rfl⟩ : syracuseStep 547375 = 821063) B821063
theorem B10574387 : Blo 546805 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B547483 : Blo 546805 547483 := bstep (se 1 (by rfl) ⟨410612, by rfl⟩ : syracuseStep 547483 = 821225) B821225
theorem B547711 : Blo 546805 547711 := bstep (se 1 (by rfl) ⟨410783, by rfl⟩ : syracuseStep 547711 = 821567) B821567
theorem B2776031 : Blo 546805 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B2087977 : Blo 546805 2087977 := bstep (se 2 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 2087977 = 1565983) B1565983
theorem B548383 : Blo 546805 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B548399 : Blo 546805 548399 := bstep (se 1 (by rfl) ⟨411299, by rfl⟩ : syracuseStep 548399 = 822599) B822599
theorem B1236815 : Blo 546805 1236815 := bstep (se 1 (by rfl) ⟨927611, by rfl⟩ : syracuseStep 1236815 = 1855223) B1855223
theorem B549311 : Blo 546805 549311 := bstep (se 1 (by rfl) ⟨411983, by rfl⟩ : syracuseStep 549311 = 823967) B823967
theorem B7135703 : Blo 546805 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B549855 : Blo 546805 549855 := bstep (se 1 (by rfl) ⟨412391, by rfl⟩ : syracuseStep 549855 = 824783) B824783
theorem B615451 : Blo 546805 615451 := bstep (se 1 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 615451 = 923177) B923177
theorem B550367 : Blo 546805 550367 := bstep (se 1 (by rfl) ⟨412775, by rfl⟩ : syracuseStep 550367 = 825551) B825551
theorem B550607 : Blo 546805 550607 := bstep (se 1 (by rfl) ⟨412955, by rfl⟩ : syracuseStep 550607 = 825911) B825911
theorem B1239227 : Blo 546805 1239227 := bstep (se 1 (by rfl) ⟨929420, by rfl⟩ : syracuseStep 1239227 = 1858841) B1858841
theorem B10578383 : Blo 546805 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B1567487 : Blo 546805 1567487 := bstep (se 1 (by rfl) ⟨1175615, by rfl⟩ : syracuseStep 1567487 = 2351231) B2351231
theorem B617755 : Blo 546805 617755 := bstep (se 1 (by rfl) ⟨463316, by rfl⟩ : syracuseStep 617755 = 926633) B926633
theorem B2781053 : Blo 546805 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B585839 : Blo 546805 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B4747643 : Blo 546805 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B2782187 : Blo 546805 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B4683257 : Blo 546805 4683257 := bstep (se 2 (by rfl) ⟨1756221, by rfl⟩ : syracuseStep 4683257 = 3512443) B3512443
theorem B21100175 : Blo 546805 21100175 := bstep (se 1 (by rfl) ⟨15825131, by rfl⟩ : syracuseStep 21100175 = 31650263) B31650263
theorem B6257735 : Blo 546805 6257735 := bstep (se 1 (by rfl) ⟨4693301, by rfl⟩ : syracuseStep 6257735 = 9386603) B9386603
theorem B2784455 : Blo 546805 2784455 := bstep (se 1 (by rfl) ⟨2088341, by rfl⟩ : syracuseStep 2784455 = 4176683) B4176683
theorem B4456009 : Blo 546805 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B5930621 : Blo 546805 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B6685379 : Blo 546805 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B820223 : Blo 546805 820223 := bstep (se 1 (by rfl) ⟨615167, by rfl⟩ : syracuseStep 820223 = 1230335) B1230335
theorem B820271 : Blo 546805 820271 := bstep (se 1 (by rfl) ⟨615203, by rfl⟩ : syracuseStep 820271 = 1230407) B1230407
theorem B820601 : Blo 546805 820601 := bstep (se 2 (by rfl) ⟨307725, by rfl⟩ : syracuseStep 820601 = 615451) B615451
theorem B820943 : Blo 546805 820943 := bstep (se 1 (by rfl) ⟨615707, by rfl⟩ : syracuseStep 820943 = 1231415) B1231415
theorem B9373481 : Blo 546805 9373481 := bstep (se 2 (by rfl) ⟨3515055, by rfl⟩ : syracuseStep 9373481 = 7030111) B7030111
theorem B821243 : Blo 546805 821243 := bstep (se 1 (by rfl) ⟨615932, by rfl⟩ : syracuseStep 821243 = 1231865) B1231865
theorem B821339 : Blo 546805 821339 := bstep (se 1 (by rfl) ⟨616004, by rfl⟩ : syracuseStep 821339 = 1232009) B1232009
theorem B81103801 : Blo 546805 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B1313833 : Blo 546805 1313833 := bstep (se 2 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 1313833 = 985375) B985375
theorem B822479 : Blo 546805 822479 := bstep (se 1 (by rfl) ⟨616859, by rfl⟩ : syracuseStep 822479 = 1233719) B1233719
theorem B822719 : Blo 546805 822719 := bstep (se 1 (by rfl) ⟨617039, by rfl⟩ : syracuseStep 822719 = 1234079) B1234079
theorem B4165505 : Blo 546805 4165505 := bstep (se 2 (by rfl) ⟨1562064, by rfl⟩ : syracuseStep 4165505 = 3124129) B3124129
theorem B13340699 : Blo 546805 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B3346535 : Blo 546805 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B7049591 : Blo 546805 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B823673 : Blo 546805 823673 := bstep (se 2 (by rfl) ⟨308877, by rfl⟩ : syracuseStep 823673 = 617755) B617755
theorem B824543 : Blo 546805 824543 := bstep (se 1 (by rfl) ⟨618407, by rfl⟩ : syracuseStep 824543 = 1236815) B1236815
theorem B922907 : Blo 546805 922907 := bstep (se 1 (by rfl) ⟨692180, by rfl⟩ : syracuseStep 922907 = 1384361) B1384361
theorem B1316263 : Blo 546805 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B6231491 : Blo 546805 6231491 := bstep (se 1 (by rfl) ⟨4673618, by rfl⟩ : syracuseStep 6231491 = 9347237) B9347237
theorem B4757135 : Blo 546805 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B826151 : Blo 546805 826151 := bstep (se 1 (by rfl) ⟨619613, by rfl⟩ : syracuseStep 826151 = 1239227) B1239227
theorem B7052255 : Blo 546805 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B924763 : Blo 546805 924763 := bstep (se 1 (by rfl) ⟨693572, by rfl⟩ : syracuseStep 924763 = 1387145) B1387145
theorem B1907849 : Blo 546805 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B17834417 : Blo 546805 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B3122171 : Blo 546805 3122171 := bstep (se 1 (by rfl) ⟨2341628, by rfl⟩ : syracuseStep 3122171 = 4683257) B4683257
theorem B14066783 : Blo 546805 14066783 := bstep (se 1 (by rfl) ⟨10550087, by rfl⟩ : syracuseStep 14066783 = 21100175) B21100175
theorem B2631143 : Blo 546805 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B4171823 : Blo 546805 4171823 := bstep (se 1 (by rfl) ⟨3128867, by rfl⟩ : syracuseStep 4171823 = 6257735) B6257735
theorem B5941345 : Blo 546805 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B928199 : Blo 546805 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B7023347 : Blo 546805 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B1878815 : Blo 546805 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B3517289 : Blo 546805 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B1322011 : Blo 546805 1322011 := bstep (se 1 (by rfl) ⟨991508, by rfl⟩ : syracuseStep 1322011 = 1983017) B1983017
theorem B3124655 : Blo 546805 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B9612755 : Blo 546805 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B929279 : Blo 546805 929279 := bstep (se 1 (by rfl) ⟨696959, by rfl⟩ : syracuseStep 929279 = 1393919) B1393919
theorem B30060557 : Blo 546805 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B7057691 : Blo 546805 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B1488041 : Blo 546805 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1849391 : Blo 546805 1849391 := bstep (se 1 (by rfl) ⟨1387043, by rfl⟩ : syracuseStep 1849391 = 2774087) B2774087
theorem B3127571 : Blo 546805 3127571 := bstep (se 1 (by rfl) ⟨2345678, by rfl⟩ : syracuseStep 3127571 = 4691357) B4691357
theorem B60766957 : Blo 546805 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B1850687 : Blo 546805 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B2343167 : Blo 546805 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B9355985 : Blo 546805 9355985 := bstep (se 2 (by rfl) ⟨3508494, by rfl⟩ : syracuseStep 9355985 = 7016989) B7016989
theorem B1854035 : Blo 546805 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B1231739 : Blo 546805 1231739 := bstep (se 1 (by rfl) ⟨923804, by rfl⟩ : syracuseStep 1231739 = 1847609) B1847609
theorem B1756043 : Blo 546805 1756043 := bstep (se 1 (by rfl) ⟨1317032, by rfl⟩ : syracuseStep 1756043 = 2634065) B2634065
theorem B3165095 : Blo 546805 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B5917817 : Blo 546805 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B1854791 : Blo 546805 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B1232639 : Blo 546805 1232639 := bstep (se 1 (by rfl) ⟨924479, by rfl⟩ : syracuseStep 1232639 = 1848959) B1848959
theorem B1856303 : Blo 546805 1856303 := bstep (se 1 (by rfl) ⟨1392227, by rfl⟩ : syracuseStep 1856303 = 2784455) B2784455
theorem B3953747 : Blo 546805 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B51533171 : Blo 546805 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B2217563 : Blo 546805 2217563 := bstep (se 1 (by rfl) ⟨1663172, by rfl⟩ : syracuseStep 2217563 = 3326345) B3326345
theorem B1562237 : Blo 546805 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B2774735 : Blo 546805 2774735 := bstep (se 1 (by rfl) ⟨2081051, by rfl⟩ : syracuseStep 2774735 = 4162103) B4162103
theorem B3135611 : Blo 546805 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B1235195 : Blo 546805 1235195 := bstep (se 1 (by rfl) ⟨926396, by rfl⟩ : syracuseStep 1235195 = 1852793) B1852793
theorem B547143 : Blo 546805 547143 := bstep (se 1 (by rfl) ⟨410357, by rfl⟩ : syracuseStep 547143 = 820715) B820715
theorem B1235321 : Blo 546805 1235321 := bstep (se 2 (by rfl) ⟨463245, by rfl⟩ : syracuseStep 1235321 = 926491) B926491
theorem B1235447 : Blo 546805 1235447 := bstep (se 1 (by rfl) ⟨926585, by rfl⟩ : syracuseStep 1235447 = 1853171) B1853171
theorem B547579 : Blo 546805 547579 := bstep (se 1 (by rfl) ⟨410684, by rfl⟩ : syracuseStep 547579 = 821369) B821369
theorem B547807 : Blo 546805 547807 := bstep (se 1 (by rfl) ⟨410855, by rfl⟩ : syracuseStep 547807 = 821711) B821711
theorem B547943 : Blo 546805 547943 := bstep (se 1 (by rfl) ⟨410957, by rfl⟩ : syracuseStep 547943 = 821915) B821915
theorem B3955823 : Blo 546805 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B1858895 : Blo 546805 1858895 := bstep (se 1 (by rfl) ⟨1394171, by rfl⟩ : syracuseStep 1858895 = 2788343) B2788343
theorem B37936795 : Blo 546805 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B548507 : Blo 546805 548507 := bstep (se 1 (by rfl) ⟨411380, by rfl⟩ : syracuseStep 548507 = 822761) B822761
theorem B548895 : Blo 546805 548895 := bstep (se 1 (by rfl) ⟨411671, by rfl⟩ : syracuseStep 548895 = 823343) B823343
theorem B548911 : Blo 546805 548911 := bstep (se 1 (by rfl) ⟨411683, by rfl⟩ : syracuseStep 548911 = 823367) B823367
theorem B549275 : Blo 546805 549275 := bstep (se 1 (by rfl) ⟨411956, by rfl⟩ : syracuseStep 549275 = 823913) B823913
theorem B1171883 : Blo 546805 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B549423 : Blo 546805 549423 := bstep (se 1 (by rfl) ⟨412067, by rfl⟩ : syracuseStep 549423 = 824135) B824135
theorem B549607 : Blo 546805 549607 := bstep (se 1 (by rfl) ⟨412205, by rfl⟩ : syracuseStep 549607 = 824411) B824411
theorem B550207 : Blo 546805 550207 := bstep (se 1 (by rfl) ⟨412655, by rfl⟩ : syracuseStep 550207 = 825311) B825311
theorem B550527 : Blo 546805 550527 := bstep (se 1 (by rfl) ⟨412895, by rfl⟩ : syracuseStep 550527 = 825791) B825791
theorem B8447651 : Blo 546805 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B618223 : Blo 546805 618223 := bstep (se 1 (by rfl) ⟨463667, by rfl⟩ : syracuseStep 618223 = 927335) B927335
theorem B880553 : Blo 546805 880553 := bstep (se 2 (by rfl) ⟨330207, by rfl⟩ : syracuseStep 880553 = 660415) B660415
theorem B2060329 : Blo 546805 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B618655 : Blo 546805 618655 := bstep (se 1 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 618655 = 927983) B927983
theorem B1044991 : Blo 546805 1044991 := bstep (se 1 (by rfl) ⟨783743, by rfl⟩ : syracuseStep 1044991 = 1567487) B1567487
theorem B3339089 : Blo 546805 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B7043233 : Blo 546805 7043233 := bstep (se 2 (by rfl) ⟨2641212, by rfl⟩ : syracuseStep 7043233 = 5282425) B5282425
theorem B4684007 : Blo 546805 4684007 := bstep (se 1 (by rfl) ⟨3513005, by rfl⟩ : syracuseStep 4684007 = 7026011) B7026011
theorem B2783969 : Blo 546805 2783969 := bstep (se 2 (by rfl) ⟨1043988, by rfl⟩ : syracuseStep 2783969 = 2087977) B2087977
theorem B4456919 : Blo 546805 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B821159 : Blo 546805 821159 := bstep (se 1 (by rfl) ⟨615869, by rfl⟩ : syracuseStep 821159 = 1231739) B1231739
theorem B821759 : Blo 546805 821759 := bstep (se 1 (by rfl) ⟨616319, by rfl⟩ : syracuseStep 821759 = 1232639) B1232639
theorem B2231023 : Blo 546805 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B1478375 : Blo 546805 1478375 := bstep (se 1 (by rfl) ⟨1108781, by rfl⟩ : syracuseStep 1478375 = 2217563) B2217563
theorem B108138401 : Blo 546805 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B823463 : Blo 546805 823463 := bstep (se 1 (by rfl) ⟨617597, by rfl⟩ : syracuseStep 823463 = 1235195) B1235195
theorem B823547 : Blo 546805 823547 := bstep (se 1 (by rfl) ⟨617660, by rfl⟩ : syracuseStep 823547 = 1235321) B1235321
theorem B823631 : Blo 546805 823631 := bstep (se 1 (by rfl) ⟨617723, by rfl⟩ : syracuseStep 823631 = 1235447) B1235447
theorem B824297 : Blo 546805 824297 := bstep (se 2 (by rfl) ⟨309111, by rfl⟩ : syracuseStep 824297 = 618223) B618223
theorem B824873 : Blo 546805 824873 := bstep (se 2 (by rfl) ⟨309327, by rfl⟩ : syracuseStep 824873 = 618655) B618655
theorem B9377855 : Blo 546805 9377855 := bstep (se 1 (by rfl) ⟨7033391, by rfl⟩ : syracuseStep 9377855 = 14066783) B14066783
theorem B992027 : Blo 546805 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B3122671 : Blo 546805 3122671 := bstep (se 1 (by rfl) ⟨2342003, by rfl⟩ : syracuseStep 3122671 = 4684007) B4684007
theorem B6237323 : Blo 546805 6237323 := bstep (se 1 (by rfl) ⟨4677992, by rfl⟩ : syracuseStep 6237323 = 9355985) B9355985
theorem B2110063 : Blo 546805 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B8893799 : Blo 546805 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B4699727 : Blo 546805 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B2635831 : Blo 546805 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B34355447 : Blo 546805 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B1849823 : Blo 546805 1849823 := bstep (se 1 (by rfl) ⟨1387367, by rfl⟩ : syracuseStep 1849823 = 2774735) B2774735
theorem B1751777 : Blo 546805 1751777 := bstep (se 2 (by rfl) ⟨656916, by rfl⟩ : syracuseStep 1751777 = 1313833) B1313833
theorem B4701503 : Blo 546805 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B2637215 : Blo 546805 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B2081447 : Blo 546805 2081447 := bstep (se 1 (by rfl) ⟨1561085, by rfl⟩ : syracuseStep 2081447 = 3122171) B3122171
theorem B1393321 : Blo 546805 1393321 := bstep (se 2 (by rfl) ⟨522495, by rfl⟩ : syracuseStep 1393321 = 1044991) B1044991
theorem B1754095 : Blo 546805 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B50742773 : Blo 546805 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B1755017 : Blo 546805 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B2344859 : Blo 546805 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B2083103 : Blo 546805 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B6408503 : Blo 546805 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B20040371 : Blo 546805 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B4705127 : Blo 546805 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B9390977 : Blo 546805 9390977 := bstep (se 2 (by rfl) ⟨3521616, by rfl⟩ : syracuseStep 9390977 = 7043233) B7043233
theorem B15780845 : Blo 546805 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B81022609 : Blo 546805 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B1232927 : Blo 546805 1232927 := bstep (se 1 (by rfl) ⟨924695, by rfl⟩ : syracuseStep 1232927 = 1849391) B1849391
theorem B1233017 : Blo 546805 1233017 := bstep (se 2 (by rfl) ⟨462381, by rfl⟩ : syracuseStep 1233017 = 924763) B924763
theorem B2085047 : Blo 546805 2085047 := bstep (se 1 (by rfl) ⟨1563785, by rfl⟩ : syracuseStep 2085047 = 3127571) B3127571
theorem B1855979 : Blo 546805 1855979 := bstep (se 1 (by rfl) ⟨1391984, by rfl⟩ : syracuseStep 1855979 = 2783969) B2783969
theorem B50582393 : Blo 546805 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B1233791 : Blo 546805 1233791 := bstep (se 1 (by rfl) ⟨925343, by rfl⟩ : syracuseStep 1233791 = 1850687) B1850687
theorem B1562111 : Blo 546805 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B546815 : Blo 546805 546815 := bstep (se 1 (by rfl) ⟨410111, by rfl⟩ : syracuseStep 546815 = 820223) B820223
theorem B546847 : Blo 546805 546847 := bstep (se 1 (by rfl) ⟨410135, by rfl⟩ : syracuseStep 546847 = 820271) B820271
theorem B547067 : Blo 546805 547067 := bstep (se 1 (by rfl) ⟨410300, by rfl⟩ : syracuseStep 547067 = 820601) B820601
theorem B547295 : Blo 546805 547295 := bstep (se 1 (by rfl) ⟨410471, by rfl⟩ : syracuseStep 547295 = 820943) B820943
theorem B6248987 : Blo 546805 6248987 := bstep (se 1 (by rfl) ⟨4686740, by rfl⟩ : syracuseStep 6248987 = 9373481) B9373481
theorem B547495 : Blo 546805 547495 := bstep (se 1 (by rfl) ⟨410621, by rfl⟩ : syracuseStep 547495 = 821243) B821243
theorem B547559 : Blo 546805 547559 := bstep (se 1 (by rfl) ⟨410669, by rfl⟩ : syracuseStep 547559 = 821339) B821339
theorem B1236023 : Blo 546805 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B1170695 : Blo 546805 1170695 := bstep (se 1 (by rfl) ⟨878021, by rfl⟩ : syracuseStep 1170695 = 1756043) B1756043
theorem B548319 : Blo 546805 548319 := bstep (se 1 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 548319 = 822479) B822479
theorem B1236527 : Blo 546805 1236527 := bstep (se 1 (by rfl) ⟨927395, by rfl⟩ : syracuseStep 1236527 = 1854791) B1854791
theorem B548479 : Blo 546805 548479 := bstep (se 1 (by rfl) ⟨411359, by rfl⟩ : syracuseStep 548479 = 822719) B822719
theorem B2777003 : Blo 546805 2777003 := bstep (se 1 (by rfl) ⟨2082752, by rfl⟩ : syracuseStep 2777003 = 4165505) B4165505
theorem B7921793 : Blo 546805 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B549115 : Blo 546805 549115 := bstep (se 1 (by rfl) ⟨411836, by rfl⟩ : syracuseStep 549115 = 823673) B823673
theorem B1237535 : Blo 546805 1237535 := bstep (se 1 (by rfl) ⟨928151, by rfl⟩ : syracuseStep 1237535 = 1856303) B1856303
theorem B549695 : Blo 546805 549695 := bstep (se 1 (by rfl) ⟨412271, by rfl⟩ : syracuseStep 549695 = 824543) B824543
theorem B615271 : Blo 546805 615271 := bstep (se 1 (by rfl) ⟨461453, by rfl⟩ : syracuseStep 615271 = 922907) B922907
theorem B4154327 : Blo 546805 4154327 := bstep (se 1 (by rfl) ⟨3115745, by rfl⟩ : syracuseStep 4154327 = 6231491) B6231491
theorem B1041491 : Blo 546805 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B1762681 : Blo 546805 1762681 := bstep (se 2 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 1762681 = 1322011) B1322011
theorem B2090407 : Blo 546805 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B550767 : Blo 546805 550767 := bstep (se 1 (by rfl) ⟨413075, by rfl⟩ : syracuseStep 550767 = 826151) B826151
theorem B1271899 : Blo 546805 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B1239263 : Blo 546805 1239263 := bstep (se 1 (by rfl) ⟨929447, by rfl⟩ : syracuseStep 1239263 = 1858895) B1858895
theorem B2747105 : Blo 546805 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B781255 : Blo 546805 781255 := bstep (se 1 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 781255 = 1171883) B1171883
theorem B11889611 : Blo 546805 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B5631767 : Blo 546805 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B2781215 : Blo 546805 2781215 := bstep (se 1 (by rfl) ⟨2085911, by rfl⟩ : syracuseStep 2781215 = 4171823) B4171823
theorem B618799 : Blo 546805 618799 := bstep (se 1 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 618799 = 928199) B928199
theorem B4682231 : Blo 546805 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B5010173 : Blo 546805 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B619519 : Blo 546805 619519 := bstep (se 1 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 619519 = 929279) B929279
theorem B587035 : Blo 546805 587035 := bstep (se 1 (by rfl) ⟨440276, by rfl⟩ : syracuseStep 587035 = 880553) B880553
theorem B2226059 : Blo 546805 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B820361 : Blo 546805 820361 := bstep (se 2 (by rfl) ⟨307635, by rfl⟩ : syracuseStep 820361 = 615271) B615271
theorem B2787209 : Blo 546805 2787209 := bstep (se 2 (by rfl) ⟨1045203, by rfl⟩ : syracuseStep 2787209 = 2090407) B2090407
theorem B6260651 : Blo 546805 6260651 := bstep (se 1 (by rfl) ⟨4695488, by rfl⟩ : syracuseStep 6260651 = 9390977) B9390977
theorem B4163561 : Blo 546805 4163561 := bstep (se 2 (by rfl) ⟨1561335, by rfl⟩ : syracuseStep 4163561 = 3122671) B3122671
theorem B10520563 : Blo 546805 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B985583 : Blo 546805 985583 := bstep (se 1 (by rfl) ⟨739187, by rfl⟩ : syracuseStep 985583 = 1478375) B1478375
theorem B72092267 : Blo 546805 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B821951 : Blo 546805 821951 := bstep (se 1 (by rfl) ⟨616463, by rfl⟩ : syracuseStep 821951 = 1232927) B1232927
theorem B822011 : Blo 546805 822011 := bstep (se 1 (by rfl) ⟨616508, by rfl⟩ : syracuseStep 822011 = 1233017) B1233017
theorem B33721595 : Blo 546805 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B822527 : Blo 546805 822527 := bstep (se 1 (by rfl) ⟨616895, by rfl⟩ : syracuseStep 822527 = 1233791) B1233791
theorem B4165991 : Blo 546805 4165991 := bstep (se 1 (by rfl) ⟨3124493, by rfl⟩ : syracuseStep 4165991 = 6248987) B6248987
theorem B824015 : Blo 546805 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B824351 : Blo 546805 824351 := bstep (se 1 (by rfl) ⟨618263, by rfl⟩ : syracuseStep 824351 = 1236527) B1236527
theorem B5281195 : Blo 546805 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B825023 : Blo 546805 825023 := bstep (se 1 (by rfl) ⟨618767, by rfl⟩ : syracuseStep 825023 = 1237535) B1237535
theorem B825065 : Blo 546805 825065 := bstep (se 2 (by rfl) ⟨309399, by rfl⟩ : syracuseStep 825065 = 618799) B618799
theorem B694327 : Blo 546805 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B826025 : Blo 546805 826025 := bstep (se 2 (by rfl) ⟨309759, by rfl⟩ : syracuseStep 826025 = 619519) B619519
theorem B826175 : Blo 546805 826175 := bstep (se 1 (by rfl) ⟨619631, by rfl⟩ : syracuseStep 826175 = 1239263) B1239263
theorem B3514441 : Blo 546805 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B3121487 : Blo 546805 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B1484039 : Blo 546805 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B1387631 : Blo 546805 1387631 := bstep (se 1 (by rfl) ⟨1040723, by rfl⟩ : syracuseStep 1387631 = 2081447) B2081447
theorem B33828515 : Blo 546805 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B2338793 : Blo 546805 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B1388735 : Blo 546805 1388735 := bstep (se 1 (by rfl) ⟨1041551, by rfl⟩ : syracuseStep 1388735 = 2083103) B2083103
theorem B4272335 : Blo 546805 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B1390031 : Blo 546805 1390031 := bstep (se 1 (by rfl) ⟨1042523, by rfl⟩ : syracuseStep 1390031 = 2085047) B2085047
theorem B1851335 : Blo 546805 1851335 := bstep (se 1 (by rfl) ⟨1388501, by rfl⟩ : syracuseStep 1851335 = 2777003) B2777003
theorem B2769551 : Blo 546805 2769551 := bstep (se 1 (by rfl) ⟨2077163, by rfl⟩ : syracuseStep 2769551 = 4154327) B4154327
theorem B3754511 : Blo 546805 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B1854143 : Blo 546805 1854143 := bstep (se 1 (by rfl) ⟨1390607, by rfl⟩ : syracuseStep 1854143 = 2781215) B2781215
theorem B3133151 : Blo 546805 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1233215 : Blo 546805 1233215 := bstep (se 1 (by rfl) ⟨924911, by rfl⟩ : syracuseStep 1233215 = 1849823) B1849823
theorem B1167851 : Blo 546805 1167851 := bstep (se 1 (by rfl) ⟨875888, by rfl⟩ : syracuseStep 1167851 = 1751777) B1751777
theorem B3134335 : Blo 546805 3134335 := bstep (se 1 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 3134335 = 4701503) B4701503
theorem B1758143 : Blo 546805 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B2971279 : Blo 546805 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B1857761 : Blo 546805 1857761 := bstep (se 2 (by rfl) ⟨696660, by rfl⟩ : syracuseStep 1857761 = 1393321) B1393321
theorem B1170011 : Blo 546805 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1563239 : Blo 546805 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B547439 : Blo 546805 547439 := bstep (se 1 (by rfl) ⟨410579, by rfl⟩ : syracuseStep 547439 = 821159) B821159
theorem B547839 : Blo 546805 547839 := bstep (se 1 (by rfl) ⟨410879, by rfl⟩ : syracuseStep 547839 = 821759) B821759
theorem B13360247 : Blo 546805 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B2350241 : Blo 546805 2350241 := bstep (se 2 (by rfl) ⟨881340, by rfl⟩ : syracuseStep 2350241 = 1762681) B1762681
theorem B3136751 : Blo 546805 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B2645405 : Blo 546805 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B548975 : Blo 546805 548975 := bstep (se 1 (by rfl) ⟨411731, by rfl⟩ : syracuseStep 548975 = 823463) B823463
theorem B1695865 : Blo 546805 1695865 := bstep (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) B1271899
theorem B549031 : Blo 546805 549031 := bstep (se 1 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 549031 = 823547) B823547
theorem B549087 : Blo 546805 549087 := bstep (se 1 (by rfl) ⟨411815, by rfl⟩ : syracuseStep 549087 = 823631) B823631
theorem B1237319 : Blo 546805 1237319 := bstep (se 1 (by rfl) ⟨927989, by rfl⟩ : syracuseStep 1237319 = 1855979) B1855979
theorem B549531 : Blo 546805 549531 := bstep (se 1 (by rfl) ⟨412148, by rfl⟩ : syracuseStep 549531 = 824297) B824297
theorem B2974697 : Blo 546805 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B1041407 : Blo 546805 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B549915 : Blo 546805 549915 := bstep (se 1 (by rfl) ⟨412436, by rfl⟩ : syracuseStep 549915 = 824873) B824873
theorem B1041673 : Blo 546805 1041673 := bstep (se 2 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 1041673 = 781255) B781255
theorem B6251903 : Blo 546805 6251903 := bstep (se 1 (by rfl) ⟨4688927, by rfl⟩ : syracuseStep 6251903 = 9377855) B9377855
theorem B780463 : Blo 546805 780463 := bstep (se 1 (by rfl) ⟨585347, by rfl⟩ : syracuseStep 780463 = 1170695) B1170695
theorem B108030145 : Blo 546805 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B2813417 : Blo 546805 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B782713 : Blo 546805 782713 := bstep (se 2 (by rfl) ⟨293517, by rfl⟩ : syracuseStep 782713 = 587035) B587035
theorem B1831403 : Blo 546805 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B7926407 : Blo 546805 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B4158215 : Blo 546805 4158215 := bstep (se 1 (by rfl) ⟨3118661, by rfl⟩ : syracuseStep 4158215 = 6237323) B6237323
theorem B3340115 : Blo 546805 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B5929199 : Blo 546805 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B22903631 : Blo 546805 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B4685921 : Blo 546805 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B2261153 : Blo 546805 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B657055 : Blo 546805 657055 := bstep (se 1 (by rfl) ⟨492791, by rfl⟩ : syracuseStep 657055 = 985583) B985583
theorem B22481063 : Blo 546805 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B4688381 : Blo 546805 4688381 := bstep (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) B1758143
theorem B14027417 : Blo 546805 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B822143 : Blo 546805 822143 := bstep (se 1 (by rfl) ⟨616607, by rfl⟩ : syracuseStep 822143 = 1233215) B1233215
theorem B824879 : Blo 546805 824879 := bstep (se 1 (by rfl) ⟨618659, by rfl⟩ : syracuseStep 824879 = 1237319) B1237319
theorem B694271 : Blo 546805 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B4167935 : Blo 546805 4167935 := bstep (se 1 (by rfl) ⟨3125951, by rfl⟩ : syracuseStep 4167935 = 6251903) B6251903
theorem B3120029 : Blo 546805 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B925087 : Blo 546805 925087 := bstep (se 1 (by rfl) ⟨693815, by rfl⟩ : syracuseStep 925087 = 1387631) B1387631
theorem B1875611 : Blo 546805 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B22552343 : Blo 546805 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B925769 : Blo 546805 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B925823 : Blo 546805 925823 := bstep (se 1 (by rfl) ⟨694367, by rfl⟩ : syracuseStep 925823 = 1388735) B1388735
theorem B1220935 : Blo 546805 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B5284271 : Blo 546805 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B926687 : Blo 546805 926687 := bstep (se 1 (by rfl) ⟨695015, by rfl⟩ : syracuseStep 926687 = 1390031) B1390031
theorem B1846367 : Blo 546805 1846367 := bstep (se 1 (by rfl) ⟨1384775, by rfl⟩ : syracuseStep 1846367 = 2769551) B2769551
theorem B4173767 : Blo 546805 4173767 := bstep (se 1 (by rfl) ⟨3130325, by rfl⟩ : syracuseStep 4173767 = 6260651) B6260651
theorem B2503007 : Blo 546805 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B1388897 : Blo 546805 1388897 := bstep (se 2 (by rfl) ⟨520836, by rfl⟩ : syracuseStep 1388897 = 1041673) B1041673
theorem B2080991 : Blo 546805 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B1983131 : Blo 546805 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B4179113 : Blo 546805 4179113 := bstep (se 2 (by rfl) ⟨1567167, by rfl⟩ : syracuseStep 4179113 = 3134335) B3134335
theorem B1559195 : Blo 546805 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B2772143 : Blo 546805 2772143 := bstep (se 1 (by rfl) ⟨2079107, by rfl⟩ : syracuseStep 2772143 = 4158215) B4158215
theorem B3952799 : Blo 546805 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B1234223 : Blo 546805 1234223 := bstep (se 1 (by rfl) ⟨925667, by rfl⟩ : syracuseStep 1234223 = 1851335) B1851335
theorem B546907 : Blo 546805 546907 := bstep (se 1 (by rfl) ⟨410180, by rfl⟩ : syracuseStep 546907 = 820361) B820361
theorem B1858139 : Blo 546805 1858139 := bstep (se 1 (by rfl) ⟨1393604, by rfl⟩ : syracuseStep 1858139 = 2787209) B2787209
theorem B2775707 : Blo 546805 2775707 := bstep (se 1 (by rfl) ⟨2081780, by rfl⟩ : syracuseStep 2775707 = 4163561) B4163561
theorem B48061511 : Blo 546805 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B547967 : Blo 546805 547967 := bstep (se 1 (by rfl) ⟨410975, by rfl⟩ : syracuseStep 547967 = 821951) B821951
theorem B1236095 : Blo 546805 1236095 := bstep (se 1 (by rfl) ⟨927071, by rfl⟩ : syracuseStep 1236095 = 1854143) B1854143
theorem B548007 : Blo 546805 548007 := bstep (se 1 (by rfl) ⟨411005, by rfl⟩ : syracuseStep 548007 = 822011) B822011
theorem B548351 : Blo 546805 548351 := bstep (se 1 (by rfl) ⟨411263, by rfl⟩ : syracuseStep 548351 = 822527) B822527
theorem B2088767 : Blo 546805 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B1040617 : Blo 546805 1040617 := bstep (se 2 (by rfl) ⟨390231, by rfl⟩ : syracuseStep 1040617 = 780463) B780463
theorem B2777327 : Blo 546805 2777327 := bstep (se 1 (by rfl) ⟨2082995, by rfl⟩ : syracuseStep 2777327 = 4165991) B4165991
theorem B144040193 : Blo 546805 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B778567 : Blo 546805 778567 := bstep (se 1 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 778567 = 1167851) B1167851
theorem B549343 : Blo 546805 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B3957437 : Blo 546805 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B549567 : Blo 546805 549567 := bstep (se 1 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 549567 = 824351) B824351
theorem B550015 : Blo 546805 550015 := bstep (se 1 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 550015 = 825023) B825023
theorem B550043 : Blo 546805 550043 := bstep (se 1 (by rfl) ⟨412532, by rfl⟩ : syracuseStep 550043 = 825065) B825065
theorem B1238507 : Blo 546805 1238507 := bstep (se 1 (by rfl) ⟨928880, by rfl⟩ : syracuseStep 1238507 = 1857761) B1857761
theorem B1042159 : Blo 546805 1042159 := bstep (se 1 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 1042159 = 1563239) B1563239
theorem B550683 : Blo 546805 550683 := bstep (se 1 (by rfl) ⟨413012, by rfl⟩ : syracuseStep 550683 = 826025) B826025
theorem B550783 : Blo 546805 550783 := bstep (se 1 (by rfl) ⟨413087, by rfl⟩ : syracuseStep 550783 = 826175) B826175
theorem B8906831 : Blo 546805 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B1566827 : Blo 546805 1566827 := bstep (se 1 (by rfl) ⟨1175120, by rfl⟩ : syracuseStep 1566827 = 2350241) B2350241
theorem B2091167 : Blo 546805 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B1763603 : Blo 546805 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B1043617 : Blo 546805 1043617 := bstep (se 2 (by rfl) ⟨391356, by rfl⟩ : syracuseStep 1043617 = 782713) B782713
theorem B7041593 : Blo 546805 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B3961705 : Blo 546805 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B2848223 : Blo 546805 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B2226743 : Blo 546805 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B15269087 : Blo 546805 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B6029741 : Blo 546805 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B2786075 : Blo 546805 2786075 := bstep (se 1 (by rfl) ⟨2089556, by rfl⟩ : syracuseStep 2786075 = 4179113) B4179113
theorem B10553165 : Blo 546805 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B822815 : Blo 546805 822815 := bstep (se 1 (by rfl) ⟨617111, by rfl⟩ : syracuseStep 822815 = 1234223) B1234223
theorem B824063 : Blo 546805 824063 := bstep (se 1 (by rfl) ⟨618047, by rfl⟩ : syracuseStep 824063 = 1236095) B1236095
theorem B1250407 : Blo 546805 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B825671 : Blo 546805 825671 := bstep (se 1 (by rfl) ⟨619253, by rfl⟩ : syracuseStep 825671 = 1238507) B1238507
theorem B5282273 : Blo 546805 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B5937887 : Blo 546805 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B925931 : Blo 546805 925931 := bstep (se 1 (by rfl) ⟨694448, by rfl⟩ : syracuseStep 925931 = 1388897) B1388897
theorem B4694395 : Blo 546805 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B1484495 : Blo 546805 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B3123947 : Blo 546805 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B1387327 : Blo 546805 1387327 := bstep (se 1 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 1387327 = 2080991) B2080991
theorem B1387489 : Blo 546805 1387489 := bstep (se 2 (by rfl) ⟨520308, by rfl⟩ : syracuseStep 1387489 = 1040617) B1040617
theorem B1322087 : Blo 546805 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B14987375 : Blo 546805 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B3125587 : Blo 546805 3125587 := bstep (se 1 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 3125587 = 4688381) B4688381
theorem B9351611 : Blo 546805 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B1848095 : Blo 546805 1848095 := bstep (se 1 (by rfl) ⟨1386071, by rfl⟩ : syracuseStep 1848095 = 2772143) B2772143
theorem B1389545 : Blo 546805 1389545 := bstep (se 2 (by rfl) ⟨521079, by rfl⟩ : syracuseStep 1389545 = 1042159) B1042159
theorem B2635199 : Blo 546805 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B1391489 : Blo 546805 1391489 := bstep (se 2 (by rfl) ⟨521808, by rfl⟩ : syracuseStep 1391489 = 1043617) B1043617
theorem B1850471 : Blo 546805 1850471 := bstep (se 1 (by rfl) ⟨1387853, by rfl⟩ : syracuseStep 1850471 = 2775707) B2775707
theorem B2080019 : Blo 546805 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B1392511 : Blo 546805 1392511 := bstep (se 1 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 1392511 = 2088767) B2088767
theorem B1851389 : Blo 546805 1851389 := bstep (se 3 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 1851389 = 694271) B694271
theorem B1851551 : Blo 546805 1851551 := bstep (se 1 (by rfl) ⟨1388663, by rfl⟩ : syracuseStep 1851551 = 2777327) B2777327
theorem B96026795 : Blo 546805 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B3522847 : Blo 546805 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B1394111 : Blo 546805 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B1230911 : Blo 546805 1230911 := bstep (se 1 (by rfl) ⟨923183, by rfl⟩ : syracuseStep 1230911 = 1846367) B1846367
theorem B40717565 : Blo 546805 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B1233449 : Blo 546805 1233449 := bstep (se 2 (by rfl) ⟨462543, by rfl⟩ : syracuseStep 1233449 = 925087) B925087
theorem B1038089 : Blo 546805 1038089 := bstep (se 2 (by rfl) ⟨389283, by rfl⟩ : syracuseStep 1038089 = 778567) B778567
theorem B1627913 : Blo 546805 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B1039463 : Blo 546805 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B548095 : Blo 546805 548095 := bstep (se 1 (by rfl) ⟨411071, by rfl⟩ : syracuseStep 548095 = 822143) B822143
theorem B549919 : Blo 546805 549919 := bstep (se 1 (by rfl) ⟨412439, by rfl⟩ : syracuseStep 549919 = 824879) B824879
theorem B2778623 : Blo 546805 2778623 := bstep (se 1 (by rfl) ⟨2083967, by rfl⟩ : syracuseStep 2778623 = 4167935) B4167935
theorem B1238759 : Blo 546805 1238759 := bstep (se 1 (by rfl) ⟨929069, by rfl⟩ : syracuseStep 1238759 = 1858139) B1858139
theorem B32041007 : Blo 546805 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B15034895 : Blo 546805 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B617179 : Blo 546805 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B617215 : Blo 546805 617215 := bstep (se 1 (by rfl) ⟨462911, by rfl⟩ : syracuseStep 617215 = 925823) B925823
theorem B617791 : Blo 546805 617791 := bstep (se 1 (by rfl) ⟨463343, by rfl⟩ : syracuseStep 617791 = 926687) B926687
theorem B1044551 : Blo 546805 1044551 := bstep (se 1 (by rfl) ⟨783413, by rfl⟩ : syracuseStep 1044551 = 1566827) B1566827
theorem B1175735 : Blo 546805 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B2782511 : Blo 546805 2782511 := bstep (se 1 (by rfl) ⟨2086883, by rfl⟩ : syracuseStep 2782511 = 4173767) B4173767
theorem B1668671 : Blo 546805 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B3504293 : Blo 546805 3504293 := bstep (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) B657055
theorem B1898815 : Blo 546805 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B6259193 : Blo 546805 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B820607 : Blo 546805 820607 := bstep (se 1 (by rfl) ⟨615455, by rfl⟩ : syracuseStep 820607 = 1230911) B1230911
theorem B822299 : Blo 546805 822299 := bstep (se 1 (by rfl) ⟨616724, by rfl⟩ : syracuseStep 822299 = 1233449) B1233449
theorem B822905 : Blo 546805 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B822953 : Blo 546805 822953 := bstep (se 2 (by rfl) ⟨308607, by rfl⟩ : syracuseStep 822953 = 617215) B617215
theorem B692059 : Blo 546805 692059 := bstep (se 1 (by rfl) ⟨519044, by rfl⟩ : syracuseStep 692059 = 1038089) B1038089
theorem B1085275 : Blo 546805 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B823721 : Blo 546805 823721 := bstep (se 2 (by rfl) ⟨308895, by rfl⟩ : syracuseStep 823721 = 617791) B617791
theorem B692975 : Blo 546805 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B4167449 : Blo 546805 4167449 := bstep (se 2 (by rfl) ⟨1562793, by rfl⟩ : syracuseStep 4167449 = 3125587) B3125587
theorem B989663 : Blo 546805 989663 := bstep (se 1 (by rfl) ⟨742247, by rfl⟩ : syracuseStep 989663 = 1484495) B1484495
theorem B825839 : Blo 546805 825839 := bstep (se 1 (by rfl) ⟨619379, by rfl⟩ : syracuseStep 825839 = 1238759) B1238759
theorem B696367 : Blo 546805 696367 := bstep (se 1 (by rfl) ⟨522275, by rfl⟩ : syracuseStep 696367 = 1044551) B1044551
theorem B6234407 : Blo 546805 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B2531753 : Blo 546805 2531753 := bstep (se 2 (by rfl) ⟨949407, by rfl⟩ : syracuseStep 2531753 = 1898815) B1898815
theorem B926363 : Blo 546805 926363 := bstep (se 1 (by rfl) ⟨694772, by rfl⟩ : syracuseStep 926363 = 1389545) B1389545
theorem B2336195 : Blo 546805 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B927659 : Blo 546805 927659 := bstep (se 1 (by rfl) ⟨695744, by rfl⟩ : syracuseStep 927659 = 1391489) B1391489
theorem B1386679 : Blo 546805 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B4697129 : Blo 546805 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B929407 : Blo 546805 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B27145043 : Blo 546805 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B1849769 : Blo 546805 1849769 := bstep (se 2 (by rfl) ⟨693663, by rfl⟩ : syracuseStep 1849769 = 1387327) B1387327
theorem B1849985 : Blo 546805 1849985 := bstep (se 2 (by rfl) ⟨693744, by rfl⟩ : syracuseStep 1849985 = 1387489) B1387489
theorem B3521515 : Blo 546805 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B6668837 : Blo 546805 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B1852415 : Blo 546805 1852415 := bstep (se 1 (by rfl) ⟨1389311, by rfl⟩ : syracuseStep 1852415 = 2778623) B2778623
theorem B2082631 : Blo 546805 2082631 := bstep (se 1 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 2082631 = 3123947) B3123947
theorem B3525565 : Blo 546805 3525565 := bstep (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) B1322087
theorem B1232063 : Blo 546805 1232063 := bstep (se 1 (by rfl) ⟨924047, by rfl⟩ : syracuseStep 1232063 = 1848095) B1848095
theorem B1855007 : Blo 546805 1855007 := bstep (se 1 (by rfl) ⟨1391255, by rfl⟩ : syracuseStep 1855007 = 2782511) B2782511
theorem B1756799 : Blo 546805 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1233647 : Blo 546805 1233647 := bstep (se 1 (by rfl) ⟨925235, by rfl⟩ : syracuseStep 1233647 = 1850471) B1850471
theorem B1856681 : Blo 546805 1856681 := bstep (se 2 (by rfl) ⟨696255, by rfl⟩ : syracuseStep 1856681 = 1392511) B1392511
theorem B1234259 : Blo 546805 1234259 := bstep (se 1 (by rfl) ⟨925694, by rfl⟩ : syracuseStep 1234259 = 1851389) B1851389
theorem B1234367 : Blo 546805 1234367 := bstep (se 1 (by rfl) ⟨925775, by rfl⟩ : syracuseStep 1234367 = 1851551) B1851551
theorem B64017863 : Blo 546805 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B4019827 : Blo 546805 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B3135293 : Blo 546805 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B1857383 : Blo 546805 1857383 := bstep (se 1 (by rfl) ⟨1393037, by rfl⟩ : syracuseStep 1857383 = 2786075) B2786075
theorem B7035443 : Blo 546805 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B548543 : Blo 546805 548543 := bstep (se 1 (by rfl) ⟨411407, by rfl⟩ : syracuseStep 548543 = 822815) B822815
theorem B549375 : Blo 546805 549375 := bstep (se 1 (by rfl) ⟨412031, by rfl⟩ : syracuseStep 549375 = 824063) B824063
theorem B550447 : Blo 546805 550447 := bstep (se 1 (by rfl) ⟨412835, by rfl⟩ : syracuseStep 550447 = 825671) B825671
theorem B3958591 : Blo 546805 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B617287 : Blo 546805 617287 := bstep (se 1 (by rfl) ⟨462965, by rfl⟩ : syracuseStep 617287 = 925931) B925931
theorem B21360671 : Blo 546805 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B10023263 : Blo 546805 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B9991583 : Blo 546805 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B1112447 : Blo 546805 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B821375 : Blo 546805 821375 := bstep (se 1 (by rfl) ⟨616031, by rfl⟩ : syracuseStep 821375 = 1232063) B1232063
theorem B5278121 : Blo 546805 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B822431 : Blo 546805 822431 := bstep (se 1 (by rfl) ⟨616823, by rfl⟩ : syracuseStep 822431 = 1233647) B1233647
theorem B822839 : Blo 546805 822839 := bstep (se 1 (by rfl) ⟨617129, by rfl⟩ : syracuseStep 822839 = 1234259) B1234259
theorem B822911 : Blo 546805 822911 := bstep (se 1 (by rfl) ⟨617183, by rfl⟩ : syracuseStep 822911 = 1234367) B1234367
theorem B823049 : Blo 546805 823049 := bstep (se 2 (by rfl) ⟨308643, by rfl⟩ : syracuseStep 823049 = 617287) B617287
theorem B4690295 : Blo 546805 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B922745 : Blo 546805 922745 := bstep (se 2 (by rfl) ⟨346029, by rfl⟩ : syracuseStep 922745 = 692059) B692059
theorem B1447033 : Blo 546805 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B18096695 : Blo 546805 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B6661055 : Blo 546805 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B4695353 : Blo 546805 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B928489 : Blo 546805 928489 := bstep (se 2 (by rfl) ⟨348183, by rfl⟩ : syracuseStep 928489 = 696367) B696367
theorem B4172795 : Blo 546805 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B1847933 : Blo 546805 1847933 := bstep (se 3 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 1847933 = 692975) B692975
theorem B1848905 : Blo 546805 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B42678575 : Blo 546805 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B4700753 : Blo 546805 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B1687835 : Blo 546805 1687835 := bstep (se 1 (by rfl) ⟨1265876, by rfl⟩ : syracuseStep 1687835 = 2531753) B2531753
theorem B1557463 : Blo 546805 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B2639101 : Blo 546805 2639101 := bstep (se 3 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 2639101 = 989663) B989663
theorem B3131419 : Blo 546805 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B5359769 : Blo 546805 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B14240447 : Blo 546805 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B741631 : Blo 546805 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B1233179 : Blo 546805 1233179 := bstep (se 1 (by rfl) ⟨924884, by rfl⟩ : syracuseStep 1233179 = 1849769) B1849769
theorem B1233323 : Blo 546805 1233323 := bstep (se 1 (by rfl) ⟨924992, by rfl⟩ : syracuseStep 1233323 = 1849985) B1849985
theorem B4445891 : Blo 546805 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B1234943 : Blo 546805 1234943 := bstep (se 1 (by rfl) ⟨926207, by rfl⟩ : syracuseStep 1234943 = 1852415) B1852415
theorem B547071 : Blo 546805 547071 := bstep (se 1 (by rfl) ⟨410303, by rfl⟩ : syracuseStep 547071 = 820607) B820607
theorem B548199 : Blo 546805 548199 := bstep (se 1 (by rfl) ⟨411149, by rfl⟩ : syracuseStep 548199 = 822299) B822299
theorem B1236671 : Blo 546805 1236671 := bstep (se 1 (by rfl) ⟨927503, by rfl⟩ : syracuseStep 1236671 = 1855007) B1855007
theorem B548603 : Blo 546805 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B1171199 : Blo 546805 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B2776841 : Blo 546805 2776841 := bstep (se 2 (by rfl) ⟨1041315, by rfl⟩ : syracuseStep 2776841 = 2082631) B2082631
theorem B548635 : Blo 546805 548635 := bstep (se 1 (by rfl) ⟨411476, by rfl⟩ : syracuseStep 548635 = 822953) B822953
theorem B549147 : Blo 546805 549147 := bstep (se 1 (by rfl) ⟨411860, by rfl⟩ : syracuseStep 549147 = 823721) B823721
theorem B1237787 : Blo 546805 1237787 := bstep (se 1 (by rfl) ⟨928340, by rfl⟩ : syracuseStep 1237787 = 1856681) B1856681
theorem B2778299 : Blo 546805 2778299 := bstep (se 1 (by rfl) ⟨2083724, by rfl⟩ : syracuseStep 2778299 = 4167449) B4167449
theorem B2090195 : Blo 546805 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B1238255 : Blo 546805 1238255 := bstep (se 1 (by rfl) ⟨928691, by rfl⟩ : syracuseStep 1238255 = 1857383) B1857383
theorem B550559 : Blo 546805 550559 := bstep (se 1 (by rfl) ⟨412919, by rfl⟩ : syracuseStep 550559 = 825839) B825839
theorem B1239209 : Blo 546805 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B4156271 : Blo 546805 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B617575 : Blo 546805 617575 := bstep (se 1 (by rfl) ⟨463181, by rfl⟩ : syracuseStep 617575 = 926363) B926363
theorem B618439 : Blo 546805 618439 := bstep (se 1 (by rfl) ⟨463829, by rfl⟩ : syracuseStep 618439 = 927659) B927659
theorem B6682175 : Blo 546805 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B3573179 : Blo 546805 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B822119 : Blo 546805 822119 := bstep (se 1 (by rfl) ⟨616589, by rfl⟩ : syracuseStep 822119 = 1233179) B1233179
theorem B822215 : Blo 546805 822215 := bstep (se 1 (by rfl) ⟨616661, by rfl⟩ : syracuseStep 822215 = 1233323) B1233323
theorem B823295 : Blo 546805 823295 := bstep (se 1 (by rfl) ⟨617471, by rfl⟩ : syracuseStep 823295 = 1234943) B1234943
theorem B823433 : Blo 546805 823433 := bstep (se 2 (by rfl) ⟨308787, by rfl⟩ : syracuseStep 823433 = 617575) B617575
theorem B824447 : Blo 546805 824447 := bstep (se 1 (by rfl) ⟨618335, by rfl⟩ : syracuseStep 824447 = 1236671) B1236671
theorem B824585 : Blo 546805 824585 := bstep (se 2 (by rfl) ⟨309219, by rfl⟩ : syracuseStep 824585 = 618439) B618439
theorem B988841 : Blo 546805 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B12064463 : Blo 546805 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B825191 : Blo 546805 825191 := bstep (se 1 (by rfl) ⟨618893, by rfl⟩ : syracuseStep 825191 = 1237787) B1237787
theorem B825503 : Blo 546805 825503 := bstep (se 1 (by rfl) ⟨619127, by rfl⟩ : syracuseStep 825503 = 1238255) B1238255
theorem B826139 : Blo 546805 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B28452383 : Blo 546805 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B3123197 : Blo 546805 3123197 := bstep (se 3 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 3123197 = 1171199) B1171199
theorem B4500893 : Blo 546805 4500893 := bstep (se 3 (by rfl) ⟨843917, by rfl⟩ : syracuseStep 4500893 = 1687835) B1687835
theorem B2076617 : Blo 546805 2076617 := bstep (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) B1557463
theorem B3518747 : Blo 546805 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B3518801 : Blo 546805 3518801 := bstep (se 2 (by rfl) ⟨1319550, by rfl⟩ : syracuseStep 3518801 = 2639101) B2639101
theorem B4175225 : Blo 546805 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B3126863 : Blo 546805 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B2963927 : Blo 546805 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1851227 : Blo 546805 1851227 := bstep (se 1 (by rfl) ⟨1388420, by rfl⟩ : syracuseStep 1851227 = 2776841) B2776841
theorem B4440703 : Blo 546805 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B1852199 : Blo 546805 1852199 := bstep (se 1 (by rfl) ⟨1389149, by rfl⟩ : syracuseStep 1852199 = 2778299) B2778299
theorem B1393463 : Blo 546805 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B3130235 : Blo 546805 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B2770847 : Blo 546805 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B1231955 : Blo 546805 1231955 := bstep (se 1 (by rfl) ⟨923966, by rfl⟩ : syracuseStep 1231955 = 1847933) B1847933
theorem B1232603 : Blo 546805 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B3133835 : Blo 546805 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B547583 : Blo 546805 547583 := bstep (se 1 (by rfl) ⟨410687, by rfl⟩ : syracuseStep 547583 = 821375) B821375
theorem B9493631 : Blo 546805 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B548287 : Blo 546805 548287 := bstep (se 1 (by rfl) ⟨411215, by rfl⟩ : syracuseStep 548287 = 822431) B822431
theorem B548559 : Blo 546805 548559 := bstep (se 1 (by rfl) ⟨411419, by rfl⟩ : syracuseStep 548559 = 822839) B822839
theorem B548607 : Blo 546805 548607 := bstep (se 1 (by rfl) ⟨411455, by rfl⟩ : syracuseStep 548607 = 822911) B822911
theorem B548699 : Blo 546805 548699 := bstep (se 1 (by rfl) ⟨411524, by rfl⟩ : syracuseStep 548699 = 823049) B823049
theorem B615163 : Blo 546805 615163 := bstep (se 1 (by rfl) ⟨461372, by rfl⟩ : syracuseStep 615163 = 922745) B922745
theorem B1237985 : Blo 546805 1237985 := bstep (se 2 (by rfl) ⟨464244, by rfl⟩ : syracuseStep 1237985 = 928489) B928489
theorem B1929377 : Blo 546805 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B2781863 : Blo 546805 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B4454783 : Blo 546805 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B5145005 : Blo 546805 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B820217 : Blo 546805 820217 := bstep (se 2 (by rfl) ⟨307581, by rfl⟩ : syracuseStep 820217 = 615163) B615163
theorem B821303 : Blo 546805 821303 := bstep (se 1 (by rfl) ⟨615977, by rfl⟩ : syracuseStep 821303 = 1231955) B1231955
theorem B821735 : Blo 546805 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B659227 : Blo 546805 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B6329087 : Blo 546805 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B825323 : Blo 546805 825323 := bstep (se 1 (by rfl) ⟨618992, by rfl⟩ : syracuseStep 825323 = 1237985) B1237985
theorem B1384411 : Blo 546805 1384411 := bstep (se 1 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 1384411 = 2076617) B2076617
theorem B1975951 : Blo 546805 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B928975 : Blo 546805 928975 := bstep (se 1 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 928975 = 1393463) B1393463
theorem B1847231 : Blo 546805 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B8042975 : Blo 546805 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B2082131 : Blo 546805 2082131 := bstep (se 1 (by rfl) ⟨1561598, by rfl⟩ : syracuseStep 2082131 = 3123197) B3123197
theorem B3000595 : Blo 546805 3000595 := bstep (se 1 (by rfl) ⟨2250446, by rfl⟩ : syracuseStep 3000595 = 4500893) B4500893
theorem B2345831 : Blo 546805 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B2345867 : Blo 546805 2345867 := bstep (se 1 (by rfl) ⟨1759400, by rfl⟩ : syracuseStep 2345867 = 3518801) B3518801
theorem B1854575 : Blo 546805 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B2084575 : Blo 546805 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B2969855 : Blo 546805 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B1234151 : Blo 546805 1234151 := bstep (se 1 (by rfl) ⟨925613, by rfl⟩ : syracuseStep 1234151 = 1851227) B1851227
theorem B1234799 : Blo 546805 1234799 := bstep (se 1 (by rfl) ⟨926099, by rfl⟩ : syracuseStep 1234799 = 1852199) B1852199
theorem B2086823 : Blo 546805 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B5920937 : Blo 546805 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B2382119 : Blo 546805 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B548079 : Blo 546805 548079 := bstep (se 1 (by rfl) ⟨411059, by rfl⟩ : syracuseStep 548079 = 822119) B822119
theorem B548143 : Blo 546805 548143 := bstep (se 1 (by rfl) ⟨411107, by rfl⟩ : syracuseStep 548143 = 822215) B822215
theorem B548863 : Blo 546805 548863 := bstep (se 1 (by rfl) ⟨411647, by rfl⟩ : syracuseStep 548863 = 823295) B823295
theorem B548955 : Blo 546805 548955 := bstep (se 1 (by rfl) ⟨411716, by rfl⟩ : syracuseStep 548955 = 823433) B823433
theorem B2089223 : Blo 546805 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B549631 : Blo 546805 549631 := bstep (se 1 (by rfl) ⟨412223, by rfl⟩ : syracuseStep 549631 = 824447) B824447
theorem B549723 : Blo 546805 549723 := bstep (se 1 (by rfl) ⟨412292, by rfl⟩ : syracuseStep 549723 = 824585) B824585
theorem B550127 : Blo 546805 550127 := bstep (se 1 (by rfl) ⟨412595, by rfl⟩ : syracuseStep 550127 = 825191) B825191
theorem B550335 : Blo 546805 550335 := bstep (se 1 (by rfl) ⟨412751, by rfl⟩ : syracuseStep 550335 = 825503) B825503
theorem B550759 : Blo 546805 550759 := bstep (se 1 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 550759 = 826139) B826139
theorem B18968255 : Blo 546805 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B2783483 : Blo 546805 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B822767 : Blo 546805 822767 := bstep (se 1 (by rfl) ⟨617075, by rfl⟩ : syracuseStep 822767 = 1234151) B1234151
theorem B823199 : Blo 546805 823199 := bstep (se 1 (by rfl) ⟨617399, by rfl⟩ : syracuseStep 823199 = 1234799) B1234799
theorem B1845881 : Blo 546805 1845881 := bstep (se 2 (by rfl) ⟨692205, by rfl⟩ : syracuseStep 1845881 = 1384411) B1384411
theorem B1388087 : Blo 546805 1388087 := bstep (se 1 (by rfl) ⟨1041065, by rfl⟩ : syracuseStep 1388087 = 2082131) B2082131
theorem B2634601 : Blo 546805 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B1979903 : Blo 546805 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B1391215 : Blo 546805 1391215 := bstep (se 1 (by rfl) ⟨1043411, by rfl⟩ : syracuseStep 1391215 = 2086823) B2086823
theorem B3947291 : Blo 546805 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B1588079 : Blo 546805 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B1392815 : Blo 546805 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B64012693 : Blo 546805 64012693 := bstep (se 6 (by rfl) ⟨1500297, by rfl⟩ : syracuseStep 64012693 = 3000595) B3000595
theorem B1231487 : Blo 546805 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B1855655 : Blo 546805 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B5361983 : Blo 546805 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B546811 : Blo 546805 546811 := bstep (se 1 (by rfl) ⟨410108, by rfl⟩ : syracuseStep 546811 = 820217) B820217
theorem B13720013 : Blo 546805 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B547535 : Blo 546805 547535 := bstep (se 1 (by rfl) ⟨410651, by rfl⟩ : syracuseStep 547535 = 821303) B821303
theorem B547823 : Blo 546805 547823 := bstep (se 1 (by rfl) ⟨410867, by rfl⟩ : syracuseStep 547823 = 821735) B821735
theorem B1563887 : Blo 546805 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B1563911 : Blo 546805 1563911 := bstep (se 1 (by rfl) ⟨1172933, by rfl⟩ : syracuseStep 1563911 = 2345867) B2345867
theorem B1236383 : Blo 546805 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B4219391 : Blo 546805 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B550215 : Blo 546805 550215 := bstep (se 1 (by rfl) ⟨412661, by rfl⟩ : syracuseStep 550215 = 825323) B825323
theorem B1238633 : Blo 546805 1238633 := bstep (se 2 (by rfl) ⟨464487, by rfl⟩ : syracuseStep 1238633 = 928975) B928975
theorem B2779433 : Blo 546805 2779433 := bstep (se 2 (by rfl) ⟨1042287, by rfl⟩ : syracuseStep 2779433 = 2084575) B2084575
theorem B878969 : Blo 546805 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B12645503 : Blo 546805 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B820991 : Blo 546805 820991 := bstep (se 1 (by rfl) ⟨615743, by rfl⟩ : syracuseStep 820991 = 1231487) B1231487
theorem B3574655 : Blo 546805 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B9146675 : Blo 546805 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B824255 : Blo 546805 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B825755 : Blo 546805 825755 := bstep (se 1 (by rfl) ⟨619316, by rfl⟩ : syracuseStep 825755 = 1238633) B1238633
theorem B3512801 : Blo 546805 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B925391 : Blo 546805 925391 := bstep (se 1 (by rfl) ⟨694043, by rfl⟩ : syracuseStep 925391 = 1388087) B1388087
theorem B4170365 : Blo 546805 4170365 := bstep (se 3 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 4170365 = 1563887) B1563887
theorem B8430335 : Blo 546805 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B1319935 : Blo 546805 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B2631527 : Blo 546805 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B1058719 : Blo 546805 1058719 := bstep (se 1 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 1058719 = 1588079) B1588079
theorem B928543 : Blo 546805 928543 := bstep (se 1 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 928543 = 1392815) B1392815
theorem B2343917 : Blo 546805 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B1852955 : Blo 546805 1852955 := bstep (se 1 (by rfl) ⟨1389716, by rfl⟩ : syracuseStep 1852955 = 2779433) B2779433
theorem B1230587 : Blo 546805 1230587 := bstep (se 1 (by rfl) ⟨922940, by rfl⟩ : syracuseStep 1230587 = 1845881) B1845881
theorem B1854953 : Blo 546805 1854953 := bstep (se 2 (by rfl) ⟨695607, by rfl⟩ : syracuseStep 1854953 = 1391215) B1391215
theorem B85350257 : Blo 546805 85350257 := bstep (se 2 (by rfl) ⟨32006346, by rfl⟩ : syracuseStep 85350257 = 64012693) B64012693
theorem B548511 : Blo 546805 548511 := bstep (se 1 (by rfl) ⟨411383, by rfl⟩ : syracuseStep 548511 = 822767) B822767
theorem B548799 : Blo 546805 548799 := bstep (se 1 (by rfl) ⟨411599, by rfl⟩ : syracuseStep 548799 = 823199) B823199
theorem B1237103 : Blo 546805 1237103 := bstep (se 1 (by rfl) ⟨927827, by rfl⟩ : syracuseStep 1237103 = 1855655) B1855655
theorem B1042607 : Blo 546805 1042607 := bstep (se 1 (by rfl) ⟨781955, by rfl⟩ : syracuseStep 1042607 = 1563911) B1563911
theorem B2812927 : Blo 546805 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B820391 : Blo 546805 820391 := bstep (se 1 (by rfl) ⟨615293, by rfl⟩ : syracuseStep 820391 = 1230587) B1230587
theorem B1411625 : Blo 546805 1411625 := bstep (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) B1058719
theorem B6097783 : Blo 546805 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B824735 : Blo 546805 824735 := bstep (se 1 (by rfl) ⟨618551, by rfl⟩ : syracuseStep 824735 = 1237103) B1237103
theorem B695071 : Blo 546805 695071 := bstep (se 1 (by rfl) ⟨521303, by rfl⟩ : syracuseStep 695071 = 1042607) B1042607
theorem B56900171 : Blo 546805 56900171 := bstep (se 1 (by rfl) ⟨42675128, by rfl⟩ : syracuseStep 56900171 = 85350257) B85350257
theorem B3750569 : Blo 546805 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B2341867 : Blo 546805 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B5620223 : Blo 546805 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B1754351 : Blo 546805 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B1235303 : Blo 546805 1235303 := bstep (se 1 (by rfl) ⟨926477, by rfl⟩ : syracuseStep 1235303 = 1852955) B1852955
theorem B547327 : Blo 546805 547327 := bstep (se 1 (by rfl) ⟨410495, by rfl⟩ : syracuseStep 547327 = 820991) B820991
theorem B1759913 : Blo 546805 1759913 := bstep (se 2 (by rfl) ⟨659967, by rfl⟩ : syracuseStep 1759913 = 1319935) B1319935
theorem B2383103 : Blo 546805 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B1236635 : Blo 546805 1236635 := bstep (se 1 (by rfl) ⟨927476, by rfl⟩ : syracuseStep 1236635 = 1854953) B1854953
theorem B6250445 : Blo 546805 6250445 := bstep (se 3 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 6250445 = 2343917) B2343917
theorem B549503 : Blo 546805 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B1238057 : Blo 546805 1238057 := bstep (se 2 (by rfl) ⟨464271, by rfl⟩ : syracuseStep 1238057 = 928543) B928543
theorem B550503 : Blo 546805 550503 := bstep (se 1 (by rfl) ⟨412877, by rfl⟩ : syracuseStep 550503 = 825755) B825755
theorem B616927 : Blo 546805 616927 := bstep (se 1 (by rfl) ⟨462695, by rfl⟩ : syracuseStep 616927 = 925391) B925391
theorem B2780243 : Blo 546805 2780243 := bstep (se 1 (by rfl) ⟨2085182, by rfl⟩ : syracuseStep 2780243 = 4170365) B4170365
theorem B822569 : Blo 546805 822569 := bstep (se 2 (by rfl) ⟨308463, by rfl⟩ : syracuseStep 822569 = 616927) B616927
theorem B8130377 : Blo 546805 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B823535 : Blo 546805 823535 := bstep (se 1 (by rfl) ⟨617651, by rfl⟩ : syracuseStep 823535 = 1235303) B1235303
theorem B824423 : Blo 546805 824423 := bstep (se 1 (by rfl) ⟨618317, by rfl⟩ : syracuseStep 824423 = 1236635) B1236635
theorem B4166963 : Blo 546805 4166963 := bstep (se 1 (by rfl) ⟨3125222, by rfl⟩ : syracuseStep 4166963 = 6250445) B6250445
theorem B825371 : Blo 546805 825371 := bstep (se 1 (by rfl) ⟨619028, by rfl⟩ : syracuseStep 825371 = 1238057) B1238057
theorem B926761 : Blo 546805 926761 := bstep (se 2 (by rfl) ⟨347535, by rfl⟩ : syracuseStep 926761 = 695071) B695071
theorem B3122489 : Blo 546805 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B2500379 : Blo 546805 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B14987261 : Blo 546805 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B1588735 : Blo 546805 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B1853495 : Blo 546805 1853495 := bstep (se 1 (by rfl) ⟨1390121, by rfl⟩ : syracuseStep 1853495 = 2780243) B2780243
theorem B37933447 : Blo 546805 37933447 := bstep (se 1 (by rfl) ⟨28450085, by rfl⟩ : syracuseStep 37933447 = 56900171) B56900171
theorem B546927 : Blo 546805 546927 := bstep (se 1 (by rfl) ⟨410195, by rfl⟩ : syracuseStep 546927 = 820391) B820391
theorem B1169567 : Blo 546805 1169567 := bstep (se 1 (by rfl) ⟨877175, by rfl⟩ : syracuseStep 1169567 = 1754351) B1754351
theorem B549823 : Blo 546805 549823 := bstep (se 1 (by rfl) ⟨412367, by rfl⟩ : syracuseStep 549823 = 824735) B824735
theorem B1173275 : Blo 546805 1173275 := bstep (se 1 (by rfl) ⟨879956, by rfl⟩ : syracuseStep 1173275 = 1759913) B1759913
theorem B3764333 : Blo 546805 3764333 := bstep (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) B1411625
theorem B5420251 : Blo 546805 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B50577929 : Blo 546805 50577929 := bstep (se 2 (by rfl) ⟨18966723, by rfl⟩ : syracuseStep 50577929 = 37933447) B37933447
theorem B2081659 : Blo 546805 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B2509555 : Blo 546805 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B2118313 : Blo 546805 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B1235663 : Blo 546805 1235663 := bstep (se 1 (by rfl) ⟨926747, by rfl⟩ : syracuseStep 1235663 = 1853495) B1853495
theorem B1235681 : Blo 546805 1235681 := bstep (se 2 (by rfl) ⟨463380, by rfl⟩ : syracuseStep 1235681 = 926761) B926761
theorem B548379 : Blo 546805 548379 := bstep (se 1 (by rfl) ⟨411284, by rfl⟩ : syracuseStep 548379 = 822569) B822569
theorem B549023 : Blo 546805 549023 := bstep (se 1 (by rfl) ⟨411767, by rfl⟩ : syracuseStep 549023 = 823535) B823535
theorem B549615 : Blo 546805 549615 := bstep (se 1 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 549615 = 824423) B824423
theorem B2777975 : Blo 546805 2777975 := bstep (se 1 (by rfl) ⟨2083481, by rfl⟩ : syracuseStep 2777975 = 4166963) B4166963
theorem B550247 : Blo 546805 550247 := bstep (se 1 (by rfl) ⟨412685, by rfl⟩ : syracuseStep 550247 = 825371) B825371
theorem B779711 : Blo 546805 779711 := bstep (se 1 (by rfl) ⟨584783, by rfl⟩ : syracuseStep 779711 = 1169567) B1169567
theorem B1666919 : Blo 546805 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B782183 : Blo 546805 782183 := bstep (se 1 (by rfl) ⟨586637, by rfl⟩ : syracuseStep 782183 = 1173275) B1173275
theorem B9991507 : Blo 546805 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B33718619 : Blo 546805 33718619 := bstep (se 1 (by rfl) ⟨25288964, by rfl⟩ : syracuseStep 33718619 = 50577929) B50577929
theorem B3346073 : Blo 546805 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B823775 : Blo 546805 823775 := bstep (se 1 (by rfl) ⟨617831, by rfl⟩ : syracuseStep 823775 = 1235663) B1235663
theorem B823787 : Blo 546805 823787 := bstep (se 1 (by rfl) ⟨617840, by rfl⟩ : syracuseStep 823787 = 1235681) B1235681
theorem B2824417 : Blo 546805 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B2079229 : Blo 546805 2079229 := bstep (se 3 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 2079229 = 779711) B779711
theorem B1851983 : Blo 546805 1851983 := bstep (se 1 (by rfl) ⟨1388987, by rfl⟩ : syracuseStep 1851983 = 2777975) B2777975
theorem B7227001 : Blo 546805 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B13322009 : Blo 546805 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B2085821 : Blo 546805 2085821 := bstep (se 3 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 2085821 = 782183) B782183
theorem B2775545 : Blo 546805 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B1111279 : Blo 546805 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B22479079 : Blo 546805 22479079 := bstep (se 1 (by rfl) ⟨16859309, by rfl⟩ : syracuseStep 22479079 = 33718619) B33718619
theorem B8881339 : Blo 546805 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B2230715 : Blo 546805 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B1481705 : Blo 546805 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B38544005 : Blo 546805 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B1390547 : Blo 546805 1390547 := bstep (se 1 (by rfl) ⟨1042910, by rfl⟩ : syracuseStep 1390547 = 2085821) B2085821
theorem B1850363 : Blo 546805 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B2772305 : Blo 546805 2772305 := bstep (se 2 (by rfl) ⟨1039614, by rfl⟩ : syracuseStep 2772305 = 2079229) B2079229
theorem B1234655 : Blo 546805 1234655 := bstep (se 1 (by rfl) ⟨925991, by rfl⟩ : syracuseStep 1234655 = 1851983) B1851983
theorem B549183 : Blo 546805 549183 := bstep (se 1 (by rfl) ⟨411887, by rfl⟩ : syracuseStep 549183 = 823775) B823775
theorem B549191 : Blo 546805 549191 := bstep (se 1 (by rfl) ⟨411893, by rfl⟩ : syracuseStep 549191 = 823787) B823787
theorem B3765889 : Blo 546805 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B823103 : Blo 546805 823103 := bstep (se 1 (by rfl) ⟨617327, by rfl⟩ : syracuseStep 823103 = 1234655) B1234655
theorem B987803 : Blo 546805 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B25696003 : Blo 546805 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B5021185 : Blo 546805 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B927031 : Blo 546805 927031 := bstep (se 1 (by rfl) ⟨695273, by rfl⟩ : syracuseStep 927031 = 1390547) B1390547
theorem B11841785 : Blo 546805 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B1487143 : Blo 546805 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B1848203 : Blo 546805 1848203 := bstep (se 1 (by rfl) ⟨1386152, by rfl⟩ : syracuseStep 1848203 = 2772305) B2772305
theorem B1233575 : Blo 546805 1233575 := bstep (se 1 (by rfl) ⟨925181, by rfl⟩ : syracuseStep 1233575 = 1850363) B1850363
theorem B29972105 : Blo 546805 29972105 := bstep (se 2 (by rfl) ⟨11239539, by rfl⟩ : syracuseStep 29972105 = 22479079) B22479079
theorem B7931429 : Blo 546805 7931429 := bstep (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) B1487143
theorem B658535 : Blo 546805 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B822383 : Blo 546805 822383 := bstep (se 1 (by rfl) ⟨616787, by rfl⟩ : syracuseStep 822383 = 1233575) B1233575
theorem B6694913 : Blo 546805 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B34261337 : Blo 546805 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1232135 : Blo 546805 1232135 := bstep (se 1 (by rfl) ⟨924101, by rfl⟩ : syracuseStep 1232135 = 1848203) B1848203
theorem B1236041 : Blo 546805 1236041 := bstep (se 2 (by rfl) ⟨463515, by rfl⟩ : syracuseStep 1236041 = 927031) B927031
theorem B548735 : Blo 546805 548735 := bstep (se 1 (by rfl) ⟨411551, by rfl⟩ : syracuseStep 548735 = 823103) B823103
theorem B19981403 : Blo 546805 19981403 := bstep (se 1 (by rfl) ⟨14986052, by rfl⟩ : syracuseStep 19981403 = 29972105) B29972105
theorem B7894523 : Blo 546805 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B821423 : Blo 546805 821423 := bstep (se 1 (by rfl) ⟨616067, by rfl⟩ : syracuseStep 821423 = 1232135) B1232135
theorem B824027 : Blo 546805 824027 := bstep (se 1 (by rfl) ⟨618020, by rfl⟩ : syracuseStep 824027 = 1236041) B1236041
theorem B91363565 : Blo 546805 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B4463275 : Blo 546805 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B5287619 : Blo 546805 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B13320935 : Blo 546805 13320935 := bstep (se 1 (by rfl) ⟨9990701, by rfl⟩ : syracuseStep 13320935 = 19981403) B19981403
theorem B1756093 : Blo 546805 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B5263015 : Blo 546805 5263015 := bstep (se 1 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 5263015 = 7894523) B7894523
theorem B548255 : Blo 546805 548255 := bstep (se 1 (by rfl) ⟨411191, by rfl⟩ : syracuseStep 548255 = 822383) B822383
theorem B8880623 : Blo 546805 8880623 := bstep (se 1 (by rfl) ⟨6660467, by rfl⟩ : syracuseStep 8880623 = 13320935) B13320935
theorem B7017353 : Blo 546805 7017353 := bstep (se 2 (by rfl) ⟨2631507, by rfl⟩ : syracuseStep 7017353 = 5263015) B5263015
theorem B2341457 : Blo 546805 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B3525079 : Blo 546805 3525079 := bstep (se 1 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 3525079 = 5287619) B5287619
theorem B5951033 : Blo 546805 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B547615 : Blo 546805 547615 := bstep (se 1 (by rfl) ⟨410711, by rfl⟩ : syracuseStep 547615 = 821423) B821423
theorem B549351 : Blo 546805 549351 := bstep (se 1 (by rfl) ⟨412013, by rfl⟩ : syracuseStep 549351 = 824027) B824027
theorem B60909043 : Blo 546805 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B3967355 : Blo 546805 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B81212057 : Blo 546805 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B4700105 : Blo 546805 4700105 := bstep (se 2 (by rfl) ⟨1762539, by rfl⟩ : syracuseStep 4700105 = 3525079) B3525079
theorem B1560971 : Blo 546805 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B5920415 : Blo 546805 5920415 := bstep (se 1 (by rfl) ⟨4440311, by rfl⟩ : syracuseStep 5920415 = 8880623) B8880623
theorem B4678235 : Blo 546805 4678235 := bstep (se 1 (by rfl) ⟨3508676, by rfl⟩ : syracuseStep 4678235 = 7017353) B7017353
theorem B4162589 : Blo 546805 4162589 := bstep (se 3 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 4162589 = 1560971) B1560971
theorem B3118823 : Blo 546805 3118823 := bstep (se 1 (by rfl) ⟨2339117, by rfl⟩ : syracuseStep 3118823 = 4678235) B4678235
theorem B54141371 : Blo 546805 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B3946943 : Blo 546805 3946943 := bstep (se 1 (by rfl) ⟨2960207, by rfl⟩ : syracuseStep 3946943 = 5920415) B5920415
theorem B3133403 : Blo 546805 3133403 := bstep (se 1 (by rfl) ⟨2350052, by rfl⟩ : syracuseStep 3133403 = 4700105) B4700105
theorem B2644903 : Blo 546805 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B2631295 : Blo 546805 2631295 := bstep (se 1 (by rfl) ⟨1973471, by rfl⟩ : syracuseStep 2631295 = 3946943) B3946943
theorem B2079215 : Blo 546805 2079215 := bstep (se 1 (by rfl) ⟨1559411, by rfl⟩ : syracuseStep 2079215 = 3118823) B3118823
theorem B14106149 : Blo 546805 14106149 := bstep (se 4 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 14106149 = 2644903) B2644903
theorem B36094247 : Blo 546805 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2775059 : Blo 546805 2775059 := bstep (se 1 (by rfl) ⟨2081294, by rfl⟩ : syracuseStep 2775059 = 4162589) B4162589
theorem B2088935 : Blo 546805 2088935 := bstep (se 1 (by rfl) ⟨1566701, by rfl⟩ : syracuseStep 2088935 = 3133403) B3133403
theorem B3508393 : Blo 546805 3508393 := bstep (se 2 (by rfl) ⟨1315647, by rfl⟩ : syracuseStep 3508393 = 2631295) B2631295
theorem B1386143 : Blo 546805 1386143 := bstep (se 1 (by rfl) ⟨1039607, by rfl⟩ : syracuseStep 1386143 = 2079215) B2079215
theorem B24062831 : Blo 546805 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1850039 : Blo 546805 1850039 := bstep (se 1 (by rfl) ⟨1387529, by rfl⟩ : syracuseStep 1850039 = 2775059) B2775059
theorem B1392623 : Blo 546805 1392623 := bstep (se 1 (by rfl) ⟨1044467, by rfl⟩ : syracuseStep 1392623 = 2088935) B2088935
theorem B9404099 : Blo 546805 9404099 := bstep (se 1 (by rfl) ⟨7053074, by rfl⟩ : syracuseStep 9404099 = 14106149) B14106149
theorem B924095 : Blo 546805 924095 := bstep (se 1 (by rfl) ⟨693071, by rfl⟩ : syracuseStep 924095 = 1386143) B1386143
theorem B6269399 : Blo 546805 6269399 := bstep (se 1 (by rfl) ⟨4702049, by rfl⟩ : syracuseStep 6269399 = 9404099) B9404099
theorem B928415 : Blo 546805 928415 := bstep (se 1 (by rfl) ⟨696311, by rfl⟩ : syracuseStep 928415 = 1392623) B1392623
theorem B16041887 : Blo 546805 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B1233359 : Blo 546805 1233359 := bstep (se 1 (by rfl) ⟨925019, by rfl⟩ : syracuseStep 1233359 = 1850039) B1850039
theorem B4677857 : Blo 546805 4677857 := bstep (se 2 (by rfl) ⟨1754196, by rfl⟩ : syracuseStep 4677857 = 3508393) B3508393
theorem B822239 : Blo 546805 822239 := bstep (se 1 (by rfl) ⟨616679, by rfl⟩ : syracuseStep 822239 = 1233359) B1233359
theorem B3118571 : Blo 546805 3118571 := bstep (se 1 (by rfl) ⟨2338928, by rfl⟩ : syracuseStep 3118571 = 4677857) B4677857
theorem B10694591 : Blo 546805 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B4179599 : Blo 546805 4179599 := bstep (se 1 (by rfl) ⟨3134699, by rfl⟩ : syracuseStep 4179599 = 6269399) B6269399
theorem B616063 : Blo 546805 616063 := bstep (se 1 (by rfl) ⟨462047, by rfl⟩ : syracuseStep 616063 = 924095) B924095
theorem B618943 : Blo 546805 618943 := bstep (se 1 (by rfl) ⟨464207, by rfl⟩ : syracuseStep 618943 = 928415) B928415
theorem B2786399 : Blo 546805 2786399 := bstep (se 1 (by rfl) ⟨2089799, by rfl⟩ : syracuseStep 2786399 = 4179599) B4179599
theorem B821417 : Blo 546805 821417 := bstep (se 2 (by rfl) ⟨308031, by rfl⟩ : syracuseStep 821417 = 616063) B616063
theorem B825257 : Blo 546805 825257 := bstep (se 2 (by rfl) ⟨309471, by rfl⟩ : syracuseStep 825257 = 618943) B618943
theorem B2079047 : Blo 546805 2079047 := bstep (se 1 (by rfl) ⟨1559285, by rfl⟩ : syracuseStep 2079047 = 3118571) B3118571
theorem B7129727 : Blo 546805 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B548159 : Blo 546805 548159 := bstep (se 1 (by rfl) ⟨411119, by rfl⟩ : syracuseStep 548159 = 822239) B822239
theorem B4753151 : Blo 546805 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B1386031 : Blo 546805 1386031 := bstep (se 1 (by rfl) ⟨1039523, by rfl⟩ : syracuseStep 1386031 = 2079047) B2079047
theorem B1857599 : Blo 546805 1857599 := bstep (se 1 (by rfl) ⟨1393199, by rfl⟩ : syracuseStep 1857599 = 2786399) B2786399
theorem B547611 : Blo 546805 547611 := bstep (se 1 (by rfl) ⟨410708, by rfl⟩ : syracuseStep 547611 = 821417) B821417
theorem B550171 : Blo 546805 550171 := bstep (se 1 (by rfl) ⟨412628, by rfl⟩ : syracuseStep 550171 = 825257) B825257
theorem B1848041 : Blo 546805 1848041 := bstep (se 2 (by rfl) ⟨693015, by rfl⟩ : syracuseStep 1848041 = 1386031) B1386031
theorem B3168767 : Blo 546805 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B1238399 : Blo 546805 1238399 := bstep (se 1 (by rfl) ⟨928799, by rfl⟩ : syracuseStep 1238399 = 1857599) B1857599
theorem B825599 : Blo 546805 825599 := bstep (se 1 (by rfl) ⟨619199, by rfl⟩ : syracuseStep 825599 = 1238399) B1238399
theorem B1232027 : Blo 546805 1232027 := bstep (se 1 (by rfl) ⟨924020, by rfl⟩ : syracuseStep 1232027 = 1848041) B1848041
theorem B8450045 : Blo 546805 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B821351 : Blo 546805 821351 := bstep (se 1 (by rfl) ⟨616013, by rfl⟩ : syracuseStep 821351 = 1232027) B1232027
theorem B550399 : Blo 546805 550399 := bstep (se 1 (by rfl) ⟨412799, by rfl⟩ : syracuseStep 550399 = 825599) B825599
theorem B5633363 : Blo 546805 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B3755575 : Blo 546805 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B547567 : Blo 546805 547567 := bstep (se 1 (by rfl) ⟨410675, by rfl⟩ : syracuseStep 547567 = 821351) B821351
theorem B5007433 : Blo 546805 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B6676577 : Blo 546805 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B4451051 : Blo 546805 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B2967367 : Blo 546805 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B3956489 : Blo 546805 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B2637659 : Blo 546805 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B1758439 : Blo 546805 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B2344585 : Blo 546805 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B3126113 : Blo 546805 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B2084075 : Blo 546805 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B1389383 : Blo 546805 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B926255 : Blo 546805 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B617503 : Blo 546805 617503 := bstep (se 1 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 617503 = 926255) B926255
theorem B823337 : Blo 546805 823337 := bstep (se 2 (by rfl) ⟨308751, by rfl⟩ : syracuseStep 823337 = 617503) B617503
theorem B548891 : Blo 546805 548891 := bstep (se 1 (by rfl) ⟨411668, by rfl⟩ : syracuseStep 548891 = 823337) B823337

theorem C0 (j : ℕ) (h1 : 136701 ≤ j) (h2 : j ≤ 137400) : Blo 546805 (4 * j + 3) := by
  interval_cases j
  · exact B546807
  · exact B546811
  · exact B546815
  · exact B546819
  · exact B546823
  · exact B546827
  · exact B546831
  · exact B546835
  · exact B546839
  · exact B546843
  · exact B546847
  · exact B546851
  · exact B546855
  · exact B546859
  · exact B546863
  · exact B546867
  · exact B546871
  · exact B546875
  · exact B546879
  · exact B546883
  · exact B546887
  · exact B546891
  · exact B546895
  · exact B546899
  · exact B546903
  · exact B546907
  · exact B546911
  · exact B546915
  · exact B546919
  · exact B546923
  · exact B546927
  · exact B546931
  · exact B546935
  · exact B546939
  · exact B546943
  · exact B546947
  · exact B546951
  · exact B546955
  · exact B546959
  · exact B546963
  · exact B546967
  · exact B546971
  · exact B546975
  · exact B546979
  · exact B546983
  · exact B546987
  · exact B546991
  · exact B546995
  · exact B546999
  · exact B547003
  · exact B547007
  · exact B547011
  · exact B547015
  · exact B547019
  · exact B547023
  · exact B547027
  · exact B547031
  · exact B547035
  · exact B547039
  · exact B547043
  · exact B547047
  · exact B547051
  · exact B547055
  · exact B547059
  · exact B547063
  · exact B547067
  · exact B547071
  · exact B547075
  · exact B547079
  · exact B547083
  · exact B547087
  · exact B547091
  · exact B547095
  · exact B547099
  · exact B547103
  · exact B547107
  · exact B547111
  · exact B547115
  · exact B547119
  · exact B547123
  · exact B547127
  · exact B547131
  · exact B547135
  · exact B547139
  · exact B547143
  · exact B547147
  · exact B547151
  · exact B547155
  · exact B547159
  · exact B547163
  · exact B547167
  · exact B547171
  · exact B547175
  · exact B547179
  · exact B547183
  · exact B547187
  · exact B547191
  · exact B547195
  · exact B547199
  · exact B547203
  · exact B547207
  · exact B547211
  · exact B547215
  · exact B547219
  · exact B547223
  · exact B547227
  · exact B547231
  · exact B547235
  · exact B547239
  · exact B547243
  · exact B547247
  · exact B547251
  · exact B547255
  · exact B547259
  · exact B547263
  · exact B547267
  · exact B547271
  · exact B547275
  · exact B547279
  · exact B547283
  · exact B547287
  · exact B547291
  · exact B547295
  · exact B547299
  · exact B547303
  · exact B547307
  · exact B547311
  · exact B547315
  · exact B547319
  · exact B547323
  · exact B547327
  · exact B547331
  · exact B547335
  · exact B547339
  · exact B547343
  · exact B547347
  · exact B547351
  · exact B547355
  · exact B547359
  · exact B547363
  · exact B547367
  · exact B547371
  · exact B547375
  · exact B547379
  · exact B547383
  · exact B547387
  · exact B547391
  · exact B547395
  · exact B547399
  · exact B547403
  · exact B547407
  · exact B547411
  · exact B547415
  · exact B547419
  · exact B547423
  · exact B547427
  · exact B547431
  · exact B547435
  · exact B547439
  · exact B547443
  · exact B547447
  · exact B547451
  · exact B547455
  · exact B547459
  · exact B547463
  · exact B547467
  · exact B547471
  · exact B547475
  · exact B547479
  · exact B547483
  · exact B547487
  · exact B547491
  · exact B547495
  · exact B547499
  · exact B547503
  · exact B547507
  · exact B547511
  · exact B547515
  · exact B547519
  · exact B547523
  · exact B547527
  · exact B547531
  · exact B547535
  · exact B547539
  · exact B547543
  · exact B547547
  · exact B547551
  · exact B547555
  · exact B547559
  · exact B547563
  · exact B547567
  · exact B547571
  · exact B547575
  · exact B547579
  · exact B547583
  · exact B547587
  · exact B547591
  · exact B547595
  · exact B547599
  · exact B547603
  · exact B547607
  · exact B547611
  · exact B547615
  · exact B547619
  · exact B547623
  · exact B547627
  · exact B547631
  · exact B547635
  · exact B547639
  · exact B547643
  · exact B547647
  · exact B547651
  · exact B547655
  · exact B547659
  · exact B547663
  · exact B547667
  · exact B547671
  · exact B547675
  · exact B547679
  · exact B547683
  · exact B547687
  · exact B547691
  · exact B547695
  · exact B547699
  · exact B547703
  · exact B547707
  · exact B547711
  · exact B547715
  · exact B547719
  · exact B547723
  · exact B547727
  · exact B547731
  · exact B547735
  · exact B547739
  · exact B547743
  · exact B547747
  · exact B547751
  · exact B547755
  · exact B547759
  · exact B547763
  · exact B547767
  · exact B547771
  · exact B547775
  · exact B547779
  · exact B547783
  · exact B547787
  · exact B547791
  · exact B547795
  · exact B547799
  · exact B547803
  · exact B547807
  · exact B547811
  · exact B547815
  · exact B547819
  · exact B547823
  · exact B547827
  · exact B547831
  · exact B547835
  · exact B547839
  · exact B547843
  · exact B547847
  · exact B547851
  · exact B547855
  · exact B547859
  · exact B547863
  · exact B547867
  · exact B547871
  · exact B547875
  · exact B547879
  · exact B547883
  · exact B547887
  · exact B547891
  · exact B547895
  · exact B547899
  · exact B547903
  · exact B547907
  · exact B547911
  · exact B547915
  · exact B547919
  · exact B547923
  · exact B547927
  · exact B547931
  · exact B547935
  · exact B547939
  · exact B547943
  · exact B547947
  · exact B547951
  · exact B547955
  · exact B547959
  · exact B547963
  · exact B547967
  · exact B547971
  · exact B547975
  · exact B547979
  · exact B547983
  · exact B547987
  · exact B547991
  · exact B547995
  · exact B547999
  · exact B548003
  · exact B548007
  · exact B548011
  · exact B548015
  · exact B548019
  · exact B548023
  · exact B548027
  · exact B548031
  · exact B548035
  · exact B548039
  · exact B548043
  · exact B548047
  · exact B548051
  · exact B548055
  · exact B548059
  · exact B548063
  · exact B548067
  · exact B548071
  · exact B548075
  · exact B548079
  · exact B548083
  · exact B548087
  · exact B548091
  · exact B548095
  · exact B548099
  · exact B548103
  · exact B548107
  · exact B548111
  · exact B548115
  · exact B548119
  · exact B548123
  · exact B548127
  · exact B548131
  · exact B548135
  · exact B548139
  · exact B548143
  · exact B548147
  · exact B548151
  · exact B548155
  · exact B548159
  · exact B548163
  · exact B548167
  · exact B548171
  · exact B548175
  · exact B548179
  · exact B548183
  · exact B548187
  · exact B548191
  · exact B548195
  · exact B548199
  · exact B548203
  · exact B548207
  · exact B548211
  · exact B548215
  · exact B548219
  · exact B548223
  · exact B548227
  · exact B548231
  · exact B548235
  · exact B548239
  · exact B548243
  · exact B548247
  · exact B548251
  · exact B548255
  · exact B548259
  · exact B548263
  · exact B548267
  · exact B548271
  · exact B548275
  · exact B548279
  · exact B548283
  · exact B548287
  · exact B548291
  · exact B548295
  · exact B548299
  · exact B548303
  · exact B548307
  · exact B548311
  · exact B548315
  · exact B548319
  · exact B548323
  · exact B548327
  · exact B548331
  · exact B548335
  · exact B548339
  · exact B548343
  · exact B548347
  · exact B548351
  · exact B548355
  · exact B548359
  · exact B548363
  · exact B548367
  · exact B548371
  · exact B548375
  · exact B548379
  · exact B548383
  · exact B548387
  · exact B548391
  · exact B548395
  · exact B548399
  · exact B548403
  · exact B548407
  · exact B548411
  · exact B548415
  · exact B548419
  · exact B548423
  · exact B548427
  · exact B548431
  · exact B548435
  · exact B548439
  · exact B548443
  · exact B548447
  · exact B548451
  · exact B548455
  · exact B548459
  · exact B548463
  · exact B548467
  · exact B548471
  · exact B548475
  · exact B548479
  · exact B548483
  · exact B548487
  · exact B548491
  · exact B548495
  · exact B548499
  · exact B548503
  · exact B548507
  · exact B548511
  · exact B548515
  · exact B548519
  · exact B548523
  · exact B548527
  · exact B548531
  · exact B548535
  · exact B548539
  · exact B548543
  · exact B548547
  · exact B548551
  · exact B548555
  · exact B548559
  · exact B548563
  · exact B548567
  · exact B548571
  · exact B548575
  · exact B548579
  · exact B548583
  · exact B548587
  · exact B548591
  · exact B548595
  · exact B548599
  · exact B548603
  · exact B548607
  · exact B548611
  · exact B548615
  · exact B548619
  · exact B548623
  · exact B548627
  · exact B548631
  · exact B548635
  · exact B548639
  · exact B548643
  · exact B548647
  · exact B548651
  · exact B548655
  · exact B548659
  · exact B548663
  · exact B548667
  · exact B548671
  · exact B548675
  · exact B548679
  · exact B548683
  · exact B548687
  · exact B548691
  · exact B548695
  · exact B548699
  · exact B548703
  · exact B548707
  · exact B548711
  · exact B548715
  · exact B548719
  · exact B548723
  · exact B548727
  · exact B548731
  · exact B548735
  · exact B548739
  · exact B548743
  · exact B548747
  · exact B548751
  · exact B548755
  · exact B548759
  · exact B548763
  · exact B548767
  · exact B548771
  · exact B548775
  · exact B548779
  · exact B548783
  · exact B548787
  · exact B548791
  · exact B548795
  · exact B548799
  · exact B548803
  · exact B548807
  · exact B548811
  · exact B548815
  · exact B548819
  · exact B548823
  · exact B548827
  · exact B548831
  · exact B548835
  · exact B548839
  · exact B548843
  · exact B548847
  · exact B548851
  · exact B548855
  · exact B548859
  · exact B548863
  · exact B548867
  · exact B548871
  · exact B548875
  · exact B548879
  · exact B548883
  · exact B548887
  · exact B548891
  · exact B548895
  · exact B548899
  · exact B548903
  · exact B548907
  · exact B548911
  · exact B548915
  · exact B548919
  · exact B548923
  · exact B548927
  · exact B548931
  · exact B548935
  · exact B548939
  · exact B548943
  · exact B548947
  · exact B548951
  · exact B548955
  · exact B548959
  · exact B548963
  · exact B548967
  · exact B548971
  · exact B548975
  · exact B548979
  · exact B548983
  · exact B548987
  · exact B548991
  · exact B548995
  · exact B548999
  · exact B549003
  · exact B549007
  · exact B549011
  · exact B549015
  · exact B549019
  · exact B549023
  · exact B549027
  · exact B549031
  · exact B549035
  · exact B549039
  · exact B549043
  · exact B549047
  · exact B549051
  · exact B549055
  · exact B549059
  · exact B549063
  · exact B549067
  · exact B549071
  · exact B549075
  · exact B549079
  · exact B549083
  · exact B549087
  · exact B549091
  · exact B549095
  · exact B549099
  · exact B549103
  · exact B549107
  · exact B549111
  · exact B549115
  · exact B549119
  · exact B549123
  · exact B549127
  · exact B549131
  · exact B549135
  · exact B549139
  · exact B549143
  · exact B549147
  · exact B549151
  · exact B549155
  · exact B549159
  · exact B549163
  · exact B549167
  · exact B549171
  · exact B549175
  · exact B549179
  · exact B549183
  · exact B549187
  · exact B549191
  · exact B549195
  · exact B549199
  · exact B549203
  · exact B549207
  · exact B549211
  · exact B549215
  · exact B549219
  · exact B549223
  · exact B549227
  · exact B549231
  · exact B549235
  · exact B549239
  · exact B549243
  · exact B549247
  · exact B549251
  · exact B549255
  · exact B549259
  · exact B549263
  · exact B549267
  · exact B549271
  · exact B549275
  · exact B549279
  · exact B549283
  · exact B549287
  · exact B549291
  · exact B549295
  · exact B549299
  · exact B549303
  · exact B549307
  · exact B549311
  · exact B549315
  · exact B549319
  · exact B549323
  · exact B549327
  · exact B549331
  · exact B549335
  · exact B549339
  · exact B549343
  · exact B549347
  · exact B549351
  · exact B549355
  · exact B549359
  · exact B549363
  · exact B549367
  · exact B549371
  · exact B549375
  · exact B549379
  · exact B549383
  · exact B549387
  · exact B549391
  · exact B549395
  · exact B549399
  · exact B549403
  · exact B549407
  · exact B549411
  · exact B549415
  · exact B549419
  · exact B549423
  · exact B549427
  · exact B549431
  · exact B549435
  · exact B549439
  · exact B549443
  · exact B549447
  · exact B549451
  · exact B549455
  · exact B549459
  · exact B549463
  · exact B549467
  · exact B549471
  · exact B549475
  · exact B549479
  · exact B549483
  · exact B549487
  · exact B549491
  · exact B549495
  · exact B549499
  · exact B549503
  · exact B549507
  · exact B549511
  · exact B549515
  · exact B549519
  · exact B549523
  · exact B549527
  · exact B549531
  · exact B549535
  · exact B549539
  · exact B549543
  · exact B549547
  · exact B549551
  · exact B549555
  · exact B549559
  · exact B549563
  · exact B549567
  · exact B549571
  · exact B549575
  · exact B549579
  · exact B549583
  · exact B549587
  · exact B549591
  · exact B549595
  · exact B549599
  · exact B549603

theorem C1 (j : ℕ) (h1 : 137401 ≤ j) (h2 : j ≤ 137700) : Blo 546805 (4 * j + 3) := by
  interval_cases j
  · exact B549607
  · exact B549611
  · exact B549615
  · exact B549619
  · exact B549623
  · exact B549627
  · exact B549631
  · exact B549635
  · exact B549639
  · exact B549643
  · exact B549647
  · exact B549651
  · exact B549655
  · exact B549659
  · exact B549663
  · exact B549667
  · exact B549671
  · exact B549675
  · exact B549679
  · exact B549683
  · exact B549687
  · exact B549691
  · exact B549695
  · exact B549699
  · exact B549703
  · exact B549707
  · exact B549711
  · exact B549715
  · exact B549719
  · exact B549723
  · exact B549727
  · exact B549731
  · exact B549735
  · exact B549739
  · exact B549743
  · exact B549747
  · exact B549751
  · exact B549755
  · exact B549759
  · exact B549763
  · exact B549767
  · exact B549771
  · exact B549775
  · exact B549779
  · exact B549783
  · exact B549787
  · exact B549791
  · exact B549795
  · exact B549799
  · exact B549803
  · exact B549807
  · exact B549811
  · exact B549815
  · exact B549819
  · exact B549823
  · exact B549827
  · exact B549831
  · exact B549835
  · exact B549839
  · exact B549843
  · exact B549847
  · exact B549851
  · exact B549855
  · exact B549859
  · exact B549863
  · exact B549867
  · exact B549871
  · exact B549875
  · exact B549879
  · exact B549883
  · exact B549887
  · exact B549891
  · exact B549895
  · exact B549899
  · exact B549903
  · exact B549907
  · exact B549911
  · exact B549915
  · exact B549919
  · exact B549923
  · exact B549927
  · exact B549931
  · exact B549935
  · exact B549939
  · exact B549943
  · exact B549947
  · exact B549951
  · exact B549955
  · exact B549959
  · exact B549963
  · exact B549967
  · exact B549971
  · exact B549975
  · exact B549979
  · exact B549983
  · exact B549987
  · exact B549991
  · exact B549995
  · exact B549999
  · exact B550003
  · exact B550007
  · exact B550011
  · exact B550015
  · exact B550019
  · exact B550023
  · exact B550027
  · exact B550031
  · exact B550035
  · exact B550039
  · exact B550043
  · exact B550047
  · exact B550051
  · exact B550055
  · exact B550059
  · exact B550063
  · exact B550067
  · exact B550071
  · exact B550075
  · exact B550079
  · exact B550083
  · exact B550087
  · exact B550091
  · exact B550095
  · exact B550099
  · exact B550103
  · exact B550107
  · exact B550111
  · exact B550115
  · exact B550119
  · exact B550123
  · exact B550127
  · exact B550131
  · exact B550135
  · exact B550139
  · exact B550143
  · exact B550147
  · exact B550151
  · exact B550155
  · exact B550159
  · exact B550163
  · exact B550167
  · exact B550171
  · exact B550175
  · exact B550179
  · exact B550183
  · exact B550187
  · exact B550191
  · exact B550195
  · exact B550199
  · exact B550203
  · exact B550207
  · exact B550211
  · exact B550215
  · exact B550219
  · exact B550223
  · exact B550227
  · exact B550231
  · exact B550235
  · exact B550239
  · exact B550243
  · exact B550247
  · exact B550251
  · exact B550255
  · exact B550259
  · exact B550263
  · exact B550267
  · exact B550271
  · exact B550275
  · exact B550279
  · exact B550283
  · exact B550287
  · exact B550291
  · exact B550295
  · exact B550299
  · exact B550303
  · exact B550307
  · exact B550311
  · exact B550315
  · exact B550319
  · exact B550323
  · exact B550327
  · exact B550331
  · exact B550335
  · exact B550339
  · exact B550343
  · exact B550347
  · exact B550351
  · exact B550355
  · exact B550359
  · exact B550363
  · exact B550367
  · exact B550371
  · exact B550375
  · exact B550379
  · exact B550383
  · exact B550387
  · exact B550391
  · exact B550395
  · exact B550399
  · exact B550403
  · exact B550407
  · exact B550411
  · exact B550415
  · exact B550419
  · exact B550423
  · exact B550427
  · exact B550431
  · exact B550435
  · exact B550439
  · exact B550443
  · exact B550447
  · exact B550451
  · exact B550455
  · exact B550459
  · exact B550463
  · exact B550467
  · exact B550471
  · exact B550475
  · exact B550479
  · exact B550483
  · exact B550487
  · exact B550491
  · exact B550495
  · exact B550499
  · exact B550503
  · exact B550507
  · exact B550511
  · exact B550515
  · exact B550519
  · exact B550523
  · exact B550527
  · exact B550531
  · exact B550535
  · exact B550539
  · exact B550543
  · exact B550547
  · exact B550551
  · exact B550555
  · exact B550559
  · exact B550563
  · exact B550567
  · exact B550571
  · exact B550575
  · exact B550579
  · exact B550583
  · exact B550587
  · exact B550591
  · exact B550595
  · exact B550599
  · exact B550603
  · exact B550607
  · exact B550611
  · exact B550615
  · exact B550619
  · exact B550623
  · exact B550627
  · exact B550631
  · exact B550635
  · exact B550639
  · exact B550643
  · exact B550647
  · exact B550651
  · exact B550655
  · exact B550659
  · exact B550663
  · exact B550667
  · exact B550671
  · exact B550675
  · exact B550679
  · exact B550683
  · exact B550687
  · exact B550691
  · exact B550695
  · exact B550699
  · exact B550703
  · exact B550707
  · exact B550711
  · exact B550715
  · exact B550719
  · exact B550723
  · exact B550727
  · exact B550731
  · exact B550735
  · exact B550739
  · exact B550743
  · exact B550747
  · exact B550751
  · exact B550755
  · exact B550759
  · exact B550763
  · exact B550767
  · exact B550771
  · exact B550775
  · exact B550779
  · exact B550783
  · exact B550787
  · exact B550791
  · exact B550795
  · exact B550799
  · exact B550803

theorem solution (m : ℕ) (hlo : 546805 ≤ m) (hhi : m ≤ 550805) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 136701 ≤ j := by omega
    have hj2 : j ≤ 137700 := by omega
    have hb : Blo 546805 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 137401 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
