-- Prove2me | solution 1 for syracuse_descends_range_1266451_1268451
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:26.30887+00:00
-- url     : https://prove2.me/submissions/939476c2-17bc-4edd-9d97-44bb8a549aec

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


theorem B1523713 : Blo 1266451 1523713 := bbase (se 2 (by rfl) ⟨571392, by rfl⟩ : syracuseStep 1523713 = 1142785) (by norm_num)
theorem B2850821 : Blo 1266451 2850821 := bbase (se 4 (by rfl) ⟨267264, by rfl⟩ : syracuseStep 2850821 = 534529) (by norm_num)
theorem B1900565 : Blo 1266451 1900565 := bbase (se 6 (by rfl) ⟨44544, by rfl⟩ : syracuseStep 1900565 = 89089) (by norm_num)
theorem B1425433 : Blo 1266451 1425433 := bbase (se 2 (by rfl) ⟨534537, by rfl⟩ : syracuseStep 1425433 = 1069075) (by norm_num)
theorem B1523741 : Blo 1266451 1523741 := bbase (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) (by norm_num)
theorem B3711013 : Blo 1266451 3711013 := bbase (se 4 (by rfl) ⟨347907, by rfl⟩ : syracuseStep 3711013 = 695815) (by norm_num)
theorem B1900589 : Blo 1266451 1900589 := bbase (se 3 (by rfl) ⟨356360, by rfl⟩ : syracuseStep 1900589 = 712721) (by norm_num)
theorem B6414389 : Blo 1266451 6414389 := bbase (se 5 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 6414389 = 601349) (by norm_num)
theorem B1425469 : Blo 1266451 1425469 := bbase (se 3 (by rfl) ⟨267275, by rfl⟩ : syracuseStep 1425469 = 534551) (by norm_num)
theorem B1900613 : Blo 1266451 1900613 := bbase (se 4 (by rfl) ⟨178182, by rfl⟩ : syracuseStep 1900613 = 356365) (by norm_num)
theorem B2850893 : Blo 1266451 2850893 := bbase (se 3 (by rfl) ⟨534542, by rfl⟩ : syracuseStep 2850893 = 1069085) (by norm_num)
theorem B2138197 : Blo 1266451 2138197 := bbase (se 8 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 2138197 = 25057) (by norm_num)
theorem B1900637 : Blo 1266451 1900637 := bbase (se 3 (by rfl) ⟨356369, by rfl⟩ : syracuseStep 1900637 = 712739) (by norm_num)
theorem B1425505 : Blo 1266451 1425505 := bbase (se 2 (by rfl) ⟨534564, by rfl⟩ : syracuseStep 1425505 = 1069129) (by norm_num)
theorem B1900661 : Blo 1266451 1900661 := bbase (se 5 (by rfl) ⟨89093, by rfl⟩ : syracuseStep 1900661 = 178187) (by norm_num)
theorem B1425541 : Blo 1266451 1425541 := bbase (se 4 (by rfl) ⟨133644, by rfl⟩ : syracuseStep 1425541 = 267289) (by norm_num)
theorem B1900685 : Blo 1266451 1900685 := bbase (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) (by norm_num)
theorem B2850965 : Blo 1266451 2850965 := bbase (se 6 (by rfl) ⟨66819, by rfl⟩ : syracuseStep 2850965 = 133639) (by norm_num)
theorem B1900709 : Blo 1266451 1900709 := bbase (se 4 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 1900709 = 356383) (by norm_num)
theorem B1425577 : Blo 1266451 1425577 := bbase (se 2 (by rfl) ⟨534591, by rfl⟩ : syracuseStep 1425577 = 1069183) (by norm_num)
theorem B2138285 : Blo 1266451 2138285 := bbase (se 3 (by rfl) ⟨400928, by rfl⟩ : syracuseStep 2138285 = 801857) (by norm_num)
theorem B1900733 : Blo 1266451 1900733 := bbase (se 3 (by rfl) ⟨356387, by rfl⟩ : syracuseStep 1900733 = 712775) (by norm_num)
theorem B4276421 : Blo 1266451 4276421 := bbase (se 4 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 4276421 = 801829) (by norm_num)
theorem B1425613 : Blo 1266451 1425613 := bbase (se 3 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 1425613 = 534605) (by norm_num)
theorem B1900757 : Blo 1266451 1900757 := bbase (se 7 (by rfl) ⟨22274, by rfl⟩ : syracuseStep 1900757 = 44549) (by norm_num)
theorem B2851037 : Blo 1266451 2851037 := bbase (se 3 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 2851037 = 1069139) (by norm_num)
theorem B1900781 : Blo 1266451 1900781 := bbase (se 3 (by rfl) ⟨356396, by rfl⟩ : syracuseStep 1900781 = 712793) (by norm_num)
theorem B1425649 : Blo 1266451 1425649 := bbase (se 2 (by rfl) ⟨534618, by rfl⟩ : syracuseStep 1425649 = 1069237) (by norm_num)
theorem B1900805 : Blo 1266451 1900805 := bbase (se 4 (by rfl) ⟨178200, by rfl⟩ : syracuseStep 1900805 = 356401) (by norm_num)
theorem B1425685 : Blo 1266451 1425685 := bbase (se 6 (by rfl) ⟨33414, by rfl⟩ : syracuseStep 1425685 = 66829) (by norm_num)
theorem B1900829 : Blo 1266451 1900829 := bbase (se 3 (by rfl) ⟨356405, by rfl⟩ : syracuseStep 1900829 = 712811) (by norm_num)
theorem B2851109 : Blo 1266451 2851109 := bbase (se 4 (by rfl) ⟨267291, by rfl⟩ : syracuseStep 2851109 = 534583) (by norm_num)
theorem B2138413 : Blo 1266451 2138413 := bbase (se 3 (by rfl) ⟨400952, by rfl⟩ : syracuseStep 2138413 = 801905) (by norm_num)
theorem B1900853 : Blo 1266451 1900853 := bbase (se 5 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 1900853 = 178205) (by norm_num)
theorem B1425721 : Blo 1266451 1425721 := bbase (se 2 (by rfl) ⟨534645, by rfl⟩ : syracuseStep 1425721 = 1069291) (by norm_num)
theorem B1900877 : Blo 1266451 1900877 := bbase (se 3 (by rfl) ⟨356414, by rfl⟩ : syracuseStep 1900877 = 712829) (by norm_num)
theorem B1425757 : Blo 1266451 1425757 := bbase (se 3 (by rfl) ⟨267329, by rfl⟩ : syracuseStep 1425757 = 534659) (by norm_num)
theorem B1900901 : Blo 1266451 1900901 := bbase (se 4 (by rfl) ⟨178209, by rfl⟩ : syracuseStep 1900901 = 356419) (by norm_num)
theorem B2851181 : Blo 1266451 2851181 := bbase (se 3 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 2851181 = 1069193) (by norm_num)
theorem B4809077 : Blo 1266451 4809077 := bbase (se 5 (by rfl) ⟨225425, by rfl⟩ : syracuseStep 4809077 = 450851) (by norm_num)
theorem B1900925 : Blo 1266451 1900925 := bbase (se 3 (by rfl) ⟨356423, by rfl⟩ : syracuseStep 1900925 = 712847) (by norm_num)
theorem B1425793 : Blo 1266451 1425793 := bbase (se 2 (by rfl) ⟨534672, by rfl⟩ : syracuseStep 1425793 = 1069345) (by norm_num)
theorem B2138501 : Blo 1266451 2138501 := bbase (se 4 (by rfl) ⟨200484, by rfl⟩ : syracuseStep 2138501 = 400969) (by norm_num)
theorem B1900949 : Blo 1266451 1900949 := bbase (se 6 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 1900949 = 89107) (by norm_num)
theorem B1425829 : Blo 1266451 1425829 := bbase (se 4 (by rfl) ⟨133671, by rfl⟩ : syracuseStep 1425829 = 267343) (by norm_num)
theorem B1900973 : Blo 1266451 1900973 := bbase (se 3 (by rfl) ⟨356432, by rfl⟩ : syracuseStep 1900973 = 712865) (by norm_num)
theorem B2851253 : Blo 1266451 2851253 := bbase (se 5 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 2851253 = 267305) (by norm_num)
theorem B1900997 : Blo 1266451 1900997 := bbase (se 4 (by rfl) ⟨178218, by rfl⟩ : syracuseStep 1900997 = 356437) (by norm_num)
theorem B1425865 : Blo 1266451 1425865 := bbase (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) (by norm_num)
theorem B1901021 : Blo 1266451 1901021 := bbase (se 3 (by rfl) ⟨356441, by rfl⟩ : syracuseStep 1901021 = 712883) (by norm_num)
theorem B1425901 : Blo 1266451 1425901 := bbase (se 3 (by rfl) ⟨267356, by rfl⟩ : syracuseStep 1425901 = 534713) (by norm_num)
theorem B1901045 : Blo 1266451 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B2851325 : Blo 1266451 2851325 := bbase (se 3 (by rfl) ⟨534623, by rfl⟩ : syracuseStep 2851325 = 1069247) (by norm_num)
theorem B2138629 : Blo 1266451 2138629 := bbase (se 4 (by rfl) ⟨200496, by rfl⟩ : syracuseStep 2138629 = 400993) (by norm_num)
theorem B1901069 : Blo 1266451 1901069 := bbase (se 3 (by rfl) ⟨356450, by rfl⟩ : syracuseStep 1901069 = 712901) (by norm_num)
theorem B1425937 : Blo 1266451 1425937 := bbase (se 2 (by rfl) ⟨534726, by rfl⟩ : syracuseStep 1425937 = 1069453) (by norm_num)
theorem B1901093 : Blo 1266451 1901093 := bbase (se 4 (by rfl) ⟨178227, by rfl⟩ : syracuseStep 1901093 = 356455) (by norm_num)
theorem B1425973 : Blo 1266451 1425973 := bbase (se 5 (by rfl) ⟨66842, by rfl⟩ : syracuseStep 1425973 = 133685) (by norm_num)
theorem B8127029 : Blo 1266451 8127029 := bbase (se 5 (by rfl) ⟨380954, by rfl⟩ : syracuseStep 8127029 = 761909) (by norm_num)
theorem B1901117 : Blo 1266451 1901117 := bbase (se 3 (by rfl) ⟨356459, by rfl⟩ : syracuseStep 1901117 = 712919) (by norm_num)
theorem B2851397 : Blo 1266451 2851397 := bbase (se 4 (by rfl) ⟨267318, by rfl⟩ : syracuseStep 2851397 = 534637) (by norm_num)
theorem B1901141 : Blo 1266451 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B1426009 : Blo 1266451 1426009 := bbase (se 2 (by rfl) ⟨534753, by rfl⟩ : syracuseStep 1426009 = 1069507) (by norm_num)
theorem B2138717 : Blo 1266451 2138717 := bbase (se 3 (by rfl) ⟨401009, by rfl⟩ : syracuseStep 2138717 = 802019) (by norm_num)
theorem B1901165 : Blo 1266451 1901165 := bbase (se 3 (by rfl) ⟨356468, by rfl⟩ : syracuseStep 1901165 = 712937) (by norm_num)
theorem B4276853 : Blo 1266451 4276853 := bbase (se 5 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 4276853 = 400955) (by norm_num)
theorem B1426045 : Blo 1266451 1426045 := bbase (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) (by norm_num)
theorem B1901189 : Blo 1266451 1901189 := bbase (se 4 (by rfl) ⟨178236, by rfl⟩ : syracuseStep 1901189 = 356473) (by norm_num)
theorem B2851469 : Blo 1266451 2851469 := bbase (se 3 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 2851469 = 1069301) (by norm_num)
theorem B4809365 : Blo 1266451 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B1901213 : Blo 1266451 1901213 := bbase (se 3 (by rfl) ⟨356477, by rfl⟩ : syracuseStep 1901213 = 712955) (by norm_num)
theorem B1426081 : Blo 1266451 1426081 := bbase (se 2 (by rfl) ⟨534780, by rfl⟩ : syracuseStep 1426081 = 1069561) (by norm_num)
theorem B1901237 : Blo 1266451 1901237 := bbase (se 5 (by rfl) ⟨89120, by rfl⟩ : syracuseStep 1901237 = 178241) (by norm_num)
theorem B1426117 : Blo 1266451 1426117 := bbase (se 4 (by rfl) ⟨133698, by rfl⟩ : syracuseStep 1426117 = 267397) (by norm_num)
theorem B1901261 : Blo 1266451 1901261 := bbase (se 3 (by rfl) ⟨356486, by rfl⟩ : syracuseStep 1901261 = 712973) (by norm_num)
theorem B2851541 : Blo 1266451 2851541 := bbase (se 7 (by rfl) ⟨33416, by rfl⟩ : syracuseStep 2851541 = 66833) (by norm_num)
theorem B2138845 : Blo 1266451 2138845 := bbase (se 3 (by rfl) ⟨401033, by rfl⟩ : syracuseStep 2138845 = 802067) (by norm_num)
theorem B1901285 : Blo 1266451 1901285 := bbase (se 4 (by rfl) ⟨178245, by rfl⟩ : syracuseStep 1901285 = 356491) (by norm_num)
theorem B1426153 : Blo 1266451 1426153 := bbase (se 2 (by rfl) ⟨534807, by rfl⟩ : syracuseStep 1426153 = 1069615) (by norm_num)
theorem B6087413 : Blo 1266451 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B1901309 : Blo 1266451 1901309 := bbase (se 3 (by rfl) ⟨356495, by rfl⟩ : syracuseStep 1901309 = 712991) (by norm_num)
theorem B1426189 : Blo 1266451 1426189 := bbase (se 3 (by rfl) ⟨267410, by rfl⟩ : syracuseStep 1426189 = 534821) (by norm_num)
theorem B1901333 : Blo 1266451 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B2851613 : Blo 1266451 2851613 := bbase (se 3 (by rfl) ⟨534677, by rfl⟩ : syracuseStep 2851613 = 1069355) (by norm_num)
theorem B1352485 : Blo 1266451 1352485 := bbase (se 4 (by rfl) ⟨126795, by rfl⟩ : syracuseStep 1352485 = 253591) (by norm_num)
theorem B1901357 : Blo 1266451 1901357 := bbase (se 3 (by rfl) ⟨356504, by rfl⟩ : syracuseStep 1901357 = 713009) (by norm_num)
theorem B1426225 : Blo 1266451 1426225 := bbase (se 2 (by rfl) ⟨534834, by rfl⟩ : syracuseStep 1426225 = 1069669) (by norm_num)
theorem B2138933 : Blo 1266451 2138933 := bbase (se 5 (by rfl) ⟨100262, by rfl⟩ : syracuseStep 2138933 = 200525) (by norm_num)
theorem B1901381 : Blo 1266451 1901381 := bbase (se 4 (by rfl) ⟨178254, by rfl⟩ : syracuseStep 1901381 = 356509) (by norm_num)
theorem B1426261 : Blo 1266451 1426261 := bbase (se 9 (by rfl) ⟨4178, by rfl⟩ : syracuseStep 1426261 = 8357) (by norm_num)
theorem B1901405 : Blo 1266451 1901405 := bbase (se 3 (by rfl) ⟨356513, by rfl⟩ : syracuseStep 1901405 = 713027) (by norm_num)
theorem B2851685 : Blo 1266451 2851685 := bbase (se 4 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 2851685 = 534691) (by norm_num)
theorem B1352557 : Blo 1266451 1352557 := bbase (se 3 (by rfl) ⟨253604, by rfl⟩ : syracuseStep 1352557 = 507209) (by norm_num)
theorem B1901429 : Blo 1266451 1901429 := bbase (se 5 (by rfl) ⟨89129, by rfl⟩ : syracuseStep 1901429 = 178259) (by norm_num)
theorem B1426297 : Blo 1266451 1426297 := bbase (se 2 (by rfl) ⟨534861, by rfl⟩ : syracuseStep 1426297 = 1069723) (by norm_num)
theorem B1901453 : Blo 1266451 1901453 := bbase (se 3 (by rfl) ⟨356522, by rfl⟩ : syracuseStep 1901453 = 713045) (by norm_num)
theorem B1426333 : Blo 1266451 1426333 := bbase (se 3 (by rfl) ⟨267437, by rfl⟩ : syracuseStep 1426333 = 534875) (by norm_num)
theorem B1901477 : Blo 1266451 1901477 := bbase (se 4 (by rfl) ⟨178263, by rfl⟩ : syracuseStep 1901477 = 356527) (by norm_num)
theorem B2851757 : Blo 1266451 2851757 := bbase (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) (by norm_num)
theorem B2139061 : Blo 1266451 2139061 := bbase (se 5 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 2139061 = 200537) (by norm_num)
theorem B1901501 : Blo 1266451 1901501 := bbase (se 3 (by rfl) ⟨356531, by rfl⟩ : syracuseStep 1901501 = 713063) (by norm_num)
theorem B1426369 : Blo 1266451 1426369 := bbase (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) (by norm_num)
theorem B1901525 : Blo 1266451 1901525 := bbase (se 7 (by rfl) ⟨22283, by rfl⟩ : syracuseStep 1901525 = 44567) (by norm_num)
theorem B1426405 : Blo 1266451 1426405 := bbase (se 4 (by rfl) ⟨133725, by rfl⟩ : syracuseStep 1426405 = 267451) (by norm_num)
theorem B1901549 : Blo 1266451 1901549 := bbase (se 3 (by rfl) ⟨356540, by rfl⟩ : syracuseStep 1901549 = 713081) (by norm_num)
theorem B2851829 : Blo 1266451 2851829 := bbase (se 5 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 2851829 = 267359) (by norm_num)
theorem B1901573 : Blo 1266451 1901573 := bbase (se 4 (by rfl) ⟨178272, by rfl⟩ : syracuseStep 1901573 = 356545) (by norm_num)
theorem B1426441 : Blo 1266451 1426441 := bbase (se 2 (by rfl) ⟨534915, by rfl⟩ : syracuseStep 1426441 = 1069831) (by norm_num)
theorem B2139149 : Blo 1266451 2139149 := bbase (se 3 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 2139149 = 802181) (by norm_num)
theorem B1901597 : Blo 1266451 1901597 := bbase (se 3 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 1901597 = 713099) (by norm_num)
theorem B1352737 : Blo 1266451 1352737 := bbase (se 2 (by rfl) ⟨507276, by rfl⟩ : syracuseStep 1352737 = 1014553) (by norm_num)
theorem B4277285 : Blo 1266451 4277285 := bbase (se 4 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 4277285 = 801991) (by norm_num)
theorem B1426477 : Blo 1266451 1426477 := bbase (se 3 (by rfl) ⟨267464, by rfl⟩ : syracuseStep 1426477 = 534929) (by norm_num)
theorem B1901621 : Blo 1266451 1901621 := bbase (se 5 (by rfl) ⟨89138, by rfl⟩ : syracuseStep 1901621 = 178277) (by norm_num)
theorem B2851901 : Blo 1266451 2851901 := bbase (se 3 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 2851901 = 1069463) (by norm_num)
theorem B1803341 : Blo 1266451 1803341 := bbase (se 3 (by rfl) ⟨338126, by rfl⟩ : syracuseStep 1803341 = 676253) (by norm_num)
theorem B1901645 : Blo 1266451 1901645 := bbase (se 3 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 1901645 = 713117) (by norm_num)
theorem B3253325 : Blo 1266451 3253325 := bbase (se 3 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 3253325 = 1219997) (by norm_num)
theorem B1426513 : Blo 1266451 1426513 := bbase (se 2 (by rfl) ⟨534942, by rfl⟩ : syracuseStep 1426513 = 1069885) (by norm_num)
theorem B1901669 : Blo 1266451 1901669 := bbase (se 4 (by rfl) ⟨178281, by rfl⟩ : syracuseStep 1901669 = 356563) (by norm_num)
theorem B1426549 : Blo 1266451 1426549 := bbase (se 5 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 1426549 = 133739) (by norm_num)
theorem B1901693 : Blo 1266451 1901693 := bbase (se 3 (by rfl) ⟨356567, by rfl⟩ : syracuseStep 1901693 = 713135) (by norm_num)
theorem B2851973 : Blo 1266451 2851973 := bbase (se 4 (by rfl) ⟨267372, by rfl⟩ : syracuseStep 2851973 = 534745) (by norm_num)
theorem B2139277 : Blo 1266451 2139277 := bbase (se 3 (by rfl) ⟨401114, by rfl⟩ : syracuseStep 2139277 = 802229) (by norm_num)
theorem B1901717 : Blo 1266451 1901717 := bbase (se 6 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 1901717 = 89143) (by norm_num)
theorem B1426585 : Blo 1266451 1426585 := bbase (se 2 (by rfl) ⟨534969, by rfl⟩ : syracuseStep 1426585 = 1069939) (by norm_num)
theorem B1803421 : Blo 1266451 1803421 := bbase (se 3 (by rfl) ⟨338141, by rfl⟩ : syracuseStep 1803421 = 676283) (by norm_num)
theorem B1901741 : Blo 1266451 1901741 := bbase (se 3 (by rfl) ⟨356576, by rfl⟩ : syracuseStep 1901741 = 713153) (by norm_num)
theorem B1426621 : Blo 1266451 1426621 := bbase (se 3 (by rfl) ⟨267491, by rfl⟩ : syracuseStep 1426621 = 534983) (by norm_num)
theorem B2196677 : Blo 1266451 2196677 := bbase (se 4 (by rfl) ⟨205938, by rfl⟩ : syracuseStep 2196677 = 411877) (by norm_num)
theorem B1901765 : Blo 1266451 1901765 := bbase (se 4 (by rfl) ⟨178290, by rfl⟩ : syracuseStep 1901765 = 356581) (by norm_num)
theorem B2852045 : Blo 1266451 2852045 := bbase (se 3 (by rfl) ⟨534758, by rfl⟩ : syracuseStep 2852045 = 1069517) (by norm_num)
theorem B1901789 : Blo 1266451 1901789 := bbase (se 3 (by rfl) ⟨356585, by rfl⟩ : syracuseStep 1901789 = 713171) (by norm_num)
theorem B1426657 : Blo 1266451 1426657 := bbase (se 2 (by rfl) ⟨534996, by rfl⟩ : syracuseStep 1426657 = 1069993) (by norm_num)
theorem B2139365 : Blo 1266451 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B1901813 : Blo 1266451 1901813 := bbase (se 5 (by rfl) ⟨89147, by rfl⟩ : syracuseStep 1901813 = 178295) (by norm_num)
theorem B1426693 : Blo 1266451 1426693 := bbase (se 4 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 1426693 = 267505) (by norm_num)
theorem B1901837 : Blo 1266451 1901837 := bbase (se 3 (by rfl) ⟨356594, by rfl⟩ : syracuseStep 1901837 = 713189) (by norm_num)
theorem B1803541 : Blo 1266451 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B2852117 : Blo 1266451 2852117 := bbase (se 6 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 2852117 = 133693) (by norm_num)
theorem B1901861 : Blo 1266451 1901861 := bbase (se 4 (by rfl) ⟨178299, by rfl⟩ : syracuseStep 1901861 = 356599) (by norm_num)
theorem B1426729 : Blo 1266451 1426729 := bbase (se 2 (by rfl) ⟨535023, by rfl⟩ : syracuseStep 1426729 = 1070047) (by norm_num)
theorem B1901885 : Blo 1266451 1901885 := bbase (se 3 (by rfl) ⟨356603, by rfl⟩ : syracuseStep 1901885 = 713207) (by norm_num)
theorem B6415685 : Blo 1266451 6415685 := bbase (se 4 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 6415685 = 1202941) (by norm_num)
theorem B1713485 : Blo 1266451 1713485 := bbase (se 3 (by rfl) ⟨321278, by rfl⟩ : syracuseStep 1713485 = 642557) (by norm_num)
theorem B1426765 : Blo 1266451 1426765 := bbase (se 3 (by rfl) ⟨267518, by rfl⟩ : syracuseStep 1426765 = 535037) (by norm_num)
theorem B1901909 : Blo 1266451 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B2852189 : Blo 1266451 2852189 := bbase (se 3 (by rfl) ⟨534785, by rfl⟩ : syracuseStep 2852189 = 1069571) (by norm_num)
theorem B2139493 : Blo 1266451 2139493 := bbase (se 4 (by rfl) ⟨200577, by rfl⟩ : syracuseStep 2139493 = 401155) (by norm_num)
theorem B1901933 : Blo 1266451 1901933 := bbase (se 3 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 1901933 = 713225) (by norm_num)
theorem B1426801 : Blo 1266451 1426801 := bbase (se 2 (by rfl) ⟨535050, by rfl⟩ : syracuseStep 1426801 = 1070101) (by norm_num)
theorem B1803637 : Blo 1266451 1803637 := bbase (se 5 (by rfl) ⟨84545, by rfl⟩ : syracuseStep 1803637 = 169091) (by norm_num)
theorem B1901957 : Blo 1266451 1901957 := bbase (se 4 (by rfl) ⟨178308, by rfl⟩ : syracuseStep 1901957 = 356617) (by norm_num)
theorem B6088085 : Blo 1266451 6088085 := bbase (se 6 (by rfl) ⟨142689, by rfl⟩ : syracuseStep 6088085 = 285379) (by norm_num)
theorem B1426837 : Blo 1266451 1426837 := bbase (se 6 (by rfl) ⟨33441, by rfl⟩ : syracuseStep 1426837 = 66883) (by norm_num)
theorem B1901981 : Blo 1266451 1901981 := bbase (se 3 (by rfl) ⟨356621, by rfl⟩ : syracuseStep 1901981 = 713243) (by norm_num)
theorem B5137829 : Blo 1266451 5137829 := bbase (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) (by norm_num)
theorem B2852261 : Blo 1266451 2852261 := bbase (se 4 (by rfl) ⟨267399, by rfl⟩ : syracuseStep 2852261 = 534799) (by norm_num)
theorem B1902005 : Blo 1266451 1902005 := bbase (se 5 (by rfl) ⟨89156, by rfl⟩ : syracuseStep 1902005 = 178313) (by norm_num)
theorem B1426873 : Blo 1266451 1426873 := bbase (se 2 (by rfl) ⟨535077, by rfl⟩ : syracuseStep 1426873 = 1070155) (by norm_num)
theorem B2139581 : Blo 1266451 2139581 := bbase (se 3 (by rfl) ⟨401171, by rfl⟩ : syracuseStep 2139581 = 802343) (by norm_num)
theorem B4564421 : Blo 1266451 4564421 := bbase (se 4 (by rfl) ⟨427914, by rfl⟩ : syracuseStep 4564421 = 855829) (by norm_num)
theorem B1902029 : Blo 1266451 1902029 := bbase (se 3 (by rfl) ⟨356630, by rfl⟩ : syracuseStep 1902029 = 713261) (by norm_num)
theorem B4277717 : Blo 1266451 4277717 := bbase (se 7 (by rfl) ⟨50129, by rfl⟩ : syracuseStep 4277717 = 100259) (by norm_num)
theorem B1353181 : Blo 1266451 1353181 := bbase (se 3 (by rfl) ⟨253721, by rfl⟩ : syracuseStep 1353181 = 507443) (by norm_num)
theorem B1426909 : Blo 1266451 1426909 := bbase (se 3 (by rfl) ⟨267545, by rfl⟩ : syracuseStep 1426909 = 535091) (by norm_num)
theorem B1902053 : Blo 1266451 1902053 := bbase (se 4 (by rfl) ⟨178317, by rfl⟩ : syracuseStep 1902053 = 356635) (by norm_num)
theorem B2852333 : Blo 1266451 2852333 := bbase (se 3 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 2852333 = 1069625) (by norm_num)
theorem B1902077 : Blo 1266451 1902077 := bbase (se 3 (by rfl) ⟨356639, by rfl⟩ : syracuseStep 1902077 = 713279) (by norm_num)
theorem B1426945 : Blo 1266451 1426945 := bbase (se 2 (by rfl) ⟨535104, by rfl⟩ : syracuseStep 1426945 = 1070209) (by norm_num)
theorem B2704909 : Blo 1266451 2704909 := bbase (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) (by norm_num)
theorem B1902101 : Blo 1266451 1902101 := bbase (se 6 (by rfl) ⟨44580, by rfl⟩ : syracuseStep 1902101 = 89161) (by norm_num)
theorem B1426981 : Blo 1266451 1426981 := bbase (se 4 (by rfl) ⟨133779, by rfl⟩ : syracuseStep 1426981 = 267559) (by norm_num)
theorem B1902125 : Blo 1266451 1902125 := bbase (se 3 (by rfl) ⟨356648, by rfl⟩ : syracuseStep 1902125 = 713297) (by norm_num)
theorem B2852405 : Blo 1266451 2852405 := bbase (se 5 (by rfl) ⟨133706, by rfl⟩ : syracuseStep 2852405 = 267413) (by norm_num)
theorem B2139709 : Blo 1266451 2139709 := bbase (se 3 (by rfl) ⟨401195, by rfl⟩ : syracuseStep 2139709 = 802391) (by norm_num)
theorem B1902149 : Blo 1266451 1902149 := bbase (se 4 (by rfl) ⟨178326, by rfl⟩ : syracuseStep 1902149 = 356653) (by norm_num)
theorem B1353305 : Blo 1266451 1353305 := bbase (se 2 (by rfl) ⟨507489, by rfl⟩ : syracuseStep 1353305 = 1014979) (by norm_num)
theorem B1902173 : Blo 1266451 1902173 := bbase (se 3 (by rfl) ⟨356657, by rfl⟩ : syracuseStep 1902173 = 713315) (by norm_num)
theorem B1902197 : Blo 1266451 1902197 := bbase (se 5 (by rfl) ⟨89165, by rfl⟩ : syracuseStep 1902197 = 178331) (by norm_num)
theorem B2852477 : Blo 1266451 2852477 := bbase (se 3 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 2852477 = 1069679) (by norm_num)
theorem B5777029 : Blo 1266451 5777029 := bbase (se 4 (by rfl) ⟨541596, by rfl⟩ : syracuseStep 5777029 = 1083193) (by norm_num)
theorem B1902221 : Blo 1266451 1902221 := bbase (se 3 (by rfl) ⟨356666, by rfl⟩ : syracuseStep 1902221 = 713333) (by norm_num)
theorem B2139797 : Blo 1266451 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B1902245 : Blo 1266451 1902245 := bbase (se 4 (by rfl) ⟨178335, by rfl⟩ : syracuseStep 1902245 = 356671) (by norm_num)
theorem B1902269 : Blo 1266451 1902269 := bbase (se 3 (by rfl) ⟨356675, by rfl⟩ : syracuseStep 1902269 = 713351) (by norm_num)
theorem B2852549 : Blo 1266451 2852549 := bbase (se 4 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 2852549 = 534853) (by norm_num)
theorem B6850261 : Blo 1266451 6850261 := bbase (se 7 (by rfl) ⟨80276, by rfl⟩ : syracuseStep 6850261 = 160553) (by norm_num)
theorem B1902293 : Blo 1266451 1902293 := bbase (se 7 (by rfl) ⟨22292, by rfl⟩ : syracuseStep 1902293 = 44585) (by norm_num)
theorem B1902317 : Blo 1266451 1902317 := bbase (se 3 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 1902317 = 713369) (by norm_num)
theorem B1902341 : Blo 1266451 1902341 := bbase (se 4 (by rfl) ⟨178344, by rfl⟩ : syracuseStep 1902341 = 356689) (by norm_num)
theorem B2852621 : Blo 1266451 2852621 := bbase (se 3 (by rfl) ⟨534866, by rfl⟩ : syracuseStep 2852621 = 1069733) (by norm_num)
theorem B5777173 : Blo 1266451 5777173 := bbase (se 6 (by rfl) ⟨135402, by rfl⟩ : syracuseStep 5777173 = 270805) (by norm_num)
theorem B2139925 : Blo 1266451 2139925 := bbase (se 6 (by rfl) ⟨50154, by rfl⟩ : syracuseStep 2139925 = 100309) (by norm_num)
theorem B1902365 : Blo 1266451 1902365 := bbase (se 3 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 1902365 = 713387) (by norm_num)
theorem B4810549 : Blo 1266451 4810549 := bbase (se 5 (by rfl) ⟨225494, by rfl⟩ : syracuseStep 4810549 = 450989) (by norm_num)
theorem B1902389 : Blo 1266451 1902389 := bbase (se 5 (by rfl) ⟨89174, by rfl⟩ : syracuseStep 1902389 = 178349) (by norm_num)
theorem B1902413 : Blo 1266451 1902413 := bbase (se 3 (by rfl) ⟨356702, by rfl⟩ : syracuseStep 1902413 = 713405) (by norm_num)
theorem B1353557 : Blo 1266451 1353557 := bbase (se 9 (by rfl) ⟨3965, by rfl⟩ : syracuseStep 1353557 = 7931) (by norm_num)
theorem B2852693 : Blo 1266451 2852693 := bbase (se 9 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 2852693 = 16715) (by norm_num)
theorem B5416789 : Blo 1266451 5416789 := bbase (se 9 (by rfl) ⟨15869, by rfl⟩ : syracuseStep 5416789 = 31739) (by norm_num)
theorem B1804133 : Blo 1266451 1804133 := bbase (se 4 (by rfl) ⟨169137, by rfl⟩ : syracuseStep 1804133 = 338275) (by norm_num)
theorem B1902437 : Blo 1266451 1902437 := bbase (se 4 (by rfl) ⟨178353, by rfl⟩ : syracuseStep 1902437 = 356707) (by norm_num)
theorem B2140013 : Blo 1266451 2140013 := bbase (se 3 (by rfl) ⟨401252, by rfl⟩ : syracuseStep 2140013 = 802505) (by norm_num)
theorem B1902461 : Blo 1266451 1902461 := bbase (se 3 (by rfl) ⟨356711, by rfl⟩ : syracuseStep 1902461 = 713423) (by norm_num)
theorem B2705285 : Blo 1266451 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B4278149 : Blo 1266451 4278149 := bbase (se 4 (by rfl) ⟨401076, by rfl⟩ : syracuseStep 4278149 = 802153) (by norm_num)
theorem B1902485 : Blo 1266451 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B2852765 : Blo 1266451 2852765 := bbase (se 3 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 2852765 = 1069787) (by norm_num)
theorem B1902509 : Blo 1266451 1902509 := bbase (se 3 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 1902509 = 713441) (by norm_num)
theorem B1902533 : Blo 1266451 1902533 := bbase (se 4 (by rfl) ⟨178362, by rfl⟩ : syracuseStep 1902533 = 356725) (by norm_num)
theorem B1902557 : Blo 1266451 1902557 := bbase (se 3 (by rfl) ⟨356729, by rfl⟩ : syracuseStep 1902557 = 713459) (by norm_num)
theorem B2852837 : Blo 1266451 2852837 := bbase (se 4 (by rfl) ⟨267453, by rfl⟩ : syracuseStep 2852837 = 534907) (by norm_num)
theorem B2140141 : Blo 1266451 2140141 := bbase (se 3 (by rfl) ⟨401276, by rfl⟩ : syracuseStep 2140141 = 802553) (by norm_num)
theorem B1902581 : Blo 1266451 1902581 := bbase (se 5 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 1902581 = 178367) (by norm_num)
theorem B1902605 : Blo 1266451 1902605 := bbase (se 3 (by rfl) ⟨356738, by rfl⟩ : syracuseStep 1902605 = 713477) (by norm_num)
theorem B1902629 : Blo 1266451 1902629 := bbase (se 4 (by rfl) ⟨178371, by rfl⟩ : syracuseStep 1902629 = 356743) (by norm_num)
theorem B2852909 : Blo 1266451 2852909 := bbase (se 3 (by rfl) ⟨534920, by rfl⟩ : syracuseStep 2852909 = 1069841) (by norm_num)
theorem B1902653 : Blo 1266451 1902653 := bbase (se 3 (by rfl) ⟨356747, by rfl⟩ : syracuseStep 1902653 = 713495) (by norm_num)
theorem B2140229 : Blo 1266451 2140229 := bbase (se 4 (by rfl) ⟨200646, by rfl⟩ : syracuseStep 2140229 = 401293) (by norm_num)
theorem B1902677 : Blo 1266451 1902677 := bbase (se 8 (by rfl) ⟨11148, by rfl⟩ : syracuseStep 1902677 = 22297) (by norm_num)
theorem B4810853 : Blo 1266451 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B2852981 : Blo 1266451 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B5777573 : Blo 1266451 5777573 := bbase (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) (by norm_num)
theorem B2853053 : Blo 1266451 2853053 := bbase (se 3 (by rfl) ⟨534947, by rfl⟩ : syracuseStep 2853053 = 1069895) (by norm_num)
theorem B2140357 : Blo 1266451 2140357 := bbase (se 4 (by rfl) ⟨200658, by rfl⟩ : syracuseStep 2140357 = 401317) (by norm_num)
theorem B2705653 : Blo 1266451 2705653 := bbase (se 5 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 2705653 = 253655) (by norm_num)
theorem B8669429 : Blo 1266451 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B2853125 : Blo 1266451 2853125 := bbase (se 4 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 2853125 = 534961) (by norm_num)
theorem B1354001 : Blo 1266451 1354001 := bbase (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) (by norm_num)
theorem B2140445 : Blo 1266451 2140445 := bbase (se 3 (by rfl) ⟨401333, by rfl⟩ : syracuseStep 2140445 = 802667) (by norm_num)
theorem B1648945 : Blo 1266451 1648945 := bbase (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) (by norm_num)
theorem B4278581 : Blo 1266451 4278581 := bbase (se 5 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 4278581 = 401117) (by norm_num)
theorem B2853197 : Blo 1266451 2853197 := bbase (se 3 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 2853197 = 1069949) (by norm_num)
theorem B1804685 : Blo 1266451 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B2853269 : Blo 1266451 2853269 := bbase (se 6 (by rfl) ⟨66873, by rfl⟩ : syracuseStep 2853269 = 133747) (by norm_num)
theorem B5491109 : Blo 1266451 5491109 := bbase (se 4 (by rfl) ⟨514791, by rfl⟩ : syracuseStep 5491109 = 1029583) (by norm_num)
theorem B2853341 : Blo 1266451 2853341 := bbase (se 3 (by rfl) ⟨535001, by rfl⟩ : syracuseStep 2853341 = 1070003) (by norm_num)
theorem B1444321 : Blo 1266451 1444321 := bbase (se 2 (by rfl) ⟨541620, by rfl⟩ : syracuseStep 1444321 = 1083241) (by norm_num)
theorem B1354249 : Blo 1266451 1354249 := bbase (se 2 (by rfl) ⟨507843, by rfl⟩ : syracuseStep 1354249 = 1015687) (by norm_num)
theorem B2853413 : Blo 1266451 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B6416981 : Blo 1266451 6416981 := bbase (se 8 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 6416981 = 75199) (by norm_num)
theorem B2853485 : Blo 1266451 2853485 := bbase (se 3 (by rfl) ⟨535028, by rfl⟩ : syracuseStep 2853485 = 1070057) (by norm_num)
theorem B3205757 : Blo 1266451 3205757 := bbase (se 3 (by rfl) ⟨601079, by rfl⟩ : syracuseStep 3205757 = 1202159) (by norm_num)
theorem B2198197 : Blo 1266451 2198197 := bbase (se 5 (by rfl) ⟨103040, by rfl⟩ : syracuseStep 2198197 = 206081) (by norm_num)
theorem B2853557 : Blo 1266451 2853557 := bbase (se 5 (by rfl) ⟨133760, by rfl⟩ : syracuseStep 2853557 = 267521) (by norm_num)
theorem B7219925 : Blo 1266451 7219925 := bbase (se 7 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 7219925 = 169217) (by norm_num)
theorem B4279013 : Blo 1266451 4279013 := bbase (se 4 (by rfl) ⟨401157, by rfl⟩ : syracuseStep 4279013 = 802315) (by norm_num)
theorem B2853629 : Blo 1266451 2853629 := bbase (se 3 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 2853629 = 1070111) (by norm_num)
theorem B4057877 : Blo 1266451 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B16468757 : Blo 1266451 16468757 := bbase (se 6 (by rfl) ⟨385986, by rfl⟩ : syracuseStep 16468757 = 771973) (by norm_num)
theorem B1444649 : Blo 1266451 1444649 := bbase (se 2 (by rfl) ⟨541743, by rfl⟩ : syracuseStep 1444649 = 1083487) (by norm_num)
theorem B2853701 : Blo 1266451 2853701 := bbase (se 4 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 2853701 = 535069) (by norm_num)
theorem B2853773 : Blo 1266451 2853773 := bbase (se 3 (by rfl) ⟨535082, by rfl⟩ : syracuseStep 2853773 = 1070165) (by norm_num)
theorem B5483477 : Blo 1266451 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B3206101 : Blo 1266451 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B2853845 : Blo 1266451 2853845 := bbase (se 7 (by rfl) ⟨33443, by rfl⟩ : syracuseStep 2853845 = 66887) (by norm_num)
theorem B2853917 : Blo 1266451 2853917 := bbase (se 3 (by rfl) ⟨535109, by rfl⟩ : syracuseStep 2853917 = 1070219) (by norm_num)
theorem B3206213 : Blo 1266451 3206213 := bbase (se 4 (by rfl) ⟨300582, by rfl⟩ : syracuseStep 3206213 = 601165) (by norm_num)
theorem B2853989 : Blo 1266451 2853989 := bbase (se 4 (by rfl) ⟨267561, by rfl⟩ : syracuseStep 2853989 = 535123) (by norm_num)
theorem B1805437 : Blo 1266451 1805437 := bbase (se 3 (by rfl) ⟨338519, by rfl⟩ : syracuseStep 1805437 = 677039) (by norm_num)
theorem B3607685 : Blo 1266451 3607685 := bbase (se 4 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 3607685 = 676441) (by norm_num)
theorem B4566149 : Blo 1266451 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B4942997 : Blo 1266451 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B4279445 : Blo 1266451 4279445 := bbase (se 6 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 4279445 = 200599) (by norm_num)
theorem B3206405 : Blo 1266451 3206405 := bbase (se 4 (by rfl) ⟨300600, by rfl⟩ : syracuseStep 3206405 = 601201) (by norm_num)
theorem B2198869 : Blo 1266451 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B1371701 : Blo 1266451 1371701 := bbase (se 5 (by rfl) ⟨64298, by rfl⟩ : syracuseStep 1371701 = 128597) (by norm_num)
theorem B4279877 : Blo 1266451 4279877 := bbase (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) (by norm_num)
theorem B3206749 : Blo 1266451 3206749 := bbase (se 3 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 3206749 = 1202531) (by norm_num)
theorem B6950549 : Blo 1266451 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B3206861 : Blo 1266451 3206861 := bbase (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) (by norm_num)
theorem B2707157 : Blo 1266451 2707157 := bbase (se 7 (by rfl) ⟨31724, by rfl⟩ : syracuseStep 2707157 = 63449) (by norm_num)
theorem B2707301 : Blo 1266451 2707301 := bbase (se 4 (by rfl) ⟨253809, by rfl⟩ : syracuseStep 2707301 = 507619) (by norm_num)
theorem B6418277 : Blo 1266451 6418277 := bbase (se 4 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 6418277 = 1203427) (by norm_num)
theorem B4566901 : Blo 1266451 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B7221109 : Blo 1266451 7221109 := bbase (se 5 (by rfl) ⟨338489, by rfl⟩ : syracuseStep 7221109 = 676979) (by norm_num)
theorem B3207053 : Blo 1266451 3207053 := bbase (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) (by norm_num)
theorem B6500245 : Blo 1266451 6500245 := bbase (se 6 (by rfl) ⟨152349, by rfl⟩ : syracuseStep 6500245 = 304699) (by norm_num)
theorem B2404333 : Blo 1266451 2404333 := bbase (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) (by norm_num)
theorem B4280309 : Blo 1266451 4280309 := bbase (se 5 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 4280309 = 401279) (by norm_num)
theorem B10276949 : Blo 1266451 10276949 := bbase (se 8 (by rfl) ⟨60216, by rfl⟩ : syracuseStep 10276949 = 120433) (by norm_num)
theorem B4812965 : Blo 1266451 4812965 := bbase (se 4 (by rfl) ⟨451215, by rfl⟩ : syracuseStep 4812965 = 902431) (by norm_num)
theorem B2707661 : Blo 1266451 2707661 := bbase (se 3 (by rfl) ⟨507686, by rfl⟩ : syracuseStep 2707661 = 1015373) (by norm_num)
theorem B3207397 : Blo 1266451 3207397 := bbase (se 4 (by rfl) ⟨300693, by rfl⟩ : syracuseStep 3207397 = 601387) (by norm_num)
theorem B12521749 : Blo 1266451 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B2404637 : Blo 1266451 2404637 := bbase (se 3 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 2404637 = 901739) (by norm_num)
theorem B3608869 : Blo 1266451 3608869 := bbase (se 4 (by rfl) ⟨338331, by rfl⟩ : syracuseStep 3608869 = 676663) (by norm_num)
theorem B3207509 : Blo 1266451 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B4280741 : Blo 1266451 4280741 := bbase (se 4 (by rfl) ⟨401319, by rfl⟩ : syracuseStep 4280741 = 802639) (by norm_num)
theorem B11121077 : Blo 1266451 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B3609029 : Blo 1266451 3609029 := bbase (se 4 (by rfl) ⟨338346, by rfl⟩ : syracuseStep 3609029 = 676693) (by norm_num)
theorem B4813253 : Blo 1266451 4813253 := bbase (se 4 (by rfl) ⟨451242, by rfl⟩ : syracuseStep 4813253 = 902485) (by norm_num)
theorem B5485013 : Blo 1266451 5485013 := bbase (se 7 (by rfl) ⟨64277, by rfl⟩ : syracuseStep 5485013 = 128555) (by norm_num)
theorem B3207701 : Blo 1266451 3207701 := bbase (se 6 (by rfl) ⟨75180, by rfl⟩ : syracuseStep 3207701 = 150361) (by norm_num)
theorem B3609269 : Blo 1266451 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B4567909 : Blo 1266451 4567909 := bbase (se 4 (by rfl) ⟨428241, by rfl⟩ : syracuseStep 4567909 = 856483) (by norm_num)
theorem B3208045 : Blo 1266451 3208045 := bbase (se 3 (by rfl) ⟨601508, by rfl⟩ : syracuseStep 3208045 = 1203017) (by norm_num)
theorem B3609461 : Blo 1266451 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B3855221 : Blo 1266451 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B5411717 : Blo 1266451 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B3208157 : Blo 1266451 3208157 := bbase (se 3 (by rfl) ⟨601529, by rfl⟩ : syracuseStep 3208157 = 1203059) (by norm_num)
theorem B2405389 : Blo 1266451 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B2708549 : Blo 1266451 2708549 := bbase (se 4 (by rfl) ⟨253926, by rfl⟩ : syracuseStep 2708549 = 507853) (by norm_num)
theorem B6419573 : Blo 1266451 6419573 := bbase (se 5 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 6419573 = 601835) (by norm_num)
theorem B4338821 : Blo 1266451 4338821 := bbase (se 4 (by rfl) ⟨406764, by rfl⟩ : syracuseStep 4338821 = 813529) (by norm_num)
theorem B2405533 : Blo 1266451 2405533 := bbase (se 3 (by rfl) ⟨451037, by rfl⟩ : syracuseStep 2405533 = 902075) (by norm_num)
theorem B3208349 : Blo 1266451 3208349 := bbase (se 3 (by rfl) ⟨601565, by rfl⟩ : syracuseStep 3208349 = 1203131) (by norm_num)
theorem B5412005 : Blo 1266451 5412005 := bbase (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) (by norm_num)
theorem B2282701 : Blo 1266451 2282701 := bbase (se 3 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 2282701 = 856013) (by norm_num)
theorem B2405693 : Blo 1266451 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B2708797 : Blo 1266451 2708797 := bbase (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) (by norm_num)
theorem B9631061 : Blo 1266451 9631061 := bbase (se 13 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 9631061 = 3527) (by norm_num)
theorem B1602929 : Blo 1266451 1602929 := bbase (se 2 (by rfl) ⟨601098, by rfl⟩ : syracuseStep 1602929 = 1202197) (by norm_num)
theorem B2282917 : Blo 1266451 2282917 := bbase (se 4 (by rfl) ⟨214023, by rfl⟩ : syracuseStep 2282917 = 428047) (by norm_num)
theorem B1602985 : Blo 1266451 1602985 := bbase (se 2 (by rfl) ⟨601119, by rfl⟩ : syracuseStep 1602985 = 1202239) (by norm_num)
theorem B2405837 : Blo 1266451 2405837 := bbase (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) (by norm_num)
theorem B3208693 : Blo 1266451 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B1603081 : Blo 1266451 1603081 := bbase (se 2 (by rfl) ⟨601155, by rfl⟩ : syracuseStep 1603081 = 1202311) (by norm_num)
theorem B6411797 : Blo 1266451 6411797 := bbase (se 6 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 6411797 = 300553) (by norm_num)
theorem B3044965 : Blo 1266451 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B3208805 : Blo 1266451 3208805 := bbase (se 4 (by rfl) ⟨300825, by rfl⟩ : syracuseStep 3208805 = 601651) (by norm_num)
theorem B4814437 : Blo 1266451 4814437 := bbase (se 4 (by rfl) ⟨451353, by rfl⟩ : syracuseStep 4814437 = 902707) (by norm_num)
theorem B1603253 : Blo 1266451 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B1603309 : Blo 1266451 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B2406125 : Blo 1266451 2406125 := bbase (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) (by norm_num)
theorem B9623285 : Blo 1266451 9623285 := bbase (se 5 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 9623285 = 902183) (by norm_num)
theorem B2029349 : Blo 1266451 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B3208997 : Blo 1266451 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B7223093 : Blo 1266451 7223093 := bbase (se 5 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 7223093 = 677165) (by norm_num)
theorem B10835765 : Blo 1266451 10835765 := bbase (se 5 (by rfl) ⟨507926, by rfl⟩ : syracuseStep 10835765 = 1015853) (by norm_num)
theorem B1603405 : Blo 1266451 1603405 := bbase (se 3 (by rfl) ⟨300638, by rfl⟩ : syracuseStep 1603405 = 601277) (by norm_num)
theorem B3610453 : Blo 1266451 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B2406277 : Blo 1266451 2406277 := bbase (se 4 (by rfl) ⟨225588, by rfl⟩ : syracuseStep 2406277 = 451177) (by norm_num)
theorem B5412757 : Blo 1266451 5412757 := bbase (se 6 (by rfl) ⟨126861, by rfl⟩ : syracuseStep 5412757 = 253723) (by norm_num)
theorem B4814741 : Blo 1266451 4814741 := bbase (se 6 (by rfl) ⟨112845, by rfl⟩ : syracuseStep 4814741 = 225691) (by norm_num)
theorem B2029477 : Blo 1266451 2029477 := bbase (se 4 (by rfl) ⟨190263, by rfl⟩ : syracuseStep 2029477 = 380527) (by norm_num)
theorem B10827701 : Blo 1266451 10827701 := bbase (se 5 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 10827701 = 1015097) (by norm_num)
theorem B2742229 : Blo 1266451 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B3250133 : Blo 1266451 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B1603577 : Blo 1266451 1603577 := bbase (se 2 (by rfl) ⟨601341, by rfl⟩ : syracuseStep 1603577 = 1202683) (by norm_num)
theorem B2930717 : Blo 1266451 2930717 := bbase (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) (by norm_num)
theorem B1603633 : Blo 1266451 1603633 := bbase (se 2 (by rfl) ⟨601362, by rfl⟩ : syracuseStep 1603633 = 1202725) (by norm_num)
theorem B3209341 : Blo 1266451 3209341 := bbase (se 3 (by rfl) ⟨601751, by rfl⟩ : syracuseStep 3209341 = 1203503) (by norm_num)
theorem B1603729 : Blo 1266451 1603729 := bbase (se 2 (by rfl) ⟨601398, by rfl⟩ : syracuseStep 1603729 = 1202797) (by norm_num)
theorem B2406581 : Blo 1266451 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B3659957 : Blo 1266451 3659957 := bbase (se 5 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 3659957 = 343121) (by norm_num)
theorem B1521877 : Blo 1266451 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B3209453 : Blo 1266451 3209453 := bbase (se 3 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 3209453 = 1203545) (by norm_num)
theorem B3045637 : Blo 1266451 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B2029861 : Blo 1266451 2029861 := bbase (se 4 (by rfl) ⟨190299, by rfl⟩ : syracuseStep 2029861 = 380599) (by norm_num)
theorem B1521973 : Blo 1266451 1521973 := bbase (se 5 (by rfl) ⟨71342, by rfl⟩ : syracuseStep 1521973 = 142685) (by norm_num)
theorem B1603901 : Blo 1266451 1603901 := bbase (se 3 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 1603901 = 601463) (by norm_num)
theorem B1603957 : Blo 1266451 1603957 := bbase (se 5 (by rfl) ⟨75185, by rfl⟩ : syracuseStep 1603957 = 150371) (by norm_num)
theorem B6420869 : Blo 1266451 6420869 := bbase (se 4 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 6420869 = 1203913) (by norm_num)
theorem B3209645 : Blo 1266451 3209645 := bbase (se 3 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 3209645 = 1203617) (by norm_num)
theorem B1604053 : Blo 1266451 1604053 := bbase (se 7 (by rfl) ⟨18797, by rfl⟩ : syracuseStep 1604053 = 37595) (by norm_num)
theorem B2169301 : Blo 1266451 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B4061669 : Blo 1266451 4061669 := bbase (se 4 (by rfl) ⟨380781, by rfl⟩ : syracuseStep 4061669 = 761563) (by norm_num)
theorem B3045869 : Blo 1266451 3045869 := bbase (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) (by norm_num)
theorem B2931197 : Blo 1266451 2931197 := bbase (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) (by norm_num)
theorem B4274693 : Blo 1266451 4274693 := bbase (se 4 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 4274693 = 801505) (by norm_num)
theorem B2030117 : Blo 1266451 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B5413493 : Blo 1266451 5413493 := bbase (se 5 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 5413493 = 507515) (by norm_num)
theorem B3046013 : Blo 1266451 3046013 := bbase (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) (by norm_num)
theorem B1604225 : Blo 1266451 1604225 := bbase (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) (by norm_num)
theorem B3046061 : Blo 1266451 3046061 := bbase (se 3 (by rfl) ⟨571136, by rfl⟩ : syracuseStep 3046061 = 1142273) (by norm_num)
theorem B1522357 : Blo 1266451 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B1604281 : Blo 1266451 1604281 := bbase (se 2 (by rfl) ⟨601605, by rfl⟩ : syracuseStep 1604281 = 1203211) (by norm_num)
theorem B2849525 : Blo 1266451 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B4692725 : Blo 1266451 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B3209989 : Blo 1266451 3209989 := bbase (se 4 (by rfl) ⟨300936, by rfl⟩ : syracuseStep 3209989 = 601873) (by norm_num)
theorem B2284301 : Blo 1266451 2284301 := bbase (se 3 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 2284301 = 856613) (by norm_num)
theorem B9132821 : Blo 1266451 9132821 := bbase (se 6 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 9132821 = 428101) (by norm_num)
theorem B1604377 : Blo 1266451 1604377 := bbase (se 2 (by rfl) ⟨601641, by rfl⟩ : syracuseStep 1604377 = 1203283) (by norm_num)
theorem B6413093 : Blo 1266451 6413093 := bbase (se 4 (by rfl) ⟨601227, by rfl⟩ : syracuseStep 6413093 = 1202455) (by norm_num)
theorem B2849597 : Blo 1266451 2849597 := bbase (se 3 (by rfl) ⟨534299, by rfl⟩ : syracuseStep 2849597 = 1068599) (by norm_num)
theorem B7322453 : Blo 1266451 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B3210101 : Blo 1266451 3210101 := bbase (se 5 (by rfl) ⟨150473, by rfl⟩ : syracuseStep 3210101 = 300947) (by norm_num)
theorem B2849669 : Blo 1266451 2849669 := bbase (se 4 (by rfl) ⟨267156, by rfl⟩ : syracuseStep 2849669 = 534313) (by norm_num)
theorem B2284453 : Blo 1266451 2284453 := bbase (se 4 (by rfl) ⟨214167, by rfl⟩ : syracuseStep 2284453 = 428335) (by norm_num)
theorem B2407333 : Blo 1266451 2407333 := bbase (se 4 (by rfl) ⟨225687, by rfl⟩ : syracuseStep 2407333 = 451375) (by norm_num)
theorem B3611557 : Blo 1266451 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B3251117 : Blo 1266451 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B4275125 : Blo 1266451 4275125 := bbase (se 5 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 4275125 = 400793) (by norm_num)
theorem B8231861 : Blo 1266451 8231861 := bbase (se 5 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 8231861 = 771737) (by norm_num)
theorem B1604549 : Blo 1266451 1604549 := bbase (se 4 (by rfl) ⟨150426, by rfl⟩ : syracuseStep 1604549 = 300853) (by norm_num)
theorem B2849741 : Blo 1266451 2849741 := bbase (se 3 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 2849741 = 1068653) (by norm_num)
theorem B3046349 : Blo 1266451 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B2284517 : Blo 1266451 2284517 := bbase (se 4 (by rfl) ⟨214173, by rfl⟩ : syracuseStep 2284517 = 428347) (by norm_num)
theorem B12352501 : Blo 1266451 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B1604605 : Blo 1266451 1604605 := bbase (se 3 (by rfl) ⟨300863, by rfl⟩ : syracuseStep 1604605 = 601727) (by norm_num)
theorem B2849813 : Blo 1266451 2849813 := bbase (se 6 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 2849813 = 133585) (by norm_num)
theorem B5209109 : Blo 1266451 5209109 := bbase (se 6 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 5209109 = 244177) (by norm_num)
theorem B2407477 : Blo 1266451 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B3210293 : Blo 1266451 3210293 := bbase (se 5 (by rfl) ⟨150482, by rfl⟩ : syracuseStep 3210293 = 300965) (by norm_num)
theorem B15416405 : Blo 1266451 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B2849885 : Blo 1266451 2849885 := bbase (se 3 (by rfl) ⟨534353, by rfl⟩ : syracuseStep 2849885 = 1068707) (by norm_num)
theorem B1604701 : Blo 1266451 1604701 := bbase (se 3 (by rfl) ⟨300881, by rfl⟩ : syracuseStep 1604701 = 601763) (by norm_num)
theorem B2137205 : Blo 1266451 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B2284661 : Blo 1266451 2284661 := bbase (se 5 (by rfl) ⟨107093, by rfl⟩ : syracuseStep 2284661 = 214187) (by norm_num)
theorem B6855797 : Blo 1266451 6855797 := bbase (se 5 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 6855797 = 642731) (by norm_num)
theorem B1391737 : Blo 1266451 1391737 := bbase (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) (by norm_num)
theorem B1899677 : Blo 1266451 1899677 := bbase (se 3 (by rfl) ⟨356189, by rfl⟩ : syracuseStep 1899677 = 712379) (by norm_num)
theorem B2849957 : Blo 1266451 2849957 := bbase (se 4 (by rfl) ⟨267183, by rfl⟩ : syracuseStep 2849957 = 534367) (by norm_num)
theorem B1899701 : Blo 1266451 1899701 := bbase (se 5 (by rfl) ⟨89048, by rfl⟩ : syracuseStep 1899701 = 178097) (by norm_num)
theorem B1899725 : Blo 1266451 1899725 := bbase (se 3 (by rfl) ⟨356198, by rfl⟩ : syracuseStep 1899725 = 712397) (by norm_num)
theorem B2407637 : Blo 1266451 2407637 := bbase (se 7 (by rfl) ⟨28214, by rfl⟩ : syracuseStep 2407637 = 56429) (by norm_num)
theorem B1899749 : Blo 1266451 1899749 := bbase (se 4 (by rfl) ⟨178101, by rfl⟩ : syracuseStep 1899749 = 356203) (by norm_num)
theorem B2850029 : Blo 1266451 2850029 := bbase (se 3 (by rfl) ⟨534380, by rfl⟩ : syracuseStep 2850029 = 1068761) (by norm_num)
theorem B2137333 : Blo 1266451 2137333 := bbase (se 5 (by rfl) ⟨100187, by rfl⟩ : syracuseStep 2137333 = 200375) (by norm_num)
theorem B1899773 : Blo 1266451 1899773 := bbase (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) (by norm_num)
theorem B1604873 : Blo 1266451 1604873 := bbase (se 2 (by rfl) ⟨601827, by rfl⟩ : syracuseStep 1604873 = 1203655) (by norm_num)
theorem B1899797 : Blo 1266451 1899797 := bbase (se 6 (by rfl) ⟨44526, by rfl⟩ : syracuseStep 1899797 = 89053) (by norm_num)
theorem B1899821 : Blo 1266451 1899821 := bbase (se 3 (by rfl) ⟨356216, by rfl⟩ : syracuseStep 1899821 = 712433) (by norm_num)
theorem B2850101 : Blo 1266451 2850101 := bbase (se 5 (by rfl) ⟨133598, by rfl⟩ : syracuseStep 2850101 = 267197) (by norm_num)
theorem B1604929 : Blo 1266451 1604929 := bbase (se 2 (by rfl) ⟨601848, by rfl⟩ : syracuseStep 1604929 = 1203697) (by norm_num)
theorem B1899845 : Blo 1266451 1899845 := bbase (se 4 (by rfl) ⟨178110, by rfl⟩ : syracuseStep 1899845 = 356221) (by norm_num)
theorem B2137421 : Blo 1266451 2137421 := bbase (se 3 (by rfl) ⟨400766, by rfl⟩ : syracuseStep 2137421 = 801533) (by norm_num)
theorem B1899869 : Blo 1266451 1899869 := bbase (se 3 (by rfl) ⟨356225, by rfl⟩ : syracuseStep 1899869 = 712451) (by norm_num)
theorem B4275557 : Blo 1266451 4275557 := bbase (se 4 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 4275557 = 801667) (by norm_num)
theorem B2407781 : Blo 1266451 2407781 := bbase (se 4 (by rfl) ⟨225729, by rfl⟩ : syracuseStep 2407781 = 451459) (by norm_num)
theorem B1899893 : Blo 1266451 1899893 := bbase (se 5 (by rfl) ⟨89057, by rfl⟩ : syracuseStep 1899893 = 178115) (by norm_num)
theorem B4062581 : Blo 1266451 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B2850173 : Blo 1266451 2850173 := bbase (se 3 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 2850173 = 1068815) (by norm_num)
theorem B1899917 : Blo 1266451 1899917 := bbase (se 3 (by rfl) ⟨356234, by rfl⟩ : syracuseStep 1899917 = 712469) (by norm_num)
theorem B2030989 : Blo 1266451 2030989 := bbase (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) (by norm_num)
theorem B3210637 : Blo 1266451 3210637 := bbase (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) (by norm_num)
theorem B1424785 : Blo 1266451 1424785 := bbase (se 2 (by rfl) ⟨534294, by rfl⟩ : syracuseStep 1424785 = 1068589) (by norm_num)
theorem B1605025 : Blo 1266451 1605025 := bbase (se 2 (by rfl) ⟨601884, by rfl⟩ : syracuseStep 1605025 = 1203769) (by norm_num)
theorem B1899941 : Blo 1266451 1899941 := bbase (se 4 (by rfl) ⟨178119, by rfl⟩ : syracuseStep 1899941 = 356239) (by norm_num)
theorem B1424821 : Blo 1266451 1424821 := bbase (se 5 (by rfl) ⟨66788, by rfl⟩ : syracuseStep 1424821 = 133577) (by norm_num)
theorem B1899965 : Blo 1266451 1899965 := bbase (se 3 (by rfl) ⟨356243, by rfl⟩ : syracuseStep 1899965 = 712487) (by norm_num)
theorem B2850245 : Blo 1266451 2850245 := bbase (se 4 (by rfl) ⟨267210, by rfl⟩ : syracuseStep 2850245 = 534421) (by norm_num)
theorem B2137549 : Blo 1266451 2137549 := bbase (se 3 (by rfl) ⟨400790, by rfl⟩ : syracuseStep 2137549 = 801581) (by norm_num)
theorem B1899989 : Blo 1266451 1899989 := bbase (se 7 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 1899989 = 44531) (by norm_num)
theorem B1424857 : Blo 1266451 1424857 := bbase (se 2 (by rfl) ⟨534321, by rfl⟩ : syracuseStep 1424857 = 1068643) (by norm_num)
theorem B1900013 : Blo 1266451 1900013 := bbase (se 3 (by rfl) ⟨356252, by rfl⟩ : syracuseStep 1900013 = 712505) (by norm_num)
theorem B2031085 : Blo 1266451 2031085 := bbase (se 3 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 2031085 = 761657) (by norm_num)
theorem B1424893 : Blo 1266451 1424893 := bbase (se 3 (by rfl) ⟨267167, by rfl⟩ : syracuseStep 1424893 = 534335) (by norm_num)
theorem B3210749 : Blo 1266451 3210749 := bbase (se 3 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 3210749 = 1204031) (by norm_num)
theorem B1900037 : Blo 1266451 1900037 := bbase (se 4 (by rfl) ⟨178128, by rfl⟩ : syracuseStep 1900037 = 356257) (by norm_num)
theorem B2850317 : Blo 1266451 2850317 := bbase (se 3 (by rfl) ⟨534434, by rfl⟩ : syracuseStep 2850317 = 1068869) (by norm_num)
theorem B1900061 : Blo 1266451 1900061 := bbase (se 3 (by rfl) ⟨356261, by rfl⟩ : syracuseStep 1900061 = 712523) (by norm_num)
theorem B1424929 : Blo 1266451 1424929 := bbase (se 2 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 1424929 = 1068697) (by norm_num)
theorem B2137637 : Blo 1266451 2137637 := bbase (se 4 (by rfl) ⟨200403, by rfl⟩ : syracuseStep 2137637 = 400807) (by norm_num)
theorem B1900085 : Blo 1266451 1900085 := bbase (se 5 (by rfl) ⟨89066, by rfl⟩ : syracuseStep 1900085 = 178133) (by norm_num)
theorem B1424965 : Blo 1266451 1424965 := bbase (se 4 (by rfl) ⟨133590, by rfl⟩ : syracuseStep 1424965 = 267181) (by norm_num)
theorem B1900109 : Blo 1266451 1900109 := bbase (se 3 (by rfl) ⟨356270, by rfl⟩ : syracuseStep 1900109 = 712541) (by norm_num)
theorem B1605197 : Blo 1266451 1605197 := bbase (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) (by norm_num)
theorem B2850389 : Blo 1266451 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B18775637 : Blo 1266451 18775637 := bbase (se 8 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 18775637 = 220027) (by norm_num)
theorem B1900133 : Blo 1266451 1900133 := bbase (se 4 (by rfl) ⟨178137, by rfl⟩ : syracuseStep 1900133 = 356275) (by norm_num)
theorem B1425001 : Blo 1266451 1425001 := bbase (se 2 (by rfl) ⟨534375, by rfl⟩ : syracuseStep 1425001 = 1068751) (by norm_num)
theorem B1900157 : Blo 1266451 1900157 := bbase (se 3 (by rfl) ⟨356279, by rfl⟩ : syracuseStep 1900157 = 712559) (by norm_num)
theorem B1605253 : Blo 1266451 1605253 := bbase (se 4 (by rfl) ⟨150492, by rfl⟩ : syracuseStep 1605253 = 300985) (by norm_num)
theorem B2408069 : Blo 1266451 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B1425037 : Blo 1266451 1425037 := bbase (se 3 (by rfl) ⟨267194, by rfl⟩ : syracuseStep 1425037 = 534389) (by norm_num)
theorem B2031245 : Blo 1266451 2031245 := bbase (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) (by norm_num)
theorem B1900181 : Blo 1266451 1900181 := bbase (se 6 (by rfl) ⟨44535, by rfl⟩ : syracuseStep 1900181 = 89071) (by norm_num)
theorem B2850461 : Blo 1266451 2850461 := bbase (se 3 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 2850461 = 1068923) (by norm_num)
theorem B2137765 : Blo 1266451 2137765 := bbase (se 4 (by rfl) ⟨200415, by rfl⟩ : syracuseStep 2137765 = 400831) (by norm_num)
theorem B1900205 : Blo 1266451 1900205 := bbase (se 3 (by rfl) ⟨356288, by rfl⟩ : syracuseStep 1900205 = 712577) (by norm_num)
theorem B1425073 : Blo 1266451 1425073 := bbase (se 2 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 1425073 = 1068805) (by norm_num)
theorem B1900229 : Blo 1266451 1900229 := bbase (se 4 (by rfl) ⟨178146, by rfl⟩ : syracuseStep 1900229 = 356293) (by norm_num)
theorem B1523405 : Blo 1266451 1523405 := bbase (se 3 (by rfl) ⟨285638, by rfl⟩ : syracuseStep 1523405 = 571277) (by norm_num)
theorem B1425109 : Blo 1266451 1425109 := bbase (se 7 (by rfl) ⟨16700, by rfl⟩ : syracuseStep 1425109 = 33401) (by norm_num)
theorem B1900253 : Blo 1266451 1900253 := bbase (se 3 (by rfl) ⟨356297, by rfl⟩ : syracuseStep 1900253 = 712595) (by norm_num)
theorem B1564381 : Blo 1266451 1564381 := bbase (se 3 (by rfl) ⟨293321, by rfl⟩ : syracuseStep 1564381 = 586643) (by norm_num)
theorem B2850533 : Blo 1266451 2850533 := bbase (se 4 (by rfl) ⟨267237, by rfl⟩ : syracuseStep 2850533 = 534475) (by norm_num)
theorem B1605349 : Blo 1266451 1605349 := bbase (se 4 (by rfl) ⟨150501, by rfl⟩ : syracuseStep 1605349 = 301003) (by norm_num)
theorem B1900277 : Blo 1266451 1900277 := bbase (se 5 (by rfl) ⟨89075, by rfl⟩ : syracuseStep 1900277 = 178151) (by norm_num)
theorem B1425145 : Blo 1266451 1425145 := bbase (se 2 (by rfl) ⟨534429, by rfl⟩ : syracuseStep 1425145 = 1068859) (by norm_num)
theorem B2137853 : Blo 1266451 2137853 := bbase (se 3 (by rfl) ⟨400847, by rfl⟩ : syracuseStep 2137853 = 801695) (by norm_num)
theorem B1900301 : Blo 1266451 1900301 := bbase (se 3 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 1900301 = 712613) (by norm_num)
theorem B4275989 : Blo 1266451 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B1425181 : Blo 1266451 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B1900325 : Blo 1266451 1900325 := bbase (se 4 (by rfl) ⟨178155, by rfl⟩ : syracuseStep 1900325 = 356311) (by norm_num)
theorem B2850605 : Blo 1266451 2850605 := bbase (se 3 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 2850605 = 1068977) (by norm_num)
theorem B1900349 : Blo 1266451 1900349 := bbase (se 3 (by rfl) ⟨356315, by rfl⟩ : syracuseStep 1900349 = 712631) (by norm_num)
theorem B1425217 : Blo 1266451 1425217 := bbase (se 2 (by rfl) ⟨534456, by rfl⟩ : syracuseStep 1425217 = 1068913) (by norm_num)
theorem B1900373 : Blo 1266451 1900373 := bbase (se 9 (by rfl) ⟨5567, by rfl⟩ : syracuseStep 1900373 = 11135) (by norm_num)
theorem B1425253 : Blo 1266451 1425253 := bbase (se 4 (by rfl) ⟨133617, by rfl⟩ : syracuseStep 1425253 = 267235) (by norm_num)
theorem B1900397 : Blo 1266451 1900397 := bbase (se 3 (by rfl) ⟨356324, by rfl⟩ : syracuseStep 1900397 = 712649) (by norm_num)
theorem B2850677 : Blo 1266451 2850677 := bbase (se 5 (by rfl) ⟨133625, by rfl⟩ : syracuseStep 2850677 = 267251) (by norm_num)
theorem B2137981 : Blo 1266451 2137981 := bbase (se 3 (by rfl) ⟨400871, by rfl⟩ : syracuseStep 2137981 = 801743) (by norm_num)
theorem B1900421 : Blo 1266451 1900421 := bbase (se 4 (by rfl) ⟨178164, by rfl⟩ : syracuseStep 1900421 = 356329) (by norm_num)
theorem B1425289 : Blo 1266451 1425289 := bbase (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) (by norm_num)
theorem B13705109 : Blo 1266451 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B1900445 : Blo 1266451 1900445 := bbase (se 3 (by rfl) ⟨356333, by rfl⟩ : syracuseStep 1900445 = 712667) (by norm_num)
theorem B1425325 : Blo 1266451 1425325 := bbase (se 3 (by rfl) ⟨267248, by rfl⟩ : syracuseStep 1425325 = 534497) (by norm_num)
theorem B1900469 : Blo 1266451 1900469 := bbase (se 5 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 1900469 = 178169) (by norm_num)
theorem B2850749 : Blo 1266451 2850749 := bbase (se 3 (by rfl) ⟨534515, by rfl⟩ : syracuseStep 2850749 = 1069031) (by norm_num)
theorem B1900493 : Blo 1266451 1900493 := bbase (se 3 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 1900493 = 712685) (by norm_num)
theorem B1425361 : Blo 1266451 1425361 := bbase (se 2 (by rfl) ⟨534510, by rfl⟩ : syracuseStep 1425361 = 1069021) (by norm_num)
theorem B2138069 : Blo 1266451 2138069 := bbase (se 7 (by rfl) ⟨25055, by rfl⟩ : syracuseStep 2138069 = 50111) (by norm_num)
theorem B1712101 : Blo 1266451 1712101 := bbase (se 4 (by rfl) ⟨160509, by rfl⟩ : syracuseStep 1712101 = 321019) (by norm_num)
theorem B1900517 : Blo 1266451 1900517 := bbase (se 4 (by rfl) ⟨178173, by rfl⟩ : syracuseStep 1900517 = 356347) (by norm_num)
theorem B1425397 : Blo 1266451 1425397 := bbase (se 5 (by rfl) ⟨66815, by rfl⟩ : syracuseStep 1425397 = 133631) (by norm_num)
theorem B2744309 : Blo 1266451 2744309 := bbase (se 5 (by rfl) ⟨128639, by rfl⟩ : syracuseStep 2744309 = 257279) (by norm_num)
theorem B1900541 : Blo 1266451 1900541 := bbase (se 3 (by rfl) ⟨356351, by rfl⟩ : syracuseStep 1900541 = 712703) (by norm_num)
theorem B2031617 : Blo 1266451 2031617 := bstep (se 2 (by rfl) ⟨761856, by rfl⟩ : syracuseStep 2031617 = 1523713) B1523713
theorem B1900547 : Blo 1266451 1900547 := bstep (se 1 (by rfl) ⟨1425410, by rfl⟩ : syracuseStep 1900547 = 2850821) B2850821
theorem B1900577 : Blo 1266451 1900577 := bstep (se 2 (by rfl) ⟨712716, by rfl⟩ : syracuseStep 1900577 = 1425433) B1425433
theorem B4276259 : Blo 1266451 4276259 := bstep (se 1 (by rfl) ⟨3207194, by rfl⟩ : syracuseStep 4276259 = 6414389) B6414389
theorem B1900595 : Blo 1266451 1900595 := bstep (se 1 (by rfl) ⟨1425446, by rfl⟩ : syracuseStep 1900595 = 2850893) B2850893
theorem B2138177 : Blo 1266451 2138177 := bstep (se 2 (by rfl) ⟨801816, by rfl⟩ : syracuseStep 2138177 = 1603633) B1603633
theorem B1900625 : Blo 1266451 1900625 := bstep (se 2 (by rfl) ⟨712734, by rfl⟩ : syracuseStep 1900625 = 1425469) B1425469
theorem B1900643 : Blo 1266451 1900643 := bstep (se 1 (by rfl) ⟨1425482, by rfl⟩ : syracuseStep 1900643 = 2850965) B2850965
theorem B2850929 : Blo 1266451 2850929 := bstep (se 2 (by rfl) ⟨1069098, by rfl⟩ : syracuseStep 2850929 = 2138197) B2138197
theorem B1425523 : Blo 1266451 1425523 := bstep (se 1 (by rfl) ⟨1069142, by rfl⟩ : syracuseStep 1425523 = 2138285) B2138285
theorem B1900673 : Blo 1266451 1900673 := bstep (se 2 (by rfl) ⟨712752, by rfl⟩ : syracuseStep 1900673 = 1425505) B1425505
theorem B2850947 : Blo 1266451 2850947 := bstep (se 1 (by rfl) ⟨2138210, by rfl⟩ : syracuseStep 2850947 = 4276421) B4276421
theorem B1900691 : Blo 1266451 1900691 := bstep (se 1 (by rfl) ⟨1425518, by rfl⟩ : syracuseStep 1900691 = 2851037) B2851037
theorem B1900721 : Blo 1266451 1900721 := bstep (se 2 (by rfl) ⟨712770, by rfl⟩ : syracuseStep 1900721 = 1425541) B1425541
theorem B2138305 : Blo 1266451 2138305 := bstep (se 2 (by rfl) ⟨801864, by rfl⟩ : syracuseStep 2138305 = 1603729) B1603729
theorem B1900739 : Blo 1266451 1900739 := bstep (se 1 (by rfl) ⟨1425554, by rfl⟩ : syracuseStep 1900739 = 2851109) B2851109
theorem B19792069 : Blo 1266451 19792069 := bstep (se 4 (by rfl) ⟨1855506, by rfl⟩ : syracuseStep 19792069 = 3711013) B3711013
theorem B4808909 : Blo 1266451 4808909 := bstep (se 3 (by rfl) ⟨901670, by rfl⟩ : syracuseStep 4808909 = 1803341) B1803341
theorem B8675533 : Blo 1266451 8675533 := bstep (se 3 (by rfl) ⟨1626662, by rfl⟩ : syracuseStep 8675533 = 3253325) B3253325
theorem B1900769 : Blo 1266451 1900769 := bstep (se 2 (by rfl) ⟨712788, by rfl⟩ : syracuseStep 1900769 = 1425577) B1425577
theorem B2138339 : Blo 1266451 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B1900787 : Blo 1266451 1900787 := bstep (se 1 (by rfl) ⟨1425590, by rfl⟩ : syracuseStep 1900787 = 2851181) B2851181
theorem B1425667 : Blo 1266451 1425667 := bstep (se 1 (by rfl) ⟨1069250, by rfl⟩ : syracuseStep 1425667 = 2138501) B2138501
theorem B1900817 : Blo 1266451 1900817 := bstep (se 2 (by rfl) ⟨712806, by rfl⟩ : syracuseStep 1900817 = 1425613) B1425613
theorem B7414051 : Blo 1266451 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B1900835 : Blo 1266451 1900835 := bstep (se 1 (by rfl) ⟨1425626, by rfl⟩ : syracuseStep 1900835 = 2851253) B2851253
theorem B4276529 : Blo 1266451 4276529 := bstep (se 2 (by rfl) ⟨1603698, by rfl⟩ : syracuseStep 4276529 = 3207397) B3207397
theorem B16253237 : Blo 1266451 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B1900865 : Blo 1266451 1900865 := bstep (se 2 (by rfl) ⟨712824, by rfl⟩ : syracuseStep 1900865 = 1425649) B1425649
theorem B1900883 : Blo 1266451 1900883 := bstep (se 1 (by rfl) ⟨1425662, by rfl⟩ : syracuseStep 1900883 = 2851325) B2851325
theorem B2138467 : Blo 1266451 2138467 := bstep (se 1 (by rfl) ⟨1603850, by rfl⟩ : syracuseStep 2138467 = 3207701) B3207701
theorem B1900913 : Blo 1266451 1900913 := bstep (se 2 (by rfl) ⟨712842, by rfl⟩ : syracuseStep 1900913 = 1425685) B1425685
theorem B16695665 : Blo 1266451 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B1900931 : Blo 1266451 1900931 := bstep (se 1 (by rfl) ⟨1425698, by rfl⟩ : syracuseStep 1900931 = 2851397) B2851397
theorem B2851217 : Blo 1266451 2851217 := bstep (se 2 (by rfl) ⟨1069206, by rfl⟩ : syracuseStep 2851217 = 2138413) B2138413
theorem B1425811 : Blo 1266451 1425811 := bstep (se 1 (by rfl) ⟨1069358, by rfl⟩ : syracuseStep 1425811 = 2138717) B2138717
theorem B1900961 : Blo 1266451 1900961 := bstep (se 2 (by rfl) ⟨712860, by rfl⟩ : syracuseStep 1900961 = 1425721) B1425721
theorem B2851235 : Blo 1266451 2851235 := bstep (se 1 (by rfl) ⟨2138426, by rfl⟩ : syracuseStep 2851235 = 4276853) B4276853
theorem B1900979 : Blo 1266451 1900979 := bstep (se 1 (by rfl) ⟨1425734, by rfl⟩ : syracuseStep 1900979 = 2851469) B2851469
theorem B1901009 : Blo 1266451 1901009 := bstep (se 2 (by rfl) ⟨712878, by rfl⟩ : syracuseStep 1901009 = 1425757) B1425757
theorem B1901027 : Blo 1266451 1901027 := bstep (se 1 (by rfl) ⟨1425770, by rfl⟩ : syracuseStep 1901027 = 2851541) B2851541
theorem B2138609 : Blo 1266451 2138609 := bstep (se 2 (by rfl) ⟨801978, by rfl⟩ : syracuseStep 2138609 = 1603957) B1603957
theorem B1901057 : Blo 1266451 1901057 := bstep (se 2 (by rfl) ⟨712896, by rfl⟩ : syracuseStep 1901057 = 1425793) B1425793
theorem B1901075 : Blo 1266451 1901075 := bstep (se 1 (by rfl) ⟨1425806, by rfl⟩ : syracuseStep 1901075 = 2851613) B2851613
theorem B1425955 : Blo 1266451 1425955 := bstep (se 1 (by rfl) ⟨1069466, by rfl⟩ : syracuseStep 1425955 = 2138933) B2138933
theorem B1901105 : Blo 1266451 1901105 := bstep (se 2 (by rfl) ⟨712914, by rfl⟩ : syracuseStep 1901105 = 1425829) B1425829
theorem B1901123 : Blo 1266451 1901123 := bstep (se 1 (by rfl) ⟨1425842, by rfl⟩ : syracuseStep 1901123 = 2851685) B2851685
theorem B1901153 : Blo 1266451 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B2138737 : Blo 1266451 2138737 := bstep (se 2 (by rfl) ⟨802026, by rfl⟩ : syracuseStep 2138737 = 1604053) B1604053
theorem B2892401 : Blo 1266451 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B1901171 : Blo 1266451 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B1925761 : Blo 1266451 1925761 := bstep (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) B1444321
theorem B1901201 : Blo 1266451 1901201 := bstep (se 2 (by rfl) ⟨712950, by rfl⟩ : syracuseStep 1901201 = 1425901) B1425901
theorem B2138771 : Blo 1266451 2138771 := bstep (se 1 (by rfl) ⟨1604078, by rfl⟩ : syracuseStep 2138771 = 3208157) B3208157
theorem B1901219 : Blo 1266451 1901219 := bstep (se 1 (by rfl) ⟨1425914, by rfl⟩ : syracuseStep 1901219 = 2851829) B2851829
theorem B2851505 : Blo 1266451 2851505 := bstep (se 2 (by rfl) ⟨1069314, by rfl⟩ : syracuseStep 2851505 = 2138629) B2138629
theorem B1426099 : Blo 1266451 1426099 := bstep (se 1 (by rfl) ⟨1069574, by rfl⟩ : syracuseStep 1426099 = 2139149) B2139149
theorem B1901249 : Blo 1266451 1901249 := bstep (se 2 (by rfl) ⟨712968, by rfl⟩ : syracuseStep 1901249 = 1425937) B1425937
theorem B2851523 : Blo 1266451 2851523 := bstep (se 1 (by rfl) ⟨2138642, by rfl⟩ : syracuseStep 2851523 = 4277285) B4277285
theorem B1901267 : Blo 1266451 1901267 := bstep (se 1 (by rfl) ⟨1425950, by rfl⟩ : syracuseStep 1901267 = 2851901) B2851901
theorem B1901297 : Blo 1266451 1901297 := bstep (se 2 (by rfl) ⟨712986, by rfl⟩ : syracuseStep 1901297 = 1425973) B1425973
theorem B1901315 : Blo 1266451 1901315 := bstep (se 1 (by rfl) ⟨1425986, by rfl⟩ : syracuseStep 1901315 = 2851973) B2851973
theorem B2892547 : Blo 1266451 2892547 := bstep (se 1 (by rfl) ⟨2169410, by rfl⟩ : syracuseStep 2892547 = 4338821) B4338821
theorem B2138899 : Blo 1266451 2138899 := bstep (se 1 (by rfl) ⟨1604174, by rfl⟩ : syracuseStep 2138899 = 3208349) B3208349
theorem B1901345 : Blo 1266451 1901345 := bstep (se 2 (by rfl) ⟨713004, by rfl⟩ : syracuseStep 1901345 = 1426009) B1426009
theorem B1901363 : Blo 1266451 1901363 := bstep (se 1 (by rfl) ⟨1426022, by rfl⟩ : syracuseStep 1901363 = 2852045) B2852045
theorem B1426243 : Blo 1266451 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B4277069 : Blo 1266451 4277069 := bstep (se 3 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 4277069 = 1603901) B1603901
theorem B1901393 : Blo 1266451 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B1901411 : Blo 1266451 1901411 := bstep (se 1 (by rfl) ⟨1426058, by rfl⟩ : syracuseStep 1901411 = 2852117) B2852117
theorem B1901441 : Blo 1266451 1901441 := bstep (se 2 (by rfl) ⟨713040, by rfl⟩ : syracuseStep 1901441 = 1426081) B1426081
theorem B4277123 : Blo 1266451 4277123 := bstep (se 1 (by rfl) ⟨3207842, by rfl⟩ : syracuseStep 4277123 = 6415685) B6415685
theorem B1901459 : Blo 1266451 1901459 := bstep (se 1 (by rfl) ⟨1426094, by rfl⟩ : syracuseStep 1901459 = 2852189) B2852189
theorem B2139041 : Blo 1266451 2139041 := bstep (se 2 (by rfl) ⟨802140, by rfl⟩ : syracuseStep 2139041 = 1604281) B1604281
theorem B1901489 : Blo 1266451 1901489 := bstep (se 2 (by rfl) ⟨713058, by rfl⟩ : syracuseStep 1901489 = 1426117) B1426117
theorem B3425219 : Blo 1266451 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B1901507 : Blo 1266451 1901507 := bstep (se 1 (by rfl) ⟨1426130, by rfl⟩ : syracuseStep 1901507 = 2852261) B2852261
theorem B11723717 : Blo 1266451 11723717 := bstep (se 4 (by rfl) ⟨1099098, by rfl⟩ : syracuseStep 11723717 = 2198197) B2198197
theorem B2851793 : Blo 1266451 2851793 := bstep (se 2 (by rfl) ⟨1069422, by rfl⟩ : syracuseStep 2851793 = 2138845) B2138845
theorem B1426387 : Blo 1266451 1426387 := bstep (se 1 (by rfl) ⟨1069790, by rfl⟩ : syracuseStep 1426387 = 2139581) B2139581
theorem B1901537 : Blo 1266451 1901537 := bstep (se 2 (by rfl) ⟨713076, by rfl⟩ : syracuseStep 1901537 = 1426153) B1426153
theorem B2851811 : Blo 1266451 2851811 := bstep (se 1 (by rfl) ⟨2138858, by rfl⟩ : syracuseStep 2851811 = 4277717) B4277717
theorem B1901555 : Blo 1266451 1901555 := bstep (se 1 (by rfl) ⟨1426166, by rfl⟩ : syracuseStep 1901555 = 2852333) B2852333
theorem B1901585 : Blo 1266451 1901585 := bstep (se 2 (by rfl) ⟨713094, by rfl⟩ : syracuseStep 1901585 = 1426189) B1426189
theorem B2139169 : Blo 1266451 2139169 := bstep (se 2 (by rfl) ⟨802188, by rfl⟩ : syracuseStep 2139169 = 1604377) B1604377
theorem B1901603 : Blo 1266451 1901603 := bstep (se 1 (by rfl) ⟨1426202, by rfl⟩ : syracuseStep 1901603 = 2852405) B2852405
theorem B1803313 : Blo 1266451 1803313 := bstep (se 2 (by rfl) ⟨676242, by rfl⟩ : syracuseStep 1803313 = 1352485) B1352485
theorem B1901633 : Blo 1266451 1901633 := bstep (se 2 (by rfl) ⟨713112, by rfl⟩ : syracuseStep 1901633 = 1426225) B1426225
theorem B2139203 : Blo 1266451 2139203 := bstep (se 1 (by rfl) ⟨1604402, by rfl⟩ : syracuseStep 2139203 = 3208805) B3208805
theorem B1901651 : Blo 1266451 1901651 := bstep (se 1 (by rfl) ⟨1426238, by rfl⟩ : syracuseStep 1901651 = 2852477) B2852477
theorem B1426531 : Blo 1266451 1426531 := bstep (se 1 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 1426531 = 2139797) B2139797
theorem B1901681 : Blo 1266451 1901681 := bstep (se 2 (by rfl) ⟨713130, by rfl⟩ : syracuseStep 1901681 = 1426261) B1426261
theorem B1901699 : Blo 1266451 1901699 := bstep (se 1 (by rfl) ⟨1426274, by rfl⟩ : syracuseStep 1901699 = 2852549) B2852549
theorem B4277393 : Blo 1266451 4277393 := bstep (se 2 (by rfl) ⟨1604022, by rfl⟩ : syracuseStep 4277393 = 3208045) B3208045
theorem B1901729 : Blo 1266451 1901729 := bstep (se 2 (by rfl) ⟨713148, by rfl⟩ : syracuseStep 1901729 = 1426297) B1426297
theorem B6415523 : Blo 1266451 6415523 := bstep (se 1 (by rfl) ⟨4811642, by rfl⟩ : syracuseStep 6415523 = 9623285) B9623285
theorem B1901747 : Blo 1266451 1901747 := bstep (se 1 (by rfl) ⟨1426310, by rfl⟩ : syracuseStep 1901747 = 2852621) B2852621
theorem B1352899 : Blo 1266451 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B2139331 : Blo 1266451 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B1901777 : Blo 1266451 1901777 := bstep (se 2 (by rfl) ⟨713166, by rfl⟩ : syracuseStep 1901777 = 1426333) B1426333
theorem B1901795 : Blo 1266451 1901795 := bstep (se 1 (by rfl) ⟨1426346, by rfl⟩ : syracuseStep 1901795 = 2852693) B2852693
theorem B2852081 : Blo 1266451 2852081 := bstep (se 2 (by rfl) ⟨1069530, by rfl⟩ : syracuseStep 2852081 = 2139061) B2139061
theorem B1426675 : Blo 1266451 1426675 := bstep (se 1 (by rfl) ⟨1070006, by rfl⟩ : syracuseStep 1426675 = 2140013) B2140013
theorem B1901825 : Blo 1266451 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B2852099 : Blo 1266451 2852099 := bstep (se 1 (by rfl) ⟨2139074, by rfl⟩ : syracuseStep 2852099 = 4278149) B4278149
theorem B10831117 : Blo 1266451 10831117 := bstep (se 3 (by rfl) ⟨2030834, by rfl⟩ : syracuseStep 10831117 = 4061669) B4061669
theorem B1901843 : Blo 1266451 1901843 := bstep (se 1 (by rfl) ⟨1426382, by rfl⟩ : syracuseStep 1901843 = 2852765) B2852765
theorem B7218467 : Blo 1266451 7218467 := bstep (se 1 (by rfl) ⟨5413850, by rfl⟩ : syracuseStep 7218467 = 10827701) B10827701
theorem B1901873 : Blo 1266451 1901873 := bstep (se 2 (by rfl) ⟨713202, by rfl⟩ : syracuseStep 1901873 = 1426405) B1426405
theorem B1901891 : Blo 1266451 1901891 := bstep (se 1 (by rfl) ⟨1426418, by rfl⟩ : syracuseStep 1901891 = 2852837) B2852837
theorem B2139473 : Blo 1266451 2139473 := bstep (se 2 (by rfl) ⟨802302, by rfl⟩ : syracuseStep 2139473 = 1604605) B1604605
theorem B1901921 : Blo 1266451 1901921 := bstep (se 2 (by rfl) ⟨713220, by rfl⟩ : syracuseStep 1901921 = 1426441) B1426441
theorem B1901939 : Blo 1266451 1901939 := bstep (se 1 (by rfl) ⟨1426454, by rfl⟩ : syracuseStep 1901939 = 2852909) B2852909
theorem B1803649 : Blo 1266451 1803649 := bstep (se 2 (by rfl) ⟨676368, by rfl⟩ : syracuseStep 1803649 = 1352737) B1352737
theorem B1426819 : Blo 1266451 1426819 := bstep (se 1 (by rfl) ⟨1070114, by rfl⟩ : syracuseStep 1426819 = 2140229) B2140229
theorem B1901969 : Blo 1266451 1901969 := bstep (se 2 (by rfl) ⟨713238, by rfl⟩ : syracuseStep 1901969 = 1426477) B1426477
theorem B1901987 : Blo 1266451 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B1902017 : Blo 1266451 1902017 := bstep (se 2 (by rfl) ⟨713256, by rfl⟩ : syracuseStep 1902017 = 1426513) B1426513
theorem B2139601 : Blo 1266451 2139601 := bstep (se 2 (by rfl) ⟨802350, by rfl⟩ : syracuseStep 2139601 = 1604701) B1604701
theorem B1902035 : Blo 1266451 1902035 := bstep (se 1 (by rfl) ⟨1426526, by rfl⟩ : syracuseStep 1902035 = 2853053) B2853053
theorem B1902065 : Blo 1266451 1902065 := bstep (se 2 (by rfl) ⟨713274, by rfl⟩ : syracuseStep 1902065 = 1426549) B1426549
theorem B2139635 : Blo 1266451 2139635 := bstep (se 1 (by rfl) ⟨1604726, by rfl⟩ : syracuseStep 2139635 = 3209453) B3209453
theorem B1902083 : Blo 1266451 1902083 := bstep (se 1 (by rfl) ⟨1426562, by rfl⟩ : syracuseStep 1902083 = 2853125) B2853125
theorem B2852369 : Blo 1266451 2852369 := bstep (se 2 (by rfl) ⟨1069638, by rfl⟩ : syracuseStep 2852369 = 2139277) B2139277
theorem B1426963 : Blo 1266451 1426963 := bstep (se 1 (by rfl) ⟨1070222, by rfl⟩ : syracuseStep 1426963 = 2140445) B2140445
theorem B1902113 : Blo 1266451 1902113 := bstep (se 2 (by rfl) ⟨713292, by rfl⟩ : syracuseStep 1902113 = 1426585) B1426585
theorem B2852387 : Blo 1266451 2852387 := bstep (se 1 (by rfl) ⟨2139290, by rfl⟩ : syracuseStep 2852387 = 4278581) B4278581
theorem B1902131 : Blo 1266451 1902131 := bstep (se 1 (by rfl) ⟨1426598, by rfl⟩ : syracuseStep 1902131 = 2853197) B2853197
theorem B1902161 : Blo 1266451 1902161 := bstep (se 2 (by rfl) ⟨713310, by rfl⟩ : syracuseStep 1902161 = 1426621) B1426621
theorem B1902179 : Blo 1266451 1902179 := bstep (se 1 (by rfl) ⟨1426634, by rfl⟩ : syracuseStep 1902179 = 2853269) B2853269
theorem B2139763 : Blo 1266451 2139763 := bstep (se 1 (by rfl) ⟨1604822, by rfl⟩ : syracuseStep 2139763 = 3209645) B3209645
theorem B1902209 : Blo 1266451 1902209 := bstep (se 2 (by rfl) ⟨713328, by rfl⟩ : syracuseStep 1902209 = 1426657) B1426657
theorem B1902227 : Blo 1266451 1902227 := bstep (se 1 (by rfl) ⟨1426670, by rfl⟩ : syracuseStep 1902227 = 2853341) B2853341
theorem B4277933 : Blo 1266451 4277933 := bstep (se 3 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 4277933 = 1604225) B1604225
theorem B1902257 : Blo 1266451 1902257 := bstep (se 2 (by rfl) ⟨713346, by rfl⟩ : syracuseStep 1902257 = 1426693) B1426693
theorem B1902275 : Blo 1266451 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B1902305 : Blo 1266451 1902305 := bstep (se 2 (by rfl) ⟨713364, by rfl⟩ : syracuseStep 1902305 = 1426729) B1426729
theorem B4277987 : Blo 1266451 4277987 := bstep (se 1 (by rfl) ⟨3208490, by rfl⟩ : syracuseStep 4277987 = 6416981) B6416981
theorem B1902323 : Blo 1266451 1902323 := bstep (se 1 (by rfl) ⟨1426742, by rfl⟩ : syracuseStep 1902323 = 2853485) B2853485
theorem B2139905 : Blo 1266451 2139905 := bstep (se 2 (by rfl) ⟨802464, by rfl⟩ : syracuseStep 2139905 = 1604929) B1604929
theorem B1902353 : Blo 1266451 1902353 := bstep (se 2 (by rfl) ⟨713382, by rfl⟩ : syracuseStep 1902353 = 1426765) B1426765
theorem B46909205 : Blo 1266451 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B1902371 : Blo 1266451 1902371 := bstep (se 1 (by rfl) ⟨1426778, by rfl⟩ : syracuseStep 1902371 = 2853557) B2853557
theorem B2852657 : Blo 1266451 2852657 := bstep (se 2 (by rfl) ⟨1069746, by rfl⟩ : syracuseStep 2852657 = 2139493) B2139493
theorem B1902401 : Blo 1266451 1902401 := bstep (se 2 (by rfl) ⟨713400, by rfl⟩ : syracuseStep 1902401 = 1426801) B1426801
theorem B2852675 : Blo 1266451 2852675 := bstep (se 1 (by rfl) ⟨2139506, by rfl⟩ : syracuseStep 2852675 = 4279013) B4279013
theorem B1902419 : Blo 1266451 1902419 := bstep (se 1 (by rfl) ⟨1426814, by rfl⟩ : syracuseStep 1902419 = 2853629) B2853629
theorem B2705251 : Blo 1266451 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B6088547 : Blo 1266451 6088547 := bstep (se 1 (by rfl) ⟨4566410, by rfl⟩ : syracuseStep 6088547 = 9132821) B9132821
theorem B10979171 : Blo 1266451 10979171 := bstep (se 1 (by rfl) ⟨8234378, by rfl⟩ : syracuseStep 10979171 = 16468757) B16468757
theorem B1902449 : Blo 1266451 1902449 := bstep (se 2 (by rfl) ⟨713418, by rfl⟩ : syracuseStep 1902449 = 1426837) B1426837
theorem B2140033 : Blo 1266451 2140033 := bstep (se 2 (by rfl) ⟨802512, by rfl⟩ : syracuseStep 2140033 = 1605025) B1605025
theorem B1902467 : Blo 1266451 1902467 := bstep (se 1 (by rfl) ⟨1426850, by rfl⟩ : syracuseStep 1902467 = 2853701) B2853701
theorem B1902497 : Blo 1266451 1902497 := bstep (se 2 (by rfl) ⟨713436, by rfl⟩ : syracuseStep 1902497 = 1426873) B1426873
theorem B2140067 : Blo 1266451 2140067 := bstep (se 1 (by rfl) ⟨1605050, by rfl⟩ : syracuseStep 2140067 = 3210101) B3210101
theorem B1902515 : Blo 1266451 1902515 := bstep (se 1 (by rfl) ⟨1426886, by rfl⟩ : syracuseStep 1902515 = 2853773) B2853773
theorem B9619397 : Blo 1266451 9619397 := bstep (se 4 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 9619397 = 1803637) B1803637
theorem B6416333 : Blo 1266451 6416333 := bstep (se 3 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 6416333 = 2406125) B2406125
theorem B1804241 : Blo 1266451 1804241 := bstep (se 2 (by rfl) ⟨676590, by rfl⟩ : syracuseStep 1804241 = 1353181) B1353181
theorem B1902545 : Blo 1266451 1902545 := bstep (se 2 (by rfl) ⟨713454, by rfl⟩ : syracuseStep 1902545 = 1426909) B1426909
theorem B3655651 : Blo 1266451 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B1902563 : Blo 1266451 1902563 := bstep (se 1 (by rfl) ⟨1426922, by rfl⟩ : syracuseStep 1902563 = 2853845) B2853845
theorem B4278257 : Blo 1266451 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B1902593 : Blo 1266451 1902593 := bstep (se 2 (by rfl) ⟨713472, by rfl⟩ : syracuseStep 1902593 = 1426945) B1426945
theorem B3606545 : Blo 1266451 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B1902611 : Blo 1266451 1902611 := bstep (se 1 (by rfl) ⟨1426958, by rfl⟩ : syracuseStep 1902611 = 2853917) B2853917
theorem B2140195 : Blo 1266451 2140195 := bstep (se 1 (by rfl) ⟨1605146, by rfl⟩ : syracuseStep 2140195 = 3210293) B3210293
theorem B1902641 : Blo 1266451 1902641 := bstep (se 2 (by rfl) ⟨713490, by rfl⟩ : syracuseStep 1902641 = 1426981) B1426981
theorem B1902659 : Blo 1266451 1902659 := bstep (se 1 (by rfl) ⟨1426994, by rfl⟩ : syracuseStep 1902659 = 2853989) B2853989
theorem B2852945 : Blo 1266451 2852945 := bstep (se 2 (by rfl) ⟨1069854, by rfl⟩ : syracuseStep 2852945 = 2139709) B2139709
theorem B3295331 : Blo 1266451 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2852963 : Blo 1266451 2852963 := bstep (se 1 (by rfl) ⟨2139722, by rfl⟩ : syracuseStep 2852963 = 4279445) B4279445
theorem B3852397 : Blo 1266451 3852397 := bstep (se 3 (by rfl) ⟨722324, by rfl⟩ : syracuseStep 3852397 = 1444649) B1444649
theorem B7702705 : Blo 1266451 7702705 := bstep (se 2 (by rfl) ⟨2888514, by rfl⟩ : syracuseStep 7702705 = 5777029) B5777029
theorem B2140337 : Blo 1266451 2140337 := bstep (se 2 (by rfl) ⟨802626, by rfl⟩ : syracuseStep 2140337 = 1605253) B1605253
theorem B4811021 : Blo 1266451 4811021 := bstep (se 3 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 4811021 = 1804133) B1804133
theorem B7219469 : Blo 1266451 7219469 := bstep (se 3 (by rfl) ⟨1353650, by rfl⟩ : syracuseStep 7219469 = 2707301) B2707301
theorem B2140465 : Blo 1266451 2140465 := bstep (se 2 (by rfl) ⟨802674, by rfl⟩ : syracuseStep 2140465 = 1605349) B1605349
theorem B2140499 : Blo 1266451 2140499 := bstep (se 1 (by rfl) ⟨1605374, by rfl⟩ : syracuseStep 2140499 = 3210749) B3210749
theorem B7702897 : Blo 1266451 7702897 := bstep (se 2 (by rfl) ⟨2888586, by rfl⟩ : syracuseStep 7702897 = 5777173) B5777173
theorem B2853233 : Blo 1266451 2853233 := bstep (se 2 (by rfl) ⟨1069962, by rfl⟩ : syracuseStep 2853233 = 2139925) B2139925
theorem B2853251 : Blo 1266451 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B1354163 : Blo 1266451 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B8669645 : Blo 1266451 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B1804771 : Blo 1266451 1804771 := bstep (se 1 (by rfl) ⟨1353578, by rfl⟩ : syracuseStep 1804771 = 2707157) B2707157
theorem B6089201 : Blo 1266451 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B9628145 : Blo 1266451 9628145 := bstep (se 2 (by rfl) ⟨3610554, by rfl⟩ : syracuseStep 9628145 = 7221109) B7221109
theorem B4278797 : Blo 1266451 4278797 := bstep (se 3 (by rfl) ⟨802274, by rfl⟩ : syracuseStep 4278797 = 1604549) B1604549
theorem B2705969 : Blo 1266451 2705969 := bstep (se 2 (by rfl) ⟨1014738, by rfl⟩ : syracuseStep 2705969 = 2029477) B2029477
theorem B4278851 : Blo 1266451 4278851 := bstep (se 1 (by rfl) ⟨3209138, by rfl⟩ : syracuseStep 4278851 = 6418277) B6418277
theorem B10832453 : Blo 1266451 10832453 := bstep (se 4 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 10832453 = 2031085) B2031085
theorem B9136739 : Blo 1266451 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B3656305 : Blo 1266451 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B3205777 : Blo 1266451 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B2853521 : Blo 1266451 2853521 := bstep (se 2 (by rfl) ⟨1070070, by rfl⟩ : syracuseStep 2853521 = 2140141) B2140141
theorem B1829539 : Blo 1266451 1829539 := bstep (se 1 (by rfl) ⟨1372154, by rfl⟩ : syracuseStep 1829539 = 2744309) B2744309
theorem B2853539 : Blo 1266451 2853539 := bstep (se 1 (by rfl) ⟨2140154, by rfl⟩ : syracuseStep 2853539 = 4280309) B4280309
theorem B6851299 : Blo 1266451 6851299 := bstep (se 1 (by rfl) ⟨5138474, by rfl⟩ : syracuseStep 6851299 = 10276949) B10276949
theorem B1805107 : Blo 1266451 1805107 := bstep (se 1 (by rfl) ⟨1353830, by rfl⟩ : syracuseStep 1805107 = 2707661) B2707661
theorem B4279121 : Blo 1266451 4279121 := bstep (se 2 (by rfl) ⟨1604670, by rfl⟩ : syracuseStep 4279121 = 3209341) B3209341
theorem B3206051 : Blo 1266451 3206051 := bstep (se 1 (by rfl) ⟨2404538, by rfl⟩ : syracuseStep 3206051 = 4809077) B4809077
theorem B2853809 : Blo 1266451 2853809 := bstep (se 2 (by rfl) ⟨1070178, by rfl⟩ : syracuseStep 2853809 = 2140357) B2140357
theorem B2853827 : Blo 1266451 2853827 := bstep (se 1 (by rfl) ⟨2140370, by rfl⟩ : syracuseStep 2853827 = 4280741) B4280741
theorem B3656675 : Blo 1266451 3656675 := bstep (se 1 (by rfl) ⟨2742506, by rfl⟩ : syracuseStep 3656675 = 5485013) B5485013
theorem B3607537 : Blo 1266451 3607537 := bstep (se 2 (by rfl) ⟨1352826, by rfl⟩ : syracuseStep 3607537 = 2705653) B2705653
theorem B5418019 : Blo 1266451 5418019 := bstep (se 1 (by rfl) ⟨4063514, by rfl⟩ : syracuseStep 5418019 = 8127029) B8127029
theorem B2706481 : Blo 1266451 2706481 := bstep (se 2 (by rfl) ⟨1014930, by rfl⟩ : syracuseStep 2706481 = 2029861) B2029861
theorem B4811825 : Blo 1266451 4811825 := bstep (se 2 (by rfl) ⟨1804434, by rfl⟩ : syracuseStep 4811825 = 3608869) B3608869
theorem B2198593 : Blo 1266451 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B3206243 : Blo 1266451 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B4058275 : Blo 1266451 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B3607811 : Blo 1266451 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B1805665 : Blo 1266451 1805665 := bstep (se 2 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 1805665 = 1354249) B1354249
theorem B4279661 : Blo 1266451 4279661 := bstep (se 3 (by rfl) ⟨802436, by rfl⟩ : syracuseStep 4279661 = 1604873) B1604873
theorem B1805699 : Blo 1266451 1805699 := bstep (se 1 (by rfl) ⟨1354274, by rfl⟩ : syracuseStep 1805699 = 2708549) B2708549
theorem B4279715 : Blo 1266451 4279715 := bstep (se 1 (by rfl) ⟨3209786, by rfl⟩ : syracuseStep 4279715 = 6419573) B6419573
theorem B3608003 : Blo 1266451 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B4058723 : Blo 1266451 4058723 := bstep (se 1 (by rfl) ⟨3044042, by rfl⟩ : syracuseStep 4058723 = 6088085) B6088085
theorem B3042947 : Blo 1266451 3042947 := bstep (se 1 (by rfl) ⟨2282210, by rfl⟩ : syracuseStep 3042947 = 4564421) B4564421
theorem B4279985 : Blo 1266451 4279985 := bstep (se 2 (by rfl) ⟨1604994, by rfl⟩ : syracuseStep 4279985 = 3209989) B3209989
theorem B4812493 : Blo 1266451 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B14642957 : Blo 1266451 14642957 := bstep (se 3 (by rfl) ⟨2745554, by rfl⟩ : syracuseStep 14642957 = 5491109) B5491109
theorem B32476949 : Blo 1266451 32476949 := bstep (se 6 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 32476949 = 1522357) B1522357
theorem B6090545 : Blo 1266451 6090545 := bstep (se 2 (by rfl) ⟨2283954, by rfl⟩ : syracuseStep 6090545 = 4567909) B4567909
theorem B2166755 : Blo 1266451 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B16470001 : Blo 1266451 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B3207185 : Blo 1266451 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B1953811 : Blo 1266451 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B3207235 : Blo 1266451 3207235 := bstep (se 1 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 3207235 = 4810853) B4810853
theorem B3657869 : Blo 1266451 3657869 := bstep (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) B1371701
theorem B1855649 : Blo 1266451 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B5779619 : Blo 1266451 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B4280525 : Blo 1266451 4280525 := bstep (se 3 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 4280525 = 1605197) B1605197
theorem B2404561 : Blo 1266451 2404561 := bstep (se 2 (by rfl) ⟨901710, by rfl⟩ : syracuseStep 2404561 = 1803421) B1803421
theorem B3207377 : Blo 1266451 3207377 := bstep (se 2 (by rfl) ⟨1202766, by rfl⟩ : syracuseStep 3207377 = 2405533) B2405533
theorem B3608813 : Blo 1266451 3608813 := bstep (se 3 (by rfl) ⟨676652, by rfl⟩ : syracuseStep 3608813 = 1353305) B1353305
theorem B4280579 : Blo 1266451 4280579 := bstep (se 1 (by rfl) ⟨3210434, by rfl⟩ : syracuseStep 4280579 = 6420869) B6420869
theorem B3043601 : Blo 1266451 3043601 := bstep (se 2 (by rfl) ⟨1141350, by rfl⟩ : syracuseStep 3043601 = 2282701) B2282701
theorem B2404721 : Blo 1266451 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B3608995 : Blo 1266451 3608995 := bstep (se 1 (by rfl) ⟨2706746, by rfl⟩ : syracuseStep 3608995 = 5413493) B5413493
theorem B4813283 : Blo 1266451 4813283 := bstep (se 1 (by rfl) ⟨3609962, by rfl⟩ : syracuseStep 4813283 = 7219925) B7219925
theorem B2707985 : Blo 1266451 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B4280849 : Blo 1266451 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B3043889 : Blo 1266451 3043889 := bstep (se 2 (by rfl) ⟨1141458, by rfl⟩ : syracuseStep 3043889 = 2282917) B2282917
theorem B7213637 : Blo 1266451 7213637 := bstep (se 4 (by rfl) ⟨676278, by rfl⟩ : syracuseStep 7213637 = 1352557) B1352557
theorem B6091469 : Blo 1266451 6091469 := bstep (se 3 (by rfl) ⟨1142150, by rfl⟩ : syracuseStep 6091469 = 2284301) B2284301
theorem B10277603 : Blo 1266451 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B2405123 : Blo 1266451 2405123 := bstep (se 1 (by rfl) ⟨1803842, by rfl⟩ : syracuseStep 2405123 = 3607685) B3607685
theorem B3044099 : Blo 1266451 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B1266451 : Blo 1266451 1266451 := bstep (se 1 (by rfl) ⟨949838, by rfl⟩ : syracuseStep 1266451 = 1899677) B1899677
theorem B1266467 : Blo 1266451 1266467 := bstep (se 1 (by rfl) ⟨949850, by rfl⟩ : syracuseStep 1266467 = 1899701) B1899701
theorem B4059953 : Blo 1266451 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B6419249 : Blo 1266451 6419249 := bstep (se 2 (by rfl) ⟨2407218, by rfl⟩ : syracuseStep 6419249 = 4814437) B4814437
theorem B1266483 : Blo 1266451 1266483 := bstep (se 1 (by rfl) ⟨949862, by rfl⟩ : syracuseStep 1266483 = 1899725) B1899725
theorem B1266499 : Blo 1266451 1266499 := bstep (se 1 (by rfl) ⟨949874, by rfl⟩ : syracuseStep 1266499 = 1899749) B1899749
theorem B1266515 : Blo 1266451 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B1266531 : Blo 1266451 1266531 := bstep (se 1 (by rfl) ⟨949898, by rfl⟩ : syracuseStep 1266531 = 1899797) B1899797
theorem B1266547 : Blo 1266451 1266547 := bstep (se 1 (by rfl) ⟨949910, by rfl⟩ : syracuseStep 1266547 = 1899821) B1899821
theorem B1266563 : Blo 1266451 1266563 := bstep (se 1 (by rfl) ⟨949922, by rfl⟩ : syracuseStep 1266563 = 1899845) B1899845
theorem B3609485 : Blo 1266451 3609485 := bstep (se 3 (by rfl) ⟨676778, by rfl⟩ : syracuseStep 3609485 = 1353557) B1353557
theorem B1266579 : Blo 1266451 1266579 := bstep (se 1 (by rfl) ⟨949934, by rfl⟩ : syracuseStep 1266579 = 1899869) B1899869
theorem B1266595 : Blo 1266451 1266595 := bstep (se 1 (by rfl) ⟨949946, by rfl⟩ : syracuseStep 1266595 = 1899893) B1899893
theorem B2708387 : Blo 1266451 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B1266611 : Blo 1266451 1266611 := bstep (se 1 (by rfl) ⟨949958, by rfl⟩ : syracuseStep 1266611 = 1899917) B1899917
theorem B1266627 : Blo 1266451 1266627 := bstep (se 1 (by rfl) ⟨949970, by rfl⟩ : syracuseStep 1266627 = 1899941) B1899941
theorem B2085841 : Blo 1266451 2085841 := bstep (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) B1564381
theorem B1266643 : Blo 1266451 1266643 := bstep (se 1 (by rfl) ⟨949982, by rfl⟩ : syracuseStep 1266643 = 1899965) B1899965
theorem B1266659 : Blo 1266451 1266659 := bstep (se 1 (by rfl) ⟨949994, by rfl⟩ : syracuseStep 1266659 = 1899989) B1899989
theorem B1266675 : Blo 1266451 1266675 := bstep (se 1 (by rfl) ⟨950006, by rfl⟩ : syracuseStep 1266675 = 1900013) B1900013
theorem B1266691 : Blo 1266451 1266691 := bstep (se 1 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 1266691 = 1900037) B1900037
theorem B7214093 : Blo 1266451 7214093 := bstep (se 3 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 7214093 = 2705285) B2705285
theorem B1266707 : Blo 1266451 1266707 := bstep (se 1 (by rfl) ⟨950030, by rfl⟩ : syracuseStep 1266707 = 1900061) B1900061
theorem B1266723 : Blo 1266451 1266723 := bstep (se 1 (by rfl) ⟨950042, by rfl⟩ : syracuseStep 1266723 = 1900085) B1900085
theorem B1266739 : Blo 1266451 1266739 := bstep (se 1 (by rfl) ⟨950054, by rfl⟩ : syracuseStep 1266739 = 1900109) B1900109
theorem B1266755 : Blo 1266451 1266755 := bstep (se 1 (by rfl) ⟨950066, by rfl⟩ : syracuseStep 1266755 = 1900133) B1900133
theorem B1266771 : Blo 1266451 1266771 := bstep (se 1 (by rfl) ⟨950078, by rfl⟩ : syracuseStep 1266771 = 1900157) B1900157
theorem B1266787 : Blo 1266451 1266787 := bstep (se 1 (by rfl) ⟨950090, by rfl⟩ : syracuseStep 1266787 = 1900181) B1900181
theorem B4633699 : Blo 1266451 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B4813937 : Blo 1266451 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B7222385 : Blo 1266451 7222385 := bstep (se 2 (by rfl) ⟨2708394, by rfl⟩ : syracuseStep 7222385 = 5416789) B5416789
theorem B1266803 : Blo 1266451 1266803 := bstep (se 1 (by rfl) ⟨950102, by rfl⟩ : syracuseStep 1266803 = 1900205) B1900205
theorem B1266819 : Blo 1266451 1266819 := bstep (se 1 (by rfl) ⟨950114, by rfl⟩ : syracuseStep 1266819 = 1900229) B1900229
theorem B1266835 : Blo 1266451 1266835 := bstep (se 1 (by rfl) ⟨950126, by rfl⟩ : syracuseStep 1266835 = 1900253) B1900253
theorem B1266851 : Blo 1266451 1266851 := bstep (se 1 (by rfl) ⟨950138, by rfl⟩ : syracuseStep 1266851 = 1900277) B1900277
theorem B3208369 : Blo 1266451 3208369 := bstep (se 2 (by rfl) ⟨1203138, by rfl⟩ : syracuseStep 3208369 = 2406277) B2406277
theorem B1266867 : Blo 1266451 1266867 := bstep (se 1 (by rfl) ⟨950150, by rfl⟩ : syracuseStep 1266867 = 1900301) B1900301
theorem B1266883 : Blo 1266451 1266883 := bstep (se 1 (by rfl) ⟨950162, by rfl⟩ : syracuseStep 1266883 = 1900325) B1900325
theorem B8123597 : Blo 1266451 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B1266899 : Blo 1266451 1266899 := bstep (se 1 (by rfl) ⟨950174, by rfl⟩ : syracuseStep 1266899 = 1900349) B1900349
theorem B1266915 : Blo 1266451 1266915 := bstep (se 1 (by rfl) ⟨950186, by rfl⟩ : syracuseStep 1266915 = 1900373) B1900373
theorem B1266931 : Blo 1266451 1266931 := bstep (se 1 (by rfl) ⟨950198, by rfl⟩ : syracuseStep 1266931 = 1900397) B1900397
theorem B1266947 : Blo 1266451 1266947 := bstep (se 1 (by rfl) ⟨950210, by rfl⟩ : syracuseStep 1266947 = 1900421) B1900421
theorem B1266963 : Blo 1266451 1266963 := bstep (se 1 (by rfl) ⟨950222, by rfl⟩ : syracuseStep 1266963 = 1900445) B1900445
theorem B1266979 : Blo 1266451 1266979 := bstep (se 1 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 1266979 = 1900469) B1900469
theorem B2282801 : Blo 1266451 2282801 := bstep (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) B1712101
theorem B1266995 : Blo 1266451 1266995 := bstep (se 1 (by rfl) ⟨950246, by rfl⟩ : syracuseStep 1266995 = 1900493) B1900493
theorem B31266101 : Blo 1266451 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B1267011 : Blo 1266451 1267011 := bstep (se 1 (by rfl) ⟨950258, by rfl⟩ : syracuseStep 1267011 = 1900517) B1900517
theorem B1267027 : Blo 1266451 1267027 := bstep (se 1 (by rfl) ⟨950270, by rfl⟩ : syracuseStep 1267027 = 1900541) B1900541
theorem B1267043 : Blo 1266451 1267043 := bstep (se 1 (by rfl) ⟨950282, by rfl⟩ : syracuseStep 1267043 = 1900565) B1900565
theorem B1267059 : Blo 1266451 1267059 := bstep (se 1 (by rfl) ⟨950294, by rfl⟩ : syracuseStep 1267059 = 1900589) B1900589
theorem B1267075 : Blo 1266451 1267075 := bstep (se 1 (by rfl) ⟨950306, by rfl⟩ : syracuseStep 1267075 = 1900613) B1900613
theorem B1267091 : Blo 1266451 1267091 := bstep (se 1 (by rfl) ⟨950318, by rfl⟩ : syracuseStep 1267091 = 1900637) B1900637
theorem B1267107 : Blo 1266451 1267107 := bstep (se 1 (by rfl) ⟨950330, by rfl⟩ : syracuseStep 1267107 = 1900661) B1900661
theorem B1267123 : Blo 1266451 1267123 := bstep (se 1 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 1267123 = 1900685) B1900685
theorem B1267139 : Blo 1266451 1267139 := bstep (se 1 (by rfl) ⟨950354, by rfl⟩ : syracuseStep 1267139 = 1900709) B1900709
theorem B3208643 : Blo 1266451 3208643 := bstep (se 1 (by rfl) ⟨2406482, by rfl⟩ : syracuseStep 3208643 = 4812965) B4812965
theorem B1267155 : Blo 1266451 1267155 := bstep (se 1 (by rfl) ⟨950366, by rfl⟩ : syracuseStep 1267155 = 1900733) B1900733
theorem B1267171 : Blo 1266451 1267171 := bstep (se 1 (by rfl) ⟨950378, by rfl⟩ : syracuseStep 1267171 = 1900757) B1900757
theorem B1267187 : Blo 1266451 1267187 := bstep (se 1 (by rfl) ⟨950390, by rfl⟩ : syracuseStep 1267187 = 1900781) B1900781
theorem B1267203 : Blo 1266451 1267203 := bstep (se 1 (by rfl) ⟨950402, by rfl⟩ : syracuseStep 1267203 = 1900805) B1900805
theorem B1603091 : Blo 1266451 1603091 := bstep (se 1 (by rfl) ⟨1202318, by rfl⟩ : syracuseStep 1603091 = 2404637) B2404637
theorem B1267219 : Blo 1266451 1267219 := bstep (se 1 (by rfl) ⟨950414, by rfl⟩ : syracuseStep 1267219 = 1900829) B1900829
theorem B1267235 : Blo 1266451 1267235 := bstep (se 1 (by rfl) ⟨950426, by rfl⟩ : syracuseStep 1267235 = 1900853) B1900853
theorem B1267251 : Blo 1266451 1267251 := bstep (se 1 (by rfl) ⟨950438, by rfl⟩ : syracuseStep 1267251 = 1900877) B1900877
theorem B1267267 : Blo 1266451 1267267 := bstep (se 1 (by rfl) ⟨950450, by rfl⟩ : syracuseStep 1267267 = 1900901) B1900901
theorem B1267283 : Blo 1266451 1267283 := bstep (se 1 (by rfl) ⟨950462, by rfl⟩ : syracuseStep 1267283 = 1900925) B1900925
theorem B1267299 : Blo 1266451 1267299 := bstep (se 1 (by rfl) ⟨950474, by rfl⟩ : syracuseStep 1267299 = 1900949) B1900949
theorem B2029169 : Blo 1266451 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B1267315 : Blo 1266451 1267315 := bstep (se 1 (by rfl) ⟨950486, by rfl⟩ : syracuseStep 1267315 = 1900973) B1900973
theorem B1267331 : Blo 1266451 1267331 := bstep (se 1 (by rfl) ⟨950498, by rfl⟩ : syracuseStep 1267331 = 1900997) B1900997
theorem B2406019 : Blo 1266451 2406019 := bstep (se 1 (by rfl) ⟨1804514, by rfl⟩ : syracuseStep 2406019 = 3609029) B3609029
theorem B3208835 : Blo 1266451 3208835 := bstep (se 1 (by rfl) ⟨2406626, by rfl⟩ : syracuseStep 3208835 = 4813253) B4813253
theorem B18282125 : Blo 1266451 18282125 := bstep (se 3 (by rfl) ⟨3427898, by rfl⟩ : syracuseStep 18282125 = 6855797) B6855797
theorem B1267347 : Blo 1266451 1267347 := bstep (se 1 (by rfl) ⟨950510, by rfl⟩ : syracuseStep 1267347 = 1901021) B1901021
theorem B1267363 : Blo 1266451 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B4060849 : Blo 1266451 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B1267379 : Blo 1266451 1267379 := bstep (se 1 (by rfl) ⟨950534, by rfl⟩ : syracuseStep 1267379 = 1901069) B1901069
theorem B1267395 : Blo 1266451 1267395 := bstep (se 1 (by rfl) ⟨950546, by rfl⟩ : syracuseStep 1267395 = 1901093) B1901093
theorem B1267411 : Blo 1266451 1267411 := bstep (se 1 (by rfl) ⟨950558, by rfl⟩ : syracuseStep 1267411 = 1901117) B1901117
theorem B1267427 : Blo 1266451 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B2029297 : Blo 1266451 2029297 := bstep (se 2 (by rfl) ⟨760986, by rfl⟩ : syracuseStep 2029297 = 1521973) B1521973
theorem B1267443 : Blo 1266451 1267443 := bstep (se 1 (by rfl) ⟨950582, by rfl⟩ : syracuseStep 1267443 = 1901165) B1901165
theorem B1267459 : Blo 1266451 1267459 := bstep (se 1 (by rfl) ⟨950594, by rfl⟩ : syracuseStep 1267459 = 1901189) B1901189
theorem B15406861 : Blo 1266451 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B1267475 : Blo 1266451 1267475 := bstep (se 1 (by rfl) ⟨950606, by rfl⟩ : syracuseStep 1267475 = 1901213) B1901213
theorem B2406179 : Blo 1266451 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B1267491 : Blo 1266451 1267491 := bstep (se 1 (by rfl) ⟨950618, by rfl⟩ : syracuseStep 1267491 = 1901237) B1901237
theorem B1267507 : Blo 1266451 1267507 := bstep (se 1 (by rfl) ⟨950630, by rfl⟩ : syracuseStep 1267507 = 1901261) B1901261
theorem B1267523 : Blo 1266451 1267523 := bstep (se 1 (by rfl) ⟨950642, by rfl⟩ : syracuseStep 1267523 = 1901285) B1901285
theorem B1267539 : Blo 1266451 1267539 := bstep (se 1 (by rfl) ⟨950654, by rfl⟩ : syracuseStep 1267539 = 1901309) B1901309
theorem B1267555 : Blo 1266451 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B1267571 : Blo 1266451 1267571 := bstep (se 1 (by rfl) ⟨950678, by rfl⟩ : syracuseStep 1267571 = 1901357) B1901357
theorem B1267587 : Blo 1266451 1267587 := bstep (se 1 (by rfl) ⟨950690, by rfl⟩ : syracuseStep 1267587 = 1901381) B1901381
theorem B1267603 : Blo 1266451 1267603 := bstep (se 1 (by rfl) ⟨950702, by rfl⟩ : syracuseStep 1267603 = 1901405) B1901405
theorem B1267619 : Blo 1266451 1267619 := bstep (se 1 (by rfl) ⟨950714, by rfl⟩ : syracuseStep 1267619 = 1901429) B1901429
theorem B2570147 : Blo 1266451 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B1267635 : Blo 1266451 1267635 := bstep (se 1 (by rfl) ⟨950726, by rfl⟩ : syracuseStep 1267635 = 1901453) B1901453
theorem B1267651 : Blo 1266451 1267651 := bstep (se 1 (by rfl) ⟨950738, by rfl⟩ : syracuseStep 1267651 = 1901477) B1901477
theorem B1267667 : Blo 1266451 1267667 := bstep (se 1 (by rfl) ⟨950750, by rfl⟩ : syracuseStep 1267667 = 1901501) B1901501
theorem B1267683 : Blo 1266451 1267683 := bstep (se 1 (by rfl) ⟨950762, by rfl⟩ : syracuseStep 1267683 = 1901525) B1901525
theorem B1267699 : Blo 1266451 1267699 := bstep (se 1 (by rfl) ⟨950774, by rfl⟩ : syracuseStep 1267699 = 1901549) B1901549
theorem B1267715 : Blo 1266451 1267715 := bstep (se 1 (by rfl) ⟨950786, by rfl⟩ : syracuseStep 1267715 = 1901573) B1901573
theorem B1267731 : Blo 1266451 1267731 := bstep (se 1 (by rfl) ⟨950798, by rfl⟩ : syracuseStep 1267731 = 1901597) B1901597
theorem B1267747 : Blo 1266451 1267747 := bstep (se 1 (by rfl) ⟨950810, by rfl⟩ : syracuseStep 1267747 = 1901621) B1901621
theorem B3610669 : Blo 1266451 3610669 := bstep (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) B1354001
theorem B1267763 : Blo 1266451 1267763 := bstep (se 1 (by rfl) ⟨950822, by rfl⟩ : syracuseStep 1267763 = 1901645) B1901645
theorem B1267779 : Blo 1266451 1267779 := bstep (se 1 (by rfl) ⟨950834, by rfl⟩ : syracuseStep 1267779 = 1901669) B1901669
theorem B1267795 : Blo 1266451 1267795 := bstep (se 1 (by rfl) ⟨950846, by rfl⟩ : syracuseStep 1267795 = 1901693) B1901693
theorem B1267811 : Blo 1266451 1267811 := bstep (se 1 (by rfl) ⟨950858, by rfl⟩ : syracuseStep 1267811 = 1901717) B1901717
theorem B1267827 : Blo 1266451 1267827 := bstep (se 1 (by rfl) ⟨950870, by rfl⟩ : syracuseStep 1267827 = 1901741) B1901741
theorem B1464451 : Blo 1266451 1464451 := bstep (se 1 (by rfl) ⟨1098338, by rfl⟩ : syracuseStep 1464451 = 2196677) B2196677
theorem B1267843 : Blo 1266451 1267843 := bstep (se 1 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 1267843 = 1901765) B1901765
theorem B1267859 : Blo 1266451 1267859 := bstep (se 1 (by rfl) ⟨950894, by rfl⟩ : syracuseStep 1267859 = 1901789) B1901789
theorem B1267875 : Blo 1266451 1267875 := bstep (se 1 (by rfl) ⟨950906, by rfl⟩ : syracuseStep 1267875 = 1901813) B1901813
theorem B1267891 : Blo 1266451 1267891 := bstep (se 1 (by rfl) ⟨950918, by rfl⟩ : syracuseStep 1267891 = 1901837) B1901837
theorem B1267907 : Blo 1266451 1267907 := bstep (se 1 (by rfl) ⟨950930, by rfl⟩ : syracuseStep 1267907 = 1901861) B1901861
theorem B4569293 : Blo 1266451 4569293 := bstep (se 3 (by rfl) ⟨856742, by rfl⟩ : syracuseStep 4569293 = 1713485) B1713485
theorem B1603795 : Blo 1266451 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B1267923 : Blo 1266451 1267923 := bstep (se 1 (by rfl) ⟨950942, by rfl⟩ : syracuseStep 1267923 = 1901885) B1901885
theorem B1267939 : Blo 1266451 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B6420707 : Blo 1266451 6420707 := bstep (se 1 (by rfl) ⟨4815530, by rfl⟩ : syracuseStep 6420707 = 9631061) B9631061
theorem B1267955 : Blo 1266451 1267955 := bstep (se 1 (by rfl) ⟨950966, by rfl⟩ : syracuseStep 1267955 = 1901933) B1901933
theorem B1267971 : Blo 1266451 1267971 := bstep (se 1 (by rfl) ⟨950978, by rfl⟩ : syracuseStep 1267971 = 1901957) B1901957
theorem B1267987 : Blo 1266451 1267987 := bstep (se 1 (by rfl) ⟨950990, by rfl⟩ : syracuseStep 1267987 = 1901981) B1901981
theorem B1268003 : Blo 1266451 1268003 := bstep (se 1 (by rfl) ⟨951002, by rfl⟩ : syracuseStep 1268003 = 1902005) B1902005
theorem B4274477 : Blo 1266451 4274477 := bstep (se 3 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 4274477 = 1602929) B1602929
theorem B1603891 : Blo 1266451 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B1268019 : Blo 1266451 1268019 := bstep (se 1 (by rfl) ⟨951014, by rfl⟩ : syracuseStep 1268019 = 1902029) B1902029
theorem B1268035 : Blo 1266451 1268035 := bstep (se 1 (by rfl) ⟨951026, by rfl⟩ : syracuseStep 1268035 = 1902053) B1902053
theorem B1268051 : Blo 1266451 1268051 := bstep (se 1 (by rfl) ⟨951038, by rfl⟩ : syracuseStep 1268051 = 1902077) B1902077
theorem B4274531 : Blo 1266451 4274531 := bstep (se 1 (by rfl) ⟨3205898, by rfl⟩ : syracuseStep 4274531 = 6411797) B6411797
theorem B1268067 : Blo 1266451 1268067 := bstep (se 1 (by rfl) ⟨951050, by rfl⟩ : syracuseStep 1268067 = 1902101) B1902101
theorem B1268083 : Blo 1266451 1268083 := bstep (se 1 (by rfl) ⟨951062, by rfl⟩ : syracuseStep 1268083 = 1902125) B1902125
theorem B1268099 : Blo 1266451 1268099 := bstep (se 1 (by rfl) ⟨951074, by rfl⟩ : syracuseStep 1268099 = 1902149) B1902149
theorem B1268115 : Blo 1266451 1268115 := bstep (se 1 (by rfl) ⟨951086, by rfl⟩ : syracuseStep 1268115 = 1902173) B1902173
theorem B1268131 : Blo 1266451 1268131 := bstep (se 1 (by rfl) ⟨951098, by rfl⟩ : syracuseStep 1268131 = 1902197) B1902197
theorem B1268147 : Blo 1266451 1268147 := bstep (se 1 (by rfl) ⟨951110, by rfl⟩ : syracuseStep 1268147 = 1902221) B1902221
theorem B1268163 : Blo 1266451 1268163 := bstep (se 1 (by rfl) ⟨951122, by rfl⟩ : syracuseStep 1268163 = 1902245) B1902245
theorem B36534725 : Blo 1266451 36534725 := bstep (se 4 (by rfl) ⟨3425130, by rfl⟩ : syracuseStep 36534725 = 6850261) B6850261
theorem B1268179 : Blo 1266451 1268179 := bstep (se 1 (by rfl) ⟨951134, by rfl⟩ : syracuseStep 1268179 = 1902269) B1902269
theorem B1268195 : Blo 1266451 1268195 := bstep (se 1 (by rfl) ⟨951146, by rfl⟩ : syracuseStep 1268195 = 1902293) B1902293
theorem B1268211 : Blo 1266451 1268211 := bstep (se 1 (by rfl) ⟨951158, by rfl⟩ : syracuseStep 1268211 = 1902317) B1902317
theorem B1268227 : Blo 1266451 1268227 := bstep (se 1 (by rfl) ⟨951170, by rfl⟩ : syracuseStep 1268227 = 1902341) B1902341
theorem B1268243 : Blo 1266451 1268243 := bstep (se 1 (by rfl) ⟨951182, by rfl⟩ : syracuseStep 1268243 = 1902365) B1902365
theorem B4815395 : Blo 1266451 4815395 := bstep (se 1 (by rfl) ⟨3611546, by rfl⟩ : syracuseStep 4815395 = 7223093) B7223093
theorem B1268259 : Blo 1266451 1268259 := bstep (se 1 (by rfl) ⟨951194, by rfl⟩ : syracuseStep 1268259 = 1902389) B1902389
theorem B7223843 : Blo 1266451 7223843 := bstep (se 1 (by rfl) ⟨5417882, by rfl⟩ : syracuseStep 7223843 = 10835765) B10835765
theorem B3045937 : Blo 1266451 3045937 := bstep (se 2 (by rfl) ⟨1142226, by rfl⟩ : syracuseStep 3045937 = 2284453) B2284453
theorem B3209777 : Blo 1266451 3209777 := bstep (se 2 (by rfl) ⟨1203666, by rfl⟩ : syracuseStep 3209777 = 2407333) B2407333
theorem B4815409 : Blo 1266451 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B1268275 : Blo 1266451 1268275 := bstep (se 1 (by rfl) ⟨951206, by rfl⟩ : syracuseStep 1268275 = 1902413) B1902413
theorem B1268291 : Blo 1266451 1268291 := bstep (se 1 (by rfl) ⟨951218, by rfl⟩ : syracuseStep 1268291 = 1902437) B1902437
theorem B1268307 : Blo 1266451 1268307 := bstep (se 1 (by rfl) ⟨951230, by rfl⟩ : syracuseStep 1268307 = 1902461) B1902461
theorem B3209827 : Blo 1266451 3209827 := bstep (se 1 (by rfl) ⟨2407370, by rfl⟩ : syracuseStep 3209827 = 4814741) B4814741
theorem B1268323 : Blo 1266451 1268323 := bstep (se 1 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 1268323 = 1902485) B1902485
theorem B4274801 : Blo 1266451 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B1268339 : Blo 1266451 1268339 := bstep (se 1 (by rfl) ⟨951254, by rfl⟩ : syracuseStep 1268339 = 1902509) B1902509
theorem B1268355 : Blo 1266451 1268355 := bstep (se 1 (by rfl) ⟨951266, by rfl⟩ : syracuseStep 1268355 = 1902533) B1902533
theorem B1268371 : Blo 1266451 1268371 := bstep (se 1 (by rfl) ⟨951278, by rfl⟩ : syracuseStep 1268371 = 1902557) B1902557
theorem B1268387 : Blo 1266451 1268387 := bstep (se 1 (by rfl) ⟨951290, by rfl⟩ : syracuseStep 1268387 = 1902581) B1902581
theorem B1268403 : Blo 1266451 1268403 := bstep (se 1 (by rfl) ⟨951302, by rfl⟩ : syracuseStep 1268403 = 1902605) B1902605
theorem B1268419 : Blo 1266451 1268419 := bstep (se 1 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 1268419 = 1902629) B1902629
theorem B1268435 : Blo 1266451 1268435 := bstep (se 1 (by rfl) ⟨951326, by rfl⟩ : syracuseStep 1268435 = 1902653) B1902653
theorem B1268451 : Blo 1266451 1268451 := bstep (se 1 (by rfl) ⟨951338, by rfl⟩ : syracuseStep 1268451 = 1902677) B1902677
theorem B3209969 : Blo 1266451 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B5413645 : Blo 1266451 5413645 := bstep (se 3 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 5413645 = 2030117) B2030117
theorem B1604387 : Blo 1266451 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B2439971 : Blo 1266451 2439971 := bstep (se 1 (by rfl) ⟨1829978, by rfl⟩ : syracuseStep 2439971 = 3659957) B3659957
theorem B2407249 : Blo 1266451 2407249 := bstep (se 2 (by rfl) ⟨902718, by rfl⟩ : syracuseStep 2407249 = 1805437) B1805437
theorem B2849777 : Blo 1266451 2849777 := bstep (se 2 (by rfl) ⟨1068666, by rfl⟩ : syracuseStep 2849777 = 2137333) B2137333
theorem B2030579 : Blo 1266451 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B2849795 : Blo 1266451 2849795 := bstep (se 1 (by rfl) ⟨2137346, by rfl⟩ : syracuseStep 2849795 = 4274693) B4274693
theorem B6421517 : Blo 1266451 6421517 := bstep (se 3 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 6421517 = 2408069) B2408069
theorem B3611729 : Blo 1266451 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B2137171 : Blo 1266451 2137171 := bstep (se 1 (by rfl) ⟨1602878, by rfl⟩ : syracuseStep 2137171 = 3205757) B3205757
theorem B2030675 : Blo 1266451 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B2030707 : Blo 1266451 2030707 := bstep (se 1 (by rfl) ⟨1523030, by rfl⟩ : syracuseStep 2030707 = 3046061) B3046061
theorem B4275341 : Blo 1266451 4275341 := bstep (se 3 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 4275341 = 1603253) B1603253
theorem B1899683 : Blo 1266451 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B3128483 : Blo 1266451 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B1899713 : Blo 1266451 1899713 := bstep (se 2 (by rfl) ⟨712392, by rfl⟩ : syracuseStep 1899713 = 1424785) B1424785
theorem B4275395 : Blo 1266451 4275395 := bstep (se 1 (by rfl) ⟨3206546, by rfl⟩ : syracuseStep 4275395 = 6413093) B6413093
theorem B4062413 : Blo 1266451 4062413 := bstep (se 3 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 4062413 = 1523405) B1523405
theorem B1899731 : Blo 1266451 1899731 := bstep (se 1 (by rfl) ⟨1424798, by rfl⟩ : syracuseStep 1899731 = 2849597) B2849597
theorem B2137313 : Blo 1266451 2137313 := bstep (se 2 (by rfl) ⟨801492, by rfl⟩ : syracuseStep 2137313 = 1602985) B1602985
theorem B4881635 : Blo 1266451 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B1899761 : Blo 1266451 1899761 := bstep (se 2 (by rfl) ⟨712410, by rfl⟩ : syracuseStep 1899761 = 1424821) B1424821
theorem B1899779 : Blo 1266451 1899779 := bstep (se 1 (by rfl) ⟨1424834, by rfl⟩ : syracuseStep 1899779 = 2849669) B2849669
theorem B2850065 : Blo 1266451 2850065 := bstep (se 2 (by rfl) ⟨1068774, by rfl⟩ : syracuseStep 2850065 = 2137549) B2137549
theorem B1899809 : Blo 1266451 1899809 := bstep (se 2 (by rfl) ⟨712428, by rfl⟩ : syracuseStep 1899809 = 1424857) B1424857
theorem B2850083 : Blo 1266451 2850083 := bstep (se 1 (by rfl) ⟨2137562, by rfl⟩ : syracuseStep 2850083 = 4275125) B4275125
theorem B5487907 : Blo 1266451 5487907 := bstep (se 1 (by rfl) ⟨4115930, by rfl⟩ : syracuseStep 5487907 = 8231861) B8231861
theorem B1899827 : Blo 1266451 1899827 := bstep (se 1 (by rfl) ⟨1424870, by rfl⟩ : syracuseStep 1899827 = 2849741) B2849741
theorem B1523011 : Blo 1266451 1523011 := bstep (se 1 (by rfl) ⟨1142258, by rfl⟩ : syracuseStep 1523011 = 2284517) B2284517
theorem B1899857 : Blo 1266451 1899857 := bstep (se 2 (by rfl) ⟨712446, by rfl⟩ : syracuseStep 1899857 = 1424893) B1424893
theorem B2137441 : Blo 1266451 2137441 := bstep (se 2 (by rfl) ⟨801540, by rfl⟩ : syracuseStep 2137441 = 1603081) B1603081
theorem B1899875 : Blo 1266451 1899875 := bstep (se 1 (by rfl) ⟨1424906, by rfl⟩ : syracuseStep 1899875 = 2849813) B2849813
theorem B3472739 : Blo 1266451 3472739 := bstep (se 1 (by rfl) ⟨2604554, by rfl⟩ : syracuseStep 3472739 = 5209109) B5209109
theorem B1899905 : Blo 1266451 1899905 := bstep (se 2 (by rfl) ⟨712464, by rfl⟩ : syracuseStep 1899905 = 1424929) B1424929
theorem B2137475 : Blo 1266451 2137475 := bstep (se 1 (by rfl) ⟨1603106, by rfl⟩ : syracuseStep 2137475 = 3206213) B3206213
theorem B1899923 : Blo 1266451 1899923 := bstep (se 1 (by rfl) ⟨1424942, by rfl⟩ : syracuseStep 1899923 = 2849885) B2849885
theorem B1424803 : Blo 1266451 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1523107 : Blo 1266451 1523107 := bstep (se 1 (by rfl) ⟨1142330, by rfl⟩ : syracuseStep 1523107 = 2284661) B2284661
theorem B1899953 : Blo 1266451 1899953 := bstep (se 2 (by rfl) ⟨712482, by rfl⟩ : syracuseStep 1899953 = 1424965) B1424965
theorem B1899971 : Blo 1266451 1899971 := bstep (se 1 (by rfl) ⟨1424978, by rfl⟩ : syracuseStep 1899971 = 2849957) B2849957
theorem B4275665 : Blo 1266451 4275665 := bstep (se 2 (by rfl) ⟨1603374, by rfl⟩ : syracuseStep 4275665 = 3206749) B3206749
theorem B1900001 : Blo 1266451 1900001 := bstep (se 2 (by rfl) ⟨712500, by rfl⟩ : syracuseStep 1900001 = 1425001) B1425001
theorem B1605091 : Blo 1266451 1605091 := bstep (se 1 (by rfl) ⟨1203818, by rfl⟩ : syracuseStep 1605091 = 2407637) B2407637
theorem B1900019 : Blo 1266451 1900019 := bstep (se 1 (by rfl) ⟨1425014, by rfl⟩ : syracuseStep 1900019 = 2850029) B2850029
theorem B2137603 : Blo 1266451 2137603 := bstep (se 1 (by rfl) ⟨1603202, by rfl⟩ : syracuseStep 2137603 = 3206405) B3206405
theorem B1900049 : Blo 1266451 1900049 := bstep (se 2 (by rfl) ⟨712518, by rfl⟩ : syracuseStep 1900049 = 1425037) B1425037
theorem B1900067 : Blo 1266451 1900067 := bstep (se 1 (by rfl) ⟨1425050, by rfl⟩ : syracuseStep 1900067 = 2850101) B2850101
theorem B2850353 : Blo 1266451 2850353 := bstep (se 2 (by rfl) ⟨1068882, by rfl⟩ : syracuseStep 2850353 = 2137765) B2137765
theorem B1424947 : Blo 1266451 1424947 := bstep (se 1 (by rfl) ⟨1068710, by rfl⟩ : syracuseStep 1424947 = 2137421) B2137421
theorem B1900097 : Blo 1266451 1900097 := bstep (se 2 (by rfl) ⟨712536, by rfl⟩ : syracuseStep 1900097 = 1425073) B1425073
theorem B2850371 : Blo 1266451 2850371 := bstep (se 1 (by rfl) ⟨2137778, by rfl⟩ : syracuseStep 2850371 = 4275557) B4275557
theorem B1605187 : Blo 1266451 1605187 := bstep (se 1 (by rfl) ⟨1203890, by rfl⟩ : syracuseStep 1605187 = 2407781) B2407781
theorem B1900115 : Blo 1266451 1900115 := bstep (se 1 (by rfl) ⟨1425086, by rfl⟩ : syracuseStep 1900115 = 2850173) B2850173
theorem B1900145 : Blo 1266451 1900145 := bstep (se 2 (by rfl) ⟨712554, by rfl⟩ : syracuseStep 1900145 = 1425109) B1425109
theorem B1900163 : Blo 1266451 1900163 := bstep (se 1 (by rfl) ⟨1425122, by rfl⟩ : syracuseStep 1900163 = 2850245) B2850245
theorem B9625229 : Blo 1266451 9625229 := bstep (se 3 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 9625229 = 3609461) B3609461
theorem B2137745 : Blo 1266451 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1900193 : Blo 1266451 1900193 := bstep (se 2 (by rfl) ⟨712572, by rfl⟩ : syracuseStep 1900193 = 1425145) B1425145
theorem B1900211 : Blo 1266451 1900211 := bstep (se 1 (by rfl) ⟨1425158, by rfl⟩ : syracuseStep 1900211 = 2850317) B2850317
theorem B1425091 : Blo 1266451 1425091 := bstep (se 1 (by rfl) ⟨1068818, by rfl⟩ : syracuseStep 1425091 = 2137637) B2137637
theorem B1900241 : Blo 1266451 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B1900259 : Blo 1266451 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B12517091 : Blo 1266451 12517091 := bstep (se 1 (by rfl) ⟨9387818, by rfl⟩ : syracuseStep 12517091 = 18775637) B18775637
theorem B6414065 : Blo 1266451 6414065 := bstep (se 2 (by rfl) ⟨2405274, by rfl⟩ : syracuseStep 6414065 = 4810549) B4810549
theorem B1900289 : Blo 1266451 1900289 := bstep (se 2 (by rfl) ⟨712608, by rfl⟩ : syracuseStep 1900289 = 1425217) B1425217
theorem B2137873 : Blo 1266451 2137873 := bstep (se 2 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 2137873 = 1603405) B1603405
theorem B1900307 : Blo 1266451 1900307 := bstep (se 1 (by rfl) ⟨1425230, by rfl⟩ : syracuseStep 1900307 = 2850461) B2850461
theorem B1900337 : Blo 1266451 1900337 := bstep (se 2 (by rfl) ⟨712626, by rfl⟩ : syracuseStep 1900337 = 1425253) B1425253
theorem B2137907 : Blo 1266451 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B1900355 : Blo 1266451 1900355 := bstep (se 1 (by rfl) ⟨1425266, by rfl⟩ : syracuseStep 1900355 = 2850533) B2850533
theorem B2850641 : Blo 1266451 2850641 := bstep (se 2 (by rfl) ⟨1068990, by rfl⟩ : syracuseStep 2850641 = 2137981) B2137981
theorem B1425235 : Blo 1266451 1425235 := bstep (se 1 (by rfl) ⟨1068926, by rfl⟩ : syracuseStep 1425235 = 2137853) B2137853
theorem B1900385 : Blo 1266451 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B2850659 : Blo 1266451 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B8666993 : Blo 1266451 8666993 := bstep (se 2 (by rfl) ⟨3250122, by rfl⟩ : syracuseStep 8666993 = 6500245) B6500245
theorem B7217009 : Blo 1266451 7217009 := bstep (se 2 (by rfl) ⟨2706378, by rfl⟩ : syracuseStep 7217009 = 5412757) B5412757
theorem B1900403 : Blo 1266451 1900403 := bstep (se 1 (by rfl) ⟨1425302, by rfl⟩ : syracuseStep 1900403 = 2850605) B2850605
theorem B1900433 : Blo 1266451 1900433 := bstep (se 2 (by rfl) ⟨712662, by rfl⟩ : syracuseStep 1900433 = 1425325) B1425325
theorem B1900451 : Blo 1266451 1900451 := bstep (se 1 (by rfl) ⟨1425338, by rfl⟩ : syracuseStep 1900451 = 2850677) B2850677
theorem B2138035 : Blo 1266451 2138035 := bstep (se 1 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 2138035 = 3207053) B3207053
theorem B1900481 : Blo 1266451 1900481 := bstep (se 2 (by rfl) ⟨712680, by rfl⟩ : syracuseStep 1900481 = 1425361) B1425361
theorem B1900499 : Blo 1266451 1900499 := bstep (se 1 (by rfl) ⟨1425374, by rfl⟩ : syracuseStep 1900499 = 2850749) B2850749
theorem B1425379 : Blo 1266451 1425379 := bstep (se 1 (by rfl) ⟨1069034, by rfl⟩ : syracuseStep 1425379 = 2138069) B2138069
theorem B4276205 : Blo 1266451 4276205 := bstep (se 3 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 4276205 = 1603577) B1603577
theorem B1900529 : Blo 1266451 1900529 := bstep (se 2 (by rfl) ⟨712698, by rfl⟩ : syracuseStep 1900529 = 1425397) B1425397
theorem B2138123 : Blo 1266451 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B2850839 : Blo 1266451 2850839 := bstep (se 1 (by rfl) ⟨2138129, by rfl⟩ : syracuseStep 2850839 = 4276259) B4276259
theorem B1425451 : Blo 1266451 1425451 := bstep (se 1 (by rfl) ⟨1069088, by rfl⟩ : syracuseStep 1425451 = 2138177) B2138177
theorem B9617453 : Blo 1266451 9617453 := bstep (se 3 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 9617453 = 3606545) B3606545
theorem B1900619 : Blo 1266451 1900619 := bstep (se 1 (by rfl) ⟨1425464, by rfl⟩ : syracuseStep 1900619 = 2850929) B2850929
theorem B1900631 : Blo 1266451 1900631 := bstep (se 1 (by rfl) ⟨1425473, by rfl⟩ : syracuseStep 1900631 = 2850947) B2850947
theorem B4276313 : Blo 1266451 4276313 := bstep (se 2 (by rfl) ⟨1603617, by rfl⟩ : syracuseStep 4276313 = 3207235) B3207235
theorem B10420325 : Blo 1266451 10420325 := bstep (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) B1953811
theorem B2138251 : Blo 1266451 2138251 := bstep (se 1 (by rfl) ⟨1603688, by rfl⟩ : syracuseStep 2138251 = 3207377) B3207377
theorem B5136529 : Blo 1266451 5136529 := bstep (se 2 (by rfl) ⟨1926198, by rfl⟩ : syracuseStep 5136529 = 3852397) B3852397
theorem B1425559 : Blo 1266451 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B1900697 : Blo 1266451 1900697 := bstep (se 2 (by rfl) ⟨712761, by rfl⟩ : syracuseStep 1900697 = 1425523) B1425523
theorem B2851019 : Blo 1266451 2851019 := bstep (se 1 (by rfl) ⟨2138264, by rfl⟩ : syracuseStep 2851019 = 4276529) B4276529
theorem B5415133 : Blo 1266451 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B2851073 : Blo 1266451 2851073 := bstep (se 2 (by rfl) ⟨1069152, by rfl⟩ : syracuseStep 2851073 = 2138305) B2138305
theorem B1900811 : Blo 1266451 1900811 := bstep (se 1 (by rfl) ⟨1425608, by rfl⟩ : syracuseStep 1900811 = 2851217) B2851217
theorem B11567377 : Blo 1266451 11567377 := bstep (se 2 (by rfl) ⟨4337766, by rfl⟩ : syracuseStep 11567377 = 8675533) B8675533
theorem B1900823 : Blo 1266451 1900823 := bstep (se 1 (by rfl) ⟨1425617, by rfl⟩ : syracuseStep 1900823 = 2851235) B2851235
theorem B2138393 : Blo 1266451 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B1425739 : Blo 1266451 1425739 := bstep (se 1 (by rfl) ⟨1069304, by rfl⟩ : syracuseStep 1425739 = 2138609) B2138609
theorem B1900889 : Blo 1266451 1900889 := bstep (se 2 (by rfl) ⟨712833, by rfl⟩ : syracuseStep 1900889 = 1425667) B1425667
theorem B4809091 : Blo 1266451 4809091 := bstep (se 1 (by rfl) ⟨3606818, by rfl⟩ : syracuseStep 4809091 = 7213637) B7213637
theorem B2138521 : Blo 1266451 2138521 := bstep (se 2 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 2138521 = 1603891) B1603891
theorem B4948397 : Blo 1266451 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B1425847 : Blo 1266451 1425847 := bstep (se 1 (by rfl) ⟨1069385, by rfl⟩ : syracuseStep 1425847 = 2138771) B2138771
theorem B1901003 : Blo 1266451 1901003 := bstep (se 1 (by rfl) ⟨1425752, by rfl⟩ : syracuseStep 1901003 = 2851505) B2851505
theorem B1901015 : Blo 1266451 1901015 := bstep (se 1 (by rfl) ⟨1425761, by rfl⟩ : syracuseStep 1901015 = 2851523) B2851523
theorem B2851289 : Blo 1266451 2851289 := bstep (se 2 (by rfl) ⟨1069233, by rfl⟩ : syracuseStep 2851289 = 2138467) B2138467
theorem B1901081 : Blo 1266451 1901081 := bstep (se 2 (by rfl) ⟨712905, by rfl⟩ : syracuseStep 1901081 = 1425811) B1425811
theorem B2851379 : Blo 1266451 2851379 := bstep (se 1 (by rfl) ⟨2138534, by rfl⟩ : syracuseStep 2851379 = 4277069) B4277069
theorem B2851415 : Blo 1266451 2851415 := bstep (se 1 (by rfl) ⟨2138561, by rfl⟩ : syracuseStep 2851415 = 4277123) B4277123
theorem B1426027 : Blo 1266451 1426027 := bstep (se 1 (by rfl) ⟨1069520, by rfl⟩ : syracuseStep 1426027 = 2139041) B2139041
theorem B7815811 : Blo 1266451 7815811 := bstep (se 1 (by rfl) ⟨5861858, by rfl⟩ : syracuseStep 7815811 = 11723717) B11723717
theorem B1901195 : Blo 1266451 1901195 := bstep (se 1 (by rfl) ⟨1425896, by rfl⟩ : syracuseStep 1901195 = 2851793) B2851793
theorem B1901207 : Blo 1266451 1901207 := bstep (se 1 (by rfl) ⟨1425905, by rfl⟩ : syracuseStep 1901207 = 2851811) B2851811
theorem B4809395 : Blo 1266451 4809395 := bstep (se 1 (by rfl) ⟨3607046, by rfl⟩ : syracuseStep 4809395 = 7214093) B7214093
theorem B1426135 : Blo 1266451 1426135 := bstep (se 1 (by rfl) ⟨1069601, by rfl⟩ : syracuseStep 1426135 = 2139203) B2139203
theorem B1901273 : Blo 1266451 1901273 := bstep (se 2 (by rfl) ⟨712977, by rfl⟩ : syracuseStep 1901273 = 1425955) B1425955
theorem B2851595 : Blo 1266451 2851595 := bstep (se 1 (by rfl) ⟨2138696, by rfl⟩ : syracuseStep 2851595 = 4277393) B4277393
theorem B4277015 : Blo 1266451 4277015 := bstep (se 1 (by rfl) ⟨3207761, by rfl⟩ : syracuseStep 4277015 = 6415523) B6415523
theorem B6087469 : Blo 1266451 6087469 := bstep (se 3 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 6087469 = 2282801) B2282801
theorem B5415731 : Blo 1266451 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B4875073 : Blo 1266451 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B2851649 : Blo 1266451 2851649 := bstep (se 2 (by rfl) ⟨1069368, by rfl⟩ : syracuseStep 2851649 = 2138737) B2138737
theorem B1901387 : Blo 1266451 1901387 := bstep (se 1 (by rfl) ⟨1426040, by rfl⟩ : syracuseStep 1901387 = 2852081) B2852081
theorem B1901399 : Blo 1266451 1901399 := bstep (se 1 (by rfl) ⟨1426049, by rfl⟩ : syracuseStep 1901399 = 2852099) B2852099
theorem B1426315 : Blo 1266451 1426315 := bstep (se 1 (by rfl) ⟨1069736, by rfl⟩ : syracuseStep 1426315 = 2139473) B2139473
theorem B1901465 : Blo 1266451 1901465 := bstep (se 2 (by rfl) ⟨713049, by rfl⟩ : syracuseStep 1901465 = 1426099) B1426099
theorem B2139095 : Blo 1266451 2139095 := bstep (se 1 (by rfl) ⟨1604321, by rfl⟩ : syracuseStep 2139095 = 3208643) B3208643
theorem B9135065 : Blo 1266451 9135065 := bstep (se 2 (by rfl) ⟨3425649, by rfl⟩ : syracuseStep 9135065 = 6851299) B6851299
theorem B1426423 : Blo 1266451 1426423 := bstep (se 1 (by rfl) ⟨1069817, by rfl⟩ : syracuseStep 1426423 = 2139635) B2139635
theorem B1901579 : Blo 1266451 1901579 := bstep (se 1 (by rfl) ⟨1426184, by rfl⟩ : syracuseStep 1901579 = 2852369) B2852369
theorem B7218193 : Blo 1266451 7218193 := bstep (se 2 (by rfl) ⟨2706822, by rfl⟩ : syracuseStep 7218193 = 5413645) B5413645
theorem B1901591 : Blo 1266451 1901591 := bstep (se 1 (by rfl) ⟨1426193, by rfl⟩ : syracuseStep 1901591 = 2852387) B2852387
theorem B2851865 : Blo 1266451 2851865 := bstep (se 2 (by rfl) ⟨1069449, by rfl⟩ : syracuseStep 2851865 = 2138899) B2138899
theorem B2139223 : Blo 1266451 2139223 := bstep (se 1 (by rfl) ⟨1604417, by rfl⟩ : syracuseStep 2139223 = 3208835) B3208835
theorem B1901657 : Blo 1266451 1901657 := bstep (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) B1426243
theorem B2851955 : Blo 1266451 2851955 := bstep (se 1 (by rfl) ⟨2138966, by rfl⟩ : syracuseStep 2851955 = 4277933) B4277933
theorem B2851991 : Blo 1266451 2851991 := bstep (se 1 (by rfl) ⟨2138993, by rfl⟩ : syracuseStep 2851991 = 4277987) B4277987
theorem B1426603 : Blo 1266451 1426603 := bstep (se 1 (by rfl) ⟨1069952, by rfl⟩ : syracuseStep 1426603 = 2139905) B2139905
theorem B1901771 : Blo 1266451 1901771 := bstep (se 1 (by rfl) ⟨1426328, by rfl⟩ : syracuseStep 1901771 = 2852657) B2852657
theorem B1901783 : Blo 1266451 1901783 := bstep (se 1 (by rfl) ⟨1426337, by rfl⟩ : syracuseStep 1901783 = 2852675) B2852675
theorem B1713431 : Blo 1266451 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B1426711 : Blo 1266451 1426711 := bstep (se 1 (by rfl) ⟨1070033, by rfl⟩ : syracuseStep 1426711 = 2140067) B2140067
theorem B1901849 : Blo 1266451 1901849 := bstep (se 2 (by rfl) ⟨713193, by rfl⟩ : syracuseStep 1901849 = 1426387) B1426387
theorem B4277555 : Blo 1266451 4277555 := bstep (se 1 (by rfl) ⟨3208166, by rfl⟩ : syracuseStep 4277555 = 6416333) B6416333
theorem B4810049 : Blo 1266451 4810049 := bstep (se 2 (by rfl) ⟨1803768, by rfl⟩ : syracuseStep 4810049 = 3607537) B3607537
theorem B2852171 : Blo 1266451 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B2852225 : Blo 1266451 2852225 := bstep (se 2 (by rfl) ⟨1069584, by rfl⟩ : syracuseStep 2852225 = 2139169) B2139169
theorem B1901963 : Blo 1266451 1901963 := bstep (se 1 (by rfl) ⟨1426472, by rfl⟩ : syracuseStep 1901963 = 2852945) B2852945
theorem B2196887 : Blo 1266451 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1901975 : Blo 1266451 1901975 := bstep (se 1 (by rfl) ⟨1426481, by rfl⟩ : syracuseStep 1901975 = 2852963) B2852963
theorem B1426891 : Blo 1266451 1426891 := bstep (se 1 (by rfl) ⟨1070168, by rfl⟩ : syracuseStep 1426891 = 2140337) B2140337
theorem B1902041 : Blo 1266451 1902041 := bstep (se 2 (by rfl) ⟨713265, by rfl⟩ : syracuseStep 1902041 = 1426531) B1426531
theorem B6178265 : Blo 1266451 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B1426999 : Blo 1266451 1426999 := bstep (se 1 (by rfl) ⟨1070249, by rfl⟩ : syracuseStep 1426999 = 2140499) B2140499
theorem B4277825 : Blo 1266451 4277825 := bstep (se 2 (by rfl) ⟨1604184, by rfl⟩ : syracuseStep 4277825 = 3208369) B3208369
theorem B1902155 : Blo 1266451 1902155 := bstep (se 1 (by rfl) ⟨1426616, by rfl⟩ : syracuseStep 1902155 = 2853233) B2853233
theorem B1902167 : Blo 1266451 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B1803865 : Blo 1266451 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B2852441 : Blo 1266451 2852441 := bstep (se 2 (by rfl) ⟨1069665, by rfl⟩ : syracuseStep 2852441 = 2139331) B2139331
theorem B24364637 : Blo 1266451 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B24356483 : Blo 1266451 24356483 := bstep (se 1 (by rfl) ⟨18267362, by rfl⟩ : syracuseStep 24356483 = 36534725) B36534725
theorem B1902233 : Blo 1266451 1902233 := bstep (se 2 (by rfl) ⟨713337, by rfl⟩ : syracuseStep 1902233 = 1426675) B1426675
theorem B2852531 : Blo 1266451 2852531 := bstep (se 1 (by rfl) ⟨2139398, by rfl⟩ : syracuseStep 2852531 = 4278797) B4278797
theorem B1803979 : Blo 1266451 1803979 := bstep (se 1 (by rfl) ⟨1352984, by rfl⟩ : syracuseStep 1803979 = 2705969) B2705969
theorem B2139851 : Blo 1266451 2139851 := bstep (se 1 (by rfl) ⟨1604888, by rfl⟩ : syracuseStep 2139851 = 3209777) B3209777
theorem B2852567 : Blo 1266451 2852567 := bstep (se 1 (by rfl) ⟨2139425, by rfl⟩ : syracuseStep 2852567 = 4278851) B4278851
theorem B7317209 : Blo 1266451 7317209 := bstep (se 2 (by rfl) ⟨2743953, by rfl⟩ : syracuseStep 7317209 = 5487907) B5487907
theorem B1902347 : Blo 1266451 1902347 := bstep (se 1 (by rfl) ⟨1426760, by rfl⟩ : syracuseStep 1902347 = 2853521) B2853521
theorem B1902359 : Blo 1266451 1902359 := bstep (se 1 (by rfl) ⟨1426769, by rfl⟩ : syracuseStep 1902359 = 2853539) B2853539
theorem B2139979 : Blo 1266451 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B1902425 : Blo 1266451 1902425 := bstep (se 2 (by rfl) ⟨713409, by rfl⟩ : syracuseStep 1902425 = 1426819) B1426819
theorem B14444405 : Blo 1266451 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B2852747 : Blo 1266451 2852747 := bstep (se 1 (by rfl) ⟨2139560, by rfl⟩ : syracuseStep 2852747 = 4279121) B4279121
theorem B2852801 : Blo 1266451 2852801 := bstep (se 2 (by rfl) ⟨1069800, by rfl⟩ : syracuseStep 2852801 = 2139601) B2139601
theorem B1902539 : Blo 1266451 1902539 := bstep (se 1 (by rfl) ⟨1426904, by rfl⟩ : syracuseStep 1902539 = 2853809) B2853809
theorem B1902551 : Blo 1266451 1902551 := bstep (se 1 (by rfl) ⟨1426913, by rfl⟩ : syracuseStep 1902551 = 2853827) B2853827
theorem B2140121 : Blo 1266451 2140121 := bstep (se 2 (by rfl) ⟨802545, by rfl⟩ : syracuseStep 2140121 = 1605091) B1605091
theorem B1353719 : Blo 1266451 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B1902617 : Blo 1266451 1902617 := bstep (se 2 (by rfl) ⟨713481, by rfl⟩ : syracuseStep 1902617 = 1426963) B1426963
theorem B2140249 : Blo 1266451 2140249 := bstep (se 2 (by rfl) ⟨802593, by rfl⟩ : syracuseStep 2140249 = 1605187) B1605187
theorem B4278365 : Blo 1266451 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B3254423 : Blo 1266451 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B2853017 : Blo 1266451 2853017 := bstep (se 2 (by rfl) ⟨1069881, by rfl⟩ : syracuseStep 2853017 = 2139763) B2139763
theorem B2853107 : Blo 1266451 2853107 := bstep (se 1 (by rfl) ⟨2139830, by rfl⟩ : syracuseStep 2853107 = 4279661) B4279661
theorem B6416657 : Blo 1266451 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B2853143 : Blo 1266451 2853143 := bstep (se 1 (by rfl) ⟨2139857, by rfl⟩ : syracuseStep 2853143 = 4279715) B4279715
theorem B2705729 : Blo 1266451 2705729 := bstep (se 2 (by rfl) ⟨1014648, by rfl⟩ : syracuseStep 2705729 = 2029297) B2029297
theorem B2705815 : Blo 1266451 2705815 := bstep (se 1 (by rfl) ⟨2029361, by rfl⟩ : syracuseStep 2705815 = 4058723) B4058723
theorem B6416819 : Blo 1266451 6416819 := bstep (se 1 (by rfl) ⟨4812614, by rfl⟩ : syracuseStep 6416819 = 9625229) B9625229
theorem B2853323 : Blo 1266451 2853323 := bstep (se 1 (by rfl) ⟨2139992, by rfl⟩ : syracuseStep 2853323 = 4279985) B4279985
theorem B3607001 : Blo 1266451 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B2853377 : Blo 1266451 2853377 := bstep (se 2 (by rfl) ⟨1070016, by rfl⟩ : syracuseStep 2853377 = 2140033) B2140033
theorem B4811309 : Blo 1266451 4811309 := bstep (se 3 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 4811309 = 1804241) B1804241
theorem B5777995 : Blo 1266451 5777995 := bstep (se 1 (by rfl) ⟨4333496, by rfl⟩ : syracuseStep 5777995 = 8666993) B8666993
theorem B4811339 : Blo 1266451 4811339 := bstep (se 1 (by rfl) ⟨3608504, by rfl⟩ : syracuseStep 4811339 = 7217009) B7217009
theorem B5778013 : Blo 1266451 5778013 := bstep (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) B2166755
theorem B9751133 : Blo 1266451 9751133 := bstep (se 3 (by rfl) ⟨1828337, by rfl⟩ : syracuseStep 9751133 = 3656675) B3656675
theorem B1354411 : Blo 1266451 1354411 := bstep (se 1 (by rfl) ⟨1015808, by rfl⟩ : syracuseStep 1354411 = 2031617) B2031617
theorem B2853593 : Blo 1266451 2853593 := bstep (se 2 (by rfl) ⟨1070097, by rfl⟩ : syracuseStep 2853593 = 2140195) B2140195
theorem B3853079 : Blo 1266451 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B3205939 : Blo 1266451 3205939 := bstep (se 1 (by rfl) ⟨2404454, by rfl⟩ : syracuseStep 3205939 = 4808909) B4808909
theorem B2853683 : Blo 1266451 2853683 := bstep (se 1 (by rfl) ⟨2140262, by rfl⟩ : syracuseStep 2853683 = 4280525) B4280525
theorem B2853719 : Blo 1266451 2853719 := bstep (se 1 (by rfl) ⟨2140289, by rfl⟩ : syracuseStep 2853719 = 4280579) B4280579
theorem B3206081 : Blo 1266451 3206081 := bstep (se 2 (by rfl) ⟨1202280, by rfl⟩ : syracuseStep 3206081 = 2404561) B2404561
theorem B11725829 : Blo 1266451 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B1805323 : Blo 1266451 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B2853899 : Blo 1266451 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B2853953 : Blo 1266451 2853953 := bstep (se 2 (by rfl) ⟨1070232, by rfl⟩ : syracuseStep 2853953 = 2140465) B2140465
theorem B1928267 : Blo 1266451 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B8342621 : Blo 1266451 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B6851735 : Blo 1266451 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B2706635 : Blo 1266451 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B4279499 : Blo 1266451 4279499 := bstep (se 1 (by rfl) ⟨3209624, by rfl⟩ : syracuseStep 4279499 = 6419249) B6419249
theorem B10833101 : Blo 1266451 10833101 := bstep (se 3 (by rfl) ⟨2031206, by rfl⟩ : syracuseStep 10833101 = 4062413) B4062413
theorem B4811993 : Blo 1266451 4811993 := bstep (se 2 (by rfl) ⟨1804497, by rfl⟩ : syracuseStep 4811993 = 3608995) B3608995
theorem B1805591 : Blo 1266451 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B7810405 : Blo 1266451 7810405 := bstep (se 4 (by rfl) ⟨732225, by rfl⟩ : syracuseStep 7810405 = 1464451) B1464451
theorem B4279769 : Blo 1266451 4279769 := bstep (se 2 (by rfl) ⟨1604913, by rfl⟩ : syracuseStep 4279769 = 3209827) B3209827
theorem B2567681 : Blo 1266451 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B4812311 : Blo 1266451 4812311 := bstep (se 1 (by rfl) ⟨3609233, by rfl⟩ : syracuseStep 4812311 = 7218467) B7218467
theorem B20844067 : Blo 1266451 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B105557701 : Blo 1266451 105557701 := bstep (se 4 (by rfl) ⟨9896034, by rfl⟩ : syracuseStep 105557701 = 19792069) B19792069
theorem B9621341 : Blo 1266451 9621341 := bstep (se 3 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 9621341 = 3608003) B3608003
theorem B31272803 : Blo 1266451 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B4059031 : Blo 1266451 4059031 := bstep (se 1 (by rfl) ⟨3044273, by rfl⟩ : syracuseStep 4059031 = 6088547) B6088547
theorem B7319447 : Blo 1266451 7319447 := bstep (se 1 (by rfl) ⟨5489585, by rfl⟩ : syracuseStep 7319447 = 10979171) B10979171
theorem B2404417 : Blo 1266451 2404417 := bstep (se 2 (by rfl) ⟨901656, by rfl⟩ : syracuseStep 2404417 = 1803313) B1803313
theorem B3608641 : Blo 1266451 3608641 := bstep (se 2 (by rfl) ⟨1353240, by rfl⟩ : syracuseStep 3608641 = 2706481) B2706481
theorem B4280471 : Blo 1266451 4280471 := bstep (se 1 (by rfl) ⟨3210353, by rfl⟩ : syracuseStep 4280471 = 6420707) B6420707
theorem B2707609 : Blo 1266451 2707609 := bstep (se 2 (by rfl) ⟨1015353, by rfl⟩ : syracuseStep 2707609 = 2030707) B2030707
theorem B3207347 : Blo 1266451 3207347 := bstep (se 1 (by rfl) ⟨2405510, by rfl⟩ : syracuseStep 3207347 = 4811021) B4811021
theorem B4812979 : Blo 1266451 4812979 := bstep (se 1 (by rfl) ⟨3609734, by rfl⟩ : syracuseStep 4812979 = 7219469) B7219469
theorem B5411033 : Blo 1266451 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B5411117 : Blo 1266451 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B5779763 : Blo 1266451 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B4059467 : Blo 1266451 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B6418763 : Blo 1266451 6418763 := bstep (se 1 (by rfl) ⟨4814072, by rfl⟩ : syracuseStep 6418763 = 9628145) B9628145
theorem B7221635 : Blo 1266451 7221635 := bstep (se 1 (by rfl) ⟨5416226, by rfl⟩ : syracuseStep 7221635 = 10832453) B10832453
theorem B2404865 : Blo 1266451 2404865 := bstep (se 2 (by rfl) ⟨901824, by rfl⟩ : syracuseStep 2404865 = 1803649) B1803649
theorem B1626647 : Blo 1266451 1626647 := bstep (se 1 (by rfl) ⟨1219985, by rfl⟩ : syracuseStep 1626647 = 2439971) B2439971
theorem B4281011 : Blo 1266451 4281011 := bstep (se 1 (by rfl) ⟨3210758, by rfl⟩ : syracuseStep 4281011 = 6421517) B6421517
theorem B3207883 : Blo 1266451 3207883 := bstep (se 1 (by rfl) ⟨2405912, by rfl⟩ : syracuseStep 3207883 = 4811825) B4811825
theorem B1266455 : Blo 1266451 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B1266475 : Blo 1266451 1266475 := bstep (se 1 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 1266475 = 1899713) B1899713
theorem B1266487 : Blo 1266451 1266487 := bstep (se 1 (by rfl) ⟨949865, by rfl⟩ : syracuseStep 1266487 = 1899731) B1899731
theorem B1266507 : Blo 1266451 1266507 := bstep (se 1 (by rfl) ⟨949880, by rfl⟩ : syracuseStep 1266507 = 1899761) B1899761
theorem B1266519 : Blo 1266451 1266519 := bstep (se 1 (by rfl) ⟨949889, by rfl⟩ : syracuseStep 1266519 = 1899779) B1899779
theorem B2405207 : Blo 1266451 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B3208025 : Blo 1266451 3208025 := bstep (se 2 (by rfl) ⟨1203009, by rfl⟩ : syracuseStep 3208025 = 2406019) B2406019
theorem B8123237 : Blo 1266451 8123237 := bstep (se 4 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 8123237 = 1523107) B1523107
theorem B1266539 : Blo 1266451 1266539 := bstep (se 1 (by rfl) ⟨949904, by rfl⟩ : syracuseStep 1266539 = 1899809) B1899809
theorem B1266551 : Blo 1266451 1266551 := bstep (se 1 (by rfl) ⟨949913, by rfl⟩ : syracuseStep 1266551 = 1899827) B1899827
theorem B1266571 : Blo 1266451 1266571 := bstep (se 1 (by rfl) ⟨949928, by rfl⟩ : syracuseStep 1266571 = 1899857) B1899857
theorem B1266583 : Blo 1266451 1266583 := bstep (se 1 (by rfl) ⟨949937, by rfl⟩ : syracuseStep 1266583 = 1899875) B1899875
theorem B2315159 : Blo 1266451 2315159 := bstep (se 1 (by rfl) ⟨1736369, by rfl⟩ : syracuseStep 2315159 = 3472739) B3472739
theorem B1266603 : Blo 1266451 1266603 := bstep (se 1 (by rfl) ⟨949952, by rfl⟩ : syracuseStep 1266603 = 1899905) B1899905
theorem B1266615 : Blo 1266451 1266615 := bstep (se 1 (by rfl) ⟨949961, by rfl⟩ : syracuseStep 1266615 = 1899923) B1899923
theorem B1266635 : Blo 1266451 1266635 := bstep (se 1 (by rfl) ⟨949976, by rfl⟩ : syracuseStep 1266635 = 1899953) B1899953
theorem B1266647 : Blo 1266451 1266647 := bstep (se 1 (by rfl) ⟨949985, by rfl⟩ : syracuseStep 1266647 = 1899971) B1899971
theorem B1266667 : Blo 1266451 1266667 := bstep (se 1 (by rfl) ⟨950000, by rfl⟩ : syracuseStep 1266667 = 1900001) B1900001
theorem B1266679 : Blo 1266451 1266679 := bstep (se 1 (by rfl) ⟨950009, by rfl⟩ : syracuseStep 1266679 = 1900019) B1900019
theorem B1266699 : Blo 1266451 1266699 := bstep (se 1 (by rfl) ⟨950024, by rfl⟩ : syracuseStep 1266699 = 1900049) B1900049
theorem B20542481 : Blo 1266451 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B1266711 : Blo 1266451 1266711 := bstep (se 1 (by rfl) ⟨950033, by rfl⟩ : syracuseStep 1266711 = 1900067) B1900067
theorem B1266731 : Blo 1266451 1266731 := bstep (se 1 (by rfl) ⟨950048, by rfl⟩ : syracuseStep 1266731 = 1900097) B1900097
theorem B1266743 : Blo 1266451 1266743 := bstep (se 1 (by rfl) ⟨950057, by rfl⟩ : syracuseStep 1266743 = 1900115) B1900115
theorem B1266763 : Blo 1266451 1266763 := bstep (se 1 (by rfl) ⟨950072, by rfl⟩ : syracuseStep 1266763 = 1900145) B1900145
theorem B2028631 : Blo 1266451 2028631 := bstep (se 1 (by rfl) ⟨1521473, by rfl⟩ : syracuseStep 2028631 = 3042947) B3042947
theorem B1266775 : Blo 1266451 1266775 := bstep (se 1 (by rfl) ⟨950081, by rfl⟩ : syracuseStep 1266775 = 1900163) B1900163
theorem B1266795 : Blo 1266451 1266795 := bstep (se 1 (by rfl) ⟨950096, by rfl⟩ : syracuseStep 1266795 = 1900193) B1900193
theorem B1266807 : Blo 1266451 1266807 := bstep (se 1 (by rfl) ⟨950105, by rfl⟩ : syracuseStep 1266807 = 1900211) B1900211
theorem B1266827 : Blo 1266451 1266827 := bstep (se 1 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 1266827 = 1900241) B1900241
theorem B1266839 : Blo 1266451 1266839 := bstep (se 1 (by rfl) ⟨950129, by rfl⟩ : syracuseStep 1266839 = 1900259) B1900259
theorem B8344727 : Blo 1266451 8344727 := bstep (se 1 (by rfl) ⟨6258545, by rfl⟩ : syracuseStep 8344727 = 12517091) B12517091
theorem B1266859 : Blo 1266451 1266859 := bstep (se 1 (by rfl) ⟨950144, by rfl⟩ : syracuseStep 1266859 = 1900289) B1900289
theorem B9761971 : Blo 1266451 9761971 := bstep (se 1 (by rfl) ⟨7321478, by rfl⟩ : syracuseStep 9761971 = 14642957) B14642957
theorem B1266871 : Blo 1266451 1266871 := bstep (se 1 (by rfl) ⟨950153, by rfl⟩ : syracuseStep 1266871 = 1900307) B1900307
theorem B1266891 : Blo 1266451 1266891 := bstep (se 1 (by rfl) ⟨950168, by rfl⟩ : syracuseStep 1266891 = 1900337) B1900337
theorem B4060363 : Blo 1266451 4060363 := bstep (se 1 (by rfl) ⟨3045272, by rfl⟩ : syracuseStep 4060363 = 6090545) B6090545
theorem B1266903 : Blo 1266451 1266903 := bstep (se 1 (by rfl) ⟨950177, by rfl⟩ : syracuseStep 1266903 = 1900355) B1900355
theorem B1266923 : Blo 1266451 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B1266935 : Blo 1266451 1266935 := bstep (se 1 (by rfl) ⟨950201, by rfl⟩ : syracuseStep 1266935 = 1900403) B1900403
theorem B1266955 : Blo 1266451 1266955 := bstep (se 1 (by rfl) ⟨950216, by rfl⟩ : syracuseStep 1266955 = 1900433) B1900433
theorem B1266967 : Blo 1266451 1266967 := bstep (se 1 (by rfl) ⟨950225, by rfl⟩ : syracuseStep 1266967 = 1900451) B1900451
theorem B1266987 : Blo 1266451 1266987 := bstep (se 1 (by rfl) ⟨950240, by rfl⟩ : syracuseStep 1266987 = 1900481) B1900481
theorem B1266999 : Blo 1266451 1266999 := bstep (se 1 (by rfl) ⟨950249, by rfl⟩ : syracuseStep 1266999 = 1900499) B1900499
theorem B21960001 : Blo 1266451 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B1267019 : Blo 1266451 1267019 := bstep (se 1 (by rfl) ⟨950264, by rfl⟩ : syracuseStep 1267019 = 1900529) B1900529
theorem B1267031 : Blo 1266451 1267031 := bstep (se 1 (by rfl) ⟨950273, by rfl⟩ : syracuseStep 1267031 = 1900547) B1900547
theorem B1267051 : Blo 1266451 1267051 := bstep (se 1 (by rfl) ⟨950288, by rfl⟩ : syracuseStep 1267051 = 1900577) B1900577
theorem B1267063 : Blo 1266451 1267063 := bstep (se 1 (by rfl) ⟨950297, by rfl⟩ : syracuseStep 1267063 = 1900595) B1900595
theorem B1267083 : Blo 1266451 1267083 := bstep (se 1 (by rfl) ⟨950312, by rfl⟩ : syracuseStep 1267083 = 1900625) B1900625
theorem B4814225 : Blo 1266451 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B1267095 : Blo 1266451 1267095 := bstep (se 1 (by rfl) ⟨950321, by rfl⟩ : syracuseStep 1267095 = 1900643) B1900643
theorem B1267115 : Blo 1266451 1267115 := bstep (se 1 (by rfl) ⟨950336, by rfl⟩ : syracuseStep 1267115 = 1900673) B1900673
theorem B2438579 : Blo 1266451 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B1267127 : Blo 1266451 1267127 := bstep (se 1 (by rfl) ⟨950345, by rfl⟩ : syracuseStep 1267127 = 1900691) B1900691
theorem B1267147 : Blo 1266451 1267147 := bstep (se 1 (by rfl) ⟨950360, by rfl⟩ : syracuseStep 1267147 = 1900721) B1900721
theorem B1267159 : Blo 1266451 1267159 := bstep (se 1 (by rfl) ⟨950369, by rfl⟩ : syracuseStep 1267159 = 1900739) B1900739
theorem B1267179 : Blo 1266451 1267179 := bstep (se 1 (by rfl) ⟨950384, by rfl⟩ : syracuseStep 1267179 = 1900769) B1900769
theorem B2405875 : Blo 1266451 2405875 := bstep (se 1 (by rfl) ⟨1804406, by rfl⟩ : syracuseStep 2405875 = 3608813) B3608813
theorem B1267191 : Blo 1266451 1267191 := bstep (se 1 (by rfl) ⟨950393, by rfl⟩ : syracuseStep 1267191 = 1900787) B1900787
theorem B2029067 : Blo 1266451 2029067 := bstep (se 1 (by rfl) ⟨1521800, by rfl⟩ : syracuseStep 2029067 = 3043601) B3043601
theorem B1267211 : Blo 1266451 1267211 := bstep (se 1 (by rfl) ⟨950408, by rfl⟩ : syracuseStep 1267211 = 1900817) B1900817
theorem B1267223 : Blo 1266451 1267223 := bstep (se 1 (by rfl) ⟨950417, by rfl⟩ : syracuseStep 1267223 = 1900835) B1900835
theorem B10835491 : Blo 1266451 10835491 := bstep (se 1 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 10835491 = 16253237) B16253237
theorem B1267243 : Blo 1266451 1267243 := bstep (se 1 (by rfl) ⟨950432, by rfl⟩ : syracuseStep 1267243 = 1900865) B1900865
theorem B1267255 : Blo 1266451 1267255 := bstep (se 1 (by rfl) ⟨950441, by rfl⟩ : syracuseStep 1267255 = 1900883) B1900883
theorem B10270273 : Blo 1266451 10270273 := bstep (se 2 (by rfl) ⟨3851352, by rfl⟩ : syracuseStep 10270273 = 7702705) B7702705
theorem B1603147 : Blo 1266451 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1267275 : Blo 1266451 1267275 := bstep (se 1 (by rfl) ⟨950456, by rfl⟩ : syracuseStep 1267275 = 1900913) B1900913
theorem B11130443 : Blo 1266451 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B1267287 : Blo 1266451 1267287 := bstep (se 1 (by rfl) ⟨950465, by rfl⟩ : syracuseStep 1267287 = 1900931) B1900931
theorem B1267307 : Blo 1266451 1267307 := bstep (se 1 (by rfl) ⟨950480, by rfl⟩ : syracuseStep 1267307 = 1900961) B1900961
theorem B1267319 : Blo 1266451 1267319 := bstep (se 1 (by rfl) ⟨950489, by rfl⟩ : syracuseStep 1267319 = 1900979) B1900979
theorem B1267339 : Blo 1266451 1267339 := bstep (se 1 (by rfl) ⟨950504, by rfl⟩ : syracuseStep 1267339 = 1901009) B1901009
theorem B1267351 : Blo 1266451 1267351 := bstep (se 1 (by rfl) ⟨950513, by rfl⟩ : syracuseStep 1267351 = 1901027) B1901027
theorem B3208855 : Blo 1266451 3208855 := bstep (se 1 (by rfl) ⟨2406641, by rfl⟩ : syracuseStep 3208855 = 4813283) B4813283
theorem B1267371 : Blo 1266451 1267371 := bstep (se 1 (by rfl) ⟨950528, by rfl⟩ : syracuseStep 1267371 = 1901057) B1901057
theorem B1267383 : Blo 1266451 1267383 := bstep (se 1 (by rfl) ⟨950537, by rfl⟩ : syracuseStep 1267383 = 1901075) B1901075
theorem B2029259 : Blo 1266451 2029259 := bstep (se 1 (by rfl) ⟨1521944, by rfl⟩ : syracuseStep 2029259 = 3043889) B3043889
theorem B1267403 : Blo 1266451 1267403 := bstep (se 1 (by rfl) ⟨950552, by rfl⟩ : syracuseStep 1267403 = 1901105) B1901105
theorem B1267415 : Blo 1266451 1267415 := bstep (se 1 (by rfl) ⟨950561, by rfl⟩ : syracuseStep 1267415 = 1901123) B1901123
theorem B9885401 : Blo 1266451 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B1267435 : Blo 1266451 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B1267447 : Blo 1266451 1267447 := bstep (se 1 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 1267447 = 1901171) B1901171
theorem B1267467 : Blo 1266451 1267467 := bstep (se 1 (by rfl) ⟨950600, by rfl⟩ : syracuseStep 1267467 = 1901201) B1901201
theorem B1267479 : Blo 1266451 1267479 := bstep (se 1 (by rfl) ⟨950609, by rfl⟩ : syracuseStep 1267479 = 1901219) B1901219
theorem B1267499 : Blo 1266451 1267499 := bstep (se 1 (by rfl) ⟨950624, by rfl⟩ : syracuseStep 1267499 = 1901249) B1901249
theorem B4060979 : Blo 1266451 4060979 := bstep (se 1 (by rfl) ⟨3045734, by rfl⟩ : syracuseStep 4060979 = 6091469) B6091469
theorem B1267511 : Blo 1266451 1267511 := bstep (se 1 (by rfl) ⟨950633, by rfl⟩ : syracuseStep 1267511 = 1901267) B1901267
theorem B10270529 : Blo 1266451 10270529 := bstep (se 2 (by rfl) ⟨3851448, by rfl⟩ : syracuseStep 10270529 = 7702897) B7702897
theorem B1267531 : Blo 1266451 1267531 := bstep (se 1 (by rfl) ⟨950648, by rfl⟩ : syracuseStep 1267531 = 1901297) B1901297
theorem B1603415 : Blo 1266451 1603415 := bstep (se 1 (by rfl) ⟨1202561, by rfl⟩ : syracuseStep 1603415 = 2405123) B2405123
theorem B1267543 : Blo 1266451 1267543 := bstep (se 1 (by rfl) ⟨950657, by rfl⟩ : syracuseStep 1267543 = 1901315) B1901315
theorem B1267563 : Blo 1266451 1267563 := bstep (se 1 (by rfl) ⟨950672, by rfl⟩ : syracuseStep 1267563 = 1901345) B1901345
theorem B1267575 : Blo 1266451 1267575 := bstep (se 1 (by rfl) ⟨950681, by rfl⟩ : syracuseStep 1267575 = 1901363) B1901363
theorem B1267595 : Blo 1266451 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B1267607 : Blo 1266451 1267607 := bstep (se 1 (by rfl) ⟨950705, by rfl⟩ : syracuseStep 1267607 = 1901411) B1901411
theorem B1267627 : Blo 1266451 1267627 := bstep (se 1 (by rfl) ⟨950720, by rfl⟩ : syracuseStep 1267627 = 1901441) B1901441
theorem B2406323 : Blo 1266451 2406323 := bstep (se 1 (by rfl) ⟨1804742, by rfl⟩ : syracuseStep 2406323 = 3609485) B3609485
theorem B1267639 : Blo 1266451 1267639 := bstep (se 1 (by rfl) ⟨950729, by rfl⟩ : syracuseStep 1267639 = 1901459) B1901459
theorem B1267659 : Blo 1266451 1267659 := bstep (se 1 (by rfl) ⟨950744, by rfl⟩ : syracuseStep 1267659 = 1901489) B1901489
theorem B2283479 : Blo 1266451 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B1267671 : Blo 1266451 1267671 := bstep (se 1 (by rfl) ⟨950753, by rfl⟩ : syracuseStep 1267671 = 1901507) B1901507
theorem B2406361 : Blo 1266451 2406361 := bstep (se 2 (by rfl) ⟨902385, by rfl⟩ : syracuseStep 2406361 = 1804771) B1804771
theorem B1267691 : Blo 1266451 1267691 := bstep (se 1 (by rfl) ⟨950768, by rfl⟩ : syracuseStep 1267691 = 1901537) B1901537
theorem B1267703 : Blo 1266451 1267703 := bstep (se 1 (by rfl) ⟨950777, by rfl⟩ : syracuseStep 1267703 = 1901555) B1901555
theorem B1267723 : Blo 1266451 1267723 := bstep (se 1 (by rfl) ⟨950792, by rfl⟩ : syracuseStep 1267723 = 1901585) B1901585
theorem B1267735 : Blo 1266451 1267735 := bstep (se 1 (by rfl) ⟨950801, by rfl⟩ : syracuseStep 1267735 = 1901603) B1901603
theorem B1267755 : Blo 1266451 1267755 := bstep (se 1 (by rfl) ⟨950816, by rfl⟩ : syracuseStep 1267755 = 1901633) B1901633
theorem B1267767 : Blo 1266451 1267767 := bstep (se 1 (by rfl) ⟨950825, by rfl⟩ : syracuseStep 1267767 = 1901651) B1901651
theorem B4061249 : Blo 1266451 4061249 := bstep (se 2 (by rfl) ⟨1522968, by rfl⟩ : syracuseStep 4061249 = 3045937) B3045937
theorem B6420545 : Blo 1266451 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B1267787 : Blo 1266451 1267787 := bstep (se 1 (by rfl) ⟨950840, by rfl⟩ : syracuseStep 1267787 = 1901681) B1901681
theorem B3209291 : Blo 1266451 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B4814923 : Blo 1266451 4814923 := bstep (se 1 (by rfl) ⟨3611192, by rfl⟩ : syracuseStep 4814923 = 7222385) B7222385
theorem B1267799 : Blo 1266451 1267799 := bstep (se 1 (by rfl) ⟨950849, by rfl⟩ : syracuseStep 1267799 = 1901699) B1901699
theorem B1267819 : Blo 1266451 1267819 := bstep (se 1 (by rfl) ⟨950864, by rfl⟩ : syracuseStep 1267819 = 1901729) B1901729
theorem B1267831 : Blo 1266451 1267831 := bstep (se 1 (by rfl) ⟨950873, by rfl⟩ : syracuseStep 1267831 = 1901747) B1901747
theorem B1267851 : Blo 1266451 1267851 := bstep (se 1 (by rfl) ⟨950888, by rfl⟩ : syracuseStep 1267851 = 1901777) B1901777
theorem B1267863 : Blo 1266451 1267863 := bstep (se 1 (by rfl) ⟨950897, by rfl⟩ : syracuseStep 1267863 = 1901795) B1901795
theorem B1267883 : Blo 1266451 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1267895 : Blo 1266451 1267895 := bstep (se 1 (by rfl) ⟨950921, by rfl⟩ : syracuseStep 1267895 = 1901843) B1901843
theorem B4274369 : Blo 1266451 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B1267915 : Blo 1266451 1267915 := bstep (se 1 (by rfl) ⟨950936, by rfl⟩ : syracuseStep 1267915 = 1901873) B1901873
theorem B1267927 : Blo 1266451 1267927 := bstep (se 1 (by rfl) ⟨950945, by rfl⟩ : syracuseStep 1267927 = 1901891) B1901891
theorem B2439385 : Blo 1266451 2439385 := bstep (se 2 (by rfl) ⟨914769, by rfl⟩ : syracuseStep 2439385 = 1829539) B1829539
theorem B1267947 : Blo 1266451 1267947 := bstep (se 1 (by rfl) ⟨950960, by rfl⟩ : syracuseStep 1267947 = 1901921) B1901921
theorem B1267959 : Blo 1266451 1267959 := bstep (se 1 (by rfl) ⟨950969, by rfl⟩ : syracuseStep 1267959 = 1901939) B1901939
theorem B1267979 : Blo 1266451 1267979 := bstep (se 1 (by rfl) ⟨950984, by rfl⟩ : syracuseStep 1267979 = 1901969) B1901969
theorem B1267991 : Blo 1266451 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B1268011 : Blo 1266451 1268011 := bstep (se 1 (by rfl) ⟨951008, by rfl⟩ : syracuseStep 1268011 = 1902017) B1902017
theorem B1268023 : Blo 1266451 1268023 := bstep (se 1 (by rfl) ⟨951017, by rfl⟩ : syracuseStep 1268023 = 1902035) B1902035
theorem B1268043 : Blo 1266451 1268043 := bstep (se 1 (by rfl) ⟨951032, by rfl⟩ : syracuseStep 1268043 = 1902065) B1902065
theorem B1268055 : Blo 1266451 1268055 := bstep (se 1 (by rfl) ⟨951041, by rfl⟩ : syracuseStep 1268055 = 1902083) B1902083
theorem B3856729 : Blo 1266451 3856729 := bstep (se 2 (by rfl) ⟨1446273, by rfl⟩ : syracuseStep 3856729 = 2892547) B2892547
theorem B4815197 : Blo 1266451 4815197 := bstep (se 3 (by rfl) ⟨902849, by rfl⟩ : syracuseStep 4815197 = 1805699) B1805699
theorem B1268075 : Blo 1266451 1268075 := bstep (se 1 (by rfl) ⟨951056, by rfl⟩ : syracuseStep 1268075 = 1902113) B1902113
theorem B1268087 : Blo 1266451 1268087 := bstep (se 1 (by rfl) ⟨951065, by rfl⟩ : syracuseStep 1268087 = 1902131) B1902131
theorem B1268107 : Blo 1266451 1268107 := bstep (se 1 (by rfl) ⟨951080, by rfl⟩ : syracuseStep 1268107 = 1902161) B1902161
theorem B1268119 : Blo 1266451 1268119 := bstep (se 1 (by rfl) ⟨951089, by rfl⟩ : syracuseStep 1268119 = 1902179) B1902179
theorem B2406809 : Blo 1266451 2406809 := bstep (se 2 (by rfl) ⟨902553, by rfl⟩ : syracuseStep 2406809 = 1805107) B1805107
theorem B1268139 : Blo 1266451 1268139 := bstep (se 1 (by rfl) ⟨951104, by rfl⟩ : syracuseStep 1268139 = 1902209) B1902209
theorem B12188083 : Blo 1266451 12188083 := bstep (se 1 (by rfl) ⟨9141062, by rfl⟩ : syracuseStep 12188083 = 18282125) B18282125
theorem B1268151 : Blo 1266451 1268151 := bstep (se 1 (by rfl) ⟨951113, by rfl⟩ : syracuseStep 1268151 = 1902227) B1902227
theorem B3209665 : Blo 1266451 3209665 := bstep (se 2 (by rfl) ⟨1203624, by rfl⟩ : syracuseStep 3209665 = 2407249) B2407249
theorem B1268171 : Blo 1266451 1268171 := bstep (se 1 (by rfl) ⟨951128, by rfl⟩ : syracuseStep 1268171 = 1902257) B1902257
theorem B1268183 : Blo 1266451 1268183 := bstep (se 1 (by rfl) ⟨951137, by rfl⟩ : syracuseStep 1268183 = 1902275) B1902275
theorem B1268203 : Blo 1266451 1268203 := bstep (se 1 (by rfl) ⟨951152, by rfl⟩ : syracuseStep 1268203 = 1902305) B1902305
theorem B1268215 : Blo 1266451 1268215 := bstep (se 1 (by rfl) ⟨951161, by rfl⟩ : syracuseStep 1268215 = 1902323) B1902323
theorem B1268235 : Blo 1266451 1268235 := bstep (se 1 (by rfl) ⟨951176, by rfl⟩ : syracuseStep 1268235 = 1902353) B1902353
theorem B1604119 : Blo 1266451 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B1268247 : Blo 1266451 1268247 := bstep (se 1 (by rfl) ⟨951185, by rfl⟩ : syracuseStep 1268247 = 1902371) B1902371
theorem B1268267 : Blo 1266451 1268267 := bstep (se 1 (by rfl) ⟨951200, by rfl⟩ : syracuseStep 1268267 = 1902401) B1902401
theorem B1268279 : Blo 1266451 1268279 := bstep (se 1 (by rfl) ⟨951209, by rfl⟩ : syracuseStep 1268279 = 1902419) B1902419
theorem B1268299 : Blo 1266451 1268299 := bstep (se 1 (by rfl) ⟨951224, by rfl⟩ : syracuseStep 1268299 = 1902449) B1902449
theorem B1268311 : Blo 1266451 1268311 := bstep (se 1 (by rfl) ⟨951233, by rfl⟩ : syracuseStep 1268311 = 1902467) B1902467
theorem B1268331 : Blo 1266451 1268331 := bstep (se 1 (by rfl) ⟨951248, by rfl⟩ : syracuseStep 1268331 = 1902497) B1902497
theorem B1268343 : Blo 1266451 1268343 := bstep (se 1 (by rfl) ⟨951257, by rfl⟩ : syracuseStep 1268343 = 1902515) B1902515
theorem B6412931 : Blo 1266451 6412931 := bstep (se 1 (by rfl) ⟨4809698, by rfl⟩ : syracuseStep 6412931 = 9619397) B9619397
theorem B1268363 : Blo 1266451 1268363 := bstep (se 1 (by rfl) ⟨951272, by rfl⟩ : syracuseStep 1268363 = 1902545) B1902545
theorem B1268375 : Blo 1266451 1268375 := bstep (se 1 (by rfl) ⟨951281, by rfl⟩ : syracuseStep 1268375 = 1902563) B1902563
theorem B1268395 : Blo 1266451 1268395 := bstep (se 1 (by rfl) ⟨951296, by rfl⟩ : syracuseStep 1268395 = 1902593) B1902593
theorem B1268407 : Blo 1266451 1268407 := bstep (se 1 (by rfl) ⟨951305, by rfl⟩ : syracuseStep 1268407 = 1902611) B1902611
theorem B1268427 : Blo 1266451 1268427 := bstep (se 1 (by rfl) ⟨951320, by rfl⟩ : syracuseStep 1268427 = 1902641) B1902641
theorem B1268439 : Blo 1266451 1268439 := bstep (se 1 (by rfl) ⟨951329, by rfl⟩ : syracuseStep 1268439 = 1902659) B1902659
theorem B7224025 : Blo 1266451 7224025 := bstep (se 2 (by rfl) ⟨2709009, by rfl⟩ : syracuseStep 7224025 = 5418019) B5418019
theorem B4274909 : Blo 1266451 4274909 := bstep (se 3 (by rfl) ⟨801545, by rfl⟩ : syracuseStep 4274909 = 1603091) B1603091
theorem B2849561 : Blo 1266451 2849561 := bstep (se 2 (by rfl) ⟨1068585, by rfl⟩ : syracuseStep 2849561 = 2137171) B2137171
theorem B3046195 : Blo 1266451 3046195 := bstep (se 1 (by rfl) ⟨2284646, by rfl⟩ : syracuseStep 3046195 = 4569293) B4569293
theorem B2849651 : Blo 1266451 2849651 := bstep (se 1 (by rfl) ⟨2137238, by rfl⟩ : syracuseStep 2849651 = 4274477) B4274477
theorem B2849687 : Blo 1266451 2849687 := bstep (se 1 (by rfl) ⟨2137265, by rfl⟩ : syracuseStep 2849687 = 4274531) B4274531
theorem B14441489 : Blo 1266451 14441489 := bstep (se 2 (by rfl) ⟨5415558, by rfl⟩ : syracuseStep 14441489 = 10831117) B10831117
theorem B3210263 : Blo 1266451 3210263 := bstep (se 1 (by rfl) ⟨2407697, by rfl⟩ : syracuseStep 3210263 = 4815395) B4815395
theorem B4815895 : Blo 1266451 4815895 := bstep (se 1 (by rfl) ⟨3611921, by rfl⟩ : syracuseStep 4815895 = 7223843) B7223843
theorem B2849867 : Blo 1266451 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B2030681 : Blo 1266451 2030681 := bstep (se 2 (by rfl) ⟨761505, by rfl⟩ : syracuseStep 2030681 = 1523011) B1523011
theorem B2849921 : Blo 1266451 2849921 := bstep (se 2 (by rfl) ⟨1068720, by rfl⟩ : syracuseStep 2849921 = 2137441) B2137441
theorem B2407553 : Blo 1266451 2407553 := bstep (se 2 (by rfl) ⟨902832, by rfl⟩ : syracuseStep 2407553 = 1805665) B1805665
theorem B1899737 : Blo 1266451 1899737 := bstep (se 2 (by rfl) ⟨712401, by rfl⟩ : syracuseStep 1899737 = 1424803) B1424803
theorem B2137367 : Blo 1266451 2137367 := bstep (se 1 (by rfl) ⟨1603025, by rfl⟩ : syracuseStep 2137367 = 3206051) B3206051
theorem B1899851 : Blo 1266451 1899851 := bstep (se 1 (by rfl) ⟨1424888, by rfl⟩ : syracuseStep 1899851 = 2849777) B2849777
theorem B1899863 : Blo 1266451 1899863 := bstep (se 1 (by rfl) ⟨1424897, by rfl⟩ : syracuseStep 1899863 = 2849795) B2849795
theorem B2850137 : Blo 1266451 2850137 := bstep (se 2 (by rfl) ⟨1068801, by rfl⟩ : syracuseStep 2850137 = 2137603) B2137603
theorem B8117597 : Blo 1266451 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B2407819 : Blo 1266451 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B2137495 : Blo 1266451 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B1899929 : Blo 1266451 1899929 := bstep (se 2 (by rfl) ⟨712473, by rfl⟩ : syracuseStep 1899929 = 1424947) B1424947
theorem B2850227 : Blo 1266451 2850227 := bstep (se 1 (by rfl) ⟨2137670, by rfl⟩ : syracuseStep 2850227 = 4275341) B4275341
theorem B2850263 : Blo 1266451 2850263 := bstep (se 1 (by rfl) ⟨2137697, by rfl⟩ : syracuseStep 2850263 = 4275395) B4275395
theorem B1424875 : Blo 1266451 1424875 := bstep (se 1 (by rfl) ⟨1068656, by rfl⟩ : syracuseStep 1424875 = 2137313) B2137313
theorem B1900043 : Blo 1266451 1900043 := bstep (se 1 (by rfl) ⟨1425032, by rfl⟩ : syracuseStep 1900043 = 2850065) B2850065
theorem B1900055 : Blo 1266451 1900055 := bstep (se 1 (by rfl) ⟨1425041, by rfl⟩ : syracuseStep 1900055 = 2850083) B2850083
theorem B5414465 : Blo 1266451 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B1424983 : Blo 1266451 1424983 := bstep (se 1 (by rfl) ⟨1068737, by rfl⟩ : syracuseStep 1424983 = 2137475) B2137475
theorem B1900121 : Blo 1266451 1900121 := bstep (se 2 (by rfl) ⟨712545, by rfl⟩ : syracuseStep 1900121 = 1425091) B1425091
theorem B2850443 : Blo 1266451 2850443 := bstep (se 1 (by rfl) ⟨2137832, by rfl⟩ : syracuseStep 2850443 = 4275665) B4275665
theorem B2850497 : Blo 1266451 2850497 := bstep (se 2 (by rfl) ⟨1068936, by rfl⟩ : syracuseStep 2850497 = 2137873) B2137873
theorem B1900235 : Blo 1266451 1900235 := bstep (se 1 (by rfl) ⟨1425176, by rfl⟩ : syracuseStep 1900235 = 2850353) B2850353
theorem B1900247 : Blo 1266451 1900247 := bstep (se 1 (by rfl) ⟨1425185, by rfl⟩ : syracuseStep 1900247 = 2850371) B2850371
theorem B11124485 : Blo 1266451 11124485 := bstep (se 4 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 11124485 = 2085841) B2085841
theorem B1425163 : Blo 1266451 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B1900313 : Blo 1266451 1900313 := bstep (se 2 (by rfl) ⟨712617, by rfl⟩ : syracuseStep 1900313 = 1425235) B1425235
theorem B4276043 : Blo 1266451 4276043 := bstep (se 1 (by rfl) ⟨3207032, by rfl⟩ : syracuseStep 4276043 = 6414065) B6414065
theorem B21651299 : Blo 1266451 21651299 := bstep (se 1 (by rfl) ⟨16238474, by rfl⟩ : syracuseStep 21651299 = 32476949) B32476949
theorem B1425271 : Blo 1266451 1425271 := bstep (se 1 (by rfl) ⟨1068953, by rfl⟩ : syracuseStep 1425271 = 2137907) B2137907
theorem B1900427 : Blo 1266451 1900427 := bstep (se 1 (by rfl) ⟨1425320, by rfl⟩ : syracuseStep 1900427 = 2850641) B2850641
theorem B1900439 : Blo 1266451 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B2850713 : Blo 1266451 2850713 := bstep (se 2 (by rfl) ⟨1069017, by rfl⟩ : syracuseStep 2850713 = 2138035) B2138035
theorem B4874201 : Blo 1266451 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B1900505 : Blo 1266451 1900505 := bstep (se 2 (by rfl) ⟨712689, by rfl⟩ : syracuseStep 1900505 = 1425379) B1425379
theorem B2850803 : Blo 1266451 2850803 := bstep (se 1 (by rfl) ⟨2138102, by rfl⟩ : syracuseStep 2850803 = 4276205) B4276205
theorem B1425415 : Blo 1266451 1425415 := bstep (se 1 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 1425415 = 2138123) B2138123
theorem B1900559 : Blo 1266451 1900559 := bstep (se 1 (by rfl) ⟨1425419, by rfl⟩ : syracuseStep 1900559 = 2850839) B2850839
theorem B1900601 : Blo 1266451 1900601 := bstep (se 2 (by rfl) ⟨712725, by rfl⟩ : syracuseStep 1900601 = 1425451) B1425451
theorem B2850875 : Blo 1266451 2850875 := bstep (se 1 (by rfl) ⟨2138156, by rfl⟩ : syracuseStep 2850875 = 4276313) B4276313
theorem B6946883 : Blo 1266451 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B2138231 : Blo 1266451 2138231 := bstep (se 1 (by rfl) ⟨1603673, by rfl⟩ : syracuseStep 2138231 = 3207347) B3207347
theorem B1900679 : Blo 1266451 1900679 := bstep (se 1 (by rfl) ⟨1425509, by rfl⟩ : syracuseStep 1900679 = 2851019) B2851019
theorem B1900715 : Blo 1266451 1900715 := bstep (se 1 (by rfl) ⟨1425536, by rfl⟩ : syracuseStep 1900715 = 2851073) B2851073
theorem B2851001 : Blo 1266451 2851001 := bstep (se 2 (by rfl) ⟨1069125, by rfl⟩ : syracuseStep 2851001 = 2138251) B2138251
theorem B1425595 : Blo 1266451 1425595 := bstep (se 1 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 1425595 = 2138393) B2138393
theorem B6848705 : Blo 1266451 6848705 := bstep (se 2 (by rfl) ⟨2568264, by rfl⟩ : syracuseStep 6848705 = 5136529) B5136529
theorem B1900745 : Blo 1266451 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B5415149 : Blo 1266451 5415149 := bstep (se 3 (by rfl) ⟨1015340, by rfl⟩ : syracuseStep 5415149 = 2030681) B2030681
theorem B1900859 : Blo 1266451 1900859 := bstep (se 1 (by rfl) ⟨1425644, by rfl⟩ : syracuseStep 1900859 = 2851289) B2851289
theorem B1900919 : Blo 1266451 1900919 := bstep (se 1 (by rfl) ⟨1425689, by rfl⟩ : syracuseStep 1900919 = 2851379) B2851379
theorem B1900943 : Blo 1266451 1900943 := bstep (se 1 (by rfl) ⟨1425707, by rfl⟩ : syracuseStep 1900943 = 2851415) B2851415
theorem B1900985 : Blo 1266451 1900985 := bstep (se 2 (by rfl) ⟨712869, by rfl⟩ : syracuseStep 1900985 = 1425739) B1425739
theorem B1901063 : Blo 1266451 1901063 := bstep (se 1 (by rfl) ⟨1425797, by rfl⟩ : syracuseStep 1901063 = 2851595) B2851595
theorem B2851343 : Blo 1266451 2851343 := bstep (se 1 (by rfl) ⟨2138507, by rfl⟩ : syracuseStep 2851343 = 4277015) B4277015
theorem B7217693 : Blo 1266451 7217693 := bstep (se 3 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 7217693 = 2706635) B2706635
theorem B2851361 : Blo 1266451 2851361 := bstep (se 2 (by rfl) ⟨1069260, by rfl⟩ : syracuseStep 2851361 = 2138521) B2138521
theorem B1901099 : Blo 1266451 1901099 := bstep (se 1 (by rfl) ⟨1425824, by rfl⟩ : syracuseStep 1901099 = 2851649) B2851649
theorem B2138683 : Blo 1266451 2138683 := bstep (se 1 (by rfl) ⟨1604012, by rfl⟩ : syracuseStep 2138683 = 3208025) B3208025
theorem B5415491 : Blo 1266451 5415491 := bstep (se 1 (by rfl) ⟨4061618, by rfl⟩ : syracuseStep 5415491 = 8123237) B8123237
theorem B1901129 : Blo 1266451 1901129 := bstep (se 2 (by rfl) ⟨712923, by rfl⟩ : syracuseStep 1901129 = 1425847) B1425847
theorem B1426063 : Blo 1266451 1426063 := bstep (se 1 (by rfl) ⟨1069547, by rfl⟩ : syracuseStep 1426063 = 2139095) B2139095
theorem B1901243 : Blo 1266451 1901243 := bstep (se 1 (by rfl) ⟨1425932, by rfl⟩ : syracuseStep 1901243 = 2851865) B2851865
theorem B2138825 : Blo 1266451 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B1901303 : Blo 1266451 1901303 := bstep (se 1 (by rfl) ⟨1425977, by rfl⟩ : syracuseStep 1901303 = 2851955) B2851955
theorem B1901327 : Blo 1266451 1901327 := bstep (se 1 (by rfl) ⟨1425995, by rfl⟩ : syracuseStep 1901327 = 2851991) B2851991
theorem B5563151 : Blo 1266451 5563151 := bstep (se 1 (by rfl) ⟨4172363, by rfl⟩ : syracuseStep 5563151 = 8344727) B8344727
theorem B1901369 : Blo 1266451 1901369 := bstep (se 2 (by rfl) ⟨713013, by rfl⟩ : syracuseStep 1901369 = 1426027) B1426027
theorem B10421081 : Blo 1266451 10421081 := bstep (se 2 (by rfl) ⟨3907905, by rfl⟩ : syracuseStep 10421081 = 7815811) B7815811
theorem B2851703 : Blo 1266451 2851703 := bstep (se 1 (by rfl) ⟨2138777, by rfl⟩ : syracuseStep 2851703 = 4277555) B4277555
theorem B1901447 : Blo 1266451 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B1901483 : Blo 1266451 1901483 := bstep (se 1 (by rfl) ⟨1426112, by rfl⟩ : syracuseStep 1901483 = 2852225) B2852225
theorem B4277177 : Blo 1266451 4277177 := bstep (se 2 (by rfl) ⟨1603941, by rfl⟩ : syracuseStep 4277177 = 3207883) B3207883
theorem B1901513 : Blo 1266451 1901513 := bstep (se 2 (by rfl) ⟨713067, by rfl⟩ : syracuseStep 1901513 = 1426135) B1426135
theorem B1352711 : Blo 1266451 1352711 := bstep (se 1 (by rfl) ⟨1014533, by rfl⟩ : syracuseStep 1352711 = 2029067) B2029067
theorem B2851883 : Blo 1266451 2851883 := bstep (se 1 (by rfl) ⟨2138912, by rfl⟩ : syracuseStep 2851883 = 4277825) B4277825
theorem B1901627 : Blo 1266451 1901627 := bstep (se 1 (by rfl) ⟨1426220, by rfl⟩ : syracuseStep 1901627 = 2852441) B2852441
theorem B5858365 : Blo 1266451 5858365 := bstep (se 3 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 5858365 = 2196887) B2196887
theorem B16237655 : Blo 1266451 16237655 := bstep (se 1 (by rfl) ⟨12178241, by rfl⟩ : syracuseStep 16237655 = 24356483) B24356483
theorem B1901687 : Blo 1266451 1901687 := bstep (se 1 (by rfl) ⟨1426265, by rfl⟩ : syracuseStep 1901687 = 2852531) B2852531
theorem B13010053 : Blo 1266451 13010053 := bstep (se 4 (by rfl) ⟨1219692, by rfl⟩ : syracuseStep 13010053 = 2439385) B2439385
theorem B1426567 : Blo 1266451 1426567 := bstep (se 1 (by rfl) ⟨1069925, by rfl⟩ : syracuseStep 1426567 = 2139851) B2139851
theorem B1901711 : Blo 1266451 1901711 := bstep (se 1 (by rfl) ⟨1426283, by rfl⟩ : syracuseStep 1901711 = 2852567) B2852567
theorem B1901753 : Blo 1266451 1901753 := bstep (se 2 (by rfl) ⟨713157, by rfl⟩ : syracuseStep 1901753 = 1426315) B1426315
theorem B1901831 : Blo 1266451 1901831 := bstep (se 1 (by rfl) ⟨1426373, by rfl⟩ : syracuseStep 1901831 = 2852747) B2852747
theorem B1901867 : Blo 1266451 1901867 := bstep (se 1 (by rfl) ⟨1426400, by rfl⟩ : syracuseStep 1901867 = 2852801) B2852801
theorem B1426747 : Blo 1266451 1426747 := bstep (se 1 (by rfl) ⟨1070060, by rfl⟩ : syracuseStep 1426747 = 2140121) B2140121
theorem B1901897 : Blo 1266451 1901897 := bstep (se 2 (by rfl) ⟨713211, by rfl⟩ : syracuseStep 1901897 = 1426423) B1426423
theorem B2139527 : Blo 1266451 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B2852243 : Blo 1266451 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B1902011 : Blo 1266451 1902011 := bstep (se 1 (by rfl) ⟨1426508, by rfl⟩ : syracuseStep 1902011 = 2853017) B2853017
theorem B2704841 : Blo 1266451 2704841 := bstep (se 2 (by rfl) ⟨1014315, by rfl⟩ : syracuseStep 2704841 = 2028631) B2028631
theorem B2852297 : Blo 1266451 2852297 := bstep (se 2 (by rfl) ⟨1069611, by rfl⟩ : syracuseStep 2852297 = 2139223) B2139223
theorem B1902071 : Blo 1266451 1902071 := bstep (se 1 (by rfl) ⟨1426553, by rfl⟩ : syracuseStep 1902071 = 2853107) B2853107
theorem B4277771 : Blo 1266451 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B1902095 : Blo 1266451 1902095 := bstep (se 1 (by rfl) ⟨1426571, by rfl⟩ : syracuseStep 1902095 = 2853143) B2853143
theorem B1902137 : Blo 1266451 1902137 := bstep (se 2 (by rfl) ⟨713301, by rfl⟩ : syracuseStep 1902137 = 1426603) B1426603
theorem B4277879 : Blo 1266451 4277879 := bstep (se 1 (by rfl) ⟨3208409, by rfl⟩ : syracuseStep 4277879 = 6416819) B6416819
theorem B1902215 : Blo 1266451 1902215 := bstep (se 1 (by rfl) ⟨1426661, by rfl⟩ : syracuseStep 1902215 = 2853323) B2853323
theorem B1902251 : Blo 1266451 1902251 := bstep (se 1 (by rfl) ⟨1426688, by rfl⟩ : syracuseStep 1902251 = 2853377) B2853377
theorem B1902281 : Blo 1266451 1902281 := bstep (se 2 (by rfl) ⟨713355, by rfl⟩ : syracuseStep 1902281 = 1426711) B1426711
theorem B29280001 : Blo 1266451 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B1902395 : Blo 1266451 1902395 := bstep (se 1 (by rfl) ⟨1426796, by rfl⟩ : syracuseStep 1902395 = 2853593) B2853593
theorem B1902455 : Blo 1266451 1902455 := bstep (se 1 (by rfl) ⟨1426841, by rfl⟩ : syracuseStep 1902455 = 2853683) B2853683
theorem B1902479 : Blo 1266451 1902479 := bstep (se 1 (by rfl) ⟨1426859, by rfl⟩ : syracuseStep 1902479 = 2853719) B2853719
theorem B1902521 : Blo 1266451 1902521 := bstep (se 2 (by rfl) ⟨713445, by rfl⟩ : syracuseStep 1902521 = 1426891) B1426891
theorem B7817219 : Blo 1266451 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B1902599 : Blo 1266451 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B9627659 : Blo 1266451 9627659 := bstep (se 1 (by rfl) ⟨7220744, by rfl⟩ : syracuseStep 9627659 = 14441489) B14441489
theorem B2140175 : Blo 1266451 2140175 := bstep (se 1 (by rfl) ⟨1605131, by rfl⟩ : syracuseStep 2140175 = 3210263) B3210263
theorem B1902635 : Blo 1266451 1902635 := bstep (se 1 (by rfl) ⟨1426976, by rfl⟩ : syracuseStep 1902635 = 2853953) B2853953
theorem B1902665 : Blo 1266451 1902665 := bstep (se 2 (by rfl) ⟨713499, by rfl⟩ : syracuseStep 1902665 = 1426999) B1426999
theorem B2852999 : Blo 1266451 2852999 := bstep (se 1 (by rfl) ⟨2139749, by rfl⟩ : syracuseStep 2852999 = 4279499) B4279499
theorem B4278473 : Blo 1266451 4278473 := bstep (se 2 (by rfl) ⟨1604427, by rfl⟩ : syracuseStep 4278473 = 3208855) B3208855
theorem B2853179 : Blo 1266451 2853179 := bstep (se 1 (by rfl) ⟨2139884, by rfl⟩ : syracuseStep 2853179 = 4279769) B4279769
theorem B2853305 : Blo 1266451 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B7416323 : Blo 1266451 7416323 := bstep (se 1 (by rfl) ⟨5562242, by rfl⟩ : syracuseStep 7416323 = 11124485) B11124485
theorem B3205889 : Blo 1266451 3205889 := bstep (se 2 (by rfl) ⟨1202208, by rfl⟩ : syracuseStep 3205889 = 2404417) B2404417
theorem B4811521 : Blo 1266451 4811521 := bstep (se 2 (by rfl) ⟨1804320, by rfl⟩ : syracuseStep 4811521 = 3608641) B3608641
theorem B2853647 : Blo 1266451 2853647 := bstep (se 1 (by rfl) ⟨2140235, by rfl⟩ : syracuseStep 2853647 = 4280471) B4280471
theorem B2853665 : Blo 1266451 2853665 := bstep (se 2 (by rfl) ⟨1070124, by rfl⟩ : syracuseStep 2853665 = 2140249) B2140249
theorem B3607355 : Blo 1266451 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B3607411 : Blo 1266451 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B3853175 : Blo 1266451 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B2706311 : Blo 1266451 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B4279175 : Blo 1266451 4279175 := bstep (se 1 (by rfl) ⟨3209381, by rfl⟩ : syracuseStep 4279175 = 6418763) B6418763
theorem B6417305 : Blo 1266451 6417305 := bstep (se 2 (by rfl) ⟨2406489, by rfl⟩ : syracuseStep 6417305 = 4812979) B4812979
theorem B7220177 : Blo 1266451 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B8678461 : Blo 1266451 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B3206263 : Blo 1266451 3206263 := bstep (se 1 (by rfl) ⟨2404697, by rfl⟩ : syracuseStep 3206263 = 4809395) B4809395
theorem B2854007 : Blo 1266451 2854007 := bstep (se 1 (by rfl) ⟨2140505, by rfl⟩ : syracuseStep 2854007 = 4281011) B4281011
theorem B3607753 : Blo 1266451 3607753 := bstep (se 2 (by rfl) ⟨1352907, by rfl⟩ : syracuseStep 3607753 = 2705815) B2705815
theorem B4279553 : Blo 1266451 4279553 := bstep (se 2 (by rfl) ⟨1604832, by rfl⟩ : syracuseStep 4279553 = 3209665) B3209665
theorem B1543439 : Blo 1266451 1543439 := bstep (se 1 (by rfl) ⟨1157579, by rfl⟩ : syracuseStep 1543439 = 2315159) B2315159
theorem B7703993 : Blo 1266451 7703993 := bstep (se 2 (by rfl) ⟨2888997, by rfl⟩ : syracuseStep 7703993 = 5777995) B5777995
theorem B7704017 : Blo 1266451 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B3206699 : Blo 1266451 3206699 := bstep (se 1 (by rfl) ⟨2405024, by rfl⟩ : syracuseStep 3206699 = 4810049) B4810049
theorem B21646925 : Blo 1266451 21646925 := bstep (se 3 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 21646925 = 8117597) B8117597
theorem B1625719 : Blo 1266451 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B6590267 : Blo 1266451 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B4878139 : Blo 1266451 4878139 := bstep (se 1 (by rfl) ⟨3658604, by rfl⟩ : syracuseStep 4878139 = 7317209) B7317209
theorem B2707319 : Blo 1266451 2707319 := bstep (se 1 (by rfl) ⟨2030489, by rfl⟩ : syracuseStep 2707319 = 4060979) B4060979
theorem B9629603 : Blo 1266451 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B2707499 : Blo 1266451 2707499 := bstep (se 1 (by rfl) ⟨2030624, by rfl⟩ : syracuseStep 2707499 = 4061249) B4061249
theorem B4280363 : Blo 1266451 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B4337725 : Blo 1266451 4337725 := bstep (se 3 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 4337725 = 1626647) B1626647
theorem B14438573 : Blo 1266451 14438573 := bstep (se 3 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 14438573 = 5414465) B5414465
theorem B2404667 : Blo 1266451 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B3207539 : Blo 1266451 3207539 := bstep (se 1 (by rfl) ⟨2405654, by rfl⟩ : syracuseStep 3207539 = 4811309) B4811309
theorem B3207559 : Blo 1266451 3207559 := bstep (se 1 (by rfl) ⟨2405669, by rfl⟩ : syracuseStep 3207559 = 4811339) B4811339
theorem B6500755 : Blo 1266451 6500755 := bstep (se 1 (by rfl) ⟨4875566, by rfl⟩ : syracuseStep 6500755 = 9751133) B9751133
theorem B2568719 : Blo 1266451 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B5411357 : Blo 1266451 5411357 := bstep (se 3 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 5411357 = 2029259) B2029259
theorem B3207833 : Blo 1266451 3207833 := bstep (se 2 (by rfl) ⟨1202937, by rfl⟩ : syracuseStep 3207833 = 2405875) B2405875
theorem B27792089 : Blo 1266451 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B14447321 : Blo 1266451 14447321 := bstep (se 2 (by rfl) ⟨5417745, by rfl⟩ : syracuseStep 14447321 = 10835491) B10835491
theorem B13693697 : Blo 1266451 13693697 := bstep (se 2 (by rfl) ⟨5135136, by rfl⟩ : syracuseStep 13693697 = 10270273) B10270273
theorem B4567823 : Blo 1266451 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2405153 : Blo 1266451 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B7222067 : Blo 1266451 7222067 := bstep (se 1 (by rfl) ⟨5416550, by rfl⟩ : syracuseStep 7222067 = 10833101) B10833101
theorem B1266491 : Blo 1266451 1266491 := bstep (se 1 (by rfl) ⟨949868, by rfl⟩ : syracuseStep 1266491 = 1899737) B1899737
theorem B3207995 : Blo 1266451 3207995 := bstep (se 1 (by rfl) ⟨2405996, by rfl⟩ : syracuseStep 3207995 = 4811993) B4811993
theorem B1266567 : Blo 1266451 1266567 := bstep (se 1 (by rfl) ⟨949925, by rfl⟩ : syracuseStep 1266567 = 1899851) B1899851
theorem B1266575 : Blo 1266451 1266575 := bstep (se 1 (by rfl) ⟨949931, by rfl⟩ : syracuseStep 1266575 = 1899863) B1899863
theorem B140743601 : Blo 1266451 140743601 := bstep (se 2 (by rfl) ⟨52778850, by rfl⟩ : syracuseStep 140743601 = 105557701) B105557701
theorem B2405305 : Blo 1266451 2405305 := bstep (se 2 (by rfl) ⟨901989, by rfl⟩ : syracuseStep 2405305 = 1803979) B1803979
theorem B1266619 : Blo 1266451 1266619 := bstep (se 1 (by rfl) ⟨949964, by rfl⟩ : syracuseStep 1266619 = 1899929) B1899929
theorem B1266695 : Blo 1266451 1266695 := bstep (se 1 (by rfl) ⟨950021, by rfl⟩ : syracuseStep 1266695 = 1900043) B1900043
theorem B1266703 : Blo 1266451 1266703 := bstep (se 1 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 1266703 = 1900055) B1900055
theorem B3208207 : Blo 1266451 3208207 := bstep (se 1 (by rfl) ⟨2406155, by rfl⟩ : syracuseStep 3208207 = 4812311) B4812311
theorem B1266747 : Blo 1266451 1266747 := bstep (se 1 (by rfl) ⟨950060, by rfl⟩ : syracuseStep 1266747 = 1900121) B1900121
theorem B1266823 : Blo 1266451 1266823 := bstep (se 1 (by rfl) ⟨950117, by rfl⟩ : syracuseStep 1266823 = 1900235) B1900235
theorem B1266831 : Blo 1266451 1266831 := bstep (se 1 (by rfl) ⟨950123, by rfl⟩ : syracuseStep 1266831 = 1900247) B1900247
theorem B1266875 : Blo 1266451 1266875 := bstep (se 1 (by rfl) ⟨950156, by rfl⟩ : syracuseStep 1266875 = 1900313) B1900313
theorem B5412041 : Blo 1266451 5412041 := bstep (se 2 (by rfl) ⟨2029515, by rfl⟩ : syracuseStep 5412041 = 4059031) B4059031
theorem B24360173 : Blo 1266451 24360173 := bstep (se 3 (by rfl) ⟨4567532, by rfl⟩ : syracuseStep 24360173 = 9135065) B9135065
theorem B1266951 : Blo 1266451 1266951 := bstep (se 1 (by rfl) ⟨950213, by rfl⟩ : syracuseStep 1266951 = 1900427) B1900427
theorem B1266959 : Blo 1266451 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B4879631 : Blo 1266451 4879631 := bstep (se 1 (by rfl) ⟨3659723, by rfl⟩ : syracuseStep 4879631 = 7319447) B7319447
theorem B3208481 : Blo 1266451 3208481 := bstep (se 2 (by rfl) ⟨1203180, by rfl⟩ : syracuseStep 3208481 = 2406361) B2406361
theorem B3249467 : Blo 1266451 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B1267003 : Blo 1266451 1267003 := bstep (se 1 (by rfl) ⟨950252, by rfl⟩ : syracuseStep 1267003 = 1900505) B1900505
theorem B3609917 : Blo 1266451 3609917 := bstep (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) B1353719
theorem B6411635 : Blo 1266451 6411635 := bstep (se 1 (by rfl) ⟨4808726, by rfl⟩ : syracuseStep 6411635 = 9617453) B9617453
theorem B1267079 : Blo 1266451 1267079 := bstep (se 1 (by rfl) ⟨950309, by rfl⟩ : syracuseStep 1267079 = 1900619) B1900619
theorem B1267087 : Blo 1266451 1267087 := bstep (se 1 (by rfl) ⟨950315, by rfl⟩ : syracuseStep 1267087 = 1900631) B1900631
theorem B6419897 : Blo 1266451 6419897 := bstep (se 2 (by rfl) ⟨2407461, by rfl⟩ : syracuseStep 6419897 = 4814923) B4814923
theorem B1267131 : Blo 1266451 1267131 := bstep (se 1 (by rfl) ⟨950348, by rfl⟩ : syracuseStep 1267131 = 1900697) B1900697
theorem B1267207 : Blo 1266451 1267207 := bstep (se 1 (by rfl) ⟨950405, by rfl⟩ : syracuseStep 1267207 = 1900811) B1900811
theorem B1267215 : Blo 1266451 1267215 := bstep (se 1 (by rfl) ⟨950411, by rfl⟩ : syracuseStep 1267215 = 1900823) B1900823
theorem B3610145 : Blo 1266451 3610145 := bstep (se 2 (by rfl) ⟨1353804, by rfl⟩ : syracuseStep 3610145 = 2707609) B2707609
theorem B1267259 : Blo 1266451 1267259 := bstep (se 1 (by rfl) ⟨950444, by rfl⟩ : syracuseStep 1267259 = 1900889) B1900889
theorem B4814423 : Blo 1266451 4814423 := bstep (se 1 (by rfl) ⟨3610817, by rfl⟩ : syracuseStep 4814423 = 7221635) B7221635
theorem B3298931 : Blo 1266451 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B1267335 : Blo 1266451 1267335 := bstep (se 1 (by rfl) ⟨950501, by rfl⟩ : syracuseStep 1267335 = 1901003) B1901003
theorem B1267343 : Blo 1266451 1267343 := bstep (se 1 (by rfl) ⟨950507, by rfl⟩ : syracuseStep 1267343 = 1901015) B1901015
theorem B1603243 : Blo 1266451 1603243 := bstep (se 1 (by rfl) ⟨1202432, by rfl⟩ : syracuseStep 1603243 = 2404865) B2404865
theorem B1267387 : Blo 1266451 1267387 := bstep (se 1 (by rfl) ⟨950540, by rfl⟩ : syracuseStep 1267387 = 1901081) B1901081
theorem B15423169 : Blo 1266451 15423169 := bstep (se 2 (by rfl) ⟨5783688, by rfl⟩ : syracuseStep 15423169 = 11567377) B11567377
theorem B1267463 : Blo 1266451 1267463 := bstep (se 1 (by rfl) ⟨950597, by rfl⟩ : syracuseStep 1267463 = 1901195) B1901195
theorem B1267471 : Blo 1266451 1267471 := bstep (se 1 (by rfl) ⟨950603, by rfl⟩ : syracuseStep 1267471 = 1901207) B1901207
theorem B5142305 : Blo 1266451 5142305 := bstep (se 2 (by rfl) ⟨1928364, by rfl⟩ : syracuseStep 5142305 = 3856729) B3856729
theorem B1267515 : Blo 1266451 1267515 := bstep (se 1 (by rfl) ⟨950636, by rfl⟩ : syracuseStep 1267515 = 1901273) B1901273
theorem B6412121 : Blo 1266451 6412121 := bstep (se 2 (by rfl) ⟨2404545, by rfl⟩ : syracuseStep 6412121 = 4809091) B4809091
theorem B3610487 : Blo 1266451 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B1267591 : Blo 1266451 1267591 := bstep (se 1 (by rfl) ⟨950693, by rfl⟩ : syracuseStep 1267591 = 1901387) B1901387
theorem B1603471 : Blo 1266451 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B1267599 : Blo 1266451 1267599 := bstep (se 1 (by rfl) ⟨950699, by rfl⟩ : syracuseStep 1267599 = 1901399) B1901399
theorem B16250777 : Blo 1266451 16250777 := bstep (se 2 (by rfl) ⟨6094041, by rfl⟩ : syracuseStep 16250777 = 12188083) B12188083
theorem B1267643 : Blo 1266451 1267643 := bstep (se 1 (by rfl) ⟨950732, by rfl⟩ : syracuseStep 1267643 = 1901465) B1901465
theorem B1267719 : Blo 1266451 1267719 := bstep (se 1 (by rfl) ⟨950789, by rfl⟩ : syracuseStep 1267719 = 1901579) B1901579
theorem B13694987 : Blo 1266451 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B1267727 : Blo 1266451 1267727 := bstep (se 1 (by rfl) ⟨950795, by rfl⟩ : syracuseStep 1267727 = 1901591) B1901591
theorem B1267771 : Blo 1266451 1267771 := bstep (se 1 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 1267771 = 1901657) B1901657
theorem B4569149 : Blo 1266451 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B4814909 : Blo 1266451 4814909 := bstep (se 3 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 4814909 = 1805591) B1805591
theorem B1267847 : Blo 1266451 1267847 := bstep (se 1 (by rfl) ⟨950885, by rfl⟩ : syracuseStep 1267847 = 1901771) B1901771
theorem B1267855 : Blo 1266451 1267855 := bstep (se 1 (by rfl) ⟨950891, by rfl⟩ : syracuseStep 1267855 = 1901783) B1901783
theorem B7215277 : Blo 1266451 7215277 := bstep (se 3 (by rfl) ⟨1352864, by rfl⟩ : syracuseStep 7215277 = 2705729) B2705729
theorem B1267899 : Blo 1266451 1267899 := bstep (se 1 (by rfl) ⟨950924, by rfl⟩ : syracuseStep 1267899 = 1901849) B1901849
theorem B7223525 : Blo 1266451 7223525 := bstep (se 4 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 7223525 = 1354411) B1354411
theorem B1267975 : Blo 1266451 1267975 := bstep (se 1 (by rfl) ⟨950981, by rfl⟩ : syracuseStep 1267975 = 1901963) B1901963
theorem B3209483 : Blo 1266451 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B1267983 : Blo 1266451 1267983 := bstep (se 1 (by rfl) ⟨950987, by rfl⟩ : syracuseStep 1267983 = 1901975) B1901975
theorem B9632033 : Blo 1266451 9632033 := bstep (se 2 (by rfl) ⟨3612012, by rfl⟩ : syracuseStep 9632033 = 7224025) B7224025
theorem B1268027 : Blo 1266451 1268027 := bstep (se 1 (by rfl) ⟨951020, by rfl⟩ : syracuseStep 1268027 = 1902041) B1902041
theorem B4118843 : Blo 1266451 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B7420295 : Blo 1266451 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B1268103 : Blo 1266451 1268103 := bstep (se 1 (by rfl) ⟨951077, by rfl⟩ : syracuseStep 1268103 = 1902155) B1902155
theorem B1268111 : Blo 1266451 1268111 := bstep (se 1 (by rfl) ⟨951083, by rfl⟩ : syracuseStep 1268111 = 1902167) B1902167
theorem B8116625 : Blo 1266451 8116625 := bstep (se 2 (by rfl) ⟨3043734, by rfl⟩ : syracuseStep 8116625 = 6087469) B6087469
theorem B16243091 : Blo 1266451 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B4274585 : Blo 1266451 4274585 := bstep (se 2 (by rfl) ⟨1602969, by rfl⟩ : syracuseStep 4274585 = 3205939) B3205939
theorem B4061593 : Blo 1266451 4061593 := bstep (se 2 (by rfl) ⟨1523097, by rfl⟩ : syracuseStep 4061593 = 3046195) B3046195
theorem B1268155 : Blo 1266451 1268155 := bstep (se 1 (by rfl) ⟨951116, by rfl⟩ : syracuseStep 1268155 = 1902233) B1902233
theorem B1268231 : Blo 1266451 1268231 := bstep (se 1 (by rfl) ⟨951173, by rfl⟩ : syracuseStep 1268231 = 1902347) B1902347
theorem B1268239 : Blo 1266451 1268239 := bstep (se 1 (by rfl) ⟨951179, by rfl⟩ : syracuseStep 1268239 = 1902359) B1902359
theorem B6847019 : Blo 1266451 6847019 := bstep (se 1 (by rfl) ⟨5135264, by rfl⟩ : syracuseStep 6847019 = 10270529) B10270529
theorem B1268283 : Blo 1266451 1268283 := bstep (se 1 (by rfl) ⟨951212, by rfl⟩ : syracuseStep 1268283 = 1902425) B1902425
theorem B1604215 : Blo 1266451 1604215 := bstep (se 1 (by rfl) ⟨1203161, by rfl⟩ : syracuseStep 1604215 = 2406323) B2406323
theorem B1268359 : Blo 1266451 1268359 := bstep (se 1 (by rfl) ⟨951269, by rfl⟩ : syracuseStep 1268359 = 1902539) B1902539
theorem B1522319 : Blo 1266451 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B1268367 : Blo 1266451 1268367 := bstep (se 1 (by rfl) ⟨951275, by rfl⟩ : syracuseStep 1268367 = 1902551) B1902551
theorem B2407097 : Blo 1266451 2407097 := bstep (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) B1805323
theorem B1268411 : Blo 1266451 1268411 := bstep (se 1 (by rfl) ⟨951308, by rfl⟩ : syracuseStep 1268411 = 1902617) B1902617
theorem B9624257 : Blo 1266451 9624257 := bstep (se 2 (by rfl) ⟨3609096, by rfl⟩ : syracuseStep 9624257 = 7218193) B7218193
theorem B6421193 : Blo 1266451 6421193 := bstep (se 2 (by rfl) ⟨2407947, by rfl⟩ : syracuseStep 6421193 = 4815895) B4815895
theorem B2849579 : Blo 1266451 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B3210131 : Blo 1266451 3210131 := bstep (se 1 (by rfl) ⟨2407598, by rfl⟩ : syracuseStep 3210131 = 4815197) B4815197
theorem B13015961 : Blo 1266451 13015961 := bstep (se 2 (by rfl) ⟨4880985, by rfl⟩ : syracuseStep 13015961 = 9761971) B9761971
theorem B5413817 : Blo 1266451 5413817 := bstep (se 2 (by rfl) ⟨2030181, by rfl⟩ : syracuseStep 5413817 = 4060363) B4060363
theorem B1604539 : Blo 1266451 1604539 := bstep (se 1 (by rfl) ⟨1203404, by rfl⟩ : syracuseStep 1604539 = 2406809) B2406809
theorem B26000389 : Blo 1266451 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B4275287 : Blo 1266451 4275287 := bstep (se 1 (by rfl) ⟨3206465, by rfl⟩ : syracuseStep 4275287 = 6412931) B6412931
theorem B2849939 : Blo 1266451 2849939 := bstep (se 1 (by rfl) ⟨2137454, by rfl⟩ : syracuseStep 2849939 = 4274909) B4274909
theorem B3210425 : Blo 1266451 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B1899707 : Blo 1266451 1899707 := bstep (se 1 (by rfl) ⟨1424780, by rfl⟩ : syracuseStep 1899707 = 2849561) B2849561
theorem B41655493 : Blo 1266451 41655493 := bstep (se 4 (by rfl) ⟨3905202, by rfl⟩ : syracuseStep 41655493 = 7810405) B7810405
theorem B2849993 : Blo 1266451 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B1899767 : Blo 1266451 1899767 := bstep (se 1 (by rfl) ⟨1424825, by rfl⟩ : syracuseStep 1899767 = 2849651) B2849651
theorem B1899791 : Blo 1266451 1899791 := bstep (se 1 (by rfl) ⟨1424843, by rfl⟩ : syracuseStep 1899791 = 2849687) B2849687
theorem B2137387 : Blo 1266451 2137387 := bstep (se 1 (by rfl) ⟨1603040, by rfl⟩ : syracuseStep 2137387 = 3206081) B3206081
theorem B1899833 : Blo 1266451 1899833 := bstep (se 2 (by rfl) ⟨712437, by rfl⟩ : syracuseStep 1899833 = 1424875) B1424875
theorem B1899911 : Blo 1266451 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B1285511 : Blo 1266451 1285511 := bstep (se 1 (by rfl) ⟨964133, by rfl⟩ : syracuseStep 1285511 = 1928267) B1928267
theorem B5561747 : Blo 1266451 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B1899947 : Blo 1266451 1899947 := bstep (se 1 (by rfl) ⟨1424960, by rfl⟩ : syracuseStep 1899947 = 2849921) B2849921
theorem B1605035 : Blo 1266451 1605035 := bstep (se 1 (by rfl) ⟨1203776, by rfl⟩ : syracuseStep 1605035 = 2407553) B2407553
theorem B2137529 : Blo 1266451 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B1899977 : Blo 1266451 1899977 := bstep (se 2 (by rfl) ⟨712491, by rfl⟩ : syracuseStep 1899977 = 1424983) B1424983
theorem B1424911 : Blo 1266451 1424911 := bstep (se 1 (by rfl) ⟨1068683, by rfl⟩ : syracuseStep 1424911 = 2137367) B2137367
theorem B1900091 : Blo 1266451 1900091 := bstep (se 1 (by rfl) ⟨1425068, by rfl⟩ : syracuseStep 1900091 = 2850137) B2850137
theorem B4275773 : Blo 1266451 4275773 := bstep (se 3 (by rfl) ⟨801707, by rfl⟩ : syracuseStep 4275773 = 1603415) B1603415
theorem B1900151 : Blo 1266451 1900151 := bstep (se 1 (by rfl) ⟨1425113, by rfl⟩ : syracuseStep 1900151 = 2850227) B2850227
theorem B1900175 : Blo 1266451 1900175 := bstep (se 1 (by rfl) ⟨1425131, by rfl⟩ : syracuseStep 1900175 = 2850263) B2850263
theorem B1711787 : Blo 1266451 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B1900217 : Blo 1266451 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1900295 : Blo 1266451 1900295 := bstep (se 1 (by rfl) ⟨1425221, by rfl⟩ : syracuseStep 1900295 = 2850443) B2850443
theorem B1900331 : Blo 1266451 1900331 := bstep (se 1 (by rfl) ⟨1425248, by rfl⟩ : syracuseStep 1900331 = 2850497) B2850497
theorem B1900361 : Blo 1266451 1900361 := bstep (se 2 (by rfl) ⟨712635, by rfl⟩ : syracuseStep 1900361 = 1425271) B1425271
theorem B2850695 : Blo 1266451 2850695 := bstep (se 1 (by rfl) ⟨2138021, by rfl⟩ : syracuseStep 2850695 = 4276043) B4276043
theorem B6414227 : Blo 1266451 6414227 := bstep (se 1 (by rfl) ⟨4810670, by rfl⟩ : syracuseStep 6414227 = 9621341) B9621341
theorem B14434199 : Blo 1266451 14434199 := bstep (se 1 (by rfl) ⟨10825649, by rfl⟩ : syracuseStep 14434199 = 21651299) B21651299
theorem B20848535 : Blo 1266451 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B1900475 : Blo 1266451 1900475 := bstep (se 1 (by rfl) ⟨1425356, by rfl⟩ : syracuseStep 1900475 = 2850713) B2850713
theorem B1900535 : Blo 1266451 1900535 := bstep (se 1 (by rfl) ⟨1425401, by rfl⟩ : syracuseStep 1900535 = 2850803) B2850803
theorem B1900553 : Blo 1266451 1900553 := bstep (se 2 (by rfl) ⟨712707, by rfl⟩ : syracuseStep 1900553 = 1425415) B1425415
theorem B1900583 : Blo 1266451 1900583 := bstep (se 1 (by rfl) ⟨1425437, by rfl⟩ : syracuseStep 1900583 = 2850875) B2850875
theorem B1425487 : Blo 1266451 1425487 := bstep (se 1 (by rfl) ⟨1069115, by rfl⟩ : syracuseStep 1425487 = 2138231) B2138231
theorem B5783633 : Blo 1266451 5783633 := bstep (se 2 (by rfl) ⟨2168862, by rfl⟩ : syracuseStep 5783633 = 4337725) B4337725
theorem B9625715 : Blo 1266451 9625715 := bstep (se 1 (by rfl) ⟨7219286, by rfl⟩ : syracuseStep 9625715 = 14438573) B14438573
theorem B1900667 : Blo 1266451 1900667 := bstep (se 1 (by rfl) ⟨1425500, by rfl⟩ : syracuseStep 1900667 = 2851001) B2851001
theorem B2138359 : Blo 1266451 2138359 := bstep (se 1 (by rfl) ⟨1603769, by rfl⟩ : syracuseStep 2138359 = 3207539) B3207539
theorem B1900793 : Blo 1266451 1900793 := bstep (se 2 (by rfl) ⟨712797, by rfl⟩ : syracuseStep 1900793 = 1425595) B1425595
theorem B1900895 : Blo 1266451 1900895 := bstep (se 1 (by rfl) ⟨1425671, by rfl⟩ : syracuseStep 1900895 = 2851343) B2851343
theorem B1900907 : Blo 1266451 1900907 := bstep (se 1 (by rfl) ⟨1425680, by rfl⟩ : syracuseStep 1900907 = 2851361) B2851361
theorem B2138555 : Blo 1266451 2138555 := bstep (se 1 (by rfl) ⟨1603916, by rfl⟩ : syracuseStep 2138555 = 3207833) B3207833
theorem B1425883 : Blo 1266451 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B4276745 : Blo 1266451 4276745 := bstep (se 2 (by rfl) ⟨1603779, by rfl⟩ : syracuseStep 4276745 = 3207559) B3207559
theorem B5415457 : Blo 1266451 5415457 := bstep (se 2 (by rfl) ⟨2030796, by rfl⟩ : syracuseStep 5415457 = 4061593) B4061593
theorem B2138663 : Blo 1266451 2138663 := bstep (se 1 (by rfl) ⟨1603997, by rfl⟩ : syracuseStep 2138663 = 3207995) B3207995
theorem B6947387 : Blo 1266451 6947387 := bstep (se 1 (by rfl) ⟨5210540, by rfl⟩ : syracuseStep 6947387 = 10421081) B10421081
theorem B1901135 : Blo 1266451 1901135 := bstep (se 1 (by rfl) ⟨1425851, by rfl⟩ : syracuseStep 1901135 = 2851703) B2851703
theorem B2851451 : Blo 1266451 2851451 := bstep (se 1 (by rfl) ⟨2138588, by rfl⟩ : syracuseStep 2851451 = 4277177) B4277177
theorem B1901255 : Blo 1266451 1901255 := bstep (se 1 (by rfl) ⟨1425941, by rfl⟩ : syracuseStep 1901255 = 2851883) B2851883
theorem B2851577 : Blo 1266451 2851577 := bstep (se 2 (by rfl) ⟨1069341, by rfl⟩ : syracuseStep 2851577 = 2138683) B2138683
theorem B2138953 : Blo 1266451 2138953 := bstep (se 2 (by rfl) ⟨802107, by rfl⟩ : syracuseStep 2138953 = 1604215) B1604215
theorem B3253087 : Blo 1266451 3253087 := bstep (se 1 (by rfl) ⟨2439815, by rfl⟩ : syracuseStep 3253087 = 4879631) B4879631
theorem B1901417 : Blo 1266451 1901417 := bstep (se 2 (by rfl) ⟨713031, by rfl⟩ : syracuseStep 1901417 = 1426063) B1426063
theorem B2138987 : Blo 1266451 2138987 := bstep (se 1 (by rfl) ⟨1604240, by rfl⟩ : syracuseStep 2138987 = 3208481) B3208481
theorem B1426351 : Blo 1266451 1426351 := bstep (se 1 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 1426351 = 2139527) B2139527
theorem B1901495 : Blo 1266451 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B1803227 : Blo 1266451 1803227 := bstep (se 1 (by rfl) ⟨1352420, by rfl⟩ : syracuseStep 1803227 = 2704841) B2704841
theorem B1901531 : Blo 1266451 1901531 := bstep (se 1 (by rfl) ⟨1426148, by rfl⟩ : syracuseStep 1901531 = 2852297) B2852297
theorem B6415361 : Blo 1266451 6415361 := bstep (se 2 (by rfl) ⟨2405760, by rfl⟩ : syracuseStep 6415361 = 4811521) B4811521
theorem B2851847 : Blo 1266451 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B2851919 : Blo 1266451 2851919 := bstep (se 1 (by rfl) ⟨2138939, by rfl⟩ : syracuseStep 2851919 = 4277879) B4277879
theorem B4809881 : Blo 1266451 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B41100533 : Blo 1266451 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B2139385 : Blo 1266451 2139385 := bstep (se 2 (by rfl) ⟨802269, by rfl⟩ : syracuseStep 2139385 = 1604539) B1604539
theorem B5211479 : Blo 1266451 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B1426783 : Blo 1266451 1426783 := bstep (se 1 (by rfl) ⟨1070087, by rfl⟩ : syracuseStep 1426783 = 2140175) B2140175
theorem B4277609 : Blo 1266451 4277609 := bstep (se 2 (by rfl) ⟨1604103, by rfl⟩ : syracuseStep 4277609 = 3208207) B3208207
theorem B6849917 : Blo 1266451 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B1901999 : Blo 1266451 1901999 := bstep (se 1 (by rfl) ⟨1426499, by rfl⟩ : syracuseStep 1901999 = 2852999) B2852999
theorem B2852315 : Blo 1266451 2852315 := bstep (se 1 (by rfl) ⟨2139236, by rfl⟩ : syracuseStep 2852315 = 4278473) B4278473
theorem B2139655 : Blo 1266451 2139655 := bstep (se 1 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 2139655 = 3209483) B3209483
theorem B1902089 : Blo 1266451 1902089 := bstep (se 2 (by rfl) ⟨713283, by rfl⟩ : syracuseStep 1902089 = 1426567) B1426567
theorem B1902119 : Blo 1266451 1902119 := bstep (se 1 (by rfl) ⟨1426589, by rfl⟩ : syracuseStep 1902119 = 2853179) B2853179
theorem B2745895 : Blo 1266451 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B4810337 : Blo 1266451 4810337 := bstep (se 2 (by rfl) ⟨1803876, by rfl⟩ : syracuseStep 4810337 = 3607753) B3607753
theorem B1902203 : Blo 1266451 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B4564679 : Blo 1266451 4564679 := bstep (se 1 (by rfl) ⟨3423509, by rfl⟩ : syracuseStep 4564679 = 6847019) B6847019
theorem B1902329 : Blo 1266451 1902329 := bstep (se 2 (by rfl) ⟨713373, by rfl⟩ : syracuseStep 1902329 = 1426747) B1426747
theorem B4564765 : Blo 1266451 4564765 := bstep (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) B1711787
theorem B6416171 : Blo 1266451 6416171 := bstep (se 1 (by rfl) ⟨4812128, by rfl⟩ : syracuseStep 6416171 = 9624257) B9624257
theorem B1902431 : Blo 1266451 1902431 := bstep (se 1 (by rfl) ⟨1426823, by rfl⟩ : syracuseStep 1902431 = 2853647) B2853647
theorem B1902443 : Blo 1266451 1902443 := bstep (se 1 (by rfl) ⟨1426832, by rfl⟩ : syracuseStep 1902443 = 2853665) B2853665
theorem B1804207 : Blo 1266451 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B2852783 : Blo 1266451 2852783 := bstep (se 1 (by rfl) ⟨2139587, by rfl⟩ : syracuseStep 2852783 = 4279175) B4279175
theorem B2140087 : Blo 1266451 2140087 := bstep (se 1 (by rfl) ⟨1605065, by rfl⟩ : syracuseStep 2140087 = 3210131) B3210131
theorem B4278203 : Blo 1266451 4278203 := bstep (se 1 (by rfl) ⟨3208652, by rfl⟩ : syracuseStep 4278203 = 6417305) B6417305
theorem B8677307 : Blo 1266451 8677307 := bstep (se 1 (by rfl) ⟨6507980, by rfl⟩ : syracuseStep 8677307 = 13015961) B13015961
theorem B1902671 : Blo 1266451 1902671 := bstep (se 1 (by rfl) ⟨1427003, by rfl⟩ : syracuseStep 1902671 = 2854007) B2854007
theorem B34670693 : Blo 1266451 34670693 := bstep (se 4 (by rfl) ⟨3250377, by rfl⟩ : syracuseStep 34670693 = 6500755) B6500755
theorem B2140283 : Blo 1266451 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B2853035 : Blo 1266451 2853035 := bstep (se 1 (by rfl) ⟨2139776, by rfl⟩ : syracuseStep 2853035 = 4279553) B4279553
theorem B20564225 : Blo 1266451 20564225 := bstep (se 2 (by rfl) ⟨7711584, by rfl⟩ : syracuseStep 20564225 = 15423169) B15423169
theorem B4393511 : Blo 1266451 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B1804879 : Blo 1266451 1804879 := bstep (se 1 (by rfl) ⟨1353659, by rfl⟩ : syracuseStep 1804879 = 2707319) B2707319
theorem B3607229 : Blo 1266451 3607229 := bstep (se 3 (by rfl) ⟨676355, by rfl⟩ : syracuseStep 3607229 = 1352711) B1352711
theorem B1804999 : Blo 1266451 1804999 := bstep (se 1 (by rfl) ⟨1353749, by rfl⟩ : syracuseStep 1804999 = 2707499) B2707499
theorem B2853575 : Blo 1266451 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B4631255 : Blo 1266451 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B4565803 : Blo 1266451 4565803 := bstep (se 1 (by rfl) ⟨3424352, by rfl⟩ : syracuseStep 4565803 = 6848705) B6848705
theorem B9620369 : Blo 1266451 9620369 := bstep (se 2 (by rfl) ⟨3607638, by rfl⟩ : syracuseStep 9620369 = 7215277) B7215277
theorem B3607571 : Blo 1266451 3607571 := bstep (se 1 (by rfl) ⟨2705678, by rfl⟩ : syracuseStep 3607571 = 5411357) B5411357
theorem B4811795 : Blo 1266451 4811795 := bstep (se 1 (by rfl) ⟨3608846, by rfl⟩ : syracuseStep 4811795 = 7217693) B7217693
theorem B9129131 : Blo 1266451 9129131 := bstep (se 1 (by rfl) ⟨6846848, by rfl⟩ : syracuseStep 9129131 = 13693697) B13693697
theorem B4115837 : Blo 1266451 4115837 := bstep (se 3 (by rfl) ⟨771719, by rfl⟩ : syracuseStep 4115837 = 1543439) B1543439
theorem B10825103 : Blo 1266451 10825103 := bstep (se 1 (by rfl) ⟨8118827, by rfl⟩ : syracuseStep 10825103 = 16237655) B16237655
theorem B3608027 : Blo 1266451 3608027 := bstep (se 1 (by rfl) ⟨2706020, by rfl⟩ : syracuseStep 3608027 = 5412041) B5412041
theorem B16240115 : Blo 1266451 16240115 := bstep (se 1 (by rfl) ⟨12180086, by rfl⟩ : syracuseStep 16240115 = 24360173) B24360173
theorem B2166311 : Blo 1266451 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B4279931 : Blo 1266451 4279931 := bstep (se 1 (by rfl) ⟨3209948, by rfl⟩ : syracuseStep 4279931 = 6419897) B6419897
theorem B19787453 : Blo 1266451 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B3428029 : Blo 1266451 3428029 := bstep (se 3 (by rfl) ⟨642755, by rfl⟩ : syracuseStep 3428029 = 1285511) B1285511
theorem B2199287 : Blo 1266451 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B4280093 : Blo 1266451 4280093 := bstep (se 3 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 4280093 = 1605035) B1605035
theorem B3428203 : Blo 1266451 3428203 := bstep (se 1 (by rfl) ⟨2571152, by rfl⟩ : syracuseStep 3428203 = 5142305) B5142305
theorem B3207073 : Blo 1266451 3207073 := bstep (se 2 (by rfl) ⟨1202652, by rfl⟩ : syracuseStep 3207073 = 2405305) B2405305
theorem B10833851 : Blo 1266451 10833851 := bstep (se 1 (by rfl) ⟨8125388, by rfl⟩ : syracuseStep 10833851 = 16250777) B16250777
theorem B9129991 : Blo 1266451 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B6418439 : Blo 1266451 6418439 := bstep (se 1 (by rfl) ⟨4813829, by rfl⟩ : syracuseStep 6418439 = 9627659) B9627659
theorem B7811153 : Blo 1266451 7811153 := bstep (se 2 (by rfl) ⟨2929182, by rfl⟩ : syracuseStep 7811153 = 5858365) B5858365
theorem B11571281 : Blo 1266451 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B17346737 : Blo 1266451 17346737 := bstep (se 2 (by rfl) ⟨6505026, by rfl⟩ : syracuseStep 17346737 = 13010053) B13010053
theorem B5411083 : Blo 1266451 5411083 := bstep (se 1 (by rfl) ⟨4058312, by rfl⟩ : syracuseStep 5411083 = 8116625) B8116625
theorem B4944215 : Blo 1266451 4944215 := bstep (se 1 (by rfl) ⟨3708161, by rfl⟩ : syracuseStep 4944215 = 7416323) B7416323
theorem B4059517 : Blo 1266451 4059517 := bstep (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) B1522319
theorem B4280795 : Blo 1266451 4280795 := bstep (se 1 (by rfl) ⟨3210596, by rfl⟩ : syracuseStep 4280795 = 6421193) B6421193
theorem B6418925 : Blo 1266451 6418925 := bstep (se 3 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 6418925 = 2407097) B2407097
theorem B2404903 : Blo 1266451 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B3609211 : Blo 1266451 3609211 := bstep (se 1 (by rfl) ⟨2706908, by rfl⟩ : syracuseStep 3609211 = 5413817) B5413817
theorem B4813451 : Blo 1266451 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B1266471 : Blo 1266451 1266471 := bstep (se 1 (by rfl) ⟨949853, by rfl⟩ : syracuseStep 1266471 = 1899707) B1899707
theorem B2167625 : Blo 1266451 2167625 := bstep (se 2 (by rfl) ⟨812859, by rfl⟩ : syracuseStep 2167625 = 1625719) B1625719
theorem B1266511 : Blo 1266451 1266511 := bstep (se 1 (by rfl) ⟨949883, by rfl⟩ : syracuseStep 1266511 = 1899767) B1899767
theorem B1266527 : Blo 1266451 1266527 := bstep (se 1 (by rfl) ⟨949895, by rfl⟩ : syracuseStep 1266527 = 1899791) B1899791
theorem B1266555 : Blo 1266451 1266555 := bstep (se 1 (by rfl) ⟨949916, by rfl⟩ : syracuseStep 1266555 = 1899833) B1899833
theorem B1266607 : Blo 1266451 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B3707831 : Blo 1266451 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B1266631 : Blo 1266451 1266631 := bstep (se 1 (by rfl) ⟨949973, by rfl⟩ : syracuseStep 1266631 = 1899947) B1899947
theorem B1266651 : Blo 1266451 1266651 := bstep (se 1 (by rfl) ⟨949988, by rfl⟩ : syracuseStep 1266651 = 1899977) B1899977
theorem B39040001 : Blo 1266451 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B1266727 : Blo 1266451 1266727 := bstep (se 1 (by rfl) ⟨950045, by rfl⟩ : syracuseStep 1266727 = 1900091) B1900091
theorem B14431283 : Blo 1266451 14431283 := bstep (se 1 (by rfl) ⟨10823462, by rfl⟩ : syracuseStep 14431283 = 21646925) B21646925
theorem B1266767 : Blo 1266451 1266767 := bstep (se 1 (by rfl) ⟨950075, by rfl⟩ : syracuseStep 1266767 = 1900151) B1900151
theorem B1266783 : Blo 1266451 1266783 := bstep (se 1 (by rfl) ⟨950087, by rfl⟩ : syracuseStep 1266783 = 1900175) B1900175
theorem B1266811 : Blo 1266451 1266811 := bstep (se 1 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 1266811 = 1900217) B1900217
theorem B1266863 : Blo 1266451 1266863 := bstep (se 1 (by rfl) ⟨950147, by rfl⟩ : syracuseStep 1266863 = 1900295) B1900295
theorem B1266887 : Blo 1266451 1266887 := bstep (se 1 (by rfl) ⟨950165, by rfl⟩ : syracuseStep 1266887 = 1900331) B1900331
theorem B1266907 : Blo 1266451 1266907 := bstep (se 1 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 1266907 = 1900361) B1900361
theorem B9622799 : Blo 1266451 9622799 := bstep (se 1 (by rfl) ⟨7217099, by rfl⟩ : syracuseStep 9622799 = 14434199) B14434199
theorem B13899023 : Blo 1266451 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B6419735 : Blo 1266451 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B1266983 : Blo 1266451 1266983 := bstep (se 1 (by rfl) ⟨950237, by rfl⟩ : syracuseStep 1266983 = 1900475) B1900475
theorem B1267023 : Blo 1266451 1267023 := bstep (se 1 (by rfl) ⟨950267, by rfl⟩ : syracuseStep 1267023 = 1900535) B1900535
theorem B1267039 : Blo 1266451 1267039 := bstep (se 1 (by rfl) ⟨950279, by rfl⟩ : syracuseStep 1267039 = 1900559) B1900559
theorem B1267067 : Blo 1266451 1267067 := bstep (se 1 (by rfl) ⟨950300, by rfl⟩ : syracuseStep 1267067 = 1900601) B1900601
theorem B1267119 : Blo 1266451 1267119 := bstep (se 1 (by rfl) ⟨950339, by rfl⟩ : syracuseStep 1267119 = 1900679) B1900679
theorem B1267143 : Blo 1266451 1267143 := bstep (se 1 (by rfl) ⟨950357, by rfl⟩ : syracuseStep 1267143 = 1900715) B1900715
theorem B1267163 : Blo 1266451 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B3610099 : Blo 1266451 3610099 := bstep (se 1 (by rfl) ⟨2707574, by rfl⟩ : syracuseStep 3610099 = 5415149) B5415149
theorem B1267239 : Blo 1266451 1267239 := bstep (se 1 (by rfl) ⟨950429, by rfl⟩ : syracuseStep 1267239 = 1900859) B1900859
theorem B1267279 : Blo 1266451 1267279 := bstep (se 1 (by rfl) ⟨950459, by rfl⟩ : syracuseStep 1267279 = 1900919) B1900919
theorem B1267295 : Blo 1266451 1267295 := bstep (se 1 (by rfl) ⟨950471, by rfl⟩ : syracuseStep 1267295 = 1900943) B1900943
theorem B1267323 : Blo 1266451 1267323 := bstep (se 1 (by rfl) ⟨950492, by rfl⟩ : syracuseStep 1267323 = 1900985) B1900985
theorem B1267375 : Blo 1266451 1267375 := bstep (se 1 (by rfl) ⟨950531, by rfl⟩ : syracuseStep 1267375 = 1901063) B1901063
theorem B1267399 : Blo 1266451 1267399 := bstep (se 1 (by rfl) ⟨950549, by rfl⟩ : syracuseStep 1267399 = 1901099) B1901099
theorem B3610327 : Blo 1266451 3610327 := bstep (se 1 (by rfl) ⟨2707745, by rfl⟩ : syracuseStep 3610327 = 5415491) B5415491
theorem B1267419 : Blo 1266451 1267419 := bstep (se 1 (by rfl) ⟨950564, by rfl⟩ : syracuseStep 1267419 = 1901129) B1901129
theorem B1267495 : Blo 1266451 1267495 := bstep (se 1 (by rfl) ⟨950621, by rfl⟩ : syracuseStep 1267495 = 1901243) B1901243
theorem B18528059 : Blo 1266451 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B9631547 : Blo 1266451 9631547 := bstep (se 1 (by rfl) ⟨7223660, by rfl⟩ : syracuseStep 9631547 = 14447321) B14447321
theorem B1267535 : Blo 1266451 1267535 := bstep (se 1 (by rfl) ⟨950651, by rfl⟩ : syracuseStep 1267535 = 1901303) B1901303
theorem B3045215 : Blo 1266451 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1267551 : Blo 1266451 1267551 := bstep (se 1 (by rfl) ⟨950663, by rfl⟩ : syracuseStep 1267551 = 1901327) B1901327
theorem B3708767 : Blo 1266451 3708767 := bstep (se 1 (by rfl) ⟨2781575, by rfl⟩ : syracuseStep 3708767 = 5563151) B5563151
theorem B4814711 : Blo 1266451 4814711 := bstep (se 1 (by rfl) ⟨3611033, by rfl⟩ : syracuseStep 4814711 = 7222067) B7222067
theorem B1267579 : Blo 1266451 1267579 := bstep (se 1 (by rfl) ⟨950684, by rfl⟩ : syracuseStep 1267579 = 1901369) B1901369
theorem B1267631 : Blo 1266451 1267631 := bstep (se 1 (by rfl) ⟨950723, by rfl⟩ : syracuseStep 1267631 = 1901447) B1901447
theorem B1267655 : Blo 1266451 1267655 := bstep (se 1 (by rfl) ⟨950741, by rfl⟩ : syracuseStep 1267655 = 1901483) B1901483
theorem B93829067 : Blo 1266451 93829067 := bstep (se 1 (by rfl) ⟨70371800, by rfl⟩ : syracuseStep 93829067 = 140743601) B140743601
theorem B1267675 : Blo 1266451 1267675 := bstep (se 1 (by rfl) ⟨950756, by rfl⟩ : syracuseStep 1267675 = 1901513) B1901513
theorem B1267751 : Blo 1266451 1267751 := bstep (se 1 (by rfl) ⟨950813, by rfl⟩ : syracuseStep 1267751 = 1901627) B1901627
theorem B1267791 : Blo 1266451 1267791 := bstep (se 1 (by rfl) ⟨950843, by rfl⟩ : syracuseStep 1267791 = 1901687) B1901687
theorem B1267807 : Blo 1266451 1267807 := bstep (se 1 (by rfl) ⟨950855, by rfl⟩ : syracuseStep 1267807 = 1901711) B1901711
theorem B1267835 : Blo 1266451 1267835 := bstep (se 1 (by rfl) ⟨950876, by rfl⟩ : syracuseStep 1267835 = 1901753) B1901753
theorem B6412445 : Blo 1266451 6412445 := bstep (se 3 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 6412445 = 2404667) B2404667
theorem B1267887 : Blo 1266451 1267887 := bstep (se 1 (by rfl) ⟨950915, by rfl⟩ : syracuseStep 1267887 = 1901831) B1901831
theorem B1267911 : Blo 1266451 1267911 := bstep (se 1 (by rfl) ⟨950933, by rfl⟩ : syracuseStep 1267911 = 1901867) B1901867
theorem B2406611 : Blo 1266451 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B1267931 : Blo 1266451 1267931 := bstep (se 1 (by rfl) ⟨950948, by rfl⟩ : syracuseStep 1267931 = 1901897) B1901897
theorem B4274423 : Blo 1266451 4274423 := bstep (se 1 (by rfl) ⟨3205817, by rfl⟩ : syracuseStep 4274423 = 6411635) B6411635
theorem B1268007 : Blo 1266451 1268007 := bstep (se 1 (by rfl) ⟨951005, by rfl⟩ : syracuseStep 1268007 = 1902011) B1902011
theorem B1268047 : Blo 1266451 1268047 := bstep (se 1 (by rfl) ⟨951035, by rfl⟩ : syracuseStep 1268047 = 1902071) B1902071
theorem B1268063 : Blo 1266451 1268063 := bstep (se 1 (by rfl) ⟨951047, by rfl⟩ : syracuseStep 1268063 = 1902095) B1902095
theorem B2406763 : Blo 1266451 2406763 := bstep (se 1 (by rfl) ⟨1805072, by rfl⟩ : syracuseStep 2406763 = 3610145) B3610145
theorem B1268091 : Blo 1266451 1268091 := bstep (se 1 (by rfl) ⟨951068, by rfl⟩ : syracuseStep 1268091 = 1902137) B1902137
theorem B3209615 : Blo 1266451 3209615 := bstep (se 1 (by rfl) ⟨2407211, by rfl⟩ : syracuseStep 3209615 = 4814423) B4814423
theorem B1268143 : Blo 1266451 1268143 := bstep (se 1 (by rfl) ⟨951107, by rfl⟩ : syracuseStep 1268143 = 1902215) B1902215
theorem B1268167 : Blo 1266451 1268167 := bstep (se 1 (by rfl) ⟨951125, by rfl⟩ : syracuseStep 1268167 = 1902251) B1902251
theorem B1268187 : Blo 1266451 1268187 := bstep (se 1 (by rfl) ⟨951140, by rfl⟩ : syracuseStep 1268187 = 1902281) B1902281
theorem B1268263 : Blo 1266451 1268263 := bstep (se 1 (by rfl) ⟨951197, by rfl⟩ : syracuseStep 1268263 = 1902395) B1902395
theorem B4274747 : Blo 1266451 4274747 := bstep (se 1 (by rfl) ⟨3206060, by rfl⟩ : syracuseStep 4274747 = 6412121) B6412121
theorem B2406991 : Blo 1266451 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B1268303 : Blo 1266451 1268303 := bstep (se 1 (by rfl) ⟨951227, by rfl⟩ : syracuseStep 1268303 = 1902455) B1902455
theorem B1268319 : Blo 1266451 1268319 := bstep (se 1 (by rfl) ⟨951239, by rfl⟩ : syracuseStep 1268319 = 1902479) B1902479
theorem B1268347 : Blo 1266451 1268347 := bstep (se 1 (by rfl) ⟨951260, by rfl⟩ : syracuseStep 1268347 = 1902521) B1902521
theorem B1268399 : Blo 1266451 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B34667185 : Blo 1266451 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B1268423 : Blo 1266451 1268423 := bstep (se 1 (by rfl) ⟨951317, by rfl⟩ : syracuseStep 1268423 = 1902635) B1902635
theorem B3046099 : Blo 1266451 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B3209939 : Blo 1266451 3209939 := bstep (se 1 (by rfl) ⟨2407454, by rfl⟩ : syracuseStep 3209939 = 4814909) B4814909
theorem B1268443 : Blo 1266451 1268443 := bstep (se 1 (by rfl) ⟨951332, by rfl⟩ : syracuseStep 1268443 = 1902665) B1902665
theorem B4815683 : Blo 1266451 4815683 := bstep (se 1 (by rfl) ⟨3611762, by rfl⟩ : syracuseStep 4815683 = 7223525) B7223525
theorem B4275017 : Blo 1266451 4275017 := bstep (se 2 (by rfl) ⟨1603131, by rfl⟩ : syracuseStep 4275017 = 3206263) B3206263
theorem B6421355 : Blo 1266451 6421355 := bstep (se 1 (by rfl) ⟨4816016, by rfl⟩ : syracuseStep 6421355 = 9632033) B9632033
theorem B55540657 : Blo 1266451 55540657 := bstep (se 2 (by rfl) ⟨20827746, by rfl⟩ : syracuseStep 55540657 = 41655493) B41655493
theorem B10828727 : Blo 1266451 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B2849723 : Blo 1266451 2849723 := bstep (se 1 (by rfl) ⟨2137292, by rfl⟩ : syracuseStep 2849723 = 4274585) B4274585
theorem B2849849 : Blo 1266451 2849849 := bstep (se 2 (by rfl) ⟨1068693, by rfl⟩ : syracuseStep 2849849 = 2137387) B2137387
theorem B2137259 : Blo 1266451 2137259 := bstep (se 1 (by rfl) ⟨1602944, by rfl⟩ : syracuseStep 2137259 = 3205889) B3205889
theorem B1899719 : Blo 1266451 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B1899881 : Blo 1266451 1899881 := bstep (se 2 (by rfl) ⟨712455, by rfl⟩ : syracuseStep 1899881 = 1424911) B1424911
theorem B2850191 : Blo 1266451 2850191 := bstep (se 1 (by rfl) ⟨2137643, by rfl⟩ : syracuseStep 2850191 = 4275287) B4275287
theorem B6413741 : Blo 1266451 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B1899959 : Blo 1266451 1899959 := bstep (se 1 (by rfl) ⟨1424969, by rfl⟩ : syracuseStep 1899959 = 2849939) B2849939
theorem B1899995 : Blo 1266451 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B2137657 : Blo 1266451 2137657 := bstep (se 2 (by rfl) ⟨801621, by rfl⟩ : syracuseStep 2137657 = 1603243) B1603243
theorem B1425019 : Blo 1266451 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B5135995 : Blo 1266451 5135995 := bstep (se 1 (by rfl) ⟨3851996, by rfl⟩ : syracuseStep 5135995 = 7703993) B7703993
theorem B5136011 : Blo 1266451 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B2137799 : Blo 1266451 2137799 := bstep (se 1 (by rfl) ⟨1603349, by rfl⟩ : syracuseStep 2137799 = 3206699) B3206699
theorem B2850515 : Blo 1266451 2850515 := bstep (se 1 (by rfl) ⟨2137886, by rfl⟩ : syracuseStep 2850515 = 4275773) B4275773
theorem B6504185 : Blo 1266451 6504185 := bstep (se 2 (by rfl) ⟨2439069, by rfl⟩ : syracuseStep 6504185 = 4878139) B4878139
theorem B2137961 : Blo 1266451 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B1900463 : Blo 1266451 1900463 := bstep (se 1 (by rfl) ⟨1425347, by rfl⟩ : syracuseStep 1900463 = 2850695) B2850695
theorem B4276151 : Blo 1266451 4276151 := bstep (se 1 (by rfl) ⟨3207113, by rfl⟩ : syracuseStep 4276151 = 6414227) B6414227
theorem B12173321 : Blo 1266451 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B1900649 : Blo 1266451 1900649 := bstep (se 2 (by rfl) ⟨712743, by rfl⟩ : syracuseStep 1900649 = 1425487) B1425487
theorem B1425703 : Blo 1266451 1425703 := bstep (se 1 (by rfl) ⟨1069277, by rfl⟩ : syracuseStep 1425703 = 2138555) B2138555
theorem B2851145 : Blo 1266451 2851145 := bstep (se 2 (by rfl) ⟨1069179, by rfl⟩ : syracuseStep 2851145 = 2138359) B2138359
theorem B2851163 : Blo 1266451 2851163 := bstep (se 1 (by rfl) ⟨2138372, by rfl⟩ : syracuseStep 2851163 = 4276745) B4276745
theorem B1425775 : Blo 1266451 1425775 := bstep (se 1 (by rfl) ⟨1069331, by rfl⟩ : syracuseStep 1425775 = 2138663) B2138663
theorem B1900967 : Blo 1266451 1900967 := bstep (se 1 (by rfl) ⟨1425725, by rfl⟩ : syracuseStep 1900967 = 2851451) B2851451
theorem B1901051 : Blo 1266451 1901051 := bstep (se 1 (by rfl) ⟨1425788, by rfl⟩ : syracuseStep 1901051 = 2851577) B2851577
theorem B1425991 : Blo 1266451 1425991 := bstep (se 1 (by rfl) ⟨1069493, by rfl⟩ : syracuseStep 1425991 = 2138987) B2138987
theorem B1901177 : Blo 1266451 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B4276907 : Blo 1266451 4276907 := bstep (se 1 (by rfl) ⟨3207680, by rfl⟩ : syracuseStep 4276907 = 6415361) B6415361
theorem B26026667 : Blo 1266451 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B1901231 : Blo 1266451 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B1901279 : Blo 1266451 1901279 := bstep (se 1 (by rfl) ⟨1425959, by rfl⟩ : syracuseStep 1901279 = 2851919) B2851919
theorem B6415199 : Blo 1266451 6415199 := bstep (se 1 (by rfl) ⟨4811399, by rfl⟩ : syracuseStep 6415199 = 9622799) B9622799
theorem B9266015 : Blo 1266451 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B2851739 : Blo 1266451 2851739 := bstep (se 1 (by rfl) ⟨2138804, by rfl⟩ : syracuseStep 2851739 = 4277609) B4277609
theorem B1901543 : Blo 1266451 1901543 := bstep (se 1 (by rfl) ⟨1426157, by rfl⟩ : syracuseStep 1901543 = 2852315) B2852315
theorem B6087737 : Blo 1266451 6087737 := bstep (se 2 (by rfl) ⟨2282901, by rfl⟩ : syracuseStep 6087737 = 4565803) B4565803
theorem B2851937 : Blo 1266451 2851937 := bstep (se 2 (by rfl) ⟨1069476, by rfl⟩ : syracuseStep 2851937 = 2138953) B2138953
theorem B4277447 : Blo 1266451 4277447 := bstep (se 1 (by rfl) ⟨3208085, by rfl⟩ : syracuseStep 4277447 = 6416171) B6416171
theorem B1901801 : Blo 1266451 1901801 := bstep (se 2 (by rfl) ⟨713175, by rfl⟩ : syracuseStep 1901801 = 1426351) B1426351
theorem B1901855 : Blo 1266451 1901855 := bstep (se 1 (by rfl) ⟨1426391, by rfl⟩ : syracuseStep 1901855 = 2852783) B2852783
theorem B2852135 : Blo 1266451 2852135 := bstep (se 1 (by rfl) ⟨2139101, by rfl⟩ : syracuseStep 2852135 = 4278203) B4278203
theorem B5784871 : Blo 1266451 5784871 := bstep (se 1 (by rfl) ⟨4338653, by rfl⟩ : syracuseStep 5784871 = 8677307) B8677307
theorem B1426855 : Blo 1266451 1426855 := bstep (se 1 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 1426855 = 2140283) B2140283
theorem B5776829 : Blo 1266451 5776829 := bstep (se 3 (by rfl) ⟨1083155, by rfl⟩ : syracuseStep 5776829 = 2166311) B2166311
theorem B1902023 : Blo 1266451 1902023 := bstep (se 1 (by rfl) ⟨1426517, by rfl⟩ : syracuseStep 1902023 = 2853035) B2853035
theorem B2139743 : Blo 1266451 2139743 := bstep (se 1 (by rfl) ⟨1604807, by rfl⟩ : syracuseStep 2139743 = 3209615) B3209615
theorem B2852513 : Blo 1266451 2852513 := bstep (se 2 (by rfl) ⟨1069692, by rfl⟩ : syracuseStep 2852513 = 2139385) B2139385
theorem B1902377 : Blo 1266451 1902377 := bstep (se 2 (by rfl) ⟨713391, by rfl⟩ : syracuseStep 1902377 = 1426783) B1426783
theorem B1902383 : Blo 1266451 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B2139959 : Blo 1266451 2139959 := bstep (se 1 (by rfl) ⟨1604969, by rfl⟩ : syracuseStep 2139959 = 3209939) B3209939
theorem B7219151 : Blo 1266451 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B2852873 : Blo 1266451 2852873 := bstep (se 2 (by rfl) ⟨1069827, by rfl⟩ : syracuseStep 2852873 = 2139655) B2139655
theorem B49408157 : Blo 1266451 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B8120573 : Blo 1266451 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B9890045 : Blo 1266451 9890045 := bstep (se 3 (by rfl) ⟨1854383, by rfl⟩ : syracuseStep 9890045 = 3708767) B3708767
theorem B2853287 : Blo 1266451 2853287 := bstep (se 1 (by rfl) ⟨2139965, by rfl⟩ : syracuseStep 2853287 = 4279931) B4279931
theorem B13191635 : Blo 1266451 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B4336123 : Blo 1266451 4336123 := bstep (se 1 (by rfl) ⟨3252092, by rfl⟩ : syracuseStep 4336123 = 6504185) B6504185
theorem B2853395 : Blo 1266451 2853395 := bstep (se 1 (by rfl) ⟨2140046, by rfl⟩ : syracuseStep 2853395 = 4280093) B4280093
theorem B2853449 : Blo 1266451 2853449 := bstep (se 2 (by rfl) ⟨1070043, by rfl⟩ : syracuseStep 2853449 = 2140087) B2140087
theorem B4278959 : Blo 1266451 4278959 := bstep (se 1 (by rfl) ⟨3209219, by rfl⟩ : syracuseStep 4278959 = 6418439) B6418439
theorem B6417143 : Blo 1266451 6417143 := bstep (se 1 (by rfl) ⟨4812857, by rfl⟩ : syracuseStep 6417143 = 9625715) B9625715
theorem B3296143 : Blo 1266451 3296143 := bstep (se 1 (by rfl) ⟨2472107, by rfl⟩ : syracuseStep 3296143 = 4944215) B4944215
theorem B2853863 : Blo 1266451 2853863 := bstep (se 1 (by rfl) ⟨2140397, by rfl⟩ : syracuseStep 2853863 = 4280795) B4280795
theorem B4279283 : Blo 1266451 4279283 := bstep (se 1 (by rfl) ⟨3209462, by rfl⟩ : syracuseStep 4279283 = 6418925) B6418925
theorem B4631591 : Blo 1266451 4631591 := bstep (se 1 (by rfl) ⟨3473693, by rfl⟩ : syracuseStep 4631591 = 6947387) B6947387
theorem B1445083 : Blo 1266451 1445083 := bstep (se 1 (by rfl) ⟨1083812, by rfl⟩ : syracuseStep 1445083 = 2167625) B2167625
theorem B6417629 : Blo 1266451 6417629 := bstep (se 3 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 6417629 = 2406611) B2406611
theorem B9620855 : Blo 1266451 9620855 := bstep (se 1 (by rfl) ⟨7215641, by rfl⟩ : syracuseStep 9620855 = 14431283) B14431283
theorem B7220609 : Blo 1266451 7220609 := bstep (se 2 (by rfl) ⟨2707728, by rfl⟩ : syracuseStep 7220609 = 5415457) B5415457
theorem B3206537 : Blo 1266451 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B3206587 : Blo 1266451 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B4812281 : Blo 1266451 4812281 := bstep (se 2 (by rfl) ⟨1804605, by rfl⟩ : syracuseStep 4812281 = 3609211) B3609211
theorem B4279823 : Blo 1266451 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B13897277 : Blo 1266451 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B46222913 : Blo 1266451 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B4566611 : Blo 1266451 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B3206891 : Blo 1266451 3206891 := bstep (se 1 (by rfl) ⟨2405168, by rfl⟩ : syracuseStep 3206891 = 4810337) B4810337
theorem B4337449 : Blo 1266451 4337449 := bstep (se 2 (by rfl) ⟨1626543, by rfl⟩ : syracuseStep 4337449 = 3253087) B3253087
theorem B23113795 : Blo 1266451 23113795 := bstep (se 1 (by rfl) ⟨17335346, by rfl⟩ : syracuseStep 23113795 = 34670693) B34670693
theorem B13709483 : Blo 1266451 13709483 := bstep (se 1 (by rfl) ⟨10282112, by rfl⟩ : syracuseStep 13709483 = 20564225) B20564225
theorem B2929007 : Blo 1266451 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B2404819 : Blo 1266451 2404819 := bstep (se 1 (by rfl) ⟨1803614, by rfl⟩ : syracuseStep 2404819 = 3607229) B3607229
theorem B4280903 : Blo 1266451 4280903 := bstep (se 1 (by rfl) ⟨3210677, by rfl⟩ : syracuseStep 4280903 = 6421355) B6421355
theorem B4813465 : Blo 1266451 4813465 := bstep (se 2 (by rfl) ⟨1805049, by rfl⟩ : syracuseStep 4813465 = 3610099) B3610099
theorem B2405047 : Blo 1266451 2405047 := bstep (se 1 (by rfl) ⟨1803785, by rfl⟩ : syracuseStep 2405047 = 3607571) B3607571
theorem B3207863 : Blo 1266451 3207863 := bstep (se 1 (by rfl) ⟨2405897, by rfl⟩ : syracuseStep 3207863 = 4811795) B4811795
theorem B1266479 : Blo 1266451 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B1266587 : Blo 1266451 1266587 := bstep (se 1 (by rfl) ⟨949940, by rfl⟩ : syracuseStep 1266587 = 1899881) B1899881
theorem B4813769 : Blo 1266451 4813769 := bstep (se 2 (by rfl) ⟨1805163, by rfl⟩ : syracuseStep 4813769 = 3610327) B3610327
theorem B1266639 : Blo 1266451 1266639 := bstep (se 1 (by rfl) ⟨949979, by rfl⟩ : syracuseStep 1266639 = 1899959) B1899959
theorem B1266663 : Blo 1266451 1266663 := bstep (se 1 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 1266663 = 1899995) B1899995
theorem B2405351 : Blo 1266451 2405351 := bstep (se 1 (by rfl) ⟨1804013, by rfl⟩ : syracuseStep 2405351 = 3608027) B3608027
theorem B10826743 : Blo 1266451 10826743 := bstep (se 1 (by rfl) ⟨8120057, by rfl⟩ : syracuseStep 10826743 = 16240115) B16240115
theorem B2405609 : Blo 1266451 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B1266975 : Blo 1266451 1266975 := bstep (se 1 (by rfl) ⟨950231, by rfl⟩ : syracuseStep 1266975 = 1900463) B1900463
theorem B7222567 : Blo 1266451 7222567 := bstep (se 1 (by rfl) ⟨5416925, by rfl⟩ : syracuseStep 7222567 = 10833851) B10833851
theorem B1267035 : Blo 1266451 1267035 := bstep (se 1 (by rfl) ⟨950276, by rfl⟩ : syracuseStep 1267035 = 1900553) B1900553
theorem B1267055 : Blo 1266451 1267055 := bstep (se 1 (by rfl) ⟨950291, by rfl⟩ : syracuseStep 1267055 = 1900583) B1900583
theorem B5207435 : Blo 1266451 5207435 := bstep (se 1 (by rfl) ⟨3905576, by rfl⟩ : syracuseStep 5207435 = 7811153) B7811153
theorem B3855755 : Blo 1266451 3855755 := bstep (se 1 (by rfl) ⟨2891816, by rfl⟩ : syracuseStep 3855755 = 5783633) B5783633
theorem B7714187 : Blo 1266451 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B1267111 : Blo 1266451 1267111 := bstep (se 1 (by rfl) ⟨950333, by rfl⟩ : syracuseStep 1267111 = 1900667) B1900667
theorem B11564491 : Blo 1266451 11564491 := bstep (se 1 (by rfl) ⟨8673368, by rfl⟩ : syracuseStep 11564491 = 17346737) B17346737
theorem B1267195 : Blo 1266451 1267195 := bstep (se 1 (by rfl) ⟨950396, by rfl⟩ : syracuseStep 1267195 = 1900793) B1900793
theorem B1267263 : Blo 1266451 1267263 := bstep (se 1 (by rfl) ⟨950447, by rfl⟩ : syracuseStep 1267263 = 1900895) B1900895
theorem B1267271 : Blo 1266451 1267271 := bstep (se 1 (by rfl) ⟨950453, by rfl⟩ : syracuseStep 1267271 = 1900907) B1900907
theorem B7214777 : Blo 1266451 7214777 := bstep (se 2 (by rfl) ⟨2705541, by rfl⟩ : syracuseStep 7214777 = 5411083) B5411083
theorem B1267423 : Blo 1266451 1267423 := bstep (se 1 (by rfl) ⟨950567, by rfl⟩ : syracuseStep 1267423 = 1901135) B1901135
theorem B3208967 : Blo 1266451 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B1267503 : Blo 1266451 1267503 := bstep (se 1 (by rfl) ⟨950627, by rfl⟩ : syracuseStep 1267503 = 1901255) B1901255
theorem B3209017 : Blo 1266451 3209017 := bstep (se 2 (by rfl) ⟨1203381, by rfl⟩ : syracuseStep 3209017 = 2406763) B2406763
theorem B5412689 : Blo 1266451 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B1267611 : Blo 1266451 1267611 := bstep (se 1 (by rfl) ⟨950708, by rfl⟩ : syracuseStep 1267611 = 1901417) B1901417
theorem B2471887 : Blo 1266451 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B1267663 : Blo 1266451 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B1267687 : Blo 1266451 1267687 := bstep (se 1 (by rfl) ⟨950765, by rfl⟩ : syracuseStep 1267687 = 1901531) B1901531
theorem B2406505 : Blo 1266451 2406505 := bstep (se 2 (by rfl) ⟨902439, by rfl⟩ : syracuseStep 2406505 = 1804879) B1804879
theorem B3209321 : Blo 1266451 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B27400355 : Blo 1266451 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B2406665 : Blo 1266451 2406665 := bstep (se 2 (by rfl) ⟨902499, by rfl⟩ : syracuseStep 2406665 = 1804999) B1804999
theorem B4061465 : Blo 1266451 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B1267999 : Blo 1266451 1267999 := bstep (se 1 (by rfl) ⟨950999, by rfl⟩ : syracuseStep 1267999 = 1901999) B1901999
theorem B10975565 : Blo 1266451 10975565 := bstep (se 3 (by rfl) ⟨2057918, by rfl⟩ : syracuseStep 10975565 = 4115837) B4115837
theorem B1268059 : Blo 1266451 1268059 := bstep (se 1 (by rfl) ⟨951044, by rfl⟩ : syracuseStep 1268059 = 1902089) B1902089
theorem B1268079 : Blo 1266451 1268079 := bstep (se 1 (by rfl) ⟨951059, by rfl⟩ : syracuseStep 1268079 = 1902119) B1902119
theorem B1268135 : Blo 1266451 1268135 := bstep (se 1 (by rfl) ⟨951101, by rfl⟩ : syracuseStep 1268135 = 1902203) B1902203
theorem B1268219 : Blo 1266451 1268219 := bstep (se 1 (by rfl) ⟨951164, by rfl⟩ : syracuseStep 1268219 = 1902329) B1902329
theorem B6421031 : Blo 1266451 6421031 := bstep (se 1 (by rfl) ⟨4815773, by rfl⟩ : syracuseStep 6421031 = 9631547) B9631547
theorem B1268287 : Blo 1266451 1268287 := bstep (se 1 (by rfl) ⟨951215, by rfl⟩ : syracuseStep 1268287 = 1902431) B1902431
theorem B74054209 : Blo 1266451 74054209 := bstep (se 2 (by rfl) ⟨27770328, by rfl⟩ : syracuseStep 74054209 = 55540657) B55540657
theorem B1268295 : Blo 1266451 1268295 := bstep (se 1 (by rfl) ⟨951221, by rfl⟩ : syracuseStep 1268295 = 1902443) B1902443
theorem B3209807 : Blo 1266451 3209807 := bstep (se 1 (by rfl) ⟨2407355, by rfl⟩ : syracuseStep 3209807 = 4814711) B4814711
theorem B62552711 : Blo 1266451 62552711 := bstep (se 1 (by rfl) ⟨46914533, by rfl⟩ : syracuseStep 62552711 = 93829067) B93829067
theorem B1268447 : Blo 1266451 1268447 := bstep (se 1 (by rfl) ⟨951335, by rfl⟩ : syracuseStep 1268447 = 1902671) B1902671
theorem B4274963 : Blo 1266451 4274963 := bstep (se 1 (by rfl) ⟨3206222, by rfl⟩ : syracuseStep 4274963 = 6412445) B6412445
theorem B2849615 : Blo 1266451 2849615 := bstep (se 1 (by rfl) ⟨2137211, by rfl⟩ : syracuseStep 2849615 = 4274423) B4274423
theorem B2849831 : Blo 1266451 2849831 := bstep (se 1 (by rfl) ⟨2137373, by rfl⟩ : syracuseStep 2849831 = 4274747) B4274747
theorem B3087503 : Blo 1266451 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B12172477 : Blo 1266451 12172477 := bstep (se 3 (by rfl) ⟨2282339, by rfl⟩ : syracuseStep 12172477 = 4564679) B4564679
theorem B3210455 : Blo 1266451 3210455 := bstep (se 1 (by rfl) ⟨2407841, by rfl⟩ : syracuseStep 3210455 = 4815683) B4815683
theorem B2850011 : Blo 1266451 2850011 := bstep (se 1 (by rfl) ⟨2137508, by rfl⟩ : syracuseStep 2850011 = 4275017) B4275017
theorem B6413579 : Blo 1266451 6413579 := bstep (se 1 (by rfl) ⟨4810184, by rfl⟩ : syracuseStep 6413579 = 9620369) B9620369
theorem B1899815 : Blo 1266451 1899815 := bstep (se 1 (by rfl) ⟨1424861, by rfl⟩ : syracuseStep 1899815 = 2849723) B2849723
theorem B1899899 : Blo 1266451 1899899 := bstep (se 1 (by rfl) ⟨1424924, by rfl⟩ : syracuseStep 1899899 = 2849849) B2849849
theorem B3661193 : Blo 1266451 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B2850209 : Blo 1266451 2850209 := bstep (se 2 (by rfl) ⟨1068828, by rfl⟩ : syracuseStep 2850209 = 2137657) B2137657
theorem B6086087 : Blo 1266451 6086087 := bstep (se 1 (by rfl) ⟨4564565, by rfl⟩ : syracuseStep 6086087 = 9129131) B9129131
theorem B1424839 : Blo 1266451 1424839 := bstep (se 1 (by rfl) ⟨1068629, by rfl⟩ : syracuseStep 1424839 = 2137259) B2137259
theorem B1900025 : Blo 1266451 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B6847993 : Blo 1266451 6847993 := bstep (se 2 (by rfl) ⟨2567997, by rfl⟩ : syracuseStep 6847993 = 5135995) B5135995
theorem B4570705 : Blo 1266451 4570705 := bstep (se 2 (by rfl) ⟨1714014, by rfl⟩ : syracuseStep 4570705 = 3428029) B3428029
theorem B1900127 : Blo 1266451 1900127 := bstep (se 1 (by rfl) ⟨1425095, by rfl⟩ : syracuseStep 1900127 = 2850191) B2850191
theorem B7216735 : Blo 1266451 7216735 := bstep (se 1 (by rfl) ⟨5412551, by rfl⟩ : syracuseStep 7216735 = 10825103) B10825103
theorem B4275827 : Blo 1266451 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B6086353 : Blo 1266451 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B3424007 : Blo 1266451 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B1425199 : Blo 1266451 1425199 := bstep (se 1 (by rfl) ⟨1068899, by rfl⟩ : syracuseStep 1425199 = 2137799) B2137799
theorem B1900343 : Blo 1266451 1900343 := bstep (se 1 (by rfl) ⟨1425257, by rfl⟩ : syracuseStep 1900343 = 2850515) B2850515
theorem B4570937 : Blo 1266451 4570937 := bstep (se 2 (by rfl) ⟨1714101, by rfl⟩ : syracuseStep 4570937 = 3428203) B3428203
theorem B1466191 : Blo 1266451 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B4276097 : Blo 1266451 4276097 := bstep (se 2 (by rfl) ⟨1603536, by rfl⟩ : syracuseStep 4276097 = 3207073) B3207073
theorem B1425307 : Blo 1266451 1425307 := bstep (se 1 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 1425307 = 2137961) B2137961
theorem B4808605 : Blo 1266451 4808605 := bstep (se 3 (by rfl) ⟨901613, by rfl⟩ : syracuseStep 4808605 = 1803227) B1803227
theorem B2850767 : Blo 1266451 2850767 := bstep (se 1 (by rfl) ⟨2138075, by rfl⟩ : syracuseStep 2850767 = 4276151) B4276151
theorem B30818393 : Blo 1266451 30818393 := bstep (se 2 (by rfl) ⟨11556897, by rfl⟩ : syracuseStep 30818393 = 23113795) B23113795
theorem B1900763 : Blo 1266451 1900763 := bstep (se 1 (by rfl) ⟨1425572, by rfl⟩ : syracuseStep 1900763 = 2851145) B2851145
theorem B1900775 : Blo 1266451 1900775 := bstep (se 1 (by rfl) ⟨1425581, by rfl⟩ : syracuseStep 1900775 = 2851163) B2851163
theorem B1900937 : Blo 1266451 1900937 := bstep (se 2 (by rfl) ⟨712851, by rfl⟩ : syracuseStep 1900937 = 1425703) B1425703
theorem B2851271 : Blo 1266451 2851271 := bstep (se 1 (by rfl) ⟨2138453, by rfl⟩ : syracuseStep 2851271 = 4276907) B4276907
theorem B17351111 : Blo 1266451 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B2138575 : Blo 1266451 2138575 := bstep (se 1 (by rfl) ⟨1603931, by rfl⟩ : syracuseStep 2138575 = 3207863) B3207863
theorem B1901033 : Blo 1266451 1901033 := bstep (se 2 (by rfl) ⟨712887, by rfl⟩ : syracuseStep 1901033 = 1425775) B1425775
theorem B4276799 : Blo 1266451 4276799 := bstep (se 1 (by rfl) ⟨3207599, by rfl⟩ : syracuseStep 4276799 = 6415199) B6415199
theorem B1901159 : Blo 1266451 1901159 := bstep (se 1 (by rfl) ⟨1425869, by rfl⟩ : syracuseStep 1901159 = 2851739) B2851739
theorem B1901291 : Blo 1266451 1901291 := bstep (se 1 (by rfl) ⟨1425968, by rfl⟩ : syracuseStep 1901291 = 2851937) B2851937
theorem B98738945 : Blo 1266451 98738945 := bstep (se 2 (by rfl) ⟨37027104, by rfl⟩ : syracuseStep 98738945 = 74054209) B74054209
theorem B1901321 : Blo 1266451 1901321 := bstep (se 2 (by rfl) ⟨712995, by rfl⟩ : syracuseStep 1901321 = 1425991) B1425991
theorem B2851631 : Blo 1266451 2851631 := bstep (se 1 (by rfl) ⟨2138723, by rfl⟩ : syracuseStep 2851631 = 4277447) B4277447
theorem B1901423 : Blo 1266451 1901423 := bstep (se 1 (by rfl) ⟨1426067, by rfl⟩ : syracuseStep 1901423 = 2852135) B2852135
theorem B3851219 : Blo 1266451 3851219 := bstep (se 1 (by rfl) ⟨2888414, by rfl⟩ : syracuseStep 3851219 = 5776829) B5776829
theorem B1426495 : Blo 1266451 1426495 := bstep (se 1 (by rfl) ⟨1069871, by rfl⟩ : syracuseStep 1426495 = 2139743) B2139743
theorem B1901675 : Blo 1266451 1901675 := bstep (se 1 (by rfl) ⟨1426256, by rfl⟩ : syracuseStep 1901675 = 2852513) B2852513
theorem B4809851 : Blo 1266451 4809851 := bstep (se 1 (by rfl) ⟨3607388, by rfl⟩ : syracuseStep 4809851 = 7214777) B7214777
theorem B2139311 : Blo 1266451 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B1426639 : Blo 1266451 1426639 := bstep (se 1 (by rfl) ⟨1069979, by rfl⟩ : syracuseStep 1426639 = 2139959) B2139959
theorem B14435657 : Blo 1266451 14435657 := bstep (se 2 (by rfl) ⟨5413371, by rfl⟩ : syracuseStep 14435657 = 10826743) B10826743
theorem B1901915 : Blo 1266451 1901915 := bstep (se 1 (by rfl) ⟨1426436, by rfl⟩ : syracuseStep 1901915 = 2852873) B2852873
theorem B2139547 : Blo 1266451 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B16229969 : Blo 1266451 16229969 := bstep (se 2 (by rfl) ⟨6086238, by rfl⟩ : syracuseStep 16229969 = 12172477) B12172477
theorem B1902191 : Blo 1266451 1902191 := bstep (se 1 (by rfl) ⟨1426643, by rfl⟩ : syracuseStep 1902191 = 2853287) B2853287
theorem B1902263 : Blo 1266451 1902263 := bstep (se 1 (by rfl) ⟨1426697, by rfl⟩ : syracuseStep 1902263 = 2853395) B2853395
theorem B1902299 : Blo 1266451 1902299 := bstep (se 1 (by rfl) ⟨1426724, by rfl⟩ : syracuseStep 1902299 = 2853449) B2853449
theorem B2139871 : Blo 1266451 2139871 := bstep (se 1 (by rfl) ⟨1604903, by rfl⟩ : syracuseStep 2139871 = 3209807) B3209807
theorem B2852639 : Blo 1266451 2852639 := bstep (se 1 (by rfl) ⟨2139479, by rfl⟩ : syracuseStep 2852639 = 4278959) B4278959
theorem B4278095 : Blo 1266451 4278095 := bstep (se 1 (by rfl) ⟨3208571, by rfl⟩ : syracuseStep 4278095 = 6417143) B6417143
theorem B1902473 : Blo 1266451 1902473 := bstep (se 2 (by rfl) ⟨713427, by rfl⟩ : syracuseStep 1902473 = 1426855) B1426855
theorem B15419321 : Blo 1266451 15419321 := bstep (se 2 (by rfl) ⟨5782245, by rfl⟩ : syracuseStep 15419321 = 11564491) B11564491
theorem B1902575 : Blo 1266451 1902575 := bstep (se 1 (by rfl) ⟨1426931, by rfl⟩ : syracuseStep 1902575 = 2853863) B2853863
theorem B2852855 : Blo 1266451 2852855 := bstep (se 1 (by rfl) ⟨2139641, by rfl⟩ : syracuseStep 2852855 = 4279283) B4279283
theorem B2058335 : Blo 1266451 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B2140303 : Blo 1266451 2140303 := bstep (se 1 (by rfl) ⟨1605227, by rfl⟩ : syracuseStep 2140303 = 3210455) B3210455
theorem B4278419 : Blo 1266451 4278419 := bstep (se 1 (by rfl) ⟨3208814, by rfl⟩ : syracuseStep 4278419 = 6417629) B6417629
theorem B24709373 : Blo 1266451 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B4057391 : Blo 1266451 4057391 := bstep (se 1 (by rfl) ⟨3043043, by rfl⟩ : syracuseStep 4057391 = 6086087) B6086087
theorem B2853215 : Blo 1266451 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B4278689 : Blo 1266451 4278689 := bstep (se 2 (by rfl) ⟨1604508, by rfl⟩ : syracuseStep 4278689 = 3209017) B3209017
theorem B13183397 : Blo 1266451 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B1952671 : Blo 1266451 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B2853935 : Blo 1266451 2853935 := bstep (se 1 (by rfl) ⟨2140451, by rfl⟩ : syracuseStep 2853935 = 4280903) B4280903
theorem B131755085 : Blo 1266451 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B3206425 : Blo 1266451 3206425 := bstep (se 2 (by rfl) ⟨1202409, by rfl⟩ : syracuseStep 3206425 = 2404819) B2404819
theorem B6417953 : Blo 1266451 6417953 := bstep (se 2 (by rfl) ⟨2406732, by rfl⟩ : syracuseStep 6417953 = 4813465) B4813465
theorem B3206729 : Blo 1266451 3206729 := bstep (se 2 (by rfl) ⟨1202523, by rfl⟩ : syracuseStep 3206729 = 2405047) B2405047
theorem B4394857 : Blo 1266451 4394857 := bstep (se 2 (by rfl) ⟨1648071, by rfl⟩ : syracuseStep 4394857 = 3296143) B3296143
theorem B3608459 : Blo 1266451 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B4812767 : Blo 1266451 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B2707643 : Blo 1266451 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B8794423 : Blo 1266451 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B4280687 : Blo 1266451 4280687 := bstep (se 1 (by rfl) ⟨3210515, by rfl⟩ : syracuseStep 4280687 = 6421031) B6421031
theorem B9630089 : Blo 1266451 9630089 := bstep (se 2 (by rfl) ⟨3611283, by rfl⟩ : syracuseStep 9630089 = 7222567) B7222567
theorem B7713161 : Blo 1266451 7713161 := bstep (se 2 (by rfl) ⟨2892435, by rfl⟩ : syracuseStep 7713161 = 5784871) B5784871
theorem B7819685 : Blo 1266451 7819685 := bstep (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) B1466191
theorem B41701807 : Blo 1266451 41701807 := bstep (se 1 (by rfl) ⟨31276355, by rfl⟩ : syracuseStep 41701807 = 62552711) B62552711
theorem B9130657 : Blo 1266451 9130657 := bstep (se 2 (by rfl) ⟨3423996, by rfl⟩ : syracuseStep 9130657 = 6847993) B6847993
theorem B9622313 : Blo 1266451 9622313 := bstep (se 2 (by rfl) ⟨3608367, by rfl⟩ : syracuseStep 9622313 = 7216735) B7216735
theorem B1266543 : Blo 1266451 1266543 := bstep (se 1 (by rfl) ⟨949907, by rfl⟩ : syracuseStep 1266543 = 1899815) B1899815
theorem B1266599 : Blo 1266451 1266599 := bstep (se 1 (by rfl) ⟨949949, by rfl⟩ : syracuseStep 1266599 = 1899899) B1899899
theorem B4813739 : Blo 1266451 4813739 := bstep (se 1 (by rfl) ⟨3610304, by rfl⟩ : syracuseStep 4813739 = 7220609) B7220609
theorem B8115137 : Blo 1266451 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B1266683 : Blo 1266451 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B3208187 : Blo 1266451 3208187 := bstep (se 1 (by rfl) ⟨2406140, by rfl⟩ : syracuseStep 3208187 = 4812281) B4812281
theorem B30815275 : Blo 1266451 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B3044407 : Blo 1266451 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B1266751 : Blo 1266451 1266751 := bstep (se 1 (by rfl) ⟨950063, by rfl⟩ : syracuseStep 1266751 = 1900127) B1900127
theorem B2282671 : Blo 1266451 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B1266895 : Blo 1266451 1266895 := bstep (se 1 (by rfl) ⟨950171, by rfl⟩ : syracuseStep 1266895 = 1900343) B1900343
theorem B6411473 : Blo 1266451 6411473 := bstep (se 2 (by rfl) ⟨2404302, by rfl⟩ : syracuseStep 6411473 = 4808605) B4808605
theorem B8115547 : Blo 1266451 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1267099 : Blo 1266451 1267099 := bstep (se 1 (by rfl) ⟨950324, by rfl⟩ : syracuseStep 1267099 = 1900649) B1900649
theorem B9139655 : Blo 1266451 9139655 := bstep (se 1 (by rfl) ⟨6854741, by rfl⟩ : syracuseStep 9139655 = 13709483) B13709483
theorem B3208673 : Blo 1266451 3208673 := bstep (se 2 (by rfl) ⟨1203252, by rfl⟩ : syracuseStep 3208673 = 2406505) B2406505
theorem B16233965 : Blo 1266451 16233965 := bstep (se 3 (by rfl) ⟨3043868, by rfl⟩ : syracuseStep 16233965 = 6087737) B6087737
theorem B1267311 : Blo 1266451 1267311 := bstep (se 1 (by rfl) ⟨950483, by rfl⟩ : syracuseStep 1267311 = 1900967) B1900967
theorem B1267367 : Blo 1266451 1267367 := bstep (se 1 (by rfl) ⟨950525, by rfl⟩ : syracuseStep 1267367 = 1901051) B1901051
theorem B1267451 : Blo 1266451 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B1267487 : Blo 1266451 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B1267519 : Blo 1266451 1267519 := bstep (se 1 (by rfl) ⟨950639, by rfl⟩ : syracuseStep 1267519 = 1901279) B1901279
theorem B3209179 : Blo 1266451 3209179 := bstep (se 1 (by rfl) ⟨2406884, by rfl⟩ : syracuseStep 3209179 = 4813769) B4813769
theorem B1603567 : Blo 1266451 1603567 := bstep (se 1 (by rfl) ⟨1202675, by rfl⟩ : syracuseStep 1603567 = 2405351) B2405351
theorem B1267695 : Blo 1266451 1267695 := bstep (se 1 (by rfl) ⟨950771, by rfl⟩ : syracuseStep 1267695 = 1901543) B1901543
theorem B5781497 : Blo 1266451 5781497 := bstep (se 2 (by rfl) ⟨2168061, by rfl⟩ : syracuseStep 5781497 = 4336123) B4336123
theorem B1603739 : Blo 1266451 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B1267867 : Blo 1266451 1267867 := bstep (se 1 (by rfl) ⟨950900, by rfl⟩ : syracuseStep 1267867 = 1901801) B1901801
theorem B1267903 : Blo 1266451 1267903 := bstep (se 1 (by rfl) ⟨950927, by rfl⟩ : syracuseStep 1267903 = 1901855) B1901855
theorem B29268173 : Blo 1266451 29268173 := bstep (se 3 (by rfl) ⟨5487782, by rfl⟩ : syracuseStep 29268173 = 10975565) B10975565
theorem B3471623 : Blo 1266451 3471623 := bstep (se 1 (by rfl) ⟨2603717, by rfl⟩ : syracuseStep 3471623 = 5207435) B5207435
theorem B2570503 : Blo 1266451 2570503 := bstep (se 1 (by rfl) ⟨1927877, by rfl⟩ : syracuseStep 2570503 = 3855755) B3855755
theorem B5142791 : Blo 1266451 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B1268015 : Blo 1266451 1268015 := bstep (se 1 (by rfl) ⟨951011, by rfl⟩ : syracuseStep 1268015 = 1902023) B1902023
theorem B7707109 : Blo 1266451 7707109 := bstep (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) B1445083
theorem B1268251 : Blo 1266451 1268251 := bstep (se 1 (by rfl) ⟨951188, by rfl⟩ : syracuseStep 1268251 = 1902377) B1902377
theorem B1268255 : Blo 1266451 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B18266903 : Blo 1266451 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B5413715 : Blo 1266451 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B6593363 : Blo 1266451 6593363 := bstep (se 1 (by rfl) ⟨4945022, by rfl⟩ : syracuseStep 6593363 = 9890045) B9890045
theorem B1604443 : Blo 1266451 1604443 := bstep (se 1 (by rfl) ⟨1203332, by rfl⟩ : syracuseStep 1604443 = 2406665) B2406665
theorem B23133061 : Blo 1266451 23133061 := bstep (se 4 (by rfl) ⟨2168724, by rfl⟩ : syracuseStep 23133061 = 4337449) B4337449
theorem B2849975 : Blo 1266451 2849975 := bstep (se 1 (by rfl) ⟨2137481, by rfl⟩ : syracuseStep 2849975 = 4274963) B4274963
theorem B1899743 : Blo 1266451 1899743 := bstep (se 1 (by rfl) ⟨1424807, by rfl⟩ : syracuseStep 1899743 = 2849615) B2849615
theorem B4275449 : Blo 1266451 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B1899785 : Blo 1266451 1899785 := bstep (se 2 (by rfl) ⟨712419, by rfl⟩ : syracuseStep 1899785 = 1424839) B1424839
theorem B1899887 : Blo 1266451 1899887 := bstep (se 1 (by rfl) ⟨1424915, by rfl⟩ : syracuseStep 1899887 = 2849831) B2849831
theorem B3087727 : Blo 1266451 3087727 := bstep (se 1 (by rfl) ⟨2315795, by rfl⟩ : syracuseStep 3087727 = 4631591) B4631591
theorem B6094273 : Blo 1266451 6094273 := bstep (se 2 (by rfl) ⟨2285352, by rfl⟩ : syracuseStep 6094273 = 4570705) B4570705
theorem B1900007 : Blo 1266451 1900007 := bstep (se 1 (by rfl) ⟨1425005, by rfl⟩ : syracuseStep 1900007 = 2850011) B2850011
theorem B4275719 : Blo 1266451 4275719 := bstep (se 1 (by rfl) ⟨3206789, by rfl⟩ : syracuseStep 4275719 = 6413579) B6413579
theorem B6413903 : Blo 1266451 6413903 := bstep (se 1 (by rfl) ⟨4810427, by rfl⟩ : syracuseStep 6413903 = 9620855) B9620855
theorem B2137691 : Blo 1266451 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B2440795 : Blo 1266451 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B1900139 : Blo 1266451 1900139 := bstep (se 1 (by rfl) ⟨1425104, by rfl⟩ : syracuseStep 1900139 = 2850209) B2850209
theorem B9264851 : Blo 1266451 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B1900265 : Blo 1266451 1900265 := bstep (se 2 (by rfl) ⟨712599, by rfl⟩ : syracuseStep 1900265 = 1425199) B1425199
theorem B2850551 : Blo 1266451 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B2137927 : Blo 1266451 2137927 := bstep (se 1 (by rfl) ⟨1603445, by rfl⟩ : syracuseStep 2137927 = 3206891) B3206891
theorem B1900409 : Blo 1266451 1900409 := bstep (se 2 (by rfl) ⟨712653, by rfl⟩ : syracuseStep 1900409 = 1425307) B1425307
theorem B3047291 : Blo 1266451 3047291 := bstep (se 1 (by rfl) ⟨2285468, by rfl⟩ : syracuseStep 3047291 = 4570937) B4570937
theorem B2850731 : Blo 1266451 2850731 := bstep (se 1 (by rfl) ⟨2138048, by rfl⟩ : syracuseStep 2850731 = 4276097) B4276097
theorem B1900511 : Blo 1266451 1900511 := bstep (se 1 (by rfl) ⟨1425383, by rfl⟩ : syracuseStep 1900511 = 2850767) B2850767
theorem B20545595 : Blo 1266451 20545595 := bstep (se 1 (by rfl) ⟨15409196, by rfl⟩ : syracuseStep 20545595 = 30818393) B30818393
theorem B1900847 : Blo 1266451 1900847 := bstep (se 1 (by rfl) ⟨1425635, by rfl⟩ : syracuseStep 1900847 = 2851271) B2851271
theorem B2851199 : Blo 1266451 2851199 := bstep (se 1 (by rfl) ⟨2138399, by rfl⟩ : syracuseStep 2851199 = 4276799) B4276799
theorem B4276637 : Blo 1266451 4276637 := bstep (se 3 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 4276637 = 1603739) B1603739
theorem B6414875 : Blo 1266451 6414875 := bstep (se 1 (by rfl) ⟨4811156, by rfl⟩ : syracuseStep 6414875 = 9622313) B9622313
theorem B1901087 : Blo 1266451 1901087 := bstep (se 1 (by rfl) ⟨1425815, by rfl⟩ : syracuseStep 1901087 = 2851631) B2851631
theorem B2851433 : Blo 1266451 2851433 := bstep (se 2 (by rfl) ⟨1069287, by rfl⟩ : syracuseStep 2851433 = 2138575) B2138575
theorem B2138791 : Blo 1266451 2138791 := bstep (se 1 (by rfl) ⟨1604093, by rfl⟩ : syracuseStep 2138791 = 3208187) B3208187
theorem B13714109 : Blo 1266451 13714109 := bstep (se 3 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 13714109 = 5142791) B5142791
theorem B1426207 : Blo 1266451 1426207 := bstep (se 1 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 1426207 = 2139311) B2139311
theorem B12174209 : Blo 1266451 12174209 := bstep (se 2 (by rfl) ⟨4565328, by rfl⟩ : syracuseStep 12174209 = 9130657) B9130657
theorem B12174245 : Blo 1266451 12174245 := bstep (se 4 (by rfl) ⟨1141335, by rfl⟩ : syracuseStep 12174245 = 2282671) B2282671
theorem B2139115 : Blo 1266451 2139115 := bstep (se 1 (by rfl) ⟨1604336, by rfl⟩ : syracuseStep 2139115 = 3208673) B3208673
theorem B10822643 : Blo 1266451 10822643 := bstep (se 1 (by rfl) ⟨8116982, by rfl⟩ : syracuseStep 10822643 = 16233965) B16233965
theorem B2139257 : Blo 1266451 2139257 := bstep (se 2 (by rfl) ⟨802221, by rfl⟩ : syracuseStep 2139257 = 1604443) B1604443
theorem B30844081 : Blo 1266451 30844081 := bstep (se 2 (by rfl) ⟨11566530, by rfl⟩ : syracuseStep 30844081 = 23133061) B23133061
theorem B46269629 : Blo 1266451 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B1901759 : Blo 1266451 1901759 := bstep (se 1 (by rfl) ⟨1426319, by rfl⟩ : syracuseStep 1901759 = 2852639) B2852639
theorem B2852063 : Blo 1266451 2852063 := bstep (se 1 (by rfl) ⟨2139047, by rfl⟩ : syracuseStep 2852063 = 4278095) B4278095
theorem B1901903 : Blo 1266451 1901903 := bstep (se 1 (by rfl) ⟨1426427, by rfl⟩ : syracuseStep 1901903 = 2852855) B2852855
theorem B1901993 : Blo 1266451 1901993 := bstep (se 2 (by rfl) ⟨713247, by rfl⟩ : syracuseStep 1901993 = 1426495) B1426495
theorem B2852279 : Blo 1266451 2852279 := bstep (se 1 (by rfl) ⟨2139209, by rfl⟩ : syracuseStep 2852279 = 4278419) B4278419
theorem B2704927 : Blo 1266451 2704927 := bstep (se 1 (by rfl) ⟨2028695, by rfl⟩ : syracuseStep 2704927 = 4057391) B4057391
theorem B1902143 : Blo 1266451 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B1902185 : Blo 1266451 1902185 := bstep (se 2 (by rfl) ⟨713319, by rfl⟩ : syracuseStep 1902185 = 1426639) B1426639
theorem B2852459 : Blo 1266451 2852459 := bstep (se 1 (by rfl) ⟨2139344, by rfl⟩ : syracuseStep 2852459 = 4278689) B4278689
theorem B2852729 : Blo 1266451 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B16467877 : Blo 1266451 16467877 := bstep (se 4 (by rfl) ⟨1543863, by rfl⟩ : syracuseStep 16467877 = 3087727) B3087727
theorem B1902623 : Blo 1266451 1902623 := bstep (se 1 (by rfl) ⟨1426967, by rfl⟩ : syracuseStep 1902623 = 2853935) B2853935
theorem B87836723 : Blo 1266451 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B3254393 : Blo 1266451 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B2853161 : Blo 1266451 2853161 := bstep (se 2 (by rfl) ⟨1069935, by rfl⟩ : syracuseStep 2853161 = 2139871) B2139871
theorem B4278635 : Blo 1266451 4278635 := bstep (se 1 (by rfl) ⟨3208976, by rfl⟩ : syracuseStep 4278635 = 6417953) B6417953
theorem B5859809 : Blo 1266451 5859809 := bstep (se 2 (by rfl) ⟨2197428, by rfl⟩ : syracuseStep 5859809 = 4394857) B4394857
theorem B4278905 : Blo 1266451 4278905 := bstep (se 2 (by rfl) ⟨1604589, by rfl⟩ : syracuseStep 4278905 = 3209179) B3209179
theorem B1805095 : Blo 1266451 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B2853737 : Blo 1266451 2853737 := bstep (se 2 (by rfl) ⟨1070151, by rfl⟩ : syracuseStep 2853737 = 2140303) B2140303
theorem B2853791 : Blo 1266451 2853791 := bstep (se 1 (by rfl) ⟨2140343, by rfl⟩ : syracuseStep 2853791 = 4280687) B4280687
theorem B5213123 : Blo 1266451 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B3427337 : Blo 1266451 3427337 := bstep (se 2 (by rfl) ⟨1285251, by rfl⟩ : syracuseStep 3427337 = 2570503) B2570503
theorem B11725897 : Blo 1266451 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B65825963 : Blo 1266451 65825963 := bstep (se 1 (by rfl) ⟨49369472, by rfl⟩ : syracuseStep 65825963 = 98738945) B98738945
theorem B78048461 : Blo 1266451 78048461 := bstep (se 3 (by rfl) ⟨14634086, by rfl⟩ : syracuseStep 78048461 = 29268173) B29268173
theorem B55602409 : Blo 1266451 55602409 := bstep (se 2 (by rfl) ⟨20850903, by rfl⟩ : syracuseStep 55602409 = 41701807) B41701807
theorem B5410091 : Blo 1266451 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B10276145 : Blo 1266451 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B2567479 : Blo 1266451 2567479 := bstep (se 1 (by rfl) ⟨1925609, by rfl⟩ : syracuseStep 2567479 = 3851219) B3851219
theorem B3206567 : Blo 1266451 3206567 := bstep (se 1 (by rfl) ⟨2404925, by rfl⟩ : syracuseStep 3206567 = 4809851) B4809851
theorem B41087033 : Blo 1266451 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B1372223 : Blo 1266451 1372223 := bstep (se 1 (by rfl) ⟨1029167, by rfl⟩ : syracuseStep 1372223 = 2058335) B2058335
theorem B4059209 : Blo 1266451 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B2314415 : Blo 1266451 2314415 := bstep (se 1 (by rfl) ⟨1735811, by rfl⟩ : syracuseStep 2314415 = 3471623) B3471623
theorem B12177935 : Blo 1266451 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B3609143 : Blo 1266451 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B4395575 : Blo 1266451 4395575 := bstep (se 1 (by rfl) ⟨3296681, by rfl⟩ : syracuseStep 4395575 = 6593363) B6593363
theorem B1266495 : Blo 1266451 1266495 := bstep (se 1 (by rfl) ⟨949871, by rfl⟩ : syracuseStep 1266495 = 1899743) B1899743
theorem B1266523 : Blo 1266451 1266523 := bstep (se 1 (by rfl) ⟨949892, by rfl⟩ : syracuseStep 1266523 = 1899785) B1899785
theorem B1266591 : Blo 1266451 1266591 := bstep (se 1 (by rfl) ⟨949943, by rfl⟩ : syracuseStep 1266591 = 1899887) B1899887
theorem B1266671 : Blo 1266451 1266671 := bstep (se 1 (by rfl) ⟨950003, by rfl⟩ : syracuseStep 1266671 = 1900007) B1900007
theorem B1266759 : Blo 1266451 1266759 := bstep (se 1 (by rfl) ⟨950069, by rfl⟩ : syracuseStep 1266759 = 1900139) B1900139
theorem B1266843 : Blo 1266451 1266843 := bstep (se 1 (by rfl) ⟨950132, by rfl⟩ : syracuseStep 1266843 = 1900265) B1900265
theorem B1266939 : Blo 1266451 1266939 := bstep (se 1 (by rfl) ⟨950204, by rfl⟩ : syracuseStep 1266939 = 1900409) B1900409
theorem B2405639 : Blo 1266451 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B1267007 : Blo 1266451 1267007 := bstep (se 1 (by rfl) ⟨950255, by rfl⟩ : syracuseStep 1267007 = 1900511) B1900511
theorem B3208511 : Blo 1266451 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B1267175 : Blo 1266451 1267175 := bstep (se 1 (by rfl) ⟨950381, by rfl⟩ : syracuseStep 1267175 = 1900763) B1900763
theorem B1267183 : Blo 1266451 1267183 := bstep (se 1 (by rfl) ⟨950387, by rfl⟩ : syracuseStep 1267183 = 1900775) B1900775
theorem B1267291 : Blo 1266451 1267291 := bstep (se 1 (by rfl) ⟨950468, by rfl⟩ : syracuseStep 1267291 = 1900937) B1900937
theorem B6420059 : Blo 1266451 6420059 := bstep (se 1 (by rfl) ⟨4815044, by rfl⟩ : syracuseStep 6420059 = 9630089) B9630089
theorem B5142107 : Blo 1266451 5142107 := bstep (se 1 (by rfl) ⟨3856580, by rfl⟩ : syracuseStep 5142107 = 7713161) B7713161
theorem B1267355 : Blo 1266451 1267355 := bstep (se 1 (by rfl) ⟨950516, by rfl⟩ : syracuseStep 1267355 = 1901033) B1901033
theorem B1267439 : Blo 1266451 1267439 := bstep (se 1 (by rfl) ⟨950579, by rfl⟩ : syracuseStep 1267439 = 1901159) B1901159
theorem B1267527 : Blo 1266451 1267527 := bstep (se 1 (by rfl) ⟨950645, by rfl⟩ : syracuseStep 1267527 = 1901291) B1901291
theorem B1267547 : Blo 1266451 1267547 := bstep (se 1 (by rfl) ⟨950660, by rfl⟩ : syracuseStep 1267547 = 1901321) B1901321
theorem B1267615 : Blo 1266451 1267615 := bstep (se 1 (by rfl) ⟨950711, by rfl⟩ : syracuseStep 1267615 = 1901423) B1901423
theorem B3209159 : Blo 1266451 3209159 := bstep (se 1 (by rfl) ⟨2406869, by rfl⟩ : syracuseStep 3209159 = 4813739) B4813739
theorem B1267783 : Blo 1266451 1267783 := bstep (se 1 (by rfl) ⟨950837, by rfl⟩ : syracuseStep 1267783 = 1901675) B1901675
theorem B4274315 : Blo 1266451 4274315 := bstep (se 1 (by rfl) ⟨3205736, by rfl⟩ : syracuseStep 4274315 = 6411473) B6411473
theorem B9623771 : Blo 1266451 9623771 := bstep (se 1 (by rfl) ⟨7217828, by rfl⟩ : syracuseStep 9623771 = 14435657) B14435657
theorem B1267943 : Blo 1266451 1267943 := bstep (se 1 (by rfl) ⟨950957, by rfl⟩ : syracuseStep 1267943 = 1901915) B1901915
theorem B6093103 : Blo 1266451 6093103 := bstep (se 1 (by rfl) ⟨4569827, by rfl⟩ : syracuseStep 6093103 = 9139655) B9139655
theorem B10819979 : Blo 1266451 10819979 := bstep (se 1 (by rfl) ⟨8114984, by rfl⟩ : syracuseStep 10819979 = 16229969) B16229969
theorem B1268127 : Blo 1266451 1268127 := bstep (se 1 (by rfl) ⟨951095, by rfl⟩ : syracuseStep 1268127 = 1902191) B1902191
theorem B1268175 : Blo 1266451 1268175 := bstep (se 1 (by rfl) ⟨951131, by rfl⟩ : syracuseStep 1268175 = 1902263) B1902263
theorem B1268199 : Blo 1266451 1268199 := bstep (se 1 (by rfl) ⟨951149, by rfl⟩ : syracuseStep 1268199 = 1902299) B1902299
theorem B2603561 : Blo 1266451 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B1268315 : Blo 1266451 1268315 := bstep (se 1 (by rfl) ⟨951236, by rfl⟩ : syracuseStep 1268315 = 1902473) B1902473
theorem B10279547 : Blo 1266451 10279547 := bstep (se 1 (by rfl) ⟨7709660, by rfl⟩ : syracuseStep 10279547 = 15419321) B15419321
theorem B1268383 : Blo 1266451 1268383 := bstep (se 1 (by rfl) ⟨951287, by rfl⟩ : syracuseStep 1268383 = 1902575) B1902575
theorem B16472915 : Blo 1266451 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B8788931 : Blo 1266451 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B4275233 : Blo 1266451 4275233 := bstep (se 2 (by rfl) ⟨1603212, by rfl⟩ : syracuseStep 4275233 = 3206425) B3206425
theorem B10820729 : Blo 1266451 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B8125697 : Blo 1266451 8125697 := bstep (se 2 (by rfl) ⟨3047136, by rfl⟩ : syracuseStep 8125697 = 6094273) B6094273
theorem B1899983 : Blo 1266451 1899983 := bstep (se 1 (by rfl) ⟨1424987, by rfl⟩ : syracuseStep 1899983 = 2849975) B2849975
theorem B2850299 : Blo 1266451 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B2850479 : Blo 1266451 2850479 := bstep (se 1 (by rfl) ⟨2137859, by rfl⟩ : syracuseStep 2850479 = 4275719) B4275719
theorem B2137819 : Blo 1266451 2137819 := bstep (se 1 (by rfl) ⟨1603364, by rfl⟩ : syracuseStep 2137819 = 3206729) B3206729
theorem B4275935 : Blo 1266451 4275935 := bstep (se 1 (by rfl) ⟨3206951, by rfl⟩ : syracuseStep 4275935 = 6413903) B6413903
theorem B1425127 : Blo 1266451 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B2850569 : Blo 1266451 2850569 := bstep (se 2 (by rfl) ⟨1068963, by rfl⟩ : syracuseStep 2850569 = 2137927) B2137927
theorem B6176567 : Blo 1266451 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B1900367 : Blo 1266451 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B2031527 : Blo 1266451 2031527 := bstep (se 1 (by rfl) ⟨1523645, by rfl⟩ : syracuseStep 2031527 = 3047291) B3047291
theorem B1900487 : Blo 1266451 1900487 := bstep (se 1 (by rfl) ⟨1425365, by rfl⟩ : syracuseStep 1900487 = 2850731) B2850731
theorem B2138089 : Blo 1266451 2138089 := bstep (se 2 (by rfl) ⟨801783, by rfl⟩ : syracuseStep 2138089 = 1603567) B1603567
theorem B15417325 : Blo 1266451 15417325 := bstep (se 3 (by rfl) ⟨2890748, by rfl⟩ : syracuseStep 15417325 = 5781497) B5781497
theorem B13697063 : Blo 1266451 13697063 := bstep (se 1 (by rfl) ⟨10272797, by rfl⟩ : syracuseStep 13697063 = 20545595) B20545595
theorem B1900799 : Blo 1266451 1900799 := bstep (se 1 (by rfl) ⟨1425599, by rfl⟩ : syracuseStep 1900799 = 2851199) B2851199
theorem B2851091 : Blo 1266451 2851091 := bstep (se 1 (by rfl) ⟨2138318, by rfl⟩ : syracuseStep 2851091 = 4276637) B4276637
theorem B8118623 : Blo 1266451 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B4276583 : Blo 1266451 4276583 := bstep (se 1 (by rfl) ⟨3207437, by rfl⟩ : syracuseStep 4276583 = 6414875) B6414875
theorem B1900955 : Blo 1266451 1900955 := bstep (se 1 (by rfl) ⟨1425716, by rfl⟩ : syracuseStep 1900955 = 2851433) B2851433
theorem B9142739 : Blo 1266451 9142739 := bstep (se 1 (by rfl) ⟨6857054, by rfl⟩ : syracuseStep 9142739 = 13714109) B13714109
theorem B6415037 : Blo 1266451 6415037 := bstep (se 3 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 6415037 = 2405639) B2405639
theorem B1426171 : Blo 1266451 1426171 := bstep (se 1 (by rfl) ⟨1069628, by rfl⟩ : syracuseStep 1426171 = 2139257) B2139257
theorem B14426909 : Blo 1266451 14426909 := bstep (se 3 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 14426909 = 5410091) B5410091
theorem B1901375 : Blo 1266451 1901375 := bstep (se 1 (by rfl) ⟨1426031, by rfl⟩ : syracuseStep 1901375 = 2852063) B2852063
theorem B2139007 : Blo 1266451 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B2851721 : Blo 1266451 2851721 := bstep (se 2 (by rfl) ⟨1069395, by rfl⟩ : syracuseStep 2851721 = 2138791) B2138791
theorem B1901519 : Blo 1266451 1901519 := bstep (se 1 (by rfl) ⟨1426139, by rfl⟩ : syracuseStep 1901519 = 2852279) B2852279
theorem B1901609 : Blo 1266451 1901609 := bstep (se 2 (by rfl) ⟨713103, by rfl⟩ : syracuseStep 1901609 = 1426207) B1426207
theorem B1901639 : Blo 1266451 1901639 := bstep (se 1 (by rfl) ⟨1426229, by rfl⟩ : syracuseStep 1901639 = 2852459) B2852459
theorem B1901819 : Blo 1266451 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B2139439 : Blo 1266451 2139439 := bstep (se 1 (by rfl) ⟨1604579, by rfl⟩ : syracuseStep 2139439 = 3209159) B3209159
theorem B2852153 : Blo 1266451 2852153 := bstep (se 2 (by rfl) ⟨1069557, by rfl⟩ : syracuseStep 2852153 = 2139115) B2139115
theorem B58557815 : Blo 1266451 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B6415847 : Blo 1266451 6415847 := bstep (se 1 (by rfl) ⟨4811885, by rfl⟩ : syracuseStep 6415847 = 9623771) B9623771
theorem B1902107 : Blo 1266451 1902107 := bstep (se 1 (by rfl) ⟨1426580, by rfl⟩ : syracuseStep 1902107 = 2853161) B2853161
theorem B9627173 : Blo 1266451 9627173 := bstep (se 4 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 9627173 = 1805095) B1805095
theorem B41125441 : Blo 1266451 41125441 := bstep (se 2 (by rfl) ⟨15422040, by rfl⟩ : syracuseStep 41125441 = 30844081) B30844081
theorem B2852423 : Blo 1266451 2852423 := bstep (se 1 (by rfl) ⟨2139317, by rfl⟩ : syracuseStep 2852423 = 4278635) B4278635
theorem B2852603 : Blo 1266451 2852603 := bstep (se 1 (by rfl) ⟨2139452, by rfl⟩ : syracuseStep 2852603 = 4278905) B4278905
theorem B1902491 : Blo 1266451 1902491 := bstep (se 1 (by rfl) ⟨1426868, by rfl⟩ : syracuseStep 1902491 = 2853737) B2853737
theorem B1902527 : Blo 1266451 1902527 := bstep (se 1 (by rfl) ⟨1426895, by rfl⟩ : syracuseStep 1902527 = 2853791) B2853791
theorem B5859287 : Blo 1266451 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B3475415 : Blo 1266451 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B3606569 : Blo 1266451 3606569 := bstep (se 2 (by rfl) ⟨1352463, by rfl⟩ : syracuseStep 3606569 = 2704927) B2704927
theorem B5417131 : Blo 1266451 5417131 := bstep (se 1 (by rfl) ⟨4062848, by rfl⟩ : syracuseStep 5417131 = 8125697) B8125697
theorem B6850763 : Blo 1266451 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B5417405 : Blo 1266451 5417405 := bstep (se 3 (by rfl) ⟨1015763, by rfl⟩ : syracuseStep 5417405 = 2031527) B2031527
theorem B21957169 : Blo 1266451 21957169 := bstep (se 2 (by rfl) ⟨8233938, by rfl⟩ : syracuseStep 21957169 = 16467877) B16467877
theorem B20556433 : Blo 1266451 20556433 := bstep (se 2 (by rfl) ⟨7708662, by rfl⟩ : syracuseStep 20556433 = 15417325) B15417325
theorem B2706139 : Blo 1266451 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B1542943 : Blo 1266451 1542943 := bstep (se 1 (by rfl) ⟨1157207, by rfl⟩ : syracuseStep 1542943 = 2314415) B2314415
theorem B30846419 : Blo 1266451 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B4280039 : Blo 1266451 4280039 := bstep (se 1 (by rfl) ⟨3210029, by rfl⟩ : syracuseStep 4280039 = 6420059) B6420059
theorem B15634529 : Blo 1266451 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B6942829 : Blo 1266451 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B7213319 : Blo 1266451 7213319 := bstep (se 1 (by rfl) ⟨5409989, by rfl⟩ : syracuseStep 7213319 = 10819979) B10819979
theorem B6853031 : Blo 1266451 6853031 := bstep (se 1 (by rfl) ⟨5139773, by rfl⟩ : syracuseStep 6853031 = 10279547) B10279547
theorem B10981943 : Blo 1266451 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B7213819 : Blo 1266451 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B52032307 : Blo 1266451 52032307 := bstep (se 1 (by rfl) ⟨39024230, by rfl⟩ : syracuseStep 52032307 = 78048461) B78048461
theorem B1266655 : Blo 1266451 1266655 := bstep (se 1 (by rfl) ⟨949991, by rfl⟩ : syracuseStep 1266655 = 1899983) B1899983
theorem B4117711 : Blo 1266451 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B1266911 : Blo 1266451 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B1266991 : Blo 1266451 1266991 := bstep (se 1 (by rfl) ⟨950243, by rfl⟩ : syracuseStep 1266991 = 1900487) B1900487
theorem B27391355 : Blo 1266451 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B3659261 : Blo 1266451 3659261 := bstep (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) B1372223
theorem B1267231 : Blo 1266451 1267231 := bstep (se 1 (by rfl) ⟨950423, by rfl⟩ : syracuseStep 1267231 = 1900847) B1900847
theorem B1267391 : Blo 1266451 1267391 := bstep (se 1 (by rfl) ⟨950543, by rfl⟩ : syracuseStep 1267391 = 1901087) B1901087
theorem B2406095 : Blo 1266451 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B2930383 : Blo 1266451 2930383 := bstep (se 1 (by rfl) ⟨2197787, by rfl⟩ : syracuseStep 2930383 = 4395575) B4395575
theorem B8124137 : Blo 1266451 8124137 := bstep (se 2 (by rfl) ⟨3046551, by rfl⟩ : syracuseStep 8124137 = 6093103) B6093103
theorem B8116139 : Blo 1266451 8116139 := bstep (se 1 (by rfl) ⟨6087104, by rfl⟩ : syracuseStep 8116139 = 12174209) B12174209
theorem B8116163 : Blo 1266451 8116163 := bstep (se 1 (by rfl) ⟨6087122, by rfl⟩ : syracuseStep 8116163 = 12174245) B12174245
theorem B7215095 : Blo 1266451 7215095 := bstep (se 1 (by rfl) ⟨5411321, by rfl⟩ : syracuseStep 7215095 = 10822643) B10822643
theorem B1267839 : Blo 1266451 1267839 := bstep (se 1 (by rfl) ⟨950879, by rfl⟩ : syracuseStep 1267839 = 1901759) B1901759
theorem B1267935 : Blo 1266451 1267935 := bstep (se 1 (by rfl) ⟨950951, by rfl⟩ : syracuseStep 1267935 = 1901903) B1901903
theorem B1267995 : Blo 1266451 1267995 := bstep (se 1 (by rfl) ⟨950996, by rfl⟩ : syracuseStep 1267995 = 1901993) B1901993
theorem B1268095 : Blo 1266451 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B1268123 : Blo 1266451 1268123 := bstep (se 1 (by rfl) ⟨951092, by rfl⟩ : syracuseStep 1268123 = 1902185) B1902185
theorem B1268415 : Blo 1266451 1268415 := bstep (se 1 (by rfl) ⟨951311, by rfl⟩ : syracuseStep 1268415 = 1902623) B1902623
theorem B2169595 : Blo 1266451 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B2849543 : Blo 1266451 2849543 := bstep (se 1 (by rfl) ⟨2137157, by rfl⟩ : syracuseStep 2849543 = 4274315) B4274315
theorem B13712285 : Blo 1266451 13712285 := bstep (se 3 (by rfl) ⟨2571053, by rfl⟩ : syracuseStep 13712285 = 5142107) B5142107
theorem B74136545 : Blo 1266451 74136545 := bstep (se 2 (by rfl) ⟨27801204, by rfl⟩ : syracuseStep 74136545 = 55602409) B55602409
theorem B3906539 : Blo 1266451 3906539 := bstep (se 1 (by rfl) ⟨2929904, by rfl⟩ : syracuseStep 3906539 = 5859809) B5859809
theorem B3423305 : Blo 1266451 3423305 := bstep (se 2 (by rfl) ⟨1283739, by rfl⟩ : syracuseStep 3423305 = 2567479) B2567479
theorem B2284891 : Blo 1266451 2284891 := bstep (se 1 (by rfl) ⟨1713668, by rfl⟩ : syracuseStep 2284891 = 3427337) B3427337
theorem B2850155 : Blo 1266451 2850155 := bstep (se 1 (by rfl) ⟨2137616, by rfl⟩ : syracuseStep 2850155 = 4275233) B4275233
theorem B43883975 : Blo 1266451 43883975 := bstep (se 1 (by rfl) ⟨32912981, by rfl⟩ : syracuseStep 43883975 = 65825963) B65825963
theorem B2137711 : Blo 1266451 2137711 := bstep (se 1 (by rfl) ⟨1603283, by rfl⟩ : syracuseStep 2137711 = 3206567) B3206567
theorem B2850425 : Blo 1266451 2850425 := bstep (se 2 (by rfl) ⟨1068909, by rfl⟩ : syracuseStep 2850425 = 2137819) B2137819
theorem B1900169 : Blo 1266451 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B1900199 : Blo 1266451 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B1900319 : Blo 1266451 1900319 := bstep (se 1 (by rfl) ⟨1425239, by rfl⟩ : syracuseStep 1900319 = 2850479) B2850479
theorem B2850623 : Blo 1266451 2850623 := bstep (se 1 (by rfl) ⟨2137967, by rfl⟩ : syracuseStep 2850623 = 4275935) B4275935
theorem B1900379 : Blo 1266451 1900379 := bstep (se 1 (by rfl) ⟨1425284, by rfl⟩ : syracuseStep 1900379 = 2850569) B2850569
theorem B2850785 : Blo 1266451 2850785 := bstep (se 2 (by rfl) ⟨1069044, by rfl⟩ : syracuseStep 2850785 = 2138089) B2138089
theorem B9257105 : Blo 1266451 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B4808879 : Blo 1266451 4808879 := bstep (se 1 (by rfl) ⟨3606659, by rfl⟩ : syracuseStep 4808879 = 7213319) B7213319
theorem B1900727 : Blo 1266451 1900727 := bstep (se 1 (by rfl) ⟨1425545, by rfl⟩ : syracuseStep 1900727 = 2851091) B2851091
theorem B2851055 : Blo 1266451 2851055 := bstep (se 1 (by rfl) ⟨2138291, by rfl⟩ : syracuseStep 2851055 = 4276583) B4276583
theorem B6095159 : Blo 1266451 6095159 := bstep (se 1 (by rfl) ⟨4571369, by rfl⟩ : syracuseStep 6095159 = 9142739) B9142739
theorem B4276691 : Blo 1266451 4276691 := bstep (se 1 (by rfl) ⟨3207518, by rfl⟩ : syracuseStep 4276691 = 6415037) B6415037
theorem B9617939 : Blo 1266451 9617939 := bstep (se 1 (by rfl) ⟨7213454, by rfl⟩ : syracuseStep 9617939 = 14426909) B14426909
theorem B1901147 : Blo 1266451 1901147 := bstep (se 1 (by rfl) ⟨1425860, by rfl⟩ : syracuseStep 1901147 = 2851721) B2851721
theorem B1901435 : Blo 1266451 1901435 := bstep (se 1 (by rfl) ⟨1426076, by rfl⟩ : syracuseStep 1901435 = 2852153) B2852153
theorem B18260903 : Blo 1266451 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B4277231 : Blo 1266451 4277231 := bstep (se 1 (by rfl) ⟨3207923, by rfl⟩ : syracuseStep 4277231 = 6415847) B6415847
theorem B9618425 : Blo 1266451 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B1901561 : Blo 1266451 1901561 := bstep (se 2 (by rfl) ⟨713085, by rfl⟩ : syracuseStep 1901561 = 1426171) B1426171
theorem B2057257 : Blo 1266451 2057257 := bstep (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) B1542943
theorem B1901615 : Blo 1266451 1901615 := bstep (se 1 (by rfl) ⟨1426211, by rfl⟩ : syracuseStep 1901615 = 2852423) B2852423
theorem B5416091 : Blo 1266451 5416091 := bstep (se 1 (by rfl) ⟨4062068, by rfl⟩ : syracuseStep 5416091 = 8124137) B8124137
theorem B1901735 : Blo 1266451 1901735 := bstep (se 1 (by rfl) ⟨1426301, by rfl⟩ : syracuseStep 1901735 = 2852603) B2852603
theorem B2852009 : Blo 1266451 2852009 := bstep (se 2 (by rfl) ⟨1069503, by rfl⟩ : syracuseStep 2852009 = 2139007) B2139007
theorem B117023933 : Blo 1266451 117023933 := bstep (se 3 (by rfl) ⟨21941987, by rfl⟩ : syracuseStep 117023933 = 43883975) B43883975
theorem B4810063 : Blo 1266451 4810063 := bstep (se 1 (by rfl) ⟨3607547, by rfl⟩ : syracuseStep 4810063 = 7215095) B7215095
theorem B5490281 : Blo 1266451 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B2852585 : Blo 1266451 2852585 := bstep (se 2 (by rfl) ⟨1069719, by rfl⟩ : syracuseStep 2852585 = 2139439) B2139439
theorem B49424363 : Blo 1266451 49424363 := bstep (se 1 (by rfl) ⟨37068272, by rfl⟩ : syracuseStep 49424363 = 74136545) B74136545
theorem B20564279 : Blo 1266451 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B2853359 : Blo 1266451 2853359 := bstep (se 1 (by rfl) ⟨2140019, by rfl⟩ : syracuseStep 2853359 = 4280039) B4280039
theorem B10423019 : Blo 1266451 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B39038543 : Blo 1266451 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B6418115 : Blo 1266451 6418115 := bstep (se 1 (by rfl) ⟨4813586, by rfl⟩ : syracuseStep 6418115 = 9627173) B9627173
theorem B5410759 : Blo 1266451 5410759 := bstep (se 1 (by rfl) ⟨4058069, by rfl⟩ : syracuseStep 5410759 = 8116139) B8116139
theorem B5410775 : Blo 1266451 5410775 := bstep (se 1 (by rfl) ⟨4058081, by rfl⟩ : syracuseStep 5410775 = 8116163) B8116163
theorem B11571173 : Blo 1266451 11571173 := bstep (se 4 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 11571173 = 2169595) B2169595
theorem B2404379 : Blo 1266451 2404379 := bstep (se 1 (by rfl) ⟨1803284, by rfl⟩ : syracuseStep 2404379 = 3606569) B3606569
theorem B4567175 : Blo 1266451 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B12186085 : Blo 1266451 12186085 := bstep (se 4 (by rfl) ⟨1142445, by rfl⟩ : syracuseStep 12186085 = 2284891) B2284891
theorem B2282203 : Blo 1266451 2282203 := bstep (se 1 (by rfl) ⟨1711652, by rfl⟩ : syracuseStep 2282203 = 3423305) B3423305
theorem B54833921 : Blo 1266451 54833921 := bstep (se 2 (by rfl) ⟨20562720, by rfl⟩ : syracuseStep 54833921 = 41125441) B41125441
theorem B36566093 : Blo 1266451 36566093 := bstep (se 3 (by rfl) ⟨6856142, by rfl⟩ : syracuseStep 36566093 = 13712285) B13712285
theorem B1266779 : Blo 1266451 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B1266799 : Blo 1266451 1266799 := bstep (se 1 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 1266799 = 1900199) B1900199
theorem B1266879 : Blo 1266451 1266879 := bstep (se 1 (by rfl) ⟨950159, by rfl⟩ : syracuseStep 1266879 = 1900319) B1900319
theorem B1266919 : Blo 1266451 1266919 := bstep (se 1 (by rfl) ⟨950189, by rfl⟩ : syracuseStep 1266919 = 1900379) B1900379
theorem B39032117 : Blo 1266451 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B9131375 : Blo 1266451 9131375 := bstep (se 1 (by rfl) ⟨6848531, by rfl⟩ : syracuseStep 9131375 = 13697063) B13697063
theorem B1267199 : Blo 1266451 1267199 := bstep (se 1 (by rfl) ⟨950399, by rfl⟩ : syracuseStep 1267199 = 1900799) B1900799
theorem B7222841 : Blo 1266451 7222841 := bstep (se 2 (by rfl) ⟨2708565, by rfl⟩ : syracuseStep 7222841 = 5417131) B5417131
theorem B5412415 : Blo 1266451 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B1267303 : Blo 1266451 1267303 := bstep (se 1 (by rfl) ⟨950477, by rfl⟩ : syracuseStep 1267303 = 1900955) B1900955
theorem B4568687 : Blo 1266451 4568687 := bstep (se 1 (by rfl) ⟨3426515, by rfl⟩ : syracuseStep 4568687 = 6853031) B6853031
theorem B7321295 : Blo 1266451 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B1267583 : Blo 1266451 1267583 := bstep (se 1 (by rfl) ⟨950687, by rfl⟩ : syracuseStep 1267583 = 1901375) B1901375
theorem B1267679 : Blo 1266451 1267679 := bstep (se 1 (by rfl) ⟨950759, by rfl⟩ : syracuseStep 1267679 = 1901519) B1901519
theorem B1267739 : Blo 1266451 1267739 := bstep (se 1 (by rfl) ⟨950804, by rfl⟩ : syracuseStep 1267739 = 1901609) B1901609
theorem B1267759 : Blo 1266451 1267759 := bstep (se 1 (by rfl) ⟨950819, by rfl⟩ : syracuseStep 1267759 = 1901639) B1901639
theorem B29276225 : Blo 1266451 29276225 := bstep (se 2 (by rfl) ⟨10978584, by rfl⟩ : syracuseStep 29276225 = 21957169) B21957169
theorem B1267879 : Blo 1266451 1267879 := bstep (se 1 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 1267879 = 1901819) B1901819
theorem B27408577 : Blo 1266451 27408577 := bstep (se 2 (by rfl) ⟨10278216, by rfl⟩ : syracuseStep 27408577 = 20556433) B20556433
theorem B1268071 : Blo 1266451 1268071 := bstep (se 1 (by rfl) ⟨951053, by rfl⟩ : syracuseStep 1268071 = 1902107) B1902107
theorem B69376409 : Blo 1266451 69376409 := bstep (se 2 (by rfl) ⟨26016153, by rfl⟩ : syracuseStep 69376409 = 52032307) B52032307
theorem B15628709 : Blo 1266451 15628709 := bstep (se 4 (by rfl) ⟨1465191, by rfl⟩ : syracuseStep 15628709 = 2930383) B2930383
theorem B1604063 : Blo 1266451 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B14432741 : Blo 1266451 14432741 := bstep (se 4 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 14432741 = 2706139) B2706139
theorem B1268327 : Blo 1266451 1268327 := bstep (se 1 (by rfl) ⟨951245, by rfl⟩ : syracuseStep 1268327 = 1902491) B1902491
theorem B1268351 : Blo 1266451 1268351 := bstep (se 1 (by rfl) ⟨951263, by rfl⟩ : syracuseStep 1268351 = 1902527) B1902527
theorem B3906191 : Blo 1266451 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B2316943 : Blo 1266451 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B3611603 : Blo 1266451 3611603 := bstep (se 1 (by rfl) ⟨2708702, by rfl⟩ : syracuseStep 3611603 = 5417405) B5417405
theorem B1899695 : Blo 1266451 1899695 := bstep (se 1 (by rfl) ⟨1424771, by rfl⟩ : syracuseStep 1899695 = 2849543) B2849543
theorem B2604359 : Blo 1266451 2604359 := bstep (se 1 (by rfl) ⟨1953269, by rfl⟩ : syracuseStep 2604359 = 3906539) B3906539
theorem B2850281 : Blo 1266451 2850281 := bstep (se 2 (by rfl) ⟨1068855, by rfl⟩ : syracuseStep 2850281 = 2137711) B2137711
theorem B1900103 : Blo 1266451 1900103 := bstep (se 1 (by rfl) ⟨1425077, by rfl⟩ : syracuseStep 1900103 = 2850155) B2850155
theorem B1900283 : Blo 1266451 1900283 := bstep (se 1 (by rfl) ⟨1425212, by rfl⟩ : syracuseStep 1900283 = 2850425) B2850425
theorem B1900415 : Blo 1266451 1900415 := bstep (se 1 (by rfl) ⟨1425311, by rfl⟩ : syracuseStep 1900415 = 2850623) B2850623
theorem B1900523 : Blo 1266451 1900523 := bstep (se 1 (by rfl) ⟨1425392, by rfl⟩ : syracuseStep 1900523 = 2850785) B2850785
theorem B1900703 : Blo 1266451 1900703 := bstep (se 1 (by rfl) ⟨1425527, by rfl⟩ : syracuseStep 1900703 = 2851055) B2851055
theorem B4063439 : Blo 1266451 4063439 := bstep (se 1 (by rfl) ⟨3047579, by rfl⟩ : syracuseStep 4063439 = 6095159) B6095159
theorem B36544769 : Blo 1266451 36544769 := bstep (se 2 (by rfl) ⟨13704288, by rfl⟩ : syracuseStep 36544769 = 27408577) B27408577
theorem B2851127 : Blo 1266451 2851127 := bstep (se 1 (by rfl) ⟨2138345, by rfl⟩ : syracuseStep 2851127 = 4276691) B4276691
theorem B2851487 : Blo 1266451 2851487 := bstep (se 1 (by rfl) ⟨2138615, by rfl⟩ : syracuseStep 2851487 = 4277231) B4277231
theorem B1901339 : Blo 1266451 1901339 := bstep (se 1 (by rfl) ⟨1426004, by rfl⟩ : syracuseStep 1901339 = 2852009) B2852009
theorem B6087583 : Blo 1266451 6087583 := bstep (se 1 (by rfl) ⟨4565687, by rfl⟩ : syracuseStep 6087583 = 9131375) B9131375
theorem B1901723 : Blo 1266451 1901723 := bstep (se 1 (by rfl) ⟨1426292, by rfl⟩ : syracuseStep 1901723 = 2852585) B2852585
theorem B4277501 : Blo 1266451 4277501 := bstep (se 3 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 4277501 = 1604063) B1604063
theorem B32949575 : Blo 1266451 32949575 := bstep (se 1 (by rfl) ⟨24712181, by rfl⟩ : syracuseStep 32949575 = 49424363) B49424363
theorem B14640749 : Blo 1266451 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B1902239 : Blo 1266451 1902239 := bstep (se 1 (by rfl) ⟨1426679, by rfl⟩ : syracuseStep 1902239 = 2853359) B2853359
theorem B48695741 : Blo 1266451 48695741 := bstep (se 3 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 48695741 = 18260903) B18260903
theorem B4278743 : Blo 1266451 4278743 := bstep (se 1 (by rfl) ⟨3209057, by rfl⟩ : syracuseStep 4278743 = 6418115) B6418115
theorem B3607183 : Blo 1266451 3607183 := bstep (se 1 (by rfl) ⟨2705387, by rfl⟩ : syracuseStep 3607183 = 5410775) B5410775
theorem B6171403 : Blo 1266451 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B3205919 : Blo 1266451 3205919 := bstep (se 1 (by rfl) ⟨2404439, by rfl⟩ : syracuseStep 3205919 = 4808879) B4808879
theorem B10972037 : Blo 1266451 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B36555947 : Blo 1266451 36555947 := bstep (se 1 (by rfl) ⟨27416960, by rfl⟩ : syracuseStep 36555947 = 54833921) B54833921
theorem B16248113 : Blo 1266451 16248113 := bstep (se 2 (by rfl) ⟨6093042, by rfl⟩ : syracuseStep 16248113 = 12186085) B12186085
theorem B12357029 : Blo 1266451 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B78015955 : Blo 1266451 78015955 := bstep (se 1 (by rfl) ⟨58511966, by rfl⟩ : syracuseStep 78015955 = 117023933) B117023933
theorem B26021411 : Blo 1266451 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B3042937 : Blo 1266451 3042937 := bstep (se 2 (by rfl) ⟨1141101, by rfl⟩ : syracuseStep 3042937 = 2282203) B2282203
theorem B19517483 : Blo 1266451 19517483 := bstep (se 1 (by rfl) ⟨14638112, by rfl⟩ : syracuseStep 19517483 = 29276225) B29276225
theorem B13709519 : Blo 1266451 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B9621827 : Blo 1266451 9621827 := bstep (se 1 (by rfl) ⟨7216370, by rfl⟩ : syracuseStep 9621827 = 14432741) B14432741
theorem B10416509 : Blo 1266451 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B1266463 : Blo 1266451 1266463 := bstep (se 1 (by rfl) ⟨949847, by rfl⟩ : syracuseStep 1266463 = 1899695) B1899695
theorem B1266735 : Blo 1266451 1266735 := bstep (se 1 (by rfl) ⟨950051, by rfl⟩ : syracuseStep 1266735 = 1900103) B1900103
theorem B1266855 : Blo 1266451 1266855 := bstep (se 1 (by rfl) ⟨950141, by rfl⟩ : syracuseStep 1266855 = 1900283) B1900283
theorem B1266943 : Blo 1266451 1266943 := bstep (se 1 (by rfl) ⟨950207, by rfl⟩ : syracuseStep 1266943 = 1900415) B1900415
theorem B7214345 : Blo 1266451 7214345 := bstep (se 2 (by rfl) ⟨2705379, by rfl⟩ : syracuseStep 7214345 = 5410759) B5410759
theorem B7714115 : Blo 1266451 7714115 := bstep (se 1 (by rfl) ⟨5785586, by rfl⟩ : syracuseStep 7714115 = 11571173) B11571173
theorem B1267015 : Blo 1266451 1267015 := bstep (se 1 (by rfl) ⟨950261, by rfl⟩ : syracuseStep 1267015 = 1900523) B1900523
theorem B1602919 : Blo 1266451 1602919 := bstep (se 1 (by rfl) ⟨1202189, by rfl⟩ : syracuseStep 1602919 = 2404379) B2404379
theorem B3044783 : Blo 1266451 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B1267151 : Blo 1266451 1267151 := bstep (se 1 (by rfl) ⟨950363, by rfl⟩ : syracuseStep 1267151 = 1900727) B1900727
theorem B6411959 : Blo 1266451 6411959 := bstep (se 1 (by rfl) ⟨4808969, by rfl⟩ : syracuseStep 6411959 = 9617939) B9617939
theorem B1267431 : Blo 1266451 1267431 := bstep (se 1 (by rfl) ⟨950573, by rfl⟩ : syracuseStep 1267431 = 1901147) B1901147
theorem B1267623 : Blo 1266451 1267623 := bstep (se 1 (by rfl) ⟨950717, by rfl⟩ : syracuseStep 1267623 = 1901435) B1901435
theorem B6412283 : Blo 1266451 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B1267707 : Blo 1266451 1267707 := bstep (se 1 (by rfl) ⟨950780, by rfl⟩ : syracuseStep 1267707 = 1901561) B1901561
theorem B1267743 : Blo 1266451 1267743 := bstep (se 1 (by rfl) ⟨950807, by rfl⟩ : syracuseStep 1267743 = 1901615) B1901615
theorem B24377395 : Blo 1266451 24377395 := bstep (se 1 (by rfl) ⟨18283046, by rfl⟩ : syracuseStep 24377395 = 36566093) B36566093
theorem B3610727 : Blo 1266451 3610727 := bstep (se 1 (by rfl) ⟨2708045, by rfl⟩ : syracuseStep 3610727 = 5416091) B5416091
theorem B1267823 : Blo 1266451 1267823 := bstep (se 1 (by rfl) ⟨950867, by rfl⟩ : syracuseStep 1267823 = 1901735) B1901735
theorem B4815227 : Blo 1266451 4815227 := bstep (se 1 (by rfl) ⟨3611420, by rfl⟩ : syracuseStep 4815227 = 7222841) B7222841
theorem B3045791 : Blo 1266451 3045791 := bstep (se 1 (by rfl) ⟨2284343, by rfl⟩ : syracuseStep 3045791 = 4568687) B4568687
theorem B4880863 : Blo 1266451 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B46250939 : Blo 1266451 46250939 := bstep (se 1 (by rfl) ⟨34688204, by rfl⟩ : syracuseStep 46250939 = 69376409) B69376409
theorem B10419139 : Blo 1266451 10419139 := bstep (se 1 (by rfl) ⟨7814354, by rfl⟩ : syracuseStep 10419139 = 15628709) B15628709
theorem B6413417 : Blo 1266451 6413417 := bstep (se 2 (by rfl) ⟨2405031, by rfl⟩ : syracuseStep 6413417 = 4810063) B4810063
theorem B27794717 : Blo 1266451 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B2407735 : Blo 1266451 2407735 := bstep (se 1 (by rfl) ⟨1805801, by rfl⟩ : syracuseStep 2407735 = 3611603) B3611603
theorem B7216553 : Blo 1266451 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B1736239 : Blo 1266451 1736239 := bstep (se 1 (by rfl) ⟨1302179, by rfl⟩ : syracuseStep 1736239 = 2604359) B2604359
theorem B1900187 : Blo 1266451 1900187 := bstep (se 1 (by rfl) ⟨1425140, by rfl⟩ : syracuseStep 1900187 = 2850281) B2850281
theorem B26025695 : Blo 1266451 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B24363179 : Blo 1266451 24363179 := bstep (se 1 (by rfl) ⟨18272384, by rfl⟩ : syracuseStep 24363179 = 36544769) B36544769
theorem B1900751 : Blo 1266451 1900751 := bstep (se 1 (by rfl) ⟨1425563, by rfl⟩ : syracuseStep 1900751 = 2851127) B2851127
theorem B6414551 : Blo 1266451 6414551 := bstep (se 1 (by rfl) ⟨4810913, by rfl⟩ : syracuseStep 6414551 = 9621827) B9621827
theorem B1900991 : Blo 1266451 1900991 := bstep (se 1 (by rfl) ⟨1425743, by rfl⟩ : syracuseStep 1900991 = 2851487) B2851487
theorem B16228997 : Blo 1266451 16228997 := bstep (se 4 (by rfl) ⟨1521468, by rfl⟩ : syracuseStep 16228997 = 3042937) B3042937
theorem B2851667 : Blo 1266451 2851667 := bstep (se 1 (by rfl) ⟨2138750, by rfl⟩ : syracuseStep 2851667 = 4277501) B4277501
theorem B4809563 : Blo 1266451 4809563 := bstep (se 1 (by rfl) ⟨3607172, by rfl⟩ : syracuseStep 4809563 = 7214345) B7214345
theorem B4809577 : Blo 1266451 4809577 := bstep (se 2 (by rfl) ⟨1803591, by rfl⟩ : syracuseStep 4809577 = 3607183) B3607183
theorem B2852495 : Blo 1266451 2852495 := bstep (se 1 (by rfl) ⟨2139371, by rfl⟩ : syracuseStep 2852495 = 4278743) B4278743
theorem B10832075 : Blo 1266451 10832075 := bstep (se 1 (by rfl) ⟨8124056, by rfl⟩ : syracuseStep 10832075 = 16248113) B16248113
theorem B4811035 : Blo 1266451 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B52046621 : Blo 1266451 52046621 := bstep (se 3 (by rfl) ⟨9758741, by rfl⟩ : syracuseStep 52046621 = 19517483) B19517483
theorem B21966383 : Blo 1266451 21966383 := bstep (se 1 (by rfl) ⟨16474787, by rfl⟩ : syracuseStep 21966383 = 32949575) B32949575
theorem B8228537 : Blo 1266451 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B9760499 : Blo 1266451 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B2314985 : Blo 1266451 2314985 := bstep (se 2 (by rfl) ⟨868119, by rfl⟩ : syracuseStep 2314985 = 1736239) B1736239
theorem B8238019 : Blo 1266451 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B29258765 : Blo 1266451 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B17347607 : Blo 1266451 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B1266791 : Blo 1266451 1266791 := bstep (se 1 (by rfl) ⟨950093, by rfl⟩ : syracuseStep 1266791 = 1900187) B1900187
theorem B26031269 : Blo 1266451 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B32503193 : Blo 1266451 32503193 := bstep (se 2 (by rfl) ⟨12188697, by rfl⟩ : syracuseStep 32503193 = 24377395) B24377395
theorem B1267135 : Blo 1266451 1267135 := bstep (se 1 (by rfl) ⟨950351, by rfl⟩ : syracuseStep 1267135 = 1900703) B1900703
theorem B9139679 : Blo 1266451 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B2708959 : Blo 1266451 2708959 := bstep (se 1 (by rfl) ⟨2031719, by rfl⟩ : syracuseStep 2708959 = 4063439) B4063439
theorem B6944339 : Blo 1266451 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B1267559 : Blo 1266451 1267559 := bstep (se 1 (by rfl) ⟨950669, by rfl⟩ : syracuseStep 1267559 = 1901339) B1901339
theorem B1267815 : Blo 1266451 1267815 := bstep (se 1 (by rfl) ⟨950861, by rfl⟩ : syracuseStep 1267815 = 1901723) B1901723
theorem B5142743 : Blo 1266451 5142743 := bstep (se 1 (by rfl) ⟨3857057, by rfl⟩ : syracuseStep 5142743 = 7714115) B7714115
theorem B2029855 : Blo 1266451 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B1268159 : Blo 1266451 1268159 := bstep (se 1 (by rfl) ⟨951119, by rfl⟩ : syracuseStep 1268159 = 1902239) B1902239
theorem B4274639 : Blo 1266451 4274639 := bstep (se 1 (by rfl) ⟨3205979, by rfl⟩ : syracuseStep 4274639 = 6411959) B6411959
theorem B8116777 : Blo 1266451 8116777 := bstep (se 2 (by rfl) ⟨3043791, by rfl⟩ : syracuseStep 8116777 = 6087583) B6087583
theorem B13892185 : Blo 1266451 13892185 := bstep (se 2 (by rfl) ⟨5209569, by rfl⟩ : syracuseStep 13892185 = 10419139) B10419139
theorem B4274855 : Blo 1266451 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B2407151 : Blo 1266451 2407151 := bstep (se 1 (by rfl) ⟨1805363, by rfl⟩ : syracuseStep 2407151 = 3610727) B3610727
theorem B3210151 : Blo 1266451 3210151 := bstep (se 1 (by rfl) ⟨2407613, by rfl⟩ : syracuseStep 3210151 = 4815227) B4815227
theorem B2030527 : Blo 1266451 2030527 := bstep (se 1 (by rfl) ⟨1522895, by rfl⟩ : syracuseStep 2030527 = 3045791) B3045791
theorem B32463827 : Blo 1266451 32463827 := bstep (se 1 (by rfl) ⟨24347870, by rfl⟩ : syracuseStep 32463827 = 48695741) B48695741
theorem B3210313 : Blo 1266451 3210313 := bstep (se 2 (by rfl) ⟨1203867, by rfl⟩ : syracuseStep 3210313 = 2407735) B2407735
theorem B2137225 : Blo 1266451 2137225 := bstep (se 2 (by rfl) ⟨801459, by rfl⟩ : syracuseStep 2137225 = 1602919) B1602919
theorem B2137279 : Blo 1266451 2137279 := bstep (se 1 (by rfl) ⟨1602959, by rfl⟩ : syracuseStep 2137279 = 3205919) B3205919
theorem B104021273 : Blo 1266451 104021273 := bstep (se 2 (by rfl) ⟨39007977, by rfl⟩ : syracuseStep 104021273 = 78015955) B78015955
theorem B30833959 : Blo 1266451 30833959 := bstep (se 1 (by rfl) ⟨23125469, by rfl⟩ : syracuseStep 30833959 = 46250939) B46250939
theorem B4275611 : Blo 1266451 4275611 := bstep (se 1 (by rfl) ⟨3206708, by rfl⟩ : syracuseStep 4275611 = 6413417) B6413417
theorem B24370631 : Blo 1266451 24370631 := bstep (se 1 (by rfl) ⟨18277973, by rfl⟩ : syracuseStep 24370631 = 36555947) B36555947
theorem B18529811 : Blo 1266451 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B17350463 : Blo 1266451 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B4276367 : Blo 1266451 4276367 := bstep (se 1 (by rfl) ⟨3207275, by rfl⟩ : syracuseStep 4276367 = 6414551) B6414551
theorem B6414713 : Blo 1266451 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B1901111 : Blo 1266451 1901111 := bstep (se 1 (by rfl) ⟨1425833, by rfl⟩ : syracuseStep 1901111 = 2851667) B2851667
theorem B19505843 : Blo 1266451 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B10822369 : Blo 1266451 10822369 := bstep (se 2 (by rfl) ⟨4058388, by rfl⟩ : syracuseStep 10822369 = 8116777) B8116777
theorem B18522913 : Blo 1266451 18522913 := bstep (se 2 (by rfl) ⟨6946092, by rfl⟩ : syracuseStep 18522913 = 13892185) B13892185
theorem B21668795 : Blo 1266451 21668795 := bstep (se 1 (by rfl) ⟨16251596, by rfl⟩ : syracuseStep 21668795 = 32503193) B32503193
theorem B4629559 : Blo 1266451 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B1901663 : Blo 1266451 1901663 := bstep (se 1 (by rfl) ⟨1426247, by rfl⟩ : syracuseStep 1901663 = 2852495) B2852495
theorem B69347515 : Blo 1266451 69347515 := bstep (se 1 (by rfl) ⟨52010636, by rfl⟩ : syracuseStep 69347515 = 104021273) B104021273
theorem B16247087 : Blo 1266451 16247087 := bstep (se 1 (by rfl) ⟨12185315, by rfl⟩ : syracuseStep 16247087 = 24370631) B24370631
theorem B6506999 : Blo 1266451 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B2706473 : Blo 1266451 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B3206375 : Blo 1266451 3206375 := bstep (se 1 (by rfl) ⟨2404781, by rfl⟩ : syracuseStep 3206375 = 4809563) B4809563
theorem B17354179 : Blo 1266451 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B4280201 : Blo 1266451 4280201 := bstep (se 2 (by rfl) ⟨1605075, by rfl⟩ : syracuseStep 4280201 = 3210151) B3210151
theorem B4280417 : Blo 1266451 4280417 := bstep (se 2 (by rfl) ⟨1605156, by rfl⟩ : syracuseStep 4280417 = 3210313) B3210313
theorem B7221383 : Blo 1266451 7221383 := bstep (se 1 (by rfl) ⟨5416037, by rfl⟩ : syracuseStep 7221383 = 10832075) B10832075
theorem B3428495 : Blo 1266451 3428495 := bstep (se 1 (by rfl) ⟨2571371, by rfl⟩ : syracuseStep 3428495 = 5142743) B5142743
theorem B41111945 : Blo 1266451 41111945 := bstep (se 2 (by rfl) ⟨15416979, by rfl⟩ : syracuseStep 41111945 = 30833959) B30833959
theorem B34697747 : Blo 1266451 34697747 := bstep (se 1 (by rfl) ⟨26023310, by rfl⟩ : syracuseStep 34697747 = 52046621) B52046621
theorem B6173293 : Blo 1266451 6173293 := bstep (se 3 (by rfl) ⟨1157492, by rfl⟩ : syracuseStep 6173293 = 2314985) B2314985
theorem B14644255 : Blo 1266451 14644255 := bstep (se 1 (by rfl) ⟨10983191, by rfl⟩ : syracuseStep 14644255 = 21966383) B21966383
theorem B5485691 : Blo 1266451 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B16242119 : Blo 1266451 16242119 := bstep (se 1 (by rfl) ⟨12181589, by rfl⟩ : syracuseStep 16242119 = 24363179) B24363179
theorem B1267167 : Blo 1266451 1267167 := bstep (se 1 (by rfl) ⟨950375, by rfl⟩ : syracuseStep 1267167 = 1900751) B1900751
theorem B1267327 : Blo 1266451 1267327 := bstep (se 1 (by rfl) ⟨950495, by rfl⟩ : syracuseStep 1267327 = 1900991) B1900991
theorem B10819331 : Blo 1266451 10819331 := bstep (se 1 (by rfl) ⟨8114498, by rfl⟩ : syracuseStep 10819331 = 16228997) B16228997
theorem B11565071 : Blo 1266451 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B6093119 : Blo 1266451 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B6412769 : Blo 1266451 6412769 := bstep (se 2 (by rfl) ⟨2404788, by rfl⟩ : syracuseStep 6412769 = 4809577) B4809577
theorem B10984025 : Blo 1266451 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B2849633 : Blo 1266451 2849633 := bstep (se 2 (by rfl) ⟨1068612, by rfl⟩ : syracuseStep 2849633 = 2137225) B2137225
theorem B2849705 : Blo 1266451 2849705 := bstep (se 2 (by rfl) ⟨1068639, by rfl⟩ : syracuseStep 2849705 = 2137279) B2137279
theorem B2849759 : Blo 1266451 2849759 := bstep (se 1 (by rfl) ⟨2137319, by rfl⟩ : syracuseStep 2849759 = 4274639) B4274639
theorem B2849903 : Blo 1266451 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B1604767 : Blo 1266451 1604767 := bstep (se 1 (by rfl) ⟨1203575, by rfl⟩ : syracuseStep 1604767 = 2407151) B2407151
theorem B3611945 : Blo 1266451 3611945 := bstep (se 2 (by rfl) ⟨1354479, by rfl⟩ : syracuseStep 3611945 = 2708959) B2708959
theorem B21642551 : Blo 1266451 21642551 := bstep (se 1 (by rfl) ⟨16231913, by rfl⟩ : syracuseStep 21642551 = 32463827) B32463827
theorem B2850407 : Blo 1266451 2850407 := bstep (se 1 (by rfl) ⟨2137805, by rfl⟩ : syracuseStep 2850407 = 4275611) B4275611
theorem B10829477 : Blo 1266451 10829477 := bstep (se 4 (by rfl) ⟨1015263, by rfl⟩ : syracuseStep 10829477 = 2030527) B2030527
theorem B12353207 : Blo 1266451 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B11566975 : Blo 1266451 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B2850911 : Blo 1266451 2850911 := bstep (se 1 (by rfl) ⟨2138183, by rfl⟩ : syracuseStep 2850911 = 4276367) B4276367
theorem B2285663 : Blo 1266451 2285663 := bstep (se 1 (by rfl) ⟨1714247, by rfl⟩ : syracuseStep 2285663 = 3428495) B3428495
theorem B7217261 : Blo 1266451 7217261 := bstep (se 3 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 7217261 = 2706473) B2706473
theorem B92463353 : Blo 1266451 92463353 := bstep (se 2 (by rfl) ⟨34673757, by rfl⟩ : syracuseStep 92463353 = 69347515) B69347515
theorem B4276475 : Blo 1266451 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B7710047 : Blo 1266451 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B10831391 : Blo 1266451 10831391 := bstep (se 1 (by rfl) ⟨8123543, by rfl⟩ : syracuseStep 10831391 = 16247087) B16247087
theorem B2139689 : Blo 1266451 2139689 := bstep (se 2 (by rfl) ⟨802383, by rfl⟩ : syracuseStep 2139689 = 1604767) B1604767
theorem B32941885 : Blo 1266451 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B14428367 : Blo 1266451 14428367 := bstep (se 1 (by rfl) ⟨10821275, by rfl⟩ : syracuseStep 14428367 = 21642551) B21642551
theorem B7219651 : Blo 1266451 7219651 := bstep (se 1 (by rfl) ⟨5414738, by rfl⟩ : syracuseStep 7219651 = 10829477) B10829477
theorem B2853467 : Blo 1266451 2853467 := bstep (se 1 (by rfl) ⟨2140100, by rfl⟩ : syracuseStep 2853467 = 4280201) B4280201
theorem B2853611 : Blo 1266451 2853611 := bstep (se 1 (by rfl) ⟨2140208, by rfl⟩ : syracuseStep 2853611 = 4280417) B4280417
theorem B13003895 : Blo 1266451 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B14445863 : Blo 1266451 14445863 := bstep (se 1 (by rfl) ⟨10834397, by rfl⟩ : syracuseStep 14445863 = 21668795) B21668795
theorem B14429825 : Blo 1266451 14429825 := bstep (se 2 (by rfl) ⟨5411184, by rfl⟩ : syracuseStep 14429825 = 10822369) B10822369
theorem B7212887 : Blo 1266451 7212887 := bstep (se 1 (by rfl) ⟨5409665, by rfl⟩ : syracuseStep 7212887 = 10819331) B10819331
theorem B19525673 : Blo 1266451 19525673 := bstep (se 2 (by rfl) ⟨7322127, by rfl⟩ : syracuseStep 19525673 = 14644255) B14644255
theorem B6172745 : Blo 1266451 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B29290733 : Blo 1266451 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B4337999 : Blo 1266451 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B23138905 : Blo 1266451 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B15422633 : Blo 1266451 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B4814255 : Blo 1266451 4814255 := bstep (se 1 (by rfl) ⟨3610691, by rfl⟩ : syracuseStep 4814255 = 7221383) B7221383
theorem B27407963 : Blo 1266451 27407963 := bstep (se 1 (by rfl) ⟨20555972, by rfl⟩ : syracuseStep 27407963 = 41111945) B41111945
theorem B14628509 : Blo 1266451 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B23131831 : Blo 1266451 23131831 := bstep (se 1 (by rfl) ⟨17348873, by rfl⟩ : syracuseStep 23131831 = 34697747) B34697747
theorem B1267407 : Blo 1266451 1267407 := bstep (se 1 (by rfl) ⟨950555, by rfl⟩ : syracuseStep 1267407 = 1901111) B1901111
theorem B1267775 : Blo 1266451 1267775 := bstep (se 1 (by rfl) ⟨950831, by rfl⟩ : syracuseStep 1267775 = 1901663) B1901663
theorem B8231057 : Blo 1266451 8231057 := bstep (se 2 (by rfl) ⟨3086646, by rfl⟩ : syracuseStep 8231057 = 6173293) B6173293
theorem B10828079 : Blo 1266451 10828079 := bstep (se 1 (by rfl) ⟨8121059, by rfl⟩ : syracuseStep 10828079 = 16242119) B16242119
theorem B24697217 : Blo 1266451 24697217 := bstep (se 2 (by rfl) ⟨9261456, by rfl⟩ : syracuseStep 24697217 = 18522913) B18522913
theorem B4062079 : Blo 1266451 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B4275179 : Blo 1266451 4275179 := bstep (se 1 (by rfl) ⟨3206384, by rfl⟩ : syracuseStep 4275179 = 6412769) B6412769
theorem B1899755 : Blo 1266451 1899755 := bstep (se 1 (by rfl) ⟨1424816, by rfl⟩ : syracuseStep 1899755 = 2849633) B2849633
theorem B1899803 : Blo 1266451 1899803 := bstep (se 1 (by rfl) ⟨1424852, by rfl⟩ : syracuseStep 1899803 = 2849705) B2849705
theorem B1899839 : Blo 1266451 1899839 := bstep (se 1 (by rfl) ⟨1424879, by rfl⟩ : syracuseStep 1899839 = 2849759) B2849759
theorem B1899935 : Blo 1266451 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B2137583 : Blo 1266451 2137583 := bstep (se 1 (by rfl) ⟨1603187, by rfl⟩ : syracuseStep 2137583 = 3206375) B3206375
theorem B2407963 : Blo 1266451 2407963 := bstep (se 1 (by rfl) ⟨1805972, by rfl⟩ : syracuseStep 2407963 = 3611945) B3611945
theorem B1900271 : Blo 1266451 1900271 := bstep (se 1 (by rfl) ⟨1425203, by rfl⟩ : syracuseStep 1900271 = 2850407) B2850407
theorem B13017115 : Blo 1266451 13017115 := bstep (se 1 (by rfl) ⟨9762836, by rfl⟩ : syracuseStep 13017115 = 19525673) B19525673
theorem B1900607 : Blo 1266451 1900607 := bstep (se 1 (by rfl) ⟨1425455, by rfl⟩ : syracuseStep 1900607 = 2850911) B2850911
theorem B2850983 : Blo 1266451 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B2891999 : Blo 1266451 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B6095101 : Blo 1266451 6095101 := bstep (se 3 (by rfl) ⟨1142831, by rfl⟩ : syracuseStep 6095101 = 2285663) B2285663
theorem B9626201 : Blo 1266451 9626201 := bstep (se 2 (by rfl) ⟨3609825, by rfl⟩ : syracuseStep 9626201 = 7219651) B7219651
theorem B10281755 : Blo 1266451 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B30851873 : Blo 1266451 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B1426459 : Blo 1266451 1426459 := bstep (se 1 (by rfl) ⟨1069844, by rfl⟩ : syracuseStep 1426459 = 2139689) B2139689
theorem B9618911 : Blo 1266451 9618911 := bstep (se 1 (by rfl) ⟨7214183, by rfl⟩ : syracuseStep 9618911 = 14428367) B14428367
theorem B7218719 : Blo 1266451 7218719 := bstep (se 1 (by rfl) ⟨5414039, by rfl⟩ : syracuseStep 7218719 = 10828079) B10828079
theorem B1902311 : Blo 1266451 1902311 := bstep (se 1 (by rfl) ⟨1426733, by rfl⟩ : syracuseStep 1902311 = 2853467) B2853467
theorem B1902407 : Blo 1266451 1902407 := bstep (se 1 (by rfl) ⟨1426805, by rfl⟩ : syracuseStep 1902407 = 2853611) B2853611
theorem B8669263 : Blo 1266451 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B9619883 : Blo 1266451 9619883 := bstep (se 1 (by rfl) ⟨7214912, by rfl⟩ : syracuseStep 9619883 = 14429825) B14429825
theorem B4811507 : Blo 1266451 4811507 := bstep (se 1 (by rfl) ⟨3608630, by rfl⟩ : syracuseStep 4811507 = 7217261) B7217261
theorem B16460653 : Blo 1266451 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B5140031 : Blo 1266451 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B7220927 : Blo 1266451 7220927 := bstep (se 1 (by rfl) ⟨5415695, by rfl⟩ : syracuseStep 7220927 = 10831391) B10831391
theorem B18271975 : Blo 1266451 18271975 := bstep (se 1 (by rfl) ⟨13703981, by rfl⟩ : syracuseStep 18271975 = 27407963) B27407963
theorem B9752339 : Blo 1266451 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B21664421 : Blo 1266451 21664421 := bstep (se 4 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 21664421 = 4062079) B4062079
theorem B1266503 : Blo 1266451 1266503 := bstep (se 1 (by rfl) ⟨949877, by rfl⟩ : syracuseStep 1266503 = 1899755) B1899755
theorem B1266535 : Blo 1266451 1266535 := bstep (se 1 (by rfl) ⟨949901, by rfl⟩ : syracuseStep 1266535 = 1899803) B1899803
theorem B9630575 : Blo 1266451 9630575 := bstep (se 1 (by rfl) ⟨7222931, by rfl⟩ : syracuseStep 9630575 = 14445863) B14445863
theorem B1266559 : Blo 1266451 1266559 := bstep (se 1 (by rfl) ⟨949919, by rfl⟩ : syracuseStep 1266559 = 1899839) B1899839
theorem B1266623 : Blo 1266451 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B43922513 : Blo 1266451 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B1266847 : Blo 1266451 1266847 := bstep (se 1 (by rfl) ⟨950135, by rfl⟩ : syracuseStep 1266847 = 1900271) B1900271
theorem B19527155 : Blo 1266451 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B61642235 : Blo 1266451 61642235 := bstep (se 1 (by rfl) ⟨46231676, by rfl⟩ : syracuseStep 61642235 = 92463353) B92463353
theorem B3209503 : Blo 1266451 3209503 := bstep (se 1 (by rfl) ⟨2407127, by rfl⟩ : syracuseStep 3209503 = 4814255) B4814255
theorem B5487371 : Blo 1266451 5487371 := bstep (se 1 (by rfl) ⟨4115528, by rfl⟩ : syracuseStep 5487371 = 8231057) B8231057
theorem B16464811 : Blo 1266451 16464811 := bstep (se 1 (by rfl) ⟨12348608, by rfl⟩ : syracuseStep 16464811 = 24697217) B24697217
theorem B2850119 : Blo 1266451 2850119 := bstep (se 1 (by rfl) ⟨2137589, by rfl⟩ : syracuseStep 2850119 = 4275179) B4275179
theorem B3210617 : Blo 1266451 3210617 := bstep (se 2 (by rfl) ⟨1203981, by rfl⟩ : syracuseStep 3210617 = 2407963) B2407963
theorem B30842441 : Blo 1266451 30842441 := bstep (se 2 (by rfl) ⟨11565915, by rfl⟩ : syracuseStep 30842441 = 23131831) B23131831
theorem B1425055 : Blo 1266451 1425055 := bstep (se 1 (by rfl) ⟨1068791, by rfl⟩ : syracuseStep 1425055 = 2137583) B2137583
theorem B4808591 : Blo 1266451 4808591 := bstep (se 1 (by rfl) ⟨3606443, by rfl⟩ : syracuseStep 4808591 = 7212887) B7212887
theorem B11559017 : Blo 1266451 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B1900655 : Blo 1266451 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B8126801 : Blo 1266451 8126801 := bstep (se 2 (by rfl) ⟨3047550, by rfl⟩ : syracuseStep 8126801 = 6095101) B6095101
theorem B14442947 : Blo 1266451 14442947 := bstep (se 1 (by rfl) ⟨10832210, by rfl⟩ : syracuseStep 14442947 = 21664421) B21664421
theorem B13018103 : Blo 1266451 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B21947537 : Blo 1266451 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B1901945 : Blo 1266451 1901945 := bstep (se 2 (by rfl) ⟨713229, by rfl⟩ : syracuseStep 1901945 = 1426459) B1426459
theorem B13706749 : Blo 1266451 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B2140411 : Blo 1266451 2140411 := bstep (se 1 (by rfl) ⟨1605308, by rfl⟩ : syracuseStep 2140411 = 3210617) B3210617
theorem B3205727 : Blo 1266451 3205727 := bstep (se 1 (by rfl) ⟨2404295, by rfl⟩ : syracuseStep 3205727 = 4808591) B4808591
theorem B1927999 : Blo 1266451 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B4279337 : Blo 1266451 4279337 := bstep (se 2 (by rfl) ⟨1604751, by rfl⟩ : syracuseStep 4279337 = 3209503) B3209503
theorem B6417467 : Blo 1266451 6417467 := bstep (se 1 (by rfl) ⟨4813100, by rfl⟩ : syracuseStep 6417467 = 9626201) B9626201
theorem B29281675 : Blo 1266451 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B41094823 : Blo 1266451 41094823 := bstep (se 1 (by rfl) ⟨30821117, by rfl⟩ : syracuseStep 41094823 = 61642235) B61642235
theorem B4812479 : Blo 1266451 4812479 := bstep (se 1 (by rfl) ⟨3609359, by rfl⟩ : syracuseStep 4812479 = 7218719) B7218719
theorem B3207671 : Blo 1266451 3207671 := bstep (se 1 (by rfl) ⟨2405753, by rfl⟩ : syracuseStep 3207671 = 4811507) B4811507
theorem B3658247 : Blo 1266451 3658247 := bstep (se 1 (by rfl) ⟨2743685, by rfl⟩ : syracuseStep 3658247 = 5487371) B5487371
theorem B4813951 : Blo 1266451 4813951 := bstep (se 1 (by rfl) ⟨3610463, by rfl⟩ : syracuseStep 4813951 = 7220927) B7220927
theorem B6501559 : Blo 1266451 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B17356153 : Blo 1266451 17356153 := bstep (se 2 (by rfl) ⟨6508557, by rfl⟩ : syracuseStep 17356153 = 13017115) B13017115
theorem B1267071 : Blo 1266451 1267071 := bstep (se 1 (by rfl) ⟨950303, by rfl⟩ : syracuseStep 1267071 = 1900607) B1900607
theorem B6854503 : Blo 1266451 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B20567915 : Blo 1266451 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B6420383 : Blo 1266451 6420383 := bstep (se 1 (by rfl) ⟨4815287, by rfl⟩ : syracuseStep 6420383 = 9630575) B9630575
theorem B6412607 : Blo 1266451 6412607 := bstep (se 1 (by rfl) ⟨4809455, by rfl⟩ : syracuseStep 6412607 = 9618911) B9618911
theorem B1268207 : Blo 1266451 1268207 := bstep (se 1 (by rfl) ⟨951155, by rfl⟩ : syracuseStep 1268207 = 1902311) B1902311
theorem B1268271 : Blo 1266451 1268271 := bstep (se 1 (by rfl) ⟨951203, by rfl⟩ : syracuseStep 1268271 = 1902407) B1902407
theorem B21953081 : Blo 1266451 21953081 := bstep (se 2 (by rfl) ⟨8232405, by rfl⟩ : syracuseStep 21953081 = 16464811) B16464811
theorem B6413255 : Blo 1266451 6413255 := bstep (se 1 (by rfl) ⟨4809941, by rfl⟩ : syracuseStep 6413255 = 9619883) B9619883
theorem B1900073 : Blo 1266451 1900073 := bstep (se 2 (by rfl) ⟨712527, by rfl⟩ : syracuseStep 1900073 = 1425055) B1425055
theorem B1900079 : Blo 1266451 1900079 := bstep (se 1 (by rfl) ⟨1425059, by rfl⟩ : syracuseStep 1900079 = 2850119) B2850119
theorem B24362633 : Blo 1266451 24362633 := bstep (se 2 (by rfl) ⟨9135987, by rfl⟩ : syracuseStep 24362633 = 18271975) B18271975
theorem B20561627 : Blo 1266451 20561627 := bstep (se 1 (by rfl) ⟨15421220, by rfl⟩ : syracuseStep 20561627 = 30842441) B30842441
theorem B2138447 : Blo 1266451 2138447 := bstep (se 1 (by rfl) ⟨1603835, by rfl⟩ : syracuseStep 2138447 = 3207671) B3207671
theorem B14631691 : Blo 1266451 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B8668745 : Blo 1266451 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B2852891 : Blo 1266451 2852891 := bstep (se 1 (by rfl) ⟨2139668, by rfl⟩ : syracuseStep 2852891 = 4279337) B4279337
theorem B4278311 : Blo 1266451 4278311 := bstep (se 1 (by rfl) ⟨3208733, by rfl⟩ : syracuseStep 4278311 = 6417467) B6417467
theorem B13707751 : Blo 1266451 13707751 := bstep (se 1 (by rfl) ⟨10280813, by rfl⟩ : syracuseStep 13707751 = 20561627) B20561627
theorem B5417867 : Blo 1266451 5417867 := bstep (se 1 (by rfl) ⟨4063400, by rfl⟩ : syracuseStep 5417867 = 8126801) B8126801
theorem B9628631 : Blo 1266451 9628631 := bstep (se 1 (by rfl) ⟨7221473, by rfl⟩ : syracuseStep 9628631 = 14442947) B14442947
theorem B2853881 : Blo 1266451 2853881 := bstep (se 2 (by rfl) ⟨1070205, by rfl⟩ : syracuseStep 2853881 = 2140411) B2140411
theorem B8678735 : Blo 1266451 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B4280255 : Blo 1266451 4280255 := bstep (se 1 (by rfl) ⟨3210191, by rfl⟩ : syracuseStep 4280255 = 6420383) B6420383
theorem B6418601 : Blo 1266451 6418601 := bstep (se 2 (by rfl) ⟨2406975, by rfl⟩ : syracuseStep 6418601 = 4813951) B4813951
theorem B14635387 : Blo 1266451 14635387 := bstep (se 1 (by rfl) ⟨10976540, by rfl⟩ : syracuseStep 14635387 = 21953081) B21953081
theorem B54793097 : Blo 1266451 54793097 := bstep (se 2 (by rfl) ⟨20547411, by rfl⟩ : syracuseStep 54793097 = 41094823) B41094823
theorem B1266715 : Blo 1266451 1266715 := bstep (se 1 (by rfl) ⟨950036, by rfl⟩ : syracuseStep 1266715 = 1900073) B1900073
theorem B1266719 : Blo 1266451 1266719 := bstep (se 1 (by rfl) ⟨950039, by rfl⟩ : syracuseStep 1266719 = 1900079) B1900079
theorem B16241755 : Blo 1266451 16241755 := bstep (se 1 (by rfl) ⟨12181316, by rfl⟩ : syracuseStep 16241755 = 24362633) B24362633
theorem B3208319 : Blo 1266451 3208319 := bstep (se 1 (by rfl) ⟨2406239, by rfl⟩ : syracuseStep 3208319 = 4812479) B4812479
theorem B9139337 : Blo 1266451 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B73102661 : Blo 1266451 73102661 := bstep (se 4 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 73102661 = 13706749) B13706749
theorem B7706011 : Blo 1266451 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B1267103 : Blo 1266451 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B2438831 : Blo 1266451 2438831 := bstep (se 1 (by rfl) ⟨1829123, by rfl⟩ : syracuseStep 2438831 = 3658247) B3658247
theorem B1267963 : Blo 1266451 1267963 := bstep (se 1 (by rfl) ⟨950972, by rfl⟩ : syracuseStep 1267963 = 1901945) B1901945
theorem B2570665 : Blo 1266451 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B13711943 : Blo 1266451 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B4275071 : Blo 1266451 4275071 := bstep (se 1 (by rfl) ⟨3206303, by rfl⟩ : syracuseStep 4275071 = 6412607) B6412607
theorem B2137151 : Blo 1266451 2137151 := bstep (se 1 (by rfl) ⟨1602863, by rfl⟩ : syracuseStep 2137151 = 3205727) B3205727
theorem B23141537 : Blo 1266451 23141537 := bstep (se 2 (by rfl) ⟨8678076, by rfl⟩ : syracuseStep 23141537 = 17356153) B17356153
theorem B39042233 : Blo 1266451 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B4275503 : Blo 1266451 4275503 := bstep (se 1 (by rfl) ⟨3206627, by rfl⟩ : syracuseStep 4275503 = 6413255) B6413255
theorem B1425631 : Blo 1266451 1425631 := bstep (se 1 (by rfl) ⟨1069223, by rfl⟩ : syracuseStep 1425631 = 2138447) B2138447
theorem B36528731 : Blo 1266451 36528731 := bstep (se 1 (by rfl) ⟨27396548, by rfl⟩ : syracuseStep 36528731 = 54793097) B54793097
theorem B18277001 : Blo 1266451 18277001 := bstep (se 2 (by rfl) ⟨6853875, by rfl⟩ : syracuseStep 18277001 = 13707751) B13707751
theorem B2138879 : Blo 1266451 2138879 := bstep (se 1 (by rfl) ⟨1604159, by rfl⟩ : syracuseStep 2138879 = 3208319) B3208319
theorem B48735107 : Blo 1266451 48735107 := bstep (se 1 (by rfl) ⟨36551330, by rfl⟩ : syracuseStep 48735107 = 73102661) B73102661
theorem B1901927 : Blo 1266451 1901927 := bstep (se 1 (by rfl) ⟨1426445, by rfl⟩ : syracuseStep 1901927 = 2852891) B2852891
theorem B2852207 : Blo 1266451 2852207 := bstep (se 1 (by rfl) ⟨2139155, by rfl⟩ : syracuseStep 2852207 = 4278311) B4278311
theorem B10274681 : Blo 1266451 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B78055397 : Blo 1266451 78055397 := bstep (se 4 (by rfl) ⟨7317693, by rfl⟩ : syracuseStep 78055397 = 14635387) B14635387
theorem B1902587 : Blo 1266451 1902587 := bstep (se 1 (by rfl) ⟨1426940, by rfl⟩ : syracuseStep 1902587 = 2853881) B2853881
theorem B15427691 : Blo 1266451 15427691 := bstep (se 1 (by rfl) ⟨11570768, by rfl⟩ : syracuseStep 15427691 = 23141537) B23141537
theorem B26028155 : Blo 1266451 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B5785823 : Blo 1266451 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B2853503 : Blo 1266451 2853503 := bstep (se 1 (by rfl) ⟨2140127, by rfl⟩ : syracuseStep 2853503 = 4280255) B4280255
theorem B4279067 : Blo 1266451 4279067 := bstep (se 1 (by rfl) ⟨3209300, by rfl⟩ : syracuseStep 4279067 = 6418601) B6418601
theorem B3427553 : Blo 1266451 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B19508921 : Blo 1266451 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B5779163 : Blo 1266451 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B1625887 : Blo 1266451 1625887 := bstep (se 1 (by rfl) ⟨1219415, by rfl⟩ : syracuseStep 1625887 = 2438831) B2438831
theorem B21655673 : Blo 1266451 21655673 := bstep (se 2 (by rfl) ⟨8120877, by rfl⟩ : syracuseStep 21655673 = 16241755) B16241755
theorem B6419087 : Blo 1266451 6419087 := bstep (se 1 (by rfl) ⟨4814315, by rfl⟩ : syracuseStep 6419087 = 9628631) B9628631
theorem B6092891 : Blo 1266451 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B9141295 : Blo 1266451 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B2850047 : Blo 1266451 2850047 := bstep (se 1 (by rfl) ⟨2137535, by rfl⟩ : syracuseStep 2850047 = 4275071) B4275071
theorem B3611911 : Blo 1266451 3611911 := bstep (se 1 (by rfl) ⟨2708933, by rfl⟩ : syracuseStep 3611911 = 5417867) B5417867
theorem B1424767 : Blo 1266451 1424767 := bstep (se 1 (by rfl) ⟨1068575, by rfl⟩ : syracuseStep 1424767 = 2137151) B2137151
theorem B2850335 : Blo 1266451 2850335 := bstep (se 1 (by rfl) ⟨2137751, by rfl⟩ : syracuseStep 2850335 = 4275503) B4275503
theorem B1900841 : Blo 1266451 1900841 := bstep (se 2 (by rfl) ⟨712815, by rfl⟩ : syracuseStep 1900841 = 1425631) B1425631
theorem B1425919 : Blo 1266451 1425919 := bstep (se 1 (by rfl) ⟨1069439, by rfl⟩ : syracuseStep 1425919 = 2138879) B2138879
theorem B32490071 : Blo 1266451 32490071 := bstep (se 1 (by rfl) ⟨24367553, by rfl⟩ : syracuseStep 32490071 = 48735107) B48735107
theorem B1901471 : Blo 1266451 1901471 := bstep (se 1 (by rfl) ⟨1426103, by rfl⟩ : syracuseStep 1901471 = 2852207) B2852207
theorem B6849787 : Blo 1266451 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B52036931 : Blo 1266451 52036931 := bstep (se 1 (by rfl) ⟨39027698, by rfl⟩ : syracuseStep 52036931 = 78055397) B78055397
theorem B17352103 : Blo 1266451 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B1902335 : Blo 1266451 1902335 := bstep (se 1 (by rfl) ⟨1426751, by rfl⟩ : syracuseStep 1902335 = 2853503) B2853503
theorem B2852711 : Blo 1266451 2852711 := bstep (se 1 (by rfl) ⟨2139533, by rfl⟩ : syracuseStep 2852711 = 4279067) B4279067
theorem B3852775 : Blo 1266451 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B14437115 : Blo 1266451 14437115 := bstep (se 1 (by rfl) ⟨10827836, by rfl⟩ : syracuseStep 14437115 = 21655673) B21655673
theorem B12184667 : Blo 1266451 12184667 := bstep (se 1 (by rfl) ⟨9138500, by rfl⟩ : syracuseStep 12184667 = 18277001) B18277001
theorem B4279391 : Blo 1266451 4279391 := bstep (se 1 (by rfl) ⟨3209543, by rfl⟩ : syracuseStep 4279391 = 6419087) B6419087
theorem B10285127 : Blo 1266451 10285127 := bstep (se 1 (by rfl) ⟨7713845, by rfl⟩ : syracuseStep 10285127 = 15427691) B15427691
theorem B2167849 : Blo 1266451 2167849 := bstep (se 2 (by rfl) ⟨812943, by rfl⟩ : syracuseStep 2167849 = 1625887) B1625887
theorem B13005947 : Blo 1266451 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B24352487 : Blo 1266451 24352487 := bstep (se 1 (by rfl) ⟨18264365, by rfl⟩ : syracuseStep 24352487 = 36528731) B36528731
theorem B9140141 : Blo 1266451 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B1267951 : Blo 1266451 1267951 := bstep (se 1 (by rfl) ⟨950963, by rfl⟩ : syracuseStep 1267951 = 1901927) B1901927
theorem B1268391 : Blo 1266451 1268391 := bstep (se 1 (by rfl) ⟨951293, by rfl⟩ : syracuseStep 1268391 = 1902587) B1902587
theorem B4061927 : Blo 1266451 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B12188393 : Blo 1266451 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B3857215 : Blo 1266451 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B4815881 : Blo 1266451 4815881 := bstep (se 2 (by rfl) ⟨1805955, by rfl⟩ : syracuseStep 4815881 = 3611911) B3611911
theorem B1899689 : Blo 1266451 1899689 := bstep (se 2 (by rfl) ⟨712383, by rfl⟩ : syracuseStep 1899689 = 1424767) B1424767
theorem B1900031 : Blo 1266451 1900031 := bstep (se 1 (by rfl) ⟨1425023, by rfl⟩ : syracuseStep 1900031 = 2850047) B2850047
theorem B1900223 : Blo 1266451 1900223 := bstep (se 1 (by rfl) ⟨1425167, by rfl⟩ : syracuseStep 1900223 = 2850335) B2850335
theorem B6856751 : Blo 1266451 6856751 := bstep (se 1 (by rfl) ⟨5142563, by rfl⟩ : syracuseStep 6856751 = 10285127) B10285127
theorem B21660047 : Blo 1266451 21660047 := bstep (se 1 (by rfl) ⟨16245035, by rfl⟩ : syracuseStep 21660047 = 32490071) B32490071
theorem B5137033 : Blo 1266451 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B1901225 : Blo 1266451 1901225 := bstep (se 2 (by rfl) ⟨712959, by rfl⟩ : syracuseStep 1901225 = 1425919) B1425919
theorem B1901807 : Blo 1266451 1901807 := bstep (se 1 (by rfl) ⟨1426355, by rfl⟩ : syracuseStep 1901807 = 2852711) B2852711
theorem B23136137 : Blo 1266451 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B2852927 : Blo 1266451 2852927 := bstep (se 1 (by rfl) ⟨2139695, by rfl⟩ : syracuseStep 2852927 = 4279391) B4279391
theorem B11561861 : Blo 1266451 11561861 := bstep (se 4 (by rfl) ⟨1083924, by rfl⟩ : syracuseStep 11561861 = 2167849) B2167849
theorem B2707951 : Blo 1266451 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B8123111 : Blo 1266451 8123111 := bstep (se 1 (by rfl) ⟨6092333, by rfl⟩ : syracuseStep 8123111 = 12184667) B12184667
theorem B1266459 : Blo 1266451 1266459 := bstep (se 1 (by rfl) ⟨949844, by rfl⟩ : syracuseStep 1266459 = 1899689) B1899689
theorem B1266687 : Blo 1266451 1266687 := bstep (se 1 (by rfl) ⟨950015, by rfl⟩ : syracuseStep 1266687 = 1900031) B1900031
theorem B1266815 : Blo 1266451 1266815 := bstep (se 1 (by rfl) ⟨950111, by rfl⟩ : syracuseStep 1266815 = 1900223) B1900223
theorem B1267227 : Blo 1266451 1267227 := bstep (se 1 (by rfl) ⟨950420, by rfl⟩ : syracuseStep 1267227 = 1900841) B1900841
theorem B34682525 : Blo 1266451 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B1267647 : Blo 1266451 1267647 := bstep (se 1 (by rfl) ⟨950735, by rfl⟩ : syracuseStep 1267647 = 1901471) B1901471
theorem B34691287 : Blo 1266451 34691287 := bstep (se 1 (by rfl) ⟨26018465, by rfl⟩ : syracuseStep 34691287 = 52036931) B52036931
theorem B5142953 : Blo 1266451 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B16234991 : Blo 1266451 16234991 := bstep (se 1 (by rfl) ⟨12176243, by rfl⟩ : syracuseStep 16234991 = 24352487) B24352487
theorem B1268223 : Blo 1266451 1268223 := bstep (se 1 (by rfl) ⟨951167, by rfl⟩ : syracuseStep 1268223 = 1902335) B1902335
theorem B6093427 : Blo 1266451 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B9133049 : Blo 1266451 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B8125595 : Blo 1266451 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B9624743 : Blo 1266451 9624743 := bstep (se 1 (by rfl) ⟨7218557, by rfl⟩ : syracuseStep 9624743 = 14437115) B14437115
theorem B3210587 : Blo 1266451 3210587 := bstep (se 1 (by rfl) ⟨2407940, by rfl⟩ : syracuseStep 3210587 = 4815881) B4815881
theorem B4571167 : Blo 1266451 4571167 := bstep (se 1 (by rfl) ⟨3428375, by rfl⟩ : syracuseStep 4571167 = 6856751) B6856751
theorem B5415407 : Blo 1266451 5415407 := bstep (se 1 (by rfl) ⟨4061555, by rfl⟩ : syracuseStep 5415407 = 8123111) B8123111
theorem B6849377 : Blo 1266451 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B13714541 : Blo 1266451 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B1901951 : Blo 1266451 1901951 := bstep (se 1 (by rfl) ⟨1426463, by rfl⟩ : syracuseStep 1901951 = 2852927) B2852927
theorem B10823327 : Blo 1266451 10823327 := bstep (se 1 (by rfl) ⟨8117495, by rfl⟩ : syracuseStep 10823327 = 16234991) B16234991
theorem B6088699 : Blo 1266451 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B5417063 : Blo 1266451 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B6416495 : Blo 1266451 6416495 := bstep (se 1 (by rfl) ⟨4812371, by rfl⟩ : syracuseStep 6416495 = 9624743) B9624743
theorem B2140391 : Blo 1266451 2140391 := bstep (se 1 (by rfl) ⟨1605293, by rfl⟩ : syracuseStep 2140391 = 3210587) B3210587
theorem B46255049 : Blo 1266451 46255049 := bstep (se 2 (by rfl) ⟨17345643, by rfl⟩ : syracuseStep 46255049 = 34691287) B34691287
theorem B23121683 : Blo 1266451 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B14440031 : Blo 1266451 14440031 := bstep (se 1 (by rfl) ⟨10830023, by rfl⟩ : syracuseStep 14440031 = 21660047) B21660047
theorem B1267483 : Blo 1266451 1267483 := bstep (se 1 (by rfl) ⟨950612, by rfl⟩ : syracuseStep 1267483 = 1901225) B1901225
theorem B3610601 : Blo 1266451 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B8124569 : Blo 1266451 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B1267871 : Blo 1266451 1267871 := bstep (se 1 (by rfl) ⟨950903, by rfl⟩ : syracuseStep 1267871 = 1901807) B1901807
theorem B15424091 : Blo 1266451 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B7707907 : Blo 1266451 7707907 := bstep (se 1 (by rfl) ⟨5780930, by rfl⟩ : syracuseStep 7707907 = 11561861) B11561861
theorem B6094889 : Blo 1266451 6094889 := bstep (se 2 (by rfl) ⟨2285583, by rfl⟩ : syracuseStep 6094889 = 4571167) B4571167
theorem B9143027 : Blo 1266451 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B9626687 : Blo 1266451 9626687 := bstep (se 1 (by rfl) ⟨7220015, by rfl⟩ : syracuseStep 9626687 = 14440031) B14440031
theorem B4277663 : Blo 1266451 4277663 := bstep (se 1 (by rfl) ⟨3208247, by rfl⟩ : syracuseStep 4277663 = 6416495) B6416495
theorem B5416379 : Blo 1266451 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B1426927 : Blo 1266451 1426927 := bstep (se 1 (by rfl) ⟨1070195, by rfl⟩ : syracuseStep 1426927 = 2140391) B2140391
theorem B10282727 : Blo 1266451 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B30836699 : Blo 1266451 30836699 := bstep (se 1 (by rfl) ⟨23127524, by rfl⟩ : syracuseStep 30836699 = 46255049) B46255049
theorem B4566251 : Blo 1266451 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B10277209 : Blo 1266451 10277209 := bstep (se 2 (by rfl) ⟨3853953, by rfl⟩ : syracuseStep 10277209 = 7707907) B7707907
theorem B15414455 : Blo 1266451 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B3610271 : Blo 1266451 3610271 := bstep (se 1 (by rfl) ⟨2707703, by rfl⟩ : syracuseStep 3610271 = 5415407) B5415407
theorem B1267967 : Blo 1266451 1267967 := bstep (se 1 (by rfl) ⟨950975, by rfl⟩ : syracuseStep 1267967 = 1901951) B1901951
theorem B7215551 : Blo 1266451 7215551 := bstep (se 1 (by rfl) ⟨5411663, by rfl⟩ : syracuseStep 7215551 = 10823327) B10823327
theorem B2407067 : Blo 1266451 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B3611375 : Blo 1266451 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B8118265 : Blo 1266451 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B4063259 : Blo 1266451 4063259 := bstep (se 1 (by rfl) ⟨3047444, by rfl⟩ : syracuseStep 4063259 = 6094889) B6094889
theorem B6095351 : Blo 1266451 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B2851775 : Blo 1266451 2851775 := bstep (se 1 (by rfl) ⟨2138831, by rfl⟩ : syracuseStep 2851775 = 4277663) B4277663
theorem B4810367 : Blo 1266451 4810367 := bstep (se 1 (by rfl) ⟨3607775, by rfl⟩ : syracuseStep 4810367 = 7215551) B7215551
theorem B27420605 : Blo 1266451 27420605 := bstep (se 3 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 27420605 = 10282727) B10282727
theorem B1902569 : Blo 1266451 1902569 := bstep (se 2 (by rfl) ⟨713463, by rfl⟩ : syracuseStep 1902569 = 1426927) B1426927
theorem B10824353 : Blo 1266451 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B12176669 : Blo 1266451 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B6417791 : Blo 1266451 6417791 := bstep (se 1 (by rfl) ⟨4813343, by rfl⟩ : syracuseStep 6417791 = 9626687) B9626687
theorem B10276303 : Blo 1266451 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B20557799 : Blo 1266451 20557799 := bstep (se 1 (by rfl) ⟨15418349, by rfl⟩ : syracuseStep 20557799 = 30836699) B30836699
theorem B13702945 : Blo 1266451 13702945 := bstep (se 2 (by rfl) ⟨5138604, by rfl⟩ : syracuseStep 13702945 = 10277209) B10277209
theorem B3610919 : Blo 1266451 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B2406847 : Blo 1266451 2406847 := bstep (se 1 (by rfl) ⟨1805135, by rfl⟩ : syracuseStep 2406847 = 3610271) B3610271
theorem B1604711 : Blo 1266451 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B2407583 : Blo 1266451 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B4063567 : Blo 1266451 4063567 := bstep (se 1 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 4063567 = 6095351) B6095351
theorem B1901183 : Blo 1266451 1901183 := bstep (se 1 (by rfl) ⟨1425887, by rfl⟩ : syracuseStep 1901183 = 2851775) B2851775
theorem B4278527 : Blo 1266451 4278527 := bstep (se 1 (by rfl) ⟨3208895, by rfl⟩ : syracuseStep 4278527 = 6417791) B6417791
theorem B18270593 : Blo 1266451 18270593 := bstep (se 2 (by rfl) ⟨6851472, by rfl⟩ : syracuseStep 18270593 = 13702945) B13702945
theorem B4279229 : Blo 1266451 4279229 := bstep (se 3 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 4279229 = 1604711) B1604711
theorem B9629117 : Blo 1266451 9629117 := bstep (se 3 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 9629117 = 3610919) B3610919
theorem B3206911 : Blo 1266451 3206911 := bstep (se 1 (by rfl) ⟨2405183, by rfl⟩ : syracuseStep 3206911 = 4810367) B4810367
theorem B18280403 : Blo 1266451 18280403 := bstep (se 1 (by rfl) ⟨13710302, by rfl⟩ : syracuseStep 18280403 = 27420605) B27420605
theorem B13701737 : Blo 1266451 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B2708839 : Blo 1266451 2708839 := bstep (se 1 (by rfl) ⟨2031629, by rfl⟩ : syracuseStep 2708839 = 4063259) B4063259
theorem B6420221 : Blo 1266451 6420221 := bstep (se 3 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 6420221 = 2407583) B2407583
theorem B3209129 : Blo 1266451 3209129 := bstep (se 2 (by rfl) ⟨1203423, by rfl⟩ : syracuseStep 3209129 = 2406847) B2406847
theorem B1268379 : Blo 1266451 1268379 := bstep (se 1 (by rfl) ⟨951284, by rfl⟩ : syracuseStep 1268379 = 1902569) B1902569
theorem B7216235 : Blo 1266451 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B8117779 : Blo 1266451 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B13705199 : Blo 1266451 13705199 := bstep (se 1 (by rfl) ⟨10278899, by rfl⟩ : syracuseStep 13705199 = 20557799) B20557799
theorem B9134491 : Blo 1266451 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B2139419 : Blo 1266451 2139419 := bstep (se 1 (by rfl) ⟨1604564, by rfl⟩ : syracuseStep 2139419 = 3209129) B3209129
theorem B2852351 : Blo 1266451 2852351 := bstep (se 1 (by rfl) ⟨2139263, by rfl⟩ : syracuseStep 2852351 = 4278527) B4278527
theorem B2852819 : Blo 1266451 2852819 := bstep (se 1 (by rfl) ⟨2139614, by rfl⟩ : syracuseStep 2852819 = 4279229) B4279229
theorem B10823705 : Blo 1266451 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B4810823 : Blo 1266451 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B9136799 : Blo 1266451 9136799 := bstep (se 1 (by rfl) ⟨6852599, by rfl⟩ : syracuseStep 9136799 = 13705199) B13705199
theorem B5418089 : Blo 1266451 5418089 := bstep (se 2 (by rfl) ⟨2031783, by rfl⟩ : syracuseStep 5418089 = 4063567) B4063567
theorem B4280147 : Blo 1266451 4280147 := bstep (se 1 (by rfl) ⟨3210110, by rfl⟩ : syracuseStep 4280147 = 6420221) B6420221
theorem B6419411 : Blo 1266451 6419411 := bstep (se 1 (by rfl) ⟨4814558, by rfl⟩ : syracuseStep 6419411 = 9629117) B9629117
theorem B12186935 : Blo 1266451 12186935 := bstep (se 1 (by rfl) ⟨9140201, by rfl⟩ : syracuseStep 12186935 = 18280403) B18280403
theorem B1267455 : Blo 1266451 1267455 := bstep (se 1 (by rfl) ⟨950591, by rfl⟩ : syracuseStep 1267455 = 1901183) B1901183
theorem B12180395 : Blo 1266451 12180395 := bstep (se 1 (by rfl) ⟨9135296, by rfl⟩ : syracuseStep 12180395 = 18270593) B18270593
theorem B3611785 : Blo 1266451 3611785 := bstep (se 2 (by rfl) ⟨1354419, by rfl⟩ : syracuseStep 3611785 = 2708839) B2708839
theorem B4275881 : Blo 1266451 4275881 := bstep (se 2 (by rfl) ⟨1603455, by rfl⟩ : syracuseStep 4275881 = 3206911) B3206911
theorem B1426279 : Blo 1266451 1426279 := bstep (se 1 (by rfl) ⟨1069709, by rfl⟩ : syracuseStep 1426279 = 2139419) B2139419
theorem B1901567 : Blo 1266451 1901567 := bstep (se 1 (by rfl) ⟨1426175, by rfl⟩ : syracuseStep 1901567 = 2852351) B2852351
theorem B1901879 : Blo 1266451 1901879 := bstep (se 1 (by rfl) ⟨1426409, by rfl⟩ : syracuseStep 1901879 = 2852819) B2852819
theorem B8120263 : Blo 1266451 8120263 := bstep (se 1 (by rfl) ⟨6090197, by rfl⟩ : syracuseStep 8120263 = 12180395) B12180395
theorem B2853431 : Blo 1266451 2853431 := bstep (se 1 (by rfl) ⟨2140073, by rfl⟩ : syracuseStep 2853431 = 4280147) B4280147
theorem B4279607 : Blo 1266451 4279607 := bstep (se 1 (by rfl) ⟨3209705, by rfl⟩ : syracuseStep 4279607 = 6419411) B6419411
theorem B3207215 : Blo 1266451 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B6091199 : Blo 1266451 6091199 := bstep (se 1 (by rfl) ⟨4568399, by rfl⟩ : syracuseStep 6091199 = 9136799) B9136799
theorem B12179321 : Blo 1266451 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B8124623 : Blo 1266451 8124623 := bstep (se 1 (by rfl) ⟨6093467, by rfl⟩ : syracuseStep 8124623 = 12186935) B12186935
theorem B7215803 : Blo 1266451 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B4815713 : Blo 1266451 4815713 := bstep (se 2 (by rfl) ⟨1805892, by rfl⟩ : syracuseStep 4815713 = 3611785) B3611785
theorem B3612059 : Blo 1266451 3612059 := bstep (se 1 (by rfl) ⟨2709044, by rfl⟩ : syracuseStep 3612059 = 5418089) B5418089
theorem B2850587 : Blo 1266451 2850587 := bstep (se 1 (by rfl) ⟨2137940, by rfl⟩ : syracuseStep 2850587 = 4275881) B4275881
theorem B2138143 : Blo 1266451 2138143 := bstep (se 1 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 2138143 = 3207215) B3207215
theorem B1901705 : Blo 1266451 1901705 := bstep (se 2 (by rfl) ⟨713139, by rfl⟩ : syracuseStep 1901705 = 1426279) B1426279
theorem B8119547 : Blo 1266451 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B5416415 : Blo 1266451 5416415 := bstep (se 1 (by rfl) ⟨4062311, by rfl⟩ : syracuseStep 5416415 = 8124623) B8124623
theorem B1902287 : Blo 1266451 1902287 := bstep (se 1 (by rfl) ⟨1426715, by rfl⟩ : syracuseStep 1902287 = 2853431) B2853431
theorem B4810535 : Blo 1266451 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B2853071 : Blo 1266451 2853071 := bstep (se 1 (by rfl) ⟨2139803, by rfl⟩ : syracuseStep 2853071 = 4279607) B4279607
theorem B10827017 : Blo 1266451 10827017 := bstep (se 2 (by rfl) ⟨4060131, by rfl⟩ : syracuseStep 10827017 = 8120263) B8120263
theorem B4060799 : Blo 1266451 4060799 := bstep (se 1 (by rfl) ⟨3045599, by rfl⟩ : syracuseStep 4060799 = 6091199) B6091199
theorem B1267711 : Blo 1266451 1267711 := bstep (se 1 (by rfl) ⟨950783, by rfl⟩ : syracuseStep 1267711 = 1901567) B1901567
theorem B1267919 : Blo 1266451 1267919 := bstep (se 1 (by rfl) ⟨950939, by rfl⟩ : syracuseStep 1267919 = 1901879) B1901879
theorem B3210475 : Blo 1266451 3210475 := bstep (se 1 (by rfl) ⟨2407856, by rfl⟩ : syracuseStep 3210475 = 4815713) B4815713
theorem B2408039 : Blo 1266451 2408039 := bstep (se 1 (by rfl) ⟨1806029, by rfl⟩ : syracuseStep 2408039 = 3612059) B3612059
theorem B1900391 : Blo 1266451 1900391 := bstep (se 1 (by rfl) ⟨1425293, by rfl⟩ : syracuseStep 1900391 = 2850587) B2850587
theorem B2850857 : Blo 1266451 2850857 := bstep (se 2 (by rfl) ⟨1069071, by rfl⟩ : syracuseStep 2850857 = 2138143) B2138143
theorem B7218011 : Blo 1266451 7218011 := bstep (se 1 (by rfl) ⟨5413508, by rfl⟩ : syracuseStep 7218011 = 10827017) B10827017
theorem B1902047 : Blo 1266451 1902047 := bstep (se 1 (by rfl) ⟨1426535, by rfl⟩ : syracuseStep 1902047 = 2853071) B2853071
theorem B2707199 : Blo 1266451 2707199 := bstep (se 1 (by rfl) ⟨2030399, by rfl⟩ : syracuseStep 2707199 = 4060799) B4060799
theorem B3207023 : Blo 1266451 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B4280633 : Blo 1266451 4280633 := bstep (se 2 (by rfl) ⟨1605237, by rfl⟩ : syracuseStep 4280633 = 3210475) B3210475
theorem B1266927 : Blo 1266451 1266927 := bstep (se 1 (by rfl) ⟨950195, by rfl⟩ : syracuseStep 1266927 = 1900391) B1900391
theorem B1267803 : Blo 1266451 1267803 := bstep (se 1 (by rfl) ⟨950852, by rfl⟩ : syracuseStep 1267803 = 1901705) B1901705
theorem B5413031 : Blo 1266451 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B3610943 : Blo 1266451 3610943 := bstep (se 1 (by rfl) ⟨2708207, by rfl⟩ : syracuseStep 3610943 = 5416415) B5416415
theorem B1268191 : Blo 1266451 1268191 := bstep (se 1 (by rfl) ⟨951143, by rfl⟩ : syracuseStep 1268191 = 1902287) B1902287
theorem B1605359 : Blo 1266451 1605359 := bstep (se 1 (by rfl) ⟨1204019, by rfl⟩ : syracuseStep 1605359 = 2408039) B2408039
theorem B1900571 : Blo 1266451 1900571 := bstep (se 1 (by rfl) ⟨1425428, by rfl⟩ : syracuseStep 1900571 = 2850857) B2850857
theorem B1804799 : Blo 1266451 1804799 := bstep (se 1 (by rfl) ⟨1353599, by rfl⟩ : syracuseStep 1804799 = 2707199) B2707199
theorem B2853755 : Blo 1266451 2853755 := bstep (se 1 (by rfl) ⟨2140316, by rfl⟩ : syracuseStep 2853755 = 4280633) B4280633
theorem B4812007 : Blo 1266451 4812007 := bstep (se 1 (by rfl) ⟨3609005, by rfl⟩ : syracuseStep 4812007 = 7218011) B7218011
theorem B3608687 : Blo 1266451 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B4280957 : Blo 1266451 4280957 := bstep (se 3 (by rfl) ⟨802679, by rfl⟩ : syracuseStep 4280957 = 1605359) B1605359
theorem B1268031 : Blo 1266451 1268031 := bstep (se 1 (by rfl) ⟨951023, by rfl⟩ : syracuseStep 1268031 = 1902047) B1902047
theorem B2407295 : Blo 1266451 2407295 := bstep (se 1 (by rfl) ⟨1805471, by rfl⟩ : syracuseStep 2407295 = 3610943) B3610943
theorem B2138015 : Blo 1266451 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B6416009 : Blo 1266451 6416009 := bstep (se 2 (by rfl) ⟨2406003, by rfl⟩ : syracuseStep 6416009 = 4812007) B4812007
theorem B1902503 : Blo 1266451 1902503 := bstep (se 1 (by rfl) ⟨1426877, by rfl⟩ : syracuseStep 1902503 = 2853755) B2853755
theorem B2853971 : Blo 1266451 2853971 := bstep (se 1 (by rfl) ⟨2140478, by rfl⟩ : syracuseStep 2853971 = 4280957) B4280957
theorem B4812797 : Blo 1266451 4812797 := bstep (se 3 (by rfl) ⟨902399, by rfl⟩ : syracuseStep 4812797 = 1804799) B1804799
theorem B1267047 : Blo 1266451 1267047 := bstep (se 1 (by rfl) ⟨950285, by rfl⟩ : syracuseStep 1267047 = 1900571) B1900571
theorem B2405791 : Blo 1266451 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B1604863 : Blo 1266451 1604863 := bstep (se 1 (by rfl) ⟨1203647, by rfl⟩ : syracuseStep 1604863 = 2407295) B2407295
theorem B1425343 : Blo 1266451 1425343 := bstep (se 1 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 1425343 = 2138015) B2138015
theorem B4277339 : Blo 1266451 4277339 := bstep (se 1 (by rfl) ⟨3208004, by rfl⟩ : syracuseStep 4277339 = 6416009) B6416009
theorem B2139817 : Blo 1266451 2139817 := bstep (se 2 (by rfl) ⟨802431, by rfl⟩ : syracuseStep 2139817 = 1604863) B1604863
theorem B1902647 : Blo 1266451 1902647 := bstep (se 1 (by rfl) ⟨1426985, by rfl⟩ : syracuseStep 1902647 = 2853971) B2853971
theorem B3207721 : Blo 1266451 3207721 := bstep (se 2 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 3207721 = 2405791) B2405791
theorem B3208531 : Blo 1266451 3208531 := bstep (se 1 (by rfl) ⟨2406398, by rfl⟩ : syracuseStep 3208531 = 4812797) B4812797
theorem B1268335 : Blo 1266451 1268335 := bstep (se 1 (by rfl) ⟨951251, by rfl⟩ : syracuseStep 1268335 = 1902503) B1902503
theorem B1900457 : Blo 1266451 1900457 := bstep (se 2 (by rfl) ⟨712671, by rfl⟩ : syracuseStep 1900457 = 1425343) B1425343
theorem B4276961 : Blo 1266451 4276961 := bstep (se 2 (by rfl) ⟨1603860, by rfl⟩ : syracuseStep 4276961 = 3207721) B3207721
theorem B2851559 : Blo 1266451 2851559 := bstep (se 1 (by rfl) ⟨2138669, by rfl⟩ : syracuseStep 2851559 = 4277339) B4277339
theorem B4278041 : Blo 1266451 4278041 := bstep (se 2 (by rfl) ⟨1604265, by rfl⟩ : syracuseStep 4278041 = 3208531) B3208531
theorem B2853089 : Blo 1266451 2853089 := bstep (se 2 (by rfl) ⟨1069908, by rfl⟩ : syracuseStep 2853089 = 2139817) B2139817
theorem B1266971 : Blo 1266451 1266971 := bstep (se 1 (by rfl) ⟨950228, by rfl⟩ : syracuseStep 1266971 = 1900457) B1900457
theorem B1268431 : Blo 1266451 1268431 := bstep (se 1 (by rfl) ⟨951323, by rfl⟩ : syracuseStep 1268431 = 1902647) B1902647
theorem B2851307 : Blo 1266451 2851307 := bstep (se 1 (by rfl) ⟨2138480, by rfl⟩ : syracuseStep 2851307 = 4276961) B4276961
theorem B1901039 : Blo 1266451 1901039 := bstep (se 1 (by rfl) ⟨1425779, by rfl⟩ : syracuseStep 1901039 = 2851559) B2851559
theorem B2852027 : Blo 1266451 2852027 := bstep (se 1 (by rfl) ⟨2139020, by rfl⟩ : syracuseStep 2852027 = 4278041) B4278041
theorem B1902059 : Blo 1266451 1902059 := bstep (se 1 (by rfl) ⟨1426544, by rfl⟩ : syracuseStep 1902059 = 2853089) B2853089
theorem B1900871 : Blo 1266451 1900871 := bstep (se 1 (by rfl) ⟨1425653, by rfl⟩ : syracuseStep 1900871 = 2851307) B2851307
theorem B1901351 : Blo 1266451 1901351 := bstep (se 1 (by rfl) ⟨1426013, by rfl⟩ : syracuseStep 1901351 = 2852027) B2852027
theorem B1267359 : Blo 1266451 1267359 := bstep (se 1 (by rfl) ⟨950519, by rfl⟩ : syracuseStep 1267359 = 1901039) B1901039
theorem B1268039 : Blo 1266451 1268039 := bstep (se 1 (by rfl) ⟨951029, by rfl⟩ : syracuseStep 1268039 = 1902059) B1902059
theorem B1267247 : Blo 1266451 1267247 := bstep (se 1 (by rfl) ⟨950435, by rfl⟩ : syracuseStep 1267247 = 1900871) B1900871
theorem B1267567 : Blo 1266451 1267567 := bstep (se 1 (by rfl) ⟨950675, by rfl⟩ : syracuseStep 1267567 = 1901351) B1901351

theorem C0 (j : ℕ) (h1 : 316612 ≤ j) (h2 : j ≤ 317112) : Blo 1266451 (4 * j + 3) := by
  interval_cases j
  · exact B1266451
  · exact B1266455
  · exact B1266459
  · exact B1266463
  · exact B1266467
  · exact B1266471
  · exact B1266475
  · exact B1266479
  · exact B1266483
  · exact B1266487
  · exact B1266491
  · exact B1266495
  · exact B1266499
  · exact B1266503
  · exact B1266507
  · exact B1266511
  · exact B1266515
  · exact B1266519
  · exact B1266523
  · exact B1266527
  · exact B1266531
  · exact B1266535
  · exact B1266539
  · exact B1266543
  · exact B1266547
  · exact B1266551
  · exact B1266555
  · exact B1266559
  · exact B1266563
  · exact B1266567
  · exact B1266571
  · exact B1266575
  · exact B1266579
  · exact B1266583
  · exact B1266587
  · exact B1266591
  · exact B1266595
  · exact B1266599
  · exact B1266603
  · exact B1266607
  · exact B1266611
  · exact B1266615
  · exact B1266619
  · exact B1266623
  · exact B1266627
  · exact B1266631
  · exact B1266635
  · exact B1266639
  · exact B1266643
  · exact B1266647
  · exact B1266651
  · exact B1266655
  · exact B1266659
  · exact B1266663
  · exact B1266667
  · exact B1266671
  · exact B1266675
  · exact B1266679
  · exact B1266683
  · exact B1266687
  · exact B1266691
  · exact B1266695
  · exact B1266699
  · exact B1266703
  · exact B1266707
  · exact B1266711
  · exact B1266715
  · exact B1266719
  · exact B1266723
  · exact B1266727
  · exact B1266731
  · exact B1266735
  · exact B1266739
  · exact B1266743
  · exact B1266747
  · exact B1266751
  · exact B1266755
  · exact B1266759
  · exact B1266763
  · exact B1266767
  · exact B1266771
  · exact B1266775
  · exact B1266779
  · exact B1266783
  · exact B1266787
  · exact B1266791
  · exact B1266795
  · exact B1266799
  · exact B1266803
  · exact B1266807
  · exact B1266811
  · exact B1266815
  · exact B1266819
  · exact B1266823
  · exact B1266827
  · exact B1266831
  · exact B1266835
  · exact B1266839
  · exact B1266843
  · exact B1266847
  · exact B1266851
  · exact B1266855
  · exact B1266859
  · exact B1266863
  · exact B1266867
  · exact B1266871
  · exact B1266875
  · exact B1266879
  · exact B1266883
  · exact B1266887
  · exact B1266891
  · exact B1266895
  · exact B1266899
  · exact B1266903
  · exact B1266907
  · exact B1266911
  · exact B1266915
  · exact B1266919
  · exact B1266923
  · exact B1266927
  · exact B1266931
  · exact B1266935
  · exact B1266939
  · exact B1266943
  · exact B1266947
  · exact B1266951
  · exact B1266955
  · exact B1266959
  · exact B1266963
  · exact B1266967
  · exact B1266971
  · exact B1266975
  · exact B1266979
  · exact B1266983
  · exact B1266987
  · exact B1266991
  · exact B1266995
  · exact B1266999
  · exact B1267003
  · exact B1267007
  · exact B1267011
  · exact B1267015
  · exact B1267019
  · exact B1267023
  · exact B1267027
  · exact B1267031
  · exact B1267035
  · exact B1267039
  · exact B1267043
  · exact B1267047
  · exact B1267051
  · exact B1267055
  · exact B1267059
  · exact B1267063
  · exact B1267067
  · exact B1267071
  · exact B1267075
  · exact B1267079
  · exact B1267083
  · exact B1267087
  · exact B1267091
  · exact B1267095
  · exact B1267099
  · exact B1267103
  · exact B1267107
  · exact B1267111
  · exact B1267115
  · exact B1267119
  · exact B1267123
  · exact B1267127
  · exact B1267131
  · exact B1267135
  · exact B1267139
  · exact B1267143
  · exact B1267147
  · exact B1267151
  · exact B1267155
  · exact B1267159
  · exact B1267163
  · exact B1267167
  · exact B1267171
  · exact B1267175
  · exact B1267179
  · exact B1267183
  · exact B1267187
  · exact B1267191
  · exact B1267195
  · exact B1267199
  · exact B1267203
  · exact B1267207
  · exact B1267211
  · exact B1267215
  · exact B1267219
  · exact B1267223
  · exact B1267227
  · exact B1267231
  · exact B1267235
  · exact B1267239
  · exact B1267243
  · exact B1267247
  · exact B1267251
  · exact B1267255
  · exact B1267259
  · exact B1267263
  · exact B1267267
  · exact B1267271
  · exact B1267275
  · exact B1267279
  · exact B1267283
  · exact B1267287
  · exact B1267291
  · exact B1267295
  · exact B1267299
  · exact B1267303
  · exact B1267307
  · exact B1267311
  · exact B1267315
  · exact B1267319
  · exact B1267323
  · exact B1267327
  · exact B1267331
  · exact B1267335
  · exact B1267339
  · exact B1267343
  · exact B1267347
  · exact B1267351
  · exact B1267355
  · exact B1267359
  · exact B1267363
  · exact B1267367
  · exact B1267371
  · exact B1267375
  · exact B1267379
  · exact B1267383
  · exact B1267387
  · exact B1267391
  · exact B1267395
  · exact B1267399
  · exact B1267403
  · exact B1267407
  · exact B1267411
  · exact B1267415
  · exact B1267419
  · exact B1267423
  · exact B1267427
  · exact B1267431
  · exact B1267435
  · exact B1267439
  · exact B1267443
  · exact B1267447
  · exact B1267451
  · exact B1267455
  · exact B1267459
  · exact B1267463
  · exact B1267467
  · exact B1267471
  · exact B1267475
  · exact B1267479
  · exact B1267483
  · exact B1267487
  · exact B1267491
  · exact B1267495
  · exact B1267499
  · exact B1267503
  · exact B1267507
  · exact B1267511
  · exact B1267515
  · exact B1267519
  · exact B1267523
  · exact B1267527
  · exact B1267531
  · exact B1267535
  · exact B1267539
  · exact B1267543
  · exact B1267547
  · exact B1267551
  · exact B1267555
  · exact B1267559
  · exact B1267563
  · exact B1267567
  · exact B1267571
  · exact B1267575
  · exact B1267579
  · exact B1267583
  · exact B1267587
  · exact B1267591
  · exact B1267595
  · exact B1267599
  · exact B1267603
  · exact B1267607
  · exact B1267611
  · exact B1267615
  · exact B1267619
  · exact B1267623
  · exact B1267627
  · exact B1267631
  · exact B1267635
  · exact B1267639
  · exact B1267643
  · exact B1267647
  · exact B1267651
  · exact B1267655
  · exact B1267659
  · exact B1267663
  · exact B1267667
  · exact B1267671
  · exact B1267675
  · exact B1267679
  · exact B1267683
  · exact B1267687
  · exact B1267691
  · exact B1267695
  · exact B1267699
  · exact B1267703
  · exact B1267707
  · exact B1267711
  · exact B1267715
  · exact B1267719
  · exact B1267723
  · exact B1267727
  · exact B1267731
  · exact B1267735
  · exact B1267739
  · exact B1267743
  · exact B1267747
  · exact B1267751
  · exact B1267755
  · exact B1267759
  · exact B1267763
  · exact B1267767
  · exact B1267771
  · exact B1267775
  · exact B1267779
  · exact B1267783
  · exact B1267787
  · exact B1267791
  · exact B1267795
  · exact B1267799
  · exact B1267803
  · exact B1267807
  · exact B1267811
  · exact B1267815
  · exact B1267819
  · exact B1267823
  · exact B1267827
  · exact B1267831
  · exact B1267835
  · exact B1267839
  · exact B1267843
  · exact B1267847
  · exact B1267851
  · exact B1267855
  · exact B1267859
  · exact B1267863
  · exact B1267867
  · exact B1267871
  · exact B1267875
  · exact B1267879
  · exact B1267883
  · exact B1267887
  · exact B1267891
  · exact B1267895
  · exact B1267899
  · exact B1267903
  · exact B1267907
  · exact B1267911
  · exact B1267915
  · exact B1267919
  · exact B1267923
  · exact B1267927
  · exact B1267931
  · exact B1267935
  · exact B1267939
  · exact B1267943
  · exact B1267947
  · exact B1267951
  · exact B1267955
  · exact B1267959
  · exact B1267963
  · exact B1267967
  · exact B1267971
  · exact B1267975
  · exact B1267979
  · exact B1267983
  · exact B1267987
  · exact B1267991
  · exact B1267995
  · exact B1267999
  · exact B1268003
  · exact B1268007
  · exact B1268011
  · exact B1268015
  · exact B1268019
  · exact B1268023
  · exact B1268027
  · exact B1268031
  · exact B1268035
  · exact B1268039
  · exact B1268043
  · exact B1268047
  · exact B1268051
  · exact B1268055
  · exact B1268059
  · exact B1268063
  · exact B1268067
  · exact B1268071
  · exact B1268075
  · exact B1268079
  · exact B1268083
  · exact B1268087
  · exact B1268091
  · exact B1268095
  · exact B1268099
  · exact B1268103
  · exact B1268107
  · exact B1268111
  · exact B1268115
  · exact B1268119
  · exact B1268123
  · exact B1268127
  · exact B1268131
  · exact B1268135
  · exact B1268139
  · exact B1268143
  · exact B1268147
  · exact B1268151
  · exact B1268155
  · exact B1268159
  · exact B1268163
  · exact B1268167
  · exact B1268171
  · exact B1268175
  · exact B1268179
  · exact B1268183
  · exact B1268187
  · exact B1268191
  · exact B1268195
  · exact B1268199
  · exact B1268203
  · exact B1268207
  · exact B1268211
  · exact B1268215
  · exact B1268219
  · exact B1268223
  · exact B1268227
  · exact B1268231
  · exact B1268235
  · exact B1268239
  · exact B1268243
  · exact B1268247
  · exact B1268251
  · exact B1268255
  · exact B1268259
  · exact B1268263
  · exact B1268267
  · exact B1268271
  · exact B1268275
  · exact B1268279
  · exact B1268283
  · exact B1268287
  · exact B1268291
  · exact B1268295
  · exact B1268299
  · exact B1268303
  · exact B1268307
  · exact B1268311
  · exact B1268315
  · exact B1268319
  · exact B1268323
  · exact B1268327
  · exact B1268331
  · exact B1268335
  · exact B1268339
  · exact B1268343
  · exact B1268347
  · exact B1268351
  · exact B1268355
  · exact B1268359
  · exact B1268363
  · exact B1268367
  · exact B1268371
  · exact B1268375
  · exact B1268379
  · exact B1268383
  · exact B1268387
  · exact B1268391
  · exact B1268395
  · exact B1268399
  · exact B1268403
  · exact B1268407
  · exact B1268411
  · exact B1268415
  · exact B1268419
  · exact B1268423
  · exact B1268427
  · exact B1268431
  · exact B1268435
  · exact B1268439
  · exact B1268443
  · exact B1268447
  · exact B1268451

theorem solution (m : ℕ) (hlo : 1266451 ≤ m) (hhi : m ≤ 1268451) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 316612 ≤ j := by omega
    have hj2 : j ≤ 317112 := by omega
    have hb : Blo 1266451 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
