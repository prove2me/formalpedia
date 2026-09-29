-- Prove2me | solution 1 for syracuse_descends_range_366759_370759
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:39.966732+00:00
-- url     : https://prove2.me/submissions/301841eb-837a-43ad-be9c-c538a7ced0d7

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


theorem B589837 : Blo 366759 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B393233 : Blo 366759 393233 := bbase (se 2 (by rfl) ⟨147462, by rfl⟩ : syracuseStep 393233 = 294925) (by norm_num)
theorem B622613 : Blo 366759 622613 := bbase (se 6 (by rfl) ⟨14592, by rfl⟩ : syracuseStep 622613 = 29185) (by norm_num)
theorem B393293 : Blo 366759 393293 := bbase (se 3 (by rfl) ⟨73742, by rfl⟩ : syracuseStep 393293 = 147485) (by norm_num)
theorem B622741 : Blo 366759 622741 := bbase (se 6 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 622741 = 29191) (by norm_num)
theorem B393421 : Blo 366759 393421 := bbase (se 3 (by rfl) ⟨73766, by rfl⟩ : syracuseStep 393421 = 147533) (by norm_num)
theorem B622829 : Blo 366759 622829 := bbase (se 3 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 622829 = 233561) (by norm_num)
theorem B1868021 : Blo 366759 1868021 := bbase (se 5 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 1868021 = 175127) (by norm_num)
theorem B1245509 : Blo 366759 1245509 := bbase (se 4 (by rfl) ⟨116766, by rfl⟩ : syracuseStep 1245509 = 233533) (by norm_num)
theorem B622957 : Blo 366759 622957 := bbase (se 3 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 622957 = 233609) (by norm_num)
theorem B950717 : Blo 366759 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B623045 : Blo 366759 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B590285 : Blo 366759 590285 := bbase (se 3 (by rfl) ⟨110678, by rfl⟩ : syracuseStep 590285 = 221357) (by norm_num)
theorem B10584533 : Blo 366759 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B5374421 : Blo 366759 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B1573445 : Blo 366759 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B787013 : Blo 366759 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B623173 : Blo 366759 623173 := bbase (se 4 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 623173 = 116845) (by norm_num)
theorem B950885 : Blo 366759 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B393865 : Blo 366759 393865 := bbase (se 2 (by rfl) ⟨147699, by rfl⟩ : syracuseStep 393865 = 295399) (by norm_num)
theorem B1049237 : Blo 366759 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B590485 : Blo 366759 590485 := bbase (se 6 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 590485 = 27679) (by norm_num)
theorem B623261 : Blo 366759 623261 := bbase (se 3 (by rfl) ⟨116861, by rfl⟩ : syracuseStep 623261 = 233723) (by norm_num)
theorem B787133 : Blo 366759 787133 := bbase (se 3 (by rfl) ⟨147587, by rfl⟩ : syracuseStep 787133 = 295175) (by norm_num)
theorem B1245941 : Blo 366759 1245941 := bbase (se 5 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 1245941 = 116807) (by norm_num)
theorem B393985 : Blo 366759 393985 := bbase (se 2 (by rfl) ⟨147744, by rfl⟩ : syracuseStep 393985 = 295489) (by norm_num)
theorem B623389 : Blo 366759 623389 := bbase (se 3 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 623389 = 233771) (by norm_num)
theorem B623477 : Blo 366759 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B590741 : Blo 366759 590741 := bbase (se 6 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 590741 = 27691) (by norm_num)
theorem B623605 : Blo 366759 623605 := bbase (se 5 (by rfl) ⟨29231, by rfl⟩ : syracuseStep 623605 = 58463) (by norm_num)
theorem B394237 : Blo 366759 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B394241 : Blo 366759 394241 := bbase (se 2 (by rfl) ⟨147840, by rfl⟩ : syracuseStep 394241 = 295681) (by norm_num)
theorem B1049669 : Blo 366759 1049669 := bbase (se 4 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 1049669 = 196813) (by norm_num)
theorem B623693 : Blo 366759 623693 := bbase (se 3 (by rfl) ⟨116942, by rfl⟩ : syracuseStep 623693 = 233885) (by norm_num)
theorem B1246373 : Blo 366759 1246373 := bbase (se 4 (by rfl) ⟨116847, by rfl⟩ : syracuseStep 1246373 = 233695) (by norm_num)
theorem B623821 : Blo 366759 623821 := bbase (se 3 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 623821 = 233933) (by norm_num)
theorem B525541 : Blo 366759 525541 := bbase (se 4 (by rfl) ⟨49269, by rfl⟩ : syracuseStep 525541 = 98539) (by norm_num)
theorem B623909 : Blo 366759 623909 := bbase (se 4 (by rfl) ⟨58491, by rfl⟩ : syracuseStep 623909 = 116983) (by norm_num)
theorem B787765 : Blo 366759 787765 := bbase (se 5 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 787765 = 73853) (by norm_num)
theorem B624037 : Blo 366759 624037 := bbase (se 4 (by rfl) ⟨58503, by rfl⟩ : syracuseStep 624037 = 117007) (by norm_num)
theorem B624125 : Blo 366759 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B1869317 : Blo 366759 1869317 := bbase (se 4 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 1869317 = 350497) (by norm_num)
theorem B394805 : Blo 366759 394805 := bbase (se 5 (by rfl) ⟨18506, by rfl⟩ : syracuseStep 394805 = 37013) (by norm_num)
theorem B1246805 : Blo 366759 1246805 := bbase (se 8 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 1246805 = 14611) (by norm_num)
theorem B624253 : Blo 366759 624253 := bbase (se 3 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 624253 = 234095) (by norm_num)
theorem B624341 : Blo 366759 624341 := bbase (se 7 (by rfl) ⟨7316, by rfl⟩ : syracuseStep 624341 = 14633) (by norm_num)
theorem B394993 : Blo 366759 394993 := bbase (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) (by norm_num)
theorem B1050421 : Blo 366759 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B526133 : Blo 366759 526133 := bbase (se 5 (by rfl) ⟨24662, by rfl⟩ : syracuseStep 526133 = 49325) (by norm_num)
theorem B624469 : Blo 366759 624469 := bbase (se 9 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 624469 = 3659) (by norm_num)
theorem B526213 : Blo 366759 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B624557 : Blo 366759 624557 := bbase (se 3 (by rfl) ⟨117104, by rfl⟩ : syracuseStep 624557 = 234209) (by norm_num)
theorem B591869 : Blo 366759 591869 := bbase (se 3 (by rfl) ⟨110975, by rfl⟩ : syracuseStep 591869 = 221951) (by norm_num)
theorem B526333 : Blo 366759 526333 := bbase (se 3 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 526333 = 197375) (by norm_num)
theorem B1247237 : Blo 366759 1247237 := bbase (se 4 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 1247237 = 233857) (by norm_num)
theorem B624685 : Blo 366759 624685 := bbase (se 3 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 624685 = 234257) (by norm_num)
theorem B526429 : Blo 366759 526429 := bbase (se 3 (by rfl) ⟨98705, by rfl⟩ : syracuseStep 526429 = 197411) (by norm_num)
theorem B886909 : Blo 366759 886909 := bbase (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) (by norm_num)
theorem B624773 : Blo 366759 624773 := bbase (se 4 (by rfl) ⟨58572, by rfl⟩ : syracuseStep 624773 = 117145) (by norm_num)
theorem B788653 : Blo 366759 788653 := bbase (se 3 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 788653 = 295745) (by norm_num)
theorem B821485 : Blo 366759 821485 := bbase (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) (by norm_num)
theorem B624901 : Blo 366759 624901 := bbase (se 4 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 624901 = 117169) (by norm_num)
theorem B559381 : Blo 366759 559381 := bbase (se 6 (by rfl) ⟨13110, by rfl⟩ : syracuseStep 559381 = 26221) (by norm_num)
theorem B788773 : Blo 366759 788773 := bbase (se 4 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 788773 = 147895) (by norm_num)
theorem B624989 : Blo 366759 624989 := bbase (se 3 (by rfl) ⟨117185, by rfl⟩ : syracuseStep 624989 = 234371) (by norm_num)
theorem B1247669 : Blo 366759 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B625117 : Blo 366759 625117 := bbase (se 3 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 625117 = 234419) (by norm_num)
theorem B592381 : Blo 366759 592381 := bbase (se 3 (by rfl) ⟨111071, by rfl⟩ : syracuseStep 592381 = 222143) (by norm_num)
theorem B789029 : Blo 366759 789029 := bbase (se 4 (by rfl) ⟨73971, by rfl⟩ : syracuseStep 789029 = 147943) (by norm_num)
theorem B395813 : Blo 366759 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B625205 : Blo 366759 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B526925 : Blo 366759 526925 := bbase (se 3 (by rfl) ⟨98798, by rfl⟩ : syracuseStep 526925 = 197597) (by norm_num)
theorem B625333 : Blo 366759 625333 := bbase (se 5 (by rfl) ⟨29312, by rfl⟩ : syracuseStep 625333 = 58625) (by norm_num)
theorem B625421 : Blo 366759 625421 := bbase (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) (by norm_num)
theorem B887573 : Blo 366759 887573 := bbase (se 6 (by rfl) ⟨20802, by rfl⟩ : syracuseStep 887573 = 41605) (by norm_num)
theorem B1870613 : Blo 366759 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B2788181 : Blo 366759 2788181 := bbase (se 9 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 2788181 = 16337) (by norm_num)
theorem B1248101 : Blo 366759 1248101 := bbase (se 4 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 1248101 = 234019) (by norm_num)
theorem B625549 : Blo 366759 625549 := bbase (se 3 (by rfl) ⟨117290, by rfl⟩ : syracuseStep 625549 = 234581) (by norm_num)
theorem B625637 : Blo 366759 625637 := bbase (se 4 (by rfl) ⟨58653, by rfl⟩ : syracuseStep 625637 = 117307) (by norm_num)
theorem B1772549 : Blo 366759 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B592925 : Blo 366759 592925 := bbase (se 3 (by rfl) ⟨111173, by rfl⟩ : syracuseStep 592925 = 222347) (by norm_num)
theorem B527477 : Blo 366759 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B1182917 : Blo 366759 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B1248533 : Blo 366759 1248533 := bbase (se 6 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 1248533 = 58525) (by norm_num)
theorem B1772837 : Blo 366759 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B789917 : Blo 366759 789917 := bbase (se 3 (by rfl) ⟨148109, by rfl⟩ : syracuseStep 789917 = 296219) (by norm_num)
theorem B593477 : Blo 366759 593477 := bbase (se 4 (by rfl) ⟨55638, by rfl⟩ : syracuseStep 593477 = 111277) (by norm_num)
theorem B593509 : Blo 366759 593509 := bbase (se 4 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 593509 = 111283) (by norm_num)
theorem B790157 : Blo 366759 790157 := bbase (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) (by norm_num)
theorem B757405 : Blo 366759 757405 := bbase (se 3 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 757405 = 284027) (by norm_num)
theorem B1248965 : Blo 366759 1248965 := bbase (se 4 (by rfl) ⟨117090, by rfl⟩ : syracuseStep 1248965 = 234181) (by norm_num)
theorem B1347317 : Blo 366759 1347317 := bbase (se 5 (by rfl) ⟨63155, by rfl⟩ : syracuseStep 1347317 = 126311) (by norm_num)
theorem B15109973 : Blo 366759 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B561053 : Blo 366759 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B1871909 : Blo 366759 1871909 := bbase (se 4 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 1871909 = 350983) (by norm_num)
theorem B1249397 : Blo 366759 1249397 := bbase (se 5 (by rfl) ⟨58565, by rfl⟩ : syracuseStep 1249397 = 117131) (by norm_num)
theorem B888965 : Blo 366759 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B790661 : Blo 366759 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B790669 : Blo 366759 790669 := bbase (se 3 (by rfl) ⟨148250, by rfl⟩ : syracuseStep 790669 = 296501) (by norm_num)
theorem B889061 : Blo 366759 889061 := bbase (se 4 (by rfl) ⟨83349, by rfl⟩ : syracuseStep 889061 = 166699) (by norm_num)
theorem B2265365 : Blo 366759 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B2003285 : Blo 366759 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B1249829 : Blo 366759 1249829 := bbase (se 4 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 1249829 = 234343) (by norm_num)
theorem B1053269 : Blo 366759 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B1577717 : Blo 366759 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B561917 : Blo 366759 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B1250261 : Blo 366759 1250261 := bbase (se 7 (by rfl) ⟨14651, by rfl⟩ : syracuseStep 1250261 = 29303) (by norm_num)
theorem B791797 : Blo 366759 791797 := bbase (se 5 (by rfl) ⟨37115, by rfl⟩ : syracuseStep 791797 = 74231) (by norm_num)
theorem B1873205 : Blo 366759 1873205 := bbase (se 5 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 1873205 = 175613) (by norm_num)
theorem B464221 : Blo 366759 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B1250693 : Blo 366759 1250693 := bbase (se 4 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 1250693 = 234505) (by norm_num)
theorem B464393 : Blo 366759 464393 := bbase (se 2 (by rfl) ⟨174147, by rfl⟩ : syracuseStep 464393 = 348295) (by norm_num)
theorem B464449 : Blo 366759 464449 := bbase (se 2 (by rfl) ⟨174168, by rfl⟩ : syracuseStep 464449 = 348337) (by norm_num)
theorem B464545 : Blo 366759 464545 := bbase (se 2 (by rfl) ⟨174204, by rfl⟩ : syracuseStep 464545 = 348409) (by norm_num)
theorem B2103029 : Blo 366759 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B1054453 : Blo 366759 1054453 := bbase (se 5 (by rfl) ⟨49427, by rfl⟩ : syracuseStep 1054453 = 98855) (by norm_num)
theorem B1251125 : Blo 366759 1251125 := bbase (se 5 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 1251125 = 117293) (by norm_num)
theorem B431929 : Blo 366759 431929 := bbase (se 2 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 431929 = 323947) (by norm_num)
theorem B464717 : Blo 366759 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B464773 : Blo 366759 464773 := bbase (se 4 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 464773 = 87145) (by norm_num)
theorem B1054613 : Blo 366759 1054613 := bbase (se 6 (by rfl) ⟨24717, by rfl⟩ : syracuseStep 1054613 = 49435) (by norm_num)
theorem B825245 : Blo 366759 825245 := bbase (se 3 (by rfl) ⟨154733, by rfl⟩ : syracuseStep 825245 = 309467) (by norm_num)
theorem B759709 : Blo 366759 759709 := bbase (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) (by norm_num)
theorem B1185749 : Blo 366759 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B825317 : Blo 366759 825317 := bbase (se 4 (by rfl) ⟨77373, by rfl⟩ : syracuseStep 825317 = 154747) (by norm_num)
theorem B464869 : Blo 366759 464869 := bbase (se 4 (by rfl) ⟨43581, by rfl⟩ : syracuseStep 464869 = 87163) (by norm_num)
theorem B595949 : Blo 366759 595949 := bbase (se 3 (by rfl) ⟨111740, by rfl⟩ : syracuseStep 595949 = 223481) (by norm_num)
theorem B825389 : Blo 366759 825389 := bbase (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) (by norm_num)
theorem B825461 : Blo 366759 825461 := bbase (se 5 (by rfl) ⟨38693, by rfl⟩ : syracuseStep 825461 = 77387) (by norm_num)
theorem B661621 : Blo 366759 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B1054853 : Blo 366759 1054853 := bbase (se 4 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 1054853 = 197785) (by norm_num)
theorem B465041 : Blo 366759 465041 := bbase (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) (by norm_num)
theorem B825533 : Blo 366759 825533 := bbase (se 3 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 825533 = 309575) (by norm_num)
theorem B465097 : Blo 366759 465097 := bbase (se 2 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 465097 = 348823) (by norm_num)
theorem B825605 : Blo 366759 825605 := bbase (se 4 (by rfl) ⟨77400, by rfl⟩ : syracuseStep 825605 = 154801) (by norm_num)
theorem B465193 : Blo 366759 465193 := bbase (se 2 (by rfl) ⟨174447, by rfl⟩ : syracuseStep 465193 = 348895) (by norm_num)
theorem B530749 : Blo 366759 530749 := bbase (se 3 (by rfl) ⟨99515, by rfl⟩ : syracuseStep 530749 = 199031) (by norm_num)
theorem B1055045 : Blo 366759 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B825677 : Blo 366759 825677 := bbase (se 3 (by rfl) ⟨154814, by rfl⟩ : syracuseStep 825677 = 309629) (by norm_num)
theorem B825749 : Blo 366759 825749 := bbase (se 6 (by rfl) ⟨19353, by rfl⟩ : syracuseStep 825749 = 38707) (by norm_num)
theorem B465365 : Blo 366759 465365 := bbase (se 7 (by rfl) ⟨5453, by rfl⟩ : syracuseStep 465365 = 10907) (by norm_num)
theorem B825821 : Blo 366759 825821 := bbase (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) (by norm_num)
theorem B1579493 : Blo 366759 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B465421 : Blo 366759 465421 := bbase (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) (by norm_num)
theorem B825893 : Blo 366759 825893 := bbase (se 4 (by rfl) ⟨77427, by rfl⟩ : syracuseStep 825893 = 154855) (by norm_num)
theorem B1874501 : Blo 366759 1874501 := bbase (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) (by norm_num)
theorem B825965 : Blo 366759 825965 := bbase (se 3 (by rfl) ⟨154868, by rfl⟩ : syracuseStep 825965 = 309737) (by norm_num)
theorem B465517 : Blo 366759 465517 := bbase (se 3 (by rfl) ⟨87284, by rfl⟩ : syracuseStep 465517 = 174569) (by norm_num)
theorem B498325 : Blo 366759 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B826037 : Blo 366759 826037 := bbase (se 5 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 826037 = 77441) (by norm_num)
theorem B11901653 : Blo 366759 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B1579733 : Blo 366759 1579733 := bbase (se 7 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 1579733 = 37025) (by norm_num)
theorem B826109 : Blo 366759 826109 := bbase (se 3 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 826109 = 309791) (by norm_num)
theorem B465689 : Blo 366759 465689 := bbase (se 2 (by rfl) ⟨174633, by rfl⟩ : syracuseStep 465689 = 349267) (by norm_num)
theorem B826181 : Blo 366759 826181 := bbase (se 4 (by rfl) ⟨77454, by rfl⟩ : syracuseStep 826181 = 154909) (by norm_num)
theorem B662341 : Blo 366759 662341 := bbase (se 4 (by rfl) ⟨62094, by rfl⟩ : syracuseStep 662341 = 124189) (by norm_num)
theorem B465745 : Blo 366759 465745 := bbase (se 2 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 465745 = 349309) (by norm_num)
theorem B1186645 : Blo 366759 1186645 := bbase (se 9 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 1186645 = 6953) (by norm_num)
theorem B826253 : Blo 366759 826253 := bbase (se 3 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 826253 = 309845) (by norm_num)
theorem B465841 : Blo 366759 465841 := bbase (se 2 (by rfl) ⟨174690, by rfl⟩ : syracuseStep 465841 = 349381) (by norm_num)
theorem B826325 : Blo 366759 826325 := bbase (se 7 (by rfl) ⟨9683, by rfl⟩ : syracuseStep 826325 = 19367) (by norm_num)
theorem B629741 : Blo 366759 629741 := bbase (se 3 (by rfl) ⟨118076, by rfl⟩ : syracuseStep 629741 = 236153) (by norm_num)
theorem B826397 : Blo 366759 826397 := bbase (se 3 (by rfl) ⟨154949, by rfl⟩ : syracuseStep 826397 = 309899) (by norm_num)
theorem B662573 : Blo 366759 662573 := bbase (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) (by norm_num)
theorem B466013 : Blo 366759 466013 := bbase (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) (by norm_num)
theorem B826469 : Blo 366759 826469 := bbase (se 4 (by rfl) ⟨77481, by rfl⟩ : syracuseStep 826469 = 154963) (by norm_num)
theorem B466069 : Blo 366759 466069 := bbase (se 6 (by rfl) ⟨10923, by rfl⟩ : syracuseStep 466069 = 21847) (by norm_num)
theorem B826541 : Blo 366759 826541 := bbase (se 3 (by rfl) ⟨154976, by rfl⟩ : syracuseStep 826541 = 309953) (by norm_num)
theorem B826613 : Blo 366759 826613 := bbase (se 5 (by rfl) ⟨38747, by rfl⟩ : syracuseStep 826613 = 77495) (by norm_num)
theorem B466165 : Blo 366759 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B826685 : Blo 366759 826685 := bbase (se 3 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 826685 = 310007) (by norm_num)
theorem B826757 : Blo 366759 826757 := bbase (se 4 (by rfl) ⟨77508, by rfl⟩ : syracuseStep 826757 = 155017) (by norm_num)
theorem B466337 : Blo 366759 466337 := bbase (se 2 (by rfl) ⟨174876, by rfl⟩ : syracuseStep 466337 = 349753) (by norm_num)
theorem B826829 : Blo 366759 826829 := bbase (se 3 (by rfl) ⟨155030, by rfl⟩ : syracuseStep 826829 = 310061) (by norm_num)
theorem B466393 : Blo 366759 466393 := bbase (se 2 (by rfl) ⟨174897, by rfl⟩ : syracuseStep 466393 = 349795) (by norm_num)
theorem B663005 : Blo 366759 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B826901 : Blo 366759 826901 := bbase (se 6 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 826901 = 38761) (by norm_num)
theorem B466489 : Blo 366759 466489 := bbase (se 2 (by rfl) ⟨174933, by rfl⟩ : syracuseStep 466489 = 349867) (by norm_num)
theorem B826973 : Blo 366759 826973 := bbase (se 3 (by rfl) ⟨155057, by rfl⟩ : syracuseStep 826973 = 310115) (by norm_num)
theorem B663149 : Blo 366759 663149 := bbase (se 3 (by rfl) ⟨124340, by rfl⟩ : syracuseStep 663149 = 248681) (by norm_num)
theorem B827045 : Blo 366759 827045 := bbase (se 4 (by rfl) ⟨77535, by rfl⟩ : syracuseStep 827045 = 155071) (by norm_num)
theorem B466661 : Blo 366759 466661 := bbase (se 4 (by rfl) ⟨43749, by rfl⟩ : syracuseStep 466661 = 87499) (by norm_num)
theorem B827117 : Blo 366759 827117 := bbase (se 3 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 827117 = 310169) (by norm_num)
theorem B466717 : Blo 366759 466717 := bbase (se 3 (by rfl) ⟨87509, by rfl⟩ : syracuseStep 466717 = 175019) (by norm_num)
theorem B827189 : Blo 366759 827189 := bbase (se 5 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 827189 = 77549) (by norm_num)
theorem B1875797 : Blo 366759 1875797 := bbase (se 9 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 1875797 = 10991) (by norm_num)
theorem B827261 : Blo 366759 827261 := bbase (se 3 (by rfl) ⟨155111, by rfl⟩ : syracuseStep 827261 = 310223) (by norm_num)
theorem B466813 : Blo 366759 466813 := bbase (se 3 (by rfl) ⟨87527, by rfl⟩ : syracuseStep 466813 = 175055) (by norm_num)
theorem B663437 : Blo 366759 663437 := bbase (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) (by norm_num)
theorem B827333 : Blo 366759 827333 := bbase (se 4 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 827333 = 155125) (by norm_num)
theorem B1777621 : Blo 366759 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B499709 : Blo 366759 499709 := bbase (se 3 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 499709 = 187391) (by norm_num)
theorem B827405 : Blo 366759 827405 := bbase (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) (by norm_num)
theorem B466985 : Blo 366759 466985 := bbase (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) (by norm_num)
theorem B827477 : Blo 366759 827477 := bbase (se 8 (by rfl) ⟨4848, by rfl⟩ : syracuseStep 827477 = 9697) (by norm_num)
theorem B16162901 : Blo 366759 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B467041 : Blo 366759 467041 := bbase (se 2 (by rfl) ⟨175140, by rfl⟩ : syracuseStep 467041 = 350281) (by norm_num)
theorem B663661 : Blo 366759 663661 := bbase (se 3 (by rfl) ⟨124436, by rfl⟩ : syracuseStep 663661 = 248873) (by norm_num)
theorem B827549 : Blo 366759 827549 := bbase (se 3 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 827549 = 310331) (by norm_num)
theorem B663725 : Blo 366759 663725 := bbase (se 3 (by rfl) ⟨124448, by rfl⟩ : syracuseStep 663725 = 248897) (by norm_num)
theorem B467137 : Blo 366759 467137 := bbase (se 2 (by rfl) ⟨175176, by rfl⟩ : syracuseStep 467137 = 350353) (by norm_num)
theorem B4726997 : Blo 366759 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B2367701 : Blo 366759 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B827621 : Blo 366759 827621 := bbase (se 4 (by rfl) ⟨77589, by rfl⟩ : syracuseStep 827621 = 155179) (by norm_num)
theorem B696613 : Blo 366759 696613 := bbase (se 4 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 696613 = 130615) (by norm_num)
theorem B827693 : Blo 366759 827693 := bbase (se 3 (by rfl) ⟨155192, by rfl⟩ : syracuseStep 827693 = 310385) (by norm_num)
theorem B2662741 : Blo 366759 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B467309 : Blo 366759 467309 := bbase (se 3 (by rfl) ⟨87620, by rfl⟩ : syracuseStep 467309 = 175241) (by norm_num)
theorem B827765 : Blo 366759 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B467365 : Blo 366759 467365 := bbase (se 4 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 467365 = 87631) (by norm_num)
theorem B696757 : Blo 366759 696757 := bbase (se 5 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 696757 = 65321) (by norm_num)
theorem B827837 : Blo 366759 827837 := bbase (se 3 (by rfl) ⟨155219, by rfl⟩ : syracuseStep 827837 = 310439) (by norm_num)
theorem B827909 : Blo 366759 827909 := bbase (se 4 (by rfl) ⟨77616, by rfl⟩ : syracuseStep 827909 = 155233) (by norm_num)
theorem B467461 : Blo 366759 467461 := bbase (se 4 (by rfl) ⟨43824, by rfl⟩ : syracuseStep 467461 = 87649) (by norm_num)
theorem B827981 : Blo 366759 827981 := bbase (se 3 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 827981 = 310493) (by norm_num)
theorem B696917 : Blo 366759 696917 := bbase (se 8 (by rfl) ⟨4083, by rfl⟩ : syracuseStep 696917 = 8167) (by norm_num)
theorem B828053 : Blo 366759 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B467633 : Blo 366759 467633 := bbase (se 2 (by rfl) ⟨175362, by rfl⟩ : syracuseStep 467633 = 350725) (by norm_num)
theorem B828125 : Blo 366759 828125 := bbase (se 3 (by rfl) ⟨155273, by rfl⟩ : syracuseStep 828125 = 310547) (by norm_num)
theorem B959197 : Blo 366759 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B697061 : Blo 366759 697061 := bbase (se 4 (by rfl) ⟨65349, by rfl⟩ : syracuseStep 697061 = 130699) (by norm_num)
theorem B467689 : Blo 366759 467689 := bbase (se 2 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 467689 = 350767) (by norm_num)
theorem B828197 : Blo 366759 828197 := bbase (se 4 (by rfl) ⟨77643, by rfl⟩ : syracuseStep 828197 = 155287) (by norm_num)
theorem B467785 : Blo 366759 467785 := bbase (se 2 (by rfl) ⟨175419, by rfl⟩ : syracuseStep 467785 = 350839) (by norm_num)
theorem B828269 : Blo 366759 828269 := bbase (se 3 (by rfl) ⟨155300, by rfl⟩ : syracuseStep 828269 = 310601) (by norm_num)
theorem B4203413 : Blo 366759 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B828341 : Blo 366759 828341 := bbase (se 5 (by rfl) ⟨38828, by rfl⟩ : syracuseStep 828341 = 77657) (by norm_num)
theorem B1582021 : Blo 366759 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B467957 : Blo 366759 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B828413 : Blo 366759 828413 := bbase (se 3 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 828413 = 310655) (by norm_num)
theorem B697349 : Blo 366759 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B468013 : Blo 366759 468013 := bbase (se 3 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 468013 = 175505) (by norm_num)
theorem B894005 : Blo 366759 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B828485 : Blo 366759 828485 := bbase (se 4 (by rfl) ⟨77670, by rfl⟩ : syracuseStep 828485 = 155341) (by norm_num)
theorem B828557 : Blo 366759 828557 := bbase (se 3 (by rfl) ⟨155354, by rfl⟩ : syracuseStep 828557 = 310709) (by norm_num)
theorem B468109 : Blo 366759 468109 := bbase (se 3 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 468109 = 175541) (by norm_num)
theorem B697501 : Blo 366759 697501 := bbase (se 3 (by rfl) ⟨130781, by rfl⟩ : syracuseStep 697501 = 261563) (by norm_num)
theorem B828629 : Blo 366759 828629 := bbase (se 7 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 828629 = 19421) (by norm_num)
theorem B1123541 : Blo 366759 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B828701 : Blo 366759 828701 := bbase (se 3 (by rfl) ⟨155381, by rfl⟩ : syracuseStep 828701 = 310763) (by norm_num)
theorem B468281 : Blo 366759 468281 := bbase (se 2 (by rfl) ⟨175605, by rfl⟩ : syracuseStep 468281 = 351211) (by norm_num)
theorem B828773 : Blo 366759 828773 := bbase (se 4 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 828773 = 155395) (by norm_num)
theorem B468337 : Blo 366759 468337 := bbase (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) (by norm_num)
theorem B828845 : Blo 366759 828845 := bbase (se 3 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 828845 = 310817) (by norm_num)
theorem B697805 : Blo 366759 697805 := bbase (se 3 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 697805 = 261677) (by norm_num)
theorem B468433 : Blo 366759 468433 := bbase (se 2 (by rfl) ⟨175662, by rfl⟩ : syracuseStep 468433 = 351325) (by norm_num)
theorem B828917 : Blo 366759 828917 := bbase (se 5 (by rfl) ⟨38855, by rfl⟩ : syracuseStep 828917 = 77711) (by norm_num)
theorem B894461 : Blo 366759 894461 := bbase (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) (by norm_num)
theorem B828989 : Blo 366759 828989 := bbase (se 3 (by rfl) ⟨155435, by rfl⟩ : syracuseStep 828989 = 310871) (by norm_num)
theorem B468605 : Blo 366759 468605 := bbase (se 3 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 468605 = 175727) (by norm_num)
theorem B829061 : Blo 366759 829061 := bbase (se 4 (by rfl) ⟨77724, by rfl⟩ : syracuseStep 829061 = 155449) (by norm_num)
theorem B468661 : Blo 366759 468661 := bbase (se 5 (by rfl) ⟨21968, by rfl⟩ : syracuseStep 468661 = 43937) (by norm_num)
theorem B829133 : Blo 366759 829133 := bbase (se 3 (by rfl) ⟨155462, by rfl⟩ : syracuseStep 829133 = 310925) (by norm_num)
theorem B829205 : Blo 366759 829205 := bbase (se 6 (by rfl) ⟨19434, by rfl⟩ : syracuseStep 829205 = 38869) (by norm_num)
theorem B468757 : Blo 366759 468757 := bbase (se 6 (by rfl) ⟨10986, by rfl⟩ : syracuseStep 468757 = 21973) (by norm_num)
theorem B829277 : Blo 366759 829277 := bbase (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) (by norm_num)
theorem B829349 : Blo 366759 829349 := bbase (se 4 (by rfl) ⟨77751, by rfl⟩ : syracuseStep 829349 = 155503) (by norm_num)
theorem B468929 : Blo 366759 468929 := bbase (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) (by norm_num)
theorem B829421 : Blo 366759 829421 := bbase (se 3 (by rfl) ⟨155516, by rfl⟩ : syracuseStep 829421 = 311033) (by norm_num)
theorem B468985 : Blo 366759 468985 := bbase (se 2 (by rfl) ⟨175869, by rfl⟩ : syracuseStep 468985 = 351739) (by norm_num)
theorem B829493 : Blo 366759 829493 := bbase (se 5 (by rfl) ⟨38882, by rfl⟩ : syracuseStep 829493 = 77765) (by norm_num)
theorem B13674581 : Blo 366759 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B469081 : Blo 366759 469081 := bbase (se 2 (by rfl) ⟨175905, by rfl⟩ : syracuseStep 469081 = 351811) (by norm_num)
theorem B829565 : Blo 366759 829565 := bbase (se 3 (by rfl) ⟨155543, by rfl⟩ : syracuseStep 829565 = 311087) (by norm_num)
theorem B3549365 : Blo 366759 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B698557 : Blo 366759 698557 := bbase (se 3 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 698557 = 261959) (by norm_num)
theorem B829637 : Blo 366759 829637 := bbase (se 4 (by rfl) ⟨77778, by rfl⟩ : syracuseStep 829637 = 155557) (by norm_num)
theorem B829709 : Blo 366759 829709 := bbase (se 3 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 829709 = 311141) (by norm_num)
theorem B698701 : Blo 366759 698701 := bbase (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) (by norm_num)
theorem B829781 : Blo 366759 829781 := bbase (se 10 (by rfl) ⟨1215, by rfl⟩ : syracuseStep 829781 = 2431) (by norm_num)
theorem B567685 : Blo 366759 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B1583509 : Blo 366759 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B829853 : Blo 366759 829853 := bbase (se 3 (by rfl) ⟨155597, by rfl⟩ : syracuseStep 829853 = 311195) (by norm_num)
theorem B1583525 : Blo 366759 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B2795957 : Blo 366759 2795957 := bbase (se 5 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 2795957 = 262121) (by norm_num)
theorem B534997 : Blo 366759 534997 := bbase (se 7 (by rfl) ⟨6269, by rfl⟩ : syracuseStep 534997 = 12539) (by norm_num)
theorem B829925 : Blo 366759 829925 := bbase (se 4 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 829925 = 155611) (by norm_num)
theorem B698861 : Blo 366759 698861 := bbase (se 3 (by rfl) ⟨131036, by rfl⟩ : syracuseStep 698861 = 262073) (by norm_num)
theorem B829997 : Blo 366759 829997 := bbase (se 3 (by rfl) ⟨155624, by rfl⟩ : syracuseStep 829997 = 311249) (by norm_num)
theorem B830069 : Blo 366759 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B928381 : Blo 366759 928381 := bbase (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) (by norm_num)
theorem B699005 : Blo 366759 699005 := bbase (se 3 (by rfl) ⟨131063, by rfl⟩ : syracuseStep 699005 = 262127) (by norm_num)
theorem B633469 : Blo 366759 633469 := bbase (se 3 (by rfl) ⟨118775, by rfl⟩ : syracuseStep 633469 = 237551) (by norm_num)
theorem B830141 : Blo 366759 830141 := bbase (se 3 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 830141 = 311303) (by norm_num)
theorem B928493 : Blo 366759 928493 := bbase (se 3 (by rfl) ⟨174092, by rfl⟩ : syracuseStep 928493 = 348185) (by norm_num)
theorem B830213 : Blo 366759 830213 := bbase (se 4 (by rfl) ⟨77832, by rfl⟩ : syracuseStep 830213 = 155665) (by norm_num)
theorem B994117 : Blo 366759 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B830285 : Blo 366759 830285 := bbase (se 3 (by rfl) ⟨155678, by rfl⟩ : syracuseStep 830285 = 311357) (by norm_num)
theorem B1321829 : Blo 366759 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B830357 : Blo 366759 830357 := bbase (se 6 (by rfl) ⟨19461, by rfl⟩ : syracuseStep 830357 = 38923) (by norm_num)
theorem B699293 : Blo 366759 699293 := bbase (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) (by norm_num)
theorem B928685 : Blo 366759 928685 := bbase (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) (by norm_num)
theorem B830429 : Blo 366759 830429 := bbase (se 3 (by rfl) ⟨155705, by rfl⟩ : syracuseStep 830429 = 311411) (by norm_num)
theorem B830501 : Blo 366759 830501 := bbase (se 4 (by rfl) ⟨77859, by rfl⟩ : syracuseStep 830501 = 155719) (by norm_num)
theorem B699445 : Blo 366759 699445 := bbase (se 5 (by rfl) ⟨32786, by rfl⟩ : syracuseStep 699445 = 65573) (by norm_num)
theorem B830573 : Blo 366759 830573 := bbase (se 3 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 830573 = 311465) (by norm_num)
theorem B830645 : Blo 366759 830645 := bbase (se 5 (by rfl) ⟨38936, by rfl⟩ : syracuseStep 830645 = 77873) (by norm_num)
theorem B6302933 : Blo 366759 6302933 := bbase (se 7 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 6302933 = 147725) (by norm_num)
theorem B830717 : Blo 366759 830717 := bbase (se 3 (by rfl) ⟨155759, by rfl⟩ : syracuseStep 830717 = 311519) (by norm_num)
theorem B929029 : Blo 366759 929029 := bbase (se 4 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 929029 = 174193) (by norm_num)
theorem B830789 : Blo 366759 830789 := bbase (se 4 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 830789 = 155773) (by norm_num)
theorem B699749 : Blo 366759 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B929141 : Blo 366759 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B372097 : Blo 366759 372097 := bbase (se 2 (by rfl) ⟨139536, by rfl⟩ : syracuseStep 372097 = 279073) (by norm_num)
theorem B830861 : Blo 366759 830861 := bbase (se 3 (by rfl) ⟨155786, by rfl⟩ : syracuseStep 830861 = 311573) (by norm_num)
theorem B830933 : Blo 366759 830933 := bbase (se 7 (by rfl) ⟨9737, by rfl⟩ : syracuseStep 830933 = 19475) (by norm_num)
theorem B831005 : Blo 366759 831005 := bbase (se 3 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 831005 = 311627) (by norm_num)
theorem B929333 : Blo 366759 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B1683013 : Blo 366759 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B831077 : Blo 366759 831077 := bbase (se 4 (by rfl) ⟨77913, by rfl⟩ : syracuseStep 831077 = 155827) (by norm_num)
theorem B667237 : Blo 366759 667237 := bbase (se 4 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 667237 = 125107) (by norm_num)
theorem B831149 : Blo 366759 831149 := bbase (se 3 (by rfl) ⟨155840, by rfl⟩ : syracuseStep 831149 = 311681) (by norm_num)
theorem B831221 : Blo 366759 831221 := bbase (se 5 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 831221 = 77927) (by norm_num)
theorem B667445 : Blo 366759 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B831293 : Blo 366759 831293 := bbase (se 3 (by rfl) ⟨155867, by rfl⟩ : syracuseStep 831293 = 311735) (by norm_num)
theorem B1781621 : Blo 366759 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B831365 : Blo 366759 831365 := bbase (se 4 (by rfl) ⟨77940, by rfl⟩ : syracuseStep 831365 = 155881) (by norm_num)
theorem B929677 : Blo 366759 929677 := bbase (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) (by norm_num)
theorem B405433 : Blo 366759 405433 := bbase (se 2 (by rfl) ⟨152037, by rfl⟩ : syracuseStep 405433 = 304075) (by norm_num)
theorem B831437 : Blo 366759 831437 := bbase (se 3 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 831437 = 311789) (by norm_num)
theorem B1683413 : Blo 366759 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B929789 : Blo 366759 929789 := bbase (se 3 (by rfl) ⟨174335, by rfl⟩ : syracuseStep 929789 = 348671) (by norm_num)
theorem B831509 : Blo 366759 831509 := bbase (se 6 (by rfl) ⟨19488, by rfl⟩ : syracuseStep 831509 = 38977) (by norm_num)
theorem B700501 : Blo 366759 700501 := bbase (se 8 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 700501 = 8209) (by norm_num)
theorem B831581 : Blo 366759 831581 := bbase (se 3 (by rfl) ⟨155921, by rfl⟩ : syracuseStep 831581 = 311843) (by norm_num)
theorem B831653 : Blo 366759 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B929981 : Blo 366759 929981 := bbase (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) (by norm_num)
theorem B700645 : Blo 366759 700645 := bbase (se 4 (by rfl) ⟨65685, by rfl⟩ : syracuseStep 700645 = 131371) (by norm_num)
theorem B831725 : Blo 366759 831725 := bbase (se 3 (by rfl) ⟨155948, by rfl⟩ : syracuseStep 831725 = 311897) (by norm_num)
theorem B372997 : Blo 366759 372997 := bbase (se 4 (by rfl) ⟨34968, by rfl⟩ : syracuseStep 372997 = 69937) (by norm_num)
theorem B831797 : Blo 366759 831797 := bbase (se 5 (by rfl) ⟨38990, by rfl⟩ : syracuseStep 831797 = 77981) (by norm_num)
theorem B831869 : Blo 366759 831869 := bbase (se 3 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 831869 = 311951) (by norm_num)
theorem B700805 : Blo 366759 700805 := bbase (se 4 (by rfl) ⟨65700, by rfl⟩ : syracuseStep 700805 = 131401) (by norm_num)
theorem B831941 : Blo 366759 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B832013 : Blo 366759 832013 := bbase (se 3 (by rfl) ⟨156002, by rfl⟩ : syracuseStep 832013 = 312005) (by norm_num)
theorem B930325 : Blo 366759 930325 := bbase (se 6 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 930325 = 43609) (by norm_num)
theorem B700949 : Blo 366759 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B1487413 : Blo 366759 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B373313 : Blo 366759 373313 := bbase (se 2 (by rfl) ⟨139992, by rfl⟩ : syracuseStep 373313 = 279985) (by norm_num)
theorem B832085 : Blo 366759 832085 := bbase (se 8 (by rfl) ⟨4875, by rfl⟩ : syracuseStep 832085 = 9751) (by norm_num)
theorem B930437 : Blo 366759 930437 := bbase (se 4 (by rfl) ⟨87228, by rfl⟩ : syracuseStep 930437 = 174457) (by norm_num)
theorem B832157 : Blo 366759 832157 := bbase (se 3 (by rfl) ⟨156029, by rfl⟩ : syracuseStep 832157 = 312059) (by norm_num)
theorem B832229 : Blo 366759 832229 := bbase (se 4 (by rfl) ⟨78021, by rfl⟩ : syracuseStep 832229 = 156043) (by norm_num)
theorem B832301 : Blo 366759 832301 := bbase (se 3 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 832301 = 312113) (by norm_num)
theorem B701237 : Blo 366759 701237 := bbase (se 5 (by rfl) ⟨32870, by rfl⟩ : syracuseStep 701237 = 65741) (by norm_num)
theorem B930629 : Blo 366759 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B373573 : Blo 366759 373573 := bbase (se 4 (by rfl) ⟨35022, by rfl⟩ : syracuseStep 373573 = 70045) (by norm_num)
theorem B8926037 : Blo 366759 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B832373 : Blo 366759 832373 := bbase (se 5 (by rfl) ⟨39017, by rfl⟩ : syracuseStep 832373 = 78035) (by norm_num)
theorem B832445 : Blo 366759 832445 := bbase (se 3 (by rfl) ⟨156083, by rfl⟩ : syracuseStep 832445 = 312167) (by norm_num)
theorem B701389 : Blo 366759 701389 := bbase (se 3 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 701389 = 263021) (by norm_num)
theorem B832517 : Blo 366759 832517 := bbase (se 4 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 832517 = 156097) (by norm_num)
theorem B832589 : Blo 366759 832589 := bbase (se 3 (by rfl) ⟨156110, by rfl⟩ : syracuseStep 832589 = 312221) (by norm_num)
theorem B832661 : Blo 366759 832661 := bbase (se 6 (by rfl) ⟨19515, by rfl⟩ : syracuseStep 832661 = 39031) (by norm_num)
theorem B930973 : Blo 366759 930973 := bbase (se 3 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 930973 = 349115) (by norm_num)
theorem B832733 : Blo 366759 832733 := bbase (se 3 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 832733 = 312275) (by norm_num)
theorem B701693 : Blo 366759 701693 := bbase (se 3 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 701693 = 263135) (by norm_num)
theorem B931085 : Blo 366759 931085 := bbase (se 3 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 931085 = 349157) (by norm_num)
theorem B832805 : Blo 366759 832805 := bbase (se 4 (by rfl) ⟨78075, by rfl⟩ : syracuseStep 832805 = 156151) (by norm_num)
theorem B832877 : Blo 366759 832877 := bbase (se 3 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 832877 = 312329) (by norm_num)
theorem B832949 : Blo 366759 832949 := bbase (se 5 (by rfl) ⟨39044, by rfl⟩ : syracuseStep 832949 = 78089) (by norm_num)
theorem B931277 : Blo 366759 931277 := bbase (se 3 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 931277 = 349229) (by norm_num)
theorem B833021 : Blo 366759 833021 := bbase (se 3 (by rfl) ⟨156191, by rfl⟩ : syracuseStep 833021 = 312383) (by norm_num)
theorem B833093 : Blo 366759 833093 := bbase (se 4 (by rfl) ⟨78102, by rfl⟩ : syracuseStep 833093 = 156205) (by norm_num)
theorem B2111093 : Blo 366759 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B472717 : Blo 366759 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B833165 : Blo 366759 833165 := bbase (se 3 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 833165 = 312437) (by norm_num)
theorem B374477 : Blo 366759 374477 := bbase (se 3 (by rfl) ⟨70214, by rfl⟩ : syracuseStep 374477 = 140429) (by norm_num)
theorem B3192533 : Blo 366759 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B833237 : Blo 366759 833237 := bbase (se 7 (by rfl) ⟨9764, by rfl⟩ : syracuseStep 833237 = 19529) (by norm_num)
theorem B2668277 : Blo 366759 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B833309 : Blo 366759 833309 := bbase (se 3 (by rfl) ⟨156245, by rfl⟩ : syracuseStep 833309 = 312491) (by norm_num)
theorem B931621 : Blo 366759 931621 := bbase (se 4 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 931621 = 174679) (by norm_num)
theorem B1259333 : Blo 366759 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B833381 : Blo 366759 833381 := bbase (se 4 (by rfl) ⟨78129, by rfl⟩ : syracuseStep 833381 = 156259) (by norm_num)
theorem B931733 : Blo 366759 931733 := bbase (se 6 (by rfl) ⟨21837, by rfl⟩ : syracuseStep 931733 = 43675) (by norm_num)
theorem B833453 : Blo 366759 833453 := bbase (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) (by norm_num)
theorem B473045 : Blo 366759 473045 := bbase (se 7 (by rfl) ⟨5543, by rfl⟩ : syracuseStep 473045 = 11087) (by norm_num)
theorem B702445 : Blo 366759 702445 := bbase (se 3 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 702445 = 263417) (by norm_num)
theorem B833525 : Blo 366759 833525 := bbase (se 5 (by rfl) ⟨39071, by rfl⟩ : syracuseStep 833525 = 78143) (by norm_num)
theorem B833597 : Blo 366759 833597 := bbase (se 3 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 833597 = 312599) (by norm_num)
theorem B931925 : Blo 366759 931925 := bbase (se 8 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 931925 = 10921) (by norm_num)
theorem B702589 : Blo 366759 702589 := bbase (se 3 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 702589 = 263471) (by norm_num)
theorem B833669 : Blo 366759 833669 := bbase (se 4 (by rfl) ⟨78156, by rfl⟩ : syracuseStep 833669 = 156313) (by norm_num)
theorem B833741 : Blo 366759 833741 := bbase (se 3 (by rfl) ⟨156326, by rfl⟩ : syracuseStep 833741 = 312653) (by norm_num)
theorem B375041 : Blo 366759 375041 := bbase (se 2 (by rfl) ⟨140640, by rfl⟩ : syracuseStep 375041 = 281281) (by norm_num)
theorem B1325317 : Blo 366759 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B833813 : Blo 366759 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B702749 : Blo 366759 702749 := bbase (se 3 (by rfl) ⟨131765, by rfl⟩ : syracuseStep 702749 = 263531) (by norm_num)
theorem B833885 : Blo 366759 833885 := bbase (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) (by norm_num)
theorem B440677 : Blo 366759 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B1325477 : Blo 366759 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B833957 : Blo 366759 833957 := bbase (se 4 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 833957 = 156367) (by norm_num)
theorem B440749 : Blo 366759 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B932269 : Blo 366759 932269 := bbase (se 3 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 932269 = 349601) (by norm_num)
theorem B702893 : Blo 366759 702893 := bbase (se 3 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 702893 = 263585) (by norm_num)
theorem B1423813 : Blo 366759 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B834029 : Blo 366759 834029 := bbase (se 3 (by rfl) ⟨156380, by rfl⟩ : syracuseStep 834029 = 312761) (by norm_num)
theorem B932381 : Blo 366759 932381 := bbase (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) (by norm_num)
theorem B440869 : Blo 366759 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B1325605 : Blo 366759 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B473645 : Blo 366759 473645 := bbase (se 3 (by rfl) ⟨88808, by rfl⟩ : syracuseStep 473645 = 177617) (by norm_num)
theorem B834101 : Blo 366759 834101 := bbase (se 5 (by rfl) ⟨39098, by rfl⟩ : syracuseStep 834101 = 78197) (by norm_num)
theorem B834173 : Blo 366759 834173 := bbase (se 3 (by rfl) ⟨156407, by rfl⟩ : syracuseStep 834173 = 312815) (by norm_num)
theorem B703181 : Blo 366759 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B932573 : Blo 366759 932573 := bbase (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) (by norm_num)
theorem B473881 : Blo 366759 473881 := bbase (se 2 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 473881 = 355411) (by norm_num)
theorem B703333 : Blo 366759 703333 := bbase (se 4 (by rfl) ⟨65937, by rfl⟩ : syracuseStep 703333 = 131875) (by norm_num)
theorem B441253 : Blo 366759 441253 := bbase (se 4 (by rfl) ⟨41367, by rfl⟩ : syracuseStep 441253 = 82735) (by norm_num)
theorem B932917 : Blo 366759 932917 := bbase (se 5 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 932917 = 87461) (by norm_num)
theorem B703637 : Blo 366759 703637 := bbase (se 6 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 703637 = 32983) (by norm_num)
theorem B933029 : Blo 366759 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B998725 : Blo 366759 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B933221 : Blo 366759 933221 := bbase (se 4 (by rfl) ⟨87489, by rfl⟩ : syracuseStep 933221 = 174979) (by norm_num)
theorem B900629 : Blo 366759 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B441941 : Blo 366759 441941 := bbase (se 8 (by rfl) ⟨2589, by rfl⟩ : syracuseStep 441941 = 5179) (by norm_num)
theorem B933565 : Blo 366759 933565 := bbase (se 3 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 933565 = 350087) (by norm_num)
theorem B933677 : Blo 366759 933677 := bbase (se 3 (by rfl) ⟨175064, by rfl⟩ : syracuseStep 933677 = 350129) (by norm_num)
theorem B933869 : Blo 366759 933869 := bbase (se 3 (by rfl) ⟨175100, by rfl⟩ : syracuseStep 933869 = 350201) (by norm_num)
theorem B409709 : Blo 366759 409709 := bbase (se 3 (by rfl) ⟨76820, by rfl⟩ : syracuseStep 409709 = 153641) (by norm_num)
theorem B606341 : Blo 366759 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B442541 : Blo 366759 442541 := bbase (se 3 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 442541 = 165953) (by norm_num)
theorem B934213 : Blo 366759 934213 := bbase (se 4 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 934213 = 175165) (by norm_num)
theorem B1392997 : Blo 366759 1392997 := bbase (se 4 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 1392997 = 261187) (by norm_num)
theorem B934325 : Blo 366759 934325 := bbase (se 5 (by rfl) ⟨43796, by rfl⟩ : syracuseStep 934325 = 87593) (by norm_num)
theorem B442849 : Blo 366759 442849 := bbase (se 2 (by rfl) ⟨166068, by rfl⟩ : syracuseStep 442849 = 332137) (by norm_num)
theorem B442945 : Blo 366759 442945 := bbase (se 2 (by rfl) ⟨166104, by rfl⟩ : syracuseStep 442945 = 332209) (by norm_num)
theorem B1360469 : Blo 366759 1360469 := bbase (se 8 (by rfl) ⟨7971, by rfl⟩ : syracuseStep 1360469 = 15943) (by norm_num)
theorem B442993 : Blo 366759 442993 := bbase (se 2 (by rfl) ⟨166122, by rfl⟩ : syracuseStep 442993 = 332245) (by norm_num)
theorem B934517 : Blo 366759 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B1393301 : Blo 366759 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B934861 : Blo 366759 934861 := bbase (se 3 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 934861 = 350573) (by norm_num)
theorem B1262549 : Blo 366759 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B934973 : Blo 366759 934973 := bbase (se 3 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 934973 = 350615) (by norm_num)
theorem B1066117 : Blo 366759 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B1688741 : Blo 366759 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B935165 : Blo 366759 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B837029 : Blo 366759 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B935509 : Blo 366759 935509 := bbase (se 8 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 935509 = 10963) (by norm_num)
theorem B935621 : Blo 366759 935621 := bbase (se 4 (by rfl) ⟨87714, by rfl⟩ : syracuseStep 935621 = 175429) (by norm_num)
theorem B14436053 : Blo 366759 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B444209 : Blo 366759 444209 := bbase (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) (by norm_num)
theorem B935813 : Blo 366759 935813 := bbase (se 4 (by rfl) ⟨87732, by rfl⟩ : syracuseStep 935813 = 175465) (by norm_num)
theorem B444377 : Blo 366759 444377 := bbase (se 2 (by rfl) ⟨166641, by rfl⟩ : syracuseStep 444377 = 333283) (by norm_num)
theorem B2803733 : Blo 366759 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B804917 : Blo 366759 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B936157 : Blo 366759 936157 := bbase (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) (by norm_num)
theorem B444685 : Blo 366759 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B936269 : Blo 366759 936269 := bbase (se 3 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 936269 = 351101) (by norm_num)
theorem B1886597 : Blo 366759 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B444901 : Blo 366759 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B936461 : Blo 366759 936461 := bbase (se 3 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 936461 = 351173) (by norm_num)
theorem B1198709 : Blo 366759 1198709 := bbase (se 5 (by rfl) ⟨56189, by rfl⟩ : syracuseStep 1198709 = 112379) (by norm_num)
theorem B1395413 : Blo 366759 1395413 := bbase (se 7 (by rfl) ⟨16352, by rfl⟩ : syracuseStep 1395413 = 32705) (by norm_num)
theorem B445213 : Blo 366759 445213 := bbase (se 3 (by rfl) ⟨83477, by rfl⟩ : syracuseStep 445213 = 166955) (by norm_num)
theorem B936805 : Blo 366759 936805 := bbase (se 4 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 936805 = 175651) (by norm_num)
theorem B412609 : Blo 366759 412609 := bbase (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) (by norm_num)
theorem B936917 : Blo 366759 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B412645 : Blo 366759 412645 := bbase (se 4 (by rfl) ⟨38685, by rfl⟩ : syracuseStep 412645 = 77371) (by norm_num)
theorem B1395701 : Blo 366759 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B412681 : Blo 366759 412681 := bbase (se 2 (by rfl) ⟨154755, by rfl⟩ : syracuseStep 412681 = 309511) (by norm_num)
theorem B412717 : Blo 366759 412717 := bbase (se 3 (by rfl) ⟨77384, by rfl⟩ : syracuseStep 412717 = 154769) (by norm_num)
theorem B412753 : Blo 366759 412753 := bbase (se 2 (by rfl) ⟨154782, by rfl⟩ : syracuseStep 412753 = 309565) (by norm_num)
theorem B412789 : Blo 366759 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B937109 : Blo 366759 937109 := bbase (se 6 (by rfl) ⟨21963, by rfl⟩ : syracuseStep 937109 = 43927) (by norm_num)
theorem B412825 : Blo 366759 412825 := bbase (se 2 (by rfl) ⟨154809, by rfl⟩ : syracuseStep 412825 = 309619) (by norm_num)
theorem B412861 : Blo 366759 412861 := bbase (se 3 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 412861 = 154823) (by norm_num)
theorem B412897 : Blo 366759 412897 := bbase (se 2 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 412897 = 309673) (by norm_num)
theorem B412933 : Blo 366759 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B412969 : Blo 366759 412969 := bbase (se 2 (by rfl) ⟨154863, by rfl⟩ : syracuseStep 412969 = 309727) (by norm_num)
theorem B413005 : Blo 366759 413005 := bbase (se 3 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 413005 = 154877) (by norm_num)
theorem B839005 : Blo 366759 839005 := bbase (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) (by norm_num)
theorem B1264997 : Blo 366759 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B413041 : Blo 366759 413041 := bbase (se 2 (by rfl) ⟨154890, by rfl⟩ : syracuseStep 413041 = 309781) (by norm_num)
theorem B413077 : Blo 366759 413077 := bbase (se 6 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 413077 = 19363) (by norm_num)
theorem B413113 : Blo 366759 413113 := bbase (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) (by norm_num)
theorem B413149 : Blo 366759 413149 := bbase (se 3 (by rfl) ⟨77465, by rfl⟩ : syracuseStep 413149 = 154931) (by norm_num)
theorem B937453 : Blo 366759 937453 := bbase (se 3 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 937453 = 351545) (by norm_num)
theorem B413185 : Blo 366759 413185 := bbase (se 2 (by rfl) ⟨154944, by rfl⟩ : syracuseStep 413185 = 309889) (by norm_num)
theorem B413221 : Blo 366759 413221 := bbase (se 4 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 413221 = 77479) (by norm_num)
theorem B1691189 : Blo 366759 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B413257 : Blo 366759 413257 := bbase (se 2 (by rfl) ⟨154971, by rfl⟩ : syracuseStep 413257 = 309943) (by norm_num)
theorem B4705877 : Blo 366759 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B937565 : Blo 366759 937565 := bbase (se 3 (by rfl) ⟨175793, by rfl⟩ : syracuseStep 937565 = 351587) (by norm_num)
theorem B413293 : Blo 366759 413293 := bbase (se 3 (by rfl) ⟨77492, by rfl⟩ : syracuseStep 413293 = 154985) (by norm_num)
theorem B413329 : Blo 366759 413329 := bbase (se 2 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 413329 = 309997) (by norm_num)
theorem B413365 : Blo 366759 413365 := bbase (se 5 (by rfl) ⟨19376, by rfl⟩ : syracuseStep 413365 = 38753) (by norm_num)
theorem B413401 : Blo 366759 413401 := bbase (se 2 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 413401 = 310051) (by norm_num)
theorem B413437 : Blo 366759 413437 := bbase (se 3 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 413437 = 155039) (by norm_num)
theorem B1068821 : Blo 366759 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B937757 : Blo 366759 937757 := bbase (se 3 (by rfl) ⟨175829, by rfl⟩ : syracuseStep 937757 = 351659) (by norm_num)
theorem B413473 : Blo 366759 413473 := bbase (se 2 (by rfl) ⟨155052, by rfl⟩ : syracuseStep 413473 = 310105) (by norm_num)
theorem B413509 : Blo 366759 413509 := bbase (se 4 (by rfl) ⟨38766, by rfl⟩ : syracuseStep 413509 = 77533) (by norm_num)
theorem B675677 : Blo 366759 675677 := bbase (se 3 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 675677 = 253379) (by norm_num)
theorem B413545 : Blo 366759 413545 := bbase (se 2 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 413545 = 310159) (by norm_num)
theorem B413581 : Blo 366759 413581 := bbase (se 3 (by rfl) ⟨77546, by rfl⟩ : syracuseStep 413581 = 155093) (by norm_num)
theorem B413617 : Blo 366759 413617 := bbase (se 2 (by rfl) ⟨155106, by rfl⟩ : syracuseStep 413617 = 310213) (by norm_num)
theorem B413653 : Blo 366759 413653 := bbase (se 7 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 413653 = 9695) (by norm_num)
theorem B413689 : Blo 366759 413689 := bbase (se 2 (by rfl) ⟨155133, by rfl⟩ : syracuseStep 413689 = 310267) (by norm_num)
theorem B4739093 : Blo 366759 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B3166229 : Blo 366759 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B413725 : Blo 366759 413725 := bbase (se 3 (by rfl) ⟨77573, by rfl⟩ : syracuseStep 413725 = 155147) (by norm_num)
theorem B413761 : Blo 366759 413761 := bbase (se 2 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 413761 = 310321) (by norm_num)
theorem B512093 : Blo 366759 512093 := bbase (se 3 (by rfl) ⟨96017, by rfl⟩ : syracuseStep 512093 = 192035) (by norm_num)
theorem B413797 : Blo 366759 413797 := bbase (se 4 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 413797 = 77587) (by norm_num)
theorem B1986677 : Blo 366759 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B938101 : Blo 366759 938101 := bbase (se 5 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 938101 = 87947) (by norm_num)
theorem B413833 : Blo 366759 413833 := bbase (se 2 (by rfl) ⟨155187, by rfl⟩ : syracuseStep 413833 = 310375) (by norm_num)
theorem B1396885 : Blo 366759 1396885 := bbase (se 6 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 1396885 = 65479) (by norm_num)
theorem B413869 : Blo 366759 413869 := bbase (se 3 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 413869 = 155201) (by norm_num)
theorem B413905 : Blo 366759 413905 := bbase (se 2 (by rfl) ⟨155214, by rfl⟩ : syracuseStep 413905 = 310429) (by norm_num)
theorem B938213 : Blo 366759 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B413941 : Blo 366759 413941 := bbase (se 5 (by rfl) ⟨19403, by rfl⟩ : syracuseStep 413941 = 38807) (by norm_num)
theorem B413977 : Blo 366759 413977 := bbase (se 2 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 413977 = 310483) (by norm_num)
theorem B414013 : Blo 366759 414013 := bbase (se 3 (by rfl) ⟨77627, by rfl⟩ : syracuseStep 414013 = 155255) (by norm_num)
theorem B414049 : Blo 366759 414049 := bbase (se 2 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 414049 = 310537) (by norm_num)
theorem B414085 : Blo 366759 414085 := bbase (se 4 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 414085 = 77641) (by norm_num)
theorem B709021 : Blo 366759 709021 := bbase (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) (by norm_num)
theorem B938405 : Blo 366759 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B414121 : Blo 366759 414121 := bbase (se 2 (by rfl) ⟨155295, by rfl⟩ : syracuseStep 414121 = 310591) (by norm_num)
theorem B1397189 : Blo 366759 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B414157 : Blo 366759 414157 := bbase (se 3 (by rfl) ⟨77654, by rfl⟩ : syracuseStep 414157 = 155309) (by norm_num)
theorem B414193 : Blo 366759 414193 := bbase (se 2 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 414193 = 310645) (by norm_num)
theorem B2544149 : Blo 366759 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B414229 : Blo 366759 414229 := bbase (se 6 (by rfl) ⟨9708, by rfl⟩ : syracuseStep 414229 = 19417) (by norm_num)
theorem B414265 : Blo 366759 414265 := bbase (se 2 (by rfl) ⟨155349, by rfl⟩ : syracuseStep 414265 = 310699) (by norm_num)
theorem B414301 : Blo 366759 414301 := bbase (se 3 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 414301 = 155363) (by norm_num)
theorem B414337 : Blo 366759 414337 := bbase (se 2 (by rfl) ⟨155376, by rfl⟩ : syracuseStep 414337 = 310753) (by norm_num)
theorem B414373 : Blo 366759 414373 := bbase (se 4 (by rfl) ⟨38847, by rfl⟩ : syracuseStep 414373 = 77695) (by norm_num)
theorem B414409 : Blo 366759 414409 := bbase (se 2 (by rfl) ⟨155403, by rfl⟩ : syracuseStep 414409 = 310807) (by norm_num)
theorem B414445 : Blo 366759 414445 := bbase (se 3 (by rfl) ⟨77708, by rfl⟩ : syracuseStep 414445 = 155417) (by norm_num)
theorem B414481 : Blo 366759 414481 := bbase (se 2 (by rfl) ⟨155430, by rfl⟩ : syracuseStep 414481 = 310861) (by norm_num)
theorem B414517 : Blo 366759 414517 := bbase (se 5 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 414517 = 38861) (by norm_num)
theorem B414553 : Blo 366759 414553 := bbase (se 2 (by rfl) ⟨155457, by rfl⟩ : syracuseStep 414553 = 310915) (by norm_num)
theorem B414589 : Blo 366759 414589 := bbase (se 3 (by rfl) ⟨77735, by rfl⟩ : syracuseStep 414589 = 155471) (by norm_num)
theorem B414625 : Blo 366759 414625 := bbase (se 2 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 414625 = 310969) (by norm_num)
theorem B414661 : Blo 366759 414661 := bbase (se 4 (by rfl) ⟨38874, by rfl⟩ : syracuseStep 414661 = 77749) (by norm_num)
theorem B414697 : Blo 366759 414697 := bbase (se 2 (by rfl) ⟨155511, by rfl⟩ : syracuseStep 414697 = 311023) (by norm_num)
theorem B414733 : Blo 366759 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B414769 : Blo 366759 414769 := bbase (se 2 (by rfl) ⟨155538, by rfl⟩ : syracuseStep 414769 = 311077) (by norm_num)
theorem B1332293 : Blo 366759 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B414805 : Blo 366759 414805 := bbase (se 8 (by rfl) ⟨2430, by rfl⟩ : syracuseStep 414805 = 4861) (by norm_num)
theorem B414841 : Blo 366759 414841 := bbase (se 2 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 414841 = 311131) (by norm_num)
theorem B414877 : Blo 366759 414877 := bbase (se 3 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 414877 = 155579) (by norm_num)
theorem B414913 : Blo 366759 414913 := bbase (se 2 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 414913 = 311185) (by norm_num)
theorem B414949 : Blo 366759 414949 := bbase (se 4 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 414949 = 77803) (by norm_num)
theorem B414985 : Blo 366759 414985 := bbase (se 2 (by rfl) ⟨155619, by rfl⟩ : syracuseStep 414985 = 311239) (by norm_num)
theorem B415021 : Blo 366759 415021 := bbase (se 3 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 415021 = 155633) (by norm_num)
theorem B415057 : Blo 366759 415057 := bbase (se 2 (by rfl) ⟨155646, by rfl⟩ : syracuseStep 415057 = 311293) (by norm_num)
theorem B415093 : Blo 366759 415093 := bbase (se 5 (by rfl) ⟨19457, by rfl⟩ : syracuseStep 415093 = 38915) (by norm_num)
theorem B415129 : Blo 366759 415129 := bbase (se 2 (by rfl) ⟨155673, by rfl⟩ : syracuseStep 415129 = 311347) (by norm_num)
theorem B415165 : Blo 366759 415165 := bbase (se 3 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 415165 = 155687) (by norm_num)
theorem B2840021 : Blo 366759 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B415201 : Blo 366759 415201 := bbase (se 2 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 415201 = 311401) (by norm_num)
theorem B415237 : Blo 366759 415237 := bbase (se 4 (by rfl) ⟨38928, by rfl⟩ : syracuseStep 415237 = 77857) (by norm_num)
theorem B415273 : Blo 366759 415273 := bbase (se 2 (by rfl) ⟨155727, by rfl⟩ : syracuseStep 415273 = 311455) (by norm_num)
theorem B415309 : Blo 366759 415309 := bbase (se 3 (by rfl) ⟨77870, by rfl⟩ : syracuseStep 415309 = 155741) (by norm_num)
theorem B415345 : Blo 366759 415345 := bbase (se 2 (by rfl) ⟨155754, by rfl⟩ : syracuseStep 415345 = 311509) (by norm_num)
theorem B415381 : Blo 366759 415381 := bbase (se 6 (by rfl) ⟨9735, by rfl⟩ : syracuseStep 415381 = 19471) (by norm_num)
theorem B415417 : Blo 366759 415417 := bbase (se 2 (by rfl) ⟨155781, by rfl⟩ : syracuseStep 415417 = 311563) (by norm_num)
theorem B415453 : Blo 366759 415453 := bbase (se 3 (by rfl) ⟨77897, by rfl⟩ : syracuseStep 415453 = 155795) (by norm_num)
theorem B415489 : Blo 366759 415489 := bbase (se 2 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 415489 = 311617) (by norm_num)
theorem B415525 : Blo 366759 415525 := bbase (se 4 (by rfl) ⟨38955, by rfl⟩ : syracuseStep 415525 = 77911) (by norm_num)
theorem B415561 : Blo 366759 415561 := bbase (se 2 (by rfl) ⟨155835, by rfl⟩ : syracuseStep 415561 = 311671) (by norm_num)
theorem B415597 : Blo 366759 415597 := bbase (se 3 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 415597 = 155849) (by norm_num)
theorem B382837 : Blo 366759 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B415633 : Blo 366759 415633 := bbase (se 2 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 415633 = 311725) (by norm_num)
theorem B415669 : Blo 366759 415669 := bbase (se 5 (by rfl) ⟨19484, by rfl⟩ : syracuseStep 415669 = 38969) (by norm_num)
theorem B1333205 : Blo 366759 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B415705 : Blo 366759 415705 := bbase (se 2 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 415705 = 311779) (by norm_num)
theorem B415741 : Blo 366759 415741 := bbase (se 3 (by rfl) ⟨77951, by rfl⟩ : syracuseStep 415741 = 155903) (by norm_num)
theorem B415777 : Blo 366759 415777 := bbase (se 2 (by rfl) ⟨155916, by rfl⟩ : syracuseStep 415777 = 311833) (by norm_num)
theorem B415813 : Blo 366759 415813 := bbase (se 4 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 415813 = 77965) (by norm_num)
theorem B415849 : Blo 366759 415849 := bbase (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) (by norm_num)
theorem B1857653 : Blo 366759 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B841853 : Blo 366759 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B415885 : Blo 366759 415885 := bbase (se 3 (by rfl) ⟨77978, by rfl⟩ : syracuseStep 415885 = 155957) (by norm_num)
theorem B415921 : Blo 366759 415921 := bbase (se 2 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 415921 = 311941) (by norm_num)
theorem B415957 : Blo 366759 415957 := bbase (se 7 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 415957 = 9749) (by norm_num)
theorem B415993 : Blo 366759 415993 := bbase (se 2 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 415993 = 311995) (by norm_num)
theorem B416029 : Blo 366759 416029 := bbase (se 3 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 416029 = 156011) (by norm_num)
theorem B416065 : Blo 366759 416065 := bbase (se 2 (by rfl) ⟨156024, by rfl⟩ : syracuseStep 416065 = 312049) (by norm_num)
theorem B416101 : Blo 366759 416101 := bbase (se 4 (by rfl) ⟨39009, by rfl⟩ : syracuseStep 416101 = 78019) (by norm_num)
theorem B416137 : Blo 366759 416137 := bbase (se 2 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 416137 = 312103) (by norm_num)
theorem B3627413 : Blo 366759 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B416173 : Blo 366759 416173 := bbase (se 3 (by rfl) ⟨78032, by rfl⟩ : syracuseStep 416173 = 156065) (by norm_num)
theorem B416209 : Blo 366759 416209 := bbase (se 2 (by rfl) ⟨156078, by rfl⟩ : syracuseStep 416209 = 312157) (by norm_num)
theorem B3365333 : Blo 366759 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B416245 : Blo 366759 416245 := bbase (se 5 (by rfl) ⟨19511, by rfl⟩ : syracuseStep 416245 = 39023) (by norm_num)
theorem B1104389 : Blo 366759 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1399301 : Blo 366759 1399301 := bbase (se 4 (by rfl) ⟨131184, by rfl⟩ : syracuseStep 1399301 = 262369) (by norm_num)
theorem B416281 : Blo 366759 416281 := bbase (se 2 (by rfl) ⟨156105, by rfl⟩ : syracuseStep 416281 = 312211) (by norm_num)
theorem B416317 : Blo 366759 416317 := bbase (se 3 (by rfl) ⟨78059, by rfl⟩ : syracuseStep 416317 = 156119) (by norm_num)
theorem B416353 : Blo 366759 416353 := bbase (se 2 (by rfl) ⟨156132, by rfl⟩ : syracuseStep 416353 = 312265) (by norm_num)
theorem B416389 : Blo 366759 416389 := bbase (se 4 (by rfl) ⟨39036, by rfl⟩ : syracuseStep 416389 = 78073) (by norm_num)
theorem B416425 : Blo 366759 416425 := bbase (se 2 (by rfl) ⟨156159, by rfl⟩ : syracuseStep 416425 = 312319) (by norm_num)
theorem B416461 : Blo 366759 416461 := bbase (se 3 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 416461 = 156173) (by norm_num)
theorem B416497 : Blo 366759 416497 := bbase (se 2 (by rfl) ⟨156186, by rfl⟩ : syracuseStep 416497 = 312373) (by norm_num)
theorem B416533 : Blo 366759 416533 := bbase (se 6 (by rfl) ⟨9762, by rfl⟩ : syracuseStep 416533 = 19525) (by norm_num)
theorem B1399589 : Blo 366759 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B416569 : Blo 366759 416569 := bbase (se 2 (by rfl) ⟨156213, by rfl⟩ : syracuseStep 416569 = 312427) (by norm_num)
theorem B416605 : Blo 366759 416605 := bbase (se 3 (by rfl) ⟨78113, by rfl⟩ : syracuseStep 416605 = 156227) (by norm_num)
theorem B416641 : Blo 366759 416641 := bbase (se 2 (by rfl) ⟨156240, by rfl⟩ : syracuseStep 416641 = 312481) (by norm_num)
theorem B416677 : Blo 366759 416677 := bbase (se 4 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 416677 = 78127) (by norm_num)
theorem B416713 : Blo 366759 416713 := bbase (se 2 (by rfl) ⟨156267, by rfl⟩ : syracuseStep 416713 = 312535) (by norm_num)
theorem B416749 : Blo 366759 416749 := bbase (se 3 (by rfl) ⟨78140, by rfl⟩ : syracuseStep 416749 = 156281) (by norm_num)
theorem B416785 : Blo 366759 416785 := bbase (se 2 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 416785 = 312589) (by norm_num)
theorem B416821 : Blo 366759 416821 := bbase (se 5 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 416821 = 39077) (by norm_num)
theorem B416857 : Blo 366759 416857 := bbase (se 2 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 416857 = 312643) (by norm_num)
theorem B416893 : Blo 366759 416893 := bbase (se 3 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 416893 = 156335) (by norm_num)
theorem B416929 : Blo 366759 416929 := bbase (se 2 (by rfl) ⟨156348, by rfl⟩ : syracuseStep 416929 = 312697) (by norm_num)
theorem B416965 : Blo 366759 416965 := bbase (se 4 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 416965 = 78181) (by norm_num)
theorem B417001 : Blo 366759 417001 := bbase (se 2 (by rfl) ⟨156375, by rfl⟩ : syracuseStep 417001 = 312751) (by norm_num)
theorem B417037 : Blo 366759 417037 := bbase (se 3 (by rfl) ⟨78194, by rfl⟩ : syracuseStep 417037 = 156389) (by norm_num)
theorem B417073 : Blo 366759 417073 := bbase (se 2 (by rfl) ⟨156402, by rfl⟩ : syracuseStep 417073 = 312805) (by norm_num)
theorem B1858949 : Blo 366759 1858949 := bbase (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) (by norm_num)
theorem B1335061 : Blo 366759 1335061 := bbase (se 6 (by rfl) ⟨31290, by rfl⟩ : syracuseStep 1335061 = 62581) (by norm_num)
theorem B1400773 : Blo 366759 1400773 := bbase (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) (by norm_num)
theorem B2088949 : Blo 366759 2088949 := bbase (se 5 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 2088949 = 195839) (by norm_num)
theorem B3137525 : Blo 366759 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B1401077 : Blo 366759 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B450937 : Blo 366759 450937 := bbase (se 2 (by rfl) ⟨169101, by rfl⟩ : syracuseStep 450937 = 338203) (by norm_num)
theorem B746101 : Blo 366759 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B1860245 : Blo 366759 1860245 := bbase (se 6 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 1860245 = 87199) (by norm_num)
theorem B1335973 : Blo 366759 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B1794901 : Blo 366759 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1598341 : Blo 366759 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B1238165 : Blo 366759 1238165 := bbase (se 6 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 1238165 = 58039) (by norm_num)
theorem B1500389 : Blo 366759 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B550157 : Blo 366759 550157 := bbase (se 3 (by rfl) ⟨103154, by rfl⟩ : syracuseStep 550157 = 206309) (by norm_num)
theorem B550181 : Blo 366759 550181 := bbase (se 4 (by rfl) ⟨51579, by rfl⟩ : syracuseStep 550181 = 103159) (by norm_num)
theorem B845101 : Blo 366759 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B2647349 : Blo 366759 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B550205 : Blo 366759 550205 := bbase (se 3 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 550205 = 206327) (by norm_num)
theorem B550229 : Blo 366759 550229 := bbase (se 12 (by rfl) ⟨201, by rfl⟩ : syracuseStep 550229 = 403) (by norm_num)
theorem B550253 : Blo 366759 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B550277 : Blo 366759 550277 := bbase (se 4 (by rfl) ⟨51588, by rfl⟩ : syracuseStep 550277 = 103177) (by norm_num)
theorem B550301 : Blo 366759 550301 := bbase (se 3 (by rfl) ⟨103181, by rfl⟩ : syracuseStep 550301 = 206363) (by norm_num)
theorem B550325 : Blo 366759 550325 := bbase (se 5 (by rfl) ⟨25796, by rfl⟩ : syracuseStep 550325 = 51593) (by norm_num)
theorem B550349 : Blo 366759 550349 := bbase (se 3 (by rfl) ⟨103190, by rfl⟩ : syracuseStep 550349 = 206381) (by norm_num)
theorem B550373 : Blo 366759 550373 := bbase (se 4 (by rfl) ⟨51597, by rfl⟩ : syracuseStep 550373 = 103195) (by norm_num)
theorem B648685 : Blo 366759 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B550397 : Blo 366759 550397 := bbase (se 3 (by rfl) ⟨103199, by rfl⟩ : syracuseStep 550397 = 206399) (by norm_num)
theorem B550421 : Blo 366759 550421 := bbase (se 6 (by rfl) ⟨12900, by rfl⟩ : syracuseStep 550421 = 25801) (by norm_num)
theorem B550445 : Blo 366759 550445 := bbase (se 3 (by rfl) ⟨103208, by rfl⟩ : syracuseStep 550445 = 206417) (by norm_num)
theorem B550469 : Blo 366759 550469 := bbase (se 4 (by rfl) ⟨51606, by rfl⟩ : syracuseStep 550469 = 103213) (by norm_num)
theorem B1238597 : Blo 366759 1238597 := bbase (se 4 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 1238597 = 232237) (by norm_num)
theorem B2647637 : Blo 366759 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B550493 : Blo 366759 550493 := bbase (se 3 (by rfl) ⟨103217, by rfl⟩ : syracuseStep 550493 = 206435) (by norm_num)
theorem B550517 : Blo 366759 550517 := bbase (se 5 (by rfl) ⟨25805, by rfl⟩ : syracuseStep 550517 = 51611) (by norm_num)
theorem B2811509 : Blo 366759 2811509 := bbase (se 5 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 2811509 = 263579) (by norm_num)
theorem B550541 : Blo 366759 550541 := bbase (se 3 (by rfl) ⟨103226, by rfl⟩ : syracuseStep 550541 = 206453) (by norm_num)
theorem B419485 : Blo 366759 419485 := bbase (se 3 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 419485 = 157307) (by norm_num)
theorem B550565 : Blo 366759 550565 := bbase (se 4 (by rfl) ⟨51615, by rfl⟩ : syracuseStep 550565 = 103231) (by norm_num)
theorem B550589 : Blo 366759 550589 := bbase (se 3 (by rfl) ⟨103235, by rfl⟩ : syracuseStep 550589 = 206471) (by norm_num)
theorem B550613 : Blo 366759 550613 := bbase (se 7 (by rfl) ⟨6452, by rfl⟩ : syracuseStep 550613 = 12905) (by norm_num)
theorem B550637 : Blo 366759 550637 := bbase (se 3 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 550637 = 206489) (by norm_num)
theorem B550661 : Blo 366759 550661 := bbase (se 4 (by rfl) ⟨51624, by rfl⟩ : syracuseStep 550661 = 103249) (by norm_num)
theorem B550685 : Blo 366759 550685 := bbase (se 3 (by rfl) ⟨103253, by rfl⟩ : syracuseStep 550685 = 206507) (by norm_num)
theorem B550709 : Blo 366759 550709 := bbase (se 5 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 550709 = 51629) (by norm_num)
theorem B550733 : Blo 366759 550733 := bbase (se 3 (by rfl) ⟨103262, by rfl⟩ : syracuseStep 550733 = 206525) (by norm_num)
theorem B550757 : Blo 366759 550757 := bbase (se 4 (by rfl) ⟨51633, by rfl⟩ : syracuseStep 550757 = 103267) (by norm_num)
theorem B550781 : Blo 366759 550781 := bbase (se 3 (by rfl) ⟨103271, by rfl⟩ : syracuseStep 550781 = 206543) (by norm_num)
theorem B747397 : Blo 366759 747397 := bbase (se 4 (by rfl) ⟨70068, by rfl⟩ : syracuseStep 747397 = 140137) (by norm_num)
theorem B550805 : Blo 366759 550805 := bbase (se 6 (by rfl) ⟨12909, by rfl⟩ : syracuseStep 550805 = 25819) (by norm_num)
theorem B1861541 : Blo 366759 1861541 := bbase (se 4 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 1861541 = 349039) (by norm_num)
theorem B550829 : Blo 366759 550829 := bbase (se 3 (by rfl) ⟨103280, by rfl⟩ : syracuseStep 550829 = 206561) (by norm_num)
theorem B2090933 : Blo 366759 2090933 := bbase (se 5 (by rfl) ⟨98012, by rfl⟩ : syracuseStep 2090933 = 196025) (by norm_num)
theorem B550853 : Blo 366759 550853 := bbase (se 4 (by rfl) ⟨51642, by rfl⟩ : syracuseStep 550853 = 103285) (by norm_num)
theorem B550877 : Blo 366759 550877 := bbase (se 3 (by rfl) ⟨103289, by rfl⟩ : syracuseStep 550877 = 206579) (by norm_num)
theorem B1239029 : Blo 366759 1239029 := bbase (se 5 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 1239029 = 116159) (by norm_num)
theorem B550901 : Blo 366759 550901 := bbase (se 5 (by rfl) ⟨25823, by rfl⟩ : syracuseStep 550901 = 51647) (by norm_num)
theorem B550925 : Blo 366759 550925 := bbase (se 3 (by rfl) ⟨103298, by rfl⟩ : syracuseStep 550925 = 206597) (by norm_num)
theorem B550949 : Blo 366759 550949 := bbase (se 4 (by rfl) ⟨51651, by rfl⟩ : syracuseStep 550949 = 103303) (by norm_num)
theorem B550973 : Blo 366759 550973 := bbase (se 3 (by rfl) ⟨103307, by rfl⟩ : syracuseStep 550973 = 206615) (by norm_num)
theorem B550997 : Blo 366759 550997 := bbase (se 8 (by rfl) ⟨3228, by rfl⟩ : syracuseStep 550997 = 6457) (by norm_num)
theorem B419941 : Blo 366759 419941 := bbase (se 4 (by rfl) ⟨39369, by rfl⟩ : syracuseStep 419941 = 78739) (by norm_num)
theorem B551021 : Blo 366759 551021 := bbase (se 3 (by rfl) ⟨103316, by rfl⟩ : syracuseStep 551021 = 206633) (by norm_num)
theorem B551045 : Blo 366759 551045 := bbase (se 4 (by rfl) ⟨51660, by rfl⟩ : syracuseStep 551045 = 103321) (by norm_num)
theorem B2648213 : Blo 366759 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B551069 : Blo 366759 551069 := bbase (se 3 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 551069 = 206651) (by norm_num)
theorem B551093 : Blo 366759 551093 := bbase (se 5 (by rfl) ⟨25832, by rfl⟩ : syracuseStep 551093 = 51665) (by norm_num)
theorem B551117 : Blo 366759 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B551141 : Blo 366759 551141 := bbase (se 4 (by rfl) ⟨51669, by rfl⟩ : syracuseStep 551141 = 103339) (by norm_num)
theorem B551165 : Blo 366759 551165 := bbase (se 3 (by rfl) ⟨103343, by rfl⟩ : syracuseStep 551165 = 206687) (by norm_num)
theorem B551189 : Blo 366759 551189 := bbase (se 6 (by rfl) ⟨12918, by rfl⟩ : syracuseStep 551189 = 25837) (by norm_num)
theorem B551213 : Blo 366759 551213 := bbase (se 3 (by rfl) ⟨103352, by rfl⟩ : syracuseStep 551213 = 206705) (by norm_num)
theorem B1403189 : Blo 366759 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B551237 : Blo 366759 551237 := bbase (se 4 (by rfl) ⟨51678, by rfl⟩ : syracuseStep 551237 = 103357) (by norm_num)
theorem B551261 : Blo 366759 551261 := bbase (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) (by norm_num)
theorem B551285 : Blo 366759 551285 := bbase (se 5 (by rfl) ⟨25841, by rfl⟩ : syracuseStep 551285 = 51683) (by norm_num)
theorem B551309 : Blo 366759 551309 := bbase (se 3 (by rfl) ⟨103370, by rfl⟩ : syracuseStep 551309 = 206741) (by norm_num)
theorem B1239461 : Blo 366759 1239461 := bbase (se 4 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 1239461 = 232399) (by norm_num)
theorem B551333 : Blo 366759 551333 := bbase (se 4 (by rfl) ⟨51687, by rfl⟩ : syracuseStep 551333 = 103375) (by norm_num)
theorem B551357 : Blo 366759 551357 := bbase (se 3 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 551357 = 206759) (by norm_num)
theorem B551381 : Blo 366759 551381 := bbase (se 7 (by rfl) ⟨6461, by rfl⟩ : syracuseStep 551381 = 12923) (by norm_num)
theorem B551405 : Blo 366759 551405 := bbase (se 3 (by rfl) ⟨103388, by rfl⟩ : syracuseStep 551405 = 206777) (by norm_num)
theorem B551429 : Blo 366759 551429 := bbase (se 4 (by rfl) ⟨51696, by rfl⟩ : syracuseStep 551429 = 103393) (by norm_num)
theorem B551453 : Blo 366759 551453 := bbase (se 3 (by rfl) ⟨103397, by rfl⟩ : syracuseStep 551453 = 206795) (by norm_num)
theorem B551477 : Blo 366759 551477 := bbase (se 5 (by rfl) ⟨25850, by rfl⟩ : syracuseStep 551477 = 51701) (by norm_num)
theorem B551501 : Blo 366759 551501 := bbase (se 3 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 551501 = 206813) (by norm_num)
theorem B1403477 : Blo 366759 1403477 := bbase (se 8 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 1403477 = 16447) (by norm_num)
theorem B551525 : Blo 366759 551525 := bbase (se 4 (by rfl) ⟨51705, by rfl⟩ : syracuseStep 551525 = 103411) (by norm_num)
theorem B551549 : Blo 366759 551549 := bbase (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) (by norm_num)
theorem B551573 : Blo 366759 551573 := bbase (se 6 (by rfl) ⟨12927, by rfl⟩ : syracuseStep 551573 = 25855) (by norm_num)
theorem B551597 : Blo 366759 551597 := bbase (se 3 (by rfl) ⟨103424, by rfl⟩ : syracuseStep 551597 = 206849) (by norm_num)
theorem B1010357 : Blo 366759 1010357 := bbase (se 5 (by rfl) ⟨47360, by rfl⟩ : syracuseStep 1010357 = 94721) (by norm_num)
theorem B551621 : Blo 366759 551621 := bbase (se 4 (by rfl) ⟨51714, by rfl⟩ : syracuseStep 551621 = 103429) (by norm_num)
theorem B551645 : Blo 366759 551645 := bbase (se 3 (by rfl) ⟨103433, by rfl⟩ : syracuseStep 551645 = 206867) (by norm_num)
theorem B551669 : Blo 366759 551669 := bbase (se 5 (by rfl) ⟨25859, by rfl⟩ : syracuseStep 551669 = 51719) (by norm_num)
theorem B551693 : Blo 366759 551693 := bbase (se 3 (by rfl) ⟨103442, by rfl⟩ : syracuseStep 551693 = 206885) (by norm_num)
theorem B551717 : Blo 366759 551717 := bbase (se 4 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 551717 = 103447) (by norm_num)
theorem B551741 : Blo 366759 551741 := bbase (se 3 (by rfl) ⟨103451, by rfl⟩ : syracuseStep 551741 = 206903) (by norm_num)
theorem B1239893 : Blo 366759 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B551765 : Blo 366759 551765 := bbase (se 9 (by rfl) ⟨1616, by rfl⟩ : syracuseStep 551765 = 3233) (by norm_num)
theorem B551789 : Blo 366759 551789 := bbase (se 3 (by rfl) ⟨103460, by rfl⟩ : syracuseStep 551789 = 206921) (by norm_num)
theorem B551813 : Blo 366759 551813 := bbase (se 4 (by rfl) ⟨51732, by rfl⟩ : syracuseStep 551813 = 103465) (by norm_num)
theorem B551837 : Blo 366759 551837 := bbase (se 3 (by rfl) ⟨103469, by rfl⟩ : syracuseStep 551837 = 206939) (by norm_num)
theorem B1567669 : Blo 366759 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B551861 : Blo 366759 551861 := bbase (se 5 (by rfl) ⟨25868, by rfl⟩ : syracuseStep 551861 = 51737) (by norm_num)
theorem B551885 : Blo 366759 551885 := bbase (se 3 (by rfl) ⟨103478, by rfl⟩ : syracuseStep 551885 = 206957) (by norm_num)
theorem B551909 : Blo 366759 551909 := bbase (se 4 (by rfl) ⟨51741, by rfl⟩ : syracuseStep 551909 = 103483) (by norm_num)
theorem B388093 : Blo 366759 388093 := bbase (se 3 (by rfl) ⟨72767, by rfl⟩ : syracuseStep 388093 = 145535) (by norm_num)
theorem B551933 : Blo 366759 551933 := bbase (se 3 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 551933 = 206975) (by norm_num)
theorem B551957 : Blo 366759 551957 := bbase (se 6 (by rfl) ⟨12936, by rfl⟩ : syracuseStep 551957 = 25873) (by norm_num)
theorem B551981 : Blo 366759 551981 := bbase (se 3 (by rfl) ⟨103496, by rfl⟩ : syracuseStep 551981 = 206993) (by norm_num)
theorem B552005 : Blo 366759 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B552029 : Blo 366759 552029 := bbase (se 3 (by rfl) ⟨103505, by rfl⟩ : syracuseStep 552029 = 207011) (by norm_num)
theorem B748637 : Blo 366759 748637 := bbase (se 3 (by rfl) ⟨140369, by rfl⟩ : syracuseStep 748637 = 280739) (by norm_num)
theorem B552053 : Blo 366759 552053 := bbase (se 5 (by rfl) ⟨25877, by rfl⟩ : syracuseStep 552053 = 51755) (by norm_num)
theorem B552077 : Blo 366759 552077 := bbase (se 3 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 552077 = 207029) (by norm_num)
theorem B552101 : Blo 366759 552101 := bbase (se 4 (by rfl) ⟨51759, by rfl⟩ : syracuseStep 552101 = 103519) (by norm_num)
theorem B1862837 : Blo 366759 1862837 := bbase (se 5 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 1862837 = 174641) (by norm_num)
theorem B552125 : Blo 366759 552125 := bbase (se 3 (by rfl) ⟨103523, by rfl⟩ : syracuseStep 552125 = 207047) (by norm_num)
theorem B552149 : Blo 366759 552149 := bbase (se 7 (by rfl) ⟨6470, by rfl⟩ : syracuseStep 552149 = 12941) (by norm_num)
theorem B552173 : Blo 366759 552173 := bbase (se 3 (by rfl) ⟨103532, by rfl⟩ : syracuseStep 552173 = 207065) (by norm_num)
theorem B1240325 : Blo 366759 1240325 := bbase (se 4 (by rfl) ⟨116280, by rfl⟩ : syracuseStep 1240325 = 232561) (by norm_num)
theorem B552197 : Blo 366759 552197 := bbase (se 4 (by rfl) ⟨51768, by rfl⟩ : syracuseStep 552197 = 103537) (by norm_num)
theorem B1764629 : Blo 366759 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B3534101 : Blo 366759 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B552221 : Blo 366759 552221 := bbase (se 3 (by rfl) ⟨103541, by rfl⟩ : syracuseStep 552221 = 207083) (by norm_num)
theorem B552245 : Blo 366759 552245 := bbase (se 5 (by rfl) ⟨25886, by rfl⟩ : syracuseStep 552245 = 51773) (by norm_num)
theorem B552269 : Blo 366759 552269 := bbase (se 3 (by rfl) ⟨103550, by rfl⟩ : syracuseStep 552269 = 207101) (by norm_num)
theorem B552293 : Blo 366759 552293 := bbase (se 4 (by rfl) ⟨51777, by rfl⟩ : syracuseStep 552293 = 103555) (by norm_num)
theorem B552317 : Blo 366759 552317 := bbase (se 3 (by rfl) ⟨103559, by rfl⟩ : syracuseStep 552317 = 207119) (by norm_num)
theorem B552341 : Blo 366759 552341 := bbase (se 6 (by rfl) ⟨12945, by rfl⟩ : syracuseStep 552341 = 25891) (by norm_num)
theorem B552365 : Blo 366759 552365 := bbase (se 3 (by rfl) ⟨103568, by rfl⟩ : syracuseStep 552365 = 207137) (by norm_num)
theorem B552389 : Blo 366759 552389 := bbase (se 4 (by rfl) ⟨51786, by rfl⟩ : syracuseStep 552389 = 103573) (by norm_num)
theorem B552413 : Blo 366759 552413 := bbase (se 3 (by rfl) ⟨103577, by rfl⟩ : syracuseStep 552413 = 207155) (by norm_num)
theorem B552437 : Blo 366759 552437 := bbase (se 5 (by rfl) ⟨25895, by rfl⟩ : syracuseStep 552437 = 51791) (by norm_num)
theorem B552461 : Blo 366759 552461 := bbase (se 3 (by rfl) ⟨103586, by rfl⟩ : syracuseStep 552461 = 207173) (by norm_num)
theorem B552485 : Blo 366759 552485 := bbase (se 4 (by rfl) ⟨51795, by rfl⟩ : syracuseStep 552485 = 103591) (by norm_num)
theorem B552509 : Blo 366759 552509 := bbase (se 3 (by rfl) ⟨103595, by rfl⟩ : syracuseStep 552509 = 207191) (by norm_num)
theorem B552533 : Blo 366759 552533 := bbase (se 8 (by rfl) ⟨3237, by rfl⟩ : syracuseStep 552533 = 6475) (by norm_num)
theorem B552557 : Blo 366759 552557 := bbase (se 3 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 552557 = 207209) (by norm_num)
theorem B552581 : Blo 366759 552581 := bbase (se 4 (by rfl) ⟨51804, by rfl⟩ : syracuseStep 552581 = 103609) (by norm_num)
theorem B421529 : Blo 366759 421529 := bbase (se 2 (by rfl) ⟨158073, by rfl⟩ : syracuseStep 421529 = 316147) (by norm_num)
theorem B552605 : Blo 366759 552605 := bbase (se 3 (by rfl) ⟨103613, by rfl⟩ : syracuseStep 552605 = 207227) (by norm_num)
theorem B1240757 : Blo 366759 1240757 := bbase (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) (by norm_num)
theorem B552629 : Blo 366759 552629 := bbase (se 5 (by rfl) ⟨25904, by rfl⟩ : syracuseStep 552629 = 51809) (by norm_num)
theorem B552653 : Blo 366759 552653 := bbase (se 3 (by rfl) ⟨103622, by rfl⟩ : syracuseStep 552653 = 207245) (by norm_num)
theorem B552677 : Blo 366759 552677 := bbase (se 4 (by rfl) ⟨51813, by rfl⟩ : syracuseStep 552677 = 103627) (by norm_num)
theorem B1404661 : Blo 366759 1404661 := bbase (se 5 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 1404661 = 131687) (by norm_num)
theorem B552701 : Blo 366759 552701 := bbase (se 3 (by rfl) ⟨103631, by rfl⟩ : syracuseStep 552701 = 207263) (by norm_num)
theorem B552725 : Blo 366759 552725 := bbase (se 6 (by rfl) ⟨12954, by rfl⟩ : syracuseStep 552725 = 25909) (by norm_num)
theorem B552749 : Blo 366759 552749 := bbase (se 3 (by rfl) ⟨103640, by rfl⟩ : syracuseStep 552749 = 207281) (by norm_num)
theorem B552773 : Blo 366759 552773 := bbase (se 4 (by rfl) ⟨51822, by rfl⟩ : syracuseStep 552773 = 103645) (by norm_num)
theorem B552797 : Blo 366759 552797 := bbase (se 3 (by rfl) ⟨103649, by rfl⟩ : syracuseStep 552797 = 207299) (by norm_num)
theorem B552821 : Blo 366759 552821 := bbase (se 5 (by rfl) ⟨25913, by rfl⟩ : syracuseStep 552821 = 51827) (by norm_num)
theorem B552845 : Blo 366759 552845 := bbase (se 3 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 552845 = 207317) (by norm_num)
theorem B716701 : Blo 366759 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B552869 : Blo 366759 552869 := bbase (se 4 (by rfl) ⟨51831, by rfl⟩ : syracuseStep 552869 = 103663) (by norm_num)
theorem B552893 : Blo 366759 552893 := bbase (se 3 (by rfl) ⟨103667, by rfl⟩ : syracuseStep 552893 = 207335) (by norm_num)
theorem B552917 : Blo 366759 552917 := bbase (se 7 (by rfl) ⟨6479, by rfl⟩ : syracuseStep 552917 = 12959) (by norm_num)
theorem B552941 : Blo 366759 552941 := bbase (se 3 (by rfl) ⟨103676, by rfl⟩ : syracuseStep 552941 = 207353) (by norm_num)
theorem B552965 : Blo 366759 552965 := bbase (se 4 (by rfl) ⟨51840, by rfl⟩ : syracuseStep 552965 = 103681) (by norm_num)
theorem B1175573 : Blo 366759 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B552989 : Blo 366759 552989 := bbase (se 3 (by rfl) ⟨103685, by rfl⟩ : syracuseStep 552989 = 207371) (by norm_num)
theorem B1404965 : Blo 366759 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B553013 : Blo 366759 553013 := bbase (se 5 (by rfl) ⟨25922, by rfl⟩ : syracuseStep 553013 = 51845) (by norm_num)
theorem B454717 : Blo 366759 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B553037 : Blo 366759 553037 := bbase (se 3 (by rfl) ⟨103694, by rfl⟩ : syracuseStep 553037 = 207389) (by norm_num)
theorem B2093141 : Blo 366759 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1241189 : Blo 366759 1241189 := bbase (se 4 (by rfl) ⟨116361, by rfl⟩ : syracuseStep 1241189 = 232723) (by norm_num)
theorem B553061 : Blo 366759 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B553085 : Blo 366759 553085 := bbase (se 3 (by rfl) ⟨103703, by rfl⟩ : syracuseStep 553085 = 207407) (by norm_num)
theorem B422021 : Blo 366759 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B553109 : Blo 366759 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B553133 : Blo 366759 553133 := bbase (se 3 (by rfl) ⟨103712, by rfl⟩ : syracuseStep 553133 = 207425) (by norm_num)
theorem B1896629 : Blo 366759 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B553157 : Blo 366759 553157 := bbase (se 4 (by rfl) ⟨51858, by rfl⟩ : syracuseStep 553157 = 103717) (by norm_num)
theorem B553181 : Blo 366759 553181 := bbase (se 3 (by rfl) ⟨103721, by rfl⟩ : syracuseStep 553181 = 207443) (by norm_num)
theorem B553205 : Blo 366759 553205 := bbase (se 5 (by rfl) ⟨25931, by rfl⟩ : syracuseStep 553205 = 51863) (by norm_num)
theorem B553229 : Blo 366759 553229 := bbase (se 3 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 553229 = 207461) (by norm_num)
theorem B553253 : Blo 366759 553253 := bbase (se 4 (by rfl) ⟨51867, by rfl⟩ : syracuseStep 553253 = 103735) (by norm_num)
theorem B553277 : Blo 366759 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B553301 : Blo 366759 553301 := bbase (se 10 (by rfl) ⟨810, by rfl⟩ : syracuseStep 553301 = 1621) (by norm_num)
theorem B3993941 : Blo 366759 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B553325 : Blo 366759 553325 := bbase (se 3 (by rfl) ⟨103748, by rfl⟩ : syracuseStep 553325 = 207497) (by norm_num)
theorem B553349 : Blo 366759 553349 := bbase (se 4 (by rfl) ⟨51876, by rfl⟩ : syracuseStep 553349 = 103753) (by norm_num)
theorem B2355605 : Blo 366759 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B553373 : Blo 366759 553373 := bbase (se 3 (by rfl) ⟨103757, by rfl⟩ : syracuseStep 553373 = 207515) (by norm_num)
theorem B553397 : Blo 366759 553397 := bbase (se 5 (by rfl) ⟨25940, by rfl⟩ : syracuseStep 553397 = 51881) (by norm_num)
theorem B618941 : Blo 366759 618941 := bbase (se 3 (by rfl) ⟨116051, by rfl⟩ : syracuseStep 618941 = 232103) (by norm_num)
theorem B1864133 : Blo 366759 1864133 := bbase (se 4 (by rfl) ⟨174762, by rfl⟩ : syracuseStep 1864133 = 349525) (by norm_num)
theorem B553421 : Blo 366759 553421 := bbase (se 3 (by rfl) ⟨103766, by rfl⟩ : syracuseStep 553421 = 207533) (by norm_num)
theorem B553445 : Blo 366759 553445 := bbase (se 4 (by rfl) ⟨51885, by rfl⟩ : syracuseStep 553445 = 103771) (by norm_num)
theorem B553469 : Blo 366759 553469 := bbase (se 3 (by rfl) ⟨103775, by rfl⟩ : syracuseStep 553469 = 207551) (by norm_num)
theorem B1241621 : Blo 366759 1241621 := bbase (se 6 (by rfl) ⟨29100, by rfl⟩ : syracuseStep 1241621 = 58201) (by norm_num)
theorem B553493 : Blo 366759 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B553517 : Blo 366759 553517 := bbase (se 3 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 553517 = 207569) (by norm_num)
theorem B3600949 : Blo 366759 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B619069 : Blo 366759 619069 := bbase (se 3 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 619069 = 232151) (by norm_num)
theorem B553541 : Blo 366759 553541 := bbase (se 4 (by rfl) ⟨51894, by rfl⟩ : syracuseStep 553541 = 103789) (by norm_num)
theorem B553565 : Blo 366759 553565 := bbase (se 3 (by rfl) ⟨103793, by rfl⟩ : syracuseStep 553565 = 207587) (by norm_num)
theorem B553589 : Blo 366759 553589 := bbase (se 5 (by rfl) ⟨25949, by rfl⟩ : syracuseStep 553589 = 51899) (by norm_num)
theorem B553613 : Blo 366759 553613 := bbase (se 3 (by rfl) ⟨103802, by rfl⟩ : syracuseStep 553613 = 207605) (by norm_num)
theorem B619157 : Blo 366759 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B553637 : Blo 366759 553637 := bbase (se 4 (by rfl) ⟨51903, by rfl⟩ : syracuseStep 553637 = 103807) (by norm_num)
theorem B553661 : Blo 366759 553661 := bbase (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) (by norm_num)
theorem B553685 : Blo 366759 553685 := bbase (se 7 (by rfl) ⟨6488, by rfl⟩ : syracuseStep 553685 = 12977) (by norm_num)
theorem B553709 : Blo 366759 553709 := bbase (se 3 (by rfl) ⟨103820, by rfl⟩ : syracuseStep 553709 = 207641) (by norm_num)
theorem B3764981 : Blo 366759 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B553733 : Blo 366759 553733 := bbase (se 4 (by rfl) ⟨51912, by rfl⟩ : syracuseStep 553733 = 103825) (by norm_num)
theorem B619285 : Blo 366759 619285 := bbase (se 6 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 619285 = 29029) (by norm_num)
theorem B553757 : Blo 366759 553757 := bbase (se 3 (by rfl) ⟨103829, by rfl⟩ : syracuseStep 553757 = 207659) (by norm_num)
theorem B553781 : Blo 366759 553781 := bbase (se 5 (by rfl) ⟨25958, by rfl⟩ : syracuseStep 553781 = 51917) (by norm_num)
theorem B750389 : Blo 366759 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B553805 : Blo 366759 553805 := bbase (se 3 (by rfl) ⟨103838, by rfl⟩ : syracuseStep 553805 = 207677) (by norm_num)
theorem B553829 : Blo 366759 553829 := bbase (se 4 (by rfl) ⟨51921, by rfl⟩ : syracuseStep 553829 = 103843) (by norm_num)
theorem B619373 : Blo 366759 619373 := bbase (se 3 (by rfl) ⟨116132, by rfl⟩ : syracuseStep 619373 = 232265) (by norm_num)
theorem B553853 : Blo 366759 553853 := bbase (se 3 (by rfl) ⟨103847, by rfl⟩ : syracuseStep 553853 = 207695) (by norm_num)
theorem B553877 : Blo 366759 553877 := bbase (se 6 (by rfl) ⟨12981, by rfl⟩ : syracuseStep 553877 = 25963) (by norm_num)
theorem B553901 : Blo 366759 553901 := bbase (se 3 (by rfl) ⟨103856, by rfl⟩ : syracuseStep 553901 = 207713) (by norm_num)
theorem B1242053 : Blo 366759 1242053 := bbase (se 4 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 1242053 = 232885) (by norm_num)
theorem B553925 : Blo 366759 553925 := bbase (se 4 (by rfl) ⟨51930, by rfl⟩ : syracuseStep 553925 = 103861) (by norm_num)
theorem B553949 : Blo 366759 553949 := bbase (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) (by norm_num)
theorem B1045477 : Blo 366759 1045477 := bbase (se 4 (by rfl) ⟨98013, by rfl⟩ : syracuseStep 1045477 = 196027) (by norm_num)
theorem B619501 : Blo 366759 619501 := bbase (se 3 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 619501 = 232313) (by norm_num)
theorem B553973 : Blo 366759 553973 := bbase (se 5 (by rfl) ⟨25967, by rfl⟩ : syracuseStep 553973 = 51935) (by norm_num)
theorem B553997 : Blo 366759 553997 := bbase (se 3 (by rfl) ⟨103874, by rfl⟩ : syracuseStep 553997 = 207749) (by norm_num)
theorem B554021 : Blo 366759 554021 := bbase (se 4 (by rfl) ⟨51939, by rfl⟩ : syracuseStep 554021 = 103879) (by norm_num)
theorem B554045 : Blo 366759 554045 := bbase (se 3 (by rfl) ⟨103883, by rfl⟩ : syracuseStep 554045 = 207767) (by norm_num)
theorem B619589 : Blo 366759 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B554069 : Blo 366759 554069 := bbase (se 8 (by rfl) ⟨3246, by rfl⟩ : syracuseStep 554069 = 6493) (by norm_num)
theorem B554093 : Blo 366759 554093 := bbase (se 3 (by rfl) ⟨103892, by rfl⟩ : syracuseStep 554093 = 207785) (by norm_num)
theorem B554117 : Blo 366759 554117 := bbase (se 4 (by rfl) ⟨51948, by rfl⟩ : syracuseStep 554117 = 103897) (by norm_num)
theorem B554141 : Blo 366759 554141 := bbase (se 3 (by rfl) ⟨103901, by rfl⟩ : syracuseStep 554141 = 207803) (by norm_num)
theorem B554165 : Blo 366759 554165 := bbase (se 5 (by rfl) ⟨25976, by rfl⟩ : syracuseStep 554165 = 51953) (by norm_num)
theorem B619717 : Blo 366759 619717 := bbase (se 4 (by rfl) ⟨58098, by rfl⟩ : syracuseStep 619717 = 116197) (by norm_num)
theorem B554189 : Blo 366759 554189 := bbase (se 3 (by rfl) ⟨103910, by rfl⟩ : syracuseStep 554189 = 207821) (by norm_num)
theorem B554213 : Blo 366759 554213 := bbase (se 4 (by rfl) ⟨51957, by rfl⟩ : syracuseStep 554213 = 103915) (by norm_num)
theorem B554237 : Blo 366759 554237 := bbase (se 3 (by rfl) ⟨103919, by rfl⟩ : syracuseStep 554237 = 207839) (by norm_num)
theorem B554261 : Blo 366759 554261 := bbase (se 6 (by rfl) ⟨12990, by rfl⟩ : syracuseStep 554261 = 25981) (by norm_num)
theorem B619805 : Blo 366759 619805 := bbase (se 3 (by rfl) ⟨116213, by rfl⟩ : syracuseStep 619805 = 232427) (by norm_num)
theorem B1176869 : Blo 366759 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B554285 : Blo 366759 554285 := bbase (se 3 (by rfl) ⟨103928, by rfl⟩ : syracuseStep 554285 = 207857) (by norm_num)
theorem B554309 : Blo 366759 554309 := bbase (se 4 (by rfl) ⟨51966, by rfl⟩ : syracuseStep 554309 = 103933) (by norm_num)
theorem B554333 : Blo 366759 554333 := bbase (se 3 (by rfl) ⟨103937, by rfl⟩ : syracuseStep 554333 = 207875) (by norm_num)
theorem B750941 : Blo 366759 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B1242485 : Blo 366759 1242485 := bbase (se 5 (by rfl) ⟨58241, by rfl⟩ : syracuseStep 1242485 = 116483) (by norm_num)
theorem B554357 : Blo 366759 554357 := bbase (se 5 (by rfl) ⟨25985, by rfl⟩ : syracuseStep 554357 = 51971) (by norm_num)
theorem B554381 : Blo 366759 554381 := bbase (se 3 (by rfl) ⟨103946, by rfl⟩ : syracuseStep 554381 = 207893) (by norm_num)
theorem B619933 : Blo 366759 619933 := bbase (se 3 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 619933 = 232475) (by norm_num)
theorem B554405 : Blo 366759 554405 := bbase (se 4 (by rfl) ⟨51975, by rfl⟩ : syracuseStep 554405 = 103951) (by norm_num)
theorem B554429 : Blo 366759 554429 := bbase (se 3 (by rfl) ⟨103955, by rfl⟩ : syracuseStep 554429 = 207911) (by norm_num)
theorem B554453 : Blo 366759 554453 := bbase (se 7 (by rfl) ⟨6497, by rfl⟩ : syracuseStep 554453 = 12995) (by norm_num)
theorem B554477 : Blo 366759 554477 := bbase (se 3 (by rfl) ⟨103964, by rfl⟩ : syracuseStep 554477 = 207929) (by norm_num)
theorem B620021 : Blo 366759 620021 := bbase (se 5 (by rfl) ⟨29063, by rfl⟩ : syracuseStep 620021 = 58127) (by norm_num)
theorem B554501 : Blo 366759 554501 := bbase (se 4 (by rfl) ⟨51984, by rfl⟩ : syracuseStep 554501 = 103969) (by norm_num)
theorem B554525 : Blo 366759 554525 := bbase (se 3 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 554525 = 207947) (by norm_num)
theorem B554549 : Blo 366759 554549 := bbase (se 5 (by rfl) ⟨25994, by rfl⟩ : syracuseStep 554549 = 51989) (by norm_num)
theorem B554573 : Blo 366759 554573 := bbase (se 3 (by rfl) ⟨103982, by rfl⟩ : syracuseStep 554573 = 207965) (by norm_num)
theorem B554597 : Blo 366759 554597 := bbase (se 4 (by rfl) ⟨51993, by rfl⟩ : syracuseStep 554597 = 103987) (by norm_num)
theorem B783989 : Blo 366759 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B620149 : Blo 366759 620149 := bbase (se 5 (by rfl) ⟨29069, by rfl⟩ : syracuseStep 620149 = 58139) (by norm_num)
theorem B554621 : Blo 366759 554621 := bbase (se 3 (by rfl) ⟨103991, by rfl⟩ : syracuseStep 554621 = 207983) (by norm_num)
theorem B554645 : Blo 366759 554645 := bbase (se 6 (by rfl) ⟨12999, by rfl⟩ : syracuseStep 554645 = 25999) (by norm_num)
theorem B554669 : Blo 366759 554669 := bbase (se 3 (by rfl) ⟨104000, by rfl⟩ : syracuseStep 554669 = 208001) (by norm_num)
theorem B554693 : Blo 366759 554693 := bbase (se 4 (by rfl) ⟨52002, by rfl⟩ : syracuseStep 554693 = 104005) (by norm_num)
theorem B620237 : Blo 366759 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B1865429 : Blo 366759 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B554717 : Blo 366759 554717 := bbase (se 3 (by rfl) ⟨104009, by rfl⟩ : syracuseStep 554717 = 208019) (by norm_num)
theorem B554741 : Blo 366759 554741 := bbase (se 5 (by rfl) ⟨26003, by rfl⟩ : syracuseStep 554741 = 52007) (by norm_num)
theorem B554765 : Blo 366759 554765 := bbase (se 3 (by rfl) ⟨104018, by rfl⟩ : syracuseStep 554765 = 208037) (by norm_num)
theorem B1242917 : Blo 366759 1242917 := bbase (se 4 (by rfl) ⟨116523, by rfl⟩ : syracuseStep 1242917 = 233047) (by norm_num)
theorem B554789 : Blo 366759 554789 := bbase (se 4 (by rfl) ⟨52011, by rfl⟩ : syracuseStep 554789 = 104023) (by norm_num)
theorem B554813 : Blo 366759 554813 := bbase (se 3 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 554813 = 208055) (by norm_num)
theorem B620365 : Blo 366759 620365 := bbase (se 3 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 620365 = 232637) (by norm_num)
theorem B554837 : Blo 366759 554837 := bbase (se 9 (by rfl) ⟨1625, by rfl⟩ : syracuseStep 554837 = 3251) (by norm_num)
theorem B1570661 : Blo 366759 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B784237 : Blo 366759 784237 := bbase (se 3 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 784237 = 294089) (by norm_num)
theorem B554861 : Blo 366759 554861 := bbase (se 3 (by rfl) ⟨104036, by rfl⟩ : syracuseStep 554861 = 208073) (by norm_num)
theorem B554885 : Blo 366759 554885 := bbase (se 4 (by rfl) ⟨52020, by rfl⟩ : syracuseStep 554885 = 104041) (by norm_num)
theorem B554909 : Blo 366759 554909 := bbase (se 3 (by rfl) ⟨104045, by rfl⟩ : syracuseStep 554909 = 208091) (by norm_num)
theorem B620453 : Blo 366759 620453 := bbase (se 4 (by rfl) ⟨58167, by rfl⟩ : syracuseStep 620453 = 116335) (by norm_num)
theorem B554933 : Blo 366759 554933 := bbase (se 5 (by rfl) ⟨26012, by rfl⟩ : syracuseStep 554933 = 52025) (by norm_num)
theorem B554957 : Blo 366759 554957 := bbase (se 3 (by rfl) ⟨104054, by rfl⟩ : syracuseStep 554957 = 208109) (by norm_num)
theorem B554981 : Blo 366759 554981 := bbase (se 4 (by rfl) ⟨52029, by rfl⟩ : syracuseStep 554981 = 104059) (by norm_num)
theorem B555005 : Blo 366759 555005 := bbase (se 3 (by rfl) ⟨104063, by rfl⟩ : syracuseStep 555005 = 208127) (by norm_num)
theorem B555029 : Blo 366759 555029 := bbase (se 6 (by rfl) ⟨13008, by rfl⟩ : syracuseStep 555029 = 26017) (by norm_num)
theorem B620581 : Blo 366759 620581 := bbase (se 4 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 620581 = 116359) (by norm_num)
theorem B555053 : Blo 366759 555053 := bbase (se 3 (by rfl) ⟨104072, by rfl⟩ : syracuseStep 555053 = 208145) (by norm_num)
theorem B555077 : Blo 366759 555077 := bbase (se 4 (by rfl) ⟨52038, by rfl⟩ : syracuseStep 555077 = 104077) (by norm_num)
theorem B555101 : Blo 366759 555101 := bbase (se 3 (by rfl) ⟨104081, by rfl⟩ : syracuseStep 555101 = 208163) (by norm_num)
theorem B1407077 : Blo 366759 1407077 := bbase (se 4 (by rfl) ⟨131913, by rfl⟩ : syracuseStep 1407077 = 263827) (by norm_num)
theorem B555125 : Blo 366759 555125 := bbase (se 5 (by rfl) ⟨26021, by rfl⟩ : syracuseStep 555125 = 52043) (by norm_num)
theorem B620669 : Blo 366759 620669 := bbase (se 3 (by rfl) ⟨116375, by rfl⟩ : syracuseStep 620669 = 232751) (by norm_num)
theorem B555149 : Blo 366759 555149 := bbase (se 3 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 555149 = 208181) (by norm_num)
theorem B522397 : Blo 366759 522397 := bbase (se 3 (by rfl) ⟨97949, by rfl⟩ : syracuseStep 522397 = 195899) (by norm_num)
theorem B555173 : Blo 366759 555173 := bbase (se 4 (by rfl) ⟨52047, by rfl⟩ : syracuseStep 555173 = 104095) (by norm_num)
theorem B555197 : Blo 366759 555197 := bbase (se 3 (by rfl) ⟨104099, by rfl⟩ : syracuseStep 555197 = 208199) (by norm_num)
theorem B1243349 : Blo 366759 1243349 := bbase (se 7 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 1243349 = 29141) (by norm_num)
theorem B555221 : Blo 366759 555221 := bbase (se 7 (by rfl) ⟨6506, by rfl⟩ : syracuseStep 555221 = 13013) (by norm_num)
theorem B555245 : Blo 366759 555245 := bbase (se 3 (by rfl) ⟨104108, by rfl⟩ : syracuseStep 555245 = 208217) (by norm_num)
theorem B620797 : Blo 366759 620797 := bbase (se 3 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 620797 = 232799) (by norm_num)
theorem B555269 : Blo 366759 555269 := bbase (se 4 (by rfl) ⟨52056, by rfl⟩ : syracuseStep 555269 = 104113) (by norm_num)
theorem B555293 : Blo 366759 555293 := bbase (se 3 (by rfl) ⟨104117, by rfl⟩ : syracuseStep 555293 = 208235) (by norm_num)
theorem B555317 : Blo 366759 555317 := bbase (se 5 (by rfl) ⟨26030, by rfl⟩ : syracuseStep 555317 = 52061) (by norm_num)
theorem B555341 : Blo 366759 555341 := bbase (se 3 (by rfl) ⟨104126, by rfl⟩ : syracuseStep 555341 = 208253) (by norm_num)
theorem B620885 : Blo 366759 620885 := bbase (se 10 (by rfl) ⟨909, by rfl⟩ : syracuseStep 620885 = 1819) (by norm_num)
theorem B784741 : Blo 366759 784741 := bbase (se 4 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 784741 = 147139) (by norm_num)
theorem B555365 : Blo 366759 555365 := bbase (se 4 (by rfl) ⟨52065, by rfl⟩ : syracuseStep 555365 = 104131) (by norm_num)
theorem B555389 : Blo 366759 555389 := bbase (se 3 (by rfl) ⟨104135, by rfl⟩ : syracuseStep 555389 = 208271) (by norm_num)
theorem B1407365 : Blo 366759 1407365 := bbase (se 4 (by rfl) ⟨131940, by rfl⟩ : syracuseStep 1407365 = 263881) (by norm_num)
theorem B555413 : Blo 366759 555413 := bbase (se 6 (by rfl) ⟨13017, by rfl⟩ : syracuseStep 555413 = 26035) (by norm_num)
theorem B588197 : Blo 366759 588197 := bbase (se 4 (by rfl) ⟨55143, by rfl⟩ : syracuseStep 588197 = 110287) (by norm_num)
theorem B555437 : Blo 366759 555437 := bbase (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) (by norm_num)
theorem B1046981 : Blo 366759 1046981 := bbase (se 4 (by rfl) ⟨98154, by rfl⟩ : syracuseStep 1046981 = 196309) (by norm_num)
theorem B555461 : Blo 366759 555461 := bbase (se 4 (by rfl) ⟨52074, by rfl⟩ : syracuseStep 555461 = 104149) (by norm_num)
theorem B621013 : Blo 366759 621013 := bbase (se 7 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 621013 = 14555) (by norm_num)
theorem B555485 : Blo 366759 555485 := bbase (se 3 (by rfl) ⟨104153, by rfl⟩ : syracuseStep 555485 = 208307) (by norm_num)
theorem B555509 : Blo 366759 555509 := bbase (se 5 (by rfl) ⟨26039, by rfl⟩ : syracuseStep 555509 = 52079) (by norm_num)
theorem B555533 : Blo 366759 555533 := bbase (se 3 (by rfl) ⟨104162, by rfl⟩ : syracuseStep 555533 = 208325) (by norm_num)
theorem B883237 : Blo 366759 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B555557 : Blo 366759 555557 := bbase (se 4 (by rfl) ⟨52083, by rfl⟩ : syracuseStep 555557 = 104167) (by norm_num)
theorem B391721 : Blo 366759 391721 := bbase (se 2 (by rfl) ⟨146895, by rfl⟩ : syracuseStep 391721 = 293791) (by norm_num)
theorem B621101 : Blo 366759 621101 := bbase (se 3 (by rfl) ⟨116456, by rfl⟩ : syracuseStep 621101 = 232913) (by norm_num)
theorem B555581 : Blo 366759 555581 := bbase (se 3 (by rfl) ⟨104171, by rfl⟩ : syracuseStep 555581 = 208343) (by norm_num)
theorem B555605 : Blo 366759 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B555629 : Blo 366759 555629 := bbase (se 3 (by rfl) ⟨104180, by rfl⟩ : syracuseStep 555629 = 208361) (by norm_num)
theorem B1243781 : Blo 366759 1243781 := bbase (se 4 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 1243781 = 233209) (by norm_num)
theorem B555653 : Blo 366759 555653 := bbase (se 4 (by rfl) ⟨52092, by rfl⟩ : syracuseStep 555653 = 104185) (by norm_num)
theorem B5307029 : Blo 366759 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B555677 : Blo 366759 555677 := bbase (se 3 (by rfl) ⟨104189, by rfl⟩ : syracuseStep 555677 = 208379) (by norm_num)
theorem B621229 : Blo 366759 621229 := bbase (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) (by norm_num)
theorem B555701 : Blo 366759 555701 := bbase (se 5 (by rfl) ⟨26048, by rfl⟩ : syracuseStep 555701 = 52097) (by norm_num)
theorem B555725 : Blo 366759 555725 := bbase (se 3 (by rfl) ⟨104198, by rfl⟩ : syracuseStep 555725 = 208397) (by norm_num)
theorem B555749 : Blo 366759 555749 := bbase (se 4 (by rfl) ⟨52101, by rfl⟩ : syracuseStep 555749 = 104203) (by norm_num)
theorem B555773 : Blo 366759 555773 := bbase (se 3 (by rfl) ⟨104207, by rfl⟩ : syracuseStep 555773 = 208415) (by norm_num)
theorem B621317 : Blo 366759 621317 := bbase (se 4 (by rfl) ⟨58248, by rfl⟩ : syracuseStep 621317 = 116497) (by norm_num)
theorem B4193045 : Blo 366759 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B555797 : Blo 366759 555797 := bbase (se 6 (by rfl) ⟨13026, by rfl⟩ : syracuseStep 555797 = 26053) (by norm_num)
theorem B391969 : Blo 366759 391969 := bbase (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) (by norm_num)
theorem B555821 : Blo 366759 555821 := bbase (se 3 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 555821 = 208433) (by norm_num)
theorem B555845 : Blo 366759 555845 := bbase (se 4 (by rfl) ⟨52110, by rfl⟩ : syracuseStep 555845 = 104221) (by norm_num)
theorem B1571669 : Blo 366759 1571669 := bbase (se 9 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 1571669 = 9209) (by norm_num)
theorem B555869 : Blo 366759 555869 := bbase (se 3 (by rfl) ⟨104225, by rfl⟩ : syracuseStep 555869 = 208451) (by norm_num)
theorem B555893 : Blo 366759 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B621445 : Blo 366759 621445 := bbase (se 4 (by rfl) ⟨58260, by rfl⟩ : syracuseStep 621445 = 116521) (by norm_num)
theorem B555917 : Blo 366759 555917 := bbase (se 3 (by rfl) ⟨104234, by rfl⟩ : syracuseStep 555917 = 208469) (by norm_num)
theorem B555941 : Blo 366759 555941 := bbase (se 4 (by rfl) ⟨52119, by rfl⟩ : syracuseStep 555941 = 104239) (by norm_num)
theorem B523189 : Blo 366759 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B555965 : Blo 366759 555965 := bbase (se 3 (by rfl) ⟨104243, by rfl⟩ : syracuseStep 555965 = 208487) (by norm_num)
theorem B555989 : Blo 366759 555989 := bbase (se 7 (by rfl) ⟨6515, by rfl⟩ : syracuseStep 555989 = 13031) (by norm_num)
theorem B621533 : Blo 366759 621533 := bbase (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) (by norm_num)
theorem B1866725 : Blo 366759 1866725 := bbase (se 4 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 1866725 = 350011) (by norm_num)
theorem B556013 : Blo 366759 556013 := bbase (se 3 (by rfl) ⟨104252, by rfl⟩ : syracuseStep 556013 = 208505) (by norm_num)
theorem B556037 : Blo 366759 556037 := bbase (se 4 (by rfl) ⟨52128, by rfl⟩ : syracuseStep 556037 = 104257) (by norm_num)
theorem B556061 : Blo 366759 556061 := bbase (se 3 (by rfl) ⟨104261, by rfl⟩ : syracuseStep 556061 = 208523) (by norm_num)
theorem B588845 : Blo 366759 588845 := bbase (se 3 (by rfl) ⟨110408, by rfl⟩ : syracuseStep 588845 = 220817) (by norm_num)
theorem B1244213 : Blo 366759 1244213 := bbase (se 5 (by rfl) ⟨58322, by rfl⟩ : syracuseStep 1244213 = 116645) (by norm_num)
theorem B556085 : Blo 366759 556085 := bbase (se 5 (by rfl) ⟨26066, by rfl⟩ : syracuseStep 556085 = 52133) (by norm_num)
theorem B556109 : Blo 366759 556109 := bbase (se 3 (by rfl) ⟨104270, by rfl⟩ : syracuseStep 556109 = 208541) (by norm_num)
theorem B621661 : Blo 366759 621661 := bbase (se 3 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 621661 = 233123) (by norm_num)
theorem B1178725 : Blo 366759 1178725 := bbase (se 4 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 1178725 = 221011) (by norm_num)
theorem B1768549 : Blo 366759 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B556133 : Blo 366759 556133 := bbase (se 4 (by rfl) ⟨52137, by rfl⟩ : syracuseStep 556133 = 104275) (by norm_num)
theorem B621749 : Blo 366759 621749 := bbase (se 5 (by rfl) ⟨29144, by rfl⟩ : syracuseStep 621749 = 58289) (by norm_num)
theorem B1408213 : Blo 366759 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B392413 : Blo 366759 392413 := bbase (se 3 (by rfl) ⟨73577, by rfl⟩ : syracuseStep 392413 = 147155) (by norm_num)
theorem B785629 : Blo 366759 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B523525 : Blo 366759 523525 := bbase (se 4 (by rfl) ⟨49080, by rfl⟩ : syracuseStep 523525 = 98161) (by norm_num)
theorem B392473 : Blo 366759 392473 := bbase (se 2 (by rfl) ⟨147177, by rfl⟩ : syracuseStep 392473 = 294355) (by norm_num)
theorem B621877 : Blo 366759 621877 := bbase (se 5 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 621877 = 58301) (by norm_num)
theorem B621965 : Blo 366759 621965 := bbase (se 3 (by rfl) ⟨116618, by rfl⟩ : syracuseStep 621965 = 233237) (by norm_num)
theorem B523741 : Blo 366759 523741 := bbase (se 3 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 523741 = 196403) (by norm_num)
theorem B1244645 : Blo 366759 1244645 := bbase (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) (by norm_num)
theorem B622093 : Blo 366759 622093 := bbase (se 3 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 622093 = 233285) (by norm_num)
theorem B392789 : Blo 366759 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B622181 : Blo 366759 622181 := bbase (se 4 (by rfl) ⟨58329, by rfl⟩ : syracuseStep 622181 = 116659) (by norm_num)
theorem B786125 : Blo 366759 786125 := bbase (se 3 (by rfl) ⟨147398, by rfl⟩ : syracuseStep 786125 = 294797) (by norm_num)
theorem B884429 : Blo 366759 884429 := bbase (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) (by norm_num)
theorem B622309 : Blo 366759 622309 := bbase (se 4 (by rfl) ⟨58341, by rfl⟩ : syracuseStep 622309 = 116683) (by norm_num)
theorem B622397 : Blo 366759 622397 := bbase (se 3 (by rfl) ⟨116699, by rfl⟩ : syracuseStep 622397 = 233399) (by norm_num)
theorem B524117 : Blo 366759 524117 := bbase (se 9 (by rfl) ⟨1535, by rfl⟩ : syracuseStep 524117 = 3071) (by norm_num)
theorem B884621 : Blo 366759 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B1245077 : Blo 366759 1245077 := bbase (se 6 (by rfl) ⟨29181, by rfl⟩ : syracuseStep 1245077 = 58363) (by norm_num)
theorem B622525 : Blo 366759 622525 := bbase (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) (by norm_num)
theorem B1048565 : Blo 366759 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B786449 : Blo 366759 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B1048621 : Blo 366759 1048621 := bstep (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) B393233
theorem B1245293 : Blo 366759 1245293 := bstep (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) B466985
theorem B622721 : Blo 366759 622721 := bstep (se 2 (by rfl) ⟨233520, by rfl⟩ : syracuseStep 622721 = 467041) B467041
theorem B884881 : Blo 366759 884881 := bstep (se 2 (by rfl) ⟨331830, by rfl⟩ : syracuseStep 884881 = 663661) B663661
theorem B1245347 : Blo 366759 1245347 := bstep (se 1 (by rfl) ⟨934010, by rfl⟩ : syracuseStep 1245347 = 1868021) B1868021
theorem B1048781 : Blo 366759 1048781 := bstep (se 3 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 1048781 = 393293) B393293
theorem B622849 : Blo 366759 622849 := bstep (se 2 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 622849 = 467137) B467137
theorem B524561 : Blo 366759 524561 := bstep (se 2 (by rfl) ⟨196710, by rfl⟩ : syracuseStep 524561 = 393421) B393421
theorem B622883 : Blo 366759 622883 := bstep (se 1 (by rfl) ⟨467162, by rfl⟩ : syracuseStep 622883 = 934325) B934325
theorem B1048963 : Blo 366759 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B524675 : Blo 366759 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B623011 : Blo 366759 623011 := bstep (se 1 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 623011 = 934517) B934517
theorem B1245617 : Blo 366759 1245617 := bstep (se 2 (by rfl) ⟨467106, by rfl⟩ : syracuseStep 1245617 = 934213) B934213
theorem B1769933 : Blo 366759 1769933 := bstep (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) B663725
theorem B1180109 : Blo 366759 1180109 := bstep (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) B442541
theorem B524755 : Blo 366759 524755 := bstep (se 1 (by rfl) ⟨393566, by rfl⟩ : syracuseStep 524755 = 787133) B787133
theorem B623153 : Blo 366759 623153 := bstep (se 2 (by rfl) ⟨233682, by rfl⟩ : syracuseStep 623153 = 467365) B467365
theorem B393827 : Blo 366759 393827 := bstep (se 1 (by rfl) ⟨295370, by rfl⟩ : syracuseStep 393827 = 590741) B590741
theorem B590465 : Blo 366759 590465 := bstep (se 2 (by rfl) ⟨221424, by rfl⟩ : syracuseStep 590465 = 442849) B442849
theorem B623281 : Blo 366759 623281 := bstep (se 2 (by rfl) ⟨233730, by rfl⟩ : syracuseStep 623281 = 467461) B467461
theorem B623315 : Blo 366759 623315 := bstep (se 1 (by rfl) ⟨467486, by rfl⟩ : syracuseStep 623315 = 934973) B934973
theorem B590593 : Blo 366759 590593 := bstep (se 2 (by rfl) ⟨221472, by rfl⟩ : syracuseStep 590593 = 442945) B442945
theorem B590657 : Blo 366759 590657 := bstep (se 2 (by rfl) ⟨221496, by rfl⟩ : syracuseStep 590657 = 442993) B442993
theorem B623443 : Blo 366759 623443 := bstep (se 1 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 623443 = 935165) B935165
theorem B787313 : Blo 366759 787313 := bstep (se 2 (by rfl) ⟨295242, by rfl⟩ : syracuseStep 787313 = 590485) B590485
theorem B558019 : Blo 366759 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B1246157 : Blo 366759 1246157 := bstep (se 3 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 1246157 = 467309) B467309
theorem B1278929 : Blo 366759 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B623585 : Blo 366759 623585 := bstep (se 2 (by rfl) ⟨233844, by rfl⟩ : syracuseStep 623585 = 467689) B467689
theorem B525313 : Blo 366759 525313 := bstep (se 2 (by rfl) ⟨196992, by rfl⟩ : syracuseStep 525313 = 393985) B393985
theorem B1246211 : Blo 366759 1246211 := bstep (se 1 (by rfl) ⟨934658, by rfl⟩ : syracuseStep 1246211 = 1869317) B1869317
theorem B623713 : Blo 366759 623713 := bstep (se 2 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 623713 = 467785) B467785
theorem B2393201 : Blo 366759 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B623747 : Blo 366759 623747 := bstep (se 1 (by rfl) ⟨467810, by rfl⟩ : syracuseStep 623747 = 935621) B935621
theorem B2131121 : Blo 366759 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B1574093 : Blo 366759 1574093 := bstep (se 3 (by rfl) ⟨295142, by rfl⟩ : syracuseStep 1574093 = 590285) B590285
theorem B623875 : Blo 366759 623875 := bstep (se 1 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 623875 = 935813) B935813
theorem B1246481 : Blo 366759 1246481 := bstep (se 2 (by rfl) ⟨467430, by rfl⟩ : syracuseStep 1246481 = 934861) B934861
theorem B394579 : Blo 366759 394579 := bstep (se 1 (by rfl) ⟨295934, by rfl⟩ : syracuseStep 394579 = 591869) B591869
theorem B1869155 : Blo 366759 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B624017 : Blo 366759 624017 := bstep (se 2 (by rfl) ⟨234006, by rfl⟩ : syracuseStep 624017 = 468013) B468013
theorem B624145 : Blo 366759 624145 := bstep (se 2 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 624145 = 468109) B468109
theorem B624179 : Blo 366759 624179 := bstep (se 1 (by rfl) ⟨468134, by rfl⟩ : syracuseStep 624179 = 936269) B936269
theorem B624307 : Blo 366759 624307 := bstep (se 1 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 624307 = 936461) B936461
theorem B526019 : Blo 366759 526019 := bstep (se 1 (by rfl) ⟨394514, by rfl⟩ : syracuseStep 526019 = 789029) B789029
theorem B1050353 : Blo 366759 1050353 := bstep (se 2 (by rfl) ⟨393882, by rfl⟩ : syracuseStep 1050353 = 787765) B787765
theorem B1247021 : Blo 366759 1247021 := bstep (se 3 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 1247021 = 467633) B467633
theorem B624449 : Blo 366759 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B591715 : Blo 366759 591715 := bstep (se 1 (by rfl) ⟨443786, by rfl⟩ : syracuseStep 591715 = 887573) B887573
theorem B1247075 : Blo 366759 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B624577 : Blo 366759 624577 := bstep (se 2 (by rfl) ⟨234216, by rfl⟩ : syracuseStep 624577 = 468433) B468433
theorem B624611 : Blo 366759 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B1181699 : Blo 366759 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B624739 : Blo 366759 624739 := bstep (se 1 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 624739 = 937109) B937109
theorem B1247345 : Blo 366759 1247345 := bstep (se 2 (by rfl) ⟨467754, by rfl⟩ : syracuseStep 1247345 = 935509) B935509
theorem B788611 : Blo 366759 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B1869965 : Blo 366759 1869965 := bstep (se 3 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 1869965 = 701237) B701237
theorem B2001037 : Blo 366759 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B1181891 : Blo 366759 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B559313 : Blo 366759 559313 := bstep (se 2 (by rfl) ⟨209742, by rfl⟩ : syracuseStep 559313 = 419485) B419485
theorem B624881 : Blo 366759 624881 := bstep (se 2 (by rfl) ⟨234330, by rfl⟩ : syracuseStep 624881 = 468661) B468661
theorem B526657 : Blo 366759 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B625009 : Blo 366759 625009 := bstep (se 2 (by rfl) ⟨234378, by rfl⟩ : syracuseStep 625009 = 468757) B468757
theorem B395651 : Blo 366759 395651 := bstep (se 1 (by rfl) ⟨296738, by rfl⟩ : syracuseStep 395651 = 593477) B593477
theorem B625043 : Blo 366759 625043 := bstep (se 1 (by rfl) ⟨468782, by rfl⟩ : syracuseStep 625043 = 937565) B937565
theorem B526771 : Blo 366759 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B2853317 : Blo 366759 2853317 := bstep (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) B534997
theorem B625171 : Blo 366759 625171 := bstep (se 1 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 625171 = 937757) B937757
theorem B1247885 : Blo 366759 1247885 := bstep (se 3 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 1247885 = 467957) B467957
theorem B625313 : Blo 366759 625313 := bstep (se 2 (by rfl) ⟨234492, by rfl⟩ : syracuseStep 625313 = 468985) B468985
theorem B1051309 : Blo 366759 1051309 := bstep (se 3 (by rfl) ⟨197120, by rfl⟩ : syracuseStep 1051309 = 394241) B394241
theorem B1247939 : Blo 366759 1247939 := bstep (se 1 (by rfl) ⟨935954, by rfl⟩ : syracuseStep 1247939 = 1871909) B1871909
theorem B592643 : Blo 366759 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B625441 : Blo 366759 625441 := bstep (se 2 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 625441 = 469081) B469081
theorem B559921 : Blo 366759 559921 := bstep (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) B419941
theorem B625475 : Blo 366759 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B1182545 : Blo 366759 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B1051537 : Blo 366759 1051537 := bstep (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) B788653
theorem B625603 : Blo 366759 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B1248209 : Blo 366759 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B592913 : Blo 366759 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B1051697 : Blo 366759 1051697 := bstep (se 2 (by rfl) ⟨394386, by rfl⟩ : syracuseStep 1051697 = 788773) B788773
theorem B1051811 : Blo 366759 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B756913 : Blo 366759 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B593201 : Blo 366759 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B789841 : Blo 366759 789841 := bstep (se 2 (by rfl) ⟨296190, by rfl⟩ : syracuseStep 789841 = 592381) B592381
theorem B2100613 : Blo 366759 2100613 := bstep (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) B393865
theorem B1248749 : Blo 366759 1248749 := bstep (se 3 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 1248749 = 468281) B468281
theorem B1248803 : Blo 366759 1248803 := bstep (se 1 (by rfl) ⟨936602, by rfl⟩ : syracuseStep 1248803 = 1873205) B1873205
theorem B593617 : Blo 366759 593617 := bstep (se 2 (by rfl) ⟨222606, by rfl⟩ : syracuseStep 593617 = 445213) B445213
theorem B1249073 : Blo 366759 1249073 := bstep (se 2 (by rfl) ⟨468402, by rfl⟩ : syracuseStep 1249073 = 936805) B936805
theorem B888803 : Blo 366759 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B790499 : Blo 366759 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B1052813 : Blo 366759 1052813 := bstep (se 3 (by rfl) ⟨197402, by rfl⟩ : syracuseStep 1052813 = 394805) B394805
theorem B1052995 : Blo 366759 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1249613 : Blo 366759 1249613 := bstep (se 3 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 1249613 = 468605) B468605
theorem B1249667 : Blo 366759 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B7934435 : Blo 366759 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B1053155 : Blo 366759 1053155 := bstep (se 1 (by rfl) ⟨789866, by rfl⟩ : syracuseStep 1053155 = 1579733) B1579733
theorem B496129 : Blo 366759 496129 := bstep (se 2 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 496129 = 372097) B372097
theorem B1249937 : Blo 366759 1249937 := bstep (se 2 (by rfl) ⟨468726, by rfl⟩ : syracuseStep 1249937 = 937453) B937453
theorem B1184557 : Blo 366759 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B889649 : Blo 366759 889649 := bstep (se 2 (by rfl) ⟨333618, by rfl⟩ : syracuseStep 889649 = 667237) B667237
theorem B791345 : Blo 366759 791345 := bstep (se 2 (by rfl) ⟨296754, by rfl⟩ : syracuseStep 791345 = 593509) B593509
theorem B1872881 : Blo 366759 1872881 := bstep (se 2 (by rfl) ⟨702330, by rfl⟩ : syracuseStep 1872881 = 1404661) B1404661
theorem B1250477 : Blo 366759 1250477 := bstep (se 3 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 1250477 = 468929) B468929
theorem B955601 : Blo 366759 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B1250531 : Blo 366759 1250531 := bstep (se 1 (by rfl) ⟨937898, by rfl⟩ : syracuseStep 1250531 = 1875797) B1875797
theorem B1185005 : Blo 366759 1185005 := bstep (se 3 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 1185005 = 444377) B444377
theorem B2102597 : Blo 366759 2102597 := bstep (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) B394237
theorem B3151331 : Blo 366759 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B1578467 : Blo 366759 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1250801 : Blo 366759 1250801 := bstep (se 2 (by rfl) ⟨469050, by rfl⟩ : syracuseStep 1250801 = 938101) B938101
theorem B1054225 : Blo 366759 1054225 := bstep (se 2 (by rfl) ⟨395334, by rfl⟩ : syracuseStep 1054225 = 790669) B790669
theorem B497329 : Blo 366759 497329 := bstep (se 2 (by rfl) ⟨186498, by rfl⟩ : syracuseStep 497329 = 372997) B372997
theorem B464611 : Blo 366759 464611 := bstep (se 1 (by rfl) ⟨348458, by rfl⟩ : syracuseStep 464611 = 696917) B696917
theorem B464707 : Blo 366759 464707 := bstep (se 1 (by rfl) ⟨348530, by rfl⟩ : syracuseStep 464707 = 697061) B697061
theorem B596003 : Blo 366759 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B825425 : Blo 366759 825425 := bstep (se 2 (by rfl) ⟨309534, by rfl⟩ : syracuseStep 825425 = 619069) B619069
theorem B825443 : Blo 366759 825443 := bstep (se 1 (by rfl) ⟨619082, by rfl⟩ : syracuseStep 825443 = 1238165) B1238165
theorem B366771 : Blo 366759 366771 := bstep (se 1 (by rfl) ⟨275078, by rfl⟩ : syracuseStep 366771 = 550157) B550157
theorem B366787 : Blo 366759 366787 := bstep (se 1 (by rfl) ⟨275090, by rfl⟩ : syracuseStep 366787 = 550181) B550181
theorem B366803 : Blo 366759 366803 := bstep (se 1 (by rfl) ⟨275102, by rfl⟩ : syracuseStep 366803 = 550205) B550205
theorem B366819 : Blo 366759 366819 := bstep (se 1 (by rfl) ⟨275114, by rfl⟩ : syracuseStep 366819 = 550229) B550229
theorem B366835 : Blo 366759 366835 := bstep (se 1 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 366835 = 550253) B550253
theorem B366851 : Blo 366759 366851 := bstep (se 1 (by rfl) ⟨275138, by rfl⟩ : syracuseStep 366851 = 550277) B550277
theorem B366867 : Blo 366759 366867 := bstep (se 1 (by rfl) ⟨275150, by rfl⟩ : syracuseStep 366867 = 550301) B550301
theorem B366883 : Blo 366759 366883 := bstep (se 1 (by rfl) ⟨275162, by rfl⟩ : syracuseStep 366883 = 550325) B550325
theorem B366899 : Blo 366759 366899 := bstep (se 1 (by rfl) ⟨275174, by rfl⟩ : syracuseStep 366899 = 550349) B550349
theorem B465203 : Blo 366759 465203 := bstep (se 1 (by rfl) ⟨348902, by rfl⟩ : syracuseStep 465203 = 697805) B697805
theorem B366915 : Blo 366759 366915 := bstep (se 1 (by rfl) ⟨275186, by rfl⟩ : syracuseStep 366915 = 550373) B550373
theorem B366931 : Blo 366759 366931 := bstep (se 1 (by rfl) ⟨275198, by rfl⟩ : syracuseStep 366931 = 550397) B550397
theorem B366947 : Blo 366759 366947 := bstep (se 1 (by rfl) ⟨275210, by rfl⟩ : syracuseStep 366947 = 550421) B550421
theorem B825713 : Blo 366759 825713 := bstep (se 2 (by rfl) ⟨309642, by rfl⟩ : syracuseStep 825713 = 619285) B619285
theorem B366963 : Blo 366759 366963 := bstep (se 1 (by rfl) ⟨275222, by rfl⟩ : syracuseStep 366963 = 550445) B550445
theorem B366979 : Blo 366759 366979 := bstep (se 1 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 366979 = 550469) B550469
theorem B825731 : Blo 366759 825731 := bstep (se 1 (by rfl) ⟨619298, by rfl⟩ : syracuseStep 825731 = 1238597) B1238597
theorem B366995 : Blo 366759 366995 := bstep (se 1 (by rfl) ⟨275246, by rfl⟩ : syracuseStep 366995 = 550493) B550493
theorem B367011 : Blo 366759 367011 := bstep (se 1 (by rfl) ⟨275258, by rfl⟩ : syracuseStep 367011 = 550517) B550517
theorem B1874339 : Blo 366759 1874339 := bstep (se 1 (by rfl) ⟨1405754, by rfl⟩ : syracuseStep 1874339 = 2811509) B2811509
theorem B498097 : Blo 366759 498097 := bstep (se 2 (by rfl) ⟨186786, by rfl⟩ : syracuseStep 498097 = 373573) B373573
theorem B367027 : Blo 366759 367027 := bstep (se 1 (by rfl) ⟨275270, by rfl⟩ : syracuseStep 367027 = 550541) B550541
theorem B367043 : Blo 366759 367043 := bstep (se 1 (by rfl) ⟨275282, by rfl⟩ : syracuseStep 367043 = 550565) B550565
theorem B367059 : Blo 366759 367059 := bstep (se 1 (by rfl) ⟨275294, by rfl⟩ : syracuseStep 367059 = 550589) B550589
theorem B367075 : Blo 366759 367075 := bstep (se 1 (by rfl) ⟨275306, by rfl⟩ : syracuseStep 367075 = 550613) B550613
theorem B367091 : Blo 366759 367091 := bstep (se 1 (by rfl) ⟨275318, by rfl⟩ : syracuseStep 367091 = 550637) B550637
theorem B367107 : Blo 366759 367107 := bstep (se 1 (by rfl) ⟨275330, by rfl⟩ : syracuseStep 367107 = 550661) B550661
theorem B367123 : Blo 366759 367123 := bstep (se 1 (by rfl) ⟨275342, by rfl⟩ : syracuseStep 367123 = 550685) B550685
theorem B367139 : Blo 366759 367139 := bstep (se 1 (by rfl) ⟨275354, by rfl⟩ : syracuseStep 367139 = 550709) B550709
theorem B367155 : Blo 366759 367155 := bstep (se 1 (by rfl) ⟨275366, by rfl⟩ : syracuseStep 367155 = 550733) B550733
theorem B367171 : Blo 366759 367171 := bstep (se 1 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 367171 = 550757) B550757
theorem B367187 : Blo 366759 367187 := bstep (se 1 (by rfl) ⟨275390, by rfl⟩ : syracuseStep 367187 = 550781) B550781
theorem B367203 : Blo 366759 367203 := bstep (se 1 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 367203 = 550805) B550805
theorem B367219 : Blo 366759 367219 := bstep (se 1 (by rfl) ⟨275414, by rfl⟩ : syracuseStep 367219 = 550829) B550829
theorem B367235 : Blo 366759 367235 := bstep (se 1 (by rfl) ⟨275426, by rfl⟩ : syracuseStep 367235 = 550853) B550853
theorem B826001 : Blo 366759 826001 := bstep (se 2 (by rfl) ⟨309750, by rfl⟩ : syracuseStep 826001 = 619501) B619501
theorem B367251 : Blo 366759 367251 := bstep (se 1 (by rfl) ⟨275438, by rfl⟩ : syracuseStep 367251 = 550877) B550877
theorem B826019 : Blo 366759 826019 := bstep (se 1 (by rfl) ⟨619514, by rfl⟩ : syracuseStep 826019 = 1239029) B1239029
theorem B367267 : Blo 366759 367267 := bstep (se 1 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 367267 = 550901) B550901
theorem B367283 : Blo 366759 367283 := bstep (se 1 (by rfl) ⟨275462, by rfl⟩ : syracuseStep 367283 = 550925) B550925
theorem B367299 : Blo 366759 367299 := bstep (se 1 (by rfl) ⟨275474, by rfl⟩ : syracuseStep 367299 = 550949) B550949
theorem B367315 : Blo 366759 367315 := bstep (se 1 (by rfl) ⟨275486, by rfl⟩ : syracuseStep 367315 = 550973) B550973
theorem B367331 : Blo 366759 367331 := bstep (se 1 (by rfl) ⟨275498, by rfl⟩ : syracuseStep 367331 = 550997) B550997
theorem B9116387 : Blo 366759 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B367347 : Blo 366759 367347 := bstep (se 1 (by rfl) ⟨275510, by rfl⟩ : syracuseStep 367347 = 551021) B551021
theorem B367363 : Blo 366759 367363 := bstep (se 1 (by rfl) ⟨275522, by rfl⟩ : syracuseStep 367363 = 551045) B551045
theorem B1055501 : Blo 366759 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B367379 : Blo 366759 367379 := bstep (se 1 (by rfl) ⟨275534, by rfl⟩ : syracuseStep 367379 = 551069) B551069
theorem B367395 : Blo 366759 367395 := bstep (se 1 (by rfl) ⟨275546, by rfl⟩ : syracuseStep 367395 = 551093) B551093
theorem B2366243 : Blo 366759 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B367411 : Blo 366759 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B367427 : Blo 366759 367427 := bstep (se 1 (by rfl) ⟨275570, by rfl⟩ : syracuseStep 367427 = 551141) B551141
theorem B367443 : Blo 366759 367443 := bstep (se 1 (by rfl) ⟨275582, by rfl⟩ : syracuseStep 367443 = 551165) B551165
theorem B367459 : Blo 366759 367459 := bstep (se 1 (by rfl) ⟨275594, by rfl⟩ : syracuseStep 367459 = 551189) B551189
theorem B367475 : Blo 366759 367475 := bstep (se 1 (by rfl) ⟨275606, by rfl⟩ : syracuseStep 367475 = 551213) B551213
theorem B367491 : Blo 366759 367491 := bstep (se 1 (by rfl) ⟨275618, by rfl⟩ : syracuseStep 367491 = 551237) B551237
theorem B367507 : Blo 366759 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B367523 : Blo 366759 367523 := bstep (se 1 (by rfl) ⟨275642, by rfl⟩ : syracuseStep 367523 = 551285) B551285
theorem B826289 : Blo 366759 826289 := bstep (se 2 (by rfl) ⟨309858, by rfl⟩ : syracuseStep 826289 = 619717) B619717
theorem B367539 : Blo 366759 367539 := bstep (se 1 (by rfl) ⟨275654, by rfl⟩ : syracuseStep 367539 = 551309) B551309
theorem B826307 : Blo 366759 826307 := bstep (se 1 (by rfl) ⟨619730, by rfl⟩ : syracuseStep 826307 = 1239461) B1239461
theorem B367555 : Blo 366759 367555 := bstep (se 1 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 367555 = 551333) B551333
theorem B1055683 : Blo 366759 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B367571 : Blo 366759 367571 := bstep (se 1 (by rfl) ⟨275678, by rfl⟩ : syracuseStep 367571 = 551357) B551357
theorem B367587 : Blo 366759 367587 := bstep (se 1 (by rfl) ⟨275690, by rfl⟩ : syracuseStep 367587 = 551381) B551381
theorem B1055729 : Blo 366759 1055729 := bstep (se 2 (by rfl) ⟨395898, by rfl⟩ : syracuseStep 1055729 = 791797) B791797
theorem B367603 : Blo 366759 367603 := bstep (se 1 (by rfl) ⟨275702, by rfl⟩ : syracuseStep 367603 = 551405) B551405
theorem B465907 : Blo 366759 465907 := bstep (se 1 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 465907 = 698861) B698861
theorem B367619 : Blo 366759 367619 := bstep (se 1 (by rfl) ⟨275714, by rfl⟩ : syracuseStep 367619 = 551429) B551429
theorem B367635 : Blo 366759 367635 := bstep (se 1 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 367635 = 551453) B551453
theorem B367651 : Blo 366759 367651 := bstep (se 1 (by rfl) ⟨275738, by rfl⟩ : syracuseStep 367651 = 551477) B551477
theorem B367667 : Blo 366759 367667 := bstep (se 1 (by rfl) ⟨275750, by rfl⟩ : syracuseStep 367667 = 551501) B551501
theorem B367683 : Blo 366759 367683 := bstep (se 1 (by rfl) ⟨275762, by rfl⟩ : syracuseStep 367683 = 551525) B551525
theorem B367699 : Blo 366759 367699 := bstep (se 1 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 367699 = 551549) B551549
theorem B466003 : Blo 366759 466003 := bstep (se 1 (by rfl) ⟨349502, by rfl⟩ : syracuseStep 466003 = 699005) B699005
theorem B367715 : Blo 366759 367715 := bstep (se 1 (by rfl) ⟨275786, by rfl⟩ : syracuseStep 367715 = 551573) B551573
theorem B367731 : Blo 366759 367731 := bstep (se 1 (by rfl) ⟨275798, by rfl⟩ : syracuseStep 367731 = 551597) B551597
theorem B367747 : Blo 366759 367747 := bstep (se 1 (by rfl) ⟨275810, by rfl⟩ : syracuseStep 367747 = 551621) B551621
theorem B367763 : Blo 366759 367763 := bstep (se 1 (by rfl) ⟨275822, by rfl⟩ : syracuseStep 367763 = 551645) B551645
theorem B367779 : Blo 366759 367779 := bstep (se 1 (by rfl) ⟨275834, by rfl⟩ : syracuseStep 367779 = 551669) B551669
theorem B367795 : Blo 366759 367795 := bstep (se 1 (by rfl) ⟨275846, by rfl⟩ : syracuseStep 367795 = 551693) B551693
theorem B367811 : Blo 366759 367811 := bstep (se 1 (by rfl) ⟨275858, by rfl⟩ : syracuseStep 367811 = 551717) B551717
theorem B1875149 : Blo 366759 1875149 := bstep (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) B703181
theorem B826577 : Blo 366759 826577 := bstep (se 2 (by rfl) ⟨309966, by rfl⟩ : syracuseStep 826577 = 619933) B619933
theorem B367827 : Blo 366759 367827 := bstep (se 1 (by rfl) ⟨275870, by rfl⟩ : syracuseStep 367827 = 551741) B551741
theorem B826595 : Blo 366759 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B367843 : Blo 366759 367843 := bstep (se 1 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 367843 = 551765) B551765
theorem B367859 : Blo 366759 367859 := bstep (se 1 (by rfl) ⟨275894, by rfl⟩ : syracuseStep 367859 = 551789) B551789
theorem B367875 : Blo 366759 367875 := bstep (se 1 (by rfl) ⟨275906, by rfl⟩ : syracuseStep 367875 = 551813) B551813
theorem B367891 : Blo 366759 367891 := bstep (se 1 (by rfl) ⟨275918, by rfl⟩ : syracuseStep 367891 = 551837) B551837
theorem B367907 : Blo 366759 367907 := bstep (se 1 (by rfl) ⟨275930, by rfl⟩ : syracuseStep 367907 = 551861) B551861
theorem B367923 : Blo 366759 367923 := bstep (se 1 (by rfl) ⟨275942, by rfl⟩ : syracuseStep 367923 = 551885) B551885
theorem B367939 : Blo 366759 367939 := bstep (se 1 (by rfl) ⟨275954, by rfl⟩ : syracuseStep 367939 = 551909) B551909
theorem B367955 : Blo 366759 367955 := bstep (se 1 (by rfl) ⟨275966, by rfl⟩ : syracuseStep 367955 = 551933) B551933
theorem B367971 : Blo 366759 367971 := bstep (se 1 (by rfl) ⟨275978, by rfl⟩ : syracuseStep 367971 = 551957) B551957
theorem B367987 : Blo 366759 367987 := bstep (se 1 (by rfl) ⟨275990, by rfl⟩ : syracuseStep 367987 = 551981) B551981
theorem B368003 : Blo 366759 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B368019 : Blo 366759 368019 := bstep (se 1 (by rfl) ⟨276014, by rfl⟩ : syracuseStep 368019 = 552029) B552029
theorem B499091 : Blo 366759 499091 := bstep (se 1 (by rfl) ⟨374318, by rfl⟩ : syracuseStep 499091 = 748637) B748637
theorem B368035 : Blo 366759 368035 := bstep (se 1 (by rfl) ⟨276026, by rfl⟩ : syracuseStep 368035 = 552053) B552053
theorem B368051 : Blo 366759 368051 := bstep (se 1 (by rfl) ⟨276038, by rfl⟩ : syracuseStep 368051 = 552077) B552077
theorem B368067 : Blo 366759 368067 := bstep (se 1 (by rfl) ⟨276050, by rfl⟩ : syracuseStep 368067 = 552101) B552101
theorem B368083 : Blo 366759 368083 := bstep (se 1 (by rfl) ⟨276062, by rfl⟩ : syracuseStep 368083 = 552125) B552125
theorem B368099 : Blo 366759 368099 := bstep (se 1 (by rfl) ⟨276074, by rfl⟩ : syracuseStep 368099 = 552149) B552149
theorem B4201955 : Blo 366759 4201955 := bstep (se 1 (by rfl) ⟨3151466, by rfl⟩ : syracuseStep 4201955 = 6302933) B6302933
theorem B826865 : Blo 366759 826865 := bstep (se 2 (by rfl) ⟨310074, by rfl⟩ : syracuseStep 826865 = 620149) B620149
theorem B368115 : Blo 366759 368115 := bstep (se 1 (by rfl) ⟨276086, by rfl⟩ : syracuseStep 368115 = 552173) B552173
theorem B826883 : Blo 366759 826883 := bstep (se 1 (by rfl) ⟨620162, by rfl⟩ : syracuseStep 826883 = 1240325) B1240325
theorem B368131 : Blo 366759 368131 := bstep (se 1 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 368131 = 552197) B552197
theorem B630289 : Blo 366759 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B368147 : Blo 366759 368147 := bstep (se 1 (by rfl) ⟨276110, by rfl⟩ : syracuseStep 368147 = 552221) B552221
theorem B368163 : Blo 366759 368163 := bstep (se 1 (by rfl) ⟨276122, by rfl⟩ : syracuseStep 368163 = 552245) B552245
theorem B368179 : Blo 366759 368179 := bstep (se 1 (by rfl) ⟨276134, by rfl⟩ : syracuseStep 368179 = 552269) B552269
theorem B368195 : Blo 366759 368195 := bstep (se 1 (by rfl) ⟨276146, by rfl⟩ : syracuseStep 368195 = 552293) B552293
theorem B466499 : Blo 366759 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B368211 : Blo 366759 368211 := bstep (se 1 (by rfl) ⟨276158, by rfl⟩ : syracuseStep 368211 = 552317) B552317
theorem B368227 : Blo 366759 368227 := bstep (se 1 (by rfl) ⟨276170, by rfl⟩ : syracuseStep 368227 = 552341) B552341
theorem B368243 : Blo 366759 368243 := bstep (se 1 (by rfl) ⟨276182, by rfl⟩ : syracuseStep 368243 = 552365) B552365
theorem B368259 : Blo 366759 368259 := bstep (se 1 (by rfl) ⟨276194, by rfl⟩ : syracuseStep 368259 = 552389) B552389
theorem B368275 : Blo 366759 368275 := bstep (se 1 (by rfl) ⟨276206, by rfl⟩ : syracuseStep 368275 = 552413) B552413
theorem B368291 : Blo 366759 368291 := bstep (se 1 (by rfl) ⟨276218, by rfl⟩ : syracuseStep 368291 = 552437) B552437
theorem B368307 : Blo 366759 368307 := bstep (se 1 (by rfl) ⟨276230, by rfl⟩ : syracuseStep 368307 = 552461) B552461
theorem B368323 : Blo 366759 368323 := bstep (se 1 (by rfl) ⟨276242, by rfl⟩ : syracuseStep 368323 = 552485) B552485
theorem B368339 : Blo 366759 368339 := bstep (se 1 (by rfl) ⟨276254, by rfl⟩ : syracuseStep 368339 = 552509) B552509
theorem B368355 : Blo 366759 368355 := bstep (se 1 (by rfl) ⟨276266, by rfl⟩ : syracuseStep 368355 = 552533) B552533
theorem B368371 : Blo 366759 368371 := bstep (se 1 (by rfl) ⟨276278, by rfl⟩ : syracuseStep 368371 = 552557) B552557
theorem B368387 : Blo 366759 368387 := bstep (se 1 (by rfl) ⟨276290, by rfl⟩ : syracuseStep 368387 = 552581) B552581
theorem B827153 : Blo 366759 827153 := bstep (se 2 (by rfl) ⟨310182, by rfl⟩ : syracuseStep 827153 = 620365) B620365
theorem B368403 : Blo 366759 368403 := bstep (se 1 (by rfl) ⟨276302, by rfl⟩ : syracuseStep 368403 = 552605) B552605
theorem B827171 : Blo 366759 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B368419 : Blo 366759 368419 := bstep (se 1 (by rfl) ⟨276314, by rfl⟩ : syracuseStep 368419 = 552629) B552629
theorem B368435 : Blo 366759 368435 := bstep (se 1 (by rfl) ⟨276326, by rfl⟩ : syracuseStep 368435 = 552653) B552653
theorem B368451 : Blo 366759 368451 := bstep (se 1 (by rfl) ⟨276338, by rfl⟩ : syracuseStep 368451 = 552677) B552677
theorem B368467 : Blo 366759 368467 := bstep (se 1 (by rfl) ⟨276350, by rfl⟩ : syracuseStep 368467 = 552701) B552701
theorem B368483 : Blo 366759 368483 := bstep (se 1 (by rfl) ⟨276362, by rfl⟩ : syracuseStep 368483 = 552725) B552725
theorem B368499 : Blo 366759 368499 := bstep (se 1 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 368499 = 552749) B552749
theorem B368515 : Blo 366759 368515 := bstep (se 1 (by rfl) ⟨276386, by rfl⟩ : syracuseStep 368515 = 552773) B552773
theorem B368531 : Blo 366759 368531 := bstep (se 1 (by rfl) ⟨276398, by rfl⟩ : syracuseStep 368531 = 552797) B552797
theorem B368547 : Blo 366759 368547 := bstep (se 1 (by rfl) ⟨276410, by rfl⟩ : syracuseStep 368547 = 552821) B552821
theorem B1187747 : Blo 366759 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B368563 : Blo 366759 368563 := bstep (se 1 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 368563 = 552845) B552845
theorem B368579 : Blo 366759 368579 := bstep (se 1 (by rfl) ⟨276434, by rfl⟩ : syracuseStep 368579 = 552869) B552869
theorem B1679309 : Blo 366759 1679309 := bstep (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) B629741
theorem B368595 : Blo 366759 368595 := bstep (se 1 (by rfl) ⟨276446, by rfl⟩ : syracuseStep 368595 = 552893) B552893
theorem B368611 : Blo 366759 368611 := bstep (se 1 (by rfl) ⟨276458, by rfl⟩ : syracuseStep 368611 = 552917) B552917
theorem B1122275 : Blo 366759 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B368627 : Blo 366759 368627 := bstep (se 1 (by rfl) ⟨276470, by rfl⟩ : syracuseStep 368627 = 552941) B552941
theorem B368643 : Blo 366759 368643 := bstep (se 1 (by rfl) ⟨276482, by rfl⟩ : syracuseStep 368643 = 552965) B552965
theorem B368659 : Blo 366759 368659 := bstep (se 1 (by rfl) ⟨276494, by rfl⟩ : syracuseStep 368659 = 552989) B552989
theorem B368675 : Blo 366759 368675 := bstep (se 1 (by rfl) ⟨276506, by rfl⟩ : syracuseStep 368675 = 553013) B553013
theorem B827441 : Blo 366759 827441 := bstep (se 2 (by rfl) ⟨310290, by rfl⟩ : syracuseStep 827441 = 620581) B620581
theorem B368691 : Blo 366759 368691 := bstep (se 1 (by rfl) ⟨276518, by rfl⟩ : syracuseStep 368691 = 553037) B553037
theorem B827459 : Blo 366759 827459 := bstep (se 1 (by rfl) ⟨620594, by rfl⟩ : syracuseStep 827459 = 1241189) B1241189
theorem B368707 : Blo 366759 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B1581133 : Blo 366759 1581133 := bstep (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) B592925
theorem B368723 : Blo 366759 368723 := bstep (se 1 (by rfl) ⟨276542, by rfl⟩ : syracuseStep 368723 = 553085) B553085
theorem B368739 : Blo 366759 368739 := bstep (se 1 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 368739 = 553109) B553109
theorem B368755 : Blo 366759 368755 := bstep (se 1 (by rfl) ⟨276566, by rfl⟩ : syracuseStep 368755 = 553133) B553133
theorem B368771 : Blo 366759 368771 := bstep (se 1 (by rfl) ⟨276578, by rfl⟩ : syracuseStep 368771 = 553157) B553157
theorem B368787 : Blo 366759 368787 := bstep (se 1 (by rfl) ⟨276590, by rfl⟩ : syracuseStep 368787 = 553181) B553181
theorem B368803 : Blo 366759 368803 := bstep (se 1 (by rfl) ⟨276602, by rfl⟩ : syracuseStep 368803 = 553205) B553205
theorem B368819 : Blo 366759 368819 := bstep (se 1 (by rfl) ⟨276614, by rfl⟩ : syracuseStep 368819 = 553229) B553229
theorem B368835 : Blo 366759 368835 := bstep (se 1 (by rfl) ⟨276626, by rfl⟩ : syracuseStep 368835 = 553253) B553253
theorem B696529 : Blo 366759 696529 := bstep (se 2 (by rfl) ⟨261198, by rfl⟩ : syracuseStep 696529 = 522397) B522397
theorem B368851 : Blo 366759 368851 := bstep (se 1 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 368851 = 553277) B553277
theorem B368867 : Blo 366759 368867 := bstep (se 1 (by rfl) ⟨276650, by rfl⟩ : syracuseStep 368867 = 553301) B553301
theorem B2662627 : Blo 366759 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B368883 : Blo 366759 368883 := bstep (se 1 (by rfl) ⟨276662, by rfl⟩ : syracuseStep 368883 = 553325) B553325
theorem B368899 : Blo 366759 368899 := bstep (se 1 (by rfl) ⟨276674, by rfl⟩ : syracuseStep 368899 = 553349) B553349
theorem B467203 : Blo 366759 467203 := bstep (se 1 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 467203 = 700805) B700805
theorem B368915 : Blo 366759 368915 := bstep (se 1 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 368915 = 553373) B553373
theorem B368931 : Blo 366759 368931 := bstep (se 1 (by rfl) ⟨276698, by rfl⟩ : syracuseStep 368931 = 553397) B553397
theorem B368947 : Blo 366759 368947 := bstep (se 1 (by rfl) ⟨276710, by rfl⟩ : syracuseStep 368947 = 553421) B553421
theorem B368963 : Blo 366759 368963 := bstep (se 1 (by rfl) ⟨276722, by rfl⟩ : syracuseStep 368963 = 553445) B553445
theorem B827729 : Blo 366759 827729 := bstep (se 2 (by rfl) ⟨310398, by rfl⟩ : syracuseStep 827729 = 620797) B620797
theorem B368979 : Blo 366759 368979 := bstep (se 1 (by rfl) ⟨276734, by rfl⟩ : syracuseStep 368979 = 553469) B553469
theorem B827747 : Blo 366759 827747 := bstep (se 1 (by rfl) ⟨620810, by rfl⟩ : syracuseStep 827747 = 1241621) B1241621
theorem B368995 : Blo 366759 368995 := bstep (se 1 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 368995 = 553493) B553493
theorem B467299 : Blo 366759 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B369011 : Blo 366759 369011 := bstep (se 1 (by rfl) ⟨276758, by rfl⟩ : syracuseStep 369011 = 553517) B553517
theorem B369027 : Blo 366759 369027 := bstep (se 1 (by rfl) ⟨276770, by rfl⟩ : syracuseStep 369027 = 553541) B553541
theorem B369043 : Blo 366759 369043 := bstep (se 1 (by rfl) ⟨276782, by rfl⟩ : syracuseStep 369043 = 553565) B553565
theorem B369059 : Blo 366759 369059 := bstep (se 1 (by rfl) ⟨276794, by rfl⟩ : syracuseStep 369059 = 553589) B553589
theorem B369075 : Blo 366759 369075 := bstep (se 1 (by rfl) ⟨276806, by rfl⟩ : syracuseStep 369075 = 553613) B553613
theorem B369091 : Blo 366759 369091 := bstep (se 1 (by rfl) ⟨276818, by rfl⟩ : syracuseStep 369091 = 553637) B553637
theorem B369107 : Blo 366759 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B369123 : Blo 366759 369123 := bstep (se 1 (by rfl) ⟨276842, by rfl⟩ : syracuseStep 369123 = 553685) B553685
theorem B369139 : Blo 366759 369139 := bstep (se 1 (by rfl) ⟨276854, by rfl⟩ : syracuseStep 369139 = 553709) B553709
theorem B369155 : Blo 366759 369155 := bstep (se 1 (by rfl) ⟨276866, by rfl⟩ : syracuseStep 369155 = 553733) B553733
theorem B369171 : Blo 366759 369171 := bstep (se 1 (by rfl) ⟨276878, by rfl⟩ : syracuseStep 369171 = 553757) B553757
theorem B369187 : Blo 366759 369187 := bstep (se 1 (by rfl) ⟨276890, by rfl⟩ : syracuseStep 369187 = 553781) B553781
theorem B369203 : Blo 366759 369203 := bstep (se 1 (by rfl) ⟨276902, by rfl⟩ : syracuseStep 369203 = 553805) B553805
theorem B369219 : Blo 366759 369219 := bstep (se 1 (by rfl) ⟨276914, by rfl⟩ : syracuseStep 369219 = 553829) B553829
theorem B369235 : Blo 366759 369235 := bstep (se 1 (by rfl) ⟨276926, by rfl⟩ : syracuseStep 369235 = 553853) B553853
theorem B369251 : Blo 366759 369251 := bstep (se 1 (by rfl) ⟨276938, by rfl⟩ : syracuseStep 369251 = 553877) B553877
theorem B828017 : Blo 366759 828017 := bstep (se 2 (by rfl) ⟨310506, by rfl⟩ : syracuseStep 828017 = 621013) B621013
theorem B369267 : Blo 366759 369267 := bstep (se 1 (by rfl) ⟨276950, by rfl⟩ : syracuseStep 369267 = 553901) B553901
theorem B828035 : Blo 366759 828035 := bstep (se 1 (by rfl) ⟨621026, by rfl⟩ : syracuseStep 828035 = 1242053) B1242053
theorem B369283 : Blo 366759 369283 := bstep (se 1 (by rfl) ⟨276962, by rfl⟩ : syracuseStep 369283 = 553925) B553925
theorem B369299 : Blo 366759 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B369315 : Blo 366759 369315 := bstep (se 1 (by rfl) ⟨276986, by rfl⟩ : syracuseStep 369315 = 553973) B553973
theorem B369331 : Blo 366759 369331 := bstep (se 1 (by rfl) ⟨276998, by rfl⟩ : syracuseStep 369331 = 553997) B553997
theorem B369347 : Blo 366759 369347 := bstep (se 1 (by rfl) ⟨277010, by rfl⟩ : syracuseStep 369347 = 554021) B554021
theorem B369363 : Blo 366759 369363 := bstep (se 1 (by rfl) ⟨277022, by rfl⟩ : syracuseStep 369363 = 554045) B554045
theorem B369379 : Blo 366759 369379 := bstep (se 1 (by rfl) ⟨277034, by rfl⟩ : syracuseStep 369379 = 554069) B554069
theorem B369395 : Blo 366759 369395 := bstep (se 1 (by rfl) ⟨277046, by rfl⟩ : syracuseStep 369395 = 554093) B554093
theorem B369411 : Blo 366759 369411 := bstep (se 1 (by rfl) ⟨277058, by rfl⟩ : syracuseStep 369411 = 554117) B554117
theorem B369427 : Blo 366759 369427 := bstep (se 1 (by rfl) ⟨277070, by rfl⟩ : syracuseStep 369427 = 554141) B554141
theorem B369443 : Blo 366759 369443 := bstep (se 1 (by rfl) ⟨277082, by rfl⟩ : syracuseStep 369443 = 554165) B554165
theorem B369459 : Blo 366759 369459 := bstep (se 1 (by rfl) ⟨277094, by rfl⟩ : syracuseStep 369459 = 554189) B554189
theorem B369475 : Blo 366759 369475 := bstep (se 1 (by rfl) ⟨277106, by rfl⟩ : syracuseStep 369475 = 554213) B554213
theorem B369491 : Blo 366759 369491 := bstep (se 1 (by rfl) ⟨277118, by rfl⟩ : syracuseStep 369491 = 554237) B554237
theorem B467795 : Blo 366759 467795 := bstep (se 1 (by rfl) ⟨350846, by rfl⟩ : syracuseStep 467795 = 701693) B701693
theorem B369507 : Blo 366759 369507 := bstep (se 1 (by rfl) ⟨277130, by rfl⟩ : syracuseStep 369507 = 554261) B554261
theorem B664433 : Blo 366759 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B369523 : Blo 366759 369523 := bstep (se 1 (by rfl) ⟨277142, by rfl⟩ : syracuseStep 369523 = 554285) B554285
theorem B369539 : Blo 366759 369539 := bstep (se 1 (by rfl) ⟨277154, by rfl⟩ : syracuseStep 369539 = 554309) B554309
theorem B828305 : Blo 366759 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B369555 : Blo 366759 369555 := bstep (se 1 (by rfl) ⟨277166, by rfl⟩ : syracuseStep 369555 = 554333) B554333
theorem B500627 : Blo 366759 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B828323 : Blo 366759 828323 := bstep (se 1 (by rfl) ⟨621242, by rfl⟩ : syracuseStep 828323 = 1242485) B1242485
theorem B369571 : Blo 366759 369571 := bstep (se 1 (by rfl) ⟨277178, by rfl⟩ : syracuseStep 369571 = 554357) B554357
theorem B369587 : Blo 366759 369587 := bstep (se 1 (by rfl) ⟨277190, by rfl⟩ : syracuseStep 369587 = 554381) B554381
theorem B369603 : Blo 366759 369603 := bstep (se 1 (by rfl) ⟨277202, by rfl⟩ : syracuseStep 369603 = 554405) B554405
theorem B369619 : Blo 366759 369619 := bstep (se 1 (by rfl) ⟨277214, by rfl⟩ : syracuseStep 369619 = 554429) B554429
theorem B369635 : Blo 366759 369635 := bstep (se 1 (by rfl) ⟨277226, by rfl⟩ : syracuseStep 369635 = 554453) B554453
theorem B369651 : Blo 366759 369651 := bstep (se 1 (by rfl) ⟨277238, by rfl⟩ : syracuseStep 369651 = 554477) B554477
theorem B369667 : Blo 366759 369667 := bstep (se 1 (by rfl) ⟨277250, by rfl⟩ : syracuseStep 369667 = 554501) B554501
theorem B369683 : Blo 366759 369683 := bstep (se 1 (by rfl) ⟨277262, by rfl⟩ : syracuseStep 369683 = 554525) B554525
theorem B631841 : Blo 366759 631841 := bstep (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) B473881
theorem B369699 : Blo 366759 369699 := bstep (se 1 (by rfl) ⟨277274, by rfl⟩ : syracuseStep 369699 = 554549) B554549
theorem B369715 : Blo 366759 369715 := bstep (se 1 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 369715 = 554573) B554573
theorem B369731 : Blo 366759 369731 := bstep (se 1 (by rfl) ⟨277298, by rfl⟩ : syracuseStep 369731 = 554597) B554597
theorem B2106445 : Blo 366759 2106445 := bstep (se 3 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 2106445 = 789917) B789917
theorem B369747 : Blo 366759 369747 := bstep (se 1 (by rfl) ⟨277310, by rfl⟩ : syracuseStep 369747 = 554621) B554621
theorem B369763 : Blo 366759 369763 := bstep (se 1 (by rfl) ⟨277322, by rfl⟩ : syracuseStep 369763 = 554645) B554645
theorem B1582193 : Blo 366759 1582193 := bstep (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) B1186645
theorem B369779 : Blo 366759 369779 := bstep (se 1 (by rfl) ⟨277334, by rfl⟩ : syracuseStep 369779 = 554669) B554669
theorem B369795 : Blo 366759 369795 := bstep (se 1 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 369795 = 554693) B554693
theorem B369811 : Blo 366759 369811 := bstep (se 1 (by rfl) ⟨277358, by rfl⟩ : syracuseStep 369811 = 554717) B554717
theorem B369827 : Blo 366759 369827 := bstep (se 1 (by rfl) ⟨277370, by rfl⟩ : syracuseStep 369827 = 554741) B554741
theorem B1778851 : Blo 366759 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B828593 : Blo 366759 828593 := bstep (se 2 (by rfl) ⟨310722, by rfl⟩ : syracuseStep 828593 = 621445) B621445
theorem B369843 : Blo 366759 369843 := bstep (se 1 (by rfl) ⟨277382, by rfl⟩ : syracuseStep 369843 = 554765) B554765
theorem B828611 : Blo 366759 828611 := bstep (se 1 (by rfl) ⟨621458, by rfl⟩ : syracuseStep 828611 = 1242917) B1242917
theorem B369859 : Blo 366759 369859 := bstep (se 1 (by rfl) ⟨277394, by rfl⟩ : syracuseStep 369859 = 554789) B554789
theorem B369875 : Blo 366759 369875 := bstep (se 1 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 369875 = 554813) B554813
theorem B369891 : Blo 366759 369891 := bstep (se 1 (by rfl) ⟨277418, by rfl⟩ : syracuseStep 369891 = 554837) B554837
theorem B697585 : Blo 366759 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B369907 : Blo 366759 369907 := bstep (se 1 (by rfl) ⟨277430, by rfl⟩ : syracuseStep 369907 = 554861) B554861
theorem B369923 : Blo 366759 369923 := bstep (se 1 (by rfl) ⟨277442, by rfl⟩ : syracuseStep 369923 = 554885) B554885
theorem B369939 : Blo 366759 369939 := bstep (se 1 (by rfl) ⟨277454, by rfl⟩ : syracuseStep 369939 = 554909) B554909
theorem B369955 : Blo 366759 369955 := bstep (se 1 (by rfl) ⟨277466, by rfl⟩ : syracuseStep 369955 = 554933) B554933
theorem B369971 : Blo 366759 369971 := bstep (se 1 (by rfl) ⟨277478, by rfl⟩ : syracuseStep 369971 = 554957) B554957
theorem B369987 : Blo 366759 369987 := bstep (se 1 (by rfl) ⟨277490, by rfl⟩ : syracuseStep 369987 = 554981) B554981
theorem B370003 : Blo 366759 370003 := bstep (se 1 (by rfl) ⟨277502, by rfl⟩ : syracuseStep 370003 = 555005) B555005
theorem B370019 : Blo 366759 370019 := bstep (se 1 (by rfl) ⟨277514, by rfl⟩ : syracuseStep 370019 = 555029) B555029
theorem B370035 : Blo 366759 370035 := bstep (se 1 (by rfl) ⟨277526, by rfl⟩ : syracuseStep 370035 = 555053) B555053
theorem B370051 : Blo 366759 370051 := bstep (se 1 (by rfl) ⟨277538, by rfl⟩ : syracuseStep 370051 = 555077) B555077
theorem B370067 : Blo 366759 370067 := bstep (se 1 (by rfl) ⟨277550, by rfl⟩ : syracuseStep 370067 = 555101) B555101
theorem B370083 : Blo 366759 370083 := bstep (se 1 (by rfl) ⟨277562, by rfl⟩ : syracuseStep 370083 = 555125) B555125
theorem B370099 : Blo 366759 370099 := bstep (se 1 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 370099 = 555149) B555149
theorem B370115 : Blo 366759 370115 := bstep (se 1 (by rfl) ⟨277586, by rfl⟩ : syracuseStep 370115 = 555173) B555173
theorem B7120325 : Blo 366759 7120325 := bstep (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) B1335061
theorem B828881 : Blo 366759 828881 := bstep (se 2 (by rfl) ⟨310830, by rfl⟩ : syracuseStep 828881 = 621661) B621661
theorem B370131 : Blo 366759 370131 := bstep (se 1 (by rfl) ⟨277598, by rfl⟩ : syracuseStep 370131 = 555197) B555197
theorem B828899 : Blo 366759 828899 := bstep (se 1 (by rfl) ⟨621674, by rfl⟩ : syracuseStep 828899 = 1243349) B1243349
theorem B370147 : Blo 366759 370147 := bstep (se 1 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 370147 = 555221) B555221
theorem B370163 : Blo 366759 370163 := bstep (se 1 (by rfl) ⟨277622, by rfl⟩ : syracuseStep 370163 = 555245) B555245
theorem B370179 : Blo 366759 370179 := bstep (se 1 (by rfl) ⟨277634, by rfl⟩ : syracuseStep 370179 = 555269) B555269
theorem B468499 : Blo 366759 468499 := bstep (se 1 (by rfl) ⟨351374, by rfl⟩ : syracuseStep 468499 = 702749) B702749
theorem B370195 : Blo 366759 370195 := bstep (se 1 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 370195 = 555293) B555293
theorem B370211 : Blo 366759 370211 := bstep (se 1 (by rfl) ⟨277658, by rfl⟩ : syracuseStep 370211 = 555317) B555317
theorem B370227 : Blo 366759 370227 := bstep (se 1 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 370227 = 555341) B555341
theorem B370243 : Blo 366759 370243 := bstep (se 1 (by rfl) ⟨277682, by rfl⟩ : syracuseStep 370243 = 555365) B555365
theorem B370259 : Blo 366759 370259 := bstep (se 1 (by rfl) ⟨277694, by rfl⟩ : syracuseStep 370259 = 555389) B555389
theorem B370275 : Blo 366759 370275 := bstep (se 1 (by rfl) ⟨277706, by rfl⟩ : syracuseStep 370275 = 555413) B555413
theorem B1877617 : Blo 366759 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B468595 : Blo 366759 468595 := bstep (se 1 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 468595 = 702893) B702893
theorem B370291 : Blo 366759 370291 := bstep (se 1 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 370291 = 555437) B555437
theorem B697987 : Blo 366759 697987 := bstep (se 1 (by rfl) ⟨523490, by rfl⟩ : syracuseStep 697987 = 1046981) B1046981
theorem B370307 : Blo 366759 370307 := bstep (se 1 (by rfl) ⟨277730, by rfl⟩ : syracuseStep 370307 = 555461) B555461
theorem B370323 : Blo 366759 370323 := bstep (se 1 (by rfl) ⟨277742, by rfl⟩ : syracuseStep 370323 = 555485) B555485
theorem B370339 : Blo 366759 370339 := bstep (se 1 (by rfl) ⟨277754, by rfl⟩ : syracuseStep 370339 = 555509) B555509
theorem B698033 : Blo 366759 698033 := bstep (se 2 (by rfl) ⟨261762, by rfl⟩ : syracuseStep 698033 = 523525) B523525
theorem B370355 : Blo 366759 370355 := bstep (se 1 (by rfl) ⟨277766, by rfl⟩ : syracuseStep 370355 = 555533) B555533
theorem B370371 : Blo 366759 370371 := bstep (se 1 (by rfl) ⟨277778, by rfl⟩ : syracuseStep 370371 = 555557) B555557
theorem B370387 : Blo 366759 370387 := bstep (se 1 (by rfl) ⟨277790, by rfl⟩ : syracuseStep 370387 = 555581) B555581
theorem B370403 : Blo 366759 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B1124077 : Blo 366759 1124077 := bstep (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) B421529
theorem B829169 : Blo 366759 829169 := bstep (se 2 (by rfl) ⟨310938, by rfl⟩ : syracuseStep 829169 = 621877) B621877
theorem B370419 : Blo 366759 370419 := bstep (se 1 (by rfl) ⟨277814, by rfl⟩ : syracuseStep 370419 = 555629) B555629
theorem B829187 : Blo 366759 829187 := bstep (se 1 (by rfl) ⟨621890, by rfl⟩ : syracuseStep 829187 = 1243781) B1243781
theorem B370435 : Blo 366759 370435 := bstep (se 1 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 370435 = 555653) B555653
theorem B370451 : Blo 366759 370451 := bstep (se 1 (by rfl) ⟨277838, by rfl⟩ : syracuseStep 370451 = 555677) B555677
theorem B370467 : Blo 366759 370467 := bstep (se 1 (by rfl) ⟨277850, by rfl⟩ : syracuseStep 370467 = 555701) B555701
theorem B370483 : Blo 366759 370483 := bstep (se 1 (by rfl) ⟨277862, by rfl⟩ : syracuseStep 370483 = 555725) B555725
theorem B370499 : Blo 366759 370499 := bstep (se 1 (by rfl) ⟨277874, by rfl⟩ : syracuseStep 370499 = 555749) B555749
theorem B370515 : Blo 366759 370515 := bstep (se 1 (by rfl) ⟨277886, by rfl⟩ : syracuseStep 370515 = 555773) B555773
theorem B2795363 : Blo 366759 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B370531 : Blo 366759 370531 := bstep (se 1 (by rfl) ⟨277898, by rfl⟩ : syracuseStep 370531 = 555797) B555797
theorem B370547 : Blo 366759 370547 := bstep (se 1 (by rfl) ⟨277910, by rfl⟩ : syracuseStep 370547 = 555821) B555821
theorem B370563 : Blo 366759 370563 := bstep (se 1 (by rfl) ⟨277922, by rfl⟩ : syracuseStep 370563 = 555845) B555845
theorem B370579 : Blo 366759 370579 := bstep (se 1 (by rfl) ⟨277934, by rfl⟩ : syracuseStep 370579 = 555869) B555869
theorem B370595 : Blo 366759 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B370611 : Blo 366759 370611 := bstep (se 1 (by rfl) ⟨277958, by rfl⟩ : syracuseStep 370611 = 555917) B555917
theorem B370627 : Blo 366759 370627 := bstep (se 1 (by rfl) ⟨277970, by rfl⟩ : syracuseStep 370627 = 555941) B555941
theorem B698321 : Blo 366759 698321 := bstep (se 2 (by rfl) ⟨261870, by rfl⟩ : syracuseStep 698321 = 523741) B523741
theorem B370643 : Blo 366759 370643 := bstep (se 1 (by rfl) ⟨277982, by rfl⟩ : syracuseStep 370643 = 555965) B555965
theorem B370659 : Blo 366759 370659 := bstep (se 1 (by rfl) ⟨277994, by rfl⟩ : syracuseStep 370659 = 555989) B555989
theorem B370675 : Blo 366759 370675 := bstep (se 1 (by rfl) ⟨278006, by rfl⟩ : syracuseStep 370675 = 556013) B556013
theorem B370691 : Blo 366759 370691 := bstep (se 1 (by rfl) ⟨278018, by rfl⟩ : syracuseStep 370691 = 556037) B556037
theorem B829457 : Blo 366759 829457 := bstep (se 2 (by rfl) ⟨311046, by rfl⟩ : syracuseStep 829457 = 622093) B622093
theorem B370707 : Blo 366759 370707 := bstep (se 1 (by rfl) ⟨278030, by rfl⟩ : syracuseStep 370707 = 556061) B556061
theorem B829475 : Blo 366759 829475 := bstep (se 1 (by rfl) ⟨622106, by rfl⟩ : syracuseStep 829475 = 1244213) B1244213
theorem B370723 : Blo 366759 370723 := bstep (se 1 (by rfl) ⟨278042, by rfl⟩ : syracuseStep 370723 = 556085) B556085
theorem B370739 : Blo 366759 370739 := bstep (se 1 (by rfl) ⟨278054, by rfl⟩ : syracuseStep 370739 = 556109) B556109
theorem B370755 : Blo 366759 370755 := bstep (se 1 (by rfl) ⟨278066, by rfl⟩ : syracuseStep 370755 = 556133) B556133
theorem B469091 : Blo 366759 469091 := bstep (se 1 (by rfl) ⟨351818, by rfl⟩ : syracuseStep 469091 = 703637) B703637
theorem B1779853 : Blo 366759 1779853 := bstep (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) B667445
theorem B829745 : Blo 366759 829745 := bstep (se 2 (by rfl) ⟨311154, by rfl⟩ : syracuseStep 829745 = 622309) B622309
theorem B829763 : Blo 366759 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B600419 : Blo 366759 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B830033 : Blo 366759 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B830051 : Blo 366759 830051 := bstep (se 1 (by rfl) ⟨622538, by rfl⟩ : syracuseStep 830051 = 1245077) B1245077
theorem B2370161 : Blo 366759 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B699043 : Blo 366759 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B404227 : Blo 366759 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B830321 : Blo 366759 830321 := bstep (se 2 (by rfl) ⟨311370, by rfl⟩ : syracuseStep 830321 = 622741) B622741
theorem B830339 : Blo 366759 830339 := bstep (se 1 (by rfl) ⟨622754, by rfl⟩ : syracuseStep 830339 = 1245509) B1245509
theorem B1092557 : Blo 366759 1092557 := bstep (se 3 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 1092557 = 409709) B409709
theorem B7056355 : Blo 366759 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B3582947 : Blo 366759 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B1125389 : Blo 366759 1125389 := bstep (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) B422021
theorem B2108429 : Blo 366759 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B928817 : Blo 366759 928817 := bstep (se 2 (by rfl) ⟨348306, by rfl⟩ : syracuseStep 928817 = 696613) B696613
theorem B633923 : Blo 366759 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B928867 : Blo 366759 928867 := bstep (se 1 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 928867 = 1393301) B1393301
theorem B699491 : Blo 366759 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B3550321 : Blo 366759 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B5057677 : Blo 366759 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B830609 : Blo 366759 830609 := bstep (se 2 (by rfl) ⟨311478, by rfl⟩ : syracuseStep 830609 = 622957) B622957
theorem B601249 : Blo 366759 601249 := bstep (se 2 (by rfl) ⟨225468, by rfl⟩ : syracuseStep 601249 = 450937) B450937
theorem B830627 : Blo 366759 830627 := bstep (se 1 (by rfl) ⟨622970, by rfl⟩ : syracuseStep 830627 = 1245941) B1245941
theorem B929009 : Blo 366759 929009 := bstep (se 2 (by rfl) ⟨348378, by rfl⟩ : syracuseStep 929009 = 696757) B696757
theorem B2370829 : Blo 366759 2370829 := bstep (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) B889061
theorem B699779 : Blo 366759 699779 := bstep (se 1 (by rfl) ⟨524834, by rfl⟩ : syracuseStep 699779 = 1049669) B1049669
theorem B6040973 : Blo 366759 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B830897 : Blo 366759 830897 := bstep (se 2 (by rfl) ⟨311586, by rfl⟩ : syracuseStep 830897 = 623173) B623173
theorem B830915 : Blo 366759 830915 := bstep (se 1 (by rfl) ⟨623186, by rfl⟩ : syracuseStep 830915 = 1246373) B1246373
theorem B1125827 : Blo 366759 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B994801 : Blo 366759 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B1781297 : Blo 366759 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B831185 : Blo 366759 831185 := bstep (se 2 (by rfl) ⟨311694, by rfl⟩ : syracuseStep 831185 = 623389) B623389
theorem B831203 : Blo 366759 831203 := bstep (se 1 (by rfl) ⟨623402, by rfl⟩ : syracuseStep 831203 = 1246805) B1246805
theorem B2535245 : Blo 366759 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B2109361 : Blo 366759 2109361 := bstep (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) B1582021
theorem B831473 : Blo 366759 831473 := bstep (se 2 (by rfl) ⟨311802, by rfl⟩ : syracuseStep 831473 = 623605) B623605
theorem B831491 : Blo 366759 831491 := bstep (se 1 (by rfl) ⟨623618, by rfl⟩ : syracuseStep 831491 = 1247237) B1247237
theorem B536611 : Blo 366759 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B995501 : Blo 366759 995501 := bstep (se 3 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 995501 = 373313) B373313
theorem B1421489 : Blo 366759 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B930001 : Blo 366759 930001 := bstep (se 2 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 930001 = 697501) B697501
theorem B1257731 : Blo 366759 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B831761 : Blo 366759 831761 := bstep (se 2 (by rfl) ⟨311910, by rfl⟩ : syracuseStep 831761 = 623821) B623821
theorem B831779 : Blo 366759 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B700721 : Blo 366759 700721 := bstep (se 2 (by rfl) ⟨262770, by rfl⟩ : syracuseStep 700721 = 525541) B525541
theorem B1126801 : Blo 366759 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B799139 : Blo 366759 799139 := bstep (se 1 (by rfl) ⟨599354, by rfl⟩ : syracuseStep 799139 = 1198709) B1198709
theorem B930275 : Blo 366759 930275 := bstep (se 1 (by rfl) ⟨697706, by rfl⟩ : syracuseStep 930275 = 1395413) B1395413
theorem B832049 : Blo 366759 832049 := bstep (se 2 (by rfl) ⟨312018, by rfl⟩ : syracuseStep 832049 = 624037) B624037
theorem B832067 : Blo 366759 832067 := bstep (se 1 (by rfl) ⟨624050, by rfl⟩ : syracuseStep 832067 = 1248101) B1248101
theorem B10039949 : Blo 366759 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B864913 : Blo 366759 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B930467 : Blo 366759 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B832337 : Blo 366759 832337 := bstep (se 2 (by rfl) ⟨312126, by rfl⟩ : syracuseStep 832337 = 624253) B624253
theorem B832355 : Blo 366759 832355 := bstep (se 1 (by rfl) ⟨624266, by rfl⟩ : syracuseStep 832355 = 1248533) B1248533
theorem B1127459 : Blo 366759 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B832625 : Blo 366759 832625 := bstep (se 2 (by rfl) ⟨312234, by rfl⟩ : syracuseStep 832625 = 624469) B624469
theorem B832643 : Blo 366759 832643 := bstep (se 1 (by rfl) ⟨624482, by rfl⟩ : syracuseStep 832643 = 1248965) B1248965
theorem B898211 : Blo 366759 898211 := bstep (se 1 (by rfl) ⟨673658, by rfl⟩ : syracuseStep 898211 = 1347317) B1347317
theorem B701617 : Blo 366759 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B10073315 : Blo 366759 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B701777 : Blo 366759 701777 := bstep (se 2 (by rfl) ⟨263166, by rfl⟩ : syracuseStep 701777 = 526333) B526333
theorem B3159395 : Blo 366759 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B2110819 : Blo 366759 2110819 := bstep (se 1 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 2110819 = 3166229) B3166229
theorem B832913 : Blo 366759 832913 := bstep (se 2 (by rfl) ⟨312342, by rfl⟩ : syracuseStep 832913 = 624685) B624685
theorem B1324451 : Blo 366759 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B832931 : Blo 366759 832931 := bstep (se 1 (by rfl) ⟨624698, by rfl⟩ : syracuseStep 832931 = 1249397) B1249397
theorem B931409 : Blo 366759 931409 := bstep (se 2 (by rfl) ⟨349278, by rfl⟩ : syracuseStep 931409 = 698557) B698557
theorem B931459 : Blo 366759 931459 := bstep (se 1 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 931459 = 1397189) B1397189
theorem B833201 : Blo 366759 833201 := bstep (se 2 (by rfl) ⟨312450, by rfl⟩ : syracuseStep 833201 = 624901) B624901
theorem B833219 : Blo 366759 833219 := bstep (se 1 (by rfl) ⟨624914, by rfl⟩ : syracuseStep 833219 = 1249829) B1249829
theorem B702179 : Blo 366759 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B931601 : Blo 366759 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B2111345 : Blo 366759 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B833489 : Blo 366759 833489 := bstep (se 2 (by rfl) ⟨312558, by rfl⟩ : syracuseStep 833489 = 625117) B625117
theorem B833507 : Blo 366759 833507 := bstep (se 1 (by rfl) ⟨625130, by rfl⟩ : syracuseStep 833507 = 1250261) B1250261
theorem B833777 : Blo 366759 833777 := bstep (se 2 (by rfl) ⟨312666, by rfl⟩ : syracuseStep 833777 = 625333) B625333
theorem B833795 : Blo 366759 833795 := bstep (se 1 (by rfl) ⟨625346, by rfl⟩ : syracuseStep 833795 = 1250693) B1250693
theorem B1325489 : Blo 366759 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B834065 : Blo 366759 834065 := bstep (se 2 (by rfl) ⟨312774, by rfl⟩ : syracuseStep 834065 = 625549) B625549
theorem B834083 : Blo 366759 834083 := bstep (se 1 (by rfl) ⟨625562, by rfl⟩ : syracuseStep 834083 = 1251125) B1251125
theorem B703075 : Blo 366759 703075 := bstep (se 1 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 703075 = 1054613) B1054613
theorem B932593 : Blo 366759 932593 := bstep (se 2 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 932593 = 699445) B699445
theorem B703235 : Blo 366759 703235 := bstep (se 1 (by rfl) ⟨527426, by rfl⟩ : syracuseStep 703235 = 1054853) B1054853
theorem B2243555 : Blo 366759 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B736259 : Blo 366759 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B932867 : Blo 366759 932867 := bstep (se 1 (by rfl) ⟨699650, by rfl⟩ : syracuseStep 932867 = 1399301) B1399301
theorem B933059 : Blo 366759 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B998605 : Blo 366759 998605 := bstep (se 3 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 998605 = 374477) B374477
theorem B441715 : Blo 366759 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B2244017 : Blo 366759 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B442099 : Blo 366759 442099 := bstep (se 1 (by rfl) ⟨331574, by rfl⟩ : syracuseStep 442099 = 663149) B663149
theorem B1261453 : Blo 366759 1261453 := bstep (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) B473045
theorem B540577 : Blo 366759 540577 := bstep (se 2 (by rfl) ⟨202716, by rfl⟩ : syracuseStep 540577 = 405433) B405433
theorem B606289 : Blo 366759 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B934001 : Blo 366759 934001 := bstep (se 2 (by rfl) ⟨350250, by rfl⟩ : syracuseStep 934001 = 700501) B700501
theorem B934051 : Blo 366759 934051 := bstep (se 1 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 934051 = 1401077) B1401077
theorem B934193 : Blo 366759 934193 := bstep (se 2 (by rfl) ⟨350322, by rfl⟩ : syracuseStep 934193 = 700645) B700645
theorem B2244941 : Blo 366759 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B2802275 : Blo 366759 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B1000109 : Blo 366759 1000109 := bstep (se 3 (by rfl) ⟨187520, by rfl⟩ : syracuseStep 1000109 = 375041) B375041
theorem B1983217 : Blo 366759 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B4801265 : Blo 366759 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B1000259 : Blo 366759 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B935185 : Blo 366759 935185 := bstep (se 2 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 935185 = 701389) B701389
theorem B1393955 : Blo 366759 1393955 := bstep (se 1 (by rfl) ⟨1045466, by rfl⟩ : syracuseStep 1393955 = 2090933) B2090933
theorem B1393969 : Blo 366759 1393969 := bstep (se 2 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 1393969 = 1045477) B1045477
theorem B1263053 : Blo 366759 1263053 := bstep (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) B473645
theorem B935459 : Blo 366759 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B935651 : Blo 366759 935651 := bstep (se 1 (by rfl) ⟨701738, by rfl⟩ : syracuseStep 935651 = 1403477) B1403477
theorem B673571 : Blo 366759 673571 := bstep (se 1 (by rfl) ⟨505178, by rfl⟩ : syracuseStep 673571 = 1010357) B1010357
theorem B4474693 : Blo 366759 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B575905 : Blo 366759 575905 := bstep (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) B431929
theorem B510449 : Blo 366759 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B936593 : Blo 366759 936593 := bstep (se 2 (by rfl) ⟨351222, by rfl⟩ : syracuseStep 936593 = 702445) B702445
theorem B936643 : Blo 366759 936643 := bstep (se 1 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 936643 = 1404965) B1404965
theorem B1395427 : Blo 366759 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B936785 : Blo 366759 936785 := bstep (se 2 (by rfl) ⟨351294, by rfl⟩ : syracuseStep 936785 = 702589) B702589
theorem B412627 : Blo 366759 412627 := bstep (se 1 (by rfl) ⟨309470, by rfl⟩ : syracuseStep 412627 = 618941) B618941
theorem B707665 : Blo 366759 707665 := bstep (se 2 (by rfl) ⟨265374, by rfl⟩ : syracuseStep 707665 = 530749) B530749
theorem B412771 : Blo 366759 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B5950691 : Blo 366759 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B412915 : Blo 366759 412915 := bstep (se 1 (by rfl) ⟨309686, by rfl⟩ : syracuseStep 412915 = 619373) B619373
theorem B413059 : Blo 366759 413059 := bstep (se 1 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 413059 = 619589) B619589
theorem B413203 : Blo 366759 413203 := bstep (se 1 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 413203 = 619805) B619805
theorem B413347 : Blo 366759 413347 := bstep (se 1 (by rfl) ⟨310010, by rfl⟩ : syracuseStep 413347 = 620021) B620021
theorem B937777 : Blo 366759 937777 := bstep (se 2 (by rfl) ⟨351666, by rfl⟩ : syracuseStep 937777 = 703333) B703333
theorem B413491 : Blo 366759 413491 := bstep (se 1 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 413491 = 620237) B620237
theorem B839555 : Blo 366759 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B413635 : Blo 366759 413635 := bstep (se 1 (by rfl) ⟨310226, by rfl⟩ : syracuseStep 413635 = 620453) B620453
theorem B938051 : Blo 366759 938051 := bstep (se 1 (by rfl) ⟨703538, by rfl⟩ : syracuseStep 938051 = 1407077) B1407077
theorem B413779 : Blo 366759 413779 := bstep (se 1 (by rfl) ⟨310334, by rfl⟩ : syracuseStep 413779 = 620669) B620669
theorem B413923 : Blo 366759 413923 := bstep (se 1 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 413923 = 620885) B620885
theorem B938243 : Blo 366759 938243 := bstep (se 1 (by rfl) ⟨703682, by rfl⟩ : syracuseStep 938243 = 1407365) B1407365
theorem B414067 : Blo 366759 414067 := bstep (se 1 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 414067 = 621101) B621101
theorem B1331633 : Blo 366759 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B414211 : Blo 366759 414211 := bstep (se 1 (by rfl) ⟨310658, by rfl⟩ : syracuseStep 414211 = 621317) B621317
theorem B414355 : Blo 366759 414355 := bstep (se 1 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 414355 = 621533) B621533
theorem B3986117 : Blo 366759 3986117 := bstep (se 4 (by rfl) ⟨373698, by rfl⟩ : syracuseStep 3986117 = 747397) B747397
theorem B414499 : Blo 366759 414499 := bstep (se 1 (by rfl) ⟨310874, by rfl⟩ : syracuseStep 414499 = 621749) B621749
theorem B4051781 : Blo 366759 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B1397645 : Blo 366759 1397645 := bstep (se 3 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 1397645 = 524117) B524117
theorem B414643 : Blo 366759 414643 := bstep (se 1 (by rfl) ⟨310982, by rfl⟩ : syracuseStep 414643 = 621965) B621965
theorem B414787 : Blo 366759 414787 := bstep (se 1 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 414787 = 622181) B622181
theorem B1496141 : Blo 366759 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B414931 : Blo 366759 414931 := bstep (se 1 (by rfl) ⟨311198, by rfl⟩ : syracuseStep 414931 = 622397) B622397
theorem B1332557 : Blo 366759 1332557 := bstep (se 3 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 1332557 = 499709) B499709
theorem B415075 : Blo 366759 415075 := bstep (se 1 (by rfl) ⟨311306, by rfl⟩ : syracuseStep 415075 = 622613) B622613
theorem B3134861 : Blo 366759 3134861 := bstep (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) B1175573
theorem B415219 : Blo 366759 415219 := bstep (se 1 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 415219 = 622829) B622829
theorem B1365581 : Blo 366759 1365581 := bstep (se 3 (by rfl) ⟨256046, by rfl⟩ : syracuseStep 1365581 = 512093) B512093
theorem B415363 : Blo 366759 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B415507 : Blo 366759 415507 := bstep (se 1 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 415507 = 623261) B623261
theorem B1857329 : Blo 366759 1857329 := bstep (se 2 (by rfl) ⟨696498, by rfl⟩ : syracuseStep 1857329 = 1392997) B1392997
theorem B2807621 : Blo 366759 2807621 := bstep (se 4 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 2807621 = 526429) B526429
theorem B415651 : Blo 366759 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B841699 : Blo 366759 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B415795 : Blo 366759 415795 := bstep (se 1 (by rfl) ⟨311846, by rfl⟩ : syracuseStep 415795 = 623693) B623693
theorem B14211125 : Blo 366759 14211125 := bstep (se 5 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 14211125 = 1332293) B1332293
theorem B415939 : Blo 366759 415939 := bstep (se 1 (by rfl) ⟨311954, by rfl⟩ : syracuseStep 415939 = 623909) B623909
theorem B416083 : Blo 366759 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B416227 : Blo 366759 416227 := bstep (se 1 (by rfl) ⟨312170, by rfl⟩ : syracuseStep 416227 = 624341) B624341
theorem B9624035 : Blo 366759 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B4381253 : Blo 366759 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B416371 : Blo 366759 416371 := bstep (se 1 (by rfl) ⟨312278, by rfl⟩ : syracuseStep 416371 = 624557) B624557
theorem B416515 : Blo 366759 416515 := bstep (se 1 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 416515 = 624773) B624773
theorem B3627917 : Blo 366759 3627917 := bstep (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) B1360469
theorem B416659 : Blo 366759 416659 := bstep (se 1 (by rfl) ⟨312494, by rfl⟩ : syracuseStep 416659 = 624989) B624989
theorem B416803 : Blo 366759 416803 := bstep (se 1 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 416803 = 625205) B625205
theorem B416947 : Blo 366759 416947 := bstep (se 1 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 416947 = 625421) B625421
theorem B1858787 : Blo 366759 1858787 := bstep (se 1 (by rfl) ⟨1394090, by rfl⟩ : syracuseStep 1858787 = 2788181) B2788181
theorem B417091 : Blo 366759 417091 := bstep (se 1 (by rfl) ⟨312818, by rfl⟩ : syracuseStep 417091 = 625637) B625637
theorem B1498445 : Blo 366759 1498445 := bstep (se 3 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 1498445 = 561917) B561917
theorem B3137251 : Blo 366759 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1400561 : Blo 366759 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B712547 : Blo 366759 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B450451 : Blo 366759 450451 := bstep (se 1 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 450451 = 675677) B675677
theorem B1859597 : Blo 366759 1859597 := bstep (se 3 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 1859597 = 697349) B697349
theorem B1335523 : Blo 366759 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B1696099 : Blo 366759 1696099 := bstep (se 1 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 1696099 = 2544149) B2544149
theorem B745841 : Blo 366759 745841 := bstep (se 2 (by rfl) ⟨279690, by rfl⟩ : syracuseStep 745841 = 559381) B559381
theorem B1237841 : Blo 366759 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B844625 : Blo 366759 844625 := bstep (se 2 (by rfl) ⟨316734, by rfl⟩ : syracuseStep 844625 = 633469) B633469
theorem B1893347 : Blo 366759 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B1402019 : Blo 366759 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B2090225 : Blo 366759 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B550145 : Blo 366759 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B550163 : Blo 366759 550163 := bstep (se 1 (by rfl) ⟨412622, by rfl⟩ : syracuseStep 550163 = 825245) B825245
theorem B550193 : Blo 366759 550193 := bstep (se 2 (by rfl) ⟨206322, by rfl⟩ : syracuseStep 550193 = 412645) B412645
theorem B550211 : Blo 366759 550211 := bstep (se 1 (by rfl) ⟨412658, by rfl⟩ : syracuseStep 550211 = 825317) B825317
theorem B2385229 : Blo 366759 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B517457 : Blo 366759 517457 := bstep (se 2 (by rfl) ⟨194046, by rfl⟩ : syracuseStep 517457 = 388093) B388093
theorem B550241 : Blo 366759 550241 := bstep (se 2 (by rfl) ⟨206340, by rfl⟩ : syracuseStep 550241 = 412681) B412681
theorem B1238381 : Blo 366759 1238381 := bstep (se 3 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 1238381 = 464393) B464393
theorem B550259 : Blo 366759 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B550289 : Blo 366759 550289 := bstep (se 2 (by rfl) ⟨206358, by rfl⟩ : syracuseStep 550289 = 412717) B412717
theorem B550307 : Blo 366759 550307 := bstep (se 1 (by rfl) ⟨412730, by rfl⟩ : syracuseStep 550307 = 825461) B825461
theorem B1238435 : Blo 366759 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B550337 : Blo 366759 550337 := bstep (se 2 (by rfl) ⟨206376, by rfl⟩ : syracuseStep 550337 = 412753) B412753
theorem B550355 : Blo 366759 550355 := bstep (se 1 (by rfl) ⟨412766, by rfl⟩ : syracuseStep 550355 = 825533) B825533
theorem B550385 : Blo 366759 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B550403 : Blo 366759 550403 := bstep (se 1 (by rfl) ⟨412802, by rfl⟩ : syracuseStep 550403 = 825605) B825605
theorem B550433 : Blo 366759 550433 := bstep (se 2 (by rfl) ⟨206412, by rfl⟩ : syracuseStep 550433 = 412825) B412825
theorem B550451 : Blo 366759 550451 := bstep (se 1 (by rfl) ⟨412838, by rfl⟩ : syracuseStep 550451 = 825677) B825677
theorem B550481 : Blo 366759 550481 := bstep (se 2 (by rfl) ⟨206430, by rfl⟩ : syracuseStep 550481 = 412861) B412861
theorem B550499 : Blo 366759 550499 := bstep (se 1 (by rfl) ⟨412874, by rfl⟩ : syracuseStep 550499 = 825749) B825749
theorem B2418275 : Blo 366759 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B550529 : Blo 366759 550529 := bstep (se 2 (by rfl) ⟨206448, by rfl⟩ : syracuseStep 550529 = 412897) B412897
theorem B550547 : Blo 366759 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B1238705 : Blo 366759 1238705 := bstep (se 2 (by rfl) ⟨464514, by rfl⟩ : syracuseStep 1238705 = 929029) B929029
theorem B550577 : Blo 366759 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B550595 : Blo 366759 550595 := bstep (se 1 (by rfl) ⟨412946, by rfl⟩ : syracuseStep 550595 = 825893) B825893
theorem B550625 : Blo 366759 550625 := bstep (se 2 (by rfl) ⟨206484, by rfl⟩ : syracuseStep 550625 = 412969) B412969
theorem B550643 : Blo 366759 550643 := bstep (se 1 (by rfl) ⟨412982, by rfl⟩ : syracuseStep 550643 = 825965) B825965
theorem B550673 : Blo 366759 550673 := bstep (se 2 (by rfl) ⟨206502, by rfl⟩ : syracuseStep 550673 = 413005) B413005
theorem B550691 : Blo 366759 550691 := bstep (se 1 (by rfl) ⟨413018, by rfl⟩ : syracuseStep 550691 = 826037) B826037
theorem B550721 : Blo 366759 550721 := bstep (se 2 (by rfl) ⟨206520, by rfl⟩ : syracuseStep 550721 = 413041) B413041
theorem B550739 : Blo 366759 550739 := bstep (se 1 (by rfl) ⟨413054, by rfl⟩ : syracuseStep 550739 = 826109) B826109
theorem B550769 : Blo 366759 550769 := bstep (se 2 (by rfl) ⟨206538, by rfl⟩ : syracuseStep 550769 = 413077) B413077
theorem B550787 : Blo 366759 550787 := bstep (se 1 (by rfl) ⟨413090, by rfl⟩ : syracuseStep 550787 = 826181) B826181
theorem B550817 : Blo 366759 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B550835 : Blo 366759 550835 := bstep (se 1 (by rfl) ⟨413126, by rfl⟩ : syracuseStep 550835 = 826253) B826253
theorem B550865 : Blo 366759 550865 := bstep (se 2 (by rfl) ⟨206574, by rfl⟩ : syracuseStep 550865 = 413149) B413149
theorem B550883 : Blo 366759 550883 := bstep (se 1 (by rfl) ⟨413162, by rfl⟩ : syracuseStep 550883 = 826325) B826325
theorem B550913 : Blo 366759 550913 := bstep (se 2 (by rfl) ⟨206592, by rfl⟩ : syracuseStep 550913 = 413185) B413185
theorem B550931 : Blo 366759 550931 := bstep (se 1 (by rfl) ⟨413198, by rfl⟩ : syracuseStep 550931 = 826397) B826397
theorem B550961 : Blo 366759 550961 := bstep (se 2 (by rfl) ⟨206610, by rfl⟩ : syracuseStep 550961 = 413221) B413221
theorem B550979 : Blo 366759 550979 := bstep (se 1 (by rfl) ⟨413234, by rfl⟩ : syracuseStep 550979 = 826469) B826469
theorem B551009 : Blo 366759 551009 := bstep (se 2 (by rfl) ⟨206628, by rfl⟩ : syracuseStep 551009 = 413257) B413257
theorem B551027 : Blo 366759 551027 := bstep (se 1 (by rfl) ⟨413270, by rfl⟩ : syracuseStep 551027 = 826541) B826541
theorem B1403021 : Blo 366759 1403021 := bstep (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) B526133
theorem B551057 : Blo 366759 551057 := bstep (se 2 (by rfl) ⟨206646, by rfl⟩ : syracuseStep 551057 = 413293) B413293
theorem B551075 : Blo 366759 551075 := bstep (se 1 (by rfl) ⟨413306, by rfl⟩ : syracuseStep 551075 = 826613) B826613
theorem B551105 : Blo 366759 551105 := bstep (se 2 (by rfl) ⟨206664, by rfl⟩ : syracuseStep 551105 = 413329) B413329
theorem B2353349 : Blo 366759 2353349 := bstep (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) B441253
theorem B1239245 : Blo 366759 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B1009873 : Blo 366759 1009873 := bstep (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) B757405
theorem B551123 : Blo 366759 551123 := bstep (se 1 (by rfl) ⟨413342, by rfl⟩ : syracuseStep 551123 = 826685) B826685
theorem B551153 : Blo 366759 551153 := bstep (se 2 (by rfl) ⟨206682, by rfl⟩ : syracuseStep 551153 = 413365) B413365
theorem B551171 : Blo 366759 551171 := bstep (se 1 (by rfl) ⟨413378, by rfl⟩ : syracuseStep 551171 = 826757) B826757
theorem B1239299 : Blo 366759 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B551201 : Blo 366759 551201 := bstep (se 2 (by rfl) ⟨206700, by rfl⟩ : syracuseStep 551201 = 413401) B413401
theorem B551219 : Blo 366759 551219 := bstep (se 1 (by rfl) ⟨413414, by rfl⟩ : syracuseStep 551219 = 826829) B826829
theorem B551249 : Blo 366759 551249 := bstep (se 2 (by rfl) ⟨206718, by rfl⟩ : syracuseStep 551249 = 413437) B413437
theorem B551267 : Blo 366759 551267 := bstep (se 1 (by rfl) ⟨413450, by rfl⟩ : syracuseStep 551267 = 826901) B826901
theorem B551297 : Blo 366759 551297 := bstep (se 2 (by rfl) ⟨206736, by rfl⟩ : syracuseStep 551297 = 413473) B413473
theorem B551315 : Blo 366759 551315 := bstep (se 1 (by rfl) ⟨413486, by rfl⟩ : syracuseStep 551315 = 826973) B826973
theorem B551345 : Blo 366759 551345 := bstep (se 2 (by rfl) ⟨206754, by rfl⟩ : syracuseStep 551345 = 413509) B413509
theorem B551363 : Blo 366759 551363 := bstep (se 1 (by rfl) ⟨413522, by rfl⟩ : syracuseStep 551363 = 827045) B827045
theorem B551393 : Blo 366759 551393 := bstep (se 2 (by rfl) ⟨206772, by rfl⟩ : syracuseStep 551393 = 413545) B413545
theorem B551411 : Blo 366759 551411 := bstep (se 1 (by rfl) ⟨413558, by rfl⟩ : syracuseStep 551411 = 827117) B827117
theorem B1239569 : Blo 366759 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B551441 : Blo 366759 551441 := bstep (se 2 (by rfl) ⟨206790, by rfl⟩ : syracuseStep 551441 = 413581) B413581
theorem B551459 : Blo 366759 551459 := bstep (se 1 (by rfl) ⟨413594, by rfl⟩ : syracuseStep 551459 = 827189) B827189
theorem B551489 : Blo 366759 551489 := bstep (se 2 (by rfl) ⟨206808, by rfl⟩ : syracuseStep 551489 = 413617) B413617
theorem B551507 : Blo 366759 551507 := bstep (se 1 (by rfl) ⟨413630, by rfl⟩ : syracuseStep 551507 = 827261) B827261
theorem B551537 : Blo 366759 551537 := bstep (se 2 (by rfl) ⟨206826, by rfl⟩ : syracuseStep 551537 = 413653) B413653
theorem B551555 : Blo 366759 551555 := bstep (se 1 (by rfl) ⟨413666, by rfl⟩ : syracuseStep 551555 = 827333) B827333
theorem B551585 : Blo 366759 551585 := bstep (se 2 (by rfl) ⟨206844, by rfl⟩ : syracuseStep 551585 = 413689) B413689
theorem B2091683 : Blo 366759 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B551603 : Blo 366759 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B551633 : Blo 366759 551633 := bstep (se 2 (by rfl) ⟨206862, by rfl⟩ : syracuseStep 551633 = 413725) B413725
theorem B551651 : Blo 366759 551651 := bstep (se 1 (by rfl) ⟨413738, by rfl⟩ : syracuseStep 551651 = 827477) B827477
theorem B10775267 : Blo 366759 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B551681 : Blo 366759 551681 := bstep (se 2 (by rfl) ⟨206880, by rfl⟩ : syracuseStep 551681 = 413761) B413761
theorem B551699 : Blo 366759 551699 := bstep (se 1 (by rfl) ⟨413774, by rfl⟩ : syracuseStep 551699 = 827549) B827549
theorem B551729 : Blo 366759 551729 := bstep (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) B413797
theorem B551747 : Blo 366759 551747 := bstep (se 1 (by rfl) ⟨413810, by rfl⟩ : syracuseStep 551747 = 827621) B827621
theorem B551777 : Blo 366759 551777 := bstep (se 2 (by rfl) ⟨206916, by rfl⟩ : syracuseStep 551777 = 413833) B413833
theorem B1862513 : Blo 366759 1862513 := bstep (se 2 (by rfl) ⟨698442, by rfl⟩ : syracuseStep 1862513 = 1396885) B1396885
theorem B551795 : Blo 366759 551795 := bstep (se 1 (by rfl) ⟨413846, by rfl⟩ : syracuseStep 551795 = 827693) B827693
theorem B551825 : Blo 366759 551825 := bstep (se 2 (by rfl) ⟨206934, by rfl⟩ : syracuseStep 551825 = 413869) B413869
theorem B551843 : Blo 366759 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B551873 : Blo 366759 551873 := bstep (se 2 (by rfl) ⟨206952, by rfl⟩ : syracuseStep 551873 = 413905) B413905
theorem B551891 : Blo 366759 551891 := bstep (se 1 (by rfl) ⟨413918, by rfl⟩ : syracuseStep 551891 = 827837) B827837
theorem B551921 : Blo 366759 551921 := bstep (se 2 (by rfl) ⟨206970, by rfl⟩ : syracuseStep 551921 = 413941) B413941
theorem B551939 : Blo 366759 551939 := bstep (se 1 (by rfl) ⟨413954, by rfl⟩ : syracuseStep 551939 = 827909) B827909
theorem B551969 : Blo 366759 551969 := bstep (se 2 (by rfl) ⟨206988, by rfl⟩ : syracuseStep 551969 = 413977) B413977
theorem B1240109 : Blo 366759 1240109 := bstep (se 3 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 1240109 = 465041) B465041
theorem B551987 : Blo 366759 551987 := bstep (se 1 (by rfl) ⟨413990, by rfl⟩ : syracuseStep 551987 = 827981) B827981
theorem B552017 : Blo 366759 552017 := bstep (se 2 (by rfl) ⟨207006, by rfl⟩ : syracuseStep 552017 = 414013) B414013
theorem B1240163 : Blo 366759 1240163 := bstep (se 1 (by rfl) ⟨930122, by rfl⟩ : syracuseStep 1240163 = 1860245) B1860245
theorem B552035 : Blo 366759 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B552065 : Blo 366759 552065 := bstep (se 2 (by rfl) ⟨207024, by rfl⟩ : syracuseStep 552065 = 414049) B414049
theorem B552083 : Blo 366759 552083 := bstep (se 1 (by rfl) ⟨414062, by rfl⟩ : syracuseStep 552083 = 828125) B828125
theorem B552113 : Blo 366759 552113 := bstep (se 2 (by rfl) ⟨207042, by rfl⟩ : syracuseStep 552113 = 414085) B414085
theorem B552131 : Blo 366759 552131 := bstep (se 1 (by rfl) ⟨414098, by rfl⟩ : syracuseStep 552131 = 828197) B828197
theorem B945361 : Blo 366759 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B552161 : Blo 366759 552161 := bstep (se 2 (by rfl) ⟨207060, by rfl⟩ : syracuseStep 552161 = 414121) B414121
theorem B552179 : Blo 366759 552179 := bstep (se 1 (by rfl) ⟨414134, by rfl⟩ : syracuseStep 552179 = 828269) B828269
theorem B552209 : Blo 366759 552209 := bstep (se 2 (by rfl) ⟨207078, by rfl⟩ : syracuseStep 552209 = 414157) B414157
theorem B552227 : Blo 366759 552227 := bstep (se 1 (by rfl) ⟨414170, by rfl⟩ : syracuseStep 552227 = 828341) B828341
theorem B552257 : Blo 366759 552257 := bstep (se 2 (by rfl) ⟨207096, by rfl⟩ : syracuseStep 552257 = 414193) B414193
theorem B552275 : Blo 366759 552275 := bstep (se 1 (by rfl) ⟨414206, by rfl⟩ : syracuseStep 552275 = 828413) B828413
theorem B1240433 : Blo 366759 1240433 := bstep (se 2 (by rfl) ⟨465162, by rfl⟩ : syracuseStep 1240433 = 930325) B930325
theorem B552305 : Blo 366759 552305 := bstep (se 2 (by rfl) ⟨207114, by rfl⟩ : syracuseStep 552305 = 414229) B414229
theorem B552323 : Blo 366759 552323 := bstep (se 1 (by rfl) ⟨414242, by rfl⟩ : syracuseStep 552323 = 828485) B828485
theorem B552353 : Blo 366759 552353 := bstep (se 2 (by rfl) ⟨207132, by rfl⟩ : syracuseStep 552353 = 414265) B414265
theorem B552371 : Blo 366759 552371 := bstep (se 1 (by rfl) ⟨414278, by rfl⟩ : syracuseStep 552371 = 828557) B828557
theorem B552401 : Blo 366759 552401 := bstep (se 2 (by rfl) ⟨207150, by rfl⟩ : syracuseStep 552401 = 414301) B414301
theorem B552419 : Blo 366759 552419 := bstep (se 1 (by rfl) ⟨414314, by rfl⟩ : syracuseStep 552419 = 828629) B828629
theorem B749027 : Blo 366759 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B552449 : Blo 366759 552449 := bstep (se 2 (by rfl) ⟨207168, by rfl⟩ : syracuseStep 552449 = 414337) B414337
theorem B2813453 : Blo 366759 2813453 := bstep (se 3 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 2813453 = 1055045) B1055045
theorem B552467 : Blo 366759 552467 := bstep (se 1 (by rfl) ⟨414350, by rfl⟩ : syracuseStep 552467 = 828701) B828701
theorem B1764899 : Blo 366759 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B552497 : Blo 366759 552497 := bstep (se 2 (by rfl) ⟨207186, by rfl⟩ : syracuseStep 552497 = 414373) B414373
theorem B552515 : Blo 366759 552515 := bstep (se 1 (by rfl) ⟨414386, by rfl⟩ : syracuseStep 552515 = 828773) B828773
theorem B552545 : Blo 366759 552545 := bstep (se 2 (by rfl) ⟨207204, by rfl⟩ : syracuseStep 552545 = 414409) B414409
theorem B552563 : Blo 366759 552563 := bstep (se 1 (by rfl) ⟨414422, by rfl⟩ : syracuseStep 552563 = 828845) B828845
theorem B552593 : Blo 366759 552593 := bstep (se 2 (by rfl) ⟨207222, by rfl⟩ : syracuseStep 552593 = 414445) B414445
theorem B552611 : Blo 366759 552611 := bstep (se 1 (by rfl) ⟨414458, by rfl⟩ : syracuseStep 552611 = 828917) B828917
theorem B552641 : Blo 366759 552641 := bstep (se 2 (by rfl) ⟨207240, by rfl⟩ : syracuseStep 552641 = 414481) B414481
theorem B552659 : Blo 366759 552659 := bstep (se 1 (by rfl) ⟨414494, by rfl⟩ : syracuseStep 552659 = 828989) B828989
theorem B1765091 : Blo 366759 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B552689 : Blo 366759 552689 := bstep (se 2 (by rfl) ⟨207258, by rfl⟩ : syracuseStep 552689 = 414517) B414517
theorem B552707 : Blo 366759 552707 := bstep (se 1 (by rfl) ⟨414530, by rfl⟩ : syracuseStep 552707 = 829061) B829061
theorem B552737 : Blo 366759 552737 := bstep (se 2 (by rfl) ⟨207276, by rfl⟩ : syracuseStep 552737 = 414553) B414553
theorem B552755 : Blo 366759 552755 := bstep (se 1 (by rfl) ⟨414566, by rfl⟩ : syracuseStep 552755 = 829133) B829133
theorem B552785 : Blo 366759 552785 := bstep (se 2 (by rfl) ⟨207294, by rfl⟩ : syracuseStep 552785 = 414589) B414589
theorem B552803 : Blo 366759 552803 := bstep (se 1 (by rfl) ⟨414602, by rfl⟩ : syracuseStep 552803 = 829205) B829205
theorem B552833 : Blo 366759 552833 := bstep (se 2 (by rfl) ⟨207312, by rfl⟩ : syracuseStep 552833 = 414625) B414625
theorem B1240973 : Blo 366759 1240973 := bstep (se 3 (by rfl) ⟨232682, by rfl⟩ : syracuseStep 1240973 = 465365) B465365
theorem B552851 : Blo 366759 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B552881 : Blo 366759 552881 := bstep (se 2 (by rfl) ⟨207330, by rfl⟩ : syracuseStep 552881 = 414661) B414661
theorem B1241027 : Blo 366759 1241027 := bstep (se 1 (by rfl) ⟨930770, by rfl⟩ : syracuseStep 1241027 = 1861541) B1861541
theorem B552899 : Blo 366759 552899 := bstep (se 1 (by rfl) ⟨414674, by rfl⟩ : syracuseStep 552899 = 829349) B829349
theorem B552929 : Blo 366759 552929 := bstep (se 2 (by rfl) ⟨207348, by rfl⟩ : syracuseStep 552929 = 414697) B414697
theorem B552947 : Blo 366759 552947 := bstep (se 1 (by rfl) ⟨414710, by rfl⟩ : syracuseStep 552947 = 829421) B829421
theorem B552977 : Blo 366759 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B552995 : Blo 366759 552995 := bstep (se 1 (by rfl) ⟨414746, by rfl⟩ : syracuseStep 552995 = 829493) B829493
theorem B553025 : Blo 366759 553025 := bstep (se 2 (by rfl) ⟨207384, by rfl⟩ : syracuseStep 553025 = 414769) B414769
theorem B553043 : Blo 366759 553043 := bstep (se 1 (by rfl) ⟨414782, by rfl⟩ : syracuseStep 553043 = 829565) B829565
theorem B1765475 : Blo 366759 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B1044589 : Blo 366759 1044589 := bstep (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) B391721
theorem B553073 : Blo 366759 553073 := bstep (se 2 (by rfl) ⟨207402, by rfl⟩ : syracuseStep 553073 = 414805) B414805
theorem B553091 : Blo 366759 553091 := bstep (se 1 (by rfl) ⟨414818, by rfl⟩ : syracuseStep 553091 = 829637) B829637
theorem B553121 : Blo 366759 553121 := bstep (se 2 (by rfl) ⟨207420, by rfl⟩ : syracuseStep 553121 = 414841) B414841
theorem B553139 : Blo 366759 553139 := bstep (se 1 (by rfl) ⟨414854, by rfl⟩ : syracuseStep 553139 = 829709) B829709
theorem B1405133 : Blo 366759 1405133 := bstep (se 3 (by rfl) ⟨263462, by rfl⟩ : syracuseStep 1405133 = 526925) B526925
theorem B1241297 : Blo 366759 1241297 := bstep (se 2 (by rfl) ⟨465486, by rfl⟩ : syracuseStep 1241297 = 930973) B930973
theorem B553169 : Blo 366759 553169 := bstep (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) B414877
theorem B553187 : Blo 366759 553187 := bstep (se 1 (by rfl) ⟨414890, by rfl⟩ : syracuseStep 553187 = 829781) B829781
theorem B553217 : Blo 366759 553217 := bstep (se 2 (by rfl) ⟨207456, by rfl⟩ : syracuseStep 553217 = 414913) B414913
theorem B553235 : Blo 366759 553235 := bstep (se 1 (by rfl) ⟨414926, by rfl⟩ : syracuseStep 553235 = 829853) B829853
theorem B1863971 : Blo 366759 1863971 := bstep (se 1 (by rfl) ⟨1397978, by rfl⟩ : syracuseStep 1863971 = 2795957) B2795957
theorem B553265 : Blo 366759 553265 := bstep (se 2 (by rfl) ⟨207474, by rfl⟩ : syracuseStep 553265 = 414949) B414949
theorem B553283 : Blo 366759 553283 := bstep (se 1 (by rfl) ⟨414962, by rfl⟩ : syracuseStep 553283 = 829925) B829925
theorem B553313 : Blo 366759 553313 := bstep (se 2 (by rfl) ⟨207492, by rfl⟩ : syracuseStep 553313 = 414985) B414985
theorem B553331 : Blo 366759 553331 := bstep (se 1 (by rfl) ⟨414998, by rfl⟩ : syracuseStep 553331 = 829997) B829997
theorem B553361 : Blo 366759 553361 := bstep (se 2 (by rfl) ⟨207510, by rfl⟩ : syracuseStep 553361 = 415021) B415021
theorem B553379 : Blo 366759 553379 := bstep (se 1 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 553379 = 830069) B830069
theorem B553409 : Blo 366759 553409 := bstep (se 2 (by rfl) ⟨207528, by rfl⟩ : syracuseStep 553409 = 415057) B415057
theorem B618961 : Blo 366759 618961 := bstep (se 2 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 618961 = 464221) B464221
theorem B553427 : Blo 366759 553427 := bstep (se 1 (by rfl) ⟨415070, by rfl⟩ : syracuseStep 553427 = 830141) B830141
theorem B553457 : Blo 366759 553457 := bstep (se 2 (by rfl) ⟨207546, by rfl⟩ : syracuseStep 553457 = 415093) B415093
theorem B618995 : Blo 366759 618995 := bstep (se 1 (by rfl) ⟨464246, by rfl⟩ : syracuseStep 618995 = 928493) B928493
theorem B553475 : Blo 366759 553475 := bstep (se 1 (by rfl) ⟨415106, by rfl⟩ : syracuseStep 553475 = 830213) B830213
theorem B553505 : Blo 366759 553505 := bstep (se 2 (by rfl) ⟨207564, by rfl⟩ : syracuseStep 553505 = 415129) B415129
theorem B553523 : Blo 366759 553523 := bstep (se 1 (by rfl) ⟨415142, by rfl⟩ : syracuseStep 553523 = 830285) B830285
theorem B881219 : Blo 366759 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B553553 : Blo 366759 553553 := bstep (se 2 (by rfl) ⟨207582, by rfl⟩ : syracuseStep 553553 = 415165) B415165
theorem B553571 : Blo 366759 553571 := bstep (se 1 (by rfl) ⟨415178, by rfl⟩ : syracuseStep 553571 = 830357) B830357
theorem B619123 : Blo 366759 619123 := bstep (se 1 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 619123 = 928685) B928685
theorem B553601 : Blo 366759 553601 := bstep (se 2 (by rfl) ⟨207600, by rfl⟩ : syracuseStep 553601 = 415201) B415201
theorem B553619 : Blo 366759 553619 := bstep (se 1 (by rfl) ⟨415214, by rfl⟩ : syracuseStep 553619 = 830429) B830429
theorem B553649 : Blo 366759 553649 := bstep (se 2 (by rfl) ⟨207618, by rfl⟩ : syracuseStep 553649 = 415237) B415237
theorem B553667 : Blo 366759 553667 := bstep (se 1 (by rfl) ⟨415250, by rfl⟩ : syracuseStep 553667 = 830501) B830501
theorem B553697 : Blo 366759 553697 := bstep (se 2 (by rfl) ⟨207636, by rfl⟩ : syracuseStep 553697 = 415273) B415273
theorem B1241837 : Blo 366759 1241837 := bstep (se 3 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 1241837 = 465689) B465689
theorem B553715 : Blo 366759 553715 := bstep (se 1 (by rfl) ⟨415286, by rfl⟩ : syracuseStep 553715 = 830573) B830573
theorem B619265 : Blo 366759 619265 := bstep (se 2 (by rfl) ⟨232224, by rfl⟩ : syracuseStep 619265 = 464449) B464449
theorem B553745 : Blo 366759 553745 := bstep (se 2 (by rfl) ⟨207654, by rfl⟩ : syracuseStep 553745 = 415309) B415309
theorem B1241891 : Blo 366759 1241891 := bstep (se 1 (by rfl) ⟨931418, by rfl⟩ : syracuseStep 1241891 = 1862837) B1862837
theorem B553763 : Blo 366759 553763 := bstep (se 1 (by rfl) ⟨415322, by rfl⟩ : syracuseStep 553763 = 830645) B830645
theorem B553793 : Blo 366759 553793 := bstep (se 2 (by rfl) ⟨207672, by rfl⟩ : syracuseStep 553793 = 415345) B415345
theorem B553811 : Blo 366759 553811 := bstep (se 1 (by rfl) ⟨415358, by rfl⟩ : syracuseStep 553811 = 830717) B830717
theorem B1176419 : Blo 366759 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B2356067 : Blo 366759 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B553841 : Blo 366759 553841 := bstep (se 2 (by rfl) ⟨207690, by rfl⟩ : syracuseStep 553841 = 415381) B415381
theorem B619393 : Blo 366759 619393 := bstep (se 2 (by rfl) ⟨232272, by rfl⟩ : syracuseStep 619393 = 464545) B464545
theorem B553859 : Blo 366759 553859 := bstep (se 1 (by rfl) ⟨415394, by rfl⟩ : syracuseStep 553859 = 830789) B830789
theorem B553889 : Blo 366759 553889 := bstep (se 2 (by rfl) ⟨207708, by rfl⟩ : syracuseStep 553889 = 415417) B415417
theorem B619427 : Blo 366759 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B553907 : Blo 366759 553907 := bstep (se 1 (by rfl) ⟨415430, by rfl⟩ : syracuseStep 553907 = 830861) B830861
theorem B553937 : Blo 366759 553937 := bstep (se 2 (by rfl) ⟨207726, by rfl⟩ : syracuseStep 553937 = 415453) B415453
theorem B553955 : Blo 366759 553955 := bstep (se 1 (by rfl) ⟨415466, by rfl⟩ : syracuseStep 553955 = 830933) B830933
theorem B1405937 : Blo 366759 1405937 := bstep (se 2 (by rfl) ⟨527226, by rfl⟩ : syracuseStep 1405937 = 1054453) B1054453
theorem B553985 : Blo 366759 553985 := bstep (se 2 (by rfl) ⟨207744, by rfl⟩ : syracuseStep 553985 = 415489) B415489
theorem B554003 : Blo 366759 554003 := bstep (se 1 (by rfl) ⟨415502, by rfl⟩ : syracuseStep 554003 = 831005) B831005
theorem B619555 : Blo 366759 619555 := bstep (se 1 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 619555 = 929333) B929333
theorem B1242161 : Blo 366759 1242161 := bstep (se 2 (by rfl) ⟨465810, by rfl⟩ : syracuseStep 1242161 = 931621) B931621
theorem B554033 : Blo 366759 554033 := bstep (se 2 (by rfl) ⟨207762, by rfl⟩ : syracuseStep 554033 = 415525) B415525
theorem B554051 : Blo 366759 554051 := bstep (se 1 (by rfl) ⟨415538, by rfl⟩ : syracuseStep 554051 = 831077) B831077
theorem B1864781 : Blo 366759 1864781 := bstep (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) B699293
theorem B554081 : Blo 366759 554081 := bstep (se 2 (by rfl) ⟨207780, by rfl⟩ : syracuseStep 554081 = 415561) B415561
theorem B554099 : Blo 366759 554099 := bstep (se 1 (by rfl) ⟨415574, by rfl⟩ : syracuseStep 554099 = 831149) B831149
theorem B1045649 : Blo 366759 1045649 := bstep (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) B784237
theorem B554129 : Blo 366759 554129 := bstep (se 2 (by rfl) ⟨207798, by rfl⟩ : syracuseStep 554129 = 415597) B415597
theorem B554147 : Blo 366759 554147 := bstep (se 1 (by rfl) ⟨415610, by rfl⟩ : syracuseStep 554147 = 831221) B831221
theorem B619697 : Blo 366759 619697 := bstep (se 2 (by rfl) ⟨232386, by rfl⟩ : syracuseStep 619697 = 464773) B464773
theorem B554177 : Blo 366759 554177 := bstep (se 2 (by rfl) ⟨207816, by rfl⟩ : syracuseStep 554177 = 415633) B415633
theorem B554195 : Blo 366759 554195 := bstep (se 1 (by rfl) ⟨415646, by rfl⟩ : syracuseStep 554195 = 831293) B831293
theorem B554225 : Blo 366759 554225 := bstep (se 2 (by rfl) ⟨207834, by rfl⟩ : syracuseStep 554225 = 415669) B415669
theorem B554243 : Blo 366759 554243 := bstep (se 1 (by rfl) ⟨415682, by rfl⟩ : syracuseStep 554243 = 831365) B831365
theorem B554273 : Blo 366759 554273 := bstep (se 2 (by rfl) ⟨207852, by rfl⟩ : syracuseStep 554273 = 415705) B415705
theorem B619825 : Blo 366759 619825 := bstep (se 2 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 619825 = 464869) B464869
theorem B554291 : Blo 366759 554291 := bstep (se 1 (by rfl) ⟨415718, by rfl⟩ : syracuseStep 554291 = 831437) B831437
theorem B554321 : Blo 366759 554321 := bstep (se 2 (by rfl) ⟨207870, by rfl⟩ : syracuseStep 554321 = 415741) B415741
theorem B619859 : Blo 366759 619859 := bstep (se 1 (by rfl) ⟨464894, by rfl⟩ : syracuseStep 619859 = 929789) B929789
theorem B554339 : Blo 366759 554339 := bstep (se 1 (by rfl) ⟨415754, by rfl⟩ : syracuseStep 554339 = 831509) B831509
theorem B554369 : Blo 366759 554369 := bstep (se 2 (by rfl) ⟨207888, by rfl⟩ : syracuseStep 554369 = 415777) B415777
theorem B554387 : Blo 366759 554387 := bstep (se 1 (by rfl) ⟨415790, by rfl⟩ : syracuseStep 554387 = 831581) B831581
theorem B554417 : Blo 366759 554417 := bstep (se 2 (by rfl) ⟨207906, by rfl⟩ : syracuseStep 554417 = 415813) B415813
theorem B554435 : Blo 366759 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B619987 : Blo 366759 619987 := bstep (se 1 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 619987 = 929981) B929981
theorem B554465 : Blo 366759 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B882161 : Blo 366759 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B554483 : Blo 366759 554483 := bstep (se 1 (by rfl) ⟨415862, by rfl⟩ : syracuseStep 554483 = 831725) B831725
theorem B554513 : Blo 366759 554513 := bstep (se 2 (by rfl) ⟨207942, by rfl⟩ : syracuseStep 554513 = 415885) B415885
theorem B554531 : Blo 366759 554531 := bstep (se 1 (by rfl) ⟨415898, by rfl⟩ : syracuseStep 554531 = 831797) B831797
theorem B554561 : Blo 366759 554561 := bstep (se 2 (by rfl) ⟨207960, by rfl⟩ : syracuseStep 554561 = 415921) B415921
theorem B1242701 : Blo 366759 1242701 := bstep (se 3 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 1242701 = 466013) B466013
theorem B554579 : Blo 366759 554579 := bstep (se 1 (by rfl) ⟨415934, by rfl⟩ : syracuseStep 554579 = 831869) B831869
theorem B620129 : Blo 366759 620129 := bstep (se 2 (by rfl) ⟨232548, by rfl⟩ : syracuseStep 620129 = 465097) B465097
theorem B1570403 : Blo 366759 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B554609 : Blo 366759 554609 := bstep (se 2 (by rfl) ⟨207978, by rfl⟩ : syracuseStep 554609 = 415957) B415957
theorem B1242755 : Blo 366759 1242755 := bstep (se 1 (by rfl) ⟨932066, by rfl⟩ : syracuseStep 1242755 = 1864133) B1864133
theorem B554627 : Blo 366759 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B1406605 : Blo 366759 1406605 := bstep (se 3 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 1406605 = 527477) B527477
theorem B554657 : Blo 366759 554657 := bstep (se 2 (by rfl) ⟨207996, by rfl⟩ : syracuseStep 554657 = 415993) B415993
theorem B1767089 : Blo 366759 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B554675 : Blo 366759 554675 := bstep (se 1 (by rfl) ⟨416006, by rfl⟩ : syracuseStep 554675 = 832013) B832013
theorem B554705 : Blo 366759 554705 := bstep (se 2 (by rfl) ⟨208014, by rfl⟩ : syracuseStep 554705 = 416029) B416029
theorem B620257 : Blo 366759 620257 := bstep (se 2 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 620257 = 465193) B465193
theorem B554723 : Blo 366759 554723 := bstep (se 1 (by rfl) ⟨416042, by rfl⟩ : syracuseStep 554723 = 832085) B832085
theorem B554753 : Blo 366759 554753 := bstep (se 2 (by rfl) ⟨208032, by rfl⟩ : syracuseStep 554753 = 416065) B416065
theorem B620291 : Blo 366759 620291 := bstep (se 1 (by rfl) ⟨465218, by rfl⟩ : syracuseStep 620291 = 930437) B930437
theorem B554771 : Blo 366759 554771 := bstep (se 1 (by rfl) ⟨416078, by rfl⟩ : syracuseStep 554771 = 832157) B832157
theorem B587569 : Blo 366759 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B1046321 : Blo 366759 1046321 := bstep (se 2 (by rfl) ⟨392370, by rfl⟩ : syracuseStep 1046321 = 784741) B784741
theorem B554801 : Blo 366759 554801 := bstep (se 2 (by rfl) ⟨208050, by rfl⟩ : syracuseStep 554801 = 416101) B416101
theorem B554819 : Blo 366759 554819 := bstep (se 1 (by rfl) ⟨416114, by rfl⟩ : syracuseStep 554819 = 832229) B832229
theorem B554849 : Blo 366759 554849 := bstep (se 2 (by rfl) ⟨208068, by rfl⟩ : syracuseStep 554849 = 416137) B416137
theorem B554867 : Blo 366759 554867 := bstep (se 1 (by rfl) ⟨416150, by rfl⟩ : syracuseStep 554867 = 832301) B832301
theorem B620419 : Blo 366759 620419 := bstep (se 1 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 620419 = 930629) B930629
theorem B587665 : Blo 366759 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B1243025 : Blo 366759 1243025 := bstep (se 2 (by rfl) ⟨466134, by rfl⟩ : syracuseStep 1243025 = 932269) B932269
theorem B554897 : Blo 366759 554897 := bstep (se 2 (by rfl) ⟨208086, by rfl⟩ : syracuseStep 554897 = 416173) B416173
theorem B554915 : Blo 366759 554915 := bstep (se 1 (by rfl) ⟨416186, by rfl⟩ : syracuseStep 554915 = 832373) B832373
theorem B1898417 : Blo 366759 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B554945 : Blo 366759 554945 := bstep (se 2 (by rfl) ⟨208104, by rfl⟩ : syracuseStep 554945 = 416209) B416209
theorem B554963 : Blo 366759 554963 := bstep (se 1 (by rfl) ⟨416222, by rfl⟩ : syracuseStep 554963 = 832445) B832445
theorem B554993 : Blo 366759 554993 := bstep (se 2 (by rfl) ⟨208122, by rfl⟩ : syracuseStep 554993 = 416245) B416245
theorem B555011 : Blo 366759 555011 := bstep (se 1 (by rfl) ⟨416258, by rfl⟩ : syracuseStep 555011 = 832517) B832517
theorem B620561 : Blo 366759 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B555041 : Blo 366759 555041 := bstep (se 2 (by rfl) ⟨208140, by rfl⟩ : syracuseStep 555041 = 416281) B416281
theorem B587825 : Blo 366759 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B1177649 : Blo 366759 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B1767473 : Blo 366759 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B555059 : Blo 366759 555059 := bstep (se 1 (by rfl) ⟨416294, by rfl⟩ : syracuseStep 555059 = 832589) B832589
theorem B555089 : Blo 366759 555089 := bstep (se 2 (by rfl) ⟨208158, by rfl⟩ : syracuseStep 555089 = 416317) B416317
theorem B555107 : Blo 366759 555107 := bstep (se 1 (by rfl) ⟨416330, by rfl⟩ : syracuseStep 555107 = 832661) B832661
theorem B555137 : Blo 366759 555137 := bstep (se 2 (by rfl) ⟨208176, by rfl⟩ : syracuseStep 555137 = 416353) B416353
theorem B620689 : Blo 366759 620689 := bstep (se 2 (by rfl) ⟨232758, by rfl⟩ : syracuseStep 620689 = 465517) B465517
theorem B555155 : Blo 366759 555155 := bstep (se 1 (by rfl) ⟨416366, by rfl⟩ : syracuseStep 555155 = 832733) B832733
theorem B555185 : Blo 366759 555185 := bstep (se 2 (by rfl) ⟨208194, by rfl⟩ : syracuseStep 555185 = 416389) B416389
theorem B620723 : Blo 366759 620723 := bstep (se 1 (by rfl) ⟨465542, by rfl⟩ : syracuseStep 620723 = 931085) B931085
theorem B784579 : Blo 366759 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B555203 : Blo 366759 555203 := bstep (se 1 (by rfl) ⟨416402, by rfl⟩ : syracuseStep 555203 = 832805) B832805
theorem B555233 : Blo 366759 555233 := bstep (se 2 (by rfl) ⟨208212, by rfl⟩ : syracuseStep 555233 = 416425) B416425
theorem B555251 : Blo 366759 555251 := bstep (se 1 (by rfl) ⟨416438, by rfl⟩ : syracuseStep 555251 = 832877) B832877
theorem B3373325 : Blo 366759 3373325 := bstep (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) B1264997
theorem B555281 : Blo 366759 555281 := bstep (se 2 (by rfl) ⟨208230, by rfl⟩ : syracuseStep 555281 = 416461) B416461
theorem B555299 : Blo 366759 555299 := bstep (se 1 (by rfl) ⟨416474, by rfl⟩ : syracuseStep 555299 = 832949) B832949
theorem B620851 : Blo 366759 620851 := bstep (se 1 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 620851 = 931277) B931277
theorem B555329 : Blo 366759 555329 := bstep (se 2 (by rfl) ⟨208248, by rfl⟩ : syracuseStep 555329 = 416497) B416497
theorem B555347 : Blo 366759 555347 := bstep (se 1 (by rfl) ⟨416510, by rfl⟩ : syracuseStep 555347 = 833021) B833021
theorem B555377 : Blo 366759 555377 := bstep (se 2 (by rfl) ⟨208266, by rfl⟩ : syracuseStep 555377 = 416533) B416533
theorem B522625 : Blo 366759 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B555395 : Blo 366759 555395 := bstep (se 1 (by rfl) ⟨416546, by rfl⟩ : syracuseStep 555395 = 833093) B833093
theorem B555425 : Blo 366759 555425 := bstep (se 2 (by rfl) ⟨208284, by rfl⟩ : syracuseStep 555425 = 416569) B416569
theorem B522659 : Blo 366759 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B1407395 : Blo 366759 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1243565 : Blo 366759 1243565 := bstep (se 3 (by rfl) ⟨233168, by rfl⟩ : syracuseStep 1243565 = 466337) B466337
theorem B883121 : Blo 366759 883121 := bstep (se 2 (by rfl) ⟨331170, by rfl⟩ : syracuseStep 883121 = 662341) B662341
theorem B555443 : Blo 366759 555443 := bstep (se 1 (by rfl) ⟨416582, by rfl⟩ : syracuseStep 555443 = 833165) B833165
theorem B620993 : Blo 366759 620993 := bstep (se 2 (by rfl) ⟨232872, by rfl⟩ : syracuseStep 620993 = 465745) B465745
theorem B555473 : Blo 366759 555473 := bstep (se 2 (by rfl) ⟨208302, by rfl⟩ : syracuseStep 555473 = 416605) B416605
theorem B1243619 : Blo 366759 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B2128355 : Blo 366759 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B555491 : Blo 366759 555491 := bstep (se 1 (by rfl) ⟨416618, by rfl⟩ : syracuseStep 555491 = 833237) B833237
theorem B555521 : Blo 366759 555521 := bstep (se 2 (by rfl) ⟨208320, by rfl⟩ : syracuseStep 555521 = 416641) B416641
theorem B555539 : Blo 366759 555539 := bstep (se 1 (by rfl) ⟨416654, by rfl⟩ : syracuseStep 555539 = 833309) B833309
theorem B555569 : Blo 366759 555569 := bstep (se 2 (by rfl) ⟨208338, by rfl⟩ : syracuseStep 555569 = 416677) B416677
theorem B621121 : Blo 366759 621121 := bstep (se 2 (by rfl) ⟨232920, by rfl⟩ : syracuseStep 621121 = 465841) B465841
theorem B1047107 : Blo 366759 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B555587 : Blo 366759 555587 := bstep (se 1 (by rfl) ⟨416690, by rfl⟩ : syracuseStep 555587 = 833381) B833381
theorem B1768013 : Blo 366759 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B555617 : Blo 366759 555617 := bstep (se 2 (by rfl) ⟨208356, by rfl⟩ : syracuseStep 555617 = 416713) B416713
theorem B621155 : Blo 366759 621155 := bstep (se 1 (by rfl) ⟨465866, by rfl⟩ : syracuseStep 621155 = 931733) B931733
theorem B555635 : Blo 366759 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B555665 : Blo 366759 555665 := bstep (se 2 (by rfl) ⟨208374, by rfl⟩ : syracuseStep 555665 = 416749) B416749
theorem B555683 : Blo 366759 555683 := bstep (se 1 (by rfl) ⟨416762, by rfl⟩ : syracuseStep 555683 = 833525) B833525
theorem B555713 : Blo 366759 555713 := bstep (se 2 (by rfl) ⟨208392, by rfl⟩ : syracuseStep 555713 = 416785) B416785
theorem B555731 : Blo 366759 555731 := bstep (se 1 (by rfl) ⟨416798, by rfl⟩ : syracuseStep 555731 = 833597) B833597
theorem B621283 : Blo 366759 621283 := bstep (se 1 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 621283 = 931925) B931925
theorem B1243889 : Blo 366759 1243889 := bstep (se 2 (by rfl) ⟨466458, by rfl⟩ : syracuseStep 1243889 = 932917) B932917
theorem B555761 : Blo 366759 555761 := bstep (se 2 (by rfl) ⟨208410, by rfl⟩ : syracuseStep 555761 = 416821) B416821
theorem B555779 : Blo 366759 555779 := bstep (se 1 (by rfl) ⟨416834, by rfl⟩ : syracuseStep 555779 = 833669) B833669
theorem B555809 : Blo 366759 555809 := bstep (se 2 (by rfl) ⟨208428, by rfl⟩ : syracuseStep 555809 = 416857) B416857
theorem B1571633 : Blo 366759 1571633 := bstep (se 2 (by rfl) ⟨589362, by rfl⟩ : syracuseStep 1571633 = 1178725) B1178725
theorem B2358065 : Blo 366759 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B555827 : Blo 366759 555827 := bstep (se 1 (by rfl) ⟨416870, by rfl⟩ : syracuseStep 555827 = 833741) B833741
theorem B555857 : Blo 366759 555857 := bstep (se 2 (by rfl) ⟨208446, by rfl⟩ : syracuseStep 555857 = 416893) B416893
theorem B555875 : Blo 366759 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B621425 : Blo 366759 621425 := bstep (se 2 (by rfl) ⟨233034, by rfl⟩ : syracuseStep 621425 = 466069) B466069
theorem B555905 : Blo 366759 555905 := bstep (se 2 (by rfl) ⟨208464, by rfl⟩ : syracuseStep 555905 = 416929) B416929
theorem B1047437 : Blo 366759 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B1178509 : Blo 366759 1178509 := bstep (se 3 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 1178509 = 441941) B441941
theorem B555923 : Blo 366759 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B555953 : Blo 366759 555953 := bstep (se 2 (by rfl) ⟨208482, by rfl⟩ : syracuseStep 555953 = 416965) B416965
theorem B392131 : Blo 366759 392131 := bstep (se 1 (by rfl) ⟨294098, by rfl⟩ : syracuseStep 392131 = 588197) B588197
theorem B883651 : Blo 366759 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B555971 : Blo 366759 555971 := bstep (se 1 (by rfl) ⟨416978, by rfl⟩ : syracuseStep 555971 = 833957) B833957
theorem B523217 : Blo 366759 523217 := bstep (se 2 (by rfl) ⟨196206, by rfl⟩ : syracuseStep 523217 = 392413) B392413
theorem B1047505 : Blo 366759 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B556001 : Blo 366759 556001 := bstep (se 2 (by rfl) ⟨208500, by rfl⟩ : syracuseStep 556001 = 417001) B417001
theorem B621553 : Blo 366759 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B556019 : Blo 366759 556019 := bstep (se 1 (by rfl) ⟨417014, by rfl⟩ : syracuseStep 556019 = 834029) B834029
theorem B556049 : Blo 366759 556049 := bstep (se 2 (by rfl) ⟨208518, by rfl⟩ : syracuseStep 556049 = 417037) B417037
theorem B621587 : Blo 366759 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B523297 : Blo 366759 523297 := bstep (se 2 (by rfl) ⟨196236, by rfl⟩ : syracuseStep 523297 = 392473) B392473
theorem B556067 : Blo 366759 556067 := bstep (se 1 (by rfl) ⟨417050, by rfl⟩ : syracuseStep 556067 = 834101) B834101
theorem B556097 : Blo 366759 556097 := bstep (se 2 (by rfl) ⟨208536, by rfl⟩ : syracuseStep 556097 = 417073) B417073
theorem B556115 : Blo 366759 556115 := bstep (se 1 (by rfl) ⟨417086, by rfl⟩ : syracuseStep 556115 = 834173) B834173
theorem B3538019 : Blo 366759 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B621715 : Blo 366759 621715 := bstep (se 1 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 621715 = 932573) B932573
theorem B1047779 : Blo 366759 1047779 := bstep (se 1 (by rfl) ⟨785834, by rfl⟩ : syracuseStep 1047779 = 1571669) B1571669
theorem B1244429 : Blo 366759 1244429 := bstep (se 3 (by rfl) ⟨233330, by rfl⟩ : syracuseStep 1244429 = 466661) B466661
theorem B621857 : Blo 366759 621857 := bstep (se 2 (by rfl) ⟨233196, by rfl⟩ : syracuseStep 621857 = 466393) B466393
theorem B1244483 : Blo 366759 1244483 := bstep (se 1 (by rfl) ⟨933362, by rfl⟩ : syracuseStep 1244483 = 1866725) B1866725
theorem B392563 : Blo 366759 392563 := bstep (se 1 (by rfl) ⟨294422, by rfl⟩ : syracuseStep 392563 = 588845) B588845
theorem B621985 : Blo 366759 621985 := bstep (se 2 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 621985 = 466489) B466489
theorem B622019 : Blo 366759 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B622147 : Blo 366759 622147 := bstep (se 1 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 622147 = 933221) B933221
theorem B1244753 : Blo 366759 1244753 := bstep (se 2 (by rfl) ⟨466782, by rfl⟩ : syracuseStep 1244753 = 933565) B933565
theorem B1769165 : Blo 366759 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B2358989 : Blo 366759 2358989 := bstep (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) B884621
theorem B622289 : Blo 366759 622289 := bstep (se 2 (by rfl) ⟨233358, by rfl⟩ : syracuseStep 622289 = 466717) B466717
theorem B524083 : Blo 366759 524083 := bstep (se 1 (by rfl) ⟨393062, by rfl⟩ : syracuseStep 524083 = 786125) B786125
theorem B589619 : Blo 366759 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B6356789 : Blo 366759 6356789 := bstep (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) B595949
theorem B622417 : Blo 366759 622417 := bstep (se 2 (by rfl) ⟨233406, by rfl⟩ : syracuseStep 622417 = 466813) B466813
theorem B622451 : Blo 366759 622451 := bstep (se 1 (by rfl) ⟨466838, by rfl⟩ : syracuseStep 622451 = 933677) B933677
theorem B1867697 : Blo 366759 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B2785265 : Blo 366759 2785265 := bstep (se 2 (by rfl) ⟨1044474, by rfl⟩ : syracuseStep 2785265 = 2088949) B2088949
theorem B622579 : Blo 366759 622579 := bstep (se 1 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 622579 = 933869) B933869
theorem B2097197 : Blo 366759 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B622667 : Blo 366759 622667 := bstep (se 1 (by rfl) ⟨467000, by rfl⟩ : syracuseStep 622667 = 934001) B934001
theorem B1179841 : Blo 366759 1179841 := bstep (se 2 (by rfl) ⟨442440, by rfl⟩ : syracuseStep 1179841 = 884881) B884881
theorem B622795 : Blo 366759 622795 := bstep (se 1 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 622795 = 934193) B934193
theorem B1245401 : Blo 366759 1245401 := bstep (se 2 (by rfl) ⟨467025, by rfl⟩ : syracuseStep 1245401 = 934051) B934051
theorem B1179955 : Blo 366759 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B622937 : Blo 366759 622937 := bstep (se 2 (by rfl) ⟨233601, by rfl⟩ : syracuseStep 622937 = 467203) B467203
theorem B1868183 : Blo 366759 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B393643 : Blo 366759 393643 := bstep (se 1 (by rfl) ⟨295232, by rfl⟩ : syracuseStep 393643 = 590465) B590465
theorem B2654669 : Blo 366759 2654669 := bstep (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) B995501
theorem B2261465 : Blo 366759 2261465 := bstep (se 2 (by rfl) ⟨848049, by rfl⟩ : syracuseStep 2261465 = 1696099) B1696099
theorem B623065 : Blo 366759 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B524875 : Blo 366759 524875 := bstep (se 1 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 524875 = 787313) B787313
theorem B852619 : Blo 366759 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B1246103 : Blo 366759 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B787457 : Blo 366759 787457 := bstep (se 2 (by rfl) ⟨295296, by rfl⟩ : syracuseStep 787457 = 590593) B590593
theorem B623639 : Blo 366759 623639 := bstep (se 1 (by rfl) ⟨467729, by rfl⟩ : syracuseStep 623639 = 935459) B935459
theorem B623767 : Blo 366759 623767 := bstep (se 1 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 623767 = 935651) B935651
theorem B3146957 : Blo 366759 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B787799 : Blo 366759 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B1246643 : Blo 366759 1246643 := bstep (se 1 (by rfl) ⟨934982, by rfl⟩ : syracuseStep 1246643 = 1869965) B1869965
theorem B1050205 : Blo 366759 1050205 := bstep (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) B393827
theorem B1246913 : Blo 366759 1246913 := bstep (se 2 (by rfl) ⟨467592, by rfl⟩ : syracuseStep 1246913 = 935185) B935185
theorem B624395 : Blo 366759 624395 := bstep (se 1 (by rfl) ⟨468296, by rfl⟩ : syracuseStep 624395 = 936593) B936593
theorem B3180305 : Blo 366759 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B526105 : Blo 366759 526105 := bstep (se 2 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 526105 = 394579) B394579
theorem B788363 : Blo 366759 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B624523 : Blo 366759 624523 := bstep (se 1 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 624523 = 936785) B936785
theorem B395275 : Blo 366759 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B624665 : Blo 366759 624665 := bstep (se 2 (by rfl) ⟨234249, by rfl⟩ : syracuseStep 624665 = 468499) B468499
theorem B3967127 : Blo 366759 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B624793 : Blo 366759 624793 := bstep (se 2 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 624793 = 468595) B468595
theorem B1575085 : Blo 366759 1575085 := bstep (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) B590657
theorem B1247453 : Blo 366759 1247453 := bstep (se 3 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 1247453 = 467795) B467795
theorem B5966257 : Blo 366759 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B788953 : Blo 366759 788953 := bstep (se 2 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 788953 = 591715) B591715
theorem B559703 : Blo 366759 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B592535 : Blo 366759 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B526999 : Blo 366759 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B625367 : Blo 366759 625367 := bstep (se 1 (by rfl) ⟨469025, by rfl⟩ : syracuseStep 625367 = 938051) B938051
theorem B625495 : Blo 366759 625495 := bstep (se 1 (by rfl) ⟨469121, by rfl⟩ : syracuseStep 625495 = 938243) B938243
theorem B1051481 : Blo 366759 1051481 := bstep (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) B788611
theorem B887755 : Blo 366759 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B2657411 : Blo 366759 2657411 := bstep (se 1 (by rfl) ⟨1993058, by rfl⟩ : syracuseStep 2657411 = 3986117) B3986117
theorem B593099 : Blo 366759 593099 := bstep (se 1 (by rfl) ⟨444824, by rfl⟩ : syracuseStep 593099 = 889649) B889649
theorem B527563 : Blo 366759 527563 := bstep (se 1 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 527563 = 791345) B791345
theorem B4197581 : Blo 366759 4197581 := bstep (se 3 (by rfl) ⟨787046, by rfl⟩ : syracuseStep 4197581 = 1574093) B1574093
theorem B1248587 : Blo 366759 1248587 := bstep (se 1 (by rfl) ⟨936440, by rfl⟩ : syracuseStep 1248587 = 1872881) B1872881
theorem B790003 : Blo 366759 790003 := bstep (se 1 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 790003 = 1185005) B1185005
theorem B1379885 : Blo 366759 1379885 := bstep (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) B517457
theorem B888371 : Blo 366759 888371 := bstep (se 1 (by rfl) ⟨666278, by rfl⟩ : syracuseStep 888371 = 1332557) B1332557
theorem B1248857 : Blo 366759 1248857 := bstep (se 2 (by rfl) ⟨468321, by rfl⟩ : syracuseStep 1248857 = 936643) B936643
theorem B2100887 : Blo 366759 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B1871747 : Blo 366759 1871747 := bstep (se 1 (by rfl) ⟨1403810, by rfl⟩ : syracuseStep 1871747 = 2807621) B2807621
theorem B9408473 : Blo 366759 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B9474083 : Blo 366759 9474083 := bstep (se 1 (by rfl) ⟨7105562, by rfl⟩ : syracuseStep 9474083 = 14211125) B14211125
theorem B1249559 : Blo 366759 1249559 := bstep (se 1 (by rfl) ⟨937169, by rfl⟩ : syracuseStep 1249559 = 1874339) B1874339
theorem B2920835 : Blo 366759 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1053121 : Blo 366759 1053121 := bstep (se 2 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 1053121 = 789841) B789841
theorem B1577495 : Blo 366759 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1250099 : Blo 366759 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B791489 : Blo 366759 791489 := bstep (se 2 (by rfl) ⟨296808, by rfl⟩ : syracuseStep 791489 = 593617) B593617
theorem B1250369 : Blo 366759 1250369 := bstep (se 2 (by rfl) ⟨468888, by rfl⟩ : syracuseStep 1250369 = 937777) B937777
theorem B791831 : Blo 366759 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B1119539 : Blo 366759 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B497227 : Blo 366759 497227 := bstep (se 1 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 497227 = 745841) B745841
theorem B1250909 : Blo 366759 1250909 := bstep (se 3 (by rfl) ⟨234545, by rfl⟩ : syracuseStep 1250909 = 469091) B469091
theorem B3151709 : Blo 366759 3151709 := bstep (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) B1181891
theorem B825227 : Blo 366759 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B825281 : Blo 366759 825281 := bstep (se 2 (by rfl) ⟨309480, by rfl⟩ : syracuseStep 825281 = 618961) B618961
theorem B661505 : Blo 366759 661505 := bstep (se 2 (by rfl) ⟨248064, by rfl⟩ : syracuseStep 661505 = 496129) B496129
theorem B1054795 : Blo 366759 1054795 := bstep (se 1 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 1054795 = 1582193) B1582193
theorem B825497 : Blo 366759 825497 := bstep (se 2 (by rfl) ⟨309561, by rfl⟩ : syracuseStep 825497 = 619123) B619123
theorem B366763 : Blo 366759 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B366775 : Blo 366759 366775 := bstep (se 1 (by rfl) ⟨275081, by rfl⟩ : syracuseStep 366775 = 550163) B550163
theorem B1153217 : Blo 366759 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B366795 : Blo 366759 366795 := bstep (se 1 (by rfl) ⟨275096, by rfl⟩ : syracuseStep 366795 = 550193) B550193
theorem B366807 : Blo 366759 366807 := bstep (se 1 (by rfl) ⟨275105, by rfl⟩ : syracuseStep 366807 = 550211) B550211
theorem B366827 : Blo 366759 366827 := bstep (se 1 (by rfl) ⟨275120, by rfl⟩ : syracuseStep 366827 = 550241) B550241
theorem B825587 : Blo 366759 825587 := bstep (se 1 (by rfl) ⟨619190, by rfl⟩ : syracuseStep 825587 = 1238381) B1238381
theorem B366839 : Blo 366759 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B366859 : Blo 366759 366859 := bstep (se 1 (by rfl) ⟨275144, by rfl⟩ : syracuseStep 366859 = 550289) B550289
theorem B366871 : Blo 366759 366871 := bstep (se 1 (by rfl) ⟨275153, by rfl⟩ : syracuseStep 366871 = 550307) B550307
theorem B825623 : Blo 366759 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B366891 : Blo 366759 366891 := bstep (se 1 (by rfl) ⟨275168, by rfl⟩ : syracuseStep 366891 = 550337) B550337
theorem B366903 : Blo 366759 366903 := bstep (se 1 (by rfl) ⟨275177, by rfl⟩ : syracuseStep 366903 = 550355) B550355
theorem B366923 : Blo 366759 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B366935 : Blo 366759 366935 := bstep (se 1 (by rfl) ⟨275201, by rfl⟩ : syracuseStep 366935 = 550403) B550403
theorem B1055069 : Blo 366759 1055069 := bstep (se 3 (by rfl) ⟨197825, by rfl⟩ : syracuseStep 1055069 = 395651) B395651
theorem B366955 : Blo 366759 366955 := bstep (se 1 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 366955 = 550433) B550433
theorem B366967 : Blo 366759 366967 := bstep (se 1 (by rfl) ⟨275225, by rfl⟩ : syracuseStep 366967 = 550451) B550451
theorem B366987 : Blo 366759 366987 := bstep (se 1 (by rfl) ⟨275240, by rfl⟩ : syracuseStep 366987 = 550481) B550481
theorem B1579409 : Blo 366759 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B366999 : Blo 366759 366999 := bstep (se 1 (by rfl) ⟨275249, by rfl⟩ : syracuseStep 366999 = 550499) B550499
theorem B367019 : Blo 366759 367019 := bstep (se 1 (by rfl) ⟨275264, by rfl⟩ : syracuseStep 367019 = 550529) B550529
theorem B367031 : Blo 366759 367031 := bstep (se 1 (by rfl) ⟨275273, by rfl⟩ : syracuseStep 367031 = 550547) B550547
theorem B825803 : Blo 366759 825803 := bstep (se 1 (by rfl) ⟨619352, by rfl⟩ : syracuseStep 825803 = 1238705) B1238705
theorem B367051 : Blo 366759 367051 := bstep (se 1 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 367051 = 550577) B550577
theorem B465355 : Blo 366759 465355 := bstep (se 1 (by rfl) ⟨349016, by rfl⟩ : syracuseStep 465355 = 698033) B698033
theorem B367063 : Blo 366759 367063 := bstep (se 1 (by rfl) ⟨275297, by rfl⟩ : syracuseStep 367063 = 550595) B550595
theorem B367083 : Blo 366759 367083 := bstep (se 1 (by rfl) ⟨275312, by rfl⟩ : syracuseStep 367083 = 550625) B550625
theorem B367095 : Blo 366759 367095 := bstep (se 1 (by rfl) ⟨275321, by rfl⟩ : syracuseStep 367095 = 550643) B550643
theorem B825857 : Blo 366759 825857 := bstep (se 2 (by rfl) ⟨309696, by rfl⟩ : syracuseStep 825857 = 619393) B619393
theorem B367115 : Blo 366759 367115 := bstep (se 1 (by rfl) ⟨275336, by rfl⟩ : syracuseStep 367115 = 550673) B550673
theorem B7608845 : Blo 366759 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B367127 : Blo 366759 367127 := bstep (se 1 (by rfl) ⟨275345, by rfl⟩ : syracuseStep 367127 = 550691) B550691
theorem B367147 : Blo 366759 367147 := bstep (se 1 (by rfl) ⟨275360, by rfl⟩ : syracuseStep 367147 = 550721) B550721
theorem B367159 : Blo 366759 367159 := bstep (se 1 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 367159 = 550739) B550739
theorem B367179 : Blo 366759 367179 := bstep (se 1 (by rfl) ⟨275384, by rfl⟩ : syracuseStep 367179 = 550769) B550769
theorem B367191 : Blo 366759 367191 := bstep (se 1 (by rfl) ⟨275393, by rfl⟩ : syracuseStep 367191 = 550787) B550787
theorem B367211 : Blo 366759 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B367223 : Blo 366759 367223 := bstep (se 1 (by rfl) ⟨275417, by rfl⟩ : syracuseStep 367223 = 550835) B550835
theorem B367243 : Blo 366759 367243 := bstep (se 1 (by rfl) ⟨275432, by rfl⟩ : syracuseStep 367243 = 550865) B550865
theorem B367255 : Blo 366759 367255 := bstep (se 1 (by rfl) ⟨275441, by rfl⟩ : syracuseStep 367255 = 550883) B550883
theorem B367275 : Blo 366759 367275 := bstep (se 1 (by rfl) ⟨275456, by rfl⟩ : syracuseStep 367275 = 550913) B550913
theorem B367287 : Blo 366759 367287 := bstep (se 1 (by rfl) ⟨275465, by rfl⟩ : syracuseStep 367287 = 550931) B550931
theorem B367307 : Blo 366759 367307 := bstep (se 1 (by rfl) ⟨275480, by rfl⟩ : syracuseStep 367307 = 550961) B550961
theorem B367319 : Blo 366759 367319 := bstep (se 1 (by rfl) ⟨275489, by rfl⟩ : syracuseStep 367319 = 550979) B550979
theorem B826073 : Blo 366759 826073 := bstep (se 2 (by rfl) ⟨309777, by rfl⟩ : syracuseStep 826073 = 619555) B619555
theorem B367339 : Blo 366759 367339 := bstep (se 1 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 367339 = 551009) B551009
theorem B367351 : Blo 366759 367351 := bstep (se 1 (by rfl) ⟨275513, by rfl⟩ : syracuseStep 367351 = 551027) B551027
theorem B367371 : Blo 366759 367371 := bstep (se 1 (by rfl) ⟨275528, by rfl⟩ : syracuseStep 367371 = 551057) B551057
theorem B367383 : Blo 366759 367383 := bstep (se 1 (by rfl) ⟨275537, by rfl⟩ : syracuseStep 367383 = 551075) B551075
theorem B367403 : Blo 366759 367403 := bstep (se 1 (by rfl) ⟨275552, by rfl⟩ : syracuseStep 367403 = 551105) B551105
theorem B826163 : Blo 366759 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B367415 : Blo 366759 367415 := bstep (se 1 (by rfl) ⟨275561, by rfl⟩ : syracuseStep 367415 = 551123) B551123
theorem B367435 : Blo 366759 367435 := bstep (se 1 (by rfl) ⟨275576, by rfl⟩ : syracuseStep 367435 = 551153) B551153
theorem B826199 : Blo 366759 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B367447 : Blo 366759 367447 := bstep (se 1 (by rfl) ⟨275585, by rfl⟩ : syracuseStep 367447 = 551171) B551171
theorem B367467 : Blo 366759 367467 := bstep (se 1 (by rfl) ⟨275600, by rfl⟩ : syracuseStep 367467 = 551201) B551201
theorem B367479 : Blo 366759 367479 := bstep (se 1 (by rfl) ⟨275609, by rfl⟩ : syracuseStep 367479 = 551219) B551219
theorem B367499 : Blo 366759 367499 := bstep (se 1 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 367499 = 551249) B551249
theorem B367511 : Blo 366759 367511 := bstep (se 1 (by rfl) ⟨275633, by rfl⟩ : syracuseStep 367511 = 551267) B551267
theorem B367531 : Blo 366759 367531 := bstep (se 1 (by rfl) ⟨275648, by rfl⟩ : syracuseStep 367531 = 551297) B551297
theorem B367543 : Blo 366759 367543 := bstep (se 1 (by rfl) ⟨275657, by rfl⟩ : syracuseStep 367543 = 551315) B551315
theorem B367563 : Blo 366759 367563 := bstep (se 1 (by rfl) ⟨275672, by rfl⟩ : syracuseStep 367563 = 551345) B551345
theorem B367575 : Blo 366759 367575 := bstep (se 1 (by rfl) ⟨275681, by rfl⟩ : syracuseStep 367575 = 551363) B551363
theorem B367595 : Blo 366759 367595 := bstep (se 1 (by rfl) ⟨275696, by rfl⟩ : syracuseStep 367595 = 551393) B551393
theorem B367607 : Blo 366759 367607 := bstep (se 1 (by rfl) ⟨275705, by rfl⟩ : syracuseStep 367607 = 551411) B551411
theorem B826379 : Blo 366759 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B367627 : Blo 366759 367627 := bstep (se 1 (by rfl) ⟨275720, by rfl⟩ : syracuseStep 367627 = 551441) B551441
theorem B367639 : Blo 366759 367639 := bstep (se 1 (by rfl) ⟨275729, by rfl⟩ : syracuseStep 367639 = 551459) B551459
theorem B367659 : Blo 366759 367659 := bstep (se 1 (by rfl) ⟨275744, by rfl⟩ : syracuseStep 367659 = 551489) B551489
theorem B367671 : Blo 366759 367671 := bstep (se 1 (by rfl) ⟨275753, by rfl⟩ : syracuseStep 367671 = 551507) B551507
theorem B826433 : Blo 366759 826433 := bstep (se 2 (by rfl) ⟨309912, by rfl⟩ : syracuseStep 826433 = 619825) B619825
theorem B367691 : Blo 366759 367691 := bstep (se 1 (by rfl) ⟨275768, by rfl⟩ : syracuseStep 367691 = 551537) B551537
theorem B367703 : Blo 366759 367703 := bstep (se 1 (by rfl) ⟨275777, by rfl⟩ : syracuseStep 367703 = 551555) B551555
theorem B367723 : Blo 366759 367723 := bstep (se 1 (by rfl) ⟨275792, by rfl⟩ : syracuseStep 367723 = 551585) B551585
theorem B367735 : Blo 366759 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B367755 : Blo 366759 367755 := bstep (se 1 (by rfl) ⟨275816, by rfl⟩ : syracuseStep 367755 = 551633) B551633
theorem B367767 : Blo 366759 367767 := bstep (se 1 (by rfl) ⟨275825, by rfl⟩ : syracuseStep 367767 = 551651) B551651
theorem B7183511 : Blo 366759 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B367787 : Blo 366759 367787 := bstep (se 1 (by rfl) ⟨275840, by rfl⟩ : syracuseStep 367787 = 551681) B551681
theorem B367799 : Blo 366759 367799 := bstep (se 1 (by rfl) ⟨275849, by rfl⟩ : syracuseStep 367799 = 551699) B551699
theorem B367819 : Blo 366759 367819 := bstep (se 1 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 367819 = 551729) B551729
theorem B367831 : Blo 366759 367831 := bstep (se 1 (by rfl) ⟨275873, by rfl⟩ : syracuseStep 367831 = 551747) B551747
theorem B367851 : Blo 366759 367851 := bstep (se 1 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 367851 = 551777) B551777
theorem B367863 : Blo 366759 367863 := bstep (se 1 (by rfl) ⟨275897, by rfl⟩ : syracuseStep 367863 = 551795) B551795
theorem B367883 : Blo 366759 367883 := bstep (se 1 (by rfl) ⟨275912, by rfl⟩ : syracuseStep 367883 = 551825) B551825
theorem B367895 : Blo 366759 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B826649 : Blo 366759 826649 := bstep (se 2 (by rfl) ⟨309993, by rfl⟩ : syracuseStep 826649 = 619987) B619987
theorem B367915 : Blo 366759 367915 := bstep (se 1 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 367915 = 551873) B551873
theorem B728371 : Blo 366759 728371 := bstep (se 1 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 728371 = 1092557) B1092557
theorem B367927 : Blo 366759 367927 := bstep (se 1 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 367927 = 551891) B551891
theorem B367947 : Blo 366759 367947 := bstep (se 1 (by rfl) ⟨275960, by rfl⟩ : syracuseStep 367947 = 551921) B551921
theorem B367959 : Blo 366759 367959 := bstep (se 1 (by rfl) ⟨275969, by rfl⟩ : syracuseStep 367959 = 551939) B551939
theorem B1580381 : Blo 366759 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B367979 : Blo 366759 367979 := bstep (se 1 (by rfl) ⟨275984, by rfl⟩ : syracuseStep 367979 = 551969) B551969
theorem B826739 : Blo 366759 826739 := bstep (se 1 (by rfl) ⟨620054, by rfl⟩ : syracuseStep 826739 = 1240109) B1240109
theorem B367991 : Blo 366759 367991 := bstep (se 1 (by rfl) ⟨275993, by rfl⟩ : syracuseStep 367991 = 551987) B551987
theorem B368011 : Blo 366759 368011 := bstep (se 1 (by rfl) ⟨276008, by rfl⟩ : syracuseStep 368011 = 552017) B552017
theorem B826775 : Blo 366759 826775 := bstep (se 1 (by rfl) ⟨620081, by rfl⟩ : syracuseStep 826775 = 1240163) B1240163
theorem B368023 : Blo 366759 368023 := bstep (se 1 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 368023 = 552035) B552035
theorem B466327 : Blo 366759 466327 := bstep (se 1 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 466327 = 699491) B699491
theorem B368043 : Blo 366759 368043 := bstep (se 1 (by rfl) ⟨276032, by rfl⟩ : syracuseStep 368043 = 552065) B552065
theorem B368055 : Blo 366759 368055 := bstep (se 1 (by rfl) ⟨276041, by rfl⟩ : syracuseStep 368055 = 552083) B552083
theorem B368075 : Blo 366759 368075 := bstep (se 1 (by rfl) ⟨276056, by rfl⟩ : syracuseStep 368075 = 552113) B552113
theorem B368087 : Blo 366759 368087 := bstep (se 1 (by rfl) ⟨276065, by rfl⟩ : syracuseStep 368087 = 552131) B552131
theorem B368107 : Blo 366759 368107 := bstep (se 1 (by rfl) ⟨276080, by rfl⟩ : syracuseStep 368107 = 552161) B552161
theorem B368119 : Blo 366759 368119 := bstep (se 1 (by rfl) ⟨276089, by rfl⟩ : syracuseStep 368119 = 552179) B552179
theorem B368139 : Blo 366759 368139 := bstep (se 1 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 368139 = 552209) B552209
theorem B1875473 : Blo 366759 1875473 := bstep (se 2 (by rfl) ⟨703302, by rfl⟩ : syracuseStep 1875473 = 1406605) B1406605
theorem B368151 : Blo 366759 368151 := bstep (se 1 (by rfl) ⟨276113, by rfl⟩ : syracuseStep 368151 = 552227) B552227
theorem B368171 : Blo 366759 368171 := bstep (se 1 (by rfl) ⟨276128, by rfl⟩ : syracuseStep 368171 = 552257) B552257
theorem B368183 : Blo 366759 368183 := bstep (se 1 (by rfl) ⟨276137, by rfl⟩ : syracuseStep 368183 = 552275) B552275
theorem B826955 : Blo 366759 826955 := bstep (se 1 (by rfl) ⟨620216, by rfl⟩ : syracuseStep 826955 = 1240433) B1240433
theorem B368203 : Blo 366759 368203 := bstep (se 1 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 368203 = 552305) B552305
theorem B368215 : Blo 366759 368215 := bstep (se 1 (by rfl) ⟨276161, by rfl⟩ : syracuseStep 368215 = 552323) B552323
theorem B368235 : Blo 366759 368235 := bstep (se 1 (by rfl) ⟨276176, by rfl⟩ : syracuseStep 368235 = 552353) B552353
theorem B368247 : Blo 366759 368247 := bstep (se 1 (by rfl) ⟨276185, by rfl⟩ : syracuseStep 368247 = 552371) B552371
theorem B827009 : Blo 366759 827009 := bstep (se 2 (by rfl) ⟨310128, by rfl⟩ : syracuseStep 827009 = 620257) B620257
theorem B368267 : Blo 366759 368267 := bstep (se 1 (by rfl) ⟨276200, by rfl⟩ : syracuseStep 368267 = 552401) B552401
theorem B368279 : Blo 366759 368279 := bstep (se 1 (by rfl) ⟨276209, by rfl⟩ : syracuseStep 368279 = 552419) B552419
theorem B368299 : Blo 366759 368299 := bstep (se 1 (by rfl) ⟨276224, by rfl⟩ : syracuseStep 368299 = 552449) B552449
theorem B1875635 : Blo 366759 1875635 := bstep (se 1 (by rfl) ⟨1406726, by rfl⟩ : syracuseStep 1875635 = 2813453) B2813453
theorem B368311 : Blo 366759 368311 := bstep (se 1 (by rfl) ⟨276233, by rfl⟩ : syracuseStep 368311 = 552467) B552467
theorem B368331 : Blo 366759 368331 := bstep (se 1 (by rfl) ⟨276248, by rfl⟩ : syracuseStep 368331 = 552497) B552497
theorem B1187531 : Blo 366759 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B368343 : Blo 366759 368343 := bstep (se 1 (by rfl) ⟨276257, by rfl⟩ : syracuseStep 368343 = 552515) B552515
theorem B368363 : Blo 366759 368363 := bstep (se 1 (by rfl) ⟨276272, by rfl⟩ : syracuseStep 368363 = 552545) B552545
theorem B368375 : Blo 366759 368375 := bstep (se 1 (by rfl) ⟨276281, by rfl⟩ : syracuseStep 368375 = 552563) B552563
theorem B368395 : Blo 366759 368395 := bstep (se 1 (by rfl) ⟨276296, by rfl⟩ : syracuseStep 368395 = 552593) B552593
theorem B368407 : Blo 366759 368407 := bstep (se 1 (by rfl) ⟨276305, by rfl⟩ : syracuseStep 368407 = 552611) B552611
theorem B368427 : Blo 366759 368427 := bstep (se 1 (by rfl) ⟨276320, by rfl⟩ : syracuseStep 368427 = 552641) B552641
theorem B368439 : Blo 366759 368439 := bstep (se 1 (by rfl) ⟨276329, by rfl⟩ : syracuseStep 368439 = 552659) B552659
theorem B368459 : Blo 366759 368459 := bstep (se 1 (by rfl) ⟨276344, by rfl⟩ : syracuseStep 368459 = 552689) B552689
theorem B368471 : Blo 366759 368471 := bstep (se 1 (by rfl) ⟨276353, by rfl⟩ : syracuseStep 368471 = 552707) B552707
theorem B827225 : Blo 366759 827225 := bstep (se 2 (by rfl) ⟨310209, by rfl⟩ : syracuseStep 827225 = 620419) B620419
theorem B368491 : Blo 366759 368491 := bstep (se 1 (by rfl) ⟨276368, by rfl⟩ : syracuseStep 368491 = 552737) B552737
theorem B368503 : Blo 366759 368503 := bstep (se 1 (by rfl) ⟨276377, by rfl⟩ : syracuseStep 368503 = 552755) B552755
theorem B368523 : Blo 366759 368523 := bstep (se 1 (by rfl) ⟨276392, by rfl⟩ : syracuseStep 368523 = 552785) B552785
theorem B368535 : Blo 366759 368535 := bstep (se 1 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 368535 = 552803) B552803
theorem B368555 : Blo 366759 368555 := bstep (se 1 (by rfl) ⟨276416, by rfl⟩ : syracuseStep 368555 = 552833) B552833
theorem B827315 : Blo 366759 827315 := bstep (se 1 (by rfl) ⟨620486, by rfl⟩ : syracuseStep 827315 = 1240973) B1240973
theorem B368567 : Blo 366759 368567 := bstep (se 1 (by rfl) ⟨276425, by rfl⟩ : syracuseStep 368567 = 552851) B552851
theorem B368587 : Blo 366759 368587 := bstep (se 1 (by rfl) ⟨276440, by rfl⟩ : syracuseStep 368587 = 552881) B552881
theorem B827351 : Blo 366759 827351 := bstep (se 1 (by rfl) ⟨620513, by rfl⟩ : syracuseStep 827351 = 1241027) B1241027
theorem B368599 : Blo 366759 368599 := bstep (se 1 (by rfl) ⟨276449, by rfl⟩ : syracuseStep 368599 = 552899) B552899
theorem B1122265 : Blo 366759 1122265 := bstep (se 2 (by rfl) ⟨420849, by rfl⟩ : syracuseStep 1122265 = 841699) B841699
theorem B368619 : Blo 366759 368619 := bstep (se 1 (by rfl) ⟨276464, by rfl⟩ : syracuseStep 368619 = 552929) B552929
theorem B368631 : Blo 366759 368631 := bstep (se 1 (by rfl) ⟨276473, by rfl⟩ : syracuseStep 368631 = 552947) B552947
theorem B368651 : Blo 366759 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B368663 : Blo 366759 368663 := bstep (se 1 (by rfl) ⟨276497, by rfl⟩ : syracuseStep 368663 = 552995) B552995
theorem B368683 : Blo 366759 368683 := bstep (se 1 (by rfl) ⟨276512, by rfl⟩ : syracuseStep 368683 = 553025) B553025
theorem B368695 : Blo 366759 368695 := bstep (se 1 (by rfl) ⟨276521, by rfl⟩ : syracuseStep 368695 = 553043) B553043
theorem B368715 : Blo 366759 368715 := bstep (se 1 (by rfl) ⟨276536, by rfl⟩ : syracuseStep 368715 = 553073) B553073
theorem B368727 : Blo 366759 368727 := bstep (se 1 (by rfl) ⟨276545, by rfl⟩ : syracuseStep 368727 = 553091) B553091
theorem B368747 : Blo 366759 368747 := bstep (se 1 (by rfl) ⟨276560, by rfl⟩ : syracuseStep 368747 = 553121) B553121
theorem B368759 : Blo 366759 368759 := bstep (se 1 (by rfl) ⟨276569, by rfl⟩ : syracuseStep 368759 = 553139) B553139
theorem B827531 : Blo 366759 827531 := bstep (se 1 (by rfl) ⟨620648, by rfl⟩ : syracuseStep 827531 = 1241297) B1241297
theorem B368779 : Blo 366759 368779 := bstep (se 1 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 368779 = 553169) B553169
theorem B368791 : Blo 366759 368791 := bstep (se 1 (by rfl) ⟨276593, by rfl⟩ : syracuseStep 368791 = 553187) B553187
theorem B368811 : Blo 366759 368811 := bstep (se 1 (by rfl) ⟨276608, by rfl⟩ : syracuseStep 368811 = 553217) B553217
theorem B368823 : Blo 366759 368823 := bstep (se 1 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 368823 = 553235) B553235
theorem B827585 : Blo 366759 827585 := bstep (se 2 (by rfl) ⟨310344, by rfl⟩ : syracuseStep 827585 = 620689) B620689
theorem B368843 : Blo 366759 368843 := bstep (se 1 (by rfl) ⟨276632, by rfl⟩ : syracuseStep 368843 = 553265) B553265
theorem B467147 : Blo 366759 467147 := bstep (se 1 (by rfl) ⟨350360, by rfl⟩ : syracuseStep 467147 = 700721) B700721
theorem B368855 : Blo 366759 368855 := bstep (se 1 (by rfl) ⟨276641, by rfl⟩ : syracuseStep 368855 = 553283) B553283
theorem B368875 : Blo 366759 368875 := bstep (se 1 (by rfl) ⟨276656, by rfl⟩ : syracuseStep 368875 = 553313) B553313
theorem B368887 : Blo 366759 368887 := bstep (se 1 (by rfl) ⟨276665, by rfl⟩ : syracuseStep 368887 = 553331) B553331
theorem B368907 : Blo 366759 368907 := bstep (se 1 (by rfl) ⟨276680, by rfl⟩ : syracuseStep 368907 = 553361) B553361
theorem B368919 : Blo 366759 368919 := bstep (se 1 (by rfl) ⟨276689, by rfl⟩ : syracuseStep 368919 = 553379) B553379
theorem B532759 : Blo 366759 532759 := bstep (se 1 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 532759 = 799139) B799139
theorem B368939 : Blo 366759 368939 := bstep (se 1 (by rfl) ⟨276704, by rfl⟩ : syracuseStep 368939 = 553409) B553409
theorem B368951 : Blo 366759 368951 := bstep (se 1 (by rfl) ⟨276713, by rfl⟩ : syracuseStep 368951 = 553427) B553427
theorem B368971 : Blo 366759 368971 := bstep (se 1 (by rfl) ⟨276728, by rfl⟩ : syracuseStep 368971 = 553457) B553457
theorem B368983 : Blo 366759 368983 := bstep (se 1 (by rfl) ⟨276737, by rfl⟩ : syracuseStep 368983 = 553475) B553475
theorem B369003 : Blo 366759 369003 := bstep (se 1 (by rfl) ⟨276752, by rfl⟩ : syracuseStep 369003 = 553505) B553505
theorem B369015 : Blo 366759 369015 := bstep (se 1 (by rfl) ⟨276761, by rfl⟩ : syracuseStep 369015 = 553523) B553523
theorem B369035 : Blo 366759 369035 := bstep (se 1 (by rfl) ⟨276776, by rfl⟩ : syracuseStep 369035 = 553553) B553553
theorem B369047 : Blo 366759 369047 := bstep (se 1 (by rfl) ⟨276785, by rfl⟩ : syracuseStep 369047 = 553571) B553571
theorem B827801 : Blo 366759 827801 := bstep (se 2 (by rfl) ⟨310425, by rfl⟩ : syracuseStep 827801 = 620851) B620851
theorem B369067 : Blo 366759 369067 := bstep (se 1 (by rfl) ⟨276800, by rfl⟩ : syracuseStep 369067 = 553601) B553601
theorem B6693299 : Blo 366759 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B369079 : Blo 366759 369079 := bstep (se 1 (by rfl) ⟨276809, by rfl⟩ : syracuseStep 369079 = 553619) B553619
theorem B369099 : Blo 366759 369099 := bstep (se 1 (by rfl) ⟨276824, by rfl⟩ : syracuseStep 369099 = 553649) B553649
theorem B369111 : Blo 366759 369111 := bstep (se 1 (by rfl) ⟨276833, by rfl⟩ : syracuseStep 369111 = 553667) B553667
theorem B369131 : Blo 366759 369131 := bstep (se 1 (by rfl) ⟨276848, by rfl⟩ : syracuseStep 369131 = 553697) B553697
theorem B827891 : Blo 366759 827891 := bstep (se 1 (by rfl) ⟨620918, by rfl⟩ : syracuseStep 827891 = 1241837) B1241837
theorem B369143 : Blo 366759 369143 := bstep (se 1 (by rfl) ⟨276857, by rfl⟩ : syracuseStep 369143 = 553715) B553715
theorem B696833 : Blo 366759 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B369163 : Blo 366759 369163 := bstep (se 1 (by rfl) ⟨276872, by rfl⟩ : syracuseStep 369163 = 553745) B553745
theorem B827927 : Blo 366759 827927 := bstep (se 1 (by rfl) ⟨620945, by rfl⟩ : syracuseStep 827927 = 1241891) B1241891
theorem B369175 : Blo 366759 369175 := bstep (se 1 (by rfl) ⟨276881, by rfl⟩ : syracuseStep 369175 = 553763) B553763
theorem B369195 : Blo 366759 369195 := bstep (se 1 (by rfl) ⟨276896, by rfl⟩ : syracuseStep 369195 = 553793) B553793
theorem B369207 : Blo 366759 369207 := bstep (se 1 (by rfl) ⟨276905, by rfl⟩ : syracuseStep 369207 = 553811) B553811
theorem B664129 : Blo 366759 664129 := bstep (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) B498097
theorem B369227 : Blo 366759 369227 := bstep (se 1 (by rfl) ⟨276920, by rfl⟩ : syracuseStep 369227 = 553841) B553841
theorem B369239 : Blo 366759 369239 := bstep (se 1 (by rfl) ⟨276929, by rfl⟩ : syracuseStep 369239 = 553859) B553859
theorem B369259 : Blo 366759 369259 := bstep (se 1 (by rfl) ⟨276944, by rfl⟩ : syracuseStep 369259 = 553889) B553889
theorem B369271 : Blo 366759 369271 := bstep (se 1 (by rfl) ⟨276953, by rfl⟩ : syracuseStep 369271 = 553907) B553907
theorem B369291 : Blo 366759 369291 := bstep (se 1 (by rfl) ⟨276968, by rfl⟩ : syracuseStep 369291 = 553937) B553937
theorem B369303 : Blo 366759 369303 := bstep (se 1 (by rfl) ⟨276977, by rfl⟩ : syracuseStep 369303 = 553955) B553955
theorem B369323 : Blo 366759 369323 := bstep (se 1 (by rfl) ⟨276992, by rfl⟩ : syracuseStep 369323 = 553985) B553985
theorem B369335 : Blo 366759 369335 := bstep (se 1 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 369335 = 554003) B554003
theorem B828107 : Blo 366759 828107 := bstep (se 1 (by rfl) ⟨621080, by rfl⟩ : syracuseStep 828107 = 1242161) B1242161
theorem B369355 : Blo 366759 369355 := bstep (se 1 (by rfl) ⟨277016, by rfl⟩ : syracuseStep 369355 = 554033) B554033
theorem B369367 : Blo 366759 369367 := bstep (se 1 (by rfl) ⟨277025, by rfl⟩ : syracuseStep 369367 = 554051) B554051
theorem B369387 : Blo 366759 369387 := bstep (se 1 (by rfl) ⟨277040, by rfl⟩ : syracuseStep 369387 = 554081) B554081
theorem B369399 : Blo 366759 369399 := bstep (se 1 (by rfl) ⟨277049, by rfl⟩ : syracuseStep 369399 = 554099) B554099
theorem B828161 : Blo 366759 828161 := bstep (se 2 (by rfl) ⟨310560, by rfl⟩ : syracuseStep 828161 = 621121) B621121
theorem B697099 : Blo 366759 697099 := bstep (se 1 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 697099 = 1045649) B1045649
theorem B369419 : Blo 366759 369419 := bstep (se 1 (by rfl) ⟨277064, by rfl⟩ : syracuseStep 369419 = 554129) B554129
theorem B598807 : Blo 366759 598807 := bstep (se 1 (by rfl) ⟨449105, by rfl⟩ : syracuseStep 598807 = 898211) B898211
theorem B369431 : Blo 366759 369431 := bstep (se 1 (by rfl) ⟨277073, by rfl⟩ : syracuseStep 369431 = 554147) B554147
theorem B369451 : Blo 366759 369451 := bstep (se 1 (by rfl) ⟨277088, by rfl⟩ : syracuseStep 369451 = 554177) B554177
theorem B1581869 : Blo 366759 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B369463 : Blo 366759 369463 := bstep (se 1 (by rfl) ⟨277097, by rfl⟩ : syracuseStep 369463 = 554195) B554195
theorem B369483 : Blo 366759 369483 := bstep (se 1 (by rfl) ⟨277112, by rfl⟩ : syracuseStep 369483 = 554225) B554225
theorem B369495 : Blo 366759 369495 := bstep (se 1 (by rfl) ⟨277121, by rfl⟩ : syracuseStep 369495 = 554243) B554243
theorem B369515 : Blo 366759 369515 := bstep (se 1 (by rfl) ⟨277136, by rfl⟩ : syracuseStep 369515 = 554273) B554273
theorem B369527 : Blo 366759 369527 := bstep (se 1 (by rfl) ⟨277145, by rfl⟩ : syracuseStep 369527 = 554291) B554291
theorem B369547 : Blo 366759 369547 := bstep (se 1 (by rfl) ⟨277160, by rfl⟩ : syracuseStep 369547 = 554321) B554321
theorem B467851 : Blo 366759 467851 := bstep (se 1 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 467851 = 701777) B701777
theorem B369559 : Blo 366759 369559 := bstep (se 1 (by rfl) ⟨277169, by rfl⟩ : syracuseStep 369559 = 554339) B554339
theorem B2106263 : Blo 366759 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B369579 : Blo 366759 369579 := bstep (se 1 (by rfl) ⟨277184, by rfl⟩ : syracuseStep 369579 = 554369) B554369
theorem B369591 : Blo 366759 369591 := bstep (se 1 (by rfl) ⟨277193, by rfl⟩ : syracuseStep 369591 = 554387) B554387
theorem B369611 : Blo 366759 369611 := bstep (se 1 (by rfl) ⟨277208, by rfl⟩ : syracuseStep 369611 = 554417) B554417
theorem B369623 : Blo 366759 369623 := bstep (se 1 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 369623 = 554435) B554435
theorem B828377 : Blo 366759 828377 := bstep (se 2 (by rfl) ⟨310641, by rfl⟩ : syracuseStep 828377 = 621283) B621283
theorem B369643 : Blo 366759 369643 := bstep (se 1 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 369643 = 554465) B554465
theorem B369655 : Blo 366759 369655 := bstep (se 1 (by rfl) ⟨277241, by rfl⟩ : syracuseStep 369655 = 554483) B554483
theorem B369675 : Blo 366759 369675 := bstep (se 1 (by rfl) ⟨277256, by rfl⟩ : syracuseStep 369675 = 554513) B554513
theorem B369687 : Blo 366759 369687 := bstep (se 1 (by rfl) ⟨277265, by rfl⟩ : syracuseStep 369687 = 554531) B554531
theorem B369707 : Blo 366759 369707 := bstep (se 1 (by rfl) ⟨277280, by rfl⟩ : syracuseStep 369707 = 554561) B554561
theorem B828467 : Blo 366759 828467 := bstep (se 1 (by rfl) ⟨621350, by rfl⟩ : syracuseStep 828467 = 1242701) B1242701
theorem B369719 : Blo 366759 369719 := bstep (se 1 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 369719 = 554579) B554579
theorem B369739 : Blo 366759 369739 := bstep (se 1 (by rfl) ⟨277304, by rfl⟩ : syracuseStep 369739 = 554609) B554609
theorem B828503 : Blo 366759 828503 := bstep (se 1 (by rfl) ⟨621377, by rfl⟩ : syracuseStep 828503 = 1242755) B1242755
theorem B369751 : Blo 366759 369751 := bstep (se 1 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 369751 = 554627) B554627
theorem B369771 : Blo 366759 369771 := bstep (se 1 (by rfl) ⟨277328, by rfl⟩ : syracuseStep 369771 = 554657) B554657
theorem B369783 : Blo 366759 369783 := bstep (se 1 (by rfl) ⟨277337, by rfl⟩ : syracuseStep 369783 = 554675) B554675
theorem B369803 : Blo 366759 369803 := bstep (se 1 (by rfl) ⟨277352, by rfl⟩ : syracuseStep 369803 = 554705) B554705
theorem B369815 : Blo 366759 369815 := bstep (se 1 (by rfl) ⟨277361, by rfl⟩ : syracuseStep 369815 = 554723) B554723
theorem B468119 : Blo 366759 468119 := bstep (se 1 (by rfl) ⟨351089, by rfl⟩ : syracuseStep 468119 = 702179) B702179
theorem B369835 : Blo 366759 369835 := bstep (se 1 (by rfl) ⟨277376, by rfl⟩ : syracuseStep 369835 = 554753) B554753
theorem B369847 : Blo 366759 369847 := bstep (se 1 (by rfl) ⟨277385, by rfl⟩ : syracuseStep 369847 = 554771) B554771
theorem B697547 : Blo 366759 697547 := bstep (se 1 (by rfl) ⟨523160, by rfl⟩ : syracuseStep 697547 = 1046321) B1046321
theorem B369867 : Blo 366759 369867 := bstep (se 1 (by rfl) ⟨277400, by rfl⟩ : syracuseStep 369867 = 554801) B554801
theorem B369879 : Blo 366759 369879 := bstep (se 1 (by rfl) ⟨277409, by rfl⟩ : syracuseStep 369879 = 554819) B554819
theorem B369899 : Blo 366759 369899 := bstep (se 1 (by rfl) ⟨277424, by rfl⟩ : syracuseStep 369899 = 554849) B554849
theorem B369911 : Blo 366759 369911 := bstep (se 1 (by rfl) ⟨277433, by rfl⟩ : syracuseStep 369911 = 554867) B554867
theorem B828683 : Blo 366759 828683 := bstep (se 1 (by rfl) ⟨621512, by rfl⟩ : syracuseStep 828683 = 1243025) B1243025
theorem B369931 : Blo 366759 369931 := bstep (se 1 (by rfl) ⟨277448, by rfl⟩ : syracuseStep 369931 = 554897) B554897
theorem B369943 : Blo 366759 369943 := bstep (se 1 (by rfl) ⟨277457, by rfl⟩ : syracuseStep 369943 = 554915) B554915
theorem B369963 : Blo 366759 369963 := bstep (se 1 (by rfl) ⟨277472, by rfl⟩ : syracuseStep 369963 = 554945) B554945
theorem B369975 : Blo 366759 369975 := bstep (se 1 (by rfl) ⟨277481, by rfl⟩ : syracuseStep 369975 = 554963) B554963
theorem B828737 : Blo 366759 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B369995 : Blo 366759 369995 := bstep (se 1 (by rfl) ⟨277496, by rfl⟩ : syracuseStep 369995 = 554993) B554993
theorem B370007 : Blo 366759 370007 := bstep (se 1 (by rfl) ⟨277505, by rfl⟩ : syracuseStep 370007 = 555011) B555011
theorem B370027 : Blo 366759 370027 := bstep (se 1 (by rfl) ⟨277520, by rfl⟩ : syracuseStep 370027 = 555041) B555041
theorem B370039 : Blo 366759 370039 := bstep (se 1 (by rfl) ⟨277529, by rfl⟩ : syracuseStep 370039 = 555059) B555059
theorem B697729 : Blo 366759 697729 := bstep (se 2 (by rfl) ⟨261648, by rfl⟩ : syracuseStep 697729 = 523297) B523297
theorem B370059 : Blo 366759 370059 := bstep (se 1 (by rfl) ⟨277544, by rfl⟩ : syracuseStep 370059 = 555089) B555089
theorem B370071 : Blo 366759 370071 := bstep (se 1 (by rfl) ⟨277553, by rfl⟩ : syracuseStep 370071 = 555107) B555107
theorem B370091 : Blo 366759 370091 := bstep (se 1 (by rfl) ⟨277568, by rfl⟩ : syracuseStep 370091 = 555137) B555137
theorem B370103 : Blo 366759 370103 := bstep (se 1 (by rfl) ⟨277577, by rfl⟩ : syracuseStep 370103 = 555155) B555155
theorem B370123 : Blo 366759 370123 := bstep (se 1 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 370123 = 555185) B555185
theorem B370135 : Blo 366759 370135 := bstep (se 1 (by rfl) ⟨277601, by rfl⟩ : syracuseStep 370135 = 555203) B555203
theorem B370155 : Blo 366759 370155 := bstep (se 1 (by rfl) ⟨277616, by rfl⟩ : syracuseStep 370155 = 555233) B555233
theorem B370167 : Blo 366759 370167 := bstep (se 1 (by rfl) ⟨277625, by rfl⟩ : syracuseStep 370167 = 555251) B555251
theorem B370187 : Blo 366759 370187 := bstep (se 1 (by rfl) ⟨277640, by rfl⟩ : syracuseStep 370187 = 555281) B555281
theorem B370199 : Blo 366759 370199 := bstep (se 1 (by rfl) ⟨277649, by rfl⟩ : syracuseStep 370199 = 555299) B555299
theorem B828953 : Blo 366759 828953 := bstep (se 2 (by rfl) ⟨310857, by rfl⟩ : syracuseStep 828953 = 621715) B621715
theorem B370219 : Blo 366759 370219 := bstep (se 1 (by rfl) ⟨277664, by rfl⟩ : syracuseStep 370219 = 555329) B555329
theorem B370231 : Blo 366759 370231 := bstep (se 1 (by rfl) ⟨277673, by rfl⟩ : syracuseStep 370231 = 555347) B555347
theorem B370251 : Blo 366759 370251 := bstep (se 1 (by rfl) ⟨277688, by rfl⟩ : syracuseStep 370251 = 555377) B555377
theorem B370263 : Blo 366759 370263 := bstep (se 1 (by rfl) ⟨277697, by rfl⟩ : syracuseStep 370263 = 555395) B555395
theorem B370283 : Blo 366759 370283 := bstep (se 1 (by rfl) ⟨277712, by rfl⟩ : syracuseStep 370283 = 555425) B555425
theorem B829043 : Blo 366759 829043 := bstep (se 1 (by rfl) ⟨621782, by rfl⟩ : syracuseStep 829043 = 1243565) B1243565
theorem B370295 : Blo 366759 370295 := bstep (se 1 (by rfl) ⟨277721, by rfl⟩ : syracuseStep 370295 = 555443) B555443
theorem B370315 : Blo 366759 370315 := bstep (se 1 (by rfl) ⟨277736, by rfl⟩ : syracuseStep 370315 = 555473) B555473
theorem B829079 : Blo 366759 829079 := bstep (se 1 (by rfl) ⟨621809, by rfl⟩ : syracuseStep 829079 = 1243619) B1243619
theorem B1418903 : Blo 366759 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B370327 : Blo 366759 370327 := bstep (se 1 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 370327 = 555491) B555491
theorem B370347 : Blo 366759 370347 := bstep (se 1 (by rfl) ⟨277760, by rfl⟩ : syracuseStep 370347 = 555521) B555521
theorem B370359 : Blo 366759 370359 := bstep (se 1 (by rfl) ⟨277769, by rfl⟩ : syracuseStep 370359 = 555539) B555539
theorem B370379 : Blo 366759 370379 := bstep (se 1 (by rfl) ⟨277784, by rfl⟩ : syracuseStep 370379 = 555569) B555569
theorem B698071 : Blo 366759 698071 := bstep (se 1 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 698071 = 1047107) B1047107
theorem B370391 : Blo 366759 370391 := bstep (se 1 (by rfl) ⟨277793, by rfl⟩ : syracuseStep 370391 = 555587) B555587
theorem B370411 : Blo 366759 370411 := bstep (se 1 (by rfl) ⟨277808, by rfl⟩ : syracuseStep 370411 = 555617) B555617
theorem B370423 : Blo 366759 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B370443 : Blo 366759 370443 := bstep (se 1 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 370443 = 555665) B555665
theorem B370455 : Blo 366759 370455 := bstep (se 1 (by rfl) ⟨277841, by rfl⟩ : syracuseStep 370455 = 555683) B555683
theorem B370475 : Blo 366759 370475 := bstep (se 1 (by rfl) ⟨277856, by rfl⟩ : syracuseStep 370475 = 555713) B555713
theorem B370487 : Blo 366759 370487 := bstep (se 1 (by rfl) ⟨277865, by rfl⟩ : syracuseStep 370487 = 555731) B555731
theorem B829259 : Blo 366759 829259 := bstep (se 1 (by rfl) ⟨621944, by rfl⟩ : syracuseStep 829259 = 1243889) B1243889
theorem B370507 : Blo 366759 370507 := bstep (se 1 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 370507 = 555761) B555761
theorem B468823 : Blo 366759 468823 := bstep (se 1 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 468823 = 703235) B703235
theorem B370519 : Blo 366759 370519 := bstep (se 1 (by rfl) ⟨277889, by rfl⟩ : syracuseStep 370519 = 555779) B555779
theorem B370539 : Blo 366759 370539 := bstep (se 1 (by rfl) ⟨277904, by rfl⟩ : syracuseStep 370539 = 555809) B555809
theorem B370551 : Blo 366759 370551 := bstep (se 1 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 370551 = 555827) B555827
theorem B829313 : Blo 366759 829313 := bstep (se 2 (by rfl) ⟨310992, by rfl⟩ : syracuseStep 829313 = 621985) B621985
theorem B370571 : Blo 366759 370571 := bstep (se 1 (by rfl) ⟨277928, by rfl⟩ : syracuseStep 370571 = 555857) B555857
theorem B370583 : Blo 366759 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B370603 : Blo 366759 370603 := bstep (se 1 (by rfl) ⟨277952, by rfl⟩ : syracuseStep 370603 = 555905) B555905
theorem B698291 : Blo 366759 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B370615 : Blo 366759 370615 := bstep (se 1 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 370615 = 555923) B555923
theorem B370635 : Blo 366759 370635 := bstep (se 1 (by rfl) ⟨277976, by rfl⟩ : syracuseStep 370635 = 555953) B555953
theorem B370647 : Blo 366759 370647 := bstep (se 1 (by rfl) ⟨277985, by rfl⟩ : syracuseStep 370647 = 555971) B555971
theorem B370667 : Blo 366759 370667 := bstep (se 1 (by rfl) ⟨278000, by rfl⟩ : syracuseStep 370667 = 556001) B556001
theorem B370679 : Blo 366759 370679 := bstep (se 1 (by rfl) ⟨278009, by rfl⟩ : syracuseStep 370679 = 556019) B556019
theorem B370699 : Blo 366759 370699 := bstep (se 1 (by rfl) ⟨278024, by rfl⟩ : syracuseStep 370699 = 556049) B556049
theorem B370711 : Blo 366759 370711 := bstep (se 1 (by rfl) ⟨278033, by rfl⟩ : syracuseStep 370711 = 556067) B556067
theorem B370731 : Blo 366759 370731 := bstep (se 1 (by rfl) ⟨278048, by rfl⟩ : syracuseStep 370731 = 556097) B556097
theorem B370743 : Blo 366759 370743 := bstep (se 1 (by rfl) ⟨278057, by rfl⟩ : syracuseStep 370743 = 556115) B556115
theorem B829529 : Blo 366759 829529 := bstep (se 2 (by rfl) ⟨311073, by rfl⟩ : syracuseStep 829529 = 622147) B622147
theorem B2402405 : Blo 366759 2402405 := bstep (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) B450451
theorem B698519 : Blo 366759 698519 := bstep (se 1 (by rfl) ⟨523889, by rfl⟩ : syracuseStep 698519 = 1047779) B1047779
theorem B829619 : Blo 366759 829619 := bstep (se 1 (by rfl) ⟨622214, by rfl⟩ : syracuseStep 829619 = 1244429) B1244429
theorem B829655 : Blo 366759 829655 := bstep (se 1 (by rfl) ⟨622241, by rfl⟩ : syracuseStep 829655 = 1244483) B1244483
theorem B829835 : Blo 366759 829835 := bstep (se 1 (by rfl) ⟨622376, by rfl⟩ : syracuseStep 829835 = 1244753) B1244753
theorem B698777 : Blo 366759 698777 := bstep (se 2 (by rfl) ⟨262041, by rfl⟩ : syracuseStep 698777 = 524083) B524083
theorem B829889 : Blo 366759 829889 := bstep (se 2 (by rfl) ⟨311208, by rfl⟩ : syracuseStep 829889 = 622417) B622417
theorem B1681937 : Blo 366759 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B4237859 : Blo 366759 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B2992733 : Blo 366759 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B830105 : Blo 366759 830105 := bstep (se 2 (by rfl) ⟨311289, by rfl⟩ : syracuseStep 830105 = 622579) B622579
theorem B830195 : Blo 366759 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B2108177 : Blo 366759 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B830231 : Blo 366759 830231 := bstep (se 1 (by rfl) ⟨622673, by rfl⟩ : syracuseStep 830231 = 1245347) B1245347
theorem B699187 : Blo 366759 699187 := bstep (se 1 (by rfl) ⟨524390, by rfl⟩ : syracuseStep 699187 = 1048781) B1048781
theorem B928705 : Blo 366759 928705 := bstep (se 2 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 928705 = 696529) B696529
theorem B830411 : Blo 366759 830411 := bstep (se 1 (by rfl) ⟨622808, by rfl⟩ : syracuseStep 830411 = 1245617) B1245617
theorem B3550169 : Blo 366759 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B1780697 : Blo 366759 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B830465 : Blo 366759 830465 := bstep (se 2 (by rfl) ⟨311424, by rfl⟩ : syracuseStep 830465 = 622849) B622849
theorem B666739 : Blo 366759 666739 := bstep (se 1 (by rfl) ⟨500054, by rfl⟩ : syracuseStep 666739 = 1000109) B1000109
theorem B666839 : Blo 366759 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B830681 : Blo 366759 830681 := bstep (se 2 (by rfl) ⟨311505, by rfl⟩ : syracuseStep 830681 = 623011) B623011
theorem B699673 : Blo 366759 699673 := bstep (se 2 (by rfl) ⟨262377, by rfl⟩ : syracuseStep 699673 = 524755) B524755
theorem B830771 : Blo 366759 830771 := bstep (se 1 (by rfl) ⟨623078, by rfl⟩ : syracuseStep 830771 = 1246157) B1246157
theorem B830807 : Blo 366759 830807 := bstep (se 1 (by rfl) ⟨623105, by rfl⟩ : syracuseStep 830807 = 1246211) B1246211
theorem B1420747 : Blo 366759 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B830987 : Blo 366759 830987 := bstep (se 1 (by rfl) ⟨623240, by rfl⟩ : syracuseStep 830987 = 1246481) B1246481
theorem B929303 : Blo 366759 929303 := bstep (se 1 (by rfl) ⟨696977, by rfl⟩ : syracuseStep 929303 = 1393955) B1393955
theorem B831041 : Blo 366759 831041 := bstep (se 2 (by rfl) ⟨311640, by rfl⟩ : syracuseStep 831041 = 623281) B623281
theorem B5385989 : Blo 366759 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B831257 : Blo 366759 831257 := bstep (se 2 (by rfl) ⟨311721, by rfl⟩ : syracuseStep 831257 = 623443) B623443
theorem B700235 : Blo 366759 700235 := bstep (se 1 (by rfl) ⟨525176, by rfl⟩ : syracuseStep 700235 = 1050353) B1050353
theorem B831347 : Blo 366759 831347 := bstep (se 1 (by rfl) ⟨623510, by rfl⟩ : syracuseStep 831347 = 1247021) B1247021
theorem B831383 : Blo 366759 831383 := bstep (se 1 (by rfl) ⟨623537, by rfl⟩ : syracuseStep 831383 = 1247075) B1247075
theorem B700417 : Blo 366759 700417 := bstep (se 2 (by rfl) ⟨262656, by rfl⟩ : syracuseStep 700417 = 525313) B525313
theorem B831563 : Blo 366759 831563 := bstep (se 1 (by rfl) ⟨623672, by rfl⟩ : syracuseStep 831563 = 1247345) B1247345
theorem B831617 : Blo 366759 831617 := bstep (se 2 (by rfl) ⟨311856, by rfl⟩ : syracuseStep 831617 = 623713) B623713
theorem B372875 : Blo 366759 372875 := bstep (se 1 (by rfl) ⟨279656, by rfl⟩ : syracuseStep 372875 = 559313) B559313
theorem B930113 : Blo 366759 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B831833 : Blo 366759 831833 := bstep (se 2 (by rfl) ⟨311937, by rfl⟩ : syracuseStep 831833 = 623875) B623875
theorem B831923 : Blo 366759 831923 := bstep (se 1 (by rfl) ⟨623942, by rfl⟩ : syracuseStep 831923 = 1247885) B1247885
theorem B831959 : Blo 366759 831959 := bstep (se 1 (by rfl) ⟨623969, by rfl⟩ : syracuseStep 831959 = 1247939) B1247939
theorem B832139 : Blo 366759 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B832193 : Blo 366759 832193 := bstep (se 2 (by rfl) ⟨312072, by rfl⟩ : syracuseStep 832193 = 624145) B624145
theorem B701131 : Blo 366759 701131 := bstep (se 1 (by rfl) ⟨525848, by rfl⟩ : syracuseStep 701131 = 1051697) B1051697
theorem B701207 : Blo 366759 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B2503489 : Blo 366759 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B930649 : Blo 366759 930649 := bstep (se 2 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 930649 = 697987) B697987
theorem B832409 : Blo 366759 832409 := bstep (se 2 (by rfl) ⟨312153, by rfl⟩ : syracuseStep 832409 = 624307) B624307
theorem B832499 : Blo 366759 832499 := bstep (se 1 (by rfl) ⟨624374, by rfl⟩ : syracuseStep 832499 = 1248749) B1248749
theorem B832535 : Blo 366759 832535 := bstep (se 1 (by rfl) ⟨624401, by rfl⟩ : syracuseStep 832535 = 1248803) B1248803
theorem B832715 : Blo 366759 832715 := bstep (se 1 (by rfl) ⟨624536, by rfl⟩ : syracuseStep 832715 = 1249073) B1249073
theorem B832769 : Blo 366759 832769 := bstep (se 2 (by rfl) ⟨312288, by rfl⟩ : syracuseStep 832769 = 624577) B624577
theorem B1684909 : Blo 366759 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B701875 : Blo 366759 701875 := bstep (se 1 (by rfl) ⟨526406, by rfl⟩ : syracuseStep 701875 = 1052813) B1052813
theorem B832985 : Blo 366759 832985 := bstep (se 2 (by rfl) ⟨312369, by rfl⟩ : syracuseStep 832985 = 624739) B624739
theorem B2668049 : Blo 366759 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2373137 : Blo 366759 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B833075 : Blo 366759 833075 := bstep (se 1 (by rfl) ⟨624806, by rfl⟩ : syracuseStep 833075 = 1249613) B1249613
theorem B833111 : Blo 366759 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B5289623 : Blo 366759 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B702103 : Blo 366759 702103 := bstep (se 1 (by rfl) ⟨526577, by rfl⟩ : syracuseStep 702103 = 1053155) B1053155
theorem B702209 : Blo 366759 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B833291 : Blo 366759 833291 := bstep (se 1 (by rfl) ⟨624968, by rfl⟩ : syracuseStep 833291 = 1249937) B1249937
theorem B833345 : Blo 366759 833345 := bstep (se 2 (by rfl) ⟨312504, by rfl⟩ : syracuseStep 833345 = 625009) B625009
theorem B767873 : Blo 366759 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B2701187 : Blo 366759 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B702361 : Blo 366759 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B931763 : Blo 366759 931763 := bstep (se 1 (by rfl) ⟨698822, by rfl⟩ : syracuseStep 931763 = 1397645) B1397645
theorem B833561 : Blo 366759 833561 := bstep (se 2 (by rfl) ⟨312585, by rfl⟩ : syracuseStep 833561 = 625171) B625171
theorem B997427 : Blo 366759 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B833651 : Blo 366759 833651 := bstep (se 1 (by rfl) ⟨625238, by rfl⟩ : syracuseStep 833651 = 1250477) B1250477
theorem B637067 : Blo 366759 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B833687 : Blo 366759 833687 := bstep (se 1 (by rfl) ⟨625265, by rfl⟩ : syracuseStep 833687 = 1250531) B1250531
theorem B932057 : Blo 366759 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B833867 : Blo 366759 833867 := bstep (se 1 (by rfl) ⟨625400, by rfl⟩ : syracuseStep 833867 = 1250801) B1250801
theorem B538969 : Blo 366759 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B833921 : Blo 366759 833921 := bstep (se 2 (by rfl) ⟨312720, by rfl⟩ : syracuseStep 833921 = 625441) B625441
theorem B834137 : Blo 366759 834137 := bstep (se 2 (by rfl) ⟨312801, by rfl⟩ : syracuseStep 834137 = 625603) B625603
theorem B4209245 : Blo 366759 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B4733761 : Blo 366759 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B5323637 : Blo 366759 5323637 := bstep (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) B499091
theorem B801665 : Blo 366759 801665 := bstep (se 2 (by rfl) ⟨300624, by rfl⟩ : syracuseStep 801665 = 601249) B601249
theorem B3161105 : Blo 366759 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B6077591 : Blo 366759 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B2800817 : Blo 366759 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B703667 : Blo 366759 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B1326401 : Blo 366759 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B703819 : Blo 366759 703819 := bstep (se 1 (by rfl) ⟨527864, by rfl⟩ : syracuseStep 703819 = 1055729) B1055729
theorem B998963 : Blo 366759 998963 := bstep (se 1 (by rfl) ⟨749222, by rfl⟩ : syracuseStep 998963 = 1498445) B1498445
theorem B2801303 : Blo 366759 2801303 := bstep (se 1 (by rfl) ⟨2100977, by rfl⟩ : syracuseStep 2801303 = 4201955) B4201955
theorem B5062445 : Blo 366759 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B933707 : Blo 366759 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B475031 : Blo 366759 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B1589341 : Blo 366759 1589341 := bstep (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) B596003
theorem B1392785 : Blo 366759 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B442955 : Blo 366759 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B1262231 : Blo 366759 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B934679 : Blo 366759 934679 := bstep (se 1 (by rfl) ⟨701009, by rfl⟩ : syracuseStep 934679 = 1402019) B1402019
theorem B1393483 : Blo 366759 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B9487205 : Blo 366759 9487205 := bstep (se 4 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 9487205 = 1778851) B1778851
theorem B1393757 : Blo 366759 1393757 := bstep (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) B522659
theorem B1361197 : Blo 366759 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B935347 : Blo 366759 935347 := bstep (se 1 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 935347 = 1403021) B1403021
theorem B935489 : Blo 366759 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B1394455 : Blo 366759 1394455 := bstep (se 1 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 1394455 = 2091683) B2091683
theorem B1395245 : Blo 366759 1395245 := bstep (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) B523217
theorem B1690163 : Blo 366759 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B936755 : Blo 366759 936755 := bstep (se 1 (by rfl) ⟨702566, by rfl⟩ : syracuseStep 936755 = 1405133) B1405133
theorem B838487 : Blo 366759 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B412663 : Blo 366759 412663 := bstep (se 1 (by rfl) ⟨309497, by rfl⟩ : syracuseStep 412663 = 618995) B618995
theorem B412843 : Blo 366759 412843 := bstep (se 1 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 412843 = 619265) B619265
theorem B412951 : Blo 366759 412951 := bstep (se 1 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 412951 = 619427) B619427
theorem B937291 : Blo 366759 937291 := bstep (se 1 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 937291 = 1405937) B1405937
theorem B413131 : Blo 366759 413131 := bstep (se 1 (by rfl) ⟨309848, by rfl⟩ : syracuseStep 413131 = 619697) B619697
theorem B937433 : Blo 366759 937433 := bstep (se 2 (by rfl) ⟨351537, by rfl⟩ : syracuseStep 937433 = 703075) B703075
theorem B413239 : Blo 366759 413239 := bstep (se 1 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 413239 = 619859) B619859
theorem B413419 : Blo 366759 413419 := bstep (se 1 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 413419 = 620129) B620129
theorem B413527 : Blo 366759 413527 := bstep (se 1 (by rfl) ⟨310145, by rfl⟩ : syracuseStep 413527 = 620291) B620291
theorem B1396673 : Blo 366759 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B413707 : Blo 366759 413707 := bstep (se 1 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 413707 = 620561) B620561
theorem B413815 : Blo 366759 413815 := bstep (se 1 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 413815 = 620723) B620723
theorem B2248883 : Blo 366759 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B1331473 : Blo 366759 1331473 := bstep (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) B998605
theorem B938263 : Blo 366759 938263 := bstep (se 1 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 938263 = 1407395) B1407395
theorem B413995 : Blo 366759 413995 := bstep (se 1 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 413995 = 620993) B620993
theorem B414103 : Blo 366759 414103 := bstep (se 1 (by rfl) ⟨310577, by rfl⟩ : syracuseStep 414103 = 621155) B621155
theorem B414283 : Blo 366759 414283 := bstep (se 1 (by rfl) ⟨310712, by rfl⟩ : syracuseStep 414283 = 621425) B621425
theorem B1495703 : Blo 366759 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B414391 : Blo 366759 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B840385 : Blo 366759 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B3134213 : Blo 366759 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B414571 : Blo 366759 414571 := bstep (se 1 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 414571 = 621857) B621857
theorem B1496011 : Blo 366759 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B414679 : Blo 366759 414679 := bstep (se 1 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 414679 = 622019) B622019
theorem B4183001 : Blo 366759 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B414859 : Blo 366759 414859 := bstep (se 1 (by rfl) ⟨311144, by rfl⟩ : syracuseStep 414859 = 622289) B622289
theorem B414967 : Blo 366759 414967 := bstep (se 1 (by rfl) ⟨311225, by rfl⟩ : syracuseStep 414967 = 622451) B622451
theorem B1856843 : Blo 366759 1856843 := bstep (se 1 (by rfl) ⟨1392632, by rfl⟩ : syracuseStep 1856843 = 2785265) B2785265
theorem B7853429 : Blo 366759 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B1398161 : Blo 366759 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B415147 : Blo 366759 415147 := bstep (se 1 (by rfl) ⟨311360, by rfl⟩ : syracuseStep 415147 = 622721) B622721
theorem B808385 : Blo 366759 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B415255 : Blo 366759 415255 := bstep (se 1 (by rfl) ⟨311441, by rfl⟩ : syracuseStep 415255 = 622883) B622883
theorem B1496627 : Blo 366759 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B415435 : Blo 366759 415435 := bstep (se 1 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 415435 = 623153) B623153
theorem B415543 : Blo 366759 415543 := bstep (se 1 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 415543 = 623315) B623315
theorem B3200843 : Blo 366759 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1398617 : Blo 366759 1398617 := bstep (se 2 (by rfl) ⟨524481, by rfl⟩ : syracuseStep 1398617 = 1048963) B1048963
theorem B415723 : Blo 366759 415723 := bstep (se 1 (by rfl) ⟨311792, by rfl⟩ : syracuseStep 415723 = 623585) B623585
theorem B1398829 : Blo 366759 1398829 := bstep (se 3 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 1398829 = 524561) B524561
theorem B1595467 : Blo 366759 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B415831 : Blo 366759 415831 := bstep (se 1 (by rfl) ⟨311873, by rfl⟩ : syracuseStep 415831 = 623747) B623747
theorem B416011 : Blo 366759 416011 := bstep (se 1 (by rfl) ⟨312008, by rfl⟩ : syracuseStep 416011 = 624017) B624017
theorem B2644289 : Blo 366759 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B1399133 : Blo 366759 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B416119 : Blo 366759 416119 := bstep (se 1 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 416119 = 624179) B624179
theorem B449047 : Blo 366759 449047 := bstep (se 1 (by rfl) ⟨336785, by rfl⟩ : syracuseStep 449047 = 673571) B673571
theorem B416299 : Blo 366759 416299 := bstep (se 1 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 416299 = 624449) B624449
theorem B744025 : Blo 366759 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B416407 : Blo 366759 416407 := bstep (se 1 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 416407 = 624611) B624611
theorem B2808593 : Blo 366759 2808593 := bstep (se 2 (by rfl) ⟨1053222, by rfl⟩ : syracuseStep 2808593 = 2106445) B2106445
theorem B416587 : Blo 366759 416587 := bstep (se 1 (by rfl) ⟨312440, by rfl⟩ : syracuseStep 416587 = 624881) B624881
theorem B2349917 : Blo 366759 2349917 := bstep (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) B881219
theorem B416695 : Blo 366759 416695 := bstep (se 1 (by rfl) ⟨312521, by rfl⟩ : syracuseStep 416695 = 625043) B625043
theorem B1858625 : Blo 366759 1858625 := bstep (se 2 (by rfl) ⟨696984, by rfl⟩ : syracuseStep 1858625 = 1393969) B1393969
theorem B416875 : Blo 366759 416875 := bstep (se 1 (by rfl) ⟨312656, by rfl⟩ : syracuseStep 416875 = 625313) B625313
theorem B416983 : Blo 366759 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B2252333 : Blo 366759 2252333 := bstep (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) B844625
theorem B1498769 : Blo 366759 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B1335005 : Blo 366759 1335005 := bstep (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) B500627
theorem B3006557 : Blo 366759 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B1401731 : Blo 366759 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B1401745 : Blo 366759 1401745 := bstep (se 2 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 1401745 = 1051309) B1051309
theorem B2089907 : Blo 366759 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B1860569 : Blo 366759 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B910387 : Blo 366759 910387 := bstep (se 1 (by rfl) ⟨682790, by rfl⟩ : syracuseStep 910387 = 1365581) B1365581
theorem B746561 : Blo 366759 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B3531869 : Blo 366759 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B1402049 : Blo 366759 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B1238219 : Blo 366759 1238219 := bstep (se 1 (by rfl) ⟨928664, by rfl⟩ : syracuseStep 1238219 = 1857329) B1857329
theorem B3368141 : Blo 366759 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B550169 : Blo 366759 550169 := bstep (se 2 (by rfl) ⟨206313, by rfl⟩ : syracuseStep 550169 = 412627) B412627
theorem B550283 : Blo 366759 550283 := bstep (se 1 (by rfl) ⟨412712, by rfl⟩ : syracuseStep 550283 = 825425) B825425
theorem B550295 : Blo 366759 550295 := bstep (se 1 (by rfl) ⟨412721, by rfl⟩ : syracuseStep 550295 = 825443) B825443
theorem B943553 : Blo 366759 943553 := bstep (se 2 (by rfl) ⟨353832, by rfl⟩ : syracuseStep 943553 = 707665) B707665
theorem B550361 : Blo 366759 550361 := bstep (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) B412771
theorem B1238489 : Blo 366759 1238489 := bstep (se 2 (by rfl) ⟨464433, by rfl⟩ : syracuseStep 1238489 = 928867) B928867
theorem B6743569 : Blo 366759 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1009217 : Blo 366759 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B550475 : Blo 366759 550475 := bstep (se 1 (by rfl) ⟨412856, by rfl⟩ : syracuseStep 550475 = 825713) B825713
theorem B550487 : Blo 366759 550487 := bstep (se 1 (by rfl) ⟨412865, by rfl⟩ : syracuseStep 550487 = 825731) B825731
theorem B6448733 : Blo 366759 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B6416023 : Blo 366759 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B550553 : Blo 366759 550553 := bstep (se 2 (by rfl) ⟨206457, by rfl⟩ : syracuseStep 550553 = 412915) B412915
theorem B550667 : Blo 366759 550667 := bstep (se 1 (by rfl) ⟨413000, by rfl⟩ : syracuseStep 550667 = 826001) B826001
theorem B550679 : Blo 366759 550679 := bstep (se 1 (by rfl) ⟨413009, by rfl⟩ : syracuseStep 550679 = 826019) B826019
theorem B550745 : Blo 366759 550745 := bstep (se 2 (by rfl) ⟨206529, by rfl⟩ : syracuseStep 550745 = 413059) B413059
theorem B1402717 : Blo 366759 1402717 := bstep (se 3 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 1402717 = 526019) B526019
theorem B2418611 : Blo 366759 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B550859 : Blo 366759 550859 := bstep (se 1 (by rfl) ⟨413144, by rfl⟩ : syracuseStep 550859 = 826289) B826289
theorem B550871 : Blo 366759 550871 := bstep (se 1 (by rfl) ⟨413153, by rfl⟩ : syracuseStep 550871 = 826307) B826307
theorem B550937 : Blo 366759 550937 := bstep (se 2 (by rfl) ⟨206601, by rfl⟩ : syracuseStep 550937 = 413203) B413203
theorem B551051 : Blo 366759 551051 := bstep (se 1 (by rfl) ⟨413288, by rfl⟩ : syracuseStep 551051 = 826577) B826577
theorem B1239191 : Blo 366759 1239191 := bstep (se 1 (by rfl) ⟨929393, by rfl⟩ : syracuseStep 1239191 = 1858787) B1858787
theorem B551063 : Blo 366759 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B551129 : Blo 366759 551129 := bstep (se 2 (by rfl) ⟨206673, by rfl⟩ : syracuseStep 551129 = 413347) B413347
theorem B551243 : Blo 366759 551243 := bstep (se 1 (by rfl) ⟨413432, by rfl⟩ : syracuseStep 551243 = 826865) B826865
theorem B551255 : Blo 366759 551255 := bstep (se 1 (by rfl) ⟨413441, by rfl⟩ : syracuseStep 551255 = 826883) B826883
theorem B2091365 : Blo 366759 2091365 := bstep (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) B392131
theorem B551321 : Blo 366759 551321 := bstep (se 2 (by rfl) ⟨206745, by rfl⟩ : syracuseStep 551321 = 413491) B413491
theorem B551435 : Blo 366759 551435 := bstep (se 1 (by rfl) ⟨413576, by rfl⟩ : syracuseStep 551435 = 827153) B827153
theorem B551447 : Blo 366759 551447 := bstep (se 1 (by rfl) ⟨413585, by rfl⟩ : syracuseStep 551447 = 827171) B827171
theorem B1862189 : Blo 366759 1862189 := bstep (se 3 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 1862189 = 698321) B698321
theorem B2812481 : Blo 366759 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B551513 : Blo 366759 551513 := bstep (se 2 (by rfl) ⟨206817, by rfl⟩ : syracuseStep 551513 = 413635) B413635
theorem B1239731 : Blo 366759 1239731 := bstep (se 1 (by rfl) ⟨929798, by rfl⟩ : syracuseStep 1239731 = 1859597) B1859597
theorem B551627 : Blo 366759 551627 := bstep (se 1 (by rfl) ⟨413720, by rfl⟩ : syracuseStep 551627 = 827441) B827441
theorem B551639 : Blo 366759 551639 := bstep (se 1 (by rfl) ⟨413729, by rfl⟩ : syracuseStep 551639 = 827459) B827459
theorem B715481 : Blo 366759 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B551705 : Blo 366759 551705 := bstep (se 2 (by rfl) ⟨206889, by rfl⟩ : syracuseStep 551705 = 413779) B413779
theorem B551819 : Blo 366759 551819 := bstep (se 1 (by rfl) ⟨413864, by rfl⟩ : syracuseStep 551819 = 827729) B827729
theorem B551831 : Blo 366759 551831 := bstep (se 1 (by rfl) ⟨413873, by rfl⟩ : syracuseStep 551831 = 827747) B827747
theorem B1240001 : Blo 366759 1240001 := bstep (se 2 (by rfl) ⟨465000, by rfl⟩ : syracuseStep 1240001 = 930001) B930001
theorem B551897 : Blo 366759 551897 := bstep (se 2 (by rfl) ⟨206961, by rfl⟩ : syracuseStep 551897 = 413923) B413923
theorem B552011 : Blo 366759 552011 := bstep (se 1 (by rfl) ⟨414008, by rfl⟩ : syracuseStep 552011 = 828017) B828017
theorem B552023 : Blo 366759 552023 := bstep (se 1 (by rfl) ⟨414017, by rfl⟩ : syracuseStep 552023 = 828035) B828035
theorem B1403993 : Blo 366759 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B552089 : Blo 366759 552089 := bstep (se 2 (by rfl) ⟨207033, by rfl⟩ : syracuseStep 552089 = 414067) B414067
theorem B1502401 : Blo 366759 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B552203 : Blo 366759 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B552215 : Blo 366759 552215 := bstep (se 1 (by rfl) ⟨414161, by rfl⟩ : syracuseStep 552215 = 828323) B828323
theorem B552281 : Blo 366759 552281 := bstep (se 2 (by rfl) ⟨207105, by rfl⟩ : syracuseStep 552281 = 414211) B414211
theorem B552395 : Blo 366759 552395 := bstep (se 1 (by rfl) ⟨414296, by rfl⟩ : syracuseStep 552395 = 828593) B828593
theorem B552407 : Blo 366759 552407 := bstep (se 1 (by rfl) ⟨414305, by rfl⟩ : syracuseStep 552407 = 828611) B828611
theorem B1240541 : Blo 366759 1240541 := bstep (se 3 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 1240541 = 465203) B465203
theorem B552473 : Blo 366759 552473 := bstep (se 2 (by rfl) ⟨207177, by rfl⟩ : syracuseStep 552473 = 414355) B414355
theorem B1601117 : Blo 366759 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B4746883 : Blo 366759 4746883 := bstep (se 1 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 4746883 = 7120325) B7120325
theorem B552587 : Blo 366759 552587 := bstep (se 1 (by rfl) ⟨414440, by rfl⟩ : syracuseStep 552587 = 828881) B828881
theorem B552599 : Blo 366759 552599 := bstep (se 1 (by rfl) ⟨414449, by rfl⟩ : syracuseStep 552599 = 828899) B828899
theorem B552665 : Blo 366759 552665 := bstep (se 2 (by rfl) ⟨207249, by rfl⟩ : syracuseStep 552665 = 414499) B414499
theorem B5041925 : Blo 366759 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B2354989 : Blo 366759 2354989 := bstep (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) B883121
theorem B3534637 : Blo 366759 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B552779 : Blo 366759 552779 := bstep (se 1 (by rfl) ⟨414584, by rfl⟩ : syracuseStep 552779 = 829169) B829169
theorem B552791 : Blo 366759 552791 := bstep (se 1 (by rfl) ⟨414593, by rfl⟩ : syracuseStep 552791 = 829187) B829187
theorem B1863575 : Blo 366759 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B552857 : Blo 366759 552857 := bstep (se 2 (by rfl) ⟨207321, by rfl⟩ : syracuseStep 552857 = 414643) B414643
theorem B552971 : Blo 366759 552971 := bstep (se 1 (by rfl) ⟨414728, by rfl⟩ : syracuseStep 552971 = 829457) B829457
theorem B552983 : Blo 366759 552983 := bstep (se 1 (by rfl) ⟨414737, by rfl⟩ : syracuseStep 552983 = 829475) B829475
theorem B553049 : Blo 366759 553049 := bstep (se 2 (by rfl) ⟨207393, by rfl⟩ : syracuseStep 553049 = 414787) B414787
theorem B1568899 : Blo 366759 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B553163 : Blo 366759 553163 := bstep (se 1 (by rfl) ⟨414872, by rfl⟩ : syracuseStep 553163 = 829745) B829745
theorem B553175 : Blo 366759 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B553241 : Blo 366759 553241 := bstep (se 2 (by rfl) ⟨207465, by rfl⟩ : syracuseStep 553241 = 414931) B414931
theorem B6320429 : Blo 366759 6320429 := bstep (se 3 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 6320429 = 2370161) B2370161
theorem B553355 : Blo 366759 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B553367 : Blo 366759 553367 := bstep (se 1 (by rfl) ⟨415025, by rfl⟩ : syracuseStep 553367 = 830051) B830051
theorem B553433 : Blo 366759 553433 := bstep (se 2 (by rfl) ⟨207537, by rfl⟩ : syracuseStep 553433 = 415075) B415075
theorem B2814425 : Blo 366759 2814425 := bstep (se 2 (by rfl) ⟨1055409, by rfl⟩ : syracuseStep 2814425 = 2110819) B2110819
theorem B1241675 : Blo 366759 1241675 := bstep (se 1 (by rfl) ⟨931256, by rfl⟩ : syracuseStep 1241675 = 1862513) B1862513
theorem B553547 : Blo 366759 553547 := bstep (se 1 (by rfl) ⟨415160, by rfl⟩ : syracuseStep 553547 = 830321) B830321
theorem B553559 : Blo 366759 553559 := bstep (se 1 (by rfl) ⟨415169, by rfl⟩ : syracuseStep 553559 = 830339) B830339
theorem B2388631 : Blo 366759 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B553625 : Blo 366759 553625 := bstep (se 2 (by rfl) ⟨207609, by rfl⟩ : syracuseStep 553625 = 415219) B415219
theorem B750259 : Blo 366759 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B1405619 : Blo 366759 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B1405633 : Blo 366759 1405633 := bstep (se 2 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 1405633 = 1054225) B1054225
theorem B619211 : Blo 366759 619211 := bstep (se 1 (by rfl) ⟨464408, by rfl⟩ : syracuseStep 619211 = 928817) B928817
theorem B422615 : Blo 366759 422615 := bstep (se 1 (by rfl) ⟨316961, by rfl⟩ : syracuseStep 422615 = 633923) B633923
theorem B553739 : Blo 366759 553739 := bstep (se 1 (by rfl) ⟨415304, by rfl⟩ : syracuseStep 553739 = 830609) B830609
theorem B553751 : Blo 366759 553751 := bstep (se 1 (by rfl) ⟨415313, by rfl⟩ : syracuseStep 553751 = 830627) B830627
theorem B619339 : Blo 366759 619339 := bstep (se 1 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 619339 = 929009) B929009
theorem B1241945 : Blo 366759 1241945 := bstep (se 2 (by rfl) ⟨465729, by rfl⟩ : syracuseStep 1241945 = 931459) B931459
theorem B553817 : Blo 366759 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B4027315 : Blo 366759 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B553931 : Blo 366759 553931 := bstep (se 1 (by rfl) ⟨415448, by rfl⟩ : syracuseStep 553931 = 830897) B830897
theorem B553943 : Blo 366759 553943 := bstep (se 1 (by rfl) ⟨415457, by rfl⟩ : syracuseStep 553943 = 830915) B830915
theorem B750551 : Blo 366759 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B619481 : Blo 366759 619481 := bstep (se 2 (by rfl) ⟨232305, by rfl⟩ : syracuseStep 619481 = 464611) B464611
theorem B1176599 : Blo 366759 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B554009 : Blo 366759 554009 := bstep (se 2 (by rfl) ⟨207753, by rfl⟩ : syracuseStep 554009 = 415507) B415507
theorem B783425 : Blo 366759 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B619609 : Blo 366759 619609 := bstep (se 2 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 619609 = 464707) B464707
theorem B554123 : Blo 366759 554123 := bstep (se 1 (by rfl) ⟨415592, by rfl⟩ : syracuseStep 554123 = 831185) B831185
theorem B1176727 : Blo 366759 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B554135 : Blo 366759 554135 := bstep (se 1 (by rfl) ⟨415601, by rfl⟩ : syracuseStep 554135 = 831203) B831203
theorem B554201 : Blo 366759 554201 := bstep (se 2 (by rfl) ⟨207825, by rfl⟩ : syracuseStep 554201 = 415651) B415651
theorem B554315 : Blo 366759 554315 := bstep (se 1 (by rfl) ⟨415736, by rfl⟩ : syracuseStep 554315 = 831473) B831473
theorem B554327 : Blo 366759 554327 := bstep (se 1 (by rfl) ⟨415745, by rfl⟩ : syracuseStep 554327 = 831491) B831491
theorem B1176983 : Blo 366759 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B554393 : Blo 366759 554393 := bstep (se 2 (by rfl) ⟨207897, by rfl⟩ : syracuseStep 554393 = 415795) B415795
theorem B947659 : Blo 366759 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B554507 : Blo 366759 554507 := bstep (se 1 (by rfl) ⟨415880, by rfl⟩ : syracuseStep 554507 = 831761) B831761
theorem B1242647 : Blo 366759 1242647 := bstep (se 1 (by rfl) ⟨931985, by rfl⟩ : syracuseStep 1242647 = 1863971) B1863971
theorem B554519 : Blo 366759 554519 := bstep (se 1 (by rfl) ⟨415889, by rfl⟩ : syracuseStep 554519 = 831779) B831779
theorem B1046105 : Blo 366759 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B554585 : Blo 366759 554585 := bstep (se 2 (by rfl) ⟨207969, by rfl⟩ : syracuseStep 554585 = 415939) B415939
theorem B9434717 : Blo 366759 9434717 := bstep (se 3 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 9434717 = 3538019) B3538019
theorem B620183 : Blo 366759 620183 := bstep (se 1 (by rfl) ⟨465137, by rfl⟩ : syracuseStep 620183 = 930275) B930275
theorem B554699 : Blo 366759 554699 := bstep (se 1 (by rfl) ⟨416024, by rfl⟩ : syracuseStep 554699 = 832049) B832049
theorem B554711 : Blo 366759 554711 := bstep (se 1 (by rfl) ⟨416033, by rfl⟩ : syracuseStep 554711 = 832067) B832067
theorem B620311 : Blo 366759 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B554777 : Blo 366759 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B554891 : Blo 366759 554891 := bstep (se 1 (by rfl) ⟨416168, by rfl⟩ : syracuseStep 554891 = 832337) B832337
theorem B784279 : Blo 366759 784279 := bstep (se 1 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 784279 = 1176419) B1176419
theorem B1570711 : Blo 366759 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B554903 : Blo 366759 554903 := bstep (se 1 (by rfl) ⟨416177, by rfl⟩ : syracuseStep 554903 = 832355) B832355
theorem B554969 : Blo 366759 554969 := bstep (se 2 (by rfl) ⟨208113, by rfl⟩ : syracuseStep 554969 = 416227) B416227
theorem B1243187 : Blo 366759 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B555083 : Blo 366759 555083 := bstep (se 1 (by rfl) ⟨416312, by rfl⟩ : syracuseStep 555083 = 832625) B832625
theorem B555095 : Blo 366759 555095 := bstep (se 1 (by rfl) ⟨416321, by rfl⟩ : syracuseStep 555095 = 832643) B832643
theorem B6715543 : Blo 366759 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B555161 : Blo 366759 555161 := bstep (se 2 (by rfl) ⟨208185, by rfl⟩ : syracuseStep 555161 = 416371) B416371
theorem B2652421 : Blo 366759 2652421 := bstep (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) B497329
theorem B555275 : Blo 366759 555275 := bstep (se 1 (by rfl) ⟨416456, by rfl⟩ : syracuseStep 555275 = 832913) B832913
theorem B555287 : Blo 366759 555287 := bstep (se 1 (by rfl) ⟨416465, by rfl⟩ : syracuseStep 555287 = 832931) B832931
theorem B1243457 : Blo 366759 1243457 := bstep (se 2 (by rfl) ⟨466296, by rfl⟩ : syracuseStep 1243457 = 932593) B932593
theorem B588107 : Blo 366759 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B555353 : Blo 366759 555353 := bstep (se 2 (by rfl) ⟨208257, by rfl⟩ : syracuseStep 555353 = 416515) B416515
theorem B1866077 : Blo 366759 1866077 := bstep (se 3 (by rfl) ⟨349889, by rfl⟩ : syracuseStep 1866077 = 699779) B699779
theorem B620939 : Blo 366759 620939 := bstep (se 1 (by rfl) ⟨465704, by rfl⟩ : syracuseStep 620939 = 931409) B931409
theorem B1046935 : Blo 366759 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1178059 : Blo 366759 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B555467 : Blo 366759 555467 := bstep (se 1 (by rfl) ⟨416600, by rfl⟩ : syracuseStep 555467 = 833201) B833201
theorem B555479 : Blo 366759 555479 := bstep (se 1 (by rfl) ⟨416609, by rfl⟩ : syracuseStep 555479 = 833219) B833219
theorem B621067 : Blo 366759 621067 := bstep (se 1 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 621067 = 931601) B931601
theorem B1571345 : Blo 366759 1571345 := bstep (se 2 (by rfl) ⟨589254, by rfl⟩ : syracuseStep 1571345 = 1178509) B1178509
theorem B555545 : Blo 366759 555545 := bstep (se 2 (by rfl) ⟨208329, by rfl⟩ : syracuseStep 555545 = 416659) B416659
theorem B1407563 : Blo 366759 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B1178201 : Blo 366759 1178201 := bstep (se 2 (by rfl) ⟨441825, by rfl⟩ : syracuseStep 1178201 = 883651) B883651
theorem B1407577 : Blo 366759 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B1997405 : Blo 366759 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B555659 : Blo 366759 555659 := bstep (se 1 (by rfl) ⟨416744, by rfl⟩ : syracuseStep 555659 = 833489) B833489
theorem B555671 : Blo 366759 555671 := bstep (se 1 (by rfl) ⟨416753, by rfl⟩ : syracuseStep 555671 = 833507) B833507
theorem B621209 : Blo 366759 621209 := bstep (se 2 (by rfl) ⟨232953, by rfl⟩ : syracuseStep 621209 = 465907) B465907
theorem B391883 : Blo 366759 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B785099 : Blo 366759 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B1178315 : Blo 366759 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B555737 : Blo 366759 555737 := bstep (se 2 (by rfl) ⟨208401, by rfl⟩ : syracuseStep 555737 = 416803) B416803
theorem B621337 : Blo 366759 621337 := bstep (se 2 (by rfl) ⟨233001, by rfl⟩ : syracuseStep 621337 = 466003) B466003
theorem B555851 : Blo 366759 555851 := bstep (se 1 (by rfl) ⟨416888, by rfl⟩ : syracuseStep 555851 = 833777) B833777
theorem B555863 : Blo 366759 555863 := bstep (se 1 (by rfl) ⟨416897, by rfl⟩ : syracuseStep 555863 = 833795) B833795
theorem B1243997 : Blo 366759 1243997 := bstep (se 3 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 1243997 = 466499) B466499
theorem B555929 : Blo 366759 555929 := bstep (se 2 (by rfl) ⟨208473, by rfl⟩ : syracuseStep 555929 = 416947) B416947
theorem B556043 : Blo 366759 556043 := bstep (se 1 (by rfl) ⟨417032, by rfl⟩ : syracuseStep 556043 = 834065) B834065
theorem B556055 : Blo 366759 556055 := bstep (se 1 (by rfl) ⟨417041, by rfl⟩ : syracuseStep 556055 = 834083) B834083
theorem B1178675 : Blo 366759 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B556121 : Blo 366759 556121 := bstep (se 2 (by rfl) ⟨208545, by rfl⟩ : syracuseStep 556121 = 417091) B417091
theorem B523417 : Blo 366759 523417 := bstep (se 2 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 523417 = 392563) B392563
theorem B588953 : Blo 366759 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B1047755 : Blo 366759 1047755 := bstep (se 1 (by rfl) ⟨785816, by rfl⟩ : syracuseStep 1047755 = 1571633) B1571633
theorem B1572043 : Blo 366759 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B621911 : Blo 366759 621911 := bstep (se 1 (by rfl) ⟨466433, by rfl⟩ : syracuseStep 621911 = 932867) B932867
theorem B622039 : Blo 366759 622039 := bstep (se 1 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 622039 = 933059) B933059
theorem B1572317 : Blo 366759 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B2883077 : Blo 366759 2883077 := bstep (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) B540577
theorem B589465 : Blo 366759 589465 := bstep (se 2 (by rfl) ⟨221049, by rfl⟩ : syracuseStep 589465 = 442099) B442099
theorem B1179443 : Blo 366759 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B1572659 : Blo 366759 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B1245131 : Blo 366759 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B1573121 : Blo 366759 1573121 := bstep (se 2 (by rfl) ⟨589920, by rfl⟩ : syracuseStep 1573121 = 1179841) B1179841
theorem B1245455 : Blo 366759 1245455 := bstep (se 1 (by rfl) ⟨934091, by rfl⟩ : syracuseStep 1245455 = 1868183) B1868183
theorem B1769779 : Blo 366759 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B1507643 : Blo 366759 1507643 := bstep (se 1 (by rfl) ⟨1130732, by rfl⟩ : syracuseStep 1507643 = 2261465) B2261465
theorem B1573273 : Blo 366759 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B623119 : Blo 366759 623119 := bstep (se 1 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 623119 = 934679) B934679
theorem B1245725 : Blo 366759 1245725 := bstep (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) B467147
theorem B6324803 : Blo 366759 6324803 := bstep (se 1 (by rfl) ⟨4743602, by rfl⟩ : syracuseStep 6324803 = 9487205) B9487205
theorem B524971 : Blo 366759 524971 := bstep (se 1 (by rfl) ⟨393728, by rfl⟩ : syracuseStep 524971 = 787457) B787457
theorem B885505 : Blo 366759 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B2097971 : Blo 366759 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B525199 : Blo 366759 525199 := bstep (se 1 (by rfl) ⟨393899, by rfl⟩ : syracuseStep 525199 = 787799) B787799
theorem B623659 : Blo 366759 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B623801 : Blo 366759 623801 := bstep (se 2 (by rfl) ⟨233925, by rfl⟩ : syracuseStep 623801 = 467851) B467851
theorem B1868993 : Blo 366759 1868993 := bstep (se 2 (by rfl) ⟨700872, by rfl⟩ : syracuseStep 1868993 = 1401745) B1401745
theorem B525575 : Blo 366759 525575 := bstep (se 1 (by rfl) ⟨394181, by rfl⟩ : syracuseStep 525575 = 788363) B788363
theorem B1213849 : Blo 366759 1213849 := bstep (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) B910387
theorem B1181213 : Blo 366759 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B624503 : Blo 366759 624503 := bstep (se 1 (by rfl) ⟨468377, by rfl⟩ : syracuseStep 624503 = 936755) B936755
theorem B558991 : Blo 366759 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B1247129 : Blo 366759 1247129 := bstep (se 2 (by rfl) ⟨467673, by rfl⟩ : syracuseStep 1247129 = 935347) B935347
theorem B1771607 : Blo 366759 1771607 := bstep (se 1 (by rfl) ⟨1328705, by rfl⟩ : syracuseStep 1771607 = 2657411) B2657411
theorem B395399 : Blo 366759 395399 := bstep (se 1 (by rfl) ⟨296549, by rfl⟩ : syracuseStep 395399 = 593099) B593099
theorem B8554697 : Blo 366759 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B2099429 : Blo 366759 2099429 := bstep (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) B393643
theorem B624955 : Blo 366759 624955 := bstep (se 1 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 624955 = 937433) B937433
theorem B592247 : Blo 366759 592247 := bstep (se 1 (by rfl) ⟨444185, by rfl⟩ : syracuseStep 592247 = 888371) B888371
theorem B625097 : Blo 366759 625097 := bstep (se 2 (by rfl) ⟨234411, by rfl⟩ : syracuseStep 625097 = 468823) B468823
theorem B1870289 : Blo 366759 1870289 := bstep (se 2 (by rfl) ⟨701358, by rfl⟩ : syracuseStep 1870289 = 1402717) B1402717
theorem B1247831 : Blo 366759 1247831 := bstep (se 1 (by rfl) ⟨935873, by rfl⟩ : syracuseStep 1247831 = 1871747) B1871747
theorem B527033 : Blo 366759 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B2394917 : Blo 366759 2394917 := bstep (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) B449047
theorem B2100113 : Blo 366759 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1051663 : Blo 366759 1051663 := bstep (se 1 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 1051663 = 1577495) B1577495
theorem B1248317 : Blo 366759 1248317 := bstep (se 3 (by rfl) ⟨234059, by rfl⟩ : syracuseStep 1248317 = 468119) B468119
theorem B1051937 : Blo 366759 1051937 := bstep (se 2 (by rfl) ⟨394476, by rfl⟩ : syracuseStep 1051937 = 788953) B788953
theorem B2788667 : Blo 366759 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B2985437 : Blo 366759 2985437 := bstep (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) B1119539
theorem B527887 : Blo 366759 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B2101139 : Blo 366759 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B1183673 : Blo 366759 1183673 := bstep (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) B887755
theorem B888985 : Blo 366759 888985 := bstep (se 2 (by rfl) ⟨333369, by rfl⟩ : syracuseStep 888985 = 666739) B666739
theorem B2691245 : Blo 366759 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B2003201 : Blo 366759 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B1052939 : Blo 366759 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1249721 : Blo 366759 1249721 := bstep (se 2 (by rfl) ⟨468645, by rfl⟩ : syracuseStep 1249721 = 937291) B937291
theorem B1872395 : Blo 366759 1872395 := bstep (se 1 (by rfl) ⟨1404296, by rfl⟩ : syracuseStep 1872395 = 2808593) B2808593
theorem B1053337 : Blo 366759 1053337 := bstep (se 2 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 1053337 = 790003) B790003
theorem B1872557 : Blo 366759 1872557 := bstep (se 3 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 1872557 = 702209) B702209
theorem B8622773 : Blo 366759 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B4789007 : Blo 366759 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B6329177 : Blo 366759 6329177 := bstep (se 2 (by rfl) ⟨2373441, by rfl⟩ : syracuseStep 6329177 = 4746883) B4746883
theorem B1053587 : Blo 366759 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B1250315 : Blo 366759 1250315 := bstep (se 1 (by rfl) ⟨937736, by rfl⟩ : syracuseStep 1250315 = 1875473) B1875473
theorem B1250423 : Blo 366759 1250423 := bstep (se 1 (by rfl) ⟨937817, by rfl⟩ : syracuseStep 1250423 = 1875635) B1875635
theorem B791687 : Blo 366759 791687 := bstep (se 1 (by rfl) ⟨593765, by rfl⟩ : syracuseStep 791687 = 1187531) B1187531
theorem B890003 : Blo 366759 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B2004371 : Blo 366759 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B4462199 : Blo 366759 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B464555 : Blo 366759 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B1775297 : Blo 366759 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B1251017 : Blo 366759 1251017 := bstep (se 2 (by rfl) ⟨469131, by rfl⟩ : syracuseStep 1251017 = 938263) B938263
theorem B14718773 : Blo 366759 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B1054579 : Blo 366759 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B497707 : Blo 366759 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B825479 : Blo 366759 825479 := bstep (se 1 (by rfl) ⟨619109, by rfl⟩ : syracuseStep 825479 = 1238219) B1238219
theorem B465031 : Blo 366759 465031 := bstep (se 1 (by rfl) ⟨348773, by rfl⟩ : syracuseStep 465031 = 697547) B697547
theorem B366779 : Blo 366759 366779 := bstep (se 1 (by rfl) ⟨275084, by rfl⟩ : syracuseStep 366779 = 550169) B550169
theorem B3184841 : Blo 366759 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B1874177 : Blo 366759 1874177 := bstep (se 2 (by rfl) ⟨702816, by rfl⟩ : syracuseStep 1874177 = 1405633) B1405633
theorem B366855 : Blo 366759 366855 := bstep (se 1 (by rfl) ⟨275141, by rfl⟩ : syracuseStep 366855 = 550283) B550283
theorem B366863 : Blo 366759 366863 := bstep (se 1 (by rfl) ⟨275147, by rfl⟩ : syracuseStep 366863 = 550295) B550295
theorem B629035 : Blo 366759 629035 := bstep (se 1 (by rfl) ⟨471776, by rfl⟩ : syracuseStep 629035 = 943553) B943553
theorem B366907 : Blo 366759 366907 := bstep (se 1 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 366907 = 550361) B550361
theorem B825659 : Blo 366759 825659 := bstep (se 1 (by rfl) ⟨619244, by rfl⟩ : syracuseStep 825659 = 1238489) B1238489
theorem B366983 : Blo 366759 366983 := bstep (se 1 (by rfl) ⟨275237, by rfl⟩ : syracuseStep 366983 = 550475) B550475
theorem B366991 : Blo 366759 366991 := bstep (se 1 (by rfl) ⟨275243, by rfl⟩ : syracuseStep 366991 = 550487) B550487
theorem B4299155 : Blo 366759 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B825785 : Blo 366759 825785 := bstep (se 2 (by rfl) ⟨309669, by rfl⟩ : syracuseStep 825785 = 619339) B619339
theorem B367035 : Blo 366759 367035 := bstep (se 1 (by rfl) ⟨275276, by rfl⟩ : syracuseStep 367035 = 550553) B550553
theorem B367111 : Blo 366759 367111 := bstep (se 1 (by rfl) ⟨275333, by rfl⟩ : syracuseStep 367111 = 550667) B550667
theorem B367119 : Blo 366759 367119 := bstep (se 1 (by rfl) ⟨275339, by rfl⟩ : syracuseStep 367119 = 550679) B550679
theorem B367163 : Blo 366759 367163 := bstep (se 1 (by rfl) ⟨275372, by rfl⟩ : syracuseStep 367163 = 550745) B550745
theorem B465527 : Blo 366759 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B367239 : Blo 366759 367239 := bstep (se 1 (by rfl) ⟨275429, by rfl⟩ : syracuseStep 367239 = 550859) B550859
theorem B367247 : Blo 366759 367247 := bstep (se 1 (by rfl) ⟨275435, by rfl⟩ : syracuseStep 367247 = 550871) B550871
theorem B367291 : Blo 366759 367291 := bstep (se 1 (by rfl) ⟨275468, by rfl⟩ : syracuseStep 367291 = 550937) B550937
theorem B367367 : Blo 366759 367367 := bstep (se 1 (by rfl) ⟨275525, by rfl⟩ : syracuseStep 367367 = 551051) B551051
theorem B826127 : Blo 366759 826127 := bstep (se 1 (by rfl) ⟨619595, by rfl⟩ : syracuseStep 826127 = 1239191) B1239191
theorem B367375 : Blo 366759 367375 := bstep (se 1 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 367375 = 551063) B551063
theorem B465679 : Blo 366759 465679 := bstep (se 1 (by rfl) ⟨349259, by rfl⟩ : syracuseStep 465679 = 698519) B698519
theorem B826145 : Blo 366759 826145 := bstep (se 2 (by rfl) ⟨309804, by rfl⟩ : syracuseStep 826145 = 619609) B619609
theorem B367419 : Blo 366759 367419 := bstep (se 1 (by rfl) ⟨275564, by rfl⟩ : syracuseStep 367419 = 551129) B551129
theorem B367495 : Blo 366759 367495 := bstep (se 1 (by rfl) ⟨275621, by rfl⟩ : syracuseStep 367495 = 551243) B551243
theorem B367503 : Blo 366759 367503 := bstep (se 1 (by rfl) ⟨275627, by rfl⟩ : syracuseStep 367503 = 551255) B551255
theorem B367547 : Blo 366759 367547 := bstep (se 1 (by rfl) ⟨275660, by rfl⟩ : syracuseStep 367547 = 551321) B551321
theorem B465851 : Blo 366759 465851 := bstep (se 1 (by rfl) ⟨349388, by rfl⟩ : syracuseStep 465851 = 698777) B698777
theorem B367623 : Blo 366759 367623 := bstep (se 1 (by rfl) ⟨275717, by rfl⟩ : syracuseStep 367623 = 551435) B551435
theorem B1121291 : Blo 366759 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B367631 : Blo 366759 367631 := bstep (se 1 (by rfl) ⟨275723, by rfl⟩ : syracuseStep 367631 = 551447) B551447
theorem B1874987 : Blo 366759 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B367675 : Blo 366759 367675 := bstep (se 1 (by rfl) ⟨275756, by rfl⟩ : syracuseStep 367675 = 551513) B551513
theorem B1580093 : Blo 366759 1580093 := bstep (se 3 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 1580093 = 592535) B592535
theorem B826487 : Blo 366759 826487 := bstep (se 1 (by rfl) ⟨619865, by rfl⟩ : syracuseStep 826487 = 1239731) B1239731
theorem B367751 : Blo 366759 367751 := bstep (se 1 (by rfl) ⟨275813, by rfl⟩ : syracuseStep 367751 = 551627) B551627
theorem B367759 : Blo 366759 367759 := bstep (se 1 (by rfl) ⟨275819, by rfl⟩ : syracuseStep 367759 = 551639) B551639
theorem B367803 : Blo 366759 367803 := bstep (se 1 (by rfl) ⟨275852, by rfl⟩ : syracuseStep 367803 = 551705) B551705
theorem B367879 : Blo 366759 367879 := bstep (se 1 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 367879 = 551819) B551819
theorem B367887 : Blo 366759 367887 := bstep (se 1 (by rfl) ⟨275915, by rfl⟩ : syracuseStep 367887 = 551831) B551831
theorem B826667 : Blo 366759 826667 := bstep (se 1 (by rfl) ⟨620000, by rfl⟩ : syracuseStep 826667 = 1240001) B1240001
theorem B367931 : Blo 366759 367931 := bstep (se 1 (by rfl) ⟨275948, by rfl⟩ : syracuseStep 367931 = 551897) B551897
theorem B2366779 : Blo 366759 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B1187131 : Blo 366759 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B368007 : Blo 366759 368007 := bstep (se 1 (by rfl) ⟨276005, by rfl⟩ : syracuseStep 368007 = 552011) B552011
theorem B368015 : Blo 366759 368015 := bstep (se 1 (by rfl) ⟨276011, by rfl⟩ : syracuseStep 368015 = 552023) B552023
theorem B662969 : Blo 366759 662969 := bstep (se 2 (by rfl) ⟨248613, by rfl⟩ : syracuseStep 662969 = 497227) B497227
theorem B368059 : Blo 366759 368059 := bstep (se 1 (by rfl) ⟨276044, by rfl⟩ : syracuseStep 368059 = 552089) B552089
theorem B368135 : Blo 366759 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B368143 : Blo 366759 368143 := bstep (se 1 (by rfl) ⟨276107, by rfl⟩ : syracuseStep 368143 = 552215) B552215
theorem B368187 : Blo 366759 368187 := bstep (se 1 (by rfl) ⟨276140, by rfl⟩ : syracuseStep 368187 = 552281) B552281
theorem B368263 : Blo 366759 368263 := bstep (se 1 (by rfl) ⟨276197, by rfl⟩ : syracuseStep 368263 = 552395) B552395
theorem B368271 : Blo 366759 368271 := bstep (se 1 (by rfl) ⟨276203, by rfl⟩ : syracuseStep 368271 = 552407) B552407
theorem B827027 : Blo 366759 827027 := bstep (se 1 (by rfl) ⟨620270, by rfl⟩ : syracuseStep 827027 = 1240541) B1240541
theorem B368315 : Blo 366759 368315 := bstep (se 1 (by rfl) ⟨276236, by rfl⟩ : syracuseStep 368315 = 552473) B552473
theorem B827081 : Blo 366759 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B7577317 : Blo 366759 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B368391 : Blo 366759 368391 := bstep (se 1 (by rfl) ⟨276293, by rfl⟩ : syracuseStep 368391 = 552587) B552587
theorem B368399 : Blo 366759 368399 := bstep (se 1 (by rfl) ⟨276299, by rfl⟩ : syracuseStep 368399 = 552599) B552599
theorem B368443 : Blo 366759 368443 := bstep (se 1 (by rfl) ⟨276332, by rfl⟩ : syracuseStep 368443 = 552665) B552665
theorem B368519 : Blo 366759 368519 := bstep (se 1 (by rfl) ⟨276389, by rfl⟩ : syracuseStep 368519 = 552779) B552779
theorem B466823 : Blo 366759 466823 := bstep (se 1 (by rfl) ⟨350117, by rfl⟩ : syracuseStep 466823 = 700235) B700235
theorem B368527 : Blo 366759 368527 := bstep (se 1 (by rfl) ⟨276395, by rfl⟩ : syracuseStep 368527 = 552791) B552791
theorem B368571 : Blo 366759 368571 := bstep (se 1 (by rfl) ⟨276428, by rfl⟩ : syracuseStep 368571 = 552857) B552857
theorem B368647 : Blo 366759 368647 := bstep (se 1 (by rfl) ⟨276485, by rfl⟩ : syracuseStep 368647 = 552971) B552971
theorem B368655 : Blo 366759 368655 := bstep (se 1 (by rfl) ⟨276491, by rfl⟩ : syracuseStep 368655 = 552983) B552983
theorem B368699 : Blo 366759 368699 := bstep (se 1 (by rfl) ⟨276524, by rfl⟩ : syracuseStep 368699 = 553049) B553049
theorem B368775 : Blo 366759 368775 := bstep (se 1 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 368775 = 553163) B553163
theorem B368783 : Blo 366759 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B368827 : Blo 366759 368827 := bstep (se 1 (by rfl) ⟨276620, by rfl⟩ : syracuseStep 368827 = 553241) B553241
theorem B8954057 : Blo 366759 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B368903 : Blo 366759 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B368911 : Blo 366759 368911 := bstep (se 1 (by rfl) ⟨276683, by rfl⟩ : syracuseStep 368911 = 553367) B553367
theorem B368955 : Blo 366759 368955 := bstep (se 1 (by rfl) ⟨276716, by rfl⟩ : syracuseStep 368955 = 553433) B553433
theorem B1876283 : Blo 366759 1876283 := bstep (se 1 (by rfl) ⟨1407212, by rfl⟩ : syracuseStep 1876283 = 2814425) B2814425
theorem B827783 : Blo 366759 827783 := bstep (se 1 (by rfl) ⟨620837, by rfl⟩ : syracuseStep 827783 = 1241675) B1241675
theorem B369031 : Blo 366759 369031 := bstep (se 1 (by rfl) ⟨276773, by rfl⟩ : syracuseStep 369031 = 553547) B553547
theorem B369039 : Blo 366759 369039 := bstep (se 1 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 369039 = 553559) B553559
theorem B369083 : Blo 366759 369083 := bstep (se 1 (by rfl) ⟨276812, by rfl⟩ : syracuseStep 369083 = 553625) B553625
theorem B1876445 : Blo 366759 1876445 := bstep (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) B703667
theorem B369159 : Blo 366759 369159 := bstep (se 1 (by rfl) ⟨276869, by rfl⟩ : syracuseStep 369159 = 553739) B553739
theorem B369167 : Blo 366759 369167 := bstep (se 1 (by rfl) ⟨276875, by rfl⟩ : syracuseStep 369167 = 553751) B553751
theorem B467471 : Blo 366759 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B2794013 : Blo 366759 2794013 := bstep (se 3 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 2794013 = 1047755) B1047755
theorem B827963 : Blo 366759 827963 := bstep (se 1 (by rfl) ⟨620972, by rfl⟩ : syracuseStep 827963 = 1241945) B1241945
theorem B369211 : Blo 366759 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B1778237 : Blo 366759 1778237 := bstep (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) B666839
theorem B369287 : Blo 366759 369287 := bstep (se 1 (by rfl) ⟨276965, by rfl⟩ : syracuseStep 369287 = 553931) B553931
theorem B369295 : Blo 366759 369295 := bstep (se 1 (by rfl) ⟨276971, by rfl⟩ : syracuseStep 369295 = 553943) B553943
theorem B828089 : Blo 366759 828089 := bstep (se 2 (by rfl) ⟨310533, by rfl⟩ : syracuseStep 828089 = 621067) B621067
theorem B369339 : Blo 366759 369339 := bstep (se 1 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 369339 = 554009) B554009
theorem B369415 : Blo 366759 369415 := bstep (se 1 (by rfl) ⟨277061, by rfl⟩ : syracuseStep 369415 = 554123) B554123
theorem B369423 : Blo 366759 369423 := bstep (se 1 (by rfl) ⟨277067, by rfl⟩ : syracuseStep 369423 = 554135) B554135
theorem B992033 : Blo 366759 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B1876769 : Blo 366759 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B369467 : Blo 366759 369467 := bstep (se 1 (by rfl) ⟨277100, by rfl⟩ : syracuseStep 369467 = 554201) B554201
theorem B369543 : Blo 366759 369543 := bstep (se 1 (by rfl) ⟨277157, by rfl⟩ : syracuseStep 369543 = 554315) B554315
theorem B369551 : Blo 366759 369551 := bstep (se 1 (by rfl) ⟨277163, by rfl⟩ : syracuseStep 369551 = 554327) B554327
theorem B369595 : Blo 366759 369595 := bstep (se 1 (by rfl) ⟨277196, by rfl⟩ : syracuseStep 369595 = 554393) B554393
theorem B369671 : Blo 366759 369671 := bstep (se 1 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 369671 = 554507) B554507
theorem B1778699 : Blo 366759 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582091 : Blo 366759 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B828431 : Blo 366759 828431 := bstep (se 1 (by rfl) ⟨621323, by rfl⟩ : syracuseStep 828431 = 1242647) B1242647
theorem B369679 : Blo 366759 369679 := bstep (se 1 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 369679 = 554519) B554519
theorem B828449 : Blo 366759 828449 := bstep (se 2 (by rfl) ⟨310668, by rfl⟩ : syracuseStep 828449 = 621337) B621337
theorem B697403 : Blo 366759 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B369723 : Blo 366759 369723 := bstep (se 1 (by rfl) ⟨277292, by rfl⟩ : syracuseStep 369723 = 554585) B554585
theorem B369799 : Blo 366759 369799 := bstep (se 1 (by rfl) ⟨277349, by rfl⟩ : syracuseStep 369799 = 554699) B554699
theorem B369807 : Blo 366759 369807 := bstep (se 1 (by rfl) ⟨277355, by rfl⟩ : syracuseStep 369807 = 554711) B554711
theorem B369851 : Blo 366759 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B369927 : Blo 366759 369927 := bstep (se 1 (by rfl) ⟨277445, by rfl⟩ : syracuseStep 369927 = 554891) B554891
theorem B369935 : Blo 366759 369935 := bstep (se 1 (by rfl) ⟨277451, by rfl⟩ : syracuseStep 369935 = 554903) B554903
theorem B369979 : Blo 366759 369979 := bstep (se 1 (by rfl) ⟨277484, by rfl⟩ : syracuseStep 369979 = 554969) B554969
theorem B828791 : Blo 366759 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B664951 : Blo 366759 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B370055 : Blo 366759 370055 := bstep (se 1 (by rfl) ⟨277541, by rfl⟩ : syracuseStep 370055 = 555083) B555083
theorem B370063 : Blo 366759 370063 := bstep (se 1 (by rfl) ⟨277547, by rfl⟩ : syracuseStep 370063 = 555095) B555095
theorem B370107 : Blo 366759 370107 := bstep (se 1 (by rfl) ⟨277580, by rfl⟩ : syracuseStep 370107 = 555161) B555161
theorem B6006221 : Blo 366759 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B370183 : Blo 366759 370183 := bstep (se 1 (by rfl) ⟨277637, by rfl⟩ : syracuseStep 370183 = 555275) B555275
theorem B370191 : Blo 366759 370191 := bstep (se 1 (by rfl) ⟨277643, by rfl⟩ : syracuseStep 370191 = 555287) B555287
theorem B697889 : Blo 366759 697889 := bstep (se 2 (by rfl) ⟨261708, by rfl⟩ : syracuseStep 697889 = 523417) B523417
theorem B828971 : Blo 366759 828971 := bstep (se 1 (by rfl) ⟨621728, by rfl⟩ : syracuseStep 828971 = 1243457) B1243457
theorem B370235 : Blo 366759 370235 := bstep (se 1 (by rfl) ⟨277676, by rfl⟩ : syracuseStep 370235 = 555353) B555353
theorem B370311 : Blo 366759 370311 := bstep (se 1 (by rfl) ⟨277733, by rfl⟩ : syracuseStep 370311 = 555467) B555467
theorem B370319 : Blo 366759 370319 := bstep (se 1 (by rfl) ⟨277739, by rfl⟩ : syracuseStep 370319 = 555479) B555479
theorem B370363 : Blo 366759 370363 := bstep (se 1 (by rfl) ⟨277772, by rfl⟩ : syracuseStep 370363 = 555545) B555545
theorem B370439 : Blo 366759 370439 := bstep (se 1 (by rfl) ⟨277829, by rfl⟩ : syracuseStep 370439 = 555659) B555659
theorem B370447 : Blo 366759 370447 := bstep (se 1 (by rfl) ⟨277835, by rfl⟩ : syracuseStep 370447 = 555671) B555671
theorem B370491 : Blo 366759 370491 := bstep (se 1 (by rfl) ⟨277868, by rfl⟩ : syracuseStep 370491 = 555737) B555737
theorem B370567 : Blo 366759 370567 := bstep (se 1 (by rfl) ⟨277925, by rfl⟩ : syracuseStep 370567 = 555851) B555851
theorem B370575 : Blo 366759 370575 := bstep (se 1 (by rfl) ⟨277931, by rfl⟩ : syracuseStep 370575 = 555863) B555863
theorem B829331 : Blo 366759 829331 := bstep (se 1 (by rfl) ⟨621998, by rfl⟩ : syracuseStep 829331 = 1243997) B1243997
theorem B3549091 : Blo 366759 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B534443 : Blo 366759 534443 := bstep (se 1 (by rfl) ⟨400832, by rfl⟩ : syracuseStep 534443 = 801665) B801665
theorem B370619 : Blo 366759 370619 := bstep (se 1 (by rfl) ⟨277964, by rfl⟩ : syracuseStep 370619 = 555929) B555929
theorem B829385 : Blo 366759 829385 := bstep (se 2 (by rfl) ⟨311019, by rfl⟩ : syracuseStep 829385 = 622039) B622039
theorem B370695 : Blo 366759 370695 := bstep (se 1 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 370695 = 556043) B556043
theorem B2107403 : Blo 366759 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B370703 : Blo 366759 370703 := bstep (se 1 (by rfl) ⟨278027, by rfl⟩ : syracuseStep 370703 = 556055) B556055
theorem B370747 : Blo 366759 370747 := bstep (se 1 (by rfl) ⟨278060, by rfl⟩ : syracuseStep 370747 = 556121) B556121
theorem B8005877 : Blo 366759 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B665975 : Blo 366759 665975 := bstep (se 1 (by rfl) ⟨499481, by rfl⟩ : syracuseStep 665975 = 998963) B998963
theorem B830087 : Blo 366759 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B928523 : Blo 366759 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B830267 : Blo 366759 830267 := bstep (se 1 (by rfl) ⟨622700, by rfl⟩ : syracuseStep 830267 = 1245401) B1245401
theorem B830393 : Blo 366759 830393 := bstep (se 2 (by rfl) ⟨311397, by rfl⟩ : syracuseStep 830393 = 622795) B622795
theorem B830735 : Blo 366759 830735 := bstep (se 1 (by rfl) ⟨623051, by rfl⟩ : syracuseStep 830735 = 1246103) B1246103
theorem B830753 : Blo 366759 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B929171 : Blo 366759 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B699833 : Blo 366759 699833 := bstep (se 2 (by rfl) ⟨262437, by rfl⟩ : syracuseStep 699833 = 524875) B524875
theorem B831095 : Blo 366759 831095 := bstep (se 1 (by rfl) ⟨623321, by rfl⟩ : syracuseStep 831095 = 1246643) B1246643
theorem B929465 : Blo 366759 929465 := bstep (se 2 (by rfl) ⟨348549, by rfl⟩ : syracuseStep 929465 = 697099) B697099
theorem B798409 : Blo 366759 798409 := bstep (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) B598807
theorem B831275 : Blo 366759 831275 := bstep (se 1 (by rfl) ⟨623456, by rfl⟩ : syracuseStep 831275 = 1246913) B1246913
theorem B3977333 : Blo 366759 3977333 := bstep (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) B372875
theorem B831635 : Blo 366759 831635 := bstep (se 1 (by rfl) ⟨623726, by rfl⟩ : syracuseStep 831635 = 1247453) B1247453
theorem B831689 : Blo 366759 831689 := bstep (se 2 (by rfl) ⟨311883, by rfl⟩ : syracuseStep 831689 = 623767) B623767
theorem B930163 : Blo 366759 930163 := bstep (se 1 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 930163 = 1395245) B1395245
theorem B1126775 : Blo 366759 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B373135 : Blo 366759 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B1814929 : Blo 366759 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B930305 : Blo 366759 930305 := bstep (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) B697729
theorem B700987 : Blo 366759 700987 := bstep (se 1 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 700987 = 1051481) B1051481
theorem B1126973 : Blo 366759 1126973 := bstep (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) B422615
theorem B8991425 : Blo 366759 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B2798387 : Blo 366759 2798387 := bstep (se 1 (by rfl) ⟨2098790, by rfl⟩ : syracuseStep 2798387 = 4197581) B4197581
theorem B832391 : Blo 366759 832391 := bstep (se 1 (by rfl) ⟨624293, by rfl⟩ : syracuseStep 832391 = 1248587) B1248587
theorem B930761 : Blo 366759 930761 := bstep (se 2 (by rfl) ⟨349035, by rfl⟩ : syracuseStep 930761 = 698071) B698071
theorem B701473 : Blo 366759 701473 := bstep (se 2 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 701473 = 526105) B526105
theorem B832571 : Blo 366759 832571 := bstep (se 1 (by rfl) ⟨624428, by rfl⟩ : syracuseStep 832571 = 1248857) B1248857
theorem B2110637 : Blo 366759 2110637 := bstep (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) B791489
theorem B832697 : Blo 366759 832697 := bstep (se 2 (by rfl) ⟨312261, by rfl⟩ : syracuseStep 832697 = 624523) B624523
theorem B931115 : Blo 366759 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B6272315 : Blo 366759 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B833039 : Blo 366759 833039 := bstep (se 1 (by rfl) ⟨624779, by rfl⟩ : syracuseStep 833039 = 1249559) B1249559
theorem B833057 : Blo 366759 833057 := bstep (se 2 (by rfl) ⟨312396, by rfl⟩ : syracuseStep 833057 = 624793) B624793
theorem B1947223 : Blo 366759 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B833399 : Blo 366759 833399 := bstep (se 1 (by rfl) ⟨625049, by rfl⟩ : syracuseStep 833399 = 1250099) B1250099
theorem B833579 : Blo 366759 833579 := bstep (se 1 (by rfl) ⟨625184, by rfl⟩ : syracuseStep 833579 = 1250369) B1250369
theorem B702665 : Blo 366759 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B932107 : Blo 366759 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B997751 : Blo 366759 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B833939 : Blo 366759 833939 := bstep (se 1 (by rfl) ⟨625454, by rfl⟩ : syracuseStep 833939 = 1250909) B1250909
theorem B932249 : Blo 366759 932249 := bstep (se 2 (by rfl) ⟨349593, by rfl⟩ : syracuseStep 932249 = 699187) B699187
theorem B833993 : Blo 366759 833993 := bstep (se 2 (by rfl) ⟨312747, by rfl⟩ : syracuseStep 833993 = 625495) B625495
theorem B932411 : Blo 366759 932411 := bstep (se 1 (by rfl) ⟨699308, by rfl⟩ : syracuseStep 932411 = 1398617) B1398617
theorem B768811 : Blo 366759 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B932755 : Blo 366759 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B703379 : Blo 366759 703379 := bstep (se 1 (by rfl) ⟨527534, by rfl⟩ : syracuseStep 703379 = 1055069) B1055069
theorem B703417 : Blo 366759 703417 := bstep (se 2 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 703417 = 527563) B527563
theorem B932897 : Blo 366759 932897 := bstep (se 2 (by rfl) ⟨349836, by rfl⟩ : syracuseStep 932897 = 699673) B699673
theorem B8535581 : Blo 366759 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B999179 : Blo 366759 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B933889 : Blo 366759 933889 := bstep (se 2 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 933889 = 700417) B700417
theorem B934487 : Blo 366759 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B1393271 : Blo 366759 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B934699 : Blo 366759 934699 := bstep (se 1 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 934699 = 1402049) B1402049
theorem B2245427 : Blo 366759 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B1000345 : Blo 366759 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B934841 : Blo 366759 934841 := bstep (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) B701131
theorem B1394243 : Blo 366759 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B3884645 : Blo 366759 3884645 := bstep (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) B728371
theorem B476987 : Blo 366759 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B2246545 : Blo 366759 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B935833 : Blo 366759 935833 := bstep (se 2 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 935833 = 701875) B701875
theorem B1263545 : Blo 366759 1263545 := bstep (se 2 (by rfl) ⟨473829, by rfl⟩ : syracuseStep 1263545 = 947659) B947659
theorem B935995 : Blo 366759 935995 := bstep (se 1 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 935995 = 1403993) B1403993
theorem B4180085 : Blo 366759 4180085 := bstep (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) B391883
theorem B936137 : Blo 366759 936137 := bstep (se 2 (by rfl) ⟨351051, by rfl⟩ : syracuseStep 936137 = 702103) B702103
theorem B1067411 : Blo 366759 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B3361283 : Blo 366759 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B3590659 : Blo 366759 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B936481 : Blo 366759 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B4213619 : Blo 366759 4213619 := bstep (se 1 (by rfl) ⟨3160214, by rfl⟩ : syracuseStep 4213619 = 6320429) B6320429
theorem B937079 : Blo 366759 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B412807 : Blo 366759 412807 := bstep (se 1 (by rfl) ⟨309605, by rfl⟩ : syracuseStep 412807 = 619211) B619211
theorem B1395913 : Blo 366759 1395913 := bstep (se 2 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 1395913 = 1046935) B1046935
theorem B412987 : Blo 366759 412987 := bstep (se 1 (by rfl) ⟨309740, by rfl⟩ : syracuseStep 412987 = 619481) B619481
theorem B6311681 : Blo 366759 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B3526415 : Blo 366759 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B413455 : Blo 366759 413455 := bstep (se 1 (by rfl) ⟨310091, by rfl⟩ : syracuseStep 413455 = 620183) B620183
theorem B511915 : Blo 366759 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B413959 : Blo 366759 413959 := bstep (se 1 (by rfl) ⟨310469, by rfl⟩ : syracuseStep 413959 = 620939) B620939
theorem B938375 : Blo 366759 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B1331603 : Blo 366759 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B2806163 : Blo 366759 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B938425 : Blo 366759 938425 := bstep (se 2 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 938425 = 703819) B703819
theorem B414139 : Blo 366759 414139 := bstep (se 1 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 414139 = 621209) B621209
theorem B4051727 : Blo 366759 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B414607 : Blo 366759 414607 := bstep (se 1 (by rfl) ⟨310955, by rfl⟩ : syracuseStep 414607 = 621911) B621911
theorem B1922051 : Blo 366759 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B1266749 : Blo 366759 1266749 := bstep (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) B475031
theorem B1496353 : Blo 366759 1496353 := bstep (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) B1122265
theorem B1398131 : Blo 366759 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B415111 : Blo 366759 415111 := bstep (se 1 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 415111 = 622667) B622667
theorem B2119121 : Blo 366759 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B415291 : Blo 366759 415291 := bstep (se 1 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 415291 = 622937) B622937
theorem B710345 : Blo 366759 710345 := bstep (se 2 (by rfl) ⟨266379, by rfl⟩ : syracuseStep 710345 = 532759) B532759
theorem B8509157 : Blo 366759 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B841487 : Blo 366759 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B415759 : Blo 366759 415759 := bstep (se 1 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 415759 = 623639) B623639
theorem B1136825 : Blo 366759 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B1857977 : Blo 366759 1857977 := bstep (se 2 (by rfl) ⟨696741, by rfl⟩ : syracuseStep 1857977 = 1393483) B1393483
theorem B416263 : Blo 366759 416263 := bstep (se 1 (by rfl) ⟨312197, by rfl⟩ : syracuseStep 416263 = 624395) B624395
theorem B2120203 : Blo 366759 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B416443 : Blo 366759 416443 := bstep (se 1 (by rfl) ⟨312332, by rfl⟩ : syracuseStep 416443 = 624665) B624665
theorem B2644751 : Blo 366759 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B3988541 : Blo 366759 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B416911 : Blo 366759 416911 := bstep (se 1 (by rfl) ⟨312683, by rfl⟩ : syracuseStep 416911 = 625367) B625367
theorem B1400273 : Blo 366759 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B1859273 : Blo 366759 1859273 := bstep (se 2 (by rfl) ⟨697227, by rfl⟩ : syracuseStep 1859273 = 1394455) B1394455
theorem B1400591 : Blo 366759 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B6316055 : Blo 366759 6316055 := bstep (se 1 (by rfl) ⟨4737041, by rfl⟩ : syracuseStep 6316055 = 9474083) B9474083
theorem B1499255 : Blo 366759 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B2089475 : Blo 366759 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B7955009 : Blo 366759 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B1237895 : Blo 366759 1237895 := bstep (se 1 (by rfl) ⟨928421, by rfl⟩ : syracuseStep 1237895 = 1856843) B1856843
theorem B5235619 : Blo 366759 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B4482053 : Blo 366759 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B1238273 : Blo 366759 1238273 := bstep (se 2 (by rfl) ⟨464352, by rfl⟩ : syracuseStep 1238273 = 928705) B928705
theorem B550151 : Blo 366759 550151 := bstep (se 1 (by rfl) ⟨412613, by rfl⟩ : syracuseStep 550151 = 825227) B825227
theorem B550187 : Blo 366759 550187 := bstep (se 1 (by rfl) ⟨412640, by rfl⟩ : syracuseStep 550187 = 825281) B825281
theorem B550217 : Blo 366759 550217 := bstep (se 2 (by rfl) ⟨206331, by rfl⟩ : syracuseStep 550217 = 412663) B412663
theorem B550331 : Blo 366759 550331 := bstep (se 1 (by rfl) ⟨412748, by rfl⟩ : syracuseStep 550331 = 825497) B825497
theorem B550391 : Blo 366759 550391 := bstep (se 1 (by rfl) ⟨412793, by rfl⟩ : syracuseStep 550391 = 825587) B825587
theorem B550415 : Blo 366759 550415 := bstep (se 1 (by rfl) ⟨412811, by rfl⟩ : syracuseStep 550415 = 825623) B825623
theorem B1762859 : Blo 366759 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B550457 : Blo 366759 550457 := bstep (se 2 (by rfl) ⟨206421, by rfl⟩ : syracuseStep 550457 = 412843) B412843
theorem B550535 : Blo 366759 550535 := bstep (se 1 (by rfl) ⟨412901, by rfl⟩ : syracuseStep 550535 = 825803) B825803
theorem B550571 : Blo 366759 550571 := bstep (se 1 (by rfl) ⟨412928, by rfl⟩ : syracuseStep 550571 = 825857) B825857
theorem B5072563 : Blo 366759 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B550601 : Blo 366759 550601 := bstep (se 2 (by rfl) ⟨206475, by rfl⟩ : syracuseStep 550601 = 412951) B412951
theorem B550715 : Blo 366759 550715 := bstep (se 1 (by rfl) ⟨413036, by rfl⟩ : syracuseStep 550715 = 826073) B826073
theorem B550775 : Blo 366759 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B550799 : Blo 366759 550799 := bstep (se 1 (by rfl) ⟨413099, by rfl⟩ : syracuseStep 550799 = 826199) B826199
theorem B1566611 : Blo 366759 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B550841 : Blo 366759 550841 := bstep (se 2 (by rfl) ⟨206565, by rfl⟩ : syracuseStep 550841 = 413131) B413131
theorem B550919 : Blo 366759 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B1239083 : Blo 366759 1239083 := bstep (se 1 (by rfl) ⟨929312, by rfl⟩ : syracuseStep 1239083 = 1858625) B1858625
theorem B550955 : Blo 366759 550955 := bstep (se 1 (by rfl) ⟨413216, by rfl⟩ : syracuseStep 550955 = 826433) B826433
theorem B550985 : Blo 366759 550985 := bstep (se 2 (by rfl) ⟨206619, by rfl⟩ : syracuseStep 550985 = 413239) B413239
theorem B551099 : Blo 366759 551099 := bstep (se 1 (by rfl) ⟨413324, by rfl⟩ : syracuseStep 551099 = 826649) B826649
theorem B551159 : Blo 366759 551159 := bstep (se 1 (by rfl) ⟨413369, by rfl⟩ : syracuseStep 551159 = 826739) B826739
theorem B551183 : Blo 366759 551183 := bstep (se 1 (by rfl) ⟨413387, by rfl⟩ : syracuseStep 551183 = 826775) B826775
theorem B551225 : Blo 366759 551225 := bstep (se 2 (by rfl) ⟨206709, by rfl⟩ : syracuseStep 551225 = 413419) B413419
theorem B551303 : Blo 366759 551303 := bstep (se 1 (by rfl) ⟨413477, by rfl⟩ : syracuseStep 551303 = 826955) B826955
theorem B3139985 : Blo 366759 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B4712849 : Blo 366759 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B551339 : Blo 366759 551339 := bstep (se 1 (by rfl) ⟨413504, by rfl⟩ : syracuseStep 551339 = 827009) B827009
theorem B551369 : Blo 366759 551369 := bstep (se 2 (by rfl) ⟨206763, by rfl⟩ : syracuseStep 551369 = 413527) B413527
theorem B6449629 : Blo 366759 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B551483 : Blo 366759 551483 := bstep (se 1 (by rfl) ⟨413612, by rfl⟩ : syracuseStep 551483 = 827225) B827225
theorem B551543 : Blo 366759 551543 := bstep (se 1 (by rfl) ⟨413657, by rfl⟩ : syracuseStep 551543 = 827315) B827315
theorem B551567 : Blo 366759 551567 := bstep (se 1 (by rfl) ⟨413675, by rfl⟩ : syracuseStep 551567 = 827351) B827351
theorem B1764013 : Blo 366759 1764013 := bstep (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) B661505
theorem B551609 : Blo 366759 551609 := bstep (se 2 (by rfl) ⟨206853, by rfl⟩ : syracuseStep 551609 = 413707) B413707
theorem B551687 : Blo 366759 551687 := bstep (se 1 (by rfl) ⟨413765, by rfl⟩ : syracuseStep 551687 = 827531) B827531
theorem B551723 : Blo 366759 551723 := bstep (se 1 (by rfl) ⟨413792, by rfl⟩ : syracuseStep 551723 = 827585) B827585
theorem B551753 : Blo 366759 551753 := bstep (se 2 (by rfl) ⟨206907, by rfl⟩ : syracuseStep 551753 = 413815) B413815
theorem B2091865 : Blo 366759 2091865 := bstep (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) B1568899
theorem B551867 : Blo 366759 551867 := bstep (se 1 (by rfl) ⟨413900, by rfl⟩ : syracuseStep 551867 = 827801) B827801
theorem B551927 : Blo 366759 551927 := bstep (se 1 (by rfl) ⟨413945, by rfl⟩ : syracuseStep 551927 = 827891) B827891
theorem B551951 : Blo 366759 551951 := bstep (se 1 (by rfl) ⟨413963, by rfl⟩ : syracuseStep 551951 = 827927) B827927
theorem B551993 : Blo 366759 551993 := bstep (se 2 (by rfl) ⟨206997, by rfl⟩ : syracuseStep 551993 = 413995) B413995
theorem B552071 : Blo 366759 552071 := bstep (se 1 (by rfl) ⟨414053, by rfl⟩ : syracuseStep 552071 = 828107) B828107
theorem B552107 : Blo 366759 552107 := bstep (se 1 (by rfl) ⟨414080, by rfl⟩ : syracuseStep 552107 = 828161) B828161
theorem B552137 : Blo 366759 552137 := bstep (se 2 (by rfl) ⟨207051, by rfl⟩ : syracuseStep 552137 = 414103) B414103
theorem B1404161 : Blo 366759 1404161 := bstep (se 2 (by rfl) ⟨526560, by rfl⟩ : syracuseStep 1404161 = 1053121) B1053121
theorem B1404175 : Blo 366759 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B1240379 : Blo 366759 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B552251 : Blo 366759 552251 := bstep (se 1 (by rfl) ⟨414188, by rfl⟩ : syracuseStep 552251 = 828377) B828377
theorem B552311 : Blo 366759 552311 := bstep (se 1 (by rfl) ⟨414233, by rfl⟩ : syracuseStep 552311 = 828467) B828467
theorem B552335 : Blo 366759 552335 := bstep (se 1 (by rfl) ⟨414251, by rfl⟩ : syracuseStep 552335 = 828503) B828503
theorem B2354579 : Blo 366759 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B552377 : Blo 366759 552377 := bstep (se 2 (by rfl) ⟨207141, by rfl⟩ : syracuseStep 552377 = 414283) B414283
theorem B552455 : Blo 366759 552455 := bstep (se 1 (by rfl) ⟨414341, by rfl⟩ : syracuseStep 552455 = 828683) B828683
theorem B1568285 : Blo 366759 1568285 := bstep (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) B588107
theorem B552491 : Blo 366759 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B552521 : Blo 366759 552521 := bstep (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) B414391
theorem B552635 : Blo 366759 552635 := bstep (se 1 (by rfl) ⟨414476, by rfl⟩ : syracuseStep 552635 = 828953) B828953
theorem B552695 : Blo 366759 552695 := bstep (se 1 (by rfl) ⟨414521, by rfl⟩ : syracuseStep 552695 = 829043) B829043
theorem B3337985 : Blo 366759 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B552719 : Blo 366759 552719 := bstep (se 1 (by rfl) ⟨414539, by rfl⟩ : syracuseStep 552719 = 829079) B829079
theorem B945935 : Blo 366759 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B1240865 : Blo 366759 1240865 := bstep (se 2 (by rfl) ⟨465324, by rfl⟩ : syracuseStep 1240865 = 930649) B930649
theorem B552761 : Blo 366759 552761 := bstep (se 2 (by rfl) ⟨207285, by rfl⟩ : syracuseStep 552761 = 414571) B414571
theorem B552839 : Blo 366759 552839 := bstep (se 1 (by rfl) ⟨414629, by rfl⟩ : syracuseStep 552839 = 829259) B829259
theorem B5369753 : Blo 366759 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B552875 : Blo 366759 552875 := bstep (se 1 (by rfl) ⟨414656, by rfl⟩ : syracuseStep 552875 = 829313) B829313
theorem B1994681 : Blo 366759 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B552905 : Blo 366759 552905 := bstep (se 2 (by rfl) ⟨207339, by rfl⟩ : syracuseStep 552905 = 414679) B414679
theorem B553019 : Blo 366759 553019 := bstep (se 1 (by rfl) ⟨414764, by rfl⟩ : syracuseStep 553019 = 829529) B829529
theorem B1601603 : Blo 366759 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B11300957 : Blo 366759 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B553079 : Blo 366759 553079 := bstep (se 1 (by rfl) ⟨414809, by rfl⟩ : syracuseStep 553079 = 829619) B829619
theorem B553103 : Blo 366759 553103 := bstep (se 1 (by rfl) ⟨414827, by rfl⟩ : syracuseStep 553103 = 829655) B829655
theorem B553145 : Blo 366759 553145 := bstep (se 2 (by rfl) ⟨207429, by rfl⟩ : syracuseStep 553145 = 414859) B414859
theorem B1568969 : Blo 366759 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B553223 : Blo 366759 553223 := bstep (se 1 (by rfl) ⟨414917, by rfl⟩ : syracuseStep 553223 = 829835) B829835
theorem B553259 : Blo 366759 553259 := bstep (se 1 (by rfl) ⟨414944, by rfl⟩ : syracuseStep 553259 = 829889) B829889
theorem B553289 : Blo 366759 553289 := bstep (se 2 (by rfl) ⟨207483, by rfl⟩ : syracuseStep 553289 = 414967) B414967
theorem B1241459 : Blo 366759 1241459 := bstep (se 1 (by rfl) ⟨931094, by rfl⟩ : syracuseStep 1241459 = 1862189) B1862189
theorem B1995155 : Blo 366759 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B553403 : Blo 366759 553403 := bstep (se 1 (by rfl) ⟨415052, by rfl⟩ : syracuseStep 553403 = 830105) B830105
theorem B553463 : Blo 366759 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B1405451 : Blo 366759 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B553487 : Blo 366759 553487 := bstep (se 1 (by rfl) ⟨415115, by rfl⟩ : syracuseStep 553487 = 830231) B830231
theorem B2093597 : Blo 366759 2093597 := bstep (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) B785099
theorem B553529 : Blo 366759 553529 := bstep (se 2 (by rfl) ⟨207573, by rfl⟩ : syracuseStep 553529 = 415147) B415147
theorem B553607 : Blo 366759 553607 := bstep (se 1 (by rfl) ⟨415205, by rfl⟩ : syracuseStep 553607 = 830411) B830411
theorem B553643 : Blo 366759 553643 := bstep (se 1 (by rfl) ⟨415232, by rfl⟩ : syracuseStep 553643 = 830465) B830465
theorem B553673 : Blo 366759 553673 := bstep (se 2 (by rfl) ⟨207627, by rfl⟩ : syracuseStep 553673 = 415255) B415255
theorem B553787 : Blo 366759 553787 := bstep (se 1 (by rfl) ⟨415340, by rfl⟩ : syracuseStep 553787 = 830681) B830681
theorem B553847 : Blo 366759 553847 := bstep (se 1 (by rfl) ⟨415385, by rfl⟩ : syracuseStep 553847 = 830771) B830771
theorem B553871 : Blo 366759 553871 := bstep (se 1 (by rfl) ⟨415403, by rfl⟩ : syracuseStep 553871 = 830807) B830807
theorem B553913 : Blo 366759 553913 := bstep (se 2 (by rfl) ⟨207717, by rfl⟩ : syracuseStep 553913 = 415435) B415435
theorem B553991 : Blo 366759 553991 := bstep (se 1 (by rfl) ⟨415493, by rfl⟩ : syracuseStep 553991 = 830987) B830987
theorem B619535 : Blo 366759 619535 := bstep (se 1 (by rfl) ⟨464651, by rfl⟩ : syracuseStep 619535 = 929303) B929303
theorem B554027 : Blo 366759 554027 := bstep (se 1 (by rfl) ⟨415520, by rfl⟩ : syracuseStep 554027 = 831041) B831041
theorem B554057 : Blo 366759 554057 := bstep (se 2 (by rfl) ⟨207771, by rfl⟩ : syracuseStep 554057 = 415543) B415543
theorem B554171 : Blo 366759 554171 := bstep (se 1 (by rfl) ⟨415628, by rfl⟩ : syracuseStep 554171 = 831257) B831257
theorem B1045705 : Blo 366759 1045705 := bstep (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) B784279
theorem B2094281 : Blo 366759 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B554231 : Blo 366759 554231 := bstep (se 1 (by rfl) ⟨415673, by rfl⟩ : syracuseStep 554231 = 831347) B831347
theorem B1242383 : Blo 366759 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B554255 : Blo 366759 554255 := bstep (se 1 (by rfl) ⟨415691, by rfl⟩ : syracuseStep 554255 = 831383) B831383
theorem B554297 : Blo 366759 554297 := bstep (se 2 (by rfl) ⟨207861, by rfl⟩ : syracuseStep 554297 = 415723) B415723
theorem B554375 : Blo 366759 554375 := bstep (se 1 (by rfl) ⟨415781, by rfl⟩ : syracuseStep 554375 = 831563) B831563
theorem B1865105 : Blo 366759 1865105 := bstep (se 2 (by rfl) ⟨699414, by rfl⟩ : syracuseStep 1865105 = 1398829) B1398829
theorem B554411 : Blo 366759 554411 := bstep (se 1 (by rfl) ⟨415808, by rfl⟩ : syracuseStep 554411 = 831617) B831617
theorem B1406393 : Blo 366759 1406393 := bstep (se 2 (by rfl) ⟨527397, by rfl⟩ : syracuseStep 1406393 = 1054795) B1054795
theorem B554441 : Blo 366759 554441 := bstep (se 2 (by rfl) ⟨207915, by rfl⟩ : syracuseStep 554441 = 415831) B415831
theorem B620075 : Blo 366759 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B554555 : Blo 366759 554555 := bstep (se 1 (by rfl) ⟨415916, by rfl⟩ : syracuseStep 554555 = 831833) B831833
theorem B554615 : Blo 366759 554615 := bstep (se 1 (by rfl) ⟨415961, by rfl⟩ : syracuseStep 554615 = 831923) B831923
theorem B554639 : Blo 366759 554639 := bstep (se 1 (by rfl) ⟨415979, by rfl⟩ : syracuseStep 554639 = 831959) B831959
theorem B3536561 : Blo 366759 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B554681 : Blo 366759 554681 := bstep (se 2 (by rfl) ⟨208005, by rfl⟩ : syracuseStep 554681 = 416011) B416011
theorem B554759 : Blo 366759 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B718625 : Blo 366759 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B554795 : Blo 366759 554795 := bstep (se 1 (by rfl) ⟨416096, by rfl⟩ : syracuseStep 554795 = 832193) B832193
theorem B554825 : Blo 366759 554825 := bstep (se 2 (by rfl) ⟨208059, by rfl⟩ : syracuseStep 554825 = 416119) B416119
theorem B620473 : Blo 366759 620473 := bstep (se 2 (by rfl) ⟨232677, by rfl⟩ : syracuseStep 620473 = 465355) B465355
theorem B1570745 : Blo 366759 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B554939 : Blo 366759 554939 := bstep (se 1 (by rfl) ⟨416204, by rfl⟩ : syracuseStep 554939 = 832409) B832409
theorem B554999 : Blo 366759 554999 := bstep (se 1 (by rfl) ⟨416249, by rfl⟩ : syracuseStep 554999 = 832499) B832499
theorem B784399 : Blo 366759 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B555023 : Blo 366759 555023 := bstep (se 1 (by rfl) ⟨416267, by rfl⟩ : syracuseStep 555023 = 832535) B832535
theorem B522283 : Blo 366759 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B555065 : Blo 366759 555065 := bstep (se 2 (by rfl) ⟨208149, by rfl⟩ : syracuseStep 555065 = 416299) B416299
theorem B555143 : Blo 366759 555143 := bstep (se 1 (by rfl) ⟨416357, by rfl⟩ : syracuseStep 555143 = 832715) B832715
theorem B555179 : Blo 366759 555179 := bstep (se 1 (by rfl) ⟨416384, by rfl⟩ : syracuseStep 555179 = 832769) B832769
theorem B555209 : Blo 366759 555209 := bstep (se 2 (by rfl) ⟨208203, by rfl⟩ : syracuseStep 555209 = 416407) B416407
theorem B784655 : Blo 366759 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B555323 : Blo 366759 555323 := bstep (se 1 (by rfl) ⟨416492, by rfl⟩ : syracuseStep 555323 = 832985) B832985
theorem B555383 : Blo 366759 555383 := bstep (se 1 (by rfl) ⟨416537, by rfl⟩ : syracuseStep 555383 = 833075) B833075
theorem B555407 : Blo 366759 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B6289811 : Blo 366759 6289811 := bstep (se 1 (by rfl) ⟨4717358, by rfl⟩ : syracuseStep 6289811 = 9434717) B9434717
theorem B555449 : Blo 366759 555449 := bstep (se 2 (by rfl) ⟨208293, by rfl⟩ : syracuseStep 555449 = 416587) B416587
theorem B555527 : Blo 366759 555527 := bstep (se 1 (by rfl) ⟨416645, by rfl⟩ : syracuseStep 555527 = 833291) B833291
theorem B555563 : Blo 366759 555563 := bstep (se 1 (by rfl) ⟨416672, by rfl⟩ : syracuseStep 555563 = 833345) B833345
theorem B555593 : Blo 366759 555593 := bstep (se 2 (by rfl) ⟨208347, by rfl⟩ : syracuseStep 555593 = 416695) B416695
theorem B1800791 : Blo 366759 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B621175 : Blo 366759 621175 := bstep (se 1 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 621175 = 931763) B931763
theorem B555707 : Blo 366759 555707 := bstep (se 1 (by rfl) ⟨416780, by rfl⟩ : syracuseStep 555707 = 833561) B833561
theorem B555767 : Blo 366759 555767 := bstep (se 1 (by rfl) ⟨416825, by rfl⟩ : syracuseStep 555767 = 833651) B833651
theorem B424711 : Blo 366759 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B555791 : Blo 366759 555791 := bstep (se 1 (by rfl) ⟨416843, by rfl⟩ : syracuseStep 555791 = 833687) B833687
theorem B555833 : Blo 366759 555833 := bstep (se 2 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 555833 = 416875) B416875
theorem B621371 : Blo 366759 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B555911 : Blo 366759 555911 := bstep (se 1 (by rfl) ⟨416933, by rfl⟩ : syracuseStep 555911 = 833867) B833867
theorem B1244051 : Blo 366759 1244051 := bstep (se 1 (by rfl) ⟨933038, by rfl⟩ : syracuseStep 1244051 = 1866077) B1866077
theorem B555947 : Blo 366759 555947 := bstep (se 1 (by rfl) ⟨416960, by rfl⟩ : syracuseStep 555947 = 833921) B833921
theorem B2096057 : Blo 366759 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B555977 : Blo 366759 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B1047563 : Blo 366759 1047563 := bstep (se 1 (by rfl) ⟨785672, by rfl⟩ : syracuseStep 1047563 = 1571345) B1571345
theorem B785467 : Blo 366759 785467 := bstep (se 1 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 785467 = 1178201) B1178201
theorem B556091 : Blo 366759 556091 := bstep (se 1 (by rfl) ⟨417068, by rfl⟩ : syracuseStep 556091 = 834137) B834137
theorem B785543 : Blo 366759 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B621769 : Blo 366759 621769 := bstep (se 2 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 621769 = 466327) B466327
theorem B785783 : Blo 366759 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B392635 : Blo 366759 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B1867211 : Blo 366759 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B785953 : Blo 366759 785953 := bstep (se 2 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 785953 = 589465) B589465
theorem B884267 : Blo 366759 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B1048211 : Blo 366759 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B1867535 : Blo 366759 1867535 := bstep (se 1 (by rfl) ⟨1400651, by rfl⟩ : syracuseStep 1867535 = 2801303) B2801303
theorem B3374963 : Blo 366759 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B786295 : Blo 366759 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B1048439 : Blo 366759 1048439 := bstep (se 1 (by rfl) ⟨786329, by rfl⟩ : syracuseStep 1048439 = 1572659) B1572659
theorem B622471 : Blo 366759 622471 := bstep (se 1 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 622471 = 933707) B933707
theorem B1245185 : Blo 366759 1245185 := bstep (se 2 (by rfl) ⟨466944, by rfl⟩ : syracuseStep 1245185 = 933889) B933889
theorem B1048747 : Blo 366759 1048747 := bstep (se 1 (by rfl) ⟨786560, by rfl⟩ : syracuseStep 1048747 = 1573121) B1573121
theorem B622991 : Blo 366759 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B2359705 : Blo 366759 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B2097697 : Blo 366759 2097697 := bstep (se 2 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 2097697 = 1573273) B1573273
theorem B623227 : Blo 366759 623227 := bstep (se 1 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 623227 = 934841) B934841
theorem B1245995 : Blo 366759 1245995 := bstep (se 1 (by rfl) ⟨934496, by rfl⟩ : syracuseStep 1245995 = 1868993) B1868993
theorem B10617749 : Blo 366759 10617749 := bstep (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) B497707
theorem B1180673 : Blo 366759 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B787475 : Blo 366759 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B1246265 : Blo 366759 1246265 := bstep (se 2 (by rfl) ⟨467349, by rfl⟩ : syracuseStep 1246265 = 934699) B934699
theorem B2589763 : Blo 366759 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B6980825 : Blo 366759 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1246589 : Blo 366759 1246589 := bstep (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) B467471
theorem B1181071 : Blo 366759 1181071 := bstep (se 1 (by rfl) ⟨885803, by rfl⟩ : syracuseStep 1181071 = 1771607) B1771607
theorem B2786723 : Blo 366759 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B624091 : Blo 366759 624091 := bstep (se 1 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 624091 = 936137) B936137
theorem B5703131 : Blo 366759 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B394831 : Blo 366759 394831 := bstep (se 1 (by rfl) ⟨296123, by rfl⟩ : syracuseStep 394831 = 592247) B592247
theorem B1246859 : Blo 366759 1246859 := bstep (se 1 (by rfl) ⟨935144, by rfl⟩ : syracuseStep 1246859 = 1870289) B1870289
theorem B886601 : Blo 366759 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B624719 : Blo 366759 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B1247777 : Blo 366759 1247777 := bstep (se 2 (by rfl) ⟨467916, by rfl⟩ : syracuseStep 1247777 = 935833) B935833
theorem B789115 : Blo 366759 789115 := bstep (se 1 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 789115 = 1183673) B1183673
theorem B1247993 : Blo 366759 1247993 := bstep (se 2 (by rfl) ⟨467997, by rfl⟩ : syracuseStep 1247993 = 935995) B935995
theorem B625583 : Blo 366759 625583 := bstep (se 1 (by rfl) ⟨469187, by rfl⟩ : syracuseStep 625583 = 938375) B938375
theorem B887735 : Blo 366759 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B1870775 : Blo 366759 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1248263 : Blo 366759 1248263 := bstep (se 1 (by rfl) ⟨936197, by rfl⟩ : syracuseStep 1248263 = 1872395) B1872395
theorem B1248371 : Blo 366759 1248371 := bstep (se 1 (by rfl) ⟨936278, by rfl⟩ : syracuseStep 1248371 = 1872557) B1872557
theorem B1281367 : Blo 366759 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B4787545 : Blo 366759 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B3313021 : Blo 366759 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B1248641 : Blo 366759 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B527791 : Blo 366759 527791 := bstep (se 1 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 527791 = 791687) B791687
theorem B593335 : Blo 366759 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B1412747 : Blo 366759 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B2789153 : Blo 366759 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B5672771 : Blo 366759 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B757883 : Blo 366759 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B1249451 : Blo 366759 1249451 := bstep (se 1 (by rfl) ⟨937088, by rfl⟩ : syracuseStep 1249451 = 1874177) B1874177
theorem B1872233 : Blo 366759 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B1249991 : Blo 366759 1249991 := bstep (se 1 (by rfl) ⟨937493, by rfl⟩ : syracuseStep 1249991 = 1874987) B1874987
theorem B2659027 : Blo 366759 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B1053395 : Blo 366759 1053395 := bstep (se 1 (by rfl) ⟨790046, by rfl⟩ : syracuseStep 1053395 = 1580093) B1580093
theorem B5969371 : Blo 366759 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B1185313 : Blo 366759 1185313 := bstep (se 2 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 1185313 = 888985) B888985
theorem B1250855 : Blo 366759 1250855 := bstep (se 1 (by rfl) ⟨938141, by rfl⟩ : syracuseStep 1250855 = 1876283) B1876283
theorem B1250963 : Blo 366759 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B1054397 : Blo 366759 1054397 := bstep (se 3 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 1054397 = 395399) B395399
theorem B1185491 : Blo 366759 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B497513 : Blo 366759 497513 := bstep (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) B373135
theorem B661355 : Blo 366759 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B1251179 : Blo 366759 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B1251233 : Blo 366759 1251233 := bstep (se 2 (by rfl) ⟨469212, by rfl⟩ : syracuseStep 1251233 = 938425) B938425
theorem B825263 : Blo 366759 825263 := bstep (se 1 (by rfl) ⟨618947, by rfl⟩ : syracuseStep 825263 = 1237895) B1237895
theorem B2988035 : Blo 366759 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B1185799 : Blo 366759 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054727 : Blo 366759 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B464935 : Blo 366759 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B825515 : Blo 366759 825515 := bstep (se 1 (by rfl) ⟨619136, by rfl⟩ : syracuseStep 825515 = 1238273) B1238273
theorem B366767 : Blo 366759 366767 := bstep (se 1 (by rfl) ⟨275075, by rfl⟩ : syracuseStep 366767 = 550151) B550151
theorem B366791 : Blo 366759 366791 := bstep (se 1 (by rfl) ⟨275093, by rfl⟩ : syracuseStep 366791 = 550187) B550187
theorem B366811 : Blo 366759 366811 := bstep (se 1 (by rfl) ⟨275108, by rfl⟩ : syracuseStep 366811 = 550217) B550217
theorem B366887 : Blo 366759 366887 := bstep (se 1 (by rfl) ⟨275165, by rfl⟩ : syracuseStep 366887 = 550331) B550331
theorem B4004147 : Blo 366759 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B366927 : Blo 366759 366927 := bstep (se 1 (by rfl) ⟨275195, by rfl⟩ : syracuseStep 366927 = 550391) B550391
theorem B366943 : Blo 366759 366943 := bstep (se 1 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 366943 = 550415) B550415
theorem B465259 : Blo 366759 465259 := bstep (se 1 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 465259 = 697889) B697889
theorem B366971 : Blo 366759 366971 := bstep (se 1 (by rfl) ⟨275228, by rfl⟩ : syracuseStep 366971 = 550457) B550457
theorem B367023 : Blo 366759 367023 := bstep (se 1 (by rfl) ⟨275267, by rfl⟩ : syracuseStep 367023 = 550535) B550535
theorem B367047 : Blo 366759 367047 := bstep (se 1 (by rfl) ⟨275285, by rfl⟩ : syracuseStep 367047 = 550571) B550571
theorem B367067 : Blo 366759 367067 := bstep (se 1 (by rfl) ⟨275300, by rfl⟩ : syracuseStep 367067 = 550601) B550601
theorem B367143 : Blo 366759 367143 := bstep (se 1 (by rfl) ⟨275357, by rfl⟩ : syracuseStep 367143 = 550715) B550715
theorem B367183 : Blo 366759 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B367199 : Blo 366759 367199 := bstep (se 1 (by rfl) ⟨275399, by rfl⟩ : syracuseStep 367199 = 550799) B550799
theorem B367227 : Blo 366759 367227 := bstep (se 1 (by rfl) ⟨275420, by rfl⟩ : syracuseStep 367227 = 550841) B550841
theorem B367279 : Blo 366759 367279 := bstep (se 1 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 367279 = 550919) B550919
theorem B826055 : Blo 366759 826055 := bstep (se 1 (by rfl) ⟨619541, by rfl⟩ : syracuseStep 826055 = 1239083) B1239083
theorem B367303 : Blo 366759 367303 := bstep (se 1 (by rfl) ⟨275477, by rfl⟩ : syracuseStep 367303 = 550955) B550955
theorem B367323 : Blo 366759 367323 := bstep (se 1 (by rfl) ⟨275492, by rfl⟩ : syracuseStep 367323 = 550985) B550985
theorem B367399 : Blo 366759 367399 := bstep (se 1 (by rfl) ⟨275549, by rfl⟩ : syracuseStep 367399 = 551099) B551099
theorem B367439 : Blo 366759 367439 := bstep (se 1 (by rfl) ⟨275579, by rfl⟩ : syracuseStep 367439 = 551159) B551159
theorem B367455 : Blo 366759 367455 := bstep (se 1 (by rfl) ⟨275591, by rfl⟩ : syracuseStep 367455 = 551183) B551183
theorem B367483 : Blo 366759 367483 := bstep (se 1 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 367483 = 551225) B551225
theorem B367535 : Blo 366759 367535 := bstep (se 1 (by rfl) ⟨275651, by rfl⟩ : syracuseStep 367535 = 551303) B551303
theorem B367559 : Blo 366759 367559 := bstep (se 1 (by rfl) ⟨275669, by rfl⟩ : syracuseStep 367559 = 551339) B551339
theorem B367579 : Blo 366759 367579 := bstep (se 1 (by rfl) ⟨275684, by rfl⟩ : syracuseStep 367579 = 551369) B551369
theorem B367655 : Blo 366759 367655 := bstep (se 1 (by rfl) ⟨275741, by rfl⟩ : syracuseStep 367655 = 551483) B551483
theorem B367695 : Blo 366759 367695 := bstep (se 1 (by rfl) ⟨275771, by rfl⟩ : syracuseStep 367695 = 551543) B551543
theorem B367711 : Blo 366759 367711 := bstep (se 1 (by rfl) ⟨275783, by rfl⟩ : syracuseStep 367711 = 551567) B551567
theorem B367739 : Blo 366759 367739 := bstep (se 1 (by rfl) ⟨275804, by rfl⟩ : syracuseStep 367739 = 551609) B551609
theorem B367791 : Blo 366759 367791 := bstep (se 1 (by rfl) ⟨275843, by rfl⟩ : syracuseStep 367791 = 551687) B551687
theorem B367815 : Blo 366759 367815 := bstep (se 1 (by rfl) ⟨275861, by rfl⟩ : syracuseStep 367815 = 551723) B551723
theorem B367835 : Blo 366759 367835 := bstep (se 1 (by rfl) ⟨275876, by rfl⟩ : syracuseStep 367835 = 551753) B551753
theorem B367911 : Blo 366759 367911 := bstep (se 1 (by rfl) ⟨275933, by rfl⟩ : syracuseStep 367911 = 551867) B551867
theorem B367951 : Blo 366759 367951 := bstep (se 1 (by rfl) ⟨275963, by rfl⟩ : syracuseStep 367951 = 551927) B551927
theorem B367967 : Blo 366759 367967 := bstep (se 1 (by rfl) ⟨275975, by rfl⟩ : syracuseStep 367967 = 551951) B551951
theorem B367995 : Blo 366759 367995 := bstep (se 1 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 367995 = 551993) B551993
theorem B368047 : Blo 366759 368047 := bstep (se 1 (by rfl) ⟨276035, by rfl⟩ : syracuseStep 368047 = 552071) B552071
theorem B368071 : Blo 366759 368071 := bstep (se 1 (by rfl) ⟨276053, by rfl⟩ : syracuseStep 368071 = 552107) B552107
theorem B368091 : Blo 366759 368091 := bstep (se 1 (by rfl) ⟨276068, by rfl⟩ : syracuseStep 368091 = 552137) B552137
theorem B826919 : Blo 366759 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B368167 : Blo 366759 368167 := bstep (se 1 (by rfl) ⟨276125, by rfl⟩ : syracuseStep 368167 = 552251) B552251
theorem B368207 : Blo 366759 368207 := bstep (se 1 (by rfl) ⟨276155, by rfl⟩ : syracuseStep 368207 = 552311) B552311
theorem B368223 : Blo 366759 368223 := bstep (se 1 (by rfl) ⟨276167, by rfl⟩ : syracuseStep 368223 = 552335) B552335
theorem B368251 : Blo 366759 368251 := bstep (se 1 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 368251 = 552377) B552377
theorem B466555 : Blo 366759 466555 := bstep (se 1 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 466555 = 699833) B699833
theorem B368303 : Blo 366759 368303 := bstep (se 1 (by rfl) ⟨276227, by rfl⟩ : syracuseStep 368303 = 552455) B552455
theorem B368327 : Blo 366759 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B368347 : Blo 366759 368347 := bstep (se 1 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 368347 = 552521) B552521
theorem B368423 : Blo 366759 368423 := bstep (se 1 (by rfl) ⟨276317, by rfl⟩ : syracuseStep 368423 = 552635) B552635
theorem B368463 : Blo 366759 368463 := bstep (se 1 (by rfl) ⟨276347, by rfl⟩ : syracuseStep 368463 = 552695) B552695
theorem B368479 : Blo 366759 368479 := bstep (se 1 (by rfl) ⟨276359, by rfl⟩ : syracuseStep 368479 = 552719) B552719
theorem B630623 : Blo 366759 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B827243 : Blo 366759 827243 := bstep (se 1 (by rfl) ⟨620432, by rfl⟩ : syracuseStep 827243 = 1240865) B1240865
theorem B368507 : Blo 366759 368507 := bstep (se 1 (by rfl) ⟨276380, by rfl⟩ : syracuseStep 368507 = 552761) B552761
theorem B827297 : Blo 366759 827297 := bstep (se 2 (by rfl) ⟨310236, by rfl⟩ : syracuseStep 827297 = 620473) B620473
theorem B368559 : Blo 366759 368559 := bstep (se 1 (by rfl) ⟨276419, by rfl⟩ : syracuseStep 368559 = 552839) B552839
theorem B3579835 : Blo 366759 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B368583 : Blo 366759 368583 := bstep (se 1 (by rfl) ⟨276437, by rfl⟩ : syracuseStep 368583 = 552875) B552875
theorem B368603 : Blo 366759 368603 := bstep (se 1 (by rfl) ⟨276452, by rfl⟩ : syracuseStep 368603 = 552905) B552905
theorem B368679 : Blo 366759 368679 := bstep (se 1 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 368679 = 553019) B553019
theorem B696377 : Blo 366759 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B368719 : Blo 366759 368719 := bstep (se 1 (by rfl) ⟨276539, by rfl⟩ : syracuseStep 368719 = 553079) B553079
theorem B368735 : Blo 366759 368735 := bstep (se 1 (by rfl) ⟨276551, by rfl⟩ : syracuseStep 368735 = 553103) B553103
theorem B368763 : Blo 366759 368763 := bstep (se 1 (by rfl) ⟨276572, by rfl⟩ : syracuseStep 368763 = 553145) B553145
theorem B368815 : Blo 366759 368815 := bstep (se 1 (by rfl) ⟨276611, by rfl⟩ : syracuseStep 368815 = 553223) B553223
theorem B368839 : Blo 366759 368839 := bstep (se 1 (by rfl) ⟨276629, by rfl⟩ : syracuseStep 368839 = 553259) B553259
theorem B368859 : Blo 366759 368859 := bstep (se 1 (by rfl) ⟨276644, by rfl⟩ : syracuseStep 368859 = 553289) B553289
theorem B827639 : Blo 366759 827639 := bstep (se 1 (by rfl) ⟨620729, by rfl⟩ : syracuseStep 827639 = 1241459) B1241459
theorem B368935 : Blo 366759 368935 := bstep (se 1 (by rfl) ⟨276701, by rfl⟩ : syracuseStep 368935 = 553403) B553403
theorem B368975 : Blo 366759 368975 := bstep (se 1 (by rfl) ⟨276731, by rfl⟩ : syracuseStep 368975 = 553463) B553463
theorem B368991 : Blo 366759 368991 := bstep (se 1 (by rfl) ⟨276743, by rfl⟩ : syracuseStep 368991 = 553487) B553487
theorem B369019 : Blo 366759 369019 := bstep (se 1 (by rfl) ⟨276764, by rfl⟩ : syracuseStep 369019 = 553529) B553529
theorem B369071 : Blo 366759 369071 := bstep (se 1 (by rfl) ⟨276803, by rfl⟩ : syracuseStep 369071 = 553607) B553607
theorem B369095 : Blo 366759 369095 := bstep (se 1 (by rfl) ⟨276821, by rfl⟩ : syracuseStep 369095 = 553643) B553643
theorem B369115 : Blo 366759 369115 := bstep (se 1 (by rfl) ⟨276836, by rfl⟩ : syracuseStep 369115 = 553673) B553673
theorem B369191 : Blo 366759 369191 := bstep (se 1 (by rfl) ⟨276893, by rfl⟩ : syracuseStep 369191 = 553787) B553787
theorem B369231 : Blo 366759 369231 := bstep (se 1 (by rfl) ⟨276923, by rfl⟩ : syracuseStep 369231 = 553847) B553847
theorem B369247 : Blo 366759 369247 := bstep (se 1 (by rfl) ⟨276935, by rfl⟩ : syracuseStep 369247 = 553871) B553871
theorem B369275 : Blo 366759 369275 := bstep (se 1 (by rfl) ⟨276956, by rfl⟩ : syracuseStep 369275 = 553913) B553913
theorem B369327 : Blo 366759 369327 := bstep (se 1 (by rfl) ⟨276995, by rfl⟩ : syracuseStep 369327 = 553991) B553991
theorem B2826937 : Blo 366759 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B369351 : Blo 366759 369351 := bstep (se 1 (by rfl) ⟨277013, by rfl⟩ : syracuseStep 369351 = 554027) B554027
theorem B369371 : Blo 366759 369371 := bstep (se 1 (by rfl) ⟨277028, by rfl⟩ : syracuseStep 369371 = 554057) B554057
theorem B369447 : Blo 366759 369447 := bstep (se 1 (by rfl) ⟨277085, by rfl⟩ : syracuseStep 369447 = 554171) B554171
theorem B828233 : Blo 366759 828233 := bstep (se 2 (by rfl) ⟨310587, by rfl⟩ : syracuseStep 828233 = 621175) B621175
theorem B369487 : Blo 366759 369487 := bstep (se 1 (by rfl) ⟨277115, by rfl⟩ : syracuseStep 369487 = 554231) B554231
theorem B369503 : Blo 366759 369503 := bstep (se 1 (by rfl) ⟨277127, by rfl⟩ : syracuseStep 369503 = 554255) B554255
theorem B369531 : Blo 366759 369531 := bstep (se 1 (by rfl) ⟨277148, by rfl⟩ : syracuseStep 369531 = 554297) B554297
theorem B369583 : Blo 366759 369583 := bstep (se 1 (by rfl) ⟨277187, by rfl⟩ : syracuseStep 369583 = 554375) B554375
theorem B369607 : Blo 366759 369607 := bstep (se 1 (by rfl) ⟨277205, by rfl⟩ : syracuseStep 369607 = 554411) B554411
theorem B369627 : Blo 366759 369627 := bstep (se 1 (by rfl) ⟨277220, by rfl⟩ : syracuseStep 369627 = 554441) B554441
theorem B566281 : Blo 366759 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B369703 : Blo 366759 369703 := bstep (se 1 (by rfl) ⟨277277, by rfl⟩ : syracuseStep 369703 = 554555) B554555
theorem B1025081 : Blo 366759 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B369743 : Blo 366759 369743 := bstep (se 1 (by rfl) ⟨277307, by rfl⟩ : syracuseStep 369743 = 554615) B554615
theorem B369759 : Blo 366759 369759 := bstep (se 1 (by rfl) ⟨277319, by rfl⟩ : syracuseStep 369759 = 554639) B554639
theorem B369787 : Blo 366759 369787 := bstep (se 1 (by rfl) ⟨277340, by rfl⟩ : syracuseStep 369787 = 554681) B554681
theorem B369839 : Blo 366759 369839 := bstep (se 1 (by rfl) ⟨277379, by rfl⟩ : syracuseStep 369839 = 554759) B554759
theorem B40412357 : Blo 366759 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B369863 : Blo 366759 369863 := bstep (se 1 (by rfl) ⟨277397, by rfl⟩ : syracuseStep 369863 = 554795) B554795
theorem B369883 : Blo 366759 369883 := bstep (se 1 (by rfl) ⟨277412, by rfl⟩ : syracuseStep 369883 = 554825) B554825
theorem B369959 : Blo 366759 369959 := bstep (se 1 (by rfl) ⟨277469, by rfl⟩ : syracuseStep 369959 = 554939) B554939
theorem B369999 : Blo 366759 369999 := bstep (se 1 (by rfl) ⟨277499, by rfl⟩ : syracuseStep 369999 = 554999) B554999
theorem B370015 : Blo 366759 370015 := bstep (se 1 (by rfl) ⟨277511, by rfl⟩ : syracuseStep 370015 = 555023) B555023
theorem B370043 : Blo 366759 370043 := bstep (se 1 (by rfl) ⟨277532, by rfl⟩ : syracuseStep 370043 = 555065) B555065
theorem B370095 : Blo 366759 370095 := bstep (se 1 (by rfl) ⟨277571, by rfl⟩ : syracuseStep 370095 = 555143) B555143
theorem B370119 : Blo 366759 370119 := bstep (se 1 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 370119 = 555179) B555179
theorem B468443 : Blo 366759 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B370139 : Blo 366759 370139 := bstep (se 1 (by rfl) ⟨277604, by rfl⟩ : syracuseStep 370139 = 555209) B555209
theorem B370215 : Blo 366759 370215 := bstep (se 1 (by rfl) ⟨277661, by rfl⟩ : syracuseStep 370215 = 555323) B555323
theorem B665167 : Blo 366759 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B370255 : Blo 366759 370255 := bstep (se 1 (by rfl) ⟨277691, by rfl⟩ : syracuseStep 370255 = 555383) B555383
theorem B370271 : Blo 366759 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B829025 : Blo 366759 829025 := bstep (se 2 (by rfl) ⟨310884, by rfl⟩ : syracuseStep 829025 = 621769) B621769
theorem B370299 : Blo 366759 370299 := bstep (se 1 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 370299 = 555449) B555449
theorem B370351 : Blo 366759 370351 := bstep (se 1 (by rfl) ⟨277763, by rfl⟩ : syracuseStep 370351 = 555527) B555527
theorem B370375 : Blo 366759 370375 := bstep (se 1 (by rfl) ⟨277781, by rfl⟩ : syracuseStep 370375 = 555563) B555563
theorem B370395 : Blo 366759 370395 := bstep (se 1 (by rfl) ⟨277796, by rfl⟩ : syracuseStep 370395 = 555593) B555593
theorem B3155705 : Blo 366759 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B1582841 : Blo 366759 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B370471 : Blo 366759 370471 := bstep (se 1 (by rfl) ⟨277853, by rfl⟩ : syracuseStep 370471 = 555707) B555707
theorem B370511 : Blo 366759 370511 := bstep (se 1 (by rfl) ⟨277883, by rfl⟩ : syracuseStep 370511 = 555767) B555767
theorem B370527 : Blo 366759 370527 := bstep (se 1 (by rfl) ⟨277895, by rfl⟩ : syracuseStep 370527 = 555791) B555791
theorem B370555 : Blo 366759 370555 := bstep (se 1 (by rfl) ⟨277916, by rfl⟩ : syracuseStep 370555 = 555833) B555833
theorem B370607 : Blo 366759 370607 := bstep (se 1 (by rfl) ⟨277955, by rfl⟩ : syracuseStep 370607 = 555911) B555911
theorem B829367 : Blo 366759 829367 := bstep (se 1 (by rfl) ⟨622025, by rfl⟩ : syracuseStep 829367 = 1244051) B1244051
theorem B468919 : Blo 366759 468919 := bstep (se 1 (by rfl) ⟨351689, by rfl⟩ : syracuseStep 468919 = 703379) B703379
theorem B370631 : Blo 366759 370631 := bstep (se 1 (by rfl) ⟨277973, by rfl⟩ : syracuseStep 370631 = 555947) B555947
theorem B370651 : Blo 366759 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B698375 : Blo 366759 698375 := bstep (se 1 (by rfl) ⟨523781, by rfl⟩ : syracuseStep 698375 = 1047563) B1047563
theorem B370727 : Blo 366759 370727 := bstep (se 1 (by rfl) ⟨278045, by rfl⟩ : syracuseStep 370727 = 556091) B556091
theorem B698807 : Blo 366759 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B666119 : Blo 366759 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B829961 : Blo 366759 829961 := bstep (se 2 (by rfl) ⟨311235, by rfl⟩ : syracuseStep 829961 = 622471) B622471
theorem B698959 : Blo 366759 698959 := bstep (se 1 (by rfl) ⟨524219, by rfl⟩ : syracuseStep 698959 = 1048439) B1048439
theorem B830303 : Blo 366759 830303 := bstep (se 1 (by rfl) ⟨622727, by rfl⟩ : syracuseStep 830303 = 1245455) B1245455
theorem B830483 : Blo 366759 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B928847 : Blo 366759 928847 := bstep (se 1 (by rfl) ⟨696635, by rfl⟩ : syracuseStep 928847 = 1393271) B1393271
theorem B830825 : Blo 366759 830825 := bstep (se 2 (by rfl) ⟨311559, by rfl⟩ : syracuseStep 830825 = 623119) B623119
theorem B929495 : Blo 366759 929495 := bstep (se 1 (by rfl) ⟨697121, by rfl⟩ : syracuseStep 929495 = 1394243) B1394243
theorem B700265 : Blo 366759 700265 := bstep (se 2 (by rfl) ⟨262599, by rfl⟩ : syracuseStep 700265 = 525199) B525199
theorem B831419 : Blo 366759 831419 := bstep (se 1 (by rfl) ⟨623564, by rfl⟩ : syracuseStep 831419 = 1247129) B1247129
theorem B831545 : Blo 366759 831545 := bstep (se 2 (by rfl) ⟨311829, by rfl⟩ : syracuseStep 831545 = 623659) B623659
theorem B3354853 : Blo 366759 3354853 := bstep (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) B629035
theorem B2240855 : Blo 366759 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B831887 : Blo 366759 831887 := bstep (se 1 (by rfl) ⟨623915, by rfl⟩ : syracuseStep 831887 = 1247831) B1247831
theorem B832211 : Blo 366759 832211 := bstep (se 1 (by rfl) ⟨624158, by rfl⟩ : syracuseStep 832211 = 1248317) B1248317
theorem B9679621 : Blo 366759 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B701291 : Blo 366759 701291 := bstep (se 1 (by rfl) ⟨525968, by rfl⟩ : syracuseStep 701291 = 1051937) B1051937
theorem B4207787 : Blo 366759 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B2995393 : Blo 366759 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B4732121 : Blo 366759 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B701959 : Blo 366759 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B833147 : Blo 366759 833147 := bstep (se 1 (by rfl) ⟨624860, by rfl⟩ : syracuseStep 833147 = 1249721) B1249721
theorem B833273 : Blo 366759 833273 := bstep (se 2 (by rfl) ⟨312477, by rfl⟩ : syracuseStep 833273 = 624955) B624955
theorem B5748515 : Blo 366759 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B3192671 : Blo 366759 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B2701151 : Blo 366759 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B8599505 : Blo 366759 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B833543 : Blo 366759 833543 := bstep (se 1 (by rfl) ⟨625157, by rfl⟩ : syracuseStep 833543 = 1250315) B1250315
theorem B833615 : Blo 366759 833615 := bstep (se 1 (by rfl) ⟨625211, by rfl⟩ : syracuseStep 833615 = 1250423) B1250423
theorem B2799845 : Blo 366759 2799845 := bstep (se 4 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 2799845 = 524971) B524971
theorem B932087 : Blo 366759 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B473563 : Blo 366759 473563 := bstep (se 1 (by rfl) ⟨355172, by rfl⟩ : syracuseStep 473563 = 710345) B710345
theorem B834011 : Blo 366759 834011 := bstep (se 1 (by rfl) ⟨625508, by rfl⟩ : syracuseStep 834011 = 1251017) B1251017
theorem B9812515 : Blo 366759 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B2866103 : Blo 366759 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B4734125 : Blo 366759 4734125 := bstep (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) B1775297
theorem B2243965 : Blo 366759 2243965 := bstep (se 3 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 2243965 = 841487) B841487
theorem B1064545 : Blo 366759 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B441979 : Blo 366759 441979 := bstep (se 1 (by rfl) ⟨331484, by rfl⟩ : syracuseStep 441979 = 662969) B662969
theorem B933515 : Blo 366759 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B1425181 : Blo 366759 1425181 := bstep (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) B534443
theorem B933727 : Blo 366759 933727 := bstep (se 1 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 933727 = 1400591) B1400591
theorem B4210703 : Blo 366759 4210703 := bstep (se 1 (by rfl) ⟨3158027, by rfl⟩ : syracuseStep 4210703 = 6316055) B6316055
theorem B999503 : Blo 366759 999503 := bstep (se 1 (by rfl) ⟨749627, by rfl⟩ : syracuseStep 999503 = 1499255) B1499255
theorem B1392983 : Blo 366759 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B934649 : Blo 366759 934649 := bstep (se 2 (by rfl) ⟨350493, by rfl⟩ : syracuseStep 934649 = 700987) B700987
theorem B935297 : Blo 366759 935297 := bstep (se 2 (by rfl) ⟨350736, by rfl⟩ : syracuseStep 935297 = 701473) B701473
theorem B443983 : Blo 366759 443983 := bstep (se 1 (by rfl) ⟨332987, by rfl⟩ : syracuseStep 443983 = 665975) B665975
theorem B1394273 : Blo 366759 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B6473861 : Blo 366759 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B936107 : Blo 366759 936107 := bstep (se 1 (by rfl) ⟨702080, by rfl⟩ : syracuseStep 936107 = 1404161) B1404161
theorem B1329787 : Blo 366759 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B1067735 : Blo 366759 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B1330103 : Blo 366759 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B936967 : Blo 366759 936967 := bstep (se 1 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 936967 = 1405451) B1405451
theorem B1395731 : Blo 366759 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B413023 : Blo 366759 413023 := bstep (se 1 (by rfl) ⟨309767, by rfl⟩ : syracuseStep 413023 = 619535) B619535
theorem B1396187 : Blo 366759 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B4181543 : Blo 366759 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B27053669 : Blo 366759 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B937595 : Blo 366759 937595 := bstep (se 1 (by rfl) ⟨703196, by rfl⟩ : syracuseStep 937595 = 1406393) B1406393
theorem B413383 : Blo 366759 413383 := bstep (se 1 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 413383 = 620075) B620075
theorem B479083 : Blo 366759 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B937889 : Blo 366759 937889 := bstep (se 2 (by rfl) ⟨351708, by rfl⟩ : syracuseStep 937889 = 703417) B703417
theorem B1200527 : Blo 366759 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B414247 : Blo 366759 414247 := bstep (se 1 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 414247 = 621371) B621371
theorem B1397371 : Blo 366759 1397371 := bstep (se 1 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 1397371 = 2096057) B2096057
theorem B5690387 : Blo 366759 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B2249975 : Blo 366759 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B1005095 : Blo 366759 1005095 := bstep (se 1 (by rfl) ⟨753821, by rfl⟩ : syracuseStep 1005095 = 1507643) B1507643
theorem B4216535 : Blo 366759 4216535 := bstep (se 1 (by rfl) ⟨3162401, by rfl⟩ : syracuseStep 4216535 = 6324803) B6324803
theorem B1398647 : Blo 366759 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1496951 : Blo 366759 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B415867 : Blo 366759 415867 := bstep (se 1 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 415867 = 623801) B623801
theorem B3004733 : Blo 366759 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B1333793 : Blo 366759 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B416335 : Blo 366759 416335 := bstep (se 1 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 416335 = 624503) B624503
theorem B842363 : Blo 366759 842363 := bstep (se 1 (by rfl) ⟨631772, by rfl⟩ : syracuseStep 842363 = 1263545) B1263545
theorem B1399619 : Blo 366759 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B711607 : Blo 366759 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B416731 : Blo 366759 416731 := bstep (se 1 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 416731 = 625097) B625097
theorem B1596611 : Blo 366759 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B2809079 : Blo 366759 2809079 := bstep (se 1 (by rfl) ⟨2106809, by rfl⟩ : syracuseStep 2809079 = 4213619) B4213619
theorem B1400075 : Blo 366759 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1859111 : Blo 366759 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B1990291 : Blo 366759 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B2809565 : Blo 366759 2809565 := bstep (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) B1053587
theorem B2350943 : Blo 366759 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B1400759 : Blo 366759 1400759 := bstep (se 1 (by rfl) ⟨1050569, by rfl⟩ : syracuseStep 1400759 = 2101139) B2101139
theorem B1794163 : Blo 366759 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1335467 : Blo 366759 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B4219451 : Blo 366759 4219451 := bstep (se 1 (by rfl) ⟨3164588, by rfl⟩ : syracuseStep 4219451 = 6329177) B6329177
theorem B1401533 : Blo 366759 1401533 := bstep (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) B525575
theorem B844499 : Blo 366759 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B2352017 : Blo 366759 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B1336247 : Blo 366759 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B2974799 : Blo 366759 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B1402217 : Blo 366759 1402217 := bstep (se 2 (by rfl) ⟨525831, by rfl⟩ : syracuseStep 1402217 = 1051663) B1051663
theorem B550319 : Blo 366759 550319 := bstep (se 1 (by rfl) ⟨412739, by rfl⟩ : syracuseStep 550319 = 825479) B825479
theorem B2123227 : Blo 366759 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B550409 : Blo 366759 550409 := bstep (se 2 (by rfl) ⟨206403, by rfl⟩ : syracuseStep 550409 = 412807) B412807
theorem B550439 : Blo 366759 550439 := bstep (se 1 (by rfl) ⟨412829, by rfl⟩ : syracuseStep 550439 = 825659) B825659
theorem B1861217 : Blo 366759 1861217 := bstep (se 2 (by rfl) ⟨697956, by rfl⟩ : syracuseStep 1861217 = 1395913) B1395913
theorem B1238651 : Blo 366759 1238651 := bstep (se 1 (by rfl) ⟨928988, by rfl⟩ : syracuseStep 1238651 = 1857977) B1857977
theorem B550523 : Blo 366759 550523 := bstep (se 1 (by rfl) ⟨412892, by rfl⟩ : syracuseStep 550523 = 825785) B825785
theorem B550649 : Blo 366759 550649 := bstep (se 2 (by rfl) ⟨206493, by rfl⟩ : syracuseStep 550649 = 412987) B412987
theorem B1238813 : Blo 366759 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B1763167 : Blo 366759 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B550751 : Blo 366759 550751 := bstep (se 1 (by rfl) ⟨413063, by rfl⟩ : syracuseStep 550751 = 826127) B826127
theorem B550763 : Blo 366759 550763 := bstep (se 1 (by rfl) ⟨413072, by rfl⟩ : syracuseStep 550763 = 826145) B826145
theorem B747527 : Blo 366759 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B550991 : Blo 366759 550991 := bstep (se 1 (by rfl) ⟨413243, by rfl⟩ : syracuseStep 550991 = 826487) B826487
theorem B1271965 : Blo 366759 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B551111 : Blo 366759 551111 := bstep (se 1 (by rfl) ⟨413333, by rfl⟩ : syracuseStep 551111 = 826667) B826667
theorem B551273 : Blo 366759 551273 := bstep (se 2 (by rfl) ⟨206727, by rfl⟩ : syracuseStep 551273 = 413455) B413455
theorem B551351 : Blo 366759 551351 := bstep (se 1 (by rfl) ⟨413513, by rfl⟩ : syracuseStep 551351 = 827027) B827027
theorem B1239515 : Blo 366759 1239515 := bstep (se 1 (by rfl) ⟨929636, by rfl⟩ : syracuseStep 1239515 = 1859273) B1859273
theorem B551387 : Blo 366759 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B682553 : Blo 366759 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B551855 : Blo 366759 551855 := bstep (se 1 (by rfl) ⟨413891, by rfl⟩ : syracuseStep 551855 = 827783) B827783
theorem B551945 : Blo 366759 551945 := bstep (se 2 (by rfl) ⟨206979, by rfl⟩ : syracuseStep 551945 = 413959) B413959
theorem B1862675 : Blo 366759 1862675 := bstep (se 1 (by rfl) ⟨1397006, by rfl⟩ : syracuseStep 1862675 = 2794013) B2794013
theorem B551975 : Blo 366759 551975 := bstep (se 1 (by rfl) ⟨413981, by rfl⟩ : syracuseStep 551975 = 827963) B827963
theorem B5303339 : Blo 366759 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B552059 : Blo 366759 552059 := bstep (se 1 (by rfl) ⟨414044, by rfl⟩ : syracuseStep 552059 = 828089) B828089
theorem B1240217 : Blo 366759 1240217 := bstep (se 2 (by rfl) ⟨465081, by rfl⟩ : syracuseStep 1240217 = 930163) B930163
theorem B552185 : Blo 366759 552185 := bstep (se 2 (by rfl) ⟨207069, by rfl⟩ : syracuseStep 552185 = 414139) B414139
theorem B552287 : Blo 366759 552287 := bstep (se 1 (by rfl) ⟨414215, by rfl⟩ : syracuseStep 552287 = 828431) B828431
theorem B552299 : Blo 366759 552299 := bstep (se 1 (by rfl) ⟨414224, by rfl⟩ : syracuseStep 552299 = 828449) B828449
theorem B1404449 : Blo 366759 1404449 := bstep (se 2 (by rfl) ⟨526668, by rfl⟩ : syracuseStep 1404449 = 1053337) B1053337
theorem B552527 : Blo 366759 552527 := bstep (se 1 (by rfl) ⟨414395, by rfl⟩ : syracuseStep 552527 = 828791) B828791
theorem B1175239 : Blo 366759 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B552647 : Blo 366759 552647 := bstep (se 1 (by rfl) ⟨414485, by rfl⟩ : syracuseStep 552647 = 828971) B828971
theorem B552809 : Blo 366759 552809 := bstep (se 2 (by rfl) ⟨207303, by rfl⟩ : syracuseStep 552809 = 414607) B414607
theorem B1044407 : Blo 366759 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B552887 : Blo 366759 552887 := bstep (se 1 (by rfl) ⟨414665, by rfl⟩ : syracuseStep 552887 = 829331) B829331
theorem B552923 : Blo 366759 552923 := bstep (se 1 (by rfl) ⟨414692, by rfl⟩ : syracuseStep 552923 = 829385) B829385
theorem B1404935 : Blo 366759 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B5337251 : Blo 366759 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B2093323 : Blo 366759 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B3141899 : Blo 366759 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B1241405 : Blo 366759 1241405 := bstep (se 3 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 1241405 = 465527) B465527
theorem B1995137 : Blo 366759 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B553391 : Blo 366759 553391 := bstep (se 1 (by rfl) ⟨415043, by rfl⟩ : syracuseStep 553391 = 830087) B830087
theorem B1405421 : Blo 366759 1405421 := bstep (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) B527033
theorem B619015 : Blo 366759 619015 := bstep (se 1 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 619015 = 928523) B928523
theorem B553481 : Blo 366759 553481 := bstep (se 2 (by rfl) ⟨207555, by rfl⟩ : syracuseStep 553481 = 415111) B415111
theorem B553511 : Blo 366759 553511 := bstep (se 1 (by rfl) ⟨415133, by rfl⟩ : syracuseStep 553511 = 830267) B830267
theorem B553595 : Blo 366759 553595 := bstep (se 1 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 553595 = 830393) B830393
theorem B553721 : Blo 366759 553721 := bstep (se 2 (by rfl) ⟨207645, by rfl⟩ : syracuseStep 553721 = 415291) B415291
theorem B553823 : Blo 366759 553823 := bstep (se 1 (by rfl) ⟨415367, by rfl⟩ : syracuseStep 553823 = 830735) B830735
theorem B553835 : Blo 366759 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B619447 : Blo 366759 619447 := bstep (se 1 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 619447 = 929171) B929171
theorem B1569719 : Blo 366759 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B1045523 : Blo 366759 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B554063 : Blo 366759 554063 := bstep (se 1 (by rfl) ⟨415547, by rfl⟩ : syracuseStep 554063 = 831095) B831095
theorem B619643 : Blo 366759 619643 := bstep (se 1 (by rfl) ⟨464732, by rfl⟩ : syracuseStep 619643 = 929465) B929465
theorem B1406105 : Blo 366759 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B1242269 : Blo 366759 1242269 := bstep (se 3 (by rfl) ⟨232925, by rfl⟩ : syracuseStep 1242269 = 465851) B465851
theorem B2225323 : Blo 366759 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B554183 : Blo 366759 554183 := bstep (se 1 (by rfl) ⟨415637, by rfl⟩ : syracuseStep 554183 = 831275) B831275
theorem B1045865 : Blo 366759 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B554345 : Blo 366759 554345 := bstep (se 2 (by rfl) ⟨207879, by rfl⟩ : syracuseStep 554345 = 415759) B415759
theorem B7533971 : Blo 366759 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B2651555 : Blo 366759 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B2815397 : Blo 366759 2815397 := bstep (se 4 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 2815397 = 527887) B527887
theorem B554423 : Blo 366759 554423 := bstep (se 1 (by rfl) ⟨415817, by rfl⟩ : syracuseStep 554423 = 831635) B831635
theorem B1045979 : Blo 366759 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B554459 : Blo 366759 554459 := bstep (se 1 (by rfl) ⟨415844, by rfl⟩ : syracuseStep 554459 = 831689) B831689
theorem B4191749 : Blo 366759 4191749 := bstep (se 4 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 4191749 = 785953) B785953
theorem B620041 : Blo 366759 620041 := bstep (se 2 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 620041 = 465031) B465031
theorem B620203 : Blo 366759 620203 := bstep (se 1 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 620203 = 930305) B930305
theorem B1242809 : Blo 366759 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B2094781 : Blo 366759 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B751315 : Blo 366759 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B10385189 : Blo 366759 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B5994283 : Blo 366759 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1865591 : Blo 366759 1865591 := bstep (se 1 (by rfl) ⟨1399193, by rfl⟩ : syracuseStep 1865591 = 2798387) B2798387
theorem B554927 : Blo 366759 554927 := bstep (se 1 (by rfl) ⟨416195, by rfl⟩ : syracuseStep 554927 = 832391) B832391
theorem B620507 : Blo 366759 620507 := bstep (se 1 (by rfl) ⟨465380, by rfl⟩ : syracuseStep 620507 = 930761) B930761
theorem B555017 : Blo 366759 555017 := bstep (se 2 (by rfl) ⟨208131, by rfl⟩ : syracuseStep 555017 = 416263) B416263
theorem B555047 : Blo 366759 555047 := bstep (se 1 (by rfl) ⟨416285, by rfl⟩ : syracuseStep 555047 = 832571) B832571
theorem B1407091 : Blo 366759 1407091 := bstep (se 1 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 1407091 = 2110637) B2110637
theorem B555131 : Blo 366759 555131 := bstep (se 1 (by rfl) ⟨416348, by rfl⟩ : syracuseStep 555131 = 832697) B832697
theorem B620743 : Blo 366759 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B555257 : Blo 366759 555257 := bstep (se 2 (by rfl) ⟨208221, by rfl⟩ : syracuseStep 555257 = 416443) B416443
theorem B1243403 : Blo 366759 1243403 := bstep (se 1 (by rfl) ⟨932552, by rfl⟩ : syracuseStep 1243403 = 1865105) B1865105
theorem B555359 : Blo 366759 555359 := bstep (se 1 (by rfl) ⟨416519, by rfl⟩ : syracuseStep 555359 = 833039) B833039
theorem B620905 : Blo 366759 620905 := bstep (se 2 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 620905 = 465679) B465679
theorem B555371 : Blo 366759 555371 := bstep (se 1 (by rfl) ⟨416528, by rfl⟩ : syracuseStep 555371 = 833057) B833057
theorem B2357707 : Blo 366759 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B1243673 : Blo 366759 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B555599 : Blo 366759 555599 := bstep (se 1 (by rfl) ⟨416699, by rfl⟩ : syracuseStep 555599 = 833399) B833399
theorem B1047163 : Blo 366759 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B555719 : Blo 366759 555719 := bstep (se 1 (by rfl) ⟨416789, by rfl⟩ : syracuseStep 555719 = 833579) B833579
theorem B1047289 : Blo 366759 1047289 := bstep (se 2 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 1047289 = 785467) B785467
theorem B523103 : Blo 366759 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B555881 : Blo 366759 555881 := bstep (se 2 (by rfl) ⟨208455, by rfl⟩ : syracuseStep 555881 = 416911) B416911
theorem B4193207 : Blo 366759 4193207 := bstep (se 1 (by rfl) ⟨3144905, by rfl⟩ : syracuseStep 4193207 = 6289811) B6289811
theorem B555959 : Blo 366759 555959 := bstep (se 1 (by rfl) ⟨416969, by rfl⟩ : syracuseStep 555959 = 833939) B833939
theorem B621499 : Blo 366759 621499 := bstep (se 1 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 621499 = 932249) B932249
theorem B555995 : Blo 366759 555995 := bstep (se 1 (by rfl) ⟨416996, by rfl⟩ : syracuseStep 555995 = 833993) B833993
theorem B621607 : Blo 366759 621607 := bstep (se 1 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 621607 = 932411) B932411
theorem B523513 : Blo 366759 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B621931 : Blo 366759 621931 := bstep (se 1 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 621931 = 932897) B932897
theorem B2981285 : Blo 366759 2981285 := bstep (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) B558991
theorem B523855 : Blo 366759 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B1244807 : Blo 366759 1244807 := bstep (se 1 (by rfl) ⟨933605, by rfl⟩ : syracuseStep 1244807 = 1867211) B1867211
theorem B1244861 : Blo 366759 1244861 := bstep (se 3 (by rfl) ⟨233411, by rfl⟩ : syracuseStep 1244861 = 466823) B466823
theorem B589511 : Blo 366759 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B1048393 : Blo 366759 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B1245023 : Blo 366759 1245023 := bstep (se 1 (by rfl) ⟨933767, by rfl⟩ : syracuseStep 1245023 = 1867535) B1867535
theorem B2392217 : Blo 366759 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B623099 : Blo 366759 623099 := bstep (se 1 (by rfl) ⟨467324, by rfl⟩ : syracuseStep 623099 = 934649) B934649
theorem B3146273 : Blo 366759 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B7078499 : Blo 366759 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B787115 : Blo 366759 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B524983 : Blo 366759 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B4653883 : Blo 366759 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B3769249 : Blo 366759 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B623531 : Blo 366759 623531 := bstep (se 1 (by rfl) ⟨467648, by rfl⟩ : syracuseStep 623531 = 935297) B935297
theorem B3802087 : Blo 366759 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B591067 : Blo 366759 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B55248277 : Blo 366759 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B624071 : Blo 366759 624071 := bstep (se 1 (by rfl) ⟨468053, by rfl⟩ : syracuseStep 624071 = 936107) B936107
theorem B1574761 : Blo 366759 1574761 := bstep (se 2 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 1574761 = 1181071) B1181071
theorem B886735 : Blo 366759 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B591823 : Blo 366759 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B1247183 : Blo 366759 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B886889 : Blo 366759 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B526441 : Blo 366759 526441 := bstep (se 2 (by rfl) ⟨197415, by rfl⟩ : syracuseStep 526441 = 394831) B394831
theorem B591977 : Blo 366759 591977 := bstep (se 2 (by rfl) ⟨221991, by rfl⟩ : syracuseStep 591977 = 443983) B443983
theorem B2787695 : Blo 366759 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B625063 : Blo 366759 625063 := bstep (se 1 (by rfl) ⟨468797, by rfl⟩ : syracuseStep 625063 = 937595) B937595
theorem B625225 : Blo 366759 625225 := bstep (se 2 (by rfl) ⟨234459, by rfl⟩ : syracuseStep 625225 = 468919) B468919
theorem B625259 : Blo 366759 625259 := bstep (se 1 (by rfl) ⟨468944, by rfl⟩ : syracuseStep 625259 = 937889) B937889
theorem B1248155 : Blo 366759 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B5999933 : Blo 366759 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B1052153 : Blo 366759 1052153 := bstep (se 2 (by rfl) ⟨394557, by rfl⟩ : syracuseStep 1052153 = 789115) B789115
theorem B1773049 : Blo 366759 1773049 := bstep (se 2 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 1773049 = 1329787) B1329787
theorem B790327 : Blo 366759 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1249181 : Blo 366759 1249181 := bstep (se 3 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 1249181 = 468443) B468443
theorem B1249289 : Blo 366759 1249289 := bstep (se 2 (by rfl) ⟨468483, by rfl⟩ : syracuseStep 1249289 = 936967) B936967
theorem B561575 : Blo 366759 561575 := bstep (se 1 (by rfl) ⟨421181, by rfl⟩ : syracuseStep 561575 = 842363) B842363
theorem B1708489 : Blo 366759 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B1872719 : Blo 366759 1872719 := bstep (se 1 (by rfl) ⟨1404539, by rfl⟩ : syracuseStep 1872719 = 2809079) B2809079
theorem B1873043 : Blo 366759 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B3020165 : Blo 366759 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B890311 : Blo 366759 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B2791097 : Blo 366759 2791097 := bstep (se 2 (by rfl) ⟨1046661, by rfl⟩ : syracuseStep 2791097 = 2093323) B2093323
theorem B562999 : Blo 366759 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B890831 : Blo 366759 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B825353 : Blo 366759 825353 := bstep (se 2 (by rfl) ⟨309507, by rfl⟩ : syracuseStep 825353 = 619015) B619015
theorem B26941571 : Blo 366759 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B11868389 : Blo 366759 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B3545369 : Blo 366759 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B366879 : Blo 366759 366879 := bstep (se 1 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 366879 = 550319) B550319
theorem B366939 : Blo 366759 366939 := bstep (se 1 (by rfl) ⟨275204, by rfl⟩ : syracuseStep 366939 = 550409) B550409
theorem B366959 : Blo 366759 366959 := bstep (se 1 (by rfl) ⟨275219, by rfl⟩ : syracuseStep 366959 = 550439) B550439
theorem B825767 : Blo 366759 825767 := bstep (se 1 (by rfl) ⟨619325, by rfl⟩ : syracuseStep 825767 = 1238651) B1238651
theorem B367015 : Blo 366759 367015 := bstep (se 1 (by rfl) ⟨275261, by rfl⟩ : syracuseStep 367015 = 550523) B550523
theorem B367099 : Blo 366759 367099 := bstep (se 1 (by rfl) ⟨275324, by rfl⟩ : syracuseStep 367099 = 550649) B550649
theorem B2103803 : Blo 366759 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B825875 : Blo 366759 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B367167 : Blo 366759 367167 := bstep (se 1 (by rfl) ⟨275375, by rfl⟩ : syracuseStep 367167 = 550751) B550751
theorem B367175 : Blo 366759 367175 := bstep (se 1 (by rfl) ⟨275381, by rfl⟩ : syracuseStep 367175 = 550763) B550763
theorem B825929 : Blo 366759 825929 := bstep (se 2 (by rfl) ⟨309723, by rfl⟩ : syracuseStep 825929 = 619447) B619447
theorem B2792069 : Blo 366759 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B465583 : Blo 366759 465583 := bstep (se 1 (by rfl) ⟨349187, by rfl⟩ : syracuseStep 465583 = 698375) B698375
theorem B367327 : Blo 366759 367327 := bstep (se 1 (by rfl) ⟨275495, by rfl⟩ : syracuseStep 367327 = 550991) B550991
theorem B367407 : Blo 366759 367407 := bstep (se 1 (by rfl) ⟨275555, by rfl⟩ : syracuseStep 367407 = 551111) B551111
theorem B367515 : Blo 366759 367515 := bstep (se 1 (by rfl) ⟨275636, by rfl⟩ : syracuseStep 367515 = 551273) B551273
theorem B367567 : Blo 366759 367567 := bstep (se 1 (by rfl) ⟨275675, by rfl⟩ : syracuseStep 367567 = 551351) B551351
theorem B826343 : Blo 366759 826343 := bstep (se 1 (by rfl) ⟨619757, by rfl⟩ : syracuseStep 826343 = 1239515) B1239515
theorem B367591 : Blo 366759 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B367903 : Blo 366759 367903 := bstep (se 1 (by rfl) ⟨275927, by rfl⟩ : syracuseStep 367903 = 551855) B551855
theorem B367963 : Blo 366759 367963 := bstep (se 1 (by rfl) ⟨275972, by rfl⟩ : syracuseStep 367963 = 551945) B551945
theorem B826721 : Blo 366759 826721 := bstep (se 2 (by rfl) ⟨310020, by rfl⟩ : syracuseStep 826721 = 620041) B620041
theorem B367983 : Blo 366759 367983 := bstep (se 1 (by rfl) ⟨275987, by rfl⟩ : syracuseStep 367983 = 551975) B551975
theorem B1580417 : Blo 366759 1580417 := bstep (se 2 (by rfl) ⟨592656, by rfl⟩ : syracuseStep 1580417 = 1185313) B1185313
theorem B368039 : Blo 366759 368039 := bstep (se 1 (by rfl) ⟨276029, by rfl⟩ : syracuseStep 368039 = 552059) B552059
theorem B826811 : Blo 366759 826811 := bstep (se 1 (by rfl) ⟨620108, by rfl⟩ : syracuseStep 826811 = 1240217) B1240217
theorem B368123 : Blo 366759 368123 := bstep (se 1 (by rfl) ⟨276092, by rfl⟩ : syracuseStep 368123 = 552185) B552185
theorem B826937 : Blo 366759 826937 := bstep (se 2 (by rfl) ⟨310101, by rfl⟩ : syracuseStep 826937 = 620203) B620203
theorem B368191 : Blo 366759 368191 := bstep (se 1 (by rfl) ⟨276143, by rfl⟩ : syracuseStep 368191 = 552287) B552287
theorem B368199 : Blo 366759 368199 := bstep (se 1 (by rfl) ⟨276149, by rfl⟩ : syracuseStep 368199 = 552299) B552299
theorem B2793041 : Blo 366759 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B368351 : Blo 366759 368351 := bstep (se 1 (by rfl) ⟨276263, by rfl⟩ : syracuseStep 368351 = 552527) B552527
theorem B368431 : Blo 366759 368431 := bstep (se 1 (by rfl) ⟨276323, by rfl⟩ : syracuseStep 368431 = 552647) B552647
theorem B368539 : Blo 366759 368539 := bstep (se 1 (by rfl) ⟨276404, by rfl⟩ : syracuseStep 368539 = 552809) B552809
theorem B696271 : Blo 366759 696271 := bstep (se 1 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 696271 = 1044407) B1044407
theorem B368591 : Blo 366759 368591 := bstep (se 1 (by rfl) ⟨276443, by rfl⟩ : syracuseStep 368591 = 552887) B552887
theorem B368615 : Blo 366759 368615 := bstep (se 1 (by rfl) ⟨276461, by rfl⟩ : syracuseStep 368615 = 552923) B552923
theorem B1581065 : Blo 366759 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B1876121 : Blo 366759 1876121 := bstep (se 2 (by rfl) ⟨703545, by rfl⟩ : syracuseStep 1876121 = 1407091) B1407091
theorem B827603 : Blo 366759 827603 := bstep (se 1 (by rfl) ⟨620702, by rfl⟩ : syracuseStep 827603 = 1241405) B1241405
theorem B827657 : Blo 366759 827657 := bstep (se 2 (by rfl) ⟨310371, by rfl⟩ : syracuseStep 827657 = 620743) B620743
theorem B368927 : Blo 366759 368927 := bstep (se 1 (by rfl) ⟨276695, by rfl⟩ : syracuseStep 368927 = 553391) B553391
theorem B368987 : Blo 366759 368987 := bstep (se 1 (by rfl) ⟨276740, by rfl⟩ : syracuseStep 368987 = 553481) B553481
theorem B369007 : Blo 366759 369007 := bstep (se 1 (by rfl) ⟨276755, by rfl⟩ : syracuseStep 369007 = 553511) B553511
theorem B369063 : Blo 366759 369063 := bstep (se 1 (by rfl) ⟨276797, by rfl⟩ : syracuseStep 369063 = 553595) B553595
theorem B827873 : Blo 366759 827873 := bstep (se 2 (by rfl) ⟨310452, by rfl⟩ : syracuseStep 827873 = 620905) B620905
theorem B369147 : Blo 366759 369147 := bstep (se 1 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 369147 = 553721) B553721
theorem B5677573 : Blo 366759 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B369215 : Blo 366759 369215 := bstep (se 1 (by rfl) ⟨276911, by rfl⟩ : syracuseStep 369215 = 553823) B553823
theorem B369223 : Blo 366759 369223 := bstep (se 1 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 369223 = 553835) B553835
theorem B467527 : Blo 366759 467527 := bstep (se 1 (by rfl) ⟨350645, by rfl⟩ : syracuseStep 467527 = 701291) B701291
theorem B631417 : Blo 366759 631417 := bstep (se 2 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 631417 = 473563) B473563
theorem B697015 : Blo 366759 697015 := bstep (se 1 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 697015 = 1045523) B1045523
theorem B13083353 : Blo 366759 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B369375 : Blo 366759 369375 := bstep (se 1 (by rfl) ⟨277031, by rfl⟩ : syracuseStep 369375 = 554063) B554063
theorem B828179 : Blo 366759 828179 := bstep (se 1 (by rfl) ⟨621134, by rfl⟩ : syracuseStep 828179 = 1242269) B1242269
theorem B369455 : Blo 366759 369455 := bstep (se 1 (by rfl) ⟨277091, by rfl⟩ : syracuseStep 369455 = 554183) B554183
theorem B3154747 : Blo 366759 3154747 := bstep (se 1 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 3154747 = 4732121) B4732121
theorem B697243 : Blo 366759 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B369563 : Blo 366759 369563 := bstep (se 1 (by rfl) ⟨277172, by rfl⟩ : syracuseStep 369563 = 554345) B554345
theorem B5022647 : Blo 366759 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B1876931 : Blo 366759 1876931 := bstep (se 1 (by rfl) ⟨1407698, by rfl⟩ : syracuseStep 1876931 = 2815397) B2815397
theorem B369615 : Blo 366759 369615 := bstep (se 1 (by rfl) ⟨277211, by rfl⟩ : syracuseStep 369615 = 554423) B554423
theorem B697319 : Blo 366759 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B369639 : Blo 366759 369639 := bstep (se 1 (by rfl) ⟨277229, by rfl⟩ : syracuseStep 369639 = 554459) B554459
theorem B2794499 : Blo 366759 2794499 := bstep (se 1 (by rfl) ⟨2095874, by rfl⟩ : syracuseStep 2794499 = 4191749) B4191749
theorem B6267941 : Blo 366759 6267941 := bstep (se 4 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 6267941 = 1175239) B1175239
theorem B828539 : Blo 366759 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B6923459 : Blo 366759 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B828665 : Blo 366759 828665 := bstep (se 2 (by rfl) ⟨310749, by rfl⟩ : syracuseStep 828665 = 621499) B621499
theorem B369951 : Blo 366759 369951 := bstep (se 1 (by rfl) ⟨277463, by rfl⟩ : syracuseStep 369951 = 554927) B554927
theorem B370011 : Blo 366759 370011 := bstep (se 1 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 370011 = 555017) B555017
theorem B370031 : Blo 366759 370031 := bstep (se 1 (by rfl) ⟨277523, by rfl⟩ : syracuseStep 370031 = 555047) B555047
theorem B828809 : Blo 366759 828809 := bstep (se 2 (by rfl) ⟨310803, by rfl⟩ : syracuseStep 828809 = 621607) B621607
theorem B370087 : Blo 366759 370087 := bstep (se 1 (by rfl) ⟨277565, by rfl⟩ : syracuseStep 370087 = 555131) B555131
theorem B370171 : Blo 366759 370171 := bstep (se 1 (by rfl) ⟨277628, by rfl⟩ : syracuseStep 370171 = 555257) B555257
theorem B828935 : Blo 366759 828935 := bstep (se 1 (by rfl) ⟨621701, by rfl⟩ : syracuseStep 828935 = 1243403) B1243403
theorem B370239 : Blo 366759 370239 := bstep (se 1 (by rfl) ⟨277679, by rfl⟩ : syracuseStep 370239 = 555359) B555359
theorem B370247 : Blo 366759 370247 := bstep (se 1 (by rfl) ⟨277685, by rfl⟩ : syracuseStep 370247 = 555371) B555371
theorem B829115 : Blo 366759 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B370399 : Blo 366759 370399 := bstep (se 1 (by rfl) ⟨277799, by rfl⟩ : syracuseStep 370399 = 555599) B555599
theorem B370479 : Blo 366759 370479 := bstep (se 1 (by rfl) ⟨277859, by rfl⟩ : syracuseStep 370479 = 555719) B555719
theorem B829241 : Blo 366759 829241 := bstep (se 2 (by rfl) ⟨310965, by rfl⟩ : syracuseStep 829241 = 621931) B621931
theorem B2991953 : Blo 366759 2991953 := bstep (se 2 (by rfl) ⟨1121982, by rfl⟩ : syracuseStep 2991953 = 2243965) B2243965
theorem B370587 : Blo 366759 370587 := bstep (se 1 (by rfl) ⟨277940, by rfl⟩ : syracuseStep 370587 = 555881) B555881
theorem B1910735 : Blo 366759 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B2795471 : Blo 366759 2795471 := bstep (se 1 (by rfl) ⟨2096603, by rfl⟩ : syracuseStep 2795471 = 4193207) B4193207
theorem B370639 : Blo 366759 370639 := bstep (se 1 (by rfl) ⟨277979, by rfl⟩ : syracuseStep 370639 = 555959) B555959
theorem B370663 : Blo 366759 370663 := bstep (se 1 (by rfl) ⟨277997, by rfl⟩ : syracuseStep 370663 = 555995) B555995
theorem B698473 : Blo 366759 698473 := bstep (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) B523855
theorem B3156083 : Blo 366759 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B1681661 : Blo 366759 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B829871 : Blo 366759 829871 := bstep (se 1 (by rfl) ⟨622403, by rfl⟩ : syracuseStep 829871 = 1244807) B1244807
theorem B829907 : Blo 366759 829907 := bstep (se 1 (by rfl) ⟨622430, by rfl⟩ : syracuseStep 829907 = 1244861) B1244861
theorem B830015 : Blo 366759 830015 := bstep (se 1 (by rfl) ⟨622511, by rfl⟩ : syracuseStep 830015 = 1245023) B1245023
theorem B830123 : Blo 366759 830123 := bstep (se 1 (by rfl) ⟨622592, by rfl⟩ : syracuseStep 830123 = 1245185) B1245185
theorem B666335 : Blo 366759 666335 := bstep (se 1 (by rfl) ⟨499751, by rfl⟩ : syracuseStep 666335 = 999503) B999503
theorem B928655 : Blo 366759 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B830663 : Blo 366759 830663 := bstep (se 1 (by rfl) ⟨622997, by rfl⟩ : syracuseStep 830663 = 1245995) B1245995
theorem B830843 : Blo 366759 830843 := bstep (se 1 (by rfl) ⟨623132, by rfl⟩ : syracuseStep 830843 = 1246265) B1246265
theorem B2796929 : Blo 366759 2796929 := bstep (se 2 (by rfl) ⟨1048848, by rfl⟩ : syracuseStep 2796929 = 2097697) B2097697
theorem B830969 : Blo 366759 830969 := bstep (se 2 (by rfl) ⟨311613, by rfl⟩ : syracuseStep 830969 = 623227) B623227
theorem B831059 : Blo 366759 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B929515 : Blo 366759 929515 := bstep (se 1 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 929515 = 1394273) B1394273
theorem B831239 : Blo 366759 831239 := bstep (se 1 (by rfl) ⟨623429, by rfl⟩ : syracuseStep 831239 = 1246859) B1246859
theorem B831851 : Blo 366759 831851 := bstep (se 1 (by rfl) ⟨623888, by rfl⟩ : syracuseStep 831851 = 1247777) B1247777
theorem B831995 : Blo 366759 831995 := bstep (se 1 (by rfl) ⟨623996, by rfl⟩ : syracuseStep 831995 = 1247993) B1247993
theorem B2830969 : Blo 366759 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B832121 : Blo 366759 832121 := bstep (se 2 (by rfl) ⟨312045, by rfl⟩ : syracuseStep 832121 = 624091) B624091
theorem B832175 : Blo 366759 832175 := bstep (se 1 (by rfl) ⟨624131, by rfl⟩ : syracuseStep 832175 = 1248263) B1248263
theorem B930487 : Blo 366759 930487 := bstep (se 1 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 930487 = 1395731) B1395731
theorem B832247 : Blo 366759 832247 := bstep (se 1 (by rfl) ⟨624185, by rfl⟩ : syracuseStep 832247 = 1248371) B1248371
theorem B832427 : Blo 366759 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B930791 : Blo 366759 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B18035779 : Blo 366759 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B3781847 : Blo 366759 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B832967 : Blo 366759 832967 := bstep (se 1 (by rfl) ⟨624725, by rfl⟩ : syracuseStep 832967 = 1249451) B1249451
theorem B800351 : Blo 366759 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B833327 : Blo 366759 833327 := bstep (se 1 (by rfl) ⟨624995, by rfl⟩ : syracuseStep 833327 = 1249991) B1249991
theorem B702263 : Blo 366759 702263 := bstep (se 1 (by rfl) ⟨526697, by rfl⟩ : syracuseStep 702263 = 1053395) B1053395
theorem B931945 : Blo 366759 931945 := bstep (se 2 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 931945 = 698959) B698959
theorem B670063 : Blo 366759 670063 := bstep (se 1 (by rfl) ⟨502547, by rfl⟩ : syracuseStep 670063 = 1005095) B1005095
theorem B833903 : Blo 366759 833903 := bstep (se 1 (by rfl) ⟨625427, by rfl⟩ : syracuseStep 833903 = 1250855) B1250855
theorem B833975 : Blo 366759 833975 := bstep (se 1 (by rfl) ⟨625481, by rfl⟩ : syracuseStep 833975 = 1250963) B1250963
theorem B702931 : Blo 366759 702931 := bstep (se 1 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 702931 = 1054397) B1054397
theorem B440903 : Blo 366759 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B834119 : Blo 366759 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B932431 : Blo 366759 932431 := bstep (se 1 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 932431 = 1398647) B1398647
theorem B997967 : Blo 366759 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B834155 : Blo 366759 834155 := bstep (se 1 (by rfl) ⟨625616, by rfl⟩ : syracuseStep 834155 = 1251233) B1251233
theorem B703151 : Blo 366759 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B2669431 : Blo 366759 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B933079 : Blo 366759 933079 := bstep (se 1 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 933079 = 1399619) B1399619
theorem B703721 : Blo 366759 703721 := bstep (se 2 (by rfl) ⟨263895, by rfl⟩ : syracuseStep 703721 = 527791) B527791
theorem B933383 : Blo 366759 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B1326701 : Blo 366759 1326701 := bstep (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) B497513
theorem B638777 : Blo 366759 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B933839 : Blo 366759 933839 := bstep (se 1 (by rfl) ⟨700379, by rfl⟩ : syracuseStep 933839 = 1400759) B1400759
theorem B4473137 : Blo 366759 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B934355 : Blo 366759 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B1983199 : Blo 366759 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B8012621 : Blo 366759 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B934811 : Blo 366759 934811 := bstep (se 1 (by rfl) ⟨701108, by rfl⟩ : syracuseStep 934811 = 1402217) B1402217
theorem B3556781 : Blo 366759 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B1820141 : Blo 366759 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B444079 : Blo 366759 444079 := bstep (se 1 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 444079 = 666119) B666119
theorem B935945 : Blo 366759 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B1394941 : Blo 366759 1394941 := bstep (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) B523103
theorem B1001753 : Blo 366759 1001753 := bstep (se 2 (by rfl) ⟨375657, by rfl⟩ : syracuseStep 1001753 = 751315) B751315
theorem B3164453 : Blo 366759 3164453 := bstep (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) B593335
theorem B936299 : Blo 366759 936299 := bstep (se 1 (by rfl) ⟨702224, by rfl⟩ : syracuseStep 936299 = 1404449) B1404449
theorem B936623 : Blo 366759 936623 := bstep (se 1 (by rfl) ⟨702467, by rfl⟩ : syracuseStep 936623 = 1404935) B1404935
theorem B3558167 : Blo 366759 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B1493903 : Blo 366759 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B1330091 : Blo 366759 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B936947 : Blo 366759 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B413095 : Blo 366759 413095 := bstep (se 1 (by rfl) ⟨309821, by rfl⟩ : syracuseStep 413095 = 619643) B619643
theorem B937403 : Blo 366759 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B2805191 : Blo 366759 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B1396217 : Blo 366759 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B1396385 : Blo 366759 1396385 := bstep (se 2 (by rfl) ⟨523644, by rfl⟩ : syracuseStep 1396385 = 1047289) B1047289
theorem B413671 : Blo 366759 413671 := bstep (se 1 (by rfl) ⟨310253, by rfl⟩ : syracuseStep 413671 = 620507) B620507
theorem B1987523 : Blo 366759 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B1397857 : Blo 366759 1397857 := bstep (se 2 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 1397857 = 1048393) B1048393
theorem B4773113 : Blo 366759 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B2807135 : Blo 366759 2807135 := bstep (se 1 (by rfl) ⟨2105351, by rfl⟩ : syracuseStep 2807135 = 4210703) B4210703
theorem B1857005 : Blo 366759 1857005 := bstep (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) B696377
theorem B1398329 : Blo 366759 1398329 := bstep (se 2 (by rfl) ⟨524373, by rfl⟩ : syracuseStep 1398329 = 1048747) B1048747
theorem B415327 : Blo 366759 415327 := bstep (se 1 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 415327 = 622991) B622991
theorem B2021021 : Blo 366759 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B1857815 : Blo 366759 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B416479 : Blo 366759 416479 := bstep (se 1 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 416479 = 624719) B624719
theorem B4315907 : Blo 366759 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B711823 : Blo 366759 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B417055 : Blo 366759 417055 := bstep (se 1 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 417055 = 625583) B625583
theorem B941831 : Blo 366759 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B2350889 : Blo 366759 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B4185917 : Blo 366759 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B1859435 : Blo 366759 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B1695953 : Blo 366759 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B3793591 : Blo 366759 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B7070813 : Blo 366759 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B2811023 : Blo 366759 2811023 := bstep (se 1 (by rfl) ⟨2108267, by rfl⟩ : syracuseStep 2811023 = 4216535) B4216535
theorem B550175 : Blo 366759 550175 := bstep (se 1 (by rfl) ⟨412631, by rfl⟩ : syracuseStep 550175 = 825263) B825263
theorem B1992023 : Blo 366759 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B550343 : Blo 366759 550343 := bstep (se 1 (by rfl) ⟨412757, by rfl⟩ : syracuseStep 550343 = 825515) B825515
theorem B6383393 : Blo 366759 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B550697 : Blo 366759 550697 := bstep (se 2 (by rfl) ⟨206511, by rfl⟩ : syracuseStep 550697 = 413023) B413023
theorem B550703 : Blo 366759 550703 := bstep (se 1 (by rfl) ⟨413027, by rfl⟩ : syracuseStep 550703 = 826055) B826055
theorem B4417361 : Blo 366759 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B4220909 : Blo 366759 4220909 := bstep (se 3 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 4220909 = 1582841) B1582841
theorem B551177 : Blo 366759 551177 := bstep (se 2 (by rfl) ⟨206691, by rfl⟩ : syracuseStep 551177 = 413383) B413383
theorem B1239407 : Blo 366759 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B551279 : Blo 366759 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B22932013 : Blo 366759 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B1567295 : Blo 366759 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B551495 : Blo 366759 551495 := bstep (se 1 (by rfl) ⟨413621, by rfl⟩ : syracuseStep 551495 = 827243) B827243
theorem B551531 : Blo 366759 551531 := bstep (se 1 (by rfl) ⟨413648, by rfl⟩ : syracuseStep 551531 = 827297) B827297
theorem B1993405 : Blo 366759 1993405 := bstep (se 3 (by rfl) ⟨373763, by rfl⟩ : syracuseStep 1993405 = 747527) B747527
theorem B551759 : Blo 366759 551759 := bstep (se 1 (by rfl) ⟨413819, by rfl⟩ : syracuseStep 551759 = 827639) B827639
theorem B2812967 : Blo 366759 2812967 := bstep (se 1 (by rfl) ⟨2109725, by rfl⟩ : syracuseStep 2812967 = 4219451) B4219451
theorem B552155 : Blo 366759 552155 := bstep (se 1 (by rfl) ⟨414116, by rfl⟩ : syracuseStep 552155 = 828233) B828233
theorem B1568011 : Blo 366759 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B683387 : Blo 366759 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B552329 : Blo 366759 552329 := bstep (se 2 (by rfl) ⟨207123, by rfl⟩ : syracuseStep 552329 = 414247) B414247
theorem B1863161 : Blo 366759 1863161 := bstep (se 2 (by rfl) ⟨698685, by rfl⟩ : syracuseStep 1863161 = 1397371) B1397371
theorem B12906161 : Blo 366759 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B1240811 : Blo 366759 1240811 := bstep (se 1 (by rfl) ⟨930608, by rfl⟩ : syracuseStep 1240811 = 1861217) B1861217
theorem B552683 : Blo 366759 552683 := bstep (se 1 (by rfl) ⟨414512, by rfl⟩ : syracuseStep 552683 = 829025) B829025
theorem B1863485 : Blo 366759 1863485 := bstep (se 3 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 1863485 = 698807) B698807
theorem B552911 : Blo 366759 552911 := bstep (se 1 (by rfl) ⟨414683, by rfl⟩ : syracuseStep 552911 = 829367) B829367
theorem B3993857 : Blo 366759 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B553307 : Blo 366759 553307 := bstep (se 1 (by rfl) ⟨414980, by rfl⟩ : syracuseStep 553307 = 829961) B829961
theorem B553535 : Blo 366759 553535 := bstep (se 1 (by rfl) ⟨415151, by rfl⟩ : syracuseStep 553535 = 830303) B830303
theorem B7959161 : Blo 366759 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B1241783 : Blo 366759 1241783 := bstep (se 1 (by rfl) ⟨931337, by rfl⟩ : syracuseStep 1241783 = 1862675) B1862675
theorem B553655 : Blo 366759 553655 := bstep (se 1 (by rfl) ⟨415241, by rfl⟩ : syracuseStep 553655 = 830483) B830483
theorem B3535559 : Blo 366759 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B619231 : Blo 366759 619231 := bstep (se 1 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 619231 = 928847) B928847
theorem B553883 : Blo 366759 553883 := bstep (se 1 (by rfl) ⟨415412, by rfl⟩ : syracuseStep 553883 = 830825) B830825
theorem B7992377 : Blo 366759 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B619663 : Blo 366759 619663 := bstep (se 1 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 619663 = 929495) B929495
theorem B554279 : Blo 366759 554279 := bstep (se 1 (by rfl) ⟨415709, by rfl⟩ : syracuseStep 554279 = 831419) B831419
theorem B554363 : Blo 366759 554363 := bstep (se 1 (by rfl) ⟨415772, by rfl⟩ : syracuseStep 554363 = 831545) B831545
theorem B619913 : Blo 366759 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B554489 : Blo 366759 554489 := bstep (se 2 (by rfl) ⟨207933, by rfl⟩ : syracuseStep 554489 = 415867) B415867
theorem B2094599 : Blo 366759 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B554591 : Blo 366759 554591 := bstep (se 1 (by rfl) ⟨415943, by rfl⟩ : syracuseStep 554591 = 831887) B831887
theorem B554807 : Blo 366759 554807 := bstep (se 1 (by rfl) ⟨416105, by rfl⟩ : syracuseStep 554807 = 832211) B832211
theorem B620345 : Blo 366759 620345 := bstep (se 2 (by rfl) ⟨232629, by rfl⟩ : syracuseStep 620345 = 465259) B465259
theorem B4257629 : Blo 366759 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B3143609 : Blo 366759 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B2357221 : Blo 366759 2357221 := bstep (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) B441979
theorem B555113 : Blo 366759 555113 := bstep (se 2 (by rfl) ⟨208167, by rfl⟩ : syracuseStep 555113 = 416335) B416335
theorem B555431 : Blo 366759 555431 := bstep (se 1 (by rfl) ⟨416573, by rfl⟩ : syracuseStep 555431 = 833147) B833147
theorem B555515 : Blo 366759 555515 := bstep (se 1 (by rfl) ⟨416636, by rfl⟩ : syracuseStep 555515 = 833273) B833273
theorem B3832343 : Blo 366759 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B2128447 : Blo 366759 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B1800767 : Blo 366759 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B948809 : Blo 366759 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B1243727 : Blo 366759 1243727 := bstep (se 1 (by rfl) ⟨932795, by rfl⟩ : syracuseStep 1243727 = 1865591) B1865591
theorem B555641 : Blo 366759 555641 := bstep (se 2 (by rfl) ⟨208365, by rfl⟩ : syracuseStep 555641 = 416731) B416731
theorem B555695 : Blo 366759 555695 := bstep (se 1 (by rfl) ⟨416771, by rfl⟩ : syracuseStep 555695 = 833543) B833543
theorem B555743 : Blo 366759 555743 := bstep (se 1 (by rfl) ⟨416807, by rfl⟩ : syracuseStep 555743 = 833615) B833615
theorem B1866563 : Blo 366759 1866563 := bstep (se 1 (by rfl) ⟨1399922, by rfl⟩ : syracuseStep 1866563 = 2799845) B2799845
theorem B621391 : Blo 366759 621391 := bstep (se 1 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 621391 = 932087) B932087
theorem B556007 : Blo 366759 556007 := bstep (se 1 (by rfl) ⟨417005, by rfl⟩ : syracuseStep 556007 = 834011) B834011
theorem B622073 : Blo 366759 622073 := bstep (se 2 (by rfl) ⟨233277, by rfl⟩ : syracuseStep 622073 = 466555) B466555
theorem B2653721 : Blo 366759 2653721 := bstep (se 2 (by rfl) ⟨995145, by rfl⟩ : syracuseStep 2653721 = 1990291) B1990291
theorem B1867373 : Blo 366759 1867373 := bstep (se 3 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 1867373 = 700265) B700265
theorem B1900241 : Blo 366759 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B622343 : Blo 366759 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B1244969 : Blo 366759 1244969 := bstep (se 2 (by rfl) ⟨466863, by rfl⟩ : syracuseStep 1244969 = 933727) B933727
theorem B393007 : Blo 366759 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B2982091 : Blo 366759 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B622903 : Blo 366759 622903 := bstep (se 1 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 622903 = 934355) B934355
theorem B2097515 : Blo 366759 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B4718999 : Blo 366759 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B5341747 : Blo 366759 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B623207 : Blo 366759 623207 := bstep (se 1 (by rfl) ⟨467405, by rfl⟩ : syracuseStep 623207 = 934811) B934811
theorem B7570097 : Blo 366759 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B623369 : Blo 366759 623369 := bstep (se 2 (by rfl) ⟨233763, by rfl⟩ : syracuseStep 623369 = 467527) B467527
theorem B1213427 : Blo 366759 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B623963 : Blo 366759 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B394651 : Blo 366759 394651 := bstep (se 1 (by rfl) ⟨295988, by rfl⟩ : syracuseStep 394651 = 591977) B591977
theorem B624199 : Blo 366759 624199 := bstep (se 1 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 624199 = 936299) B936299
theorem B2098973 : Blo 366759 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B624415 : Blo 366759 624415 := bstep (se 1 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 624415 = 936623) B936623
theorem B73664369 : Blo 366759 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B886727 : Blo 366759 886727 := bstep (se 1 (by rfl) ⟨665045, by rfl⟩ : syracuseStep 886727 = 1330091) B1330091
theorem B624631 : Blo 366759 624631 := bstep (se 1 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 624631 = 936947) B936947
theorem B3999955 : Blo 366759 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B592105 : Blo 366759 592105 := bstep (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) B444079
theorem B624935 : Blo 366759 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B1870127 : Blo 366759 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B2099681 : Blo 366759 2099681 := bstep (se 2 (by rfl) ⟨787380, by rfl⟩ : syracuseStep 2099681 = 1574761) B1574761
theorem B1182313 : Blo 366759 1182313 := bstep (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) B886735
theorem B789097 : Blo 366759 789097 := bstep (se 2 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 789097 = 591823) B591823
theorem B1248479 : Blo 366759 1248479 := bstep (se 1 (by rfl) ⟨936359, by rfl⟩ : syracuseStep 1248479 = 1872719) B1872719
theorem B30576017 : Blo 366759 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B1248695 : Blo 366759 1248695 := bstep (se 1 (by rfl) ⟨936521, by rfl⟩ : syracuseStep 1248695 = 1873043) B1873043
theorem B3182075 : Blo 366759 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B1871423 : Blo 366759 1871423 := bstep (se 1 (by rfl) ⟨1403567, by rfl⟩ : syracuseStep 1871423 = 2807135) B2807135
theorem B2657873 : Blo 366759 2657873 := bstep (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) B1993405
theorem B1347347 : Blo 366759 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B593887 : Blo 366759 593887 := bstep (se 1 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 593887 = 890831) B890831
theorem B17961047 : Blo 366759 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B2363579 : Blo 366759 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B2364065 : Blo 366759 2364065 := bstep (se 2 (by rfl) ⟨886524, by rfl⟩ : syracuseStep 2364065 = 1773049) B1773049
theorem B1053611 : Blo 366759 1053611 := bstep (se 1 (by rfl) ⟨790208, by rfl⟩ : syracuseStep 1053611 = 1580417) B1580417
theorem B627887 : Blo 366759 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B2790611 : Blo 366759 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B1054043 : Blo 366759 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1250747 : Blo 366759 1250747 := bstep (se 1 (by rfl) ⟨938060, by rfl⟩ : syracuseStep 1250747 = 1876121) B1876121
theorem B2365037 : Blo 366759 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B8722235 : Blo 366759 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B3348431 : Blo 366759 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B1251287 : Blo 366759 1251287 := bstep (se 1 (by rfl) ⟨938465, by rfl⟩ : syracuseStep 1251287 = 1876931) B1876931
theorem B464879 : Blo 366759 464879 := bstep (se 1 (by rfl) ⟨348659, by rfl⟩ : syracuseStep 464879 = 697319) B697319
theorem B1874015 : Blo 366759 1874015 := bstep (se 1 (by rfl) ⟨1405511, by rfl⟩ : syracuseStep 1874015 = 2811023) B2811023
theorem B366783 : Blo 366759 366783 := bstep (se 1 (by rfl) ⟨275087, by rfl⟩ : syracuseStep 366783 = 550175) B550175
theorem B825641 : Blo 366759 825641 := bstep (se 2 (by rfl) ⟨309615, by rfl⟩ : syracuseStep 825641 = 619231) B619231
theorem B366895 : Blo 366759 366895 := bstep (se 1 (by rfl) ⟨275171, by rfl⟩ : syracuseStep 366895 = 550343) B550343
theorem B3152357 : Blo 366759 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B367131 : Blo 366759 367131 := bstep (se 1 (by rfl) ⟨275348, by rfl⟩ : syracuseStep 367131 = 550697) B550697
theorem B367135 : Blo 366759 367135 := bstep (se 1 (by rfl) ⟨275351, by rfl⟩ : syracuseStep 367135 = 550703) B550703
theorem B2104055 : Blo 366759 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B367451 : Blo 366759 367451 := bstep (se 1 (by rfl) ⟨275588, by rfl⟩ : syracuseStep 367451 = 551177) B551177
theorem B826217 : Blo 366759 826217 := bstep (se 2 (by rfl) ⟨309831, by rfl⟩ : syracuseStep 826217 = 619663) B619663
theorem B2661245 : Blo 366759 2661245 := bstep (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) B997967
theorem B826271 : Blo 366759 826271 := bstep (se 1 (by rfl) ⟨619703, by rfl⟩ : syracuseStep 826271 = 1239407) B1239407
theorem B367519 : Blo 366759 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B367663 : Blo 366759 367663 := bstep (se 1 (by rfl) ⟨275747, by rfl⟩ : syracuseStep 367663 = 551495) B551495
theorem B367687 : Blo 366759 367687 := bstep (se 1 (by rfl) ⟨275765, by rfl⟩ : syracuseStep 367687 = 551531) B551531
theorem B367839 : Blo 366759 367839 := bstep (se 1 (by rfl) ⟨275879, by rfl⟩ : syracuseStep 367839 = 551759) B551759
theorem B1187081 : Blo 366759 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B11509085 : Blo 366759 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B1875311 : Blo 366759 1875311 := bstep (se 1 (by rfl) ⟨1406483, by rfl⟩ : syracuseStep 1875311 = 2812967) B2812967
theorem B368103 : Blo 366759 368103 := bstep (se 1 (by rfl) ⟨276077, by rfl⟩ : syracuseStep 368103 = 552155) B552155
theorem B368219 : Blo 366759 368219 := bstep (se 1 (by rfl) ⟨276164, by rfl⟩ : syracuseStep 368219 = 552329) B552329
theorem B14294677 : Blo 366759 14294677 := bstep (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) B670063
theorem B827207 : Blo 366759 827207 := bstep (se 1 (by rfl) ⟨620405, by rfl⟩ : syracuseStep 827207 = 1240811) B1240811
theorem B368455 : Blo 366759 368455 := bstep (se 1 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 368455 = 552683) B552683
theorem B368607 : Blo 366759 368607 := bstep (se 1 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 368607 = 552911) B552911
theorem B2662571 : Blo 366759 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B368871 : Blo 366759 368871 := bstep (se 1 (by rfl) ⟨276653, by rfl⟩ : syracuseStep 368871 = 553307) B553307
theorem B369023 : Blo 366759 369023 := bstep (se 1 (by rfl) ⟨276767, by rfl⟩ : syracuseStep 369023 = 553535) B553535
theorem B827855 : Blo 366759 827855 := bstep (se 1 (by rfl) ⟨620891, by rfl⟩ : syracuseStep 827855 = 1241783) B1241783
theorem B369103 : Blo 366759 369103 := bstep (se 1 (by rfl) ⟨276827, by rfl⟩ : syracuseStep 369103 = 553655) B553655
theorem B369255 : Blo 366759 369255 := bstep (se 1 (by rfl) ⟨276941, by rfl⟩ : syracuseStep 369255 = 553883) B553883
theorem B369519 : Blo 366759 369519 := bstep (se 1 (by rfl) ⟨277139, by rfl⟩ : syracuseStep 369519 = 554279) B554279
theorem B369575 : Blo 366759 369575 := bstep (se 1 (by rfl) ⟨277181, by rfl⟩ : syracuseStep 369575 = 554363) B554363
theorem B369659 : Blo 366759 369659 := bstep (se 1 (by rfl) ⟨277244, by rfl⟩ : syracuseStep 369659 = 554489) B554489
theorem B533567 : Blo 366759 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B369727 : Blo 366759 369727 := bstep (se 1 (by rfl) ⟨277295, by rfl⟩ : syracuseStep 369727 = 554591) B554591
theorem B828521 : Blo 366759 828521 := bstep (se 2 (by rfl) ⟨310695, by rfl⟩ : syracuseStep 828521 = 621391) B621391
theorem B369871 : Blo 366759 369871 := bstep (se 1 (by rfl) ⟨277403, by rfl⟩ : syracuseStep 369871 = 554807) B554807
theorem B468175 : Blo 366759 468175 := bstep (se 1 (by rfl) ⟨351131, by rfl⟩ : syracuseStep 468175 = 702263) B702263
theorem B370075 : Blo 366759 370075 := bstep (se 1 (by rfl) ⟨277556, by rfl⟩ : syracuseStep 370075 = 555113) B555113
theorem B370287 : Blo 366759 370287 := bstep (se 1 (by rfl) ⟨277715, by rfl⟩ : syracuseStep 370287 = 555431) B555431
theorem B370343 : Blo 366759 370343 := bstep (se 1 (by rfl) ⟨277757, by rfl⟩ : syracuseStep 370343 = 555515) B555515
theorem B632539 : Blo 366759 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B829151 : Blo 366759 829151 := bstep (se 1 (by rfl) ⟨621863, by rfl⟩ : syracuseStep 829151 = 1243727) B1243727
theorem B370427 : Blo 366759 370427 := bstep (se 1 (by rfl) ⟨277820, by rfl⟩ : syracuseStep 370427 = 555641) B555641
theorem B468767 : Blo 366759 468767 := bstep (se 1 (by rfl) ⟨351575, by rfl⟩ : syracuseStep 468767 = 703151) B703151
theorem B370463 : Blo 366759 370463 := bstep (se 1 (by rfl) ⟨277847, by rfl⟩ : syracuseStep 370463 = 555695) B555695
theorem B370495 : Blo 366759 370495 := bstep (se 1 (by rfl) ⟨277871, by rfl⟩ : syracuseStep 370495 = 555743) B555743
theorem B370671 : Blo 366759 370671 := bstep (se 1 (by rfl) ⟨278003, by rfl⟩ : syracuseStep 370671 = 556007) B556007
theorem B469147 : Blo 366759 469147 := bstep (se 1 (by rfl) ⟨351860, by rfl⟩ : syracuseStep 469147 = 703721) B703721
theorem B829979 : Blo 366759 829979 := bstep (se 1 (by rfl) ⟨622484, by rfl⟩ : syracuseStep 829979 = 1244969) B1244969
theorem B928361 : Blo 366759 928361 := bstep (se 2 (by rfl) ⟨348135, by rfl⟩ : syracuseStep 928361 = 696271) B696271
theorem B929353 : Blo 366759 929353 := bstep (se 2 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 929353 = 697015) B697015
theorem B699977 : Blo 366759 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B5058121 : Blo 366759 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B2371187 : Blo 366759 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B6205177 : Blo 366759 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B4206329 : Blo 366759 4206329 := bstep (se 2 (by rfl) ⟨1577373, by rfl⟩ : syracuseStep 4206329 = 3154747) B3154747
theorem B929657 : Blo 366759 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B5025665 : Blo 366759 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B831455 : Blo 366759 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B667835 : Blo 366759 667835 := bstep (se 1 (by rfl) ⟨500876, by rfl⟩ : syracuseStep 667835 = 1001753) B1001753
theorem B2109635 : Blo 366759 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B2372111 : Blo 366759 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B995935 : Blo 366759 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B832103 : Blo 366759 832103 := bstep (se 1 (by rfl) ⟨624077, by rfl⟩ : syracuseStep 832103 = 1248155) B1248155
theorem B930811 : Blo 366759 930811 := bstep (se 1 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 930811 = 1396217) B1396217
theorem B701435 : Blo 366759 701435 := bstep (se 1 (by rfl) ⟨526076, by rfl⟩ : syracuseStep 701435 = 1052153) B1052153
theorem B930923 : Blo 366759 930923 := bstep (se 1 (by rfl) ⟨698192, by rfl⟩ : syracuseStep 930923 = 1396385) B1396385
theorem B832787 : Blo 366759 832787 := bstep (se 1 (by rfl) ⟨624590, by rfl⟩ : syracuseStep 832787 = 1249181) B1249181
theorem B832859 : Blo 366759 832859 := bstep (se 1 (by rfl) ⟨624644, by rfl⟩ : syracuseStep 832859 = 1249289) B1249289
theorem B931297 : Blo 366759 931297 := bstep (se 2 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 931297 = 698473) B698473
theorem B701921 : Blo 366759 701921 := bstep (se 2 (by rfl) ⟨263220, by rfl⟩ : syracuseStep 701921 = 526441) B526441
theorem B833417 : Blo 366759 833417 := bstep (se 2 (by rfl) ⟨312531, by rfl⟩ : syracuseStep 833417 = 625063) B625063
theorem B1325015 : Blo 366759 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B833633 : Blo 366759 833633 := bstep (se 2 (by rfl) ⟨312612, by rfl⟩ : syracuseStep 833633 = 625225) B625225
theorem B2013443 : Blo 366759 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B932219 : Blo 366759 932219 := bstep (se 1 (by rfl) ⟨699164, by rfl⟩ : syracuseStep 932219 = 1398329) B1398329
theorem B7912259 : Blo 366759 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B1130635 : Blo 366759 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B2277985 : Blo 366759 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B4178627 : Blo 366759 4178627 := bstep (se 1 (by rfl) ⟨3133970, by rfl⟩ : syracuseStep 4178627 = 6267941) B6267941
theorem B1328015 : Blo 366759 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B444223 : Blo 366759 444223 := bstep (se 1 (by rfl) ⟨333167, by rfl⟩ : syracuseStep 444223 = 666335) B666335
theorem B20269237 : Blo 366759 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B8604107 : Blo 366759 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B937241 : Blo 366759 937241 := bstep (se 2 (by rfl) ⟨351465, by rfl⟩ : syracuseStep 937241 = 702931) B702931
theorem B5328251 : Blo 366759 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B2837929 : Blo 366759 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B413275 : Blo 366759 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B1396399 : Blo 366759 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B3559241 : Blo 366759 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B413563 : Blo 366759 413563 := bstep (se 1 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 413563 = 620345) B620345
theorem B2838419 : Blo 366759 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B4215077 : Blo 366759 4215077 := bstep (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) B790327
theorem B1200511 : Blo 366759 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B414715 : Blo 366759 414715 := bstep (se 1 (by rfl) ⟨311036, by rfl⟩ : syracuseStep 414715 = 622073) B622073
theorem B414895 : Blo 366759 414895 := bstep (se 1 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 414895 = 622343) B622343
theorem B1594811 : Blo 366759 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B415399 : Blo 366759 415399 := bstep (se 1 (by rfl) ⟨311549, by rfl⟩ : syracuseStep 415399 = 623099) B623099
theorem B415687 : Blo 366759 415687 := bstep (se 1 (by rfl) ⟨311765, by rfl⟩ : syracuseStep 415687 = 623531) B623531
theorem B841889 : Blo 366759 841889 := bstep (se 2 (by rfl) ⟨315708, by rfl⟩ : syracuseStep 841889 = 631417) B631417
theorem B2644265 : Blo 366759 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B416047 : Blo 366759 416047 := bstep (se 1 (by rfl) ⟨312035, by rfl⟩ : syracuseStep 416047 = 624071) B624071
theorem B1497533 : Blo 366759 1497533 := bstep (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) B561575
theorem B5069449 : Blo 366759 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B1858463 : Blo 366759 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B416839 : Blo 366759 416839 := bstep (se 1 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 416839 = 625259) B625259
theorem B1859921 : Blo 366759 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B10084925 : Blo 366759 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B15098501 : Blo 366759 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B1238003 : Blo 366759 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B1860731 : Blo 366759 1860731 := bstep (se 1 (by rfl) ⟨1395548, by rfl⟩ : syracuseStep 1860731 = 2791097) B2791097
theorem B550235 : Blo 366759 550235 := bstep (se 1 (by rfl) ⟨412676, by rfl⟩ : syracuseStep 550235 = 825353) B825353
theorem B1238543 : Blo 366759 1238543 := bstep (se 1 (by rfl) ⟨928907, by rfl⟩ : syracuseStep 1238543 = 1857815) B1857815
theorem B550511 : Blo 366759 550511 := bstep (se 1 (by rfl) ⟨412883, by rfl⟩ : syracuseStep 550511 = 825767) B825767
theorem B1402535 : Blo 366759 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B550583 : Blo 366759 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B2090681 : Blo 366759 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B550619 : Blo 366759 550619 := bstep (se 1 (by rfl) ⟨412964, by rfl⟩ : syracuseStep 550619 = 825929) B825929
theorem B1861379 : Blo 366759 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B550793 : Blo 366759 550793 := bstep (se 2 (by rfl) ⟨206547, by rfl⟩ : syracuseStep 550793 = 413095) B413095
theorem B550895 : Blo 366759 550895 := bstep (se 1 (by rfl) ⟨413171, by rfl⟩ : syracuseStep 550895 = 826343) B826343
theorem B551147 : Blo 366759 551147 := bstep (se 1 (by rfl) ⟨413360, by rfl⟩ : syracuseStep 551147 = 826721) B826721
theorem B551207 : Blo 366759 551207 := bstep (se 1 (by rfl) ⟨413405, by rfl⟩ : syracuseStep 551207 = 826811) B826811
theorem B1239353 : Blo 366759 1239353 := bstep (se 2 (by rfl) ⟨464757, by rfl⟩ : syracuseStep 1239353 = 929515) B929515
theorem B551291 : Blo 366759 551291 := bstep (se 1 (by rfl) ⟨413468, by rfl⟩ : syracuseStep 551291 = 826937) B826937
theorem B1862027 : Blo 366759 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1567259 : Blo 366759 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B1239623 : Blo 366759 1239623 := bstep (se 1 (by rfl) ⟨929717, by rfl⟩ : syracuseStep 1239623 = 1859435) B1859435
theorem B551561 : Blo 366759 551561 := bstep (se 2 (by rfl) ⟨206835, by rfl⟩ : syracuseStep 551561 = 413671) B413671
theorem B551735 : Blo 366759 551735 := bstep (se 1 (by rfl) ⟨413801, by rfl⟩ : syracuseStep 551735 = 827603) B827603
theorem B551771 : Blo 366759 551771 := bstep (se 1 (by rfl) ⟨413828, by rfl⟩ : syracuseStep 551771 = 827657) B827657
theorem B551915 : Blo 366759 551915 := bstep (se 1 (by rfl) ⟨413936, by rfl⟩ : syracuseStep 551915 = 827873) B827873
theorem B552119 : Blo 366759 552119 := bstep (se 1 (by rfl) ⟨414089, by rfl⟩ : syracuseStep 552119 = 828179) B828179
theorem B4484429 : Blo 366759 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B1862999 : Blo 366759 1862999 := bstep (se 1 (by rfl) ⟨1397249, by rfl⟩ : syracuseStep 1862999 = 2794499) B2794499
theorem B4713875 : Blo 366759 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B552359 : Blo 366759 552359 := bstep (se 1 (by rfl) ⟨414269, by rfl⟩ : syracuseStep 552359 = 828539) B828539
theorem B4615639 : Blo 366759 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B552443 : Blo 366759 552443 := bstep (se 1 (by rfl) ⟨414332, by rfl⟩ : syracuseStep 552443 = 828665) B828665
theorem B1240649 : Blo 366759 1240649 := bstep (se 2 (by rfl) ⟨465243, by rfl⟩ : syracuseStep 1240649 = 930487) B930487
theorem B552539 : Blo 366759 552539 := bstep (se 1 (by rfl) ⟨414404, by rfl⟩ : syracuseStep 552539 = 828809) B828809
theorem B552623 : Blo 366759 552623 := bstep (se 1 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 552623 = 828935) B828935
theorem B552743 : Blo 366759 552743 := bstep (se 1 (by rfl) ⟨414557, by rfl⟩ : syracuseStep 552743 = 829115) B829115
theorem B4255595 : Blo 366759 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B552827 : Blo 366759 552827 := bstep (se 1 (by rfl) ⟨414620, by rfl⟩ : syracuseStep 552827 = 829241) B829241
theorem B2944907 : Blo 366759 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B1994635 : Blo 366759 1994635 := bstep (se 1 (by rfl) ⟨1495976, by rfl⟩ : syracuseStep 1994635 = 2991953) B2991953
theorem B1273823 : Blo 366759 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B1863647 : Blo 366759 1863647 := bstep (se 1 (by rfl) ⟨1397735, by rfl⟩ : syracuseStep 1863647 = 2795471) B2795471
theorem B2813939 : Blo 366759 2813939 := bstep (se 1 (by rfl) ⟨2110454, by rfl⟩ : syracuseStep 2813939 = 4220909) B4220909
theorem B24047705 : Blo 366759 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B1863809 : Blo 366759 1863809 := bstep (se 2 (by rfl) ⟨698928, by rfl⟩ : syracuseStep 1863809 = 1397857) B1397857
theorem B1175741 : Blo 366759 1175741 := bstep (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) B440903
theorem B553247 : Blo 366759 553247 := bstep (se 1 (by rfl) ⟨414935, by rfl⟩ : syracuseStep 553247 = 829871) B829871
theorem B553271 : Blo 366759 553271 := bstep (se 1 (by rfl) ⟨414953, by rfl⟩ : syracuseStep 553271 = 829907) B829907
theorem B1044863 : Blo 366759 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B553343 : Blo 366759 553343 := bstep (se 1 (by rfl) ⟨415007, by rfl⟩ : syracuseStep 553343 = 830015) B830015
theorem B553415 : Blo 366759 553415 := bstep (se 1 (by rfl) ⟨415061, by rfl⟩ : syracuseStep 553415 = 830123) B830123
theorem B619103 : Blo 366759 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B553769 : Blo 366759 553769 := bstep (se 2 (by rfl) ⟨207663, by rfl⟩ : syracuseStep 553769 = 415327) B415327
theorem B553775 : Blo 366759 553775 := bstep (se 1 (by rfl) ⟨415331, by rfl⟩ : syracuseStep 553775 = 830663) B830663
theorem B455591 : Blo 366759 455591 := bstep (se 1 (by rfl) ⟨341693, by rfl⟩ : syracuseStep 455591 = 683387) B683387
theorem B553895 : Blo 366759 553895 := bstep (se 1 (by rfl) ⟨415421, by rfl⟩ : syracuseStep 553895 = 830843) B830843
theorem B1864619 : Blo 366759 1864619 := bstep (se 1 (by rfl) ⟨1398464, by rfl⟩ : syracuseStep 1864619 = 2796929) B2796929
theorem B1242107 : Blo 366759 1242107 := bstep (se 1 (by rfl) ⟨931580, by rfl⟩ : syracuseStep 1242107 = 1863161) B1863161
theorem B553979 : Blo 366759 553979 := bstep (se 1 (by rfl) ⟨415484, by rfl⟩ : syracuseStep 553979 = 830969) B830969
theorem B554039 : Blo 366759 554039 := bstep (se 1 (by rfl) ⟨415529, by rfl⟩ : syracuseStep 554039 = 831059) B831059
theorem B750665 : Blo 366759 750665 := bstep (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) B562999
theorem B554159 : Blo 366759 554159 := bstep (se 1 (by rfl) ⟨415619, by rfl⟩ : syracuseStep 554159 = 831239) B831239
theorem B1242323 : Blo 366759 1242323 := bstep (se 1 (by rfl) ⟨931742, by rfl⟩ : syracuseStep 1242323 = 1863485) B1863485
theorem B3142961 : Blo 366759 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B1242593 : Blo 366759 1242593 := bstep (se 2 (by rfl) ⟨465972, by rfl⟩ : syracuseStep 1242593 = 931945) B931945
theorem B554567 : Blo 366759 554567 := bstep (se 1 (by rfl) ⟨415925, by rfl⟩ : syracuseStep 554567 = 831851) B831851
theorem B554663 : Blo 366759 554663 := bstep (se 1 (by rfl) ⟨415997, by rfl⟩ : syracuseStep 554663 = 831995) B831995
theorem B5306107 : Blo 366759 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B554747 : Blo 366759 554747 := bstep (se 1 (by rfl) ⟨416060, by rfl⟩ : syracuseStep 554747 = 832121) B832121
theorem B554783 : Blo 366759 554783 := bstep (se 1 (by rfl) ⟨416087, by rfl⟩ : syracuseStep 554783 = 832175) B832175
theorem B2357039 : Blo 366759 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B554831 : Blo 366759 554831 := bstep (se 1 (by rfl) ⟨416123, by rfl⟩ : syracuseStep 554831 = 832247) B832247
theorem B554951 : Blo 366759 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B620527 : Blo 366759 620527 := bstep (se 1 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 620527 = 930791) B930791
theorem B1243241 : Blo 366759 1243241 := bstep (se 2 (by rfl) ⟨466215, by rfl⟩ : syracuseStep 1243241 = 932431) B932431
theorem B620777 : Blo 366759 620777 := bstep (se 2 (by rfl) ⟨232791, by rfl⟩ : syracuseStep 620777 = 465583) B465583
theorem B555305 : Blo 366759 555305 := bstep (se 2 (by rfl) ⟨208239, by rfl⟩ : syracuseStep 555305 = 416479) B416479
theorem B555311 : Blo 366759 555311 := bstep (se 1 (by rfl) ⟨416483, by rfl⟩ : syracuseStep 555311 = 832967) B832967
theorem B555551 : Blo 366759 555551 := bstep (se 1 (by rfl) ⟨416663, by rfl⟩ : syracuseStep 555551 = 833327) B833327
theorem B2095739 : Blo 366759 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B949097 : Blo 366759 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B555935 : Blo 366759 555935 := bstep (se 1 (by rfl) ⟨416951, by rfl⟩ : syracuseStep 555935 = 833903) B833903
theorem B1244105 : Blo 366759 1244105 := bstep (se 2 (by rfl) ⟨466539, by rfl⟩ : syracuseStep 1244105 = 933079) B933079
theorem B555983 : Blo 366759 555983 := bstep (se 1 (by rfl) ⟨416987, by rfl⟩ : syracuseStep 555983 = 833975) B833975
theorem B2554895 : Blo 366759 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B556073 : Blo 366759 556073 := bstep (se 2 (by rfl) ⟨208527, by rfl⟩ : syracuseStep 556073 = 417055) B417055
theorem B556079 : Blo 366759 556079 := bstep (se 1 (by rfl) ⟨417059, by rfl⟩ : syracuseStep 556079 = 834119) B834119
theorem B556103 : Blo 366759 556103 := bstep (se 1 (by rfl) ⟨417077, by rfl⟩ : syracuseStep 556103 = 834155) B834155
theorem B1244375 : Blo 366759 1244375 := bstep (se 1 (by rfl) ⟨933281, by rfl⟩ : syracuseStep 1244375 = 1866563) B1866563
theorem B1703405 : Blo 366759 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B622255 : Blo 366759 622255 := bstep (se 1 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 622255 = 933383) B933383
theorem B1769147 : Blo 366759 1769147 := bstep (se 1 (by rfl) ⟨1326860, by rfl⟩ : syracuseStep 1769147 = 2653721) B2653721
theorem B524009 : Blo 366759 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B884467 : Blo 366759 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B1244915 : Blo 366759 1244915 := bstep (se 1 (by rfl) ⟨933686, by rfl⟩ : syracuseStep 1244915 = 1867373) B1867373
theorem B622559 : Blo 366759 622559 := bstep (se 1 (by rfl) ⟨466919, by rfl⟩ : syracuseStep 622559 = 933839) B933839
theorem B1507513 : Blo 366759 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B3145999 : Blo 366759 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B5046731 : Blo 366759 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2785751 : Blo 366759 2785751 := bstep (se 1 (by rfl) ⟨2089313, by rfl⟩ : syracuseStep 2785751 = 4178627) B4178627
theorem B885343 : Blo 366759 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B591151 : Blo 366759 591151 := bstep (se 1 (by rfl) ⟨443363, by rfl⟩ : syracuseStep 591151 = 886727) B886727
theorem B1246751 : Blo 366759 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B624233 : Blo 366759 624233 := bstep (se 2 (by rfl) ⟨234087, by rfl⟩ : syracuseStep 624233 = 468175) B468175
theorem B5736071 : Blo 366759 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B624827 : Blo 366759 624827 := bstep (se 1 (by rfl) ⟨468620, by rfl⟩ : syracuseStep 624827 = 937241) B937241
theorem B20384011 : Blo 366759 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B1247615 : Blo 366759 1247615 := bstep (se 1 (by rfl) ⟨935711, by rfl⟩ : syracuseStep 1247615 = 1871423) B1871423
theorem B1771915 : Blo 366759 1771915 := bstep (se 1 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 1771915 = 2657873) B2657873
theorem B1214909 : Blo 366759 1214909 := bstep (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) B455591
theorem B1575719 : Blo 366759 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B2001773 : Blo 366759 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B625529 : Blo 366759 625529 := bstep (se 2 (by rfl) ⟨234573, by rfl⟩ : syracuseStep 625529 = 469147) B469147
theorem B789473 : Blo 366759 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B1576043 : Blo 366759 1576043 := bstep (se 1 (by rfl) ⟨1182032, by rfl⟩ : syracuseStep 1576043 = 2364065) B2364065
theorem B27037061 : Blo 366759 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B1576417 : Blo 366759 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B1052129 : Blo 366759 1052129 := bstep (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) B789097
theorem B1576691 : Blo 366759 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B2232287 : Blo 366759 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B1249343 : Blo 366759 1249343 := bstep (se 1 (by rfl) ⟨937007, by rfl⟩ : syracuseStep 1249343 = 1874015) B1874015
theorem B561259 : Blo 366759 561259 := bstep (se 1 (by rfl) ⟨420944, by rfl⟩ : syracuseStep 561259 = 841889) B841889
theorem B2101571 : Blo 366759 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B1774163 : Blo 366759 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1250045 : Blo 366759 1250045 := bstep (se 3 (by rfl) ⟨234383, by rfl⟩ : syracuseStep 1250045 = 468767) B468767
theorem B791387 : Blo 366759 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B1250207 : Blo 366759 1250207 := bstep (se 1 (by rfl) ⟨937655, by rfl⟩ : syracuseStep 1250207 = 1875311) B1875311
theorem B2659513 : Blo 366759 2659513 := bstep (se 2 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 2659513 = 1994635) B1994635
theorem B791849 : Blo 366759 791849 := bstep (se 2 (by rfl) ⟨296943, by rfl⟩ : syracuseStep 791849 = 593887) B593887
theorem B1775047 : Blo 366759 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B6723283 : Blo 366759 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B10065667 : Blo 366759 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B825335 : Blo 366759 825335 := bstep (se 1 (by rfl) ⟨619001, by rfl⟩ : syracuseStep 825335 = 1238003) B1238003
theorem B366823 : Blo 366759 366823 := bstep (se 1 (by rfl) ⟨275117, by rfl⟩ : syracuseStep 366823 = 550235) B550235
theorem B825695 : Blo 366759 825695 := bstep (se 1 (by rfl) ⟨619271, by rfl⟩ : syracuseStep 825695 = 1238543) B1238543
theorem B367007 : Blo 366759 367007 := bstep (se 1 (by rfl) ⟨275255, by rfl⟩ : syracuseStep 367007 = 550511) B550511
theorem B367055 : Blo 366759 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B367079 : Blo 366759 367079 := bstep (se 1 (by rfl) ⟨275309, by rfl⟩ : syracuseStep 367079 = 550619) B550619
theorem B367195 : Blo 366759 367195 := bstep (se 1 (by rfl) ⟨275396, by rfl⟩ : syracuseStep 367195 = 550793) B550793
theorem B367263 : Blo 366759 367263 := bstep (se 1 (by rfl) ⟨275447, by rfl⟩ : syracuseStep 367263 = 550895) B550895
theorem B367431 : Blo 366759 367431 := bstep (se 1 (by rfl) ⟨275573, by rfl⟩ : syracuseStep 367431 = 551147) B551147
theorem B367471 : Blo 366759 367471 := bstep (se 1 (by rfl) ⟨275603, by rfl⟩ : syracuseStep 367471 = 551207) B551207
theorem B826235 : Blo 366759 826235 := bstep (se 1 (by rfl) ⟨619676, by rfl⟩ : syracuseStep 826235 = 1239353) B1239353
theorem B367527 : Blo 366759 367527 := bstep (se 1 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 367527 = 551291) B551291
theorem B826415 : Blo 366759 826415 := bstep (se 1 (by rfl) ⟨619811, by rfl⟩ : syracuseStep 826415 = 1239623) B1239623
theorem B367707 : Blo 366759 367707 := bstep (se 1 (by rfl) ⟨275780, by rfl⟩ : syracuseStep 367707 = 551561) B551561
theorem B367823 : Blo 366759 367823 := bstep (se 1 (by rfl) ⟨275867, by rfl⟩ : syracuseStep 367823 = 551735) B551735
theorem B367847 : Blo 366759 367847 := bstep (se 1 (by rfl) ⟨275885, by rfl⟩ : syracuseStep 367847 = 551771) B551771
theorem B367943 : Blo 366759 367943 := bstep (se 1 (by rfl) ⟨275957, by rfl⟩ : syracuseStep 367943 = 551915) B551915
theorem B368079 : Blo 366759 368079 := bstep (se 1 (by rfl) ⟨276059, by rfl⟩ : syracuseStep 368079 = 552119) B552119
theorem B2104805 : Blo 366759 2104805 := bstep (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) B394651
theorem B2989619 : Blo 366759 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B368239 : Blo 366759 368239 := bstep (se 1 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 368239 = 552359) B552359
theorem B368295 : Blo 366759 368295 := bstep (se 1 (by rfl) ⟨276221, by rfl⟩ : syracuseStep 368295 = 552443) B552443
theorem B827099 : Blo 366759 827099 := bstep (se 1 (by rfl) ⟨620324, by rfl⟩ : syracuseStep 827099 = 1240649) B1240649
theorem B466651 : Blo 366759 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B368359 : Blo 366759 368359 := bstep (se 1 (by rfl) ⟨276269, by rfl⟩ : syracuseStep 368359 = 552539) B552539
theorem B1580791 : Blo 366759 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B368415 : Blo 366759 368415 := bstep (se 1 (by rfl) ⟨276311, by rfl⟩ : syracuseStep 368415 = 552623) B552623
theorem B368495 : Blo 366759 368495 := bstep (se 1 (by rfl) ⟨276371, by rfl⟩ : syracuseStep 368495 = 552743) B552743
theorem B368551 : Blo 366759 368551 := bstep (se 1 (by rfl) ⟨276413, by rfl⟩ : syracuseStep 368551 = 552827) B552827
theorem B3350443 : Blo 366759 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B827369 : Blo 366759 827369 := bstep (se 2 (by rfl) ⟨310263, by rfl⟩ : syracuseStep 827369 = 620527) B620527
theorem B1875959 : Blo 366759 1875959 := bstep (se 1 (by rfl) ⟨1406969, by rfl⟩ : syracuseStep 1875959 = 2813939) B2813939
theorem B16031803 : Blo 366759 16031803 := bstep (se 1 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 16031803 = 24047705) B24047705
theorem B368831 : Blo 366759 368831 := bstep (se 1 (by rfl) ⟨276623, by rfl⟩ : syracuseStep 368831 = 553247) B553247
theorem B368847 : Blo 366759 368847 := bstep (se 1 (by rfl) ⟨276635, by rfl⟩ : syracuseStep 368847 = 553271) B553271
theorem B696575 : Blo 366759 696575 := bstep (se 1 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 696575 = 1044863) B1044863
theorem B368895 : Blo 366759 368895 := bstep (se 1 (by rfl) ⟨276671, by rfl⟩ : syracuseStep 368895 = 553343) B553343
theorem B368943 : Blo 366759 368943 := bstep (se 1 (by rfl) ⟨276707, by rfl⟩ : syracuseStep 368943 = 553415) B553415
theorem B1581407 : Blo 366759 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B369179 : Blo 366759 369179 := bstep (se 1 (by rfl) ⟨276884, by rfl⟩ : syracuseStep 369179 = 553769) B553769
theorem B369183 : Blo 366759 369183 := bstep (se 1 (by rfl) ⟨276887, by rfl⟩ : syracuseStep 369183 = 553775) B553775
theorem B369263 : Blo 366759 369263 := bstep (se 1 (by rfl) ⟨276947, by rfl⟩ : syracuseStep 369263 = 553895) B553895
theorem B828071 : Blo 366759 828071 := bstep (se 1 (by rfl) ⟨621053, by rfl⟩ : syracuseStep 828071 = 1242107) B1242107
theorem B369319 : Blo 366759 369319 := bstep (se 1 (by rfl) ⟨276989, by rfl⟩ : syracuseStep 369319 = 553979) B553979
theorem B467623 : Blo 366759 467623 := bstep (se 1 (by rfl) ⟨350717, by rfl⟩ : syracuseStep 467623 = 701435) B701435
theorem B369359 : Blo 366759 369359 := bstep (se 1 (by rfl) ⟨277019, by rfl⟩ : syracuseStep 369359 = 554039) B554039
theorem B369439 : Blo 366759 369439 := bstep (se 1 (by rfl) ⟨277079, by rfl⟩ : syracuseStep 369439 = 554159) B554159
theorem B828215 : Blo 366759 828215 := bstep (se 1 (by rfl) ⟨621161, by rfl⟩ : syracuseStep 828215 = 1242323) B1242323
theorem B828395 : Blo 366759 828395 := bstep (se 1 (by rfl) ⟨621296, by rfl⟩ : syracuseStep 828395 = 1242593) B1242593
theorem B467947 : Blo 366759 467947 := bstep (se 1 (by rfl) ⟨350960, by rfl⟩ : syracuseStep 467947 = 701921) B701921
theorem B369711 : Blo 366759 369711 := bstep (se 1 (by rfl) ⟨277283, by rfl⟩ : syracuseStep 369711 = 554567) B554567
theorem B369775 : Blo 366759 369775 := bstep (se 1 (by rfl) ⟨277331, by rfl⟩ : syracuseStep 369775 = 554663) B554663
theorem B369831 : Blo 366759 369831 := bstep (se 1 (by rfl) ⟨277373, by rfl⟩ : syracuseStep 369831 = 554747) B554747
theorem B369855 : Blo 366759 369855 := bstep (se 1 (by rfl) ⟨277391, by rfl⟩ : syracuseStep 369855 = 554783) B554783
theorem B369887 : Blo 366759 369887 := bstep (se 1 (by rfl) ⟨277415, by rfl⟩ : syracuseStep 369887 = 554831) B554831
theorem B369967 : Blo 366759 369967 := bstep (se 1 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 369967 = 554951) B554951
theorem B828827 : Blo 366759 828827 := bstep (se 1 (by rfl) ⟨621620, by rfl⟩ : syracuseStep 828827 = 1243241) B1243241
theorem B370203 : Blo 366759 370203 := bstep (se 1 (by rfl) ⟨277652, by rfl⟩ : syracuseStep 370203 = 555305) B555305
theorem B370207 : Blo 366759 370207 := bstep (se 1 (by rfl) ⟨277655, by rfl⟩ : syracuseStep 370207 = 555311) B555311
theorem B2369189 : Blo 366759 2369189 := bstep (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) B444223
theorem B370367 : Blo 366759 370367 := bstep (se 1 (by rfl) ⟨277775, by rfl⟩ : syracuseStep 370367 = 555551) B555551
theorem B632731 : Blo 366759 632731 := bstep (se 1 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 632731 = 949097) B949097
theorem B370623 : Blo 366759 370623 := bstep (se 1 (by rfl) ⟨277967, by rfl⟩ : syracuseStep 370623 = 555935) B555935
theorem B829403 : Blo 366759 829403 := bstep (se 1 (by rfl) ⟨622052, by rfl⟩ : syracuseStep 829403 = 1244105) B1244105
theorem B370655 : Blo 366759 370655 := bstep (se 1 (by rfl) ⟨277991, by rfl⟩ : syracuseStep 370655 = 555983) B555983
theorem B370715 : Blo 366759 370715 := bstep (se 1 (by rfl) ⟨278036, by rfl⟩ : syracuseStep 370715 = 556073) B556073
theorem B370719 : Blo 366759 370719 := bstep (se 1 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 370719 = 556079) B556079
theorem B370735 : Blo 366759 370735 := bstep (se 1 (by rfl) ⟨278051, by rfl⟩ : syracuseStep 370735 = 556103) B556103
theorem B829583 : Blo 366759 829583 := bstep (se 1 (by rfl) ⟨622187, by rfl⟩ : syracuseStep 829583 = 1244375) B1244375
theorem B829673 : Blo 366759 829673 := bstep (se 2 (by rfl) ⟨311127, by rfl⟩ : syracuseStep 829673 = 622255) B622255
theorem B829943 : Blo 366759 829943 := bstep (se 1 (by rfl) ⟨622457, by rfl⟩ : syracuseStep 829943 = 1244915) B1244915
theorem B3976121 : Blo 366759 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B830537 : Blo 366759 830537 := bstep (se 2 (by rfl) ⟨311451, by rfl⟩ : syracuseStep 830537 = 622903) B622903
theorem B7122329 : Blo 366759 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B6402725 : Blo 366759 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B832265 : Blo 366759 832265 := bstep (se 2 (by rfl) ⟨312099, by rfl⟩ : syracuseStep 832265 = 624199) B624199
theorem B832319 : Blo 366759 832319 := bstep (se 1 (by rfl) ⟨624239, by rfl⟩ : syracuseStep 832319 = 1248479) B1248479
theorem B3552167 : Blo 366759 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B832463 : Blo 366759 832463 := bstep (se 1 (by rfl) ⟨624347, by rfl⟩ : syracuseStep 832463 = 1248695) B1248695
theorem B832553 : Blo 366759 832553 := bstep (se 2 (by rfl) ⟨312207, by rfl⟩ : syracuseStep 832553 = 624415) B624415
theorem B898231 : Blo 366759 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B2372827 : Blo 366759 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B832841 : Blo 366759 832841 := bstep (se 2 (by rfl) ⟨312315, by rfl⟩ : syracuseStep 832841 = 624631) B624631
theorem B11974031 : Blo 366759 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B1422845 : Blo 366759 1422845 := bstep (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) B533567
theorem B702407 : Blo 366759 702407 := bstep (se 1 (by rfl) ⟨526805, by rfl⟩ : syracuseStep 702407 = 1053611) B1053611
theorem B702695 : Blo 366759 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B1063207 : Blo 366759 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B833831 : Blo 366759 833831 := bstep (se 1 (by rfl) ⟨625373, by rfl⟩ : syracuseStep 833831 = 1250747) B1250747
theorem B5814823 : Blo 366759 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B834191 : Blo 366759 834191 := bstep (se 1 (by rfl) ⟨625643, by rfl⟩ : syracuseStep 834191 = 1251287) B1251287
theorem B3783905 : Blo 366759 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B1327913 : Blo 366759 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B935023 : Blo 366759 935023 := bstep (se 1 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 935023 = 1402535) B1402535
theorem B1393787 : Blo 366759 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B2804219 : Blo 366759 2804219 := bstep (se 1 (by rfl) ⟨2103164, by rfl⟩ : syracuseStep 2804219 = 4206329) B4206329
theorem B2837063 : Blo 366759 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B445223 : Blo 366759 445223 := bstep (se 1 (by rfl) ⟨333917, by rfl⟩ : syracuseStep 445223 = 667835) B667835
theorem B412735 : Blo 366759 412735 := bstep (se 1 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 412735 = 619103) B619103
theorem B30690893 : Blo 366759 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B413851 : Blo 366759 413851 := bstep (se 1 (by rfl) ⟨310388, by rfl⟩ : syracuseStep 413851 = 620777) B620777
theorem B1397159 : Blo 366759 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1397357 : Blo 366759 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B19059569 : Blo 366759 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1135603 : Blo 366759 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B415039 : Blo 366759 415039 := bstep (se 1 (by rfl) ⟨311279, by rfl⟩ : syracuseStep 415039 = 622559) B622559
theorem B1398343 : Blo 366759 1398343 := bstep (se 1 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 1398343 = 2097515) B2097515
theorem B415471 : Blo 366759 415471 := bstep (se 1 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 415471 = 623207) B623207
theorem B415579 : Blo 366759 415579 := bstep (se 1 (by rfl) ⟨311684, by rfl⟩ : syracuseStep 415579 = 623369) B623369
theorem B808951 : Blo 366759 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B3037313 : Blo 366759 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B415975 : Blo 366759 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B1399315 : Blo 366759 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B49109579 : Blo 366759 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B416623 : Blo 366759 416623 := bstep (se 1 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 416623 = 624935) B624935
theorem B1399787 : Blo 366759 1399787 := bstep (se 1 (by rfl) ⟨1049840, by rfl⟩ : syracuseStep 1399787 = 2099681) B2099681
theorem B843385 : Blo 366759 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B2121383 : Blo 366759 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B1892279 : Blo 366759 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B2810051 : Blo 366759 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B27025649 : Blo 366759 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B5333273 : Blo 366759 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B418591 : Blo 366759 418591 := bstep (se 1 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 418591 = 627887) B627887
theorem B1860407 : Blo 366759 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B1762843 : Blo 366759 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B550427 : Blo 366759 550427 := bstep (se 1 (by rfl) ⟨412820, by rfl⟩ : syracuseStep 550427 = 825641) B825641
theorem B1402703 : Blo 366759 1402703 := bstep (se 1 (by rfl) ⟨1052027, by rfl⟩ : syracuseStep 1402703 = 2104055) B2104055
theorem B550811 : Blo 366759 550811 := bstep (se 1 (by rfl) ⟨413108, by rfl⟩ : syracuseStep 550811 = 826217) B826217
theorem B1238975 : Blo 366759 1238975 := bstep (se 1 (by rfl) ⟨929231, by rfl⟩ : syracuseStep 1238975 = 1858463) B1858463
theorem B550847 : Blo 366759 550847 := bstep (se 1 (by rfl) ⟨413135, by rfl⟩ : syracuseStep 550847 = 826271) B826271
theorem B1239137 : Blo 366759 1239137 := bstep (se 2 (by rfl) ⟨464676, by rfl⟩ : syracuseStep 1239137 = 929353) B929353
theorem B6744161 : Blo 366759 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B551033 : Blo 366759 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B6285437 : Blo 366759 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B1861865 : Blo 366759 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B551417 : Blo 366759 551417 := bstep (se 2 (by rfl) ⟨206781, by rfl⟩ : syracuseStep 551417 = 413563) B413563
theorem B551471 : Blo 366759 551471 := bstep (se 1 (by rfl) ⟨413603, by rfl⟩ : syracuseStep 551471 = 827207) B827207
theorem B1239677 : Blo 366759 1239677 := bstep (se 3 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 1239677 = 464879) B464879
theorem B1239947 : Blo 366759 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B551903 : Blo 366759 551903 := bstep (se 1 (by rfl) ⟨413927, by rfl⟩ : syracuseStep 551903 = 827855) B827855
theorem B552347 : Blo 366759 552347 := bstep (se 1 (by rfl) ⟨414260, by rfl⟩ : syracuseStep 552347 = 828521) B828521
theorem B1240487 : Blo 366759 1240487 := bstep (se 1 (by rfl) ⟨930365, by rfl⟩ : syracuseStep 1240487 = 1860731) B1860731
theorem B552767 : Blo 366759 552767 := bstep (se 1 (by rfl) ⟨414575, by rfl⟩ : syracuseStep 552767 = 829151) B829151
theorem B3993421 : Blo 366759 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B1240919 : Blo 366759 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B1241081 : Blo 366759 1241081 := bstep (se 2 (by rfl) ⟨465405, by rfl⟩ : syracuseStep 1241081 = 930811) B930811
theorem B552953 : Blo 366759 552953 := bstep (se 2 (by rfl) ⟨207357, by rfl⟩ : syracuseStep 552953 = 414715) B414715
theorem B553193 : Blo 366759 553193 := bstep (se 2 (by rfl) ⟨207447, by rfl⟩ : syracuseStep 553193 = 414895) B414895
theorem B1241351 : Blo 366759 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B1044839 : Blo 366759 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B553319 : Blo 366759 553319 := bstep (se 1 (by rfl) ⟨414989, by rfl⟩ : syracuseStep 553319 = 829979) B829979
theorem B618907 : Blo 366759 618907 := bstep (se 1 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 618907 = 928361) B928361
theorem B1241729 : Blo 366759 1241729 := bstep (se 2 (by rfl) ⟨465648, by rfl⟩ : syracuseStep 1241729 = 931297) B931297
theorem B553865 : Blo 366759 553865 := bstep (se 2 (by rfl) ⟨207699, by rfl⟩ : syracuseStep 553865 = 415399) B415399
theorem B1241999 : Blo 366759 1241999 := bstep (se 1 (by rfl) ⟨931499, by rfl⟩ : syracuseStep 1241999 = 1862999) B1862999
theorem B3142583 : Blo 366759 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B7074809 : Blo 366759 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B619771 : Blo 366759 619771 := bstep (se 1 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 619771 = 929657) B929657
theorem B1963271 : Blo 366759 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B554249 : Blo 366759 554249 := bstep (se 2 (by rfl) ⟨207843, by rfl⟩ : syracuseStep 554249 = 415687) B415687
theorem B849215 : Blo 366759 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B1242431 : Blo 366759 1242431 := bstep (se 1 (by rfl) ⟨931823, by rfl⟩ : syracuseStep 1242431 = 1863647) B1863647
theorem B554303 : Blo 366759 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B1242539 : Blo 366759 1242539 := bstep (se 1 (by rfl) ⟨931904, by rfl⟩ : syracuseStep 1242539 = 1863809) B1863809
theorem B783827 : Blo 366759 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B1406423 : Blo 366759 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B554729 : Blo 366759 554729 := bstep (se 2 (by rfl) ⟨208023, by rfl⟩ : syracuseStep 554729 = 416047) B416047
theorem B554735 : Blo 366759 554735 := bstep (se 1 (by rfl) ⟨416051, by rfl⟩ : syracuseStep 554735 = 832103) B832103
theorem B1243079 : Blo 366759 1243079 := bstep (se 1 (by rfl) ⟨932309, by rfl⟩ : syracuseStep 1243079 = 1864619) B1864619
theorem B620615 : Blo 366759 620615 := bstep (se 1 (by rfl) ⟨465461, by rfl⟩ : syracuseStep 620615 = 930923) B930923
theorem B555191 : Blo 366759 555191 := bstep (se 1 (by rfl) ⟨416393, by rfl⟩ : syracuseStep 555191 = 832787) B832787
theorem B2095307 : Blo 366759 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B555239 : Blo 366759 555239 := bstep (se 1 (by rfl) ⟨416429, by rfl⟩ : syracuseStep 555239 = 832859) B832859
theorem B555611 : Blo 366759 555611 := bstep (se 1 (by rfl) ⟨416708, by rfl⟩ : syracuseStep 555611 = 833417) B833417
theorem B33094277 : Blo 366759 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B883343 : Blo 366759 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B555755 : Blo 366759 555755 := bstep (se 1 (by rfl) ⟨416816, by rfl⟩ : syracuseStep 555755 = 833633) B833633
theorem B555785 : Blo 366759 555785 := bstep (se 2 (by rfl) ⟨208419, by rfl⟩ : syracuseStep 555785 = 416839) B416839
theorem B1342295 : Blo 366759 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B621479 : Blo 366759 621479 := bstep (se 1 (by rfl) ⟨466109, by rfl⟩ : syracuseStep 621479 = 932219) B932219
theorem B98466965 : Blo 366759 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B5274839 : Blo 366759 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B1703263 : Blo 366759 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1179289 : Blo 366759 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B1179431 : Blo 366759 1179431 := bstep (se 1 (by rfl) ⟨884573, by rfl⟩ : syracuseStep 1179431 = 1769147) B1769147
theorem B4194665 : Blo 366759 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B885275 : Blo 366759 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B1180457 : Blo 366759 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B623497 : Blo 366759 623497 := bstep (se 2 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 623497 = 467623) B467623
theorem B2786237 : Blo 366759 2786237 := bstep (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) B1044839
theorem B558121 : Blo 366759 558121 := bstep (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) B418591
theorem B623929 : Blo 366759 623929 := bstep (se 2 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 623929 = 467947) B467947
theorem B1246697 : Blo 366759 1246697 := bstep (se 2 (by rfl) ⟨467511, by rfl⟩ : syracuseStep 1246697 = 935023) B935023
theorem B1869479 : Blo 366759 1869479 := bstep (se 1 (by rfl) ⟨1402109, by rfl⟩ : syracuseStep 1869479 = 2804219) B2804219
theorem B788201 : Blo 366759 788201 := bstep (se 2 (by rfl) ⟨295575, by rfl⟩ : syracuseStep 788201 = 591151) B591151
theorem B1050479 : Blo 366759 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B1050695 : Blo 366759 1050695 := bstep (se 1 (by rfl) ⟨788021, by rfl⟩ : syracuseStep 1050695 = 1576043) B1576043
theorem B18024707 : Blo 366759 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B1051127 : Blo 366759 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B1182775 : Blo 366759 1182775 := bstep (se 1 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 1182775 = 1774163) B1774163
theorem B2362553 : Blo 366759 2362553 := bstep (se 2 (by rfl) ⟨885957, by rfl⟩ : syracuseStep 2362553 = 1771915) B1771915
theorem B527591 : Blo 366759 527591 := bstep (se 1 (by rfl) ⟨395693, by rfl⟩ : syracuseStep 527591 = 791387) B791387
theorem B2264573 : Blo 366759 2264573 := bstep (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) B849215
theorem B527899 : Blo 366759 527899 := bstep (se 1 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 527899 = 791849) B791849
theorem B32739719 : Blo 366759 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B2101889 : Blo 366759 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B1414255 : Blo 366759 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1250639 : Blo 366759 1250639 := bstep (se 1 (by rfl) ⟨937979, by rfl⟩ : syracuseStep 1250639 = 1875959) B1875959
theorem B1873367 : Blo 366759 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B464383 : Blo 366759 464383 := bstep (se 1 (by rfl) ⟨348287, by rfl⟩ : syracuseStep 464383 = 696575) B696575
theorem B1054271 : Blo 366759 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B825209 : Blo 366759 825209 := bstep (se 2 (by rfl) ⟨309453, by rfl⟩ : syracuseStep 825209 = 618907) B618907
theorem B1873853 : Blo 366759 1873853 := bstep (se 3 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 1873853 = 702695) B702695
theorem B366951 : Blo 366759 366951 := bstep (se 1 (by rfl) ⟨275213, by rfl⟩ : syracuseStep 366951 = 550427) B550427
theorem B1579459 : Blo 366759 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B367207 : Blo 366759 367207 := bstep (se 1 (by rfl) ⟨275405, by rfl⟩ : syracuseStep 367207 = 550811) B550811
theorem B825983 : Blo 366759 825983 := bstep (se 1 (by rfl) ⟨619487, by rfl⟩ : syracuseStep 825983 = 1238975) B1238975
theorem B367231 : Blo 366759 367231 := bstep (se 1 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 367231 = 550847) B550847
theorem B1514137 : Blo 366759 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B826091 : Blo 366759 826091 := bstep (se 1 (by rfl) ⟨619568, by rfl⟩ : syracuseStep 826091 = 1239137) B1239137
theorem B4496107 : Blo 366759 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B367355 : Blo 366759 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B3546017 : Blo 366759 3546017 := bstep (se 2 (by rfl) ⟨1329756, by rfl⟩ : syracuseStep 3546017 = 2659513) B2659513
theorem B826361 : Blo 366759 826361 := bstep (se 2 (by rfl) ⟨309885, by rfl⟩ : syracuseStep 826361 = 619771) B619771
theorem B367611 : Blo 366759 367611 := bstep (se 1 (by rfl) ⟨275708, by rfl⟩ : syracuseStep 367611 = 551417) B551417
theorem B367647 : Blo 366759 367647 := bstep (se 1 (by rfl) ⟨275735, by rfl⟩ : syracuseStep 367647 = 551471) B551471
theorem B826451 : Blo 366759 826451 := bstep (se 1 (by rfl) ⟨619838, by rfl⟩ : syracuseStep 826451 = 1239677) B1239677
theorem B826631 : Blo 366759 826631 := bstep (se 1 (by rfl) ⟨619973, by rfl⟩ : syracuseStep 826631 = 1239947) B1239947
theorem B2366729 : Blo 366759 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B367935 : Blo 366759 367935 := bstep (se 1 (by rfl) ⟨275951, by rfl⟩ : syracuseStep 367935 = 551903) B551903
theorem B1187261 : Blo 366759 1187261 := bstep (se 3 (by rfl) ⟨222611, by rfl⟩ : syracuseStep 1187261 = 445223) B445223
theorem B368231 : Blo 366759 368231 := bstep (se 1 (by rfl) ⟨276173, by rfl⟩ : syracuseStep 368231 = 552347) B552347
theorem B826991 : Blo 366759 826991 := bstep (se 1 (by rfl) ⟨620243, by rfl⟩ : syracuseStep 826991 = 1240487) B1240487
theorem B368511 : Blo 366759 368511 := bstep (se 1 (by rfl) ⟨276383, by rfl⟩ : syracuseStep 368511 = 552767) B552767
theorem B827279 : Blo 366759 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B2105261 : Blo 366759 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B368635 : Blo 366759 368635 := bstep (se 1 (by rfl) ⟨276476, by rfl⟩ : syracuseStep 368635 = 552953) B552953
theorem B827387 : Blo 366759 827387 := bstep (se 1 (by rfl) ⟨620540, by rfl⟩ : syracuseStep 827387 = 1241081) B1241081
theorem B368795 : Blo 366759 368795 := bstep (se 1 (by rfl) ⟨276596, by rfl⟩ : syracuseStep 368795 = 553193) B553193
theorem B827567 : Blo 366759 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B368879 : Blo 366759 368879 := bstep (se 1 (by rfl) ⟨276659, by rfl⟩ : syracuseStep 368879 = 553319) B553319
theorem B1417609 : Blo 366759 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B827819 : Blo 366759 827819 := bstep (se 1 (by rfl) ⟨620864, by rfl⟩ : syracuseStep 827819 = 1241729) B1241729
theorem B4268483 : Blo 366759 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B14066237 : Blo 366759 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B369243 : Blo 366759 369243 := bstep (se 1 (by rfl) ⟨276932, by rfl⟩ : syracuseStep 369243 = 553865) B553865
theorem B827999 : Blo 366759 827999 := bstep (se 1 (by rfl) ⟨620999, by rfl⟩ : syracuseStep 827999 = 1241999) B1241999
theorem B2368111 : Blo 366759 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B369499 : Blo 366759 369499 := bstep (se 1 (by rfl) ⟨277124, by rfl⟩ : syracuseStep 369499 = 554249) B554249
theorem B828287 : Blo 366759 828287 := bstep (se 1 (by rfl) ⟨621215, by rfl⟩ : syracuseStep 828287 = 1242431) B1242431
theorem B369535 : Blo 366759 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B828359 : Blo 366759 828359 := bstep (se 1 (by rfl) ⟨621269, by rfl⟩ : syracuseStep 828359 = 1242539) B1242539
theorem B369819 : Blo 366759 369819 := bstep (se 1 (by rfl) ⟨277364, by rfl⟩ : syracuseStep 369819 = 554729) B554729
theorem B369823 : Blo 366759 369823 := bstep (se 1 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 369823 = 554735) B554735
theorem B828719 : Blo 366759 828719 := bstep (se 1 (by rfl) ⟨621539, by rfl⟩ : syracuseStep 828719 = 1243079) B1243079
theorem B468271 : Blo 366759 468271 := bstep (se 1 (by rfl) ⟨351203, by rfl⟩ : syracuseStep 468271 = 702407) B702407
theorem B370127 : Blo 366759 370127 := bstep (se 1 (by rfl) ⟨277595, by rfl⟩ : syracuseStep 370127 = 555191) B555191
theorem B370159 : Blo 366759 370159 := bstep (se 1 (by rfl) ⟨277619, by rfl⟩ : syracuseStep 370159 = 555239) B555239
theorem B370407 : Blo 366759 370407 := bstep (se 1 (by rfl) ⟨277805, by rfl⟩ : syracuseStep 370407 = 555611) B555611
theorem B22062851 : Blo 366759 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B2271017 : Blo 366759 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B370503 : Blo 366759 370503 := bstep (se 1 (by rfl) ⟨277877, by rfl⟩ : syracuseStep 370503 = 555755) B555755
theorem B370523 : Blo 366759 370523 := bstep (se 1 (by rfl) ⟨277892, by rfl⟩ : syracuseStep 370523 = 555785) B555785
theorem B894863 : Blo 366759 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B65644643 : Blo 366759 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B1124513 : Blo 366759 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B2107721 : Blo 366759 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B4467257 : Blo 366759 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B21375737 : Blo 366759 21375737 := bstep (se 2 (by rfl) ⟨8015901, by rfl⟩ : syracuseStep 21375737 = 16031803) B16031803
theorem B2010017 : Blo 366759 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B2993381 : Blo 366759 2993381 := bstep (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) B561259
theorem B929191 : Blo 366759 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B831167 : Blo 366759 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B831743 : Blo 366759 831743 := bstep (se 1 (by rfl) ⟨623807, by rfl⟩ : syracuseStep 831743 = 1247615) B1247615
theorem B20460595 : Blo 366759 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B1488191 : Blo 366759 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B832895 : Blo 366759 832895 := bstep (se 1 (by rfl) ⟨624671, by rfl⟩ : syracuseStep 832895 = 1249343) B1249343
theorem B931439 : Blo 366759 931439 := bstep (se 1 (by rfl) ⟨698579, by rfl⟩ : syracuseStep 931439 = 1397159) B1397159
theorem B27178681 : Blo 366759 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B931571 : Blo 366759 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B833363 : Blo 366759 833363 := bstep (se 1 (by rfl) ⟨625022, by rfl⟩ : syracuseStep 833363 = 1250045) B1250045
theorem B833471 : Blo 366759 833471 := bstep (se 1 (by rfl) ⟨625103, by rfl⟩ : syracuseStep 833471 = 1250207) B1250207
theorem B933191 : Blo 366759 933191 := bstep (se 1 (by rfl) ⟨699893, by rfl⟩ : syracuseStep 933191 = 1399787) B1399787
theorem B5324561 : Blo 366759 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B3555515 : Blo 366759 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B935135 : Blo 366759 935135 := bstep (se 1 (by rfl) ⟨701351, by rfl⟩ : syracuseStep 935135 = 1402703) B1402703
theorem B1197641 : Blo 366759 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B3163769 : Blo 366759 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B8964377 : Blo 366759 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B13420889 : Blo 366759 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B7753097 : Blo 366759 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B7982687 : Blo 366759 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B937615 : Blo 366759 937615 := bstep (se 1 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 937615 = 1406423) B1406423
theorem B2805677 : Blo 366759 2805677 := bstep (se 3 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 2805677 = 1052129) B1052129
theorem B413743 : Blo 366759 413743 := bstep (se 1 (by rfl) ⟨310307, by rfl⟩ : syracuseStep 413743 = 620615) B620615
theorem B1396871 : Blo 366759 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B414319 : Blo 366759 414319 := bstep (se 1 (by rfl) ⟨310739, by rfl⟩ : syracuseStep 414319 = 621479) B621479
theorem B3364487 : Blo 366759 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1857167 : Blo 366759 1857167 := bstep (se 1 (by rfl) ⟨1392875, by rfl⟩ : syracuseStep 1857167 = 2785751) B2785751
theorem B416155 : Blo 366759 416155 := bstep (se 1 (by rfl) ⟨312116, by rfl⟩ : syracuseStep 416155 = 624233) B624233
theorem B3824047 : Blo 366759 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B416551 : Blo 366759 416551 := bstep (se 1 (by rfl) ⟨312413, by rfl⟩ : syracuseStep 416551 = 624827) B624827
theorem B809939 : Blo 366759 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B1334515 : Blo 366759 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B417019 : Blo 366759 417019 := bstep (se 1 (by rfl) ⟨312764, by rfl⟩ : syracuseStep 417019 = 625529) B625529
theorem B2350457 : Blo 366759 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B843641 : Blo 366759 843641 := bstep (se 2 (by rfl) ⟨316365, by rfl⟩ : syracuseStep 843641 = 632731) B632731
theorem B1401047 : Blo 366759 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B12706379 : Blo 366759 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B550223 : Blo 366759 550223 := bstep (se 1 (by rfl) ⟨412667, by rfl⟩ : syracuseStep 550223 = 825335) B825335
theorem B550313 : Blo 366759 550313 := bstep (se 2 (by rfl) ⟨206367, by rfl⟩ : syracuseStep 550313 = 412735) B412735
theorem B2024875 : Blo 366759 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B550463 : Blo 366759 550463 := bstep (se 1 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 550463 = 825695) B825695
theorem B550823 : Blo 366759 550823 := bstep (se 1 (by rfl) ⟨413117, by rfl⟩ : syracuseStep 550823 = 826235) B826235
theorem B550943 : Blo 366759 550943 := bstep (se 1 (by rfl) ⟨413207, by rfl⟩ : syracuseStep 550943 = 826415) B826415
theorem B1403203 : Blo 366759 1403203 := bstep (se 1 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 1403203 = 2104805) B2104805
theorem B1993079 : Blo 366759 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B551399 : Blo 366759 551399 := bstep (se 1 (by rfl) ⟨413549, by rfl⟩ : syracuseStep 551399 = 827099) B827099
theorem B551579 : Blo 366759 551579 := bstep (se 1 (by rfl) ⟨413684, by rfl⟩ : syracuseStep 551579 = 827369) B827369
theorem B18017099 : Blo 366759 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B551801 : Blo 366759 551801 := bstep (se 2 (by rfl) ⟨206925, by rfl⟩ : syracuseStep 551801 = 413851) B413851
theorem B552047 : Blo 366759 552047 := bstep (se 1 (by rfl) ⟨414035, by rfl⟩ : syracuseStep 552047 = 828071) B828071
theorem B1240271 : Blo 366759 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B552143 : Blo 366759 552143 := bstep (se 1 (by rfl) ⟨414107, by rfl⟩ : syracuseStep 552143 = 828215) B828215
theorem B552263 : Blo 366759 552263 := bstep (se 1 (by rfl) ⟨414197, by rfl⟩ : syracuseStep 552263 = 828395) B828395
theorem B552551 : Blo 366759 552551 := bstep (se 1 (by rfl) ⟨414413, by rfl⟩ : syracuseStep 552551 = 828827) B828827
theorem B552935 : Blo 366759 552935 := bstep (se 1 (by rfl) ⟨414701, by rfl⟩ : syracuseStep 552935 = 829403) B829403
theorem B4190291 : Blo 366759 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B553055 : Blo 366759 553055 := bstep (se 1 (by rfl) ⟨414791, by rfl⟩ : syracuseStep 553055 = 829583) B829583
theorem B1241243 : Blo 366759 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B553115 : Blo 366759 553115 := bstep (se 1 (by rfl) ⟨414836, by rfl⟩ : syracuseStep 553115 = 829673) B829673
theorem B7565501 : Blo 366759 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B553295 : Blo 366759 553295 := bstep (se 1 (by rfl) ⟨414971, by rfl⟩ : syracuseStep 553295 = 829943) B829943
theorem B2355581 : Blo 366759 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B553385 : Blo 366759 553385 := bstep (se 2 (by rfl) ⟨207519, by rfl⟩ : syracuseStep 553385 = 415039) B415039
theorem B2650747 : Blo 366759 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B553691 : Blo 366759 553691 := bstep (se 1 (by rfl) ⟨415268, by rfl⟩ : syracuseStep 553691 = 830537) B830537
theorem B1864457 : Blo 366759 1864457 := bstep (se 2 (by rfl) ⟨699171, by rfl⟩ : syracuseStep 1864457 = 1398343) B1398343
theorem B4748219 : Blo 366759 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B553961 : Blo 366759 553961 := bstep (se 2 (by rfl) ⟨207735, by rfl⟩ : syracuseStep 553961 = 415471) B415471
theorem B554105 : Blo 366759 554105 := bstep (se 2 (by rfl) ⟨207789, by rfl⟩ : syracuseStep 554105 = 415579) B415579
theorem B1078601 : Blo 366759 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B554633 : Blo 366759 554633 := bstep (se 2 (by rfl) ⟨207987, by rfl⟩ : syracuseStep 554633 = 415975) B415975
theorem B554843 : Blo 366759 554843 := bstep (se 1 (by rfl) ⟨416132, by rfl⟩ : syracuseStep 554843 = 832265) B832265
theorem B554879 : Blo 366759 554879 := bstep (se 1 (by rfl) ⟨416159, by rfl⟩ : syracuseStep 554879 = 832319) B832319
theorem B2095055 : Blo 366759 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B554975 : Blo 366759 554975 := bstep (se 1 (by rfl) ⟨416231, by rfl⟩ : syracuseStep 554975 = 832463) B832463
theorem B4716539 : Blo 366759 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B1865753 : Blo 366759 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B555035 : Blo 366759 555035 := bstep (se 1 (by rfl) ⟨416276, by rfl⟩ : syracuseStep 555035 = 832553) B832553
theorem B1308847 : Blo 366759 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B555227 : Blo 366759 555227 := bstep (se 1 (by rfl) ⟨416420, by rfl⟩ : syracuseStep 555227 = 832841) B832841
theorem B522551 : Blo 366759 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B948563 : Blo 366759 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B555497 : Blo 366759 555497 := bstep (se 2 (by rfl) ⟨208311, by rfl⟩ : syracuseStep 555497 = 416623) B416623
theorem B555887 : Blo 366759 555887 := bstep (se 1 (by rfl) ⟨416915, by rfl⟩ : syracuseStep 555887 = 833831) B833831
theorem B556127 : Blo 366759 556127 := bstep (se 1 (by rfl) ⟨417095, by rfl⟩ : syracuseStep 556127 = 834191) B834191
theorem B2522603 : Blo 366759 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B1572385 : Blo 366759 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B622201 : Blo 366759 622201 := bstep (se 2 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 622201 = 466651) B466651
theorem B5046077 : Blo 366759 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B786287 : Blo 366759 786287 := bstep (se 1 (by rfl) ⟨589715, by rfl⟩ : syracuseStep 786287 = 1179431) B1179431
theorem B590183 : Blo 366759 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B786971 : Blo 366759 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B623423 : Blo 366759 623423 := bstep (se 1 (by rfl) ⟨467567, by rfl⟩ : syracuseStep 623423 = 935135) B935135
theorem B1246319 : Blo 366759 1246319 := bstep (se 1 (by rfl) ⟨934739, by rfl⟩ : syracuseStep 1246319 = 1869479) B1869479
theorem B525467 : Blo 366759 525467 := bstep (se 1 (by rfl) ⟨394100, by rfl⟩ : syracuseStep 525467 = 788201) B788201
theorem B8947259 : Blo 366759 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B624361 : Blo 366759 624361 := bstep (se 2 (by rfl) ⟨234135, by rfl⟩ : syracuseStep 624361 = 468271) B468271
theorem B1575035 : Blo 366759 1575035 := bstep (se 1 (by rfl) ⟨1181276, by rfl⟩ : syracuseStep 1575035 = 2362553) B2362553
theorem B1509715 : Blo 366759 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1870451 : Blo 366759 1870451 := bstep (se 1 (by rfl) ⟨1402838, by rfl⟩ : syracuseStep 1870451 = 2805677) B2805677
theorem B1870937 : Blo 366759 1870937 := bstep (se 2 (by rfl) ⟨701601, by rfl⟩ : syracuseStep 1870937 = 1403203) B1403203
theorem B11505077 : Blo 366759 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B3968509 : Blo 366759 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B1248911 : Blo 366759 1248911 := bstep (se 1 (by rfl) ⟨936683, by rfl⟩ : syracuseStep 1248911 = 1873367) B1873367
theorem B1249235 : Blo 366759 1249235 := bstep (se 1 (by rfl) ⟨936926, by rfl⟩ : syracuseStep 1249235 = 1873853) B1873853
theorem B1577033 : Blo 366759 1577033 := bstep (se 2 (by rfl) ⟨591387, by rfl⟩ : syracuseStep 1577033 = 1182775) B1182775
theorem B2364011 : Blo 366759 2364011 := bstep (se 1 (by rfl) ⟨1773008, by rfl⟩ : syracuseStep 2364011 = 3546017) B3546017
theorem B1577819 : Blo 366759 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B1250153 : Blo 366759 1250153 := bstep (se 2 (by rfl) ⟨468807, by rfl⟩ : syracuseStep 1250153 = 937615) B937615
theorem B791507 : Blo 366759 791507 := bstep (se 1 (by rfl) ⟨593630, by rfl⟩ : syracuseStep 791507 = 1187261) B1187261
theorem B562427 : Blo 366759 562427 := bstep (se 1 (by rfl) ⟨421820, by rfl⟩ : syracuseStep 562427 = 843641) B843641
theorem B9377491 : Blo 366759 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B366815 : Blo 366759 366815 := bstep (se 1 (by rfl) ⟨275111, by rfl⟩ : syracuseStep 366815 = 550223) B550223
theorem B366875 : Blo 366759 366875 := bstep (se 1 (by rfl) ⟨275156, by rfl⟩ : syracuseStep 366875 = 550313) B550313
theorem B366975 : Blo 366759 366975 := bstep (se 1 (by rfl) ⟨275231, by rfl⟩ : syracuseStep 366975 = 550463) B550463
theorem B596575 : Blo 366759 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B367215 : Blo 366759 367215 := bstep (se 1 (by rfl) ⟨275411, by rfl⟩ : syracuseStep 367215 = 550823) B550823
theorem B367295 : Blo 366759 367295 := bstep (se 1 (by rfl) ⟨275471, by rfl⟩ : syracuseStep 367295 = 550943) B550943
theorem B367599 : Blo 366759 367599 := bstep (se 1 (by rfl) ⟨275699, by rfl⟩ : syracuseStep 367599 = 551399) B551399
theorem B367719 : Blo 366759 367719 := bstep (se 1 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 367719 = 551579) B551579
theorem B367867 : Blo 366759 367867 := bstep (se 1 (by rfl) ⟨275900, by rfl⟩ : syracuseStep 367867 = 551801) B551801
theorem B368031 : Blo 366759 368031 := bstep (se 1 (by rfl) ⟨276023, by rfl⟩ : syracuseStep 368031 = 552047) B552047
theorem B826847 : Blo 366759 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B368095 : Blo 366759 368095 := bstep (se 1 (by rfl) ⟨276071, by rfl⟩ : syracuseStep 368095 = 552143) B552143
theorem B368175 : Blo 366759 368175 := bstep (se 1 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 368175 = 552263) B552263
theorem B368367 : Blo 366759 368367 := bstep (se 1 (by rfl) ⟨276275, by rfl⟩ : syracuseStep 368367 = 552551) B552551
theorem B368623 : Blo 366759 368623 := bstep (se 1 (by rfl) ⟨276467, by rfl⟩ : syracuseStep 368623 = 552935) B552935
theorem B2793527 : Blo 366759 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B368703 : Blo 366759 368703 := bstep (se 1 (by rfl) ⟨276527, by rfl⟩ : syracuseStep 368703 = 553055) B553055
theorem B827495 : Blo 366759 827495 := bstep (se 1 (by rfl) ⟨620621, by rfl⟩ : syracuseStep 827495 = 1241243) B1241243
theorem B368743 : Blo 366759 368743 := bstep (se 1 (by rfl) ⟨276557, by rfl⟩ : syracuseStep 368743 = 553115) B553115
theorem B368863 : Blo 366759 368863 := bstep (se 1 (by rfl) ⟨276647, by rfl⟩ : syracuseStep 368863 = 553295) B553295
theorem B1745129 : Blo 366759 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B368923 : Blo 366759 368923 := bstep (se 1 (by rfl) ⟨276692, by rfl⟩ : syracuseStep 368923 = 553385) B553385
theorem B369127 : Blo 366759 369127 := bstep (se 1 (by rfl) ⟨276845, by rfl⟩ : syracuseStep 369127 = 553691) B553691
theorem B2105945 : Blo 366759 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B369307 : Blo 366759 369307 := bstep (se 1 (by rfl) ⟨276980, by rfl⟩ : syracuseStep 369307 = 553961) B553961
theorem B369403 : Blo 366759 369403 := bstep (se 1 (by rfl) ⟨277052, by rfl⟩ : syracuseStep 369403 = 554105) B554105
theorem B369755 : Blo 366759 369755 := bstep (se 1 (by rfl) ⟨277316, by rfl⟩ : syracuseStep 369755 = 554633) B554633
theorem B369895 : Blo 366759 369895 := bstep (se 1 (by rfl) ⟨277421, by rfl⟩ : syracuseStep 369895 = 554843) B554843
theorem B369919 : Blo 366759 369919 := bstep (se 1 (by rfl) ⟨277439, by rfl⟩ : syracuseStep 369919 = 554879) B554879
theorem B369983 : Blo 366759 369983 := bstep (se 1 (by rfl) ⟨277487, by rfl⟩ : syracuseStep 369983 = 554975) B554975
theorem B370023 : Blo 366759 370023 := bstep (se 1 (by rfl) ⟨277517, by rfl⟩ : syracuseStep 370023 = 555035) B555035
theorem B370151 : Blo 366759 370151 := bstep (se 1 (by rfl) ⟨277613, by rfl⟩ : syracuseStep 370151 = 555227) B555227
theorem B632375 : Blo 366759 632375 := bstep (se 1 (by rfl) ⟨474281, by rfl⟩ : syracuseStep 632375 = 948563) B948563
theorem B1779353 : Blo 366759 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B370331 : Blo 366759 370331 := bstep (se 1 (by rfl) ⟨277748, by rfl⟩ : syracuseStep 370331 = 555497) B555497
theorem B370591 : Blo 366759 370591 := bstep (se 1 (by rfl) ⟨277943, by rfl⟩ : syracuseStep 370591 = 555887) B555887
theorem B370751 : Blo 366759 370751 := bstep (se 1 (by rfl) ⟨278063, by rfl⟩ : syracuseStep 370751 = 556127) B556127
theorem B829601 : Blo 366759 829601 := bstep (se 2 (by rfl) ⟨311100, by rfl⟩ : syracuseStep 829601 = 622201) B622201
theorem B1681735 : Blo 366759 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B3549707 : Blo 366759 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B2370343 : Blo 366759 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B2796443 : Blo 366759 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B3157481 : Blo 366759 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B831131 : Blo 366759 831131 := bstep (se 1 (by rfl) ⟨623348, by rfl⟩ : syracuseStep 831131 = 1246697) B1246697
theorem B798427 : Blo 366759 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B2109179 : Blo 366759 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B831329 : Blo 366759 831329 := bstep (se 2 (by rfl) ⟨311748, by rfl⟩ : syracuseStep 831329 = 623497) B623497
theorem B700319 : Blo 366759 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B700463 : Blo 366759 700463 := bstep (se 1 (by rfl) ⟨525347, by rfl⟩ : syracuseStep 700463 = 1050695) B1050695
theorem B5976251 : Blo 366759 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B700751 : Blo 366759 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B831905 : Blo 366759 831905 := bstep (se 2 (by rfl) ⟨311964, by rfl⟩ : syracuseStep 831905 = 623929) B623929
theorem B2699833 : Blo 366759 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B5321791 : Blo 366759 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B931247 : Blo 366759 931247 := bstep (se 1 (by rfl) ⟨698435, by rfl⟩ : syracuseStep 931247 = 1396871) B1396871
theorem B833759 : Blo 366759 833759 := bstep (se 1 (by rfl) ⟨625319, by rfl⟩ : syracuseStep 833759 = 1250639) B1250639
theorem B702847 : Blo 366759 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B2242991 : Blo 366759 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B349223669 : Blo 366759 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B539959 : Blo 366759 539959 := bstep (se 1 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 539959 = 809939) B809939
theorem B703865 : Blo 366759 703865 := bstep (se 2 (by rfl) ⟨263949, by rfl⟩ : syracuseStep 703865 = 527899) B527899
theorem B934031 : Blo 366759 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B8470919 : Blo 366759 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B1393469 : Blo 366759 1393469 := bstep (se 3 (by rfl) ⟨261275, by rfl⟩ : syracuseStep 1393469 = 522551) B522551
theorem B43763095 : Blo 366759 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B27280793 : Blo 366759 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B1885673 : Blo 366759 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B1328719 : Blo 366759 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B12011399 : Blo 366759 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B5098729 : Blo 366759 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B3165479 : Blo 366759 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B2018849 : Blo 366759 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B1396703 : Blo 366759 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B3364051 : Blo 366759 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1890145 : Blo 366759 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B1857491 : Blo 366759 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B744161 : Blo 366759 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B12016471 : Blo 366759 12016471 := bstep (se 1 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 12016471 = 18024707) B18024707
theorem B5168731 : Blo 366759 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B1401259 : Blo 366759 1401259 := bstep (se 1 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 1401259 = 2101889) B2101889
theorem B1238111 : Blo 366759 1238111 := bstep (se 1 (by rfl) ⟨928583, by rfl⟩ : syracuseStep 1238111 = 1857167) B1857167
theorem B550139 : Blo 366759 550139 := bstep (se 1 (by rfl) ⟨412604, by rfl⟩ : syracuseStep 550139 = 825209) B825209
theorem B550655 : Blo 366759 550655 := bstep (se 1 (by rfl) ⟨412991, by rfl⟩ : syracuseStep 550655 = 825983) B825983
theorem B550727 : Blo 366759 550727 := bstep (se 1 (by rfl) ⟨413045, by rfl⟩ : syracuseStep 550727 = 826091) B826091
theorem B1238921 : Blo 366759 1238921 := bstep (se 2 (by rfl) ⟨464595, by rfl⟩ : syracuseStep 1238921 = 929191) B929191
theorem B550907 : Blo 366759 550907 := bstep (se 1 (by rfl) ⟨413180, by rfl⟩ : syracuseStep 550907 = 826361) B826361
theorem B550967 : Blo 366759 550967 := bstep (se 1 (by rfl) ⟨413225, by rfl⟩ : syracuseStep 550967 = 826451) B826451
theorem B6056045 : Blo 366759 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B551087 : Blo 366759 551087 := bstep (se 1 (by rfl) ⟨413315, by rfl⟩ : syracuseStep 551087 = 826631) B826631
theorem B1566971 : Blo 366759 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B551327 : Blo 366759 551327 := bstep (se 1 (by rfl) ⟨413495, by rfl⟩ : syracuseStep 551327 = 826991) B826991
theorem B551519 : Blo 366759 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B1403507 : Blo 366759 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B551591 : Blo 366759 551591 := bstep (se 1 (by rfl) ⟨413693, by rfl⟩ : syracuseStep 551591 = 827387) B827387
theorem B551657 : Blo 366759 551657 := bstep (se 2 (by rfl) ⟨206871, by rfl⟩ : syracuseStep 551657 = 413743) B413743
theorem B551711 : Blo 366759 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B551879 : Blo 366759 551879 := bstep (se 1 (by rfl) ⟨413909, by rfl⟩ : syracuseStep 551879 = 827819) B827819
theorem B2845655 : Blo 366759 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B551999 : Blo 366759 551999 := bstep (se 1 (by rfl) ⟨413999, by rfl⟩ : syracuseStep 551999 = 827999) B827999
theorem B552191 : Blo 366759 552191 := bstep (se 1 (by rfl) ⟨414143, by rfl⟩ : syracuseStep 552191 = 828287) B828287
theorem B552239 : Blo 366759 552239 := bstep (se 1 (by rfl) ⟨414179, by rfl⟩ : syracuseStep 552239 = 828359) B828359
theorem B552425 : Blo 366759 552425 := bstep (se 2 (by rfl) ⟨207159, by rfl⟩ : syracuseStep 552425 = 414319) B414319
theorem B3534329 : Blo 366759 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B552479 : Blo 366759 552479 := bstep (se 1 (by rfl) ⟨414359, by rfl⟩ : syracuseStep 552479 = 828719) B828719
theorem B14708567 : Blo 366759 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B749675 : Blo 366759 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B1405147 : Blo 366759 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B2978171 : Blo 366759 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B14250491 : Blo 366759 14250491 := bstep (se 1 (by rfl) ⟨10687868, by rfl⟩ : syracuseStep 14250491 = 21375737) B21375737
theorem B1340011 : Blo 366759 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B619177 : Blo 366759 619177 := bstep (se 2 (by rfl) ⟨232191, by rfl⟩ : syracuseStep 619177 = 464383) B464383
theorem B1995587 : Blo 366759 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B36238241 : Blo 366759 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B554111 : Blo 366759 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B5043667 : Blo 366759 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B554495 : Blo 366759 554495 := bstep (se 1 (by rfl) ⟨415871, by rfl⟩ : syracuseStep 554495 = 831743) B831743
theorem B1570387 : Blo 366759 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B1242971 : Blo 366759 1242971 := bstep (se 1 (by rfl) ⟨932228, by rfl⟩ : syracuseStep 1242971 = 1864457) B1864457
theorem B554873 : Blo 366759 554873 := bstep (se 2 (by rfl) ⟨208077, by rfl⟩ : syracuseStep 554873 = 416155) B416155
theorem B1406909 : Blo 366759 1406909 := bstep (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) B527591
theorem B555263 : Blo 366759 555263 := bstep (se 1 (by rfl) ⟨416447, by rfl⟩ : syracuseStep 555263 = 832895) B832895
theorem B5994809 : Blo 366759 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B555401 : Blo 366759 555401 := bstep (se 2 (by rfl) ⟨208275, by rfl⟩ : syracuseStep 555401 = 416551) B416551
theorem B620959 : Blo 366759 620959 := bstep (se 1 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 620959 = 931439) B931439
theorem B621047 : Blo 366759 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B555575 : Blo 366759 555575 := bstep (se 1 (by rfl) ⟨416681, by rfl⟩ : syracuseStep 555575 = 833363) B833363
theorem B555647 : Blo 366759 555647 := bstep (se 1 (by rfl) ⟨416735, by rfl⟩ : syracuseStep 555647 = 833471) B833471
theorem B3144359 : Blo 366759 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B1243835 : Blo 366759 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B556025 : Blo 366759 556025 := bstep (se 2 (by rfl) ⟨208509, by rfl⟩ : syracuseStep 556025 = 417019) B417019
theorem B2096513 : Blo 366759 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B622127 : Blo 366759 622127 := bstep (se 1 (by rfl) ⟨466595, by rfl⟩ : syracuseStep 622127 = 933191) B933191
theorem B2096765 : Blo 366759 2096765 := bstep (se 3 (by rfl) ⟨393143, by rfl⟩ : syracuseStep 2096765 = 786287) B786287
theorem B622687 : Blo 366759 622687 := bstep (se 1 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 622687 = 934031) B934031
theorem B393455 : Blo 366759 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B1999133 : Blo 366759 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B524647 : Blo 366759 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B1868345 : Blo 366759 1868345 := bstep (se 2 (by rfl) ⟨700629, by rfl⟩ : syracuseStep 1868345 = 1401259) B1401259
theorem B4653677 : Blo 366759 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B1868669 : Blo 366759 1868669 := bstep (se 3 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 1868669 = 700751) B700751
theorem B18187195 : Blo 366759 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B5964839 : Blo 366759 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B1050023 : Blo 366759 1050023 := bstep (se 1 (by rfl) ⟨787517, by rfl⟩ : syracuseStep 1050023 = 1575035) B1575035
theorem B1246967 : Blo 366759 1246967 := bstep (se 1 (by rfl) ⟨935225, by rfl⟩ : syracuseStep 1246967 = 1870451) B1870451
theorem B1247291 : Blo 366759 1247291 := bstep (se 1 (by rfl) ⟨935468, by rfl⟩ : syracuseStep 1247291 = 1870937) B1870937
theorem B1771625 : Blo 366759 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B7670051 : Blo 366759 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B1051355 : Blo 366759 1051355 := bstep (se 1 (by rfl) ⟨788516, by rfl⟩ : syracuseStep 1051355 = 1577033) B1577033
theorem B1576007 : Blo 366759 1576007 := bstep (se 1 (by rfl) ⟨1182005, by rfl⟩ : syracuseStep 1576007 = 2364011) B2364011
theorem B1051879 : Blo 366759 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B527671 : Blo 366759 527671 := bstep (se 1 (by rfl) ⟨395753, by rfl⟩ : syracuseStep 527671 = 791507) B791507
theorem B1873529 : Blo 366759 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B825407 : Blo 366759 825407 := bstep (se 1 (by rfl) ⟨619055, by rfl⟩ : syracuseStep 825407 = 1238111) B1238111
theorem B366759 : Blo 366759 366759 := bstep (se 1 (by rfl) ⟨275069, by rfl⟩ : syracuseStep 366759 = 550139) B550139
theorem B825569 : Blo 366759 825569 := bstep (se 2 (by rfl) ⟨309588, by rfl⟩ : syracuseStep 825569 = 619177) B619177
theorem B1186235 : Blo 366759 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B367103 : Blo 366759 367103 := bstep (se 1 (by rfl) ⟨275327, by rfl⟩ : syracuseStep 367103 = 550655) B550655
theorem B367151 : Blo 366759 367151 := bstep (se 1 (by rfl) ⟨275363, by rfl⟩ : syracuseStep 367151 = 550727) B550727
theorem B825947 : Blo 366759 825947 := bstep (se 1 (by rfl) ⟨619460, by rfl⟩ : syracuseStep 825947 = 1238921) B1238921
theorem B367271 : Blo 366759 367271 := bstep (se 1 (by rfl) ⟨275453, by rfl⟩ : syracuseStep 367271 = 550907) B550907
theorem B367311 : Blo 366759 367311 := bstep (se 1 (by rfl) ⟨275483, by rfl⟩ : syracuseStep 367311 = 550967) B550967
theorem B4037363 : Blo 366759 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B367391 : Blo 366759 367391 := bstep (se 1 (by rfl) ⟨275543, by rfl⟩ : syracuseStep 367391 = 551087) B551087
theorem B367551 : Blo 366759 367551 := bstep (se 1 (by rfl) ⟨275663, by rfl⟩ : syracuseStep 367551 = 551327) B551327
theorem B2366471 : Blo 366759 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B367679 : Blo 366759 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B367727 : Blo 366759 367727 := bstep (se 1 (by rfl) ⟨275795, by rfl⟩ : syracuseStep 367727 = 551591) B551591
theorem B367771 : Blo 366759 367771 := bstep (se 1 (by rfl) ⟨275828, by rfl⟩ : syracuseStep 367771 = 551657) B551657
theorem B367807 : Blo 366759 367807 := bstep (se 1 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 367807 = 551711) B551711
theorem B6724889 : Blo 366759 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B367919 : Blo 366759 367919 := bstep (se 1 (by rfl) ⟨275939, by rfl⟩ : syracuseStep 367919 = 551879) B551879
theorem B367999 : Blo 366759 367999 := bstep (se 1 (by rfl) ⟨275999, by rfl⟩ : syracuseStep 367999 = 551999) B551999
theorem B368127 : Blo 366759 368127 := bstep (se 1 (by rfl) ⟨276095, by rfl⟩ : syracuseStep 368127 = 552191) B552191
theorem B368159 : Blo 366759 368159 := bstep (se 1 (by rfl) ⟨276119, by rfl⟩ : syracuseStep 368159 = 552239) B552239
theorem B368283 : Blo 366759 368283 := bstep (se 1 (by rfl) ⟨276212, by rfl⟩ : syracuseStep 368283 = 552425) B552425
theorem B2104987 : Blo 366759 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B368319 : Blo 366759 368319 := bstep (se 1 (by rfl) ⟨276239, by rfl⟩ : syracuseStep 368319 = 552479) B552479
theorem B9805711 : Blo 366759 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B466879 : Blo 366759 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B466975 : Blo 366759 466975 := bstep (se 1 (by rfl) ⟨350231, by rfl⟩ : syracuseStep 466975 = 700463) B700463
theorem B827945 : Blo 366759 827945 := bstep (se 2 (by rfl) ⟨310479, by rfl⟩ : syracuseStep 827945 = 620959) B620959
theorem B24158827 : Blo 366759 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B369407 : Blo 366759 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B795433 : Blo 366759 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B369663 : Blo 366759 369663 := bstep (se 1 (by rfl) ⟨277247, by rfl⟩ : syracuseStep 369663 = 554495) B554495
theorem B828647 : Blo 366759 828647 := bstep (se 1 (by rfl) ⟨621485, by rfl⟩ : syracuseStep 828647 = 1242971) B1242971
theorem B369915 : Blo 366759 369915 := bstep (se 1 (by rfl) ⟨277436, by rfl⟩ : syracuseStep 369915 = 554873) B554873
theorem B5383597 : Blo 366759 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B370175 : Blo 366759 370175 := bstep (se 1 (by rfl) ⟨277631, by rfl⟩ : syracuseStep 370175 = 555263) B555263
theorem B370267 : Blo 366759 370267 := bstep (se 1 (by rfl) ⟨277700, by rfl⟩ : syracuseStep 370267 = 555401) B555401
theorem B370383 : Blo 366759 370383 := bstep (se 1 (by rfl) ⟨277787, by rfl⟩ : syracuseStep 370383 = 555575) B555575
theorem B370431 : Blo 366759 370431 := bstep (se 1 (by rfl) ⟨277823, by rfl⟩ : syracuseStep 370431 = 555647) B555647
theorem B829223 : Blo 366759 829223 := bstep (se 1 (by rfl) ⟨621917, by rfl⟩ : syracuseStep 829223 = 1243835) B1243835
theorem B370683 : Blo 366759 370683 := bstep (se 1 (by rfl) ⟨278012, by rfl⟩ : syracuseStep 370683 = 556025) B556025
theorem B6891641 : Blo 366759 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B469243 : Blo 366759 469243 := bstep (se 1 (by rfl) ⟨351932, by rfl⟩ : syracuseStep 469243 = 703865) B703865
theorem B5647279 : Blo 366759 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B928979 : Blo 366759 928979 := bstep (se 1 (by rfl) ⟨696734, by rfl⟩ : syracuseStep 928979 = 1393469) B1393469
theorem B830879 : Blo 366759 830879 := bstep (se 1 (by rfl) ⟨623159, by rfl⟩ : syracuseStep 830879 = 1246319) B1246319
theorem B1257115 : Blo 366759 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B8007599 : Blo 366759 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B2110319 : Blo 366759 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B832481 : Blo 366759 832481 := bstep (se 2 (by rfl) ⟨312180, by rfl⟩ : syracuseStep 832481 = 624361) B624361
theorem B832607 : Blo 366759 832607 := bstep (se 1 (by rfl) ⟨624455, by rfl⟩ : syracuseStep 832607 = 1248911) B1248911
theorem B832823 : Blo 366759 832823 := bstep (se 1 (by rfl) ⟨624617, by rfl⟩ : syracuseStep 832823 = 1249235) B1249235
theorem B931135 : Blo 366759 931135 := bstep (se 1 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 931135 = 1396703) B1396703
theorem B2242313 : Blo 366759 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B2012953 : Blo 366759 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B833435 : Blo 366759 833435 := bstep (se 1 (by rfl) ⟨625076, by rfl⟩ : syracuseStep 833435 = 1250153) B1250153
theorem B374951 : Blo 366759 374951 := bstep (se 1 (by rfl) ⟨281213, by rfl⟩ : syracuseStep 374951 = 562427) B562427
theorem B3160457 : Blo 366759 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B6798305 : Blo 366759 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B5291345 : Blo 366759 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B1064569 : Blo 366759 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B1786681 : Blo 366759 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B5981309 : Blo 366759 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B7095721 : Blo 366759 7095721 := bstep (se 2 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 7095721 = 5321791) B5321791
theorem B935671 : Blo 366759 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B1984429 : Blo 366759 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B12503321 : Blo 366759 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B3984167 : Blo 366759 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B1985447 : Blo 366759 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B937129 : Blo 366759 937129 := bstep (se 2 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 937129 = 702847) B702847
theorem B1330391 : Blo 366759 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B937939 : Blo 366759 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B414031 : Blo 366759 414031 := bstep (se 1 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 414031 = 621047) B621047
theorem B10080773 : Blo 366759 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B1397675 : Blo 366759 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B414751 : Blo 366759 414751 := bstep (se 1 (by rfl) ⟨311063, by rfl⟩ : syracuseStep 414751 = 622127) B622127
theorem B1397843 : Blo 366759 1397843 := bstep (se 1 (by rfl) ⟨1048382, by rfl⟩ : syracuseStep 1397843 = 2096765) B2096765
theorem B415615 : Blo 366759 415615 := bstep (se 1 (by rfl) ⟨311711, by rfl⟩ : syracuseStep 415615 = 623423) B623423
theorem B58350793 : Blo 366759 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B1401245 : Blo 366759 1401245 := bstep (se 3 (by rfl) ⟨262733, by rfl⟩ : syracuseStep 1401245 = 525467) B525467
theorem B1238327 : Blo 366759 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B551231 : Blo 366759 551231 := bstep (se 1 (by rfl) ⟨413423, by rfl⟩ : syracuseStep 551231 = 826847) B826847
theorem B1862351 : Blo 366759 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B551663 : Blo 366759 551663 := bstep (se 1 (by rfl) ⟨413747, by rfl⟩ : syracuseStep 551663 = 827495) B827495
theorem B1403963 : Blo 366759 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B3599777 : Blo 366759 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B421583 : Blo 366759 421583 := bstep (se 1 (by rfl) ⟨316187, by rfl⟩ : syracuseStep 421583 = 632375) B632375
theorem B553067 : Blo 366759 553067 := bstep (se 1 (by rfl) ⟨414800, by rfl⟩ : syracuseStep 553067 = 829601) B829601
theorem B1044647 : Blo 366759 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B4485401 : Blo 366759 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B1864295 : Blo 366759 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B1897103 : Blo 366759 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B2093849 : Blo 366759 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B2356219 : Blo 366759 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B554087 : Blo 366759 554087 := bstep (se 1 (by rfl) ⟨415565, by rfl⟩ : syracuseStep 554087 = 831131) B831131
theorem B1406119 : Blo 366759 1406119 := bstep (se 1 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 1406119 = 2109179) B2109179
theorem B554219 : Blo 366759 554219 := bstep (se 1 (by rfl) ⟨415664, by rfl⟩ : syracuseStep 554219 = 831329) B831329
theorem B554603 : Blo 366759 554603 := bstep (se 1 (by rfl) ⟨415952, by rfl⟩ : syracuseStep 554603 = 831905) B831905
theorem B9500327 : Blo 366759 9500327 := bstep (se 1 (by rfl) ⟨7125245, by rfl⟩ : syracuseStep 9500327 = 14250491) B14250491
theorem B620831 : Blo 366759 620831 := bstep (se 1 (by rfl) ⟨465623, by rfl⟩ : syracuseStep 620831 = 931247) B931247
theorem B16021961 : Blo 366759 16021961 := bstep (se 2 (by rfl) ⟨6008235, by rfl⟩ : syracuseStep 16021961 = 12016471) B12016471
theorem B555839 : Blo 366759 555839 := bstep (se 1 (by rfl) ⟨416879, by rfl⟩ : syracuseStep 555839 = 833759) B833759
theorem B3996539 : Blo 366759 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B719945 : Blo 366759 719945 := bstep (se 2 (by rfl) ⟨269979, by rfl⟩ : syracuseStep 719945 = 539959) B539959
theorem B2096239 : Blo 366759 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B232815779 : Blo 366759 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B622633 : Blo 366759 622633 := bstep (se 2 (by rfl) ⟨233487, by rfl⟩ : syracuseStep 622633 = 466975) B466975
theorem B1245563 : Blo 366759 1245563 := bstep (se 1 (by rfl) ⟨934172, by rfl⟩ : syracuseStep 1245563 = 1868345) B1868345
theorem B1245779 : Blo 366759 1245779 := bstep (se 1 (by rfl) ⟨934334, by rfl⟩ : syracuseStep 1245779 = 1868669) B1868669
theorem B1049213 : Blo 366759 1049213 := bstep (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) B393455
theorem B32211769 : Blo 366759 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B24249593 : Blo 366759 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B1181083 : Blo 366759 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B5113367 : Blo 366759 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B7178129 : Blo 366759 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B1050671 : Blo 366759 1050671 := bstep (se 1 (by rfl) ⟨788003, by rfl⟩ : syracuseStep 1050671 = 1576007) B1576007
theorem B1247561 : Blo 366759 1247561 := bstep (se 2 (by rfl) ⟨467835, by rfl⟩ : syracuseStep 1247561 = 935671) B935671
theorem B625657 : Blo 366759 625657 := bstep (se 2 (by rfl) ⟨234621, by rfl⟩ : syracuseStep 625657 = 469243) B469243
theorem B6720515 : Blo 366759 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B1249019 : Blo 366759 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B1249505 : Blo 366759 1249505 := bstep (se 2 (by rfl) ⟨468564, by rfl⟩ : syracuseStep 1249505 = 937129) B937129
theorem B790823 : Blo 366759 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B2691575 : Blo 366759 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B1577647 : Blo 366759 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B1676153 : Blo 366759 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B1250585 : Blo 366759 1250585 := bstep (se 2 (by rfl) ⟨468969, by rfl⟩ : syracuseStep 1250585 = 937939) B937939
theorem B825551 : Blo 366759 825551 := bstep (se 1 (by rfl) ⟨619163, by rfl⟩ : syracuseStep 825551 = 1238327) B1238327
theorem B4594427 : Blo 366759 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B367487 : Blo 366759 367487 := bstep (se 1 (by rfl) ⟨275615, by rfl⟩ : syracuseStep 367487 = 551231) B551231
theorem B1874825 : Blo 366759 1874825 := bstep (se 2 (by rfl) ⟨703059, by rfl⟩ : syracuseStep 1874825 = 1406119) B1406119
theorem B367775 : Blo 366759 367775 := bstep (se 1 (by rfl) ⟨275831, by rfl⟩ : syracuseStep 367775 = 551663) B551663
theorem B10624445 : Blo 366759 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B2399851 : Blo 366759 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B368711 : Blo 366759 368711 := bstep (se 1 (by rfl) ⟨276533, by rfl⟩ : syracuseStep 368711 = 553067) B553067
theorem B696431 : Blo 366759 696431 := bstep (se 1 (by rfl) ⟨522323, by rfl⟩ : syracuseStep 696431 = 1044647) B1044647
theorem B2990267 : Blo 366759 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B3547709 : Blo 366759 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B369391 : Blo 366759 369391 := bstep (se 1 (by rfl) ⟨277043, by rfl⟩ : syracuseStep 369391 = 554087) B554087
theorem B369479 : Blo 366759 369479 := bstep (se 1 (by rfl) ⟨277109, by rfl⟩ : syracuseStep 369479 = 554219) B554219
theorem B369735 : Blo 366759 369735 := bstep (se 1 (by rfl) ⟨277301, by rfl⟩ : syracuseStep 369735 = 554603) B554603
theorem B6333551 : Blo 366759 6333551 := bstep (se 1 (by rfl) ⟨4750163, by rfl⟩ : syracuseStep 6333551 = 9500327) B9500327
theorem B2794985 : Blo 366759 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B2106971 : Blo 366759 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B77801057 : Blo 366759 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B1124221 : Blo 366759 1124221 := bstep (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) B421583
theorem B370559 : Blo 366759 370559 := bstep (se 1 (by rfl) ⟨277919, by rfl⟩ : syracuseStep 370559 = 555839) B555839
theorem B2664359 : Blo 366759 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B4532203 : Blo 366759 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B1419425 : Blo 366759 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B830249 : Blo 366759 830249 := bstep (se 2 (by rfl) ⟨311343, by rfl⟩ : syracuseStep 830249 = 622687) B622687
theorem B699529 : Blo 366759 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B3976559 : Blo 366759 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B700015 : Blo 366759 700015 := bstep (se 1 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 700015 = 1050023) B1050023
theorem B1060577 : Blo 366759 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B831311 : Blo 366759 831311 := bstep (se 1 (by rfl) ⟨623483, by rfl⟩ : syracuseStep 831311 = 1246967) B1246967
theorem B831527 : Blo 366759 831527 := bstep (se 1 (by rfl) ⟨623645, by rfl⟩ : syracuseStep 831527 = 1247291) B1247291
theorem B8335547 : Blo 366759 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B5058941 : Blo 366759 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B700903 : Blo 366759 700903 := bstep (se 1 (by rfl) ⟨525677, by rfl⟩ : syracuseStep 700903 = 1051355) B1051355
theorem B1323631 : Blo 366759 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B931783 : Blo 366759 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B931895 : Blo 366759 931895 := bstep (se 1 (by rfl) ⟨698921, by rfl⟩ : syracuseStep 931895 = 1397843) B1397843
theorem B703561 : Blo 366759 703561 := bstep (se 2 (by rfl) ⟨263835, by rfl⟩ : syracuseStep 703561 = 527671) B527671
theorem B934163 : Blo 366759 934163 := bstep (se 1 (by rfl) ⟨700622, by rfl⟩ : syracuseStep 934163 = 1401245) B1401245
theorem B999869 : Blo 366759 999869 := bstep (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) B374951
theorem B935975 : Blo 366759 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B1395899 : Blo 366759 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B1494875 : Blo 366759 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B413887 : Blo 366759 413887 := bstep (se 1 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 413887 = 620831) B620831
theorem B479963 : Blo 366759 479963 := bstep (se 1 (by rfl) ⟨359972, by rfl⟩ : syracuseStep 479963 = 719945) B719945
theorem B155210519 : Blo 366759 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B2806649 : Blo 366759 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B3527563 : Blo 366759 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B1332755 : Blo 366759 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B3987539 : Blo 366759 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B12409805 : Blo 366759 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B9460961 : Blo 366759 9460961 := bstep (se 2 (by rfl) ⟨3547860, by rfl⟩ : syracuseStep 9460961 = 7095721) B7095721
theorem B2645905 : Blo 366759 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B7529705 : Blo 366759 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B550271 : Blo 366759 550271 := bstep (se 1 (by rfl) ⟨412703, by rfl⟩ : syracuseStep 550271 = 825407) B825407
theorem B550379 : Blo 366759 550379 := bstep (se 1 (by rfl) ⟨412784, by rfl⟩ : syracuseStep 550379 = 825569) B825569
theorem B9528965 : Blo 366759 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B1402505 : Blo 366759 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B550631 : Blo 366759 550631 := bstep (se 1 (by rfl) ⟨412973, by rfl⟩ : syracuseStep 550631 = 825947) B825947
theorem B4483259 : Blo 366759 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B551963 : Blo 366759 551963 := bstep (se 1 (by rfl) ⟨413972, by rfl⟩ : syracuseStep 551963 = 827945) B827945
theorem B552041 : Blo 366759 552041 := bstep (se 2 (by rfl) ⟨207015, by rfl⟩ : syracuseStep 552041 = 414031) B414031
theorem B552431 : Blo 366759 552431 := bstep (se 1 (by rfl) ⟨414323, by rfl⟩ : syracuseStep 552431 = 828647) B828647
theorem B552815 : Blo 366759 552815 := bstep (se 1 (by rfl) ⟨414611, by rfl⟩ : syracuseStep 552815 = 829223) B829223
theorem B3141625 : Blo 366759 3141625 := bstep (se 2 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 3141625 = 2356219) B2356219
theorem B553001 : Blo 366759 553001 := bstep (se 2 (by rfl) ⟨207375, by rfl⟩ : syracuseStep 553001 = 414751) B414751
theorem B1241513 : Blo 366759 1241513 := bstep (se 2 (by rfl) ⟨465567, by rfl⟩ : syracuseStep 1241513 = 931135) B931135
theorem B1241567 : Blo 366759 1241567 := bstep (se 1 (by rfl) ⟨931175, by rfl⟩ : syracuseStep 1241567 = 1862351) B1862351
theorem B619319 : Blo 366759 619319 := bstep (se 1 (by rfl) ⟨464489, by rfl⟩ : syracuseStep 619319 = 928979) B928979
theorem B553919 : Blo 366759 553919 := bstep (se 1 (by rfl) ⟨415439, by rfl⟩ : syracuseStep 553919 = 830879) B830879
theorem B2683937 : Blo 366759 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B554153 : Blo 366759 554153 := bstep (se 2 (by rfl) ⟨207807, by rfl⟩ : syracuseStep 554153 = 415615) B415615
theorem B5338399 : Blo 366759 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B1242863 : Blo 366759 1242863 := bstep (se 1 (by rfl) ⟨932147, by rfl⟩ : syracuseStep 1242863 = 1864295) B1864295
theorem B1406879 : Blo 366759 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B554987 : Blo 366759 554987 := bstep (se 1 (by rfl) ⟨416240, by rfl⟩ : syracuseStep 554987 = 832481) B832481
theorem B555071 : Blo 366759 555071 := bstep (se 1 (by rfl) ⟨416303, by rfl⟩ : syracuseStep 555071 = 832607) B832607
theorem B555215 : Blo 366759 555215 := bstep (se 1 (by rfl) ⟨416411, by rfl⟩ : syracuseStep 555215 = 832823) B832823
theorem B555623 : Blo 366759 555623 := bstep (se 1 (by rfl) ⟨416717, by rfl⟩ : syracuseStep 555623 = 833435) B833435
theorem B10681307 : Blo 366759 10681307 := bstep (se 1 (by rfl) ⟨8010980, by rfl⟩ : syracuseStep 10681307 = 16021961) B16021961
theorem B13074281 : Blo 366759 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B622505 : Blo 366759 622505 := bstep (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) B466879
theorem B622775 : Blo 366759 622775 := bstep (se 1 (by rfl) ⟨467081, by rfl⟩ : syracuseStep 622775 = 934163) B934163
theorem B3408911 : Blo 366759 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B4785419 : Blo 366759 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B623983 : Blo 366759 623983 := bstep (se 1 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 623983 = 935975) B935975
theorem B15140533 : Blo 366759 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B1574777 : Blo 366759 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B1279901 : Blo 366759 1279901 := bstep (se 3 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 1279901 = 479963) B479963
theorem B413894717 : Blo 366759 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B1117435 : Blo 366759 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B1871099 : Blo 366759 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B888503 : Blo 366759 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B2658359 : Blo 366759 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B1249883 : Blo 366759 1249883 := bstep (se 1 (by rfl) ⟨937412, by rfl⟩ : syracuseStep 1249883 = 1874825) B1874825
theorem B7082963 : Blo 366759 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B464287 : Blo 366759 464287 := bstep (se 1 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 464287 = 696431) B696431
theorem B2365139 : Blo 366759 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B5019803 : Blo 366759 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B2103529 : Blo 366759 2103529 := bstep (se 2 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 2103529 = 1577647) B1577647
theorem B366847 : Blo 366759 366847 := bstep (se 1 (by rfl) ⟨275135, by rfl⟩ : syracuseStep 366847 = 550271) B550271
theorem B366919 : Blo 366759 366919 := bstep (se 1 (by rfl) ⟨275189, by rfl⟩ : syracuseStep 366919 = 550379) B550379
theorem B367087 : Blo 366759 367087 := bstep (se 1 (by rfl) ⟨275315, by rfl⟩ : syracuseStep 367087 = 550631) B550631
theorem B1776239 : Blo 366759 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B2988839 : Blo 366759 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B7117865 : Blo 366759 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B367975 : Blo 366759 367975 := bstep (se 1 (by rfl) ⟨275981, by rfl⟩ : syracuseStep 367975 = 551963) B551963
theorem B368027 : Blo 366759 368027 := bstep (se 1 (by rfl) ⟨276020, by rfl⟩ : syracuseStep 368027 = 552041) B552041
theorem B368287 : Blo 366759 368287 := bstep (se 1 (by rfl) ⟨276215, by rfl⟩ : syracuseStep 368287 = 552431) B552431
theorem B368543 : Blo 366759 368543 := bstep (se 1 (by rfl) ⟨276407, by rfl⟩ : syracuseStep 368543 = 552815) B552815
theorem B368667 : Blo 366759 368667 := bstep (se 1 (by rfl) ⟨276500, by rfl⟩ : syracuseStep 368667 = 553001) B553001
theorem B827675 : Blo 366759 827675 := bstep (se 1 (by rfl) ⟨620756, by rfl⟩ : syracuseStep 827675 = 1241513) B1241513
theorem B827711 : Blo 366759 827711 := bstep (se 1 (by rfl) ⟨620783, by rfl⟩ : syracuseStep 827711 = 1241567) B1241567
theorem B369279 : Blo 366759 369279 := bstep (se 1 (by rfl) ⟨276959, by rfl⟩ : syracuseStep 369279 = 553919) B553919
theorem B369435 : Blo 366759 369435 := bstep (se 1 (by rfl) ⟨277076, by rfl⟩ : syracuseStep 369435 = 554153) B554153
theorem B828575 : Blo 366759 828575 := bstep (se 1 (by rfl) ⟨621431, by rfl⟩ : syracuseStep 828575 = 1242863) B1242863
theorem B369991 : Blo 366759 369991 := bstep (se 1 (by rfl) ⟨277493, by rfl⟩ : syracuseStep 369991 = 554987) B554987
theorem B370047 : Blo 366759 370047 := bstep (se 1 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 370047 = 555071) B555071
theorem B370143 : Blo 366759 370143 := bstep (se 1 (by rfl) ⟨277607, by rfl⟩ : syracuseStep 370143 = 555215) B555215
theorem B370415 : Blo 366759 370415 := bstep (se 1 (by rfl) ⟨277811, by rfl⟩ : syracuseStep 370415 = 555623) B555623
theorem B7120871 : Blo 366759 7120871 := bstep (se 1 (by rfl) ⟨5340653, by rfl⟩ : syracuseStep 7120871 = 10681307) B10681307
theorem B830177 : Blo 366759 830177 := bstep (se 2 (by rfl) ⟨311316, by rfl⟩ : syracuseStep 830177 = 622633) B622633
theorem B830375 : Blo 366759 830375 := bstep (se 1 (by rfl) ⟨622781, by rfl⟩ : syracuseStep 830375 = 1245563) B1245563
theorem B830519 : Blo 366759 830519 := bstep (se 1 (by rfl) ⟨622889, by rfl⟩ : syracuseStep 830519 = 1245779) B1245779
theorem B2108861 : Blo 366759 2108861 := bstep (se 3 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 2108861 = 790823) B790823
theorem B16166395 : Blo 366759 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B831707 : Blo 366759 831707 := bstep (se 1 (by rfl) ⟨623780, by rfl⟩ : syracuseStep 831707 = 1247561) B1247561
theorem B2797901 : Blo 366759 2797901 := bstep (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) B1049213
theorem B930599 : Blo 366759 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B832679 : Blo 366759 832679 := bstep (se 1 (by rfl) ⟨624509, by rfl⟩ : syracuseStep 832679 = 1249019) B1249019
theorem B6042937 : Blo 366759 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B833003 : Blo 366759 833003 := bstep (se 1 (by rfl) ⟨624752, by rfl⟩ : syracuseStep 833003 = 1249505) B1249505
theorem B833723 : Blo 366759 833723 := bstep (se 1 (by rfl) ⟨625292, by rfl⟩ : syracuseStep 833723 = 1250585) B1250585
theorem B834209 : Blo 366759 834209 := bstep (se 2 (by rfl) ⟨312828, by rfl⟩ : syracuseStep 834209 = 625657) B625657
theorem B932705 : Blo 366759 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B3062951 : Blo 366759 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B10665269 : Blo 366759 10665269 := bstep (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) B999869
theorem B933353 : Blo 366759 933353 := bstep (se 2 (by rfl) ⟨350007, by rfl⟩ : syracuseStep 933353 = 700015) B700015
theorem B6307307 : Blo 366759 6307307 := bstep (se 1 (by rfl) ⟨4730480, by rfl⟩ : syracuseStep 6307307 = 9460961) B9460961
theorem B2801789 : Blo 366759 2801789 := bstep (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) B1050671
theorem B934537 : Blo 366759 934537 := bstep (se 2 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 934537 = 700903) B700903
theorem B935003 : Blo 366759 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B4703417 : Blo 366759 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B707051 : Blo 366759 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B5557031 : Blo 366759 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B412879 : Blo 366759 412879 := bstep (se 1 (by rfl) ⟨309659, by rfl⟩ : syracuseStep 412879 = 619319) B619319
theorem B12799205 : Blo 366759 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B1789291 : Blo 366759 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B937919 : Blo 366759 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B938081 : Blo 366759 938081 := bstep (se 2 (by rfl) ⟨351780, by rfl⟩ : syracuseStep 938081 = 703561) B703561
theorem B3986333 : Blo 366759 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B3527873 : Blo 366759 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B415003 : Blo 366759 415003 := bstep (se 1 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 415003 = 622505) B622505
theorem B13490509 : Blo 366759 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B42949025 : Blo 366759 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B4480343 : Blo 366759 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B1498961 : Blo 366759 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1794383 : Blo 366759 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B550367 : Blo 366759 550367 := bstep (se 1 (by rfl) ⟨412775, by rfl⟩ : syracuseStep 550367 = 825551) B825551
theorem B4188833 : Blo 366759 4188833 := bstep (se 2 (by rfl) ⟨1570812, by rfl⟩ : syracuseStep 4188833 = 3141625) B3141625
theorem B1993511 : Blo 366759 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B551849 : Blo 366759 551849 := bstep (se 2 (by rfl) ⟨206943, by rfl⟩ : syracuseStep 551849 = 413887) B413887
theorem B4222367 : Blo 366759 4222367 := bstep (se 1 (by rfl) ⟨3166775, by rfl⟩ : syracuseStep 4222367 = 6333551) B6333551
theorem B1764841 : Blo 366759 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B1863323 : Blo 366759 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B1404647 : Blo 366759 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B51867371 : Blo 366759 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B6352643 : Blo 366759 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B553499 : Blo 366759 553499 := bstep (se 1 (by rfl) ⟨415124, by rfl⟩ : syracuseStep 553499 = 830249) B830249
theorem B2651039 : Blo 366759 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B33092813 : Blo 366759 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B554207 : Blo 366759 554207 := bstep (se 1 (by rfl) ⟨415655, by rfl⟩ : syracuseStep 554207 = 831311) B831311
theorem B1242377 : Blo 366759 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B554351 : Blo 366759 554351 := bstep (se 1 (by rfl) ⟨415763, by rfl⟩ : syracuseStep 554351 = 831527) B831527
theorem B621263 : Blo 366759 621263 := bstep (se 1 (by rfl) ⟨465947, by rfl⟩ : syracuseStep 621263 = 931895) B931895
theorem B8716187 : Blo 366759 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B1867859 : Blo 366759 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B623335 : Blo 366759 623335 := bstep (se 1 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 623335 = 935003) B935003
theorem B1246049 : Blo 366759 1246049 := bstep (se 2 (by rfl) ⟨467268, by rfl⟩ : syracuseStep 1246049 = 934537) B934537
theorem B1049851 : Blo 366759 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B853267 : Blo 366759 853267 := bstep (se 1 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 853267 = 1279901) B1279901
theorem B3704687 : Blo 366759 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B1247399 : Blo 366759 1247399 := bstep (se 1 (by rfl) ⟨935549, by rfl⟩ : syracuseStep 1247399 = 1871099) B1871099
theorem B20187377 : Blo 366759 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B625279 : Blo 366759 625279 := bstep (se 1 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 625279 = 937919) B937919
theorem B625387 : Blo 366759 625387 := bstep (se 1 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 625387 = 938081) B938081
theorem B88247501 : Blo 366759 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2657555 : Blo 366759 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B4721975 : Blo 366759 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B1576759 : Blo 366759 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B3346535 : Blo 366759 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B1184159 : Blo 366759 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B2986895 : Blo 366759 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B366911 : Blo 366759 366911 := bstep (se 1 (by rfl) ⟨275183, by rfl⟩ : syracuseStep 366911 = 550367) B550367
theorem B2792555 : Blo 366759 2792555 := bstep (se 1 (by rfl) ⟨2094416, by rfl⟩ : syracuseStep 2792555 = 4188833) B4188833
theorem B367899 : Blo 366759 367899 := bstep (se 1 (by rfl) ⟨275924, by rfl⟩ : syracuseStep 367899 = 551849) B551849
theorem B5316029 : Blo 366759 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B34578247 : Blo 366759 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B4235095 : Blo 366759 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B368999 : Blo 366759 368999 := bstep (se 1 (by rfl) ⟨276749, by rfl⟩ : syracuseStep 368999 = 553499) B553499
theorem B369471 : Blo 366759 369471 := bstep (se 1 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 369471 = 554207) B554207
theorem B828251 : Blo 366759 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B369567 : Blo 366759 369567 := bstep (se 1 (by rfl) ⟨277175, by rfl⟩ : syracuseStep 369567 = 554351) B554351
theorem B2369341 : Blo 366759 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B2041967 : Blo 366759 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B4204871 : Blo 366759 4204871 := bstep (se 1 (by rfl) ⟨3153653, by rfl⟩ : syracuseStep 4204871 = 6307307) B6307307
theorem B5810791 : Blo 366759 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B7088957 : Blo 366759 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B2272607 : Blo 366759 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B3190279 : Blo 366759 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B471367 : Blo 366759 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B831977 : Blo 366759 831977 := bstep (se 2 (by rfl) ⟨311991, by rfl⟩ : syracuseStep 831977 = 623983) B623983
theorem B8532803 : Blo 366759 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B833255 : Blo 366759 833255 := bstep (se 1 (by rfl) ⟨624941, by rfl⟩ : syracuseStep 833255 = 1249883) B1249883
theorem B1489913 : Blo 366759 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B999307 : Blo 366759 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B1196255 : Blo 366759 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B936431 : Blo 366759 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B2804705 : Blo 366759 2804705 := bstep (se 2 (by rfl) ⟨1051764, by rfl⟩ : syracuseStep 2804705 = 2103529) B2103529
theorem B414175 : Blo 366759 414175 := bstep (se 1 (by rfl) ⟨310631, by rfl⟩ : syracuseStep 414175 = 621263) B621263
theorem B415183 : Blo 366759 415183 := bstep (se 1 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 415183 = 622775) B622775
theorem B3135611 : Blo 366759 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B275929811 : Blo 366759 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B2351915 : Blo 366759 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B550505 : Blo 366759 550505 := bstep (se 2 (by rfl) ⟨206439, by rfl⟩ : syracuseStep 550505 = 412879) B412879
theorem B28632683 : Blo 366759 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B2385721 : Blo 366759 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B1992559 : Blo 366759 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B2353121 : Blo 366759 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B21555193 : Blo 366759 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B4745243 : Blo 366759 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B551783 : Blo 366759 551783 := bstep (se 1 (by rfl) ⟨413837, by rfl⟩ : syracuseStep 551783 = 827675) B827675
theorem B551807 : Blo 366759 551807 := bstep (se 1 (by rfl) ⟨413855, by rfl⟩ : syracuseStep 551807 = 827711) B827711
theorem B552383 : Blo 366759 552383 := bstep (se 1 (by rfl) ⟨414287, by rfl⟩ : syracuseStep 552383 = 828575) B828575
theorem B4747247 : Blo 366759 4747247 := bstep (se 1 (by rfl) ⟨3560435, by rfl⟩ : syracuseStep 4747247 = 7120871) B7120871
theorem B553337 : Blo 366759 553337 := bstep (se 2 (by rfl) ⟨207501, by rfl⟩ : syracuseStep 553337 = 415003) B415003
theorem B8057249 : Blo 366759 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B553451 : Blo 366759 553451 := bstep (se 1 (by rfl) ⟨415088, by rfl⟩ : syracuseStep 553451 = 830177) B830177
theorem B619049 : Blo 366759 619049 := bstep (se 2 (by rfl) ⟨232143, by rfl⟩ : syracuseStep 619049 = 464287) B464287
theorem B553583 : Blo 366759 553583 := bstep (se 1 (by rfl) ⟨415187, by rfl⟩ : syracuseStep 553583 = 830375) B830375
theorem B553679 : Blo 366759 553679 := bstep (se 1 (by rfl) ⟨415259, by rfl⟩ : syracuseStep 553679 = 830519) B830519
theorem B2814911 : Blo 366759 2814911 := bstep (se 1 (by rfl) ⟨2111183, by rfl⟩ : syracuseStep 2814911 = 4222367) B4222367
theorem B1405907 : Blo 366759 1405907 := bstep (se 1 (by rfl) ⟨1054430, by rfl⟩ : syracuseStep 1405907 = 2108861) B2108861
theorem B1242215 : Blo 366759 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B554471 : Blo 366759 554471 := bstep (se 1 (by rfl) ⟨415853, by rfl⟩ : syracuseStep 554471 = 831707) B831707
theorem B1865267 : Blo 366759 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B17987345 : Blo 366759 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B620399 : Blo 366759 620399 := bstep (se 1 (by rfl) ⟨465299, by rfl⟩ : syracuseStep 620399 = 930599) B930599
theorem B1767359 : Blo 366759 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B555119 : Blo 366759 555119 := bstep (se 1 (by rfl) ⟨416339, by rfl⟩ : syracuseStep 555119 = 832679) B832679
theorem B555335 : Blo 366759 555335 := bstep (se 1 (by rfl) ⟨416501, by rfl⟩ : syracuseStep 555335 = 833003) B833003
theorem B555815 : Blo 366759 555815 := bstep (se 1 (by rfl) ⟨416861, by rfl⟩ : syracuseStep 555815 = 833723) B833723
theorem B556139 : Blo 366759 556139 := bstep (se 1 (by rfl) ⟨417104, by rfl⟩ : syracuseStep 556139 = 834209) B834209
theorem B621803 : Blo 366759 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B7110179 : Blo 366759 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B622235 : Blo 366759 622235 := bstep (se 1 (by rfl) ⟨466676, by rfl⟩ : syracuseStep 622235 = 933353) B933353
theorem B1245239 : Blo 366759 1245239 := bstep (se 1 (by rfl) ⟨933929, by rfl⟩ : syracuseStep 1245239 = 1867859) B1867859
theorem B624287 : Blo 366759 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B1869803 : Blo 366759 1869803 := bstep (se 1 (by rfl) ⟨1402352, by rfl⟩ : syracuseStep 1869803 = 2804705) B2804705
theorem B1771703 : Blo 366759 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B3147983 : Blo 366759 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B7965053 : Blo 366759 7965053 := bstep (se 3 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 7965053 = 2986895) B2986895
theorem B3180961 : Blo 366759 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B2656745 : Blo 366759 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B28740257 : Blo 366759 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B2231023 : Blo 366759 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B789439 : Blo 366759 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B3544019 : Blo 366759 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B2102345 : Blo 366759 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B5445245 : Blo 366759 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B628489 : Blo 366759 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B367003 : Blo 366759 367003 := bstep (se 1 (by rfl) ⟨275252, by rfl⟩ : syracuseStep 367003 = 550505) B550505
theorem B4725971 : Blo 366759 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B367855 : Blo 366759 367855 := bstep (se 1 (by rfl) ⟨275891, by rfl⟩ : syracuseStep 367855 = 551783) B551783
theorem B367871 : Blo 366759 367871 := bstep (se 1 (by rfl) ⟨275903, by rfl⟩ : syracuseStep 367871 = 551807) B551807
theorem B1515071 : Blo 366759 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B368255 : Blo 366759 368255 := bstep (se 1 (by rfl) ⟨276191, by rfl⟩ : syracuseStep 368255 = 552383) B552383
theorem B368891 : Blo 366759 368891 := bstep (se 1 (by rfl) ⟨276668, by rfl⟩ : syracuseStep 368891 = 553337) B553337
theorem B368967 : Blo 366759 368967 := bstep (se 1 (by rfl) ⟨276725, by rfl⟩ : syracuseStep 368967 = 553451) B553451
theorem B369055 : Blo 366759 369055 := bstep (se 1 (by rfl) ⟨276791, by rfl⟩ : syracuseStep 369055 = 553583) B553583
theorem B369119 : Blo 366759 369119 := bstep (se 1 (by rfl) ⟨276839, by rfl⟩ : syracuseStep 369119 = 553679) B553679
theorem B1876607 : Blo 366759 1876607 := bstep (se 1 (by rfl) ⟨1407455, by rfl⟩ : syracuseStep 1876607 = 2814911) B2814911
theorem B828143 : Blo 366759 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B369647 : Blo 366759 369647 := bstep (se 1 (by rfl) ⟨277235, by rfl⟩ : syracuseStep 369647 = 554471) B554471
theorem B370079 : Blo 366759 370079 := bstep (se 1 (by rfl) ⟨277559, by rfl⟩ : syracuseStep 370079 = 555119) B555119
theorem B370223 : Blo 366759 370223 := bstep (se 1 (by rfl) ⟨277667, by rfl⟩ : syracuseStep 370223 = 555335) B555335
theorem B370543 : Blo 366759 370543 := bstep (se 1 (by rfl) ⟨277907, by rfl⟩ : syracuseStep 370543 = 555815) B555815
theorem B993275 : Blo 366759 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B370759 : Blo 366759 370759 := bstep (se 1 (by rfl) ⟨278069, by rfl⟩ : syracuseStep 370759 = 556139) B556139
theorem B5646793 : Blo 366759 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B830699 : Blo 366759 830699 := bstep (se 1 (by rfl) ⟨623024, by rfl⟩ : syracuseStep 830699 = 1246049) B1246049
theorem B3190013 : Blo 366759 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B831113 : Blo 366759 831113 := bstep (se 2 (by rfl) ⟨311667, by rfl⟩ : syracuseStep 831113 = 623335) B623335
theorem B2469791 : Blo 366759 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B831599 : Blo 366759 831599 := bstep (se 1 (by rfl) ⟨623699, by rfl⟩ : syracuseStep 831599 = 1247399) B1247399
theorem B58831667 : Blo 366759 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B22754141 : Blo 366759 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B3159121 : Blo 366759 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B7747721 : Blo 366759 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B833705 : Blo 366759 833705 := bstep (se 2 (by rfl) ⟨312639, by rfl⟩ : syracuseStep 833705 = 625279) B625279
theorem B833849 : Blo 366759 833849 := bstep (se 2 (by rfl) ⟨312693, by rfl⟩ : syracuseStep 833849 = 625387) B625387
theorem B19088455 : Blo 366759 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B3163495 : Blo 366759 3163495 := bstep (se 1 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 3163495 = 4745243) B4745243
theorem B2803247 : Blo 366759 2803247 := bstep (se 1 (by rfl) ⟨2102435, by rfl⟩ : syracuseStep 2803247 = 4204871) B4204871
theorem B3164831 : Blo 366759 3164831 := bstep (se 1 (by rfl) ⟨2373623, by rfl⟩ : syracuseStep 3164831 = 4747247) B4747247
theorem B412699 : Blo 366759 412699 := bstep (se 1 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 412699 = 619049) B619049
theorem B937271 : Blo 366759 937271 := bstep (se 1 (by rfl) ⟨702953, by rfl⟩ : syracuseStep 937271 = 1405907) B1405907
theorem B413599 : Blo 366759 413599 := bstep (se 1 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 413599 = 620399) B620399
theorem B5329637 : Blo 366759 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B414535 : Blo 366759 414535 := bstep (se 1 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 414535 = 621803) B621803
theorem B4740119 : Blo 366759 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B414823 : Blo 366759 414823 := bstep (se 1 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 414823 = 622235) B622235
theorem B13458251 : Blo 366759 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B1399801 : Blo 366759 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B1137689 : Blo 366759 1137689 := bstep (se 2 (by rfl) ⟨426633, by rfl⟩ : syracuseStep 1137689 = 853267) B853267
theorem B2090407 : Blo 366759 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B183953207 : Blo 366759 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B4253705 : Blo 366759 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B1861703 : Blo 366759 1861703 := bstep (se 1 (by rfl) ⟨1396277, by rfl⟩ : syracuseStep 1861703 = 2792555) B2792555
theorem B1567943 : Blo 366759 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B552167 : Blo 366759 552167 := bstep (se 1 (by rfl) ⟨414125, by rfl⟩ : syracuseStep 552167 = 828251) B828251
theorem B552233 : Blo 366759 552233 := bstep (se 2 (by rfl) ⟨207087, by rfl⟩ : syracuseStep 552233 = 414175) B414175
theorem B1568747 : Blo 366759 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B553577 : Blo 366759 553577 := bstep (se 2 (by rfl) ⟨207591, by rfl⟩ : syracuseStep 553577 = 415183) B415183
theorem B5371499 : Blo 366759 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B554651 : Blo 366759 554651 := bstep (se 1 (by rfl) ⟨415988, by rfl⟩ : syracuseStep 554651 = 831977) B831977
theorem B1243511 : Blo 366759 1243511 := bstep (se 1 (by rfl) ⟨932633, by rfl⟩ : syracuseStep 1243511 = 1865267) B1865267
theorem B555503 : Blo 366759 555503 := bstep (se 1 (by rfl) ⟨416627, by rfl⟩ : syracuseStep 555503 = 833255) B833255
theorem B11991563 : Blo 366759 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B1178239 : Blo 366759 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B46104329 : Blo 366759 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B1868831 : Blo 366759 1868831 := bstep (se 1 (by rfl) ⟨1401623, by rfl⟩ : syracuseStep 1868831 = 2803247) B2803247
theorem B1246535 : Blo 366759 1246535 := bstep (se 1 (by rfl) ⟨934901, by rfl⟩ : syracuseStep 1246535 = 1869803) B1869803
theorem B1181135 : Blo 366759 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B2098655 : Blo 366759 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B5310035 : Blo 366759 5310035 := bstep (se 1 (by rfl) ⟨3982526, by rfl⟩ : syracuseStep 5310035 = 7965053) B7965053
theorem B1771163 : Blo 366759 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B2787209 : Blo 366759 2787209 := bstep (se 2 (by rfl) ⟨1045203, by rfl⟩ : syracuseStep 2787209 = 2090407) B2090407
theorem B624847 : Blo 366759 624847 := bstep (se 1 (by rfl) ⟨468635, by rfl⟩ : syracuseStep 624847 = 937271) B937271
theorem B2362679 : Blo 366759 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B1052585 : Blo 366759 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B14520653 : Blo 366759 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B758459 : Blo 366759 758459 := bstep (se 1 (by rfl) ⟨568844, by rfl⟩ : syracuseStep 758459 = 1137689) B1137689
theorem B3150647 : Blo 366759 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1251071 : Blo 366759 1251071 := bstep (se 1 (by rfl) ⟨938303, by rfl⟩ : syracuseStep 1251071 = 1876607) B1876607
theorem B662183 : Blo 366759 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B368111 : Blo 366759 368111 := bstep (se 1 (by rfl) ⟨276083, by rfl⟩ : syracuseStep 368111 = 552167) B552167
theorem B368155 : Blo 366759 368155 := bstep (se 1 (by rfl) ⟨276116, by rfl⟩ : syracuseStep 368155 = 552233) B552233
theorem B1646527 : Blo 366759 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B369051 : Blo 366759 369051 := bstep (se 1 (by rfl) ⟨276788, by rfl⟩ : syracuseStep 369051 = 553577) B553577
theorem B3580999 : Blo 366759 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B369767 : Blo 366759 369767 := bstep (se 1 (by rfl) ⟨277325, by rfl⟩ : syracuseStep 369767 = 554651) B554651
theorem B3351941 : Blo 366759 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B4040189 : Blo 366759 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B829007 : Blo 366759 829007 := bstep (se 1 (by rfl) ⟨621755, by rfl⟩ : syracuseStep 829007 = 1243511) B1243511
theorem B370335 : Blo 366759 370335 := bstep (se 1 (by rfl) ⟨277751, by rfl⟩ : syracuseStep 370335 = 555503) B555503
theorem B830159 : Blo 366759 830159 := bstep (se 1 (by rfl) ⟨622619, by rfl⟩ : syracuseStep 830159 = 1245239) B1245239
theorem B2109887 : Blo 366759 2109887 := bstep (se 1 (by rfl) ⟨1582415, by rfl⟩ : syracuseStep 2109887 = 3164831) B3164831
theorem B3553091 : Blo 366759 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B4241281 : Blo 366759 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B3160079 : Blo 366759 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B122635471 : Blo 366759 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B2835803 : Blo 366759 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B4212161 : Blo 366759 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B5165147 : Blo 366759 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B416191 : Blo 366759 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B25451273 : Blo 366759 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B19160171 : Blo 366759 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B4217993 : Blo 366759 4217993 := bstep (se 2 (by rfl) ⟨1581747, by rfl⟩ : syracuseStep 4217993 = 3163495) B3163495
theorem B7529057 : Blo 366759 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B1401563 : Blo 366759 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B2974697 : Blo 366759 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B550265 : Blo 366759 550265 := bstep (se 2 (by rfl) ⟨206349, by rfl⟩ : syracuseStep 550265 = 412699) B412699
theorem B8972167 : Blo 366759 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B551465 : Blo 366759 551465 := bstep (se 2 (by rfl) ⟨206799, by rfl⟩ : syracuseStep 551465 = 413599) B413599
theorem B552095 : Blo 366759 552095 := bstep (se 1 (by rfl) ⟨414071, by rfl⟩ : syracuseStep 552095 = 828143) B828143
theorem B552713 : Blo 366759 552713 := bstep (se 2 (by rfl) ⟨207267, by rfl⟩ : syracuseStep 552713 = 414535) B414535
theorem B1241135 : Blo 366759 1241135 := bstep (se 1 (by rfl) ⟨930851, by rfl⟩ : syracuseStep 1241135 = 1861703) B1861703
theorem B553097 : Blo 366759 553097 := bstep (se 2 (by rfl) ⟨207411, by rfl⟩ : syracuseStep 553097 = 414823) B414823
theorem B1045295 : Blo 366759 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B553799 : Blo 366759 553799 := bstep (se 1 (by rfl) ⟨415349, by rfl⟩ : syracuseStep 553799 = 830699) B830699
theorem B2126675 : Blo 366759 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B554075 : Blo 366759 554075 := bstep (se 1 (by rfl) ⟨415556, by rfl⟩ : syracuseStep 554075 = 831113) B831113
theorem B1045831 : Blo 366759 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B554399 : Blo 366759 554399 := bstep (se 1 (by rfl) ⟨415799, by rfl⟩ : syracuseStep 554399 = 831599) B831599
theorem B39221111 : Blo 366759 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B15169427 : Blo 366759 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B1570985 : Blo 366759 1570985 := bstep (se 2 (by rfl) ⟨589119, by rfl⟩ : syracuseStep 1570985 = 1178239) B1178239
theorem B1866401 : Blo 366759 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B555803 : Blo 366759 555803 := bstep (se 1 (by rfl) ⟨416852, by rfl⟩ : syracuseStep 555803 = 833705) B833705
theorem B555899 : Blo 366759 555899 := bstep (se 1 (by rfl) ⟨416924, by rfl⟩ : syracuseStep 555899 = 833849) B833849
theorem B7994375 : Blo 366759 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B30736219 : Blo 366759 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B1245887 : Blo 366759 1245887 := bstep (se 1 (by rfl) ⟨934415, by rfl⟩ : syracuseStep 1245887 = 1868831) B1868831
theorem B787423 : Blo 366759 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B3540023 : Blo 366759 3540023 := bstep (se 1 (by rfl) ⟨2655017, by rfl⟩ : syracuseStep 3540023 = 5310035) B5310035
theorem B1180775 : Blo 366759 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B163513961 : Blo 366759 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B1575119 : Blo 366759 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B5671133 : Blo 366759 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B11962889 : Blo 366759 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B2100431 : Blo 366759 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B5019371 : Blo 366759 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B366843 : Blo 366759 366843 := bstep (se 1 (by rfl) ⟨275132, by rfl⟩ : syracuseStep 366843 = 550265) B550265
theorem B2234627 : Blo 366759 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B2693459 : Blo 366759 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B367643 : Blo 366759 367643 := bstep (se 1 (by rfl) ⟨275732, by rfl⟩ : syracuseStep 367643 = 551465) B551465
theorem B67870061 : Blo 366759 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B368063 : Blo 366759 368063 := bstep (se 1 (by rfl) ⟨276047, by rfl⟩ : syracuseStep 368063 = 552095) B552095
theorem B368475 : Blo 366759 368475 := bstep (se 1 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 368475 = 552713) B552713
theorem B827423 : Blo 366759 827423 := bstep (se 1 (by rfl) ⟨620567, by rfl⟩ : syracuseStep 827423 = 1241135) B1241135
theorem B368731 : Blo 366759 368731 := bstep (se 1 (by rfl) ⟨276548, by rfl⟩ : syracuseStep 368731 = 553097) B553097
theorem B696863 : Blo 366759 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B369199 : Blo 366759 369199 := bstep (se 1 (by rfl) ⟨276899, by rfl⟩ : syracuseStep 369199 = 553799) B553799
theorem B369383 : Blo 366759 369383 := bstep (se 1 (by rfl) ⟨277037, by rfl⟩ : syracuseStep 369383 = 554075) B554075
theorem B369599 : Blo 366759 369599 := bstep (se 1 (by rfl) ⟨277199, by rfl⟩ : syracuseStep 369599 = 554399) B554399
theorem B2368727 : Blo 366759 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B2106719 : Blo 366759 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B370535 : Blo 366759 370535 := bstep (se 1 (by rfl) ⟨277901, by rfl⟩ : syracuseStep 370535 = 555803) B555803
theorem B370599 : Blo 366759 370599 := bstep (se 1 (by rfl) ⟨277949, by rfl⟩ : syracuseStep 370599 = 555899) B555899
theorem B13773725 : Blo 366759 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B831023 : Blo 366759 831023 := bstep (se 1 (by rfl) ⟨623267, by rfl⟩ : syracuseStep 831023 = 1246535) B1246535
theorem B701723 : Blo 366759 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B9680435 : Blo 366759 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B833129 : Blo 366759 833129 := bstep (se 2 (by rfl) ⟨312423, by rfl⟩ : syracuseStep 833129 = 624847) B624847
theorem B505639 : Blo 366759 505639 := bstep (se 1 (by rfl) ⟨379229, by rfl⟩ : syracuseStep 505639 = 758459) B758459
theorem B834047 : Blo 366759 834047 := bstep (se 1 (by rfl) ⟨625535, by rfl⟩ : syracuseStep 834047 = 1251071) B1251071
theorem B441455 : Blo 366759 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B934375 : Blo 366759 934375 := bstep (se 1 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 934375 = 1401563) B1401563
theorem B1983131 : Blo 366759 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B1394441 : Blo 366759 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B5655041 : Blo 366759 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B10112951 : Blo 366759 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B5329583 : Blo 366759 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B40981625 : Blo 366759 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B1890535 : Blo 366759 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B2808107 : Blo 366759 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B1399103 : Blo 366759 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B1858139 : Blo 366759 1858139 := bstep (se 1 (by rfl) ⟨1393604, by rfl⟩ : syracuseStep 1858139 = 2787209) B2787209
theorem B12773447 : Blo 366759 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B2811995 : Blo 366759 2811995 := bstep (se 1 (by rfl) ⟨2108996, by rfl⟩ : syracuseStep 2811995 = 4217993) B4217993
theorem B19098661 : Blo 366759 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B552671 : Blo 366759 552671 := bstep (se 1 (by rfl) ⟨414503, by rfl⟩ : syracuseStep 552671 = 829007) B829007
theorem B553439 : Blo 366759 553439 := bstep (se 1 (by rfl) ⟨415079, by rfl⟩ : syracuseStep 553439 = 830159) B830159
theorem B1406591 : Blo 366759 1406591 := bstep (se 1 (by rfl) ⟨1054943, by rfl⟩ : syracuseStep 1406591 = 2109887) B2109887
theorem B554921 : Blo 366759 554921 := bstep (se 2 (by rfl) ⟨208095, by rfl⟩ : syracuseStep 554921 = 416191) B416191
theorem B26147407 : Blo 366759 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B1047323 : Blo 366759 1047323 := bstep (se 1 (by rfl) ⟨785492, by rfl⟩ : syracuseStep 1047323 = 1570985) B1570985
theorem B1244267 : Blo 366759 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B2195369 : Blo 366759 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B1245833 : Blo 366759 1245833 := bstep (se 2 (by rfl) ⟨467187, by rfl⟩ : syracuseStep 1245833 = 934375) B934375
theorem B2360015 : Blo 366759 2360015 := bstep (se 1 (by rfl) ⟨1770011, by rfl⟩ : syracuseStep 2360015 = 3540023) B3540023
theorem B1049897 : Blo 366759 1049897 := bstep (se 2 (by rfl) ⟨393711, by rfl⟩ : syracuseStep 1049897 = 787423) B787423
theorem B1050079 : Blo 366759 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B3770027 : Blo 366759 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B3148733 : Blo 366759 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B1871261 : Blo 366759 1871261 := bstep (se 3 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 1871261 = 701723) B701723
theorem B3346247 : Blo 366759 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B25464881 : Blo 366759 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1872071 : Blo 366759 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B1579151 : Blo 366759 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B7182557 : Blo 366759 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B1874663 : Blo 366759 1874663 := bstep (se 1 (by rfl) ⟨1405997, by rfl⟩ : syracuseStep 1874663 = 2811995) B2811995
theorem B9182483 : Blo 366759 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B368447 : Blo 366759 368447 := bstep (se 1 (by rfl) ⟨276335, by rfl⟩ : syracuseStep 368447 = 552671) B552671
theorem B368959 : Blo 366759 368959 := bstep (se 1 (by rfl) ⟨276719, by rfl⟩ : syracuseStep 368959 = 553439) B553439
theorem B369947 : Blo 366759 369947 := bstep (se 1 (by rfl) ⟨277460, by rfl⟩ : syracuseStep 369947 = 554921) B554921
theorem B698215 : Blo 366759 698215 := bstep (se 1 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 698215 = 1047323) B1047323
theorem B829511 : Blo 366759 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B1322087 : Blo 366759 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B830591 : Blo 366759 830591 := bstep (se 1 (by rfl) ⟨622943, by rfl⟩ : syracuseStep 830591 = 1245887) B1245887
theorem B929627 : Blo 366759 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B3780755 : Blo 366759 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B7975259 : Blo 366759 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B3553055 : Blo 366759 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B1489751 : Blo 366759 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B932735 : Blo 366759 932735 := bstep (se 1 (by rfl) ⟨699551, by rfl⟩ : syracuseStep 932735 = 1399103) B1399103
theorem B674185 : Blo 366759 674185 := bstep (se 2 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 674185 = 505639) B505639
theorem B937727 : Blo 366759 937727 := bstep (se 1 (by rfl) ⟨703295, by rfl⟩ : syracuseStep 937727 = 1406591) B1406591
theorem B1463579 : Blo 366759 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B109009307 : Blo 366759 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B4708853 : Blo 366759 4708853 := bstep (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) B441455
theorem B1858301 : Blo 366759 1858301 := bstep (se 3 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 1858301 = 696863) B696863
theorem B1400287 : Blo 366759 1400287 := bstep (se 1 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 1400287 = 2100431) B2100431
theorem B6741967 : Blo 366759 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B27321083 : Blo 366759 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B1238759 : Blo 366759 1238759 := bstep (se 1 (by rfl) ⟨929069, by rfl⟩ : syracuseStep 1238759 = 1858139) B1858139
theorem B45246707 : Blo 366759 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B551615 : Blo 366759 551615 := bstep (se 1 (by rfl) ⟨413711, by rfl⟩ : syracuseStep 551615 = 827423) B827423
theorem B1404479 : Blo 366759 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B8515631 : Blo 366759 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B554015 : Blo 366759 554015 := bstep (se 1 (by rfl) ⟨415511, by rfl⟩ : syracuseStep 554015 = 831023) B831023
theorem B2520713 : Blo 366759 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B34863209 : Blo 366759 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B6453623 : Blo 366759 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B555419 : Blo 366759 555419 := bstep (se 1 (by rfl) ⟨416564, by rfl⟩ : syracuseStep 555419 = 833129) B833129
theorem B556031 : Blo 366759 556031 := bstep (se 1 (by rfl) ⟨417023, by rfl⟩ : syracuseStep 556031 = 834047) B834047
theorem B1573343 : Blo 366759 1573343 := bstep (se 1 (by rfl) ⟨1180007, by rfl⟩ : syracuseStep 1573343 = 2360015) B2360015
theorem B2099155 : Blo 366759 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B1247507 : Blo 366759 1247507 := bstep (se 1 (by rfl) ⟨935630, by rfl⟩ : syracuseStep 1247507 = 1871261) B1871261
theorem B625151 : Blo 366759 625151 := bstep (se 1 (by rfl) ⟨468863, by rfl⟩ : syracuseStep 625151 = 937727) B937727
theorem B2230831 : Blo 366759 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B16976587 : Blo 366759 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B1248047 : Blo 366759 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B1052767 : Blo 366759 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B4788371 : Blo 366759 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B1249775 : Blo 366759 1249775 := bstep (se 1 (by rfl) ⟨937331, by rfl⟩ : syracuseStep 1249775 = 1874663) B1874663
theorem B825839 : Blo 366759 825839 := bstep (se 1 (by rfl) ⟨619379, by rfl⟩ : syracuseStep 825839 = 1238759) B1238759
theorem B367743 : Blo 366759 367743 := bstep (se 1 (by rfl) ⟨275807, by rfl⟩ : syracuseStep 367743 = 551615) B551615
theorem B5677087 : Blo 366759 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B5316839 : Blo 366759 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B369343 : Blo 366759 369343 := bstep (se 1 (by rfl) ⟨277007, by rfl⟩ : syracuseStep 369343 = 554015) B554015
theorem B1680475 : Blo 366759 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B2368703 : Blo 366759 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B23242139 : Blo 366759 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B4302415 : Blo 366759 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B370279 : Blo 366759 370279 := bstep (se 1 (by rfl) ⟨277709, by rfl⟩ : syracuseStep 370279 = 555419) B555419
theorem B993167 : Blo 366759 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B370687 : Blo 366759 370687 := bstep (se 1 (by rfl) ⟨278015, by rfl⟩ : syracuseStep 370687 = 556031) B556031
theorem B8989289 : Blo 366759 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B830555 : Blo 366759 830555 := bstep (se 1 (by rfl) ⟨622916, by rfl⟩ : syracuseStep 830555 = 1245833) B1245833
theorem B699931 : Blo 366759 699931 := bstep (se 1 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 699931 = 1049897) B1049897
theorem B930953 : Blo 366759 930953 := bstep (se 2 (by rfl) ⟨349107, by rfl⟩ : syracuseStep 930953 = 698215) B698215
theorem B898913 : Blo 366759 898913 := bstep (se 2 (by rfl) ⟨337092, by rfl⟩ : syracuseStep 898913 = 674185) B674185
theorem B30164471 : Blo 366759 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B936319 : Blo 366759 936319 := bstep (se 1 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 936319 = 1404479) B1404479
theorem B3525565 : Blo 366759 3525565 := bstep (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) B1322087
theorem B2513351 : Blo 366759 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B1400105 : Blo 366759 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B975719 : Blo 366759 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B72672871 : Blo 366759 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B3139235 : Blo 366759 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B1238867 : Blo 366759 1238867 := bstep (se 1 (by rfl) ⟨929150, by rfl⟩ : syracuseStep 1238867 = 1858301) B1858301
theorem B6121655 : Blo 366759 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B18214055 : Blo 366759 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B553007 : Blo 366759 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B553727 : Blo 366759 553727 := bstep (se 1 (by rfl) ⟨415295, by rfl⟩ : syracuseStep 553727 = 830591) B830591
theorem B619751 : Blo 366759 619751 := bstep (se 1 (by rfl) ⟨464813, by rfl⟩ : syracuseStep 619751 = 929627) B929627
theorem B2520503 : Blo 366759 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B621823 : Blo 366759 621823 := bstep (se 1 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 621823 = 932735) B932735
theorem B1867049 : Blo 366759 1867049 := bstep (se 2 (by rfl) ⟨700143, by rfl⟩ : syracuseStep 1867049 = 1400287) B1400287
theorem B7569449 : Blo 366759 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B1048895 : Blo 366759 1048895 := bstep (se 1 (by rfl) ⟨786671, by rfl⟩ : syracuseStep 1048895 = 1573343) B1573343
theorem B5736553 : Blo 366759 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B96897161 : Blo 366759 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B1248425 : Blo 366759 1248425 := bstep (se 2 (by rfl) ⟨468159, by rfl⟩ : syracuseStep 1248425 = 936319) B936319
theorem B1675567 : Blo 366759 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B3544559 : Blo 366759 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B1579135 : Blo 366759 1579135 := bstep (se 1 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 1579135 = 2368703) B2368703
theorem B825911 : Blo 366759 825911 := bstep (se 1 (by rfl) ⟨619433, by rfl⟩ : syracuseStep 825911 = 1238867) B1238867
theorem B662111 : Blo 366759 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B368671 : Blo 366759 368671 := bstep (se 1 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 368671 = 553007) B553007
theorem B369151 : Blo 366759 369151 := bstep (se 1 (by rfl) ⟨276863, by rfl⟩ : syracuseStep 369151 = 553727) B553727
theorem B1680335 : Blo 366759 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B599275 : Blo 366759 599275 := bstep (se 1 (by rfl) ⟨449456, by rfl⟩ : syracuseStep 599275 = 898913) B898913
theorem B829097 : Blo 366759 829097 := bstep (se 2 (by rfl) ⟨310911, by rfl⟩ : syracuseStep 829097 = 621823) B621823
theorem B2240633 : Blo 366759 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B831671 : Blo 366759 831671 := bstep (se 1 (by rfl) ⟨623753, by rfl⟩ : syracuseStep 831671 = 1247507) B1247507
theorem B832031 : Blo 366759 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B2798873 : Blo 366759 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B3192247 : Blo 366759 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B833183 : Blo 366759 833183 := bstep (se 1 (by rfl) ⟨624887, by rfl⟩ : syracuseStep 833183 = 1249775) B1249775
theorem B4700753 : Blo 366759 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B933241 : Blo 366759 933241 := bstep (se 2 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 933241 = 699931) B699931
theorem B933403 : Blo 366759 933403 := bstep (se 1 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 933403 = 1400105) B1400105
theorem B4081103 : Blo 366759 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B12142703 : Blo 366759 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B413167 : Blo 366759 413167 := bstep (se 1 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 413167 = 619751) B619751
theorem B20109647 : Blo 366759 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B416767 : Blo 366759 416767 := bstep (se 1 (by rfl) ⟨312575, by rfl⟩ : syracuseStep 416767 = 625151) B625151
theorem B2974441 : Blo 366759 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B22635449 : Blo 366759 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B550559 : Blo 366759 550559 := bstep (se 1 (by rfl) ⟨412919, by rfl⟩ : syracuseStep 550559 = 825839) B825839
theorem B1403689 : Blo 366759 1403689 := bstep (se 2 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 1403689 = 1052767) B1052767
theorem B650479 : Blo 366759 650479 := bstep (se 1 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 650479 = 975719) B975719
theorem B15494759 : Blo 366759 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B2092823 : Blo 366759 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B5992859 : Blo 366759 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B553703 : Blo 366759 553703 := bstep (se 1 (by rfl) ⟨415277, by rfl⟩ : syracuseStep 553703 = 830555) B830555
theorem B620635 : Blo 366759 620635 := bstep (se 1 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 620635 = 930953) B930953
theorem B1244699 : Blo 366759 1244699 := bstep (se 1 (by rfl) ⟨933524, by rfl⟩ : syracuseStep 1244699 = 1867049) B1867049
theorem B5046299 : Blo 366759 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B2720735 : Blo 366759 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B3965921 : Blo 366759 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B8095135 : Blo 366759 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B2363039 : Blo 366759 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B1871585 : Blo 366759 1871585 := bstep (se 2 (by rfl) ⟨701844, by rfl⟩ : syracuseStep 1871585 = 1403689) B1403689
theorem B13406431 : Blo 366759 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B2234089 : Blo 366759 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B1120223 : Blo 366759 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B367039 : Blo 366759 367039 := bstep (se 1 (by rfl) ⟨275279, by rfl⟩ : syracuseStep 367039 = 550559) B550559
theorem B10329839 : Blo 366759 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B827513 : Blo 366759 827513 := bstep (se 2 (by rfl) ⟨310317, by rfl⟩ : syracuseStep 827513 = 620635) B620635
theorem B2105513 : Blo 366759 2105513 := bstep (se 2 (by rfl) ⟨789567, by rfl⟩ : syracuseStep 2105513 = 1579135) B1579135
theorem B369135 : Blo 366759 369135 := bstep (se 1 (by rfl) ⟨276851, by rfl⟩ : syracuseStep 369135 = 553703) B553703
theorem B829799 : Blo 366759 829799 := bstep (se 1 (by rfl) ⟨622349, by rfl⟩ : syracuseStep 829799 = 1244699) B1244699
theorem B699263 : Blo 366759 699263 := bstep (se 1 (by rfl) ⟨524447, by rfl⟩ : syracuseStep 699263 = 1048895) B1048895
theorem B5975021 : Blo 366759 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B799033 : Blo 366759 799033 := bstep (se 2 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 799033 = 599275) B599275
theorem B832283 : Blo 366759 832283 := bstep (se 1 (by rfl) ⟨624212, by rfl⟩ : syracuseStep 832283 = 1248425) B1248425
theorem B867305 : Blo 366759 867305 := bstep (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) B650479
theorem B441407 : Blo 366759 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B258392429 : Blo 366759 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B15090299 : Blo 366759 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B1395215 : Blo 366759 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B3133835 : Blo 366759 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B122379797 : Blo 366759 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B550607 : Blo 366759 550607 := bstep (se 1 (by rfl) ⟨412955, by rfl⟩ : syracuseStep 550607 = 825911) B825911
theorem B550889 : Blo 366759 550889 := bstep (se 2 (by rfl) ⟨206583, by rfl⟩ : syracuseStep 550889 = 413167) B413167
theorem B552731 : Blo 366759 552731 := bstep (se 1 (by rfl) ⟨414548, by rfl⟩ : syracuseStep 552731 = 829097) B829097
theorem B4256329 : Blo 366759 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B554447 : Blo 366759 554447 := bstep (se 1 (by rfl) ⟨415835, by rfl⟩ : syracuseStep 554447 = 831671) B831671
theorem B3995239 : Blo 366759 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B554687 : Blo 366759 554687 := bstep (se 1 (by rfl) ⟨416015, by rfl⟩ : syracuseStep 554687 = 832031) B832031
theorem B1865915 : Blo 366759 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B555455 : Blo 366759 555455 := bstep (se 1 (by rfl) ⟨416591, by rfl⟩ : syracuseStep 555455 = 833183) B833183
theorem B555689 : Blo 366759 555689 := bstep (se 2 (by rfl) ⟨208383, by rfl⟩ : syracuseStep 555689 = 416767) B416767
theorem B1244321 : Blo 366759 1244321 := bstep (se 2 (by rfl) ⟨466620, by rfl⟩ : syracuseStep 1244321 = 933241) B933241
theorem B1244537 : Blo 366759 1244537 := bstep (se 2 (by rfl) ⟨466701, by rfl⟩ : syracuseStep 1244537 = 933403) B933403
theorem B172261619 : Blo 366759 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B10060199 : Blo 366759 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B1575359 : Blo 366759 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B1247723 : Blo 366759 1247723 := bstep (se 1 (by rfl) ⟨935792, by rfl⟩ : syracuseStep 1247723 = 1871585) B1871585
theorem B6886559 : Blo 366759 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B5675105 : Blo 366759 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B367071 : Blo 366759 367071 := bstep (se 1 (by rfl) ⟨275303, by rfl⟩ : syracuseStep 367071 = 550607) B550607
theorem B367259 : Blo 366759 367259 := bstep (se 1 (by rfl) ⟨275444, by rfl⟩ : syracuseStep 367259 = 550889) B550889
theorem B466175 : Blo 366759 466175 := bstep (se 1 (by rfl) ⟨349631, by rfl⟩ : syracuseStep 466175 = 699263) B699263
theorem B368487 : Blo 366759 368487 := bstep (se 1 (by rfl) ⟨276365, by rfl⟩ : syracuseStep 368487 = 552731) B552731
theorem B369631 : Blo 366759 369631 := bstep (se 1 (by rfl) ⟨277223, by rfl⟩ : syracuseStep 369631 = 554447) B554447
theorem B369791 : Blo 366759 369791 := bstep (se 1 (by rfl) ⟨277343, by rfl⟩ : syracuseStep 369791 = 554687) B554687
theorem B370303 : Blo 366759 370303 := bstep (se 1 (by rfl) ⟨277727, by rfl⟩ : syracuseStep 370303 = 555455) B555455
theorem B370459 : Blo 366759 370459 := bstep (se 1 (by rfl) ⟨277844, by rfl⟩ : syracuseStep 370459 = 555689) B555689
theorem B829547 : Blo 366759 829547 := bstep (se 1 (by rfl) ⟨622160, by rfl⟩ : syracuseStep 829547 = 1244321) B1244321
theorem B829691 : Blo 366759 829691 := bstep (se 1 (by rfl) ⟨622268, by rfl⟩ : syracuseStep 829691 = 1244537) B1244537
theorem B1813823 : Blo 366759 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B930143 : Blo 366759 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B10793513 : Blo 366759 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B17875241 : Blo 366759 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B1065377 : Blo 366759 1065377 := bstep (se 2 (by rfl) ⟨399516, by rfl⟩ : syracuseStep 1065377 = 799033) B799033
theorem B3983347 : Blo 366759 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B5326985 : Blo 366759 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B2312813 : Blo 366759 2312813 := bstep (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) B867305
theorem B3364199 : Blo 366759 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B2643947 : Blo 366759 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2089223 : Blo 366759 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B746815 : Blo 366759 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B81586531 : Blo 366759 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B551675 : Blo 366759 551675 := bstep (se 1 (by rfl) ⟨413756, by rfl⟩ : syracuseStep 551675 = 827513) B827513
theorem B1403675 : Blo 366759 1403675 := bstep (se 1 (by rfl) ⟨1052756, by rfl⟩ : syracuseStep 1403675 = 2105513) B2105513
theorem B553199 : Blo 366759 553199 := bstep (se 1 (by rfl) ⟨414899, by rfl⟩ : syracuseStep 553199 = 829799) B829799
theorem B2978785 : Blo 366759 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B1177085 : Blo 366759 1177085 := bstep (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) B441407
theorem B554855 : Blo 366759 554855 := bstep (se 1 (by rfl) ⟨416141, by rfl⟩ : syracuseStep 554855 = 832283) B832283
theorem B1243943 : Blo 366759 1243943 := bstep (se 1 (by rfl) ⟨932957, by rfl⟩ : syracuseStep 1243943 = 1865915) B1865915
theorem B1050239 : Blo 366759 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B5311129 : Blo 366759 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B3971713 : Blo 366759 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B6167501 : Blo 366759 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B367783 : Blo 366759 367783 := bstep (se 1 (by rfl) ⟨275837, by rfl⟩ : syracuseStep 367783 = 551675) B551675
theorem B368799 : Blo 366759 368799 := bstep (se 1 (by rfl) ⟨276599, by rfl⟩ : syracuseStep 368799 = 553199) B553199
theorem B369903 : Blo 366759 369903 := bstep (se 1 (by rfl) ⟨277427, by rfl⟩ : syracuseStep 369903 = 554855) B554855
theorem B829295 : Blo 366759 829295 := bstep (se 1 (by rfl) ⟨621971, by rfl⟩ : syracuseStep 829295 = 1243943) B1243943
theorem B3551323 : Blo 366759 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B831815 : Blo 366759 831815 := bstep (se 1 (by rfl) ⟨623861, by rfl⟩ : syracuseStep 831815 = 1247723) B1247723
theorem B995753 : Blo 366759 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B18364157 : Blo 366759 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B2242799 : Blo 366759 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B1392815 : Blo 366759 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B935783 : Blo 366759 935783 := bstep (se 1 (by rfl) ⟨701837, by rfl⟩ : syracuseStep 935783 = 1403675) B1403675
theorem B7195675 : Blo 366759 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B114841079 : Blo 366759 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B11916827 : Blo 366759 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B710251 : Blo 366759 710251 := bstep (se 1 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 710251 = 1065377) B1065377
theorem B6706799 : Blo 366759 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B108782041 : Blo 366759 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B1762631 : Blo 366759 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B15133613 : Blo 366759 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B553031 : Blo 366759 553031 := bstep (se 1 (by rfl) ⟨414773, by rfl⟩ : syracuseStep 553031 = 829547) B829547
theorem B553127 : Blo 366759 553127 := bstep (se 1 (by rfl) ⟨414845, by rfl⟩ : syracuseStep 553127 = 829691) B829691
theorem B1209215 : Blo 366759 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B620095 : Blo 366759 620095 := bstep (se 1 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 620095 = 930143) B930143
theorem B1243133 : Blo 366759 1243133 := bstep (se 3 (by rfl) ⟨233087, by rfl⟩ : syracuseStep 1243133 = 466175) B466175
theorem B784723 : Blo 366759 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B623855 : Blo 366759 623855 := bstep (se 1 (by rfl) ⟨467891, by rfl⟩ : syracuseStep 623855 = 935783) B935783
theorem B7081505 : Blo 366759 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B826793 : Blo 366759 826793 := bstep (se 2 (by rfl) ⟨310047, by rfl⟩ : syracuseStep 826793 = 620095) B620095
theorem B368687 : Blo 366759 368687 := bstep (se 1 (by rfl) ⟨276515, by rfl⟩ : syracuseStep 368687 = 553031) B553031
theorem B368751 : Blo 366759 368751 := bstep (se 1 (by rfl) ⟨276563, by rfl⟩ : syracuseStep 368751 = 553127) B553127
theorem B663835 : Blo 366759 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B828755 : Blo 366759 828755 := bstep (se 1 (by rfl) ⟨621566, by rfl⟩ : syracuseStep 828755 = 1243133) B1243133
theorem B928543 : Blo 366759 928543 := bstep (se 1 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 928543 = 1392815) B1392815
theorem B145042721 : Blo 366759 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B700159 : Blo 366759 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B3224573 : Blo 366759 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B76560719 : Blo 366759 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B7944551 : Blo 366759 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B4471199 : Blo 366759 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B4111667 : Blo 366759 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B4735097 : Blo 366759 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B40356301 : Blo 366759 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B3788005 : Blo 366759 3788005 := bstep (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) B710251
theorem B5295617 : Blo 366759 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B12242771 : Blo 366759 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B1495199 : Blo 366759 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B9594233 : Blo 366759 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B1175087 : Blo 366759 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B552863 : Blo 366759 552863 := bstep (se 1 (by rfl) ⟨414647, by rfl⟩ : syracuseStep 552863 = 829295) B829295
theorem B554543 : Blo 366759 554543 := bstep (se 1 (by rfl) ⟨415907, by rfl⟩ : syracuseStep 554543 = 831815) B831815
theorem B1046297 : Blo 366759 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B885113 : Blo 366759 885113 := bstep (se 2 (by rfl) ⟨331917, by rfl⟩ : syracuseStep 885113 = 663835) B663835
theorem B4721003 : Blo 366759 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B8161847 : Blo 366759 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B53808401 : Blo 366759 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B5050673 : Blo 366759 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2790125 : Blo 366759 2790125 := bstep (se 3 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 2790125 = 1046297) B1046297
theorem B6396155 : Blo 366759 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B368575 : Blo 366759 368575 := bstep (se 1 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 368575 = 552863) B552863
theorem B369695 : Blo 366759 369695 := bstep (se 1 (by rfl) ⟨277271, by rfl⟩ : syracuseStep 369695 = 554543) B554543
theorem B3156731 : Blo 366759 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B996799 : Blo 366759 996799 := bstep (se 1 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 996799 = 1495199) B1495199
theorem B933545 : Blo 366759 933545 := bstep (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) B700159
theorem B204161917 : Blo 366759 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B2149715 : Blo 366759 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B5296367 : Blo 366759 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B2741111 : Blo 366759 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B415903 : Blo 366759 415903 := bstep (se 1 (by rfl) ⟨311927, by rfl⟩ : syracuseStep 415903 = 623855) B623855
theorem B3530411 : Blo 366759 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B1238057 : Blo 366759 1238057 := bstep (se 2 (by rfl) ⟨464271, by rfl⟩ : syracuseStep 1238057 = 928543) B928543
theorem B551195 : Blo 366759 551195 := bstep (se 1 (by rfl) ⟨413396, by rfl⟩ : syracuseStep 551195 = 826793) B826793
theorem B552503 : Blo 366759 552503 := bstep (se 1 (by rfl) ⟨414377, by rfl⟩ : syracuseStep 552503 = 828755) B828755
theorem B96695147 : Blo 366759 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B783391 : Blo 366759 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B2980799 : Blo 366759 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B590075 : Blo 366759 590075 := bstep (se 1 (by rfl) ⟨442556, by rfl⟩ : syracuseStep 590075 = 885113) B885113
theorem B3147335 : Blo 366759 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B5441231 : Blo 366759 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B257853725 : Blo 366759 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B4264103 : Blo 366759 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B825371 : Blo 366759 825371 := bstep (se 1 (by rfl) ⟨619028, by rfl⟩ : syracuseStep 825371 = 1238057) B1238057
theorem B367463 : Blo 366759 367463 := bstep (se 1 (by rfl) ⟨275597, by rfl⟩ : syracuseStep 367463 = 551195) B551195
theorem B2104487 : Blo 366759 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B368335 : Blo 366759 368335 := bstep (se 1 (by rfl) ⟨276251, by rfl⟩ : syracuseStep 368335 = 552503) B552503
theorem B272215889 : Blo 366759 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1329065 : Blo 366759 1329065 := bstep (se 2 (by rfl) ⟨498399, by rfl⟩ : syracuseStep 1329065 = 996799) B996799
theorem B1987199 : Blo 366759 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B35872267 : Blo 366759 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B1433143 : Blo 366759 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B3530911 : Blo 366759 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B3367115 : Blo 366759 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1860083 : Blo 366759 1860083 := bstep (se 1 (by rfl) ⟨1395062, by rfl⟩ : syracuseStep 1860083 = 2790125) B2790125
theorem B1827407 : Blo 366759 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B2353607 : Blo 366759 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B1044521 : Blo 366759 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B554537 : Blo 366759 554537 := bstep (se 2 (by rfl) ⟨207951, by rfl⟩ : syracuseStep 554537 = 415903) B415903
theorem B622363 : Blo 366759 622363 := bstep (se 1 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 622363 = 933545) B933545
theorem B393383 : Blo 366759 393383 := bstep (se 1 (by rfl) ⟨295037, by rfl⟩ : syracuseStep 393383 = 590075) B590075
theorem B2098223 : Blo 366759 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B886043 : Blo 366759 886043 := bstep (se 1 (by rfl) ⟨664532, by rfl⟩ : syracuseStep 886043 = 1329065) B1329065
theorem B171902483 : Blo 366759 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B181477259 : Blo 366759 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B696347 : Blo 366759 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B7643429 : Blo 366759 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B369691 : Blo 366759 369691 := bstep (se 1 (by rfl) ⟨277268, by rfl⟩ : syracuseStep 369691 = 554537) B554537
theorem B829817 : Blo 366759 829817 := bstep (se 2 (by rfl) ⟨311181, by rfl⟩ : syracuseStep 829817 = 622363) B622363
theorem B1324799 : Blo 366759 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B2244743 : Blo 366759 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B47829689 : Blo 366759 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B4707881 : Blo 366759 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B3627487 : Blo 366759 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B4873085 : Blo 366759 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B2842735 : Blo 366759 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B550247 : Blo 366759 550247 := bstep (se 1 (by rfl) ⟨412685, by rfl⟩ : syracuseStep 550247 = 825371) B825371
theorem B1402991 : Blo 366759 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B1240055 : Blo 366759 1240055 := bstep (se 1 (by rfl) ⟨930041, by rfl⟩ : syracuseStep 1240055 = 1860083) B1860083
theorem B1569071 : Blo 366759 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B1049021 : Blo 366759 1049021 := bstep (se 3 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 1049021 = 393383) B393383
theorem B590695 : Blo 366759 590695 := bstep (se 1 (by rfl) ⟨443021, by rfl⟩ : syracuseStep 590695 = 886043) B886043
theorem B31886459 : Blo 366759 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B3248723 : Blo 366759 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B120984839 : Blo 366759 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B464231 : Blo 366759 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B366831 : Blo 366759 366831 := bstep (se 1 (by rfl) ⟨275123, by rfl⟩ : syracuseStep 366831 = 550247) B550247
theorem B826703 : Blo 366759 826703 := bstep (se 1 (by rfl) ⟨620027, by rfl⟩ : syracuseStep 826703 = 1240055) B1240055
theorem B114601655 : Blo 366759 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B19346597 : Blo 366759 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B5095619 : Blo 366759 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B935327 : Blo 366759 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B1496495 : Blo 366759 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3790313 : Blo 366759 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B1398815 : Blo 366759 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B3138587 : Blo 366759 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B553211 : Blo 366759 553211 := bstep (se 1 (by rfl) ⟨414908, by rfl⟩ : syracuseStep 553211 = 829817) B829817
theorem B1046047 : Blo 366759 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B883199 : Blo 366759 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B623551 : Blo 366759 623551 := bstep (se 1 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 623551 = 935327) B935327
theorem B2165815 : Blo 366759 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B2526875 : Blo 366759 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B3150373 : Blo 366759 3150373 := bstep (se 4 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 3150373 = 590695) B590695
theorem B368807 : Blo 366759 368807 := bstep (se 1 (by rfl) ⟨276605, by rfl⟩ : syracuseStep 368807 = 553211) B553211
theorem B699347 : Blo 366759 699347 := bstep (se 1 (by rfl) ⟨524510, by rfl⟩ : syracuseStep 699347 = 1049021) B1049021
theorem B80656559 : Blo 366759 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B932543 : Blo 366759 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B1394729 : Blo 366759 1394729 := bstep (se 2 (by rfl) ⟨523023, by rfl⟩ : syracuseStep 1394729 = 1046047) B1046047
theorem B76401103 : Blo 366759 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B12897731 : Blo 366759 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B3397079 : Blo 366759 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B21257639 : Blo 366759 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B1237949 : Blo 366759 1237949 := bstep (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) B464231
theorem B3990653 : Blo 366759 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B551135 : Blo 366759 551135 := bstep (se 1 (by rfl) ⟨413351, by rfl⟩ : syracuseStep 551135 = 826703) B826703
theorem B2092391 : Blo 366759 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B588799 : Blo 366759 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B2264719 : Blo 366759 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B2887753 : Blo 366759 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B825299 : Blo 366759 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B4200497 : Blo 366759 4200497 := bstep (se 2 (by rfl) ⟨1575186, by rfl⟩ : syracuseStep 4200497 = 3150373) B3150373
theorem B2660435 : Blo 366759 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B367423 : Blo 366759 367423 := bstep (se 1 (by rfl) ⟨275567, by rfl⟩ : syracuseStep 367423 = 551135) B551135
theorem B466231 : Blo 366759 466231 := bstep (se 1 (by rfl) ⟨349673, by rfl⟩ : syracuseStep 466231 = 699347) B699347
theorem B831401 : Blo 366759 831401 := bstep (se 2 (by rfl) ⟨311775, by rfl⟩ : syracuseStep 831401 = 623551) B623551
theorem B929819 : Blo 366759 929819 := bstep (se 1 (by rfl) ⟨697364, by rfl⟩ : syracuseStep 929819 = 1394729) B1394729
theorem B8598487 : Blo 366759 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B1684583 : Blo 366759 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B14171759 : Blo 366759 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B1394927 : Blo 366759 1394927 := bstep (se 1 (by rfl) ⟨1046195, by rfl⟩ : syracuseStep 1394927 = 2092391) B2092391
theorem B101868137 : Blo 366759 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B785065 : Blo 366759 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B53771039 : Blo 366759 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B621695 : Blo 366759 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B1773623 : Blo 366759 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B3019625 : Blo 366759 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B1123055 : Blo 366759 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B9447839 : Blo 366759 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B929951 : Blo 366759 929951 := bstep (se 1 (by rfl) ⟨697463, by rfl⟩ : syracuseStep 929951 = 1394927) B1394927
theorem B2800331 : Blo 366759 2800331 := bstep (se 1 (by rfl) ⟨2100248, by rfl⟩ : syracuseStep 2800331 = 4200497) B4200497
theorem B3850337 : Blo 366759 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B67912091 : Blo 366759 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B414463 : Blo 366759 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B550199 : Blo 366759 550199 := bstep (se 1 (by rfl) ⟨412649, by rfl⟩ : syracuseStep 550199 = 825299) B825299
theorem B11464649 : Blo 366759 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B554267 : Blo 366759 554267 := bstep (se 1 (by rfl) ⟨415700, by rfl⟩ : syracuseStep 554267 = 831401) B831401
theorem B619879 : Blo 366759 619879 := bstep (se 1 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 619879 = 929819) B929819
theorem B1046753 : Blo 366759 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B621641 : Blo 366759 621641 := bstep (se 2 (by rfl) ⟨233115, by rfl⟩ : syracuseStep 621641 = 466231) B466231
theorem B35847359 : Blo 366759 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B366799 : Blo 366759 366799 := bstep (se 1 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 366799 = 550199) B550199
theorem B6298559 : Blo 366759 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B826505 : Blo 366759 826505 := bstep (se 2 (by rfl) ⟨309939, by rfl⟩ : syracuseStep 826505 = 619879) B619879
theorem B7643099 : Blo 366759 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B369511 : Blo 366759 369511 := bstep (se 1 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 369511 = 554267) B554267
theorem B697835 : Blo 366759 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B23898239 : Blo 366759 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B2566891 : Blo 366759 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B4729661 : Blo 366759 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B2013083 : Blo 366759 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B414427 : Blo 366759 414427 := bstep (se 1 (by rfl) ⟨310820, by rfl⟩ : syracuseStep 414427 = 621641) B621641
theorem B45274727 : Blo 366759 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B748703 : Blo 366759 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B552617 : Blo 366759 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B619967 : Blo 366759 619967 := bstep (se 1 (by rfl) ⟨464975, by rfl⟩ : syracuseStep 619967 = 929951) B929951
theorem B1866887 : Blo 366759 1866887 := bstep (se 1 (by rfl) ⟨1400165, by rfl⟩ : syracuseStep 1866887 = 2800331) B2800331
theorem B4199039 : Blo 366759 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B15932159 : Blo 366759 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B3153107 : Blo 366759 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B499135 : Blo 366759 499135 := bstep (se 1 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 499135 = 748703) B748703
theorem B368411 : Blo 366759 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B3422521 : Blo 366759 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B120732605 : Blo 366759 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B5095399 : Blo 366759 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B413311 : Blo 366759 413311 := bstep (se 1 (by rfl) ⟨309983, by rfl⟩ : syracuseStep 413311 = 619967) B619967
theorem B1860893 : Blo 366759 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B551003 : Blo 366759 551003 := bstep (se 1 (by rfl) ⟨413252, by rfl⟩ : syracuseStep 551003 = 826505) B826505
theorem B552569 : Blo 366759 552569 := bstep (se 2 (by rfl) ⟨207213, by rfl⟩ : syracuseStep 552569 = 414427) B414427
theorem B1342055 : Blo 366759 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B1244591 : Blo 366759 1244591 := bstep (se 1 (by rfl) ⟨933443, by rfl⟩ : syracuseStep 1244591 = 1866887) B1866887
theorem B10621439 : Blo 366759 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B2102071 : Blo 366759 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B367335 : Blo 366759 367335 := bstep (se 1 (by rfl) ⟨275501, by rfl⟩ : syracuseStep 367335 = 551003) B551003
theorem B3578813 : Blo 366759 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B368379 : Blo 366759 368379 := bstep (se 1 (by rfl) ⟨276284, by rfl⟩ : syracuseStep 368379 = 552569) B552569
theorem B4563361 : Blo 366759 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B665513 : Blo 366759 665513 := bstep (se 2 (by rfl) ⟨249567, by rfl⟩ : syracuseStep 665513 = 499135) B499135
theorem B80488403 : Blo 366759 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B829727 : Blo 366759 829727 := bstep (se 1 (by rfl) ⟨622295, by rfl⟩ : syracuseStep 829727 = 1244591) B1244591
theorem B6793865 : Blo 366759 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B2799359 : Blo 366759 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B551081 : Blo 366759 551081 := bstep (se 2 (by rfl) ⟨206655, by rfl⟩ : syracuseStep 551081 = 413311) B413311
theorem B1240595 : Blo 366759 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B7080959 : Blo 366759 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B367387 : Blo 366759 367387 := bstep (se 1 (by rfl) ⟨275540, by rfl⟩ : syracuseStep 367387 = 551081) B551081
theorem B4529243 : Blo 366759 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B827063 : Blo 366759 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B2802761 : Blo 366759 2802761 := bstep (se 2 (by rfl) ⟨1051035, by rfl⟩ : syracuseStep 2802761 = 2102071) B2102071
theorem B443675 : Blo 366759 443675 := bstep (se 1 (by rfl) ⟨332756, by rfl⟩ : syracuseStep 443675 = 665513) B665513
theorem B53658935 : Blo 366759 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B24337925 : Blo 366759 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B2385875 : Blo 366759 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B553151 : Blo 366759 553151 := bstep (se 1 (by rfl) ⟨414863, by rfl⟩ : syracuseStep 553151 = 829727) B829727
theorem B1866239 : Blo 366759 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B1868507 : Blo 366759 1868507 := bstep (se 1 (by rfl) ⟨1401380, by rfl⟩ : syracuseStep 1868507 = 2802761) B2802761
theorem B4720639 : Blo 366759 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B1183133 : Blo 366759 1183133 := bstep (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) B443675
theorem B16225283 : Blo 366759 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B6362333 : Blo 366759 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B368767 : Blo 366759 368767 := bstep (se 1 (by rfl) ⟨276575, by rfl⟩ : syracuseStep 368767 = 553151) B553151
theorem B12077981 : Blo 366759 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B35772623 : Blo 366759 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B551375 : Blo 366759 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B1244159 : Blo 366759 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B1245671 : Blo 366759 1245671 := bstep (se 1 (by rfl) ⟨934253, by rfl⟩ : syracuseStep 1245671 = 1868507) B1868507
theorem B6294185 : Blo 366759 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B367583 : Blo 366759 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B3155021 : Blo 366759 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B829439 : Blo 366759 829439 := bstep (se 1 (by rfl) ⟨622079, by rfl⟩ : syracuseStep 829439 = 1244159) B1244159
theorem B43267421 : Blo 366759 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B4241555 : Blo 366759 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B8051987 : Blo 366759 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B23848415 : Blo 366759 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B4196123 : Blo 366759 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B2103347 : Blo 366759 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B15898943 : Blo 366759 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B28844947 : Blo 366759 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B2827703 : Blo 366759 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B830447 : Blo 366759 830447 := bstep (se 1 (by rfl) ⟨622835, by rfl⟩ : syracuseStep 830447 = 1245671) B1245671
theorem B5367991 : Blo 366759 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B552959 : Blo 366759 552959 := bstep (se 1 (by rfl) ⟨414719, by rfl⟩ : syracuseStep 552959 = 829439) B829439
theorem B368639 : Blo 366759 368639 := bstep (se 1 (by rfl) ⟨276479, by rfl⟩ : syracuseStep 368639 = 552959) B552959
theorem B2797415 : Blo 366759 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B7157321 : Blo 366759 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B10599295 : Blo 366759 10599295 := bstep (se 1 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 10599295 = 15898943) B15898943
theorem B1885135 : Blo 366759 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B38459929 : Blo 366759 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B1402231 : Blo 366759 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B553631 : Blo 366759 553631 := bstep (se 1 (by rfl) ⟨415223, by rfl⟩ : syracuseStep 553631 = 830447) B830447
theorem B1869641 : Blo 366759 1869641 := bstep (se 2 (by rfl) ⟨701115, by rfl⟩ : syracuseStep 1869641 = 1402231) B1402231
theorem B369087 : Blo 366759 369087 := bstep (se 1 (by rfl) ⟨276815, by rfl⟩ : syracuseStep 369087 = 553631) B553631
theorem B14132393 : Blo 366759 14132393 := bstep (se 2 (by rfl) ⟨5299647, by rfl⟩ : syracuseStep 14132393 = 10599295) B10599295
theorem B4771547 : Blo 366759 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B2513513 : Blo 366759 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B1864943 : Blo 366759 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B51279905 : Blo 366759 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B1246427 : Blo 366759 1246427 := bstep (se 1 (by rfl) ⟨934820, by rfl⟩ : syracuseStep 1246427 = 1869641) B1869641
theorem B3181031 : Blo 366759 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B1675675 : Blo 366759 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B136746413 : Blo 366759 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B9421595 : Blo 366759 9421595 := bstep (se 1 (by rfl) ⟨7066196, by rfl⟩ : syracuseStep 9421595 = 14132393) B14132393
theorem B1243295 : Blo 366759 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B91164275 : Blo 366759 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B2234233 : Blo 366759 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B828863 : Blo 366759 828863 := bstep (se 1 (by rfl) ⟨621647, by rfl⟩ : syracuseStep 828863 = 1243295) B1243295
theorem B830951 : Blo 366759 830951 := bstep (se 1 (by rfl) ⟨623213, by rfl⟩ : syracuseStep 830951 = 1246427) B1246427
theorem B6281063 : Blo 366759 6281063 := bstep (se 1 (by rfl) ⟨4710797, by rfl⟩ : syracuseStep 6281063 = 9421595) B9421595
theorem B2120687 : Blo 366759 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1413791 : Blo 366759 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B60776183 : Blo 366759 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B4187375 : Blo 366759 4187375 := bstep (se 1 (by rfl) ⟨3140531, by rfl⟩ : syracuseStep 4187375 = 6281063) B6281063
theorem B552575 : Blo 366759 552575 := bstep (se 1 (by rfl) ⟨414431, by rfl⟩ : syracuseStep 552575 = 828863) B828863
theorem B553967 : Blo 366759 553967 := bstep (se 1 (by rfl) ⟨415475, by rfl⟩ : syracuseStep 553967 = 830951) B830951
theorem B2978977 : Blo 366759 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B2791583 : Blo 366759 2791583 := bstep (se 1 (by rfl) ⟨2093687, by rfl⟩ : syracuseStep 2791583 = 4187375) B4187375
theorem B3971969 : Blo 366759 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B368383 : Blo 366759 368383 := bstep (se 1 (by rfl) ⟨276287, by rfl⟩ : syracuseStep 368383 = 552575) B552575
theorem B369311 : Blo 366759 369311 := bstep (se 1 (by rfl) ⟨276983, by rfl⟩ : syracuseStep 369311 = 553967) B553967
theorem B40517455 : Blo 366759 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B942527 : Blo 366759 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B54023273 : Blo 366759 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B2513405 : Blo 366759 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B1861055 : Blo 366759 1861055 := bstep (se 1 (by rfl) ⟨1395791, by rfl⟩ : syracuseStep 1861055 = 2791583) B2791583
theorem B2647979 : Blo 366759 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B36015515 : Blo 366759 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B1675603 : Blo 366759 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B1240703 : Blo 366759 1240703 := bstep (se 1 (by rfl) ⟨930527, by rfl⟩ : syracuseStep 1240703 = 1861055) B1861055
theorem B1765319 : Blo 366759 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B2234137 : Blo 366759 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B827135 : Blo 366759 827135 := bstep (se 1 (by rfl) ⟨620351, by rfl⟩ : syracuseStep 827135 = 1240703) B1240703
theorem B4707517 : Blo 366759 4707517 := bstep (se 3 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 4707517 = 1765319) B1765319
theorem B24010343 : Blo 366759 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B16006895 : Blo 366759 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B6276689 : Blo 366759 6276689 := bstep (se 2 (by rfl) ⟨2353758, by rfl⟩ : syracuseStep 6276689 = 4707517) B4707517
theorem B551423 : Blo 366759 551423 := bstep (se 1 (by rfl) ⟨413567, by rfl⟩ : syracuseStep 551423 = 827135) B827135
theorem B2978849 : Blo 366759 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B367615 : Blo 366759 367615 := bstep (se 1 (by rfl) ⟨275711, by rfl⟩ : syracuseStep 367615 = 551423) B551423
theorem B1985899 : Blo 366759 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B10671263 : Blo 366759 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B4184459 : Blo 366759 4184459 := bstep (se 1 (by rfl) ⟨3138344, by rfl⟩ : syracuseStep 4184459 = 6276689) B6276689
theorem B7114175 : Blo 366759 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B2789639 : Blo 366759 2789639 := bstep (se 1 (by rfl) ⟨2092229, by rfl⟩ : syracuseStep 2789639 = 4184459) B4184459
theorem B2647865 : Blo 366759 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B4742783 : Blo 366759 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B1859759 : Blo 366759 1859759 := bstep (se 1 (by rfl) ⟨1394819, by rfl⟩ : syracuseStep 1859759 = 2789639) B2789639
theorem B1765243 : Blo 366759 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B3161855 : Blo 366759 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B2353657 : Blo 366759 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B1239839 : Blo 366759 1239839 := bstep (se 1 (by rfl) ⟨929879, by rfl⟩ : syracuseStep 1239839 = 1859759) B1859759
theorem B826559 : Blo 366759 826559 := bstep (se 1 (by rfl) ⟨619919, by rfl⟩ : syracuseStep 826559 = 1239839) B1239839
theorem B2107903 : Blo 366759 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B3138209 : Blo 366759 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2810537 : Blo 366759 2810537 := bstep (se 2 (by rfl) ⟨1053951, by rfl⟩ : syracuseStep 2810537 = 2107903) B2107903
theorem B551039 : Blo 366759 551039 := bstep (se 1 (by rfl) ⟨413279, by rfl⟩ : syracuseStep 551039 = 826559) B826559
theorem B2092139 : Blo 366759 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B1873691 : Blo 366759 1873691 := bstep (se 1 (by rfl) ⟨1405268, by rfl⟩ : syracuseStep 1873691 = 2810537) B2810537
theorem B367359 : Blo 366759 367359 := bstep (se 1 (by rfl) ⟨275519, by rfl⟩ : syracuseStep 367359 = 551039) B551039
theorem B1394759 : Blo 366759 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B1249127 : Blo 366759 1249127 := bstep (se 1 (by rfl) ⟨936845, by rfl⟩ : syracuseStep 1249127 = 1873691) B1873691
theorem B929839 : Blo 366759 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B832751 : Blo 366759 832751 := bstep (se 1 (by rfl) ⟨624563, by rfl⟩ : syracuseStep 832751 = 1249127) B1249127
theorem B1239785 : Blo 366759 1239785 := bstep (se 2 (by rfl) ⟨464919, by rfl⟩ : syracuseStep 1239785 = 929839) B929839
theorem B826523 : Blo 366759 826523 := bstep (se 1 (by rfl) ⟨619892, by rfl⟩ : syracuseStep 826523 = 1239785) B1239785
theorem B555167 : Blo 366759 555167 := bstep (se 1 (by rfl) ⟨416375, by rfl⟩ : syracuseStep 555167 = 832751) B832751
theorem B370111 : Blo 366759 370111 := bstep (se 1 (by rfl) ⟨277583, by rfl⟩ : syracuseStep 370111 = 555167) B555167
theorem B551015 : Blo 366759 551015 := bstep (se 1 (by rfl) ⟨413261, by rfl⟩ : syracuseStep 551015 = 826523) B826523
theorem B367343 : Blo 366759 367343 := bstep (se 1 (by rfl) ⟨275507, by rfl⟩ : syracuseStep 367343 = 551015) B551015

theorem C0 (j : ℕ) (h1 : 91689 ≤ j) (h2 : j ≤ 92388) : Blo 366759 (4 * j + 3) := by
  interval_cases j
  · exact B366759
  · exact B366763
  · exact B366767
  · exact B366771
  · exact B366775
  · exact B366779
  · exact B366783
  · exact B366787
  · exact B366791
  · exact B366795
  · exact B366799
  · exact B366803
  · exact B366807
  · exact B366811
  · exact B366815
  · exact B366819
  · exact B366823
  · exact B366827
  · exact B366831
  · exact B366835
  · exact B366839
  · exact B366843
  · exact B366847
  · exact B366851
  · exact B366855
  · exact B366859
  · exact B366863
  · exact B366867
  · exact B366871
  · exact B366875
  · exact B366879
  · exact B366883
  · exact B366887
  · exact B366891
  · exact B366895
  · exact B366899
  · exact B366903
  · exact B366907
  · exact B366911
  · exact B366915
  · exact B366919
  · exact B366923
  · exact B366927
  · exact B366931
  · exact B366935
  · exact B366939
  · exact B366943
  · exact B366947
  · exact B366951
  · exact B366955
  · exact B366959
  · exact B366963
  · exact B366967
  · exact B366971
  · exact B366975
  · exact B366979
  · exact B366983
  · exact B366987
  · exact B366991
  · exact B366995
  · exact B366999
  · exact B367003
  · exact B367007
  · exact B367011
  · exact B367015
  · exact B367019
  · exact B367023
  · exact B367027
  · exact B367031
  · exact B367035
  · exact B367039
  · exact B367043
  · exact B367047
  · exact B367051
  · exact B367055
  · exact B367059
  · exact B367063
  · exact B367067
  · exact B367071
  · exact B367075
  · exact B367079
  · exact B367083
  · exact B367087
  · exact B367091
  · exact B367095
  · exact B367099
  · exact B367103
  · exact B367107
  · exact B367111
  · exact B367115
  · exact B367119
  · exact B367123
  · exact B367127
  · exact B367131
  · exact B367135
  · exact B367139
  · exact B367143
  · exact B367147
  · exact B367151
  · exact B367155
  · exact B367159
  · exact B367163
  · exact B367167
  · exact B367171
  · exact B367175
  · exact B367179
  · exact B367183
  · exact B367187
  · exact B367191
  · exact B367195
  · exact B367199
  · exact B367203
  · exact B367207
  · exact B367211
  · exact B367215
  · exact B367219
  · exact B367223
  · exact B367227
  · exact B367231
  · exact B367235
  · exact B367239
  · exact B367243
  · exact B367247
  · exact B367251
  · exact B367255
  · exact B367259
  · exact B367263
  · exact B367267
  · exact B367271
  · exact B367275
  · exact B367279
  · exact B367283
  · exact B367287
  · exact B367291
  · exact B367295
  · exact B367299
  · exact B367303
  · exact B367307
  · exact B367311
  · exact B367315
  · exact B367319
  · exact B367323
  · exact B367327
  · exact B367331
  · exact B367335
  · exact B367339
  · exact B367343
  · exact B367347
  · exact B367351
  · exact B367355
  · exact B367359
  · exact B367363
  · exact B367367
  · exact B367371
  · exact B367375
  · exact B367379
  · exact B367383
  · exact B367387
  · exact B367391
  · exact B367395
  · exact B367399
  · exact B367403
  · exact B367407
  · exact B367411
  · exact B367415
  · exact B367419
  · exact B367423
  · exact B367427
  · exact B367431
  · exact B367435
  · exact B367439
  · exact B367443
  · exact B367447
  · exact B367451
  · exact B367455
  · exact B367459
  · exact B367463
  · exact B367467
  · exact B367471
  · exact B367475
  · exact B367479
  · exact B367483
  · exact B367487
  · exact B367491
  · exact B367495
  · exact B367499
  · exact B367503
  · exact B367507
  · exact B367511
  · exact B367515
  · exact B367519
  · exact B367523
  · exact B367527
  · exact B367531
  · exact B367535
  · exact B367539
  · exact B367543
  · exact B367547
  · exact B367551
  · exact B367555
  · exact B367559
  · exact B367563
  · exact B367567
  · exact B367571
  · exact B367575
  · exact B367579
  · exact B367583
  · exact B367587
  · exact B367591
  · exact B367595
  · exact B367599
  · exact B367603
  · exact B367607
  · exact B367611
  · exact B367615
  · exact B367619
  · exact B367623
  · exact B367627
  · exact B367631
  · exact B367635
  · exact B367639
  · exact B367643
  · exact B367647
  · exact B367651
  · exact B367655
  · exact B367659
  · exact B367663
  · exact B367667
  · exact B367671
  · exact B367675
  · exact B367679
  · exact B367683
  · exact B367687
  · exact B367691
  · exact B367695
  · exact B367699
  · exact B367703
  · exact B367707
  · exact B367711
  · exact B367715
  · exact B367719
  · exact B367723
  · exact B367727
  · exact B367731
  · exact B367735
  · exact B367739
  · exact B367743
  · exact B367747
  · exact B367751
  · exact B367755
  · exact B367759
  · exact B367763
  · exact B367767
  · exact B367771
  · exact B367775
  · exact B367779
  · exact B367783
  · exact B367787
  · exact B367791
  · exact B367795
  · exact B367799
  · exact B367803
  · exact B367807
  · exact B367811
  · exact B367815
  · exact B367819
  · exact B367823
  · exact B367827
  · exact B367831
  · exact B367835
  · exact B367839
  · exact B367843
  · exact B367847
  · exact B367851
  · exact B367855
  · exact B367859
  · exact B367863
  · exact B367867
  · exact B367871
  · exact B367875
  · exact B367879
  · exact B367883
  · exact B367887
  · exact B367891
  · exact B367895
  · exact B367899
  · exact B367903
  · exact B367907
  · exact B367911
  · exact B367915
  · exact B367919
  · exact B367923
  · exact B367927
  · exact B367931
  · exact B367935
  · exact B367939
  · exact B367943
  · exact B367947
  · exact B367951
  · exact B367955
  · exact B367959
  · exact B367963
  · exact B367967
  · exact B367971
  · exact B367975
  · exact B367979
  · exact B367983
  · exact B367987
  · exact B367991
  · exact B367995
  · exact B367999
  · exact B368003
  · exact B368007
  · exact B368011
  · exact B368015
  · exact B368019
  · exact B368023
  · exact B368027
  · exact B368031
  · exact B368035
  · exact B368039
  · exact B368043
  · exact B368047
  · exact B368051
  · exact B368055
  · exact B368059
  · exact B368063
  · exact B368067
  · exact B368071
  · exact B368075
  · exact B368079
  · exact B368083
  · exact B368087
  · exact B368091
  · exact B368095
  · exact B368099
  · exact B368103
  · exact B368107
  · exact B368111
  · exact B368115
  · exact B368119
  · exact B368123
  · exact B368127
  · exact B368131
  · exact B368135
  · exact B368139
  · exact B368143
  · exact B368147
  · exact B368151
  · exact B368155
  · exact B368159
  · exact B368163
  · exact B368167
  · exact B368171
  · exact B368175
  · exact B368179
  · exact B368183
  · exact B368187
  · exact B368191
  · exact B368195
  · exact B368199
  · exact B368203
  · exact B368207
  · exact B368211
  · exact B368215
  · exact B368219
  · exact B368223
  · exact B368227
  · exact B368231
  · exact B368235
  · exact B368239
  · exact B368243
  · exact B368247
  · exact B368251
  · exact B368255
  · exact B368259
  · exact B368263
  · exact B368267
  · exact B368271
  · exact B368275
  · exact B368279
  · exact B368283
  · exact B368287
  · exact B368291
  · exact B368295
  · exact B368299
  · exact B368303
  · exact B368307
  · exact B368311
  · exact B368315
  · exact B368319
  · exact B368323
  · exact B368327
  · exact B368331
  · exact B368335
  · exact B368339
  · exact B368343
  · exact B368347
  · exact B368351
  · exact B368355
  · exact B368359
  · exact B368363
  · exact B368367
  · exact B368371
  · exact B368375
  · exact B368379
  · exact B368383
  · exact B368387
  · exact B368391
  · exact B368395
  · exact B368399
  · exact B368403
  · exact B368407
  · exact B368411
  · exact B368415
  · exact B368419
  · exact B368423
  · exact B368427
  · exact B368431
  · exact B368435
  · exact B368439
  · exact B368443
  · exact B368447
  · exact B368451
  · exact B368455
  · exact B368459
  · exact B368463
  · exact B368467
  · exact B368471
  · exact B368475
  · exact B368479
  · exact B368483
  · exact B368487
  · exact B368491
  · exact B368495
  · exact B368499
  · exact B368503
  · exact B368507
  · exact B368511
  · exact B368515
  · exact B368519
  · exact B368523
  · exact B368527
  · exact B368531
  · exact B368535
  · exact B368539
  · exact B368543
  · exact B368547
  · exact B368551
  · exact B368555
  · exact B368559
  · exact B368563
  · exact B368567
  · exact B368571
  · exact B368575
  · exact B368579
  · exact B368583
  · exact B368587
  · exact B368591
  · exact B368595
  · exact B368599
  · exact B368603
  · exact B368607
  · exact B368611
  · exact B368615
  · exact B368619
  · exact B368623
  · exact B368627
  · exact B368631
  · exact B368635
  · exact B368639
  · exact B368643
  · exact B368647
  · exact B368651
  · exact B368655
  · exact B368659
  · exact B368663
  · exact B368667
  · exact B368671
  · exact B368675
  · exact B368679
  · exact B368683
  · exact B368687
  · exact B368691
  · exact B368695
  · exact B368699
  · exact B368703
  · exact B368707
  · exact B368711
  · exact B368715
  · exact B368719
  · exact B368723
  · exact B368727
  · exact B368731
  · exact B368735
  · exact B368739
  · exact B368743
  · exact B368747
  · exact B368751
  · exact B368755
  · exact B368759
  · exact B368763
  · exact B368767
  · exact B368771
  · exact B368775
  · exact B368779
  · exact B368783
  · exact B368787
  · exact B368791
  · exact B368795
  · exact B368799
  · exact B368803
  · exact B368807
  · exact B368811
  · exact B368815
  · exact B368819
  · exact B368823
  · exact B368827
  · exact B368831
  · exact B368835
  · exact B368839
  · exact B368843
  · exact B368847
  · exact B368851
  · exact B368855
  · exact B368859
  · exact B368863
  · exact B368867
  · exact B368871
  · exact B368875
  · exact B368879
  · exact B368883
  · exact B368887
  · exact B368891
  · exact B368895
  · exact B368899
  · exact B368903
  · exact B368907
  · exact B368911
  · exact B368915
  · exact B368919
  · exact B368923
  · exact B368927
  · exact B368931
  · exact B368935
  · exact B368939
  · exact B368943
  · exact B368947
  · exact B368951
  · exact B368955
  · exact B368959
  · exact B368963
  · exact B368967
  · exact B368971
  · exact B368975
  · exact B368979
  · exact B368983
  · exact B368987
  · exact B368991
  · exact B368995
  · exact B368999
  · exact B369003
  · exact B369007
  · exact B369011
  · exact B369015
  · exact B369019
  · exact B369023
  · exact B369027
  · exact B369031
  · exact B369035
  · exact B369039
  · exact B369043
  · exact B369047
  · exact B369051
  · exact B369055
  · exact B369059
  · exact B369063
  · exact B369067
  · exact B369071
  · exact B369075
  · exact B369079
  · exact B369083
  · exact B369087
  · exact B369091
  · exact B369095
  · exact B369099
  · exact B369103
  · exact B369107
  · exact B369111
  · exact B369115
  · exact B369119
  · exact B369123
  · exact B369127
  · exact B369131
  · exact B369135
  · exact B369139
  · exact B369143
  · exact B369147
  · exact B369151
  · exact B369155
  · exact B369159
  · exact B369163
  · exact B369167
  · exact B369171
  · exact B369175
  · exact B369179
  · exact B369183
  · exact B369187
  · exact B369191
  · exact B369195
  · exact B369199
  · exact B369203
  · exact B369207
  · exact B369211
  · exact B369215
  · exact B369219
  · exact B369223
  · exact B369227
  · exact B369231
  · exact B369235
  · exact B369239
  · exact B369243
  · exact B369247
  · exact B369251
  · exact B369255
  · exact B369259
  · exact B369263
  · exact B369267
  · exact B369271
  · exact B369275
  · exact B369279
  · exact B369283
  · exact B369287
  · exact B369291
  · exact B369295
  · exact B369299
  · exact B369303
  · exact B369307
  · exact B369311
  · exact B369315
  · exact B369319
  · exact B369323
  · exact B369327
  · exact B369331
  · exact B369335
  · exact B369339
  · exact B369343
  · exact B369347
  · exact B369351
  · exact B369355
  · exact B369359
  · exact B369363
  · exact B369367
  · exact B369371
  · exact B369375
  · exact B369379
  · exact B369383
  · exact B369387
  · exact B369391
  · exact B369395
  · exact B369399
  · exact B369403
  · exact B369407
  · exact B369411
  · exact B369415
  · exact B369419
  · exact B369423
  · exact B369427
  · exact B369431
  · exact B369435
  · exact B369439
  · exact B369443
  · exact B369447
  · exact B369451
  · exact B369455
  · exact B369459
  · exact B369463
  · exact B369467
  · exact B369471
  · exact B369475
  · exact B369479
  · exact B369483
  · exact B369487
  · exact B369491
  · exact B369495
  · exact B369499
  · exact B369503
  · exact B369507
  · exact B369511
  · exact B369515
  · exact B369519
  · exact B369523
  · exact B369527
  · exact B369531
  · exact B369535
  · exact B369539
  · exact B369543
  · exact B369547
  · exact B369551
  · exact B369555

theorem C1 (j : ℕ) (h1 : 92389 ≤ j) (h2 : j ≤ 92689) : Blo 366759 (4 * j + 3) := by
  interval_cases j
  · exact B369559
  · exact B369563
  · exact B369567
  · exact B369571
  · exact B369575
  · exact B369579
  · exact B369583
  · exact B369587
  · exact B369591
  · exact B369595
  · exact B369599
  · exact B369603
  · exact B369607
  · exact B369611
  · exact B369615
  · exact B369619
  · exact B369623
  · exact B369627
  · exact B369631
  · exact B369635
  · exact B369639
  · exact B369643
  · exact B369647
  · exact B369651
  · exact B369655
  · exact B369659
  · exact B369663
  · exact B369667
  · exact B369671
  · exact B369675
  · exact B369679
  · exact B369683
  · exact B369687
  · exact B369691
  · exact B369695
  · exact B369699
  · exact B369703
  · exact B369707
  · exact B369711
  · exact B369715
  · exact B369719
  · exact B369723
  · exact B369727
  · exact B369731
  · exact B369735
  · exact B369739
  · exact B369743
  · exact B369747
  · exact B369751
  · exact B369755
  · exact B369759
  · exact B369763
  · exact B369767
  · exact B369771
  · exact B369775
  · exact B369779
  · exact B369783
  · exact B369787
  · exact B369791
  · exact B369795
  · exact B369799
  · exact B369803
  · exact B369807
  · exact B369811
  · exact B369815
  · exact B369819
  · exact B369823
  · exact B369827
  · exact B369831
  · exact B369835
  · exact B369839
  · exact B369843
  · exact B369847
  · exact B369851
  · exact B369855
  · exact B369859
  · exact B369863
  · exact B369867
  · exact B369871
  · exact B369875
  · exact B369879
  · exact B369883
  · exact B369887
  · exact B369891
  · exact B369895
  · exact B369899
  · exact B369903
  · exact B369907
  · exact B369911
  · exact B369915
  · exact B369919
  · exact B369923
  · exact B369927
  · exact B369931
  · exact B369935
  · exact B369939
  · exact B369943
  · exact B369947
  · exact B369951
  · exact B369955
  · exact B369959
  · exact B369963
  · exact B369967
  · exact B369971
  · exact B369975
  · exact B369979
  · exact B369983
  · exact B369987
  · exact B369991
  · exact B369995
  · exact B369999
  · exact B370003
  · exact B370007
  · exact B370011
  · exact B370015
  · exact B370019
  · exact B370023
  · exact B370027
  · exact B370031
  · exact B370035
  · exact B370039
  · exact B370043
  · exact B370047
  · exact B370051
  · exact B370055
  · exact B370059
  · exact B370063
  · exact B370067
  · exact B370071
  · exact B370075
  · exact B370079
  · exact B370083
  · exact B370087
  · exact B370091
  · exact B370095
  · exact B370099
  · exact B370103
  · exact B370107
  · exact B370111
  · exact B370115
  · exact B370119
  · exact B370123
  · exact B370127
  · exact B370131
  · exact B370135
  · exact B370139
  · exact B370143
  · exact B370147
  · exact B370151
  · exact B370155
  · exact B370159
  · exact B370163
  · exact B370167
  · exact B370171
  · exact B370175
  · exact B370179
  · exact B370183
  · exact B370187
  · exact B370191
  · exact B370195
  · exact B370199
  · exact B370203
  · exact B370207
  · exact B370211
  · exact B370215
  · exact B370219
  · exact B370223
  · exact B370227
  · exact B370231
  · exact B370235
  · exact B370239
  · exact B370243
  · exact B370247
  · exact B370251
  · exact B370255
  · exact B370259
  · exact B370263
  · exact B370267
  · exact B370271
  · exact B370275
  · exact B370279
  · exact B370283
  · exact B370287
  · exact B370291
  · exact B370295
  · exact B370299
  · exact B370303
  · exact B370307
  · exact B370311
  · exact B370315
  · exact B370319
  · exact B370323
  · exact B370327
  · exact B370331
  · exact B370335
  · exact B370339
  · exact B370343
  · exact B370347
  · exact B370351
  · exact B370355
  · exact B370359
  · exact B370363
  · exact B370367
  · exact B370371
  · exact B370375
  · exact B370379
  · exact B370383
  · exact B370387
  · exact B370391
  · exact B370395
  · exact B370399
  · exact B370403
  · exact B370407
  · exact B370411
  · exact B370415
  · exact B370419
  · exact B370423
  · exact B370427
  · exact B370431
  · exact B370435
  · exact B370439
  · exact B370443
  · exact B370447
  · exact B370451
  · exact B370455
  · exact B370459
  · exact B370463
  · exact B370467
  · exact B370471
  · exact B370475
  · exact B370479
  · exact B370483
  · exact B370487
  · exact B370491
  · exact B370495
  · exact B370499
  · exact B370503
  · exact B370507
  · exact B370511
  · exact B370515
  · exact B370519
  · exact B370523
  · exact B370527
  · exact B370531
  · exact B370535
  · exact B370539
  · exact B370543
  · exact B370547
  · exact B370551
  · exact B370555
  · exact B370559
  · exact B370563
  · exact B370567
  · exact B370571
  · exact B370575
  · exact B370579
  · exact B370583
  · exact B370587
  · exact B370591
  · exact B370595
  · exact B370599
  · exact B370603
  · exact B370607
  · exact B370611
  · exact B370615
  · exact B370619
  · exact B370623
  · exact B370627
  · exact B370631
  · exact B370635
  · exact B370639
  · exact B370643
  · exact B370647
  · exact B370651
  · exact B370655
  · exact B370659
  · exact B370663
  · exact B370667
  · exact B370671
  · exact B370675
  · exact B370679
  · exact B370683
  · exact B370687
  · exact B370691
  · exact B370695
  · exact B370699
  · exact B370703
  · exact B370707
  · exact B370711
  · exact B370715
  · exact B370719
  · exact B370723
  · exact B370727
  · exact B370731
  · exact B370735
  · exact B370739
  · exact B370743
  · exact B370747
  · exact B370751
  · exact B370755
  · exact B370759

theorem solution (m : ℕ) (hlo : 366759 ≤ m) (hhi : m ≤ 370759) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 91689 ≤ j := by omega
    have hj2 : j ≤ 92689 := by omega
    have hb : Blo 366759 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 92389 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
