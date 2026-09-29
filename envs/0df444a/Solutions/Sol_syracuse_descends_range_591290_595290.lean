-- Prove2me | solution 1 for syracuse_descends_range_591290_595290
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:26.699666+00:00
-- url     : https://prove2.me/submissions/1f3380a9-703d-4550-95d5-2a89c1563585

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


theorem B1441813 : Blo 591290 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B1998917 : Blo 591290 1998917 := bbase (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) (by norm_num)
theorem B1999349 : Blo 591290 1999349 := bbase (se 5 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 1999349 = 187439) (by norm_num)
theorem B1901141 : Blo 591290 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B1016477 : Blo 591290 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B1999781 : Blo 591290 1999781 := bbase (se 4 (by rfl) ⟨187479, by rfl⟩ : syracuseStep 1999781 = 374959) (by norm_num)
theorem B951205 : Blo 591290 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B721841 : Blo 591290 721841 := bbase (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) (by norm_num)
theorem B3376181 : Blo 591290 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B1803541 : Blo 591290 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B2000213 : Blo 591290 2000213 := bbase (se 12 (by rfl) ⟨732, by rfl⟩ : syracuseStep 2000213 = 1465) (by norm_num)
theorem B951653 : Blo 591290 951653 := bbase (se 4 (by rfl) ⟨89217, by rfl⟩ : syracuseStep 951653 = 178435) (by norm_num)
theorem B722369 : Blo 591290 722369 := bbase (se 2 (by rfl) ⟨270888, by rfl⟩ : syracuseStep 722369 = 541777) (by norm_num)
theorem B1607125 : Blo 591290 1607125 := bbase (se 7 (by rfl) ⟨18833, by rfl⟩ : syracuseStep 1607125 = 37667) (by norm_num)
theorem B2000645 : Blo 591290 2000645 := bbase (se 4 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 2000645 = 375121) (by norm_num)
theorem B4491125 : Blo 591290 4491125 := bbase (se 5 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 4491125 = 421043) (by norm_num)
theorem B1902485 : Blo 591290 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B2131877 : Blo 591290 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B3803125 : Blo 591290 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B886949 : Blo 591290 886949 := bbase (se 4 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 886949 = 166303) (by norm_num)
theorem B2001077 : Blo 591290 2001077 := bbase (se 5 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 2001077 = 187601) (by norm_num)
theorem B886973 : Blo 591290 886973 := bbase (se 3 (by rfl) ⟨166307, by rfl⟩ : syracuseStep 886973 = 332615) (by norm_num)
theorem B886997 : Blo 591290 886997 := bbase (se 7 (by rfl) ⟨10394, by rfl⟩ : syracuseStep 886997 = 20789) (by norm_num)
theorem B887021 : Blo 591290 887021 := bbase (se 3 (by rfl) ⟨166316, by rfl⟩ : syracuseStep 887021 = 332633) (by norm_num)
theorem B821485 : Blo 591290 821485 := bbase (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) (by norm_num)
theorem B887045 : Blo 591290 887045 := bbase (se 4 (by rfl) ⟨83160, by rfl⟩ : syracuseStep 887045 = 166321) (by norm_num)
theorem B887069 : Blo 591290 887069 := bbase (se 3 (by rfl) ⟨166325, by rfl⟩ : syracuseStep 887069 = 332651) (by norm_num)
theorem B887093 : Blo 591290 887093 := bbase (se 5 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 887093 = 83165) (by norm_num)
theorem B887117 : Blo 591290 887117 := bbase (se 3 (by rfl) ⟨166334, by rfl⟩ : syracuseStep 887117 = 332669) (by norm_num)
theorem B887141 : Blo 591290 887141 := bbase (se 4 (by rfl) ⟨83169, by rfl⟩ : syracuseStep 887141 = 166339) (by norm_num)
theorem B887165 : Blo 591290 887165 := bbase (se 3 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 887165 = 332687) (by norm_num)
theorem B887189 : Blo 591290 887189 := bbase (se 6 (by rfl) ⟨20793, by rfl⟩ : syracuseStep 887189 = 41587) (by norm_num)
theorem B887213 : Blo 591290 887213 := bbase (se 3 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 887213 = 332705) (by norm_num)
theorem B854453 : Blo 591290 854453 := bbase (se 5 (by rfl) ⟨40052, by rfl⟩ : syracuseStep 854453 = 80105) (by norm_num)
theorem B887237 : Blo 591290 887237 := bbase (se 4 (by rfl) ⟨83178, by rfl⟩ : syracuseStep 887237 = 166357) (by norm_num)
theorem B887261 : Blo 591290 887261 := bbase (se 3 (by rfl) ⟨166361, by rfl⟩ : syracuseStep 887261 = 332723) (by norm_num)
theorem B887285 : Blo 591290 887285 := bbase (se 5 (by rfl) ⟨41591, by rfl⟩ : syracuseStep 887285 = 83183) (by norm_num)
theorem B887309 : Blo 591290 887309 := bbase (se 3 (by rfl) ⟨166370, by rfl⟩ : syracuseStep 887309 = 332741) (by norm_num)
theorem B887333 : Blo 591290 887333 := bbase (se 4 (by rfl) ⟨83187, by rfl⟩ : syracuseStep 887333 = 166375) (by norm_num)
theorem B887357 : Blo 591290 887357 := bbase (se 3 (by rfl) ⟨166379, by rfl⟩ : syracuseStep 887357 = 332759) (by norm_num)
theorem B887381 : Blo 591290 887381 := bbase (se 8 (by rfl) ⟨5199, by rfl⟩ : syracuseStep 887381 = 10399) (by norm_num)
theorem B2001509 : Blo 591290 2001509 := bbase (se 4 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 2001509 = 375283) (by norm_num)
theorem B887405 : Blo 591290 887405 := bbase (se 3 (by rfl) ⟨166388, by rfl⟩ : syracuseStep 887405 = 332777) (by norm_num)
theorem B887429 : Blo 591290 887429 := bbase (se 4 (by rfl) ⟨83196, by rfl⟩ : syracuseStep 887429 = 166393) (by norm_num)
theorem B887453 : Blo 591290 887453 := bbase (se 3 (by rfl) ⟨166397, by rfl⟩ : syracuseStep 887453 = 332795) (by norm_num)
theorem B887477 : Blo 591290 887477 := bbase (se 5 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 887477 = 83201) (by norm_num)
theorem B887501 : Blo 591290 887501 := bbase (se 3 (by rfl) ⟨166406, by rfl⟩ : syracuseStep 887501 = 332813) (by norm_num)
theorem B887525 : Blo 591290 887525 := bbase (se 4 (by rfl) ⟨83205, by rfl⟩ : syracuseStep 887525 = 166411) (by norm_num)
theorem B887549 : Blo 591290 887549 := bbase (se 3 (by rfl) ⟨166415, by rfl⟩ : syracuseStep 887549 = 332831) (by norm_num)
theorem B887573 : Blo 591290 887573 := bbase (se 6 (by rfl) ⟨20802, by rfl⟩ : syracuseStep 887573 = 41605) (by norm_num)
theorem B1542941 : Blo 591290 1542941 := bbase (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) (by norm_num)
theorem B887597 : Blo 591290 887597 := bbase (se 3 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 887597 = 332849) (by norm_num)
theorem B887621 : Blo 591290 887621 := bbase (se 4 (by rfl) ⟨83214, by rfl⟩ : syracuseStep 887621 = 166429) (by norm_num)
theorem B953165 : Blo 591290 953165 := bbase (se 3 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 953165 = 357437) (by norm_num)
theorem B887645 : Blo 591290 887645 := bbase (se 3 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 887645 = 332867) (by norm_num)
theorem B887669 : Blo 591290 887669 := bbase (se 5 (by rfl) ⟨41609, by rfl⟩ : syracuseStep 887669 = 83219) (by norm_num)
theorem B887693 : Blo 591290 887693 := bbase (se 3 (by rfl) ⟨166442, by rfl⟩ : syracuseStep 887693 = 332885) (by norm_num)
theorem B887717 : Blo 591290 887717 := bbase (se 4 (by rfl) ⟨83223, by rfl⟩ : syracuseStep 887717 = 166447) (by norm_num)
theorem B887741 : Blo 591290 887741 := bbase (se 3 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 887741 = 332903) (by norm_num)
theorem B953293 : Blo 591290 953293 := bbase (se 3 (by rfl) ⟨178742, by rfl⟩ : syracuseStep 953293 = 357485) (by norm_num)
theorem B887765 : Blo 591290 887765 := bbase (se 7 (by rfl) ⟨10403, by rfl⟩ : syracuseStep 887765 = 20807) (by norm_num)
theorem B887789 : Blo 591290 887789 := bbase (se 3 (by rfl) ⟨166460, by rfl⟩ : syracuseStep 887789 = 332921) (by norm_num)
theorem B887813 : Blo 591290 887813 := bbase (se 4 (by rfl) ⟨83232, by rfl⟩ : syracuseStep 887813 = 166465) (by norm_num)
theorem B2001941 : Blo 591290 2001941 := bbase (se 6 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 2001941 = 93841) (by norm_num)
theorem B887837 : Blo 591290 887837 := bbase (se 3 (by rfl) ⟨166469, by rfl⟩ : syracuseStep 887837 = 332939) (by norm_num)
theorem B887861 : Blo 591290 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B887885 : Blo 591290 887885 := bbase (se 3 (by rfl) ⟨166478, by rfl⟩ : syracuseStep 887885 = 332957) (by norm_num)
theorem B887909 : Blo 591290 887909 := bbase (se 4 (by rfl) ⟨83241, by rfl⟩ : syracuseStep 887909 = 166483) (by norm_num)
theorem B887933 : Blo 591290 887933 := bbase (se 3 (by rfl) ⟨166487, by rfl⟩ : syracuseStep 887933 = 332975) (by norm_num)
theorem B887957 : Blo 591290 887957 := bbase (se 6 (by rfl) ⟨20811, by rfl⟩ : syracuseStep 887957 = 41623) (by norm_num)
theorem B887981 : Blo 591290 887981 := bbase (se 3 (by rfl) ⟨166496, by rfl⟩ : syracuseStep 887981 = 332993) (by norm_num)
theorem B888005 : Blo 591290 888005 := bbase (se 4 (by rfl) ⟨83250, by rfl⟩ : syracuseStep 888005 = 166501) (by norm_num)
theorem B888029 : Blo 591290 888029 := bbase (se 3 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 888029 = 333011) (by norm_num)
theorem B888053 : Blo 591290 888053 := bbase (se 5 (by rfl) ⟨41627, by rfl⟩ : syracuseStep 888053 = 83255) (by norm_num)
theorem B888077 : Blo 591290 888077 := bbase (se 3 (by rfl) ⟨166514, by rfl⟩ : syracuseStep 888077 = 333029) (by norm_num)
theorem B1084693 : Blo 591290 1084693 := bbase (se 6 (by rfl) ⟨25422, by rfl⟩ : syracuseStep 1084693 = 50845) (by norm_num)
theorem B888101 : Blo 591290 888101 := bbase (se 4 (by rfl) ⟨83259, by rfl⟩ : syracuseStep 888101 = 166519) (by norm_num)
theorem B888125 : Blo 591290 888125 := bbase (se 3 (by rfl) ⟨166523, by rfl⟩ : syracuseStep 888125 = 333047) (by norm_num)
theorem B888149 : Blo 591290 888149 := bbase (se 11 (by rfl) ⟨650, by rfl⟩ : syracuseStep 888149 = 1301) (by norm_num)
theorem B888173 : Blo 591290 888173 := bbase (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) (by norm_num)
theorem B888197 : Blo 591290 888197 := bbase (se 4 (by rfl) ⟨83268, by rfl⟩ : syracuseStep 888197 = 166537) (by norm_num)
theorem B888221 : Blo 591290 888221 := bbase (se 3 (by rfl) ⟨166541, by rfl⟩ : syracuseStep 888221 = 333083) (by norm_num)
theorem B888245 : Blo 591290 888245 := bbase (se 5 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 888245 = 83273) (by norm_num)
theorem B2002373 : Blo 591290 2002373 := bbase (se 4 (by rfl) ⟨187722, by rfl⟩ : syracuseStep 2002373 = 375445) (by norm_num)
theorem B888269 : Blo 591290 888269 := bbase (se 3 (by rfl) ⟨166550, by rfl⟩ : syracuseStep 888269 = 333101) (by norm_num)
theorem B888293 : Blo 591290 888293 := bbase (se 4 (by rfl) ⟨83277, by rfl⟩ : syracuseStep 888293 = 166555) (by norm_num)
theorem B888317 : Blo 591290 888317 := bbase (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) (by norm_num)
theorem B888341 : Blo 591290 888341 := bbase (se 6 (by rfl) ⟨20820, by rfl⟩ : syracuseStep 888341 = 41641) (by norm_num)
theorem B888365 : Blo 591290 888365 := bbase (se 3 (by rfl) ⟨166568, by rfl⟩ : syracuseStep 888365 = 333137) (by norm_num)
theorem B888389 : Blo 591290 888389 := bbase (se 4 (by rfl) ⟨83286, by rfl⟩ : syracuseStep 888389 = 166573) (by norm_num)
theorem B2526805 : Blo 591290 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B888413 : Blo 591290 888413 := bbase (se 3 (by rfl) ⟨166577, by rfl⟩ : syracuseStep 888413 = 333155) (by norm_num)
theorem B888437 : Blo 591290 888437 := bbase (se 5 (by rfl) ⟨41645, by rfl⟩ : syracuseStep 888437 = 83291) (by norm_num)
theorem B888461 : Blo 591290 888461 := bbase (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) (by norm_num)
theorem B888485 : Blo 591290 888485 := bbase (se 4 (by rfl) ⟨83295, by rfl⟩ : syracuseStep 888485 = 166591) (by norm_num)
theorem B3051173 : Blo 591290 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B888509 : Blo 591290 888509 := bbase (se 3 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 888509 = 333191) (by norm_num)
theorem B888533 : Blo 591290 888533 := bbase (se 7 (by rfl) ⟨10412, by rfl⟩ : syracuseStep 888533 = 20825) (by norm_num)
theorem B888557 : Blo 591290 888557 := bbase (se 3 (by rfl) ⟨166604, by rfl⟩ : syracuseStep 888557 = 333209) (by norm_num)
theorem B888581 : Blo 591290 888581 := bbase (se 4 (by rfl) ⟨83304, by rfl⟩ : syracuseStep 888581 = 166609) (by norm_num)
theorem B888605 : Blo 591290 888605 := bbase (se 3 (by rfl) ⟨166613, by rfl⟩ : syracuseStep 888605 = 333227) (by norm_num)
theorem B888629 : Blo 591290 888629 := bbase (se 5 (by rfl) ⟨41654, by rfl⟩ : syracuseStep 888629 = 83309) (by norm_num)
theorem B888653 : Blo 591290 888653 := bbase (se 3 (by rfl) ⟨166622, by rfl⟩ : syracuseStep 888653 = 333245) (by norm_num)
theorem B888677 : Blo 591290 888677 := bbase (se 4 (by rfl) ⟨83313, by rfl⟩ : syracuseStep 888677 = 166627) (by norm_num)
theorem B1904485 : Blo 591290 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B2002805 : Blo 591290 2002805 := bbase (se 5 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 2002805 = 187763) (by norm_num)
theorem B888701 : Blo 591290 888701 := bbase (se 3 (by rfl) ⟨166631, by rfl⟩ : syracuseStep 888701 = 333263) (by norm_num)
theorem B888725 : Blo 591290 888725 := bbase (se 6 (by rfl) ⟨20829, by rfl⟩ : syracuseStep 888725 = 41659) (by norm_num)
theorem B888749 : Blo 591290 888749 := bbase (se 3 (by rfl) ⟨166640, by rfl⟩ : syracuseStep 888749 = 333281) (by norm_num)
theorem B888773 : Blo 591290 888773 := bbase (se 4 (by rfl) ⟨83322, by rfl⟩ : syracuseStep 888773 = 166645) (by norm_num)
theorem B888797 : Blo 591290 888797 := bbase (se 3 (by rfl) ⟨166649, by rfl⟩ : syracuseStep 888797 = 333299) (by norm_num)
theorem B888821 : Blo 591290 888821 := bbase (se 5 (by rfl) ⟨41663, by rfl⟩ : syracuseStep 888821 = 83327) (by norm_num)
theorem B888845 : Blo 591290 888845 := bbase (se 3 (by rfl) ⟨166658, by rfl⟩ : syracuseStep 888845 = 333317) (by norm_num)
theorem B888869 : Blo 591290 888869 := bbase (se 4 (by rfl) ⟨83331, by rfl⟩ : syracuseStep 888869 = 166663) (by norm_num)
theorem B888893 : Blo 591290 888893 := bbase (se 3 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 888893 = 333335) (by norm_num)
theorem B888917 : Blo 591290 888917 := bbase (se 8 (by rfl) ⟨5208, by rfl⟩ : syracuseStep 888917 = 10417) (by norm_num)
theorem B888941 : Blo 591290 888941 := bbase (se 3 (by rfl) ⟨166676, by rfl⟩ : syracuseStep 888941 = 333353) (by norm_num)
theorem B888965 : Blo 591290 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B6426773 : Blo 591290 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B888989 : Blo 591290 888989 := bbase (se 3 (by rfl) ⟨166685, by rfl⟩ : syracuseStep 888989 = 333371) (by norm_num)
theorem B889013 : Blo 591290 889013 := bbase (se 5 (by rfl) ⟨41672, by rfl⟩ : syracuseStep 889013 = 83345) (by norm_num)
theorem B889037 : Blo 591290 889037 := bbase (se 3 (by rfl) ⟨166694, by rfl⟩ : syracuseStep 889037 = 333389) (by norm_num)
theorem B889061 : Blo 591290 889061 := bbase (se 4 (by rfl) ⟨83349, by rfl⟩ : syracuseStep 889061 = 166699) (by norm_num)
theorem B889085 : Blo 591290 889085 := bbase (se 3 (by rfl) ⟨166703, by rfl⟩ : syracuseStep 889085 = 333407) (by norm_num)
theorem B889109 : Blo 591290 889109 := bbase (se 6 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 889109 = 41677) (by norm_num)
theorem B2855189 : Blo 591290 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B2003237 : Blo 591290 2003237 := bbase (se 4 (by rfl) ⟨187803, by rfl⟩ : syracuseStep 2003237 = 375607) (by norm_num)
theorem B889133 : Blo 591290 889133 := bbase (se 3 (by rfl) ⟨166712, by rfl⟩ : syracuseStep 889133 = 333425) (by norm_num)
theorem B889157 : Blo 591290 889157 := bbase (se 4 (by rfl) ⟨83358, by rfl⟩ : syracuseStep 889157 = 166717) (by norm_num)
theorem B889181 : Blo 591290 889181 := bbase (se 3 (by rfl) ⟨166721, by rfl⟩ : syracuseStep 889181 = 333443) (by norm_num)
theorem B889205 : Blo 591290 889205 := bbase (se 5 (by rfl) ⟨41681, by rfl⟩ : syracuseStep 889205 = 83363) (by norm_num)
theorem B889229 : Blo 591290 889229 := bbase (se 3 (by rfl) ⟨166730, by rfl⟩ : syracuseStep 889229 = 333461) (by norm_num)
theorem B889253 : Blo 591290 889253 := bbase (se 4 (by rfl) ⟨83367, by rfl⟩ : syracuseStep 889253 = 166735) (by norm_num)
theorem B889277 : Blo 591290 889277 := bbase (se 3 (by rfl) ⟨166739, by rfl⟩ : syracuseStep 889277 = 333479) (by norm_num)
theorem B889301 : Blo 591290 889301 := bbase (se 7 (by rfl) ⟨10421, by rfl⟩ : syracuseStep 889301 = 20843) (by norm_num)
theorem B889325 : Blo 591290 889325 := bbase (se 3 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 889325 = 333497) (by norm_num)
theorem B889349 : Blo 591290 889349 := bbase (se 4 (by rfl) ⟨83376, by rfl⟩ : syracuseStep 889349 = 166753) (by norm_num)
theorem B889373 : Blo 591290 889373 := bbase (se 3 (by rfl) ⟨166757, by rfl⟩ : syracuseStep 889373 = 333515) (by norm_num)
theorem B889397 : Blo 591290 889397 := bbase (se 5 (by rfl) ⟨41690, by rfl⟩ : syracuseStep 889397 = 83381) (by norm_num)
theorem B889421 : Blo 591290 889421 := bbase (se 3 (by rfl) ⟨166766, by rfl⟩ : syracuseStep 889421 = 333533) (by norm_num)
theorem B1282645 : Blo 591290 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B889445 : Blo 591290 889445 := bbase (se 4 (by rfl) ⟨83385, by rfl⟩ : syracuseStep 889445 = 166771) (by norm_num)
theorem B889469 : Blo 591290 889469 := bbase (se 3 (by rfl) ⟨166775, by rfl⟩ : syracuseStep 889469 = 333551) (by norm_num)
theorem B889493 : Blo 591290 889493 := bbase (se 6 (by rfl) ⟨20847, by rfl⟩ : syracuseStep 889493 = 41695) (by norm_num)
theorem B889517 : Blo 591290 889517 := bbase (se 3 (by rfl) ⟨166784, by rfl⟩ : syracuseStep 889517 = 333569) (by norm_num)
theorem B889541 : Blo 591290 889541 := bbase (se 4 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 889541 = 166789) (by norm_num)
theorem B2003669 : Blo 591290 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B889565 : Blo 591290 889565 := bbase (se 3 (by rfl) ⟨166793, by rfl⟩ : syracuseStep 889565 = 333587) (by norm_num)
theorem B889589 : Blo 591290 889589 := bbase (se 5 (by rfl) ⟨41699, by rfl⟩ : syracuseStep 889589 = 83399) (by norm_num)
theorem B889613 : Blo 591290 889613 := bbase (se 3 (by rfl) ⟨166802, by rfl⟩ : syracuseStep 889613 = 333605) (by norm_num)
theorem B3805973 : Blo 591290 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B889637 : Blo 591290 889637 := bbase (se 4 (by rfl) ⟨83403, by rfl⟩ : syracuseStep 889637 = 166807) (by norm_num)
theorem B889661 : Blo 591290 889661 := bbase (se 3 (by rfl) ⟨166811, by rfl⟩ : syracuseStep 889661 = 333623) (by norm_num)
theorem B889685 : Blo 591290 889685 := bbase (se 9 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 889685 = 5213) (by norm_num)
theorem B889709 : Blo 591290 889709 := bbase (se 3 (by rfl) ⟨166820, by rfl⟩ : syracuseStep 889709 = 333641) (by norm_num)
theorem B889733 : Blo 591290 889733 := bbase (se 4 (by rfl) ⟨83412, by rfl⟩ : syracuseStep 889733 = 166825) (by norm_num)
theorem B889757 : Blo 591290 889757 := bbase (se 3 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 889757 = 333659) (by norm_num)
theorem B889781 : Blo 591290 889781 := bbase (se 5 (by rfl) ⟨41708, by rfl⟩ : syracuseStep 889781 = 83417) (by norm_num)
theorem B889805 : Blo 591290 889805 := bbase (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) (by norm_num)
theorem B889829 : Blo 591290 889829 := bbase (se 4 (by rfl) ⟨83421, by rfl⟩ : syracuseStep 889829 = 166843) (by norm_num)
theorem B889853 : Blo 591290 889853 := bbase (se 3 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 889853 = 333695) (by norm_num)
theorem B1086461 : Blo 591290 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B889877 : Blo 591290 889877 := bbase (se 6 (by rfl) ⟨20856, by rfl⟩ : syracuseStep 889877 = 41713) (by norm_num)
theorem B2528293 : Blo 591290 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B889901 : Blo 591290 889901 := bbase (se 3 (by rfl) ⟨166856, by rfl⟩ : syracuseStep 889901 = 333713) (by norm_num)
theorem B2528309 : Blo 591290 2528309 := bbase (se 5 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 2528309 = 237029) (by norm_num)
theorem B889925 : Blo 591290 889925 := bbase (se 4 (by rfl) ⟨83430, by rfl⟩ : syracuseStep 889925 = 166861) (by norm_num)
theorem B889949 : Blo 591290 889949 := bbase (se 3 (by rfl) ⟨166865, by rfl⟩ : syracuseStep 889949 = 333731) (by norm_num)
theorem B889973 : Blo 591290 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B2004101 : Blo 591290 2004101 := bbase (se 4 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 2004101 = 375769) (by norm_num)
theorem B889997 : Blo 591290 889997 := bbase (se 3 (by rfl) ⟨166874, by rfl⟩ : syracuseStep 889997 = 333749) (by norm_num)
theorem B890021 : Blo 591290 890021 := bbase (se 4 (by rfl) ⟨83439, by rfl⟩ : syracuseStep 890021 = 166879) (by norm_num)
theorem B890045 : Blo 591290 890045 := bbase (se 3 (by rfl) ⟨166883, by rfl⟩ : syracuseStep 890045 = 333767) (by norm_num)
theorem B890069 : Blo 591290 890069 := bbase (se 7 (by rfl) ⟨10430, by rfl⟩ : syracuseStep 890069 = 20861) (by norm_num)
theorem B890093 : Blo 591290 890093 := bbase (se 3 (by rfl) ⟨166892, by rfl⟩ : syracuseStep 890093 = 333785) (by norm_num)
theorem B890117 : Blo 591290 890117 := bbase (se 4 (by rfl) ⟨83448, by rfl⟩ : syracuseStep 890117 = 166897) (by norm_num)
theorem B890141 : Blo 591290 890141 := bbase (se 3 (by rfl) ⟨166901, by rfl⟩ : syracuseStep 890141 = 333803) (by norm_num)
theorem B890165 : Blo 591290 890165 := bbase (se 5 (by rfl) ⟨41726, by rfl⟩ : syracuseStep 890165 = 83453) (by norm_num)
theorem B890189 : Blo 591290 890189 := bbase (se 3 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 890189 = 333821) (by norm_num)
theorem B890213 : Blo 591290 890213 := bbase (se 4 (by rfl) ⟨83457, by rfl⟩ : syracuseStep 890213 = 166915) (by norm_num)
theorem B759145 : Blo 591290 759145 := bbase (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) (by norm_num)
theorem B890237 : Blo 591290 890237 := bbase (se 3 (by rfl) ⟨166919, by rfl⟩ : syracuseStep 890237 = 333839) (by norm_num)
theorem B890261 : Blo 591290 890261 := bbase (se 6 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 890261 = 41731) (by norm_num)
theorem B890285 : Blo 591290 890285 := bbase (se 3 (by rfl) ⟨166928, by rfl⟩ : syracuseStep 890285 = 333857) (by norm_num)
theorem B890309 : Blo 591290 890309 := bbase (se 4 (by rfl) ⟨83466, by rfl⟩ : syracuseStep 890309 = 166933) (by norm_num)
theorem B890333 : Blo 591290 890333 := bbase (se 3 (by rfl) ⟨166937, by rfl⟩ : syracuseStep 890333 = 333875) (by norm_num)
theorem B890357 : Blo 591290 890357 := bbase (se 5 (by rfl) ⟨41735, by rfl⟩ : syracuseStep 890357 = 83471) (by norm_num)
theorem B759305 : Blo 591290 759305 := bbase (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) (by norm_num)
theorem B890381 : Blo 591290 890381 := bbase (se 3 (by rfl) ⟨166946, by rfl⟩ : syracuseStep 890381 = 333893) (by norm_num)
theorem B890405 : Blo 591290 890405 := bbase (se 4 (by rfl) ⟨83475, by rfl⟩ : syracuseStep 890405 = 166951) (by norm_num)
theorem B2004533 : Blo 591290 2004533 := bbase (se 5 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 2004533 = 187925) (by norm_num)
theorem B890429 : Blo 591290 890429 := bbase (se 3 (by rfl) ⟨166955, by rfl⟩ : syracuseStep 890429 = 333911) (by norm_num)
theorem B890453 : Blo 591290 890453 := bbase (se 8 (by rfl) ⟨5217, by rfl⟩ : syracuseStep 890453 = 10435) (by norm_num)
theorem B890477 : Blo 591290 890477 := bbase (se 3 (by rfl) ⟨166964, by rfl⟩ : syracuseStep 890477 = 333929) (by norm_num)
theorem B890501 : Blo 591290 890501 := bbase (se 4 (by rfl) ⟨83484, by rfl⟩ : syracuseStep 890501 = 166969) (by norm_num)
theorem B890525 : Blo 591290 890525 := bbase (se 3 (by rfl) ⟨166973, by rfl⟩ : syracuseStep 890525 = 333947) (by norm_num)
theorem B890549 : Blo 591290 890549 := bbase (se 5 (by rfl) ⟨41744, by rfl⟩ : syracuseStep 890549 = 83489) (by norm_num)
theorem B890573 : Blo 591290 890573 := bbase (se 3 (by rfl) ⟨166982, by rfl⟩ : syracuseStep 890573 = 333965) (by norm_num)
theorem B890597 : Blo 591290 890597 := bbase (se 4 (by rfl) ⟨83493, by rfl⟩ : syracuseStep 890597 = 166987) (by norm_num)
theorem B890621 : Blo 591290 890621 := bbase (se 3 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 890621 = 333983) (by norm_num)
theorem B890645 : Blo 591290 890645 := bbase (se 6 (by rfl) ⟨20874, by rfl⟩ : syracuseStep 890645 = 41749) (by norm_num)
theorem B694057 : Blo 591290 694057 := bbase (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) (by norm_num)
theorem B890669 : Blo 591290 890669 := bbase (se 3 (by rfl) ⟨167000, by rfl⟩ : syracuseStep 890669 = 334001) (by norm_num)
theorem B890693 : Blo 591290 890693 := bbase (se 4 (by rfl) ⟨83502, by rfl⟩ : syracuseStep 890693 = 167005) (by norm_num)
theorem B890717 : Blo 591290 890717 := bbase (se 3 (by rfl) ⟨167009, by rfl⟩ : syracuseStep 890717 = 334019) (by norm_num)
theorem B890741 : Blo 591290 890741 := bbase (se 5 (by rfl) ⟨41753, by rfl⟩ : syracuseStep 890741 = 83507) (by norm_num)
theorem B890765 : Blo 591290 890765 := bbase (se 3 (by rfl) ⟨167018, by rfl⟩ : syracuseStep 890765 = 334037) (by norm_num)
theorem B890789 : Blo 591290 890789 := bbase (se 4 (by rfl) ⟨83511, by rfl⟩ : syracuseStep 890789 = 167023) (by norm_num)
theorem B890813 : Blo 591290 890813 := bbase (se 3 (by rfl) ⟨167027, by rfl⟩ : syracuseStep 890813 = 334055) (by norm_num)
theorem B890837 : Blo 591290 890837 := bbase (se 7 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 890837 = 20879) (by norm_num)
theorem B2004965 : Blo 591290 2004965 := bbase (se 4 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 2004965 = 375931) (by norm_num)
theorem B890861 : Blo 591290 890861 := bbase (se 3 (by rfl) ⟨167036, by rfl⟩ : syracuseStep 890861 = 334073) (by norm_num)
theorem B890885 : Blo 591290 890885 := bbase (se 4 (by rfl) ⟨83520, by rfl⟩ : syracuseStep 890885 = 167041) (by norm_num)
theorem B890909 : Blo 591290 890909 := bbase (se 3 (by rfl) ⟨167045, by rfl⟩ : syracuseStep 890909 = 334091) (by norm_num)
theorem B890933 : Blo 591290 890933 := bbase (se 5 (by rfl) ⟨41762, by rfl⟩ : syracuseStep 890933 = 83525) (by norm_num)
theorem B890957 : Blo 591290 890957 := bbase (se 3 (by rfl) ⟨167054, by rfl⟩ : syracuseStep 890957 = 334109) (by norm_num)
theorem B890981 : Blo 591290 890981 := bbase (se 4 (by rfl) ⟨83529, by rfl⟩ : syracuseStep 890981 = 167059) (by norm_num)
theorem B891005 : Blo 591290 891005 := bbase (se 3 (by rfl) ⟨167063, by rfl⟩ : syracuseStep 891005 = 334127) (by norm_num)
theorem B1218701 : Blo 591290 1218701 := bbase (se 3 (by rfl) ⟨228506, by rfl⟩ : syracuseStep 1218701 = 457013) (by norm_num)
theorem B891029 : Blo 591290 891029 := bbase (se 6 (by rfl) ⟨20883, by rfl⟩ : syracuseStep 891029 = 41767) (by norm_num)
theorem B759965 : Blo 591290 759965 := bbase (se 3 (by rfl) ⟨142493, by rfl⟩ : syracuseStep 759965 = 284987) (by norm_num)
theorem B891053 : Blo 591290 891053 := bbase (se 3 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 891053 = 334145) (by norm_num)
theorem B891077 : Blo 591290 891077 := bbase (se 4 (by rfl) ⟨83538, by rfl⟩ : syracuseStep 891077 = 167077) (by norm_num)
theorem B891101 : Blo 591290 891101 := bbase (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) (by norm_num)
theorem B891125 : Blo 591290 891125 := bbase (se 5 (by rfl) ⟨41771, by rfl⟩ : syracuseStep 891125 = 83543) (by norm_num)
theorem B891149 : Blo 591290 891149 := bbase (se 3 (by rfl) ⟨167090, by rfl⟩ : syracuseStep 891149 = 334181) (by norm_num)
theorem B891173 : Blo 591290 891173 := bbase (se 4 (by rfl) ⟨83547, by rfl⟩ : syracuseStep 891173 = 167095) (by norm_num)
theorem B891197 : Blo 591290 891197 := bbase (se 3 (by rfl) ⟨167099, by rfl⟩ : syracuseStep 891197 = 334199) (by norm_num)
theorem B891221 : Blo 591290 891221 := bbase (se 10 (by rfl) ⟨1305, by rfl⟩ : syracuseStep 891221 = 2611) (by norm_num)
theorem B891245 : Blo 591290 891245 := bbase (se 3 (by rfl) ⟨167108, by rfl⟩ : syracuseStep 891245 = 334217) (by norm_num)
theorem B891269 : Blo 591290 891269 := bbase (se 4 (by rfl) ⟨83556, by rfl⟩ : syracuseStep 891269 = 167113) (by norm_num)
theorem B1350029 : Blo 591290 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B2005397 : Blo 591290 2005397 := bbase (se 6 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 2005397 = 94003) (by norm_num)
theorem B891293 : Blo 591290 891293 := bbase (se 3 (by rfl) ⟨167117, by rfl⟩ : syracuseStep 891293 = 334235) (by norm_num)
theorem B891317 : Blo 591290 891317 := bbase (se 5 (by rfl) ⟨41780, by rfl⟩ : syracuseStep 891317 = 83561) (by norm_num)
theorem B891341 : Blo 591290 891341 := bbase (se 3 (by rfl) ⟨167126, by rfl⟩ : syracuseStep 891341 = 334253) (by norm_num)
theorem B891365 : Blo 591290 891365 := bbase (se 4 (by rfl) ⟨83565, by rfl⟩ : syracuseStep 891365 = 167131) (by norm_num)
theorem B891389 : Blo 591290 891389 := bbase (se 3 (by rfl) ⟨167135, by rfl⟩ : syracuseStep 891389 = 334271) (by norm_num)
theorem B891413 : Blo 591290 891413 := bbase (se 6 (by rfl) ⟨20892, by rfl⟩ : syracuseStep 891413 = 41785) (by norm_num)
theorem B891437 : Blo 591290 891437 := bbase (se 3 (by rfl) ⟨167144, by rfl⟩ : syracuseStep 891437 = 334289) (by norm_num)
theorem B891461 : Blo 591290 891461 := bbase (se 4 (by rfl) ⟨83574, by rfl⟩ : syracuseStep 891461 = 167149) (by norm_num)
theorem B891485 : Blo 591290 891485 := bbase (se 3 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 891485 = 334307) (by norm_num)
theorem B891509 : Blo 591290 891509 := bbase (se 5 (by rfl) ⟨41789, by rfl⟩ : syracuseStep 891509 = 83579) (by norm_num)
theorem B891533 : Blo 591290 891533 := bbase (se 3 (by rfl) ⟨167162, by rfl⟩ : syracuseStep 891533 = 334325) (by norm_num)
theorem B3054229 : Blo 591290 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B891557 : Blo 591290 891557 := bbase (se 4 (by rfl) ⟨83583, by rfl⟩ : syracuseStep 891557 = 167167) (by norm_num)
theorem B891581 : Blo 591290 891581 := bbase (se 3 (by rfl) ⟨167171, by rfl⟩ : syracuseStep 891581 = 334343) (by norm_num)
theorem B891605 : Blo 591290 891605 := bbase (se 7 (by rfl) ⟨10448, by rfl⟩ : syracuseStep 891605 = 20897) (by norm_num)
theorem B891629 : Blo 591290 891629 := bbase (se 3 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 891629 = 334361) (by norm_num)
theorem B891653 : Blo 591290 891653 := bbase (se 4 (by rfl) ⟨83592, by rfl⟩ : syracuseStep 891653 = 167185) (by norm_num)
theorem B891677 : Blo 591290 891677 := bbase (se 3 (by rfl) ⟨167189, by rfl⟩ : syracuseStep 891677 = 334379) (by norm_num)
theorem B891701 : Blo 591290 891701 := bbase (se 5 (by rfl) ⟨41798, by rfl⟩ : syracuseStep 891701 = 83597) (by norm_num)
theorem B2005829 : Blo 591290 2005829 := bbase (se 4 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 2005829 = 376093) (by norm_num)
theorem B891725 : Blo 591290 891725 := bbase (se 3 (by rfl) ⟨167198, by rfl⟩ : syracuseStep 891725 = 334397) (by norm_num)
theorem B891749 : Blo 591290 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B891773 : Blo 591290 891773 := bbase (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) (by norm_num)
theorem B891797 : Blo 591290 891797 := bbase (se 6 (by rfl) ⟨20901, by rfl⟩ : syracuseStep 891797 = 41803) (by norm_num)
theorem B891821 : Blo 591290 891821 := bbase (se 3 (by rfl) ⟨167216, by rfl⟩ : syracuseStep 891821 = 334433) (by norm_num)
theorem B891845 : Blo 591290 891845 := bbase (se 4 (by rfl) ⟨83610, by rfl⟩ : syracuseStep 891845 = 167221) (by norm_num)
theorem B891869 : Blo 591290 891869 := bbase (se 3 (by rfl) ⟨167225, by rfl⟩ : syracuseStep 891869 = 334451) (by norm_num)
theorem B891893 : Blo 591290 891893 := bbase (se 5 (by rfl) ⟨41807, by rfl⟩ : syracuseStep 891893 = 83615) (by norm_num)
theorem B891917 : Blo 591290 891917 := bbase (se 3 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 891917 = 334469) (by norm_num)
theorem B891941 : Blo 591290 891941 := bbase (se 4 (by rfl) ⟨83619, by rfl⟩ : syracuseStep 891941 = 167239) (by norm_num)
theorem B891965 : Blo 591290 891965 := bbase (se 3 (by rfl) ⟨167243, by rfl⟩ : syracuseStep 891965 = 334487) (by norm_num)
theorem B891989 : Blo 591290 891989 := bbase (se 8 (by rfl) ⟨5226, by rfl⟩ : syracuseStep 891989 = 10453) (by norm_num)
theorem B892013 : Blo 591290 892013 := bbase (se 3 (by rfl) ⟨167252, by rfl⟩ : syracuseStep 892013 = 334505) (by norm_num)
theorem B892037 : Blo 591290 892037 := bbase (se 4 (by rfl) ⟨83628, by rfl⟩ : syracuseStep 892037 = 167257) (by norm_num)
theorem B892061 : Blo 591290 892061 := bbase (se 3 (by rfl) ⟨167261, by rfl⟩ : syracuseStep 892061 = 334523) (by norm_num)
theorem B892085 : Blo 591290 892085 := bbase (se 5 (by rfl) ⟨41816, by rfl⟩ : syracuseStep 892085 = 83633) (by norm_num)
theorem B892109 : Blo 591290 892109 := bbase (se 3 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 892109 = 334541) (by norm_num)
theorem B892133 : Blo 591290 892133 := bbase (se 4 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 892133 = 167275) (by norm_num)
theorem B2006261 : Blo 591290 2006261 := bbase (se 5 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 2006261 = 188087) (by norm_num)
theorem B892157 : Blo 591290 892157 := bbase (se 3 (by rfl) ⟨167279, by rfl⟩ : syracuseStep 892157 = 334559) (by norm_num)
theorem B2530565 : Blo 591290 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B1219853 : Blo 591290 1219853 := bbase (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) (by norm_num)
theorem B892181 : Blo 591290 892181 := bbase (se 6 (by rfl) ⟨20910, by rfl⟩ : syracuseStep 892181 = 41821) (by norm_num)
theorem B892205 : Blo 591290 892205 := bbase (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) (by norm_num)
theorem B892229 : Blo 591290 892229 := bbase (se 4 (by rfl) ⟨83646, by rfl⟩ : syracuseStep 892229 = 167293) (by norm_num)
theorem B892253 : Blo 591290 892253 := bbase (se 3 (by rfl) ⟨167297, by rfl⟩ : syracuseStep 892253 = 334595) (by norm_num)
theorem B2858341 : Blo 591290 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B892277 : Blo 591290 892277 := bbase (se 5 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 892277 = 83651) (by norm_num)
theorem B892301 : Blo 591290 892301 := bbase (se 3 (by rfl) ⟨167306, by rfl⟩ : syracuseStep 892301 = 334613) (by norm_num)
theorem B892325 : Blo 591290 892325 := bbase (se 4 (by rfl) ⟨83655, by rfl⟩ : syracuseStep 892325 = 167311) (by norm_num)
theorem B892349 : Blo 591290 892349 := bbase (se 3 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 892349 = 334631) (by norm_num)
theorem B892373 : Blo 591290 892373 := bbase (se 7 (by rfl) ⟨10457, by rfl⟩ : syracuseStep 892373 = 20915) (by norm_num)
theorem B892397 : Blo 591290 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B2137589 : Blo 591290 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B892421 : Blo 591290 892421 := bbase (se 4 (by rfl) ⟨83664, by rfl⟩ : syracuseStep 892421 = 167329) (by norm_num)
theorem B892445 : Blo 591290 892445 := bbase (se 3 (by rfl) ⟨167333, by rfl⟩ : syracuseStep 892445 = 334667) (by norm_num)
theorem B892469 : Blo 591290 892469 := bbase (se 5 (by rfl) ⟨41834, by rfl⟩ : syracuseStep 892469 = 83669) (by norm_num)
theorem B892493 : Blo 591290 892493 := bbase (se 3 (by rfl) ⟨167342, by rfl⟩ : syracuseStep 892493 = 334685) (by norm_num)
theorem B892517 : Blo 591290 892517 := bbase (se 4 (by rfl) ⟨83673, by rfl⟩ : syracuseStep 892517 = 167347) (by norm_num)
theorem B892541 : Blo 591290 892541 := bbase (se 3 (by rfl) ⟨167351, by rfl⟩ : syracuseStep 892541 = 334703) (by norm_num)
theorem B892565 : Blo 591290 892565 := bbase (se 6 (by rfl) ⟨20919, by rfl⟩ : syracuseStep 892565 = 41839) (by norm_num)
theorem B2006693 : Blo 591290 2006693 := bbase (se 4 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 2006693 = 376255) (by norm_num)
theorem B892589 : Blo 591290 892589 := bbase (se 3 (by rfl) ⟨167360, by rfl⟩ : syracuseStep 892589 = 334721) (by norm_num)
theorem B892613 : Blo 591290 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B892637 : Blo 591290 892637 := bbase (se 3 (by rfl) ⟨167369, by rfl⟩ : syracuseStep 892637 = 334739) (by norm_num)
theorem B892661 : Blo 591290 892661 := bbase (se 5 (by rfl) ⟨41843, by rfl⟩ : syracuseStep 892661 = 83687) (by norm_num)
theorem B2137861 : Blo 591290 2137861 := bbase (se 4 (by rfl) ⟨200424, by rfl⟩ : syracuseStep 2137861 = 400849) (by norm_num)
theorem B892685 : Blo 591290 892685 := bbase (se 3 (by rfl) ⟨167378, by rfl⟩ : syracuseStep 892685 = 334757) (by norm_num)
theorem B3612437 : Blo 591290 3612437 := bbase (se 6 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 3612437 = 169333) (by norm_num)
theorem B892709 : Blo 591290 892709 := bbase (se 4 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 892709 = 167383) (by norm_num)
theorem B892733 : Blo 591290 892733 := bbase (se 3 (by rfl) ⟨167387, by rfl⟩ : syracuseStep 892733 = 334775) (by norm_num)
theorem B892757 : Blo 591290 892757 := bbase (se 9 (by rfl) ⟨2615, by rfl⟩ : syracuseStep 892757 = 5231) (by norm_num)
theorem B892781 : Blo 591290 892781 := bbase (se 3 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 892781 = 334793) (by norm_num)
theorem B892805 : Blo 591290 892805 := bbase (se 4 (by rfl) ⟨83700, by rfl⟩ : syracuseStep 892805 = 167401) (by norm_num)
theorem B892829 : Blo 591290 892829 := bbase (se 3 (by rfl) ⟨167405, by rfl⟩ : syracuseStep 892829 = 334811) (by norm_num)
theorem B2138021 : Blo 591290 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B892853 : Blo 591290 892853 := bbase (se 5 (by rfl) ⟨41852, by rfl⟩ : syracuseStep 892853 = 83705) (by norm_num)
theorem B892877 : Blo 591290 892877 := bbase (se 3 (by rfl) ⟨167414, by rfl⟩ : syracuseStep 892877 = 334829) (by norm_num)
theorem B892901 : Blo 591290 892901 := bbase (se 4 (by rfl) ⟨83709, by rfl⟩ : syracuseStep 892901 = 167419) (by norm_num)
theorem B2400245 : Blo 591290 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B892925 : Blo 591290 892925 := bbase (se 3 (by rfl) ⟨167423, by rfl⟩ : syracuseStep 892925 = 334847) (by norm_num)
theorem B2007125 : Blo 591290 2007125 := bbase (se 8 (by rfl) ⟨11760, by rfl⟩ : syracuseStep 2007125 = 23521) (by norm_num)
theorem B1351781 : Blo 591290 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B1122653 : Blo 591290 1122653 := bbase (se 3 (by rfl) ⟨210497, by rfl⟩ : syracuseStep 1122653 = 420995) (by norm_num)
theorem B1122797 : Blo 591290 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B2007557 : Blo 591290 2007557 := bbase (se 4 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 2007557 = 376417) (by norm_num)
theorem B1123085 : Blo 591290 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B5481269 : Blo 591290 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B1123237 : Blo 591290 1123237 := bbase (se 4 (by rfl) ⟨105303, by rfl⟩ : syracuseStep 1123237 = 210607) (by norm_num)
theorem B2007989 : Blo 591290 2007989 := bbase (se 5 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 2007989 = 188249) (by norm_num)
theorem B632009 : Blo 591290 632009 := bbase (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) (by norm_num)
theorem B1123541 : Blo 591290 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B5055797 : Blo 591290 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B2008421 : Blo 591290 2008421 := bbase (se 4 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 2008421 = 376579) (by norm_num)
theorem B599405 : Blo 591290 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B4498901 : Blo 591290 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B665221 : Blo 591290 665221 := bbase (se 4 (by rfl) ⟨62364, by rfl⟩ : syracuseStep 665221 = 124729) (by norm_num)
theorem B632453 : Blo 591290 632453 := bbase (se 4 (by rfl) ⟨59292, by rfl⟩ : syracuseStep 632453 = 118585) (by norm_num)
theorem B1353349 : Blo 591290 1353349 := bbase (se 4 (by rfl) ⟨126876, by rfl⟩ : syracuseStep 1353349 = 253753) (by norm_num)
theorem B665257 : Blo 591290 665257 := bbase (se 2 (by rfl) ⟨249471, by rfl⟩ : syracuseStep 665257 = 498943) (by norm_num)
theorem B665293 : Blo 591290 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B665329 : Blo 591290 665329 := bbase (se 2 (by rfl) ⟨249498, by rfl⟩ : syracuseStep 665329 = 498997) (by norm_num)
theorem B665365 : Blo 591290 665365 := bbase (se 6 (by rfl) ⟨15594, by rfl⟩ : syracuseStep 665365 = 31189) (by norm_num)
theorem B2008853 : Blo 591290 2008853 := bbase (se 6 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 2008853 = 94165) (by norm_num)
theorem B665401 : Blo 591290 665401 := bbase (se 2 (by rfl) ⟨249525, by rfl⟩ : syracuseStep 665401 = 499051) (by norm_num)
theorem B665437 : Blo 591290 665437 := bbase (se 3 (by rfl) ⟨124769, by rfl⟩ : syracuseStep 665437 = 249539) (by norm_num)
theorem B1288045 : Blo 591290 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B632701 : Blo 591290 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B665473 : Blo 591290 665473 := bbase (se 2 (by rfl) ⟨249552, by rfl⟩ : syracuseStep 665473 = 499105) (by norm_num)
theorem B665509 : Blo 591290 665509 := bbase (se 4 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 665509 = 124783) (by norm_num)
theorem B1124293 : Blo 591290 1124293 := bbase (se 4 (by rfl) ⟨105402, by rfl⟩ : syracuseStep 1124293 = 210805) (by norm_num)
theorem B665545 : Blo 591290 665545 := bbase (se 2 (by rfl) ⟨249579, by rfl⟩ : syracuseStep 665545 = 499159) (by norm_num)
theorem B665581 : Blo 591290 665581 := bbase (se 3 (by rfl) ⟨124796, by rfl⟩ : syracuseStep 665581 = 249593) (by norm_num)
theorem B600053 : Blo 591290 600053 := bbase (se 5 (by rfl) ⟨28127, by rfl⟩ : syracuseStep 600053 = 56255) (by norm_num)
theorem B665617 : Blo 591290 665617 := bbase (se 2 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 665617 = 499213) (by norm_num)
theorem B665653 : Blo 591290 665653 := bbase (se 5 (by rfl) ⟨31202, by rfl⟩ : syracuseStep 665653 = 62405) (by norm_num)
theorem B1124437 : Blo 591290 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B665689 : Blo 591290 665689 := bbase (se 2 (by rfl) ⟨249633, by rfl⟩ : syracuseStep 665689 = 499267) (by norm_num)
theorem B665725 : Blo 591290 665725 := bbase (se 3 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 665725 = 249647) (by norm_num)
theorem B665761 : Blo 591290 665761 := bbase (se 2 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 665761 = 499321) (by norm_num)
theorem B665797 : Blo 591290 665797 := bbase (se 4 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 665797 = 124837) (by norm_num)
theorem B665833 : Blo 591290 665833 := bbase (se 2 (by rfl) ⟨249687, by rfl⟩ : syracuseStep 665833 = 499375) (by norm_num)
theorem B1124597 : Blo 591290 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B665869 : Blo 591290 665869 := bbase (se 3 (by rfl) ⟨124850, by rfl⟩ : syracuseStep 665869 = 249701) (by norm_num)
theorem B633133 : Blo 591290 633133 := bbase (se 3 (by rfl) ⟨118712, by rfl⟩ : syracuseStep 633133 = 237425) (by norm_num)
theorem B665905 : Blo 591290 665905 := bbase (se 2 (by rfl) ⟨249714, by rfl⟩ : syracuseStep 665905 = 499429) (by norm_num)
theorem B3909941 : Blo 591290 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B665941 : Blo 591290 665941 := bbase (se 10 (by rfl) ⟨975, by rfl⟩ : syracuseStep 665941 = 1951) (by norm_num)
theorem B633205 : Blo 591290 633205 := bbase (se 5 (by rfl) ⟨29681, by rfl⟩ : syracuseStep 633205 = 59363) (by norm_num)
theorem B665977 : Blo 591290 665977 := bbase (se 2 (by rfl) ⟨249741, by rfl⟩ : syracuseStep 665977 = 499483) (by norm_num)
theorem B1124741 : Blo 591290 1124741 := bbase (se 4 (by rfl) ⟨105444, by rfl⟩ : syracuseStep 1124741 = 210889) (by norm_num)
theorem B666013 : Blo 591290 666013 := bbase (se 3 (by rfl) ⟨124877, by rfl⟩ : syracuseStep 666013 = 249755) (by norm_num)
theorem B666049 : Blo 591290 666049 := bbase (se 2 (by rfl) ⟨249768, by rfl⟩ : syracuseStep 666049 = 499537) (by norm_num)
theorem B666085 : Blo 591290 666085 := bbase (se 4 (by rfl) ⟨62445, by rfl⟩ : syracuseStep 666085 = 124891) (by norm_num)
theorem B666121 : Blo 591290 666121 := bbase (se 2 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 666121 = 499591) (by norm_num)
theorem B2599445 : Blo 591290 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B666157 : Blo 591290 666157 := bbase (se 3 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 666157 = 249809) (by norm_num)
theorem B600625 : Blo 591290 600625 := bbase (se 2 (by rfl) ⟨225234, by rfl⟩ : syracuseStep 600625 = 450469) (by norm_num)
theorem B666193 : Blo 591290 666193 := bbase (se 2 (by rfl) ⟨249822, by rfl⟩ : syracuseStep 666193 = 499645) (by norm_num)
theorem B600661 : Blo 591290 600661 := bbase (se 8 (by rfl) ⟨3519, by rfl⟩ : syracuseStep 600661 = 7039) (by norm_num)
theorem B666229 : Blo 591290 666229 := bbase (se 5 (by rfl) ⟨31229, by rfl⟩ : syracuseStep 666229 = 62459) (by norm_num)
theorem B2140789 : Blo 591290 2140789 := bbase (se 5 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 2140789 = 200699) (by norm_num)
theorem B666265 : Blo 591290 666265 := bbase (se 2 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 666265 = 499699) (by norm_num)
theorem B1125029 : Blo 591290 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B666301 : Blo 591290 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B3386069 : Blo 591290 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B666337 : Blo 591290 666337 := bbase (se 2 (by rfl) ⟨249876, by rfl⟩ : syracuseStep 666337 = 499753) (by norm_num)
theorem B633577 : Blo 591290 633577 := bbase (se 2 (by rfl) ⟨237591, by rfl⟩ : syracuseStep 633577 = 475183) (by norm_num)
theorem B666373 : Blo 591290 666373 := bbase (se 4 (by rfl) ⟨62472, by rfl⟩ : syracuseStep 666373 = 124945) (by norm_num)
theorem B666409 : Blo 591290 666409 := bbase (se 2 (by rfl) ⟨249903, by rfl⟩ : syracuseStep 666409 = 499807) (by norm_num)
theorem B1125181 : Blo 591290 1125181 := bbase (se 3 (by rfl) ⟨210971, by rfl⟩ : syracuseStep 1125181 = 421943) (by norm_num)
theorem B666445 : Blo 591290 666445 := bbase (se 3 (by rfl) ⟨124958, by rfl⟩ : syracuseStep 666445 = 249917) (by norm_num)
theorem B666481 : Blo 591290 666481 := bbase (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) (by norm_num)
theorem B666517 : Blo 591290 666517 := bbase (se 6 (by rfl) ⟨15621, by rfl⟩ : syracuseStep 666517 = 31243) (by norm_num)
theorem B666553 : Blo 591290 666553 := bbase (se 2 (by rfl) ⟨249957, by rfl⟩ : syracuseStep 666553 = 499915) (by norm_num)
theorem B666589 : Blo 591290 666589 := bbase (se 3 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 666589 = 249971) (by norm_num)
theorem B666625 : Blo 591290 666625 := bbase (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) (by norm_num)
theorem B666661 : Blo 591290 666661 := bbase (se 4 (by rfl) ⟨62499, by rfl⟩ : syracuseStep 666661 = 124999) (by norm_num)
theorem B666697 : Blo 591290 666697 := bbase (se 2 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 666697 = 500023) (by norm_num)
theorem B633953 : Blo 591290 633953 := bbase (se 2 (by rfl) ⟨237732, by rfl⟩ : syracuseStep 633953 = 475465) (by norm_num)
theorem B666733 : Blo 591290 666733 := bbase (se 3 (by rfl) ⟨125012, by rfl⟩ : syracuseStep 666733 = 250025) (by norm_num)
theorem B1125485 : Blo 591290 1125485 := bbase (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) (by norm_num)
theorem B666769 : Blo 591290 666769 := bbase (se 2 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 666769 = 500077) (by norm_num)
theorem B634025 : Blo 591290 634025 := bbase (se 2 (by rfl) ⟨237759, by rfl⟩ : syracuseStep 634025 = 475519) (by norm_num)
theorem B666805 : Blo 591290 666805 := bbase (se 5 (by rfl) ⟨31256, by rfl⟩ : syracuseStep 666805 = 62513) (by norm_num)
theorem B2534597 : Blo 591290 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B666841 : Blo 591290 666841 := bbase (se 2 (by rfl) ⟨250065, by rfl⟩ : syracuseStep 666841 = 500131) (by norm_num)
theorem B666877 : Blo 591290 666877 := bbase (se 3 (by rfl) ⟨125039, by rfl⟩ : syracuseStep 666877 = 250079) (by norm_num)
theorem B929045 : Blo 591290 929045 := bbase (se 6 (by rfl) ⟨21774, by rfl⟩ : syracuseStep 929045 = 43549) (by norm_num)
theorem B666913 : Blo 591290 666913 := bbase (se 2 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 666913 = 500185) (by norm_num)
theorem B666949 : Blo 591290 666949 := bbase (se 4 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 666949 = 125053) (by norm_num)
theorem B634213 : Blo 591290 634213 := bbase (se 4 (by rfl) ⟨59457, by rfl⟩ : syracuseStep 634213 = 118915) (by norm_num)
theorem B666985 : Blo 591290 666985 := bbase (se 2 (by rfl) ⟨250119, by rfl⟩ : syracuseStep 666985 = 500239) (by norm_num)
theorem B667021 : Blo 591290 667021 := bbase (se 3 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 667021 = 250133) (by norm_num)
theorem B667057 : Blo 591290 667057 := bbase (se 2 (by rfl) ⟨250146, by rfl⟩ : syracuseStep 667057 = 500293) (by norm_num)
theorem B667093 : Blo 591290 667093 := bbase (se 7 (by rfl) ⟨7817, by rfl⟩ : syracuseStep 667093 = 15635) (by norm_num)
theorem B667129 : Blo 591290 667129 := bbase (se 2 (by rfl) ⟨250173, by rfl⟩ : syracuseStep 667129 = 500347) (by norm_num)
theorem B1420829 : Blo 591290 1420829 := bbase (se 3 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 1420829 = 532811) (by norm_num)
theorem B667165 : Blo 591290 667165 := bbase (se 3 (by rfl) ⟨125093, by rfl⟩ : syracuseStep 667165 = 250187) (by norm_num)
theorem B634397 : Blo 591290 634397 := bbase (se 3 (by rfl) ⟨118949, by rfl⟩ : syracuseStep 634397 = 237899) (by norm_num)
theorem B667201 : Blo 591290 667201 := bbase (se 2 (by rfl) ⟨250200, by rfl⟩ : syracuseStep 667201 = 500401) (by norm_num)
theorem B667237 : Blo 591290 667237 := bbase (se 4 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 667237 = 125107) (by norm_num)
theorem B667273 : Blo 591290 667273 := bbase (se 2 (by rfl) ⟨250227, by rfl⟩ : syracuseStep 667273 = 500455) (by norm_num)
theorem B667309 : Blo 591290 667309 := bbase (se 3 (by rfl) ⟨125120, by rfl⟩ : syracuseStep 667309 = 250241) (by norm_num)
theorem B667345 : Blo 591290 667345 := bbase (se 2 (by rfl) ⟨250254, by rfl⟩ : syracuseStep 667345 = 500509) (by norm_num)
theorem B634601 : Blo 591290 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B667381 : Blo 591290 667381 := bbase (se 5 (by rfl) ⟨31283, by rfl⟩ : syracuseStep 667381 = 62567) (by norm_num)
theorem B667417 : Blo 591290 667417 := bbase (se 2 (by rfl) ⟨250281, by rfl⟩ : syracuseStep 667417 = 500563) (by norm_num)
theorem B667453 : Blo 591290 667453 := bbase (se 3 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 667453 = 250295) (by norm_num)
theorem B1126237 : Blo 591290 1126237 := bbase (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) (by norm_num)
theorem B667489 : Blo 591290 667489 := bbase (se 2 (by rfl) ⟨250308, by rfl⟩ : syracuseStep 667489 = 500617) (by norm_num)
theorem B667525 : Blo 591290 667525 := bbase (se 4 (by rfl) ⟨62580, by rfl⟩ : syracuseStep 667525 = 125161) (by norm_num)
theorem B667561 : Blo 591290 667561 := bbase (se 2 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 667561 = 500671) (by norm_num)
theorem B667597 : Blo 591290 667597 := bbase (se 3 (by rfl) ⟨125174, by rfl⟩ : syracuseStep 667597 = 250349) (by norm_num)
theorem B1126381 : Blo 591290 1126381 := bbase (se 3 (by rfl) ⟨211196, by rfl⟩ : syracuseStep 1126381 = 422393) (by norm_num)
theorem B667633 : Blo 591290 667633 := bbase (se 2 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 667633 = 500725) (by norm_num)
theorem B667669 : Blo 591290 667669 := bbase (se 6 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 667669 = 31297) (by norm_num)
theorem B602137 : Blo 591290 602137 := bbase (se 2 (by rfl) ⟨225801, by rfl⟩ : syracuseStep 602137 = 451603) (by norm_num)
theorem B667705 : Blo 591290 667705 := bbase (se 2 (by rfl) ⟨250389, by rfl⟩ : syracuseStep 667705 = 500779) (by norm_num)
theorem B2994245 : Blo 591290 2994245 := bbase (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) (by norm_num)
theorem B667741 : Blo 591290 667741 := bbase (se 3 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 667741 = 250403) (by norm_num)
theorem B667777 : Blo 591290 667777 := bbase (se 2 (by rfl) ⟨250416, by rfl⟩ : syracuseStep 667777 = 500833) (by norm_num)
theorem B1126541 : Blo 591290 1126541 := bbase (se 3 (by rfl) ⟨211226, by rfl⟩ : syracuseStep 1126541 = 422453) (by norm_num)
theorem B1355933 : Blo 591290 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B667813 : Blo 591290 667813 := bbase (se 4 (by rfl) ⟨62607, by rfl⟩ : syracuseStep 667813 = 125215) (by norm_num)
theorem B667849 : Blo 591290 667849 := bbase (se 2 (by rfl) ⟨250443, by rfl⟩ : syracuseStep 667849 = 500887) (by norm_num)
theorem B5058773 : Blo 591290 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B667885 : Blo 591290 667885 := bbase (se 3 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 667885 = 250457) (by norm_num)
theorem B635149 : Blo 591290 635149 := bbase (se 3 (by rfl) ⟨119090, by rfl⟩ : syracuseStep 635149 = 238181) (by norm_num)
theorem B667921 : Blo 591290 667921 := bbase (se 2 (by rfl) ⟨250470, by rfl⟩ : syracuseStep 667921 = 500941) (by norm_num)
theorem B1126685 : Blo 591290 1126685 := bbase (se 3 (by rfl) ⟨211253, by rfl⟩ : syracuseStep 1126685 = 422507) (by norm_num)
theorem B667957 : Blo 591290 667957 := bbase (se 5 (by rfl) ⟨31310, by rfl⟩ : syracuseStep 667957 = 62621) (by norm_num)
theorem B635221 : Blo 591290 635221 := bbase (se 10 (by rfl) ⟨930, by rfl⟩ : syracuseStep 635221 = 1861) (by norm_num)
theorem B667993 : Blo 591290 667993 := bbase (se 2 (by rfl) ⟨250497, by rfl⟩ : syracuseStep 667993 = 500995) (by norm_num)
theorem B668029 : Blo 591290 668029 := bbase (se 3 (by rfl) ⟨125255, by rfl⟩ : syracuseStep 668029 = 250511) (by norm_num)
theorem B668065 : Blo 591290 668065 := bbase (se 2 (by rfl) ⟨250524, by rfl⟩ : syracuseStep 668065 = 501049) (by norm_num)
theorem B668101 : Blo 591290 668101 := bbase (se 4 (by rfl) ⟨62634, by rfl⟩ : syracuseStep 668101 = 125269) (by norm_num)
theorem B668137 : Blo 591290 668137 := bbase (se 2 (by rfl) ⟨250551, by rfl⟩ : syracuseStep 668137 = 501103) (by norm_num)
theorem B635401 : Blo 591290 635401 := bbase (se 2 (by rfl) ⟨238275, by rfl⟩ : syracuseStep 635401 = 476551) (by norm_num)
theorem B668173 : Blo 591290 668173 := bbase (se 3 (by rfl) ⟨125282, by rfl⟩ : syracuseStep 668173 = 250565) (by norm_num)
theorem B668209 : Blo 591290 668209 := bbase (se 2 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 668209 = 501157) (by norm_num)
theorem B1126973 : Blo 591290 1126973 := bbase (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) (by norm_num)
theorem B668245 : Blo 591290 668245 := bbase (se 8 (by rfl) ⟨3915, by rfl⟩ : syracuseStep 668245 = 7831) (by norm_num)
theorem B668281 : Blo 591290 668281 := bbase (se 2 (by rfl) ⟨250605, by rfl⟩ : syracuseStep 668281 = 501211) (by norm_num)
theorem B5419669 : Blo 591290 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B668317 : Blo 591290 668317 := bbase (se 3 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 668317 = 250619) (by norm_num)
theorem B668353 : Blo 591290 668353 := bbase (se 2 (by rfl) ⟨250632, by rfl⟩ : syracuseStep 668353 = 501265) (by norm_num)
theorem B1127125 : Blo 591290 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B668389 : Blo 591290 668389 := bbase (se 4 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 668389 = 125323) (by norm_num)
theorem B2142949 : Blo 591290 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B668425 : Blo 591290 668425 := bbase (se 2 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 668425 = 501319) (by norm_num)
theorem B668461 : Blo 591290 668461 := bbase (se 3 (by rfl) ⟨125336, by rfl⟩ : syracuseStep 668461 = 250673) (by norm_num)
theorem B668497 : Blo 591290 668497 := bbase (se 2 (by rfl) ⟨250686, by rfl⟩ : syracuseStep 668497 = 501373) (by norm_num)
theorem B1684309 : Blo 591290 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B668533 : Blo 591290 668533 := bbase (se 5 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 668533 = 62675) (by norm_num)
theorem B5714837 : Blo 591290 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B668569 : Blo 591290 668569 := bbase (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) (by norm_num)
theorem B2536373 : Blo 591290 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B603061 : Blo 591290 603061 := bbase (se 5 (by rfl) ⟨28268, by rfl⟩ : syracuseStep 603061 = 56537) (by norm_num)
theorem B668605 : Blo 591290 668605 := bbase (se 3 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 668605 = 250727) (by norm_num)
theorem B668641 : Blo 591290 668641 := bbase (se 2 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 668641 = 501481) (by norm_num)
theorem B1684469 : Blo 591290 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B1127429 : Blo 591290 1127429 := bbase (se 4 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 1127429 = 211393) (by norm_num)
theorem B668677 : Blo 591290 668677 := bbase (se 4 (by rfl) ⟨62688, by rfl⟩ : syracuseStep 668677 = 125377) (by norm_num)
theorem B668713 : Blo 591290 668713 := bbase (se 2 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 668713 = 501535) (by norm_num)
theorem B668749 : Blo 591290 668749 := bbase (se 3 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 668749 = 250781) (by norm_num)
theorem B668785 : Blo 591290 668785 := bbase (se 2 (by rfl) ⟨250794, by rfl⟩ : syracuseStep 668785 = 501589) (by norm_num)
theorem B668821 : Blo 591290 668821 := bbase (se 6 (by rfl) ⟨15675, by rfl⟩ : syracuseStep 668821 = 31351) (by norm_num)
theorem B2143397 : Blo 591290 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B668857 : Blo 591290 668857 := bbase (se 2 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 668857 = 501643) (by norm_num)
theorem B668893 : Blo 591290 668893 := bbase (se 3 (by rfl) ⟨125417, by rfl⟩ : syracuseStep 668893 = 250835) (by norm_num)
theorem B1684709 : Blo 591290 1684709 := bbase (se 4 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 1684709 = 315883) (by norm_num)
theorem B668929 : Blo 591290 668929 := bbase (se 2 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 668929 = 501697) (by norm_num)
theorem B668965 : Blo 591290 668965 := bbase (se 4 (by rfl) ⟨62715, by rfl⟩ : syracuseStep 668965 = 125431) (by norm_num)
theorem B669001 : Blo 591290 669001 := bbase (se 2 (by rfl) ⟨250875, by rfl⟩ : syracuseStep 669001 = 501751) (by norm_num)
theorem B2995541 : Blo 591290 2995541 := bbase (se 13 (by rfl) ⟨548, by rfl⟩ : syracuseStep 2995541 = 1097) (by norm_num)
theorem B669037 : Blo 591290 669037 := bbase (se 3 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 669037 = 250889) (by norm_num)
theorem B1357181 : Blo 591290 1357181 := bbase (se 3 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 1357181 = 508943) (by norm_num)
theorem B669073 : Blo 591290 669073 := bbase (se 2 (by rfl) ⟨250902, by rfl⟩ : syracuseStep 669073 = 501805) (by norm_num)
theorem B1684901 : Blo 591290 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B669109 : Blo 591290 669109 := bbase (se 5 (by rfl) ⟨31364, by rfl⟩ : syracuseStep 669109 = 62729) (by norm_num)
theorem B669145 : Blo 591290 669145 := bbase (se 2 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 669145 = 501859) (by norm_num)
theorem B669181 : Blo 591290 669181 := bbase (se 3 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 669181 = 250943) (by norm_num)
theorem B669217 : Blo 591290 669217 := bbase (se 2 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 669217 = 501913) (by norm_num)
theorem B669253 : Blo 591290 669253 := bbase (se 4 (by rfl) ⟨62742, by rfl⟩ : syracuseStep 669253 = 125485) (by norm_num)
theorem B669289 : Blo 591290 669289 := bbase (se 2 (by rfl) ⟨250983, by rfl⟩ : syracuseStep 669289 = 501967) (by norm_num)
theorem B669325 : Blo 591290 669325 := bbase (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) (by norm_num)
theorem B669361 : Blo 591290 669361 := bbase (se 2 (by rfl) ⟨251010, by rfl⟩ : syracuseStep 669361 = 502021) (by norm_num)
theorem B4273877 : Blo 591290 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B669397 : Blo 591290 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B1128181 : Blo 591290 1128181 := bbase (se 5 (by rfl) ⟨52883, by rfl⟩ : syracuseStep 1128181 = 105767) (by norm_num)
theorem B669433 : Blo 591290 669433 := bbase (se 2 (by rfl) ⟨251037, by rfl⟩ : syracuseStep 669433 = 502075) (by norm_num)
theorem B2406149 : Blo 591290 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B669469 : Blo 591290 669469 := bbase (se 3 (by rfl) ⟨125525, by rfl⟩ : syracuseStep 669469 = 251051) (by norm_num)
theorem B669505 : Blo 591290 669505 := bbase (se 2 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 669505 = 502129) (by norm_num)
theorem B669541 : Blo 591290 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B1128325 : Blo 591290 1128325 := bbase (se 4 (by rfl) ⟨105780, by rfl⟩ : syracuseStep 1128325 = 211561) (by norm_num)
theorem B669577 : Blo 591290 669577 := bbase (se 2 (by rfl) ⟨251091, by rfl⟩ : syracuseStep 669577 = 502183) (by norm_num)
theorem B2537365 : Blo 591290 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B669613 : Blo 591290 669613 := bbase (se 3 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 669613 = 251105) (by norm_num)
theorem B669649 : Blo 591290 669649 := bbase (se 2 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 669649 = 502237) (by norm_num)
theorem B1718261 : Blo 591290 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B669685 : Blo 591290 669685 := bbase (se 5 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 669685 = 62783) (by norm_num)
theorem B1128485 : Blo 591290 1128485 := bbase (se 4 (by rfl) ⟨105795, by rfl⟩ : syracuseStep 1128485 = 211591) (by norm_num)
theorem B4110421 : Blo 591290 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B9615509 : Blo 591290 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B1128629 : Blo 591290 1128629 := bbase (se 5 (by rfl) ⟨52904, by rfl⟩ : syracuseStep 1128629 = 105809) (by norm_num)
theorem B1423597 : Blo 591290 1423597 := bbase (se 3 (by rfl) ⟨266924, by rfl⟩ : syracuseStep 1423597 = 533849) (by norm_num)
theorem B899381 : Blo 591290 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B1685893 : Blo 591290 1685893 := bbase (se 4 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 1685893 = 316105) (by norm_num)
theorem B997805 : Blo 591290 997805 := bbase (se 3 (by rfl) ⟨187088, by rfl⟩ : syracuseStep 997805 = 374177) (by norm_num)
theorem B1128917 : Blo 591290 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B6404629 : Blo 591290 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B997933 : Blo 591290 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B2996837 : Blo 591290 2996837 := bbase (se 4 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 2996837 = 561907) (by norm_num)
theorem B1129069 : Blo 591290 1129069 := bbase (se 3 (by rfl) ⟨211700, by rfl⟩ : syracuseStep 1129069 = 423401) (by norm_num)
theorem B998021 : Blo 591290 998021 := bbase (se 4 (by rfl) ⟨93564, by rfl⟩ : syracuseStep 998021 = 187129) (by norm_num)
theorem B1424117 : Blo 591290 1424117 := bbase (se 5 (by rfl) ⟨66755, by rfl⟩ : syracuseStep 1424117 = 133511) (by norm_num)
theorem B998149 : Blo 591290 998149 := bbase (se 4 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 998149 = 187153) (by norm_num)
theorem B1424213 : Blo 591290 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B998237 : Blo 591290 998237 := bbase (se 3 (by rfl) ⟨187169, by rfl⟩ : syracuseStep 998237 = 374339) (by norm_num)
theorem B1129373 : Blo 591290 1129373 := bbase (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) (by norm_num)
theorem B998365 : Blo 591290 998365 := bbase (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) (by norm_num)
theorem B998453 : Blo 591290 998453 := bbase (se 5 (by rfl) ⟨46802, by rfl⟩ : syracuseStep 998453 = 93605) (by norm_num)
theorem B998581 : Blo 591290 998581 := bbase (se 5 (by rfl) ⟨46808, by rfl⟩ : syracuseStep 998581 = 93617) (by norm_num)
theorem B998669 : Blo 591290 998669 := bbase (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) (by norm_num)
theorem B998797 : Blo 591290 998797 := bbase (se 3 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 998797 = 374549) (by norm_num)
theorem B1686997 : Blo 591290 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B998885 : Blo 591290 998885 := bbase (se 4 (by rfl) ⟨93645, by rfl⟩ : syracuseStep 998885 = 187291) (by norm_num)
theorem B900629 : Blo 591290 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B999013 : Blo 591290 999013 := bbase (se 4 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 999013 = 187315) (by norm_num)
theorem B802477 : Blo 591290 802477 := bbase (se 3 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 802477 = 300929) (by norm_num)
theorem B999101 : Blo 591290 999101 := bbase (se 3 (by rfl) ⟨187331, by rfl⟩ : syracuseStep 999101 = 374663) (by norm_num)
theorem B999229 : Blo 591290 999229 := bbase (se 3 (by rfl) ⟨187355, by rfl⟩ : syracuseStep 999229 = 374711) (by norm_num)
theorem B2998133 : Blo 591290 2998133 := bbase (se 5 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 2998133 = 281075) (by norm_num)
theorem B999317 : Blo 591290 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B2703253 : Blo 591290 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B769981 : Blo 591290 769981 := bbase (se 3 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 769981 = 288743) (by norm_num)
theorem B5128181 : Blo 591290 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B999445 : Blo 591290 999445 := bbase (se 6 (by rfl) ⟨23424, by rfl⟩ : syracuseStep 999445 = 46849) (by norm_num)
theorem B999533 : Blo 591290 999533 := bbase (se 3 (by rfl) ⟨187412, by rfl⟩ : syracuseStep 999533 = 374825) (by norm_num)
theorem B1425557 : Blo 591290 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B999661 : Blo 591290 999661 := bbase (se 3 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 999661 = 374873) (by norm_num)
theorem B999749 : Blo 591290 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B10797461 : Blo 591290 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B999877 : Blo 591290 999877 := bbase (se 4 (by rfl) ⟨93738, by rfl⟩ : syracuseStep 999877 = 187477) (by norm_num)
theorem B999965 : Blo 591290 999965 := bbase (se 3 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 999965 = 374987) (by norm_num)
theorem B1065565 : Blo 591290 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B1000093 : Blo 591290 1000093 := bbase (se 3 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 1000093 = 375035) (by norm_num)
theorem B1000181 : Blo 591290 1000181 := bbase (se 5 (by rfl) ⟨46883, by rfl⟩ : syracuseStep 1000181 = 93767) (by norm_num)
theorem B1000309 : Blo 591290 1000309 := bbase (se 5 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 1000309 = 93779) (by norm_num)
theorem B1688501 : Blo 591290 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B1000397 : Blo 591290 1000397 := bbase (se 3 (by rfl) ⟨187574, by rfl⟩ : syracuseStep 1000397 = 375149) (by norm_num)
theorem B4506677 : Blo 591290 4506677 := bbase (se 5 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 4506677 = 422501) (by norm_num)
theorem B1000525 : Blo 591290 1000525 := bbase (se 3 (by rfl) ⟨187598, by rfl⟩ : syracuseStep 1000525 = 375197) (by norm_num)
theorem B1066069 : Blo 591290 1066069 := bbase (se 8 (by rfl) ⟨6246, by rfl⟩ : syracuseStep 1066069 = 12493) (by norm_num)
theorem B2999429 : Blo 591290 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B1000613 : Blo 591290 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B2573477 : Blo 591290 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B804125 : Blo 591290 804125 := bbase (se 3 (by rfl) ⟨150773, by rfl⟩ : syracuseStep 804125 = 301547) (by norm_num)
theorem B1000741 : Blo 591290 1000741 := bbase (se 4 (by rfl) ⟨93819, by rfl⟩ : syracuseStep 1000741 = 187639) (by norm_num)
theorem B607541 : Blo 591290 607541 := bbase (se 5 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 607541 = 56957) (by norm_num)
theorem B1000829 : Blo 591290 1000829 := bbase (se 3 (by rfl) ⟨187655, by rfl⟩ : syracuseStep 1000829 = 375311) (by norm_num)
theorem B902549 : Blo 591290 902549 := bbase (se 6 (by rfl) ⟨21153, by rfl⟩ : syracuseStep 902549 = 42307) (by norm_num)
theorem B607657 : Blo 591290 607657 := bbase (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) (by norm_num)
theorem B1263053 : Blo 591290 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B1263061 : Blo 591290 1263061 := bbase (se 7 (by rfl) ⟨14801, by rfl⟩ : syracuseStep 1263061 = 29603) (by norm_num)
theorem B1000957 : Blo 591290 1000957 := bbase (se 3 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 1000957 = 375359) (by norm_num)
theorem B1001045 : Blo 591290 1001045 := bbase (se 8 (by rfl) ⟨5865, by rfl⟩ : syracuseStep 1001045 = 11731) (by norm_num)
theorem B1001173 : Blo 591290 1001173 := bbase (se 7 (by rfl) ⟨11732, by rfl⟩ : syracuseStep 1001173 = 23465) (by norm_num)
theorem B1001261 : Blo 591290 1001261 := bbase (se 3 (by rfl) ⟨187736, by rfl⟩ : syracuseStep 1001261 = 375473) (by norm_num)
theorem B1001389 : Blo 591290 1001389 := bbase (se 3 (by rfl) ⟨187760, by rfl⟩ : syracuseStep 1001389 = 375521) (by norm_num)
theorem B1066949 : Blo 591290 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B1001477 : Blo 591290 1001477 := bbase (se 4 (by rfl) ⟨93888, by rfl⟩ : syracuseStep 1001477 = 187777) (by norm_num)
theorem B1427557 : Blo 591290 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1001605 : Blo 591290 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B1001693 : Blo 591290 1001693 := bbase (se 3 (by rfl) ⟨187817, by rfl⟩ : syracuseStep 1001693 = 375635) (by norm_num)
theorem B2246885 : Blo 591290 2246885 := bbase (se 4 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 2246885 = 421291) (by norm_num)
theorem B1427701 : Blo 591290 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B1001821 : Blo 591290 1001821 := bbase (se 3 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 1001821 = 375683) (by norm_num)
theorem B3000725 : Blo 591290 3000725 := bbase (se 6 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 3000725 = 140659) (by norm_num)
theorem B1001909 : Blo 591290 1001909 := bbase (se 5 (by rfl) ⟨46964, by rfl⟩ : syracuseStep 1001909 = 93929) (by norm_num)
theorem B1690085 : Blo 591290 1690085 := bbase (se 4 (by rfl) ⟨158445, by rfl⟩ : syracuseStep 1690085 = 316891) (by norm_num)
theorem B2247173 : Blo 591290 2247173 := bbase (se 4 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 2247173 = 421345) (by norm_num)
theorem B1002037 : Blo 591290 1002037 := bbase (se 5 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 1002037 = 93941) (by norm_num)
theorem B1264189 : Blo 591290 1264189 := bbase (se 3 (by rfl) ⟨237035, by rfl⟩ : syracuseStep 1264189 = 474071) (by norm_num)
theorem B1002125 : Blo 591290 1002125 := bbase (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) (by norm_num)
theorem B1002253 : Blo 591290 1002253 := bbase (se 3 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 1002253 = 375845) (by norm_num)
theorem B2542373 : Blo 591290 2542373 := bbase (se 4 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 2542373 = 476695) (by norm_num)
theorem B6769493 : Blo 591290 6769493 := bbase (se 9 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 6769493 = 39665) (by norm_num)
theorem B1428317 : Blo 591290 1428317 := bbase (se 3 (by rfl) ⟨267809, by rfl⟩ : syracuseStep 1428317 = 535619) (by norm_num)
theorem B1002341 : Blo 591290 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B1264565 : Blo 591290 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B1067957 : Blo 591290 1067957 := bbase (se 5 (by rfl) ⟨50060, by rfl⟩ : syracuseStep 1067957 = 100121) (by norm_num)
theorem B1002469 : Blo 591290 1002469 := bbase (se 4 (by rfl) ⟨93981, by rfl⟩ : syracuseStep 1002469 = 187963) (by norm_num)
theorem B642053 : Blo 591290 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B1002557 : Blo 591290 1002557 := bbase (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) (by norm_num)
theorem B2542661 : Blo 591290 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B1690757 : Blo 591290 1690757 := bbase (se 4 (by rfl) ⟨158508, by rfl⟩ : syracuseStep 1690757 = 317017) (by norm_num)
theorem B1526933 : Blo 591290 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B1428653 : Blo 591290 1428653 := bbase (se 3 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 1428653 = 535745) (by norm_num)
theorem B1002685 : Blo 591290 1002685 := bbase (se 3 (by rfl) ⟨188003, by rfl⟩ : syracuseStep 1002685 = 376007) (by norm_num)
theorem B1428749 : Blo 591290 1428749 := bbase (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) (by norm_num)
theorem B1002773 : Blo 591290 1002773 := bbase (se 6 (by rfl) ⟨23502, by rfl⟩ : syracuseStep 1002773 = 47005) (by norm_num)
theorem B1330469 : Blo 591290 1330469 := bbase (se 4 (by rfl) ⟨124731, by rfl⟩ : syracuseStep 1330469 = 249463) (by norm_num)
theorem B1330541 : Blo 591290 1330541 := bbase (se 3 (by rfl) ⟨249476, by rfl⟩ : syracuseStep 1330541 = 498953) (by norm_num)
theorem B1002901 : Blo 591290 1002901 := bbase (se 6 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 1002901 = 47011) (by norm_num)
theorem B1330613 : Blo 591290 1330613 := bbase (se 5 (by rfl) ⟨62372, by rfl⟩ : syracuseStep 1330613 = 124745) (by norm_num)
theorem B1428941 : Blo 591290 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B1002989 : Blo 591290 1002989 := bbase (se 3 (by rfl) ⟨188060, by rfl⟩ : syracuseStep 1002989 = 376121) (by norm_num)
theorem B1330685 : Blo 591290 1330685 := bbase (se 3 (by rfl) ⟨249503, by rfl⟩ : syracuseStep 1330685 = 499007) (by norm_num)
theorem B1691189 : Blo 591290 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1330757 : Blo 591290 1330757 := bbase (se 4 (by rfl) ⟨124758, by rfl⟩ : syracuseStep 1330757 = 249517) (by norm_num)
theorem B1199701 : Blo 591290 1199701 := bbase (se 8 (by rfl) ⟨7029, by rfl⟩ : syracuseStep 1199701 = 14059) (by norm_num)
theorem B1003117 : Blo 591290 1003117 := bbase (se 3 (by rfl) ⟨188084, by rfl⟩ : syracuseStep 1003117 = 376169) (by norm_num)
theorem B1330829 : Blo 591290 1330829 := bbase (se 3 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 1330829 = 499061) (by norm_num)
theorem B2248357 : Blo 591290 2248357 := bbase (se 4 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 2248357 = 421567) (by norm_num)
theorem B3002021 : Blo 591290 3002021 := bbase (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) (by norm_num)
theorem B1003205 : Blo 591290 1003205 := bbase (se 4 (by rfl) ⟨94050, by rfl⟩ : syracuseStep 1003205 = 188101) (by norm_num)
theorem B1330901 : Blo 591290 1330901 := bbase (se 7 (by rfl) ⟨15596, by rfl⟩ : syracuseStep 1330901 = 31193) (by norm_num)
theorem B1330973 : Blo 591290 1330973 := bbase (se 3 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 1330973 = 499115) (by norm_num)
theorem B610081 : Blo 591290 610081 := bbase (se 2 (by rfl) ⟨228780, by rfl⟩ : syracuseStep 610081 = 457561) (by norm_num)
theorem B1003333 : Blo 591290 1003333 := bbase (se 4 (by rfl) ⟨94062, by rfl⟩ : syracuseStep 1003333 = 188125) (by norm_num)
theorem B1331045 : Blo 591290 1331045 := bbase (se 4 (by rfl) ⟨124785, by rfl⟩ : syracuseStep 1331045 = 249571) (by norm_num)
theorem B1003421 : Blo 591290 1003421 := bbase (se 3 (by rfl) ⟨188141, by rfl⟩ : syracuseStep 1003421 = 376283) (by norm_num)
theorem B1331117 : Blo 591290 1331117 := bbase (se 3 (by rfl) ⟨249584, by rfl⟩ : syracuseStep 1331117 = 499169) (by norm_num)
theorem B2248661 : Blo 591290 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B1331189 : Blo 591290 1331189 := bbase (se 5 (by rfl) ⟨62399, by rfl⟩ : syracuseStep 1331189 = 124799) (by norm_num)
theorem B8572949 : Blo 591290 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B1003549 : Blo 591290 1003549 := bbase (se 3 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 1003549 = 376331) (by norm_num)
theorem B1331261 : Blo 591290 1331261 := bbase (se 3 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 1331261 = 499223) (by norm_num)
theorem B7721045 : Blo 591290 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B1003637 : Blo 591290 1003637 := bbase (se 5 (by rfl) ⟨47045, by rfl⟩ : syracuseStep 1003637 = 94091) (by norm_num)
theorem B1331333 : Blo 591290 1331333 := bbase (se 4 (by rfl) ⟨124812, by rfl⟩ : syracuseStep 1331333 = 249625) (by norm_num)
theorem B2281621 : Blo 591290 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B1331405 : Blo 591290 1331405 := bbase (se 3 (by rfl) ⟨249638, by rfl⟩ : syracuseStep 1331405 = 499277) (by norm_num)
theorem B1626325 : Blo 591290 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B1003765 : Blo 591290 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B1331477 : Blo 591290 1331477 := bbase (se 6 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 1331477 = 62413) (by norm_num)
theorem B1691941 : Blo 591290 1691941 := bbase (se 4 (by rfl) ⟨158619, by rfl⟩ : syracuseStep 1691941 = 317239) (by norm_num)
theorem B1003853 : Blo 591290 1003853 := bbase (se 3 (by rfl) ⟨188222, by rfl⟩ : syracuseStep 1003853 = 376445) (by norm_num)
theorem B1331549 : Blo 591290 1331549 := bbase (se 3 (by rfl) ⟨249665, by rfl⟩ : syracuseStep 1331549 = 499331) (by norm_num)
theorem B676237 : Blo 591290 676237 := bbase (se 3 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 676237 = 253589) (by norm_num)
theorem B1331621 : Blo 591290 1331621 := bbase (se 4 (by rfl) ⟨124839, by rfl⟩ : syracuseStep 1331621 = 249679) (by norm_num)
theorem B1003981 : Blo 591290 1003981 := bbase (se 3 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 1003981 = 376493) (by norm_num)
theorem B1331693 : Blo 591290 1331693 := bbase (se 3 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 1331693 = 499385) (by norm_num)
theorem B1266205 : Blo 591290 1266205 := bbase (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) (by norm_num)
theorem B1004069 : Blo 591290 1004069 := bbase (se 4 (by rfl) ⟨94131, by rfl⟩ : syracuseStep 1004069 = 188263) (by norm_num)
theorem B676397 : Blo 591290 676397 := bbase (se 3 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 676397 = 253649) (by norm_num)
theorem B1331765 : Blo 591290 1331765 := bbase (se 5 (by rfl) ⟨62426, by rfl⟩ : syracuseStep 1331765 = 124853) (by norm_num)
theorem B1069645 : Blo 591290 1069645 := bbase (se 3 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 1069645 = 401117) (by norm_num)
theorem B1430093 : Blo 591290 1430093 := bbase (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) (by norm_num)
theorem B1331837 : Blo 591290 1331837 := bbase (se 3 (by rfl) ⟨249719, by rfl⟩ : syracuseStep 1331837 = 499439) (by norm_num)
theorem B1004197 : Blo 591290 1004197 := bbase (se 4 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 1004197 = 188287) (by norm_num)
theorem B1331909 : Blo 591290 1331909 := bbase (se 4 (by rfl) ⟨124866, by rfl⟩ : syracuseStep 1331909 = 249733) (by norm_num)
theorem B1004285 : Blo 591290 1004285 := bbase (se 3 (by rfl) ⟨188303, by rfl⟩ : syracuseStep 1004285 = 376607) (by norm_num)
theorem B1200901 : Blo 591290 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B1331981 : Blo 591290 1331981 := bbase (se 3 (by rfl) ⟨249746, by rfl⟩ : syracuseStep 1331981 = 499493) (by norm_num)
theorem B1069853 : Blo 591290 1069853 := bbase (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) (by norm_num)
theorem B1069861 : Blo 591290 1069861 := bbase (se 4 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 1069861 = 200599) (by norm_num)
theorem B19452757 : Blo 591290 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B1332053 : Blo 591290 1332053 := bbase (se 9 (by rfl) ⟨3902, by rfl⟩ : syracuseStep 1332053 = 7805) (by norm_num)
theorem B1004413 : Blo 591290 1004413 := bbase (se 3 (by rfl) ⟨188327, by rfl⟩ : syracuseStep 1004413 = 376655) (by norm_num)
theorem B1332125 : Blo 591290 1332125 := bbase (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) (by norm_num)
theorem B3003317 : Blo 591290 3003317 := bbase (se 5 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 3003317 = 281561) (by norm_num)
theorem B1070005 : Blo 591290 1070005 := bbase (se 5 (by rfl) ⟨50156, by rfl⟩ : syracuseStep 1070005 = 100313) (by norm_num)
theorem B644045 : Blo 591290 644045 := bbase (se 3 (by rfl) ⟨120758, by rfl⟩ : syracuseStep 644045 = 241517) (by norm_num)
theorem B1004501 : Blo 591290 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B1332197 : Blo 591290 1332197 := bbase (se 4 (by rfl) ⟨124893, by rfl⟩ : syracuseStep 1332197 = 249787) (by norm_num)
theorem B1332269 : Blo 591290 1332269 := bbase (se 3 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 1332269 = 499601) (by norm_num)
theorem B1332341 : Blo 591290 1332341 := bbase (se 5 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 1332341 = 124907) (by norm_num)
theorem B1332413 : Blo 591290 1332413 := bbase (se 3 (by rfl) ⟨249827, by rfl⟩ : syracuseStep 1332413 = 499655) (by norm_num)
theorem B1627381 : Blo 591290 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B1332485 : Blo 591290 1332485 := bbase (se 4 (by rfl) ⟨124920, by rfl⟩ : syracuseStep 1332485 = 249841) (by norm_num)
theorem B3855637 : Blo 591290 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B1332557 : Blo 591290 1332557 := bbase (se 3 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 1332557 = 499709) (by norm_num)
theorem B1332629 : Blo 591290 1332629 := bbase (se 6 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 1332629 = 62467) (by norm_num)
theorem B1267093 : Blo 591290 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B1332701 : Blo 591290 1332701 := bbase (se 3 (by rfl) ⟨249881, by rfl⟩ : syracuseStep 1332701 = 499763) (by norm_num)
theorem B1332773 : Blo 591290 1332773 := bbase (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) (by norm_num)
theorem B1332845 : Blo 591290 1332845 := bbase (se 3 (by rfl) ⟨249908, by rfl⟩ : syracuseStep 1332845 = 499817) (by norm_num)
theorem B3200629 : Blo 591290 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B1070725 : Blo 591290 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1332917 : Blo 591290 1332917 := bbase (se 5 (by rfl) ⟨62480, by rfl⟩ : syracuseStep 1332917 = 124961) (by norm_num)
theorem B1496789 : Blo 591290 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B1070813 : Blo 591290 1070813 := bbase (se 3 (by rfl) ⟨200777, by rfl⟩ : syracuseStep 1070813 = 401555) (by norm_num)
theorem B1332989 : Blo 591290 1332989 := bbase (se 3 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 1332989 = 499871) (by norm_num)
theorem B1333061 : Blo 591290 1333061 := bbase (se 4 (by rfl) ⟨124974, by rfl⟩ : syracuseStep 1333061 = 249949) (by norm_num)
theorem B1267589 : Blo 591290 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B1333133 : Blo 591290 1333133 := bbase (se 3 (by rfl) ⟨249962, by rfl⟩ : syracuseStep 1333133 = 499925) (by norm_num)
theorem B710545 : Blo 591290 710545 := bbase (se 2 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 710545 = 532909) (by norm_num)
theorem B1496981 : Blo 591290 1496981 := bbase (se 6 (by rfl) ⟨35085, by rfl⟩ : syracuseStep 1496981 = 70171) (by norm_num)
theorem B1333205 : Blo 591290 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B2250773 : Blo 591290 2250773 := bbase (se 6 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 2250773 = 105505) (by norm_num)
theorem B1333277 : Blo 591290 1333277 := bbase (se 3 (by rfl) ⟨249989, by rfl⟩ : syracuseStep 1333277 = 499979) (by norm_num)
theorem B1333349 : Blo 591290 1333349 := bbase (se 4 (by rfl) ⟨125001, by rfl⟩ : syracuseStep 1333349 = 250003) (by norm_num)
theorem B1071245 : Blo 591290 1071245 := bbase (se 3 (by rfl) ⟨200858, by rfl⟩ : syracuseStep 1071245 = 401717) (by norm_num)
theorem B1333421 : Blo 591290 1333421 := bbase (se 3 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 1333421 = 500033) (by norm_num)
theorem B3004613 : Blo 591290 3004613 := bbase (se 4 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 3004613 = 563365) (by norm_num)
theorem B1497325 : Blo 591290 1497325 := bbase (se 3 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 1497325 = 561497) (by norm_num)
theorem B1333493 : Blo 591290 1333493 := bbase (se 5 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 1333493 = 125015) (by norm_num)
theorem B1071389 : Blo 591290 1071389 := bbase (se 3 (by rfl) ⟨200885, by rfl⟩ : syracuseStep 1071389 = 401771) (by norm_num)
theorem B2251061 : Blo 591290 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1333565 : Blo 591290 1333565 := bbase (se 3 (by rfl) ⟨250043, by rfl⟩ : syracuseStep 1333565 = 500087) (by norm_num)
theorem B1497437 : Blo 591290 1497437 := bbase (se 3 (by rfl) ⟨280769, by rfl⟩ : syracuseStep 1497437 = 561539) (by norm_num)
theorem B1333637 : Blo 591290 1333637 := bbase (se 4 (by rfl) ⟨125028, by rfl⟩ : syracuseStep 1333637 = 250057) (by norm_num)
theorem B1333709 : Blo 591290 1333709 := bbase (se 3 (by rfl) ⟨250070, by rfl⟩ : syracuseStep 1333709 = 500141) (by norm_num)
theorem B1071605 : Blo 591290 1071605 := bbase (se 5 (by rfl) ⟨50231, by rfl⟩ : syracuseStep 1071605 = 100463) (by norm_num)
theorem B1333781 : Blo 591290 1333781 := bbase (se 6 (by rfl) ⟨31260, by rfl⟩ : syracuseStep 1333781 = 62521) (by norm_num)
theorem B1497629 : Blo 591290 1497629 := bbase (se 3 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 1497629 = 561611) (by norm_num)
theorem B1333853 : Blo 591290 1333853 := bbase (se 3 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 1333853 = 500195) (by norm_num)
theorem B842405 : Blo 591290 842405 := bbase (se 4 (by rfl) ⟨78975, by rfl⟩ : syracuseStep 842405 = 157951) (by norm_num)
theorem B1333925 : Blo 591290 1333925 := bbase (se 4 (by rfl) ⟨125055, by rfl⟩ : syracuseStep 1333925 = 250111) (by norm_num)
theorem B1268453 : Blo 591290 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B1333997 : Blo 591290 1333997 := bbase (se 3 (by rfl) ⟨250124, by rfl⟩ : syracuseStep 1333997 = 500249) (by norm_num)
theorem B711433 : Blo 591290 711433 := bbase (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) (by norm_num)
theorem B1334069 : Blo 591290 1334069 := bbase (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) (by norm_num)
theorem B1497973 : Blo 591290 1497973 := bbase (se 5 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 1497973 = 140435) (by norm_num)
theorem B1268597 : Blo 591290 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B1334141 : Blo 591290 1334141 := bbase (se 3 (by rfl) ⟨250151, by rfl⟩ : syracuseStep 1334141 = 500303) (by norm_num)
theorem B1334213 : Blo 591290 1334213 := bbase (se 4 (by rfl) ⟨125082, by rfl⟩ : syracuseStep 1334213 = 250165) (by norm_num)
theorem B1498085 : Blo 591290 1498085 := bbase (se 4 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 1498085 = 280891) (by norm_num)
theorem B5790709 : Blo 591290 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B1334285 : Blo 591290 1334285 := bbase (se 3 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 1334285 = 500357) (by norm_num)
theorem B2710565 : Blo 591290 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B1694789 : Blo 591290 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B1334357 : Blo 591290 1334357 := bbase (se 8 (by rfl) ⟨7818, by rfl⟩ : syracuseStep 1334357 = 15637) (by norm_num)
theorem B1236061 : Blo 591290 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B2841733 : Blo 591290 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B1334429 : Blo 591290 1334429 := bbase (se 3 (by rfl) ⟨250205, by rfl⟩ : syracuseStep 1334429 = 500411) (by norm_num)
theorem B1498277 : Blo 591290 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B1334501 : Blo 591290 1334501 := bbase (se 4 (by rfl) ⟨125109, by rfl⟩ : syracuseStep 1334501 = 250219) (by norm_num)
theorem B1072397 : Blo 591290 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B5692693 : Blo 591290 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1334573 : Blo 591290 1334573 := bbase (se 3 (by rfl) ⟨250232, by rfl⟩ : syracuseStep 1334573 = 500465) (by norm_num)
theorem B1334645 : Blo 591290 1334645 := bbase (se 5 (by rfl) ⟨62561, by rfl⟩ : syracuseStep 1334645 = 125123) (by norm_num)
theorem B843157 : Blo 591290 843157 := bbase (se 6 (by rfl) ⟨19761, by rfl⟩ : syracuseStep 843157 = 39523) (by norm_num)
theorem B1334717 : Blo 591290 1334717 := bbase (se 3 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 1334717 = 500519) (by norm_num)
theorem B2252245 : Blo 591290 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B3005909 : Blo 591290 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B1072621 : Blo 591290 1072621 := bbase (se 3 (by rfl) ⟨201116, by rfl⟩ : syracuseStep 1072621 = 402233) (by norm_num)
theorem B1498621 : Blo 591290 1498621 := bbase (se 3 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 1498621 = 561983) (by norm_num)
theorem B1334789 : Blo 591290 1334789 := bbase (se 4 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 1334789 = 250273) (by norm_num)
theorem B2022965 : Blo 591290 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B1334861 : Blo 591290 1334861 := bbase (se 3 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 1334861 = 500573) (by norm_num)
theorem B1269341 : Blo 591290 1269341 := bbase (se 3 (by rfl) ⟨238001, by rfl⟩ : syracuseStep 1269341 = 476003) (by norm_num)
theorem B1498733 : Blo 591290 1498733 := bbase (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) (by norm_num)
theorem B1334933 : Blo 591290 1334933 := bbase (se 6 (by rfl) ⟨31287, by rfl⟩ : syracuseStep 1334933 = 62575) (by norm_num)
theorem B4284053 : Blo 591290 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B1335005 : Blo 591290 1335005 := bbase (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) (by norm_num)
theorem B2252549 : Blo 591290 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B712481 : Blo 591290 712481 := bbase (se 2 (by rfl) ⟨267180, by rfl⟩ : syracuseStep 712481 = 534361) (by norm_num)
theorem B1335077 : Blo 591290 1335077 := bbase (se 4 (by rfl) ⟨125163, by rfl⟩ : syracuseStep 1335077 = 250327) (by norm_num)
theorem B1498925 : Blo 591290 1498925 := bbase (se 3 (by rfl) ⟨281048, by rfl⟩ : syracuseStep 1498925 = 562097) (by norm_num)
theorem B1335149 : Blo 591290 1335149 := bbase (se 3 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 1335149 = 500681) (by norm_num)
theorem B1335221 : Blo 591290 1335221 := bbase (se 5 (by rfl) ⟨62588, by rfl⟩ : syracuseStep 1335221 = 125177) (by norm_num)
theorem B1335293 : Blo 591290 1335293 := bbase (se 3 (by rfl) ⟨250367, by rfl⟩ : syracuseStep 1335293 = 500735) (by norm_num)
theorem B1335365 : Blo 591290 1335365 := bbase (se 4 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 1335365 = 250381) (by norm_num)
theorem B1499269 : Blo 591290 1499269 := bbase (se 4 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 1499269 = 281113) (by norm_num)
theorem B712837 : Blo 591290 712837 := bbase (se 4 (by rfl) ⟨66828, by rfl⟩ : syracuseStep 712837 = 133657) (by norm_num)
theorem B1335437 : Blo 591290 1335437 := bbase (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) (by norm_num)
theorem B843949 : Blo 591290 843949 := bbase (se 3 (by rfl) ⟨158240, by rfl⟩ : syracuseStep 843949 = 316481) (by norm_num)
theorem B1335509 : Blo 591290 1335509 := bbase (se 7 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 1335509 = 31301) (by norm_num)
theorem B1499381 : Blo 591290 1499381 := bbase (se 5 (by rfl) ⟨70283, by rfl⟩ : syracuseStep 1499381 = 140567) (by norm_num)
theorem B1335581 : Blo 591290 1335581 := bbase (se 3 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 1335581 = 500843) (by norm_num)
theorem B713029 : Blo 591290 713029 := bbase (se 4 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 713029 = 133693) (by norm_num)
theorem B1270093 : Blo 591290 1270093 := bbase (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) (by norm_num)
theorem B1335653 : Blo 591290 1335653 := bbase (se 4 (by rfl) ⟨125217, by rfl⟩ : syracuseStep 1335653 = 250435) (by norm_num)
theorem B1335725 : Blo 591290 1335725 := bbase (se 3 (by rfl) ⟨250448, by rfl⟩ : syracuseStep 1335725 = 500897) (by norm_num)
theorem B1499573 : Blo 591290 1499573 := bbase (se 5 (by rfl) ⟨70292, by rfl⟩ : syracuseStep 1499573 = 140585) (by norm_num)
theorem B1139141 : Blo 591290 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B713173 : Blo 591290 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B1270237 : Blo 591290 1270237 := bbase (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) (by norm_num)
theorem B1335797 : Blo 591290 1335797 := bbase (se 5 (by rfl) ⟨62615, by rfl⟩ : syracuseStep 1335797 = 125231) (by norm_num)
theorem B844285 : Blo 591290 844285 := bbase (se 3 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 844285 = 316607) (by norm_num)
theorem B1335869 : Blo 591290 1335869 := bbase (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) (by norm_num)
theorem B1335941 : Blo 591290 1335941 := bbase (se 4 (by rfl) ⟨125244, by rfl⟩ : syracuseStep 1335941 = 250489) (by norm_num)
theorem B4514453 : Blo 591290 4514453 := bbase (se 6 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 4514453 = 211615) (by norm_num)
theorem B1336013 : Blo 591290 1336013 := bbase (se 3 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 1336013 = 501005) (by norm_num)
theorem B844501 : Blo 591290 844501 := bbase (se 7 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 844501 = 19793) (by norm_num)
theorem B3007205 : Blo 591290 3007205 := bbase (se 4 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 3007205 = 563851) (by norm_num)
theorem B1499917 : Blo 591290 1499917 := bbase (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) (by norm_num)
theorem B1336085 : Blo 591290 1336085 := bbase (se 6 (by rfl) ⟨31314, by rfl⟩ : syracuseStep 1336085 = 62629) (by norm_num)
theorem B1270613 : Blo 591290 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B1336157 : Blo 591290 1336157 := bbase (se 3 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 1336157 = 501059) (by norm_num)
theorem B1500029 : Blo 591290 1500029 := bbase (se 3 (by rfl) ⟨281255, by rfl⟩ : syracuseStep 1500029 = 562511) (by norm_num)
theorem B3597205 : Blo 591290 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B1336229 : Blo 591290 1336229 := bbase (se 4 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 1336229 = 250543) (by norm_num)
theorem B3793877 : Blo 591290 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B1336301 : Blo 591290 1336301 := bbase (se 3 (by rfl) ⟨250556, by rfl⟩ : syracuseStep 1336301 = 501113) (by norm_num)
theorem B1336373 : Blo 591290 1336373 := bbase (se 5 (by rfl) ⟨62642, by rfl⟩ : syracuseStep 1336373 = 125285) (by norm_num)
theorem B1500221 : Blo 591290 1500221 := bbase (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) (by norm_num)
theorem B844877 : Blo 591290 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1336445 : Blo 591290 1336445 := bbase (se 3 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 1336445 = 501167) (by norm_num)
theorem B1336517 : Blo 591290 1336517 := bbase (se 4 (by rfl) ⟨125298, by rfl⟩ : syracuseStep 1336517 = 250597) (by norm_num)
theorem B1270981 : Blo 591290 1270981 := bbase (se 4 (by rfl) ⟨119154, by rfl⟩ : syracuseStep 1270981 = 238309) (by norm_num)
theorem B1336589 : Blo 591290 1336589 := bbase (se 3 (by rfl) ⟨250610, by rfl⟩ : syracuseStep 1336589 = 501221) (by norm_num)
theorem B2057557 : Blo 591290 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B1336661 : Blo 591290 1336661 := bbase (se 12 (by rfl) ⟨489, by rfl⟩ : syracuseStep 1336661 = 979) (by norm_num)
theorem B1598821 : Blo 591290 1598821 := bbase (se 4 (by rfl) ⟨149889, by rfl⟩ : syracuseStep 1598821 = 299779) (by norm_num)
theorem B812389 : Blo 591290 812389 := bbase (se 4 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 812389 = 152323) (by norm_num)
theorem B1500565 : Blo 591290 1500565 := bbase (se 6 (by rfl) ⟨35169, by rfl⟩ : syracuseStep 1500565 = 70339) (by norm_num)
theorem B1336733 : Blo 591290 1336733 := bbase (se 3 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 1336733 = 501275) (by norm_num)
theorem B1336805 : Blo 591290 1336805 := bbase (se 4 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 1336805 = 250651) (by norm_num)
theorem B1500677 : Blo 591290 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B1336877 : Blo 591290 1336877 := bbase (se 3 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 1336877 = 501329) (by norm_num)
theorem B1336949 : Blo 591290 1336949 := bbase (se 5 (by rfl) ⟨62669, by rfl⟩ : syracuseStep 1336949 = 125339) (by norm_num)
theorem B1337021 : Blo 591290 1337021 := bbase (se 3 (by rfl) ⟨250691, by rfl⟩ : syracuseStep 1337021 = 501383) (by norm_num)
theorem B1500869 : Blo 591290 1500869 := bbase (se 4 (by rfl) ⟨140706, by rfl⟩ : syracuseStep 1500869 = 281413) (by norm_num)
theorem B1337093 : Blo 591290 1337093 := bbase (se 4 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 1337093 = 250705) (by norm_num)
theorem B2254661 : Blo 591290 2254661 := bbase (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) (by norm_num)
theorem B1337165 : Blo 591290 1337165 := bbase (se 3 (by rfl) ⟨250718, by rfl⟩ : syracuseStep 1337165 = 501437) (by norm_num)
theorem B1599365 : Blo 591290 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B1337237 : Blo 591290 1337237 := bbase (se 6 (by rfl) ⟨31341, by rfl⟩ : syracuseStep 1337237 = 62683) (by norm_num)
theorem B714701 : Blo 591290 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B1337309 : Blo 591290 1337309 := bbase (se 3 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 1337309 = 501491) (by norm_num)
theorem B3008501 : Blo 591290 3008501 := bbase (se 5 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 3008501 = 282047) (by norm_num)
theorem B1501213 : Blo 591290 1501213 := bbase (se 3 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 1501213 = 562955) (by norm_num)
theorem B1337381 : Blo 591290 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B5695541 : Blo 591290 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B2254949 : Blo 591290 2254949 := bbase (se 4 (by rfl) ⟨211401, by rfl⟩ : syracuseStep 2254949 = 422803) (by norm_num)
theorem B1337453 : Blo 591290 1337453 := bbase (se 3 (by rfl) ⟨250772, by rfl⟩ : syracuseStep 1337453 = 501545) (by norm_num)
theorem B1501325 : Blo 591290 1501325 := bbase (se 3 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 1501325 = 562997) (by norm_num)
theorem B1337525 : Blo 591290 1337525 := bbase (se 5 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 1337525 = 125393) (by norm_num)
theorem B1337597 : Blo 591290 1337597 := bbase (se 3 (by rfl) ⟨250799, by rfl⟩ : syracuseStep 1337597 = 501599) (by norm_num)
theorem B715009 : Blo 591290 715009 := bbase (se 2 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 715009 = 536257) (by norm_num)
theorem B1337669 : Blo 591290 1337669 := bbase (se 4 (by rfl) ⟨125406, by rfl⟩ : syracuseStep 1337669 = 250813) (by norm_num)
theorem B1501517 : Blo 591290 1501517 := bbase (se 3 (by rfl) ⟨281534, by rfl⟩ : syracuseStep 1501517 = 563069) (by norm_num)
theorem B715105 : Blo 591290 715105 := bbase (se 2 (by rfl) ⟨268164, by rfl⟩ : syracuseStep 715105 = 536329) (by norm_num)
theorem B1337741 : Blo 591290 1337741 := bbase (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) (by norm_num)
theorem B1337813 : Blo 591290 1337813 := bbase (se 7 (by rfl) ⟨15677, by rfl⟩ : syracuseStep 1337813 = 31355) (by norm_num)
theorem B846301 : Blo 591290 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B1337885 : Blo 591290 1337885 := bbase (se 3 (by rfl) ⟨250853, by rfl⟩ : syracuseStep 1337885 = 501707) (by norm_num)
theorem B1337957 : Blo 591290 1337957 := bbase (se 4 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 1337957 = 250867) (by norm_num)
theorem B1501861 : Blo 591290 1501861 := bbase (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) (by norm_num)
theorem B1338029 : Blo 591290 1338029 := bbase (se 3 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 1338029 = 501761) (by norm_num)
theorem B1338101 : Blo 591290 1338101 := bbase (se 5 (by rfl) ⟨62723, by rfl⟩ : syracuseStep 1338101 = 125447) (by norm_num)
theorem B1501973 : Blo 591290 1501973 := bbase (se 6 (by rfl) ⟨35202, by rfl⟩ : syracuseStep 1501973 = 70405) (by norm_num)
theorem B1338173 : Blo 591290 1338173 := bbase (se 3 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 1338173 = 501815) (by norm_num)
theorem B748369 : Blo 591290 748369 := bbase (se 2 (by rfl) ⟨280638, by rfl⟩ : syracuseStep 748369 = 561277) (by norm_num)
theorem B1338245 : Blo 591290 1338245 := bbase (se 4 (by rfl) ⟨125460, by rfl⟩ : syracuseStep 1338245 = 250921) (by norm_num)
theorem B813997 : Blo 591290 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B1338317 : Blo 591290 1338317 := bbase (se 3 (by rfl) ⟨250934, by rfl⟩ : syracuseStep 1338317 = 501869) (by norm_num)
theorem B3206101 : Blo 591290 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B1502165 : Blo 591290 1502165 := bbase (se 7 (by rfl) ⟨17603, by rfl⟩ : syracuseStep 1502165 = 35207) (by norm_num)
theorem B748541 : Blo 591290 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1338389 : Blo 591290 1338389 := bbase (se 6 (by rfl) ⟨31368, by rfl⟩ : syracuseStep 1338389 = 62737) (by norm_num)
theorem B846893 : Blo 591290 846893 := bbase (se 3 (by rfl) ⟨158792, by rfl⟩ : syracuseStep 846893 = 317585) (by norm_num)
theorem B748597 : Blo 591290 748597 := bbase (se 5 (by rfl) ⟨35090, by rfl⟩ : syracuseStep 748597 = 70181) (by norm_num)
theorem B1338461 : Blo 591290 1338461 := bbase (se 3 (by rfl) ⟨250961, by rfl⟩ : syracuseStep 1338461 = 501923) (by norm_num)
theorem B1174637 : Blo 591290 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B846973 : Blo 591290 846973 := bbase (se 3 (by rfl) ⟨158807, by rfl⟩ : syracuseStep 846973 = 317615) (by norm_num)
theorem B748693 : Blo 591290 748693 := bbase (se 6 (by rfl) ⟨17547, by rfl⟩ : syracuseStep 748693 = 35095) (by norm_num)
theorem B1338533 : Blo 591290 1338533 := bbase (se 4 (by rfl) ⟨125487, by rfl⟩ : syracuseStep 1338533 = 250975) (by norm_num)
theorem B2845925 : Blo 591290 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1338605 : Blo 591290 1338605 := bbase (se 3 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 1338605 = 501977) (by norm_num)
theorem B1895669 : Blo 591290 1895669 := bbase (se 5 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 1895669 = 177719) (by norm_num)
theorem B847093 : Blo 591290 847093 := bbase (se 5 (by rfl) ⟨39707, by rfl⟩ : syracuseStep 847093 = 79415) (by norm_num)
theorem B2256133 : Blo 591290 2256133 := bbase (se 4 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 2256133 = 423025) (by norm_num)
theorem B3009797 : Blo 591290 3009797 := bbase (se 4 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 3009797 = 564337) (by norm_num)
theorem B1502509 : Blo 591290 1502509 := bbase (se 3 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 1502509 = 563441) (by norm_num)
theorem B1338677 : Blo 591290 1338677 := bbase (se 5 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 1338677 = 125501) (by norm_num)
theorem B748865 : Blo 591290 748865 := bbase (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) (by norm_num)
theorem B847189 : Blo 591290 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B748921 : Blo 591290 748921 := bbase (se 2 (by rfl) ⟨280845, by rfl⟩ : syracuseStep 748921 = 561691) (by norm_num)
theorem B1338749 : Blo 591290 1338749 := bbase (se 3 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 1338749 = 502031) (by norm_num)
theorem B1142165 : Blo 591290 1142165 := bbase (se 6 (by rfl) ⟨26769, by rfl⟩ : syracuseStep 1142165 = 53539) (by norm_num)
theorem B1502621 : Blo 591290 1502621 := bbase (se 3 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 1502621 = 563483) (by norm_num)
theorem B1338821 : Blo 591290 1338821 := bbase (se 4 (by rfl) ⟨125514, by rfl⟩ : syracuseStep 1338821 = 251029) (by norm_num)
theorem B749017 : Blo 591290 749017 := bbase (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) (by norm_num)
theorem B1338893 : Blo 591290 1338893 := bbase (se 3 (by rfl) ⟨251042, by rfl⟩ : syracuseStep 1338893 = 502085) (by norm_num)
theorem B2256437 : Blo 591290 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1338965 : Blo 591290 1338965 := bbase (se 8 (by rfl) ⟨7845, by rfl⟩ : syracuseStep 1338965 = 15691) (by norm_num)
theorem B1502813 : Blo 591290 1502813 := bbase (se 3 (by rfl) ⟨281777, by rfl⟩ : syracuseStep 1502813 = 563555) (by norm_num)
theorem B1142381 : Blo 591290 1142381 := bbase (se 3 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 1142381 = 428393) (by norm_num)
theorem B749189 : Blo 591290 749189 := bbase (se 4 (by rfl) ⟨70236, by rfl⟩ : syracuseStep 749189 = 140473) (by norm_num)
theorem B1339037 : Blo 591290 1339037 := bbase (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) (by norm_num)
theorem B749245 : Blo 591290 749245 := bbase (se 3 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 749245 = 280967) (by norm_num)
theorem B1339109 : Blo 591290 1339109 := bbase (se 4 (by rfl) ⟨125541, by rfl⟩ : syracuseStep 1339109 = 251083) (by norm_num)
theorem B9596693 : Blo 591290 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B749341 : Blo 591290 749341 := bbase (se 3 (by rfl) ⟨140501, by rfl⟩ : syracuseStep 749341 = 281003) (by norm_num)
theorem B1339181 : Blo 591290 1339181 := bbase (se 3 (by rfl) ⟨251096, by rfl⟩ : syracuseStep 1339181 = 502193) (by norm_num)
theorem B3370805 : Blo 591290 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B1339253 : Blo 591290 1339253 := bbase (se 5 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 1339253 = 125555) (by norm_num)
theorem B1503157 : Blo 591290 1503157 := bbase (se 5 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 1503157 = 140921) (by norm_num)
theorem B1339325 : Blo 591290 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B749513 : Blo 591290 749513 := bbase (se 2 (by rfl) ⟨281067, by rfl⟩ : syracuseStep 749513 = 562135) (by norm_num)
theorem B5074933 : Blo 591290 5074933 := bbase (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) (by norm_num)
theorem B749569 : Blo 591290 749569 := bbase (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) (by norm_num)
theorem B1339397 : Blo 591290 1339397 := bbase (se 4 (by rfl) ⟨125568, by rfl⟩ : syracuseStep 1339397 = 251137) (by norm_num)
theorem B1503269 : Blo 591290 1503269 := bbase (se 4 (by rfl) ⟨140931, by rfl⟩ : syracuseStep 1503269 = 281863) (by norm_num)
theorem B3797077 : Blo 591290 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B749665 : Blo 591290 749665 := bbase (se 2 (by rfl) ⟨281124, by rfl⟩ : syracuseStep 749665 = 562249) (by norm_num)
theorem B1503461 : Blo 591290 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B749837 : Blo 591290 749837 := bbase (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) (by norm_num)
theorem B749893 : Blo 591290 749893 := bbase (se 4 (by rfl) ⟨70302, by rfl⟩ : syracuseStep 749893 = 140605) (by norm_num)
theorem B1012133 : Blo 591290 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B749989 : Blo 591290 749989 := bbase (se 4 (by rfl) ⟨70311, by rfl⟩ : syracuseStep 749989 = 140623) (by norm_num)
theorem B1896949 : Blo 591290 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B3011093 : Blo 591290 3011093 := bbase (se 6 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 3011093 = 141145) (by norm_num)
theorem B2847269 : Blo 591290 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B1503805 : Blo 591290 1503805 := bbase (se 3 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 1503805 = 563927) (by norm_num)
theorem B750161 : Blo 591290 750161 := bbase (se 2 (by rfl) ⟨281310, by rfl⟩ : syracuseStep 750161 = 562621) (by norm_num)
theorem B750217 : Blo 591290 750217 := bbase (se 2 (by rfl) ⟨281331, by rfl⟩ : syracuseStep 750217 = 562663) (by norm_num)
theorem B1503917 : Blo 591290 1503917 := bbase (se 3 (by rfl) ⟨281984, by rfl⟩ : syracuseStep 1503917 = 563969) (by norm_num)
theorem B750313 : Blo 591290 750313 := bbase (se 2 (by rfl) ⟨281367, by rfl⟩ : syracuseStep 750313 = 562735) (by norm_num)
theorem B2028325 : Blo 591290 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B783145 : Blo 591290 783145 := bbase (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) (by norm_num)
theorem B1504109 : Blo 591290 1504109 := bbase (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) (by norm_num)
theorem B750485 : Blo 591290 750485 := bbase (se 6 (by rfl) ⟨17589, by rfl⟩ : syracuseStep 750485 = 35179) (by norm_num)
theorem B750541 : Blo 591290 750541 := bbase (se 3 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 750541 = 281453) (by norm_num)
theorem B3371989 : Blo 591290 3371989 := bbase (se 7 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 3371989 = 79031) (by norm_num)
theorem B750637 : Blo 591290 750637 := bbase (se 3 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 750637 = 281489) (by norm_num)
theorem B1995893 : Blo 591290 1995893 := bbase (se 5 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 1995893 = 187115) (by norm_num)
theorem B1504453 : Blo 591290 1504453 := bbase (se 4 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 1504453 = 282085) (by norm_num)
theorem B750809 : Blo 591290 750809 := bbase (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) (by norm_num)
theorem B750865 : Blo 591290 750865 := bbase (se 2 (by rfl) ⟨281574, by rfl⟩ : syracuseStep 750865 = 563149) (by norm_num)
theorem B1504565 : Blo 591290 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B750961 : Blo 591290 750961 := bbase (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) (by norm_num)
theorem B3667349 : Blo 591290 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B947629 : Blo 591290 947629 := bbase (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) (by norm_num)
theorem B1504757 : Blo 591290 1504757 := bbase (se 5 (by rfl) ⟨70535, by rfl⟩ : syracuseStep 1504757 = 141071) (by norm_num)
theorem B751133 : Blo 591290 751133 := bbase (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) (by norm_num)
theorem B1996325 : Blo 591290 1996325 := bbase (se 4 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 1996325 = 374311) (by norm_num)
theorem B751189 : Blo 591290 751189 := bbase (se 8 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 751189 = 8803) (by norm_num)
theorem B2258549 : Blo 591290 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B751285 : Blo 591290 751285 := bbase (se 5 (by rfl) ⟨35216, by rfl⟩ : syracuseStep 751285 = 70433) (by norm_num)
theorem B3012389 : Blo 591290 3012389 := bbase (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) (by norm_num)
theorem B1898309 : Blo 591290 1898309 := bbase (se 4 (by rfl) ⟨177966, by rfl⟩ : syracuseStep 1898309 = 355933) (by norm_num)
theorem B1505101 : Blo 591290 1505101 := bbase (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) (by norm_num)
theorem B751457 : Blo 591290 751457 := bbase (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) (by norm_num)
theorem B2258837 : Blo 591290 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B751513 : Blo 591290 751513 := bbase (se 2 (by rfl) ⟨281817, by rfl⟩ : syracuseStep 751513 = 563635) (by norm_num)
theorem B685981 : Blo 591290 685981 := bbase (se 3 (by rfl) ⟨128621, by rfl⟩ : syracuseStep 685981 = 257243) (by norm_num)
theorem B1603493 : Blo 591290 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B5076917 : Blo 591290 5076917 := bbase (se 5 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 5076917 = 475961) (by norm_num)
theorem B1505213 : Blo 591290 1505213 := bbase (se 3 (by rfl) ⟨282227, by rfl⟩ : syracuseStep 1505213 = 564455) (by norm_num)
theorem B1898437 : Blo 591290 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B1996757 : Blo 591290 1996757 := bbase (se 7 (by rfl) ⟨23399, by rfl⟩ : syracuseStep 1996757 = 46799) (by norm_num)
theorem B948181 : Blo 591290 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B751609 : Blo 591290 751609 := bbase (se 2 (by rfl) ⟨281853, by rfl⟩ : syracuseStep 751609 = 563707) (by norm_num)
theorem B1931381 : Blo 591290 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B1505405 : Blo 591290 1505405 := bbase (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) (by norm_num)
theorem B751781 : Blo 591290 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B1898693 : Blo 591290 1898693 := bbase (se 4 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 1898693 = 356005) (by norm_num)
theorem B948437 : Blo 591290 948437 := bbase (se 7 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 948437 = 22229) (by norm_num)
theorem B751837 : Blo 591290 751837 := bbase (se 3 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 751837 = 281939) (by norm_num)
theorem B1145053 : Blo 591290 1145053 := bbase (se 3 (by rfl) ⟨214697, by rfl⟩ : syracuseStep 1145053 = 429395) (by norm_num)
theorem B751933 : Blo 591290 751933 := bbase (se 3 (by rfl) ⟨140987, by rfl⟩ : syracuseStep 751933 = 281975) (by norm_num)
theorem B1997189 : Blo 591290 1997189 := bbase (se 4 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 1997189 = 374473) (by norm_num)
theorem B8550805 : Blo 591290 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B1505749 : Blo 591290 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B752105 : Blo 591290 752105 := bbase (se 2 (by rfl) ⟨282039, by rfl⟩ : syracuseStep 752105 = 564079) (by norm_num)
theorem B2849269 : Blo 591290 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B752161 : Blo 591290 752161 := bbase (se 2 (by rfl) ⟨282060, by rfl⟩ : syracuseStep 752161 = 564121) (by norm_num)
theorem B1505861 : Blo 591290 1505861 := bbase (se 4 (by rfl) ⟨141174, by rfl⟩ : syracuseStep 1505861 = 282349) (by norm_num)
theorem B752257 : Blo 591290 752257 := bbase (se 2 (by rfl) ⟨282096, by rfl⟩ : syracuseStep 752257 = 564193) (by norm_num)
theorem B1506053 : Blo 591290 1506053 := bbase (se 4 (by rfl) ⟨141192, by rfl⟩ : syracuseStep 1506053 = 282385) (by norm_num)
theorem B752429 : Blo 591290 752429 := bbase (se 3 (by rfl) ⟨141080, by rfl⟩ : syracuseStep 752429 = 282161) (by norm_num)
theorem B1997621 : Blo 591290 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B752485 : Blo 591290 752485 := bbase (se 4 (by rfl) ⟨70545, by rfl⟩ : syracuseStep 752485 = 141091) (by norm_num)
theorem B1801109 : Blo 591290 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B3373973 : Blo 591290 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B949141 : Blo 591290 949141 := bbase (se 6 (by rfl) ⟨22245, by rfl⟩ : syracuseStep 949141 = 44491) (by norm_num)
theorem B752581 : Blo 591290 752581 := bbase (se 4 (by rfl) ⟨70554, by rfl⟩ : syracuseStep 752581 = 141109) (by norm_num)
theorem B687109 : Blo 591290 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B2260021 : Blo 591290 2260021 := bbase (se 5 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 2260021 = 211877) (by norm_num)
theorem B1506397 : Blo 591290 1506397 := bbase (se 3 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 1506397 = 564899) (by norm_num)
theorem B1440877 : Blo 591290 1440877 := bbase (se 3 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 1440877 = 540329) (by norm_num)
theorem B752753 : Blo 591290 752753 := bbase (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) (by norm_num)
theorem B752809 : Blo 591290 752809 := bbase (se 2 (by rfl) ⟨282303, by rfl⟩ : syracuseStep 752809 = 564607) (by norm_num)
theorem B1506509 : Blo 591290 1506509 := bbase (se 3 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 1506509 = 564941) (by norm_num)
theorem B1998053 : Blo 591290 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B752905 : Blo 591290 752905 := bbase (se 2 (by rfl) ⟨282339, by rfl⟩ : syracuseStep 752905 = 564679) (by norm_num)
theorem B1539341 : Blo 591290 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B949565 : Blo 591290 949565 := bbase (se 3 (by rfl) ⟨178043, by rfl⟩ : syracuseStep 949565 = 356087) (by norm_num)
theorem B2751877 : Blo 591290 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B1506701 : Blo 591290 1506701 := bbase (se 3 (by rfl) ⟨282506, by rfl⟩ : syracuseStep 1506701 = 565013) (by norm_num)
theorem B1375645 : Blo 591290 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B753077 : Blo 591290 753077 := bbase (se 5 (by rfl) ⟨35300, by rfl⟩ : syracuseStep 753077 = 70601) (by norm_num)
theorem B753133 : Blo 591290 753133 := bbase (se 3 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 753133 = 282425) (by norm_num)
theorem B753229 : Blo 591290 753229 := bbase (se 3 (by rfl) ⟨141230, by rfl⟩ : syracuseStep 753229 = 282461) (by norm_num)
theorem B949853 : Blo 591290 949853 := bbase (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) (by norm_num)
theorem B1998485 : Blo 591290 1998485 := bbase (se 6 (by rfl) ⟨46839, by rfl⟩ : syracuseStep 1998485 = 93679) (by norm_num)
theorem B3210965 : Blo 591290 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B753401 : Blo 591290 753401 := bbase (se 2 (by rfl) ⟨282525, by rfl⟩ : syracuseStep 753401 = 565051) (by norm_num)
theorem B950077 : Blo 591290 950077 := bbase (se 3 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 950077 = 356279) (by norm_num)
theorem B3211397 : Blo 591290 3211397 := bstep (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) B602137
theorem B1999025 : Blo 591290 1999025 := bstep (se 2 (by rfl) ⟨749634, by rfl⟩ : syracuseStep 1999025 = 1499269) B1499269
theorem B950449 : Blo 591290 950449 := bstep (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) B712837
theorem B3801485 : Blo 591290 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B950705 : Blo 591290 950705 := bstep (se 2 (by rfl) ⟨356514, by rfl⟩ : syracuseStep 950705 = 713029) B713029
theorem B950897 : Blo 591290 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B1999565 : Blo 591290 1999565 := bstep (se 3 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 1999565 = 749837) B749837
theorem B1999619 : Blo 591290 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B1999889 : Blo 591290 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B591299 : Blo 591290 591299 := bstep (se 1 (by rfl) ⟨443474, by rfl⟩ : syracuseStep 591299 = 886949) B886949
theorem B1803725 : Blo 591290 1803725 := bstep (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) B676397
theorem B591315 : Blo 591290 591315 := bstep (se 1 (by rfl) ⟨443486, by rfl⟩ : syracuseStep 591315 = 886973) B886973
theorem B591331 : Blo 591290 591331 := bstep (se 1 (by rfl) ⟨443498, by rfl⟩ : syracuseStep 591331 = 886997) B886997
theorem B591347 : Blo 591290 591347 := bstep (se 1 (by rfl) ⟨443510, by rfl⟩ : syracuseStep 591347 = 887021) B887021
theorem B591363 : Blo 591290 591363 := bstep (se 1 (by rfl) ⟨443522, by rfl⟩ : syracuseStep 591363 = 887045) B887045
theorem B591379 : Blo 591290 591379 := bstep (se 1 (by rfl) ⟨443534, by rfl⟩ : syracuseStep 591379 = 887069) B887069
theorem B591395 : Blo 591290 591395 := bstep (se 1 (by rfl) ⟨443546, by rfl⟩ : syracuseStep 591395 = 887093) B887093
theorem B2000429 : Blo 591290 2000429 := bstep (se 3 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 2000429 = 750161) B750161
theorem B591411 : Blo 591290 591411 := bstep (se 1 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 591411 = 887117) B887117
theorem B591427 : Blo 591290 591427 := bstep (se 1 (by rfl) ⟨443570, by rfl⟩ : syracuseStep 591427 = 887141) B887141
theorem B591443 : Blo 591290 591443 := bstep (se 1 (by rfl) ⟨443582, by rfl⟩ : syracuseStep 591443 = 887165) B887165
theorem B591459 : Blo 591290 591459 := bstep (se 1 (by rfl) ⟨443594, by rfl⟩ : syracuseStep 591459 = 887189) B887189
theorem B2000483 : Blo 591290 2000483 := bstep (se 1 (by rfl) ⟨1500362, by rfl⟩ : syracuseStep 2000483 = 3000725) B3000725
theorem B591475 : Blo 591290 591475 := bstep (se 1 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 591475 = 887213) B887213
theorem B591491 : Blo 591290 591491 := bstep (se 1 (by rfl) ⟨443618, by rfl⟩ : syracuseStep 591491 = 887237) B887237
theorem B591507 : Blo 591290 591507 := bstep (se 1 (by rfl) ⟨443630, by rfl⟩ : syracuseStep 591507 = 887261) B887261
theorem B591523 : Blo 591290 591523 := bstep (se 1 (by rfl) ⟨443642, by rfl⟩ : syracuseStep 591523 = 887285) B887285
theorem B591539 : Blo 591290 591539 := bstep (se 1 (by rfl) ⟨443654, by rfl⟩ : syracuseStep 591539 = 887309) B887309
theorem B591555 : Blo 591290 591555 := bstep (se 1 (by rfl) ⟨443666, by rfl⟩ : syracuseStep 591555 = 887333) B887333
theorem B591571 : Blo 591290 591571 := bstep (se 1 (by rfl) ⟨443678, by rfl⟩ : syracuseStep 591571 = 887357) B887357
theorem B591587 : Blo 591290 591587 := bstep (se 1 (by rfl) ⟨443690, by rfl⟩ : syracuseStep 591587 = 887381) B887381
theorem B591603 : Blo 591290 591603 := bstep (se 1 (by rfl) ⟨443702, by rfl⟩ : syracuseStep 591603 = 887405) B887405
theorem B591619 : Blo 591290 591619 := bstep (se 1 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 591619 = 887429) B887429
theorem B591635 : Blo 591290 591635 := bstep (se 1 (by rfl) ⟨443726, by rfl⟩ : syracuseStep 591635 = 887453) B887453
theorem B591651 : Blo 591290 591651 := bstep (se 1 (by rfl) ⟨443738, by rfl⟩ : syracuseStep 591651 = 887477) B887477
theorem B591667 : Blo 591290 591667 := bstep (se 1 (by rfl) ⟨443750, by rfl⟩ : syracuseStep 591667 = 887501) B887501
theorem B591683 : Blo 591290 591683 := bstep (se 1 (by rfl) ⟨443762, by rfl⟩ : syracuseStep 591683 = 887525) B887525
theorem B591699 : Blo 591290 591699 := bstep (se 1 (by rfl) ⟨443774, by rfl⟩ : syracuseStep 591699 = 887549) B887549
theorem B591715 : Blo 591290 591715 := bstep (se 1 (by rfl) ⟨443786, by rfl⟩ : syracuseStep 591715 = 887573) B887573
theorem B2000753 : Blo 591290 2000753 := bstep (se 2 (by rfl) ⟨750282, by rfl⟩ : syracuseStep 2000753 = 1500565) B1500565
theorem B591731 : Blo 591290 591731 := bstep (se 1 (by rfl) ⟨443798, by rfl⟩ : syracuseStep 591731 = 887597) B887597
theorem B591747 : Blo 591290 591747 := bstep (se 1 (by rfl) ⟨443810, by rfl⟩ : syracuseStep 591747 = 887621) B887621
theorem B591763 : Blo 591290 591763 := bstep (se 1 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 591763 = 887645) B887645
theorem B952211 : Blo 591290 952211 := bstep (se 1 (by rfl) ⟨714158, by rfl⟩ : syracuseStep 952211 = 1428317) B1428317
theorem B591779 : Blo 591290 591779 := bstep (se 1 (by rfl) ⟨443834, by rfl⟩ : syracuseStep 591779 = 887669) B887669
theorem B591795 : Blo 591290 591795 := bstep (se 1 (by rfl) ⟨443846, by rfl⟩ : syracuseStep 591795 = 887693) B887693
theorem B591811 : Blo 591290 591811 := bstep (se 1 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 591811 = 887717) B887717
theorem B591827 : Blo 591290 591827 := bstep (se 1 (by rfl) ⟨443870, by rfl⟩ : syracuseStep 591827 = 887741) B887741
theorem B591843 : Blo 591290 591843 := bstep (se 1 (by rfl) ⟨443882, by rfl⟩ : syracuseStep 591843 = 887765) B887765
theorem B591859 : Blo 591290 591859 := bstep (se 1 (by rfl) ⟨443894, by rfl⟩ : syracuseStep 591859 = 887789) B887789
theorem B591875 : Blo 591290 591875 := bstep (se 1 (by rfl) ⟨443906, by rfl⟩ : syracuseStep 591875 = 887813) B887813
theorem B591891 : Blo 591290 591891 := bstep (se 1 (by rfl) ⟨443918, by rfl⟩ : syracuseStep 591891 = 887837) B887837
theorem B591907 : Blo 591290 591907 := bstep (se 1 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 591907 = 887861) B887861
theorem B591923 : Blo 591290 591923 := bstep (se 1 (by rfl) ⟨443942, by rfl⟩ : syracuseStep 591923 = 887885) B887885
theorem B591939 : Blo 591290 591939 := bstep (se 1 (by rfl) ⟨443954, by rfl⟩ : syracuseStep 591939 = 887909) B887909
theorem B591955 : Blo 591290 591955 := bstep (se 1 (by rfl) ⟨443966, by rfl⟩ : syracuseStep 591955 = 887933) B887933
theorem B591971 : Blo 591290 591971 := bstep (se 1 (by rfl) ⟨443978, by rfl⟩ : syracuseStep 591971 = 887957) B887957
theorem B1017955 : Blo 591290 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B591987 : Blo 591290 591987 := bstep (se 1 (by rfl) ⟨443990, by rfl⟩ : syracuseStep 591987 = 887981) B887981
theorem B952435 : Blo 591290 952435 := bstep (se 1 (by rfl) ⟨714326, by rfl⟩ : syracuseStep 952435 = 1428653) B1428653
theorem B592003 : Blo 591290 592003 := bstep (se 1 (by rfl) ⟨444002, by rfl⟩ : syracuseStep 592003 = 888005) B888005
theorem B592019 : Blo 591290 592019 := bstep (se 1 (by rfl) ⟨444014, by rfl⟩ : syracuseStep 592019 = 888029) B888029
theorem B592035 : Blo 591290 592035 := bstep (se 1 (by rfl) ⟨444026, by rfl⟩ : syracuseStep 592035 = 888053) B888053
theorem B886961 : Blo 591290 886961 := bstep (se 2 (by rfl) ⟨332610, by rfl⟩ : syracuseStep 886961 = 665221) B665221
theorem B1804465 : Blo 591290 1804465 := bstep (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) B1353349
theorem B592051 : Blo 591290 592051 := bstep (se 1 (by rfl) ⟨444038, by rfl⟩ : syracuseStep 592051 = 888077) B888077
theorem B952499 : Blo 591290 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B886979 : Blo 591290 886979 := bstep (se 1 (by rfl) ⟨665234, by rfl⟩ : syracuseStep 886979 = 1330469) B1330469
theorem B592067 : Blo 591290 592067 := bstep (se 1 (by rfl) ⟨444050, by rfl⟩ : syracuseStep 592067 = 888101) B888101
theorem B592083 : Blo 591290 592083 := bstep (se 1 (by rfl) ⟨444062, by rfl⟩ : syracuseStep 592083 = 888125) B888125
theorem B887009 : Blo 591290 887009 := bstep (se 2 (by rfl) ⟨332628, by rfl⟩ : syracuseStep 887009 = 665257) B665257
theorem B592099 : Blo 591290 592099 := bstep (se 1 (by rfl) ⟨444074, by rfl⟩ : syracuseStep 592099 = 888149) B888149
theorem B887027 : Blo 591290 887027 := bstep (se 1 (by rfl) ⟨665270, by rfl⟩ : syracuseStep 887027 = 1330541) B1330541
theorem B592115 : Blo 591290 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B592131 : Blo 591290 592131 := bstep (se 1 (by rfl) ⟨444098, by rfl⟩ : syracuseStep 592131 = 888197) B888197
theorem B887057 : Blo 591290 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B592147 : Blo 591290 592147 := bstep (se 1 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 592147 = 888221) B888221
theorem B887075 : Blo 591290 887075 := bstep (se 1 (by rfl) ⟨665306, by rfl⟩ : syracuseStep 887075 = 1330613) B1330613
theorem B592163 : Blo 591290 592163 := bstep (se 1 (by rfl) ⟨444122, by rfl⟩ : syracuseStep 592163 = 888245) B888245
theorem B592179 : Blo 591290 592179 := bstep (se 1 (by rfl) ⟨444134, by rfl⟩ : syracuseStep 592179 = 888269) B888269
theorem B952627 : Blo 591290 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B887105 : Blo 591290 887105 := bstep (se 2 (by rfl) ⟨332664, by rfl⟩ : syracuseStep 887105 = 665329) B665329
theorem B592195 : Blo 591290 592195 := bstep (se 1 (by rfl) ⟨444146, by rfl⟩ : syracuseStep 592195 = 888293) B888293
theorem B887123 : Blo 591290 887123 := bstep (se 1 (by rfl) ⟨665342, by rfl⟩ : syracuseStep 887123 = 1330685) B1330685
theorem B592211 : Blo 591290 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B592227 : Blo 591290 592227 := bstep (se 1 (by rfl) ⟨444170, by rfl⟩ : syracuseStep 592227 = 888341) B888341
theorem B887153 : Blo 591290 887153 := bstep (se 2 (by rfl) ⟨332682, by rfl⟩ : syracuseStep 887153 = 665365) B665365
theorem B592243 : Blo 591290 592243 := bstep (se 1 (by rfl) ⟨444182, by rfl⟩ : syracuseStep 592243 = 888365) B888365
theorem B887171 : Blo 591290 887171 := bstep (se 1 (by rfl) ⟨665378, by rfl⟩ : syracuseStep 887171 = 1330757) B1330757
theorem B592259 : Blo 591290 592259 := bstep (se 1 (by rfl) ⟨444194, by rfl⟩ : syracuseStep 592259 = 888389) B888389
theorem B2001293 : Blo 591290 2001293 := bstep (se 3 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 2001293 = 750485) B750485
theorem B592275 : Blo 591290 592275 := bstep (se 1 (by rfl) ⟨444206, by rfl⟩ : syracuseStep 592275 = 888413) B888413
theorem B887201 : Blo 591290 887201 := bstep (se 2 (by rfl) ⟨332700, by rfl⟩ : syracuseStep 887201 = 665401) B665401
theorem B592291 : Blo 591290 592291 := bstep (se 1 (by rfl) ⟨444218, by rfl⟩ : syracuseStep 592291 = 888437) B888437
theorem B887219 : Blo 591290 887219 := bstep (se 1 (by rfl) ⟨665414, by rfl⟩ : syracuseStep 887219 = 1330829) B1330829
theorem B592307 : Blo 591290 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B592323 : Blo 591290 592323 := bstep (se 1 (by rfl) ⟨444242, by rfl⟩ : syracuseStep 592323 = 888485) B888485
theorem B2001347 : Blo 591290 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B2034115 : Blo 591290 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B887249 : Blo 591290 887249 := bstep (se 2 (by rfl) ⟨332718, by rfl⟩ : syracuseStep 887249 = 665437) B665437
theorem B592339 : Blo 591290 592339 := bstep (se 1 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 592339 = 888509) B888509
theorem B887267 : Blo 591290 887267 := bstep (se 1 (by rfl) ⟨665450, by rfl⟩ : syracuseStep 887267 = 1330901) B1330901
theorem B592355 : Blo 591290 592355 := bstep (se 1 (by rfl) ⟨444266, by rfl⟩ : syracuseStep 592355 = 888533) B888533
theorem B592371 : Blo 591290 592371 := bstep (se 1 (by rfl) ⟨444278, by rfl⟩ : syracuseStep 592371 = 888557) B888557
theorem B887297 : Blo 591290 887297 := bstep (se 2 (by rfl) ⟨332736, by rfl⟩ : syracuseStep 887297 = 665473) B665473
theorem B592387 : Blo 591290 592387 := bstep (se 1 (by rfl) ⟨444290, by rfl⟩ : syracuseStep 592387 = 888581) B888581
theorem B887315 : Blo 591290 887315 := bstep (se 1 (by rfl) ⟨665486, by rfl⟩ : syracuseStep 887315 = 1330973) B1330973
theorem B592403 : Blo 591290 592403 := bstep (se 1 (by rfl) ⟨444302, by rfl⟩ : syracuseStep 592403 = 888605) B888605
theorem B592419 : Blo 591290 592419 := bstep (se 1 (by rfl) ⟨444314, by rfl⟩ : syracuseStep 592419 = 888629) B888629
theorem B887345 : Blo 591290 887345 := bstep (se 2 (by rfl) ⟨332754, by rfl⟩ : syracuseStep 887345 = 665509) B665509
theorem B592435 : Blo 591290 592435 := bstep (se 1 (by rfl) ⟨444326, by rfl⟩ : syracuseStep 592435 = 888653) B888653
theorem B887363 : Blo 591290 887363 := bstep (se 1 (by rfl) ⟨665522, by rfl⟩ : syracuseStep 887363 = 1331045) B1331045
theorem B592451 : Blo 591290 592451 := bstep (se 1 (by rfl) ⟨444338, by rfl⟩ : syracuseStep 592451 = 888677) B888677
theorem B592467 : Blo 591290 592467 := bstep (se 1 (by rfl) ⟨444350, by rfl⟩ : syracuseStep 592467 = 888701) B888701
theorem B887393 : Blo 591290 887393 := bstep (se 2 (by rfl) ⟨332772, by rfl⟩ : syracuseStep 887393 = 665545) B665545
theorem B592483 : Blo 591290 592483 := bstep (se 1 (by rfl) ⟨444362, by rfl⟩ : syracuseStep 592483 = 888725) B888725
theorem B887411 : Blo 591290 887411 := bstep (se 1 (by rfl) ⟨665558, by rfl⟩ : syracuseStep 887411 = 1331117) B1331117
theorem B592499 : Blo 591290 592499 := bstep (se 1 (by rfl) ⟨444374, by rfl⟩ : syracuseStep 592499 = 888749) B888749
theorem B592515 : Blo 591290 592515 := bstep (se 1 (by rfl) ⟨444386, by rfl⟩ : syracuseStep 592515 = 888773) B888773
theorem B887441 : Blo 591290 887441 := bstep (se 2 (by rfl) ⟨332790, by rfl⟩ : syracuseStep 887441 = 665581) B665581
theorem B592531 : Blo 591290 592531 := bstep (se 1 (by rfl) ⟨444398, by rfl⟩ : syracuseStep 592531 = 888797) B888797
theorem B887459 : Blo 591290 887459 := bstep (se 1 (by rfl) ⟨665594, by rfl⟩ : syracuseStep 887459 = 1331189) B1331189
theorem B592547 : Blo 591290 592547 := bstep (se 1 (by rfl) ⟨444410, by rfl⟩ : syracuseStep 592547 = 888821) B888821
theorem B592563 : Blo 591290 592563 := bstep (se 1 (by rfl) ⟨444422, by rfl⟩ : syracuseStep 592563 = 888845) B888845
theorem B887489 : Blo 591290 887489 := bstep (se 2 (by rfl) ⟨332808, by rfl⟩ : syracuseStep 887489 = 665617) B665617
theorem B592579 : Blo 591290 592579 := bstep (se 1 (by rfl) ⟨444434, by rfl⟩ : syracuseStep 592579 = 888869) B888869
theorem B2001617 : Blo 591290 2001617 := bstep (se 2 (by rfl) ⟨750606, by rfl⟩ : syracuseStep 2001617 = 1501213) B1501213
theorem B887507 : Blo 591290 887507 := bstep (se 1 (by rfl) ⟨665630, by rfl⟩ : syracuseStep 887507 = 1331261) B1331261
theorem B592595 : Blo 591290 592595 := bstep (se 1 (by rfl) ⟨444446, by rfl⟩ : syracuseStep 592595 = 888893) B888893
theorem B592611 : Blo 591290 592611 := bstep (se 1 (by rfl) ⟨444458, by rfl⟩ : syracuseStep 592611 = 888917) B888917
theorem B5147363 : Blo 591290 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B887537 : Blo 591290 887537 := bstep (se 2 (by rfl) ⟨332826, by rfl⟩ : syracuseStep 887537 = 665653) B665653
theorem B592627 : Blo 591290 592627 := bstep (se 1 (by rfl) ⟨444470, by rfl⟩ : syracuseStep 592627 = 888941) B888941
theorem B887555 : Blo 591290 887555 := bstep (se 1 (by rfl) ⟨665666, by rfl⟩ : syracuseStep 887555 = 1331333) B1331333
theorem B592643 : Blo 591290 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B592659 : Blo 591290 592659 := bstep (se 1 (by rfl) ⟨444494, by rfl⟩ : syracuseStep 592659 = 888989) B888989
theorem B887585 : Blo 591290 887585 := bstep (se 2 (by rfl) ⟨332844, by rfl⟩ : syracuseStep 887585 = 665689) B665689
theorem B592675 : Blo 591290 592675 := bstep (se 1 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 592675 = 889013) B889013
theorem B1903409 : Blo 591290 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B887603 : Blo 591290 887603 := bstep (se 1 (by rfl) ⟨665702, by rfl⟩ : syracuseStep 887603 = 1331405) B1331405
theorem B592691 : Blo 591290 592691 := bstep (se 1 (by rfl) ⟨444518, by rfl⟩ : syracuseStep 592691 = 889037) B889037
theorem B592707 : Blo 591290 592707 := bstep (se 1 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 592707 = 889061) B889061
theorem B887633 : Blo 591290 887633 := bstep (se 2 (by rfl) ⟨332862, by rfl⟩ : syracuseStep 887633 = 665725) B665725
theorem B592723 : Blo 591290 592723 := bstep (se 1 (by rfl) ⟨444542, by rfl⟩ : syracuseStep 592723 = 889085) B889085
theorem B887651 : Blo 591290 887651 := bstep (se 1 (by rfl) ⟨665738, by rfl⟩ : syracuseStep 887651 = 1331477) B1331477
theorem B592739 : Blo 591290 592739 := bstep (se 1 (by rfl) ⟨444554, by rfl⟩ : syracuseStep 592739 = 889109) B889109
theorem B592755 : Blo 591290 592755 := bstep (se 1 (by rfl) ⟨444566, by rfl⟩ : syracuseStep 592755 = 889133) B889133
theorem B887681 : Blo 591290 887681 := bstep (se 2 (by rfl) ⟨332880, by rfl⟩ : syracuseStep 887681 = 665761) B665761
theorem B592771 : Blo 591290 592771 := bstep (se 1 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 592771 = 889157) B889157
theorem B887699 : Blo 591290 887699 := bstep (se 1 (by rfl) ⟨665774, by rfl⟩ : syracuseStep 887699 = 1331549) B1331549
theorem B592787 : Blo 591290 592787 := bstep (se 1 (by rfl) ⟨444590, by rfl⟩ : syracuseStep 592787 = 889181) B889181
theorem B592803 : Blo 591290 592803 := bstep (se 1 (by rfl) ⟨444602, by rfl⟩ : syracuseStep 592803 = 889205) B889205
theorem B887729 : Blo 591290 887729 := bstep (se 2 (by rfl) ⟨332898, by rfl⟩ : syracuseStep 887729 = 665797) B665797
theorem B592819 : Blo 591290 592819 := bstep (se 1 (by rfl) ⟨444614, by rfl⟩ : syracuseStep 592819 = 889229) B889229
theorem B887747 : Blo 591290 887747 := bstep (se 1 (by rfl) ⟨665810, by rfl⟩ : syracuseStep 887747 = 1331621) B1331621
theorem B592835 : Blo 591290 592835 := bstep (se 1 (by rfl) ⟨444626, by rfl⟩ : syracuseStep 592835 = 889253) B889253
theorem B592851 : Blo 591290 592851 := bstep (se 1 (by rfl) ⟨444638, by rfl⟩ : syracuseStep 592851 = 889277) B889277
theorem B887777 : Blo 591290 887777 := bstep (se 2 (by rfl) ⟨332916, by rfl⟩ : syracuseStep 887777 = 665833) B665833
theorem B592867 : Blo 591290 592867 := bstep (se 1 (by rfl) ⟨444650, by rfl⟩ : syracuseStep 592867 = 889301) B889301
theorem B1903601 : Blo 591290 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B887795 : Blo 591290 887795 := bstep (se 1 (by rfl) ⟨665846, by rfl⟩ : syracuseStep 887795 = 1331693) B1331693
theorem B592883 : Blo 591290 592883 := bstep (se 1 (by rfl) ⟨444662, by rfl⟩ : syracuseStep 592883 = 889325) B889325
theorem B953345 : Blo 591290 953345 := bstep (se 2 (by rfl) ⟨357504, by rfl⟩ : syracuseStep 953345 = 715009) B715009
theorem B592899 : Blo 591290 592899 := bstep (se 1 (by rfl) ⟨444674, by rfl⟩ : syracuseStep 592899 = 889349) B889349
theorem B887825 : Blo 591290 887825 := bstep (se 2 (by rfl) ⟨332934, by rfl⟩ : syracuseStep 887825 = 665869) B665869
theorem B592915 : Blo 591290 592915 := bstep (se 1 (by rfl) ⟨444686, by rfl⟩ : syracuseStep 592915 = 889373) B889373
theorem B887843 : Blo 591290 887843 := bstep (se 1 (by rfl) ⟨665882, by rfl⟩ : syracuseStep 887843 = 1331765) B1331765
theorem B592931 : Blo 591290 592931 := bstep (se 1 (by rfl) ⟨444698, by rfl⟩ : syracuseStep 592931 = 889397) B889397
theorem B592947 : Blo 591290 592947 := bstep (se 1 (by rfl) ⟨444710, by rfl⟩ : syracuseStep 592947 = 889421) B889421
theorem B887873 : Blo 591290 887873 := bstep (se 2 (by rfl) ⟨332952, by rfl⟩ : syracuseStep 887873 = 665905) B665905
theorem B592963 : Blo 591290 592963 := bstep (se 1 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 592963 = 889445) B889445
theorem B887891 : Blo 591290 887891 := bstep (se 1 (by rfl) ⟨665918, by rfl⟩ : syracuseStep 887891 = 1331837) B1331837
theorem B592979 : Blo 591290 592979 := bstep (se 1 (by rfl) ⟨444734, by rfl⟩ : syracuseStep 592979 = 889469) B889469
theorem B592995 : Blo 591290 592995 := bstep (se 1 (by rfl) ⟨444746, by rfl⟩ : syracuseStep 592995 = 889493) B889493
theorem B887921 : Blo 591290 887921 := bstep (se 2 (by rfl) ⟨332970, by rfl⟩ : syracuseStep 887921 = 665941) B665941
theorem B593011 : Blo 591290 593011 := bstep (se 1 (by rfl) ⟨444758, by rfl⟩ : syracuseStep 593011 = 889517) B889517
theorem B953473 : Blo 591290 953473 := bstep (se 2 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 953473 = 715105) B715105
theorem B887939 : Blo 591290 887939 := bstep (se 1 (by rfl) ⟨665954, by rfl⟩ : syracuseStep 887939 = 1331909) B1331909
theorem B593027 : Blo 591290 593027 := bstep (se 1 (by rfl) ⟨444770, by rfl⟩ : syracuseStep 593027 = 889541) B889541
theorem B593043 : Blo 591290 593043 := bstep (se 1 (by rfl) ⟨444782, by rfl⟩ : syracuseStep 593043 = 889565) B889565
theorem B887969 : Blo 591290 887969 := bstep (se 2 (by rfl) ⟨332988, by rfl⟩ : syracuseStep 887969 = 665977) B665977
theorem B593059 : Blo 591290 593059 := bstep (se 1 (by rfl) ⟨444794, by rfl⟩ : syracuseStep 593059 = 889589) B889589
theorem B887987 : Blo 591290 887987 := bstep (se 1 (by rfl) ⟨665990, by rfl⟩ : syracuseStep 887987 = 1331981) B1331981
theorem B593075 : Blo 591290 593075 := bstep (se 1 (by rfl) ⟨444806, by rfl⟩ : syracuseStep 593075 = 889613) B889613
theorem B593091 : Blo 591290 593091 := bstep (se 1 (by rfl) ⟨444818, by rfl⟩ : syracuseStep 593091 = 889637) B889637
theorem B888017 : Blo 591290 888017 := bstep (se 2 (by rfl) ⟨333006, by rfl⟩ : syracuseStep 888017 = 666013) B666013
theorem B593107 : Blo 591290 593107 := bstep (se 1 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 593107 = 889661) B889661
theorem B888035 : Blo 591290 888035 := bstep (se 1 (by rfl) ⟨666026, by rfl⟩ : syracuseStep 888035 = 1332053) B1332053
theorem B593123 : Blo 591290 593123 := bstep (se 1 (by rfl) ⟨444842, by rfl⟩ : syracuseStep 593123 = 889685) B889685
theorem B2002157 : Blo 591290 2002157 := bstep (se 3 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 2002157 = 750809) B750809
theorem B593139 : Blo 591290 593139 := bstep (se 1 (by rfl) ⟨444854, by rfl⟩ : syracuseStep 593139 = 889709) B889709
theorem B888065 : Blo 591290 888065 := bstep (se 2 (by rfl) ⟨333024, by rfl⟩ : syracuseStep 888065 = 666049) B666049
theorem B593155 : Blo 591290 593155 := bstep (se 1 (by rfl) ⟨444866, by rfl⟩ : syracuseStep 593155 = 889733) B889733
theorem B888083 : Blo 591290 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B593171 : Blo 591290 593171 := bstep (se 1 (by rfl) ⟨444878, by rfl⟩ : syracuseStep 593171 = 889757) B889757
theorem B593187 : Blo 591290 593187 := bstep (se 1 (by rfl) ⟨444890, by rfl⟩ : syracuseStep 593187 = 889781) B889781
theorem B2002211 : Blo 591290 2002211 := bstep (se 1 (by rfl) ⟨1501658, by rfl⟩ : syracuseStep 2002211 = 3003317) B3003317
theorem B888113 : Blo 591290 888113 := bstep (se 2 (by rfl) ⟨333042, by rfl⟩ : syracuseStep 888113 = 666085) B666085
theorem B593203 : Blo 591290 593203 := bstep (se 1 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 593203 = 889805) B889805
theorem B888131 : Blo 591290 888131 := bstep (se 1 (by rfl) ⟨666098, by rfl⟩ : syracuseStep 888131 = 1332197) B1332197
theorem B593219 : Blo 591290 593219 := bstep (se 1 (by rfl) ⟨444914, by rfl⟩ : syracuseStep 593219 = 889829) B889829
theorem B593235 : Blo 591290 593235 := bstep (se 1 (by rfl) ⟨444926, by rfl⟩ : syracuseStep 593235 = 889853) B889853
theorem B724307 : Blo 591290 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B888161 : Blo 591290 888161 := bstep (se 2 (by rfl) ⟨333060, by rfl⟩ : syracuseStep 888161 = 666121) B666121
theorem B593251 : Blo 591290 593251 := bstep (se 1 (by rfl) ⟨444938, by rfl⟩ : syracuseStep 593251 = 889877) B889877
theorem B888179 : Blo 591290 888179 := bstep (se 1 (by rfl) ⟨666134, by rfl⟩ : syracuseStep 888179 = 1332269) B1332269
theorem B593267 : Blo 591290 593267 := bstep (se 1 (by rfl) ⟨444950, by rfl⟩ : syracuseStep 593267 = 889901) B889901
theorem B593283 : Blo 591290 593283 := bstep (se 1 (by rfl) ⟨444962, by rfl⟩ : syracuseStep 593283 = 889925) B889925
theorem B888209 : Blo 591290 888209 := bstep (se 2 (by rfl) ⟨333078, by rfl⟩ : syracuseStep 888209 = 666157) B666157
theorem B593299 : Blo 591290 593299 := bstep (se 1 (by rfl) ⟨444974, by rfl⟩ : syracuseStep 593299 = 889949) B889949
theorem B888227 : Blo 591290 888227 := bstep (se 1 (by rfl) ⟨666170, by rfl⟩ : syracuseStep 888227 = 1332341) B1332341
theorem B593315 : Blo 591290 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B593331 : Blo 591290 593331 := bstep (se 1 (by rfl) ⟨444998, by rfl⟩ : syracuseStep 593331 = 889997) B889997
theorem B888257 : Blo 591290 888257 := bstep (se 2 (by rfl) ⟨333096, by rfl⟩ : syracuseStep 888257 = 666193) B666193
theorem B593347 : Blo 591290 593347 := bstep (se 1 (by rfl) ⟨445010, by rfl⟩ : syracuseStep 593347 = 890021) B890021
theorem B16289221 : Blo 591290 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B888275 : Blo 591290 888275 := bstep (se 1 (by rfl) ⟨666206, by rfl⟩ : syracuseStep 888275 = 1332413) B1332413
theorem B593363 : Blo 591290 593363 := bstep (se 1 (by rfl) ⟨445022, by rfl⟩ : syracuseStep 593363 = 890045) B890045
theorem B593379 : Blo 591290 593379 := bstep (se 1 (by rfl) ⟨445034, by rfl⟩ : syracuseStep 593379 = 890069) B890069
theorem B888305 : Blo 591290 888305 := bstep (se 2 (by rfl) ⟨333114, by rfl⟩ : syracuseStep 888305 = 666229) B666229
theorem B2854385 : Blo 591290 2854385 := bstep (se 2 (by rfl) ⟨1070394, by rfl⟩ : syracuseStep 2854385 = 2140789) B2140789
theorem B593395 : Blo 591290 593395 := bstep (se 1 (by rfl) ⟨445046, by rfl⟩ : syracuseStep 593395 = 890093) B890093
theorem B888323 : Blo 591290 888323 := bstep (se 1 (by rfl) ⟨666242, by rfl⟩ : syracuseStep 888323 = 1332485) B1332485
theorem B593411 : Blo 591290 593411 := bstep (se 1 (by rfl) ⟨445058, by rfl⟩ : syracuseStep 593411 = 890117) B890117
theorem B593427 : Blo 591290 593427 := bstep (se 1 (by rfl) ⟨445070, by rfl⟩ : syracuseStep 593427 = 890141) B890141
theorem B888353 : Blo 591290 888353 := bstep (se 2 (by rfl) ⟨333132, by rfl⟩ : syracuseStep 888353 = 666265) B666265
theorem B593443 : Blo 591290 593443 := bstep (se 1 (by rfl) ⟨445082, by rfl⟩ : syracuseStep 593443 = 890165) B890165
theorem B2002481 : Blo 591290 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B888371 : Blo 591290 888371 := bstep (se 1 (by rfl) ⟨666278, by rfl⟩ : syracuseStep 888371 = 1332557) B1332557
theorem B593459 : Blo 591290 593459 := bstep (se 1 (by rfl) ⟨445094, by rfl⟩ : syracuseStep 593459 = 890189) B890189
theorem B593475 : Blo 591290 593475 := bstep (se 1 (by rfl) ⟨445106, by rfl⟩ : syracuseStep 593475 = 890213) B890213
theorem B888401 : Blo 591290 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B593491 : Blo 591290 593491 := bstep (se 1 (by rfl) ⟨445118, by rfl⟩ : syracuseStep 593491 = 890237) B890237
theorem B888419 : Blo 591290 888419 := bstep (se 1 (by rfl) ⟨666314, by rfl⟩ : syracuseStep 888419 = 1332629) B1332629
theorem B593507 : Blo 591290 593507 := bstep (se 1 (by rfl) ⟨445130, by rfl⟩ : syracuseStep 593507 = 890261) B890261
theorem B593523 : Blo 591290 593523 := bstep (se 1 (by rfl) ⟨445142, by rfl⟩ : syracuseStep 593523 = 890285) B890285
theorem B888449 : Blo 591290 888449 := bstep (se 2 (by rfl) ⟨333168, by rfl⟩ : syracuseStep 888449 = 666337) B666337
theorem B593539 : Blo 591290 593539 := bstep (se 1 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 593539 = 890309) B890309
theorem B888467 : Blo 591290 888467 := bstep (se 1 (by rfl) ⟨666350, by rfl⟩ : syracuseStep 888467 = 1332701) B1332701
theorem B593555 : Blo 591290 593555 := bstep (se 1 (by rfl) ⟨445166, by rfl⟩ : syracuseStep 593555 = 890333) B890333
theorem B593571 : Blo 591290 593571 := bstep (se 1 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 593571 = 890357) B890357
theorem B888497 : Blo 591290 888497 := bstep (se 2 (by rfl) ⟨333186, by rfl⟩ : syracuseStep 888497 = 666373) B666373
theorem B593587 : Blo 591290 593587 := bstep (se 1 (by rfl) ⟨445190, by rfl⟩ : syracuseStep 593587 = 890381) B890381
theorem B888515 : Blo 591290 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B593603 : Blo 591290 593603 := bstep (se 1 (by rfl) ⟨445202, by rfl⟩ : syracuseStep 593603 = 890405) B890405
theorem B593619 : Blo 591290 593619 := bstep (se 1 (by rfl) ⟨445214, by rfl⟩ : syracuseStep 593619 = 890429) B890429
theorem B888545 : Blo 591290 888545 := bstep (se 2 (by rfl) ⟨333204, by rfl⟩ : syracuseStep 888545 = 666409) B666409
theorem B593635 : Blo 591290 593635 := bstep (se 1 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 593635 = 890453) B890453
theorem B888563 : Blo 591290 888563 := bstep (se 1 (by rfl) ⟨666422, by rfl⟩ : syracuseStep 888563 = 1332845) B1332845
theorem B593651 : Blo 591290 593651 := bstep (se 1 (by rfl) ⟨445238, by rfl⟩ : syracuseStep 593651 = 890477) B890477
theorem B593667 : Blo 591290 593667 := bstep (se 1 (by rfl) ⟨445250, by rfl⟩ : syracuseStep 593667 = 890501) B890501
theorem B4493069 : Blo 591290 4493069 := bstep (se 3 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 4493069 = 1684901) B1684901
theorem B888593 : Blo 591290 888593 := bstep (se 2 (by rfl) ⟨333222, by rfl⟩ : syracuseStep 888593 = 666445) B666445
theorem B593683 : Blo 591290 593683 := bstep (se 1 (by rfl) ⟨445262, by rfl⟩ : syracuseStep 593683 = 890525) B890525
theorem B888611 : Blo 591290 888611 := bstep (se 1 (by rfl) ⟨666458, by rfl⟩ : syracuseStep 888611 = 1332917) B1332917
theorem B593699 : Blo 591290 593699 := bstep (se 1 (by rfl) ⟨445274, by rfl⟩ : syracuseStep 593699 = 890549) B890549
theorem B593715 : Blo 591290 593715 := bstep (se 1 (by rfl) ⟨445286, by rfl⟩ : syracuseStep 593715 = 890573) B890573
theorem B888641 : Blo 591290 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B593731 : Blo 591290 593731 := bstep (se 1 (by rfl) ⟨445298, by rfl⟩ : syracuseStep 593731 = 890597) B890597
theorem B888659 : Blo 591290 888659 := bstep (se 1 (by rfl) ⟨666494, by rfl⟩ : syracuseStep 888659 = 1332989) B1332989
theorem B593747 : Blo 591290 593747 := bstep (se 1 (by rfl) ⟨445310, by rfl⟩ : syracuseStep 593747 = 890621) B890621
theorem B593763 : Blo 591290 593763 := bstep (se 1 (by rfl) ⟨445322, by rfl⟩ : syracuseStep 593763 = 890645) B890645
theorem B888689 : Blo 591290 888689 := bstep (se 2 (by rfl) ⟨333258, by rfl⟩ : syracuseStep 888689 = 666517) B666517
theorem B593779 : Blo 591290 593779 := bstep (se 1 (by rfl) ⟨445334, by rfl⟩ : syracuseStep 593779 = 890669) B890669
theorem B888707 : Blo 591290 888707 := bstep (se 1 (by rfl) ⟨666530, by rfl⟩ : syracuseStep 888707 = 1333061) B1333061
theorem B593795 : Blo 591290 593795 := bstep (se 1 (by rfl) ⟨445346, by rfl⟩ : syracuseStep 593795 = 890693) B890693
theorem B1085329 : Blo 591290 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B593811 : Blo 591290 593811 := bstep (se 1 (by rfl) ⟨445358, by rfl⟩ : syracuseStep 593811 = 890717) B890717
theorem B888737 : Blo 591290 888737 := bstep (se 2 (by rfl) ⟨333276, by rfl⟩ : syracuseStep 888737 = 666553) B666553
theorem B593827 : Blo 591290 593827 := bstep (se 1 (by rfl) ⟨445370, by rfl⟩ : syracuseStep 593827 = 890741) B890741
theorem B888755 : Blo 591290 888755 := bstep (se 1 (by rfl) ⟨666566, by rfl⟩ : syracuseStep 888755 = 1333133) B1333133
theorem B593843 : Blo 591290 593843 := bstep (se 1 (by rfl) ⟨445382, by rfl⟩ : syracuseStep 593843 = 890765) B890765
theorem B593859 : Blo 591290 593859 := bstep (se 1 (by rfl) ⟨445394, by rfl⟩ : syracuseStep 593859 = 890789) B890789
theorem B888785 : Blo 591290 888785 := bstep (se 2 (by rfl) ⟨333294, by rfl⟩ : syracuseStep 888785 = 666589) B666589
theorem B593875 : Blo 591290 593875 := bstep (se 1 (by rfl) ⟨445406, by rfl⟩ : syracuseStep 593875 = 890813) B890813
theorem B888803 : Blo 591290 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B593891 : Blo 591290 593891 := bstep (se 1 (by rfl) ⟨445418, by rfl⟩ : syracuseStep 593891 = 890837) B890837
theorem B593907 : Blo 591290 593907 := bstep (se 1 (by rfl) ⟨445430, by rfl⟩ : syracuseStep 593907 = 890861) B890861
theorem B888833 : Blo 591290 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B593923 : Blo 591290 593923 := bstep (se 1 (by rfl) ⟨445442, by rfl⟩ : syracuseStep 593923 = 890885) B890885
theorem B888851 : Blo 591290 888851 := bstep (se 1 (by rfl) ⟨666638, by rfl⟩ : syracuseStep 888851 = 1333277) B1333277
theorem B593939 : Blo 591290 593939 := bstep (se 1 (by rfl) ⟨445454, by rfl⟩ : syracuseStep 593939 = 890909) B890909
theorem B593955 : Blo 591290 593955 := bstep (se 1 (by rfl) ⟨445466, by rfl⟩ : syracuseStep 593955 = 890933) B890933
theorem B888881 : Blo 591290 888881 := bstep (se 2 (by rfl) ⟨333330, by rfl⟩ : syracuseStep 888881 = 666661) B666661
theorem B593971 : Blo 591290 593971 := bstep (se 1 (by rfl) ⟨445478, by rfl⟩ : syracuseStep 593971 = 890957) B890957
theorem B888899 : Blo 591290 888899 := bstep (se 1 (by rfl) ⟨666674, by rfl⟩ : syracuseStep 888899 = 1333349) B1333349
theorem B593987 : Blo 591290 593987 := bstep (se 1 (by rfl) ⟨445490, by rfl⟩ : syracuseStep 593987 = 890981) B890981
theorem B2003021 : Blo 591290 2003021 := bstep (se 3 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 2003021 = 751133) B751133
theorem B594003 : Blo 591290 594003 := bstep (se 1 (by rfl) ⟨445502, by rfl⟩ : syracuseStep 594003 = 891005) B891005
theorem B888929 : Blo 591290 888929 := bstep (se 2 (by rfl) ⟨333348, by rfl⟩ : syracuseStep 888929 = 666697) B666697
theorem B594019 : Blo 591290 594019 := bstep (se 1 (by rfl) ⟨445514, by rfl⟩ : syracuseStep 594019 = 891029) B891029
theorem B888947 : Blo 591290 888947 := bstep (se 1 (by rfl) ⟨666710, by rfl⟩ : syracuseStep 888947 = 1333421) B1333421
theorem B594035 : Blo 591290 594035 := bstep (se 1 (by rfl) ⟨445526, by rfl⟩ : syracuseStep 594035 = 891053) B891053
theorem B2003075 : Blo 591290 2003075 := bstep (se 1 (by rfl) ⟨1502306, by rfl⟩ : syracuseStep 2003075 = 3004613) B3004613
theorem B594051 : Blo 591290 594051 := bstep (se 1 (by rfl) ⟨445538, by rfl⟩ : syracuseStep 594051 = 891077) B891077
theorem B888977 : Blo 591290 888977 := bstep (se 2 (by rfl) ⟨333366, by rfl⟩ : syracuseStep 888977 = 666733) B666733
theorem B594067 : Blo 591290 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B888995 : Blo 591290 888995 := bstep (se 1 (by rfl) ⟨666746, by rfl⟩ : syracuseStep 888995 = 1333493) B1333493
theorem B594083 : Blo 591290 594083 := bstep (se 1 (by rfl) ⟨445562, by rfl⟩ : syracuseStep 594083 = 891125) B891125
theorem B594099 : Blo 591290 594099 := bstep (se 1 (by rfl) ⟨445574, by rfl⟩ : syracuseStep 594099 = 891149) B891149
theorem B889025 : Blo 591290 889025 := bstep (se 2 (by rfl) ⟨333384, by rfl⟩ : syracuseStep 889025 = 666769) B666769
theorem B594115 : Blo 591290 594115 := bstep (se 1 (by rfl) ⟨445586, by rfl⟩ : syracuseStep 594115 = 891173) B891173
theorem B889043 : Blo 591290 889043 := bstep (se 1 (by rfl) ⟨666782, by rfl⟩ : syracuseStep 889043 = 1333565) B1333565
theorem B594131 : Blo 591290 594131 := bstep (se 1 (by rfl) ⟨445598, by rfl⟩ : syracuseStep 594131 = 891197) B891197
theorem B594147 : Blo 591290 594147 := bstep (se 1 (by rfl) ⟨445610, by rfl⟩ : syracuseStep 594147 = 891221) B891221
theorem B889073 : Blo 591290 889073 := bstep (se 2 (by rfl) ⟨333402, by rfl⟩ : syracuseStep 889073 = 666805) B666805
theorem B594163 : Blo 591290 594163 := bstep (se 1 (by rfl) ⟨445622, by rfl⟩ : syracuseStep 594163 = 891245) B891245
theorem B889091 : Blo 591290 889091 := bstep (se 1 (by rfl) ⟨666818, by rfl⟩ : syracuseStep 889091 = 1333637) B1333637
theorem B594179 : Blo 591290 594179 := bstep (se 1 (by rfl) ⟨445634, by rfl⟩ : syracuseStep 594179 = 891269) B891269
theorem B594195 : Blo 591290 594195 := bstep (se 1 (by rfl) ⟨445646, by rfl⟩ : syracuseStep 594195 = 891293) B891293
theorem B889121 : Blo 591290 889121 := bstep (se 2 (by rfl) ⟨333420, by rfl⟩ : syracuseStep 889121 = 666841) B666841
theorem B594211 : Blo 591290 594211 := bstep (se 1 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 594211 = 891317) B891317
theorem B889139 : Blo 591290 889139 := bstep (se 1 (by rfl) ⟨666854, by rfl⟩ : syracuseStep 889139 = 1333709) B1333709
theorem B594227 : Blo 591290 594227 := bstep (se 1 (by rfl) ⟨445670, by rfl⟩ : syracuseStep 594227 = 891341) B891341
theorem B594243 : Blo 591290 594243 := bstep (se 1 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 594243 = 891365) B891365
theorem B889169 : Blo 591290 889169 := bstep (se 2 (by rfl) ⟨333438, by rfl⟩ : syracuseStep 889169 = 666877) B666877
theorem B594259 : Blo 591290 594259 := bstep (se 1 (by rfl) ⟨445694, by rfl⟩ : syracuseStep 594259 = 891389) B891389
theorem B889187 : Blo 591290 889187 := bstep (se 1 (by rfl) ⟨666890, by rfl⟩ : syracuseStep 889187 = 1333781) B1333781
theorem B594275 : Blo 591290 594275 := bstep (se 1 (by rfl) ⟨445706, by rfl⟩ : syracuseStep 594275 = 891413) B891413
theorem B1446257 : Blo 591290 1446257 := bstep (se 2 (by rfl) ⟨542346, by rfl⟩ : syracuseStep 1446257 = 1084693) B1084693
theorem B594291 : Blo 591290 594291 := bstep (se 1 (by rfl) ⟨445718, by rfl⟩ : syracuseStep 594291 = 891437) B891437
theorem B889217 : Blo 591290 889217 := bstep (se 2 (by rfl) ⟨333456, by rfl⟩ : syracuseStep 889217 = 666913) B666913
theorem B594307 : Blo 591290 594307 := bstep (se 1 (by rfl) ⟨445730, by rfl⟩ : syracuseStep 594307 = 891461) B891461
theorem B2003345 : Blo 591290 2003345 := bstep (se 2 (by rfl) ⟨751254, by rfl⟩ : syracuseStep 2003345 = 1502509) B1502509
theorem B889235 : Blo 591290 889235 := bstep (se 1 (by rfl) ⟨666926, by rfl⟩ : syracuseStep 889235 = 1333853) B1333853
theorem B594323 : Blo 591290 594323 := bstep (se 1 (by rfl) ⟨445742, by rfl⟩ : syracuseStep 594323 = 891485) B891485
theorem B594339 : Blo 591290 594339 := bstep (se 1 (by rfl) ⟨445754, by rfl⟩ : syracuseStep 594339 = 891509) B891509
theorem B889265 : Blo 591290 889265 := bstep (se 2 (by rfl) ⟨333474, by rfl⟩ : syracuseStep 889265 = 666949) B666949
theorem B594355 : Blo 591290 594355 := bstep (se 1 (by rfl) ⟨445766, by rfl⟩ : syracuseStep 594355 = 891533) B891533
theorem B889283 : Blo 591290 889283 := bstep (se 1 (by rfl) ⟨666962, by rfl⟩ : syracuseStep 889283 = 1333925) B1333925
theorem B594371 : Blo 591290 594371 := bstep (se 1 (by rfl) ⟨445778, by rfl⟩ : syracuseStep 594371 = 891557) B891557
theorem B594387 : Blo 591290 594387 := bstep (se 1 (by rfl) ⟨445790, by rfl⟩ : syracuseStep 594387 = 891581) B891581
theorem B889313 : Blo 591290 889313 := bstep (se 2 (by rfl) ⟨333492, by rfl⟩ : syracuseStep 889313 = 666985) B666985
theorem B594403 : Blo 591290 594403 := bstep (se 1 (by rfl) ⟨445802, by rfl⟩ : syracuseStep 594403 = 891605) B891605
theorem B889331 : Blo 591290 889331 := bstep (se 1 (by rfl) ⟨666998, by rfl⟩ : syracuseStep 889331 = 1333997) B1333997
theorem B594419 : Blo 591290 594419 := bstep (se 1 (by rfl) ⟨445814, by rfl⟩ : syracuseStep 594419 = 891629) B891629
theorem B594435 : Blo 591290 594435 := bstep (se 1 (by rfl) ⟨445826, by rfl⟩ : syracuseStep 594435 = 891653) B891653
theorem B889361 : Blo 591290 889361 := bstep (se 2 (by rfl) ⟨333510, by rfl⟩ : syracuseStep 889361 = 667021) B667021
theorem B594451 : Blo 591290 594451 := bstep (se 1 (by rfl) ⟨445838, by rfl⟩ : syracuseStep 594451 = 891677) B891677
theorem B889379 : Blo 591290 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B594467 : Blo 591290 594467 := bstep (se 1 (by rfl) ⟨445850, by rfl⟩ : syracuseStep 594467 = 891701) B891701
theorem B594483 : Blo 591290 594483 := bstep (se 1 (by rfl) ⟨445862, by rfl⟩ : syracuseStep 594483 = 891725) B891725
theorem B889409 : Blo 591290 889409 := bstep (se 2 (by rfl) ⟨333528, by rfl⟩ : syracuseStep 889409 = 667057) B667057
theorem B594499 : Blo 591290 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B889427 : Blo 591290 889427 := bstep (se 1 (by rfl) ⟨667070, by rfl⟩ : syracuseStep 889427 = 1334141) B1334141
theorem B594515 : Blo 591290 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B594531 : Blo 591290 594531 := bstep (se 1 (by rfl) ⟨445898, by rfl⟩ : syracuseStep 594531 = 891797) B891797
theorem B889457 : Blo 591290 889457 := bstep (se 2 (by rfl) ⟨333546, by rfl⟩ : syracuseStep 889457 = 667093) B667093
theorem B594547 : Blo 591290 594547 := bstep (se 1 (by rfl) ⟨445910, by rfl⟩ : syracuseStep 594547 = 891821) B891821
theorem B889475 : Blo 591290 889475 := bstep (se 1 (by rfl) ⟨667106, by rfl⟩ : syracuseStep 889475 = 1334213) B1334213
theorem B594563 : Blo 591290 594563 := bstep (se 1 (by rfl) ⟨445922, by rfl⟩ : syracuseStep 594563 = 891845) B891845
theorem B594579 : Blo 591290 594579 := bstep (se 1 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 594579 = 891869) B891869
theorem B889505 : Blo 591290 889505 := bstep (se 2 (by rfl) ⟨333564, by rfl⟩ : syracuseStep 889505 = 667129) B667129
theorem B594595 : Blo 591290 594595 := bstep (se 1 (by rfl) ⟨445946, by rfl⟩ : syracuseStep 594595 = 891893) B891893
theorem B889523 : Blo 591290 889523 := bstep (se 1 (by rfl) ⟨667142, by rfl⟩ : syracuseStep 889523 = 1334285) B1334285
theorem B594611 : Blo 591290 594611 := bstep (se 1 (by rfl) ⟨445958, by rfl⟩ : syracuseStep 594611 = 891917) B891917
theorem B1807043 : Blo 591290 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B594627 : Blo 591290 594627 := bstep (se 1 (by rfl) ⟨445970, by rfl⟩ : syracuseStep 594627 = 891941) B891941
theorem B889553 : Blo 591290 889553 := bstep (se 2 (by rfl) ⟨333582, by rfl⟩ : syracuseStep 889553 = 667165) B667165
theorem B594643 : Blo 591290 594643 := bstep (se 1 (by rfl) ⟨445982, by rfl⟩ : syracuseStep 594643 = 891965) B891965
theorem B889571 : Blo 591290 889571 := bstep (se 1 (by rfl) ⟨667178, by rfl⟩ : syracuseStep 889571 = 1334357) B1334357
theorem B594659 : Blo 591290 594659 := bstep (se 1 (by rfl) ⟨445994, by rfl⟩ : syracuseStep 594659 = 891989) B891989
theorem B594675 : Blo 591290 594675 := bstep (se 1 (by rfl) ⟨446006, by rfl⟩ : syracuseStep 594675 = 892013) B892013
theorem B889601 : Blo 591290 889601 := bstep (se 2 (by rfl) ⟨333600, by rfl⟩ : syracuseStep 889601 = 667201) B667201
theorem B594691 : Blo 591290 594691 := bstep (se 1 (by rfl) ⟨446018, by rfl⟩ : syracuseStep 594691 = 892037) B892037
theorem B889619 : Blo 591290 889619 := bstep (se 1 (by rfl) ⟨667214, by rfl⟩ : syracuseStep 889619 = 1334429) B1334429
theorem B594707 : Blo 591290 594707 := bstep (se 1 (by rfl) ⟨446030, by rfl⟩ : syracuseStep 594707 = 892061) B892061
theorem B594723 : Blo 591290 594723 := bstep (se 1 (by rfl) ⟨446042, by rfl⟩ : syracuseStep 594723 = 892085) B892085
theorem B889649 : Blo 591290 889649 := bstep (se 2 (by rfl) ⟨333618, by rfl⟩ : syracuseStep 889649 = 667237) B667237
theorem B594739 : Blo 591290 594739 := bstep (se 1 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 594739 = 892109) B892109
theorem B889667 : Blo 591290 889667 := bstep (se 1 (by rfl) ⟨667250, by rfl⟩ : syracuseStep 889667 = 1334501) B1334501
theorem B594755 : Blo 591290 594755 := bstep (se 1 (by rfl) ⟨446066, by rfl⟩ : syracuseStep 594755 = 892133) B892133
theorem B594771 : Blo 591290 594771 := bstep (se 1 (by rfl) ⟨446078, by rfl⟩ : syracuseStep 594771 = 892157) B892157
theorem B889697 : Blo 591290 889697 := bstep (se 2 (by rfl) ⟨333636, by rfl⟩ : syracuseStep 889697 = 667273) B667273
theorem B594787 : Blo 591290 594787 := bstep (se 1 (by rfl) ⟨446090, by rfl⟩ : syracuseStep 594787 = 892181) B892181
theorem B889715 : Blo 591290 889715 := bstep (se 1 (by rfl) ⟨667286, by rfl⟩ : syracuseStep 889715 = 1334573) B1334573
theorem B594803 : Blo 591290 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B594819 : Blo 591290 594819 := bstep (se 1 (by rfl) ⟨446114, by rfl⟩ : syracuseStep 594819 = 892229) B892229
theorem B889745 : Blo 591290 889745 := bstep (se 2 (by rfl) ⟨333654, by rfl⟩ : syracuseStep 889745 = 667309) B667309
theorem B594835 : Blo 591290 594835 := bstep (se 1 (by rfl) ⟨446126, by rfl⟩ : syracuseStep 594835 = 892253) B892253
theorem B889763 : Blo 591290 889763 := bstep (se 1 (by rfl) ⟨667322, by rfl⟩ : syracuseStep 889763 = 1334645) B1334645
theorem B594851 : Blo 591290 594851 := bstep (se 1 (by rfl) ⟨446138, by rfl⟩ : syracuseStep 594851 = 892277) B892277
theorem B2003885 : Blo 591290 2003885 := bstep (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) B751457
theorem B594867 : Blo 591290 594867 := bstep (se 1 (by rfl) ⟨446150, by rfl⟩ : syracuseStep 594867 = 892301) B892301
theorem B889793 : Blo 591290 889793 := bstep (se 2 (by rfl) ⟨333672, by rfl⟩ : syracuseStep 889793 = 667345) B667345
theorem B594883 : Blo 591290 594883 := bstep (se 1 (by rfl) ⟨446162, by rfl⟩ : syracuseStep 594883 = 892325) B892325
theorem B889811 : Blo 591290 889811 := bstep (se 1 (by rfl) ⟨667358, by rfl⟩ : syracuseStep 889811 = 1334717) B1334717
theorem B594899 : Blo 591290 594899 := bstep (se 1 (by rfl) ⟨446174, by rfl⟩ : syracuseStep 594899 = 892349) B892349
theorem B2003939 : Blo 591290 2003939 := bstep (se 1 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 2003939 = 3005909) B3005909
theorem B594915 : Blo 591290 594915 := bstep (se 1 (by rfl) ⟨446186, by rfl⟩ : syracuseStep 594915 = 892373) B892373
theorem B889841 : Blo 591290 889841 := bstep (se 2 (by rfl) ⟨333690, by rfl⟩ : syracuseStep 889841 = 667381) B667381
theorem B594931 : Blo 591290 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B889859 : Blo 591290 889859 := bstep (se 1 (by rfl) ⟨667394, by rfl⟩ : syracuseStep 889859 = 1334789) B1334789
theorem B594947 : Blo 591290 594947 := bstep (se 1 (by rfl) ⟨446210, by rfl⟩ : syracuseStep 594947 = 892421) B892421
theorem B3380237 : Blo 591290 3380237 := bstep (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) B1267589
theorem B594963 : Blo 591290 594963 := bstep (se 1 (by rfl) ⟨446222, by rfl⟩ : syracuseStep 594963 = 892445) B892445
theorem B889889 : Blo 591290 889889 := bstep (se 2 (by rfl) ⟨333708, by rfl⟩ : syracuseStep 889889 = 667417) B667417
theorem B1348643 : Blo 591290 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B594979 : Blo 591290 594979 := bstep (se 1 (by rfl) ⟨446234, by rfl⟩ : syracuseStep 594979 = 892469) B892469
theorem B889907 : Blo 591290 889907 := bstep (se 1 (by rfl) ⟨667430, by rfl⟩ : syracuseStep 889907 = 1334861) B1334861
theorem B594995 : Blo 591290 594995 := bstep (se 1 (by rfl) ⟨446246, by rfl⟩ : syracuseStep 594995 = 892493) B892493
theorem B595011 : Blo 591290 595011 := bstep (se 1 (by rfl) ⟨446258, by rfl⟩ : syracuseStep 595011 = 892517) B892517
theorem B889937 : Blo 591290 889937 := bstep (se 2 (by rfl) ⟨333726, by rfl⟩ : syracuseStep 889937 = 667453) B667453
theorem B595027 : Blo 591290 595027 := bstep (se 1 (by rfl) ⟨446270, by rfl⟩ : syracuseStep 595027 = 892541) B892541
theorem B889955 : Blo 591290 889955 := bstep (se 1 (by rfl) ⟨667466, by rfl⟩ : syracuseStep 889955 = 1334933) B1334933
theorem B2856035 : Blo 591290 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B595043 : Blo 591290 595043 := bstep (se 1 (by rfl) ⟨446282, by rfl⟩ : syracuseStep 595043 = 892565) B892565
theorem B595059 : Blo 591290 595059 := bstep (se 1 (by rfl) ⟨446294, by rfl⟩ : syracuseStep 595059 = 892589) B892589
theorem B889985 : Blo 591290 889985 := bstep (se 2 (by rfl) ⟨333744, by rfl⟩ : syracuseStep 889985 = 667489) B667489
theorem B595075 : Blo 591290 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B890003 : Blo 591290 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B595091 : Blo 591290 595091 := bstep (se 1 (by rfl) ⟨446318, by rfl⟩ : syracuseStep 595091 = 892637) B892637
theorem B595107 : Blo 591290 595107 := bstep (se 1 (by rfl) ⟨446330, by rfl⟩ : syracuseStep 595107 = 892661) B892661
theorem B890033 : Blo 591290 890033 := bstep (se 2 (by rfl) ⟨333762, by rfl⟩ : syracuseStep 890033 = 667525) B667525
theorem B595123 : Blo 591290 595123 := bstep (se 1 (by rfl) ⟨446342, by rfl⟩ : syracuseStep 595123 = 892685) B892685
theorem B890051 : Blo 591290 890051 := bstep (se 1 (by rfl) ⟨667538, by rfl⟩ : syracuseStep 890051 = 1335077) B1335077
theorem B595139 : Blo 591290 595139 := bstep (se 1 (by rfl) ⟨446354, by rfl⟩ : syracuseStep 595139 = 892709) B892709
theorem B1905869 : Blo 591290 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B595155 : Blo 591290 595155 := bstep (se 1 (by rfl) ⟨446366, by rfl⟩ : syracuseStep 595155 = 892733) B892733
theorem B890081 : Blo 591290 890081 := bstep (se 2 (by rfl) ⟨333780, by rfl⟩ : syracuseStep 890081 = 667561) B667561
theorem B595171 : Blo 591290 595171 := bstep (se 1 (by rfl) ⟨446378, by rfl⟩ : syracuseStep 595171 = 892757) B892757
theorem B2004209 : Blo 591290 2004209 := bstep (se 2 (by rfl) ⟨751578, by rfl⟩ : syracuseStep 2004209 = 1503157) B1503157
theorem B890099 : Blo 591290 890099 := bstep (se 1 (by rfl) ⟨667574, by rfl⟩ : syracuseStep 890099 = 1335149) B1335149
theorem B595187 : Blo 591290 595187 := bstep (se 1 (by rfl) ⟨446390, by rfl⟩ : syracuseStep 595187 = 892781) B892781
theorem B595203 : Blo 591290 595203 := bstep (se 1 (by rfl) ⟨446402, by rfl⟩ : syracuseStep 595203 = 892805) B892805
theorem B890129 : Blo 591290 890129 := bstep (se 2 (by rfl) ⟨333798, by rfl⟩ : syracuseStep 890129 = 667597) B667597
theorem B595219 : Blo 591290 595219 := bstep (se 1 (by rfl) ⟨446414, by rfl⟩ : syracuseStep 595219 = 892829) B892829
theorem B890147 : Blo 591290 890147 := bstep (se 1 (by rfl) ⟨667610, by rfl⟩ : syracuseStep 890147 = 1335221) B1335221
theorem B595235 : Blo 591290 595235 := bstep (se 1 (by rfl) ⟨446426, by rfl⟩ : syracuseStep 595235 = 892853) B892853
theorem B595251 : Blo 591290 595251 := bstep (se 1 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 595251 = 892877) B892877
theorem B890177 : Blo 591290 890177 := bstep (se 2 (by rfl) ⟨333816, by rfl⟩ : syracuseStep 890177 = 667633) B667633
theorem B595267 : Blo 591290 595267 := bstep (se 1 (by rfl) ⟨446450, by rfl⟩ : syracuseStep 595267 = 892901) B892901
theorem B890195 : Blo 591290 890195 := bstep (se 1 (by rfl) ⟨667646, by rfl⟩ : syracuseStep 890195 = 1335293) B1335293
theorem B595283 : Blo 591290 595283 := bstep (se 1 (by rfl) ⟨446462, by rfl⟩ : syracuseStep 595283 = 892925) B892925
theorem B890225 : Blo 591290 890225 := bstep (se 2 (by rfl) ⟨333834, by rfl⟩ : syracuseStep 890225 = 667669) B667669
theorem B890243 : Blo 591290 890243 := bstep (se 1 (by rfl) ⟨667682, by rfl⟩ : syracuseStep 890243 = 1335365) B1335365
theorem B890273 : Blo 591290 890273 := bstep (se 2 (by rfl) ⟨333852, by rfl⟩ : syracuseStep 890273 = 667705) B667705
theorem B890291 : Blo 591290 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B890321 : Blo 591290 890321 := bstep (se 2 (by rfl) ⟨333870, by rfl⟩ : syracuseStep 890321 = 667741) B667741
theorem B890339 : Blo 591290 890339 := bstep (se 1 (by rfl) ⟨667754, by rfl⟩ : syracuseStep 890339 = 1335509) B1335509
theorem B890369 : Blo 591290 890369 := bstep (se 2 (by rfl) ⟨333888, by rfl⟩ : syracuseStep 890369 = 667777) B667777
theorem B890387 : Blo 591290 890387 := bstep (se 1 (by rfl) ⟨667790, by rfl⟩ : syracuseStep 890387 = 1335581) B1335581
theorem B890417 : Blo 591290 890417 := bstep (se 2 (by rfl) ⟨333906, by rfl⟩ : syracuseStep 890417 = 667813) B667813
theorem B890435 : Blo 591290 890435 := bstep (se 1 (by rfl) ⟨667826, by rfl⟩ : syracuseStep 890435 = 1335653) B1335653
theorem B890465 : Blo 591290 890465 := bstep (se 2 (by rfl) ⟨333924, by rfl⟩ : syracuseStep 890465 = 667849) B667849
theorem B890483 : Blo 591290 890483 := bstep (se 1 (by rfl) ⟨667862, by rfl⟩ : syracuseStep 890483 = 1335725) B1335725
theorem B890513 : Blo 591290 890513 := bstep (se 2 (by rfl) ⟨333942, by rfl⟩ : syracuseStep 890513 = 667885) B667885
theorem B890531 : Blo 591290 890531 := bstep (se 1 (by rfl) ⟨667898, by rfl⟩ : syracuseStep 890531 = 1335797) B1335797
theorem B890561 : Blo 591290 890561 := bstep (se 2 (by rfl) ⟨333960, by rfl⟩ : syracuseStep 890561 = 667921) B667921
theorem B890579 : Blo 591290 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B890609 : Blo 591290 890609 := bstep (se 2 (by rfl) ⟨333978, by rfl⟩ : syracuseStep 890609 = 667957) B667957
theorem B890627 : Blo 591290 890627 := bstep (se 1 (by rfl) ⟨667970, by rfl⟩ : syracuseStep 890627 = 1335941) B1335941
theorem B2004749 : Blo 591290 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B890657 : Blo 591290 890657 := bstep (se 2 (by rfl) ⟨333996, by rfl⟩ : syracuseStep 890657 = 667993) B667993
theorem B890675 : Blo 591290 890675 := bstep (se 1 (by rfl) ⟨668006, by rfl⟩ : syracuseStep 890675 = 1336013) B1336013
theorem B2004803 : Blo 591290 2004803 := bstep (se 1 (by rfl) ⟨1503602, by rfl⟩ : syracuseStep 2004803 = 3007205) B3007205
theorem B890705 : Blo 591290 890705 := bstep (se 2 (by rfl) ⟨334014, by rfl⟩ : syracuseStep 890705 = 668029) B668029
theorem B890723 : Blo 591290 890723 := bstep (se 1 (by rfl) ⟨668042, by rfl⟩ : syracuseStep 890723 = 1336085) B1336085
theorem B890753 : Blo 591290 890753 := bstep (se 2 (by rfl) ⟨334032, by rfl⟩ : syracuseStep 890753 = 668065) B668065
theorem B890771 : Blo 591290 890771 := bstep (se 1 (by rfl) ⟨668078, by rfl⟩ : syracuseStep 890771 = 1336157) B1336157
theorem B890801 : Blo 591290 890801 := bstep (se 2 (by rfl) ⟨334050, by rfl⟩ : syracuseStep 890801 = 668101) B668101
theorem B890819 : Blo 591290 890819 := bstep (se 1 (by rfl) ⟨668114, by rfl⟩ : syracuseStep 890819 = 1336229) B1336229
theorem B890849 : Blo 591290 890849 := bstep (se 2 (by rfl) ⟨334068, by rfl⟩ : syracuseStep 890849 = 668137) B668137
theorem B2529251 : Blo 591290 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B890867 : Blo 591290 890867 := bstep (se 1 (by rfl) ⟨668150, by rfl⟩ : syracuseStep 890867 = 1336301) B1336301
theorem B890897 : Blo 591290 890897 := bstep (se 2 (by rfl) ⟨334086, by rfl⟩ : syracuseStep 890897 = 668173) B668173
theorem B890915 : Blo 591290 890915 := bstep (se 1 (by rfl) ⟨668186, by rfl⟩ : syracuseStep 890915 = 1336373) B1336373
theorem B890945 : Blo 591290 890945 := bstep (se 2 (by rfl) ⟨334104, by rfl⟩ : syracuseStep 890945 = 668209) B668209
theorem B2005073 : Blo 591290 2005073 := bstep (se 2 (by rfl) ⟨751902, by rfl⟩ : syracuseStep 2005073 = 1503805) B1503805
theorem B890963 : Blo 591290 890963 := bstep (se 1 (by rfl) ⟨668222, by rfl⟩ : syracuseStep 890963 = 1336445) B1336445
theorem B1710193 : Blo 591290 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B890993 : Blo 591290 890993 := bstep (se 2 (by rfl) ⟨334122, by rfl⟩ : syracuseStep 890993 = 668245) B668245
theorem B891011 : Blo 591290 891011 := bstep (se 1 (by rfl) ⟨668258, by rfl⟩ : syracuseStep 891011 = 1336517) B1336517
theorem B2398349 : Blo 591290 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B891041 : Blo 591290 891041 := bstep (se 2 (by rfl) ⟨334140, by rfl⟩ : syracuseStep 891041 = 668281) B668281
theorem B891059 : Blo 591290 891059 := bstep (se 1 (by rfl) ⟨668294, by rfl⟩ : syracuseStep 891059 = 1336589) B1336589
theorem B891089 : Blo 591290 891089 := bstep (se 2 (by rfl) ⟨334158, by rfl⟩ : syracuseStep 891089 = 668317) B668317
theorem B891107 : Blo 591290 891107 := bstep (se 1 (by rfl) ⟨668330, by rfl⟩ : syracuseStep 891107 = 1336661) B1336661
theorem B891137 : Blo 591290 891137 := bstep (se 2 (by rfl) ⟨334176, by rfl⟩ : syracuseStep 891137 = 668353) B668353
theorem B891155 : Blo 591290 891155 := bstep (se 1 (by rfl) ⟨668366, by rfl⟩ : syracuseStep 891155 = 1336733) B1336733
theorem B891185 : Blo 591290 891185 := bstep (se 2 (by rfl) ⟨334194, by rfl⟩ : syracuseStep 891185 = 668389) B668389
theorem B2857265 : Blo 591290 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B891203 : Blo 591290 891203 := bstep (se 1 (by rfl) ⟨668402, by rfl⟩ : syracuseStep 891203 = 1336805) B1336805
theorem B891233 : Blo 591290 891233 := bstep (se 2 (by rfl) ⟨334212, by rfl⟩ : syracuseStep 891233 = 668425) B668425
theorem B891251 : Blo 591290 891251 := bstep (se 1 (by rfl) ⟨668438, by rfl⟩ : syracuseStep 891251 = 1336877) B1336877
theorem B891281 : Blo 591290 891281 := bstep (se 2 (by rfl) ⟨334230, by rfl⟩ : syracuseStep 891281 = 668461) B668461
theorem B891299 : Blo 591290 891299 := bstep (se 1 (by rfl) ⟨668474, by rfl⟩ : syracuseStep 891299 = 1336949) B1336949
theorem B891329 : Blo 591290 891329 := bstep (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) B668497
theorem B891347 : Blo 591290 891347 := bstep (se 1 (by rfl) ⟨668510, by rfl⟩ : syracuseStep 891347 = 1337021) B1337021
theorem B891377 : Blo 591290 891377 := bstep (se 2 (by rfl) ⟨334266, by rfl⟩ : syracuseStep 891377 = 668533) B668533
theorem B891395 : Blo 591290 891395 := bstep (se 1 (by rfl) ⟨668546, by rfl⟩ : syracuseStep 891395 = 1337093) B1337093
theorem B891425 : Blo 591290 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B891443 : Blo 591290 891443 := bstep (se 1 (by rfl) ⟨668582, by rfl⟩ : syracuseStep 891443 = 1337165) B1337165
theorem B891473 : Blo 591290 891473 := bstep (se 2 (by rfl) ⟨334302, by rfl⟩ : syracuseStep 891473 = 668605) B668605
theorem B891491 : Blo 591290 891491 := bstep (se 1 (by rfl) ⟨668618, by rfl⟩ : syracuseStep 891491 = 1337237) B1337237
theorem B2005613 : Blo 591290 2005613 := bstep (se 3 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 2005613 = 752105) B752105
theorem B4495985 : Blo 591290 4495985 := bstep (se 2 (by rfl) ⟨1685994, by rfl⟩ : syracuseStep 4495985 = 3371989) B3371989
theorem B891521 : Blo 591290 891521 := bstep (se 2 (by rfl) ⟨334320, by rfl⟩ : syracuseStep 891521 = 668641) B668641
theorem B891539 : Blo 591290 891539 := bstep (se 1 (by rfl) ⟨668654, by rfl⟩ : syracuseStep 891539 = 1337309) B1337309
theorem B2005667 : Blo 591290 2005667 := bstep (se 1 (by rfl) ⟨1504250, by rfl⟩ : syracuseStep 2005667 = 3008501) B3008501
theorem B891569 : Blo 591290 891569 := bstep (se 2 (by rfl) ⟨334338, by rfl⟩ : syracuseStep 891569 = 668677) B668677
theorem B891587 : Blo 591290 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B891617 : Blo 591290 891617 := bstep (se 2 (by rfl) ⟨334356, by rfl⟩ : syracuseStep 891617 = 668713) B668713
theorem B891635 : Blo 591290 891635 := bstep (se 1 (by rfl) ⟨668726, by rfl⟩ : syracuseStep 891635 = 1337453) B1337453
theorem B891665 : Blo 591290 891665 := bstep (se 2 (by rfl) ⟨334374, by rfl⟩ : syracuseStep 891665 = 668749) B668749
theorem B891683 : Blo 591290 891683 := bstep (se 1 (by rfl) ⟨668762, by rfl⟩ : syracuseStep 891683 = 1337525) B1337525
theorem B891713 : Blo 591290 891713 := bstep (se 2 (by rfl) ⟨334392, by rfl⟩ : syracuseStep 891713 = 668785) B668785
theorem B891731 : Blo 591290 891731 := bstep (se 1 (by rfl) ⟨668798, by rfl⟩ : syracuseStep 891731 = 1337597) B1337597
theorem B891761 : Blo 591290 891761 := bstep (se 2 (by rfl) ⟨334410, by rfl⟩ : syracuseStep 891761 = 668821) B668821
theorem B891779 : Blo 591290 891779 := bstep (se 1 (by rfl) ⟨668834, by rfl⟩ : syracuseStep 891779 = 1337669) B1337669
theorem B891809 : Blo 591290 891809 := bstep (se 2 (by rfl) ⟨334428, by rfl⟩ : syracuseStep 891809 = 668857) B668857
theorem B2005937 : Blo 591290 2005937 := bstep (se 2 (by rfl) ⟨752226, by rfl⟩ : syracuseStep 2005937 = 1504453) B1504453
theorem B891827 : Blo 591290 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B891857 : Blo 591290 891857 := bstep (se 2 (by rfl) ⟨334446, by rfl⟩ : syracuseStep 891857 = 668893) B668893
theorem B891875 : Blo 591290 891875 := bstep (se 1 (by rfl) ⟨668906, by rfl⟩ : syracuseStep 891875 = 1337813) B1337813
theorem B2169841 : Blo 591290 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B891905 : Blo 591290 891905 := bstep (se 2 (by rfl) ⟨334464, by rfl⟩ : syracuseStep 891905 = 668929) B668929
theorem B891923 : Blo 591290 891923 := bstep (se 1 (by rfl) ⟨668942, by rfl⟩ : syracuseStep 891923 = 1337885) B1337885
theorem B891953 : Blo 591290 891953 := bstep (se 2 (by rfl) ⟨334482, by rfl⟩ : syracuseStep 891953 = 668965) B668965
theorem B891971 : Blo 591290 891971 := bstep (se 1 (by rfl) ⟨668978, by rfl⟩ : syracuseStep 891971 = 1337957) B1337957
theorem B892001 : Blo 591290 892001 := bstep (se 2 (by rfl) ⟨334500, by rfl⟩ : syracuseStep 892001 = 669001) B669001
theorem B892019 : Blo 591290 892019 := bstep (se 1 (by rfl) ⟨669014, by rfl⟩ : syracuseStep 892019 = 1338029) B1338029
theorem B892049 : Blo 591290 892049 := bstep (se 2 (by rfl) ⟨334518, by rfl⟩ : syracuseStep 892049 = 669037) B669037
theorem B892067 : Blo 591290 892067 := bstep (se 1 (by rfl) ⟨669050, by rfl⟩ : syracuseStep 892067 = 1338101) B1338101
theorem B892097 : Blo 591290 892097 := bstep (se 2 (by rfl) ⟨334536, by rfl⟩ : syracuseStep 892097 = 669073) B669073
theorem B8527045 : Blo 591290 8527045 := bstep (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) B1598821
theorem B3382469 : Blo 591290 3382469 := bstep (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) B634213
theorem B892115 : Blo 591290 892115 := bstep (se 1 (by rfl) ⟨669086, by rfl⟩ : syracuseStep 892115 = 1338173) B1338173
theorem B892145 : Blo 591290 892145 := bstep (se 2 (by rfl) ⟨334554, by rfl⟩ : syracuseStep 892145 = 669109) B669109
theorem B892163 : Blo 591290 892163 := bstep (se 1 (by rfl) ⟨669122, by rfl⟩ : syracuseStep 892163 = 1338245) B1338245
theorem B892193 : Blo 591290 892193 := bstep (se 2 (by rfl) ⟨334572, by rfl⟩ : syracuseStep 892193 = 669145) B669145
theorem B892211 : Blo 591290 892211 := bstep (se 1 (by rfl) ⟨669158, by rfl⟩ : syracuseStep 892211 = 1338317) B1338317
theorem B892241 : Blo 591290 892241 := bstep (se 2 (by rfl) ⟨334590, by rfl⟩ : syracuseStep 892241 = 669181) B669181
theorem B892259 : Blo 591290 892259 := bstep (se 1 (by rfl) ⟨669194, by rfl⟩ : syracuseStep 892259 = 1338389) B1338389
theorem B892289 : Blo 591290 892289 := bstep (se 2 (by rfl) ⟨334608, by rfl⟩ : syracuseStep 892289 = 669217) B669217
theorem B892307 : Blo 591290 892307 := bstep (se 1 (by rfl) ⟨669230, by rfl⟩ : syracuseStep 892307 = 1338461) B1338461
theorem B892337 : Blo 591290 892337 := bstep (se 2 (by rfl) ⟨334626, by rfl⟩ : syracuseStep 892337 = 669253) B669253
theorem B892355 : Blo 591290 892355 := bstep (se 1 (by rfl) ⟨669266, by rfl⟩ : syracuseStep 892355 = 1338533) B1338533
theorem B6757829 : Blo 591290 6757829 := bstep (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) B1267093
theorem B2006477 : Blo 591290 2006477 := bstep (se 3 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 2006477 = 752429) B752429
theorem B892385 : Blo 591290 892385 := bstep (se 2 (by rfl) ⟨334644, by rfl⟩ : syracuseStep 892385 = 669289) B669289
theorem B4267505 : Blo 591290 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B892403 : Blo 591290 892403 := bstep (se 1 (by rfl) ⟨669302, by rfl⟩ : syracuseStep 892403 = 1338605) B1338605
theorem B2006531 : Blo 591290 2006531 := bstep (se 1 (by rfl) ⟨1504898, by rfl⟩ : syracuseStep 2006531 = 3009797) B3009797
theorem B892433 : Blo 591290 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B892451 : Blo 591290 892451 := bstep (se 1 (by rfl) ⟨669338, by rfl⟩ : syracuseStep 892451 = 1338677) B1338677
theorem B892481 : Blo 591290 892481 := bstep (se 2 (by rfl) ⟨334680, by rfl⟩ : syracuseStep 892481 = 669361) B669361
theorem B5054021 : Blo 591290 5054021 := bstep (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) B947629
theorem B892499 : Blo 591290 892499 := bstep (se 1 (by rfl) ⟨669374, by rfl⟩ : syracuseStep 892499 = 1338749) B1338749
theorem B761443 : Blo 591290 761443 := bstep (se 1 (by rfl) ⟨571082, by rfl⟩ : syracuseStep 761443 = 1142165) B1142165
theorem B892529 : Blo 591290 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B892547 : Blo 591290 892547 := bstep (se 1 (by rfl) ⟨669410, by rfl⟩ : syracuseStep 892547 = 1338821) B1338821
theorem B892577 : Blo 591290 892577 := bstep (se 2 (by rfl) ⟨334716, by rfl⟩ : syracuseStep 892577 = 669433) B669433
theorem B892595 : Blo 591290 892595 := bstep (se 1 (by rfl) ⟨669446, by rfl⟩ : syracuseStep 892595 = 1338893) B1338893
theorem B892625 : Blo 591290 892625 := bstep (se 2 (by rfl) ⟨334734, by rfl⟩ : syracuseStep 892625 = 669469) B669469
theorem B925409 : Blo 591290 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B892643 : Blo 591290 892643 := bstep (se 1 (by rfl) ⟨669482, by rfl⟩ : syracuseStep 892643 = 1338965) B1338965
theorem B892673 : Blo 591290 892673 := bstep (se 2 (by rfl) ⟨334752, by rfl⟩ : syracuseStep 892673 = 669505) B669505
theorem B2006801 : Blo 591290 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B892691 : Blo 591290 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B892721 : Blo 591290 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B892739 : Blo 591290 892739 := bstep (se 1 (by rfl) ⟨669554, by rfl⟩ : syracuseStep 892739 = 1339109) B1339109
theorem B892769 : Blo 591290 892769 := bstep (se 2 (by rfl) ⟨334788, by rfl⟩ : syracuseStep 892769 = 669577) B669577
theorem B6397795 : Blo 591290 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B3383153 : Blo 591290 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B892787 : Blo 591290 892787 := bstep (se 1 (by rfl) ⟨669590, by rfl⟩ : syracuseStep 892787 = 1339181) B1339181
theorem B892817 : Blo 591290 892817 := bstep (se 2 (by rfl) ⟨334806, by rfl⟩ : syracuseStep 892817 = 669613) B669613
theorem B892835 : Blo 591290 892835 := bstep (se 1 (by rfl) ⟨669626, by rfl⟩ : syracuseStep 892835 = 1339253) B1339253
theorem B2531249 : Blo 591290 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B892865 : Blo 591290 892865 := bstep (se 2 (by rfl) ⟨334824, by rfl⟩ : syracuseStep 892865 = 669649) B669649
theorem B892883 : Blo 591290 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B892913 : Blo 591290 892913 := bstep (se 2 (by rfl) ⟨334842, by rfl⟩ : syracuseStep 892913 = 669685) B669685
theorem B892931 : Blo 591290 892931 := bstep (se 1 (by rfl) ⟨669698, by rfl⟩ : syracuseStep 892931 = 1339397) B1339397
theorem B1712141 : Blo 591290 1712141 := bstep (se 3 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 1712141 = 642053) B642053
theorem B5480561 : Blo 591290 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B2007341 : Blo 591290 2007341 := bstep (se 3 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 2007341 = 752753) B752753
theorem B11411765 : Blo 591290 11411765 := bstep (se 5 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 11411765 = 1069853) B1069853
theorem B2007395 : Blo 591290 2007395 := bstep (se 1 (by rfl) ⟨1505546, by rfl⟩ : syracuseStep 2007395 = 3011093) B3011093
theorem B3809891 : Blo 591290 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B2007665 : Blo 591290 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B1122979 : Blo 591290 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B2859725 : Blo 591290 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B1123139 : Blo 591290 1123139 := bstep (se 1 (by rfl) ⟨842354, by rfl⟩ : syracuseStep 1123139 = 1684709) B1684709
theorem B2008205 : Blo 591290 2008205 := bstep (se 3 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 2008205 = 753077) B753077
theorem B2008259 : Blo 591290 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B3384611 : Blo 591290 3384611 := bstep (se 1 (by rfl) ⟨2538458, by rfl⟩ : syracuseStep 3384611 = 5076917) B5076917
theorem B1287587 : Blo 591290 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B1648081 : Blo 591290 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B2008529 : Blo 591290 2008529 := bstep (se 2 (by rfl) ⟨753198, by rfl⟩ : syracuseStep 2008529 = 1506397) B1506397
theorem B632291 : Blo 591290 632291 := bstep (se 1 (by rfl) ⟨474218, by rfl⟩ : syracuseStep 632291 = 948437) B948437
theorem B3253765 : Blo 591290 3253765 := bstep (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) B610081
theorem B2532941 : Blo 591290 2532941 := bstep (se 3 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 2532941 = 949853) B949853
theorem B665203 : Blo 591290 665203 := bstep (se 1 (by rfl) ⟨498902, by rfl⟩ : syracuseStep 665203 = 997805) B997805
theorem B665347 : Blo 591290 665347 := bstep (se 1 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 665347 = 998021) B998021
theorem B3811121 : Blo 591290 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B1124209 : Blo 591290 1124209 := bstep (se 2 (by rfl) ⟨421578, by rfl⟩ : syracuseStep 1124209 = 843157) B843157
theorem B665491 : Blo 591290 665491 := bstep (se 1 (by rfl) ⟨499118, by rfl⟩ : syracuseStep 665491 = 998237) B998237
theorem B2009069 : Blo 591290 2009069 := bstep (se 3 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 2009069 = 753401) B753401
theorem B665635 : Blo 591290 665635 := bstep (se 1 (by rfl) ⟨499226, by rfl⟩ : syracuseStep 665635 = 998453) B998453
theorem B665779 : Blo 591290 665779 := bstep (se 1 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 665779 = 998669) B998669
theorem B1026227 : Blo 591290 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B633043 : Blo 591290 633043 := bstep (se 1 (by rfl) ⟨474782, by rfl⟩ : syracuseStep 633043 = 949565) B949565
theorem B665923 : Blo 591290 665923 := bstep (se 1 (by rfl) ⟨499442, by rfl⟩ : syracuseStep 665923 = 998885) B998885
theorem B600419 : Blo 591290 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B666067 : Blo 591290 666067 := bstep (se 1 (by rfl) ⟨499550, by rfl⟩ : syracuseStep 666067 = 999101) B999101
theorem B2140643 : Blo 591290 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B6400565 : Blo 591290 6400565 := bstep (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) B600053
theorem B1026641 : Blo 591290 1026641 := bstep (se 2 (by rfl) ⟨384990, by rfl⟩ : syracuseStep 1026641 = 769981) B769981
theorem B666211 : Blo 591290 666211 := bstep (se 1 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 666211 = 999317) B999317
theorem B3418787 : Blo 591290 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B666355 : Blo 591290 666355 := bstep (se 1 (by rfl) ⟨499766, by rfl⟩ : syracuseStep 666355 = 999533) B999533
theorem B666499 : Blo 591290 666499 := bstep (se 1 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 666499 = 999749) B999749
theorem B1125265 : Blo 591290 1125265 := bstep (se 2 (by rfl) ⟨421974, by rfl⟩ : syracuseStep 1125265 = 843949) B843949
theorem B666643 : Blo 591290 666643 := bstep (se 1 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 666643 = 999965) B999965
theorem B666787 : Blo 591290 666787 := bstep (se 1 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 666787 = 1000181) B1000181
theorem B1125667 : Blo 591290 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B666931 : Blo 591290 666931 := bstep (se 1 (by rfl) ⟨500198, by rfl⟩ : syracuseStep 666931 = 1000397) B1000397
theorem B1125713 : Blo 591290 1125713 := bstep (se 2 (by rfl) ⟨422142, by rfl⟩ : syracuseStep 1125713 = 844285) B844285
theorem B7613837 : Blo 591290 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B667075 : Blo 591290 667075 := bstep (se 1 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 667075 = 1000613) B1000613
theorem B1715651 : Blo 591290 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1420753 : Blo 591290 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B634435 : Blo 591290 634435 := bstep (se 1 (by rfl) ⟨475826, by rfl⟩ : syracuseStep 634435 = 951653) B951653
theorem B667219 : Blo 591290 667219 := bstep (se 1 (by rfl) ⟨500414, by rfl⟩ : syracuseStep 667219 = 1000829) B1000829
theorem B1126001 : Blo 591290 1126001 := bstep (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) B844501
theorem B667363 : Blo 591290 667363 := bstep (se 1 (by rfl) ⟨500522, by rfl⟩ : syracuseStep 667363 = 1001045) B1001045
theorem B2699021 : Blo 591290 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B4796273 : Blo 591290 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B667507 : Blo 591290 667507 := bstep (se 1 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 667507 = 1001261) B1001261
theorem B2994083 : Blo 591290 2994083 := bstep (se 1 (by rfl) ⟨2245562, by rfl⟩ : syracuseStep 2994083 = 4491125) B4491125
theorem B667651 : Blo 591290 667651 := bstep (se 1 (by rfl) ⟨500738, by rfl⟩ : syracuseStep 667651 = 1001477) B1001477
theorem B1421425 : Blo 591290 1421425 := bstep (se 2 (by rfl) ⟨533034, by rfl⟩ : syracuseStep 1421425 = 1066069) B1066069
theorem B667795 : Blo 591290 667795 := bstep (se 1 (by rfl) ⟨500846, by rfl⟩ : syracuseStep 667795 = 1001693) B1001693
theorem B3813581 : Blo 591290 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B667939 : Blo 591290 667939 := bstep (se 1 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 667939 = 1001909) B1001909
theorem B8106293 : Blo 591290 8106293 := bstep (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) B759965
theorem B1126723 : Blo 591290 1126723 := bstep (se 1 (by rfl) ⟨845042, by rfl⟩ : syracuseStep 1126723 = 1690085) B1690085
theorem B2404721 : Blo 591290 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B668083 : Blo 591290 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B3387845 : Blo 591290 3387845 := bstep (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) B635221
theorem B1028627 : Blo 591290 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B668227 : Blo 591290 668227 := bstep (se 1 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 668227 = 1002341) B1002341
theorem B2142833 : Blo 591290 2142833 := bstep (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) B1607125
theorem B1684081 : Blo 591290 1684081 := bstep (se 2 (by rfl) ⟨631530, by rfl⟩ : syracuseStep 1684081 = 1263061) B1263061
theorem B2994893 : Blo 591290 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B668371 : Blo 591290 668371 := bstep (se 1 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 668371 = 1002557) B1002557
theorem B1127171 : Blo 591290 1127171 := bstep (se 1 (by rfl) ⟨845378, by rfl⟩ : syracuseStep 1127171 = 1690757) B1690757
theorem B668515 : Blo 591290 668515 := bstep (se 1 (by rfl) ⟨501386, by rfl⟩ : syracuseStep 668515 = 1002773) B1002773
theorem B3388301 : Blo 591290 3388301 := bstep (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) B1270613
theorem B668659 : Blo 591290 668659 := bstep (se 1 (by rfl) ⟨501494, by rfl⟩ : syracuseStep 668659 = 1002989) B1002989
theorem B1127459 : Blo 591290 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B668803 : Blo 591290 668803 := bstep (se 1 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 668803 = 1003205) B1003205
theorem B6763661 : Blo 591290 6763661 := bstep (se 3 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 6763661 = 2536373) B2536373
theorem B1717393 : Blo 591290 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B1717453 : Blo 591290 1717453 := bstep (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) B644045
theorem B668947 : Blo 591290 668947 := bstep (se 1 (by rfl) ⟨501710, by rfl⟩ : syracuseStep 668947 = 1003421) B1003421
theorem B5715299 : Blo 591290 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B669091 : Blo 591290 669091 := bstep (se 1 (by rfl) ⟨501818, by rfl⟩ : syracuseStep 669091 = 1003637) B1003637
theorem B669235 : Blo 591290 669235 := bstep (se 1 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 669235 = 1003853) B1003853
theorem B669379 : Blo 591290 669379 := bstep (se 1 (by rfl) ⟨502034, by rfl⟩ : syracuseStep 669379 = 1004069) B1004069
theorem B669523 : Blo 591290 669523 := bstep (se 1 (by rfl) ⟨502142, by rfl⟩ : syracuseStep 669523 = 1004285) B1004285
theorem B2537315 : Blo 591290 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B1685357 : Blo 591290 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B1128401 : Blo 591290 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B669667 : Blo 591290 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B1685539 : Blo 591290 1685539 := bstep (se 1 (by rfl) ⟨1264154, by rfl⟩ : syracuseStep 1685539 = 2528309) B2528309
theorem B2144333 : Blo 591290 2144333 := bstep (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) B804125
theorem B1685585 : Blo 591290 1685585 := bstep (se 2 (by rfl) ⟨632094, by rfl⟩ : syracuseStep 1685585 = 1264189) B1264189
theorem B1620109 : Blo 591290 1620109 := bstep (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) B607541
theorem B2406797 : Blo 591290 2406797 := bstep (se 3 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 2406797 = 902549) B902549
theorem B997825 : Blo 591290 997825 := bstep (se 2 (by rfl) ⟨374184, by rfl⟩ : syracuseStep 997825 = 748369) B748369
theorem B997859 : Blo 591290 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B997987 : Blo 591290 997987 := bstep (se 1 (by rfl) ⟨748490, by rfl⟩ : syracuseStep 997987 = 1496981) B1496981
theorem B4274801 : Blo 591290 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B998129 : Blo 591290 998129 := bstep (se 2 (by rfl) ⟨374298, by rfl⟩ : syracuseStep 998129 = 748597) B748597
theorem B1129297 : Blo 591290 1129297 := bstep (se 2 (by rfl) ⟨423486, by rfl⟩ : syracuseStep 1129297 = 846973) B846973
theorem B998257 : Blo 591290 998257 := bstep (se 2 (by rfl) ⟨374346, by rfl⟩ : syracuseStep 998257 = 748693) B748693
theorem B998291 : Blo 591290 998291 := bstep (se 1 (by rfl) ⟨748718, by rfl⟩ : syracuseStep 998291 = 1497437) B1497437
theorem B900019 : Blo 591290 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B1129457 : Blo 591290 1129457 := bstep (se 2 (by rfl) ⟨423546, by rfl⟩ : syracuseStep 1129457 = 847093) B847093
theorem B998419 : Blo 591290 998419 := bstep (se 1 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 998419 = 1497629) B1497629
theorem B998561 : Blo 591290 998561 := bstep (se 2 (by rfl) ⟨374460, by rfl⟩ : syracuseStep 998561 = 748921) B748921
theorem B998689 : Blo 591290 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B998723 : Blo 591290 998723 := bstep (se 1 (by rfl) ⟨749042, by rfl⟩ : syracuseStep 998723 = 1498085) B1498085
theorem B1129859 : Blo 591290 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B998851 : Blo 591290 998851 := bstep (se 1 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 998851 = 1498277) B1498277
theorem B5062085 : Blo 591290 5062085 := bstep (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) B949141
theorem B1687043 : Blo 591290 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B2997809 : Blo 591290 2997809 := bstep (se 2 (by rfl) ⟨1124178, by rfl⟩ : syracuseStep 2997809 = 2248357) B2248357
theorem B998993 : Blo 591290 998993 := bstep (se 2 (by rfl) ⟨374622, by rfl⟩ : syracuseStep 998993 = 749245) B749245
theorem B1425059 : Blo 591290 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B999121 : Blo 591290 999121 := bstep (se 2 (by rfl) ⟨374670, by rfl⟩ : syracuseStep 999121 = 749341) B749341
theorem B999155 : Blo 591290 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B5685005 : Blo 591290 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B2539313 : Blo 591290 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B2408291 : Blo 591290 2408291 := bstep (se 1 (by rfl) ⟨1806218, by rfl⟩ : syracuseStep 2408291 = 3612437) B3612437
theorem B999283 : Blo 591290 999283 := bstep (se 1 (by rfl) ⟨749462, by rfl⟩ : syracuseStep 999283 = 1498925) B1498925
theorem B1425347 : Blo 591290 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B30883781 : Blo 591290 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B6766577 : Blo 591290 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B999425 : Blo 591290 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B901187 : Blo 591290 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B5062769 : Blo 591290 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B999553 : Blo 591290 999553 := bstep (se 2 (by rfl) ⟨374832, by rfl⟩ : syracuseStep 999553 = 749665) B749665
theorem B999587 : Blo 591290 999587 := bstep (se 1 (by rfl) ⟨749690, by rfl⟩ : syracuseStep 999587 = 1499381) B1499381
theorem B999715 : Blo 591290 999715 := bstep (se 1 (by rfl) ⟨749786, by rfl⟩ : syracuseStep 999715 = 1499573) B1499573
theorem B999857 : Blo 591290 999857 := bstep (se 2 (by rfl) ⟨374946, by rfl⟩ : syracuseStep 999857 = 749893) B749893
theorem B901649 : Blo 591290 901649 := bstep (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) B676237
theorem B3654179 : Blo 591290 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B999985 : Blo 591290 999985 := bstep (se 2 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 999985 = 749989) B749989
theorem B1000019 : Blo 591290 1000019 := bstep (se 1 (by rfl) ⟨750014, by rfl⟩ : syracuseStep 1000019 = 1500029) B1500029
theorem B15155909 : Blo 591290 15155909 := bstep (se 4 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 15155909 = 2841733) B2841733
theorem B1688273 : Blo 591290 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1000147 : Blo 591290 1000147 := bstep (se 1 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 1000147 = 1500221) B1500221
theorem B1426193 : Blo 591290 1426193 := bstep (se 2 (by rfl) ⟨534822, by rfl⟩ : syracuseStep 1426193 = 1069645) B1069645
theorem B1000289 : Blo 591290 1000289 := bstep (se 2 (by rfl) ⟨375108, by rfl⟩ : syracuseStep 1000289 = 750217) B750217
theorem B7226225 : Blo 591290 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B1000417 : Blo 591290 1000417 := bstep (se 2 (by rfl) ⟨375156, by rfl⟩ : syracuseStep 1000417 = 750313) B750313
theorem B2999267 : Blo 591290 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1000451 : Blo 591290 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B2704433 : Blo 591290 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1426481 : Blo 591290 1426481 := bstep (se 2 (by rfl) ⟨534930, by rfl⟩ : syracuseStep 1426481 = 1069861) B1069861
theorem B2245745 : Blo 591290 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B25937009 : Blo 591290 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B1000579 : Blo 591290 1000579 := bstep (se 1 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 1000579 = 1500869) B1500869
theorem B2278541 : Blo 591290 2278541 := bstep (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) B854453
theorem B1426673 : Blo 591290 1426673 := bstep (se 2 (by rfl) ⟨535002, by rfl⟩ : syracuseStep 1426673 = 1070005) B1070005
theorem B1066243 : Blo 591290 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B1000721 : Blo 591290 1000721 := bstep (se 2 (by rfl) ⟨375270, by rfl⟩ : syracuseStep 1000721 = 750541) B750541
theorem B1000849 : Blo 591290 1000849 := bstep (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) B750637
theorem B1000883 : Blo 591290 1000883 := bstep (se 1 (by rfl) ⟨750662, by rfl⟩ : syracuseStep 1000883 = 1501325) B1501325
theorem B2606627 : Blo 591290 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1001011 : Blo 591290 1001011 := bstep (se 1 (by rfl) ⟨750758, by rfl⟩ : syracuseStep 1001011 = 1501517) B1501517
theorem B1001153 : Blo 591290 1001153 := bstep (se 2 (by rfl) ⟨375432, by rfl⟩ : syracuseStep 1001153 = 750865) B750865
theorem B2246413 : Blo 591290 2246413 := bstep (se 3 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 2246413 = 842405) B842405
theorem B3000077 : Blo 591290 3000077 := bstep (se 3 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 3000077 = 1125029) B1125029
theorem B1001281 : Blo 591290 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B1001315 : Blo 591290 1001315 := bstep (se 1 (by rfl) ⟨750986, by rfl⟩ : syracuseStep 1001315 = 1501973) B1501973
theorem B1001443 : Blo 591290 1001443 := bstep (se 1 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 1001443 = 1502165) B1502165
theorem B1001585 : Blo 591290 1001585 := bstep (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) B751189
theorem B1689731 : Blo 591290 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B1263779 : Blo 591290 1263779 := bstep (se 1 (by rfl) ⟨947834, by rfl⟩ : syracuseStep 1263779 = 1895669) B1895669
theorem B1427633 : Blo 591290 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B2541773 : Blo 591290 2541773 := bstep (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) B953165
theorem B1001713 : Blo 591290 1001713 := bstep (se 2 (by rfl) ⟨375642, by rfl⟩ : syracuseStep 1001713 = 751285) B751285
theorem B1001747 : Blo 591290 1001747 := bstep (se 1 (by rfl) ⟨751310, by rfl⟩ : syracuseStep 1001747 = 1502621) B1502621
theorem B1001875 : Blo 591290 1001875 := bstep (se 1 (by rfl) ⟨751406, by rfl⟩ : syracuseStep 1001875 = 1502813) B1502813
theorem B1002017 : Blo 591290 1002017 := bstep (se 2 (by rfl) ⟨375756, by rfl⟩ : syracuseStep 1002017 = 751513) B751513
theorem B2247203 : Blo 591290 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B5720645 : Blo 591290 5720645 := bstep (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) B1072621
theorem B1264241 : Blo 591290 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B1002145 : Blo 591290 1002145 := bstep (se 2 (by rfl) ⟨375804, by rfl⟩ : syracuseStep 1002145 = 751609) B751609
theorem B1002179 : Blo 591290 1002179 := bstep (se 1 (by rfl) ⟨751634, by rfl⟩ : syracuseStep 1002179 = 1503269) B1503269
theorem B903955 : Blo 591290 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B1002307 : Blo 591290 1002307 := bstep (se 1 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 1002307 = 1503461) B1503461
theorem B1690541 : Blo 591290 1690541 := bstep (se 3 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 1690541 = 633953) B633953
theorem B3132365 : Blo 591290 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B1002449 : Blo 591290 1002449 := bstep (se 2 (by rfl) ⟨375918, by rfl⟩ : syracuseStep 1002449 = 751837) B751837
theorem B1526737 : Blo 591290 1526737 := bstep (se 2 (by rfl) ⟨572526, by rfl⟩ : syracuseStep 1526737 = 1145053) B1145053
theorem B1002577 : Blo 591290 1002577 := bstep (se 2 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 1002577 = 751933) B751933
theorem B1690733 : Blo 591290 1690733 := bstep (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) B634025
theorem B1002611 : Blo 591290 1002611 := bstep (se 1 (by rfl) ⟨751958, by rfl⟩ : syracuseStep 1002611 = 1503917) B1503917
theorem B2247857 : Blo 591290 2247857 := bstep (se 2 (by rfl) ⟨842946, by rfl⟩ : syracuseStep 2247857 = 1685893) B1685893
theorem B1002739 : Blo 591290 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B8539505 : Blo 591290 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1002881 : Blo 591290 1002881 := bstep (se 2 (by rfl) ⟨376080, by rfl⟩ : syracuseStep 1002881 = 752161) B752161
theorem B1330577 : Blo 591290 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B1330595 : Blo 591290 1330595 := bstep (se 1 (by rfl) ⟨997946, by rfl⟩ : syracuseStep 1330595 = 1995893) B1995893
theorem B1428931 : Blo 591290 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B1003009 : Blo 591290 1003009 := bstep (se 2 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 1003009 = 752257) B752257
theorem B1003043 : Blo 591290 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B4279877 : Blo 591290 4279877 := bstep (se 4 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 4279877 = 802477) B802477
theorem B904787 : Blo 591290 904787 := bstep (se 1 (by rfl) ⟨678590, by rfl⟩ : syracuseStep 904787 = 1357181) B1357181
theorem B2444899 : Blo 591290 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B1003171 : Blo 591290 1003171 := bstep (se 1 (by rfl) ⟨752378, by rfl⟩ : syracuseStep 1003171 = 1504757) B1504757
theorem B1330865 : Blo 591290 1330865 := bstep (se 2 (by rfl) ⟨499074, by rfl⟩ : syracuseStep 1330865 = 998149) B998149
theorem B1330883 : Blo 591290 1330883 := bstep (se 1 (by rfl) ⟨998162, by rfl⟩ : syracuseStep 1330883 = 1996325) B1996325
theorem B12865301 : Blo 591290 12865301 := bstep (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) B603061
theorem B1003313 : Blo 591290 1003313 := bstep (se 2 (by rfl) ⟨376242, by rfl⟩ : syracuseStep 1003313 = 752485) B752485
theorem B1265539 : Blo 591290 1265539 := bstep (se 1 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 1265539 = 1898309) B1898309
theorem B1003441 : Blo 591290 1003441 := bstep (se 2 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 1003441 = 752581) B752581
theorem B1068995 : Blo 591290 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B1331153 : Blo 591290 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B1003475 : Blo 591290 1003475 := bstep (se 1 (by rfl) ⟨752606, by rfl⟩ : syracuseStep 1003475 = 1505213) B1505213
theorem B1331171 : Blo 591290 1331171 := bstep (se 1 (by rfl) ⟨998378, by rfl⟩ : syracuseStep 1331171 = 1996757) B1996757
theorem B1691725 : Blo 591290 1691725 := bstep (se 3 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 1691725 = 634397) B634397
theorem B1003603 : Blo 591290 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B6410339 : Blo 591290 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1265795 : Blo 591290 1265795 := bstep (se 1 (by rfl) ⟨949346, by rfl⟩ : syracuseStep 1265795 = 1898693) B1898693
theorem B1921169 : Blo 591290 1921169 := bstep (se 2 (by rfl) ⟨720438, by rfl⟩ : syracuseStep 1921169 = 1440877) B1440877
theorem B1003745 : Blo 591290 1003745 := bstep (se 2 (by rfl) ⟨376404, by rfl⟩ : syracuseStep 1003745 = 752809) B752809
theorem B1331441 : Blo 591290 1331441 := bstep (se 2 (by rfl) ⟨499290, by rfl⟩ : syracuseStep 1331441 = 998581) B998581
theorem B1331459 : Blo 591290 1331459 := bstep (se 1 (by rfl) ⟨998594, by rfl⟩ : syracuseStep 1331459 = 1997189) B1997189
theorem B1003873 : Blo 591290 1003873 := bstep (se 2 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 1003873 = 752905) B752905
theorem B7590257 : Blo 591290 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B1003907 : Blo 591290 1003907 := bstep (se 1 (by rfl) ⟨752930, by rfl⟩ : syracuseStep 1003907 = 1505861) B1505861
theorem B1004035 : Blo 591290 1004035 := bstep (se 1 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 1004035 = 1506053) B1506053
theorem B1331729 : Blo 591290 1331729 := bstep (se 2 (by rfl) ⟨499398, by rfl⟩ : syracuseStep 1331729 = 998797) B998797
theorem B1331747 : Blo 591290 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1200739 : Blo 591290 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B2249315 : Blo 591290 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B1692269 : Blo 591290 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B2249329 : Blo 591290 2249329 := bstep (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) B1686997
theorem B3002993 : Blo 591290 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B1004177 : Blo 591290 1004177 := bstep (se 2 (by rfl) ⟨376566, by rfl⟩ : syracuseStep 1004177 = 753133) B753133
theorem B1004305 : Blo 591290 1004305 := bstep (se 2 (by rfl) ⟨376614, by rfl⟩ : syracuseStep 1004305 = 753229) B753229
theorem B1332017 : Blo 591290 1332017 := bstep (se 2 (by rfl) ⟨499506, by rfl⟩ : syracuseStep 1332017 = 999013) B999013
theorem B1004339 : Blo 591290 1004339 := bstep (se 1 (by rfl) ⟨753254, by rfl⟩ : syracuseStep 1004339 = 1506509) B1506509
theorem B1332035 : Blo 591290 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B1004467 : Blo 591290 1004467 := bstep (se 1 (by rfl) ⟨753350, by rfl⟩ : syracuseStep 1004467 = 1506701) B1506701
theorem B1332305 : Blo 591290 1332305 := bstep (se 2 (by rfl) ⟨499614, by rfl⟩ : syracuseStep 1332305 = 999229) B999229
theorem B1266769 : Blo 591290 1266769 := bstep (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) B950077
theorem B1332323 : Blo 591290 1332323 := bstep (se 1 (by rfl) ⟨999242, by rfl⟩ : syracuseStep 1332323 = 1998485) B1998485
theorem B1922417 : Blo 591290 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B1332593 : Blo 591290 1332593 := bstep (se 2 (by rfl) ⟨499722, by rfl⟩ : syracuseStep 1332593 = 999445) B999445
theorem B1332611 : Blo 591290 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B7198307 : Blo 591290 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B1332881 : Blo 591290 1332881 := bstep (se 2 (by rfl) ⟨499830, by rfl⟩ : syracuseStep 1332881 = 999661) B999661
theorem B1332899 : Blo 591290 1332899 := bstep (se 1 (by rfl) ⟨999674, by rfl⟩ : syracuseStep 1332899 = 1999349) B1999349
theorem B1267427 : Blo 591290 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B1693457 : Blo 591290 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B677651 : Blo 591290 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B1333169 : Blo 591290 1333169 := bstep (se 2 (by rfl) ⟨499938, by rfl⟩ : syracuseStep 1333169 = 999877) B999877
theorem B1333187 : Blo 591290 1333187 := bstep (se 1 (by rfl) ⟨999890, by rfl⟩ : syracuseStep 1333187 = 1999781) B1999781
theorem B1693649 : Blo 591290 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B2250787 : Blo 591290 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B3004451 : Blo 591290 3004451 := bstep (se 1 (by rfl) ⟨2253338, by rfl⟩ : syracuseStep 3004451 = 4506677) B4506677
theorem B1333457 : Blo 591290 1333457 := bstep (se 2 (by rfl) ⟨500046, by rfl⟩ : syracuseStep 1333457 = 1000093) B1000093
theorem B1333475 : Blo 591290 1333475 := bstep (se 1 (by rfl) ⟨1000106, by rfl⟩ : syracuseStep 1333475 = 2000213) B2000213
theorem B8673733 : Blo 591290 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B1333745 : Blo 591290 1333745 := bstep (se 2 (by rfl) ⟨500154, by rfl⟩ : syracuseStep 1333745 = 1000309) B1000309
theorem B1333763 : Blo 591290 1333763 := bstep (se 1 (by rfl) ⟨1000322, by rfl⟩ : syracuseStep 1333763 = 2000645) B2000645
theorem B3037709 : Blo 591290 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B1497649 : Blo 591290 1497649 := bstep (se 2 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 1497649 = 1123237) B1123237
theorem B1268273 : Blo 591290 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B4381253 : Blo 591290 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B711299 : Blo 591290 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B7592717 : Blo 591290 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B1334033 : Blo 591290 1334033 := bstep (se 2 (by rfl) ⟨500262, by rfl⟩ : syracuseStep 1334033 = 1000525) B1000525
theorem B1334051 : Blo 591290 1334051 := bstep (se 1 (by rfl) ⟨1000538, by rfl⟩ : syracuseStep 1334051 = 2001077) B2001077
theorem B1497923 : Blo 591290 1497923 := bstep (se 1 (by rfl) ⟨1123442, by rfl⟩ : syracuseStep 1497923 = 2246885) B2246885
theorem B3005261 : Blo 591290 3005261 := bstep (se 3 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 3005261 = 1126973) B1126973
theorem B1694641 : Blo 591290 1694641 := bstep (se 2 (by rfl) ⟨635490, by rfl⟩ : syracuseStep 1694641 = 1270981) B1270981
theorem B1498115 : Blo 591290 1498115 := bstep (se 1 (by rfl) ⟨1123586, by rfl⟩ : syracuseStep 1498115 = 2247173) B2247173
theorem B1334321 : Blo 591290 1334321 := bstep (se 2 (by rfl) ⟨500370, by rfl⟩ : syracuseStep 1334321 = 1000741) B1000741
theorem B1334339 : Blo 591290 1334339 := bstep (se 1 (by rfl) ⟨1000754, by rfl⟩ : syracuseStep 1334339 = 2001509) B2001509
theorem B2743409 : Blo 591290 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B1694915 : Blo 591290 1694915 := bstep (se 1 (by rfl) ⟨1271186, by rfl⟩ : syracuseStep 1694915 = 2542373) B2542373
theorem B810209 : Blo 591290 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B4512995 : Blo 591290 4512995 := bstep (se 1 (by rfl) ⟨3384746, by rfl⟩ : syracuseStep 4512995 = 6769493) B6769493
theorem B843043 : Blo 591290 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B711971 : Blo 591290 711971 := bstep (se 1 (by rfl) ⟨533978, by rfl⟩ : syracuseStep 711971 = 1067957) B1067957
theorem B1334609 : Blo 591290 1334609 := bstep (se 2 (by rfl) ⟨500478, by rfl⟩ : syracuseStep 1334609 = 1000957) B1000957
theorem B1334627 : Blo 591290 1334627 := bstep (se 1 (by rfl) ⟨1000970, by rfl⟩ : syracuseStep 1334627 = 2001941) B2001941
theorem B1695107 : Blo 591290 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B1334897 : Blo 591290 1334897 := bstep (se 2 (by rfl) ⟨500586, by rfl⟩ : syracuseStep 1334897 = 1001173) B1001173
theorem B1334915 : Blo 591290 1334915 := bstep (se 1 (by rfl) ⟨1001186, by rfl⟩ : syracuseStep 1334915 = 2002373) B2002373
theorem B1335185 : Blo 591290 1335185 := bstep (se 2 (by rfl) ⟨500694, by rfl⟩ : syracuseStep 1335185 = 1001389) B1001389
theorem B1335203 : Blo 591290 1335203 := bstep (se 1 (by rfl) ⟨1001402, by rfl⟩ : syracuseStep 1335203 = 2002805) B2002805
theorem B1499057 : Blo 591290 1499057 := bstep (se 2 (by rfl) ⟨562146, by rfl⟩ : syracuseStep 1499057 = 1124293) B1124293
theorem B10117061 : Blo 591290 10117061 := bstep (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) B1896949
theorem B1499107 : Blo 591290 1499107 := bstep (se 1 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 1499107 = 2248661) B2248661
theorem B5070833 : Blo 591290 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B4284515 : Blo 591290 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1499249 : Blo 591290 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B1335473 : Blo 591290 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B1335491 : Blo 591290 1335491 := bstep (se 1 (by rfl) ⟨1001618, by rfl⟩ : syracuseStep 1335491 = 2003237) B2003237
theorem B2253005 : Blo 591290 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B3203333 : Blo 591290 3203333 := bstep (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) B600625
theorem B844177 : Blo 591290 844177 := bstep (se 2 (by rfl) ⟨316566, by rfl⟩ : syracuseStep 844177 = 633133) B633133
theorem B3203525 : Blo 591290 3203525 := bstep (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) B600661
theorem B1335761 : Blo 591290 1335761 := bstep (se 2 (by rfl) ⟨500910, by rfl⟩ : syracuseStep 1335761 = 1001821) B1001821
theorem B1335779 : Blo 591290 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B844273 : Blo 591290 844273 := bstep (se 2 (by rfl) ⟨316602, by rfl⟩ : syracuseStep 844273 = 633205) B633205
theorem B1336049 : Blo 591290 1336049 := bstep (se 2 (by rfl) ⟨501018, by rfl⟩ : syracuseStep 1336049 = 1002037) B1002037
theorem B1336067 : Blo 591290 1336067 := bstep (se 1 (by rfl) ⟨1002050, by rfl⟩ : syracuseStep 1336067 = 2004101) B2004101
theorem B1598413 : Blo 591290 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B844769 : Blo 591290 844769 := bstep (se 2 (by rfl) ⟨316788, by rfl⟩ : syracuseStep 844769 = 633577) B633577
theorem B1336337 : Blo 591290 1336337 := bstep (se 2 (by rfl) ⟨501126, by rfl⟩ : syracuseStep 1336337 = 1002253) B1002253
theorem B1336355 : Blo 591290 1336355 := bstep (se 1 (by rfl) ⟨1002266, by rfl⟩ : syracuseStep 1336355 = 2004533) B2004533
theorem B1500241 : Blo 591290 1500241 := bstep (se 2 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 1500241 = 1125181) B1125181
theorem B713875 : Blo 591290 713875 := bstep (se 1 (by rfl) ⟨535406, by rfl⟩ : syracuseStep 713875 = 1070813) B1070813
theorem B1926317 : Blo 591290 1926317 := bstep (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) B722369
theorem B3368141 : Blo 591290 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B1271057 : Blo 591290 1271057 := bstep (se 2 (by rfl) ⟨476646, by rfl⟩ : syracuseStep 1271057 = 953293) B953293
theorem B1336625 : Blo 591290 1336625 := bstep (se 2 (by rfl) ⟨501234, by rfl⟩ : syracuseStep 1336625 = 1002469) B1002469
theorem B1336643 : Blo 591290 1336643 := bstep (se 1 (by rfl) ⟨1002482, by rfl⟩ : syracuseStep 1336643 = 2004965) B2004965
theorem B1500515 : Blo 591290 1500515 := bstep (se 1 (by rfl) ⟨1125386, by rfl⟩ : syracuseStep 1500515 = 2250773) B2250773
theorem B2024813 : Blo 591290 2024813 := bstep (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) B759305
theorem B3794309 : Blo 591290 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B812467 : Blo 591290 812467 := bstep (se 1 (by rfl) ⟨609350, by rfl⟩ : syracuseStep 812467 = 1218701) B1218701
theorem B714163 : Blo 591290 714163 := bstep (se 1 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 714163 = 1071245) B1071245
theorem B714259 : Blo 591290 714259 := bstep (se 1 (by rfl) ⟨535694, by rfl⟩ : syracuseStep 714259 = 1071389) B1071389
theorem B1500707 : Blo 591290 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1336913 : Blo 591290 1336913 := bstep (se 2 (by rfl) ⟨501342, by rfl⟩ : syracuseStep 1336913 = 1002685) B1002685
theorem B1336931 : Blo 591290 1336931 := bstep (se 1 (by rfl) ⟨1002698, by rfl⟩ : syracuseStep 1336931 = 2005397) B2005397
theorem B714403 : Blo 591290 714403 := bstep (se 1 (by rfl) ⟨535802, by rfl⟩ : syracuseStep 714403 = 1071605) B1071605
theorem B3008177 : Blo 591290 3008177 := bstep (se 2 (by rfl) ⟨1128066, by rfl⟩ : syracuseStep 3008177 = 2256133) B2256133
theorem B845635 : Blo 591290 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B1337201 : Blo 591290 1337201 := bstep (se 2 (by rfl) ⟨501450, by rfl⟩ : syracuseStep 1337201 = 1002901) B1002901
theorem B1337219 : Blo 591290 1337219 := bstep (se 1 (by rfl) ⟨1002914, by rfl⟩ : syracuseStep 1337219 = 2005829) B2005829
theorem B845731 : Blo 591290 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B3369073 : Blo 591290 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B1599601 : Blo 591290 1599601 := bstep (se 2 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 1599601 = 1199701) B1199701
theorem B1337489 : Blo 591290 1337489 := bstep (se 2 (by rfl) ⟨501558, by rfl⟩ : syracuseStep 1337489 = 1003117) B1003117
theorem B1337507 : Blo 591290 1337507 := bstep (se 1 (by rfl) ⟨1003130, by rfl⟩ : syracuseStep 1337507 = 2006261) B2006261
theorem B813235 : Blo 591290 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B5073293 : Blo 591290 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B846227 : Blo 591290 846227 := bstep (se 1 (by rfl) ⟨634670, by rfl⟩ : syracuseStep 846227 = 1269341) B1269341
theorem B1337777 : Blo 591290 1337777 := bstep (se 2 (by rfl) ⟨501666, by rfl⟩ : syracuseStep 1337777 = 1003333) B1003333
theorem B1337795 : Blo 591290 1337795 := bstep (se 1 (by rfl) ⟨1003346, by rfl⟩ : syracuseStep 1337795 = 2006693) B2006693
theorem B1501649 : Blo 591290 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B1501699 : Blo 591290 1501699 := bstep (se 1 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 1501699 = 2252549) B2252549
theorem B1501841 : Blo 591290 1501841 := bstep (se 2 (by rfl) ⟨563190, by rfl⟩ : syracuseStep 1501841 = 1126381) B1126381
theorem B1600163 : Blo 591290 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1338065 : Blo 591290 1338065 := bstep (se 2 (by rfl) ⟨501774, by rfl⟩ : syracuseStep 1338065 = 1003549) B1003549
theorem B1338083 : Blo 591290 1338083 := bstep (se 1 (by rfl) ⟨1003562, by rfl⟩ : syracuseStep 1338083 = 2007125) B2007125
theorem B3042161 : Blo 591290 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B748435 : Blo 591290 748435 := bstep (se 1 (by rfl) ⟨561326, by rfl⟩ : syracuseStep 748435 = 1122653) B1122653
theorem B1338353 : Blo 591290 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B748531 : Blo 591290 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B1338371 : Blo 591290 1338371 := bstep (se 1 (by rfl) ⟨1003778, by rfl⟩ : syracuseStep 1338371 = 2007557) B2007557
theorem B846865 : Blo 591290 846865 := bstep (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) B635149
theorem B2255921 : Blo 591290 2255921 := bstep (se 2 (by rfl) ⟨845970, by rfl⟩ : syracuseStep 2255921 = 1691941) B1691941
theorem B3009635 : Blo 591290 3009635 := bstep (se 1 (by rfl) ⟨2257226, by rfl⟩ : syracuseStep 3009635 = 4514453) B4514453
theorem B1338641 : Blo 591290 1338641 := bstep (se 2 (by rfl) ⟨501990, by rfl⟩ : syracuseStep 1338641 = 1003981) B1003981
theorem B1338659 : Blo 591290 1338659 := bstep (se 1 (by rfl) ⟨1003994, by rfl⟩ : syracuseStep 1338659 = 2007989) B2007989
theorem B847201 : Blo 591290 847201 := bstep (se 2 (by rfl) ⟨317700, by rfl⟩ : syracuseStep 847201 = 635401) B635401
theorem B749027 : Blo 591290 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B3370531 : Blo 591290 3370531 := bstep (se 1 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 3370531 = 5055797) B5055797
theorem B1338929 : Blo 591290 1338929 := bstep (se 2 (by rfl) ⟨502098, by rfl⟩ : syracuseStep 1338929 = 1004197) B1004197
theorem B1338947 : Blo 591290 1338947 := bstep (se 1 (by rfl) ⟨1004210, by rfl⟩ : syracuseStep 1338947 = 2008421) B2008421
theorem B1502833 : Blo 591290 1502833 := bstep (se 2 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 1502833 = 1127125) B1127125
theorem B1601201 : Blo 591290 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B1044193 : Blo 591290 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B1339217 : Blo 591290 1339217 := bstep (se 2 (by rfl) ⟨502206, by rfl⟩ : syracuseStep 1339217 = 1004413) B1004413
theorem B1339235 : Blo 591290 1339235 := bstep (se 1 (by rfl) ⟨1004426, by rfl⟩ : syracuseStep 1339235 = 2008853) B2008853
theorem B1503107 : Blo 591290 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B3010445 : Blo 591290 3010445 := bstep (se 3 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 3010445 = 1128917) B1128917
theorem B3797027 : Blo 591290 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B3371057 : Blo 591290 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B6746165 : Blo 591290 6746165 := bstep (se 5 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 6746165 = 632453) B632453
theorem B1503299 : Blo 591290 1503299 := bstep (se 1 (by rfl) ⟨1127474, by rfl⟩ : syracuseStep 1503299 = 2254949) B2254949
theorem B749731 : Blo 591290 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B749827 : Blo 591290 749827 := bstep (se 1 (by rfl) ⟨562370, by rfl⟩ : syracuseStep 749827 = 1124741) B1124741
theorem B1732963 : Blo 591290 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B5140849 : Blo 591290 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B4518341 : Blo 591290 4518341 := bstep (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) B847189
theorem B1012193 : Blo 591290 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B2257379 : Blo 591290 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B14676677 : Blo 591290 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B750323 : Blo 591290 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B17330965 : Blo 591290 17330965 := bstep (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) B812389
theorem B1897283 : Blo 591290 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B619363 : Blo 591290 619363 := bstep (se 1 (by rfl) ⟨464522, by rfl⟩ : syracuseStep 619363 = 929045) B929045
theorem B1504241 : Blo 591290 1504241 := bstep (se 2 (by rfl) ⟨564090, by rfl⟩ : syracuseStep 1504241 = 1128181) B1128181
theorem B947219 : Blo 591290 947219 := bstep (se 1 (by rfl) ⟨710414, by rfl⟩ : syracuseStep 947219 = 1420829) B1420829
theorem B1504291 : Blo 591290 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B1504433 : Blo 591290 1504433 := bstep (se 2 (by rfl) ⟨564162, by rfl⟩ : syracuseStep 1504433 = 1128325) B1128325
theorem B947393 : Blo 591290 947393 := bstep (se 2 (by rfl) ⟨355272, by rfl⟩ : syracuseStep 947393 = 710545) B710545
theorem B914641 : Blo 591290 914641 := bstep (se 2 (by rfl) ⟨342990, by rfl⟩ : syracuseStep 914641 = 685981) B685981
theorem B1996109 : Blo 591290 1996109 := bstep (se 3 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 1996109 = 748541) B748541
theorem B1996163 : Blo 591290 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B751027 : Blo 591290 751027 := bstep (se 1 (by rfl) ⟨563270, by rfl⟩ : syracuseStep 751027 = 1126541) B1126541
theorem B2258381 : Blo 591290 2258381 := bstep (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) B846893
theorem B3372515 : Blo 591290 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B751123 : Blo 591290 751123 := bstep (se 1 (by rfl) ⟨563342, by rfl⟩ : syracuseStep 751123 = 1126685) B1126685
theorem B1996433 : Blo 591290 1996433 := bstep (se 2 (by rfl) ⟨748662, by rfl⟩ : syracuseStep 1996433 = 1497325) B1497325
theorem B1898129 : Blo 591290 1898129 := bstep (se 2 (by rfl) ⟨711798, by rfl⟩ : syracuseStep 1898129 = 1423597) B1423597
theorem B11401073 : Blo 591290 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B3799025 : Blo 591290 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B751619 : Blo 591290 751619 := bstep (se 1 (by rfl) ⟨563714, by rfl⟩ : syracuseStep 751619 = 1127429) B1127429
theorem B1505425 : Blo 591290 1505425 := bstep (se 2 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 1505425 = 1129069) B1129069
theorem B1996973 : Blo 591290 1996973 := bstep (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) B748865
theorem B1997027 : Blo 591290 1997027 := bstep (se 1 (by rfl) ⟨1497770, by rfl⟩ : syracuseStep 1997027 = 2995541) B2995541
theorem B1505699 : Blo 591290 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B2849251 : Blo 591290 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B1997297 : Blo 591290 1997297 := bstep (se 2 (by rfl) ⟨748986, by rfl⟩ : syracuseStep 1997297 = 1497973) B1497973
theorem B1604099 : Blo 591290 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B1505891 : Blo 591290 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1145507 : Blo 591290 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B916145 : Blo 591290 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B752323 : Blo 591290 752323 := bstep (se 1 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 752323 = 1128485) B1128485
theorem B3013361 : Blo 591290 3013361 := bstep (se 2 (by rfl) ⟨1130010, by rfl⟩ : syracuseStep 3013361 = 2260021) B2260021
theorem B752419 : Blo 591290 752419 := bstep (se 1 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 752419 = 1128629) B1128629
theorem B3046349 : Blo 591290 3046349 := bstep (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) B1142381
theorem B1997837 : Blo 591290 1997837 := bstep (se 3 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 1997837 = 749189) B749189
theorem B1997891 : Blo 591290 1997891 := bstep (se 1 (by rfl) ⟨1498418, by rfl⟩ : syracuseStep 1997891 = 2996837) B2996837
theorem B949411 : Blo 591290 949411 := bstep (se 1 (by rfl) ⟨712058, by rfl⟩ : syracuseStep 949411 = 1424117) B1424117
theorem B7699637 : Blo 591290 7699637 := bstep (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) B721841
theorem B1834193 : Blo 591290 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B949475 : Blo 591290 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B752915 : Blo 591290 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B3374405 : Blo 591290 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B1998161 : Blo 591290 1998161 := bstep (se 2 (by rfl) ⟨749310, by rfl⟩ : syracuseStep 1998161 = 1498621) B1498621
theorem B1899949 : Blo 591290 1899949 := bstep (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) B712481
theorem B2850481 : Blo 591290 2850481 := bstep (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) B2137861
theorem B1998701 : Blo 591290 1998701 := bstep (se 3 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 1998701 = 749513) B749513
theorem B3604337 : Blo 591290 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B1998755 : Blo 591290 1998755 := bstep (se 1 (by rfl) ⟨1499066, by rfl⟩ : syracuseStep 1998755 = 2998133) B2998133
theorem B3375179 : Blo 591290 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B950795 : Blo 591290 950795 := bstep (se 1 (by rfl) ⟨713096, by rfl⟩ : syracuseStep 950795 = 1426193) B1426193
theorem B4817483 : Blo 591290 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B1999511 : Blo 591290 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B950987 : Blo 591290 950987 := bstep (se 1 (by rfl) ⟨713240, by rfl⟩ : syracuseStep 950987 = 1426481) B1426481
theorem B951115 : Blo 591290 951115 := bstep (se 1 (by rfl) ⟨713336, by rfl⟩ : syracuseStep 951115 = 1426673) B1426673
theorem B2000051 : Blo 591290 2000051 := bstep (se 1 (by rfl) ⟨1500038, by rfl⟩ : syracuseStep 2000051 = 3000077) B3000077
theorem B2131217 : Blo 591290 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B2000321 : Blo 591290 2000321 := bstep (se 2 (by rfl) ⟨750120, by rfl⟩ : syracuseStep 2000321 = 1500241) B1500241
theorem B591307 : Blo 591290 591307 := bstep (se 1 (by rfl) ⟨443480, by rfl⟩ : syracuseStep 591307 = 886961) B886961
theorem B951755 : Blo 591290 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B591319 : Blo 591290 591319 := bstep (se 1 (by rfl) ⟨443489, by rfl⟩ : syracuseStep 591319 = 886979) B886979
theorem B591339 : Blo 591290 591339 := bstep (se 1 (by rfl) ⟨443504, by rfl⟩ : syracuseStep 591339 = 887009) B887009
theorem B591351 : Blo 591290 591351 := bstep (se 1 (by rfl) ⟨443513, by rfl⟩ : syracuseStep 591351 = 887027) B887027
theorem B591371 : Blo 591290 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B591383 : Blo 591290 591383 := bstep (se 1 (by rfl) ⟨443537, by rfl⟩ : syracuseStep 591383 = 887075) B887075
theorem B951833 : Blo 591290 951833 := bstep (se 2 (by rfl) ⟨356937, by rfl⟩ : syracuseStep 951833 = 713875) B713875
theorem B591403 : Blo 591290 591403 := bstep (se 1 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 591403 = 887105) B887105
theorem B591415 : Blo 591290 591415 := bstep (se 1 (by rfl) ⟨443561, by rfl⟩ : syracuseStep 591415 = 887123) B887123
theorem B591435 : Blo 591290 591435 := bstep (se 1 (by rfl) ⟨443576, by rfl⟩ : syracuseStep 591435 = 887153) B887153
theorem B591447 : Blo 591290 591447 := bstep (se 1 (by rfl) ⟨443585, by rfl⟩ : syracuseStep 591447 = 887171) B887171
theorem B591467 : Blo 591290 591467 := bstep (se 1 (by rfl) ⟨443600, by rfl⟩ : syracuseStep 591467 = 887201) B887201
theorem B591479 : Blo 591290 591479 := bstep (se 1 (by rfl) ⟨443609, by rfl⟩ : syracuseStep 591479 = 887219) B887219
theorem B591499 : Blo 591290 591499 := bstep (se 1 (by rfl) ⟨443624, by rfl⟩ : syracuseStep 591499 = 887249) B887249
theorem B591511 : Blo 591290 591511 := bstep (se 1 (by rfl) ⟨443633, by rfl⟩ : syracuseStep 591511 = 887267) B887267
theorem B591531 : Blo 591290 591531 := bstep (se 1 (by rfl) ⟨443648, by rfl⟩ : syracuseStep 591531 = 887297) B887297
theorem B591543 : Blo 591290 591543 := bstep (se 1 (by rfl) ⟨443657, by rfl⟩ : syracuseStep 591543 = 887315) B887315
theorem B591563 : Blo 591290 591563 := bstep (se 1 (by rfl) ⟨443672, by rfl⟩ : syracuseStep 591563 = 887345) B887345
theorem B591575 : Blo 591290 591575 := bstep (se 1 (by rfl) ⟨443681, by rfl⟩ : syracuseStep 591575 = 887363) B887363
theorem B591595 : Blo 591290 591595 := bstep (se 1 (by rfl) ⟨443696, by rfl⟩ : syracuseStep 591595 = 887393) B887393
theorem B591607 : Blo 591290 591607 := bstep (se 1 (by rfl) ⟨443705, by rfl⟩ : syracuseStep 591607 = 887411) B887411
theorem B591627 : Blo 591290 591627 := bstep (se 1 (by rfl) ⟨443720, by rfl⟩ : syracuseStep 591627 = 887441) B887441
theorem B591639 : Blo 591290 591639 := bstep (se 1 (by rfl) ⟨443729, by rfl⟩ : syracuseStep 591639 = 887459) B887459
theorem B591659 : Blo 591290 591659 := bstep (se 1 (by rfl) ⟨443744, by rfl⟩ : syracuseStep 591659 = 887489) B887489
theorem B591671 : Blo 591290 591671 := bstep (se 1 (by rfl) ⟨443753, by rfl⟩ : syracuseStep 591671 = 887507) B887507
theorem B591691 : Blo 591290 591691 := bstep (se 1 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 591691 = 887537) B887537
theorem B591703 : Blo 591290 591703 := bstep (se 1 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 591703 = 887555) B887555
theorem B4818781 : Blo 591290 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B591723 : Blo 591290 591723 := bstep (se 1 (by rfl) ⟨443792, by rfl⟩ : syracuseStep 591723 = 887585) B887585
theorem B591735 : Blo 591290 591735 := bstep (se 1 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 591735 = 887603) B887603
theorem B591755 : Blo 591290 591755 := bstep (se 1 (by rfl) ⟨443816, by rfl⟩ : syracuseStep 591755 = 887633) B887633
theorem B591767 : Blo 591290 591767 := bstep (se 1 (by rfl) ⟨443825, by rfl⟩ : syracuseStep 591767 = 887651) B887651
theorem B1083289 : Blo 591290 1083289 := bstep (se 2 (by rfl) ⟨406233, by rfl⟩ : syracuseStep 1083289 = 812467) B812467
theorem B952217 : Blo 591290 952217 := bstep (se 2 (by rfl) ⟨357081, by rfl⟩ : syracuseStep 952217 = 714163) B714163
theorem B591787 : Blo 591290 591787 := bstep (se 1 (by rfl) ⟨443840, by rfl⟩ : syracuseStep 591787 = 887681) B887681
theorem B591799 : Blo 591290 591799 := bstep (se 1 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 591799 = 887699) B887699
theorem B2197441 : Blo 591290 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B591819 : Blo 591290 591819 := bstep (se 1 (by rfl) ⟨443864, by rfl⟩ : syracuseStep 591819 = 887729) B887729
theorem B591831 : Blo 591290 591831 := bstep (se 1 (by rfl) ⟨443873, by rfl⟩ : syracuseStep 591831 = 887747) B887747
theorem B2000861 : Blo 591290 2000861 := bstep (se 3 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 2000861 = 750323) B750323
theorem B591851 : Blo 591290 591851 := bstep (se 1 (by rfl) ⟨443888, by rfl⟩ : syracuseStep 591851 = 887777) B887777
theorem B591863 : Blo 591290 591863 := bstep (se 1 (by rfl) ⟨443897, by rfl⟩ : syracuseStep 591863 = 887795) B887795
theorem B591883 : Blo 591290 591883 := bstep (se 1 (by rfl) ⟨443912, by rfl⟩ : syracuseStep 591883 = 887825) B887825
theorem B591895 : Blo 591290 591895 := bstep (se 1 (by rfl) ⟨443921, by rfl⟩ : syracuseStep 591895 = 887843) B887843
theorem B952345 : Blo 591290 952345 := bstep (se 2 (by rfl) ⟨357129, by rfl⟩ : syracuseStep 952345 = 714259) B714259
theorem B591915 : Blo 591290 591915 := bstep (se 1 (by rfl) ⟨443936, by rfl⟩ : syracuseStep 591915 = 887873) B887873
theorem B591927 : Blo 591290 591927 := bstep (se 1 (by rfl) ⟨443945, by rfl⟩ : syracuseStep 591927 = 887891) B887891
theorem B591947 : Blo 591290 591947 := bstep (se 1 (by rfl) ⟨443960, by rfl⟩ : syracuseStep 591947 = 887921) B887921
theorem B591959 : Blo 591290 591959 := bstep (se 1 (by rfl) ⟨443969, by rfl⟩ : syracuseStep 591959 = 887939) B887939
theorem B591979 : Blo 591290 591979 := bstep (se 1 (by rfl) ⟨443984, by rfl⟩ : syracuseStep 591979 = 887969) B887969
theorem B591991 : Blo 591290 591991 := bstep (se 1 (by rfl) ⟨443993, by rfl⟩ : syracuseStep 591991 = 887987) B887987
theorem B592011 : Blo 591290 592011 := bstep (se 1 (by rfl) ⟨444008, by rfl⟩ : syracuseStep 592011 = 888017) B888017
theorem B592023 : Blo 591290 592023 := bstep (se 1 (by rfl) ⟨444017, by rfl⟩ : syracuseStep 592023 = 888035) B888035
theorem B886937 : Blo 591290 886937 := bstep (se 2 (by rfl) ⟨332601, by rfl⟩ : syracuseStep 886937 = 665203) B665203
theorem B592043 : Blo 591290 592043 := bstep (se 1 (by rfl) ⟨444032, by rfl⟩ : syracuseStep 592043 = 888065) B888065
theorem B592055 : Blo 591290 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B592075 : Blo 591290 592075 := bstep (se 1 (by rfl) ⟨444056, by rfl⟩ : syracuseStep 592075 = 888113) B888113
theorem B592087 : Blo 591290 592087 := bstep (se 1 (by rfl) ⟨444065, by rfl⟩ : syracuseStep 592087 = 888131) B888131
theorem B592107 : Blo 591290 592107 := bstep (se 1 (by rfl) ⟨444080, by rfl⟩ : syracuseStep 592107 = 888161) B888161
theorem B592119 : Blo 591290 592119 := bstep (se 1 (by rfl) ⟨444089, by rfl⟩ : syracuseStep 592119 = 888179) B888179
theorem B887051 : Blo 591290 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B592139 : Blo 591290 592139 := bstep (se 1 (by rfl) ⟨444104, by rfl⟩ : syracuseStep 592139 = 888209) B888209
theorem B887063 : Blo 591290 887063 := bstep (se 1 (by rfl) ⟨665297, by rfl⟩ : syracuseStep 887063 = 1330595) B1330595
theorem B592151 : Blo 591290 592151 := bstep (se 1 (by rfl) ⟨444113, by rfl⟩ : syracuseStep 592151 = 888227) B888227
theorem B592171 : Blo 591290 592171 := bstep (se 1 (by rfl) ⟨444128, by rfl⟩ : syracuseStep 592171 = 888257) B888257
theorem B592183 : Blo 591290 592183 := bstep (se 1 (by rfl) ⟨444137, by rfl⟩ : syracuseStep 592183 = 888275) B888275
theorem B592203 : Blo 591290 592203 := bstep (se 1 (by rfl) ⟨444152, by rfl⟩ : syracuseStep 592203 = 888305) B888305
theorem B1902923 : Blo 591290 1902923 := bstep (se 1 (by rfl) ⟨1427192, by rfl⟩ : syracuseStep 1902923 = 2854385) B2854385
theorem B592215 : Blo 591290 592215 := bstep (se 1 (by rfl) ⟨444161, by rfl⟩ : syracuseStep 592215 = 888323) B888323
theorem B887129 : Blo 591290 887129 := bstep (se 2 (by rfl) ⟨332673, by rfl⟩ : syracuseStep 887129 = 665347) B665347
theorem B592235 : Blo 591290 592235 := bstep (se 1 (by rfl) ⟨444176, by rfl⟩ : syracuseStep 592235 = 888353) B888353
theorem B592247 : Blo 591290 592247 := bstep (se 1 (by rfl) ⟨444185, by rfl⟩ : syracuseStep 592247 = 888371) B888371
theorem B2853251 : Blo 591290 2853251 := bstep (se 1 (by rfl) ⟨2139938, by rfl⟩ : syracuseStep 2853251 = 4279877) B4279877
theorem B592267 : Blo 591290 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B592279 : Blo 591290 592279 := bstep (se 1 (by rfl) ⟨444209, by rfl⟩ : syracuseStep 592279 = 888419) B888419
theorem B592299 : Blo 591290 592299 := bstep (se 1 (by rfl) ⟨444224, by rfl⟩ : syracuseStep 592299 = 888449) B888449
theorem B592311 : Blo 591290 592311 := bstep (se 1 (by rfl) ⟨444233, by rfl⟩ : syracuseStep 592311 = 888467) B888467
theorem B887243 : Blo 591290 887243 := bstep (se 1 (by rfl) ⟨665432, by rfl⟩ : syracuseStep 887243 = 1330865) B1330865
theorem B592331 : Blo 591290 592331 := bstep (se 1 (by rfl) ⟨444248, by rfl⟩ : syracuseStep 592331 = 888497) B888497
theorem B887255 : Blo 591290 887255 := bstep (se 1 (by rfl) ⟨665441, by rfl⟩ : syracuseStep 887255 = 1330883) B1330883
theorem B592343 : Blo 591290 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B592363 : Blo 591290 592363 := bstep (se 1 (by rfl) ⟨444272, by rfl⟩ : syracuseStep 592363 = 888545) B888545
theorem B592375 : Blo 591290 592375 := bstep (se 1 (by rfl) ⟨444281, by rfl⟩ : syracuseStep 592375 = 888563) B888563
theorem B592395 : Blo 591290 592395 := bstep (se 1 (by rfl) ⟨444296, by rfl⟩ : syracuseStep 592395 = 888593) B888593
theorem B592407 : Blo 591290 592407 := bstep (se 1 (by rfl) ⟨444305, by rfl⟩ : syracuseStep 592407 = 888611) B888611
theorem B887321 : Blo 591290 887321 := bstep (se 2 (by rfl) ⟨332745, by rfl⟩ : syracuseStep 887321 = 665491) B665491
theorem B592427 : Blo 591290 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B592439 : Blo 591290 592439 := bstep (se 1 (by rfl) ⟨444329, by rfl⟩ : syracuseStep 592439 = 888659) B888659
theorem B592459 : Blo 591290 592459 := bstep (se 1 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 592459 = 888689) B888689
theorem B592471 : Blo 591290 592471 := bstep (se 1 (by rfl) ⟨444353, by rfl⟩ : syracuseStep 592471 = 888707) B888707
theorem B592491 : Blo 591290 592491 := bstep (se 1 (by rfl) ⟨444368, by rfl⟩ : syracuseStep 592491 = 888737) B888737
theorem B592503 : Blo 591290 592503 := bstep (se 1 (by rfl) ⟨444377, by rfl⟩ : syracuseStep 592503 = 888755) B888755
theorem B887435 : Blo 591290 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B592523 : Blo 591290 592523 := bstep (se 1 (by rfl) ⟨444392, by rfl⟩ : syracuseStep 592523 = 888785) B888785
theorem B887447 : Blo 591290 887447 := bstep (se 1 (by rfl) ⟨665585, by rfl⟩ : syracuseStep 887447 = 1331171) B1331171
theorem B592535 : Blo 591290 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B592555 : Blo 591290 592555 := bstep (se 1 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 592555 = 888833) B888833
theorem B592567 : Blo 591290 592567 := bstep (se 1 (by rfl) ⟨444425, by rfl⟩ : syracuseStep 592567 = 888851) B888851
theorem B592587 : Blo 591290 592587 := bstep (se 1 (by rfl) ⟨444440, by rfl⟩ : syracuseStep 592587 = 888881) B888881
theorem B592599 : Blo 591290 592599 := bstep (se 1 (by rfl) ⟨444449, by rfl⟩ : syracuseStep 592599 = 888899) B888899
theorem B887513 : Blo 591290 887513 := bstep (se 2 (by rfl) ⟨332817, by rfl⟩ : syracuseStep 887513 = 665635) B665635
theorem B2525917 : Blo 591290 2525917 := bstep (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) B947219
theorem B592619 : Blo 591290 592619 := bstep (se 1 (by rfl) ⟨444464, by rfl⟩ : syracuseStep 592619 = 888929) B888929
theorem B592631 : Blo 591290 592631 := bstep (se 1 (by rfl) ⟨444473, by rfl⟩ : syracuseStep 592631 = 888947) B888947
theorem B1280779 : Blo 591290 1280779 := bstep (se 1 (by rfl) ⟨960584, by rfl⟩ : syracuseStep 1280779 = 1921169) B1921169
theorem B592651 : Blo 591290 592651 := bstep (se 1 (by rfl) ⟨444488, by rfl⟩ : syracuseStep 592651 = 888977) B888977
theorem B592663 : Blo 591290 592663 := bstep (se 1 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 592663 = 888995) B888995
theorem B592683 : Blo 591290 592683 := bstep (se 1 (by rfl) ⟨444512, by rfl⟩ : syracuseStep 592683 = 889025) B889025
theorem B7211821 : Blo 591290 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B592695 : Blo 591290 592695 := bstep (se 1 (by rfl) ⟨444521, by rfl⟩ : syracuseStep 592695 = 889043) B889043
theorem B4492097 : Blo 591290 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B2132801 : Blo 591290 2132801 := bstep (se 2 (by rfl) ⟨799800, by rfl⟩ : syracuseStep 2132801 = 1599601) B1599601
theorem B887627 : Blo 591290 887627 := bstep (se 1 (by rfl) ⟨665720, by rfl⟩ : syracuseStep 887627 = 1331441) B1331441
theorem B592715 : Blo 591290 592715 := bstep (se 1 (by rfl) ⟨444536, by rfl⟩ : syracuseStep 592715 = 889073) B889073
theorem B887639 : Blo 591290 887639 := bstep (se 1 (by rfl) ⟨665729, by rfl⟩ : syracuseStep 887639 = 1331459) B1331459
theorem B592727 : Blo 591290 592727 := bstep (se 1 (by rfl) ⟨444545, by rfl⟩ : syracuseStep 592727 = 889091) B889091
theorem B592747 : Blo 591290 592747 := bstep (se 1 (by rfl) ⟨444560, by rfl⟩ : syracuseStep 592747 = 889121) B889121
theorem B592759 : Blo 591290 592759 := bstep (se 1 (by rfl) ⟨444569, by rfl⟩ : syracuseStep 592759 = 889139) B889139
theorem B592779 : Blo 591290 592779 := bstep (se 1 (by rfl) ⟨444584, by rfl⟩ : syracuseStep 592779 = 889169) B889169
theorem B592791 : Blo 591290 592791 := bstep (se 1 (by rfl) ⟨444593, by rfl⟩ : syracuseStep 592791 = 889187) B889187
theorem B887705 : Blo 591290 887705 := bstep (se 2 (by rfl) ⟨332889, by rfl⟩ : syracuseStep 887705 = 665779) B665779
theorem B1084313 : Blo 591290 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B592811 : Blo 591290 592811 := bstep (se 1 (by rfl) ⟨444608, by rfl⟩ : syracuseStep 592811 = 889217) B889217
theorem B592823 : Blo 591290 592823 := bstep (se 1 (by rfl) ⟨444617, by rfl⟩ : syracuseStep 592823 = 889235) B889235
theorem B592843 : Blo 591290 592843 := bstep (se 1 (by rfl) ⟨444632, by rfl⟩ : syracuseStep 592843 = 889265) B889265
theorem B592855 : Blo 591290 592855 := bstep (se 1 (by rfl) ⟨444641, by rfl⟩ : syracuseStep 592855 = 889283) B889283
theorem B592875 : Blo 591290 592875 := bstep (se 1 (by rfl) ⟨444656, by rfl⟩ : syracuseStep 592875 = 889313) B889313
theorem B592887 : Blo 591290 592887 := bstep (se 1 (by rfl) ⟨444665, by rfl⟩ : syracuseStep 592887 = 889331) B889331
theorem B887819 : Blo 591290 887819 := bstep (se 1 (by rfl) ⟨665864, by rfl⟩ : syracuseStep 887819 = 1331729) B1331729
theorem B592907 : Blo 591290 592907 := bstep (se 1 (by rfl) ⟨444680, by rfl⟩ : syracuseStep 592907 = 889361) B889361
theorem B36637717 : Blo 591290 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B887831 : Blo 591290 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B592919 : Blo 591290 592919 := bstep (se 1 (by rfl) ⟨444689, by rfl⟩ : syracuseStep 592919 = 889379) B889379
theorem B592939 : Blo 591290 592939 := bstep (se 1 (by rfl) ⟨444704, by rfl⟩ : syracuseStep 592939 = 889409) B889409
theorem B592951 : Blo 591290 592951 := bstep (se 1 (by rfl) ⟨444713, by rfl⟩ : syracuseStep 592951 = 889427) B889427
theorem B592971 : Blo 591290 592971 := bstep (se 1 (by rfl) ⟨444728, by rfl⟩ : syracuseStep 592971 = 889457) B889457
theorem B2001995 : Blo 591290 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B592983 : Blo 591290 592983 := bstep (se 1 (by rfl) ⟨444737, by rfl⟩ : syracuseStep 592983 = 889475) B889475
theorem B887897 : Blo 591290 887897 := bstep (se 2 (by rfl) ⟨332961, by rfl⟩ : syracuseStep 887897 = 665923) B665923
theorem B593003 : Blo 591290 593003 := bstep (se 1 (by rfl) ⟨444752, by rfl⟩ : syracuseStep 593003 = 889505) B889505
theorem B593015 : Blo 591290 593015 := bstep (se 1 (by rfl) ⟨444761, by rfl⟩ : syracuseStep 593015 = 889523) B889523
theorem B593035 : Blo 591290 593035 := bstep (se 1 (by rfl) ⟨444776, by rfl⟩ : syracuseStep 593035 = 889553) B889553
theorem B593047 : Blo 591290 593047 := bstep (se 1 (by rfl) ⟨444785, by rfl⟩ : syracuseStep 593047 = 889571) B889571
theorem B593067 : Blo 591290 593067 := bstep (se 1 (by rfl) ⟨444800, by rfl⟩ : syracuseStep 593067 = 889601) B889601
theorem B593079 : Blo 591290 593079 := bstep (se 1 (by rfl) ⟨444809, by rfl⟩ : syracuseStep 593079 = 889619) B889619
theorem B888011 : Blo 591290 888011 := bstep (se 1 (by rfl) ⟨666008, by rfl⟩ : syracuseStep 888011 = 1332017) B1332017
theorem B593099 : Blo 591290 593099 := bstep (se 1 (by rfl) ⟨444824, by rfl⟩ : syracuseStep 593099 = 889649) B889649
theorem B888023 : Blo 591290 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B593111 : Blo 591290 593111 := bstep (se 1 (by rfl) ⟨444833, by rfl⟩ : syracuseStep 593111 = 889667) B889667
theorem B593131 : Blo 591290 593131 := bstep (se 1 (by rfl) ⟨444848, by rfl⟩ : syracuseStep 593131 = 889697) B889697
theorem B593143 : Blo 591290 593143 := bstep (se 1 (by rfl) ⟨444857, by rfl⟩ : syracuseStep 593143 = 889715) B889715
theorem B593163 : Blo 591290 593163 := bstep (se 1 (by rfl) ⟨444872, by rfl⟩ : syracuseStep 593163 = 889745) B889745
theorem B593175 : Blo 591290 593175 := bstep (se 1 (by rfl) ⟨444881, by rfl⟩ : syracuseStep 593175 = 889763) B889763
theorem B888089 : Blo 591290 888089 := bstep (se 2 (by rfl) ⟨333033, by rfl⟩ : syracuseStep 888089 = 666067) B666067
theorem B593195 : Blo 591290 593195 := bstep (se 1 (by rfl) ⟨444896, by rfl⟩ : syracuseStep 593195 = 889793) B889793
theorem B593207 : Blo 591290 593207 := bstep (se 1 (by rfl) ⟨444905, by rfl⟩ : syracuseStep 593207 = 889811) B889811
theorem B593227 : Blo 591290 593227 := bstep (se 1 (by rfl) ⟨444920, by rfl⟩ : syracuseStep 593227 = 889841) B889841
theorem B593239 : Blo 591290 593239 := bstep (se 1 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 593239 = 889859) B889859
theorem B2002265 : Blo 591290 2002265 := bstep (se 2 (by rfl) ⟨750849, by rfl⟩ : syracuseStep 2002265 = 1501699) B1501699
theorem B593259 : Blo 591290 593259 := bstep (se 1 (by rfl) ⟨444944, by rfl⟩ : syracuseStep 593259 = 889889) B889889
theorem B593271 : Blo 591290 593271 := bstep (se 1 (by rfl) ⟨444953, by rfl⟩ : syracuseStep 593271 = 889907) B889907
theorem B888203 : Blo 591290 888203 := bstep (se 1 (by rfl) ⟨666152, by rfl⟩ : syracuseStep 888203 = 1332305) B1332305
theorem B593291 : Blo 591290 593291 := bstep (se 1 (by rfl) ⟨444968, by rfl⟩ : syracuseStep 593291 = 889937) B889937
theorem B888215 : Blo 591290 888215 := bstep (se 1 (by rfl) ⟨666161, by rfl⟩ : syracuseStep 888215 = 1332323) B1332323
theorem B593303 : Blo 591290 593303 := bstep (se 1 (by rfl) ⟨444977, by rfl⟩ : syracuseStep 593303 = 889955) B889955
theorem B1904023 : Blo 591290 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B593323 : Blo 591290 593323 := bstep (se 1 (by rfl) ⟨444992, by rfl⟩ : syracuseStep 593323 = 889985) B889985
theorem B593335 : Blo 591290 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B593355 : Blo 591290 593355 := bstep (se 1 (by rfl) ⟨445016, by rfl⟩ : syracuseStep 593355 = 890033) B890033
theorem B593367 : Blo 591290 593367 := bstep (se 1 (by rfl) ⟨445025, by rfl⟩ : syracuseStep 593367 = 890051) B890051
theorem B888281 : Blo 591290 888281 := bstep (se 2 (by rfl) ⟨333105, by rfl⟩ : syracuseStep 888281 = 666211) B666211
theorem B593387 : Blo 591290 593387 := bstep (se 1 (by rfl) ⟨445040, by rfl⟩ : syracuseStep 593387 = 890081) B890081
theorem B593399 : Blo 591290 593399 := bstep (se 1 (by rfl) ⟨445049, by rfl⟩ : syracuseStep 593399 = 890099) B890099
theorem B593419 : Blo 591290 593419 := bstep (se 1 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 593419 = 890129) B890129
theorem B593431 : Blo 591290 593431 := bstep (se 1 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 593431 = 890147) B890147
theorem B593451 : Blo 591290 593451 := bstep (se 1 (by rfl) ⟨445088, by rfl⟩ : syracuseStep 593451 = 890177) B890177
theorem B593463 : Blo 591290 593463 := bstep (se 1 (by rfl) ⟨445097, by rfl⟩ : syracuseStep 593463 = 890195) B890195
theorem B1281611 : Blo 591290 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B888395 : Blo 591290 888395 := bstep (se 1 (by rfl) ⟨666296, by rfl⟩ : syracuseStep 888395 = 1332593) B1332593
theorem B593483 : Blo 591290 593483 := bstep (se 1 (by rfl) ⟨445112, by rfl⟩ : syracuseStep 593483 = 890225) B890225
theorem B888407 : Blo 591290 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B593495 : Blo 591290 593495 := bstep (se 1 (by rfl) ⟨445121, by rfl⟩ : syracuseStep 593495 = 890243) B890243
theorem B593515 : Blo 591290 593515 := bstep (se 1 (by rfl) ⟨445136, by rfl⟩ : syracuseStep 593515 = 890273) B890273
theorem B593527 : Blo 591290 593527 := bstep (se 1 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 593527 = 890291) B890291
theorem B593547 : Blo 591290 593547 := bstep (se 1 (by rfl) ⟨445160, by rfl⟩ : syracuseStep 593547 = 890321) B890321
theorem B593559 : Blo 591290 593559 := bstep (se 1 (by rfl) ⟨445169, by rfl⟩ : syracuseStep 593559 = 890339) B890339
theorem B888473 : Blo 591290 888473 := bstep (se 2 (by rfl) ⟨333177, by rfl⟩ : syracuseStep 888473 = 666355) B666355
theorem B593579 : Blo 591290 593579 := bstep (se 1 (by rfl) ⟨445184, by rfl⟩ : syracuseStep 593579 = 890369) B890369
theorem B593591 : Blo 591290 593591 := bstep (se 1 (by rfl) ⟨445193, by rfl⟩ : syracuseStep 593591 = 890387) B890387
theorem B593611 : Blo 591290 593611 := bstep (se 1 (by rfl) ⟨445208, by rfl⟩ : syracuseStep 593611 = 890417) B890417
theorem B593623 : Blo 591290 593623 := bstep (se 1 (by rfl) ⟨445217, by rfl⟩ : syracuseStep 593623 = 890435) B890435
theorem B593643 : Blo 591290 593643 := bstep (se 1 (by rfl) ⟨445232, by rfl⟩ : syracuseStep 593643 = 890465) B890465
theorem B593655 : Blo 591290 593655 := bstep (se 1 (by rfl) ⟨445241, by rfl⟩ : syracuseStep 593655 = 890483) B890483
theorem B888587 : Blo 591290 888587 := bstep (se 1 (by rfl) ⟨666440, by rfl⟩ : syracuseStep 888587 = 1332881) B1332881
theorem B593675 : Blo 591290 593675 := bstep (se 1 (by rfl) ⟨445256, by rfl⟩ : syracuseStep 593675 = 890513) B890513
theorem B888599 : Blo 591290 888599 := bstep (se 1 (by rfl) ⟨666449, by rfl⟩ : syracuseStep 888599 = 1332899) B1332899
theorem B593687 : Blo 591290 593687 := bstep (se 1 (by rfl) ⟨445265, by rfl⟩ : syracuseStep 593687 = 890531) B890531
theorem B593707 : Blo 591290 593707 := bstep (se 1 (by rfl) ⟨445280, by rfl⟩ : syracuseStep 593707 = 890561) B890561
theorem B593719 : Blo 591290 593719 := bstep (se 1 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 593719 = 890579) B890579
theorem B593739 : Blo 591290 593739 := bstep (se 1 (by rfl) ⟨445304, by rfl⟩ : syracuseStep 593739 = 890609) B890609
theorem B593751 : Blo 591290 593751 := bstep (se 1 (by rfl) ⟨445313, by rfl⟩ : syracuseStep 593751 = 890627) B890627
theorem B888665 : Blo 591290 888665 := bstep (se 2 (by rfl) ⟨333249, by rfl⟩ : syracuseStep 888665 = 666499) B666499
theorem B593771 : Blo 591290 593771 := bstep (se 1 (by rfl) ⟨445328, by rfl⟩ : syracuseStep 593771 = 890657) B890657
theorem B593783 : Blo 591290 593783 := bstep (se 1 (by rfl) ⟨445337, by rfl⟩ : syracuseStep 593783 = 890675) B890675
theorem B593803 : Blo 591290 593803 := bstep (se 1 (by rfl) ⟨445352, by rfl⟩ : syracuseStep 593803 = 890705) B890705
theorem B593815 : Blo 591290 593815 := bstep (se 1 (by rfl) ⟨445361, by rfl⟩ : syracuseStep 593815 = 890723) B890723
theorem B593835 : Blo 591290 593835 := bstep (se 1 (by rfl) ⟨445376, by rfl⟩ : syracuseStep 593835 = 890753) B890753
theorem B593847 : Blo 591290 593847 := bstep (se 1 (by rfl) ⟨445385, by rfl⟩ : syracuseStep 593847 = 890771) B890771
theorem B2035649 : Blo 591290 2035649 := bstep (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) B1526737
theorem B888779 : Blo 591290 888779 := bstep (se 1 (by rfl) ⟨666584, by rfl⟩ : syracuseStep 888779 = 1333169) B1333169
theorem B593867 : Blo 591290 593867 := bstep (se 1 (by rfl) ⟨445400, by rfl⟩ : syracuseStep 593867 = 890801) B890801
theorem B888791 : Blo 591290 888791 := bstep (se 1 (by rfl) ⟨666593, by rfl⟩ : syracuseStep 888791 = 1333187) B1333187
theorem B593879 : Blo 591290 593879 := bstep (se 1 (by rfl) ⟨445409, by rfl⟩ : syracuseStep 593879 = 890819) B890819
theorem B593899 : Blo 591290 593899 := bstep (se 1 (by rfl) ⟨445424, by rfl⟩ : syracuseStep 593899 = 890849) B890849
theorem B593911 : Blo 591290 593911 := bstep (se 1 (by rfl) ⟨445433, by rfl⟩ : syracuseStep 593911 = 890867) B890867
theorem B593931 : Blo 591290 593931 := bstep (se 1 (by rfl) ⟨445448, by rfl⟩ : syracuseStep 593931 = 890897) B890897
theorem B2002967 : Blo 591290 2002967 := bstep (se 1 (by rfl) ⟨1502225, by rfl⟩ : syracuseStep 2002967 = 3004451) B3004451
theorem B593943 : Blo 591290 593943 := bstep (se 1 (by rfl) ⟨445457, by rfl⟩ : syracuseStep 593943 = 890915) B890915
theorem B888857 : Blo 591290 888857 := bstep (se 2 (by rfl) ⟨333321, by rfl⟩ : syracuseStep 888857 = 666643) B666643
theorem B593963 : Blo 591290 593963 := bstep (se 1 (by rfl) ⟨445472, by rfl⟩ : syracuseStep 593963 = 890945) B890945
theorem B593975 : Blo 591290 593975 := bstep (se 1 (by rfl) ⟨445481, by rfl⟩ : syracuseStep 593975 = 890963) B890963
theorem B593995 : Blo 591290 593995 := bstep (se 1 (by rfl) ⟨445496, by rfl⟩ : syracuseStep 593995 = 890993) B890993
theorem B594007 : Blo 591290 594007 := bstep (se 1 (by rfl) ⟨445505, by rfl⟩ : syracuseStep 594007 = 891011) B891011
theorem B6951005 : Blo 591290 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B594027 : Blo 591290 594027 := bstep (se 1 (by rfl) ⟨445520, by rfl⟩ : syracuseStep 594027 = 891041) B891041
theorem B594039 : Blo 591290 594039 := bstep (se 1 (by rfl) ⟨445529, by rfl⟩ : syracuseStep 594039 = 891059) B891059
theorem B888971 : Blo 591290 888971 := bstep (se 1 (by rfl) ⟨666728, by rfl⟩ : syracuseStep 888971 = 1333457) B1333457
theorem B594059 : Blo 591290 594059 := bstep (se 1 (by rfl) ⟨445544, by rfl⟩ : syracuseStep 594059 = 891089) B891089
theorem B888983 : Blo 591290 888983 := bstep (se 1 (by rfl) ⟨666737, by rfl⟩ : syracuseStep 888983 = 1333475) B1333475
theorem B594071 : Blo 591290 594071 := bstep (se 1 (by rfl) ⟨445553, by rfl⟩ : syracuseStep 594071 = 891107) B891107
theorem B594091 : Blo 591290 594091 := bstep (se 1 (by rfl) ⟨445568, by rfl⟩ : syracuseStep 594091 = 891137) B891137
theorem B594103 : Blo 591290 594103 := bstep (se 1 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 594103 = 891155) B891155
theorem B594123 : Blo 591290 594123 := bstep (se 1 (by rfl) ⟨445592, by rfl⟩ : syracuseStep 594123 = 891185) B891185
theorem B1904843 : Blo 591290 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B594135 : Blo 591290 594135 := bstep (se 1 (by rfl) ⟨445601, by rfl⟩ : syracuseStep 594135 = 891203) B891203
theorem B889049 : Blo 591290 889049 := bstep (se 2 (by rfl) ⟨333393, by rfl⟩ : syracuseStep 889049 = 666787) B666787
theorem B594155 : Blo 591290 594155 := bstep (se 1 (by rfl) ⟨445616, by rfl⟩ : syracuseStep 594155 = 891233) B891233
theorem B594167 : Blo 591290 594167 := bstep (se 1 (by rfl) ⟨445625, by rfl⟩ : syracuseStep 594167 = 891251) B891251
theorem B594187 : Blo 591290 594187 := bstep (se 1 (by rfl) ⟨445640, by rfl⟩ : syracuseStep 594187 = 891281) B891281
theorem B594199 : Blo 591290 594199 := bstep (se 1 (by rfl) ⟨445649, by rfl⟩ : syracuseStep 594199 = 891299) B891299
theorem B594219 : Blo 591290 594219 := bstep (se 1 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 594219 = 891329) B891329
theorem B594231 : Blo 591290 594231 := bstep (se 1 (by rfl) ⟨445673, by rfl⟩ : syracuseStep 594231 = 891347) B891347
theorem B889163 : Blo 591290 889163 := bstep (se 1 (by rfl) ⟨666872, by rfl⟩ : syracuseStep 889163 = 1333745) B1333745
theorem B594251 : Blo 591290 594251 := bstep (se 1 (by rfl) ⟨445688, by rfl⟩ : syracuseStep 594251 = 891377) B891377
theorem B889175 : Blo 591290 889175 := bstep (se 1 (by rfl) ⟨666881, by rfl⟩ : syracuseStep 889175 = 1333763) B1333763
theorem B594263 : Blo 591290 594263 := bstep (se 1 (by rfl) ⟨445697, by rfl⟩ : syracuseStep 594263 = 891395) B891395
theorem B594283 : Blo 591290 594283 := bstep (se 1 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 594283 = 891425) B891425
theorem B594295 : Blo 591290 594295 := bstep (se 1 (by rfl) ⟨445721, by rfl⟩ : syracuseStep 594295 = 891443) B891443
theorem B2920835 : Blo 591290 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B594315 : Blo 591290 594315 := bstep (se 1 (by rfl) ⟨445736, by rfl⟩ : syracuseStep 594315 = 891473) B891473
theorem B594327 : Blo 591290 594327 := bstep (se 1 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 594327 = 891491) B891491
theorem B889241 : Blo 591290 889241 := bstep (se 2 (by rfl) ⟨333465, by rfl⟩ : syracuseStep 889241 = 666931) B666931
theorem B594347 : Blo 591290 594347 := bstep (se 1 (by rfl) ⟨445760, by rfl⟩ : syracuseStep 594347 = 891521) B891521
theorem B594359 : Blo 591290 594359 := bstep (se 1 (by rfl) ⟨445769, by rfl⟩ : syracuseStep 594359 = 891539) B891539
theorem B594379 : Blo 591290 594379 := bstep (se 1 (by rfl) ⟨445784, by rfl⟩ : syracuseStep 594379 = 891569) B891569
theorem B594391 : Blo 591290 594391 := bstep (se 1 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 594391 = 891587) B891587
theorem B594411 : Blo 591290 594411 := bstep (se 1 (by rfl) ⟨445808, by rfl⟩ : syracuseStep 594411 = 891617) B891617
theorem B594423 : Blo 591290 594423 := bstep (se 1 (by rfl) ⟨445817, by rfl⟩ : syracuseStep 594423 = 891635) B891635
theorem B889355 : Blo 591290 889355 := bstep (se 1 (by rfl) ⟨667016, by rfl⟩ : syracuseStep 889355 = 1334033) B1334033
theorem B594443 : Blo 591290 594443 := bstep (se 1 (by rfl) ⟨445832, by rfl⟩ : syracuseStep 594443 = 891665) B891665
theorem B889367 : Blo 591290 889367 := bstep (se 1 (by rfl) ⟨667025, by rfl⟩ : syracuseStep 889367 = 1334051) B1334051
theorem B594455 : Blo 591290 594455 := bstep (se 1 (by rfl) ⟨445841, by rfl⟩ : syracuseStep 594455 = 891683) B891683
theorem B594475 : Blo 591290 594475 := bstep (se 1 (by rfl) ⟨445856, by rfl⟩ : syracuseStep 594475 = 891713) B891713
theorem B2003507 : Blo 591290 2003507 := bstep (se 1 (by rfl) ⟨1502630, by rfl⟩ : syracuseStep 2003507 = 3005261) B3005261
theorem B594487 : Blo 591290 594487 := bstep (se 1 (by rfl) ⟨445865, by rfl⟩ : syracuseStep 594487 = 891731) B891731
theorem B594507 : Blo 591290 594507 := bstep (se 1 (by rfl) ⟨445880, by rfl⟩ : syracuseStep 594507 = 891761) B891761
theorem B594519 : Blo 591290 594519 := bstep (se 1 (by rfl) ⟨445889, by rfl⟩ : syracuseStep 594519 = 891779) B891779
theorem B889433 : Blo 591290 889433 := bstep (se 2 (by rfl) ⟨333537, by rfl⟩ : syracuseStep 889433 = 667075) B667075
theorem B3379805 : Blo 591290 3379805 := bstep (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) B1267427
theorem B594539 : Blo 591290 594539 := bstep (se 1 (by rfl) ⟨445904, by rfl⟩ : syracuseStep 594539 = 891809) B891809
theorem B594551 : Blo 591290 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B594571 : Blo 591290 594571 := bstep (se 1 (by rfl) ⟨445928, by rfl⟩ : syracuseStep 594571 = 891857) B891857
theorem B594583 : Blo 591290 594583 := bstep (se 1 (by rfl) ⟨445937, by rfl⟩ : syracuseStep 594583 = 891875) B891875
theorem B594603 : Blo 591290 594603 := bstep (se 1 (by rfl) ⟨445952, by rfl⟩ : syracuseStep 594603 = 891905) B891905
theorem B594615 : Blo 591290 594615 := bstep (se 1 (by rfl) ⟨445961, by rfl⟩ : syracuseStep 594615 = 891923) B891923
theorem B889547 : Blo 591290 889547 := bstep (se 1 (by rfl) ⟨667160, by rfl⟩ : syracuseStep 889547 = 1334321) B1334321
theorem B594635 : Blo 591290 594635 := bstep (se 1 (by rfl) ⟨445976, by rfl⟩ : syracuseStep 594635 = 891953) B891953
theorem B889559 : Blo 591290 889559 := bstep (se 1 (by rfl) ⟨667169, by rfl⟩ : syracuseStep 889559 = 1334339) B1334339
theorem B4494041 : Blo 591290 4494041 := bstep (se 2 (by rfl) ⟨1685265, by rfl⟩ : syracuseStep 4494041 = 3370531) B3370531
theorem B594647 : Blo 591290 594647 := bstep (se 1 (by rfl) ⟨445985, by rfl⟩ : syracuseStep 594647 = 891971) B891971
theorem B594667 : Blo 591290 594667 := bstep (se 1 (by rfl) ⟨446000, by rfl⟩ : syracuseStep 594667 = 892001) B892001
theorem B594679 : Blo 591290 594679 := bstep (se 1 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 594679 = 892019) B892019
theorem B594699 : Blo 591290 594699 := bstep (se 1 (by rfl) ⟨446024, by rfl⟩ : syracuseStep 594699 = 892049) B892049
theorem B594711 : Blo 591290 594711 := bstep (se 1 (by rfl) ⟨446033, by rfl⟩ : syracuseStep 594711 = 892067) B892067
theorem B889625 : Blo 591290 889625 := bstep (se 2 (by rfl) ⟨333609, by rfl⟩ : syracuseStep 889625 = 667219) B667219
theorem B594731 : Blo 591290 594731 := bstep (se 1 (by rfl) ⟨446048, by rfl⟩ : syracuseStep 594731 = 892097) B892097
theorem B594743 : Blo 591290 594743 := bstep (se 1 (by rfl) ⟨446057, by rfl⟩ : syracuseStep 594743 = 892115) B892115
theorem B2003777 : Blo 591290 2003777 := bstep (se 2 (by rfl) ⟨751416, by rfl⟩ : syracuseStep 2003777 = 1502833) B1502833
theorem B594763 : Blo 591290 594763 := bstep (se 1 (by rfl) ⟨446072, by rfl⟩ : syracuseStep 594763 = 892145) B892145
theorem B594775 : Blo 591290 594775 := bstep (se 1 (by rfl) ⟨446081, by rfl⟩ : syracuseStep 594775 = 892163) B892163
theorem B594795 : Blo 591290 594795 := bstep (se 1 (by rfl) ⟨446096, by rfl⟩ : syracuseStep 594795 = 892193) B892193
theorem B594807 : Blo 591290 594807 := bstep (se 1 (by rfl) ⟨446105, by rfl⟩ : syracuseStep 594807 = 892211) B892211
theorem B889739 : Blo 591290 889739 := bstep (se 1 (by rfl) ⟨667304, by rfl⟩ : syracuseStep 889739 = 1334609) B1334609
theorem B594827 : Blo 591290 594827 := bstep (se 1 (by rfl) ⟨446120, by rfl⟩ : syracuseStep 594827 = 892241) B892241
theorem B889751 : Blo 591290 889751 := bstep (se 1 (by rfl) ⟨667313, by rfl⟩ : syracuseStep 889751 = 1334627) B1334627
theorem B594839 : Blo 591290 594839 := bstep (se 1 (by rfl) ⟨446129, by rfl⟩ : syracuseStep 594839 = 892259) B892259
theorem B594859 : Blo 591290 594859 := bstep (se 1 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 594859 = 892289) B892289
theorem B594871 : Blo 591290 594871 := bstep (se 1 (by rfl) ⟨446153, by rfl⟩ : syracuseStep 594871 = 892307) B892307
theorem B594891 : Blo 591290 594891 := bstep (se 1 (by rfl) ⟨446168, by rfl⟩ : syracuseStep 594891 = 892337) B892337
theorem B594903 : Blo 591290 594903 := bstep (se 1 (by rfl) ⟨446177, by rfl⟩ : syracuseStep 594903 = 892355) B892355
theorem B889817 : Blo 591290 889817 := bstep (se 2 (by rfl) ⟨333681, by rfl⟩ : syracuseStep 889817 = 667363) B667363
theorem B594923 : Blo 591290 594923 := bstep (se 1 (by rfl) ⟨446192, by rfl⟩ : syracuseStep 594923 = 892385) B892385
theorem B594935 : Blo 591290 594935 := bstep (se 1 (by rfl) ⟨446201, by rfl⟩ : syracuseStep 594935 = 892403) B892403
theorem B594955 : Blo 591290 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B594967 : Blo 591290 594967 := bstep (se 1 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 594967 = 892451) B892451
theorem B594987 : Blo 591290 594987 := bstep (se 1 (by rfl) ⟨446240, by rfl⟩ : syracuseStep 594987 = 892481) B892481
theorem B594999 : Blo 591290 594999 := bstep (se 1 (by rfl) ⟨446249, by rfl⟩ : syracuseStep 594999 = 892499) B892499
theorem B889931 : Blo 591290 889931 := bstep (se 1 (by rfl) ⟨667448, by rfl⟩ : syracuseStep 889931 = 1334897) B1334897
theorem B595019 : Blo 591290 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B889943 : Blo 591290 889943 := bstep (se 1 (by rfl) ⟨667457, by rfl⟩ : syracuseStep 889943 = 1334915) B1334915
theorem B595031 : Blo 591290 595031 := bstep (se 1 (by rfl) ⟨446273, by rfl⟩ : syracuseStep 595031 = 892547) B892547
theorem B595051 : Blo 591290 595051 := bstep (se 1 (by rfl) ⟨446288, by rfl⟩ : syracuseStep 595051 = 892577) B892577
theorem B595063 : Blo 591290 595063 := bstep (se 1 (by rfl) ⟨446297, by rfl⟩ : syracuseStep 595063 = 892595) B892595
theorem B595083 : Blo 591290 595083 := bstep (se 1 (by rfl) ⟨446312, by rfl⟩ : syracuseStep 595083 = 892625) B892625
theorem B595095 : Blo 591290 595095 := bstep (se 1 (by rfl) ⟨446321, by rfl⟩ : syracuseStep 595095 = 892643) B892643
theorem B890009 : Blo 591290 890009 := bstep (se 2 (by rfl) ⟨333753, by rfl⟩ : syracuseStep 890009 = 667507) B667507
theorem B595115 : Blo 591290 595115 := bstep (se 1 (by rfl) ⟨446336, by rfl⟩ : syracuseStep 595115 = 892673) B892673
theorem B595127 : Blo 591290 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B595147 : Blo 591290 595147 := bstep (se 1 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 595147 = 892721) B892721
theorem B595159 : Blo 591290 595159 := bstep (se 1 (by rfl) ⟨446369, by rfl⟩ : syracuseStep 595159 = 892739) B892739
theorem B595179 : Blo 591290 595179 := bstep (se 1 (by rfl) ⟨446384, by rfl⟩ : syracuseStep 595179 = 892769) B892769
theorem B595191 : Blo 591290 595191 := bstep (se 1 (by rfl) ⟨446393, by rfl⟩ : syracuseStep 595191 = 892787) B892787
theorem B890123 : Blo 591290 890123 := bstep (se 1 (by rfl) ⟨667592, by rfl⟩ : syracuseStep 890123 = 1335185) B1335185
theorem B595211 : Blo 591290 595211 := bstep (se 1 (by rfl) ⟨446408, by rfl⟩ : syracuseStep 595211 = 892817) B892817
theorem B890135 : Blo 591290 890135 := bstep (se 1 (by rfl) ⟨667601, by rfl⟩ : syracuseStep 890135 = 1335203) B1335203
theorem B595223 : Blo 591290 595223 := bstep (se 1 (by rfl) ⟨446417, by rfl⟩ : syracuseStep 595223 = 892835) B892835
theorem B595243 : Blo 591290 595243 := bstep (se 1 (by rfl) ⟨446432, by rfl⟩ : syracuseStep 595243 = 892865) B892865
theorem B595255 : Blo 591290 595255 := bstep (se 1 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 595255 = 892883) B892883
theorem B3380555 : Blo 591290 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B595275 : Blo 591290 595275 := bstep (se 1 (by rfl) ⟨446456, by rfl⟩ : syracuseStep 595275 = 892913) B892913
theorem B595287 : Blo 591290 595287 := bstep (se 1 (by rfl) ⟨446465, by rfl⟩ : syracuseStep 595287 = 892931) B892931
theorem B890201 : Blo 591290 890201 := bstep (se 2 (by rfl) ⟨333825, by rfl⟩ : syracuseStep 890201 = 667651) B667651
theorem B2004317 : Blo 591290 2004317 := bstep (se 3 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 2004317 = 751619) B751619
theorem B2856343 : Blo 591290 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B890315 : Blo 591290 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B890327 : Blo 591290 890327 := bstep (se 1 (by rfl) ⟨667745, by rfl⟩ : syracuseStep 890327 = 1335491) B1335491
theorem B2135555 : Blo 591290 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B890393 : Blo 591290 890393 := bstep (se 2 (by rfl) ⟨333897, by rfl⟩ : syracuseStep 890393 = 667795) B667795
theorem B7607843 : Blo 591290 7607843 := bstep (se 1 (by rfl) ⟨5705882, by rfl⟩ : syracuseStep 7607843 = 11411765) B11411765
theorem B2135683 : Blo 591290 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B890507 : Blo 591290 890507 := bstep (se 1 (by rfl) ⟨667880, by rfl⟩ : syracuseStep 890507 = 1335761) B1335761
theorem B890519 : Blo 591290 890519 := bstep (se 1 (by rfl) ⟨667889, by rfl⟩ : syracuseStep 890519 = 1335779) B1335779
theorem B890585 : Blo 591290 890585 := bstep (se 2 (by rfl) ⟨333969, by rfl⟩ : syracuseStep 890585 = 667939) B667939
theorem B6854465 : Blo 591290 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B890699 : Blo 591290 890699 := bstep (se 1 (by rfl) ⟨668024, by rfl⟩ : syracuseStep 890699 = 1336049) B1336049
theorem B890711 : Blo 591290 890711 := bstep (se 1 (by rfl) ⟨668033, by rfl⟩ : syracuseStep 890711 = 1336067) B1336067
theorem B890777 : Blo 591290 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B890891 : Blo 591290 890891 := bstep (se 1 (by rfl) ⟨668168, by rfl⟩ : syracuseStep 890891 = 1336337) B1336337
theorem B890903 : Blo 591290 890903 := bstep (se 1 (by rfl) ⟨668177, by rfl⟩ : syracuseStep 890903 = 1336355) B1336355
theorem B890969 : Blo 591290 890969 := bstep (se 2 (by rfl) ⟨334113, by rfl⟩ : syracuseStep 890969 = 668227) B668227
theorem B1284211 : Blo 591290 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B891083 : Blo 591290 891083 := bstep (se 1 (by rfl) ⟨668312, by rfl⟩ : syracuseStep 891083 = 1336625) B1336625
theorem B891095 : Blo 591290 891095 := bstep (se 1 (by rfl) ⟨668321, by rfl⟩ : syracuseStep 891095 = 1336643) B1336643
theorem B1349875 : Blo 591290 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B2529539 : Blo 591290 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B891161 : Blo 591290 891161 := bstep (se 2 (by rfl) ⟨334185, by rfl⟩ : syracuseStep 891161 = 668371) B668371
theorem B891275 : Blo 591290 891275 := bstep (se 1 (by rfl) ⟨668456, by rfl⟩ : syracuseStep 891275 = 1336913) B1336913
theorem B891287 : Blo 591290 891287 := bstep (se 1 (by rfl) ⟨668465, by rfl⟩ : syracuseStep 891287 = 1336931) B1336931
theorem B2005451 : Blo 591290 2005451 := bstep (se 1 (by rfl) ⟨1504088, by rfl⟩ : syracuseStep 2005451 = 3008177) B3008177
theorem B891353 : Blo 591290 891353 := bstep (se 2 (by rfl) ⟨334257, by rfl⟩ : syracuseStep 891353 = 668515) B668515
theorem B825817 : Blo 591290 825817 := bstep (se 2 (by rfl) ⟨309681, by rfl⟩ : syracuseStep 825817 = 619363) B619363
theorem B891467 : Blo 591290 891467 := bstep (se 1 (by rfl) ⟨668600, by rfl⟩ : syracuseStep 891467 = 1337201) B1337201
theorem B891479 : Blo 591290 891479 := bstep (se 1 (by rfl) ⟨668609, by rfl⟩ : syracuseStep 891479 = 1337219) B1337219
theorem B891545 : Blo 591290 891545 := bstep (se 2 (by rfl) ⟨334329, by rfl⟩ : syracuseStep 891545 = 668659) B668659
theorem B8100557 : Blo 591290 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B2005721 : Blo 591290 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B891659 : Blo 591290 891659 := bstep (se 1 (by rfl) ⟨668744, by rfl⟩ : syracuseStep 891659 = 1337489) B1337489
theorem B891671 : Blo 591290 891671 := bstep (se 1 (by rfl) ⟨668753, by rfl⟩ : syracuseStep 891671 = 1337507) B1337507
theorem B891737 : Blo 591290 891737 := bstep (se 2 (by rfl) ⟨334401, by rfl⟩ : syracuseStep 891737 = 668803) B668803
theorem B3382195 : Blo 591290 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B891851 : Blo 591290 891851 := bstep (se 1 (by rfl) ⟨668888, by rfl⟩ : syracuseStep 891851 = 1337777) B1337777
theorem B891863 : Blo 591290 891863 := bstep (se 1 (by rfl) ⟨668897, by rfl⟩ : syracuseStep 891863 = 1337795) B1337795
theorem B891929 : Blo 591290 891929 := bstep (se 2 (by rfl) ⟨334473, by rfl⟩ : syracuseStep 891929 = 668947) B668947
theorem B4267043 : Blo 591290 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B3054685 : Blo 591290 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B892043 : Blo 591290 892043 := bstep (se 1 (by rfl) ⟨669032, by rfl⟩ : syracuseStep 892043 = 1338065) B1338065
theorem B892055 : Blo 591290 892055 := bstep (se 1 (by rfl) ⟨669041, by rfl⟩ : syracuseStep 892055 = 1338083) B1338083
theorem B892121 : Blo 591290 892121 := bstep (se 2 (by rfl) ⟨334545, by rfl⟩ : syracuseStep 892121 = 669091) B669091
theorem B892235 : Blo 591290 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B892247 : Blo 591290 892247 := bstep (se 1 (by rfl) ⟨669185, by rfl⟩ : syracuseStep 892247 = 1338371) B1338371
theorem B2006423 : Blo 591290 2006423 := bstep (se 1 (by rfl) ⟨1504817, by rfl⟩ : syracuseStep 2006423 = 3009635) B3009635
theorem B892313 : Blo 591290 892313 := bstep (se 2 (by rfl) ⟨334617, by rfl⟩ : syracuseStep 892313 = 669235) B669235
theorem B892427 : Blo 591290 892427 := bstep (se 1 (by rfl) ⟨669320, by rfl⟩ : syracuseStep 892427 = 1338641) B1338641
theorem B892439 : Blo 591290 892439 := bstep (se 1 (by rfl) ⟨669329, by rfl⟩ : syracuseStep 892439 = 1338659) B1338659
theorem B892505 : Blo 591290 892505 := bstep (se 2 (by rfl) ⟨334689, by rfl⟩ : syracuseStep 892505 = 669379) B669379
theorem B892619 : Blo 591290 892619 := bstep (se 1 (by rfl) ⟨669464, by rfl⟩ : syracuseStep 892619 = 1338929) B1338929
theorem B892631 : Blo 591290 892631 := bstep (se 1 (by rfl) ⟨669473, by rfl⟩ : syracuseStep 892631 = 1338947) B1338947
theorem B892697 : Blo 591290 892697 := bstep (se 2 (by rfl) ⟨334761, by rfl⟩ : syracuseStep 892697 = 669523) B669523
theorem B892811 : Blo 591290 892811 := bstep (se 1 (by rfl) ⟨669608, by rfl⟩ : syracuseStep 892811 = 1339217) B1339217
theorem B892823 : Blo 591290 892823 := bstep (se 1 (by rfl) ⟨669617, by rfl⟩ : syracuseStep 892823 = 1339235) B1339235
theorem B2006963 : Blo 591290 2006963 := bstep (se 1 (by rfl) ⟨1505222, by rfl⟩ : syracuseStep 2006963 = 3010445) B3010445
theorem B892889 : Blo 591290 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B2531351 : Blo 591290 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B4497443 : Blo 591290 4497443 := bstep (se 1 (by rfl) ⟨3373082, by rfl⟩ : syracuseStep 4497443 = 6746165) B6746165
theorem B2007233 : Blo 591290 2007233 := bstep (se 2 (by rfl) ⟨752712, by rfl⟩ : syracuseStep 2007233 = 1505425) B1505425
theorem B3383653 : Blo 591290 3383653 := bstep (se 4 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 3383653 = 634435) B634435
theorem B2007773 : Blo 591290 2007773 := bstep (se 3 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 2007773 = 752915) B752915
theorem B631595 : Blo 591290 631595 := bstep (se 1 (by rfl) ⟨473696, by rfl⟩ : syracuseStep 631595 = 947393) B947393
theorem B3810149 : Blo 591290 3810149 := bstep (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) B714403
theorem B3810199 : Blo 591290 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B1123571 : Blo 591290 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B2893121 : Blo 591290 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B2532683 : Blo 591290 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B1123723 : Blo 591290 1123723 := bstep (se 1 (by rfl) ⟨842792, by rfl⟩ : syracuseStep 1123723 = 1685585) B1685585
theorem B43394453 : Blo 591290 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B665239 : Blo 591290 665239 := bstep (se 1 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 665239 = 997859) B997859
theorem B1124057 : Blo 591290 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B665419 : Blo 591290 665419 := bstep (se 1 (by rfl) ⟨499064, by rfl⟩ : syracuseStep 665419 = 998129) B998129
theorem B2008907 : Blo 591290 2008907 := bstep (se 1 (by rfl) ⟨1506680, by rfl⟩ : syracuseStep 2008907 = 3013361) B3013361
theorem B2533265 : Blo 591290 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B2467757 : Blo 591290 2467757 := bstep (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) B925409
theorem B665527 : Blo 591290 665527 := bstep (se 1 (by rfl) ⟨499145, by rfl⟩ : syracuseStep 665527 = 998291) B998291
theorem B665707 : Blo 591290 665707 := bstep (se 1 (by rfl) ⟨499280, by rfl⟩ : syracuseStep 665707 = 998561) B998561
theorem B1222795 : Blo 591290 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B632983 : Blo 591290 632983 := bstep (se 1 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 632983 = 949475) B949475
theorem B665815 : Blo 591290 665815 := bstep (se 1 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 665815 = 998723) B998723
theorem B1124695 : Blo 591290 1124695 := bstep (se 1 (by rfl) ⟨843521, by rfl⟩ : syracuseStep 1124695 = 1687043) B1687043
theorem B665995 : Blo 591290 665995 := bstep (se 1 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 665995 = 998993) B998993
theorem B8530393 : Blo 591290 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B666103 : Blo 591290 666103 := bstep (se 1 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 666103 = 999155) B999155
theorem B82356749 : Blo 591290 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B2402891 : Blo 591290 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B666283 : Blo 591290 666283 := bstep (se 1 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 666283 = 999425) B999425
theorem B600791 : Blo 591290 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B2140931 : Blo 591290 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B666391 : Blo 591290 666391 := bstep (se 1 (by rfl) ⟨499793, by rfl⟩ : syracuseStep 666391 = 999587) B999587
theorem B2534323 : Blo 591290 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B666571 : Blo 591290 666571 := bstep (se 1 (by rfl) ⟨499928, by rfl⟩ : syracuseStep 666571 = 999857) B999857
theorem B633803 : Blo 591290 633803 := bstep (se 1 (by rfl) ⟨475352, by rfl⟩ : syracuseStep 633803 = 950705) B950705
theorem B2436119 : Blo 591290 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B666679 : Blo 591290 666679 := bstep (se 1 (by rfl) ⟨500009, by rfl⟩ : syracuseStep 666679 = 1000019) B1000019
theorem B10103939 : Blo 591290 10103939 := bstep (se 1 (by rfl) ⟨7577954, by rfl⟩ : syracuseStep 10103939 = 15155909) B15155909
theorem B1125515 : Blo 591290 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B1125569 : Blo 591290 1125569 := bstep (se 2 (by rfl) ⟨422088, by rfl⟩ : syracuseStep 1125569 = 844177) B844177
theorem B10169549 : Blo 591290 10169549 := bstep (se 3 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 10169549 = 3813581) B3813581
theorem B666859 : Blo 591290 666859 := bstep (se 1 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 666859 = 1000289) B1000289
theorem B666967 : Blo 591290 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B667147 : Blo 591290 667147 := bstep (se 1 (by rfl) ⟨500360, by rfl⟩ : syracuseStep 667147 = 1000721) B1000721
theorem B667255 : Blo 591290 667255 := bstep (se 1 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 667255 = 1000883) B1000883
theorem B667435 : Blo 591290 667435 := bstep (se 1 (by rfl) ⟨500576, by rfl⟩ : syracuseStep 667435 = 1001153) B1001153
theorem B667543 : Blo 591290 667543 := bstep (se 1 (by rfl) ⟨500657, by rfl⟩ : syracuseStep 667543 = 1001315) B1001315
theorem B634807 : Blo 591290 634807 := bstep (se 1 (by rfl) ⟨476105, by rfl⟩ : syracuseStep 634807 = 952211) B952211
theorem B2404397 : Blo 591290 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B667723 : Blo 591290 667723 := bstep (se 1 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 667723 = 1001585) B1001585
theorem B1126487 : Blo 591290 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B667831 : Blo 591290 667831 := bstep (se 1 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 667831 = 1001747) B1001747
theorem B2535725 : Blo 591290 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B5714221 : Blo 591290 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B1421657 : Blo 591290 1421657 := bstep (se 2 (by rfl) ⟨533121, by rfl⟩ : syracuseStep 1421657 = 1066243) B1066243
theorem B668011 : Blo 591290 668011 := bstep (se 1 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 668011 = 1002017) B1002017
theorem B3813763 : Blo 591290 3813763 := bstep (se 1 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 3813763 = 5720645) B5720645
theorem B668119 : Blo 591290 668119 := bstep (se 1 (by rfl) ⟨501089, by rfl⟩ : syracuseStep 668119 = 1002179) B1002179
theorem B1127027 : Blo 591290 1127027 := bstep (se 1 (by rfl) ⟨845270, by rfl⟩ : syracuseStep 1127027 = 1690541) B1690541
theorem B668299 : Blo 591290 668299 := bstep (se 1 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 668299 = 1002449) B1002449
theorem B635563 : Blo 591290 635563 := bstep (se 1 (by rfl) ⟨476672, by rfl⟩ : syracuseStep 635563 = 953345) B953345
theorem B4338353 : Blo 591290 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B668407 : Blo 591290 668407 := bstep (se 1 (by rfl) ⟨501305, by rfl⟩ : syracuseStep 668407 = 1002611) B1002611
theorem B5059421 : Blo 591290 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B668587 : Blo 591290 668587 := bstep (se 1 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 668587 = 1002881) B1002881
theorem B2995217 : Blo 591290 2995217 := bstep (se 2 (by rfl) ⟨1123206, by rfl⟩ : syracuseStep 2995217 = 2246413) B2246413
theorem B668695 : Blo 591290 668695 := bstep (se 1 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 668695 = 1003043) B1003043
theorem B603191 : Blo 591290 603191 := bstep (se 1 (by rfl) ⟨452393, by rfl⟩ : syracuseStep 603191 = 904787) B904787
theorem B1127513 : Blo 591290 1127513 := bstep (se 2 (by rfl) ⟨422817, by rfl⟩ : syracuseStep 1127513 = 845635) B845635
theorem B2995379 : Blo 591290 2995379 := bstep (se 1 (by rfl) ⟨2246534, by rfl⟩ : syracuseStep 2995379 = 4493069) B4493069
theorem B668875 : Blo 591290 668875 := bstep (se 1 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 668875 = 1003313) B1003313
theorem B4502789 : Blo 591290 4502789 := bstep (se 4 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 4502789 = 844273) B844273
theorem B668983 : Blo 591290 668983 := bstep (se 1 (by rfl) ⟨501737, by rfl⟩ : syracuseStep 668983 = 1003475) B1003475
theorem B4273559 : Blo 591290 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B1357273 : Blo 591290 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B669163 : Blo 591290 669163 := bstep (se 1 (by rfl) ⟨501872, by rfl⟩ : syracuseStep 669163 = 1003745) B1003745
theorem B2405953 : Blo 591290 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B5060171 : Blo 591290 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B964171 : Blo 591290 964171 := bstep (se 1 (by rfl) ⟨723128, by rfl⟩ : syracuseStep 964171 = 1446257) B1446257
theorem B669271 : Blo 591290 669271 := bstep (se 1 (by rfl) ⟨501953, by rfl⟩ : syracuseStep 669271 = 1003907) B1003907
theorem B6076109 : Blo 591290 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B1128179 : Blo 591290 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B669451 : Blo 591290 669451 := bstep (se 1 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 669451 = 1004177) B1004177
theorem B669559 : Blo 591290 669559 := bstep (se 1 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 669559 = 1004339) B1004339
theorem B899095 : Blo 591290 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B3389485 : Blo 591290 3389485 := bstep (se 3 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 3389485 = 1271057) B1271057
theorem B4798871 : Blo 591290 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B1128971 : Blo 591290 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B997913 : Blo 591290 997913 := bstep (se 2 (by rfl) ⟨374217, by rfl⟩ : syracuseStep 997913 = 748435) B748435
theorem B1686109 : Blo 591290 1686109 := bstep (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) B632291
theorem B1686167 : Blo 591290 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B998041 : Blo 591290 998041 := bstep (se 2 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 998041 = 748531) B748531
theorem B1129153 : Blo 591290 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B2997323 : Blo 591290 2997323 := bstep (se 1 (by rfl) ⟨2247992, by rfl⟩ : syracuseStep 2997323 = 4495985) B4495985
theorem B1129601 : Blo 591290 1129601 := bstep (se 2 (by rfl) ⟨423600, by rfl⟩ : syracuseStep 1129601 = 847201) B847201
theorem B5061811 : Blo 591290 5061811 := bstep (se 1 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 5061811 = 7592717) B7592717
theorem B998615 : Blo 591290 998615 := bstep (se 1 (by rfl) ⟨748961, by rfl⟩ : syracuseStep 998615 = 1497923) B1497923
theorem B998743 : Blo 591290 998743 := bstep (se 1 (by rfl) ⟨749057, by rfl⟩ : syracuseStep 998743 = 1498115) B1498115
theorem B1129943 : Blo 591290 1129943 := bstep (se 1 (by rfl) ⟨847457, by rfl⟩ : syracuseStep 1129943 = 1694915) B1694915
theorem B3259865 : Blo 591290 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B1392257 : Blo 591290 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B4505219 : Blo 591290 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B1687385 : Blo 591290 1687385 := bstep (se 2 (by rfl) ⟨632769, by rfl⟩ : syracuseStep 1687385 = 1265539) B1265539
theorem B999371 : Blo 591290 999371 := bstep (se 1 (by rfl) ⟨749528, by rfl⟩ : syracuseStep 999371 = 1499057) B1499057
theorem B1687499 : Blo 591290 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B999499 : Blo 591290 999499 := bstep (se 1 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 999499 = 1499249) B1499249
theorem B3653707 : Blo 591290 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B5718221 : Blo 591290 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B999641 : Blo 591290 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B999769 : Blo 591290 999769 := bstep (se 2 (by rfl) ⟨374913, by rfl⟩ : syracuseStep 999769 = 749827) B749827
theorem B2539927 : Blo 591290 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B2310617 : Blo 591290 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B2736605 : Blo 591290 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B2539997 : Blo 591290 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B2245427 : Blo 591290 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B2245441 : Blo 591290 2245441 := bstep (se 2 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 2245441 = 1684081) B1684081
theorem B2999105 : Blo 591290 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B1000343 : Blo 591290 1000343 := bstep (se 1 (by rfl) ⟨750257, by rfl⟩ : syracuseStep 1000343 = 1500515) B1500515
theorem B1000471 : Blo 591290 1000471 := bstep (se 1 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 1000471 = 1500707) B1500707
theorem B1688627 : Blo 591290 1688627 := bstep (se 1 (by rfl) ⟨1266470, by rfl⟩ : syracuseStep 1688627 = 2532941) B2532941
theorem B9159749 : Blo 591290 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B2540747 : Blo 591290 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B1689025 : Blo 591290 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B1001099 : Blo 591290 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1427095 : Blo 591290 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B1001227 : Blo 591290 1001227 := bstep (se 1 (by rfl) ⟨750920, by rfl⟩ : syracuseStep 1001227 = 1501841) B1501841
theorem B1066775 : Blo 591290 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B2279191 : Blo 591290 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B1001369 : Blo 591290 1001369 := bstep (se 2 (by rfl) ⟨375513, by rfl⟩ : syracuseStep 1001369 = 751027) B751027
theorem B1001497 : Blo 591290 1001497 := bstep (se 2 (by rfl) ⟨375561, by rfl⟩ : syracuseStep 1001497 = 751123) B751123
theorem B7620965 : Blo 591290 7620965 := bstep (se 4 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 7620965 = 1428931) B1428931
theorem B1067467 : Blo 591290 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B3197515 : Blo 591290 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B1002071 : Blo 591290 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B2247371 : Blo 591290 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B1002199 : Blo 591290 1002199 := bstep (se 1 (by rfl) ⟨751649, by rfl⟩ : syracuseStep 1002199 = 1503299) B1503299
theorem B2247385 : Blo 591290 2247385 := bstep (se 2 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 2247385 = 1685539) B1685539
theorem B3001049 : Blo 591290 3001049 := bstep (se 2 (by rfl) ⟨1125393, by rfl⟩ : syracuseStep 3001049 = 2250787) B2250787
theorem B2280257 : Blo 591290 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B7228277 : Blo 591290 7228277 := bstep (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) B677651
theorem B4508621 : Blo 591290 4508621 := bstep (se 3 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 4508621 = 1690733) B1690733
theorem B674795 : Blo 591290 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B9784451 : Blo 591290 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B1330433 : Blo 591290 1330433 := bstep (se 2 (by rfl) ⟨498912, by rfl⟩ : syracuseStep 1330433 = 997825) B997825
theorem B1002827 : Blo 591290 1002827 := bstep (se 1 (by rfl) ⟨752120, by rfl⟩ : syracuseStep 1002827 = 1504241) B1504241
theorem B4509107 : Blo 591290 4509107 := bstep (se 1 (by rfl) ⟨3381830, by rfl⟩ : syracuseStep 4509107 = 6763661) B6763661
theorem B1002955 : Blo 591290 1002955 := bstep (se 1 (by rfl) ⟨752216, by rfl⟩ : syracuseStep 1002955 = 1504433) B1504433
theorem B1330649 : Blo 591290 1330649 := bstep (se 2 (by rfl) ⟨498993, by rfl⟩ : syracuseStep 1330649 = 997987) B997987
theorem B1330739 : Blo 591290 1330739 := bstep (se 1 (by rfl) ⟨998054, by rfl⟩ : syracuseStep 1330739 = 1996109) B1996109
theorem B1330775 : Blo 591290 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B1003097 : Blo 591290 1003097 := bstep (se 2 (by rfl) ⟨376161, by rfl⟩ : syracuseStep 1003097 = 752323) B752323
theorem B2248343 : Blo 591290 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B1003225 : Blo 591290 1003225 := bstep (se 2 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 1003225 = 752419) B752419
theorem B1330955 : Blo 591290 1330955 := bstep (se 1 (by rfl) ⟨998216, by rfl⟩ : syracuseStep 1330955 = 1996433) B1996433
theorem B1265419 : Blo 591290 1265419 := bstep (se 1 (by rfl) ⟨949064, by rfl⟩ : syracuseStep 1265419 = 1898129) B1898129
theorem B1331009 : Blo 591290 1331009 := bstep (se 2 (by rfl) ⟨499128, by rfl⟩ : syracuseStep 1331009 = 998257) B998257
theorem B1691543 : Blo 591290 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B1200025 : Blo 591290 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B1331225 : Blo 591290 1331225 := bstep (se 2 (by rfl) ⟨499209, by rfl⟩ : syracuseStep 1331225 = 998419) B998419
theorem B1331315 : Blo 591290 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B1331351 : Blo 591290 1331351 := bstep (se 1 (by rfl) ⟨998513, by rfl⟩ : syracuseStep 1331351 = 1997027) B1997027
theorem B1265881 : Blo 591290 1265881 := bstep (se 2 (by rfl) ⟨474705, by rfl⟩ : syracuseStep 1265881 = 949411) B949411
theorem B1003799 : Blo 591290 1003799 := bstep (se 1 (by rfl) ⟨752849, by rfl⟩ : syracuseStep 1003799 = 1505699) B1505699
theorem B3002669 : Blo 591290 3002669 := bstep (se 3 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 3002669 = 1126001) B1126001
theorem B1331531 : Blo 591290 1331531 := bstep (se 1 (by rfl) ⟨998648, by rfl⟩ : syracuseStep 1331531 = 1997297) B1997297
theorem B1069399 : Blo 591290 1069399 := bstep (se 1 (by rfl) ⟨802049, by rfl⟩ : syracuseStep 1069399 = 1604099) B1604099
theorem B1331585 : Blo 591290 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B1003927 : Blo 591290 1003927 := bstep (se 1 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 1003927 = 1505891) B1505891
theorem B610763 : Blo 591290 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B1331801 : Blo 591290 1331801 := bstep (se 2 (by rfl) ⟨499425, by rfl⟩ : syracuseStep 1331801 = 998851) B998851
theorem B1331891 : Blo 591290 1331891 := bstep (se 1 (by rfl) ⟨998918, by rfl⟩ : syracuseStep 1331891 = 1997837) B1997837
theorem B1331927 : Blo 591290 1331927 := bstep (se 1 (by rfl) ⟨998945, by rfl⟩ : syracuseStep 1331927 = 1997891) B1997891
theorem B5788421 : Blo 591290 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B5133091 : Blo 591290 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B4510565 : Blo 591290 4510565 := bstep (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) B845731
theorem B2249603 : Blo 591290 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B1332107 : Blo 591290 1332107 := bstep (se 1 (by rfl) ⟨999080, by rfl⟩ : syracuseStep 1332107 = 1998161) B1998161
theorem B1332161 : Blo 591290 1332161 := bstep (se 2 (by rfl) ⟨499560, by rfl⟩ : syracuseStep 1332161 = 999121) B999121
theorem B1332377 : Blo 591290 1332377 := bstep (se 2 (by rfl) ⟨499641, by rfl⟩ : syracuseStep 1332377 = 999283) B999283
theorem B3790003 : Blo 591290 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B1692875 : Blo 591290 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B1332467 : Blo 591290 1332467 := bstep (se 1 (by rfl) ⟨999350, by rfl⟩ : syracuseStep 1332467 = 1998701) B1998701
theorem B1332503 : Blo 591290 1332503 := bstep (se 1 (by rfl) ⟨999377, by rfl⟩ : syracuseStep 1332503 = 1998755) B1998755
theorem B4511051 : Blo 591290 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B1332683 : Blo 591290 1332683 := bstep (se 1 (by rfl) ⟨999512, by rfl⟩ : syracuseStep 1332683 = 1999025) B1999025
theorem B1332737 : Blo 591290 1332737 := bstep (se 2 (by rfl) ⟨499776, by rfl⟩ : syracuseStep 1332737 = 999553) B999553
theorem B1267265 : Blo 591290 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B1332953 : Blo 591290 1332953 := bstep (se 2 (by rfl) ⟨499857, by rfl⟩ : syracuseStep 1332953 = 999715) B999715
theorem B1333043 : Blo 591290 1333043 := bstep (se 1 (by rfl) ⟨999782, by rfl⟩ : syracuseStep 1333043 = 1999565) B1999565
theorem B1333079 : Blo 591290 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B1333259 : Blo 591290 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B1333313 : Blo 591290 1333313 := bstep (se 2 (by rfl) ⟨499992, by rfl⟩ : syracuseStep 1333313 = 999985) B999985
theorem B1497163 : Blo 591290 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B17291339 : Blo 591290 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B1497305 : Blo 591290 1497305 := bstep (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) B1122979
theorem B1333529 : Blo 591290 1333529 := bstep (se 2 (by rfl) ⟨500073, by rfl⟩ : syracuseStep 1333529 = 1000147) B1000147
theorem B1202483 : Blo 591290 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B1333619 : Blo 591290 1333619 := bstep (se 1 (by rfl) ⟨1000214, by rfl⟩ : syracuseStep 1333619 = 2000429) B2000429
theorem B1333655 : Blo 591290 1333655 := bstep (se 1 (by rfl) ⟨1000241, by rfl⟩ : syracuseStep 1333655 = 2000483) B2000483
theorem B1333835 : Blo 591290 1333835 := bstep (se 1 (by rfl) ⟨1000376, by rfl⟩ : syracuseStep 1333835 = 2000753) B2000753
theorem B1333889 : Blo 591290 1333889 := bstep (se 2 (by rfl) ⟨500208, by rfl⟩ : syracuseStep 1333889 = 1000417) B1000417
theorem B842519 : Blo 591290 842519 := bstep (se 1 (by rfl) ⟨631889, by rfl⟩ : syracuseStep 842519 = 1263779) B1263779
theorem B1694515 : Blo 591290 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B1334105 : Blo 591290 1334105 := bstep (se 2 (by rfl) ⟨500289, by rfl⟩ : syracuseStep 1334105 = 1000579) B1000579
theorem B1334195 : Blo 591290 1334195 := bstep (se 1 (by rfl) ⟨1000646, by rfl⟩ : syracuseStep 1334195 = 2001293) B2001293
theorem B1334231 : Blo 591290 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B1498135 : Blo 591290 1498135 := bstep (se 1 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 1498135 = 2247203) B2247203
theorem B842827 : Blo 591290 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B1334411 : Blo 591290 1334411 := bstep (se 1 (by rfl) ⟨1000808, by rfl⟩ : syracuseStep 1334411 = 2001617) B2001617
theorem B3431575 : Blo 591290 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B1334465 : Blo 591290 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B1268939 : Blo 591290 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B7625933 : Blo 591290 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B1334681 : Blo 591290 1334681 := bstep (se 2 (by rfl) ⟨500505, by rfl⟩ : syracuseStep 1334681 = 1001011) B1001011
theorem B1498571 : Blo 591290 1498571 := bstep (se 1 (by rfl) ⟨1123928, by rfl⟩ : syracuseStep 1498571 = 2247857) B2247857
theorem B1334771 : Blo 591290 1334771 := bstep (se 1 (by rfl) ⟨1001078, by rfl⟩ : syracuseStep 1334771 = 2002157) B2002157
theorem B1334807 : Blo 591290 1334807 := bstep (se 1 (by rfl) ⟨1001105, by rfl⟩ : syracuseStep 1334807 = 2002211) B2002211
theorem B5693003 : Blo 591290 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B1334987 : Blo 591290 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B1335041 : Blo 591290 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B1498945 : Blo 591290 1498945 := bstep (se 2 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 1498945 = 1124209) B1124209
theorem B8576867 : Blo 591290 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B2252717 : Blo 591290 2252717 := bstep (se 3 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 2252717 = 844769) B844769
theorem B1335257 : Blo 591290 1335257 := bstep (se 2 (by rfl) ⟨500721, by rfl⟩ : syracuseStep 1335257 = 1001443) B1001443
theorem B1335347 : Blo 591290 1335347 := bstep (se 1 (by rfl) ⟨1001510, by rfl⟩ : syracuseStep 1335347 = 2003021) B2003021
theorem B843863 : Blo 591290 843863 := bstep (se 1 (by rfl) ⟨632897, by rfl⟩ : syracuseStep 843863 = 1265795) B1265795
theorem B1335383 : Blo 591290 1335383 := bstep (se 1 (by rfl) ⟨1001537, by rfl⟩ : syracuseStep 1335383 = 2003075) B2003075
theorem B3006557 : Blo 591290 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B1269913 : Blo 591290 1269913 := bstep (se 2 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 1269913 = 952435) B952435
theorem B1335563 : Blo 591290 1335563 := bstep (se 1 (by rfl) ⟨1001672, by rfl⟩ : syracuseStep 1335563 = 2003345) B2003345
theorem B844057 : Blo 591290 844057 := bstep (se 2 (by rfl) ⟨316521, by rfl⟩ : syracuseStep 844057 = 633043) B633043
theorem B1335617 : Blo 591290 1335617 := bstep (se 2 (by rfl) ⟨500856, by rfl⟩ : syracuseStep 1335617 = 1001713) B1001713
theorem B7594357 : Blo 591290 7594357 := bstep (se 5 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 7594357 = 711971) B711971
theorem B1499543 : Blo 591290 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B1270169 : Blo 591290 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B1335833 : Blo 591290 1335833 := bstep (se 2 (by rfl) ⟨500937, by rfl⟩ : syracuseStep 1335833 = 1001875) B1001875
theorem B1335923 : Blo 591290 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B1335959 : Blo 591290 1335959 := bstep (se 1 (by rfl) ⟨1001969, by rfl⟩ : syracuseStep 1335959 = 2003939) B2003939
theorem B2253491 : Blo 591290 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B1270579 : Blo 591290 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1336139 : Blo 591290 1336139 := bstep (se 1 (by rfl) ⟨1002104, by rfl⟩ : syracuseStep 1336139 = 2004209) B2004209
theorem B7725941 : Blo 591290 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B1336193 : Blo 591290 1336193 := bstep (se 2 (by rfl) ⟨501072, by rfl⟩ : syracuseStep 1336193 = 1002145) B1002145
theorem B1205273 : Blo 591290 1205273 := bstep (se 2 (by rfl) ⟨451977, by rfl⟩ : syracuseStep 1205273 = 903955) B903955
theorem B1336409 : Blo 591290 1336409 := bstep (se 2 (by rfl) ⟨501153, by rfl⟩ : syracuseStep 1336409 = 1002307) B1002307
theorem B3433565 : Blo 591290 3433565 := bstep (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) B1287587
theorem B1336499 : Blo 591290 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B1500353 : Blo 591290 1500353 := bstep (se 2 (by rfl) ⟨562632, by rfl⟩ : syracuseStep 1500353 = 1125265) B1125265
theorem B1336535 : Blo 591290 1336535 := bstep (se 1 (by rfl) ⟨1002401, by rfl⟩ : syracuseStep 1336535 = 2004803) B2004803
theorem B1336715 : Blo 591290 1336715 := bstep (se 1 (by rfl) ⟨1002536, by rfl⟩ : syracuseStep 1336715 = 2005073) B2005073
theorem B1598899 : Blo 591290 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1336769 : Blo 591290 1336769 := bstep (se 2 (by rfl) ⟨501288, by rfl⟩ : syracuseStep 1336769 = 1002577) B1002577
theorem B92431813 : Blo 591290 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B1271297 : Blo 591290 1271297 := bstep (se 2 (by rfl) ⟨476736, by rfl⟩ : syracuseStep 1271297 = 953473) B953473
theorem B1336985 : Blo 591290 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B845515 : Blo 591290 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B1500889 : Blo 591290 1500889 := bstep (se 2 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 1500889 = 1125667) B1125667
theorem B1337075 : Blo 591290 1337075 := bstep (se 1 (by rfl) ⟨1002806, by rfl⟩ : syracuseStep 1337075 = 2005613) B2005613
theorem B1337111 : Blo 591290 1337111 := bstep (se 1 (by rfl) ⟨1002833, by rfl⟩ : syracuseStep 1337111 = 2005667) B2005667
theorem B21718961 : Blo 591290 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B1894337 : Blo 591290 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B1337291 : Blo 591290 1337291 := bstep (se 1 (by rfl) ⟨1002968, by rfl⟩ : syracuseStep 1337291 = 2005937) B2005937
theorem B1337345 : Blo 591290 1337345 := bstep (se 2 (by rfl) ⟨501504, by rfl⟩ : syracuseStep 1337345 = 1003009) B1003009
theorem B1828939 : Blo 591290 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B2254979 : Blo 591290 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B3008663 : Blo 591290 3008663 := bstep (se 1 (by rfl) ⟨2256497, by rfl⟩ : syracuseStep 3008663 = 4512995) B4512995
theorem B1337561 : Blo 591290 1337561 := bstep (se 2 (by rfl) ⟨501585, by rfl⟩ : syracuseStep 1337561 = 1003171) B1003171
theorem B1337651 : Blo 591290 1337651 := bstep (se 1 (by rfl) ⟨1003238, by rfl⟩ : syracuseStep 1337651 = 2006477) B2006477
theorem B2845003 : Blo 591290 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B1337687 : Blo 591290 1337687 := bstep (se 1 (by rfl) ⟨1003265, by rfl⟩ : syracuseStep 1337687 = 2006531) B2006531
theorem B3369347 : Blo 591290 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B1337867 : Blo 591290 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B4516397 : Blo 591290 4516397 := bstep (se 3 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 4516397 = 1693649) B1693649
theorem B1337921 : Blo 591290 1337921 := bstep (se 2 (by rfl) ⟨501720, by rfl⟩ : syracuseStep 1337921 = 1003441) B1003441
theorem B2255435 : Blo 591290 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B6744707 : Blo 591290 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B1141427 : Blo 591290 1141427 := bstep (se 1 (by rfl) ⟨856070, by rfl⟩ : syracuseStep 1141427 = 1712141) B1712141
theorem B2255633 : Blo 591290 2255633 := bstep (se 2 (by rfl) ⟨845862, by rfl⟩ : syracuseStep 2255633 = 1691725) B1691725
theorem B1338137 : Blo 591290 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B1502003 : Blo 591290 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1895233 : Blo 591290 1895233 := bstep (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) B1421425
theorem B1338227 : Blo 591290 1338227 := bstep (se 1 (by rfl) ⟨1003670, by rfl⟩ : syracuseStep 1338227 = 2007341) B2007341
theorem B1338263 : Blo 591290 1338263 := bstep (se 1 (by rfl) ⟨1003697, by rfl⟩ : syracuseStep 1338263 = 2007395) B2007395
theorem B1338443 : Blo 591290 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B1502297 : Blo 591290 1502297 := bstep (se 2 (by rfl) ⟨563361, by rfl⟩ : syracuseStep 1502297 = 1126723) B1126723
theorem B1338497 : Blo 591290 1338497 := bstep (se 2 (by rfl) ⟨501936, by rfl⟩ : syracuseStep 1338497 = 1003873) B1003873
theorem B748759 : Blo 591290 748759 := bstep (se 1 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 748759 = 1123139) B1123139
theorem B1338713 : Blo 591290 1338713 := bstep (se 2 (by rfl) ⟨502017, by rfl⟩ : syracuseStep 1338713 = 1004035) B1004035
theorem B1338803 : Blo 591290 1338803 := bstep (se 1 (by rfl) ⟨1004102, by rfl⟩ : syracuseStep 1338803 = 2008205) B2008205
theorem B1338839 : Blo 591290 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B1600985 : Blo 591290 1600985 := bstep (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) B1200739
theorem B2256407 : Blo 591290 2256407 := bstep (se 1 (by rfl) ⟨1692305, by rfl⟩ : syracuseStep 2256407 = 3384611) B3384611
theorem B1601117 : Blo 591290 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B1339019 : Blo 591290 1339019 := bstep (se 1 (by rfl) ⟨1004264, by rfl⟩ : syracuseStep 1339019 = 2008529) B2008529
theorem B1339073 : Blo 591290 1339073 := bstep (se 2 (by rfl) ⟨502152, by rfl⟩ : syracuseStep 1339073 = 1004305) B1004305
theorem B2256605 : Blo 591290 2256605 := bstep (se 3 (by rfl) ⟨423113, by rfl⟩ : syracuseStep 2256605 = 846227) B846227
theorem B4878085 : Blo 591290 4878085 := bstep (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) B914641
theorem B1339289 : Blo 591290 1339289 := bstep (se 2 (by rfl) ⟨502233, by rfl⟩ : syracuseStep 1339289 = 1004467) B1004467
theorem B1339379 : Blo 591290 1339379 := bstep (se 1 (by rfl) ⟨1004534, by rfl⟩ : syracuseStep 1339379 = 2009069) B2009069
theorem B1896797 : Blo 591290 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B684427 : Blo 591290 684427 := bstep (se 1 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 684427 = 1026641) B1026641
theorem B2028107 : Blo 591290 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B1503947 : Blo 591290 1503947 := bstep (se 1 (by rfl) ⟨1127960, by rfl⟩ : syracuseStep 1503947 = 2255921) B2255921
theorem B750475 : Blo 591290 750475 := bstep (se 1 (by rfl) ⟨562856, by rfl⟩ : syracuseStep 750475 = 1125713) B1125713
theorem B5075891 : Blo 591290 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B1143767 : Blo 591290 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1799347 : Blo 591290 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B8123597 : Blo 591290 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B8352973 : Blo 591290 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1996055 : Blo 591290 1996055 := bstep (se 1 (by rfl) ⟨1497041, by rfl⟩ : syracuseStep 1996055 = 2994083) B2994083
theorem B5076269 : Blo 591290 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B2160145 : Blo 591290 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B5404195 : Blo 591290 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B1603147 : Blo 591290 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B2258563 : Blo 591290 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B3012227 : Blo 591290 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B1504919 : Blo 591290 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B685751 : Blo 591290 685751 := bstep (se 1 (by rfl) ⟨514313, by rfl⟩ : syracuseStep 685751 = 1028627) B1028627
theorem B1996595 : Blo 591290 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B751447 : Blo 591290 751447 := bstep (se 1 (by rfl) ⟨563585, by rfl⟩ : syracuseStep 751447 = 1127171) B1127171
theorem B4061029 : Blo 591290 4061029 := bstep (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) B761443
theorem B2160557 : Blo 591290 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B11564977 : Blo 591290 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B2258867 : Blo 591290 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B3799001 : Blo 591290 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B1996865 : Blo 591290 1996865 := bstep (se 2 (by rfl) ⟨748824, by rfl⟩ : syracuseStep 1996865 = 1497649) B1497649
theorem B1505587 : Blo 591290 1505587 := bstep (se 1 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 1505587 = 2258381) B2258381
theorem B4520285 : Blo 591290 4520285 := bstep (se 3 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 4520285 = 1695107) B1695107
theorem B1505729 : Blo 591290 1505729 := bstep (se 2 (by rfl) ⟨564648, by rfl⟩ : syracuseStep 1505729 = 1129297) B1129297
theorem B2259521 : Blo 591290 2259521 := bstep (se 2 (by rfl) ⟨847320, by rfl⟩ : syracuseStep 2259521 = 1694641) B1694641
theorem B7600715 : Blo 591290 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B1997405 : Blo 591290 1997405 := bstep (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) B749027
theorem B752267 : Blo 591290 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B11369393 : Blo 591290 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B1604531 : Blo 591290 1604531 := bstep (se 1 (by rfl) ⟨1203398, by rfl⟩ : syracuseStep 1604531 = 2406797) B2406797
theorem B2849867 : Blo 591290 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B752971 : Blo 591290 752971 := bstep (se 1 (by rfl) ⟨564728, by rfl⟩ : syracuseStep 752971 = 1129457) B1129457
theorem B3800641 : Blo 591290 3800641 := bstep (se 2 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 3800641 = 2850481) B2850481
theorem B753239 : Blo 591290 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B3374723 : Blo 591290 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B1998539 : Blo 591290 1998539 := bstep (se 1 (by rfl) ⟨1498904, by rfl⟩ : syracuseStep 1998539 = 2997809) B2997809
theorem B950039 : Blo 591290 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B2850653 : Blo 591290 2850653 := bstep (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) B1068995
theorem B1605527 : Blo 591290 1605527 := bstep (se 1 (by rfl) ⟨1204145, by rfl⟩ : syracuseStep 1605527 = 2408291) B2408291
theorem B950231 : Blo 591290 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B1998809 : Blo 591290 1998809 := bstep (se 2 (by rfl) ⟨749553, by rfl⟩ : syracuseStep 1998809 = 1499107) B1499107
theorem B3211655 : Blo 591290 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B10125809 : Blo 591290 10125809 := bstep (se 2 (by rfl) ⟨3797178, by rfl⟩ : syracuseStep 10125809 = 7594357) B7594357
theorem B5079581 : Blo 591290 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B1999403 : Blo 591290 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B6521573 : Blo 591290 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B5080265 : Blo 591290 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B6161645 : Blo 591290 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B591291 : Blo 591290 591291 := bstep (se 1 (by rfl) ⟨443468, by rfl⟩ : syracuseStep 591291 = 886937) B886937
theorem B591367 : Blo 591290 591367 := bstep (se 1 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 591367 = 887051) B887051
theorem B591375 : Blo 591290 591375 := bstep (se 1 (by rfl) ⟨443531, by rfl⟩ : syracuseStep 591375 = 887063) B887063
theorem B591419 : Blo 591290 591419 := bstep (se 1 (by rfl) ⟨443564, by rfl⟩ : syracuseStep 591419 = 887129) B887129
theorem B5080643 : Blo 591290 5080643 := bstep (se 1 (by rfl) ⟨3810482, by rfl⟩ : syracuseStep 5080643 = 7620965) B7620965
theorem B1902167 : Blo 591290 1902167 := bstep (se 1 (by rfl) ⟨1426625, by rfl⟩ : syracuseStep 1902167 = 2853251) B2853251
theorem B591495 : Blo 591290 591495 := bstep (se 1 (by rfl) ⟨443621, by rfl⟩ : syracuseStep 591495 = 887243) B887243
theorem B591503 : Blo 591290 591503 := bstep (se 1 (by rfl) ⟨443627, by rfl⟩ : syracuseStep 591503 = 887255) B887255
theorem B591547 : Blo 591290 591547 := bstep (se 1 (by rfl) ⟨443660, by rfl⟩ : syracuseStep 591547 = 887321) B887321
theorem B591623 : Blo 591290 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B591631 : Blo 591290 591631 := bstep (se 1 (by rfl) ⟨443723, by rfl⟩ : syracuseStep 591631 = 887447) B887447
theorem B591675 : Blo 591290 591675 := bstep (se 1 (by rfl) ⟨443756, by rfl⟩ : syracuseStep 591675 = 887513) B887513
theorem B2000699 : Blo 591290 2000699 := bstep (se 1 (by rfl) ⟨1500524, by rfl⟩ : syracuseStep 2000699 = 3001049) B3001049
theorem B591751 : Blo 591290 591751 := bstep (se 1 (by rfl) ⟨443813, by rfl⟩ : syracuseStep 591751 = 887627) B887627
theorem B591759 : Blo 591290 591759 := bstep (se 1 (by rfl) ⟨443819, by rfl⟩ : syracuseStep 591759 = 887639) B887639
theorem B2131865 : Blo 591290 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B4818851 : Blo 591290 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B123242417 : Blo 591290 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B591803 : Blo 591290 591803 := bstep (se 1 (by rfl) ⟨443852, by rfl⟩ : syracuseStep 591803 = 887705) B887705
theorem B722875 : Blo 591290 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B591879 : Blo 591290 591879 := bstep (se 1 (by rfl) ⟨443909, by rfl⟩ : syracuseStep 591879 = 887819) B887819
theorem B591887 : Blo 591290 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B591931 : Blo 591290 591931 := bstep (se 1 (by rfl) ⟨443948, by rfl⟩ : syracuseStep 591931 = 887897) B887897
theorem B6522967 : Blo 591290 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B592007 : Blo 591290 592007 := bstep (se 1 (by rfl) ⟨444005, by rfl⟩ : syracuseStep 592007 = 888011) B888011
theorem B592015 : Blo 591290 592015 := bstep (se 1 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 592015 = 888023) B888023
theorem B886955 : Blo 591290 886955 := bstep (se 1 (by rfl) ⟨665216, by rfl⟩ : syracuseStep 886955 = 1330433) B1330433
theorem B592059 : Blo 591290 592059 := bstep (se 1 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 592059 = 888089) B888089
theorem B886985 : Blo 591290 886985 := bstep (se 2 (by rfl) ⟨332619, by rfl⟩ : syracuseStep 886985 = 665239) B665239
theorem B1902793 : Blo 591290 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B592135 : Blo 591290 592135 := bstep (se 1 (by rfl) ⟨444101, by rfl⟩ : syracuseStep 592135 = 888203) B888203
theorem B592143 : Blo 591290 592143 := bstep (se 1 (by rfl) ⟨444107, by rfl⟩ : syracuseStep 592143 = 888215) B888215
theorem B2001185 : Blo 591290 2001185 := bstep (se 2 (by rfl) ⟨750444, by rfl⟩ : syracuseStep 2001185 = 1500889) B1500889
theorem B887099 : Blo 591290 887099 := bstep (se 1 (by rfl) ⟨665324, by rfl⟩ : syracuseStep 887099 = 1330649) B1330649
theorem B592187 : Blo 591290 592187 := bstep (se 1 (by rfl) ⟨444140, by rfl⟩ : syracuseStep 592187 = 888281) B888281
theorem B887159 : Blo 591290 887159 := bstep (se 1 (by rfl) ⟨665369, by rfl⟩ : syracuseStep 887159 = 1330739) B1330739
theorem B854407 : Blo 591290 854407 := bstep (se 1 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 854407 = 1281611) B1281611
theorem B592263 : Blo 591290 592263 := bstep (se 1 (by rfl) ⟨444197, by rfl⟩ : syracuseStep 592263 = 888395) B888395
theorem B887183 : Blo 591290 887183 := bstep (se 1 (by rfl) ⟨665387, by rfl⟩ : syracuseStep 887183 = 1330775) B1330775
theorem B592271 : Blo 591290 592271 := bstep (se 1 (by rfl) ⟨444203, by rfl⟩ : syracuseStep 592271 = 888407) B888407
theorem B887225 : Blo 591290 887225 := bstep (se 2 (by rfl) ⟨332709, by rfl⟩ : syracuseStep 887225 = 665419) B665419
theorem B592315 : Blo 591290 592315 := bstep (se 1 (by rfl) ⟨444236, by rfl⟩ : syracuseStep 592315 = 888473) B888473
theorem B6425041 : Blo 591290 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B887303 : Blo 591290 887303 := bstep (se 1 (by rfl) ⟨665477, by rfl⟩ : syracuseStep 887303 = 1330955) B1330955
theorem B592391 : Blo 591290 592391 := bstep (se 1 (by rfl) ⟨444293, by rfl⟩ : syracuseStep 592391 = 888587) B888587
theorem B592399 : Blo 591290 592399 := bstep (se 1 (by rfl) ⟨444299, by rfl⟩ : syracuseStep 592399 = 888599) B888599
theorem B1444385 : Blo 591290 1444385 := bstep (se 2 (by rfl) ⟨541644, by rfl⟩ : syracuseStep 1444385 = 1083289) B1083289
theorem B887339 : Blo 591290 887339 := bstep (se 1 (by rfl) ⟨665504, by rfl⟩ : syracuseStep 887339 = 1331009) B1331009
theorem B592443 : Blo 591290 592443 := bstep (se 1 (by rfl) ⟨444332, by rfl⟩ : syracuseStep 592443 = 888665) B888665
theorem B3050045 : Blo 591290 3050045 := bstep (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) B1143767
theorem B887369 : Blo 591290 887369 := bstep (se 2 (by rfl) ⟨332763, by rfl⟩ : syracuseStep 887369 = 665527) B665527
theorem B592519 : Blo 591290 592519 := bstep (se 1 (by rfl) ⟨444389, by rfl⟩ : syracuseStep 592519 = 888779) B888779
theorem B592527 : Blo 591290 592527 := bstep (se 1 (by rfl) ⟨444395, by rfl⟩ : syracuseStep 592527 = 888791) B888791
theorem B887483 : Blo 591290 887483 := bstep (se 1 (by rfl) ⟨665612, by rfl⟩ : syracuseStep 887483 = 1331225) B1331225
theorem B592571 : Blo 591290 592571 := bstep (se 1 (by rfl) ⟨444428, by rfl⟩ : syracuseStep 592571 = 888857) B888857
theorem B887543 : Blo 591290 887543 := bstep (se 1 (by rfl) ⟨665657, by rfl⟩ : syracuseStep 887543 = 1331315) B1331315
theorem B592647 : Blo 591290 592647 := bstep (se 1 (by rfl) ⟨444485, by rfl⟩ : syracuseStep 592647 = 888971) B888971
theorem B887567 : Blo 591290 887567 := bstep (se 1 (by rfl) ⟨665675, by rfl⟩ : syracuseStep 887567 = 1331351) B1331351
theorem B592655 : Blo 591290 592655 := bstep (se 1 (by rfl) ⟨444491, by rfl⟩ : syracuseStep 592655 = 888983) B888983
theorem B887609 : Blo 591290 887609 := bstep (se 2 (by rfl) ⟨332853, by rfl⟩ : syracuseStep 887609 = 665707) B665707
theorem B592699 : Blo 591290 592699 := bstep (se 1 (by rfl) ⟨444524, by rfl⟩ : syracuseStep 592699 = 889049) B889049
theorem B1608509 : Blo 591290 1608509 := bstep (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) B603191
theorem B2001779 : Blo 591290 2001779 := bstep (se 1 (by rfl) ⟨1501334, by rfl⟩ : syracuseStep 2001779 = 3002669) B3002669
theorem B887687 : Blo 591290 887687 := bstep (se 1 (by rfl) ⟨665765, by rfl⟩ : syracuseStep 887687 = 1331531) B1331531
theorem B592775 : Blo 591290 592775 := bstep (se 1 (by rfl) ⟨444581, by rfl⟩ : syracuseStep 592775 = 889163) B889163
theorem B592783 : Blo 591290 592783 := bstep (se 1 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 592783 = 889175) B889175
theorem B887723 : Blo 591290 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B592827 : Blo 591290 592827 := bstep (se 1 (by rfl) ⟨444620, by rfl⟩ : syracuseStep 592827 = 889241) B889241
theorem B887753 : Blo 591290 887753 := bstep (se 2 (by rfl) ⟨332907, by rfl⟩ : syracuseStep 887753 = 665815) B665815
theorem B592903 : Blo 591290 592903 := bstep (se 1 (by rfl) ⟨444677, by rfl⟩ : syracuseStep 592903 = 889355) B889355
theorem B592911 : Blo 591290 592911 := bstep (se 1 (by rfl) ⟨444683, by rfl⟩ : syracuseStep 592911 = 889367) B889367
theorem B887867 : Blo 591290 887867 := bstep (se 1 (by rfl) ⟨665900, by rfl⟩ : syracuseStep 887867 = 1331801) B1331801
theorem B592955 : Blo 591290 592955 := bstep (se 1 (by rfl) ⟨444716, by rfl⟩ : syracuseStep 592955 = 889433) B889433
theorem B887927 : Blo 591290 887927 := bstep (se 1 (by rfl) ⟨665945, by rfl⟩ : syracuseStep 887927 = 1331891) B1331891
theorem B593031 : Blo 591290 593031 := bstep (se 1 (by rfl) ⟨444773, by rfl⟩ : syracuseStep 593031 = 889547) B889547
theorem B887951 : Blo 591290 887951 := bstep (se 1 (by rfl) ⟨665963, by rfl⟩ : syracuseStep 887951 = 1331927) B1331927
theorem B593039 : Blo 591290 593039 := bstep (se 1 (by rfl) ⟨444779, by rfl⟩ : syracuseStep 593039 = 889559) B889559
theorem B887993 : Blo 591290 887993 := bstep (se 2 (by rfl) ⟨332997, by rfl⟩ : syracuseStep 887993 = 665995) B665995
theorem B593083 : Blo 591290 593083 := bstep (se 1 (by rfl) ⟨444812, by rfl⟩ : syracuseStep 593083 = 889625) B889625
theorem B888071 : Blo 591290 888071 := bstep (se 1 (by rfl) ⟨666053, by rfl⟩ : syracuseStep 888071 = 1332107) B1332107
theorem B593159 : Blo 591290 593159 := bstep (se 1 (by rfl) ⟨444869, by rfl⟩ : syracuseStep 593159 = 889739) B889739
theorem B593167 : Blo 591290 593167 := bstep (se 1 (by rfl) ⟨444875, by rfl⟩ : syracuseStep 593167 = 889751) B889751
theorem B11373857 : Blo 591290 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B888107 : Blo 591290 888107 := bstep (se 1 (by rfl) ⟨666080, by rfl⟩ : syracuseStep 888107 = 1332161) B1332161
theorem B593211 : Blo 591290 593211 := bstep (se 1 (by rfl) ⟨444908, by rfl⟩ : syracuseStep 593211 = 889817) B889817
theorem B888137 : Blo 591290 888137 := bstep (se 2 (by rfl) ⟨333051, by rfl⟩ : syracuseStep 888137 = 666103) B666103
theorem B593287 : Blo 591290 593287 := bstep (se 1 (by rfl) ⟨444965, by rfl⟩ : syracuseStep 593287 = 889931) B889931
theorem B593295 : Blo 591290 593295 := bstep (se 1 (by rfl) ⟨444971, by rfl⟩ : syracuseStep 593295 = 889943) B889943
theorem B4263353 : Blo 591290 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B888251 : Blo 591290 888251 := bstep (se 1 (by rfl) ⟨666188, by rfl⟩ : syracuseStep 888251 = 1332377) B1332377
theorem B593339 : Blo 591290 593339 := bstep (se 1 (by rfl) ⟨445004, by rfl⟩ : syracuseStep 593339 = 890009) B890009
theorem B888311 : Blo 591290 888311 := bstep (se 1 (by rfl) ⟨666233, by rfl⟩ : syracuseStep 888311 = 1332467) B1332467
theorem B593415 : Blo 591290 593415 := bstep (se 1 (by rfl) ⟨445061, by rfl⟩ : syracuseStep 593415 = 890123) B890123
theorem B888335 : Blo 591290 888335 := bstep (se 1 (by rfl) ⟨666251, by rfl⟩ : syracuseStep 888335 = 1332503) B1332503
theorem B593423 : Blo 591290 593423 := bstep (se 1 (by rfl) ⟨445067, by rfl⟩ : syracuseStep 593423 = 890135) B890135
theorem B888377 : Blo 591290 888377 := bstep (se 2 (by rfl) ⟨333141, by rfl⟩ : syracuseStep 888377 = 666283) B666283
theorem B593467 : Blo 591290 593467 := bstep (se 1 (by rfl) ⟨445100, by rfl⟩ : syracuseStep 593467 = 890201) B890201
theorem B888455 : Blo 591290 888455 := bstep (se 1 (by rfl) ⟨666341, by rfl⟩ : syracuseStep 888455 = 1332683) B1332683
theorem B593543 : Blo 591290 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B593551 : Blo 591290 593551 := bstep (se 1 (by rfl) ⟨445163, by rfl⟩ : syracuseStep 593551 = 890327) B890327
theorem B888491 : Blo 591290 888491 := bstep (se 1 (by rfl) ⟨666368, by rfl⟩ : syracuseStep 888491 = 1332737) B1332737
theorem B593595 : Blo 591290 593595 := bstep (se 1 (by rfl) ⟨445196, by rfl⟩ : syracuseStep 593595 = 890393) B890393
theorem B888521 : Blo 591290 888521 := bstep (se 2 (by rfl) ⟨333195, by rfl⟩ : syracuseStep 888521 = 666391) B666391
theorem B2526977 : Blo 591290 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B593671 : Blo 591290 593671 := bstep (se 1 (by rfl) ⟨445253, by rfl⟩ : syracuseStep 593671 = 890507) B890507
theorem B593679 : Blo 591290 593679 := bstep (se 1 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 593679 = 890519) B890519
theorem B888635 : Blo 591290 888635 := bstep (se 1 (by rfl) ⟨666476, by rfl⟩ : syracuseStep 888635 = 1332953) B1332953
theorem B593723 : Blo 591290 593723 := bstep (se 1 (by rfl) ⟨445292, by rfl⟩ : syracuseStep 593723 = 890585) B890585
theorem B888695 : Blo 591290 888695 := bstep (se 1 (by rfl) ⟨666521, by rfl⟩ : syracuseStep 888695 = 1333043) B1333043
theorem B593799 : Blo 591290 593799 := bstep (se 1 (by rfl) ⟨445349, by rfl⟩ : syracuseStep 593799 = 890699) B890699
theorem B888719 : Blo 591290 888719 := bstep (se 1 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 888719 = 1333079) B1333079
theorem B593807 : Blo 591290 593807 := bstep (se 1 (by rfl) ⟨445355, by rfl⟩ : syracuseStep 593807 = 890711) B890711
theorem B3379097 : Blo 591290 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B888761 : Blo 591290 888761 := bstep (se 2 (by rfl) ⟨333285, by rfl⟩ : syracuseStep 888761 = 666571) B666571
theorem B593851 : Blo 591290 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B888839 : Blo 591290 888839 := bstep (se 1 (by rfl) ⟨666629, by rfl⟩ : syracuseStep 888839 = 1333259) B1333259
theorem B593927 : Blo 591290 593927 := bstep (se 1 (by rfl) ⟨445445, by rfl⟩ : syracuseStep 593927 = 890891) B890891
theorem B593935 : Blo 591290 593935 := bstep (se 1 (by rfl) ⟨445451, by rfl⟩ : syracuseStep 593935 = 890903) B890903
theorem B888875 : Blo 591290 888875 := bstep (se 1 (by rfl) ⟨666656, by rfl⟩ : syracuseStep 888875 = 1333313) B1333313
theorem B593979 : Blo 591290 593979 := bstep (se 1 (by rfl) ⟨445484, by rfl⟩ : syracuseStep 593979 = 890969) B890969
theorem B888905 : Blo 591290 888905 := bstep (se 2 (by rfl) ⟨333339, by rfl⟩ : syracuseStep 888905 = 666679) B666679
theorem B594055 : Blo 591290 594055 := bstep (se 1 (by rfl) ⟨445541, by rfl⟩ : syracuseStep 594055 = 891083) B891083
theorem B594063 : Blo 591290 594063 := bstep (se 1 (by rfl) ⟨445547, by rfl⟩ : syracuseStep 594063 = 891095) B891095
theorem B889019 : Blo 591290 889019 := bstep (se 1 (by rfl) ⟨666764, by rfl⟩ : syracuseStep 889019 = 1333529) B1333529
theorem B594107 : Blo 591290 594107 := bstep (se 1 (by rfl) ⟨445580, by rfl⟩ : syracuseStep 594107 = 891161) B891161
theorem B889079 : Blo 591290 889079 := bstep (se 1 (by rfl) ⟨666809, by rfl⟩ : syracuseStep 889079 = 1333619) B1333619
theorem B594183 : Blo 591290 594183 := bstep (se 1 (by rfl) ⟨445637, by rfl⟩ : syracuseStep 594183 = 891275) B891275
theorem B889103 : Blo 591290 889103 := bstep (se 1 (by rfl) ⟨666827, by rfl⟩ : syracuseStep 889103 = 1333655) B1333655
theorem B594191 : Blo 591290 594191 := bstep (se 1 (by rfl) ⟨445643, by rfl⟩ : syracuseStep 594191 = 891287) B891287
theorem B889145 : Blo 591290 889145 := bstep (se 2 (by rfl) ⟨333429, by rfl⟩ : syracuseStep 889145 = 666859) B666859
theorem B594235 : Blo 591290 594235 := bstep (se 1 (by rfl) ⟨445676, by rfl⟩ : syracuseStep 594235 = 891353) B891353
theorem B594311 : Blo 591290 594311 := bstep (se 1 (by rfl) ⟨445733, by rfl⟩ : syracuseStep 594311 = 891467) B891467
theorem B889223 : Blo 591290 889223 := bstep (se 1 (by rfl) ⟨666917, by rfl⟩ : syracuseStep 889223 = 1333835) B1333835
theorem B594319 : Blo 591290 594319 := bstep (se 1 (by rfl) ⟨445739, by rfl⟩ : syracuseStep 594319 = 891479) B891479
theorem B889259 : Blo 591290 889259 := bstep (se 1 (by rfl) ⟨666944, by rfl⟩ : syracuseStep 889259 = 1333889) B1333889
theorem B594363 : Blo 591290 594363 := bstep (se 1 (by rfl) ⟨445772, by rfl⟩ : syracuseStep 594363 = 891545) B891545
theorem B889289 : Blo 591290 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B594439 : Blo 591290 594439 := bstep (se 1 (by rfl) ⟨445829, by rfl⟩ : syracuseStep 594439 = 891659) B891659
theorem B594447 : Blo 591290 594447 := bstep (se 1 (by rfl) ⟨445835, by rfl⟩ : syracuseStep 594447 = 891671) B891671
theorem B889403 : Blo 591290 889403 := bstep (se 1 (by rfl) ⟨667052, by rfl⟩ : syracuseStep 889403 = 1334105) B1334105
theorem B594491 : Blo 591290 594491 := bstep (se 1 (by rfl) ⟨445868, by rfl⟩ : syracuseStep 594491 = 891737) B891737
theorem B889463 : Blo 591290 889463 := bstep (se 1 (by rfl) ⟨667097, by rfl⟩ : syracuseStep 889463 = 1334195) B1334195
theorem B594567 : Blo 591290 594567 := bstep (se 1 (by rfl) ⟨445925, by rfl⟩ : syracuseStep 594567 = 891851) B891851
theorem B889487 : Blo 591290 889487 := bstep (se 1 (by rfl) ⟨667115, by rfl⟩ : syracuseStep 889487 = 1334231) B1334231
theorem B594575 : Blo 591290 594575 := bstep (se 1 (by rfl) ⟨445931, by rfl⟩ : syracuseStep 594575 = 891863) B891863
theorem B889529 : Blo 591290 889529 := bstep (se 2 (by rfl) ⟨333573, by rfl⟩ : syracuseStep 889529 = 667147) B667147
theorem B594619 : Blo 591290 594619 := bstep (se 1 (by rfl) ⟨445964, by rfl⟩ : syracuseStep 594619 = 891929) B891929
theorem B889607 : Blo 591290 889607 := bstep (se 1 (by rfl) ⟨667205, by rfl⟩ : syracuseStep 889607 = 1334411) B1334411
theorem B594695 : Blo 591290 594695 := bstep (se 1 (by rfl) ⟨446021, by rfl⟩ : syracuseStep 594695 = 892043) B892043
theorem B594703 : Blo 591290 594703 := bstep (se 1 (by rfl) ⟨446027, by rfl⟩ : syracuseStep 594703 = 892055) B892055
theorem B889643 : Blo 591290 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B5083955 : Blo 591290 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B594747 : Blo 591290 594747 := bstep (se 1 (by rfl) ⟨446060, by rfl⟩ : syracuseStep 594747 = 892121) B892121
theorem B889673 : Blo 591290 889673 := bstep (se 2 (by rfl) ⟨333627, by rfl⟩ : syracuseStep 889673 = 667255) B667255
theorem B594823 : Blo 591290 594823 := bstep (se 1 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 594823 = 892235) B892235
theorem B594831 : Blo 591290 594831 := bstep (se 1 (by rfl) ⟨446123, by rfl⟩ : syracuseStep 594831 = 892247) B892247
theorem B889787 : Blo 591290 889787 := bstep (se 1 (by rfl) ⟨667340, by rfl⟩ : syracuseStep 889787 = 1334681) B1334681
theorem B594875 : Blo 591290 594875 := bstep (se 1 (by rfl) ⟨446156, by rfl⟩ : syracuseStep 594875 = 892313) B892313
theorem B889847 : Blo 591290 889847 := bstep (se 1 (by rfl) ⟨667385, by rfl⟩ : syracuseStep 889847 = 1334771) B1334771
theorem B594951 : Blo 591290 594951 := bstep (se 1 (by rfl) ⟨446213, by rfl⟩ : syracuseStep 594951 = 892427) B892427
theorem B889871 : Blo 591290 889871 := bstep (se 1 (by rfl) ⟨667403, by rfl⟩ : syracuseStep 889871 = 1334807) B1334807
theorem B594959 : Blo 591290 594959 := bstep (se 1 (by rfl) ⟨446219, by rfl⟩ : syracuseStep 594959 = 892439) B892439
theorem B889913 : Blo 591290 889913 := bstep (se 2 (by rfl) ⟨333717, by rfl⟩ : syracuseStep 889913 = 667435) B667435
theorem B595003 : Blo 591290 595003 := bstep (se 1 (by rfl) ⟨446252, by rfl⟩ : syracuseStep 595003 = 892505) B892505
theorem B889991 : Blo 591290 889991 := bstep (se 1 (by rfl) ⟨667493, by rfl⟩ : syracuseStep 889991 = 1334987) B1334987
theorem B595079 : Blo 591290 595079 := bstep (se 1 (by rfl) ⟨446309, by rfl⟩ : syracuseStep 595079 = 892619) B892619
theorem B595087 : Blo 591290 595087 := bstep (se 1 (by rfl) ⟨446315, by rfl⟩ : syracuseStep 595087 = 892631) B892631
theorem B890027 : Blo 591290 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B595131 : Blo 591290 595131 := bstep (se 1 (by rfl) ⟨446348, by rfl⟩ : syracuseStep 595131 = 892697) B892697
theorem B890057 : Blo 591290 890057 := bstep (se 2 (by rfl) ⟨333771, by rfl⟩ : syracuseStep 890057 = 667543) B667543
theorem B595207 : Blo 591290 595207 := bstep (se 1 (by rfl) ⟨446405, by rfl⟩ : syracuseStep 595207 = 892811) B892811
theorem B595215 : Blo 591290 595215 := bstep (se 1 (by rfl) ⟨446411, by rfl⟩ : syracuseStep 595215 = 892823) B892823
theorem B890171 : Blo 591290 890171 := bstep (se 1 (by rfl) ⟨667628, by rfl⟩ : syracuseStep 890171 = 1335257) B1335257
theorem B595259 : Blo 591290 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B890231 : Blo 591290 890231 := bstep (se 1 (by rfl) ⟨667673, by rfl⟩ : syracuseStep 890231 = 1335347) B1335347
theorem B890255 : Blo 591290 890255 := bstep (se 1 (by rfl) ⟨667691, by rfl⟩ : syracuseStep 890255 = 1335383) B1335383
theorem B2004371 : Blo 591290 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B890297 : Blo 591290 890297 := bstep (se 2 (by rfl) ⟨333861, by rfl⟩ : syracuseStep 890297 = 667723) B667723
theorem B890375 : Blo 591290 890375 := bstep (se 1 (by rfl) ⟨667781, by rfl⟩ : syracuseStep 890375 = 1335563) B1335563
theorem B890411 : Blo 591290 890411 := bstep (se 1 (by rfl) ⟨667808, by rfl⟩ : syracuseStep 890411 = 1335617) B1335617
theorem B890441 : Blo 591290 890441 := bstep (se 2 (by rfl) ⟨333915, by rfl⟩ : syracuseStep 890441 = 667831) B667831
theorem B890555 : Blo 591290 890555 := bstep (se 1 (by rfl) ⟨667916, by rfl⟩ : syracuseStep 890555 = 1335833) B1335833
theorem B890615 : Blo 591290 890615 := bstep (se 1 (by rfl) ⟨667961, by rfl⟩ : syracuseStep 890615 = 1335923) B1335923
theorem B890639 : Blo 591290 890639 := bstep (se 1 (by rfl) ⟨667979, by rfl⟩ : syracuseStep 890639 = 1335959) B1335959
theorem B890681 : Blo 591290 890681 := bstep (se 2 (by rfl) ⟨334005, by rfl⟩ : syracuseStep 890681 = 668011) B668011
theorem B5085017 : Blo 591290 5085017 := bstep (se 2 (by rfl) ⟨1906881, by rfl⟩ : syracuseStep 5085017 = 3813763) B3813763
theorem B890759 : Blo 591290 890759 := bstep (se 1 (by rfl) ⟨668069, by rfl⟩ : syracuseStep 890759 = 1336139) B1336139
theorem B5150627 : Blo 591290 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B890795 : Blo 591290 890795 := bstep (se 1 (by rfl) ⟨668096, by rfl⟩ : syracuseStep 890795 = 1336193) B1336193
theorem B890825 : Blo 591290 890825 := bstep (se 2 (by rfl) ⟨334059, by rfl⟩ : syracuseStep 890825 = 668119) B668119
theorem B890939 : Blo 591290 890939 := bstep (se 1 (by rfl) ⟨668204, by rfl⟩ : syracuseStep 890939 = 1336409) B1336409
theorem B890999 : Blo 591290 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B891023 : Blo 591290 891023 := bstep (se 1 (by rfl) ⟨668267, by rfl⟩ : syracuseStep 891023 = 1336535) B1336535
theorem B891065 : Blo 591290 891065 := bstep (se 2 (by rfl) ⟨334149, by rfl⟩ : syracuseStep 891065 = 668299) B668299
theorem B891143 : Blo 591290 891143 := bstep (se 1 (by rfl) ⟨668357, by rfl⟩ : syracuseStep 891143 = 1336715) B1336715
theorem B891179 : Blo 591290 891179 := bstep (se 1 (by rfl) ⟨668384, by rfl⟩ : syracuseStep 891179 = 1336769) B1336769
theorem B891209 : Blo 591290 891209 := bstep (se 2 (by rfl) ⟨334203, by rfl⟩ : syracuseStep 891209 = 668407) B668407
theorem B891323 : Blo 591290 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B891383 : Blo 591290 891383 := bstep (se 1 (by rfl) ⟨668537, by rfl⟩ : syracuseStep 891383 = 1337075) B1337075
theorem B891407 : Blo 591290 891407 := bstep (se 1 (by rfl) ⟨668555, by rfl⟩ : syracuseStep 891407 = 1337111) B1337111
theorem B891449 : Blo 591290 891449 := bstep (se 2 (by rfl) ⟨334293, by rfl⟩ : syracuseStep 891449 = 668587) B668587
theorem B1645171 : Blo 591290 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B891527 : Blo 591290 891527 := bstep (se 1 (by rfl) ⟨668645, by rfl⟩ : syracuseStep 891527 = 1337291) B1337291
theorem B891563 : Blo 591290 891563 := bstep (se 1 (by rfl) ⟨668672, by rfl⟩ : syracuseStep 891563 = 1337345) B1337345
theorem B891593 : Blo 591290 891593 := bstep (se 2 (by rfl) ⟨334347, by rfl⟩ : syracuseStep 891593 = 668695) B668695
theorem B2005775 : Blo 591290 2005775 := bstep (se 1 (by rfl) ⟨1504331, by rfl⟩ : syracuseStep 2005775 = 3008663) B3008663
theorem B891707 : Blo 591290 891707 := bstep (se 1 (by rfl) ⟨668780, by rfl⟩ : syracuseStep 891707 = 1337561) B1337561
theorem B891767 : Blo 591290 891767 := bstep (se 1 (by rfl) ⟨668825, by rfl⟩ : syracuseStep 891767 = 1337651) B1337651
theorem B891791 : Blo 591290 891791 := bstep (se 1 (by rfl) ⟨668843, by rfl⟩ : syracuseStep 891791 = 1337687) B1337687
theorem B5053337 : Blo 591290 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B2399129 : Blo 591290 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B891833 : Blo 591290 891833 := bstep (se 2 (by rfl) ⟨334437, by rfl⟩ : syracuseStep 891833 = 668875) B668875
theorem B891911 : Blo 591290 891911 := bstep (se 1 (by rfl) ⟨668933, by rfl⟩ : syracuseStep 891911 = 1337867) B1337867
theorem B2006045 : Blo 591290 2006045 := bstep (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) B752267
theorem B891947 : Blo 591290 891947 := bstep (se 1 (by rfl) ⟨668960, by rfl⟩ : syracuseStep 891947 = 1337921) B1337921
theorem B891977 : Blo 591290 891977 := bstep (se 2 (by rfl) ⟨334491, by rfl⟩ : syracuseStep 891977 = 668983) B668983
theorem B4496471 : Blo 591290 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B760951 : Blo 591290 760951 := bstep (se 1 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 760951 = 1141427) B1141427
theorem B892091 : Blo 591290 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B3808457 : Blo 591290 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B892151 : Blo 591290 892151 := bstep (se 1 (by rfl) ⟨669113, by rfl⟩ : syracuseStep 892151 = 1338227) B1338227
theorem B892175 : Blo 591290 892175 := bstep (se 1 (by rfl) ⟨669131, by rfl⟩ : syracuseStep 892175 = 1338263) B1338263
theorem B1809697 : Blo 591290 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B892217 : Blo 591290 892217 := bstep (se 2 (by rfl) ⟨334581, by rfl⟩ : syracuseStep 892217 = 669163) B669163
theorem B5709149 : Blo 591290 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B892295 : Blo 591290 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B892331 : Blo 591290 892331 := bstep (se 1 (by rfl) ⟨669248, by rfl⟩ : syracuseStep 892331 = 1338497) B1338497
theorem B2137529 : Blo 591290 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B1285561 : Blo 591290 1285561 := bstep (se 2 (by rfl) ⟨482085, by rfl⟩ : syracuseStep 1285561 = 964171) B964171
theorem B892361 : Blo 591290 892361 := bstep (se 2 (by rfl) ⟨334635, by rfl⟩ : syracuseStep 892361 = 669271) B669271
theorem B892475 : Blo 591290 892475 := bstep (se 1 (by rfl) ⟨669356, by rfl⟩ : syracuseStep 892475 = 1338713) B1338713
theorem B892535 : Blo 591290 892535 := bstep (se 1 (by rfl) ⟨669401, by rfl⟩ : syracuseStep 892535 = 1338803) B1338803
theorem B892559 : Blo 591290 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B892601 : Blo 591290 892601 := bstep (se 2 (by rfl) ⟨334725, by rfl⟩ : syracuseStep 892601 = 669451) B669451
theorem B892679 : Blo 591290 892679 := bstep (se 1 (by rfl) ⟨669509, by rfl⟩ : syracuseStep 892679 = 1339019) B1339019
theorem B892715 : Blo 591290 892715 := bstep (se 1 (by rfl) ⟨669536, by rfl⟩ : syracuseStep 892715 = 1339073) B1339073
theorem B5414705 : Blo 591290 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B892745 : Blo 591290 892745 := bstep (se 2 (by rfl) ⟨334779, by rfl⟩ : syracuseStep 892745 = 669559) B669559
theorem B892859 : Blo 591290 892859 := bstep (se 1 (by rfl) ⟨669644, by rfl⟩ : syracuseStep 892859 = 1339289) B1339289
theorem B892919 : Blo 591290 892919 := bstep (se 1 (by rfl) ⟨669689, by rfl⟩ : syracuseStep 892919 = 1339379) B1339379
theorem B1712281 : Blo 591290 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B1352071 : Blo 591290 1352071 := bstep (se 1 (by rfl) ⟨1014053, by rfl⟩ : syracuseStep 1352071 = 2028107) B2028107
theorem B2007449 : Blo 591290 2007449 := bstep (se 2 (by rfl) ⟨752793, by rfl⟩ : syracuseStep 2007449 = 1505587) B1505587
theorem B2892235 : Blo 591290 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B3383927 : Blo 591290 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B5415731 : Blo 591290 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B3384179 : Blo 591290 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B2008151 : Blo 591290 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B2532667 : Blo 591290 2532667 := bstep (se 1 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 2532667 = 3799001) B3799001
theorem B1123769 : Blo 591290 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B4072913 : Blo 591290 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B2008637 : Blo 591290 2008637 := bstep (se 3 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 2008637 = 753239) B753239
theorem B665275 : Blo 591290 665275 := bstep (se 1 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 665275 = 997913) B997913
theorem B1124111 : Blo 591290 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B7579595 : Blo 591290 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B6400133 : Blo 591290 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B665743 : Blo 591290 665743 := bstep (se 1 (by rfl) ⟨499307, by rfl⟩ : syracuseStep 665743 = 998615) B998615
theorem B3385637 : Blo 591290 3385637 := bstep (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) B634807
theorem B2173243 : Blo 591290 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B928171 : Blo 591290 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B633359 : Blo 591290 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B1124923 : Blo 591290 1124923 := bstep (se 1 (by rfl) ⟨843692, by rfl⟩ : syracuseStep 1124923 = 1687385) B1687385
theorem B2533949 : Blo 591290 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B666247 : Blo 591290 666247 := bstep (se 1 (by rfl) ⟨499685, by rfl⟩ : syracuseStep 666247 = 999371) B999371
theorem B1124999 : Blo 591290 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B3812147 : Blo 591290 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B666427 : Blo 591290 666427 := bstep (se 1 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 666427 = 999641) B999641
theorem B633863 : Blo 591290 633863 := bstep (se 1 (by rfl) ⟨475397, by rfl⟩ : syracuseStep 633863 = 950795) B950795
theorem B1125409 : Blo 591290 1125409 := bstep (se 2 (by rfl) ⟨422028, by rfl⟩ : syracuseStep 1125409 = 844057) B844057
theorem B633991 : Blo 591290 633991 := bstep (se 1 (by rfl) ⟨475493, by rfl⟩ : syracuseStep 633991 = 950987) B950987
theorem B3386569 : Blo 591290 3386569 := bstep (se 2 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 3386569 = 2539927) B2539927
theorem B666895 : Blo 591290 666895 := bstep (se 1 (by rfl) ⟨500171, by rfl⟩ : syracuseStep 666895 = 1000343) B1000343
theorem B1125751 : Blo 591290 1125751 := bstep (se 1 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 1125751 = 1688627) B1688627
theorem B6106499 : Blo 591290 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B1420811 : Blo 591290 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B634555 : Blo 591290 634555 := bstep (se 1 (by rfl) ⟨475916, by rfl⟩ : syracuseStep 634555 = 951833) B951833
theorem B2993921 : Blo 591290 2993921 := bstep (se 2 (by rfl) ⟨1122720, by rfl⟩ : syracuseStep 2993921 = 2245441) B2245441
theorem B667399 : Blo 591290 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B667579 : Blo 591290 667579 := bstep (se 1 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 667579 = 1001369) B1001369
theorem B634811 : Blo 591290 634811 := bstep (se 1 (by rfl) ⟨476108, by rfl⟩ : syracuseStep 634811 = 952217) B952217
theorem B668047 : Blo 591290 668047 := bstep (se 1 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 668047 = 1002071) B1002071
theorem B2994731 : Blo 591290 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B1421867 : Blo 591290 1421867 := bstep (se 1 (by rfl) ⟨1066400, by rfl⟩ : syracuseStep 1421867 = 2132801) B2132801
theorem B1520171 : Blo 591290 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B1684253 : Blo 591290 1684253 := bstep (se 3 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 1684253 = 631595) B631595
theorem B668551 : Blo 591290 668551 := bstep (se 1 (by rfl) ⟨501413, by rfl⟩ : syracuseStep 668551 = 1002827) B1002827
theorem B1127353 : Blo 591290 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B668731 : Blo 591290 668731 := bstep (se 1 (by rfl) ⟨501548, by rfl⟩ : syracuseStep 668731 = 1003097) B1003097
theorem B1127695 : Blo 591290 1127695 := bstep (se 1 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 1127695 = 1691543) B1691543
theorem B4634003 : Blo 591290 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B2438585 : Blo 591290 2438585 := bstep (se 2 (by rfl) ⟨914469, by rfl⟩ : syracuseStep 2438585 = 1828939) B1828939
theorem B669199 : Blo 591290 669199 := bstep (se 1 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 669199 = 1003799) B1003799
theorem B1947223 : Blo 591290 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B2996027 : Blo 591290 2996027 := bstep (se 1 (by rfl) ⟨2247020, by rfl⟩ : syracuseStep 2996027 = 4494041) B4494041
theorem B1423289 : Blo 591290 1423289 := bstep (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) B1067467
theorem B2996189 : Blo 591290 2996189 := bstep (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) B1123571
theorem B1128583 : Blo 591290 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B2996513 : Blo 591290 2996513 := bstep (se 2 (by rfl) ⟨1123692, by rfl⟩ : syracuseStep 2996513 = 2247385) B2247385
theorem B1423703 : Blo 591290 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B9615761 : Blo 591290 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B4569643 : Blo 591290 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B6830821 : Blo 591290 6830821 := bstep (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) B1280779
theorem B998203 : Blo 591290 998203 := bstep (se 1 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 998203 = 1497305) B1497305
theorem B1686359 : Blo 591290 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B998345 : Blo 591290 998345 := bstep (se 2 (by rfl) ⟨374379, by rfl⟩ : syracuseStep 998345 = 748759) B748759
theorem B2538697 : Blo 591290 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B2997485 : Blo 591290 2997485 := bstep (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) B1124057
theorem B999047 : Blo 591290 999047 := bstep (se 1 (by rfl) ⟨749285, by rfl⟩ : syracuseStep 999047 = 1498571) B1498571
theorem B6504113 : Blo 591290 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B1687225 : Blo 591290 1687225 := bstep (se 2 (by rfl) ⟨632709, by rfl⟩ : syracuseStep 1687225 = 1265419) B1265419
theorem B1687567 : Blo 591290 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B2998295 : Blo 591290 2998295 := bstep (se 1 (by rfl) ⟨2248721, by rfl⟩ : syracuseStep 2998295 = 4497443) B4497443
theorem B999695 : Blo 591290 999695 := bstep (se 1 (by rfl) ⟨749771, by rfl⟩ : syracuseStep 999695 = 1499543) B1499543
theorem B1687841 : Blo 591290 1687841 := bstep (se 2 (by rfl) ⟨632940, by rfl⟩ : syracuseStep 1687841 = 1265881) B1265881
theorem B7618961 : Blo 591290 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B1425865 : Blo 591290 1425865 := bstep (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) B1069399
theorem B2540099 : Blo 591290 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B803515 : Blo 591290 803515 := bstep (se 1 (by rfl) ⟨602636, by rfl⟩ : syracuseStep 803515 = 1205273) B1205273
theorem B18301733 : Blo 591290 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B1000235 : Blo 591290 1000235 := bstep (se 1 (by rfl) ⟨750176, by rfl⟩ : syracuseStep 1000235 = 1500353) B1500353
theorem B1688455 : Blo 591290 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B1000633 : Blo 591290 1000633 := bstep (se 2 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 1000633 = 750475) B750475
theorem B1688843 : Blo 591290 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1262891 : Blo 591290 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B2246231 : Blo 591290 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B54904499 : Blo 591290 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B1001335 : Blo 591290 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B1624079 : Blo 591290 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B1001531 : Blo 591290 1001531 := bstep (se 1 (by rfl) ⟨751148, by rfl⟩ : syracuseStep 1001531 = 1502297) B1502297
theorem B2246717 : Blo 591290 2246717 := bstep (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) B842519
theorem B6735959 : Blo 591290 6735959 := bstep (se 1 (by rfl) ⟨5051969, by rfl⟩ : syracuseStep 6735959 = 10103939) B10103939
theorem B1067323 : Blo 591290 1067323 := bstep (se 1 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 1067323 = 1600985) B1600985
theorem B1067411 : Blo 591290 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1001929 : Blo 591290 1001929 := bstep (se 2 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 1001929 = 751447) B751447
theorem B1690141 : Blo 591290 1690141 := bstep (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) B633803
theorem B15419969 : Blo 591290 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B1198793 : Blo 591290 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B1690483 : Blo 591290 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B1264531 : Blo 591290 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B3001373 : Blo 591290 3001373 := bstep (se 3 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 3001373 = 1125515) B1125515
theorem B1002631 : Blo 591290 1002631 := bstep (se 1 (by rfl) ⟨751973, by rfl⟩ : syracuseStep 1002631 = 1503947) B1503947
theorem B1101089 : Blo 591290 1101089 := bstep (se 2 (by rfl) ⟨412908, by rfl⟩ : syracuseStep 1101089 = 825817) B825817
theorem B2248145 : Blo 591290 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B3001859 : Blo 591290 3001859 := bstep (se 1 (by rfl) ⟨2251394, by rfl⟩ : syracuseStep 3001859 = 4502789) B4502789
theorem B1330703 : Blo 591290 1330703 := bstep (se 1 (by rfl) ⟨998027, by rfl⟩ : syracuseStep 1330703 = 1996055) B1996055
theorem B1330721 : Blo 591290 1330721 := bstep (se 2 (by rfl) ⟨499020, by rfl⟩ : syracuseStep 1330721 = 998041) B998041
theorem B1003279 : Blo 591290 1003279 := bstep (se 1 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 1003279 = 1504919) B1504919
theorem B4050739 : Blo 591290 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B1331063 : Blo 591290 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B4509593 : Blo 591290 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B1331243 : Blo 591290 1331243 := bstep (se 1 (by rfl) ⟨998432, by rfl⟩ : syracuseStep 1331243 = 1996865) B1996865
theorem B3199247 : Blo 591290 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B1003819 : Blo 591290 1003819 := bstep (se 1 (by rfl) ⟨752864, by rfl⟩ : syracuseStep 1003819 = 1505729) B1505729
theorem B5067143 : Blo 591290 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B1331603 : Blo 591290 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B1003961 : Blo 591290 1003961 := bstep (se 2 (by rfl) ⟨376485, by rfl⟩ : syracuseStep 1003961 = 752971) B752971
theorem B1331657 : Blo 591290 1331657 := bstep (se 2 (by rfl) ⟨499371, by rfl⟩ : syracuseStep 1331657 = 998743) B998743
theorem B1069687 : Blo 591290 1069687 := bstep (se 1 (by rfl) ⟨802265, by rfl⟩ : syracuseStep 1069687 = 1604531) B1604531
theorem B5067521 : Blo 591290 5067521 := bstep (se 2 (by rfl) ⟨1900320, by rfl⟩ : syracuseStep 5067521 = 3800641) B3800641
theorem B11719685 : Blo 591290 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B2249815 : Blo 591290 2249815 := bstep (se 1 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 2249815 = 3374723) B3374723
theorem B3003479 : Blo 591290 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B1332359 : Blo 591290 1332359 := bstep (se 1 (by rfl) ⟨999269, by rfl⟩ : syracuseStep 1332359 = 1998539) B1998539
theorem B5428397 : Blo 591290 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B1070351 : Blo 591290 1070351 := bstep (se 1 (by rfl) ⟨802763, by rfl⟩ : syracuseStep 1070351 = 1605527) B1605527
theorem B1332539 : Blo 591290 1332539 := bstep (se 1 (by rfl) ⟨999404, by rfl⟩ : syracuseStep 1332539 = 1998809) B1998809
theorem B2250119 : Blo 591290 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B1332665 : Blo 591290 1332665 := bstep (se 2 (by rfl) ⟨499749, by rfl⟩ : syracuseStep 1332665 = 999499) B999499
theorem B4871609 : Blo 591290 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B1693217 : Blo 591290 1693217 := bstep (se 2 (by rfl) ⟨634956, by rfl⟩ : syracuseStep 1693217 = 1269913) B1269913
theorem B2250301 : Blo 591290 2250301 := bstep (se 3 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 2250301 = 843863) B843863
theorem B3003965 : Blo 591290 3003965 := bstep (se 3 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 3003965 = 1126487) B1126487
theorem B1824403 : Blo 591290 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B1693331 : Blo 591290 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B1333007 : Blo 591290 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B1333025 : Blo 591290 1333025 := bstep (se 2 (by rfl) ⟨499884, by rfl⟩ : syracuseStep 1333025 = 999769) B999769
theorem B4511537 : Blo 591290 4511537 := bstep (se 2 (by rfl) ⟨1691826, by rfl⟩ : syracuseStep 4511537 = 3383653) B3383653
theorem B1496951 : Blo 591290 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B1333367 : Blo 591290 1333367 := bstep (se 1 (by rfl) ⟨1000025, by rfl⟩ : syracuseStep 1333367 = 2000051) B2000051
theorem B1333547 : Blo 591290 1333547 := bstep (se 1 (by rfl) ⟨1000160, by rfl⟩ : syracuseStep 1333547 = 2000321) B2000321
theorem B1694105 : Blo 591290 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B1268153 : Blo 591290 1268153 := bstep (se 2 (by rfl) ⟨475557, by rfl⟩ : syracuseStep 1268153 = 951115) B951115
theorem B1333907 : Blo 591290 1333907 := bstep (se 1 (by rfl) ⟨1000430, by rfl⟩ : syracuseStep 1333907 = 2000861) B2000861
theorem B1333961 : Blo 591290 1333961 := bstep (se 2 (by rfl) ⟨500235, by rfl⟩ : syracuseStep 1333961 = 1000471) B1000471
theorem B1268615 : Blo 591290 1268615 := bstep (se 1 (by rfl) ⟨951461, by rfl⟩ : syracuseStep 1268615 = 1902923) B1902923
theorem B1498247 : Blo 591290 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B1498297 : Blo 591290 1498297 := bstep (se 2 (by rfl) ⟨561861, by rfl⟩ : syracuseStep 1498297 = 1123723) B1123723
theorem B2252033 : Blo 591290 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B3005747 : Blo 591290 3005747 := bstep (se 1 (by rfl) ⟨2254310, by rfl⟩ : syracuseStep 3005747 = 4508621) B4508621
theorem B1334663 : Blo 591290 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B1334843 : Blo 591290 1334843 := bstep (se 1 (by rfl) ⟨1001132, by rfl⟩ : syracuseStep 1334843 = 2002265) B2002265
theorem B3006071 : Blo 591290 3006071 := bstep (se 1 (by rfl) ⟨2254553, by rfl⟩ : syracuseStep 3006071 = 4509107) B4509107
theorem B1334969 : Blo 591290 1334969 := bstep (se 2 (by rfl) ⟨500613, by rfl⟩ : syracuseStep 1334969 = 1001227) B1001227
theorem B3038921 : Blo 591290 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B1498895 : Blo 591290 1498895 := bstep (se 1 (by rfl) ⟨1124171, by rfl⟩ : syracuseStep 1498895 = 2248343) B2248343
theorem B1335311 : Blo 591290 1335311 := bstep (se 1 (by rfl) ⟨1001483, by rfl⟩ : syracuseStep 1335311 = 2002967) B2002967
theorem B1335329 : Blo 591290 1335329 := bstep (se 2 (by rfl) ⟨500748, by rfl⟩ : syracuseStep 1335329 = 1001497) B1001497
theorem B1269793 : Blo 591290 1269793 := bstep (se 2 (by rfl) ⟨476172, by rfl⟩ : syracuseStep 1269793 = 952345) B952345
theorem B843977 : Blo 591290 843977 := bstep (se 2 (by rfl) ⟨316491, by rfl⟩ : syracuseStep 843977 = 632983) B632983
theorem B1335671 : Blo 591290 1335671 := bstep (se 1 (by rfl) ⟨1001753, by rfl⟩ : syracuseStep 1335671 = 2003507) B2003507
theorem B2253203 : Blo 591290 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B3793337 : Blo 591290 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B1499593 : Blo 591290 1499593 := bstep (se 2 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 1499593 = 1124695) B1124695
theorem B3858947 : Blo 591290 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B6775325 : Blo 591290 6775325 := bstep (se 3 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 6775325 = 2540747) B2540747
theorem B1335851 : Blo 591290 1335851 := bstep (se 1 (by rfl) ⟨1001888, by rfl⟩ : syracuseStep 1335851 = 2003777) B2003777
theorem B3007043 : Blo 591290 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B1499735 : Blo 591290 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B2253703 : Blo 591290 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B3007367 : Blo 591290 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B1336211 : Blo 591290 1336211 := bstep (se 1 (by rfl) ⟨1002158, by rfl⟩ : syracuseStep 1336211 = 2004317) B2004317
theorem B1336265 : Blo 591290 1336265 := bstep (se 2 (by rfl) ⟨501099, by rfl⟩ : syracuseStep 1336265 = 1002199) B1002199
theorem B3367889 : Blo 591290 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B5071895 : Blo 591290 5071895 := bstep (se 1 (by rfl) ⟨3803921, by rfl⟩ : syracuseStep 5071895 = 7607843) B7607843
theorem B844843 : Blo 591290 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B48850289 : Blo 591290 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B11527559 : Blo 591290 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B1336967 : Blo 591290 1336967 := bstep (se 1 (by rfl) ⟨1002725, by rfl⟩ : syracuseStep 1336967 = 2005451) B2005451
theorem B5400371 : Blo 591290 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B1337147 : Blo 591290 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B1828669 : Blo 591290 1828669 := bstep (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) B685751
theorem B1337273 : Blo 591290 1337273 := bstep (se 2 (by rfl) ⟨501477, by rfl⟩ : syracuseStep 1337273 = 1002955) B1002955
theorem B3008477 : Blo 591290 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B2844695 : Blo 591290 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B2844733 : Blo 591290 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B10152053 : Blo 591290 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B6514805 : Blo 591290 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B845959 : Blo 591290 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1337615 : Blo 591290 1337615 := bstep (se 1 (by rfl) ⟨1003211, by rfl⟩ : syracuseStep 1337615 = 2006423) B2006423
theorem B1337633 : Blo 591290 1337633 := bstep (se 2 (by rfl) ⟨501612, by rfl⟩ : syracuseStep 1337633 = 1003225) B1003225
theorem B3795335 : Blo 591290 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B1501811 : Blo 591290 1501811 := bstep (se 1 (by rfl) ⟨1126358, by rfl⟩ : syracuseStep 1501811 = 2252717) B2252717
theorem B1337975 : Blo 591290 1337975 := bstep (se 1 (by rfl) ⟨1003481, by rfl⟩ : syracuseStep 1337975 = 2006963) B2006963
theorem B1338155 : Blo 591290 1338155 := bstep (se 1 (by rfl) ⟨1003616, by rfl⟩ : syracuseStep 1338155 = 2007233) B2007233
theorem B846779 : Blo 591290 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B1502327 : Blo 591290 1502327 := bstep (se 1 (by rfl) ⟨1126745, by rfl⟩ : syracuseStep 1502327 = 2253491) B2253491
theorem B1338515 : Blo 591290 1338515 := bstep (se 1 (by rfl) ⟨1003886, by rfl⟩ : syracuseStep 1338515 = 2007773) B2007773
theorem B912569 : Blo 591290 912569 := bstep (se 2 (by rfl) ⟨342213, by rfl⟩ : syracuseStep 912569 = 684427) B684427
theorem B1338569 : Blo 591290 1338569 := bstep (se 2 (by rfl) ⟨501963, by rfl⟩ : syracuseStep 1338569 = 1003927) B1003927
theorem B2289043 : Blo 591290 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B3206621 : Blo 591290 3206621 := bstep (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) B1202483
theorem B1928747 : Blo 591290 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B847417 : Blo 591290 847417 := bstep (se 2 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 847417 = 635563) B635563
theorem B28929635 : Blo 591290 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B847531 : Blo 591290 847531 := bstep (se 1 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 847531 = 1271297) B1271297
theorem B6844121 : Blo 591290 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B1339271 : Blo 591290 1339271 := bstep (se 1 (by rfl) ⟨1004453, by rfl⟩ : syracuseStep 1339271 = 2008907) B2008907
theorem B14479307 : Blo 591290 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B1503319 : Blo 591290 1503319 := bstep (se 1 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 1503319 = 2254979) B2254979
theorem B11137297 : Blo 591290 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B3010931 : Blo 591290 3010931 := bstep (se 1 (by rfl) ⟨2258198, by rfl⟩ : syracuseStep 3010931 = 4516397) B4516397
theorem B1503623 : Blo 591290 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1601927 : Blo 591290 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B1503755 : Blo 591290 1503755 := bstep (se 1 (by rfl) ⟨1127816, by rfl⟩ : syracuseStep 1503755 = 2255633) B2255633
theorem B1602109 : Blo 591290 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B2880193 : Blo 591290 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B7205593 : Blo 591290 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B3207937 : Blo 591290 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B750379 : Blo 591290 750379 := bstep (se 1 (by rfl) ⟨562784, by rfl⟩ : syracuseStep 750379 = 1125569) B1125569
theorem B6779699 : Blo 591290 6779699 := bstep (se 1 (by rfl) ⟨5084774, by rfl⟩ : syracuseStep 6779699 = 10169549) B10169549
theorem B2847577 : Blo 591290 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B3011417 : Blo 591290 3011417 := bstep (se 2 (by rfl) ⟨1129281, by rfl⟩ : syracuseStep 3011417 = 2258563) B2258563
theorem B1504271 : Blo 591290 1504271 := bstep (se 1 (by rfl) ⟨1128203, by rfl⟩ : syracuseStep 1504271 = 2256407) B2256407
theorem B1504403 : Blo 591290 1504403 := bstep (se 1 (by rfl) ⟨1128302, by rfl⟩ : syracuseStep 1504403 = 2256605) B2256605
theorem B1799453 : Blo 591290 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B1602931 : Blo 591290 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B4519313 : Blo 591290 4519313 := bstep (se 2 (by rfl) ⟨1694742, by rfl⟩ : syracuseStep 4519313 = 3389485) B3389485
theorem B1996217 : Blo 591290 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B947771 : Blo 591290 947771 := bstep (se 1 (by rfl) ⟨710828, by rfl⟩ : syracuseStep 947771 = 1421657) B1421657
theorem B1799833 : Blo 591290 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B751351 : Blo 591290 751351 := bstep (se 1 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 751351 = 1127027) B1127027
theorem B3372947 : Blo 591290 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B1996811 : Blo 591290 1996811 := bstep (se 1 (by rfl) ⟨1497608, by rfl⟩ : syracuseStep 1996811 = 2995217) B2995217
theorem B751675 : Blo 591290 751675 := bstep (se 1 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 751675 = 1127513) B1127513
theorem B1996919 : Blo 591290 1996919 := bstep (se 1 (by rfl) ⟨1497689, by rfl⟩ : syracuseStep 1996919 = 2995379) B2995379
theorem B1505537 : Blo 591290 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B2849039 : Blo 591290 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B3373447 : Blo 591290 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B2259353 : Blo 591290 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B1440371 : Blo 591290 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B1505911 : Blo 591290 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B1997513 : Blo 591290 1997513 := bstep (se 2 (by rfl) ⟨749067, by rfl⟩ : syracuseStep 1997513 = 1498135) B1498135
theorem B3013523 : Blo 591290 3013523 := bstep (se 1 (by rfl) ⟨2260142, by rfl⟩ : syracuseStep 3013523 = 4520285) B4520285
theorem B6749081 : Blo 591290 6749081 := bstep (se 2 (by rfl) ⟨2530905, by rfl⟩ : syracuseStep 6749081 = 5061811) B5061811
theorem B752647 : Blo 591290 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B1506347 : Blo 591290 1506347 := bstep (se 1 (by rfl) ⟨1129760, by rfl⟩ : syracuseStep 1506347 = 2259521) B2259521
theorem B1998215 : Blo 591290 1998215 := bstep (se 1 (by rfl) ⟨1498661, by rfl⟩ : syracuseStep 1998215 = 2997323) B2997323
theorem B1899911 : Blo 591290 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B753067 : Blo 591290 753067 := bstep (se 1 (by rfl) ⟨564800, by rfl⟩ : syracuseStep 753067 = 1129601) B1129601
theorem B22871645 : Blo 591290 22871645 := bstep (se 3 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 22871645 = 8576867) B8576867
theorem B753295 : Blo 591290 753295 := bstep (se 1 (by rfl) ⟨564971, by rfl⟩ : syracuseStep 753295 = 1129943) B1129943
theorem B1998593 : Blo 591290 1998593 := bstep (se 2 (by rfl) ⟨749472, by rfl⟩ : syracuseStep 1998593 = 1498945) B1498945
theorem B1900435 : Blo 591290 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B1998863 : Blo 591290 1998863 := bstep (se 1 (by rfl) ⟨1499147, by rfl⟩ : syracuseStep 1998863 = 2998295) B2998295
theorem B5079307 : Blo 591290 5079307 := bstep (se 1 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 5079307 = 7618961) B7618961
theorem B6750539 : Blo 591290 6750539 := bstep (se 1 (by rfl) ⟨5062904, by rfl⟩ : syracuseStep 6750539 = 10125809) B10125809
theorem B1999457 : Blo 591290 1999457 := bstep (se 2 (by rfl) ⟨749796, by rfl⟩ : syracuseStep 1999457 = 1499593) B1499593
theorem B1901153 : Blo 591290 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B36602999 : Blo 591290 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B3212567 : Blo 591290 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B1082719 : Blo 591290 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B4490639 : Blo 591290 4490639 := bstep (se 1 (by rfl) ⟨3367979, by rfl⟩ : syracuseStep 4490639 = 6735959) B6735959
theorem B591303 : Blo 591290 591303 := bstep (se 1 (by rfl) ⟨443477, by rfl⟩ : syracuseStep 591303 = 886955) B886955
theorem B591323 : Blo 591290 591323 := bstep (se 1 (by rfl) ⟨443492, by rfl⟩ : syracuseStep 591323 = 886985) B886985
theorem B591399 : Blo 591290 591399 := bstep (se 1 (by rfl) ⟨443549, by rfl⟩ : syracuseStep 591399 = 887099) B887099
theorem B591439 : Blo 591290 591439 := bstep (se 1 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 591439 = 887159) B887159
theorem B591455 : Blo 591290 591455 := bstep (se 1 (by rfl) ⟨443591, by rfl⟩ : syracuseStep 591455 = 887183) B887183
theorem B591483 : Blo 591290 591483 := bstep (se 1 (by rfl) ⟨443612, by rfl⟩ : syracuseStep 591483 = 887225) B887225
theorem B591535 : Blo 591290 591535 := bstep (se 1 (by rfl) ⟨443651, by rfl⟩ : syracuseStep 591535 = 887303) B887303
theorem B591559 : Blo 591290 591559 := bstep (se 1 (by rfl) ⟨443669, by rfl⟩ : syracuseStep 591559 = 887339) B887339
theorem B2033363 : Blo 591290 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B591579 : Blo 591290 591579 := bstep (se 1 (by rfl) ⟨443684, by rfl⟩ : syracuseStep 591579 = 887369) B887369
theorem B3376889 : Blo 591290 3376889 := bstep (se 2 (by rfl) ⟨1266333, by rfl⟩ : syracuseStep 3376889 = 2532667) B2532667
theorem B591655 : Blo 591290 591655 := bstep (se 1 (by rfl) ⟨443741, by rfl⟩ : syracuseStep 591655 = 887483) B887483
theorem B591695 : Blo 591290 591695 := bstep (se 1 (by rfl) ⟨443771, by rfl⟩ : syracuseStep 591695 = 887543) B887543
theorem B591711 : Blo 591290 591711 := bstep (se 1 (by rfl) ⟨443783, by rfl⟩ : syracuseStep 591711 = 887567) B887567
theorem B591739 : Blo 591290 591739 := bstep (se 1 (by rfl) ⟨443804, by rfl⟩ : syracuseStep 591739 = 887609) B887609
theorem B591791 : Blo 591290 591791 := bstep (se 1 (by rfl) ⟨443843, by rfl⟩ : syracuseStep 591791 = 887687) B887687
theorem B9734069 : Blo 591290 9734069 := bstep (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) B912569
theorem B591815 : Blo 591290 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B591835 : Blo 591290 591835 := bstep (se 1 (by rfl) ⟨443876, by rfl⟩ : syracuseStep 591835 = 887753) B887753
theorem B2000915 : Blo 591290 2000915 := bstep (se 1 (by rfl) ⟨1500686, by rfl⟩ : syracuseStep 2000915 = 3001373) B3001373
theorem B4556837 : Blo 591290 4556837 := bstep (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) B854407
theorem B7211045 : Blo 591290 7211045 := bstep (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) B1352071
theorem B591911 : Blo 591290 591911 := bstep (se 1 (by rfl) ⟨443933, by rfl⟩ : syracuseStep 591911 = 887867) B887867
theorem B591951 : Blo 591290 591951 := bstep (se 1 (by rfl) ⟨443963, by rfl⟩ : syracuseStep 591951 = 887927) B887927
theorem B591967 : Blo 591290 591967 := bstep (se 1 (by rfl) ⟨443975, by rfl⟩ : syracuseStep 591967 = 887951) B887951
theorem B591995 : Blo 591290 591995 := bstep (se 1 (by rfl) ⟨443996, by rfl⟩ : syracuseStep 591995 = 887993) B887993
theorem B592047 : Blo 591290 592047 := bstep (se 1 (by rfl) ⟨444035, by rfl⟩ : syracuseStep 592047 = 888071) B888071
theorem B592071 : Blo 591290 592071 := bstep (se 1 (by rfl) ⟨444053, by rfl⟩ : syracuseStep 592071 = 888107) B888107
theorem B592091 : Blo 591290 592091 := bstep (se 1 (by rfl) ⟨444068, by rfl⟩ : syracuseStep 592091 = 888137) B888137
theorem B4950245 : Blo 591290 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B887033 : Blo 591290 887033 := bstep (se 2 (by rfl) ⟨332637, by rfl⟩ : syracuseStep 887033 = 665275) B665275
theorem B592167 : Blo 591290 592167 := bstep (se 1 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 592167 = 888251) B888251
theorem B592207 : Blo 591290 592207 := bstep (se 1 (by rfl) ⟨444155, by rfl⟩ : syracuseStep 592207 = 888311) B888311
theorem B2001239 : Blo 591290 2001239 := bstep (se 1 (by rfl) ⟨1500929, by rfl⟩ : syracuseStep 2001239 = 3001859) B3001859
theorem B887135 : Blo 591290 887135 := bstep (se 1 (by rfl) ⟨665351, by rfl⟩ : syracuseStep 887135 = 1330703) B1330703
theorem B592223 : Blo 591290 592223 := bstep (se 1 (by rfl) ⟨444167, by rfl⟩ : syracuseStep 592223 = 888335) B888335
theorem B887147 : Blo 591290 887147 := bstep (se 1 (by rfl) ⟨665360, by rfl⟩ : syracuseStep 887147 = 1330721) B1330721
theorem B592251 : Blo 591290 592251 := bstep (se 1 (by rfl) ⟨444188, by rfl⟩ : syracuseStep 592251 = 888377) B888377
theorem B592303 : Blo 591290 592303 := bstep (se 1 (by rfl) ⟨444227, by rfl⟩ : syracuseStep 592303 = 888455) B888455
theorem B592327 : Blo 591290 592327 := bstep (se 1 (by rfl) ⟨444245, by rfl⟩ : syracuseStep 592327 = 888491) B888491
theorem B592347 : Blo 591290 592347 := bstep (se 1 (by rfl) ⟨444260, by rfl⟩ : syracuseStep 592347 = 888521) B888521
theorem B592423 : Blo 591290 592423 := bstep (se 1 (by rfl) ⟨444317, by rfl⟩ : syracuseStep 592423 = 888635) B888635
theorem B887375 : Blo 591290 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B592463 : Blo 591290 592463 := bstep (se 1 (by rfl) ⟨444347, by rfl⟩ : syracuseStep 592463 = 888695) B888695
theorem B592479 : Blo 591290 592479 := bstep (se 1 (by rfl) ⟨444359, by rfl⟩ : syracuseStep 592479 = 888719) B888719
theorem B592507 : Blo 591290 592507 := bstep (se 1 (by rfl) ⟨444380, by rfl⟩ : syracuseStep 592507 = 888761) B888761
theorem B592559 : Blo 591290 592559 := bstep (se 1 (by rfl) ⟨444419, by rfl⟩ : syracuseStep 592559 = 888839) B888839
theorem B887495 : Blo 591290 887495 := bstep (se 1 (by rfl) ⟨665621, by rfl⟩ : syracuseStep 887495 = 1331243) B1331243
theorem B592583 : Blo 591290 592583 := bstep (se 1 (by rfl) ⟨444437, by rfl⟩ : syracuseStep 592583 = 888875) B888875
theorem B592603 : Blo 591290 592603 := bstep (se 1 (by rfl) ⟨444452, by rfl⟩ : syracuseStep 592603 = 888905) B888905
theorem B592679 : Blo 591290 592679 := bstep (se 1 (by rfl) ⟨444509, by rfl⟩ : syracuseStep 592679 = 889019) B889019
theorem B592719 : Blo 591290 592719 := bstep (se 1 (by rfl) ⟨444539, by rfl⟩ : syracuseStep 592719 = 889079) B889079
theorem B2132831 : Blo 591290 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B592735 : Blo 591290 592735 := bstep (se 1 (by rfl) ⟨444551, by rfl⟩ : syracuseStep 592735 = 889103) B889103
theorem B887657 : Blo 591290 887657 := bstep (se 2 (by rfl) ⟨332871, by rfl⟩ : syracuseStep 887657 = 665743) B665743
theorem B592763 : Blo 591290 592763 := bstep (se 1 (by rfl) ⟨444572, by rfl⟩ : syracuseStep 592763 = 889145) B889145
theorem B592815 : Blo 591290 592815 := bstep (se 1 (by rfl) ⟨444611, by rfl⟩ : syracuseStep 592815 = 889223) B889223
theorem B3378095 : Blo 591290 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B887735 : Blo 591290 887735 := bstep (se 1 (by rfl) ⟨665801, by rfl⟩ : syracuseStep 887735 = 1331603) B1331603
theorem B592839 : Blo 591290 592839 := bstep (se 1 (by rfl) ⟨444629, by rfl⟩ : syracuseStep 592839 = 889259) B889259
theorem B887771 : Blo 591290 887771 := bstep (se 1 (by rfl) ⟨665828, by rfl⟩ : syracuseStep 887771 = 1331657) B1331657
theorem B592859 : Blo 591290 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B592935 : Blo 591290 592935 := bstep (se 1 (by rfl) ⟨444701, by rfl⟩ : syracuseStep 592935 = 889403) B889403
theorem B592975 : Blo 591290 592975 := bstep (se 1 (by rfl) ⟨444731, by rfl⟩ : syracuseStep 592975 = 889463) B889463
theorem B592991 : Blo 591290 592991 := bstep (se 1 (by rfl) ⟨444743, by rfl⟩ : syracuseStep 592991 = 889487) B889487
theorem B593019 : Blo 591290 593019 := bstep (se 1 (by rfl) ⟨444764, by rfl⟩ : syracuseStep 593019 = 889529) B889529
theorem B3378347 : Blo 591290 3378347 := bstep (se 1 (by rfl) ⟨2533760, by rfl⟩ : syracuseStep 3378347 = 5067521) B5067521
theorem B593071 : Blo 591290 593071 := bstep (se 1 (by rfl) ⟨444803, by rfl⟩ : syracuseStep 593071 = 889607) B889607
theorem B593095 : Blo 591290 593095 := bstep (se 1 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 593095 = 889643) B889643
theorem B593115 : Blo 591290 593115 := bstep (se 1 (by rfl) ⟨444836, by rfl⟩ : syracuseStep 593115 = 889673) B889673
theorem B593191 : Blo 591290 593191 := bstep (se 1 (by rfl) ⟨444893, by rfl⟩ : syracuseStep 593191 = 889787) B889787
theorem B593231 : Blo 591290 593231 := bstep (se 1 (by rfl) ⟨444923, by rfl⟩ : syracuseStep 593231 = 889847) B889847
theorem B593247 : Blo 591290 593247 := bstep (se 1 (by rfl) ⟨444935, by rfl⟩ : syracuseStep 593247 = 889871) B889871
theorem B593275 : Blo 591290 593275 := bstep (se 1 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 593275 = 889913) B889913
theorem B2002319 : Blo 591290 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B888239 : Blo 591290 888239 := bstep (se 1 (by rfl) ⟨666179, by rfl⟩ : syracuseStep 888239 = 1332359) B1332359
theorem B593327 : Blo 591290 593327 := bstep (se 1 (by rfl) ⟨444995, by rfl⟩ : syracuseStep 593327 = 889991) B889991
theorem B593351 : Blo 591290 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B593371 : Blo 591290 593371 := bstep (se 1 (by rfl) ⟨445028, by rfl⟩ : syracuseStep 593371 = 890057) B890057
theorem B888329 : Blo 591290 888329 := bstep (se 2 (by rfl) ⟨333123, by rfl⟩ : syracuseStep 888329 = 666247) B666247
theorem B888359 : Blo 591290 888359 := bstep (se 1 (by rfl) ⟨666269, by rfl⟩ : syracuseStep 888359 = 1332539) B1332539
theorem B593447 : Blo 591290 593447 := bstep (se 1 (by rfl) ⟨445085, by rfl⟩ : syracuseStep 593447 = 890171) B890171
theorem B593487 : Blo 591290 593487 := bstep (se 1 (by rfl) ⟨445115, by rfl⟩ : syracuseStep 593487 = 890231) B890231
theorem B593503 : Blo 591290 593503 := bstep (se 1 (by rfl) ⟨445127, by rfl⟩ : syracuseStep 593503 = 890255) B890255
theorem B888443 : Blo 591290 888443 := bstep (se 1 (by rfl) ⟨666332, by rfl⟩ : syracuseStep 888443 = 1332665) B1332665
theorem B3247739 : Blo 591290 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B593531 : Blo 591290 593531 := bstep (se 1 (by rfl) ⟨445148, by rfl⟩ : syracuseStep 593531 = 890297) B890297
theorem B593583 : Blo 591290 593583 := bstep (se 1 (by rfl) ⟨445187, by rfl⟩ : syracuseStep 593583 = 890375) B890375
theorem B593607 : Blo 591290 593607 := bstep (se 1 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 593607 = 890411) B890411
theorem B2002643 : Blo 591290 2002643 := bstep (se 1 (by rfl) ⟨1501982, by rfl⟩ : syracuseStep 2002643 = 3003965) B3003965
theorem B593627 : Blo 591290 593627 := bstep (se 1 (by rfl) ⟨445220, by rfl⟩ : syracuseStep 593627 = 890441) B890441
theorem B888569 : Blo 591290 888569 := bstep (se 2 (by rfl) ⟨333213, by rfl⟩ : syracuseStep 888569 = 666427) B666427
theorem B593703 : Blo 591290 593703 := bstep (se 1 (by rfl) ⟨445277, by rfl⟩ : syracuseStep 593703 = 890555) B890555
theorem B593743 : Blo 591290 593743 := bstep (se 1 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 593743 = 890615) B890615
theorem B888671 : Blo 591290 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B593759 : Blo 591290 593759 := bstep (se 1 (by rfl) ⟨445319, by rfl⟩ : syracuseStep 593759 = 890639) B890639
theorem B888683 : Blo 591290 888683 := bstep (se 1 (by rfl) ⟨666512, by rfl⟩ : syracuseStep 888683 = 1333025) B1333025
theorem B593787 : Blo 591290 593787 := bstep (se 1 (by rfl) ⟨445340, by rfl⟩ : syracuseStep 593787 = 890681) B890681
theorem B593839 : Blo 591290 593839 := bstep (se 1 (by rfl) ⟨445379, by rfl⟩ : syracuseStep 593839 = 890759) B890759
theorem B593863 : Blo 591290 593863 := bstep (se 1 (by rfl) ⟨445397, by rfl⟩ : syracuseStep 593863 = 890795) B890795
theorem B593883 : Blo 591290 593883 := bstep (se 1 (by rfl) ⟨445412, by rfl⟩ : syracuseStep 593883 = 890825) B890825
theorem B593959 : Blo 591290 593959 := bstep (se 1 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 593959 = 890939) B890939
theorem B888911 : Blo 591290 888911 := bstep (se 1 (by rfl) ⟨666683, by rfl⟩ : syracuseStep 888911 = 1333367) B1333367
theorem B593999 : Blo 591290 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B594015 : Blo 591290 594015 := bstep (se 1 (by rfl) ⟨445511, by rfl⟩ : syracuseStep 594015 = 891023) B891023
theorem B594043 : Blo 591290 594043 := bstep (se 1 (by rfl) ⟨445532, by rfl⟩ : syracuseStep 594043 = 891065) B891065
theorem B594095 : Blo 591290 594095 := bstep (se 1 (by rfl) ⟨445571, by rfl⟩ : syracuseStep 594095 = 891143) B891143
theorem B889031 : Blo 591290 889031 := bstep (se 1 (by rfl) ⟨666773, by rfl⟩ : syracuseStep 889031 = 1333547) B1333547
theorem B594119 : Blo 591290 594119 := bstep (se 1 (by rfl) ⟨445589, by rfl⟩ : syracuseStep 594119 = 891179) B891179
theorem B594139 : Blo 591290 594139 := bstep (se 1 (by rfl) ⟨445604, by rfl⟩ : syracuseStep 594139 = 891209) B891209
theorem B594215 : Blo 591290 594215 := bstep (se 1 (by rfl) ⟨445661, by rfl⟩ : syracuseStep 594215 = 891323) B891323
theorem B594255 : Blo 591290 594255 := bstep (se 1 (by rfl) ⟨445691, by rfl⟩ : syracuseStep 594255 = 891383) B891383
theorem B594271 : Blo 591290 594271 := bstep (se 1 (by rfl) ⟨445703, by rfl⟩ : syracuseStep 594271 = 891407) B891407
theorem B889193 : Blo 591290 889193 := bstep (se 2 (by rfl) ⟨333447, by rfl⟩ : syracuseStep 889193 = 666895) B666895
theorem B594299 : Blo 591290 594299 := bstep (se 1 (by rfl) ⟨445724, by rfl⟩ : syracuseStep 594299 = 891449) B891449
theorem B594351 : Blo 591290 594351 := bstep (se 1 (by rfl) ⟨445763, by rfl⟩ : syracuseStep 594351 = 891527) B891527
theorem B889271 : Blo 591290 889271 := bstep (se 1 (by rfl) ⟨666953, by rfl⟩ : syracuseStep 889271 = 1333907) B1333907
theorem B594375 : Blo 591290 594375 := bstep (se 1 (by rfl) ⟨445781, by rfl⟩ : syracuseStep 594375 = 891563) B891563
theorem B889307 : Blo 591290 889307 := bstep (se 1 (by rfl) ⟨666980, by rfl⟩ : syracuseStep 889307 = 1333961) B1333961
theorem B594395 : Blo 591290 594395 := bstep (se 1 (by rfl) ⟨445796, by rfl⟩ : syracuseStep 594395 = 891593) B891593
theorem B594471 : Blo 591290 594471 := bstep (se 1 (by rfl) ⟨445853, by rfl⟩ : syracuseStep 594471 = 891707) B891707
theorem B594511 : Blo 591290 594511 := bstep (se 1 (by rfl) ⟨445883, by rfl⟩ : syracuseStep 594511 = 891767) B891767
theorem B594527 : Blo 591290 594527 := bstep (se 1 (by rfl) ⟨445895, by rfl⟩ : syracuseStep 594527 = 891791) B891791
theorem B594555 : Blo 591290 594555 := bstep (se 1 (by rfl) ⟨445916, by rfl⟩ : syracuseStep 594555 = 891833) B891833
theorem B594607 : Blo 591290 594607 := bstep (se 1 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 594607 = 891911) B891911
theorem B594631 : Blo 591290 594631 := bstep (se 1 (by rfl) ⟨445973, by rfl⟩ : syracuseStep 594631 = 891947) B891947
theorem B594651 : Blo 591290 594651 := bstep (se 1 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 594651 = 891977) B891977
theorem B594727 : Blo 591290 594727 := bstep (se 1 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 594727 = 892091) B892091
theorem B594767 : Blo 591290 594767 := bstep (se 1 (by rfl) ⟨446075, by rfl⟩ : syracuseStep 594767 = 892151) B892151
theorem B594783 : Blo 591290 594783 := bstep (se 1 (by rfl) ⟨446087, by rfl⟩ : syracuseStep 594783 = 892175) B892175
theorem B2003831 : Blo 591290 2003831 := bstep (se 1 (by rfl) ⟨1502873, by rfl⟩ : syracuseStep 2003831 = 3005747) B3005747
theorem B594811 : Blo 591290 594811 := bstep (se 1 (by rfl) ⟨446108, by rfl⟩ : syracuseStep 594811 = 892217) B892217
theorem B3806099 : Blo 591290 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B889775 : Blo 591290 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B594863 : Blo 591290 594863 := bstep (se 1 (by rfl) ⟨446147, by rfl⟩ : syracuseStep 594863 = 892295) B892295
theorem B594887 : Blo 591290 594887 := bstep (se 1 (by rfl) ⟨446165, by rfl⟩ : syracuseStep 594887 = 892331) B892331
theorem B594907 : Blo 591290 594907 := bstep (se 1 (by rfl) ⟨446180, by rfl⟩ : syracuseStep 594907 = 892361) B892361
theorem B889865 : Blo 591290 889865 := bstep (se 2 (by rfl) ⟨333699, by rfl⟩ : syracuseStep 889865 = 667399) B667399
theorem B889895 : Blo 591290 889895 := bstep (se 1 (by rfl) ⟨667421, by rfl⟩ : syracuseStep 889895 = 1334843) B1334843
theorem B594983 : Blo 591290 594983 := bstep (se 1 (by rfl) ⟨446237, by rfl⟩ : syracuseStep 594983 = 892475) B892475
theorem B2004047 : Blo 591290 2004047 := bstep (se 1 (by rfl) ⟨1503035, by rfl⟩ : syracuseStep 2004047 = 3006071) B3006071
theorem B595023 : Blo 591290 595023 := bstep (se 1 (by rfl) ⟨446267, by rfl⟩ : syracuseStep 595023 = 892535) B892535
theorem B595039 : Blo 591290 595039 := bstep (se 1 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 595039 = 892559) B892559
theorem B889979 : Blo 591290 889979 := bstep (se 1 (by rfl) ⟨667484, by rfl⟩ : syracuseStep 889979 = 1334969) B1334969
theorem B595067 : Blo 591290 595067 := bstep (se 1 (by rfl) ⟨446300, by rfl⟩ : syracuseStep 595067 = 892601) B892601
theorem B595119 : Blo 591290 595119 := bstep (se 1 (by rfl) ⟨446339, by rfl⟩ : syracuseStep 595119 = 892679) B892679
theorem B595143 : Blo 591290 595143 := bstep (se 1 (by rfl) ⟨446357, by rfl⟩ : syracuseStep 595143 = 892715) B892715
theorem B3609803 : Blo 591290 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B595163 : Blo 591290 595163 := bstep (se 1 (by rfl) ⟨446372, by rfl⟩ : syracuseStep 595163 = 892745) B892745
theorem B890105 : Blo 591290 890105 := bstep (se 2 (by rfl) ⟨333789, by rfl⟩ : syracuseStep 890105 = 667579) B667579
theorem B595239 : Blo 591290 595239 := bstep (se 1 (by rfl) ⟨446429, by rfl⟩ : syracuseStep 595239 = 892859) B892859
theorem B595279 : Blo 591290 595279 := bstep (se 1 (by rfl) ⟨446459, by rfl⟩ : syracuseStep 595279 = 892919) B892919
theorem B890207 : Blo 591290 890207 := bstep (se 1 (by rfl) ⟨667655, by rfl⟩ : syracuseStep 890207 = 1335311) B1335311
theorem B890219 : Blo 591290 890219 := bstep (se 1 (by rfl) ⟨667664, by rfl⟩ : syracuseStep 890219 = 1335329) B1335329
theorem B2004425 : Blo 591290 2004425 := bstep (se 2 (by rfl) ⟨751659, by rfl⟩ : syracuseStep 2004425 = 1503319) B1503319
theorem B890447 : Blo 591290 890447 := bstep (se 1 (by rfl) ⟨667835, by rfl⟩ : syracuseStep 890447 = 1335671) B1335671
theorem B2528891 : Blo 591290 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B14849729 : Blo 591290 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B890567 : Blo 591290 890567 := bstep (se 1 (by rfl) ⟨667925, by rfl⟩ : syracuseStep 890567 = 1335851) B1335851
theorem B2004695 : Blo 591290 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B890729 : Blo 591290 890729 := bstep (se 2 (by rfl) ⟨334023, by rfl⟩ : syracuseStep 890729 = 668047) B668047
theorem B3610487 : Blo 591290 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B2004911 : Blo 591290 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B890807 : Blo 591290 890807 := bstep (se 1 (by rfl) ⟨668105, by rfl⟩ : syracuseStep 890807 = 1336211) B1336211
theorem B890843 : Blo 591290 890843 := bstep (se 1 (by rfl) ⟨668132, by rfl⟩ : syracuseStep 890843 = 1336265) B1336265
theorem B3381263 : Blo 591290 3381263 := bstep (se 1 (by rfl) ⟨2535947, by rfl⟩ : syracuseStep 3381263 = 5071895) B5071895
theorem B2136145 : Blo 591290 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B3840257 : Blo 591290 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B9607457 : Blo 591290 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B891311 : Blo 591290 891311 := bstep (se 1 (by rfl) ⟨668483, by rfl⟩ : syracuseStep 891311 = 1336967) B1336967
theorem B891401 : Blo 591290 891401 := bstep (se 2 (by rfl) ⟨334275, by rfl⟩ : syracuseStep 891401 = 668551) B668551
theorem B891431 : Blo 591290 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B891515 : Blo 591290 891515 := bstep (se 1 (by rfl) ⟨668636, by rfl⟩ : syracuseStep 891515 = 1337273) B1337273
theorem B5053063 : Blo 591290 5053063 := bstep (se 1 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 5053063 = 7579595) B7579595
theorem B2005651 : Blo 591290 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B891641 : Blo 591290 891641 := bstep (se 2 (by rfl) ⟨334365, by rfl⟩ : syracuseStep 891641 = 668731) B668731
theorem B4266755 : Blo 591290 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B891743 : Blo 591290 891743 := bstep (se 1 (by rfl) ⟨668807, by rfl⟩ : syracuseStep 891743 = 1337615) B1337615
theorem B891755 : Blo 591290 891755 := bstep (se 1 (by rfl) ⟨668816, by rfl⟩ : syracuseStep 891755 = 1337633) B1337633
theorem B2530223 : Blo 591290 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B891983 : Blo 591290 891983 := bstep (se 1 (by rfl) ⟨668987, by rfl⟩ : syracuseStep 891983 = 1337975) B1337975
theorem B2137241 : Blo 591290 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B892103 : Blo 591290 892103 := bstep (se 1 (by rfl) ⟨669077, by rfl⟩ : syracuseStep 892103 = 1338155) B1338155
theorem B892265 : Blo 591290 892265 := bstep (se 2 (by rfl) ⟨334599, by rfl⟩ : syracuseStep 892265 = 669199) B669199
theorem B892343 : Blo 591290 892343 := bstep (se 1 (by rfl) ⟨669257, by rfl⟩ : syracuseStep 892343 = 1338515) B1338515
theorem B892379 : Blo 591290 892379 := bstep (se 1 (by rfl) ⟨669284, by rfl⟩ : syracuseStep 892379 = 1338569) B1338569
theorem B2432537 : Blo 591290 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B2399777 : Blo 591290 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B4496957 : Blo 591290 4496957 := bstep (se 3 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 4496957 = 1686359) B1686359
theorem B4070999 : Blo 591290 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B2137747 : Blo 591290 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B1285831 : Blo 591290 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B4562747 : Blo 591290 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B892847 : Blo 591290 892847 := bstep (se 1 (by rfl) ⟨669635, by rfl⟩ : syracuseStep 892847 = 1339271) B1339271
theorem B2007287 : Blo 591290 2007287 := bstep (se 1 (by rfl) ⟨1505465, by rfl⟩ : syracuseStep 2007287 = 3010931) B3010931
theorem B4497929 : Blo 591290 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B1122835 : Blo 591290 1122835 := bstep (se 1 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 1122835 = 1684253) B1684253
theorem B2007611 : Blo 591290 2007611 := bstep (se 1 (by rfl) ⟨1505708, by rfl⟩ : syracuseStep 2007611 = 3011417) B3011417
theorem B2007881 : Blo 591290 2007881 := bstep (se 2 (by rfl) ⟨752955, by rfl⟩ : syracuseStep 2007881 = 1505911) B1505911
theorem B3089335 : Blo 591290 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B631847 : Blo 591290 631847 := bstep (se 1 (by rfl) ⟨473885, by rfl⟩ : syracuseStep 631847 = 947771) B947771
theorem B3384929 : Blo 591290 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B960247 : Blo 591290 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B1714081 : Blo 591290 1714081 := bstep (se 2 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 1714081 = 1285561) B1285561
theorem B2009015 : Blo 591290 2009015 := bstep (se 1 (by rfl) ⟨1506761, by rfl⟩ : syracuseStep 2009015 = 3013523) B3013523
theorem B4499387 : Blo 591290 4499387 := bstep (se 1 (by rfl) ⟨3374540, by rfl⟩ : syracuseStep 4499387 = 6749081) B6749081
theorem B665563 : Blo 591290 665563 := bstep (se 1 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 665563 = 998345) B998345
theorem B15247763 : Blo 591290 15247763 := bstep (se 1 (by rfl) ⟨11435822, by rfl⟩ : syracuseStep 15247763 = 22871645) B22871645
theorem B666031 : Blo 591290 666031 := bstep (se 1 (by rfl) ⟨499523, by rfl⟩ : syracuseStep 666031 = 999047) B999047
theorem B4336075 : Blo 591290 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B2533913 : Blo 591290 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B666463 : Blo 591290 666463 := bstep (se 1 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 666463 = 999695) B999695
theorem B1125227 : Blo 591290 1125227 := bstep (se 1 (by rfl) ⟨843920, by rfl⟩ : syracuseStep 1125227 = 1687841) B1687841
theorem B3386387 : Blo 591290 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B12201155 : Blo 591290 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B666823 : Blo 591290 666823 := bstep (se 1 (by rfl) ⟨500117, by rfl⟩ : syracuseStep 666823 = 1000235) B1000235
theorem B3386843 : Blo 591290 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B4107763 : Blo 591290 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B1125895 : Blo 591290 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B8564413 : Blo 591290 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B3387095 : Blo 591290 3387095 := bstep (se 1 (by rfl) ⟨2540321, by rfl⟩ : syracuseStep 3387095 = 5080643) B5080643
theorem B1421243 : Blo 591290 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B82161611 : Blo 591290 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B667687 : Blo 591290 667687 := bstep (se 1 (by rfl) ⟨500765, by rfl⟩ : syracuseStep 667687 = 1001531) B1001531
theorem B1126457 : Blo 591290 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B962923 : Blo 591290 962923 := bstep (se 1 (by rfl) ⟨722192, by rfl⟩ : syracuseStep 962923 = 1444385) B1444385
theorem B799195 : Blo 591290 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B7582571 : Blo 591290 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B2438225 : Blo 591290 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B1684651 : Blo 591290 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B963833 : Blo 591290 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B8697289 : Blo 591290 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B1127945 : Blo 591290 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B2537057 : Blo 591290 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B669307 : Blo 591290 669307 := bstep (se 1 (by rfl) ⟨501980, by rfl⟩ : syracuseStep 669307 = 1003961) B1003961
theorem B1423097 : Blo 591290 1423097 := bstep (se 2 (by rfl) ⟨533661, by rfl⟩ : syracuseStep 1423097 = 1067323) B1067323
theorem B2897657 : Blo 591290 2897657 := bstep (se 2 (by rfl) ⟨1086621, by rfl⟩ : syracuseStep 2897657 = 2173243) B2173243
theorem B3389303 : Blo 591290 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B8566721 : Blo 591290 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B4798541 : Blo 591290 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B3618931 : Blo 591290 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B1128811 : Blo 591290 1128811 := bstep (se 1 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 1128811 = 1693217) B1693217
theorem B1128887 : Blo 591290 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B1686041 : Blo 591290 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B3390011 : Blo 591290 3390011 := bstep (se 1 (by rfl) ⟨2542508, by rfl⟩ : syracuseStep 3390011 = 5085017) B5085017
theorem B997967 : Blo 591290 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B1129403 : Blo 591290 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B2997647 : Blo 591290 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B1129889 : Blo 591290 1129889 := bstep (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) B847417
theorem B998831 : Blo 591290 998831 := bstep (se 1 (by rfl) ⟨749123, by rfl⟩ : syracuseStep 998831 = 1498247) B1498247
theorem B2538971 : Blo 591290 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B1130041 : Blo 591290 1130041 := bstep (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) B847531
theorem B1425019 : Blo 591290 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B999263 : Blo 591290 999263 := bstep (se 1 (by rfl) ⟨749447, by rfl⟩ : syracuseStep 999263 = 1498895) B1498895
theorem B2572631 : Blo 591290 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B999823 : Blo 591290 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B2245259 : Blo 591290 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B1426249 : Blo 591290 1426249 := bstep (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) B1069687
theorem B7685039 : Blo 591290 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B4277249 : Blo 591290 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B1000505 : Blo 591290 1000505 := bstep (se 2 (by rfl) ⟨375189, by rfl⟩ : syracuseStep 1000505 = 750379) B750379
theorem B1688957 : Blo 591290 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B6768035 : Blo 591290 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4343203 : Blo 591290 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B2999753 : Blo 591290 2999753 := bstep (se 2 (by rfl) ⟨1124907, by rfl⟩ : syracuseStep 2999753 = 2249815) B2249815
theorem B1689299 : Blo 591290 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B1001207 : Blo 591290 1001207 := bstep (se 1 (by rfl) ⟨750905, by rfl⟩ : syracuseStep 1001207 = 1501811) B1501811
theorem B2541431 : Blo 591290 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B1001551 : Blo 591290 1001551 := bstep (se 1 (by rfl) ⟨751163, by rfl⟩ : syracuseStep 1001551 = 1502327) B1502327
theorem B3000401 : Blo 591290 3000401 := bstep (se 2 (by rfl) ⟨1125150, by rfl⟩ : syracuseStep 3000401 = 2250301) B2250301
theorem B12208229 : Blo 591290 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B1001801 : Blo 591290 1001801 := bstep (se 2 (by rfl) ⟨375675, by rfl⟩ : syracuseStep 1001801 = 751351) B751351
theorem B19286423 : Blo 591290 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B9652871 : Blo 591290 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B1690301 : Blo 591290 1690301 := bstep (se 3 (by rfl) ⟨316931, by rfl⟩ : syracuseStep 1690301 = 633863) B633863
theorem B1002233 : Blo 591290 1002233 := bstep (se 2 (by rfl) ⟨375837, by rfl⟩ : syracuseStep 1002233 = 751675) B751675
theorem B1067951 : Blo 591290 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B1002415 : Blo 591290 1002415 := bstep (se 1 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 1002415 = 1503623) B1503623
theorem B1002503 : Blo 591290 1002503 := bstep (se 1 (by rfl) ⟨751877, by rfl⟩ : syracuseStep 1002503 = 1503755) B1503755
theorem B1002847 : Blo 591290 1002847 := bstep (se 1 (by rfl) ⟨752135, by rfl⟩ : syracuseStep 1002847 = 1504271) B1504271
theorem B2936237 : Blo 591290 2936237 := bstep (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) B1101089
theorem B1002935 : Blo 591290 1002935 := bstep (se 1 (by rfl) ⟨752201, by rfl⟩ : syracuseStep 1002935 = 1504403) B1504403
theorem B1330811 : Blo 591290 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B1625723 : Blo 591290 1625723 := bstep (se 1 (by rfl) ⟨1219292, by rfl⟩ : syracuseStep 1625723 = 2438585) B2438585
theorem B1330937 : Blo 591290 1330937 := bstep (se 2 (by rfl) ⟨499101, by rfl⟩ : syracuseStep 1330937 = 998203) B998203
theorem B2248631 : Blo 591290 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1331207 : Blo 591290 1331207 := bstep (se 1 (by rfl) ⟨998405, by rfl⟩ : syracuseStep 1331207 = 1996811) B1996811
theorem B1003529 : Blo 591290 1003529 := bstep (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) B752647
theorem B1331279 : Blo 591290 1331279 := bstep (se 1 (by rfl) ⟨998459, by rfl⟩ : syracuseStep 1331279 = 1996919) B1996919
theorem B1003691 : Blo 591290 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B6410507 : Blo 591290 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B2412929 : Blo 591290 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B1331675 : Blo 591290 1331675 := bstep (se 1 (by rfl) ⟨998756, by rfl⟩ : syracuseStep 1331675 = 1997513) B1997513
theorem B1004089 : Blo 591290 1004089 := bstep (se 2 (by rfl) ⟨376533, by rfl⟩ : syracuseStep 1004089 = 753067) B753067
theorem B1004231 : Blo 591290 1004231 := bstep (se 1 (by rfl) ⟨753173, by rfl⟩ : syracuseStep 1004231 = 1506347) B1506347
theorem B1004393 : Blo 591290 1004393 := bstep (se 2 (by rfl) ⟨376647, by rfl⟩ : syracuseStep 1004393 = 753295) B753295
theorem B2249633 : Blo 591290 2249633 := bstep (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) B1687225
theorem B1332143 : Blo 591290 1332143 := bstep (se 1 (by rfl) ⟨999107, by rfl⟩ : syracuseStep 1332143 = 1998215) B1998215
theorem B1266607 : Blo 591290 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B1692829 : Blo 591290 1692829 := bstep (se 3 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 1692829 = 634811) B634811
theorem B1332395 : Blo 591290 1332395 := bstep (se 1 (by rfl) ⟨999296, by rfl⟩ : syracuseStep 1332395 = 1998593) B1998593
theorem B2250089 : Blo 591290 2250089 := bstep (se 2 (by rfl) ⟨843783, by rfl⟩ : syracuseStep 2250089 = 1687567) B1687567
theorem B1693057 : Blo 591290 1693057 := bstep (se 2 (by rfl) ⟨634896, by rfl⟩ : syracuseStep 1693057 = 1269793) B1269793
theorem B2283041 : Blo 591290 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B1332935 : Blo 591290 1332935 := bstep (se 1 (by rfl) ⟨999701, by rfl⟩ : syracuseStep 1332935 = 1999403) B1999403
theorem B1693399 : Blo 591290 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B4347715 : Blo 591290 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B2250605 : Blo 591290 2250605 := bstep (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) B843977
theorem B3856313 : Blo 591290 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B841927 : Blo 591290 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1071353 : Blo 591290 1071353 := bstep (se 2 (by rfl) ⟨401757, by rfl⟩ : syracuseStep 1071353 = 803515) B803515
theorem B1497487 : Blo 591290 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B1268111 : Blo 591290 1268111 := bstep (se 1 (by rfl) ⟨951083, by rfl⟩ : syracuseStep 1268111 = 1902167) B1902167
theorem B2251273 : Blo 591290 2251273 := bstep (se 2 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 2251273 = 1688455) B1688455
theorem B3004937 : Blo 591290 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B1333799 : Blo 591290 1333799 := bstep (se 1 (by rfl) ⟨1000349, by rfl⟩ : syracuseStep 1333799 = 2000699) B2000699
theorem B1497811 : Blo 591290 1497811 := bstep (se 1 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 1497811 = 2246717) B2246717
theorem B1334123 : Blo 591290 1334123 := bstep (se 1 (by rfl) ⟨1000592, by rfl⟩ : syracuseStep 1334123 = 2001185) B2001185
theorem B1334177 : Blo 591290 1334177 := bstep (se 2 (by rfl) ⟨500316, by rfl⟩ : syracuseStep 1334177 = 1000633) B1000633
theorem B711607 : Blo 591290 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B10279979 : Blo 591290 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B1334519 : Blo 591290 1334519 := bstep (se 1 (by rfl) ⟨1000889, by rfl⟩ : syracuseStep 1334519 = 2001779) B2001779
theorem B2842235 : Blo 591290 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B1498763 : Blo 591290 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B1335113 : Blo 591290 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B2252731 : Blo 591290 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B3006395 : Blo 591290 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B31252493 : Blo 591290 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B3792977 : Blo 591290 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1335905 : Blo 591290 1335905 := bstep (se 2 (by rfl) ⟨500964, by rfl⟩ : syracuseStep 1335905 = 1001929) B1001929
theorem B8774245 : Blo 591290 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B2253521 : Blo 591290 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B1499897 : Blo 591290 1499897 := bstep (se 2 (by rfl) ⟨562461, by rfl⟩ : syracuseStep 1499897 = 1124923) B1124923
theorem B713567 : Blo 591290 713567 := bstep (se 1 (by rfl) ⟨535175, by rfl⟩ : syracuseStep 713567 = 1070351) B1070351
theorem B1500079 : Blo 591290 1500079 := bstep (se 1 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 1500079 = 2250119) B2250119
theorem B1336247 : Blo 591290 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B2253977 : Blo 591290 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B3007691 : Blo 591290 3007691 := bstep (se 1 (by rfl) ⟨2255768, by rfl⟩ : syracuseStep 3007691 = 4511537) B4511537
theorem B3433751 : Blo 591290 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1500545 : Blo 591290 1500545 := bstep (se 2 (by rfl) ⟨562704, by rfl⟩ : syracuseStep 1500545 = 1125409) B1125409
theorem B845321 : Blo 591290 845321 := bstep (se 2 (by rfl) ⟨316995, by rfl⟩ : syracuseStep 845321 = 633991) B633991
theorem B1336841 : Blo 591290 1336841 := bstep (se 2 (by rfl) ⟨501315, by rfl⟩ : syracuseStep 1336841 = 1002631) B1002631
theorem B4515425 : Blo 591290 4515425 := bstep (se 2 (by rfl) ⟨1693284, by rfl⟩ : syracuseStep 4515425 = 3386569) B3386569
theorem B845435 : Blo 591290 845435 := bstep (se 1 (by rfl) ⟨634076, by rfl⟩ : syracuseStep 845435 = 1268153) B1268153
theorem B1501001 : Blo 591290 1501001 := bstep (se 2 (by rfl) ⟨562875, by rfl⟩ : syracuseStep 1501001 = 1125751) B1125751
theorem B1337183 : Blo 591290 1337183 := bstep (se 1 (by rfl) ⟨1002887, by rfl⟩ : syracuseStep 1337183 = 2005775) B2005775
theorem B845743 : Blo 591290 845743 := bstep (se 1 (by rfl) ⟨634307, by rfl⟩ : syracuseStep 845743 = 1268615) B1268615
theorem B3368891 : Blo 591290 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B1599419 : Blo 591290 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B1337363 : Blo 591290 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B1501355 : Blo 591290 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B846073 : Blo 591290 846073 := bstep (se 2 (by rfl) ⟨317277, by rfl⟩ : syracuseStep 846073 = 634555) B634555
theorem B1337705 : Blo 591290 1337705 := bstep (se 2 (by rfl) ⟨501639, by rfl⟩ : syracuseStep 1337705 = 1003279) B1003279
theorem B5400985 : Blo 591290 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B2025947 : Blo 591290 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B3795437 : Blo 591290 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B1502135 : Blo 591290 1502135 := bstep (se 1 (by rfl) ⟨1126601, by rfl⟩ : syracuseStep 1502135 = 2253203) B2253203
theorem B1338299 : Blo 591290 1338299 := bstep (se 1 (by rfl) ⟨1003724, by rfl⟩ : syracuseStep 1338299 = 2007449) B2007449
theorem B4516883 : Blo 591290 4516883 := bstep (se 1 (by rfl) ⟨3387662, by rfl⟩ : syracuseStep 4516883 = 6775325) B6775325
theorem B1338425 : Blo 591290 1338425 := bstep (se 2 (by rfl) ⟨501909, by rfl⟩ : syracuseStep 1338425 = 1003819) B1003819
theorem B2255951 : Blo 591290 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B2256119 : Blo 591290 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B1338767 : Blo 591290 1338767 := bstep (se 1 (by rfl) ⟨1004075, by rfl⟩ : syracuseStep 1338767 = 2008151) B2008151
theorem B3796541 : Blo 591290 3796541 := bstep (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) B1423703
theorem B32566859 : Blo 591290 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B749179 : Blo 591290 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B2715275 : Blo 591290 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B1339091 : Blo 591290 1339091 := bstep (se 1 (by rfl) ⟨1004318, by rfl⟩ : syracuseStep 1339091 = 2008637) B2008637
theorem B3796769 : Blo 591290 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B749407 : Blo 591290 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B3600247 : Blo 591290 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B1503137 : Blo 591290 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B1896463 : Blo 591290 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B2257091 : Blo 591290 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B1503593 : Blo 591290 1503593 := bstep (se 2 (by rfl) ⟨563847, by rfl⟩ : syracuseStep 1503593 = 1127695) B1127695
theorem B749999 : Blo 591290 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B4289357 : Blo 591290 4289357 := bstep (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) B1608509
theorem B947207 : Blo 591290 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B2258077 : Blo 591290 2258077 := bstep (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) B846779
theorem B1995947 : Blo 591290 1995947 := bstep (se 1 (by rfl) ⟨1496960, by rfl⟩ : syracuseStep 1995947 = 2993921) B2993921
theorem B1504777 : Blo 591290 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B1996487 : Blo 591290 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B947911 : Blo 591290 947911 := bstep (se 1 (by rfl) ⟨710933, by rfl⟩ : syracuseStep 947911 = 1421867) B1421867
theorem B1013447 : Blo 591290 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B10385189 : Blo 591290 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B4519799 : Blo 591290 4519799 := bstep (se 1 (by rfl) ⟨3389849, by rfl⟩ : syracuseStep 4519799 = 6779699) B6779699
theorem B6092857 : Blo 591290 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B3012875 : Blo 591290 3012875 := bstep (se 1 (by rfl) ⟨2259656, by rfl⟩ : syracuseStep 3012875 = 4519313) B4519313
theorem B9107761 : Blo 591290 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B1997351 : Blo 591290 1997351 := bstep (se 1 (by rfl) ⟨1498013, by rfl⟩ : syracuseStep 1997351 = 2996027) B2996027
theorem B1997459 : Blo 591290 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B1014601 : Blo 591290 1014601 := bstep (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) B760951
theorem B1899359 : Blo 591290 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B1997675 : Blo 591290 1997675 := bstep (se 1 (by rfl) ⟨1498256, by rfl⟩ : syracuseStep 1997675 = 2996513) B2996513
theorem B1997729 : Blo 591290 1997729 := bstep (se 2 (by rfl) ⟨749148, by rfl⟩ : syracuseStep 1997729 = 1498297) B1498297
theorem B1506235 : Blo 591290 1506235 := bstep (se 1 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 1506235 = 2259353) B2259353
theorem B1998323 : Blo 591290 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B2851499 : Blo 591290 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B11698993 : Blo 591290 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B1999835 : Blo 591290 1999835 := bstep (se 1 (by rfl) ⟨1499876, by rfl⟩ : syracuseStep 1999835 = 2999753) B2999753
theorem B1901665 : Blo 591290 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B1999997 : Blo 591290 1999997 := bstep (se 3 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 1999997 = 749999) B749999
theorem B2000105 : Blo 591290 2000105 := bstep (se 2 (by rfl) ⟨750039, by rfl⟩ : syracuseStep 2000105 = 1500079) B1500079
theorem B6489379 : Blo 591290 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B2000267 : Blo 591290 2000267 := bstep (se 1 (by rfl) ⟨1500200, by rfl⟩ : syracuseStep 2000267 = 3000401) B3000401
theorem B591355 : Blo 591290 591355 := bstep (se 1 (by rfl) ⟨443516, by rfl⟩ : syracuseStep 591355 = 887033) B887033
theorem B591423 : Blo 591290 591423 := bstep (se 1 (by rfl) ⟨443567, by rfl⟩ : syracuseStep 591423 = 887135) B887135
theorem B591431 : Blo 591290 591431 := bstep (se 1 (by rfl) ⟨443573, by rfl⟩ : syracuseStep 591431 = 887147) B887147
theorem B591583 : Blo 591290 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B1443625 : Blo 591290 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B591663 : Blo 591290 591663 := bstep (se 1 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 591663 = 887495) B887495
theorem B591771 : Blo 591290 591771 := bstep (se 1 (by rfl) ⟨443828, by rfl⟩ : syracuseStep 591771 = 887657) B887657
theorem B591823 : Blo 591290 591823 := bstep (se 1 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 591823 = 887735) B887735
theorem B591847 : Blo 591290 591847 := bstep (se 1 (by rfl) ⟨443885, by rfl⟩ : syracuseStep 591847 = 887771) B887771
theorem B1902845 : Blo 591290 1902845 := bstep (se 3 (by rfl) ⟨356783, by rfl⟩ : syracuseStep 1902845 = 713567) B713567
theorem B592159 : Blo 591290 592159 := bstep (se 1 (by rfl) ⟨444119, by rfl⟩ : syracuseStep 592159 = 888239) B888239
theorem B1280329 : Blo 591290 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B592219 : Blo 591290 592219 := bstep (se 1 (by rfl) ⟨444164, by rfl⟩ : syracuseStep 592219 = 888329) B888329
theorem B592239 : Blo 591290 592239 := bstep (se 1 (by rfl) ⟨444179, by rfl⟩ : syracuseStep 592239 = 888359) B888359
theorem B887207 : Blo 591290 887207 := bstep (se 1 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 887207 = 1330811) B1330811
theorem B592295 : Blo 591290 592295 := bstep (se 1 (by rfl) ⟨444221, by rfl⟩ : syracuseStep 592295 = 888443) B888443
theorem B2165159 : Blo 591290 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B1083815 : Blo 591290 1083815 := bstep (se 1 (by rfl) ⟨812861, by rfl⟩ : syracuseStep 1083815 = 1625723) B1625723
theorem B887291 : Blo 591290 887291 := bstep (se 1 (by rfl) ⟨665468, by rfl⟩ : syracuseStep 887291 = 1330937) B1330937
theorem B592379 : Blo 591290 592379 := bstep (se 1 (by rfl) ⟨444284, by rfl⟩ : syracuseStep 592379 = 888569) B888569
theorem B592447 : Blo 591290 592447 := bstep (se 1 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 592447 = 888671) B888671
theorem B592455 : Blo 591290 592455 := bstep (se 1 (by rfl) ⟨444341, by rfl⟩ : syracuseStep 592455 = 888683) B888683
theorem B887417 : Blo 591290 887417 := bstep (se 2 (by rfl) ⟨332781, by rfl⟩ : syracuseStep 887417 = 665563) B665563
theorem B887471 : Blo 591290 887471 := bstep (se 1 (by rfl) ⟨665603, by rfl⟩ : syracuseStep 887471 = 1331207) B1331207
theorem B887519 : Blo 591290 887519 := bstep (se 1 (by rfl) ⟨665639, by rfl⟩ : syracuseStep 887519 = 1331279) B1331279
theorem B592607 : Blo 591290 592607 := bstep (se 1 (by rfl) ⟨444455, by rfl⟩ : syracuseStep 592607 = 888911) B888911
theorem B592687 : Blo 591290 592687 := bstep (se 1 (by rfl) ⟨444515, by rfl⟩ : syracuseStep 592687 = 889031) B889031
theorem B592795 : Blo 591290 592795 := bstep (se 1 (by rfl) ⟨444596, by rfl⟩ : syracuseStep 592795 = 889193) B889193
theorem B1608619 : Blo 591290 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B592847 : Blo 591290 592847 := bstep (se 1 (by rfl) ⟨444635, by rfl⟩ : syracuseStep 592847 = 889271) B889271
theorem B887783 : Blo 591290 887783 := bstep (se 1 (by rfl) ⟨665837, by rfl⟩ : syracuseStep 887783 = 1331675) B1331675
theorem B592871 : Blo 591290 592871 := bstep (se 1 (by rfl) ⟨444653, by rfl⟩ : syracuseStep 592871 = 889307) B889307
theorem B888041 : Blo 591290 888041 := bstep (se 2 (by rfl) ⟨333015, by rfl⟩ : syracuseStep 888041 = 666031) B666031
theorem B888095 : Blo 591290 888095 := bstep (se 1 (by rfl) ⟨666071, by rfl⟩ : syracuseStep 888095 = 1332143) B1332143
theorem B593183 : Blo 591290 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B593243 : Blo 591290 593243 := bstep (se 1 (by rfl) ⟨444932, by rfl⟩ : syracuseStep 593243 = 889865) B889865
theorem B593263 : Blo 591290 593263 := bstep (se 1 (by rfl) ⟨444947, by rfl⟩ : syracuseStep 593263 = 889895) B889895
theorem B593319 : Blo 591290 593319 := bstep (se 1 (by rfl) ⟨444989, by rfl⟩ : syracuseStep 593319 = 889979) B889979
theorem B888263 : Blo 591290 888263 := bstep (se 1 (by rfl) ⟨666197, by rfl⟩ : syracuseStep 888263 = 1332395) B1332395
theorem B593403 : Blo 591290 593403 := bstep (se 1 (by rfl) ⟨445052, by rfl⟩ : syracuseStep 593403 = 890105) B890105
theorem B593471 : Blo 591290 593471 := bstep (se 1 (by rfl) ⟨445103, by rfl⟩ : syracuseStep 593471 = 890207) B890207
theorem B593479 : Blo 591290 593479 := bstep (se 1 (by rfl) ⟨445109, by rfl⟩ : syracuseStep 593479 = 890219) B890219
theorem B593631 : Blo 591290 593631 := bstep (se 1 (by rfl) ⟨445223, by rfl⟩ : syracuseStep 593631 = 890447) B890447
theorem B888617 : Blo 591290 888617 := bstep (se 2 (by rfl) ⟨333231, by rfl⟩ : syracuseStep 888617 = 666463) B666463
theorem B9899819 : Blo 591290 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B888623 : Blo 591290 888623 := bstep (se 1 (by rfl) ⟨666467, by rfl⟩ : syracuseStep 888623 = 1332935) B1332935
theorem B593711 : Blo 591290 593711 := bstep (se 1 (by rfl) ⟨445283, by rfl⟩ : syracuseStep 593711 = 890567) B890567
theorem B593819 : Blo 591290 593819 := bstep (se 1 (by rfl) ⟨445364, by rfl⟩ : syracuseStep 593819 = 890729) B890729
theorem B593871 : Blo 591290 593871 := bstep (se 1 (by rfl) ⟨445403, by rfl⟩ : syracuseStep 593871 = 890807) B890807
theorem B593895 : Blo 591290 593895 := bstep (se 1 (by rfl) ⟨445421, by rfl⟩ : syracuseStep 593895 = 890843) B890843
theorem B889097 : Blo 591290 889097 := bstep (se 2 (by rfl) ⟨333411, by rfl⟩ : syracuseStep 889097 = 666823) B666823
theorem B594207 : Blo 591290 594207 := bstep (se 1 (by rfl) ⟨445655, by rfl⟩ : syracuseStep 594207 = 891311) B891311
theorem B2003291 : Blo 591290 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B594267 : Blo 591290 594267 := bstep (se 1 (by rfl) ⟨445700, by rfl⟩ : syracuseStep 594267 = 891401) B891401
theorem B889199 : Blo 591290 889199 := bstep (se 1 (by rfl) ⟨666899, by rfl⟩ : syracuseStep 889199 = 1333799) B1333799
theorem B594287 : Blo 591290 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B594343 : Blo 591290 594343 := bstep (se 1 (by rfl) ⟨445757, by rfl⟩ : syracuseStep 594343 = 891515) B891515
theorem B594427 : Blo 591290 594427 := bstep (se 1 (by rfl) ⟨445820, by rfl⟩ : syracuseStep 594427 = 891641) B891641
theorem B594495 : Blo 591290 594495 := bstep (se 1 (by rfl) ⟨445871, by rfl⟩ : syracuseStep 594495 = 891743) B891743
theorem B889415 : Blo 591290 889415 := bstep (se 1 (by rfl) ⟨667061, by rfl⟩ : syracuseStep 889415 = 1334123) B1334123
theorem B594503 : Blo 591290 594503 := bstep (se 1 (by rfl) ⟨445877, by rfl⟩ : syracuseStep 594503 = 891755) B891755
theorem B889451 : Blo 591290 889451 := bstep (se 1 (by rfl) ⟨667088, by rfl⟩ : syracuseStep 889451 = 1334177) B1334177
theorem B6853319 : Blo 591290 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B594655 : Blo 591290 594655 := bstep (se 1 (by rfl) ⟨445991, by rfl⟩ : syracuseStep 594655 = 891983) B891983
theorem B594735 : Blo 591290 594735 := bstep (se 1 (by rfl) ⟨446051, by rfl⟩ : syracuseStep 594735 = 892103) B892103
theorem B889679 : Blo 591290 889679 := bstep (se 1 (by rfl) ⟨667259, by rfl⟩ : syracuseStep 889679 = 1334519) B1334519
theorem B594843 : Blo 591290 594843 := bstep (se 1 (by rfl) ⟨446132, by rfl⟩ : syracuseStep 594843 = 892265) B892265
theorem B594895 : Blo 591290 594895 := bstep (se 1 (by rfl) ⟨446171, by rfl⟩ : syracuseStep 594895 = 892343) B892343
theorem B594919 : Blo 591290 594919 := bstep (se 1 (by rfl) ⟨446189, by rfl⟩ : syracuseStep 594919 = 892379) B892379
theorem B890075 : Blo 591290 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B595231 : Blo 591290 595231 := bstep (se 1 (by rfl) ⟨446423, by rfl⟩ : syracuseStep 595231 = 892847) B892847
theorem B2004263 : Blo 591290 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B2528617 : Blo 591290 2528617 := bstep (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) B1896463
theorem B890249 : Blo 591290 890249 := bstep (se 2 (by rfl) ⟨333843, by rfl⟩ : syracuseStep 890249 = 667687) B667687
theorem B2528651 : Blo 591290 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B890603 : Blo 591290 890603 := bstep (se 1 (by rfl) ⟨667952, by rfl⟩ : syracuseStep 890603 = 1335905) B1335905
theorem B1283897 : Blo 591290 1283897 := bstep (se 2 (by rfl) ⟨481461, by rfl⟩ : syracuseStep 1283897 = 962923) B962923
theorem B890831 : Blo 591290 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B2856941 : Blo 591290 2856941 := bstep (se 3 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 2856941 = 1071353) B1071353
theorem B2005127 : Blo 591290 2005127 := bstep (se 1 (by rfl) ⟨1503845, by rfl⟩ : syracuseStep 2005127 = 3007691) B3007691
theorem B891227 : Blo 591290 891227 := bstep (se 1 (by rfl) ⟨668420, by rfl⟩ : syracuseStep 891227 = 1336841) B1336841
theorem B891455 : Blo 591290 891455 := bstep (se 1 (by rfl) ⟨668591, by rfl⟩ : syracuseStep 891455 = 1337183) B1337183
theorem B891575 : Blo 591290 891575 := bstep (se 1 (by rfl) ⟨668681, by rfl⟩ : syracuseStep 891575 = 1337363) B1337363
theorem B891803 : Blo 591290 891803 := bstep (se 1 (by rfl) ⟨668852, by rfl⟩ : syracuseStep 891803 = 1337705) B1337705
theorem B10165175 : Blo 591290 10165175 := bstep (se 1 (by rfl) ⟨7623881, by rfl⟩ : syracuseStep 10165175 = 15247763) B15247763
theorem B1350631 : Blo 591290 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B2530291 : Blo 591290 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B892199 : Blo 591290 892199 := bstep (se 1 (by rfl) ⟨669149, by rfl⟩ : syracuseStep 892199 = 1338299) B1338299
theorem B2006369 : Blo 591290 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B892283 : Blo 591290 892283 := bstep (se 1 (by rfl) ⟨669212, by rfl⟩ : syracuseStep 892283 = 1338425) B1338425
theorem B8134103 : Blo 591290 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B892409 : Blo 591290 892409 := bstep (se 2 (by rfl) ⟨334653, by rfl⟩ : syracuseStep 892409 = 669307) B669307
theorem B892511 : Blo 591290 892511 := bstep (se 1 (by rfl) ⟨669383, by rfl⟩ : syracuseStep 892511 = 1338767) B1338767
theorem B2531027 : Blo 591290 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B1810183 : Blo 591290 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B892727 : Blo 591290 892727 := bstep (se 1 (by rfl) ⟨669545, by rfl⟩ : syracuseStep 892727 = 1339091) B1339091
theorem B2531179 : Blo 591290 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B4825241 : Blo 591290 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B1122569 : Blo 591290 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B2859571 : Blo 591290 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B5055047 : Blo 591290 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B631471 : Blo 591290 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B1352801 : Blo 591290 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B6923459 : Blo 591290 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B2008313 : Blo 591290 2008313 := bstep (se 2 (by rfl) ⟨753117, by rfl⟩ : syracuseStep 2008313 = 1506235) B1506235
theorem B5711147 : Blo 591290 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B2008583 : Blo 591290 2008583 := bstep (se 1 (by rfl) ⟨1506437, by rfl⟩ : syracuseStep 2008583 = 3012875) B3012875
theorem B1124027 : Blo 591290 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B665311 : Blo 591290 665311 := bstep (se 1 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 665311 = 997967) B997967
theorem B1714441 : Blo 591290 1714441 := bstep (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) B1285831
theorem B665887 : Blo 591290 665887 := bstep (se 1 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 665887 = 998831) B998831
theorem B666175 : Blo 591290 666175 := bstep (se 1 (by rfl) ⟨499631, by rfl⟩ : syracuseStep 666175 = 999263) B999263
theorem B4500359 : Blo 591290 4500359 := bstep (se 1 (by rfl) ⟨3375269, by rfl⟩ : syracuseStep 4500359 = 6750539) B6750539
theorem B1715087 : Blo 591290 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B5123359 : Blo 591290 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B667003 : Blo 591290 667003 := bstep (se 1 (by rfl) ⟨500252, by rfl⟩ : syracuseStep 667003 = 1000505) B1000505
theorem B2141711 : Blo 591290 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B1125971 : Blo 591290 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B2993759 : Blo 591290 2993759 := bstep (se 1 (by rfl) ⟨2245319, by rfl⟩ : syracuseStep 2993759 = 4490639) B4490639
theorem B1126199 : Blo 591290 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B667471 : Blo 591290 667471 := bstep (se 1 (by rfl) ⟨500603, by rfl⟩ : syracuseStep 667471 = 1001207) B1001207
theorem B8138819 : Blo 591290 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B667867 : Blo 591290 667867 := bstep (se 1 (by rfl) ⟨500900, by rfl⟩ : syracuseStep 667867 = 1001801) B1001801
theorem B12857615 : Blo 591290 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B1126867 : Blo 591290 1126867 := bstep (se 1 (by rfl) ⟨845150, by rfl⟩ : syracuseStep 1126867 = 1690301) B1690301
theorem B668155 : Blo 591290 668155 := bstep (se 1 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 668155 = 1002233) B1002233
theorem B1421887 : Blo 591290 1421887 := bstep (se 1 (by rfl) ⟨1066415, by rfl⟩ : syracuseStep 1421887 = 2132831) B2132831
theorem B668335 : Blo 591290 668335 := bstep (se 1 (by rfl) ⟨501251, by rfl⟩ : syracuseStep 668335 = 1002503) B1002503
theorem B668623 : Blo 591290 668623 := bstep (se 1 (by rfl) ⟨501467, by rfl⟩ : syracuseStep 668623 = 1002935) B1002935
theorem B1127657 : Blo 591290 1127657 := bstep (se 2 (by rfl) ⟨422871, by rfl⟩ : syracuseStep 1127657 = 845743) B845743
theorem B669019 : Blo 591290 669019 := bstep (se 1 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 669019 = 1003529) B1003529
theorem B1684925 : Blo 591290 1684925 := bstep (se 3 (by rfl) ⟨315923, by rfl⟩ : syracuseStep 1684925 = 631847) B631847
theorem B669127 : Blo 591290 669127 := bstep (se 1 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 669127 = 1003691) B1003691
theorem B1128097 : Blo 591290 1128097 := bstep (se 2 (by rfl) ⟨423036, by rfl⟩ : syracuseStep 1128097 = 846073) B846073
theorem B669487 : Blo 591290 669487 := bstep (se 1 (by rfl) ⟨502115, by rfl⟩ : syracuseStep 669487 = 1004231) B1004231
theorem B669595 : Blo 591290 669595 := bstep (se 1 (by rfl) ⟨502196, by rfl⟩ : syracuseStep 669595 = 1004393) B1004393
theorem B2537399 : Blo 591290 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B2570221 : Blo 591290 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B1522027 : Blo 591290 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1685927 : Blo 591290 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B2406991 : Blo 591290 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B5422301 : Blo 591290 5422301 := bstep (se 3 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 5422301 = 2033363) B2033363
theorem B1686815 : Blo 591290 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B1424827 : Blo 591290 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B998905 : Blo 591290 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B11419217 : Blo 591290 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B1621691 : Blo 591290 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B2997971 : Blo 591290 2997971 := bstep (se 1 (by rfl) ⟨2248478, by rfl⟩ : syracuseStep 2997971 = 4496957) B4496957
theorem B999175 : Blo 591290 999175 := bstep (se 1 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 999175 = 1498763) B1498763
theorem B999209 : Blo 591290 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B4800329 : Blo 591290 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B2998619 : Blo 591290 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B999931 : Blo 591290 999931 := bstep (se 1 (by rfl) ⟨749948, by rfl⟩ : syracuseStep 999931 = 1499897) B1499897
theorem B1065593 : Blo 591290 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B10240685 : Blo 591290 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B1000363 : Blo 591290 1000363 := bstep (se 1 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 1000363 = 1500545) B1500545
theorem B1000667 : Blo 591290 1000667 := bstep (se 1 (by rfl) ⟨750500, by rfl⟩ : syracuseStep 1000667 = 1501001) B1501001
theorem B1688809 : Blo 591290 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B2245927 : Blo 591290 2245927 := bstep (se 1 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 2245927 = 3368891) B3368891
theorem B1066279 : Blo 591290 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B2999591 : Blo 591290 2999591 := bstep (se 1 (by rfl) ⟨2249693, by rfl⟩ : syracuseStep 2999591 = 4499387) B4499387
theorem B1000903 : Blo 591290 1000903 := bstep (se 1 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 1000903 = 1501355) B1501355
theorem B2246201 : Blo 591290 2246201 := bstep (se 2 (by rfl) ⟨842325, by rfl⟩ : syracuseStep 2246201 = 1684651) B1684651
theorem B1689275 : Blo 591290 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B25740989 : Blo 591290 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B1001423 : Blo 591290 1001423 := bstep (se 1 (by rfl) ⟨751067, by rfl⟩ : syracuseStep 1001423 = 1502135) B1502135
theorem B1263881 : Blo 591290 1263881 := bstep (se 2 (by rfl) ⟨473955, by rfl⟩ : syracuseStep 1263881 = 947911) B947911
theorem B21711239 : Blo 591290 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B21908069 : Blo 591290 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1002091 : Blo 591290 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B54774407 : Blo 591290 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B1002395 : Blo 591290 1002395 := bstep (se 1 (by rfl) ⟨751796, by rfl⟩ : syracuseStep 1002395 = 1503593) B1503593
theorem B12143681 : Blo 591290 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B3001697 : Blo 591290 3001697 := bstep (se 2 (by rfl) ⟨1125636, by rfl⟩ : syracuseStep 3001697 = 2251273) B2251273
theorem B1625483 : Blo 591290 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B1330631 : Blo 591290 1330631 := bstep (se 1 (by rfl) ⟨997973, by rfl⟩ : syracuseStep 1330631 = 1995947) B1995947
theorem B6737417 : Blo 591290 6737417 := bstep (se 2 (by rfl) ⟨2526531, by rfl⟩ : syracuseStep 6737417 = 5053063) B5053063
theorem B2674201 : Blo 591290 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B1691371 : Blo 591290 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B1330991 : Blo 591290 1330991 := bstep (se 1 (by rfl) ⟨998243, by rfl⟩ : syracuseStep 1330991 = 1996487) B1996487
theorem B675631 : Blo 591290 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B3199027 : Blo 591290 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B1331567 : Blo 591290 1331567 := bstep (se 1 (by rfl) ⟨998675, by rfl⟩ : syracuseStep 1331567 = 1997351) B1997351
theorem B1331639 : Blo 591290 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B1266239 : Blo 591290 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B1331783 : Blo 591290 1331783 := bstep (se 1 (by rfl) ⟨998837, by rfl⟩ : syracuseStep 1331783 = 1997675) B1997675
theorem B1331819 : Blo 591290 1331819 := bstep (se 1 (by rfl) ⟨998864, by rfl⟩ : syracuseStep 1331819 = 1997729) B1997729
theorem B1692647 : Blo 591290 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B1332215 : Blo 591290 1332215 := bstep (se 1 (by rfl) ⟨999161, by rfl⟩ : syracuseStep 1332215 = 1998323) B1998323
theorem B3003641 : Blo 591290 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B1332575 : Blo 591290 1332575 := bstep (se 1 (by rfl) ⟨999431, by rfl⟩ : syracuseStep 1332575 = 1998863) B1998863
theorem B6772409 : Blo 591290 6772409 := bstep (se 2 (by rfl) ⟨2539653, by rfl⟩ : syracuseStep 6772409 = 5079307) B5079307
theorem B1332971 : Blo 591290 1332971 := bstep (se 1 (by rfl) ⟨999728, by rfl⟩ : syracuseStep 1332971 = 1999457) B1999457
theorem B1267435 : Blo 591290 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B1496839 : Blo 591290 1496839 := bstep (se 1 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 1496839 = 2245259) B2245259
theorem B1333097 : Blo 591290 1333097 := bstep (se 2 (by rfl) ⟨499911, by rfl⟩ : syracuseStep 1333097 = 999823) B999823
theorem B1497113 : Blo 591290 1497113 := bstep (se 2 (by rfl) ⟨561417, by rfl⟩ : syracuseStep 1497113 = 1122835) B1122835
theorem B17094685 : Blo 591290 17094685 := bstep (se 3 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 17094685 = 6410507) B6410507
theorem B24401999 : Blo 591290 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B4512023 : Blo 591290 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B2251259 : Blo 591290 2251259 := bstep (se 1 (by rfl) ⟨1688444, by rfl⟩ : syracuseStep 2251259 = 3376889) B3376889
theorem B4119113 : Blo 591290 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1694287 : Blo 591290 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B1333943 : Blo 591290 1333943 := bstep (se 1 (by rfl) ⟨1000457, by rfl⟩ : syracuseStep 1333943 = 2000915) B2000915
theorem B4807363 : Blo 591290 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B1334159 : Blo 591290 1334159 := bstep (se 1 (by rfl) ⟨1000619, by rfl⟩ : syracuseStep 1334159 = 2001239) B2001239
theorem B5790937 : Blo 591290 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B2252063 : Blo 591290 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B2252231 : Blo 591290 2252231 := bstep (se 1 (by rfl) ⟨1689173, by rfl⟩ : syracuseStep 2252231 = 3378347) B3378347
theorem B1334879 : Blo 591290 1334879 := bstep (se 1 (by rfl) ⟨1001159, by rfl⟩ : syracuseStep 1334879 = 2002319) B2002319
theorem B23125733 : Blo 591290 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B1335095 : Blo 591290 1335095 := bstep (se 1 (by rfl) ⟨1001321, by rfl⟩ : syracuseStep 1335095 = 2002643) B2002643
theorem B2285441 : Blo 591290 2285441 := bstep (se 2 (by rfl) ⟨857040, by rfl⟩ : syracuseStep 2285441 = 1714081) B1714081
theorem B1499087 : Blo 591290 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B1335401 : Blo 591290 1335401 := bstep (se 2 (by rfl) ⟨500775, by rfl⟩ : syracuseStep 1335401 = 1001551) B1001551
theorem B9626141 : Blo 591290 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B7201313 : Blo 591290 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B1335887 : Blo 591290 1335887 := bstep (se 1 (by rfl) ⟨1001915, by rfl⟩ : syracuseStep 1335887 = 2003831) B2003831
theorem B1499755 : Blo 591290 1499755 := bstep (se 1 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 1499755 = 2249633) B2249633
theorem B1336031 : Blo 591290 1336031 := bstep (se 1 (by rfl) ⟨1002023, by rfl⟩ : syracuseStep 1336031 = 2004047) B2004047
theorem B1500059 : Blo 591290 1500059 := bstep (se 1 (by rfl) ⟨1125044, by rfl⟩ : syracuseStep 1500059 = 2250089) B2250089
theorem B1336283 : Blo 591290 1336283 := bstep (se 1 (by rfl) ⟨1002212, by rfl⟩ : syracuseStep 1336283 = 2004425) B2004425
theorem B1336463 : Blo 591290 1336463 := bstep (se 1 (by rfl) ⟨1002347, by rfl⟩ : syracuseStep 1336463 = 2004695) B2004695
theorem B1336553 : Blo 591290 1336553 := bstep (se 2 (by rfl) ⟨501207, by rfl⟩ : syracuseStep 1336553 = 1002415) B1002415
theorem B1500403 : Blo 591290 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B1336607 : Blo 591290 1336607 := bstep (se 1 (by rfl) ⟨1002455, by rfl⟩ : syracuseStep 1336607 = 2004911) B2004911
theorem B2254175 : Blo 591290 2254175 := bstep (se 1 (by rfl) ⟨1690631, by rfl⟩ : syracuseStep 2254175 = 3381263) B3381263
theorem B2254189 : Blo 591290 2254189 := bstep (se 3 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 2254189 = 845321) B845321
theorem B3007853 : Blo 591290 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B845407 : Blo 591290 845407 := bstep (se 1 (by rfl) ⟨634055, by rfl⟩ : syracuseStep 845407 = 1268111) B1268111
theorem B2254493 : Blo 591290 2254493 := bstep (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) B845435
theorem B1337129 : Blo 591290 1337129 := bstep (se 2 (by rfl) ⟨501423, by rfl⟩ : syracuseStep 1337129 = 1002847) B1002847
theorem B2844503 : Blo 591290 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B1501193 : Blo 591290 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B1599851 : Blo 591290 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B2713999 : Blo 591290 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B1894823 : Blo 591290 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B10283501 : Blo 591290 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B3041831 : Blo 591290 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B20834995 : Blo 591290 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B12151565 : Blo 591290 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1338191 : Blo 591290 1338191 := bstep (se 1 (by rfl) ⟨1003643, by rfl⟩ : syracuseStep 1338191 = 2007287) B2007287
theorem B1338407 : Blo 591290 1338407 := bstep (se 1 (by rfl) ⟨1003805, by rfl⟩ : syracuseStep 1338407 = 2007611) B2007611
theorem B1502347 : Blo 591290 1502347 := bstep (se 1 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 1502347 = 2253521) B2253521
theorem B1338587 : Blo 591290 1338587 := bstep (se 1 (by rfl) ⟨1003940, by rfl⟩ : syracuseStep 1338587 = 2007881) B2007881
theorem B13200653 : Blo 591290 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B1338785 : Blo 591290 1338785 := bstep (se 2 (by rfl) ⟨502044, by rfl⟩ : syracuseStep 1338785 = 1004089) B1004089
theorem B25619885 : Blo 591290 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B1502651 : Blo 591290 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B2289167 : Blo 591290 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B2256619 : Blo 591290 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B3010283 : Blo 591290 3010283 := bstep (se 1 (by rfl) ⟨2257712, by rfl⟩ : syracuseStep 3010283 = 4515425) B4515425
theorem B1339343 : Blo 591290 1339343 := bstep (se 1 (by rfl) ⟨1004507, by rfl⟩ : syracuseStep 1339343 = 2009015) B2009015
theorem B2257105 : Blo 591290 2257105 := bstep (se 2 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 2257105 = 1692829) B1692829
theorem B3010769 : Blo 591290 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B2257409 : Blo 591290 2257409 := bstep (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) B1693057
theorem B750151 : Blo 591290 750151 := bstep (se 1 (by rfl) ⟨562613, by rfl⟩ : syracuseStep 750151 = 1125227) B1125227
theorem B11596385 : Blo 591290 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B2257591 : Blo 591290 2257591 := bstep (se 1 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 2257591 = 3386387) B3386387
theorem B3011255 : Blo 591290 3011255 := bstep (se 1 (by rfl) ⟨2258441, by rfl⟩ : syracuseStep 3011255 = 4516883) B4516883
theorem B1503967 : Blo 591290 1503967 := bstep (se 1 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 1503967 = 2255951) B2255951
theorem B1504079 : Blo 591290 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B2257865 : Blo 591290 2257865 := bstep (se 2 (by rfl) ⟨846699, by rfl⟩ : syracuseStep 2257865 = 1693399) B1693399
theorem B2257895 : Blo 591290 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B5796953 : Blo 591290 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B2847869 : Blo 591290 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B2258063 : Blo 591290 2258063 := bstep (se 1 (by rfl) ⟨1693547, by rfl⟩ : syracuseStep 2258063 = 3387095) B3387095
theorem B3011741 : Blo 591290 3011741 := bstep (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) B1129403
theorem B947495 : Blo 591290 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B750971 : Blo 591290 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B8123809 : Blo 591290 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B2848193 : Blo 591290 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B1504727 : Blo 591290 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B1505081 : Blo 591290 1505081 := bstep (se 2 (by rfl) ⟨564405, by rfl⟩ : syracuseStep 1505081 = 1128811) B1128811
theorem B1996649 : Blo 591290 1996649 := bstep (se 2 (by rfl) ⟨748743, by rfl⟩ : syracuseStep 1996649 = 1497487) B1497487
theorem B1997081 : Blo 591290 1997081 := bstep (se 2 (by rfl) ⟨748905, by rfl⟩ : syracuseStep 1997081 = 1497811) B1497811
theorem B3013037 : Blo 591290 3013037 := bstep (se 3 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 3013037 = 1129889) B1129889
theorem B7829965 : Blo 591290 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B948731 : Blo 591290 948731 := bstep (se 1 (by rfl) ⟨711548, by rfl⟩ : syracuseStep 948731 = 1423097) B1423097
theorem B1931771 : Blo 591290 1931771 := bstep (se 1 (by rfl) ⟨1448828, by rfl⟩ : syracuseStep 1931771 = 2897657) B2897657
theorem B948809 : Blo 591290 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B2259535 : Blo 591290 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B3013199 : Blo 591290 3013199 := bstep (se 1 (by rfl) ⟨2259899, by rfl⟩ : syracuseStep 3013199 = 4519799) B4519799
theorem B752591 : Blo 591290 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B2260007 : Blo 591290 2260007 := bstep (se 1 (by rfl) ⟨1695005, by rfl⟩ : syracuseStep 2260007 = 3390011) B3390011
theorem B1506721 : Blo 591290 1506721 := bstep (se 2 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 1506721 = 1130041) B1130041
theorem B1900025 : Blo 591290 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B2850329 : Blo 591290 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B1998431 : Blo 591290 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B1999079 : Blo 591290 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B1900999 : Blo 591290 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B1999673 : Blo 591290 1999673 := bstep (se 2 (by rfl) ⟨749877, by rfl⟩ : syracuseStep 1999673 = 1499755) B1499755
theorem B1999727 : Blo 591290 1999727 := bstep (se 1 (by rfl) ⟨1499795, by rfl⟩ : syracuseStep 1999727 = 2999591) B2999591
theorem B15598657 : Blo 591290 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B3376637 : Blo 591290 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B591471 : Blo 591290 591471 := bstep (se 1 (by rfl) ⟨443603, by rfl⟩ : syracuseStep 591471 = 887207) B887207
theorem B1443439 : Blo 591290 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B722543 : Blo 591290 722543 := bstep (se 1 (by rfl) ⟨541907, by rfl⟩ : syracuseStep 722543 = 1083815) B1083815
theorem B2000537 : Blo 591290 2000537 := bstep (se 2 (by rfl) ⟨750201, by rfl⟩ : syracuseStep 2000537 = 1500403) B1500403
theorem B591527 : Blo 591290 591527 := bstep (se 1 (by rfl) ⟨443645, by rfl⟩ : syracuseStep 591527 = 887291) B887291
theorem B8652505 : Blo 591290 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B591611 : Blo 591290 591611 := bstep (se 1 (by rfl) ⟨443708, by rfl⟩ : syracuseStep 591611 = 887417) B887417
theorem B591647 : Blo 591290 591647 := bstep (se 1 (by rfl) ⟨443735, by rfl⟩ : syracuseStep 591647 = 887471) B887471
theorem B591679 : Blo 591290 591679 := bstep (se 1 (by rfl) ⟨443759, by rfl⟩ : syracuseStep 591679 = 887519) B887519
theorem B591855 : Blo 591290 591855 := bstep (se 1 (by rfl) ⟨443891, by rfl⟩ : syracuseStep 591855 = 887783) B887783
theorem B8095787 : Blo 591290 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B592027 : Blo 591290 592027 := bstep (se 1 (by rfl) ⟨444020, by rfl⟩ : syracuseStep 592027 = 888041) B888041
theorem B592063 : Blo 591290 592063 := bstep (se 1 (by rfl) ⟨444047, by rfl⟩ : syracuseStep 592063 = 888095) B888095
theorem B2001131 : Blo 591290 2001131 := bstep (se 1 (by rfl) ⟨1500848, by rfl⟩ : syracuseStep 2001131 = 3001697) B3001697
theorem B1083655 : Blo 591290 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B887081 : Blo 591290 887081 := bstep (se 2 (by rfl) ⟨332655, by rfl⟩ : syracuseStep 887081 = 665311) B665311
theorem B887087 : Blo 591290 887087 := bstep (se 1 (by rfl) ⟨665315, by rfl⟩ : syracuseStep 887087 = 1330631) B1330631
theorem B592175 : Blo 591290 592175 := bstep (se 1 (by rfl) ⟨444131, by rfl⟩ : syracuseStep 592175 = 888263) B888263
theorem B4491611 : Blo 591290 4491611 := bstep (se 1 (by rfl) ⟨3368708, by rfl⟩ : syracuseStep 4491611 = 6737417) B6737417
theorem B592411 : Blo 591290 592411 := bstep (se 1 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 592411 = 888617) B888617
theorem B887327 : Blo 591290 887327 := bstep (se 1 (by rfl) ⟨665495, by rfl⟩ : syracuseStep 887327 = 1330991) B1330991
theorem B592415 : Blo 591290 592415 := bstep (se 1 (by rfl) ⟨444311, by rfl⟩ : syracuseStep 592415 = 888623) B888623
theorem B592731 : Blo 591290 592731 := bstep (se 1 (by rfl) ⟨444548, by rfl⟩ : syracuseStep 592731 = 889097) B889097
theorem B887711 : Blo 591290 887711 := bstep (se 1 (by rfl) ⟨665783, by rfl⟩ : syracuseStep 887711 = 1331567) B1331567
theorem B592799 : Blo 591290 592799 := bstep (se 1 (by rfl) ⟨444599, by rfl⟩ : syracuseStep 592799 = 889199) B889199
theorem B3607469 : Blo 591290 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B887759 : Blo 591290 887759 := bstep (se 1 (by rfl) ⟨665819, by rfl⟩ : syracuseStep 887759 = 1331639) B1331639
theorem B887849 : Blo 591290 887849 := bstep (se 2 (by rfl) ⟨332943, by rfl⟩ : syracuseStep 887849 = 665887) B665887
theorem B887855 : Blo 591290 887855 := bstep (se 1 (by rfl) ⟨665891, by rfl⟩ : syracuseStep 887855 = 1331783) B1331783
theorem B592943 : Blo 591290 592943 := bstep (se 1 (by rfl) ⟨444707, by rfl⟩ : syracuseStep 592943 = 889415) B889415
theorem B887879 : Blo 591290 887879 := bstep (se 1 (by rfl) ⟨665909, by rfl⟩ : syracuseStep 887879 = 1331819) B1331819
theorem B592967 : Blo 591290 592967 := bstep (se 1 (by rfl) ⟨444725, by rfl⟩ : syracuseStep 592967 = 889451) B889451
theorem B593119 : Blo 591290 593119 := bstep (se 1 (by rfl) ⟨444839, by rfl⟩ : syracuseStep 593119 = 889679) B889679
theorem B888143 : Blo 591290 888143 := bstep (se 1 (by rfl) ⟨666107, by rfl⟩ : syracuseStep 888143 = 1332215) B1332215
theorem B888233 : Blo 591290 888233 := bstep (se 2 (by rfl) ⟨333087, by rfl⟩ : syracuseStep 888233 = 666175) B666175
theorem B2526653 : Blo 591290 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B593383 : Blo 591290 593383 := bstep (se 1 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 593383 = 890075) B890075
theorem B2002427 : Blo 591290 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B888383 : Blo 591290 888383 := bstep (se 1 (by rfl) ⟨666287, by rfl⟩ : syracuseStep 888383 = 1332575) B1332575
theorem B593499 : Blo 591290 593499 := bstep (se 1 (by rfl) ⟨445124, by rfl⟩ : syracuseStep 593499 = 890249) B890249
theorem B2002589 : Blo 591290 2002589 := bstep (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) B750971
theorem B888647 : Blo 591290 888647 := bstep (se 1 (by rfl) ⟨666485, by rfl⟩ : syracuseStep 888647 = 1332971) B1332971
theorem B593735 : Blo 591290 593735 := bstep (se 1 (by rfl) ⟨445301, by rfl⟩ : syracuseStep 593735 = 890603) B890603
theorem B855931 : Blo 591290 855931 := bstep (se 1 (by rfl) ⟨641948, by rfl⟩ : syracuseStep 855931 = 1283897) B1283897
theorem B888731 : Blo 591290 888731 := bstep (se 1 (by rfl) ⟨666548, by rfl⟩ : syracuseStep 888731 = 1333097) B1333097
theorem B593887 : Blo 591290 593887 := bstep (se 1 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 593887 = 890831) B890831
theorem B1904627 : Blo 591290 1904627 := bstep (se 1 (by rfl) ⟨1428470, by rfl⟩ : syracuseStep 1904627 = 2856941) B2856941
theorem B2003129 : Blo 591290 2003129 := bstep (se 2 (by rfl) ⟨751173, by rfl⟩ : syracuseStep 2003129 = 1502347) B1502347
theorem B594151 : Blo 591290 594151 := bstep (se 1 (by rfl) ⟨445613, by rfl⟩ : syracuseStep 594151 = 891227) B891227
theorem B594303 : Blo 591290 594303 := bstep (se 1 (by rfl) ⟨445727, by rfl⟩ : syracuseStep 594303 = 891455) B891455
theorem B889295 : Blo 591290 889295 := bstep (se 1 (by rfl) ⟨666971, by rfl⟩ : syracuseStep 889295 = 1333943) B1333943
theorem B594383 : Blo 591290 594383 := bstep (se 1 (by rfl) ⟨445787, by rfl⟩ : syracuseStep 594383 = 891575) B891575
theorem B889337 : Blo 591290 889337 := bstep (se 2 (by rfl) ⟨333501, by rfl⟩ : syracuseStep 889337 = 667003) B667003
theorem B889439 : Blo 591290 889439 := bstep (se 1 (by rfl) ⟨667079, by rfl⟩ : syracuseStep 889439 = 1334159) B1334159
theorem B594535 : Blo 591290 594535 := bstep (se 1 (by rfl) ⟨445901, by rfl⟩ : syracuseStep 594535 = 891803) B891803
theorem B594799 : Blo 591290 594799 := bstep (se 1 (by rfl) ⟨446099, by rfl⟩ : syracuseStep 594799 = 892199) B892199
theorem B594855 : Blo 591290 594855 := bstep (se 1 (by rfl) ⟨446141, by rfl⟩ : syracuseStep 594855 = 892283) B892283
theorem B594939 : Blo 591290 594939 := bstep (se 1 (by rfl) ⟨446204, by rfl⟩ : syracuseStep 594939 = 892409) B892409
theorem B889919 : Blo 591290 889919 := bstep (se 1 (by rfl) ⟨667439, by rfl⟩ : syracuseStep 889919 = 1334879) B1334879
theorem B595007 : Blo 591290 595007 := bstep (se 1 (by rfl) ⟨446255, by rfl⟩ : syracuseStep 595007 = 892511) B892511
theorem B889961 : Blo 591290 889961 := bstep (se 2 (by rfl) ⟨333735, by rfl⟩ : syracuseStep 889961 = 667471) B667471
theorem B890063 : Blo 591290 890063 := bstep (se 1 (by rfl) ⟨667547, by rfl⟩ : syracuseStep 890063 = 1335095) B1335095
theorem B595151 : Blo 591290 595151 := bstep (se 1 (by rfl) ⟨446363, by rfl⟩ : syracuseStep 595151 = 892727) B892727
theorem B4265369 : Blo 591290 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B890267 : Blo 591290 890267 := bstep (se 1 (by rfl) ⟨667700, by rfl⟩ : syracuseStep 890267 = 1335401) B1335401
theorem B3216827 : Blo 591290 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B890489 : Blo 591290 890489 := bstep (se 2 (by rfl) ⟨333933, by rfl⟩ : syracuseStep 890489 = 667867) B667867
theorem B890591 : Blo 591290 890591 := bstep (se 1 (by rfl) ⟨667943, by rfl⟩ : syracuseStep 890591 = 1335887) B1335887
theorem B890687 : Blo 591290 890687 := bstep (se 1 (by rfl) ⟨668015, by rfl⟩ : syracuseStep 890687 = 1336031) B1336031
theorem B890855 : Blo 591290 890855 := bstep (se 1 (by rfl) ⟨668141, by rfl⟩ : syracuseStep 890855 = 1336283) B1336283
theorem B890873 : Blo 591290 890873 := bstep (se 2 (by rfl) ⟨334077, by rfl⟩ : syracuseStep 890873 = 668155) B668155
theorem B890975 : Blo 591290 890975 := bstep (se 1 (by rfl) ⟨668231, by rfl⟩ : syracuseStep 890975 = 1336463) B1336463
theorem B891035 : Blo 591290 891035 := bstep (se 1 (by rfl) ⟨668276, by rfl⟩ : syracuseStep 891035 = 1336553) B1336553
theorem B891071 : Blo 591290 891071 := bstep (se 1 (by rfl) ⟨668303, by rfl⟩ : syracuseStep 891071 = 1336607) B1336607
theorem B3807431 : Blo 591290 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B891113 : Blo 591290 891113 := bstep (se 2 (by rfl) ⟨334167, by rfl⟩ : syracuseStep 891113 = 668335) B668335
theorem B2005235 : Blo 591290 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B4266269 : Blo 591290 4266269 := bstep (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) B1599851
theorem B2005289 : Blo 591290 2005289 := bstep (se 2 (by rfl) ⟨751983, by rfl⟩ : syracuseStep 2005289 = 1503967) B1503967
theorem B891419 : Blo 591290 891419 := bstep (se 1 (by rfl) ⟨668564, by rfl⟩ : syracuseStep 891419 = 1337129) B1337129
theorem B891497 : Blo 591290 891497 := bstep (se 2 (by rfl) ⟨334311, by rfl⟩ : syracuseStep 891497 = 668623) B668623
theorem B2529949 : Blo 591290 2529949 := bstep (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) B948731
theorem B6855667 : Blo 591290 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B892025 : Blo 591290 892025 := bstep (se 2 (by rfl) ⟨334509, by rfl⟩ : syracuseStep 892025 = 669019) B669019
theorem B8101043 : Blo 591290 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B892127 : Blo 591290 892127 := bstep (se 1 (by rfl) ⟨669095, by rfl⟩ : syracuseStep 892127 = 1338191) B1338191
theorem B892169 : Blo 591290 892169 := bstep (se 2 (by rfl) ⟨334563, by rfl⟩ : syracuseStep 892169 = 669127) B669127
theorem B892271 : Blo 591290 892271 := bstep (se 1 (by rfl) ⟨669203, by rfl⟩ : syracuseStep 892271 = 1338407) B1338407
theorem B892391 : Blo 591290 892391 := bstep (se 1 (by rfl) ⟨669293, by rfl⟩ : syracuseStep 892391 = 1338587) B1338587
theorem B892523 : Blo 591290 892523 := bstep (se 1 (by rfl) ⟨669392, by rfl⟩ : syracuseStep 892523 = 1338785) B1338785
theorem B17079923 : Blo 591290 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B892649 : Blo 591290 892649 := bstep (se 2 (by rfl) ⟨334743, by rfl⟩ : syracuseStep 892649 = 669487) B669487
theorem B2006855 : Blo 591290 2006855 := bstep (se 1 (by rfl) ⟨1505141, by rfl⟩ : syracuseStep 2006855 = 3010283) B3010283
theorem B892793 : Blo 591290 892793 := bstep (se 2 (by rfl) ⟨334797, by rfl⟩ : syracuseStep 892793 = 669595) B669595
theorem B2006909 : Blo 591290 2006909 := bstep (se 3 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 2006909 = 752591) B752591
theorem B892895 : Blo 591290 892895 := bstep (se 1 (by rfl) ⟨669671, by rfl⟩ : syracuseStep 892895 = 1339343) B1339343
theorem B2007179 : Blo 591290 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B2007503 : Blo 591290 2007503 := bstep (se 1 (by rfl) ⟨1505627, by rfl⟩ : syracuseStep 2007503 = 3011255) B3011255
theorem B2007827 : Blo 591290 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B1123283 : Blo 591290 1123283 := bstep (se 1 (by rfl) ⟨842462, by rfl⟩ : syracuseStep 1123283 = 1684925) B1684925
theorem B1123951 : Blo 591290 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B2008691 : Blo 591290 2008691 := bstep (se 1 (by rfl) ⟨1506518, by rfl⟩ : syracuseStep 2008691 = 3013037) B3013037
theorem B1287847 : Blo 591290 1287847 := bstep (se 1 (by rfl) ⟨965885, by rfl⟩ : syracuseStep 1287847 = 1931771) B1931771
theorem B632539 : Blo 591290 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B2008799 : Blo 591290 2008799 := bstep (se 1 (by rfl) ⟨1506599, by rfl⟩ : syracuseStep 2008799 = 3013199) B3013199
theorem B2008961 : Blo 591290 2008961 := bstep (se 2 (by rfl) ⟨753360, by rfl⟩ : syracuseStep 2008961 = 1506721) B1506721
theorem B3614867 : Blo 591290 3614867 := bstep (se 1 (by rfl) ⟨2711150, by rfl⟩ : syracuseStep 3614867 = 5422301) B5422301
theorem B1124543 : Blo 591290 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B7612811 : Blo 591290 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B666139 : Blo 591290 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B6827123 : Blo 591290 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B3812761 : Blo 591290 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B667111 : Blo 591290 667111 := bstep (se 1 (by rfl) ⟨500333, by rfl⟩ : syracuseStep 667111 = 1000667) B1000667
theorem B667615 : Blo 591290 667615 := bstep (se 1 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 667615 = 1001423) B1001423
theorem B25669709 : Blo 591290 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B2535553 : Blo 591290 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B2994569 : Blo 591290 2994569 := bstep (se 2 (by rfl) ⟨1122963, by rfl⟩ : syracuseStep 2994569 = 2245927) B2245927
theorem B1421705 : Blo 591290 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B36516271 : Blo 591290 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B668263 : Blo 591290 668263 := bstep (se 1 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 668263 = 1002395) B1002395
theorem B1127209 : Blo 591290 1127209 := bstep (se 2 (by rfl) ⟨422703, by rfl⟩ : syracuseStep 1127209 = 845407) B845407
theorem B41759813 : Blo 591290 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B6599879 : Blo 591290 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B4568879 : Blo 591290 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B3618665 : Blo 591290 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B1128431 : Blo 591290 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B1685767 : Blo 591290 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B2144825 : Blo 591290 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B998075 : Blo 591290 998075 := bstep (se 1 (by rfl) ⟨748556, by rfl⟩ : syracuseStep 998075 = 1497113) B1497113
theorem B16267999 : Blo 591290 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B6831145 : Blo 591290 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B4504733 : Blo 591290 4504733 := bstep (se 3 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 4504733 = 1689275) B1689275
theorem B5422735 : Blo 591290 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B1687351 : Blo 591290 1687351 := bstep (se 1 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 1687351 = 2531027) B2531027
theorem B15417155 : Blo 591290 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B1523627 : Blo 591290 1523627 := bstep (se 1 (by rfl) ⟨1142720, by rfl⟩ : syracuseStep 1523627 = 2285441) B2285441
theorem B999391 : Blo 591290 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B4800875 : Blo 591290 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B1000039 : Blo 591290 1000039 := bstep (se 1 (by rfl) ⟨750029, by rfl⟩ : syracuseStep 1000039 = 1500059) B1500059
theorem B1000201 : Blo 591290 1000201 := bstep (se 2 (by rfl) ⟨375075, by rfl⟩ : syracuseStep 1000201 = 750151) B750151
theorem B1000795 : Blo 591290 1000795 := bstep (se 1 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 1000795 = 1501193) B1501193
theorem B8111549 : Blo 591290 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B27313685 : Blo 591290 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B1263215 : Blo 591290 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B10831745 : Blo 591290 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B3000239 : Blo 591290 3000239 := bstep (se 1 (by rfl) ⟨2250179, by rfl⟩ : syracuseStep 3000239 = 4500359) B4500359
theorem B8800435 : Blo 591290 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B1001767 : Blo 591290 1001767 := bstep (se 1 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 1001767 = 1502651) B1502651
theorem B1689913 : Blo 591290 1689913 := bstep (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) B1267435
theorem B1427807 : Blo 591290 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B1526111 : Blo 591290 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B3426961 : Blo 591290 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B22792913 : Blo 591290 22792913 := bstep (se 2 (by rfl) ⟨8547342, by rfl⟩ : syracuseStep 22792913 = 17094685) B17094685
theorem B5425879 : Blo 591290 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B8571743 : Blo 591290 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B1002719 : Blo 591290 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B6409817 : Blo 591290 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B1003151 : Blo 591290 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B1003387 : Blo 591290 1003387 := bstep (se 1 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 1003387 = 1505081) B1505081
theorem B1331099 : Blo 591290 1331099 := bstep (se 1 (by rfl) ⟨998324, by rfl⟩ : syracuseStep 1331099 = 1996649) B1996649
theorem B1691599 : Blo 591290 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B1331387 : Blo 591290 1331387 := bstep (se 1 (by rfl) ⟨998540, by rfl⟩ : syracuseStep 1331387 = 1997081) B1997081
theorem B7721249 : Blo 591290 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B1331873 : Blo 591290 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B1266683 : Blo 591290 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B1332233 : Blo 591290 1332233 := bstep (se 2 (by rfl) ⟨499587, by rfl⟩ : syracuseStep 1332233 = 999175) B999175
theorem B2413577 : Blo 591290 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1332287 : Blo 591290 1332287 := bstep (se 1 (by rfl) ⟨999215, by rfl⟩ : syracuseStep 1332287 = 1998431) B1998431
theorem B3200219 : Blo 591290 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B1333223 : Blo 591290 1333223 := bstep (se 1 (by rfl) ⟨999917, by rfl⟩ : syracuseStep 1333223 = 1999835) B1999835
theorem B1333241 : Blo 591290 1333241 := bstep (se 2 (by rfl) ⟨499965, by rfl⟩ : syracuseStep 1333241 = 999931) B999931
theorem B1333331 : Blo 591290 1333331 := bstep (se 1 (by rfl) ⟨999998, by rfl⟩ : syracuseStep 1333331 = 1999997) B1999997
theorem B1333403 : Blo 591290 1333403 := bstep (se 1 (by rfl) ⟨1000052, by rfl⟩ : syracuseStep 1333403 = 2000105) B2000105
theorem B841961 : Blo 591290 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B1333511 : Blo 591290 1333511 := bstep (se 1 (by rfl) ⟨1000133, by rfl⟩ : syracuseStep 1333511 = 2000267) B2000267
theorem B1497467 : Blo 591290 1497467 := bstep (se 1 (by rfl) ⟨1123100, by rfl⟩ : syracuseStep 1497467 = 2246201) B2246201
theorem B17160659 : Blo 591290 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B1333817 : Blo 591290 1333817 := bstep (se 2 (by rfl) ⟨500181, by rfl⟩ : syracuseStep 1333817 = 1000363) B1000363
theorem B1268563 : Blo 591290 1268563 := bstep (se 1 (by rfl) ⟨951422, by rfl⟩ : syracuseStep 1268563 = 1902845) B1902845
theorem B14474159 : Blo 591290 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B2251745 : Blo 591290 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B2841581 : Blo 591290 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B14605379 : Blo 591290 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B3005585 : Blo 591290 3005585 := bstep (se 2 (by rfl) ⟨1127094, by rfl⟩ : syracuseStep 3005585 = 2254189) B2254189
theorem B1334537 : Blo 591290 1334537 := bstep (se 2 (by rfl) ⟨500451, by rfl⟩ : syracuseStep 1334537 = 1000903) B1000903
theorem B1335527 : Blo 591290 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B2285921 : Blo 591290 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B1336121 : Blo 591290 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B1336175 : Blo 591290 1336175 := bstep (se 1 (by rfl) ⟨1002131, by rfl⟩ : syracuseStep 1336175 = 2004263) B2004263
theorem B27779993 : Blo 591290 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B4514939 : Blo 591290 4514939 := bstep (se 1 (by rfl) ⟨3386204, by rfl⟩ : syracuseStep 4514939 = 6772409) B6772409
theorem B1336751 : Blo 591290 1336751 := bstep (se 1 (by rfl) ⟨1002563, by rfl⟩ : syracuseStep 1336751 = 2005127) B2005127
theorem B3008015 : Blo 591290 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B1500839 : Blo 591290 1500839 := bstep (se 1 (by rfl) ⟨1125629, by rfl⟩ : syracuseStep 1500839 = 2251259) B2251259
theorem B2746075 : Blo 591290 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B6776783 : Blo 591290 6776783 := bstep (se 1 (by rfl) ⟨5082587, by rfl⟩ : syracuseStep 6776783 = 10165175) B10165175
theorem B3565601 : Blo 591290 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B1501375 : Blo 591290 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B1337579 : Blo 591290 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B1501487 : Blo 591290 1501487 := bstep (se 1 (by rfl) ⟨1126115, by rfl⟩ : syracuseStep 1501487 = 2252231) B2252231
theorem B2255161 : Blo 591290 2255161 := bstep (se 2 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 2255161 = 1691371) B1691371
theorem B3008825 : Blo 591290 3008825 := bstep (se 2 (by rfl) ⟨1128309, by rfl⟩ : syracuseStep 3008825 = 2256619) B2256619
theorem B748379 : Blo 591290 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B3009473 : Blo 591290 3009473 := bstep (se 2 (by rfl) ⟨1128552, by rfl⟩ : syracuseStep 3009473 = 2257105) B2257105
theorem B3370031 : Blo 591290 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B1502489 : Blo 591290 1502489 := bstep (se 2 (by rfl) ⟨563433, by rfl⟩ : syracuseStep 1502489 = 1126867) B1126867
theorem B3370349 : Blo 591290 3370349 := bstep (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) B1263881
theorem B1895849 : Blo 591290 1895849 := bstep (se 2 (by rfl) ⟨710943, by rfl⟩ : syracuseStep 1895849 = 1421887) B1421887
theorem B4615639 : Blo 591290 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B1338875 : Blo 591290 1338875 := bstep (se 1 (by rfl) ⟨1004156, by rfl⟩ : syracuseStep 1338875 = 2008313) B2008313
theorem B30797333 : Blo 591290 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B1502783 : Blo 591290 1502783 := bstep (se 1 (by rfl) ⟨1127087, by rfl⟩ : syracuseStep 1502783 = 2254175) B2254175
theorem B3010121 : Blo 591290 3010121 := bstep (se 2 (by rfl) ⟨1128795, by rfl⟩ : syracuseStep 3010121 = 2257591) B2257591
theorem B1339055 : Blo 591290 1339055 := bstep (se 1 (by rfl) ⟨1004291, by rfl⟩ : syracuseStep 1339055 = 2008583) B2008583
theorem B1502995 : Blo 591290 1502995 := bstep (se 1 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 1502995 = 2254493) B2254493
theorem B749351 : Blo 591290 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B1896335 : Blo 591290 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B3371489 : Blo 591290 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B1143391 : Blo 591290 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B1504129 : Blo 591290 1504129 := bstep (se 2 (by rfl) ⟨564048, by rfl⟩ : syracuseStep 1504129 = 1128097) B1128097
theorem B1995785 : Blo 591290 1995785 := bstep (se 2 (by rfl) ⟨748419, by rfl⟩ : syracuseStep 1995785 = 1496839) B1496839
theorem B750647 : Blo 591290 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B1995839 : Blo 591290 1995839 := bstep (se 1 (by rfl) ⟨1496879, by rfl⟩ : syracuseStep 1995839 = 2993759) B2993759
theorem B750799 : Blo 591290 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B1504939 : Blo 591290 1504939 := bstep (se 1 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 1504939 = 2257409) B2257409
theorem B7730923 : Blo 591290 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B2029369 : Blo 591290 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B1505243 : Blo 591290 1505243 := bstep (se 1 (by rfl) ⟨1128932, by rfl⟩ : syracuseStep 1505243 = 2257865) B2257865
theorem B1505263 : Blo 591290 1505263 := bstep (se 1 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 1505263 = 2257895) B2257895
theorem B3864635 : Blo 591290 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B1898579 : Blo 591290 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B1505375 : Blo 591290 1505375 := bstep (se 1 (by rfl) ⟨1129031, by rfl⟩ : syracuseStep 1505375 = 2258063) B2258063
theorem B3209321 : Blo 591290 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B2259049 : Blo 591290 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B3012713 : Blo 591290 3012713 := bstep (se 2 (by rfl) ⟨1129767, by rfl⟩ : syracuseStep 3012713 = 2259535) B2259535
theorem B751771 : Blo 591290 751771 := bstep (se 1 (by rfl) ⟨563828, by rfl⟩ : syracuseStep 751771 = 1127657) B1127657
theorem B1898795 : Blo 591290 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B1800841 : Blo 591290 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B3373721 : Blo 591290 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B3603365 : Blo 591290 3603365 := bstep (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) B675631
theorem B1899769 : Blo 591290 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B1506671 : Blo 591290 1506671 := bstep (se 1 (by rfl) ⟨1130003, by rfl⟩ : syracuseStep 1506671 = 2260007) B2260007
theorem B1900219 : Blo 591290 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B1081127 : Blo 591290 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B1998647 : Blo 591290 1998647 := bstep (se 1 (by rfl) ⟨1498985, by rfl⟩ : syracuseStep 1998647 = 2997971) B2997971
theorem B3374905 : Blo 591290 3374905 := bstep (se 2 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 3374905 = 2531179) B2531179
theorem B2000159 : Blo 591290 2000159 := bstep (se 1 (by rfl) ⟨1500119, by rfl⟩ : syracuseStep 2000159 = 3000239) B3000239
theorem B591387 : Blo 591290 591387 := bstep (se 1 (by rfl) ⟨443540, by rfl⟩ : syracuseStep 591387 = 887081) B887081
theorem B591391 : Blo 591290 591391 := bstep (se 1 (by rfl) ⟨443543, by rfl⟩ : syracuseStep 591391 = 887087) B887087
theorem B1017407 : Blo 591290 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B591551 : Blo 591290 591551 := bstep (se 1 (by rfl) ⟨443663, by rfl⟩ : syracuseStep 591551 = 887327) B887327
theorem B591807 : Blo 591290 591807 := bstep (se 1 (by rfl) ⟨443855, by rfl⟩ : syracuseStep 591807 = 887711) B887711
theorem B591839 : Blo 591290 591839 := bstep (se 1 (by rfl) ⟨443879, by rfl⟩ : syracuseStep 591839 = 887759) B887759
theorem B591899 : Blo 591290 591899 := bstep (se 1 (by rfl) ⟨443924, by rfl⟩ : syracuseStep 591899 = 887849) B887849
theorem B591903 : Blo 591290 591903 := bstep (se 1 (by rfl) ⟨443927, by rfl⟩ : syracuseStep 591903 = 887855) B887855
theorem B591919 : Blo 591290 591919 := bstep (se 1 (by rfl) ⟨443939, by rfl⟩ : syracuseStep 591919 = 887879) B887879
theorem B592095 : Blo 591290 592095 := bstep (se 1 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 592095 = 888143) B888143
theorem B592155 : Blo 591290 592155 := bstep (se 1 (by rfl) ⟨444116, by rfl⟩ : syracuseStep 592155 = 888233) B888233
theorem B11536673 : Blo 591290 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B592255 : Blo 591290 592255 := bstep (se 1 (by rfl) ⟨444191, by rfl⟩ : syracuseStep 592255 = 888383) B888383
theorem B592431 : Blo 591290 592431 := bstep (se 1 (by rfl) ⟨444323, by rfl⟩ : syracuseStep 592431 = 888647) B888647
theorem B887399 : Blo 591290 887399 := bstep (se 1 (by rfl) ⟨665549, by rfl⟩ : syracuseStep 887399 = 1331099) B1331099
theorem B592487 : Blo 591290 592487 := bstep (se 1 (by rfl) ⟨444365, by rfl⟩ : syracuseStep 592487 = 888731) B888731
theorem B3377821 : Blo 591290 3377821 := bstep (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) B1266683
theorem B887591 : Blo 591290 887591 := bstep (se 1 (by rfl) ⟨665693, by rfl⟩ : syracuseStep 887591 = 1331387) B1331387
theorem B2001725 : Blo 591290 2001725 := bstep (se 3 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 2001725 = 750647) B750647
theorem B11733913 : Blo 591290 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B2001833 : Blo 591290 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B592863 : Blo 591290 592863 := bstep (se 1 (by rfl) ⟨444647, by rfl⟩ : syracuseStep 592863 = 889295) B889295
theorem B592891 : Blo 591290 592891 := bstep (se 1 (by rfl) ⟨444668, by rfl⟩ : syracuseStep 592891 = 889337) B889337
theorem B1444873 : Blo 591290 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B592959 : Blo 591290 592959 := bstep (se 1 (by rfl) ⟨444719, by rfl⟩ : syracuseStep 592959 = 889439) B889439
theorem B887915 : Blo 591290 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B888155 : Blo 591290 888155 := bstep (se 1 (by rfl) ⟨666116, by rfl⟩ : syracuseStep 888155 = 1332233) B1332233
theorem B888185 : Blo 591290 888185 := bstep (se 2 (by rfl) ⟨333069, by rfl⟩ : syracuseStep 888185 = 666139) B666139
theorem B888191 : Blo 591290 888191 := bstep (se 1 (by rfl) ⟨666143, by rfl⟩ : syracuseStep 888191 = 1332287) B1332287
theorem B593279 : Blo 591290 593279 := bstep (se 1 (by rfl) ⟨444959, by rfl⟩ : syracuseStep 593279 = 889919) B889919
theorem B593307 : Blo 591290 593307 := bstep (se 1 (by rfl) ⟨444980, by rfl⟩ : syracuseStep 593307 = 889961) B889961
theorem B593375 : Blo 591290 593375 := bstep (se 1 (by rfl) ⟨445031, by rfl⟩ : syracuseStep 593375 = 890063) B890063
theorem B2133479 : Blo 591290 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B593511 : Blo 591290 593511 := bstep (se 1 (by rfl) ⟨445133, by rfl⟩ : syracuseStep 593511 = 890267) B890267
theorem B593659 : Blo 591290 593659 := bstep (se 1 (by rfl) ⟨445244, by rfl⟩ : syracuseStep 593659 = 890489) B890489
theorem B593727 : Blo 591290 593727 := bstep (se 1 (by rfl) ⟨445295, by rfl⟩ : syracuseStep 593727 = 890591) B890591
theorem B21630797 : Blo 591290 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B593791 : Blo 591290 593791 := bstep (se 1 (by rfl) ⟨445343, by rfl⟩ : syracuseStep 593791 = 890687) B890687
theorem B888815 : Blo 591290 888815 := bstep (se 1 (by rfl) ⟨666611, by rfl⟩ : syracuseStep 888815 = 1333223) B1333223
theorem B593903 : Blo 591290 593903 := bstep (se 1 (by rfl) ⟨445427, by rfl⟩ : syracuseStep 593903 = 890855) B890855
theorem B888827 : Blo 591290 888827 := bstep (se 1 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 888827 = 1333241) B1333241
theorem B593915 : Blo 591290 593915 := bstep (se 1 (by rfl) ⟨445436, by rfl⟩ : syracuseStep 593915 = 890873) B890873
theorem B888887 : Blo 591290 888887 := bstep (se 1 (by rfl) ⟨666665, by rfl⟩ : syracuseStep 888887 = 1333331) B1333331
theorem B593983 : Blo 591290 593983 := bstep (se 1 (by rfl) ⟨445487, by rfl⟩ : syracuseStep 593983 = 890975) B890975
theorem B888935 : Blo 591290 888935 := bstep (se 1 (by rfl) ⟨666701, by rfl⟩ : syracuseStep 888935 = 1333403) B1333403
theorem B594023 : Blo 591290 594023 := bstep (se 1 (by rfl) ⟨445517, by rfl⟩ : syracuseStep 594023 = 891035) B891035
theorem B594047 : Blo 591290 594047 := bstep (se 1 (by rfl) ⟨445535, by rfl⟩ : syracuseStep 594047 = 891071) B891071
theorem B594075 : Blo 591290 594075 := bstep (se 1 (by rfl) ⟨445556, by rfl⟩ : syracuseStep 594075 = 891113) B891113
theorem B889007 : Blo 591290 889007 := bstep (se 1 (by rfl) ⟨666755, by rfl⟩ : syracuseStep 889007 = 1333511) B1333511
theorem B11440439 : Blo 591290 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B594279 : Blo 591290 594279 := bstep (se 1 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 594279 = 891419) B891419
theorem B889211 : Blo 591290 889211 := bstep (se 1 (by rfl) ⟨666908, by rfl⟩ : syracuseStep 889211 = 1333817) B1333817
theorem B594331 : Blo 591290 594331 := bstep (se 1 (by rfl) ⟨445748, by rfl⟩ : syracuseStep 594331 = 891497) B891497
theorem B5083681 : Blo 591290 5083681 := bstep (se 2 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 5083681 = 3812761) B3812761
theorem B889481 : Blo 591290 889481 := bstep (se 2 (by rfl) ⟨333555, by rfl⟩ : syracuseStep 889481 = 667111) B667111
theorem B9736919 : Blo 591290 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B594683 : Blo 591290 594683 := bstep (se 1 (by rfl) ⟨446012, by rfl⟩ : syracuseStep 594683 = 892025) B892025
theorem B2003723 : Blo 591290 2003723 := bstep (se 1 (by rfl) ⟨1502792, by rfl⟩ : syracuseStep 2003723 = 3005585) B3005585
theorem B594751 : Blo 591290 594751 := bstep (se 1 (by rfl) ⟨446063, by rfl⟩ : syracuseStep 594751 = 892127) B892127
theorem B889691 : Blo 591290 889691 := bstep (se 1 (by rfl) ⟨667268, by rfl⟩ : syracuseStep 889691 = 1334537) B1334537
theorem B594779 : Blo 591290 594779 := bstep (se 1 (by rfl) ⟨446084, by rfl⟩ : syracuseStep 594779 = 892169) B892169
theorem B594847 : Blo 591290 594847 := bstep (se 1 (by rfl) ⟨446135, by rfl⟩ : syracuseStep 594847 = 892271) B892271
theorem B594927 : Blo 591290 594927 := bstep (se 1 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 594927 = 892391) B892391
theorem B2003993 : Blo 591290 2003993 := bstep (se 2 (by rfl) ⟨751497, by rfl⟩ : syracuseStep 2003993 = 1502995) B1502995
theorem B595015 : Blo 591290 595015 := bstep (se 1 (by rfl) ⟨446261, by rfl⟩ : syracuseStep 595015 = 892523) B892523
theorem B595099 : Blo 591290 595099 := bstep (se 1 (by rfl) ⟨446324, by rfl⟩ : syracuseStep 595099 = 892649) B892649
theorem B595195 : Blo 591290 595195 := bstep (se 1 (by rfl) ⟨446396, by rfl⟩ : syracuseStep 595195 = 892793) B892793
theorem B890153 : Blo 591290 890153 := bstep (se 2 (by rfl) ⟨333807, by rfl⟩ : syracuseStep 890153 = 667615) B667615
theorem B595263 : Blo 591290 595263 := bstep (se 1 (by rfl) ⟨446447, by rfl⟩ : syracuseStep 595263 = 892895) B892895
theorem B890351 : Blo 591290 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B3380737 : Blo 591290 3380737 := bstep (se 2 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 3380737 = 2535553) B2535553
theorem B890747 : Blo 591290 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B890783 : Blo 591290 890783 := bstep (se 1 (by rfl) ⟨668087, by rfl⟩ : syracuseStep 890783 = 1336175) B1336175
theorem B18519995 : Blo 591290 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B891017 : Blo 591290 891017 := bstep (se 2 (by rfl) ⟨334131, by rfl⟩ : syracuseStep 891017 = 668263) B668263
theorem B3807485 : Blo 591290 3807485 := bstep (se 3 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 3807485 = 1427807) B1427807
theorem B891167 : Blo 591290 891167 := bstep (se 1 (by rfl) ⟨668375, by rfl⟩ : syracuseStep 891167 = 1336751) B1336751
theorem B2005343 : Blo 591290 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B7707125 : Blo 591290 7707125 := bstep (se 5 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 7707125 = 722543) B722543
theorem B2005505 : Blo 591290 2005505 := bstep (se 2 (by rfl) ⟨752064, by rfl⟩ : syracuseStep 2005505 = 1504129) B1504129
theorem B891719 : Blo 591290 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B2005883 : Blo 591290 2005883 := bstep (se 1 (by rfl) ⟨1504412, by rfl⟩ : syracuseStep 2005883 = 3008825) B3008825
theorem B2006315 : Blo 591290 2006315 := bstep (se 1 (by rfl) ⟨1504736, by rfl⟩ : syracuseStep 2006315 = 3009473) B3009473
theorem B2006585 : Blo 591290 2006585 := bstep (se 2 (by rfl) ⟨752469, by rfl⟩ : syracuseStep 2006585 = 1504939) B1504939
theorem B892583 : Blo 591290 892583 := bstep (se 1 (by rfl) ⟨669437, by rfl⟩ : syracuseStep 892583 = 1338875) B1338875
theorem B2006747 : Blo 591290 2006747 := bstep (se 1 (by rfl) ⟨1505060, by rfl⟩ : syracuseStep 2006747 = 3010121) B3010121
theorem B892703 : Blo 591290 892703 := bstep (se 1 (by rfl) ⟨669527, by rfl⟩ : syracuseStep 892703 = 1339055) B1339055
theorem B2007017 : Blo 591290 2007017 := bstep (se 2 (by rfl) ⟨752631, by rfl⟩ : syracuseStep 2007017 = 1505263) B1505263
theorem B17113139 : Blo 591290 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B4399919 : Blo 591290 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B2401121 : Blo 591290 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B2139547 : Blo 591290 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B2008475 : Blo 591290 2008475 := bstep (se 1 (by rfl) ⟨1506356, by rfl⟩ : syracuseStep 2008475 = 3012713) B3012713
theorem B2533025 : Blo 591290 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B665383 : Blo 591290 665383 := bstep (se 1 (by rfl) ⟨499037, by rfl⟩ : syracuseStep 665383 = 998075) B998075
theorem B2402243 : Blo 591290 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B2533625 : Blo 591290 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B4499873 : Blo 591290 4499873 := bstep (se 2 (by rfl) ⟨1687452, by rfl⟩ : syracuseStep 4499873 = 3374905) B3374905
theorem B2534665 : Blo 591290 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B20589997 : Blo 591290 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B7221163 : Blo 591290 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B2994407 : Blo 591290 2994407 := bstep (se 1 (by rfl) ⟨2245805, by rfl⟩ : syracuseStep 2994407 = 4491611) B4491611
theorem B5714495 : Blo 591290 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B2404979 : Blo 591290 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B668479 : Blo 591290 668479 := bstep (se 1 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 668479 = 1002719) B1002719
theorem B1717129 : Blo 591290 1717129 := bstep (se 2 (by rfl) ⟨643923, by rfl⟩ : syracuseStep 1717129 = 1287847) B1287847
theorem B1684435 : Blo 591290 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B4273211 : Blo 591290 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B668767 : Blo 591290 668767 := bstep (se 1 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 668767 = 1003151) B1003151
theorem B6436205 : Blo 591290 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B4569281 : Blo 591290 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B2144551 : Blo 591290 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B2538287 : Blo 591290 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B998311 : Blo 591290 998311 := bstep (se 1 (by rfl) ⟨748733, by rfl⟩ : syracuseStep 998311 = 1497467) B1497467
theorem B9649439 : Blo 591290 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B11386615 : Blo 591290 11386615 := bstep (se 1 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 11386615 = 17079923) B17079923
theorem B1523947 : Blo 591290 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B2998781 : Blo 591290 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B2245229 : Blo 591290 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B1524521 : Blo 591290 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B1000559 : Blo 591290 1000559 := bstep (se 1 (by rfl) ⟨750419, by rfl⟩ : syracuseStep 1000559 = 1500839) B1500839
theorem B2377067 : Blo 591290 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B2409911 : Blo 591290 2409911 := bstep (se 1 (by rfl) ⟨1807433, by rfl⟩ : syracuseStep 2409911 = 3614867) B3614867
theorem B1000991 : Blo 591290 1000991 := bstep (se 1 (by rfl) ⟨750743, by rfl⟩ : syracuseStep 1000991 = 1501487) B1501487
theorem B1001065 : Blo 591290 1001065 := bstep (se 2 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 1001065 = 750799) B750799
theorem B2246687 : Blo 591290 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B1001659 : Blo 591290 1001659 := bstep (se 1 (by rfl) ⟨751244, by rfl⟩ : syracuseStep 1001659 = 1502489) B1502489
theorem B2246899 : Blo 591290 2246899 := bstep (se 1 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 2246899 = 3370349) B3370349
theorem B1263899 : Blo 591290 1263899 := bstep (se 1 (by rfl) ⟨947924, by rfl⟩ : syracuseStep 1263899 = 1895849) B1895849
theorem B10307897 : Blo 591290 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B20531555 : Blo 591290 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B1001855 : Blo 591290 1001855 := bstep (se 1 (by rfl) ⟨751391, by rfl⟩ : syracuseStep 1001855 = 1502783) B1502783
theorem B2705825 : Blo 591290 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B1264223 : Blo 591290 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B1002361 : Blo 591290 1002361 := bstep (se 2 (by rfl) ⟨375885, by rfl⟩ : syracuseStep 1002361 = 751771) B751771
theorem B18205661 : Blo 591290 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B2247659 : Blo 591290 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B2247689 : Blo 591290 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B1330523 : Blo 591290 1330523 := bstep (se 1 (by rfl) ⟨997892, by rfl⟩ : syracuseStep 1330523 = 1995785) B1995785
theorem B1330559 : Blo 591290 1330559 := bstep (se 1 (by rfl) ⟨997919, by rfl⟩ : syracuseStep 1330559 = 1995839) B1995839
theorem B27839875 : Blo 591290 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B1691417 : Blo 591290 1691417 := bstep (se 2 (by rfl) ⟨634281, by rfl⟩ : syracuseStep 1691417 = 1268563) B1268563
theorem B2412443 : Blo 591290 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B1003495 : Blo 591290 1003495 := bstep (se 1 (by rfl) ⟨752621, by rfl⟩ : syracuseStep 1003495 = 1505243) B1505243
theorem B2576423 : Blo 591290 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B1265719 : Blo 591290 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B1003583 : Blo 591290 1003583 := bstep (se 1 (by rfl) ⟨752687, by rfl⟩ : syracuseStep 1003583 = 1505375) B1505375
theorem B1265863 : Blo 591290 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1429883 : Blo 591290 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B2249147 : Blo 591290 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B3003155 : Blo 591290 3003155 := bstep (se 1 (by rfl) ⟨2252366, by rfl⟩ : syracuseStep 3003155 = 4504733) B4504733
theorem B7230313 : Blo 591290 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B1004447 : Blo 591290 1004447 := bstep (se 1 (by rfl) ⟨753335, by rfl⟩ : syracuseStep 1004447 = 1506671) B1506671
theorem B2249801 : Blo 591290 2249801 := bstep (se 2 (by rfl) ⟨843675, by rfl⟩ : syracuseStep 2249801 = 1687351) B1687351
theorem B1332431 : Blo 591290 1332431 := bstep (se 1 (by rfl) ⟨999323, by rfl⟩ : syracuseStep 1332431 = 1998647) B1998647
theorem B10278103 : Blo 591290 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B1332521 : Blo 591290 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B1332719 : Blo 591290 1332719 := bstep (se 1 (by rfl) ⟨999539, by rfl⟩ : syracuseStep 1332719 = 1999079) B1999079
theorem B1333115 : Blo 591290 1333115 := bstep (se 1 (by rfl) ⟨999836, by rfl⟩ : syracuseStep 1333115 = 1999673) B1999673
theorem B1333151 : Blo 591290 1333151 := bstep (se 1 (by rfl) ⟨999863, by rfl⟩ : syracuseStep 1333151 = 1999727) B1999727
theorem B1333385 : Blo 591290 1333385 := bstep (se 2 (by rfl) ⟨500019, by rfl⟩ : syracuseStep 1333385 = 1000039) B1000039
theorem B12802333 : Blo 591290 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B2251091 : Blo 591290 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B1333601 : Blo 591290 1333601 := bstep (se 2 (by rfl) ⟨500100, by rfl⟩ : syracuseStep 1333601 = 1000201) B1000201
theorem B18209123 : Blo 591290 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B1333691 : Blo 591290 1333691 := bstep (se 1 (by rfl) ⟨1000268, by rfl⟩ : syracuseStep 1333691 = 2000537) B2000537
theorem B5397191 : Blo 591290 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B20798209 : Blo 591290 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B1334087 : Blo 591290 1334087 := bstep (se 1 (by rfl) ⟨1000565, by rfl⟩ : syracuseStep 1334087 = 2001131) B2001131
theorem B1334393 : Blo 591290 1334393 := bstep (se 2 (by rfl) ⟨500397, by rfl⟩ : syracuseStep 1334393 = 1000795) B1000795
theorem B15195275 : Blo 591290 15195275 := bstep (se 1 (by rfl) ⟨11396456, by rfl⟩ : syracuseStep 15195275 = 22792913) B22792913
theorem B1498601 : Blo 591290 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B843385 : Blo 591290 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B3661433 : Blo 591290 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B1334951 : Blo 591290 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B1335059 : Blo 591290 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B1269751 : Blo 591290 1269751 := bstep (se 1 (by rfl) ⟨952313, by rfl⟩ : syracuseStep 1269751 = 1904627) B1904627
theorem B1335419 : Blo 591290 1335419 := bstep (se 1 (by rfl) ⟨1001564, by rfl⟩ : syracuseStep 1335419 = 2003129) B2003129
theorem B1335689 : Blo 591290 1335689 := bstep (se 2 (by rfl) ⟨500883, by rfl⟩ : syracuseStep 1335689 = 1001767) B1001767
theorem B2253217 : Blo 591290 2253217 := bstep (se 2 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 2253217 = 1689913) B1689913
theorem B3006881 : Blo 591290 3006881 := bstep (se 2 (by rfl) ⟨1127580, by rfl⟩ : syracuseStep 3006881 = 2255161) B2255161
theorem B2843579 : Blo 591290 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B7234505 : Blo 591290 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B1336823 : Blo 591290 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B2844179 : Blo 591290 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B1336859 : Blo 591290 1336859 := bstep (se 1 (by rfl) ⟨1002644, by rfl⟩ : syracuseStep 1336859 = 2005289) B2005289
theorem B3368573 : Blo 591290 3368573 := bstep (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) B1263215
theorem B1501163 : Blo 591290 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1894387 : Blo 591290 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B5400695 : Blo 591290 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B1141241 : Blo 591290 1141241 := bstep (se 2 (by rfl) ⟨427965, by rfl⟩ : syracuseStep 1141241 = 855931) B855931
theorem B1337849 : Blo 591290 1337849 := bstep (se 2 (by rfl) ⟨501693, by rfl⟩ : syracuseStep 1337849 = 1003387) B1003387
theorem B1337903 : Blo 591290 1337903 := bstep (se 1 (by rfl) ⟨1003427, by rfl⟩ : syracuseStep 1337903 = 2006855) B2006855
theorem B1337939 : Blo 591290 1337939 := bstep (se 1 (by rfl) ⟨1003454, by rfl⟩ : syracuseStep 1337939 = 2006909) B2006909
theorem B36563557 : Blo 591290 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B2255465 : Blo 591290 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B3009149 : Blo 591290 3009149 := bstep (se 3 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 3009149 = 1128431) B1128431
theorem B1338119 : Blo 591290 1338119 := bstep (se 1 (by rfl) ⟨1003589, by rfl⟩ : syracuseStep 1338119 = 2007179) B2007179
theorem B36432773 : Blo 591290 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B1338335 : Blo 591290 1338335 := bstep (se 1 (by rfl) ⟨1003751, by rfl⟩ : syracuseStep 1338335 = 2007503) B2007503
theorem B1338551 : Blo 591290 1338551 := bstep (se 1 (by rfl) ⟨1003913, by rfl⟩ : syracuseStep 1338551 = 2007827) B2007827
theorem B48688361 : Blo 591290 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B748855 : Blo 591290 748855 := bstep (se 1 (by rfl) ⟨561641, by rfl⟩ : syracuseStep 748855 = 1123283) B1123283
theorem B3009959 : Blo 591290 3009959 := bstep (se 1 (by rfl) ⟨2257469, by rfl⟩ : syracuseStep 3009959 = 4514939) B4514939
theorem B1502945 : Blo 591290 1502945 := bstep (se 2 (by rfl) ⟨563604, by rfl⟩ : syracuseStep 1502945 = 1127209) B1127209
theorem B1339127 : Blo 591290 1339127 := bstep (se 1 (by rfl) ⟨1004345, by rfl⟩ : syracuseStep 1339127 = 2008691) B2008691
theorem B1339199 : Blo 591290 1339199 := bstep (se 1 (by rfl) ⟨1004399, by rfl⟩ : syracuseStep 1339199 = 2008799) B2008799
theorem B1339307 : Blo 591290 1339307 := bstep (se 1 (by rfl) ⟨1004480, by rfl⟩ : syracuseStep 1339307 = 2008961) B2008961
theorem B4517855 : Blo 591290 4517855 := bstep (se 1 (by rfl) ⟨3388391, by rfl⟩ : syracuseStep 4517855 = 6776783) B6776783
theorem B5075207 : Blo 591290 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B1995677 : Blo 591290 1995677 := bstep (se 3 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 1995677 = 748379) B748379
theorem B3012065 : Blo 591290 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B1996379 : Blo 591290 1996379 := bstep (se 1 (by rfl) ⟨1497284, by rfl⟩ : syracuseStep 1996379 = 2994569) B2994569
theorem B947803 : Blo 591290 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B7698341 : Blo 591290 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B3373265 : Blo 591290 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B21690665 : Blo 591290 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B3045919 : Blo 591290 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B98466965 : Blo 591290 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B1998269 : Blo 591290 1998269 := bstep (se 3 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 1998269 = 749351) B749351
theorem B720751 : Blo 591290 720751 := bstep (se 1 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 720751 = 1081127) B1081127
theorem B1015751 : Blo 591290 1015751 := bstep (se 1 (by rfl) ⟨761813, by rfl⟩ : syracuseStep 1015751 = 1523627) B1523627
theorem B2031929 : Blo 591290 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B1999187 : Blo 591290 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B1606607 : Blo 591290 1606607 := bstep (se 1 (by rfl) ⟨1204955, by rfl⟩ : syracuseStep 1606607 = 2409911) B2409911
theorem B1803883 : Blo 591290 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B591599 : Blo 591290 591599 := bstep (se 1 (by rfl) ⟨443699, by rfl⟩ : syracuseStep 591599 = 887399) B887399
theorem B591727 : Blo 591290 591727 := bstep (se 1 (by rfl) ⟨443795, by rfl⟩ : syracuseStep 591727 = 887591) B887591
theorem B2852729 : Blo 591290 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B591943 : Blo 591290 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B4065389 : Blo 591290 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B887015 : Blo 591290 887015 := bstep (se 1 (by rfl) ⟨665261, by rfl⟩ : syracuseStep 887015 = 1330523) B1330523
theorem B592103 : Blo 591290 592103 := bstep (se 1 (by rfl) ⟨444077, by rfl⟩ : syracuseStep 592103 = 888155) B888155
theorem B592123 : Blo 591290 592123 := bstep (se 1 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 592123 = 888185) B888185
theorem B887039 : Blo 591290 887039 := bstep (se 1 (by rfl) ⟨665279, by rfl⟩ : syracuseStep 887039 = 1330559) B1330559
theorem B592127 : Blo 591290 592127 := bstep (se 1 (by rfl) ⟨444095, by rfl⟩ : syracuseStep 592127 = 888191) B888191
theorem B887177 : Blo 591290 887177 := bstep (se 2 (by rfl) ⟨332691, by rfl⟩ : syracuseStep 887177 = 665383) B665383
theorem B14420531 : Blo 591290 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B1608295 : Blo 591290 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B2525849 : Blo 591290 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B592543 : Blo 591290 592543 := bstep (se 1 (by rfl) ⟨444407, by rfl⟩ : syracuseStep 592543 = 888815) B888815
theorem B592551 : Blo 591290 592551 := bstep (se 1 (by rfl) ⟨444413, by rfl⟩ : syracuseStep 592551 = 888827) B888827
theorem B592591 : Blo 591290 592591 := bstep (se 1 (by rfl) ⟨444443, by rfl⟩ : syracuseStep 592591 = 888887) B888887
theorem B592623 : Blo 591290 592623 := bstep (se 1 (by rfl) ⟨444467, by rfl⟩ : syracuseStep 592623 = 888935) B888935
theorem B592671 : Blo 591290 592671 := bstep (se 1 (by rfl) ⟨444503, by rfl⟩ : syracuseStep 592671 = 889007) B889007
theorem B592807 : Blo 591290 592807 := bstep (se 1 (by rfl) ⟨444605, by rfl⟩ : syracuseStep 592807 = 889211) B889211
theorem B953255 : Blo 591290 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B592987 : Blo 591290 592987 := bstep (se 1 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 592987 = 889481) B889481
theorem B6491279 : Blo 591290 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B2002103 : Blo 591290 2002103 := bstep (se 1 (by rfl) ⟨1501577, by rfl⟩ : syracuseStep 2002103 = 3003155) B3003155
theorem B593127 : Blo 591290 593127 := bstep (se 1 (by rfl) ⟨444845, by rfl⟩ : syracuseStep 593127 = 889691) B889691
theorem B888287 : Blo 591290 888287 := bstep (se 1 (by rfl) ⟨666215, by rfl⟩ : syracuseStep 888287 = 1332431) B1332431
theorem B888347 : Blo 591290 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B593435 : Blo 591290 593435 := bstep (se 1 (by rfl) ⟨445076, by rfl⟩ : syracuseStep 593435 = 890153) B890153
theorem B888479 : Blo 591290 888479 := bstep (se 1 (by rfl) ⟨666359, by rfl⟩ : syracuseStep 888479 = 1332719) B1332719
theorem B593567 : Blo 591290 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B888743 : Blo 591290 888743 := bstep (se 1 (by rfl) ⟨666557, by rfl⟩ : syracuseStep 888743 = 1333115) B1333115
theorem B593831 : Blo 591290 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B888767 : Blo 591290 888767 := bstep (se 1 (by rfl) ⟨666575, by rfl⟩ : syracuseStep 888767 = 1333151) B1333151
theorem B593855 : Blo 591290 593855 := bstep (se 1 (by rfl) ⟨445391, by rfl⟩ : syracuseStep 593855 = 890783) B890783
theorem B888923 : Blo 591290 888923 := bstep (se 1 (by rfl) ⟨666692, by rfl⟩ : syracuseStep 888923 = 1333385) B1333385
theorem B594011 : Blo 591290 594011 := bstep (se 1 (by rfl) ⟨445508, by rfl⟩ : syracuseStep 594011 = 891017) B891017
theorem B594111 : Blo 591290 594111 := bstep (se 1 (by rfl) ⟨445583, by rfl⟩ : syracuseStep 594111 = 891167) B891167
theorem B889067 : Blo 591290 889067 := bstep (se 1 (by rfl) ⟨666800, by rfl⟩ : syracuseStep 889067 = 1333601) B1333601
theorem B889127 : Blo 591290 889127 := bstep (se 1 (by rfl) ⟨666845, by rfl⟩ : syracuseStep 889127 = 1333691) B1333691
theorem B3379553 : Blo 591290 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B889391 : Blo 591290 889391 := bstep (se 1 (by rfl) ⟨667043, by rfl⟩ : syracuseStep 889391 = 1334087) B1334087
theorem B594479 : Blo 591290 594479 := bstep (se 1 (by rfl) ⟨445859, by rfl⟩ : syracuseStep 594479 = 891719) B891719
theorem B889595 : Blo 591290 889595 := bstep (se 1 (by rfl) ⟨667196, by rfl⟩ : syracuseStep 889595 = 1334393) B1334393
theorem B10130183 : Blo 591290 10130183 := bstep (se 1 (by rfl) ⟨7597637, by rfl⟩ : syracuseStep 10130183 = 15195275) B15195275
theorem B889967 : Blo 591290 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B595055 : Blo 591290 595055 := bstep (se 1 (by rfl) ⟨446291, by rfl⟩ : syracuseStep 595055 = 892583) B892583
theorem B890039 : Blo 591290 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B595135 : Blo 591290 595135 := bstep (se 1 (by rfl) ⟨446351, by rfl⟩ : syracuseStep 595135 = 892703) B892703
theorem B11408759 : Blo 591290 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B890279 : Blo 591290 890279 := bstep (se 1 (by rfl) ⟨667709, by rfl⟩ : syracuseStep 890279 = 1335419) B1335419
theorem B890459 : Blo 591290 890459 := bstep (se 1 (by rfl) ⟨667844, by rfl⟩ : syracuseStep 890459 = 1335689) B1335689
theorem B2004587 : Blo 591290 2004587 := bstep (se 1 (by rfl) ⟨1503440, by rfl⟩ : syracuseStep 2004587 = 3006881) B3006881
theorem B4823003 : Blo 591290 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B891215 : Blo 591290 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B891239 : Blo 591290 891239 := bstep (se 1 (by rfl) ⟨668429, by rfl⟩ : syracuseStep 891239 = 1336859) B1336859
theorem B891305 : Blo 591290 891305 := bstep (se 2 (by rfl) ⟨334239, by rfl⟩ : syracuseStep 891305 = 668479) B668479
theorem B9640417 : Blo 591290 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B891689 : Blo 591290 891689 := bstep (se 2 (by rfl) ⟨334383, by rfl⟩ : syracuseStep 891689 = 668767) B668767
theorem B13704137 : Blo 591290 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B891899 : Blo 591290 891899 := bstep (se 1 (by rfl) ⟨668924, by rfl⟩ : syracuseStep 891899 = 1337849) B1337849
theorem B891935 : Blo 591290 891935 := bstep (se 1 (by rfl) ⟨668951, by rfl⟩ : syracuseStep 891935 = 1337903) B1337903
theorem B891959 : Blo 591290 891959 := bstep (se 1 (by rfl) ⟨668969, by rfl⟩ : syracuseStep 891959 = 1337939) B1337939
theorem B2006099 : Blo 591290 2006099 := bstep (se 1 (by rfl) ⟨1504574, by rfl⟩ : syracuseStep 2006099 = 3009149) B3009149
theorem B892079 : Blo 591290 892079 := bstep (se 1 (by rfl) ⟨669059, by rfl⟩ : syracuseStep 892079 = 1338119) B1338119
theorem B24288515 : Blo 591290 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B892223 : Blo 591290 892223 := bstep (se 1 (by rfl) ⟨669167, by rfl⟩ : syracuseStep 892223 = 1338335) B1338335
theorem B892367 : Blo 591290 892367 := bstep (se 1 (by rfl) ⟨669275, by rfl⟩ : syracuseStep 892367 = 1338551) B1338551
theorem B2006639 : Blo 591290 2006639 := bstep (se 1 (by rfl) ⟨1504979, by rfl⟩ : syracuseStep 2006639 = 3009959) B3009959
theorem B892751 : Blo 591290 892751 := bstep (se 1 (by rfl) ⟨669563, by rfl⟩ : syracuseStep 892751 = 1339127) B1339127
theorem B892799 : Blo 591290 892799 := bstep (se 1 (by rfl) ⟨669599, by rfl⟩ : syracuseStep 892799 = 1339199) B1339199
theorem B892871 : Blo 591290 892871 := bstep (se 1 (by rfl) ⟨669653, by rfl⟩ : syracuseStep 892871 = 1339307) B1339307
theorem B3383471 : Blo 591290 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B3809663 : Blo 591290 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2859401 : Blo 591290 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B2008043 : Blo 591290 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B27730945 : Blo 591290 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B14460443 : Blo 591290 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B65644643 : Blo 591290 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B1124513 : Blo 591290 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B6432959 : Blo 591290 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B15182153 : Blo 591290 15182153 := bstep (se 2 (by rfl) ⟨5693307, by rfl⟩ : syracuseStep 15182153 = 11386615) B11386615
theorem B961001 : Blo 591290 961001 := bstep (se 2 (by rfl) ⟨360375, by rfl⟩ : syracuseStep 961001 = 720751) B720751
theorem B667039 : Blo 591290 667039 := bstep (se 1 (by rfl) ⟨500279, by rfl⟩ : syracuseStep 667039 = 1000559) B1000559
theorem B667327 : Blo 591290 667327 := bstep (se 1 (by rfl) ⟨500495, by rfl⟩ : syracuseStep 667327 = 1000991) B1000991
theorem B667903 : Blo 591290 667903 := bstep (se 1 (by rfl) ⟨500927, by rfl⟩ : syracuseStep 667903 = 1001855) B1001855
theorem B6402989 : Blo 591290 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B1127611 : Blo 591290 1127611 := bstep (se 1 (by rfl) ⟨845708, by rfl⟩ : syracuseStep 1127611 = 1691417) B1691417
theorem B1717615 : Blo 591290 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B669055 : Blo 591290 669055 := bstep (se 1 (by rfl) ⟨501791, by rfl⟩ : syracuseStep 669055 = 1003583) B1003583
theorem B2995865 : Blo 591290 2995865 := bstep (se 2 (by rfl) ⟨1123449, by rfl⟩ : syracuseStep 2995865 = 2246899) B2246899
theorem B669631 : Blo 591290 669631 := bstep (se 1 (by rfl) ⟨502223, by rfl⟩ : syracuseStep 669631 = 1004447) B1004447
theorem B4503761 : Blo 591290 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B6338845 : Blo 591290 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B2538323 : Blo 591290 2538323 := bstep (se 1 (by rfl) ⟨1903742, by rfl⟩ : syracuseStep 2538323 = 3807485) B3807485
theorem B12139415 : Blo 591290 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B998473 : Blo 591290 998473 := bstep (se 2 (by rfl) ⟨374427, by rfl⟩ : syracuseStep 998473 = 748855) B748855
theorem B999067 : Blo 591290 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B2440955 : Blo 591290 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B20528909 : Blo 591290 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B12173237 : Blo 591290 12173237 := bstep (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) B1141241
theorem B1687625 : Blo 591290 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B1687817 : Blo 591290 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B2933279 : Blo 591290 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B2245715 : Blo 591290 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B1688683 : Blo 591290 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B2245913 : Blo 591290 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1000775 : Blo 591290 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B1689083 : Blo 591290 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B2999915 : Blo 591290 2999915 := bstep (se 1 (by rfl) ⟨2249936, by rfl⟩ : syracuseStep 2999915 = 4499873) B4499873
theorem B4507649 : Blo 591290 4507649 := bstep (se 2 (by rfl) ⟨1690368, by rfl⟩ : syracuseStep 4507649 = 3380737) B3380737
theorem B1263737 : Blo 591290 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B32458907 : Blo 591290 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B1001963 : Blo 591290 1001963 := bstep (se 1 (by rfl) ⟨751472, by rfl⟩ : syracuseStep 1001963 = 1502945) B1502945
theorem B48548429 : Blo 591290 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1330451 : Blo 591290 1330451 := bstep (se 1 (by rfl) ⟨997838, by rfl⟩ : syracuseStep 1330451 = 1995677) B1995677
theorem B1330919 : Blo 591290 1330919 := bstep (se 1 (by rfl) ⟨998189, by rfl⟩ : syracuseStep 1330919 = 1996379) B1996379
theorem B1331081 : Blo 591290 1331081 := bstep (se 2 (by rfl) ⟨499155, by rfl⟩ : syracuseStep 1331081 = 998311) B998311
theorem B5689277 : Blo 591290 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B2248843 : Blo 591290 2248843 := bstep (se 1 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 2248843 = 3373265) B3373265
theorem B1692191 : Blo 591290 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1332179 : Blo 591290 1332179 := bstep (se 1 (by rfl) ⟨999134, by rfl⟩ : syracuseStep 1332179 = 1998269) B1998269
theorem B677167 : Blo 591290 677167 := bstep (se 1 (by rfl) ⟨507875, by rfl⟩ : syracuseStep 677167 = 1015751) B1015751
theorem B1693001 : Blo 591290 1693001 := bstep (se 2 (by rfl) ⟨634875, by rfl⟩ : syracuseStep 1693001 = 1269751) B1269751
theorem B1496819 : Blo 591290 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B3004289 : Blo 591290 3004289 := bstep (se 2 (by rfl) ⟨1126608, by rfl⟩ : syracuseStep 3004289 = 2253217) B2253217
theorem B1333439 : Blo 591290 1333439 := bstep (se 1 (by rfl) ⟨1000079, by rfl⟩ : syracuseStep 1333439 = 2000159) B2000159
theorem B1497791 : Blo 591290 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B842599 : Blo 591290 842599 := bstep (se 1 (by rfl) ⟨631949, by rfl⟩ : syracuseStep 842599 = 1263899) B1263899
theorem B6871931 : Blo 591290 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B13687703 : Blo 591290 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B842815 : Blo 591290 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B1334483 : Blo 591290 1334483 := bstep (se 1 (by rfl) ⟨1000862, by rfl⟩ : syracuseStep 1334483 = 2001725) B2001725
theorem B1334555 : Blo 591290 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B1498439 : Blo 591290 1498439 := bstep (se 1 (by rfl) ⟨1123829, by rfl⟩ : syracuseStep 1498439 = 2247659) B2247659
theorem B1498459 : Blo 591290 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B1334753 : Blo 591290 1334753 := bstep (se 2 (by rfl) ⟨500532, by rfl⟩ : syracuseStep 1334753 = 1001065) B1001065
theorem B7626959 : Blo 591290 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B1335545 : Blo 591290 1335545 := bstep (se 2 (by rfl) ⟨500829, by rfl⟩ : syracuseStep 1335545 = 1001659) B1001659
theorem B1499431 : Blo 591290 1499431 := bstep (se 1 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 1499431 = 2249147) B2249147
theorem B1335815 : Blo 591290 1335815 := bstep (se 1 (by rfl) ⟨1001861, by rfl⟩ : syracuseStep 1335815 = 2003723) B2003723
theorem B1335995 : Blo 591290 1335995 := bstep (se 1 (by rfl) ⟨1001996, by rfl⟩ : syracuseStep 1335995 = 2003993) B2003993
theorem B1499867 : Blo 591290 1499867 := bstep (se 1 (by rfl) ⟨1124900, by rfl⟩ : syracuseStep 1499867 = 2249801) B2249801
theorem B48751409 : Blo 591290 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B1336481 : Blo 591290 1336481 := bstep (se 2 (by rfl) ⟨501180, by rfl⟩ : syracuseStep 1336481 = 1002361) B1002361
theorem B12346663 : Blo 591290 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1926497 : Blo 591290 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B2713085 : Blo 591290 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B1500727 : Blo 591290 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1336895 : Blo 591290 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B5138083 : Blo 591290 5138083 := bstep (se 1 (by rfl) ⟨3853562, by rfl⟩ : syracuseStep 5138083 = 7707125) B7707125
theorem B1337003 : Blo 591290 1337003 := bstep (se 1 (by rfl) ⟨1002752, by rfl⟩ : syracuseStep 1337003 = 2005505) B2005505
theorem B3598127 : Blo 591290 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B37119833 : Blo 591290 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B27453329 : Blo 591290 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B1337255 : Blo 591290 1337255 := bstep (se 1 (by rfl) ⟨1002941, by rfl⟩ : syracuseStep 1337255 = 2005883) B2005883
theorem B62580869 : Blo 591290 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B1337543 : Blo 591290 1337543 := bstep (se 1 (by rfl) ⟨1003157, by rfl⟩ : syracuseStep 1337543 = 2006315) B2006315
theorem B1337723 : Blo 591290 1337723 := bstep (se 1 (by rfl) ⟨1003292, by rfl⟩ : syracuseStep 1337723 = 2006585) B2006585
theorem B1337831 : Blo 591290 1337831 := bstep (se 1 (by rfl) ⟨1003373, by rfl⟩ : syracuseStep 1337831 = 2006747) B2006747
theorem B9628217 : Blo 591290 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B1337993 : Blo 591290 1337993 := bstep (se 2 (by rfl) ⟨501747, by rfl⟩ : syracuseStep 1337993 = 1003495) B1003495
theorem B1338011 : Blo 591290 1338011 := bstep (se 1 (by rfl) ⟨1003508, by rfl⟩ : syracuseStep 1338011 = 2007017) B2007017
theorem B1895719 : Blo 591290 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B6778241 : Blo 591290 6778241 := bstep (se 2 (by rfl) ⟨2541840, by rfl⟩ : syracuseStep 6778241 = 5083681) B5083681
theorem B30764461 : Blo 591290 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B1338983 : Blo 591290 1338983 := bstep (se 1 (by rfl) ⟨1004237, by rfl⟩ : syracuseStep 1338983 = 2008475) B2008475
theorem B1896119 : Blo 591290 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B2289505 : Blo 591290 2289505 := bstep (se 2 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 2289505 = 1717129) B1717129
theorem B1601495 : Blo 591290 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B3600463 : Blo 591290 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B1503643 : Blo 591290 1503643 := bstep (se 1 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 1503643 = 2255465) B2255465
theorem B3011903 : Blo 591290 3011903 := bstep (se 1 (by rfl) ⟨2258927, by rfl⟩ : syracuseStep 3011903 = 4517855) B4517855
theorem B1996271 : Blo 591290 1996271 := bstep (se 1 (by rfl) ⟨1497203, by rfl⟩ : syracuseStep 1996271 = 2994407) B2994407
theorem B17069777 : Blo 591290 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B1603319 : Blo 591290 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B2848807 : Blo 591290 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B4061225 : Blo 591290 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B4290803 : Blo 591290 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B3046187 : Blo 591290 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B1999241 : Blo 591290 1999241 := bstep (se 2 (by rfl) ⟨749715, by rfl⟩ : syracuseStep 1999241 = 1499431) B1499431
theorem B1999943 : Blo 591290 1999943 := bstep (se 1 (by rfl) ⟨1499957, by rfl⟩ : syracuseStep 1999943 = 2999915) B2999915
theorem B1901819 : Blo 591290 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B591343 : Blo 591290 591343 := bstep (se 1 (by rfl) ⟨443507, by rfl⟩ : syracuseStep 591343 = 887015) B887015
theorem B591359 : Blo 591290 591359 := bstep (se 1 (by rfl) ⟨443519, by rfl⟩ : syracuseStep 591359 = 887039) B887039
theorem B591451 : Blo 591290 591451 := bstep (se 1 (by rfl) ⟨443588, by rfl⟩ : syracuseStep 591451 = 887177) B887177
theorem B2000969 : Blo 591290 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B4327519 : Blo 591290 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B886967 : Blo 591290 886967 := bstep (se 1 (by rfl) ⟨665225, by rfl⟩ : syracuseStep 886967 = 1330451) B1330451
theorem B6850777 : Blo 591290 6850777 := bstep (se 2 (by rfl) ⟨2569041, by rfl⟩ : syracuseStep 6850777 = 5138083) B5138083
theorem B592191 : Blo 591290 592191 := bstep (se 1 (by rfl) ⟨444143, by rfl⟩ : syracuseStep 592191 = 888287) B888287
theorem B592231 : Blo 591290 592231 := bstep (se 1 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 592231 = 888347) B888347
theorem B592319 : Blo 591290 592319 := bstep (se 1 (by rfl) ⟨444239, by rfl⟩ : syracuseStep 592319 = 888479) B888479
theorem B887279 : Blo 591290 887279 := bstep (se 1 (by rfl) ⟨665459, by rfl⟩ : syracuseStep 887279 = 1330919) B1330919
theorem B887387 : Blo 591290 887387 := bstep (se 1 (by rfl) ⟨665540, by rfl⟩ : syracuseStep 887387 = 1331081) B1331081
theorem B592495 : Blo 591290 592495 := bstep (se 1 (by rfl) ⟨444371, by rfl⟩ : syracuseStep 592495 = 888743) B888743
theorem B592511 : Blo 591290 592511 := bstep (se 1 (by rfl) ⟨444383, by rfl⟩ : syracuseStep 592511 = 888767) B888767
theorem B592615 : Blo 591290 592615 := bstep (se 1 (by rfl) ⟨444461, by rfl⟩ : syracuseStep 592615 = 888923) B888923
theorem B592711 : Blo 591290 592711 := bstep (se 1 (by rfl) ⟨444533, by rfl⟩ : syracuseStep 592711 = 889067) B889067
theorem B592751 : Blo 591290 592751 := bstep (se 1 (by rfl) ⟨444563, by rfl⟩ : syracuseStep 592751 = 889127) B889127
theorem B592927 : Blo 591290 592927 := bstep (se 1 (by rfl) ⟨444695, by rfl⟩ : syracuseStep 592927 = 889391) B889391
theorem B593063 : Blo 591290 593063 := bstep (se 1 (by rfl) ⟨444797, by rfl⟩ : syracuseStep 593063 = 889595) B889595
theorem B6753455 : Blo 591290 6753455 := bstep (se 1 (by rfl) ⟨5065091, by rfl⟩ : syracuseStep 6753455 = 10130183) B10130183
theorem B888119 : Blo 591290 888119 := bstep (se 1 (by rfl) ⟨666089, by rfl⟩ : syracuseStep 888119 = 1332179) B1332179
theorem B593311 : Blo 591290 593311 := bstep (se 1 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 593311 = 889967) B889967
theorem B593359 : Blo 591290 593359 := bstep (se 1 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 593359 = 890039) B890039
theorem B7605839 : Blo 591290 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B593519 : Blo 591290 593519 := bstep (se 1 (by rfl) ⟨445139, by rfl⟩ : syracuseStep 593519 = 890279) B890279
theorem B593639 : Blo 591290 593639 := bstep (se 1 (by rfl) ⟨445229, by rfl⟩ : syracuseStep 593639 = 890459) B890459
theorem B2002859 : Blo 591290 2002859 := bstep (se 1 (by rfl) ⟨1502144, by rfl⟩ : syracuseStep 2002859 = 3004289) B3004289
theorem B3215335 : Blo 591290 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B888959 : Blo 591290 888959 := bstep (se 1 (by rfl) ⟨666719, by rfl⟩ : syracuseStep 888959 = 1333439) B1333439
theorem B594143 : Blo 591290 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B594159 : Blo 591290 594159 := bstep (se 1 (by rfl) ⟨445619, by rfl⟩ : syracuseStep 594159 = 891239) B891239
theorem B594203 : Blo 591290 594203 := bstep (se 1 (by rfl) ⟨445652, by rfl⟩ : syracuseStep 594203 = 891305) B891305
theorem B2527625 : Blo 591290 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B594459 : Blo 591290 594459 := bstep (se 1 (by rfl) ⟨445844, by rfl⟩ : syracuseStep 594459 = 891689) B891689
theorem B889385 : Blo 591290 889385 := bstep (se 2 (by rfl) ⟨333519, by rfl⟩ : syracuseStep 889385 = 667039) B667039
theorem B594599 : Blo 591290 594599 := bstep (se 1 (by rfl) ⟨445949, by rfl⟩ : syracuseStep 594599 = 891899) B891899
theorem B594623 : Blo 591290 594623 := bstep (se 1 (by rfl) ⟨445967, by rfl⟩ : syracuseStep 594623 = 891935) B891935
theorem B594639 : Blo 591290 594639 := bstep (se 1 (by rfl) ⟨445979, by rfl⟩ : syracuseStep 594639 = 891959) B891959
theorem B594719 : Blo 591290 594719 := bstep (se 1 (by rfl) ⟨446039, by rfl⟩ : syracuseStep 594719 = 892079) B892079
theorem B889655 : Blo 591290 889655 := bstep (se 1 (by rfl) ⟨667241, by rfl⟩ : syracuseStep 889655 = 1334483) B1334483
theorem B16192343 : Blo 591290 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B889703 : Blo 591290 889703 := bstep (se 1 (by rfl) ⟨667277, by rfl⟩ : syracuseStep 889703 = 1334555) B1334555
theorem B594815 : Blo 591290 594815 := bstep (se 1 (by rfl) ⟨446111, by rfl⟩ : syracuseStep 594815 = 892223) B892223
theorem B889769 : Blo 591290 889769 := bstep (se 2 (by rfl) ⟨333663, by rfl⟩ : syracuseStep 889769 = 667327) B667327
theorem B594911 : Blo 591290 594911 := bstep (se 1 (by rfl) ⟨446183, by rfl⟩ : syracuseStep 594911 = 892367) B892367
theorem B889835 : Blo 591290 889835 := bstep (se 1 (by rfl) ⟨667376, by rfl⟩ : syracuseStep 889835 = 1334753) B1334753
theorem B3052673 : Blo 591290 3052673 := bstep (se 2 (by rfl) ⟨1144752, by rfl⟩ : syracuseStep 3052673 = 2289505) B2289505
theorem B595167 : Blo 591290 595167 := bstep (se 1 (by rfl) ⟨446375, by rfl⟩ : syracuseStep 595167 = 892751) B892751
theorem B595199 : Blo 591290 595199 := bstep (se 1 (by rfl) ⟨446399, by rfl⟩ : syracuseStep 595199 = 892799) B892799
theorem B595247 : Blo 591290 595247 := bstep (se 1 (by rfl) ⟨446435, by rfl⟩ : syracuseStep 595247 = 892871) B892871
theorem B5084639 : Blo 591290 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B890363 : Blo 591290 890363 := bstep (se 1 (by rfl) ⟨667772, by rfl⟩ : syracuseStep 890363 = 1335545) B1335545
theorem B1906267 : Blo 591290 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B4495013 : Blo 591290 4495013 := bstep (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) B842815
theorem B890537 : Blo 591290 890537 := bstep (se 2 (by rfl) ⟨333951, by rfl⟩ : syracuseStep 890537 = 667903) B667903
theorem B890543 : Blo 591290 890543 := bstep (se 1 (by rfl) ⟨667907, by rfl⟩ : syracuseStep 890543 = 1335815) B1335815
theorem B890663 : Blo 591290 890663 := bstep (se 1 (by rfl) ⟨667997, by rfl⟩ : syracuseStep 890663 = 1335995) B1335995
theorem B2004857 : Blo 591290 2004857 := bstep (se 2 (by rfl) ⟨751821, by rfl⟩ : syracuseStep 2004857 = 1503643) B1503643
theorem B890987 : Blo 591290 890987 := bstep (se 1 (by rfl) ⟨668240, by rfl⟩ : syracuseStep 890987 = 1336481) B1336481
theorem B1284331 : Blo 591290 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B1808723 : Blo 591290 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B9640295 : Blo 591290 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B891263 : Blo 591290 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B891335 : Blo 591290 891335 := bstep (se 1 (by rfl) ⟨668501, by rfl⟩ : syracuseStep 891335 = 1337003) B1337003
theorem B2398751 : Blo 591290 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B24746555 : Blo 591290 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B891503 : Blo 591290 891503 := bstep (se 1 (by rfl) ⟨668627, by rfl⟩ : syracuseStep 891503 = 1337255) B1337255
theorem B41720579 : Blo 591290 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B891695 : Blo 591290 891695 := bstep (se 1 (by rfl) ⟨668771, by rfl⟩ : syracuseStep 891695 = 1337543) B1337543
theorem B3611557 : Blo 591290 3611557 := bstep (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) B677167
theorem B891815 : Blo 591290 891815 := bstep (se 1 (by rfl) ⟨668861, by rfl⟩ : syracuseStep 891815 = 1337723) B1337723
theorem B891887 : Blo 591290 891887 := bstep (se 1 (by rfl) ⟨668915, by rfl⟩ : syracuseStep 891887 = 1337831) B1337831
theorem B891995 : Blo 591290 891995 := bstep (se 1 (by rfl) ⟨668996, by rfl⟩ : syracuseStep 891995 = 1337993) B1337993
theorem B892007 : Blo 591290 892007 := bstep (se 1 (by rfl) ⟨669005, by rfl⟩ : syracuseStep 892007 = 1338011) B1338011
theorem B892073 : Blo 591290 892073 := bstep (se 2 (by rfl) ⟨334527, by rfl⟩ : syracuseStep 892073 = 669055) B669055
theorem B892655 : Blo 591290 892655 := bstep (se 1 (by rfl) ⟨669491, by rfl⟩ : syracuseStep 892655 = 1338983) B1338983
theorem B892841 : Blo 591290 892841 := bstep (se 2 (by rfl) ⟨334815, by rfl⟩ : syracuseStep 892841 = 669631) B669631
theorem B4268659 : Blo 591290 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B12853889 : Blo 591290 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B2007935 : Blo 591290 2007935 := bstep (se 1 (by rfl) ⟨1505951, by rfl⟩ : syracuseStep 2007935 = 3011903) B3011903
theorem B1123465 : Blo 591290 1123465 := bstep (se 2 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 1123465 = 842599) B842599
theorem B11379851 : Blo 591290 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B2860535 : Blo 591290 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B1125083 : Blo 591290 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B1354619 : Blo 591290 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B4500845 : Blo 591290 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B667183 : Blo 591290 667183 := bstep (se 1 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 667183 = 1000775) B1000775
theorem B1126055 : Blo 591290 1126055 := bstep (se 1 (by rfl) ⟨844541, by rfl⟩ : syracuseStep 1126055 = 1689083) B1689083
theorem B36974593 : Blo 591290 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B21639271 : Blo 591290 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B667975 : Blo 591290 667975 := bstep (se 1 (by rfl) ⟨500981, by rfl⟩ : syracuseStep 667975 = 1001963) B1001963
theorem B9613687 : Blo 591290 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B16462217 : Blo 591290 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B1683899 : Blo 591290 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B2405177 : Blo 591290 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B2144393 : Blo 591290 2144393 := bstep (se 2 (by rfl) ⟨804147, by rfl⟩ : syracuseStep 2144393 = 1608295) B1608295
theorem B1128667 : Blo 591290 1128667 := bstep (se 1 (by rfl) ⟨846500, by rfl⟩ : syracuseStep 1128667 = 1693001) B1693001
theorem B997879 : Blo 591290 997879 := bstep (se 1 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 997879 = 1496819) B1496819
theorem B998527 : Blo 591290 998527 := bstep (se 1 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 998527 = 1497791) B1497791
theorem B9125135 : Blo 591290 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B4275517 : Blo 591290 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B998959 : Blo 591290 998959 := bstep (se 1 (by rfl) ⟨749219, by rfl⟩ : syracuseStep 998959 = 1498439) B1498439
theorem B4800617 : Blo 591290 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B10829933 : Blo 591290 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B2998457 : Blo 591290 2998457 := bstep (se 2 (by rfl) ⟨1124421, by rfl⟩ : syracuseStep 2998457 = 2248843) B2248843
theorem B2539775 : Blo 591290 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B999911 : Blo 591290 999911 := bstep (se 1 (by rfl) ⟨749933, by rfl⟩ : syracuseStep 999911 = 1499867) B1499867
theorem B18302219 : Blo 591290 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B43763095 : Blo 591290 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B640667 : Blo 591290 640667 := bstep (se 1 (by rfl) ⟨480500, by rfl⟩ : syracuseStep 640667 = 961001) B961001
theorem B2542013 : Blo 591290 2542013 := bstep (se 3 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 2542013 = 953255) B953255
theorem B1264079 : Blo 591290 1264079 := bstep (se 1 (by rfl) ⟨948059, by rfl⟩ : syracuseStep 1264079 = 1896119) B1896119
theorem B1067663 : Blo 591290 1067663 := bstep (se 1 (by rfl) ⟨800747, by rfl⟩ : syracuseStep 1067663 = 1601495) B1601495
theorem B1330847 : Blo 591290 1330847 := bstep (se 1 (by rfl) ⟨998135, by rfl⟩ : syracuseStep 1330847 = 1996271) B1996271
theorem B1331297 : Blo 591290 1331297 := bstep (se 2 (by rfl) ⟨499236, by rfl⟩ : syracuseStep 1331297 = 998473) B998473
theorem B3002507 : Blo 591290 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B1692215 : Blo 591290 1692215 := bstep (se 1 (by rfl) ⟨1269161, by rfl⟩ : syracuseStep 1692215 = 2538323) B2538323
theorem B1332089 : Blo 591290 1332089 := bstep (se 2 (by rfl) ⟨499533, by rfl⟩ : syracuseStep 1332089 = 999067) B999067
theorem B1627303 : Blo 591290 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B13685939 : Blo 591290 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B8115491 : Blo 591290 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B1332791 : Blo 591290 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B1955519 : Blo 591290 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B1071071 : Blo 591290 1071071 := bstep (se 1 (by rfl) ⟨803303, by rfl⟩ : syracuseStep 1071071 = 1606607) B1606607
theorem B1497143 : Blo 591290 1497143 := bstep (se 1 (by rfl) ⟨1122857, by rfl⟩ : syracuseStep 1497143 = 2245715) B2245715
theorem B1497275 : Blo 591290 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B3005099 : Blo 591290 3005099 := bstep (se 1 (by rfl) ⟨2253824, by rfl⟩ : syracuseStep 3005099 = 4507649) B4507649
theorem B2710259 : Blo 591290 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B842491 : Blo 591290 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B4512509 : Blo 591290 4512509 := bstep (se 3 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 4512509 = 1692191) B1692191
theorem B2251577 : Blo 591290 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B32365619 : Blo 591290 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1334735 : Blo 591290 1334735 := bstep (se 1 (by rfl) ⟨1001051, by rfl⟩ : syracuseStep 1334735 = 2002103) B2002103
theorem B3792851 : Blo 591290 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B2253035 : Blo 591290 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B1336391 : Blo 591290 1336391 := bstep (se 1 (by rfl) ⟨1002293, by rfl⟩ : syracuseStep 1336391 = 2004587) B2004587
theorem B41019281 : Blo 591290 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B4581287 : Blo 591290 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B9136091 : Blo 591290 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B1337399 : Blo 591290 1337399 := bstep (se 1 (by rfl) ⟨1003049, by rfl⟩ : syracuseStep 1337399 = 2006099) B2006099
theorem B1337759 : Blo 591290 1337759 := bstep (se 1 (by rfl) ⟨1003319, by rfl⟩ : syracuseStep 1337759 = 2006639) B2006639
theorem B2255647 : Blo 591290 2255647 := bstep (se 1 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 2255647 = 3383471) B3383471
theorem B32500939 : Blo 591290 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B1338695 : Blo 591290 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B749675 : Blo 591290 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B4288639 : Blo 591290 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B10121435 : Blo 591290 10121435 := bstep (se 1 (by rfl) ⟨7591076, by rfl⟩ : syracuseStep 10121435 = 15182153) B15182153
theorem B1503481 : Blo 591290 1503481 := bstep (se 2 (by rfl) ⟨563805, by rfl⟩ : syracuseStep 1503481 = 1127611) B1127611
theorem B6418811 : Blo 591290 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B2290153 : Blo 591290 2290153 := bstep (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) B1717615
theorem B4518827 : Blo 591290 4518827 := bstep (se 1 (by rfl) ⟨3389120, by rfl⟩ : syracuseStep 4518827 = 6778241) B6778241
theorem B3798409 : Blo 591290 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B8451793 : Blo 591290 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1997243 : Blo 591290 1997243 := bstep (se 1 (by rfl) ⟨1497932, by rfl⟩ : syracuseStep 1997243 = 2995865) B2995865
theorem B1997945 : Blo 591290 1997945 := bstep (se 2 (by rfl) ⟨749229, by rfl⟩ : syracuseStep 1997945 = 1498459) B1498459
theorem B2030791 : Blo 591290 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B8092943 : Blo 591290 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B1998971 : Blo 591290 1998971 := bstep (se 1 (by rfl) ⟨1499228, by rfl⟩ : syracuseStep 1998971 = 2998457) B2998457
theorem B1999133 : Blo 591290 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B591311 : Blo 591290 591311 := bstep (se 1 (by rfl) ⟨443483, by rfl⟩ : syracuseStep 591311 = 886967) B886967
theorem B591519 : Blo 591290 591519 := bstep (se 1 (by rfl) ⟨443639, by rfl⟩ : syracuseStep 591519 = 887279) B887279
theorem B591591 : Blo 591290 591591 := bstep (se 1 (by rfl) ⟨443693, by rfl⟩ : syracuseStep 591591 = 887387) B887387
theorem B592079 : Blo 591290 592079 := bstep (se 1 (by rfl) ⟨444059, by rfl⟩ : syracuseStep 592079 = 888119) B888119
theorem B887231 : Blo 591290 887231 := bstep (se 1 (by rfl) ⟨665423, by rfl⟩ : syracuseStep 887231 = 1330847) B1330847
theorem B887531 : Blo 591290 887531 := bstep (se 1 (by rfl) ⟨665648, by rfl⟩ : syracuseStep 887531 = 1331297) B1331297
theorem B592639 : Blo 591290 592639 := bstep (se 1 (by rfl) ⟨444479, by rfl⟩ : syracuseStep 592639 = 888959) B888959
theorem B2001671 : Blo 591290 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B5770025 : Blo 591290 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B592923 : Blo 591290 592923 := bstep (se 1 (by rfl) ⟨444692, by rfl⟩ : syracuseStep 592923 = 889385) B889385
theorem B593103 : Blo 591290 593103 := bstep (se 1 (by rfl) ⟨444827, by rfl⟩ : syracuseStep 593103 = 889655) B889655
theorem B593135 : Blo 591290 593135 := bstep (se 1 (by rfl) ⟨444851, by rfl⟩ : syracuseStep 593135 = 889703) B889703
theorem B888059 : Blo 591290 888059 := bstep (se 1 (by rfl) ⟨666044, by rfl⟩ : syracuseStep 888059 = 1332089) B1332089
theorem B593179 : Blo 591290 593179 := bstep (se 1 (by rfl) ⟨444884, by rfl⟩ : syracuseStep 593179 = 889769) B889769
theorem B593223 : Blo 591290 593223 := bstep (se 1 (by rfl) ⟨444917, by rfl⟩ : syracuseStep 593223 = 889835) B889835
theorem B2035115 : Blo 591290 2035115 := bstep (se 1 (by rfl) ⟨1526336, by rfl⟩ : syracuseStep 2035115 = 3052673) B3052673
theorem B5410327 : Blo 591290 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B593575 : Blo 591290 593575 := bstep (se 1 (by rfl) ⟨445181, by rfl⟩ : syracuseStep 593575 = 890363) B890363
theorem B888527 : Blo 591290 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B593691 : Blo 591290 593691 := bstep (se 1 (by rfl) ⟨445268, by rfl⟩ : syracuseStep 593691 = 890537) B890537
theorem B593695 : Blo 591290 593695 := bstep (se 1 (by rfl) ⟨445271, by rfl⟩ : syracuseStep 593695 = 890543) B890543
theorem B593775 : Blo 591290 593775 := bstep (se 1 (by rfl) ⟨445331, by rfl⟩ : syracuseStep 593775 = 890663) B890663
theorem B593991 : Blo 591290 593991 := bstep (se 1 (by rfl) ⟨445493, by rfl⟩ : syracuseStep 593991 = 890987) B890987
theorem B6426863 : Blo 591290 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B594175 : Blo 591290 594175 := bstep (se 1 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 594175 = 891263) B891263
theorem B594223 : Blo 591290 594223 := bstep (se 1 (by rfl) ⟨445667, by rfl⟩ : syracuseStep 594223 = 891335) B891335
theorem B1708445 : Blo 591290 1708445 := bstep (se 3 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 1708445 = 640667) B640667
theorem B594335 : Blo 591290 594335 := bstep (se 1 (by rfl) ⟨445751, by rfl⟩ : syracuseStep 594335 = 891503) B891503
theorem B2003399 : Blo 591290 2003399 := bstep (se 1 (by rfl) ⟨1502549, by rfl⟩ : syracuseStep 2003399 = 3005099) B3005099
theorem B1806839 : Blo 591290 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B594463 : Blo 591290 594463 := bstep (se 1 (by rfl) ⟨445847, by rfl⟩ : syracuseStep 594463 = 891695) B891695
theorem B594543 : Blo 591290 594543 := bstep (se 1 (by rfl) ⟨445907, by rfl⟩ : syracuseStep 594543 = 891815) B891815
theorem B594591 : Blo 591290 594591 := bstep (se 1 (by rfl) ⟨445943, by rfl⟩ : syracuseStep 594591 = 891887) B891887
theorem B594663 : Blo 591290 594663 := bstep (se 1 (by rfl) ⟨445997, by rfl⟩ : syracuseStep 594663 = 891995) B891995
theorem B889577 : Blo 591290 889577 := bstep (se 2 (by rfl) ⟨333591, by rfl⟩ : syracuseStep 889577 = 667183) B667183
theorem B594671 : Blo 591290 594671 := bstep (se 1 (by rfl) ⟨446003, by rfl⟩ : syracuseStep 594671 = 892007) B892007
theorem B594715 : Blo 591290 594715 := bstep (se 1 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 594715 = 892073) B892073
theorem B889823 : Blo 591290 889823 := bstep (se 1 (by rfl) ⟨667367, by rfl⟩ : syracuseStep 889823 = 1334735) B1334735
theorem B595103 : Blo 591290 595103 := bstep (se 1 (by rfl) ⟨446327, by rfl⟩ : syracuseStep 595103 = 892655) B892655
theorem B595227 : Blo 591290 595227 := bstep (se 1 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 595227 = 892841) B892841
theorem B2528567 : Blo 591290 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B2004641 : Blo 591290 2004641 := bstep (se 2 (by rfl) ⟨751740, by rfl⟩ : syracuseStep 2004641 = 1503481) B1503481
theorem B890633 : Blo 591290 890633 := bstep (se 2 (by rfl) ⟨333987, by rfl⟩ : syracuseStep 890633 = 667975) B667975
theorem B12818249 : Blo 591290 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B3053537 : Blo 591290 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B890927 : Blo 591290 890927 := bstep (se 1 (by rfl) ⟨668195, by rfl⟩ : syracuseStep 890927 = 1336391) B1336391
theorem B1907023 : Blo 591290 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B3054191 : Blo 591290 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B891599 : Blo 591290 891599 := bstep (se 1 (by rfl) ⟨668699, by rfl⟩ : syracuseStep 891599 = 1337399) B1337399
theorem B2169737 : Blo 591290 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B891839 : Blo 591290 891839 := bstep (se 1 (by rfl) ⟨668879, by rfl⟩ : syracuseStep 891839 = 1337759) B1337759
theorem B892463 : Blo 591290 892463 := bstep (se 1 (by rfl) ⟨669347, by rfl⟩ : syracuseStep 892463 = 1338695) B1338695
theorem B1122599 : Blo 591290 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B1712441 : Blo 591290 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B1123321 : Blo 591290 1123321 := bstep (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) B842491
theorem B7219955 : Blo 591290 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B666607 : Blo 591290 666607 := bstep (se 1 (by rfl) ⟨499955, by rfl⟩ : syracuseStep 666607 = 999911) B999911
theorem B12201479 : Blo 591290 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B17116829 : Blo 591290 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B4502303 : Blo 591290 4502303 := bstep (se 1 (by rfl) ⟨3376727, by rfl⟩ : syracuseStep 4502303 = 6753455) B6753455
theorem B1128143 : Blo 591290 1128143 := bstep (se 1 (by rfl) ⟨846107, by rfl⟩ : syracuseStep 1128143 = 1692215) B1692215
theorem B9123959 : Blo 591290 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B3389759 : Blo 591290 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B2996675 : Blo 591290 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B998095 : Blo 591290 998095 := bstep (se 1 (by rfl) ⟨748571, by rfl⟩ : syracuseStep 998095 = 1497143) B1497143
theorem B998183 : Blo 591290 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B43334585 : Blo 591290 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B16497703 : Blo 591290 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B21577079 : Blo 591290 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B49299457 : Blo 591290 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B28852361 : Blo 591290 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B5718185 : Blo 591290 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B8569259 : Blo 591290 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B7586567 : Blo 591290 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B27346187 : Blo 591290 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B5064545 : Blo 591290 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B903079 : Blo 591290 903079 := bstep (se 1 (by rfl) ⟨677309, by rfl⟩ : syracuseStep 903079 = 1354619) B1354619
theorem B2541689 : Blo 591290 2541689 := bstep (se 2 (by rfl) ⟨953133, by rfl⟩ : syracuseStep 2541689 = 1906267) B1906267
theorem B3000563 : Blo 591290 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B1330505 : Blo 591290 1330505 := bstep (se 2 (by rfl) ⟨498939, by rfl⟩ : syracuseStep 1330505 = 997879) B997879
theorem B1429595 : Blo 591290 1429595 := bstep (se 1 (by rfl) ⟨1072196, by rfl⟩ : syracuseStep 1429595 = 2144393) B2144393
theorem B1331369 : Blo 591290 1331369 := bstep (se 2 (by rfl) ⟨499263, by rfl⟩ : syracuseStep 1331369 = 998527) B998527
theorem B2707721 : Blo 591290 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B1331495 : Blo 591290 1331495 := bstep (se 1 (by rfl) ⟨998621, by rfl⟩ : syracuseStep 1331495 = 1997243) B1997243
theorem B1331945 : Blo 591290 1331945 := bstep (se 2 (by rfl) ⟨499479, by rfl⟩ : syracuseStep 1331945 = 998959) B998959
theorem B1331963 : Blo 591290 1331963 := bstep (se 1 (by rfl) ⟨998972, by rfl⟩ : syracuseStep 1331963 = 1997945) B1997945
theorem B5395295 : Blo 591290 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B6083423 : Blo 591290 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B3200411 : Blo 591290 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B1693183 : Blo 591290 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B1332827 : Blo 591290 1332827 := bstep (se 1 (by rfl) ⟨999620, by rfl⟩ : syracuseStep 1332827 = 1999241) B1999241
theorem B1333295 : Blo 591290 1333295 := bstep (se 1 (by rfl) ⟨999971, by rfl⟩ : syracuseStep 1333295 = 1999943) B1999943
theorem B5691545 : Blo 591290 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B6740333 : Blo 591290 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B1333979 : Blo 591290 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B1497953 : Blo 591290 1497953 := bstep (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) B1123465
theorem B1694675 : Blo 591290 1694675 := bstep (se 1 (by rfl) ⟨1271006, by rfl⟩ : syracuseStep 1694675 = 2542013) B2542013
theorem B842719 : Blo 591290 842719 := bstep (se 1 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 842719 = 1264079) B1264079
theorem B711775 : Blo 591290 711775 := bstep (se 1 (by rfl) ⟨533831, by rfl⟩ : syracuseStep 711775 = 1067663) B1067663
theorem B58350793 : Blo 591290 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B43179581 : Blo 591290 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B5070559 : Blo 591290 5070559 := bstep (se 1 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 5070559 = 7605839) B7605839
theorem B1335239 : Blo 591290 1335239 := bstep (se 1 (by rfl) ⟨1001429, by rfl⟩ : syracuseStep 1335239 = 2002859) B2002859
theorem B9134369 : Blo 591290 9134369 := bstep (se 2 (by rfl) ⟨3425388, by rfl⟩ : syracuseStep 9134369 = 6850777) B6850777
theorem B5071517 : Blo 591290 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B3007529 : Blo 591290 3007529 := bstep (se 2 (by rfl) ⟨1127823, by rfl⟩ : syracuseStep 3007529 = 2255647) B2255647
theorem B1303679 : Blo 591290 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B1336571 : Blo 591290 1336571 := bstep (se 1 (by rfl) ⟨1002428, by rfl⟩ : syracuseStep 1336571 = 2004857) B2004857
theorem B714047 : Blo 591290 714047 := bstep (se 1 (by rfl) ⟨535535, by rfl⟩ : syracuseStep 714047 = 1071071) B1071071
theorem B1205815 : Blo 591290 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1599167 : Blo 591290 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B3008339 : Blo 591290 3008339 := bstep (se 1 (by rfl) ⟨2256254, by rfl⟩ : syracuseStep 3008339 = 4512509) B4512509
theorem B27813719 : Blo 591290 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B1501051 : Blo 591290 1501051 := bstep (se 1 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 1501051 = 2251577) B2251577
theorem B4287113 : Blo 591290 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B1502023 : Blo 591290 1502023 := bstep (se 1 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 1502023 = 2253035) B2253035
theorem B1338623 : Blo 591290 1338623 := bstep (se 1 (by rfl) ⟨1003967, by rfl⟩ : syracuseStep 1338623 = 2007935) B2007935
theorem B6090727 : Blo 591290 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B750055 : Blo 591290 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B11269057 : Blo 591290 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B750703 : Blo 591290 750703 := bstep (se 1 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 750703 = 1126055) B1126055
theorem B6747623 : Blo 591290 6747623 := bstep (se 1 (by rfl) ⟨5060717, by rfl⟩ : syracuseStep 6747623 = 10121435) B10121435
theorem B10974811 : Blo 591290 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B1504889 : Blo 591290 1504889 := bstep (se 2 (by rfl) ⟨564333, by rfl⟩ : syracuseStep 1504889 = 1128667) B1128667
theorem B1603451 : Blo 591290 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B3012551 : Blo 591290 3012551 := bstep (se 1 (by rfl) ⟨2259413, by rfl⟩ : syracuseStep 3012551 = 4518827) B4518827
theorem B4815409 : Blo 591290 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B5700689 : Blo 591290 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B65732609 : Blo 591290 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B19234907 : Blo 591290 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B3376363 : Blo 591290 3376363 := bstep (se 1 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 3376363 = 5064545) B5064545
theorem B2000375 : Blo 591290 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B591487 : Blo 591290 591487 := bstep (se 1 (by rfl) ⟨443615, by rfl⟩ : syracuseStep 591487 = 887231) B887231
theorem B591687 : Blo 591290 591687 := bstep (se 1 (by rfl) ⟨443765, by rfl⟩ : syracuseStep 591687 = 887531) B887531
theorem B1607753 : Blo 591290 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B592039 : Blo 591290 592039 := bstep (se 1 (by rfl) ⟨444029, by rfl⟩ : syracuseStep 592039 = 888059) B888059
theorem B887003 : Blo 591290 887003 := bstep (se 1 (by rfl) ⟨665252, by rfl⟩ : syracuseStep 887003 = 1330505) B1330505
theorem B14387453 : Blo 591290 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B592351 : Blo 591290 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B2001401 : Blo 591290 2001401 := bstep (se 2 (by rfl) ⟨750525, by rfl⟩ : syracuseStep 2001401 = 1501051) B1501051
theorem B953063 : Blo 591290 953063 := bstep (se 1 (by rfl) ⟨714797, by rfl⟩ : syracuseStep 953063 = 1429595) B1429595
theorem B887579 : Blo 591290 887579 := bstep (se 1 (by rfl) ⟨665684, by rfl⟩ : syracuseStep 887579 = 1331369) B1331369
theorem B1805147 : Blo 591290 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B887663 : Blo 591290 887663 := bstep (se 1 (by rfl) ⟨665747, by rfl⟩ : syracuseStep 887663 = 1331495) B1331495
theorem B3476477 : Blo 591290 3476477 := bstep (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) B1303679
theorem B887963 : Blo 591290 887963 := bstep (se 1 (by rfl) ⟨665972, by rfl⟩ : syracuseStep 887963 = 1331945) B1331945
theorem B593051 : Blo 591290 593051 := bstep (se 1 (by rfl) ⟨444788, by rfl⟩ : syracuseStep 593051 = 889577) B889577
theorem B887975 : Blo 591290 887975 := bstep (se 1 (by rfl) ⟨665981, by rfl⟩ : syracuseStep 887975 = 1331963) B1331963
theorem B593215 : Blo 591290 593215 := bstep (se 1 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 593215 = 889823) B889823
theorem B2133607 : Blo 591290 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B888551 : Blo 591290 888551 := bstep (se 1 (by rfl) ⟨666413, by rfl⟩ : syracuseStep 888551 = 1332827) B1332827
theorem B2002697 : Blo 591290 2002697 := bstep (se 2 (by rfl) ⟨751011, by rfl⟩ : syracuseStep 2002697 = 1502023) B1502023
theorem B593755 : Blo 591290 593755 := bstep (se 1 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 593755 = 890633) B890633
theorem B888809 : Blo 591290 888809 := bstep (se 2 (by rfl) ⟨333303, by rfl⟩ : syracuseStep 888809 = 666607) B666607
theorem B2035691 : Blo 591290 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B888863 : Blo 591290 888863 := bstep (se 1 (by rfl) ⟨666647, by rfl⟩ : syracuseStep 888863 = 1333295) B1333295
theorem B593951 : Blo 591290 593951 := bstep (se 1 (by rfl) ⟨445463, by rfl⟩ : syracuseStep 593951 = 890927) B890927
theorem B4493555 : Blo 591290 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B594399 : Blo 591290 594399 := bstep (se 1 (by rfl) ⟨445799, by rfl⟩ : syracuseStep 594399 = 891599) B891599
theorem B889319 : Blo 591290 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B4264445 : Blo 591290 4264445 := bstep (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) B1599167
theorem B1446491 : Blo 591290 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B594559 : Blo 591290 594559 := bstep (se 1 (by rfl) ⟨445919, by rfl⟩ : syracuseStep 594559 = 891839) B891839
theorem B7213769 : Blo 591290 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B594975 : Blo 591290 594975 := bstep (se 1 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 594975 = 892463) B892463
theorem B890159 : Blo 591290 890159 := bstep (se 1 (by rfl) ⟨667619, by rfl⟩ : syracuseStep 890159 = 1335239) B1335239
theorem B3381011 : Blo 591290 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B2005019 : Blo 591290 2005019 := bstep (se 1 (by rfl) ⟨1503764, by rfl⟩ : syracuseStep 2005019 = 3007529) B3007529
theorem B891047 : Blo 591290 891047 := bstep (se 1 (by rfl) ⟨668285, by rfl⟩ : syracuseStep 891047 = 1336571) B1336571
theorem B2005559 : Blo 591290 2005559 := bstep (se 1 (by rfl) ⟨1504169, by rfl⟩ : syracuseStep 2005559 = 3008339) B3008339
theorem B2858075 : Blo 591290 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B892415 : Blo 591290 892415 := bstep (se 1 (by rfl) ⟨669311, by rfl⟩ : syracuseStep 892415 = 1338623) B1338623
theorem B8134319 : Blo 591290 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B11411219 : Blo 591290 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B4498415 : Blo 591290 4498415 := bstep (se 1 (by rfl) ⟨3373811, by rfl⟩ : syracuseStep 4498415 = 6747623) B6747623
theorem B1123625 : Blo 591290 1123625 := bstep (se 2 (by rfl) ⟨421359, by rfl⟩ : syracuseStep 1123625 = 842719) B842719
theorem B2008367 : Blo 591290 2008367 := bstep (se 1 (by rfl) ⟨1506275, by rfl⟩ : syracuseStep 2008367 = 3012551) B3012551
theorem B21996937 : Blo 591290 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B77801057 : Blo 591290 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B665455 : Blo 591290 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B6760745 : Blo 591290 6760745 := bstep (se 2 (by rfl) ⟨2535279, by rfl⟩ : syracuseStep 6760745 = 5070559) B5070559
theorem B3812123 : Blo 591290 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B5712839 : Blo 591290 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B5057711 : Blo 591290 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B2993597 : Blo 591290 2993597 := bstep (se 3 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 2993597 = 1122599) B1122599
theorem B18230791 : Blo 591290 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B3846683 : Blo 591290 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B1356743 : Blo 591290 1356743 := bstep (se 1 (by rfl) ⟨1017557, by rfl⟩ : syracuseStep 1356743 = 2035115) B2035115
theorem B7616501 : Blo 591290 7616501 := bstep (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) B714047
theorem B1685711 : Blo 591290 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B998635 : Blo 591290 998635 := bstep (se 1 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 998635 = 1497953) B1497953
theorem B1129783 : Blo 591290 1129783 := bstep (se 1 (by rfl) ⟨847337, by rfl⟩ : syracuseStep 1129783 = 1694675) B1694675
theorem B28786387 : Blo 591290 28786387 := bstep (se 1 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 28786387 = 43179581) B43179581
theorem B24330557 : Blo 591290 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B1000073 : Blo 591290 1000073 := bstep (se 2 (by rfl) ⟨375027, by rfl⟩ : syracuseStep 1000073 = 750055) B750055
theorem B15025409 : Blo 591290 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B1000937 : Blo 591290 1000937 := bstep (se 2 (by rfl) ⟨375351, by rfl⟩ : syracuseStep 1000937 = 750703) B750703
theorem B8144509 : Blo 591290 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B14633081 : Blo 591290 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B2542697 : Blo 591290 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B3001535 : Blo 591290 3001535 := bstep (se 1 (by rfl) ⟨2251151, by rfl⟩ : syracuseStep 3001535 = 4502303) B4502303
theorem B1330793 : Blo 591290 1330793 := bstep (se 2 (by rfl) ⟨499047, by rfl⟩ : syracuseStep 1330793 = 998095) B998095
theorem B1003259 : Blo 591290 1003259 := bstep (se 1 (by rfl) ⟨752444, by rfl⟩ : syracuseStep 1003259 = 1504889) B1504889
theorem B1068967 : Blo 591290 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B28889723 : Blo 591290 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B1332647 : Blo 591290 1332647 := bstep (se 1 (by rfl) ⟨999485, by rfl⟩ : syracuseStep 1332647 = 1998971) B1998971
theorem B1332755 : Blo 591290 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B1497761 : Blo 591290 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B1694459 : Blo 591290 1694459 := bstep (se 1 (by rfl) ⟨1270844, by rfl⟩ : syracuseStep 1694459 = 2541689) B2541689
theorem B1334447 : Blo 591290 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B1204105 : Blo 591290 1204105 := bstep (se 2 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 1204105 = 903079) B903079
theorem B4284575 : Blo 591290 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B1138963 : Blo 591290 1138963 := bstep (se 1 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 1138963 = 1708445) B1708445
theorem B1335599 : Blo 591290 1335599 := bstep (se 1 (by rfl) ⟨1001699, by rfl⟩ : syracuseStep 1335599 = 2003399) B2003399
theorem B1204559 : Blo 591290 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B4055615 : Blo 591290 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B1336427 : Blo 591290 1336427 := bstep (se 1 (by rfl) ⟨1002320, by rfl⟩ : syracuseStep 1336427 = 2004641) B2004641
theorem B8545499 : Blo 591290 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B3794363 : Blo 591290 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B8120969 : Blo 591290 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B6089579 : Blo 591290 6089579 := bstep (se 1 (by rfl) ⟨4567184, by rfl⟩ : syracuseStep 6089579 = 9134369) B9134369
theorem B1141627 : Blo 591290 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B18542479 : Blo 591290 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B4813303 : Blo 591290 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B2257577 : Blo 591290 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B6420545 : Blo 591290 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B752095 : Blo 591290 752095 := bstep (se 1 (by rfl) ⟨564071, by rfl⟩ : syracuseStep 752095 = 1128143) B1128143
theorem B949033 : Blo 591290 949033 := bstep (se 2 (by rfl) ⟨355887, by rfl⟩ : syracuseStep 949033 = 711775) B711775
theorem B2259839 : Blo 591290 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B1997783 : Blo 591290 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B3800459 : Blo 591290 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B14384719 : Blo 591290 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B16220371 : Blo 591290 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B11371853 : Blo 591290 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B591335 : Blo 591290 591335 := bstep (se 1 (by rfl) ⟨443501, by rfl⟩ : syracuseStep 591335 = 887003) B887003
theorem B29329249 : Blo 591290 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B591719 : Blo 591290 591719 := bstep (se 1 (by rfl) ⟨443789, by rfl⟩ : syracuseStep 591719 = 887579) B887579
theorem B591775 : Blo 591290 591775 := bstep (se 1 (by rfl) ⟨443831, by rfl⟩ : syracuseStep 591775 = 887663) B887663
theorem B591975 : Blo 591290 591975 := bstep (se 1 (by rfl) ⟨443981, by rfl⟩ : syracuseStep 591975 = 887963) B887963
theorem B591983 : Blo 591290 591983 := bstep (se 1 (by rfl) ⟨443987, by rfl⟩ : syracuseStep 591983 = 887975) B887975
theorem B2001023 : Blo 591290 2001023 := bstep (se 1 (by rfl) ⟨1500767, by rfl⟩ : syracuseStep 2001023 = 3001535) B3001535
theorem B887195 : Blo 591290 887195 := bstep (se 1 (by rfl) ⟨665396, by rfl⟩ : syracuseStep 887195 = 1330793) B1330793
theorem B887273 : Blo 591290 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B592367 : Blo 591290 592367 := bstep (se 1 (by rfl) ⟨444275, by rfl⟩ : syracuseStep 592367 = 888551) B888551
theorem B592539 : Blo 591290 592539 := bstep (se 1 (by rfl) ⟨444404, by rfl⟩ : syracuseStep 592539 = 888809) B888809
theorem B592575 : Blo 591290 592575 := bstep (se 1 (by rfl) ⟨444431, by rfl⟩ : syracuseStep 592575 = 888863) B888863
theorem B592879 : Blo 591290 592879 := bstep (se 1 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 592879 = 889319) B889319
theorem B593439 : Blo 591290 593439 := bstep (se 1 (by rfl) ⟨445079, by rfl⟩ : syracuseStep 593439 = 890159) B890159
theorem B888431 : Blo 591290 888431 := bstep (se 1 (by rfl) ⟨666323, by rfl⟩ : syracuseStep 888431 = 1332647) B1332647
theorem B888503 : Blo 591290 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B594031 : Blo 591290 594031 := bstep (se 1 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 594031 = 891047) B891047
theorem B1905383 : Blo 591290 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B889631 : Blo 591290 889631 := bstep (se 1 (by rfl) ⟨667223, by rfl⟩ : syracuseStep 889631 = 1334447) B1334447
theorem B594943 : Blo 591290 594943 := bstep (se 1 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 594943 = 892415) B892415
theorem B7607479 : Blo 591290 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B2856383 : Blo 591290 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B890399 : Blo 591290 890399 := bstep (se 1 (by rfl) ⟨667799, by rfl⟩ : syracuseStep 890399 = 1335599) B1335599
theorem B890951 : Blo 591290 890951 := bstep (se 1 (by rfl) ⟨668213, by rfl⟩ : syracuseStep 890951 = 1336427) B1336427
theorem B2529575 : Blo 591290 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B5413979 : Blo 591290 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B3808559 : Blo 591290 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B2564455 : Blo 591290 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B10134557 : Blo 591290 10134557 := bstep (se 3 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 10134557 = 3800459) B3800459
theorem B1123807 : Blo 591290 1123807 := bstep (se 1 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 1123807 = 1685711) B1685711
theorem B19179625 : Blo 591290 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B38381849 : Blo 591290 38381849 := bstep (se 2 (by rfl) ⟨14393193, by rfl⟩ : syracuseStep 38381849 = 28786387) B28786387
theorem B43821739 : Blo 591290 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B12823271 : Blo 591290 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B1518617 : Blo 591290 1518617 := bstep (se 2 (by rfl) ⟨569481, by rfl⟩ : syracuseStep 1518617 = 1138963) B1138963
theorem B666715 : Blo 591290 666715 := bstep (se 1 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 666715 = 1000073) B1000073
theorem B667291 : Blo 591290 667291 := bstep (se 1 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 667291 = 1000937) B1000937
theorem B4501817 : Blo 591290 4501817 := bstep (se 2 (by rfl) ⟨1688181, by rfl⟩ : syracuseStep 4501817 = 3376363) B3376363
theorem B635375 : Blo 591290 635375 := bstep (se 1 (by rfl) ⟨476531, by rfl⟩ : syracuseStep 635375 = 953063) B953063
theorem B10859345 : Blo 591290 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B668839 : Blo 591290 668839 := bstep (se 1 (by rfl) ⟨501629, by rfl⟩ : syracuseStep 668839 = 1003259) B1003259
theorem B1357127 : Blo 591290 1357127 := bstep (se 1 (by rfl) ⟨1017845, by rfl⟩ : syracuseStep 1357127 = 2035691) B2035691
theorem B2995703 : Blo 591290 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B964327 : Blo 591290 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B1522169 : Blo 591290 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B998507 : Blo 591290 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B1129639 : Blo 591290 1129639 := bstep (se 1 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 1129639 = 1694459) B1694459
theorem B5422879 : Blo 591290 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B24723305 : Blo 591290 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B1425289 : Blo 591290 1425289 := bstep (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) B1068967
theorem B803039 : Blo 591290 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B2703743 : Blo 591290 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B2998943 : Blo 591290 2998943 := bstep (se 1 (by rfl) ⟨2249207, by rfl⟩ : syracuseStep 2998943 = 4498415) B4498415
theorem B4507163 : Blo 591290 4507163 := bstep (se 1 (by rfl) ⟨3380372, by rfl⟩ : syracuseStep 4507163 = 6760745) B6760745
theorem B2541415 : Blo 591290 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B1002793 : Blo 591290 1002793 := bstep (se 2 (by rfl) ⟨376047, by rfl⟩ : syracuseStep 1002793 = 752095) B752095
theorem B904495 : Blo 591290 904495 := bstep (se 1 (by rfl) ⟨678371, by rfl⟩ : syracuseStep 904495 = 1356743) B1356743
theorem B1265377 : Blo 591290 1265377 := bstep (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) B949033
theorem B4280363 : Blo 591290 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B1331513 : Blo 591290 1331513 := bstep (se 2 (by rfl) ⟨499317, by rfl⟩ : syracuseStep 1331513 = 998635) B998635
theorem B1331855 : Blo 591290 1331855 := bstep (se 1 (by rfl) ⟨998891, by rfl⟩ : syracuseStep 1331855 = 1997783) B1997783
theorem B10016939 : Blo 591290 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1333583 : Blo 591290 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B1071835 : Blo 591290 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B9755387 : Blo 591290 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B9591635 : Blo 591290 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B1334267 : Blo 591290 1334267 := bstep (se 1 (by rfl) ⟨1000700, by rfl⟩ : syracuseStep 1334267 = 2001401) B2001401
theorem B1203431 : Blo 591290 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1695131 : Blo 591290 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B1335131 : Blo 591290 1335131 := bstep (se 1 (by rfl) ⟨1001348, by rfl⟩ : syracuseStep 1335131 = 2002697) B2002697
theorem B19259815 : Blo 591290 19259815 := bstep (se 1 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 19259815 = 28889723) B28889723
theorem B4809179 : Blo 591290 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B2254007 : Blo 591290 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B1336679 : Blo 591290 1336679 := bstep (se 1 (by rfl) ⟨1002509, by rfl⟩ : syracuseStep 1336679 = 2005019) B2005019
theorem B1337039 : Blo 591290 1337039 := bstep (se 1 (by rfl) ⟨1002779, by rfl⟩ : syracuseStep 1337039 = 2005559) B2005559
theorem B24307721 : Blo 591290 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B2844809 : Blo 591290 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B6417737 : Blo 591290 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B5696999 : Blo 591290 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B749083 : Blo 591290 749083 := bstep (se 1 (by rfl) ⟨561812, by rfl⟩ : syracuseStep 749083 = 1123625) B1123625
theorem B1338911 : Blo 591290 1338911 := bstep (se 1 (by rfl) ⟨1004183, by rfl⟩ : syracuseStep 1338911 = 2008367) B2008367
theorem B51867371 : Blo 591290 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B4059719 : Blo 591290 4059719 := bstep (se 1 (by rfl) ⟨3044789, by rfl⟩ : syracuseStep 4059719 = 6089579) B6089579
theorem B3371807 : Blo 591290 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B1995731 : Blo 591290 1995731 := bstep (se 1 (by rfl) ⟨1496798, by rfl⟩ : syracuseStep 1995731 = 2993597) B2993597
theorem B9270605 : Blo 591290 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B1505051 : Blo 591290 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B5077667 : Blo 591290 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B1506377 : Blo 591290 1506377 := bstep (se 2 (by rfl) ⟨564891, by rfl⟩ : syracuseStep 1506377 = 1129783) B1129783
theorem B1506559 : Blo 591290 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B1605473 : Blo 591290 1605473 := bstep (se 2 (by rfl) ⟨602052, by rfl⟩ : syracuseStep 1605473 = 1204105) B1204105
theorem B1802495 : Blo 591290 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B21627161 : Blo 591290 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B1999295 : Blo 591290 1999295 := bstep (se 1 (by rfl) ⟨1499471, by rfl⟩ : syracuseStep 1999295 = 2998943) B2998943
theorem B591463 : Blo 591290 591463 := bstep (se 1 (by rfl) ⟨443597, by rfl⟩ : syracuseStep 591463 = 887195) B887195
theorem B591515 : Blo 591290 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B592287 : Blo 591290 592287 := bstep (se 1 (by rfl) ⟨444215, by rfl⟩ : syracuseStep 592287 = 888431) B888431
theorem B592335 : Blo 591290 592335 := bstep (se 1 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 592335 = 888503) B888503
theorem B2853575 : Blo 591290 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B887675 : Blo 591290 887675 := bstep (se 1 (by rfl) ⟨665756, by rfl⟩ : syracuseStep 887675 = 1331513) B1331513
theorem B887903 : Blo 591290 887903 := bstep (se 1 (by rfl) ⟨665927, by rfl⟩ : syracuseStep 887903 = 1331855) B1331855
theorem B593087 : Blo 591290 593087 := bstep (se 1 (by rfl) ⟨444815, by rfl⟩ : syracuseStep 593087 = 889631) B889631
theorem B58428985 : Blo 591290 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B1904255 : Blo 591290 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B593599 : Blo 591290 593599 := bstep (se 1 (by rfl) ⟨445199, by rfl⟩ : syracuseStep 593599 = 890399) B890399
theorem B593967 : Blo 591290 593967 := bstep (se 1 (by rfl) ⟨445475, by rfl⟩ : syracuseStep 593967 = 890951) B890951
theorem B888953 : Blo 591290 888953 := bstep (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) B666715
theorem B889055 : Blo 591290 889055 := bstep (se 1 (by rfl) ⟨666791, by rfl⟩ : syracuseStep 889055 = 1333583) B1333583
theorem B6394423 : Blo 591290 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B889511 : Blo 591290 889511 := bstep (se 1 (by rfl) ⟨667133, by rfl⟩ : syracuseStep 889511 = 1334267) B1334267
theorem B889721 : Blo 591290 889721 := bstep (se 2 (by rfl) ⟨333645, by rfl⟩ : syracuseStep 889721 = 667291) B667291
theorem B890087 : Blo 591290 890087 := bstep (se 1 (by rfl) ⟨667565, by rfl⟩ : syracuseStep 890087 = 1335131) B1335131
theorem B6756371 : Blo 591290 6756371 := bstep (se 1 (by rfl) ⟨5067278, by rfl⟩ : syracuseStep 6756371 = 10134557) B10134557
theorem B891119 : Blo 591290 891119 := bstep (se 1 (by rfl) ⟨668339, by rfl⟩ : syracuseStep 891119 = 1336679) B1336679
theorem B891359 : Blo 591290 891359 := bstep (se 1 (by rfl) ⟨668519, by rfl⟩ : syracuseStep 891359 = 1337039) B1337039
theorem B891785 : Blo 591290 891785 := bstep (se 2 (by rfl) ⟨334419, by rfl⟩ : syracuseStep 891785 = 668839) B668839
theorem B1285769 : Blo 591290 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B892607 : Blo 591290 892607 := bstep (se 1 (by rfl) ⟨669455, by rfl⟩ : syracuseStep 892607 = 1338911) B1338911
theorem B34578247 : Blo 591290 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B2008745 : Blo 591290 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B3385111 : Blo 591290 3385111 := bstep (se 1 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 3385111 = 5077667) B5077667
theorem B665671 : Blo 591290 665671 := bstep (se 1 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 665671 = 998507) B998507
theorem B3419273 : Blo 591290 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B7581235 : Blo 591290 7581235 := bstep (se 1 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 7581235 = 11371853) B11371853
theorem B12824477 : Blo 591290 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B8565749 : Blo 591290 8565749 := bstep (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) B803039
theorem B39105665 : Blo 591290 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B3388553 : Blo 591290 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B25572833 : Blo 591290 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B5716453 : Blo 591290 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B1686383 : Blo 591290 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B6503591 : Blo 591290 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B998777 : Blo 591290 998777 := bstep (se 2 (by rfl) ⟨374541, by rfl⟩ : syracuseStep 998777 = 749083) B749083
theorem B2539039 : Blo 591290 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B1130087 : Blo 591290 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1687169 : Blo 591290 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B16205147 : Blo 591290 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B10143305 : Blo 591290 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B4278491 : Blo 591290 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B3001211 : Blo 591290 3001211 := bstep (se 1 (by rfl) ⟨2250908, by rfl⟩ : syracuseStep 3001211 = 4501817) B4501817
theorem B14437277 : Blo 591290 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B2706479 : Blo 591290 2706479 := bstep (se 1 (by rfl) ⟨2029859, by rfl⟩ : syracuseStep 2706479 = 4059719) B4059719
theorem B2247871 : Blo 591290 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B1330487 : Blo 591290 1330487 := bstep (se 1 (by rfl) ⟨997865, by rfl⟩ : syracuseStep 1330487 = 1995731) B1995731
theorem B904751 : Blo 591290 904751 := bstep (se 1 (by rfl) ⟨678563, by rfl⟩ : syracuseStep 904751 = 1357127) B1357127
theorem B6180403 : Blo 591290 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B1003367 : Blo 591290 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B1004251 : Blo 591290 1004251 := bstep (se 1 (by rfl) ⟨753188, by rfl⟩ : syracuseStep 1004251 = 1506377) B1506377
theorem B7230505 : Blo 591290 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1070315 : Blo 591290 1070315 := bstep (se 1 (by rfl) ⟨802736, by rfl⟩ : syracuseStep 1070315 = 1605473) B1605473
theorem B25679753 : Blo 591290 25679753 := bstep (se 2 (by rfl) ⟨9629907, by rfl⟩ : syracuseStep 25679753 = 19259815) B19259815
theorem B3004775 : Blo 591290 3004775 := bstep (se 1 (by rfl) ⟨2253581, by rfl⟩ : syracuseStep 3004775 = 4507163) B4507163
theorem B1694333 : Blo 591290 1694333 := bstep (se 3 (by rfl) ⟨317687, by rfl⟩ : syracuseStep 1694333 = 635375) B635375
theorem B1334015 : Blo 591290 1334015 := bstep (se 1 (by rfl) ⟨1000511, by rfl⟩ : syracuseStep 1334015 = 2001023) B2001023
theorem B1498409 : Blo 591290 1498409 := bstep (se 2 (by rfl) ⟨561903, by rfl⟩ : syracuseStep 1498409 = 1123807) B1123807
theorem B1270255 : Blo 591290 1270255 := bstep (se 1 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 1270255 = 1905383) B1905383
theorem B6677959 : Blo 591290 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B1337057 : Blo 591290 1337057 := bstep (se 2 (by rfl) ⟨501396, by rfl⟩ : syracuseStep 1337057 = 1002793) B1002793
theorem B1205993 : Blo 591290 1205993 := bstep (se 2 (by rfl) ⟨452247, by rfl⟩ : syracuseStep 1205993 = 904495) B904495
theorem B1502671 : Blo 591290 1502671 := bstep (se 1 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 1502671 = 2254007) B2254007
theorem B1896539 : Blo 591290 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B25587899 : Blo 591290 25587899 := bstep (se 1 (by rfl) ⟨19190924, by rfl⟩ : syracuseStep 25587899 = 38381849) B38381849
theorem B8548847 : Blo 591290 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B1012411 : Blo 591290 1012411 := bstep (se 1 (by rfl) ⟨759308, by rfl⟩ : syracuseStep 1012411 = 1518617) B1518617
theorem B3797999 : Blo 591290 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B7239563 : Blo 591290 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B3209149 : Blo 591290 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B1997135 : Blo 591290 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B1506185 : Blo 591290 1506185 := bstep (se 2 (by rfl) ⟨564819, by rfl⟩ : syracuseStep 1506185 = 1129639) B1129639
theorem B1014779 : Blo 591290 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B1900385 : Blo 591290 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B16482203 : Blo 591290 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B14418107 : Blo 591290 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B2852327 : Blo 591290 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B1902383 : Blo 591290 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B591783 : Blo 591290 591783 := bstep (se 1 (by rfl) ⟨443837, by rfl⟩ : syracuseStep 591783 = 887675) B887675
theorem B2000807 : Blo 591290 2000807 := bstep (se 1 (by rfl) ⟨1500605, by rfl⟩ : syracuseStep 2000807 = 3001211) B3001211
theorem B1804319 : Blo 591290 1804319 := bstep (se 1 (by rfl) ⟨1353239, by rfl⟩ : syracuseStep 1804319 = 2706479) B2706479
theorem B591935 : Blo 591290 591935 := bstep (se 1 (by rfl) ⟨443951, by rfl⟩ : syracuseStep 591935 = 887903) B887903
theorem B886991 : Blo 591290 886991 := bstep (se 1 (by rfl) ⟨665243, by rfl⟩ : syracuseStep 886991 = 1330487) B1330487
theorem B592635 : Blo 591290 592635 := bstep (se 1 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 592635 = 888953) B888953
theorem B887561 : Blo 591290 887561 := bstep (se 2 (by rfl) ⟨332835, by rfl⟩ : syracuseStep 887561 = 665671) B665671
theorem B592703 : Blo 591290 592703 := bstep (se 1 (by rfl) ⟨444527, by rfl⟩ : syracuseStep 592703 = 889055) B889055
theorem B593007 : Blo 591290 593007 := bstep (se 1 (by rfl) ⟨444755, by rfl⟩ : syracuseStep 593007 = 889511) B889511
theorem B593147 : Blo 591290 593147 := bstep (se 1 (by rfl) ⟨444860, by rfl⟩ : syracuseStep 593147 = 889721) B889721
theorem B593391 : Blo 591290 593391 := bstep (se 1 (by rfl) ⟨445043, by rfl⟩ : syracuseStep 593391 = 890087) B890087
theorem B594079 : Blo 591290 594079 := bstep (se 1 (by rfl) ⟨445559, by rfl⟩ : syracuseStep 594079 = 891119) B891119
theorem B2003183 : Blo 591290 2003183 := bstep (se 1 (by rfl) ⟨1502387, by rfl⟩ : syracuseStep 2003183 = 3004775) B3004775
theorem B594239 : Blo 591290 594239 := bstep (se 1 (by rfl) ⟨445679, by rfl⟩ : syracuseStep 594239 = 891359) B891359
theorem B889343 : Blo 591290 889343 := bstep (se 1 (by rfl) ⟨667007, by rfl⟩ : syracuseStep 889343 = 1334015) B1334015
theorem B594523 : Blo 591290 594523 := bstep (se 1 (by rfl) ⟨445892, by rfl⟩ : syracuseStep 594523 = 891785) B891785
theorem B2003561 : Blo 591290 2003561 := bstep (se 2 (by rfl) ⟨751335, by rfl⟩ : syracuseStep 2003561 = 1502671) B1502671
theorem B857179 : Blo 591290 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B595071 : Blo 591290 595071 := bstep (se 1 (by rfl) ⟨446303, by rfl⟩ : syracuseStep 595071 = 892607) B892607
theorem B8525897 : Blo 591290 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1349881 : Blo 591290 1349881 := bstep (se 2 (by rfl) ⟨506205, by rfl⟩ : syracuseStep 1349881 = 1012411) B1012411
theorem B891371 : Blo 591290 891371 := bstep (se 1 (by rfl) ⟨668528, by rfl⟩ : syracuseStep 891371 = 1337057) B1337057
theorem B9640673 : Blo 591290 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B17342909 : Blo 591290 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B2531999 : Blo 591290 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B5710499 : Blo 591290 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B17048555 : Blo 591290 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B4826375 : Blo 591290 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B1124255 : Blo 591290 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B3385385 : Blo 591290 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B665851 : Blo 591290 665851 := bstep (se 1 (by rfl) ⟨499388, by rfl⟩ : syracuseStep 665851 = 998777) B998777
theorem B1124779 : Blo 591290 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B10988135 : Blo 591290 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B5057437 : Blo 591290 5057437 := bstep (se 3 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 5057437 = 1896539) B1896539
theorem B6762203 : Blo 591290 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B603167 : Blo 591290 603167 := bstep (se 1 (by rfl) ⟨452375, by rfl⟩ : syracuseStep 603167 = 904751) B904751
theorem B668911 : Blo 591290 668911 := bstep (se 1 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 668911 = 1003367) B1003367
theorem B17119835 : Blo 591290 17119835 := bstep (se 1 (by rfl) ⟨12839876, by rfl⟩ : syracuseStep 17119835 = 25679753) B25679753
theorem B4504247 : Blo 591290 4504247 := bstep (se 1 (by rfl) ⟨3378185, by rfl⟩ : syracuseStep 4504247 = 6756371) B6756371
theorem B2997161 : Blo 591290 2997161 := bstep (se 2 (by rfl) ⟨1123935, by rfl⟩ : syracuseStep 2997161 = 2247871) B2247871
theorem B1129555 : Blo 591290 1129555 := bstep (se 1 (by rfl) ⟨847166, by rfl⟩ : syracuseStep 1129555 = 1694333) B1694333
theorem B10108313 : Blo 591290 10108313 := bstep (se 2 (by rfl) ⟨3790617, by rfl⟩ : syracuseStep 10108313 = 7581235) B7581235
theorem B8240537 : Blo 591290 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B77905313 : Blo 591290 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B998939 : Blo 591290 998939 := bstep (se 1 (by rfl) ⟨749204, by rfl⟩ : syracuseStep 998939 = 1498409) B1498409
theorem B803995 : Blo 591290 803995 := bstep (se 1 (by rfl) ⟨602996, by rfl⟩ : syracuseStep 803995 = 1205993) B1205993
theorem B2279515 : Blo 591290 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B4278865 : Blo 591290 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B2706077 : Blo 591290 2706077 := bstep (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) B1014779
theorem B17058599 : Blo 591290 17058599 := bstep (se 1 (by rfl) ⟨12793949, by rfl⟩ : syracuseStep 17058599 = 25587899) B25587899
theorem B7621937 : Blo 591290 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B26070443 : Blo 591290 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B1331423 : Blo 591290 1331423 := bstep (se 1 (by rfl) ⟨998567, by rfl⟩ : syracuseStep 1331423 = 1997135) B1997135
theorem B1004123 : Blo 591290 1004123 := bstep (se 1 (by rfl) ⟨753092, by rfl⟩ : syracuseStep 1004123 = 1506185) B1506185
theorem B1266923 : Blo 591290 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B1201663 : Blo 591290 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B1332863 : Blo 591290 1332863 := bstep (se 1 (by rfl) ⟨999647, by rfl⟩ : syracuseStep 1332863 = 1999295) B1999295
theorem B1693673 : Blo 591290 1693673 := bstep (se 2 (by rfl) ⟨635127, by rfl⟩ : syracuseStep 1693673 = 1270255) B1270255
theorem B10803431 : Blo 591290 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B8903945 : Blo 591290 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B9624851 : Blo 591290 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B4513481 : Blo 591290 4513481 := bstep (se 2 (by rfl) ⟨1692555, by rfl⟩ : syracuseStep 4513481 = 3385111) B3385111
theorem B1269503 : Blo 591290 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B713543 : Blo 591290 713543 := bstep (se 1 (by rfl) ⟨535157, by rfl⟩ : syracuseStep 713543 = 1070315) B1070315
theorem B1339001 : Blo 591290 1339001 := bstep (se 2 (by rfl) ⟨502125, by rfl⟩ : syracuseStep 1339001 = 1004251) B1004251
theorem B1339163 : Blo 591290 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B8549651 : Blo 591290 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B5699231 : Blo 591290 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B2259035 : Blo 591290 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B753391 : Blo 591290 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B46104329 : Blo 591290 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B1901551 : Blo 591290 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B591327 : Blo 591290 591327 := bstep (se 1 (by rfl) ⟨443495, by rfl⟩ : syracuseStep 591327 = 886991) B886991
theorem B6751997 : Blo 591290 6751997 := bstep (se 3 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 6751997 = 2531999) B2531999
theorem B1804051 : Blo 591290 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B591707 : Blo 591290 591707 := bstep (se 1 (by rfl) ⟨443780, by rfl⟩ : syracuseStep 591707 = 887561) B887561
theorem B11372399 : Blo 591290 11372399 := bstep (se 1 (by rfl) ⟨8529299, by rfl⟩ : syracuseStep 11372399 = 17058599) B17058599
theorem B1902781 : Blo 591290 1902781 := bstep (se 3 (by rfl) ⟨356771, by rfl⟩ : syracuseStep 1902781 = 713543) B713543
theorem B5081291 : Blo 591290 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B1608445 : Blo 591290 1608445 := bstep (se 3 (by rfl) ⟨301583, by rfl⟩ : syracuseStep 1608445 = 603167) B603167
theorem B887615 : Blo 591290 887615 := bstep (se 1 (by rfl) ⟨665711, by rfl⟩ : syracuseStep 887615 = 1331423) B1331423
theorem B887801 : Blo 591290 887801 := bstep (se 2 (by rfl) ⟨332925, by rfl⟩ : syracuseStep 887801 = 665851) B665851
theorem B592895 : Blo 591290 592895 := bstep (se 1 (by rfl) ⟨444671, by rfl⟩ : syracuseStep 592895 = 889343) B889343
theorem B5705153 : Blo 591290 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B888575 : Blo 591290 888575 := bstep (se 1 (by rfl) ⟨666431, by rfl⟩ : syracuseStep 888575 = 1332863) B1332863
theorem B594247 : Blo 591290 594247 := bstep (se 1 (by rfl) ⟨445685, by rfl⟩ : syracuseStep 594247 = 891371) B891371
theorem B6427115 : Blo 591290 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B5935963 : Blo 591290 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B3806999 : Blo 591290 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B3217583 : Blo 591290 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B891881 : Blo 591290 891881 := bstep (se 2 (by rfl) ⟨334455, by rfl⟩ : syracuseStep 891881 = 668911) B668911
theorem B892667 : Blo 591290 892667 := bstep (se 1 (by rfl) ⟨669500, by rfl⟩ : syracuseStep 892667 = 1339001) B1339001
theorem B892775 : Blo 591290 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B11413223 : Blo 591290 11413223 := bstep (se 1 (by rfl) ⟨8559917, by rfl⟩ : syracuseStep 11413223 = 17119835) B17119835
theorem B665959 : Blo 591290 665959 := bstep (se 1 (by rfl) ⟨499469, by rfl⟩ : syracuseStep 665959 = 998939) B998939
theorem B9612071 : Blo 591290 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B17380295 : Blo 591290 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B669415 : Blo 591290 669415 := bstep (se 1 (by rfl) ⟨502061, by rfl⟩ : syracuseStep 669415 = 1004123) B1004123
theorem B1129115 : Blo 591290 1129115 := bstep (se 1 (by rfl) ⟨846836, by rfl⟩ : syracuseStep 1129115 = 1693673) B1693673
theorem B5683931 : Blo 591290 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B7325423 : Blo 591290 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B4508135 : Blo 591290 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B3002831 : Blo 591290 3002831 := bstep (se 1 (by rfl) ⟨2252123, by rfl⟩ : syracuseStep 3002831 = 4504247) B4504247
theorem B6738875 : Blo 591290 6738875 := bstep (se 1 (by rfl) ⟨5054156, by rfl⟩ : syracuseStep 6738875 = 10108313) B10108313
theorem B5493691 : Blo 591290 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B1004521 : Blo 591290 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B1268255 : Blo 591290 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B1333871 : Blo 591290 1333871 := bstep (se 1 (by rfl) ⟨1000403, by rfl⟩ : syracuseStep 1333871 = 2000807) B2000807
theorem B7199365 : Blo 591290 7199365 := bstep (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) B1349881
theorem B1202879 : Blo 591290 1202879 := bstep (se 1 (by rfl) ⟨902159, by rfl⟩ : syracuseStep 1202879 = 1804319) B1804319
theorem B3039353 : Blo 591290 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B1335455 : Blo 591290 1335455 := bstep (se 1 (by rfl) ⟨1001591, by rfl⟩ : syracuseStep 1335455 = 2003183) B2003183
theorem B1335707 : Blo 591290 1335707 := bstep (se 1 (by rfl) ⟨1001780, by rfl⟩ : syracuseStep 1335707 = 2003561) B2003561
theorem B1499705 : Blo 591290 1499705 := bstep (se 2 (by rfl) ⟨562389, by rfl⟩ : syracuseStep 1499705 = 1124779) B1124779
theorem B844615 : Blo 591290 844615 := bstep (se 1 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 844615 = 1266923) B1266923
theorem B6743249 : Blo 591290 6743249 := bstep (se 2 (by rfl) ⟨2528718, by rfl⟩ : syracuseStep 6743249 = 5057437) B5057437
theorem B7202287 : Blo 591290 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B6416567 : Blo 591290 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B3008987 : Blo 591290 3008987 := bstep (se 1 (by rfl) ⟨2256740, by rfl⟩ : syracuseStep 3008987 = 4513481) B4513481
theorem B846335 : Blo 591290 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B11561939 : Blo 591290 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B11365703 : Blo 591290 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B4287973 : Blo 591290 4287973 := bstep (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) B803995
theorem B749503 : Blo 591290 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B2256923 : Blo 591290 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B1142905 : Blo 591290 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1602217 : Blo 591290 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B5699767 : Blo 591290 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B3799487 : Blo 591290 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B1506023 : Blo 591290 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B1506073 : Blo 591290 1506073 := bstep (se 2 (by rfl) ⟨564777, by rfl⟩ : syracuseStep 1506073 = 1129555) B1129555
theorem B1998107 : Blo 591290 1998107 := bstep (se 1 (by rfl) ⟨1498580, by rfl⟩ : syracuseStep 1998107 = 2997161) B2997161
theorem B51936875 : Blo 591290 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B30736219 : Blo 591290 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B4883615 : Blo 591290 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B591743 : Blo 591290 591743 := bstep (se 1 (by rfl) ⟨443807, by rfl⟩ : syracuseStep 591743 = 887615) B887615
theorem B9603049 : Blo 591290 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B591867 : Blo 591290 591867 := bstep (se 1 (by rfl) ⟨443900, by rfl⟩ : syracuseStep 591867 = 887801) B887801
theorem B3803435 : Blo 591290 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B592383 : Blo 591290 592383 := bstep (se 1 (by rfl) ⟨444287, by rfl⟩ : syracuseStep 592383 = 888575) B888575
theorem B2001887 : Blo 591290 2001887 := bstep (se 1 (by rfl) ⟨1501415, by rfl⟩ : syracuseStep 2001887 = 3002831) B3002831
theorem B887945 : Blo 591290 887945 := bstep (se 2 (by rfl) ⟨332979, by rfl⟩ : syracuseStep 887945 = 665959) B665959
theorem B4492583 : Blo 591290 4492583 := bstep (se 1 (by rfl) ⟨3369437, by rfl⟩ : syracuseStep 4492583 = 6738875) B6738875
theorem B889247 : Blo 591290 889247 := bstep (se 1 (by rfl) ⟨666935, by rfl⟩ : syracuseStep 889247 = 1333871) B1333871
theorem B594587 : Blo 591290 594587 := bstep (se 1 (by rfl) ⟨445940, by rfl⟩ : syracuseStep 594587 = 891881) B891881
theorem B595111 : Blo 591290 595111 := bstep (se 1 (by rfl) ⟨446333, by rfl⟩ : syracuseStep 595111 = 892667) B892667
theorem B595183 : Blo 591290 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B890303 : Blo 591290 890303 := bstep (se 1 (by rfl) ⟨667727, by rfl⟩ : syracuseStep 890303 = 1335455) B1335455
theorem B890471 : Blo 591290 890471 := bstep (se 1 (by rfl) ⟨667853, by rfl⟩ : syracuseStep 890471 = 1335707) B1335707
theorem B4495499 : Blo 591290 4495499 := bstep (se 1 (by rfl) ⟨3371624, by rfl⟩ : syracuseStep 4495499 = 6743249) B6743249
theorem B2136289 : Blo 591290 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B7608815 : Blo 591290 7608815 := bstep (se 1 (by rfl) ⟨5706611, by rfl⟩ : syracuseStep 7608815 = 11413223) B11413223
theorem B3382013 : Blo 591290 3382013 := bstep (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) B1268255
theorem B2005991 : Blo 591290 2005991 := bstep (se 1 (by rfl) ⟨1504493, by rfl⟩ : syracuseStep 2005991 = 3008987) B3008987
theorem B7707959 : Blo 591290 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B7577135 : Blo 591290 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B892553 : Blo 591290 892553 := bstep (se 2 (by rfl) ⟨334707, by rfl⟩ : syracuseStep 892553 = 669415) B669415
theorem B2008097 : Blo 591290 2008097 := bstep (se 2 (by rfl) ⟨753036, by rfl⟩ : syracuseStep 2008097 = 1506073) B1506073
theorem B2532991 : Blo 591290 2532991 := bstep (se 1 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 2532991 = 3799487) B3799487
theorem B1126153 : Blo 591290 1126153 := bstep (se 2 (by rfl) ⟨422307, by rfl⟩ : syracuseStep 1126153 = 844615) B844615
theorem B4501331 : Blo 591290 4501331 := bstep (se 1 (by rfl) ⟨3375998, by rfl⟩ : syracuseStep 4501331 = 6751997) B6751997
theorem B7581599 : Blo 591290 7581599 := bstep (se 1 (by rfl) ⟨5686199, by rfl⟩ : syracuseStep 7581599 = 11372399) B11372399
theorem B2535401 : Blo 591290 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B3387527 : Blo 591290 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B2537041 : Blo 591290 2537041 := bstep (se 2 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 2537041 = 1902781) B1902781
theorem B2144593 : Blo 591290 2144593 := bstep (se 2 (by rfl) ⟨804222, by rfl⟩ : syracuseStep 2144593 = 1608445) B1608445
theorem B2537999 : Blo 591290 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B2145055 : Blo 591290 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B801919 : Blo 591290 801919 := bstep (se 1 (by rfl) ⟨601439, by rfl⟩ : syracuseStep 801919 = 1202879) B1202879
theorem B5717297 : Blo 591290 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B999337 : Blo 591290 999337 := bstep (se 2 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 999337 = 749503) B749503
theorem B1523873 : Blo 591290 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B999803 : Blo 591290 999803 := bstep (se 1 (by rfl) ⟨749852, by rfl⟩ : syracuseStep 999803 = 1499705) B1499705
theorem B7914617 : Blo 591290 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B7324921 : Blo 591290 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B4277711 : Blo 591290 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B6408047 : Blo 591290 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B11586863 : Blo 591290 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B9621605 : Blo 591290 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B3789287 : Blo 591290 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B1004015 : Blo 591290 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B1332071 : Blo 591290 1332071 := bstep (se 1 (by rfl) ⟨999053, by rfl⟩ : syracuseStep 1332071 = 1998107) B1998107
theorem B34624583 : Blo 591290 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B40981625 : Blo 591290 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B3005423 : Blo 591290 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B4284743 : Blo 591290 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B2026235 : Blo 591290 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B1339361 : Blo 591290 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B2256893 : Blo 591290 2256893 := bstep (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) B846335
theorem B1504615 : Blo 591290 1504615 := bstep (se 1 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 1504615 = 2256923) B2256923
theorem B7599689 : Blo 591290 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B9599153 : Blo 591290 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B752743 : Blo 591290 752743 := bstep (se 1 (by rfl) ⟨564557, by rfl⟩ : syracuseStep 752743 = 1129115) B1129115
theorem B1015915 : Blo 591290 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B5276411 : Blo 591290 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2851807 : Blo 591290 2851807 := bstep (se 1 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 2851807 = 4277711) B4277711
theorem B591963 : Blo 591290 591963 := bstep (se 1 (by rfl) ⟨443972, by rfl⟩ : syracuseStep 591963 = 887945) B887945
theorem B3377321 : Blo 591290 3377321 := bstep (se 2 (by rfl) ⟨1266495, by rfl⟩ : syracuseStep 3377321 = 2532991) B2532991
theorem B592831 : Blo 591290 592831 := bstep (se 1 (by rfl) ⟨444623, by rfl⟩ : syracuseStep 592831 = 889247) B889247
theorem B2526191 : Blo 591290 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B888047 : Blo 591290 888047 := bstep (se 1 (by rfl) ⟨666035, by rfl⟩ : syracuseStep 888047 = 1332071) B1332071
theorem B593535 : Blo 591290 593535 := bstep (se 1 (by rfl) ⟨445151, by rfl⟩ : syracuseStep 593535 = 890303) B890303
theorem B593647 : Blo 591290 593647 := bstep (se 1 (by rfl) ⟨445235, by rfl⟩ : syracuseStep 593647 = 890471) B890471
theorem B2003615 : Blo 591290 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B5051423 : Blo 591290 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B595035 : Blo 591290 595035 := bstep (se 1 (by rfl) ⟨446276, by rfl⟩ : syracuseStep 595035 = 892553) B892553
theorem B25597741 : Blo 591290 25597741 := bstep (se 3 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 25597741 = 9599153) B9599153
theorem B39066245 : Blo 591290 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B2006153 : Blo 591290 2006153 := bstep (se 2 (by rfl) ⟨752307, by rfl⟩ : syracuseStep 2006153 = 1504615) B1504615
theorem B3382721 : Blo 591290 3382721 := bstep (se 2 (by rfl) ⟨1268520, by rfl⟩ : syracuseStep 3382721 = 2537041) B2537041
theorem B5054399 : Blo 591290 5054399 := bstep (se 1 (by rfl) ⟨3790799, by rfl⟩ : syracuseStep 5054399 = 7581599) B7581599
theorem B892907 : Blo 591290 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B2859457 : Blo 591290 2859457 := bstep (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) B2144593
theorem B2860073 : Blo 591290 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B3811531 : Blo 591290 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B666535 : Blo 591290 666535 := bstep (se 1 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 666535 = 999803) B999803
theorem B3255743 : Blo 591290 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B4272031 : Blo 591290 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B2535623 : Blo 591290 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B2995055 : Blo 591290 2995055 := bstep (se 1 (by rfl) ⟨2246291, by rfl⟩ : syracuseStep 2995055 = 4492583) B4492583
theorem B669343 : Blo 591290 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B23083055 : Blo 591290 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B2996999 : Blo 591290 2996999 := bstep (se 1 (by rfl) ⟨2247749, by rfl⟩ : syracuseStep 2996999 = 4495499) B4495499
theorem B4276901 : Blo 591290 4276901 := bstep (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) B801919
theorem B3000887 : Blo 591290 3000887 := bstep (se 1 (by rfl) ⟨2250665, by rfl⟩ : syracuseStep 3000887 = 4501331) B4501331
theorem B1690267 : Blo 591290 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B5066459 : Blo 591290 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B1003657 : Blo 591290 1003657 := bstep (se 2 (by rfl) ⟨376371, by rfl⟩ : syracuseStep 1003657 = 752743) B752743
theorem B1691999 : Blo 591290 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B1332449 : Blo 591290 1332449 := bstep (se 2 (by rfl) ⟨499668, by rfl⟩ : syracuseStep 1332449 = 999337) B999337
theorem B11425981 : Blo 591290 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B1334591 : Blo 591290 1334591 := bstep (se 1 (by rfl) ⟨1000943, by rfl⟩ : syracuseStep 1334591 = 2001887) B2001887
theorem B7724575 : Blo 591290 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B12804065 : Blo 591290 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B6414403 : Blo 591290 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B27321083 : Blo 591290 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B5072543 : Blo 591290 5072543 := bstep (se 1 (by rfl) ⟨3804407, by rfl⟩ : syracuseStep 5072543 = 7608815) B7608815
theorem B2254675 : Blo 591290 2254675 := bstep (se 1 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 2254675 = 3382013) B3382013
theorem B1337327 : Blo 591290 1337327 := bstep (se 1 (by rfl) ⟨1002995, by rfl⟩ : syracuseStep 1337327 = 2005991) B2005991
theorem B5138639 : Blo 591290 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B1501537 : Blo 591290 1501537 := bstep (se 2 (by rfl) ⟨563076, by rfl⟩ : syracuseStep 1501537 = 1126153) B1126153
theorem B1338731 : Blo 591290 1338731 := bstep (se 1 (by rfl) ⟨1004048, by rfl⟩ : syracuseStep 1338731 = 2008097) B2008097
theorem B5403293 : Blo 591290 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B1504595 : Blo 591290 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B2258351 : Blo 591290 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B2848385 : Blo 591290 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B8552537 : Blo 591290 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B3802409 : Blo 591290 3802409 := bstep (se 2 (by rfl) ⟨1425903, by rfl⟩ : syracuseStep 3802409 = 2851807) B2851807
theorem B2000591 : Blo 591290 2000591 := bstep (se 1 (by rfl) ⟨1500443, by rfl⟩ : syracuseStep 2000591 = 3000887) B3000887
theorem B11405069 : Blo 591290 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B592031 : Blo 591290 592031 := bstep (se 1 (by rfl) ⟨444023, by rfl⟩ : syracuseStep 592031 = 888047) B888047
theorem B3377639 : Blo 591290 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B5082041 : Blo 591290 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B2002049 : Blo 591290 2002049 := bstep (se 2 (by rfl) ⟨750768, by rfl⟩ : syracuseStep 2002049 = 1501537) B1501537
theorem B888299 : Blo 591290 888299 := bstep (se 1 (by rfl) ⟨666224, by rfl⟩ : syracuseStep 888299 = 1332449) B1332449
theorem B888713 : Blo 591290 888713 := bstep (se 2 (by rfl) ⟨333267, by rfl⟩ : syracuseStep 888713 = 666535) B666535
theorem B889727 : Blo 591290 889727 := bstep (se 1 (by rfl) ⟨667295, by rfl⟩ : syracuseStep 889727 = 1334591) B1334591
theorem B595271 : Blo 591290 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B1906715 : Blo 591290 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B3381695 : Blo 591290 3381695 := bstep (se 1 (by rfl) ⟨2536271, by rfl⟩ : syracuseStep 3381695 = 5072543) B5072543
theorem B891551 : Blo 591290 891551 := bstep (se 1 (by rfl) ⟨668663, by rfl⟩ : syracuseStep 891551 = 1337327) B1337327
theorem B892457 : Blo 591290 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B892487 : Blo 591290 892487 := bstep (se 1 (by rfl) ⟨669365, by rfl⟩ : syracuseStep 892487 = 1338731) B1338731
theorem B2170495 : Blo 591290 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B10299433 : Blo 591290 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B1354553 : Blo 591290 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B3517607 : Blo 591290 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B3812609 : Blo 591290 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B1684127 : Blo 591290 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B1127999 : Blo 591290 1127999 := bstep (se 1 (by rfl) ⟨845999, by rfl⟩ : syracuseStep 1127999 = 1691999) B1691999
theorem B8536043 : Blo 591290 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B3425759 : Blo 591290 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B34130321 : Blo 591290 34130321 := bstep (se 2 (by rfl) ⟨12798870, by rfl⟩ : syracuseStep 34130321 = 25597741) B25597741
theorem B1690415 : Blo 591290 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B1003063 : Blo 591290 1003063 := bstep (se 1 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 1003063 = 1504595) B1504595
theorem B15388703 : Blo 591290 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B2251547 : Blo 591290 2251547 := bstep (se 1 (by rfl) ⟨1688660, by rfl⟩ : syracuseStep 2251547 = 3377321) B3377321
theorem B3006233 : Blo 591290 3006233 := bstep (se 2 (by rfl) ⟨1127337, by rfl⟩ : syracuseStep 3006233 = 2254675) B2254675
theorem B1335743 : Blo 591290 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B3367615 : Blo 591290 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B2253689 : Blo 591290 2253689 := bstep (se 2 (by rfl) ⟨845133, by rfl⟩ : syracuseStep 2253689 = 1690267) B1690267
theorem B7595693 : Blo 591290 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B26044163 : Blo 591290 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B1337435 : Blo 591290 1337435 := bstep (se 1 (by rfl) ⟨1003076, by rfl⟩ : syracuseStep 1337435 = 2006153) B2006153
theorem B2255147 : Blo 591290 2255147 := bstep (se 1 (by rfl) ⟨1691360, by rfl⟩ : syracuseStep 2255147 = 3382721) B3382721
theorem B5696041 : Blo 591290 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B3369599 : Blo 591290 3369599 := bstep (se 1 (by rfl) ⟨2527199, by rfl⟩ : syracuseStep 3369599 = 5054399) B5054399
theorem B1338209 : Blo 591290 1338209 := bstep (se 2 (by rfl) ⟨501828, by rfl⟩ : syracuseStep 1338209 = 1003657) B1003657
theorem B18214055 : Blo 591290 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B15234641 : Blo 591290 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B3602195 : Blo 591290 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B1996703 : Blo 591290 1996703 := bstep (se 1 (by rfl) ⟨1497527, by rfl⟩ : syracuseStep 1996703 = 2995055) B2995055
theorem B1505567 : Blo 591290 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B1997999 : Blo 591290 1997999 := bstep (se 1 (by rfl) ⟨1498499, by rfl⟩ : syracuseStep 1997999 = 2996999) B2996999
theorem B5701691 : Blo 591290 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B4490153 : Blo 591290 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B7603379 : Blo 591290 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B592199 : Blo 591290 592199 := bstep (se 1 (by rfl) ⟨444149, by rfl⟩ : syracuseStep 592199 = 888299) B888299
theorem B592475 : Blo 591290 592475 := bstep (se 1 (by rfl) ⟨444356, by rfl⟩ : syracuseStep 592475 = 888713) B888713
theorem B10259135 : Blo 591290 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B13732577 : Blo 591290 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B593151 : Blo 591290 593151 := bstep (se 1 (by rfl) ⟨444863, by rfl⟩ : syracuseStep 593151 = 889727) B889727
theorem B594367 : Blo 591290 594367 := bstep (se 1 (by rfl) ⟨445775, by rfl⟩ : syracuseStep 594367 = 891551) B891551
theorem B594971 : Blo 591290 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B594991 : Blo 591290 594991 := bstep (se 1 (by rfl) ⟨446243, by rfl⟩ : syracuseStep 594991 = 892487) B892487
theorem B2004155 : Blo 591290 2004155 := bstep (se 1 (by rfl) ⟨1503116, by rfl⟩ : syracuseStep 2004155 = 3006233) B3006233
theorem B890495 : Blo 591290 890495 := bstep (se 1 (by rfl) ⟨667871, by rfl⟩ : syracuseStep 890495 = 1335743) B1335743
theorem B891623 : Blo 591290 891623 := bstep (se 1 (by rfl) ⟨668717, by rfl⟩ : syracuseStep 891623 = 1337435) B1337435
theorem B892139 : Blo 591290 892139 := bstep (se 1 (by rfl) ⟨669104, by rfl⟩ : syracuseStep 892139 = 1338209) B1338209
theorem B1122751 : Blo 591290 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B11575973 : Blo 591290 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B2401463 : Blo 591290 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B2534939 : Blo 591290 2534939 := bstep (se 1 (by rfl) ⟨1901204, by rfl⟩ : syracuseStep 2534939 = 3802409) B3802409
theorem B22753547 : Blo 591290 22753547 := bstep (se 1 (by rfl) ⟨17065160, by rfl⟩ : syracuseStep 22753547 = 34130321) B34130321
theorem B1126943 : Blo 591290 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B3388027 : Blo 591290 3388027 := bstep (se 1 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 3388027 = 5082041) B5082041
theorem B5063795 : Blo 591290 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B2246399 : Blo 591290 2246399 := bstep (se 1 (by rfl) ⟨1684799, by rfl⟩ : syracuseStep 2246399 = 3369599) B3369599
theorem B903035 : Blo 591290 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B12142703 : Blo 591290 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B2345071 : Blo 591290 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B2541739 : Blo 591290 2541739 := bstep (se 1 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 2541739 = 3812609) B3812609
theorem B1331135 : Blo 591290 1331135 := bstep (se 1 (by rfl) ⟨998351, by rfl⟩ : syracuseStep 1331135 = 1996703) B1996703
theorem B1003711 : Blo 591290 1003711 := bstep (se 1 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 1003711 = 1505567) B1505567
theorem B1331999 : Blo 591290 1331999 := bstep (se 1 (by rfl) ⟨998999, by rfl⟩ : syracuseStep 1331999 = 1997999) B1997999
theorem B5690695 : Blo 591290 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B2283839 : Blo 591290 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B1333727 : Blo 591290 1333727 := bstep (se 1 (by rfl) ⟨1000295, by rfl⟩ : syracuseStep 1333727 = 2000591) B2000591
theorem B2251759 : Blo 591290 2251759 := bstep (se 1 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 2251759 = 3377639) B3377639
theorem B1334699 : Blo 591290 1334699 := bstep (se 1 (by rfl) ⟨1001024, by rfl⟩ : syracuseStep 1334699 = 2002049) B2002049
theorem B7594721 : Blo 591290 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1271143 : Blo 591290 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B2254463 : Blo 591290 2254463 := bstep (se 1 (by rfl) ⟨1690847, by rfl⟩ : syracuseStep 2254463 = 3381695) B3381695
theorem B1501031 : Blo 591290 1501031 := bstep (se 1 (by rfl) ⟨1125773, by rfl⟩ : syracuseStep 1501031 = 2251547) B2251547
theorem B1337417 : Blo 591290 1337417 := bstep (se 2 (by rfl) ⟨501531, by rfl⟩ : syracuseStep 1337417 = 1003063) B1003063
theorem B1502459 : Blo 591290 1502459 := bstep (se 1 (by rfl) ⟨1126844, by rfl⟩ : syracuseStep 1502459 = 2253689) B2253689
theorem B17362775 : Blo 591290 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B1503431 : Blo 591290 1503431 := bstep (se 1 (by rfl) ⟨1127573, by rfl⟩ : syracuseStep 1503431 = 2255147) B2255147
theorem B751999 : Blo 591290 751999 := bstep (se 1 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 751999 = 1127999) B1127999
theorem B10156427 : Blo 591290 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B3801127 : Blo 591290 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B3375863 : Blo 591290 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B8095135 : Blo 591290 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B887423 : Blo 591290 887423 := bstep (se 1 (by rfl) ⟨665567, by rfl⟩ : syracuseStep 887423 = 1331135) B1331135
theorem B887999 : Blo 591290 887999 := bstep (se 1 (by rfl) ⟨665999, by rfl⟩ : syracuseStep 887999 = 1331999) B1331999
theorem B593663 : Blo 591290 593663 := bstep (se 1 (by rfl) ⟨445247, by rfl⟩ : syracuseStep 593663 = 890495) B890495
theorem B889151 : Blo 591290 889151 := bstep (se 1 (by rfl) ⟨666863, by rfl⟩ : syracuseStep 889151 = 1333727) B1333727
theorem B594415 : Blo 591290 594415 := bstep (se 1 (by rfl) ⟨445811, by rfl⟩ : syracuseStep 594415 = 891623) B891623
theorem B594759 : Blo 591290 594759 := bstep (se 1 (by rfl) ⟨446069, by rfl⟩ : syracuseStep 594759 = 892139) B892139
theorem B889799 : Blo 591290 889799 := bstep (se 1 (by rfl) ⟨667349, by rfl⟩ : syracuseStep 889799 = 1334699) B1334699
theorem B891611 : Blo 591290 891611 := bstep (se 1 (by rfl) ⟨668708, by rfl⟩ : syracuseStep 891611 = 1337417) B1337417
theorem B11575183 : Blo 591290 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B2993435 : Blo 591290 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B602023 : Blo 591290 602023 := bstep (se 1 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 602023 = 903035) B903035
theorem B9155051 : Blo 591290 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B3126761 : Blo 591290 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B3388985 : Blo 591290 3388985 := bstep (se 2 (by rfl) ⟨1270869, by rfl⟩ : syracuseStep 3388985 = 2541739) B2541739
theorem B1522559 : Blo 591290 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B7717315 : Blo 591290 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B5063147 : Blo 591290 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B1000687 : Blo 591290 1000687 := bstep (se 1 (by rfl) ⟨750515, by rfl⟩ : syracuseStep 1000687 = 1501031) B1501031
theorem B7587593 : Blo 591290 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B1001639 : Blo 591290 1001639 := bstep (se 1 (by rfl) ⟨751229, by rfl⟩ : syracuseStep 1001639 = 1502459) B1502459
theorem B1689959 : Blo 591290 1689959 := bstep (se 1 (by rfl) ⟨1267469, by rfl⟩ : syracuseStep 1689959 = 2534939) B2534939
theorem B1002287 : Blo 591290 1002287 := bstep (se 1 (by rfl) ⟨751715, by rfl⟩ : syracuseStep 1002287 = 1503431) B1503431
theorem B1002665 : Blo 591290 1002665 := bstep (se 2 (by rfl) ⟨375999, by rfl⟩ : syracuseStep 1002665 = 751999) B751999
theorem B3002345 : Blo 591290 3002345 := bstep (se 2 (by rfl) ⟨1125879, by rfl⟩ : syracuseStep 3002345 = 2251759) B2251759
theorem B6770951 : Blo 591290 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B1497001 : Blo 591290 1497001 := bstep (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) B1122751
theorem B5068919 : Blo 591290 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B1497599 : Blo 591290 1497599 := bstep (se 1 (by rfl) ⟨1123199, by rfl⟩ : syracuseStep 1497599 = 2246399) B2246399
theorem B6839423 : Blo 591290 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B1694857 : Blo 591290 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B1336103 : Blo 591290 1336103 := bstep (se 1 (by rfl) ⟨1002077, by rfl⟩ : syracuseStep 1336103 = 2004155) B2004155
theorem B1338281 : Blo 591290 1338281 := bstep (se 2 (by rfl) ⟨501855, by rfl⟩ : syracuseStep 1338281 = 1003711) B1003711
theorem B1600975 : Blo 591290 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B4517369 : Blo 591290 4517369 := bstep (se 2 (by rfl) ⟨1694013, by rfl⟩ : syracuseStep 4517369 = 3388027) B3388027
theorem B1502975 : Blo 591290 1502975 := bstep (se 1 (by rfl) ⟨1127231, by rfl⟩ : syracuseStep 1502975 = 2254463) B2254463
theorem B15169031 : Blo 591290 15169031 := bstep (se 1 (by rfl) ⟨11376773, by rfl⟩ : syracuseStep 15169031 = 22753547) B22753547
theorem B751295 : Blo 591290 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B3375431 : Blo 591290 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B10289753 : Blo 591290 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B591615 : Blo 591290 591615 := bstep (se 1 (by rfl) ⟨443711, by rfl⟩ : syracuseStep 591615 = 887423) B887423
theorem B591999 : Blo 591290 591999 := bstep (se 1 (by rfl) ⟨443999, by rfl⟩ : syracuseStep 591999 = 887999) B887999
theorem B2001563 : Blo 591290 2001563 := bstep (se 1 (by rfl) ⟨1501172, by rfl⟩ : syracuseStep 2001563 = 3002345) B3002345
theorem B592767 : Blo 591290 592767 := bstep (se 1 (by rfl) ⟨444575, by rfl⟩ : syracuseStep 592767 = 889151) B889151
theorem B593199 : Blo 591290 593199 := bstep (se 1 (by rfl) ⟨444899, by rfl⟩ : syracuseStep 593199 = 889799) B889799
theorem B3379279 : Blo 591290 3379279 := bstep (se 1 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 3379279 = 5068919) B5068919
theorem B594407 : Blo 591290 594407 := bstep (se 1 (by rfl) ⟨445805, by rfl⟩ : syracuseStep 594407 = 891611) B891611
theorem B2003453 : Blo 591290 2003453 := bstep (se 3 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 2003453 = 751295) B751295
theorem B2134633 : Blo 591290 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B4559615 : Blo 591290 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B890735 : Blo 591290 890735 := bstep (se 1 (by rfl) ⟨668051, by rfl⟩ : syracuseStep 890735 = 1336103) B1336103
theorem B892187 : Blo 591290 892187 := bstep (se 1 (by rfl) ⟨669140, by rfl⟩ : syracuseStep 892187 = 1338281) B1338281
theorem B6103367 : Blo 591290 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B5058395 : Blo 591290 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B667759 : Blo 591290 667759 := bstep (se 1 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 667759 = 1001639) B1001639
theorem B1126639 : Blo 591290 1126639 := bstep (se 1 (by rfl) ⟨844979, by rfl⟩ : syracuseStep 1126639 = 1689959) B1689959
theorem B668191 : Blo 591290 668191 := bstep (se 1 (by rfl) ⟨501143, by rfl⟩ : syracuseStep 668191 = 1002287) B1002287
theorem B10793513 : Blo 591290 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B668443 : Blo 591290 668443 := bstep (se 1 (by rfl) ⟨501332, by rfl⟩ : syracuseStep 668443 = 1002665) B1002665
theorem B998399 : Blo 591290 998399 := bstep (se 1 (by rfl) ⟨748799, by rfl⟩ : syracuseStep 998399 = 1497599) B1497599
theorem B1001983 : Blo 591290 1001983 := bstep (se 1 (by rfl) ⟨751487, by rfl⟩ : syracuseStep 1001983 = 1502975) B1502975
theorem B2084507 : Blo 591290 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B10112687 : Blo 591290 10112687 := bstep (se 1 (by rfl) ⟨7584515, by rfl⟩ : syracuseStep 10112687 = 15169031) B15169031
theorem B5068169 : Blo 591290 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B2250575 : Blo 591290 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B1334249 : Blo 591290 1334249 := bstep (se 2 (by rfl) ⟨500343, by rfl⟩ : syracuseStep 1334249 = 1000687) B1000687
theorem B4513967 : Blo 591290 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B51372629 : Blo 591290 51372629 := bstep (se 8 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 51372629 = 602023) B602023
theorem B1995623 : Blo 591290 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B3011579 : Blo 591290 3011579 := bstep (se 1 (by rfl) ⟨2258684, by rfl⟩ : syracuseStep 3011579 = 4517369) B4517369
theorem B1996001 : Blo 591290 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B2259323 : Blo 591290 2259323 := bstep (se 1 (by rfl) ⟨1694492, by rfl⟩ : syracuseStep 2259323 = 3388985) B3388985
theorem B2259809 : Blo 591290 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B1015039 : Blo 591290 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B15433577 : Blo 591290 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B3378779 : Blo 591290 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B593823 : Blo 591290 593823 := bstep (se 1 (by rfl) ⟨445367, by rfl⟩ : syracuseStep 593823 = 890735) B890735
theorem B889499 : Blo 591290 889499 := bstep (se 1 (by rfl) ⟨667124, by rfl⟩ : syracuseStep 889499 = 1334249) B1334249
theorem B594791 : Blo 591290 594791 := bstep (se 1 (by rfl) ⟨446093, by rfl⟩ : syracuseStep 594791 = 892187) B892187
theorem B890345 : Blo 591290 890345 := bstep (se 2 (by rfl) ⟨333879, by rfl⟩ : syracuseStep 890345 = 667759) B667759
theorem B4068911 : Blo 591290 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B34248419 : Blo 591290 34248419 := bstep (se 1 (by rfl) ⟨25686314, by rfl⟩ : syracuseStep 34248419 = 51372629) B51372629
theorem B890921 : Blo 591290 890921 := bstep (se 2 (by rfl) ⟨334095, by rfl⟩ : syracuseStep 890921 = 668191) B668191
theorem B891257 : Blo 591290 891257 := bstep (se 2 (by rfl) ⟨334221, by rfl⟩ : syracuseStep 891257 = 668443) B668443
theorem B2007719 : Blo 591290 2007719 := bstep (se 1 (by rfl) ⟨1505789, by rfl⟩ : syracuseStep 2007719 = 3011579) B3011579
theorem B1353385 : Blo 591290 1353385 := bstep (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) B1015039
theorem B665599 : Blo 591290 665599 := bstep (se 1 (by rfl) ⟨499199, by rfl⟩ : syracuseStep 665599 = 998399) B998399
theorem B6859835 : Blo 591290 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B1389671 : Blo 591290 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B4505705 : Blo 591290 4505705 := bstep (se 2 (by rfl) ⟨1689639, by rfl⟩ : syracuseStep 4505705 = 3379279) B3379279
theorem B7195675 : Blo 591290 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B1330415 : Blo 591290 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B1330667 : Blo 591290 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B2250287 : Blo 591290 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B1334375 : Blo 591290 1334375 := bstep (se 1 (by rfl) ⟨1000781, by rfl⟩ : syracuseStep 1334375 = 2001563) B2001563
theorem B6741791 : Blo 591290 6741791 := bstep (se 1 (by rfl) ⟨5056343, by rfl⟩ : syracuseStep 6741791 = 10112687) B10112687
theorem B1335635 : Blo 591290 1335635 := bstep (se 1 (by rfl) ⟨1001726, by rfl⟩ : syracuseStep 1335635 = 2003453) B2003453
theorem B3039743 : Blo 591290 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B1335977 : Blo 591290 1335977 := bstep (se 2 (by rfl) ⟨500991, by rfl⟩ : syracuseStep 1335977 = 1001983) B1001983
theorem B1500383 : Blo 591290 1500383 := bstep (se 1 (by rfl) ⟨1125287, by rfl⟩ : syracuseStep 1500383 = 2250575) B2250575
theorem B3009311 : Blo 591290 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B1502185 : Blo 591290 1502185 := bstep (se 2 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 1502185 = 1126639) B1126639
theorem B2846177 : Blo 591290 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B3372263 : Blo 591290 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B1506215 : Blo 591290 1506215 := bstep (se 1 (by rfl) ⟨1129661, by rfl⟩ : syracuseStep 1506215 = 2259323) B2259323
theorem B1506539 : Blo 591290 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B10289051 : Blo 591290 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B886943 : Blo 591290 886943 := bstep (se 1 (by rfl) ⟨665207, by rfl⟩ : syracuseStep 886943 = 1330415) B1330415
theorem B1804513 : Blo 591290 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B887111 : Blo 591290 887111 := bstep (se 1 (by rfl) ⟨665333, by rfl⟩ : syracuseStep 887111 = 1330667) B1330667
theorem B887465 : Blo 591290 887465 := bstep (se 2 (by rfl) ⟨332799, by rfl⟩ : syracuseStep 887465 = 665599) B665599
theorem B592999 : Blo 591290 592999 := bstep (se 1 (by rfl) ⟨444749, by rfl⟩ : syracuseStep 592999 = 889499) B889499
theorem B593563 : Blo 591290 593563 := bstep (se 1 (by rfl) ⟨445172, by rfl⟩ : syracuseStep 593563 = 890345) B890345
theorem B2002913 : Blo 591290 2002913 := bstep (se 2 (by rfl) ⟨751092, by rfl⟩ : syracuseStep 2002913 = 1502185) B1502185
theorem B593947 : Blo 591290 593947 := bstep (se 1 (by rfl) ⟨445460, by rfl⟩ : syracuseStep 593947 = 890921) B890921
theorem B10850429 : Blo 591290 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B594171 : Blo 591290 594171 := bstep (se 1 (by rfl) ⟨445628, by rfl⟩ : syracuseStep 594171 = 891257) B891257
theorem B889583 : Blo 591290 889583 := bstep (se 1 (by rfl) ⟨667187, by rfl⟩ : syracuseStep 889583 = 1334375) B1334375
theorem B4494527 : Blo 591290 4494527 := bstep (se 1 (by rfl) ⟨3370895, by rfl⟩ : syracuseStep 4494527 = 6741791) B6741791
theorem B890423 : Blo 591290 890423 := bstep (se 1 (by rfl) ⟨667817, by rfl⟩ : syracuseStep 890423 = 1335635) B1335635
theorem B890651 : Blo 591290 890651 := bstep (se 1 (by rfl) ⟨667988, by rfl⟩ : syracuseStep 890651 = 1335977) B1335977
theorem B2006207 : Blo 591290 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B926447 : Blo 591290 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B6859367 : Blo 591290 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B1000255 : Blo 591290 1000255 := bstep (se 1 (by rfl) ⟨750191, by rfl⟩ : syracuseStep 1000255 = 1500383) B1500383
theorem B4573223 : Blo 591290 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B2248175 : Blo 591290 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B1004143 : Blo 591290 1004143 := bstep (se 1 (by rfl) ⟨753107, by rfl⟩ : syracuseStep 1004143 = 1506215) B1506215
theorem B1004359 : Blo 591290 1004359 := bstep (se 1 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 1004359 = 1506539) B1506539
theorem B3003803 : Blo 591290 3003803 := bstep (se 1 (by rfl) ⟨2252852, by rfl⟩ : syracuseStep 3003803 = 4505705) B4505705
theorem B2252519 : Blo 591290 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B1500191 : Blo 591290 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B22832279 : Blo 591290 22832279 := bstep (se 1 (by rfl) ⟨17124209, by rfl⟩ : syracuseStep 22832279 = 34248419) B34248419
theorem B9594233 : Blo 591290 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B2026495 : Blo 591290 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B1338479 : Blo 591290 1338479 := bstep (se 1 (by rfl) ⟨1003859, by rfl⟩ : syracuseStep 1338479 = 2007719) B2007719
theorem B1897451 : Blo 591290 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B3048815 : Blo 591290 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B591295 : Blo 591290 591295 := bstep (se 1 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 591295 = 886943) B886943
theorem B591407 : Blo 591290 591407 := bstep (se 1 (by rfl) ⟨443555, by rfl⟩ : syracuseStep 591407 = 887111) B887111
theorem B591643 : Blo 591290 591643 := bstep (se 1 (by rfl) ⟨443732, by rfl⟩ : syracuseStep 591643 = 887465) B887465
theorem B593055 : Blo 591290 593055 := bstep (se 1 (by rfl) ⟨444791, by rfl⟩ : syracuseStep 593055 = 889583) B889583
theorem B2002535 : Blo 591290 2002535 := bstep (se 1 (by rfl) ⟨1501901, by rfl⟩ : syracuseStep 2002535 = 3003803) B3003803
theorem B593615 : Blo 591290 593615 := bstep (se 1 (by rfl) ⟨445211, by rfl⟩ : syracuseStep 593615 = 890423) B890423
theorem B593767 : Blo 591290 593767 := bstep (se 1 (by rfl) ⟨445325, by rfl⟩ : syracuseStep 593767 = 890651) B890651
theorem B6396155 : Blo 591290 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B892319 : Blo 591290 892319 := bstep (se 1 (by rfl) ⟨669239, by rfl⟩ : syracuseStep 892319 = 1338479) B1338479
theorem B2406017 : Blo 591290 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B2996351 : Blo 591290 2996351 := bstep (se 1 (by rfl) ⟨2247263, by rfl⟩ : syracuseStep 2996351 = 4494527) B4494527
theorem B2701993 : Blo 591290 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B1000127 : Blo 591290 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B15221519 : Blo 591290 15221519 := bstep (se 1 (by rfl) ⟨11416139, by rfl⟩ : syracuseStep 15221519 = 22832279) B22832279
theorem B4572911 : Blo 591290 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B9882101 : Blo 591290 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B1264967 : Blo 591290 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B1333673 : Blo 591290 1333673 := bstep (se 2 (by rfl) ⟨500127, by rfl⟩ : syracuseStep 1333673 = 1000255) B1000255
theorem B1498783 : Blo 591290 1498783 := bstep (se 1 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 1498783 = 2248175) B2248175
theorem B1335275 : Blo 591290 1335275 := bstep (se 1 (by rfl) ⟨1001456, by rfl⟩ : syracuseStep 1335275 = 2002913) B2002913
theorem B7233619 : Blo 591290 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B1337471 : Blo 591290 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B1501679 : Blo 591290 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B1338857 : Blo 591290 1338857 := bstep (se 2 (by rfl) ⟨502071, by rfl⟩ : syracuseStep 1338857 = 1004143) B1004143
theorem B1339145 : Blo 591290 1339145 := bstep (se 2 (by rfl) ⟨502179, by rfl⟩ : syracuseStep 1339145 = 1004359) B1004359
theorem B2032543 : Blo 591290 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B3048607 : Blo 591290 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B6588067 : Blo 591290 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B4264103 : Blo 591290 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B889115 : Blo 591290 889115 := bstep (se 1 (by rfl) ⟨666836, by rfl⟩ : syracuseStep 889115 = 1333673) B1333673
theorem B594879 : Blo 591290 594879 := bstep (se 1 (by rfl) ⟨446159, by rfl⟩ : syracuseStep 594879 = 892319) B892319
theorem B890183 : Blo 591290 890183 := bstep (se 1 (by rfl) ⟨667637, by rfl⟩ : syracuseStep 890183 = 1335275) B1335275
theorem B891647 : Blo 591290 891647 := bstep (se 1 (by rfl) ⟨668735, by rfl⟩ : syracuseStep 891647 = 1337471) B1337471
theorem B892571 : Blo 591290 892571 := bstep (se 1 (by rfl) ⟨669428, by rfl⟩ : syracuseStep 892571 = 1338857) B1338857
theorem B892763 : Blo 591290 892763 := bstep (se 1 (by rfl) ⟨669572, by rfl⟩ : syracuseStep 892763 = 1339145) B1339145
theorem B9644825 : Blo 591290 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B666751 : Blo 591290 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B1001119 : Blo 591290 1001119 := bstep (se 1 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 1001119 = 1501679) B1501679
theorem B10147679 : Blo 591290 10147679 := bstep (se 1 (by rfl) ⟨7610759, by rfl⟩ : syracuseStep 10147679 = 15221519) B15221519
theorem B843311 : Blo 591290 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B1335023 : Blo 591290 1335023 := bstep (se 1 (by rfl) ⟨1001267, by rfl⟩ : syracuseStep 1335023 = 2002535) B2002535
theorem B3602657 : Blo 591290 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B1604011 : Blo 591290 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B1997567 : Blo 591290 1997567 := bstep (se 1 (by rfl) ⟨1498175, by rfl⟩ : syracuseStep 1997567 = 2996351) B2996351
theorem B1998377 : Blo 591290 1998377 := bstep (se 2 (by rfl) ⟨749391, by rfl⟩ : syracuseStep 1998377 = 1498783) B1498783
theorem B8784089 : Blo 591290 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B592743 : Blo 591290 592743 := bstep (se 1 (by rfl) ⟨444557, by rfl⟩ : syracuseStep 592743 = 889115) B889115
theorem B593455 : Blo 591290 593455 := bstep (se 1 (by rfl) ⟨445091, by rfl⟩ : syracuseStep 593455 = 890183) B890183
theorem B889001 : Blo 591290 889001 := bstep (se 2 (by rfl) ⟨333375, by rfl⟩ : syracuseStep 889001 = 666751) B666751
theorem B594431 : Blo 591290 594431 := bstep (se 1 (by rfl) ⟨445823, by rfl⟩ : syracuseStep 594431 = 891647) B891647
theorem B595047 : Blo 591290 595047 := bstep (se 1 (by rfl) ⟨446285, by rfl⟩ : syracuseStep 595047 = 892571) B892571
theorem B890015 : Blo 591290 890015 := bstep (se 1 (by rfl) ⟨667511, by rfl⟩ : syracuseStep 890015 = 1335023) B1335023
theorem B595175 : Blo 591290 595175 := bstep (se 1 (by rfl) ⟨446381, by rfl⟩ : syracuseStep 595175 = 892763) B892763
theorem B16259237 : Blo 591290 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B6429883 : Blo 591290 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B2138681 : Blo 591290 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B2401771 : Blo 591290 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B6765119 : Blo 591290 6765119 := bstep (se 1 (by rfl) ⟨5073839, by rfl⟩ : syracuseStep 6765119 = 10147679) B10147679
theorem B2248829 : Blo 591290 2248829 := bstep (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) B843311
theorem B1331711 : Blo 591290 1331711 := bstep (se 1 (by rfl) ⟨998783, by rfl⟩ : syracuseStep 1331711 = 1997567) B1997567
theorem B1332251 : Blo 591290 1332251 := bstep (se 1 (by rfl) ⟨999188, by rfl⟩ : syracuseStep 1332251 = 1998377) B1998377
theorem B1334825 : Blo 591290 1334825 := bstep (se 2 (by rfl) ⟨500559, by rfl⟩ : syracuseStep 1334825 = 1001119) B1001119
theorem B2842735 : Blo 591290 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B10840229 : Blo 591290 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B5703149 : Blo 591290 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B592667 : Blo 591290 592667 := bstep (se 1 (by rfl) ⟨444500, by rfl⟩ : syracuseStep 592667 = 889001) B889001
theorem B887807 : Blo 591290 887807 := bstep (se 1 (by rfl) ⟨665855, by rfl⟩ : syracuseStep 887807 = 1331711) B1331711
theorem B888167 : Blo 591290 888167 := bstep (se 1 (by rfl) ⟨666125, by rfl⟩ : syracuseStep 888167 = 1332251) B1332251
theorem B593343 : Blo 591290 593343 := bstep (se 1 (by rfl) ⟨445007, by rfl⟩ : syracuseStep 593343 = 890015) B890015
theorem B889883 : Blo 591290 889883 := bstep (se 1 (by rfl) ⟨667412, by rfl⟩ : syracuseStep 889883 = 1334825) B1334825
theorem B7226819 : Blo 591290 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B8573177 : Blo 591290 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B4510079 : Blo 591290 4510079 := bstep (se 1 (by rfl) ⟨3382559, by rfl⟩ : syracuseStep 4510079 = 6765119) B6765119
theorem B3790313 : Blo 591290 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B5856059 : Blo 591290 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3202361 : Blo 591290 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B1499219 : Blo 591290 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B10839491 : Blo 591290 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B4817879 : Blo 591290 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B591871 : Blo 591290 591871 := bstep (se 1 (by rfl) ⟨443903, by rfl⟩ : syracuseStep 591871 = 887807) B887807
theorem B592111 : Blo 591290 592111 := bstep (se 1 (by rfl) ⟨444083, by rfl⟩ : syracuseStep 592111 = 888167) B888167
theorem B593255 : Blo 591290 593255 := bstep (se 1 (by rfl) ⟨444941, by rfl⟩ : syracuseStep 593255 = 889883) B889883
theorem B2526875 : Blo 591290 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B15208397 : Blo 591290 15208397 := bstep (se 3 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 15208397 = 5703149) B5703149
theorem B3904039 : Blo 591290 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B2134907 : Blo 591290 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B5715451 : Blo 591290 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B999479 : Blo 591290 999479 := bstep (se 1 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 999479 = 1499219) B1499219
theorem B7226327 : Blo 591290 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B3006719 : Blo 591290 3006719 := bstep (se 1 (by rfl) ⟨2255039, by rfl⟩ : syracuseStep 3006719 = 4510079) B4510079
theorem B4817551 : Blo 591290 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B3211919 : Blo 591290 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B2004479 : Blo 591290 2004479 := bstep (se 1 (by rfl) ⟨1503359, by rfl⟩ : syracuseStep 2004479 = 3006719) B3006719
theorem B666319 : Blo 591290 666319 := bstep (se 1 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 666319 = 999479) B999479
theorem B1684583 : Blo 591290 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B10138931 : Blo 591290 10138931 := bstep (se 1 (by rfl) ⟨7604198, by rfl⟩ : syracuseStep 10138931 = 15208397) B15208397
theorem B1423271 : Blo 591290 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B7620601 : Blo 591290 7620601 := bstep (se 2 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 7620601 = 5715451) B5715451
theorem B5205385 : Blo 591290 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B6423401 : Blo 591290 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B10160801 : Blo 591290 10160801 := bstep (se 2 (by rfl) ⟨3810300, by rfl⟩ : syracuseStep 10160801 = 7620601) B7620601
theorem B888425 : Blo 591290 888425 := bstep (se 2 (by rfl) ⟨333159, by rfl⟩ : syracuseStep 888425 = 666319) B666319
theorem B1123055 : Blo 591290 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B6759287 : Blo 591290 6759287 := bstep (se 1 (by rfl) ⟨5069465, by rfl⟩ : syracuseStep 6759287 = 10138931) B10138931
theorem B2141279 : Blo 591290 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B1336319 : Blo 591290 1336319 := bstep (se 1 (by rfl) ⟨1002239, by rfl⟩ : syracuseStep 1336319 = 2004479) B2004479
theorem B6940513 : Blo 591290 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B948847 : Blo 591290 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B592283 : Blo 591290 592283 := bstep (se 1 (by rfl) ⟨444212, by rfl⟩ : syracuseStep 592283 = 888425) B888425
theorem B890879 : Blo 591290 890879 := bstep (se 1 (by rfl) ⟨668159, by rfl⟩ : syracuseStep 890879 = 1336319) B1336319
theorem B9254017 : Blo 591290 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B4506191 : Blo 591290 4506191 := bstep (se 1 (by rfl) ⟨3379643, by rfl⟩ : syracuseStep 4506191 = 6759287) B6759287
theorem B1427519 : Blo 591290 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B1265129 : Blo 591290 1265129 := bstep (se 2 (by rfl) ⟨474423, by rfl⟩ : syracuseStep 1265129 = 948847) B948847
theorem B4282267 : Blo 591290 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B6773867 : Blo 591290 6773867 := bstep (se 1 (by rfl) ⟨5080400, by rfl⟩ : syracuseStep 6773867 = 10160801) B10160801
theorem B748703 : Blo 591290 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B951679 : Blo 591290 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B593919 : Blo 591290 593919 := bstep (se 1 (by rfl) ⟨445439, by rfl⟩ : syracuseStep 593919 = 890879) B890879
theorem B5709689 : Blo 591290 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B12338689 : Blo 591290 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B3004127 : Blo 591290 3004127 := bstep (se 1 (by rfl) ⟨2253095, by rfl⟩ : syracuseStep 3004127 = 4506191) B4506191
theorem B843419 : Blo 591290 843419 := bstep (se 1 (by rfl) ⟨632564, by rfl⟩ : syracuseStep 843419 = 1265129) B1265129
theorem B4515911 : Blo 591290 4515911 := bstep (se 1 (by rfl) ⟨3386933, by rfl⟩ : syracuseStep 4515911 = 6773867) B6773867
theorem B1996541 : Blo 591290 1996541 := bstep (se 3 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 1996541 = 748703) B748703
theorem B16451585 : Blo 591290 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B2002751 : Blo 591290 2002751 := bstep (se 1 (by rfl) ⟨1502063, by rfl⟩ : syracuseStep 2002751 = 3004127) B3004127
theorem B3806459 : Blo 591290 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B1331027 : Blo 591290 1331027 := bstep (se 1 (by rfl) ⟨998270, by rfl⟩ : syracuseStep 1331027 = 1996541) B1996541
theorem B2249117 : Blo 591290 2249117 := bstep (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) B843419
theorem B1268905 : Blo 591290 1268905 := bstep (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) B951679
theorem B3010607 : Blo 591290 3010607 := bstep (se 1 (by rfl) ⟨2257955, by rfl⟩ : syracuseStep 3010607 = 4515911) B4515911
theorem B887351 : Blo 591290 887351 := bstep (se 1 (by rfl) ⟨665513, by rfl⟩ : syracuseStep 887351 = 1331027) B1331027
theorem B2007071 : Blo 591290 2007071 := bstep (se 1 (by rfl) ⟨1505303, by rfl⟩ : syracuseStep 2007071 = 3010607) B3010607
theorem B2537639 : Blo 591290 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B1691873 : Blo 591290 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B10967723 : Blo 591290 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B1335167 : Blo 591290 1335167 := bstep (se 1 (by rfl) ⟨1001375, by rfl⟩ : syracuseStep 1335167 = 2002751) B2002751
theorem B1499411 : Blo 591290 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B591567 : Blo 591290 591567 := bstep (se 1 (by rfl) ⟨443675, by rfl⟩ : syracuseStep 591567 = 887351) B887351
theorem B7311815 : Blo 591290 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B890111 : Blo 591290 890111 := bstep (se 1 (by rfl) ⟨667583, by rfl⟩ : syracuseStep 890111 = 1335167) B1335167
theorem B1127915 : Blo 591290 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B999607 : Blo 591290 999607 := bstep (se 1 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 999607 = 1499411) B1499411
theorem B1691759 : Blo 591290 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B1338047 : Blo 591290 1338047 := bstep (se 1 (by rfl) ⟨1003535, by rfl⟩ : syracuseStep 1338047 = 2007071) B2007071
theorem B593407 : Blo 591290 593407 := bstep (se 1 (by rfl) ⟨445055, by rfl⟩ : syracuseStep 593407 = 890111) B890111
theorem B892031 : Blo 591290 892031 := bstep (se 1 (by rfl) ⟨669023, by rfl⟩ : syracuseStep 892031 = 1338047) B1338047
theorem B1127839 : Blo 591290 1127839 := bstep (se 1 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 1127839 = 1691759) B1691759
theorem B1332809 : Blo 591290 1332809 := bstep (se 2 (by rfl) ⟨499803, by rfl⟩ : syracuseStep 1332809 = 999607) B999607
theorem B4874543 : Blo 591290 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B751943 : Blo 591290 751943 := bstep (se 1 (by rfl) ⟨563957, by rfl⟩ : syracuseStep 751943 = 1127915) B1127915
theorem B888539 : Blo 591290 888539 := bstep (se 1 (by rfl) ⟨666404, by rfl⟩ : syracuseStep 888539 = 1332809) B1332809
theorem B594687 : Blo 591290 594687 := bstep (se 1 (by rfl) ⟨446015, by rfl⟩ : syracuseStep 594687 = 892031) B892031
theorem B3249695 : Blo 591290 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B2005181 : Blo 591290 2005181 := bstep (se 3 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 2005181 = 751943) B751943
theorem B1503785 : Blo 591290 1503785 := bstep (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) B1127839
theorem B592359 : Blo 591290 592359 := bstep (se 1 (by rfl) ⟨444269, by rfl⟩ : syracuseStep 592359 = 888539) B888539
theorem B2166463 : Blo 591290 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B1002523 : Blo 591290 1002523 := bstep (se 1 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 1002523 = 1503785) B1503785
theorem B1336787 : Blo 591290 1336787 := bstep (se 1 (by rfl) ⟨1002590, by rfl⟩ : syracuseStep 1336787 = 2005181) B2005181
theorem B2888617 : Blo 591290 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B891191 : Blo 591290 891191 := bstep (se 1 (by rfl) ⟨668393, by rfl⟩ : syracuseStep 891191 = 1336787) B1336787
theorem B1336697 : Blo 591290 1336697 := bstep (se 2 (by rfl) ⟨501261, by rfl⟩ : syracuseStep 1336697 = 1002523) B1002523
theorem B594127 : Blo 591290 594127 := bstep (se 1 (by rfl) ⟨445595, by rfl⟩ : syracuseStep 594127 = 891191) B891191
theorem B891131 : Blo 591290 891131 := bstep (se 1 (by rfl) ⟨668348, by rfl⟩ : syracuseStep 891131 = 1336697) B1336697
theorem B3851489 : Blo 591290 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B594087 : Blo 591290 594087 := bstep (se 1 (by rfl) ⟨445565, by rfl⟩ : syracuseStep 594087 = 891131) B891131
theorem B2567659 : Blo 591290 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B3423545 : Blo 591290 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B2282363 : Blo 591290 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B1521575 : Blo 591290 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B1014383 : Blo 591290 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B676255 : Blo 591290 676255 := bstep (se 1 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 676255 = 1014383) B1014383
theorem B901673 : Blo 591290 901673 := bstep (se 2 (by rfl) ⟨338127, by rfl⟩ : syracuseStep 901673 = 676255) B676255
theorem B601115 : Blo 591290 601115 := bstep (se 1 (by rfl) ⟨450836, by rfl⟩ : syracuseStep 601115 = 901673) B901673
theorem B1602973 : Blo 591290 1602973 := bstep (se 3 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 1602973 = 601115) B601115
theorem B8549189 : Blo 591290 8549189 := bstep (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) B1602973
theorem B5699459 : Blo 591290 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B3799639 : Blo 591290 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B5066185 : Blo 591290 5066185 := bstep (se 2 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 5066185 = 3799639) B3799639
theorem B6754913 : Blo 591290 6754913 := bstep (se 2 (by rfl) ⟨2533092, by rfl⟩ : syracuseStep 6754913 = 5066185) B5066185
theorem B4503275 : Blo 591290 4503275 := bstep (se 1 (by rfl) ⟨3377456, by rfl⟩ : syracuseStep 4503275 = 6754913) B6754913
theorem B3002183 : Blo 591290 3002183 := bstep (se 1 (by rfl) ⟨2251637, by rfl⟩ : syracuseStep 3002183 = 4503275) B4503275
theorem B2001455 : Blo 591290 2001455 := bstep (se 1 (by rfl) ⟨1501091, by rfl⟩ : syracuseStep 2001455 = 3002183) B3002183
theorem B1334303 : Blo 591290 1334303 := bstep (se 1 (by rfl) ⟨1000727, by rfl⟩ : syracuseStep 1334303 = 2001455) B2001455
theorem B889535 : Blo 591290 889535 := bstep (se 1 (by rfl) ⟨667151, by rfl⟩ : syracuseStep 889535 = 1334303) B1334303
theorem B593023 : Blo 591290 593023 := bstep (se 1 (by rfl) ⟨444767, by rfl⟩ : syracuseStep 593023 = 889535) B889535

theorem C0 (j : ℕ) (h1 : 147822 ≤ j) (h2 : j ≤ 148521) : Blo 591290 (4 * j + 3) := by
  interval_cases j
  · exact B591291
  · exact B591295
  · exact B591299
  · exact B591303
  · exact B591307
  · exact B591311
  · exact B591315
  · exact B591319
  · exact B591323
  · exact B591327
  · exact B591331
  · exact B591335
  · exact B591339
  · exact B591343
  · exact B591347
  · exact B591351
  · exact B591355
  · exact B591359
  · exact B591363
  · exact B591367
  · exact B591371
  · exact B591375
  · exact B591379
  · exact B591383
  · exact B591387
  · exact B591391
  · exact B591395
  · exact B591399
  · exact B591403
  · exact B591407
  · exact B591411
  · exact B591415
  · exact B591419
  · exact B591423
  · exact B591427
  · exact B591431
  · exact B591435
  · exact B591439
  · exact B591443
  · exact B591447
  · exact B591451
  · exact B591455
  · exact B591459
  · exact B591463
  · exact B591467
  · exact B591471
  · exact B591475
  · exact B591479
  · exact B591483
  · exact B591487
  · exact B591491
  · exact B591495
  · exact B591499
  · exact B591503
  · exact B591507
  · exact B591511
  · exact B591515
  · exact B591519
  · exact B591523
  · exact B591527
  · exact B591531
  · exact B591535
  · exact B591539
  · exact B591543
  · exact B591547
  · exact B591551
  · exact B591555
  · exact B591559
  · exact B591563
  · exact B591567
  · exact B591571
  · exact B591575
  · exact B591579
  · exact B591583
  · exact B591587
  · exact B591591
  · exact B591595
  · exact B591599
  · exact B591603
  · exact B591607
  · exact B591611
  · exact B591615
  · exact B591619
  · exact B591623
  · exact B591627
  · exact B591631
  · exact B591635
  · exact B591639
  · exact B591643
  · exact B591647
  · exact B591651
  · exact B591655
  · exact B591659
  · exact B591663
  · exact B591667
  · exact B591671
  · exact B591675
  · exact B591679
  · exact B591683
  · exact B591687
  · exact B591691
  · exact B591695
  · exact B591699
  · exact B591703
  · exact B591707
  · exact B591711
  · exact B591715
  · exact B591719
  · exact B591723
  · exact B591727
  · exact B591731
  · exact B591735
  · exact B591739
  · exact B591743
  · exact B591747
  · exact B591751
  · exact B591755
  · exact B591759
  · exact B591763
  · exact B591767
  · exact B591771
  · exact B591775
  · exact B591779
  · exact B591783
  · exact B591787
  · exact B591791
  · exact B591795
  · exact B591799
  · exact B591803
  · exact B591807
  · exact B591811
  · exact B591815
  · exact B591819
  · exact B591823
  · exact B591827
  · exact B591831
  · exact B591835
  · exact B591839
  · exact B591843
  · exact B591847
  · exact B591851
  · exact B591855
  · exact B591859
  · exact B591863
  · exact B591867
  · exact B591871
  · exact B591875
  · exact B591879
  · exact B591883
  · exact B591887
  · exact B591891
  · exact B591895
  · exact B591899
  · exact B591903
  · exact B591907
  · exact B591911
  · exact B591915
  · exact B591919
  · exact B591923
  · exact B591927
  · exact B591931
  · exact B591935
  · exact B591939
  · exact B591943
  · exact B591947
  · exact B591951
  · exact B591955
  · exact B591959
  · exact B591963
  · exact B591967
  · exact B591971
  · exact B591975
  · exact B591979
  · exact B591983
  · exact B591987
  · exact B591991
  · exact B591995
  · exact B591999
  · exact B592003
  · exact B592007
  · exact B592011
  · exact B592015
  · exact B592019
  · exact B592023
  · exact B592027
  · exact B592031
  · exact B592035
  · exact B592039
  · exact B592043
  · exact B592047
  · exact B592051
  · exact B592055
  · exact B592059
  · exact B592063
  · exact B592067
  · exact B592071
  · exact B592075
  · exact B592079
  · exact B592083
  · exact B592087
  · exact B592091
  · exact B592095
  · exact B592099
  · exact B592103
  · exact B592107
  · exact B592111
  · exact B592115
  · exact B592119
  · exact B592123
  · exact B592127
  · exact B592131
  · exact B592135
  · exact B592139
  · exact B592143
  · exact B592147
  · exact B592151
  · exact B592155
  · exact B592159
  · exact B592163
  · exact B592167
  · exact B592171
  · exact B592175
  · exact B592179
  · exact B592183
  · exact B592187
  · exact B592191
  · exact B592195
  · exact B592199
  · exact B592203
  · exact B592207
  · exact B592211
  · exact B592215
  · exact B592219
  · exact B592223
  · exact B592227
  · exact B592231
  · exact B592235
  · exact B592239
  · exact B592243
  · exact B592247
  · exact B592251
  · exact B592255
  · exact B592259
  · exact B592263
  · exact B592267
  · exact B592271
  · exact B592275
  · exact B592279
  · exact B592283
  · exact B592287
  · exact B592291
  · exact B592295
  · exact B592299
  · exact B592303
  · exact B592307
  · exact B592311
  · exact B592315
  · exact B592319
  · exact B592323
  · exact B592327
  · exact B592331
  · exact B592335
  · exact B592339
  · exact B592343
  · exact B592347
  · exact B592351
  · exact B592355
  · exact B592359
  · exact B592363
  · exact B592367
  · exact B592371
  · exact B592375
  · exact B592379
  · exact B592383
  · exact B592387
  · exact B592391
  · exact B592395
  · exact B592399
  · exact B592403
  · exact B592407
  · exact B592411
  · exact B592415
  · exact B592419
  · exact B592423
  · exact B592427
  · exact B592431
  · exact B592435
  · exact B592439
  · exact B592443
  · exact B592447
  · exact B592451
  · exact B592455
  · exact B592459
  · exact B592463
  · exact B592467
  · exact B592471
  · exact B592475
  · exact B592479
  · exact B592483
  · exact B592487
  · exact B592491
  · exact B592495
  · exact B592499
  · exact B592503
  · exact B592507
  · exact B592511
  · exact B592515
  · exact B592519
  · exact B592523
  · exact B592527
  · exact B592531
  · exact B592535
  · exact B592539
  · exact B592543
  · exact B592547
  · exact B592551
  · exact B592555
  · exact B592559
  · exact B592563
  · exact B592567
  · exact B592571
  · exact B592575
  · exact B592579
  · exact B592583
  · exact B592587
  · exact B592591
  · exact B592595
  · exact B592599
  · exact B592603
  · exact B592607
  · exact B592611
  · exact B592615
  · exact B592619
  · exact B592623
  · exact B592627
  · exact B592631
  · exact B592635
  · exact B592639
  · exact B592643
  · exact B592647
  · exact B592651
  · exact B592655
  · exact B592659
  · exact B592663
  · exact B592667
  · exact B592671
  · exact B592675
  · exact B592679
  · exact B592683
  · exact B592687
  · exact B592691
  · exact B592695
  · exact B592699
  · exact B592703
  · exact B592707
  · exact B592711
  · exact B592715
  · exact B592719
  · exact B592723
  · exact B592727
  · exact B592731
  · exact B592735
  · exact B592739
  · exact B592743
  · exact B592747
  · exact B592751
  · exact B592755
  · exact B592759
  · exact B592763
  · exact B592767
  · exact B592771
  · exact B592775
  · exact B592779
  · exact B592783
  · exact B592787
  · exact B592791
  · exact B592795
  · exact B592799
  · exact B592803
  · exact B592807
  · exact B592811
  · exact B592815
  · exact B592819
  · exact B592823
  · exact B592827
  · exact B592831
  · exact B592835
  · exact B592839
  · exact B592843
  · exact B592847
  · exact B592851
  · exact B592855
  · exact B592859
  · exact B592863
  · exact B592867
  · exact B592871
  · exact B592875
  · exact B592879
  · exact B592883
  · exact B592887
  · exact B592891
  · exact B592895
  · exact B592899
  · exact B592903
  · exact B592907
  · exact B592911
  · exact B592915
  · exact B592919
  · exact B592923
  · exact B592927
  · exact B592931
  · exact B592935
  · exact B592939
  · exact B592943
  · exact B592947
  · exact B592951
  · exact B592955
  · exact B592959
  · exact B592963
  · exact B592967
  · exact B592971
  · exact B592975
  · exact B592979
  · exact B592983
  · exact B592987
  · exact B592991
  · exact B592995
  · exact B592999
  · exact B593003
  · exact B593007
  · exact B593011
  · exact B593015
  · exact B593019
  · exact B593023
  · exact B593027
  · exact B593031
  · exact B593035
  · exact B593039
  · exact B593043
  · exact B593047
  · exact B593051
  · exact B593055
  · exact B593059
  · exact B593063
  · exact B593067
  · exact B593071
  · exact B593075
  · exact B593079
  · exact B593083
  · exact B593087
  · exact B593091
  · exact B593095
  · exact B593099
  · exact B593103
  · exact B593107
  · exact B593111
  · exact B593115
  · exact B593119
  · exact B593123
  · exact B593127
  · exact B593131
  · exact B593135
  · exact B593139
  · exact B593143
  · exact B593147
  · exact B593151
  · exact B593155
  · exact B593159
  · exact B593163
  · exact B593167
  · exact B593171
  · exact B593175
  · exact B593179
  · exact B593183
  · exact B593187
  · exact B593191
  · exact B593195
  · exact B593199
  · exact B593203
  · exact B593207
  · exact B593211
  · exact B593215
  · exact B593219
  · exact B593223
  · exact B593227
  · exact B593231
  · exact B593235
  · exact B593239
  · exact B593243
  · exact B593247
  · exact B593251
  · exact B593255
  · exact B593259
  · exact B593263
  · exact B593267
  · exact B593271
  · exact B593275
  · exact B593279
  · exact B593283
  · exact B593287
  · exact B593291
  · exact B593295
  · exact B593299
  · exact B593303
  · exact B593307
  · exact B593311
  · exact B593315
  · exact B593319
  · exact B593323
  · exact B593327
  · exact B593331
  · exact B593335
  · exact B593339
  · exact B593343
  · exact B593347
  · exact B593351
  · exact B593355
  · exact B593359
  · exact B593363
  · exact B593367
  · exact B593371
  · exact B593375
  · exact B593379
  · exact B593383
  · exact B593387
  · exact B593391
  · exact B593395
  · exact B593399
  · exact B593403
  · exact B593407
  · exact B593411
  · exact B593415
  · exact B593419
  · exact B593423
  · exact B593427
  · exact B593431
  · exact B593435
  · exact B593439
  · exact B593443
  · exact B593447
  · exact B593451
  · exact B593455
  · exact B593459
  · exact B593463
  · exact B593467
  · exact B593471
  · exact B593475
  · exact B593479
  · exact B593483
  · exact B593487
  · exact B593491
  · exact B593495
  · exact B593499
  · exact B593503
  · exact B593507
  · exact B593511
  · exact B593515
  · exact B593519
  · exact B593523
  · exact B593527
  · exact B593531
  · exact B593535
  · exact B593539
  · exact B593543
  · exact B593547
  · exact B593551
  · exact B593555
  · exact B593559
  · exact B593563
  · exact B593567
  · exact B593571
  · exact B593575
  · exact B593579
  · exact B593583
  · exact B593587
  · exact B593591
  · exact B593595
  · exact B593599
  · exact B593603
  · exact B593607
  · exact B593611
  · exact B593615
  · exact B593619
  · exact B593623
  · exact B593627
  · exact B593631
  · exact B593635
  · exact B593639
  · exact B593643
  · exact B593647
  · exact B593651
  · exact B593655
  · exact B593659
  · exact B593663
  · exact B593667
  · exact B593671
  · exact B593675
  · exact B593679
  · exact B593683
  · exact B593687
  · exact B593691
  · exact B593695
  · exact B593699
  · exact B593703
  · exact B593707
  · exact B593711
  · exact B593715
  · exact B593719
  · exact B593723
  · exact B593727
  · exact B593731
  · exact B593735
  · exact B593739
  · exact B593743
  · exact B593747
  · exact B593751
  · exact B593755
  · exact B593759
  · exact B593763
  · exact B593767
  · exact B593771
  · exact B593775
  · exact B593779
  · exact B593783
  · exact B593787
  · exact B593791
  · exact B593795
  · exact B593799
  · exact B593803
  · exact B593807
  · exact B593811
  · exact B593815
  · exact B593819
  · exact B593823
  · exact B593827
  · exact B593831
  · exact B593835
  · exact B593839
  · exact B593843
  · exact B593847
  · exact B593851
  · exact B593855
  · exact B593859
  · exact B593863
  · exact B593867
  · exact B593871
  · exact B593875
  · exact B593879
  · exact B593883
  · exact B593887
  · exact B593891
  · exact B593895
  · exact B593899
  · exact B593903
  · exact B593907
  · exact B593911
  · exact B593915
  · exact B593919
  · exact B593923
  · exact B593927
  · exact B593931
  · exact B593935
  · exact B593939
  · exact B593943
  · exact B593947
  · exact B593951
  · exact B593955
  · exact B593959
  · exact B593963
  · exact B593967
  · exact B593971
  · exact B593975
  · exact B593979
  · exact B593983
  · exact B593987
  · exact B593991
  · exact B593995
  · exact B593999
  · exact B594003
  · exact B594007
  · exact B594011
  · exact B594015
  · exact B594019
  · exact B594023
  · exact B594027
  · exact B594031
  · exact B594035
  · exact B594039
  · exact B594043
  · exact B594047
  · exact B594051
  · exact B594055
  · exact B594059
  · exact B594063
  · exact B594067
  · exact B594071
  · exact B594075
  · exact B594079
  · exact B594083
  · exact B594087

theorem C1 (j : ℕ) (h1 : 148522 ≤ j) (h2 : j ≤ 148821) : Blo 591290 (4 * j + 3) := by
  interval_cases j
  · exact B594091
  · exact B594095
  · exact B594099
  · exact B594103
  · exact B594107
  · exact B594111
  · exact B594115
  · exact B594119
  · exact B594123
  · exact B594127
  · exact B594131
  · exact B594135
  · exact B594139
  · exact B594143
  · exact B594147
  · exact B594151
  · exact B594155
  · exact B594159
  · exact B594163
  · exact B594167
  · exact B594171
  · exact B594175
  · exact B594179
  · exact B594183
  · exact B594187
  · exact B594191
  · exact B594195
  · exact B594199
  · exact B594203
  · exact B594207
  · exact B594211
  · exact B594215
  · exact B594219
  · exact B594223
  · exact B594227
  · exact B594231
  · exact B594235
  · exact B594239
  · exact B594243
  · exact B594247
  · exact B594251
  · exact B594255
  · exact B594259
  · exact B594263
  · exact B594267
  · exact B594271
  · exact B594275
  · exact B594279
  · exact B594283
  · exact B594287
  · exact B594291
  · exact B594295
  · exact B594299
  · exact B594303
  · exact B594307
  · exact B594311
  · exact B594315
  · exact B594319
  · exact B594323
  · exact B594327
  · exact B594331
  · exact B594335
  · exact B594339
  · exact B594343
  · exact B594347
  · exact B594351
  · exact B594355
  · exact B594359
  · exact B594363
  · exact B594367
  · exact B594371
  · exact B594375
  · exact B594379
  · exact B594383
  · exact B594387
  · exact B594391
  · exact B594395
  · exact B594399
  · exact B594403
  · exact B594407
  · exact B594411
  · exact B594415
  · exact B594419
  · exact B594423
  · exact B594427
  · exact B594431
  · exact B594435
  · exact B594439
  · exact B594443
  · exact B594447
  · exact B594451
  · exact B594455
  · exact B594459
  · exact B594463
  · exact B594467
  · exact B594471
  · exact B594475
  · exact B594479
  · exact B594483
  · exact B594487
  · exact B594491
  · exact B594495
  · exact B594499
  · exact B594503
  · exact B594507
  · exact B594511
  · exact B594515
  · exact B594519
  · exact B594523
  · exact B594527
  · exact B594531
  · exact B594535
  · exact B594539
  · exact B594543
  · exact B594547
  · exact B594551
  · exact B594555
  · exact B594559
  · exact B594563
  · exact B594567
  · exact B594571
  · exact B594575
  · exact B594579
  · exact B594583
  · exact B594587
  · exact B594591
  · exact B594595
  · exact B594599
  · exact B594603
  · exact B594607
  · exact B594611
  · exact B594615
  · exact B594619
  · exact B594623
  · exact B594627
  · exact B594631
  · exact B594635
  · exact B594639
  · exact B594643
  · exact B594647
  · exact B594651
  · exact B594655
  · exact B594659
  · exact B594663
  · exact B594667
  · exact B594671
  · exact B594675
  · exact B594679
  · exact B594683
  · exact B594687
  · exact B594691
  · exact B594695
  · exact B594699
  · exact B594703
  · exact B594707
  · exact B594711
  · exact B594715
  · exact B594719
  · exact B594723
  · exact B594727
  · exact B594731
  · exact B594735
  · exact B594739
  · exact B594743
  · exact B594747
  · exact B594751
  · exact B594755
  · exact B594759
  · exact B594763
  · exact B594767
  · exact B594771
  · exact B594775
  · exact B594779
  · exact B594783
  · exact B594787
  · exact B594791
  · exact B594795
  · exact B594799
  · exact B594803
  · exact B594807
  · exact B594811
  · exact B594815
  · exact B594819
  · exact B594823
  · exact B594827
  · exact B594831
  · exact B594835
  · exact B594839
  · exact B594843
  · exact B594847
  · exact B594851
  · exact B594855
  · exact B594859
  · exact B594863
  · exact B594867
  · exact B594871
  · exact B594875
  · exact B594879
  · exact B594883
  · exact B594887
  · exact B594891
  · exact B594895
  · exact B594899
  · exact B594903
  · exact B594907
  · exact B594911
  · exact B594915
  · exact B594919
  · exact B594923
  · exact B594927
  · exact B594931
  · exact B594935
  · exact B594939
  · exact B594943
  · exact B594947
  · exact B594951
  · exact B594955
  · exact B594959
  · exact B594963
  · exact B594967
  · exact B594971
  · exact B594975
  · exact B594979
  · exact B594983
  · exact B594987
  · exact B594991
  · exact B594995
  · exact B594999
  · exact B595003
  · exact B595007
  · exact B595011
  · exact B595015
  · exact B595019
  · exact B595023
  · exact B595027
  · exact B595031
  · exact B595035
  · exact B595039
  · exact B595043
  · exact B595047
  · exact B595051
  · exact B595055
  · exact B595059
  · exact B595063
  · exact B595067
  · exact B595071
  · exact B595075
  · exact B595079
  · exact B595083
  · exact B595087
  · exact B595091
  · exact B595095
  · exact B595099
  · exact B595103
  · exact B595107
  · exact B595111
  · exact B595115
  · exact B595119
  · exact B595123
  · exact B595127
  · exact B595131
  · exact B595135
  · exact B595139
  · exact B595143
  · exact B595147
  · exact B595151
  · exact B595155
  · exact B595159
  · exact B595163
  · exact B595167
  · exact B595171
  · exact B595175
  · exact B595179
  · exact B595183
  · exact B595187
  · exact B595191
  · exact B595195
  · exact B595199
  · exact B595203
  · exact B595207
  · exact B595211
  · exact B595215
  · exact B595219
  · exact B595223
  · exact B595227
  · exact B595231
  · exact B595235
  · exact B595239
  · exact B595243
  · exact B595247
  · exact B595251
  · exact B595255
  · exact B595259
  · exact B595263
  · exact B595267
  · exact B595271
  · exact B595275
  · exact B595279
  · exact B595283
  · exact B595287

theorem solution (m : ℕ) (hlo : 591290 ≤ m) (hhi : m ≤ 595290) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 147822 ≤ j := by omega
    have hj2 : j ≤ 148821 := by omega
    have hb : Blo 591290 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 148522 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
