-- Prove2me | solution 1 for syracuse_descends_range_1370504_1372004
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:11.581996+00:00
-- url     : https://prove2.me/submissions/f6b72c42-4b8a-4c25-8682-e92c4a1674a2

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


theorem B2056205 : Blo 1370504 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B4628501 : Blo 1370504 4628501 := bbase (se 6 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 4628501 = 216961) (by norm_num)
theorem B2056229 : Blo 1370504 2056229 := bbase (se 4 (by rfl) ⟨192771, by rfl⟩ : syracuseStep 2056229 = 385543) (by norm_num)
theorem B2056253 : Blo 1370504 2056253 := bbase (se 3 (by rfl) ⟨385547, by rfl⟩ : syracuseStep 2056253 = 771095) (by norm_num)
theorem B2056277 : Blo 1370504 2056277 := bbase (se 8 (by rfl) ⟨12048, by rfl⟩ : syracuseStep 2056277 = 24097) (by norm_num)
theorem B2056301 : Blo 1370504 2056301 := bbase (se 3 (by rfl) ⟨385556, by rfl⟩ : syracuseStep 2056301 = 771113) (by norm_num)
theorem B2056325 : Blo 1370504 2056325 := bbase (se 4 (by rfl) ⟨192780, by rfl⟩ : syracuseStep 2056325 = 385561) (by norm_num)
theorem B1646741 : Blo 1370504 1646741 := bbase (se 6 (by rfl) ⟨38595, by rfl⟩ : syracuseStep 1646741 = 77191) (by norm_num)
theorem B2056349 : Blo 1370504 2056349 := bbase (se 3 (by rfl) ⟨385565, by rfl⟩ : syracuseStep 2056349 = 771131) (by norm_num)
theorem B2056373 : Blo 1370504 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B2056397 : Blo 1370504 2056397 := bbase (se 3 (by rfl) ⟨385574, by rfl⟩ : syracuseStep 2056397 = 771149) (by norm_num)
theorem B2056421 : Blo 1370504 2056421 := bbase (se 4 (by rfl) ⟨192789, by rfl⟩ : syracuseStep 2056421 = 385579) (by norm_num)
theorem B2056445 : Blo 1370504 2056445 := bbase (se 3 (by rfl) ⟨385583, by rfl⟩ : syracuseStep 2056445 = 771167) (by norm_num)
theorem B2056469 : Blo 1370504 2056469 := bbase (se 6 (by rfl) ⟨48198, by rfl⟩ : syracuseStep 2056469 = 96397) (by norm_num)
theorem B2056493 : Blo 1370504 2056493 := bbase (se 3 (by rfl) ⟨385592, by rfl⟩ : syracuseStep 2056493 = 771185) (by norm_num)
theorem B2056517 : Blo 1370504 2056517 := bbase (se 4 (by rfl) ⟨192798, by rfl⟩ : syracuseStep 2056517 = 385597) (by norm_num)
theorem B2056541 : Blo 1370504 2056541 := bbase (se 3 (by rfl) ⟨385601, by rfl⟩ : syracuseStep 2056541 = 771203) (by norm_num)
theorem B2056565 : Blo 1370504 2056565 := bbase (se 5 (by rfl) ⟨96401, by rfl⟩ : syracuseStep 2056565 = 192803) (by norm_num)
theorem B2056589 : Blo 1370504 2056589 := bbase (se 3 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 2056589 = 771221) (by norm_num)
theorem B1647001 : Blo 1370504 1647001 := bbase (se 2 (by rfl) ⟨617625, by rfl⟩ : syracuseStep 1647001 = 1235251) (by norm_num)
theorem B3293597 : Blo 1370504 3293597 := bbase (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) (by norm_num)
theorem B2056613 : Blo 1370504 2056613 := bbase (se 4 (by rfl) ⟨192807, by rfl⟩ : syracuseStep 2056613 = 385615) (by norm_num)
theorem B2056637 : Blo 1370504 2056637 := bbase (se 3 (by rfl) ⟨385619, by rfl⟩ : syracuseStep 2056637 = 771239) (by norm_num)
theorem B4628933 : Blo 1370504 4628933 := bbase (se 4 (by rfl) ⟨433962, by rfl⟩ : syracuseStep 4628933 = 867925) (by norm_num)
theorem B1647049 : Blo 1370504 1647049 := bbase (se 2 (by rfl) ⟨617643, by rfl⟩ : syracuseStep 1647049 = 1235287) (by norm_num)
theorem B2113997 : Blo 1370504 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B2056661 : Blo 1370504 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B8028629 : Blo 1370504 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B2056685 : Blo 1370504 2056685 := bbase (se 3 (by rfl) ⟨385628, by rfl⟩ : syracuseStep 2056685 = 771257) (by norm_num)
theorem B2056709 : Blo 1370504 2056709 := bbase (se 4 (by rfl) ⟨192816, by rfl⟩ : syracuseStep 2056709 = 385633) (by norm_num)
theorem B2056733 : Blo 1370504 2056733 := bbase (se 3 (by rfl) ⟨385637, by rfl⟩ : syracuseStep 2056733 = 771275) (by norm_num)
theorem B2056757 : Blo 1370504 2056757 := bbase (se 5 (by rfl) ⟨96410, by rfl⟩ : syracuseStep 2056757 = 192821) (by norm_num)
theorem B2056781 : Blo 1370504 2056781 := bbase (se 3 (by rfl) ⟨385646, by rfl⟩ : syracuseStep 2056781 = 771293) (by norm_num)
theorem B3293789 : Blo 1370504 3293789 := bbase (se 3 (by rfl) ⟨617585, by rfl⟩ : syracuseStep 3293789 = 1235171) (by norm_num)
theorem B2056805 : Blo 1370504 2056805 := bbase (se 4 (by rfl) ⟨192825, by rfl⟩ : syracuseStep 2056805 = 385651) (by norm_num)
theorem B2056829 : Blo 1370504 2056829 := bbase (se 3 (by rfl) ⟨385655, by rfl⟩ : syracuseStep 2056829 = 771311) (by norm_num)
theorem B6939269 : Blo 1370504 6939269 := bbase (se 4 (by rfl) ⟨650556, by rfl⟩ : syracuseStep 6939269 = 1301113) (by norm_num)
theorem B2056853 : Blo 1370504 2056853 := bbase (se 6 (by rfl) ⟨48207, by rfl⟩ : syracuseStep 2056853 = 96415) (by norm_num)
theorem B2056877 : Blo 1370504 2056877 := bbase (se 3 (by rfl) ⟨385664, by rfl⟩ : syracuseStep 2056877 = 771329) (by norm_num)
theorem B2056901 : Blo 1370504 2056901 := bbase (se 4 (by rfl) ⟨192834, by rfl⟩ : syracuseStep 2056901 = 385669) (by norm_num)
theorem B2056925 : Blo 1370504 2056925 := bbase (se 3 (by rfl) ⟨385673, by rfl⟩ : syracuseStep 2056925 = 771347) (by norm_num)
theorem B2056949 : Blo 1370504 2056949 := bbase (se 5 (by rfl) ⟨96419, by rfl⟩ : syracuseStep 2056949 = 192839) (by norm_num)
theorem B2056973 : Blo 1370504 2056973 := bbase (se 3 (by rfl) ⟨385682, by rfl⟩ : syracuseStep 2056973 = 771365) (by norm_num)
theorem B2056997 : Blo 1370504 2056997 := bbase (se 4 (by rfl) ⟨192843, by rfl⟩ : syracuseStep 2056997 = 385687) (by norm_num)
theorem B2057021 : Blo 1370504 2057021 := bbase (se 3 (by rfl) ⟨385691, by rfl⟩ : syracuseStep 2057021 = 771383) (by norm_num)
theorem B2057045 : Blo 1370504 2057045 := bbase (se 9 (by rfl) ⟨6026, by rfl⟩ : syracuseStep 2057045 = 12053) (by norm_num)
theorem B2057069 : Blo 1370504 2057069 := bbase (se 3 (by rfl) ⟨385700, by rfl⟩ : syracuseStep 2057069 = 771401) (by norm_num)
theorem B4629365 : Blo 1370504 4629365 := bbase (se 5 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 4629365 = 434003) (by norm_num)
theorem B2057093 : Blo 1370504 2057093 := bbase (se 4 (by rfl) ⟨192852, by rfl⟩ : syracuseStep 2057093 = 385705) (by norm_num)
theorem B2057117 : Blo 1370504 2057117 := bbase (se 3 (by rfl) ⟨385709, by rfl⟩ : syracuseStep 2057117 = 771419) (by norm_num)
theorem B2057141 : Blo 1370504 2057141 := bbase (se 5 (by rfl) ⟨96428, by rfl⟩ : syracuseStep 2057141 = 192857) (by norm_num)
theorem B4940741 : Blo 1370504 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B2057165 : Blo 1370504 2057165 := bbase (se 3 (by rfl) ⟨385718, by rfl⟩ : syracuseStep 2057165 = 771437) (by norm_num)
theorem B2057189 : Blo 1370504 2057189 := bbase (se 4 (by rfl) ⟨192861, by rfl⟩ : syracuseStep 2057189 = 385723) (by norm_num)
theorem B2057213 : Blo 1370504 2057213 := bbase (se 3 (by rfl) ⟨385727, by rfl⟩ : syracuseStep 2057213 = 771455) (by norm_num)
theorem B6251525 : Blo 1370504 6251525 := bbase (se 4 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 6251525 = 1172161) (by norm_num)
theorem B2057237 : Blo 1370504 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B2057261 : Blo 1370504 2057261 := bbase (se 3 (by rfl) ⟨385736, by rfl⟩ : syracuseStep 2057261 = 771473) (by norm_num)
theorem B8782901 : Blo 1370504 8782901 := bbase (se 5 (by rfl) ⟨411698, by rfl⟩ : syracuseStep 8782901 = 823397) (by norm_num)
theorem B2057285 : Blo 1370504 2057285 := bbase (se 4 (by rfl) ⟨192870, by rfl⟩ : syracuseStep 2057285 = 385741) (by norm_num)
theorem B2057309 : Blo 1370504 2057309 := bbase (se 3 (by rfl) ⟨385745, by rfl⟩ : syracuseStep 2057309 = 771491) (by norm_num)
theorem B1647721 : Blo 1370504 1647721 := bbase (se 2 (by rfl) ⟨617895, by rfl⟩ : syracuseStep 1647721 = 1235791) (by norm_num)
theorem B2057333 : Blo 1370504 2057333 := bbase (se 5 (by rfl) ⟨96437, by rfl⟩ : syracuseStep 2057333 = 192875) (by norm_num)
theorem B2057357 : Blo 1370504 2057357 := bbase (se 3 (by rfl) ⟨385754, by rfl⟩ : syracuseStep 2057357 = 771509) (by norm_num)
theorem B2196629 : Blo 1370504 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2057381 : Blo 1370504 2057381 := bbase (se 4 (by rfl) ⟨192879, by rfl⟩ : syracuseStep 2057381 = 385759) (by norm_num)
theorem B2057405 : Blo 1370504 2057405 := bbase (se 3 (by rfl) ⟨385763, by rfl⟩ : syracuseStep 2057405 = 771527) (by norm_num)
theorem B2057429 : Blo 1370504 2057429 := bbase (se 7 (by rfl) ⟨24110, by rfl⟩ : syracuseStep 2057429 = 48221) (by norm_num)
theorem B2057453 : Blo 1370504 2057453 := bbase (se 3 (by rfl) ⟨385772, by rfl⟩ : syracuseStep 2057453 = 771545) (by norm_num)
theorem B2057477 : Blo 1370504 2057477 := bbase (se 4 (by rfl) ⟨192888, by rfl⟩ : syracuseStep 2057477 = 385777) (by norm_num)
theorem B2057501 : Blo 1370504 2057501 := bbase (se 3 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 2057501 = 771563) (by norm_num)
theorem B4629797 : Blo 1370504 4629797 := bbase (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) (by norm_num)
theorem B2057525 : Blo 1370504 2057525 := bbase (se 5 (by rfl) ⟨96446, by rfl⟩ : syracuseStep 2057525 = 192893) (by norm_num)
theorem B2057549 : Blo 1370504 2057549 := bbase (se 3 (by rfl) ⟨385790, by rfl⟩ : syracuseStep 2057549 = 771581) (by norm_num)
theorem B2196821 : Blo 1370504 2196821 := bbase (se 12 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2196821 = 1609) (by norm_num)
theorem B2057573 : Blo 1370504 2057573 := bbase (se 4 (by rfl) ⟨192897, by rfl⟩ : syracuseStep 2057573 = 385795) (by norm_num)
theorem B2057597 : Blo 1370504 2057597 := bbase (se 3 (by rfl) ⟨385799, by rfl⟩ : syracuseStep 2057597 = 771599) (by norm_num)
theorem B2057621 : Blo 1370504 2057621 := bbase (se 6 (by rfl) ⟨48225, by rfl⟩ : syracuseStep 2057621 = 96451) (by norm_num)
theorem B2057645 : Blo 1370504 2057645 := bbase (se 3 (by rfl) ⟨385808, by rfl⟩ : syracuseStep 2057645 = 771617) (by norm_num)
theorem B2057669 : Blo 1370504 2057669 := bbase (se 4 (by rfl) ⟨192906, by rfl⟩ : syracuseStep 2057669 = 385813) (by norm_num)
theorem B2344405 : Blo 1370504 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B2057693 : Blo 1370504 2057693 := bbase (se 3 (by rfl) ⟨385817, by rfl⟩ : syracuseStep 2057693 = 771635) (by norm_num)
theorem B7808501 : Blo 1370504 7808501 := bbase (se 5 (by rfl) ⟨366023, by rfl⟩ : syracuseStep 7808501 = 732047) (by norm_num)
theorem B2057717 : Blo 1370504 2057717 := bbase (se 5 (by rfl) ⟨96455, by rfl⟩ : syracuseStep 2057717 = 192911) (by norm_num)
theorem B2057741 : Blo 1370504 2057741 := bbase (se 3 (by rfl) ⟨385826, by rfl⟩ : syracuseStep 2057741 = 771653) (by norm_num)
theorem B5858837 : Blo 1370504 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B2057765 : Blo 1370504 2057765 := bbase (se 4 (by rfl) ⟨192915, by rfl⟩ : syracuseStep 2057765 = 385831) (by norm_num)
theorem B2967101 : Blo 1370504 2967101 := bbase (se 3 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 2967101 = 1112663) (by norm_num)
theorem B2057789 : Blo 1370504 2057789 := bbase (se 3 (by rfl) ⟨385835, by rfl⟩ : syracuseStep 2057789 = 771671) (by norm_num)
theorem B2057813 : Blo 1370504 2057813 := bbase (se 8 (by rfl) ⟨12057, by rfl⟩ : syracuseStep 2057813 = 24115) (by norm_num)
theorem B2057837 : Blo 1370504 2057837 := bbase (se 3 (by rfl) ⟨385844, by rfl⟩ : syracuseStep 2057837 = 771689) (by norm_num)
theorem B2057861 : Blo 1370504 2057861 := bbase (se 4 (by rfl) ⟨192924, by rfl⟩ : syracuseStep 2057861 = 385849) (by norm_num)
theorem B2057885 : Blo 1370504 2057885 := bbase (se 3 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 2057885 = 771707) (by norm_num)
theorem B4171429 : Blo 1370504 4171429 := bbase (se 4 (by rfl) ⟨391071, by rfl⟩ : syracuseStep 4171429 = 782143) (by norm_num)
theorem B2057909 : Blo 1370504 2057909 := bbase (se 5 (by rfl) ⟨96464, by rfl⟩ : syracuseStep 2057909 = 192929) (by norm_num)
theorem B1541821 : Blo 1370504 1541821 := bbase (se 3 (by rfl) ⟨289091, by rfl⟩ : syracuseStep 1541821 = 578183) (by norm_num)
theorem B2057933 : Blo 1370504 2057933 := bbase (se 3 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 2057933 = 771725) (by norm_num)
theorem B4630229 : Blo 1370504 4630229 := bbase (se 7 (by rfl) ⟨54260, by rfl⟩ : syracuseStep 4630229 = 108521) (by norm_num)
theorem B1541857 : Blo 1370504 1541857 := bbase (se 2 (by rfl) ⟨578196, by rfl⟩ : syracuseStep 1541857 = 1156393) (by norm_num)
theorem B2057957 : Blo 1370504 2057957 := bbase (se 4 (by rfl) ⟨192933, by rfl⟩ : syracuseStep 2057957 = 385867) (by norm_num)
theorem B2057981 : Blo 1370504 2057981 := bbase (se 3 (by rfl) ⟨385871, by rfl⟩ : syracuseStep 2057981 = 771743) (by norm_num)
theorem B1541893 : Blo 1370504 1541893 := bbase (se 4 (by rfl) ⟨144552, by rfl⟩ : syracuseStep 1541893 = 289105) (by norm_num)
theorem B2058005 : Blo 1370504 2058005 := bbase (se 6 (by rfl) ⟨48234, by rfl⟩ : syracuseStep 2058005 = 96469) (by norm_num)
theorem B1541929 : Blo 1370504 1541929 := bbase (se 2 (by rfl) ⟨578223, by rfl⟩ : syracuseStep 1541929 = 1156447) (by norm_num)
theorem B1541965 : Blo 1370504 1541965 := bbase (se 3 (by rfl) ⟨289118, by rfl⟩ : syracuseStep 1541965 = 578237) (by norm_num)
theorem B1542001 : Blo 1370504 1542001 := bbase (se 2 (by rfl) ⟨578250, by rfl⟩ : syracuseStep 1542001 = 1156501) (by norm_num)
theorem B1542037 : Blo 1370504 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B6940565 : Blo 1370504 6940565 := bbase (se 6 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 6940565 = 325339) (by norm_num)
theorem B1542073 : Blo 1370504 1542073 := bbase (se 2 (by rfl) ⟨578277, by rfl⟩ : syracuseStep 1542073 = 1156555) (by norm_num)
theorem B1542109 : Blo 1370504 1542109 := bbase (se 3 (by rfl) ⟨289145, by rfl⟩ : syracuseStep 1542109 = 578291) (by norm_num)
theorem B4392949 : Blo 1370504 4392949 := bbase (se 5 (by rfl) ⟨205919, by rfl⟩ : syracuseStep 4392949 = 411839) (by norm_num)
theorem B1542145 : Blo 1370504 1542145 := bbase (se 2 (by rfl) ⟨578304, by rfl⟩ : syracuseStep 1542145 = 1156609) (by norm_num)
theorem B1542181 : Blo 1370504 1542181 := bbase (se 4 (by rfl) ⟨144579, by rfl⟩ : syracuseStep 1542181 = 289159) (by norm_num)
theorem B2377765 : Blo 1370504 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B1542217 : Blo 1370504 1542217 := bbase (se 2 (by rfl) ⟨578331, by rfl⟩ : syracuseStep 1542217 = 1156663) (by norm_num)
theorem B1542253 : Blo 1370504 1542253 := bbase (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) (by norm_num)
theorem B1542289 : Blo 1370504 1542289 := bbase (se 2 (by rfl) ⟨578358, by rfl⟩ : syracuseStep 1542289 = 1156717) (by norm_num)
theorem B1542325 : Blo 1370504 1542325 := bbase (se 5 (by rfl) ⟨72296, by rfl⟩ : syracuseStep 1542325 = 144593) (by norm_num)
theorem B1542361 : Blo 1370504 1542361 := bbase (se 2 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 1542361 = 1156771) (by norm_num)
theorem B4393205 : Blo 1370504 4393205 := bbase (se 5 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 4393205 = 411863) (by norm_num)
theorem B1542397 : Blo 1370504 1542397 := bbase (se 3 (by rfl) ⟨289199, by rfl⟩ : syracuseStep 1542397 = 578399) (by norm_num)
theorem B2345213 : Blo 1370504 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B1952029 : Blo 1370504 1952029 := bbase (se 3 (by rfl) ⟨366005, by rfl⟩ : syracuseStep 1952029 = 732011) (by norm_num)
theorem B1542433 : Blo 1370504 1542433 := bbase (se 2 (by rfl) ⟨578412, by rfl⟩ : syracuseStep 1542433 = 1156825) (by norm_num)
theorem B1542469 : Blo 1370504 1542469 := bbase (se 4 (by rfl) ⟨144606, by rfl⟩ : syracuseStep 1542469 = 289213) (by norm_num)
theorem B3008845 : Blo 1370504 3008845 := bbase (se 3 (by rfl) ⟨564158, by rfl⟩ : syracuseStep 3008845 = 1128317) (by norm_num)
theorem B1542505 : Blo 1370504 1542505 := bbase (se 2 (by rfl) ⟨578439, by rfl⟩ : syracuseStep 1542505 = 1156879) (by norm_num)
theorem B1542541 : Blo 1370504 1542541 := bbase (se 3 (by rfl) ⟨289226, by rfl⟩ : syracuseStep 1542541 = 578453) (by norm_num)
theorem B1542577 : Blo 1370504 1542577 := bbase (se 2 (by rfl) ⟨578466, by rfl⟩ : syracuseStep 1542577 = 1156933) (by norm_num)
theorem B1542613 : Blo 1370504 1542613 := bbase (se 7 (by rfl) ⟨18077, by rfl⟩ : syracuseStep 1542613 = 36155) (by norm_num)
theorem B1542649 : Blo 1370504 1542649 := bbase (se 2 (by rfl) ⟨578493, by rfl⟩ : syracuseStep 1542649 = 1156987) (by norm_num)
theorem B3295741 : Blo 1370504 3295741 := bbase (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) (by norm_num)
theorem B1542685 : Blo 1370504 1542685 := bbase (se 3 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 1542685 = 578507) (by norm_num)
theorem B1542721 : Blo 1370504 1542721 := bbase (se 2 (by rfl) ⟨578520, by rfl⟩ : syracuseStep 1542721 = 1157041) (by norm_num)
theorem B1542757 : Blo 1370504 1542757 := bbase (se 4 (by rfl) ⟨144633, by rfl⟩ : syracuseStep 1542757 = 289267) (by norm_num)
theorem B2312813 : Blo 1370504 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B1952365 : Blo 1370504 1952365 := bbase (se 3 (by rfl) ⟨366068, by rfl⟩ : syracuseStep 1952365 = 732137) (by norm_num)
theorem B1542793 : Blo 1370504 1542793 := bbase (se 2 (by rfl) ⟨578547, by rfl⟩ : syracuseStep 1542793 = 1157095) (by norm_num)
theorem B1542829 : Blo 1370504 1542829 := bbase (se 3 (by rfl) ⟨289280, by rfl⟩ : syracuseStep 1542829 = 578561) (by norm_num)
theorem B1542865 : Blo 1370504 1542865 := bbase (se 2 (by rfl) ⟨578574, by rfl⟩ : syracuseStep 1542865 = 1157149) (by norm_num)
theorem B2312941 : Blo 1370504 2312941 := bbase (se 3 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 2312941 = 867353) (by norm_num)
theorem B1542901 : Blo 1370504 1542901 := bbase (se 5 (by rfl) ⟨72323, by rfl⟩ : syracuseStep 1542901 = 144647) (by norm_num)
theorem B1542937 : Blo 1370504 1542937 := bbase (se 2 (by rfl) ⟨578601, by rfl⟩ : syracuseStep 1542937 = 1157203) (by norm_num)
theorem B1542973 : Blo 1370504 1542973 := bbase (se 3 (by rfl) ⟨289307, by rfl⟩ : syracuseStep 1542973 = 578615) (by norm_num)
theorem B2313029 : Blo 1370504 2313029 := bbase (se 4 (by rfl) ⟨216846, by rfl⟩ : syracuseStep 2313029 = 433693) (by norm_num)
theorem B1952581 : Blo 1370504 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B1543009 : Blo 1370504 1543009 := bbase (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) (by norm_num)
theorem B1543045 : Blo 1370504 1543045 := bbase (se 4 (by rfl) ⟨144660, by rfl⟩ : syracuseStep 1543045 = 289321) (by norm_num)
theorem B1543081 : Blo 1370504 1543081 := bbase (se 2 (by rfl) ⟨578655, by rfl⟩ : syracuseStep 1543081 = 1157311) (by norm_num)
theorem B2313157 : Blo 1370504 2313157 := bbase (se 4 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 2313157 = 433717) (by norm_num)
theorem B1543117 : Blo 1370504 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B18754517 : Blo 1370504 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B1543153 : Blo 1370504 1543153 := bbase (se 2 (by rfl) ⟨578682, by rfl⟩ : syracuseStep 1543153 = 1157365) (by norm_num)
theorem B1543189 : Blo 1370504 1543189 := bbase (se 6 (by rfl) ⟨36168, by rfl⟩ : syracuseStep 1543189 = 72337) (by norm_num)
theorem B2313245 : Blo 1370504 2313245 := bbase (se 3 (by rfl) ⟨433733, by rfl⟩ : syracuseStep 2313245 = 867467) (by norm_num)
theorem B1543225 : Blo 1370504 1543225 := bbase (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) (by norm_num)
theorem B1543261 : Blo 1370504 1543261 := bbase (se 3 (by rfl) ⟨289361, by rfl⟩ : syracuseStep 1543261 = 578723) (by norm_num)
theorem B2968693 : Blo 1370504 2968693 := bbase (se 5 (by rfl) ⟨139157, by rfl⟩ : syracuseStep 2968693 = 278315) (by norm_num)
theorem B1543297 : Blo 1370504 1543297 := bbase (se 2 (by rfl) ⟨578736, by rfl⟩ : syracuseStep 1543297 = 1157473) (by norm_num)
theorem B2256005 : Blo 1370504 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B2313373 : Blo 1370504 2313373 := bbase (se 3 (by rfl) ⟨433757, by rfl⟩ : syracuseStep 2313373 = 867515) (by norm_num)
theorem B6941861 : Blo 1370504 6941861 := bbase (se 4 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 6941861 = 1301599) (by norm_num)
theorem B1543333 : Blo 1370504 1543333 := bbase (se 4 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 1543333 = 289375) (by norm_num)
theorem B1952957 : Blo 1370504 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B6589637 : Blo 1370504 6589637 := bbase (se 4 (by rfl) ⟨617778, by rfl⟩ : syracuseStep 6589637 = 1235557) (by norm_num)
theorem B1543369 : Blo 1370504 1543369 := bbase (se 2 (by rfl) ⟨578763, by rfl⟩ : syracuseStep 1543369 = 1157527) (by norm_num)
theorem B1543405 : Blo 1370504 1543405 := bbase (se 3 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 1543405 = 578777) (by norm_num)
theorem B2313461 : Blo 1370504 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B1543441 : Blo 1370504 1543441 := bbase (se 2 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 1543441 = 1157581) (by norm_num)
theorem B1543477 : Blo 1370504 1543477 := bbase (se 5 (by rfl) ⟨72350, by rfl⟩ : syracuseStep 1543477 = 144701) (by norm_num)
theorem B2313589 : Blo 1370504 2313589 := bbase (se 5 (by rfl) ⟨108449, by rfl⟩ : syracuseStep 2313589 = 216899) (by norm_num)
theorem B3083669 : Blo 1370504 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B3517877 : Blo 1370504 3517877 := bbase (se 5 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 3517877 = 329801) (by norm_num)
theorem B2313677 : Blo 1370504 2313677 := bbase (se 3 (by rfl) ⟨433814, by rfl⟩ : syracuseStep 2313677 = 867629) (by norm_num)
theorem B3706325 : Blo 1370504 3706325 := bbase (se 7 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 3706325 = 86867) (by norm_num)
theorem B3083741 : Blo 1370504 3083741 := bbase (se 3 (by rfl) ⟨578201, by rfl⟩ : syracuseStep 3083741 = 1156403) (by norm_num)
theorem B3083813 : Blo 1370504 3083813 := bbase (se 4 (by rfl) ⟨289107, by rfl⟩ : syracuseStep 3083813 = 578215) (by norm_num)
theorem B2313805 : Blo 1370504 2313805 := bbase (se 3 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 2313805 = 867677) (by norm_num)
theorem B8343125 : Blo 1370504 8343125 := bbase (se 8 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 8343125 = 97771) (by norm_num)
theorem B3083885 : Blo 1370504 3083885 := bbase (se 3 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 3083885 = 1156457) (by norm_num)
theorem B5205653 : Blo 1370504 5205653 := bbase (se 6 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 5205653 = 244015) (by norm_num)
theorem B2313893 : Blo 1370504 2313893 := bbase (se 4 (by rfl) ⟨216927, by rfl⟩ : syracuseStep 2313893 = 433855) (by norm_num)
theorem B3083957 : Blo 1370504 3083957 := bbase (se 5 (by rfl) ⟨144560, by rfl⟩ : syracuseStep 3083957 = 289121) (by norm_num)
theorem B3903157 : Blo 1370504 3903157 := bbase (se 5 (by rfl) ⟨182960, by rfl⟩ : syracuseStep 3903157 = 365921) (by norm_num)
theorem B13184693 : Blo 1370504 13184693 := bbase (se 5 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 13184693 = 1236065) (by norm_num)
theorem B2928325 : Blo 1370504 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B4067029 : Blo 1370504 4067029 := bbase (se 7 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 4067029 = 95321) (by norm_num)
theorem B3084029 : Blo 1370504 3084029 := bbase (se 3 (by rfl) ⟨578255, by rfl⟩ : syracuseStep 3084029 = 1156511) (by norm_num)
theorem B2314021 : Blo 1370504 2314021 := bbase (se 4 (by rfl) ⟨216939, by rfl⟩ : syracuseStep 2314021 = 433879) (by norm_num)
theorem B5279525 : Blo 1370504 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B3084101 : Blo 1370504 3084101 := bbase (se 4 (by rfl) ⟨289134, by rfl⟩ : syracuseStep 3084101 = 578269) (by norm_num)
theorem B3518309 : Blo 1370504 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B2314109 : Blo 1370504 2314109 := bbase (se 3 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 2314109 = 867791) (by norm_num)
theorem B3469189 : Blo 1370504 3469189 := bbase (se 4 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 3469189 = 650473) (by norm_num)
theorem B3084173 : Blo 1370504 3084173 := bbase (se 3 (by rfl) ⟨578282, by rfl⟩ : syracuseStep 3084173 = 1156565) (by norm_num)
theorem B5205941 : Blo 1370504 5205941 := bbase (se 5 (by rfl) ⟨244028, by rfl⟩ : syracuseStep 5205941 = 488057) (by norm_num)
theorem B3084245 : Blo 1370504 3084245 := bbase (se 7 (by rfl) ⟨36143, by rfl⟩ : syracuseStep 3084245 = 72287) (by norm_num)
theorem B3469301 : Blo 1370504 3469301 := bbase (se 5 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 3469301 = 325247) (by norm_num)
theorem B2314237 : Blo 1370504 2314237 := bbase (se 3 (by rfl) ⟨433919, by rfl⟩ : syracuseStep 2314237 = 867839) (by norm_num)
theorem B3084317 : Blo 1370504 3084317 := bbase (se 3 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 3084317 = 1156619) (by norm_num)
theorem B2314325 : Blo 1370504 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B3084389 : Blo 1370504 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B3084461 : Blo 1370504 3084461 := bbase (se 3 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 3084461 = 1156673) (by norm_num)
theorem B3469493 : Blo 1370504 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B2314453 : Blo 1370504 2314453 := bbase (se 7 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 2314453 = 54245) (by norm_num)
theorem B3084533 : Blo 1370504 3084533 := bbase (se 5 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 3084533 = 289175) (by norm_num)
theorem B2085149 : Blo 1370504 2085149 := bbase (se 3 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 2085149 = 781931) (by norm_num)
theorem B2314541 : Blo 1370504 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B10416437 : Blo 1370504 10416437 := bbase (se 5 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 10416437 = 976541) (by norm_num)
theorem B3084605 : Blo 1370504 3084605 := bbase (se 3 (by rfl) ⟨578363, by rfl⟩ : syracuseStep 3084605 = 1156727) (by norm_num)
theorem B2470213 : Blo 1370504 2470213 := bbase (se 4 (by rfl) ⟨231582, by rfl⟩ : syracuseStep 2470213 = 463165) (by norm_num)
theorem B2085197 : Blo 1370504 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B3567997 : Blo 1370504 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B3084677 : Blo 1370504 3084677 := bbase (se 4 (by rfl) ⟨289188, by rfl⟩ : syracuseStep 3084677 = 578377) (by norm_num)
theorem B2470285 : Blo 1370504 2470285 := bbase (se 3 (by rfl) ⟨463178, by rfl⟩ : syracuseStep 2470285 = 926357) (by norm_num)
theorem B2314669 : Blo 1370504 2314669 := bbase (se 3 (by rfl) ⟨434000, by rfl⟩ : syracuseStep 2314669 = 868001) (by norm_num)
theorem B6943157 : Blo 1370504 6943157 := bbase (se 5 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 6943157 = 650921) (by norm_num)
theorem B3084749 : Blo 1370504 3084749 := bbase (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) (by norm_num)
theorem B2200069 : Blo 1370504 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B2314757 : Blo 1370504 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B3469837 : Blo 1370504 3469837 := bbase (se 3 (by rfl) ⟨650594, by rfl⟩ : syracuseStep 3469837 = 1301189) (by norm_num)
theorem B3084821 : Blo 1370504 3084821 := bbase (se 6 (by rfl) ⟨72300, by rfl⟩ : syracuseStep 3084821 = 144601) (by norm_num)
theorem B2470429 : Blo 1370504 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B2929213 : Blo 1370504 2929213 := bbase (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) (by norm_num)
theorem B3084893 : Blo 1370504 3084893 := bbase (se 3 (by rfl) ⟨578417, by rfl⟩ : syracuseStep 3084893 = 1156835) (by norm_num)
theorem B3469949 : Blo 1370504 3469949 := bbase (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) (by norm_num)
theorem B2314885 : Blo 1370504 2314885 := bbase (se 4 (by rfl) ⟨217020, by rfl⟩ : syracuseStep 2314885 = 434041) (by norm_num)
theorem B3084965 : Blo 1370504 3084965 := bbase (se 4 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 3084965 = 578431) (by norm_num)
theorem B10408661 : Blo 1370504 10408661 := bbase (se 7 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 10408661 = 243953) (by norm_num)
theorem B2314973 : Blo 1370504 2314973 := bbase (se 3 (by rfl) ⟨434057, by rfl⟩ : syracuseStep 2314973 = 868115) (by norm_num)
theorem B3756773 : Blo 1370504 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B3085037 : Blo 1370504 3085037 := bbase (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) (by norm_num)
theorem B6591269 : Blo 1370504 6591269 := bbase (se 4 (by rfl) ⟨617931, by rfl⟩ : syracuseStep 6591269 = 1235863) (by norm_num)
theorem B3085109 : Blo 1370504 3085109 := bbase (se 5 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 3085109 = 289229) (by norm_num)
theorem B3470141 : Blo 1370504 3470141 := bbase (se 3 (by rfl) ⟨650651, by rfl⟩ : syracuseStep 3470141 = 1301303) (by norm_num)
theorem B2315101 : Blo 1370504 2315101 := bbase (se 3 (by rfl) ⟨434081, by rfl⟩ : syracuseStep 2315101 = 868163) (by norm_num)
theorem B1979245 : Blo 1370504 1979245 := bbase (se 3 (by rfl) ⟨371108, by rfl⟩ : syracuseStep 1979245 = 742217) (by norm_num)
theorem B3085181 : Blo 1370504 3085181 := bbase (se 3 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 3085181 = 1156943) (by norm_num)
theorem B2601877 : Blo 1370504 2601877 := bbase (se 6 (by rfl) ⟨60981, by rfl⟩ : syracuseStep 2601877 = 121963) (by norm_num)
theorem B5952437 : Blo 1370504 5952437 := bbase (se 5 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 5952437 = 558041) (by norm_num)
theorem B2315189 : Blo 1370504 2315189 := bbase (se 5 (by rfl) ⟨108524, by rfl⟩ : syracuseStep 2315189 = 217049) (by norm_num)
theorem B3085253 : Blo 1370504 3085253 := bbase (se 4 (by rfl) ⟨289242, by rfl⟩ : syracuseStep 3085253 = 578485) (by norm_num)
theorem B3085325 : Blo 1370504 3085325 := bbase (se 3 (by rfl) ⟨578498, by rfl⟩ : syracuseStep 3085325 = 1156997) (by norm_num)
theorem B2929709 : Blo 1370504 2929709 := bbase (se 3 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 2929709 = 1098641) (by norm_num)
theorem B2602037 : Blo 1370504 2602037 := bbase (se 5 (by rfl) ⟨121970, by rfl⟩ : syracuseStep 2602037 = 243941) (by norm_num)
theorem B4625477 : Blo 1370504 4625477 := bbase (se 4 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 4625477 = 867277) (by norm_num)
theorem B1782853 : Blo 1370504 1782853 := bbase (se 4 (by rfl) ⟨167142, by rfl⟩ : syracuseStep 1782853 = 334285) (by norm_num)
theorem B3085397 : Blo 1370504 3085397 := bbase (se 8 (by rfl) ⟨18078, by rfl⟩ : syracuseStep 3085397 = 36157) (by norm_num)
theorem B5207125 : Blo 1370504 5207125 := bbase (se 8 (by rfl) ⟨30510, by rfl⟩ : syracuseStep 5207125 = 61021) (by norm_num)
theorem B3470485 : Blo 1370504 3470485 := bbase (se 6 (by rfl) ⟨81339, by rfl⟩ : syracuseStep 3470485 = 162679) (by norm_num)
theorem B3904661 : Blo 1370504 3904661 := bbase (se 6 (by rfl) ⟨91515, by rfl⟩ : syracuseStep 3904661 = 183031) (by norm_num)
theorem B3085469 : Blo 1370504 3085469 := bbase (se 3 (by rfl) ⟨578525, by rfl⟩ : syracuseStep 3085469 = 1157051) (by norm_num)
theorem B2602181 : Blo 1370504 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B3085541 : Blo 1370504 3085541 := bbase (se 4 (by rfl) ⟨289269, by rfl⟩ : syracuseStep 3085541 = 578539) (by norm_num)
theorem B3470597 : Blo 1370504 3470597 := bbase (se 4 (by rfl) ⟨325368, by rfl⟩ : syracuseStep 3470597 = 650737) (by norm_num)
theorem B3085613 : Blo 1370504 3085613 := bbase (se 3 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 3085613 = 1157105) (by norm_num)
theorem B3085685 : Blo 1370504 3085685 := bbase (se 5 (by rfl) ⟨144641, by rfl⟩ : syracuseStep 3085685 = 289283) (by norm_num)
theorem B2471293 : Blo 1370504 2471293 := bbase (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) (by norm_num)
theorem B5207429 : Blo 1370504 5207429 := bbase (se 4 (by rfl) ⟨488196, by rfl⟩ : syracuseStep 5207429 = 976393) (by norm_num)
theorem B3085757 : Blo 1370504 3085757 := bbase (se 3 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 3085757 = 1157159) (by norm_num)
theorem B3470789 : Blo 1370504 3470789 := bbase (se 4 (by rfl) ⟨325386, by rfl⟩ : syracuseStep 3470789 = 650773) (by norm_num)
theorem B5559749 : Blo 1370504 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B1463761 : Blo 1370504 1463761 := bbase (se 2 (by rfl) ⟨548910, by rfl⟩ : syracuseStep 1463761 = 1097821) (by norm_num)
theorem B2471381 : Blo 1370504 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B2602469 : Blo 1370504 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B4625909 : Blo 1370504 4625909 := bbase (se 5 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 4625909 = 433679) (by norm_num)
theorem B3085829 : Blo 1370504 3085829 := bbase (se 4 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 3085829 = 578593) (by norm_num)
theorem B3085901 : Blo 1370504 3085901 := bbase (se 3 (by rfl) ⟨578606, by rfl⟩ : syracuseStep 3085901 = 1157213) (by norm_num)
theorem B5854805 : Blo 1370504 5854805 := bbase (se 8 (by rfl) ⟨34305, by rfl⟩ : syracuseStep 5854805 = 68611) (by norm_num)
theorem B2602621 : Blo 1370504 2602621 := bbase (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) (by norm_num)
theorem B3085973 : Blo 1370504 3085973 := bbase (se 6 (by rfl) ⟨72327, by rfl⟩ : syracuseStep 3085973 = 144655) (by norm_num)
theorem B6944453 : Blo 1370504 6944453 := bbase (se 4 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 6944453 = 1302085) (by norm_num)
theorem B3086045 : Blo 1370504 3086045 := bbase (se 3 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 3086045 = 1157267) (by norm_num)
theorem B7034645 : Blo 1370504 7034645 := bbase (se 6 (by rfl) ⟨164874, by rfl⟩ : syracuseStep 7034645 = 329749) (by norm_num)
theorem B3471133 : Blo 1370504 3471133 := bbase (se 3 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 3471133 = 1301675) (by norm_num)
theorem B3086117 : Blo 1370504 3086117 := bbase (se 4 (by rfl) ⟨289323, by rfl⟩ : syracuseStep 3086117 = 578647) (by norm_num)
theorem B1783625 : Blo 1370504 1783625 := bbase (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) (by norm_num)
theorem B3086189 : Blo 1370504 3086189 := bbase (se 3 (by rfl) ⟨578660, by rfl⟩ : syracuseStep 3086189 = 1157321) (by norm_num)
theorem B7919477 : Blo 1370504 7919477 := bbase (se 5 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 7919477 = 742451) (by norm_num)
theorem B1464193 : Blo 1370504 1464193 := bbase (se 2 (by rfl) ⟨549072, by rfl⟩ : syracuseStep 1464193 = 1098145) (by norm_num)
theorem B2471813 : Blo 1370504 2471813 := bbase (se 4 (by rfl) ⟨231732, by rfl⟩ : syracuseStep 2471813 = 463465) (by norm_num)
theorem B3471245 : Blo 1370504 3471245 := bbase (se 3 (by rfl) ⟨650858, by rfl⟩ : syracuseStep 3471245 = 1301717) (by norm_num)
theorem B4626341 : Blo 1370504 4626341 := bbase (se 4 (by rfl) ⟨433719, by rfl⟩ : syracuseStep 4626341 = 867439) (by norm_num)
theorem B1669033 : Blo 1370504 1669033 := bbase (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) (by norm_num)
theorem B2602925 : Blo 1370504 2602925 := bbase (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) (by norm_num)
theorem B3086261 : Blo 1370504 3086261 := bbase (se 5 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 3086261 = 289337) (by norm_num)
theorem B1464265 : Blo 1370504 1464265 := bbase (se 2 (by rfl) ⟨549099, by rfl⟩ : syracuseStep 1464265 = 1098199) (by norm_num)
theorem B1734625 : Blo 1370504 1734625 := bbase (se 2 (by rfl) ⟨650484, by rfl⟩ : syracuseStep 1734625 = 1300969) (by norm_num)
theorem B3086333 : Blo 1370504 3086333 := bbase (se 3 (by rfl) ⟨578687, by rfl⟩ : syracuseStep 3086333 = 1157375) (by norm_num)
theorem B12515381 : Blo 1370504 12515381 := bbase (se 5 (by rfl) ⟨586658, by rfl⟩ : syracuseStep 12515381 = 1173317) (by norm_num)
theorem B3086405 : Blo 1370504 3086405 := bbase (se 4 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 3086405 = 578701) (by norm_num)
theorem B3471437 : Blo 1370504 3471437 := bbase (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) (by norm_num)
theorem B1734797 : Blo 1370504 1734797 := bbase (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) (by norm_num)
theorem B3086477 : Blo 1370504 3086477 := bbase (se 3 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 3086477 = 1157429) (by norm_num)
theorem B2472101 : Blo 1370504 2472101 := bbase (se 4 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 2472101 = 463519) (by norm_num)
theorem B1734853 : Blo 1370504 1734853 := bbase (se 4 (by rfl) ⟨162642, by rfl⟩ : syracuseStep 1734853 = 325285) (by norm_num)
theorem B3086549 : Blo 1370504 3086549 := bbase (se 7 (by rfl) ⟨36170, by rfl⟩ : syracuseStep 3086549 = 72341) (by norm_num)
theorem B3086621 : Blo 1370504 3086621 := bbase (se 3 (by rfl) ⟨578741, by rfl⟩ : syracuseStep 3086621 = 1157483) (by norm_num)
theorem B1734949 : Blo 1370504 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B2226469 : Blo 1370504 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B1464637 : Blo 1370504 1464637 := bbase (se 3 (by rfl) ⟨274619, by rfl⟩ : syracuseStep 1464637 = 549239) (by norm_num)
theorem B4626773 : Blo 1370504 4626773 := bbase (se 10 (by rfl) ⟨6777, by rfl⟩ : syracuseStep 4626773 = 13555) (by norm_num)
theorem B3086693 : Blo 1370504 3086693 := bbase (se 4 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 3086693 = 578755) (by norm_num)
theorem B3471781 : Blo 1370504 3471781 := bbase (se 4 (by rfl) ⟨325479, by rfl⟩ : syracuseStep 3471781 = 650959) (by norm_num)
theorem B3086765 : Blo 1370504 3086765 := bbase (se 3 (by rfl) ⟨578768, by rfl⟩ : syracuseStep 3086765 = 1157537) (by norm_num)
theorem B1735121 : Blo 1370504 1735121 := bbase (se 2 (by rfl) ⟨650670, by rfl⟩ : syracuseStep 1735121 = 1301341) (by norm_num)
theorem B3086837 : Blo 1370504 3086837 := bbase (se 5 (by rfl) ⟨144695, by rfl⟩ : syracuseStep 3086837 = 289391) (by norm_num)
theorem B1735177 : Blo 1370504 1735177 := bbase (se 2 (by rfl) ⟨650691, by rfl⟩ : syracuseStep 1735177 = 1301383) (by norm_num)
theorem B3471893 : Blo 1370504 3471893 := bbase (se 6 (by rfl) ⟨81372, by rfl⟩ : syracuseStep 3471893 = 162745) (by norm_num)
theorem B3086909 : Blo 1370504 3086909 := bbase (se 3 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 3086909 = 1157591) (by norm_num)
theorem B2226781 : Blo 1370504 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B1735273 : Blo 1370504 1735273 := bbase (se 2 (by rfl) ⟨650727, by rfl⟩ : syracuseStep 1735273 = 1301455) (by norm_num)
theorem B3086981 : Blo 1370504 3086981 := bbase (se 4 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 3086981 = 578809) (by norm_num)
theorem B2603677 : Blo 1370504 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B2226845 : Blo 1370504 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B1465013 : Blo 1370504 1465013 := bbase (se 5 (by rfl) ⟨68672, by rfl⟩ : syracuseStep 1465013 = 137345) (by norm_num)
theorem B3906245 : Blo 1370504 3906245 := bbase (se 4 (by rfl) ⟨366210, by rfl⟩ : syracuseStep 3906245 = 732421) (by norm_num)
theorem B3472085 : Blo 1370504 3472085 := bbase (se 7 (by rfl) ⟨40688, by rfl⟩ : syracuseStep 3472085 = 81377) (by norm_num)
theorem B4455125 : Blo 1370504 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1465085 : Blo 1370504 1465085 := bbase (se 3 (by rfl) ⟨274703, by rfl⟩ : syracuseStep 1465085 = 549407) (by norm_num)
theorem B4627205 : Blo 1370504 4627205 := bbase (se 4 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 4627205 = 867601) (by norm_num)
theorem B1735445 : Blo 1370504 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B2603821 : Blo 1370504 2603821 := bbase (se 3 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 2603821 = 976433) (by norm_num)
theorem B1735501 : Blo 1370504 1735501 := bbase (se 3 (by rfl) ⟨325406, by rfl⟩ : syracuseStep 1735501 = 650813) (by norm_num)
theorem B31652693 : Blo 1370504 31652693 := bbase (se 9 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 31652693 = 185465) (by norm_num)
theorem B5561189 : Blo 1370504 5561189 := bbase (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) (by norm_num)
theorem B1735597 : Blo 1370504 1735597 := bbase (se 3 (by rfl) ⟨325424, by rfl⟩ : syracuseStep 1735597 = 650849) (by norm_num)
theorem B2603981 : Blo 1370504 2603981 := bbase (se 3 (by rfl) ⟨488246, by rfl⟩ : syracuseStep 2603981 = 976493) (by norm_num)
theorem B6945749 : Blo 1370504 6945749 := bbase (se 7 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 6945749 = 162791) (by norm_num)
theorem B4168741 : Blo 1370504 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B3472429 : Blo 1370504 3472429 := bbase (se 3 (by rfl) ⟨651080, by rfl⟩ : syracuseStep 3472429 = 1302161) (by norm_num)
theorem B1735769 : Blo 1370504 1735769 := bbase (se 2 (by rfl) ⟨650913, by rfl⟩ : syracuseStep 1735769 = 1301827) (by norm_num)
theorem B3169373 : Blo 1370504 3169373 := bbase (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) (by norm_num)
theorem B2604125 : Blo 1370504 2604125 := bbase (se 3 (by rfl) ⟨488273, by rfl⟩ : syracuseStep 2604125 = 976547) (by norm_num)
theorem B4168837 : Blo 1370504 4168837 := bbase (se 4 (by rfl) ⟨390828, by rfl⟩ : syracuseStep 4168837 = 781657) (by norm_num)
theorem B1735825 : Blo 1370504 1735825 := bbase (se 2 (by rfl) ⟨650934, by rfl⟩ : syracuseStep 1735825 = 1301869) (by norm_num)
theorem B3472541 : Blo 1370504 3472541 := bbase (se 3 (by rfl) ⟨651101, by rfl⟩ : syracuseStep 3472541 = 1302203) (by norm_num)
theorem B4627637 : Blo 1370504 4627637 := bbase (se 5 (by rfl) ⟨216920, by rfl⟩ : syracuseStep 4627637 = 433841) (by norm_num)
theorem B1735921 : Blo 1370504 1735921 := bbase (se 2 (by rfl) ⟨650970, by rfl⟩ : syracuseStep 1735921 = 1301941) (by norm_num)
theorem B2817301 : Blo 1370504 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B7806293 : Blo 1370504 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B3472733 : Blo 1370504 3472733 := bbase (se 3 (by rfl) ⟨651137, by rfl⟩ : syracuseStep 3472733 = 1302275) (by norm_num)
theorem B3906917 : Blo 1370504 3906917 := bbase (se 4 (by rfl) ⟨366273, by rfl⟩ : syracuseStep 3906917 = 732547) (by norm_num)
theorem B3128701 : Blo 1370504 3128701 := bbase (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) (by norm_num)
theorem B2604413 : Blo 1370504 2604413 := bbase (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) (by norm_num)
theorem B1736093 : Blo 1370504 1736093 := bbase (se 3 (by rfl) ⟨325517, by rfl⟩ : syracuseStep 1736093 = 651035) (by norm_num)
theorem B9379253 : Blo 1370504 9379253 := bbase (se 5 (by rfl) ⟨439652, by rfl⟩ : syracuseStep 9379253 = 879305) (by norm_num)
theorem B4693445 : Blo 1370504 4693445 := bbase (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) (by norm_num)
theorem B1736149 : Blo 1370504 1736149 := bbase (se 7 (by rfl) ⟨20345, by rfl⟩ : syracuseStep 1736149 = 40691) (by norm_num)
theorem B2604565 : Blo 1370504 2604565 := bbase (se 6 (by rfl) ⟨61044, by rfl⟩ : syracuseStep 2604565 = 122089) (by norm_num)
theorem B1564213 : Blo 1370504 1564213 := bbase (se 5 (by rfl) ⟨73322, by rfl⟩ : syracuseStep 1564213 = 146645) (by norm_num)
theorem B1736245 : Blo 1370504 1736245 := bbase (se 5 (by rfl) ⟨81386, by rfl⟩ : syracuseStep 1736245 = 162773) (by norm_num)
theorem B2055773 : Blo 1370504 2055773 := bbase (se 3 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 2055773 = 770915) (by norm_num)
theorem B4628069 : Blo 1370504 4628069 := bbase (se 4 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 4628069 = 867763) (by norm_num)
theorem B2055797 : Blo 1370504 2055797 := bbase (se 5 (by rfl) ⟨96365, by rfl⟩ : syracuseStep 2055797 = 192731) (by norm_num)
theorem B2055821 : Blo 1370504 2055821 := bbase (se 3 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 2055821 = 770933) (by norm_num)
theorem B2817677 : Blo 1370504 2817677 := bbase (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) (by norm_num)
theorem B2055845 : Blo 1370504 2055845 := bbase (se 4 (by rfl) ⟨192735, by rfl⟩ : syracuseStep 2055845 = 385471) (by norm_num)
theorem B2055869 : Blo 1370504 2055869 := bbase (se 3 (by rfl) ⟨385475, by rfl⟩ : syracuseStep 2055869 = 770951) (by norm_num)
theorem B2637517 : Blo 1370504 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B2055893 : Blo 1370504 2055893 := bbase (se 7 (by rfl) ⟨24092, by rfl⟩ : syracuseStep 2055893 = 48185) (by norm_num)
theorem B1736417 : Blo 1370504 1736417 := bbase (se 2 (by rfl) ⟨651156, by rfl⟩ : syracuseStep 1736417 = 1302313) (by norm_num)
theorem B2055917 : Blo 1370504 2055917 := bbase (se 3 (by rfl) ⟨385484, by rfl⟩ : syracuseStep 2055917 = 770969) (by norm_num)
theorem B2055941 : Blo 1370504 2055941 := bbase (se 4 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 2055941 = 385489) (by norm_num)
theorem B2055965 : Blo 1370504 2055965 := bbase (se 3 (by rfl) ⟨385493, by rfl⟩ : syracuseStep 2055965 = 770987) (by norm_num)
theorem B2055989 : Blo 1370504 2055989 := bbase (se 5 (by rfl) ⟨96374, by rfl⟩ : syracuseStep 2055989 = 192749) (by norm_num)
theorem B2056013 : Blo 1370504 2056013 := bbase (se 3 (by rfl) ⟨385502, by rfl⟩ : syracuseStep 2056013 = 771005) (by norm_num)
theorem B2056037 : Blo 1370504 2056037 := bbase (se 4 (by rfl) ⟨192753, by rfl⟩ : syracuseStep 2056037 = 385507) (by norm_num)
theorem B2056061 : Blo 1370504 2056061 := bbase (se 3 (by rfl) ⟨385511, by rfl⟩ : syracuseStep 2056061 = 771023) (by norm_num)
theorem B2056085 : Blo 1370504 2056085 := bbase (se 6 (by rfl) ⟨48189, by rfl⟩ : syracuseStep 2056085 = 96379) (by norm_num)
theorem B2056109 : Blo 1370504 2056109 := bbase (se 3 (by rfl) ⟨385520, by rfl⟩ : syracuseStep 2056109 = 771041) (by norm_num)
theorem B2056133 : Blo 1370504 2056133 := bbase (se 4 (by rfl) ⟨192762, by rfl⟩ : syracuseStep 2056133 = 385525) (by norm_num)
theorem B2056157 : Blo 1370504 2056157 := bbase (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) (by norm_num)
theorem B2195437 : Blo 1370504 2195437 := bbase (se 3 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 2195437 = 823289) (by norm_num)
theorem B2056181 : Blo 1370504 2056181 := bbase (se 5 (by rfl) ⟨96383, by rfl⟩ : syracuseStep 2056181 = 192767) (by norm_num)
theorem B2056193 : Blo 1370504 2056193 := bstep (se 2 (by rfl) ⟨771072, by rfl⟩ : syracuseStep 2056193 = 1542145) B1542145
theorem B2056211 : Blo 1370504 2056211 := bstep (se 1 (by rfl) ⟨1542158, by rfl⟩ : syracuseStep 2056211 = 3084317) B3084317
theorem B2056241 : Blo 1370504 2056241 := bstep (se 2 (by rfl) ⟨771090, by rfl⟩ : syracuseStep 2056241 = 1542181) B1542181
theorem B3170353 : Blo 1370504 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B2056259 : Blo 1370504 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B2056289 : Blo 1370504 2056289 := bstep (se 2 (by rfl) ⟨771108, by rfl⟩ : syracuseStep 2056289 = 1542217) B1542217
theorem B2056307 : Blo 1370504 2056307 := bstep (se 1 (by rfl) ⟨1542230, by rfl⟩ : syracuseStep 2056307 = 3084461) B3084461
theorem B2056337 : Blo 1370504 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B2056355 : Blo 1370504 2056355 := bstep (se 1 (by rfl) ⟨1542266, by rfl⟩ : syracuseStep 2056355 = 3084533) B3084533
theorem B2056385 : Blo 1370504 2056385 := bstep (se 2 (by rfl) ⟨771144, by rfl⟩ : syracuseStep 2056385 = 1542289) B1542289
theorem B2056403 : Blo 1370504 2056403 := bstep (se 1 (by rfl) ⟨1542302, by rfl⟩ : syracuseStep 2056403 = 3084605) B3084605
theorem B4628717 : Blo 1370504 4628717 := bstep (se 3 (by rfl) ⟨867884, by rfl⟩ : syracuseStep 4628717 = 1735769) B1735769
theorem B2056433 : Blo 1370504 2056433 := bstep (se 2 (by rfl) ⟨771162, by rfl⟩ : syracuseStep 2056433 = 1542325) B1542325
theorem B2056451 : Blo 1370504 2056451 := bstep (se 1 (by rfl) ⟨1542338, by rfl⟩ : syracuseStep 2056451 = 3084677) B3084677
theorem B2195731 : Blo 1370504 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B2056481 : Blo 1370504 2056481 := bstep (se 2 (by rfl) ⟨771180, by rfl⟩ : syracuseStep 2056481 = 1542361) B1542361
theorem B4628771 : Blo 1370504 4628771 := bstep (se 1 (by rfl) ⟨3471578, by rfl⟩ : syracuseStep 4628771 = 6943157) B6943157
theorem B2056499 : Blo 1370504 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B15622469 : Blo 1370504 15622469 := bstep (se 4 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 15622469 = 2929213) B2929213
theorem B2056529 : Blo 1370504 2056529 := bstep (se 2 (by rfl) ⟨771198, by rfl⟩ : syracuseStep 2056529 = 1542397) B1542397
theorem B2056547 : Blo 1370504 2056547 := bstep (se 1 (by rfl) ⟨1542410, by rfl⟩ : syracuseStep 2056547 = 3084821) B3084821
theorem B2056577 : Blo 1370504 2056577 := bstep (se 2 (by rfl) ⟨771216, by rfl⟩ : syracuseStep 2056577 = 1542433) B1542433
theorem B4391309 : Blo 1370504 4391309 := bstep (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) B1646741
theorem B2056595 : Blo 1370504 2056595 := bstep (se 1 (by rfl) ⟨1542446, by rfl⟩ : syracuseStep 2056595 = 3084893) B3084893
theorem B3293617 : Blo 1370504 3293617 := bstep (se 2 (by rfl) ⟨1235106, by rfl⟩ : syracuseStep 3293617 = 2470213) B2470213
theorem B2056625 : Blo 1370504 2056625 := bstep (se 2 (by rfl) ⟨771234, by rfl⟩ : syracuseStep 2056625 = 1542469) B1542469
theorem B2056643 : Blo 1370504 2056643 := bstep (se 1 (by rfl) ⟨1542482, by rfl⟩ : syracuseStep 2056643 = 3084965) B3084965
theorem B2056673 : Blo 1370504 2056673 := bstep (se 2 (by rfl) ⟨771252, by rfl⟩ : syracuseStep 2056673 = 1542505) B1542505
theorem B6939107 : Blo 1370504 6939107 := bstep (se 1 (by rfl) ⟨5204330, by rfl⟩ : syracuseStep 6939107 = 10408661) B10408661
theorem B2056691 : Blo 1370504 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B3293713 : Blo 1370504 3293713 := bstep (se 2 (by rfl) ⟨1235142, by rfl⟩ : syracuseStep 3293713 = 2470285) B2470285
theorem B2056721 : Blo 1370504 2056721 := bstep (se 2 (by rfl) ⟨771270, by rfl⟩ : syracuseStep 2056721 = 1542541) B1542541
theorem B2196001 : Blo 1370504 2196001 := bstep (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) B1647001
theorem B2056739 : Blo 1370504 2056739 := bstep (se 1 (by rfl) ⟨1542554, by rfl⟩ : syracuseStep 2056739 = 3085109) B3085109
theorem B4629041 : Blo 1370504 4629041 := bstep (se 2 (by rfl) ⟨1735890, by rfl⟩ : syracuseStep 4629041 = 3471781) B3471781
theorem B2056769 : Blo 1370504 2056769 := bstep (se 2 (by rfl) ⟨771288, by rfl⟩ : syracuseStep 2056769 = 1542577) B1542577
theorem B2056787 : Blo 1370504 2056787 := bstep (se 1 (by rfl) ⟨1542590, by rfl⟩ : syracuseStep 2056787 = 3085181) B3085181
theorem B2196065 : Blo 1370504 2196065 := bstep (se 2 (by rfl) ⟨823524, by rfl⟩ : syracuseStep 2196065 = 1647049) B1647049
theorem B2056817 : Blo 1370504 2056817 := bstep (se 2 (by rfl) ⟨771306, by rfl⟩ : syracuseStep 2056817 = 1542613) B1542613
theorem B3293827 : Blo 1370504 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B2056835 : Blo 1370504 2056835 := bstep (se 1 (by rfl) ⟨1542626, by rfl⟩ : syracuseStep 2056835 = 3085253) B3085253
theorem B2056865 : Blo 1370504 2056865 := bstep (se 2 (by rfl) ⟨771324, by rfl⟩ : syracuseStep 2056865 = 1542649) B1542649
theorem B2933425 : Blo 1370504 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B2056883 : Blo 1370504 2056883 := bstep (se 1 (by rfl) ⟨1542662, by rfl⟩ : syracuseStep 2056883 = 3085325) B3085325
theorem B3293905 : Blo 1370504 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B2056913 : Blo 1370504 2056913 := bstep (se 2 (by rfl) ⟨771342, by rfl⟩ : syracuseStep 2056913 = 1542685) B1542685
theorem B2056931 : Blo 1370504 2056931 := bstep (se 1 (by rfl) ⟨1542698, by rfl⟩ : syracuseStep 2056931 = 3085397) B3085397
theorem B2056961 : Blo 1370504 2056961 := bstep (se 2 (by rfl) ⟨771360, by rfl⟩ : syracuseStep 2056961 = 1542721) B1542721
theorem B2056979 : Blo 1370504 2056979 := bstep (se 1 (by rfl) ⟨1542734, by rfl⟩ : syracuseStep 2056979 = 3085469) B3085469
theorem B2057009 : Blo 1370504 2057009 := bstep (se 2 (by rfl) ⟨771378, by rfl⟩ : syracuseStep 2057009 = 1542757) B1542757
theorem B2057027 : Blo 1370504 2057027 := bstep (se 1 (by rfl) ⟨1542770, by rfl⟩ : syracuseStep 2057027 = 3085541) B3085541
theorem B2057057 : Blo 1370504 2057057 := bstep (se 2 (by rfl) ⟨771396, by rfl⟩ : syracuseStep 2057057 = 1542793) B1542793
theorem B2057075 : Blo 1370504 2057075 := bstep (se 1 (by rfl) ⟨1542806, by rfl⟩ : syracuseStep 2057075 = 3085613) B3085613
theorem B5858189 : Blo 1370504 5858189 := bstep (se 3 (by rfl) ⟨1098410, by rfl⟩ : syracuseStep 5858189 = 2196821) B2196821
theorem B2057105 : Blo 1370504 2057105 := bstep (se 2 (by rfl) ⟨771414, by rfl⟩ : syracuseStep 2057105 = 1542829) B1542829
theorem B2057123 : Blo 1370504 2057123 := bstep (se 1 (by rfl) ⟨1542842, by rfl⟩ : syracuseStep 2057123 = 3085685) B3085685
theorem B2057153 : Blo 1370504 2057153 := bstep (se 2 (by rfl) ⟨771432, by rfl⟩ : syracuseStep 2057153 = 1542865) B1542865
theorem B2057171 : Blo 1370504 2057171 := bstep (se 1 (by rfl) ⟨1542878, by rfl⟩ : syracuseStep 2057171 = 3085757) B3085757
theorem B1647587 : Blo 1370504 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B2057201 : Blo 1370504 2057201 := bstep (se 2 (by rfl) ⟨771450, by rfl⟩ : syracuseStep 2057201 = 1542901) B1542901
theorem B2057219 : Blo 1370504 2057219 := bstep (se 1 (by rfl) ⟨1542914, by rfl⟩ : syracuseStep 2057219 = 3085829) B3085829
theorem B2057249 : Blo 1370504 2057249 := bstep (se 2 (by rfl) ⟨771468, by rfl⟩ : syracuseStep 2057249 = 1542937) B1542937
theorem B2057267 : Blo 1370504 2057267 := bstep (se 1 (by rfl) ⟨1542950, by rfl⟩ : syracuseStep 2057267 = 3085901) B3085901
theorem B4629581 : Blo 1370504 4629581 := bstep (se 3 (by rfl) ⟨868046, by rfl⟩ : syracuseStep 4629581 = 1736093) B1736093
theorem B2057297 : Blo 1370504 2057297 := bstep (se 2 (by rfl) ⟨771486, by rfl⟩ : syracuseStep 2057297 = 1542973) B1542973
theorem B2057315 : Blo 1370504 2057315 := bstep (se 1 (by rfl) ⟨1542986, by rfl⟩ : syracuseStep 2057315 = 3085973) B3085973
theorem B2057345 : Blo 1370504 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B4629635 : Blo 1370504 4629635 := bstep (se 1 (by rfl) ⟨3472226, by rfl⟩ : syracuseStep 4629635 = 6944453) B6944453
theorem B9381005 : Blo 1370504 9381005 := bstep (se 3 (by rfl) ⟨1758938, by rfl⟩ : syracuseStep 9381005 = 3517877) B3517877
theorem B2638993 : Blo 1370504 2638993 := bstep (se 2 (by rfl) ⟨989622, by rfl⟩ : syracuseStep 2638993 = 1979245) B1979245
theorem B2057363 : Blo 1370504 2057363 := bstep (se 1 (by rfl) ⟨1543022, by rfl⟩ : syracuseStep 2057363 = 3086045) B3086045
theorem B2057393 : Blo 1370504 2057393 := bstep (se 2 (by rfl) ⟨771522, by rfl⟩ : syracuseStep 2057393 = 1543045) B1543045
theorem B2057411 : Blo 1370504 2057411 := bstep (se 1 (by rfl) ⟨1543058, by rfl⟩ : syracuseStep 2057411 = 3086117) B3086117
theorem B5637325 : Blo 1370504 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B2057441 : Blo 1370504 2057441 := bstep (se 2 (by rfl) ⟨771540, by rfl⟩ : syracuseStep 2057441 = 1543081) B1543081
theorem B2057459 : Blo 1370504 2057459 := bstep (se 1 (by rfl) ⟨1543094, by rfl⟩ : syracuseStep 2057459 = 3086189) B3086189
theorem B1647875 : Blo 1370504 1647875 := bstep (se 1 (by rfl) ⟨1235906, by rfl⟩ : syracuseStep 1647875 = 2471813) B2471813
theorem B6939917 : Blo 1370504 6939917 := bstep (se 3 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 6939917 = 2602469) B2602469
theorem B2057489 : Blo 1370504 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B2057507 : Blo 1370504 2057507 := bstep (se 1 (by rfl) ⟨1543130, by rfl⟩ : syracuseStep 2057507 = 3086261) B3086261
theorem B2057537 : Blo 1370504 2057537 := bstep (se 2 (by rfl) ⟨771576, by rfl⟩ : syracuseStep 2057537 = 1543153) B1543153
theorem B2057555 : Blo 1370504 2057555 := bstep (se 1 (by rfl) ⟨1543166, by rfl⟩ : syracuseStep 2057555 = 3086333) B3086333
theorem B2057585 : Blo 1370504 2057585 := bstep (se 2 (by rfl) ⟨771594, by rfl⟩ : syracuseStep 2057585 = 1543189) B1543189
theorem B2057603 : Blo 1370504 2057603 := bstep (se 1 (by rfl) ⟨1543202, by rfl⟩ : syracuseStep 2057603 = 3086405) B3086405
theorem B4629905 : Blo 1370504 4629905 := bstep (se 2 (by rfl) ⟨1736214, by rfl⟩ : syracuseStep 4629905 = 3472429) B3472429
theorem B2057633 : Blo 1370504 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B2057651 : Blo 1370504 2057651 := bstep (se 1 (by rfl) ⟨1543238, by rfl⟩ : syracuseStep 2057651 = 3086477) B3086477
theorem B1648067 : Blo 1370504 1648067 := bstep (se 1 (by rfl) ⟨1236050, by rfl⟩ : syracuseStep 1648067 = 2472101) B2472101
theorem B2057681 : Blo 1370504 2057681 := bstep (se 2 (by rfl) ⟨771630, by rfl⟩ : syracuseStep 2057681 = 1543261) B1543261
theorem B2057699 : Blo 1370504 2057699 := bstep (se 1 (by rfl) ⟨1543274, by rfl⟩ : syracuseStep 2057699 = 3086549) B3086549
theorem B2057729 : Blo 1370504 2057729 := bstep (se 2 (by rfl) ⟨771648, by rfl⟩ : syracuseStep 2057729 = 1543297) B1543297
theorem B2057747 : Blo 1370504 2057747 := bstep (se 1 (by rfl) ⟨1543310, by rfl⟩ : syracuseStep 2057747 = 3086621) B3086621
theorem B2057777 : Blo 1370504 2057777 := bstep (se 2 (by rfl) ⟨771666, by rfl⟩ : syracuseStep 2057777 = 1543333) B1543333
theorem B2057795 : Blo 1370504 2057795 := bstep (se 1 (by rfl) ⟨1543346, by rfl⟩ : syracuseStep 2057795 = 3086693) B3086693
theorem B8783437 : Blo 1370504 8783437 := bstep (se 3 (by rfl) ⟨1646894, by rfl⟩ : syracuseStep 8783437 = 3293789) B3293789
theorem B2057825 : Blo 1370504 2057825 := bstep (se 2 (by rfl) ⟨771684, by rfl⟩ : syracuseStep 2057825 = 1543369) B1543369
theorem B2057843 : Blo 1370504 2057843 := bstep (se 1 (by rfl) ⟨1543382, by rfl⟩ : syracuseStep 2057843 = 3086765) B3086765
theorem B2057873 : Blo 1370504 2057873 := bstep (se 2 (by rfl) ⟨771702, by rfl⟩ : syracuseStep 2057873 = 1543405) B1543405
theorem B2057891 : Blo 1370504 2057891 := bstep (se 1 (by rfl) ⟨1543418, by rfl⟩ : syracuseStep 2057891 = 3086837) B3086837
theorem B2057921 : Blo 1370504 2057921 := bstep (se 2 (by rfl) ⟨771720, by rfl⟩ : syracuseStep 2057921 = 1543441) B1543441
theorem B7513805 : Blo 1370504 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B2057939 : Blo 1370504 2057939 := bstep (se 1 (by rfl) ⟨1543454, by rfl⟩ : syracuseStep 2057939 = 3086909) B3086909
theorem B2057969 : Blo 1370504 2057969 := bstep (se 2 (by rfl) ⟨771738, by rfl⟩ : syracuseStep 2057969 = 1543477) B1543477
theorem B1541875 : Blo 1370504 1541875 := bstep (se 1 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 1541875 = 2312813) B2312813
theorem B2057987 : Blo 1370504 2057987 := bstep (se 1 (by rfl) ⟨1543490, by rfl⟩ : syracuseStep 2057987 = 3086981) B3086981
theorem B4171601 : Blo 1370504 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B1542019 : Blo 1370504 1542019 := bstep (se 1 (by rfl) ⟨1156514, by rfl⟩ : syracuseStep 1542019 = 2313029) B2313029
theorem B4630445 : Blo 1370504 4630445 := bstep (se 3 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 4630445 = 1736417) B1736417
theorem B12503011 : Blo 1370504 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B4630499 : Blo 1370504 4630499 := bstep (se 1 (by rfl) ⟨3472874, by rfl⟩ : syracuseStep 4630499 = 6945749) B6945749
theorem B1542163 : Blo 1370504 1542163 := bstep (se 1 (by rfl) ⟨1156622, by rfl⟩ : syracuseStep 1542163 = 2313245) B2313245
theorem B4393091 : Blo 1370504 4393091 := bstep (se 1 (by rfl) ⟨3294818, by rfl⟩ : syracuseStep 4393091 = 6589637) B6589637
theorem B1542307 : Blo 1370504 1542307 := bstep (se 1 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 1542307 = 2313461) B2313461
theorem B5204195 : Blo 1370504 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B5204209 : Blo 1370504 5204209 := bstep (se 2 (by rfl) ⟨1951578, by rfl⟩ : syracuseStep 5204209 = 3903157) B3903157
theorem B3516689 : Blo 1370504 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B6252835 : Blo 1370504 6252835 := bstep (se 1 (by rfl) ⟨4689626, by rfl⟩ : syracuseStep 6252835 = 9379253) B9379253
theorem B1542451 : Blo 1370504 1542451 := bstep (se 1 (by rfl) ⟨1156838, by rfl⟩ : syracuseStep 1542451 = 2313677) B2313677
theorem B1370515 : Blo 1370504 1370515 := bstep (se 1 (by rfl) ⟨1027886, by rfl⟩ : syracuseStep 1370515 = 2055773) B2055773
theorem B1370531 : Blo 1370504 1370531 := bstep (se 1 (by rfl) ⟨1027898, by rfl⟩ : syracuseStep 1370531 = 2055797) B2055797
theorem B1370547 : Blo 1370504 1370547 := bstep (se 1 (by rfl) ⟨1027910, by rfl⟩ : syracuseStep 1370547 = 2055821) B2055821
theorem B1370563 : Blo 1370504 1370563 := bstep (se 1 (by rfl) ⟨1027922, by rfl⟩ : syracuseStep 1370563 = 2055845) B2055845
theorem B1542595 : Blo 1370504 1542595 := bstep (se 1 (by rfl) ⟨1156946, by rfl⟩ : syracuseStep 1542595 = 2313893) B2313893
theorem B1370579 : Blo 1370504 1370579 := bstep (se 1 (by rfl) ⟨1027934, by rfl⟩ : syracuseStep 1370579 = 2055869) B2055869
theorem B1370595 : Blo 1370504 1370595 := bstep (se 1 (by rfl) ⟨1027946, by rfl⟩ : syracuseStep 1370595 = 2055893) B2055893
theorem B1370611 : Blo 1370504 1370611 := bstep (se 1 (by rfl) ⟨1027958, by rfl⟩ : syracuseStep 1370611 = 2055917) B2055917
theorem B1952257 : Blo 1370504 1952257 := bstep (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) B1464193
theorem B1370627 : Blo 1370504 1370627 := bstep (se 1 (by rfl) ⟨1027970, by rfl⟩ : syracuseStep 1370627 = 2055941) B2055941
theorem B1370643 : Blo 1370504 1370643 := bstep (se 1 (by rfl) ⟨1027982, by rfl⟩ : syracuseStep 1370643 = 2055965) B2055965
theorem B1370659 : Blo 1370504 1370659 := bstep (se 1 (by rfl) ⟨1027994, by rfl⟩ : syracuseStep 1370659 = 2055989) B2055989
theorem B1370675 : Blo 1370504 1370675 := bstep (se 1 (by rfl) ⟨1028006, by rfl⟩ : syracuseStep 1370675 = 2056013) B2056013
theorem B1370691 : Blo 1370504 1370691 := bstep (se 1 (by rfl) ⟨1028018, by rfl⟩ : syracuseStep 1370691 = 2056037) B2056037
theorem B2345539 : Blo 1370504 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B1370707 : Blo 1370504 1370707 := bstep (se 1 (by rfl) ⟨1028030, by rfl⟩ : syracuseStep 1370707 = 2056061) B2056061
theorem B1542739 : Blo 1370504 1542739 := bstep (se 1 (by rfl) ⟨1157054, by rfl⟩ : syracuseStep 1542739 = 2314109) B2314109
theorem B1952353 : Blo 1370504 1952353 := bstep (se 2 (by rfl) ⟨732132, by rfl⟩ : syracuseStep 1952353 = 1464265) B1464265
theorem B1370723 : Blo 1370504 1370723 := bstep (se 1 (by rfl) ⟨1028042, by rfl⟩ : syracuseStep 1370723 = 2056085) B2056085
theorem B1370739 : Blo 1370504 1370739 := bstep (se 1 (by rfl) ⟨1028054, by rfl⟩ : syracuseStep 1370739 = 2056109) B2056109
theorem B2312833 : Blo 1370504 2312833 := bstep (se 2 (by rfl) ⟨867312, by rfl⟩ : syracuseStep 2312833 = 1734625) B1734625
theorem B1370755 : Blo 1370504 1370755 := bstep (se 1 (by rfl) ⟨1028066, by rfl⟩ : syracuseStep 1370755 = 2056133) B2056133
theorem B2927249 : Blo 1370504 2927249 := bstep (se 2 (by rfl) ⟨1097718, by rfl⟩ : syracuseStep 2927249 = 2195437) B2195437
theorem B1370771 : Blo 1370504 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B2312867 : Blo 1370504 2312867 := bstep (se 1 (by rfl) ⟨1734650, by rfl⟩ : syracuseStep 2312867 = 3469301) B3469301
theorem B1370787 : Blo 1370504 1370787 := bstep (se 1 (by rfl) ⟨1028090, by rfl⟩ : syracuseStep 1370787 = 2056181) B2056181
theorem B1370803 : Blo 1370504 1370803 := bstep (se 1 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 1370803 = 2056205) B2056205
theorem B1370819 : Blo 1370504 1370819 := bstep (se 1 (by rfl) ⟨1028114, by rfl⟩ : syracuseStep 1370819 = 2056229) B2056229
theorem B1370835 : Blo 1370504 1370835 := bstep (se 1 (by rfl) ⟨1028126, by rfl⟩ : syracuseStep 1370835 = 2056253) B2056253
theorem B1370851 : Blo 1370504 1370851 := bstep (se 1 (by rfl) ⟨1028138, by rfl⟩ : syracuseStep 1370851 = 2056277) B2056277
theorem B1542883 : Blo 1370504 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B1370867 : Blo 1370504 1370867 := bstep (se 1 (by rfl) ⟨1028150, by rfl⟩ : syracuseStep 1370867 = 2056301) B2056301
theorem B1370883 : Blo 1370504 1370883 := bstep (se 1 (by rfl) ⟨1028162, by rfl⟩ : syracuseStep 1370883 = 2056325) B2056325
theorem B1370899 : Blo 1370504 1370899 := bstep (se 1 (by rfl) ⟨1028174, by rfl⟩ : syracuseStep 1370899 = 2056349) B2056349
theorem B2312995 : Blo 1370504 2312995 := bstep (se 1 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 2312995 = 3469493) B3469493
theorem B1370915 : Blo 1370504 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B1370931 : Blo 1370504 1370931 := bstep (se 1 (by rfl) ⟨1028198, by rfl⟩ : syracuseStep 1370931 = 2056397) B2056397
theorem B1370947 : Blo 1370504 1370947 := bstep (se 1 (by rfl) ⟨1028210, by rfl⟩ : syracuseStep 1370947 = 2056421) B2056421
theorem B1370963 : Blo 1370504 1370963 := bstep (se 1 (by rfl) ⟨1028222, by rfl⟩ : syracuseStep 1370963 = 2056445) B2056445
theorem B1370979 : Blo 1370504 1370979 := bstep (se 1 (by rfl) ⟨1028234, by rfl⟩ : syracuseStep 1370979 = 2056469) B2056469
theorem B1370995 : Blo 1370504 1370995 := bstep (se 1 (by rfl) ⟨1028246, by rfl⟩ : syracuseStep 1370995 = 2056493) B2056493
theorem B1543027 : Blo 1370504 1543027 := bstep (se 1 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 1543027 = 2314541) B2314541
theorem B1371011 : Blo 1370504 1371011 := bstep (se 1 (by rfl) ⟨1028258, by rfl⟩ : syracuseStep 1371011 = 2056517) B2056517
theorem B1371027 : Blo 1370504 1371027 := bstep (se 1 (by rfl) ⟨1028270, by rfl⟩ : syracuseStep 1371027 = 2056541) B2056541
theorem B1371043 : Blo 1370504 1371043 := bstep (se 1 (by rfl) ⟨1028282, by rfl⟩ : syracuseStep 1371043 = 2056565) B2056565
theorem B2313137 : Blo 1370504 2313137 := bstep (se 2 (by rfl) ⟨867426, by rfl⟩ : syracuseStep 2313137 = 1734853) B1734853
theorem B1371059 : Blo 1370504 1371059 := bstep (se 1 (by rfl) ⟨1028294, by rfl⟩ : syracuseStep 1371059 = 2056589) B2056589
theorem B1371075 : Blo 1370504 1371075 := bstep (se 1 (by rfl) ⟨1028306, by rfl⟩ : syracuseStep 1371075 = 2056613) B2056613
theorem B1371091 : Blo 1370504 1371091 := bstep (se 1 (by rfl) ⟨1028318, by rfl⟩ : syracuseStep 1371091 = 2056637) B2056637
theorem B1371107 : Blo 1370504 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B5352419 : Blo 1370504 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B1371123 : Blo 1370504 1371123 := bstep (se 1 (by rfl) ⟨1028342, by rfl⟩ : syracuseStep 1371123 = 2056685) B2056685
theorem B1371139 : Blo 1370504 1371139 := bstep (se 1 (by rfl) ⟨1028354, by rfl⟩ : syracuseStep 1371139 = 2056709) B2056709
theorem B1543171 : Blo 1370504 1543171 := bstep (se 1 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 1543171 = 2314757) B2314757
theorem B1371155 : Blo 1370504 1371155 := bstep (se 1 (by rfl) ⟨1028366, by rfl⟩ : syracuseStep 1371155 = 2056733) B2056733
theorem B1371171 : Blo 1370504 1371171 := bstep (se 1 (by rfl) ⟨1028378, by rfl⟩ : syracuseStep 1371171 = 2056757) B2056757
theorem B2313265 : Blo 1370504 2313265 := bstep (se 2 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 2313265 = 1734949) B1734949
theorem B2968625 : Blo 1370504 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B1371187 : Blo 1370504 1371187 := bstep (se 1 (by rfl) ⟨1028390, by rfl⟩ : syracuseStep 1371187 = 2056781) B2056781
theorem B1371203 : Blo 1370504 1371203 := bstep (se 1 (by rfl) ⟨1028402, by rfl⟩ : syracuseStep 1371203 = 2056805) B2056805
theorem B1952849 : Blo 1370504 1952849 := bstep (se 2 (by rfl) ⟨732318, by rfl⟩ : syracuseStep 1952849 = 1464637) B1464637
theorem B2313299 : Blo 1370504 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B1371219 : Blo 1370504 1371219 := bstep (se 1 (by rfl) ⟨1028414, by rfl⟩ : syracuseStep 1371219 = 2056829) B2056829
theorem B1371235 : Blo 1370504 1371235 := bstep (se 1 (by rfl) ⟨1028426, by rfl⟩ : syracuseStep 1371235 = 2056853) B2056853
theorem B1371251 : Blo 1370504 1371251 := bstep (se 1 (by rfl) ⟨1028438, by rfl⟩ : syracuseStep 1371251 = 2056877) B2056877
theorem B1371267 : Blo 1370504 1371267 := bstep (se 1 (by rfl) ⟨1028450, by rfl⟩ : syracuseStep 1371267 = 2056901) B2056901
theorem B1371283 : Blo 1370504 1371283 := bstep (se 1 (by rfl) ⟨1028462, by rfl⟩ : syracuseStep 1371283 = 2056925) B2056925
theorem B1543315 : Blo 1370504 1543315 := bstep (se 1 (by rfl) ⟨1157486, by rfl⟩ : syracuseStep 1543315 = 2314973) B2314973
theorem B1371299 : Blo 1370504 1371299 := bstep (se 1 (by rfl) ⟨1028474, by rfl⟩ : syracuseStep 1371299 = 2056949) B2056949
theorem B1371315 : Blo 1370504 1371315 := bstep (se 1 (by rfl) ⟨1028486, by rfl⟩ : syracuseStep 1371315 = 2056973) B2056973
theorem B1371331 : Blo 1370504 1371331 := bstep (se 1 (by rfl) ⟨1028498, by rfl⟩ : syracuseStep 1371331 = 2056997) B2056997
theorem B4394179 : Blo 1370504 4394179 := bstep (se 1 (by rfl) ⟨3295634, by rfl⟩ : syracuseStep 4394179 = 6591269) B6591269
theorem B2313427 : Blo 1370504 2313427 := bstep (se 1 (by rfl) ⟨1735070, by rfl⟩ : syracuseStep 2313427 = 3470141) B3470141
theorem B1371347 : Blo 1370504 1371347 := bstep (se 1 (by rfl) ⟨1028510, by rfl⟩ : syracuseStep 1371347 = 2057021) B2057021
theorem B1371363 : Blo 1370504 1371363 := bstep (se 1 (by rfl) ⟨1028522, by rfl⟩ : syracuseStep 1371363 = 2057045) B2057045
theorem B1371379 : Blo 1370504 1371379 := bstep (se 1 (by rfl) ⟨1028534, by rfl⟩ : syracuseStep 1371379 = 2057069) B2057069
theorem B1371395 : Blo 1370504 1371395 := bstep (se 1 (by rfl) ⟨1028546, by rfl⟩ : syracuseStep 1371395 = 2057093) B2057093
theorem B1371411 : Blo 1370504 1371411 := bstep (se 1 (by rfl) ⟨1028558, by rfl⟩ : syracuseStep 1371411 = 2057117) B2057117
theorem B1371427 : Blo 1370504 1371427 := bstep (se 1 (by rfl) ⟨1028570, by rfl⟩ : syracuseStep 1371427 = 2057141) B2057141
theorem B3968291 : Blo 1370504 3968291 := bstep (se 1 (by rfl) ⟨2976218, by rfl⟩ : syracuseStep 3968291 = 5952437) B5952437
theorem B1543459 : Blo 1370504 1543459 := bstep (se 1 (by rfl) ⟨1157594, by rfl⟩ : syracuseStep 1543459 = 2315189) B2315189
theorem B1371443 : Blo 1370504 1371443 := bstep (se 1 (by rfl) ⟨1028582, by rfl⟩ : syracuseStep 1371443 = 2057165) B2057165
theorem B1371459 : Blo 1370504 1371459 := bstep (se 1 (by rfl) ⟨1028594, by rfl⟩ : syracuseStep 1371459 = 2057189) B2057189
theorem B4394321 : Blo 1370504 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B1371475 : Blo 1370504 1371475 := bstep (se 1 (by rfl) ⟨1028606, by rfl⟩ : syracuseStep 1371475 = 2057213) B2057213
theorem B2313569 : Blo 1370504 2313569 := bstep (se 2 (by rfl) ⟨867588, by rfl⟩ : syracuseStep 2313569 = 1735177) B1735177
theorem B1371491 : Blo 1370504 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B1371507 : Blo 1370504 1371507 := bstep (se 1 (by rfl) ⟨1028630, by rfl⟩ : syracuseStep 1371507 = 2057261) B2057261
theorem B3083651 : Blo 1370504 3083651 := bstep (se 1 (by rfl) ⟨2312738, by rfl⟩ : syracuseStep 3083651 = 4625477) B4625477
theorem B1371523 : Blo 1370504 1371523 := bstep (se 1 (by rfl) ⟨1028642, by rfl⟩ : syracuseStep 1371523 = 2057285) B2057285
theorem B1371539 : Blo 1370504 1371539 := bstep (se 1 (by rfl) ⟨1028654, by rfl⟩ : syracuseStep 1371539 = 2057309) B2057309
theorem B1371555 : Blo 1370504 1371555 := bstep (se 1 (by rfl) ⟨1028666, by rfl⟩ : syracuseStep 1371555 = 2057333) B2057333
theorem B1371571 : Blo 1370504 1371571 := bstep (se 1 (by rfl) ⟨1028678, by rfl⟩ : syracuseStep 1371571 = 2057357) B2057357
theorem B1371587 : Blo 1370504 1371587 := bstep (se 1 (by rfl) ⟨1028690, by rfl⟩ : syracuseStep 1371587 = 2057381) B2057381
theorem B2969041 : Blo 1370504 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B1371603 : Blo 1370504 1371603 := bstep (se 1 (by rfl) ⟨1028702, by rfl⟩ : syracuseStep 1371603 = 2057405) B2057405
theorem B2313697 : Blo 1370504 2313697 := bstep (se 2 (by rfl) ⟨867636, by rfl⟩ : syracuseStep 2313697 = 1735273) B1735273
theorem B1371619 : Blo 1370504 1371619 := bstep (se 1 (by rfl) ⟨1028714, by rfl⟩ : syracuseStep 1371619 = 2057429) B2057429
theorem B1371635 : Blo 1370504 1371635 := bstep (se 1 (by rfl) ⟨1028726, by rfl⟩ : syracuseStep 1371635 = 2057453) B2057453
theorem B2313731 : Blo 1370504 2313731 := bstep (se 1 (by rfl) ⟨1735298, by rfl⟩ : syracuseStep 2313731 = 3470597) B3470597
theorem B1371651 : Blo 1370504 1371651 := bstep (se 1 (by rfl) ⟨1028738, by rfl⟩ : syracuseStep 1371651 = 2057477) B2057477
theorem B1371667 : Blo 1370504 1371667 := bstep (se 1 (by rfl) ⟨1028750, by rfl⟩ : syracuseStep 1371667 = 2057501) B2057501
theorem B1371683 : Blo 1370504 1371683 := bstep (se 1 (by rfl) ⟨1028762, by rfl⟩ : syracuseStep 1371683 = 2057525) B2057525
theorem B1371699 : Blo 1370504 1371699 := bstep (se 1 (by rfl) ⟨1028774, by rfl⟩ : syracuseStep 1371699 = 2057549) B2057549
theorem B1371715 : Blo 1370504 1371715 := bstep (se 1 (by rfl) ⟨1028786, by rfl⟩ : syracuseStep 1371715 = 2057573) B2057573
theorem B1371731 : Blo 1370504 1371731 := bstep (se 1 (by rfl) ⟨1028798, by rfl⟩ : syracuseStep 1371731 = 2057597) B2057597
theorem B1371747 : Blo 1370504 1371747 := bstep (se 1 (by rfl) ⟨1028810, by rfl⟩ : syracuseStep 1371747 = 2057621) B2057621
theorem B1371763 : Blo 1370504 1371763 := bstep (se 1 (by rfl) ⟨1028822, by rfl⟩ : syracuseStep 1371763 = 2057645) B2057645
theorem B2313859 : Blo 1370504 2313859 := bstep (se 1 (by rfl) ⟨1735394, by rfl⟩ : syracuseStep 2313859 = 3470789) B3470789
theorem B3706499 : Blo 1370504 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B1371779 : Blo 1370504 1371779 := bstep (se 1 (by rfl) ⟨1028834, by rfl⟩ : syracuseStep 1371779 = 2057669) B2057669
theorem B3083921 : Blo 1370504 3083921 := bstep (se 2 (by rfl) ⟨1156470, by rfl⟩ : syracuseStep 3083921 = 2312941) B2312941
theorem B1371795 : Blo 1370504 1371795 := bstep (se 1 (by rfl) ⟨1028846, by rfl⟩ : syracuseStep 1371795 = 2057693) B2057693
theorem B3083939 : Blo 1370504 3083939 := bstep (se 1 (by rfl) ⟨2312954, by rfl⟩ : syracuseStep 3083939 = 4625909) B4625909
theorem B5205667 : Blo 1370504 5205667 := bstep (se 1 (by rfl) ⟨3904250, by rfl⟩ : syracuseStep 5205667 = 7808501) B7808501
theorem B1371811 : Blo 1370504 1371811 := bstep (se 1 (by rfl) ⟨1028858, by rfl⟩ : syracuseStep 1371811 = 2057717) B2057717
theorem B1371827 : Blo 1370504 1371827 := bstep (se 1 (by rfl) ⟨1028870, by rfl⟩ : syracuseStep 1371827 = 2057741) B2057741
theorem B1371843 : Blo 1370504 1371843 := bstep (se 1 (by rfl) ⟨1028882, by rfl⟩ : syracuseStep 1371843 = 2057765) B2057765
theorem B1978067 : Blo 1370504 1978067 := bstep (se 1 (by rfl) ⟨1483550, by rfl⟩ : syracuseStep 1978067 = 2967101) B2967101
theorem B1371859 : Blo 1370504 1371859 := bstep (se 1 (by rfl) ⟨1028894, by rfl⟩ : syracuseStep 1371859 = 2057789) B2057789
theorem B3903203 : Blo 1370504 3903203 := bstep (se 1 (by rfl) ⟨2927402, by rfl⟩ : syracuseStep 3903203 = 5854805) B5854805
theorem B1371875 : Blo 1370504 1371875 := bstep (se 1 (by rfl) ⟨1028906, by rfl⟩ : syracuseStep 1371875 = 2057813) B2057813
theorem B1371891 : Blo 1370504 1371891 := bstep (se 1 (by rfl) ⟨1028918, by rfl⟩ : syracuseStep 1371891 = 2057837) B2057837
theorem B1371907 : Blo 1370504 1371907 := bstep (se 1 (by rfl) ⟨1028930, by rfl⟩ : syracuseStep 1371907 = 2057861) B2057861
theorem B2314001 : Blo 1370504 2314001 := bstep (se 2 (by rfl) ⟨867750, by rfl⟩ : syracuseStep 2314001 = 1735501) B1735501
theorem B1371923 : Blo 1370504 1371923 := bstep (se 1 (by rfl) ⟨1028942, by rfl⟩ : syracuseStep 1371923 = 2057885) B2057885
theorem B1371939 : Blo 1370504 1371939 := bstep (se 1 (by rfl) ⟨1028954, by rfl⟩ : syracuseStep 1371939 = 2057909) B2057909
theorem B1371955 : Blo 1370504 1371955 := bstep (se 1 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 1371955 = 2057933) B2057933
theorem B1371971 : Blo 1370504 1371971 := bstep (se 1 (by rfl) ⟨1028978, by rfl⟩ : syracuseStep 1371971 = 2057957) B2057957
theorem B1371987 : Blo 1370504 1371987 := bstep (se 1 (by rfl) ⟨1028990, by rfl⟩ : syracuseStep 1371987 = 2057981) B2057981
theorem B1372003 : Blo 1370504 1372003 := bstep (se 1 (by rfl) ⟨1029002, by rfl⟩ : syracuseStep 1372003 = 2058005) B2058005
theorem B3469169 : Blo 1370504 3469169 := bstep (se 2 (by rfl) ⟨1300938, by rfl⟩ : syracuseStep 3469169 = 2601877) B2601877
theorem B2314129 : Blo 1370504 2314129 := bstep (se 2 (by rfl) ⟨867798, by rfl⟩ : syracuseStep 2314129 = 1735597) B1735597
theorem B5279651 : Blo 1370504 5279651 := bstep (se 1 (by rfl) ⟨3959738, by rfl⟩ : syracuseStep 5279651 = 7919477) B7919477
theorem B3084209 : Blo 1370504 3084209 := bstep (se 2 (by rfl) ⟨1156578, by rfl⟩ : syracuseStep 3084209 = 2313157) B2313157
theorem B2314163 : Blo 1370504 2314163 := bstep (se 1 (by rfl) ⟨1735622, by rfl⟩ : syracuseStep 2314163 = 3471245) B3471245
theorem B3084227 : Blo 1370504 3084227 := bstep (se 1 (by rfl) ⟨2313170, by rfl⟩ : syracuseStep 3084227 = 4626341) B4626341
theorem B8343587 : Blo 1370504 8343587 := bstep (se 1 (by rfl) ⟨6257690, by rfl⟩ : syracuseStep 8343587 = 12515381) B12515381
theorem B5558321 : Blo 1370504 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B2314291 : Blo 1370504 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B6942833 : Blo 1370504 6942833 := bstep (se 2 (by rfl) ⟨2603562, by rfl⟩ : syracuseStep 6942833 = 5207125) B5207125
theorem B2928803 : Blo 1370504 2928803 := bstep (se 1 (by rfl) ⟨2196602, by rfl⟩ : syracuseStep 2928803 = 4393205) B4393205
theorem B5558449 : Blo 1370504 5558449 := bstep (se 2 (by rfl) ⟨2084418, by rfl⟩ : syracuseStep 5558449 = 4168837) B4168837
theorem B2314433 : Blo 1370504 2314433 := bstep (se 2 (by rfl) ⟨867912, by rfl⟩ : syracuseStep 2314433 = 1735825) B1735825
theorem B3084497 : Blo 1370504 3084497 := bstep (se 2 (by rfl) ⟨1156686, by rfl⟩ : syracuseStep 3084497 = 2313373) B2313373
theorem B3084515 : Blo 1370504 3084515 := bstep (se 1 (by rfl) ⟨2313386, by rfl⟩ : syracuseStep 3084515 = 4626773) B4626773
theorem B2314561 : Blo 1370504 2314561 := bstep (se 2 (by rfl) ⟨867960, by rfl⟩ : syracuseStep 2314561 = 1735921) B1735921
theorem B2314595 : Blo 1370504 2314595 := bstep (se 1 (by rfl) ⟨1735946, by rfl⟩ : syracuseStep 2314595 = 3471893) B3471893
theorem B3756401 : Blo 1370504 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B2314723 : Blo 1370504 2314723 := bstep (se 1 (by rfl) ⟨1736042, by rfl⟩ : syracuseStep 2314723 = 3472085) B3472085
theorem B2970083 : Blo 1370504 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B3084785 : Blo 1370504 3084785 := bstep (se 2 (by rfl) ⟨1156794, by rfl⟩ : syracuseStep 3084785 = 2313589) B2313589
theorem B3084803 : Blo 1370504 3084803 := bstep (se 1 (by rfl) ⟨2313602, by rfl⟩ : syracuseStep 3084803 = 4627205) B4627205
theorem B3707459 : Blo 1370504 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B3125873 : Blo 1370504 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B2314865 : Blo 1370504 2314865 := bstep (se 2 (by rfl) ⟨868074, by rfl⟩ : syracuseStep 2314865 = 1736149) B1736149
theorem B2085617 : Blo 1370504 2085617 := bstep (se 2 (by rfl) ⟨782106, by rfl⟩ : syracuseStep 2085617 = 1564213) B1564213
theorem B2314993 : Blo 1370504 2314993 := bstep (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) B1736245
theorem B1504003 : Blo 1370504 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B3085073 : Blo 1370504 3085073 := bstep (se 2 (by rfl) ⟨1156902, by rfl⟩ : syracuseStep 3085073 = 2313805) B2313805
theorem B2315027 : Blo 1370504 2315027 := bstep (se 1 (by rfl) ⟨1736270, by rfl⟩ : syracuseStep 2315027 = 3472541) B3472541
theorem B3085091 : Blo 1370504 3085091 := bstep (se 1 (by rfl) ⟨2313818, by rfl⟩ : syracuseStep 3085091 = 4627637) B4627637
theorem B3470161 : Blo 1370504 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B4756333 : Blo 1370504 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B2315155 : Blo 1370504 2315155 := bstep (se 1 (by rfl) ⟨1736366, by rfl⟩ : syracuseStep 2315155 = 3472733) B3472733
theorem B3904433 : Blo 1370504 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B2470883 : Blo 1370504 2470883 := bstep (se 1 (by rfl) ⟨1853162, by rfl⟩ : syracuseStep 2470883 = 3706325) B3706325
theorem B3085361 : Blo 1370504 3085361 := bstep (se 2 (by rfl) ⟨1157010, by rfl⟩ : syracuseStep 3085361 = 2314021) B2314021
theorem B3085379 : Blo 1370504 3085379 := bstep (se 1 (by rfl) ⟨2314034, by rfl⟩ : syracuseStep 3085379 = 4628069) B4628069
theorem B3470435 : Blo 1370504 3470435 := bstep (se 1 (by rfl) ⟨2602826, by rfl⟩ : syracuseStep 3470435 = 5205653) B5205653
theorem B4625585 : Blo 1370504 4625585 := bstep (se 2 (by rfl) ⟨1734594, by rfl⟩ : syracuseStep 4625585 = 3469189) B3469189
theorem B3519683 : Blo 1370504 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2225377 : Blo 1370504 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B3470627 : Blo 1370504 3470627 := bstep (se 1 (by rfl) ⟨2602970, by rfl⟩ : syracuseStep 3470627 = 5205941) B5205941
theorem B3085649 : Blo 1370504 3085649 := bstep (se 2 (by rfl) ⟨1157118, by rfl⟩ : syracuseStep 3085649 = 2314237) B2314237
theorem B3085667 : Blo 1370504 3085667 := bstep (se 1 (by rfl) ⟨2314250, by rfl⟩ : syracuseStep 3085667 = 4628501) B4628501
theorem B7812557 : Blo 1370504 7812557 := bstep (se 3 (by rfl) ⟨1464854, by rfl⟩ : syracuseStep 7812557 = 2929709) B2929709
theorem B6944291 : Blo 1370504 6944291 := bstep (se 1 (by rfl) ⟨5208218, by rfl⟩ : syracuseStep 6944291 = 10416437) B10416437
theorem B8451661 : Blo 1370504 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B3085937 : Blo 1370504 3085937 := bstep (se 2 (by rfl) ⟨1157226, by rfl⟩ : syracuseStep 3085937 = 2314453) B2314453
theorem B3085955 : Blo 1370504 3085955 := bstep (se 1 (by rfl) ⟨2314466, by rfl⟩ : syracuseStep 3085955 = 4628933) B4628933
theorem B9508549 : Blo 1370504 9508549 := bstep (se 4 (by rfl) ⟨891426, by rfl⟩ : syracuseStep 9508549 = 1782853) B1782853
theorem B4626125 : Blo 1370504 4626125 := bstep (se 3 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 4626125 = 1734797) B1734797
theorem B2602705 : Blo 1370504 2602705 := bstep (se 2 (by rfl) ⟨976014, by rfl⟩ : syracuseStep 2602705 = 1952029) B1952029
theorem B4626179 : Blo 1370504 4626179 := bstep (se 1 (by rfl) ⟨3469634, by rfl⟩ : syracuseStep 4626179 = 6939269) B6939269
theorem B2504515 : Blo 1370504 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B5207885 : Blo 1370504 5207885 := bstep (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) B1952957
theorem B4757329 : Blo 1370504 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B8787845 : Blo 1370504 8787845 := bstep (se 4 (by rfl) ⟨823860, by rfl⟩ : syracuseStep 8787845 = 1647721) B1647721
theorem B3086225 : Blo 1370504 3086225 := bstep (se 2 (by rfl) ⟨1157334, by rfl⟩ : syracuseStep 3086225 = 2314669) B2314669
theorem B3086243 : Blo 1370504 3086243 := bstep (se 1 (by rfl) ⟨2314682, by rfl⟩ : syracuseStep 3086243 = 4629365) B4629365
theorem B4167683 : Blo 1370504 4167683 := bstep (se 1 (by rfl) ⟨3125762, by rfl⟩ : syracuseStep 4167683 = 6251525) B6251525
theorem B4626449 : Blo 1370504 4626449 := bstep (se 2 (by rfl) ⟨1734918, by rfl⟩ : syracuseStep 4626449 = 3469837) B3469837
theorem B1734691 : Blo 1370504 1734691 := bstep (se 1 (by rfl) ⟨1301018, by rfl⟩ : syracuseStep 1734691 = 2602037) B2602037
theorem B5855267 : Blo 1370504 5855267 := bstep (se 1 (by rfl) ⟨4391450, by rfl⟩ : syracuseStep 5855267 = 8782901) B8782901
theorem B5560397 : Blo 1370504 5560397 := bstep (se 3 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 5560397 = 2085149) B2085149
theorem B2603107 : Blo 1370504 2603107 := bstep (se 1 (by rfl) ⟨1952330, by rfl⟩ : syracuseStep 2603107 = 3904661) B3904661
theorem B1464419 : Blo 1370504 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B1734787 : Blo 1370504 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B2603153 : Blo 1370504 2603153 := bstep (se 2 (by rfl) ⟨976182, by rfl⟩ : syracuseStep 2603153 = 1952365) B1952365
theorem B3086513 : Blo 1370504 3086513 := bstep (se 2 (by rfl) ⟨1157442, by rfl⟩ : syracuseStep 3086513 = 2314885) B2314885
theorem B3086531 : Blo 1370504 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B5560525 : Blo 1370504 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B3471569 : Blo 1370504 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B3471619 : Blo 1370504 3471619 := bstep (se 1 (by rfl) ⟨2603714, by rfl⟩ : syracuseStep 3471619 = 5207429) B5207429
theorem B6945101 : Blo 1370504 6945101 := bstep (se 3 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 6945101 = 2604413) B2604413
theorem B3905891 : Blo 1370504 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B3471761 : Blo 1370504 3471761 := bstep (se 2 (by rfl) ⟨1301910, by rfl⟩ : syracuseStep 3471761 = 2603821) B2603821
theorem B2603441 : Blo 1370504 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B21690821 : Blo 1370504 21690821 := bstep (se 4 (by rfl) ⟨2033514, by rfl⟩ : syracuseStep 21690821 = 4067029) B4067029
theorem B3086801 : Blo 1370504 3086801 := bstep (se 2 (by rfl) ⟨1157550, by rfl⟩ : syracuseStep 3086801 = 2315101) B2315101
theorem B3086819 : Blo 1370504 3086819 := bstep (se 1 (by rfl) ⟨2315114, by rfl⟩ : syracuseStep 3086819 = 4630229) B4630229
theorem B4626989 : Blo 1370504 4626989 := bstep (se 3 (by rfl) ⟨867560, by rfl⟩ : syracuseStep 4626989 = 1735121) B1735121
theorem B4627043 : Blo 1370504 4627043 := bstep (se 1 (by rfl) ⟨3470282, by rfl⟩ : syracuseStep 4627043 = 6940565) B6940565
theorem B1735283 : Blo 1370504 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B1563475 : Blo 1370504 1563475 := bstep (se 1 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 1563475 = 2345213) B2345213
theorem B4627313 : Blo 1370504 4627313 := bstep (se 2 (by rfl) ⟨1735242, by rfl⟩ : syracuseStep 4627313 = 3470485) B3470485
theorem B16047173 : Blo 1370504 16047173 := bstep (se 4 (by rfl) ⟨1504422, by rfl⟩ : syracuseStep 16047173 = 3008845) B3008845
theorem B5938253 : Blo 1370504 5938253 := bstep (se 3 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 5938253 = 2226845) B2226845
theorem B2604163 : Blo 1370504 2604163 := bstep (se 1 (by rfl) ⟨1953122, by rfl⟩ : syracuseStep 2604163 = 3906245) B3906245
theorem B3906701 : Blo 1370504 3906701 := bstep (se 3 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 3906701 = 1465013) B1465013
theorem B21101795 : Blo 1370504 21101795 := bstep (se 1 (by rfl) ⟨15826346, by rfl⟩ : syracuseStep 21101795 = 31652693) B31652693
theorem B1735987 : Blo 1370504 1735987 := bstep (se 1 (by rfl) ⟨1301990, by rfl⟩ : syracuseStep 1735987 = 2603981) B2603981
theorem B13180229 : Blo 1370504 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B3906893 : Blo 1370504 3906893 := bstep (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) B1465085
theorem B3472753 : Blo 1370504 3472753 := bstep (se 2 (by rfl) ⟨1302282, by rfl⟩ : syracuseStep 3472753 = 2604565) B2604565
theorem B18759053 : Blo 1370504 18759053 := bstep (se 3 (by rfl) ⟨3517322, by rfl⟩ : syracuseStep 18759053 = 7034645) B7034645
theorem B4627853 : Blo 1370504 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B1736083 : Blo 1370504 1736083 := bstep (se 1 (by rfl) ⟨1302062, by rfl⟩ : syracuseStep 1736083 = 2604125) B2604125
theorem B4627907 : Blo 1370504 4627907 := bstep (se 1 (by rfl) ⟨3470930, by rfl⟩ : syracuseStep 4627907 = 6941861) B6941861
theorem B5561905 : Blo 1370504 5561905 := bstep (se 2 (by rfl) ⟨2085714, by rfl⟩ : syracuseStep 5561905 = 4171429) B4171429
theorem B2604611 : Blo 1370504 2604611 := bstep (se 1 (by rfl) ⟨1953458, by rfl⟩ : syracuseStep 2604611 = 3906917) B3906917
theorem B2055761 : Blo 1370504 2055761 := bstep (se 2 (by rfl) ⟨770910, by rfl⟩ : syracuseStep 2055761 = 1541821) B1541821
theorem B2055779 : Blo 1370504 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B2055809 : Blo 1370504 2055809 := bstep (se 2 (by rfl) ⟨770928, by rfl⟩ : syracuseStep 2055809 = 1541857) B1541857
theorem B3128963 : Blo 1370504 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B2055827 : Blo 1370504 2055827 := bstep (se 1 (by rfl) ⟨1541870, by rfl⟩ : syracuseStep 2055827 = 3083741) B3083741
theorem B2055857 : Blo 1370504 2055857 := bstep (se 2 (by rfl) ⟨770946, by rfl⟩ : syracuseStep 2055857 = 1541893) B1541893
theorem B2055875 : Blo 1370504 2055875 := bstep (se 1 (by rfl) ⟨1541906, by rfl⟩ : syracuseStep 2055875 = 3083813) B3083813
theorem B4628177 : Blo 1370504 4628177 := bstep (se 2 (by rfl) ⟨1735566, by rfl⟩ : syracuseStep 4628177 = 3471133) B3471133
theorem B2055905 : Blo 1370504 2055905 := bstep (se 2 (by rfl) ⟨770964, by rfl⟩ : syracuseStep 2055905 = 1541929) B1541929
theorem B5562083 : Blo 1370504 5562083 := bstep (se 1 (by rfl) ⟨4171562, by rfl⟩ : syracuseStep 5562083 = 8343125) B8343125
theorem B2055923 : Blo 1370504 2055923 := bstep (se 1 (by rfl) ⟨1541942, by rfl⟩ : syracuseStep 2055923 = 3083885) B3083885
theorem B7806725 : Blo 1370504 7806725 := bstep (se 4 (by rfl) ⟨731880, by rfl⟩ : syracuseStep 7806725 = 1463761) B1463761
theorem B2055953 : Blo 1370504 2055953 := bstep (se 2 (by rfl) ⟨770982, by rfl⟩ : syracuseStep 2055953 = 1541965) B1541965
theorem B63332117 : Blo 1370504 63332117 := bstep (se 6 (by rfl) ⟨1484346, by rfl⟩ : syracuseStep 63332117 = 2968693) B2968693
theorem B2055971 : Blo 1370504 2055971 := bstep (se 1 (by rfl) ⟨1541978, by rfl⟩ : syracuseStep 2055971 = 3083957) B3083957
theorem B8789795 : Blo 1370504 8789795 := bstep (se 1 (by rfl) ⟨6592346, by rfl⟩ : syracuseStep 8789795 = 13184693) B13184693
theorem B2056001 : Blo 1370504 2056001 := bstep (se 2 (by rfl) ⟨771000, by rfl⟩ : syracuseStep 2056001 = 1542001) B1542001
theorem B2056019 : Blo 1370504 2056019 := bstep (se 1 (by rfl) ⟨1542014, by rfl⟩ : syracuseStep 2056019 = 3084029) B3084029
theorem B2056049 : Blo 1370504 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B2056067 : Blo 1370504 2056067 := bstep (se 1 (by rfl) ⟨1542050, by rfl⟩ : syracuseStep 2056067 = 3084101) B3084101
theorem B2056097 : Blo 1370504 2056097 := bstep (se 2 (by rfl) ⟨771036, by rfl⟩ : syracuseStep 2056097 = 1542073) B1542073
theorem B2056115 : Blo 1370504 2056115 := bstep (se 1 (by rfl) ⟨1542086, by rfl⟩ : syracuseStep 2056115 = 3084173) B3084173
theorem B2056145 : Blo 1370504 2056145 := bstep (se 2 (by rfl) ⟨771054, by rfl⟩ : syracuseStep 2056145 = 1542109) B1542109
theorem B2056163 : Blo 1370504 2056163 := bstep (se 1 (by rfl) ⟨1542122, by rfl⟩ : syracuseStep 2056163 = 3084245) B3084245
theorem B5857265 : Blo 1370504 5857265 := bstep (se 2 (by rfl) ⟨2196474, by rfl⟩ : syracuseStep 5857265 = 4392949) B4392949
theorem B5562391 : Blo 1370504 5562391 := bstep (se 1 (by rfl) ⟨4171793, by rfl⟩ : syracuseStep 5562391 = 8343587) B8343587
theorem B2056217 : Blo 1370504 2056217 := bstep (se 2 (by rfl) ⟨771081, by rfl⟩ : syracuseStep 2056217 = 1542163) B1542163
theorem B4227137 : Blo 1370504 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B4628555 : Blo 1370504 4628555 := bstep (se 1 (by rfl) ⟨3471416, by rfl⟩ : syracuseStep 4628555 = 6942833) B6942833
theorem B2056331 : Blo 1370504 2056331 := bstep (se 1 (by rfl) ⟨1542248, by rfl⟩ : syracuseStep 2056331 = 3084497) B3084497
theorem B2056343 : Blo 1370504 2056343 := bstep (se 1 (by rfl) ⟨1542257, by rfl⟩ : syracuseStep 2056343 = 3084515) B3084515
theorem B2056409 : Blo 1370504 2056409 := bstep (se 2 (by rfl) ⟨771153, by rfl⟩ : syracuseStep 2056409 = 1542307) B1542307
theorem B7414033 : Blo 1370504 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B6938945 : Blo 1370504 6938945 := bstep (se 2 (by rfl) ⟨2602104, by rfl⟩ : syracuseStep 6938945 = 5204209) B5204209
theorem B2056523 : Blo 1370504 2056523 := bstep (se 1 (by rfl) ⟨1542392, by rfl⟩ : syracuseStep 2056523 = 3084785) B3084785
theorem B2056535 : Blo 1370504 2056535 := bstep (se 1 (by rfl) ⟨1542401, by rfl⟩ : syracuseStep 2056535 = 3084803) B3084803
theorem B4628825 : Blo 1370504 4628825 := bstep (se 2 (by rfl) ⟨1735809, by rfl⟩ : syracuseStep 4628825 = 3471619) B3471619
theorem B2056601 : Blo 1370504 2056601 := bstep (se 2 (by rfl) ⟨771225, by rfl⟩ : syracuseStep 2056601 = 1542451) B1542451
theorem B10412549 : Blo 1370504 10412549 := bstep (se 4 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 10412549 = 1952353) B1952353
theorem B2056715 : Blo 1370504 2056715 := bstep (se 1 (by rfl) ⟨1542536, by rfl⟩ : syracuseStep 2056715 = 3085073) B3085073
theorem B2056727 : Blo 1370504 2056727 := bstep (se 1 (by rfl) ⟨1542545, by rfl⟩ : syracuseStep 2056727 = 3085091) B3085091
theorem B4391489 : Blo 1370504 4391489 := bstep (se 2 (by rfl) ⟨1646808, by rfl⟩ : syracuseStep 4391489 = 3293617) B3293617
theorem B2056793 : Blo 1370504 2056793 := bstep (se 2 (by rfl) ⟨771297, by rfl⟩ : syracuseStep 2056793 = 1542595) B1542595
theorem B4391617 : Blo 1370504 4391617 := bstep (se 2 (by rfl) ⟨1646856, by rfl⟩ : syracuseStep 4391617 = 3293713) B3293713
theorem B2056907 : Blo 1370504 2056907 := bstep (se 1 (by rfl) ⟨1542680, by rfl⟩ : syracuseStep 2056907 = 3085361) B3085361
theorem B2056919 : Blo 1370504 2056919 := bstep (se 1 (by rfl) ⟨1542689, by rfl⟩ : syracuseStep 2056919 = 3085379) B3085379
theorem B2056985 : Blo 1370504 2056985 := bstep (se 2 (by rfl) ⟨771369, by rfl⟩ : syracuseStep 2056985 = 1542739) B1542739
theorem B2057099 : Blo 1370504 2057099 := bstep (se 1 (by rfl) ⟨1542824, by rfl⟩ : syracuseStep 2057099 = 3085649) B3085649
theorem B2057111 : Blo 1370504 2057111 := bstep (se 1 (by rfl) ⟨1542833, by rfl⟩ : syracuseStep 2057111 = 3085667) B3085667
theorem B4391873 : Blo 1370504 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B2057177 : Blo 1370504 2057177 := bstep (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) B1542883
theorem B4629527 : Blo 1370504 4629527 := bstep (se 1 (by rfl) ⟨3472145, by rfl⟩ : syracuseStep 4629527 = 6944291) B6944291
theorem B2057291 : Blo 1370504 2057291 := bstep (se 1 (by rfl) ⟨1542968, by rfl⟩ : syracuseStep 2057291 = 3085937) B3085937
theorem B2057303 : Blo 1370504 2057303 := bstep (se 1 (by rfl) ⟨1542977, by rfl⟩ : syracuseStep 2057303 = 3085955) B3085955
theorem B6341777 : Blo 1370504 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B2057369 : Blo 1370504 2057369 := bstep (se 2 (by rfl) ⟨771513, by rfl⟩ : syracuseStep 2057369 = 1543027) B1543027
theorem B5858563 : Blo 1370504 5858563 := bstep (se 1 (by rfl) ⟨4393922, by rfl⟩ : syracuseStep 5858563 = 8787845) B8787845
theorem B2057483 : Blo 1370504 2057483 := bstep (se 1 (by rfl) ⟨1543112, by rfl⟩ : syracuseStep 2057483 = 3086225) B3086225
theorem B2057495 : Blo 1370504 2057495 := bstep (se 1 (by rfl) ⟨1543121, by rfl⟩ : syracuseStep 2057495 = 3086243) B3086243
theorem B2778455 : Blo 1370504 2778455 := bstep (se 1 (by rfl) ⟨2083841, by rfl⟩ : syracuseStep 2778455 = 4167683) B4167683
theorem B2057561 : Blo 1370504 2057561 := bstep (se 2 (by rfl) ⟨771585, by rfl⟩ : syracuseStep 2057561 = 1543171) B1543171
theorem B2057675 : Blo 1370504 2057675 := bstep (se 1 (by rfl) ⟨1543256, by rfl⟩ : syracuseStep 2057675 = 3086513) B3086513
theorem B2057687 : Blo 1370504 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B2344459 : Blo 1370504 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B2057753 : Blo 1370504 2057753 := bstep (se 2 (by rfl) ⟨771657, by rfl⟩ : syracuseStep 2057753 = 1543315) B1543315
theorem B4630067 : Blo 1370504 4630067 := bstep (se 1 (by rfl) ⟨3472550, by rfl⟩ : syracuseStep 4630067 = 6945101) B6945101
theorem B5858905 : Blo 1370504 5858905 := bstep (se 2 (by rfl) ⟨2197089, by rfl⟩ : syracuseStep 5858905 = 4394179) B4394179
theorem B14460547 : Blo 1370504 14460547 := bstep (se 1 (by rfl) ⟨10845410, by rfl⟩ : syracuseStep 14460547 = 21690821) B21690821
theorem B2057867 : Blo 1370504 2057867 := bstep (se 1 (by rfl) ⟨1543400, by rfl⟩ : syracuseStep 2057867 = 3086801) B3086801
theorem B2057879 : Blo 1370504 2057879 := bstep (se 1 (by rfl) ⟨1543409, by rfl⟩ : syracuseStep 2057879 = 3086819) B3086819
theorem B2057945 : Blo 1370504 2057945 := bstep (se 2 (by rfl) ⟨771729, by rfl⟩ : syracuseStep 2057945 = 1543459) B1543459
theorem B1951499 : Blo 1370504 1951499 := bstep (se 1 (by rfl) ⟨1463624, by rfl⟩ : syracuseStep 1951499 = 2927249) B2927249
theorem B1541911 : Blo 1370504 1541911 := bstep (se 1 (by rfl) ⟨1156433, by rfl⟩ : syracuseStep 1541911 = 2312867) B2312867
theorem B4630337 : Blo 1370504 4630337 := bstep (se 2 (by rfl) ⟨1736376, by rfl⟩ : syracuseStep 4630337 = 3472753) B3472753
theorem B3958721 : Blo 1370504 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1542091 : Blo 1370504 1542091 := bstep (se 1 (by rfl) ⟨1156568, by rfl⟩ : syracuseStep 1542091 = 2313137) B2313137
theorem B3958835 : Blo 1370504 3958835 := bstep (se 1 (by rfl) ⟨2969126, by rfl⟩ : syracuseStep 3958835 = 5938253) B5938253
theorem B1542199 : Blo 1370504 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B7415873 : Blo 1370504 7415873 := bstep (se 2 (by rfl) ⟨2780952, by rfl⟩ : syracuseStep 7415873 = 5561905) B5561905
theorem B14067863 : Blo 1370504 14067863 := bstep (se 1 (by rfl) ⟨10550897, by rfl⟩ : syracuseStep 14067863 = 21101795) B21101795
theorem B6940889 : Blo 1370504 6940889 := bstep (se 2 (by rfl) ⟨2602833, by rfl⟩ : syracuseStep 6940889 = 5205667) B5205667
theorem B1542379 : Blo 1370504 1542379 := bstep (se 1 (by rfl) ⟨1156784, by rfl⟩ : syracuseStep 1542379 = 2313569) B2313569
theorem B1542487 : Blo 1370504 1542487 := bstep (se 1 (by rfl) ⟨1156865, by rfl⟩ : syracuseStep 1542487 = 2313731) B2313731
theorem B1370507 : Blo 1370504 1370507 := bstep (se 1 (by rfl) ⟨1027880, by rfl⟩ : syracuseStep 1370507 = 2055761) B2055761
theorem B1370519 : Blo 1370504 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B1370539 : Blo 1370504 1370539 := bstep (se 1 (by rfl) ⟨1027904, by rfl⟩ : syracuseStep 1370539 = 2055809) B2055809
theorem B1370551 : Blo 1370504 1370551 := bstep (se 1 (by rfl) ⟨1027913, by rfl⟩ : syracuseStep 1370551 = 2055827) B2055827
theorem B6343105 : Blo 1370504 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B1370571 : Blo 1370504 1370571 := bstep (se 1 (by rfl) ⟨1027928, by rfl⟩ : syracuseStep 1370571 = 2055857) B2055857
theorem B1370583 : Blo 1370504 1370583 := bstep (se 1 (by rfl) ⟨1027937, by rfl⟩ : syracuseStep 1370583 = 2055875) B2055875
theorem B1370603 : Blo 1370504 1370603 := bstep (se 1 (by rfl) ⟨1027952, by rfl⟩ : syracuseStep 1370603 = 2055905) B2055905
theorem B1370615 : Blo 1370504 1370615 := bstep (se 1 (by rfl) ⟨1027961, by rfl⟩ : syracuseStep 1370615 = 2055923) B2055923
theorem B5204483 : Blo 1370504 5204483 := bstep (se 1 (by rfl) ⟨3903362, by rfl⟩ : syracuseStep 5204483 = 7806725) B7806725
theorem B1370635 : Blo 1370504 1370635 := bstep (se 1 (by rfl) ⟨1027976, by rfl⟩ : syracuseStep 1370635 = 2055953) B2055953
theorem B1542667 : Blo 1370504 1542667 := bstep (se 1 (by rfl) ⟨1157000, by rfl⟩ : syracuseStep 1542667 = 2314001) B2314001
theorem B1370647 : Blo 1370504 1370647 := bstep (se 1 (by rfl) ⟨1027985, by rfl⟩ : syracuseStep 1370647 = 2055971) B2055971
theorem B5859863 : Blo 1370504 5859863 := bstep (se 1 (by rfl) ⟨4394897, by rfl⟩ : syracuseStep 5859863 = 8789795) B8789795
theorem B1370667 : Blo 1370504 1370667 := bstep (se 1 (by rfl) ⟨1028000, by rfl⟩ : syracuseStep 1370667 = 2056001) B2056001
theorem B1370679 : Blo 1370504 1370679 := bstep (se 1 (by rfl) ⟨1028009, by rfl⟩ : syracuseStep 1370679 = 2056019) B2056019
theorem B2312779 : Blo 1370504 2312779 := bstep (se 1 (by rfl) ⟨1734584, by rfl⟩ : syracuseStep 2312779 = 3469169) B3469169
theorem B1370699 : Blo 1370504 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1370711 : Blo 1370504 1370711 := bstep (se 1 (by rfl) ⟨1028033, by rfl⟩ : syracuseStep 1370711 = 2056067) B2056067
theorem B6589021 : Blo 1370504 6589021 := bstep (se 3 (by rfl) ⟨1235441, by rfl⟩ : syracuseStep 6589021 = 2470883) B2470883
theorem B4393565 : Blo 1370504 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B1370731 : Blo 1370504 1370731 := bstep (se 1 (by rfl) ⟨1028048, by rfl⟩ : syracuseStep 1370731 = 2056097) B2056097
theorem B1370743 : Blo 1370504 1370743 := bstep (se 1 (by rfl) ⟨1028057, by rfl⟩ : syracuseStep 1370743 = 2056115) B2056115
theorem B1542775 : Blo 1370504 1542775 := bstep (se 1 (by rfl) ⟨1157081, by rfl⟩ : syracuseStep 1542775 = 2314163) B2314163
theorem B1370763 : Blo 1370504 1370763 := bstep (se 1 (by rfl) ⟨1028072, by rfl⟩ : syracuseStep 1370763 = 2056145) B2056145
theorem B1370775 : Blo 1370504 1370775 := bstep (se 1 (by rfl) ⟨1028081, by rfl⟩ : syracuseStep 1370775 = 2056163) B2056163
theorem B1370795 : Blo 1370504 1370795 := bstep (se 1 (by rfl) ⟨1028096, by rfl⟩ : syracuseStep 1370795 = 2056193) B2056193
theorem B1370807 : Blo 1370504 1370807 := bstep (se 1 (by rfl) ⟨1028105, by rfl⟩ : syracuseStep 1370807 = 2056211) B2056211
theorem B1370827 : Blo 1370504 1370827 := bstep (se 1 (by rfl) ⟨1028120, by rfl⟩ : syracuseStep 1370827 = 2056241) B2056241
theorem B1370839 : Blo 1370504 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B2312921 : Blo 1370504 2312921 := bstep (se 2 (by rfl) ⟨867345, by rfl⟩ : syracuseStep 2312921 = 1734691) B1734691
theorem B1370859 : Blo 1370504 1370859 := bstep (se 1 (by rfl) ⟨1028144, by rfl⟩ : syracuseStep 1370859 = 2056289) B2056289
theorem B1370871 : Blo 1370504 1370871 := bstep (se 1 (by rfl) ⟨1028153, by rfl⟩ : syracuseStep 1370871 = 2056307) B2056307
theorem B1370891 : Blo 1370504 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B1370903 : Blo 1370504 1370903 := bstep (se 1 (by rfl) ⟨1028177, by rfl⟩ : syracuseStep 1370903 = 2056355) B2056355
theorem B1370923 : Blo 1370504 1370923 := bstep (se 1 (by rfl) ⟨1028192, by rfl⟩ : syracuseStep 1370923 = 2056385) B2056385
theorem B14822189 : Blo 1370504 14822189 := bstep (se 3 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 14822189 = 5558321) B5558321
theorem B1542955 : Blo 1370504 1542955 := bstep (se 1 (by rfl) ⟨1157216, by rfl⟩ : syracuseStep 1542955 = 2314433) B2314433
theorem B1370935 : Blo 1370504 1370935 := bstep (se 1 (by rfl) ⟨1028201, by rfl⟩ : syracuseStep 1370935 = 2056403) B2056403
theorem B1370955 : Blo 1370504 1370955 := bstep (se 1 (by rfl) ⟨1028216, by rfl⟩ : syracuseStep 1370955 = 2056433) B2056433
theorem B1370967 : Blo 1370504 1370967 := bstep (se 1 (by rfl) ⟨1028225, by rfl⟩ : syracuseStep 1370967 = 2056451) B2056451
theorem B2313049 : Blo 1370504 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B1370987 : Blo 1370504 1370987 := bstep (se 1 (by rfl) ⟨1028240, by rfl⟩ : syracuseStep 1370987 = 2056481) B2056481
theorem B1370999 : Blo 1370504 1370999 := bstep (se 1 (by rfl) ⟨1028249, by rfl⟩ : syracuseStep 1370999 = 2056499) B2056499
theorem B10414979 : Blo 1370504 10414979 := bstep (se 1 (by rfl) ⟨7811234, by rfl⟩ : syracuseStep 10414979 = 15622469) B15622469
theorem B1371019 : Blo 1370504 1371019 := bstep (se 1 (by rfl) ⟨1028264, by rfl⟩ : syracuseStep 1371019 = 2056529) B2056529
theorem B1371031 : Blo 1370504 1371031 := bstep (se 1 (by rfl) ⟨1028273, by rfl⟩ : syracuseStep 1371031 = 2056547) B2056547
theorem B1543063 : Blo 1370504 1543063 := bstep (se 1 (by rfl) ⟨1157297, by rfl⟩ : syracuseStep 1543063 = 2314595) B2314595
theorem B1371051 : Blo 1370504 1371051 := bstep (se 1 (by rfl) ⟨1028288, by rfl⟩ : syracuseStep 1371051 = 2056577) B2056577
theorem B2927539 : Blo 1370504 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B1371063 : Blo 1370504 1371063 := bstep (se 1 (by rfl) ⟨1028297, by rfl⟩ : syracuseStep 1371063 = 2056595) B2056595
theorem B1371083 : Blo 1370504 1371083 := bstep (se 1 (by rfl) ⟨1028312, by rfl⟩ : syracuseStep 1371083 = 2056625) B2056625
theorem B1371095 : Blo 1370504 1371095 := bstep (se 1 (by rfl) ⟨1028321, by rfl⟩ : syracuseStep 1371095 = 2056643) B2056643
theorem B1371115 : Blo 1370504 1371115 := bstep (se 1 (by rfl) ⟨1028336, by rfl⟩ : syracuseStep 1371115 = 2056673) B2056673
theorem B1371127 : Blo 1370504 1371127 := bstep (se 1 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 1371127 = 2056691) B2056691
theorem B1371147 : Blo 1370504 1371147 := bstep (se 1 (by rfl) ⟨1028360, by rfl⟩ : syracuseStep 1371147 = 2056721) B2056721
theorem B1371159 : Blo 1370504 1371159 := bstep (se 1 (by rfl) ⟨1028369, by rfl⟩ : syracuseStep 1371159 = 2056739) B2056739
theorem B1371179 : Blo 1370504 1371179 := bstep (se 1 (by rfl) ⟨1028384, by rfl⟩ : syracuseStep 1371179 = 2056769) B2056769
theorem B1371191 : Blo 1370504 1371191 := bstep (se 1 (by rfl) ⟨1028393, by rfl⟩ : syracuseStep 1371191 = 2056787) B2056787
theorem B2083915 : Blo 1370504 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B1371211 : Blo 1370504 1371211 := bstep (se 1 (by rfl) ⟨1028408, by rfl⟩ : syracuseStep 1371211 = 2056817) B2056817
theorem B1543243 : Blo 1370504 1543243 := bstep (se 1 (by rfl) ⟨1157432, by rfl⟩ : syracuseStep 1543243 = 2314865) B2314865
theorem B1371223 : Blo 1370504 1371223 := bstep (se 1 (by rfl) ⟨1028417, by rfl⟩ : syracuseStep 1371223 = 2056835) B2056835
theorem B7810141 : Blo 1370504 7810141 := bstep (se 3 (by rfl) ⟨1464401, by rfl⟩ : syracuseStep 7810141 = 2928803) B2928803
theorem B1371243 : Blo 1370504 1371243 := bstep (se 1 (by rfl) ⟨1028432, by rfl⟩ : syracuseStep 1371243 = 2056865) B2056865
theorem B1371255 : Blo 1370504 1371255 := bstep (se 1 (by rfl) ⟨1028441, by rfl⟩ : syracuseStep 1371255 = 2056883) B2056883
theorem B1371275 : Blo 1370504 1371275 := bstep (se 1 (by rfl) ⟨1028456, by rfl⟩ : syracuseStep 1371275 = 2056913) B2056913
theorem B1371287 : Blo 1370504 1371287 := bstep (se 1 (by rfl) ⟨1028465, by rfl⟩ : syracuseStep 1371287 = 2056931) B2056931
theorem B1371307 : Blo 1370504 1371307 := bstep (se 1 (by rfl) ⟨1028480, by rfl⟩ : syracuseStep 1371307 = 2056961) B2056961
theorem B1371319 : Blo 1370504 1371319 := bstep (se 1 (by rfl) ⟨1028489, by rfl⟩ : syracuseStep 1371319 = 2056979) B2056979
theorem B1543351 : Blo 1370504 1543351 := bstep (se 1 (by rfl) ⟨1157513, by rfl⟩ : syracuseStep 1543351 = 2315027) B2315027
theorem B1371339 : Blo 1370504 1371339 := bstep (se 1 (by rfl) ⟨1028504, by rfl⟩ : syracuseStep 1371339 = 2057009) B2057009
theorem B1371351 : Blo 1370504 1371351 := bstep (se 1 (by rfl) ⟨1028513, by rfl⟩ : syracuseStep 1371351 = 2057027) B2057027
theorem B1371371 : Blo 1370504 1371371 := bstep (se 1 (by rfl) ⟨1028528, by rfl⟩ : syracuseStep 1371371 = 2057057) B2057057
theorem B1371383 : Blo 1370504 1371383 := bstep (se 1 (by rfl) ⟨1028537, by rfl⟩ : syracuseStep 1371383 = 2057075) B2057075
theorem B1371403 : Blo 1370504 1371403 := bstep (se 1 (by rfl) ⟨1028552, by rfl⟩ : syracuseStep 1371403 = 2057105) B2057105
theorem B1371415 : Blo 1370504 1371415 := bstep (se 1 (by rfl) ⟨1028561, by rfl⟩ : syracuseStep 1371415 = 2057123) B2057123
theorem B1371435 : Blo 1370504 1371435 := bstep (se 1 (by rfl) ⟨1028576, by rfl⟩ : syracuseStep 1371435 = 2057153) B2057153
theorem B1371447 : Blo 1370504 1371447 := bstep (se 1 (by rfl) ⟨1028585, by rfl⟩ : syracuseStep 1371447 = 2057171) B2057171
theorem B1371467 : Blo 1370504 1371467 := bstep (se 1 (by rfl) ⟨1028600, by rfl⟩ : syracuseStep 1371467 = 2057201) B2057201
theorem B1371479 : Blo 1370504 1371479 := bstep (se 1 (by rfl) ⟨1028609, by rfl⟩ : syracuseStep 1371479 = 2057219) B2057219
theorem B4394333 : Blo 1370504 4394333 := bstep (se 3 (by rfl) ⟨823937, by rfl⟩ : syracuseStep 4394333 = 1647875) B1647875
theorem B17567077 : Blo 1370504 17567077 := bstep (se 4 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 17567077 = 3293827) B3293827
theorem B1371499 : Blo 1370504 1371499 := bstep (se 1 (by rfl) ⟨1028624, by rfl⟩ : syracuseStep 1371499 = 2057249) B2057249
theorem B1371511 : Blo 1370504 1371511 := bstep (se 1 (by rfl) ⟨1028633, by rfl⟩ : syracuseStep 1371511 = 2057267) B2057267
theorem B2928001 : Blo 1370504 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B1371531 : Blo 1370504 1371531 := bstep (se 1 (by rfl) ⟨1028648, by rfl⟩ : syracuseStep 1371531 = 2057297) B2057297
theorem B2313623 : Blo 1370504 2313623 := bstep (se 1 (by rfl) ⟨1735217, by rfl⟩ : syracuseStep 2313623 = 3470435) B3470435
theorem B1371543 : Blo 1370504 1371543 := bstep (se 1 (by rfl) ⟨1028657, by rfl⟩ : syracuseStep 1371543 = 2057315) B2057315
theorem B1371563 : Blo 1370504 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B6254003 : Blo 1370504 6254003 := bstep (se 1 (by rfl) ⟨4690502, by rfl⟩ : syracuseStep 6254003 = 9381005) B9381005
theorem B1371575 : Blo 1370504 1371575 := bstep (se 1 (by rfl) ⟨1028681, by rfl⟩ : syracuseStep 1371575 = 2057363) B2057363
theorem B3083723 : Blo 1370504 3083723 := bstep (se 1 (by rfl) ⟨2312792, by rfl⟩ : syracuseStep 3083723 = 4625585) B4625585
theorem B1371595 : Blo 1370504 1371595 := bstep (se 1 (by rfl) ⟨1028696, by rfl⟩ : syracuseStep 1371595 = 2057393) B2057393
theorem B1371607 : Blo 1370504 1371607 := bstep (se 1 (by rfl) ⟨1028705, by rfl⟩ : syracuseStep 1371607 = 2057411) B2057411
theorem B2346455 : Blo 1370504 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B1371627 : Blo 1370504 1371627 := bstep (se 1 (by rfl) ⟨1028720, by rfl⟩ : syracuseStep 1371627 = 2057441) B2057441
theorem B1371639 : Blo 1370504 1371639 := bstep (se 1 (by rfl) ⟨1028729, by rfl⟩ : syracuseStep 1371639 = 2057459) B2057459
theorem B3083777 : Blo 1370504 3083777 := bstep (se 2 (by rfl) ⟨1156416, by rfl⟩ : syracuseStep 3083777 = 2312833) B2312833
theorem B1371659 : Blo 1370504 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B2313751 : Blo 1370504 2313751 := bstep (se 1 (by rfl) ⟨1735313, by rfl⟩ : syracuseStep 2313751 = 3470627) B3470627
theorem B1371671 : Blo 1370504 1371671 := bstep (se 1 (by rfl) ⟨1028753, by rfl⟩ : syracuseStep 1371671 = 2057507) B2057507
theorem B1371691 : Blo 1370504 1371691 := bstep (se 1 (by rfl) ⟨1028768, by rfl⟩ : syracuseStep 1371691 = 2057537) B2057537
theorem B1371703 : Blo 1370504 1371703 := bstep (se 1 (by rfl) ⟨1028777, by rfl⟩ : syracuseStep 1371703 = 2057555) B2057555
theorem B1371723 : Blo 1370504 1371723 := bstep (se 1 (by rfl) ⟨1028792, by rfl⟩ : syracuseStep 1371723 = 2057585) B2057585
theorem B1371735 : Blo 1370504 1371735 := bstep (se 1 (by rfl) ⟨1028801, by rfl⟩ : syracuseStep 1371735 = 2057603) B2057603
theorem B1371755 : Blo 1370504 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B1371767 : Blo 1370504 1371767 := bstep (se 1 (by rfl) ⟨1028825, by rfl⟩ : syracuseStep 1371767 = 2057651) B2057651
theorem B1371787 : Blo 1370504 1371787 := bstep (se 1 (by rfl) ⟨1028840, by rfl⟩ : syracuseStep 1371787 = 2057681) B2057681
theorem B1371799 : Blo 1370504 1371799 := bstep (se 1 (by rfl) ⟨1028849, by rfl⟩ : syracuseStep 1371799 = 2057699) B2057699
theorem B1371819 : Blo 1370504 1371819 := bstep (se 1 (by rfl) ⟨1028864, by rfl⟩ : syracuseStep 1371819 = 2057729) B2057729
theorem B1371831 : Blo 1370504 1371831 := bstep (se 1 (by rfl) ⟨1028873, by rfl⟩ : syracuseStep 1371831 = 2057747) B2057747
theorem B1371851 : Blo 1370504 1371851 := bstep (se 1 (by rfl) ⟨1028888, by rfl⟩ : syracuseStep 1371851 = 2057777) B2057777
theorem B50024141 : Blo 1370504 50024141 := bstep (se 3 (by rfl) ⟨9379526, by rfl⟩ : syracuseStep 50024141 = 18759053) B18759053
theorem B1371863 : Blo 1370504 1371863 := bstep (se 1 (by rfl) ⟨1028897, by rfl⟩ : syracuseStep 1371863 = 2057795) B2057795
theorem B3083993 : Blo 1370504 3083993 := bstep (se 2 (by rfl) ⟨1156497, by rfl⟩ : syracuseStep 3083993 = 2312995) B2312995
theorem B1371883 : Blo 1370504 1371883 := bstep (se 1 (by rfl) ⟨1028912, by rfl⟩ : syracuseStep 1371883 = 2057825) B2057825
theorem B1371895 : Blo 1370504 1371895 := bstep (se 1 (by rfl) ⟨1028921, by rfl⟩ : syracuseStep 1371895 = 2057843) B2057843
theorem B1371915 : Blo 1370504 1371915 := bstep (se 1 (by rfl) ⟨1028936, by rfl⟩ : syracuseStep 1371915 = 2057873) B2057873
theorem B1371927 : Blo 1370504 1371927 := bstep (se 1 (by rfl) ⟨1028945, by rfl⟩ : syracuseStep 1371927 = 2057891) B2057891
theorem B2084633 : Blo 1370504 2084633 := bstep (se 2 (by rfl) ⟨781737, by rfl⟩ : syracuseStep 2084633 = 1563475) B1563475
theorem B1371947 : Blo 1370504 1371947 := bstep (se 1 (by rfl) ⟨1028960, by rfl⟩ : syracuseStep 1371947 = 2057921) B2057921
theorem B6942509 : Blo 1370504 6942509 := bstep (se 3 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 6942509 = 2603441) B2603441
theorem B3084083 : Blo 1370504 3084083 := bstep (se 1 (by rfl) ⟨2313062, by rfl⟩ : syracuseStep 3084083 = 4626125) B4626125
theorem B5009203 : Blo 1370504 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B1371959 : Blo 1370504 1371959 := bstep (se 1 (by rfl) ⟨1028969, by rfl⟩ : syracuseStep 1371959 = 2057939) B2057939
theorem B1371979 : Blo 1370504 1371979 := bstep (se 1 (by rfl) ⟨1028984, by rfl⟩ : syracuseStep 1371979 = 2057969) B2057969
theorem B3084119 : Blo 1370504 3084119 := bstep (se 1 (by rfl) ⟨2313089, by rfl⟩ : syracuseStep 3084119 = 4626179) B4626179
theorem B1371991 : Blo 1370504 1371991 := bstep (se 1 (by rfl) ⟨1028993, by rfl⟩ : syracuseStep 1371991 = 2057987) B2057987
theorem B4394845 : Blo 1370504 4394845 := bstep (se 3 (by rfl) ⟨824033, by rfl⟩ : syracuseStep 4394845 = 1648067) B1648067
theorem B2781067 : Blo 1370504 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B3084299 : Blo 1370504 3084299 := bstep (se 1 (by rfl) ⟨2313224, by rfl⟩ : syracuseStep 3084299 = 4626449) B4626449
theorem B3903511 : Blo 1370504 3903511 := bstep (se 1 (by rfl) ⟨2927633, by rfl⟩ : syracuseStep 3903511 = 5855267) B5855267
theorem B3706931 : Blo 1370504 3706931 := bstep (se 1 (by rfl) ⟨2780198, by rfl⟩ : syracuseStep 3706931 = 5560397) B5560397
theorem B3084353 : Blo 1370504 3084353 := bstep (se 2 (by rfl) ⟨1156632, by rfl⟩ : syracuseStep 3084353 = 2313265) B2313265
theorem B2928727 : Blo 1370504 2928727 := bstep (se 1 (by rfl) ⟨2196545, by rfl⟩ : syracuseStep 2928727 = 4393091) B4393091
theorem B11710565 : Blo 1370504 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B2314379 : Blo 1370504 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B3469463 : Blo 1370504 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B3518657 : Blo 1370504 3518657 := bstep (se 2 (by rfl) ⟨1319496, by rfl⟩ : syracuseStep 3518657 = 2638993) B2638993
theorem B2314507 : Blo 1370504 2314507 := bstep (se 1 (by rfl) ⟨1735880, by rfl⟩ : syracuseStep 2314507 = 3471761) B3471761
theorem B7516433 : Blo 1370504 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B3084569 : Blo 1370504 3084569 := bstep (se 2 (by rfl) ⟨1156713, by rfl⟩ : syracuseStep 3084569 = 2313427) B2313427
theorem B8343901 : Blo 1370504 8343901 := bstep (se 3 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 8343901 = 3128963) B3128963
theorem B3084659 : Blo 1370504 3084659 := bstep (se 1 (by rfl) ⟨2313494, by rfl⟩ : syracuseStep 3084659 = 4626989) B4626989
theorem B3084695 : Blo 1370504 3084695 := bstep (se 1 (by rfl) ⟨2313521, by rfl⟩ : syracuseStep 3084695 = 4627043) B4627043
theorem B2314649 : Blo 1370504 2314649 := bstep (se 2 (by rfl) ⟨867993, by rfl⟩ : syracuseStep 2314649 = 1735987) B1735987
theorem B2314777 : Blo 1370504 2314777 := bstep (se 2 (by rfl) ⟨868041, by rfl⟩ : syracuseStep 2314777 = 1736083) B1736083
theorem B3084875 : Blo 1370504 3084875 := bstep (se 1 (by rfl) ⟨2313656, by rfl⟩ : syracuseStep 3084875 = 4627313) B4627313
theorem B3084929 : Blo 1370504 3084929 := bstep (se 2 (by rfl) ⟨1156848, by rfl⟩ : syracuseStep 3084929 = 2313697) B2313697
theorem B3568279 : Blo 1370504 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B1979083 : Blo 1370504 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B11711249 : Blo 1370504 11711249 := bstep (se 2 (by rfl) ⟨4391718, by rfl⟩ : syracuseStep 11711249 = 8783437) B8783437
theorem B11268881 : Blo 1370504 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B3085145 : Blo 1370504 3085145 := bstep (se 2 (by rfl) ⟨1156929, by rfl⟩ : syracuseStep 3085145 = 2313859) B2313859
theorem B8786819 : Blo 1370504 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B2929547 : Blo 1370504 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B12678065 : Blo 1370504 12678065 := bstep (se 2 (by rfl) ⟨4754274, by rfl⟩ : syracuseStep 12678065 = 9508549) B9508549
theorem B3085235 : Blo 1370504 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B3470273 : Blo 1370504 3470273 := bstep (se 2 (by rfl) ⟨1301352, by rfl⟩ : syracuseStep 3470273 = 2602705) B2602705
theorem B3085271 : Blo 1370504 3085271 := bstep (se 1 (by rfl) ⟨2313953, by rfl⟩ : syracuseStep 3085271 = 4627907) B4627907
theorem B2470999 : Blo 1370504 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B3339353 : Blo 1370504 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B3085451 : Blo 1370504 3085451 := bstep (se 1 (by rfl) ⟨2314088, by rfl⟩ : syracuseStep 3085451 = 4628177) B4628177
theorem B2602135 : Blo 1370504 2602135 := bstep (se 1 (by rfl) ⟨1951601, by rfl⟩ : syracuseStep 2602135 = 3903203) B3903203
theorem B3708055 : Blo 1370504 3708055 := bstep (se 1 (by rfl) ⟨2781041, by rfl⟩ : syracuseStep 3708055 = 5562083) B5562083
theorem B3085505 : Blo 1370504 3085505 := bstep (se 2 (by rfl) ⟨1157064, by rfl⟩ : syracuseStep 3085505 = 2314129) B2314129
theorem B3519767 : Blo 1370504 3519767 := bstep (se 1 (by rfl) ⟨2639825, by rfl⟩ : syracuseStep 3519767 = 5279651) B5279651
theorem B3904843 : Blo 1370504 3904843 := bstep (se 1 (by rfl) ⟨2928632, by rfl⟩ : syracuseStep 3904843 = 5857265) B5857265
theorem B3085721 : Blo 1370504 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B3470809 : Blo 1370504 3470809 := bstep (se 2 (by rfl) ⟨1301553, by rfl⟩ : syracuseStep 3470809 = 2603107) B2603107
theorem B3085811 : Blo 1370504 3085811 := bstep (se 1 (by rfl) ⟨2314358, by rfl⟩ : syracuseStep 3085811 = 4628717) B4628717
theorem B42792461 : Blo 1370504 42792461 := bstep (se 3 (by rfl) ⟨8023586, by rfl⟩ : syracuseStep 42792461 = 16047173) B16047173
theorem B3085847 : Blo 1370504 3085847 := bstep (se 1 (by rfl) ⟨2314385, by rfl⟩ : syracuseStep 3085847 = 4628771) B4628771
theorem B5207597 : Blo 1370504 5207597 := bstep (se 3 (by rfl) ⟨976424, by rfl⟩ : syracuseStep 5207597 = 1952849) B1952849
theorem B7411265 : Blo 1370504 7411265 := bstep (se 2 (by rfl) ⟨2779224, by rfl⟩ : syracuseStep 7411265 = 5558449) B5558449
theorem B2504267 : Blo 1370504 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B3905117 : Blo 1370504 3905117 := bstep (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) B1464419
theorem B4626071 : Blo 1370504 4626071 := bstep (se 1 (by rfl) ⟨3469553, by rfl⟩ : syracuseStep 4626071 = 6939107) B6939107
theorem B1980055 : Blo 1370504 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B3086027 : Blo 1370504 3086027 := bstep (se 1 (by rfl) ⟨2314520, by rfl⟩ : syracuseStep 3086027 = 4629041) B4629041
theorem B2471639 : Blo 1370504 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B8337113 : Blo 1370504 8337113 := bstep (se 2 (by rfl) ⟨3126417, by rfl⟩ : syracuseStep 8337113 = 6252835) B6252835
theorem B1464043 : Blo 1370504 1464043 := bstep (se 1 (by rfl) ⟨1098032, by rfl⟩ : syracuseStep 1464043 = 2196065) B2196065
theorem B3086081 : Blo 1370504 3086081 := bstep (se 2 (by rfl) ⟨1157280, by rfl⟩ : syracuseStep 3086081 = 2314561) B2314561
theorem B1390411 : Blo 1370504 1390411 := bstep (se 1 (by rfl) ⟨1042808, by rfl⟩ : syracuseStep 1390411 = 2085617) B2085617
theorem B3905459 : Blo 1370504 3905459 := bstep (se 1 (by rfl) ⟨2929094, by rfl⟩ : syracuseStep 3905459 = 5858189) B5858189
theorem B2602955 : Blo 1370504 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B3086297 : Blo 1370504 3086297 := bstep (se 2 (by rfl) ⟨1157361, by rfl⟩ : syracuseStep 3086297 = 2314723) B2314723
theorem B2603009 : Blo 1370504 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B3086387 : Blo 1370504 3086387 := bstep (se 1 (by rfl) ⟨2314790, by rfl⟩ : syracuseStep 3086387 = 4629581) B4629581
theorem B3086423 : Blo 1370504 3086423 := bstep (se 1 (by rfl) ⟨2314817, by rfl⟩ : syracuseStep 3086423 = 4629635) B4629635
theorem B3127385 : Blo 1370504 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B10582109 : Blo 1370504 10582109 := bstep (se 3 (by rfl) ⟨1984145, by rfl⟩ : syracuseStep 10582109 = 3968291) B3968291
theorem B4626611 : Blo 1370504 4626611 := bstep (se 1 (by rfl) ⟨3469958, by rfl⟩ : syracuseStep 4626611 = 6939917) B6939917
theorem B10418381 : Blo 1370504 10418381 := bstep (se 3 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 10418381 = 3906893) B3906893
theorem B15644933 : Blo 1370504 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B3086603 : Blo 1370504 3086603 := bstep (se 1 (by rfl) ⟨2314952, by rfl⟩ : syracuseStep 3086603 = 4629905) B4629905
theorem B5208371 : Blo 1370504 5208371 := bstep (se 1 (by rfl) ⟨3906278, by rfl⟩ : syracuseStep 5208371 = 7812557) B7812557
theorem B3086657 : Blo 1370504 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B2005337 : Blo 1370504 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B4626881 : Blo 1370504 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B11868677 : Blo 1370504 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B3086873 : Blo 1370504 3086873 := bstep (se 2 (by rfl) ⟨1157577, by rfl⟩ : syracuseStep 3086873 = 2315155) B2315155
theorem B3471923 : Blo 1370504 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B3086963 : Blo 1370504 3086963 := bstep (se 1 (by rfl) ⟨2315222, by rfl⟩ : syracuseStep 3086963 = 4630445) B4630445
theorem B3086999 : Blo 1370504 3086999 := bstep (se 1 (by rfl) ⟨2315249, by rfl⟩ : syracuseStep 3086999 = 4630499) B4630499
theorem B1735435 : Blo 1370504 1735435 := bstep (se 1 (by rfl) ⟨1301576, by rfl⟩ : syracuseStep 1735435 = 2603153) B2603153
theorem B3472217 : Blo 1370504 3472217 := bstep (se 2 (by rfl) ⟨1302081, by rfl⟩ : syracuseStep 3472217 = 2604163) B2604163
theorem B2603927 : Blo 1370504 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B4627421 : Blo 1370504 4627421 := bstep (se 3 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 4627421 = 1735283) B1735283
theorem B5274845 : Blo 1370504 5274845 := bstep (se 3 (by rfl) ⟨989033, by rfl⟩ : syracuseStep 5274845 = 1978067) B1978067
theorem B2604467 : Blo 1370504 2604467 := bstep (se 1 (by rfl) ⟨1953350, by rfl⟩ : syracuseStep 2604467 = 3906701) B3906701
theorem B2055767 : Blo 1370504 2055767 := bstep (se 1 (by rfl) ⟨1541825, by rfl⟩ : syracuseStep 2055767 = 3083651) B3083651
theorem B2055833 : Blo 1370504 2055833 := bstep (se 2 (by rfl) ⟨770937, by rfl⟩ : syracuseStep 2055833 = 1541875) B1541875
theorem B1736407 : Blo 1370504 1736407 := bstep (se 1 (by rfl) ⟨1302305, by rfl⟩ : syracuseStep 1736407 = 2604611) B2604611
theorem B2055947 : Blo 1370504 2055947 := bstep (se 1 (by rfl) ⟨1541960, by rfl⟩ : syracuseStep 2055947 = 3083921) B3083921
theorem B2055959 : Blo 1370504 2055959 := bstep (se 1 (by rfl) ⟨1541969, by rfl⟩ : syracuseStep 2055959 = 3083939) B3083939
theorem B2056025 : Blo 1370504 2056025 := bstep (se 2 (by rfl) ⟨771009, by rfl⟩ : syracuseStep 2056025 = 1542019) B1542019
theorem B42221411 : Blo 1370504 42221411 := bstep (se 1 (by rfl) ⟨31666058, by rfl⟩ : syracuseStep 42221411 = 63332117) B63332117
theorem B2056139 : Blo 1370504 2056139 := bstep (se 1 (by rfl) ⟨1542104, by rfl⟩ : syracuseStep 2056139 = 3084209) B3084209
theorem B2056151 : Blo 1370504 2056151 := bstep (se 1 (by rfl) ⟨1542113, by rfl⟩ : syracuseStep 2056151 = 3084227) B3084227
theorem B16670681 : Blo 1370504 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B2056199 : Blo 1370504 2056199 := bstep (se 1 (by rfl) ⟨1542149, by rfl⟩ : syracuseStep 2056199 = 3084299) B3084299
theorem B2056235 : Blo 1370504 2056235 := bstep (se 1 (by rfl) ⟨1542176, by rfl⟩ : syracuseStep 2056235 = 3084353) B3084353
theorem B2818091 : Blo 1370504 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B7807043 : Blo 1370504 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B2056265 : Blo 1370504 2056265 := bstep (se 2 (by rfl) ⟨771099, by rfl⟩ : syracuseStep 2056265 = 1542199) B1542199
theorem B2056379 : Blo 1370504 2056379 := bstep (se 1 (by rfl) ⟨1542284, by rfl⟩ : syracuseStep 2056379 = 3084569) B3084569
theorem B8904941 : Blo 1370504 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B2056439 : Blo 1370504 2056439 := bstep (se 1 (by rfl) ⟨1542329, by rfl⟩ : syracuseStep 2056439 = 3084659) B3084659
theorem B2056463 : Blo 1370504 2056463 := bstep (se 1 (by rfl) ⟨1542347, by rfl⟩ : syracuseStep 2056463 = 3084695) B3084695
theorem B2056505 : Blo 1370504 2056505 := bstep (se 2 (by rfl) ⟨771189, by rfl⟩ : syracuseStep 2056505 = 1542379) B1542379
theorem B2056583 : Blo 1370504 2056583 := bstep (se 1 (by rfl) ⟨1542437, by rfl⟩ : syracuseStep 2056583 = 3084875) B3084875
theorem B2056619 : Blo 1370504 2056619 := bstep (se 1 (by rfl) ⟨1542464, by rfl⟩ : syracuseStep 2056619 = 3084929) B3084929
theorem B2056649 : Blo 1370504 2056649 := bstep (se 2 (by rfl) ⟨771243, by rfl⟩ : syracuseStep 2056649 = 1542487) B1542487
theorem B11125201 : Blo 1370504 11125201 := bstep (se 2 (by rfl) ⟨4171950, by rfl⟩ : syracuseStep 11125201 = 8343901) B8343901
theorem B7807499 : Blo 1370504 7807499 := bstep (se 1 (by rfl) ⟨5855624, by rfl⟩ : syracuseStep 7807499 = 11711249) B11711249
theorem B7512587 : Blo 1370504 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B2056763 : Blo 1370504 2056763 := bstep (se 1 (by rfl) ⟨1542572, by rfl⟩ : syracuseStep 2056763 = 3085145) B3085145
theorem B2056823 : Blo 1370504 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B2056847 : Blo 1370504 2056847 := bstep (se 1 (by rfl) ⟨1542635, by rfl⟩ : syracuseStep 2056847 = 3085271) B3085271
theorem B2056889 : Blo 1370504 2056889 := bstep (se 2 (by rfl) ⟨771333, by rfl⟩ : syracuseStep 2056889 = 1542667) B1542667
theorem B2056967 : Blo 1370504 2056967 := bstep (se 1 (by rfl) ⟨1542725, by rfl⟩ : syracuseStep 2056967 = 3085451) B3085451
theorem B4227851 : Blo 1370504 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B10560293 : Blo 1370504 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B2057003 : Blo 1370504 2057003 := bstep (se 1 (by rfl) ⟨1542752, by rfl⟩ : syracuseStep 2057003 = 3085505) B3085505
theorem B2057033 : Blo 1370504 2057033 := bstep (se 2 (by rfl) ⟨771387, by rfl⟩ : syracuseStep 2057033 = 1542775) B1542775
theorem B1852303 : Blo 1370504 1852303 := bstep (se 1 (by rfl) ⟨1389227, by rfl⟩ : syracuseStep 1852303 = 2778455) B2778455
theorem B2057147 : Blo 1370504 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B2057207 : Blo 1370504 2057207 := bstep (se 1 (by rfl) ⟨1542905, by rfl⟩ : syracuseStep 2057207 = 3085811) B3085811
theorem B2057231 : Blo 1370504 2057231 := bstep (se 1 (by rfl) ⟨1542923, by rfl⟩ : syracuseStep 2057231 = 3085847) B3085847
theorem B4940843 : Blo 1370504 4940843 := bstep (se 1 (by rfl) ⟨3705632, by rfl⟩ : syracuseStep 4940843 = 7411265) B7411265
theorem B2057273 : Blo 1370504 2057273 := bstep (se 2 (by rfl) ⟨771477, by rfl⟩ : syracuseStep 2057273 = 1542955) B1542955
theorem B2057351 : Blo 1370504 2057351 := bstep (se 1 (by rfl) ⟨1543013, by rfl⟩ : syracuseStep 2057351 = 3086027) B3086027
theorem B2057387 : Blo 1370504 2057387 := bstep (se 1 (by rfl) ⟨1543040, by rfl⟩ : syracuseStep 2057387 = 3086081) B3086081
theorem B2057417 : Blo 1370504 2057417 := bstep (se 2 (by rfl) ⟨771531, by rfl⟩ : syracuseStep 2057417 = 1543063) B1543063
theorem B2639147 : Blo 1370504 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B2057531 : Blo 1370504 2057531 := bstep (se 1 (by rfl) ⟨1543148, by rfl⟩ : syracuseStep 2057531 = 3086297) B3086297
theorem B2057591 : Blo 1370504 2057591 := bstep (se 1 (by rfl) ⟨1543193, by rfl⟩ : syracuseStep 2057591 = 3086387) B3086387
theorem B2057615 : Blo 1370504 2057615 := bstep (se 1 (by rfl) ⟨1543211, by rfl⟩ : syracuseStep 2057615 = 3086423) B3086423
theorem B7054739 : Blo 1370504 7054739 := bstep (se 1 (by rfl) ⟨5291054, by rfl⟩ : syracuseStep 7054739 = 10582109) B10582109
theorem B2778553 : Blo 1370504 2778553 := bstep (se 2 (by rfl) ⟨1041957, by rfl⟩ : syracuseStep 2778553 = 2083915) B2083915
theorem B2057657 : Blo 1370504 2057657 := bstep (se 2 (by rfl) ⟨771621, by rfl⟩ : syracuseStep 2057657 = 1543243) B1543243
theorem B3294665 : Blo 1370504 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B10413521 : Blo 1370504 10413521 := bstep (se 2 (by rfl) ⟨3905070, by rfl⟩ : syracuseStep 10413521 = 7810141) B7810141
theorem B10429955 : Blo 1370504 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B2057735 : Blo 1370504 2057735 := bstep (se 1 (by rfl) ⟨1543301, by rfl⟩ : syracuseStep 2057735 = 3086603) B3086603
theorem B2057771 : Blo 1370504 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B2057801 : Blo 1370504 2057801 := bstep (se 2 (by rfl) ⟨771675, by rfl⟩ : syracuseStep 2057801 = 1543351) B1543351
theorem B2057915 : Blo 1370504 2057915 := bstep (se 1 (by rfl) ⟨1543436, by rfl⟩ : syracuseStep 2057915 = 3086873) B3086873
theorem B7415525 : Blo 1370504 7415525 := bstep (se 4 (by rfl) ⟨695205, by rfl⟩ : syracuseStep 7415525 = 1390411) B1390411
theorem B2057975 : Blo 1370504 2057975 := bstep (se 1 (by rfl) ⟨1543481, by rfl⟩ : syracuseStep 2057975 = 3086963) B3086963
theorem B2057999 : Blo 1370504 2057999 := bstep (se 1 (by rfl) ⟨1543499, by rfl⟩ : syracuseStep 2057999 = 3086999) B3086999
theorem B23422769 : Blo 1370504 23422769 := bstep (se 2 (by rfl) ⟨8783538, by rfl⟩ : syracuseStep 23422769 = 17567077) B17567077
theorem B1541947 : Blo 1370504 1541947 := bstep (se 1 (by rfl) ⟨1156460, by rfl⟩ : syracuseStep 1541947 = 2312921) B2312921
theorem B9881459 : Blo 1370504 9881459 := bstep (se 1 (by rfl) ⟨7411094, by rfl⟩ : syracuseStep 9881459 = 14822189) B14822189
theorem B5203997 : Blo 1370504 5203997 := bstep (se 3 (by rfl) ⟨975749, by rfl⟩ : syracuseStep 5203997 = 1951499) B1951499
theorem B3516563 : Blo 1370504 3516563 := bstep (se 1 (by rfl) ⟨2637422, by rfl⟩ : syracuseStep 3516563 = 5274845) B5274845
theorem B26364149 : Blo 1370504 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1542415 : Blo 1370504 1542415 := bstep (se 1 (by rfl) ⟨1156811, by rfl⟩ : syracuseStep 1542415 = 2313623) B2313623
theorem B1952057 : Blo 1370504 1952057 := bstep (se 2 (by rfl) ⟨732021, by rfl⟩ : syracuseStep 1952057 = 1464043) B1464043
theorem B23431517 : Blo 1370504 23431517 := bstep (se 3 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 23431517 = 8786819) B8786819
theorem B1370511 : Blo 1370504 1370511 := bstep (se 1 (by rfl) ⟨1027883, by rfl⟩ : syracuseStep 1370511 = 2055767) B2055767
theorem B6678937 : Blo 1370504 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B1370555 : Blo 1370504 1370555 := bstep (se 1 (by rfl) ⟨1027916, by rfl⟩ : syracuseStep 1370555 = 2055833) B2055833
theorem B5859793 : Blo 1370504 5859793 := bstep (se 2 (by rfl) ⟨2197422, by rfl⟩ : syracuseStep 5859793 = 4394845) B4394845
theorem B1370631 : Blo 1370504 1370631 := bstep (se 1 (by rfl) ⟨1027973, by rfl⟩ : syracuseStep 1370631 = 2055947) B2055947
theorem B1370639 : Blo 1370504 1370639 := bstep (se 1 (by rfl) ⟨1027979, by rfl⟩ : syracuseStep 1370639 = 2055959) B2055959
theorem B6941213 : Blo 1370504 6941213 := bstep (se 3 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 6941213 = 2602955) B2602955
theorem B1370683 : Blo 1370504 1370683 := bstep (se 1 (by rfl) ⟨1028012, by rfl⟩ : syracuseStep 1370683 = 2056025) B2056025
theorem B1370759 : Blo 1370504 1370759 := bstep (se 1 (by rfl) ⟨1028069, by rfl⟩ : syracuseStep 1370759 = 2056139) B2056139
theorem B1370767 : Blo 1370504 1370767 := bstep (se 1 (by rfl) ⟨1028075, by rfl⟩ : syracuseStep 1370767 = 2056151) B2056151
theorem B1370811 : Blo 1370504 1370811 := bstep (se 1 (by rfl) ⟨1028108, by rfl⟩ : syracuseStep 1370811 = 2056217) B2056217
theorem B5204681 : Blo 1370504 5204681 := bstep (se 2 (by rfl) ⟨1951755, by rfl⟩ : syracuseStep 5204681 = 3903511) B3903511
theorem B7416521 : Blo 1370504 7416521 := bstep (se 2 (by rfl) ⟨2781195, by rfl⟩ : syracuseStep 7416521 = 5562391) B5562391
theorem B1370887 : Blo 1370504 1370887 := bstep (se 1 (by rfl) ⟨1028165, by rfl⟩ : syracuseStep 1370887 = 2056331) B2056331
theorem B1542919 : Blo 1370504 1542919 := bstep (se 1 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 1542919 = 2314379) B2314379
theorem B2312975 : Blo 1370504 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B1370895 : Blo 1370504 1370895 := bstep (se 1 (by rfl) ⟨1028171, by rfl⟩ : syracuseStep 1370895 = 2056343) B2056343
theorem B2345771 : Blo 1370504 2345771 := bstep (se 1 (by rfl) ⟨1759328, by rfl⟩ : syracuseStep 2345771 = 3518657) B3518657
theorem B1370939 : Blo 1370504 1370939 := bstep (se 1 (by rfl) ⟨1028204, by rfl⟩ : syracuseStep 1370939 = 2056409) B2056409
theorem B1371015 : Blo 1370504 1371015 := bstep (se 1 (by rfl) ⟨1028261, by rfl⟩ : syracuseStep 1371015 = 2056523) B2056523
theorem B1371023 : Blo 1370504 1371023 := bstep (se 1 (by rfl) ⟨1028267, by rfl⟩ : syracuseStep 1371023 = 2056535) B2056535
theorem B1371067 : Blo 1370504 1371067 := bstep (se 1 (by rfl) ⟨1028300, by rfl⟩ : syracuseStep 1371067 = 2056601) B2056601
theorem B1543099 : Blo 1370504 1543099 := bstep (se 1 (by rfl) ⟨1157324, by rfl⟩ : syracuseStep 1543099 = 2314649) B2314649
theorem B6941699 : Blo 1370504 6941699 := bstep (se 1 (by rfl) ⟨5206274, by rfl⟩ : syracuseStep 6941699 = 10412549) B10412549
theorem B1371143 : Blo 1370504 1371143 := bstep (se 1 (by rfl) ⟨1028357, by rfl⟩ : syracuseStep 1371143 = 2056715) B2056715
theorem B1371151 : Blo 1370504 1371151 := bstep (se 1 (by rfl) ⟨1028363, by rfl⟩ : syracuseStep 1371151 = 2056727) B2056727
theorem B2927659 : Blo 1370504 2927659 := bstep (se 1 (by rfl) ⟨2195744, by rfl⟩ : syracuseStep 2927659 = 4391489) B4391489
theorem B1371195 : Blo 1370504 1371195 := bstep (se 1 (by rfl) ⟨1028396, by rfl⟩ : syracuseStep 1371195 = 2056793) B2056793
theorem B1371271 : Blo 1370504 1371271 := bstep (se 1 (by rfl) ⟨1028453, by rfl⟩ : syracuseStep 1371271 = 2056907) B2056907
theorem B1371279 : Blo 1370504 1371279 := bstep (se 1 (by rfl) ⟨1028459, by rfl⟩ : syracuseStep 1371279 = 2056919) B2056919
theorem B1371323 : Blo 1370504 1371323 := bstep (se 1 (by rfl) ⟨1028492, by rfl⟩ : syracuseStep 1371323 = 2056985) B2056985
theorem B8457473 : Blo 1370504 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B1371399 : Blo 1370504 1371399 := bstep (se 1 (by rfl) ⟨1028549, by rfl⟩ : syracuseStep 1371399 = 2057099) B2057099
theorem B1371407 : Blo 1370504 1371407 := bstep (se 1 (by rfl) ⟨1028555, by rfl⟩ : syracuseStep 1371407 = 2057111) B2057111
theorem B2927915 : Blo 1370504 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B2313515 : Blo 1370504 2313515 := bstep (se 1 (by rfl) ⟨1735136, by rfl⟩ : syracuseStep 2313515 = 3470273) B3470273
theorem B1371451 : Blo 1370504 1371451 := bstep (se 1 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 1371451 = 2057177) B2057177
theorem B1371527 : Blo 1370504 1371527 := bstep (se 1 (by rfl) ⟨1028645, by rfl⟩ : syracuseStep 1371527 = 2057291) B2057291
theorem B1371535 : Blo 1370504 1371535 := bstep (se 1 (by rfl) ⟨1028651, by rfl⟩ : syracuseStep 1371535 = 2057303) B2057303
theorem B3083705 : Blo 1370504 3083705 := bstep (se 2 (by rfl) ⟨1156389, by rfl⟩ : syracuseStep 3083705 = 2312779) B2312779
theorem B1371579 : Blo 1370504 1371579 := bstep (se 1 (by rfl) ⟨1028684, by rfl⟩ : syracuseStep 1371579 = 2057369) B2057369
theorem B8785361 : Blo 1370504 8785361 := bstep (se 2 (by rfl) ⟨3294510, by rfl⟩ : syracuseStep 8785361 = 6589021) B6589021
theorem B1371655 : Blo 1370504 1371655 := bstep (se 1 (by rfl) ⟨1028741, by rfl⟩ : syracuseStep 1371655 = 2057483) B2057483
theorem B1371663 : Blo 1370504 1371663 := bstep (se 1 (by rfl) ⟨1028747, by rfl⟩ : syracuseStep 1371663 = 2057495) B2057495
theorem B2346511 : Blo 1370504 2346511 := bstep (se 1 (by rfl) ⟨1759883, by rfl⟩ : syracuseStep 2346511 = 3519767) B3519767
theorem B1371707 : Blo 1370504 1371707 := bstep (se 1 (by rfl) ⟨1028780, by rfl⟩ : syracuseStep 1371707 = 2057561) B2057561
theorem B1371783 : Blo 1370504 1371783 := bstep (se 1 (by rfl) ⟨1028837, by rfl⟩ : syracuseStep 1371783 = 2057675) B2057675
theorem B1371791 : Blo 1370504 1371791 := bstep (se 1 (by rfl) ⟨1028843, by rfl⟩ : syracuseStep 1371791 = 2057687) B2057687
theorem B28528307 : Blo 1370504 28528307 := bstep (se 1 (by rfl) ⟨21396230, by rfl⟩ : syracuseStep 28528307 = 42792461) B42792461
theorem B2313913 : Blo 1370504 2313913 := bstep (se 2 (by rfl) ⟨867717, by rfl⟩ : syracuseStep 2313913 = 1735435) B1735435
theorem B1371835 : Blo 1370504 1371835 := bstep (se 1 (by rfl) ⟨1028876, by rfl⟩ : syracuseStep 1371835 = 2057753) B2057753
theorem B10555109 : Blo 1370504 10555109 := bstep (se 4 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 10555109 = 1979083) B1979083
theorem B1371911 : Blo 1370504 1371911 := bstep (se 1 (by rfl) ⟨1028933, by rfl⟩ : syracuseStep 1371911 = 2057867) B2057867
theorem B3084047 : Blo 1370504 3084047 := bstep (se 1 (by rfl) ⟨2313035, by rfl⟩ : syracuseStep 3084047 = 4626071) B4626071
theorem B1371919 : Blo 1370504 1371919 := bstep (se 1 (by rfl) ⟨1028939, by rfl⟩ : syracuseStep 1371919 = 2057879) B2057879
theorem B3084065 : Blo 1370504 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B5558075 : Blo 1370504 5558075 := bstep (se 1 (by rfl) ⟨4168556, by rfl⟩ : syracuseStep 5558075 = 8337113) B8337113
theorem B1371963 : Blo 1370504 1371963 := bstep (se 1 (by rfl) ⟨1028972, by rfl⟩ : syracuseStep 1371963 = 2057945) B2057945
theorem B3903385 : Blo 1370504 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B4943915 : Blo 1370504 4943915 := bstep (se 1 (by rfl) ⟨3707936, by rfl⟩ : syracuseStep 4943915 = 7415873) B7415873
theorem B2084923 : Blo 1370504 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B3084407 : Blo 1370504 3084407 := bstep (se 1 (by rfl) ⟨2313305, by rfl⟩ : syracuseStep 3084407 = 4626611) B4626611
theorem B3469513 : Blo 1370504 3469513 := bstep (se 2 (by rfl) ⟨1301067, by rfl⟩ : syracuseStep 3469513 = 2602135) B2602135
theorem B4944073 : Blo 1370504 4944073 := bstep (se 2 (by rfl) ⟨1854027, by rfl⟩ : syracuseStep 4944073 = 3708055) B3708055
theorem B3084587 : Blo 1370504 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B3469655 : Blo 1370504 3469655 := bstep (se 1 (by rfl) ⟨2602241, by rfl⟩ : syracuseStep 3469655 = 5204483) B5204483
theorem B7811417 : Blo 1370504 7811417 := bstep (se 2 (by rfl) ⟨2929281, by rfl⟩ : syracuseStep 7811417 = 5858563) B5858563
theorem B2314615 : Blo 1370504 2314615 := bstep (se 1 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 2314615 = 3471923) B3471923
theorem B2929043 : Blo 1370504 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B5206457 : Blo 1370504 5206457 := bstep (se 2 (by rfl) ⟨1952421, by rfl⟩ : syracuseStep 5206457 = 3904843) B3904843
theorem B3904001 : Blo 1370504 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B2314811 : Blo 1370504 2314811 := bstep (se 1 (by rfl) ⟨1736108, by rfl⟩ : syracuseStep 2314811 = 3472217) B3472217
theorem B6943319 : Blo 1370504 6943319 := bstep (se 1 (by rfl) ⟨5207489, by rfl⟩ : syracuseStep 6943319 = 10414979) B10414979
theorem B3084947 : Blo 1370504 3084947 := bstep (se 1 (by rfl) ⟨2313710, by rfl⟩ : syracuseStep 3084947 = 4627421) B4627421
theorem B3125945 : Blo 1370504 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B3085001 : Blo 1370504 3085001 := bstep (se 2 (by rfl) ⟨1156875, by rfl⟩ : syracuseStep 3085001 = 2313751) B2313751
theorem B7811873 : Blo 1370504 7811873 := bstep (se 2 (by rfl) ⟨2929452, by rfl⟩ : syracuseStep 7811873 = 5858905) B5858905
theorem B19280729 : Blo 1370504 19280729 := bstep (se 2 (by rfl) ⟨7230273, by rfl⟩ : syracuseStep 19280729 = 14460547) B14460547
theorem B2929555 : Blo 1370504 2929555 := bstep (se 1 (by rfl) ⟨2197166, by rfl⟩ : syracuseStep 2929555 = 4394333) B4394333
theorem B2315209 : Blo 1370504 2315209 := bstep (se 2 (by rfl) ⟨868203, by rfl⟩ : syracuseStep 2315209 = 1736407) B1736407
theorem B7812125 : Blo 1370504 7812125 := bstep (se 3 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 7812125 = 2929547) B2929547
theorem B6943805 : Blo 1370504 6943805 := bstep (se 3 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 6943805 = 2603927) B2603927
theorem B3708089 : Blo 1370504 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B1389755 : Blo 1370504 1389755 := bstep (se 1 (by rfl) ⟨1042316, by rfl⟩ : syracuseStep 1389755 = 2084633) B2084633
theorem B11113787 : Blo 1370504 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B3085703 : Blo 1370504 3085703 := bstep (se 1 (by rfl) ⟨2314277, by rfl⟩ : syracuseStep 3085703 = 4628555) B4628555
theorem B3904969 : Blo 1370504 3904969 := bstep (se 2 (by rfl) ⟨1464363, by rfl⟩ : syracuseStep 3904969 = 2928727) B2928727
theorem B9885149 : Blo 1370504 9885149 := bstep (se 3 (by rfl) ⟨1853465, by rfl⟩ : syracuseStep 9885149 = 3706931) B3706931
theorem B10556893 : Blo 1370504 10556893 := bstep (se 3 (by rfl) ⟨1979417, by rfl⟩ : syracuseStep 10556893 = 3958835) B3958835
theorem B4625963 : Blo 1370504 4625963 := bstep (se 1 (by rfl) ⟨3469472, by rfl⟩ : syracuseStep 4625963 = 6938945) B6938945
theorem B3085883 : Blo 1370504 3085883 := bstep (se 1 (by rfl) ⟨2314412, by rfl⟩ : syracuseStep 3085883 = 4628825) B4628825
theorem B3086009 : Blo 1370504 3086009 := bstep (se 2 (by rfl) ⟨1157253, by rfl⟩ : syracuseStep 3086009 = 2314507) B2314507
theorem B9885377 : Blo 1370504 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B8452043 : Blo 1370504 8452043 := bstep (se 1 (by rfl) ⟨6339032, by rfl⟩ : syracuseStep 8452043 = 12678065) B12678065
theorem B3086351 : Blo 1370504 3086351 := bstep (se 1 (by rfl) ⟨2314763, by rfl⟩ : syracuseStep 3086351 = 4629527) B4629527
theorem B3086369 : Blo 1370504 3086369 := bstep (se 2 (by rfl) ⟨1157388, by rfl⟩ : syracuseStep 3086369 = 2314777) B2314777
theorem B20043821 : Blo 1370504 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B4757705 : Blo 1370504 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B5347565 : Blo 1370504 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B5855489 : Blo 1370504 5855489 := bstep (se 2 (by rfl) ⟨2195808, by rfl⟩ : syracuseStep 5855489 = 4391617) B4391617
theorem B3471731 : Blo 1370504 3471731 := bstep (se 1 (by rfl) ⟨2603798, by rfl⟩ : syracuseStep 3471731 = 5207597) B5207597
theorem B3086711 : Blo 1370504 3086711 := bstep (se 1 (by rfl) ⟨2315033, by rfl⟩ : syracuseStep 3086711 = 4630067) B4630067
theorem B1669511 : Blo 1370504 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B2603411 : Blo 1370504 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B3086891 : Blo 1370504 3086891 := bstep (se 1 (by rfl) ⟨2315168, by rfl⟩ : syracuseStep 3086891 = 4630337) B4630337
theorem B2603639 : Blo 1370504 2603639 := bstep (se 1 (by rfl) ⟨1952729, by rfl⟩ : syracuseStep 2603639 = 3905459) B3905459
theorem B1735339 : Blo 1370504 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B9378575 : Blo 1370504 9378575 := bstep (se 1 (by rfl) ⟨7033931, by rfl⟩ : syracuseStep 9378575 = 14067863) B14067863
theorem B6945587 : Blo 1370504 6945587 := bstep (se 1 (by rfl) ⟨5209190, by rfl⟩ : syracuseStep 6945587 = 10418381) B10418381
theorem B4627259 : Blo 1370504 4627259 := bstep (se 1 (by rfl) ⟨3470444, by rfl⟩ : syracuseStep 4627259 = 6940889) B6940889
theorem B3472247 : Blo 1370504 3472247 := bstep (se 1 (by rfl) ⟨2604185, by rfl⟩ : syracuseStep 3472247 = 5208371) B5208371
theorem B7912451 : Blo 1370504 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B3906575 : Blo 1370504 3906575 := bstep (se 1 (by rfl) ⟨2929931, by rfl⟩ : syracuseStep 3906575 = 5859863) B5859863
theorem B4627745 : Blo 1370504 4627745 := bstep (se 2 (by rfl) ⟨1735404, by rfl⟩ : syracuseStep 4627745 = 3470809) B3470809
theorem B4169335 : Blo 1370504 4169335 := bstep (se 1 (by rfl) ⟨3127001, by rfl⟩ : syracuseStep 4169335 = 6254003) B6254003
theorem B1736311 : Blo 1370504 1736311 := bstep (se 1 (by rfl) ⟨1302233, by rfl⟩ : syracuseStep 1736311 = 2604467) B2604467
theorem B2055815 : Blo 1370504 2055815 := bstep (se 1 (by rfl) ⟨1541861, by rfl⟩ : syracuseStep 2055815 = 3083723) B3083723
theorem B1564303 : Blo 1370504 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B2055851 : Blo 1370504 2055851 := bstep (se 1 (by rfl) ⟨1541888, by rfl⟩ : syracuseStep 2055851 = 3083777) B3083777
theorem B2055881 : Blo 1370504 2055881 := bstep (se 2 (by rfl) ⟨770955, by rfl⟩ : syracuseStep 2055881 = 1541911) B1541911
theorem B33349427 : Blo 1370504 33349427 := bstep (se 1 (by rfl) ⟨25012070, by rfl⟩ : syracuseStep 33349427 = 50024141) B50024141
theorem B2055995 : Blo 1370504 2055995 := bstep (se 1 (by rfl) ⟨1541996, by rfl⟩ : syracuseStep 2055995 = 3083993) B3083993
theorem B4628339 : Blo 1370504 4628339 := bstep (se 1 (by rfl) ⟨3471254, by rfl⟩ : syracuseStep 4628339 = 6942509) B6942509
theorem B2056055 : Blo 1370504 2056055 := bstep (se 1 (by rfl) ⟨1542041, by rfl⟩ : syracuseStep 2056055 = 3084083) B3084083
theorem B2056079 : Blo 1370504 2056079 := bstep (se 1 (by rfl) ⟨1542059, by rfl⟩ : syracuseStep 2056079 = 3084119) B3084119
theorem B28147607 : Blo 1370504 28147607 := bstep (se 1 (by rfl) ⟨21110705, by rfl⟩ : syracuseStep 28147607 = 42221411) B42221411
theorem B2056121 : Blo 1370504 2056121 := bstep (se 2 (by rfl) ⟨771045, by rfl⟩ : syracuseStep 2056121 = 1542091) B1542091
theorem B2056271 : Blo 1370504 2056271 := bstep (se 1 (by rfl) ⟨1542203, by rfl⟩ : syracuseStep 2056271 = 3084407) B3084407
theorem B2056391 : Blo 1370504 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B2056553 : Blo 1370504 2056553 := bstep (se 2 (by rfl) ⟨771207, by rfl⟩ : syracuseStep 2056553 = 1542415) B1542415
theorem B4628879 : Blo 1370504 4628879 := bstep (se 1 (by rfl) ⟨3471659, by rfl⟩ : syracuseStep 4628879 = 6943319) B6943319
theorem B2056631 : Blo 1370504 2056631 := bstep (se 1 (by rfl) ⟨1542473, by rfl⟩ : syracuseStep 2056631 = 3084947) B3084947
theorem B2056667 : Blo 1370504 2056667 := bstep (se 1 (by rfl) ⟨1542500, by rfl⟩ : syracuseStep 2056667 = 3085001) B3085001
theorem B2818567 : Blo 1370504 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B8905249 : Blo 1370504 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B12853819 : Blo 1370504 12853819 := bstep (se 1 (by rfl) ⟨9640364, by rfl⟩ : syracuseStep 12853819 = 19280729) B19280729
theorem B22553261 : Blo 1370504 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B4629203 : Blo 1370504 4629203 := bstep (se 1 (by rfl) ⟨3471902, by rfl⟩ : syracuseStep 4629203 = 6943805) B6943805
theorem B7037725 : Blo 1370504 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B2057135 : Blo 1370504 2057135 := bstep (se 1 (by rfl) ⟨1542851, by rfl⟩ : syracuseStep 2057135 = 3085703) B3085703
theorem B4703159 : Blo 1370504 4703159 := bstep (se 1 (by rfl) ⟨3527369, by rfl⟩ : syracuseStep 4703159 = 7054739) B7054739
theorem B2196443 : Blo 1370504 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B2057225 : Blo 1370504 2057225 := bstep (se 2 (by rfl) ⟨771459, by rfl⟩ : syracuseStep 2057225 = 1542919) B1542919
theorem B2057255 : Blo 1370504 2057255 := bstep (se 1 (by rfl) ⟨1542941, by rfl⟩ : syracuseStep 2057255 = 3085883) B3085883
theorem B2057339 : Blo 1370504 2057339 := bstep (se 1 (by rfl) ⟨1543004, by rfl⟩ : syracuseStep 2057339 = 3086009) B3086009
theorem B15615179 : Blo 1370504 15615179 := bstep (se 1 (by rfl) ⟨11711384, by rfl⟩ : syracuseStep 15615179 = 23422769) B23422769
theorem B6587639 : Blo 1370504 6587639 := bstep (se 1 (by rfl) ⟨4940729, by rfl⟩ : syracuseStep 6587639 = 9881459) B9881459
theorem B2057465 : Blo 1370504 2057465 := bstep (se 2 (by rfl) ⟨771549, by rfl⟩ : syracuseStep 2057465 = 1543099) B1543099
theorem B2057567 : Blo 1370504 2057567 := bstep (se 1 (by rfl) ⟨1543175, by rfl⟩ : syracuseStep 2057567 = 3086351) B3086351
theorem B2057579 : Blo 1370504 2057579 := bstep (se 1 (by rfl) ⟨1543184, by rfl⟩ : syracuseStep 2057579 = 3086369) B3086369
theorem B2344375 : Blo 1370504 2344375 := bstep (se 1 (by rfl) ⟨1758281, by rfl⟩ : syracuseStep 2344375 = 3516563) B3516563
theorem B3171803 : Blo 1370504 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B3565043 : Blo 1370504 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B2057807 : Blo 1370504 2057807 := bstep (se 1 (by rfl) ⟨1543355, by rfl⟩ : syracuseStep 2057807 = 3086711) B3086711
theorem B2057927 : Blo 1370504 2057927 := bstep (se 1 (by rfl) ⟨1543445, by rfl⟩ : syracuseStep 2057927 = 3086891) B3086891
theorem B1541983 : Blo 1370504 1541983 := bstep (se 1 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 1541983 = 2312975) B2312975
theorem B6252383 : Blo 1370504 6252383 := bstep (se 1 (by rfl) ⟨4689287, by rfl⟩ : syracuseStep 6252383 = 9378575) B9378575
theorem B4630391 : Blo 1370504 4630391 := bstep (se 1 (by rfl) ⟨3472793, by rfl⟩ : syracuseStep 4630391 = 6945587) B6945587
theorem B3704737 : Blo 1370504 3704737 := bstep (se 2 (by rfl) ⟨1389276, by rfl⟩ : syracuseStep 3704737 = 2778553) B2778553
theorem B14075857 : Blo 1370504 14075857 := bstep (se 2 (by rfl) ⟨5278446, by rfl⟩ : syracuseStep 14075857 = 10556893) B10556893
theorem B1951943 : Blo 1370504 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B1542343 : Blo 1370504 1542343 := bstep (se 1 (by rfl) ⟨1156757, by rfl⟩ : syracuseStep 1542343 = 2313515) B2313515
theorem B1370543 : Blo 1370504 1370543 := bstep (se 1 (by rfl) ⟨1027907, by rfl⟩ : syracuseStep 1370543 = 2055815) B2055815
theorem B1370567 : Blo 1370504 1370567 := bstep (se 1 (by rfl) ⟨1027925, by rfl⟩ : syracuseStep 1370567 = 2055851) B2055851
theorem B1370587 : Blo 1370504 1370587 := bstep (se 1 (by rfl) ⟨1027940, by rfl⟩ : syracuseStep 1370587 = 2055881) B2055881
theorem B5204513 : Blo 1370504 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B1370663 : Blo 1370504 1370663 := bstep (se 1 (by rfl) ⟨1027997, by rfl⟩ : syracuseStep 1370663 = 2055995) B2055995
theorem B3705383 : Blo 1370504 3705383 := bstep (se 1 (by rfl) ⟨2779037, by rfl⟩ : syracuseStep 3705383 = 5558075) B5558075
theorem B1370703 : Blo 1370504 1370703 := bstep (se 1 (by rfl) ⟨1028027, by rfl⟩ : syracuseStep 1370703 = 2056055) B2056055
theorem B1370719 : Blo 1370504 1370719 := bstep (se 1 (by rfl) ⟨1028039, by rfl⟩ : syracuseStep 1370719 = 2056079) B2056079
theorem B1370747 : Blo 1370504 1370747 := bstep (se 1 (by rfl) ⟨1028060, by rfl⟩ : syracuseStep 1370747 = 2056121) B2056121
theorem B1370799 : Blo 1370504 1370799 := bstep (se 1 (by rfl) ⟨1028099, by rfl⟩ : syracuseStep 1370799 = 2056199) B2056199
theorem B1370823 : Blo 1370504 1370823 := bstep (se 1 (by rfl) ⟨1028117, by rfl⟩ : syracuseStep 1370823 = 2056235) B2056235
theorem B3295943 : Blo 1370504 3295943 := bstep (se 1 (by rfl) ⟨2471957, by rfl⟩ : syracuseStep 3295943 = 4943915) B4943915
theorem B5204695 : Blo 1370504 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B1370843 : Blo 1370504 1370843 := bstep (se 1 (by rfl) ⟨1028132, by rfl⟩ : syracuseStep 1370843 = 2056265) B2056265
theorem B13175581 : Blo 1370504 13175581 := bstep (se 3 (by rfl) ⟨2470421, by rfl⟩ : syracuseStep 13175581 = 4940843) B4940843
theorem B7514909 : Blo 1370504 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B1370919 : Blo 1370504 1370919 := bstep (se 1 (by rfl) ⟨1028189, by rfl⟩ : syracuseStep 1370919 = 2056379) B2056379
theorem B1370959 : Blo 1370504 1370959 := bstep (se 1 (by rfl) ⟨1028219, by rfl⟩ : syracuseStep 1370959 = 2056439) B2056439
theorem B1370975 : Blo 1370504 1370975 := bstep (se 1 (by rfl) ⟨1028231, by rfl⟩ : syracuseStep 1370975 = 2056463) B2056463
theorem B1371003 : Blo 1370504 1371003 := bstep (se 1 (by rfl) ⟨1028252, by rfl⟩ : syracuseStep 1371003 = 2056505) B2056505
theorem B2313103 : Blo 1370504 2313103 := bstep (se 1 (by rfl) ⟨1734827, by rfl⟩ : syracuseStep 2313103 = 3469655) B3469655
theorem B1371055 : Blo 1370504 1371055 := bstep (se 1 (by rfl) ⟨1028291, by rfl⟩ : syracuseStep 1371055 = 2056583) B2056583
theorem B1952695 : Blo 1370504 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B1371079 : Blo 1370504 1371079 := bstep (se 1 (by rfl) ⟨1028309, by rfl⟩ : syracuseStep 1371079 = 2056619) B2056619
theorem B1371099 : Blo 1370504 1371099 := bstep (se 1 (by rfl) ⟨1028324, by rfl⟩ : syracuseStep 1371099 = 2056649) B2056649
theorem B11119589 : Blo 1370504 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B5204999 : Blo 1370504 5204999 := bstep (se 1 (by rfl) ⟨3903749, by rfl⟩ : syracuseStep 5204999 = 7807499) B7807499
theorem B5008391 : Blo 1370504 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B1371175 : Blo 1370504 1371175 := bstep (se 1 (by rfl) ⟨1028381, by rfl⟩ : syracuseStep 1371175 = 2056763) B2056763
theorem B1543207 : Blo 1370504 1543207 := bstep (se 1 (by rfl) ⟨1157405, by rfl⟩ : syracuseStep 1543207 = 2314811) B2314811
theorem B1371215 : Blo 1370504 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B1371231 : Blo 1370504 1371231 := bstep (se 1 (by rfl) ⟨1028423, by rfl⟩ : syracuseStep 1371231 = 2056847) B2056847
theorem B2083963 : Blo 1370504 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B1371259 : Blo 1370504 1371259 := bstep (se 1 (by rfl) ⟨1028444, by rfl⟩ : syracuseStep 1371259 = 2056889) B2056889
theorem B3706013 : Blo 1370504 3706013 := bstep (se 3 (by rfl) ⟨694877, by rfl⟩ : syracuseStep 3706013 = 1389755) B1389755
theorem B1371311 : Blo 1370504 1371311 := bstep (se 1 (by rfl) ⟨1028483, by rfl⟩ : syracuseStep 1371311 = 2056967) B2056967
theorem B7040195 : Blo 1370504 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B1371335 : Blo 1370504 1371335 := bstep (se 1 (by rfl) ⟨1028501, by rfl⟩ : syracuseStep 1371335 = 2057003) B2057003
theorem B1371355 : Blo 1370504 1371355 := bstep (se 1 (by rfl) ⟨1028516, by rfl⟩ : syracuseStep 1371355 = 2057033) B2057033
theorem B1371431 : Blo 1370504 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B1371471 : Blo 1370504 1371471 := bstep (se 1 (by rfl) ⟨1028603, by rfl⟩ : syracuseStep 1371471 = 2057207) B2057207
theorem B1371487 : Blo 1370504 1371487 := bstep (se 1 (by rfl) ⟨1028615, by rfl⟩ : syracuseStep 1371487 = 2057231) B2057231
theorem B1371515 : Blo 1370504 1371515 := bstep (se 1 (by rfl) ⟨1028636, by rfl⟩ : syracuseStep 1371515 = 2057273) B2057273
theorem B1371567 : Blo 1370504 1371567 := bstep (se 1 (by rfl) ⟨1028675, by rfl⟩ : syracuseStep 1371567 = 2057351) B2057351
theorem B1371591 : Blo 1370504 1371591 := bstep (se 1 (by rfl) ⟨1028693, by rfl⟩ : syracuseStep 1371591 = 2057387) B2057387
theorem B1371611 : Blo 1370504 1371611 := bstep (se 1 (by rfl) ⟨1028708, by rfl⟩ : syracuseStep 1371611 = 2057417) B2057417
theorem B5205485 : Blo 1370504 5205485 := bstep (se 3 (by rfl) ⟨976028, by rfl⟩ : syracuseStep 5205485 = 1952057) B1952057
theorem B7409191 : Blo 1370504 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B1371687 : Blo 1370504 1371687 := bstep (se 1 (by rfl) ⟨1028765, by rfl⟩ : syracuseStep 1371687 = 2057531) B2057531
theorem B2313785 : Blo 1370504 2313785 := bstep (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) B1735339
theorem B1371727 : Blo 1370504 1371727 := bstep (se 1 (by rfl) ⟨1028795, by rfl⟩ : syracuseStep 1371727 = 2057591) B2057591
theorem B1371743 : Blo 1370504 1371743 := bstep (se 1 (by rfl) ⟨1028807, by rfl⟩ : syracuseStep 1371743 = 2057615) B2057615
theorem B1371771 : Blo 1370504 1371771 := bstep (se 1 (by rfl) ⟨1028828, by rfl⟩ : syracuseStep 1371771 = 2057657) B2057657
theorem B6942347 : Blo 1370504 6942347 := bstep (se 1 (by rfl) ⟨5206760, by rfl⟩ : syracuseStep 6942347 = 10413521) B10413521
theorem B6590099 : Blo 1370504 6590099 := bstep (se 1 (by rfl) ⟨4942574, by rfl⟩ : syracuseStep 6590099 = 9885149) B9885149
theorem B1371823 : Blo 1370504 1371823 := bstep (se 1 (by rfl) ⟨1028867, by rfl⟩ : syracuseStep 1371823 = 2057735) B2057735
theorem B4452029 : Blo 1370504 4452029 := bstep (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) B1669511
theorem B3083975 : Blo 1370504 3083975 := bstep (se 1 (by rfl) ⟨2312981, by rfl⟩ : syracuseStep 3083975 = 4625963) B4625963
theorem B1371847 : Blo 1370504 1371847 := bstep (se 1 (by rfl) ⟨1028885, by rfl⟩ : syracuseStep 1371847 = 2057771) B2057771
theorem B1371867 : Blo 1370504 1371867 := bstep (se 1 (by rfl) ⟨1028900, by rfl⟩ : syracuseStep 1371867 = 2057801) B2057801
theorem B1371943 : Blo 1370504 1371943 := bstep (se 1 (by rfl) ⟨1028957, by rfl⟩ : syracuseStep 1371943 = 2057915) B2057915
theorem B6590251 : Blo 1370504 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B4943683 : Blo 1370504 4943683 := bstep (se 1 (by rfl) ⟨3707762, by rfl⟩ : syracuseStep 4943683 = 7415525) B7415525
theorem B1371983 : Blo 1370504 1371983 := bstep (se 1 (by rfl) ⟨1028987, by rfl⟩ : syracuseStep 1371983 = 2057975) B2057975
theorem B1371999 : Blo 1370504 1371999 := bstep (se 1 (by rfl) ⟨1028999, by rfl⟩ : syracuseStep 1371999 = 2057999) B2057999
theorem B2469737 : Blo 1370504 2469737 := bstep (se 2 (by rfl) ⟨926151, by rfl⟩ : syracuseStep 2469737 = 1852303) B1852303
theorem B3469331 : Blo 1370504 3469331 := bstep (se 1 (by rfl) ⟨2601998, by rfl⟩ : syracuseStep 3469331 = 5203997) B5203997
theorem B3903545 : Blo 1370504 3903545 := bstep (se 2 (by rfl) ⟨1463829, by rfl⟩ : syracuseStep 3903545 = 2927659) B2927659
theorem B17576099 : Blo 1370504 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B3903659 : Blo 1370504 3903659 := bstep (se 1 (by rfl) ⟨2927744, by rfl⟩ : syracuseStep 3903659 = 5855489) B5855489
theorem B2314487 : Blo 1370504 2314487 := bstep (se 1 (by rfl) ⟨1735865, by rfl⟩ : syracuseStep 2314487 = 3471731) B3471731
theorem B3469787 : Blo 1370504 3469787 := bstep (se 1 (by rfl) ⟨2602340, by rfl⟩ : syracuseStep 3469787 = 5204681) B5204681
theorem B4944347 : Blo 1370504 4944347 := bstep (se 1 (by rfl) ⟨3708260, by rfl⟩ : syracuseStep 4944347 = 7416521) B7416521
theorem B3084839 : Blo 1370504 3084839 := bstep (se 1 (by rfl) ⟨2313629, by rfl⟩ : syracuseStep 3084839 = 4627259) B4627259
theorem B2314831 : Blo 1370504 2314831 := bstep (se 1 (by rfl) ⟨1736123, by rfl⟩ : syracuseStep 2314831 = 3472247) B3472247
theorem B5206625 : Blo 1370504 5206625 := bstep (se 2 (by rfl) ⟨1952484, by rfl⟩ : syracuseStep 5206625 = 3904969) B3904969
theorem B6255389 : Blo 1370504 6255389 := bstep (se 3 (by rfl) ⟨1172885, by rfl⟩ : syracuseStep 6255389 = 2345771) B2345771
theorem B5559113 : Blo 1370504 5559113 := bstep (se 2 (by rfl) ⟨2084667, by rfl⟩ : syracuseStep 5559113 = 4169335) B4169335
theorem B2315081 : Blo 1370504 2315081 := bstep (se 2 (by rfl) ⟨868155, by rfl⟩ : syracuseStep 2315081 = 1736311) B1736311
theorem B3085163 : Blo 1370504 3085163 := bstep (se 1 (by rfl) ⟨2313872, by rfl⟩ : syracuseStep 3085163 = 4627745) B4627745
theorem B3085217 : Blo 1370504 3085217 := bstep (se 2 (by rfl) ⟨1156956, by rfl⟩ : syracuseStep 3085217 = 2313913) B2313913
theorem B19018871 : Blo 1370504 19018871 := bstep (se 1 (by rfl) ⟨14264153, by rfl⟩ : syracuseStep 19018871 = 28528307) B28528307
theorem B3085559 : Blo 1370504 3085559 := bstep (se 1 (by rfl) ⟨2314169, by rfl⟩ : syracuseStep 3085559 = 4628339) B4628339
theorem B18765071 : Blo 1370504 18765071 := bstep (se 1 (by rfl) ⟨14073803, by rfl⟩ : syracuseStep 18765071 = 28147607) B28147607
theorem B21099869 : Blo 1370504 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B53450189 : Blo 1370504 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B5936627 : Blo 1370504 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B5207611 : Blo 1370504 5207611 := bstep (se 1 (by rfl) ⟨3905708, by rfl⟩ : syracuseStep 5207611 = 7811417) B7811417
theorem B4626017 : Blo 1370504 4626017 := bstep (se 2 (by rfl) ⟨1734756, by rfl⟩ : syracuseStep 4626017 = 3469513) B3469513
theorem B6592097 : Blo 1370504 6592097 := bstep (se 2 (by rfl) ⟨2472036, by rfl⟩ : syracuseStep 6592097 = 4944073) B4944073
theorem B3470971 : Blo 1370504 3470971 := bstep (se 1 (by rfl) ⟨2603228, by rfl⟩ : syracuseStep 3470971 = 5206457) B5206457
theorem B2602667 : Blo 1370504 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B3086153 : Blo 1370504 3086153 := bstep (se 2 (by rfl) ⟨1157307, by rfl⟩ : syracuseStep 3086153 = 2314615) B2314615
theorem B5207915 : Blo 1370504 5207915 := bstep (se 1 (by rfl) ⟨3905936, by rfl⟩ : syracuseStep 5207915 = 7811873) B7811873
theorem B7813057 : Blo 1370504 7813057 := bstep (se 2 (by rfl) ⟨2929896, by rfl⟩ : syracuseStep 7813057 = 5859793) B5859793
theorem B14833601 : Blo 1370504 14833601 := bstep (se 2 (by rfl) ⟨5562600, by rfl⟩ : syracuseStep 14833601 = 11125201) B11125201
theorem B5208083 : Blo 1370504 5208083 := bstep (se 1 (by rfl) ⟨3906062, by rfl⟩ : syracuseStep 5208083 = 7812125) B7812125
theorem B2472059 : Blo 1370504 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B6953303 : Blo 1370504 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B3906073 : Blo 1370504 3906073 := bstep (se 2 (by rfl) ⟨1464777, by rfl⟩ : syracuseStep 3906073 = 2929555) B2929555
theorem B133487189 : Blo 1370504 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B3086945 : Blo 1370504 3086945 := bstep (se 2 (by rfl) ⟨1157604, by rfl⟩ : syracuseStep 3086945 = 2315209) B2315209
theorem B5634695 : Blo 1370504 5634695 := bstep (se 1 (by rfl) ⟨4226021, by rfl⟩ : syracuseStep 5634695 = 8452043) B8452043
theorem B15621011 : Blo 1370504 15621011 := bstep (se 1 (by rfl) ⟨11715758, by rfl⟩ : syracuseStep 15621011 = 23431517) B23431517
theorem B1735607 : Blo 1370504 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B4627475 : Blo 1370504 4627475 := bstep (se 1 (by rfl) ⟨3470606, by rfl⟩ : syracuseStep 4627475 = 6941213) B6941213
theorem B1735759 : Blo 1370504 1735759 := bstep (se 1 (by rfl) ⟨1301819, by rfl⟩ : syracuseStep 1735759 = 2603639) B2603639
theorem B4627799 : Blo 1370504 4627799 := bstep (se 1 (by rfl) ⟨3470849, by rfl⟩ : syracuseStep 4627799 = 6941699) B6941699
theorem B2604383 : Blo 1370504 2604383 := bstep (se 1 (by rfl) ⟨1953287, by rfl⟩ : syracuseStep 2604383 = 3906575) B3906575
theorem B3128681 : Blo 1370504 3128681 := bstep (se 2 (by rfl) ⟨1173255, by rfl⟩ : syracuseStep 3128681 = 2346511) B2346511
theorem B2055803 : Blo 1370504 2055803 := bstep (se 1 (by rfl) ⟨1541852, by rfl⟩ : syracuseStep 2055803 = 3083705) B3083705
theorem B5856907 : Blo 1370504 5856907 := bstep (se 1 (by rfl) ⟨4392680, by rfl⟩ : syracuseStep 5856907 = 8785361) B8785361
theorem B2055929 : Blo 1370504 2055929 := bstep (se 2 (by rfl) ⟨770973, by rfl⟩ : syracuseStep 2055929 = 1541947) B1541947
theorem B7036739 : Blo 1370504 7036739 := bstep (se 1 (by rfl) ⟨5277554, by rfl⟩ : syracuseStep 7036739 = 10555109) B10555109
theorem B2056031 : Blo 1370504 2056031 := bstep (se 1 (by rfl) ⟨1542023, by rfl⟩ : syracuseStep 2056031 = 3084047) B3084047
theorem B2056043 : Blo 1370504 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B22232951 : Blo 1370504 22232951 := bstep (se 1 (by rfl) ⟨16674713, by rfl⟩ : syracuseStep 22232951 = 33349427) B33349427
theorem B2056457 : Blo 1370504 2056457 := bstep (se 2 (by rfl) ⟨771171, by rfl⟩ : syracuseStep 2056457 = 1542343) B1542343
theorem B2056559 : Blo 1370504 2056559 := bstep (se 1 (by rfl) ⟨1542419, by rfl⟩ : syracuseStep 2056559 = 3084839) B3084839
theorem B4170259 : Blo 1370504 4170259 := bstep (se 1 (by rfl) ⟨3127694, by rfl⟩ : syracuseStep 4170259 = 6255389) B6255389
theorem B2056775 : Blo 1370504 2056775 := bstep (se 1 (by rfl) ⟨1542581, by rfl⟩ : syracuseStep 2056775 = 3085163) B3085163
theorem B2056811 : Blo 1370504 2056811 := bstep (se 1 (by rfl) ⟨1542608, by rfl⟩ : syracuseStep 2056811 = 3085217) B3085217
theorem B17138425 : Blo 1370504 17138425 := bstep (se 2 (by rfl) ⟨6426909, by rfl⟩ : syracuseStep 17138425 = 12853819) B12853819
theorem B4391759 : Blo 1370504 4391759 := bstep (se 1 (by rfl) ⟨3293819, by rfl⟩ : syracuseStep 4391759 = 6587639) B6587639
theorem B2057039 : Blo 1370504 2057039 := bstep (se 1 (by rfl) ⟨1542779, by rfl⟩ : syracuseStep 2057039 = 3085559) B3085559
theorem B12510047 : Blo 1370504 12510047 := bstep (se 1 (by rfl) ⟨9382535, by rfl⟩ : syracuseStep 12510047 = 18765071) B18765071
theorem B14066579 : Blo 1370504 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B6939593 : Blo 1370504 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B2376695 : Blo 1370504 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B3957751 : Blo 1370504 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B2057435 : Blo 1370504 2057435 := bstep (se 1 (by rfl) ⟨1543076, by rfl⟩ : syracuseStep 2057435 = 3086153) B3086153
theorem B9889067 : Blo 1370504 9889067 := bstep (se 1 (by rfl) ⟨7416800, by rfl⟩ : syracuseStep 9889067 = 14833601) B14833601
theorem B2057609 : Blo 1370504 2057609 := bstep (se 2 (by rfl) ⟨771603, by rfl⟩ : syracuseStep 2057609 = 1543207) B1543207
theorem B1648039 : Blo 1370504 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B9881021 : Blo 1370504 9881021 := bstep (se 3 (by rfl) ⟨1852691, by rfl⟩ : syracuseStep 9881021 = 3705383) B3705383
theorem B2778617 : Blo 1370504 2778617 := bstep (se 2 (by rfl) ⟨1041981, by rfl⟩ : syracuseStep 2778617 = 2083963) B2083963
theorem B88991459 : Blo 1370504 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B2057963 : Blo 1370504 2057963 := bstep (se 1 (by rfl) ⟨1543472, by rfl⟩ : syracuseStep 2057963 = 3086945) B3086945
theorem B2197295 : Blo 1370504 2197295 := bstep (se 1 (by rfl) ⟨1647971, by rfl⟩ : syracuseStep 2197295 = 3295943) B3295943
theorem B10414007 : Blo 1370504 10414007 := bstep (se 1 (by rfl) ⟨7810505, by rfl⟩ : syracuseStep 10414007 = 15621011) B15621011
theorem B7809209 : Blo 1370504 7809209 := bstep (se 2 (by rfl) ⟨2928453, by rfl⟩ : syracuseStep 7809209 = 5856907) B5856907
theorem B1542523 : Blo 1370504 1542523 := bstep (se 1 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 1542523 = 2313785) B2313785
theorem B1370535 : Blo 1370504 1370535 := bstep (se 1 (by rfl) ⟨1027901, by rfl⟩ : syracuseStep 1370535 = 2055803) B2055803
theorem B4393399 : Blo 1370504 4393399 := bstep (se 1 (by rfl) ⟨3295049, by rfl⟩ : syracuseStep 4393399 = 6590099) B6590099
theorem B2968019 : Blo 1370504 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B1370619 : Blo 1370504 1370619 := bstep (se 1 (by rfl) ⟨1027964, by rfl⟩ : syracuseStep 1370619 = 2055929) B2055929
theorem B1370687 : Blo 1370504 1370687 := bstep (se 1 (by rfl) ⟨1028015, by rfl⟩ : syracuseStep 1370687 = 2056031) B2056031
theorem B1370695 : Blo 1370504 1370695 := bstep (se 1 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 1370695 = 2056043) B2056043
theorem B14821967 : Blo 1370504 14821967 := bstep (se 1 (by rfl) ⟨11116475, by rfl⟩ : syracuseStep 14821967 = 22232951) B22232951
theorem B2312887 : Blo 1370504 2312887 := bstep (se 1 (by rfl) ⟨1734665, by rfl⟩ : syracuseStep 2312887 = 3469331) B3469331
theorem B1370847 : Blo 1370504 1370847 := bstep (se 1 (by rfl) ⟨1028135, by rfl⟩ : syracuseStep 1370847 = 2056271) B2056271
theorem B11717399 : Blo 1370504 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1370927 : Blo 1370504 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B1542991 : Blo 1370504 1542991 := bstep (se 1 (by rfl) ⟨1157243, by rfl⟩ : syracuseStep 1542991 = 2314487) B2314487
theorem B1371035 : Blo 1370504 1371035 := bstep (se 1 (by rfl) ⟨1028276, by rfl⟩ : syracuseStep 1371035 = 2056553) B2056553
theorem B1371087 : Blo 1370504 1371087 := bstep (se 1 (by rfl) ⟨1028315, by rfl⟩ : syracuseStep 1371087 = 2056631) B2056631
theorem B2313191 : Blo 1370504 2313191 := bstep (se 1 (by rfl) ⟨1734893, by rfl⟩ : syracuseStep 2313191 = 3469787) B3469787
theorem B1371111 : Blo 1370504 1371111 := bstep (se 1 (by rfl) ⟨1028333, by rfl⟩ : syracuseStep 1371111 = 2056667) B2056667
theorem B3296231 : Blo 1370504 3296231 := bstep (se 1 (by rfl) ⟨2472173, by rfl⟩ : syracuseStep 3296231 = 4944347) B4944347
theorem B15035507 : Blo 1370504 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B5205181 : Blo 1370504 5205181 := bstep (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) B1951943
theorem B3706075 : Blo 1370504 3706075 := bstep (se 1 (by rfl) ⟨2779556, by rfl⟩ : syracuseStep 3706075 = 5559113) B5559113
theorem B1543387 : Blo 1370504 1543387 := bstep (se 1 (by rfl) ⟨1157540, by rfl⟩ : syracuseStep 1543387 = 2315081) B2315081
theorem B1371423 : Blo 1370504 1371423 := bstep (se 1 (by rfl) ⟨1028567, by rfl⟩ : syracuseStep 1371423 = 2057135) B2057135
theorem B1371483 : Blo 1370504 1371483 := bstep (se 1 (by rfl) ⟨1028612, by rfl⟩ : syracuseStep 1371483 = 2057225) B2057225
theorem B1371503 : Blo 1370504 1371503 := bstep (se 1 (by rfl) ⟨1028627, by rfl⟩ : syracuseStep 1371503 = 2057255) B2057255
theorem B11873665 : Blo 1370504 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B1371559 : Blo 1370504 1371559 := bstep (se 1 (by rfl) ⟨1028669, by rfl⟩ : syracuseStep 1371559 = 2057339) B2057339
theorem B1371643 : Blo 1370504 1371643 := bstep (se 1 (by rfl) ⟨1028732, by rfl⟩ : syracuseStep 1371643 = 2057465) B2057465
theorem B1371711 : Blo 1370504 1371711 := bstep (se 1 (by rfl) ⟨1028783, by rfl⟩ : syracuseStep 1371711 = 2057567) B2057567
theorem B1371719 : Blo 1370504 1371719 := bstep (se 1 (by rfl) ⟨1028789, by rfl⟩ : syracuseStep 1371719 = 2057579) B2057579
theorem B17567441 : Blo 1370504 17567441 := bstep (se 2 (by rfl) ⟨6587790, by rfl⟩ : syracuseStep 17567441 = 13175581) B13175581
theorem B9383633 : Blo 1370504 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1371871 : Blo 1370504 1371871 := bstep (se 1 (by rfl) ⟨1028903, by rfl⟩ : syracuseStep 1371871 = 2057807) B2057807
theorem B3084011 : Blo 1370504 3084011 := bstep (se 1 (by rfl) ⟨2313008, by rfl⟩ : syracuseStep 3084011 = 4626017) B4626017
theorem B4394731 : Blo 1370504 4394731 := bstep (se 1 (by rfl) ⟨3296048, by rfl⟩ : syracuseStep 4394731 = 6592097) B6592097
theorem B1371951 : Blo 1370504 1371951 := bstep (se 1 (by rfl) ⟨1028963, by rfl⟩ : syracuseStep 1371951 = 2057927) B2057927
theorem B3084137 : Blo 1370504 3084137 := bstep (se 2 (by rfl) ⟨1156551, by rfl⟩ : syracuseStep 3084137 = 2313103) B2313103
theorem B8458141 : Blo 1370504 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B2314345 : Blo 1370504 2314345 := bstep (se 2 (by rfl) ⟨867879, by rfl⟩ : syracuseStep 2314345 = 1735759) B1735759
theorem B3469675 : Blo 1370504 3469675 := bstep (se 1 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 3469675 = 5204513) B5204513
theorem B3756463 : Blo 1370504 3756463 := bstep (se 1 (by rfl) ⟨2817347, by rfl⟩ : syracuseStep 3756463 = 5634695) B5634695
theorem B5009939 : Blo 1370504 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B3125833 : Blo 1370504 3125833 := bstep (se 2 (by rfl) ⟨1172187, by rfl⟩ : syracuseStep 3125833 = 2344375) B2344375
theorem B3469999 : Blo 1370504 3469999 := bstep (se 1 (by rfl) ⟨2602499, by rfl⟩ : syracuseStep 3469999 = 5204999) B5204999
theorem B3338927 : Blo 1370504 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B3084983 : Blo 1370504 3084983 := bstep (se 1 (by rfl) ⟨2313737, by rfl⟩ : syracuseStep 3084983 = 4627475) B4627475
theorem B6943481 : Blo 1370504 6943481 := bstep (se 2 (by rfl) ⟨2603805, by rfl⟩ : syracuseStep 6943481 = 5207611) B5207611
theorem B2470675 : Blo 1370504 2470675 := bstep (se 1 (by rfl) ⟨1853006, by rfl⟩ : syracuseStep 2470675 = 3706013) B3706013
theorem B3085199 : Blo 1370504 3085199 := bstep (se 1 (by rfl) ⟨2313899, by rfl⟩ : syracuseStep 3085199 = 4627799) B4627799
theorem B2085787 : Blo 1370504 2085787 := bstep (se 1 (by rfl) ⟨1564340, by rfl⟩ : syracuseStep 2085787 = 3128681) B3128681
theorem B3470323 : Blo 1370504 3470323 := bstep (se 1 (by rfl) ⟨2602742, by rfl⟩ : syracuseStep 3470323 = 5205485) B5205485
theorem B8787001 : Blo 1370504 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B6591577 : Blo 1370504 6591577 := bstep (se 2 (by rfl) ⟨2471841, by rfl⟩ : syracuseStep 6591577 = 4943683) B4943683
theorem B4691159 : Blo 1370504 4691159 := bstep (se 1 (by rfl) ⟨3518369, by rfl⟩ : syracuseStep 4691159 = 7036739) B7036739
theorem B10417409 : Blo 1370504 10417409 := bstep (se 2 (by rfl) ⟨3906528, by rfl⟩ : syracuseStep 10417409 = 7813057) B7813057
theorem B2602363 : Blo 1370504 2602363 := bstep (se 1 (by rfl) ⟨1951772, by rfl⟩ : syracuseStep 2602363 = 3903545) B3903545
theorem B2602439 : Blo 1370504 2602439 := bstep (se 1 (by rfl) ⟨1951829, by rfl⟩ : syracuseStep 2602439 = 3903659) B3903659
theorem B3085919 : Blo 1370504 3085919 := bstep (se 1 (by rfl) ⟨2314439, by rfl⟩ : syracuseStep 3085919 = 4628879) B4628879
theorem B3471083 : Blo 1370504 3471083 := bstep (se 1 (by rfl) ⟨2603312, by rfl⟩ : syracuseStep 3471083 = 5206625) B5206625
theorem B3086135 : Blo 1370504 3086135 := bstep (se 1 (by rfl) ⟨2314601, by rfl⟩ : syracuseStep 3086135 = 4629203) B4629203
theorem B3135439 : Blo 1370504 3135439 := bstep (se 1 (by rfl) ⟨2351579, by rfl⟩ : syracuseStep 3135439 = 4703159) B4703159
theorem B3758089 : Blo 1370504 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B5208097 : Blo 1370504 5208097 := bstep (se 2 (by rfl) ⟨1953036, by rfl⟩ : syracuseStep 5208097 = 3906073) B3906073
theorem B12679247 : Blo 1370504 12679247 := bstep (se 1 (by rfl) ⟨9509435, by rfl⟩ : syracuseStep 12679247 = 19018871) B19018871
theorem B3086441 : Blo 1370504 3086441 := bstep (se 2 (by rfl) ⟨1157415, by rfl⟩ : syracuseStep 3086441 = 2314831) B2314831
theorem B10410119 : Blo 1370504 10410119 := bstep (se 1 (by rfl) ⟨7807589, by rfl⟩ : syracuseStep 10410119 = 15615179) B15615179
theorem B35633459 : Blo 1370504 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B1735111 : Blo 1370504 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B4168255 : Blo 1370504 4168255 := bstep (se 1 (by rfl) ⟨3126191, by rfl⟩ : syracuseStep 4168255 = 6252383) B6252383
theorem B3471943 : Blo 1370504 3471943 := bstep (se 1 (by rfl) ⟨2603957, by rfl⟩ : syracuseStep 3471943 = 5207915) B5207915
theorem B2603593 : Blo 1370504 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B3086927 : Blo 1370504 3086927 := bstep (se 1 (by rfl) ⟨2315195, by rfl⟩ : syracuseStep 3086927 = 4630391) B4630391
theorem B3472055 : Blo 1370504 3472055 := bstep (se 1 (by rfl) ⟨2604041, by rfl⟩ : syracuseStep 3472055 = 5208083) B5208083
theorem B4635535 : Blo 1370504 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B7413059 : Blo 1370504 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B9878921 : Blo 1370504 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B4693463 : Blo 1370504 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B4627961 : Blo 1370504 4627961 := bstep (se 2 (by rfl) ⟨1735485, by rfl⟩ : syracuseStep 4627961 = 3470971) B3470971
theorem B1736255 : Blo 1370504 1736255 := bstep (se 1 (by rfl) ⟨1302191, by rfl⟩ : syracuseStep 1736255 = 2604383) B2604383
theorem B4628231 : Blo 1370504 4628231 := bstep (se 1 (by rfl) ⟨3471173, by rfl⟩ : syracuseStep 4628231 = 6942347) B6942347
theorem B2055977 : Blo 1370504 2055977 := bstep (se 2 (by rfl) ⟨770991, by rfl⟩ : syracuseStep 2055977 = 1541983) B1541983
theorem B2055983 : Blo 1370504 2055983 := bstep (se 1 (by rfl) ⟨1541987, by rfl⟩ : syracuseStep 2055983 = 3083975) B3083975
theorem B4628285 : Blo 1370504 4628285 := bstep (se 3 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 4628285 = 1735607) B1735607
theorem B4939649 : Blo 1370504 4939649 := bstep (se 2 (by rfl) ⟨1852368, by rfl⟩ : syracuseStep 4939649 = 3704737) B3704737
theorem B1646491 : Blo 1370504 1646491 := bstep (se 1 (by rfl) ⟨1234868, by rfl⟩ : syracuseStep 1646491 = 2469737) B2469737
theorem B5857181 : Blo 1370504 5857181 := bstep (se 3 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 5857181 = 2196443) B2196443
theorem B18767809 : Blo 1370504 18767809 := bstep (se 2 (by rfl) ⟨7037928, by rfl⟩ : syracuseStep 18767809 = 14075857) B14075857
theorem B16671109 : Blo 1370504 16671109 := bstep (se 4 (by rfl) ⟨1562916, by rfl⟩ : syracuseStep 16671109 = 3125833) B3125833
theorem B2056655 : Blo 1370504 2056655 := bstep (se 1 (by rfl) ⟨1542491, by rfl⟩ : syracuseStep 2056655 = 3084983) B3084983
theorem B2056697 : Blo 1370504 2056697 := bstep (se 2 (by rfl) ⟨771261, by rfl⟩ : syracuseStep 2056697 = 1542523) B1542523
theorem B4628987 : Blo 1370504 4628987 := bstep (se 1 (by rfl) ⟨3471740, by rfl⟩ : syracuseStep 4628987 = 6943481) B6943481
theorem B8340031 : Blo 1370504 8340031 := bstep (se 1 (by rfl) ⟨6255023, by rfl⟩ : syracuseStep 8340031 = 12510047) B12510047
theorem B5857865 : Blo 1370504 5857865 := bstep (se 2 (by rfl) ⟨2196699, by rfl⟩ : syracuseStep 5857865 = 4393399) B4393399
theorem B2056799 : Blo 1370504 2056799 := bstep (se 1 (by rfl) ⟨1542599, by rfl⟩ : syracuseStep 2056799 = 3085199) B3085199
theorem B4629257 : Blo 1370504 4629257 := bstep (se 2 (by rfl) ⟨1735971, by rfl⟩ : syracuseStep 4629257 = 3471943) B3471943
theorem B26370845 : Blo 1370504 26370845 := bstep (se 3 (by rfl) ⟨4944533, by rfl⟩ : syracuseStep 26370845 = 9889067) B9889067
theorem B19768157 : Blo 1370504 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B6587347 : Blo 1370504 6587347 := bstep (se 1 (by rfl) ⟨4940510, by rfl⟩ : syracuseStep 6587347 = 9881021) B9881021
theorem B1852411 : Blo 1370504 1852411 := bstep (se 1 (by rfl) ⟨1389308, by rfl⟩ : syracuseStep 1852411 = 2778617) B2778617
theorem B3294233 : Blo 1370504 3294233 := bstep (se 2 (by rfl) ⟨1235337, by rfl⟩ : syracuseStep 3294233 = 2470675) B2470675
theorem B2057279 : Blo 1370504 2057279 := bstep (se 1 (by rfl) ⟨1542959, by rfl⟩ : syracuseStep 2057279 = 3085919) B3085919
theorem B2057321 : Blo 1370504 2057321 := bstep (se 2 (by rfl) ⟨771495, by rfl⟩ : syracuseStep 2057321 = 1542991) B1542991
theorem B59327639 : Blo 1370504 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B2057423 : Blo 1370504 2057423 := bstep (se 1 (by rfl) ⟨1543067, by rfl⟩ : syracuseStep 2057423 = 3086135) B3086135
theorem B5277001 : Blo 1370504 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B2057627 : Blo 1370504 2057627 := bstep (se 1 (by rfl) ⟨1543220, by rfl⟩ : syracuseStep 2057627 = 3086441) B3086441
theorem B11716001 : Blo 1370504 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B6940079 : Blo 1370504 6940079 := bstep (se 1 (by rfl) ⟨5205059, by rfl⟩ : syracuseStep 6940079 = 10410119) B10410119
theorem B4630013 : Blo 1370504 4630013 := bstep (se 3 (by rfl) ⟨868127, by rfl⟩ : syracuseStep 4630013 = 1736255) B1736255
theorem B6940241 : Blo 1370504 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B4941433 : Blo 1370504 4941433 := bstep (se 2 (by rfl) ⟨1853037, by rfl⟩ : syracuseStep 4941433 = 3706075) B3706075
theorem B2057849 : Blo 1370504 2057849 := bstep (se 2 (by rfl) ⟨771693, by rfl⟩ : syracuseStep 2057849 = 1543387) B1543387
theorem B9881311 : Blo 1370504 9881311 := bstep (se 1 (by rfl) ⟨7410983, by rfl⟩ : syracuseStep 9881311 = 14821967) B14821967
theorem B2057951 : Blo 1370504 2057951 := bstep (se 1 (by rfl) ⟨1543463, by rfl⟩ : syracuseStep 2057951 = 3086927) B3086927
theorem B2197385 : Blo 1370504 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B1542127 : Blo 1370504 1542127 := bstep (se 1 (by rfl) ⟨1156595, by rfl⟩ : syracuseStep 1542127 = 2313191) B2313191
theorem B2197487 : Blo 1370504 2197487 := bstep (se 1 (by rfl) ⟨1648115, by rfl⟩ : syracuseStep 2197487 = 3296231) B3296231
theorem B5859641 : Blo 1370504 5859641 := bstep (se 2 (by rfl) ⟨2197365, by rfl⟩ : syracuseStep 5859641 = 4394731) B4394731
theorem B1370651 : Blo 1370504 1370651 := bstep (se 1 (by rfl) ⟨1027988, by rfl⟩ : syracuseStep 1370651 = 2055977) B2055977
theorem B1370655 : Blo 1370504 1370655 := bstep (se 1 (by rfl) ⟨1027991, by rfl⟩ : syracuseStep 1370655 = 2055983) B2055983
theorem B4180585 : Blo 1370504 4180585 := bstep (se 2 (by rfl) ⟨1567719, by rfl⟩ : syracuseStep 4180585 = 3135439) B3135439
theorem B1370971 : Blo 1370504 1370971 := bstep (se 1 (by rfl) ⟨1028228, by rfl⟩ : syracuseStep 1370971 = 2056457) B2056457
theorem B1371039 : Blo 1370504 1371039 := bstep (se 1 (by rfl) ⟨1028279, by rfl⟩ : syracuseStep 1371039 = 2056559) B2056559
theorem B1371183 : Blo 1370504 1371183 := bstep (se 1 (by rfl) ⟨1028387, by rfl⟩ : syracuseStep 1371183 = 2056775) B2056775
theorem B1371207 : Blo 1370504 1371207 := bstep (se 1 (by rfl) ⟨1028405, by rfl⟩ : syracuseStep 1371207 = 2056811) B2056811
theorem B2927839 : Blo 1370504 2927839 := bstep (se 1 (by rfl) ⟨2195879, by rfl⟩ : syracuseStep 2927839 = 4391759) B4391759
theorem B1371359 : Blo 1370504 1371359 := bstep (se 1 (by rfl) ⟨1028519, by rfl⟩ : syracuseStep 1371359 = 2057039) B2057039
theorem B2313481 : Blo 1370504 2313481 := bstep (se 2 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 2313481 = 1735111) B1735111
theorem B1584463 : Blo 1370504 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B5557673 : Blo 1370504 5557673 := bstep (se 2 (by rfl) ⟨2084127, by rfl⟩ : syracuseStep 5557673 = 4168255) B4168255
theorem B1371623 : Blo 1370504 1371623 := bstep (se 1 (by rfl) ⟨1028717, by rfl⟩ : syracuseStep 1371623 = 2057435) B2057435
theorem B3083849 : Blo 1370504 3083849 := bstep (se 2 (by rfl) ⟨1156443, by rfl⟩ : syracuseStep 3083849 = 2312887) B2312887
theorem B1371739 : Blo 1370504 1371739 := bstep (se 1 (by rfl) ⟨1028804, by rfl⟩ : syracuseStep 1371739 = 2057609) B2057609
theorem B22851233 : Blo 1370504 22851233 := bstep (se 2 (by rfl) ⟨8569212, by rfl⟩ : syracuseStep 22851233 = 17138425) B17138425
theorem B2314055 : Blo 1370504 2314055 := bstep (se 1 (by rfl) ⟨1735541, by rfl⟩ : syracuseStep 2314055 = 3471083) B3471083
theorem B1371975 : Blo 1370504 1371975 := bstep (se 1 (by rfl) ⟨1028981, by rfl⟩ : syracuseStep 1371975 = 2057963) B2057963
theorem B6180713 : Blo 1370504 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B2781049 : Blo 1370504 2781049 := bstep (se 2 (by rfl) ⟨1042893, by rfl⟩ : syracuseStep 2781049 = 2085787) B2085787
theorem B6942671 : Blo 1370504 6942671 := bstep (se 1 (by rfl) ⟨5207003, by rfl⟩ : syracuseStep 6942671 = 10414007) B10414007
theorem B5206139 : Blo 1370504 5206139 := bstep (se 1 (by rfl) ⟨3904604, by rfl⟩ : syracuseStep 5206139 = 7809209) B7809209
theorem B1978679 : Blo 1370504 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B2314703 : Blo 1370504 2314703 := bstep (se 1 (by rfl) ⟨1736027, by rfl⟩ : syracuseStep 2314703 = 3472055) B3472055
theorem B3469817 : Blo 1370504 3469817 := bstep (se 2 (by rfl) ⟨1301181, by rfl⟩ : syracuseStep 3469817 = 2602363) B2602363
theorem B15831553 : Blo 1370504 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B7811599 : Blo 1370504 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B10023671 : Blo 1370504 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B20034469 : Blo 1370504 20034469 := bstep (se 4 (by rfl) ⟨1878231, by rfl⟩ : syracuseStep 20034469 = 3756463) B3756463
theorem B3085307 : Blo 1370504 3085307 := bstep (se 1 (by rfl) ⟨2313980, by rfl⟩ : syracuseStep 3085307 = 4627961) B4627961
theorem B11711627 : Blo 1370504 11711627 := bstep (se 1 (by rfl) ⟨8783720, by rfl⟩ : syracuseStep 11711627 = 17567441) B17567441
theorem B6255755 : Blo 1370504 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B3085487 : Blo 1370504 3085487 := bstep (se 1 (by rfl) ⟨2314115, by rfl⟩ : syracuseStep 3085487 = 4628231) B4628231
theorem B11277521 : Blo 1370504 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B3085523 : Blo 1370504 3085523 := bstep (se 1 (by rfl) ⟨2314142, by rfl⟩ : syracuseStep 3085523 = 4628285) B4628285
theorem B25023745 : Blo 1370504 25023745 := bstep (se 2 (by rfl) ⟨9383904, by rfl⟩ : syracuseStep 25023745 = 18767809) B18767809
theorem B3904787 : Blo 1370504 3904787 := bstep (se 1 (by rfl) ⟨2928590, by rfl⟩ : syracuseStep 3904787 = 5857181) B5857181
theorem B5010785 : Blo 1370504 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B6944129 : Blo 1370504 6944129 := bstep (se 2 (by rfl) ⟨2604048, by rfl⟩ : syracuseStep 6944129 = 5208097) B5208097
theorem B3085793 : Blo 1370504 3085793 := bstep (se 2 (by rfl) ⟨1157172, by rfl⟩ : syracuseStep 3085793 = 2314345) B2314345
theorem B3339959 : Blo 1370504 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B2225951 : Blo 1370504 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B4626233 : Blo 1370504 4626233 := bstep (se 2 (by rfl) ⟨1734837, by rfl⟩ : syracuseStep 4626233 = 3469675) B3469675
theorem B4626395 : Blo 1370504 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B5560345 : Blo 1370504 5560345 := bstep (se 2 (by rfl) ⟨2085129, by rfl⟩ : syracuseStep 5560345 = 4170259) B4170259
theorem B3471457 : Blo 1370504 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B3127439 : Blo 1370504 3127439 := bstep (se 1 (by rfl) ⟨2345579, by rfl⟩ : syracuseStep 3127439 = 4691159) B4691159
theorem B6944939 : Blo 1370504 6944939 := bstep (se 1 (by rfl) ⟨5208704, by rfl⟩ : syracuseStep 6944939 = 10417409) B10417409
theorem B4626665 : Blo 1370504 4626665 := bstep (se 2 (by rfl) ⟨1734999, by rfl⟩ : syracuseStep 4626665 = 3469999) B3469999
theorem B1734959 : Blo 1370504 1734959 := bstep (se 1 (by rfl) ⟨1301219, by rfl⟩ : syracuseStep 1734959 = 2602439) B2602439
theorem B1464863 : Blo 1370504 1464863 := bstep (se 1 (by rfl) ⟨1098647, by rfl⟩ : syracuseStep 1464863 = 2197295) B2197295
theorem B4627097 : Blo 1370504 4627097 := bstep (se 2 (by rfl) ⟨1735161, by rfl⟩ : syracuseStep 4627097 = 3470323) B3470323
theorem B8452831 : Blo 1370504 8452831 := bstep (se 1 (by rfl) ⟨6339623, by rfl⟩ : syracuseStep 8452831 = 12679247) B12679247
theorem B8788769 : Blo 1370504 8788769 := bstep (se 2 (by rfl) ⟨3295788, by rfl⟩ : syracuseStep 8788769 = 6591577) B6591577
theorem B23755639 : Blo 1370504 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B6585947 : Blo 1370504 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B3128975 : Blo 1370504 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B37510877 : Blo 1370504 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B2056007 : Blo 1370504 2056007 := bstep (se 1 (by rfl) ⟨1542005, by rfl⟩ : syracuseStep 2056007 = 3084011) B3084011
theorem B2195321 : Blo 1370504 2195321 := bstep (se 2 (by rfl) ⟨823245, by rfl⟩ : syracuseStep 2195321 = 1646491) B1646491
theorem B2056091 : Blo 1370504 2056091 := bstep (se 1 (by rfl) ⟨1542068, by rfl⟩ : syracuseStep 2056091 = 3084137) B3084137
theorem B3293099 : Blo 1370504 3293099 := bstep (se 1 (by rfl) ⟨2469824, by rfl⟩ : syracuseStep 3293099 = 4939649) B4939649
theorem B4628609 : Blo 1370504 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B29655173 : Blo 1370504 29655173 := bstep (se 4 (by rfl) ⟨2780172, by rfl⟩ : syracuseStep 29655173 = 5560345) B5560345
theorem B17580563 : Blo 1370504 17580563 := bstep (se 1 (by rfl) ⟨13185422, by rfl⟩ : syracuseStep 17580563 = 26370845) B26370845
theorem B2056871 : Blo 1370504 2056871 := bstep (se 1 (by rfl) ⟨1542653, by rfl⟩ : syracuseStep 2056871 = 3085307) B3085307
theorem B2196155 : Blo 1370504 2196155 := bstep (se 1 (by rfl) ⟨1647116, by rfl⟩ : syracuseStep 2196155 = 3294233) B3294233
theorem B7807751 : Blo 1370504 7807751 := bstep (se 1 (by rfl) ⟨5855813, by rfl⟩ : syracuseStep 7807751 = 11711627) B11711627
theorem B4170503 : Blo 1370504 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B39551759 : Blo 1370504 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B2056991 : Blo 1370504 2056991 := bstep (se 1 (by rfl) ⟨1542743, by rfl⟩ : syracuseStep 2056991 = 3085487) B3085487
theorem B2057015 : Blo 1370504 2057015 := bstep (se 1 (by rfl) ⟨1542761, by rfl⟩ : syracuseStep 2057015 = 3085523) B3085523
theorem B5276477 : Blo 1370504 5276477 := bstep (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) B1978679
theorem B4629419 : Blo 1370504 4629419 := bstep (se 1 (by rfl) ⟨3472064, by rfl⟩ : syracuseStep 4629419 = 6944129) B6944129
theorem B2057195 : Blo 1370504 2057195 := bstep (se 1 (by rfl) ⟨1542896, by rfl⟩ : syracuseStep 2057195 = 3085793) B3085793
theorem B1483967 : Blo 1370504 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B8783129 : Blo 1370504 8783129 := bstep (se 2 (by rfl) ⟨3293673, by rfl⟩ : syracuseStep 8783129 = 6587347) B6587347
theorem B4629959 : Blo 1370504 4629959 := bstep (se 1 (by rfl) ⟨3472469, by rfl⟩ : syracuseStep 4629959 = 6944939) B6944939
theorem B5859179 : Blo 1370504 5859179 := bstep (se 1 (by rfl) ⟨4394384, by rfl⟩ : syracuseStep 5859179 = 8788769) B8788769
theorem B6588577 : Blo 1370504 6588577 := bstep (se 2 (by rfl) ⟨2470716, by rfl⟩ : syracuseStep 6588577 = 4941433) B4941433
theorem B106850501 : Blo 1370504 106850501 := bstep (se 4 (by rfl) ⟨10017234, by rfl⟩ : syracuseStep 106850501 = 20034469) B20034469
theorem B3705115 : Blo 1370504 3705115 := bstep (se 1 (by rfl) ⟨2778836, by rfl⟩ : syracuseStep 3705115 = 5557673) B5557673
theorem B13175081 : Blo 1370504 13175081 := bstep (se 2 (by rfl) ⟨4940655, by rfl⟩ : syracuseStep 13175081 = 9881311) B9881311
theorem B1370671 : Blo 1370504 1370671 := bstep (se 1 (by rfl) ⟨1028003, by rfl⟩ : syracuseStep 1370671 = 2056007) B2056007
theorem B1542703 : Blo 1370504 1542703 := bstep (se 1 (by rfl) ⟨1157027, by rfl⟩ : syracuseStep 1542703 = 2314055) B2314055
theorem B1370727 : Blo 1370504 1370727 := bstep (se 1 (by rfl) ⟨1028045, by rfl⟩ : syracuseStep 1370727 = 2056091) B2056091
theorem B5859965 : Blo 1370504 5859965 := bstep (se 3 (by rfl) ⟨1098743, by rfl⟩ : syracuseStep 5859965 = 2197487) B2197487
theorem B1371103 : Blo 1370504 1371103 := bstep (se 1 (by rfl) ⟨1028327, by rfl⟩ : syracuseStep 1371103 = 2056655) B2056655
theorem B1543135 : Blo 1370504 1543135 := bstep (se 1 (by rfl) ⟨1157351, by rfl⟩ : syracuseStep 1543135 = 2314703) B2314703
theorem B2313211 : Blo 1370504 2313211 := bstep (se 1 (by rfl) ⟨1734908, by rfl⟩ : syracuseStep 2313211 = 3469817) B3469817
theorem B1371131 : Blo 1370504 1371131 := bstep (se 1 (by rfl) ⟨1028348, by rfl⟩ : syracuseStep 1371131 = 2056697) B2056697
theorem B1371199 : Blo 1370504 1371199 := bstep (se 1 (by rfl) ⟨1028399, by rfl⟩ : syracuseStep 1371199 = 2056799) B2056799
theorem B22228145 : Blo 1370504 22228145 := bstep (se 2 (by rfl) ⟨8335554, by rfl⟩ : syracuseStep 22228145 = 16671109) B16671109
theorem B10415465 : Blo 1370504 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1371519 : Blo 1370504 1371519 := bstep (se 1 (by rfl) ⟨1028639, by rfl⟩ : syracuseStep 1371519 = 2057279) B2057279
theorem B1371547 : Blo 1370504 1371547 := bstep (se 1 (by rfl) ⟨1028660, by rfl⟩ : syracuseStep 1371547 = 2057321) B2057321
theorem B11120041 : Blo 1370504 11120041 := bstep (se 2 (by rfl) ⟨4170015, by rfl⟩ : syracuseStep 11120041 = 8340031) B8340031
theorem B1371615 : Blo 1370504 1371615 := bstep (se 1 (by rfl) ⟨1028711, by rfl⟩ : syracuseStep 1371615 = 2057423) B2057423
theorem B1371751 : Blo 1370504 1371751 := bstep (se 1 (by rfl) ⟨1028813, by rfl⟩ : syracuseStep 1371751 = 2057627) B2057627
theorem B7810667 : Blo 1370504 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B1371899 : Blo 1370504 1371899 := bstep (se 1 (by rfl) ⟨1028924, by rfl⟩ : syracuseStep 1371899 = 2057849) B2057849
theorem B1371967 : Blo 1370504 1371967 := bstep (se 1 (by rfl) ⟨1028975, by rfl⟩ : syracuseStep 1371967 = 2057951) B2057951
theorem B31674185 : Blo 1370504 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B3084155 : Blo 1370504 3084155 := bstep (se 1 (by rfl) ⟨2313116, by rfl⟩ : syracuseStep 3084155 = 4626233) B4626233
theorem B3084263 : Blo 1370504 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B2469881 : Blo 1370504 2469881 := bstep (se 2 (by rfl) ⟨926205, by rfl⟩ : syracuseStep 2469881 = 1852411) B1852411
theorem B2084959 : Blo 1370504 2084959 := bstep (se 1 (by rfl) ⟨1563719, by rfl⟩ : syracuseStep 2084959 = 3127439) B3127439
theorem B3084443 : Blo 1370504 3084443 := bstep (se 1 (by rfl) ⟨2313332, by rfl⟩ : syracuseStep 3084443 = 4626665) B4626665
theorem B3903785 : Blo 1370504 3903785 := bstep (se 2 (by rfl) ⟨1463919, by rfl⟩ : syracuseStep 3903785 = 2927839) B2927839
theorem B3084641 : Blo 1370504 3084641 := bstep (se 2 (by rfl) ⟨1156740, by rfl⟩ : syracuseStep 3084641 = 2313481) B2313481
theorem B3084731 : Blo 1370504 3084731 := bstep (se 1 (by rfl) ⟨2313548, by rfl⟩ : syracuseStep 3084731 = 4627097) B4627097
theorem B100029005 : Blo 1370504 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B5854189 : Blo 1370504 5854189 := bstep (se 3 (by rfl) ⟨1097660, by rfl⟩ : syracuseStep 5854189 = 2195321) B2195321
theorem B2085983 : Blo 1370504 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B15234155 : Blo 1370504 15234155 := bstep (se 1 (by rfl) ⟨11425616, by rfl⟩ : syracuseStep 15234155 = 22851233) B22851233
theorem B3708065 : Blo 1370504 3708065 := bstep (se 2 (by rfl) ⟨1390524, by rfl⟩ : syracuseStep 3708065 = 2781049) B2781049
theorem B3470759 : Blo 1370504 3470759 := bstep (se 1 (by rfl) ⟨2603069, by rfl⟩ : syracuseStep 3470759 = 5206139) B5206139
theorem B3085991 : Blo 1370504 3085991 := bstep (se 1 (by rfl) ⟨2314493, by rfl⟩ : syracuseStep 3085991 = 4628987) B4628987
theorem B3905243 : Blo 1370504 3905243 := bstep (se 1 (by rfl) ⟨2928932, by rfl⟩ : syracuseStep 3905243 = 5857865) B5857865
theorem B6682447 : Blo 1370504 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B3086171 : Blo 1370504 3086171 := bstep (se 1 (by rfl) ⟨2314628, by rfl⟩ : syracuseStep 3086171 = 4629257) B4629257
theorem B13178771 : Blo 1370504 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B21108737 : Blo 1370504 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B356743253 : Blo 1370504 356743253 := bstep (se 8 (by rfl) ⟨2090292, by rfl⟩ : syracuseStep 356743253 = 4180585) B4180585
theorem B4626557 : Blo 1370504 4626557 := bstep (se 3 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 4626557 = 1734959) B1734959
theorem B7518347 : Blo 1370504 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B2603191 : Blo 1370504 2603191 := bstep (se 1 (by rfl) ⟨1952393, by rfl⟩ : syracuseStep 2603191 = 3904787) B3904787
theorem B3340523 : Blo 1370504 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B4626719 : Blo 1370504 4626719 := bstep (se 1 (by rfl) ⟨3470039, by rfl⟩ : syracuseStep 4626719 = 6940079) B6940079
theorem B11270441 : Blo 1370504 11270441 := bstep (se 2 (by rfl) ⟨4226415, by rfl⟩ : syracuseStep 11270441 = 8452831) B8452831
theorem B3086675 : Blo 1370504 3086675 := bstep (se 1 (by rfl) ⟨2315006, by rfl⟩ : syracuseStep 3086675 = 4630013) B4630013
theorem B4626827 : Blo 1370504 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B1464923 : Blo 1370504 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B3906301 : Blo 1370504 3906301 := bstep (se 3 (by rfl) ⟨732431, by rfl⟩ : syracuseStep 3906301 = 1464863) B1464863
theorem B3906427 : Blo 1370504 3906427 := bstep (se 1 (by rfl) ⟨2929820, by rfl⟩ : syracuseStep 3906427 = 5859641) B5859641
theorem B33364993 : Blo 1370504 33364993 := bstep (se 2 (by rfl) ⟨12511872, by rfl⟩ : syracuseStep 33364993 = 25023745) B25023745
theorem B7036001 : Blo 1370504 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B2112617 : Blo 1370504 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B35626229 : Blo 1370504 35626229 := bstep (se 5 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 35626229 = 3339959) B3339959
theorem B2055899 : Blo 1370504 2055899 := bstep (se 1 (by rfl) ⟨1541924, by rfl⟩ : syracuseStep 2055899 = 3083849) B3083849
theorem B4390631 : Blo 1370504 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B4120475 : Blo 1370504 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B2195399 : Blo 1370504 2195399 := bstep (se 1 (by rfl) ⟨1646549, by rfl⟩ : syracuseStep 2195399 = 3293099) B3293099
theorem B4628447 : Blo 1370504 4628447 := bstep (se 1 (by rfl) ⟨3471335, by rfl⟩ : syracuseStep 4628447 = 6942671) B6942671
theorem B2056169 : Blo 1370504 2056169 := bstep (se 2 (by rfl) ⟨771063, by rfl⟩ : syracuseStep 2056169 = 1542127) B1542127
theorem B2056295 : Blo 1370504 2056295 := bstep (se 1 (by rfl) ⟨1542221, by rfl⟩ : syracuseStep 2056295 = 3084443) B3084443
theorem B2056427 : Blo 1370504 2056427 := bstep (se 1 (by rfl) ⟨1542320, by rfl⟩ : syracuseStep 2056427 = 3084641) B3084641
theorem B2056487 : Blo 1370504 2056487 := bstep (se 1 (by rfl) ⟨1542365, by rfl⟩ : syracuseStep 2056487 = 3084731) B3084731
theorem B4940153 : Blo 1370504 4940153 := bstep (se 2 (by rfl) ⟨1852557, by rfl⟩ : syracuseStep 4940153 = 3705115) B3705115
theorem B3957245 : Blo 1370504 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B2056937 : Blo 1370504 2056937 := bstep (se 2 (by rfl) ⟨771351, by rfl⟩ : syracuseStep 2056937 = 1542703) B1542703
theorem B2057327 : Blo 1370504 2057327 := bstep (se 1 (by rfl) ⟨1542995, by rfl⟩ : syracuseStep 2057327 = 3085991) B3085991
theorem B2057447 : Blo 1370504 2057447 := bstep (se 1 (by rfl) ⟨1543085, by rfl⟩ : syracuseStep 2057447 = 3086171) B3086171
theorem B2057513 : Blo 1370504 2057513 := bstep (se 2 (by rfl) ⟨771567, by rfl⟩ : syracuseStep 2057513 = 1543135) B1543135
theorem B8783387 : Blo 1370504 8783387 := bstep (se 1 (by rfl) ⟨6587540, by rfl⟩ : syracuseStep 8783387 = 13175081) B13175081
theorem B7513627 : Blo 1370504 7513627 := bstep (se 1 (by rfl) ⟨5635220, by rfl⟩ : syracuseStep 7513627 = 11270441) B11270441
theorem B2057783 : Blo 1370504 2057783 := bstep (se 1 (by rfl) ⟨1543337, by rfl⟩ : syracuseStep 2057783 = 3086675) B3086675
theorem B23750819 : Blo 1370504 23750819 := bstep (se 1 (by rfl) ⟨17813114, by rfl⟩ : syracuseStep 23750819 = 35626229) B35626229
theorem B1646587 : Blo 1370504 1646587 := bstep (se 1 (by rfl) ⟨1234940, by rfl⟩ : syracuseStep 1646587 = 2469881) B2469881
theorem B10987933 : Blo 1370504 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B1370599 : Blo 1370504 1370599 := bstep (se 1 (by rfl) ⟨1027949, by rfl⟩ : syracuseStep 1370599 = 2055899) B2055899
theorem B2927087 : Blo 1370504 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B1370779 : Blo 1370504 1370779 := bstep (se 1 (by rfl) ⟨1028084, by rfl⟩ : syracuseStep 1370779 = 2056169) B2056169
theorem B19770115 : Blo 1370504 19770115 := bstep (se 1 (by rfl) ⟨14827586, by rfl⟩ : syracuseStep 19770115 = 29655173) B29655173
theorem B8784769 : Blo 1370504 8784769 := bstep (se 2 (by rfl) ⟨3294288, by rfl⟩ : syracuseStep 8784769 = 6588577) B6588577
theorem B66686003 : Blo 1370504 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B1371247 : Blo 1370504 1371247 := bstep (se 1 (by rfl) ⟨1028435, by rfl⟩ : syracuseStep 1371247 = 2056871) B2056871
theorem B11119781 : Blo 1370504 11119781 := bstep (se 4 (by rfl) ⟨1042479, by rfl⟩ : syracuseStep 11119781 = 2084959) B2084959
theorem B5205167 : Blo 1370504 5205167 := bstep (se 1 (by rfl) ⟨3903875, by rfl⟩ : syracuseStep 5205167 = 7807751) B7807751
theorem B2780335 : Blo 1370504 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B1371327 : Blo 1370504 1371327 := bstep (se 1 (by rfl) ⟨1028495, by rfl⟩ : syracuseStep 1371327 = 2056991) B2056991
theorem B1371343 : Blo 1370504 1371343 := bstep (se 1 (by rfl) ⟨1028507, by rfl⟩ : syracuseStep 1371343 = 2057015) B2057015
theorem B3517651 : Blo 1370504 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B8908061 : Blo 1370504 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B1371463 : Blo 1370504 1371463 := bstep (se 1 (by rfl) ⟨1028597, by rfl⟩ : syracuseStep 1371463 = 2057195) B2057195
theorem B2313839 : Blo 1370504 2313839 := bstep (se 1 (by rfl) ⟨1735379, by rfl⟩ : syracuseStep 2313839 = 3470759) B3470759
theorem B8785847 : Blo 1370504 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B3084281 : Blo 1370504 3084281 := bstep (se 2 (by rfl) ⟨1156605, by rfl⟩ : syracuseStep 3084281 = 2313211) B2313211
theorem B44486657 : Blo 1370504 44486657 := bstep (se 2 (by rfl) ⟨16682496, by rfl⟩ : syracuseStep 44486657 = 33364993) B33364993
theorem B3084371 : Blo 1370504 3084371 := bstep (se 1 (by rfl) ⟨2313278, by rfl⟩ : syracuseStep 3084371 = 4626557) B4626557
theorem B71233667 : Blo 1370504 71233667 := bstep (se 1 (by rfl) ⟨53425250, by rfl⟩ : syracuseStep 71233667 = 106850501) B106850501
theorem B3084479 : Blo 1370504 3084479 := bstep (se 1 (by rfl) ⟨2313359, by rfl⟩ : syracuseStep 3084479 = 4626719) B4626719
theorem B3084551 : Blo 1370504 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B4690667 : Blo 1370504 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B6943643 : Blo 1370504 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B5207111 : Blo 1370504 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B8909929 : Blo 1370504 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B21116123 : Blo 1370504 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B1463599 : Blo 1370504 1463599 := bstep (se 1 (by rfl) ⟨1097699, by rfl⟩ : syracuseStep 1463599 = 2195399) B2195399
theorem B3085631 : Blo 1370504 3085631 := bstep (se 1 (by rfl) ⟨2314223, by rfl⟩ : syracuseStep 3085631 = 4628447) B4628447
theorem B3085739 : Blo 1370504 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B2602523 : Blo 1370504 2602523 := bstep (se 1 (by rfl) ⟨1951892, by rfl⟩ : syracuseStep 2602523 = 3903785) B3903785
theorem B3470921 : Blo 1370504 3470921 := bstep (se 2 (by rfl) ⟨1301595, by rfl⟩ : syracuseStep 3470921 = 2603191) B2603191
theorem B11720375 : Blo 1370504 11720375 := bstep (se 1 (by rfl) ⟨8790281, by rfl⟩ : syracuseStep 11720375 = 17580563) B17580563
theorem B1464103 : Blo 1370504 1464103 := bstep (se 1 (by rfl) ⟨1098077, by rfl⟩ : syracuseStep 1464103 = 2196155) B2196155
theorem B26367839 : Blo 1370504 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B3086279 : Blo 1370504 3086279 := bstep (se 1 (by rfl) ⟨2314709, by rfl⟩ : syracuseStep 3086279 = 4629419) B4629419
theorem B1390655 : Blo 1370504 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B10156103 : Blo 1370504 10156103 := bstep (se 1 (by rfl) ⟨7617077, by rfl⟩ : syracuseStep 10156103 = 15234155) B15234155
theorem B2472043 : Blo 1370504 2472043 := bstep (se 1 (by rfl) ⟨1854032, by rfl⟩ : syracuseStep 2472043 = 3708065) B3708065
theorem B5855419 : Blo 1370504 5855419 := bstep (se 1 (by rfl) ⟨4391564, by rfl⟩ : syracuseStep 5855419 = 8783129) B8783129
theorem B3086639 : Blo 1370504 3086639 := bstep (se 1 (by rfl) ⟨2314979, by rfl⟩ : syracuseStep 3086639 = 4629959) B4629959
theorem B5208401 : Blo 1370504 5208401 := bstep (se 2 (by rfl) ⟨1953150, by rfl⟩ : syracuseStep 5208401 = 3906301) B3906301
theorem B2603495 : Blo 1370504 2603495 := bstep (se 1 (by rfl) ⟨1952621, by rfl⟩ : syracuseStep 2603495 = 3905243) B3905243
theorem B5208569 : Blo 1370504 5208569 := bstep (se 2 (by rfl) ⟨1953213, by rfl⟩ : syracuseStep 5208569 = 3906427) B3906427
theorem B3906119 : Blo 1370504 3906119 := bstep (se 1 (by rfl) ⟨2929589, by rfl⟩ : syracuseStep 3906119 = 5859179) B5859179
theorem B7805585 : Blo 1370504 7805585 := bstep (se 2 (by rfl) ⟨2927094, by rfl⟩ : syracuseStep 7805585 = 5854189) B5854189
theorem B14072491 : Blo 1370504 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B237828835 : Blo 1370504 237828835 := bstep (se 1 (by rfl) ⟨178371626, by rfl⟩ : syracuseStep 237828835 = 356743253) B356743253
theorem B5012231 : Blo 1370504 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B3906461 : Blo 1370504 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B3906643 : Blo 1370504 3906643 := bstep (se 1 (by rfl) ⟨2929982, by rfl⟩ : syracuseStep 3906643 = 5859965) B5859965
theorem B14826721 : Blo 1370504 14826721 := bstep (se 2 (by rfl) ⟨5560020, by rfl⟩ : syracuseStep 14826721 = 11120041) B11120041
theorem B1408411 : Blo 1370504 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B14818763 : Blo 1370504 14818763 := bstep (se 1 (by rfl) ⟨11114072, by rfl⟩ : syracuseStep 14818763 = 22228145) B22228145
theorem B2056103 : Blo 1370504 2056103 := bstep (se 1 (by rfl) ⟨1542077, by rfl⟩ : syracuseStep 2056103 = 3084155) B3084155
theorem B2056175 : Blo 1370504 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B2056247 : Blo 1370504 2056247 := bstep (se 1 (by rfl) ⟨1542185, by rfl⟩ : syracuseStep 2056247 = 3084371) B3084371
theorem B47489111 : Blo 1370504 47489111 := bstep (se 1 (by rfl) ⟨35616833, by rfl⟩ : syracuseStep 47489111 = 71233667) B71233667
theorem B2056319 : Blo 1370504 2056319 := bstep (se 1 (by rfl) ⟨1542239, by rfl⟩ : syracuseStep 2056319 = 3084479) B3084479
theorem B2056367 : Blo 1370504 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B7807225 : Blo 1370504 7807225 := bstep (se 2 (by rfl) ⟨2927709, by rfl⟩ : syracuseStep 7807225 = 5855419) B5855419
theorem B3293435 : Blo 1370504 3293435 := bstep (se 1 (by rfl) ⟨2470076, by rfl⟩ : syracuseStep 3293435 = 4940153) B4940153
theorem B2638163 : Blo 1370504 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B4629095 : Blo 1370504 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B2057087 : Blo 1370504 2057087 := bstep (se 1 (by rfl) ⟨1542815, by rfl⟩ : syracuseStep 2057087 = 3085631) B3085631
theorem B14828453 : Blo 1370504 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B2057159 : Blo 1370504 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B317105113 : Blo 1370504 317105113 := bstep (se 2 (by rfl) ⟨118914417, by rfl⟩ : syracuseStep 317105113 = 237828835) B237828835
theorem B18760805 : Blo 1370504 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B2057519 : Blo 1370504 2057519 := bstep (se 1 (by rfl) ⟨1543139, by rfl⟩ : syracuseStep 2057519 = 3086279) B3086279
theorem B11879905 : Blo 1370504 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B2057759 : Blo 1370504 2057759 := bstep (se 1 (by rfl) ⟨1543319, by rfl⟩ : syracuseStep 2057759 = 3086639) B3086639
theorem B19768961 : Blo 1370504 19768961 := bstep (se 2 (by rfl) ⟨7413360, by rfl⟩ : syracuseStep 19768961 = 14826721) B14826721
theorem B1951391 : Blo 1370504 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B1951465 : Blo 1370504 1951465 := bstep (se 2 (by rfl) ⟨731799, by rfl⟩ : syracuseStep 1951465 = 1463599) B1463599
theorem B5203723 : Blo 1370504 5203723 := bstep (se 1 (by rfl) ⟨3902792, by rfl⟩ : syracuseStep 5203723 = 7805585) B7805585
theorem B1877881 : Blo 1370504 1877881 := bstep (se 2 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 1877881 = 1408411) B1408411
theorem B1952137 : Blo 1370504 1952137 := bstep (se 2 (by rfl) ⟨732051, by rfl⟩ : syracuseStep 1952137 = 1464103) B1464103
theorem B1542559 : Blo 1370504 1542559 := bstep (se 1 (by rfl) ⟨1156919, by rfl⟩ : syracuseStep 1542559 = 2313839) B2313839
theorem B1370735 : Blo 1370504 1370735 := bstep (se 1 (by rfl) ⟨1028051, by rfl⟩ : syracuseStep 1370735 = 2056103) B2056103
theorem B1370783 : Blo 1370504 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B29657771 : Blo 1370504 29657771 := bstep (se 1 (by rfl) ⟨22243328, by rfl⟩ : syracuseStep 29657771 = 44486657) B44486657
theorem B1370863 : Blo 1370504 1370863 := bstep (se 1 (by rfl) ⟨1028147, by rfl⟩ : syracuseStep 1370863 = 2056295) B2056295
theorem B53463797 : Blo 1370504 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B3296057 : Blo 1370504 3296057 := bstep (se 2 (by rfl) ⟨1236021, by rfl⟩ : syracuseStep 3296057 = 2472043) B2472043
theorem B1370951 : Blo 1370504 1370951 := bstep (se 1 (by rfl) ⟨1028213, by rfl⟩ : syracuseStep 1370951 = 2056427) B2056427
theorem B1370991 : Blo 1370504 1370991 := bstep (se 1 (by rfl) ⟨1028243, by rfl⟩ : syracuseStep 1370991 = 2056487) B2056487
theorem B1371291 : Blo 1370504 1371291 := bstep (se 1 (by rfl) ⟨1028468, by rfl⟩ : syracuseStep 1371291 = 2056937) B2056937
theorem B14650577 : Blo 1370504 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B1371551 : Blo 1370504 1371551 := bstep (se 1 (by rfl) ⟨1028663, by rfl⟩ : syracuseStep 1371551 = 2057327) B2057327
theorem B14077415 : Blo 1370504 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B1371631 : Blo 1370504 1371631 := bstep (se 1 (by rfl) ⟨1028723, by rfl⟩ : syracuseStep 1371631 = 2057447) B2057447
theorem B1371675 : Blo 1370504 1371675 := bstep (se 1 (by rfl) ⟨1028756, by rfl⟩ : syracuseStep 1371675 = 2057513) B2057513
theorem B18763321 : Blo 1370504 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B1371855 : Blo 1370504 1371855 := bstep (se 1 (by rfl) ⟨1028891, by rfl⟩ : syracuseStep 1371855 = 2057783) B2057783
theorem B2313947 : Blo 1370504 2313947 := bstep (se 1 (by rfl) ⟨1735460, by rfl⟩ : syracuseStep 2313947 = 3470921) B3470921
theorem B6770735 : Blo 1370504 6770735 := bstep (se 1 (by rfl) ⟨5078051, by rfl⟩ : syracuseStep 6770735 = 10156103) B10156103
theorem B3470111 : Blo 1370504 3470111 := bstep (se 1 (by rfl) ⟨2602583, by rfl⟩ : syracuseStep 3470111 = 5205167) B5205167
theorem B3708413 : Blo 1370504 3708413 := bstep (se 3 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 3708413 = 1390655) B1390655
theorem B29652749 : Blo 1370504 29652749 := bstep (se 3 (by rfl) ⟨5559890, by rfl⟩ : syracuseStep 29652749 = 11119781) B11119781
theorem B3471407 : Blo 1370504 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B23754829 : Blo 1370504 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B26360153 : Blo 1370504 26360153 := bstep (se 2 (by rfl) ⟨9885057, by rfl⟩ : syracuseStep 26360153 = 19770115) B19770115
theorem B5855591 : Blo 1370504 5855591 := bstep (se 1 (by rfl) ⟨4391693, by rfl⟩ : syracuseStep 5855591 = 8783387) B8783387
theorem B1735015 : Blo 1370504 1735015 := bstep (se 1 (by rfl) ⟨1301261, by rfl⟩ : syracuseStep 1735015 = 2602523) B2602523
theorem B7813583 : Blo 1370504 7813583 := bstep (se 1 (by rfl) ⟨5860187, by rfl⟩ : syracuseStep 7813583 = 11720375) B11720375
theorem B11713025 : Blo 1370504 11713025 := bstep (se 2 (by rfl) ⟨4392384, by rfl⟩ : syracuseStep 11713025 = 8784769) B8784769
theorem B17578559 : Blo 1370504 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B15833879 : Blo 1370504 15833879 := bstep (se 1 (by rfl) ⟨11875409, by rfl⟩ : syracuseStep 15833879 = 23750819) B23750819
theorem B5208857 : Blo 1370504 5208857 := bstep (se 2 (by rfl) ⟨1953321, by rfl⟩ : syracuseStep 5208857 = 3906643) B3906643
theorem B3472267 : Blo 1370504 3472267 := bstep (se 1 (by rfl) ⟨2604200, by rfl⟩ : syracuseStep 3472267 = 5208401) B5208401
theorem B1735663 : Blo 1370504 1735663 := bstep (se 1 (by rfl) ⟨1301747, by rfl⟩ : syracuseStep 1735663 = 2603495) B2603495
theorem B3472379 : Blo 1370504 3472379 := bstep (se 1 (by rfl) ⟨2604284, by rfl⟩ : syracuseStep 3472379 = 5208569) B5208569
theorem B2604079 : Blo 1370504 2604079 := bstep (se 1 (by rfl) ⟨1953059, by rfl⟩ : syracuseStep 2604079 = 3906119) B3906119
theorem B2604307 : Blo 1370504 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B12508445 : Blo 1370504 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B44457335 : Blo 1370504 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B10018169 : Blo 1370504 10018169 := bstep (se 2 (by rfl) ⟨3756813, by rfl⟩ : syracuseStep 10018169 = 7513627) B7513627
theorem B9879175 : Blo 1370504 9879175 := bstep (se 1 (by rfl) ⟨7409381, by rfl⟩ : syracuseStep 9879175 = 14818763) B14818763
theorem B5857231 : Blo 1370504 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B8781797 : Blo 1370504 8781797 := bstep (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) B1646587
theorem B2056187 : Blo 1370504 2056187 := bstep (se 1 (by rfl) ⟨1542140, by rfl⟩ : syracuseStep 2056187 = 3084281) B3084281
theorem B4513823 : Blo 1370504 4513823 := bstep (se 1 (by rfl) ⟨3385367, by rfl⟩ : syracuseStep 4513823 = 6770735) B6770735
theorem B2195623 : Blo 1370504 2195623 := bstep (se 1 (by rfl) ⟨1646717, by rfl⟩ : syracuseStep 2195623 = 3293435) B3293435
theorem B2056745 : Blo 1370504 2056745 := bstep (se 2 (by rfl) ⟨771279, by rfl⟩ : syracuseStep 2056745 = 1542559) B1542559
theorem B19768499 : Blo 1370504 19768499 := bstep (se 1 (by rfl) ⟨14826374, by rfl⟩ : syracuseStep 19768499 = 29652749) B29652749
theorem B4629689 : Blo 1370504 4629689 := bstep (se 2 (by rfl) ⟨1736133, by rfl⟩ : syracuseStep 4629689 = 3472267) B3472267
theorem B422806817 : Blo 1370504 422806817 := bstep (se 2 (by rfl) ⟨158552556, by rfl⟩ : syracuseStep 422806817 = 317105113) B317105113
theorem B17573435 : Blo 1370504 17573435 := bstep (se 1 (by rfl) ⟨13180076, by rfl⟩ : syracuseStep 17573435 = 26360153) B26360153
theorem B7808683 : Blo 1370504 7808683 := bstep (se 1 (by rfl) ⟨5856512, by rfl⟩ : syracuseStep 7808683 = 11713025) B11713025
theorem B5203709 : Blo 1370504 5203709 := bstep (se 3 (by rfl) ⟨975695, by rfl⟩ : syracuseStep 5203709 = 1951391) B1951391
theorem B9767051 : Blo 1370504 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B6678779 : Blo 1370504 6678779 := bstep (se 1 (by rfl) ⟨5009084, by rfl⟩ : syracuseStep 6678779 = 10018169) B10018169
theorem B1542631 : Blo 1370504 1542631 := bstep (se 1 (by rfl) ⟨1156973, by rfl⟩ : syracuseStep 1542631 = 2313947) B2313947
theorem B7809641 : Blo 1370504 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B1370791 : Blo 1370504 1370791 := bstep (se 1 (by rfl) ⟨1028093, by rfl⟩ : syracuseStep 1370791 = 2056187) B2056187
theorem B1370831 : Blo 1370504 1370831 := bstep (se 1 (by rfl) ⟨1028123, by rfl⟩ : syracuseStep 1370831 = 2056247) B2056247
theorem B1370879 : Blo 1370504 1370879 := bstep (se 1 (by rfl) ⟨1028159, by rfl⟩ : syracuseStep 1370879 = 2056319) B2056319
theorem B31673105 : Blo 1370504 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B1370911 : Blo 1370504 1370911 := bstep (se 1 (by rfl) ⟨1028183, by rfl⟩ : syracuseStep 1370911 = 2056367) B2056367
theorem B2313353 : Blo 1370504 2313353 := bstep (se 2 (by rfl) ⟨867507, by rfl⟩ : syracuseStep 2313353 = 1735015) B1735015
theorem B2313407 : Blo 1370504 2313407 := bstep (se 1 (by rfl) ⟨1735055, by rfl⟩ : syracuseStep 2313407 = 3470111) B3470111
theorem B1371391 : Blo 1370504 1371391 := bstep (se 1 (by rfl) ⟨1028543, by rfl⟩ : syracuseStep 1371391 = 2057087) B2057087
theorem B1371439 : Blo 1370504 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B1371679 : Blo 1370504 1371679 := bstep (se 1 (by rfl) ⟨1028759, by rfl⟩ : syracuseStep 1371679 = 2057519) B2057519
theorem B1371839 : Blo 1370504 1371839 := bstep (se 1 (by rfl) ⟨1028879, by rfl⟩ : syracuseStep 1371839 = 2057759) B2057759
theorem B37539773 : Blo 1370504 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B2314217 : Blo 1370504 2314217 := bstep (se 2 (by rfl) ⟨867831, by rfl⟩ : syracuseStep 2314217 = 1735663) B1735663
theorem B2314271 : Blo 1370504 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B3903727 : Blo 1370504 3903727 := bstep (se 1 (by rfl) ⟨2927795, by rfl⟩ : syracuseStep 3903727 = 5855591) B5855591
theorem B11719039 : Blo 1370504 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B19771847 : Blo 1370504 19771847 := bstep (se 1 (by rfl) ⟨14828885, by rfl⟩ : syracuseStep 19771847 = 29657771) B29657771
theorem B10555919 : Blo 1370504 10555919 := bstep (se 1 (by rfl) ⟨7916939, by rfl⟩ : syracuseStep 10555919 = 15833879) B15833879
theorem B15839873 : Blo 1370504 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B2314919 : Blo 1370504 2314919 := bstep (se 1 (by rfl) ⟨1736189, by rfl⟩ : syracuseStep 2314919 = 3472379) B3472379
theorem B2601953 : Blo 1370504 2601953 := bstep (se 2 (by rfl) ⟨975732, by rfl⟩ : syracuseStep 2601953 = 1951465) B1951465
theorem B2503841 : Blo 1370504 2503841 := bstep (se 2 (by rfl) ⟨938940, by rfl⟩ : syracuseStep 2503841 = 1877881) B1877881
theorem B5854531 : Blo 1370504 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B31659407 : Blo 1370504 31659407 := bstep (se 1 (by rfl) ⟨23744555, by rfl⟩ : syracuseStep 31659407 = 47489111) B47489111
theorem B1758775 : Blo 1370504 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B10409633 : Blo 1370504 10409633 := bstep (se 2 (by rfl) ⟨3903612, by rfl⟩ : syracuseStep 10409633 = 7807225) B7807225
theorem B3086063 : Blo 1370504 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B2602849 : Blo 1370504 2602849 := bstep (se 2 (by rfl) ⟨976068, by rfl⟩ : syracuseStep 2602849 = 1952137) B1952137
theorem B9885635 : Blo 1370504 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B12507203 : Blo 1370504 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B2472275 : Blo 1370504 2472275 := bstep (se 1 (by rfl) ⟨1854206, by rfl⟩ : syracuseStep 2472275 = 3708413) B3708413
theorem B13179307 : Blo 1370504 13179307 := bstep (se 1 (by rfl) ⟨9884480, by rfl⟩ : syracuseStep 13179307 = 19768961) B19768961
theorem B3472105 : Blo 1370504 3472105 := bstep (se 2 (by rfl) ⟨1302039, by rfl⟩ : syracuseStep 3472105 = 2604079) B2604079
theorem B5209055 : Blo 1370504 5209055 := bstep (se 1 (by rfl) ⟨3906791, by rfl⟩ : syracuseStep 5209055 = 7813583) B7813583
theorem B3472409 : Blo 1370504 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B35642531 : Blo 1370504 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B3472571 : Blo 1370504 3472571 := bstep (se 1 (by rfl) ⟨2604428, by rfl⟩ : syracuseStep 3472571 = 5208857) B5208857
theorem B25017761 : Blo 1370504 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B8789485 : Blo 1370504 8789485 := bstep (se 3 (by rfl) ⟨1648028, by rfl⟩ : syracuseStep 8789485 = 3296057) B3296057
theorem B13172233 : Blo 1370504 13172233 := bstep (se 2 (by rfl) ⟨4939587, by rfl⟩ : syracuseStep 13172233 = 9879175) B9879175
theorem B8338963 : Blo 1370504 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B29638223 : Blo 1370504 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B6938297 : Blo 1370504 6938297 := bstep (se 2 (by rfl) ⟨2601861, by rfl⟩ : syracuseStep 6938297 = 5203723) B5203723
theorem B13181231 : Blo 1370504 13181231 := bstep (se 1 (by rfl) ⟨9885923, by rfl⟩ : syracuseStep 13181231 = 19771847) B19771847
theorem B7037279 : Blo 1370504 7037279 := bstep (se 1 (by rfl) ⟨5277959, by rfl⟩ : syracuseStep 7037279 = 10555919) B10555919
theorem B10559915 : Blo 1370504 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B17572409 : Blo 1370504 17572409 := bstep (se 2 (by rfl) ⟨6589653, by rfl⟩ : syracuseStep 17572409 = 13179307) B13179307
theorem B2056841 : Blo 1370504 2056841 := bstep (se 2 (by rfl) ⟨771315, by rfl⟩ : syracuseStep 2056841 = 1542631) B1542631
theorem B281871211 : Blo 1370504 281871211 := bstep (se 1 (by rfl) ⟨211403408, by rfl⟩ : syracuseStep 281871211 = 422806817) B422806817
theorem B4629473 : Blo 1370504 4629473 := bstep (se 2 (by rfl) ⟨1736052, by rfl⟩ : syracuseStep 4629473 = 3472105) B3472105
theorem B11715623 : Blo 1370504 11715623 := bstep (se 1 (by rfl) ⟨8786717, by rfl⟩ : syracuseStep 11715623 = 17573435) B17573435
theorem B6939755 : Blo 1370504 6939755 := bstep (se 1 (by rfl) ⟨5204816, by rfl⟩ : syracuseStep 6939755 = 10409633) B10409633
theorem B2057375 : Blo 1370504 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1648183 : Blo 1370504 1648183 := bstep (se 1 (by rfl) ⟨1236137, by rfl⟩ : syracuseStep 1648183 = 2472275) B2472275
theorem B26707637 : Blo 1370504 26707637 := bstep (se 5 (by rfl) ⟨1251920, by rfl⟩ : syracuseStep 26707637 = 2503841) B2503841
theorem B11118617 : Blo 1370504 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B2345033 : Blo 1370504 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B1542235 : Blo 1370504 1542235 := bstep (se 1 (by rfl) ⟨1156676, by rfl⟩ : syracuseStep 1542235 = 2313353) B2313353
theorem B1542271 : Blo 1370504 1542271 := bstep (se 1 (by rfl) ⟨1156703, by rfl⟩ : syracuseStep 1542271 = 2313407) B2313407
theorem B71240309 : Blo 1370504 71240309 := bstep (se 5 (by rfl) ⟨3339389, by rfl⟩ : syracuseStep 71240309 = 6678779) B6678779
theorem B1542811 : Blo 1370504 1542811 := bstep (se 1 (by rfl) ⟨1157108, by rfl⟩ : syracuseStep 1542811 = 2314217) B2314217
theorem B3009215 : Blo 1370504 3009215 := bstep (se 1 (by rfl) ⟨2256911, by rfl⟩ : syracuseStep 3009215 = 4513823) B4513823
theorem B1542847 : Blo 1370504 1542847 := bstep (se 1 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 1542847 = 2314271) B2314271
theorem B2927497 : Blo 1370504 2927497 := bstep (se 2 (by rfl) ⟨1097811, by rfl⟩ : syracuseStep 2927497 = 2195623) B2195623
theorem B5204969 : Blo 1370504 5204969 := bstep (se 2 (by rfl) ⟨1951863, by rfl⟩ : syracuseStep 5204969 = 3903727) B3903727
theorem B1371163 : Blo 1370504 1371163 := bstep (se 1 (by rfl) ⟨1028372, by rfl⟩ : syracuseStep 1371163 = 2056745) B2056745
theorem B1543279 : Blo 1370504 1543279 := bstep (se 1 (by rfl) ⟨1157459, by rfl⟩ : syracuseStep 1543279 = 2314919) B2314919
theorem B15625385 : Blo 1370504 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B21106271 : Blo 1370504 21106271 := bstep (se 1 (by rfl) ⟨15829703, by rfl⟩ : syracuseStep 21106271 = 31659407) B31659407
theorem B3469139 : Blo 1370504 3469139 := bstep (se 1 (by rfl) ⟨2601854, by rfl⟩ : syracuseStep 3469139 = 5203709) B5203709
theorem B6590423 : Blo 1370504 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B5206427 : Blo 1370504 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B21115403 : Blo 1370504 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B11719313 : Blo 1370504 11719313 := bstep (se 2 (by rfl) ⟨4394742, by rfl⟩ : syracuseStep 11719313 = 8789485) B8789485
theorem B2314939 : Blo 1370504 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B23761687 : Blo 1370504 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B2315047 : Blo 1370504 2315047 := bstep (se 1 (by rfl) ⟨1736285, by rfl⟩ : syracuseStep 2315047 = 3472571) B3472571
theorem B4625531 : Blo 1370504 4625531 := bstep (se 1 (by rfl) ⟨3469148, by rfl⟩ : syracuseStep 4625531 = 6938297) B6938297
theorem B3470465 : Blo 1370504 3470465 := bstep (se 2 (by rfl) ⟨1301424, by rfl⟩ : syracuseStep 3470465 = 2602849) B2602849
theorem B1734635 : Blo 1370504 1734635 := bstep (se 1 (by rfl) ⟨1300976, by rfl⟩ : syracuseStep 1734635 = 2601953) B2601953
theorem B13178999 : Blo 1370504 13178999 := bstep (se 1 (by rfl) ⟨9884249, by rfl⟩ : syracuseStep 13178999 = 19768499) B19768499
theorem B3086459 : Blo 1370504 3086459 := bstep (se 1 (by rfl) ⟨2314844, by rfl⟩ : syracuseStep 3086459 = 4629689) B4629689
theorem B8338135 : Blo 1370504 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B6511367 : Blo 1370504 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B7806041 : Blo 1370504 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B3472703 : Blo 1370504 3472703 := bstep (se 1 (by rfl) ⟨2604527, by rfl⟩ : syracuseStep 3472703 = 5209055) B5209055
theorem B17562977 : Blo 1370504 17562977 := bstep (se 2 (by rfl) ⟨6586116, by rfl⟩ : syracuseStep 17562977 = 13172233) B13172233
theorem B10411577 : Blo 1370504 10411577 := bstep (se 2 (by rfl) ⟨3904341, by rfl⟩ : syracuseStep 10411577 = 7808683) B7808683
theorem B16678507 : Blo 1370504 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B19758815 : Blo 1370504 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B25026515 : Blo 1370504 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B2056313 : Blo 1370504 2056313 := bstep (se 2 (by rfl) ⟨771117, by rfl⟩ : syracuseStep 2056313 = 1542235) B1542235
theorem B2056361 : Blo 1370504 2056361 := bstep (se 2 (by rfl) ⟨771135, by rfl⟩ : syracuseStep 2056361 = 1542271) B1542271
theorem B11714939 : Blo 1370504 11714939 := bstep (se 1 (by rfl) ⟨8786204, by rfl⟩ : syracuseStep 11714939 = 17572409) B17572409
theorem B2057081 : Blo 1370504 2057081 := bstep (se 2 (by rfl) ⟨771405, by rfl⟩ : syracuseStep 2057081 = 1542811) B1542811
theorem B2057129 : Blo 1370504 2057129 := bstep (se 2 (by rfl) ⟨771423, by rfl⟩ : syracuseStep 2057129 = 1542847) B1542847
theorem B11117513 : Blo 1370504 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B2057639 : Blo 1370504 2057639 := bstep (se 1 (by rfl) ⟨1543229, by rfl⟩ : syracuseStep 2057639 = 3086459) B3086459
theorem B2057705 : Blo 1370504 2057705 := bstep (se 2 (by rfl) ⟨771639, by rfl⟩ : syracuseStep 2057705 = 1543279) B1543279
theorem B5204027 : Blo 1370504 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B2197577 : Blo 1370504 2197577 := bstep (se 2 (by rfl) ⟨824091, by rfl⟩ : syracuseStep 2197577 = 1648183) B1648183
theorem B11708651 : Blo 1370504 11708651 := bstep (se 1 (by rfl) ⟨8781488, by rfl⟩ : syracuseStep 11708651 = 17562977) B17562977
theorem B6941051 : Blo 1370504 6941051 := bstep (se 1 (by rfl) ⟨5205788, by rfl⟩ : syracuseStep 6941051 = 10411577) B10411577
theorem B2312759 : Blo 1370504 2312759 := bstep (se 1 (by rfl) ⟨1734569, by rfl⟩ : syracuseStep 2312759 = 3469139) B3469139
theorem B4393615 : Blo 1370504 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B7039943 : Blo 1370504 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B14076935 : Blo 1370504 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B1371227 : Blo 1370504 1371227 := bstep (se 1 (by rfl) ⟨1028420, by rfl⟩ : syracuseStep 1371227 = 2056841) B2056841
theorem B7810415 : Blo 1370504 7810415 := bstep (se 1 (by rfl) ⟨5857811, by rfl⟩ : syracuseStep 7810415 = 11715623) B11715623
theorem B3083687 : Blo 1370504 3083687 := bstep (se 1 (by rfl) ⟨2312765, by rfl⟩ : syracuseStep 3083687 = 4625531) B4625531
theorem B2313643 : Blo 1370504 2313643 := bstep (se 1 (by rfl) ⟨1735232, by rfl⟩ : syracuseStep 2313643 = 3470465) B3470465
theorem B1371583 : Blo 1370504 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B31682249 : Blo 1370504 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B17805091 : Blo 1370504 17805091 := bstep (se 1 (by rfl) ⟨13353818, by rfl⟩ : syracuseStep 17805091 = 26707637) B26707637
theorem B375828281 : Blo 1370504 375828281 := bstep (se 2 (by rfl) ⟨140935605, by rfl⟩ : syracuseStep 375828281 = 281871211) B281871211
theorem B3903329 : Blo 1370504 3903329 := bstep (se 2 (by rfl) ⟨1463748, by rfl⟩ : syracuseStep 3903329 = 2927497) B2927497
theorem B8785999 : Blo 1370504 8785999 := bstep (se 1 (by rfl) ⟨6589499, by rfl⟩ : syracuseStep 8785999 = 13178999) B13178999
theorem B47493539 : Blo 1370504 47493539 := bstep (se 1 (by rfl) ⟨35620154, by rfl⟩ : syracuseStep 47493539 = 71240309) B71240309
theorem B8024573 : Blo 1370504 8024573 := bstep (se 3 (by rfl) ⟨1504607, by rfl⟩ : syracuseStep 8024573 = 3009215) B3009215
theorem B3469979 : Blo 1370504 3469979 := bstep (se 1 (by rfl) ⟨2602484, by rfl⟩ : syracuseStep 3469979 = 5204969) B5204969
theorem B10416923 : Blo 1370504 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B22238009 : Blo 1370504 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B2315135 : Blo 1370504 2315135 := bstep (se 1 (by rfl) ⟨1736351, by rfl⟩ : syracuseStep 2315135 = 3472703) B3472703
theorem B14070847 : Blo 1370504 14070847 := bstep (se 1 (by rfl) ⟨10553135, by rfl⟩ : syracuseStep 14070847 = 21106271) B21106271
theorem B4625693 : Blo 1370504 4625693 := bstep (se 3 (by rfl) ⟨867317, by rfl⟩ : syracuseStep 4625693 = 1734635) B1734635
theorem B16684343 : Blo 1370504 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B8787487 : Blo 1370504 8787487 := bstep (se 1 (by rfl) ⟨6590615, by rfl⟩ : syracuseStep 8787487 = 13181231) B13181231
theorem B4691519 : Blo 1370504 4691519 := bstep (se 1 (by rfl) ⟨3518639, by rfl⟩ : syracuseStep 4691519 = 7037279) B7037279
theorem B3470951 : Blo 1370504 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B7812875 : Blo 1370504 7812875 := bstep (se 1 (by rfl) ⟨5859656, by rfl⟩ : syracuseStep 7812875 = 11719313) B11719313
theorem B3086315 : Blo 1370504 3086315 := bstep (se 1 (by rfl) ⟨2314736, by rfl⟩ : syracuseStep 3086315 = 4629473) B4629473
theorem B4626503 : Blo 1370504 4626503 := bstep (se 1 (by rfl) ⟨3469877, by rfl⟩ : syracuseStep 4626503 = 6939755) B6939755
theorem B3086585 : Blo 1370504 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B3086729 : Blo 1370504 3086729 := bstep (se 2 (by rfl) ⟨1157523, by rfl⟩ : syracuseStep 3086729 = 2315047) B2315047
theorem B7412411 : Blo 1370504 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B1563355 : Blo 1370504 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B4340911 : Blo 1370504 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B13172543 : Blo 1370504 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B11714665 : Blo 1370504 11714665 := bstep (se 2 (by rfl) ⟨4392999, by rfl⟩ : syracuseStep 11714665 = 8785999) B8785999
theorem B31662359 : Blo 1370504 31662359 := bstep (se 1 (by rfl) ⟨23746769, by rfl⟩ : syracuseStep 31662359 = 47493539) B47493539
theorem B5349715 : Blo 1370504 5349715 := bstep (se 1 (by rfl) ⟨4012286, by rfl⟩ : syracuseStep 5349715 = 8024573) B8024573
theorem B5858153 : Blo 1370504 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B2057543 : Blo 1370504 2057543 := bstep (se 1 (by rfl) ⟨1543157, by rfl⟩ : syracuseStep 2057543 = 3086315) B3086315
theorem B18761129 : Blo 1370504 18761129 := bstep (se 2 (by rfl) ⟨7035423, by rfl⟩ : syracuseStep 18761129 = 14070847) B14070847
theorem B2057723 : Blo 1370504 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B2057819 : Blo 1370504 2057819 := bstep (se 1 (by rfl) ⟨1543364, by rfl⟩ : syracuseStep 2057819 = 3086729) B3086729
theorem B1541839 : Blo 1370504 1541839 := bstep (se 1 (by rfl) ⟨1156379, by rfl⟩ : syracuseStep 1541839 = 2312759) B2312759
theorem B4941607 : Blo 1370504 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B11716649 : Blo 1370504 11716649 := bstep (se 2 (by rfl) ⟨4393743, by rfl⟩ : syracuseStep 11716649 = 8787487) B8787487
theorem B21121499 : Blo 1370504 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B1370875 : Blo 1370504 1370875 := bstep (se 1 (by rfl) ⟨1028156, by rfl⟩ : syracuseStep 1370875 = 2056313) B2056313
theorem B1370907 : Blo 1370504 1370907 := bstep (se 1 (by rfl) ⟨1028180, by rfl⟩ : syracuseStep 1370907 = 2056361) B2056361
theorem B7809959 : Blo 1370504 7809959 := bstep (se 1 (by rfl) ⟨5857469, by rfl⟩ : syracuseStep 7809959 = 11714939) B11714939
theorem B2313319 : Blo 1370504 2313319 := bstep (se 1 (by rfl) ⟨1734989, by rfl⟩ : syracuseStep 2313319 = 3469979) B3469979
theorem B1371387 : Blo 1370504 1371387 := bstep (se 1 (by rfl) ⟨1028540, by rfl⟩ : syracuseStep 1371387 = 2057081) B2057081
theorem B1543423 : Blo 1370504 1543423 := bstep (se 1 (by rfl) ⟨1157567, by rfl⟩ : syracuseStep 1543423 = 2315135) B2315135
theorem B1371419 : Blo 1370504 1371419 := bstep (se 1 (by rfl) ⟨1028564, by rfl⟩ : syracuseStep 1371419 = 2057129) B2057129
theorem B3083795 : Blo 1370504 3083795 := bstep (se 1 (by rfl) ⟨2312846, by rfl⟩ : syracuseStep 3083795 = 4625693) B4625693
theorem B1371759 : Blo 1370504 1371759 := bstep (se 1 (by rfl) ⟨1028819, by rfl⟩ : syracuseStep 1371759 = 2057639) B2057639
theorem B2084473 : Blo 1370504 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B1371803 : Blo 1370504 1371803 := bstep (se 1 (by rfl) ⟨1028852, by rfl⟩ : syracuseStep 1371803 = 2057705) B2057705
theorem B2313967 : Blo 1370504 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B3469351 : Blo 1370504 3469351 := bstep (se 1 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 3469351 = 5204027) B5204027
theorem B3084335 : Blo 1370504 3084335 := bstep (se 1 (by rfl) ⟨2313251, by rfl⟩ : syracuseStep 3084335 = 4626503) B4626503
theorem B5787881 : Blo 1370504 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B3084857 : Blo 1370504 3084857 := bstep (se 2 (by rfl) ⟨1156821, by rfl⟩ : syracuseStep 3084857 = 2313643) B2313643
theorem B9384623 : Blo 1370504 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B5206943 : Blo 1370504 5206943 := bstep (se 1 (by rfl) ⟨3905207, by rfl⟩ : syracuseStep 5206943 = 7810415) B7810415
theorem B2602219 : Blo 1370504 2602219 := bstep (se 1 (by rfl) ⟨1951664, by rfl⟩ : syracuseStep 2602219 = 3903329) B3903329
theorem B6944615 : Blo 1370504 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B14825339 : Blo 1370504 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B7411675 : Blo 1370504 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B11122895 : Blo 1370504 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B3127679 : Blo 1370504 3127679 := bstep (se 1 (by rfl) ⟨2345759, by rfl⟩ : syracuseStep 3127679 = 4691519) B4691519
theorem B5208583 : Blo 1370504 5208583 := bstep (se 1 (by rfl) ⟨3906437, by rfl⟩ : syracuseStep 5208583 = 7812875) B7812875
theorem B1465051 : Blo 1370504 1465051 := bstep (se 1 (by rfl) ⟨1098788, by rfl⟩ : syracuseStep 1465051 = 2197577) B2197577
theorem B7805767 : Blo 1370504 7805767 := bstep (se 1 (by rfl) ⟨5854325, by rfl⟩ : syracuseStep 7805767 = 11708651) B11708651
theorem B4627367 : Blo 1370504 4627367 := bstep (se 1 (by rfl) ⟨3470525, by rfl⟩ : syracuseStep 4627367 = 6941051) B6941051
theorem B4693295 : Blo 1370504 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B2055791 : Blo 1370504 2055791 := bstep (se 1 (by rfl) ⟨1541843, by rfl⟩ : syracuseStep 2055791 = 3083687) B3083687
theorem B23740121 : Blo 1370504 23740121 := bstep (se 2 (by rfl) ⟨8902545, by rfl⟩ : syracuseStep 23740121 = 17805091) B17805091
theorem B250552187 : Blo 1370504 250552187 := bstep (se 1 (by rfl) ⟨187914140, by rfl⟩ : syracuseStep 250552187 = 375828281) B375828281
theorem B8781695 : Blo 1370504 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B2056223 : Blo 1370504 2056223 := bstep (se 1 (by rfl) ⟨1542167, by rfl⟩ : syracuseStep 2056223 = 3084335) B3084335
theorem B3858587 : Blo 1370504 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B2056571 : Blo 1370504 2056571 := bstep (se 1 (by rfl) ⟨1542428, by rfl⟩ : syracuseStep 2056571 = 3084857) B3084857
theorem B11117189 : Blo 1370504 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B4629743 : Blo 1370504 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B7415263 : Blo 1370504 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B2057897 : Blo 1370504 2057897 := bstep (se 2 (by rfl) ⟨771711, by rfl⟩ : syracuseStep 2057897 = 1543423) B1543423
theorem B6588809 : Blo 1370504 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B1370527 : Blo 1370504 1370527 := bstep (se 1 (by rfl) ⟨1027895, by rfl⟩ : syracuseStep 1370527 = 2055791) B2055791
theorem B9882233 : Blo 1370504 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B1371695 : Blo 1370504 1371695 := bstep (se 1 (by rfl) ⟨1028771, by rfl⟩ : syracuseStep 1371695 = 2057543) B2057543
theorem B1953401 : Blo 1370504 1953401 := bstep (se 2 (by rfl) ⟨732525, by rfl⟩ : syracuseStep 1953401 = 1465051) B1465051
theorem B1371815 : Blo 1370504 1371815 := bstep (se 1 (by rfl) ⟨1028861, by rfl⟩ : syracuseStep 1371815 = 2057723) B2057723
theorem B1371879 : Blo 1370504 1371879 := bstep (se 1 (by rfl) ⟨1028909, by rfl⟩ : syracuseStep 1371879 = 2057819) B2057819
theorem B10407689 : Blo 1370504 10407689 := bstep (se 2 (by rfl) ⟨3902883, by rfl⟩ : syracuseStep 10407689 = 7805767) B7805767
theorem B9883559 : Blo 1370504 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B7811099 : Blo 1370504 7811099 := bstep (se 1 (by rfl) ⟨5858324, by rfl⟩ : syracuseStep 7811099 = 11716649) B11716649
theorem B3084425 : Blo 1370504 3084425 := bstep (se 2 (by rfl) ⟨1156659, by rfl⟩ : syracuseStep 3084425 = 2313319) B2313319
theorem B2085119 : Blo 1370504 2085119 := bstep (se 1 (by rfl) ⟨1563839, by rfl⟩ : syracuseStep 2085119 = 3127679) B3127679
theorem B3469625 : Blo 1370504 3469625 := bstep (se 2 (by rfl) ⟨1301109, by rfl⟩ : syracuseStep 3469625 = 2602219) B2602219
theorem B3084911 : Blo 1370504 3084911 := bstep (se 1 (by rfl) ⟨2313683, by rfl⟩ : syracuseStep 3084911 = 4627367) B4627367
theorem B5206639 : Blo 1370504 5206639 := bstep (se 1 (by rfl) ⟨3904979, by rfl⟩ : syracuseStep 5206639 = 7809959) B7809959
theorem B3085289 : Blo 1370504 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B5854463 : Blo 1370504 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B4625801 : Blo 1370504 4625801 := bstep (se 2 (by rfl) ⟨1734675, by rfl⟩ : syracuseStep 4625801 = 3469351) B3469351
theorem B15619553 : Blo 1370504 15619553 := bstep (se 2 (by rfl) ⟨5857332, by rfl⟩ : syracuseStep 15619553 = 11714665) B11714665
theorem B21108239 : Blo 1370504 21108239 := bstep (se 1 (by rfl) ⟨15831179, by rfl⟩ : syracuseStep 21108239 = 31662359) B31662359
theorem B6256415 : Blo 1370504 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B3905435 : Blo 1370504 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B3471295 : Blo 1370504 3471295 := bstep (se 1 (by rfl) ⟨2603471, by rfl⟩ : syracuseStep 3471295 = 5206943) B5206943
theorem B6944777 : Blo 1370504 6944777 := bstep (se 2 (by rfl) ⟨2604291, by rfl⟩ : syracuseStep 6944777 = 5208583) B5208583
theorem B12507419 : Blo 1370504 12507419 := bstep (se 1 (by rfl) ⟨9380564, by rfl⟩ : syracuseStep 12507419 = 18761129) B18761129
theorem B14080999 : Blo 1370504 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B28531813 : Blo 1370504 28531813 := bstep (se 4 (by rfl) ⟨2674857, by rfl⟩ : syracuseStep 28531813 = 5349715) B5349715
theorem B3128863 : Blo 1370504 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B2055785 : Blo 1370504 2055785 := bstep (se 2 (by rfl) ⟨770919, by rfl⟩ : syracuseStep 2055785 = 1541839) B1541839
theorem B2055863 : Blo 1370504 2055863 := bstep (se 1 (by rfl) ⟨1541897, by rfl⟩ : syracuseStep 2055863 = 3083795) B3083795
theorem B15826747 : Blo 1370504 15826747 := bstep (se 1 (by rfl) ⟨11870060, by rfl⟩ : syracuseStep 15826747 = 23740121) B23740121
theorem B167034791 : Blo 1370504 167034791 := bstep (se 1 (by rfl) ⟨125276093, by rfl⟩ : syracuseStep 167034791 = 250552187) B250552187
theorem B2056283 : Blo 1370504 2056283 := bstep (se 1 (by rfl) ⟨1542212, by rfl⟩ : syracuseStep 2056283 = 3084425) B3084425
theorem B2572391 : Blo 1370504 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B2056607 : Blo 1370504 2056607 := bstep (se 1 (by rfl) ⟨1542455, by rfl⟩ : syracuseStep 2056607 = 3084911) B3084911
theorem B2056859 : Blo 1370504 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B10413035 : Blo 1370504 10413035 := bstep (se 1 (by rfl) ⟨7809776, by rfl⟩ : syracuseStep 10413035 = 15619553) B15619553
theorem B4170943 : Blo 1370504 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B4629851 : Blo 1370504 4629851 := bstep (se 1 (by rfl) ⟨3472388, by rfl⟩ : syracuseStep 4629851 = 6944777) B6944777
theorem B4392539 : Blo 1370504 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B6588155 : Blo 1370504 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B4171817 : Blo 1370504 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B1370523 : Blo 1370504 1370523 := bstep (se 1 (by rfl) ⟨1027892, by rfl⟩ : syracuseStep 1370523 = 2055785) B2055785
theorem B10414493 : Blo 1370504 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B1370575 : Blo 1370504 1370575 := bstep (se 1 (by rfl) ⟨1027931, by rfl⟩ : syracuseStep 1370575 = 2055863) B2055863
theorem B6589039 : Blo 1370504 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B111356527 : Blo 1370504 111356527 := bstep (se 1 (by rfl) ⟨83517395, by rfl⟩ : syracuseStep 111356527 = 167034791) B167034791
theorem B1370815 : Blo 1370504 1370815 := bstep (se 1 (by rfl) ⟨1028111, by rfl⟩ : syracuseStep 1370815 = 2056223) B2056223
theorem B2313083 : Blo 1370504 2313083 := bstep (se 1 (by rfl) ⟨1734812, by rfl⟩ : syracuseStep 2313083 = 3469625) B3469625
theorem B1371047 : Blo 1370504 1371047 := bstep (se 1 (by rfl) ⟨1028285, by rfl⟩ : syracuseStep 1371047 = 2056571) B2056571
theorem B33353117 : Blo 1370504 33353117 := bstep (se 3 (by rfl) ⟨6253709, by rfl⟩ : syracuseStep 33353117 = 12507419) B12507419
theorem B6942185 : Blo 1370504 6942185 := bstep (se 2 (by rfl) ⟨2603319, by rfl⟩ : syracuseStep 6942185 = 5206639) B5206639
theorem B3902975 : Blo 1370504 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B3083867 : Blo 1370504 3083867 := bstep (se 1 (by rfl) ⟨2312900, by rfl⟩ : syracuseStep 3083867 = 4625801) B4625801
theorem B1371931 : Blo 1370504 1371931 := bstep (se 1 (by rfl) ⟨1028948, by rfl⟩ : syracuseStep 1371931 = 2057897) B2057897
theorem B5207399 : Blo 1370504 5207399 := bstep (se 1 (by rfl) ⟨3905549, by rfl⟩ : syracuseStep 5207399 = 7811099) B7811099
theorem B1390079 : Blo 1370504 1390079 := bstep (se 1 (by rfl) ⟨1042559, by rfl⟩ : syracuseStep 1390079 = 2085119) B2085119
theorem B7411459 : Blo 1370504 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B3086495 : Blo 1370504 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B14072159 : Blo 1370504 14072159 := bstep (se 1 (by rfl) ⟨10554119, by rfl⟩ : syracuseStep 14072159 = 21108239) B21108239
theorem B18774665 : Blo 1370504 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B38042417 : Blo 1370504 38042417 := bstep (se 2 (by rfl) ⟨14265906, by rfl⟩ : syracuseStep 38042417 = 28531813) B28531813
theorem B5209069 : Blo 1370504 5209069 := bstep (se 3 (by rfl) ⟨976700, by rfl⟩ : syracuseStep 5209069 = 1953401) B1953401
theorem B9887017 : Blo 1370504 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B21102329 : Blo 1370504 21102329 := bstep (se 2 (by rfl) ⟨7913373, by rfl⟩ : syracuseStep 21102329 = 15826747) B15826747
theorem B6938459 : Blo 1370504 6938459 := bstep (se 1 (by rfl) ⟨5203844, by rfl⟩ : syracuseStep 6938459 = 10407689) B10407689
theorem B4628393 : Blo 1370504 4628393 := bstep (se 2 (by rfl) ⟨1735647, by rfl⟩ : syracuseStep 4628393 = 3471295) B3471295
theorem B2057663 : Blo 1370504 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B9381439 : Blo 1370504 9381439 := bstep (se 1 (by rfl) ⟨7036079, by rfl⟩ : syracuseStep 9381439 = 14072159) B14072159
theorem B13182689 : Blo 1370504 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B1542055 : Blo 1370504 1542055 := bstep (se 1 (by rfl) ⟨1156541, by rfl⟩ : syracuseStep 1542055 = 2313083) B2313083
theorem B56272877 : Blo 1370504 56272877 := bstep (se 3 (by rfl) ⟨10551164, by rfl⟩ : syracuseStep 56272877 = 21102329) B21102329
theorem B22235411 : Blo 1370504 22235411 := bstep (se 1 (by rfl) ⟨16676558, by rfl⟩ : syracuseStep 22235411 = 33353117) B33353117
theorem B9881945 : Blo 1370504 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B1370855 : Blo 1370504 1370855 := bstep (se 1 (by rfl) ⟨1028141, by rfl⟩ : syracuseStep 1370855 = 2056283) B2056283
theorem B1714927 : Blo 1370504 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B1371071 : Blo 1370504 1371071 := bstep (se 1 (by rfl) ⟨1028303, by rfl⟩ : syracuseStep 1371071 = 2056607) B2056607
theorem B1371239 : Blo 1370504 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B6942023 : Blo 1370504 6942023 := bstep (se 1 (by rfl) ⟨5206517, by rfl⟩ : syracuseStep 6942023 = 10413035) B10413035
theorem B8785385 : Blo 1370504 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B148475369 : Blo 1370504 148475369 := bstep (se 2 (by rfl) ⟨55678263, by rfl⟩ : syracuseStep 148475369 = 111356527) B111356527
theorem B2928359 : Blo 1370504 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B3706877 : Blo 1370504 3706877 := bstep (se 3 (by rfl) ⟨695039, by rfl⟩ : syracuseStep 3706877 = 1390079) B1390079
theorem B2781211 : Blo 1370504 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B6942995 : Blo 1370504 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B17568413 : Blo 1370504 17568413 := bstep (se 3 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 17568413 = 6588155) B6588155
theorem B101446445 : Blo 1370504 101446445 := bstep (se 3 (by rfl) ⟨19021208, by rfl⟩ : syracuseStep 101446445 = 38042417) B38042417
theorem B2601983 : Blo 1370504 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B4625639 : Blo 1370504 4625639 := bstep (se 1 (by rfl) ⟨3469229, by rfl⟩ : syracuseStep 4625639 = 6938459) B6938459
theorem B3085595 : Blo 1370504 3085595 := bstep (se 1 (by rfl) ⟨2314196, by rfl⟩ : syracuseStep 3085595 = 4628393) B4628393
theorem B3086567 : Blo 1370504 3086567 := bstep (se 1 (by rfl) ⟨2314925, by rfl⟩ : syracuseStep 3086567 = 4629851) B4629851
theorem B3471599 : Blo 1370504 3471599 := bstep (se 1 (by rfl) ⟨2603699, by rfl⟩ : syracuseStep 3471599 = 5207399) B5207399
theorem B6945425 : Blo 1370504 6945425 := bstep (se 2 (by rfl) ⟨2604534, by rfl⟩ : syracuseStep 6945425 = 5209069) B5209069
theorem B5561257 : Blo 1370504 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B12516443 : Blo 1370504 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B4628123 : Blo 1370504 4628123 := bstep (se 1 (by rfl) ⟨3471092, by rfl⟩ : syracuseStep 4628123 = 6942185) B6942185
theorem B2055911 : Blo 1370504 2055911 := bstep (se 1 (by rfl) ⟨1541933, by rfl⟩ : syracuseStep 2055911 = 3083867) B3083867
theorem B4628663 : Blo 1370504 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B2057063 : Blo 1370504 2057063 := bstep (se 1 (by rfl) ⟨1542797, by rfl⟩ : syracuseStep 2057063 = 3085595) B3085595
theorem B2286569 : Blo 1370504 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B7415009 : Blo 1370504 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B2057711 : Blo 1370504 2057711 := bstep (se 1 (by rfl) ⟨1543283, by rfl⟩ : syracuseStep 2057711 = 3086567) B3086567
theorem B6587963 : Blo 1370504 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B4630283 : Blo 1370504 4630283 := bstep (se 1 (by rfl) ⟨3472712, by rfl⟩ : syracuseStep 4630283 = 6945425) B6945425
theorem B35153837 : Blo 1370504 35153837 := bstep (se 3 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 35153837 = 13182689) B13182689
theorem B7808957 : Blo 1370504 7808957 := bstep (se 3 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 7808957 = 2928359) B2928359
theorem B1370607 : Blo 1370504 1370607 := bstep (se 1 (by rfl) ⟨1027955, by rfl⟩ : syracuseStep 1370607 = 2055911) B2055911
theorem B3083759 : Blo 1370504 3083759 := bstep (se 1 (by rfl) ⟨2312819, by rfl⟩ : syracuseStep 3083759 = 4625639) B4625639
theorem B1371775 : Blo 1370504 1371775 := bstep (se 1 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 1371775 = 2057663) B2057663
theorem B37515251 : Blo 1370504 37515251 := bstep (se 1 (by rfl) ⟨28136438, by rfl⟩ : syracuseStep 37515251 = 56272877) B56272877
theorem B2314399 : Blo 1370504 2314399 := bstep (se 1 (by rfl) ⟨1735799, by rfl⟩ : syracuseStep 2314399 = 3471599) B3471599
theorem B14823607 : Blo 1370504 14823607 := bstep (se 1 (by rfl) ⟨11117705, by rfl⟩ : syracuseStep 14823607 = 22235411) B22235411
theorem B8344295 : Blo 1370504 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B3085415 : Blo 1370504 3085415 := bstep (se 1 (by rfl) ⟨2314061, by rfl⟩ : syracuseStep 3085415 = 4628123) B4628123
theorem B2471251 : Blo 1370504 2471251 := bstep (se 1 (by rfl) ⟨1853438, by rfl⟩ : syracuseStep 2471251 = 3706877) B3706877
theorem B3708281 : Blo 1370504 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B50034341 : Blo 1370504 50034341 := bstep (se 4 (by rfl) ⟨4690719, by rfl⟩ : syracuseStep 50034341 = 9381439) B9381439
theorem B11712275 : Blo 1370504 11712275 := bstep (se 1 (by rfl) ⟨8784206, by rfl⟩ : syracuseStep 11712275 = 17568413) B17568413
theorem B67630963 : Blo 1370504 67630963 := bstep (se 1 (by rfl) ⟨50723222, by rfl⟩ : syracuseStep 67630963 = 101446445) B101446445
theorem B4628015 : Blo 1370504 4628015 := bstep (se 1 (by rfl) ⟨3471011, by rfl⟩ : syracuseStep 4628015 = 6942023) B6942023
theorem B5856923 : Blo 1370504 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B98983579 : Blo 1370504 98983579 := bstep (se 1 (by rfl) ⟨74237684, by rfl⟩ : syracuseStep 98983579 = 148475369) B148475369
theorem B2056073 : Blo 1370504 2056073 := bstep (se 2 (by rfl) ⟨771027, by rfl⟩ : syracuseStep 2056073 = 1542055) B1542055
theorem B6938621 : Blo 1370504 6938621 := bstep (se 3 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 6938621 = 2601983) B2601983
theorem B5562863 : Blo 1370504 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B2056943 : Blo 1370504 2056943 := bstep (se 1 (by rfl) ⟨1542707, by rfl⟩ : syracuseStep 2056943 = 3085415) B3085415
theorem B9888749 : Blo 1370504 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B4391975 : Blo 1370504 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B7808183 : Blo 1370504 7808183 := bstep (se 1 (by rfl) ⟨5856137, by rfl⟩ : syracuseStep 7808183 = 11712275) B11712275
theorem B3295001 : Blo 1370504 3295001 := bstep (se 2 (by rfl) ⟨1235625, by rfl⟩ : syracuseStep 3295001 = 2471251) B2471251
theorem B1370715 : Blo 1370504 1370715 := bstep (se 1 (by rfl) ⟨1028036, by rfl⟩ : syracuseStep 1370715 = 2056073) B2056073
theorem B6097517 : Blo 1370504 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B1371375 : Blo 1370504 1371375 := bstep (se 1 (by rfl) ⟨1028531, by rfl⟩ : syracuseStep 1371375 = 2057063) B2057063
theorem B4943339 : Blo 1370504 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1371807 : Blo 1370504 1371807 := bstep (se 1 (by rfl) ⟨1028855, by rfl⟩ : syracuseStep 1371807 = 2057711) B2057711
theorem B5205971 : Blo 1370504 5205971 := bstep (se 1 (by rfl) ⟨3904478, by rfl⟩ : syracuseStep 5205971 = 7808957) B7808957
theorem B131978105 : Blo 1370504 131978105 := bstep (se 2 (by rfl) ⟨49491789, by rfl⟩ : syracuseStep 131978105 = 98983579) B98983579
theorem B3085343 : Blo 1370504 3085343 := bstep (se 1 (by rfl) ⟨2314007, by rfl⟩ : syracuseStep 3085343 = 4628015) B4628015
theorem B3904615 : Blo 1370504 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B90174617 : Blo 1370504 90174617 := bstep (se 2 (by rfl) ⟨33815481, by rfl⟩ : syracuseStep 90174617 = 67630963) B67630963
theorem B4625747 : Blo 1370504 4625747 := bstep (se 1 (by rfl) ⟨3469310, by rfl⟩ : syracuseStep 4625747 = 6938621) B6938621
theorem B3085775 : Blo 1370504 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B3085865 : Blo 1370504 3085865 := bstep (se 2 (by rfl) ⟨1157199, by rfl⟩ : syracuseStep 3085865 = 2314399) B2314399
theorem B19764809 : Blo 1370504 19764809 := bstep (se 2 (by rfl) ⟨7411803, by rfl⟩ : syracuseStep 19764809 = 14823607) B14823607
theorem B33356227 : Blo 1370504 33356227 := bstep (se 1 (by rfl) ⟨25017170, by rfl⟩ : syracuseStep 33356227 = 50034341) B50034341
theorem B3086855 : Blo 1370504 3086855 := bstep (se 1 (by rfl) ⟨2315141, by rfl⟩ : syracuseStep 3086855 = 4630283) B4630283
theorem B23435891 : Blo 1370504 23435891 := bstep (se 1 (by rfl) ⟨17576918, by rfl⟩ : syracuseStep 23435891 = 35153837) B35153837
theorem B2055839 : Blo 1370504 2055839 := bstep (se 1 (by rfl) ⟨1541879, by rfl⟩ : syracuseStep 2055839 = 3083759) B3083759
theorem B25010167 : Blo 1370504 25010167 := bstep (se 1 (by rfl) ⟨18757625, by rfl⟩ : syracuseStep 25010167 = 37515251) B37515251
theorem B44474969 : Blo 1370504 44474969 := bstep (se 2 (by rfl) ⟨16678113, by rfl⟩ : syracuseStep 44474969 = 33356227) B33356227
theorem B2056895 : Blo 1370504 2056895 := bstep (se 1 (by rfl) ⟨1542671, by rfl⟩ : syracuseStep 2056895 = 3085343) B3085343
theorem B2057183 : Blo 1370504 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B2057243 : Blo 1370504 2057243 := bstep (se 1 (by rfl) ⟨1542932, by rfl⟩ : syracuseStep 2057243 = 3085865) B3085865
theorem B2196667 : Blo 1370504 2196667 := bstep (se 1 (by rfl) ⟨1647500, by rfl⟩ : syracuseStep 2196667 = 3295001) B3295001
theorem B2057903 : Blo 1370504 2057903 := bstep (se 1 (by rfl) ⟨1543427, by rfl⟩ : syracuseStep 2057903 = 3086855) B3086855
theorem B4065011 : Blo 1370504 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B15623927 : Blo 1370504 15623927 := bstep (se 1 (by rfl) ⟨11717945, by rfl⟩ : syracuseStep 15623927 = 23435891) B23435891
theorem B3295559 : Blo 1370504 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B1370559 : Blo 1370504 1370559 := bstep (se 1 (by rfl) ⟨1027919, by rfl⟩ : syracuseStep 1370559 = 2055839) B2055839
theorem B1371295 : Blo 1370504 1371295 := bstep (se 1 (by rfl) ⟨1028471, by rfl⟩ : syracuseStep 1371295 = 2056943) B2056943
theorem B87985403 : Blo 1370504 87985403 := bstep (se 1 (by rfl) ⟨65989052, by rfl⟩ : syracuseStep 87985403 = 131978105) B131978105
theorem B2927983 : Blo 1370504 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B60116411 : Blo 1370504 60116411 := bstep (se 1 (by rfl) ⟨45087308, by rfl⟩ : syracuseStep 60116411 = 90174617) B90174617
theorem B5205455 : Blo 1370504 5205455 := bstep (se 1 (by rfl) ⟨3904091, by rfl⟩ : syracuseStep 5205455 = 7808183) B7808183
theorem B3083831 : Blo 1370504 3083831 := bstep (se 1 (by rfl) ⟨2312873, by rfl⟩ : syracuseStep 3083831 = 4625747) B4625747
theorem B13176539 : Blo 1370504 13176539 := bstep (se 1 (by rfl) ⟨9882404, by rfl⟩ : syracuseStep 13176539 = 19764809) B19764809
theorem B5206153 : Blo 1370504 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B3470647 : Blo 1370504 3470647 := bstep (se 1 (by rfl) ⟨2602985, by rfl⟩ : syracuseStep 3470647 = 5205971) B5205971
theorem B33346889 : Blo 1370504 33346889 := bstep (se 2 (by rfl) ⟨12505083, by rfl⟩ : syracuseStep 33346889 = 25010167) B25010167
theorem B3708575 : Blo 1370504 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B6592499 : Blo 1370504 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B2197039 : Blo 1370504 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B58656935 : Blo 1370504 58656935 := bstep (se 1 (by rfl) ⟨43992701, by rfl⟩ : syracuseStep 58656935 = 87985403) B87985403
theorem B40077607 : Blo 1370504 40077607 := bstep (se 1 (by rfl) ⟨30058205, by rfl⟩ : syracuseStep 40077607 = 60116411) B60116411
theorem B8784359 : Blo 1370504 8784359 := bstep (se 1 (by rfl) ⟨6588269, by rfl⟩ : syracuseStep 8784359 = 13176539) B13176539
theorem B6941537 : Blo 1370504 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B29649979 : Blo 1370504 29649979 := bstep (se 1 (by rfl) ⟨22237484, by rfl⟩ : syracuseStep 29649979 = 44474969) B44474969
theorem B1371263 : Blo 1370504 1371263 := bstep (se 1 (by rfl) ⟨1028447, by rfl⟩ : syracuseStep 1371263 = 2056895) B2056895
theorem B1371455 : Blo 1370504 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B1371495 : Blo 1370504 1371495 := bstep (se 1 (by rfl) ⟨1028621, by rfl⟩ : syracuseStep 1371495 = 2057243) B2057243
theorem B1371935 : Blo 1370504 1371935 := bstep (se 1 (by rfl) ⟨1028951, by rfl⟩ : syracuseStep 1371935 = 2057903) B2057903
theorem B10415951 : Blo 1370504 10415951 := bstep (se 1 (by rfl) ⟨7811963, by rfl⟩ : syracuseStep 10415951 = 15623927) B15623927
theorem B4394999 : Blo 1370504 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B2928889 : Blo 1370504 2928889 := bstep (se 2 (by rfl) ⟨1098333, by rfl⟩ : syracuseStep 2928889 = 2196667) B2196667
theorem B3903977 : Blo 1370504 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B3470303 : Blo 1370504 3470303 := bstep (se 1 (by rfl) ⟨2602727, by rfl⟩ : syracuseStep 3470303 = 5205455) B5205455
theorem B22231259 : Blo 1370504 22231259 := bstep (se 1 (by rfl) ⟨16673444, by rfl⟩ : syracuseStep 22231259 = 33346889) B33346889
theorem B2472383 : Blo 1370504 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B2710007 : Blo 1370504 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B4627529 : Blo 1370504 4627529 := bstep (se 2 (by rfl) ⟨1735323, by rfl⟩ : syracuseStep 4627529 = 3470647) B3470647
theorem B2055887 : Blo 1370504 2055887 := bstep (se 1 (by rfl) ⟨1541915, by rfl⟩ : syracuseStep 2055887 = 3083831) B3083831
theorem B53436809 : Blo 1370504 53436809 := bstep (se 2 (by rfl) ⟨20038803, by rfl⟩ : syracuseStep 53436809 = 40077607) B40077607
theorem B14820839 : Blo 1370504 14820839 := bstep (se 1 (by rfl) ⟨11115629, by rfl⟩ : syracuseStep 14820839 = 22231259) B22231259
theorem B1370591 : Blo 1370504 1370591 := bstep (se 1 (by rfl) ⟨1027943, by rfl⟩ : syracuseStep 1370591 = 2055887) B2055887
theorem B2313535 : Blo 1370504 2313535 := bstep (se 1 (by rfl) ⟨1735151, by rfl⟩ : syracuseStep 2313535 = 3470303) B3470303
theorem B39104623 : Blo 1370504 39104623 := bstep (se 1 (by rfl) ⟨29328467, by rfl⟩ : syracuseStep 39104623 = 58656935) B58656935
theorem B1806671 : Blo 1370504 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B3085019 : Blo 1370504 3085019 := bstep (se 1 (by rfl) ⟨2313764, by rfl⟩ : syracuseStep 3085019 = 4627529) B4627529
theorem B2929385 : Blo 1370504 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B6943967 : Blo 1370504 6943967 := bstep (se 1 (by rfl) ⟨5207975, by rfl⟩ : syracuseStep 6943967 = 10415951) B10415951
theorem B11719997 : Blo 1370504 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B3905185 : Blo 1370504 3905185 := bstep (se 2 (by rfl) ⟨1464444, by rfl⟩ : syracuseStep 3905185 = 2928889) B2928889
theorem B6593021 : Blo 1370504 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B10410605 : Blo 1370504 10410605 := bstep (se 3 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 10410605 = 3903977) B3903977
theorem B39533305 : Blo 1370504 39533305 := bstep (se 2 (by rfl) ⟨14824989, by rfl⟩ : syracuseStep 39533305 = 29649979) B29649979
theorem B5856239 : Blo 1370504 5856239 := bstep (se 1 (by rfl) ⟨4392179, by rfl⟩ : syracuseStep 5856239 = 8784359) B8784359
theorem B4627691 : Blo 1370504 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B2056679 : Blo 1370504 2056679 := bstep (se 1 (by rfl) ⟨1542509, by rfl⟩ : syracuseStep 2056679 = 3085019) B3085019
theorem B4629311 : Blo 1370504 4629311 := bstep (se 1 (by rfl) ⟨3471983, by rfl⟩ : syracuseStep 4629311 = 6943967) B6943967
theorem B4817789 : Blo 1370504 4817789 := bstep (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) B1806671
theorem B9880559 : Blo 1370504 9880559 := bstep (se 1 (by rfl) ⟨7410419, by rfl⟩ : syracuseStep 9880559 = 14820839) B14820839
theorem B6940403 : Blo 1370504 6940403 := bstep (se 1 (by rfl) ⟨5205302, by rfl⟩ : syracuseStep 6940403 = 10410605) B10410605
theorem B15616637 : Blo 1370504 15616637 := bstep (se 3 (by rfl) ⟨2928119, by rfl⟩ : syracuseStep 15616637 = 5856239) B5856239
theorem B1952923 : Blo 1370504 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B52711073 : Blo 1370504 52711073 := bstep (se 2 (by rfl) ⟨19766652, by rfl⟩ : syracuseStep 52711073 = 39533305) B39533305
theorem B4395347 : Blo 1370504 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B3084713 : Blo 1370504 3084713 := bstep (se 2 (by rfl) ⟨1156767, by rfl⟩ : syracuseStep 3084713 = 2313535) B2313535
theorem B3085127 : Blo 1370504 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B5206913 : Blo 1370504 5206913 := bstep (se 2 (by rfl) ⟨1952592, by rfl⟩ : syracuseStep 5206913 = 3905185) B3905185
theorem B52139497 : Blo 1370504 52139497 := bstep (se 2 (by rfl) ⟨19552311, by rfl⟩ : syracuseStep 52139497 = 39104623) B39104623
theorem B35624539 : Blo 1370504 35624539 := bstep (se 1 (by rfl) ⟨26718404, by rfl⟩ : syracuseStep 35624539 = 53436809) B53436809
theorem B7813331 : Blo 1370504 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B2056475 : Blo 1370504 2056475 := bstep (se 1 (by rfl) ⟨1542356, by rfl⟩ : syracuseStep 2056475 = 3084713) B3084713
theorem B2056751 : Blo 1370504 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B3211859 : Blo 1370504 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B6587039 : Blo 1370504 6587039 := bstep (se 1 (by rfl) ⟨4940279, by rfl⟩ : syracuseStep 6587039 = 9880559) B9880559
theorem B69519329 : Blo 1370504 69519329 := bstep (se 2 (by rfl) ⟨26069748, by rfl⟩ : syracuseStep 69519329 = 52139497) B52139497
theorem B47499385 : Blo 1370504 47499385 := bstep (se 2 (by rfl) ⟨17812269, by rfl⟩ : syracuseStep 47499385 = 35624539) B35624539
theorem B1371119 : Blo 1370504 1371119 := bstep (se 1 (by rfl) ⟨1028339, by rfl⟩ : syracuseStep 1371119 = 2056679) B2056679
theorem B35140715 : Blo 1370504 35140715 := bstep (se 1 (by rfl) ⟨26355536, by rfl⟩ : syracuseStep 35140715 = 52711073) B52711073
theorem B2930231 : Blo 1370504 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B3086207 : Blo 1370504 3086207 := bstep (se 1 (by rfl) ⟨2314655, by rfl⟩ : syracuseStep 3086207 = 4629311) B4629311
theorem B3471275 : Blo 1370504 3471275 := bstep (se 1 (by rfl) ⟨2603456, by rfl⟩ : syracuseStep 3471275 = 5206913) B5206913
theorem B4626935 : Blo 1370504 4626935 := bstep (se 1 (by rfl) ⟨3470201, by rfl⟩ : syracuseStep 4626935 = 6940403) B6940403
theorem B5208887 : Blo 1370504 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B2603897 : Blo 1370504 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B10411091 : Blo 1370504 10411091 := bstep (se 1 (by rfl) ⟨7808318, by rfl⟩ : syracuseStep 10411091 = 15616637) B15616637
theorem B63332513 : Blo 1370504 63332513 := bstep (se 2 (by rfl) ⟨23749692, by rfl⟩ : syracuseStep 63332513 = 47499385) B47499385
theorem B2057471 : Blo 1370504 2057471 := bstep (se 1 (by rfl) ⟨1543103, by rfl⟩ : syracuseStep 2057471 = 3086207) B3086207
theorem B17565437 : Blo 1370504 17565437 := bstep (se 3 (by rfl) ⟨3293519, by rfl⟩ : syracuseStep 17565437 = 6587039) B6587039
theorem B6940727 : Blo 1370504 6940727 := bstep (se 1 (by rfl) ⟨5205545, by rfl⟩ : syracuseStep 6940727 = 10411091) B10411091
theorem B1370983 : Blo 1370504 1370983 := bstep (se 1 (by rfl) ⟨1028237, by rfl⟩ : syracuseStep 1370983 = 2056475) B2056475
theorem B1371167 : Blo 1370504 1371167 := bstep (se 1 (by rfl) ⟨1028375, by rfl⟩ : syracuseStep 1371167 = 2056751) B2056751
theorem B1953487 : Blo 1370504 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B2314183 : Blo 1370504 2314183 := bstep (se 1 (by rfl) ⟨1735637, by rfl⟩ : syracuseStep 2314183 = 3471275) B3471275
theorem B46346219 : Blo 1370504 46346219 := bstep (se 1 (by rfl) ⟨34759664, by rfl⟩ : syracuseStep 46346219 = 69519329) B69519329
theorem B8564957 : Blo 1370504 8564957 := bstep (se 3 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 8564957 = 3211859) B3211859
theorem B3084623 : Blo 1370504 3084623 := bstep (se 1 (by rfl) ⟨2313467, by rfl⟩ : syracuseStep 3084623 = 4626935) B4626935
theorem B23427143 : Blo 1370504 23427143 := bstep (se 1 (by rfl) ⟨17570357, by rfl⟩ : syracuseStep 23427143 = 35140715) B35140715
theorem B3472591 : Blo 1370504 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B1735931 : Blo 1370504 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B42221675 : Blo 1370504 42221675 := bstep (se 1 (by rfl) ⟨31666256, by rfl⟩ : syracuseStep 42221675 = 63332513) B63332513
theorem B5709971 : Blo 1370504 5709971 := bstep (se 1 (by rfl) ⟨4282478, by rfl⟩ : syracuseStep 5709971 = 8564957) B8564957
theorem B2056415 : Blo 1370504 2056415 := bstep (se 1 (by rfl) ⟨1542311, by rfl⟩ : syracuseStep 2056415 = 3084623) B3084623
theorem B4629149 : Blo 1370504 4629149 := bstep (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) B1735931
theorem B4630121 : Blo 1370504 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B1371647 : Blo 1370504 1371647 := bstep (se 1 (by rfl) ⟨1028735, by rfl⟩ : syracuseStep 1371647 = 2057471) B2057471
theorem B11710291 : Blo 1370504 11710291 := bstep (se 1 (by rfl) ⟨8782718, by rfl⟩ : syracuseStep 11710291 = 17565437) B17565437
theorem B15618095 : Blo 1370504 15618095 := bstep (se 1 (by rfl) ⟨11713571, by rfl⟩ : syracuseStep 15618095 = 23427143) B23427143
theorem B3085577 : Blo 1370504 3085577 := bstep (se 2 (by rfl) ⟨1157091, by rfl⟩ : syracuseStep 3085577 = 2314183) B2314183
theorem B30897479 : Blo 1370504 30897479 := bstep (se 1 (by rfl) ⟨23173109, by rfl⟩ : syracuseStep 30897479 = 46346219) B46346219
theorem B4627151 : Blo 1370504 4627151 := bstep (se 1 (by rfl) ⟨3470363, by rfl⟩ : syracuseStep 4627151 = 6940727) B6940727
theorem B2604649 : Blo 1370504 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B10412063 : Blo 1370504 10412063 := bstep (se 1 (by rfl) ⟨7809047, by rfl⟩ : syracuseStep 10412063 = 15618095) B15618095
theorem B28147783 : Blo 1370504 28147783 := bstep (se 1 (by rfl) ⟨21110837, by rfl⟩ : syracuseStep 28147783 = 42221675) B42221675
theorem B2057051 : Blo 1370504 2057051 := bstep (se 1 (by rfl) ⟨1542788, by rfl⟩ : syracuseStep 2057051 = 3085577) B3085577
theorem B1370943 : Blo 1370504 1370943 := bstep (se 1 (by rfl) ⟨1028207, by rfl⟩ : syracuseStep 1370943 = 2056415) B2056415
theorem B20598319 : Blo 1370504 20598319 := bstep (se 1 (by rfl) ⟨15448739, by rfl⟩ : syracuseStep 20598319 = 30897479) B30897479
theorem B3084767 : Blo 1370504 3084767 := bstep (se 1 (by rfl) ⟨2313575, by rfl⟩ : syracuseStep 3084767 = 4627151) B4627151
theorem B15226589 : Blo 1370504 15226589 := bstep (se 3 (by rfl) ⟨2854985, by rfl⟩ : syracuseStep 15226589 = 5709971) B5709971
theorem B3086099 : Blo 1370504 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B3086747 : Blo 1370504 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B3472865 : Blo 1370504 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B15613721 : Blo 1370504 15613721 := bstep (se 2 (by rfl) ⟨5855145, by rfl⟩ : syracuseStep 15613721 = 11710291) B11710291
theorem B2056511 : Blo 1370504 2056511 := bstep (se 1 (by rfl) ⟨1542383, by rfl⟩ : syracuseStep 2056511 = 3084767) B3084767
theorem B2057399 : Blo 1370504 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B2057831 : Blo 1370504 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B6941375 : Blo 1370504 6941375 := bstep (se 1 (by rfl) ⟨5206031, by rfl⟩ : syracuseStep 6941375 = 10412063) B10412063
theorem B37530377 : Blo 1370504 37530377 := bstep (se 2 (by rfl) ⟨14073891, by rfl⟩ : syracuseStep 37530377 = 28147783) B28147783
theorem B109857701 : Blo 1370504 109857701 := bstep (se 4 (by rfl) ⟨10299159, by rfl⟩ : syracuseStep 109857701 = 20598319) B20598319
theorem B1371367 : Blo 1370504 1371367 := bstep (se 1 (by rfl) ⟨1028525, by rfl⟩ : syracuseStep 1371367 = 2057051) B2057051
theorem B40604237 : Blo 1370504 40604237 := bstep (se 3 (by rfl) ⟨7613294, by rfl⟩ : syracuseStep 40604237 = 15226589) B15226589
theorem B2315243 : Blo 1370504 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B10409147 : Blo 1370504 10409147 := bstep (se 1 (by rfl) ⟨7806860, by rfl⟩ : syracuseStep 10409147 = 15613721) B15613721
theorem B6939431 : Blo 1370504 6939431 := bstep (se 1 (by rfl) ⟨5204573, by rfl⟩ : syracuseStep 6939431 = 10409147) B10409147
theorem B25020251 : Blo 1370504 25020251 := bstep (se 1 (by rfl) ⟨18765188, by rfl⟩ : syracuseStep 25020251 = 37530377) B37530377
theorem B73238467 : Blo 1370504 73238467 := bstep (se 1 (by rfl) ⟨54928850, by rfl⟩ : syracuseStep 73238467 = 109857701) B109857701
theorem B1371007 : Blo 1370504 1371007 := bstep (se 1 (by rfl) ⟨1028255, by rfl⟩ : syracuseStep 1371007 = 2056511) B2056511
theorem B27069491 : Blo 1370504 27069491 := bstep (se 1 (by rfl) ⟨20302118, by rfl⟩ : syracuseStep 27069491 = 40604237) B40604237
theorem B1543495 : Blo 1370504 1543495 := bstep (se 1 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 1543495 = 2315243) B2315243
theorem B1371599 : Blo 1370504 1371599 := bstep (se 1 (by rfl) ⟨1028699, by rfl⟩ : syracuseStep 1371599 = 2057399) B2057399
theorem B1371887 : Blo 1370504 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B4627583 : Blo 1370504 4627583 := bstep (se 1 (by rfl) ⟨3470687, by rfl⟩ : syracuseStep 4627583 = 6941375) B6941375
theorem B16680167 : Blo 1370504 16680167 := bstep (se 1 (by rfl) ⟨12510125, by rfl⟩ : syracuseStep 16680167 = 25020251) B25020251
theorem B2057993 : Blo 1370504 2057993 := bstep (se 2 (by rfl) ⟨771747, by rfl⟩ : syracuseStep 2057993 = 1543495) B1543495
theorem B97651289 : Blo 1370504 97651289 := bstep (se 2 (by rfl) ⟨36619233, by rfl⟩ : syracuseStep 97651289 = 73238467) B73238467
theorem B3085055 : Blo 1370504 3085055 := bstep (se 1 (by rfl) ⟨2313791, by rfl⟩ : syracuseStep 3085055 = 4627583) B4627583
theorem B4626287 : Blo 1370504 4626287 := bstep (se 1 (by rfl) ⟨3469715, by rfl⟩ : syracuseStep 4626287 = 6939431) B6939431
theorem B18046327 : Blo 1370504 18046327 := bstep (se 1 (by rfl) ⟨13534745, by rfl⟩ : syracuseStep 18046327 = 27069491) B27069491
theorem B2056703 : Blo 1370504 2056703 := bstep (se 1 (by rfl) ⟨1542527, by rfl⟩ : syracuseStep 2056703 = 3085055) B3085055
theorem B24061769 : Blo 1370504 24061769 := bstep (se 2 (by rfl) ⟨9023163, by rfl⟩ : syracuseStep 24061769 = 18046327) B18046327
theorem B11120111 : Blo 1370504 11120111 := bstep (se 1 (by rfl) ⟨8340083, by rfl⟩ : syracuseStep 11120111 = 16680167) B16680167
theorem B1371995 : Blo 1370504 1371995 := bstep (se 1 (by rfl) ⟨1028996, by rfl⟩ : syracuseStep 1371995 = 2057993) B2057993
theorem B3084191 : Blo 1370504 3084191 := bstep (se 1 (by rfl) ⟨2313143, by rfl⟩ : syracuseStep 3084191 = 4626287) B4626287
theorem B260403437 : Blo 1370504 260403437 := bstep (se 3 (by rfl) ⟨48825644, by rfl⟩ : syracuseStep 260403437 = 97651289) B97651289
theorem B16041179 : Blo 1370504 16041179 := bstep (se 1 (by rfl) ⟨12030884, by rfl⟩ : syracuseStep 16041179 = 24061769) B24061769
theorem B1371135 : Blo 1370504 1371135 := bstep (se 1 (by rfl) ⟨1028351, by rfl⟩ : syracuseStep 1371135 = 2056703) B2056703
theorem B173602291 : Blo 1370504 173602291 := bstep (se 1 (by rfl) ⟨130201718, by rfl⟩ : syracuseStep 173602291 = 260403437) B260403437
theorem B7413407 : Blo 1370504 7413407 := bstep (se 1 (by rfl) ⟨5560055, by rfl⟩ : syracuseStep 7413407 = 11120111) B11120111
theorem B2056127 : Blo 1370504 2056127 := bstep (se 1 (by rfl) ⟨1542095, by rfl⟩ : syracuseStep 2056127 = 3084191) B3084191
theorem B4942271 : Blo 1370504 4942271 := bstep (se 1 (by rfl) ⟨3706703, by rfl⟩ : syracuseStep 4942271 = 7413407) B7413407
theorem B1370751 : Blo 1370504 1370751 := bstep (se 1 (by rfl) ⟨1028063, by rfl⟩ : syracuseStep 1370751 = 2056127) B2056127
theorem B10694119 : Blo 1370504 10694119 := bstep (se 1 (by rfl) ⟨8020589, by rfl⟩ : syracuseStep 10694119 = 16041179) B16041179
theorem B231469721 : Blo 1370504 231469721 := bstep (se 2 (by rfl) ⟨86801145, by rfl⟩ : syracuseStep 231469721 = 173602291) B173602291
theorem B154313147 : Blo 1370504 154313147 := bstep (se 1 (by rfl) ⟨115734860, by rfl⟩ : syracuseStep 154313147 = 231469721) B231469721
theorem B3294847 : Blo 1370504 3294847 := bstep (se 1 (by rfl) ⟨2471135, by rfl⟩ : syracuseStep 3294847 = 4942271) B4942271
theorem B14258825 : Blo 1370504 14258825 := bstep (se 2 (by rfl) ⟨5347059, by rfl⟩ : syracuseStep 14258825 = 10694119) B10694119
theorem B102875431 : Blo 1370504 102875431 := bstep (se 1 (by rfl) ⟨77156573, by rfl⟩ : syracuseStep 102875431 = 154313147) B154313147
theorem B4393129 : Blo 1370504 4393129 := bstep (se 2 (by rfl) ⟨1647423, by rfl⟩ : syracuseStep 4393129 = 3294847) B3294847
theorem B9505883 : Blo 1370504 9505883 := bstep (se 1 (by rfl) ⟨7129412, by rfl⟩ : syracuseStep 9505883 = 14258825) B14258825
theorem B5857505 : Blo 1370504 5857505 := bstep (se 2 (by rfl) ⟨2196564, by rfl⟩ : syracuseStep 5857505 = 4393129) B4393129
theorem B137167241 : Blo 1370504 137167241 := bstep (se 2 (by rfl) ⟨51437715, by rfl⟩ : syracuseStep 137167241 = 102875431) B102875431
theorem B25349021 : Blo 1370504 25349021 := bstep (se 3 (by rfl) ⟨4752941, by rfl⟩ : syracuseStep 25349021 = 9505883) B9505883
theorem B3905003 : Blo 1370504 3905003 := bstep (se 1 (by rfl) ⟨2928752, by rfl⟩ : syracuseStep 3905003 = 5857505) B5857505
theorem B365779309 : Blo 1370504 365779309 := bstep (se 3 (by rfl) ⟨68583620, by rfl⟩ : syracuseStep 365779309 = 137167241) B137167241
theorem B16899347 : Blo 1370504 16899347 := bstep (se 1 (by rfl) ⟨12674510, by rfl⟩ : syracuseStep 16899347 = 25349021) B25349021
theorem B11266231 : Blo 1370504 11266231 := bstep (se 1 (by rfl) ⟨8449673, by rfl⟩ : syracuseStep 11266231 = 16899347) B16899347
theorem B487705745 : Blo 1370504 487705745 := bstep (se 2 (by rfl) ⟨182889654, by rfl⟩ : syracuseStep 487705745 = 365779309) B365779309
theorem B2603335 : Blo 1370504 2603335 := bstep (se 1 (by rfl) ⟨1952501, by rfl⟩ : syracuseStep 2603335 = 3905003) B3905003
theorem B325137163 : Blo 1370504 325137163 := bstep (se 1 (by rfl) ⟨243852872, by rfl⟩ : syracuseStep 325137163 = 487705745) B487705745
theorem B15021641 : Blo 1370504 15021641 := bstep (se 2 (by rfl) ⟨5633115, by rfl⟩ : syracuseStep 15021641 = 11266231) B11266231
theorem B3471113 : Blo 1370504 3471113 := bstep (se 2 (by rfl) ⟨1301667, by rfl⟩ : syracuseStep 3471113 = 2603335) B2603335
theorem B433516217 : Blo 1370504 433516217 := bstep (se 2 (by rfl) ⟨162568581, by rfl⟩ : syracuseStep 433516217 = 325137163) B325137163
theorem B10014427 : Blo 1370504 10014427 := bstep (se 1 (by rfl) ⟨7510820, by rfl⟩ : syracuseStep 10014427 = 15021641) B15021641
theorem B2314075 : Blo 1370504 2314075 := bstep (se 1 (by rfl) ⟨1735556, by rfl⟩ : syracuseStep 2314075 = 3471113) B3471113
theorem B4624172981 : Blo 1370504 4624172981 := bstep (se 5 (by rfl) ⟨216758108, by rfl⟩ : syracuseStep 4624172981 = 433516217) B433516217
theorem B3085433 : Blo 1370504 3085433 := bstep (se 2 (by rfl) ⟨1157037, by rfl⟩ : syracuseStep 3085433 = 2314075) B2314075
theorem B13352569 : Blo 1370504 13352569 := bstep (se 2 (by rfl) ⟨5007213, by rfl⟩ : syracuseStep 13352569 = 10014427) B10014427
theorem B2056955 : Blo 1370504 2056955 := bstep (se 1 (by rfl) ⟨1542716, by rfl⟩ : syracuseStep 2056955 = 3085433) B3085433
theorem B3082781987 : Blo 1370504 3082781987 := bstep (se 1 (by rfl) ⟨2312086490, by rfl⟩ : syracuseStep 3082781987 = 4624172981) B4624172981
theorem B284854805 : Blo 1370504 284854805 := bstep (se 6 (by rfl) ⟨6676284, by rfl⟩ : syracuseStep 284854805 = 13352569) B13352569
theorem B1371303 : Blo 1370504 1371303 := bstep (se 1 (by rfl) ⟨1028477, by rfl⟩ : syracuseStep 1371303 = 2056955) B2056955
theorem B2055187991 : Blo 1370504 2055187991 := bstep (se 1 (by rfl) ⟨1541390993, by rfl⟩ : syracuseStep 2055187991 = 3082781987) B3082781987
theorem B189903203 : Blo 1370504 189903203 := bstep (se 1 (by rfl) ⟨142427402, by rfl⟩ : syracuseStep 189903203 = 284854805) B284854805
theorem B126602135 : Blo 1370504 126602135 := bstep (se 1 (by rfl) ⟨94951601, by rfl⟩ : syracuseStep 126602135 = 189903203) B189903203
theorem B1370125327 : Blo 1370504 1370125327 := bstep (se 1 (by rfl) ⟨1027593995, by rfl⟩ : syracuseStep 1370125327 = 2055187991) B2055187991
theorem B1826833769 : Blo 1370504 1826833769 := bstep (se 2 (by rfl) ⟨685062663, by rfl⟩ : syracuseStep 1826833769 = 1370125327) B1370125327
theorem B84401423 : Blo 1370504 84401423 := bstep (se 1 (by rfl) ⟨63301067, by rfl⟩ : syracuseStep 84401423 = 126602135) B126602135
theorem B1217889179 : Blo 1370504 1217889179 := bstep (se 1 (by rfl) ⟨913416884, by rfl⟩ : syracuseStep 1217889179 = 1826833769) B1826833769
theorem B56267615 : Blo 1370504 56267615 := bstep (se 1 (by rfl) ⟨42200711, by rfl⟩ : syracuseStep 56267615 = 84401423) B84401423
theorem B37511743 : Blo 1370504 37511743 := bstep (se 1 (by rfl) ⟨28133807, by rfl⟩ : syracuseStep 37511743 = 56267615) B56267615
theorem B811926119 : Blo 1370504 811926119 := bstep (se 1 (by rfl) ⟨608944589, by rfl⟩ : syracuseStep 811926119 = 1217889179) B1217889179
theorem B50015657 : Blo 1370504 50015657 := bstep (se 2 (by rfl) ⟨18755871, by rfl⟩ : syracuseStep 50015657 = 37511743) B37511743
theorem B541284079 : Blo 1370504 541284079 := bstep (se 1 (by rfl) ⟨405963059, by rfl⟩ : syracuseStep 541284079 = 811926119) B811926119
theorem B133375085 : Blo 1370504 133375085 := bstep (se 3 (by rfl) ⟨25007828, by rfl⟩ : syracuseStep 133375085 = 50015657) B50015657
theorem B721712105 : Blo 1370504 721712105 := bstep (se 2 (by rfl) ⟨270642039, by rfl⟩ : syracuseStep 721712105 = 541284079) B541284079
theorem B481141403 : Blo 1370504 481141403 := bstep (se 1 (by rfl) ⟨360856052, by rfl⟩ : syracuseStep 481141403 = 721712105) B721712105
theorem B88916723 : Blo 1370504 88916723 := bstep (se 1 (by rfl) ⟨66687542, by rfl⟩ : syracuseStep 88916723 = 133375085) B133375085
theorem B59277815 : Blo 1370504 59277815 := bstep (se 1 (by rfl) ⟨44458361, by rfl⟩ : syracuseStep 59277815 = 88916723) B88916723
theorem B320760935 : Blo 1370504 320760935 := bstep (se 1 (by rfl) ⟨240570701, by rfl⟩ : syracuseStep 320760935 = 481141403) B481141403
theorem B39518543 : Blo 1370504 39518543 := bstep (se 1 (by rfl) ⟨29638907, by rfl⟩ : syracuseStep 39518543 = 59277815) B59277815
theorem B213840623 : Blo 1370504 213840623 := bstep (se 1 (by rfl) ⟨160380467, by rfl⟩ : syracuseStep 213840623 = 320760935) B320760935
theorem B26345695 : Blo 1370504 26345695 := bstep (se 1 (by rfl) ⟨19759271, by rfl⟩ : syracuseStep 26345695 = 39518543) B39518543
theorem B142560415 : Blo 1370504 142560415 := bstep (se 1 (by rfl) ⟨106920311, by rfl⟩ : syracuseStep 142560415 = 213840623) B213840623
theorem B35127593 : Blo 1370504 35127593 := bstep (se 2 (by rfl) ⟨13172847, by rfl⟩ : syracuseStep 35127593 = 26345695) B26345695
theorem B190080553 : Blo 1370504 190080553 := bstep (se 2 (by rfl) ⟨71280207, by rfl⟩ : syracuseStep 190080553 = 142560415) B142560415
theorem B253440737 : Blo 1370504 253440737 := bstep (se 2 (by rfl) ⟨95040276, by rfl⟩ : syracuseStep 253440737 = 190080553) B190080553
theorem B23418395 : Blo 1370504 23418395 := bstep (se 1 (by rfl) ⟨17563796, by rfl⟩ : syracuseStep 23418395 = 35127593) B35127593
theorem B168960491 : Blo 1370504 168960491 := bstep (se 1 (by rfl) ⟨126720368, by rfl⟩ : syracuseStep 168960491 = 253440737) B253440737
theorem B15612263 : Blo 1370504 15612263 := bstep (se 1 (by rfl) ⟨11709197, by rfl⟩ : syracuseStep 15612263 = 23418395) B23418395
theorem B112640327 : Blo 1370504 112640327 := bstep (se 1 (by rfl) ⟨84480245, by rfl⟩ : syracuseStep 112640327 = 168960491) B168960491
theorem B10408175 : Blo 1370504 10408175 := bstep (se 1 (by rfl) ⟨7806131, by rfl⟩ : syracuseStep 10408175 = 15612263) B15612263
theorem B6938783 : Blo 1370504 6938783 := bstep (se 1 (by rfl) ⟨5204087, by rfl⟩ : syracuseStep 6938783 = 10408175) B10408175
theorem B75093551 : Blo 1370504 75093551 := bstep (se 1 (by rfl) ⟨56320163, by rfl⟩ : syracuseStep 75093551 = 112640327) B112640327
theorem B50062367 : Blo 1370504 50062367 := bstep (se 1 (by rfl) ⟨37546775, by rfl⟩ : syracuseStep 50062367 = 75093551) B75093551
theorem B4625855 : Blo 1370504 4625855 := bstep (se 1 (by rfl) ⟨3469391, by rfl⟩ : syracuseStep 4625855 = 6938783) B6938783
theorem B33374911 : Blo 1370504 33374911 := bstep (se 1 (by rfl) ⟨25031183, by rfl⟩ : syracuseStep 33374911 = 50062367) B50062367
theorem B3083903 : Blo 1370504 3083903 := bstep (se 1 (by rfl) ⟨2312927, by rfl⟩ : syracuseStep 3083903 = 4625855) B4625855
theorem B44499881 : Blo 1370504 44499881 := bstep (se 2 (by rfl) ⟨16687455, by rfl⟩ : syracuseStep 44499881 = 33374911) B33374911
theorem B2055935 : Blo 1370504 2055935 := bstep (se 1 (by rfl) ⟨1541951, by rfl⟩ : syracuseStep 2055935 = 3083903) B3083903
theorem B1370623 : Blo 1370504 1370623 := bstep (se 1 (by rfl) ⟨1027967, by rfl⟩ : syracuseStep 1370623 = 2055935) B2055935
theorem B29666587 : Blo 1370504 29666587 := bstep (se 1 (by rfl) ⟨22249940, by rfl⟩ : syracuseStep 29666587 = 44499881) B44499881
theorem B39555449 : Blo 1370504 39555449 := bstep (se 2 (by rfl) ⟨14833293, by rfl⟩ : syracuseStep 39555449 = 29666587) B29666587
theorem B26370299 : Blo 1370504 26370299 := bstep (se 1 (by rfl) ⟨19777724, by rfl⟩ : syracuseStep 26370299 = 39555449) B39555449
theorem B17580199 : Blo 1370504 17580199 := bstep (se 1 (by rfl) ⟨13185149, by rfl⟩ : syracuseStep 17580199 = 26370299) B26370299
theorem B23440265 : Blo 1370504 23440265 := bstep (se 2 (by rfl) ⟨8790099, by rfl⟩ : syracuseStep 23440265 = 17580199) B17580199
theorem B15626843 : Blo 1370504 15626843 := bstep (se 1 (by rfl) ⟨11720132, by rfl⟩ : syracuseStep 15626843 = 23440265) B23440265
theorem B10417895 : Blo 1370504 10417895 := bstep (se 1 (by rfl) ⟨7813421, by rfl⟩ : syracuseStep 10417895 = 15626843) B15626843
theorem B6945263 : Blo 1370504 6945263 := bstep (se 1 (by rfl) ⟨5208947, by rfl⟩ : syracuseStep 6945263 = 10417895) B10417895
theorem B4630175 : Blo 1370504 4630175 := bstep (se 1 (by rfl) ⟨3472631, by rfl⟩ : syracuseStep 4630175 = 6945263) B6945263
theorem B3086783 : Blo 1370504 3086783 := bstep (se 1 (by rfl) ⟨2315087, by rfl⟩ : syracuseStep 3086783 = 4630175) B4630175
theorem B2057855 : Blo 1370504 2057855 := bstep (se 1 (by rfl) ⟨1543391, by rfl⟩ : syracuseStep 2057855 = 3086783) B3086783
theorem B1371903 : Blo 1370504 1371903 := bstep (se 1 (by rfl) ⟨1028927, by rfl⟩ : syracuseStep 1371903 = 2057855) B2057855

theorem C0 (j : ℕ) (h1 : 342626 ≤ j) (h2 : j ≤ 343000) : Blo 1370504 (4 * j + 3) := by
  interval_cases j
  · exact B1370507
  · exact B1370511
  · exact B1370515
  · exact B1370519
  · exact B1370523
  · exact B1370527
  · exact B1370531
  · exact B1370535
  · exact B1370539
  · exact B1370543
  · exact B1370547
  · exact B1370551
  · exact B1370555
  · exact B1370559
  · exact B1370563
  · exact B1370567
  · exact B1370571
  · exact B1370575
  · exact B1370579
  · exact B1370583
  · exact B1370587
  · exact B1370591
  · exact B1370595
  · exact B1370599
  · exact B1370603
  · exact B1370607
  · exact B1370611
  · exact B1370615
  · exact B1370619
  · exact B1370623
  · exact B1370627
  · exact B1370631
  · exact B1370635
  · exact B1370639
  · exact B1370643
  · exact B1370647
  · exact B1370651
  · exact B1370655
  · exact B1370659
  · exact B1370663
  · exact B1370667
  · exact B1370671
  · exact B1370675
  · exact B1370679
  · exact B1370683
  · exact B1370687
  · exact B1370691
  · exact B1370695
  · exact B1370699
  · exact B1370703
  · exact B1370707
  · exact B1370711
  · exact B1370715
  · exact B1370719
  · exact B1370723
  · exact B1370727
  · exact B1370731
  · exact B1370735
  · exact B1370739
  · exact B1370743
  · exact B1370747
  · exact B1370751
  · exact B1370755
  · exact B1370759
  · exact B1370763
  · exact B1370767
  · exact B1370771
  · exact B1370775
  · exact B1370779
  · exact B1370783
  · exact B1370787
  · exact B1370791
  · exact B1370795
  · exact B1370799
  · exact B1370803
  · exact B1370807
  · exact B1370811
  · exact B1370815
  · exact B1370819
  · exact B1370823
  · exact B1370827
  · exact B1370831
  · exact B1370835
  · exact B1370839
  · exact B1370843
  · exact B1370847
  · exact B1370851
  · exact B1370855
  · exact B1370859
  · exact B1370863
  · exact B1370867
  · exact B1370871
  · exact B1370875
  · exact B1370879
  · exact B1370883
  · exact B1370887
  · exact B1370891
  · exact B1370895
  · exact B1370899
  · exact B1370903
  · exact B1370907
  · exact B1370911
  · exact B1370915
  · exact B1370919
  · exact B1370923
  · exact B1370927
  · exact B1370931
  · exact B1370935
  · exact B1370939
  · exact B1370943
  · exact B1370947
  · exact B1370951
  · exact B1370955
  · exact B1370959
  · exact B1370963
  · exact B1370967
  · exact B1370971
  · exact B1370975
  · exact B1370979
  · exact B1370983
  · exact B1370987
  · exact B1370991
  · exact B1370995
  · exact B1370999
  · exact B1371003
  · exact B1371007
  · exact B1371011
  · exact B1371015
  · exact B1371019
  · exact B1371023
  · exact B1371027
  · exact B1371031
  · exact B1371035
  · exact B1371039
  · exact B1371043
  · exact B1371047
  · exact B1371051
  · exact B1371055
  · exact B1371059
  · exact B1371063
  · exact B1371067
  · exact B1371071
  · exact B1371075
  · exact B1371079
  · exact B1371083
  · exact B1371087
  · exact B1371091
  · exact B1371095
  · exact B1371099
  · exact B1371103
  · exact B1371107
  · exact B1371111
  · exact B1371115
  · exact B1371119
  · exact B1371123
  · exact B1371127
  · exact B1371131
  · exact B1371135
  · exact B1371139
  · exact B1371143
  · exact B1371147
  · exact B1371151
  · exact B1371155
  · exact B1371159
  · exact B1371163
  · exact B1371167
  · exact B1371171
  · exact B1371175
  · exact B1371179
  · exact B1371183
  · exact B1371187
  · exact B1371191
  · exact B1371195
  · exact B1371199
  · exact B1371203
  · exact B1371207
  · exact B1371211
  · exact B1371215
  · exact B1371219
  · exact B1371223
  · exact B1371227
  · exact B1371231
  · exact B1371235
  · exact B1371239
  · exact B1371243
  · exact B1371247
  · exact B1371251
  · exact B1371255
  · exact B1371259
  · exact B1371263
  · exact B1371267
  · exact B1371271
  · exact B1371275
  · exact B1371279
  · exact B1371283
  · exact B1371287
  · exact B1371291
  · exact B1371295
  · exact B1371299
  · exact B1371303
  · exact B1371307
  · exact B1371311
  · exact B1371315
  · exact B1371319
  · exact B1371323
  · exact B1371327
  · exact B1371331
  · exact B1371335
  · exact B1371339
  · exact B1371343
  · exact B1371347
  · exact B1371351
  · exact B1371355
  · exact B1371359
  · exact B1371363
  · exact B1371367
  · exact B1371371
  · exact B1371375
  · exact B1371379
  · exact B1371383
  · exact B1371387
  · exact B1371391
  · exact B1371395
  · exact B1371399
  · exact B1371403
  · exact B1371407
  · exact B1371411
  · exact B1371415
  · exact B1371419
  · exact B1371423
  · exact B1371427
  · exact B1371431
  · exact B1371435
  · exact B1371439
  · exact B1371443
  · exact B1371447
  · exact B1371451
  · exact B1371455
  · exact B1371459
  · exact B1371463
  · exact B1371467
  · exact B1371471
  · exact B1371475
  · exact B1371479
  · exact B1371483
  · exact B1371487
  · exact B1371491
  · exact B1371495
  · exact B1371499
  · exact B1371503
  · exact B1371507
  · exact B1371511
  · exact B1371515
  · exact B1371519
  · exact B1371523
  · exact B1371527
  · exact B1371531
  · exact B1371535
  · exact B1371539
  · exact B1371543
  · exact B1371547
  · exact B1371551
  · exact B1371555
  · exact B1371559
  · exact B1371563
  · exact B1371567
  · exact B1371571
  · exact B1371575
  · exact B1371579
  · exact B1371583
  · exact B1371587
  · exact B1371591
  · exact B1371595
  · exact B1371599
  · exact B1371603
  · exact B1371607
  · exact B1371611
  · exact B1371615
  · exact B1371619
  · exact B1371623
  · exact B1371627
  · exact B1371631
  · exact B1371635
  · exact B1371639
  · exact B1371643
  · exact B1371647
  · exact B1371651
  · exact B1371655
  · exact B1371659
  · exact B1371663
  · exact B1371667
  · exact B1371671
  · exact B1371675
  · exact B1371679
  · exact B1371683
  · exact B1371687
  · exact B1371691
  · exact B1371695
  · exact B1371699
  · exact B1371703
  · exact B1371707
  · exact B1371711
  · exact B1371715
  · exact B1371719
  · exact B1371723
  · exact B1371727
  · exact B1371731
  · exact B1371735
  · exact B1371739
  · exact B1371743
  · exact B1371747
  · exact B1371751
  · exact B1371755
  · exact B1371759
  · exact B1371763
  · exact B1371767
  · exact B1371771
  · exact B1371775
  · exact B1371779
  · exact B1371783
  · exact B1371787
  · exact B1371791
  · exact B1371795
  · exact B1371799
  · exact B1371803
  · exact B1371807
  · exact B1371811
  · exact B1371815
  · exact B1371819
  · exact B1371823
  · exact B1371827
  · exact B1371831
  · exact B1371835
  · exact B1371839
  · exact B1371843
  · exact B1371847
  · exact B1371851
  · exact B1371855
  · exact B1371859
  · exact B1371863
  · exact B1371867
  · exact B1371871
  · exact B1371875
  · exact B1371879
  · exact B1371883
  · exact B1371887
  · exact B1371891
  · exact B1371895
  · exact B1371899
  · exact B1371903
  · exact B1371907
  · exact B1371911
  · exact B1371915
  · exact B1371919
  · exact B1371923
  · exact B1371927
  · exact B1371931
  · exact B1371935
  · exact B1371939
  · exact B1371943
  · exact B1371947
  · exact B1371951
  · exact B1371955
  · exact B1371959
  · exact B1371963
  · exact B1371967
  · exact B1371971
  · exact B1371975
  · exact B1371979
  · exact B1371983
  · exact B1371987
  · exact B1371991
  · exact B1371995
  · exact B1371999
  · exact B1372003

theorem solution (m : ℕ) (hlo : 1370504 ≤ m) (hhi : m ≤ 1372004) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 342626 ≤ j := by omega
    have hj2 : j ≤ 343000 := by omega
    have hb : Blo 1370504 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
