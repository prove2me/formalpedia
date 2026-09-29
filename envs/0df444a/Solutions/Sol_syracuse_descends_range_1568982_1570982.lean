-- Prove2me | solution 1 for syracuse_descends_range_1568982_1570982
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:53.947687+00:00
-- url     : https://prove2.me/submissions/cfc413c3-2982-4eab-8e86-59e5a0346e81

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


theorem B7946261 : Blo 1568982 7946261 := bbase (se 6 (by rfl) ⟨186240, by rfl⟩ : syracuseStep 7946261 = 372481) (by norm_num)
theorem B3530789 : Blo 1568982 3530789 := bbase (se 4 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 3530789 = 662023) (by norm_num)
theorem B5300261 : Blo 1568982 5300261 := bbase (se 4 (by rfl) ⟨496899, by rfl⟩ : syracuseStep 5300261 = 993799) (by norm_num)
theorem B5963813 : Blo 1568982 5963813 := bbase (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) (by norm_num)
theorem B3530861 : Blo 1568982 3530861 := bbase (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) (by norm_num)
theorem B2982005 : Blo 1568982 2982005 := bbase (se 5 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 2982005 = 279563) (by norm_num)
theorem B3530933 : Blo 1568982 3530933 := bbase (se 5 (by rfl) ⟨165512, by rfl⟩ : syracuseStep 3530933 = 331025) (by norm_num)
theorem B3973333 : Blo 1568982 3973333 := bbase (se 7 (by rfl) ⟨46562, by rfl⟩ : syracuseStep 3973333 = 93125) (by norm_num)
theorem B3531005 : Blo 1568982 3531005 := bbase (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) (by norm_num)
theorem B3531077 : Blo 1568982 3531077 := bbase (se 4 (by rfl) ⟨331038, by rfl⟩ : syracuseStep 3531077 = 662077) (by norm_num)
theorem B3973445 : Blo 1568982 3973445 := bbase (se 4 (by rfl) ⟨372510, by rfl⟩ : syracuseStep 3973445 = 745021) (by norm_num)
theorem B5964101 : Blo 1568982 5964101 := bbase (se 4 (by rfl) ⟨559134, by rfl⟩ : syracuseStep 5964101 = 1118269) (by norm_num)
theorem B3531149 : Blo 1568982 3531149 := bbase (se 3 (by rfl) ⟨662090, by rfl⟩ : syracuseStep 3531149 = 1324181) (by norm_num)
theorem B3531221 : Blo 1568982 3531221 := bbase (se 7 (by rfl) ⟨41381, by rfl⟩ : syracuseStep 3531221 = 82763) (by norm_num)
theorem B5300693 : Blo 1568982 5300693 := bbase (se 7 (by rfl) ⟨62117, by rfl⟩ : syracuseStep 5300693 = 124235) (by norm_num)
theorem B3973637 : Blo 1568982 3973637 := bbase (se 4 (by rfl) ⟨372528, by rfl⟩ : syracuseStep 3973637 = 745057) (by norm_num)
theorem B8946197 : Blo 1568982 8946197 := bbase (se 6 (by rfl) ⟨209676, by rfl⟩ : syracuseStep 8946197 = 419353) (by norm_num)
theorem B3531293 : Blo 1568982 3531293 := bbase (se 3 (by rfl) ⟨662117, by rfl⟩ : syracuseStep 3531293 = 1324235) (by norm_num)
theorem B6365749 : Blo 1568982 6365749 := bbase (se 5 (by rfl) ⟨298394, by rfl⟩ : syracuseStep 6365749 = 596789) (by norm_num)
theorem B3531365 : Blo 1568982 3531365 := bbase (se 4 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 3531365 = 662131) (by norm_num)
theorem B8938133 : Blo 1568982 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B3531437 : Blo 1568982 3531437 := bbase (se 3 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 3531437 = 1324289) (by norm_num)
theorem B1884917 : Blo 1568982 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B3531509 : Blo 1568982 3531509 := bbase (se 5 (by rfl) ⟨165539, by rfl⟩ : syracuseStep 3531509 = 331079) (by norm_num)
theorem B3580661 : Blo 1568982 3580661 := bbase (se 5 (by rfl) ⟨167843, by rfl⟩ : syracuseStep 3580661 = 335687) (by norm_num)
theorem B4473589 : Blo 1568982 4473589 := bbase (se 5 (by rfl) ⟨209699, by rfl⟩ : syracuseStep 4473589 = 419399) (by norm_num)
theorem B9675541 : Blo 1568982 9675541 := bbase (se 6 (by rfl) ⟨226770, by rfl⟩ : syracuseStep 9675541 = 453541) (by norm_num)
theorem B1884989 : Blo 1568982 1884989 := bbase (se 3 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 1884989 = 706871) (by norm_num)
theorem B3531581 : Blo 1568982 3531581 := bbase (se 3 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 3531581 = 1324343) (by norm_num)
theorem B3351365 : Blo 1568982 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B2040665 : Blo 1568982 2040665 := bbase (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) (by norm_num)
theorem B3973981 : Blo 1568982 3973981 := bbase (se 3 (by rfl) ⟨745121, by rfl⟩ : syracuseStep 3973981 = 1490243) (by norm_num)
theorem B3531653 : Blo 1568982 3531653 := bbase (se 4 (by rfl) ⟨331092, by rfl⟩ : syracuseStep 3531653 = 662185) (by norm_num)
theorem B5301125 : Blo 1568982 5301125 := bbase (se 4 (by rfl) ⟨496980, by rfl⟩ : syracuseStep 5301125 = 993961) (by norm_num)
theorem B3531725 : Blo 1568982 3531725 := bbase (se 3 (by rfl) ⟨662198, by rfl⟩ : syracuseStep 3531725 = 1324397) (by norm_num)
theorem B3974093 : Blo 1568982 3974093 := bbase (se 3 (by rfl) ⟨745142, by rfl⟩ : syracuseStep 3974093 = 1490285) (by norm_num)
theorem B58844117 : Blo 1568982 58844117 := bbase (se 7 (by rfl) ⟨689579, by rfl⟩ : syracuseStep 58844117 = 1379159) (by norm_num)
theorem B14320597 : Blo 1568982 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B3531797 : Blo 1568982 3531797 := bbase (se 6 (by rfl) ⟨82776, by rfl⟩ : syracuseStep 3531797 = 165553) (by norm_num)
theorem B5030981 : Blo 1568982 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B3531869 : Blo 1568982 3531869 := bbase (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) (by norm_num)
theorem B1885297 : Blo 1568982 1885297 := bbase (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) (by norm_num)
theorem B2516093 : Blo 1568982 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B3974285 : Blo 1568982 3974285 := bbase (se 3 (by rfl) ⟨745178, by rfl⟩ : syracuseStep 3974285 = 1490357) (by norm_num)
theorem B3531941 : Blo 1568982 3531941 := bbase (se 4 (by rfl) ⟨331119, by rfl⟩ : syracuseStep 3531941 = 662239) (by norm_num)
theorem B2516189 : Blo 1568982 2516189 := bbase (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) (by norm_num)
theorem B3532013 : Blo 1568982 3532013 := bbase (se 3 (by rfl) ⟨662252, by rfl⟩ : syracuseStep 3532013 = 1324505) (by norm_num)
theorem B2516221 : Blo 1568982 2516221 := bbase (se 3 (by rfl) ⟨471791, by rfl⟩ : syracuseStep 2516221 = 943583) (by norm_num)
theorem B1885465 : Blo 1568982 1885465 := bbase (se 2 (by rfl) ⟨707049, by rfl⟩ : syracuseStep 1885465 = 1414099) (by norm_num)
theorem B7947557 : Blo 1568982 7947557 := bbase (se 4 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 7947557 = 1490167) (by norm_num)
theorem B3532085 : Blo 1568982 3532085 := bbase (se 5 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 3532085 = 331133) (by norm_num)
theorem B5301557 : Blo 1568982 5301557 := bbase (se 5 (by rfl) ⟨248510, by rfl⟩ : syracuseStep 5301557 = 497021) (by norm_num)
theorem B1885513 : Blo 1568982 1885513 := bbase (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) (by norm_num)
theorem B7161173 : Blo 1568982 7161173 := bbase (se 12 (by rfl) ⟨2622, by rfl⟩ : syracuseStep 7161173 = 5245) (by norm_num)
theorem B3532157 : Blo 1568982 3532157 := bbase (se 3 (by rfl) ⟨662279, by rfl⟩ : syracuseStep 3532157 = 1324559) (by norm_num)
theorem B1885609 : Blo 1568982 1885609 := bbase (se 2 (by rfl) ⟨707103, by rfl⟩ : syracuseStep 1885609 = 1414207) (by norm_num)
theorem B3532229 : Blo 1568982 3532229 := bbase (se 4 (by rfl) ⟨331146, by rfl⟩ : syracuseStep 3532229 = 662293) (by norm_num)
theorem B3974629 : Blo 1568982 3974629 := bbase (se 4 (by rfl) ⟨372621, by rfl⟩ : syracuseStep 3974629 = 745243) (by norm_num)
theorem B3532301 : Blo 1568982 3532301 := bbase (se 3 (by rfl) ⟨662306, by rfl⟩ : syracuseStep 3532301 = 1324613) (by norm_num)
theorem B3352117 : Blo 1568982 3352117 := bbase (se 5 (by rfl) ⟨157130, by rfl⟩ : syracuseStep 3352117 = 314261) (by norm_num)
theorem B3532373 : Blo 1568982 3532373 := bbase (se 8 (by rfl) ⟨20697, by rfl⟩ : syracuseStep 3532373 = 41395) (by norm_num)
theorem B3974741 : Blo 1568982 3974741 := bbase (se 8 (by rfl) ⟨23289, by rfl⟩ : syracuseStep 3974741 = 46579) (by norm_num)
theorem B3532445 : Blo 1568982 3532445 := bbase (se 3 (by rfl) ⟨662333, by rfl⟩ : syracuseStep 3532445 = 1324667) (by norm_num)
theorem B4245173 : Blo 1568982 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B2647741 : Blo 1568982 2647741 := bbase (se 3 (by rfl) ⟨496451, by rfl⟩ : syracuseStep 2647741 = 992903) (by norm_num)
theorem B3352261 : Blo 1568982 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B2827981 : Blo 1568982 2827981 := bbase (se 3 (by rfl) ⟨530246, by rfl⟩ : syracuseStep 2827981 = 1060493) (by norm_num)
theorem B20113109 : Blo 1568982 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B3532517 : Blo 1568982 3532517 := bbase (se 4 (by rfl) ⟨331173, by rfl⟩ : syracuseStep 3532517 = 662347) (by norm_num)
theorem B5301989 : Blo 1568982 5301989 := bbase (se 4 (by rfl) ⟨497061, by rfl⟩ : syracuseStep 5301989 = 994123) (by norm_num)
theorem B2647829 : Blo 1568982 2647829 := bbase (se 6 (by rfl) ⟨62058, by rfl⟩ : syracuseStep 2647829 = 124117) (by norm_num)
theorem B3974933 : Blo 1568982 3974933 := bbase (se 6 (by rfl) ⟨93162, by rfl⟩ : syracuseStep 3974933 = 186325) (by norm_num)
theorem B3532589 : Blo 1568982 3532589 := bbase (se 3 (by rfl) ⟨662360, by rfl⟩ : syracuseStep 3532589 = 1324721) (by norm_num)
theorem B6367045 : Blo 1568982 6367045 := bbase (se 4 (by rfl) ⟨596910, by rfl⟩ : syracuseStep 6367045 = 1193821) (by norm_num)
theorem B3532661 : Blo 1568982 3532661 := bbase (se 5 (by rfl) ⟨165593, by rfl⟩ : syracuseStep 3532661 = 331187) (by norm_num)
theorem B5957509 : Blo 1568982 5957509 := bbase (se 4 (by rfl) ⟨558516, by rfl⟩ : syracuseStep 5957509 = 1117033) (by norm_num)
theorem B2647957 : Blo 1568982 2647957 := bbase (se 6 (by rfl) ⟨62061, by rfl⟩ : syracuseStep 2647957 = 124123) (by norm_num)
theorem B10053557 : Blo 1568982 10053557 := bbase (se 5 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 10053557 = 942521) (by norm_num)
theorem B3532733 : Blo 1568982 3532733 := bbase (se 3 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 3532733 = 1324775) (by norm_num)
theorem B5031877 : Blo 1568982 5031877 := bbase (se 4 (by rfl) ⟨471738, by rfl⟩ : syracuseStep 5031877 = 943477) (by norm_num)
theorem B1886185 : Blo 1568982 1886185 := bbase (se 2 (by rfl) ⟨707319, by rfl⟩ : syracuseStep 1886185 = 1414639) (by norm_num)
theorem B2648045 : Blo 1568982 2648045 := bbase (se 3 (by rfl) ⟨496508, by rfl⟩ : syracuseStep 2648045 = 993017) (by norm_num)
theorem B3532805 : Blo 1568982 3532805 := bbase (se 4 (by rfl) ⟨331200, by rfl⟩ : syracuseStep 3532805 = 662401) (by norm_num)
theorem B20400149 : Blo 1568982 20400149 := bbase (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) (by norm_num)
theorem B3352637 : Blo 1568982 3352637 := bbase (se 3 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 3352637 = 1257239) (by norm_num)
theorem B2721853 : Blo 1568982 2721853 := bbase (se 3 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 2721853 = 1020695) (by norm_num)
theorem B3532877 : Blo 1568982 3532877 := bbase (se 3 (by rfl) ⟨662414, by rfl⟩ : syracuseStep 3532877 = 1324829) (by norm_num)
theorem B2041933 : Blo 1568982 2041933 := bbase (se 3 (by rfl) ⟨382862, by rfl⟩ : syracuseStep 2041933 = 765725) (by norm_num)
theorem B4245605 : Blo 1568982 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2648173 : Blo 1568982 2648173 := bbase (se 3 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 2648173 = 993065) (by norm_num)
theorem B3975277 : Blo 1568982 3975277 := bbase (se 3 (by rfl) ⟨745364, by rfl⟩ : syracuseStep 3975277 = 1490729) (by norm_num)
theorem B1591445 : Blo 1568982 1591445 := bbase (se 6 (by rfl) ⟨37299, by rfl⟩ : syracuseStep 1591445 = 74599) (by norm_num)
theorem B3532949 : Blo 1568982 3532949 := bbase (se 6 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 3532949 = 165607) (by norm_num)
theorem B5957813 : Blo 1568982 5957813 := bbase (se 5 (by rfl) ⟨279272, by rfl⟩ : syracuseStep 5957813 = 558545) (by norm_num)
theorem B2648261 : Blo 1568982 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B3533021 : Blo 1568982 3533021 := bbase (se 3 (by rfl) ⟨662441, by rfl⟩ : syracuseStep 3533021 = 1324883) (by norm_num)
theorem B3975389 : Blo 1568982 3975389 := bbase (se 3 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 3975389 = 1490771) (by norm_num)
theorem B3533093 : Blo 1568982 3533093 := bbase (se 4 (by rfl) ⟨331227, by rfl⟩ : syracuseStep 3533093 = 662455) (by norm_num)
theorem B2648389 : Blo 1568982 2648389 := bbase (se 4 (by rfl) ⟨248286, by rfl⟩ : syracuseStep 2648389 = 496573) (by norm_num)
theorem B2353493 : Blo 1568982 2353493 := bbase (se 10 (by rfl) ⟨3447, by rfl⟩ : syracuseStep 2353493 = 6895) (by norm_num)
theorem B5032277 : Blo 1568982 5032277 := bbase (se 10 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 5032277 = 14743) (by norm_num)
theorem B2353517 : Blo 1568982 2353517 := bbase (se 3 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 2353517 = 882569) (by norm_num)
theorem B3533165 : Blo 1568982 3533165 := bbase (se 3 (by rfl) ⟨662468, by rfl⟩ : syracuseStep 3533165 = 1324937) (by norm_num)
theorem B2353541 : Blo 1568982 2353541 := bbase (se 4 (by rfl) ⟨220644, by rfl⟩ : syracuseStep 2353541 = 441289) (by norm_num)
theorem B2353565 : Blo 1568982 2353565 := bbase (se 3 (by rfl) ⟨441293, by rfl⟩ : syracuseStep 2353565 = 882587) (by norm_num)
theorem B2648477 : Blo 1568982 2648477 := bbase (se 3 (by rfl) ⟨496589, by rfl⟩ : syracuseStep 2648477 = 993179) (by norm_num)
theorem B2828701 : Blo 1568982 2828701 := bbase (se 3 (by rfl) ⟨530381, by rfl⟩ : syracuseStep 2828701 = 1060763) (by norm_num)
theorem B3975581 : Blo 1568982 3975581 := bbase (se 3 (by rfl) ⟨745421, by rfl⟩ : syracuseStep 3975581 = 1490843) (by norm_num)
theorem B3353005 : Blo 1568982 3353005 := bbase (se 3 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 3353005 = 1257377) (by norm_num)
theorem B2353589 : Blo 1568982 2353589 := bbase (se 5 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 2353589 = 220649) (by norm_num)
theorem B3533237 : Blo 1568982 3533237 := bbase (se 5 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 3533237 = 331241) (by norm_num)
theorem B2353613 : Blo 1568982 2353613 := bbase (se 3 (by rfl) ⟨441302, by rfl⟩ : syracuseStep 2353613 = 882605) (by norm_num)
theorem B3582413 : Blo 1568982 3582413 := bbase (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) (by norm_num)
theorem B2353637 : Blo 1568982 2353637 := bbase (se 4 (by rfl) ⟨220653, by rfl⟩ : syracuseStep 2353637 = 441307) (by norm_num)
theorem B2353661 : Blo 1568982 2353661 := bbase (se 3 (by rfl) ⟨441311, by rfl⟩ : syracuseStep 2353661 = 882623) (by norm_num)
theorem B3533309 : Blo 1568982 3533309 := bbase (se 3 (by rfl) ⟨662495, by rfl⟩ : syracuseStep 3533309 = 1324991) (by norm_num)
theorem B2353685 : Blo 1568982 2353685 := bbase (se 6 (by rfl) ⟨55164, by rfl⟩ : syracuseStep 2353685 = 110329) (by norm_num)
theorem B2648605 : Blo 1568982 2648605 := bbase (se 3 (by rfl) ⟨496613, by rfl⟩ : syracuseStep 2648605 = 993227) (by norm_num)
theorem B2353709 : Blo 1568982 2353709 := bbase (se 3 (by rfl) ⟨441320, by rfl⟩ : syracuseStep 2353709 = 882641) (by norm_num)
theorem B7948853 : Blo 1568982 7948853 := bbase (se 5 (by rfl) ⟨372602, by rfl⟩ : syracuseStep 7948853 = 745205) (by norm_num)
theorem B2353733 : Blo 1568982 2353733 := bbase (se 4 (by rfl) ⟨220662, by rfl⟩ : syracuseStep 2353733 = 441325) (by norm_num)
theorem B3533381 : Blo 1568982 3533381 := bbase (se 4 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 3533381 = 662509) (by norm_num)
theorem B2353757 : Blo 1568982 2353757 := bbase (se 3 (by rfl) ⟨441329, by rfl⟩ : syracuseStep 2353757 = 882659) (by norm_num)
theorem B2353781 : Blo 1568982 2353781 := bbase (se 5 (by rfl) ⟨110333, by rfl⟩ : syracuseStep 2353781 = 220667) (by norm_num)
theorem B2648693 : Blo 1568982 2648693 := bbase (se 5 (by rfl) ⟨124157, by rfl⟩ : syracuseStep 2648693 = 248315) (by norm_num)
theorem B2353805 : Blo 1568982 2353805 := bbase (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) (by norm_num)
theorem B3533453 : Blo 1568982 3533453 := bbase (se 3 (by rfl) ⟨662522, by rfl⟩ : syracuseStep 3533453 = 1325045) (by norm_num)
theorem B2353829 : Blo 1568982 2353829 := bbase (se 4 (by rfl) ⟨220671, by rfl⟩ : syracuseStep 2353829 = 441343) (by norm_num)
theorem B15092405 : Blo 1568982 15092405 := bbase (se 5 (by rfl) ⟨707456, by rfl⟩ : syracuseStep 15092405 = 1414913) (by norm_num)
theorem B2353853 : Blo 1568982 2353853 := bbase (se 3 (by rfl) ⟨441347, by rfl⟩ : syracuseStep 2353853 = 882695) (by norm_num)
theorem B3631805 : Blo 1568982 3631805 := bbase (se 3 (by rfl) ⟨680963, by rfl⟩ : syracuseStep 3631805 = 1361927) (by norm_num)
theorem B2353877 : Blo 1568982 2353877 := bbase (se 7 (by rfl) ⟨27584, by rfl⟩ : syracuseStep 2353877 = 55169) (by norm_num)
theorem B3533525 : Blo 1568982 3533525 := bbase (se 7 (by rfl) ⟨41408, by rfl⟩ : syracuseStep 3533525 = 82817) (by norm_num)
theorem B2353901 : Blo 1568982 2353901 := bbase (se 3 (by rfl) ⟨441356, by rfl⟩ : syracuseStep 2353901 = 882713) (by norm_num)
theorem B2648821 : Blo 1568982 2648821 := bbase (se 5 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 2648821 = 248327) (by norm_num)
theorem B3975925 : Blo 1568982 3975925 := bbase (se 5 (by rfl) ⟨186371, by rfl⟩ : syracuseStep 3975925 = 372743) (by norm_num)
theorem B2353925 : Blo 1568982 2353925 := bbase (se 4 (by rfl) ⟨220680, by rfl⟩ : syracuseStep 2353925 = 441361) (by norm_num)
theorem B2353949 : Blo 1568982 2353949 := bbase (se 3 (by rfl) ⟨441365, by rfl⟩ : syracuseStep 2353949 = 882731) (by norm_num)
theorem B3533597 : Blo 1568982 3533597 := bbase (se 3 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 3533597 = 1325099) (by norm_num)
theorem B2353973 : Blo 1568982 2353973 := bbase (se 5 (by rfl) ⟨110342, by rfl⟩ : syracuseStep 2353973 = 220685) (by norm_num)
theorem B2353997 : Blo 1568982 2353997 := bbase (se 3 (by rfl) ⟨441374, by rfl⟩ : syracuseStep 2353997 = 882749) (by norm_num)
theorem B2648909 : Blo 1568982 2648909 := bbase (se 3 (by rfl) ⟨496670, by rfl⟩ : syracuseStep 2648909 = 993341) (by norm_num)
theorem B13405013 : Blo 1568982 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B2354021 : Blo 1568982 2354021 := bbase (se 4 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 2354021 = 441379) (by norm_num)
theorem B3533669 : Blo 1568982 3533669 := bbase (se 4 (by rfl) ⟨331281, by rfl⟩ : syracuseStep 3533669 = 662563) (by norm_num)
theorem B3976037 : Blo 1568982 3976037 := bbase (se 4 (by rfl) ⟨372753, by rfl⟩ : syracuseStep 3976037 = 745507) (by norm_num)
theorem B5368693 : Blo 1568982 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B2354045 : Blo 1568982 2354045 := bbase (se 3 (by rfl) ⟨441383, by rfl⟩ : syracuseStep 2354045 = 882767) (by norm_num)
theorem B2354069 : Blo 1568982 2354069 := bbase (se 6 (by rfl) ⟨55173, by rfl⟩ : syracuseStep 2354069 = 110347) (by norm_num)
theorem B9677717 : Blo 1568982 9677717 := bbase (se 6 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 9677717 = 453643) (by norm_num)
theorem B4533157 : Blo 1568982 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B2354093 : Blo 1568982 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B3533741 : Blo 1568982 3533741 := bbase (se 3 (by rfl) ⟨662576, by rfl⟩ : syracuseStep 3533741 = 1325153) (by norm_num)
theorem B8489909 : Blo 1568982 8489909 := bbase (se 5 (by rfl) ⟨397964, by rfl⟩ : syracuseStep 8489909 = 795929) (by norm_num)
theorem B2354117 : Blo 1568982 2354117 := bbase (se 4 (by rfl) ⟨220698, by rfl⟩ : syracuseStep 2354117 = 441397) (by norm_num)
theorem B2649037 : Blo 1568982 2649037 := bbase (se 3 (by rfl) ⟨496694, by rfl⟩ : syracuseStep 2649037 = 993389) (by norm_num)
theorem B1887185 : Blo 1568982 1887185 := bbase (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) (by norm_num)
theorem B2354141 : Blo 1568982 2354141 := bbase (se 3 (by rfl) ⟨441401, by rfl⟩ : syracuseStep 2354141 = 882803) (by norm_num)
theorem B2354165 : Blo 1568982 2354165 := bbase (se 5 (by rfl) ⟨110351, by rfl⟩ : syracuseStep 2354165 = 220703) (by norm_num)
theorem B3533813 : Blo 1568982 3533813 := bbase (se 5 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 3533813 = 331295) (by norm_num)
theorem B1887233 : Blo 1568982 1887233 := bbase (se 2 (by rfl) ⟨707712, by rfl⟩ : syracuseStep 1887233 = 1415425) (by norm_num)
theorem B5655557 : Blo 1568982 5655557 := bbase (se 4 (by rfl) ⟨530208, by rfl⟩ : syracuseStep 5655557 = 1060417) (by norm_num)
theorem B2354189 : Blo 1568982 2354189 := bbase (se 3 (by rfl) ⟨441410, by rfl⟩ : syracuseStep 2354189 = 882821) (by norm_num)
theorem B1592341 : Blo 1568982 1592341 := bbase (se 6 (by rfl) ⟨37320, by rfl⟩ : syracuseStep 1592341 = 74641) (by norm_num)
theorem B2386973 : Blo 1568982 2386973 := bbase (se 3 (by rfl) ⟨447557, by rfl⟩ : syracuseStep 2386973 = 895115) (by norm_num)
theorem B2354213 : Blo 1568982 2354213 := bbase (se 4 (by rfl) ⟨220707, by rfl⟩ : syracuseStep 2354213 = 441415) (by norm_num)
theorem B2649125 : Blo 1568982 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B3976229 : Blo 1568982 3976229 := bbase (se 4 (by rfl) ⟨372771, by rfl⟩ : syracuseStep 3976229 = 745543) (by norm_num)
theorem B13593653 : Blo 1568982 13593653 := bbase (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) (by norm_num)
theorem B2354237 : Blo 1568982 2354237 := bbase (se 3 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 2354237 = 882839) (by norm_num)
theorem B3533885 : Blo 1568982 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B12725333 : Blo 1568982 12725333 := bbase (se 8 (by rfl) ⟨74562, by rfl⟩ : syracuseStep 12725333 = 149125) (by norm_num)
theorem B2354261 : Blo 1568982 2354261 := bbase (se 8 (by rfl) ⟨13794, by rfl⟩ : syracuseStep 2354261 = 27589) (by norm_num)
theorem B2354285 : Blo 1568982 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B2354309 : Blo 1568982 2354309 := bbase (se 4 (by rfl) ⟨220716, by rfl⟩ : syracuseStep 2354309 = 441433) (by norm_num)
theorem B3533957 : Blo 1568982 3533957 := bbase (se 4 (by rfl) ⟨331308, by rfl⟩ : syracuseStep 3533957 = 662617) (by norm_num)
theorem B19106965 : Blo 1568982 19106965 := bbase (se 6 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 19106965 = 895639) (by norm_num)
theorem B2354333 : Blo 1568982 2354333 := bbase (se 3 (by rfl) ⟨441437, by rfl⟩ : syracuseStep 2354333 = 882875) (by norm_num)
theorem B2649253 : Blo 1568982 2649253 := bbase (se 4 (by rfl) ⟨248367, by rfl⟩ : syracuseStep 2649253 = 496735) (by norm_num)
theorem B2354357 : Blo 1568982 2354357 := bbase (se 5 (by rfl) ⟨110360, by rfl⟩ : syracuseStep 2354357 = 220721) (by norm_num)
theorem B2829509 : Blo 1568982 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B2354381 : Blo 1568982 2354381 := bbase (se 3 (by rfl) ⟨441446, by rfl⟩ : syracuseStep 2354381 = 882893) (by norm_num)
theorem B3534029 : Blo 1568982 3534029 := bbase (se 3 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 3534029 = 1325261) (by norm_num)
theorem B30190805 : Blo 1568982 30190805 := bbase (se 7 (by rfl) ⟨353798, by rfl⟩ : syracuseStep 30190805 = 707597) (by norm_num)
theorem B2354405 : Blo 1568982 2354405 := bbase (se 4 (by rfl) ⟨220725, by rfl⟩ : syracuseStep 2354405 = 441451) (by norm_num)
theorem B2354429 : Blo 1568982 2354429 := bbase (se 3 (by rfl) ⟨441455, by rfl⟩ : syracuseStep 2354429 = 882911) (by norm_num)
theorem B2649341 : Blo 1568982 2649341 := bbase (se 3 (by rfl) ⟨496751, by rfl⟩ : syracuseStep 2649341 = 993503) (by norm_num)
theorem B4467973 : Blo 1568982 4467973 := bbase (se 4 (by rfl) ⟨418872, by rfl⟩ : syracuseStep 4467973 = 837745) (by norm_num)
theorem B2354453 : Blo 1568982 2354453 := bbase (se 6 (by rfl) ⟨55182, by rfl⟩ : syracuseStep 2354453 = 110365) (by norm_num)
theorem B3534101 : Blo 1568982 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B2354477 : Blo 1568982 2354477 := bbase (se 3 (by rfl) ⟨441464, by rfl⟩ : syracuseStep 2354477 = 882929) (by norm_num)
theorem B2354501 : Blo 1568982 2354501 := bbase (se 4 (by rfl) ⟨220734, by rfl⟩ : syracuseStep 2354501 = 441469) (by norm_num)
theorem B2354525 : Blo 1568982 2354525 := bbase (se 3 (by rfl) ⟨441473, by rfl⟩ : syracuseStep 2354525 = 882947) (by norm_num)
theorem B3534173 : Blo 1568982 3534173 := bbase (se 3 (by rfl) ⟨662657, by rfl⟩ : syracuseStep 3534173 = 1325315) (by norm_num)
theorem B1985897 : Blo 1568982 1985897 := bbase (se 2 (by rfl) ⟨744711, by rfl⟩ : syracuseStep 1985897 = 1489423) (by norm_num)
theorem B2354549 : Blo 1568982 2354549 := bbase (se 5 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 2354549 = 220739) (by norm_num)
theorem B2649469 : Blo 1568982 2649469 := bbase (se 3 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 2649469 = 993551) (by norm_num)
theorem B2354573 : Blo 1568982 2354573 := bbase (se 3 (by rfl) ⟨441482, by rfl⟩ : syracuseStep 2354573 = 882965) (by norm_num)
theorem B5295509 : Blo 1568982 5295509 := bbase (se 6 (by rfl) ⟨124113, by rfl⟩ : syracuseStep 5295509 = 248227) (by norm_num)
theorem B1985953 : Blo 1568982 1985953 := bbase (se 2 (by rfl) ⟨744732, by rfl⟩ : syracuseStep 1985953 = 1489465) (by norm_num)
theorem B2354597 : Blo 1568982 2354597 := bbase (se 4 (by rfl) ⟨220743, by rfl⟩ : syracuseStep 2354597 = 441487) (by norm_num)
theorem B3534245 : Blo 1568982 3534245 := bbase (se 4 (by rfl) ⟨331335, by rfl⟩ : syracuseStep 3534245 = 662671) (by norm_num)
theorem B2354621 : Blo 1568982 2354621 := bbase (se 3 (by rfl) ⟨441491, by rfl⟩ : syracuseStep 2354621 = 882983) (by norm_num)
theorem B2354645 : Blo 1568982 2354645 := bbase (se 7 (by rfl) ⟨27593, by rfl⟩ : syracuseStep 2354645 = 55187) (by norm_num)
theorem B2649557 : Blo 1568982 2649557 := bbase (se 7 (by rfl) ⟨31049, by rfl⟩ : syracuseStep 2649557 = 62099) (by norm_num)
theorem B2354669 : Blo 1568982 2354669 := bbase (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) (by norm_num)
theorem B3534317 : Blo 1568982 3534317 := bbase (se 3 (by rfl) ⟨662684, by rfl⟩ : syracuseStep 3534317 = 1325369) (by norm_num)
theorem B1986049 : Blo 1568982 1986049 := bbase (se 2 (by rfl) ⟨744768, by rfl⟩ : syracuseStep 1986049 = 1489537) (by norm_num)
theorem B2354693 : Blo 1568982 2354693 := bbase (se 4 (by rfl) ⟨220752, by rfl⟩ : syracuseStep 2354693 = 441505) (by norm_num)
theorem B2354717 : Blo 1568982 2354717 := bbase (se 3 (by rfl) ⟨441509, by rfl⟩ : syracuseStep 2354717 = 883019) (by norm_num)
theorem B2354741 : Blo 1568982 2354741 := bbase (se 5 (by rfl) ⟨110378, by rfl⟩ : syracuseStep 2354741 = 220757) (by norm_num)
theorem B3534389 : Blo 1568982 3534389 := bbase (se 5 (by rfl) ⟨165674, by rfl⟩ : syracuseStep 3534389 = 331349) (by norm_num)
theorem B2354765 : Blo 1568982 2354765 := bbase (se 3 (by rfl) ⟨441518, by rfl⟩ : syracuseStep 2354765 = 883037) (by norm_num)
theorem B2649685 : Blo 1568982 2649685 := bbase (se 8 (by rfl) ⟨15525, by rfl⟩ : syracuseStep 2649685 = 31051) (by norm_num)
theorem B2354789 : Blo 1568982 2354789 := bbase (se 4 (by rfl) ⟨220761, by rfl⟩ : syracuseStep 2354789 = 441523) (by norm_num)
theorem B2354813 : Blo 1568982 2354813 := bbase (se 3 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 2354813 = 883055) (by norm_num)
theorem B3534461 : Blo 1568982 3534461 := bbase (se 3 (by rfl) ⟨662711, by rfl⟩ : syracuseStep 3534461 = 1325423) (by norm_num)
theorem B2354837 : Blo 1568982 2354837 := bbase (se 6 (by rfl) ⟨55191, by rfl⟩ : syracuseStep 2354837 = 110383) (by norm_num)
theorem B1986221 : Blo 1568982 1986221 := bbase (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) (by norm_num)
theorem B2354861 : Blo 1568982 2354861 := bbase (se 3 (by rfl) ⟨441536, by rfl⟩ : syracuseStep 2354861 = 883073) (by norm_num)
theorem B2649773 : Blo 1568982 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B2354885 : Blo 1568982 2354885 := bbase (se 4 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 2354885 = 441541) (by norm_num)
theorem B3534533 : Blo 1568982 3534533 := bbase (se 4 (by rfl) ⟨331362, by rfl⟩ : syracuseStep 3534533 = 662725) (by norm_num)
theorem B2354909 : Blo 1568982 2354909 := bbase (se 3 (by rfl) ⟨441545, by rfl⟩ : syracuseStep 2354909 = 883091) (by norm_num)
theorem B1986277 : Blo 1568982 1986277 := bbase (se 4 (by rfl) ⟨186213, by rfl⟩ : syracuseStep 1986277 = 372427) (by norm_num)
theorem B2354933 : Blo 1568982 2354933 := bbase (se 5 (by rfl) ⟨110387, by rfl⟩ : syracuseStep 2354933 = 220775) (by norm_num)
theorem B1765129 : Blo 1568982 1765129 := bbase (se 2 (by rfl) ⟨661923, by rfl⟩ : syracuseStep 1765129 = 1323847) (by norm_num)
theorem B2354957 : Blo 1568982 2354957 := bbase (se 3 (by rfl) ⟨441554, by rfl⟩ : syracuseStep 2354957 = 883109) (by norm_num)
theorem B3534605 : Blo 1568982 3534605 := bbase (se 3 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 3534605 = 1325477) (by norm_num)
theorem B2354981 : Blo 1568982 2354981 := bbase (se 4 (by rfl) ⟨220779, by rfl⟩ : syracuseStep 2354981 = 441559) (by norm_num)
theorem B1765165 : Blo 1568982 1765165 := bbase (se 3 (by rfl) ⟨330968, by rfl⟩ : syracuseStep 1765165 = 661937) (by norm_num)
theorem B2649901 : Blo 1568982 2649901 := bbase (se 3 (by rfl) ⟨496856, by rfl⟩ : syracuseStep 2649901 = 993713) (by norm_num)
theorem B2355005 : Blo 1568982 2355005 := bbase (se 3 (by rfl) ⟨441563, by rfl⟩ : syracuseStep 2355005 = 883127) (by norm_num)
theorem B5295941 : Blo 1568982 5295941 := bbase (se 4 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 5295941 = 992989) (by norm_num)
theorem B1986373 : Blo 1568982 1986373 := bbase (se 4 (by rfl) ⟨186222, by rfl⟩ : syracuseStep 1986373 = 372445) (by norm_num)
theorem B7950149 : Blo 1568982 7950149 := bbase (se 4 (by rfl) ⟨745326, by rfl⟩ : syracuseStep 7950149 = 1490653) (by norm_num)
theorem B1765201 : Blo 1568982 1765201 := bbase (se 2 (by rfl) ⟨661950, by rfl⟩ : syracuseStep 1765201 = 1323901) (by norm_num)
theorem B2355029 : Blo 1568982 2355029 := bbase (se 9 (by rfl) ⟨6899, by rfl⟩ : syracuseStep 2355029 = 13799) (by norm_num)
theorem B3534677 : Blo 1568982 3534677 := bbase (se 9 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 3534677 = 20711) (by norm_num)
theorem B2355053 : Blo 1568982 2355053 := bbase (se 3 (by rfl) ⟨441572, by rfl⟩ : syracuseStep 2355053 = 883145) (by norm_num)
theorem B1765237 : Blo 1568982 1765237 := bbase (se 5 (by rfl) ⟨82745, by rfl⟩ : syracuseStep 1765237 = 165491) (by norm_num)
theorem B2355077 : Blo 1568982 2355077 := bbase (se 4 (by rfl) ⟨220788, by rfl⟩ : syracuseStep 2355077 = 441577) (by norm_num)
theorem B2649989 : Blo 1568982 2649989 := bbase (se 4 (by rfl) ⟨248436, by rfl⟩ : syracuseStep 2649989 = 496873) (by norm_num)
theorem B3354509 : Blo 1568982 3354509 := bbase (se 3 (by rfl) ⟨628970, by rfl⟩ : syracuseStep 3354509 = 1257941) (by norm_num)
theorem B1765273 : Blo 1568982 1765273 := bbase (se 2 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 1765273 = 1323955) (by norm_num)
theorem B2355101 : Blo 1568982 2355101 := bbase (se 3 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 2355101 = 883163) (by norm_num)
theorem B2387885 : Blo 1568982 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B2355125 : Blo 1568982 2355125 := bbase (se 5 (by rfl) ⟨110396, by rfl⟩ : syracuseStep 2355125 = 220793) (by norm_num)
theorem B3821501 : Blo 1568982 3821501 := bbase (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) (by norm_num)
theorem B1765309 : Blo 1568982 1765309 := bbase (se 3 (by rfl) ⟨330995, by rfl⟩ : syracuseStep 1765309 = 661991) (by norm_num)
theorem B4771781 : Blo 1568982 4771781 := bbase (se 4 (by rfl) ⟨447354, by rfl⟩ : syracuseStep 4771781 = 894709) (by norm_num)
theorem B2355149 : Blo 1568982 2355149 := bbase (se 3 (by rfl) ⟨441590, by rfl⟩ : syracuseStep 2355149 = 883181) (by norm_num)
theorem B1765345 : Blo 1568982 1765345 := bbase (se 2 (by rfl) ⟨662004, by rfl⟩ : syracuseStep 1765345 = 1324009) (by norm_num)
theorem B2355173 : Blo 1568982 2355173 := bbase (se 4 (by rfl) ⟨220797, by rfl⟩ : syracuseStep 2355173 = 441595) (by norm_num)
theorem B1986545 : Blo 1568982 1986545 := bbase (se 2 (by rfl) ⟨744954, by rfl⟩ : syracuseStep 1986545 = 1489909) (by norm_num)
theorem B2355197 : Blo 1568982 2355197 := bbase (se 3 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 2355197 = 883199) (by norm_num)
theorem B1765381 : Blo 1568982 1765381 := bbase (se 4 (by rfl) ⟨165504, by rfl⟩ : syracuseStep 1765381 = 331009) (by norm_num)
theorem B2650117 : Blo 1568982 2650117 := bbase (se 4 (by rfl) ⟨248448, by rfl⟩ : syracuseStep 2650117 = 496897) (by norm_num)
theorem B2355221 : Blo 1568982 2355221 := bbase (se 6 (by rfl) ⟨55200, by rfl⟩ : syracuseStep 2355221 = 110401) (by norm_num)
theorem B3354653 : Blo 1568982 3354653 := bbase (se 3 (by rfl) ⟨628997, by rfl⟩ : syracuseStep 3354653 = 1257995) (by norm_num)
theorem B1765417 : Blo 1568982 1765417 := bbase (se 2 (by rfl) ⟨662031, by rfl⟩ : syracuseStep 1765417 = 1324063) (by norm_num)
theorem B1986601 : Blo 1568982 1986601 := bbase (se 2 (by rfl) ⟨744975, by rfl⟩ : syracuseStep 1986601 = 1489951) (by norm_num)
theorem B2355245 : Blo 1568982 2355245 := bbase (se 3 (by rfl) ⟨441608, by rfl⟩ : syracuseStep 2355245 = 883217) (by norm_num)
theorem B2355269 : Blo 1568982 2355269 := bbase (se 4 (by rfl) ⟨220806, by rfl⟩ : syracuseStep 2355269 = 441613) (by norm_num)
theorem B1765453 : Blo 1568982 1765453 := bbase (se 3 (by rfl) ⟨331022, by rfl⟩ : syracuseStep 1765453 = 662045) (by norm_num)
theorem B2355293 : Blo 1568982 2355293 := bbase (se 3 (by rfl) ⟨441617, by rfl⟩ : syracuseStep 2355293 = 883235) (by norm_num)
theorem B2650205 : Blo 1568982 2650205 := bbase (se 3 (by rfl) ⟨496913, by rfl⟩ : syracuseStep 2650205 = 993827) (by norm_num)
theorem B1765489 : Blo 1568982 1765489 := bbase (se 2 (by rfl) ⟨662058, by rfl⟩ : syracuseStep 1765489 = 1324117) (by norm_num)
theorem B2355317 : Blo 1568982 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B12087413 : Blo 1568982 12087413 := bbase (se 5 (by rfl) ⟨566597, by rfl⟩ : syracuseStep 12087413 = 1133195) (by norm_num)
theorem B1986697 : Blo 1568982 1986697 := bbase (se 2 (by rfl) ⟨745011, by rfl⟩ : syracuseStep 1986697 = 1490023) (by norm_num)
theorem B2355341 : Blo 1568982 2355341 := bbase (se 3 (by rfl) ⟨441626, by rfl⟩ : syracuseStep 2355341 = 883253) (by norm_num)
theorem B1765525 : Blo 1568982 1765525 := bbase (se 6 (by rfl) ⟨41379, by rfl⟩ : syracuseStep 1765525 = 82759) (by norm_num)
theorem B2355365 : Blo 1568982 2355365 := bbase (se 4 (by rfl) ⟨220815, by rfl⟩ : syracuseStep 2355365 = 441631) (by norm_num)
theorem B1765561 : Blo 1568982 1765561 := bbase (se 2 (by rfl) ⟨662085, by rfl⟩ : syracuseStep 1765561 = 1324171) (by norm_num)
theorem B2355389 : Blo 1568982 2355389 := bbase (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) (by norm_num)
theorem B2355413 : Blo 1568982 2355413 := bbase (se 7 (by rfl) ⟨27602, by rfl⟩ : syracuseStep 2355413 = 55205) (by norm_num)
theorem B1765597 : Blo 1568982 1765597 := bbase (se 3 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 1765597 = 662099) (by norm_num)
theorem B2650333 : Blo 1568982 2650333 := bbase (se 3 (by rfl) ⟨496937, by rfl⟩ : syracuseStep 2650333 = 993875) (by norm_num)
theorem B6369509 : Blo 1568982 6369509 := bbase (se 4 (by rfl) ⟨597141, by rfl⟩ : syracuseStep 6369509 = 1194283) (by norm_num)
theorem B2355437 : Blo 1568982 2355437 := bbase (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) (by norm_num)
theorem B5296373 : Blo 1568982 5296373 := bbase (se 5 (by rfl) ⟨248267, by rfl⟩ : syracuseStep 5296373 = 496535) (by norm_num)
theorem B5959925 : Blo 1568982 5959925 := bbase (se 5 (by rfl) ⟨279371, by rfl⟩ : syracuseStep 5959925 = 558743) (by norm_num)
theorem B1765633 : Blo 1568982 1765633 := bbase (se 2 (by rfl) ⟨662112, by rfl⟩ : syracuseStep 1765633 = 1324225) (by norm_num)
theorem B2355461 : Blo 1568982 2355461 := bbase (se 4 (by rfl) ⟨220824, by rfl⟩ : syracuseStep 2355461 = 441649) (by norm_num)
theorem B2355485 : Blo 1568982 2355485 := bbase (se 3 (by rfl) ⟨441653, by rfl⟩ : syracuseStep 2355485 = 883307) (by norm_num)
theorem B1765669 : Blo 1568982 1765669 := bbase (se 4 (by rfl) ⟨165531, by rfl⟩ : syracuseStep 1765669 = 331063) (by norm_num)
theorem B1790257 : Blo 1568982 1790257 := bbase (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) (by norm_num)
theorem B1986869 : Blo 1568982 1986869 := bbase (se 5 (by rfl) ⟨93134, by rfl⟩ : syracuseStep 1986869 = 186269) (by norm_num)
theorem B2355509 : Blo 1568982 2355509 := bbase (se 5 (by rfl) ⟨110414, by rfl⟩ : syracuseStep 2355509 = 220829) (by norm_num)
theorem B2650421 : Blo 1568982 2650421 := bbase (se 5 (by rfl) ⟨124238, by rfl⟩ : syracuseStep 2650421 = 248477) (by norm_num)
theorem B1765705 : Blo 1568982 1765705 := bbase (se 2 (by rfl) ⟨662139, by rfl⟩ : syracuseStep 1765705 = 1324279) (by norm_num)
theorem B2355533 : Blo 1568982 2355533 := bbase (se 3 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 2355533 = 883325) (by norm_num)
theorem B48329045 : Blo 1568982 48329045 := bbase (se 10 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 48329045 = 141589) (by norm_num)
theorem B2355557 : Blo 1568982 2355557 := bbase (se 4 (by rfl) ⟨220833, by rfl⟩ : syracuseStep 2355557 = 441667) (by norm_num)
theorem B1765741 : Blo 1568982 1765741 := bbase (se 3 (by rfl) ⟨331076, by rfl⟩ : syracuseStep 1765741 = 662153) (by norm_num)
theorem B1986925 : Blo 1568982 1986925 := bbase (se 3 (by rfl) ⟨372548, by rfl⟩ : syracuseStep 1986925 = 745097) (by norm_num)
theorem B2355581 : Blo 1568982 2355581 := bbase (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) (by norm_num)
theorem B1700221 : Blo 1568982 1700221 := bbase (se 3 (by rfl) ⟨318791, by rfl⟩ : syracuseStep 1700221 = 637583) (by norm_num)
theorem B3355013 : Blo 1568982 3355013 := bbase (se 4 (by rfl) ⟨314532, by rfl⟩ : syracuseStep 3355013 = 629065) (by norm_num)
theorem B1765777 : Blo 1568982 1765777 := bbase (se 2 (by rfl) ⟨662166, by rfl⟩ : syracuseStep 1765777 = 1324333) (by norm_num)
theorem B2355605 : Blo 1568982 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B2355629 : Blo 1568982 2355629 := bbase (se 3 (by rfl) ⟨441680, by rfl⟩ : syracuseStep 2355629 = 883361) (by norm_num)
theorem B1765813 : Blo 1568982 1765813 := bbase (se 5 (by rfl) ⟨82772, by rfl⟩ : syracuseStep 1765813 = 165545) (by norm_num)
theorem B2650549 : Blo 1568982 2650549 := bbase (se 5 (by rfl) ⟨124244, by rfl⟩ : syracuseStep 2650549 = 248489) (by norm_num)
theorem B2355653 : Blo 1568982 2355653 := bbase (se 4 (by rfl) ⟨220842, by rfl⟩ : syracuseStep 2355653 = 441685) (by norm_num)
theorem B1987021 : Blo 1568982 1987021 := bbase (se 3 (by rfl) ⟨372566, by rfl⟩ : syracuseStep 1987021 = 745133) (by norm_num)
theorem B1765849 : Blo 1568982 1765849 := bbase (se 2 (by rfl) ⟨662193, by rfl⟩ : syracuseStep 1765849 = 1324387) (by norm_num)
theorem B2355677 : Blo 1568982 2355677 := bbase (se 3 (by rfl) ⟨441689, by rfl⟩ : syracuseStep 2355677 = 883379) (by norm_num)
theorem B3183085 : Blo 1568982 3183085 := bbase (se 3 (by rfl) ⟨596828, by rfl⟩ : syracuseStep 3183085 = 1193657) (by norm_num)
theorem B3772909 : Blo 1568982 3772909 := bbase (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) (by norm_num)
theorem B11473397 : Blo 1568982 11473397 := bbase (se 5 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 11473397 = 1075631) (by norm_num)
theorem B2355701 : Blo 1568982 2355701 := bbase (se 5 (by rfl) ⟨110423, by rfl⟩ : syracuseStep 2355701 = 220847) (by norm_num)
theorem B1765885 : Blo 1568982 1765885 := bbase (se 3 (by rfl) ⟨331103, by rfl⟩ : syracuseStep 1765885 = 662207) (by norm_num)
theorem B2355725 : Blo 1568982 2355725 := bbase (se 3 (by rfl) ⟨441698, by rfl⟩ : syracuseStep 2355725 = 883397) (by norm_num)
theorem B2650637 : Blo 1568982 2650637 := bbase (se 3 (by rfl) ⟨496994, by rfl⟩ : syracuseStep 2650637 = 993989) (by norm_num)
theorem B5960213 : Blo 1568982 5960213 := bbase (se 6 (by rfl) ⟨139692, by rfl⟩ : syracuseStep 5960213 = 279385) (by norm_num)
theorem B1765921 : Blo 1568982 1765921 := bbase (se 2 (by rfl) ⟨662220, by rfl⟩ : syracuseStep 1765921 = 1324441) (by norm_num)
theorem B2355749 : Blo 1568982 2355749 := bbase (se 4 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 2355749 = 441703) (by norm_num)
theorem B3183149 : Blo 1568982 3183149 := bbase (se 3 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 3183149 = 1193681) (by norm_num)
theorem B2355773 : Blo 1568982 2355773 := bbase (se 3 (by rfl) ⟨441707, by rfl⟩ : syracuseStep 2355773 = 883415) (by norm_num)
theorem B1765957 : Blo 1568982 1765957 := bbase (se 4 (by rfl) ⟨165558, by rfl⟩ : syracuseStep 1765957 = 331117) (by norm_num)
theorem B2355797 : Blo 1568982 2355797 := bbase (se 8 (by rfl) ⟨13803, by rfl⟩ : syracuseStep 2355797 = 27607) (by norm_num)
theorem B1765993 : Blo 1568982 1765993 := bbase (se 2 (by rfl) ⟨662247, by rfl⟩ : syracuseStep 1765993 = 1324495) (by norm_num)
theorem B2355821 : Blo 1568982 2355821 := bbase (se 3 (by rfl) ⟨441716, by rfl⟩ : syracuseStep 2355821 = 883433) (by norm_num)
theorem B1987193 : Blo 1568982 1987193 := bbase (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) (by norm_num)
theorem B2355845 : Blo 1568982 2355845 := bbase (se 4 (by rfl) ⟨220860, by rfl⟩ : syracuseStep 2355845 = 441721) (by norm_num)
theorem B1766029 : Blo 1568982 1766029 := bbase (se 3 (by rfl) ⟨331130, by rfl⟩ : syracuseStep 1766029 = 662261) (by norm_num)
theorem B2650765 : Blo 1568982 2650765 := bbase (se 3 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 2650765 = 994037) (by norm_num)
theorem B2355869 : Blo 1568982 2355869 := bbase (se 3 (by rfl) ⟨441725, by rfl⟩ : syracuseStep 2355869 = 883451) (by norm_num)
theorem B3822245 : Blo 1568982 3822245 := bbase (se 4 (by rfl) ⟨358335, by rfl⟩ : syracuseStep 3822245 = 716671) (by norm_num)
theorem B5296805 : Blo 1568982 5296805 := bbase (se 4 (by rfl) ⟨496575, by rfl⟩ : syracuseStep 5296805 = 993151) (by norm_num)
theorem B1766065 : Blo 1568982 1766065 := bbase (se 2 (by rfl) ⟨662274, by rfl⟩ : syracuseStep 1766065 = 1324549) (by norm_num)
theorem B1987249 : Blo 1568982 1987249 := bbase (se 2 (by rfl) ⟨745218, by rfl⟩ : syracuseStep 1987249 = 1490437) (by norm_num)
theorem B2355893 : Blo 1568982 2355893 := bbase (se 5 (by rfl) ⟨110432, by rfl⟩ : syracuseStep 2355893 = 220865) (by norm_num)
theorem B2355917 : Blo 1568982 2355917 := bbase (se 3 (by rfl) ⟨441734, by rfl⟩ : syracuseStep 2355917 = 883469) (by norm_num)
theorem B1766101 : Blo 1568982 1766101 := bbase (se 7 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 1766101 = 41393) (by norm_num)
theorem B2355941 : Blo 1568982 2355941 := bbase (se 4 (by rfl) ⟨220869, by rfl⟩ : syracuseStep 2355941 = 441739) (by norm_num)
theorem B2650853 : Blo 1568982 2650853 := bbase (se 4 (by rfl) ⟨248517, by rfl⟩ : syracuseStep 2650853 = 497035) (by norm_num)
theorem B1766137 : Blo 1568982 1766137 := bbase (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) (by norm_num)
theorem B2355965 : Blo 1568982 2355965 := bbase (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) (by norm_num)
theorem B1987345 : Blo 1568982 1987345 := bbase (se 2 (by rfl) ⟨745254, by rfl⟩ : syracuseStep 1987345 = 1490509) (by norm_num)
theorem B2355989 : Blo 1568982 2355989 := bbase (se 6 (by rfl) ⟨55218, by rfl⟩ : syracuseStep 2355989 = 110437) (by norm_num)
theorem B1766173 : Blo 1568982 1766173 := bbase (se 3 (by rfl) ⟨331157, by rfl⟩ : syracuseStep 1766173 = 662315) (by norm_num)
theorem B2356013 : Blo 1568982 2356013 := bbase (se 3 (by rfl) ⟨441752, by rfl⟩ : syracuseStep 2356013 = 883505) (by norm_num)
theorem B1766209 : Blo 1568982 1766209 := bbase (se 2 (by rfl) ⟨662328, by rfl⟩ : syracuseStep 1766209 = 1324657) (by norm_num)
theorem B2356037 : Blo 1568982 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B2356061 : Blo 1568982 2356061 := bbase (se 3 (by rfl) ⟨441761, by rfl⟩ : syracuseStep 2356061 = 883523) (by norm_num)
theorem B1766245 : Blo 1568982 1766245 := bbase (se 4 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 1766245 = 331171) (by norm_num)
theorem B2650981 : Blo 1568982 2650981 := bbase (se 4 (by rfl) ⟨248529, by rfl⟩ : syracuseStep 2650981 = 497059) (by norm_num)
theorem B2356085 : Blo 1568982 2356085 := bbase (se 5 (by rfl) ⟨110441, by rfl⟩ : syracuseStep 2356085 = 220883) (by norm_num)
theorem B1676161 : Blo 1568982 1676161 := bbase (se 2 (by rfl) ⟨628560, by rfl⟩ : syracuseStep 1676161 = 1257121) (by norm_num)
theorem B1766281 : Blo 1568982 1766281 := bbase (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) (by norm_num)
theorem B2356109 : Blo 1568982 2356109 := bbase (se 3 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 2356109 = 883541) (by norm_num)
theorem B2356133 : Blo 1568982 2356133 := bbase (se 4 (by rfl) ⟨220887, by rfl⟩ : syracuseStep 2356133 = 441775) (by norm_num)
theorem B1766317 : Blo 1568982 1766317 := bbase (se 3 (by rfl) ⟨331184, by rfl⟩ : syracuseStep 1766317 = 662369) (by norm_num)
theorem B1987517 : Blo 1568982 1987517 := bbase (se 3 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 1987517 = 745319) (by norm_num)
theorem B2356157 : Blo 1568982 2356157 := bbase (se 3 (by rfl) ⟨441779, by rfl⟩ : syracuseStep 2356157 = 883559) (by norm_num)
theorem B1676233 : Blo 1568982 1676233 := bbase (se 2 (by rfl) ⟨628587, by rfl⟩ : syracuseStep 1676233 = 1257175) (by norm_num)
theorem B1766353 : Blo 1568982 1766353 := bbase (se 2 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 1766353 = 1324765) (by norm_num)
theorem B2356181 : Blo 1568982 2356181 := bbase (se 7 (by rfl) ⟨27611, by rfl⟩ : syracuseStep 2356181 = 55223) (by norm_num)
theorem B2356205 : Blo 1568982 2356205 := bbase (se 3 (by rfl) ⟨441788, by rfl⟩ : syracuseStep 2356205 = 883577) (by norm_num)
theorem B1766389 : Blo 1568982 1766389 := bbase (se 5 (by rfl) ⟨82799, by rfl⟩ : syracuseStep 1766389 = 165599) (by norm_num)
theorem B1987573 : Blo 1568982 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B2356229 : Blo 1568982 2356229 := bbase (se 4 (by rfl) ⟨220896, by rfl⟩ : syracuseStep 2356229 = 441793) (by norm_num)
theorem B1766425 : Blo 1568982 1766425 := bbase (se 2 (by rfl) ⟨662409, by rfl⟩ : syracuseStep 1766425 = 1324819) (by norm_num)
theorem B2356253 : Blo 1568982 2356253 := bbase (se 3 (by rfl) ⟨441797, by rfl⟩ : syracuseStep 2356253 = 883595) (by norm_num)
theorem B2978869 : Blo 1568982 2978869 := bbase (se 5 (by rfl) ⟨139634, by rfl⟩ : syracuseStep 2978869 = 279269) (by norm_num)
theorem B2356277 : Blo 1568982 2356277 := bbase (se 5 (by rfl) ⟨110450, by rfl⟩ : syracuseStep 2356277 = 220901) (by norm_num)
theorem B1766461 : Blo 1568982 1766461 := bbase (se 3 (by rfl) ⟨331211, by rfl⟩ : syracuseStep 1766461 = 662423) (by norm_num)
theorem B2356301 : Blo 1568982 2356301 := bbase (se 3 (by rfl) ⟨441806, by rfl⟩ : syracuseStep 2356301 = 883613) (by norm_num)
theorem B5297237 : Blo 1568982 5297237 := bbase (se 8 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 5297237 = 62077) (by norm_num)
theorem B1987669 : Blo 1568982 1987669 := bbase (se 8 (by rfl) ⟨11646, by rfl⟩ : syracuseStep 1987669 = 23293) (by norm_num)
theorem B7951445 : Blo 1568982 7951445 := bbase (se 8 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 7951445 = 93181) (by norm_num)
theorem B1766497 : Blo 1568982 1766497 := bbase (se 2 (by rfl) ⟨662436, by rfl⟩ : syracuseStep 1766497 = 1324873) (by norm_num)
theorem B2356325 : Blo 1568982 2356325 := bbase (se 4 (by rfl) ⟨220905, by rfl⟩ : syracuseStep 2356325 = 441811) (by norm_num)
theorem B1676413 : Blo 1568982 1676413 := bbase (se 3 (by rfl) ⟨314327, by rfl⟩ : syracuseStep 1676413 = 628655) (by norm_num)
theorem B2356349 : Blo 1568982 2356349 := bbase (se 3 (by rfl) ⟨441815, by rfl⟩ : syracuseStep 2356349 = 883631) (by norm_num)
theorem B1766533 : Blo 1568982 1766533 := bbase (se 4 (by rfl) ⟨165612, by rfl⟩ : syracuseStep 1766533 = 331225) (by norm_num)
theorem B15504533 : Blo 1568982 15504533 := bbase (se 6 (by rfl) ⟨363387, by rfl⟩ : syracuseStep 15504533 = 726775) (by norm_num)
theorem B2356373 : Blo 1568982 2356373 := bbase (se 6 (by rfl) ⟨55227, by rfl⟩ : syracuseStep 2356373 = 110455) (by norm_num)
theorem B1766569 : Blo 1568982 1766569 := bbase (se 2 (by rfl) ⟨662463, by rfl⟩ : syracuseStep 1766569 = 1324927) (by norm_num)
theorem B2356397 : Blo 1568982 2356397 := bbase (se 3 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 2356397 = 883649) (by norm_num)
theorem B2979013 : Blo 1568982 2979013 := bbase (se 4 (by rfl) ⟨279282, by rfl⟩ : syracuseStep 2979013 = 558565) (by norm_num)
theorem B2356421 : Blo 1568982 2356421 := bbase (se 4 (by rfl) ⟨220914, by rfl⟩ : syracuseStep 2356421 = 441829) (by norm_num)
theorem B1766605 : Blo 1568982 1766605 := bbase (se 3 (by rfl) ⟨331238, by rfl⟩ : syracuseStep 1766605 = 662477) (by norm_num)
theorem B1938637 : Blo 1568982 1938637 := bbase (se 3 (by rfl) ⟨363494, by rfl⟩ : syracuseStep 1938637 = 726989) (by norm_num)
theorem B2356445 : Blo 1568982 2356445 := bbase (se 3 (by rfl) ⟨441833, by rfl⟩ : syracuseStep 2356445 = 883667) (by norm_num)
theorem B1766641 : Blo 1568982 1766641 := bbase (se 2 (by rfl) ⟨662490, by rfl⟩ : syracuseStep 1766641 = 1324981) (by norm_num)
theorem B6706421 : Blo 1568982 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B2356469 : Blo 1568982 2356469 := bbase (se 5 (by rfl) ⟨110459, by rfl⟩ : syracuseStep 2356469 = 220919) (by norm_num)
theorem B1987841 : Blo 1568982 1987841 := bbase (se 2 (by rfl) ⟨745440, by rfl⟩ : syracuseStep 1987841 = 1490881) (by norm_num)
theorem B1766677 : Blo 1568982 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B1766713 : Blo 1568982 1766713 := bbase (se 2 (by rfl) ⟨662517, by rfl⟩ : syracuseStep 1766713 = 1325035) (by norm_num)
theorem B1987897 : Blo 1568982 1987897 := bbase (se 2 (by rfl) ⟨745461, by rfl⟩ : syracuseStep 1987897 = 1490923) (by norm_num)
theorem B1766749 : Blo 1568982 1766749 := bbase (se 3 (by rfl) ⟨331265, by rfl⟩ : syracuseStep 1766749 = 662531) (by norm_num)
theorem B2979173 : Blo 1568982 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B1766785 : Blo 1568982 1766785 := bbase (se 2 (by rfl) ⟨662544, by rfl⟩ : syracuseStep 1766785 = 1325089) (by norm_num)
theorem B1987993 : Blo 1568982 1987993 := bbase (se 2 (by rfl) ⟨745497, by rfl⟩ : syracuseStep 1987993 = 1490995) (by norm_num)
theorem B1766821 : Blo 1568982 1766821 := bbase (se 4 (by rfl) ⟨165639, by rfl⟩ : syracuseStep 1766821 = 331279) (by norm_num)
theorem B1766857 : Blo 1568982 1766857 := bbase (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) (by norm_num)
theorem B1766893 : Blo 1568982 1766893 := bbase (se 3 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 1766893 = 662585) (by norm_num)
theorem B7943669 : Blo 1568982 7943669 := bbase (se 5 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 7943669 = 744719) (by norm_num)
theorem B2979317 : Blo 1568982 2979317 := bbase (se 5 (by rfl) ⟨139655, by rfl⟩ : syracuseStep 2979317 = 279311) (by norm_num)
theorem B11924981 : Blo 1568982 11924981 := bbase (se 5 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 11924981 = 1117967) (by norm_num)
theorem B5297669 : Blo 1568982 5297669 := bbase (se 4 (by rfl) ⟨496656, by rfl⟩ : syracuseStep 5297669 = 993313) (by norm_num)
theorem B1766929 : Blo 1568982 1766929 := bbase (se 2 (by rfl) ⟨662598, by rfl⟩ : syracuseStep 1766929 = 1325197) (by norm_num)
theorem B8484373 : Blo 1568982 8484373 := bbase (se 6 (by rfl) ⟨198852, by rfl⟩ : syracuseStep 8484373 = 397705) (by norm_num)
theorem B6706709 : Blo 1568982 6706709 := bbase (se 6 (by rfl) ⟨157188, by rfl⟩ : syracuseStep 6706709 = 314377) (by norm_num)
theorem B1766965 : Blo 1568982 1766965 := bbase (se 5 (by rfl) ⟨82826, by rfl⟩ : syracuseStep 1766965 = 165653) (by norm_num)
theorem B1676857 : Blo 1568982 1676857 := bbase (se 2 (by rfl) ⟨628821, by rfl⟩ : syracuseStep 1676857 = 1257643) (by norm_num)
theorem B1988165 : Blo 1568982 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B1767001 : Blo 1568982 1767001 := bbase (se 2 (by rfl) ⟨662625, by rfl⟩ : syracuseStep 1767001 = 1325251) (by norm_num)
theorem B1767037 : Blo 1568982 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B1988221 : Blo 1568982 1988221 := bbase (se 3 (by rfl) ⟨372791, by rfl⟩ : syracuseStep 1988221 = 745583) (by norm_num)
theorem B1767073 : Blo 1568982 1767073 := bbase (se 2 (by rfl) ⟨662652, by rfl⟩ : syracuseStep 1767073 = 1325305) (by norm_num)
theorem B5732021 : Blo 1568982 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B5961397 : Blo 1568982 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B1676981 : Blo 1568982 1676981 := bbase (se 5 (by rfl) ⟨78608, by rfl⟩ : syracuseStep 1676981 = 157217) (by norm_num)
theorem B1767109 : Blo 1568982 1767109 := bbase (se 4 (by rfl) ⟨165666, by rfl⟩ : syracuseStep 1767109 = 331333) (by norm_num)
theorem B1767145 : Blo 1568982 1767145 := bbase (se 2 (by rfl) ⟨662679, by rfl⟩ : syracuseStep 1767145 = 1325359) (by norm_num)
theorem B1767181 : Blo 1568982 1767181 := bbase (se 3 (by rfl) ⟨331346, by rfl⟩ : syracuseStep 1767181 = 662693) (by norm_num)
theorem B2979605 : Blo 1568982 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B2012953 : Blo 1568982 2012953 := bbase (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) (by norm_num)
theorem B2684701 : Blo 1568982 2684701 := bbase (se 3 (by rfl) ⟨503381, by rfl⟩ : syracuseStep 2684701 = 1006763) (by norm_num)
theorem B1767217 : Blo 1568982 1767217 := bbase (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) (by norm_num)
theorem B3774293 : Blo 1568982 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B1767253 : Blo 1568982 1767253 := bbase (se 9 (by rfl) ⟨5177, by rfl⟩ : syracuseStep 1767253 = 10355) (by norm_num)
theorem B7542629 : Blo 1568982 7542629 := bbase (se 4 (by rfl) ⟨707121, by rfl⟩ : syracuseStep 7542629 = 1414243) (by norm_num)
theorem B1767289 : Blo 1568982 1767289 := bbase (se 2 (by rfl) ⟨662733, by rfl⟩ : syracuseStep 1767289 = 1325467) (by norm_num)
theorem B11917205 : Blo 1568982 11917205 := bbase (se 6 (by rfl) ⟨279309, by rfl⟩ : syracuseStep 11917205 = 558619) (by norm_num)
theorem B1767325 : Blo 1568982 1767325 := bbase (se 3 (by rfl) ⟨331373, by rfl⟩ : syracuseStep 1767325 = 662747) (by norm_num)
theorem B2979757 : Blo 1568982 2979757 := bbase (se 3 (by rfl) ⟨558704, by rfl⟩ : syracuseStep 2979757 = 1117409) (by norm_num)
theorem B1677233 : Blo 1568982 1677233 := bbase (se 2 (by rfl) ⟨628962, by rfl⟩ : syracuseStep 1677233 = 1257925) (by norm_num)
theorem B5298101 : Blo 1568982 5298101 := bbase (se 5 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 5298101 = 496697) (by norm_num)
theorem B2234317 : Blo 1568982 2234317 := bbase (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) (by norm_num)
theorem B5961701 : Blo 1568982 5961701 := bbase (se 4 (by rfl) ⟨558909, by rfl⟩ : syracuseStep 5961701 = 1117819) (by norm_num)
theorem B6797317 : Blo 1568982 6797317 := bbase (se 4 (by rfl) ⟨637248, by rfl⟩ : syracuseStep 6797317 = 1274497) (by norm_num)
theorem B3774485 : Blo 1568982 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B4470821 : Blo 1568982 4470821 := bbase (se 4 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 4470821 = 838279) (by norm_num)
theorem B2013337 : Blo 1568982 2013337 := bbase (se 2 (by rfl) ⟨755001, by rfl⟩ : syracuseStep 2013337 = 1510003) (by norm_num)
theorem B2980061 : Blo 1568982 2980061 := bbase (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) (by norm_num)
theorem B6707461 : Blo 1568982 6707461 := bbase (se 4 (by rfl) ⟨628824, by rfl⟩ : syracuseStep 6707461 = 1257649) (by norm_num)
theorem B5298533 : Blo 1568982 5298533 := bbase (se 4 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 5298533 = 993475) (by norm_num)
theorem B7952741 : Blo 1568982 7952741 := bbase (se 4 (by rfl) ⟨745569, by rfl⟩ : syracuseStep 7952741 = 1491139) (by norm_num)
theorem B2685325 : Blo 1568982 2685325 := bbase (se 3 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 2685325 = 1006997) (by norm_num)
theorem B3971501 : Blo 1568982 3971501 := bbase (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) (by norm_num)
theorem B36231637 : Blo 1568982 36231637 := bbase (se 7 (by rfl) ⟨424589, by rfl⟩ : syracuseStep 36231637 = 849179) (by norm_num)
theorem B2234909 : Blo 1568982 2234909 := bbase (se 3 (by rfl) ⟨419045, by rfl⟩ : syracuseStep 2234909 = 838091) (by norm_num)
theorem B3971693 : Blo 1568982 3971693 := bbase (se 3 (by rfl) ⟨744692, by rfl⟩ : syracuseStep 3971693 = 1489385) (by norm_num)
theorem B2234989 : Blo 1568982 2234989 := bbase (se 3 (by rfl) ⟨419060, by rfl⟩ : syracuseStep 2234989 = 838121) (by norm_num)
theorem B22928021 : Blo 1568982 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B13417109 : Blo 1568982 13417109 := bbase (se 6 (by rfl) ⟨314463, by rfl⟩ : syracuseStep 13417109 = 628927) (by norm_num)
theorem B14514869 : Blo 1568982 14514869 := bbase (se 5 (by rfl) ⟨680384, by rfl⟩ : syracuseStep 14514869 = 1360769) (by norm_num)
theorem B17873621 : Blo 1568982 17873621 := bbase (se 7 (by rfl) ⟨209456, by rfl⟩ : syracuseStep 17873621 = 418913) (by norm_num)
theorem B2685653 : Blo 1568982 2685653 := bbase (se 7 (by rfl) ⟨31472, by rfl⟩ : syracuseStep 2685653 = 62945) (by norm_num)
theorem B2235109 : Blo 1568982 2235109 := bbase (se 4 (by rfl) ⟨209541, by rfl⟩ : syracuseStep 2235109 = 419083) (by norm_num)
theorem B7944965 : Blo 1568982 7944965 := bbase (se 4 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 7944965 = 1489681) (by norm_num)
theorem B5298965 : Blo 1568982 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B2235205 : Blo 1568982 2235205 := bbase (se 4 (by rfl) ⟨209550, by rfl⟩ : syracuseStep 2235205 = 419101) (by norm_num)
theorem B3972037 : Blo 1568982 3972037 := bbase (se 4 (by rfl) ⟨372378, by rfl⟩ : syracuseStep 3972037 = 744757) (by norm_num)
theorem B2980813 : Blo 1568982 2980813 := bbase (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) (by norm_num)
theorem B6708197 : Blo 1568982 6708197 := bbase (se 4 (by rfl) ⟨628893, by rfl⟩ : syracuseStep 6708197 = 1257787) (by norm_num)
theorem B4242469 : Blo 1568982 4242469 := bbase (se 4 (by rfl) ⟨397731, by rfl⟩ : syracuseStep 4242469 = 795463) (by norm_num)
theorem B3972149 : Blo 1568982 3972149 := bbase (se 5 (by rfl) ⟨186194, by rfl⟩ : syracuseStep 3972149 = 372389) (by norm_num)
theorem B2980957 : Blo 1568982 2980957 := bbase (se 3 (by rfl) ⟨558929, by rfl⟩ : syracuseStep 2980957 = 1117859) (by norm_num)
theorem B5299397 : Blo 1568982 5299397 := bbase (se 4 (by rfl) ⟨496818, by rfl⟩ : syracuseStep 5299397 = 993637) (by norm_num)
theorem B4472005 : Blo 1568982 4472005 := bbase (se 4 (by rfl) ⟨419250, by rfl⟩ : syracuseStep 4472005 = 838501) (by norm_num)
theorem B2014409 : Blo 1568982 2014409 := bbase (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) (by norm_num)
theorem B3972341 : Blo 1568982 3972341 := bbase (se 5 (by rfl) ⟨186203, by rfl⟩ : syracuseStep 3972341 = 372407) (by norm_num)
theorem B2981117 : Blo 1568982 2981117 := bbase (se 3 (by rfl) ⟨558959, by rfl⟩ : syracuseStep 2981117 = 1117919) (by norm_num)
theorem B3398933 : Blo 1568982 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B2866477 : Blo 1568982 2866477 := bbase (se 3 (by rfl) ⟨537464, by rfl⟩ : syracuseStep 2866477 = 1074929) (by norm_num)
theorem B2235701 : Blo 1568982 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B4472165 : Blo 1568982 4472165 := bbase (se 4 (by rfl) ⟨419265, by rfl⟩ : syracuseStep 4472165 = 838531) (by norm_num)
theorem B2981261 : Blo 1568982 2981261 := bbase (se 3 (by rfl) ⟨558986, by rfl⟩ : syracuseStep 2981261 = 1117973) (by norm_num)
theorem B3530213 : Blo 1568982 3530213 := bbase (se 4 (by rfl) ⟨330957, by rfl⟩ : syracuseStep 3530213 = 661915) (by norm_num)
theorem B5307925 : Blo 1568982 5307925 := bbase (se 6 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 5307925 = 248809) (by norm_num)
theorem B3530285 : Blo 1568982 3530285 := bbase (se 3 (by rfl) ⟨661928, by rfl⟩ : syracuseStep 3530285 = 1323857) (by norm_num)
theorem B3972685 : Blo 1568982 3972685 := bbase (se 3 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 3972685 = 1489757) (by norm_num)
theorem B4472405 : Blo 1568982 4472405 := bbase (se 8 (by rfl) ⟨26205, by rfl⟩ : syracuseStep 4472405 = 52411) (by norm_num)
theorem B3530357 : Blo 1568982 3530357 := bbase (se 5 (by rfl) ⟨165485, by rfl⟩ : syracuseStep 3530357 = 330971) (by norm_num)
theorem B5299829 : Blo 1568982 5299829 := bbase (se 5 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 5299829 = 496859) (by norm_num)
theorem B2514581 : Blo 1568982 2514581 := bbase (se 6 (by rfl) ⟨58935, by rfl⟩ : syracuseStep 2514581 = 117871) (by norm_num)
theorem B2981549 : Blo 1568982 2981549 := bbase (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) (by norm_num)
theorem B2014897 : Blo 1568982 2014897 := bbase (se 2 (by rfl) ⟨755586, by rfl⟩ : syracuseStep 2014897 = 1511173) (by norm_num)
theorem B3530429 : Blo 1568982 3530429 := bbase (se 3 (by rfl) ⟨661955, by rfl⟩ : syracuseStep 3530429 = 1323911) (by norm_num)
theorem B3972797 : Blo 1568982 3972797 := bbase (se 3 (by rfl) ⟨744899, by rfl⟩ : syracuseStep 3972797 = 1489799) (by norm_num)
theorem B3579637 : Blo 1568982 3579637 := bbase (se 5 (by rfl) ⟨167795, by rfl⟩ : syracuseStep 3579637 = 335591) (by norm_num)
theorem B3399421 : Blo 1568982 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B3530501 : Blo 1568982 3530501 := bbase (se 4 (by rfl) ⟨330984, by rfl⟩ : syracuseStep 3530501 = 661969) (by norm_num)
theorem B4472597 : Blo 1568982 4472597 := bbase (se 6 (by rfl) ⟨104826, by rfl⟩ : syracuseStep 4472597 = 209653) (by norm_num)
theorem B2981701 : Blo 1568982 2981701 := bbase (se 4 (by rfl) ⟨279534, by rfl⟩ : syracuseStep 2981701 = 559069) (by norm_num)
theorem B3530573 : Blo 1568982 3530573 := bbase (se 3 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 3530573 = 1323965) (by norm_num)
theorem B2514773 : Blo 1568982 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B2236253 : Blo 1568982 2236253 := bbase (se 3 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 2236253 = 838595) (by norm_num)
theorem B3972989 : Blo 1568982 3972989 := bbase (se 3 (by rfl) ⟨744935, by rfl⟩ : syracuseStep 3972989 = 1489871) (by norm_num)
theorem B3530645 : Blo 1568982 3530645 := bbase (se 6 (by rfl) ⟨82749, by rfl⟩ : syracuseStep 3530645 = 165499) (by norm_num)
theorem B3530717 : Blo 1568982 3530717 := bbase (se 3 (by rfl) ⟨662009, by rfl⟩ : syracuseStep 3530717 = 1324019) (by norm_num)
theorem B8052709 : Blo 1568982 8052709 := bbase (se 4 (by rfl) ⟨754941, by rfl⟩ : syracuseStep 8052709 = 1509883) (by norm_num)
theorem B8945741 : Blo 1568982 8945741 := bstep (se 3 (by rfl) ⟨1677326, by rfl⟩ : syracuseStep 8945741 = 3354653) B3354653
theorem B3629137 : Blo 1568982 3629137 := bstep (se 2 (by rfl) ⟨1360926, by rfl⟩ : syracuseStep 3629137 = 2721853) B2721853
theorem B3530897 : Blo 1568982 3530897 := bstep (se 2 (by rfl) ⟨1324086, by rfl⟩ : syracuseStep 3530897 = 2648173) B2648173
theorem B5300369 : Blo 1568982 5300369 := bstep (se 2 (by rfl) ⟨1987638, by rfl⟩ : syracuseStep 5300369 = 3975277) B3975277
theorem B3530915 : Blo 1568982 3530915 := bstep (se 1 (by rfl) ⟨2648186, by rfl⟩ : syracuseStep 3530915 = 5296373) B5296373
theorem B3973283 : Blo 1568982 3973283 := bstep (se 1 (by rfl) ⟨2979962, by rfl⟩ : syracuseStep 3973283 = 5959925) B5959925
theorem B32219363 : Blo 1568982 32219363 := bstep (se 1 (by rfl) ⟨24164522, by rfl⟩ : syracuseStep 32219363 = 48329045) B48329045
theorem B2236675 : Blo 1568982 2236675 := bstep (se 1 (by rfl) ⟨1677506, by rfl⟩ : syracuseStep 2236675 = 3355013) B3355013
theorem B3973475 : Blo 1568982 3973475 := bstep (se 1 (by rfl) ⟨2980106, by rfl⟩ : syracuseStep 3973475 = 5960213) B5960213
theorem B5964131 : Blo 1568982 5964131 := bstep (se 1 (by rfl) ⟨4473098, by rfl⟩ : syracuseStep 5964131 = 8946197) B8946197
theorem B4243853 : Blo 1568982 4243853 := bstep (se 3 (by rfl) ⟨795722, by rfl⟩ : syracuseStep 4243853 = 1591445) B1591445
theorem B3531185 : Blo 1568982 3531185 := bstep (se 2 (by rfl) ⟨1324194, by rfl⟩ : syracuseStep 3531185 = 2648389) B2648389
theorem B2548163 : Blo 1568982 2548163 := bstep (se 1 (by rfl) ⟨1911122, by rfl⟩ : syracuseStep 2548163 = 3822245) B3822245
theorem B3531203 : Blo 1568982 3531203 := bstep (se 1 (by rfl) ⟨2648402, by rfl⟩ : syracuseStep 3531203 = 5296805) B5296805
theorem B3580433 : Blo 1568982 3580433 := bstep (se 2 (by rfl) ⟨1342662, by rfl⟩ : syracuseStep 3580433 = 2685325) B2685325
theorem B6709837 : Blo 1568982 6709837 := bstep (se 3 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 6709837 = 2516189) B2516189
theorem B48308849 : Blo 1568982 48308849 := bstep (se 2 (by rfl) ⟨18115818, by rfl⟩ : syracuseStep 48308849 = 36231637) B36231637
theorem B4244113 : Blo 1568982 4244113 := bstep (se 2 (by rfl) ⟨1591542, by rfl⟩ : syracuseStep 4244113 = 3183085) B3183085
theorem B5030545 : Blo 1568982 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B5300909 : Blo 1568982 5300909 := bstep (se 3 (by rfl) ⟨993920, by rfl⟩ : syracuseStep 5300909 = 1987841) B1987841
theorem B3531473 : Blo 1568982 3531473 := bstep (se 2 (by rfl) ⟨1324302, by rfl⟩ : syracuseStep 3531473 = 2648605) B2648605
theorem B3531491 : Blo 1568982 3531491 := bstep (se 1 (by rfl) ⟨2648618, by rfl⟩ : syracuseStep 3531491 = 5297237) B5297237
theorem B5300963 : Blo 1568982 5300963 := bstep (se 1 (by rfl) ⟨3975722, by rfl⟩ : syracuseStep 5300963 = 7951445) B7951445
theorem B8487665 : Blo 1568982 8487665 := bstep (se 2 (by rfl) ⟨3182874, by rfl⟩ : syracuseStep 8487665 = 6365749) B6365749
theorem B21767093 : Blo 1568982 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B3531761 : Blo 1568982 3531761 := bstep (se 2 (by rfl) ⟨1324410, by rfl⟩ : syracuseStep 3531761 = 2648821) B2648821
theorem B5301233 : Blo 1568982 5301233 := bstep (se 2 (by rfl) ⟨1987962, by rfl⟩ : syracuseStep 5301233 = 3975925) B3975925
theorem B5964785 : Blo 1568982 5964785 := bstep (se 2 (by rfl) ⟨2236794, by rfl⟩ : syracuseStep 5964785 = 4473589) B4473589
theorem B3531779 : Blo 1568982 3531779 := bstep (se 1 (by rfl) ⟨2648834, by rfl⟩ : syracuseStep 3531779 = 5297669) B5297669
theorem B10339397 : Blo 1568982 10339397 := bstep (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) B1938637
theorem B2516195 : Blo 1568982 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B3532049 : Blo 1568982 3532049 := bstep (se 2 (by rfl) ⟨1324518, by rfl⟩ : syracuseStep 3532049 = 2649037) B2649037
theorem B3974417 : Blo 1568982 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B6702371 : Blo 1568982 6702371 := bstep (se 1 (by rfl) ⟨5026778, by rfl⟩ : syracuseStep 6702371 = 10053557) B10053557
theorem B3532067 : Blo 1568982 3532067 := bstep (se 1 (by rfl) ⟨2649050, by rfl⟩ : syracuseStep 3532067 = 5298101) B5298101
theorem B3974467 : Blo 1568982 3974467 := bstep (se 1 (by rfl) ⟨2980850, by rfl⟩ : syracuseStep 3974467 = 5961701) B5961701
theorem B13600099 : Blo 1568982 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B8488397 : Blo 1568982 8488397 := bstep (se 3 (by rfl) ⟨1591574, by rfl⟩ : syracuseStep 8488397 = 3183149) B3183149
theorem B3974609 : Blo 1568982 3974609 := bstep (se 2 (by rfl) ⟨1490478, by rfl⟩ : syracuseStep 3974609 = 2980957) B2980957
theorem B5301773 : Blo 1568982 5301773 := bstep (se 3 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 5301773 = 1988165) B1988165
theorem B3532337 : Blo 1568982 3532337 := bstep (se 2 (by rfl) ⟨1324626, by rfl⟩ : syracuseStep 3532337 = 2649253) B2649253
theorem B3532355 : Blo 1568982 3532355 := bstep (se 1 (by rfl) ⟨2649266, by rfl⟩ : syracuseStep 3532355 = 5298533) B5298533
theorem B5301827 : Blo 1568982 5301827 := bstep (se 1 (by rfl) ⟨3976370, by rfl⟩ : syracuseStep 5301827 = 7952741) B7952741
theorem B2647667 : Blo 1568982 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B5957297 : Blo 1568982 5957297 := bstep (se 2 (by rfl) ⟨2233986, by rfl⟩ : syracuseStep 5957297 = 4467973) B4467973
theorem B11921093 : Blo 1568982 11921093 := bstep (se 4 (by rfl) ⟨1117602, by rfl⟩ : syracuseStep 11921093 = 2235205) B2235205
theorem B2647795 : Blo 1568982 2647795 := bstep (se 1 (by rfl) ⟨1985846, by rfl⟩ : syracuseStep 2647795 = 3971693) B3971693
theorem B9676579 : Blo 1568982 9676579 := bstep (se 1 (by rfl) ⟨7257434, by rfl⟩ : syracuseStep 9676579 = 14514869) B14514869
theorem B10061603 : Blo 1568982 10061603 := bstep (se 1 (by rfl) ⟨7546202, by rfl⟩ : syracuseStep 10061603 = 15092405) B15092405
theorem B3532625 : Blo 1568982 3532625 := bstep (se 2 (by rfl) ⟨1324734, by rfl⟩ : syracuseStep 3532625 = 2649469) B2649469
theorem B3532643 : Blo 1568982 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B2647937 : Blo 1568982 2647937 := bstep (se 2 (by rfl) ⟨992976, by rfl⟩ : syracuseStep 2647937 = 1985953) B1985953
theorem B2648065 : Blo 1568982 2648065 := bstep (se 2 (by rfl) ⟨993024, by rfl⟩ : syracuseStep 2648065 = 1986049) B1986049
theorem B3770371 : Blo 1568982 3770371 := bstep (se 1 (by rfl) ⟨2827778, by rfl⟩ : syracuseStep 3770371 = 5655557) B5655557
theorem B1591315 : Blo 1568982 1591315 := bstep (se 1 (by rfl) ⟨1193486, by rfl⟩ : syracuseStep 1591315 = 2386973) B2386973
theorem B2648099 : Blo 1568982 2648099 := bstep (se 1 (by rfl) ⟨1986074, by rfl⟩ : syracuseStep 2648099 = 3972149) B3972149
theorem B9062435 : Blo 1568982 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B3532913 : Blo 1568982 3532913 := bstep (se 2 (by rfl) ⟨1324842, by rfl⟩ : syracuseStep 3532913 = 2649685) B2649685
theorem B1886339 : Blo 1568982 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B3532931 : Blo 1568982 3532931 := bstep (se 1 (by rfl) ⟨2649698, by rfl⟩ : syracuseStep 3532931 = 5299397) B5299397
theorem B2648227 : Blo 1568982 2648227 := bstep (se 1 (by rfl) ⟨1986170, by rfl⟩ : syracuseStep 2648227 = 3972341) B3972341
theorem B24176837 : Blo 1568982 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B7948529 : Blo 1568982 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B3770641 : Blo 1568982 3770641 := bstep (se 2 (by rfl) ⟨1413990, by rfl⟩ : syracuseStep 3770641 = 2827981) B2827981
theorem B2648369 : Blo 1568982 2648369 := bstep (se 2 (by rfl) ⟨993138, by rfl⟩ : syracuseStep 2648369 = 1986277) B1986277
theorem B2353475 : Blo 1568982 2353475 := bstep (se 1 (by rfl) ⟨1765106, by rfl⟩ : syracuseStep 2353475 = 3530213) B3530213
theorem B4532561 : Blo 1568982 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B2353505 : Blo 1568982 2353505 := bstep (se 2 (by rfl) ⟨882564, by rfl⟩ : syracuseStep 2353505 = 1765129) B1765129
theorem B2353523 : Blo 1568982 2353523 := bstep (se 1 (by rfl) ⟨1765142, by rfl⟩ : syracuseStep 2353523 = 3530285) B3530285
theorem B8939909 : Blo 1568982 8939909 := bstep (se 4 (by rfl) ⟨838116, by rfl⟩ : syracuseStep 8939909 = 1676233) B1676233
theorem B2353553 : Blo 1568982 2353553 := bstep (se 2 (by rfl) ⟨882582, by rfl⟩ : syracuseStep 2353553 = 1765165) B1765165
theorem B3533201 : Blo 1568982 3533201 := bstep (se 2 (by rfl) ⟨1324950, by rfl⟩ : syracuseStep 3533201 = 2649901) B2649901
theorem B2353571 : Blo 1568982 2353571 := bstep (se 1 (by rfl) ⟨1765178, by rfl⟩ : syracuseStep 2353571 = 3530357) B3530357
theorem B3533219 : Blo 1568982 3533219 := bstep (se 1 (by rfl) ⟨2649914, by rfl⟩ : syracuseStep 3533219 = 5299829) B5299829
theorem B2648497 : Blo 1568982 2648497 := bstep (se 2 (by rfl) ⟨993186, by rfl⟩ : syracuseStep 2648497 = 1986373) B1986373
theorem B8489393 : Blo 1568982 8489393 := bstep (se 2 (by rfl) ⟨3183522, by rfl⟩ : syracuseStep 8489393 = 6367045) B6367045
theorem B3975601 : Blo 1568982 3975601 := bstep (se 2 (by rfl) ⟨1490850, by rfl⟩ : syracuseStep 3975601 = 2981701) B2981701
theorem B2353601 : Blo 1568982 2353601 := bstep (se 2 (by rfl) ⟨882600, by rfl⟩ : syracuseStep 2353601 = 1765201) B1765201
theorem B6367693 : Blo 1568982 6367693 := bstep (se 3 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 6367693 = 2387885) B2387885
theorem B2353619 : Blo 1568982 2353619 := bstep (se 1 (by rfl) ⟨1765214, by rfl⟩ : syracuseStep 2353619 = 3530429) B3530429
theorem B2648531 : Blo 1568982 2648531 := bstep (se 1 (by rfl) ⟨1986398, by rfl⟩ : syracuseStep 2648531 = 3972797) B3972797
theorem B2353649 : Blo 1568982 2353649 := bstep (se 2 (by rfl) ⟨882618, by rfl⟩ : syracuseStep 2353649 = 1765237) B1765237
theorem B2353667 : Blo 1568982 2353667 := bstep (se 1 (by rfl) ⟨1765250, by rfl⟩ : syracuseStep 2353667 = 3530501) B3530501
theorem B2353697 : Blo 1568982 2353697 := bstep (se 2 (by rfl) ⟨882636, by rfl⟩ : syracuseStep 2353697 = 1765273) B1765273
theorem B5032493 : Blo 1568982 5032493 := bstep (se 3 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 5032493 = 1887185) B1887185
theorem B2353715 : Blo 1568982 2353715 := bstep (se 1 (by rfl) ⟨1765286, by rfl⟩ : syracuseStep 2353715 = 3530573) B3530573
theorem B2353745 : Blo 1568982 2353745 := bstep (se 2 (by rfl) ⟨882654, by rfl⟩ : syracuseStep 2353745 = 1765309) B1765309
theorem B2648659 : Blo 1568982 2648659 := bstep (se 1 (by rfl) ⟨1986494, by rfl⟩ : syracuseStep 2648659 = 3972989) B3972989
theorem B2353763 : Blo 1568982 2353763 := bstep (se 1 (by rfl) ⟨1765322, by rfl⟩ : syracuseStep 2353763 = 3530645) B3530645
theorem B2353793 : Blo 1568982 2353793 := bstep (se 2 (by rfl) ⟨882672, by rfl⟩ : syracuseStep 2353793 = 1765345) B1765345
theorem B3181187 : Blo 1568982 3181187 := bstep (se 1 (by rfl) ⟨2385890, by rfl⟩ : syracuseStep 3181187 = 4771781) B4771781
theorem B2353811 : Blo 1568982 2353811 := bstep (se 1 (by rfl) ⟨1765358, by rfl⟩ : syracuseStep 2353811 = 3530717) B3530717
theorem B5032621 : Blo 1568982 5032621 := bstep (se 3 (by rfl) ⟨943616, by rfl⟩ : syracuseStep 5032621 = 1887233) B1887233
theorem B2353841 : Blo 1568982 2353841 := bstep (se 2 (by rfl) ⟨882690, by rfl⟩ : syracuseStep 2353841 = 1765381) B1765381
theorem B9063089 : Blo 1568982 9063089 := bstep (se 2 (by rfl) ⟨3398658, by rfl⟩ : syracuseStep 9063089 = 6797317) B6797317
theorem B3533489 : Blo 1568982 3533489 := bstep (se 2 (by rfl) ⟨1325058, by rfl⟩ : syracuseStep 3533489 = 2650117) B2650117
theorem B2353859 : Blo 1568982 2353859 := bstep (se 1 (by rfl) ⟨1765394, by rfl⟩ : syracuseStep 2353859 = 3530789) B3530789
theorem B3533507 : Blo 1568982 3533507 := bstep (se 1 (by rfl) ⟨2650130, by rfl⟩ : syracuseStep 3533507 = 5300261) B5300261
theorem B3975875 : Blo 1568982 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B2353889 : Blo 1568982 2353889 := bstep (se 2 (by rfl) ⟨882708, by rfl⟩ : syracuseStep 2353889 = 1765417) B1765417
theorem B2648801 : Blo 1568982 2648801 := bstep (se 2 (by rfl) ⟨993300, by rfl⟩ : syracuseStep 2648801 = 1986601) B1986601
theorem B2353907 : Blo 1568982 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B2353937 : Blo 1568982 2353937 := bstep (se 2 (by rfl) ⟨882726, by rfl⟩ : syracuseStep 2353937 = 1765453) B1765453
theorem B2722577 : Blo 1568982 2722577 := bstep (se 2 (by rfl) ⟨1020966, by rfl⟩ : syracuseStep 2722577 = 2041933) B2041933
theorem B2353955 : Blo 1568982 2353955 := bstep (se 1 (by rfl) ⟨1765466, by rfl⟩ : syracuseStep 2353955 = 3530933) B3530933
theorem B2353985 : Blo 1568982 2353985 := bstep (se 2 (by rfl) ⟨882744, by rfl⟩ : syracuseStep 2353985 = 1765489) B1765489
theorem B4246339 : Blo 1568982 4246339 := bstep (se 1 (by rfl) ⟨3184754, by rfl⟩ : syracuseStep 4246339 = 6369509) B6369509
theorem B8940365 : Blo 1568982 8940365 := bstep (se 3 (by rfl) ⟨1676318, by rfl⟩ : syracuseStep 8940365 = 3352637) B3352637
theorem B2354003 : Blo 1568982 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B2648929 : Blo 1568982 2648929 := bstep (se 2 (by rfl) ⟨993348, by rfl⟩ : syracuseStep 2648929 = 1986697) B1986697
theorem B2354033 : Blo 1568982 2354033 := bstep (se 2 (by rfl) ⟨882762, by rfl⟩ : syracuseStep 2354033 = 1765525) B1765525
theorem B2354051 : Blo 1568982 2354051 := bstep (se 1 (by rfl) ⟨1765538, by rfl⟩ : syracuseStep 2354051 = 3531077) B3531077
theorem B2648963 : Blo 1568982 2648963 := bstep (se 1 (by rfl) ⟨1986722, by rfl⟩ : syracuseStep 2648963 = 3973445) B3973445
theorem B3976067 : Blo 1568982 3976067 := bstep (se 1 (by rfl) ⟨2982050, by rfl⟩ : syracuseStep 3976067 = 5964101) B5964101
theorem B2354081 : Blo 1568982 2354081 := bstep (se 2 (by rfl) ⟨882780, by rfl⟩ : syracuseStep 2354081 = 1765561) B1765561
theorem B2354099 : Blo 1568982 2354099 := bstep (se 1 (by rfl) ⟨1765574, by rfl⟩ : syracuseStep 2354099 = 3531149) B3531149
theorem B2354129 : Blo 1568982 2354129 := bstep (se 2 (by rfl) ⟨882798, by rfl⟩ : syracuseStep 2354129 = 1765597) B1765597
theorem B3533777 : Blo 1568982 3533777 := bstep (se 2 (by rfl) ⟨1325166, by rfl⟩ : syracuseStep 3533777 = 2650333) B2650333
theorem B2354147 : Blo 1568982 2354147 := bstep (se 1 (by rfl) ⟨1765610, by rfl⟩ : syracuseStep 2354147 = 3531221) B3531221
theorem B3533795 : Blo 1568982 3533795 := bstep (se 1 (by rfl) ⟨2650346, by rfl⟩ : syracuseStep 3533795 = 5300693) B5300693
theorem B2354177 : Blo 1568982 2354177 := bstep (se 2 (by rfl) ⟨882816, by rfl⟩ : syracuseStep 2354177 = 1765633) B1765633
theorem B2649091 : Blo 1568982 2649091 := bstep (se 1 (by rfl) ⟨1986818, by rfl⟩ : syracuseStep 2649091 = 3973637) B3973637
theorem B2354195 : Blo 1568982 2354195 := bstep (se 1 (by rfl) ⟨1765646, by rfl⟩ : syracuseStep 2354195 = 3531293) B3531293
theorem B2354225 : Blo 1568982 2354225 := bstep (se 2 (by rfl) ⟨882834, by rfl⟩ : syracuseStep 2354225 = 1765669) B1765669
theorem B2387009 : Blo 1568982 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B2354243 : Blo 1568982 2354243 := bstep (se 1 (by rfl) ⟨1765682, by rfl⟩ : syracuseStep 2354243 = 3531365) B3531365
theorem B2354273 : Blo 1568982 2354273 := bstep (se 2 (by rfl) ⟨882852, by rfl⟩ : syracuseStep 2354273 = 1765705) B1765705
theorem B5958755 : Blo 1568982 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B2354291 : Blo 1568982 2354291 := bstep (se 1 (by rfl) ⟨1765718, by rfl⟩ : syracuseStep 2354291 = 3531437) B3531437
theorem B2354321 : Blo 1568982 2354321 := bstep (se 2 (by rfl) ⟨882870, by rfl⟩ : syracuseStep 2354321 = 1765741) B1765741
theorem B2649233 : Blo 1568982 2649233 := bstep (se 2 (by rfl) ⟨993462, by rfl⟩ : syracuseStep 2649233 = 1986925) B1986925
theorem B2354339 : Blo 1568982 2354339 := bstep (se 1 (by rfl) ⟨1765754, by rfl⟩ : syracuseStep 2354339 = 3531509) B3531509
theorem B2387107 : Blo 1568982 2387107 := bstep (se 1 (by rfl) ⟨1790330, by rfl⟩ : syracuseStep 2387107 = 3580661) B3580661
theorem B2354369 : Blo 1568982 2354369 := bstep (se 2 (by rfl) ⟨882888, by rfl⟩ : syracuseStep 2354369 = 1765777) B1765777
theorem B2354387 : Blo 1568982 2354387 := bstep (se 1 (by rfl) ⟨1765790, by rfl⟩ : syracuseStep 2354387 = 3531581) B3531581
theorem B2354417 : Blo 1568982 2354417 := bstep (se 2 (by rfl) ⟨882906, by rfl⟩ : syracuseStep 2354417 = 1765813) B1765813
theorem B3534065 : Blo 1568982 3534065 := bstep (se 2 (by rfl) ⟨1325274, by rfl⟩ : syracuseStep 3534065 = 2650549) B2650549
theorem B2354435 : Blo 1568982 2354435 := bstep (se 1 (by rfl) ⟨1765826, by rfl⟩ : syracuseStep 2354435 = 3531653) B3531653
theorem B3534083 : Blo 1568982 3534083 := bstep (se 1 (by rfl) ⟨2650562, by rfl⟩ : syracuseStep 3534083 = 5301125) B5301125
theorem B2649361 : Blo 1568982 2649361 := bstep (se 2 (by rfl) ⟨993510, by rfl⟩ : syracuseStep 2649361 = 1987021) B1987021
theorem B2354465 : Blo 1568982 2354465 := bstep (se 2 (by rfl) ⟨882924, by rfl⟩ : syracuseStep 2354465 = 1765849) B1765849
theorem B2354483 : Blo 1568982 2354483 := bstep (se 1 (by rfl) ⟨1765862, by rfl⟩ : syracuseStep 2354483 = 3531725) B3531725
theorem B2649395 : Blo 1568982 2649395 := bstep (se 1 (by rfl) ⟨1987046, by rfl⟩ : syracuseStep 2649395 = 3974093) B3974093
theorem B2354513 : Blo 1568982 2354513 := bstep (se 2 (by rfl) ⟨882942, by rfl⟩ : syracuseStep 2354513 = 1765885) B1765885
theorem B2354531 : Blo 1568982 2354531 := bstep (se 1 (by rfl) ⟨1765898, by rfl⟩ : syracuseStep 2354531 = 3531797) B3531797
theorem B2354561 : Blo 1568982 2354561 := bstep (se 2 (by rfl) ⟨882960, by rfl⟩ : syracuseStep 2354561 = 1765921) B1765921
theorem B3353987 : Blo 1568982 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B9063821 : Blo 1568982 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B2354579 : Blo 1568982 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B2354609 : Blo 1568982 2354609 := bstep (se 2 (by rfl) ⟨882978, by rfl⟩ : syracuseStep 2354609 = 1765957) B1765957
theorem B2649523 : Blo 1568982 2649523 := bstep (se 1 (by rfl) ⟨1987142, by rfl⟩ : syracuseStep 2649523 = 3974285) B3974285
theorem B2354627 : Blo 1568982 2354627 := bstep (se 1 (by rfl) ⟨1765970, by rfl⟩ : syracuseStep 2354627 = 3531941) B3531941
theorem B2354657 : Blo 1568982 2354657 := bstep (se 2 (by rfl) ⟨882996, by rfl⟩ : syracuseStep 2354657 = 1765993) B1765993
theorem B2354675 : Blo 1568982 2354675 := bstep (se 1 (by rfl) ⟨1766006, by rfl⟩ : syracuseStep 2354675 = 3532013) B3532013
theorem B2354705 : Blo 1568982 2354705 := bstep (se 2 (by rfl) ⟨883014, by rfl⟩ : syracuseStep 2354705 = 1766029) B1766029
theorem B3534353 : Blo 1568982 3534353 := bstep (se 2 (by rfl) ⟨1325382, by rfl⟩ : syracuseStep 3534353 = 2650765) B2650765
theorem B2354723 : Blo 1568982 2354723 := bstep (se 1 (by rfl) ⟨1766042, by rfl⟩ : syracuseStep 2354723 = 3532085) B3532085
theorem B3534371 : Blo 1568982 3534371 := bstep (se 1 (by rfl) ⟨2650778, by rfl⟩ : syracuseStep 3534371 = 5301557) B5301557
theorem B2354753 : Blo 1568982 2354753 := bstep (se 2 (by rfl) ⟨883032, by rfl⟩ : syracuseStep 2354753 = 1766065) B1766065
theorem B2649665 : Blo 1568982 2649665 := bstep (se 2 (by rfl) ⟨993624, by rfl⟩ : syracuseStep 2649665 = 1987249) B1987249
theorem B1986115 : Blo 1568982 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B2354771 : Blo 1568982 2354771 := bstep (se 1 (by rfl) ⟨1766078, by rfl⟩ : syracuseStep 2354771 = 3532157) B3532157
theorem B5295725 : Blo 1568982 5295725 := bstep (se 3 (by rfl) ⟨992948, by rfl⟩ : syracuseStep 5295725 = 1985897) B1985897
theorem B2354801 : Blo 1568982 2354801 := bstep (se 2 (by rfl) ⟨883050, by rfl⟩ : syracuseStep 2354801 = 1766101) B1766101
theorem B2354819 : Blo 1568982 2354819 := bstep (se 1 (by rfl) ⟨1766114, by rfl⟩ : syracuseStep 2354819 = 3532229) B3532229
theorem B2354849 : Blo 1568982 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B5295779 : Blo 1568982 5295779 := bstep (se 1 (by rfl) ⟨3971834, by rfl⟩ : syracuseStep 5295779 = 7943669) B7943669
theorem B1986211 : Blo 1568982 1986211 := bstep (se 1 (by rfl) ⟨1489658, by rfl⟩ : syracuseStep 1986211 = 2979317) B2979317
theorem B7949987 : Blo 1568982 7949987 := bstep (se 1 (by rfl) ⟨5962490, by rfl⟩ : syracuseStep 7949987 = 11924981) B11924981
theorem B2354867 : Blo 1568982 2354867 := bstep (se 1 (by rfl) ⟨1766150, by rfl⟩ : syracuseStep 2354867 = 3532301) B3532301
theorem B2649793 : Blo 1568982 2649793 := bstep (se 2 (by rfl) ⟨993672, by rfl⟩ : syracuseStep 2649793 = 1987345) B1987345
theorem B2354897 : Blo 1568982 2354897 := bstep (se 2 (by rfl) ⟨883086, by rfl⟩ : syracuseStep 2354897 = 1766173) B1766173
theorem B2354915 : Blo 1568982 2354915 := bstep (se 1 (by rfl) ⟨1766186, by rfl⟩ : syracuseStep 2354915 = 3532373) B3532373
theorem B2649827 : Blo 1568982 2649827 := bstep (se 1 (by rfl) ⟨1987370, by rfl⟩ : syracuseStep 2649827 = 3974741) B3974741
theorem B2354945 : Blo 1568982 2354945 := bstep (se 2 (by rfl) ⟨883104, by rfl⟩ : syracuseStep 2354945 = 1766209) B1766209
theorem B2354963 : Blo 1568982 2354963 := bstep (se 1 (by rfl) ⟨1766222, by rfl⟩ : syracuseStep 2354963 = 3532445) B3532445
theorem B3821347 : Blo 1568982 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2830115 : Blo 1568982 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B2354993 : Blo 1568982 2354993 := bstep (se 2 (by rfl) ⟨883122, by rfl⟩ : syracuseStep 2354993 = 1766245) B1766245
theorem B3534641 : Blo 1568982 3534641 := bstep (se 2 (by rfl) ⟨1325490, by rfl⟩ : syracuseStep 3534641 = 2650981) B2650981
theorem B2355011 : Blo 1568982 2355011 := bstep (se 1 (by rfl) ⟨1766258, by rfl⟩ : syracuseStep 2355011 = 3532517) B3532517
theorem B3534659 : Blo 1568982 3534659 := bstep (se 1 (by rfl) ⟨2650994, by rfl⟩ : syracuseStep 3534659 = 5301989) B5301989
theorem B2355041 : Blo 1568982 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B1765219 : Blo 1568982 1765219 := bstep (se 1 (by rfl) ⟨1323914, by rfl⟩ : syracuseStep 1765219 = 2647829) B2647829
theorem B2649955 : Blo 1568982 2649955 := bstep (se 1 (by rfl) ⟨1987466, by rfl⟩ : syracuseStep 2649955 = 3974933) B3974933
theorem B2355059 : Blo 1568982 2355059 := bstep (se 1 (by rfl) ⟨1766294, by rfl⟩ : syracuseStep 2355059 = 3532589) B3532589
theorem B2355089 : Blo 1568982 2355089 := bstep (se 2 (by rfl) ⟨883158, by rfl⟩ : syracuseStep 2355089 = 1766317) B1766317
theorem B2355107 : Blo 1568982 2355107 := bstep (se 1 (by rfl) ⟨1766330, by rfl⟩ : syracuseStep 2355107 = 3532661) B3532661
theorem B5296049 : Blo 1568982 5296049 := bstep (se 2 (by rfl) ⟨1986018, by rfl⟩ : syracuseStep 5296049 = 3972037) B3972037
theorem B2355137 : Blo 1568982 2355137 := bstep (se 2 (by rfl) ⟨883176, by rfl⟩ : syracuseStep 2355137 = 1766353) B1766353
theorem B2355155 : Blo 1568982 2355155 := bstep (se 1 (by rfl) ⟨1766366, by rfl⟩ : syracuseStep 2355155 = 3532733) B3532733
theorem B2355185 : Blo 1568982 2355185 := bstep (se 2 (by rfl) ⟨883194, by rfl⟩ : syracuseStep 2355185 = 1766389) B1766389
theorem B1765363 : Blo 1568982 1765363 := bstep (se 1 (by rfl) ⟨1324022, by rfl⟩ : syracuseStep 1765363 = 2648045) B2648045
theorem B2650097 : Blo 1568982 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B2355203 : Blo 1568982 2355203 := bstep (se 1 (by rfl) ⟨1766402, by rfl⟩ : syracuseStep 2355203 = 3532805) B3532805
theorem B2355233 : Blo 1568982 2355233 := bstep (se 2 (by rfl) ⟨883212, by rfl⟩ : syracuseStep 2355233 = 1766425) B1766425
theorem B5656625 : Blo 1568982 5656625 := bstep (se 2 (by rfl) ⟨2121234, by rfl⟩ : syracuseStep 5656625 = 4242469) B4242469
theorem B2355251 : Blo 1568982 2355251 := bstep (se 1 (by rfl) ⟨1766438, by rfl⟩ : syracuseStep 2355251 = 3532877) B3532877
theorem B2830403 : Blo 1568982 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B5959757 : Blo 1568982 5959757 := bstep (se 3 (by rfl) ⟨1117454, by rfl⟩ : syracuseStep 5959757 = 2234909) B2234909
theorem B2355281 : Blo 1568982 2355281 := bstep (se 2 (by rfl) ⟨883230, by rfl⟩ : syracuseStep 2355281 = 1766461) B1766461
theorem B2355299 : Blo 1568982 2355299 := bstep (se 1 (by rfl) ⟨1766474, by rfl⟩ : syracuseStep 2355299 = 3532949) B3532949
theorem B2650225 : Blo 1568982 2650225 := bstep (se 2 (by rfl) ⟨993834, by rfl⟩ : syracuseStep 2650225 = 1987669) B1987669
theorem B2355329 : Blo 1568982 2355329 := bstep (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) B1766497
theorem B1765507 : Blo 1568982 1765507 := bstep (se 1 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 1765507 = 2648261) B2648261
theorem B1986707 : Blo 1568982 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B2355347 : Blo 1568982 2355347 := bstep (se 1 (by rfl) ⟨1766510, by rfl⟩ : syracuseStep 2355347 = 3533021) B3533021
theorem B2650259 : Blo 1568982 2650259 := bstep (se 1 (by rfl) ⟨1987694, by rfl⟩ : syracuseStep 2650259 = 3975389) B3975389
theorem B2355377 : Blo 1568982 2355377 := bstep (se 2 (by rfl) ⟨883266, by rfl⟩ : syracuseStep 2355377 = 1766533) B1766533
theorem B2355395 : Blo 1568982 2355395 := bstep (se 1 (by rfl) ⟨1766546, by rfl⟩ : syracuseStep 2355395 = 3533093) B3533093
theorem B2355425 : Blo 1568982 2355425 := bstep (se 2 (by rfl) ⟨883284, by rfl⟩ : syracuseStep 2355425 = 1766569) B1766569
theorem B1568995 : Blo 1568982 1568995 := bstep (se 1 (by rfl) ⟨1176746, by rfl⟩ : syracuseStep 1568995 = 2353493) B2353493
theorem B3354851 : Blo 1568982 3354851 := bstep (se 1 (by rfl) ⟨2516138, by rfl⟩ : syracuseStep 3354851 = 5032277) B5032277
theorem B1569011 : Blo 1568982 1569011 := bstep (se 1 (by rfl) ⟨1176758, by rfl⟩ : syracuseStep 1569011 = 2353517) B2353517
theorem B2355443 : Blo 1568982 2355443 := bstep (se 1 (by rfl) ⟨1766582, by rfl⟩ : syracuseStep 2355443 = 3533165) B3533165
theorem B1569027 : Blo 1568982 1569027 := bstep (se 1 (by rfl) ⟨1176770, by rfl⟩ : syracuseStep 1569027 = 2353541) B2353541
theorem B2355473 : Blo 1568982 2355473 := bstep (se 2 (by rfl) ⟨883302, by rfl⟩ : syracuseStep 2355473 = 1766605) B1766605
theorem B1569043 : Blo 1568982 1569043 := bstep (se 1 (by rfl) ⟨1176782, by rfl⟩ : syracuseStep 1569043 = 2353565) B2353565
theorem B1765651 : Blo 1568982 1765651 := bstep (se 1 (by rfl) ⟨1324238, by rfl⟩ : syracuseStep 1765651 = 2648477) B2648477
theorem B2650387 : Blo 1568982 2650387 := bstep (se 1 (by rfl) ⟨1987790, by rfl⟩ : syracuseStep 2650387 = 3975581) B3975581
theorem B1569059 : Blo 1568982 1569059 := bstep (se 1 (by rfl) ⟨1176794, by rfl⟩ : syracuseStep 1569059 = 2353589) B2353589
theorem B2355491 : Blo 1568982 2355491 := bstep (se 1 (by rfl) ⟨1766618, by rfl⟩ : syracuseStep 2355491 = 3533237) B3533237
theorem B1569075 : Blo 1568982 1569075 := bstep (se 1 (by rfl) ⟨1176806, by rfl⟩ : syracuseStep 1569075 = 2353613) B2353613
theorem B2355521 : Blo 1568982 2355521 := bstep (se 2 (by rfl) ⟨883320, by rfl⟩ : syracuseStep 2355521 = 1766641) B1766641
theorem B1569091 : Blo 1568982 1569091 := bstep (se 1 (by rfl) ⟨1176818, by rfl⟩ : syracuseStep 1569091 = 2353637) B2353637
theorem B3354961 : Blo 1568982 3354961 := bstep (se 2 (by rfl) ⟨1258110, by rfl⟩ : syracuseStep 3354961 = 2516221) B2516221
theorem B1569107 : Blo 1568982 1569107 := bstep (se 1 (by rfl) ⟨1176830, by rfl⟩ : syracuseStep 1569107 = 2353661) B2353661
theorem B2355539 : Blo 1568982 2355539 := bstep (se 1 (by rfl) ⟨1766654, by rfl⟩ : syracuseStep 2355539 = 3533309) B3533309
theorem B1569123 : Blo 1568982 1569123 := bstep (se 1 (by rfl) ⟨1176842, by rfl⟩ : syracuseStep 1569123 = 2353685) B2353685
theorem B2355569 : Blo 1568982 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B1569139 : Blo 1568982 1569139 := bstep (se 1 (by rfl) ⟨1176854, by rfl⟩ : syracuseStep 1569139 = 2353709) B2353709
theorem B1569155 : Blo 1568982 1569155 := bstep (se 1 (by rfl) ⟨1176866, by rfl⟩ : syracuseStep 1569155 = 2353733) B2353733
theorem B2355587 : Blo 1568982 2355587 := bstep (se 1 (by rfl) ⟨1766690, by rfl⟩ : syracuseStep 2355587 = 3533381) B3533381
theorem B3821969 : Blo 1568982 3821969 := bstep (se 2 (by rfl) ⟨1433238, by rfl⟩ : syracuseStep 3821969 = 2866477) B2866477
theorem B1569171 : Blo 1568982 1569171 := bstep (se 1 (by rfl) ⟨1176878, by rfl⟩ : syracuseStep 1569171 = 2353757) B2353757
theorem B2355617 : Blo 1568982 2355617 := bstep (se 2 (by rfl) ⟨883356, by rfl⟩ : syracuseStep 2355617 = 1766713) B1766713
theorem B2650529 : Blo 1568982 2650529 := bstep (se 2 (by rfl) ⟨993948, by rfl⟩ : syracuseStep 2650529 = 1987897) B1987897
theorem B1569187 : Blo 1568982 1569187 := bstep (se 1 (by rfl) ⟨1176890, by rfl⟩ : syracuseStep 1569187 = 2353781) B2353781
theorem B1765795 : Blo 1568982 1765795 := bstep (se 1 (by rfl) ⟨1324346, by rfl⟩ : syracuseStep 1765795 = 2648693) B2648693
theorem B1569203 : Blo 1568982 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B2355635 : Blo 1568982 2355635 := bstep (se 1 (by rfl) ⟨1766726, by rfl⟩ : syracuseStep 2355635 = 3533453) B3533453
theorem B1569219 : Blo 1568982 1569219 := bstep (se 1 (by rfl) ⟨1176914, by rfl⟩ : syracuseStep 1569219 = 2353829) B2353829
theorem B5296589 : Blo 1568982 5296589 := bstep (se 3 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 5296589 = 1986221) B1986221
theorem B2355665 : Blo 1568982 2355665 := bstep (se 2 (by rfl) ⟨883374, by rfl⟩ : syracuseStep 2355665 = 1766749) B1766749
theorem B1569235 : Blo 1568982 1569235 := bstep (se 1 (by rfl) ⟨1176926, by rfl⟩ : syracuseStep 1569235 = 2353853) B2353853
theorem B7950797 : Blo 1568982 7950797 := bstep (se 3 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 7950797 = 2981549) B2981549
theorem B2421203 : Blo 1568982 2421203 := bstep (se 1 (by rfl) ⟨1815902, by rfl⟩ : syracuseStep 2421203 = 3631805) B3631805
theorem B11915747 : Blo 1568982 11915747 := bstep (se 1 (by rfl) ⟨8936810, by rfl⟩ : syracuseStep 11915747 = 17873621) B17873621
theorem B1569251 : Blo 1568982 1569251 := bstep (se 1 (by rfl) ⟨1176938, by rfl⟩ : syracuseStep 1569251 = 2353877) B2353877
theorem B1790435 : Blo 1568982 1790435 := bstep (se 1 (by rfl) ⟨1342826, by rfl⟩ : syracuseStep 1790435 = 2685653) B2685653
theorem B2355683 : Blo 1568982 2355683 := bstep (se 1 (by rfl) ⟨1766762, by rfl⟩ : syracuseStep 2355683 = 3533525) B3533525
theorem B1569267 : Blo 1568982 1569267 := bstep (se 1 (by rfl) ⟨1176950, by rfl⟩ : syracuseStep 1569267 = 2353901) B2353901
theorem B1569283 : Blo 1568982 1569283 := bstep (se 1 (by rfl) ⟨1176962, by rfl⟩ : syracuseStep 1569283 = 2353925) B2353925
theorem B5296643 : Blo 1568982 5296643 := bstep (se 1 (by rfl) ⟨3972482, by rfl⟩ : syracuseStep 5296643 = 7944965) B7944965
theorem B2355713 : Blo 1568982 2355713 := bstep (se 2 (by rfl) ⟨883392, by rfl⟩ : syracuseStep 2355713 = 1766785) B1766785
theorem B1569299 : Blo 1568982 1569299 := bstep (se 1 (by rfl) ⟨1176974, by rfl⟩ : syracuseStep 1569299 = 2353949) B2353949
theorem B2355731 : Blo 1568982 2355731 := bstep (se 1 (by rfl) ⟨1766798, by rfl⟩ : syracuseStep 2355731 = 3533597) B3533597
theorem B2650657 : Blo 1568982 2650657 := bstep (se 2 (by rfl) ⟨993996, by rfl⟩ : syracuseStep 2650657 = 1987993) B1987993
theorem B1569315 : Blo 1568982 1569315 := bstep (se 1 (by rfl) ⟨1176986, by rfl⟩ : syracuseStep 1569315 = 2353973) B2353973
theorem B2355761 : Blo 1568982 2355761 := bstep (se 2 (by rfl) ⟨883410, by rfl⟩ : syracuseStep 2355761 = 1766821) B1766821
theorem B1569331 : Blo 1568982 1569331 := bstep (se 1 (by rfl) ⟨1176998, by rfl⟩ : syracuseStep 1569331 = 2353997) B2353997
theorem B1765939 : Blo 1568982 1765939 := bstep (se 1 (by rfl) ⟨1324454, by rfl⟩ : syracuseStep 1765939 = 2648909) B2648909
theorem B1569347 : Blo 1568982 1569347 := bstep (se 1 (by rfl) ⟨1177010, by rfl⟩ : syracuseStep 1569347 = 2354021) B2354021
theorem B2355779 : Blo 1568982 2355779 := bstep (se 1 (by rfl) ⟨1766834, by rfl⟩ : syracuseStep 2355779 = 3533669) B3533669
theorem B2650691 : Blo 1568982 2650691 := bstep (se 1 (by rfl) ⟨1988018, by rfl⟩ : syracuseStep 2650691 = 3976037) B3976037
theorem B1569363 : Blo 1568982 1569363 := bstep (se 1 (by rfl) ⟨1177022, by rfl⟩ : syracuseStep 1569363 = 2354045) B2354045
theorem B2355809 : Blo 1568982 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B1569379 : Blo 1568982 1569379 := bstep (se 1 (by rfl) ⟨1177034, by rfl⟩ : syracuseStep 1569379 = 2354069) B2354069
theorem B6451811 : Blo 1568982 6451811 := bstep (se 1 (by rfl) ⟨4838858, by rfl⟩ : syracuseStep 6451811 = 9677717) B9677717
theorem B1569395 : Blo 1568982 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B2355827 : Blo 1568982 2355827 := bstep (se 1 (by rfl) ⟨1766870, by rfl⟩ : syracuseStep 2355827 = 3533741) B3533741
theorem B1569411 : Blo 1568982 1569411 := bstep (se 1 (by rfl) ⟨1177058, by rfl⟩ : syracuseStep 1569411 = 2354117) B2354117
theorem B5026445 : Blo 1568982 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B2355857 : Blo 1568982 2355857 := bstep (se 2 (by rfl) ⟨883446, by rfl⟩ : syracuseStep 2355857 = 1766893) B1766893
theorem B1569427 : Blo 1568982 1569427 := bstep (se 1 (by rfl) ⟨1177070, by rfl⟩ : syracuseStep 1569427 = 2354141) B2354141
theorem B1569443 : Blo 1568982 1569443 := bstep (se 1 (by rfl) ⟨1177082, by rfl⟩ : syracuseStep 1569443 = 2354165) B2354165
theorem B2355875 : Blo 1568982 2355875 := bstep (se 1 (by rfl) ⟨1766906, by rfl⟩ : syracuseStep 2355875 = 3533813) B3533813
theorem B1569459 : Blo 1568982 1569459 := bstep (se 1 (by rfl) ⟨1177094, by rfl⟩ : syracuseStep 1569459 = 2354189) B2354189
theorem B2355905 : Blo 1568982 2355905 := bstep (se 2 (by rfl) ⟨883464, by rfl⟩ : syracuseStep 2355905 = 1766929) B1766929
theorem B1569475 : Blo 1568982 1569475 := bstep (se 1 (by rfl) ⟨1177106, by rfl⟩ : syracuseStep 1569475 = 2354213) B2354213
theorem B1766083 : Blo 1568982 1766083 := bstep (se 1 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 1766083 = 2649125) B2649125
theorem B2650819 : Blo 1568982 2650819 := bstep (se 1 (by rfl) ⟨1988114, by rfl⟩ : syracuseStep 2650819 = 3976229) B3976229
theorem B1569491 : Blo 1568982 1569491 := bstep (se 1 (by rfl) ⟨1177118, by rfl⟩ : syracuseStep 1569491 = 2354237) B2354237
theorem B2355923 : Blo 1568982 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B8483555 : Blo 1568982 8483555 := bstep (se 1 (by rfl) ⟨6362666, by rfl⟩ : syracuseStep 8483555 = 12725333) B12725333
theorem B1569507 : Blo 1568982 1569507 := bstep (se 1 (by rfl) ⟨1177130, by rfl⟩ : syracuseStep 1569507 = 2354261) B2354261
theorem B4469489 : Blo 1568982 4469489 := bstep (se 2 (by rfl) ⟨1676058, by rfl⟩ : syracuseStep 4469489 = 3352117) B3352117
theorem B2355953 : Blo 1568982 2355953 := bstep (se 2 (by rfl) ⟨883482, by rfl⟩ : syracuseStep 2355953 = 1766965) B1766965
theorem B1569523 : Blo 1568982 1569523 := bstep (se 1 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 1569523 = 2354285) B2354285
theorem B1569539 : Blo 1568982 1569539 := bstep (se 1 (by rfl) ⟨1177154, by rfl⟩ : syracuseStep 1569539 = 2354309) B2354309
theorem B2355971 : Blo 1568982 2355971 := bstep (se 1 (by rfl) ⟨1766978, by rfl⟩ : syracuseStep 2355971 = 3533957) B3533957
theorem B5296913 : Blo 1568982 5296913 := bstep (se 2 (by rfl) ⟨1986342, by rfl⟩ : syracuseStep 5296913 = 3972685) B3972685
theorem B1569555 : Blo 1568982 1569555 := bstep (se 1 (by rfl) ⟨1177166, by rfl⟩ : syracuseStep 1569555 = 2354333) B2354333
theorem B2356001 : Blo 1568982 2356001 := bstep (se 2 (by rfl) ⟨883500, by rfl⟩ : syracuseStep 2356001 = 1767001) B1767001
theorem B1569571 : Blo 1568982 1569571 := bstep (se 1 (by rfl) ⟨1177178, by rfl⟩ : syracuseStep 1569571 = 2354357) B2354357
theorem B1569587 : Blo 1568982 1569587 := bstep (se 1 (by rfl) ⟨1177190, by rfl⟩ : syracuseStep 1569587 = 2354381) B2354381
theorem B2356019 : Blo 1568982 2356019 := bstep (se 1 (by rfl) ⟨1767014, by rfl⟩ : syracuseStep 2356019 = 3534029) B3534029
theorem B1569603 : Blo 1568982 1569603 := bstep (se 1 (by rfl) ⟨1177202, by rfl⟩ : syracuseStep 1569603 = 2354405) B2354405
theorem B15086405 : Blo 1568982 15086405 := bstep (se 4 (by rfl) ⟨1414350, by rfl⟩ : syracuseStep 15086405 = 2828701) B2828701
theorem B5026637 : Blo 1568982 5026637 := bstep (se 3 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 5026637 = 1884989) B1884989
theorem B2356049 : Blo 1568982 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B2650961 : Blo 1568982 2650961 := bstep (se 2 (by rfl) ⟨994110, by rfl⟩ : syracuseStep 2650961 = 1988221) B1988221
theorem B1569619 : Blo 1568982 1569619 := bstep (se 1 (by rfl) ⟨1177214, by rfl⟩ : syracuseStep 1569619 = 2354429) B2354429
theorem B1766227 : Blo 1568982 1766227 := bstep (se 1 (by rfl) ⟨1324670, by rfl⟩ : syracuseStep 1766227 = 2649341) B2649341
theorem B1987411 : Blo 1568982 1987411 := bstep (se 1 (by rfl) ⟨1490558, by rfl⟩ : syracuseStep 1987411 = 2981117) B2981117
theorem B1569635 : Blo 1568982 1569635 := bstep (se 1 (by rfl) ⟨1177226, by rfl⟩ : syracuseStep 1569635 = 2354453) B2354453
theorem B2356067 : Blo 1568982 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1569651 : Blo 1568982 1569651 := bstep (se 1 (by rfl) ⟨1177238, by rfl⟩ : syracuseStep 1569651 = 2354477) B2354477
theorem B1569667 : Blo 1568982 1569667 := bstep (se 1 (by rfl) ⟨1177250, by rfl⟩ : syracuseStep 1569667 = 2354501) B2354501
theorem B2356097 : Blo 1568982 2356097 := bstep (se 2 (by rfl) ⟨883536, by rfl⟩ : syracuseStep 2356097 = 1767073) B1767073
theorem B6706061 : Blo 1568982 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B1569683 : Blo 1568982 1569683 := bstep (se 1 (by rfl) ⟨1177262, by rfl⟩ : syracuseStep 1569683 = 2354525) B2354525
theorem B2356115 : Blo 1568982 2356115 := bstep (se 1 (by rfl) ⟨1767086, by rfl⟩ : syracuseStep 2356115 = 3534173) B3534173
theorem B1569699 : Blo 1568982 1569699 := bstep (se 1 (by rfl) ⟨1177274, by rfl⟩ : syracuseStep 1569699 = 2354549) B2354549
theorem B4469681 : Blo 1568982 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B2356145 : Blo 1568982 2356145 := bstep (se 2 (by rfl) ⟨883554, by rfl⟩ : syracuseStep 2356145 = 1767109) B1767109
theorem B1569715 : Blo 1568982 1569715 := bstep (se 1 (by rfl) ⟨1177286, by rfl⟩ : syracuseStep 1569715 = 2354573) B2354573
theorem B1987507 : Blo 1568982 1987507 := bstep (se 1 (by rfl) ⟨1490630, by rfl⟩ : syracuseStep 1987507 = 2981261) B2981261
theorem B1569731 : Blo 1568982 1569731 := bstep (se 1 (by rfl) ⟨1177298, by rfl⟩ : syracuseStep 1569731 = 2354597) B2354597
theorem B2356163 : Blo 1568982 2356163 := bstep (se 1 (by rfl) ⟨1767122, by rfl⟩ : syracuseStep 2356163 = 3534245) B3534245
theorem B1569747 : Blo 1568982 1569747 := bstep (se 1 (by rfl) ⟨1177310, by rfl⟩ : syracuseStep 1569747 = 2354621) B2354621
theorem B2356193 : Blo 1568982 2356193 := bstep (se 2 (by rfl) ⟨883572, by rfl⟩ : syracuseStep 2356193 = 1767145) B1767145
theorem B1569763 : Blo 1568982 1569763 := bstep (se 1 (by rfl) ⟨1177322, by rfl⟩ : syracuseStep 1569763 = 2354645) B2354645
theorem B1766371 : Blo 1568982 1766371 := bstep (se 1 (by rfl) ⟨1324778, by rfl⟩ : syracuseStep 1766371 = 2649557) B2649557
theorem B4772849 : Blo 1568982 4772849 := bstep (se 2 (by rfl) ⟨1789818, by rfl⟩ : syracuseStep 4772849 = 3579637) B3579637
theorem B1569779 : Blo 1568982 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B2356211 : Blo 1568982 2356211 := bstep (se 1 (by rfl) ⟨1767158, by rfl⟩ : syracuseStep 2356211 = 3534317) B3534317
theorem B1569795 : Blo 1568982 1569795 := bstep (se 1 (by rfl) ⟨1177346, by rfl⟩ : syracuseStep 1569795 = 2354693) B2354693
theorem B1569811 : Blo 1568982 1569811 := bstep (se 1 (by rfl) ⟨1177358, by rfl⟩ : syracuseStep 1569811 = 2354717) B2354717
theorem B2356241 : Blo 1568982 2356241 := bstep (se 2 (by rfl) ⟨883590, by rfl⟩ : syracuseStep 2356241 = 1767181) B1767181
theorem B2683937 : Blo 1568982 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B1569827 : Blo 1568982 1569827 := bstep (se 1 (by rfl) ⟨1177370, by rfl⟩ : syracuseStep 1569827 = 2354741) B2354741
theorem B2356259 : Blo 1568982 2356259 := bstep (se 1 (by rfl) ⟨1767194, by rfl⟩ : syracuseStep 2356259 = 3534389) B3534389
theorem B1569843 : Blo 1568982 1569843 := bstep (se 1 (by rfl) ⟨1177382, by rfl⟩ : syracuseStep 1569843 = 2354765) B2354765
theorem B2356289 : Blo 1568982 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B1569859 : Blo 1568982 1569859 := bstep (se 1 (by rfl) ⟨1177394, by rfl⟩ : syracuseStep 1569859 = 2354789) B2354789
theorem B1569875 : Blo 1568982 1569875 := bstep (se 1 (by rfl) ⟨1177406, by rfl⟩ : syracuseStep 1569875 = 2354813) B2354813
theorem B2356307 : Blo 1568982 2356307 := bstep (se 1 (by rfl) ⟨1767230, by rfl⟩ : syracuseStep 2356307 = 3534461) B3534461
theorem B1676387 : Blo 1568982 1676387 := bstep (se 1 (by rfl) ⟨1257290, by rfl⟩ : syracuseStep 1676387 = 2514581) B2514581
theorem B1569891 : Blo 1568982 1569891 := bstep (se 1 (by rfl) ⟨1177418, by rfl⟩ : syracuseStep 1569891 = 2354837) B2354837
theorem B2356337 : Blo 1568982 2356337 := bstep (se 2 (by rfl) ⟨883626, by rfl⟩ : syracuseStep 2356337 = 1767253) B1767253
theorem B1569907 : Blo 1568982 1569907 := bstep (se 1 (by rfl) ⟨1177430, by rfl⟩ : syracuseStep 1569907 = 2354861) B2354861
theorem B1766515 : Blo 1568982 1766515 := bstep (se 1 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 1766515 = 2649773) B2649773
theorem B1569923 : Blo 1568982 1569923 := bstep (se 1 (by rfl) ⟨1177442, by rfl⟩ : syracuseStep 1569923 = 2354885) B2354885
theorem B2356355 : Blo 1568982 2356355 := bstep (se 1 (by rfl) ⟨1767266, by rfl⟩ : syracuseStep 2356355 = 3534533) B3534533
theorem B1569939 : Blo 1568982 1569939 := bstep (se 1 (by rfl) ⟨1177454, by rfl⟩ : syracuseStep 1569939 = 2354909) B2354909
theorem B2356385 : Blo 1568982 2356385 := bstep (se 2 (by rfl) ⟨883644, by rfl⟩ : syracuseStep 2356385 = 1767289) B1767289
theorem B1569955 : Blo 1568982 1569955 := bstep (se 1 (by rfl) ⟨1177466, by rfl⟩ : syracuseStep 1569955 = 2354933) B2354933
theorem B7943345 : Blo 1568982 7943345 := bstep (se 2 (by rfl) ⟨2978754, by rfl⟩ : syracuseStep 7943345 = 5957509) B5957509
theorem B1569971 : Blo 1568982 1569971 := bstep (se 1 (by rfl) ⟨1177478, by rfl⟩ : syracuseStep 1569971 = 2354957) B2354957
theorem B2356403 : Blo 1568982 2356403 := bstep (se 1 (by rfl) ⟨1767302, by rfl⟩ : syracuseStep 2356403 = 3534605) B3534605
theorem B1569987 : Blo 1568982 1569987 := bstep (se 1 (by rfl) ⟨1177490, by rfl⟩ : syracuseStep 1569987 = 2354981) B2354981
theorem B2356433 : Blo 1568982 2356433 := bstep (se 2 (by rfl) ⟨883662, by rfl⟩ : syracuseStep 2356433 = 1767325) B1767325
theorem B1570003 : Blo 1568982 1570003 := bstep (se 1 (by rfl) ⟨1177502, by rfl⟩ : syracuseStep 1570003 = 2355005) B2355005
theorem B1570019 : Blo 1568982 1570019 := bstep (se 1 (by rfl) ⟨1177514, by rfl⟩ : syracuseStep 1570019 = 2355029) B2355029
theorem B2356451 : Blo 1568982 2356451 := bstep (se 1 (by rfl) ⟨1767338, by rfl⟩ : syracuseStep 2356451 = 3534677) B3534677
theorem B1570035 : Blo 1568982 1570035 := bstep (se 1 (by rfl) ⟨1177526, by rfl⟩ : syracuseStep 1570035 = 2355053) B2355053
theorem B1570051 : Blo 1568982 1570051 := bstep (se 1 (by rfl) ⟨1177538, by rfl⟩ : syracuseStep 1570051 = 2355077) B2355077
theorem B1766659 : Blo 1568982 1766659 := bstep (se 1 (by rfl) ⟨1324994, by rfl⟩ : syracuseStep 1766659 = 2649989) B2649989
theorem B2979089 : Blo 1568982 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B1570067 : Blo 1568982 1570067 := bstep (se 1 (by rfl) ⟨1177550, by rfl⟩ : syracuseStep 1570067 = 2355101) B2355101
theorem B1570083 : Blo 1568982 1570083 := bstep (se 1 (by rfl) ⟨1177562, by rfl⟩ : syracuseStep 1570083 = 2355125) B2355125
theorem B5297453 : Blo 1568982 5297453 := bstep (se 3 (by rfl) ⟨993272, by rfl⟩ : syracuseStep 5297453 = 1986545) B1986545
theorem B10736945 : Blo 1568982 10736945 := bstep (se 2 (by rfl) ⟨4026354, by rfl⟩ : syracuseStep 10736945 = 8052709) B8052709
theorem B1570099 : Blo 1568982 1570099 := bstep (se 1 (by rfl) ⟨1177574, by rfl⟩ : syracuseStep 1570099 = 2355149) B2355149
theorem B1570115 : Blo 1568982 1570115 := bstep (se 1 (by rfl) ⟨1177586, by rfl⟩ : syracuseStep 1570115 = 2355173) B2355173
theorem B1570131 : Blo 1568982 1570131 := bstep (se 1 (by rfl) ⟨1177598, by rfl⟩ : syracuseStep 1570131 = 2355197) B2355197
theorem B5297507 : Blo 1568982 5297507 := bstep (se 1 (by rfl) ⟨3973130, by rfl⟩ : syracuseStep 5297507 = 7946261) B7946261
theorem B1570147 : Blo 1568982 1570147 := bstep (se 1 (by rfl) ⟨1177610, by rfl⟩ : syracuseStep 1570147 = 2355221) B2355221
theorem B1570163 : Blo 1568982 1570163 := bstep (se 1 (by rfl) ⟨1177622, by rfl⟩ : syracuseStep 1570163 = 2355245) B2355245
theorem B1570179 : Blo 1568982 1570179 := bstep (se 1 (by rfl) ⟨1177634, by rfl⟩ : syracuseStep 1570179 = 2355269) B2355269
theorem B10065293 : Blo 1568982 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B1570195 : Blo 1568982 1570195 := bstep (se 1 (by rfl) ⟨1177646, by rfl⟩ : syracuseStep 1570195 = 2355293) B2355293
theorem B1766803 : Blo 1568982 1766803 := bstep (se 1 (by rfl) ⟨1325102, by rfl⟩ : syracuseStep 1766803 = 2650205) B2650205
theorem B1570211 : Blo 1568982 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B8058275 : Blo 1568982 8058275 := bstep (se 1 (by rfl) ⟨6043706, by rfl⟩ : syracuseStep 8058275 = 12087413) B12087413
theorem B1988003 : Blo 1568982 1988003 := bstep (se 1 (by rfl) ⟨1491002, by rfl⟩ : syracuseStep 1988003 = 2982005) B2982005
theorem B1570227 : Blo 1568982 1570227 := bstep (se 1 (by rfl) ⟨1177670, by rfl⟩ : syracuseStep 1570227 = 2355341) B2355341
theorem B1570243 : Blo 1568982 1570243 := bstep (se 1 (by rfl) ⟨1177682, by rfl⟩ : syracuseStep 1570243 = 2355365) B2355365
theorem B1570259 : Blo 1568982 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B1570275 : Blo 1568982 1570275 := bstep (se 1 (by rfl) ⟨1177706, by rfl⟩ : syracuseStep 1570275 = 2355413) B2355413
theorem B1570291 : Blo 1568982 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1570307 : Blo 1568982 1570307 := bstep (se 1 (by rfl) ⟨1177730, by rfl⟩ : syracuseStep 1570307 = 2355461) B2355461
theorem B1570323 : Blo 1568982 1570323 := bstep (se 1 (by rfl) ⟨1177742, by rfl⟩ : syracuseStep 1570323 = 2355485) B2355485
theorem B2684449 : Blo 1568982 2684449 := bstep (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) B2013337
theorem B1570339 : Blo 1568982 1570339 := bstep (se 1 (by rfl) ⟨1177754, by rfl⟩ : syracuseStep 1570339 = 2355509) B2355509
theorem B1766947 : Blo 1568982 1766947 := bstep (se 1 (by rfl) ⟨1325210, by rfl⟩ : syracuseStep 1766947 = 2650421) B2650421
theorem B1570355 : Blo 1568982 1570355 := bstep (se 1 (by rfl) ⟨1177766, by rfl⟩ : syracuseStep 1570355 = 2355533) B2355533
theorem B1570371 : Blo 1568982 1570371 := bstep (se 1 (by rfl) ⟨1177778, by rfl⟩ : syracuseStep 1570371 = 2355557) B2355557
theorem B1570387 : Blo 1568982 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B1570403 : Blo 1568982 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B5297777 : Blo 1568982 5297777 := bstep (se 2 (by rfl) ⟨1986666, by rfl⟩ : syracuseStep 5297777 = 3973333) B3973333
theorem B1570419 : Blo 1568982 1570419 := bstep (se 1 (by rfl) ⟨1177814, by rfl⟩ : syracuseStep 1570419 = 2355629) B2355629
theorem B1570435 : Blo 1568982 1570435 := bstep (se 1 (by rfl) ⟨1177826, by rfl⟩ : syracuseStep 1570435 = 2355653) B2355653
theorem B1570451 : Blo 1568982 1570451 := bstep (se 1 (by rfl) ⟨1177838, by rfl⟩ : syracuseStep 1570451 = 2355677) B2355677
theorem B7648931 : Blo 1568982 7648931 := bstep (se 1 (by rfl) ⟨5736698, by rfl⟩ : syracuseStep 7648931 = 11473397) B11473397
theorem B1570467 : Blo 1568982 1570467 := bstep (se 1 (by rfl) ⟨1177850, by rfl⟩ : syracuseStep 1570467 = 2355701) B2355701
theorem B8943281 : Blo 1568982 8943281 := bstep (se 2 (by rfl) ⟨3353730, by rfl⟩ : syracuseStep 8943281 = 6707461) B6707461
theorem B1570483 : Blo 1568982 1570483 := bstep (se 1 (by rfl) ⟨1177862, by rfl⟩ : syracuseStep 1570483 = 2355725) B2355725
theorem B1767091 : Blo 1568982 1767091 := bstep (se 1 (by rfl) ⟨1325318, by rfl⟩ : syracuseStep 1767091 = 2650637) B2650637
theorem B1570499 : Blo 1568982 1570499 := bstep (se 1 (by rfl) ⟨1177874, by rfl⟩ : syracuseStep 1570499 = 2355749) B2355749
theorem B1570515 : Blo 1568982 1570515 := bstep (se 1 (by rfl) ⟨1177886, by rfl⟩ : syracuseStep 1570515 = 2355773) B2355773
theorem B1570531 : Blo 1568982 1570531 := bstep (se 1 (by rfl) ⟨1177898, by rfl⟩ : syracuseStep 1570531 = 2355797) B2355797
theorem B1570547 : Blo 1568982 1570547 := bstep (se 1 (by rfl) ⟨1177910, by rfl⟩ : syracuseStep 1570547 = 2355821) B2355821
theorem B1570563 : Blo 1568982 1570563 := bstep (se 1 (by rfl) ⟨1177922, by rfl⟩ : syracuseStep 1570563 = 2355845) B2355845
theorem B1570579 : Blo 1568982 1570579 := bstep (se 1 (by rfl) ⟨1177934, by rfl⟩ : syracuseStep 1570579 = 2355869) B2355869
theorem B33969941 : Blo 1568982 33969941 := bstep (se 6 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 33969941 = 1592341) B1592341
theorem B1570595 : Blo 1568982 1570595 := bstep (se 1 (by rfl) ⟨1177946, by rfl⟩ : syracuseStep 1570595 = 2355893) B2355893
theorem B1570611 : Blo 1568982 1570611 := bstep (se 1 (by rfl) ⟨1177958, by rfl⟩ : syracuseStep 1570611 = 2355917) B2355917
theorem B1570627 : Blo 1568982 1570627 := bstep (se 1 (by rfl) ⟨1177970, by rfl⟩ : syracuseStep 1570627 = 2355941) B2355941
theorem B1767235 : Blo 1568982 1767235 := bstep (se 1 (by rfl) ⟨1325426, by rfl⟩ : syracuseStep 1767235 = 2650853) B2650853
theorem B2266961 : Blo 1568982 2266961 := bstep (se 2 (by rfl) ⟨850110, by rfl⟩ : syracuseStep 2266961 = 1700221) B1700221
theorem B1570643 : Blo 1568982 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B1570659 : Blo 1568982 1570659 := bstep (se 1 (by rfl) ⟨1177994, by rfl⟩ : syracuseStep 1570659 = 2355989) B2355989
theorem B5371757 : Blo 1568982 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B1570675 : Blo 1568982 1570675 := bstep (se 1 (by rfl) ⟨1178006, by rfl⟩ : syracuseStep 1570675 = 2356013) B2356013
theorem B2234243 : Blo 1568982 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B1570691 : Blo 1568982 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B4470673 : Blo 1568982 4470673 := bstep (se 2 (by rfl) ⟨1676502, by rfl⟩ : syracuseStep 4470673 = 3353005) B3353005
theorem B1570707 : Blo 1568982 1570707 := bstep (se 1 (by rfl) ⟨1178030, by rfl⟩ : syracuseStep 1570707 = 2356061) B2356061
theorem B1570723 : Blo 1568982 1570723 := bstep (se 1 (by rfl) ⟨1178042, by rfl⟩ : syracuseStep 1570723 = 2356085) B2356085
theorem B1570739 : Blo 1568982 1570739 := bstep (se 1 (by rfl) ⟨1178054, by rfl⟩ : syracuseStep 1570739 = 2356109) B2356109
theorem B1570755 : Blo 1568982 1570755 := bstep (se 1 (by rfl) ⟨1178066, by rfl⟩ : syracuseStep 1570755 = 2356133) B2356133
theorem B1570771 : Blo 1568982 1570771 := bstep (se 1 (by rfl) ⟨1178078, by rfl⟩ : syracuseStep 1570771 = 2356157) B2356157
theorem B1570787 : Blo 1568982 1570787 := bstep (se 1 (by rfl) ⟨1178090, by rfl⟩ : syracuseStep 1570787 = 2356181) B2356181
theorem B1570803 : Blo 1568982 1570803 := bstep (se 1 (by rfl) ⟨1178102, by rfl⟩ : syracuseStep 1570803 = 2356205) B2356205
theorem B1570819 : Blo 1568982 1570819 := bstep (se 1 (by rfl) ⟨1178114, by rfl⟩ : syracuseStep 1570819 = 2356229) B2356229
theorem B1570835 : Blo 1568982 1570835 := bstep (se 1 (by rfl) ⟨1178126, by rfl⟩ : syracuseStep 1570835 = 2356253) B2356253
theorem B1570851 : Blo 1568982 1570851 := bstep (se 1 (by rfl) ⟨1178138, by rfl⟩ : syracuseStep 1570851 = 2356277) B2356277
theorem B1570867 : Blo 1568982 1570867 := bstep (se 1 (by rfl) ⟨1178150, by rfl⟩ : syracuseStep 1570867 = 2356301) B2356301
theorem B1570883 : Blo 1568982 1570883 := bstep (se 1 (by rfl) ⟨1178162, by rfl⟩ : syracuseStep 1570883 = 2356325) B2356325
theorem B1677395 : Blo 1568982 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B1570899 : Blo 1568982 1570899 := bstep (se 1 (by rfl) ⟨1178174, by rfl⟩ : syracuseStep 1570899 = 2356349) B2356349
theorem B10336355 : Blo 1568982 10336355 := bstep (se 1 (by rfl) ⟨7752266, by rfl⟩ : syracuseStep 10336355 = 15504533) B15504533
theorem B1570915 : Blo 1568982 1570915 := bstep (se 1 (by rfl) ⟨1178186, by rfl⟩ : syracuseStep 1570915 = 2356373) B2356373
theorem B1570931 : Blo 1568982 1570931 := bstep (se 1 (by rfl) ⟨1178198, by rfl⟩ : syracuseStep 1570931 = 2356397) B2356397
theorem B1570947 : Blo 1568982 1570947 := bstep (se 1 (by rfl) ⟨1178210, by rfl⟩ : syracuseStep 1570947 = 2356421) B2356421
theorem B5298317 : Blo 1568982 5298317 := bstep (se 3 (by rfl) ⟨993434, by rfl⟩ : syracuseStep 5298317 = 1986869) B1986869
theorem B5961869 : Blo 1568982 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B2979985 : Blo 1568982 2979985 := bstep (se 2 (by rfl) ⟨1117494, by rfl⟩ : syracuseStep 2979985 = 2234989) B2234989
theorem B1570963 : Blo 1568982 1570963 := bstep (se 1 (by rfl) ⟨1178222, by rfl⟩ : syracuseStep 1570963 = 2356445) B2356445
theorem B4470947 : Blo 1568982 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B1570979 : Blo 1568982 1570979 := bstep (se 1 (by rfl) ⟨1178234, by rfl⟩ : syracuseStep 1570979 = 2356469) B2356469
theorem B5298371 : Blo 1568982 5298371 := bstep (se 1 (by rfl) ⟨3973778, by rfl⟩ : syracuseStep 5298371 = 7947557) B7947557
theorem B4774115 : Blo 1568982 4774115 := bstep (se 1 (by rfl) ⟨3580586, by rfl⟩ : syracuseStep 4774115 = 7161173) B7161173
theorem B2980145 : Blo 1568982 2980145 := bstep (se 2 (by rfl) ⟨1117554, by rfl⟩ : syracuseStep 2980145 = 2235109) B2235109
theorem B4471139 : Blo 1568982 4471139 := bstep (se 1 (by rfl) ⟨3353354, by rfl⟩ : syracuseStep 4471139 = 6706709) B6706709
theorem B12900721 : Blo 1568982 12900721 := bstep (se 2 (by rfl) ⟨4837770, by rfl⟩ : syracuseStep 12900721 = 9675541) B9675541
theorem B2388275 : Blo 1568982 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B5298641 : Blo 1568982 5298641 := bstep (se 2 (by rfl) ⟨1986990, by rfl⟩ : syracuseStep 5298641 = 3973981) B3973981
theorem B13408739 : Blo 1568982 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B7158257 : Blo 1568982 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B2234881 : Blo 1568982 2234881 := bstep (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) B1676161
theorem B5028419 : Blo 1568982 5028419 := bstep (se 1 (by rfl) ⟨3771314, by rfl⟩ : syracuseStep 5028419 = 7542629) B7542629
theorem B7944803 : Blo 1568982 7944803 := bstep (se 1 (by rfl) ⟨5958602, by rfl⟩ : syracuseStep 7944803 = 11917205) B11917205
theorem B19094129 : Blo 1568982 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B2980547 : Blo 1568982 2980547 := bstep (se 1 (by rfl) ⟨2235410, by rfl⟩ : syracuseStep 2980547 = 4470821) B4470821
theorem B3971825 : Blo 1568982 3971825 := bstep (se 2 (by rfl) ⟨1489434, by rfl⟩ : syracuseStep 3971825 = 2978869) B2978869
theorem B3971875 : Blo 1568982 3971875 := bstep (se 1 (by rfl) ⟨2978906, by rfl⟩ : syracuseStep 3971875 = 5957813) B5957813
theorem B2513729 : Blo 1568982 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B2235217 : Blo 1568982 2235217 := bstep (se 2 (by rfl) ⟨838206, by rfl⟩ : syracuseStep 2235217 = 1676413) B1676413
theorem B25475953 : Blo 1568982 25475953 := bstep (se 2 (by rfl) ⟨9553482, by rfl⟩ : syracuseStep 25475953 = 19106965) B19106965
theorem B3972017 : Blo 1568982 3972017 := bstep (se 2 (by rfl) ⟨1489506, by rfl⟩ : syracuseStep 3972017 = 2979013) B2979013
theorem B5962673 : Blo 1568982 5962673 := bstep (se 2 (by rfl) ⟨2236002, by rfl⟩ : syracuseStep 5962673 = 4472005) B4472005
theorem B5299181 : Blo 1568982 5299181 := bstep (se 3 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 5299181 = 1987193) B1987193
theorem B2513953 : Blo 1568982 2513953 := bstep (se 2 (by rfl) ⟨942732, by rfl⟩ : syracuseStep 2513953 = 1885465) B1885465
theorem B5299235 : Blo 1568982 5299235 := bstep (se 1 (by rfl) ⟨3974426, by rfl⟩ : syracuseStep 5299235 = 7948853) B7948853
theorem B2514017 : Blo 1568982 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B15285347 : Blo 1568982 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B8944739 : Blo 1568982 8944739 := bstep (se 1 (by rfl) ⟨6708554, by rfl⟩ : syracuseStep 8944739 = 13417109) B13417109
theorem B4471949 : Blo 1568982 4471949 := bstep (se 3 (by rfl) ⟨838490, by rfl⟩ : syracuseStep 4471949 = 1676981) B1676981
theorem B2514145 : Blo 1568982 2514145 := bstep (se 2 (by rfl) ⟨942804, by rfl⟩ : syracuseStep 2514145 = 1885609) B1885609
theorem B8936675 : Blo 1568982 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B5659939 : Blo 1568982 5659939 := bstep (se 1 (by rfl) ⟨4244954, by rfl⟩ : syracuseStep 5659939 = 8489909) B8489909
theorem B5299505 : Blo 1568982 5299505 := bstep (se 2 (by rfl) ⟨1987314, by rfl⟩ : syracuseStep 5299505 = 3974629) B3974629
theorem B4472131 : Blo 1568982 4472131 := bstep (se 1 (by rfl) ⟨3354098, by rfl⟩ : syracuseStep 4472131 = 6708197) B6708197
theorem B11312497 : Blo 1568982 11312497 := bstep (se 2 (by rfl) ⟨4242186, by rfl⟩ : syracuseStep 11312497 = 8484373) B8484373
theorem B7077233 : Blo 1568982 7077233 := bstep (se 2 (by rfl) ⟨2653962, by rfl⟩ : syracuseStep 7077233 = 5307925) B5307925
theorem B7945613 : Blo 1568982 7945613 := bstep (se 3 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 7945613 = 2979605) B2979605
theorem B11926925 : Blo 1568982 11926925 := bstep (se 3 (by rfl) ⟨2236298, by rfl⟩ : syracuseStep 11926925 = 4472597) B4472597
theorem B2235809 : Blo 1568982 2235809 := bstep (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) B1676857
theorem B20127203 : Blo 1568982 20127203 := bstep (se 1 (by rfl) ⟨15095402, by rfl⟩ : syracuseStep 20127203 = 30190805) B30190805
theorem B2981443 : Blo 1568982 2981443 := bstep (se 1 (by rfl) ⟨2236082, by rfl⟩ : syracuseStep 2981443 = 4472165) B4472165
theorem B2686529 : Blo 1568982 2686529 := bstep (se 2 (by rfl) ⟨1007448, by rfl⟩ : syracuseStep 2686529 = 2014897) B2014897
theorem B5963341 : Blo 1568982 5963341 := bstep (se 3 (by rfl) ⟨1118126, by rfl⟩ : syracuseStep 5963341 = 2236253) B2236253
theorem B3530321 : Blo 1568982 3530321 := bstep (se 2 (by rfl) ⟨1323870, by rfl⟩ : syracuseStep 3530321 = 2647741) B2647741
theorem B3530339 : Blo 1568982 3530339 := bstep (se 1 (by rfl) ⟨2647754, by rfl⟩ : syracuseStep 3530339 = 5295509) B5295509
theorem B3579601 : Blo 1568982 3579601 := bstep (se 2 (by rfl) ⟨1342350, by rfl⟩ : syracuseStep 3579601 = 2684701) B2684701
theorem B2981603 : Blo 1568982 2981603 := bstep (se 1 (by rfl) ⟨2236202, by rfl⟩ : syracuseStep 2981603 = 4472405) B4472405
theorem B4472621 : Blo 1568982 4472621 := bstep (se 3 (by rfl) ⟨838616, by rfl⟩ : syracuseStep 4472621 = 1677233) B1677233
theorem B5300045 : Blo 1568982 5300045 := bstep (se 3 (by rfl) ⟨993758, by rfl⟩ : syracuseStep 5300045 = 1987517) B1987517
theorem B3530609 : Blo 1568982 3530609 := bstep (se 2 (by rfl) ⟨1323978, by rfl⟩ : syracuseStep 3530609 = 2647957) B2647957
theorem B3530627 : Blo 1568982 3530627 := bstep (se 1 (by rfl) ⟨2647970, by rfl⟩ : syracuseStep 3530627 = 5295941) B5295941
theorem B5300099 : Blo 1568982 5300099 := bstep (se 1 (by rfl) ⟨3975074, by rfl⟩ : syracuseStep 5300099 = 7950149) B7950149
theorem B10059653 : Blo 1568982 10059653 := bstep (se 4 (by rfl) ⟨943092, by rfl⟩ : syracuseStep 10059653 = 1886185) B1886185
theorem B156917645 : Blo 1568982 156917645 := bstep (se 3 (by rfl) ⟨29422058, by rfl⟩ : syracuseStep 156917645 = 58844117) B58844117
theorem B3973009 : Blo 1568982 3973009 := bstep (se 2 (by rfl) ⟨1489878, by rfl⟩ : syracuseStep 3973009 = 2979757) B2979757
theorem B6709169 : Blo 1568982 6709169 := bstep (se 2 (by rfl) ⟨2515938, by rfl⟩ : syracuseStep 6709169 = 5031877) B5031877
theorem B2236339 : Blo 1568982 2236339 := bstep (se 1 (by rfl) ⟨1677254, by rfl⟩ : syracuseStep 2236339 = 3354509) B3354509
theorem B2547667 : Blo 1568982 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B3530753 : Blo 1568982 3530753 := bstep (se 2 (by rfl) ⟨1324032, by rfl⟩ : syracuseStep 3530753 = 2648065) B2648065
theorem B3973171 : Blo 1568982 3973171 := bstep (se 1 (by rfl) ⟨2979878, by rfl⟩ : syracuseStep 3973171 = 5959757) B5959757
theorem B5963827 : Blo 1568982 5963827 := bstep (se 1 (by rfl) ⟨4472870, by rfl⟩ : syracuseStep 5963827 = 8945741) B8945741
theorem B8487013 : Blo 1568982 8487013 := bstep (se 4 (by rfl) ⟨795657, by rfl⟩ : syracuseStep 8487013 = 1591315) B1591315
theorem B21479575 : Blo 1568982 21479575 := bstep (se 1 (by rfl) ⟨16109681, by rfl⟩ : syracuseStep 21479575 = 32219363) B32219363
theorem B2236567 : Blo 1568982 2236567 := bstep (se 1 (by rfl) ⟨1677425, by rfl⟩ : syracuseStep 2236567 = 3354851) B3354851
theorem B6365357 : Blo 1568982 6365357 := bstep (se 3 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 6365357 = 2387009) B2387009
theorem B29040821 : Blo 1568982 29040821 := bstep (se 5 (by rfl) ⟨1361288, by rfl⟩ : syracuseStep 29040821 = 2722577) B2722577
theorem B3973313 : Blo 1568982 3973313 := bstep (se 2 (by rfl) ⟨1489992, by rfl⟩ : syracuseStep 3973313 = 2979985) B2979985
theorem B3530969 : Blo 1568982 3530969 := bstep (se 2 (by rfl) ⟨1324113, by rfl⟩ : syracuseStep 3530969 = 2648227) B2648227
theorem B4473053 : Blo 1568982 4473053 := bstep (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) B1677395
theorem B2547979 : Blo 1568982 2547979 := bstep (se 1 (by rfl) ⟨1910984, by rfl⟩ : syracuseStep 2547979 = 3821969) B3821969
theorem B3531059 : Blo 1568982 3531059 := bstep (se 1 (by rfl) ⟨2648294, by rfl⟩ : syracuseStep 3531059 = 5296589) B5296589
theorem B5300531 : Blo 1568982 5300531 := bstep (se 1 (by rfl) ⟨3975398, by rfl⟩ : syracuseStep 5300531 = 7950797) B7950797
theorem B3531095 : Blo 1568982 3531095 := bstep (se 1 (by rfl) ⟨2648321, by rfl⟩ : syracuseStep 3531095 = 5296643) B5296643
theorem B2982233 : Blo 1568982 2982233 := bstep (se 2 (by rfl) ⟨1118337, by rfl⟩ : syracuseStep 2982233 = 2236675) B2236675
theorem B5030237 : Blo 1568982 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B4301207 : Blo 1568982 4301207 := bstep (se 1 (by rfl) ⟨3225905, by rfl⟩ : syracuseStep 4301207 = 6451811) B6451811
theorem B3350963 : Blo 1568982 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B4473281 : Blo 1568982 4473281 := bstep (se 2 (by rfl) ⟨1677480, by rfl⟩ : syracuseStep 4473281 = 3354961) B3354961
theorem B3531275 : Blo 1568982 3531275 := bstep (se 1 (by rfl) ⟨2648456, by rfl⟩ : syracuseStep 3531275 = 5296913) B5296913
theorem B64471565 : Blo 1568982 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B3531329 : Blo 1568982 3531329 := bstep (se 2 (by rfl) ⟨1324248, by rfl⟩ : syracuseStep 3531329 = 2648497) B2648497
theorem B5300801 : Blo 1568982 5300801 := bstep (se 2 (by rfl) ⟨1987800, by rfl⟩ : syracuseStep 5300801 = 3975601) B3975601
theorem B6709853 : Blo 1568982 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B8946449 : Blo 1568982 8946449 := bstep (se 2 (by rfl) ⟨3354918, by rfl⟩ : syracuseStep 8946449 = 6709837) B6709837
theorem B3531545 : Blo 1568982 3531545 := bstep (se 2 (by rfl) ⟨1324329, by rfl⟩ : syracuseStep 3531545 = 2648659) B2648659
theorem B3531635 : Blo 1568982 3531635 := bstep (se 1 (by rfl) ⟨2648726, by rfl⟩ : syracuseStep 3531635 = 5297453) B5297453
theorem B6710161 : Blo 1568982 6710161 := bstep (se 2 (by rfl) ⟨2516310, by rfl⟩ : syracuseStep 6710161 = 5032621) B5032621
theorem B3531671 : Blo 1568982 3531671 := bstep (se 1 (by rfl) ⟨2648753, by rfl⟩ : syracuseStep 3531671 = 5297507) B5297507
theorem B6710195 : Blo 1568982 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B3531851 : Blo 1568982 3531851 := bstep (se 1 (by rfl) ⟨2648888, by rfl⟩ : syracuseStep 3531851 = 5297777) B5297777
theorem B5661785 : Blo 1568982 5661785 := bstep (se 2 (by rfl) ⟨2123169, by rfl⟩ : syracuseStep 5661785 = 4246339) B4246339
theorem B5301341 : Blo 1568982 5301341 := bstep (se 3 (by rfl) ⟨994001, by rfl⟩ : syracuseStep 5301341 = 1988003) B1988003
theorem B3531905 : Blo 1568982 3531905 := bstep (se 2 (by rfl) ⟨1324464, by rfl⟩ : syracuseStep 3531905 = 2648929) B2648929
theorem B7947395 : Blo 1568982 7947395 := bstep (se 1 (by rfl) ⟨5960546, by rfl⟩ : syracuseStep 7947395 = 11921093) B11921093
theorem B3581171 : Blo 1568982 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B3532121 : Blo 1568982 3532121 := bstep (se 2 (by rfl) ⟨1324545, by rfl⟩ : syracuseStep 3532121 = 2649091) B2649091
theorem B3351937 : Blo 1568982 3351937 := bstep (se 2 (by rfl) ⟨1256976, by rfl⟩ : syracuseStep 3351937 = 2513953) B2513953
theorem B6890903 : Blo 1568982 6890903 := bstep (se 1 (by rfl) ⟨5168177, by rfl⟩ : syracuseStep 6890903 = 10336355) B10336355
theorem B3532211 : Blo 1568982 3532211 := bstep (se 1 (by rfl) ⟨2649158, by rfl⟩ : syracuseStep 3532211 = 5298317) B5298317
theorem B3974579 : Blo 1568982 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B3532247 : Blo 1568982 3532247 := bstep (se 1 (by rfl) ⟨2649185, by rfl⟩ : syracuseStep 3532247 = 5298371) B5298371
theorem B3352193 : Blo 1568982 3352193 := bstep (se 2 (by rfl) ⟨1257072, by rfl⟩ : syracuseStep 3352193 = 2514145) B2514145
theorem B3532427 : Blo 1568982 3532427 := bstep (se 1 (by rfl) ⟨2649320, by rfl⟩ : syracuseStep 3532427 = 5298641) B5298641
theorem B8939159 : Blo 1568982 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B3532481 : Blo 1568982 3532481 := bstep (se 2 (by rfl) ⟨1324680, by rfl⟩ : syracuseStep 3532481 = 2649361) B2649361
theorem B3352279 : Blo 1568982 3352279 := bstep (se 1 (by rfl) ⟨2514209, by rfl⟩ : syracuseStep 3352279 = 5028419) B5028419
theorem B15083329 : Blo 1568982 15083329 := bstep (se 2 (by rfl) ⟨5656248, by rfl⟩ : syracuseStep 15083329 = 11312497) B11312497
theorem B2647883 : Blo 1568982 2647883 := bstep (se 1 (by rfl) ⟨1985912, by rfl⟩ : syracuseStep 2647883 = 3971825) B3971825
theorem B3532697 : Blo 1568982 3532697 := bstep (se 2 (by rfl) ⟨1324761, by rfl⟩ : syracuseStep 3532697 = 2649523) B2649523
theorem B2648011 : Blo 1568982 2648011 := bstep (se 1 (by rfl) ⟨1986008, by rfl⟩ : syracuseStep 2648011 = 3972017) B3972017
theorem B3975115 : Blo 1568982 3975115 := bstep (se 1 (by rfl) ⟨2981336, by rfl⟩ : syracuseStep 3975115 = 5962673) B5962673
theorem B3532787 : Blo 1568982 3532787 := bstep (se 1 (by rfl) ⟨2649590, by rfl⟩ : syracuseStep 3532787 = 5299181) B5299181
theorem B3532823 : Blo 1568982 3532823 := bstep (se 1 (by rfl) ⟨2649617, by rfl⟩ : syracuseStep 3532823 = 5299235) B5299235
theorem B2648153 : Blo 1568982 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B3975257 : Blo 1568982 3975257 := bstep (se 2 (by rfl) ⟨1490721, by rfl⟩ : syracuseStep 3975257 = 2981443) B2981443
theorem B5957783 : Blo 1568982 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B3533003 : Blo 1568982 3533003 := bstep (se 1 (by rfl) ⟨2649752, by rfl⟩ : syracuseStep 3533003 = 5299505) B5299505
theorem B13404365 : Blo 1568982 13404365 := bstep (se 3 (by rfl) ⟨2513318, by rfl⟩ : syracuseStep 13404365 = 5026637) B5026637
theorem B2648281 : Blo 1568982 2648281 := bstep (se 2 (by rfl) ⟨993105, by rfl⟩ : syracuseStep 2648281 = 1986211) B1986211
theorem B3533057 : Blo 1568982 3533057 := bstep (se 2 (by rfl) ⟨1324896, by rfl⟩ : syracuseStep 3533057 = 2649793) B2649793
theorem B5957981 : Blo 1568982 5957981 := bstep (se 3 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 5957981 = 2234243) B2234243
theorem B2353547 : Blo 1568982 2353547 := bstep (se 1 (by rfl) ⟨1765160, by rfl⟩ : syracuseStep 2353547 = 3530321) B3530321
theorem B2353559 : Blo 1568982 2353559 := bstep (se 1 (by rfl) ⟨1765169, by rfl⟩ : syracuseStep 2353559 = 3530339) B3530339
theorem B2353625 : Blo 1568982 2353625 := bstep (se 2 (by rfl) ⟨882609, by rfl⟩ : syracuseStep 2353625 = 1765219) B1765219
theorem B3533273 : Blo 1568982 3533273 := bstep (se 2 (by rfl) ⟨1324977, by rfl⟩ : syracuseStep 3533273 = 2649955) B2649955
theorem B1886743 : Blo 1568982 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B3533363 : Blo 1568982 3533363 := bstep (se 1 (by rfl) ⟨2650022, by rfl⟩ : syracuseStep 3533363 = 5300045) B5300045
theorem B2353739 : Blo 1568982 2353739 := bstep (se 1 (by rfl) ⟨1765304, by rfl⟩ : syracuseStep 2353739 = 3530609) B3530609
theorem B2353751 : Blo 1568982 2353751 := bstep (se 1 (by rfl) ⟨1765313, by rfl⟩ : syracuseStep 2353751 = 3530627) B3530627
theorem B3533399 : Blo 1568982 3533399 := bstep (se 1 (by rfl) ⟨2650049, by rfl⟩ : syracuseStep 3533399 = 5300099) B5300099
theorem B2353817 : Blo 1568982 2353817 := bstep (se 2 (by rfl) ⟨882681, by rfl⟩ : syracuseStep 2353817 = 1765363) B1765363
theorem B3771083 : Blo 1568982 3771083 := bstep (se 1 (by rfl) ⟨2828312, by rfl⟩ : syracuseStep 3771083 = 5656625) B5656625
theorem B2353931 : Blo 1568982 2353931 := bstep (se 1 (by rfl) ⟨1765448, by rfl⟩ : syracuseStep 2353931 = 3530897) B3530897
theorem B3533579 : Blo 1568982 3533579 := bstep (se 1 (by rfl) ⟨2650184, by rfl⟩ : syracuseStep 3533579 = 5300369) B5300369
theorem B2353943 : Blo 1568982 2353943 := bstep (se 1 (by rfl) ⟨1765457, by rfl⟩ : syracuseStep 2353943 = 3530915) B3530915
theorem B2648855 : Blo 1568982 2648855 := bstep (se 1 (by rfl) ⟨1986641, by rfl⟩ : syracuseStep 2648855 = 3973283) B3973283
theorem B3533633 : Blo 1568982 3533633 := bstep (se 2 (by rfl) ⟨1325112, by rfl⟩ : syracuseStep 3533633 = 2650225) B2650225
theorem B2354009 : Blo 1568982 2354009 := bstep (se 2 (by rfl) ⟨882753, by rfl⟩ : syracuseStep 2354009 = 1765507) B1765507
theorem B7547741 : Blo 1568982 7547741 := bstep (se 3 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 7547741 = 2830403) B2830403
theorem B1592183 : Blo 1568982 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B2648983 : Blo 1568982 2648983 := bstep (se 1 (by rfl) ⟨1986737, by rfl⟩ : syracuseStep 2648983 = 3973475) B3973475
theorem B3976087 : Blo 1568982 3976087 := bstep (se 1 (by rfl) ⟨2982065, by rfl⟩ : syracuseStep 3976087 = 5964131) B5964131
theorem B6704045 : Blo 1568982 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B2354123 : Blo 1568982 2354123 := bstep (se 1 (by rfl) ⟨1765592, by rfl⟩ : syracuseStep 2354123 = 3531185) B3531185
theorem B1698775 : Blo 1568982 1698775 := bstep (se 1 (by rfl) ⟨1274081, by rfl⟩ : syracuseStep 1698775 = 2548163) B2548163
theorem B2354135 : Blo 1568982 2354135 := bstep (se 1 (by rfl) ⟨1765601, by rfl⟩ : syracuseStep 2354135 = 3531203) B3531203
theorem B2386955 : Blo 1568982 2386955 := bstep (se 1 (by rfl) ⟨1790216, by rfl⟩ : syracuseStep 2386955 = 3580433) B3580433
theorem B2354201 : Blo 1568982 2354201 := bstep (se 2 (by rfl) ⟨882825, by rfl⟩ : syracuseStep 2354201 = 1765651) B1765651
theorem B3533849 : Blo 1568982 3533849 := bstep (se 2 (by rfl) ⟨1325193, by rfl⟩ : syracuseStep 3533849 = 2650387) B2650387
theorem B32205899 : Blo 1568982 32205899 := bstep (se 1 (by rfl) ⟨24154424, by rfl⟩ : syracuseStep 32205899 = 48308849) B48308849
theorem B3533939 : Blo 1568982 3533939 := bstep (se 1 (by rfl) ⟨2650454, by rfl⟩ : syracuseStep 3533939 = 5300909) B5300909
theorem B2354315 : Blo 1568982 2354315 := bstep (se 1 (by rfl) ⟨1765736, by rfl⟩ : syracuseStep 2354315 = 3531473) B3531473
theorem B5655703 : Blo 1568982 5655703 := bstep (se 1 (by rfl) ⟨4241777, by rfl⟩ : syracuseStep 5655703 = 8483555) B8483555
theorem B2354327 : Blo 1568982 2354327 := bstep (se 1 (by rfl) ⟨1765745, by rfl⟩ : syracuseStep 2354327 = 3531491) B3531491
theorem B3533975 : Blo 1568982 3533975 := bstep (se 1 (by rfl) ⟨2650481, by rfl⟩ : syracuseStep 3533975 = 5300963) B5300963
theorem B2354393 : Blo 1568982 2354393 := bstep (se 2 (by rfl) ⟨882897, by rfl⟩ : syracuseStep 2354393 = 1765795) B1765795
theorem B8490257 : Blo 1568982 8490257 := bstep (se 2 (by rfl) ⟨3183846, by rfl⟩ : syracuseStep 8490257 = 6367693) B6367693
theorem B14511395 : Blo 1568982 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B2354507 : Blo 1568982 2354507 := bstep (se 1 (by rfl) ⟨1765880, by rfl⟩ : syracuseStep 2354507 = 3531761) B3531761
theorem B3534155 : Blo 1568982 3534155 := bstep (se 1 (by rfl) ⟨2650616, by rfl⟩ : syracuseStep 3534155 = 5301233) B5301233
theorem B3976523 : Blo 1568982 3976523 := bstep (se 1 (by rfl) ⟨2982392, by rfl⟩ : syracuseStep 3976523 = 5964785) B5964785
theorem B2354519 : Blo 1568982 2354519 := bstep (se 1 (by rfl) ⟨1765889, by rfl⟩ : syracuseStep 2354519 = 3531779) B3531779
theorem B1789291 : Blo 1568982 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B6892931 : Blo 1568982 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B3534209 : Blo 1568982 3534209 := bstep (se 2 (by rfl) ⟨1325328, by rfl⟩ : syracuseStep 3534209 = 2650657) B2650657
theorem B2354585 : Blo 1568982 2354585 := bstep (se 2 (by rfl) ⟨882969, by rfl⟩ : syracuseStep 2354585 = 1765939) B1765939
theorem B5295563 : Blo 1568982 5295563 := bstep (se 1 (by rfl) ⟨3971672, by rfl⟩ : syracuseStep 5295563 = 7943345) B7943345
theorem B1986059 : Blo 1568982 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B2354699 : Blo 1568982 2354699 := bstep (se 1 (by rfl) ⟨1766024, by rfl⟩ : syracuseStep 2354699 = 3532049) B3532049
theorem B2649611 : Blo 1568982 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B4468247 : Blo 1568982 4468247 := bstep (se 1 (by rfl) ⟨3351185, by rfl⟩ : syracuseStep 4468247 = 6702371) B6702371
theorem B2354711 : Blo 1568982 2354711 := bstep (se 1 (by rfl) ⟨1766033, by rfl⟩ : syracuseStep 2354711 = 3532067) B3532067
theorem B2354777 : Blo 1568982 2354777 := bstep (se 2 (by rfl) ⟨883041, by rfl⟩ : syracuseStep 2354777 = 1766083) B1766083
theorem B3534425 : Blo 1568982 3534425 := bstep (se 2 (by rfl) ⟨1325409, by rfl⟩ : syracuseStep 3534425 = 2650819) B2650819
theorem B11923037 : Blo 1568982 11923037 := bstep (se 3 (by rfl) ⟨2235569, by rfl⟩ : syracuseStep 11923037 = 4471139) B4471139
theorem B2649739 : Blo 1568982 2649739 := bstep (se 1 (by rfl) ⟨1987304, by rfl⟩ : syracuseStep 2649739 = 3974609) B3974609
theorem B3534515 : Blo 1568982 3534515 := bstep (se 1 (by rfl) ⟨2650886, by rfl⟩ : syracuseStep 3534515 = 5301773) B5301773
theorem B2354891 : Blo 1568982 2354891 := bstep (se 1 (by rfl) ⟨1766168, by rfl⟩ : syracuseStep 2354891 = 3532337) B3532337
theorem B11316941 : Blo 1568982 11316941 := bstep (se 3 (by rfl) ⟨2121926, by rfl⟩ : syracuseStep 11316941 = 4243853) B4243853
theorem B2354903 : Blo 1568982 2354903 := bstep (se 1 (by rfl) ⟨1766177, by rfl⟩ : syracuseStep 2354903 = 3532355) B3532355
theorem B3534551 : Blo 1568982 3534551 := bstep (se 1 (by rfl) ⟨2650913, by rfl⟩ : syracuseStep 3534551 = 5301827) B5301827
theorem B5295833 : Blo 1568982 5295833 := bstep (se 2 (by rfl) ⟨1985937, by rfl⟩ : syracuseStep 5295833 = 3971875) B3971875
theorem B1765111 : Blo 1568982 1765111 := bstep (se 1 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 1765111 = 2647667) B2647667
theorem B5099287 : Blo 1568982 5099287 := bstep (se 1 (by rfl) ⟨3824465, by rfl⟩ : syracuseStep 5099287 = 7648931) B7648931
theorem B2354969 : Blo 1568982 2354969 := bstep (se 2 (by rfl) ⟨883113, by rfl⟩ : syracuseStep 2354969 = 1766227) B1766227
theorem B2649881 : Blo 1568982 2649881 := bstep (se 2 (by rfl) ⟨993705, by rfl⟩ : syracuseStep 2649881 = 1987411) B1987411
theorem B33967937 : Blo 1568982 33967937 := bstep (se 2 (by rfl) ⟨12737976, by rfl⟩ : syracuseStep 33967937 = 25475953) B25475953
theorem B22646627 : Blo 1568982 22646627 := bstep (se 1 (by rfl) ⟨16984970, by rfl⟩ : syracuseStep 22646627 = 33969941) B33969941
theorem B2355083 : Blo 1568982 2355083 := bstep (se 1 (by rfl) ⟨1766312, by rfl⟩ : syracuseStep 2355083 = 3532625) B3532625
theorem B2355095 : Blo 1568982 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B2650009 : Blo 1568982 2650009 := bstep (se 2 (by rfl) ⟨993753, by rfl⟩ : syracuseStep 2650009 = 1987507) B1987507
theorem B1765291 : Blo 1568982 1765291 := bstep (se 1 (by rfl) ⟨1323968, by rfl⟩ : syracuseStep 1765291 = 2647937) B2647937
theorem B2355161 : Blo 1568982 2355161 := bstep (se 2 (by rfl) ⟨883185, by rfl⟩ : syracuseStep 2355161 = 1766371) B1766371
theorem B1765399 : Blo 1568982 1765399 := bstep (se 1 (by rfl) ⟨1324049, by rfl⟩ : syracuseStep 1765399 = 2648099) B2648099
theorem B6041623 : Blo 1568982 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B2355275 : Blo 1568982 2355275 := bstep (se 1 (by rfl) ⟨1766456, by rfl⟩ : syracuseStep 2355275 = 3532913) B3532913
theorem B2355287 : Blo 1568982 2355287 := bstep (se 1 (by rfl) ⟨1766465, by rfl⟩ : syracuseStep 2355287 = 3532931) B3532931
theorem B3182743 : Blo 1568982 3182743 := bstep (se 1 (by rfl) ⟨2387057, by rfl⟩ : syracuseStep 3182743 = 4774115) B4774115
theorem B2355353 : Blo 1568982 2355353 := bstep (se 2 (by rfl) ⟨883257, by rfl⟩ : syracuseStep 2355353 = 1766515) B1766515
theorem B1765579 : Blo 1568982 1765579 := bstep (se 1 (by rfl) ⟨1324184, by rfl⟩ : syracuseStep 1765579 = 2648369) B2648369
theorem B1986763 : Blo 1568982 1986763 := bstep (se 1 (by rfl) ⟨1490072, by rfl⟩ : syracuseStep 1986763 = 2980145) B2980145
theorem B1568983 : Blo 1568982 1568983 := bstep (se 1 (by rfl) ⟨1176737, by rfl⟩ : syracuseStep 1568983 = 2353475) B2353475
theorem B3182809 : Blo 1568982 3182809 := bstep (se 2 (by rfl) ⟨1193553, by rfl⟩ : syracuseStep 3182809 = 2387107) B2387107
theorem B1569003 : Blo 1568982 1569003 := bstep (se 1 (by rfl) ⟨1176752, by rfl⟩ : syracuseStep 1569003 = 2353505) B2353505
theorem B1569015 : Blo 1568982 1569015 := bstep (se 1 (by rfl) ⟨1176761, by rfl⟩ : syracuseStep 1569015 = 2353523) B2353523
theorem B5959939 : Blo 1568982 5959939 := bstep (se 1 (by rfl) ⟨4469954, by rfl⟩ : syracuseStep 5959939 = 8939909) B8939909
theorem B1569035 : Blo 1568982 1569035 := bstep (se 1 (by rfl) ⟨1176776, by rfl⟩ : syracuseStep 1569035 = 2353553) B2353553
theorem B2355467 : Blo 1568982 2355467 := bstep (se 1 (by rfl) ⟨1766600, by rfl⟩ : syracuseStep 2355467 = 3533201) B3533201
theorem B1569047 : Blo 1568982 1569047 := bstep (se 1 (by rfl) ⟨1176785, by rfl⟩ : syracuseStep 1569047 = 2353571) B2353571
theorem B2355479 : Blo 1568982 2355479 := bstep (se 1 (by rfl) ⟨1766609, by rfl⟩ : syracuseStep 2355479 = 3533219) B3533219
theorem B1569067 : Blo 1568982 1569067 := bstep (se 1 (by rfl) ⟨1176800, by rfl⟩ : syracuseStep 1569067 = 2353601) B2353601
theorem B1569079 : Blo 1568982 1569079 := bstep (se 1 (by rfl) ⟨1176809, by rfl⟩ : syracuseStep 1569079 = 2353619) B2353619
theorem B1765687 : Blo 1568982 1765687 := bstep (se 1 (by rfl) ⟨1324265, by rfl⟩ : syracuseStep 1765687 = 2648531) B2648531
theorem B1569099 : Blo 1568982 1569099 := bstep (se 1 (by rfl) ⟨1176824, by rfl⟩ : syracuseStep 1569099 = 2353649) B2353649
theorem B4772171 : Blo 1568982 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B1569111 : Blo 1568982 1569111 := bstep (se 1 (by rfl) ⟨1176833, by rfl⟩ : syracuseStep 1569111 = 2353667) B2353667
theorem B2355545 : Blo 1568982 2355545 := bstep (se 2 (by rfl) ⟨883329, by rfl⟩ : syracuseStep 2355545 = 1766659) B1766659
theorem B1569131 : Blo 1568982 1569131 := bstep (se 1 (by rfl) ⟨1176848, by rfl⟩ : syracuseStep 1569131 = 2353697) B2353697
theorem B3354995 : Blo 1568982 3354995 := bstep (se 1 (by rfl) ⟨2516246, by rfl⟩ : syracuseStep 3354995 = 5032493) B5032493
theorem B1569143 : Blo 1568982 1569143 := bstep (se 1 (by rfl) ⟨1176857, by rfl⟩ : syracuseStep 1569143 = 2353715) B2353715
theorem B1569163 : Blo 1568982 1569163 := bstep (se 1 (by rfl) ⟨1176872, by rfl⟩ : syracuseStep 1569163 = 2353745) B2353745
theorem B1569175 : Blo 1568982 1569175 := bstep (se 1 (by rfl) ⟨1176881, by rfl⟩ : syracuseStep 1569175 = 2353763) B2353763
theorem B5296535 : Blo 1568982 5296535 := bstep (se 1 (by rfl) ⟨3972401, by rfl⟩ : syracuseStep 5296535 = 7944803) B7944803
theorem B1569195 : Blo 1568982 1569195 := bstep (se 1 (by rfl) ⟨1176896, by rfl⟩ : syracuseStep 1569195 = 2353793) B2353793
theorem B1569207 : Blo 1568982 1569207 := bstep (se 1 (by rfl) ⟨1176905, by rfl⟩ : syracuseStep 1569207 = 2353811) B2353811
theorem B1569227 : Blo 1568982 1569227 := bstep (se 1 (by rfl) ⟨1176920, by rfl⟩ : syracuseStep 1569227 = 2353841) B2353841
theorem B6042059 : Blo 1568982 6042059 := bstep (se 1 (by rfl) ⟨4531544, by rfl⟩ : syracuseStep 6042059 = 9063089) B9063089
theorem B2355659 : Blo 1568982 2355659 := bstep (se 1 (by rfl) ⟨1766744, by rfl⟩ : syracuseStep 2355659 = 3533489) B3533489
theorem B1569239 : Blo 1568982 1569239 := bstep (se 1 (by rfl) ⟨1176929, by rfl⟩ : syracuseStep 1569239 = 2353859) B2353859
theorem B1987031 : Blo 1568982 1987031 := bstep (se 1 (by rfl) ⟨1490273, by rfl⟩ : syracuseStep 1987031 = 2980547) B2980547
theorem B2355671 : Blo 1568982 2355671 := bstep (se 1 (by rfl) ⟨1766753, by rfl⟩ : syracuseStep 2355671 = 3533507) B3533507
theorem B18133465 : Blo 1568982 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B2650583 : Blo 1568982 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B1569259 : Blo 1568982 1569259 := bstep (se 1 (by rfl) ⟨1176944, by rfl⟩ : syracuseStep 1569259 = 2353889) B2353889
theorem B1765867 : Blo 1568982 1765867 := bstep (se 1 (by rfl) ⟨1324400, by rfl⟩ : syracuseStep 1765867 = 2648801) B2648801
theorem B1569271 : Blo 1568982 1569271 := bstep (se 1 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 1569271 = 2353907) B2353907
theorem B1569291 : Blo 1568982 1569291 := bstep (se 1 (by rfl) ⟨1176968, by rfl⟩ : syracuseStep 1569291 = 2353937) B2353937
theorem B1569303 : Blo 1568982 1569303 := bstep (se 1 (by rfl) ⟨1176977, by rfl⟩ : syracuseStep 1569303 = 2353955) B2353955
theorem B2355737 : Blo 1568982 2355737 := bstep (se 2 (by rfl) ⟨883401, by rfl⟩ : syracuseStep 2355737 = 1766803) B1766803
theorem B1675819 : Blo 1568982 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B1569323 : Blo 1568982 1569323 := bstep (se 1 (by rfl) ⟨1176992, by rfl⟩ : syracuseStep 1569323 = 2353985) B2353985
theorem B5960243 : Blo 1568982 5960243 := bstep (se 1 (by rfl) ⟨4470182, by rfl⟩ : syracuseStep 5960243 = 8940365) B8940365
theorem B1569335 : Blo 1568982 1569335 := bstep (se 1 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 1569335 = 2354003) B2354003
theorem B1569355 : Blo 1568982 1569355 := bstep (se 1 (by rfl) ⟨1177016, by rfl⟩ : syracuseStep 1569355 = 2354033) B2354033
theorem B1569367 : Blo 1568982 1569367 := bstep (se 1 (by rfl) ⟨1177025, by rfl⟩ : syracuseStep 1569367 = 2354051) B2354051
theorem B1765975 : Blo 1568982 1765975 := bstep (se 1 (by rfl) ⟨1324481, by rfl⟩ : syracuseStep 1765975 = 2648963) B2648963
theorem B2650711 : Blo 1568982 2650711 := bstep (se 1 (by rfl) ⟨1988033, by rfl⟩ : syracuseStep 2650711 = 3976067) B3976067
theorem B1569387 : Blo 1568982 1569387 := bstep (se 1 (by rfl) ⟨1177040, by rfl⟩ : syracuseStep 1569387 = 2354081) B2354081
theorem B1569399 : Blo 1568982 1569399 := bstep (se 1 (by rfl) ⟨1177049, by rfl⟩ : syracuseStep 1569399 = 2354099) B2354099
theorem B1569419 : Blo 1568982 1569419 := bstep (se 1 (by rfl) ⟨1177064, by rfl⟩ : syracuseStep 1569419 = 2354129) B2354129
theorem B2355851 : Blo 1568982 2355851 := bstep (se 1 (by rfl) ⟨1766888, by rfl⟩ : syracuseStep 2355851 = 3533777) B3533777
theorem B1569431 : Blo 1568982 1569431 := bstep (se 1 (by rfl) ⟨1177073, by rfl⟩ : syracuseStep 1569431 = 2354147) B2354147
theorem B2355863 : Blo 1568982 2355863 := bstep (se 1 (by rfl) ⟨1766897, by rfl⟩ : syracuseStep 2355863 = 3533795) B3533795
theorem B1569451 : Blo 1568982 1569451 := bstep (se 1 (by rfl) ⟨1177088, by rfl⟩ : syracuseStep 1569451 = 2354177) B2354177
theorem B1569463 : Blo 1568982 1569463 := bstep (se 1 (by rfl) ⟨1177097, by rfl⟩ : syracuseStep 1569463 = 2354195) B2354195
theorem B1569483 : Blo 1568982 1569483 := bstep (se 1 (by rfl) ⟨1177112, by rfl⟩ : syracuseStep 1569483 = 2354225) B2354225
theorem B1569495 : Blo 1568982 1569495 := bstep (se 1 (by rfl) ⟨1177121, by rfl⟩ : syracuseStep 1569495 = 2354243) B2354243
theorem B2355929 : Blo 1568982 2355929 := bstep (se 2 (by rfl) ⟨883473, by rfl⟩ : syracuseStep 2355929 = 1766947) B1766947
theorem B1569515 : Blo 1568982 1569515 := bstep (se 1 (by rfl) ⟨1177136, by rfl⟩ : syracuseStep 1569515 = 2354273) B2354273
theorem B1569527 : Blo 1568982 1569527 := bstep (se 1 (by rfl) ⟨1177145, by rfl⟩ : syracuseStep 1569527 = 2354291) B2354291
theorem B1569547 : Blo 1568982 1569547 := bstep (se 1 (by rfl) ⟨1177160, by rfl⟩ : syracuseStep 1569547 = 2354321) B2354321
theorem B1766155 : Blo 1568982 1766155 := bstep (se 1 (by rfl) ⟨1324616, by rfl⟩ : syracuseStep 1766155 = 2649233) B2649233
theorem B7951121 : Blo 1568982 7951121 := bstep (se 2 (by rfl) ⟨2981670, by rfl⟩ : syracuseStep 7951121 = 5963341) B5963341
theorem B1569559 : Blo 1568982 1569559 := bstep (se 1 (by rfl) ⟨1177169, by rfl⟩ : syracuseStep 1569559 = 2354339) B2354339
theorem B1569579 : Blo 1568982 1569579 := bstep (se 1 (by rfl) ⟨1177184, by rfl⟩ : syracuseStep 1569579 = 2354369) B2354369
theorem B1569591 : Blo 1568982 1569591 := bstep (se 1 (by rfl) ⟨1177193, by rfl⟩ : syracuseStep 1569591 = 2354387) B2354387
theorem B1569611 : Blo 1568982 1569611 := bstep (se 1 (by rfl) ⟨1177208, by rfl⟩ : syracuseStep 1569611 = 2354417) B2354417
theorem B2356043 : Blo 1568982 2356043 := bstep (se 1 (by rfl) ⟨1767032, by rfl⟩ : syracuseStep 2356043 = 3534065) B3534065
theorem B1569623 : Blo 1568982 1569623 := bstep (se 1 (by rfl) ⟨1177217, by rfl⟩ : syracuseStep 1569623 = 2354435) B2354435
theorem B2356055 : Blo 1568982 2356055 := bstep (se 1 (by rfl) ⟨1767041, by rfl⟩ : syracuseStep 2356055 = 3534083) B3534083
theorem B1569643 : Blo 1568982 1569643 := bstep (se 1 (by rfl) ⟨1177232, by rfl⟩ : syracuseStep 1569643 = 2354465) B2354465
theorem B25826165 : Blo 1568982 25826165 := bstep (se 5 (by rfl) ⟨1210601, by rfl⟩ : syracuseStep 25826165 = 2421203) B2421203
theorem B1569655 : Blo 1568982 1569655 := bstep (se 1 (by rfl) ⟨1177241, by rfl⟩ : syracuseStep 1569655 = 2354483) B2354483
theorem B1766263 : Blo 1568982 1766263 := bstep (se 1 (by rfl) ⟨1324697, by rfl⟩ : syracuseStep 1766263 = 2649395) B2649395
theorem B1569675 : Blo 1568982 1569675 := bstep (se 1 (by rfl) ⟨1177256, by rfl⟩ : syracuseStep 1569675 = 2354513) B2354513
theorem B1569687 : Blo 1568982 1569687 := bstep (se 1 (by rfl) ⟨1177265, by rfl⟩ : syracuseStep 1569687 = 2354531) B2354531
theorem B2356121 : Blo 1568982 2356121 := bstep (se 2 (by rfl) ⟨883545, by rfl⟩ : syracuseStep 2356121 = 1767091) B1767091
theorem B1569707 : Blo 1568982 1569707 := bstep (se 1 (by rfl) ⟨1177280, by rfl⟩ : syracuseStep 1569707 = 2354561) B2354561
theorem B5297075 : Blo 1568982 5297075 := bstep (se 1 (by rfl) ⟨3972806, by rfl⟩ : syracuseStep 5297075 = 7945613) B7945613
theorem B6042547 : Blo 1568982 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B1569719 : Blo 1568982 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B7951283 : Blo 1568982 7951283 := bstep (se 1 (by rfl) ⟨5963462, by rfl⟩ : syracuseStep 7951283 = 11926925) B11926925
theorem B4772801 : Blo 1568982 4772801 := bstep (se 2 (by rfl) ⟨1789800, by rfl⟩ : syracuseStep 4772801 = 3579601) B3579601
theorem B1569739 : Blo 1568982 1569739 := bstep (se 1 (by rfl) ⟨1177304, by rfl⟩ : syracuseStep 1569739 = 2354609) B2354609
theorem B1569751 : Blo 1568982 1569751 := bstep (se 1 (by rfl) ⟨1177313, by rfl⟩ : syracuseStep 1569751 = 2354627) B2354627
theorem B1569771 : Blo 1568982 1569771 := bstep (se 1 (by rfl) ⟨1177328, by rfl⟩ : syracuseStep 1569771 = 2354657) B2354657
theorem B1569783 : Blo 1568982 1569783 := bstep (se 1 (by rfl) ⟨1177337, by rfl⟩ : syracuseStep 1569783 = 2354675) B2354675
theorem B1569803 : Blo 1568982 1569803 := bstep (se 1 (by rfl) ⟨1177352, by rfl⟩ : syracuseStep 1569803 = 2354705) B2354705
theorem B2356235 : Blo 1568982 2356235 := bstep (se 1 (by rfl) ⟨1767176, by rfl⟩ : syracuseStep 2356235 = 3534353) B3534353
theorem B26825741 : Blo 1568982 26825741 := bstep (se 3 (by rfl) ⟨5029826, by rfl⟩ : syracuseStep 26825741 = 10059653) B10059653
theorem B1569815 : Blo 1568982 1569815 := bstep (se 1 (by rfl) ⟨1177361, by rfl⟩ : syracuseStep 1569815 = 2354723) B2354723
theorem B2356247 : Blo 1568982 2356247 := bstep (se 1 (by rfl) ⟨1767185, by rfl⟩ : syracuseStep 2356247 = 3534371) B3534371
theorem B1569835 : Blo 1568982 1569835 := bstep (se 1 (by rfl) ⟨1177376, by rfl⟩ : syracuseStep 1569835 = 2354753) B2354753
theorem B1766443 : Blo 1568982 1766443 := bstep (se 1 (by rfl) ⟨1324832, by rfl⟩ : syracuseStep 1766443 = 2649665) B2649665
theorem B1791019 : Blo 1568982 1791019 := bstep (se 1 (by rfl) ⟨1343264, by rfl⟩ : syracuseStep 1791019 = 2686529) B2686529
theorem B1569847 : Blo 1568982 1569847 := bstep (se 1 (by rfl) ⟨1177385, by rfl⟩ : syracuseStep 1569847 = 2354771) B2354771
theorem B1569867 : Blo 1568982 1569867 := bstep (se 1 (by rfl) ⟨1177400, by rfl⟩ : syracuseStep 1569867 = 2354801) B2354801
theorem B1569879 : Blo 1568982 1569879 := bstep (se 1 (by rfl) ⟨1177409, by rfl⟩ : syracuseStep 1569879 = 2354819) B2354819
theorem B2356313 : Blo 1568982 2356313 := bstep (se 2 (by rfl) ⟨883617, by rfl⟩ : syracuseStep 2356313 = 1767235) B1767235
theorem B1569899 : Blo 1568982 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B1569911 : Blo 1568982 1569911 := bstep (se 1 (by rfl) ⟨1177433, by rfl⟩ : syracuseStep 1569911 = 2354867) B2354867
theorem B1569931 : Blo 1568982 1569931 := bstep (se 1 (by rfl) ⟨1177448, by rfl⟩ : syracuseStep 1569931 = 2354897) B2354897
theorem B1569943 : Blo 1568982 1569943 := bstep (se 1 (by rfl) ⟨1177457, by rfl⟩ : syracuseStep 1569943 = 2354915) B2354915
theorem B1766551 : Blo 1568982 1766551 := bstep (se 1 (by rfl) ⟨1324913, by rfl⟩ : syracuseStep 1766551 = 2649827) B2649827
theorem B1987735 : Blo 1568982 1987735 := bstep (se 1 (by rfl) ⟨1490801, by rfl⟩ : syracuseStep 1987735 = 2981603) B2981603
theorem B1569963 : Blo 1568982 1569963 := bstep (se 1 (by rfl) ⟨1177472, by rfl⟩ : syracuseStep 1569963 = 2354945) B2354945
theorem B50910389 : Blo 1568982 50910389 := bstep (se 5 (by rfl) ⟨2386424, by rfl⟩ : syracuseStep 50910389 = 4772849) B4772849
theorem B1569975 : Blo 1568982 1569975 := bstep (se 1 (by rfl) ⟨1177481, by rfl⟩ : syracuseStep 1569975 = 2354963) B2354963
theorem B5297345 : Blo 1568982 5297345 := bstep (se 2 (by rfl) ⟨1986504, by rfl⟩ : syracuseStep 5297345 = 3973009) B3973009
theorem B5960897 : Blo 1568982 5960897 := bstep (se 2 (by rfl) ⟨2235336, by rfl⟩ : syracuseStep 5960897 = 4470673) B4470673
theorem B1569995 : Blo 1568982 1569995 := bstep (se 1 (by rfl) ⟨1177496, by rfl⟩ : syracuseStep 1569995 = 2354993) B2354993
theorem B2356427 : Blo 1568982 2356427 := bstep (se 1 (by rfl) ⟨1767320, by rfl⟩ : syracuseStep 2356427 = 3534641) B3534641
theorem B1570007 : Blo 1568982 1570007 := bstep (se 1 (by rfl) ⟨1177505, by rfl⟩ : syracuseStep 1570007 = 2355011) B2355011
theorem B2356439 : Blo 1568982 2356439 := bstep (se 1 (by rfl) ⟨1767329, by rfl⟩ : syracuseStep 2356439 = 3534659) B3534659
theorem B1570027 : Blo 1568982 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B1570039 : Blo 1568982 1570039 := bstep (se 1 (by rfl) ⟨1177529, by rfl⟩ : syracuseStep 1570039 = 2355059) B2355059
theorem B1570059 : Blo 1568982 1570059 := bstep (se 1 (by rfl) ⟨1177544, by rfl⟩ : syracuseStep 1570059 = 2355089) B2355089
theorem B1570071 : Blo 1568982 1570071 := bstep (se 1 (by rfl) ⟨1177553, by rfl⟩ : syracuseStep 1570071 = 2355107) B2355107
theorem B3396889 : Blo 1568982 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B1570091 : Blo 1568982 1570091 := bstep (se 1 (by rfl) ⟨1177568, by rfl⟩ : syracuseStep 1570091 = 2355137) B2355137
theorem B1570103 : Blo 1568982 1570103 := bstep (se 1 (by rfl) ⟨1177577, by rfl⟩ : syracuseStep 1570103 = 2355155) B2355155
theorem B1570123 : Blo 1568982 1570123 := bstep (se 1 (by rfl) ⟨1177592, by rfl⟩ : syracuseStep 1570123 = 2355185) B2355185
theorem B1766731 : Blo 1568982 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1570135 : Blo 1568982 1570135 := bstep (se 1 (by rfl) ⟨1177601, by rfl⟩ : syracuseStep 1570135 = 2355203) B2355203
theorem B20108645 : Blo 1568982 20108645 := bstep (se 4 (by rfl) ⟨1885185, by rfl⟩ : syracuseStep 20108645 = 3770371) B3770371
theorem B1570155 : Blo 1568982 1570155 := bstep (se 1 (by rfl) ⟨1177616, by rfl⟩ : syracuseStep 1570155 = 2355233) B2355233
theorem B1570167 : Blo 1568982 1570167 := bstep (se 1 (by rfl) ⟨1177625, by rfl⟩ : syracuseStep 1570167 = 2355251) B2355251
theorem B1570187 : Blo 1568982 1570187 := bstep (se 1 (by rfl) ⟨1177640, by rfl⟩ : syracuseStep 1570187 = 2355281) B2355281
theorem B1570199 : Blo 1568982 1570199 := bstep (se 1 (by rfl) ⟨1177649, by rfl⟩ : syracuseStep 1570199 = 2355299) B2355299
theorem B1570219 : Blo 1568982 1570219 := bstep (se 1 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 1570219 = 2355329) B2355329
theorem B1570231 : Blo 1568982 1570231 := bstep (se 1 (by rfl) ⟨1177673, by rfl⟩ : syracuseStep 1570231 = 2355347) B2355347
theorem B1766839 : Blo 1568982 1766839 := bstep (se 1 (by rfl) ⟨1325129, by rfl⟩ : syracuseStep 1766839 = 2650259) B2650259
theorem B4838849 : Blo 1568982 4838849 := bstep (se 2 (by rfl) ⟨1814568, by rfl⟩ : syracuseStep 4838849 = 3629137) B3629137
theorem B1570251 : Blo 1568982 1570251 := bstep (se 1 (by rfl) ⟨1177688, by rfl⟩ : syracuseStep 1570251 = 2355377) B2355377
theorem B1570263 : Blo 1568982 1570263 := bstep (se 1 (by rfl) ⟨1177697, by rfl⟩ : syracuseStep 1570263 = 2355395) B2355395
theorem B1570283 : Blo 1568982 1570283 := bstep (se 1 (by rfl) ⟨1177712, by rfl⟩ : syracuseStep 1570283 = 2355425) B2355425
theorem B1570295 : Blo 1568982 1570295 := bstep (se 1 (by rfl) ⟨1177721, by rfl⟩ : syracuseStep 1570295 = 2355443) B2355443
theorem B1570315 : Blo 1568982 1570315 := bstep (se 1 (by rfl) ⟨1177736, by rfl⟩ : syracuseStep 1570315 = 2355473) B2355473
theorem B1570327 : Blo 1568982 1570327 := bstep (se 1 (by rfl) ⟨1177745, by rfl⟩ : syracuseStep 1570327 = 2355491) B2355491
theorem B1570347 : Blo 1568982 1570347 := bstep (se 1 (by rfl) ⟨1177760, by rfl⟩ : syracuseStep 1570347 = 2355521) B2355521
theorem B1570359 : Blo 1568982 1570359 := bstep (se 1 (by rfl) ⟨1177769, by rfl⟩ : syracuseStep 1570359 = 2355539) B2355539
theorem B1570379 : Blo 1568982 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1570391 : Blo 1568982 1570391 := bstep (se 1 (by rfl) ⟨1177793, by rfl⟩ : syracuseStep 1570391 = 2355587) B2355587
theorem B4470365 : Blo 1568982 4470365 := bstep (se 3 (by rfl) ⟨838193, by rfl⟩ : syracuseStep 4470365 = 1676387) B1676387
theorem B1570411 : Blo 1568982 1570411 := bstep (se 1 (by rfl) ⟨1177808, by rfl⟩ : syracuseStep 1570411 = 2355617) B2355617
theorem B1767019 : Blo 1568982 1767019 := bstep (se 1 (by rfl) ⟨1325264, by rfl⟩ : syracuseStep 1767019 = 2650529) B2650529
theorem B1570423 : Blo 1568982 1570423 := bstep (se 1 (by rfl) ⟨1177817, by rfl⟩ : syracuseStep 1570423 = 2355635) B2355635
theorem B1570443 : Blo 1568982 1570443 := bstep (se 1 (by rfl) ⟨1177832, by rfl⟩ : syracuseStep 1570443 = 2355665) B2355665
theorem B7943831 : Blo 1568982 7943831 := bstep (se 1 (by rfl) ⟨5957873, by rfl⟩ : syracuseStep 7943831 = 11915747) B11915747
theorem B1570455 : Blo 1568982 1570455 := bstep (se 1 (by rfl) ⟨1177841, by rfl⟩ : syracuseStep 1570455 = 2355683) B2355683
theorem B1570475 : Blo 1568982 1570475 := bstep (se 1 (by rfl) ⟨1177856, by rfl⟩ : syracuseStep 1570475 = 2355713) B2355713
theorem B1570487 : Blo 1568982 1570487 := bstep (se 1 (by rfl) ⟨1177865, by rfl⟩ : syracuseStep 1570487 = 2355731) B2355731
theorem B5027521 : Blo 1568982 5027521 := bstep (se 2 (by rfl) ⟨1885320, by rfl⟩ : syracuseStep 5027521 = 3770641) B3770641
theorem B1570507 : Blo 1568982 1570507 := bstep (se 1 (by rfl) ⟨1177880, by rfl⟩ : syracuseStep 1570507 = 2355761) B2355761
theorem B1570519 : Blo 1568982 1570519 := bstep (se 1 (by rfl) ⟨1177889, by rfl⟩ : syracuseStep 1570519 = 2355779) B2355779
theorem B1767127 : Blo 1568982 1767127 := bstep (se 1 (by rfl) ⟨1325345, by rfl⟩ : syracuseStep 1767127 = 2650691) B2650691
theorem B5297885 : Blo 1568982 5297885 := bstep (se 3 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 5297885 = 1986707) B1986707
theorem B1570539 : Blo 1568982 1570539 := bstep (se 1 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 1570539 = 2355809) B2355809
theorem B1570551 : Blo 1568982 1570551 := bstep (se 1 (by rfl) ⟨1177913, by rfl⟩ : syracuseStep 1570551 = 2355827) B2355827
theorem B1570571 : Blo 1568982 1570571 := bstep (se 1 (by rfl) ⟨1177928, by rfl⟩ : syracuseStep 1570571 = 2355857) B2355857
theorem B1570583 : Blo 1568982 1570583 := bstep (se 1 (by rfl) ⟨1177937, by rfl⟩ : syracuseStep 1570583 = 2355875) B2355875
theorem B1570603 : Blo 1568982 1570603 := bstep (se 1 (by rfl) ⟨1177952, by rfl⟩ : syracuseStep 1570603 = 2355905) B2355905
theorem B1570615 : Blo 1568982 1570615 := bstep (se 1 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 1570615 = 2355923) B2355923
theorem B17200961 : Blo 1568982 17200961 := bstep (se 2 (by rfl) ⟨6450360, by rfl⟩ : syracuseStep 17200961 = 12900721) B12900721
theorem B2979659 : Blo 1568982 2979659 := bstep (se 1 (by rfl) ⟨2234744, by rfl⟩ : syracuseStep 2979659 = 4469489) B4469489
theorem B5658443 : Blo 1568982 5658443 := bstep (se 1 (by rfl) ⟨4243832, by rfl⟩ : syracuseStep 5658443 = 8487665) B8487665
theorem B1570635 : Blo 1568982 1570635 := bstep (se 1 (by rfl) ⟨1177976, by rfl⟩ : syracuseStep 1570635 = 2355953) B2355953
theorem B1570647 : Blo 1568982 1570647 := bstep (se 1 (by rfl) ⟨1177985, by rfl⟩ : syracuseStep 1570647 = 2355971) B2355971
theorem B1570667 : Blo 1568982 1570667 := bstep (se 1 (by rfl) ⟨1178000, by rfl⟩ : syracuseStep 1570667 = 2356001) B2356001
theorem B1570679 : Blo 1568982 1570679 := bstep (se 1 (by rfl) ⟨1178009, by rfl⟩ : syracuseStep 1570679 = 2356019) B2356019
theorem B10057603 : Blo 1568982 10057603 := bstep (se 1 (by rfl) ⟨7543202, by rfl⟩ : syracuseStep 10057603 = 15086405) B15086405
theorem B1570699 : Blo 1568982 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B1767307 : Blo 1568982 1767307 := bstep (se 1 (by rfl) ⟨1325480, by rfl⟩ : syracuseStep 1767307 = 2650961) B2650961
theorem B1570711 : Blo 1568982 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B1570731 : Blo 1568982 1570731 := bstep (se 1 (by rfl) ⟨1178048, by rfl⟩ : syracuseStep 1570731 = 2356097) B2356097
theorem B4470707 : Blo 1568982 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B1570743 : Blo 1568982 1570743 := bstep (se 1 (by rfl) ⟨1178057, by rfl⟩ : syracuseStep 1570743 = 2356115) B2356115
theorem B1570763 : Blo 1568982 1570763 := bstep (se 1 (by rfl) ⟨1178072, by rfl⟩ : syracuseStep 1570763 = 2356145) B2356145
theorem B1570775 : Blo 1568982 1570775 := bstep (se 1 (by rfl) ⟨1178081, by rfl⟩ : syracuseStep 1570775 = 2356163) B2356163
theorem B1570795 : Blo 1568982 1570795 := bstep (se 1 (by rfl) ⟨1178096, by rfl⟩ : syracuseStep 1570795 = 2356193) B2356193
theorem B1570807 : Blo 1568982 1570807 := bstep (se 1 (by rfl) ⟨1178105, by rfl⟩ : syracuseStep 1570807 = 2356211) B2356211
theorem B2979841 : Blo 1568982 2979841 := bstep (se 2 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 2979841 = 2234881) B2234881
theorem B1570827 : Blo 1568982 1570827 := bstep (se 1 (by rfl) ⟨1178120, by rfl⟩ : syracuseStep 1570827 = 2356241) B2356241
theorem B1570839 : Blo 1568982 1570839 := bstep (se 1 (by rfl) ⟨1178129, by rfl⟩ : syracuseStep 1570839 = 2356259) B2356259
theorem B1570859 : Blo 1568982 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B1570871 : Blo 1568982 1570871 := bstep (se 1 (by rfl) ⟨1178153, by rfl⟩ : syracuseStep 1570871 = 2356307) B2356307
theorem B1570891 : Blo 1568982 1570891 := bstep (se 1 (by rfl) ⟨1178168, by rfl⟩ : syracuseStep 1570891 = 2356337) B2356337
theorem B1570903 : Blo 1568982 1570903 := bstep (se 1 (by rfl) ⟨1178177, by rfl⟩ : syracuseStep 1570903 = 2356355) B2356355
theorem B1570923 : Blo 1568982 1570923 := bstep (se 1 (by rfl) ⟨1178192, by rfl⟩ : syracuseStep 1570923 = 2356385) B2356385
theorem B1570935 : Blo 1568982 1570935 := bstep (se 1 (by rfl) ⟨1178201, by rfl⟩ : syracuseStep 1570935 = 2356403) B2356403
theorem B1570955 : Blo 1568982 1570955 := bstep (se 1 (by rfl) ⟨1178216, by rfl⟩ : syracuseStep 1570955 = 2356433) B2356433
theorem B1570967 : Blo 1568982 1570967 := bstep (se 1 (by rfl) ⟨1178225, by rfl⟩ : syracuseStep 1570967 = 2356451) B2356451
theorem B5658817 : Blo 1568982 5658817 := bstep (se 2 (by rfl) ⟨2122056, by rfl⟩ : syracuseStep 5658817 = 4244113) B4244113
theorem B6707393 : Blo 1568982 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B7157963 : Blo 1568982 7157963 := bstep (se 1 (by rfl) ⟨5368472, by rfl⟩ : syracuseStep 7157963 = 10736945) B10736945
theorem B5372183 : Blo 1568982 5372183 := bstep (se 1 (by rfl) ⟨4029137, by rfl⟩ : syracuseStep 5372183 = 8058275) B8058275
theorem B18872621 : Blo 1568982 18872621 := bstep (se 3 (by rfl) ⟨3538616, by rfl⟩ : syracuseStep 18872621 = 7077233) B7077233
theorem B5658931 : Blo 1568982 5658931 := bstep (se 1 (by rfl) ⟨4244198, by rfl⟩ : syracuseStep 5658931 = 8488397) B8488397
theorem B8943965 : Blo 1568982 8943965 := bstep (se 3 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 8943965 = 3353987) B3353987
theorem B5962157 : Blo 1568982 5962157 := bstep (se 3 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 5962157 = 2235809) B2235809
theorem B2980289 : Blo 1568982 2980289 := bstep (se 2 (by rfl) ⟨1117608, by rfl⟩ : syracuseStep 2980289 = 2235217) B2235217
theorem B3971531 : Blo 1568982 3971531 := bstep (se 1 (by rfl) ⟨2978648, by rfl⟩ : syracuseStep 3971531 = 5957297) B5957297
theorem B5962187 : Blo 1568982 5962187 := bstep (se 1 (by rfl) ⟨4471640, by rfl⟩ : syracuseStep 5962187 = 8943281) B8943281
theorem B6707735 : Blo 1568982 6707735 := bstep (se 1 (by rfl) ⟨5030801, by rfl⟩ : syracuseStep 6707735 = 10061603) B10061603
theorem B4774493 : Blo 1568982 4774493 := bstep (se 3 (by rfl) ⟨895217, by rfl⟩ : syracuseStep 4774493 = 1790435) B1790435
theorem B2980631 : Blo 1568982 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B5299019 : Blo 1568982 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B20380517 : Blo 1568982 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B30186341 : Blo 1568982 30186341 := bstep (se 4 (by rfl) ⟨2829969, by rfl⟩ : syracuseStep 30186341 = 5659939) B5659939
theorem B3021707 : Blo 1568982 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B5659595 : Blo 1568982 5659595 := bstep (se 1 (by rfl) ⟨4244696, by rfl⟩ : syracuseStep 5659595 = 8489393) B8489393
theorem B12729419 : Blo 1568982 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B2120791 : Blo 1568982 2120791 := bstep (se 1 (by rfl) ⟨1590593, by rfl⟩ : syracuseStep 2120791 = 3181187) B3181187
theorem B5299289 : Blo 1568982 5299289 := bstep (se 2 (by rfl) ⟨1987233, by rfl⟩ : syracuseStep 5299289 = 3974467) B3974467
theorem B5962841 : Blo 1568982 5962841 := bstep (se 2 (by rfl) ⟨2236065, by rfl⟩ : syracuseStep 5962841 = 4472131) B4472131
theorem B3579265 : Blo 1568982 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B10190231 : Blo 1568982 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B3972503 : Blo 1568982 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B5963159 : Blo 1568982 5963159 := bstep (se 1 (by rfl) ⟨4472369, by rfl⟩ : syracuseStep 5963159 = 8944739) B8944739
theorem B2981299 : Blo 1568982 2981299 := bstep (se 1 (by rfl) ⟨2235974, by rfl⟩ : syracuseStep 2981299 = 4471949) B4471949
theorem B6045229 : Blo 1568982 6045229 := bstep (se 3 (by rfl) ⟨1133480, by rfl⟩ : syracuseStep 6045229 = 2266961) B2266961
theorem B13418135 : Blo 1568982 13418135 := bstep (se 1 (by rfl) ⟨10063601, by rfl⟩ : syracuseStep 13418135 = 20127203) B20127203
theorem B3530393 : Blo 1568982 3530393 := bstep (se 2 (by rfl) ⟨1323897, by rfl⟩ : syracuseStep 3530393 = 2647795) B2647795
theorem B12902105 : Blo 1568982 12902105 := bstep (se 2 (by rfl) ⟨4838289, by rfl⟩ : syracuseStep 12902105 = 9676579) B9676579
theorem B3530483 : Blo 1568982 3530483 := bstep (se 1 (by rfl) ⟨2647862, by rfl⟩ : syracuseStep 3530483 = 5295725) B5295725
theorem B3530519 : Blo 1568982 3530519 := bstep (se 1 (by rfl) ⟨2647889, by rfl⟩ : syracuseStep 3530519 = 5295779) B5295779
theorem B5299991 : Blo 1568982 5299991 := bstep (se 1 (by rfl) ⟨3974993, by rfl⟩ : syracuseStep 5299991 = 7949987) B7949987
theorem B11919149 : Blo 1568982 11919149 := bstep (se 3 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 11919149 = 4469681) B4469681
theorem B17891117 : Blo 1568982 17891117 := bstep (se 3 (by rfl) ⟨3354584, by rfl⟩ : syracuseStep 17891117 = 6709169) B6709169
theorem B2981747 : Blo 1568982 2981747 := bstep (se 1 (by rfl) ⟨2236310, by rfl⟩ : syracuseStep 2981747 = 4472621) B4472621
theorem B2981785 : Blo 1568982 2981785 := bstep (se 2 (by rfl) ⟨1118169, by rfl⟩ : syracuseStep 2981785 = 2236339) B2236339
theorem B104611763 : Blo 1568982 104611763 := bstep (se 1 (by rfl) ⟨78458822, by rfl⟩ : syracuseStep 104611763 = 156917645) B156917645
theorem B3530699 : Blo 1568982 3530699 := bstep (se 1 (by rfl) ⟨2648024, by rfl⟩ : syracuseStep 3530699 = 5296049) B5296049
theorem B3973121 : Blo 1568982 3973121 := bstep (se 2 (by rfl) ⟨1489920, by rfl⟩ : syracuseStep 3973121 = 2979841) B2979841
theorem B6365213 : Blo 1568982 6365213 := bstep (se 3 (by rfl) ⟨1193477, by rfl⟩ : syracuseStep 6365213 = 2386955) B2386955
theorem B4243571 : Blo 1568982 4243571 := bstep (se 1 (by rfl) ⟨3182678, by rfl⟩ : syracuseStep 4243571 = 6365357) B6365357
theorem B2982035 : Blo 1568982 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B28639433 : Blo 1568982 28639433 := bstep (se 2 (by rfl) ⟨10739787, by rfl⟩ : syracuseStep 28639433 = 21479575) B21479575
theorem B2982089 : Blo 1568982 2982089 := bstep (se 2 (by rfl) ⟨1118283, by rfl⟩ : syracuseStep 2982089 = 2236567) B2236567
theorem B8937701 : Blo 1568982 8937701 := bstep (se 4 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 8937701 = 1675819) B1675819
theorem B2236663 : Blo 1568982 2236663 := bstep (se 1 (by rfl) ⟨1677497, by rfl⟩ : syracuseStep 2236663 = 3354995) B3354995
theorem B7545089 : Blo 1568982 7545089 := bstep (se 2 (by rfl) ⟨2829408, by rfl⟩ : syracuseStep 7545089 = 5658817) B5658817
theorem B3531023 : Blo 1568982 3531023 := bstep (se 1 (by rfl) ⟨2648267, by rfl⟩ : syracuseStep 3531023 = 5296535) B5296535
theorem B2867471 : Blo 1568982 2867471 := bstep (se 1 (by rfl) ⟨2150603, by rfl⟩ : syracuseStep 2867471 = 4301207) B4301207
theorem B3531041 : Blo 1568982 3531041 := bstep (se 2 (by rfl) ⟨1324140, by rfl⟩ : syracuseStep 3531041 = 2648281) B2648281
theorem B4243745 : Blo 1568982 4243745 := bstep (se 2 (by rfl) ⟨1591404, by rfl⟩ : syracuseStep 4243745 = 3182809) B3182809
theorem B2982187 : Blo 1568982 2982187 := bstep (se 1 (by rfl) ⟨2236640, by rfl⟩ : syracuseStep 2982187 = 4473281) B4473281
theorem B7946585 : Blo 1568982 7946585 := bstep (se 2 (by rfl) ⟨2979969, by rfl⟩ : syracuseStep 7946585 = 5959939) B5959939
theorem B3973495 : Blo 1568982 3973495 := bstep (se 1 (by rfl) ⟨2980121, by rfl⟩ : syracuseStep 3973495 = 5960243) B5960243
theorem B4473235 : Blo 1568982 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B7545241 : Blo 1568982 7545241 := bstep (se 2 (by rfl) ⟨2829465, by rfl⟩ : syracuseStep 7545241 = 5658931) B5658931
theorem B5300747 : Blo 1568982 5300747 := bstep (se 1 (by rfl) ⟨3975560, by rfl⟩ : syracuseStep 5300747 = 7951121) B7951121
theorem B5964299 : Blo 1568982 5964299 := bstep (se 1 (by rfl) ⟨4473224, by rfl⟩ : syracuseStep 5964299 = 8946449) B8946449
theorem B3531383 : Blo 1568982 3531383 := bstep (se 1 (by rfl) ⟨2648537, by rfl⟩ : syracuseStep 3531383 = 5297075) B5297075
theorem B5300855 : Blo 1568982 5300855 := bstep (se 1 (by rfl) ⟨3975641, by rfl⟩ : syracuseStep 5300855 = 7951283) B7951283
theorem B4473463 : Blo 1568982 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B17883827 : Blo 1568982 17883827 := bstep (se 1 (by rfl) ⟨13412870, by rfl⟩ : syracuseStep 17883827 = 26825741) B26825741
theorem B33940259 : Blo 1568982 33940259 := bstep (se 1 (by rfl) ⟨25455194, by rfl⟩ : syracuseStep 33940259 = 50910389) B50910389
theorem B16974629 : Blo 1568982 16974629 := bstep (se 4 (by rfl) ⟨1591371, by rfl⟩ : syracuseStep 16974629 = 3182743) B3182743
theorem B3531563 : Blo 1568982 3531563 := bstep (se 1 (by rfl) ⟨2648672, by rfl⟩ : syracuseStep 3531563 = 5297345) B5297345
theorem B3973931 : Blo 1568982 3973931 := bstep (se 1 (by rfl) ⟨2980448, by rfl⟩ : syracuseStep 3973931 = 5960897) B5960897
theorem B3531923 : Blo 1568982 3531923 := bstep (se 1 (by rfl) ⟨2648942, by rfl⟩ : syracuseStep 3531923 = 5297885) B5297885
theorem B8946881 : Blo 1568982 8946881 := bstep (se 2 (by rfl) ⟨3355080, by rfl⟩ : syracuseStep 8946881 = 6710161) B6710161
theorem B3531977 : Blo 1568982 3531977 := bstep (se 2 (by rfl) ⟨1324491, by rfl⟩ : syracuseStep 3531977 = 2648983) B2648983
theorem B5301449 : Blo 1568982 5301449 := bstep (se 2 (by rfl) ⟨1988043, by rfl⟩ : syracuseStep 5301449 = 3976087) B3976087
theorem B2827721 : Blo 1568982 2827721 := bstep (se 2 (by rfl) ⟨1060395, by rfl⟩ : syracuseStep 2827721 = 2120791) B2120791
theorem B3974771 : Blo 1568982 3974771 := bstep (se 1 (by rfl) ⟨2981078, by rfl⟩ : syracuseStep 3974771 = 5962157) B5962157
theorem B2647687 : Blo 1568982 2647687 := bstep (se 1 (by rfl) ⟨1985765, by rfl⟩ : syracuseStep 2647687 = 3971531) B3971531
theorem B3974791 : Blo 1568982 3974791 := bstep (se 1 (by rfl) ⟨2981093, by rfl⟩ : syracuseStep 3974791 = 5962187) B5962187
theorem B2385721 : Blo 1568982 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B3532679 : Blo 1568982 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B5031827 : Blo 1568982 5031827 := bstep (se 1 (by rfl) ⟨3773870, by rfl⟩ : syracuseStep 5031827 = 7547741) B7547741
theorem B3975065 : Blo 1568982 3975065 := bstep (se 2 (by rfl) ⟨1490649, by rfl⟩ : syracuseStep 3975065 = 2981299) B2981299
theorem B3532859 : Blo 1568982 3532859 := bstep (se 1 (by rfl) ⟨2649644, by rfl⟩ : syracuseStep 3532859 = 5299289) B5299289
theorem B3975227 : Blo 1568982 3975227 := bstep (se 1 (by rfl) ⟨2981420, by rfl⟩ : syracuseStep 3975227 = 5962841) B5962841
theorem B90581165 : Blo 1568982 90581165 := bstep (se 3 (by rfl) ⟨16983968, by rfl⟩ : syracuseStep 90581165 = 33967937) B33967937
theorem B3532985 : Blo 1568982 3532985 := bstep (se 2 (by rfl) ⟨1324869, by rfl⟩ : syracuseStep 3532985 = 2649739) B2649739
theorem B6703361 : Blo 1568982 6703361 := bstep (se 2 (by rfl) ⟨2513760, by rfl⟩ : syracuseStep 6703361 = 5027521) B5027521
theorem B6793487 : Blo 1568982 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B2648335 : Blo 1568982 2648335 := bstep (se 1 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 2648335 = 3972503) B3972503
theorem B3975439 : Blo 1568982 3975439 := bstep (se 1 (by rfl) ⟨2981579, by rfl⟩ : syracuseStep 3975439 = 5963159) B5963159
theorem B4245821 : Blo 1568982 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B2353481 : Blo 1568982 2353481 := bstep (se 2 (by rfl) ⟨882555, by rfl⟩ : syracuseStep 2353481 = 1765111) B1765111
theorem B7948691 : Blo 1568982 7948691 := bstep (se 1 (by rfl) ⟨5961518, by rfl⟩ : syracuseStep 7948691 = 11923037) B11923037
theorem B2353595 : Blo 1568982 2353595 := bstep (se 1 (by rfl) ⟨1765196, by rfl⟩ : syracuseStep 2353595 = 3530393) B3530393
theorem B2353655 : Blo 1568982 2353655 := bstep (se 1 (by rfl) ⟨1765241, by rfl⟩ : syracuseStep 2353655 = 3530483) B3530483
theorem B2353679 : Blo 1568982 2353679 := bstep (se 1 (by rfl) ⟨1765259, by rfl⟩ : syracuseStep 2353679 = 3530519) B3530519
theorem B3533327 : Blo 1568982 3533327 := bstep (se 1 (by rfl) ⟨2649995, by rfl⟩ : syracuseStep 3533327 = 5299991) B5299991
theorem B3533345 : Blo 1568982 3533345 := bstep (se 2 (by rfl) ⟨1325004, by rfl⟩ : syracuseStep 3533345 = 2650009) B2650009
theorem B3975713 : Blo 1568982 3975713 := bstep (se 2 (by rfl) ⟨1490892, by rfl⟩ : syracuseStep 3975713 = 2981785) B2981785
theorem B2353721 : Blo 1568982 2353721 := bstep (se 2 (by rfl) ⟨882645, by rfl⟩ : syracuseStep 2353721 = 1765291) B1765291
theorem B69741175 : Blo 1568982 69741175 := bstep (se 1 (by rfl) ⟨52305881, by rfl⟩ : syracuseStep 69741175 = 104611763) B104611763
theorem B2353799 : Blo 1568982 2353799 := bstep (se 1 (by rfl) ⟨1765349, by rfl⟩ : syracuseStep 2353799 = 3530699) B3530699
theorem B2353835 : Blo 1568982 2353835 := bstep (se 1 (by rfl) ⟨1765376, by rfl⟩ : syracuseStep 2353835 = 3530753) B3530753
theorem B2353865 : Blo 1568982 2353865 := bstep (se 2 (by rfl) ⟨882699, by rfl⟩ : syracuseStep 2353865 = 1765399) B1765399
theorem B8055497 : Blo 1568982 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B19360547 : Blo 1568982 19360547 := bstep (se 1 (by rfl) ⟨14520410, by rfl⟩ : syracuseStep 19360547 = 29040821) B29040821
theorem B10062629 : Blo 1568982 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B2648875 : Blo 1568982 2648875 := bstep (se 1 (by rfl) ⟨1986656, by rfl⟩ : syracuseStep 2648875 = 3973313) B3973313
theorem B11316017 : Blo 1568982 11316017 := bstep (se 2 (by rfl) ⟨4243506, by rfl⟩ : syracuseStep 11316017 = 8487013) B8487013
theorem B2353979 : Blo 1568982 2353979 := bstep (se 1 (by rfl) ⟨1765484, by rfl⟩ : syracuseStep 2353979 = 3530969) B3530969
theorem B2354039 : Blo 1568982 2354039 := bstep (se 1 (by rfl) ⟨1765529, by rfl⟩ : syracuseStep 2354039 = 3531059) B3531059
theorem B3533687 : Blo 1568982 3533687 := bstep (se 1 (by rfl) ⟨2650265, by rfl⟩ : syracuseStep 3533687 = 5300531) B5300531
theorem B3181447 : Blo 1568982 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B2354063 : Blo 1568982 2354063 := bstep (se 1 (by rfl) ⟨1765547, by rfl⟩ : syracuseStep 2354063 = 3531095) B3531095
theorem B3353491 : Blo 1568982 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B2354105 : Blo 1568982 2354105 := bstep (se 2 (by rfl) ⟨882789, by rfl⟩ : syracuseStep 2354105 = 1765579) B1765579
theorem B2649017 : Blo 1568982 2649017 := bstep (se 2 (by rfl) ⟨993381, by rfl⟩ : syracuseStep 2649017 = 1986763) B1986763
theorem B2354183 : Blo 1568982 2354183 := bstep (se 1 (by rfl) ⟨1765637, by rfl⟩ : syracuseStep 2354183 = 3531275) B3531275
theorem B2354219 : Blo 1568982 2354219 := bstep (se 1 (by rfl) ⟨1765664, by rfl⟩ : syracuseStep 2354219 = 3531329) B3531329
theorem B3533867 : Blo 1568982 3533867 := bstep (se 1 (by rfl) ⟨2650400, by rfl⟩ : syracuseStep 3533867 = 5300801) B5300801
theorem B2354249 : Blo 1568982 2354249 := bstep (se 2 (by rfl) ⟨882843, by rfl⟩ : syracuseStep 2354249 = 1765687) B1765687
theorem B2354363 : Blo 1568982 2354363 := bstep (se 1 (by rfl) ⟨1765772, by rfl⟩ : syracuseStep 2354363 = 3531545) B3531545
theorem B2354423 : Blo 1568982 2354423 := bstep (se 1 (by rfl) ⟨1765817, by rfl⟩ : syracuseStep 2354423 = 3531635) B3531635
theorem B2354447 : Blo 1568982 2354447 := bstep (se 1 (by rfl) ⟨1765835, by rfl⟩ : syracuseStep 2354447 = 3531671) B3531671
theorem B24177953 : Blo 1568982 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B2354489 : Blo 1568982 2354489 := bstep (se 2 (by rfl) ⟨882933, by rfl⟩ : syracuseStep 2354489 = 1765867) B1765867
theorem B2354567 : Blo 1568982 2354567 := bstep (se 1 (by rfl) ⟨1765925, by rfl⟩ : syracuseStep 2354567 = 3531851) B3531851
theorem B3534227 : Blo 1568982 3534227 := bstep (se 1 (by rfl) ⟨2650670, by rfl⟩ : syracuseStep 3534227 = 5301341) B5301341
theorem B2354603 : Blo 1568982 2354603 := bstep (se 1 (by rfl) ⟨1765952, by rfl⟩ : syracuseStep 2354603 = 3531905) B3531905
theorem B2354633 : Blo 1568982 2354633 := bstep (se 2 (by rfl) ⟨882987, by rfl⟩ : syracuseStep 2354633 = 1765975) B1765975
theorem B3534281 : Blo 1568982 3534281 := bstep (se 2 (by rfl) ⟨1325355, by rfl⟩ : syracuseStep 3534281 = 2650711) B2650711
theorem B2387447 : Blo 1568982 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B2354747 : Blo 1568982 2354747 := bstep (se 1 (by rfl) ⟨1766060, by rfl⟩ : syracuseStep 2354747 = 3532121) B3532121
theorem B13405763 : Blo 1568982 13405763 := bstep (se 1 (by rfl) ⟨10054322, by rfl⟩ : syracuseStep 13405763 = 20108645) B20108645
theorem B2354807 : Blo 1568982 2354807 := bstep (se 1 (by rfl) ⟨1766105, by rfl⟩ : syracuseStep 2354807 = 3532211) B3532211
theorem B2649719 : Blo 1568982 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B2354831 : Blo 1568982 2354831 := bstep (se 1 (by rfl) ⟨1766123, by rfl⟩ : syracuseStep 2354831 = 3532247) B3532247
theorem B2354873 : Blo 1568982 2354873 := bstep (se 2 (by rfl) ⟨883077, by rfl⟩ : syracuseStep 2354873 = 1766155) B1766155
theorem B2354951 : Blo 1568982 2354951 := bstep (se 1 (by rfl) ⟨1766213, by rfl⟩ : syracuseStep 2354951 = 3532427) B3532427
theorem B5295887 : Blo 1568982 5295887 := bstep (se 1 (by rfl) ⟨3971915, by rfl⟩ : syracuseStep 5295887 = 7943831) B7943831
theorem B5959439 : Blo 1568982 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B2354987 : Blo 1568982 2354987 := bstep (se 1 (by rfl) ⟨1766240, by rfl⟩ : syracuseStep 2354987 = 3532481) B3532481
theorem B2355017 : Blo 1568982 2355017 := bstep (se 2 (by rfl) ⟨883131, by rfl⟩ : syracuseStep 2355017 = 1766263) B1766263
theorem B1765255 : Blo 1568982 1765255 := bstep (se 1 (by rfl) ⟨1323941, by rfl⟩ : syracuseStep 1765255 = 2647883) B2647883
theorem B1986439 : Blo 1568982 1986439 := bstep (se 1 (by rfl) ⟨1489829, by rfl⟩ : syracuseStep 1986439 = 2979659) B2979659
theorem B3772295 : Blo 1568982 3772295 := bstep (se 1 (by rfl) ⟨2829221, by rfl⟩ : syracuseStep 3772295 = 5658443) B5658443
theorem B8056729 : Blo 1568982 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B2355131 : Blo 1568982 2355131 := bstep (se 1 (by rfl) ⟨1766348, by rfl⟩ : syracuseStep 2355131 = 3532697) B3532697
theorem B2355191 : Blo 1568982 2355191 := bstep (se 1 (by rfl) ⟨1766393, by rfl⟩ : syracuseStep 2355191 = 3532787) B3532787
theorem B2355215 : Blo 1568982 2355215 := bstep (se 1 (by rfl) ⟨1766411, by rfl⟩ : syracuseStep 2355215 = 3532823) B3532823
theorem B5296157 : Blo 1568982 5296157 := bstep (se 3 (by rfl) ⟨993029, by rfl⟩ : syracuseStep 5296157 = 1986059) B1986059
theorem B2355257 : Blo 1568982 2355257 := bstep (se 2 (by rfl) ⟨883221, by rfl⟩ : syracuseStep 2355257 = 1766443) B1766443
theorem B2388025 : Blo 1568982 2388025 := bstep (se 2 (by rfl) ⟨895509, by rfl⟩ : syracuseStep 2388025 = 1791019) B1791019
theorem B1765435 : Blo 1568982 1765435 := bstep (se 1 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 1765435 = 2648153) B2648153
theorem B2650171 : Blo 1568982 2650171 := bstep (se 1 (by rfl) ⟨1987628, by rfl⟩ : syracuseStep 2650171 = 3975257) B3975257
theorem B18116741 : Blo 1568982 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B4771975 : Blo 1568982 4771975 := bstep (se 1 (by rfl) ⟨3578981, by rfl⟩ : syracuseStep 4771975 = 7157963) B7157963
theorem B2355335 : Blo 1568982 2355335 := bstep (se 1 (by rfl) ⟨1766501, by rfl⟩ : syracuseStep 2355335 = 3533003) B3533003
theorem B2355371 : Blo 1568982 2355371 := bstep (se 1 (by rfl) ⟨1766528, by rfl⟩ : syracuseStep 2355371 = 3533057) B3533057
theorem B7540937 : Blo 1568982 7540937 := bstep (se 2 (by rfl) ⟨2827851, by rfl⟩ : syracuseStep 7540937 = 5655703) B5655703
theorem B2355401 : Blo 1568982 2355401 := bstep (se 2 (by rfl) ⟨883275, by rfl⟩ : syracuseStep 2355401 = 1766551) B1766551
theorem B2650313 : Blo 1568982 2650313 := bstep (se 2 (by rfl) ⟨993867, by rfl⟩ : syracuseStep 2650313 = 1987735) B1987735
theorem B1569031 : Blo 1568982 1569031 := bstep (se 1 (by rfl) ⟨1176773, by rfl⟩ : syracuseStep 1569031 = 2353547) B2353547
theorem B1569039 : Blo 1568982 1569039 := bstep (se 1 (by rfl) ⟨1176779, by rfl⟩ : syracuseStep 1569039 = 2353559) B2353559
theorem B1986859 : Blo 1568982 1986859 := bstep (se 1 (by rfl) ⟨1490144, by rfl⟩ : syracuseStep 1986859 = 2980289) B2980289
theorem B1569083 : Blo 1568982 1569083 := bstep (se 1 (by rfl) ⟨1176812, by rfl⟩ : syracuseStep 1569083 = 2353625) B2353625
theorem B2355515 : Blo 1568982 2355515 := bstep (se 1 (by rfl) ⟨1766636, by rfl⟩ : syracuseStep 2355515 = 3533273) B3533273
theorem B2355575 : Blo 1568982 2355575 := bstep (se 1 (by rfl) ⟨1766681, by rfl⟩ : syracuseStep 2355575 = 3533363) B3533363
theorem B1569159 : Blo 1568982 1569159 := bstep (se 1 (by rfl) ⟨1176869, by rfl⟩ : syracuseStep 1569159 = 2353739) B2353739
theorem B1569167 : Blo 1568982 1569167 := bstep (se 1 (by rfl) ⟨1176875, by rfl⟩ : syracuseStep 1569167 = 2353751) B2353751
theorem B2355599 : Blo 1568982 2355599 := bstep (se 1 (by rfl) ⟨1766699, by rfl⟩ : syracuseStep 2355599 = 3533399) B3533399
theorem B3182995 : Blo 1568982 3182995 := bstep (se 1 (by rfl) ⟨2387246, by rfl⟩ : syracuseStep 3182995 = 4774493) B4774493
theorem B2355641 : Blo 1568982 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B1569211 : Blo 1568982 1569211 := bstep (se 1 (by rfl) ⟨1176908, by rfl⟩ : syracuseStep 1569211 = 2353817) B2353817
theorem B4772353 : Blo 1568982 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B4469249 : Blo 1568982 4469249 := bstep (se 2 (by rfl) ⟨1675968, by rfl⟩ : syracuseStep 4469249 = 3351937) B3351937
theorem B1569287 : Blo 1568982 1569287 := bstep (se 1 (by rfl) ⟨1176965, by rfl⟩ : syracuseStep 1569287 = 2353931) B2353931
theorem B2355719 : Blo 1568982 2355719 := bstep (se 1 (by rfl) ⟨1766789, by rfl⟩ : syracuseStep 2355719 = 3533579) B3533579
theorem B1569295 : Blo 1568982 1569295 := bstep (se 1 (by rfl) ⟨1176971, by rfl⟩ : syracuseStep 1569295 = 2353943) B2353943
theorem B1765903 : Blo 1568982 1765903 := bstep (se 1 (by rfl) ⟨1324427, by rfl⟩ : syracuseStep 1765903 = 2648855) B2648855
theorem B1987087 : Blo 1568982 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B10056221 : Blo 1568982 10056221 := bstep (se 3 (by rfl) ⟨1885541, by rfl⟩ : syracuseStep 10056221 = 3771083) B3771083
theorem B2355755 : Blo 1568982 2355755 := bstep (se 1 (by rfl) ⟨1766816, by rfl⟩ : syracuseStep 2355755 = 3533633) B3533633
theorem B1569339 : Blo 1568982 1569339 := bstep (se 1 (by rfl) ⟨1177004, by rfl⟩ : syracuseStep 1569339 = 2354009) B2354009
theorem B13587011 : Blo 1568982 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B20124227 : Blo 1568982 20124227 := bstep (se 1 (by rfl) ⟨15093170, by rfl⟩ : syracuseStep 20124227 = 30186341) B30186341
theorem B2355785 : Blo 1568982 2355785 := bstep (se 2 (by rfl) ⟨883419, by rfl⟩ : syracuseStep 2355785 = 1766839) B1766839
theorem B4469363 : Blo 1568982 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B1569415 : Blo 1568982 1569415 := bstep (se 1 (by rfl) ⟨1177061, by rfl⟩ : syracuseStep 1569415 = 2354123) B2354123
theorem B3773063 : Blo 1568982 3773063 := bstep (se 1 (by rfl) ⟨2829797, by rfl⟩ : syracuseStep 3773063 = 5659595) B5659595
theorem B1569423 : Blo 1568982 1569423 := bstep (se 1 (by rfl) ⟨1177067, by rfl⟩ : syracuseStep 1569423 = 2354135) B2354135
theorem B1569467 : Blo 1568982 1569467 := bstep (se 1 (by rfl) ⟨1177100, by rfl⟩ : syracuseStep 1569467 = 2354201) B2354201
theorem B2355899 : Blo 1568982 2355899 := bstep (se 1 (by rfl) ⟨1766924, by rfl⟩ : syracuseStep 2355899 = 3533849) B3533849
theorem B2355959 : Blo 1568982 2355959 := bstep (se 1 (by rfl) ⟨1766969, by rfl⟩ : syracuseStep 2355959 = 3533939) B3533939
theorem B1569543 : Blo 1568982 1569543 := bstep (se 1 (by rfl) ⟨1177157, by rfl⟩ : syracuseStep 1569543 = 2354315) B2354315
theorem B1569551 : Blo 1568982 1569551 := bstep (se 1 (by rfl) ⟨1177163, by rfl⟩ : syracuseStep 1569551 = 2354327) B2354327
theorem B2355983 : Blo 1568982 2355983 := bstep (se 1 (by rfl) ⟨1766987, by rfl⟩ : syracuseStep 2355983 = 3533975) B3533975
theorem B2356025 : Blo 1568982 2356025 := bstep (se 2 (by rfl) ⟨883509, by rfl⟩ : syracuseStep 2356025 = 1767019) B1767019
theorem B1569595 : Blo 1568982 1569595 := bstep (se 1 (by rfl) ⟨1177196, by rfl⟩ : syracuseStep 1569595 = 2354393) B2354393
theorem B1569671 : Blo 1568982 1569671 := bstep (se 1 (by rfl) ⟨1177253, by rfl⟩ : syracuseStep 1569671 = 2354507) B2354507
theorem B2356103 : Blo 1568982 2356103 := bstep (se 1 (by rfl) ⟨1767077, by rfl⟩ : syracuseStep 2356103 = 3534155) B3534155
theorem B2651015 : Blo 1568982 2651015 := bstep (se 1 (by rfl) ⟨1988261, by rfl⟩ : syracuseStep 2651015 = 3976523) B3976523
theorem B1569679 : Blo 1568982 1569679 := bstep (se 1 (by rfl) ⟨1177259, by rfl⟩ : syracuseStep 1569679 = 2354519) B2354519
theorem B2356139 : Blo 1568982 2356139 := bstep (se 1 (by rfl) ⟨1767104, by rfl⟩ : syracuseStep 2356139 = 3534209) B3534209
theorem B1569723 : Blo 1568982 1569723 := bstep (se 1 (by rfl) ⟨1177292, by rfl⟩ : syracuseStep 1569723 = 2354585) B2354585
theorem B4469705 : Blo 1568982 4469705 := bstep (se 2 (by rfl) ⟨1676139, by rfl⟩ : syracuseStep 4469705 = 3352279) B3352279
theorem B2356169 : Blo 1568982 2356169 := bstep (se 2 (by rfl) ⟨883563, by rfl⟩ : syracuseStep 2356169 = 1767127) B1767127
theorem B1569799 : Blo 1568982 1569799 := bstep (se 1 (by rfl) ⟨1177349, by rfl⟩ : syracuseStep 1569799 = 2354699) B2354699
theorem B1766407 : Blo 1568982 1766407 := bstep (se 1 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 1766407 = 2649611) B2649611
theorem B2978831 : Blo 1568982 2978831 := bstep (se 1 (by rfl) ⟨2234123, by rfl⟩ : syracuseStep 2978831 = 4468247) B4468247
theorem B1569807 : Blo 1568982 1569807 := bstep (se 1 (by rfl) ⟨1177355, by rfl⟩ : syracuseStep 1569807 = 2354711) B2354711
theorem B1569851 : Blo 1568982 1569851 := bstep (se 1 (by rfl) ⟨1177388, by rfl⟩ : syracuseStep 1569851 = 2354777) B2354777
theorem B2356283 : Blo 1568982 2356283 := bstep (se 1 (by rfl) ⟨1767212, by rfl⟩ : syracuseStep 2356283 = 3534425) B3534425
theorem B2356343 : Blo 1568982 2356343 := bstep (se 1 (by rfl) ⟨1767257, by rfl⟩ : syracuseStep 2356343 = 3534515) B3534515
theorem B1569927 : Blo 1568982 1569927 := bstep (se 1 (by rfl) ⟨1177445, by rfl⟩ : syracuseStep 1569927 = 2354891) B2354891
theorem B1569935 : Blo 1568982 1569935 := bstep (se 1 (by rfl) ⟨1177451, by rfl⟩ : syracuseStep 1569935 = 2354903) B2354903
theorem B2356367 : Blo 1568982 2356367 := bstep (se 1 (by rfl) ⟨1767275, by rfl⟩ : syracuseStep 2356367 = 3534551) B3534551
theorem B12727469 : Blo 1568982 12727469 := bstep (se 3 (by rfl) ⟨2386400, by rfl⟩ : syracuseStep 12727469 = 4772801) B4772801
theorem B2356409 : Blo 1568982 2356409 := bstep (se 2 (by rfl) ⟨883653, by rfl⟩ : syracuseStep 2356409 = 1767307) B1767307
theorem B1569979 : Blo 1568982 1569979 := bstep (se 1 (by rfl) ⟨1177484, by rfl⟩ : syracuseStep 1569979 = 2354969) B2354969
theorem B1766587 : Blo 1568982 1766587 := bstep (se 1 (by rfl) ⟨1324940, by rfl⟩ : syracuseStep 1766587 = 2649881) B2649881
theorem B1987831 : Blo 1568982 1987831 := bstep (se 1 (by rfl) ⟨1490873, by rfl⟩ : syracuseStep 1987831 = 2981747) B2981747
theorem B1570055 : Blo 1568982 1570055 := bstep (se 1 (by rfl) ⟨1177541, by rfl⟩ : syracuseStep 1570055 = 2355083) B2355083
theorem B1570063 : Blo 1568982 1570063 := bstep (se 1 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 1570063 = 2355095) B2355095
theorem B1570107 : Blo 1568982 1570107 := bstep (se 1 (by rfl) ⟨1177580, by rfl⟩ : syracuseStep 1570107 = 2355161) B2355161
theorem B1570183 : Blo 1568982 1570183 := bstep (se 1 (by rfl) ⟨1177637, by rfl⟩ : syracuseStep 1570183 = 2355275) B2355275
theorem B1570191 : Blo 1568982 1570191 := bstep (se 1 (by rfl) ⟨1177643, by rfl⟩ : syracuseStep 1570191 = 2355287) B2355287
theorem B5297561 : Blo 1568982 5297561 := bstep (se 2 (by rfl) ⟨1986585, by rfl⟩ : syracuseStep 5297561 = 3973171) B3973171
theorem B7951769 : Blo 1568982 7951769 := bstep (se 2 (by rfl) ⟨2981913, by rfl⟩ : syracuseStep 7951769 = 5963827) B5963827
theorem B1570235 : Blo 1568982 1570235 := bstep (se 1 (by rfl) ⟨1177676, by rfl⟩ : syracuseStep 1570235 = 2355353) B2355353
theorem B1570311 : Blo 1568982 1570311 := bstep (se 1 (by rfl) ⟨1177733, by rfl⟩ : syracuseStep 1570311 = 2355467) B2355467
theorem B1570319 : Blo 1568982 1570319 := bstep (se 1 (by rfl) ⟨1177739, by rfl⟩ : syracuseStep 1570319 = 2355479) B2355479
theorem B1570363 : Blo 1568982 1570363 := bstep (se 1 (by rfl) ⟨1177772, by rfl⟩ : syracuseStep 1570363 = 2355545) B2355545
theorem B1988155 : Blo 1568982 1988155 := bstep (se 1 (by rfl) ⟨1491116, by rfl⟩ : syracuseStep 1988155 = 2982233) B2982233
theorem B2233975 : Blo 1568982 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B4028039 : Blo 1568982 4028039 := bstep (se 1 (by rfl) ⟨3021029, by rfl⟩ : syracuseStep 4028039 = 6042059) B6042059
theorem B1570439 : Blo 1568982 1570439 := bstep (se 1 (by rfl) ⟨1177829, by rfl⟩ : syracuseStep 1570439 = 2355659) B2355659
theorem B1570447 : Blo 1568982 1570447 := bstep (se 1 (by rfl) ⟨1177835, by rfl⟩ : syracuseStep 1570447 = 2355671) B2355671
theorem B1767055 : Blo 1568982 1767055 := bstep (se 1 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 1767055 = 2650583) B2650583
theorem B42981043 : Blo 1568982 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B1570491 : Blo 1568982 1570491 := bstep (se 1 (by rfl) ⟨1177868, by rfl⟩ : syracuseStep 1570491 = 2355737) B2355737
theorem B1570567 : Blo 1568982 1570567 := bstep (se 1 (by rfl) ⟨1177925, by rfl⟩ : syracuseStep 1570567 = 2355851) B2355851
theorem B1570575 : Blo 1568982 1570575 := bstep (se 1 (by rfl) ⟨1177931, by rfl⟩ : syracuseStep 1570575 = 2355863) B2355863
theorem B1570619 : Blo 1568982 1570619 := bstep (se 1 (by rfl) ⟨1177964, by rfl⟩ : syracuseStep 1570619 = 2355929) B2355929
theorem B1570695 : Blo 1568982 1570695 := bstep (se 1 (by rfl) ⟨1178021, by rfl⟩ : syracuseStep 1570695 = 2356043) B2356043
theorem B1570703 : Blo 1568982 1570703 := bstep (se 1 (by rfl) ⟨1178027, by rfl⟩ : syracuseStep 1570703 = 2356055) B2356055
theorem B17217443 : Blo 1568982 17217443 := bstep (se 1 (by rfl) ⟨12913082, by rfl⟩ : syracuseStep 17217443 = 25826165) B25826165
theorem B1570747 : Blo 1568982 1570747 := bstep (se 1 (by rfl) ⟨1178060, by rfl⟩ : syracuseStep 1570747 = 2356121) B2356121
theorem B1570823 : Blo 1568982 1570823 := bstep (se 1 (by rfl) ⟨1178117, by rfl⟩ : syracuseStep 1570823 = 2356235) B2356235
theorem B1570831 : Blo 1568982 1570831 := bstep (se 1 (by rfl) ⟨1178123, by rfl⟩ : syracuseStep 1570831 = 2356247) B2356247
theorem B1570875 : Blo 1568982 1570875 := bstep (se 1 (by rfl) ⟨1178156, by rfl⟩ : syracuseStep 1570875 = 2356313) B2356313
theorem B3774523 : Blo 1568982 3774523 := bstep (se 1 (by rfl) ⟨2830892, by rfl⟩ : syracuseStep 3774523 = 5661785) B5661785
theorem B14325821 : Blo 1568982 14325821 := bstep (se 3 (by rfl) ⟨2686091, by rfl⟩ : syracuseStep 14325821 = 5372183) B5372183
theorem B5298263 : Blo 1568982 5298263 := bstep (se 1 (by rfl) ⟨3973697, by rfl⟩ : syracuseStep 5298263 = 7947395) B7947395
theorem B1570951 : Blo 1568982 1570951 := bstep (se 1 (by rfl) ⟨1178213, by rfl⟩ : syracuseStep 1570951 = 2356427) B2356427
theorem B1570959 : Blo 1568982 1570959 := bstep (se 1 (by rfl) ⟨1178219, by rfl⟩ : syracuseStep 1570959 = 2356439) B2356439
theorem B4593935 : Blo 1568982 4593935 := bstep (se 1 (by rfl) ⟨3445451, by rfl⟩ : syracuseStep 4593935 = 6890903) B6890903
theorem B3225899 : Blo 1568982 3225899 := bstep (se 1 (by rfl) ⟨2419424, by rfl⟩ : syracuseStep 3225899 = 4838849) B4838849
theorem B2980243 : Blo 1568982 2980243 := bstep (se 1 (by rfl) ⟨2235182, by rfl⟩ : syracuseStep 2980243 = 4470365) B4470365
theorem B2234795 : Blo 1568982 2234795 := bstep (se 1 (by rfl) ⟨1676096, by rfl⟩ : syracuseStep 2234795 = 3352193) B3352193
theorem B11467307 : Blo 1568982 11467307 := bstep (se 1 (by rfl) ⟨8600480, by rfl⟩ : syracuseStep 11467307 = 17200961) B17200961
theorem B5298749 : Blo 1568982 5298749 := bstep (se 3 (by rfl) ⟨993515, by rfl⟩ : syracuseStep 5298749 = 1987031) B1987031
theorem B2980471 : Blo 1568982 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B13589221 : Blo 1568982 13589221 := bstep (se 4 (by rfl) ⟨1273989, by rfl⟩ : syracuseStep 13589221 = 2547979) B2547979
theorem B3971855 : Blo 1568982 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B4471595 : Blo 1568982 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B8936243 : Blo 1568982 8936243 := bstep (se 1 (by rfl) ⟨6702182, by rfl⟩ : syracuseStep 8936243 = 13404365) B13404365
theorem B12581747 : Blo 1568982 12581747 := bstep (se 1 (by rfl) ⟨9436310, by rfl⟩ : syracuseStep 12581747 = 18872621) B18872621
theorem B3971987 : Blo 1568982 3971987 := bstep (se 1 (by rfl) ⟨2978990, by rfl⟩ : syracuseStep 3971987 = 5957981) B5957981
theorem B5962643 : Blo 1568982 5962643 := bstep (se 1 (by rfl) ⟨4471982, by rfl⟩ : syracuseStep 5962643 = 8943965) B8943965
theorem B4471823 : Blo 1568982 4471823 := bstep (se 1 (by rfl) ⟨3353867, by rfl⟩ : syracuseStep 4471823 = 6707735) B6707735
theorem B2014471 : Blo 1568982 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B21470599 : Blo 1568982 21470599 := bstep (se 1 (by rfl) ⟨16102949, by rfl⟩ : syracuseStep 21470599 = 32205899) B32205899
theorem B8486279 : Blo 1568982 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B8060305 : Blo 1568982 8060305 := bstep (se 2 (by rfl) ⟨3022614, by rfl⟩ : syracuseStep 8060305 = 6045229) B6045229
theorem B5660171 : Blo 1568982 5660171 := bstep (se 1 (by rfl) ⟨4245128, by rfl⟩ : syracuseStep 5660171 = 8490257) B8490257
theorem B9674263 : Blo 1568982 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B4595287 : Blo 1568982 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B3530375 : Blo 1568982 3530375 := bstep (se 1 (by rfl) ⟨2647781, by rfl⟩ : syracuseStep 3530375 = 5295563) B5295563
theorem B6799049 : Blo 1568982 6799049 := bstep (se 2 (by rfl) ⟨2549643, by rfl⟩ : syracuseStep 6799049 = 5099287) B5099287
theorem B20111105 : Blo 1568982 20111105 := bstep (se 2 (by rfl) ⟨7541664, by rfl⟩ : syracuseStep 20111105 = 15083329) B15083329
theorem B8945423 : Blo 1568982 8945423 := bstep (se 1 (by rfl) ⟨6709067, by rfl⟩ : syracuseStep 8945423 = 13418135) B13418135
theorem B9060133 : Blo 1568982 9060133 := bstep (se 4 (by rfl) ⟨849387, by rfl⟩ : syracuseStep 9060133 = 1698775) B1698775
theorem B7544627 : Blo 1568982 7544627 := bstep (se 1 (by rfl) ⟨5658470, by rfl⟩ : syracuseStep 7544627 = 11316941) B11316941
theorem B3530555 : Blo 1568982 3530555 := bstep (se 1 (by rfl) ⟨2647916, by rfl⟩ : syracuseStep 3530555 = 5295833) B5295833
theorem B8601403 : Blo 1568982 8601403 := bstep (se 1 (by rfl) ⟨6451052, by rfl⟩ : syracuseStep 8601403 = 12902105) B12902105
theorem B13410137 : Blo 1568982 13410137 := bstep (se 2 (by rfl) ⟨5028801, by rfl⟩ : syracuseStep 13410137 = 10057603) B10057603
theorem B7946099 : Blo 1568982 7946099 := bstep (se 1 (by rfl) ⟨5959574, by rfl⟩ : syracuseStep 7946099 = 11919149) B11919149
theorem B11927411 : Blo 1568982 11927411 := bstep (se 1 (by rfl) ⟨8945558, by rfl⟩ : syracuseStep 11927411 = 17891117) B17891117
theorem B15097751 : Blo 1568982 15097751 := bstep (se 1 (by rfl) ⟨11323313, by rfl⟩ : syracuseStep 15097751 = 22646627) B22646627
theorem B3530681 : Blo 1568982 3530681 := bstep (se 2 (by rfl) ⟨1324005, by rfl⟩ : syracuseStep 3530681 = 2648011) B2648011
theorem B5300153 : Blo 1568982 5300153 := bstep (se 2 (by rfl) ⟨1987557, by rfl⟩ : syracuseStep 5300153 = 3975115) B3975115
theorem B3530771 : Blo 1568982 3530771 := bstep (se 1 (by rfl) ⟨2648078, by rfl⟩ : syracuseStep 3530771 = 5296157) B5296157
theorem B4243475 : Blo 1568982 4243475 := bstep (se 1 (by rfl) ⟨3182606, by rfl⟩ : syracuseStep 4243475 = 6365213) B6365213
theorem B5030059 : Blo 1568982 5030059 := bstep (se 1 (by rfl) ⟨3772544, by rfl⟩ : syracuseStep 5030059 = 7545089) B7545089
theorem B3531113 : Blo 1568982 3531113 := bstep (se 2 (by rfl) ⟨1324167, by rfl⟩ : syracuseStep 3531113 = 2648335) B2648335
theorem B5300585 : Blo 1568982 5300585 := bstep (se 2 (by rfl) ⟨1987719, by rfl⟩ : syracuseStep 5300585 = 3975439) B3975439
theorem B2515375 : Blo 1568982 2515375 := bstep (se 1 (by rfl) ⟨1886531, by rfl⟩ : syracuseStep 2515375 = 3773063) B3773063
theorem B33939917 : Blo 1568982 33939917 := bstep (se 3 (by rfl) ⟨6363734, by rfl⟩ : syracuseStep 33939917 = 12727469) B12727469
theorem B22626839 : Blo 1568982 22626839 := bstep (se 1 (by rfl) ⟨16970129, by rfl⟩ : syracuseStep 22626839 = 33940259) B33940259
theorem B3973657 : Blo 1568982 3973657 := bstep (se 2 (by rfl) ⟨1490121, by rfl⟩ : syracuseStep 3973657 = 2980243) B2980243
theorem B5964313 : Blo 1568982 5964313 := bstep (se 2 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 5964313 = 4473235) B4473235
theorem B10060321 : Blo 1568982 10060321 := bstep (se 2 (by rfl) ⟨3772620, by rfl⟩ : syracuseStep 10060321 = 7545241) B7545241
theorem B5964587 : Blo 1568982 5964587 := bstep (se 1 (by rfl) ⟨4473440, by rfl⟩ : syracuseStep 5964587 = 8946881) B8946881
theorem B92988233 : Blo 1568982 92988233 := bstep (se 2 (by rfl) ⟨34870587, by rfl⟩ : syracuseStep 92988233 = 69741175) B69741175
theorem B3973961 : Blo 1568982 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B5964617 : Blo 1568982 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B3531707 : Blo 1568982 3531707 := bstep (se 1 (by rfl) ⟨2648780, by rfl⟩ : syracuseStep 3531707 = 5297561) B5297561
theorem B5301179 : Blo 1568982 5301179 := bstep (se 1 (by rfl) ⟨3975884, by rfl⟩ : syracuseStep 5301179 = 7951769) B7951769
theorem B3531833 : Blo 1568982 3531833 := bstep (se 2 (by rfl) ⟨1324437, by rfl⟩ : syracuseStep 3531833 = 2648875) B2648875
theorem B11478295 : Blo 1568982 11478295 := bstep (se 1 (by rfl) ⟨8608721, by rfl⟩ : syracuseStep 11478295 = 17217443) B17217443
theorem B11928869 : Blo 1568982 11928869 := bstep (se 4 (by rfl) ⟨1118331, by rfl⟩ : syracuseStep 11928869 = 2236663) B2236663
theorem B3532175 : Blo 1568982 3532175 := bstep (se 1 (by rfl) ⟨2649131, by rfl⟩ : syracuseStep 3532175 = 5298263) B5298263
theorem B7644871 : Blo 1568982 7644871 := bstep (se 1 (by rfl) ⟨5733653, by rfl⟩ : syracuseStep 7644871 = 11467307) B11467307
theorem B3532499 : Blo 1568982 3532499 := bstep (se 1 (by rfl) ⟨2649374, by rfl⟩ : syracuseStep 3532499 = 5298749) B5298749
theorem B2647903 : Blo 1568982 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B21481325 : Blo 1568982 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B5957495 : Blo 1568982 5957495 := bstep (se 1 (by rfl) ⟨4468121, by rfl⟩ : syracuseStep 5957495 = 8936243) B8936243
theorem B2647991 : Blo 1568982 2647991 := bstep (se 1 (by rfl) ⟨1985993, by rfl⟩ : syracuseStep 2647991 = 3971987) B3971987
theorem B3975095 : Blo 1568982 3975095 := bstep (se 1 (by rfl) ⟨2981321, by rfl⟩ : syracuseStep 3975095 = 5962643) B5962643
theorem B16975973 : Blo 1568982 16975973 := bstep (se 4 (by rfl) ⟨1591497, by rfl⟩ : syracuseStep 16975973 = 3182995) B3182995
theorem B17885285 : Blo 1568982 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B1591631 : Blo 1568982 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B3180961 : Blo 1568982 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B2353583 : Blo 1568982 2353583 := bstep (se 1 (by rfl) ⟨1765187, by rfl⟩ : syracuseStep 2353583 = 3530375) B3530375
theorem B4532699 : Blo 1568982 4532699 := bstep (se 1 (by rfl) ⟨3399524, by rfl⟩ : syracuseStep 4532699 = 6799049) B6799049
theorem B2353673 : Blo 1568982 2353673 := bstep (se 2 (by rfl) ⟨882627, by rfl⟩ : syracuseStep 2353673 = 1765255) B1765255
theorem B2648585 : Blo 1568982 2648585 := bstep (se 2 (by rfl) ⟨993219, by rfl⟩ : syracuseStep 2648585 = 1986439) B1986439
theorem B10742305 : Blo 1568982 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B2353703 : Blo 1568982 2353703 := bstep (se 1 (by rfl) ⟨1765277, by rfl⟩ : syracuseStep 2353703 = 3530555) B3530555
theorem B8940091 : Blo 1568982 8940091 := bstep (se 1 (by rfl) ⟨6705068, by rfl⟩ : syracuseStep 8940091 = 13410137) B13410137
theorem B2353787 : Blo 1568982 2353787 := bstep (se 1 (by rfl) ⟨1765340, by rfl⟩ : syracuseStep 2353787 = 3530681) B3530681
theorem B3533435 : Blo 1568982 3533435 := bstep (se 1 (by rfl) ⟨2650076, by rfl⟩ : syracuseStep 3533435 = 5300153) B5300153
theorem B2648747 : Blo 1568982 2648747 := bstep (se 1 (by rfl) ⟨1986560, by rfl⟩ : syracuseStep 2648747 = 3973121) B3973121
theorem B2829047 : Blo 1568982 2829047 := bstep (se 1 (by rfl) ⟨2121785, by rfl⟩ : syracuseStep 2829047 = 4243571) B4243571
theorem B2353913 : Blo 1568982 2353913 := bstep (se 2 (by rfl) ⟨882717, by rfl⟩ : syracuseStep 2353913 = 1765435) B1765435
theorem B3533561 : Blo 1568982 3533561 := bstep (se 2 (by rfl) ⟨1325085, by rfl⟩ : syracuseStep 3533561 = 2650171) B2650171
theorem B5032697 : Blo 1568982 5032697 := bstep (se 2 (by rfl) ⟨1887261, by rfl⟩ : syracuseStep 5032697 = 3774523) B3774523
theorem B5958467 : Blo 1568982 5958467 := bstep (se 1 (by rfl) ⟨4468850, by rfl⟩ : syracuseStep 5958467 = 8937701) B8937701
theorem B2354015 : Blo 1568982 2354015 := bstep (se 1 (by rfl) ⟨1765511, by rfl⟩ : syracuseStep 2354015 = 3531023) B3531023
theorem B1911647 : Blo 1568982 1911647 := bstep (se 1 (by rfl) ⟨1433735, by rfl⟩ : syracuseStep 1911647 = 2867471) B2867471
theorem B2354027 : Blo 1568982 2354027 := bstep (se 1 (by rfl) ⟨1765520, by rfl⟩ : syracuseStep 2354027 = 3531041) B3531041
theorem B2829163 : Blo 1568982 2829163 := bstep (se 1 (by rfl) ⟨2121872, by rfl⟩ : syracuseStep 2829163 = 4243745) B4243745
theorem B3533831 : Blo 1568982 3533831 := bstep (se 1 (by rfl) ⟨2650373, by rfl⟩ : syracuseStep 3533831 = 5300747) B5300747
theorem B3976199 : Blo 1568982 3976199 := bstep (se 1 (by rfl) ⟨2982149, by rfl⟩ : syracuseStep 3976199 = 5964299) B5964299
theorem B48311309 : Blo 1568982 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B6704147 : Blo 1568982 6704147 := bstep (se 1 (by rfl) ⟨5028110, by rfl⟩ : syracuseStep 6704147 = 10056221) B10056221
theorem B2649145 : Blo 1568982 2649145 := bstep (se 2 (by rfl) ⟨993429, by rfl⟩ : syracuseStep 2649145 = 1986859) B1986859
theorem B3976249 : Blo 1568982 3976249 := bstep (se 2 (by rfl) ⟨1491093, by rfl⟩ : syracuseStep 3976249 = 2982187) B2982187
theorem B2354255 : Blo 1568982 2354255 := bstep (se 1 (by rfl) ⟨1765691, by rfl⟩ : syracuseStep 2354255 = 3531383) B3531383
theorem B3533903 : Blo 1568982 3533903 := bstep (se 1 (by rfl) ⟨2650427, by rfl⟩ : syracuseStep 3533903 = 5300855) B5300855
theorem B11922551 : Blo 1568982 11922551 := bstep (se 1 (by rfl) ⟨8941913, by rfl⟩ : syracuseStep 11922551 = 17883827) B17883827
theorem B11316419 : Blo 1568982 11316419 := bstep (se 1 (by rfl) ⟨8487314, by rfl⟩ : syracuseStep 11316419 = 16974629) B16974629
theorem B2354375 : Blo 1568982 2354375 := bstep (se 1 (by rfl) ⟨1765781, by rfl⟩ : syracuseStep 2354375 = 3531563) B3531563
theorem B2649287 : Blo 1568982 2649287 := bstep (se 1 (by rfl) ⟨1986965, by rfl⟩ : syracuseStep 2649287 = 3973931) B3973931
theorem B1985887 : Blo 1568982 1985887 := bstep (se 1 (by rfl) ⟨1489415, by rfl⟩ : syracuseStep 1985887 = 2978831) B2978831
theorem B2354537 : Blo 1568982 2354537 := bstep (se 2 (by rfl) ⟨882951, by rfl⟩ : syracuseStep 2354537 = 1765903) B1765903
theorem B2649449 : Blo 1568982 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B2354615 : Blo 1568982 2354615 := bstep (se 1 (by rfl) ⟨1765961, by rfl⟩ : syracuseStep 2354615 = 3531923) B3531923
theorem B2354651 : Blo 1568982 2354651 := bstep (se 1 (by rfl) ⟨1765988, by rfl⟩ : syracuseStep 2354651 = 3531977) B3531977
theorem B3534299 : Blo 1568982 3534299 := bstep (se 1 (by rfl) ⟨2650724, by rfl⟩ : syracuseStep 3534299 = 5301449) B5301449
theorem B2649847 : Blo 1568982 2649847 := bstep (se 1 (by rfl) ⟨1987385, by rfl⟩ : syracuseStep 2649847 = 3974771) B3974771
theorem B5959453 : Blo 1568982 5959453 := bstep (se 3 (by rfl) ⟨1117397, by rfl⟩ : syracuseStep 5959453 = 2234795) B2234795
theorem B7540589 : Blo 1568982 7540589 := bstep (se 3 (by rfl) ⟨1413860, by rfl⟩ : syracuseStep 7540589 = 2827721) B2827721
theorem B2355119 : Blo 1568982 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B3354551 : Blo 1568982 3354551 := bstep (se 1 (by rfl) ⟨2515913, by rfl⟩ : syracuseStep 3354551 = 5031827) B5031827
theorem B2650043 : Blo 1568982 2650043 := bstep (se 1 (by rfl) ⟨1987532, by rfl⟩ : syracuseStep 2650043 = 3975065) B3975065
theorem B2355209 : Blo 1568982 2355209 := bstep (se 2 (by rfl) ⟨883203, by rfl⟩ : syracuseStep 2355209 = 1766407) B1766407
theorem B2355239 : Blo 1568982 2355239 := bstep (se 1 (by rfl) ⟨1766429, by rfl⟩ : syracuseStep 2355239 = 3532859) B3532859
theorem B2650151 : Blo 1568982 2650151 := bstep (se 1 (by rfl) ⟨1987613, by rfl⟩ : syracuseStep 2650151 = 3975227) B3975227
theorem B60387443 : Blo 1568982 60387443 := bstep (se 1 (by rfl) ⟨45290582, by rfl⟩ : syracuseStep 60387443 = 90581165) B90581165
theorem B2355323 : Blo 1568982 2355323 := bstep (se 1 (by rfl) ⟨1766492, by rfl⟩ : syracuseStep 2355323 = 3532985) B3532985
theorem B4468907 : Blo 1568982 4468907 := bstep (se 1 (by rfl) ⟨3351680, by rfl⟩ : syracuseStep 4468907 = 6703361) B6703361
theorem B2150599 : Blo 1568982 2150599 := bstep (se 1 (by rfl) ⟨1612949, by rfl⟩ : syracuseStep 2150599 = 3225899) B3225899
theorem B2830547 : Blo 1568982 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1568987 : Blo 1568982 1568987 := bstep (se 1 (by rfl) ⟨1176740, by rfl⟩ : syracuseStep 1568987 = 2353481) B2353481
theorem B2355449 : Blo 1568982 2355449 := bstep (se 2 (by rfl) ⟨883293, by rfl⟩ : syracuseStep 2355449 = 1766587) B1766587
theorem B1569063 : Blo 1568982 1569063 := bstep (se 1 (by rfl) ⟨1176797, by rfl⟩ : syracuseStep 1569063 = 2353595) B2353595
theorem B2650441 : Blo 1568982 2650441 := bstep (se 2 (by rfl) ⟨993915, by rfl⟩ : syracuseStep 2650441 = 1987831) B1987831
theorem B1569103 : Blo 1568982 1569103 := bstep (se 1 (by rfl) ⟨1176827, by rfl⟩ : syracuseStep 1569103 = 2353655) B2353655
theorem B1569119 : Blo 1568982 1569119 := bstep (se 1 (by rfl) ⟨1176839, by rfl⟩ : syracuseStep 1569119 = 2353679) B2353679
theorem B2355551 : Blo 1568982 2355551 := bstep (se 1 (by rfl) ⟨1766663, by rfl⟩ : syracuseStep 2355551 = 3533327) B3533327
theorem B2355563 : Blo 1568982 2355563 := bstep (se 1 (by rfl) ⟨1766672, by rfl⟩ : syracuseStep 2355563 = 3533345) B3533345
theorem B2650475 : Blo 1568982 2650475 := bstep (se 1 (by rfl) ⟨1987856, by rfl⟩ : syracuseStep 2650475 = 3975713) B3975713
theorem B1569147 : Blo 1568982 1569147 := bstep (se 1 (by rfl) ⟨1176860, by rfl⟩ : syracuseStep 1569147 = 2353721) B2353721
theorem B1569199 : Blo 1568982 1569199 := bstep (se 1 (by rfl) ⟨1176899, by rfl⟩ : syracuseStep 1569199 = 2353799) B2353799
theorem B1569223 : Blo 1568982 1569223 := bstep (se 1 (by rfl) ⟨1176917, by rfl⟩ : syracuseStep 1569223 = 2353835) B2353835
theorem B1569243 : Blo 1568982 1569243 := bstep (se 1 (by rfl) ⟨1176932, by rfl⟩ : syracuseStep 1569243 = 2353865) B2353865
theorem B28627465 : Blo 1568982 28627465 := bstep (se 2 (by rfl) ⟨10735299, by rfl⟩ : syracuseStep 28627465 = 21470599) B21470599
theorem B12907031 : Blo 1568982 12907031 := bstep (se 1 (by rfl) ⟨9680273, by rfl⟩ : syracuseStep 12907031 = 19360547) B19360547
theorem B1569319 : Blo 1568982 1569319 := bstep (se 1 (by rfl) ⟨1176989, by rfl⟩ : syracuseStep 1569319 = 2353979) B2353979
theorem B1569359 : Blo 1568982 1569359 := bstep (se 1 (by rfl) ⟨1177019, by rfl⟩ : syracuseStep 1569359 = 2354039) B2354039
theorem B2355791 : Blo 1568982 2355791 := bstep (se 1 (by rfl) ⟨1766843, by rfl⟩ : syracuseStep 2355791 = 3533687) B3533687
theorem B1569375 : Blo 1568982 1569375 := bstep (se 1 (by rfl) ⟨1177031, by rfl⟩ : syracuseStep 1569375 = 2354063) B2354063
theorem B1569403 : Blo 1568982 1569403 := bstep (se 1 (by rfl) ⟨1177052, by rfl⟩ : syracuseStep 1569403 = 2354105) B2354105
theorem B1766011 : Blo 1568982 1766011 := bstep (se 1 (by rfl) ⟨1324508, by rfl⟩ : syracuseStep 1766011 = 2649017) B2649017
theorem B1569455 : Blo 1568982 1569455 := bstep (se 1 (by rfl) ⟨1177091, by rfl⟩ : syracuseStep 1569455 = 2354183) B2354183
theorem B1569479 : Blo 1568982 1569479 := bstep (se 1 (by rfl) ⟨1177109, by rfl⟩ : syracuseStep 1569479 = 2354219) B2354219
theorem B2355911 : Blo 1568982 2355911 := bstep (se 1 (by rfl) ⟨1766933, by rfl⟩ : syracuseStep 2355911 = 3533867) B3533867
theorem B12899017 : Blo 1568982 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B1569499 : Blo 1568982 1569499 := bstep (se 1 (by rfl) ⟨1177124, by rfl⟩ : syracuseStep 1569499 = 2354249) B2354249
theorem B2650873 : Blo 1568982 2650873 := bstep (se 2 (by rfl) ⟨994077, by rfl⟩ : syracuseStep 2650873 = 1988155) B1988155
theorem B1569575 : Blo 1568982 1569575 := bstep (se 1 (by rfl) ⟨1177181, by rfl⟩ : syracuseStep 1569575 = 2354363) B2354363
theorem B2978633 : Blo 1568982 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B1569615 : Blo 1568982 1569615 := bstep (se 1 (by rfl) ⟨1177211, by rfl⟩ : syracuseStep 1569615 = 2354423) B2354423
theorem B1569631 : Blo 1568982 1569631 := bstep (se 1 (by rfl) ⟨1177223, by rfl⟩ : syracuseStep 1569631 = 2354447) B2354447
theorem B2356073 : Blo 1568982 2356073 := bstep (se 2 (by rfl) ⟨883527, by rfl⟩ : syracuseStep 2356073 = 1767055) B1767055
theorem B16118635 : Blo 1568982 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B1569659 : Blo 1568982 1569659 := bstep (se 1 (by rfl) ⟨1177244, by rfl⟩ : syracuseStep 1569659 = 2354489) B2354489
theorem B57308057 : Blo 1568982 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B1569711 : Blo 1568982 1569711 := bstep (se 1 (by rfl) ⟨1177283, by rfl⟩ : syracuseStep 1569711 = 2354567) B2354567
theorem B5657519 : Blo 1568982 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B2356151 : Blo 1568982 2356151 := bstep (se 1 (by rfl) ⟨1767113, by rfl⟩ : syracuseStep 2356151 = 3534227) B3534227
theorem B1569735 : Blo 1568982 1569735 := bstep (se 1 (by rfl) ⟨1177301, by rfl⟩ : syracuseStep 1569735 = 2354603) B2354603
theorem B1569755 : Blo 1568982 1569755 := bstep (se 1 (by rfl) ⟨1177316, by rfl⟩ : syracuseStep 1569755 = 2354633) B2354633
theorem B2356187 : Blo 1568982 2356187 := bstep (se 1 (by rfl) ⟨1767140, by rfl⟩ : syracuseStep 2356187 = 3534281) B3534281
theorem B3773447 : Blo 1568982 3773447 := bstep (se 1 (by rfl) ⟨2830085, by rfl⟩ : syracuseStep 3773447 = 5660171) B5660171
theorem B1569831 : Blo 1568982 1569831 := bstep (se 1 (by rfl) ⟨1177373, by rfl⟩ : syracuseStep 1569831 = 2354747) B2354747
theorem B12080177 : Blo 1568982 12080177 := bstep (se 2 (by rfl) ⟨4530066, by rfl⟩ : syracuseStep 12080177 = 9060133) B9060133
theorem B1569871 : Blo 1568982 1569871 := bstep (se 1 (by rfl) ⟨1177403, by rfl⟩ : syracuseStep 1569871 = 2354807) B2354807
theorem B1766479 : Blo 1568982 1766479 := bstep (se 1 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 1766479 = 2649719) B2649719
theorem B1569887 : Blo 1568982 1569887 := bstep (se 1 (by rfl) ⟨1177415, by rfl⟩ : syracuseStep 1569887 = 2354831) B2354831
theorem B1569915 : Blo 1568982 1569915 := bstep (se 1 (by rfl) ⟨1177436, by rfl⟩ : syracuseStep 1569915 = 2354873) B2354873
theorem B13407403 : Blo 1568982 13407403 := bstep (se 1 (by rfl) ⟨10055552, by rfl⟩ : syracuseStep 13407403 = 20111105) B20111105
theorem B1569967 : Blo 1568982 1569967 := bstep (se 1 (by rfl) ⟨1177475, by rfl⟩ : syracuseStep 1569967 = 2354951) B2354951
theorem B1569991 : Blo 1568982 1569991 := bstep (se 1 (by rfl) ⟨1177493, by rfl⟩ : syracuseStep 1569991 = 2354987) B2354987
theorem B1570011 : Blo 1568982 1570011 := bstep (se 1 (by rfl) ⟨1177508, by rfl⟩ : syracuseStep 1570011 = 2355017) B2355017
theorem B5297399 : Blo 1568982 5297399 := bstep (se 1 (by rfl) ⟨3973049, by rfl⟩ : syracuseStep 5297399 = 7946099) B7946099
theorem B7951607 : Blo 1568982 7951607 := bstep (se 1 (by rfl) ⟨5963705, by rfl⟩ : syracuseStep 7951607 = 11927411) B11927411
theorem B10065167 : Blo 1568982 10065167 := bstep (se 1 (by rfl) ⟨7548875, by rfl⟩ : syracuseStep 10065167 = 15097751) B15097751
theorem B1570087 : Blo 1568982 1570087 := bstep (se 1 (by rfl) ⟨1177565, by rfl⟩ : syracuseStep 1570087 = 2355131) B2355131
theorem B1570127 : Blo 1568982 1570127 := bstep (se 1 (by rfl) ⟨1177595, by rfl⟩ : syracuseStep 1570127 = 2355191) B2355191
theorem B1570143 : Blo 1568982 1570143 := bstep (se 1 (by rfl) ⟨1177607, by rfl⟩ : syracuseStep 1570143 = 2355215) B2355215
theorem B1570171 : Blo 1568982 1570171 := bstep (se 1 (by rfl) ⟨1177628, by rfl⟩ : syracuseStep 1570171 = 2355257) B2355257
theorem B3184033 : Blo 1568982 3184033 := bstep (se 2 (by rfl) ⟨1194012, by rfl⟩ : syracuseStep 3184033 = 2388025) B2388025
theorem B1570223 : Blo 1568982 1570223 := bstep (se 1 (by rfl) ⟨1177667, by rfl⟩ : syracuseStep 1570223 = 2355335) B2355335
theorem B1570247 : Blo 1568982 1570247 := bstep (se 1 (by rfl) ⟨1177685, by rfl⟩ : syracuseStep 1570247 = 2355371) B2355371
theorem B5027291 : Blo 1568982 5027291 := bstep (se 1 (by rfl) ⟨3770468, by rfl⟩ : syracuseStep 5027291 = 7540937) B7540937
theorem B19092955 : Blo 1568982 19092955 := bstep (se 1 (by rfl) ⟨14319716, by rfl⟩ : syracuseStep 19092955 = 28639433) B28639433
theorem B1570267 : Blo 1568982 1570267 := bstep (se 1 (by rfl) ⟨1177700, by rfl⟩ : syracuseStep 1570267 = 2355401) B2355401
theorem B1766875 : Blo 1568982 1766875 := bstep (se 1 (by rfl) ⟨1325156, by rfl⟩ : syracuseStep 1766875 = 2650313) B2650313
theorem B1988059 : Blo 1568982 1988059 := bstep (se 1 (by rfl) ⟨1491044, by rfl⟩ : syracuseStep 1988059 = 2982089) B2982089
theorem B6362633 : Blo 1568982 6362633 := bstep (se 2 (by rfl) ⟨2385987, by rfl⟩ : syracuseStep 6362633 = 4771975) B4771975
theorem B1570343 : Blo 1568982 1570343 := bstep (se 1 (by rfl) ⟨1177757, by rfl⟩ : syracuseStep 1570343 = 2355515) B2355515
theorem B5297723 : Blo 1568982 5297723 := bstep (se 1 (by rfl) ⟨3973292, by rfl⟩ : syracuseStep 5297723 = 7946585) B7946585
theorem B1570383 : Blo 1568982 1570383 := bstep (se 1 (by rfl) ⟨1177787, by rfl⟩ : syracuseStep 1570383 = 2355575) B2355575
theorem B1570399 : Blo 1568982 1570399 := bstep (se 1 (by rfl) ⟨1177799, by rfl⟩ : syracuseStep 1570399 = 2355599) B2355599
theorem B1570427 : Blo 1568982 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B2979499 : Blo 1568982 2979499 := bstep (se 1 (by rfl) ⟨2234624, by rfl⟩ : syracuseStep 2979499 = 4469249) B4469249
theorem B1570479 : Blo 1568982 1570479 := bstep (se 1 (by rfl) ⟨1177859, by rfl⟩ : syracuseStep 1570479 = 2355719) B2355719
theorem B1570503 : Blo 1568982 1570503 := bstep (se 1 (by rfl) ⟨1177877, by rfl⟩ : syracuseStep 1570503 = 2355755) B2355755
theorem B9058007 : Blo 1568982 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B13416151 : Blo 1568982 13416151 := bstep (se 1 (by rfl) ⟨10062113, by rfl⟩ : syracuseStep 13416151 = 20124227) B20124227
theorem B1570523 : Blo 1568982 1570523 := bstep (se 1 (by rfl) ⟨1177892, by rfl⟩ : syracuseStep 1570523 = 2355785) B2355785
theorem B7952093 : Blo 1568982 7952093 := bstep (se 3 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 7952093 = 2982035) B2982035
theorem B2979575 : Blo 1568982 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B1570599 : Blo 1568982 1570599 := bstep (se 1 (by rfl) ⟨1177949, by rfl⟩ : syracuseStep 1570599 = 2355899) B2355899
theorem B5297993 : Blo 1568982 5297993 := bstep (se 2 (by rfl) ⟨1986747, by rfl⟩ : syracuseStep 5297993 = 3973495) B3973495
theorem B1570639 : Blo 1568982 1570639 := bstep (se 1 (by rfl) ⟨1177979, by rfl⟩ : syracuseStep 1570639 = 2355959) B2355959
theorem B1570655 : Blo 1568982 1570655 := bstep (se 1 (by rfl) ⟨1177991, by rfl⟩ : syracuseStep 1570655 = 2355983) B2355983
theorem B1570683 : Blo 1568982 1570683 := bstep (se 1 (by rfl) ⟨1178012, by rfl⟩ : syracuseStep 1570683 = 2356025) B2356025
theorem B1570735 : Blo 1568982 1570735 := bstep (se 1 (by rfl) ⟨1178051, by rfl⟩ : syracuseStep 1570735 = 2356103) B2356103
theorem B1767343 : Blo 1568982 1767343 := bstep (se 1 (by rfl) ⟨1325507, by rfl⟩ : syracuseStep 1767343 = 2651015) B2651015
theorem B1570759 : Blo 1568982 1570759 := bstep (se 1 (by rfl) ⟨1178069, by rfl⟩ : syracuseStep 1570759 = 2356139) B2356139
theorem B2979803 : Blo 1568982 2979803 := bstep (se 1 (by rfl) ⟨2234852, by rfl⟩ : syracuseStep 2979803 = 4469705) B4469705
theorem B1570779 : Blo 1568982 1570779 := bstep (se 1 (by rfl) ⟨1178084, by rfl⟩ : syracuseStep 1570779 = 2356169) B2356169
theorem B6363137 : Blo 1568982 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B1570855 : Blo 1568982 1570855 := bstep (se 1 (by rfl) ⟨1178141, by rfl⟩ : syracuseStep 1570855 = 2356283) B2356283
theorem B1570895 : Blo 1568982 1570895 := bstep (se 1 (by rfl) ⟨1178171, by rfl⟩ : syracuseStep 1570895 = 2356343) B2356343
theorem B1570911 : Blo 1568982 1570911 := bstep (se 1 (by rfl) ⟨1178183, by rfl⟩ : syracuseStep 1570911 = 2356367) B2356367
theorem B1570939 : Blo 1568982 1570939 := bstep (se 1 (by rfl) ⟨1178204, by rfl⟩ : syracuseStep 1570939 = 2356409) B2356409
theorem B18118961 : Blo 1568982 18118961 := bstep (se 2 (by rfl) ⟨6794610, by rfl⟩ : syracuseStep 18118961 = 13589221) B13589221
theorem B2685359 : Blo 1568982 2685359 := bstep (se 1 (by rfl) ⟨2014019, by rfl⟩ : syracuseStep 2685359 = 4028039) B4028039
theorem B4241929 : Blo 1568982 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B9550547 : Blo 1568982 9550547 := bstep (se 1 (by rfl) ⟨7162910, by rfl⟩ : syracuseStep 9550547 = 14325821) B14325821
theorem B4528991 : Blo 1568982 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B3062623 : Blo 1568982 3062623 := bstep (se 1 (by rfl) ⟨2296967, by rfl⟩ : syracuseStep 3062623 = 4593935) B4593935
theorem B5299127 : Blo 1568982 5299127 := bstep (se 1 (by rfl) ⟨3974345, by rfl⟩ : syracuseStep 5299127 = 7948691) B7948691
theorem B2685961 : Blo 1568982 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B10747073 : Blo 1568982 10747073 := bstep (se 2 (by rfl) ⟨4030152, by rfl⟩ : syracuseStep 10747073 = 8060305) B8060305
theorem B6708419 : Blo 1568982 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B2981063 : Blo 1568982 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B7544011 : Blo 1568982 7544011 := bstep (se 1 (by rfl) ⟨5658008, by rfl⟩ : syracuseStep 7544011 = 11316017) B11316017
theorem B8387831 : Blo 1568982 8387831 := bstep (se 1 (by rfl) ⟨6290873, by rfl⟩ : syracuseStep 8387831 = 12581747) B12581747
theorem B2981215 : Blo 1568982 2981215 := bstep (se 1 (by rfl) ⟨2235911, by rfl⟩ : syracuseStep 2981215 = 4471823) B4471823
theorem B6127049 : Blo 1568982 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B3530249 : Blo 1568982 3530249 := bstep (se 2 (by rfl) ⟨1323843, by rfl⟩ : syracuseStep 3530249 = 2647687) B2647687
theorem B5299721 : Blo 1568982 5299721 := bstep (se 2 (by rfl) ⟨1987395, by rfl⟩ : syracuseStep 5299721 = 3974791) B3974791
theorem B8937175 : Blo 1568982 8937175 := bstep (se 1 (by rfl) ⟨6702881, by rfl⟩ : syracuseStep 8937175 = 13405763) B13405763
theorem B11468537 : Blo 1568982 11468537 := bstep (se 2 (by rfl) ⟨4300701, by rfl⟩ : syracuseStep 11468537 = 8601403) B8601403
theorem B3530591 : Blo 1568982 3530591 := bstep (se 1 (by rfl) ⟨2647943, by rfl⟩ : syracuseStep 3530591 = 5295887) B5295887
theorem B3972959 : Blo 1568982 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B5963615 : Blo 1568982 5963615 := bstep (se 1 (by rfl) ⟨4472711, by rfl⟩ : syracuseStep 5963615 = 8945423) B8945423
theorem B5029751 : Blo 1568982 5029751 := bstep (se 1 (by rfl) ⟨3772313, by rfl⟩ : syracuseStep 5029751 = 7544627) B7544627
theorem B2514863 : Blo 1568982 2514863 := bstep (se 1 (by rfl) ⟨1886147, by rfl⟩ : syracuseStep 2514863 = 3772295) B3772295
theorem B2867465 : Blo 1568982 2867465 := bstep (se 2 (by rfl) ⟨1075299, by rfl⟩ : syracuseStep 2867465 = 2150599) B2150599
theorem B22626611 : Blo 1568982 22626611 := bstep (se 1 (by rfl) ⟨16969958, by rfl⟩ : syracuseStep 22626611 = 33939917) B33939917
theorem B2515631 : Blo 1568982 2515631 := bstep (se 1 (by rfl) ⟨1886723, by rfl⟩ : syracuseStep 2515631 = 3773447) B3773447
theorem B8053451 : Blo 1568982 8053451 := bstep (se 1 (by rfl) ⟨6040088, by rfl⟩ : syracuseStep 8053451 = 12080177) B12080177
theorem B11920121 : Blo 1568982 11920121 := bstep (se 2 (by rfl) ⟨4470045, by rfl⟩ : syracuseStep 11920121 = 8940091) B8940091
theorem B3531599 : Blo 1568982 3531599 := bstep (se 1 (by rfl) ⟨2648699, by rfl⟩ : syracuseStep 3531599 = 5297399) B5297399
theorem B5301071 : Blo 1568982 5301071 := bstep (se 1 (by rfl) ⟨3975803, by rfl⟩ : syracuseStep 5301071 = 7951607) B7951607
theorem B6710111 : Blo 1568982 6710111 := bstep (se 1 (by rfl) ⟨5032583, by rfl⟩ : syracuseStep 6710111 = 10065167) B10065167
theorem B3351527 : Blo 1568982 3351527 := bstep (se 1 (by rfl) ⟨2513645, by rfl⟩ : syracuseStep 3351527 = 5027291) B5027291
theorem B40772645 : Blo 1568982 40772645 := bstep (se 4 (by rfl) ⟨3822435, by rfl⟩ : syracuseStep 40772645 = 7644871) B7644871
theorem B3531815 : Blo 1568982 3531815 := bstep (se 1 (by rfl) ⟨2648861, by rfl⟩ : syracuseStep 3531815 = 5297723) B5297723
theorem B7160957 : Blo 1568982 7160957 := bstep (se 3 (by rfl) ⟨1342679, by rfl⟩ : syracuseStep 7160957 = 2685359) B2685359
theorem B5301395 : Blo 1568982 5301395 := bstep (se 1 (by rfl) ⟨3976046, by rfl⟩ : syracuseStep 5301395 = 7952093) B7952093
theorem B3531995 : Blo 1568982 3531995 := bstep (se 1 (by rfl) ⟨2648996, by rfl⟩ : syracuseStep 3531995 = 5297993) B5297993
theorem B14320883 : Blo 1568982 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B3581281 : Blo 1568982 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B3532193 : Blo 1568982 3532193 := bstep (se 2 (by rfl) ⟨1324572, by rfl⟩ : syracuseStep 3532193 = 2649145) B2649145
theorem B5301665 : Blo 1568982 5301665 := bstep (se 2 (by rfl) ⟨1988124, by rfl⟩ : syracuseStep 5301665 = 3976249) B3976249
theorem B17876537 : Blo 1568982 17876537 := bstep (se 2 (by rfl) ⟨6703701, by rfl⟩ : syracuseStep 17876537 = 13407403) B13407403
theorem B15304393 : Blo 1568982 15304393 := bstep (se 2 (by rfl) ⟨5739147, by rfl⟩ : syracuseStep 15304393 = 11478295) B11478295
theorem B2647849 : Blo 1568982 2647849 := bstep (se 2 (by rfl) ⟨992943, by rfl⟩ : syracuseStep 2647849 = 1985887) B1985887
theorem B3974953 : Blo 1568982 3974953 := bstep (se 2 (by rfl) ⟨1490607, by rfl⟩ : syracuseStep 3974953 = 2981215) B2981215
theorem B6367031 : Blo 1568982 6367031 := bstep (se 1 (by rfl) ⟨4775273, by rfl⟩ : syracuseStep 6367031 = 9550547) B9550547
theorem B4245377 : Blo 1568982 4245377 := bstep (se 2 (by rfl) ⟨1592016, by rfl⟩ : syracuseStep 4245377 = 3184033) B3184033
theorem B3532751 : Blo 1568982 3532751 := bstep (se 1 (by rfl) ⟨2649563, by rfl⟩ : syracuseStep 3532751 = 5299127) B5299127
theorem B13420525 : Blo 1568982 13420525 := bstep (se 3 (by rfl) ⟨2516348, by rfl⟩ : syracuseStep 13420525 = 5032697) B5032697
theorem B7948367 : Blo 1568982 7948367 := bstep (se 1 (by rfl) ⟨5961275, by rfl⟩ : syracuseStep 7948367 = 11922551) B11922551
theorem B12077309 : Blo 1568982 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B5097725 : Blo 1568982 5097725 := bstep (se 3 (by rfl) ⟨955823, by rfl⟩ : syracuseStep 5097725 = 1911647) B1911647
theorem B3533129 : Blo 1568982 3533129 := bstep (se 2 (by rfl) ⟨1324923, by rfl⟩ : syracuseStep 3533129 = 2649847) B2649847
theorem B2353499 : Blo 1568982 2353499 := bstep (se 1 (by rfl) ⟨1765124, by rfl⟩ : syracuseStep 2353499 = 3530249) B3530249
theorem B3533147 : Blo 1568982 3533147 := bstep (se 1 (by rfl) ⟨2649860, by rfl⟩ : syracuseStep 3533147 = 5299721) B5299721
theorem B7645691 : Blo 1568982 7645691 := bstep (se 1 (by rfl) ⟨5734268, by rfl⟩ : syracuseStep 7645691 = 11468537) B11468537
theorem B2353727 : Blo 1568982 2353727 := bstep (se 1 (by rfl) ⟨1765295, by rfl⟩ : syracuseStep 2353727 = 3530591) B3530591
theorem B2648639 : Blo 1568982 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B3975743 : Blo 1568982 3975743 := bstep (se 1 (by rfl) ⟨2981807, by rfl⟩ : syracuseStep 3975743 = 5963615) B5963615
theorem B3353167 : Blo 1568982 3353167 := bstep (se 1 (by rfl) ⟨2514875, by rfl⟩ : syracuseStep 3353167 = 5029751) B5029751
theorem B16968365 : Blo 1568982 16968365 := bstep (se 3 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 16968365 = 6363137) B6363137
theorem B2353847 : Blo 1568982 2353847 := bstep (se 1 (by rfl) ⟨1765385, by rfl⟩ : syracuseStep 2353847 = 3530771) B3530771
theorem B11315933 : Blo 1568982 11315933 := bstep (se 3 (by rfl) ⟨2121737, by rfl⟩ : syracuseStep 11315933 = 4243475) B4243475
theorem B40258295 : Blo 1568982 40258295 := bstep (se 1 (by rfl) ⟨30193721, by rfl⟩ : syracuseStep 40258295 = 60387443) B60387443
theorem B1887031 : Blo 1568982 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B2354075 : Blo 1568982 2354075 := bstep (se 1 (by rfl) ⟨1765556, by rfl⟩ : syracuseStep 2354075 = 3531113) B3531113
theorem B3533723 : Blo 1568982 3533723 := bstep (se 1 (by rfl) ⟨2650292, by rfl⟩ : syracuseStep 3533723 = 5300585) B5300585
theorem B15084559 : Blo 1568982 15084559 := bstep (se 1 (by rfl) ⟨11313419, by rfl⟩ : syracuseStep 15084559 = 22626839) B22626839
theorem B3533921 : Blo 1568982 3533921 := bstep (se 2 (by rfl) ⟨1325220, by rfl⟩ : syracuseStep 3533921 = 2650441) B2650441
theorem B7949501 : Blo 1568982 7949501 := bstep (se 3 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 7949501 = 2981063) B2981063
theorem B3976391 : Blo 1568982 3976391 := bstep (se 1 (by rfl) ⟨2982293, by rfl⟩ : syracuseStep 3976391 = 5964587) B5964587
theorem B61992155 : Blo 1568982 61992155 := bstep (se 1 (by rfl) ⟨46494116, by rfl⟩ : syracuseStep 61992155 = 92988233) B92988233
theorem B2649307 : Blo 1568982 2649307 := bstep (se 1 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 2649307 = 3973961) B3973961
theorem B3976411 : Blo 1568982 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B3353833 : Blo 1568982 3353833 := bstep (se 2 (by rfl) ⟨1257687, by rfl⟩ : syracuseStep 3353833 = 2515375) B2515375
theorem B3771679 : Blo 1568982 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B2354471 : Blo 1568982 2354471 := bstep (se 1 (by rfl) ⟨1765853, by rfl⟩ : syracuseStep 2354471 = 3531707) B3531707
theorem B3534119 : Blo 1568982 3534119 := bstep (se 1 (by rfl) ⟨2650589, by rfl⟩ : syracuseStep 3534119 = 5301179) B5301179
theorem B22367549 : Blo 1568982 22367549 := bstep (se 3 (by rfl) ⟨4193915, by rfl⟩ : syracuseStep 22367549 = 8387831) B8387831
theorem B38169953 : Blo 1568982 38169953 := bstep (se 2 (by rfl) ⟨14313732, by rfl⟩ : syracuseStep 38169953 = 28627465) B28627465
theorem B5655905 : Blo 1568982 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B2354555 : Blo 1568982 2354555 := bstep (se 1 (by rfl) ⟨1765916, by rfl⟩ : syracuseStep 2354555 = 3531833) B3531833
theorem B14323073 : Blo 1568982 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B13413761 : Blo 1568982 13413761 := bstep (se 2 (by rfl) ⟨5030160, by rfl⟩ : syracuseStep 13413761 = 10060321) B10060321
theorem B16977397 : Blo 1568982 16977397 := bstep (se 5 (by rfl) ⟨795815, by rfl⟩ : syracuseStep 16977397 = 1591631) B1591631
theorem B2354681 : Blo 1568982 2354681 := bstep (se 2 (by rfl) ⟨883005, by rfl⟩ : syracuseStep 2354681 = 1766011) B1766011
theorem B2354783 : Blo 1568982 2354783 := bstep (se 1 (by rfl) ⟨1766087, by rfl⟩ : syracuseStep 2354783 = 3532175) B3532175
theorem B17198689 : Blo 1568982 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B3534497 : Blo 1568982 3534497 := bstep (se 2 (by rfl) ⟨1325436, by rfl⟩ : syracuseStep 3534497 = 2650873) B2650873
theorem B4083497 : Blo 1568982 4083497 := bstep (se 2 (by rfl) ⟨1531311, by rfl⟩ : syracuseStep 4083497 = 3062623) B3062623
theorem B3772217 : Blo 1568982 3772217 := bstep (se 2 (by rfl) ⟨1414581, by rfl⟩ : syracuseStep 3772217 = 2829163) B2829163
theorem B2354999 : Blo 1568982 2354999 := bstep (se 1 (by rfl) ⟨1766249, by rfl⟩ : syracuseStep 2354999 = 3532499) B3532499
theorem B21491513 : Blo 1568982 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B1986383 : Blo 1568982 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B16338797 : Blo 1568982 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B1765327 : Blo 1568982 1765327 := bstep (se 1 (by rfl) ⟨1323995, by rfl⟩ : syracuseStep 1765327 = 2647991) B2647991
theorem B2650063 : Blo 1568982 2650063 := bstep (se 1 (by rfl) ⟨1987547, by rfl⟩ : syracuseStep 2650063 = 3975095) B3975095
theorem B1986535 : Blo 1568982 1986535 := bstep (se 1 (by rfl) ⟨1489901, by rfl⟩ : syracuseStep 1986535 = 2979803) B2979803
theorem B34418749 : Blo 1568982 34418749 := bstep (se 3 (by rfl) ⟨6453515, by rfl⟩ : syracuseStep 34418749 = 12907031) B12907031
theorem B11317315 : Blo 1568982 11317315 := bstep (se 1 (by rfl) ⟨8487986, by rfl⟩ : syracuseStep 11317315 = 16975973) B16975973
theorem B11923523 : Blo 1568982 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B2355305 : Blo 1568982 2355305 := bstep (se 2 (by rfl) ⟨883239, by rfl⟩ : syracuseStep 2355305 = 1766479) B1766479
theorem B12079307 : Blo 1568982 12079307 := bstep (se 1 (by rfl) ⟨9059480, by rfl⟩ : syracuseStep 12079307 = 18118961) B18118961
theorem B1569055 : Blo 1568982 1569055 := bstep (se 1 (by rfl) ⟨1176791, by rfl⟩ : syracuseStep 1569055 = 2353583) B2353583
theorem B1569115 : Blo 1568982 1569115 := bstep (se 1 (by rfl) ⟨1176836, by rfl⟩ : syracuseStep 1569115 = 2353673) B2353673
theorem B1765723 : Blo 1568982 1765723 := bstep (se 1 (by rfl) ⟨1324292, by rfl⟩ : syracuseStep 1765723 = 2648585) B2648585
theorem B1569135 : Blo 1568982 1569135 := bstep (se 1 (by rfl) ⟨1176851, by rfl⟩ : syracuseStep 1569135 = 2353703) B2353703
theorem B1569191 : Blo 1568982 1569191 := bstep (se 1 (by rfl) ⟨1176893, by rfl⟩ : syracuseStep 1569191 = 2353787) B2353787
theorem B2355623 : Blo 1568982 2355623 := bstep (se 1 (by rfl) ⟨1766717, by rfl⟩ : syracuseStep 2355623 = 3533435) B3533435
theorem B1765831 : Blo 1568982 1765831 := bstep (se 1 (by rfl) ⟨1324373, by rfl⟩ : syracuseStep 1765831 = 2648747) B2648747
theorem B1569275 : Blo 1568982 1569275 := bstep (se 1 (by rfl) ⟨1176956, by rfl⟩ : syracuseStep 1569275 = 2353913) B2353913
theorem B2355707 : Blo 1568982 2355707 := bstep (se 1 (by rfl) ⟨1766780, by rfl⟩ : syracuseStep 2355707 = 3533561) B3533561
theorem B24154685 : Blo 1568982 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1569343 : Blo 1568982 1569343 := bstep (se 1 (by rfl) ⟨1177007, by rfl⟩ : syracuseStep 1569343 = 2354015) B2354015
theorem B1569351 : Blo 1568982 1569351 := bstep (se 1 (by rfl) ⟨1177013, by rfl⟩ : syracuseStep 1569351 = 2354027) B2354027
theorem B25457273 : Blo 1568982 25457273 := bstep (se 2 (by rfl) ⟨9546477, by rfl⟩ : syracuseStep 25457273 = 19092955) B19092955
theorem B2355833 : Blo 1568982 2355833 := bstep (se 2 (by rfl) ⟨883437, by rfl⟩ : syracuseStep 2355833 = 1766875) B1766875
theorem B2650745 : Blo 1568982 2650745 := bstep (se 2 (by rfl) ⟨994029, by rfl⟩ : syracuseStep 2650745 = 1988059) B1988059
theorem B2355887 : Blo 1568982 2355887 := bstep (se 1 (by rfl) ⟨1766915, by rfl⟩ : syracuseStep 2355887 = 3533831) B3533831
theorem B32207539 : Blo 1568982 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B2650799 : Blo 1568982 2650799 := bstep (se 1 (by rfl) ⟨1988099, by rfl⟩ : syracuseStep 2650799 = 3976199) B3976199
theorem B4469431 : Blo 1568982 4469431 := bstep (se 1 (by rfl) ⟨3352073, by rfl⟩ : syracuseStep 4469431 = 6704147) B6704147
theorem B1569503 : Blo 1568982 1569503 := bstep (se 1 (by rfl) ⟨1177127, by rfl⟩ : syracuseStep 1569503 = 2354255) B2354255
theorem B2355935 : Blo 1568982 2355935 := bstep (se 1 (by rfl) ⟨1766951, by rfl⟩ : syracuseStep 2355935 = 3533903) B3533903
theorem B7164715 : Blo 1568982 7164715 := bstep (se 1 (by rfl) ⟨5373536, by rfl⟩ : syracuseStep 7164715 = 10747073) B10747073
theorem B1569583 : Blo 1568982 1569583 := bstep (se 1 (by rfl) ⟨1177187, by rfl⟩ : syracuseStep 1569583 = 2354375) B2354375
theorem B1766191 : Blo 1568982 1766191 := bstep (se 1 (by rfl) ⟨1324643, by rfl⟩ : syracuseStep 1766191 = 2649287) B2649287
theorem B7943021 : Blo 1568982 7943021 := bstep (se 3 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 7943021 = 2978633) B2978633
theorem B1569691 : Blo 1568982 1569691 := bstep (se 1 (by rfl) ⟨1177268, by rfl⟩ : syracuseStep 1569691 = 2354537) B2354537
theorem B1766299 : Blo 1568982 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B11916233 : Blo 1568982 11916233 := bstep (se 2 (by rfl) ⟨4468587, by rfl⟩ : syracuseStep 11916233 = 8937175) B8937175
theorem B17888201 : Blo 1568982 17888201 := bstep (se 2 (by rfl) ⟨6708075, by rfl⟩ : syracuseStep 17888201 = 13416151) B13416151
theorem B1569743 : Blo 1568982 1569743 := bstep (se 1 (by rfl) ⟨1177307, by rfl⟩ : syracuseStep 1569743 = 2354615) B2354615
theorem B1569767 : Blo 1568982 1569767 := bstep (se 1 (by rfl) ⟨1177325, by rfl⟩ : syracuseStep 1569767 = 2354651) B2354651
theorem B2356199 : Blo 1568982 2356199 := bstep (se 1 (by rfl) ⟨1767149, by rfl⟩ : syracuseStep 2356199 = 3534299) B3534299
theorem B2356457 : Blo 1568982 2356457 := bstep (se 2 (by rfl) ⟨883671, by rfl⟩ : syracuseStep 2356457 = 1767343) B1767343
theorem B5027059 : Blo 1568982 5027059 := bstep (se 1 (by rfl) ⟨3770294, by rfl⟩ : syracuseStep 5027059 = 7540589) B7540589
theorem B1676575 : Blo 1568982 1676575 := bstep (se 1 (by rfl) ⟨1257431, by rfl⟩ : syracuseStep 1676575 = 2514863) B2514863
theorem B1570079 : Blo 1568982 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B1766695 : Blo 1568982 1766695 := bstep (se 1 (by rfl) ⟨1325021, by rfl⟩ : syracuseStep 1766695 = 2650043) B2650043
theorem B1570139 : Blo 1568982 1570139 := bstep (se 1 (by rfl) ⟨1177604, by rfl⟩ : syracuseStep 1570139 = 2355209) B2355209
theorem B1570159 : Blo 1568982 1570159 := bstep (se 1 (by rfl) ⟨1177619, by rfl⟩ : syracuseStep 1570159 = 2355239) B2355239
theorem B1766767 : Blo 1568982 1766767 := bstep (se 1 (by rfl) ⟨1325075, by rfl⟩ : syracuseStep 1766767 = 2650151) B2650151
theorem B1570215 : Blo 1568982 1570215 := bstep (se 1 (by rfl) ⟨1177661, by rfl⟩ : syracuseStep 1570215 = 2355323) B2355323
theorem B2979271 : Blo 1568982 2979271 := bstep (se 1 (by rfl) ⟨2234453, by rfl⟩ : syracuseStep 2979271 = 4468907) B4468907
theorem B1570299 : Blo 1568982 1570299 := bstep (se 1 (by rfl) ⟨1177724, by rfl⟩ : syracuseStep 1570299 = 2355449) B2355449
theorem B6706745 : Blo 1568982 6706745 := bstep (se 2 (by rfl) ⟨2515029, by rfl⟩ : syracuseStep 6706745 = 5030059) B5030059
theorem B1570367 : Blo 1568982 1570367 := bstep (se 1 (by rfl) ⟨1177775, by rfl⟩ : syracuseStep 1570367 = 2355551) B2355551
theorem B1570375 : Blo 1568982 1570375 := bstep (se 1 (by rfl) ⟨1177781, by rfl⟩ : syracuseStep 1570375 = 2355563) B2355563
theorem B1766983 : Blo 1568982 1766983 := bstep (se 1 (by rfl) ⟨1325237, by rfl⟩ : syracuseStep 1766983 = 2650475) B2650475
theorem B1570527 : Blo 1568982 1570527 := bstep (se 1 (by rfl) ⟨1177895, by rfl⟩ : syracuseStep 1570527 = 2355791) B2355791
theorem B1570607 : Blo 1568982 1570607 := bstep (se 1 (by rfl) ⟨1177955, by rfl⟩ : syracuseStep 1570607 = 2355911) B2355911
theorem B4241281 : Blo 1568982 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B1570715 : Blo 1568982 1570715 := bstep (se 1 (by rfl) ⟨1178036, by rfl⟩ : syracuseStep 1570715 = 2356073) B2356073
theorem B38205371 : Blo 1568982 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B1570767 : Blo 1568982 1570767 := bstep (se 1 (by rfl) ⟨1178075, by rfl⟩ : syracuseStep 1570767 = 2356151) B2356151
theorem B1570791 : Blo 1568982 1570791 := bstep (se 1 (by rfl) ⟨1178093, by rfl⟩ : syracuseStep 1570791 = 2356187) B2356187
theorem B5298209 : Blo 1568982 5298209 := bstep (se 2 (by rfl) ⟨1986828, by rfl⟩ : syracuseStep 5298209 = 3973657) B3973657
theorem B7952417 : Blo 1568982 7952417 := bstep (se 2 (by rfl) ⟨2982156, by rfl⟩ : syracuseStep 7952417 = 5964313) B5964313
theorem B7952579 : Blo 1568982 7952579 := bstep (se 1 (by rfl) ⟨5964434, by rfl⟩ : syracuseStep 7952579 = 11928869) B11928869
theorem B4241755 : Blo 1568982 4241755 := bstep (se 1 (by rfl) ⟨3181316, by rfl⟩ : syracuseStep 4241755 = 6362633) B6362633
theorem B3971663 : Blo 1568982 3971663 := bstep (se 1 (by rfl) ⟨2978747, by rfl⟩ : syracuseStep 3971663 = 5957495) B5957495
theorem B10058681 : Blo 1568982 10058681 := bstep (se 2 (by rfl) ⟨3772005, by rfl⟩ : syracuseStep 10058681 = 7544011) B7544011
theorem B3021799 : Blo 1568982 3021799 := bstep (se 1 (by rfl) ⟨2266349, by rfl⟩ : syracuseStep 3021799 = 4532699) B4532699
theorem B3972311 : Blo 1568982 3972311 := bstep (se 1 (by rfl) ⟨2979233, by rfl⟩ : syracuseStep 3972311 = 5958467) B5958467
theorem B7544125 : Blo 1568982 7544125 := bstep (se 3 (by rfl) ⟨1414523, by rfl⟩ : syracuseStep 7544125 = 2829047) B2829047
theorem B7544279 : Blo 1568982 7544279 := bstep (se 1 (by rfl) ⟨5658209, by rfl⟩ : syracuseStep 7544279 = 11316419) B11316419
theorem B4472279 : Blo 1568982 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B3972665 : Blo 1568982 3972665 := bstep (se 2 (by rfl) ⟨1489749, by rfl⟩ : syracuseStep 3972665 = 2979499) B2979499
theorem B7945937 : Blo 1568982 7945937 := bstep (se 2 (by rfl) ⟨2979726, by rfl⟩ : syracuseStep 7945937 = 5959453) B5959453
theorem B3530537 : Blo 1568982 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B2236367 : Blo 1568982 2236367 := bstep (se 1 (by rfl) ⟨1677275, by rfl⟩ : syracuseStep 2236367 = 3354551) B3354551
theorem B45891665 : Blo 1568982 45891665 := bstep (se 2 (by rfl) ⟨17209374, by rfl⟩ : syracuseStep 45891665 = 34418749) B34418749
theorem B15089753 : Blo 1568982 15089753 := bstep (se 2 (by rfl) ⟨5658657, by rfl⟩ : syracuseStep 15089753 = 11317315) B11317315
theorem B8052871 : Blo 1568982 8052871 := bstep (se 1 (by rfl) ⟨6039653, by rfl⟩ : syracuseStep 8052871 = 12079307) B12079307
theorem B7946747 : Blo 1568982 7946747 := bstep (se 1 (by rfl) ⟨5960060, by rfl⟩ : syracuseStep 7946747 = 11920121) B11920121
theorem B4473407 : Blo 1568982 4473407 := bstep (se 1 (by rfl) ⟨3355055, by rfl⟩ : syracuseStep 4473407 = 6710111) B6710111
theorem B27181763 : Blo 1568982 27181763 := bstep (se 1 (by rfl) ⟨20386322, by rfl⟩ : syracuseStep 27181763 = 40772645) B40772645
theorem B42943385 : Blo 1568982 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B9552953 : Blo 1568982 9552953 := bstep (se 2 (by rfl) ⟨3582357, by rfl⟩ : syracuseStep 9552953 = 7164715) B7164715
theorem B2516041 : Blo 1568982 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B4244687 : Blo 1568982 4244687 := bstep (se 1 (by rfl) ⟨3183515, by rfl⟩ : syracuseStep 4244687 = 6367031) B6367031
theorem B25470247 : Blo 1568982 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B20112745 : Blo 1568982 20112745 := bstep (se 2 (by rfl) ⟨7542279, by rfl⟩ : syracuseStep 20112745 = 15084559) B15084559
theorem B3532139 : Blo 1568982 3532139 := bstep (se 1 (by rfl) ⟨2649104, by rfl⟩ : syracuseStep 3532139 = 5298209) B5298209
theorem B5301611 : Blo 1568982 5301611 := bstep (se 1 (by rfl) ⟨3976208, by rfl⟩ : syracuseStep 5301611 = 7952417) B7952417
theorem B5301719 : Blo 1568982 5301719 := bstep (se 1 (by rfl) ⟨3976289, by rfl⟩ : syracuseStep 5301719 = 7952579) B7952579
theorem B3532409 : Blo 1568982 3532409 := bstep (se 2 (by rfl) ⟨1324653, by rfl⟩ : syracuseStep 3532409 = 2649307) B2649307
theorem B5301881 : Blo 1568982 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B6702745 : Blo 1568982 6702745 := bstep (se 2 (by rfl) ⟨2513529, by rfl⟩ : syracuseStep 6702745 = 5027059) B5027059
theorem B2647775 : Blo 1568982 2647775 := bstep (se 1 (by rfl) ⟨1985831, by rfl⟩ : syracuseStep 2647775 = 3971663) B3971663
theorem B26838863 : Blo 1568982 26838863 := bstep (se 1 (by rfl) ⟨20129147, by rfl⟩ : syracuseStep 26838863 = 40258295) B40258295
theorem B22636529 : Blo 1568982 22636529 := bstep (se 2 (by rfl) ⟨8488698, by rfl⟩ : syracuseStep 22636529 = 16977397) B16977397
theorem B22931585 : Blo 1568982 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B2648207 : Blo 1568982 2648207 := bstep (se 1 (by rfl) ⟨1986155, by rfl⟩ : syracuseStep 2648207 = 3972311) B3972311
theorem B14911699 : Blo 1568982 14911699 := bstep (se 1 (by rfl) ⟨11183774, by rfl⟩ : syracuseStep 14911699 = 22367549) B22367549
theorem B25446635 : Blo 1568982 25446635 := bstep (se 1 (by rfl) ⟨19084976, by rfl⟩ : syracuseStep 25446635 = 38169953) B38169953
theorem B3770603 : Blo 1568982 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B2648443 : Blo 1568982 2648443 := bstep (se 1 (by rfl) ⟨1986332, by rfl⟩ : syracuseStep 2648443 = 3972665) B3972665
theorem B5655041 : Blo 1568982 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B2353691 : Blo 1568982 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B2722331 : Blo 1568982 2722331 := bstep (se 1 (by rfl) ⟨2041748, by rfl⟩ : syracuseStep 2722331 = 4083497) B4083497
theorem B2353769 : Blo 1568982 2353769 := bstep (se 2 (by rfl) ⟨882663, by rfl⟩ : syracuseStep 2353769 = 1765327) B1765327
theorem B3533417 : Blo 1568982 3533417 := bstep (se 2 (by rfl) ⟨1325031, by rfl⟩ : syracuseStep 3533417 = 2650063) B2650063
theorem B2648713 : Blo 1568982 2648713 := bstep (se 2 (by rfl) ⟨993267, by rfl⟩ : syracuseStep 2648713 = 1986535) B1986535
theorem B17894033 : Blo 1568982 17894033 := bstep (se 2 (by rfl) ⟨6710262, by rfl⟩ : syracuseStep 17894033 = 13420525) B13420525
theorem B7949015 : Blo 1568982 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B1911643 : Blo 1568982 1911643 := bstep (se 1 (by rfl) ⟨1433732, by rfl⟩ : syracuseStep 1911643 = 2867465) B2867465
theorem B15084407 : Blo 1568982 15084407 := bstep (se 1 (by rfl) ⟨11313305, by rfl⟩ : syracuseStep 15084407 = 22626611) B22626611
theorem B5655673 : Blo 1568982 5655673 := bstep (se 2 (by rfl) ⟨2120877, by rfl⟩ : syracuseStep 5655673 = 4241755) B4241755
theorem B2354297 : Blo 1568982 2354297 := bstep (se 2 (by rfl) ⟨882861, by rfl⟩ : syracuseStep 2354297 = 1765723) B1765723
theorem B5368967 : Blo 1568982 5368967 := bstep (se 1 (by rfl) ⟨4026725, by rfl⟩ : syracuseStep 5368967 = 8053451) B8053451
theorem B2354399 : Blo 1568982 2354399 := bstep (se 1 (by rfl) ⟨1765799, by rfl⟩ : syracuseStep 2354399 = 3531599) B3531599
theorem B3534047 : Blo 1568982 3534047 := bstep (se 1 (by rfl) ⟨2650535, by rfl⟩ : syracuseStep 3534047 = 5301071) B5301071
theorem B5295347 : Blo 1568982 5295347 := bstep (se 1 (by rfl) ⟨3971510, by rfl⟩ : syracuseStep 5295347 = 7943021) B7943021
theorem B2354441 : Blo 1568982 2354441 := bstep (se 2 (by rfl) ⟨882915, by rfl⟩ : syracuseStep 2354441 = 1765831) B1765831
theorem B32206157 : Blo 1568982 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B2354543 : Blo 1568982 2354543 := bstep (se 1 (by rfl) ⟨1765907, by rfl⟩ : syracuseStep 2354543 = 3531815) B3531815
theorem B3534263 : Blo 1568982 3534263 := bstep (se 1 (by rfl) ⟨2650697, by rfl⟩ : syracuseStep 3534263 = 5301395) B5301395
theorem B2354663 : Blo 1568982 2354663 := bstep (se 1 (by rfl) ⟨1765997, by rfl⟩ : syracuseStep 2354663 = 3531995) B3531995
theorem B9547255 : Blo 1568982 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B5959241 : Blo 1568982 5959241 := bstep (se 2 (by rfl) ⟨2234715, by rfl⟩ : syracuseStep 5959241 = 4469431) B4469431
theorem B2354795 : Blo 1568982 2354795 := bstep (se 1 (by rfl) ⟨1766096, by rfl⟩ : syracuseStep 2354795 = 3532193) B3532193
theorem B3534443 : Blo 1568982 3534443 := bstep (se 1 (by rfl) ⟨2650832, by rfl⟩ : syracuseStep 3534443 = 5301665) B5301665
theorem B2354921 : Blo 1568982 2354921 := bstep (se 2 (by rfl) ⟨883095, by rfl⟩ : syracuseStep 2354921 = 1766191) B1766191
theorem B2355065 : Blo 1568982 2355065 := bstep (se 2 (by rfl) ⟨883149, by rfl⟩ : syracuseStep 2355065 = 1766299) B1766299
theorem B2355167 : Blo 1568982 2355167 := bstep (se 1 (by rfl) ⟨1766375, by rfl⟩ : syracuseStep 2355167 = 3532751) B3532751
theorem B2355419 : Blo 1568982 2355419 := bstep (se 1 (by rfl) ⟨1766564, by rfl⟩ : syracuseStep 2355419 = 3533129) B3533129
theorem B1568999 : Blo 1568982 1568999 := bstep (se 1 (by rfl) ⟨1176749, by rfl⟩ : syracuseStep 1568999 = 2353499) B2353499
theorem B2355431 : Blo 1568982 2355431 := bstep (se 1 (by rfl) ⟨1766573, by rfl⟩ : syracuseStep 2355431 = 3533147) B3533147
theorem B1569151 : Blo 1568982 1569151 := bstep (se 1 (by rfl) ⟨1176863, by rfl⟩ : syracuseStep 1569151 = 2353727) B2353727
theorem B1765759 : Blo 1568982 1765759 := bstep (se 1 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 1765759 = 2648639) B2648639
theorem B2650495 : Blo 1568982 2650495 := bstep (se 1 (by rfl) ⟨1987871, by rfl⟩ : syracuseStep 2650495 = 3975743) B3975743
theorem B2355593 : Blo 1568982 2355593 := bstep (se 2 (by rfl) ⟨883347, by rfl⟩ : syracuseStep 2355593 = 1766695) B1766695
theorem B1569231 : Blo 1568982 1569231 := bstep (se 1 (by rfl) ⟨1176923, by rfl⟩ : syracuseStep 1569231 = 2353847) B2353847
theorem B2355689 : Blo 1568982 2355689 := bstep (se 2 (by rfl) ⟨883383, by rfl⟩ : syracuseStep 2355689 = 1766767) B1766767
theorem B1569383 : Blo 1568982 1569383 := bstep (se 1 (by rfl) ⟨1177037, by rfl⟩ : syracuseStep 1569383 = 2354075) B2354075
theorem B2355815 : Blo 1568982 2355815 := bstep (se 1 (by rfl) ⟨1766861, by rfl⟩ : syracuseStep 2355815 = 3533723) B3533723
theorem B6705787 : Blo 1568982 6705787 := bstep (se 1 (by rfl) ⟨5029340, by rfl⟩ : syracuseStep 6705787 = 10058681) B10058681
theorem B2355947 : Blo 1568982 2355947 := bstep (se 1 (by rfl) ⟨1766960, by rfl⟩ : syracuseStep 2355947 = 3533921) B3533921
theorem B2355977 : Blo 1568982 2355977 := bstep (se 2 (by rfl) ⟨883491, by rfl⟩ : syracuseStep 2355977 = 1766983) B1766983
theorem B2650927 : Blo 1568982 2650927 := bstep (se 1 (by rfl) ⟨1988195, by rfl⟩ : syracuseStep 2650927 = 3976391) B3976391
theorem B1569647 : Blo 1568982 1569647 := bstep (se 1 (by rfl) ⟨1177235, by rfl⟩ : syracuseStep 1569647 = 2354471) B2354471
theorem B2356079 : Blo 1568982 2356079 := bstep (se 1 (by rfl) ⟨1767059, by rfl⟩ : syracuseStep 2356079 = 3534119) B3534119
theorem B5297021 : Blo 1568982 5297021 := bstep (se 3 (by rfl) ⟨993191, by rfl⟩ : syracuseStep 5297021 = 1986383) B1986383
theorem B1569703 : Blo 1568982 1569703 := bstep (se 1 (by rfl) ⟨1177277, by rfl⟩ : syracuseStep 1569703 = 2354555) B2354555
theorem B8942507 : Blo 1568982 8942507 := bstep (se 1 (by rfl) ⟨6706880, by rfl⟩ : syracuseStep 8942507 = 13413761) B13413761
theorem B1569787 : Blo 1568982 1569787 := bstep (se 1 (by rfl) ⟨1177340, by rfl⟩ : syracuseStep 1569787 = 2354681) B2354681
theorem B1569855 : Blo 1568982 1569855 := bstep (se 1 (by rfl) ⟨1177391, by rfl⟩ : syracuseStep 1569855 = 2354783) B2354783
theorem B2356331 : Blo 1568982 2356331 := bstep (se 1 (by rfl) ⟨1767248, by rfl⟩ : syracuseStep 2356331 = 3534497) B3534497
theorem B5297291 : Blo 1568982 5297291 := bstep (se 1 (by rfl) ⟨3972968, by rfl⟩ : syracuseStep 5297291 = 7945937) B7945937
theorem B1569999 : Blo 1568982 1569999 := bstep (se 1 (by rfl) ⟨1177499, by rfl⟩ : syracuseStep 1569999 = 2354999) B2354999
theorem B10892531 : Blo 1568982 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B1570203 : Blo 1568982 1570203 := bstep (se 1 (by rfl) ⟨1177652, by rfl⟩ : syracuseStep 1570203 = 2355305) B2355305
theorem B1570415 : Blo 1568982 1570415 := bstep (se 1 (by rfl) ⟨1177811, by rfl⟩ : syracuseStep 1570415 = 2355623) B2355623
theorem B1570471 : Blo 1568982 1570471 := bstep (se 1 (by rfl) ⟨1177853, by rfl⟩ : syracuseStep 1570471 = 2355707) B2355707
theorem B16103123 : Blo 1568982 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B16971515 : Blo 1568982 16971515 := bstep (se 1 (by rfl) ⟨12728636, by rfl⟩ : syracuseStep 16971515 = 25457273) B25457273
theorem B1570555 : Blo 1568982 1570555 := bstep (se 1 (by rfl) ⟨1177916, by rfl⟩ : syracuseStep 1570555 = 2355833) B2355833
theorem B1767163 : Blo 1568982 1767163 := bstep (se 1 (by rfl) ⟨1325372, by rfl⟩ : syracuseStep 1767163 = 2650745) B2650745
theorem B1570591 : Blo 1568982 1570591 := bstep (se 1 (by rfl) ⟨1177943, by rfl⟩ : syracuseStep 1570591 = 2355887) B2355887
theorem B1767199 : Blo 1568982 1767199 := bstep (se 1 (by rfl) ⟨1325399, by rfl⟩ : syracuseStep 1767199 = 2650799) B2650799
theorem B1570623 : Blo 1568982 1570623 := bstep (se 1 (by rfl) ⟨1177967, by rfl⟩ : syracuseStep 1570623 = 2355935) B2355935
theorem B165312413 : Blo 1568982 165312413 := bstep (se 3 (by rfl) ⟨30996077, by rfl⟩ : syracuseStep 165312413 = 61992155) B61992155
theorem B7944155 : Blo 1568982 7944155 := bstep (se 1 (by rfl) ⟨5958116, by rfl⟩ : syracuseStep 7944155 = 11916233) B11916233
theorem B11925467 : Blo 1568982 11925467 := bstep (se 1 (by rfl) ⟨8944100, by rfl⟩ : syracuseStep 11925467 = 17888201) B17888201
theorem B2234351 : Blo 1568982 2234351 := bstep (se 1 (by rfl) ⟨1675763, by rfl⟩ : syracuseStep 2234351 = 3351527) B3351527
theorem B1570799 : Blo 1568982 1570799 := bstep (se 1 (by rfl) ⟨1178099, by rfl⟩ : syracuseStep 1570799 = 2356199) B2356199
theorem B4773971 : Blo 1568982 4773971 := bstep (se 1 (by rfl) ⟨3580478, by rfl⟩ : syracuseStep 4773971 = 7160957) B7160957
theorem B4470889 : Blo 1568982 4470889 := bstep (se 2 (by rfl) ⟨1676583, by rfl⟩ : syracuseStep 4470889 = 3353167) B3353167
theorem B1570971 : Blo 1568982 1570971 := bstep (se 1 (by rfl) ⟨1178228, by rfl⟩ : syracuseStep 1570971 = 2356457) B2356457
theorem B11917691 : Blo 1568982 11917691 := bstep (se 1 (by rfl) ⟨8938268, by rfl⟩ : syracuseStep 11917691 = 17876537) B17876537
theorem B4471163 : Blo 1568982 4471163 := bstep (se 1 (by rfl) ⟨3353372, by rfl⟩ : syracuseStep 4471163 = 6706745) B6706745
theorem B20118077 : Blo 1568982 20118077 := bstep (se 3 (by rfl) ⟨3772139, by rfl⟩ : syracuseStep 20118077 = 7544279) B7544279
theorem B4029065 : Blo 1568982 4029065 := bstep (se 2 (by rfl) ⟨1510899, by rfl⟩ : syracuseStep 4029065 = 3021799) B3021799
theorem B20388509 : Blo 1568982 20388509 := bstep (se 3 (by rfl) ⟨3822845, by rfl⟩ : syracuseStep 20388509 = 7645691) B7645691
theorem B152779445 : Blo 1568982 152779445 := bstep (se 5 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 152779445 = 14323073) B14323073
theorem B45284021 : Blo 1568982 45284021 := bstep (se 5 (by rfl) ⟨2122688, by rfl⟩ : syracuseStep 45284021 = 4245377) B4245377
theorem B5298911 : Blo 1568982 5298911 := bstep (se 1 (by rfl) ⟨3974183, by rfl⟩ : syracuseStep 5298911 = 7948367) B7948367
theorem B3398483 : Blo 1568982 3398483 := bstep (se 1 (by rfl) ⟨2548862, by rfl⟩ : syracuseStep 3398483 = 5097725) B5097725
theorem B4471777 : Blo 1568982 4471777 := bstep (se 2 (by rfl) ⟨1676916, by rfl⟩ : syracuseStep 4471777 = 3353833) B3353833
theorem B5028905 : Blo 1568982 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B2235433 : Blo 1568982 2235433 := bstep (se 2 (by rfl) ⟨838287, by rfl⟩ : syracuseStep 2235433 = 1676575) B1676575
theorem B10058833 : Blo 1568982 10058833 := bstep (se 2 (by rfl) ⟨3772062, by rfl⟩ : syracuseStep 10058833 = 7544125) B7544125
theorem B11312243 : Blo 1568982 11312243 := bstep (se 1 (by rfl) ⟨8484182, by rfl⟩ : syracuseStep 11312243 = 16968365) B16968365
theorem B6708349 : Blo 1568982 6708349 := bstep (se 3 (by rfl) ⟨1257815, by rfl⟩ : syracuseStep 6708349 = 2515631) B2515631
theorem B4775041 : Blo 1568982 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B7543955 : Blo 1568982 7543955 := bstep (se 1 (by rfl) ⟨5657966, by rfl⟩ : syracuseStep 7543955 = 11315933) B11315933
theorem B3972361 : Blo 1568982 3972361 := bstep (se 2 (by rfl) ⟨1489635, by rfl⟩ : syracuseStep 3972361 = 2979271) B2979271
theorem B5299667 : Blo 1568982 5299667 := bstep (se 1 (by rfl) ⟨3974750, by rfl⟩ : syracuseStep 5299667 = 7949501) B7949501
theorem B20405857 : Blo 1568982 20405857 := bstep (se 2 (by rfl) ⟨7652196, by rfl⟩ : syracuseStep 20405857 = 15304393) B15304393
theorem B2981519 : Blo 1568982 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B3530465 : Blo 1568982 3530465 := bstep (se 2 (by rfl) ⟨1323924, by rfl⟩ : syracuseStep 3530465 = 2647849) B2647849
theorem B5299937 : Blo 1568982 5299937 := bstep (se 2 (by rfl) ⟨1987476, by rfl⟩ : syracuseStep 5299937 = 3974953) B3974953
theorem B2514811 : Blo 1568982 2514811 := bstep (se 1 (by rfl) ⟨1886108, by rfl⟩ : syracuseStep 2514811 = 3772217) B3772217
theorem B14327675 : Blo 1568982 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B5963645 : Blo 1568982 5963645 := bstep (se 3 (by rfl) ⟨1118183, by rfl⟩ : syracuseStep 5963645 = 2236367) B2236367
theorem B10059835 : Blo 1568982 10059835 := bstep (se 1 (by rfl) ⟨7544876, by rfl⟩ : syracuseStep 10059835 = 15089753) B15089753
theorem B19882265 : Blo 1568982 19882265 := bstep (se 2 (by rfl) ⟨7455849, by rfl⟩ : syracuseStep 19882265 = 14911699) B14911699
theorem B2982271 : Blo 1568982 2982271 := bstep (se 1 (by rfl) ⟨2236703, by rfl⟩ : syracuseStep 2982271 = 4473407) B4473407
theorem B13418885 : Blo 1568982 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B18121175 : Blo 1568982 18121175 := bstep (se 1 (by rfl) ⟨13590881, by rfl⟩ : syracuseStep 18121175 = 27181763) B27181763
theorem B3531257 : Blo 1568982 3531257 := bstep (se 2 (by rfl) ⟨1324221, by rfl⟩ : syracuseStep 3531257 = 2648443) B2648443
theorem B3531347 : Blo 1568982 3531347 := bstep (se 1 (by rfl) ⟨2648510, by rfl⟩ : syracuseStep 3531347 = 5297021) B5297021
theorem B3531527 : Blo 1568982 3531527 := bstep (se 1 (by rfl) ⟨2648645, by rfl⟩ : syracuseStep 3531527 = 5297291) B5297291
theorem B3531617 : Blo 1568982 3531617 := bstep (se 2 (by rfl) ⟨1324356, by rfl⟩ : syracuseStep 3531617 = 2648713) B2648713
theorem B11314343 : Blo 1568982 11314343 := bstep (se 1 (by rfl) ⟨8485757, by rfl⟩ : syracuseStep 11314343 = 16971515) B16971515
theorem B17892575 : Blo 1568982 17892575 := bstep (se 1 (by rfl) ⟨13419431, by rfl⟩ : syracuseStep 17892575 = 26838863) B26838863
theorem B110208275 : Blo 1568982 110208275 := bstep (se 1 (by rfl) ⟨82656206, by rfl⟩ : syracuseStep 110208275 = 165312413) B165312413
theorem B15091019 : Blo 1568982 15091019 := bstep (se 1 (by rfl) ⟨11318264, by rfl⟩ : syracuseStep 15091019 = 22636529) B22636529
theorem B15287723 : Blo 1568982 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B13411777 : Blo 1568982 13411777 := bstep (se 2 (by rfl) ⟨5029416, by rfl⟩ : syracuseStep 13411777 = 10058833) B10058833
theorem B3770027 : Blo 1568982 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B13412051 : Blo 1568982 13412051 := bstep (se 1 (by rfl) ⟨10059038, by rfl⟩ : syracuseStep 13412051 = 20118077) B20118077
theorem B11929355 : Blo 1568982 11929355 := bstep (se 1 (by rfl) ⟨8947016, by rfl⟩ : syracuseStep 11929355 = 17894033) B17894033
theorem B13592339 : Blo 1568982 13592339 := bstep (se 1 (by rfl) ⟨10194254, by rfl⟩ : syracuseStep 13592339 = 20388509) B20388509
theorem B101852963 : Blo 1568982 101852963 := bstep (se 1 (by rfl) ⟨76389722, by rfl⟩ : syracuseStep 101852963 = 152779445) B152779445
theorem B30189347 : Blo 1568982 30189347 := bstep (se 1 (by rfl) ⟨22642010, by rfl⟩ : syracuseStep 30189347 = 45284021) B45284021
theorem B3532607 : Blo 1568982 3532607 := bstep (se 1 (by rfl) ⟨2649455, by rfl⟩ : syracuseStep 3532607 = 5298911) B5298911
theorem B3352603 : Blo 1568982 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B27207809 : Blo 1568982 27207809 := bstep (se 2 (by rfl) ⟨10202928, by rfl⟩ : syracuseStep 27207809 = 20405857) B20405857
theorem B9062621 : Blo 1568982 9062621 := bstep (se 3 (by rfl) ⟨1699241, by rfl⟩ : syracuseStep 9062621 = 3398483) B3398483
theorem B3533111 : Blo 1568982 3533111 := bstep (se 1 (by rfl) ⟨2649833, by rfl⟩ : syracuseStep 3533111 = 5299667) B5299667
theorem B2353643 : Blo 1568982 2353643 := bstep (se 1 (by rfl) ⟨1765232, by rfl⟩ : syracuseStep 2353643 = 3530465) B3530465
theorem B3533291 : Blo 1568982 3533291 := bstep (se 1 (by rfl) ⟨2649968, by rfl⟩ : syracuseStep 3533291 = 5299937) B5299937
theorem B3353081 : Blo 1568982 3353081 := bstep (se 2 (by rfl) ⟨1257405, by rfl⟩ : syracuseStep 3353081 = 2514811) B2514811
theorem B3975763 : Blo 1568982 3975763 := bstep (se 1 (by rfl) ⟨2981822, by rfl⟩ : syracuseStep 3975763 = 5963645) B5963645
theorem B5958269 : Blo 1568982 5958269 := bstep (se 3 (by rfl) ⟨1117175, by rfl⟩ : syracuseStep 5958269 = 2234351) B2234351
theorem B2354345 : Blo 1568982 2354345 := bstep (se 2 (by rfl) ⟨882879, by rfl⟩ : syracuseStep 2354345 = 1765759) B1765759
theorem B3533993 : Blo 1568982 3533993 := bstep (se 2 (by rfl) ⟨1325247, by rfl⟩ : syracuseStep 3533993 = 2650495) B2650495
theorem B6368635 : Blo 1568982 6368635 := bstep (se 1 (by rfl) ⟨4776476, by rfl⟩ : syracuseStep 6368635 = 9552953) B9552953
theorem B2829791 : Blo 1568982 2829791 := bstep (se 1 (by rfl) ⟨2122343, by rfl⟩ : syracuseStep 2829791 = 4244687) B4244687
theorem B8941049 : Blo 1568982 8941049 := bstep (se 2 (by rfl) ⟨3352893, by rfl⟩ : syracuseStep 8941049 = 6705787) B6705787
theorem B7261687 : Blo 1568982 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B2354759 : Blo 1568982 2354759 := bstep (se 1 (by rfl) ⟨1766069, by rfl⟩ : syracuseStep 2354759 = 3532139) B3532139
theorem B3534407 : Blo 1568982 3534407 := bstep (se 1 (by rfl) ⟨2650805, by rfl⟩ : syracuseStep 3534407 = 5301611) B5301611
theorem B3534479 : Blo 1568982 3534479 := bstep (se 1 (by rfl) ⟨2650859, by rfl⟩ : syracuseStep 3534479 = 5301719) B5301719
theorem B3534569 : Blo 1568982 3534569 := bstep (se 2 (by rfl) ⟨1325463, by rfl⟩ : syracuseStep 3534569 = 2650927) B2650927
theorem B2354939 : Blo 1568982 2354939 := bstep (se 1 (by rfl) ⟨1766204, by rfl⟩ : syracuseStep 2354939 = 3532409) B3532409
theorem B3534587 : Blo 1568982 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B10735415 : Blo 1568982 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B1765183 : Blo 1568982 1765183 := bstep (se 1 (by rfl) ⟨1323887, by rfl⟩ : syracuseStep 1765183 = 2647775) B2647775
theorem B5296103 : Blo 1568982 5296103 := bstep (se 1 (by rfl) ⟨3972077, by rfl⟩ : syracuseStep 5296103 = 7944155) B7944155
theorem B7950311 : Blo 1568982 7950311 := bstep (se 1 (by rfl) ⟨5962733, by rfl⟩ : syracuseStep 7950311 = 11925467) B11925467
theorem B3182647 : Blo 1568982 3182647 := bstep (se 1 (by rfl) ⟨2386985, by rfl⟩ : syracuseStep 3182647 = 4773971) B4773971
theorem B1765471 : Blo 1568982 1765471 := bstep (se 1 (by rfl) ⟨1324103, by rfl⟩ : syracuseStep 1765471 = 2648207) B2648207
theorem B7540897 : Blo 1568982 7540897 := bstep (se 2 (by rfl) ⟨2827836, by rfl⟩ : syracuseStep 7540897 = 5655673) B5655673
theorem B5296481 : Blo 1568982 5296481 := bstep (se 2 (by rfl) ⟨1986180, by rfl⟩ : syracuseStep 5296481 = 3972361) B3972361
theorem B1569127 : Blo 1568982 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B1814887 : Blo 1568982 1814887 := bstep (se 1 (by rfl) ⟨1361165, by rfl⟩ : syracuseStep 1814887 = 2722331) B2722331
theorem B33960329 : Blo 1568982 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B1569179 : Blo 1568982 1569179 := bstep (se 1 (by rfl) ⟨1176884, by rfl⟩ : syracuseStep 1569179 = 2353769) B2353769
theorem B2355611 : Blo 1568982 2355611 := bstep (se 1 (by rfl) ⟨1766708, by rfl⟩ : syracuseStep 2355611 = 3533417) B3533417
theorem B26816993 : Blo 1568982 26816993 := bstep (se 2 (by rfl) ⟨10056372, by rfl⟩ : syracuseStep 26816993 = 20112745) B20112745
theorem B10195429 : Blo 1568982 10195429 := bstep (se 4 (by rfl) ⟨955821, by rfl⟩ : syracuseStep 10195429 = 1911643) B1911643
theorem B10056271 : Blo 1568982 10056271 := bstep (se 1 (by rfl) ⟨7542203, by rfl⟩ : syracuseStep 10056271 = 15084407) B15084407
theorem B7541495 : Blo 1568982 7541495 := bstep (se 1 (by rfl) ⟨5656121, by rfl⟩ : syracuseStep 7541495 = 11312243) B11312243
theorem B1569531 : Blo 1568982 1569531 := bstep (se 1 (by rfl) ⟨1177148, by rfl⟩ : syracuseStep 1569531 = 2354297) B2354297
theorem B1569599 : Blo 1568982 1569599 := bstep (se 1 (by rfl) ⟨1177199, by rfl⟩ : syracuseStep 1569599 = 2354399) B2354399
theorem B2356031 : Blo 1568982 2356031 := bstep (se 1 (by rfl) ⟨1767023, by rfl⟩ : syracuseStep 2356031 = 3534047) B3534047
theorem B1569627 : Blo 1568982 1569627 := bstep (se 1 (by rfl) ⟨1177220, by rfl⟩ : syracuseStep 1569627 = 2354441) B2354441
theorem B1569695 : Blo 1568982 1569695 := bstep (se 1 (by rfl) ⟨1177271, by rfl⟩ : syracuseStep 1569695 = 2354543) B2354543
theorem B2356175 : Blo 1568982 2356175 := bstep (se 1 (by rfl) ⟨1767131, by rfl⟩ : syracuseStep 2356175 = 3534263) B3534263
theorem B1569775 : Blo 1568982 1569775 := bstep (se 1 (by rfl) ⟨1177331, by rfl⟩ : syracuseStep 1569775 = 2354663) B2354663
theorem B2356217 : Blo 1568982 2356217 := bstep (se 2 (by rfl) ⟨883581, by rfl⟩ : syracuseStep 2356217 = 1767163) B1767163
theorem B2356265 : Blo 1568982 2356265 := bstep (se 2 (by rfl) ⟨883599, by rfl⟩ : syracuseStep 2356265 = 1767199) B1767199
theorem B1569863 : Blo 1568982 1569863 := bstep (se 1 (by rfl) ⟨1177397, by rfl⟩ : syracuseStep 1569863 = 2354795) B2354795
theorem B2356295 : Blo 1568982 2356295 := bstep (se 1 (by rfl) ⟨1767221, by rfl⟩ : syracuseStep 2356295 = 3534443) B3534443
theorem B1987679 : Blo 1568982 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B1569947 : Blo 1568982 1569947 := bstep (se 1 (by rfl) ⟨1177460, by rfl⟩ : syracuseStep 1569947 = 2354921) B2354921
theorem B1570043 : Blo 1568982 1570043 := bstep (se 1 (by rfl) ⟨1177532, by rfl⟩ : syracuseStep 1570043 = 2355065) B2355065
theorem B1570111 : Blo 1568982 1570111 := bstep (se 1 (by rfl) ⟨1177583, by rfl⟩ : syracuseStep 1570111 = 2355167) B2355167
theorem B30594443 : Blo 1568982 30594443 := bstep (se 1 (by rfl) ⟨22945832, by rfl⟩ : syracuseStep 30594443 = 45891665) B45891665
theorem B5961185 : Blo 1568982 5961185 := bstep (se 2 (by rfl) ⟨2235444, by rfl⟩ : syracuseStep 5961185 = 4470889) B4470889
theorem B1570279 : Blo 1568982 1570279 := bstep (se 1 (by rfl) ⟨1177709, by rfl⟩ : syracuseStep 1570279 = 2355419) B2355419
theorem B1570287 : Blo 1568982 1570287 := bstep (se 1 (by rfl) ⟨1177715, by rfl⟩ : syracuseStep 1570287 = 2355431) B2355431
theorem B10737161 : Blo 1568982 10737161 := bstep (se 2 (by rfl) ⟨4026435, by rfl⟩ : syracuseStep 10737161 = 8052871) B8052871
theorem B1570395 : Blo 1568982 1570395 := bstep (se 1 (by rfl) ⟨1177796, by rfl⟩ : syracuseStep 1570395 = 2355593) B2355593
theorem B1570459 : Blo 1568982 1570459 := bstep (se 1 (by rfl) ⟨1177844, by rfl⟩ : syracuseStep 1570459 = 2355689) B2355689
theorem B5297831 : Blo 1568982 5297831 := bstep (se 1 (by rfl) ⟨3973373, by rfl⟩ : syracuseStep 5297831 = 7946747) B7946747
theorem B1570543 : Blo 1568982 1570543 := bstep (se 1 (by rfl) ⟨1177907, by rfl⟩ : syracuseStep 1570543 = 2355815) B2355815
theorem B1570631 : Blo 1568982 1570631 := bstep (se 1 (by rfl) ⟨1177973, by rfl⟩ : syracuseStep 1570631 = 2355947) B2355947
theorem B1570651 : Blo 1568982 1570651 := bstep (se 1 (by rfl) ⟨1177988, by rfl⟩ : syracuseStep 1570651 = 2355977) B2355977
theorem B1570719 : Blo 1568982 1570719 := bstep (se 1 (by rfl) ⟨1178039, by rfl⟩ : syracuseStep 1570719 = 2356079) B2356079
theorem B5961671 : Blo 1568982 5961671 := bstep (se 1 (by rfl) ⟨4471253, by rfl⟩ : syracuseStep 5961671 = 8942507) B8942507
theorem B25466885 : Blo 1568982 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B1570887 : Blo 1568982 1570887 := bstep (se 1 (by rfl) ⟨1178165, by rfl⟩ : syracuseStep 1570887 = 2356331) B2356331
theorem B5962369 : Blo 1568982 5962369 := bstep (se 2 (by rfl) ⟨2235888, by rfl⟩ : syracuseStep 5962369 = 4471777) B4471777
theorem B2980577 : Blo 1568982 2980577 := bstep (se 2 (by rfl) ⟨1117716, by rfl⟩ : syracuseStep 2980577 = 2235433) B2235433
theorem B16964423 : Blo 1568982 16964423 := bstep (se 1 (by rfl) ⟨12723317, by rfl⟩ : syracuseStep 16964423 = 25446635) B25446635
theorem B2513735 : Blo 1568982 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B8944465 : Blo 1568982 8944465 := bstep (se 2 (by rfl) ⟨3354174, by rfl⟩ : syracuseStep 8944465 = 6708349) B6708349
theorem B7945127 : Blo 1568982 7945127 := bstep (se 1 (by rfl) ⟨5958845, by rfl⟩ : syracuseStep 7945127 = 11917691) B11917691
theorem B2980775 : Blo 1568982 2980775 := bstep (se 1 (by rfl) ⟨2235581, by rfl⟩ : syracuseStep 2980775 = 4471163) B4471163
theorem B2686043 : Blo 1568982 2686043 := bstep (se 1 (by rfl) ⟨2014532, by rfl⟩ : syracuseStep 2686043 = 4029065) B4029065
theorem B5299343 : Blo 1568982 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B12729673 : Blo 1568982 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B3579311 : Blo 1568982 3579311 := bstep (se 1 (by rfl) ⟨2684483, by rfl⟩ : syracuseStep 3579311 = 5368967) B5368967
theorem B5029303 : Blo 1568982 5029303 := bstep (se 1 (by rfl) ⟨3771977, by rfl⟩ : syracuseStep 5029303 = 7543955) B7543955
theorem B3530231 : Blo 1568982 3530231 := bstep (se 1 (by rfl) ⟨2647673, by rfl⟩ : syracuseStep 3530231 = 5295347) B5295347
theorem B8936993 : Blo 1568982 8936993 := bstep (se 2 (by rfl) ⟨3351372, by rfl⟩ : syracuseStep 8936993 = 6702745) B6702745
theorem B21470771 : Blo 1568982 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B3972827 : Blo 1568982 3972827 := bstep (se 1 (by rfl) ⟨2979620, by rfl⟩ : syracuseStep 3972827 = 5959241) B5959241
theorem B114515693 : Blo 1568982 114515693 := bstep (se 3 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 114515693 = 42943385) B42943385
theorem B9551783 : Blo 1568982 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B4243529 : Blo 1568982 4243529 := bstep (se 2 (by rfl) ⟨1591323, by rfl⟩ : syracuseStep 4243529 = 3182647) B3182647
theorem B3530987 : Blo 1568982 3530987 := bstep (se 1 (by rfl) ⟨2648240, by rfl⟩ : syracuseStep 3530987 = 5296481) B5296481
theorem B5300477 : Blo 1568982 5300477 := bstep (se 3 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 5300477 = 1987679) B1987679
theorem B8945923 : Blo 1568982 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B53019373 : Blo 1568982 53019373 := bstep (se 3 (by rfl) ⟨9941132, by rfl⟩ : syracuseStep 53019373 = 19882265) B19882265
theorem B5301017 : Blo 1568982 5301017 := bstep (se 2 (by rfl) ⟨1987881, by rfl⟩ : syracuseStep 5301017 = 3975763) B3975763
theorem B11928383 : Blo 1568982 11928383 := bstep (se 1 (by rfl) ⟨8946287, by rfl⟩ : syracuseStep 11928383 = 17892575) B17892575
theorem B10060679 : Blo 1568982 10060679 := bstep (se 1 (by rfl) ⟨7545509, by rfl⟩ : syracuseStep 10060679 = 15091019) B15091019
theorem B10191815 : Blo 1568982 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B3974123 : Blo 1568982 3974123 := bstep (se 1 (by rfl) ⟨2980592, by rfl⟩ : syracuseStep 3974123 = 5961185) B5961185
theorem B81585181 : Blo 1568982 81585181 := bstep (se 3 (by rfl) ⟨15297221, by rfl⟩ : syracuseStep 81585181 = 30594443) B30594443
theorem B3531887 : Blo 1568982 3531887 := bstep (se 1 (by rfl) ⟨2648915, by rfl⟩ : syracuseStep 3531887 = 5297831) B5297831
theorem B9061559 : Blo 1568982 9061559 := bstep (se 1 (by rfl) ⟨6796169, by rfl⟩ : syracuseStep 9061559 = 13592339) B13592339
theorem B3974447 : Blo 1568982 3974447 := bstep (se 1 (by rfl) ⟨2980835, by rfl⟩ : syracuseStep 3974447 = 5961671) B5961671
theorem B18138539 : Blo 1568982 18138539 := bstep (se 1 (by rfl) ⟨13603904, by rfl⟩ : syracuseStep 18138539 = 27207809) B27207809
theorem B7948205 : Blo 1568982 7948205 := bstep (se 3 (by rfl) ⟨1490288, by rfl⟩ : syracuseStep 7948205 = 2980577) B2980577
theorem B3532895 : Blo 1568982 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B2386207 : Blo 1568982 2386207 := bstep (se 1 (by rfl) ⟨1789655, by rfl⟩ : syracuseStep 2386207 = 3579311) B3579311
theorem B1886527 : Blo 1568982 1886527 := bstep (se 1 (by rfl) ⟨1414895, by rfl⟩ : syracuseStep 1886527 = 2829791) B2829791
theorem B2353487 : Blo 1568982 2353487 := bstep (se 1 (by rfl) ⟨1765115, by rfl⟩ : syracuseStep 2353487 = 3530231) B3530231
theorem B5957995 : Blo 1568982 5957995 := bstep (se 1 (by rfl) ⟨4468496, by rfl⟩ : syracuseStep 5957995 = 8936993) B8936993
theorem B14313847 : Blo 1568982 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B2353577 : Blo 1568982 2353577 := bstep (se 2 (by rfl) ⟨882591, by rfl⟩ : syracuseStep 2353577 = 1765183) B1765183
theorem B25471421 : Blo 1568982 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B2648551 : Blo 1568982 2648551 := bstep (se 1 (by rfl) ⟨1986413, by rfl⟩ : syracuseStep 2648551 = 3972827) B3972827
theorem B76343795 : Blo 1568982 76343795 := bstep (se 1 (by rfl) ⟨57257846, by rfl⟩ : syracuseStep 76343795 = 114515693) B114515693
theorem B13413113 : Blo 1568982 13413113 := bstep (se 2 (by rfl) ⟨5029917, by rfl⟩ : syracuseStep 13413113 = 10059835) B10059835
theorem B2353961 : Blo 1568982 2353961 := bstep (se 2 (by rfl) ⟨882735, by rfl⟩ : syracuseStep 2353961 = 1765471) B1765471
theorem B10054529 : Blo 1568982 10054529 := bstep (se 2 (by rfl) ⟨3770448, by rfl⟩ : syracuseStep 10054529 = 7540897) B7540897
theorem B17877995 : Blo 1568982 17877995 := bstep (se 1 (by rfl) ⟨13408496, by rfl⟩ : syracuseStep 17877995 = 26816993) B26816993
theorem B2354171 : Blo 1568982 2354171 := bstep (se 1 (by rfl) ⟨1765628, by rfl⟩ : syracuseStep 2354171 = 3531257) B3531257
theorem B2354231 : Blo 1568982 2354231 := bstep (se 1 (by rfl) ⟨1765673, by rfl⟩ : syracuseStep 2354231 = 3531347) B3531347
theorem B2419849 : Blo 1568982 2419849 := bstep (se 2 (by rfl) ⟨907443, by rfl⟩ : syracuseStep 2419849 = 1814887) B1814887
theorem B3976361 : Blo 1568982 3976361 := bstep (se 2 (by rfl) ⟨1491135, by rfl⟩ : syracuseStep 3976361 = 2982271) B2982271
theorem B2354351 : Blo 1568982 2354351 := bstep (se 1 (by rfl) ⟨1765763, by rfl⟩ : syracuseStep 2354351 = 3531527) B3531527
theorem B2354411 : Blo 1568982 2354411 := bstep (se 1 (by rfl) ⟨1765808, by rfl⟩ : syracuseStep 2354411 = 3531617) B3531617
theorem B13593905 : Blo 1568982 13593905 := bstep (se 2 (by rfl) ⟨5097714, by rfl⟩ : syracuseStep 13593905 = 10195429) B10195429
theorem B7949825 : Blo 1568982 7949825 := bstep (se 2 (by rfl) ⟨2981184, by rfl⟩ : syracuseStep 7949825 = 5962369) B5962369
theorem B8941367 : Blo 1568982 8941367 := bstep (se 1 (by rfl) ⟨6706025, by rfl⟩ : syracuseStep 8941367 = 13412051) B13412051
theorem B2355071 : Blo 1568982 2355071 := bstep (se 1 (by rfl) ⟨1766303, by rfl⟩ : syracuseStep 2355071 = 3532607) B3532607
theorem B8941549 : Blo 1568982 8941549 := bstep (se 3 (by rfl) ⟨1676540, by rfl⟩ : syracuseStep 8941549 = 3353081) B3353081
theorem B16977923 : Blo 1568982 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B6041747 : Blo 1568982 6041747 := bstep (se 1 (by rfl) ⟨4531310, by rfl⟩ : syracuseStep 6041747 = 9062621) B9062621
theorem B2355407 : Blo 1568982 2355407 := bstep (se 1 (by rfl) ⟨1766555, by rfl⟩ : syracuseStep 2355407 = 3533111) B3533111
theorem B1569095 : Blo 1568982 1569095 := bstep (se 1 (by rfl) ⟨1176821, by rfl⟩ : syracuseStep 1569095 = 2353643) B2353643
theorem B2355527 : Blo 1568982 2355527 := bstep (se 1 (by rfl) ⟨1766645, by rfl⟩ : syracuseStep 2355527 = 3533291) B3533291
theorem B8491513 : Blo 1568982 8491513 := bstep (se 2 (by rfl) ⟨3184317, by rfl⟩ : syracuseStep 8491513 = 6368635) B6368635
theorem B11309615 : Blo 1568982 11309615 := bstep (se 1 (by rfl) ⟨8482211, by rfl⟩ : syracuseStep 11309615 = 16964423) B16964423
theorem B1675823 : Blo 1568982 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B6705737 : Blo 1568982 6705737 := bstep (se 2 (by rfl) ⟨2514651, by rfl⟩ : syracuseStep 6705737 = 5029303) B5029303
theorem B5296751 : Blo 1568982 5296751 := bstep (se 1 (by rfl) ⟨3972563, by rfl⟩ : syracuseStep 5296751 = 7945127) B7945127
theorem B1987183 : Blo 1568982 1987183 := bstep (se 1 (by rfl) ⟨1490387, by rfl⟩ : syracuseStep 1987183 = 2980775) B2980775
theorem B1790695 : Blo 1568982 1790695 := bstep (se 1 (by rfl) ⟨1343021, by rfl⟩ : syracuseStep 1790695 = 2686043) B2686043
theorem B1569563 : Blo 1568982 1569563 := bstep (se 1 (by rfl) ⟨1177172, by rfl⟩ : syracuseStep 1569563 = 2354345) B2354345
theorem B2355995 : Blo 1568982 2355995 := bstep (se 1 (by rfl) ⟨1766996, by rfl⟩ : syracuseStep 2355995 = 3533993) B3533993
theorem B5960699 : Blo 1568982 5960699 := bstep (se 1 (by rfl) ⟨4470524, by rfl⟩ : syracuseStep 5960699 = 8941049) B8941049
theorem B1569839 : Blo 1568982 1569839 := bstep (se 1 (by rfl) ⟨1177379, by rfl⟩ : syracuseStep 1569839 = 2354759) B2354759
theorem B2356271 : Blo 1568982 2356271 := bstep (se 1 (by rfl) ⟨1767203, by rfl⟩ : syracuseStep 2356271 = 3534407) B3534407
theorem B2356319 : Blo 1568982 2356319 := bstep (se 1 (by rfl) ⟨1767239, by rfl⟩ : syracuseStep 2356319 = 3534479) B3534479
theorem B2356379 : Blo 1568982 2356379 := bstep (se 1 (by rfl) ⟨1767284, by rfl⟩ : syracuseStep 2356379 = 3534569) B3534569
theorem B1569959 : Blo 1568982 1569959 := bstep (se 1 (by rfl) ⟨1177469, by rfl⟩ : syracuseStep 1569959 = 2354939) B2354939
theorem B2356391 : Blo 1568982 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B7156943 : Blo 1568982 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B4470137 : Blo 1568982 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B22640219 : Blo 1568982 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B1570407 : Blo 1568982 1570407 := bstep (se 1 (by rfl) ⟨1177805, by rfl⟩ : syracuseStep 1570407 = 2355611) B2355611
theorem B12080783 : Blo 1568982 12080783 := bstep (se 1 (by rfl) ⟨9060587, by rfl⟩ : syracuseStep 12080783 = 18121175) B18121175
theorem B5027663 : Blo 1568982 5027663 := bstep (se 1 (by rfl) ⟨3770747, by rfl⟩ : syracuseStep 5027663 = 7541495) B7541495
theorem B1570687 : Blo 1568982 1570687 := bstep (se 1 (by rfl) ⟨1178015, by rfl⟩ : syracuseStep 1570687 = 2356031) B2356031
theorem B1570783 : Blo 1568982 1570783 := bstep (se 1 (by rfl) ⟨1178087, by rfl⟩ : syracuseStep 1570783 = 2356175) B2356175
theorem B1570811 : Blo 1568982 1570811 := bstep (se 1 (by rfl) ⟨1178108, by rfl⟩ : syracuseStep 1570811 = 2356217) B2356217
theorem B1570843 : Blo 1568982 1570843 := bstep (se 1 (by rfl) ⟨1178132, by rfl⟩ : syracuseStep 1570843 = 2356265) B2356265
theorem B1570863 : Blo 1568982 1570863 := bstep (se 1 (by rfl) ⟨1178147, by rfl⟩ : syracuseStep 1570863 = 2356295) B2356295
theorem B13408361 : Blo 1568982 13408361 := bstep (se 2 (by rfl) ⟨5028135, by rfl⟩ : syracuseStep 13408361 = 10056271) B10056271
theorem B7542895 : Blo 1568982 7542895 := bstep (se 1 (by rfl) ⟨5657171, by rfl⟩ : syracuseStep 7542895 = 11314343) B11314343
theorem B73472183 : Blo 1568982 73472183 := bstep (se 1 (by rfl) ⟨55104137, by rfl⟩ : syracuseStep 73472183 = 110208275) B110208275
theorem B7158107 : Blo 1568982 7158107 := bstep (se 1 (by rfl) ⟨5368580, by rfl⟩ : syracuseStep 7158107 = 10737161) B10737161
theorem B11925953 : Blo 1568982 11925953 := bstep (se 2 (by rfl) ⟨4472232, by rfl⟩ : syracuseStep 11925953 = 8944465) B8944465
theorem B2513351 : Blo 1568982 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B7952903 : Blo 1568982 7952903 := bstep (se 1 (by rfl) ⟨5964677, by rfl⟩ : syracuseStep 7952903 = 11929355) B11929355
theorem B67901975 : Blo 1568982 67901975 := bstep (se 1 (by rfl) ⟨50926481, by rfl⟩ : syracuseStep 67901975 = 101852963) B101852963
theorem B20126231 : Blo 1568982 20126231 := bstep (se 1 (by rfl) ⟨15094673, by rfl⟩ : syracuseStep 20126231 = 30189347) B30189347
theorem B3972179 : Blo 1568982 3972179 := bstep (se 1 (by rfl) ⟨2979134, by rfl⟩ : syracuseStep 3972179 = 5958269) B5958269
theorem B16972897 : Blo 1568982 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B17882369 : Blo 1568982 17882369 := bstep (se 2 (by rfl) ⟨6705888, by rfl⟩ : syracuseStep 17882369 = 13411777) B13411777
theorem B9682249 : Blo 1568982 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B3530735 : Blo 1568982 3530735 := bstep (se 1 (by rfl) ⟨2648051, by rfl⟩ : syracuseStep 3530735 = 5296103) B5296103
theorem B5300207 : Blo 1568982 5300207 := bstep (se 1 (by rfl) ⟨3975155, by rfl⟩ : syracuseStep 5300207 = 7950311) B7950311
theorem B11927897 : Blo 1568982 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B3531167 : Blo 1568982 3531167 := bstep (se 1 (by rfl) ⟨2648375, by rfl⟩ : syracuseStep 3531167 = 5296751) B5296751
theorem B2515369 : Blo 1568982 2515369 := bstep (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) B1886527
theorem B3531401 : Blo 1568982 3531401 := bstep (se 2 (by rfl) ⟨1324275, by rfl⟩ : syracuseStep 3531401 = 2648551) B2648551
theorem B11322017 : Blo 1568982 11322017 := bstep (se 2 (by rfl) ⟨4245756, by rfl⟩ : syracuseStep 11322017 = 8491513) B8491513
theorem B3973799 : Blo 1568982 3973799 := bstep (se 1 (by rfl) ⟨2980349, by rfl⟩ : syracuseStep 3973799 = 5960699) B5960699
theorem B12092359 : Blo 1568982 12092359 := bstep (se 1 (by rfl) ⟨9069269, by rfl⟩ : syracuseStep 12092359 = 18138539) B18138539
theorem B3351775 : Blo 1568982 3351775 := bstep (se 1 (by rfl) ⟨2513831, by rfl⟩ : syracuseStep 3351775 = 5027663) B5027663
theorem B8938907 : Blo 1568982 8938907 := bstep (se 1 (by rfl) ⟨6704180, by rfl⟩ : syracuseStep 8938907 = 13408361) B13408361
theorem B48981455 : Blo 1568982 48981455 := bstep (se 1 (by rfl) ⟨36736091, by rfl⟩ : syracuseStep 48981455 = 73472183) B73472183
theorem B5301935 : Blo 1568982 5301935 := bstep (se 1 (by rfl) ⟨3976451, by rfl⟩ : syracuseStep 5301935 = 7952903) B7952903
theorem B6703019 : Blo 1568982 6703019 := bstep (se 1 (by rfl) ⟨5027264, by rfl⟩ : syracuseStep 6703019 = 10054529) B10054529
theorem B2648119 : Blo 1568982 2648119 := bstep (se 1 (by rfl) ⟨1986089, by rfl⟩ : syracuseStep 2648119 = 3972179) B3972179
theorem B11921579 : Blo 1568982 11921579 := bstep (se 1 (by rfl) ⟨8941184, by rfl⟩ : syracuseStep 11921579 = 17882369) B17882369
theorem B9062603 : Blo 1568982 9062603 := bstep (se 1 (by rfl) ⟨6796952, by rfl⟩ : syracuseStep 9062603 = 13593905) B13593905
theorem B11922065 : Blo 1568982 11922065 := bstep (se 2 (by rfl) ⟨4470774, by rfl⟩ : syracuseStep 11922065 = 8941549) B8941549
theorem B2353823 : Blo 1568982 2353823 := bstep (se 1 (by rfl) ⟨1765367, by rfl⟩ : syracuseStep 2353823 = 3530735) B3530735
theorem B3533471 : Blo 1568982 3533471 := bstep (se 1 (by rfl) ⟨2650103, by rfl⟩ : syracuseStep 3533471 = 5300207) B5300207
theorem B2829019 : Blo 1568982 2829019 := bstep (se 1 (by rfl) ⟨2121764, by rfl⟩ : syracuseStep 2829019 = 4243529) B4243529
theorem B2353991 : Blo 1568982 2353991 := bstep (se 1 (by rfl) ⟨1765493, by rfl⟩ : syracuseStep 2353991 = 3530987) B3530987
theorem B3533651 : Blo 1568982 3533651 := bstep (se 1 (by rfl) ⟨2650238, by rfl⟩ : syracuseStep 3533651 = 5300477) B5300477
theorem B7539743 : Blo 1568982 7539743 := bstep (se 1 (by rfl) ⟨5654807, by rfl⟩ : syracuseStep 7539743 = 11309615) B11309615
theorem B3181609 : Blo 1568982 3181609 := bstep (se 2 (by rfl) ⟨1193103, by rfl⟩ : syracuseStep 3181609 = 2386207) B2386207
theorem B3534011 : Blo 1568982 3534011 := bstep (se 1 (by rfl) ⟨2650508, by rfl⟩ : syracuseStep 3534011 = 5301017) B5301017
theorem B6794543 : Blo 1568982 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B2649415 : Blo 1568982 2649415 := bstep (se 1 (by rfl) ⟨1987061, by rfl⟩ : syracuseStep 2649415 = 3974123) B3974123
theorem B2354591 : Blo 1568982 2354591 := bstep (se 1 (by rfl) ⟨1765943, by rfl⟩ : syracuseStep 2354591 = 3531887) B3531887
theorem B6041039 : Blo 1568982 6041039 := bstep (se 1 (by rfl) ⟨4530779, by rfl⟩ : syracuseStep 6041039 = 9061559) B9061559
theorem B4771295 : Blo 1568982 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B2649577 : Blo 1568982 2649577 := bstep (se 2 (by rfl) ⟨993591, by rfl⟩ : syracuseStep 2649577 = 1987183) B1987183
theorem B2649631 : Blo 1568982 2649631 := bstep (se 1 (by rfl) ⟨1987223, by rfl⟩ : syracuseStep 2649631 = 3974447) B3974447
theorem B2387593 : Blo 1568982 2387593 := bstep (se 2 (by rfl) ⟨895347, by rfl⟩ : syracuseStep 2387593 = 1790695) B1790695
theorem B70692497 : Blo 1568982 70692497 := bstep (se 2 (by rfl) ⟨26509686, by rfl⟩ : syracuseStep 70692497 = 53019373) B53019373
theorem B15093479 : Blo 1568982 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B2355263 : Blo 1568982 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B4468861 : Blo 1568982 4468861 := bstep (se 3 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 4468861 = 1675823) B1675823
theorem B22630529 : Blo 1568982 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B1568991 : Blo 1568982 1568991 := bstep (se 1 (by rfl) ⟨1176743, by rfl⟩ : syracuseStep 1568991 = 2353487) B2353487
theorem B4772071 : Blo 1568982 4772071 := bstep (se 1 (by rfl) ⟨3579053, by rfl⟩ : syracuseStep 4772071 = 7158107) B7158107
theorem B1569051 : Blo 1568982 1569051 := bstep (se 1 (by rfl) ⟨1176788, by rfl⟩ : syracuseStep 1569051 = 2353577) B2353577
theorem B7950635 : Blo 1568982 7950635 := bstep (se 1 (by rfl) ⟨5962976, by rfl⟩ : syracuseStep 7950635 = 11925953) B11925953
theorem B1675567 : Blo 1568982 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B32215421 : Blo 1568982 32215421 := bstep (se 3 (by rfl) ⟨6040391, by rfl⟩ : syracuseStep 32215421 = 12080783) B12080783
theorem B8942075 : Blo 1568982 8942075 := bstep (se 1 (by rfl) ⟨6706556, by rfl⟩ : syracuseStep 8942075 = 13413113) B13413113
theorem B1569307 : Blo 1568982 1569307 := bstep (se 1 (by rfl) ⟨1176980, by rfl⟩ : syracuseStep 1569307 = 2353961) B2353961
theorem B1569447 : Blo 1568982 1569447 := bstep (se 1 (by rfl) ⟨1177085, by rfl⟩ : syracuseStep 1569447 = 2354171) B2354171
theorem B1569487 : Blo 1568982 1569487 := bstep (se 1 (by rfl) ⟨1177115, by rfl⟩ : syracuseStep 1569487 = 2354231) B2354231
theorem B1569567 : Blo 1568982 1569567 := bstep (se 1 (by rfl) ⟨1177175, by rfl⟩ : syracuseStep 1569567 = 2354351) B2354351
theorem B2650907 : Blo 1568982 2650907 := bstep (se 1 (by rfl) ⟨1988180, by rfl⟩ : syracuseStep 2650907 = 3976361) B3976361
theorem B1569607 : Blo 1568982 1569607 := bstep (se 1 (by rfl) ⟨1177205, by rfl⟩ : syracuseStep 1569607 = 2354411) B2354411
theorem B5960911 : Blo 1568982 5960911 := bstep (se 1 (by rfl) ⟨4470683, by rfl⟩ : syracuseStep 5960911 = 8941367) B8941367
theorem B1570047 : Blo 1568982 1570047 := bstep (se 1 (by rfl) ⟨1177535, by rfl⟩ : syracuseStep 1570047 = 2355071) B2355071
theorem B11318615 : Blo 1568982 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B1570271 : Blo 1568982 1570271 := bstep (se 1 (by rfl) ⟨1177703, by rfl⟩ : syracuseStep 1570271 = 2355407) B2355407
theorem B10057193 : Blo 1568982 10057193 := bstep (se 2 (by rfl) ⟨3771447, by rfl⟩ : syracuseStep 10057193 = 7542895) B7542895
theorem B1570351 : Blo 1568982 1570351 := bstep (se 1 (by rfl) ⟨1177763, by rfl⟩ : syracuseStep 1570351 = 2355527) B2355527
theorem B4470491 : Blo 1568982 4470491 := bstep (se 1 (by rfl) ⟨3352868, by rfl⟩ : syracuseStep 4470491 = 6705737) B6705737
theorem B16111325 : Blo 1568982 16111325 := bstep (se 3 (by rfl) ⟨3020873, by rfl⟩ : syracuseStep 16111325 = 6041747) B6041747
theorem B7943993 : Blo 1568982 7943993 := bstep (se 2 (by rfl) ⟨2978997, by rfl⟩ : syracuseStep 7943993 = 5957995) B5957995
theorem B19085129 : Blo 1568982 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B1570663 : Blo 1568982 1570663 := bstep (se 1 (by rfl) ⟨1177997, by rfl⟩ : syracuseStep 1570663 = 2355995) B2355995
theorem B7952255 : Blo 1568982 7952255 := bstep (se 1 (by rfl) ⟨5964191, by rfl⟩ : syracuseStep 7952255 = 11928383) B11928383
theorem B6707119 : Blo 1568982 6707119 := bstep (se 1 (by rfl) ⟨5030339, by rfl⟩ : syracuseStep 6707119 = 10060679) B10060679
theorem B1570847 : Blo 1568982 1570847 := bstep (se 1 (by rfl) ⟨1178135, by rfl⟩ : syracuseStep 1570847 = 2356271) B2356271
theorem B1570879 : Blo 1568982 1570879 := bstep (se 1 (by rfl) ⟨1178159, by rfl⟩ : syracuseStep 1570879 = 2356319) B2356319
theorem B1570919 : Blo 1568982 1570919 := bstep (se 1 (by rfl) ⟨1178189, by rfl⟩ : syracuseStep 1570919 = 2356379) B2356379
theorem B1570927 : Blo 1568982 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B2980091 : Blo 1568982 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B5298803 : Blo 1568982 5298803 := bstep (se 1 (by rfl) ⟨3974102, by rfl⟩ : syracuseStep 5298803 = 7948205) B7948205
theorem B108780241 : Blo 1568982 108780241 := bstep (se 2 (by rfl) ⟨40792590, by rfl⟩ : syracuseStep 108780241 = 81585181) B81585181
theorem B3226465 : Blo 1568982 3226465 := bstep (se 2 (by rfl) ⟨1209924, by rfl⟩ : syracuseStep 3226465 = 2419849) B2419849
theorem B16980947 : Blo 1568982 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B50895863 : Blo 1568982 50895863 := bstep (se 1 (by rfl) ⟨38171897, by rfl⟩ : syracuseStep 50895863 = 76343795) B76343795
theorem B45267983 : Blo 1568982 45267983 := bstep (se 1 (by rfl) ⟨33950987, by rfl⟩ : syracuseStep 45267983 = 67901975) B67901975
theorem B13417487 : Blo 1568982 13417487 := bstep (se 1 (by rfl) ⟨10063115, by rfl⟩ : syracuseStep 13417487 = 20126231) B20126231
theorem B12909665 : Blo 1568982 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B11918663 : Blo 1568982 11918663 := bstep (se 1 (by rfl) ⟨8938997, by rfl⟩ : syracuseStep 11918663 = 17877995) B17877995
theorem B5299883 : Blo 1568982 5299883 := bstep (se 1 (by rfl) ⟨3974912, by rfl⟩ : syracuseStep 5299883 = 7949825) B7949825
theorem B3530825 : Blo 1568982 3530825 := bstep (se 2 (by rfl) ⟨1324059, by rfl⟩ : syracuseStep 3530825 = 2648119) B2648119
theorem B5300423 : Blo 1568982 5300423 := bstep (se 1 (by rfl) ⟨3975317, by rfl⟩ : syracuseStep 5300423 = 7950635) B7950635
theorem B7946909 : Blo 1568982 7946909 := bstep (se 3 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 7946909 = 2980091) B2980091
theorem B7545743 : Blo 1568982 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B145040321 : Blo 1568982 145040321 := bstep (se 2 (by rfl) ⟨54390120, by rfl⟩ : syracuseStep 145040321 = 108780241) B108780241
theorem B32654303 : Blo 1568982 32654303 := bstep (se 1 (by rfl) ⟨24490727, by rfl⟩ : syracuseStep 32654303 = 48981455) B48981455
theorem B4301953 : Blo 1568982 4301953 := bstep (se 2 (by rfl) ⟨1613232, by rfl⟩ : syracuseStep 4301953 = 3226465) B3226465
theorem B12723419 : Blo 1568982 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B5301503 : Blo 1568982 5301503 := bstep (se 1 (by rfl) ⟨3976127, by rfl⟩ : syracuseStep 5301503 = 7952255) B7952255
theorem B16123145 : Blo 1568982 16123145 := bstep (se 2 (by rfl) ⟨6046179, by rfl⟩ : syracuseStep 16123145 = 12092359) B12092359
theorem B7947719 : Blo 1568982 7947719 := bstep (se 1 (by rfl) ⟨5960789, by rfl⟩ : syracuseStep 7947719 = 11921579) B11921579
theorem B7947881 : Blo 1568982 7947881 := bstep (se 2 (by rfl) ⟨2980455, by rfl⟩ : syracuseStep 7947881 = 5960911) B5960911
theorem B3532535 : Blo 1568982 3532535 := bstep (se 1 (by rfl) ⟨2649401, by rfl⟩ : syracuseStep 3532535 = 5298803) B5298803
theorem B3532553 : Blo 1568982 3532553 := bstep (se 2 (by rfl) ⟨1324707, by rfl⟩ : syracuseStep 3532553 = 2649415) B2649415
theorem B7948043 : Blo 1568982 7948043 := bstep (se 1 (by rfl) ⟨5961032, by rfl⟩ : syracuseStep 7948043 = 11922065) B11922065
theorem B3532769 : Blo 1568982 3532769 := bstep (se 2 (by rfl) ⟨1324788, by rfl⟩ : syracuseStep 3532769 = 2649577) B2649577
theorem B3532841 : Blo 1568982 3532841 := bstep (se 2 (by rfl) ⟨1324815, by rfl⟩ : syracuseStep 3532841 = 2649631) B2649631
theorem B3180863 : Blo 1568982 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B3533255 : Blo 1568982 3533255 := bstep (se 1 (by rfl) ⟨2649941, by rfl⟩ : syracuseStep 3533255 = 5299883) B5299883
theorem B10062319 : Blo 1568982 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B20105981 : Blo 1568982 20105981 := bstep (se 3 (by rfl) ⟨3769871, by rfl⟩ : syracuseStep 20105981 = 7539743) B7539743
theorem B5958481 : Blo 1568982 5958481 := bstep (se 2 (by rfl) ⟨2234430, by rfl⟩ : syracuseStep 5958481 = 4468861) B4468861
theorem B34425773 : Blo 1568982 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B2354111 : Blo 1568982 2354111 := bstep (se 1 (by rfl) ⟨1765583, by rfl⟩ : syracuseStep 2354111 = 3531167) B3531167
theorem B2354267 : Blo 1568982 2354267 := bstep (se 1 (by rfl) ⟨1765700, by rfl⟩ : syracuseStep 2354267 = 3531401) B3531401
theorem B7548011 : Blo 1568982 7548011 := bstep (se 1 (by rfl) ⟨5661008, by rfl⟩ : syracuseStep 7548011 = 11322017) B11322017
theorem B2649199 : Blo 1568982 2649199 := bstep (se 1 (by rfl) ⟨1986899, by rfl⟩ : syracuseStep 2649199 = 3973799) B3973799
theorem B3353825 : Blo 1568982 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B5959271 : Blo 1568982 5959271 := bstep (se 1 (by rfl) ⟨4469453, by rfl⟩ : syracuseStep 5959271 = 8938907) B8938907
theorem B3772025 : Blo 1568982 3772025 := bstep (se 2 (by rfl) ⟨1414509, by rfl⟩ : syracuseStep 3772025 = 2829019) B2829019
theorem B6704795 : Blo 1568982 6704795 := bstep (se 1 (by rfl) ⟨5028596, by rfl⟩ : syracuseStep 6704795 = 10057193) B10057193
theorem B3534623 : Blo 1568982 3534623 := bstep (se 1 (by rfl) ⟨2650967, by rfl⟩ : syracuseStep 3534623 = 5301935) B5301935
theorem B5295995 : Blo 1568982 5295995 := bstep (se 1 (by rfl) ⟨3971996, by rfl⟩ : syracuseStep 5295995 = 7943993) B7943993
theorem B16109437 : Blo 1568982 16109437 := bstep (se 3 (by rfl) ⟨3020519, by rfl⟩ : syracuseStep 16109437 = 6041039) B6041039
theorem B4468679 : Blo 1568982 4468679 := bstep (se 1 (by rfl) ⟨3351509, by rfl⟩ : syracuseStep 4468679 = 6703019) B6703019
theorem B6041735 : Blo 1568982 6041735 := bstep (se 1 (by rfl) ⟨4531301, by rfl⟩ : syracuseStep 6041735 = 9062603) B9062603
theorem B4469033 : Blo 1568982 4469033 := bstep (se 2 (by rfl) ⟨1675887, by rfl⟩ : syracuseStep 4469033 = 3351775) B3351775
theorem B1569215 : Blo 1568982 1569215 := bstep (se 1 (by rfl) ⟨1176911, by rfl⟩ : syracuseStep 1569215 = 2353823) B2353823
theorem B2355647 : Blo 1568982 2355647 := bstep (se 1 (by rfl) ⟨1766735, by rfl⟩ : syracuseStep 2355647 = 3533471) B3533471
theorem B1569327 : Blo 1568982 1569327 := bstep (se 1 (by rfl) ⟨1176995, by rfl⟩ : syracuseStep 1569327 = 2353991) B2353991
theorem B2355767 : Blo 1568982 2355767 := bstep (se 1 (by rfl) ⟨1766825, by rfl⟩ : syracuseStep 2355767 = 3533651) B3533651
theorem B42963533 : Blo 1568982 42963533 := bstep (se 3 (by rfl) ⟨8055662, by rfl⟩ : syracuseStep 42963533 = 16111325) B16111325
theorem B2356007 : Blo 1568982 2356007 := bstep (se 1 (by rfl) ⟨1767005, by rfl⟩ : syracuseStep 2356007 = 3534011) B3534011
theorem B3183457 : Blo 1568982 3183457 := bstep (se 2 (by rfl) ⟨1193796, by rfl⟩ : syracuseStep 3183457 = 2387593) B2387593
theorem B1569727 : Blo 1568982 1569727 := bstep (se 1 (by rfl) ⟨1177295, by rfl⟩ : syracuseStep 1569727 = 2354591) B2354591
theorem B8942825 : Blo 1568982 8942825 := bstep (se 2 (by rfl) ⟨3353559, by rfl⟩ : syracuseStep 8942825 = 6707119) B6707119
theorem B1570175 : Blo 1568982 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B7951931 : Blo 1568982 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B6362761 : Blo 1568982 6362761 := bstep (se 2 (by rfl) ⟨2386035, by rfl⟩ : syracuseStep 6362761 = 4772071) B4772071
theorem B5961383 : Blo 1568982 5961383 := bstep (se 1 (by rfl) ⟨4471037, by rfl⟩ : syracuseStep 5961383 = 8942075) B8942075
theorem B60348077 : Blo 1568982 60348077 := bstep (se 3 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 60348077 = 22630529) B22630529
theorem B2234089 : Blo 1568982 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B1767271 : Blo 1568982 1767271 := bstep (se 1 (by rfl) ⟨1325453, by rfl⟩ : syracuseStep 1767271 = 2650907) B2650907
theorem B85907789 : Blo 1568982 85907789 := bstep (se 3 (by rfl) ⟨16107710, by rfl⟩ : syracuseStep 85907789 = 32215421) B32215421
theorem B2980327 : Blo 1568982 2980327 := bstep (se 1 (by rfl) ⟨2235245, by rfl⟩ : syracuseStep 2980327 = 4470491) B4470491
theorem B4242145 : Blo 1568982 4242145 := bstep (se 2 (by rfl) ⟨1590804, by rfl⟩ : syracuseStep 4242145 = 3181609) B3181609
theorem B11320631 : Blo 1568982 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B33930575 : Blo 1568982 33930575 := bstep (se 1 (by rfl) ⟨25447931, by rfl⟩ : syracuseStep 33930575 = 50895863) B50895863
theorem B30178655 : Blo 1568982 30178655 := bstep (se 1 (by rfl) ⟨22633991, by rfl⟩ : syracuseStep 30178655 = 45267983) B45267983
theorem B8944991 : Blo 1568982 8944991 := bstep (se 1 (by rfl) ⟨6708743, by rfl⟩ : syracuseStep 8944991 = 13417487) B13417487
theorem B4529695 : Blo 1568982 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B7945775 : Blo 1568982 7945775 := bstep (se 1 (by rfl) ⟨5959331, by rfl⟩ : syracuseStep 7945775 = 11918663) B11918663
theorem B47128331 : Blo 1568982 47128331 := bstep (se 1 (by rfl) ⟨35346248, by rfl⟩ : syracuseStep 47128331 = 70692497) B70692497
theorem B5030495 : Blo 1568982 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B3973769 : Blo 1568982 3973769 := bstep (se 2 (by rfl) ⟨1490163, by rfl⟩ : syracuseStep 3973769 = 2980327) B2980327
theorem B5301287 : Blo 1568982 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B3974255 : Blo 1568982 3974255 := bstep (se 1 (by rfl) ⟨2980691, by rfl⟩ : syracuseStep 3974255 = 5961383) B5961383
theorem B40232051 : Blo 1568982 40232051 := bstep (se 1 (by rfl) ⟨30174038, by rfl⟩ : syracuseStep 40232051 = 60348077) B60348077
theorem B4244609 : Blo 1568982 4244609 := bstep (se 2 (by rfl) ⟨1591728, by rfl⟩ : syracuseStep 4244609 = 3183457) B3183457
theorem B3532265 : Blo 1568982 3532265 := bstep (se 2 (by rfl) ⟨1324599, by rfl⟩ : syracuseStep 3532265 = 2649199) B2649199
theorem B57271859 : Blo 1568982 57271859 := bstep (se 1 (by rfl) ⟨42953894, by rfl⟩ : syracuseStep 57271859 = 85907789) B85907789
theorem B13403987 : Blo 1568982 13403987 := bstep (se 1 (by rfl) ⟨10052990, by rfl⟩ : syracuseStep 13403987 = 20105981) B20105981
theorem B6039593 : Blo 1568982 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B5032007 : Blo 1568982 5032007 := bstep (se 1 (by rfl) ⟨3774005, by rfl⟩ : syracuseStep 5032007 = 7548011) B7548011
theorem B7547087 : Blo 1568982 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B22620383 : Blo 1568982 22620383 := bstep (se 1 (by rfl) ⟨16965287, by rfl⟩ : syracuseStep 22620383 = 33930575) B33930575
theorem B31418887 : Blo 1568982 31418887 := bstep (se 1 (by rfl) ⟨23564165, by rfl⟩ : syracuseStep 31418887 = 47128331) B47128331
theorem B2353883 : Blo 1568982 2353883 := bstep (se 1 (by rfl) ⟨1765412, by rfl⟩ : syracuseStep 2353883 = 3530825) B3530825
theorem B3533615 : Blo 1568982 3533615 := bstep (se 1 (by rfl) ⟨2650211, by rfl⟩ : syracuseStep 3533615 = 5300423) B5300423
theorem B28642355 : Blo 1568982 28642355 := bstep (se 1 (by rfl) ⟨21481766, by rfl⟩ : syracuseStep 28642355 = 42963533) B42963533
theorem B96693547 : Blo 1568982 96693547 := bstep (se 1 (by rfl) ⟨72520160, by rfl⟩ : syracuseStep 96693547 = 145040321) B145040321
theorem B21769535 : Blo 1568982 21769535 := bstep (se 1 (by rfl) ⟨16327151, by rfl⟩ : syracuseStep 21769535 = 32654303) B32654303
theorem B42995053 : Blo 1568982 42995053 := bstep (se 3 (by rfl) ⟨8061572, by rfl⟩ : syracuseStep 42995053 = 16123145) B16123145
theorem B3534335 : Blo 1568982 3534335 := bstep (se 1 (by rfl) ⟨2650751, by rfl⟩ : syracuseStep 3534335 = 5301503) B5301503
theorem B5656193 : Blo 1568982 5656193 := bstep (se 2 (by rfl) ⟨2121072, by rfl⟩ : syracuseStep 5656193 = 4242145) B4242145
theorem B2355023 : Blo 1568982 2355023 := bstep (se 1 (by rfl) ⟨1766267, by rfl⟩ : syracuseStep 2355023 = 3532535) B3532535
theorem B2355035 : Blo 1568982 2355035 := bstep (se 1 (by rfl) ⟨1766276, by rfl⟩ : syracuseStep 2355035 = 3532553) B3532553
theorem B2355179 : Blo 1568982 2355179 := bstep (se 1 (by rfl) ⟨1766384, by rfl⟩ : syracuseStep 2355179 = 3532769) B3532769
theorem B2355227 : Blo 1568982 2355227 := bstep (se 1 (by rfl) ⟨1766420, by rfl⟩ : syracuseStep 2355227 = 3532841) B3532841
theorem B2355503 : Blo 1568982 2355503 := bstep (se 1 (by rfl) ⟨1766627, by rfl⟩ : syracuseStep 2355503 = 3533255) B3533255
theorem B17879453 : Blo 1568982 17879453 := bstep (se 3 (by rfl) ⟨3352397, by rfl⟩ : syracuseStep 17879453 = 6704795) B6704795
theorem B22950515 : Blo 1568982 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B1569407 : Blo 1568982 1569407 := bstep (se 1 (by rfl) ⟨1177055, by rfl⟩ : syracuseStep 1569407 = 2354111) B2354111
theorem B1569511 : Blo 1568982 1569511 := bstep (se 1 (by rfl) ⟨1177133, by rfl⟩ : syracuseStep 1569511 = 2354267) B2354267
theorem B8483681 : Blo 1568982 8483681 := bstep (se 2 (by rfl) ⟨3181380, by rfl⟩ : syracuseStep 8483681 = 6362761) B6362761
theorem B2978785 : Blo 1568982 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B5297183 : Blo 1568982 5297183 := bstep (se 1 (by rfl) ⟨3972887, by rfl⟩ : syracuseStep 5297183 = 7945775) B7945775
theorem B2356361 : Blo 1568982 2356361 := bstep (se 2 (by rfl) ⟨883635, by rfl⟩ : syracuseStep 2356361 = 1767271) B1767271
theorem B2356415 : Blo 1568982 2356415 := bstep (se 1 (by rfl) ⟨1767311, by rfl⟩ : syracuseStep 2356415 = 3534623) B3534623
theorem B2979119 : Blo 1568982 2979119 := bstep (se 1 (by rfl) ⟨2234339, by rfl⟩ : syracuseStep 2979119 = 4468679) B4468679
theorem B4027823 : Blo 1568982 4027823 := bstep (se 1 (by rfl) ⟨3020867, by rfl⟩ : syracuseStep 4027823 = 6041735) B6041735
theorem B2979355 : Blo 1568982 2979355 := bstep (se 1 (by rfl) ⟨2234516, by rfl⟩ : syracuseStep 2979355 = 4469033) B4469033
theorem B1570431 : Blo 1568982 1570431 := bstep (se 1 (by rfl) ⟨1177823, by rfl⟩ : syracuseStep 1570431 = 2355647) B2355647
theorem B1570511 : Blo 1568982 1570511 := bstep (se 1 (by rfl) ⟨1177883, by rfl⟩ : syracuseStep 1570511 = 2355767) B2355767
theorem B5297939 : Blo 1568982 5297939 := bstep (se 1 (by rfl) ⟨3973454, by rfl⟩ : syracuseStep 5297939 = 7946909) B7946909
theorem B1570671 : Blo 1568982 1570671 := bstep (se 1 (by rfl) ⟨1178003, by rfl⟩ : syracuseStep 1570671 = 2356007) B2356007
theorem B33929117 : Blo 1568982 33929117 := bstep (se 3 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 33929117 = 12723419) B12723419
theorem B8943533 : Blo 1568982 8943533 := bstep (se 3 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 8943533 = 3353825) B3353825
theorem B13416425 : Blo 1568982 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B22943749 : Blo 1568982 22943749 := bstep (se 4 (by rfl) ⟨2150976, by rfl⟩ : syracuseStep 22943749 = 4301953) B4301953
theorem B5961883 : Blo 1568982 5961883 := bstep (se 1 (by rfl) ⟨4471412, by rfl⟩ : syracuseStep 5961883 = 8942825) B8942825
theorem B5298479 : Blo 1568982 5298479 := bstep (se 1 (by rfl) ⟨3973859, by rfl⟩ : syracuseStep 5298479 = 7947719) B7947719
theorem B5298587 : Blo 1568982 5298587 := bstep (se 1 (by rfl) ⟨3973940, by rfl⟩ : syracuseStep 5298587 = 7947881) B7947881
theorem B7944641 : Blo 1568982 7944641 := bstep (se 2 (by rfl) ⟨2979240, by rfl⟩ : syracuseStep 7944641 = 5958481) B5958481
theorem B5298695 : Blo 1568982 5298695 := bstep (se 1 (by rfl) ⟨3974021, by rfl⟩ : syracuseStep 5298695 = 7948043) B7948043
theorem B2120575 : Blo 1568982 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B20119103 : Blo 1568982 20119103 := bstep (se 1 (by rfl) ⟨15089327, by rfl⟩ : syracuseStep 20119103 = 30178655) B30178655
theorem B5963327 : Blo 1568982 5963327 := bstep (se 1 (by rfl) ⟨4472495, by rfl⟩ : syracuseStep 5963327 = 8944991) B8944991
theorem B3972847 : Blo 1568982 3972847 := bstep (se 1 (by rfl) ⟨2979635, by rfl⟩ : syracuseStep 3972847 = 5959271) B5959271
theorem B2514683 : Blo 1568982 2514683 := bstep (se 1 (by rfl) ⟨1886012, by rfl⟩ : syracuseStep 2514683 = 3772025) B3772025
theorem B21479249 : Blo 1568982 21479249 := bstep (se 2 (by rfl) ⟨8054718, by rfl⟩ : syracuseStep 21479249 = 16109437) B16109437
theorem B3530663 : Blo 1568982 3530663 := bstep (se 1 (by rfl) ⟨2647997, by rfl⟩ : syracuseStep 3530663 = 5295995) B5295995
theorem B11919635 : Blo 1568982 11919635 := bstep (se 1 (by rfl) ⟨8939726, by rfl⟩ : syracuseStep 11919635 = 17879453) B17879453
theorem B3531455 : Blo 1568982 3531455 := bstep (se 1 (by rfl) ⟨2648591, by rfl⟩ : syracuseStep 3531455 = 5297183) B5297183
theorem B26821367 : Blo 1568982 26821367 := bstep (se 1 (by rfl) ⟨20116025, by rfl⟩ : syracuseStep 26821367 = 40232051) B40232051
theorem B2827433 : Blo 1568982 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B3531959 : Blo 1568982 3531959 := bstep (se 1 (by rfl) ⟨2648969, by rfl⟩ : syracuseStep 3531959 = 5297939) B5297939
theorem B22619411 : Blo 1568982 22619411 := bstep (se 1 (by rfl) ⟨16964558, by rfl⟩ : syracuseStep 22619411 = 33929117) B33929117
theorem B5031391 : Blo 1568982 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B3532319 : Blo 1568982 3532319 := bstep (se 1 (by rfl) ⟨2649239, by rfl⟩ : syracuseStep 3532319 = 5298479) B5298479
theorem B3532391 : Blo 1568982 3532391 := bstep (se 1 (by rfl) ⟨2649293, by rfl⟩ : syracuseStep 3532391 = 5298587) B5298587
theorem B3532463 : Blo 1568982 3532463 := bstep (se 1 (by rfl) ⟨2649347, by rfl⟩ : syracuseStep 3532463 = 5298695) B5298695
theorem B13412735 : Blo 1568982 13412735 := bstep (se 1 (by rfl) ⟨10059551, by rfl⟩ : syracuseStep 13412735 = 20119103) B20119103
theorem B3975551 : Blo 1568982 3975551 := bstep (se 1 (by rfl) ⟨2981663, by rfl⟩ : syracuseStep 3975551 = 5963327) B5963327
theorem B3770795 : Blo 1568982 3770795 := bstep (se 1 (by rfl) ⟨2828096, by rfl⟩ : syracuseStep 3770795 = 5656193) B5656193
theorem B2353775 : Blo 1568982 2353775 := bstep (se 1 (by rfl) ⟨1765331, by rfl⟩ : syracuseStep 2353775 = 3530663) B3530663
theorem B30591665 : Blo 1568982 30591665 := bstep (se 2 (by rfl) ⟨11471874, by rfl⟩ : syracuseStep 30591665 = 22943749) B22943749
theorem B7949177 : Blo 1568982 7949177 := bstep (se 2 (by rfl) ⟨2980941, by rfl⟩ : syracuseStep 7949177 = 5961883) B5961883
theorem B3353663 : Blo 1568982 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B2649179 : Blo 1568982 2649179 := bstep (se 1 (by rfl) ⟨1986884, by rfl⟩ : syracuseStep 2649179 = 3973769) B3973769
theorem B5655787 : Blo 1568982 5655787 := bstep (se 1 (by rfl) ⟨4241840, by rfl⟩ : syracuseStep 5655787 = 8483681) B8483681
theorem B3534191 : Blo 1568982 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B2649503 : Blo 1568982 2649503 := bstep (se 1 (by rfl) ⟨1987127, by rfl⟩ : syracuseStep 2649503 = 3974255) B3974255
theorem B2829739 : Blo 1568982 2829739 := bstep (se 1 (by rfl) ⟨2122304, by rfl⟩ : syracuseStep 2829739 = 4244609) B4244609
theorem B2354843 : Blo 1568982 2354843 := bstep (se 1 (by rfl) ⟨1766132, by rfl⟩ : syracuseStep 2354843 = 3532265) B3532265
theorem B4026395 : Blo 1568982 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B3354671 : Blo 1568982 3354671 := bstep (se 1 (by rfl) ⟨2516003, by rfl⟩ : syracuseStep 3354671 = 5032007) B5032007
theorem B5296427 : Blo 1568982 5296427 := bstep (se 1 (by rfl) ⟨3972320, by rfl⟩ : syracuseStep 5296427 = 7944641) B7944641
theorem B1569255 : Blo 1568982 1569255 := bstep (se 1 (by rfl) ⟨1176941, by rfl⟩ : syracuseStep 1569255 = 2353883) B2353883
theorem B2355743 : Blo 1568982 2355743 := bstep (se 1 (by rfl) ⟨1766807, by rfl⟩ : syracuseStep 2355743 = 3533615) B3533615
theorem B229306949 : Blo 1568982 229306949 := bstep (se 4 (by rfl) ⟨21497526, by rfl⟩ : syracuseStep 229306949 = 42995053) B42995053
theorem B6705821 : Blo 1568982 6705821 := bstep (se 3 (by rfl) ⟨1257341, by rfl⟩ : syracuseStep 6705821 = 2514683) B2514683
theorem B14513023 : Blo 1568982 14513023 := bstep (se 1 (by rfl) ⟨10884767, by rfl⟩ : syracuseStep 14513023 = 21769535) B21769535
theorem B5297129 : Blo 1568982 5297129 := bstep (se 2 (by rfl) ⟨1986423, by rfl⟩ : syracuseStep 5297129 = 3972847) B3972847
theorem B2356223 : Blo 1568982 2356223 := bstep (se 1 (by rfl) ⟨1767167, by rfl⟩ : syracuseStep 2356223 = 3534335) B3534335
theorem B1570015 : Blo 1568982 1570015 := bstep (se 1 (by rfl) ⟨1177511, by rfl⟩ : syracuseStep 1570015 = 2355023) B2355023
theorem B1570023 : Blo 1568982 1570023 := bstep (se 1 (by rfl) ⟨1177517, by rfl⟩ : syracuseStep 1570023 = 2355035) B2355035
theorem B1570119 : Blo 1568982 1570119 := bstep (se 1 (by rfl) ⟨1177589, by rfl⟩ : syracuseStep 1570119 = 2355179) B2355179
theorem B1570151 : Blo 1568982 1570151 := bstep (se 1 (by rfl) ⟨1177613, by rfl⟩ : syracuseStep 1570151 = 2355227) B2355227
theorem B1570335 : Blo 1568982 1570335 := bstep (se 1 (by rfl) ⟨1177751, by rfl⟩ : syracuseStep 1570335 = 2355503) B2355503
theorem B15300343 : Blo 1568982 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B41891849 : Blo 1568982 41891849 := bstep (se 2 (by rfl) ⟨15709443, by rfl⟩ : syracuseStep 41891849 = 31418887) B31418887
theorem B1570907 : Blo 1568982 1570907 := bstep (se 1 (by rfl) ⟨1178180, by rfl⟩ : syracuseStep 1570907 = 2356361) B2356361
theorem B7944317 : Blo 1568982 7944317 := bstep (se 3 (by rfl) ⟨1489559, by rfl⟩ : syracuseStep 7944317 = 2979119) B2979119
theorem B1570943 : Blo 1568982 1570943 := bstep (se 1 (by rfl) ⟨1178207, by rfl⟩ : syracuseStep 1570943 = 2356415) B2356415
theorem B2685215 : Blo 1568982 2685215 := bstep (se 1 (by rfl) ⟨2013911, by rfl⟩ : syracuseStep 2685215 = 4027823) B4027823
theorem B38181239 : Blo 1568982 38181239 := bstep (se 1 (by rfl) ⟨28635929, by rfl⟩ : syracuseStep 38181239 = 57271859) B57271859
theorem B8935991 : Blo 1568982 8935991 := bstep (se 1 (by rfl) ⟨6701993, by rfl⟩ : syracuseStep 8935991 = 13403987) B13403987
theorem B5962355 : Blo 1568982 5962355 := bstep (se 1 (by rfl) ⟨4471766, by rfl⟩ : syracuseStep 5962355 = 8943533) B8943533
theorem B3971713 : Blo 1568982 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B8944283 : Blo 1568982 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B15080255 : Blo 1568982 15080255 := bstep (se 1 (by rfl) ⟨11310191, by rfl⟩ : syracuseStep 15080255 = 22620383) B22620383
theorem B128924729 : Blo 1568982 128924729 := bstep (se 2 (by rfl) ⟨48346773, by rfl⟩ : syracuseStep 128924729 = 96693547) B96693547
theorem B19094903 : Blo 1568982 19094903 := bstep (se 1 (by rfl) ⟨14321177, by rfl⟩ : syracuseStep 19094903 = 28642355) B28642355
theorem B3972473 : Blo 1568982 3972473 := bstep (se 2 (by rfl) ⟨1489677, by rfl⟩ : syracuseStep 3972473 = 2979355) B2979355
theorem B14319499 : Blo 1568982 14319499 := bstep (se 1 (by rfl) ⟨10739624, by rfl⟩ : syracuseStep 14319499 = 21479249) B21479249
theorem B2236447 : Blo 1568982 2236447 := bstep (se 1 (by rfl) ⟨1677335, by rfl⟩ : syracuseStep 2236447 = 3354671) B3354671
theorem B7946423 : Blo 1568982 7946423 := bstep (se 1 (by rfl) ⟨5959817, by rfl⟩ : syracuseStep 7946423 = 11919635) B11919635
theorem B3530951 : Blo 1568982 3530951 := bstep (se 1 (by rfl) ⟨2648213, by rfl⟩ : syracuseStep 3530951 = 5296427) B5296427
theorem B152871299 : Blo 1568982 152871299 := bstep (se 1 (by rfl) ⟨114653474, by rfl⟩ : syracuseStep 152871299 = 229306949) B229306949
theorem B3531419 : Blo 1568982 3531419 := bstep (se 1 (by rfl) ⟨2648564, by rfl⟩ : syracuseStep 3531419 = 5297129) B5297129
theorem B1884955 : Blo 1568982 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B19350697 : Blo 1568982 19350697 := bstep (se 2 (by rfl) ⟨7256511, by rfl⟩ : syracuseStep 19350697 = 14513023) B14513023
theorem B30164197 : Blo 1568982 30164197 := bstep (se 4 (by rfl) ⟨2827893, by rfl⟩ : syracuseStep 30164197 = 5655787) B5655787
theorem B27927899 : Blo 1568982 27927899 := bstep (se 1 (by rfl) ⟨20945924, by rfl⟩ : syracuseStep 27927899 = 41891849) B41891849
theorem B25454159 : Blo 1568982 25454159 := bstep (se 1 (by rfl) ⟨19090619, by rfl⟩ : syracuseStep 25454159 = 38181239) B38181239
theorem B5957327 : Blo 1568982 5957327 := bstep (se 1 (by rfl) ⟨4467995, by rfl⟩ : syracuseStep 5957327 = 8935991) B8935991
theorem B3974903 : Blo 1568982 3974903 := bstep (se 1 (by rfl) ⟨2981177, by rfl⟩ : syracuseStep 3974903 = 5962355) B5962355
theorem B10053503 : Blo 1568982 10053503 := bstep (se 1 (by rfl) ⟨7540127, by rfl⟩ : syracuseStep 10053503 = 15080255) B15080255
theorem B2648315 : Blo 1568982 2648315 := bstep (se 1 (by rfl) ⟨1986236, by rfl⟩ : syracuseStep 2648315 = 3972473) B3972473
theorem B20400457 : Blo 1568982 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B2354303 : Blo 1568982 2354303 := bstep (se 1 (by rfl) ⟨1765727, by rfl⟩ : syracuseStep 2354303 = 3531455) B3531455
theorem B2354639 : Blo 1568982 2354639 := bstep (se 1 (by rfl) ⟨1765979, by rfl⟩ : syracuseStep 2354639 = 3531959) B3531959
theorem B5295617 : Blo 1568982 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B2354879 : Blo 1568982 2354879 := bstep (se 1 (by rfl) ⟨1766159, by rfl⟩ : syracuseStep 2354879 = 3532319) B3532319
theorem B2354927 : Blo 1568982 2354927 := bstep (se 1 (by rfl) ⟨1766195, by rfl⟩ : syracuseStep 2354927 = 3532391) B3532391
theorem B2354975 : Blo 1568982 2354975 := bstep (se 1 (by rfl) ⟨1766231, by rfl⟩ : syracuseStep 2354975 = 3532463) B3532463
theorem B5296211 : Blo 1568982 5296211 := bstep (se 1 (by rfl) ⟨3972158, by rfl⟩ : syracuseStep 5296211 = 7944317) B7944317
theorem B1790143 : Blo 1568982 1790143 := bstep (se 1 (by rfl) ⟨1342607, by rfl⟩ : syracuseStep 1790143 = 2685215) B2685215
theorem B8941823 : Blo 1568982 8941823 := bstep (se 1 (by rfl) ⟨6706367, by rfl⟩ : syracuseStep 8941823 = 13412735) B13412735
theorem B2650367 : Blo 1568982 2650367 := bstep (se 1 (by rfl) ⟨1987775, by rfl⟩ : syracuseStep 2650367 = 3975551) B3975551
theorem B1569183 : Blo 1568982 1569183 := bstep (se 1 (by rfl) ⟨1176887, by rfl⟩ : syracuseStep 1569183 = 2353775) B2353775
theorem B20394443 : Blo 1568982 20394443 := bstep (se 1 (by rfl) ⟨15295832, by rfl⟩ : syracuseStep 20394443 = 30591665) B30591665
theorem B3772985 : Blo 1568982 3772985 := bstep (se 2 (by rfl) ⟨1414869, by rfl⟩ : syracuseStep 3772985 = 2829739) B2829739
theorem B1766119 : Blo 1568982 1766119 := bstep (se 1 (by rfl) ⟨1324589, by rfl⟩ : syracuseStep 1766119 = 2649179) B2649179
theorem B2356127 : Blo 1568982 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B1766335 : Blo 1568982 1766335 := bstep (se 1 (by rfl) ⟨1324751, by rfl⟩ : syracuseStep 1766335 = 2649503) B2649503
theorem B1569895 : Blo 1568982 1569895 := bstep (se 1 (by rfl) ⟨1177421, by rfl⟩ : syracuseStep 1569895 = 2354843) B2354843
theorem B19092665 : Blo 1568982 19092665 := bstep (se 2 (by rfl) ⟨7159749, by rfl⟩ : syracuseStep 19092665 = 14319499) B14319499
theorem B2684263 : Blo 1568982 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B1570495 : Blo 1568982 1570495 := bstep (se 1 (by rfl) ⟨1177871, by rfl⟩ : syracuseStep 1570495 = 2355743) B2355743
theorem B4470547 : Blo 1568982 4470547 := bstep (se 1 (by rfl) ⟨3352910, by rfl⟩ : syracuseStep 4470547 = 6705821) B6705821
theorem B17880911 : Blo 1568982 17880911 := bstep (se 1 (by rfl) ⟨13410683, by rfl⟩ : syracuseStep 17880911 = 26821367) B26821367
theorem B1570815 : Blo 1568982 1570815 := bstep (se 1 (by rfl) ⟨1178111, by rfl⟩ : syracuseStep 1570815 = 2356223) B2356223
theorem B15079607 : Blo 1568982 15079607 := bstep (se 1 (by rfl) ⟨11309705, by rfl⟩ : syracuseStep 15079607 = 22619411) B22619411
theorem B2513863 : Blo 1568982 2513863 := bstep (se 1 (by rfl) ⟨1885397, by rfl⟩ : syracuseStep 2513863 = 3770795) B3770795
theorem B5962855 : Blo 1568982 5962855 := bstep (se 1 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 5962855 = 8944283) B8944283
theorem B5299451 : Blo 1568982 5299451 := bstep (se 1 (by rfl) ⟨3974588, by rfl⟩ : syracuseStep 5299451 = 7949177) B7949177
theorem B6708521 : Blo 1568982 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B85949819 : Blo 1568982 85949819 := bstep (se 1 (by rfl) ⟨64462364, by rfl⟩ : syracuseStep 85949819 = 128924729) B128924729
theorem B2235775 : Blo 1568982 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B12729935 : Blo 1568982 12729935 := bstep (se 1 (by rfl) ⟨9547451, by rfl⟩ : syracuseStep 12729935 = 19094903) B19094903
theorem B2981929 : Blo 1568982 2981929 := bstep (se 2 (by rfl) ⟨1118223, by rfl⟩ : syracuseStep 2981929 = 2236447) B2236447
theorem B3530807 : Blo 1568982 3530807 := bstep (se 1 (by rfl) ⟨2648105, by rfl⟩ : syracuseStep 3530807 = 5296211) B5296211
theorem B11920607 : Blo 1568982 11920607 := bstep (se 1 (by rfl) ⟨8940455, by rfl⟩ : syracuseStep 11920607 = 17880911) B17880911
theorem B6702335 : Blo 1568982 6702335 := bstep (se 1 (by rfl) ⟨5026751, by rfl⟩ : syracuseStep 6702335 = 10053503) B10053503
theorem B3351817 : Blo 1568982 3351817 := bstep (se 2 (by rfl) ⟨1256931, by rfl⟩ : syracuseStep 3351817 = 2513863) B2513863
theorem B10053071 : Blo 1568982 10053071 := bstep (se 1 (by rfl) ⟨7539803, by rfl⟩ : syracuseStep 10053071 = 15079607) B15079607
theorem B3532967 : Blo 1568982 3532967 := bstep (se 1 (by rfl) ⟨2649725, by rfl⟩ : syracuseStep 3532967 = 5299451) B5299451
theorem B2353967 : Blo 1568982 2353967 := bstep (se 1 (by rfl) ⟨1765475, by rfl⟩ : syracuseStep 2353967 = 3530951) B3530951
theorem B27200609 : Blo 1568982 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B2354279 : Blo 1568982 2354279 := bstep (se 1 (by rfl) ⟨1765709, by rfl⟩ : syracuseStep 2354279 = 3531419) B3531419
theorem B2354825 : Blo 1568982 2354825 := bstep (se 2 (by rfl) ⟨883059, by rfl⟩ : syracuseStep 2354825 = 1766119) B1766119
theorem B9547429 : Blo 1568982 9547429 := bstep (se 4 (by rfl) ⟨895071, by rfl⟩ : syracuseStep 9547429 = 1790143) B1790143
theorem B16969439 : Blo 1568982 16969439 := bstep (se 1 (by rfl) ⟨12727079, by rfl⟩ : syracuseStep 16969439 = 25454159) B25454159
theorem B2649935 : Blo 1568982 2649935 := bstep (se 1 (by rfl) ⟨1987451, by rfl⟩ : syracuseStep 2649935 = 3974903) B3974903
theorem B2355113 : Blo 1568982 2355113 := bstep (se 2 (by rfl) ⟨883167, by rfl⟩ : syracuseStep 2355113 = 1766335) B1766335
theorem B7950473 : Blo 1568982 7950473 := bstep (se 2 (by rfl) ⟨2981427, by rfl⟩ : syracuseStep 7950473 = 5962855) B5962855
theorem B1765543 : Blo 1568982 1765543 := bstep (se 1 (by rfl) ⟨1324157, by rfl⟩ : syracuseStep 1765543 = 2648315) B2648315
theorem B25800929 : Blo 1568982 25800929 := bstep (se 2 (by rfl) ⟨9675348, by rfl⟩ : syracuseStep 25800929 = 19350697) B19350697
theorem B40218929 : Blo 1568982 40218929 := bstep (se 2 (by rfl) ⟨15082098, by rfl⟩ : syracuseStep 40218929 = 30164197) B30164197
theorem B1569535 : Blo 1568982 1569535 := bstep (se 1 (by rfl) ⟨1177151, by rfl⟩ : syracuseStep 1569535 = 2354303) B2354303
theorem B57299879 : Blo 1568982 57299879 := bstep (se 1 (by rfl) ⟨42974909, by rfl⟩ : syracuseStep 57299879 = 85949819) B85949819
theorem B1569759 : Blo 1568982 1569759 := bstep (se 1 (by rfl) ⟨1177319, by rfl⟩ : syracuseStep 1569759 = 2354639) B2354639
theorem B5960729 : Blo 1568982 5960729 := bstep (se 2 (by rfl) ⟨2235273, by rfl⟩ : syracuseStep 5960729 = 4470547) B4470547
theorem B1569919 : Blo 1568982 1569919 := bstep (se 1 (by rfl) ⟨1177439, by rfl⟩ : syracuseStep 1569919 = 2354879) B2354879
theorem B1569951 : Blo 1568982 1569951 := bstep (se 1 (by rfl) ⟨1177463, by rfl⟩ : syracuseStep 1569951 = 2354927) B2354927
theorem B1569983 : Blo 1568982 1569983 := bstep (se 1 (by rfl) ⟨1177487, by rfl⟩ : syracuseStep 1569983 = 2354975) B2354975
theorem B5297615 : Blo 1568982 5297615 := bstep (se 1 (by rfl) ⟨3973211, by rfl⟩ : syracuseStep 5297615 = 7946423) B7946423
theorem B5961215 : Blo 1568982 5961215 := bstep (se 1 (by rfl) ⟨4470911, by rfl⟩ : syracuseStep 5961215 = 8941823) B8941823
theorem B1766911 : Blo 1568982 1766911 := bstep (se 1 (by rfl) ⟨1325183, by rfl⟩ : syracuseStep 1766911 = 2650367) B2650367
theorem B101914199 : Blo 1568982 101914199 := bstep (se 1 (by rfl) ⟨76435649, by rfl⟩ : syracuseStep 101914199 = 152871299) B152871299
theorem B13596295 : Blo 1568982 13596295 := bstep (se 1 (by rfl) ⟨10197221, by rfl⟩ : syracuseStep 13596295 = 20394443) B20394443
theorem B40245173 : Blo 1568982 40245173 := bstep (se 5 (by rfl) ⟨1886492, by rfl⟩ : syracuseStep 40245173 = 3772985) B3772985
theorem B1570751 : Blo 1568982 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B12728443 : Blo 1568982 12728443 := bstep (se 1 (by rfl) ⟨9546332, by rfl⟩ : syracuseStep 12728443 = 19092665) B19092665
theorem B18618599 : Blo 1568982 18618599 := bstep (se 1 (by rfl) ⟨13963949, by rfl⟩ : syracuseStep 18618599 = 27927899) B27927899
theorem B2513273 : Blo 1568982 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B3971551 : Blo 1568982 3971551 := bstep (se 1 (by rfl) ⟨2978663, by rfl⟩ : syracuseStep 3971551 = 5957327) B5957327
theorem B3579017 : Blo 1568982 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B2981033 : Blo 1568982 2981033 := bstep (se 2 (by rfl) ⟨1117887, by rfl⟩ : syracuseStep 2981033 = 2235775) B2235775
theorem B4472347 : Blo 1568982 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B3530411 : Blo 1568982 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B8486623 : Blo 1568982 8486623 := bstep (se 1 (by rfl) ⟨6364967, by rfl⟩ : syracuseStep 8486623 = 12729935) B12729935
theorem B5300315 : Blo 1568982 5300315 := bstep (se 1 (by rfl) ⟨3975236, by rfl⟩ : syracuseStep 5300315 = 7950473) B7950473
theorem B26812619 : Blo 1568982 26812619 := bstep (se 1 (by rfl) ⟨20109464, by rfl⟩ : syracuseStep 26812619 = 40218929) B40218929
theorem B38199919 : Blo 1568982 38199919 := bstep (se 1 (by rfl) ⟨28649939, by rfl⟩ : syracuseStep 38199919 = 57299879) B57299879
theorem B3973819 : Blo 1568982 3973819 := bstep (se 1 (by rfl) ⟨2980364, by rfl⟩ : syracuseStep 3973819 = 5960729) B5960729
theorem B7947071 : Blo 1568982 7947071 := bstep (se 1 (by rfl) ⟨5960303, by rfl⟩ : syracuseStep 7947071 = 11920607) B11920607
theorem B6702047 : Blo 1568982 6702047 := bstep (se 1 (by rfl) ⟨5026535, by rfl⟩ : syracuseStep 6702047 = 10053071) B10053071
theorem B3531743 : Blo 1568982 3531743 := bstep (se 1 (by rfl) ⟨2648807, by rfl⟩ : syracuseStep 3531743 = 5297615) B5297615
theorem B3974143 : Blo 1568982 3974143 := bstep (se 1 (by rfl) ⟨2980607, by rfl⟩ : syracuseStep 3974143 = 5961215) B5961215
theorem B26830115 : Blo 1568982 26830115 := bstep (se 1 (by rfl) ⟨20122586, by rfl⟩ : syracuseStep 26830115 = 40245173) B40245173
theorem B38176181 : Blo 1568982 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B12412399 : Blo 1568982 12412399 := bstep (se 1 (by rfl) ⟨9309299, by rfl⟩ : syracuseStep 12412399 = 18618599) B18618599
theorem B11315497 : Blo 1568982 11315497 := bstep (se 2 (by rfl) ⟨4243311, by rfl⟩ : syracuseStep 11315497 = 8486623) B8486623
theorem B2353607 : Blo 1568982 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B2353871 : Blo 1568982 2353871 := bstep (se 1 (by rfl) ⟨1765403, by rfl⟩ : syracuseStep 2353871 = 3530807) B3530807
theorem B3975905 : Blo 1568982 3975905 := bstep (se 2 (by rfl) ⟨1490964, by rfl⟩ : syracuseStep 3975905 = 2981929) B2981929
theorem B2354057 : Blo 1568982 2354057 := bstep (se 2 (by rfl) ⟨882771, by rfl⟩ : syracuseStep 2354057 = 1765543) B1765543
theorem B5295401 : Blo 1568982 5295401 := bstep (se 2 (by rfl) ⟨1985775, by rfl⟩ : syracuseStep 5295401 = 3971551) B3971551
theorem B4468223 : Blo 1568982 4468223 := bstep (se 1 (by rfl) ⟨3351167, by rfl⟩ : syracuseStep 4468223 = 6702335) B6702335
theorem B26808245 : Blo 1568982 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B2355311 : Blo 1568982 2355311 := bstep (se 1 (by rfl) ⟨1766483, by rfl⟩ : syracuseStep 2355311 = 3532967) B3532967
theorem B4469089 : Blo 1568982 4469089 := bstep (se 2 (by rfl) ⟨1675908, by rfl⟩ : syracuseStep 4469089 = 3351817) B3351817
theorem B1569311 : Blo 1568982 1569311 := bstep (se 1 (by rfl) ⟨1176983, by rfl⟩ : syracuseStep 1569311 = 2353967) B2353967
theorem B2355881 : Blo 1568982 2355881 := bstep (se 2 (by rfl) ⟨883455, by rfl⟩ : syracuseStep 2355881 = 1766911) B1766911
theorem B18133739 : Blo 1568982 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B1569519 : Blo 1568982 1569519 := bstep (se 1 (by rfl) ⟨1177139, by rfl⟩ : syracuseStep 1569519 = 2354279) B2354279
theorem B1987355 : Blo 1568982 1987355 := bstep (se 1 (by rfl) ⟨1490516, by rfl⟩ : syracuseStep 1987355 = 2981033) B2981033
theorem B1569883 : Blo 1568982 1569883 := bstep (se 1 (by rfl) ⟨1177412, by rfl⟩ : syracuseStep 1569883 = 2354825) B2354825
theorem B1766623 : Blo 1568982 1766623 := bstep (se 1 (by rfl) ⟨1324967, by rfl⟩ : syracuseStep 1766623 = 2649935) B2649935
theorem B1570075 : Blo 1568982 1570075 := bstep (se 1 (by rfl) ⟨1177556, by rfl⟩ : syracuseStep 1570075 = 2355113) B2355113
theorem B17200619 : Blo 1568982 17200619 := bstep (se 1 (by rfl) ⟨12900464, by rfl⟩ : syracuseStep 17200619 = 25800929) B25800929
theorem B16971257 : Blo 1568982 16971257 := bstep (se 2 (by rfl) ⟨6364221, by rfl⟩ : syracuseStep 16971257 = 12728443) B12728443
theorem B67942799 : Blo 1568982 67942799 := bstep (se 1 (by rfl) ⟨50957099, by rfl⟩ : syracuseStep 67942799 = 101914199) B101914199
theorem B5963129 : Blo 1568982 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B18128393 : Blo 1568982 18128393 := bstep (se 2 (by rfl) ⟨6798147, by rfl⟩ : syracuseStep 18128393 = 13596295) B13596295
theorem B12729905 : Blo 1568982 12729905 := bstep (se 2 (by rfl) ⟨4773714, by rfl⟩ : syracuseStep 12729905 = 9547429) B9547429
theorem B11312959 : Blo 1568982 11312959 := bstep (se 1 (by rfl) ⟨8484719, by rfl⟩ : syracuseStep 11312959 = 16969439) B16969439
theorem B17875079 : Blo 1568982 17875079 := bstep (se 1 (by rfl) ⟨13406309, by rfl⟩ : syracuseStep 17875079 = 26812619) B26812619
theorem B11314171 : Blo 1568982 11314171 := bstep (se 1 (by rfl) ⟨8485628, by rfl⟩ : syracuseStep 11314171 = 16971257) B16971257
theorem B45295199 : Blo 1568982 45295199 := bstep (se 1 (by rfl) ⟨33971399, by rfl⟩ : syracuseStep 45295199 = 67942799) B67942799
theorem B16549865 : Blo 1568982 16549865 := bstep (se 2 (by rfl) ⟨6206199, by rfl⟩ : syracuseStep 16549865 = 12412399) B12412399
theorem B3975419 : Blo 1568982 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B12085595 : Blo 1568982 12085595 := bstep (se 1 (by rfl) ⟨9064196, by rfl⟩ : syracuseStep 12085595 = 18128393) B18128393
theorem B15083945 : Blo 1568982 15083945 := bstep (se 2 (by rfl) ⟨5656479, by rfl⟩ : syracuseStep 15083945 = 11312959) B11312959
theorem B3533543 : Blo 1568982 3533543 := bstep (se 1 (by rfl) ⟨2650157, by rfl⟩ : syracuseStep 3533543 = 5300315) B5300315
theorem B5958785 : Blo 1568982 5958785 := bstep (se 2 (by rfl) ⟨2234544, by rfl⟩ : syracuseStep 5958785 = 4469089) B4469089
theorem B4468031 : Blo 1568982 4468031 := bstep (se 1 (by rfl) ⟨3351023, by rfl⟩ : syracuseStep 4468031 = 6702047) B6702047
theorem B2354495 : Blo 1568982 2354495 := bstep (se 1 (by rfl) ⟨1765871, by rfl⟩ : syracuseStep 2354495 = 3531743) B3531743
theorem B50933225 : Blo 1568982 50933225 := bstep (se 2 (by rfl) ⟨19099959, by rfl⟩ : syracuseStep 50933225 = 38199919) B38199919
theorem B17886743 : Blo 1568982 17886743 := bstep (se 1 (by rfl) ⟨13415057, by rfl⟩ : syracuseStep 17886743 = 26830115) B26830115
theorem B11915261 : Blo 1568982 11915261 := bstep (se 3 (by rfl) ⟨2234111, by rfl⟩ : syracuseStep 11915261 = 4468223) B4468223
theorem B2355497 : Blo 1568982 2355497 := bstep (se 2 (by rfl) ⟨883311, by rfl⟩ : syracuseStep 2355497 = 1766623) B1766623
theorem B1569071 : Blo 1568982 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B1569247 : Blo 1568982 1569247 := bstep (se 1 (by rfl) ⟨1176935, by rfl⟩ : syracuseStep 1569247 = 2353871) B2353871
theorem B2650603 : Blo 1568982 2650603 := bstep (se 1 (by rfl) ⟨1987952, by rfl⟩ : syracuseStep 2650603 = 3975905) B3975905
theorem B1569371 : Blo 1568982 1569371 := bstep (se 1 (by rfl) ⟨1177028, by rfl⟩ : syracuseStep 1569371 = 2354057) B2354057
theorem B17872163 : Blo 1568982 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B1570207 : Blo 1568982 1570207 := bstep (se 1 (by rfl) ⟨1177655, by rfl⟩ : syracuseStep 1570207 = 2355311) B2355311
theorem B15087329 : Blo 1568982 15087329 := bstep (se 2 (by rfl) ⟨5657748, by rfl⟩ : syracuseStep 15087329 = 11315497) B11315497
theorem B1570587 : Blo 1568982 1570587 := bstep (se 1 (by rfl) ⟨1177940, by rfl⟩ : syracuseStep 1570587 = 2355881) B2355881
theorem B12089159 : Blo 1568982 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B5298047 : Blo 1568982 5298047 := bstep (se 1 (by rfl) ⟨3973535, by rfl⟩ : syracuseStep 5298047 = 7947071) B7947071
theorem B5298425 : Blo 1568982 5298425 := bstep (se 2 (by rfl) ⟨1986909, by rfl⟩ : syracuseStep 5298425 = 3973819) B3973819
theorem B25450787 : Blo 1568982 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B11467079 : Blo 1568982 11467079 := bstep (se 1 (by rfl) ⟨8600309, by rfl⟩ : syracuseStep 11467079 = 17200619) B17200619
theorem B5298857 : Blo 1568982 5298857 := bstep (se 2 (by rfl) ⟨1987071, by rfl⟩ : syracuseStep 5298857 = 3974143) B3974143
theorem B5299613 : Blo 1568982 5299613 := bstep (se 3 (by rfl) ⟨993677, by rfl⟩ : syracuseStep 5299613 = 1987355) B1987355
theorem B3530267 : Blo 1568982 3530267 := bstep (se 1 (by rfl) ⟨2647700, by rfl⟩ : syracuseStep 3530267 = 5295401) B5295401
theorem B8486603 : Blo 1568982 8486603 := bstep (se 1 (by rfl) ⟨6364952, by rfl⟩ : syracuseStep 8486603 = 12729905) B12729905
theorem B30196799 : Blo 1568982 30196799 := bstep (se 1 (by rfl) ⟨22647599, by rfl⟩ : syracuseStep 30196799 = 45295199) B45295199
theorem B3532031 : Blo 1568982 3532031 := bstep (se 1 (by rfl) ⟨2649023, by rfl⟩ : syracuseStep 3532031 = 5298047) B5298047
theorem B3532283 : Blo 1568982 3532283 := bstep (se 1 (by rfl) ⟨2649212, by rfl⟩ : syracuseStep 3532283 = 5298425) B5298425
theorem B16967191 : Blo 1568982 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B7644719 : Blo 1568982 7644719 := bstep (se 1 (by rfl) ⟨5733539, by rfl⟩ : syracuseStep 7644719 = 11467079) B11467079
theorem B3532571 : Blo 1568982 3532571 := bstep (se 1 (by rfl) ⟨2649428, by rfl⟩ : syracuseStep 3532571 = 5298857) B5298857
theorem B3533075 : Blo 1568982 3533075 := bstep (se 1 (by rfl) ⟨2649806, by rfl⟩ : syracuseStep 3533075 = 5299613) B5299613
theorem B2353511 : Blo 1568982 2353511 := bstep (se 1 (by rfl) ⟨1765133, by rfl⟩ : syracuseStep 2353511 = 3530267) B3530267
theorem B3534137 : Blo 1568982 3534137 := bstep (se 2 (by rfl) ⟨1325301, by rfl⟩ : syracuseStep 3534137 = 2650603) B2650603
theorem B11914775 : Blo 1568982 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B15085561 : Blo 1568982 15085561 := bstep (se 2 (by rfl) ⟨5657085, by rfl⟩ : syracuseStep 15085561 = 11314171) B11314171
theorem B2650279 : Blo 1568982 2650279 := bstep (se 1 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 2650279 = 3975419) B3975419
theorem B8057063 : Blo 1568982 8057063 := bstep (se 1 (by rfl) ⟨6042797, by rfl⟩ : syracuseStep 8057063 = 12085595) B12085595
theorem B10055963 : Blo 1568982 10055963 := bstep (se 1 (by rfl) ⟨7541972, by rfl⟩ : syracuseStep 10055963 = 15083945) B15083945
theorem B2355695 : Blo 1568982 2355695 := bstep (se 1 (by rfl) ⟨1766771, by rfl⟩ : syracuseStep 2355695 = 3533543) B3533543
theorem B2978687 : Blo 1568982 2978687 := bstep (se 1 (by rfl) ⟨2234015, by rfl⟩ : syracuseStep 2978687 = 4468031) B4468031
theorem B1569663 : Blo 1568982 1569663 := bstep (se 1 (by rfl) ⟨1177247, by rfl⟩ : syracuseStep 1569663 = 2354495) B2354495
theorem B11924495 : Blo 1568982 11924495 := bstep (se 1 (by rfl) ⟨8943371, by rfl⟩ : syracuseStep 11924495 = 17886743) B17886743
theorem B5657735 : Blo 1568982 5657735 := bstep (se 1 (by rfl) ⟨4243301, by rfl⟩ : syracuseStep 5657735 = 8486603) B8486603
theorem B7943507 : Blo 1568982 7943507 := bstep (se 1 (by rfl) ⟨5957630, by rfl⟩ : syracuseStep 7943507 = 11915261) B11915261
theorem B11916719 : Blo 1568982 11916719 := bstep (se 1 (by rfl) ⟨8937539, by rfl⟩ : syracuseStep 11916719 = 17875079) B17875079
theorem B1570331 : Blo 1568982 1570331 := bstep (se 1 (by rfl) ⟨1177748, by rfl⟩ : syracuseStep 1570331 = 2355497) B2355497
theorem B10058219 : Blo 1568982 10058219 := bstep (se 1 (by rfl) ⟨7543664, by rfl⟩ : syracuseStep 10058219 = 15087329) B15087329
theorem B8059439 : Blo 1568982 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B11033243 : Blo 1568982 11033243 := bstep (se 1 (by rfl) ⟨8274932, by rfl⟩ : syracuseStep 11033243 = 16549865) B16549865
theorem B3972523 : Blo 1568982 3972523 := bstep (se 1 (by rfl) ⟨2979392, by rfl⟩ : syracuseStep 3972523 = 5958785) B5958785
theorem B33955483 : Blo 1568982 33955483 := bstep (se 1 (by rfl) ⟨25466612, by rfl⟩ : syracuseStep 33955483 = 50933225) B50933225
theorem B20114081 : Blo 1568982 20114081 := bstep (se 2 (by rfl) ⟨7542780, by rfl⟩ : syracuseStep 20114081 = 15085561) B15085561
theorem B6703975 : Blo 1568982 6703975 := bstep (se 1 (by rfl) ⟨5027981, by rfl⟩ : syracuseStep 6703975 = 10055963) B10055963
theorem B3533705 : Blo 1568982 3533705 := bstep (se 2 (by rfl) ⟨1325139, by rfl⟩ : syracuseStep 3533705 = 2650279) B2650279
theorem B1985791 : Blo 1568982 1985791 := bstep (se 1 (by rfl) ⟨1489343, by rfl⟩ : syracuseStep 1985791 = 2978687) B2978687
theorem B7949663 : Blo 1568982 7949663 := bstep (se 1 (by rfl) ⟨5962247, by rfl⟩ : syracuseStep 7949663 = 11924495) B11924495
theorem B20131199 : Blo 1568982 20131199 := bstep (se 1 (by rfl) ⟨15098399, by rfl⟩ : syracuseStep 20131199 = 30196799) B30196799
theorem B2354687 : Blo 1568982 2354687 := bstep (se 1 (by rfl) ⟨1766015, by rfl⟩ : syracuseStep 2354687 = 3532031) B3532031
theorem B5295671 : Blo 1568982 5295671 := bstep (se 1 (by rfl) ⟨3971753, by rfl⟩ : syracuseStep 5295671 = 7943507) B7943507
theorem B2354855 : Blo 1568982 2354855 := bstep (se 1 (by rfl) ⟨1766141, by rfl⟩ : syracuseStep 2354855 = 3532283) B3532283
theorem B2355047 : Blo 1568982 2355047 := bstep (se 1 (by rfl) ⟨1766285, by rfl⟩ : syracuseStep 2355047 = 3532571) B3532571
theorem B20385917 : Blo 1568982 20385917 := bstep (se 3 (by rfl) ⟨3822359, by rfl⟩ : syracuseStep 20385917 = 7644719) B7644719
theorem B2355383 : Blo 1568982 2355383 := bstep (se 1 (by rfl) ⟨1766537, by rfl⟩ : syracuseStep 2355383 = 3533075) B3533075
theorem B1569007 : Blo 1568982 1569007 := bstep (se 1 (by rfl) ⟨1176755, by rfl⟩ : syracuseStep 1569007 = 2353511) B2353511
theorem B6705479 : Blo 1568982 6705479 := bstep (se 1 (by rfl) ⟨5029109, by rfl⟩ : syracuseStep 6705479 = 10058219) B10058219
theorem B5296697 : Blo 1568982 5296697 := bstep (se 2 (by rfl) ⟨1986261, by rfl⟩ : syracuseStep 5296697 = 3972523) B3972523
theorem B22622921 : Blo 1568982 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B45273977 : Blo 1568982 45273977 := bstep (se 2 (by rfl) ⟨16977741, by rfl⟩ : syracuseStep 45273977 = 33955483) B33955483
theorem B2356091 : Blo 1568982 2356091 := bstep (se 1 (by rfl) ⟨1767068, by rfl⟩ : syracuseStep 2356091 = 3534137) B3534137
theorem B7943183 : Blo 1568982 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B5371375 : Blo 1568982 5371375 := bstep (se 1 (by rfl) ⟨4028531, by rfl⟩ : syracuseStep 5371375 = 8057063) B8057063
theorem B1570463 : Blo 1568982 1570463 := bstep (se 1 (by rfl) ⟨1177847, by rfl⟩ : syracuseStep 1570463 = 2355695) B2355695
theorem B15087293 : Blo 1568982 15087293 := bstep (se 3 (by rfl) ⟨2828867, by rfl⟩ : syracuseStep 15087293 = 5657735) B5657735
theorem B7944479 : Blo 1568982 7944479 := bstep (se 1 (by rfl) ⟨5958359, by rfl⟩ : syracuseStep 7944479 = 11916719) B11916719
theorem B5372959 : Blo 1568982 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B7355495 : Blo 1568982 7355495 := bstep (se 1 (by rfl) ⟨5516621, by rfl⟩ : syracuseStep 7355495 = 11033243) B11033243
theorem B13590611 : Blo 1568982 13590611 := bstep (se 1 (by rfl) ⟨10192958, by rfl⟩ : syracuseStep 13590611 = 20385917) B20385917
theorem B3531131 : Blo 1568982 3531131 := bstep (se 1 (by rfl) ⟨2648348, by rfl⟩ : syracuseStep 3531131 = 5296697) B5296697
theorem B15081947 : Blo 1568982 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B8938633 : Blo 1568982 8938633 := bstep (se 2 (by rfl) ⟨3351987, by rfl⟩ : syracuseStep 8938633 = 6703975) B6703975
theorem B2647721 : Blo 1568982 2647721 := bstep (se 2 (by rfl) ⟨992895, by rfl⟩ : syracuseStep 2647721 = 1985791) B1985791
theorem B7161833 : Blo 1568982 7161833 := bstep (se 2 (by rfl) ⟨2685687, by rfl⟩ : syracuseStep 7161833 = 5371375) B5371375
theorem B13420799 : Blo 1568982 13420799 := bstep (se 1 (by rfl) ⟨10065599, by rfl⟩ : syracuseStep 13420799 = 20131199) B20131199
theorem B19614653 : Blo 1568982 19614653 := bstep (se 3 (by rfl) ⟨3677747, by rfl⟩ : syracuseStep 19614653 = 7355495) B7355495
theorem B30182651 : Blo 1568982 30182651 := bstep (se 1 (by rfl) ⟨22636988, by rfl⟩ : syracuseStep 30182651 = 45273977) B45273977
theorem B5295455 : Blo 1568982 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B7163945 : Blo 1568982 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B5296319 : Blo 1568982 5296319 := bstep (se 1 (by rfl) ⟨3972239, by rfl⟩ : syracuseStep 5296319 = 7944479) B7944479
theorem B2355803 : Blo 1568982 2355803 := bstep (se 1 (by rfl) ⟨1766852, by rfl⟩ : syracuseStep 2355803 = 3533705) B3533705
theorem B1569791 : Blo 1568982 1569791 := bstep (se 1 (by rfl) ⟨1177343, by rfl⟩ : syracuseStep 1569791 = 2354687) B2354687
theorem B1569903 : Blo 1568982 1569903 := bstep (se 1 (by rfl) ⟨1177427, by rfl⟩ : syracuseStep 1569903 = 2354855) B2354855
theorem B1570031 : Blo 1568982 1570031 := bstep (se 1 (by rfl) ⟨1177523, by rfl⟩ : syracuseStep 1570031 = 2355047) B2355047
theorem B1570255 : Blo 1568982 1570255 := bstep (se 1 (by rfl) ⟨1177691, by rfl⟩ : syracuseStep 1570255 = 2355383) B2355383
theorem B4470319 : Blo 1568982 4470319 := bstep (se 1 (by rfl) ⟨3352739, by rfl⟩ : syracuseStep 4470319 = 6705479) B6705479
theorem B1570727 : Blo 1568982 1570727 := bstep (se 1 (by rfl) ⟨1178045, by rfl⟩ : syracuseStep 1570727 = 2356091) B2356091
theorem B10058195 : Blo 1568982 10058195 := bstep (se 1 (by rfl) ⟨7543646, by rfl⟩ : syracuseStep 10058195 = 15087293) B15087293
theorem B13409387 : Blo 1568982 13409387 := bstep (se 1 (by rfl) ⟨10057040, by rfl⟩ : syracuseStep 13409387 = 20114081) B20114081
theorem B5299775 : Blo 1568982 5299775 := bstep (se 1 (by rfl) ⟨3974831, by rfl⟩ : syracuseStep 5299775 = 7949663) B7949663
theorem B3530447 : Blo 1568982 3530447 := bstep (se 1 (by rfl) ⟨2647835, by rfl⟩ : syracuseStep 3530447 = 5295671) B5295671
theorem B4775963 : Blo 1568982 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B9060407 : Blo 1568982 9060407 := bstep (se 1 (by rfl) ⟨6795305, by rfl⟩ : syracuseStep 9060407 = 13590611) B13590611
theorem B3530879 : Blo 1568982 3530879 := bstep (se 1 (by rfl) ⟨2648159, by rfl⟩ : syracuseStep 3530879 = 5296319) B5296319
theorem B8947199 : Blo 1568982 8947199 := bstep (se 1 (by rfl) ⟨6710399, by rfl⟩ : syracuseStep 8947199 = 13420799) B13420799
theorem B13076435 : Blo 1568982 13076435 := bstep (se 1 (by rfl) ⟨9807326, by rfl⟩ : syracuseStep 13076435 = 19614653) B19614653
theorem B8939591 : Blo 1568982 8939591 := bstep (se 1 (by rfl) ⟨6704693, by rfl⟩ : syracuseStep 8939591 = 13409387) B13409387
theorem B20121767 : Blo 1568982 20121767 := bstep (se 1 (by rfl) ⟨15091325, by rfl⟩ : syracuseStep 20121767 = 30182651) B30182651
theorem B3533183 : Blo 1568982 3533183 := bstep (se 1 (by rfl) ⟨2649887, by rfl⟩ : syracuseStep 3533183 = 5299775) B5299775
theorem B2353631 : Blo 1568982 2353631 := bstep (se 1 (by rfl) ⟨1765223, by rfl⟩ : syracuseStep 2353631 = 3530447) B3530447
theorem B2354087 : Blo 1568982 2354087 := bstep (se 1 (by rfl) ⟨1765565, by rfl⟩ : syracuseStep 2354087 = 3531131) B3531131
theorem B10054631 : Blo 1568982 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B1765147 : Blo 1568982 1765147 := bstep (se 1 (by rfl) ⟨1323860, by rfl⟩ : syracuseStep 1765147 = 2647721) B2647721
theorem B6705463 : Blo 1568982 6705463 := bstep (se 1 (by rfl) ⟨5029097, by rfl⟩ : syracuseStep 6705463 = 10058195) B10058195
theorem B5960425 : Blo 1568982 5960425 := bstep (se 2 (by rfl) ⟨2235159, by rfl⟩ : syracuseStep 5960425 = 4470319) B4470319
theorem B1570535 : Blo 1568982 1570535 := bstep (se 1 (by rfl) ⟨1177901, by rfl⟩ : syracuseStep 1570535 = 2355803) B2355803
theorem B4774555 : Blo 1568982 4774555 := bstep (se 1 (by rfl) ⟨3580916, by rfl⟩ : syracuseStep 4774555 = 7161833) B7161833
theorem B11918177 : Blo 1568982 11918177 := bstep (se 2 (by rfl) ⟨4469316, by rfl⟩ : syracuseStep 11918177 = 8938633) B8938633
theorem B3530303 : Blo 1568982 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B6366073 : Blo 1568982 6366073 := bstep (se 2 (by rfl) ⟨2387277, by rfl⟩ : syracuseStep 6366073 = 4774555) B4774555
theorem B7947233 : Blo 1568982 7947233 := bstep (se 2 (by rfl) ⟨2980212, by rfl⟩ : syracuseStep 7947233 = 5960425) B5960425
theorem B5964799 : Blo 1568982 5964799 := bstep (se 1 (by rfl) ⟨4473599, by rfl⟩ : syracuseStep 5964799 = 8947199) B8947199
theorem B6703087 : Blo 1568982 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B2353529 : Blo 1568982 2353529 := bstep (se 2 (by rfl) ⟨882573, by rfl⟩ : syracuseStep 2353529 = 1765147) B1765147
theorem B2353535 : Blo 1568982 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B6040271 : Blo 1568982 6040271 := bstep (se 1 (by rfl) ⟨4530203, by rfl⟩ : syracuseStep 6040271 = 9060407) B9060407
theorem B2353919 : Blo 1568982 2353919 := bstep (se 1 (by rfl) ⟨1765439, by rfl⟩ : syracuseStep 2353919 = 3530879) B3530879
theorem B8940617 : Blo 1568982 8940617 := bstep (se 2 (by rfl) ⟨3352731, by rfl⟩ : syracuseStep 8940617 = 6705463) B6705463
theorem B5959727 : Blo 1568982 5959727 := bstep (se 1 (by rfl) ⟨4469795, by rfl⟩ : syracuseStep 5959727 = 8939591) B8939591
theorem B13414511 : Blo 1568982 13414511 := bstep (se 1 (by rfl) ⟨10060883, by rfl⟩ : syracuseStep 13414511 = 20121767) B20121767
theorem B2355455 : Blo 1568982 2355455 := bstep (se 1 (by rfl) ⟨1766591, by rfl⟩ : syracuseStep 2355455 = 3533183) B3533183
theorem B1569087 : Blo 1568982 1569087 := bstep (se 1 (by rfl) ⟨1176815, by rfl⟩ : syracuseStep 1569087 = 2353631) B2353631
theorem B1569391 : Blo 1568982 1569391 := bstep (se 1 (by rfl) ⟨1177043, by rfl⟩ : syracuseStep 1569391 = 2354087) B2354087
theorem B34870493 : Blo 1568982 34870493 := bstep (se 3 (by rfl) ⟨6538217, by rfl⟩ : syracuseStep 34870493 = 13076435) B13076435
theorem B12735901 : Blo 1568982 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B7945451 : Blo 1568982 7945451 := bstep (se 1 (by rfl) ⟨5959088, by rfl⟩ : syracuseStep 7945451 = 11918177) B11918177
theorem B3973151 : Blo 1568982 3973151 := bstep (se 1 (by rfl) ⟨2979863, by rfl⟩ : syracuseStep 3973151 = 5959727) B5959727
theorem B8488097 : Blo 1568982 8488097 := bstep (se 2 (by rfl) ⟨3183036, by rfl⟩ : syracuseStep 8488097 = 6366073) B6366073
theorem B1569019 : Blo 1568982 1569019 := bstep (se 1 (by rfl) ⟨1176764, by rfl⟩ : syracuseStep 1569019 = 2353529) B2353529
theorem B1569023 : Blo 1568982 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B4026847 : Blo 1568982 4026847 := bstep (se 1 (by rfl) ⟨3020135, by rfl⟩ : syracuseStep 4026847 = 6040271) B6040271
theorem B1569279 : Blo 1568982 1569279 := bstep (se 1 (by rfl) ⟨1176959, by rfl⟩ : syracuseStep 1569279 = 2353919) B2353919
theorem B5960411 : Blo 1568982 5960411 := bstep (se 1 (by rfl) ⟨4470308, by rfl⟩ : syracuseStep 5960411 = 8940617) B8940617
theorem B5296967 : Blo 1568982 5296967 := bstep (se 1 (by rfl) ⟨3972725, by rfl⟩ : syracuseStep 5296967 = 7945451) B7945451
theorem B8943007 : Blo 1568982 8943007 := bstep (se 1 (by rfl) ⟨6707255, by rfl⟩ : syracuseStep 8943007 = 13414511) B13414511
theorem B1570303 : Blo 1568982 1570303 := bstep (se 1 (by rfl) ⟨1177727, by rfl⟩ : syracuseStep 1570303 = 2355455) B2355455
theorem B5298155 : Blo 1568982 5298155 := bstep (se 1 (by rfl) ⟨3973616, by rfl⟩ : syracuseStep 5298155 = 7947233) B7947233
theorem B23246995 : Blo 1568982 23246995 := bstep (se 1 (by rfl) ⟨17435246, by rfl⟩ : syracuseStep 23246995 = 34870493) B34870493
theorem B7953065 : Blo 1568982 7953065 := bstep (se 2 (by rfl) ⟨2982399, by rfl⟩ : syracuseStep 7953065 = 5964799) B5964799
theorem B16981201 : Blo 1568982 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B8937449 : Blo 1568982 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B3973607 : Blo 1568982 3973607 := bstep (se 1 (by rfl) ⟨2980205, by rfl⟩ : syracuseStep 3973607 = 5960411) B5960411
theorem B3531311 : Blo 1568982 3531311 := bstep (se 1 (by rfl) ⟨2648483, by rfl⟩ : syracuseStep 3531311 = 5296967) B5296967
theorem B3532103 : Blo 1568982 3532103 := bstep (se 1 (by rfl) ⟨2649077, by rfl⟩ : syracuseStep 3532103 = 5298155) B5298155
theorem B5302043 : Blo 1568982 5302043 := bstep (se 1 (by rfl) ⟨3976532, by rfl⟩ : syracuseStep 5302043 = 7953065) B7953065
theorem B5958299 : Blo 1568982 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B2648767 : Blo 1568982 2648767 := bstep (se 1 (by rfl) ⟨1986575, by rfl⟩ : syracuseStep 2648767 = 3973151) B3973151
theorem B5369129 : Blo 1568982 5369129 := bstep (se 2 (by rfl) ⟨2013423, by rfl⟩ : syracuseStep 5369129 = 4026847) B4026847
theorem B11924009 : Blo 1568982 11924009 := bstep (se 2 (by rfl) ⟨4471503, by rfl⟩ : syracuseStep 11924009 = 8943007) B8943007
theorem B30995993 : Blo 1568982 30995993 := bstep (se 2 (by rfl) ⟨11623497, by rfl⟩ : syracuseStep 30995993 = 23246995) B23246995
theorem B5658731 : Blo 1568982 5658731 := bstep (se 1 (by rfl) ⟨4244048, by rfl⟩ : syracuseStep 5658731 = 8488097) B8488097
theorem B22641601 : Blo 1568982 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B3531689 : Blo 1568982 3531689 := bstep (se 2 (by rfl) ⟨1324383, by rfl⟩ : syracuseStep 3531689 = 2648767) B2648767
theorem B30188801 : Blo 1568982 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B2649071 : Blo 1568982 2649071 := bstep (se 1 (by rfl) ⟨1986803, by rfl⟩ : syracuseStep 2649071 = 3973607) B3973607
theorem B7949339 : Blo 1568982 7949339 := bstep (se 1 (by rfl) ⟨5962004, by rfl⟩ : syracuseStep 7949339 = 11924009) B11924009
theorem B2354207 : Blo 1568982 2354207 := bstep (se 1 (by rfl) ⟨1765655, by rfl⟩ : syracuseStep 2354207 = 3531311) B3531311
theorem B2354735 : Blo 1568982 2354735 := bstep (se 1 (by rfl) ⟨1766051, by rfl⟩ : syracuseStep 2354735 = 3532103) B3532103
theorem B20663995 : Blo 1568982 20663995 := bstep (se 1 (by rfl) ⟨15497996, by rfl⟩ : syracuseStep 20663995 = 30995993) B30995993
theorem B3534695 : Blo 1568982 3534695 := bstep (se 1 (by rfl) ⟨2651021, by rfl⟩ : syracuseStep 3534695 = 5302043) B5302043
theorem B3772487 : Blo 1568982 3772487 := bstep (se 1 (by rfl) ⟨2829365, by rfl⟩ : syracuseStep 3772487 = 5658731) B5658731
theorem B3972199 : Blo 1568982 3972199 := bstep (se 1 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 3972199 = 5958299) B5958299
theorem B3579419 : Blo 1568982 3579419 := bstep (se 1 (by rfl) ⟨2684564, by rfl⟩ : syracuseStep 3579419 = 5369129) B5369129
theorem B2514991 : Blo 1568982 2514991 := bstep (se 1 (by rfl) ⟨1886243, by rfl⟩ : syracuseStep 2514991 = 3772487) B3772487
theorem B27551993 : Blo 1568982 27551993 := bstep (se 2 (by rfl) ⟨10331997, by rfl⟩ : syracuseStep 27551993 = 20663995) B20663995
theorem B2386279 : Blo 1568982 2386279 := bstep (se 1 (by rfl) ⟨1789709, by rfl⟩ : syracuseStep 2386279 = 3579419) B3579419
theorem B2354459 : Blo 1568982 2354459 := bstep (se 1 (by rfl) ⟨1765844, by rfl⟩ : syracuseStep 2354459 = 3531689) B3531689
theorem B5296265 : Blo 1568982 5296265 := bstep (se 2 (by rfl) ⟨1986099, by rfl⟩ : syracuseStep 5296265 = 3972199) B3972199
theorem B1766047 : Blo 1568982 1766047 := bstep (se 1 (by rfl) ⟨1324535, by rfl⟩ : syracuseStep 1766047 = 2649071) B2649071
theorem B1569471 : Blo 1568982 1569471 := bstep (se 1 (by rfl) ⟨1177103, by rfl⟩ : syracuseStep 1569471 = 2354207) B2354207
theorem B1569823 : Blo 1568982 1569823 := bstep (se 1 (by rfl) ⟨1177367, by rfl⟩ : syracuseStep 1569823 = 2354735) B2354735
theorem B2356463 : Blo 1568982 2356463 := bstep (se 1 (by rfl) ⟨1767347, by rfl⟩ : syracuseStep 2356463 = 3534695) B3534695
theorem B20125867 : Blo 1568982 20125867 := bstep (se 1 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 20125867 = 30188801) B30188801
theorem B5299559 : Blo 1568982 5299559 := bstep (se 1 (by rfl) ⟨3974669, by rfl⟩ : syracuseStep 5299559 = 7949339) B7949339
theorem B3530843 : Blo 1568982 3530843 := bstep (se 1 (by rfl) ⟨2648132, by rfl⟩ : syracuseStep 3530843 = 5296265) B5296265
theorem B3533039 : Blo 1568982 3533039 := bstep (se 1 (by rfl) ⟨2649779, by rfl⟩ : syracuseStep 3533039 = 5299559) B5299559
theorem B3353321 : Blo 1568982 3353321 := bstep (se 2 (by rfl) ⟨1257495, by rfl⟩ : syracuseStep 3353321 = 2514991) B2514991
theorem B2354729 : Blo 1568982 2354729 := bstep (se 2 (by rfl) ⟨883023, by rfl⟩ : syracuseStep 2354729 = 1766047) B1766047
theorem B12726821 : Blo 1568982 12726821 := bstep (se 4 (by rfl) ⟨1193139, by rfl⟩ : syracuseStep 12726821 = 2386279) B2386279
theorem B1569639 : Blo 1568982 1569639 := bstep (se 1 (by rfl) ⟨1177229, by rfl⟩ : syracuseStep 1569639 = 2354459) B2354459
theorem B26834489 : Blo 1568982 26834489 := bstep (se 2 (by rfl) ⟨10062933, by rfl⟩ : syracuseStep 26834489 = 20125867) B20125867
theorem B73471981 : Blo 1568982 73471981 := bstep (se 3 (by rfl) ⟨13775996, by rfl⟩ : syracuseStep 73471981 = 27551993) B27551993
theorem B1570975 : Blo 1568982 1570975 := bstep (se 1 (by rfl) ⟨1178231, by rfl⟩ : syracuseStep 1570975 = 2356463) B2356463
theorem B97962641 : Blo 1568982 97962641 := bstep (se 2 (by rfl) ⟨36735990, by rfl⟩ : syracuseStep 97962641 = 73471981) B73471981
theorem B2353895 : Blo 1568982 2353895 := bstep (se 1 (by rfl) ⟨1765421, by rfl⟩ : syracuseStep 2353895 = 3530843) B3530843
theorem B2355359 : Blo 1568982 2355359 := bstep (se 1 (by rfl) ⟨1766519, by rfl⟩ : syracuseStep 2355359 = 3533039) B3533039
theorem B1569819 : Blo 1568982 1569819 := bstep (se 1 (by rfl) ⟨1177364, by rfl⟩ : syracuseStep 1569819 = 2354729) B2354729
theorem B8484547 : Blo 1568982 8484547 := bstep (se 1 (by rfl) ⟨6363410, by rfl⟩ : syracuseStep 8484547 = 12726821) B12726821
theorem B17889659 : Blo 1568982 17889659 := bstep (se 1 (by rfl) ⟨13417244, by rfl⟩ : syracuseStep 17889659 = 26834489) B26834489
theorem B2235547 : Blo 1568982 2235547 := bstep (se 1 (by rfl) ⟨1676660, by rfl⟩ : syracuseStep 2235547 = 3353321) B3353321
theorem B65308427 : Blo 1568982 65308427 := bstep (se 1 (by rfl) ⟨48981320, by rfl⟩ : syracuseStep 65308427 = 97962641) B97962641
theorem B1569263 : Blo 1568982 1569263 := bstep (se 1 (by rfl) ⟨1176947, by rfl⟩ : syracuseStep 1569263 = 2353895) B2353895
theorem B1570239 : Blo 1568982 1570239 := bstep (se 1 (by rfl) ⟨1177679, by rfl⟩ : syracuseStep 1570239 = 2355359) B2355359
theorem B2980729 : Blo 1568982 2980729 := bstep (se 2 (by rfl) ⟨1117773, by rfl⟩ : syracuseStep 2980729 = 2235547) B2235547
theorem B11926439 : Blo 1568982 11926439 := bstep (se 1 (by rfl) ⟨8944829, by rfl⟩ : syracuseStep 11926439 = 17889659) B17889659
theorem B11312729 : Blo 1568982 11312729 := bstep (se 2 (by rfl) ⟨4242273, by rfl⟩ : syracuseStep 11312729 = 8484547) B8484547
theorem B3974305 : Blo 1568982 3974305 := bstep (se 2 (by rfl) ⟨1490364, by rfl⟩ : syracuseStep 3974305 = 2980729) B2980729
theorem B7950959 : Blo 1568982 7950959 := bstep (se 1 (by rfl) ⟨5963219, by rfl⟩ : syracuseStep 7950959 = 11926439) B11926439
theorem B7541819 : Blo 1568982 7541819 := bstep (se 1 (by rfl) ⟨5656364, by rfl⟩ : syracuseStep 7541819 = 11312729) B11312729
theorem B43538951 : Blo 1568982 43538951 := bstep (se 1 (by rfl) ⟨32654213, by rfl⟩ : syracuseStep 43538951 = 65308427) B65308427
theorem B5300639 : Blo 1568982 5300639 := bstep (se 1 (by rfl) ⟨3975479, by rfl⟩ : syracuseStep 5300639 = 7950959) B7950959
theorem B29025967 : Blo 1568982 29025967 := bstep (se 1 (by rfl) ⟨21769475, by rfl⟩ : syracuseStep 29025967 = 43538951) B43538951
theorem B5027879 : Blo 1568982 5027879 := bstep (se 1 (by rfl) ⟨3770909, by rfl⟩ : syracuseStep 5027879 = 7541819) B7541819
theorem B5299073 : Blo 1568982 5299073 := bstep (se 2 (by rfl) ⟨1987152, by rfl⟩ : syracuseStep 5299073 = 3974305) B3974305
theorem B3532715 : Blo 1568982 3532715 := bstep (se 1 (by rfl) ⟨2649536, by rfl⟩ : syracuseStep 3532715 = 5299073) B5299073
theorem B38701289 : Blo 1568982 38701289 := bstep (se 2 (by rfl) ⟨14512983, by rfl⟩ : syracuseStep 38701289 = 29025967) B29025967
theorem B3533759 : Blo 1568982 3533759 := bstep (se 1 (by rfl) ⟨2650319, by rfl⟩ : syracuseStep 3533759 = 5300639) B5300639
theorem B13407677 : Blo 1568982 13407677 := bstep (se 3 (by rfl) ⟨2513939, by rfl⟩ : syracuseStep 13407677 = 5027879) B5027879
theorem B8938451 : Blo 1568982 8938451 := bstep (se 1 (by rfl) ⟨6703838, by rfl⟩ : syracuseStep 8938451 = 13407677) B13407677
theorem B2355143 : Blo 1568982 2355143 := bstep (se 1 (by rfl) ⟨1766357, by rfl⟩ : syracuseStep 2355143 = 3532715) B3532715
theorem B25800859 : Blo 1568982 25800859 := bstep (se 1 (by rfl) ⟨19350644, by rfl⟩ : syracuseStep 25800859 = 38701289) B38701289
theorem B2355839 : Blo 1568982 2355839 := bstep (se 1 (by rfl) ⟨1766879, by rfl⟩ : syracuseStep 2355839 = 3533759) B3533759
theorem B34401145 : Blo 1568982 34401145 := bstep (se 2 (by rfl) ⟨12900429, by rfl⟩ : syracuseStep 34401145 = 25800859) B25800859
theorem B5958967 : Blo 1568982 5958967 := bstep (se 1 (by rfl) ⟨4469225, by rfl⟩ : syracuseStep 5958967 = 8938451) B8938451
theorem B1570095 : Blo 1568982 1570095 := bstep (se 1 (by rfl) ⟨1177571, by rfl⟩ : syracuseStep 1570095 = 2355143) B2355143
theorem B1570559 : Blo 1568982 1570559 := bstep (se 1 (by rfl) ⟨1177919, by rfl⟩ : syracuseStep 1570559 = 2355839) B2355839
theorem B45868193 : Blo 1568982 45868193 := bstep (se 2 (by rfl) ⟨17200572, by rfl⟩ : syracuseStep 45868193 = 34401145) B34401145
theorem B7945289 : Blo 1568982 7945289 := bstep (se 2 (by rfl) ⟨2979483, by rfl⟩ : syracuseStep 7945289 = 5958967) B5958967
theorem B5296859 : Blo 1568982 5296859 := bstep (se 1 (by rfl) ⟨3972644, by rfl⟩ : syracuseStep 5296859 = 7945289) B7945289
theorem B30578795 : Blo 1568982 30578795 := bstep (se 1 (by rfl) ⟨22934096, by rfl⟩ : syracuseStep 30578795 = 45868193) B45868193
theorem B3531239 : Blo 1568982 3531239 := bstep (se 1 (by rfl) ⟨2648429, by rfl⟩ : syracuseStep 3531239 = 5296859) B5296859
theorem B20385863 : Blo 1568982 20385863 := bstep (se 1 (by rfl) ⟨15289397, by rfl⟩ : syracuseStep 20385863 = 30578795) B30578795
theorem B13590575 : Blo 1568982 13590575 := bstep (se 1 (by rfl) ⟨10192931, by rfl⟩ : syracuseStep 13590575 = 20385863) B20385863
theorem B2354159 : Blo 1568982 2354159 := bstep (se 1 (by rfl) ⟨1765619, by rfl⟩ : syracuseStep 2354159 = 3531239) B3531239
theorem B9060383 : Blo 1568982 9060383 := bstep (se 1 (by rfl) ⟨6795287, by rfl⟩ : syracuseStep 9060383 = 13590575) B13590575
theorem B1569439 : Blo 1568982 1569439 := bstep (se 1 (by rfl) ⟨1177079, by rfl⟩ : syracuseStep 1569439 = 2354159) B2354159
theorem B6040255 : Blo 1568982 6040255 := bstep (se 1 (by rfl) ⟨4530191, by rfl⟩ : syracuseStep 6040255 = 9060383) B9060383
theorem B8053673 : Blo 1568982 8053673 := bstep (se 2 (by rfl) ⟨3020127, by rfl⟩ : syracuseStep 8053673 = 6040255) B6040255
theorem B21476461 : Blo 1568982 21476461 := bstep (se 3 (by rfl) ⟨4026836, by rfl⟩ : syracuseStep 21476461 = 8053673) B8053673
theorem B28635281 : Blo 1568982 28635281 := bstep (se 2 (by rfl) ⟨10738230, by rfl⟩ : syracuseStep 28635281 = 21476461) B21476461
theorem B19090187 : Blo 1568982 19090187 := bstep (se 1 (by rfl) ⟨14317640, by rfl⟩ : syracuseStep 19090187 = 28635281) B28635281
theorem B12726791 : Blo 1568982 12726791 := bstep (se 1 (by rfl) ⟨9545093, by rfl⟩ : syracuseStep 12726791 = 19090187) B19090187
theorem B8484527 : Blo 1568982 8484527 := bstep (se 1 (by rfl) ⟨6363395, by rfl⟩ : syracuseStep 8484527 = 12726791) B12726791
theorem B22625405 : Blo 1568982 22625405 := bstep (se 3 (by rfl) ⟨4242263, by rfl⟩ : syracuseStep 22625405 = 8484527) B8484527
theorem B15083603 : Blo 1568982 15083603 := bstep (se 1 (by rfl) ⟨11312702, by rfl⟩ : syracuseStep 15083603 = 22625405) B22625405
theorem B10055735 : Blo 1568982 10055735 := bstep (se 1 (by rfl) ⟨7541801, by rfl⟩ : syracuseStep 10055735 = 15083603) B15083603
theorem B6703823 : Blo 1568982 6703823 := bstep (se 1 (by rfl) ⟨5027867, by rfl⟩ : syracuseStep 6703823 = 10055735) B10055735
theorem B4469215 : Blo 1568982 4469215 := bstep (se 1 (by rfl) ⟨3351911, by rfl⟩ : syracuseStep 4469215 = 6703823) B6703823
theorem B5958953 : Blo 1568982 5958953 := bstep (se 2 (by rfl) ⟨2234607, by rfl⟩ : syracuseStep 5958953 = 4469215) B4469215
theorem B3972635 : Blo 1568982 3972635 := bstep (se 1 (by rfl) ⟨2979476, by rfl⟩ : syracuseStep 3972635 = 5958953) B5958953
theorem B2648423 : Blo 1568982 2648423 := bstep (se 1 (by rfl) ⟨1986317, by rfl⟩ : syracuseStep 2648423 = 3972635) B3972635
theorem B1765615 : Blo 1568982 1765615 := bstep (se 1 (by rfl) ⟨1324211, by rfl⟩ : syracuseStep 1765615 = 2648423) B2648423
theorem B2354153 : Blo 1568982 2354153 := bstep (se 2 (by rfl) ⟨882807, by rfl⟩ : syracuseStep 2354153 = 1765615) B1765615
theorem B1569435 : Blo 1568982 1569435 := bstep (se 1 (by rfl) ⟨1177076, by rfl⟩ : syracuseStep 1569435 = 2354153) B2354153

theorem C0 (j : ℕ) (h1 : 392245 ≤ j) (h2 : j ≤ 392744) : Blo 1568982 (4 * j + 3) := by
  interval_cases j
  · exact B1568983
  · exact B1568987
  · exact B1568991
  · exact B1568995
  · exact B1568999
  · exact B1569003
  · exact B1569007
  · exact B1569011
  · exact B1569015
  · exact B1569019
  · exact B1569023
  · exact B1569027
  · exact B1569031
  · exact B1569035
  · exact B1569039
  · exact B1569043
  · exact B1569047
  · exact B1569051
  · exact B1569055
  · exact B1569059
  · exact B1569063
  · exact B1569067
  · exact B1569071
  · exact B1569075
  · exact B1569079
  · exact B1569083
  · exact B1569087
  · exact B1569091
  · exact B1569095
  · exact B1569099
  · exact B1569103
  · exact B1569107
  · exact B1569111
  · exact B1569115
  · exact B1569119
  · exact B1569123
  · exact B1569127
  · exact B1569131
  · exact B1569135
  · exact B1569139
  · exact B1569143
  · exact B1569147
  · exact B1569151
  · exact B1569155
  · exact B1569159
  · exact B1569163
  · exact B1569167
  · exact B1569171
  · exact B1569175
  · exact B1569179
  · exact B1569183
  · exact B1569187
  · exact B1569191
  · exact B1569195
  · exact B1569199
  · exact B1569203
  · exact B1569207
  · exact B1569211
  · exact B1569215
  · exact B1569219
  · exact B1569223
  · exact B1569227
  · exact B1569231
  · exact B1569235
  · exact B1569239
  · exact B1569243
  · exact B1569247
  · exact B1569251
  · exact B1569255
  · exact B1569259
  · exact B1569263
  · exact B1569267
  · exact B1569271
  · exact B1569275
  · exact B1569279
  · exact B1569283
  · exact B1569287
  · exact B1569291
  · exact B1569295
  · exact B1569299
  · exact B1569303
  · exact B1569307
  · exact B1569311
  · exact B1569315
  · exact B1569319
  · exact B1569323
  · exact B1569327
  · exact B1569331
  · exact B1569335
  · exact B1569339
  · exact B1569343
  · exact B1569347
  · exact B1569351
  · exact B1569355
  · exact B1569359
  · exact B1569363
  · exact B1569367
  · exact B1569371
  · exact B1569375
  · exact B1569379
  · exact B1569383
  · exact B1569387
  · exact B1569391
  · exact B1569395
  · exact B1569399
  · exact B1569403
  · exact B1569407
  · exact B1569411
  · exact B1569415
  · exact B1569419
  · exact B1569423
  · exact B1569427
  · exact B1569431
  · exact B1569435
  · exact B1569439
  · exact B1569443
  · exact B1569447
  · exact B1569451
  · exact B1569455
  · exact B1569459
  · exact B1569463
  · exact B1569467
  · exact B1569471
  · exact B1569475
  · exact B1569479
  · exact B1569483
  · exact B1569487
  · exact B1569491
  · exact B1569495
  · exact B1569499
  · exact B1569503
  · exact B1569507
  · exact B1569511
  · exact B1569515
  · exact B1569519
  · exact B1569523
  · exact B1569527
  · exact B1569531
  · exact B1569535
  · exact B1569539
  · exact B1569543
  · exact B1569547
  · exact B1569551
  · exact B1569555
  · exact B1569559
  · exact B1569563
  · exact B1569567
  · exact B1569571
  · exact B1569575
  · exact B1569579
  · exact B1569583
  · exact B1569587
  · exact B1569591
  · exact B1569595
  · exact B1569599
  · exact B1569603
  · exact B1569607
  · exact B1569611
  · exact B1569615
  · exact B1569619
  · exact B1569623
  · exact B1569627
  · exact B1569631
  · exact B1569635
  · exact B1569639
  · exact B1569643
  · exact B1569647
  · exact B1569651
  · exact B1569655
  · exact B1569659
  · exact B1569663
  · exact B1569667
  · exact B1569671
  · exact B1569675
  · exact B1569679
  · exact B1569683
  · exact B1569687
  · exact B1569691
  · exact B1569695
  · exact B1569699
  · exact B1569703
  · exact B1569707
  · exact B1569711
  · exact B1569715
  · exact B1569719
  · exact B1569723
  · exact B1569727
  · exact B1569731
  · exact B1569735
  · exact B1569739
  · exact B1569743
  · exact B1569747
  · exact B1569751
  · exact B1569755
  · exact B1569759
  · exact B1569763
  · exact B1569767
  · exact B1569771
  · exact B1569775
  · exact B1569779
  · exact B1569783
  · exact B1569787
  · exact B1569791
  · exact B1569795
  · exact B1569799
  · exact B1569803
  · exact B1569807
  · exact B1569811
  · exact B1569815
  · exact B1569819
  · exact B1569823
  · exact B1569827
  · exact B1569831
  · exact B1569835
  · exact B1569839
  · exact B1569843
  · exact B1569847
  · exact B1569851
  · exact B1569855
  · exact B1569859
  · exact B1569863
  · exact B1569867
  · exact B1569871
  · exact B1569875
  · exact B1569879
  · exact B1569883
  · exact B1569887
  · exact B1569891
  · exact B1569895
  · exact B1569899
  · exact B1569903
  · exact B1569907
  · exact B1569911
  · exact B1569915
  · exact B1569919
  · exact B1569923
  · exact B1569927
  · exact B1569931
  · exact B1569935
  · exact B1569939
  · exact B1569943
  · exact B1569947
  · exact B1569951
  · exact B1569955
  · exact B1569959
  · exact B1569963
  · exact B1569967
  · exact B1569971
  · exact B1569975
  · exact B1569979
  · exact B1569983
  · exact B1569987
  · exact B1569991
  · exact B1569995
  · exact B1569999
  · exact B1570003
  · exact B1570007
  · exact B1570011
  · exact B1570015
  · exact B1570019
  · exact B1570023
  · exact B1570027
  · exact B1570031
  · exact B1570035
  · exact B1570039
  · exact B1570043
  · exact B1570047
  · exact B1570051
  · exact B1570055
  · exact B1570059
  · exact B1570063
  · exact B1570067
  · exact B1570071
  · exact B1570075
  · exact B1570079
  · exact B1570083
  · exact B1570087
  · exact B1570091
  · exact B1570095
  · exact B1570099
  · exact B1570103
  · exact B1570107
  · exact B1570111
  · exact B1570115
  · exact B1570119
  · exact B1570123
  · exact B1570127
  · exact B1570131
  · exact B1570135
  · exact B1570139
  · exact B1570143
  · exact B1570147
  · exact B1570151
  · exact B1570155
  · exact B1570159
  · exact B1570163
  · exact B1570167
  · exact B1570171
  · exact B1570175
  · exact B1570179
  · exact B1570183
  · exact B1570187
  · exact B1570191
  · exact B1570195
  · exact B1570199
  · exact B1570203
  · exact B1570207
  · exact B1570211
  · exact B1570215
  · exact B1570219
  · exact B1570223
  · exact B1570227
  · exact B1570231
  · exact B1570235
  · exact B1570239
  · exact B1570243
  · exact B1570247
  · exact B1570251
  · exact B1570255
  · exact B1570259
  · exact B1570263
  · exact B1570267
  · exact B1570271
  · exact B1570275
  · exact B1570279
  · exact B1570283
  · exact B1570287
  · exact B1570291
  · exact B1570295
  · exact B1570299
  · exact B1570303
  · exact B1570307
  · exact B1570311
  · exact B1570315
  · exact B1570319
  · exact B1570323
  · exact B1570327
  · exact B1570331
  · exact B1570335
  · exact B1570339
  · exact B1570343
  · exact B1570347
  · exact B1570351
  · exact B1570355
  · exact B1570359
  · exact B1570363
  · exact B1570367
  · exact B1570371
  · exact B1570375
  · exact B1570379
  · exact B1570383
  · exact B1570387
  · exact B1570391
  · exact B1570395
  · exact B1570399
  · exact B1570403
  · exact B1570407
  · exact B1570411
  · exact B1570415
  · exact B1570419
  · exact B1570423
  · exact B1570427
  · exact B1570431
  · exact B1570435
  · exact B1570439
  · exact B1570443
  · exact B1570447
  · exact B1570451
  · exact B1570455
  · exact B1570459
  · exact B1570463
  · exact B1570467
  · exact B1570471
  · exact B1570475
  · exact B1570479
  · exact B1570483
  · exact B1570487
  · exact B1570491
  · exact B1570495
  · exact B1570499
  · exact B1570503
  · exact B1570507
  · exact B1570511
  · exact B1570515
  · exact B1570519
  · exact B1570523
  · exact B1570527
  · exact B1570531
  · exact B1570535
  · exact B1570539
  · exact B1570543
  · exact B1570547
  · exact B1570551
  · exact B1570555
  · exact B1570559
  · exact B1570563
  · exact B1570567
  · exact B1570571
  · exact B1570575
  · exact B1570579
  · exact B1570583
  · exact B1570587
  · exact B1570591
  · exact B1570595
  · exact B1570599
  · exact B1570603
  · exact B1570607
  · exact B1570611
  · exact B1570615
  · exact B1570619
  · exact B1570623
  · exact B1570627
  · exact B1570631
  · exact B1570635
  · exact B1570639
  · exact B1570643
  · exact B1570647
  · exact B1570651
  · exact B1570655
  · exact B1570659
  · exact B1570663
  · exact B1570667
  · exact B1570671
  · exact B1570675
  · exact B1570679
  · exact B1570683
  · exact B1570687
  · exact B1570691
  · exact B1570695
  · exact B1570699
  · exact B1570703
  · exact B1570707
  · exact B1570711
  · exact B1570715
  · exact B1570719
  · exact B1570723
  · exact B1570727
  · exact B1570731
  · exact B1570735
  · exact B1570739
  · exact B1570743
  · exact B1570747
  · exact B1570751
  · exact B1570755
  · exact B1570759
  · exact B1570763
  · exact B1570767
  · exact B1570771
  · exact B1570775
  · exact B1570779
  · exact B1570783
  · exact B1570787
  · exact B1570791
  · exact B1570795
  · exact B1570799
  · exact B1570803
  · exact B1570807
  · exact B1570811
  · exact B1570815
  · exact B1570819
  · exact B1570823
  · exact B1570827
  · exact B1570831
  · exact B1570835
  · exact B1570839
  · exact B1570843
  · exact B1570847
  · exact B1570851
  · exact B1570855
  · exact B1570859
  · exact B1570863
  · exact B1570867
  · exact B1570871
  · exact B1570875
  · exact B1570879
  · exact B1570883
  · exact B1570887
  · exact B1570891
  · exact B1570895
  · exact B1570899
  · exact B1570903
  · exact B1570907
  · exact B1570911
  · exact B1570915
  · exact B1570919
  · exact B1570923
  · exact B1570927
  · exact B1570931
  · exact B1570935
  · exact B1570939
  · exact B1570943
  · exact B1570947
  · exact B1570951
  · exact B1570955
  · exact B1570959
  · exact B1570963
  · exact B1570967
  · exact B1570971
  · exact B1570975
  · exact B1570979

theorem solution (m : ℕ) (hlo : 1568982 ≤ m) (hhi : m ≤ 1570982) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 392245 ≤ j := by omega
    have hj2 : j ≤ 392744 := by omega
    have hb : Blo 1568982 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
