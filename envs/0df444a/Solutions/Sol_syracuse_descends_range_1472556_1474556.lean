-- Prove2me | solution 1 for syracuse_descends_range_1472556_1474556
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:45:04.713856+00:00
-- url     : https://prove2.me/submissions/eef56398-59ff-4b84-bb93-c20219eeb4d6

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


theorem B2154533 : Blo 1472556 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B2302013 : Blo 1472556 2302013 := bbase (se 3 (by rfl) ⟨431627, by rfl⟩ : syracuseStep 2302013 = 863255) (by norm_num)
theorem B1572949 : Blo 1472556 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B5308517 : Blo 1472556 5308517 := bbase (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) (by norm_num)
theorem B6291589 : Blo 1472556 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B1704085 : Blo 1472556 1704085 := bbase (se 6 (by rfl) ⟨39939, by rfl⟩ : syracuseStep 1704085 = 79879) (by norm_num)
theorem B2834597 : Blo 1472556 2834597 := bbase (se 4 (by rfl) ⟨265743, by rfl⟩ : syracuseStep 2834597 = 531487) (by norm_num)
theorem B3145949 : Blo 1472556 3145949 := bbase (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) (by norm_num)
theorem B4972805 : Blo 1472556 4972805 := bbase (se 4 (by rfl) ⟨466200, by rfl⟩ : syracuseStep 4972805 = 932401) (by norm_num)
theorem B2654525 : Blo 1472556 2654525 := bbase (se 3 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 2654525 = 995447) (by norm_num)
theorem B7455077 : Blo 1472556 7455077 := bbase (se 4 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 7455077 = 1397827) (by norm_num)
theorem B3727741 : Blo 1472556 3727741 := bbase (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) (by norm_num)
theorem B8511925 : Blo 1472556 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B4194757 : Blo 1472556 4194757 := bbase (se 4 (by rfl) ⟨393258, by rfl⟩ : syracuseStep 4194757 = 786517) (by norm_num)
theorem B3146197 : Blo 1472556 3146197 := bbase (se 7 (by rfl) ⟨36869, by rfl⟩ : syracuseStep 3146197 = 73739) (by norm_num)
theorem B3727853 : Blo 1472556 3727853 := bbase (se 3 (by rfl) ⟨698972, by rfl⟩ : syracuseStep 3727853 = 1397945) (by norm_num)
theorem B1573393 : Blo 1472556 1573393 := bbase (se 2 (by rfl) ⟨590022, by rfl⟩ : syracuseStep 1573393 = 1180045) (by norm_num)
theorem B2654741 : Blo 1472556 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B3539501 : Blo 1472556 3539501 := bbase (se 3 (by rfl) ⟨663656, by rfl⟩ : syracuseStep 3539501 = 1327313) (by norm_num)
theorem B1573453 : Blo 1472556 1573453 := bbase (se 3 (by rfl) ⟨295022, by rfl⟩ : syracuseStep 1573453 = 590045) (by norm_num)
theorem B2654813 : Blo 1472556 2654813 := bbase (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) (by norm_num)
theorem B1991261 : Blo 1472556 1991261 := bbase (se 3 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 1991261 = 746723) (by norm_num)
theorem B3539557 : Blo 1472556 3539557 := bbase (se 4 (by rfl) ⟨331833, by rfl⟩ : syracuseStep 3539557 = 663667) (by norm_num)
theorem B2097829 : Blo 1472556 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B3728045 : Blo 1472556 3728045 := bbase (se 3 (by rfl) ⟨699008, by rfl⟩ : syracuseStep 3728045 = 1398017) (by norm_num)
theorem B2654893 : Blo 1472556 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B4973237 : Blo 1472556 4973237 := bbase (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) (by norm_num)
theorem B2654957 : Blo 1472556 2654957 := bbase (se 3 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 2654957 = 995609) (by norm_num)
theorem B1770221 : Blo 1472556 1770221 := bbase (se 3 (by rfl) ⟨331916, by rfl⟩ : syracuseStep 1770221 = 663833) (by norm_num)
theorem B5595925 : Blo 1472556 5595925 := bbase (se 6 (by rfl) ⟨131154, by rfl⟩ : syracuseStep 5595925 = 262309) (by norm_num)
theorem B8389493 : Blo 1472556 8389493 := bbase (se 5 (by rfl) ⟨393257, by rfl⟩ : syracuseStep 8389493 = 786515) (by norm_num)
theorem B1573769 : Blo 1472556 1573769 := bbase (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) (by norm_num)
theorem B14156693 : Blo 1472556 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B3146701 : Blo 1472556 3146701 := bbase (se 3 (by rfl) ⟨590006, by rfl⟩ : syracuseStep 3146701 = 1180013) (by norm_num)
theorem B2360269 : Blo 1472556 2360269 := bbase (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) (by norm_num)
theorem B2098165 : Blo 1472556 2098165 := bbase (se 5 (by rfl) ⟨98351, by rfl⟩ : syracuseStep 2098165 = 196703) (by norm_num)
theorem B10224629 : Blo 1472556 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B3728389 : Blo 1472556 3728389 := bbase (se 4 (by rfl) ⟨349536, by rfl⟩ : syracuseStep 3728389 = 699073) (by norm_num)
theorem B2655245 : Blo 1472556 2655245 := bbase (se 3 (by rfl) ⟨497858, by rfl⟩ : syracuseStep 2655245 = 995717) (by norm_num)
theorem B1991693 : Blo 1472556 1991693 := bbase (se 3 (by rfl) ⟨373442, by rfl⟩ : syracuseStep 1991693 = 746885) (by norm_num)
theorem B5596229 : Blo 1472556 5596229 := bbase (se 4 (by rfl) ⟨524646, by rfl⟩ : syracuseStep 5596229 = 1049293) (by norm_num)
theorem B4973669 : Blo 1472556 4973669 := bbase (se 4 (by rfl) ⟨466281, by rfl⟩ : syracuseStep 4973669 = 932563) (by norm_num)
theorem B3728501 : Blo 1472556 3728501 := bbase (se 5 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 3728501 = 349547) (by norm_num)
theorem B2098381 : Blo 1472556 2098381 := bbase (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) (by norm_num)
theorem B7464149 : Blo 1472556 7464149 := bbase (se 7 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 7464149 = 174941) (by norm_num)
theorem B3728693 : Blo 1472556 3728693 := bbase (se 5 (by rfl) ⟨174782, by rfl⟩ : syracuseStep 3728693 = 349565) (by norm_num)
theorem B1770817 : Blo 1472556 1770817 := bbase (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) (by norm_num)
theorem B1574213 : Blo 1472556 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B5309797 : Blo 1472556 5309797 := bbase (se 4 (by rfl) ⟨497793, by rfl⟩ : syracuseStep 5309797 = 995587) (by norm_num)
theorem B1574273 : Blo 1472556 1574273 := bbase (se 2 (by rfl) ⟨590352, by rfl⟩ : syracuseStep 1574273 = 1180705) (by norm_num)
theorem B1770913 : Blo 1472556 1770913 := bbase (se 2 (by rfl) ⟨664092, by rfl⟩ : syracuseStep 1770913 = 1328185) (by norm_num)
theorem B1574401 : Blo 1472556 1574401 := bbase (se 2 (by rfl) ⟨590400, by rfl⟩ : syracuseStep 1574401 = 1180801) (by norm_num)
theorem B4974101 : Blo 1472556 4974101 := bbase (se 6 (by rfl) ⟨116580, by rfl⟩ : syracuseStep 4974101 = 233161) (by norm_num)
theorem B2098757 : Blo 1472556 2098757 := bbase (se 4 (by rfl) ⟨196758, by rfl⟩ : syracuseStep 2098757 = 393517) (by norm_num)
theorem B3540557 : Blo 1472556 3540557 := bbase (se 3 (by rfl) ⟨663854, by rfl⟩ : syracuseStep 3540557 = 1327709) (by norm_num)
theorem B7456373 : Blo 1472556 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B5973637 : Blo 1472556 5973637 := bbase (se 4 (by rfl) ⟨560028, by rfl⟩ : syracuseStep 5973637 = 1120057) (by norm_num)
theorem B3729037 : Blo 1472556 3729037 := bbase (se 3 (by rfl) ⟨699194, by rfl⟩ : syracuseStep 3729037 = 1398389) (by norm_num)
theorem B2360981 : Blo 1472556 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B7079653 : Blo 1472556 7079653 := bbase (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) (by norm_num)
theorem B3729149 : Blo 1472556 3729149 := bbase (se 3 (by rfl) ⟨699215, by rfl⟩ : syracuseStep 3729149 = 1398431) (by norm_num)
theorem B3147589 : Blo 1472556 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B1656661 : Blo 1472556 1656661 := bbase (se 9 (by rfl) ⟨4853, by rfl⟩ : syracuseStep 1656661 = 9707) (by norm_num)
theorem B4786037 : Blo 1472556 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B1656697 : Blo 1472556 1656697 := bbase (se 2 (by rfl) ⟨621261, by rfl⟩ : syracuseStep 1656697 = 1242523) (by norm_num)
theorem B4482965 : Blo 1472556 4482965 := bbase (se 6 (by rfl) ⟨105069, by rfl⟩ : syracuseStep 4482965 = 210139) (by norm_num)
theorem B1656733 : Blo 1472556 1656733 := bbase (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) (by norm_num)
theorem B4196261 : Blo 1472556 4196261 := bbase (se 4 (by rfl) ⟨393399, by rfl⟩ : syracuseStep 4196261 = 786799) (by norm_num)
theorem B3360685 : Blo 1472556 3360685 := bbase (se 3 (by rfl) ⟨630128, by rfl⟩ : syracuseStep 3360685 = 1260257) (by norm_num)
theorem B3729341 : Blo 1472556 3729341 := bbase (se 3 (by rfl) ⟨699251, by rfl⟩ : syracuseStep 3729341 = 1398503) (by norm_num)
theorem B1656769 : Blo 1472556 1656769 := bbase (se 2 (by rfl) ⟨621288, by rfl⟩ : syracuseStep 1656769 = 1242577) (by norm_num)
theorem B4974533 : Blo 1472556 4974533 := bbase (se 4 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 4974533 = 932725) (by norm_num)
theorem B1656805 : Blo 1472556 1656805 := bbase (se 4 (by rfl) ⟨155325, by rfl⟩ : syracuseStep 1656805 = 310651) (by norm_num)
theorem B1656841 : Blo 1472556 1656841 := bbase (se 2 (by rfl) ⟨621315, by rfl⟩ : syracuseStep 1656841 = 1242631) (by norm_num)
theorem B1656877 : Blo 1472556 1656877 := bbase (se 3 (by rfl) ⟨310664, by rfl⟩ : syracuseStep 1656877 = 621329) (by norm_num)
theorem B1534009 : Blo 1472556 1534009 := bbase (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) (by norm_num)
theorem B1656913 : Blo 1472556 1656913 := bbase (se 2 (by rfl) ⟨621342, by rfl⟩ : syracuseStep 1656913 = 1242685) (by norm_num)
theorem B1493105 : Blo 1472556 1493105 := bbase (se 2 (by rfl) ⟨559914, by rfl⟩ : syracuseStep 1493105 = 1119829) (by norm_num)
theorem B1656949 : Blo 1472556 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1656985 : Blo 1472556 1656985 := bbase (se 2 (by rfl) ⟨621369, by rfl⟩ : syracuseStep 1656985 = 1242739) (by norm_num)
theorem B1657021 : Blo 1472556 1657021 := bbase (se 3 (by rfl) ⟨310691, by rfl⟩ : syracuseStep 1657021 = 621383) (by norm_num)
theorem B1657057 : Blo 1472556 1657057 := bbase (se 2 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 1657057 = 1242793) (by norm_num)
theorem B1657093 : Blo 1472556 1657093 := bbase (se 4 (by rfl) ⟨155352, by rfl⟩ : syracuseStep 1657093 = 310705) (by norm_num)
theorem B3729685 : Blo 1472556 3729685 := bbase (se 6 (by rfl) ⟨87414, by rfl⟩ : syracuseStep 3729685 = 174829) (by norm_num)
theorem B3688741 : Blo 1472556 3688741 := bbase (se 4 (by rfl) ⟨345819, by rfl⟩ : syracuseStep 3688741 = 691639) (by norm_num)
theorem B1657129 : Blo 1472556 1657129 := bbase (se 2 (by rfl) ⟨621423, by rfl⟩ : syracuseStep 1657129 = 1242847) (by norm_num)
theorem B3148085 : Blo 1472556 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2656565 : Blo 1472556 2656565 := bbase (se 5 (by rfl) ⟨124526, by rfl⟩ : syracuseStep 2656565 = 249053) (by norm_num)
theorem B2361653 : Blo 1472556 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B1657165 : Blo 1472556 1657165 := bbase (se 3 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 1657165 = 621437) (by norm_num)
theorem B1657201 : Blo 1472556 1657201 := bbase (se 2 (by rfl) ⟨621450, by rfl⟩ : syracuseStep 1657201 = 1242901) (by norm_num)
theorem B4974965 : Blo 1472556 4974965 := bbase (se 5 (by rfl) ⟨233201, by rfl⟩ : syracuseStep 4974965 = 466403) (by norm_num)
theorem B3729797 : Blo 1472556 3729797 := bbase (se 4 (by rfl) ⟨349668, by rfl⟩ : syracuseStep 3729797 = 699337) (by norm_num)
theorem B1657237 : Blo 1472556 1657237 := bbase (se 6 (by rfl) ⟨38841, by rfl⟩ : syracuseStep 1657237 = 77683) (by norm_num)
theorem B12585365 : Blo 1472556 12585365 := bbase (se 6 (by rfl) ⟨294969, by rfl⟩ : syracuseStep 12585365 = 589939) (by norm_num)
theorem B26888597 : Blo 1472556 26888597 := bbase (se 6 (by rfl) ⟨630201, by rfl⟩ : syracuseStep 26888597 = 1260403) (by norm_num)
theorem B1657273 : Blo 1472556 1657273 := bbase (se 2 (by rfl) ⟨621477, by rfl⟩ : syracuseStep 1657273 = 1242955) (by norm_num)
theorem B2591165 : Blo 1472556 2591165 := bbase (se 3 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 2591165 = 971687) (by norm_num)
theorem B1657309 : Blo 1472556 1657309 := bbase (se 3 (by rfl) ⟨310745, by rfl⟩ : syracuseStep 1657309 = 621491) (by norm_num)
theorem B9079285 : Blo 1472556 9079285 := bbase (se 5 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 9079285 = 851183) (by norm_num)
theorem B4721141 : Blo 1472556 4721141 := bbase (se 5 (by rfl) ⟨221303, by rfl⟩ : syracuseStep 4721141 = 442607) (by norm_num)
theorem B1657345 : Blo 1472556 1657345 := bbase (se 2 (by rfl) ⟨621504, by rfl⟩ : syracuseStep 1657345 = 1243009) (by norm_num)
theorem B1657381 : Blo 1472556 1657381 := bbase (se 4 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 1657381 = 310759) (by norm_num)
theorem B3729989 : Blo 1472556 3729989 := bbase (se 4 (by rfl) ⟨349686, by rfl⟩ : syracuseStep 3729989 = 699373) (by norm_num)
theorem B1657417 : Blo 1472556 1657417 := bbase (se 2 (by rfl) ⟨621531, by rfl⟩ : syracuseStep 1657417 = 1243063) (by norm_num)
theorem B2796133 : Blo 1472556 2796133 := bbase (se 4 (by rfl) ⟨262137, by rfl⟩ : syracuseStep 2796133 = 524275) (by norm_num)
theorem B1657453 : Blo 1472556 1657453 := bbase (se 3 (by rfl) ⟨310772, by rfl⟩ : syracuseStep 1657453 = 621545) (by norm_num)
theorem B1657489 : Blo 1472556 1657489 := bbase (se 2 (by rfl) ⟨621558, by rfl⟩ : syracuseStep 1657489 = 1243117) (by norm_num)
theorem B1657525 : Blo 1472556 1657525 := bbase (se 5 (by rfl) ⟨77696, by rfl⟩ : syracuseStep 1657525 = 155393) (by norm_num)
theorem B1657561 : Blo 1472556 1657561 := bbase (se 2 (by rfl) ⟨621585, by rfl⟩ : syracuseStep 1657561 = 1243171) (by norm_num)
theorem B2484965 : Blo 1472556 2484965 := bbase (se 4 (by rfl) ⟨232965, by rfl⟩ : syracuseStep 2484965 = 465931) (by norm_num)
theorem B2796277 : Blo 1472556 2796277 := bbase (se 5 (by rfl) ⟨131075, by rfl⟩ : syracuseStep 2796277 = 262151) (by norm_num)
theorem B1657597 : Blo 1472556 1657597 := bbase (se 3 (by rfl) ⟨310799, by rfl⟩ : syracuseStep 1657597 = 621599) (by norm_num)
theorem B3590909 : Blo 1472556 3590909 := bbase (se 3 (by rfl) ⟨673295, by rfl⟩ : syracuseStep 3590909 = 1346591) (by norm_num)
theorem B1657633 : Blo 1472556 1657633 := bbase (se 2 (by rfl) ⟨621612, by rfl⟩ : syracuseStep 1657633 = 1243225) (by norm_num)
theorem B4975397 : Blo 1472556 4975397 := bbase (se 4 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 4975397 = 932887) (by norm_num)
theorem B1657669 : Blo 1472556 1657669 := bbase (se 4 (by rfl) ⟨155406, by rfl⟩ : syracuseStep 1657669 = 310813) (by norm_num)
theorem B24218453 : Blo 1472556 24218453 := bbase (se 9 (by rfl) ⟨70952, by rfl⟩ : syracuseStep 24218453 = 141905) (by norm_num)
theorem B2485093 : Blo 1472556 2485093 := bbase (se 4 (by rfl) ⟨232977, by rfl⟩ : syracuseStep 2485093 = 465955) (by norm_num)
theorem B1657705 : Blo 1472556 1657705 := bbase (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) (by norm_num)
theorem B7457669 : Blo 1472556 7457669 := bbase (se 4 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 7457669 = 1398313) (by norm_num)
theorem B1657741 : Blo 1472556 1657741 := bbase (se 3 (by rfl) ⟨310826, by rfl⟩ : syracuseStep 1657741 = 621653) (by norm_num)
theorem B2796437 : Blo 1472556 2796437 := bbase (se 6 (by rfl) ⟨65541, by rfl⟩ : syracuseStep 2796437 = 131083) (by norm_num)
theorem B3730333 : Blo 1472556 3730333 := bbase (se 3 (by rfl) ⟨699437, by rfl⟩ : syracuseStep 3730333 = 1398875) (by norm_num)
theorem B1657777 : Blo 1472556 1657777 := bbase (se 2 (by rfl) ⟨621666, by rfl⟩ : syracuseStep 1657777 = 1243333) (by norm_num)
theorem B14560181 : Blo 1472556 14560181 := bbase (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) (by norm_num)
theorem B2485181 : Blo 1472556 2485181 := bbase (se 3 (by rfl) ⟨465971, by rfl⟩ : syracuseStep 2485181 = 931943) (by norm_num)
theorem B1493965 : Blo 1472556 1493965 := bbase (se 3 (by rfl) ⟨280118, by rfl⟩ : syracuseStep 1493965 = 560237) (by norm_num)
theorem B1657813 : Blo 1472556 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B1657849 : Blo 1472556 1657849 := bbase (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) (by norm_num)
theorem B3730445 : Blo 1472556 3730445 := bbase (se 3 (by rfl) ⟨699458, by rfl⟩ : syracuseStep 3730445 = 1398917) (by norm_num)
theorem B8391701 : Blo 1472556 8391701 := bbase (se 6 (by rfl) ⟨196680, by rfl⟩ : syracuseStep 8391701 = 393361) (by norm_num)
theorem B11955221 : Blo 1472556 11955221 := bbase (se 6 (by rfl) ⟨280200, by rfl⟩ : syracuseStep 11955221 = 560401) (by norm_num)
theorem B1657885 : Blo 1472556 1657885 := bbase (se 3 (by rfl) ⟨310853, by rfl⟩ : syracuseStep 1657885 = 621707) (by norm_num)
theorem B2796581 : Blo 1472556 2796581 := bbase (se 4 (by rfl) ⟨262179, by rfl⟩ : syracuseStep 2796581 = 524359) (by norm_num)
theorem B6294581 : Blo 1472556 6294581 := bbase (se 5 (by rfl) ⟨295058, by rfl⟩ : syracuseStep 6294581 = 590117) (by norm_num)
theorem B2485309 : Blo 1472556 2485309 := bbase (se 3 (by rfl) ⟨465995, by rfl⟩ : syracuseStep 2485309 = 931991) (by norm_num)
theorem B1657921 : Blo 1472556 1657921 := bbase (se 2 (by rfl) ⟨621720, by rfl⟩ : syracuseStep 1657921 = 1243441) (by norm_num)
theorem B1657957 : Blo 1472556 1657957 := bbase (se 4 (by rfl) ⟨155433, by rfl⟩ : syracuseStep 1657957 = 310867) (by norm_num)
theorem B5598341 : Blo 1472556 5598341 := bbase (se 4 (by rfl) ⟨524844, by rfl⟩ : syracuseStep 5598341 = 1049689) (by norm_num)
theorem B1657993 : Blo 1472556 1657993 := bbase (se 2 (by rfl) ⟨621747, by rfl⟩ : syracuseStep 1657993 = 1243495) (by norm_num)
theorem B2485397 : Blo 1472556 2485397 := bbase (se 6 (by rfl) ⟨58251, by rfl⟩ : syracuseStep 2485397 = 116503) (by norm_num)
theorem B1658029 : Blo 1472556 1658029 := bbase (se 3 (by rfl) ⟨310880, by rfl⟩ : syracuseStep 1658029 = 621761) (by norm_num)
theorem B3148973 : Blo 1472556 3148973 := bbase (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) (by norm_num)
theorem B3730637 : Blo 1472556 3730637 := bbase (se 3 (by rfl) ⟨699494, by rfl⟩ : syracuseStep 3730637 = 1398989) (by norm_num)
theorem B1658065 : Blo 1472556 1658065 := bbase (se 2 (by rfl) ⟨621774, by rfl⟩ : syracuseStep 1658065 = 1243549) (by norm_num)
theorem B4975829 : Blo 1472556 4975829 := bbase (se 7 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 4975829 = 116621) (by norm_num)
theorem B1658101 : Blo 1472556 1658101 := bbase (se 5 (by rfl) ⟨77723, by rfl⟩ : syracuseStep 1658101 = 155447) (by norm_num)
theorem B2485525 : Blo 1472556 2485525 := bbase (se 6 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 2485525 = 116509) (by norm_num)
theorem B1658137 : Blo 1472556 1658137 := bbase (se 2 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 1658137 = 1243603) (by norm_num)
theorem B3149093 : Blo 1472556 3149093 := bbase (se 4 (by rfl) ⟨295227, by rfl⟩ : syracuseStep 3149093 = 590455) (by norm_num)
theorem B1658173 : Blo 1472556 1658173 := bbase (se 3 (by rfl) ⟨310907, by rfl⟩ : syracuseStep 1658173 = 621815) (by norm_num)
theorem B2796869 : Blo 1472556 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B1658209 : Blo 1472556 1658209 := bbase (se 2 (by rfl) ⟨621828, by rfl⟩ : syracuseStep 1658209 = 1243657) (by norm_num)
theorem B2485613 : Blo 1472556 2485613 := bbase (se 3 (by rfl) ⟨466052, by rfl⟩ : syracuseStep 2485613 = 932105) (by norm_num)
theorem B4148597 : Blo 1472556 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B1658245 : Blo 1472556 1658245 := bbase (se 4 (by rfl) ⟨155460, by rfl⟩ : syracuseStep 1658245 = 310921) (by norm_num)
theorem B5598629 : Blo 1472556 5598629 := bbase (se 4 (by rfl) ⟨524871, by rfl⟩ : syracuseStep 5598629 = 1049743) (by norm_num)
theorem B1658281 : Blo 1472556 1658281 := bbase (se 2 (by rfl) ⟨621855, by rfl⟩ : syracuseStep 1658281 = 1243711) (by norm_num)
theorem B1658317 : Blo 1472556 1658317 := bbase (se 3 (by rfl) ⟨310934, by rfl⟩ : syracuseStep 1658317 = 621869) (by norm_num)
theorem B4197845 : Blo 1472556 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B2797021 : Blo 1472556 2797021 := bbase (se 3 (by rfl) ⟨524441, by rfl⟩ : syracuseStep 2797021 = 1048883) (by norm_num)
theorem B2485741 : Blo 1472556 2485741 := bbase (se 3 (by rfl) ⟨466076, by rfl⟩ : syracuseStep 2485741 = 932153) (by norm_num)
theorem B1658353 : Blo 1472556 1658353 := bbase (se 2 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 1658353 = 1243765) (by norm_num)
theorem B1658389 : Blo 1472556 1658389 := bbase (se 6 (by rfl) ⟨38868, by rfl⟩ : syracuseStep 1658389 = 77737) (by norm_num)
theorem B3730981 : Blo 1472556 3730981 := bbase (se 4 (by rfl) ⟨349779, by rfl⟩ : syracuseStep 3730981 = 699559) (by norm_num)
theorem B4722229 : Blo 1472556 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B1658425 : Blo 1472556 1658425 := bbase (se 2 (by rfl) ⟨621909, by rfl⟩ : syracuseStep 1658425 = 1243819) (by norm_num)
theorem B2485829 : Blo 1472556 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B1658461 : Blo 1472556 1658461 := bbase (se 3 (by rfl) ⟨310961, by rfl⟩ : syracuseStep 1658461 = 621923) (by norm_num)
theorem B3313277 : Blo 1472556 3313277 := bbase (se 3 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 3313277 = 1242479) (by norm_num)
theorem B1658497 : Blo 1472556 1658497 := bbase (se 2 (by rfl) ⟨621936, by rfl⟩ : syracuseStep 1658497 = 1243873) (by norm_num)
theorem B4976261 : Blo 1472556 4976261 := bbase (se 4 (by rfl) ⟨466524, by rfl⟩ : syracuseStep 4976261 = 933049) (by norm_num)
theorem B3731093 : Blo 1472556 3731093 := bbase (se 6 (by rfl) ⟨87447, by rfl⟩ : syracuseStep 3731093 = 174895) (by norm_num)
theorem B1658533 : Blo 1472556 1658533 := bbase (se 4 (by rfl) ⟨155487, by rfl⟩ : syracuseStep 1658533 = 310975) (by norm_num)
theorem B11194037 : Blo 1472556 11194037 := bbase (se 5 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 11194037 = 1049441) (by norm_num)
theorem B3313349 : Blo 1472556 3313349 := bbase (se 4 (by rfl) ⟨310626, by rfl⟩ : syracuseStep 3313349 = 621253) (by norm_num)
theorem B2485957 : Blo 1472556 2485957 := bbase (se 4 (by rfl) ⟨233058, by rfl⟩ : syracuseStep 2485957 = 466117) (by norm_num)
theorem B1658569 : Blo 1472556 1658569 := bbase (se 2 (by rfl) ⟨621963, by rfl⟩ : syracuseStep 1658569 = 1243927) (by norm_num)
theorem B30240469 : Blo 1472556 30240469 := bbase (se 7 (by rfl) ⟨354380, by rfl⟩ : syracuseStep 30240469 = 708761) (by norm_num)
theorem B3985109 : Blo 1472556 3985109 := bbase (se 7 (by rfl) ⟨46700, by rfl⟩ : syracuseStep 3985109 = 93401) (by norm_num)
theorem B1658605 : Blo 1472556 1658605 := bbase (se 3 (by rfl) ⟨310988, by rfl⟩ : syracuseStep 1658605 = 621977) (by norm_num)
theorem B3313421 : Blo 1472556 3313421 := bbase (se 3 (by rfl) ⟨621266, by rfl⟩ : syracuseStep 3313421 = 1242533) (by norm_num)
theorem B2797325 : Blo 1472556 2797325 := bbase (se 3 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 2797325 = 1048997) (by norm_num)
theorem B1658641 : Blo 1472556 1658641 := bbase (se 2 (by rfl) ⟨621990, by rfl⟩ : syracuseStep 1658641 = 1243981) (by norm_num)
theorem B2486045 : Blo 1472556 2486045 := bbase (se 3 (by rfl) ⟨466133, by rfl⟩ : syracuseStep 2486045 = 932267) (by norm_num)
theorem B1658677 : Blo 1472556 1658677 := bbase (se 5 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 1658677 = 155501) (by norm_num)
theorem B3313493 : Blo 1472556 3313493 := bbase (se 9 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 3313493 = 19415) (by norm_num)
theorem B3731285 : Blo 1472556 3731285 := bbase (se 9 (by rfl) ⟨10931, by rfl⟩ : syracuseStep 3731285 = 21863) (by norm_num)
theorem B1658713 : Blo 1472556 1658713 := bbase (se 2 (by rfl) ⟨622017, by rfl⟩ : syracuseStep 1658713 = 1244035) (by norm_num)
theorem B1658749 : Blo 1472556 1658749 := bbase (se 3 (by rfl) ⟨311015, by rfl⟩ : syracuseStep 1658749 = 622031) (by norm_num)
theorem B3542933 : Blo 1472556 3542933 := bbase (se 6 (by rfl) ⟨83037, by rfl⟩ : syracuseStep 3542933 = 166075) (by norm_num)
theorem B3313565 : Blo 1472556 3313565 := bbase (se 3 (by rfl) ⟨621293, by rfl⟩ : syracuseStep 3313565 = 1242587) (by norm_num)
theorem B2486173 : Blo 1472556 2486173 := bbase (se 3 (by rfl) ⟨466157, by rfl⟩ : syracuseStep 2486173 = 932315) (by norm_num)
theorem B1658785 : Blo 1472556 1658785 := bbase (se 2 (by rfl) ⟨622044, by rfl⟩ : syracuseStep 1658785 = 1244089) (by norm_num)
theorem B1658821 : Blo 1472556 1658821 := bbase (se 4 (by rfl) ⟨155514, by rfl⟩ : syracuseStep 1658821 = 311029) (by norm_num)
theorem B3313637 : Blo 1472556 3313637 := bbase (se 4 (by rfl) ⟨310653, by rfl⟩ : syracuseStep 3313637 = 621307) (by norm_num)
theorem B1658857 : Blo 1472556 1658857 := bbase (se 2 (by rfl) ⟨622071, by rfl⟩ : syracuseStep 1658857 = 1244143) (by norm_num)
theorem B2486261 : Blo 1472556 2486261 := bbase (se 5 (by rfl) ⟨116543, by rfl⟩ : syracuseStep 2486261 = 233087) (by norm_num)
theorem B6295589 : Blo 1472556 6295589 := bbase (se 4 (by rfl) ⟨590211, by rfl⟩ : syracuseStep 6295589 = 1180423) (by norm_num)
theorem B3313709 : Blo 1472556 3313709 := bbase (se 3 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 3313709 = 1242641) (by norm_num)
theorem B1863749 : Blo 1472556 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B11186261 : Blo 1472556 11186261 := bbase (se 8 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 11186261 = 131089) (by norm_num)
theorem B3313781 : Blo 1472556 3313781 := bbase (se 5 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 3313781 = 310667) (by norm_num)
theorem B2486389 : Blo 1472556 2486389 := bbase (se 5 (by rfl) ⟨116549, by rfl⟩ : syracuseStep 2486389 = 233099) (by norm_num)
theorem B4198517 : Blo 1472556 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B1863805 : Blo 1472556 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B7458965 : Blo 1472556 7458965 := bbase (se 6 (by rfl) ⟨174819, by rfl⟩ : syracuseStep 7458965 = 349639) (by norm_num)
theorem B3731629 : Blo 1472556 3731629 := bbase (se 3 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 3731629 = 1399361) (by norm_num)
theorem B9441461 : Blo 1472556 9441461 := bbase (se 5 (by rfl) ⟨442568, by rfl⟩ : syracuseStep 9441461 = 885137) (by norm_num)
theorem B3313853 : Blo 1472556 3313853 := bbase (se 3 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 3313853 = 1242695) (by norm_num)
theorem B2486477 : Blo 1472556 2486477 := bbase (se 3 (by rfl) ⟨466214, by rfl⟩ : syracuseStep 2486477 = 932429) (by norm_num)
theorem B1863901 : Blo 1472556 1863901 := bbase (se 3 (by rfl) ⟨349481, by rfl⟩ : syracuseStep 1863901 = 698963) (by norm_num)
theorem B3313925 : Blo 1472556 3313925 := bbase (se 4 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 3313925 = 621361) (by norm_num)
theorem B3731741 : Blo 1472556 3731741 := bbase (se 3 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 3731741 = 1399403) (by norm_num)
theorem B3313997 : Blo 1472556 3313997 := bbase (se 3 (by rfl) ⟨621374, by rfl⟩ : syracuseStep 3313997 = 1242749) (by norm_num)
theorem B2486605 : Blo 1472556 2486605 := bbase (se 3 (by rfl) ⟨466238, by rfl⟩ : syracuseStep 2486605 = 932477) (by norm_num)
theorem B2240893 : Blo 1472556 2240893 := bbase (se 3 (by rfl) ⟨420167, by rfl⟩ : syracuseStep 2240893 = 840335) (by norm_num)
theorem B1864073 : Blo 1472556 1864073 := bbase (se 2 (by rfl) ⟨699027, by rfl⟩ : syracuseStep 1864073 = 1398055) (by norm_num)
theorem B3314069 : Blo 1472556 3314069 := bbase (se 6 (by rfl) ⟨77673, by rfl⟩ : syracuseStep 3314069 = 155347) (by norm_num)
theorem B2486693 : Blo 1472556 2486693 := bbase (se 4 (by rfl) ⟨233127, by rfl⟩ : syracuseStep 2486693 = 466255) (by norm_num)
theorem B1864129 : Blo 1472556 1864129 := bbase (se 2 (by rfl) ⟨699048, by rfl⟩ : syracuseStep 1864129 = 1398097) (by norm_num)
theorem B54514133 : Blo 1472556 54514133 := bbase (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) (by norm_num)
theorem B3314141 : Blo 1472556 3314141 := bbase (se 3 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 3314141 = 1242803) (by norm_num)
theorem B3731933 : Blo 1472556 3731933 := bbase (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) (by norm_num)
theorem B2798077 : Blo 1472556 2798077 := bbase (se 3 (by rfl) ⟨524639, by rfl⟩ : syracuseStep 2798077 = 1049279) (by norm_num)
theorem B1864225 : Blo 1472556 1864225 := bbase (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) (by norm_num)
theorem B3314213 : Blo 1472556 3314213 := bbase (se 4 (by rfl) ⟨310707, by rfl⟩ : syracuseStep 3314213 = 621415) (by norm_num)
theorem B2486821 : Blo 1472556 2486821 := bbase (se 4 (by rfl) ⟨233139, by rfl⟩ : syracuseStep 2486821 = 466279) (by norm_num)
theorem B4198949 : Blo 1472556 4198949 := bbase (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) (by norm_num)
theorem B3314285 : Blo 1472556 3314285 := bbase (se 3 (by rfl) ⟨621428, by rfl⟩ : syracuseStep 3314285 = 1242857) (by norm_num)
theorem B2486909 : Blo 1472556 2486909 := bbase (se 3 (by rfl) ⟨466295, by rfl⟩ : syracuseStep 2486909 = 932591) (by norm_num)
theorem B2798221 : Blo 1472556 2798221 := bbase (se 3 (by rfl) ⟨524666, by rfl⟩ : syracuseStep 2798221 = 1049333) (by norm_num)
theorem B3314357 : Blo 1472556 3314357 := bbase (se 5 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 3314357 = 310721) (by norm_num)
theorem B4723397 : Blo 1472556 4723397 := bbase (se 4 (by rfl) ⟨442818, by rfl⟩ : syracuseStep 4723397 = 885637) (by norm_num)
theorem B1864397 : Blo 1472556 1864397 := bbase (se 3 (by rfl) ⟨349574, by rfl⟩ : syracuseStep 1864397 = 699149) (by norm_num)
theorem B3314429 : Blo 1472556 3314429 := bbase (se 3 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 3314429 = 1242911) (by norm_num)
theorem B2487037 : Blo 1472556 2487037 := bbase (se 3 (by rfl) ⟨466319, by rfl⟩ : syracuseStep 2487037 = 932639) (by norm_num)
theorem B1864453 : Blo 1472556 1864453 := bbase (se 4 (by rfl) ⟨174792, by rfl⟩ : syracuseStep 1864453 = 349585) (by norm_num)
theorem B2798381 : Blo 1472556 2798381 := bbase (se 3 (by rfl) ⟨524696, by rfl⟩ : syracuseStep 2798381 = 1049393) (by norm_num)
theorem B3732277 : Blo 1472556 3732277 := bbase (se 5 (by rfl) ⟨174950, by rfl⟩ : syracuseStep 3732277 = 349901) (by norm_num)
theorem B3314501 : Blo 1472556 3314501 := bbase (se 4 (by rfl) ⟨310734, by rfl⟩ : syracuseStep 3314501 = 621469) (by norm_num)
theorem B2487125 : Blo 1472556 2487125 := bbase (se 9 (by rfl) ⟨7286, by rfl⟩ : syracuseStep 2487125 = 14573) (by norm_num)
theorem B1864549 : Blo 1472556 1864549 := bbase (se 4 (by rfl) ⟨174801, by rfl⟩ : syracuseStep 1864549 = 349603) (by norm_num)
theorem B3314573 : Blo 1472556 3314573 := bbase (se 3 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 3314573 = 1242965) (by norm_num)
theorem B3732389 : Blo 1472556 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B2798525 : Blo 1472556 2798525 := bbase (se 3 (by rfl) ⟨524723, by rfl⟩ : syracuseStep 2798525 = 1049447) (by norm_num)
theorem B3314645 : Blo 1472556 3314645 := bbase (se 7 (by rfl) ⟨38843, by rfl⟩ : syracuseStep 3314645 = 77687) (by norm_num)
theorem B2487253 : Blo 1472556 2487253 := bbase (se 7 (by rfl) ⟨29147, by rfl⟩ : syracuseStep 2487253 = 58295) (by norm_num)
theorem B2986973 : Blo 1472556 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B5592037 : Blo 1472556 5592037 := bbase (se 4 (by rfl) ⟨524253, by rfl⟩ : syracuseStep 5592037 = 1048507) (by norm_num)
theorem B5977061 : Blo 1472556 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B2987021 : Blo 1472556 2987021 := bbase (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) (by norm_num)
theorem B1864721 : Blo 1472556 1864721 := bbase (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) (by norm_num)
theorem B3314717 : Blo 1472556 3314717 := bbase (se 3 (by rfl) ⟨621509, by rfl⟩ : syracuseStep 3314717 = 1243019) (by norm_num)
theorem B2487341 : Blo 1472556 2487341 := bbase (se 3 (by rfl) ⟨466376, by rfl⟩ : syracuseStep 2487341 = 932753) (by norm_num)
theorem B1864777 : Blo 1472556 1864777 := bbase (se 2 (by rfl) ⟨699291, by rfl⟩ : syracuseStep 1864777 = 1398583) (by norm_num)
theorem B2208845 : Blo 1472556 2208845 := bbase (se 3 (by rfl) ⟨414158, by rfl⟩ : syracuseStep 2208845 = 828317) (by norm_num)
theorem B2208869 : Blo 1472556 2208869 := bbase (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) (by norm_num)
theorem B3314789 : Blo 1472556 3314789 := bbase (se 4 (by rfl) ⟨310761, by rfl⟩ : syracuseStep 3314789 = 621523) (by norm_num)
theorem B2126965 : Blo 1472556 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B2208893 : Blo 1472556 2208893 := bbase (se 3 (by rfl) ⟨414167, by rfl⟩ : syracuseStep 2208893 = 828335) (by norm_num)
theorem B2208917 : Blo 1472556 2208917 := bbase (se 6 (by rfl) ⟨51771, by rfl⟩ : syracuseStep 2208917 = 103543) (by norm_num)
theorem B1864873 : Blo 1472556 1864873 := bbase (se 2 (by rfl) ⟨699327, by rfl⟩ : syracuseStep 1864873 = 1398655) (by norm_num)
theorem B2208941 : Blo 1472556 2208941 := bbase (se 3 (by rfl) ⟨414176, by rfl⟩ : syracuseStep 2208941 = 828353) (by norm_num)
theorem B3314861 : Blo 1472556 3314861 := bbase (se 3 (by rfl) ⟨621536, by rfl⟩ : syracuseStep 3314861 = 1243073) (by norm_num)
theorem B2487469 : Blo 1472556 2487469 := bbase (se 3 (by rfl) ⟨466400, by rfl⟩ : syracuseStep 2487469 = 932801) (by norm_num)
theorem B2208965 : Blo 1472556 2208965 := bbase (se 4 (by rfl) ⟨207090, by rfl⟩ : syracuseStep 2208965 = 414181) (by norm_num)
theorem B2208989 : Blo 1472556 2208989 := bbase (se 3 (by rfl) ⟨414185, by rfl⟩ : syracuseStep 2208989 = 828371) (by norm_num)
theorem B2798813 : Blo 1472556 2798813 := bbase (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) (by norm_num)
theorem B2209013 : Blo 1472556 2209013 := bbase (se 5 (by rfl) ⟨103547, by rfl⟩ : syracuseStep 2209013 = 207095) (by norm_num)
theorem B3314933 : Blo 1472556 3314933 := bbase (se 5 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 3314933 = 310775) (by norm_num)
theorem B2487557 : Blo 1472556 2487557 := bbase (se 4 (by rfl) ⟨233208, by rfl⟩ : syracuseStep 2487557 = 466417) (by norm_num)
theorem B2209037 : Blo 1472556 2209037 := bbase (se 3 (by rfl) ⟨414194, by rfl⟩ : syracuseStep 2209037 = 828389) (by norm_num)
theorem B5592341 : Blo 1472556 5592341 := bbase (se 6 (by rfl) ⟨131070, by rfl⟩ : syracuseStep 5592341 = 262141) (by norm_num)
theorem B2209061 : Blo 1472556 2209061 := bbase (se 4 (by rfl) ⟨207099, by rfl⟩ : syracuseStep 2209061 = 414199) (by norm_num)
theorem B1594669 : Blo 1472556 1594669 := bbase (se 3 (by rfl) ⟨299000, by rfl⟩ : syracuseStep 1594669 = 598001) (by norm_num)
theorem B2209085 : Blo 1472556 2209085 := bbase (se 3 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 2209085 = 828407) (by norm_num)
theorem B3315005 : Blo 1472556 3315005 := bbase (se 3 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 3315005 = 1243127) (by norm_num)
theorem B2209109 : Blo 1472556 2209109 := bbase (se 13 (by rfl) ⟨404, by rfl⟩ : syracuseStep 2209109 = 809) (by norm_num)
theorem B1865045 : Blo 1472556 1865045 := bbase (se 13 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1865045 = 683) (by norm_num)
theorem B2209133 : Blo 1472556 2209133 := bbase (se 3 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 2209133 = 828425) (by norm_num)
theorem B2798965 : Blo 1472556 2798965 := bbase (se 5 (by rfl) ⟨131201, by rfl⟩ : syracuseStep 2798965 = 262403) (by norm_num)
theorem B2209157 : Blo 1472556 2209157 := bbase (se 4 (by rfl) ⟨207108, by rfl⟩ : syracuseStep 2209157 = 414217) (by norm_num)
theorem B3315077 : Blo 1472556 3315077 := bbase (se 4 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 3315077 = 621577) (by norm_num)
theorem B2487685 : Blo 1472556 2487685 := bbase (se 4 (by rfl) ⟨233220, by rfl⟩ : syracuseStep 2487685 = 466441) (by norm_num)
theorem B1865101 : Blo 1472556 1865101 := bbase (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) (by norm_num)
theorem B2209181 : Blo 1472556 2209181 := bbase (se 3 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 2209181 = 828443) (by norm_num)
theorem B7460261 : Blo 1472556 7460261 := bbase (se 4 (by rfl) ⟨699399, by rfl⟩ : syracuseStep 7460261 = 1398799) (by norm_num)
theorem B2209205 : Blo 1472556 2209205 := bbase (se 5 (by rfl) ⟨103556, by rfl⟩ : syracuseStep 2209205 = 207113) (by norm_num)
theorem B7558597 : Blo 1472556 7558597 := bbase (se 4 (by rfl) ⟨708618, by rfl⟩ : syracuseStep 7558597 = 1417237) (by norm_num)
theorem B2209229 : Blo 1472556 2209229 := bbase (se 3 (by rfl) ⟨414230, by rfl⟩ : syracuseStep 2209229 = 828461) (by norm_num)
theorem B3315149 : Blo 1472556 3315149 := bbase (se 3 (by rfl) ⟨621590, by rfl⟩ : syracuseStep 3315149 = 1243181) (by norm_num)
theorem B2487773 : Blo 1472556 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B2209253 : Blo 1472556 2209253 := bbase (se 4 (by rfl) ⟨207117, by rfl⟩ : syracuseStep 2209253 = 414235) (by norm_num)
theorem B1865197 : Blo 1472556 1865197 := bbase (se 3 (by rfl) ⟨349724, by rfl⟩ : syracuseStep 1865197 = 699449) (by norm_num)
theorem B2209277 : Blo 1472556 2209277 := bbase (se 3 (by rfl) ⟨414239, by rfl⟩ : syracuseStep 2209277 = 828479) (by norm_num)
theorem B2209301 : Blo 1472556 2209301 := bbase (se 6 (by rfl) ⟨51780, by rfl⟩ : syracuseStep 2209301 = 103561) (by norm_num)
theorem B3315221 : Blo 1472556 3315221 := bbase (se 6 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 3315221 = 155401) (by norm_num)
theorem B7083557 : Blo 1472556 7083557 := bbase (se 4 (by rfl) ⟨664083, by rfl⟩ : syracuseStep 7083557 = 1328167) (by norm_num)
theorem B2209325 : Blo 1472556 2209325 := bbase (se 3 (by rfl) ⟨414248, by rfl⟩ : syracuseStep 2209325 = 828497) (by norm_num)
theorem B2209349 : Blo 1472556 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B1513033 : Blo 1472556 1513033 := bbase (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) (by norm_num)
theorem B2209373 : Blo 1472556 2209373 := bbase (se 3 (by rfl) ⟨414257, by rfl⟩ : syracuseStep 2209373 = 828515) (by norm_num)
theorem B3315293 : Blo 1472556 3315293 := bbase (se 3 (by rfl) ⟨621617, by rfl⟩ : syracuseStep 3315293 = 1243235) (by norm_num)
theorem B2487901 : Blo 1472556 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B2209397 : Blo 1472556 2209397 := bbase (se 5 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 2209397 = 207131) (by norm_num)
theorem B2209421 : Blo 1472556 2209421 := bbase (se 3 (by rfl) ⟨414266, by rfl⟩ : syracuseStep 2209421 = 828533) (by norm_num)
theorem B1865369 : Blo 1472556 1865369 := bbase (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) (by norm_num)
theorem B2209445 : Blo 1472556 2209445 := bbase (se 4 (by rfl) ⟨207135, by rfl⟩ : syracuseStep 2209445 = 414271) (by norm_num)
theorem B3315365 : Blo 1472556 3315365 := bbase (se 4 (by rfl) ⟨310815, by rfl⟩ : syracuseStep 3315365 = 621631) (by norm_num)
theorem B2799269 : Blo 1472556 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B2487989 : Blo 1472556 2487989 := bbase (se 5 (by rfl) ⟨116624, by rfl⟩ : syracuseStep 2487989 = 233249) (by norm_num)
theorem B2209469 : Blo 1472556 2209469 := bbase (se 3 (by rfl) ⟨414275, by rfl⟩ : syracuseStep 2209469 = 828551) (by norm_num)
theorem B1865425 : Blo 1472556 1865425 := bbase (se 2 (by rfl) ⟨699534, by rfl⟩ : syracuseStep 1865425 = 1399069) (by norm_num)
theorem B2209493 : Blo 1472556 2209493 := bbase (se 7 (by rfl) ⟨25892, by rfl⟩ : syracuseStep 2209493 = 51785) (by norm_num)
theorem B4970213 : Blo 1472556 4970213 := bbase (se 4 (by rfl) ⟨465957, by rfl⟩ : syracuseStep 4970213 = 931915) (by norm_num)
theorem B2209517 : Blo 1472556 2209517 := bbase (se 3 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 2209517 = 828569) (by norm_num)
theorem B3315437 : Blo 1472556 3315437 := bbase (se 3 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 3315437 = 1243289) (by norm_num)
theorem B1595137 : Blo 1472556 1595137 := bbase (se 2 (by rfl) ⟨598176, by rfl⟩ : syracuseStep 1595137 = 1196353) (by norm_num)
theorem B2209541 : Blo 1472556 2209541 := bbase (se 4 (by rfl) ⟨207144, by rfl⟩ : syracuseStep 2209541 = 414289) (by norm_num)
theorem B6297365 : Blo 1472556 6297365 := bbase (se 6 (by rfl) ⟨147594, by rfl⟩ : syracuseStep 6297365 = 295189) (by norm_num)
theorem B2209565 : Blo 1472556 2209565 := bbase (se 3 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 2209565 = 828587) (by norm_num)
theorem B1865521 : Blo 1472556 1865521 := bbase (se 2 (by rfl) ⟨699570, by rfl⟩ : syracuseStep 1865521 = 1399141) (by norm_num)
theorem B2209589 : Blo 1472556 2209589 := bbase (se 5 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 2209589 = 207149) (by norm_num)
theorem B3315509 : Blo 1472556 3315509 := bbase (se 5 (by rfl) ⟨155414, by rfl⟩ : syracuseStep 3315509 = 310829) (by norm_num)
theorem B2488117 : Blo 1472556 2488117 := bbase (se 5 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 2488117 = 233261) (by norm_num)
theorem B2209613 : Blo 1472556 2209613 := bbase (se 3 (by rfl) ⟨414302, by rfl⟩ : syracuseStep 2209613 = 828605) (by norm_num)
theorem B2209637 : Blo 1472556 2209637 := bbase (se 4 (by rfl) ⟨207153, by rfl⟩ : syracuseStep 2209637 = 414307) (by norm_num)
theorem B2209661 : Blo 1472556 2209661 := bbase (se 3 (by rfl) ⟨414311, by rfl⟩ : syracuseStep 2209661 = 828623) (by norm_num)
theorem B3315581 : Blo 1472556 3315581 := bbase (se 3 (by rfl) ⟨621671, by rfl⟩ : syracuseStep 3315581 = 1243343) (by norm_num)
theorem B2488205 : Blo 1472556 2488205 := bbase (se 3 (by rfl) ⟨466538, by rfl⟩ : syracuseStep 2488205 = 933077) (by norm_num)
theorem B2209685 : Blo 1472556 2209685 := bbase (se 6 (by rfl) ⟨51789, by rfl⟩ : syracuseStep 2209685 = 103579) (by norm_num)
theorem B2209709 : Blo 1472556 2209709 := bbase (se 3 (by rfl) ⟨414320, by rfl⟩ : syracuseStep 2209709 = 828641) (by norm_num)
theorem B2209733 : Blo 1472556 2209733 := bbase (se 4 (by rfl) ⟨207162, by rfl⟩ : syracuseStep 2209733 = 414325) (by norm_num)
theorem B3315653 : Blo 1472556 3315653 := bbase (se 4 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 3315653 = 621685) (by norm_num)
theorem B45357013 : Blo 1472556 45357013 := bbase (se 7 (by rfl) ⟨531527, by rfl⟩ : syracuseStep 45357013 = 1063055) (by norm_num)
theorem B2209757 : Blo 1472556 2209757 := bbase (se 3 (by rfl) ⟨414329, by rfl⟩ : syracuseStep 2209757 = 828659) (by norm_num)
theorem B1865693 : Blo 1472556 1865693 := bbase (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) (by norm_num)
theorem B2209781 : Blo 1472556 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B2209805 : Blo 1472556 2209805 := bbase (se 3 (by rfl) ⟨414338, by rfl⟩ : syracuseStep 2209805 = 828677) (by norm_num)
theorem B3315725 : Blo 1472556 3315725 := bbase (se 3 (by rfl) ⟨621698, by rfl⟩ : syracuseStep 3315725 = 1243397) (by norm_num)
theorem B1865749 : Blo 1472556 1865749 := bbase (se 6 (by rfl) ⟨43728, by rfl⟩ : syracuseStep 1865749 = 87457) (by norm_num)
theorem B2209829 : Blo 1472556 2209829 := bbase (se 4 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 2209829 = 414343) (by norm_num)
theorem B2209853 : Blo 1472556 2209853 := bbase (se 3 (by rfl) ⟨414347, by rfl⟩ : syracuseStep 2209853 = 828695) (by norm_num)
theorem B2209877 : Blo 1472556 2209877 := bbase (se 8 (by rfl) ⟨12948, by rfl⟩ : syracuseStep 2209877 = 25897) (by norm_num)
theorem B3315797 : Blo 1472556 3315797 := bbase (se 8 (by rfl) ⟨19428, by rfl⟩ : syracuseStep 3315797 = 38857) (by norm_num)
theorem B2209901 : Blo 1472556 2209901 := bbase (se 3 (by rfl) ⟨414356, by rfl⟩ : syracuseStep 2209901 = 828713) (by norm_num)
theorem B1865845 : Blo 1472556 1865845 := bbase (se 5 (by rfl) ⟨87461, by rfl⟩ : syracuseStep 1865845 = 174923) (by norm_num)
theorem B2209925 : Blo 1472556 2209925 := bbase (se 4 (by rfl) ⟨207180, by rfl⟩ : syracuseStep 2209925 = 414361) (by norm_num)
theorem B4970645 : Blo 1472556 4970645 := bbase (se 6 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 4970645 = 232999) (by norm_num)
theorem B2209949 : Blo 1472556 2209949 := bbase (se 3 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 2209949 = 828731) (by norm_num)
theorem B3315869 : Blo 1472556 3315869 := bbase (se 3 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 3315869 = 1243451) (by norm_num)
theorem B2209973 : Blo 1472556 2209973 := bbase (se 5 (by rfl) ⟨103592, by rfl⟩ : syracuseStep 2209973 = 207185) (by norm_num)
theorem B2209997 : Blo 1472556 2209997 := bbase (se 3 (by rfl) ⟨414374, by rfl⟩ : syracuseStep 2209997 = 828749) (by norm_num)
theorem B2210021 : Blo 1472556 2210021 := bbase (se 4 (by rfl) ⟨207189, by rfl⟩ : syracuseStep 2210021 = 414379) (by norm_num)
theorem B3315941 : Blo 1472556 3315941 := bbase (se 4 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 3315941 = 621739) (by norm_num)
theorem B2210045 : Blo 1472556 2210045 := bbase (se 3 (by rfl) ⟨414383, by rfl⟩ : syracuseStep 2210045 = 828767) (by norm_num)
theorem B2210069 : Blo 1472556 2210069 := bbase (se 6 (by rfl) ⟨51798, by rfl⟩ : syracuseStep 2210069 = 103597) (by norm_num)
theorem B1866017 : Blo 1472556 1866017 := bbase (se 2 (by rfl) ⟨699756, by rfl⟩ : syracuseStep 1866017 = 1399513) (by norm_num)
theorem B2210093 : Blo 1472556 2210093 := bbase (se 3 (by rfl) ⟨414392, by rfl⟩ : syracuseStep 2210093 = 828785) (by norm_num)
theorem B3316013 : Blo 1472556 3316013 := bbase (se 3 (by rfl) ⟨621752, by rfl⟩ : syracuseStep 3316013 = 1243505) (by norm_num)
theorem B2210117 : Blo 1472556 2210117 := bbase (se 4 (by rfl) ⟨207198, by rfl⟩ : syracuseStep 2210117 = 414397) (by norm_num)
theorem B1866073 : Blo 1472556 1866073 := bbase (se 2 (by rfl) ⟨699777, by rfl⟩ : syracuseStep 1866073 = 1399555) (by norm_num)
theorem B2210141 : Blo 1472556 2210141 := bbase (se 3 (by rfl) ⟨414401, by rfl⟩ : syracuseStep 2210141 = 828803) (by norm_num)
theorem B2210165 : Blo 1472556 2210165 := bbase (se 5 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 2210165 = 207203) (by norm_num)
theorem B3316085 : Blo 1472556 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B1890697 : Blo 1472556 1890697 := bbase (se 2 (by rfl) ⟨709011, by rfl⟩ : syracuseStep 1890697 = 1418023) (by norm_num)
theorem B2210189 : Blo 1472556 2210189 := bbase (se 3 (by rfl) ⟨414410, by rfl⟩ : syracuseStep 2210189 = 828821) (by norm_num)
theorem B1890713 : Blo 1472556 1890713 := bbase (se 2 (by rfl) ⟨709017, by rfl⟩ : syracuseStep 1890713 = 1418035) (by norm_num)
theorem B2210213 : Blo 1472556 2210213 := bbase (se 4 (by rfl) ⟨207207, by rfl⟩ : syracuseStep 2210213 = 414415) (by norm_num)
theorem B1866169 : Blo 1472556 1866169 := bbase (se 2 (by rfl) ⟨699813, by rfl⟩ : syracuseStep 1866169 = 1399627) (by norm_num)
theorem B2210237 : Blo 1472556 2210237 := bbase (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) (by norm_num)
theorem B3316157 : Blo 1472556 3316157 := bbase (se 3 (by rfl) ⟨621779, by rfl⟩ : syracuseStep 3316157 = 1243559) (by norm_num)
theorem B2210261 : Blo 1472556 2210261 := bbase (se 7 (by rfl) ⟨25901, by rfl⟩ : syracuseStep 2210261 = 51803) (by norm_num)
theorem B2210285 : Blo 1472556 2210285 := bbase (se 3 (by rfl) ⟨414428, by rfl⟩ : syracuseStep 2210285 = 828857) (by norm_num)
theorem B2210309 : Blo 1472556 2210309 := bbase (se 4 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 2210309 = 414433) (by norm_num)
theorem B3316229 : Blo 1472556 3316229 := bbase (se 4 (by rfl) ⟨310896, by rfl⟩ : syracuseStep 3316229 = 621793) (by norm_num)
theorem B2521613 : Blo 1472556 2521613 := bbase (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) (by norm_num)
theorem B2210333 : Blo 1472556 2210333 := bbase (se 3 (by rfl) ⟨414437, by rfl⟩ : syracuseStep 2210333 = 828875) (by norm_num)
theorem B2210357 : Blo 1472556 2210357 := bbase (se 5 (by rfl) ⟨103610, by rfl⟩ : syracuseStep 2210357 = 207221) (by norm_num)
theorem B4971077 : Blo 1472556 4971077 := bbase (se 4 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 4971077 = 932077) (by norm_num)
theorem B2210381 : Blo 1472556 2210381 := bbase (se 3 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 2210381 = 828893) (by norm_num)
theorem B3316301 : Blo 1472556 3316301 := bbase (se 3 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 3316301 = 1243613) (by norm_num)
theorem B2210405 : Blo 1472556 2210405 := bbase (se 4 (by rfl) ⟨207225, by rfl⟩ : syracuseStep 2210405 = 414451) (by norm_num)
theorem B12270197 : Blo 1472556 12270197 := bbase (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) (by norm_num)
theorem B2210429 : Blo 1472556 2210429 := bbase (se 3 (by rfl) ⟨414455, by rfl⟩ : syracuseStep 2210429 = 828911) (by norm_num)
theorem B30227093 : Blo 1472556 30227093 := bbase (se 6 (by rfl) ⟨708447, by rfl⟩ : syracuseStep 30227093 = 1416895) (by norm_num)
theorem B7961237 : Blo 1472556 7961237 := bbase (se 6 (by rfl) ⟨186591, by rfl⟩ : syracuseStep 7961237 = 373183) (by norm_num)
theorem B9435797 : Blo 1472556 9435797 := bbase (se 6 (by rfl) ⟨221151, by rfl⟩ : syracuseStep 9435797 = 442303) (by norm_num)
theorem B2210453 : Blo 1472556 2210453 := bbase (se 6 (by rfl) ⟨51807, by rfl⟩ : syracuseStep 2210453 = 103615) (by norm_num)
theorem B3316373 : Blo 1472556 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B2210477 : Blo 1472556 2210477 := bbase (se 3 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 2210477 = 828929) (by norm_num)
theorem B7461557 : Blo 1472556 7461557 := bbase (se 5 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 7461557 = 699521) (by norm_num)
theorem B2210501 : Blo 1472556 2210501 := bbase (se 4 (by rfl) ⟨207234, by rfl⟩ : syracuseStep 2210501 = 414469) (by norm_num)
theorem B2210525 : Blo 1472556 2210525 := bbase (se 3 (by rfl) ⟨414473, by rfl⟩ : syracuseStep 2210525 = 828947) (by norm_num)
theorem B3316445 : Blo 1472556 3316445 := bbase (se 3 (by rfl) ⟨621833, by rfl⟩ : syracuseStep 3316445 = 1243667) (by norm_num)
theorem B1891045 : Blo 1472556 1891045 := bbase (se 4 (by rfl) ⟨177285, by rfl⟩ : syracuseStep 1891045 = 354571) (by norm_num)
theorem B2210549 : Blo 1472556 2210549 := bbase (se 5 (by rfl) ⟨103619, by rfl⟩ : syracuseStep 2210549 = 207239) (by norm_num)
theorem B2210573 : Blo 1472556 2210573 := bbase (se 3 (by rfl) ⟨414482, by rfl⟩ : syracuseStep 2210573 = 828965) (by norm_num)
theorem B2210597 : Blo 1472556 2210597 := bbase (se 4 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 2210597 = 414487) (by norm_num)
theorem B3316517 : Blo 1472556 3316517 := bbase (se 4 (by rfl) ⟨310923, by rfl⟩ : syracuseStep 3316517 = 621847) (by norm_num)
theorem B2210621 : Blo 1472556 2210621 := bbase (se 3 (by rfl) ⟨414491, by rfl⟩ : syracuseStep 2210621 = 828983) (by norm_num)
theorem B2210645 : Blo 1472556 2210645 := bbase (se 9 (by rfl) ⟨6476, by rfl⟩ : syracuseStep 2210645 = 12953) (by norm_num)
theorem B3406693 : Blo 1472556 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B2210669 : Blo 1472556 2210669 := bbase (se 3 (by rfl) ⟨414500, by rfl⟩ : syracuseStep 2210669 = 829001) (by norm_num)
theorem B3316589 : Blo 1472556 3316589 := bbase (se 3 (by rfl) ⟨621860, by rfl⟩ : syracuseStep 3316589 = 1243721) (by norm_num)
theorem B2210693 : Blo 1472556 2210693 := bbase (se 4 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 2210693 = 414505) (by norm_num)
theorem B2210717 : Blo 1472556 2210717 := bbase (se 3 (by rfl) ⟨414509, by rfl⟩ : syracuseStep 2210717 = 829019) (by norm_num)
theorem B8387509 : Blo 1472556 8387509 := bbase (se 5 (by rfl) ⟨393164, by rfl⟩ : syracuseStep 8387509 = 786329) (by norm_num)
theorem B2210741 : Blo 1472556 2210741 := bbase (se 5 (by rfl) ⟨103628, by rfl⟩ : syracuseStep 2210741 = 207257) (by norm_num)
theorem B3316661 : Blo 1472556 3316661 := bbase (se 5 (by rfl) ⟨155468, by rfl⟩ : syracuseStep 3316661 = 310937) (by norm_num)
theorem B2210765 : Blo 1472556 2210765 := bbase (se 3 (by rfl) ⟨414518, by rfl⟩ : syracuseStep 2210765 = 829037) (by norm_num)
theorem B2210789 : Blo 1472556 2210789 := bbase (se 4 (by rfl) ⟨207261, by rfl⟩ : syracuseStep 2210789 = 414523) (by norm_num)
theorem B4971509 : Blo 1472556 4971509 := bbase (se 5 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 4971509 = 466079) (by norm_num)
theorem B2210813 : Blo 1472556 2210813 := bbase (se 3 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 2210813 = 829055) (by norm_num)
theorem B3316733 : Blo 1472556 3316733 := bbase (se 3 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 3316733 = 1243775) (by norm_num)
theorem B2210837 : Blo 1472556 2210837 := bbase (se 6 (by rfl) ⟨51816, by rfl⟩ : syracuseStep 2210837 = 103633) (by norm_num)
theorem B2210861 : Blo 1472556 2210861 := bbase (se 3 (by rfl) ⟨414536, by rfl⟩ : syracuseStep 2210861 = 829073) (by norm_num)
theorem B2210885 : Blo 1472556 2210885 := bbase (se 4 (by rfl) ⟨207270, by rfl⟩ : syracuseStep 2210885 = 414541) (by norm_num)
theorem B3316805 : Blo 1472556 3316805 := bbase (se 4 (by rfl) ⟨310950, by rfl⟩ : syracuseStep 3316805 = 621901) (by norm_num)
theorem B2210909 : Blo 1472556 2210909 := bbase (se 3 (by rfl) ⟨414545, by rfl⟩ : syracuseStep 2210909 = 829091) (by norm_num)
theorem B2210933 : Blo 1472556 2210933 := bbase (se 5 (by rfl) ⟨103637, by rfl⟩ : syracuseStep 2210933 = 207275) (by norm_num)
theorem B2210957 : Blo 1472556 2210957 := bbase (se 3 (by rfl) ⟨414554, by rfl⟩ : syracuseStep 2210957 = 829109) (by norm_num)
theorem B3316877 : Blo 1472556 3316877 := bbase (se 3 (by rfl) ⟨621914, by rfl⟩ : syracuseStep 3316877 = 1243829) (by norm_num)
theorem B2210981 : Blo 1472556 2210981 := bbase (se 4 (by rfl) ⟨207279, by rfl⟩ : syracuseStep 2210981 = 414559) (by norm_num)
theorem B2211005 : Blo 1472556 2211005 := bbase (se 3 (by rfl) ⟨414563, by rfl⟩ : syracuseStep 2211005 = 829127) (by norm_num)
theorem B11943125 : Blo 1472556 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B21232853 : Blo 1472556 21232853 := bbase (se 7 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 21232853 = 497645) (by norm_num)
theorem B2211029 : Blo 1472556 2211029 := bbase (se 7 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 2211029 = 51821) (by norm_num)
theorem B3316949 : Blo 1472556 3316949 := bbase (se 7 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 3316949 = 77741) (by norm_num)
theorem B2211053 : Blo 1472556 2211053 := bbase (se 3 (by rfl) ⟨414572, by rfl⟩ : syracuseStep 2211053 = 829145) (by norm_num)
theorem B2211077 : Blo 1472556 2211077 := bbase (se 4 (by rfl) ⟨207288, by rfl⟩ : syracuseStep 2211077 = 414577) (by norm_num)
theorem B2989325 : Blo 1472556 2989325 := bbase (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) (by norm_num)
theorem B2211101 : Blo 1472556 2211101 := bbase (se 3 (by rfl) ⟨414581, by rfl⟩ : syracuseStep 2211101 = 829163) (by norm_num)
theorem B3317021 : Blo 1472556 3317021 := bbase (se 3 (by rfl) ⟨621941, by rfl⟩ : syracuseStep 3317021 = 1243883) (by norm_num)
theorem B2211125 : Blo 1472556 2211125 := bbase (se 5 (by rfl) ⟨103646, by rfl⟩ : syracuseStep 2211125 = 207293) (by norm_num)
theorem B2211149 : Blo 1472556 2211149 := bbase (se 3 (by rfl) ⟨414590, by rfl⟩ : syracuseStep 2211149 = 829181) (by norm_num)
theorem B5594453 : Blo 1472556 5594453 := bbase (se 11 (by rfl) ⟨4097, by rfl⟩ : syracuseStep 5594453 = 8195) (by norm_num)
theorem B3145061 : Blo 1472556 3145061 := bbase (se 4 (by rfl) ⟨294849, by rfl⟩ : syracuseStep 3145061 = 589699) (by norm_num)
theorem B2211173 : Blo 1472556 2211173 := bbase (se 4 (by rfl) ⟨207297, by rfl⟩ : syracuseStep 2211173 = 414595) (by norm_num)
theorem B3317093 : Blo 1472556 3317093 := bbase (se 4 (by rfl) ⟨310977, by rfl⟩ : syracuseStep 3317093 = 621955) (by norm_num)
theorem B4193653 : Blo 1472556 4193653 := bbase (se 5 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 4193653 = 393155) (by norm_num)
theorem B2211197 : Blo 1472556 2211197 := bbase (se 3 (by rfl) ⟨414599, by rfl⟩ : syracuseStep 2211197 = 829199) (by norm_num)
theorem B5307781 : Blo 1472556 5307781 := bbase (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) (by norm_num)
theorem B7077253 : Blo 1472556 7077253 := bbase (se 4 (by rfl) ⟨663492, by rfl⟩ : syracuseStep 7077253 = 1326985) (by norm_num)
theorem B7077269 : Blo 1472556 7077269 := bbase (se 6 (by rfl) ⟨165873, by rfl⟩ : syracuseStep 7077269 = 331747) (by norm_num)
theorem B5750165 : Blo 1472556 5750165 := bbase (se 6 (by rfl) ⟨134769, by rfl⟩ : syracuseStep 5750165 = 269539) (by norm_num)
theorem B2211221 : Blo 1472556 2211221 := bbase (se 6 (by rfl) ⟨51825, by rfl⟩ : syracuseStep 2211221 = 103651) (by norm_num)
theorem B4971941 : Blo 1472556 4971941 := bbase (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) (by norm_num)
theorem B2211245 : Blo 1472556 2211245 := bbase (se 3 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 2211245 = 829217) (by norm_num)
theorem B3317165 : Blo 1472556 3317165 := bbase (se 3 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 3317165 = 1243937) (by norm_num)
theorem B2211269 : Blo 1472556 2211269 := bbase (se 4 (by rfl) ⟨207306, by rfl⟩ : syracuseStep 2211269 = 414613) (by norm_num)
theorem B2211293 : Blo 1472556 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B2358757 : Blo 1472556 2358757 := bbase (se 4 (by rfl) ⟨221133, by rfl⟩ : syracuseStep 2358757 = 442267) (by norm_num)
theorem B1916389 : Blo 1472556 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B11943413 : Blo 1472556 11943413 := bbase (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) (by norm_num)
theorem B2211317 : Blo 1472556 2211317 := bbase (se 5 (by rfl) ⟨103655, by rfl⟩ : syracuseStep 2211317 = 207311) (by norm_num)
theorem B3317237 : Blo 1472556 3317237 := bbase (se 5 (by rfl) ⟨155495, by rfl⟩ : syracuseStep 3317237 = 310991) (by norm_num)
theorem B7085573 : Blo 1472556 7085573 := bbase (se 4 (by rfl) ⟨664272, by rfl⟩ : syracuseStep 7085573 = 1328545) (by norm_num)
theorem B2211341 : Blo 1472556 2211341 := bbase (se 3 (by rfl) ⟨414626, by rfl⟩ : syracuseStep 2211341 = 829253) (by norm_num)
theorem B2653717 : Blo 1472556 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B2211365 : Blo 1472556 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B2211389 : Blo 1472556 2211389 := bbase (se 3 (by rfl) ⟨414635, by rfl⟩ : syracuseStep 2211389 = 829271) (by norm_num)
theorem B3317309 : Blo 1472556 3317309 := bbase (se 3 (by rfl) ⟨621995, by rfl⟩ : syracuseStep 3317309 = 1243991) (by norm_num)
theorem B2211413 : Blo 1472556 2211413 := bbase (se 8 (by rfl) ⟨12957, by rfl⟩ : syracuseStep 2211413 = 25915) (by norm_num)
theorem B2211437 : Blo 1472556 2211437 := bbase (se 3 (by rfl) ⟨414644, by rfl⟩ : syracuseStep 2211437 = 829289) (by norm_num)
theorem B5594741 : Blo 1472556 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B2211461 : Blo 1472556 2211461 := bbase (se 4 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 2211461 = 414649) (by norm_num)
theorem B3317381 : Blo 1472556 3317381 := bbase (se 4 (by rfl) ⟨311004, by rfl⟩ : syracuseStep 3317381 = 622009) (by norm_num)
theorem B2211485 : Blo 1472556 2211485 := bbase (se 3 (by rfl) ⟨414653, by rfl⟩ : syracuseStep 2211485 = 829307) (by norm_num)
theorem B2211509 : Blo 1472556 2211509 := bbase (se 5 (by rfl) ⟨103664, by rfl⟩ : syracuseStep 2211509 = 207329) (by norm_num)
theorem B2211533 : Blo 1472556 2211533 := bbase (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) (by norm_num)
theorem B3317453 : Blo 1472556 3317453 := bbase (se 3 (by rfl) ⟨622022, by rfl⟩ : syracuseStep 3317453 = 1244045) (by norm_num)
theorem B4038373 : Blo 1472556 4038373 := bbase (se 4 (by rfl) ⟨378597, by rfl⟩ : syracuseStep 4038373 = 757195) (by norm_num)
theorem B2211557 : Blo 1472556 2211557 := bbase (se 4 (by rfl) ⟨207333, by rfl⟩ : syracuseStep 2211557 = 414667) (by norm_num)
theorem B2211581 : Blo 1472556 2211581 := bbase (se 3 (by rfl) ⟨414671, by rfl⟩ : syracuseStep 2211581 = 829343) (by norm_num)
theorem B2211605 : Blo 1472556 2211605 := bbase (se 6 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 2211605 = 103669) (by norm_num)
theorem B3317525 : Blo 1472556 3317525 := bbase (se 6 (by rfl) ⟨77754, by rfl⟩ : syracuseStep 3317525 = 155509) (by norm_num)
theorem B4038437 : Blo 1472556 4038437 := bbase (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) (by norm_num)
theorem B2211629 : Blo 1472556 2211629 := bbase (se 3 (by rfl) ⟨414680, by rfl⟩ : syracuseStep 2211629 = 829361) (by norm_num)
theorem B2211653 : Blo 1472556 2211653 := bbase (se 4 (by rfl) ⟨207342, by rfl⟩ : syracuseStep 2211653 = 414685) (by norm_num)
theorem B4972373 : Blo 1472556 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B1572701 : Blo 1472556 1572701 := bbase (se 3 (by rfl) ⟨294881, by rfl⟩ : syracuseStep 1572701 = 589763) (by norm_num)
theorem B2211677 : Blo 1472556 2211677 := bbase (se 3 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 2211677 = 829379) (by norm_num)
theorem B3317597 : Blo 1472556 3317597 := bbase (se 3 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 3317597 = 1244099) (by norm_num)
theorem B12115829 : Blo 1472556 12115829 := bbase (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) (by norm_num)
theorem B2211701 : Blo 1472556 2211701 := bbase (se 5 (by rfl) ⟨103673, by rfl⟩ : syracuseStep 2211701 = 207347) (by norm_num)
theorem B2097037 : Blo 1472556 2097037 := bbase (se 3 (by rfl) ⟨393194, by rfl⟩ : syracuseStep 2097037 = 786389) (by norm_num)
theorem B2211725 : Blo 1472556 2211725 := bbase (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) (by norm_num)
theorem B2662301 : Blo 1472556 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B2211749 : Blo 1472556 2211749 := bbase (se 4 (by rfl) ⟨207351, by rfl⟩ : syracuseStep 2211749 = 414703) (by norm_num)
theorem B3317669 : Blo 1472556 3317669 := bbase (se 4 (by rfl) ⟨311031, by rfl⟩ : syracuseStep 3317669 = 622063) (by norm_num)
theorem B2211773 : Blo 1472556 2211773 := bbase (se 3 (by rfl) ⟨414707, by rfl⟩ : syracuseStep 2211773 = 829415) (by norm_num)
theorem B1679297 : Blo 1472556 1679297 := bbase (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) (by norm_num)
theorem B3538885 : Blo 1472556 3538885 := bbase (se 4 (by rfl) ⟨331770, by rfl⟩ : syracuseStep 3538885 = 663541) (by norm_num)
theorem B7462853 : Blo 1472556 7462853 := bbase (se 4 (by rfl) ⟨699642, by rfl⟩ : syracuseStep 7462853 = 1399285) (by norm_num)
theorem B2211797 : Blo 1472556 2211797 := bbase (se 7 (by rfl) ⟨25919, by rfl⟩ : syracuseStep 2211797 = 51839) (by norm_num)
theorem B2211821 : Blo 1472556 2211821 := bbase (se 3 (by rfl) ⟨414716, by rfl⟩ : syracuseStep 2211821 = 829433) (by norm_num)
theorem B3317741 : Blo 1472556 3317741 := bbase (se 3 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 3317741 = 1244153) (by norm_num)
theorem B4972589 : Blo 1472556 4972589 := bstep (se 3 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 4972589 = 1864721) B1864721
theorem B3539011 : Blo 1472556 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B4972643 : Blo 1472556 4972643 := bstep (se 1 (by rfl) ⟨3729482, by rfl⟩ : syracuseStep 4972643 = 7458965) B7458965
theorem B2097265 : Blo 1472556 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B2097299 : Blo 1472556 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B8388785 : Blo 1472556 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B1769683 : Blo 1472556 1769683 := bstep (se 1 (by rfl) ⟨1327262, by rfl⟩ : syracuseStep 1769683 = 2654525) B2654525
theorem B4972913 : Blo 1472556 4972913 := bstep (se 2 (by rfl) ⟨1864842, by rfl⟩ : syracuseStep 4972913 = 3729685) B3729685
theorem B2359667 : Blo 1472556 2359667 := bstep (se 1 (by rfl) ⟨1769750, by rfl⟩ : syracuseStep 2359667 = 3539501) B3539501
theorem B8069509 : Blo 1472556 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B7463501 : Blo 1472556 7463501 := bstep (se 3 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 7463501 = 2798813) B2798813
theorem B9437795 : Blo 1472556 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B4194929 : Blo 1472556 4194929 := bstep (se 2 (by rfl) ⟨1573098, by rfl⟩ : syracuseStep 4194929 = 3146197) B3146197
theorem B1991315 : Blo 1472556 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B6816419 : Blo 1472556 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B1991347 : Blo 1472556 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B1770163 : Blo 1472556 1770163 := bstep (se 1 (by rfl) ⟨1327622, by rfl⟩ : syracuseStep 1770163 = 2655245) B2655245
theorem B2097857 : Blo 1472556 2097857 := bstep (se 2 (by rfl) ⟨786696, by rfl⟩ : syracuseStep 2097857 = 1573393) B1573393
theorem B7971533 : Blo 1472556 7971533 := bstep (se 3 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 7971533 = 2989325) B2989325
theorem B2097937 : Blo 1472556 2097937 := bstep (se 2 (by rfl) ⟨786726, by rfl⟩ : syracuseStep 2097937 = 1573453) B1573453
theorem B3728177 : Blo 1472556 3728177 := bstep (se 2 (by rfl) ⟨1398066, by rfl⟩ : syracuseStep 3728177 = 2796133) B2796133
theorem B3728227 : Blo 1472556 3728227 := bstep (se 1 (by rfl) ⟨2796170, by rfl⟩ : syracuseStep 3728227 = 5592341) B5592341
theorem B4973453 : Blo 1472556 4973453 := bstep (se 3 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 4973453 = 1865045) B1865045
theorem B3539857 : Blo 1472556 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B4973507 : Blo 1472556 4973507 := bstep (se 1 (by rfl) ⟨3730130, by rfl⟩ : syracuseStep 4973507 = 7460261) B7460261
theorem B3728369 : Blo 1472556 3728369 := bstep (se 2 (by rfl) ⟨1398138, by rfl⟩ : syracuseStep 3728369 = 2796277) B2796277
theorem B1573987 : Blo 1472556 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B15926453 : Blo 1472556 15926453 := bstep (se 5 (by rfl) ⟨746552, by rfl⟩ : syracuseStep 15926453 = 1493105) B1493105
theorem B10085573 : Blo 1472556 10085573 := bstep (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) B1891045
theorem B4973777 : Blo 1472556 4973777 := bstep (se 2 (by rfl) ⟨1865166, by rfl⟩ : syracuseStep 4973777 = 3730333) B3730333
theorem B11183345 : Blo 1472556 11183345 := bstep (se 2 (by rfl) ⟨4193754, by rfl⟩ : syracuseStep 11183345 = 8387509) B8387509
theorem B4195601 : Blo 1472556 4195601 := bstep (se 2 (by rfl) ⟨1573350, by rfl⟩ : syracuseStep 4195601 = 3146701) B3146701
theorem B3147025 : Blo 1472556 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B1991953 : Blo 1472556 1991953 := bstep (se 2 (by rfl) ⟨746982, by rfl⟩ : syracuseStep 1991953 = 1493965) B1493965
theorem B7456049 : Blo 1472556 7456049 := bstep (se 2 (by rfl) ⟨2796018, by rfl⟩ : syracuseStep 7456049 = 5592037) B5592037
theorem B7079309 : Blo 1472556 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B2835953 : Blo 1472556 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B5596685 : Blo 1472556 5596685 := bstep (se 3 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 5596685 = 2098757) B2098757
theorem B2098723 : Blo 1472556 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B1771043 : Blo 1472556 1771043 := bstep (se 1 (by rfl) ⟨1328282, by rfl⟩ : syracuseStep 1771043 = 2656565) B2656565
theorem B1574435 : Blo 1472556 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B7079501 : Blo 1472556 7079501 := bstep (se 3 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 7079501 = 2654813) B2654813
theorem B5310029 : Blo 1472556 5310029 := bstep (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) B1991261
theorem B8390243 : Blo 1472556 8390243 := bstep (se 1 (by rfl) ⟨6292682, by rfl⟩ : syracuseStep 8390243 = 12585365) B12585365
theorem B17925731 : Blo 1472556 17925731 := bstep (se 1 (by rfl) ⟨13444298, by rfl⟩ : syracuseStep 17925731 = 26888597) B26888597
theorem B32720525 : Blo 1472556 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B3147427 : Blo 1472556 3147427 := bstep (se 1 (by rfl) ⟨2360570, by rfl⟩ : syracuseStep 3147427 = 4721141) B4721141
theorem B1681075 : Blo 1472556 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B4974317 : Blo 1472556 4974317 := bstep (se 3 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 4974317 = 1865369) B1865369
theorem B2361089 : Blo 1472556 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B4974371 : Blo 1472556 4974371 := bstep (se 1 (by rfl) ⟨3730778, by rfl⟩ : syracuseStep 4974371 = 7461557) B7461557
theorem B7079729 : Blo 1472556 7079729 := bstep (se 2 (by rfl) ⟨2654898, by rfl⟩ : syracuseStep 7079729 = 5309797) B5309797
theorem B1656643 : Blo 1472556 1656643 := bstep (se 1 (by rfl) ⟨1242482, by rfl⟩ : syracuseStep 1656643 = 2484965) B2484965
theorem B2393939 : Blo 1472556 2393939 := bstep (se 1 (by rfl) ⟨1795454, by rfl⟩ : syracuseStep 2393939 = 3590909) B3590909
theorem B10078129 : Blo 1472556 10078129 := bstep (se 2 (by rfl) ⟨3779298, by rfl⟩ : syracuseStep 10078129 = 7558597) B7558597
theorem B7079885 : Blo 1472556 7079885 := bstep (se 3 (by rfl) ⟨1327478, by rfl⟩ : syracuseStep 7079885 = 2654957) B2654957
theorem B4720589 : Blo 1472556 4720589 := bstep (se 3 (by rfl) ⟨885110, by rfl⟩ : syracuseStep 4720589 = 1770221) B1770221
theorem B3729361 : Blo 1472556 3729361 := bstep (se 2 (by rfl) ⟨1398510, by rfl⟩ : syracuseStep 3729361 = 2797021) B2797021
theorem B1656787 : Blo 1472556 1656787 := bstep (se 1 (by rfl) ⟨1242590, by rfl⟩ : syracuseStep 1656787 = 2485181) B2485181
theorem B2099201 : Blo 1472556 2099201 := bstep (se 2 (by rfl) ⟨787200, by rfl⟩ : syracuseStep 2099201 = 1574401) B1574401
theorem B4196387 : Blo 1472556 4196387 := bstep (se 1 (by rfl) ⟨3147290, by rfl⟩ : syracuseStep 4196387 = 6294581) B6294581
theorem B4974641 : Blo 1472556 4974641 := bstep (se 2 (by rfl) ⟨1865490, by rfl⟩ : syracuseStep 4974641 = 3730981) B3730981
theorem B1656931 : Blo 1472556 1656931 := bstep (se 1 (by rfl) ⟨1242698, by rfl⟩ : syracuseStep 1656931 = 2485397) B2485397
theorem B2099315 : Blo 1472556 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B7964849 : Blo 1472556 7964849 := bstep (se 2 (by rfl) ⟨2986818, by rfl⟩ : syracuseStep 7964849 = 5973637) B5973637
theorem B2099395 : Blo 1472556 2099395 := bstep (se 1 (by rfl) ⟨1574546, by rfl⟩ : syracuseStep 2099395 = 3149093) B3149093
theorem B3729635 : Blo 1472556 3729635 := bstep (se 1 (by rfl) ⟨2797226, by rfl⟩ : syracuseStep 3729635 = 5594453) B5594453
theorem B1657075 : Blo 1472556 1657075 := bstep (se 1 (by rfl) ⟨1242806, by rfl⟩ : syracuseStep 1657075 = 2485613) B2485613
theorem B9439537 : Blo 1472556 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B5384497 : Blo 1472556 5384497 := bstep (se 2 (by rfl) ⟨2019186, by rfl⟩ : syracuseStep 5384497 = 4038373) B4038373
theorem B4196717 : Blo 1472556 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B1657219 : Blo 1472556 1657219 := bstep (se 1 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 1657219 = 2485829) B2485829
theorem B3729827 : Blo 1472556 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B4196785 : Blo 1472556 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B2656739 : Blo 1472556 2656739 := bstep (se 1 (by rfl) ⟨1992554, by rfl⟩ : syracuseStep 2656739 = 3985109) B3985109
theorem B2796049 : Blo 1472556 2796049 := bstep (se 2 (by rfl) ⟨1048518, by rfl⟩ : syracuseStep 2796049 = 2097037) B2097037
theorem B1657363 : Blo 1472556 1657363 := bstep (se 1 (by rfl) ⟨1243022, by rfl⟩ : syracuseStep 1657363 = 2486045) B2486045
theorem B4975181 : Blo 1472556 4975181 := bstep (se 3 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 4975181 = 1865693) B1865693
theorem B3317219 : Blo 1472556 3317219 := bstep (se 1 (by rfl) ⟨2487914, by rfl⟩ : syracuseStep 3317219 = 4975829) B4975829
theorem B2361955 : Blo 1472556 2361955 := bstep (se 1 (by rfl) ⟨1771466, by rfl⟩ : syracuseStep 2361955 = 3542933) B3542933
theorem B60476017 : Blo 1472556 60476017 := bstep (se 2 (by rfl) ⟨22678506, by rfl⟩ : syracuseStep 60476017 = 45357013) B45357013
theorem B4975235 : Blo 1472556 4975235 := bstep (se 1 (by rfl) ⟨3731426, by rfl⟩ : syracuseStep 4975235 = 7462853) B7462853
theorem B1657507 : Blo 1472556 1657507 := bstep (se 1 (by rfl) ⟨1243130, by rfl⟩ : syracuseStep 1657507 = 2486261) B2486261
theorem B4197059 : Blo 1472556 4197059 := bstep (se 1 (by rfl) ⟨3147794, by rfl⟩ : syracuseStep 4197059 = 6295589) B6295589
theorem B5311181 : Blo 1472556 5311181 := bstep (se 3 (by rfl) ⟨995846, by rfl⟩ : syracuseStep 5311181 = 1991693) B1991693
theorem B1534675 : Blo 1472556 1534675 := bstep (se 1 (by rfl) ⟨1151006, by rfl⟩ : syracuseStep 1534675 = 2302013) B2302013
theorem B7457507 : Blo 1472556 7457507 := bstep (se 1 (by rfl) ⟨5593130, by rfl⟩ : syracuseStep 7457507 = 11186261) B11186261
theorem B5745421 : Blo 1472556 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B6294307 : Blo 1472556 6294307 := bstep (se 1 (by rfl) ⟨4720730, by rfl⟩ : syracuseStep 6294307 = 9441461) B9441461
theorem B1657651 : Blo 1472556 1657651 := bstep (se 1 (by rfl) ⟨1243238, by rfl⟩ : syracuseStep 1657651 = 2486477) B2486477
theorem B2485073 : Blo 1472556 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B4975505 : Blo 1472556 4975505 := bstep (se 2 (by rfl) ⟨1865814, by rfl⟩ : syracuseStep 4975505 = 3731629) B3731629
theorem B1657795 : Blo 1472556 1657795 := bstep (se 1 (by rfl) ⟨1243346, by rfl⟩ : syracuseStep 1657795 = 2486693) B2486693
theorem B2485201 : Blo 1472556 2485201 := bstep (se 2 (by rfl) ⟨931950, by rfl⟩ : syracuseStep 2485201 = 1863901) B1863901
theorem B36342755 : Blo 1472556 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B2485235 : Blo 1472556 2485235 := bstep (se 1 (by rfl) ⟨1863926, by rfl⟩ : syracuseStep 2485235 = 3727853) B3727853
theorem B4918321 : Blo 1472556 4918321 := bstep (se 2 (by rfl) ⟨1844370, by rfl⟩ : syracuseStep 4918321 = 3688741) B3688741
theorem B1657939 : Blo 1472556 1657939 := bstep (se 1 (by rfl) ⟨1243454, by rfl⟩ : syracuseStep 1657939 = 2486909) B2486909
theorem B2485363 : Blo 1472556 2485363 := bstep (se 1 (by rfl) ⟨1864022, by rfl⟩ : syracuseStep 2485363 = 3728045) B3728045
theorem B3148931 : Blo 1472556 3148931 := bstep (se 1 (by rfl) ⟨2361698, by rfl⟩ : syracuseStep 3148931 = 4723397) B4723397
theorem B18877637 : Blo 1472556 18877637 := bstep (se 4 (by rfl) ⟨1769778, by rfl⟩ : syracuseStep 18877637 = 3539557) B3539557
theorem B1658083 : Blo 1472556 1658083 := bstep (se 1 (by rfl) ⟨1243562, by rfl⟩ : syracuseStep 1658083 = 2487125) B2487125
theorem B11349233 : Blo 1472556 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B2485505 : Blo 1472556 2485505 := bstep (se 2 (by rfl) ⟨932064, by rfl⟩ : syracuseStep 2485505 = 1864129) B1864129
theorem B3984707 : Blo 1472556 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B3730769 : Blo 1472556 3730769 := bstep (se 2 (by rfl) ⟨1399038, by rfl⟩ : syracuseStep 3730769 = 2798077) B2798077
theorem B1658227 : Blo 1472556 1658227 := bstep (se 1 (by rfl) ⟨1243670, by rfl⟩ : syracuseStep 1658227 = 2487341) B2487341
theorem B2485633 : Blo 1472556 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B3730819 : Blo 1472556 3730819 := bstep (se 1 (by rfl) ⟨2798114, by rfl⟩ : syracuseStep 3730819 = 5596229) B5596229
theorem B2485667 : Blo 1472556 2485667 := bstep (se 1 (by rfl) ⟨1864250, by rfl⟩ : syracuseStep 2485667 = 3728501) B3728501
theorem B4976045 : Blo 1472556 4976045 := bstep (se 3 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 4976045 = 1866017) B1866017
theorem B9088453 : Blo 1472556 9088453 := bstep (se 4 (by rfl) ⟨852042, by rfl⟩ : syracuseStep 9088453 = 1704085) B1704085
theorem B4976099 : Blo 1472556 4976099 := bstep (se 1 (by rfl) ⟨3732074, by rfl⟩ : syracuseStep 4976099 = 7464149) B7464149
theorem B1658371 : Blo 1472556 1658371 := bstep (se 1 (by rfl) ⟨1243778, by rfl⟩ : syracuseStep 1658371 = 2487557) B2487557
theorem B7458317 : Blo 1472556 7458317 := bstep (se 3 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 7458317 = 2796869) B2796869
theorem B4197901 : Blo 1472556 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B3730961 : Blo 1472556 3730961 := bstep (se 2 (by rfl) ⟨1399110, by rfl⟩ : syracuseStep 3730961 = 2798221) B2798221
theorem B2485795 : Blo 1472556 2485795 := bstep (se 1 (by rfl) ⟨1864346, by rfl⟩ : syracuseStep 2485795 = 3728693) B3728693
theorem B2797105 : Blo 1472556 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B11062925 : Blo 1472556 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B1658515 : Blo 1472556 1658515 := bstep (se 1 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 1658515 = 2487773) B2487773
theorem B4198061 : Blo 1472556 4198061 := bstep (se 3 (by rfl) ⟨787136, by rfl⟩ : syracuseStep 4198061 = 1574273) B1574273
theorem B2485937 : Blo 1472556 2485937 := bstep (se 2 (by rfl) ⟨932226, by rfl⟩ : syracuseStep 2485937 = 1864453) B1864453
theorem B4722371 : Blo 1472556 4722371 := bstep (se 1 (by rfl) ⟨3541778, by rfl⟩ : syracuseStep 4722371 = 7083557) B7083557
theorem B5041901 : Blo 1472556 5041901 := bstep (se 3 (by rfl) ⟨945356, by rfl⟩ : syracuseStep 5041901 = 1890713) B1890713
theorem B4976369 : Blo 1472556 4976369 := bstep (se 2 (by rfl) ⟨1866138, by rfl⟩ : syracuseStep 4976369 = 3732277) B3732277
theorem B1658659 : Blo 1472556 1658659 := bstep (se 1 (by rfl) ⟨1243994, by rfl⟩ : syracuseStep 1658659 = 2487989) B2487989
theorem B3313457 : Blo 1472556 3313457 := bstep (se 2 (by rfl) ⟨1242546, by rfl⟩ : syracuseStep 3313457 = 2485093) B2485093
theorem B2486065 : Blo 1472556 2486065 := bstep (se 2 (by rfl) ⟨932274, by rfl⟩ : syracuseStep 2486065 = 1864549) B1864549
theorem B4542257 : Blo 1472556 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B3313475 : Blo 1472556 3313475 := bstep (se 1 (by rfl) ⟨2485106, by rfl⟩ : syracuseStep 3313475 = 4970213) B4970213
theorem B2486099 : Blo 1472556 2486099 := bstep (se 1 (by rfl) ⟨1864574, by rfl⟩ : syracuseStep 2486099 = 3729149) B3729149
theorem B4198243 : Blo 1472556 4198243 := bstep (se 1 (by rfl) ⟨3148682, by rfl⟩ : syracuseStep 4198243 = 6297365) B6297365
theorem B3190691 : Blo 1472556 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B1658803 : Blo 1472556 1658803 := bstep (se 1 (by rfl) ⟨1244102, by rfl⟩ : syracuseStep 1658803 = 2488205) B2488205
theorem B2797507 : Blo 1472556 2797507 := bstep (se 1 (by rfl) ⟨2098130, by rfl⟩ : syracuseStep 2797507 = 4196261) B4196261
theorem B2486227 : Blo 1472556 2486227 := bstep (se 1 (by rfl) ⟨1864670, by rfl⟩ : syracuseStep 2486227 = 3729341) B3729341
theorem B2797553 : Blo 1472556 2797553 := bstep (se 2 (by rfl) ⟨1049082, by rfl⟩ : syracuseStep 2797553 = 2098165) B2098165
theorem B3313745 : Blo 1472556 3313745 := bstep (se 2 (by rfl) ⟨1242654, by rfl⟩ : syracuseStep 3313745 = 2485309) B2485309
theorem B2486369 : Blo 1472556 2486369 := bstep (se 2 (by rfl) ⟨932388, by rfl⟩ : syracuseStep 2486369 = 1864777) B1864777
theorem B3313763 : Blo 1472556 3313763 := bstep (se 1 (by rfl) ⟨2485322, by rfl⟩ : syracuseStep 3313763 = 4970645) B4970645
theorem B9441485 : Blo 1472556 9441485 := bstep (se 3 (by rfl) ⟨1770278, by rfl⟩ : syracuseStep 9441485 = 3540557) B3540557
theorem B2486497 : Blo 1472556 2486497 := bstep (se 2 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 2486497 = 1864873) B1864873
theorem B2486531 : Blo 1472556 2486531 := bstep (se 1 (by rfl) ⟨1864898, by rfl⟩ : syracuseStep 2486531 = 3729797) B3729797
theorem B2797841 : Blo 1472556 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B3314033 : Blo 1472556 3314033 := bstep (se 2 (by rfl) ⟨1242762, by rfl⟩ : syracuseStep 3314033 = 2485525) B2485525
theorem B3314051 : Blo 1472556 3314051 := bstep (se 1 (by rfl) ⟨2485538, by rfl⟩ : syracuseStep 3314051 = 4971077) B4971077
theorem B2486659 : Blo 1472556 2486659 := bstep (se 1 (by rfl) ⟨1864994, by rfl⟩ : syracuseStep 2486659 = 3729989) B3729989
theorem B5591537 : Blo 1472556 5591537 := bstep (se 2 (by rfl) ⟨2096826, by rfl⟩ : syracuseStep 5591537 = 4193653) B4193653
theorem B3731953 : Blo 1472556 3731953 := bstep (se 2 (by rfl) ⟨1399482, by rfl⟩ : syracuseStep 3731953 = 2798965) B2798965
theorem B2486801 : Blo 1472556 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1864291 : Blo 1472556 1864291 := bstep (se 1 (by rfl) ⟨1398218, by rfl⟩ : syracuseStep 1864291 = 2796437) B2796437
theorem B3314321 : Blo 1472556 3314321 := bstep (se 2 (by rfl) ⟨1242870, by rfl⟩ : syracuseStep 3314321 = 2485741) B2485741
theorem B2486929 : Blo 1472556 2486929 := bstep (se 2 (by rfl) ⟨932598, by rfl⟩ : syracuseStep 2486929 = 1865197) B1865197
theorem B3314339 : Blo 1472556 3314339 := bstep (se 1 (by rfl) ⟨2485754, by rfl⟩ : syracuseStep 3314339 = 4971509) B4971509
theorem B2486963 : Blo 1472556 2486963 := bstep (se 1 (by rfl) ⟨1865222, by rfl⟩ : syracuseStep 2486963 = 3730445) B3730445
theorem B1864387 : Blo 1472556 1864387 := bstep (se 1 (by rfl) ⟨1398290, by rfl⟩ : syracuseStep 1864387 = 2796581) B2796581
theorem B6296305 : Blo 1472556 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B3732227 : Blo 1472556 3732227 := bstep (se 1 (by rfl) ⟨2799170, by rfl⟩ : syracuseStep 3732227 = 5598341) B5598341
theorem B10769165 : Blo 1472556 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B2487091 : Blo 1472556 2487091 := bstep (se 1 (by rfl) ⟨1865318, by rfl⟩ : syracuseStep 2487091 = 3730637) B3730637
theorem B3314609 : Blo 1472556 3314609 := bstep (se 2 (by rfl) ⟨1242978, by rfl⟩ : syracuseStep 3314609 = 2485957) B2485957
theorem B2487233 : Blo 1472556 2487233 := bstep (se 2 (by rfl) ⟨932712, by rfl⟩ : syracuseStep 2487233 = 1865425) B1865425
theorem B3314627 : Blo 1472556 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B3732419 : Blo 1472556 3732419 := bstep (se 1 (by rfl) ⟨2799314, by rfl⟩ : syracuseStep 3732419 = 5598629) B5598629
theorem B2798563 : Blo 1472556 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B2126849 : Blo 1472556 2126849 := bstep (se 2 (by rfl) ⟨797568, by rfl⟩ : syracuseStep 2126849 = 1595137) B1595137
theorem B4723715 : Blo 1472556 4723715 := bstep (se 1 (by rfl) ⟨3542786, by rfl⟩ : syracuseStep 4723715 = 7085573) B7085573
theorem B2487361 : Blo 1472556 2487361 := bstep (se 2 (by rfl) ⟨932760, by rfl⟩ : syracuseStep 2487361 = 1865521) B1865521
theorem B2208851 : Blo 1472556 2208851 := bstep (se 1 (by rfl) ⟨1656638, by rfl⟩ : syracuseStep 2208851 = 3313277) B3313277
theorem B2487395 : Blo 1472556 2487395 := bstep (se 1 (by rfl) ⟨1865546, by rfl⟩ : syracuseStep 2487395 = 3731093) B3731093
theorem B2208881 : Blo 1472556 2208881 := bstep (se 2 (by rfl) ⟨828330, by rfl⟩ : syracuseStep 2208881 = 1656661) B1656661
theorem B2208899 : Blo 1472556 2208899 := bstep (se 1 (by rfl) ⟨1656674, by rfl⟩ : syracuseStep 2208899 = 3313349) B3313349
theorem B2208929 : Blo 1472556 2208929 := bstep (se 2 (by rfl) ⟨828348, by rfl⟩ : syracuseStep 2208929 = 1656697) B1656697
theorem B4478125 : Blo 1472556 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B2208947 : Blo 1472556 2208947 := bstep (se 1 (by rfl) ⟨1656710, by rfl⟩ : syracuseStep 2208947 = 3313421) B3313421
theorem B1864883 : Blo 1472556 1864883 := bstep (se 1 (by rfl) ⟨1398662, by rfl⟩ : syracuseStep 1864883 = 2797325) B2797325
theorem B10220741 : Blo 1472556 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B2208977 : Blo 1472556 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B3314897 : Blo 1472556 3314897 := bstep (se 2 (by rfl) ⟨1243086, by rfl⟩ : syracuseStep 3314897 = 2486173) B2486173
theorem B2208995 : Blo 1472556 2208995 := bstep (se 1 (by rfl) ⟨1656746, by rfl⟩ : syracuseStep 2208995 = 3313493) B3313493
theorem B3314915 : Blo 1472556 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B2487523 : Blo 1472556 2487523 := bstep (se 1 (by rfl) ⟨1865642, by rfl⟩ : syracuseStep 2487523 = 3731285) B3731285
theorem B2209025 : Blo 1472556 2209025 := bstep (se 2 (by rfl) ⟨828384, by rfl⟩ : syracuseStep 2209025 = 1656769) B1656769
theorem B2209043 : Blo 1472556 2209043 := bstep (se 1 (by rfl) ⟨1656782, by rfl⟩ : syracuseStep 2209043 = 3313565) B3313565
theorem B1774867 : Blo 1472556 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2209073 : Blo 1472556 2209073 := bstep (se 2 (by rfl) ⟨828402, by rfl⟩ : syracuseStep 2209073 = 1656805) B1656805
theorem B2209091 : Blo 1472556 2209091 := bstep (se 1 (by rfl) ⟨1656818, by rfl⟩ : syracuseStep 2209091 = 3313637) B3313637
theorem B2209121 : Blo 1472556 2209121 := bstep (se 2 (by rfl) ⟨828420, by rfl⟩ : syracuseStep 2209121 = 1656841) B1656841
theorem B2487665 : Blo 1472556 2487665 := bstep (se 2 (by rfl) ⟨932874, by rfl⟩ : syracuseStep 2487665 = 1865749) B1865749
theorem B2209139 : Blo 1472556 2209139 := bstep (se 1 (by rfl) ⟨1656854, by rfl⟩ : syracuseStep 2209139 = 3313709) B3313709
theorem B2209169 : Blo 1472556 2209169 := bstep (se 2 (by rfl) ⟨828438, by rfl⟩ : syracuseStep 2209169 = 1656877) B1656877
theorem B2045345 : Blo 1472556 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B2209187 : Blo 1472556 2209187 := bstep (se 1 (by rfl) ⟨1656890, by rfl⟩ : syracuseStep 2209187 = 3313781) B3313781
theorem B2799011 : Blo 1472556 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B2209217 : Blo 1472556 2209217 := bstep (se 2 (by rfl) ⟨828456, by rfl⟩ : syracuseStep 2209217 = 1656913) B1656913
theorem B2209235 : Blo 1472556 2209235 := bstep (se 1 (by rfl) ⟨1656926, by rfl⟩ : syracuseStep 2209235 = 3313853) B3313853
theorem B2209265 : Blo 1472556 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B3315185 : Blo 1472556 3315185 := bstep (se 2 (by rfl) ⟨1243194, by rfl⟩ : syracuseStep 3315185 = 2486389) B2486389
theorem B2487793 : Blo 1472556 2487793 := bstep (se 2 (by rfl) ⟨932922, by rfl⟩ : syracuseStep 2487793 = 1865845) B1865845
theorem B2209283 : Blo 1472556 2209283 := bstep (se 1 (by rfl) ⟨1656962, by rfl⟩ : syracuseStep 2209283 = 3313925) B3313925
theorem B3315203 : Blo 1472556 3315203 := bstep (se 1 (by rfl) ⟨2486402, by rfl⟩ : syracuseStep 3315203 = 4972805) B4972805
theorem B4969997 : Blo 1472556 4969997 := bstep (se 3 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 4969997 = 1863749) B1863749
theorem B2487827 : Blo 1472556 2487827 := bstep (se 1 (by rfl) ⟨1865870, by rfl⟩ : syracuseStep 2487827 = 3731741) B3731741
theorem B2209313 : Blo 1472556 2209313 := bstep (se 2 (by rfl) ⟨828492, by rfl⟩ : syracuseStep 2209313 = 1656985) B1656985
theorem B2209331 : Blo 1472556 2209331 := bstep (se 1 (by rfl) ⟨1656998, by rfl⟩ : syracuseStep 2209331 = 3313997) B3313997
theorem B4970051 : Blo 1472556 4970051 := bstep (se 1 (by rfl) ⟨3727538, by rfl⟩ : syracuseStep 4970051 = 7455077) B7455077
theorem B2209361 : Blo 1472556 2209361 := bstep (se 2 (by rfl) ⟨828510, by rfl⟩ : syracuseStep 2209361 = 1657021) B1657021
theorem B2209379 : Blo 1472556 2209379 := bstep (se 1 (by rfl) ⟨1657034, by rfl⟩ : syracuseStep 2209379 = 3314069) B3314069
theorem B2209409 : Blo 1472556 2209409 := bstep (se 2 (by rfl) ⟨828528, by rfl⟩ : syracuseStep 2209409 = 1657057) B1657057
theorem B2209427 : Blo 1472556 2209427 := bstep (se 1 (by rfl) ⟨1657070, by rfl⟩ : syracuseStep 2209427 = 3314141) B3314141
theorem B2487955 : Blo 1472556 2487955 := bstep (se 1 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 2487955 = 3731933) B3731933
theorem B2209457 : Blo 1472556 2209457 := bstep (se 2 (by rfl) ⟨828546, by rfl⟩ : syracuseStep 2209457 = 1657093) B1657093
theorem B2209475 : Blo 1472556 2209475 := bstep (se 1 (by rfl) ⟨1657106, by rfl⟩ : syracuseStep 2209475 = 3314213) B3314213
theorem B2799299 : Blo 1472556 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B2209505 : Blo 1472556 2209505 := bstep (se 2 (by rfl) ⟨828564, by rfl⟩ : syracuseStep 2209505 = 1657129) B1657129
theorem B2209523 : Blo 1472556 2209523 := bstep (se 1 (by rfl) ⟨1657142, by rfl⟩ : syracuseStep 2209523 = 3314285) B3314285
theorem B7558925 : Blo 1472556 7558925 := bstep (se 3 (by rfl) ⟨1417298, by rfl⟩ : syracuseStep 7558925 = 2834597) B2834597
theorem B2209553 : Blo 1472556 2209553 := bstep (se 2 (by rfl) ⟨828582, by rfl⟩ : syracuseStep 2209553 = 1657165) B1657165
theorem B3315473 : Blo 1472556 3315473 := bstep (se 2 (by rfl) ⟨1243302, by rfl⟩ : syracuseStep 3315473 = 2486605) B2486605
theorem B2488097 : Blo 1472556 2488097 := bstep (se 2 (by rfl) ⟨933036, by rfl⟩ : syracuseStep 2488097 = 1866073) B1866073
theorem B2209571 : Blo 1472556 2209571 := bstep (se 1 (by rfl) ⟨1657178, by rfl⟩ : syracuseStep 2209571 = 3314357) B3314357
theorem B3315491 : Blo 1472556 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B2209601 : Blo 1472556 2209601 := bstep (se 2 (by rfl) ⟨828600, by rfl⟩ : syracuseStep 2209601 = 1657201) B1657201
theorem B4970321 : Blo 1472556 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B2987857 : Blo 1472556 2987857 := bstep (se 2 (by rfl) ⟨1120446, by rfl⟩ : syracuseStep 2987857 = 2240893) B2240893
theorem B2209619 : Blo 1472556 2209619 := bstep (se 1 (by rfl) ⟨1657214, by rfl⟩ : syracuseStep 2209619 = 3314429) B3314429
theorem B2520929 : Blo 1472556 2520929 := bstep (se 2 (by rfl) ⟨945348, by rfl⟩ : syracuseStep 2520929 = 1890697) B1890697
theorem B2209649 : Blo 1472556 2209649 := bstep (se 2 (by rfl) ⟨828618, by rfl⟩ : syracuseStep 2209649 = 1657237) B1657237
theorem B1865587 : Blo 1472556 1865587 := bstep (se 1 (by rfl) ⟨1399190, by rfl⟩ : syracuseStep 1865587 = 2798381) B2798381
theorem B2209667 : Blo 1472556 2209667 := bstep (se 1 (by rfl) ⟨1657250, by rfl⟩ : syracuseStep 2209667 = 3314501) B3314501
theorem B2209697 : Blo 1472556 2209697 := bstep (se 2 (by rfl) ⟨828636, by rfl⟩ : syracuseStep 2209697 = 1657273) B1657273
theorem B5592995 : Blo 1472556 5592995 := bstep (se 1 (by rfl) ⟨4194746, by rfl⟩ : syracuseStep 5592995 = 8389493) B8389493
theorem B2488225 : Blo 1472556 2488225 := bstep (se 2 (by rfl) ⟨933084, by rfl⟩ : syracuseStep 2488225 = 1866169) B1866169
theorem B5593009 : Blo 1472556 5593009 := bstep (se 2 (by rfl) ⟨2097378, by rfl⟩ : syracuseStep 5593009 = 4194757) B4194757
theorem B2209715 : Blo 1472556 2209715 := bstep (se 1 (by rfl) ⟨1657286, by rfl⟩ : syracuseStep 2209715 = 3314573) B3314573
theorem B2488259 : Blo 1472556 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B2209745 : Blo 1472556 2209745 := bstep (se 2 (by rfl) ⟨828654, by rfl⟩ : syracuseStep 2209745 = 1657309) B1657309
theorem B1865683 : Blo 1472556 1865683 := bstep (se 1 (by rfl) ⟨1399262, by rfl⟩ : syracuseStep 1865683 = 2798525) B2798525
theorem B2209763 : Blo 1472556 2209763 := bstep (se 1 (by rfl) ⟨1657322, by rfl⟩ : syracuseStep 2209763 = 3314645) B3314645
theorem B12105713 : Blo 1472556 12105713 := bstep (se 2 (by rfl) ⟨4539642, by rfl⟩ : syracuseStep 12105713 = 9079285) B9079285
theorem B2209793 : Blo 1472556 2209793 := bstep (se 2 (by rfl) ⟨828672, by rfl⟩ : syracuseStep 2209793 = 1657345) B1657345
theorem B2209811 : Blo 1472556 2209811 := bstep (se 1 (by rfl) ⟨1657358, by rfl⟩ : syracuseStep 2209811 = 3314717) B3314717
theorem B2209841 : Blo 1472556 2209841 := bstep (se 2 (by rfl) ⟨828690, by rfl⟩ : syracuseStep 2209841 = 1657381) B1657381
theorem B3315761 : Blo 1472556 3315761 := bstep (se 2 (by rfl) ⟨1243410, by rfl⟩ : syracuseStep 3315761 = 2486821) B2486821
theorem B1472563 : Blo 1472556 1472563 := bstep (se 1 (by rfl) ⟨1104422, by rfl⟩ : syracuseStep 1472563 = 2208845) B2208845
theorem B1472579 : Blo 1472556 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B2209859 : Blo 1472556 2209859 := bstep (se 1 (by rfl) ⟨1657394, by rfl⟩ : syracuseStep 2209859 = 3314789) B3314789
theorem B3315779 : Blo 1472556 3315779 := bstep (se 1 (by rfl) ⟨2486834, by rfl⟩ : syracuseStep 3315779 = 4973669) B4973669
theorem B1472595 : Blo 1472556 1472595 := bstep (se 1 (by rfl) ⟨1104446, by rfl⟩ : syracuseStep 1472595 = 2208893) B2208893
theorem B2209889 : Blo 1472556 2209889 := bstep (se 2 (by rfl) ⟨828708, by rfl⟩ : syracuseStep 2209889 = 1657417) B1657417
theorem B1472611 : Blo 1472556 1472611 := bstep (se 1 (by rfl) ⟨1104458, by rfl⟩ : syracuseStep 1472611 = 2208917) B2208917
theorem B1472627 : Blo 1472556 1472627 := bstep (se 1 (by rfl) ⟨1104470, by rfl⟩ : syracuseStep 1472627 = 2208941) B2208941
theorem B2209907 : Blo 1472556 2209907 := bstep (se 1 (by rfl) ⟨1657430, by rfl⟩ : syracuseStep 2209907 = 3314861) B3314861
theorem B1472643 : Blo 1472556 1472643 := bstep (se 1 (by rfl) ⟨1104482, by rfl⟩ : syracuseStep 1472643 = 2208965) B2208965
theorem B2209937 : Blo 1472556 2209937 := bstep (se 2 (by rfl) ⟨828726, by rfl⟩ : syracuseStep 2209937 = 1657453) B1657453
theorem B1472659 : Blo 1472556 1472659 := bstep (se 1 (by rfl) ⟨1104494, by rfl⟩ : syracuseStep 1472659 = 2208989) B2208989
theorem B1472675 : Blo 1472556 1472675 := bstep (se 1 (by rfl) ⟨1104506, by rfl⟩ : syracuseStep 1472675 = 2209013) B2209013
theorem B2209955 : Blo 1472556 2209955 := bstep (se 1 (by rfl) ⟨1657466, by rfl⟩ : syracuseStep 2209955 = 3314933) B3314933
theorem B1472691 : Blo 1472556 1472691 := bstep (se 1 (by rfl) ⟨1104518, by rfl⟩ : syracuseStep 1472691 = 2209037) B2209037
theorem B2209985 : Blo 1472556 2209985 := bstep (se 2 (by rfl) ⟨828744, by rfl⟩ : syracuseStep 2209985 = 1657489) B1657489
theorem B1472707 : Blo 1472556 1472707 := bstep (se 1 (by rfl) ⟨1104530, by rfl⟩ : syracuseStep 1472707 = 2209061) B2209061
theorem B1472723 : Blo 1472556 1472723 := bstep (se 1 (by rfl) ⟨1104542, by rfl⟩ : syracuseStep 1472723 = 2209085) B2209085
theorem B2210003 : Blo 1472556 2210003 := bstep (se 1 (by rfl) ⟨1657502, by rfl⟩ : syracuseStep 2210003 = 3315005) B3315005
theorem B1472739 : Blo 1472556 1472739 := bstep (se 1 (by rfl) ⟨1104554, by rfl⟩ : syracuseStep 1472739 = 2209109) B2209109
theorem B2210033 : Blo 1472556 2210033 := bstep (se 2 (by rfl) ⟨828762, by rfl⟩ : syracuseStep 2210033 = 1657525) B1657525
theorem B1472755 : Blo 1472556 1472755 := bstep (se 1 (by rfl) ⟨1104566, by rfl⟩ : syracuseStep 1472755 = 2209133) B2209133
theorem B1472771 : Blo 1472556 1472771 := bstep (se 1 (by rfl) ⟨1104578, by rfl⟩ : syracuseStep 1472771 = 2209157) B2209157
theorem B2210051 : Blo 1472556 2210051 := bstep (se 1 (by rfl) ⟨1657538, by rfl⟩ : syracuseStep 2210051 = 3315077) B3315077
theorem B1472787 : Blo 1472556 1472787 := bstep (se 1 (by rfl) ⟨1104590, by rfl⟩ : syracuseStep 1472787 = 2209181) B2209181
theorem B34019605 : Blo 1472556 34019605 := bstep (se 6 (by rfl) ⟨797334, by rfl⟩ : syracuseStep 34019605 = 1594669) B1594669
theorem B2210081 : Blo 1472556 2210081 := bstep (se 2 (by rfl) ⟨828780, by rfl⟩ : syracuseStep 2210081 = 1657561) B1657561
theorem B1472803 : Blo 1472556 1472803 := bstep (se 1 (by rfl) ⟨1104602, by rfl⟩ : syracuseStep 1472803 = 2209205) B2209205
theorem B1472819 : Blo 1472556 1472819 := bstep (se 1 (by rfl) ⟨1104614, by rfl⟩ : syracuseStep 1472819 = 2209229) B2209229
theorem B2210099 : Blo 1472556 2210099 := bstep (se 1 (by rfl) ⟨1657574, by rfl⟩ : syracuseStep 2210099 = 3315149) B3315149
theorem B1472835 : Blo 1472556 1472835 := bstep (se 1 (by rfl) ⟨1104626, by rfl⟩ : syracuseStep 1472835 = 2209253) B2209253
theorem B2210129 : Blo 1472556 2210129 := bstep (se 2 (by rfl) ⟨828798, by rfl⟩ : syracuseStep 2210129 = 1657597) B1657597
theorem B3316049 : Blo 1472556 3316049 := bstep (se 2 (by rfl) ⟨1243518, by rfl⟩ : syracuseStep 3316049 = 2487037) B2487037
theorem B1472851 : Blo 1472556 1472851 := bstep (se 1 (by rfl) ⟨1104638, by rfl⟩ : syracuseStep 1472851 = 2209277) B2209277
theorem B1472867 : Blo 1472556 1472867 := bstep (se 1 (by rfl) ⟨1104650, by rfl⟩ : syracuseStep 1472867 = 2209301) B2209301
theorem B2210147 : Blo 1472556 2210147 := bstep (se 1 (by rfl) ⟨1657610, by rfl⟩ : syracuseStep 2210147 = 3315221) B3315221
theorem B3316067 : Blo 1472556 3316067 := bstep (se 1 (by rfl) ⟨2487050, by rfl⟩ : syracuseStep 3316067 = 4974101) B4974101
theorem B4970861 : Blo 1472556 4970861 := bstep (se 3 (by rfl) ⟨932036, by rfl⟩ : syracuseStep 4970861 = 1864073) B1864073
theorem B7461233 : Blo 1472556 7461233 := bstep (se 2 (by rfl) ⟨2797962, by rfl⟩ : syracuseStep 7461233 = 5595925) B5595925
theorem B1472883 : Blo 1472556 1472883 := bstep (se 1 (by rfl) ⟨1104662, by rfl⟩ : syracuseStep 1472883 = 2209325) B2209325
theorem B2210177 : Blo 1472556 2210177 := bstep (se 2 (by rfl) ⟨828816, by rfl⟩ : syracuseStep 2210177 = 1657633) B1657633
theorem B1472899 : Blo 1472556 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B1472915 : Blo 1472556 1472915 := bstep (se 1 (by rfl) ⟨1104686, by rfl⟩ : syracuseStep 1472915 = 2209373) B2209373
theorem B2210195 : Blo 1472556 2210195 := bstep (se 1 (by rfl) ⟨1657646, by rfl⟩ : syracuseStep 2210195 = 3315293) B3315293
theorem B4970915 : Blo 1472556 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B1472931 : Blo 1472556 1472931 := bstep (se 1 (by rfl) ⟨1104698, by rfl⟩ : syracuseStep 1472931 = 2209397) B2209397
theorem B2210225 : Blo 1472556 2210225 := bstep (se 2 (by rfl) ⟨828834, by rfl⟩ : syracuseStep 2210225 = 1657669) B1657669
theorem B1472947 : Blo 1472556 1472947 := bstep (se 1 (by rfl) ⟨1104710, by rfl⟩ : syracuseStep 1472947 = 2209421) B2209421
theorem B1472963 : Blo 1472556 1472963 := bstep (se 1 (by rfl) ⟨1104722, by rfl⟩ : syracuseStep 1472963 = 2209445) B2209445
theorem B2210243 : Blo 1472556 2210243 := bstep (se 1 (by rfl) ⟨1657682, by rfl⟩ : syracuseStep 2210243 = 3315365) B3315365
theorem B161282501 : Blo 1472556 161282501 := bstep (se 4 (by rfl) ⟨15120234, by rfl⟩ : syracuseStep 161282501 = 30240469) B30240469
theorem B1866179 : Blo 1472556 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1472979 : Blo 1472556 1472979 := bstep (se 1 (by rfl) ⟨1104734, by rfl⟩ : syracuseStep 1472979 = 2209469) B2209469
theorem B2210273 : Blo 1472556 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B1472995 : Blo 1472556 1472995 := bstep (se 1 (by rfl) ⟨1104746, by rfl⟩ : syracuseStep 1472995 = 2209493) B2209493
theorem B1473011 : Blo 1472556 1473011 := bstep (se 1 (by rfl) ⟨1104758, by rfl⟩ : syracuseStep 1473011 = 2209517) B2209517
theorem B2210291 : Blo 1472556 2210291 := bstep (se 1 (by rfl) ⟨1657718, by rfl⟩ : syracuseStep 2210291 = 3315437) B3315437
theorem B1473027 : Blo 1472556 1473027 := bstep (se 1 (by rfl) ⟨1104770, by rfl⟩ : syracuseStep 1473027 = 2209541) B2209541
theorem B2210321 : Blo 1472556 2210321 := bstep (se 2 (by rfl) ⟨828870, by rfl⟩ : syracuseStep 2210321 = 1657741) B1657741
theorem B1473043 : Blo 1472556 1473043 := bstep (se 1 (by rfl) ⟨1104782, by rfl⟩ : syracuseStep 1473043 = 2209565) B2209565
theorem B1473059 : Blo 1472556 1473059 := bstep (se 1 (by rfl) ⟨1104794, by rfl⟩ : syracuseStep 1473059 = 2209589) B2209589
theorem B2210339 : Blo 1472556 2210339 := bstep (se 1 (by rfl) ⟨1657754, by rfl⟩ : syracuseStep 2210339 = 3315509) B3315509
theorem B1473075 : Blo 1472556 1473075 := bstep (se 1 (by rfl) ⟨1104806, by rfl⟩ : syracuseStep 1473075 = 2209613) B2209613
theorem B2210369 : Blo 1472556 2210369 := bstep (se 2 (by rfl) ⟨828888, by rfl⟩ : syracuseStep 2210369 = 1657777) B1657777
theorem B1473091 : Blo 1472556 1473091 := bstep (se 1 (by rfl) ⟨1104818, by rfl⟩ : syracuseStep 1473091 = 2209637) B2209637
theorem B1473107 : Blo 1472556 1473107 := bstep (se 1 (by rfl) ⟨1104830, by rfl⟩ : syracuseStep 1473107 = 2209661) B2209661
theorem B2210387 : Blo 1472556 2210387 := bstep (se 1 (by rfl) ⟨1657790, by rfl⟩ : syracuseStep 2210387 = 3315581) B3315581
theorem B1473123 : Blo 1472556 1473123 := bstep (se 1 (by rfl) ⟨1104842, by rfl⟩ : syracuseStep 1473123 = 2209685) B2209685
theorem B2988643 : Blo 1472556 2988643 := bstep (se 1 (by rfl) ⟨2241482, by rfl⟩ : syracuseStep 2988643 = 4482965) B4482965
theorem B2210417 : Blo 1472556 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B3316337 : Blo 1472556 3316337 := bstep (se 2 (by rfl) ⟨1243626, by rfl⟩ : syracuseStep 3316337 = 2487253) B2487253
theorem B1473139 : Blo 1472556 1473139 := bstep (se 1 (by rfl) ⟨1104854, by rfl⟩ : syracuseStep 1473139 = 2209709) B2209709
theorem B1473155 : Blo 1472556 1473155 := bstep (se 1 (by rfl) ⟨1104866, by rfl⟩ : syracuseStep 1473155 = 2209733) B2209733
theorem B2210435 : Blo 1472556 2210435 := bstep (se 1 (by rfl) ⟨1657826, by rfl⟩ : syracuseStep 2210435 = 3315653) B3315653
theorem B3316355 : Blo 1472556 3316355 := bstep (se 1 (by rfl) ⟨2487266, by rfl⟩ : syracuseStep 3316355 = 4974533) B4974533
theorem B1473171 : Blo 1472556 1473171 := bstep (se 1 (by rfl) ⟨1104878, by rfl⟩ : syracuseStep 1473171 = 2209757) B2209757
theorem B2210465 : Blo 1472556 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B1473187 : Blo 1472556 1473187 := bstep (se 1 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 1473187 = 2209781) B2209781
theorem B4971185 : Blo 1472556 4971185 := bstep (se 2 (by rfl) ⟨1864194, by rfl⟩ : syracuseStep 4971185 = 3728389) B3728389
theorem B1473203 : Blo 1472556 1473203 := bstep (se 1 (by rfl) ⟨1104902, by rfl⟩ : syracuseStep 1473203 = 2209805) B2209805
theorem B2210483 : Blo 1472556 2210483 := bstep (se 1 (by rfl) ⟨1657862, by rfl⟩ : syracuseStep 2210483 = 3315725) B3315725
theorem B1473219 : Blo 1472556 1473219 := bstep (se 1 (by rfl) ⟨1104914, by rfl⟩ : syracuseStep 1473219 = 2209829) B2209829
theorem B2210513 : Blo 1472556 2210513 := bstep (se 2 (by rfl) ⟨828942, by rfl⟩ : syracuseStep 2210513 = 1657885) B1657885
theorem B1473235 : Blo 1472556 1473235 := bstep (se 1 (by rfl) ⟨1104926, by rfl⟩ : syracuseStep 1473235 = 2209853) B2209853
theorem B1473251 : Blo 1472556 1473251 := bstep (se 1 (by rfl) ⟨1104938, by rfl⟩ : syracuseStep 1473251 = 2209877) B2209877
theorem B2210531 : Blo 1472556 2210531 := bstep (se 1 (by rfl) ⟨1657898, by rfl⟩ : syracuseStep 2210531 = 3315797) B3315797
theorem B1473267 : Blo 1472556 1473267 := bstep (se 1 (by rfl) ⟨1104950, by rfl⟩ : syracuseStep 1473267 = 2209901) B2209901
theorem B2210561 : Blo 1472556 2210561 := bstep (se 2 (by rfl) ⟨828960, by rfl⟩ : syracuseStep 2210561 = 1657921) B1657921
theorem B1473283 : Blo 1472556 1473283 := bstep (se 1 (by rfl) ⟨1104962, by rfl⟩ : syracuseStep 1473283 = 2209925) B2209925
theorem B1473299 : Blo 1472556 1473299 := bstep (se 1 (by rfl) ⟨1104974, by rfl⟩ : syracuseStep 1473299 = 2209949) B2209949
theorem B2210579 : Blo 1472556 2210579 := bstep (se 1 (by rfl) ⟨1657934, by rfl⟩ : syracuseStep 2210579 = 3315869) B3315869
theorem B1473315 : Blo 1472556 1473315 := bstep (se 1 (by rfl) ⟨1104986, by rfl⟩ : syracuseStep 1473315 = 2209973) B2209973
theorem B2210609 : Blo 1472556 2210609 := bstep (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) B1657957
theorem B1473331 : Blo 1472556 1473331 := bstep (se 1 (by rfl) ⟨1104998, by rfl⟩ : syracuseStep 1473331 = 2209997) B2209997
theorem B1473347 : Blo 1472556 1473347 := bstep (se 1 (by rfl) ⟨1105010, by rfl⟩ : syracuseStep 1473347 = 2210021) B2210021
theorem B2210627 : Blo 1472556 2210627 := bstep (se 1 (by rfl) ⟨1657970, by rfl⟩ : syracuseStep 2210627 = 3315941) B3315941
theorem B1473363 : Blo 1472556 1473363 := bstep (se 1 (by rfl) ⟨1105022, by rfl⟩ : syracuseStep 1473363 = 2210045) B2210045
theorem B2210657 : Blo 1472556 2210657 := bstep (se 2 (by rfl) ⟨828996, by rfl⟩ : syracuseStep 2210657 = 1657993) B1657993
theorem B1473379 : Blo 1472556 1473379 := bstep (se 1 (by rfl) ⟨1105034, by rfl⟩ : syracuseStep 1473379 = 2210069) B2210069
theorem B1473395 : Blo 1472556 1473395 := bstep (se 1 (by rfl) ⟨1105046, by rfl⟩ : syracuseStep 1473395 = 2210093) B2210093
theorem B2210675 : Blo 1472556 2210675 := bstep (se 1 (by rfl) ⟨1658006, by rfl⟩ : syracuseStep 2210675 = 3316013) B3316013
theorem B1473411 : Blo 1472556 1473411 := bstep (se 1 (by rfl) ⟨1105058, by rfl⟩ : syracuseStep 1473411 = 2210117) B2210117
theorem B2210705 : Blo 1472556 2210705 := bstep (se 2 (by rfl) ⟨829014, by rfl⟩ : syracuseStep 2210705 = 1658029) B1658029
theorem B1473427 : Blo 1472556 1473427 := bstep (se 1 (by rfl) ⟨1105070, by rfl⟩ : syracuseStep 1473427 = 2210141) B2210141
theorem B3316625 : Blo 1472556 3316625 := bstep (se 2 (by rfl) ⟨1243734, by rfl⟩ : syracuseStep 3316625 = 2487469) B2487469
theorem B1473443 : Blo 1472556 1473443 := bstep (se 1 (by rfl) ⟨1105082, by rfl⟩ : syracuseStep 1473443 = 2210165) B2210165
theorem B2210723 : Blo 1472556 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B3316643 : Blo 1472556 3316643 := bstep (se 1 (by rfl) ⟨2487482, by rfl⟩ : syracuseStep 3316643 = 4974965) B4974965
theorem B1473459 : Blo 1472556 1473459 := bstep (se 1 (by rfl) ⟨1105094, by rfl⟩ : syracuseStep 1473459 = 2210189) B2210189
theorem B2210753 : Blo 1472556 2210753 := bstep (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) B1658065
theorem B1473475 : Blo 1472556 1473475 := bstep (se 1 (by rfl) ⟨1105106, by rfl⟩ : syracuseStep 1473475 = 2210213) B2210213
theorem B1473491 : Blo 1472556 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B2210771 : Blo 1472556 2210771 := bstep (se 1 (by rfl) ⟨1658078, by rfl⟩ : syracuseStep 2210771 = 3316157) B3316157
theorem B1727443 : Blo 1472556 1727443 := bstep (se 1 (by rfl) ⟨1295582, by rfl⟩ : syracuseStep 1727443 = 2591165) B2591165
theorem B1473507 : Blo 1472556 1473507 := bstep (se 1 (by rfl) ⟨1105130, by rfl⟩ : syracuseStep 1473507 = 2210261) B2210261
theorem B2210801 : Blo 1472556 2210801 := bstep (se 2 (by rfl) ⟨829050, by rfl⟩ : syracuseStep 2210801 = 1658101) B1658101
theorem B1473523 : Blo 1472556 1473523 := bstep (se 1 (by rfl) ⟨1105142, by rfl⟩ : syracuseStep 1473523 = 2210285) B2210285
theorem B1473539 : Blo 1472556 1473539 := bstep (se 1 (by rfl) ⟨1105154, by rfl⟩ : syracuseStep 1473539 = 2210309) B2210309
theorem B2210819 : Blo 1472556 2210819 := bstep (se 1 (by rfl) ⟨1658114, by rfl⟩ : syracuseStep 2210819 = 3316229) B3316229
theorem B1473555 : Blo 1472556 1473555 := bstep (se 1 (by rfl) ⟨1105166, by rfl⟩ : syracuseStep 1473555 = 2210333) B2210333
theorem B2210849 : Blo 1472556 2210849 := bstep (se 2 (by rfl) ⟨829068, by rfl⟩ : syracuseStep 2210849 = 1658137) B1658137
theorem B1473571 : Blo 1472556 1473571 := bstep (se 1 (by rfl) ⟨1105178, by rfl⟩ : syracuseStep 1473571 = 2210357) B2210357
theorem B1473587 : Blo 1472556 1473587 := bstep (se 1 (by rfl) ⟨1105190, by rfl⟩ : syracuseStep 1473587 = 2210381) B2210381
theorem B2210867 : Blo 1472556 2210867 := bstep (se 1 (by rfl) ⟨1658150, by rfl⟩ : syracuseStep 2210867 = 3316301) B3316301
theorem B1473603 : Blo 1472556 1473603 := bstep (se 1 (by rfl) ⟨1105202, by rfl⟩ : syracuseStep 1473603 = 2210405) B2210405
theorem B2210897 : Blo 1472556 2210897 := bstep (se 2 (by rfl) ⟨829086, by rfl⟩ : syracuseStep 2210897 = 1658173) B1658173
theorem B1473619 : Blo 1472556 1473619 := bstep (se 1 (by rfl) ⟨1105214, by rfl⟩ : syracuseStep 1473619 = 2210429) B2210429
theorem B20151395 : Blo 1472556 20151395 := bstep (se 1 (by rfl) ⟨15113546, by rfl⟩ : syracuseStep 20151395 = 30227093) B30227093
theorem B5307491 : Blo 1472556 5307491 := bstep (se 1 (by rfl) ⟨3980618, by rfl⟩ : syracuseStep 5307491 = 7961237) B7961237
theorem B6290531 : Blo 1472556 6290531 := bstep (se 1 (by rfl) ⟨4717898, by rfl⟩ : syracuseStep 6290531 = 9435797) B9435797
theorem B1473635 : Blo 1472556 1473635 := bstep (se 1 (by rfl) ⟨1105226, by rfl⟩ : syracuseStep 1473635 = 2210453) B2210453
theorem B2210915 : Blo 1472556 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B1473651 : Blo 1472556 1473651 := bstep (se 1 (by rfl) ⟨1105238, by rfl⟩ : syracuseStep 1473651 = 2210477) B2210477
theorem B2210945 : Blo 1472556 2210945 := bstep (se 2 (by rfl) ⟨829104, by rfl⟩ : syracuseStep 2210945 = 1658209) B1658209
theorem B1473667 : Blo 1472556 1473667 := bstep (se 1 (by rfl) ⟨1105250, by rfl⟩ : syracuseStep 1473667 = 2210501) B2210501
theorem B1473683 : Blo 1472556 1473683 := bstep (se 1 (by rfl) ⟨1105262, by rfl⟩ : syracuseStep 1473683 = 2210525) B2210525
theorem B2210963 : Blo 1472556 2210963 := bstep (se 1 (by rfl) ⟨1658222, by rfl⟩ : syracuseStep 2210963 = 3316445) B3316445
theorem B1473699 : Blo 1472556 1473699 := bstep (se 1 (by rfl) ⟨1105274, by rfl⟩ : syracuseStep 1473699 = 2210549) B2210549
theorem B7077041 : Blo 1472556 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B9436337 : Blo 1472556 9436337 := bstep (se 2 (by rfl) ⟨3538626, by rfl⟩ : syracuseStep 9436337 = 7077253) B7077253
theorem B1473715 : Blo 1472556 1473715 := bstep (se 1 (by rfl) ⟨1105286, by rfl⟩ : syracuseStep 1473715 = 2210573) B2210573
theorem B2210993 : Blo 1472556 2210993 := bstep (se 2 (by rfl) ⟨829122, by rfl⟩ : syracuseStep 2210993 = 1658245) B1658245
theorem B3316913 : Blo 1472556 3316913 := bstep (se 2 (by rfl) ⟨1243842, by rfl⟩ : syracuseStep 3316913 = 2487685) B2487685
theorem B1473731 : Blo 1472556 1473731 := bstep (se 1 (by rfl) ⟨1105298, by rfl⟩ : syracuseStep 1473731 = 2210597) B2210597
theorem B2211011 : Blo 1472556 2211011 := bstep (se 1 (by rfl) ⟨1658258, by rfl⟩ : syracuseStep 2211011 = 3316517) B3316517
theorem B3316931 : Blo 1472556 3316931 := bstep (se 1 (by rfl) ⟨2487698, by rfl⟩ : syracuseStep 3316931 = 4975397) B4975397
theorem B4971725 : Blo 1472556 4971725 := bstep (se 3 (by rfl) ⟨932198, by rfl⟩ : syracuseStep 4971725 = 1864397) B1864397
theorem B1473747 : Blo 1472556 1473747 := bstep (se 1 (by rfl) ⟨1105310, by rfl⟩ : syracuseStep 1473747 = 2210621) B2210621
theorem B2211041 : Blo 1472556 2211041 := bstep (se 2 (by rfl) ⟨829140, by rfl⟩ : syracuseStep 2211041 = 1658281) B1658281
theorem B16145635 : Blo 1472556 16145635 := bstep (se 1 (by rfl) ⟨12109226, by rfl⟩ : syracuseStep 16145635 = 24218453) B24218453
theorem B1473763 : Blo 1472556 1473763 := bstep (se 1 (by rfl) ⟨1105322, by rfl⟩ : syracuseStep 1473763 = 2210645) B2210645
theorem B1473779 : Blo 1472556 1473779 := bstep (se 1 (by rfl) ⟨1105334, by rfl⟩ : syracuseStep 1473779 = 2210669) B2210669
theorem B2211059 : Blo 1472556 2211059 := bstep (se 1 (by rfl) ⟨1658294, by rfl⟩ : syracuseStep 2211059 = 3316589) B3316589
theorem B4971779 : Blo 1472556 4971779 := bstep (se 1 (by rfl) ⟨3728834, by rfl⟩ : syracuseStep 4971779 = 7457669) B7457669
theorem B1473795 : Blo 1472556 1473795 := bstep (se 1 (by rfl) ⟨1105346, by rfl⟩ : syracuseStep 1473795 = 2210693) B2210693
theorem B2211089 : Blo 1472556 2211089 := bstep (se 2 (by rfl) ⟨829158, by rfl⟩ : syracuseStep 2211089 = 1658317) B1658317
theorem B1473811 : Blo 1472556 1473811 := bstep (se 1 (by rfl) ⟨1105358, by rfl⟩ : syracuseStep 1473811 = 2210717) B2210717
theorem B1473827 : Blo 1472556 1473827 := bstep (se 1 (by rfl) ⟨1105370, by rfl⟩ : syracuseStep 1473827 = 2210741) B2210741
theorem B2211107 : Blo 1472556 2211107 := bstep (se 1 (by rfl) ⟨1658330, by rfl⟩ : syracuseStep 2211107 = 3316661) B3316661
theorem B9706787 : Blo 1472556 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B3145009 : Blo 1472556 3145009 := bstep (se 2 (by rfl) ⟨1179378, by rfl⟩ : syracuseStep 3145009 = 2358757) B2358757
theorem B1473843 : Blo 1472556 1473843 := bstep (se 1 (by rfl) ⟨1105382, by rfl⟩ : syracuseStep 1473843 = 2210765) B2210765
theorem B2211137 : Blo 1472556 2211137 := bstep (se 2 (by rfl) ⟨829176, by rfl⟩ : syracuseStep 2211137 = 1658353) B1658353
theorem B1473859 : Blo 1472556 1473859 := bstep (se 1 (by rfl) ⟨1105394, by rfl⟩ : syracuseStep 1473859 = 2210789) B2210789
theorem B1473875 : Blo 1472556 1473875 := bstep (se 1 (by rfl) ⟨1105406, by rfl⟩ : syracuseStep 1473875 = 2210813) B2210813
theorem B2211155 : Blo 1472556 2211155 := bstep (se 1 (by rfl) ⟨1658366, by rfl⟩ : syracuseStep 2211155 = 3316733) B3316733
theorem B5594467 : Blo 1472556 5594467 := bstep (se 1 (by rfl) ⟨4195850, by rfl⟩ : syracuseStep 5594467 = 8391701) B8391701
theorem B1473891 : Blo 1472556 1473891 := bstep (se 1 (by rfl) ⟨1105418, by rfl⟩ : syracuseStep 1473891 = 2210837) B2210837
theorem B7970147 : Blo 1472556 7970147 := bstep (se 1 (by rfl) ⟨5977610, by rfl⟩ : syracuseStep 7970147 = 11955221) B11955221
theorem B3538289 : Blo 1472556 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B2211185 : Blo 1472556 2211185 := bstep (se 2 (by rfl) ⟨829194, by rfl⟩ : syracuseStep 2211185 = 1658389) B1658389
theorem B1473907 : Blo 1472556 1473907 := bstep (se 1 (by rfl) ⟨1105430, by rfl⟩ : syracuseStep 1473907 = 2210861) B2210861
theorem B1473923 : Blo 1472556 1473923 := bstep (se 1 (by rfl) ⟨1105442, by rfl⟩ : syracuseStep 1473923 = 2210885) B2210885
theorem B2211203 : Blo 1472556 2211203 := bstep (se 1 (by rfl) ⟨1658402, by rfl⟩ : syracuseStep 2211203 = 3316805) B3316805
theorem B1473939 : Blo 1472556 1473939 := bstep (se 1 (by rfl) ⟨1105454, by rfl⟩ : syracuseStep 1473939 = 2210909) B2210909
theorem B2211233 : Blo 1472556 2211233 := bstep (se 2 (by rfl) ⟨829212, by rfl⟩ : syracuseStep 2211233 = 1658425) B1658425
theorem B1473955 : Blo 1472556 1473955 := bstep (se 1 (by rfl) ⟨1105466, by rfl⟩ : syracuseStep 1473955 = 2210933) B2210933
theorem B1473971 : Blo 1472556 1473971 := bstep (se 1 (by rfl) ⟨1105478, by rfl⟩ : syracuseStep 1473971 = 2210957) B2210957
theorem B2211251 : Blo 1472556 2211251 := bstep (se 1 (by rfl) ⟨1658438, by rfl⟩ : syracuseStep 2211251 = 3316877) B3316877
theorem B1473987 : Blo 1472556 1473987 := bstep (se 1 (by rfl) ⟨1105490, by rfl⟩ : syracuseStep 1473987 = 2210981) B2210981
theorem B2211281 : Blo 1472556 2211281 := bstep (se 2 (by rfl) ⟨829230, by rfl⟩ : syracuseStep 2211281 = 1658461) B1658461
theorem B3317201 : Blo 1472556 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B1474003 : Blo 1472556 1474003 := bstep (se 1 (by rfl) ⟨1105502, by rfl⟩ : syracuseStep 1474003 = 2211005) B2211005
theorem B7962083 : Blo 1472556 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B14155235 : Blo 1472556 14155235 := bstep (se 1 (by rfl) ⟨10616426, by rfl⟩ : syracuseStep 14155235 = 21232853) B21232853
theorem B1474019 : Blo 1472556 1474019 := bstep (se 1 (by rfl) ⟨1105514, by rfl⟩ : syracuseStep 1474019 = 2211029) B2211029
theorem B2211299 : Blo 1472556 2211299 := bstep (se 1 (by rfl) ⟨1658474, by rfl⟩ : syracuseStep 2211299 = 3316949) B3316949
theorem B1474035 : Blo 1472556 1474035 := bstep (se 1 (by rfl) ⟨1105526, by rfl⟩ : syracuseStep 1474035 = 2211053) B2211053
theorem B2211329 : Blo 1472556 2211329 := bstep (se 2 (by rfl) ⟨829248, by rfl⟩ : syracuseStep 2211329 = 1658497) B1658497
theorem B1474051 : Blo 1472556 1474051 := bstep (se 1 (by rfl) ⟨1105538, by rfl⟩ : syracuseStep 1474051 = 2211077) B2211077
theorem B9444869 : Blo 1472556 9444869 := bstep (se 4 (by rfl) ⟨885456, by rfl⟩ : syracuseStep 9444869 = 1770913) B1770913
theorem B4972049 : Blo 1472556 4972049 := bstep (se 2 (by rfl) ⟨1864518, by rfl⟩ : syracuseStep 4972049 = 3729037) B3729037
theorem B1474067 : Blo 1472556 1474067 := bstep (se 1 (by rfl) ⟨1105550, by rfl⟩ : syracuseStep 1474067 = 2211101) B2211101
theorem B2211347 : Blo 1472556 2211347 := bstep (se 1 (by rfl) ⟨1658510, by rfl⟩ : syracuseStep 2211347 = 3317021) B3317021
theorem B1474083 : Blo 1472556 1474083 := bstep (se 1 (by rfl) ⟨1105562, by rfl⟩ : syracuseStep 1474083 = 2211125) B2211125
theorem B2211377 : Blo 1472556 2211377 := bstep (se 2 (by rfl) ⟨829266, by rfl⟩ : syracuseStep 2211377 = 1658533) B1658533
theorem B1474099 : Blo 1472556 1474099 := bstep (se 1 (by rfl) ⟨1105574, by rfl⟩ : syracuseStep 1474099 = 2211149) B2211149
theorem B2096707 : Blo 1472556 2096707 := bstep (se 1 (by rfl) ⟨1572530, by rfl⟩ : syracuseStep 2096707 = 3145061) B3145061
theorem B1474115 : Blo 1472556 1474115 := bstep (se 1 (by rfl) ⟨1105586, by rfl⟩ : syracuseStep 1474115 = 2211173) B2211173
theorem B2211395 : Blo 1472556 2211395 := bstep (se 1 (by rfl) ⟨1658546, by rfl⟩ : syracuseStep 2211395 = 3317093) B3317093
theorem B4193869 : Blo 1472556 4193869 := bstep (se 3 (by rfl) ⟨786350, by rfl⟩ : syracuseStep 4193869 = 1572701) B1572701
theorem B1474131 : Blo 1472556 1474131 := bstep (se 1 (by rfl) ⟨1105598, by rfl⟩ : syracuseStep 1474131 = 2211197) B2211197
theorem B2211425 : Blo 1472556 2211425 := bstep (se 2 (by rfl) ⟨829284, by rfl⟩ : syracuseStep 2211425 = 1658569) B1658569
theorem B4718179 : Blo 1472556 4718179 := bstep (se 1 (by rfl) ⟨3538634, by rfl⟩ : syracuseStep 4718179 = 7077269) B7077269
theorem B3833443 : Blo 1472556 3833443 := bstep (se 1 (by rfl) ⟨2875082, by rfl⟩ : syracuseStep 3833443 = 5750165) B5750165
theorem B1474147 : Blo 1472556 1474147 := bstep (se 1 (by rfl) ⟨1105610, by rfl⟩ : syracuseStep 1474147 = 2211221) B2211221
theorem B1474163 : Blo 1472556 1474163 := bstep (se 1 (by rfl) ⟨1105622, by rfl⟩ : syracuseStep 1474163 = 2211245) B2211245
theorem B2211443 : Blo 1472556 2211443 := bstep (se 1 (by rfl) ⟨1658582, by rfl⟩ : syracuseStep 2211443 = 3317165) B3317165
theorem B1474179 : Blo 1472556 1474179 := bstep (se 1 (by rfl) ⟨1105634, by rfl⟩ : syracuseStep 1474179 = 2211269) B2211269
theorem B2211473 : Blo 1472556 2211473 := bstep (se 2 (by rfl) ⟨829302, by rfl⟩ : syracuseStep 2211473 = 1658605) B1658605
theorem B1474195 : Blo 1472556 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B7962275 : Blo 1472556 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B1474211 : Blo 1472556 1474211 := bstep (se 1 (by rfl) ⟨1105658, by rfl⟩ : syracuseStep 1474211 = 2211317) B2211317
theorem B2211491 : Blo 1472556 2211491 := bstep (se 1 (by rfl) ⟨1658618, by rfl⟩ : syracuseStep 2211491 = 3317237) B3317237
theorem B1474227 : Blo 1472556 1474227 := bstep (se 1 (by rfl) ⟨1105670, by rfl⟩ : syracuseStep 1474227 = 2211341) B2211341
theorem B2211521 : Blo 1472556 2211521 := bstep (se 2 (by rfl) ⟨829320, by rfl⟩ : syracuseStep 2211521 = 1658641) B1658641
theorem B1474243 : Blo 1472556 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B1474259 : Blo 1472556 1474259 := bstep (se 1 (by rfl) ⟨1105694, by rfl⟩ : syracuseStep 1474259 = 2211389) B2211389
theorem B2211539 : Blo 1472556 2211539 := bstep (se 1 (by rfl) ⟨1658654, by rfl⟩ : syracuseStep 2211539 = 3317309) B3317309
theorem B1474275 : Blo 1472556 1474275 := bstep (se 1 (by rfl) ⟨1105706, by rfl⟩ : syracuseStep 1474275 = 2211413) B2211413
theorem B2211569 : Blo 1472556 2211569 := bstep (se 2 (by rfl) ⟨829338, by rfl⟩ : syracuseStep 2211569 = 1658677) B1658677
theorem B3317489 : Blo 1472556 3317489 := bstep (se 2 (by rfl) ⟨1244058, by rfl⟩ : syracuseStep 3317489 = 2488117) B2488117
theorem B1474291 : Blo 1472556 1474291 := bstep (se 1 (by rfl) ⟨1105718, by rfl⟩ : syracuseStep 1474291 = 2211437) B2211437
theorem B1474307 : Blo 1472556 1474307 := bstep (se 1 (by rfl) ⟨1105730, by rfl⟩ : syracuseStep 1474307 = 2211461) B2211461
theorem B2211587 : Blo 1472556 2211587 := bstep (se 1 (by rfl) ⟨1658690, by rfl⟩ : syracuseStep 2211587 = 3317381) B3317381
theorem B3317507 : Blo 1472556 3317507 := bstep (se 1 (by rfl) ⟨2488130, by rfl⟩ : syracuseStep 3317507 = 4976261) B4976261
theorem B1474323 : Blo 1472556 1474323 := bstep (se 1 (by rfl) ⟨1105742, by rfl⟩ : syracuseStep 1474323 = 2211485) B2211485
theorem B2211617 : Blo 1472556 2211617 := bstep (se 2 (by rfl) ⟨829356, by rfl⟩ : syracuseStep 2211617 = 1658713) B1658713
theorem B7462691 : Blo 1472556 7462691 := bstep (se 1 (by rfl) ⟨5597018, by rfl⟩ : syracuseStep 7462691 = 11194037) B11194037
theorem B1474339 : Blo 1472556 1474339 := bstep (se 1 (by rfl) ⟨1105754, by rfl⟩ : syracuseStep 1474339 = 2211509) B2211509
theorem B1474355 : Blo 1472556 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B2211635 : Blo 1472556 2211635 := bstep (se 1 (by rfl) ⟨1658726, by rfl⟩ : syracuseStep 2211635 = 3317453) B3317453
theorem B1474371 : Blo 1472556 1474371 := bstep (se 1 (by rfl) ⟨1105778, by rfl⟩ : syracuseStep 1474371 = 2211557) B2211557
theorem B2211665 : Blo 1472556 2211665 := bstep (se 2 (by rfl) ⟨829374, by rfl⟩ : syracuseStep 2211665 = 1658749) B1658749
theorem B1474387 : Blo 1472556 1474387 := bstep (se 1 (by rfl) ⟨1105790, by rfl⟩ : syracuseStep 1474387 = 2211581) B2211581
theorem B1474403 : Blo 1472556 1474403 := bstep (se 1 (by rfl) ⟨1105802, by rfl⟩ : syracuseStep 1474403 = 2211605) B2211605
theorem B2211683 : Blo 1472556 2211683 := bstep (se 1 (by rfl) ⟨1658762, by rfl⟩ : syracuseStep 2211683 = 3317525) B3317525
theorem B1474419 : Blo 1472556 1474419 := bstep (se 1 (by rfl) ⟨1105814, by rfl⟩ : syracuseStep 1474419 = 2211629) B2211629
theorem B2211713 : Blo 1472556 2211713 := bstep (se 2 (by rfl) ⟨829392, by rfl⟩ : syracuseStep 2211713 = 1658785) B1658785
theorem B1474435 : Blo 1472556 1474435 := bstep (se 1 (by rfl) ⟨1105826, by rfl⟩ : syracuseStep 1474435 = 2211653) B2211653
theorem B4480913 : Blo 1472556 4480913 := bstep (se 2 (by rfl) ⟨1680342, by rfl⟩ : syracuseStep 4480913 = 3360685) B3360685
theorem B1474451 : Blo 1472556 1474451 := bstep (se 1 (by rfl) ⟨1105838, by rfl⟩ : syracuseStep 1474451 = 2211677) B2211677
theorem B2211731 : Blo 1472556 2211731 := bstep (se 1 (by rfl) ⟨1658798, by rfl⟩ : syracuseStep 2211731 = 3317597) B3317597
theorem B8077219 : Blo 1472556 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B1474467 : Blo 1472556 1474467 := bstep (se 1 (by rfl) ⟨1105850, by rfl⟩ : syracuseStep 1474467 = 2211701) B2211701
theorem B4718513 : Blo 1472556 4718513 := bstep (se 2 (by rfl) ⟨1769442, by rfl⟩ : syracuseStep 4718513 = 3538885) B3538885
theorem B2211761 : Blo 1472556 2211761 := bstep (se 2 (by rfl) ⟨829410, by rfl⟩ : syracuseStep 2211761 = 1658821) B1658821
theorem B1474483 : Blo 1472556 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1474499 : Blo 1472556 1474499 := bstep (se 1 (by rfl) ⟨1105874, by rfl⟩ : syracuseStep 1474499 = 2211749) B2211749
theorem B2211779 : Blo 1472556 2211779 := bstep (se 1 (by rfl) ⟨1658834, by rfl⟩ : syracuseStep 2211779 = 3317669) B3317669
theorem B1474515 : Blo 1472556 1474515 := bstep (se 1 (by rfl) ⟨1105886, by rfl⟩ : syracuseStep 1474515 = 2211773) B2211773
theorem B2211809 : Blo 1472556 2211809 := bstep (se 2 (by rfl) ⟨829428, by rfl⟩ : syracuseStep 2211809 = 1658857) B1658857
theorem B1474531 : Blo 1472556 1474531 := bstep (se 1 (by rfl) ⟨1105898, by rfl⟩ : syracuseStep 1474531 = 2211797) B2211797
theorem B1474547 : Blo 1472556 1474547 := bstep (se 1 (by rfl) ⟨1105910, by rfl⟩ : syracuseStep 1474547 = 2211821) B2211821
theorem B2211827 : Blo 1472556 2211827 := bstep (se 1 (by rfl) ⟨1658870, by rfl⟩ : syracuseStep 2211827 = 3317741) B3317741
theorem B4718681 : Blo 1472556 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B1573111 : Blo 1472556 1573111 := bstep (se 1 (by rfl) ⟨1179833, by rfl⟩ : syracuseStep 1573111 = 2359667) B2359667
theorem B2359577 : Blo 1472556 2359577 := bstep (se 2 (by rfl) ⟨884841, by rfl⟩ : syracuseStep 2359577 = 1769683) B1769683
theorem B3727691 : Blo 1472556 3727691 := bstep (se 1 (by rfl) ⟨2795768, by rfl⟩ : syracuseStep 3727691 = 5591537) B5591537
theorem B45359473 : Blo 1472556 45359473 := bstep (se 2 (by rfl) ⟨17009802, by rfl⟩ : syracuseStep 45359473 = 34019605) B34019605
theorem B6291863 : Blo 1472556 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4973021 : Blo 1472556 4973021 := bstep (se 3 (by rfl) ⟨932441, by rfl⟩ : syracuseStep 4973021 = 1864883) B1864883
theorem B26894861 : Blo 1472556 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B5595713 : Blo 1472556 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B3728065 : Blo 1472556 3728065 := bstep (se 2 (by rfl) ⟨1398024, by rfl⟩ : syracuseStep 3728065 = 2796049) B2796049
theorem B10617635 : Blo 1472556 10617635 := bstep (se 1 (by rfl) ⟨7963226, by rfl⟩ : syracuseStep 10617635 = 15926453) B15926453
theorem B80634689 : Blo 1472556 80634689 := bstep (se 2 (by rfl) ⟨30238008, by rfl⟩ : syracuseStep 80634689 = 60476017) B60476017
theorem B7455563 : Blo 1472556 7455563 := bstep (se 1 (by rfl) ⟨5591672, by rfl⟩ : syracuseStep 7455563 = 11183345) B11183345
theorem B4719539 : Blo 1472556 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B4719667 : Blo 1472556 4719667 := bstep (se 1 (by rfl) ⟨3539750, by rfl⟩ : syracuseStep 4719667 = 7079501) B7079501
theorem B3540019 : Blo 1472556 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B4719809 : Blo 1472556 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B3728663 : Blo 1472556 3728663 := bstep (se 1 (by rfl) ⟨2796497, by rfl⟩ : syracuseStep 3728663 = 5592995) B5592995
theorem B2303257 : Blo 1472556 2303257 := bstep (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) B1727443
theorem B4719923 : Blo 1472556 4719923 := bstep (se 1 (by rfl) ⟨3539942, by rfl⟩ : syracuseStep 4719923 = 7079885) B7079885
theorem B3147059 : Blo 1472556 3147059 := bstep (se 1 (by rfl) ⟨2360294, by rfl⟩ : syracuseStep 3147059 = 4720589) B4720589
theorem B8070475 : Blo 1472556 8070475 := bstep (se 1 (by rfl) ⟨6052856, by rfl⟩ : syracuseStep 8070475 = 12105713) B12105713
theorem B2098649 : Blo 1472556 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B4974155 : Blo 1472556 4974155 := bstep (se 1 (by rfl) ⟨3730616, by rfl⟩ : syracuseStep 4974155 = 7461233) B7461233
theorem B107521667 : Blo 1472556 107521667 := bstep (se 1 (by rfl) ⟨80641250, by rfl⟩ : syracuseStep 107521667 = 161282501) B161282501
theorem B1771159 : Blo 1472556 1771159 := bstep (se 1 (by rfl) ⟨1328369, by rfl⟩ : syracuseStep 1771159 = 2656739) B2656739
theorem B4196033 : Blo 1472556 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B2655937 : Blo 1472556 2655937 := bstep (se 2 (by rfl) ⟨995976, by rfl⟩ : syracuseStep 2655937 = 1991953) B1991953
theorem B5310173 : Blo 1472556 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B4974425 : Blo 1472556 4974425 := bstep (se 2 (by rfl) ⟨1865409, by rfl⟩ : syracuseStep 4974425 = 3730819) B3730819
theorem B7464797 : Blo 1472556 7464797 := bstep (se 3 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 7464797 = 2799299) B2799299
theorem B1656715 : Blo 1472556 1656715 := bstep (se 1 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 1656715 = 2485073) B2485073
theorem B12117937 : Blo 1472556 12117937 := bstep (se 2 (by rfl) ⟨4544226, by rfl⟩ : syracuseStep 12117937 = 9088453) B9088453
theorem B1656823 : Blo 1472556 1656823 := bstep (se 1 (by rfl) ⟨1242617, by rfl⟩ : syracuseStep 1656823 = 2485235) B2485235
theorem B5597201 : Blo 1472556 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B3729473 : Blo 1472556 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B2099287 : Blo 1472556 2099287 := bstep (se 1 (by rfl) ⟨1574465, by rfl⟩ : syracuseStep 2099287 = 3148931) B3148931
theorem B2795609 : Blo 1472556 2795609 := bstep (se 2 (by rfl) ⟨1048353, by rfl⟩ : syracuseStep 2795609 = 2096707) B2096707
theorem B12585091 : Blo 1472556 12585091 := bstep (se 1 (by rfl) ⟨9438818, by rfl⟩ : syracuseStep 12585091 = 18877637) B18877637
theorem B1657003 : Blo 1472556 1657003 := bstep (se 1 (by rfl) ⟨1242752, by rfl⟩ : syracuseStep 1657003 = 2485505) B2485505
theorem B2656471 : Blo 1472556 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B4196569 : Blo 1472556 4196569 := bstep (se 2 (by rfl) ⟨1573713, by rfl⟩ : syracuseStep 4196569 = 3147427) B3147427
theorem B6383837 : Blo 1472556 6383837 := bstep (se 3 (by rfl) ⟨1196969, by rfl⟩ : syracuseStep 6383837 = 2393939) B2393939
theorem B1657111 : Blo 1472556 1657111 := bstep (se 1 (by rfl) ⟨1242833, by rfl⟩ : syracuseStep 1657111 = 2485667) B2485667
theorem B7375283 : Blo 1472556 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B3983809 : Blo 1472556 3983809 := bstep (se 2 (by rfl) ⟨1493928, by rfl⟩ : syracuseStep 3983809 = 2987857) B2987857
theorem B1657291 : Blo 1472556 1657291 := bstep (se 1 (by rfl) ⟨1242968, by rfl⟩ : syracuseStep 1657291 = 2485937) B2485937
theorem B3148247 : Blo 1472556 3148247 := bstep (se 1 (by rfl) ⟨2361185, by rfl⟩ : syracuseStep 3148247 = 4722371) B4722371
theorem B5597657 : Blo 1472556 5597657 := bstep (se 2 (by rfl) ⟨2099121, by rfl⟩ : syracuseStep 5597657 = 4198243) B4198243
theorem B3361267 : Blo 1472556 3361267 := bstep (se 1 (by rfl) ⟨2520950, by rfl⟩ : syracuseStep 3361267 = 5041901) B5041901
theorem B4975127 : Blo 1472556 4975127 := bstep (se 1 (by rfl) ⟨3731345, by rfl⟩ : syracuseStep 4975127 = 7462691) B7462691
theorem B1657399 : Blo 1472556 1657399 := bstep (se 1 (by rfl) ⟨1243049, by rfl⟩ : syracuseStep 1657399 = 2486099) B2486099
theorem B13437505 : Blo 1472556 13437505 := bstep (se 2 (by rfl) ⟨5039064, by rfl⟩ : syracuseStep 13437505 = 10078129) B10078129
theorem B7457345 : Blo 1472556 7457345 := bstep (se 2 (by rfl) ⟨2796504, by rfl⟩ : syracuseStep 7457345 = 5593009) B5593009
theorem B3730009 : Blo 1472556 3730009 := bstep (se 2 (by rfl) ⟨1398753, by rfl⟩ : syracuseStep 3730009 = 2797507) B2797507
theorem B5597869 : Blo 1472556 5597869 := bstep (se 3 (by rfl) ⟨1049600, by rfl⟩ : syracuseStep 5597869 = 2099201) B2099201
theorem B22686389 : Blo 1472556 22686389 := bstep (se 5 (by rfl) ⟨1063424, by rfl⟩ : syracuseStep 22686389 = 2126849) B2126849
theorem B1657579 : Blo 1472556 1657579 := bstep (se 1 (by rfl) ⟨1243184, by rfl⟩ : syracuseStep 1657579 = 2486369) B2486369
theorem B6294323 : Blo 1472556 6294323 := bstep (se 1 (by rfl) ⟨4720742, by rfl⟩ : syracuseStep 6294323 = 9441485) B9441485
theorem B2796353 : Blo 1472556 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B1657687 : Blo 1472556 1657687 := bstep (se 1 (by rfl) ⟨1243265, by rfl⟩ : syracuseStep 1657687 = 2486531) B2486531
theorem B5598173 : Blo 1472556 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B1657867 : Blo 1472556 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B4975667 : Blo 1472556 4975667 := bstep (se 1 (by rfl) ⟨3731750, by rfl⟩ : syracuseStep 4975667 = 7463501) B7463501
theorem B12586049 : Blo 1472556 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B7179329 : Blo 1472556 7179329 := bstep (se 2 (by rfl) ⟨2692248, by rfl⟩ : syracuseStep 7179329 = 5384497) B5384497
theorem B2796619 : Blo 1472556 2796619 := bstep (se 1 (by rfl) ⟨2097464, by rfl⟩ : syracuseStep 2796619 = 4194929) B4194929
theorem B1657975 : Blo 1472556 1657975 := bstep (se 1 (by rfl) ⟨1243481, by rfl⟩ : syracuseStep 1657975 = 2486963) B2486963
theorem B7179443 : Blo 1472556 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B2485451 : Blo 1472556 2485451 := bstep (se 1 (by rfl) ⟨1864088, by rfl⟩ : syracuseStep 2485451 = 3728177) B3728177
theorem B1658155 : Blo 1472556 1658155 := bstep (se 1 (by rfl) ⟨1243616, by rfl⟩ : syracuseStep 1658155 = 2487233) B2487233
theorem B4975937 : Blo 1472556 4975937 := bstep (se 2 (by rfl) ⟨1865976, by rfl⟩ : syracuseStep 4975937 = 3731953) B3731953
theorem B2485579 : Blo 1472556 2485579 := bstep (se 1 (by rfl) ⟨1864184, by rfl⟩ : syracuseStep 2485579 = 3728369) B3728369
theorem B1658263 : Blo 1472556 1658263 := bstep (se 1 (by rfl) ⟨1243697, by rfl⟩ : syracuseStep 1658263 = 2487395) B2487395
theorem B2485721 : Blo 1472556 2485721 := bstep (se 2 (by rfl) ⟨932145, by rfl⟩ : syracuseStep 2485721 = 1864291) B1864291
theorem B3984857 : Blo 1472556 3984857 := bstep (se 2 (by rfl) ⟨1494321, by rfl⟩ : syracuseStep 3984857 = 2988643) B2988643
theorem B3149273 : Blo 1472556 3149273 := bstep (se 2 (by rfl) ⟨1180977, by rfl⟩ : syracuseStep 3149273 = 2361955) B2361955
theorem B2797067 : Blo 1472556 2797067 := bstep (se 1 (by rfl) ⟨2097800, by rfl⟩ : syracuseStep 2797067 = 4195601) B4195601
theorem B1658443 : Blo 1472556 1658443 := bstep (se 1 (by rfl) ⟨1243832, by rfl⟩ : syracuseStep 1658443 = 2487665) B2487665
theorem B2485849 : Blo 1472556 2485849 := bstep (se 2 (by rfl) ⟨932193, by rfl⟩ : syracuseStep 2485849 = 1864387) B1864387
theorem B10620517 : Blo 1472556 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B9440869 : Blo 1472556 9440869 := bstep (se 4 (by rfl) ⟨885081, by rfl⟩ : syracuseStep 9440869 = 1770163) B1770163
theorem B3313331 : Blo 1472556 3313331 := bstep (se 1 (by rfl) ⟨2484998, by rfl⟩ : syracuseStep 3313331 = 4969997) B4969997
theorem B3731123 : Blo 1472556 3731123 := bstep (se 1 (by rfl) ⟨2798342, by rfl⟩ : syracuseStep 3731123 = 5596685) B5596685
theorem B1658551 : Blo 1472556 1658551 := bstep (se 1 (by rfl) ⟨1243913, by rfl⟩ : syracuseStep 1658551 = 2487827) B2487827
theorem B2797249 : Blo 1472556 2797249 := bstep (se 2 (by rfl) ⟨1048968, by rfl⟩ : syracuseStep 2797249 = 2097937) B2097937
theorem B3313367 : Blo 1472556 3313367 := bstep (se 1 (by rfl) ⟨2485025, by rfl⟩ : syracuseStep 3313367 = 4970051) B4970051
theorem B8392409 : Blo 1472556 8392409 := bstep (se 2 (by rfl) ⟨3147153, by rfl⟩ : syracuseStep 8392409 = 6294307) B6294307
theorem B4976477 : Blo 1472556 4976477 := bstep (se 3 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 4976477 = 1866179) B1866179
theorem B1658731 : Blo 1472556 1658731 := bstep (se 1 (by rfl) ⟨1244048, by rfl⟩ : syracuseStep 1658731 = 2488097) B2488097
theorem B3313547 : Blo 1472556 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B3313601 : Blo 1472556 3313601 := bstep (se 2 (by rfl) ⟨1242600, by rfl⟩ : syracuseStep 3313601 = 2485201) B2485201
theorem B1658839 : Blo 1472556 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B3731417 : Blo 1472556 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B2797591 : Blo 1472556 2797591 := bstep (se 1 (by rfl) ⟨2098193, by rfl⟩ : syracuseStep 2797591 = 4196387) B4196387
theorem B6557761 : Blo 1472556 6557761 := bstep (se 2 (by rfl) ⟨2459160, by rfl⟩ : syracuseStep 6557761 = 4918321) B4918321
theorem B30642245 : Blo 1472556 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B4722781 : Blo 1472556 4722781 := bstep (se 3 (by rfl) ⟨885521, by rfl⟩ : syracuseStep 4722781 = 1771043) B1771043
theorem B4198493 : Blo 1472556 4198493 := bstep (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) B1574435
theorem B2486423 : Blo 1472556 2486423 := bstep (se 1 (by rfl) ⟨1864817, by rfl⟩ : syracuseStep 2486423 = 3729635) B3729635
theorem B3313817 : Blo 1472556 3313817 := bstep (se 2 (by rfl) ⟨1242681, by rfl⟩ : syracuseStep 3313817 = 2485363) B2485363
theorem B3313907 : Blo 1472556 3313907 := bstep (se 1 (by rfl) ⟨2485430, by rfl⟩ : syracuseStep 3313907 = 4970861) B4970861
theorem B2797811 : Blo 1472556 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B3313943 : Blo 1472556 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B2486551 : Blo 1472556 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B3314123 : Blo 1472556 3314123 := bstep (se 1 (by rfl) ⟨2485592, by rfl⟩ : syracuseStep 3314123 = 4971185) B4971185
theorem B2798039 : Blo 1472556 2798039 := bstep (se 1 (by rfl) ⟨2098529, by rfl⟩ : syracuseStep 2798039 = 4197059) B4197059
theorem B7459289 : Blo 1472556 7459289 := bstep (se 2 (by rfl) ⟨2797233, by rfl⟩ : syracuseStep 7459289 = 5594467) B5594467
theorem B3314177 : Blo 1472556 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B24228503 : Blo 1472556 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B6296237 : Blo 1472556 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B43037381 : Blo 1472556 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B20157133 : Blo 1472556 20157133 := bstep (se 3 (by rfl) ⟨3779462, by rfl⟩ : syracuseStep 20157133 = 7558925) B7558925
theorem B3314393 : Blo 1472556 3314393 := bstep (se 2 (by rfl) ⟨1242897, by rfl⟩ : syracuseStep 3314393 = 2485795) B2485795
theorem B2798297 : Blo 1472556 2798297 := bstep (se 2 (by rfl) ⟨1049361, by rfl⟩ : syracuseStep 2798297 = 2098723) B2098723
theorem B5591825 : Blo 1472556 5591825 := bstep (se 2 (by rfl) ⟨2096934, by rfl⟩ : syracuseStep 5591825 = 4193869) B4193869
theorem B18879277 : Blo 1472556 18879277 := bstep (se 3 (by rfl) ⟨3539864, by rfl⟩ : syracuseStep 18879277 = 7079729) B7079729
theorem B12112685 : Blo 1472556 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B3314483 : Blo 1472556 3314483 := bstep (se 1 (by rfl) ⟨2485862, by rfl⟩ : syracuseStep 3314483 = 4971725) B4971725
theorem B7566155 : Blo 1472556 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B3314519 : Blo 1472556 3314519 := bstep (se 1 (by rfl) ⟨2485889, by rfl⟩ : syracuseStep 3314519 = 4971779) B4971779
theorem B43078501 : Blo 1472556 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B2487179 : Blo 1472556 2487179 := bstep (se 1 (by rfl) ⟨1865384, by rfl⟩ : syracuseStep 2487179 = 3730769) B3730769
theorem B5313431 : Blo 1472556 5313431 := bstep (se 1 (by rfl) ⟨3985073, by rfl⟩ : syracuseStep 5313431 = 7970147) B7970147
theorem B2241433 : Blo 1472556 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B6722477 : Blo 1472556 6722477 := bstep (se 3 (by rfl) ⟨1260464, by rfl⟩ : syracuseStep 6722477 = 2520929) B2520929
theorem B1474551 : Blo 1472556 1474551 := bstep (se 1 (by rfl) ⟨1105913, by rfl⟩ : syracuseStep 1474551 = 2211827) B2211827
theorem B6296579 : Blo 1472556 6296579 := bstep (se 1 (by rfl) ⟨4722434, by rfl⟩ : syracuseStep 6296579 = 9444869) B9444869
theorem B3314699 : Blo 1472556 3314699 := bstep (se 1 (by rfl) ⟨2486024, by rfl⟩ : syracuseStep 3314699 = 4972049) B4972049
theorem B2487307 : Blo 1472556 2487307 := bstep (se 1 (by rfl) ⟨1865480, by rfl⟩ : syracuseStep 2487307 = 3730961) B3730961
theorem B3314753 : Blo 1472556 3314753 := bstep (se 2 (by rfl) ⟨1243032, by rfl⟩ : syracuseStep 3314753 = 2486065) B2486065
theorem B2208857 : Blo 1472556 2208857 := bstep (se 2 (by rfl) ⟨828321, by rfl⟩ : syracuseStep 2208857 = 1656643) B1656643
theorem B8508509 : Blo 1472556 8508509 := bstep (se 3 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 8508509 = 3190691) B3190691
theorem B2798707 : Blo 1472556 2798707 := bstep (se 1 (by rfl) ⟨2099030, by rfl⟩ : syracuseStep 2798707 = 4198061) B4198061
theorem B2487449 : Blo 1472556 2487449 := bstep (se 2 (by rfl) ⟨932793, by rfl⟩ : syracuseStep 2487449 = 1865587) B1865587
theorem B2208971 : Blo 1472556 2208971 := bstep (se 1 (by rfl) ⟨1656728, by rfl⟩ : syracuseStep 2208971 = 3313457) B3313457
theorem B2208983 : Blo 1472556 2208983 := bstep (se 1 (by rfl) ⟨1656737, by rfl⟩ : syracuseStep 2208983 = 3313475) B3313475
theorem B2987275 : Blo 1472556 2987275 := bstep (se 1 (by rfl) ⟨2240456, by rfl⟩ : syracuseStep 2987275 = 4480913) B4480913
theorem B2209049 : Blo 1472556 2209049 := bstep (se 2 (by rfl) ⟨828393, by rfl⟩ : syracuseStep 2209049 = 1656787) B1656787
theorem B3314969 : Blo 1472556 3314969 := bstep (se 2 (by rfl) ⟨1243113, by rfl⟩ : syracuseStep 3314969 = 2486227) B2486227
theorem B2487577 : Blo 1472556 2487577 := bstep (se 2 (by rfl) ⟨932841, by rfl⟩ : syracuseStep 2487577 = 1865683) B1865683
theorem B1865035 : Blo 1472556 1865035 := bstep (se 1 (by rfl) ⟨1398776, by rfl⟩ : syracuseStep 1865035 = 2797553) B2797553
theorem B12596573 : Blo 1472556 12596573 := bstep (se 3 (by rfl) ⟨2361857, by rfl⟩ : syracuseStep 12596573 = 4723715) B4723715
theorem B3315059 : Blo 1472556 3315059 := bstep (se 1 (by rfl) ⟨2486294, by rfl⟩ : syracuseStep 3315059 = 4972589) B4972589
theorem B2209163 : Blo 1472556 2209163 := bstep (se 1 (by rfl) ⟨1656872, by rfl⟩ : syracuseStep 2209163 = 3313745) B3313745
theorem B2209175 : Blo 1472556 2209175 := bstep (se 1 (by rfl) ⟨1656881, by rfl⟩ : syracuseStep 2209175 = 3313763) B3313763
theorem B3315095 : Blo 1472556 3315095 := bstep (se 1 (by rfl) ⟨2486321, by rfl⟩ : syracuseStep 3315095 = 4972643) B4972643
theorem B5592523 : Blo 1472556 5592523 := bstep (se 1 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 5592523 = 8388785) B8388785
theorem B2209241 : Blo 1472556 2209241 := bstep (se 2 (by rfl) ⟨828465, by rfl⟩ : syracuseStep 2209241 = 1656931) B1656931
theorem B2209355 : Blo 1472556 2209355 := bstep (se 1 (by rfl) ⟨1657016, by rfl⟩ : syracuseStep 2209355 = 3314033) B3314033
theorem B3315275 : Blo 1472556 3315275 := bstep (se 1 (by rfl) ⟨2486456, by rfl⟩ : syracuseStep 3315275 = 4972913) B4972913
theorem B2209367 : Blo 1472556 2209367 := bstep (se 1 (by rfl) ⟨1657025, by rfl⟩ : syracuseStep 2209367 = 3314051) B3314051
theorem B2799193 : Blo 1472556 2799193 := bstep (se 2 (by rfl) ⟨1049697, by rfl⟩ : syracuseStep 2799193 = 2099395) B2099395
theorem B3315329 : Blo 1472556 3315329 := bstep (se 2 (by rfl) ⟨1243248, by rfl⟩ : syracuseStep 3315329 = 2486497) B2486497
theorem B2209433 : Blo 1472556 2209433 := bstep (se 2 (by rfl) ⟨828537, by rfl⟩ : syracuseStep 2209433 = 1657075) B1657075
theorem B5592797 : Blo 1472556 5592797 := bstep (se 3 (by rfl) ⟨1048649, by rfl⟩ : syracuseStep 5592797 = 2097299) B2097299
theorem B2209547 : Blo 1472556 2209547 := bstep (se 1 (by rfl) ⟨1657160, by rfl⟩ : syracuseStep 2209547 = 3314321) B3314321
theorem B2209559 : Blo 1472556 2209559 := bstep (se 1 (by rfl) ⟨1657169, by rfl⟩ : syracuseStep 2209559 = 3314339) B3314339
theorem B4544279 : Blo 1472556 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B21239597 : Blo 1472556 21239597 := bstep (se 3 (by rfl) ⟨3982424, by rfl⟩ : syracuseStep 21239597 = 7964849) B7964849
theorem B5314355 : Blo 1472556 5314355 := bstep (se 1 (by rfl) ⟨3985766, by rfl⟩ : syracuseStep 5314355 = 7971533) B7971533
theorem B2488151 : Blo 1472556 2488151 := bstep (se 1 (by rfl) ⟨1866113, by rfl⟩ : syracuseStep 2488151 = 3732227) B3732227
theorem B2209625 : Blo 1472556 2209625 := bstep (se 2 (by rfl) ⟨828609, by rfl⟩ : syracuseStep 2209625 = 1657219) B1657219
theorem B3315545 : Blo 1472556 3315545 := bstep (se 2 (by rfl) ⟨1243329, by rfl⟩ : syracuseStep 3315545 = 2486659) B2486659
theorem B25163621 : Blo 1472556 25163621 := bstep (se 4 (by rfl) ⟨2359089, by rfl⟩ : syracuseStep 25163621 = 4718179) B4718179
theorem B3315635 : Blo 1472556 3315635 := bstep (se 1 (by rfl) ⟨2486726, by rfl⟩ : syracuseStep 3315635 = 4973453) B4973453
theorem B2209739 : Blo 1472556 2209739 := bstep (se 1 (by rfl) ⟨1657304, by rfl⟩ : syracuseStep 2209739 = 3314609) B3314609
theorem B2209751 : Blo 1472556 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B3315671 : Blo 1472556 3315671 := bstep (se 1 (by rfl) ⟨2486753, by rfl⟩ : syracuseStep 3315671 = 4973507) B4973507
theorem B2488279 : Blo 1472556 2488279 := bstep (se 1 (by rfl) ⟨1866209, by rfl⟩ : syracuseStep 2488279 = 3732419) B3732419
theorem B2209817 : Blo 1472556 2209817 := bstep (se 2 (by rfl) ⟨828681, by rfl⟩ : syracuseStep 2209817 = 1657363) B1657363
theorem B7460909 : Blo 1472556 7460909 := bstep (se 3 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 7460909 = 2797841) B2797841
theorem B1472567 : Blo 1472556 1472567 := bstep (se 1 (by rfl) ⟨1104425, by rfl⟩ : syracuseStep 1472567 = 2208851) B2208851
theorem B1472587 : Blo 1472556 1472587 := bstep (se 1 (by rfl) ⟨1104440, by rfl⟩ : syracuseStep 1472587 = 2208881) B2208881
theorem B1472599 : Blo 1472556 1472599 := bstep (se 1 (by rfl) ⟨1104449, by rfl⟩ : syracuseStep 1472599 = 2208899) B2208899
theorem B1472619 : Blo 1472556 1472619 := bstep (se 1 (by rfl) ⟨1104464, by rfl⟩ : syracuseStep 1472619 = 2208929) B2208929
theorem B1472631 : Blo 1472556 1472631 := bstep (se 1 (by rfl) ⟨1104473, by rfl⟩ : syracuseStep 1472631 = 2208947) B2208947
theorem B6813827 : Blo 1472556 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B1472651 : Blo 1472556 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B2209931 : Blo 1472556 2209931 := bstep (se 1 (by rfl) ⟨1657448, by rfl⟩ : syracuseStep 2209931 = 3314897) B3314897
theorem B3315851 : Blo 1472556 3315851 := bstep (se 1 (by rfl) ⟨2486888, by rfl⟩ : syracuseStep 3315851 = 4973777) B4973777
theorem B1472663 : Blo 1472556 1472663 := bstep (se 1 (by rfl) ⟨1104497, by rfl⟩ : syracuseStep 1472663 = 2208995) B2208995
theorem B2209943 : Blo 1472556 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1472683 : Blo 1472556 1472683 := bstep (se 1 (by rfl) ⟨1104512, by rfl⟩ : syracuseStep 1472683 = 2209025) B2209025
theorem B1472695 : Blo 1472556 1472695 := bstep (se 1 (by rfl) ⟨1104521, by rfl⟩ : syracuseStep 1472695 = 2209043) B2209043
theorem B3315905 : Blo 1472556 3315905 := bstep (se 2 (by rfl) ⟨1243464, by rfl⟩ : syracuseStep 3315905 = 2486929) B2486929
theorem B1472715 : Blo 1472556 1472715 := bstep (se 1 (by rfl) ⟨1104536, by rfl⟩ : syracuseStep 1472715 = 2209073) B2209073
theorem B4970699 : Blo 1472556 4970699 := bstep (se 1 (by rfl) ⟨3728024, by rfl⟩ : syracuseStep 4970699 = 7456049) B7456049
theorem B1472727 : Blo 1472556 1472727 := bstep (se 1 (by rfl) ⟨1104545, by rfl⟩ : syracuseStep 1472727 = 2209091) B2209091
theorem B2210009 : Blo 1472556 2210009 := bstep (se 2 (by rfl) ⟨828753, by rfl⟩ : syracuseStep 2210009 = 1657507) B1657507
theorem B1472747 : Blo 1472556 1472747 := bstep (se 1 (by rfl) ⟨1104560, by rfl⟩ : syracuseStep 1472747 = 2209121) B2209121
theorem B1472759 : Blo 1472556 1472759 := bstep (se 1 (by rfl) ⟨1104569, by rfl⟩ : syracuseStep 1472759 = 2209139) B2209139
theorem B1472779 : Blo 1472556 1472779 := bstep (se 1 (by rfl) ⟨1104584, by rfl⟩ : syracuseStep 1472779 = 2209169) B2209169
theorem B1472791 : Blo 1472556 1472791 := bstep (se 1 (by rfl) ⟨1104593, by rfl⟩ : syracuseStep 1472791 = 2209187) B2209187
theorem B1866007 : Blo 1472556 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B2046233 : Blo 1472556 2046233 := bstep (se 2 (by rfl) ⟨767337, by rfl⟩ : syracuseStep 2046233 = 1534675) B1534675
theorem B1472811 : Blo 1472556 1472811 := bstep (se 1 (by rfl) ⟨1104608, by rfl⟩ : syracuseStep 1472811 = 2209217) B2209217
theorem B9435437 : Blo 1472556 9435437 := bstep (se 3 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 9435437 = 3538289) B3538289
theorem B1472823 : Blo 1472556 1472823 := bstep (se 1 (by rfl) ⟨1104617, by rfl⟩ : syracuseStep 1472823 = 2209235) B2209235
theorem B8395073 : Blo 1472556 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B1472843 : Blo 1472556 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B2210123 : Blo 1472556 2210123 := bstep (se 1 (by rfl) ⟨1657592, by rfl⟩ : syracuseStep 2210123 = 3315185) B3315185
theorem B1890635 : Blo 1472556 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B1472855 : Blo 1472556 1472855 := bstep (se 1 (by rfl) ⟨1104641, by rfl⟩ : syracuseStep 1472855 = 2209283) B2209283
theorem B2210135 : Blo 1472556 2210135 := bstep (se 1 (by rfl) ⟨1657601, by rfl⟩ : syracuseStep 2210135 = 3315203) B3315203
theorem B1472875 : Blo 1472556 1472875 := bstep (se 1 (by rfl) ⟨1104656, by rfl⟩ : syracuseStep 1472875 = 2209313) B2209313
theorem B1472887 : Blo 1472556 1472887 := bstep (se 1 (by rfl) ⟨1104665, by rfl⟩ : syracuseStep 1472887 = 2209331) B2209331
theorem B1472907 : Blo 1472556 1472907 := bstep (se 1 (by rfl) ⟨1104680, by rfl⟩ : syracuseStep 1472907 = 2209361) B2209361
theorem B1472919 : Blo 1472556 1472919 := bstep (se 1 (by rfl) ⟨1104689, by rfl⟩ : syracuseStep 1472919 = 2209379) B2209379
theorem B5593495 : Blo 1472556 5593495 := bstep (se 1 (by rfl) ⟨4195121, by rfl⟩ : syracuseStep 5593495 = 8390243) B8390243
theorem B2210201 : Blo 1472556 2210201 := bstep (se 2 (by rfl) ⟨828825, by rfl⟩ : syracuseStep 2210201 = 1657651) B1657651
theorem B11950487 : Blo 1472556 11950487 := bstep (se 1 (by rfl) ⟨8962865, by rfl⟩ : syracuseStep 11950487 = 17925731) B17925731
theorem B3316121 : Blo 1472556 3316121 := bstep (se 2 (by rfl) ⟨1243545, by rfl⟩ : syracuseStep 3316121 = 2487091) B2487091
theorem B1472939 : Blo 1472556 1472939 := bstep (se 1 (by rfl) ⟨1104704, by rfl⟩ : syracuseStep 1472939 = 2209409) B2209409
theorem B5454253 : Blo 1472556 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B21813683 : Blo 1472556 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B1472951 : Blo 1472556 1472951 := bstep (se 1 (by rfl) ⟨1104713, by rfl⟩ : syracuseStep 1472951 = 2209427) B2209427
theorem B1472971 : Blo 1472556 1472971 := bstep (se 1 (by rfl) ⟨1104728, by rfl⟩ : syracuseStep 1472971 = 2209457) B2209457
theorem B1472983 : Blo 1472556 1472983 := bstep (se 1 (by rfl) ⟨1104737, by rfl⟩ : syracuseStep 1472983 = 2209475) B2209475
theorem B4970969 : Blo 1472556 4970969 := bstep (se 2 (by rfl) ⟨1864113, by rfl⟩ : syracuseStep 4970969 = 3728227) B3728227
theorem B1473003 : Blo 1472556 1473003 := bstep (se 1 (by rfl) ⟨1104752, by rfl⟩ : syracuseStep 1473003 = 2209505) B2209505
theorem B3316211 : Blo 1472556 3316211 := bstep (se 1 (by rfl) ⟨2487158, by rfl⟩ : syracuseStep 3316211 = 4974317) B4974317
theorem B1473015 : Blo 1472556 1473015 := bstep (se 1 (by rfl) ⟨1104761, by rfl⟩ : syracuseStep 1473015 = 2209523) B2209523
theorem B1473035 : Blo 1472556 1473035 := bstep (se 1 (by rfl) ⟨1104776, by rfl⟩ : syracuseStep 1473035 = 2209553) B2209553
theorem B2210315 : Blo 1472556 2210315 := bstep (se 1 (by rfl) ⟨1657736, by rfl⟩ : syracuseStep 2210315 = 3315473) B3315473
theorem B1473047 : Blo 1472556 1473047 := bstep (se 1 (by rfl) ⟨1104785, by rfl⟩ : syracuseStep 1473047 = 2209571) B2209571
theorem B2210327 : Blo 1472556 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B3316247 : Blo 1472556 3316247 := bstep (se 1 (by rfl) ⟨2487185, by rfl⟩ : syracuseStep 3316247 = 4974371) B4974371
theorem B1473067 : Blo 1472556 1473067 := bstep (se 1 (by rfl) ⟨1104800, by rfl⟩ : syracuseStep 1473067 = 2209601) B2209601
theorem B1473079 : Blo 1472556 1473079 := bstep (se 1 (by rfl) ⟨1104809, by rfl⟩ : syracuseStep 1473079 = 2209619) B2209619
theorem B1473099 : Blo 1472556 1473099 := bstep (se 1 (by rfl) ⟨1104824, by rfl⟩ : syracuseStep 1473099 = 2209649) B2209649
theorem B1473111 : Blo 1472556 1473111 := bstep (se 1 (by rfl) ⟨1104833, by rfl⟩ : syracuseStep 1473111 = 2209667) B2209667
theorem B2210393 : Blo 1472556 2210393 := bstep (se 2 (by rfl) ⟨828897, by rfl⟩ : syracuseStep 2210393 = 1657795) B1657795
theorem B1473131 : Blo 1472556 1473131 := bstep (se 1 (by rfl) ⟨1104848, by rfl⟩ : syracuseStep 1473131 = 2209697) B2209697
theorem B1473143 : Blo 1472556 1473143 := bstep (se 1 (by rfl) ⟨1104857, by rfl⟩ : syracuseStep 1473143 = 2209715) B2209715
theorem B1473163 : Blo 1472556 1473163 := bstep (se 1 (by rfl) ⟨1104872, by rfl⟩ : syracuseStep 1473163 = 2209745) B2209745
theorem B1473175 : Blo 1472556 1473175 := bstep (se 1 (by rfl) ⟨1104881, by rfl⟩ : syracuseStep 1473175 = 2209763) B2209763
theorem B1473195 : Blo 1472556 1473195 := bstep (se 1 (by rfl) ⟨1104896, by rfl⟩ : syracuseStep 1473195 = 2209793) B2209793
theorem B1473207 : Blo 1472556 1473207 := bstep (se 1 (by rfl) ⟨1104905, by rfl⟩ : syracuseStep 1473207 = 2209811) B2209811
theorem B1473227 : Blo 1472556 1473227 := bstep (se 1 (by rfl) ⟨1104920, by rfl⟩ : syracuseStep 1473227 = 2209841) B2209841
theorem B2210507 : Blo 1472556 2210507 := bstep (se 1 (by rfl) ⟨1657880, by rfl⟩ : syracuseStep 2210507 = 3315761) B3315761
theorem B3316427 : Blo 1472556 3316427 := bstep (se 1 (by rfl) ⟨2487320, by rfl⟩ : syracuseStep 3316427 = 4974641) B4974641
theorem B1473239 : Blo 1472556 1473239 := bstep (se 1 (by rfl) ⟨1104929, by rfl⟩ : syracuseStep 1473239 = 2209859) B2209859
theorem B2210519 : Blo 1472556 2210519 := bstep (se 1 (by rfl) ⟨1657889, by rfl⟩ : syracuseStep 2210519 = 3315779) B3315779
theorem B1473259 : Blo 1472556 1473259 := bstep (se 1 (by rfl) ⟨1104944, by rfl⟩ : syracuseStep 1473259 = 2209889) B2209889
theorem B1473271 : Blo 1472556 1473271 := bstep (se 1 (by rfl) ⟨1104953, by rfl⟩ : syracuseStep 1473271 = 2209907) B2209907
theorem B3316481 : Blo 1472556 3316481 := bstep (se 2 (by rfl) ⟨1243680, by rfl⟩ : syracuseStep 3316481 = 2487361) B2487361
theorem B1473291 : Blo 1472556 1473291 := bstep (se 1 (by rfl) ⟨1104968, by rfl⟩ : syracuseStep 1473291 = 2209937) B2209937
theorem B1473303 : Blo 1472556 1473303 := bstep (se 1 (by rfl) ⟨1104977, by rfl⟩ : syracuseStep 1473303 = 2209955) B2209955
theorem B2210585 : Blo 1472556 2210585 := bstep (se 2 (by rfl) ⟨828969, by rfl⟩ : syracuseStep 2210585 = 1657939) B1657939
theorem B1473323 : Blo 1472556 1473323 := bstep (se 1 (by rfl) ⟨1104992, by rfl⟩ : syracuseStep 1473323 = 2209985) B2209985
theorem B1473335 : Blo 1472556 1473335 := bstep (se 1 (by rfl) ⟨1105001, by rfl⟩ : syracuseStep 1473335 = 2210003) B2210003
theorem B1473355 : Blo 1472556 1473355 := bstep (se 1 (by rfl) ⟨1105016, by rfl⟩ : syracuseStep 1473355 = 2210033) B2210033
theorem B1473367 : Blo 1472556 1473367 := bstep (se 1 (by rfl) ⟨1105025, by rfl⟩ : syracuseStep 1473367 = 2210051) B2210051
theorem B1473387 : Blo 1472556 1473387 := bstep (se 1 (by rfl) ⟨1105040, by rfl⟩ : syracuseStep 1473387 = 2210081) B2210081
theorem B1473399 : Blo 1472556 1473399 := bstep (se 1 (by rfl) ⟨1105049, by rfl⟩ : syracuseStep 1473399 = 2210099) B2210099
theorem B1473419 : Blo 1472556 1473419 := bstep (se 1 (by rfl) ⟨1105064, by rfl⟩ : syracuseStep 1473419 = 2210129) B2210129
theorem B2210699 : Blo 1472556 2210699 := bstep (se 1 (by rfl) ⟨1658024, by rfl⟩ : syracuseStep 2210699 = 3316049) B3316049
theorem B5970833 : Blo 1472556 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B1473431 : Blo 1472556 1473431 := bstep (se 1 (by rfl) ⟨1105073, by rfl⟩ : syracuseStep 1473431 = 2210147) B2210147
theorem B2210711 : Blo 1472556 2210711 := bstep (se 1 (by rfl) ⟨1658033, by rfl⟩ : syracuseStep 2210711 = 3316067) B3316067
theorem B1473451 : Blo 1472556 1473451 := bstep (se 1 (by rfl) ⟨1105088, by rfl⟩ : syracuseStep 1473451 = 2210177) B2210177
theorem B1473463 : Blo 1472556 1473463 := bstep (se 1 (by rfl) ⟨1105097, by rfl⟩ : syracuseStep 1473463 = 2210195) B2210195
theorem B1473483 : Blo 1472556 1473483 := bstep (se 1 (by rfl) ⟨1105112, by rfl⟩ : syracuseStep 1473483 = 2210225) B2210225
theorem B1473495 : Blo 1472556 1473495 := bstep (se 1 (by rfl) ⟨1105121, by rfl⟩ : syracuseStep 1473495 = 2210243) B2210243
theorem B21527513 : Blo 1472556 21527513 := bstep (se 2 (by rfl) ⟨8072817, by rfl⟩ : syracuseStep 21527513 = 16145635) B16145635
theorem B2210777 : Blo 1472556 2210777 := bstep (se 2 (by rfl) ⟨829041, by rfl⟩ : syracuseStep 2210777 = 1658083) B1658083
theorem B3316697 : Blo 1472556 3316697 := bstep (se 2 (by rfl) ⟨1243761, by rfl⟩ : syracuseStep 3316697 = 2487523) B2487523
theorem B1473515 : Blo 1472556 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B1473527 : Blo 1472556 1473527 := bstep (se 1 (by rfl) ⟨1105145, by rfl⟩ : syracuseStep 1473527 = 2210291) B2210291
theorem B1473547 : Blo 1472556 1473547 := bstep (se 1 (by rfl) ⟨1105160, by rfl⟩ : syracuseStep 1473547 = 2210321) B2210321
theorem B1473559 : Blo 1472556 1473559 := bstep (se 1 (by rfl) ⟨1105169, by rfl⟩ : syracuseStep 1473559 = 2210339) B2210339
theorem B2366489 : Blo 1472556 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B1473579 : Blo 1472556 1473579 := bstep (se 1 (by rfl) ⟨1105184, by rfl⟩ : syracuseStep 1473579 = 2210369) B2210369
theorem B3316787 : Blo 1472556 3316787 := bstep (se 1 (by rfl) ⟨2487590, by rfl⟩ : syracuseStep 3316787 = 4975181) B4975181
theorem B1473591 : Blo 1472556 1473591 := bstep (se 1 (by rfl) ⟨1105193, by rfl⟩ : syracuseStep 1473591 = 2210387) B2210387
theorem B4193345 : Blo 1472556 4193345 := bstep (se 2 (by rfl) ⟨1572504, by rfl⟩ : syracuseStep 4193345 = 3145009) B3145009
theorem B1473611 : Blo 1472556 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B2210891 : Blo 1472556 2210891 := bstep (se 1 (by rfl) ⟨1658168, by rfl⟩ : syracuseStep 2210891 = 3316337) B3316337
theorem B1473623 : Blo 1472556 1473623 := bstep (se 1 (by rfl) ⟨1105217, by rfl⟩ : syracuseStep 1473623 = 2210435) B2210435
theorem B2210903 : Blo 1472556 2210903 := bstep (se 1 (by rfl) ⟨1658177, by rfl⟩ : syracuseStep 2210903 = 3316355) B3316355
theorem B3316823 : Blo 1472556 3316823 := bstep (se 1 (by rfl) ⟨2487617, by rfl⟩ : syracuseStep 3316823 = 4975235) B4975235
theorem B1473643 : Blo 1472556 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1473655 : Blo 1472556 1473655 := bstep (se 1 (by rfl) ⟨1105241, by rfl⟩ : syracuseStep 1473655 = 2210483) B2210483
theorem B1473675 : Blo 1472556 1473675 := bstep (se 1 (by rfl) ⟨1105256, by rfl⟩ : syracuseStep 1473675 = 2210513) B2210513
theorem B4971671 : Blo 1472556 4971671 := bstep (se 1 (by rfl) ⟨3728753, by rfl⟩ : syracuseStep 4971671 = 7457507) B7457507
theorem B1473687 : Blo 1472556 1473687 := bstep (se 1 (by rfl) ⟨1105265, by rfl⟩ : syracuseStep 1473687 = 2210531) B2210531
theorem B2210969 : Blo 1472556 2210969 := bstep (se 2 (by rfl) ⟨829113, by rfl⟩ : syracuseStep 2210969 = 1658227) B1658227
theorem B1473707 : Blo 1472556 1473707 := bstep (se 1 (by rfl) ⟨1105280, by rfl⟩ : syracuseStep 1473707 = 2210561) B2210561
theorem B5594285 : Blo 1472556 5594285 := bstep (se 3 (by rfl) ⟨1048928, by rfl⟩ : syracuseStep 5594285 = 2097857) B2097857
theorem B1473719 : Blo 1472556 1473719 := bstep (se 1 (by rfl) ⟨1105289, by rfl⟩ : syracuseStep 1473719 = 2210579) B2210579
theorem B1473739 : Blo 1472556 1473739 := bstep (se 1 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 1473739 = 2210609) B2210609
theorem B14163149 : Blo 1472556 14163149 := bstep (se 3 (by rfl) ⟨2655590, by rfl⟩ : syracuseStep 14163149 = 5311181) B5311181
theorem B1473751 : Blo 1472556 1473751 := bstep (se 1 (by rfl) ⟨1105313, by rfl⟩ : syracuseStep 1473751 = 2210627) B2210627
theorem B1473771 : Blo 1472556 1473771 := bstep (se 1 (by rfl) ⟨1105328, by rfl⟩ : syracuseStep 1473771 = 2210657) B2210657
theorem B1473783 : Blo 1472556 1473783 := bstep (se 1 (by rfl) ⟨1105337, by rfl⟩ : syracuseStep 1473783 = 2210675) B2210675
theorem B1473803 : Blo 1472556 1473803 := bstep (se 1 (by rfl) ⟨1105352, by rfl⟩ : syracuseStep 1473803 = 2210705) B2210705
theorem B2211083 : Blo 1472556 2211083 := bstep (se 1 (by rfl) ⟨1658312, by rfl⟩ : syracuseStep 2211083 = 3316625) B3316625
theorem B3317003 : Blo 1472556 3317003 := bstep (se 1 (by rfl) ⟨2487752, by rfl⟩ : syracuseStep 3317003 = 4975505) B4975505
theorem B1473815 : Blo 1472556 1473815 := bstep (se 1 (by rfl) ⟨1105361, by rfl⟩ : syracuseStep 1473815 = 2210723) B2210723
theorem B2211095 : Blo 1472556 2211095 := bstep (se 1 (by rfl) ⟨1658321, by rfl⟩ : syracuseStep 2211095 = 3316643) B3316643
theorem B1473835 : Blo 1472556 1473835 := bstep (se 1 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 1473835 = 2210753) B2210753
theorem B1473847 : Blo 1472556 1473847 := bstep (se 1 (by rfl) ⟨1105385, by rfl⟩ : syracuseStep 1473847 = 2210771) B2210771
theorem B3317057 : Blo 1472556 3317057 := bstep (se 2 (by rfl) ⟨1243896, by rfl⟩ : syracuseStep 3317057 = 2487793) B2487793
theorem B1473867 : Blo 1472556 1473867 := bstep (se 1 (by rfl) ⟨1105400, by rfl⟩ : syracuseStep 1473867 = 2210801) B2210801
theorem B1473879 : Blo 1472556 1473879 := bstep (se 1 (by rfl) ⟨1105409, by rfl⟩ : syracuseStep 1473879 = 2210819) B2210819
theorem B2211161 : Blo 1472556 2211161 := bstep (se 2 (by rfl) ⟨829185, by rfl⟩ : syracuseStep 2211161 = 1658371) B1658371
theorem B1473899 : Blo 1472556 1473899 := bstep (se 1 (by rfl) ⟨1105424, by rfl⟩ : syracuseStep 1473899 = 2210849) B2210849
theorem B1473911 : Blo 1472556 1473911 := bstep (se 1 (by rfl) ⟨1105433, by rfl⟩ : syracuseStep 1473911 = 2210867) B2210867
theorem B1473931 : Blo 1472556 1473931 := bstep (se 1 (by rfl) ⟨1105448, by rfl⟩ : syracuseStep 1473931 = 2210897) B2210897
theorem B13434263 : Blo 1472556 13434263 := bstep (se 1 (by rfl) ⟨10075697, by rfl⟩ : syracuseStep 13434263 = 20151395) B20151395
theorem B3538327 : Blo 1472556 3538327 := bstep (se 1 (by rfl) ⟨2653745, by rfl⟩ : syracuseStep 3538327 = 5307491) B5307491
theorem B4193687 : Blo 1472556 4193687 := bstep (se 1 (by rfl) ⟨3145265, by rfl⟩ : syracuseStep 4193687 = 6290531) B6290531
theorem B1473943 : Blo 1472556 1473943 := bstep (se 1 (by rfl) ⟨1105457, by rfl⟩ : syracuseStep 1473943 = 2210915) B2210915
theorem B1473963 : Blo 1472556 1473963 := bstep (se 1 (by rfl) ⟨1105472, by rfl⟩ : syracuseStep 1473963 = 2210945) B2210945
theorem B1473975 : Blo 1472556 1473975 := bstep (se 1 (by rfl) ⟨1105481, by rfl⟩ : syracuseStep 1473975 = 2210963) B2210963
theorem B4718027 : Blo 1472556 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B6290891 : Blo 1472556 6290891 := bstep (se 1 (by rfl) ⟨4718168, by rfl⟩ : syracuseStep 6290891 = 9436337) B9436337
theorem B1473995 : Blo 1472556 1473995 := bstep (se 1 (by rfl) ⟨1105496, by rfl⟩ : syracuseStep 1473995 = 2210993) B2210993
theorem B2211275 : Blo 1472556 2211275 := bstep (se 1 (by rfl) ⟨1658456, by rfl⟩ : syracuseStep 2211275 = 3316913) B3316913
theorem B1474007 : Blo 1472556 1474007 := bstep (se 1 (by rfl) ⟨1105505, by rfl⟩ : syracuseStep 1474007 = 2211011) B2211011
theorem B2211287 : Blo 1472556 2211287 := bstep (se 1 (by rfl) ⟨1658465, by rfl⟩ : syracuseStep 2211287 = 3316931) B3316931
theorem B5111257 : Blo 1472556 5111257 := bstep (se 2 (by rfl) ⟨1916721, by rfl⟩ : syracuseStep 5111257 = 3833443) B3833443
theorem B1474027 : Blo 1472556 1474027 := bstep (se 1 (by rfl) ⟨1105520, by rfl⟩ : syracuseStep 1474027 = 2211041) B2211041
theorem B1474039 : Blo 1472556 1474039 := bstep (se 1 (by rfl) ⟨1105529, by rfl⟩ : syracuseStep 1474039 = 2211059) B2211059
theorem B1474059 : Blo 1472556 1474059 := bstep (se 1 (by rfl) ⟨1105544, by rfl⟩ : syracuseStep 1474059 = 2211089) B2211089
theorem B1474071 : Blo 1472556 1474071 := bstep (se 1 (by rfl) ⟨1105553, by rfl⟩ : syracuseStep 1474071 = 2211107) B2211107
theorem B6471191 : Blo 1472556 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B2211353 : Blo 1472556 2211353 := bstep (se 2 (by rfl) ⟨829257, by rfl⟩ : syracuseStep 2211353 = 1658515) B1658515
theorem B3317273 : Blo 1472556 3317273 := bstep (se 2 (by rfl) ⟨1243977, by rfl⟩ : syracuseStep 3317273 = 2487955) B2487955
theorem B1474091 : Blo 1472556 1474091 := bstep (se 1 (by rfl) ⟨1105568, by rfl⟩ : syracuseStep 1474091 = 2211137) B2211137
theorem B1474103 : Blo 1472556 1474103 := bstep (se 1 (by rfl) ⟨1105577, by rfl⟩ : syracuseStep 1474103 = 2211155) B2211155
theorem B1474123 : Blo 1472556 1474123 := bstep (se 1 (by rfl) ⟨1105592, by rfl⟩ : syracuseStep 1474123 = 2211185) B2211185
theorem B1474135 : Blo 1472556 1474135 := bstep (se 1 (by rfl) ⟨1105601, by rfl⟩ : syracuseStep 1474135 = 2211203) B2211203
theorem B1474155 : Blo 1472556 1474155 := bstep (se 1 (by rfl) ⟨1105616, by rfl⟩ : syracuseStep 1474155 = 2211233) B2211233
theorem B3317363 : Blo 1472556 3317363 := bstep (se 1 (by rfl) ⟨2488022, by rfl⟩ : syracuseStep 3317363 = 4976045) B4976045
theorem B1474167 : Blo 1472556 1474167 := bstep (se 1 (by rfl) ⟨1105625, by rfl⟩ : syracuseStep 1474167 = 2211251) B2211251
theorem B1474187 : Blo 1472556 1474187 := bstep (se 1 (by rfl) ⟨1105640, by rfl⟩ : syracuseStep 1474187 = 2211281) B2211281
theorem B2211467 : Blo 1472556 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B5308055 : Blo 1472556 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B9436823 : Blo 1472556 9436823 := bstep (se 1 (by rfl) ⟨7077617, by rfl⟩ : syracuseStep 9436823 = 14155235) B14155235
theorem B1474199 : Blo 1472556 1474199 := bstep (se 1 (by rfl) ⟨1105649, by rfl⟩ : syracuseStep 1474199 = 2211299) B2211299
theorem B2211479 : Blo 1472556 2211479 := bstep (se 1 (by rfl) ⟨1658609, by rfl⟩ : syracuseStep 2211479 = 3317219) B3317219
theorem B3317399 : Blo 1472556 3317399 := bstep (se 1 (by rfl) ⟨2488049, by rfl⟩ : syracuseStep 3317399 = 4976099) B4976099
theorem B1474219 : Blo 1472556 1474219 := bstep (se 1 (by rfl) ⟨1105664, by rfl⟩ : syracuseStep 1474219 = 2211329) B2211329
theorem B4972211 : Blo 1472556 4972211 := bstep (se 1 (by rfl) ⟨3729158, by rfl⟩ : syracuseStep 4972211 = 7458317) B7458317
theorem B1474231 : Blo 1472556 1474231 := bstep (se 1 (by rfl) ⟨1105673, by rfl⟩ : syracuseStep 1474231 = 2211347) B2211347
theorem B1474251 : Blo 1472556 1474251 := bstep (se 1 (by rfl) ⟨1105688, by rfl⟩ : syracuseStep 1474251 = 2211377) B2211377
theorem B1474263 : Blo 1472556 1474263 := bstep (se 1 (by rfl) ⟨1105697, by rfl⟩ : syracuseStep 1474263 = 2211395) B2211395
theorem B2211545 : Blo 1472556 2211545 := bstep (se 2 (by rfl) ⟨829329, by rfl⟩ : syracuseStep 2211545 = 1658659) B1658659
theorem B1474283 : Blo 1472556 1474283 := bstep (se 1 (by rfl) ⟨1105712, by rfl⟩ : syracuseStep 1474283 = 2211425) B2211425
theorem B1474295 : Blo 1472556 1474295 := bstep (se 1 (by rfl) ⟨1105721, by rfl⟩ : syracuseStep 1474295 = 2211443) B2211443
theorem B1474315 : Blo 1472556 1474315 := bstep (se 1 (by rfl) ⟨1105736, by rfl⟩ : syracuseStep 1474315 = 2211473) B2211473
theorem B5308183 : Blo 1472556 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B1474327 : Blo 1472556 1474327 := bstep (se 1 (by rfl) ⟨1105745, by rfl⟩ : syracuseStep 1474327 = 2211491) B2211491
theorem B1474347 : Blo 1472556 1474347 := bstep (se 1 (by rfl) ⟨1105760, by rfl⟩ : syracuseStep 1474347 = 2211521) B2211521
theorem B12582701 : Blo 1472556 12582701 := bstep (se 3 (by rfl) ⟨2359256, by rfl⟩ : syracuseStep 12582701 = 4718513) B4718513
theorem B1474359 : Blo 1472556 1474359 := bstep (se 1 (by rfl) ⟨1105769, by rfl⟩ : syracuseStep 1474359 = 2211539) B2211539
theorem B1474379 : Blo 1472556 1474379 := bstep (se 1 (by rfl) ⟨1105784, by rfl⟩ : syracuseStep 1474379 = 2211569) B2211569
theorem B2211659 : Blo 1472556 2211659 := bstep (se 1 (by rfl) ⟨1658744, by rfl⟩ : syracuseStep 2211659 = 3317489) B3317489
theorem B3317579 : Blo 1472556 3317579 := bstep (se 1 (by rfl) ⟨2488184, by rfl⟩ : syracuseStep 3317579 = 4976369) B4976369
theorem B1474391 : Blo 1472556 1474391 := bstep (se 1 (by rfl) ⟨1105793, by rfl⟩ : syracuseStep 1474391 = 2211587) B2211587
theorem B2211671 : Blo 1472556 2211671 := bstep (se 1 (by rfl) ⟨1658753, by rfl⟩ : syracuseStep 2211671 = 3317507) B3317507
theorem B1474411 : Blo 1472556 1474411 := bstep (se 1 (by rfl) ⟨1105808, by rfl⟩ : syracuseStep 1474411 = 2211617) B2211617
theorem B1474423 : Blo 1472556 1474423 := bstep (se 1 (by rfl) ⟨1105817, by rfl⟩ : syracuseStep 1474423 = 2211635) B2211635
theorem B3317633 : Blo 1472556 3317633 := bstep (se 2 (by rfl) ⟨1244112, by rfl⟩ : syracuseStep 3317633 = 2488225) B2488225
theorem B1474443 : Blo 1472556 1474443 := bstep (se 1 (by rfl) ⟨1105832, by rfl⟩ : syracuseStep 1474443 = 2211665) B2211665
theorem B1474455 : Blo 1472556 1474455 := bstep (se 1 (by rfl) ⟨1105841, by rfl⟩ : syracuseStep 1474455 = 2211683) B2211683
theorem B2211737 : Blo 1472556 2211737 := bstep (se 2 (by rfl) ⟨829401, by rfl⟩ : syracuseStep 2211737 = 1658803) B1658803
theorem B1474475 : Blo 1472556 1474475 := bstep (se 1 (by rfl) ⟨1105856, by rfl⟩ : syracuseStep 1474475 = 2211713) B2211713
theorem B1474487 : Blo 1472556 1474487 := bstep (se 1 (by rfl) ⟨1105865, by rfl⟩ : syracuseStep 1474487 = 2211731) B2211731
theorem B4972481 : Blo 1472556 4972481 := bstep (se 2 (by rfl) ⟨1864680, by rfl⟩ : syracuseStep 4972481 = 3729361) B3729361
theorem B1474507 : Blo 1472556 1474507 := bstep (se 1 (by rfl) ⟨1105880, by rfl⟩ : syracuseStep 1474507 = 2211761) B2211761
theorem B1474519 : Blo 1472556 1474519 := bstep (se 1 (by rfl) ⟨1105889, by rfl⟩ : syracuseStep 1474519 = 2211779) B2211779
theorem B1474539 : Blo 1472556 1474539 := bstep (se 1 (by rfl) ⟨1105904, by rfl⟩ : syracuseStep 1474539 = 2211809) B2211809
theorem B3145787 : Blo 1472556 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B4194575 : Blo 1472556 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B5595425 : Blo 1472556 5595425 := bstep (se 2 (by rfl) ⟨2098284, by rfl⟩ : syracuseStep 5595425 = 4196569) B4196569
theorem B4972859 : Blo 1472556 4972859 := bstep (se 1 (by rfl) ⟨3729644, by rfl⟩ : syracuseStep 4972859 = 7459289) B7459289
theorem B3727883 : Blo 1472556 3727883 := bstep (se 1 (by rfl) ⟨2795912, by rfl⟩ : syracuseStep 3727883 = 5591825) B5591825
theorem B49136149 : Blo 1472556 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B7078423 : Blo 1472556 7078423 := bstep (se 1 (by rfl) ⟨5308817, by rfl⟩ : syracuseStep 7078423 = 10617635) B10617635
theorem B53756459 : Blo 1472556 53756459 := bstep (se 1 (by rfl) ⟨40317344, by rfl⟩ : syracuseStep 53756459 = 80634689) B80634689
theorem B4481651 : Blo 1472556 4481651 := bstep (se 1 (by rfl) ⟨3361238, by rfl⟩ : syracuseStep 4481651 = 6722477) B6722477
theorem B3146359 : Blo 1472556 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B6292205 : Blo 1472556 6292205 := bstep (se 3 (by rfl) ⟨1179788, by rfl⟩ : syracuseStep 6292205 = 2359577) B2359577
theorem B5456621 : Blo 1472556 5456621 := bstep (se 3 (by rfl) ⟨1023116, by rfl⟩ : syracuseStep 5456621 = 2046233) B2046233
theorem B4973345 : Blo 1472556 4973345 := bstep (se 2 (by rfl) ⟨1865004, by rfl⟩ : syracuseStep 4973345 = 3730009) B3730009
theorem B3146539 : Blo 1472556 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B3146615 : Blo 1472556 3146615 := bstep (se 1 (by rfl) ⟨2359961, by rfl⟩ : syracuseStep 3146615 = 4719923) B4719923
theorem B7463825 : Blo 1472556 7463825 := bstep (se 2 (by rfl) ⟨2798934, by rfl⟩ : syracuseStep 7463825 = 5597869) B5597869
theorem B8397715 : Blo 1472556 8397715 := bstep (se 1 (by rfl) ⟨6298286, by rfl⟩ : syracuseStep 8397715 = 12596573) B12596573
theorem B71681111 : Blo 1472556 71681111 := bstep (se 1 (by rfl) ⟨53760833, by rfl⟩ : syracuseStep 71681111 = 107521667) B107521667
theorem B3728531 : Blo 1472556 3728531 := bstep (se 1 (by rfl) ⟨2796398, by rfl⟩ : syracuseStep 3728531 = 5592797) B5592797
theorem B3540115 : Blo 1472556 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B5596397 : Blo 1472556 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B8389925 : Blo 1472556 8389925 := bstep (se 4 (by rfl) ⟨786555, by rfl⟩ : syracuseStep 8389925 = 1573111) B1573111
theorem B4973939 : Blo 1472556 4973939 := bstep (se 1 (by rfl) ⟨3730454, by rfl⟩ : syracuseStep 4973939 = 7460909) B7460909
theorem B6292889 : Blo 1472556 6292889 := bstep (se 2 (by rfl) ⟨2359833, by rfl⟩ : syracuseStep 6292889 = 4719667) B4719667
theorem B4720025 : Blo 1472556 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B3728825 : Blo 1472556 3728825 := bstep (se 2 (by rfl) ⟨1398309, by rfl⟩ : syracuseStep 3728825 = 2796619) B2796619
theorem B5596715 : Blo 1472556 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B4916855 : Blo 1472556 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B3983033 : Blo 1472556 3983033 := bstep (se 2 (by rfl) ⟨1493637, by rfl⟩ : syracuseStep 3983033 = 2987275) B2987275
theorem B15124259 : Blo 1472556 15124259 := bstep (se 1 (by rfl) ⟨11343194, by rfl⟩ : syracuseStep 15124259 = 22686389) B22686389
theorem B4196215 : Blo 1472556 4196215 := bstep (se 1 (by rfl) ⟨3147161, by rfl⟩ : syracuseStep 4196215 = 6294323) B6294323
theorem B7456697 : Blo 1472556 7456697 := bstep (se 2 (by rfl) ⟨2796261, by rfl⟩ : syracuseStep 7456697 = 5592523) B5592523
theorem B2795563 : Blo 1472556 2795563 := bstep (se 1 (by rfl) ⟨2096672, by rfl⟩ : syracuseStep 2795563 = 4193345) B4193345
theorem B8390699 : Blo 1472556 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B4786219 : Blo 1472556 4786219 := bstep (se 1 (by rfl) ⟨3589664, by rfl⟩ : syracuseStep 4786219 = 7179329) B7179329
theorem B3729523 : Blo 1472556 3729523 := bstep (se 1 (by rfl) ⟨2797142, by rfl⟩ : syracuseStep 3729523 = 5594285) B5594285
theorem B4786295 : Blo 1472556 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B11954309 : Blo 1472556 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B1656967 : Blo 1472556 1656967 := bstep (se 1 (by rfl) ⟨1242725, by rfl⟩ : syracuseStep 1656967 = 2485451) B2485451
theorem B2361545 : Blo 1472556 2361545 := bstep (se 2 (by rfl) ⟨885579, by rfl⟩ : syracuseStep 2361545 = 1771159) B1771159
theorem B3729665 : Blo 1472556 3729665 := bstep (se 2 (by rfl) ⟨1398624, by rfl⟩ : syracuseStep 3729665 = 2797249) B2797249
theorem B3541249 : Blo 1472556 3541249 := bstep (se 2 (by rfl) ⟨1327968, by rfl⟩ : syracuseStep 3541249 = 2655937) B2655937
theorem B8956175 : Blo 1472556 8956175 := bstep (se 1 (by rfl) ⟨6717131, by rfl⟩ : syracuseStep 8956175 = 13434263) B13434263
theorem B2795791 : Blo 1472556 2795791 := bstep (se 1 (by rfl) ⟨2096843, by rfl⟩ : syracuseStep 2795791 = 4193687) B4193687
theorem B1657147 : Blo 1472556 1657147 := bstep (se 1 (by rfl) ⟨1242860, by rfl⟩ : syracuseStep 1657147 = 2485721) B2485721
theorem B2656571 : Blo 1472556 2656571 := bstep (se 1 (by rfl) ⟨1992428, by rfl⟩ : syracuseStep 2656571 = 3984857) B3984857
theorem B2099515 : Blo 1472556 2099515 := bstep (se 1 (by rfl) ⟨1574636, by rfl⟩ : syracuseStep 2099515 = 3149273) B3149273
theorem B16157249 : Blo 1472556 16157249 := bstep (se 2 (by rfl) ⟨6058968, by rfl⟩ : syracuseStep 16157249 = 12117937) B12117937
theorem B17926757 : Blo 1472556 17926757 := bstep (se 4 (by rfl) ⟨1680633, by rfl⟩ : syracuseStep 17926757 = 3361267) B3361267
theorem B3730121 : Blo 1472556 3730121 := bstep (se 2 (by rfl) ⟨1398795, by rfl⟩ : syracuseStep 3730121 = 2797591) B2797591
theorem B8743681 : Blo 1472556 8743681 := bstep (se 2 (by rfl) ⟨3278880, by rfl⟩ : syracuseStep 8743681 = 6557761) B6557761
theorem B1657615 : Blo 1472556 1657615 := bstep (se 1 (by rfl) ⟨1243211, by rfl⟩ : syracuseStep 1657615 = 2486423) B2486423
theorem B16780121 : Blo 1472556 16780121 := bstep (se 2 (by rfl) ⟨6292545, by rfl⟩ : syracuseStep 16780121 = 12585091) B12585091
theorem B2485127 : Blo 1472556 2485127 := bstep (se 1 (by rfl) ⟨1863845, by rfl⟩ : syracuseStep 2485127 = 3727691) B3727691
theorem B3541961 : Blo 1472556 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B71666693 : Blo 1472556 71666693 := bstep (se 4 (by rfl) ⟨6718752, by rfl⟩ : syracuseStep 71666693 = 13437505) B13437505
theorem B3730475 : Blo 1472556 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B4197491 : Blo 1472556 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B28691587 : Blo 1472556 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B7457993 : Blo 1472556 7457993 := bstep (se 2 (by rfl) ⟨2796747, by rfl⟩ : syracuseStep 7457993 = 5593495) B5593495
theorem B5311745 : Blo 1472556 5311745 := bstep (se 2 (by rfl) ⟨1991904, by rfl⟩ : syracuseStep 5311745 = 3983809) B3983809
theorem B1658119 : Blo 1472556 1658119 := bstep (se 1 (by rfl) ⟨1243589, by rfl⟩ : syracuseStep 1658119 = 2487179) B2487179
theorem B3542287 : Blo 1472556 3542287 := bstep (se 1 (by rfl) ⟨2656715, by rfl⟩ : syracuseStep 3542287 = 5313431) B5313431
theorem B4197719 : Blo 1472556 4197719 := bstep (se 1 (by rfl) ⟨3148289, by rfl⟩ : syracuseStep 4197719 = 6296579) B6296579
theorem B5672339 : Blo 1472556 5672339 := bstep (se 1 (by rfl) ⟨4254254, by rfl⟩ : syracuseStep 5672339 = 8508509) B8508509
theorem B1658299 : Blo 1472556 1658299 := bstep (se 1 (by rfl) ⟨1243724, by rfl⟩ : syracuseStep 1658299 = 2487449) B2487449
theorem B8392157 : Blo 1472556 8392157 := bstep (se 3 (by rfl) ⟨1573529, by rfl⟩ : syracuseStep 8392157 = 3147059) B3147059
theorem B2485775 : Blo 1472556 2485775 := bstep (se 1 (by rfl) ⟨1864331, by rfl⟩ : syracuseStep 2485775 = 3728663) B3728663
theorem B5041693 : Blo 1472556 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B2797355 : Blo 1472556 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B57438001 : Blo 1472556 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B14159731 : Blo 1472556 14159731 := bstep (se 1 (by rfl) ⟨10619798, by rfl⟩ : syracuseStep 14159731 = 21239597) B21239597
theorem B3542903 : Blo 1472556 3542903 := bstep (se 1 (by rfl) ⟨2657177, by rfl⟩ : syracuseStep 3542903 = 5314355) B5314355
theorem B1658767 : Blo 1472556 1658767 := bstep (se 1 (by rfl) ⟨1244075, by rfl⟩ : syracuseStep 1658767 = 2488151) B2488151
theorem B4976531 : Blo 1472556 4976531 := bstep (se 1 (by rfl) ⟨3732398, by rfl⟩ : syracuseStep 4976531 = 7464797) B7464797
theorem B3731467 : Blo 1472556 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B2486315 : Blo 1472556 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B1863739 : Blo 1472556 1863739 := bstep (se 1 (by rfl) ⟨1397804, by rfl⟩ : syracuseStep 1863739 = 2795609) B2795609
theorem B17256509 : Blo 1472556 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B4542551 : Blo 1472556 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3313799 : Blo 1472556 3313799 := bstep (se 1 (by rfl) ⟨2485349, by rfl⟩ : syracuseStep 3313799 = 4970699) B4970699
theorem B4255891 : Blo 1472556 4255891 := bstep (se 1 (by rfl) ⟨3191918, by rfl⟩ : syracuseStep 4255891 = 6383837) B6383837
theorem B3731609 : Blo 1472556 3731609 := bstep (se 2 (by rfl) ⟨1399353, by rfl⟩ : syracuseStep 3731609 = 2798707) B2798707
theorem B7966991 : Blo 1472556 7966991 := bstep (se 1 (by rfl) ⟨5975243, by rfl⟩ : syracuseStep 7966991 = 11950487) B11950487
theorem B3313979 : Blo 1472556 3313979 := bstep (se 1 (by rfl) ⟨2485484, by rfl⟩ : syracuseStep 3313979 = 4970969) B4970969
theorem B3731771 : Blo 1472556 3731771 := bstep (se 1 (by rfl) ⟨2798828, by rfl⟩ : syracuseStep 3731771 = 5597657) B5597657
theorem B10760633 : Blo 1472556 10760633 := bstep (se 2 (by rfl) ⟨4035237, by rfl⟩ : syracuseStep 10760633 = 8070475) B8070475
theorem B3314105 : Blo 1472556 3314105 := bstep (se 2 (by rfl) ⟨1242789, by rfl⟩ : syracuseStep 3314105 = 2485579) B2485579
theorem B2486713 : Blo 1472556 2486713 := bstep (se 2 (by rfl) ⟨932517, by rfl⟩ : syracuseStep 2486713 = 1865035) B1865035
theorem B1864235 : Blo 1472556 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B3732115 : Blo 1472556 3732115 := bstep (se 1 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 3732115 = 5598173) B5598173
theorem B1577659 : Blo 1472556 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B3314447 : Blo 1472556 3314447 := bstep (se 1 (by rfl) ⟨2485835, by rfl⟩ : syracuseStep 3314447 = 4971671) B4971671
theorem B3314465 : Blo 1472556 3314465 := bstep (se 2 (by rfl) ⟨1242924, by rfl⟩ : syracuseStep 3314465 = 2485849) B2485849
theorem B3732257 : Blo 1472556 3732257 := bstep (se 2 (by rfl) ⟨1399596, by rfl⟩ : syracuseStep 3732257 = 2799193) B2799193
theorem B14160689 : Blo 1472556 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B12587825 : Blo 1472556 12587825 := bstep (se 2 (by rfl) ⟨4720434, by rfl⟩ : syracuseStep 12587825 = 9440869) B9440869
theorem B9442099 : Blo 1472556 9442099 := bstep (se 1 (by rfl) ⟨7081574, by rfl⟩ : syracuseStep 9442099 = 14163149) B14163149
theorem B1864711 : Blo 1472556 1864711 := bstep (se 1 (by rfl) ⟨1398533, by rfl⟩ : syracuseStep 1864711 = 2797067) B2797067
theorem B2208887 : Blo 1472556 2208887 := bstep (se 1 (by rfl) ⟨1656665, by rfl⟩ : syracuseStep 2208887 = 3313331) B3313331
theorem B3314807 : Blo 1472556 3314807 := bstep (se 1 (by rfl) ⟨2486105, by rfl⟩ : syracuseStep 3314807 = 4972211) B4972211
theorem B2487415 : Blo 1472556 2487415 := bstep (se 1 (by rfl) ⟨1865561, by rfl⟩ : syracuseStep 2487415 = 3731123) B3731123
theorem B2208911 : Blo 1472556 2208911 := bstep (se 1 (by rfl) ⟨1656683, by rfl⟩ : syracuseStep 2208911 = 3313367) B3313367
theorem B2208953 : Blo 1472556 2208953 := bstep (se 2 (by rfl) ⟨828357, by rfl⟩ : syracuseStep 2208953 = 1656715) B1656715
theorem B2209031 : Blo 1472556 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B2209067 : Blo 1472556 2209067 := bstep (se 1 (by rfl) ⟨1656800, by rfl⟩ : syracuseStep 2209067 = 3313601) B3313601
theorem B3314987 : Blo 1472556 3314987 := bstep (se 1 (by rfl) ⟨2486240, by rfl⟩ : syracuseStep 3314987 = 4972481) B4972481
theorem B2487611 : Blo 1472556 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B2209097 : Blo 1472556 2209097 := bstep (se 2 (by rfl) ⟨828411, by rfl⟩ : syracuseStep 2209097 = 1656823) B1656823
theorem B20428163 : Blo 1472556 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B2209211 : Blo 1472556 2209211 := bstep (se 1 (by rfl) ⟨1656908, by rfl⟩ : syracuseStep 2209211 = 3313817) B3313817
theorem B2799049 : Blo 1472556 2799049 := bstep (se 2 (by rfl) ⟨1049643, by rfl⟩ : syracuseStep 2799049 = 2099287) B2099287
theorem B6297041 : Blo 1472556 6297041 := bstep (se 2 (by rfl) ⟨2361390, by rfl⟩ : syracuseStep 6297041 = 4722781) B4722781
theorem B2209271 : Blo 1472556 2209271 := bstep (se 1 (by rfl) ⟨1656953, by rfl⟩ : syracuseStep 2209271 = 3313907) B3313907
theorem B1865207 : Blo 1472556 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B2209295 : Blo 1472556 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B2209337 : Blo 1472556 2209337 := bstep (se 2 (by rfl) ⟨828501, by rfl⟩ : syracuseStep 2209337 = 1657003) B1657003
theorem B11195981 : Blo 1472556 11195981 := bstep (se 3 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 11195981 = 4198493) B4198493
theorem B2209415 : Blo 1472556 2209415 := bstep (se 1 (by rfl) ⟨1657061, by rfl⟩ : syracuseStep 2209415 = 3314123) B3314123
theorem B1865359 : Blo 1472556 1865359 := bstep (se 1 (by rfl) ⟨1399019, by rfl⟩ : syracuseStep 1865359 = 2798039) B2798039
theorem B3315347 : Blo 1472556 3315347 := bstep (se 1 (by rfl) ⟨2486510, by rfl⟩ : syracuseStep 3315347 = 4973021) B4973021
theorem B2209451 : Blo 1472556 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B17929907 : Blo 1472556 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B2209481 : Blo 1472556 2209481 := bstep (se 2 (by rfl) ⟨828555, by rfl⟩ : syracuseStep 2209481 = 1657111) B1657111
theorem B3315401 : Blo 1472556 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B2488009 : Blo 1472556 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B16152335 : Blo 1472556 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B2209595 : Blo 1472556 2209595 := bstep (se 1 (by rfl) ⟨1657196, by rfl⟩ : syracuseStep 2209595 = 3314393) B3314393
theorem B1865531 : Blo 1472556 1865531 := bstep (se 1 (by rfl) ⟨1399148, by rfl⟩ : syracuseStep 1865531 = 2798297) B2798297
theorem B60479297 : Blo 1472556 60479297 := bstep (se 2 (by rfl) ⟨22679736, by rfl⟩ : syracuseStep 60479297 = 45359473) B45359473
theorem B8075123 : Blo 1472556 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B2209655 : Blo 1472556 2209655 := bstep (se 1 (by rfl) ⟨1657241, by rfl⟩ : syracuseStep 2209655 = 3314483) B3314483
theorem B4970375 : Blo 1472556 4970375 := bstep (se 1 (by rfl) ⟨3727781, by rfl⟩ : syracuseStep 4970375 = 7455563) B7455563
theorem B5044103 : Blo 1472556 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B2209679 : Blo 1472556 2209679 := bstep (se 1 (by rfl) ⟨1657259, by rfl⟩ : syracuseStep 2209679 = 3314519) B3314519
theorem B7272337 : Blo 1472556 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B2209721 : Blo 1472556 2209721 := bstep (se 2 (by rfl) ⟨828645, by rfl⟩ : syracuseStep 2209721 = 1657291) B1657291
theorem B2209799 : Blo 1472556 2209799 := bstep (se 1 (by rfl) ⟨1657349, by rfl⟩ : syracuseStep 2209799 = 3314699) B3314699
theorem B2209835 : Blo 1472556 2209835 := bstep (se 1 (by rfl) ⟨1657376, by rfl⟩ : syracuseStep 2209835 = 3314753) B3314753
theorem B1472571 : Blo 1472556 1472571 := bstep (se 1 (by rfl) ⟨1104428, by rfl⟩ : syracuseStep 1472571 = 2208857) B2208857
theorem B2209865 : Blo 1472556 2209865 := bstep (se 2 (by rfl) ⟨828699, by rfl⟩ : syracuseStep 2209865 = 1657399) B1657399
theorem B1472647 : Blo 1472556 1472647 := bstep (se 1 (by rfl) ⟨1104485, by rfl⟩ : syracuseStep 1472647 = 2208971) B2208971
theorem B1472655 : Blo 1472556 1472655 := bstep (se 1 (by rfl) ⟨1104491, by rfl⟩ : syracuseStep 1472655 = 2208983) B2208983
theorem B1472699 : Blo 1472556 1472699 := bstep (se 1 (by rfl) ⟨1104524, by rfl⟩ : syracuseStep 1472699 = 2209049) B2209049
theorem B2209979 : Blo 1472556 2209979 := bstep (se 1 (by rfl) ⟨1657484, by rfl⟩ : syracuseStep 2209979 = 3314969) B3314969
theorem B2210039 : Blo 1472556 2210039 := bstep (se 1 (by rfl) ⟨1657529, by rfl⟩ : syracuseStep 2210039 = 3315059) B3315059
theorem B4970753 : Blo 1472556 4970753 := bstep (se 2 (by rfl) ⟨1864032, by rfl⟩ : syracuseStep 4970753 = 3728065) B3728065
theorem B1472775 : Blo 1472556 1472775 := bstep (se 1 (by rfl) ⟨1104581, by rfl⟩ : syracuseStep 1472775 = 2209163) B2209163
theorem B1472783 : Blo 1472556 1472783 := bstep (se 1 (by rfl) ⟨1104587, by rfl⟩ : syracuseStep 1472783 = 2209175) B2209175
theorem B2210063 : Blo 1472556 2210063 := bstep (se 1 (by rfl) ⟨1657547, by rfl⟩ : syracuseStep 2210063 = 3315095) B3315095
theorem B26876177 : Blo 1472556 26876177 := bstep (se 2 (by rfl) ⟨10078566, by rfl⟩ : syracuseStep 26876177 = 20157133) B20157133
theorem B2210105 : Blo 1472556 2210105 := bstep (se 2 (by rfl) ⟨828789, by rfl⟩ : syracuseStep 2210105 = 1657579) B1657579
theorem B1472827 : Blo 1472556 1472827 := bstep (se 1 (by rfl) ⟨1104620, by rfl⟩ : syracuseStep 1472827 = 2209241) B2209241
theorem B1472903 : Blo 1472556 1472903 := bstep (se 1 (by rfl) ⟨1104677, by rfl⟩ : syracuseStep 1472903 = 2209355) B2209355
theorem B2210183 : Blo 1472556 2210183 := bstep (se 1 (by rfl) ⟨1657637, by rfl⟩ : syracuseStep 2210183 = 3315275) B3315275
theorem B3316103 : Blo 1472556 3316103 := bstep (se 1 (by rfl) ⟨2487077, by rfl⟩ : syracuseStep 3316103 = 4974155) B4974155
theorem B1472911 : Blo 1472556 1472911 := bstep (se 1 (by rfl) ⟨1104683, by rfl⟩ : syracuseStep 1472911 = 2209367) B2209367
theorem B25172369 : Blo 1472556 25172369 := bstep (se 2 (by rfl) ⟨9439638, by rfl⟩ : syracuseStep 25172369 = 18879277) B18879277
theorem B2210219 : Blo 1472556 2210219 := bstep (se 1 (by rfl) ⟨1657664, by rfl⟩ : syracuseStep 2210219 = 3315329) B3315329
theorem B1472955 : Blo 1472556 1472955 := bstep (se 1 (by rfl) ⟨1104716, by rfl⟩ : syracuseStep 1472955 = 2209433) B2209433
theorem B2210249 : Blo 1472556 2210249 := bstep (se 2 (by rfl) ⟨828843, by rfl⟩ : syracuseStep 2210249 = 1657687) B1657687
theorem B58169821 : Blo 1472556 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B1473031 : Blo 1472556 1473031 := bstep (se 1 (by rfl) ⟨1104773, by rfl⟩ : syracuseStep 1473031 = 2209547) B2209547
theorem B1473039 : Blo 1472556 1473039 := bstep (se 1 (by rfl) ⟨1104779, by rfl⟩ : syracuseStep 1473039 = 2209559) B2209559
theorem B3029519 : Blo 1472556 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B1473083 : Blo 1472556 1473083 := bstep (se 1 (by rfl) ⟨1104812, by rfl⟩ : syracuseStep 1473083 = 2209625) B2209625
theorem B2210363 : Blo 1472556 2210363 := bstep (se 1 (by rfl) ⟨1657772, by rfl⟩ : syracuseStep 2210363 = 3315545) B3315545
theorem B3316283 : Blo 1472556 3316283 := bstep (se 1 (by rfl) ⟨2487212, by rfl⟩ : syracuseStep 3316283 = 4974425) B4974425
theorem B8395325 : Blo 1472556 8395325 := bstep (se 3 (by rfl) ⟨1574123, by rfl⟩ : syracuseStep 8395325 = 3148247) B3148247
theorem B16775747 : Blo 1472556 16775747 := bstep (se 1 (by rfl) ⟨12581810, by rfl⟩ : syracuseStep 16775747 = 25163621) B25163621
theorem B2210423 : Blo 1472556 2210423 := bstep (se 1 (by rfl) ⟨1657817, by rfl⟩ : syracuseStep 2210423 = 3315635) B3315635
theorem B1473159 : Blo 1472556 1473159 := bstep (se 1 (by rfl) ⟨1104869, by rfl⟩ : syracuseStep 1473159 = 2209739) B2209739
theorem B1473167 : Blo 1472556 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B2210447 : Blo 1472556 2210447 := bstep (se 1 (by rfl) ⟨1657835, by rfl⟩ : syracuseStep 2210447 = 3315671) B3315671
theorem B2210489 : Blo 1472556 2210489 := bstep (se 2 (by rfl) ⟨828933, by rfl⟩ : syracuseStep 2210489 = 1657867) B1657867
theorem B3316409 : Blo 1472556 3316409 := bstep (se 2 (by rfl) ⟨1243653, by rfl⟩ : syracuseStep 3316409 = 2487307) B2487307
theorem B1473211 : Blo 1472556 1473211 := bstep (se 1 (by rfl) ⟨1104908, by rfl⟩ : syracuseStep 1473211 = 2209817) B2209817
theorem B1473287 : Blo 1472556 1473287 := bstep (se 1 (by rfl) ⟨1104965, by rfl⟩ : syracuseStep 1473287 = 2209931) B2209931
theorem B2210567 : Blo 1472556 2210567 := bstep (se 1 (by rfl) ⟨1657925, by rfl⟩ : syracuseStep 2210567 = 3315851) B3315851
theorem B1473295 : Blo 1472556 1473295 := bstep (se 1 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 1473295 = 2209943) B2209943
theorem B2210603 : Blo 1472556 2210603 := bstep (se 1 (by rfl) ⟨1657952, by rfl⟩ : syracuseStep 2210603 = 3315905) B3315905
theorem B1473339 : Blo 1472556 1473339 := bstep (se 1 (by rfl) ⟨1105004, by rfl⟩ : syracuseStep 1473339 = 2210009) B2210009
theorem B2210633 : Blo 1472556 2210633 := bstep (se 2 (by rfl) ⟨828987, by rfl⟩ : syracuseStep 2210633 = 1657975) B1657975
theorem B6290291 : Blo 1472556 6290291 := bstep (se 1 (by rfl) ⟨4717718, by rfl⟩ : syracuseStep 6290291 = 9435437) B9435437
theorem B1473415 : Blo 1472556 1473415 := bstep (se 1 (by rfl) ⟨1105061, by rfl⟩ : syracuseStep 1473415 = 2210123) B2210123
theorem B1473423 : Blo 1472556 1473423 := bstep (se 1 (by rfl) ⟨1105067, by rfl⟩ : syracuseStep 1473423 = 2210135) B2210135
theorem B1473467 : Blo 1472556 1473467 := bstep (se 1 (by rfl) ⟨1105100, by rfl⟩ : syracuseStep 1473467 = 2210201) B2210201
theorem B2210747 : Blo 1472556 2210747 := bstep (se 1 (by rfl) ⟨1658060, by rfl⟩ : syracuseStep 2210747 = 3316121) B3316121
theorem B2210807 : Blo 1472556 2210807 := bstep (se 1 (by rfl) ⟨1658105, by rfl⟩ : syracuseStep 2210807 = 3316211) B3316211
theorem B1473543 : Blo 1472556 1473543 := bstep (se 1 (by rfl) ⟨1105157, by rfl⟩ : syracuseStep 1473543 = 2210315) B2210315
theorem B1473551 : Blo 1472556 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B2210831 : Blo 1472556 2210831 := bstep (se 1 (by rfl) ⟨1658123, by rfl⟩ : syracuseStep 2210831 = 3316247) B3316247
theorem B3316751 : Blo 1472556 3316751 := bstep (se 1 (by rfl) ⟨2487563, by rfl⟩ : syracuseStep 3316751 = 4975127) B4975127
theorem B3316769 : Blo 1472556 3316769 := bstep (se 2 (by rfl) ⟨1243788, by rfl⟩ : syracuseStep 3316769 = 2487577) B2487577
theorem B4971563 : Blo 1472556 4971563 := bstep (se 1 (by rfl) ⟨3728672, by rfl⟩ : syracuseStep 4971563 = 7457345) B7457345
theorem B2210873 : Blo 1472556 2210873 := bstep (se 2 (by rfl) ⟨829077, by rfl⟩ : syracuseStep 2210873 = 1658155) B1658155
theorem B1473595 : Blo 1472556 1473595 := bstep (se 1 (by rfl) ⟨1105196, by rfl⟩ : syracuseStep 1473595 = 2210393) B2210393
theorem B1473671 : Blo 1472556 1473671 := bstep (se 1 (by rfl) ⟨1105253, by rfl⟩ : syracuseStep 1473671 = 2210507) B2210507
theorem B2210951 : Blo 1472556 2210951 := bstep (se 1 (by rfl) ⟨1658213, by rfl⟩ : syracuseStep 2210951 = 3316427) B3316427
theorem B1473679 : Blo 1472556 1473679 := bstep (se 1 (by rfl) ⟨1105259, by rfl⟩ : syracuseStep 1473679 = 2210519) B2210519
theorem B2210987 : Blo 1472556 2210987 := bstep (se 1 (by rfl) ⟨1658240, by rfl⟩ : syracuseStep 2210987 = 3316481) B3316481
theorem B1473723 : Blo 1472556 1473723 := bstep (se 1 (by rfl) ⟨1105292, by rfl⟩ : syracuseStep 1473723 = 2210585) B2210585
theorem B4717769 : Blo 1472556 4717769 := bstep (se 2 (by rfl) ⟨1769163, by rfl⟩ : syracuseStep 4717769 = 3538327) B3538327
theorem B2211017 : Blo 1472556 2211017 := bstep (se 2 (by rfl) ⟨829131, by rfl⟩ : syracuseStep 2211017 = 1658263) B1658263
theorem B1473799 : Blo 1472556 1473799 := bstep (se 1 (by rfl) ⟨1105349, by rfl⟩ : syracuseStep 1473799 = 2210699) B2210699
theorem B3980555 : Blo 1472556 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B1473807 : Blo 1472556 1473807 := bstep (se 1 (by rfl) ⟨1105355, by rfl⟩ : syracuseStep 1473807 = 2210711) B2210711
theorem B6815009 : Blo 1472556 6815009 := bstep (se 2 (by rfl) ⟨2555628, by rfl⟩ : syracuseStep 6815009 = 5111257) B5111257
theorem B14351675 : Blo 1472556 14351675 := bstep (se 1 (by rfl) ⟨10763756, by rfl⟩ : syracuseStep 14351675 = 21527513) B21527513
theorem B1473851 : Blo 1472556 1473851 := bstep (se 1 (by rfl) ⟨1105388, by rfl⟩ : syracuseStep 1473851 = 2210777) B2210777
theorem B2211131 : Blo 1472556 2211131 := bstep (se 1 (by rfl) ⟨1658348, by rfl⟩ : syracuseStep 2211131 = 3316697) B3316697
theorem B2211191 : Blo 1472556 2211191 := bstep (se 1 (by rfl) ⟨1658393, by rfl⟩ : syracuseStep 2211191 = 3316787) B3316787
theorem B3317111 : Blo 1472556 3317111 := bstep (se 1 (by rfl) ⟨2487833, by rfl⟩ : syracuseStep 3317111 = 4975667) B4975667
theorem B1473927 : Blo 1472556 1473927 := bstep (se 1 (by rfl) ⟨1105445, by rfl⟩ : syracuseStep 1473927 = 2210891) B2210891
theorem B1473935 : Blo 1472556 1473935 := bstep (se 1 (by rfl) ⟨1105451, by rfl⟩ : syracuseStep 1473935 = 2210903) B2210903
theorem B2211215 : Blo 1472556 2211215 := bstep (se 1 (by rfl) ⟨1658411, by rfl⟩ : syracuseStep 2211215 = 3316823) B3316823
theorem B2211257 : Blo 1472556 2211257 := bstep (se 2 (by rfl) ⟨829221, by rfl⟩ : syracuseStep 2211257 = 1658443) B1658443
theorem B1473979 : Blo 1472556 1473979 := bstep (se 1 (by rfl) ⟨1105484, by rfl⟩ : syracuseStep 1473979 = 2210969) B2210969
theorem B1474055 : Blo 1472556 1474055 := bstep (se 1 (by rfl) ⟨1105541, by rfl⟩ : syracuseStep 1474055 = 2211083) B2211083
theorem B2211335 : Blo 1472556 2211335 := bstep (se 1 (by rfl) ⟨1658501, by rfl⟩ : syracuseStep 2211335 = 3317003) B3317003
theorem B1474063 : Blo 1472556 1474063 := bstep (se 1 (by rfl) ⟨1105547, by rfl⟩ : syracuseStep 1474063 = 2211095) B2211095
theorem B2211371 : Blo 1472556 2211371 := bstep (se 1 (by rfl) ⟨1658528, by rfl⟩ : syracuseStep 2211371 = 3317057) B3317057
theorem B3317291 : Blo 1472556 3317291 := bstep (se 1 (by rfl) ⟨2487968, by rfl⟩ : syracuseStep 3317291 = 4975937) B4975937
theorem B1474107 : Blo 1472556 1474107 := bstep (se 1 (by rfl) ⟨1105580, by rfl⟩ : syracuseStep 1474107 = 2211161) B2211161
theorem B2211401 : Blo 1472556 2211401 := bstep (se 2 (by rfl) ⟨829275, by rfl⟩ : syracuseStep 2211401 = 1658551) B1658551
theorem B3145351 : Blo 1472556 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B4193927 : Blo 1472556 4193927 := bstep (se 1 (by rfl) ⟨3145445, by rfl⟩ : syracuseStep 4193927 = 6290891) B6290891
theorem B1474183 : Blo 1472556 1474183 := bstep (se 1 (by rfl) ⟨1105637, by rfl⟩ : syracuseStep 1474183 = 2211275) B2211275
theorem B1474191 : Blo 1472556 1474191 := bstep (se 1 (by rfl) ⟨1105643, by rfl⟩ : syracuseStep 1474191 = 2211287) B2211287
theorem B1474235 : Blo 1472556 1474235 := bstep (se 1 (by rfl) ⟨1105676, by rfl⟩ : syracuseStep 1474235 = 2211353) B2211353
theorem B2211515 : Blo 1472556 2211515 := bstep (se 1 (by rfl) ⟨1658636, by rfl⟩ : syracuseStep 2211515 = 3317273) B3317273
theorem B7077577 : Blo 1472556 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B2211575 : Blo 1472556 2211575 := bstep (se 1 (by rfl) ⟨1658681, by rfl⟩ : syracuseStep 2211575 = 3317363) B3317363
theorem B1474311 : Blo 1472556 1474311 := bstep (se 1 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 1474311 = 2211467) B2211467
theorem B3538703 : Blo 1472556 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B6291215 : Blo 1472556 6291215 := bstep (se 1 (by rfl) ⟨4718411, by rfl⟩ : syracuseStep 6291215 = 9436823) B9436823
theorem B1474319 : Blo 1472556 1474319 := bstep (se 1 (by rfl) ⟨1105739, by rfl⟩ : syracuseStep 1474319 = 2211479) B2211479
theorem B2211599 : Blo 1472556 2211599 := bstep (se 1 (by rfl) ⟨1658699, by rfl⟩ : syracuseStep 2211599 = 3317399) B3317399
theorem B2211641 : Blo 1472556 2211641 := bstep (se 2 (by rfl) ⟨829365, by rfl⟩ : syracuseStep 2211641 = 1658731) B1658731
theorem B5594939 : Blo 1472556 5594939 := bstep (se 1 (by rfl) ⟨4196204, by rfl⟩ : syracuseStep 5594939 = 8392409) B8392409
theorem B1474363 : Blo 1472556 1474363 := bstep (se 1 (by rfl) ⟨1105772, by rfl⟩ : syracuseStep 1474363 = 2211545) B2211545
theorem B8388467 : Blo 1472556 8388467 := bstep (se 1 (by rfl) ⟨6291350, by rfl⟩ : syracuseStep 8388467 = 12582701) B12582701
theorem B1474439 : Blo 1472556 1474439 := bstep (se 1 (by rfl) ⟨1105829, by rfl⟩ : syracuseStep 1474439 = 2211659) B2211659
theorem B2211719 : Blo 1472556 2211719 := bstep (se 1 (by rfl) ⟨1658789, by rfl⟩ : syracuseStep 2211719 = 3317579) B3317579
theorem B1474447 : Blo 1472556 1474447 := bstep (se 1 (by rfl) ⟨1105835, by rfl⟩ : syracuseStep 1474447 = 2211671) B2211671
theorem B3317651 : Blo 1472556 3317651 := bstep (se 1 (by rfl) ⟨2488238, by rfl⟩ : syracuseStep 3317651 = 4976477) B4976477
theorem B2211755 : Blo 1472556 2211755 := bstep (se 1 (by rfl) ⟨1658816, by rfl⟩ : syracuseStep 2211755 = 3317633) B3317633
theorem B1474491 : Blo 1472556 1474491 := bstep (se 1 (by rfl) ⟨1105868, by rfl⟩ : syracuseStep 1474491 = 2211737) B2211737
theorem B2211785 : Blo 1472556 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B3317705 : Blo 1472556 3317705 := bstep (se 2 (by rfl) ⟨1244139, by rfl⟩ : syracuseStep 3317705 = 2488279) B2488279
theorem B2097191 : Blo 1472556 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B3727417 : Blo 1472556 3727417 := bstep (se 2 (by rfl) ⟨1397781, by rfl⟩ : syracuseStep 3727417 = 2795563) B2795563
theorem B6381625 : Blo 1472556 6381625 := bstep (se 2 (by rfl) ⟨2393109, by rfl⟩ : syracuseStep 6381625 = 4786219) B4786219
theorem B4972697 : Blo 1472556 4972697 := bstep (se 2 (by rfl) ⟨1864761, by rfl⟩ : syracuseStep 4972697 = 3729523) B3729523
theorem B12763453 : Blo 1472556 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B3727721 : Blo 1472556 3727721 := bstep (se 2 (by rfl) ⟨1397895, by rfl⟩ : syracuseStep 3727721 = 2795791) B2795791
theorem B4194803 : Blo 1472556 4194803 := bstep (se 1 (by rfl) ⟨3146102, by rfl⟩ : syracuseStep 4194803 = 6292205) B6292205
theorem B3637747 : Blo 1472556 3637747 := bstep (se 1 (by rfl) ⟨2728310, by rfl⟩ : syracuseStep 3637747 = 5456621) B5456621
theorem B2097743 : Blo 1472556 2097743 := bstep (se 1 (by rfl) ⟨1573307, by rfl⟩ : syracuseStep 2097743 = 3146615) B3146615
theorem B9437897 : Blo 1472556 9437897 := bstep (se 2 (by rfl) ⟨3539211, by rfl⟩ : syracuseStep 9437897 = 7078423) B7078423
theorem B4195145 : Blo 1472556 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B4195259 : Blo 1472556 4195259 := bstep (se 1 (by rfl) ⟨3146444, by rfl⟩ : syracuseStep 4195259 = 6292889) B6292889
theorem B3146683 : Blo 1472556 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B11658241 : Blo 1472556 11658241 := bstep (se 2 (by rfl) ⟨4371840, by rfl⟩ : syracuseStep 11658241 = 8743681) B8743681
theorem B7463987 : Blo 1472556 7463987 := bstep (se 1 (by rfl) ⟨5597990, by rfl⟩ : syracuseStep 7463987 = 11195981) B11195981
theorem B4195385 : Blo 1472556 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B3277903 : Blo 1472556 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B11953271 : Blo 1472556 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B2655355 : Blo 1472556 2655355 := bstep (se 1 (by rfl) ⟨1991516, by rfl⟩ : syracuseStep 2655355 = 3983033) B3983033
theorem B5383415 : Blo 1472556 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B4973885 : Blo 1472556 4973885 := bstep (se 3 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 4973885 = 1865207) B1865207
theorem B8078717 : Blo 1472556 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B1574363 : Blo 1472556 1574363 := bstep (se 1 (by rfl) ⟨1180772, by rfl⟩ : syracuseStep 1574363 = 2361545) B2361545
theorem B17917451 : Blo 1472556 17917451 := bstep (se 1 (by rfl) ⟨13438088, by rfl⟩ : syracuseStep 17917451 = 26876177) B26876177
theorem B5596883 : Blo 1472556 5596883 := bstep (se 1 (by rfl) ⟨4197662, by rfl⟩ : syracuseStep 5596883 = 8395325) B8395325
theorem B11183831 : Blo 1472556 11183831 := bstep (se 1 (by rfl) ⟨8387873, by rfl⟩ : syracuseStep 11183831 = 16775747) B16775747
theorem B1656751 : Blo 1472556 1656751 := bstep (se 1 (by rfl) ⟨1242563, by rfl⟩ : syracuseStep 1656751 = 2485127) B2485127
theorem B2361307 : Blo 1472556 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B47777795 : Blo 1472556 47777795 := bstep (se 1 (by rfl) ⟨35833346, by rfl⟩ : syracuseStep 47777795 = 71666693) B71666693
theorem B40331357 : Blo 1472556 40331357 := bstep (se 3 (by rfl) ⟨7562129, by rfl⟩ : syracuseStep 40331357 = 15124259) B15124259
theorem B4974749 : Blo 1472556 4974749 := bstep (se 3 (by rfl) ⟨932765, by rfl⟩ : syracuseStep 4974749 = 1865531) B1865531
theorem B3541163 : Blo 1472556 3541163 := bstep (se 1 (by rfl) ⟨2655872, by rfl⟩ : syracuseStep 3541163 = 5311745) B5311745
theorem B1657183 : Blo 1472556 1657183 := bstep (se 1 (by rfl) ⟨1242887, by rfl⟩ : syracuseStep 1657183 = 2485775) B2485775
theorem B2795951 : Blo 1472556 2795951 := bstep (se 1 (by rfl) ⟨2096963, by rfl⟩ : syracuseStep 2795951 = 4193927) B4193927
theorem B3729959 : Blo 1472556 3729959 := bstep (se 1 (by rfl) ⟨2797469, by rfl⟩ : syracuseStep 3729959 = 5594939) B5594939
theorem B2361935 : Blo 1472556 2361935 := bstep (se 1 (by rfl) ⟨1771451, by rfl⟩ : syracuseStep 2361935 = 3542903) B3542903
theorem B4975289 : Blo 1472556 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B1657543 : Blo 1472556 1657543 := bstep (se 1 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 1657543 = 2486315) B2486315
theorem B11504339 : Blo 1472556 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B2484985 : Blo 1472556 2484985 := bstep (se 2 (by rfl) ⟨931869, by rfl⟩ : syracuseStep 2484985 = 1863739) B1863739
theorem B26889029 : Blo 1472556 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B2796383 : Blo 1472556 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B5311327 : Blo 1472556 5311327 := bstep (se 1 (by rfl) ⟨3983495, by rfl⟩ : syracuseStep 5311327 = 7966991) B7966991
theorem B3730283 : Blo 1472556 3730283 := bstep (se 1 (by rfl) ⟨2797712, by rfl⟩ : syracuseStep 3730283 = 5595425) B5595425
theorem B4721665 : Blo 1472556 4721665 := bstep (se 2 (by rfl) ⟨1770624, by rfl⟩ : syracuseStep 4721665 = 3541249) B3541249
theorem B2485255 : Blo 1472556 2485255 := bstep (se 1 (by rfl) ⟨1863941, by rfl⟩ : syracuseStep 2485255 = 3727883) B3727883
theorem B31878157 : Blo 1472556 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B9440459 : Blo 1472556 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B8391883 : Blo 1472556 8391883 := bstep (se 1 (by rfl) ⟨6293912, by rfl⟩ : syracuseStep 8391883 = 12587825) B12587825
theorem B4975883 : Blo 1472556 4975883 := bstep (se 1 (by rfl) ⟨3731912, by rfl⟩ : syracuseStep 4975883 = 7463825) B7463825
theorem B65514865 : Blo 1472556 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B23883133 : Blo 1472556 23883133 := bstep (se 3 (by rfl) ⟨4478087, by rfl⟩ : syracuseStep 23883133 = 8956175) B8956175
theorem B47787407 : Blo 1472556 47787407 := bstep (se 1 (by rfl) ⟨35840555, by rfl⟩ : syracuseStep 47787407 = 71681111) B71681111
theorem B2485687 : Blo 1472556 2485687 := bstep (se 1 (by rfl) ⟨1864265, by rfl⟩ : syracuseStep 2485687 = 3728531) B3728531
theorem B3730931 : Blo 1472556 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B4976153 : Blo 1472556 4976153 := bstep (se 2 (by rfl) ⟨1866057, by rfl⟩ : syracuseStep 4976153 = 3732115) B3732115
theorem B1658407 : Blo 1472556 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B13618775 : Blo 1472556 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B2485883 : Blo 1472556 2485883 := bstep (se 1 (by rfl) ⟨1864412, by rfl⟩ : syracuseStep 2485883 = 3728825) B3728825
theorem B4198027 : Blo 1472556 4198027 := bstep (se 1 (by rfl) ⟨3148520, by rfl⟩ : syracuseStep 4198027 = 6297041) B6297041
theorem B3731143 : Blo 1472556 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B10768223 : Blo 1472556 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B3313583 : Blo 1472556 3313583 := bstep (se 1 (by rfl) ⟨2485187, by rfl⟩ : syracuseStep 3313583 = 4970375) B4970375
theorem B3362735 : Blo 1472556 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B2486281 : Blo 1472556 2486281 := bstep (se 2 (by rfl) ⟨932355, by rfl⟩ : syracuseStep 2486281 = 1864711) B1864711
theorem B3313835 : Blo 1472556 3313835 := bstep (se 1 (by rfl) ⟨2485376, by rfl⟩ : syracuseStep 3313835 = 4970753) B4970753
theorem B2486443 : Blo 1472556 2486443 := bstep (se 1 (by rfl) ⟨1864832, by rfl⟩ : syracuseStep 2486443 = 3729665) B3729665
theorem B16781579 : Blo 1472556 16781579 := bstep (se 1 (by rfl) ⟨12586184, by rfl⟩ : syracuseStep 16781579 = 25172369) B25172369
theorem B4723049 : Blo 1472556 4723049 := bstep (se 2 (by rfl) ⟨1771143, by rfl⟩ : syracuseStep 4723049 = 3542287) B3542287
theorem B2486747 : Blo 1472556 2486747 := bstep (se 1 (by rfl) ⟨1865060, by rfl⟩ : syracuseStep 2486747 = 3730121) B3730121
theorem B11186747 : Blo 1472556 11186747 := bstep (se 1 (by rfl) ⟨8390060, by rfl⟩ : syracuseStep 11186747 = 16780121) B16780121
theorem B3732065 : Blo 1472556 3732065 := bstep (se 2 (by rfl) ⟨1399524, by rfl⟩ : syracuseStep 3732065 = 2799049) B2799049
theorem B3314375 : Blo 1472556 3314375 := bstep (se 1 (by rfl) ⟨2485781, by rfl⟩ : syracuseStep 3314375 = 4971563) B4971563
theorem B2486983 : Blo 1472556 2486983 := bstep (se 1 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 2486983 = 3730475) B3730475
theorem B2798327 : Blo 1472556 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B7459613 : Blo 1472556 7459613 := bstep (se 3 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 7459613 = 2797355) B2797355
theorem B2487145 : Blo 1472556 2487145 := bstep (se 2 (by rfl) ⟨932679, by rfl⟩ : syracuseStep 2487145 = 1865359) B1865359
theorem B4543339 : Blo 1472556 4543339 := bstep (se 1 (by rfl) ⟨3407504, by rfl⟩ : syracuseStep 4543339 = 6815009) B6815009
theorem B2798479 : Blo 1472556 2798479 := bstep (se 1 (by rfl) ⟨2098859, by rfl⟩ : syracuseStep 2798479 = 4197719) B4197719
theorem B3781559 : Blo 1472556 3781559 := bstep (se 1 (by rfl) ⟨2836169, by rfl⟩ : syracuseStep 3781559 = 5672339) B5672339
theorem B76584001 : Blo 1472556 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B18879641 : Blo 1472556 18879641 := bstep (se 2 (by rfl) ⟨7079865, by rfl⟩ : syracuseStep 18879641 = 14159731) B14159731
theorem B9696449 : Blo 1472556 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B5592311 : Blo 1472556 5592311 := bstep (se 1 (by rfl) ⟨4194233, by rfl⟩ : syracuseStep 5592311 = 8388467) B8388467
theorem B3028367 : Blo 1472556 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B2209199 : Blo 1472556 2209199 := bstep (se 1 (by rfl) ⟨1656899, by rfl⟩ : syracuseStep 2209199 = 3313799) B3313799
theorem B2487739 : Blo 1472556 2487739 := bstep (se 1 (by rfl) ⟨1865804, by rfl⟩ : syracuseStep 2487739 = 3731609) B3731609
theorem B2209289 : Blo 1472556 2209289 := bstep (se 2 (by rfl) ⟨828483, by rfl⟩ : syracuseStep 2209289 = 1656967) B1656967
theorem B2209319 : Blo 1472556 2209319 := bstep (se 1 (by rfl) ⟨1656989, by rfl⟩ : syracuseStep 2209319 = 3313979) B3313979
theorem B3315239 : Blo 1472556 3315239 := bstep (se 1 (by rfl) ⟨2486429, by rfl⟩ : syracuseStep 3315239 = 4972859) B4972859
theorem B2487847 : Blo 1472556 2487847 := bstep (se 1 (by rfl) ⟨1865885, by rfl⟩ : syracuseStep 2487847 = 3731771) B3731771
theorem B7173755 : Blo 1472556 7173755 := bstep (se 1 (by rfl) ⟨5380316, by rfl⟩ : syracuseStep 7173755 = 10760633) B10760633
theorem B2209403 : Blo 1472556 2209403 := bstep (se 1 (by rfl) ⟨1657052, by rfl⟩ : syracuseStep 2209403 = 3314105) B3314105
theorem B35837639 : Blo 1472556 35837639 := bstep (se 1 (by rfl) ⟨26878229, by rfl⟩ : syracuseStep 35837639 = 53756459) B53756459
theorem B2987767 : Blo 1472556 2987767 := bstep (se 1 (by rfl) ⟨2240825, by rfl⟩ : syracuseStep 2987767 = 4481651) B4481651
theorem B2209529 : Blo 1472556 2209529 := bstep (se 2 (by rfl) ⟨828573, by rfl⟩ : syracuseStep 2209529 = 1657147) B1657147
theorem B2799353 : Blo 1472556 2799353 := bstep (se 2 (by rfl) ⟨1049757, by rfl⟩ : syracuseStep 2799353 = 2099515) B2099515
theorem B2209631 : Blo 1472556 2209631 := bstep (se 1 (by rfl) ⟨1657223, by rfl⟩ : syracuseStep 2209631 = 3314447) B3314447
theorem B2209643 : Blo 1472556 2209643 := bstep (se 1 (by rfl) ⟨1657232, by rfl⟩ : syracuseStep 2209643 = 3314465) B3314465
theorem B3315563 : Blo 1472556 3315563 := bstep (se 1 (by rfl) ⟨2486672, by rfl⟩ : syracuseStep 3315563 = 4973345) B4973345
theorem B12580717 : Blo 1472556 12580717 := bstep (se 3 (by rfl) ⟨2358884, by rfl⟩ : syracuseStep 12580717 = 4717769) B4717769
theorem B2488171 : Blo 1472556 2488171 := bstep (se 1 (by rfl) ⟨1866128, by rfl⟩ : syracuseStep 2488171 = 3732257) B3732257
theorem B3315617 : Blo 1472556 3315617 := bstep (se 2 (by rfl) ⟨1243356, by rfl⟩ : syracuseStep 3315617 = 2486713) B2486713
theorem B77559761 : Blo 1472556 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B1472591 : Blo 1472556 1472591 := bstep (se 1 (by rfl) ⟨1104443, by rfl⟩ : syracuseStep 1472591 = 2208887) B2208887
theorem B2209871 : Blo 1472556 2209871 := bstep (se 1 (by rfl) ⟨1657403, by rfl⟩ : syracuseStep 2209871 = 3314807) B3314807
theorem B1472607 : Blo 1472556 1472607 := bstep (se 1 (by rfl) ⟨1104455, by rfl⟩ : syracuseStep 1472607 = 2208911) B2208911
theorem B18880613 : Blo 1472556 18880613 := bstep (se 4 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 18880613 = 3540115) B3540115
theorem B22698085 : Blo 1472556 22698085 := bstep (se 4 (by rfl) ⟨2127945, by rfl⟩ : syracuseStep 22698085 = 4255891) B4255891
theorem B1472635 : Blo 1472556 1472635 := bstep (se 1 (by rfl) ⟨1104476, by rfl⟩ : syracuseStep 1472635 = 2208953) B2208953
theorem B38271133 : Blo 1472556 38271133 := bstep (se 3 (by rfl) ⟨7175837, by rfl⟩ : syracuseStep 38271133 = 14351675) B14351675
theorem B7084189 : Blo 1472556 7084189 := bstep (se 3 (by rfl) ⟨1328285, by rfl⟩ : syracuseStep 7084189 = 2656571) B2656571
theorem B1472687 : Blo 1472556 1472687 := bstep (se 1 (by rfl) ⟨1104515, by rfl⟩ : syracuseStep 1472687 = 2209031) B2209031
theorem B5593283 : Blo 1472556 5593283 := bstep (se 1 (by rfl) ⟨4194962, by rfl⟩ : syracuseStep 5593283 = 8389925) B8389925
theorem B1472711 : Blo 1472556 1472711 := bstep (se 1 (by rfl) ⟨1104533, by rfl⟩ : syracuseStep 1472711 = 2209067) B2209067
theorem B2209991 : Blo 1472556 2209991 := bstep (se 1 (by rfl) ⟨1657493, by rfl⟩ : syracuseStep 2209991 = 3314987) B3314987
theorem B1472731 : Blo 1472556 1472731 := bstep (se 1 (by rfl) ⟨1104548, by rfl⟩ : syracuseStep 1472731 = 2209097) B2209097
theorem B3315959 : Blo 1472556 3315959 := bstep (se 1 (by rfl) ⟨2486969, by rfl⟩ : syracuseStep 3315959 = 4973939) B4973939
theorem B2103545 : Blo 1472556 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B1472807 : Blo 1472556 1472807 := bstep (se 1 (by rfl) ⟨1104605, by rfl⟩ : syracuseStep 1472807 = 2209211) B2209211
theorem B1472847 : Blo 1472556 1472847 := bstep (se 1 (by rfl) ⟨1104635, by rfl⟩ : syracuseStep 1472847 = 2209271) B2209271
theorem B1472863 : Blo 1472556 1472863 := bstep (se 1 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 1472863 = 2209295) B2209295
theorem B2210153 : Blo 1472556 2210153 := bstep (se 2 (by rfl) ⟨828807, by rfl⟩ : syracuseStep 2210153 = 1657615) B1657615
theorem B1472891 : Blo 1472556 1472891 := bstep (se 1 (by rfl) ⟨1104668, by rfl⟩ : syracuseStep 1472891 = 2209337) B2209337
theorem B12589465 : Blo 1472556 12589465 := bstep (se 2 (by rfl) ⟨4721049, by rfl⟩ : syracuseStep 12589465 = 9442099) B9442099
theorem B1472943 : Blo 1472556 1472943 := bstep (se 1 (by rfl) ⟨1104707, by rfl⟩ : syracuseStep 1472943 = 2209415) B2209415
theorem B2210231 : Blo 1472556 2210231 := bstep (se 1 (by rfl) ⟨1657673, by rfl⟩ : syracuseStep 2210231 = 3315347) B3315347
theorem B1472967 : Blo 1472556 1472967 := bstep (se 1 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 1472967 = 2209451) B2209451
theorem B1472987 : Blo 1472556 1472987 := bstep (se 1 (by rfl) ⟨1104740, by rfl⟩ : syracuseStep 1472987 = 2209481) B2209481
theorem B2210267 : Blo 1472556 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B11196953 : Blo 1472556 11196953 := bstep (se 2 (by rfl) ⟨4198857, by rfl⟩ : syracuseStep 11196953 = 8397715) B8397715
theorem B1473063 : Blo 1472556 1473063 := bstep (se 1 (by rfl) ⟨1104797, by rfl⟩ : syracuseStep 1473063 = 2209595) B2209595
theorem B40319531 : Blo 1472556 40319531 := bstep (se 1 (by rfl) ⟨30239648, by rfl⟩ : syracuseStep 40319531 = 60479297) B60479297
theorem B1473103 : Blo 1472556 1473103 := bstep (se 1 (by rfl) ⟨1104827, by rfl⟩ : syracuseStep 1473103 = 2209655) B2209655
theorem B1473119 : Blo 1472556 1473119 := bstep (se 1 (by rfl) ⟨1104839, by rfl⟩ : syracuseStep 1473119 = 2209679) B2209679
theorem B4971131 : Blo 1472556 4971131 := bstep (se 1 (by rfl) ⟨3728348, by rfl⟩ : syracuseStep 4971131 = 7456697) B7456697
theorem B1473147 : Blo 1472556 1473147 := bstep (se 1 (by rfl) ⟨1104860, by rfl⟩ : syracuseStep 1473147 = 2209721) B2209721
theorem B1473199 : Blo 1472556 1473199 := bstep (se 1 (by rfl) ⟨1104899, by rfl⟩ : syracuseStep 1473199 = 2209799) B2209799
theorem B1473223 : Blo 1472556 1473223 := bstep (se 1 (by rfl) ⟨1104917, by rfl⟩ : syracuseStep 1473223 = 2209835) B2209835
theorem B5593799 : Blo 1472556 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B1473243 : Blo 1472556 1473243 := bstep (se 1 (by rfl) ⟨1104932, by rfl⟩ : syracuseStep 1473243 = 2209865) B2209865
theorem B4971293 : Blo 1472556 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B1473319 : Blo 1472556 1473319 := bstep (se 1 (by rfl) ⟨1104989, by rfl⟩ : syracuseStep 1473319 = 2209979) B2209979
theorem B3316553 : Blo 1472556 3316553 := bstep (se 2 (by rfl) ⟨1243707, by rfl⟩ : syracuseStep 3316553 = 2487415) B2487415
theorem B1473359 : Blo 1472556 1473359 := bstep (se 1 (by rfl) ⟨1105019, by rfl⟩ : syracuseStep 1473359 = 2210039) B2210039
theorem B38255449 : Blo 1472556 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B1473375 : Blo 1472556 1473375 := bstep (se 1 (by rfl) ⟨1105031, by rfl⟩ : syracuseStep 1473375 = 2210063) B2210063
theorem B1473403 : Blo 1472556 1473403 := bstep (se 1 (by rfl) ⟨1105052, by rfl⟩ : syracuseStep 1473403 = 2210105) B2210105
theorem B1473455 : Blo 1472556 1473455 := bstep (se 1 (by rfl) ⟨1105091, by rfl⟩ : syracuseStep 1473455 = 2210183) B2210183
theorem B2210735 : Blo 1472556 2210735 := bstep (se 1 (by rfl) ⟨1658051, by rfl⟩ : syracuseStep 2210735 = 3316103) B3316103
theorem B1473479 : Blo 1472556 1473479 := bstep (se 1 (by rfl) ⟨1105109, by rfl⟩ : syracuseStep 1473479 = 2210219) B2210219
theorem B1473499 : Blo 1472556 1473499 := bstep (se 1 (by rfl) ⟨1105124, by rfl⟩ : syracuseStep 1473499 = 2210249) B2210249
theorem B2210825 : Blo 1472556 2210825 := bstep (se 2 (by rfl) ⟨829059, by rfl⟩ : syracuseStep 2210825 = 1658119) B1658119
theorem B1473575 : Blo 1472556 1473575 := bstep (se 1 (by rfl) ⟨1105181, by rfl⟩ : syracuseStep 1473575 = 2210363) B2210363
theorem B2210855 : Blo 1472556 2210855 := bstep (se 1 (by rfl) ⟨1658141, by rfl⟩ : syracuseStep 2210855 = 3316283) B3316283
theorem B10771499 : Blo 1472556 10771499 := bstep (se 1 (by rfl) ⟨8078624, by rfl⟩ : syracuseStep 10771499 = 16157249) B16157249
theorem B11951171 : Blo 1472556 11951171 := bstep (se 1 (by rfl) ⟨8963378, by rfl⟩ : syracuseStep 11951171 = 17926757) B17926757
theorem B1473615 : Blo 1472556 1473615 := bstep (se 1 (by rfl) ⟨1105211, by rfl⟩ : syracuseStep 1473615 = 2210423) B2210423
theorem B1473631 : Blo 1472556 1473631 := bstep (se 1 (by rfl) ⟨1105223, by rfl⟩ : syracuseStep 1473631 = 2210447) B2210447
theorem B1473659 : Blo 1472556 1473659 := bstep (se 1 (by rfl) ⟨1105244, by rfl⟩ : syracuseStep 1473659 = 2210489) B2210489
theorem B2210939 : Blo 1472556 2210939 := bstep (se 1 (by rfl) ⟨1658204, by rfl⟩ : syracuseStep 2210939 = 3316409) B3316409
theorem B1473711 : Blo 1472556 1473711 := bstep (se 1 (by rfl) ⟨1105283, by rfl⟩ : syracuseStep 1473711 = 2210567) B2210567
theorem B1473735 : Blo 1472556 1473735 := bstep (se 1 (by rfl) ⟨1105301, by rfl⟩ : syracuseStep 1473735 = 2210603) B2210603
theorem B1473755 : Blo 1472556 1473755 := bstep (se 1 (by rfl) ⟨1105316, by rfl⟩ : syracuseStep 1473755 = 2210633) B2210633
theorem B4193527 : Blo 1472556 4193527 := bstep (se 1 (by rfl) ⟨3145145, by rfl⟩ : syracuseStep 4193527 = 6290291) B6290291
theorem B2211065 : Blo 1472556 2211065 := bstep (se 2 (by rfl) ⟨829149, by rfl⟩ : syracuseStep 2211065 = 1658299) B1658299
theorem B1473831 : Blo 1472556 1473831 := bstep (se 1 (by rfl) ⟨1105373, by rfl⟩ : syracuseStep 1473831 = 2210747) B2210747
theorem B1473871 : Blo 1472556 1473871 := bstep (se 1 (by rfl) ⟨1105403, by rfl⟩ : syracuseStep 1473871 = 2210807) B2210807
theorem B1473887 : Blo 1472556 1473887 := bstep (se 1 (by rfl) ⟨1105415, by rfl⟩ : syracuseStep 1473887 = 2210831) B2210831
theorem B2211167 : Blo 1472556 2211167 := bstep (se 1 (by rfl) ⟨1658375, by rfl⟩ : syracuseStep 2211167 = 3316751) B3316751
theorem B2211179 : Blo 1472556 2211179 := bstep (se 1 (by rfl) ⟨1658384, by rfl⟩ : syracuseStep 2211179 = 3316769) B3316769
theorem B1473915 : Blo 1472556 1473915 := bstep (se 1 (by rfl) ⟨1105436, by rfl⟩ : syracuseStep 1473915 = 2210873) B2210873
theorem B1473967 : Blo 1472556 1473967 := bstep (se 1 (by rfl) ⟨1105475, by rfl⟩ : syracuseStep 1473967 = 2210951) B2210951
theorem B1473991 : Blo 1472556 1473991 := bstep (se 1 (by rfl) ⟨1105493, by rfl⟩ : syracuseStep 1473991 = 2210987) B2210987
theorem B4971995 : Blo 1472556 4971995 := bstep (se 1 (by rfl) ⟨3728996, by rfl⟩ : syracuseStep 4971995 = 7457993) B7457993
theorem B1474011 : Blo 1472556 1474011 := bstep (se 1 (by rfl) ⟨1105508, by rfl⟩ : syracuseStep 1474011 = 2211017) B2211017
theorem B2653703 : Blo 1472556 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B4193801 : Blo 1472556 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B1474087 : Blo 1472556 1474087 := bstep (se 1 (by rfl) ⟨1105565, by rfl⟩ : syracuseStep 1474087 = 2211131) B2211131
theorem B1474127 : Blo 1472556 1474127 := bstep (se 1 (by rfl) ⟨1105595, by rfl⟩ : syracuseStep 1474127 = 2211191) B2211191
theorem B2211407 : Blo 1472556 2211407 := bstep (se 1 (by rfl) ⟨1658555, by rfl⟩ : syracuseStep 2211407 = 3317111) B3317111
theorem B1474143 : Blo 1472556 1474143 := bstep (se 1 (by rfl) ⟨1105607, by rfl⟩ : syracuseStep 1474143 = 2211215) B2211215
theorem B9436769 : Blo 1472556 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B3317345 : Blo 1472556 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B1474171 : Blo 1472556 1474171 := bstep (se 1 (by rfl) ⟨1105628, by rfl⟩ : syracuseStep 1474171 = 2211257) B2211257
theorem B5594771 : Blo 1472556 5594771 := bstep (se 1 (by rfl) ⟨4196078, by rfl⟩ : syracuseStep 5594771 = 8392157) B8392157
theorem B1474223 : Blo 1472556 1474223 := bstep (se 1 (by rfl) ⟨1105667, by rfl⟩ : syracuseStep 1474223 = 2211335) B2211335
theorem B1474247 : Blo 1472556 1474247 := bstep (se 1 (by rfl) ⟨1105685, by rfl⟩ : syracuseStep 1474247 = 2211371) B2211371
theorem B2211527 : Blo 1472556 2211527 := bstep (se 1 (by rfl) ⟨1658645, by rfl⟩ : syracuseStep 2211527 = 3317291) B3317291
theorem B1474267 : Blo 1472556 1474267 := bstep (se 1 (by rfl) ⟨1105700, by rfl⟩ : syracuseStep 1474267 = 2211401) B2211401
theorem B1474343 : Blo 1472556 1474343 := bstep (se 1 (by rfl) ⟨1105757, by rfl⟩ : syracuseStep 1474343 = 2211515) B2211515
theorem B5594953 : Blo 1472556 5594953 := bstep (se 2 (by rfl) ⟨2098107, by rfl⟩ : syracuseStep 5594953 = 4196215) B4196215
theorem B1474383 : Blo 1472556 1474383 := bstep (se 1 (by rfl) ⟨1105787, by rfl⟩ : syracuseStep 1474383 = 2211575) B2211575
theorem B2359135 : Blo 1472556 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B4194143 : Blo 1472556 4194143 := bstep (se 1 (by rfl) ⟨3145607, by rfl⟩ : syracuseStep 4194143 = 6291215) B6291215
theorem B1474399 : Blo 1472556 1474399 := bstep (se 1 (by rfl) ⟨1105799, by rfl⟩ : syracuseStep 1474399 = 2211599) B2211599
theorem B2211689 : Blo 1472556 2211689 := bstep (se 2 (by rfl) ⟨829383, by rfl⟩ : syracuseStep 2211689 = 1658767) B1658767
theorem B1474427 : Blo 1472556 1474427 := bstep (se 1 (by rfl) ⟨1105820, by rfl⟩ : syracuseStep 1474427 = 2211641) B2211641
theorem B1474479 : Blo 1472556 1474479 := bstep (se 1 (by rfl) ⟨1105859, by rfl⟩ : syracuseStep 1474479 = 2211719) B2211719
theorem B2211767 : Blo 1472556 2211767 := bstep (se 1 (by rfl) ⟨1658825, by rfl⟩ : syracuseStep 2211767 = 3317651) B3317651
theorem B3317687 : Blo 1472556 3317687 := bstep (se 1 (by rfl) ⟨2488265, by rfl⟩ : syracuseStep 3317687 = 4976531) B4976531
theorem B1474503 : Blo 1472556 1474503 := bstep (se 1 (by rfl) ⟨1105877, by rfl⟩ : syracuseStep 1474503 = 2211755) B2211755
theorem B1474523 : Blo 1472556 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B2211803 : Blo 1472556 2211803 := bstep (se 1 (by rfl) ⟨1658852, by rfl⟩ : syracuseStep 2211803 = 3317705) B3317705
theorem B51028177 : Blo 1472556 51028177 := bstep (se 2 (by rfl) ⟨19135566, by rfl⟩ : syracuseStep 51028177 = 38271133) B38271133
theorem B9445585 : Blo 1472556 9445585 := bstep (se 2 (by rfl) ⟨3542094, by rfl⟩ : syracuseStep 9445585 = 7084189) B7084189
theorem B31875389 : Blo 1472556 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B6291931 : Blo 1472556 6291931 := bstep (se 1 (by rfl) ⟨4718948, by rfl⟩ : syracuseStep 6291931 = 9437897) B9437897
theorem B4973075 : Blo 1472556 4973075 := bstep (se 1 (by rfl) ⟨3729806, by rfl⟩ : syracuseStep 4973075 = 7459613) B7459613
theorem B16785953 : Blo 1472556 16785953 := bstep (se 2 (by rfl) ⟨6294732, by rfl⟩ : syracuseStep 16785953 = 12589465) B12589465
theorem B4850329 : Blo 1472556 4850329 := bstep (se 2 (by rfl) ⟨1818873, by rfl⟩ : syracuseStep 4850329 = 3637747) B3637747
theorem B3728207 : Blo 1472556 3728207 := bstep (se 1 (by rfl) ⟨2796155, by rfl⟩ : syracuseStep 3728207 = 5592311) B5592311
theorem B3588943 : Blo 1472556 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B11944967 : Blo 1472556 11944967 := bstep (se 1 (by rfl) ⟨8958725, by rfl⟩ : syracuseStep 11944967 = 17917451) B17917451
theorem B7455887 : Blo 1472556 7455887 := bstep (se 1 (by rfl) ⟨5591915, by rfl⟩ : syracuseStep 7455887 = 11183831) B11183831
theorem B4195577 : Blo 1472556 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B31851863 : Blo 1472556 31851863 := bstep (se 1 (by rfl) ⟨23888897, by rfl⟩ : syracuseStep 31851863 = 47777795) B47777795
theorem B26887571 : Blo 1472556 26887571 := bstep (se 1 (by rfl) ⟨20165678, by rfl⟩ : syracuseStep 26887571 = 40331357) B40331357
theorem B3728855 : Blo 1472556 3728855 := bstep (se 1 (by rfl) ⟨2796641, by rfl⟩ : syracuseStep 3728855 = 5593283) B5593283
theorem B3540473 : Blo 1472556 3540473 := bstep (se 2 (by rfl) ⟨1327677, by rfl⟩ : syracuseStep 3540473 = 2655355) B2655355
theorem B7464635 : Blo 1472556 7464635 := bstep (se 1 (by rfl) ⟨5598476, by rfl⟩ : syracuseStep 7464635 = 11196953) B11196953
theorem B26879687 : Blo 1472556 26879687 := bstep (se 1 (by rfl) ⟨20159765, by rfl⟩ : syracuseStep 26879687 = 40319531) B40319531
theorem B1574623 : Blo 1472556 1574623 := bstep (se 1 (by rfl) ⟨1180967, by rfl⟩ : syracuseStep 1574623 = 2361935) B2361935
theorem B3729199 : Blo 1472556 3729199 := bstep (se 1 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 3729199 = 5593799) B5593799
theorem B7669559 : Blo 1472556 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B87353153 : Blo 1472556 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B31844177 : Blo 1472556 31844177 := bstep (se 2 (by rfl) ⟨11941566, by rfl⟩ : syracuseStep 31844177 = 23883133) B23883133
theorem B17926019 : Blo 1472556 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B6293639 : Blo 1472556 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B5597369 : Blo 1472556 5597369 := bstep (se 2 (by rfl) ⟨2099013, by rfl⟩ : syracuseStep 5597369 = 4198027) B4198027
theorem B7457021 : Blo 1472556 7457021 := bstep (se 3 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 7457021 = 2796383) B2796383
theorem B4974857 : Blo 1472556 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B3983689 : Blo 1472556 3983689 := bstep (se 2 (by rfl) ⟨1493883, by rfl⟩ : syracuseStep 3983689 = 2987767) B2987767
theorem B2795867 : Blo 1472556 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B9079183 : Blo 1472556 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B1657255 : Blo 1472556 1657255 := bstep (se 1 (by rfl) ⟨1242941, by rfl⟩ : syracuseStep 1657255 = 2485883) B2485883
theorem B3729847 : Blo 1472556 3729847 := bstep (se 1 (by rfl) ⟨2797385, by rfl⟩ : syracuseStep 3729847 = 5594771) B5594771
theorem B2796095 : Blo 1472556 2796095 := bstep (se 1 (by rfl) ⟨2097071, by rfl⟩ : syracuseStep 2796095 = 4194143) B4194143
theorem B7178815 : Blo 1472556 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B3148409 : Blo 1472556 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B28723997 : Blo 1472556 28723997 := bstep (se 3 (by rfl) ⟨5385749, by rfl⟩ : syracuseStep 28723997 = 10771499) B10771499
theorem B30264113 : Blo 1472556 30264113 := bstep (se 2 (by rfl) ⟨11349042, by rfl⟩ : syracuseStep 30264113 = 22698085) B22698085
theorem B2485147 : Blo 1472556 2485147 := bstep (se 1 (by rfl) ⟨1863860, by rfl⟩ : syracuseStep 2485147 = 3727721) B3727721
theorem B1657831 : Blo 1472556 1657831 := bstep (se 1 (by rfl) ⟨1243373, by rfl⟩ : syracuseStep 1657831 = 2486747) B2486747
theorem B2796535 : Blo 1472556 2796535 := bstep (se 1 (by rfl) ⟨2097401, by rfl⟩ : syracuseStep 2796535 = 4194803) B4194803
theorem B7457831 : Blo 1472556 7457831 := bstep (se 1 (by rfl) ⟨5593373, by rfl⟩ : syracuseStep 7457831 = 11186747) B11186747
theorem B17017937 : Blo 1472556 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B25857197 : Blo 1472556 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B2796763 : Blo 1472556 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B2796839 : Blo 1472556 2796839 := bstep (se 1 (by rfl) ⟨2097629, by rfl⟩ : syracuseStep 2796839 = 4195259) B4195259
theorem B4975991 : Blo 1472556 4975991 := bstep (se 1 (by rfl) ⟨3731993, by rfl⟩ : syracuseStep 4975991 = 7463987) B7463987
theorem B2796923 : Blo 1472556 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B12586427 : Blo 1472556 12586427 := bstep (se 1 (by rfl) ⟨9439820, by rfl⟩ : syracuseStep 12586427 = 18879641) B18879641
theorem B5385811 : Blo 1472556 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B12594797 : Blo 1472556 12594797 := bstep (se 3 (by rfl) ⟨2361524, by rfl⟩ : syracuseStep 12594797 = 4723049) B4723049
theorem B3313313 : Blo 1472556 3313313 := bstep (se 2 (by rfl) ⟨1242492, by rfl⟩ : syracuseStep 3313313 = 2484985) B2484985
theorem B51007265 : Blo 1472556 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B7081769 : Blo 1472556 7081769 := bstep (se 2 (by rfl) ⟨2655663, by rfl⟩ : syracuseStep 7081769 = 5311327) B5311327
theorem B23891759 : Blo 1472556 23891759 := bstep (se 1 (by rfl) ⟨17918819, by rfl⟩ : syracuseStep 23891759 = 35837639) B35837639
theorem B3731255 : Blo 1472556 3731255 := bstep (se 1 (by rfl) ⟨2798441, by rfl⟩ : syracuseStep 3731255 = 5596883) B5596883
theorem B6057785 : Blo 1472556 6057785 := bstep (se 2 (by rfl) ⟨2271669, by rfl⟩ : syracuseStep 6057785 = 4543339) B4543339
theorem B3731305 : Blo 1472556 3731305 := bstep (se 2 (by rfl) ⟨1399239, by rfl⟩ : syracuseStep 3731305 = 2798479) B2798479
theorem B4198301 : Blo 1472556 4198301 := bstep (se 3 (by rfl) ⟨787181, by rfl⟩ : syracuseStep 4198301 = 1574363) B1574363
theorem B6295553 : Blo 1472556 6295553 := bstep (se 2 (by rfl) ⟨2360832, by rfl⟩ : syracuseStep 6295553 = 4721665) B4721665
theorem B15544321 : Blo 1472556 15544321 := bstep (se 2 (by rfl) ⟨5829120, by rfl⟩ : syracuseStep 15544321 = 11658241) B11658241
theorem B3313673 : Blo 1472556 3313673 := bstep (se 2 (by rfl) ⟨1242627, by rfl⟩ : syracuseStep 3313673 = 2485255) B2485255
theorem B42504209 : Blo 1472556 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B12587075 : Blo 1472556 12587075 := bstep (se 1 (by rfl) ⟨9440306, by rfl⟩ : syracuseStep 12587075 = 18880613) B18880613
theorem B4370537 : Blo 1472556 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B1863967 : Blo 1472556 1863967 := bstep (se 1 (by rfl) ⟨1397975, by rfl⟩ : syracuseStep 1863967 = 2795951) B2795951
theorem B5591369 : Blo 1472556 5591369 := bstep (se 2 (by rfl) ⟨2096763, by rfl⟩ : syracuseStep 5591369 = 4193527) B4193527
theorem B2486639 : Blo 1472556 2486639 := bstep (se 1 (by rfl) ⟨1864979, by rfl⟩ : syracuseStep 2486639 = 3729959) B3729959
theorem B3314087 : Blo 1472556 3314087 := bstep (se 1 (by rfl) ⟨2485565, by rfl⟩ : syracuseStep 3314087 = 4971131) B4971131
theorem B3314195 : Blo 1472556 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B2486855 : Blo 1472556 2486855 := bstep (se 1 (by rfl) ⟨1865141, by rfl⟩ : syracuseStep 2486855 = 3730283) B3730283
theorem B3314249 : Blo 1472556 3314249 := bstep (se 2 (by rfl) ⟨1242843, by rfl⟩ : syracuseStep 3314249 = 2485687) B2485687
theorem B7967447 : Blo 1472556 7967447 := bstep (se 1 (by rfl) ⟨5975585, by rfl⟩ : syracuseStep 7967447 = 11951171) B11951171
theorem B3314663 : Blo 1472556 3314663 := bstep (se 1 (by rfl) ⟨2485997, by rfl⟩ : syracuseStep 3314663 = 4971995) B4971995
theorem B2487287 : Blo 1472556 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B7459937 : Blo 1472556 7459937 := bstep (se 2 (by rfl) ⟨2797476, by rfl⟩ : syracuseStep 7459937 = 5594953) B5594953
theorem B8967293 : Blo 1472556 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B16774289 : Blo 1472556 16774289 := bstep (se 2 (by rfl) ⟨6290358, by rfl⟩ : syracuseStep 16774289 = 12580717) B12580717
theorem B2209001 : Blo 1472556 2209001 := bstep (se 2 (by rfl) ⟨828375, by rfl⟩ : syracuseStep 2209001 = 1656751) B1656751
theorem B2209055 : Blo 1472556 2209055 := bstep (se 1 (by rfl) ⟨1656791, by rfl⟩ : syracuseStep 2209055 = 3313583) B3313583
theorem B3315041 : Blo 1472556 3315041 := bstep (se 2 (by rfl) ⟨1243140, by rfl⟩ : syracuseStep 3315041 = 2486281) B2486281
theorem B4969889 : Blo 1472556 4969889 := bstep (se 2 (by rfl) ⟨1863708, by rfl⟩ : syracuseStep 4969889 = 3727417) B3727417
theorem B8508833 : Blo 1472556 8508833 := bstep (se 2 (by rfl) ⟨3190812, by rfl⟩ : syracuseStep 8508833 = 6381625) B6381625
theorem B3315131 : Blo 1472556 3315131 := bstep (se 1 (by rfl) ⟨2486348, by rfl⟩ : syracuseStep 3315131 = 4972697) B4972697
theorem B5592509 : Blo 1472556 5592509 := bstep (se 3 (by rfl) ⟨1048595, by rfl⟩ : syracuseStep 5592509 = 2097191) B2097191
theorem B2209223 : Blo 1472556 2209223 := bstep (se 1 (by rfl) ⟨1656917, by rfl⟩ : syracuseStep 2209223 = 3313835) B3313835
theorem B11187719 : Blo 1472556 11187719 := bstep (se 1 (by rfl) ⟨8390789, by rfl⟩ : syracuseStep 11187719 = 16781579) B16781579
theorem B3315257 : Blo 1472556 3315257 := bstep (se 2 (by rfl) ⟨1243221, by rfl⟩ : syracuseStep 3315257 = 2486443) B2486443
theorem B2488043 : Blo 1472556 2488043 := bstep (se 1 (by rfl) ⟨1866032, by rfl⟩ : syracuseStep 2488043 = 3732065) B3732065
theorem B9443101 : Blo 1472556 9443101 := bstep (se 3 (by rfl) ⟨1770581, by rfl⟩ : syracuseStep 9443101 = 3541163) B3541163
theorem B2209577 : Blo 1472556 2209577 := bstep (se 2 (by rfl) ⟨828591, by rfl⟩ : syracuseStep 2209577 = 1657183) B1657183
theorem B2209583 : Blo 1472556 2209583 := bstep (se 1 (by rfl) ⟨1657187, by rfl⟩ : syracuseStep 2209583 = 3314375) B3314375
theorem B2521039 : Blo 1472556 2521039 := bstep (se 1 (by rfl) ⟨1890779, by rfl⟩ : syracuseStep 2521039 = 3781559) B3781559
theorem B5609453 : Blo 1472556 5609453 := bstep (se 3 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 5609453 = 2103545) B2103545
theorem B3315923 : Blo 1472556 3315923 := bstep (se 1 (by rfl) ⟨2486942, by rfl⟩ : syracuseStep 3315923 = 4973885) B4973885
theorem B2210057 : Blo 1472556 2210057 := bstep (se 2 (by rfl) ⟨828771, by rfl⟩ : syracuseStep 2210057 = 1657543) B1657543
theorem B3315977 : Blo 1472556 3315977 := bstep (se 2 (by rfl) ⟨1243491, by rfl⟩ : syracuseStep 3315977 = 2486983) B2486983
theorem B1472799 : Blo 1472556 1472799 := bstep (se 1 (by rfl) ⟨1104599, by rfl⟩ : syracuseStep 1472799 = 2209199) B2209199
theorem B1472859 : Blo 1472556 1472859 := bstep (se 1 (by rfl) ⟨1104644, by rfl⟩ : syracuseStep 1472859 = 2209289) B2209289
theorem B1472879 : Blo 1472556 1472879 := bstep (se 1 (by rfl) ⟨1104659, by rfl⟩ : syracuseStep 1472879 = 2209319) B2209319
theorem B2210159 : Blo 1472556 2210159 := bstep (se 1 (by rfl) ⟨1657619, by rfl⟩ : syracuseStep 2210159 = 3315239) B3315239
theorem B8075645 : Blo 1472556 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B4782503 : Blo 1472556 4782503 := bstep (se 1 (by rfl) ⟨3586877, by rfl⟩ : syracuseStep 4782503 = 7173755) B7173755
theorem B1472935 : Blo 1472556 1472935 := bstep (se 1 (by rfl) ⟨1104701, by rfl⟩ : syracuseStep 1472935 = 2209403) B2209403
theorem B3316193 : Blo 1472556 3316193 := bstep (se 2 (by rfl) ⟨1243572, by rfl⟩ : syracuseStep 3316193 = 2487145) B2487145
theorem B1473019 : Blo 1472556 1473019 := bstep (se 1 (by rfl) ⟨1104764, by rfl⟩ : syracuseStep 1473019 = 2209529) B2209529
theorem B1866235 : Blo 1472556 1866235 := bstep (se 1 (by rfl) ⟨1399676, by rfl⟩ : syracuseStep 1866235 = 2799353) B2799353
theorem B1473087 : Blo 1472556 1473087 := bstep (se 1 (by rfl) ⟨1104815, by rfl⟩ : syracuseStep 1473087 = 2209631) B2209631
theorem B1473095 : Blo 1472556 1473095 := bstep (se 1 (by rfl) ⟨1104821, by rfl⟩ : syracuseStep 1473095 = 2209643) B2209643
theorem B2210375 : Blo 1472556 2210375 := bstep (se 1 (by rfl) ⟨1657781, by rfl⟩ : syracuseStep 2210375 = 3315563) B3315563
theorem B2210411 : Blo 1472556 2210411 := bstep (se 1 (by rfl) ⟨1657808, by rfl⟩ : syracuseStep 2210411 = 3315617) B3315617
theorem B51706507 : Blo 1472556 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B1473247 : Blo 1472556 1473247 := bstep (se 1 (by rfl) ⟨1104935, by rfl⟩ : syracuseStep 1473247 = 2209871) B2209871
theorem B102112001 : Blo 1472556 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B3316499 : Blo 1472556 3316499 := bstep (se 1 (by rfl) ⟨2487374, by rfl⟩ : syracuseStep 3316499 = 4974749) B4974749
theorem B1473327 : Blo 1472556 1473327 := bstep (se 1 (by rfl) ⟨1104995, by rfl⟩ : syracuseStep 1473327 = 2209991) B2209991
theorem B2210639 : Blo 1472556 2210639 := bstep (se 1 (by rfl) ⟨1657979, by rfl⟩ : syracuseStep 2210639 = 3315959) B3315959
theorem B5593981 : Blo 1472556 5593981 := bstep (se 3 (by rfl) ⟨1048871, by rfl⟩ : syracuseStep 5593981 = 2097743) B2097743
theorem B1473435 : Blo 1472556 1473435 := bstep (se 1 (by rfl) ⟨1105076, by rfl⟩ : syracuseStep 1473435 = 2210153) B2210153
theorem B11189177 : Blo 1472556 11189177 := bstep (se 2 (by rfl) ⟨4195941, by rfl⟩ : syracuseStep 11189177 = 8391883) B8391883
theorem B1473487 : Blo 1472556 1473487 := bstep (se 1 (by rfl) ⟨1105115, by rfl⟩ : syracuseStep 1473487 = 2210231) B2210231
theorem B1473511 : Blo 1472556 1473511 := bstep (se 1 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 1473511 = 2210267) B2210267
theorem B3316859 : Blo 1472556 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B12582053 : Blo 1472556 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B2211035 : Blo 1472556 2211035 := bstep (se 1 (by rfl) ⟨1658276, by rfl⟩ : syracuseStep 2211035 = 3316553) B3316553
theorem B3316985 : Blo 1472556 3316985 := bstep (se 2 (by rfl) ⟨1243869, by rfl⟩ : syracuseStep 3316985 = 2487739) B2487739
theorem B1473823 : Blo 1472556 1473823 := bstep (se 1 (by rfl) ⟨1105367, by rfl⟩ : syracuseStep 1473823 = 2210735) B2210735
theorem B7462205 : Blo 1472556 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B1473883 : Blo 1472556 1473883 := bstep (se 1 (by rfl) ⟨1105412, by rfl⟩ : syracuseStep 1473883 = 2210825) B2210825
theorem B1473903 : Blo 1472556 1473903 := bstep (se 1 (by rfl) ⟨1105427, by rfl⟩ : syracuseStep 1473903 = 2210855) B2210855
theorem B2211209 : Blo 1472556 2211209 := bstep (se 2 (by rfl) ⟨829203, by rfl⟩ : syracuseStep 2211209 = 1658407) B1658407
theorem B3317129 : Blo 1472556 3317129 := bstep (se 2 (by rfl) ⟨1243923, by rfl⟩ : syracuseStep 3317129 = 2487847) B2487847
theorem B1473959 : Blo 1472556 1473959 := bstep (se 1 (by rfl) ⟨1105469, by rfl⟩ : syracuseStep 1473959 = 2210939) B2210939
theorem B1474043 : Blo 1472556 1474043 := bstep (se 1 (by rfl) ⟨1105532, by rfl⟩ : syracuseStep 1474043 = 2211065) B2211065
theorem B3317255 : Blo 1472556 3317255 := bstep (se 1 (by rfl) ⟨2487941, by rfl⟩ : syracuseStep 3317255 = 4975883) B4975883
theorem B1474111 : Blo 1472556 1474111 := bstep (se 1 (by rfl) ⟨1105583, by rfl⟩ : syracuseStep 1474111 = 2211167) B2211167
theorem B1474119 : Blo 1472556 1474119 := bstep (se 1 (by rfl) ⟨1105589, by rfl⟩ : syracuseStep 1474119 = 2211179) B2211179
theorem B31858271 : Blo 1472556 31858271 := bstep (se 1 (by rfl) ⟨23893703, by rfl⟩ : syracuseStep 31858271 = 47787407) B47787407
theorem B1769135 : Blo 1472556 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B3317435 : Blo 1472556 3317435 := bstep (se 1 (by rfl) ⟨2488076, by rfl⟩ : syracuseStep 3317435 = 4976153) B4976153
theorem B1474271 : Blo 1472556 1474271 := bstep (se 1 (by rfl) ⟨1105703, by rfl⟩ : syracuseStep 1474271 = 2211407) B2211407
theorem B6291179 : Blo 1472556 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B2211563 : Blo 1472556 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B1474351 : Blo 1472556 1474351 := bstep (se 1 (by rfl) ⟨1105763, by rfl⟩ : syracuseStep 1474351 = 2211527) B2211527
theorem B3317561 : Blo 1472556 3317561 := bstep (se 2 (by rfl) ⟨1244085, by rfl⟩ : syracuseStep 3317561 = 2488171) B2488171
theorem B1474459 : Blo 1472556 1474459 := bstep (se 1 (by rfl) ⟨1105844, by rfl⟩ : syracuseStep 1474459 = 2211689) B2211689
theorem B1474511 : Blo 1472556 1474511 := bstep (se 1 (by rfl) ⟨1105883, by rfl⟩ : syracuseStep 1474511 = 2211767) B2211767
theorem B2211791 : Blo 1472556 2211791 := bstep (se 1 (by rfl) ⟨1658843, by rfl⟩ : syracuseStep 2211791 = 3317687) B3317687
theorem B1474535 : Blo 1472556 1474535 := bstep (se 1 (by rfl) ⟨1105901, by rfl⟩ : syracuseStep 1474535 = 2211803) B2211803
theorem B82903045 : Blo 1472556 82903045 := bstep (se 4 (by rfl) ⟨7772160, by rfl⟩ : syracuseStep 82903045 = 15544321) B15544321
theorem B28336139 : Blo 1472556 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B21250259 : Blo 1472556 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B3727579 : Blo 1472556 3727579 := bstep (se 1 (by rfl) ⟨2795684, by rfl⟩ : syracuseStep 3727579 = 5591369) B5591369
theorem B11190635 : Blo 1472556 11190635 := bstep (se 1 (by rfl) ⟨8392976, by rfl⟩ : syracuseStep 11190635 = 16785953) B16785953
theorem B4973129 : Blo 1472556 4973129 := bstep (se 2 (by rfl) ⟨1864923, by rfl⟩ : syracuseStep 4973129 = 3729847) B3729847
theorem B8389241 : Blo 1472556 8389241 := bstep (se 2 (by rfl) ⟨3145965, by rfl⟩ : syracuseStep 8389241 = 6291931) B6291931
theorem B4973291 : Blo 1472556 4973291 := bstep (se 1 (by rfl) ⟨3729968, by rfl⟩ : syracuseStep 4973291 = 7459937) B7459937
theorem B11182859 : Blo 1472556 11182859 := bstep (se 1 (by rfl) ⟨8387144, by rfl⟩ : syracuseStep 11182859 = 16774289) B16774289
theorem B21234575 : Blo 1472556 21234575 := bstep (se 1 (by rfl) ⟨15925931, by rfl⟩ : syracuseStep 21234575 = 31851863) B31851863
theorem B17925047 : Blo 1472556 17925047 := bstep (se 1 (by rfl) ⟨13443785, by rfl⟩ : syracuseStep 17925047 = 26887571) B26887571
theorem B3728339 : Blo 1472556 3728339 := bstep (se 1 (by rfl) ⟨2796254, by rfl⟩ : syracuseStep 3728339 = 5592509) B5592509
theorem B2360315 : Blo 1472556 2360315 := bstep (se 1 (by rfl) ⟨1770236, by rfl⟩ : syracuseStep 2360315 = 3540473) B3540473
theorem B4785257 : Blo 1472556 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B8397989 : Blo 1472556 8397989 := bstep (se 4 (by rfl) ⟨787311, by rfl⟩ : syracuseStep 8397989 = 1574623) B1574623
theorem B5113039 : Blo 1472556 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B3728713 : Blo 1472556 3728713 := bstep (se 2 (by rfl) ⟨1398267, by rfl⟩ : syracuseStep 3728713 = 2796535) B2796535
theorem B5383763 : Blo 1472556 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B3188335 : Blo 1472556 3188335 := bstep (se 1 (by rfl) ⟨2391251, by rfl⟩ : syracuseStep 3188335 = 4782503) B4782503
theorem B3729017 : Blo 1472556 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B17238131 : Blo 1472556 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B4974803 : Blo 1472556 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B8390951 : Blo 1472556 8390951 := bstep (se 1 (by rfl) ⟨6293213, by rfl⟩ : syracuseStep 8390951 = 12586427) B12586427
theorem B4975073 : Blo 1472556 4975073 := bstep (se 2 (by rfl) ⟨1865652, by rfl⟩ : syracuseStep 4975073 = 3731305) B3731305
theorem B4721179 : Blo 1472556 4721179 := bstep (se 1 (by rfl) ⟨3540884, by rfl⟩ : syracuseStep 4721179 = 7081769) B7081769
theorem B15927839 : Blo 1472556 15927839 := bstep (se 1 (by rfl) ⟨11945879, by rfl⟩ : syracuseStep 15927839 = 23891759) B23891759
theorem B3361385 : Blo 1472556 3361385 := bstep (se 2 (by rfl) ⟨1260519, by rfl⟩ : syracuseStep 3361385 = 2521039) B2521039
theorem B4197035 : Blo 1472556 4197035 := bstep (se 1 (by rfl) ⟨3147776, by rfl⟩ : syracuseStep 4197035 = 6295553) B6295553
theorem B31853245 : Blo 1472556 31853245 := bstep (se 3 (by rfl) ⟨5972483, by rfl⟩ : syracuseStep 31853245 = 11944967) B11944967
theorem B8391383 : Blo 1472556 8391383 := bstep (se 1 (by rfl) ⟨6293537, by rfl⟩ : syracuseStep 8391383 = 12587075) B12587075
theorem B1657759 : Blo 1472556 1657759 := bstep (se 1 (by rfl) ⟨1243319, by rfl⟩ : syracuseStep 1657759 = 2486639) B2486639
theorem B68037569 : Blo 1472556 68037569 := bstep (se 2 (by rfl) ⟨25514088, by rfl⟩ : syracuseStep 68037569 = 51028177) B51028177
theorem B12594113 : Blo 1472556 12594113 := bstep (se 2 (by rfl) ⟨4722792, by rfl⟩ : syracuseStep 12594113 = 9445585) B9445585
theorem B2485289 : Blo 1472556 2485289 := bstep (se 2 (by rfl) ⟨931983, by rfl⟩ : syracuseStep 2485289 = 1863967) B1863967
theorem B1657903 : Blo 1472556 1657903 := bstep (se 1 (by rfl) ⟨1243427, by rfl⟩ : syracuseStep 1657903 = 2486855) B2486855
theorem B5311585 : Blo 1472556 5311585 := bstep (se 2 (by rfl) ⟨1991844, by rfl⟩ : syracuseStep 5311585 = 3983689) B3983689
theorem B5311631 : Blo 1472556 5311631 := bstep (se 1 (by rfl) ⟨3983723, by rfl⟩ : syracuseStep 5311631 = 7967447) B7967447
theorem B2485471 : Blo 1472556 2485471 := bstep (se 1 (by rfl) ⟨1864103, by rfl⟩ : syracuseStep 2485471 = 3728207) B3728207
theorem B1658191 : Blo 1472556 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B9571753 : Blo 1472556 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B6467105 : Blo 1472556 6467105 := bstep (se 2 (by rfl) ⟨2425164, by rfl⟩ : syracuseStep 6467105 = 4850329) B4850329
theorem B3313259 : Blo 1472556 3313259 := bstep (se 1 (by rfl) ⟨2484944, by rfl⟩ : syracuseStep 3313259 = 4969889) B4969889
theorem B5672555 : Blo 1472556 5672555 := bstep (se 1 (by rfl) ⟨4254416, by rfl⟩ : syracuseStep 5672555 = 8508833) B8508833
theorem B2485903 : Blo 1472556 2485903 := bstep (se 1 (by rfl) ⟨1864427, by rfl⟩ : syracuseStep 2485903 = 3728855) B3728855
theorem B7458479 : Blo 1472556 7458479 := bstep (se 1 (by rfl) ⟨5593859, by rfl⟩ : syracuseStep 7458479 = 11187719) B11187719
theorem B4976423 : Blo 1472556 4976423 := bstep (se 1 (by rfl) ⟨3732317, by rfl⟩ : syracuseStep 4976423 = 7464635) B7464635
theorem B17919791 : Blo 1472556 17919791 := bstep (se 1 (by rfl) ⟨13439843, by rfl⟩ : syracuseStep 17919791 = 26879687) B26879687
theorem B1658695 : Blo 1472556 1658695 := bstep (se 1 (by rfl) ⟨1244021, by rfl⟩ : syracuseStep 1658695 = 2488043) B2488043
theorem B7458641 : Blo 1472556 7458641 := bstep (se 2 (by rfl) ⟨2796990, by rfl⟩ : syracuseStep 7458641 = 5593981) B5593981
theorem B3313529 : Blo 1472556 3313529 := bstep (se 2 (by rfl) ⟨1242573, by rfl⟩ : syracuseStep 3313529 = 2485147) B2485147
theorem B21229451 : Blo 1472556 21229451 := bstep (se 1 (by rfl) ⟨15922088, by rfl⟩ : syracuseStep 21229451 = 31844177) B31844177
theorem B3731579 : Blo 1472556 3731579 := bstep (se 1 (by rfl) ⟨2798684, by rfl⟩ : syracuseStep 3731579 = 5597369) B5597369
theorem B1863911 : Blo 1472556 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B1864063 : Blo 1472556 1864063 := bstep (se 1 (by rfl) ⟨1398047, by rfl⟩ : syracuseStep 1864063 = 2796095) B2796095
theorem B19149331 : Blo 1472556 19149331 := bstep (se 1 (by rfl) ⟨14361998, by rfl⟩ : syracuseStep 19149331 = 28723997) B28723997
theorem B7459451 : Blo 1472556 7459451 := bstep (se 1 (by rfl) ⟨5594588, by rfl⟩ : syracuseStep 7459451 = 11189177) B11189177
theorem B7181081 : Blo 1472556 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B1864559 : Blo 1472556 1864559 := bstep (se 1 (by rfl) ⟨1398419, by rfl⟩ : syracuseStep 1864559 = 2796839) B2796839
theorem B1864615 : Blo 1472556 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B21238847 : Blo 1472556 21238847 := bstep (se 1 (by rfl) ⟨15929135, by rfl⟩ : syracuseStep 21238847 = 31858271) B31858271
theorem B2208875 : Blo 1472556 2208875 := bstep (se 1 (by rfl) ⟨1656656, by rfl⟩ : syracuseStep 2208875 = 3313313) B3313313
theorem B2487503 : Blo 1472556 2487503 := bstep (se 1 (by rfl) ⟨1865627, by rfl⟩ : syracuseStep 2487503 = 3731255) B3731255
theorem B2798867 : Blo 1472556 2798867 := bstep (se 1 (by rfl) ⟨2099150, by rfl⟩ : syracuseStep 2798867 = 4198301) B4198301
theorem B2209115 : Blo 1472556 2209115 := bstep (se 1 (by rfl) ⟨1656836, by rfl⟩ : syracuseStep 2209115 = 3313673) B3313673
theorem B11654765 : Blo 1472556 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B2209391 : Blo 1472556 2209391 := bstep (se 1 (by rfl) ⟨1657043, by rfl⟩ : syracuseStep 2209391 = 3314087) B3314087
theorem B2209463 : Blo 1472556 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B3315383 : Blo 1472556 3315383 := bstep (se 1 (by rfl) ⟨2486537, by rfl⟩ : syracuseStep 3315383 = 4973075) B4973075
theorem B16783037 : Blo 1472556 16783037 := bstep (se 3 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 16783037 = 6293639) B6293639
theorem B2209499 : Blo 1472556 2209499 := bstep (se 1 (by rfl) ⟨1657124, by rfl⟩ : syracuseStep 2209499 = 3314249) B3314249
theorem B12105577 : Blo 1472556 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B2209673 : Blo 1472556 2209673 := bstep (se 2 (by rfl) ⟨828627, by rfl⟩ : syracuseStep 2209673 = 1657255) B1657255
theorem B11188205 : Blo 1472556 11188205 := bstep (se 3 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 11188205 = 4195577) B4195577
theorem B2209775 : Blo 1472556 2209775 := bstep (se 1 (by rfl) ⟨1657331, by rfl⟩ : syracuseStep 2209775 = 3314663) B3314663
theorem B2488313 : Blo 1472556 2488313 := bstep (se 2 (by rfl) ⟨933117, by rfl⟩ : syracuseStep 2488313 = 1866235) B1866235
theorem B5978195 : Blo 1472556 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B4970591 : Blo 1472556 4970591 := bstep (se 1 (by rfl) ⟨3727943, by rfl⟩ : syracuseStep 4970591 = 7455887) B7455887
theorem B1472667 : Blo 1472556 1472667 := bstep (se 1 (by rfl) ⟨1104500, by rfl⟩ : syracuseStep 1472667 = 2209001) B2209001
theorem B68942009 : Blo 1472556 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B1472703 : Blo 1472556 1472703 := bstep (se 1 (by rfl) ⟨1104527, by rfl⟩ : syracuseStep 1472703 = 2209055) B2209055
theorem B2210027 : Blo 1472556 2210027 := bstep (se 1 (by rfl) ⟨1657520, by rfl⟩ : syracuseStep 2210027 = 3315041) B3315041
theorem B2210087 : Blo 1472556 2210087 := bstep (se 1 (by rfl) ⟨1657565, by rfl⟩ : syracuseStep 2210087 = 3315131) B3315131
theorem B1472815 : Blo 1472556 1472815 := bstep (se 1 (by rfl) ⟨1104611, by rfl⟩ : syracuseStep 1472815 = 2209223) B2209223
theorem B2210171 : Blo 1472556 2210171 := bstep (se 1 (by rfl) ⟨1657628, by rfl⟩ : syracuseStep 2210171 = 3315257) B3315257
theorem B1473051 : Blo 1472556 1473051 := bstep (se 1 (by rfl) ⟨1104788, by rfl⟩ : syracuseStep 1473051 = 2209577) B2209577
theorem B1473055 : Blo 1472556 1473055 := bstep (se 1 (by rfl) ⟨1104791, by rfl⟩ : syracuseStep 1473055 = 2209583) B2209583
theorem B58235435 : Blo 1472556 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B11950679 : Blo 1472556 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B2210441 : Blo 1472556 2210441 := bstep (se 2 (by rfl) ⟨828915, by rfl⟩ : syracuseStep 2210441 = 1657831) B1657831
theorem B2210615 : Blo 1472556 2210615 := bstep (se 1 (by rfl) ⟨1657961, by rfl⟩ : syracuseStep 2210615 = 3315923) B3315923
theorem B4971347 : Blo 1472556 4971347 := bstep (se 1 (by rfl) ⟨3728510, by rfl⟩ : syracuseStep 4971347 = 7457021) B7457021
theorem B1473371 : Blo 1472556 1473371 := bstep (se 1 (by rfl) ⟨1105028, by rfl⟩ : syracuseStep 1473371 = 2210057) B2210057
theorem B2210651 : Blo 1472556 2210651 := bstep (se 1 (by rfl) ⟨1657988, by rfl⟩ : syracuseStep 2210651 = 3315977) B3315977
theorem B3316571 : Blo 1472556 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B1473439 : Blo 1472556 1473439 := bstep (se 1 (by rfl) ⟨1105079, by rfl⟩ : syracuseStep 1473439 = 2210159) B2210159
theorem B2210795 : Blo 1472556 2210795 := bstep (se 1 (by rfl) ⟨1658096, by rfl⟩ : syracuseStep 2210795 = 3316193) B3316193
theorem B8395757 : Blo 1472556 8395757 := bstep (se 3 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 8395757 = 3148409) B3148409
theorem B1473583 : Blo 1472556 1473583 := bstep (se 1 (by rfl) ⟨1105187, by rfl⟩ : syracuseStep 1473583 = 2210375) B2210375
theorem B1473607 : Blo 1472556 1473607 := bstep (se 1 (by rfl) ⟨1105205, by rfl⟩ : syracuseStep 1473607 = 2210411) B2210411
theorem B4717693 : Blo 1472556 4717693 := bstep (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) B1769135
theorem B68074667 : Blo 1472556 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B2210999 : Blo 1472556 2210999 := bstep (se 1 (by rfl) ⟨1658249, by rfl⟩ : syracuseStep 2210999 = 3316499) B3316499
theorem B20176075 : Blo 1472556 20176075 := bstep (se 1 (by rfl) ⟨15132056, by rfl⟩ : syracuseStep 20176075 = 30264113) B30264113
theorem B1473759 : Blo 1472556 1473759 := bstep (se 1 (by rfl) ⟨1105319, by rfl⟩ : syracuseStep 1473759 = 2210639) B2210639
theorem B4971887 : Blo 1472556 4971887 := bstep (se 1 (by rfl) ⟨3728915, by rfl⟩ : syracuseStep 4971887 = 7457831) B7457831
theorem B11345291 : Blo 1472556 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B2211239 : Blo 1472556 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B8388035 : Blo 1472556 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B1474023 : Blo 1472556 1474023 := bstep (se 1 (by rfl) ⟨1105517, by rfl⟩ : syracuseStep 1474023 = 2211035) B2211035
theorem B16154093 : Blo 1472556 16154093 := bstep (se 3 (by rfl) ⟨3028892, by rfl⟩ : syracuseStep 16154093 = 6057785) B6057785
theorem B2211323 : Blo 1472556 2211323 := bstep (se 1 (by rfl) ⟨1658492, by rfl⟩ : syracuseStep 2211323 = 3316985) B3316985
theorem B3317327 : Blo 1472556 3317327 := bstep (se 1 (by rfl) ⟨2487995, by rfl⟩ : syracuseStep 3317327 = 4975991) B4975991
theorem B1474139 : Blo 1472556 1474139 := bstep (se 1 (by rfl) ⟨1105604, by rfl⟩ : syracuseStep 1474139 = 2211209) B2211209
theorem B2211419 : Blo 1472556 2211419 := bstep (se 1 (by rfl) ⟨1658564, by rfl⟩ : syracuseStep 2211419 = 3317129) B3317129
theorem B2211503 : Blo 1472556 2211503 := bstep (se 1 (by rfl) ⟨1658627, by rfl⟩ : syracuseStep 2211503 = 3317255) B3317255
theorem B12590801 : Blo 1472556 12590801 := bstep (se 2 (by rfl) ⟨4721550, by rfl⟩ : syracuseStep 12590801 = 9443101) B9443101
theorem B4972265 : Blo 1472556 4972265 := bstep (se 2 (by rfl) ⟨1864599, by rfl⟩ : syracuseStep 4972265 = 3729199) B3729199
theorem B8396531 : Blo 1472556 8396531 := bstep (se 1 (by rfl) ⟨6297398, by rfl⟩ : syracuseStep 8396531 = 12594797) B12594797
theorem B2211623 : Blo 1472556 2211623 := bstep (se 1 (by rfl) ⟨1658717, by rfl⟩ : syracuseStep 2211623 = 3317435) B3317435
theorem B4194119 : Blo 1472556 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B1474375 : Blo 1472556 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B34004843 : Blo 1472556 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B2211707 : Blo 1472556 2211707 := bstep (se 1 (by rfl) ⟨1658780, by rfl⟩ : syracuseStep 2211707 = 3317561) B3317561
theorem B14958541 : Blo 1472556 14958541 := bstep (se 3 (by rfl) ⟨2804726, by rfl⟩ : syracuseStep 14958541 = 5609453) B5609453
theorem B1474527 : Blo 1472556 1474527 := bstep (se 1 (by rfl) ⟨1105895, by rfl⟩ : syracuseStep 1474527 = 2211791) B2211791
theorem B18890759 : Blo 1472556 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B4972967 : Blo 1472556 4972967 := bstep (se 1 (by rfl) ⟨3729725, by rfl⟩ : syracuseStep 4972967 = 7459451) B7459451
theorem B28328453 : Blo 1472556 28328453 := bstep (se 4 (by rfl) ⟨2655792, by rfl⟩ : syracuseStep 28328453 = 5311585) B5311585
theorem B7455239 : Blo 1472556 7455239 := bstep (se 1 (by rfl) ⟨5591429, by rfl⟩ : syracuseStep 7455239 = 11182859) B11182859
theorem B14156383 : Blo 1472556 14156383 := bstep (se 1 (by rfl) ⟨10617287, by rfl⟩ : syracuseStep 14156383 = 21234575) B21234575
theorem B1573543 : Blo 1472556 1573543 := bstep (se 1 (by rfl) ⟨1180157, by rfl⟩ : syracuseStep 1573543 = 2360315) B2360315
theorem B3589175 : Blo 1472556 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B6817385 : Blo 1472556 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B8963693 : Blo 1472556 8963693 := bstep (se 3 (by rfl) ⟨1680692, by rfl⟩ : syracuseStep 8963693 = 3361385) B3361385
theorem B10618559 : Blo 1472556 10618559 := bstep (se 1 (by rfl) ⟨7963919, by rfl⟩ : syracuseStep 10618559 = 15927839) B15927839
theorem B38823623 : Blo 1472556 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B11192093 : Blo 1472556 11192093 := bstep (se 3 (by rfl) ⟨2098517, by rfl⟩ : syracuseStep 11192093 = 4197035) B4197035
theorem B64563077 : Blo 1472556 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B5597171 : Blo 1472556 5597171 := bstep (se 1 (by rfl) ⟨4197878, by rfl⟩ : syracuseStep 5597171 = 8395757) B8395757
theorem B1656859 : Blo 1472556 1656859 := bstep (se 1 (by rfl) ⟨1242644, by rfl⟩ : syracuseStep 1656859 = 2485289) B2485289
theorem B3541087 : Blo 1472556 3541087 := bstep (se 1 (by rfl) ⟨2655815, by rfl⟩ : syracuseStep 3541087 = 5311631) B5311631
theorem B11184317 : Blo 1472556 11184317 := bstep (se 3 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 11184317 = 4194119) B4194119
theorem B7563527 : Blo 1472556 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B4311403 : Blo 1472556 4311403 := bstep (se 1 (by rfl) ⟨3233552, by rfl⟩ : syracuseStep 4311403 = 6467105) B6467105
theorem B5597687 : Blo 1472556 5597687 := bstep (se 1 (by rfl) ⟨4198265, by rfl⟩ : syracuseStep 5597687 = 8396531) B8396531
theorem B11946527 : Blo 1472556 11946527 := bstep (se 1 (by rfl) ⟨8959895, by rfl⟩ : syracuseStep 11946527 = 17919791) B17919791
theorem B22669895 : Blo 1472556 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B110537393 : Blo 1472556 110537393 := bstep (se 2 (by rfl) ⟨41451522, by rfl⟩ : syracuseStep 110537393 = 82903045) B82903045
theorem B14166839 : Blo 1472556 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B2485417 : Blo 1472556 2485417 := bstep (se 2 (by rfl) ⟨932031, by rfl⟩ : syracuseStep 2485417 = 1864063) B1864063
theorem B4787387 : Blo 1472556 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B2485559 : Blo 1472556 2485559 := bstep (se 1 (by rfl) ⟨1864169, by rfl⟩ : syracuseStep 2485559 = 3728339) B3728339
theorem B6294905 : Blo 1472556 6294905 := bstep (se 2 (by rfl) ⟨2360589, by rfl⟩ : syracuseStep 6294905 = 4721179) B4721179
theorem B14159231 : Blo 1472556 14159231 := bstep (se 1 (by rfl) ⟨10619423, by rfl⟩ : syracuseStep 14159231 = 21238847) B21238847
theorem B5598659 : Blo 1472556 5598659 := bstep (se 1 (by rfl) ⟨4198994, by rfl⟩ : syracuseStep 5598659 = 8397989) B8397989
theorem B1658335 : Blo 1472556 1658335 := bstep (se 1 (by rfl) ⟨1243751, by rfl⟩ : syracuseStep 1658335 = 2487503) B2487503
theorem B42470993 : Blo 1472556 42470993 := bstep (se 2 (by rfl) ⟨15926622, by rfl⟩ : syracuseStep 42470993 = 31853245) B31853245
theorem B7769843 : Blo 1472556 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B2486011 : Blo 1472556 2486011 := bstep (se 1 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 2486011 = 3729017) B3729017
theorem B183873397 : Blo 1472556 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B2486153 : Blo 1472556 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B43077581 : Blo 1472556 43077581 := bstep (se 3 (by rfl) ⟨8077046, by rfl⟩ : syracuseStep 43077581 = 16154093) B16154093
theorem B7458803 : Blo 1472556 7458803 := bstep (se 1 (by rfl) ⟨5594102, by rfl⟩ : syracuseStep 7458803 = 11188205) B11188205
theorem B1658875 : Blo 1472556 1658875 := bstep (se 1 (by rfl) ⟨1244156, by rfl⟩ : syracuseStep 1658875 = 2488313) B2488313
theorem B3985463 : Blo 1472556 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B3313727 : Blo 1472556 3313727 := bstep (se 1 (by rfl) ⟨2485295, by rfl⟩ : syracuseStep 3313727 = 4970591) B4970591
theorem B45961339 : Blo 1472556 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B3313961 : Blo 1472556 3313961 := bstep (se 2 (by rfl) ⟨1242735, by rfl⟩ : syracuseStep 3313961 = 2485471) B2485471
theorem B7967119 : Blo 1472556 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B3314231 : Blo 1472556 3314231 := bstep (se 1 (by rfl) ⟨2485673, by rfl⟩ : syracuseStep 3314231 = 4971347) B4971347
theorem B3314537 : Blo 1472556 3314537 := bstep (se 2 (by rfl) ⟨1242951, by rfl⟩ : syracuseStep 3314537 = 2485903) B2485903
theorem B51049349 : Blo 1472556 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B3314591 : Blo 1472556 3314591 := bstep (se 1 (by rfl) ⟨2485943, by rfl⟩ : syracuseStep 3314591 = 4971887) B4971887
theorem B5592023 : Blo 1472556 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B2208839 : Blo 1472556 2208839 := bstep (se 1 (by rfl) ⟨1656629, by rfl⟩ : syracuseStep 2208839 = 3313259) B3313259
theorem B3781703 : Blo 1472556 3781703 := bstep (se 1 (by rfl) ⟨2836277, by rfl⟩ : syracuseStep 3781703 = 5672555) B5672555
theorem B8393867 : Blo 1472556 8393867 := bstep (se 1 (by rfl) ⟨6295400, by rfl⟩ : syracuseStep 8393867 = 12590801) B12590801
theorem B3314843 : Blo 1472556 3314843 := bstep (se 1 (by rfl) ⟨2486132, by rfl⟩ : syracuseStep 3314843 = 4972265) B4972265
theorem B2209019 : Blo 1472556 2209019 := bstep (se 1 (by rfl) ⟨1656764, by rfl⟩ : syracuseStep 2209019 = 3313529) B3313529
theorem B14152967 : Blo 1472556 14152967 := bstep (se 1 (by rfl) ⟨10614725, by rfl⟩ : syracuseStep 14152967 = 21229451) B21229451
theorem B19944721 : Blo 1472556 19944721 := bstep (se 2 (by rfl) ⟨7479270, by rfl⟩ : syracuseStep 19944721 = 14958541) B14958541
theorem B2487719 : Blo 1472556 2487719 := bstep (se 1 (by rfl) ⟨1865789, by rfl⟩ : syracuseStep 2487719 = 3731579) B3731579
theorem B7460423 : Blo 1472556 7460423 := bstep (se 1 (by rfl) ⟨5595317, by rfl⟩ : syracuseStep 7460423 = 11190635) B11190635
theorem B12760685 : Blo 1472556 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B4970105 : Blo 1472556 4970105 := bstep (se 2 (by rfl) ⟨1863789, by rfl⟩ : syracuseStep 4970105 = 3727579) B3727579
theorem B3315419 : Blo 1472556 3315419 := bstep (se 1 (by rfl) ⟨2486564, by rfl⟩ : syracuseStep 3315419 = 4973129) B4973129
theorem B5592827 : Blo 1472556 5592827 := bstep (se 1 (by rfl) ⟨4194620, by rfl⟩ : syracuseStep 5592827 = 8389241) B8389241
theorem B3315527 : Blo 1472556 3315527 := bstep (se 1 (by rfl) ⟨2486645, by rfl⟩ : syracuseStep 3315527 = 4973291) B4973291
theorem B4970429 : Blo 1472556 4970429 := bstep (se 3 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 4970429 = 1863911) B1863911
theorem B11950031 : Blo 1472556 11950031 := bstep (se 1 (by rfl) ⟨8962523, by rfl⟩ : syracuseStep 11950031 = 17925047) B17925047
theorem B25532441 : Blo 1472556 25532441 := bstep (se 2 (by rfl) ⟨9574665, by rfl⟩ : syracuseStep 25532441 = 19149331) B19149331
theorem B1472583 : Blo 1472556 1472583 := bstep (se 1 (by rfl) ⟨1104437, by rfl⟩ : syracuseStep 1472583 = 2208875) B2208875
theorem B1865911 : Blo 1472556 1865911 := bstep (se 1 (by rfl) ⟨1399433, by rfl⟩ : syracuseStep 1865911 = 2798867) B2798867
theorem B1472743 : Blo 1472556 1472743 := bstep (se 1 (by rfl) ⟨1104557, by rfl⟩ : syracuseStep 1472743 = 2209115) B2209115
theorem B1472927 : Blo 1472556 1472927 := bstep (se 1 (by rfl) ⟨1104695, by rfl⟩ : syracuseStep 1472927 = 2209391) B2209391
theorem B1472975 : Blo 1472556 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B2210255 : Blo 1472556 2210255 := bstep (se 1 (by rfl) ⟨1657691, by rfl⟩ : syracuseStep 2210255 = 3315383) B3315383
theorem B11188691 : Blo 1472556 11188691 := bstep (se 1 (by rfl) ⟨8391518, by rfl⟩ : syracuseStep 11188691 = 16783037) B16783037
theorem B1472999 : Blo 1472556 1472999 := bstep (se 1 (by rfl) ⟨1104749, by rfl⟩ : syracuseStep 1472999 = 2209499) B2209499
theorem B2210345 : Blo 1472556 2210345 := bstep (se 2 (by rfl) ⟨828879, by rfl⟩ : syracuseStep 2210345 = 1657759) B1657759
theorem B1473115 : Blo 1472556 1473115 := bstep (se 1 (by rfl) ⟨1104836, by rfl⟩ : syracuseStep 1473115 = 2209673) B2209673
theorem B1473183 : Blo 1472556 1473183 := bstep (se 1 (by rfl) ⟨1104887, by rfl⟩ : syracuseStep 1473183 = 2209775) B2209775
theorem B2210537 : Blo 1472556 2210537 := bstep (se 2 (by rfl) ⟨828951, by rfl⟩ : syracuseStep 2210537 = 1657903) B1657903
theorem B3316535 : Blo 1472556 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B1473351 : Blo 1472556 1473351 := bstep (se 1 (by rfl) ⟨1105013, by rfl⟩ : syracuseStep 1473351 = 2210027) B2210027
theorem B6290257 : Blo 1472556 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B5593967 : Blo 1472556 5593967 := bstep (se 1 (by rfl) ⟨4195475, by rfl⟩ : syracuseStep 5593967 = 8390951) B8390951
theorem B1473391 : Blo 1472556 1473391 := bstep (se 1 (by rfl) ⟨1105043, by rfl⟩ : syracuseStep 1473391 = 2210087) B2210087
theorem B1473447 : Blo 1472556 1473447 := bstep (se 1 (by rfl) ⟨1105085, by rfl⟩ : syracuseStep 1473447 = 2210171) B2210171
theorem B26901433 : Blo 1472556 26901433 := bstep (se 2 (by rfl) ⟨10088037, by rfl⟩ : syracuseStep 26901433 = 20176075) B20176075
theorem B3316715 : Blo 1472556 3316715 := bstep (se 1 (by rfl) ⟨2487536, by rfl⟩ : syracuseStep 3316715 = 4975073) B4975073
theorem B1473627 : Blo 1472556 1473627 := bstep (se 1 (by rfl) ⟨1105220, by rfl⟩ : syracuseStep 1473627 = 2210441) B2210441
theorem B4971617 : Blo 1472556 4971617 := bstep (se 2 (by rfl) ⟨1864356, by rfl⟩ : syracuseStep 4971617 = 3728713) B3728713
theorem B2210921 : Blo 1472556 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B5594255 : Blo 1472556 5594255 := bstep (se 1 (by rfl) ⟨4195691, by rfl⟩ : syracuseStep 5594255 = 8391383) B8391383
theorem B1473743 : Blo 1472556 1473743 := bstep (se 1 (by rfl) ⟨1105307, by rfl⟩ : syracuseStep 1473743 = 2210615) B2210615
theorem B1473767 : Blo 1472556 1473767 := bstep (se 1 (by rfl) ⟨1105325, by rfl⟩ : syracuseStep 1473767 = 2210651) B2210651
theorem B2211047 : Blo 1472556 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B45358379 : Blo 1472556 45358379 := bstep (se 1 (by rfl) ⟨34018784, by rfl⟩ : syracuseStep 45358379 = 68037569) B68037569
theorem B8396075 : Blo 1472556 8396075 := bstep (se 1 (by rfl) ⟨6297056, by rfl⟩ : syracuseStep 8396075 = 12594113) B12594113
theorem B1473863 : Blo 1472556 1473863 := bstep (se 1 (by rfl) ⟨1105397, by rfl⟩ : syracuseStep 1473863 = 2210795) B2210795
theorem B45383111 : Blo 1472556 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B1473999 : Blo 1472556 1473999 := bstep (se 1 (by rfl) ⟨1105499, by rfl⟩ : syracuseStep 1473999 = 2210999) B2210999
theorem B4251113 : Blo 1472556 4251113 := bstep (se 2 (by rfl) ⟨1594167, by rfl⟩ : syracuseStep 4251113 = 3188335) B3188335
theorem B1474159 : Blo 1472556 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B4972157 : Blo 1472556 4972157 := bstep (se 3 (by rfl) ⟨932279, by rfl⟩ : syracuseStep 4972157 = 1864559) B1864559
theorem B1474215 : Blo 1472556 1474215 := bstep (se 1 (by rfl) ⟨1105661, by rfl⟩ : syracuseStep 1474215 = 2211323) B2211323
theorem B2211551 : Blo 1472556 2211551 := bstep (se 1 (by rfl) ⟨1658663, by rfl⟩ : syracuseStep 2211551 = 3317327) B3317327
theorem B1474279 : Blo 1472556 1474279 := bstep (se 1 (by rfl) ⟨1105709, by rfl⟩ : syracuseStep 1474279 = 2211419) B2211419
theorem B2211593 : Blo 1472556 2211593 := bstep (se 2 (by rfl) ⟨829347, by rfl⟩ : syracuseStep 2211593 = 1658695) B1658695
theorem B4972319 : Blo 1472556 4972319 := bstep (se 1 (by rfl) ⟨3729239, by rfl⟩ : syracuseStep 4972319 = 7458479) B7458479
theorem B1474335 : Blo 1472556 1474335 := bstep (se 1 (by rfl) ⟨1105751, by rfl⟩ : syracuseStep 1474335 = 2211503) B2211503
theorem B1474415 : Blo 1472556 1474415 := bstep (se 1 (by rfl) ⟨1105811, by rfl⟩ : syracuseStep 1474415 = 2211623) B2211623
theorem B3317615 : Blo 1472556 3317615 := bstep (se 1 (by rfl) ⟨2488211, by rfl⟩ : syracuseStep 3317615 = 4976423) B4976423
theorem B4972427 : Blo 1472556 4972427 := bstep (se 1 (by rfl) ⟨3729320, by rfl⟩ : syracuseStep 4972427 = 7458641) B7458641
theorem B1474471 : Blo 1472556 1474471 := bstep (se 1 (by rfl) ⟨1105853, by rfl⟩ : syracuseStep 1474471 = 2211707) B2211707
theorem B3728015 : Blo 1472556 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B2392783 : Blo 1472556 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B5595911 : Blo 1472556 5595911 := bstep (se 1 (by rfl) ⟨4196933, by rfl⟩ : syracuseStep 5595911 = 8393867) B8393867
theorem B18875177 : Blo 1472556 18875177 := bstep (se 2 (by rfl) ⟨7078191, by rfl⟩ : syracuseStep 18875177 = 14156383) B14156383
theorem B2098057 : Blo 1472556 2098057 := bstep (se 2 (by rfl) ⟨786771, by rfl⟩ : syracuseStep 2098057 = 1573543) B1573543
theorem B4973615 : Blo 1472556 4973615 := bstep (se 1 (by rfl) ⟨3730211, by rfl⟩ : syracuseStep 4973615 = 7460423) B7460423
theorem B7079039 : Blo 1472556 7079039 := bstep (se 1 (by rfl) ⟨5309279, by rfl⟩ : syracuseStep 7079039 = 10618559) B10618559
theorem B3728551 : Blo 1472556 3728551 := bstep (se 1 (by rfl) ⟨2796413, by rfl⟩ : syracuseStep 3728551 = 5592827) B5592827
theorem B43042051 : Blo 1472556 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B7456211 : Blo 1472556 7456211 := bstep (se 1 (by rfl) ⟨5592158, by rfl⟩ : syracuseStep 7456211 = 11184317) B11184317
theorem B7964351 : Blo 1472556 7964351 := bstep (se 1 (by rfl) ⟨5973263, by rfl⟩ : syracuseStep 7964351 = 11946527) B11946527
theorem B26592961 : Blo 1472556 26592961 := bstep (se 2 (by rfl) ⟨9972360, by rfl⟩ : syracuseStep 26592961 = 19944721) B19944721
theorem B294766381 : Blo 1472556 294766381 := bstep (se 3 (by rfl) ⟨55268696, by rfl⟩ : syracuseStep 294766381 = 110537393) B110537393
theorem B3729311 : Blo 1472556 3729311 := bstep (se 1 (by rfl) ⟨2796983, by rfl⟩ : syracuseStep 3729311 = 5593967) B5593967
theorem B3729503 : Blo 1472556 3729503 := bstep (se 1 (by rfl) ⟨2797127, by rfl⟩ : syracuseStep 3729503 = 5594255) B5594255
theorem B30238919 : Blo 1472556 30238919 := bstep (se 1 (by rfl) ⟨22679189, by rfl⟩ : syracuseStep 30238919 = 45358379) B45358379
theorem B5597383 : Blo 1472556 5597383 := bstep (se 1 (by rfl) ⟨4198037, by rfl⟩ : syracuseStep 5597383 = 8396075) B8396075
theorem B1657039 : Blo 1472556 1657039 := bstep (se 1 (by rfl) ⟨1242779, by rfl⟩ : syracuseStep 1657039 = 2485559) B2485559
theorem B4196603 : Blo 1472556 4196603 := bstep (se 1 (by rfl) ⟨3147452, by rfl⟩ : syracuseStep 4196603 = 6294905) B6294905
theorem B9439487 : Blo 1472556 9439487 := bstep (se 1 (by rfl) ⟨7079615, by rfl⟩ : syracuseStep 9439487 = 14159231) B14159231
theorem B30255407 : Blo 1472556 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B28313995 : Blo 1472556 28313995 := bstep (se 1 (by rfl) ⟨21235496, by rfl⟩ : syracuseStep 28313995 = 42470993) B42470993
theorem B245164529 : Blo 1472556 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B5179895 : Blo 1472556 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B1657435 : Blo 1472556 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B12593839 : Blo 1472556 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B2656975 : Blo 1472556 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B4721449 : Blo 1472556 4721449 := bstep (se 2 (by rfl) ⟨1770543, by rfl⟩ : syracuseStep 4721449 = 3541087) B3541087
theorem B18885635 : Blo 1472556 18885635 := bstep (se 1 (by rfl) ⟨14164226, by rfl⟩ : syracuseStep 18885635 = 28328453) B28328453
theorem B34032899 : Blo 1472556 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B2211833 : Blo 1472556 2211833 := bstep (se 2 (by rfl) ⟨829437, by rfl⟩ : syracuseStep 2211833 = 1658875) B1658875
theorem B1658479 : Blo 1472556 1658479 := bstep (se 1 (by rfl) ⟨1243859, by rfl⟩ : syracuseStep 1658479 = 2487719) B2487719
theorem B8507123 : Blo 1472556 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B5975795 : Blo 1472556 5975795 := bstep (se 1 (by rfl) ⟨4481846, by rfl⟩ : syracuseStep 5975795 = 8963693) B8963693
theorem B3313403 : Blo 1472556 3313403 := bstep (se 1 (by rfl) ⟨2485052, by rfl⟩ : syracuseStep 3313403 = 4970105) B4970105
theorem B25882415 : Blo 1472556 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B35868577 : Blo 1472556 35868577 := bstep (se 2 (by rfl) ⟨13450716, by rfl⟩ : syracuseStep 35868577 = 26901433) B26901433
theorem B3313619 : Blo 1472556 3313619 := bstep (se 1 (by rfl) ⟨2485214, by rfl⟩ : syracuseStep 3313619 = 4970429) B4970429
theorem B7966687 : Blo 1472556 7966687 := bstep (se 1 (by rfl) ⟨5975015, by rfl⟩ : syracuseStep 7966687 = 11950031) B11950031
theorem B3731447 : Blo 1472556 3731447 := bstep (se 1 (by rfl) ⟨2798585, by rfl⟩ : syracuseStep 3731447 = 5597171) B5597171
theorem B5042351 : Blo 1472556 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B3313889 : Blo 1472556 3313889 := bstep (se 2 (by rfl) ⟨1242708, by rfl⟩ : syracuseStep 3313889 = 2485417) B2485417
theorem B7459127 : Blo 1472556 7459127 := bstep (se 1 (by rfl) ⟨5594345, by rfl⟩ : syracuseStep 7459127 = 11188691) B11188691
theorem B3731791 : Blo 1472556 3731791 := bstep (se 1 (by rfl) ⟨2798843, by rfl⟩ : syracuseStep 3731791 = 5597687) B5597687
theorem B3314411 : Blo 1472556 3314411 := bstep (se 1 (by rfl) ⟨2485808, by rfl⟩ : syracuseStep 3314411 = 4971617) B4971617
theorem B3191591 : Blo 1472556 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B37778237 : Blo 1472556 37778237 := bstep (se 3 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 37778237 = 14166839) B14166839
theorem B91976597 : Blo 1472556 91976597 := bstep (se 6 (by rfl) ⟨2155701, by rfl⟩ : syracuseStep 91976597 = 4311403) B4311403
theorem B3732439 : Blo 1472556 3732439 := bstep (se 1 (by rfl) ⟨2799329, by rfl⟩ : syracuseStep 3732439 = 5598659) B5598659
theorem B3314681 : Blo 1472556 3314681 := bstep (se 2 (by rfl) ⟨1243005, by rfl⟩ : syracuseStep 3314681 = 2486011) B2486011
theorem B3314771 : Blo 1472556 3314771 := bstep (se 1 (by rfl) ⟨2486078, by rfl⟩ : syracuseStep 3314771 = 4972157) B4972157
theorem B3314879 : Blo 1472556 3314879 := bstep (se 1 (by rfl) ⟨2486159, by rfl⟩ : syracuseStep 3314879 = 4972319) B4972319
theorem B3314951 : Blo 1472556 3314951 := bstep (se 1 (by rfl) ⟨2486213, by rfl⟩ : syracuseStep 3314951 = 4972427) B4972427
theorem B28718387 : Blo 1472556 28718387 := bstep (se 1 (by rfl) ⟨21538790, by rfl⟩ : syracuseStep 28718387 = 43077581) B43077581
theorem B2209145 : Blo 1472556 2209145 := bstep (se 2 (by rfl) ⟨828429, by rfl⟩ : syracuseStep 2209145 = 1656859) B1656859
theorem B2209151 : Blo 1472556 2209151 := bstep (se 1 (by rfl) ⟨1656863, by rfl⟩ : syracuseStep 2209151 = 3313727) B3313727
theorem B61281785 : Blo 1472556 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B2209307 : Blo 1472556 2209307 := bstep (se 1 (by rfl) ⟨1656980, by rfl⟩ : syracuseStep 2209307 = 3313961) B3313961
theorem B2487881 : Blo 1472556 2487881 := bstep (se 2 (by rfl) ⟨932955, by rfl⟩ : syracuseStep 2487881 = 1865911) B1865911
theorem B3315311 : Blo 1472556 3315311 := bstep (se 1 (by rfl) ⟨2486483, by rfl⟩ : syracuseStep 3315311 = 4972967) B4972967
theorem B4970159 : Blo 1472556 4970159 := bstep (se 1 (by rfl) ⟨3727619, by rfl⟩ : syracuseStep 4970159 = 7455239) B7455239
theorem B2209487 : Blo 1472556 2209487 := bstep (se 1 (by rfl) ⟨1657115, by rfl⟩ : syracuseStep 2209487 = 3314231) B3314231
theorem B10622825 : Blo 1472556 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B2209691 : Blo 1472556 2209691 := bstep (se 1 (by rfl) ⟨1657268, by rfl⟩ : syracuseStep 2209691 = 3314537) B3314537
theorem B2209727 : Blo 1472556 2209727 := bstep (se 1 (by rfl) ⟨1657295, by rfl⟩ : syracuseStep 2209727 = 3314591) B3314591
theorem B1472559 : Blo 1472556 1472559 := bstep (se 1 (by rfl) ⟨1104419, by rfl⟩ : syracuseStep 1472559 = 2208839) B2208839
theorem B2521135 : Blo 1472556 2521135 := bstep (se 1 (by rfl) ⟨1890851, by rfl⟩ : syracuseStep 2521135 = 3781703) B3781703
theorem B2209895 : Blo 1472556 2209895 := bstep (se 1 (by rfl) ⟨1657421, by rfl⟩ : syracuseStep 2209895 = 3314843) B3314843
theorem B1472679 : Blo 1472556 1472679 := bstep (se 1 (by rfl) ⟨1104509, by rfl⟩ : syracuseStep 1472679 = 2209019) B2209019
theorem B9435311 : Blo 1472556 9435311 := bstep (se 1 (by rfl) ⟨7076483, by rfl⟩ : syracuseStep 9435311 = 14152967) B14152967
theorem B4544923 : Blo 1472556 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B8387009 : Blo 1472556 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B2210279 : Blo 1472556 2210279 := bstep (se 1 (by rfl) ⟨1657709, by rfl⟩ : syracuseStep 2210279 = 3315419) B3315419
theorem B7461395 : Blo 1472556 7461395 := bstep (se 1 (by rfl) ⟨5596046, by rfl⟩ : syracuseStep 7461395 = 11192093) B11192093
theorem B2210351 : Blo 1472556 2210351 := bstep (se 1 (by rfl) ⟨1657763, by rfl⟩ : syracuseStep 2210351 = 3315527) B3315527
theorem B17021627 : Blo 1472556 17021627 := bstep (se 1 (by rfl) ⟨12766220, by rfl⟩ : syracuseStep 17021627 = 25532441) B25532441
theorem B1473503 : Blo 1472556 1473503 := bstep (se 1 (by rfl) ⟨1105127, by rfl⟩ : syracuseStep 1473503 = 2210255) B2210255
theorem B1473563 : Blo 1472556 1473563 := bstep (se 1 (by rfl) ⟨1105172, by rfl⟩ : syracuseStep 1473563 = 2210345) B2210345
theorem B15113263 : Blo 1472556 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B1473691 : Blo 1472556 1473691 := bstep (se 1 (by rfl) ⟨1105268, by rfl⟩ : syracuseStep 1473691 = 2210537) B2210537
theorem B2211023 : Blo 1472556 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B2211113 : Blo 1472556 2211113 := bstep (se 2 (by rfl) ⟨829167, by rfl⟩ : syracuseStep 2211113 = 1658335) B1658335
theorem B2211143 : Blo 1472556 2211143 := bstep (se 1 (by rfl) ⟨1658357, by rfl⟩ : syracuseStep 2211143 = 3316715) B3316715
theorem B1473947 : Blo 1472556 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1474031 : Blo 1472556 1474031 := bstep (se 1 (by rfl) ⟨1105523, by rfl⟩ : syracuseStep 1474031 = 2211047) B2211047
theorem B2834075 : Blo 1472556 2834075 := bstep (se 1 (by rfl) ⟨2125556, by rfl⟩ : syracuseStep 2834075 = 4251113) B4251113
theorem B4972535 : Blo 1472556 4972535 := bstep (se 1 (by rfl) ⟨3729401, by rfl⟩ : syracuseStep 4972535 = 7458803) B7458803
theorem B1474367 : Blo 1472556 1474367 := bstep (se 1 (by rfl) ⟨1105775, by rfl⟩ : syracuseStep 1474367 = 2211551) B2211551
theorem B1474395 : Blo 1472556 1474395 := bstep (se 1 (by rfl) ⟨1105796, by rfl⟩ : syracuseStep 1474395 = 2211593) B2211593
theorem B2211743 : Blo 1472556 2211743 := bstep (se 1 (by rfl) ⟨1658807, by rfl⟩ : syracuseStep 2211743 = 3317615) B3317615
theorem B4972751 : Blo 1472556 4972751 := bstep (se 1 (by rfl) ⟨3729563, by rfl⟩ : syracuseStep 4972751 = 7459127) B7459127
theorem B7463177 : Blo 1472556 7463177 := bstep (se 2 (by rfl) ⟨2798691, by rfl⟩ : syracuseStep 7463177 = 5597383) B5597383
theorem B12583451 : Blo 1472556 12583451 := bstep (se 1 (by rfl) ⟨9437588, by rfl⟩ : syracuseStep 12583451 = 18875177) B18875177
theorem B61317731 : Blo 1472556 61317731 := bstep (se 1 (by rfl) ⟨45988298, by rfl⟩ : syracuseStep 61317731 = 91976597) B91976597
theorem B4719359 : Blo 1472556 4719359 := bstep (se 1 (by rfl) ⟨3539519, by rfl⟩ : syracuseStep 4719359 = 7079039) B7079039
theorem B19145591 : Blo 1472556 19145591 := bstep (se 1 (by rfl) ⟨14359193, by rfl⟩ : syracuseStep 19145591 = 28718387) B28718387
theorem B5309567 : Blo 1472556 5309567 := bstep (se 1 (by rfl) ⟨3982175, by rfl⟩ : syracuseStep 5309567 = 7964351) B7964351
theorem B6292991 : Blo 1472556 6292991 := bstep (se 1 (by rfl) ⟨4719743, by rfl⟩ : syracuseStep 6292991 = 9439487) B9439487
theorem B20170271 : Blo 1472556 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B51046037 : Blo 1472556 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B4974263 : Blo 1472556 4974263 := bstep (se 1 (by rfl) ⟨3730697, by rfl⟩ : syracuseStep 4974263 = 7461395) B7461395
theorem B11347751 : Blo 1472556 11347751 := bstep (se 1 (by rfl) ⟨8510813, by rfl⟩ : syracuseStep 11347751 = 17021627) B17021627
theorem B15935453 : Blo 1472556 15935453 := bstep (se 3 (by rfl) ⟨2987897, by rfl⟩ : syracuseStep 15935453 = 5975795) B5975795
theorem B35457281 : Blo 1472556 35457281 := bstep (se 2 (by rfl) ⟨13296480, by rfl⟩ : syracuseStep 35457281 = 26592961) B26592961
theorem B393021841 : Blo 1472556 393021841 := bstep (se 2 (by rfl) ⟨147383190, by rfl⟩ : syracuseStep 393021841 = 294766381) B294766381
theorem B5671415 : Blo 1472556 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B17254943 : Blo 1472556 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B3361513 : Blo 1472556 3361513 := bstep (se 2 (by rfl) ⟨1260567, by rfl⟩ : syracuseStep 3361513 = 2521135) B2521135
theorem B2485343 : Blo 1472556 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B4975721 : Blo 1472556 4975721 := bstep (se 2 (by rfl) ⟨1865895, by rfl⟩ : syracuseStep 4975721 = 3731791) B3731791
theorem B13446269 : Blo 1472556 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B3730607 : Blo 1472556 3730607 := bstep (se 1 (by rfl) ⟨2797955, by rfl⟩ : syracuseStep 3730607 = 5595911) B5595911
theorem B37751993 : Blo 1472556 37751993 := bstep (se 2 (by rfl) ⟨14156997, by rfl⟩ : syracuseStep 37751993 = 28313995) B28313995
theorem B25185491 : Blo 1472556 25185491 := bstep (se 1 (by rfl) ⟨18889118, by rfl⟩ : syracuseStep 25185491 = 37778237) B37778237
theorem B3542633 : Blo 1472556 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B1658587 : Blo 1472556 1658587 := bstep (se 1 (by rfl) ⟨1243940, by rfl⟩ : syracuseStep 1658587 = 2487881) B2487881
theorem B6295265 : Blo 1472556 6295265 := bstep (se 2 (by rfl) ⟨2360724, by rfl⟩ : syracuseStep 6295265 = 4721449) B4721449
theorem B3313439 : Blo 1472556 3313439 := bstep (se 1 (by rfl) ⟨2485079, by rfl⟩ : syracuseStep 3313439 = 4970159) B4970159
theorem B2797409 : Blo 1472556 2797409 := bstep (se 2 (by rfl) ⟨1049028, by rfl⟩ : syracuseStep 2797409 = 2098057) B2098057
theorem B7081883 : Blo 1472556 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B2486207 : Blo 1472556 2486207 := bstep (se 1 (by rfl) ⟨1864655, by rfl⟩ : syracuseStep 2486207 = 3729311) B3729311
theorem B4976585 : Blo 1472556 4976585 := bstep (se 2 (by rfl) ⟨1866219, by rfl⟩ : syracuseStep 4976585 = 3732439) B3732439
theorem B163418093 : Blo 1472556 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B2486335 : Blo 1472556 2486335 := bstep (se 1 (by rfl) ⟨1864751, by rfl⟩ : syracuseStep 2486335 = 3729503) B3729503
theorem B2797735 : Blo 1472556 2797735 := bstep (se 1 (by rfl) ⟨2098301, by rfl⟩ : syracuseStep 2797735 = 4196603) B4196603
theorem B5591339 : Blo 1472556 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B163443019 : Blo 1472556 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B3453263 : Blo 1472556 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B57389401 : Blo 1472556 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B7557533 : Blo 1472556 7557533 := bstep (se 3 (by rfl) ⟨1417037, by rfl⟩ : syracuseStep 7557533 = 2834075) B2834075
theorem B22688599 : Blo 1472556 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B1474555 : Blo 1472556 1474555 := bstep (se 1 (by rfl) ⟨1105916, by rfl⟩ : syracuseStep 1474555 = 2211833) B2211833
theorem B2208935 : Blo 1472556 2208935 := bstep (se 1 (by rfl) ⟨1656701, by rfl⟩ : syracuseStep 2208935 = 3313403) B3313403
theorem B10622249 : Blo 1472556 10622249 := bstep (se 2 (by rfl) ⟨3983343, by rfl⟩ : syracuseStep 10622249 = 7966687) B7966687
theorem B2209079 : Blo 1472556 2209079 := bstep (se 1 (by rfl) ⟨1656809, by rfl⟩ : syracuseStep 2209079 = 3313619) B3313619
theorem B3315023 : Blo 1472556 3315023 := bstep (se 1 (by rfl) ⟨2486267, by rfl⟩ : syracuseStep 3315023 = 4972535) B4972535
theorem B2487631 : Blo 1472556 2487631 := bstep (se 1 (by rfl) ⟨1865723, by rfl⟩ : syracuseStep 2487631 = 3731447) B3731447
theorem B2209259 : Blo 1472556 2209259 := bstep (se 1 (by rfl) ⟨1656944, by rfl⟩ : syracuseStep 2209259 = 3313889) B3313889
theorem B2209385 : Blo 1472556 2209385 := bstep (se 2 (by rfl) ⟨828519, by rfl⟩ : syracuseStep 2209385 = 1657039) B1657039
theorem B2209607 : Blo 1472556 2209607 := bstep (se 1 (by rfl) ⟨1657205, by rfl⟩ : syracuseStep 2209607 = 3314411) B3314411
theorem B2127727 : Blo 1472556 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B6059897 : Blo 1472556 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B2209787 : Blo 1472556 2209787 := bstep (se 1 (by rfl) ⟨1657340, by rfl⟩ : syracuseStep 2209787 = 3314681) B3314681
theorem B3315743 : Blo 1472556 3315743 := bstep (se 1 (by rfl) ⟨2486807, by rfl⟩ : syracuseStep 3315743 = 4973615) B4973615
theorem B2209847 : Blo 1472556 2209847 := bstep (se 1 (by rfl) ⟨1657385, by rfl⟩ : syracuseStep 2209847 = 3314771) B3314771
theorem B2209913 : Blo 1472556 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B2209919 : Blo 1472556 2209919 := bstep (se 1 (by rfl) ⟨1657439, by rfl⟩ : syracuseStep 2209919 = 3314879) B3314879
theorem B2209967 : Blo 1472556 2209967 := bstep (se 1 (by rfl) ⟨1657475, by rfl⟩ : syracuseStep 2209967 = 3314951) B3314951
theorem B16791785 : Blo 1472556 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1472763 : Blo 1472556 1472763 := bstep (se 1 (by rfl) ⟨1104572, by rfl⟩ : syracuseStep 1472763 = 2209145) B2209145
theorem B1472767 : Blo 1472556 1472767 := bstep (se 1 (by rfl) ⟨1104575, by rfl⟩ : syracuseStep 1472767 = 2209151) B2209151
theorem B4970807 : Blo 1472556 4970807 := bstep (se 1 (by rfl) ⟨3728105, by rfl⟩ : syracuseStep 4970807 = 7456211) B7456211
theorem B1472871 : Blo 1472556 1472871 := bstep (se 1 (by rfl) ⟨1104653, by rfl⟩ : syracuseStep 1472871 = 2209307) B2209307
theorem B2210207 : Blo 1472556 2210207 := bstep (se 1 (by rfl) ⟨1657655, by rfl⟩ : syracuseStep 2210207 = 3315311) B3315311
theorem B1472991 : Blo 1472556 1472991 := bstep (se 1 (by rfl) ⟨1104743, by rfl⟩ : syracuseStep 1472991 = 2209487) B2209487
theorem B1473127 : Blo 1472556 1473127 := bstep (se 1 (by rfl) ⟨1104845, by rfl⟩ : syracuseStep 1473127 = 2209691) B2209691
theorem B1473151 : Blo 1472556 1473151 := bstep (se 1 (by rfl) ⟨1104863, by rfl⟩ : syracuseStep 1473151 = 2209727) B2209727
theorem B20151017 : Blo 1472556 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B1473263 : Blo 1472556 1473263 := bstep (se 1 (by rfl) ⟨1104947, by rfl⟩ : syracuseStep 1473263 = 2209895) B2209895
theorem B6290207 : Blo 1472556 6290207 := bstep (se 1 (by rfl) ⟨4717655, by rfl⟩ : syracuseStep 6290207 = 9435311) B9435311
theorem B20159279 : Blo 1472556 20159279 := bstep (se 1 (by rfl) ⟨15119459, by rfl⟩ : syracuseStep 20159279 = 30238919) B30238919
theorem B4971401 : Blo 1472556 4971401 := bstep (se 2 (by rfl) ⟨1864275, by rfl⟩ : syracuseStep 4971401 = 3728551) B3728551
theorem B1473519 : Blo 1472556 1473519 := bstep (se 1 (by rfl) ⟨1105139, by rfl⟩ : syracuseStep 1473519 = 2210279) B2210279
theorem B1473567 : Blo 1472556 1473567 := bstep (se 1 (by rfl) ⟨1105175, by rfl⟩ : syracuseStep 1473567 = 2210351) B2210351
theorem B12590423 : Blo 1472556 12590423 := bstep (se 1 (by rfl) ⟨9442817, by rfl⟩ : syracuseStep 12590423 = 18885635) B18885635
theorem B1474015 : Blo 1472556 1474015 := bstep (se 1 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 1474015 = 2211023) B2211023
theorem B2211305 : Blo 1472556 2211305 := bstep (se 2 (by rfl) ⟨829239, by rfl⟩ : syracuseStep 2211305 = 1658479) B1658479
theorem B1474075 : Blo 1472556 1474075 := bstep (se 1 (by rfl) ⟨1105556, by rfl⟩ : syracuseStep 1474075 = 2211113) B2211113
theorem B1474095 : Blo 1472556 1474095 := bstep (se 1 (by rfl) ⟨1105571, by rfl⟩ : syracuseStep 1474095 = 2211143) B2211143
theorem B47824769 : Blo 1472556 47824769 := bstep (se 2 (by rfl) ⟨17934288, by rfl⟩ : syracuseStep 47824769 = 35868577) B35868577
theorem B1474495 : Blo 1472556 1474495 := bstep (se 1 (by rfl) ⟨1105871, by rfl⟩ : syracuseStep 1474495 = 2211743) B2211743
theorem B3727559 : Blo 1472556 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B2302175 : Blo 1472556 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B5038355 : Blo 1472556 5038355 := bstep (se 1 (by rfl) ⟨3778766, by rfl⟩ : syracuseStep 5038355 = 7557533) B7557533
theorem B8388967 : Blo 1472556 8388967 := bstep (se 1 (by rfl) ⟨6291725, by rfl⟩ : syracuseStep 8388967 = 12583451) B12583451
theorem B40878487 : Blo 1472556 40878487 := bstep (se 1 (by rfl) ⟨30658865, by rfl⟩ : syracuseStep 40878487 = 61317731) B61317731
theorem B217924025 : Blo 1472556 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B3146239 : Blo 1472556 3146239 := bstep (se 1 (by rfl) ⟨2359679, by rfl⟩ : syracuseStep 3146239 = 4719359) B4719359
theorem B12763727 : Blo 1472556 12763727 := bstep (se 1 (by rfl) ⟨9572795, by rfl⟩ : syracuseStep 12763727 = 19145591) B19145591
theorem B3539711 : Blo 1472556 3539711 := bstep (se 1 (by rfl) ⟨2654783, by rfl⟩ : syracuseStep 3539711 = 5309567) B5309567
theorem B4482017 : Blo 1472556 4482017 := bstep (se 2 (by rfl) ⟨1680756, by rfl⟩ : syracuseStep 4482017 = 3361513) B3361513
theorem B4195327 : Blo 1472556 4195327 := bstep (se 1 (by rfl) ⟨3146495, by rfl⟩ : syracuseStep 4195327 = 6292991) B6292991
theorem B34030691 : Blo 1472556 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B4039931 : Blo 1472556 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B15123773 : Blo 1472556 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B11503295 : Blo 1472556 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B11347877 : Blo 1472556 11347877 := bstep (se 4 (by rfl) ⟨1063863, by rfl⟩ : syracuseStep 11347877 = 2127727) B2127727
theorem B1656895 : Blo 1472556 1656895 := bstep (se 1 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 1656895 = 2485343) B2485343
theorem B8964179 : Blo 1472556 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B25167995 : Blo 1472556 25167995 := bstep (se 1 (by rfl) ⟨18875996, by rfl⟩ : syracuseStep 25167995 = 37751993) B37751993
theorem B2361755 : Blo 1472556 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B4196843 : Blo 1472556 4196843 := bstep (se 1 (by rfl) ⟨3147632, by rfl⟩ : syracuseStep 4196843 = 6295265) B6295265
theorem B4721255 : Blo 1472556 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B1657471 : Blo 1472556 1657471 := bstep (se 1 (by rfl) ⟨1243103, by rfl⟩ : syracuseStep 1657471 = 2486207) B2486207
theorem B378210997 : Blo 1472556 378210997 := bstep (se 5 (by rfl) ⟨17728640, by rfl⟩ : syracuseStep 378210997 = 35457281) B35457281
theorem B4975451 : Blo 1472556 4975451 := bstep (se 1 (by rfl) ⟨3731588, by rfl⟩ : syracuseStep 4975451 = 7463177) B7463177
theorem B3730313 : Blo 1472556 3730313 := bstep (se 2 (by rfl) ⟨1398867, by rfl⟩ : syracuseStep 3730313 = 2797735) B2797735
theorem B524029121 : Blo 1472556 524029121 := bstep (se 2 (by rfl) ⟨196510920, by rfl⟩ : syracuseStep 524029121 = 393021841) B393021841
theorem B7081499 : Blo 1472556 7081499 := bstep (se 1 (by rfl) ⟨5311124, by rfl⟩ : syracuseStep 7081499 = 10622249) B10622249
theorem B13446847 : Blo 1472556 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B7565167 : Blo 1472556 7565167 := bstep (se 1 (by rfl) ⟨5673875, by rfl⟩ : syracuseStep 7565167 = 11347751) B11347751
theorem B11194523 : Blo 1472556 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B3313871 : Blo 1472556 3313871 := bstep (se 1 (by rfl) ⟨2485403, by rfl⟩ : syracuseStep 3313871 = 4970807) B4970807
theorem B13439519 : Blo 1472556 13439519 := bstep (se 1 (by rfl) ⟨10079639, by rfl⟩ : syracuseStep 13439519 = 20159279) B20159279
theorem B3314267 : Blo 1472556 3314267 := bstep (se 1 (by rfl) ⟨2485700, by rfl⟩ : syracuseStep 3314267 = 4971401) B4971401
theorem B2487071 : Blo 1472556 2487071 := bstep (se 1 (by rfl) ⟨1865303, by rfl⟩ : syracuseStep 2487071 = 3730607) B3730607
theorem B16790327 : Blo 1472556 16790327 := bstep (se 1 (by rfl) ⟨12592745, by rfl⟩ : syracuseStep 16790327 = 25185491) B25185491
theorem B8393615 : Blo 1472556 8393615 := bstep (se 1 (by rfl) ⟨6295211, by rfl⟩ : syracuseStep 8393615 = 12590423) B12590423
theorem B2208959 : Blo 1472556 2208959 := bstep (se 1 (by rfl) ⟨1656719, by rfl⟩ : syracuseStep 2208959 = 3313439) B3313439
theorem B1864939 : Blo 1472556 1864939 := bstep (se 1 (by rfl) ⟨1398704, by rfl⟩ : syracuseStep 1864939 = 2797409) B2797409
theorem B3315113 : Blo 1472556 3315113 := bstep (se 2 (by rfl) ⟨1243167, by rfl⟩ : syracuseStep 3315113 = 2486335) B2486335
theorem B3315167 : Blo 1472556 3315167 := bstep (se 1 (by rfl) ⟨2486375, by rfl⟩ : syracuseStep 3315167 = 4972751) B4972751
theorem B76519201 : Blo 1472556 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B1472623 : Blo 1472556 1472623 := bstep (se 1 (by rfl) ⟨1104467, by rfl⟩ : syracuseStep 1472623 = 2208935) B2208935
theorem B1472719 : Blo 1472556 1472719 := bstep (se 1 (by rfl) ⟨1104539, by rfl⟩ : syracuseStep 1472719 = 2209079) B2209079
theorem B2210015 : Blo 1472556 2210015 := bstep (se 1 (by rfl) ⟨1657511, by rfl⟩ : syracuseStep 2210015 = 3315023) B3315023
theorem B1472839 : Blo 1472556 1472839 := bstep (se 1 (by rfl) ⟨1104629, by rfl⟩ : syracuseStep 1472839 = 2209259) B2209259
theorem B1472923 : Blo 1472556 1472923 := bstep (se 1 (by rfl) ⟨1104692, by rfl⟩ : syracuseStep 1472923 = 2209385) B2209385
theorem B30251465 : Blo 1472556 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B3316175 : Blo 1472556 3316175 := bstep (se 1 (by rfl) ⟨2487131, by rfl⟩ : syracuseStep 3316175 = 4974263) B4974263
theorem B1473071 : Blo 1472556 1473071 := bstep (se 1 (by rfl) ⟨1104803, by rfl⟩ : syracuseStep 1473071 = 2209607) B2209607
theorem B10623635 : Blo 1472556 10623635 := bstep (se 1 (by rfl) ⟨7967726, by rfl⟩ : syracuseStep 10623635 = 15935453) B15935453
theorem B1473191 : Blo 1472556 1473191 := bstep (se 1 (by rfl) ⟨1104893, by rfl⟩ : syracuseStep 1473191 = 2209787) B2209787
theorem B2210495 : Blo 1472556 2210495 := bstep (se 1 (by rfl) ⟨1657871, by rfl⟩ : syracuseStep 2210495 = 3315743) B3315743
theorem B1473231 : Blo 1472556 1473231 := bstep (se 1 (by rfl) ⟨1104923, by rfl⟩ : syracuseStep 1473231 = 2209847) B2209847
theorem B1473275 : Blo 1472556 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B1473279 : Blo 1472556 1473279 := bstep (se 1 (by rfl) ⟨1104959, by rfl⟩ : syracuseStep 1473279 = 2209919) B2209919
theorem B1473311 : Blo 1472556 1473311 := bstep (se 1 (by rfl) ⟨1104983, by rfl⟩ : syracuseStep 1473311 = 2209967) B2209967
theorem B1473471 : Blo 1472556 1473471 := bstep (se 1 (by rfl) ⟨1105103, by rfl⟩ : syracuseStep 1473471 = 2210207) B2210207
theorem B3316841 : Blo 1472556 3316841 := bstep (se 2 (by rfl) ⟨1243815, by rfl⟩ : syracuseStep 3316841 = 2487631) B2487631
theorem B13434011 : Blo 1472556 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B4193471 : Blo 1472556 4193471 := bstep (se 1 (by rfl) ⟨3145103, by rfl⟩ : syracuseStep 4193471 = 6290207) B6290207
theorem B3317147 : Blo 1472556 3317147 := bstep (se 1 (by rfl) ⟨2487860, by rfl⟩ : syracuseStep 3317147 = 4975721) B4975721
theorem B2211449 : Blo 1472556 2211449 := bstep (se 2 (by rfl) ⟨829293, by rfl⟩ : syracuseStep 2211449 = 1658587) B1658587
theorem B1474203 : Blo 1472556 1474203 := bstep (se 1 (by rfl) ⟨1105652, by rfl⟩ : syracuseStep 1474203 = 2211305) B2211305
theorem B31883179 : Blo 1472556 31883179 := bstep (se 1 (by rfl) ⟨23912384, by rfl⟩ : syracuseStep 31883179 = 47824769) B47824769
theorem B3317723 : Blo 1472556 3317723 := bstep (se 1 (by rfl) ⟨2488292, by rfl⟩ : syracuseStep 3317723 = 4976585) B4976585
theorem B108945395 : Blo 1472556 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B7463015 : Blo 1472556 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B3358903 : Blo 1472556 3358903 := bstep (se 1 (by rfl) ⟨2519177, by rfl⟩ : syracuseStep 3358903 = 5038355) B5038355
theorem B5595743 : Blo 1472556 5595743 := bstep (se 1 (by rfl) ⟨4196807, by rfl⟩ : syracuseStep 5595743 = 8393615) B8393615
theorem B4194985 : Blo 1472556 4194985 := bstep (se 2 (by rfl) ⟨1573119, by rfl⟩ : syracuseStep 4194985 = 3146239) B3146239
theorem B2017125317 : Blo 1472556 2017125317 := bstep (se 4 (by rfl) ⟨189105498, by rfl⟩ : syracuseStep 2017125317 = 378210997) B378210997
theorem B7668863 : Blo 1472556 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B16778663 : Blo 1472556 16778663 := bstep (se 1 (by rfl) ⟨12583997, by rfl⟩ : syracuseStep 16778663 = 25167995) B25167995
theorem B3147503 : Blo 1472556 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2324522933 : Blo 1472556 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B9439229 : Blo 1472556 9439229 := bstep (se 3 (by rfl) ⟨1769855, by rfl⟩ : syracuseStep 9439229 = 3539711) B3539711
theorem B8956007 : Blo 1472556 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B2795647 : Blo 1472556 2795647 := bstep (se 1 (by rfl) ⟨2096735, by rfl⟩ : syracuseStep 2795647 = 4193471) B4193471
theorem B4720999 : Blo 1472556 4720999 := bstep (se 1 (by rfl) ⟨3540749, by rfl⟩ : syracuseStep 4720999 = 7081499) B7081499
theorem B102025601 : Blo 1472556 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B10086889 : Blo 1472556 10086889 := bstep (se 2 (by rfl) ⟨3782583, by rfl⟩ : syracuseStep 10086889 = 7565167) B7565167
theorem B42510905 : Blo 1472556 42510905 := bstep (se 2 (by rfl) ⟨15941589, by rfl⟩ : syracuseStep 42510905 = 31883179) B31883179
theorem B2485039 : Blo 1472556 2485039 := bstep (se 1 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 2485039 = 3727559) B3727559
theorem B11185289 : Blo 1472556 11185289 := bstep (se 2 (by rfl) ⟨4194483, by rfl⟩ : syracuseStep 11185289 = 8388967) B8388967
theorem B1658047 : Blo 1472556 1658047 := bstep (se 1 (by rfl) ⟨1243535, by rfl⟩ : syracuseStep 1658047 = 2487071) B2487071
theorem B54504649 : Blo 1472556 54504649 := bstep (se 2 (by rfl) ⟨20439243, by rfl⟩ : syracuseStep 54504649 = 40878487) B40878487
theorem B11193551 : Blo 1472556 11193551 := bstep (se 1 (by rfl) ⟨8395163, by rfl⟩ : syracuseStep 11193551 = 16790327) B16790327
theorem B6139133 : Blo 1472556 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B22687127 : Blo 1472556 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B7565251 : Blo 1472556 7565251 := bstep (se 1 (by rfl) ⟨5673938, by rfl⟩ : syracuseStep 7565251 = 11347877) B11347877
theorem B5976119 : Blo 1472556 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B2486585 : Blo 1472556 2486585 := bstep (se 2 (by rfl) ⟨932469, by rfl⟩ : syracuseStep 2486585 = 1864939) B1864939
theorem B2797895 : Blo 1472556 2797895 := bstep (se 1 (by rfl) ⟨2098421, by rfl⟩ : syracuseStep 2797895 = 4196843) B4196843
theorem B7082423 : Blo 1472556 7082423 := bstep (se 1 (by rfl) ⟨5311817, by rfl⟩ : syracuseStep 7082423 = 10623635) B10623635
theorem B2486875 : Blo 1472556 2486875 := bstep (se 1 (by rfl) ⟨1865156, by rfl⟩ : syracuseStep 2486875 = 3730313) B3730313
theorem B349352747 : Blo 1472556 349352747 := bstep (se 1 (by rfl) ⟨262014560, by rfl⟩ : syracuseStep 349352747 = 524029121) B524029121
theorem B17929129 : Blo 1472556 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B2209193 : Blo 1472556 2209193 := bstep (se 2 (by rfl) ⟨828447, by rfl⟩ : syracuseStep 2209193 = 1656895) B1656895
theorem B2209247 : Blo 1472556 2209247 := bstep (se 1 (by rfl) ⟨1656935, by rfl⟩ : syracuseStep 2209247 = 3313871) B3313871
theorem B8959679 : Blo 1472556 8959679 := bstep (se 1 (by rfl) ⟨6719759, by rfl⟩ : syracuseStep 8959679 = 13439519) B13439519
theorem B8509151 : Blo 1472556 8509151 := bstep (se 1 (by rfl) ⟨6381863, by rfl⟩ : syracuseStep 8509151 = 12763727) B12763727
theorem B2209511 : Blo 1472556 2209511 := bstep (se 1 (by rfl) ⟨1657133, by rfl⟩ : syracuseStep 2209511 = 3314267) B3314267
theorem B2988011 : Blo 1472556 2988011 := bstep (se 1 (by rfl) ⟨2241008, by rfl⟩ : syracuseStep 2988011 = 4482017) B4482017
theorem B1472639 : Blo 1472556 1472639 := bstep (se 1 (by rfl) ⟨1104479, by rfl⟩ : syracuseStep 1472639 = 2208959) B2208959
theorem B2693287 : Blo 1472556 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B2209961 : Blo 1472556 2209961 := bstep (se 2 (by rfl) ⟨828735, by rfl⟩ : syracuseStep 2209961 = 1657471) B1657471
theorem B10082515 : Blo 1472556 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B2210075 : Blo 1472556 2210075 := bstep (se 1 (by rfl) ⟨1657556, by rfl⟩ : syracuseStep 2210075 = 3315113) B3315113
theorem B2210111 : Blo 1472556 2210111 := bstep (se 1 (by rfl) ⟨1657583, by rfl⟩ : syracuseStep 2210111 = 3315167) B3315167
theorem B6298013 : Blo 1472556 6298013 := bstep (se 3 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 6298013 = 2361755) B2361755
theorem B5593769 : Blo 1472556 5593769 := bstep (se 2 (by rfl) ⟨2097663, by rfl⟩ : syracuseStep 5593769 = 4195327) B4195327
theorem B1473343 : Blo 1472556 1473343 := bstep (se 1 (by rfl) ⟨1105007, by rfl⟩ : syracuseStep 1473343 = 2210015) B2210015
theorem B20167643 : Blo 1472556 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B2210783 : Blo 1472556 2210783 := bstep (se 1 (by rfl) ⟨1658087, by rfl⟩ : syracuseStep 2210783 = 3316175) B3316175
theorem B1473663 : Blo 1472556 1473663 := bstep (se 1 (by rfl) ⟨1105247, by rfl⟩ : syracuseStep 1473663 = 2210495) B2210495
theorem B3316967 : Blo 1472556 3316967 := bstep (se 1 (by rfl) ⟨2487725, by rfl⟩ : syracuseStep 3316967 = 4975451) B4975451
theorem B2211227 : Blo 1472556 2211227 := bstep (se 1 (by rfl) ⟨1658420, by rfl⟩ : syracuseStep 2211227 = 3316841) B3316841
theorem B2211431 : Blo 1472556 2211431 := bstep (se 1 (by rfl) ⟨1658573, by rfl⟩ : syracuseStep 2211431 = 3317147) B3317147
theorem B1474299 : Blo 1472556 1474299 := bstep (se 1 (by rfl) ⟨1105724, by rfl⟩ : syracuseStep 1474299 = 2211449) B2211449
theorem B2211815 : Blo 1472556 2211815 := bstep (se 1 (by rfl) ⟨1658861, by rfl⟩ : syracuseStep 2211815 = 3317723) B3317723
theorem B72630263 : Blo 1472556 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B3727529 : Blo 1472556 3727529 := bstep (se 2 (by rfl) ⟨1397823, by rfl⟩ : syracuseStep 3727529 = 2795647) B2795647
theorem B13443353 : Blo 1472556 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B1344750211 : Blo 1472556 1344750211 := bstep (se 1 (by rfl) ⟨1008562658, by rfl⟩ : syracuseStep 1344750211 = 2017125317) B2017125317
theorem B5112575 : Blo 1472556 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B16794701 : Blo 1472556 16794701 := bstep (se 3 (by rfl) ⟨3149006, by rfl⟩ : syracuseStep 16794701 = 6298013) B6298013
theorem B5973119 : Blo 1472556 5973119 := bstep (se 1 (by rfl) ⟨4479839, by rfl⟩ : syracuseStep 5973119 = 8959679) B8959679
theorem B23905505 : Blo 1472556 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B1549681955 : Blo 1472556 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B1992007 : Blo 1472556 1992007 := bstep (se 1 (by rfl) ⟨1494005, by rfl⟩ : syracuseStep 1992007 = 2988011) B2988011
theorem B6292819 : Blo 1472556 6292819 := bstep (se 1 (by rfl) ⟨4719614, by rfl⟩ : syracuseStep 6292819 = 9439229) B9439229
theorem B3729179 : Blo 1472556 3729179 := bstep (se 1 (by rfl) ⟨2796884, by rfl⟩ : syracuseStep 3729179 = 5593769) B5593769
theorem B7456859 : Blo 1472556 7456859 := bstep (se 1 (by rfl) ⟨5592644, by rfl⟩ : syracuseStep 7456859 = 11185289) B11185289
theorem B15124751 : Blo 1472556 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B10087001 : Blo 1472556 10087001 := bstep (se 2 (by rfl) ⟨3782625, by rfl⟩ : syracuseStep 10087001 = 7565251) B7565251
theorem B3984079 : Blo 1472556 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B4975343 : Blo 1472556 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1657723 : Blo 1472556 1657723 := bstep (se 1 (by rfl) ⟨1243292, by rfl⟩ : syracuseStep 1657723 = 2486585) B2486585
theorem B3591049 : Blo 1472556 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B4721615 : Blo 1472556 4721615 := bstep (se 1 (by rfl) ⟨3541211, by rfl⟩ : syracuseStep 4721615 = 7082423) B7082423
theorem B3730495 : Blo 1472556 3730495 := bstep (se 1 (by rfl) ⟨2797871, by rfl⟩ : syracuseStep 3730495 = 5595743) B5595743
theorem B6294665 : Blo 1472556 6294665 := bstep (se 2 (by rfl) ⟨2360499, by rfl⟩ : syracuseStep 6294665 = 4720999) B4720999
theorem B232901831 : Blo 1472556 232901831 := bstep (se 1 (by rfl) ⟨174676373, by rfl⟩ : syracuseStep 232901831 = 349352747) B349352747
theorem B11185775 : Blo 1472556 11185775 := bstep (se 1 (by rfl) ⟨8389331, by rfl⟩ : syracuseStep 11185775 = 16778663) B16778663
theorem B3313385 : Blo 1472556 3313385 := bstep (se 2 (by rfl) ⟨1242519, by rfl⟩ : syracuseStep 3313385 = 2485039) B2485039
theorem B5672767 : Blo 1472556 5672767 := bstep (se 1 (by rfl) ⟨4254575, by rfl⟩ : syracuseStep 5672767 = 8509151) B8509151
theorem B28340603 : Blo 1472556 28340603 := bstep (se 1 (by rfl) ⟨21255452, by rfl⟩ : syracuseStep 28340603 = 42510905) B42510905
theorem B8393341 : Blo 1472556 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B4092755 : Blo 1472556 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B48420175 : Blo 1472556 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B1865263 : Blo 1472556 1865263 := bstep (se 1 (by rfl) ⟨1398947, by rfl⟩ : syracuseStep 1865263 = 2797895) B2797895
theorem B4478537 : Blo 1472556 4478537 := bstep (se 2 (by rfl) ⟨1679451, by rfl⟩ : syracuseStep 4478537 = 3358903) B3358903
theorem B13449185 : Blo 1472556 13449185 := bstep (se 2 (by rfl) ⟨5043444, by rfl⟩ : syracuseStep 13449185 = 10086889) B10086889
theorem B3315833 : Blo 1472556 3315833 := bstep (se 2 (by rfl) ⟨1243437, by rfl⟩ : syracuseStep 3315833 = 2486875) B2486875
theorem B5593313 : Blo 1472556 5593313 := bstep (se 2 (by rfl) ⟨2097492, by rfl⟩ : syracuseStep 5593313 = 4194985) B4194985
theorem B1472795 : Blo 1472556 1472795 := bstep (se 1 (by rfl) ⟨1104596, by rfl⟩ : syracuseStep 1472795 = 2209193) B2209193
theorem B1472831 : Blo 1472556 1472831 := bstep (se 1 (by rfl) ⟨1104623, by rfl⟩ : syracuseStep 1472831 = 2209247) B2209247
theorem B290691461 : Blo 1472556 290691461 := bstep (se 4 (by rfl) ⟨27252324, by rfl⟩ : syracuseStep 290691461 = 54504649) B54504649
theorem B1473007 : Blo 1472556 1473007 := bstep (se 1 (by rfl) ⟨1104755, by rfl⟩ : syracuseStep 1473007 = 2209511) B2209511
theorem B5970671 : Blo 1472556 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B1473307 : Blo 1472556 1473307 := bstep (se 1 (by rfl) ⟨1104980, by rfl⟩ : syracuseStep 1473307 = 2209961) B2209961
theorem B1473383 : Blo 1472556 1473383 := bstep (se 1 (by rfl) ⟨1105037, by rfl⟩ : syracuseStep 1473383 = 2210075) B2210075
theorem B1473407 : Blo 1472556 1473407 := bstep (se 1 (by rfl) ⟨1105055, by rfl⟩ : syracuseStep 1473407 = 2210111) B2210111
theorem B2210729 : Blo 1472556 2210729 := bstep (se 2 (by rfl) ⟨829023, by rfl⟩ : syracuseStep 2210729 = 1658047) B1658047
theorem B68017067 : Blo 1472556 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B1473855 : Blo 1472556 1473855 := bstep (se 1 (by rfl) ⟨1105391, by rfl⟩ : syracuseStep 1473855 = 2210783) B2210783
theorem B7462367 : Blo 1472556 7462367 := bstep (se 1 (by rfl) ⟨5596775, by rfl⟩ : syracuseStep 7462367 = 11193551) B11193551
theorem B2211311 : Blo 1472556 2211311 := bstep (se 1 (by rfl) ⟨1658483, by rfl⟩ : syracuseStep 2211311 = 3316967) B3316967
theorem B1474151 : Blo 1472556 1474151 := bstep (se 1 (by rfl) ⟨1105613, by rfl⟩ : syracuseStep 1474151 = 2211227) B2211227
theorem B1474287 : Blo 1472556 1474287 := bstep (se 1 (by rfl) ⟨1105715, by rfl⟩ : syracuseStep 1474287 = 2211431) B2211431
theorem B53780381 : Blo 1472556 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B1474543 : Blo 1472556 1474543 := bstep (se 1 (by rfl) ⟨1105907, by rfl⟩ : syracuseStep 1474543 = 2211815) B2211815
theorem B8962235 : Blo 1472556 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B3408383 : Blo 1472556 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B3982079 : Blo 1472556 3982079 := bstep (se 1 (by rfl) ⟨2986559, by rfl⟩ : syracuseStep 3982079 = 5973119) B5973119
theorem B11191121 : Blo 1472556 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B1793000281 : Blo 1472556 1793000281 := bstep (se 2 (by rfl) ⟨672375105, by rfl⟩ : syracuseStep 1793000281 = 1344750211) B1344750211
theorem B775177229 : Blo 1472556 775177229 := bstep (se 3 (by rfl) ⟨145345730, by rfl⟩ : syracuseStep 775177229 = 290691461) B290691461
theorem B4973993 : Blo 1472556 4973993 := bstep (se 2 (by rfl) ⟨1865247, by rfl⟩ : syracuseStep 4973993 = 3730495) B3730495
theorem B3728875 : Blo 1472556 3728875 := bstep (se 1 (by rfl) ⟨2796656, by rfl⟩ : syracuseStep 3728875 = 5593313) B5593313
theorem B2656009 : Blo 1472556 2656009 := bstep (se 2 (by rfl) ⟨996003, by rfl⟩ : syracuseStep 2656009 = 1992007) B1992007
theorem B8390425 : Blo 1472556 8390425 := bstep (se 2 (by rfl) ⟨3146409, by rfl⟩ : syracuseStep 8390425 = 6292819) B6292819
theorem B45344711 : Blo 1472556 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B3147743 : Blo 1472556 3147743 := bstep (se 1 (by rfl) ⟨2360807, by rfl⟩ : syracuseStep 3147743 = 4721615) B4721615
theorem B4196443 : Blo 1472556 4196443 := bstep (se 1 (by rfl) ⟨3147332, by rfl⟩ : syracuseStep 4196443 = 6294665) B6294665
theorem B10914013 : Blo 1472556 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B4974911 : Blo 1472556 4974911 := bstep (se 1 (by rfl) ⟨3731183, by rfl⟩ : syracuseStep 4974911 = 7462367) B7462367
theorem B7457183 : Blo 1472556 7457183 := bstep (se 1 (by rfl) ⟨5592887, by rfl⟩ : syracuseStep 7457183 = 11185775) B11185775
theorem B7563689 : Blo 1472556 7563689 := bstep (se 2 (by rfl) ⟨2836383, by rfl⟩ : syracuseStep 7563689 = 5672767) B5672767
theorem B2485019 : Blo 1472556 2485019 := bstep (se 1 (by rfl) ⟨1863764, by rfl⟩ : syracuseStep 2485019 = 3727529) B3727529
theorem B18893735 : Blo 1472556 18893735 := bstep (se 1 (by rfl) ⟨14170301, by rfl⟩ : syracuseStep 18893735 = 28340603) B28340603
theorem B15937003 : Blo 1472556 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B1033121303 : Blo 1472556 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B5312105 : Blo 1472556 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B2985691 : Blo 1472556 2985691 := bstep (se 1 (by rfl) ⟨2239268, by rfl⟩ : syracuseStep 2985691 = 4478537) B4478537
theorem B4788065 : Blo 1472556 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B2486119 : Blo 1472556 2486119 := bstep (se 1 (by rfl) ⟨1864589, by rfl⟩ : syracuseStep 2486119 = 3729179) B3729179
theorem B8966123 : Blo 1472556 8966123 := bstep (se 1 (by rfl) ⟨6724592, by rfl⟩ : syracuseStep 8966123 = 13449185) B13449185
theorem B2487017 : Blo 1472556 2487017 := bstep (se 2 (by rfl) ⟨932631, by rfl⟩ : syracuseStep 2487017 = 1865263) B1865263
theorem B155267887 : Blo 1472556 155267887 := bstep (se 1 (by rfl) ⟨116450915, by rfl⟩ : syracuseStep 155267887 = 232901831) B232901831
theorem B2208923 : Blo 1472556 2208923 := bstep (se 1 (by rfl) ⟨1656692, by rfl⟩ : syracuseStep 2208923 = 3313385) B3313385
theorem B35853587 : Blo 1472556 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B11196467 : Blo 1472556 11196467 := bstep (se 1 (by rfl) ⟨8397350, by rfl⟩ : syracuseStep 11196467 = 16794701) B16794701
theorem B2210297 : Blo 1472556 2210297 := bstep (se 2 (by rfl) ⟨828861, by rfl⟩ : syracuseStep 2210297 = 1657723) B1657723
theorem B4971239 : Blo 1472556 4971239 := bstep (se 1 (by rfl) ⟨3728429, by rfl⟩ : syracuseStep 4971239 = 7456859) B7456859
theorem B2210555 : Blo 1472556 2210555 := bstep (se 1 (by rfl) ⟨1657916, by rfl⟩ : syracuseStep 2210555 = 3315833) B3315833
theorem B10083167 : Blo 1472556 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B6724667 : Blo 1472556 6724667 := bstep (se 1 (by rfl) ⟨5043500, by rfl⟩ : syracuseStep 6724667 = 10087001) B10087001
theorem B64560233 : Blo 1472556 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B3980447 : Blo 1472556 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B3316895 : Blo 1472556 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B1473819 : Blo 1472556 1473819 := bstep (se 1 (by rfl) ⟨1105364, by rfl⟩ : syracuseStep 1473819 = 2210729) B2210729
theorem B1474207 : Blo 1472556 1474207 := bstep (se 1 (by rfl) ⟨1105655, by rfl⟩ : syracuseStep 1474207 = 2211311) B2211311
theorem B5595257 : Blo 1472556 5595257 := bstep (se 2 (by rfl) ⟨2098221, by rfl⟩ : syracuseStep 5595257 = 4196443) B4196443
theorem B516784819 : Blo 1472556 516784819 := bstep (se 1 (by rfl) ⟨387588614, by rfl⟩ : syracuseStep 516784819 = 775177229) B775177229
theorem B30229807 : Blo 1472556 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B2098495 : Blo 1472556 2098495 := bstep (se 1 (by rfl) ⟨1573871, by rfl⟩ : syracuseStep 2098495 = 3147743) B3147743
theorem B7464311 : Blo 1472556 7464311 := bstep (se 1 (by rfl) ⟨5598233, by rfl⟩ : syracuseStep 7464311 = 11196467) B11196467
theorem B14165381 : Blo 1472556 14165381 := bstep (se 4 (by rfl) ⟨1328004, by rfl⟩ : syracuseStep 14165381 = 2656009) B2656009
theorem B1656679 : Blo 1472556 1656679 := bstep (se 1 (by rfl) ⟨1242509, by rfl⟩ : syracuseStep 1656679 = 2485019) B2485019
theorem B10618877 : Blo 1472556 10618877 := bstep (se 3 (by rfl) ⟨1991039, by rfl⟩ : syracuseStep 10618877 = 3982079) B3982079
theorem B4483111 : Blo 1472556 4483111 := bstep (se 1 (by rfl) ⟨3362333, by rfl⟩ : syracuseStep 4483111 = 6724667) B6724667
theorem B3541403 : Blo 1472556 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B5974823 : Blo 1472556 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B14552017 : Blo 1472556 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B2272255 : Blo 1472556 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B1658011 : Blo 1472556 1658011 := bstep (se 1 (by rfl) ⟨1243508, by rfl⟩ : syracuseStep 1658011 = 2487017) B2487017
theorem B207023849 : Blo 1472556 207023849 := bstep (se 2 (by rfl) ⟨77633943, by rfl⟩ : syracuseStep 207023849 = 155267887) B155267887
theorem B2390667041 : Blo 1472556 2390667041 := bstep (se 2 (by rfl) ⟨896500140, by rfl⟩ : syracuseStep 2390667041 = 1793000281) B1793000281
theorem B5042459 : Blo 1472556 5042459 := bstep (se 1 (by rfl) ⟨3781844, by rfl⟩ : syracuseStep 5042459 = 7563689) B7563689
theorem B3314159 : Blo 1472556 3314159 := bstep (se 1 (by rfl) ⟨2485619, by rfl⟩ : syracuseStep 3314159 = 4971239) B4971239
theorem B6722111 : Blo 1472556 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B12595823 : Blo 1472556 12595823 := bstep (se 1 (by rfl) ⟨9446867, by rfl⟩ : syracuseStep 12595823 = 18893735) B18893735
theorem B688747535 : Blo 1472556 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B11187233 : Blo 1472556 11187233 := bstep (se 2 (by rfl) ⟨4195212, by rfl⟩ : syracuseStep 11187233 = 8390425) B8390425
theorem B3314825 : Blo 1472556 3314825 := bstep (se 2 (by rfl) ⟨1243059, by rfl⟩ : syracuseStep 3314825 = 2486119) B2486119
theorem B3192043 : Blo 1472556 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B5977415 : Blo 1472556 5977415 := bstep (se 1 (by rfl) ⟨4483061, by rfl⟩ : syracuseStep 5977415 = 8966123) B8966123
theorem B7460747 : Blo 1472556 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B1472615 : Blo 1472556 1472615 := bstep (se 1 (by rfl) ⟨1104461, by rfl⟩ : syracuseStep 1472615 = 2208923) B2208923
theorem B23902391 : Blo 1472556 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B3315995 : Blo 1472556 3315995 := bstep (se 1 (by rfl) ⟨2486996, by rfl⟩ : syracuseStep 3315995 = 4973993) B4973993
theorem B3316607 : Blo 1472556 3316607 := bstep (se 1 (by rfl) ⟨2487455, by rfl⟩ : syracuseStep 3316607 = 4974911) B4974911
theorem B4971455 : Blo 1472556 4971455 := bstep (se 1 (by rfl) ⟨3728591, by rfl⟩ : syracuseStep 4971455 = 7457183) B7457183
theorem B1473531 : Blo 1472556 1473531 := bstep (se 1 (by rfl) ⟨1105148, by rfl⟩ : syracuseStep 1473531 = 2210297) B2210297
theorem B1473703 : Blo 1472556 1473703 := bstep (se 1 (by rfl) ⟨1105277, by rfl⟩ : syracuseStep 1473703 = 2210555) B2210555
theorem B4971833 : Blo 1472556 4971833 := bstep (se 2 (by rfl) ⟨1864437, by rfl⟩ : syracuseStep 4971833 = 3728875) B3728875
theorem B21249337 : Blo 1472556 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B43040155 : Blo 1472556 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B2653631 : Blo 1472556 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B2211263 : Blo 1472556 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B3980921 : Blo 1472556 3980921 := bstep (se 2 (by rfl) ⟨1492845, by rfl⟩ : syracuseStep 3980921 = 2985691) B2985691
theorem B4481407 : Blo 1472556 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B8397215 : Blo 1472556 8397215 := bstep (se 1 (by rfl) ⟨6297911, by rfl⟩ : syracuseStep 8397215 = 12595823) B12595823
theorem B689046425 : Blo 1472556 689046425 := bstep (se 2 (by rfl) ⟨258392409, by rfl⟩ : syracuseStep 689046425 = 516784819) B516784819
theorem B4973831 : Blo 1472556 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B7079251 : Blo 1472556 7079251 := bstep (se 1 (by rfl) ⟨5309438, by rfl⟩ : syracuseStep 7079251 = 10618877) B10618877
theorem B15934927 : Blo 1472556 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B2360935 : Blo 1472556 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B40306409 : Blo 1472556 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B3983215 : Blo 1472556 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B57386873 : Blo 1472556 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B48474773 : Blo 1472556 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B3730171 : Blo 1472556 3730171 := bstep (se 1 (by rfl) ⟨2797628, by rfl⟩ : syracuseStep 3730171 = 5595257) B5595257
theorem B459165023 : Blo 1472556 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B7458155 : Blo 1472556 7458155 := bstep (se 1 (by rfl) ⟨5593616, by rfl⟩ : syracuseStep 7458155 = 11187233) B11187233
theorem B13446557 : Blo 1472556 13446557 := bstep (se 3 (by rfl) ⟨2521229, by rfl⟩ : syracuseStep 13446557 = 5042459) B5042459
theorem B4976207 : Blo 1472556 4976207 := bstep (se 1 (by rfl) ⟨3732155, by rfl⟩ : syracuseStep 4976207 = 7464311) B7464311
theorem B4256057 : Blo 1472556 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B28332449 : Blo 1472556 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B2797993 : Blo 1472556 2797993 := bstep (se 2 (by rfl) ⟨1049247, by rfl⟩ : syracuseStep 2797993 = 2098495) B2098495
theorem B3314303 : Blo 1472556 3314303 := bstep (se 1 (by rfl) ⟨2485727, by rfl⟩ : syracuseStep 3314303 = 4971455) B4971455
theorem B3314555 : Blo 1472556 3314555 := bstep (se 1 (by rfl) ⟨2485916, by rfl⟩ : syracuseStep 3314555 = 4971833) B4971833
theorem B2208905 : Blo 1472556 2208905 := bstep (se 2 (by rfl) ⟨828339, by rfl⟩ : syracuseStep 2208905 = 1656679) B1656679
theorem B138015899 : Blo 1472556 138015899 := bstep (se 1 (by rfl) ⟨103511924, by rfl⟩ : syracuseStep 138015899 = 207023849) B207023849
theorem B5977481 : Blo 1472556 5977481 := bstep (se 2 (by rfl) ⟨2241555, by rfl⟩ : syracuseStep 5977481 = 4483111) B4483111
theorem B2209439 : Blo 1472556 2209439 := bstep (se 1 (by rfl) ⟨1657079, by rfl⟩ : syracuseStep 2209439 = 3314159) B3314159
theorem B2209883 : Blo 1472556 2209883 := bstep (se 1 (by rfl) ⟨1657412, by rfl⟩ : syracuseStep 2209883 = 3314825) B3314825
theorem B15939773 : Blo 1472556 15939773 := bstep (se 3 (by rfl) ⟨2988707, by rfl⟩ : syracuseStep 15939773 = 5977415) B5977415
theorem B9443587 : Blo 1472556 9443587 := bstep (se 1 (by rfl) ⟨7082690, by rfl⟩ : syracuseStep 9443587 = 14165381) B14165381
theorem B2210663 : Blo 1472556 2210663 := bstep (se 1 (by rfl) ⟨1657997, by rfl⟩ : syracuseStep 2210663 = 3315995) B3315995
theorem B2210681 : Blo 1472556 2210681 := bstep (se 2 (by rfl) ⟨829005, by rfl⟩ : syracuseStep 2210681 = 1658011) B1658011
theorem B10615789 : Blo 1472556 10615789 := bstep (se 3 (by rfl) ⟨1990460, by rfl⟩ : syracuseStep 10615789 = 3980921) B3980921
theorem B2211071 : Blo 1472556 2211071 := bstep (se 1 (by rfl) ⟨1658303, by rfl⟩ : syracuseStep 2211071 = 3316607) B3316607
theorem B1769087 : Blo 1472556 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B1474175 : Blo 1472556 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B77610757 : Blo 1472556 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B1593778027 : Blo 1472556 1593778027 := bstep (se 1 (by rfl) ⟨1195333520, by rfl⟩ : syracuseStep 1593778027 = 2390667041) B2390667041
theorem B12591449 : Blo 1472556 12591449 := bstep (se 2 (by rfl) ⟨4721793, by rfl⟩ : syracuseStep 12591449 = 9443587) B9443587
theorem B4973561 : Blo 1472556 4973561 := bstep (se 2 (by rfl) ⟨1865085, by rfl⟩ : syracuseStep 4973561 = 3730171) B3730171
theorem B26870939 : Blo 1472556 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B38257915 : Blo 1472556 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B10626515 : Blo 1472556 10626515 := bstep (se 1 (by rfl) ⟨7969886, by rfl⟩ : syracuseStep 10626515 = 15939773) B15939773
theorem B9439001 : Blo 1472556 9439001 := bstep (se 2 (by rfl) ⟨3539625, by rfl⟩ : syracuseStep 9439001 = 7079251) B7079251
theorem B3147913 : Blo 1472556 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B8964371 : Blo 1472556 8964371 := bstep (se 1 (by rfl) ⟨6723278, by rfl⟩ : syracuseStep 8964371 = 13446557) B13446557
theorem B5310953 : Blo 1472556 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B2837371 : Blo 1472556 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B5598143 : Blo 1472556 5598143 := bstep (se 1 (by rfl) ⟨4198607, by rfl⟩ : syracuseStep 5598143 = 8397215) B8397215
theorem B5975209 : Blo 1472556 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B3730657 : Blo 1472556 3730657 := bstep (se 2 (by rfl) ⟨1398996, by rfl⟩ : syracuseStep 3730657 = 2797993) B2797993
theorem B21246569 : Blo 1472556 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B18888299 : Blo 1472556 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B32316515 : Blo 1472556 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B2209535 : Blo 1472556 2209535 := bstep (se 1 (by rfl) ⟨1657151, by rfl⟩ : syracuseStep 2209535 = 3314303) B3314303
theorem B2209703 : Blo 1472556 2209703 := bstep (se 1 (by rfl) ⟨1657277, by rfl⟩ : syracuseStep 2209703 = 3314555) B3314555
theorem B459364283 : Blo 1472556 459364283 := bstep (se 1 (by rfl) ⟨344523212, by rfl⟩ : syracuseStep 459364283 = 689046425) B689046425
theorem B1472603 : Blo 1472556 1472603 := bstep (se 1 (by rfl) ⟨1104452, by rfl⟩ : syracuseStep 1472603 = 2208905) B2208905
theorem B92010599 : Blo 1472556 92010599 := bstep (se 1 (by rfl) ⟨69007949, by rfl⟩ : syracuseStep 92010599 = 138015899) B138015899
theorem B3315887 : Blo 1472556 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B15939949 : Blo 1472556 15939949 := bstep (se 3 (by rfl) ⟨2988740, by rfl⟩ : syracuseStep 15939949 = 5977481) B5977481
theorem B1472959 : Blo 1472556 1472959 := bstep (se 1 (by rfl) ⟨1104719, by rfl⟩ : syracuseStep 1472959 = 2209439) B2209439
theorem B14154385 : Blo 1472556 14154385 := bstep (se 2 (by rfl) ⟨5307894, by rfl⟩ : syracuseStep 14154385 = 10615789) B10615789
theorem B1473255 : Blo 1472556 1473255 := bstep (se 1 (by rfl) ⟨1104941, by rfl⟩ : syracuseStep 1473255 = 2209883) B2209883
theorem B4717565 : Blo 1472556 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B1473775 : Blo 1472556 1473775 := bstep (se 1 (by rfl) ⟨1105331, by rfl⟩ : syracuseStep 1473775 = 2210663) B2210663
theorem B1473787 : Blo 1472556 1473787 := bstep (se 1 (by rfl) ⟨1105340, by rfl⟩ : syracuseStep 1473787 = 2210681) B2210681
theorem B1474047 : Blo 1472556 1474047 := bstep (se 1 (by rfl) ⟨1105535, by rfl⟩ : syracuseStep 1474047 = 2211071) B2211071
theorem B306110015 : Blo 1472556 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B4972103 : Blo 1472556 4972103 := bstep (se 1 (by rfl) ⟨3729077, by rfl⟩ : syracuseStep 4972103 = 7458155) B7458155
theorem B103481009 : Blo 1472556 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B3317471 : Blo 1472556 3317471 := bstep (se 1 (by rfl) ⟨2488103, by rfl⟩ : syracuseStep 3317471 = 4976207) B4976207
theorem B2125037369 : Blo 1472556 2125037369 := bstep (se 2 (by rfl) ⟨796889013, by rfl⟩ : syracuseStep 2125037369 = 1593778027) B1593778027
theorem B14164379 : Blo 1472556 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B23904989 : Blo 1472556 23904989 := bstep (se 3 (by rfl) ⟨4482185, by rfl⟩ : syracuseStep 23904989 = 8964371) B8964371
theorem B12592199 : Blo 1472556 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B6292667 : Blo 1472556 6292667 := bstep (se 1 (by rfl) ⟨4719500, by rfl⟩ : syracuseStep 6292667 = 9439001) B9439001
theorem B306242855 : Blo 1472556 306242855 := bstep (se 1 (by rfl) ⟨229682141, by rfl⟩ : syracuseStep 306242855 = 459364283) B459364283
theorem B4974209 : Blo 1472556 4974209 := bstep (se 2 (by rfl) ⟨1865328, by rfl⟩ : syracuseStep 4974209 = 3730657) B3730657
theorem B3540635 : Blo 1472556 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B204073343 : Blo 1472556 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B68987339 : Blo 1472556 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B21253265 : Blo 1472556 21253265 := bstep (se 2 (by rfl) ⟨7969974, by rfl⟩ : syracuseStep 21253265 = 15939949) B15939949
theorem B16788869 : Blo 1472556 16788869 := bstep (se 4 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 16788869 = 3147913) B3147913
theorem B7966945 : Blo 1472556 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B3732095 : Blo 1472556 3732095 := bstep (se 1 (by rfl) ⟨2799071, by rfl⟩ : syracuseStep 3732095 = 5598143) B5598143
theorem B3314735 : Blo 1472556 3314735 := bstep (se 1 (by rfl) ⟨2486051, by rfl⟩ : syracuseStep 3314735 = 4972103) B4972103
theorem B8394299 : Blo 1472556 8394299 := bstep (se 1 (by rfl) ⟨6295724, by rfl⟩ : syracuseStep 8394299 = 12591449) B12591449
theorem B3315707 : Blo 1472556 3315707 := bstep (se 1 (by rfl) ⟨2486780, by rfl⟩ : syracuseStep 3315707 = 4973561) B4973561
theorem B17913959 : Blo 1472556 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B18872513 : Blo 1472556 18872513 := bstep (se 2 (by rfl) ⟨7077192, by rfl⟩ : syracuseStep 18872513 = 14154385) B14154385
theorem B7084343 : Blo 1472556 7084343 := bstep (se 1 (by rfl) ⟨5313257, by rfl⟩ : syracuseStep 7084343 = 10626515) B10626515
theorem B21544343 : Blo 1472556 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B3783161 : Blo 1472556 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B1473023 : Blo 1472556 1473023 := bstep (se 1 (by rfl) ⟨1104767, by rfl⟩ : syracuseStep 1473023 = 2209535) B2209535
theorem B1473135 : Blo 1472556 1473135 := bstep (se 1 (by rfl) ⟨1104851, by rfl⟩ : syracuseStep 1473135 = 2209703) B2209703
theorem B61340399 : Blo 1472556 61340399 := bstep (se 1 (by rfl) ⟨46005299, by rfl⟩ : syracuseStep 61340399 = 92010599) B92010599
theorem B2210591 : Blo 1472556 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B51010553 : Blo 1472556 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B3145043 : Blo 1472556 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B2211647 : Blo 1472556 2211647 := bstep (se 1 (by rfl) ⟨1658735, by rfl⟩ : syracuseStep 2211647 = 3317471) B3317471
theorem B1416691579 : Blo 1472556 1416691579 := bstep (se 1 (by rfl) ⟨1062518684, by rfl⟩ : syracuseStep 1416691579 = 2125037369) B2125037369
theorem B4195111 : Blo 1472556 4195111 := bstep (se 1 (by rfl) ⟨3146333, by rfl⟩ : syracuseStep 4195111 = 6292667) B6292667
theorem B204161903 : Blo 1472556 204161903 := bstep (se 1 (by rfl) ⟨153121427, by rfl⟩ : syracuseStep 204161903 = 306242855) B306242855
theorem B5596199 : Blo 1472556 5596199 := bstep (se 1 (by rfl) ⟨4197149, by rfl⟩ : syracuseStep 5596199 = 8394299) B8394299
theorem B2360423 : Blo 1472556 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B45991559 : Blo 1472556 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B34007035 : Blo 1472556 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B11192579 : Blo 1472556 11192579 := bstep (se 1 (by rfl) ⟨8394434, by rfl⟩ : syracuseStep 11192579 = 16788869) B16788869
theorem B14362895 : Blo 1472556 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B1888922105 : Blo 1472556 1888922105 := bstep (se 2 (by rfl) ⟨708345789, by rfl⟩ : syracuseStep 1888922105 = 1416691579) B1416691579
theorem B15936659 : Blo 1472556 15936659 := bstep (se 1 (by rfl) ⟨11952494, by rfl⟩ : syracuseStep 15936659 = 23904989) B23904989
theorem B4722895 : Blo 1472556 4722895 := bstep (se 1 (by rfl) ⟨3542171, by rfl⟩ : syracuseStep 4722895 = 7084343) B7084343
theorem B136048895 : Blo 1472556 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B14168843 : Blo 1472556 14168843 := bstep (se 1 (by rfl) ⟨10626632, by rfl⟩ : syracuseStep 14168843 = 21253265) B21253265
theorem B9442919 : Blo 1472556 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B10622593 : Blo 1472556 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B2488063 : Blo 1472556 2488063 := bstep (se 1 (by rfl) ⟨1866047, by rfl⟩ : syracuseStep 2488063 = 3732095) B3732095
theorem B2209823 : Blo 1472556 2209823 := bstep (se 1 (by rfl) ⟨1657367, by rfl⟩ : syracuseStep 2209823 = 3314735) B3314735
theorem B8394799 : Blo 1472556 8394799 := bstep (se 1 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 8394799 = 12592199) B12592199
theorem B3316139 : Blo 1472556 3316139 := bstep (se 1 (by rfl) ⟨2487104, by rfl⟩ : syracuseStep 3316139 = 4974209) B4974209
theorem B2210471 : Blo 1472556 2210471 := bstep (se 1 (by rfl) ⟨1657853, by rfl⟩ : syracuseStep 2210471 = 3315707) B3315707
theorem B11942639 : Blo 1472556 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B12581675 : Blo 1472556 12581675 := bstep (se 1 (by rfl) ⟨9436256, by rfl⟩ : syracuseStep 12581675 = 18872513) B18872513
theorem B2522107 : Blo 1472556 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B40893599 : Blo 1472556 40893599 := bstep (se 1 (by rfl) ⟨30670199, by rfl⟩ : syracuseStep 40893599 = 61340399) B61340399
theorem B1473727 : Blo 1472556 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B2096695 : Blo 1472556 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B1474431 : Blo 1472556 1474431 := bstep (se 1 (by rfl) ⟨1105823, by rfl⟩ : syracuseStep 1474431 = 2211647) B2211647
theorem B11182373 : Blo 1472556 11182373 := bstep (se 4 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 11182373 = 2096695) B2096695
theorem B9445895 : Blo 1472556 9445895 := bstep (se 1 (by rfl) ⟨7084421, by rfl⟩ : syracuseStep 9445895 = 14168843) B14168843
theorem B1573615 : Blo 1472556 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B11193065 : Blo 1472556 11193065 := bstep (se 2 (by rfl) ⟨4197399, by rfl⟩ : syracuseStep 11193065 = 8394799) B8394799
theorem B3730799 : Blo 1472556 3730799 := bstep (se 1 (by rfl) ⟨2798099, by rfl⟩ : syracuseStep 3730799 = 5596199) B5596199
theorem B3362809 : Blo 1472556 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B90699263 : Blo 1472556 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B6297193 : Blo 1472556 6297193 := bstep (se 2 (by rfl) ⟨2361447, by rfl⟩ : syracuseStep 6297193 = 4722895) B4722895
theorem B109049597 : Blo 1472556 109049597 := bstep (se 3 (by rfl) ⟨20446799, by rfl⟩ : syracuseStep 109049597 = 40893599) B40893599
theorem B136107935 : Blo 1472556 136107935 := bstep (se 1 (by rfl) ⟨102080951, by rfl⟩ : syracuseStep 136107935 = 204161903) B204161903
theorem B5593481 : Blo 1472556 5593481 := bstep (se 2 (by rfl) ⟨2097555, by rfl⟩ : syracuseStep 5593481 = 4195111) B4195111
theorem B30661039 : Blo 1472556 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B1473215 : Blo 1472556 1473215 := bstep (se 1 (by rfl) ⟨1104911, by rfl⟩ : syracuseStep 1473215 = 2209823) B2209823
theorem B7461719 : Blo 1472556 7461719 := bstep (se 1 (by rfl) ⟨5596289, by rfl⟩ : syracuseStep 7461719 = 11192579) B11192579
theorem B9575263 : Blo 1472556 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B25181117 : Blo 1472556 25181117 := bstep (se 3 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 25181117 = 9442919) B9442919
theorem B2210759 : Blo 1472556 2210759 := bstep (se 1 (by rfl) ⟨1658069, by rfl⟩ : syracuseStep 2210759 = 3316139) B3316139
theorem B1259281403 : Blo 1472556 1259281403 := bstep (se 1 (by rfl) ⟨944461052, by rfl⟩ : syracuseStep 1259281403 = 1888922105) B1888922105
theorem B1473647 : Blo 1472556 1473647 := bstep (se 1 (by rfl) ⟨1105235, by rfl⟩ : syracuseStep 1473647 = 2210471) B2210471
theorem B7961759 : Blo 1472556 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B8387783 : Blo 1472556 8387783 := bstep (se 1 (by rfl) ⟨6290837, by rfl⟩ : syracuseStep 8387783 = 12581675) B12581675
theorem B10624439 : Blo 1472556 10624439 := bstep (se 1 (by rfl) ⟨7968329, by rfl⟩ : syracuseStep 10624439 = 15936659) B15936659
theorem B14163457 : Blo 1472556 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B3317417 : Blo 1472556 3317417 := bstep (se 2 (by rfl) ⟨1244031, by rfl⟩ : syracuseStep 3317417 = 2488063) B2488063
theorem B45342713 : Blo 1472556 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B7454915 : Blo 1472556 7454915 := bstep (se 1 (by rfl) ⟨5591186, by rfl⟩ : syracuseStep 7454915 = 11182373) B11182373
theorem B2098153 : Blo 1472556 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B60466175 : Blo 1472556 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B3728987 : Blo 1472556 3728987 := bstep (se 1 (by rfl) ⟨2796740, by rfl⟩ : syracuseStep 3728987 = 5593481) B5593481
theorem B4974479 : Blo 1472556 4974479 := bstep (se 1 (by rfl) ⟨3730859, by rfl⟩ : syracuseStep 4974479 = 7461719) B7461719
theorem B16787411 : Blo 1472556 16787411 := bstep (se 1 (by rfl) ⟨12590558, by rfl⟩ : syracuseStep 16787411 = 25181117) B25181117
theorem B18884609 : Blo 1472556 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B4483745 : Blo 1472556 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B40881385 : Blo 1472556 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B72699731 : Blo 1472556 72699731 := bstep (se 1 (by rfl) ⟨54524798, by rfl⟩ : syracuseStep 72699731 = 109049597) B109049597
theorem B90738623 : Blo 1472556 90738623 := bstep (se 1 (by rfl) ⟨68053967, by rfl⟩ : syracuseStep 90738623 = 136107935) B136107935
theorem B839520935 : Blo 1472556 839520935 := bstep (se 1 (by rfl) ⟨629640701, by rfl⟩ : syracuseStep 839520935 = 1259281403) B1259281403
theorem B5591855 : Blo 1472556 5591855 := bstep (se 1 (by rfl) ⟨4193891, by rfl⟩ : syracuseStep 5591855 = 8387783) B8387783
theorem B2487199 : Blo 1472556 2487199 := bstep (se 1 (by rfl) ⟨1865399, by rfl⟩ : syracuseStep 2487199 = 3730799) B3730799
theorem B7082959 : Blo 1472556 7082959 := bstep (se 1 (by rfl) ⟨5312219, by rfl⟩ : syracuseStep 7082959 = 10624439) B10624439
theorem B6297263 : Blo 1472556 6297263 := bstep (se 1 (by rfl) ⟨4722947, by rfl⟩ : syracuseStep 6297263 = 9445895) B9445895
theorem B7462043 : Blo 1472556 7462043 := bstep (se 1 (by rfl) ⟨5596532, by rfl⟩ : syracuseStep 7462043 = 11193065) B11193065
theorem B51068069 : Blo 1472556 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B1473839 : Blo 1472556 1473839 := bstep (se 1 (by rfl) ⟨1105379, by rfl⟩ : syracuseStep 1473839 = 2210759) B2210759
theorem B5307839 : Blo 1472556 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B8396257 : Blo 1472556 8396257 := bstep (se 2 (by rfl) ⟨3148596, by rfl⟩ : syracuseStep 8396257 = 6297193) B6297193
theorem B2211611 : Blo 1472556 2211611 := bstep (se 1 (by rfl) ⟨1658708, by rfl⟩ : syracuseStep 2211611 = 3317417) B3317417
theorem B30228475 : Blo 1472556 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B3727903 : Blo 1472556 3727903 := bstep (se 1 (by rfl) ⟨2795927, by rfl⟩ : syracuseStep 3727903 = 5591855) B5591855
theorem B11191607 : Blo 1472556 11191607 := bstep (se 1 (by rfl) ⟨8393705, by rfl⟩ : syracuseStep 11191607 = 16787411) B16787411
theorem B4974695 : Blo 1472556 4974695 := bstep (se 1 (by rfl) ⟨3731021, by rfl⟩ : syracuseStep 4974695 = 7462043) B7462043
theorem B48466487 : Blo 1472556 48466487 := bstep (se 1 (by rfl) ⟨36349865, by rfl⟩ : syracuseStep 48466487 = 72699731) B72699731
theorem B60492415 : Blo 1472556 60492415 := bstep (se 1 (by rfl) ⟨45369311, by rfl⟩ : syracuseStep 60492415 = 90738623) B90738623
theorem B559680623 : Blo 1472556 559680623 := bstep (se 1 (by rfl) ⟨419760467, by rfl⟩ : syracuseStep 559680623 = 839520935) B839520935
theorem B2485991 : Blo 1472556 2485991 := bstep (se 1 (by rfl) ⟨1864493, by rfl⟩ : syracuseStep 2485991 = 3728987) B3728987
theorem B4198175 : Blo 1472556 4198175 := bstep (se 1 (by rfl) ⟨3148631, by rfl⟩ : syracuseStep 4198175 = 6297263) B6297263
theorem B11195009 : Blo 1472556 11195009 := bstep (se 2 (by rfl) ⟨4198128, by rfl⟩ : syracuseStep 11195009 = 8396257) B8396257
theorem B4969943 : Blo 1472556 4969943 := bstep (se 1 (by rfl) ⟨3727457, by rfl⟩ : syracuseStep 4969943 = 7454915) B7454915
theorem B40310783 : Blo 1472556 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B3316265 : Blo 1472556 3316265 := bstep (se 2 (by rfl) ⟨1243599, by rfl⟩ : syracuseStep 3316265 = 2487199) B2487199
theorem B3316319 : Blo 1472556 3316319 := bstep (se 1 (by rfl) ⟨2487239, by rfl⟩ : syracuseStep 3316319 = 4974479) B4974479
theorem B9443945 : Blo 1472556 9443945 := bstep (se 2 (by rfl) ⟨3541479, by rfl⟩ : syracuseStep 9443945 = 7082959) B7082959
theorem B12589739 : Blo 1472556 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B54508513 : Blo 1472556 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B2989163 : Blo 1472556 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B34045379 : Blo 1472556 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B3538559 : Blo 1472556 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B1474407 : Blo 1472556 1474407 := bstep (se 1 (by rfl) ⟨1105805, by rfl⟩ : syracuseStep 1474407 = 2211611) B2211611
theorem B11190149 : Blo 1472556 11190149 := bstep (se 4 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 11190149 = 2098153) B2098153
theorem B40304633 : Blo 1472556 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B7463339 : Blo 1472556 7463339 := bstep (se 1 (by rfl) ⟨5597504, by rfl⟩ : syracuseStep 7463339 = 11195009) B11195009
theorem B32310991 : Blo 1472556 32310991 := bstep (se 1 (by rfl) ⟨24233243, by rfl⟩ : syracuseStep 32310991 = 48466487) B48466487
theorem B1992775 : Blo 1472556 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B1657327 : Blo 1472556 1657327 := bstep (se 1 (by rfl) ⟨1242995, by rfl⟩ : syracuseStep 1657327 = 2485991) B2485991
theorem B3313295 : Blo 1472556 3313295 := bstep (se 1 (by rfl) ⟨2484971, by rfl⟩ : syracuseStep 3313295 = 4969943) B4969943
theorem B26873855 : Blo 1472556 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B6295963 : Blo 1472556 6295963 := bstep (se 1 (by rfl) ⟨4721972, by rfl⟩ : syracuseStep 6295963 = 9443945) B9443945
theorem B8393159 : Blo 1472556 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B22696919 : Blo 1472556 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B2798783 : Blo 1472556 2798783 := bstep (se 1 (by rfl) ⟨2099087, by rfl⟩ : syracuseStep 2798783 = 4198175) B4198175
theorem B7460099 : Blo 1472556 7460099 := bstep (se 1 (by rfl) ⟨5595074, by rfl⟩ : syracuseStep 7460099 = 11190149) B11190149
theorem B4970537 : Blo 1472556 4970537 := bstep (se 2 (by rfl) ⟨1863951, by rfl⟩ : syracuseStep 4970537 = 3727903) B3727903
theorem B80656553 : Blo 1472556 80656553 := bstep (se 2 (by rfl) ⟨30246207, by rfl⟩ : syracuseStep 80656553 = 60492415) B60492415
theorem B7461071 : Blo 1472556 7461071 := bstep (se 1 (by rfl) ⟨5595803, by rfl⟩ : syracuseStep 7461071 = 11191607) B11191607
theorem B72678017 : Blo 1472556 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B3316463 : Blo 1472556 3316463 := bstep (se 1 (by rfl) ⟨2487347, by rfl⟩ : syracuseStep 3316463 = 4974695) B4974695
theorem B2210843 : Blo 1472556 2210843 := bstep (se 1 (by rfl) ⟨1658132, by rfl⟩ : syracuseStep 2210843 = 3316265) B3316265
theorem B2210879 : Blo 1472556 2210879 := bstep (se 1 (by rfl) ⟨1658159, by rfl⟩ : syracuseStep 2210879 = 3316319) B3316319
theorem B373120415 : Blo 1472556 373120415 := bstep (se 1 (by rfl) ⟨279840311, by rfl⟩ : syracuseStep 373120415 = 559680623) B559680623
theorem B2359039 : Blo 1472556 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B107479021 : Blo 1472556 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B5595439 : Blo 1472556 5595439 := bstep (se 1 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 5595439 = 8393159) B8393159
theorem B15131279 : Blo 1472556 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B4973399 : Blo 1472556 4973399 := bstep (se 1 (by rfl) ⟨3730049, by rfl⟩ : syracuseStep 4973399 = 7460099) B7460099
theorem B4974047 : Blo 1472556 4974047 := bstep (se 1 (by rfl) ⟨3730535, by rfl⟩ : syracuseStep 4974047 = 7461071) B7461071
theorem B193808045 : Blo 1472556 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B143305361 : Blo 1472556 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B17915903 : Blo 1472556 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B2657033 : Blo 1472556 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B4975559 : Blo 1472556 4975559 := bstep (se 1 (by rfl) ⟨3731669, by rfl⟩ : syracuseStep 4975559 = 7463339) B7463339
theorem B3313691 : Blo 1472556 3313691 := bstep (se 1 (by rfl) ⟨2485268, by rfl⟩ : syracuseStep 3313691 = 4970537) B4970537
theorem B248746943 : Blo 1472556 248746943 := bstep (se 1 (by rfl) ⟨186560207, by rfl⟩ : syracuseStep 248746943 = 373120415) B373120415
theorem B2208863 : Blo 1472556 2208863 := bstep (se 1 (by rfl) ⟨1656647, by rfl⟩ : syracuseStep 2208863 = 3313295) B3313295
theorem B8394617 : Blo 1472556 8394617 := bstep (se 2 (by rfl) ⟨3147981, by rfl⟩ : syracuseStep 8394617 = 6295963) B6295963
theorem B2209769 : Blo 1472556 2209769 := bstep (se 2 (by rfl) ⟨828663, by rfl⟩ : syracuseStep 2209769 = 1657327) B1657327
theorem B1865855 : Blo 1472556 1865855 := bstep (se 1 (by rfl) ⟨1399391, by rfl⟩ : syracuseStep 1865855 = 2798783) B2798783
theorem B53771035 : Blo 1472556 53771035 := bstep (se 1 (by rfl) ⟨40328276, by rfl⟩ : syracuseStep 53771035 = 80656553) B80656553
theorem B2210975 : Blo 1472556 2210975 := bstep (se 1 (by rfl) ⟨1658231, by rfl⟩ : syracuseStep 2210975 = 3316463) B3316463
theorem B1473895 : Blo 1472556 1473895 := bstep (se 1 (by rfl) ⟨1105421, by rfl⟩ : syracuseStep 1473895 = 2210843) B2210843
theorem B1473919 : Blo 1472556 1473919 := bstep (se 1 (by rfl) ⟨1105439, by rfl⟩ : syracuseStep 1473919 = 2210879) B2210879
theorem B43081321 : Blo 1472556 43081321 := bstep (se 2 (by rfl) ⟨16155495, by rfl⟩ : syracuseStep 43081321 = 32310991) B32310991
theorem B3145385 : Blo 1472556 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B165831295 : Blo 1472556 165831295 := bstep (se 1 (by rfl) ⟨124373471, by rfl⟩ : syracuseStep 165831295 = 248746943) B248746943
theorem B129205363 : Blo 1472556 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B5596411 : Blo 1472556 5596411 := bstep (se 1 (by rfl) ⟨4197308, by rfl⟩ : syracuseStep 5596411 = 8394617) B8394617
theorem B95536907 : Blo 1472556 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B1771355 : Blo 1472556 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B4975613 : Blo 1472556 4975613 := bstep (se 3 (by rfl) ⟨932927, by rfl⟩ : syracuseStep 4975613 = 1865855) B1865855
theorem B10087519 : Blo 1472556 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B11943935 : Blo 1472556 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B2209127 : Blo 1472556 2209127 := bstep (se 1 (by rfl) ⟨1656845, by rfl⟩ : syracuseStep 2209127 = 3313691) B3313691
theorem B7460585 : Blo 1472556 7460585 := bstep (se 2 (by rfl) ⟨2797719, by rfl⟩ : syracuseStep 7460585 = 5595439) B5595439
theorem B3315599 : Blo 1472556 3315599 := bstep (se 1 (by rfl) ⟨2486699, by rfl⟩ : syracuseStep 3315599 = 4973399) B4973399
theorem B1472575 : Blo 1472556 1472575 := bstep (se 1 (by rfl) ⟨1104431, by rfl⟩ : syracuseStep 1472575 = 2208863) B2208863
theorem B3316031 : Blo 1472556 3316031 := bstep (se 1 (by rfl) ⟨2487023, by rfl⟩ : syracuseStep 3316031 = 4974047) B4974047
theorem B71694713 : Blo 1472556 71694713 := bstep (se 2 (by rfl) ⟨26885517, by rfl⟩ : syracuseStep 71694713 = 53771035) B53771035
theorem B1473179 : Blo 1472556 1473179 := bstep (se 1 (by rfl) ⟨1104884, by rfl⟩ : syracuseStep 1473179 = 2209769) B2209769
theorem B3317039 : Blo 1472556 3317039 := bstep (se 1 (by rfl) ⟨2487779, by rfl⟩ : syracuseStep 3317039 = 4975559) B4975559
theorem B1473983 : Blo 1472556 1473983 := bstep (se 1 (by rfl) ⟨1105487, by rfl⟩ : syracuseStep 1473983 = 2210975) B2210975
theorem B57441761 : Blo 1472556 57441761 := bstep (se 2 (by rfl) ⟨21540660, by rfl⟩ : syracuseStep 57441761 = 43081321) B43081321
theorem B2096923 : Blo 1472556 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B4973723 : Blo 1472556 4973723 := bstep (se 1 (by rfl) ⟨3730292, by rfl⟩ : syracuseStep 4973723 = 7460585) B7460585
theorem B2795897 : Blo 1472556 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B7962623 : Blo 1472556 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B172273817 : Blo 1472556 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B47796475 : Blo 1472556 47796475 := bstep (se 1 (by rfl) ⟨35847356, by rfl⟩ : syracuseStep 47796475 = 71694713) B71694713
theorem B4723613 : Blo 1472556 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B38294507 : Blo 1472556 38294507 := bstep (se 1 (by rfl) ⟨28720880, by rfl⟩ : syracuseStep 38294507 = 57441761) B57441761
theorem B221108393 : Blo 1472556 221108393 := bstep (se 2 (by rfl) ⟨82915647, by rfl⟩ : syracuseStep 221108393 = 165831295) B165831295
theorem B1472751 : Blo 1472556 1472751 := bstep (se 1 (by rfl) ⟨1104563, by rfl⟩ : syracuseStep 1472751 = 2209127) B2209127
theorem B63691271 : Blo 1472556 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B2210399 : Blo 1472556 2210399 := bstep (se 1 (by rfl) ⟨1657799, by rfl⟩ : syracuseStep 2210399 = 3315599) B3315599
theorem B13450025 : Blo 1472556 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B2210687 : Blo 1472556 2210687 := bstep (se 1 (by rfl) ⟨1658015, by rfl⟩ : syracuseStep 2210687 = 3316031) B3316031
theorem B7461881 : Blo 1472556 7461881 := bstep (se 2 (by rfl) ⟨2798205, by rfl⟩ : syracuseStep 7461881 = 5596411) B5596411
theorem B3317075 : Blo 1472556 3317075 := bstep (se 1 (by rfl) ⟨2487806, by rfl⟩ : syracuseStep 3317075 = 4975613) B4975613
theorem B2211359 : Blo 1472556 2211359 := bstep (se 1 (by rfl) ⟨1658519, by rfl⟩ : syracuseStep 2211359 = 3317039) B3317039
theorem B7455725 : Blo 1472556 7455725 := bstep (se 3 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 7455725 = 2795897) B2795897
theorem B42460847 : Blo 1472556 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B5308415 : Blo 1472556 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B4974587 : Blo 1472556 4974587 := bstep (se 1 (by rfl) ⟨3730940, by rfl⟩ : syracuseStep 4974587 = 7461881) B7461881
theorem B63728633 : Blo 1472556 63728633 := bstep (se 2 (by rfl) ⟨23898237, by rfl⟩ : syracuseStep 63728633 = 47796475) B47796475
theorem B3149075 : Blo 1472556 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B25529671 : Blo 1472556 25529671 := bstep (se 1 (by rfl) ⟨19147253, by rfl⟩ : syracuseStep 25529671 = 38294507) B38294507
theorem B8966683 : Blo 1472556 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B459396845 : Blo 1472556 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B3315815 : Blo 1472556 3315815 := bstep (se 1 (by rfl) ⟨2486861, by rfl⟩ : syracuseStep 3315815 = 4973723) B4973723
theorem B147405595 : Blo 1472556 147405595 := bstep (se 1 (by rfl) ⟨110554196, by rfl⟩ : syracuseStep 147405595 = 221108393) B221108393
theorem B1473599 : Blo 1472556 1473599 := bstep (se 1 (by rfl) ⟨1105199, by rfl⟩ : syracuseStep 1473599 = 2210399) B2210399
theorem B1473791 : Blo 1472556 1473791 := bstep (se 1 (by rfl) ⟨1105343, by rfl⟩ : syracuseStep 1473791 = 2210687) B2210687
theorem B2211383 : Blo 1472556 2211383 := bstep (se 1 (by rfl) ⟨1658537, by rfl⟩ : syracuseStep 2211383 = 3317075) B3317075
theorem B1474239 : Blo 1472556 1474239 := bstep (se 1 (by rfl) ⟨1105679, by rfl⟩ : syracuseStep 1474239 = 2211359) B2211359
theorem B8397533 : Blo 1472556 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B34039561 : Blo 1472556 34039561 := bstep (se 2 (by rfl) ⟨12764835, by rfl⟩ : syracuseStep 34039561 = 25529671) B25529671
theorem B42485755 : Blo 1472556 42485755 := bstep (se 1 (by rfl) ⟨31864316, by rfl⟩ : syracuseStep 42485755 = 63728633) B63728633
theorem B28307231 : Blo 1472556 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B3538943 : Blo 1472556 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B47822309 : Blo 1472556 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B4970483 : Blo 1472556 4970483 := bstep (se 1 (by rfl) ⟨3727862, by rfl⟩ : syracuseStep 4970483 = 7455725) B7455725
theorem B196540793 : Blo 1472556 196540793 := bstep (se 2 (by rfl) ⟨73702797, by rfl⟩ : syracuseStep 196540793 = 147405595) B147405595
theorem B306264563 : Blo 1472556 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B3316391 : Blo 1472556 3316391 := bstep (se 1 (by rfl) ⟨2487293, by rfl⟩ : syracuseStep 3316391 = 4974587) B4974587
theorem B2210543 : Blo 1472556 2210543 := bstep (se 1 (by rfl) ⟨1657907, by rfl⟩ : syracuseStep 2210543 = 3315815) B3315815
theorem B1474255 : Blo 1472556 1474255 := bstep (se 1 (by rfl) ⟨1105691, by rfl⟩ : syracuseStep 1474255 = 2211383) B2211383
theorem B56647673 : Blo 1472556 56647673 := bstep (se 2 (by rfl) ⟨21242877, by rfl⟩ : syracuseStep 56647673 = 42485755) B42485755
theorem B45386081 : Blo 1472556 45386081 := bstep (se 2 (by rfl) ⟨17019780, by rfl⟩ : syracuseStep 45386081 = 34039561) B34039561
theorem B5598355 : Blo 1472556 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B3313655 : Blo 1472556 3313655 := bstep (se 1 (by rfl) ⟨2485241, by rfl⟩ : syracuseStep 3313655 = 4970483) B4970483
theorem B131027195 : Blo 1472556 131027195 := bstep (se 1 (by rfl) ⟨98270396, by rfl⟩ : syracuseStep 131027195 = 196540793) B196540793
theorem B18871487 : Blo 1472556 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B31881539 : Blo 1472556 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B204176375 : Blo 1472556 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B2210927 : Blo 1472556 2210927 := bstep (se 1 (by rfl) ⟨1658195, by rfl⟩ : syracuseStep 2210927 = 3316391) B3316391
theorem B1473695 : Blo 1472556 1473695 := bstep (se 1 (by rfl) ⟨1105271, by rfl⟩ : syracuseStep 1473695 = 2210543) B2210543
theorem B2359295 : Blo 1472556 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B87351463 : Blo 1472556 87351463 := bstep (se 1 (by rfl) ⟨65513597, by rfl⟩ : syracuseStep 87351463 = 131027195) B131027195
theorem B37765115 : Blo 1472556 37765115 := bstep (se 1 (by rfl) ⟨28323836, by rfl⟩ : syracuseStep 37765115 = 56647673) B56647673
theorem B1572863 : Blo 1472556 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B7464473 : Blo 1472556 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B21254359 : Blo 1472556 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B30257387 : Blo 1472556 30257387 := bstep (se 1 (by rfl) ⟨22693040, by rfl⟩ : syracuseStep 30257387 = 45386081) B45386081
theorem B2209103 : Blo 1472556 2209103 := bstep (se 1 (by rfl) ⟨1656827, by rfl⟩ : syracuseStep 2209103 = 3313655) B3313655
theorem B12580991 : Blo 1472556 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B136117583 : Blo 1472556 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B1473951 : Blo 1472556 1473951 := bstep (se 1 (by rfl) ⟨1105463, by rfl⟩ : syracuseStep 1473951 = 2210927) B2210927
theorem B90745055 : Blo 1472556 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B25176743 : Blo 1472556 25176743 := bstep (se 1 (by rfl) ⟨18882557, by rfl⟩ : syracuseStep 25176743 = 37765115) B37765115
theorem B20171591 : Blo 1472556 20171591 := bstep (se 1 (by rfl) ⟨15128693, by rfl⟩ : syracuseStep 20171591 = 30257387) B30257387
theorem B116468617 : Blo 1472556 116468617 := bstep (se 2 (by rfl) ⟨43675731, by rfl⟩ : syracuseStep 116468617 = 87351463) B87351463
theorem B28339145 : Blo 1472556 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B4976315 : Blo 1472556 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B1472735 : Blo 1472556 1472735 := bstep (se 1 (by rfl) ⟨1104551, by rfl⟩ : syracuseStep 1472735 = 2209103) B2209103
theorem B8387327 : Blo 1472556 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B16777205 : Blo 1472556 16777205 := bstep (se 5 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 16777205 = 1572863) B1572863
theorem B18892763 : Blo 1472556 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B11184803 : Blo 1472556 11184803 := bstep (se 1 (by rfl) ⟨8388602, by rfl⟩ : syracuseStep 11184803 = 16777205) B16777205
theorem B155291489 : Blo 1472556 155291489 := bstep (se 2 (by rfl) ⟨58234308, by rfl⟩ : syracuseStep 155291489 = 116468617) B116468617
theorem B5591551 : Blo 1472556 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B13447727 : Blo 1472556 13447727 := bstep (se 1 (by rfl) ⟨10085795, by rfl⟩ : syracuseStep 13447727 = 20171591) B20171591
theorem B60496703 : Blo 1472556 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B16784495 : Blo 1472556 16784495 := bstep (se 1 (by rfl) ⟨12588371, by rfl⟩ : syracuseStep 16784495 = 25176743) B25176743
theorem B3317543 : Blo 1472556 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B7455401 : Blo 1472556 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B7456535 : Blo 1472556 7456535 := bstep (se 1 (by rfl) ⟨5592401, by rfl⟩ : syracuseStep 7456535 = 11184803) B11184803
theorem B40331135 : Blo 1472556 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B8965151 : Blo 1472556 8965151 := bstep (se 1 (by rfl) ⟨6723863, by rfl⟩ : syracuseStep 8965151 = 13447727) B13447727
theorem B12595175 : Blo 1472556 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B103527659 : Blo 1472556 103527659 := bstep (se 1 (by rfl) ⟨77645744, by rfl⟩ : syracuseStep 103527659 = 155291489) B155291489
theorem B11189663 : Blo 1472556 11189663 := bstep (se 1 (by rfl) ⟨8392247, by rfl⟩ : syracuseStep 11189663 = 16784495) B16784495
theorem B2211695 : Blo 1472556 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B26887423 : Blo 1472556 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B276073757 : Blo 1472556 276073757 := bstep (se 3 (by rfl) ⟨51763829, by rfl⟩ : syracuseStep 276073757 = 103527659) B103527659
theorem B5976767 : Blo 1472556 5976767 := bstep (se 1 (by rfl) ⟨4482575, by rfl⟩ : syracuseStep 5976767 = 8965151) B8965151
theorem B7459775 : Blo 1472556 7459775 := bstep (se 1 (by rfl) ⟨5594831, by rfl⟩ : syracuseStep 7459775 = 11189663) B11189663
theorem B4970267 : Blo 1472556 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B4971023 : Blo 1472556 4971023 := bstep (se 1 (by rfl) ⟨3728267, by rfl⟩ : syracuseStep 4971023 = 7456535) B7456535
theorem B1474463 : Blo 1472556 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B8396783 : Blo 1472556 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B4973183 : Blo 1472556 4973183 := bstep (se 1 (by rfl) ⟨3729887, by rfl⟩ : syracuseStep 4973183 = 7459775) B7459775
theorem B35849897 : Blo 1472556 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B5597855 : Blo 1472556 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B3313511 : Blo 1472556 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B3314015 : Blo 1472556 3314015 := bstep (se 1 (by rfl) ⟨2485511, by rfl⟩ : syracuseStep 3314015 = 4971023) B4971023
theorem B15938045 : Blo 1472556 15938045 := bstep (se 3 (by rfl) ⟨2988383, by rfl⟩ : syracuseStep 15938045 = 5976767) B5976767
theorem B184049171 : Blo 1472556 184049171 := bstep (se 1 (by rfl) ⟨138036878, by rfl⟩ : syracuseStep 184049171 = 276073757) B276073757
theorem B10625363 : Blo 1472556 10625363 := bstep (se 1 (by rfl) ⟨7969022, by rfl⟩ : syracuseStep 10625363 = 15938045) B15938045
theorem B23899931 : Blo 1472556 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B3731903 : Blo 1472556 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B2209007 : Blo 1472556 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B2209343 : Blo 1472556 2209343 := bstep (se 1 (by rfl) ⟨1657007, by rfl⟩ : syracuseStep 2209343 = 3314015) B3314015
theorem B3315455 : Blo 1472556 3315455 := bstep (se 1 (by rfl) ⟨2486591, by rfl⟩ : syracuseStep 3315455 = 4973183) B4973183
theorem B122699447 : Blo 1472556 122699447 := bstep (se 1 (by rfl) ⟨92024585, by rfl⟩ : syracuseStep 122699447 = 184049171) B184049171
theorem B81799631 : Blo 1472556 81799631 := bstep (se 1 (by rfl) ⟨61349723, by rfl⟩ : syracuseStep 81799631 = 122699447) B122699447
theorem B7083575 : Blo 1472556 7083575 := bstep (se 1 (by rfl) ⟨5312681, by rfl⟩ : syracuseStep 7083575 = 10625363) B10625363
theorem B2487935 : Blo 1472556 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B1472671 : Blo 1472556 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B1472895 : Blo 1472556 1472895 := bstep (se 1 (by rfl) ⟨1104671, by rfl⟩ : syracuseStep 1472895 = 2209343) B2209343
theorem B2210303 : Blo 1472556 2210303 := bstep (se 1 (by rfl) ⟨1657727, by rfl⟩ : syracuseStep 2210303 = 3315455) B3315455
theorem B15933287 : Blo 1472556 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B4722383 : Blo 1472556 4722383 := bstep (se 1 (by rfl) ⟨3541787, by rfl⟩ : syracuseStep 4722383 = 7083575) B7083575
theorem B1658623 : Blo 1472556 1658623 := bstep (se 1 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 1658623 = 2487935) B2487935
theorem B10622191 : Blo 1472556 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B54533087 : Blo 1472556 54533087 := bstep (se 1 (by rfl) ⟨40899815, by rfl⟩ : syracuseStep 54533087 = 81799631) B81799631
theorem B1473535 : Blo 1472556 1473535 := bstep (se 1 (by rfl) ⟨1105151, by rfl⟩ : syracuseStep 1473535 = 2210303) B2210303
theorem B3148255 : Blo 1472556 3148255 := bstep (se 1 (by rfl) ⟨2361191, by rfl⟩ : syracuseStep 3148255 = 4722383) B4722383
theorem B14162921 : Blo 1472556 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B36355391 : Blo 1472556 36355391 := bstep (se 1 (by rfl) ⟨27266543, by rfl⟩ : syracuseStep 36355391 = 54533087) B54533087
theorem B2211497 : Blo 1472556 2211497 := bstep (se 2 (by rfl) ⟨829311, by rfl⟩ : syracuseStep 2211497 = 1658623) B1658623
theorem B4197673 : Blo 1472556 4197673 := bstep (se 2 (by rfl) ⟨1574127, by rfl⟩ : syracuseStep 4197673 = 3148255) B3148255
theorem B9441947 : Blo 1472556 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B24236927 : Blo 1472556 24236927 := bstep (se 1 (by rfl) ⟨18177695, by rfl⟩ : syracuseStep 24236927 = 36355391) B36355391
theorem B1474331 : Blo 1472556 1474331 := bstep (se 1 (by rfl) ⟨1105748, by rfl⟩ : syracuseStep 1474331 = 2211497) B2211497
theorem B5596897 : Blo 1472556 5596897 := bstep (se 2 (by rfl) ⟨2098836, by rfl⟩ : syracuseStep 5596897 = 4197673) B4197673
theorem B6294631 : Blo 1472556 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B16157951 : Blo 1472556 16157951 := bstep (se 1 (by rfl) ⟨12118463, by rfl⟩ : syracuseStep 16157951 = 24236927) B24236927
theorem B8392841 : Blo 1472556 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B10771967 : Blo 1472556 10771967 := bstep (se 1 (by rfl) ⟨8078975, by rfl⟩ : syracuseStep 10771967 = 16157951) B16157951
theorem B7462529 : Blo 1472556 7462529 := bstep (se 2 (by rfl) ⟨2798448, by rfl⟩ : syracuseStep 7462529 = 5596897) B5596897
theorem B5595227 : Blo 1472556 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B4975019 : Blo 1472556 4975019 := bstep (se 1 (by rfl) ⟨3731264, by rfl⟩ : syracuseStep 4975019 = 7462529) B7462529
theorem B7181311 : Blo 1472556 7181311 := bstep (se 1 (by rfl) ⟨5385983, by rfl⟩ : syracuseStep 7181311 = 10771967) B10771967
theorem B3730151 : Blo 1472556 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B9575081 : Blo 1472556 9575081 := bstep (se 2 (by rfl) ⟨3590655, by rfl⟩ : syracuseStep 9575081 = 7181311) B7181311
theorem B3316679 : Blo 1472556 3316679 := bstep (se 1 (by rfl) ⟨2487509, by rfl⟩ : syracuseStep 3316679 = 4975019) B4975019
theorem B6383387 : Blo 1472556 6383387 := bstep (se 1 (by rfl) ⟨4787540, by rfl⟩ : syracuseStep 6383387 = 9575081) B9575081
theorem B2486767 : Blo 1472556 2486767 := bstep (se 1 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 2486767 = 3730151) B3730151
theorem B2211119 : Blo 1472556 2211119 := bstep (se 1 (by rfl) ⟨1658339, by rfl⟩ : syracuseStep 2211119 = 3316679) B3316679
theorem B4255591 : Blo 1472556 4255591 := bstep (se 1 (by rfl) ⟨3191693, by rfl⟩ : syracuseStep 4255591 = 6383387) B6383387
theorem B3315689 : Blo 1472556 3315689 := bstep (se 2 (by rfl) ⟨1243383, by rfl⟩ : syracuseStep 3315689 = 2486767) B2486767
theorem B1474079 : Blo 1472556 1474079 := bstep (se 1 (by rfl) ⟨1105559, by rfl⟩ : syracuseStep 1474079 = 2211119) B2211119
theorem B5674121 : Blo 1472556 5674121 := bstep (se 2 (by rfl) ⟨2127795, by rfl⟩ : syracuseStep 5674121 = 4255591) B4255591
theorem B2210459 : Blo 1472556 2210459 := bstep (se 1 (by rfl) ⟨1657844, by rfl⟩ : syracuseStep 2210459 = 3315689) B3315689
theorem B3782747 : Blo 1472556 3782747 := bstep (se 1 (by rfl) ⟨2837060, by rfl⟩ : syracuseStep 3782747 = 5674121) B5674121
theorem B1473639 : Blo 1472556 1473639 := bstep (se 1 (by rfl) ⟨1105229, by rfl⟩ : syracuseStep 1473639 = 2210459) B2210459
theorem B2521831 : Blo 1472556 2521831 := bstep (se 1 (by rfl) ⟨1891373, by rfl⟩ : syracuseStep 2521831 = 3782747) B3782747
theorem B53799061 : Blo 1472556 53799061 := bstep (se 6 (by rfl) ⟨1260915, by rfl⟩ : syracuseStep 53799061 = 2521831) B2521831
theorem B71732081 : Blo 1472556 71732081 := bstep (se 2 (by rfl) ⟨26899530, by rfl⟩ : syracuseStep 71732081 = 53799061) B53799061
theorem B47821387 : Blo 1472556 47821387 := bstep (se 1 (by rfl) ⟨35866040, by rfl⟩ : syracuseStep 47821387 = 71732081) B71732081
theorem B63761849 : Blo 1472556 63761849 := bstep (se 2 (by rfl) ⟨23910693, by rfl⟩ : syracuseStep 63761849 = 47821387) B47821387
theorem B42507899 : Blo 1472556 42507899 := bstep (se 1 (by rfl) ⟨31880924, by rfl⟩ : syracuseStep 42507899 = 63761849) B63761849
theorem B28338599 : Blo 1472556 28338599 := bstep (se 1 (by rfl) ⟨21253949, by rfl⟩ : syracuseStep 28338599 = 42507899) B42507899
theorem B18892399 : Blo 1472556 18892399 := bstep (se 1 (by rfl) ⟨14169299, by rfl⟩ : syracuseStep 18892399 = 28338599) B28338599
theorem B25189865 : Blo 1472556 25189865 := bstep (se 2 (by rfl) ⟨9446199, by rfl⟩ : syracuseStep 25189865 = 18892399) B18892399
theorem B16793243 : Blo 1472556 16793243 := bstep (se 1 (by rfl) ⟨12594932, by rfl⟩ : syracuseStep 16793243 = 25189865) B25189865
theorem B11195495 : Blo 1472556 11195495 := bstep (se 1 (by rfl) ⟨8396621, by rfl⟩ : syracuseStep 11195495 = 16793243) B16793243
theorem B7463663 : Blo 1472556 7463663 := bstep (se 1 (by rfl) ⟨5597747, by rfl⟩ : syracuseStep 7463663 = 11195495) B11195495
theorem B4975775 : Blo 1472556 4975775 := bstep (se 1 (by rfl) ⟨3731831, by rfl⟩ : syracuseStep 4975775 = 7463663) B7463663
theorem B3317183 : Blo 1472556 3317183 := bstep (se 1 (by rfl) ⟨2487887, by rfl⟩ : syracuseStep 3317183 = 4975775) B4975775
theorem B2211455 : Blo 1472556 2211455 := bstep (se 1 (by rfl) ⟨1658591, by rfl⟩ : syracuseStep 2211455 = 3317183) B3317183
theorem B1474303 : Blo 1472556 1474303 := bstep (se 1 (by rfl) ⟨1105727, by rfl⟩ : syracuseStep 1474303 = 2211455) B2211455

theorem C0 (j : ℕ) (h1 : 368139 ≤ j) (h2 : j ≤ 368638) : Blo 1472556 (4 * j + 3) := by
  interval_cases j
  · exact B1472559
  · exact B1472563
  · exact B1472567
  · exact B1472571
  · exact B1472575
  · exact B1472579
  · exact B1472583
  · exact B1472587
  · exact B1472591
  · exact B1472595
  · exact B1472599
  · exact B1472603
  · exact B1472607
  · exact B1472611
  · exact B1472615
  · exact B1472619
  · exact B1472623
  · exact B1472627
  · exact B1472631
  · exact B1472635
  · exact B1472639
  · exact B1472643
  · exact B1472647
  · exact B1472651
  · exact B1472655
  · exact B1472659
  · exact B1472663
  · exact B1472667
  · exact B1472671
  · exact B1472675
  · exact B1472679
  · exact B1472683
  · exact B1472687
  · exact B1472691
  · exact B1472695
  · exact B1472699
  · exact B1472703
  · exact B1472707
  · exact B1472711
  · exact B1472715
  · exact B1472719
  · exact B1472723
  · exact B1472727
  · exact B1472731
  · exact B1472735
  · exact B1472739
  · exact B1472743
  · exact B1472747
  · exact B1472751
  · exact B1472755
  · exact B1472759
  · exact B1472763
  · exact B1472767
  · exact B1472771
  · exact B1472775
  · exact B1472779
  · exact B1472783
  · exact B1472787
  · exact B1472791
  · exact B1472795
  · exact B1472799
  · exact B1472803
  · exact B1472807
  · exact B1472811
  · exact B1472815
  · exact B1472819
  · exact B1472823
  · exact B1472827
  · exact B1472831
  · exact B1472835
  · exact B1472839
  · exact B1472843
  · exact B1472847
  · exact B1472851
  · exact B1472855
  · exact B1472859
  · exact B1472863
  · exact B1472867
  · exact B1472871
  · exact B1472875
  · exact B1472879
  · exact B1472883
  · exact B1472887
  · exact B1472891
  · exact B1472895
  · exact B1472899
  · exact B1472903
  · exact B1472907
  · exact B1472911
  · exact B1472915
  · exact B1472919
  · exact B1472923
  · exact B1472927
  · exact B1472931
  · exact B1472935
  · exact B1472939
  · exact B1472943
  · exact B1472947
  · exact B1472951
  · exact B1472955
  · exact B1472959
  · exact B1472963
  · exact B1472967
  · exact B1472971
  · exact B1472975
  · exact B1472979
  · exact B1472983
  · exact B1472987
  · exact B1472991
  · exact B1472995
  · exact B1472999
  · exact B1473003
  · exact B1473007
  · exact B1473011
  · exact B1473015
  · exact B1473019
  · exact B1473023
  · exact B1473027
  · exact B1473031
  · exact B1473035
  · exact B1473039
  · exact B1473043
  · exact B1473047
  · exact B1473051
  · exact B1473055
  · exact B1473059
  · exact B1473063
  · exact B1473067
  · exact B1473071
  · exact B1473075
  · exact B1473079
  · exact B1473083
  · exact B1473087
  · exact B1473091
  · exact B1473095
  · exact B1473099
  · exact B1473103
  · exact B1473107
  · exact B1473111
  · exact B1473115
  · exact B1473119
  · exact B1473123
  · exact B1473127
  · exact B1473131
  · exact B1473135
  · exact B1473139
  · exact B1473143
  · exact B1473147
  · exact B1473151
  · exact B1473155
  · exact B1473159
  · exact B1473163
  · exact B1473167
  · exact B1473171
  · exact B1473175
  · exact B1473179
  · exact B1473183
  · exact B1473187
  · exact B1473191
  · exact B1473195
  · exact B1473199
  · exact B1473203
  · exact B1473207
  · exact B1473211
  · exact B1473215
  · exact B1473219
  · exact B1473223
  · exact B1473227
  · exact B1473231
  · exact B1473235
  · exact B1473239
  · exact B1473243
  · exact B1473247
  · exact B1473251
  · exact B1473255
  · exact B1473259
  · exact B1473263
  · exact B1473267
  · exact B1473271
  · exact B1473275
  · exact B1473279
  · exact B1473283
  · exact B1473287
  · exact B1473291
  · exact B1473295
  · exact B1473299
  · exact B1473303
  · exact B1473307
  · exact B1473311
  · exact B1473315
  · exact B1473319
  · exact B1473323
  · exact B1473327
  · exact B1473331
  · exact B1473335
  · exact B1473339
  · exact B1473343
  · exact B1473347
  · exact B1473351
  · exact B1473355
  · exact B1473359
  · exact B1473363
  · exact B1473367
  · exact B1473371
  · exact B1473375
  · exact B1473379
  · exact B1473383
  · exact B1473387
  · exact B1473391
  · exact B1473395
  · exact B1473399
  · exact B1473403
  · exact B1473407
  · exact B1473411
  · exact B1473415
  · exact B1473419
  · exact B1473423
  · exact B1473427
  · exact B1473431
  · exact B1473435
  · exact B1473439
  · exact B1473443
  · exact B1473447
  · exact B1473451
  · exact B1473455
  · exact B1473459
  · exact B1473463
  · exact B1473467
  · exact B1473471
  · exact B1473475
  · exact B1473479
  · exact B1473483
  · exact B1473487
  · exact B1473491
  · exact B1473495
  · exact B1473499
  · exact B1473503
  · exact B1473507
  · exact B1473511
  · exact B1473515
  · exact B1473519
  · exact B1473523
  · exact B1473527
  · exact B1473531
  · exact B1473535
  · exact B1473539
  · exact B1473543
  · exact B1473547
  · exact B1473551
  · exact B1473555
  · exact B1473559
  · exact B1473563
  · exact B1473567
  · exact B1473571
  · exact B1473575
  · exact B1473579
  · exact B1473583
  · exact B1473587
  · exact B1473591
  · exact B1473595
  · exact B1473599
  · exact B1473603
  · exact B1473607
  · exact B1473611
  · exact B1473615
  · exact B1473619
  · exact B1473623
  · exact B1473627
  · exact B1473631
  · exact B1473635
  · exact B1473639
  · exact B1473643
  · exact B1473647
  · exact B1473651
  · exact B1473655
  · exact B1473659
  · exact B1473663
  · exact B1473667
  · exact B1473671
  · exact B1473675
  · exact B1473679
  · exact B1473683
  · exact B1473687
  · exact B1473691
  · exact B1473695
  · exact B1473699
  · exact B1473703
  · exact B1473707
  · exact B1473711
  · exact B1473715
  · exact B1473719
  · exact B1473723
  · exact B1473727
  · exact B1473731
  · exact B1473735
  · exact B1473739
  · exact B1473743
  · exact B1473747
  · exact B1473751
  · exact B1473755
  · exact B1473759
  · exact B1473763
  · exact B1473767
  · exact B1473771
  · exact B1473775
  · exact B1473779
  · exact B1473783
  · exact B1473787
  · exact B1473791
  · exact B1473795
  · exact B1473799
  · exact B1473803
  · exact B1473807
  · exact B1473811
  · exact B1473815
  · exact B1473819
  · exact B1473823
  · exact B1473827
  · exact B1473831
  · exact B1473835
  · exact B1473839
  · exact B1473843
  · exact B1473847
  · exact B1473851
  · exact B1473855
  · exact B1473859
  · exact B1473863
  · exact B1473867
  · exact B1473871
  · exact B1473875
  · exact B1473879
  · exact B1473883
  · exact B1473887
  · exact B1473891
  · exact B1473895
  · exact B1473899
  · exact B1473903
  · exact B1473907
  · exact B1473911
  · exact B1473915
  · exact B1473919
  · exact B1473923
  · exact B1473927
  · exact B1473931
  · exact B1473935
  · exact B1473939
  · exact B1473943
  · exact B1473947
  · exact B1473951
  · exact B1473955
  · exact B1473959
  · exact B1473963
  · exact B1473967
  · exact B1473971
  · exact B1473975
  · exact B1473979
  · exact B1473983
  · exact B1473987
  · exact B1473991
  · exact B1473995
  · exact B1473999
  · exact B1474003
  · exact B1474007
  · exact B1474011
  · exact B1474015
  · exact B1474019
  · exact B1474023
  · exact B1474027
  · exact B1474031
  · exact B1474035
  · exact B1474039
  · exact B1474043
  · exact B1474047
  · exact B1474051
  · exact B1474055
  · exact B1474059
  · exact B1474063
  · exact B1474067
  · exact B1474071
  · exact B1474075
  · exact B1474079
  · exact B1474083
  · exact B1474087
  · exact B1474091
  · exact B1474095
  · exact B1474099
  · exact B1474103
  · exact B1474107
  · exact B1474111
  · exact B1474115
  · exact B1474119
  · exact B1474123
  · exact B1474127
  · exact B1474131
  · exact B1474135
  · exact B1474139
  · exact B1474143
  · exact B1474147
  · exact B1474151
  · exact B1474155
  · exact B1474159
  · exact B1474163
  · exact B1474167
  · exact B1474171
  · exact B1474175
  · exact B1474179
  · exact B1474183
  · exact B1474187
  · exact B1474191
  · exact B1474195
  · exact B1474199
  · exact B1474203
  · exact B1474207
  · exact B1474211
  · exact B1474215
  · exact B1474219
  · exact B1474223
  · exact B1474227
  · exact B1474231
  · exact B1474235
  · exact B1474239
  · exact B1474243
  · exact B1474247
  · exact B1474251
  · exact B1474255
  · exact B1474259
  · exact B1474263
  · exact B1474267
  · exact B1474271
  · exact B1474275
  · exact B1474279
  · exact B1474283
  · exact B1474287
  · exact B1474291
  · exact B1474295
  · exact B1474299
  · exact B1474303
  · exact B1474307
  · exact B1474311
  · exact B1474315
  · exact B1474319
  · exact B1474323
  · exact B1474327
  · exact B1474331
  · exact B1474335
  · exact B1474339
  · exact B1474343
  · exact B1474347
  · exact B1474351
  · exact B1474355
  · exact B1474359
  · exact B1474363
  · exact B1474367
  · exact B1474371
  · exact B1474375
  · exact B1474379
  · exact B1474383
  · exact B1474387
  · exact B1474391
  · exact B1474395
  · exact B1474399
  · exact B1474403
  · exact B1474407
  · exact B1474411
  · exact B1474415
  · exact B1474419
  · exact B1474423
  · exact B1474427
  · exact B1474431
  · exact B1474435
  · exact B1474439
  · exact B1474443
  · exact B1474447
  · exact B1474451
  · exact B1474455
  · exact B1474459
  · exact B1474463
  · exact B1474467
  · exact B1474471
  · exact B1474475
  · exact B1474479
  · exact B1474483
  · exact B1474487
  · exact B1474491
  · exact B1474495
  · exact B1474499
  · exact B1474503
  · exact B1474507
  · exact B1474511
  · exact B1474515
  · exact B1474519
  · exact B1474523
  · exact B1474527
  · exact B1474531
  · exact B1474535
  · exact B1474539
  · exact B1474543
  · exact B1474547
  · exact B1474551
  · exact B1474555

theorem solution (m : ℕ) (hlo : 1472556 ≤ m) (hhi : m ≤ 1474556) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 368139 ≤ j := by omega
    have hj2 : j ≤ 368638 := by omega
    have hb : Blo 1472556 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
