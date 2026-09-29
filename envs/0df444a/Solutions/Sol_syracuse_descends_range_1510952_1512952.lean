-- Prove2me | solution 1 for syracuse_descends_range_1510952_1512952
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:11.019892+00:00
-- url     : https://prove2.me/submissions/9073050e-2880-4049-be83-1b0f55303090

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


theorem B3448853 : Blo 1510952 3448853 := bbase (se 6 (by rfl) ⟨80832, by rfl⟩ : syracuseStep 3448853 = 161665) (by norm_num)
theorem B2269205 : Blo 1510952 2269205 := bbase (se 6 (by rfl) ⟨53184, by rfl⟩ : syracuseStep 2269205 = 106369) (by norm_num)
theorem B3825701 : Blo 1510952 3825701 := bbase (se 4 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 3825701 = 717319) (by norm_num)
theorem B2269229 : Blo 1510952 2269229 := bbase (se 3 (by rfl) ⟨425480, by rfl⟩ : syracuseStep 2269229 = 850961) (by norm_num)
theorem B3399749 : Blo 1510952 3399749 := bbase (se 4 (by rfl) ⟨318726, by rfl⟩ : syracuseStep 3399749 = 637453) (by norm_num)
theorem B2269253 : Blo 1510952 2269253 := bbase (se 4 (by rfl) ⟨212742, by rfl⟩ : syracuseStep 2269253 = 425485) (by norm_num)
theorem B10485845 : Blo 1510952 10485845 := bbase (se 8 (by rfl) ⟨61440, by rfl⟩ : syracuseStep 10485845 = 122881) (by norm_num)
theorem B5103701 : Blo 1510952 5103701 := bbase (se 8 (by rfl) ⟨29904, by rfl⟩ : syracuseStep 5103701 = 59809) (by norm_num)
theorem B2269277 : Blo 1510952 2269277 := bbase (se 3 (by rfl) ⟨425489, by rfl⟩ : syracuseStep 2269277 = 850979) (by norm_num)
theorem B2269301 : Blo 1510952 2269301 := bbase (se 5 (by rfl) ⟨106373, by rfl⟩ : syracuseStep 2269301 = 212747) (by norm_num)
theorem B3399821 : Blo 1510952 3399821 := bbase (se 3 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 3399821 = 1274933) (by norm_num)
theorem B2269325 : Blo 1510952 2269325 := bbase (se 3 (by rfl) ⟨425498, by rfl⟩ : syracuseStep 2269325 = 850997) (by norm_num)
theorem B1613989 : Blo 1510952 1613989 := bbase (se 4 (by rfl) ⟨151311, by rfl⟩ : syracuseStep 1613989 = 302623) (by norm_num)
theorem B2269349 : Blo 1510952 2269349 := bbase (se 4 (by rfl) ⟨212751, by rfl⟩ : syracuseStep 2269349 = 425503) (by norm_num)
theorem B6455477 : Blo 1510952 6455477 := bbase (se 5 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 6455477 = 605201) (by norm_num)
theorem B2269373 : Blo 1510952 2269373 := bbase (se 3 (by rfl) ⟨425507, by rfl⟩ : syracuseStep 2269373 = 851015) (by norm_num)
theorem B3399893 : Blo 1510952 3399893 := bbase (se 7 (by rfl) ⟨39842, by rfl⟩ : syracuseStep 3399893 = 79685) (by norm_num)
theorem B14532821 : Blo 1510952 14532821 := bbase (se 7 (by rfl) ⟨170306, by rfl⟩ : syracuseStep 14532821 = 340613) (by norm_num)
theorem B2269397 : Blo 1510952 2269397 := bbase (se 7 (by rfl) ⟨26594, by rfl⟩ : syracuseStep 2269397 = 53189) (by norm_num)
theorem B3825893 : Blo 1510952 3825893 := bbase (se 4 (by rfl) ⟨358677, by rfl⟩ : syracuseStep 3825893 = 717355) (by norm_num)
theorem B2269421 : Blo 1510952 2269421 := bbase (se 3 (by rfl) ⟨425516, by rfl⟩ : syracuseStep 2269421 = 851033) (by norm_num)
theorem B3399965 : Blo 1510952 3399965 := bbase (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) (by norm_num)
theorem B4841813 : Blo 1510952 4841813 := bbase (se 10 (by rfl) ⟨7092, by rfl⟩ : syracuseStep 4841813 = 14185) (by norm_num)
theorem B1614173 : Blo 1510952 1614173 := bbase (se 3 (by rfl) ⟨302657, by rfl⟩ : syracuseStep 1614173 = 605315) (by norm_num)
theorem B3400037 : Blo 1510952 3400037 := bbase (se 4 (by rfl) ⟨318753, by rfl⟩ : syracuseStep 3400037 = 637507) (by norm_num)
theorem B3228005 : Blo 1510952 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B3064189 : Blo 1510952 3064189 := bbase (se 3 (by rfl) ⟨574535, by rfl⟩ : syracuseStep 3064189 = 1149071) (by norm_num)
theorem B1532305 : Blo 1510952 1532305 := bbase (se 2 (by rfl) ⟨574614, by rfl⟩ : syracuseStep 1532305 = 1149229) (by norm_num)
theorem B3400109 : Blo 1510952 3400109 := bbase (se 3 (by rfl) ⟨637520, by rfl⟩ : syracuseStep 3400109 = 1275041) (by norm_num)
theorem B3400181 : Blo 1510952 3400181 := bbase (se 5 (by rfl) ⟨159383, by rfl⟩ : syracuseStep 3400181 = 318767) (by norm_num)
theorem B3228149 : Blo 1510952 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B5104133 : Blo 1510952 5104133 := bbase (se 4 (by rfl) ⟨478512, by rfl⟩ : syracuseStep 5104133 = 957025) (by norm_num)
theorem B3400253 : Blo 1510952 3400253 := bbase (se 3 (by rfl) ⟨637547, by rfl⟩ : syracuseStep 3400253 = 1275095) (by norm_num)
theorem B3826237 : Blo 1510952 3826237 := bbase (se 3 (by rfl) ⟨717419, by rfl⟩ : syracuseStep 3826237 = 1434839) (by norm_num)
theorem B3400325 : Blo 1510952 3400325 := bbase (se 4 (by rfl) ⟨318780, by rfl⟩ : syracuseStep 3400325 = 637561) (by norm_num)
theorem B3826349 : Blo 1510952 3826349 := bbase (se 3 (by rfl) ⟨717440, by rfl⟩ : syracuseStep 3826349 = 1434881) (by norm_num)
theorem B3400397 : Blo 1510952 3400397 := bbase (se 3 (by rfl) ⟨637574, by rfl⟩ : syracuseStep 3400397 = 1275149) (by norm_num)
theorem B3449549 : Blo 1510952 3449549 := bbase (se 3 (by rfl) ⟨646790, by rfl⟩ : syracuseStep 3449549 = 1293581) (by norm_num)
theorem B7652069 : Blo 1510952 7652069 := bbase (se 4 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 7652069 = 1434763) (by norm_num)
theorem B3400469 : Blo 1510952 3400469 := bbase (se 6 (by rfl) ⟨79698, by rfl⟩ : syracuseStep 3400469 = 159397) (by norm_num)
theorem B5817109 : Blo 1510952 5817109 := bbase (se 6 (by rfl) ⟨136338, by rfl⟩ : syracuseStep 5817109 = 272677) (by norm_num)
theorem B17220437 : Blo 1510952 17220437 := bbase (se 9 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 17220437 = 100901) (by norm_num)
theorem B3400541 : Blo 1510952 3400541 := bbase (se 3 (by rfl) ⟨637601, by rfl⟩ : syracuseStep 3400541 = 1275203) (by norm_num)
theorem B4088677 : Blo 1510952 4088677 := bbase (se 4 (by rfl) ⟨383313, by rfl⟩ : syracuseStep 4088677 = 766627) (by norm_num)
theorem B3826541 : Blo 1510952 3826541 := bbase (se 3 (by rfl) ⟨717476, by rfl⟩ : syracuseStep 3826541 = 1434953) (by norm_num)
theorem B14926709 : Blo 1510952 14926709 := bbase (se 5 (by rfl) ⟨699689, by rfl⟩ : syracuseStep 14926709 = 1399379) (by norm_num)
theorem B3064709 : Blo 1510952 3064709 := bbase (se 4 (by rfl) ⟨287316, by rfl⟩ : syracuseStep 3064709 = 574633) (by norm_num)
theorem B3400613 : Blo 1510952 3400613 := bbase (se 4 (by rfl) ⟨318807, by rfl⟩ : syracuseStep 3400613 = 637615) (by norm_num)
theorem B5104565 : Blo 1510952 5104565 := bbase (se 5 (by rfl) ⟨239276, by rfl⟩ : syracuseStep 5104565 = 478553) (by norm_num)
theorem B2909125 : Blo 1510952 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B3400685 : Blo 1510952 3400685 := bbase (se 3 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 3400685 = 1275257) (by norm_num)
theorem B7267333 : Blo 1510952 7267333 := bbase (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) (by norm_num)
theorem B3400757 : Blo 1510952 3400757 := bbase (se 5 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 3400757 = 318821) (by norm_num)
theorem B5743669 : Blo 1510952 5743669 := bbase (se 5 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 5743669 = 538469) (by norm_num)
theorem B1614925 : Blo 1510952 1614925 := bbase (se 3 (by rfl) ⟨302798, by rfl⟩ : syracuseStep 1614925 = 605597) (by norm_num)
theorem B3400829 : Blo 1510952 3400829 := bbase (se 3 (by rfl) ⟨637655, by rfl⟩ : syracuseStep 3400829 = 1275311) (by norm_num)
theorem B6456469 : Blo 1510952 6456469 := bbase (se 6 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 6456469 = 302647) (by norm_num)
theorem B1614997 : Blo 1510952 1614997 := bbase (se 6 (by rfl) ⟨37851, by rfl⟩ : syracuseStep 1614997 = 75703) (by norm_num)
theorem B3400901 : Blo 1510952 3400901 := bbase (se 4 (by rfl) ⟨318834, by rfl⟩ : syracuseStep 3400901 = 637669) (by norm_num)
theorem B3826885 : Blo 1510952 3826885 := bbase (se 4 (by rfl) ⟨358770, by rfl⟩ : syracuseStep 3826885 = 717541) (by norm_num)
theorem B3228893 : Blo 1510952 3228893 := bbase (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) (by norm_num)
theorem B3400973 : Blo 1510952 3400973 := bbase (se 3 (by rfl) ⟨637682, by rfl⟩ : syracuseStep 3400973 = 1275365) (by norm_num)
theorem B8733973 : Blo 1510952 8733973 := bbase (se 6 (by rfl) ⟨204702, by rfl⟩ : syracuseStep 8733973 = 409405) (by norm_num)
theorem B2868509 : Blo 1510952 2868509 := bbase (se 3 (by rfl) ⟨537845, by rfl⟩ : syracuseStep 2868509 = 1075691) (by norm_num)
theorem B2909477 : Blo 1510952 2909477 := bbase (se 4 (by rfl) ⟨272763, by rfl⟩ : syracuseStep 2909477 = 545527) (by norm_num)
theorem B3826997 : Blo 1510952 3826997 := bbase (se 5 (by rfl) ⟨179390, by rfl⟩ : syracuseStep 3826997 = 358781) (by norm_num)
theorem B1615177 : Blo 1510952 1615177 := bbase (se 2 (by rfl) ⟨605691, by rfl⟩ : syracuseStep 1615177 = 1211383) (by norm_num)
theorem B3401045 : Blo 1510952 3401045 := bbase (se 12 (by rfl) ⟨1245, by rfl⟩ : syracuseStep 3401045 = 2491) (by norm_num)
theorem B36799829 : Blo 1510952 36799829 := bbase (se 12 (by rfl) ⟨13476, by rfl⟩ : syracuseStep 36799829 = 26953) (by norm_num)
theorem B5104997 : Blo 1510952 5104997 := bbase (se 4 (by rfl) ⟨478593, by rfl⟩ : syracuseStep 5104997 = 957187) (by norm_num)
theorem B5743973 : Blo 1510952 5743973 := bbase (se 4 (by rfl) ⟨538497, by rfl⟩ : syracuseStep 5743973 = 1076995) (by norm_num)
theorem B3401117 : Blo 1510952 3401117 := bbase (se 3 (by rfl) ⟨637709, by rfl⟩ : syracuseStep 3401117 = 1275419) (by norm_num)
theorem B3401189 : Blo 1510952 3401189 := bbase (se 4 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 3401189 = 637723) (by norm_num)
theorem B3827189 : Blo 1510952 3827189 := bbase (se 5 (by rfl) ⟨179399, by rfl⟩ : syracuseStep 3827189 = 358799) (by norm_num)
theorem B3065357 : Blo 1510952 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B3401261 : Blo 1510952 3401261 := bbase (se 3 (by rfl) ⟨637736, by rfl⟩ : syracuseStep 3401261 = 1275473) (by norm_num)
theorem B2868797 : Blo 1510952 2868797 := bbase (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) (by norm_num)
theorem B3065453 : Blo 1510952 3065453 := bbase (se 3 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 3065453 = 1149545) (by norm_num)
theorem B3401333 : Blo 1510952 3401333 := bbase (se 5 (by rfl) ⟨159437, by rfl⟩ : syracuseStep 3401333 = 318875) (by norm_num)
theorem B9684629 : Blo 1510952 9684629 := bbase (se 6 (by rfl) ⟨226983, by rfl⟩ : syracuseStep 9684629 = 453967) (by norm_num)
theorem B3401405 : Blo 1510952 3401405 := bbase (se 3 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 3401405 = 1275527) (by norm_num)
theorem B2868949 : Blo 1510952 2868949 := bbase (se 7 (by rfl) ⟨33620, by rfl⟩ : syracuseStep 2868949 = 67241) (by norm_num)
theorem B8611541 : Blo 1510952 8611541 := bbase (se 7 (by rfl) ⟨100916, by rfl⟩ : syracuseStep 8611541 = 201833) (by norm_num)
theorem B3401477 : Blo 1510952 3401477 := bbase (se 4 (by rfl) ⟨318888, by rfl⟩ : syracuseStep 3401477 = 637777) (by norm_num)
theorem B1615621 : Blo 1510952 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B5105429 : Blo 1510952 5105429 := bbase (se 6 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 5105429 = 239317) (by norm_num)
theorem B6211397 : Blo 1510952 6211397 := bbase (se 4 (by rfl) ⟨582318, by rfl⟩ : syracuseStep 6211397 = 1164637) (by norm_num)
theorem B3401549 : Blo 1510952 3401549 := bbase (se 3 (by rfl) ⟨637790, by rfl⟩ : syracuseStep 3401549 = 1275581) (by norm_num)
theorem B3827533 : Blo 1510952 3827533 := bbase (se 3 (by rfl) ⟨717662, by rfl⟩ : syracuseStep 3827533 = 1435325) (by norm_num)
theorem B3401621 : Blo 1510952 3401621 := bbase (se 6 (by rfl) ⟨79725, by rfl⟩ : syracuseStep 3401621 = 159451) (by norm_num)
theorem B3827645 : Blo 1510952 3827645 := bbase (se 3 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 3827645 = 1435367) (by norm_num)
theorem B3229645 : Blo 1510952 3229645 := bbase (se 3 (by rfl) ⟨605558, by rfl⟩ : syracuseStep 3229645 = 1211117) (by norm_num)
theorem B21792725 : Blo 1510952 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B3401693 : Blo 1510952 3401693 := bbase (se 3 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 3401693 = 1275635) (by norm_num)
theorem B4302821 : Blo 1510952 4302821 := bbase (se 4 (by rfl) ⟨403389, by rfl⟩ : syracuseStep 4302821 = 806779) (by norm_num)
theorem B7653365 : Blo 1510952 7653365 := bbase (se 5 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 7653365 = 717503) (by norm_num)
theorem B2549765 : Blo 1510952 2549765 := bbase (se 4 (by rfl) ⟨239040, by rfl⟩ : syracuseStep 2549765 = 478081) (by norm_num)
theorem B2869253 : Blo 1510952 2869253 := bbase (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) (by norm_num)
theorem B3401765 : Blo 1510952 3401765 := bbase (se 4 (by rfl) ⟨318915, by rfl⟩ : syracuseStep 3401765 = 637831) (by norm_num)
theorem B3229789 : Blo 1510952 3229789 := bbase (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) (by norm_num)
theorem B3401837 : Blo 1510952 3401837 := bbase (se 3 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 3401837 = 1275689) (by norm_num)
theorem B3827837 : Blo 1510952 3827837 := bbase (se 3 (by rfl) ⟨717719, by rfl⟩ : syracuseStep 3827837 = 1435439) (by norm_num)
theorem B2549893 : Blo 1510952 2549893 := bbase (se 4 (by rfl) ⟨239052, by rfl⟩ : syracuseStep 2549893 = 478105) (by norm_num)
theorem B3401909 : Blo 1510952 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B7760069 : Blo 1510952 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B5105861 : Blo 1510952 5105861 := bbase (se 4 (by rfl) ⟨478674, by rfl⟩ : syracuseStep 5105861 = 957349) (by norm_num)
theorem B2549981 : Blo 1510952 2549981 := bbase (se 3 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 2549981 = 956243) (by norm_num)
theorem B3401981 : Blo 1510952 3401981 := bbase (se 3 (by rfl) ⟨637871, by rfl⟩ : syracuseStep 3401981 = 1275743) (by norm_num)
theorem B4843813 : Blo 1510952 4843813 := bbase (se 4 (by rfl) ⟨454107, by rfl⟩ : syracuseStep 4843813 = 908215) (by norm_num)
theorem B3402053 : Blo 1510952 3402053 := bbase (se 4 (by rfl) ⟨318942, by rfl⟩ : syracuseStep 3402053 = 637885) (by norm_num)
theorem B2550109 : Blo 1510952 2550109 := bbase (se 3 (by rfl) ⟨478145, by rfl⟩ : syracuseStep 2550109 = 956291) (by norm_num)
theorem B3402125 : Blo 1510952 3402125 := bbase (se 3 (by rfl) ⟨637898, by rfl⟩ : syracuseStep 3402125 = 1275797) (by norm_num)
theorem B2550197 : Blo 1510952 2550197 := bbase (se 5 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 2550197 = 239081) (by norm_num)
theorem B3402197 : Blo 1510952 3402197 := bbase (se 7 (by rfl) ⟨39869, by rfl⟩ : syracuseStep 3402197 = 79739) (by norm_num)
theorem B3828181 : Blo 1510952 3828181 := bbase (se 7 (by rfl) ⟨44861, by rfl⟩ : syracuseStep 3828181 = 89723) (by norm_num)
theorem B3230165 : Blo 1510952 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B12913141 : Blo 1510952 12913141 := bbase (se 5 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 12913141 = 1210607) (by norm_num)
theorem B3402269 : Blo 1510952 3402269 := bbase (se 3 (by rfl) ⟨637925, by rfl⟩ : syracuseStep 3402269 = 1275851) (by norm_num)
theorem B4975141 : Blo 1510952 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B2550325 : Blo 1510952 2550325 := bbase (se 5 (by rfl) ⟨119546, by rfl⟩ : syracuseStep 2550325 = 239093) (by norm_num)
theorem B3828293 : Blo 1510952 3828293 := bbase (se 4 (by rfl) ⟨358902, by rfl⟩ : syracuseStep 3828293 = 717805) (by norm_num)
theorem B3402341 : Blo 1510952 3402341 := bbase (se 4 (by rfl) ⟨318969, by rfl⟩ : syracuseStep 3402341 = 637939) (by norm_num)
theorem B4303493 : Blo 1510952 4303493 := bbase (se 4 (by rfl) ⟨403452, by rfl⟩ : syracuseStep 4303493 = 806905) (by norm_num)
theorem B2550413 : Blo 1510952 2550413 := bbase (se 3 (by rfl) ⟨478202, by rfl⟩ : syracuseStep 2550413 = 956405) (by norm_num)
theorem B2042533 : Blo 1510952 2042533 := bbase (se 4 (by rfl) ⟨191487, by rfl⟩ : syracuseStep 2042533 = 382975) (by norm_num)
theorem B3402413 : Blo 1510952 3402413 := bbase (se 3 (by rfl) ⟨637952, by rfl⟩ : syracuseStep 3402413 = 1275905) (by norm_num)
theorem B2870005 : Blo 1510952 2870005 := bbase (se 5 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 2870005 = 269063) (by norm_num)
theorem B3402485 : Blo 1510952 3402485 := bbase (se 5 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 3402485 = 318983) (by norm_num)
theorem B3828485 : Blo 1510952 3828485 := bbase (se 4 (by rfl) ⟨358920, by rfl⟩ : syracuseStep 3828485 = 717841) (by norm_num)
theorem B2550541 : Blo 1510952 2550541 := bbase (se 3 (by rfl) ⟨478226, by rfl⟩ : syracuseStep 2550541 = 956453) (by norm_num)
theorem B3402557 : Blo 1510952 3402557 := bbase (se 3 (by rfl) ⟨637979, by rfl⟩ : syracuseStep 3402557 = 1275959) (by norm_num)
theorem B3230533 : Blo 1510952 3230533 := bbase (se 4 (by rfl) ⟨302862, by rfl⟩ : syracuseStep 3230533 = 605725) (by norm_num)
theorem B2550629 : Blo 1510952 2550629 := bbase (se 4 (by rfl) ⟨239121, by rfl⟩ : syracuseStep 2550629 = 478243) (by norm_num)
theorem B1723241 : Blo 1510952 1723241 := bbase (se 2 (by rfl) ⟨646215, by rfl⟩ : syracuseStep 1723241 = 1292431) (by norm_num)
theorem B2870149 : Blo 1510952 2870149 := bbase (se 4 (by rfl) ⟨269076, by rfl⟩ : syracuseStep 2870149 = 538153) (by norm_num)
theorem B3402629 : Blo 1510952 3402629 := bbase (se 4 (by rfl) ⟨318996, by rfl⟩ : syracuseStep 3402629 = 637993) (by norm_num)
theorem B1723297 : Blo 1510952 1723297 := bbase (se 2 (by rfl) ⟨646236, by rfl⟩ : syracuseStep 1723297 = 1292473) (by norm_num)
theorem B3632053 : Blo 1510952 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B3402701 : Blo 1510952 3402701 := bbase (se 3 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 3402701 = 1276013) (by norm_num)
theorem B2550757 : Blo 1510952 2550757 := bbase (se 4 (by rfl) ⟨239133, by rfl⟩ : syracuseStep 2550757 = 478267) (by norm_num)
theorem B3402773 : Blo 1510952 3402773 := bbase (se 6 (by rfl) ⟨79752, by rfl⟩ : syracuseStep 3402773 = 159505) (by norm_num)
theorem B2870309 : Blo 1510952 2870309 := bbase (se 4 (by rfl) ⟨269091, by rfl⟩ : syracuseStep 2870309 = 538183) (by norm_num)
theorem B4303925 : Blo 1510952 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B12266549 : Blo 1510952 12266549 := bbase (se 5 (by rfl) ⟨574994, by rfl⟩ : syracuseStep 12266549 = 1149989) (by norm_num)
theorem B2550845 : Blo 1510952 2550845 := bbase (se 3 (by rfl) ⟨478283, by rfl⟩ : syracuseStep 2550845 = 956567) (by norm_num)
theorem B3632197 : Blo 1510952 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B3402845 : Blo 1510952 3402845 := bbase (se 3 (by rfl) ⟨638033, by rfl⟩ : syracuseStep 3402845 = 1276067) (by norm_num)
theorem B3828829 : Blo 1510952 3828829 := bbase (se 3 (by rfl) ⟨717905, by rfl⟩ : syracuseStep 3828829 = 1435811) (by norm_num)
theorem B3402917 : Blo 1510952 3402917 := bbase (se 4 (by rfl) ⟨319023, by rfl⟩ : syracuseStep 3402917 = 638047) (by norm_num)
theorem B2870453 : Blo 1510952 2870453 := bbase (se 5 (by rfl) ⟨134552, by rfl⟩ : syracuseStep 2870453 = 269105) (by norm_num)
theorem B2550973 : Blo 1510952 2550973 := bbase (se 3 (by rfl) ⟨478307, by rfl⟩ : syracuseStep 2550973 = 956615) (by norm_num)
theorem B3828941 : Blo 1510952 3828941 := bbase (se 3 (by rfl) ⟨717926, by rfl⟩ : syracuseStep 3828941 = 1435853) (by norm_num)
theorem B3402989 : Blo 1510952 3402989 := bbase (se 3 (by rfl) ⟨638060, by rfl⟩ : syracuseStep 3402989 = 1276121) (by norm_num)
theorem B7654661 : Blo 1510952 7654661 := bbase (se 4 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 7654661 = 1435249) (by norm_num)
theorem B2551061 : Blo 1510952 2551061 := bbase (se 6 (by rfl) ⟨59790, by rfl⟩ : syracuseStep 2551061 = 119581) (by norm_num)
theorem B3403061 : Blo 1510952 3403061 := bbase (se 5 (by rfl) ⟨159518, by rfl⟩ : syracuseStep 3403061 = 319037) (by norm_num)
theorem B5451077 : Blo 1510952 5451077 := bbase (se 4 (by rfl) ⟨511038, by rfl⟩ : syracuseStep 5451077 = 1022077) (by norm_num)
theorem B3403133 : Blo 1510952 3403133 := bbase (se 3 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 3403133 = 1276175) (by norm_num)
theorem B1723789 : Blo 1510952 1723789 := bbase (se 3 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 1723789 = 646421) (by norm_num)
theorem B3829133 : Blo 1510952 3829133 := bbase (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) (by norm_num)
theorem B2551189 : Blo 1510952 2551189 := bbase (se 6 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 2551189 = 119587) (by norm_num)
theorem B3403205 : Blo 1510952 3403205 := bbase (se 4 (by rfl) ⟨319050, by rfl⟩ : syracuseStep 3403205 = 638101) (by norm_num)
theorem B2870741 : Blo 1510952 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B2551277 : Blo 1510952 2551277 := bbase (se 3 (by rfl) ⟨478364, by rfl⟩ : syracuseStep 2551277 = 956729) (by norm_num)
theorem B3403277 : Blo 1510952 3403277 := bbase (se 3 (by rfl) ⟨638114, by rfl⟩ : syracuseStep 3403277 = 1276229) (by norm_num)
theorem B1912349 : Blo 1510952 1912349 := bbase (se 3 (by rfl) ⟨358565, by rfl⟩ : syracuseStep 1912349 = 717131) (by norm_num)
theorem B1912405 : Blo 1510952 1912405 := bbase (se 8 (by rfl) ⟨11205, by rfl⟩ : syracuseStep 1912405 = 22411) (by norm_num)
theorem B3403349 : Blo 1510952 3403349 := bbase (se 8 (by rfl) ⟨19941, by rfl⟩ : syracuseStep 3403349 = 39883) (by norm_num)
theorem B2551405 : Blo 1510952 2551405 := bbase (se 3 (by rfl) ⟨478388, by rfl⟩ : syracuseStep 2551405 = 956777) (by norm_num)
theorem B2870893 : Blo 1510952 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B3403421 : Blo 1510952 3403421 := bbase (se 3 (by rfl) ⟨638141, by rfl⟩ : syracuseStep 3403421 = 1276283) (by norm_num)
theorem B3632813 : Blo 1510952 3632813 := bbase (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) (by norm_num)
theorem B1912501 : Blo 1510952 1912501 := bbase (se 5 (by rfl) ⟨89648, by rfl⟩ : syracuseStep 1912501 = 179297) (by norm_num)
theorem B2551493 : Blo 1510952 2551493 := bbase (se 4 (by rfl) ⟨239202, by rfl⟩ : syracuseStep 2551493 = 478405) (by norm_num)
theorem B3403493 : Blo 1510952 3403493 := bbase (se 4 (by rfl) ⟨319077, by rfl⟩ : syracuseStep 3403493 = 638155) (by norm_num)
theorem B3829477 : Blo 1510952 3829477 := bbase (se 4 (by rfl) ⟨359013, by rfl⟩ : syracuseStep 3829477 = 718027) (by norm_num)
theorem B4304677 : Blo 1510952 4304677 := bbase (se 4 (by rfl) ⟨403563, by rfl⟩ : syracuseStep 4304677 = 807127) (by norm_num)
theorem B7270181 : Blo 1510952 7270181 := bbase (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) (by norm_num)
theorem B3403565 : Blo 1510952 3403565 := bbase (se 3 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 3403565 = 1276337) (by norm_num)
theorem B5738309 : Blo 1510952 5738309 := bbase (se 4 (by rfl) ⟨537966, by rfl⟩ : syracuseStep 5738309 = 1075933) (by norm_num)
theorem B2551621 : Blo 1510952 2551621 := bbase (se 4 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 2551621 = 478429) (by norm_num)
theorem B2043733 : Blo 1510952 2043733 := bbase (se 9 (by rfl) ⟨5987, by rfl⟩ : syracuseStep 2043733 = 11975) (by norm_num)
theorem B3829589 : Blo 1510952 3829589 := bbase (se 9 (by rfl) ⟨11219, by rfl⟩ : syracuseStep 3829589 = 22439) (by norm_num)
theorem B1912673 : Blo 1510952 1912673 := bbase (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) (by norm_num)
theorem B3403637 : Blo 1510952 3403637 := bbase (se 5 (by rfl) ⟨159545, by rfl⟩ : syracuseStep 3403637 = 319091) (by norm_num)
theorem B1912729 : Blo 1510952 1912729 := bbase (se 2 (by rfl) ⟨717273, by rfl⟩ : syracuseStep 1912729 = 1434547) (by norm_num)
theorem B2551709 : Blo 1510952 2551709 := bbase (se 3 (by rfl) ⟨478445, by rfl⟩ : syracuseStep 2551709 = 956891) (by norm_num)
theorem B2871197 : Blo 1510952 2871197 := bbase (se 3 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 2871197 = 1076699) (by norm_num)
theorem B3403709 : Blo 1510952 3403709 := bbase (se 3 (by rfl) ⟨638195, by rfl⟩ : syracuseStep 3403709 = 1276391) (by norm_num)
theorem B1699825 : Blo 1510952 1699825 := bbase (se 2 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 1699825 = 1274869) (by norm_num)
theorem B1912825 : Blo 1510952 1912825 := bbase (se 2 (by rfl) ⟨717309, by rfl⟩ : syracuseStep 1912825 = 1434619) (by norm_num)
theorem B3633149 : Blo 1510952 3633149 := bbase (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) (by norm_num)
theorem B6131717 : Blo 1510952 6131717 := bbase (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) (by norm_num)
theorem B3403781 : Blo 1510952 3403781 := bbase (se 4 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 3403781 = 638209) (by norm_num)
theorem B1699861 : Blo 1510952 1699861 := bbase (se 6 (by rfl) ⟨39840, by rfl⟩ : syracuseStep 1699861 = 79681) (by norm_num)
theorem B2551837 : Blo 1510952 2551837 := bbase (se 3 (by rfl) ⟨478469, by rfl⟩ : syracuseStep 2551837 = 956939) (by norm_num)
theorem B1699897 : Blo 1510952 1699897 := bbase (se 2 (by rfl) ⟨637461, by rfl⟩ : syracuseStep 1699897 = 1274923) (by norm_num)
theorem B3403853 : Blo 1510952 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B1699933 : Blo 1510952 1699933 := bbase (se 3 (by rfl) ⟨318737, by rfl⟩ : syracuseStep 1699933 = 637475) (by norm_num)
theorem B3633245 : Blo 1510952 3633245 := bbase (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) (by norm_num)
theorem B5738597 : Blo 1510952 5738597 := bbase (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) (by norm_num)
theorem B2551925 : Blo 1510952 2551925 := bbase (se 5 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 2551925 = 239243) (by norm_num)
theorem B1699969 : Blo 1510952 1699969 := bbase (se 2 (by rfl) ⟨637488, by rfl⟩ : syracuseStep 1699969 = 1274977) (by norm_num)
theorem B2420869 : Blo 1510952 2420869 := bbase (se 4 (by rfl) ⟨226956, by rfl⟩ : syracuseStep 2420869 = 453913) (by norm_num)
theorem B3403925 : Blo 1510952 3403925 := bbase (se 6 (by rfl) ⟨79779, by rfl⟩ : syracuseStep 3403925 = 159559) (by norm_num)
theorem B1700005 : Blo 1510952 1700005 := bbase (se 4 (by rfl) ⟨159375, by rfl⟩ : syracuseStep 1700005 = 318751) (by norm_num)
theorem B1912997 : Blo 1510952 1912997 := bbase (se 4 (by rfl) ⟨179343, by rfl⟩ : syracuseStep 1912997 = 358687) (by norm_num)
theorem B1700041 : Blo 1510952 1700041 := bbase (se 2 (by rfl) ⟨637515, by rfl⟩ : syracuseStep 1700041 = 1275031) (by norm_num)
theorem B1913053 : Blo 1510952 1913053 := bbase (se 3 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 1913053 = 717395) (by norm_num)
theorem B3403997 : Blo 1510952 3403997 := bbase (se 3 (by rfl) ⟨638249, by rfl⟩ : syracuseStep 3403997 = 1276499) (by norm_num)
theorem B1700077 : Blo 1510952 1700077 := bbase (se 3 (by rfl) ⟨318764, by rfl⟩ : syracuseStep 1700077 = 637529) (by norm_num)
theorem B2552053 : Blo 1510952 2552053 := bbase (se 5 (by rfl) ⟨119627, by rfl⟩ : syracuseStep 2552053 = 239255) (by norm_num)
theorem B1700113 : Blo 1510952 1700113 := bbase (se 2 (by rfl) ⟨637542, by rfl⟩ : syracuseStep 1700113 = 1275085) (by norm_num)
theorem B3633437 : Blo 1510952 3633437 := bbase (se 3 (by rfl) ⟨681269, by rfl⟩ : syracuseStep 3633437 = 1362539) (by norm_num)
theorem B5099813 : Blo 1510952 5099813 := bbase (se 4 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 5099813 = 956215) (by norm_num)
theorem B3404069 : Blo 1510952 3404069 := bbase (se 4 (by rfl) ⟨319131, by rfl⟩ : syracuseStep 3404069 = 638263) (by norm_num)
theorem B1700149 : Blo 1510952 1700149 := bbase (se 5 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 1700149 = 159389) (by norm_num)
theorem B1913149 : Blo 1510952 1913149 := bbase (se 3 (by rfl) ⟨358715, by rfl⟩ : syracuseStep 1913149 = 717431) (by norm_num)
theorem B2552141 : Blo 1510952 2552141 := bbase (se 3 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 2552141 = 957053) (by norm_num)
theorem B1700185 : Blo 1510952 1700185 := bbase (se 2 (by rfl) ⟨637569, by rfl⟩ : syracuseStep 1700185 = 1275139) (by norm_num)
theorem B3404141 : Blo 1510952 3404141 := bbase (se 3 (by rfl) ⟨638276, by rfl⟩ : syracuseStep 3404141 = 1276553) (by norm_num)
theorem B1700221 : Blo 1510952 1700221 := bbase (se 3 (by rfl) ⟨318791, by rfl⟩ : syracuseStep 1700221 = 637583) (by norm_num)
theorem B1700257 : Blo 1510952 1700257 := bbase (se 2 (by rfl) ⟨637596, by rfl⟩ : syracuseStep 1700257 = 1275193) (by norm_num)
theorem B12915125 : Blo 1510952 12915125 := bbase (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) (by norm_num)
theorem B1700293 : Blo 1510952 1700293 := bbase (se 4 (by rfl) ⟨159402, by rfl⟩ : syracuseStep 1700293 = 318805) (by norm_num)
theorem B2552269 : Blo 1510952 2552269 := bbase (se 3 (by rfl) ⟨478550, by rfl⟩ : syracuseStep 2552269 = 957101) (by norm_num)
theorem B3879389 : Blo 1510952 3879389 := bbase (se 3 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 3879389 = 1454771) (by norm_num)
theorem B1700329 : Blo 1510952 1700329 := bbase (se 2 (by rfl) ⟨637623, by rfl⟩ : syracuseStep 1700329 = 1275247) (by norm_num)
theorem B1913321 : Blo 1510952 1913321 := bbase (se 2 (by rfl) ⟨717495, by rfl⟩ : syracuseStep 1913321 = 1434991) (by norm_num)
theorem B1700365 : Blo 1510952 1700365 := bbase (se 3 (by rfl) ⟨318818, by rfl⟩ : syracuseStep 1700365 = 637637) (by norm_num)
theorem B7655957 : Blo 1510952 7655957 := bbase (se 6 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 7655957 = 358873) (by norm_num)
theorem B1913377 : Blo 1510952 1913377 := bbase (se 2 (by rfl) ⟨717516, by rfl⟩ : syracuseStep 1913377 = 1435033) (by norm_num)
theorem B2552357 : Blo 1510952 2552357 := bbase (se 4 (by rfl) ⟨239283, by rfl⟩ : syracuseStep 2552357 = 478567) (by norm_num)
theorem B1700401 : Blo 1510952 1700401 := bbase (se 2 (by rfl) ⟨637650, by rfl⟩ : syracuseStep 1700401 = 1275301) (by norm_num)
theorem B2421317 : Blo 1510952 2421317 := bbase (se 4 (by rfl) ⟨226998, by rfl⟩ : syracuseStep 2421317 = 453997) (by norm_num)
theorem B1700437 : Blo 1510952 1700437 := bbase (se 8 (by rfl) ⟨9963, by rfl⟩ : syracuseStep 1700437 = 19927) (by norm_num)
theorem B1700473 : Blo 1510952 1700473 := bbase (se 2 (by rfl) ⟨637677, by rfl⟩ : syracuseStep 1700473 = 1275355) (by norm_num)
theorem B1913473 : Blo 1510952 1913473 := bbase (se 2 (by rfl) ⟨717552, by rfl⟩ : syracuseStep 1913473 = 1435105) (by norm_num)
theorem B2871949 : Blo 1510952 2871949 := bbase (se 3 (by rfl) ⟨538490, by rfl⟩ : syracuseStep 2871949 = 1076981) (by norm_num)
theorem B11481749 : Blo 1510952 11481749 := bbase (se 6 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 11481749 = 538207) (by norm_num)
theorem B1700509 : Blo 1510952 1700509 := bbase (se 3 (by rfl) ⟨318845, by rfl⟩ : syracuseStep 1700509 = 637691) (by norm_num)
theorem B2552485 : Blo 1510952 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B1700545 : Blo 1510952 1700545 := bbase (se 2 (by rfl) ⟨637704, by rfl⟩ : syracuseStep 1700545 = 1275409) (by norm_num)
theorem B5100245 : Blo 1510952 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B1700581 : Blo 1510952 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B1815277 : Blo 1510952 1815277 := bbase (se 3 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 1815277 = 680729) (by norm_num)
theorem B2552573 : Blo 1510952 2552573 := bbase (se 3 (by rfl) ⟨478607, by rfl⟩ : syracuseStep 2552573 = 957215) (by norm_num)
theorem B1700617 : Blo 1510952 1700617 := bbase (se 2 (by rfl) ⟨637731, by rfl⟩ : syracuseStep 1700617 = 1275463) (by norm_num)
theorem B1725193 : Blo 1510952 1725193 := bbase (se 2 (by rfl) ⟨646947, by rfl⟩ : syracuseStep 1725193 = 1293895) (by norm_num)
theorem B2872093 : Blo 1510952 2872093 := bbase (se 3 (by rfl) ⟨538517, by rfl⟩ : syracuseStep 2872093 = 1077035) (by norm_num)
theorem B1700653 : Blo 1510952 1700653 := bbase (se 3 (by rfl) ⟨318872, by rfl⟩ : syracuseStep 1700653 = 637745) (by norm_num)
theorem B1913645 : Blo 1510952 1913645 := bbase (se 3 (by rfl) ⟨358808, by rfl⟩ : syracuseStep 1913645 = 717617) (by norm_num)
theorem B2298701 : Blo 1510952 2298701 := bbase (se 3 (by rfl) ⟨431006, by rfl⟩ : syracuseStep 2298701 = 862013) (by norm_num)
theorem B1700689 : Blo 1510952 1700689 := bbase (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) (by norm_num)
theorem B7361381 : Blo 1510952 7361381 := bbase (se 4 (by rfl) ⟨690129, by rfl⟩ : syracuseStep 7361381 = 1380259) (by norm_num)
theorem B1913701 : Blo 1510952 1913701 := bbase (se 4 (by rfl) ⟨179409, by rfl⟩ : syracuseStep 1913701 = 358819) (by norm_num)
theorem B1700725 : Blo 1510952 1700725 := bbase (se 5 (by rfl) ⟨79721, by rfl⟩ : syracuseStep 1700725 = 159443) (by norm_num)
theorem B2724725 : Blo 1510952 2724725 := bbase (se 5 (by rfl) ⟨127721, by rfl⟩ : syracuseStep 2724725 = 255443) (by norm_num)
theorem B1815421 : Blo 1510952 1815421 := bbase (se 3 (by rfl) ⟨340391, by rfl⟩ : syracuseStep 1815421 = 680783) (by norm_num)
theorem B2552701 : Blo 1510952 2552701 := bbase (se 3 (by rfl) ⟨478631, by rfl⟩ : syracuseStep 2552701 = 957263) (by norm_num)
theorem B1700761 : Blo 1510952 1700761 := bbase (se 2 (by rfl) ⟨637785, by rfl⟩ : syracuseStep 1700761 = 1275571) (by norm_num)
theorem B1700797 : Blo 1510952 1700797 := bbase (se 3 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 1700797 = 637799) (by norm_num)
theorem B1913797 : Blo 1510952 1913797 := bbase (se 4 (by rfl) ⟨179418, by rfl⟩ : syracuseStep 1913797 = 358837) (by norm_num)
theorem B2552789 : Blo 1510952 2552789 := bbase (se 7 (by rfl) ⟨29915, by rfl⟩ : syracuseStep 2552789 = 59831) (by norm_num)
theorem B1700833 : Blo 1510952 1700833 := bbase (se 2 (by rfl) ⟨637812, by rfl⟩ : syracuseStep 1700833 = 1275625) (by norm_num)
theorem B1700869 : Blo 1510952 1700869 := bbase (se 4 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 1700869 = 318913) (by norm_num)
theorem B1700905 : Blo 1510952 1700905 := bbase (se 2 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 1700905 = 1275679) (by norm_num)
theorem B11473973 : Blo 1510952 11473973 := bbase (se 5 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 11473973 = 1075685) (by norm_num)
theorem B1700941 : Blo 1510952 1700941 := bbase (se 3 (by rfl) ⟨318926, by rfl⟩ : syracuseStep 1700941 = 637853) (by norm_num)
theorem B16356437 : Blo 1510952 16356437 := bbase (se 8 (by rfl) ⟨95838, by rfl⟩ : syracuseStep 16356437 = 191677) (by norm_num)
theorem B2552917 : Blo 1510952 2552917 := bbase (se 8 (by rfl) ⟨14958, by rfl⟩ : syracuseStep 2552917 = 29917) (by norm_num)
theorem B1700977 : Blo 1510952 1700977 := bbase (se 2 (by rfl) ⟨637866, by rfl⟩ : syracuseStep 1700977 = 1275733) (by norm_num)
theorem B1913969 : Blo 1510952 1913969 := bbase (se 2 (by rfl) ⟨717738, by rfl⟩ : syracuseStep 1913969 = 1435477) (by norm_num)
theorem B5100677 : Blo 1510952 5100677 := bbase (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) (by norm_num)
theorem B1701013 : Blo 1510952 1701013 := bbase (se 6 (by rfl) ⟨39867, by rfl⟩ : syracuseStep 1701013 = 79735) (by norm_num)
theorem B1914025 : Blo 1510952 1914025 := bbase (se 2 (by rfl) ⟨717759, by rfl⟩ : syracuseStep 1914025 = 1435519) (by norm_num)
theorem B2553005 : Blo 1510952 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B1701049 : Blo 1510952 1701049 := bbase (se 2 (by rfl) ⟨637893, by rfl⟩ : syracuseStep 1701049 = 1275787) (by norm_num)
theorem B1701085 : Blo 1510952 1701085 := bbase (se 3 (by rfl) ⟨318953, by rfl⟩ : syracuseStep 1701085 = 637907) (by norm_num)
theorem B2269181 : Blo 1510952 2269181 := bbase (se 3 (by rfl) ⟨425471, by rfl⟩ : syracuseStep 2269181 = 850943) (by norm_num)
theorem B4846837 : Blo 1510952 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B1701121 : Blo 1510952 1701121 := bbase (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) (by norm_num)
theorem B5739781 : Blo 1510952 5739781 := bbase (se 4 (by rfl) ⟨538104, by rfl⟩ : syracuseStep 5739781 = 1076209) (by norm_num)
theorem B1914121 : Blo 1510952 1914121 := bbase (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) (by norm_num)
theorem B1701157 : Blo 1510952 1701157 := bbase (se 4 (by rfl) ⟨159483, by rfl⟩ : syracuseStep 1701157 = 318967) (by norm_num)
theorem B5387573 : Blo 1510952 5387573 := bbase (se 5 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 5387573 = 505085) (by norm_num)
theorem B1701193 : Blo 1510952 1701193 := bbase (se 2 (by rfl) ⟨637947, by rfl⟩ : syracuseStep 1701193 = 1275895) (by norm_num)
theorem B2266445 : Blo 1510952 2266445 := bbase (se 3 (by rfl) ⟨424958, by rfl⟩ : syracuseStep 2266445 = 849917) (by norm_num)
theorem B2266469 : Blo 1510952 2266469 := bbase (se 4 (by rfl) ⟨212481, by rfl⟩ : syracuseStep 2266469 = 424963) (by norm_num)
theorem B1701229 : Blo 1510952 1701229 := bbase (se 3 (by rfl) ⟨318980, by rfl⟩ : syracuseStep 1701229 = 637961) (by norm_num)
theorem B2266493 : Blo 1510952 2266493 := bbase (se 3 (by rfl) ⟨424967, by rfl⟩ : syracuseStep 2266493 = 849935) (by norm_num)
theorem B1701265 : Blo 1510952 1701265 := bbase (se 2 (by rfl) ⟨637974, by rfl⟩ : syracuseStep 1701265 = 1275949) (by norm_num)
theorem B2266517 : Blo 1510952 2266517 := bbase (se 6 (by rfl) ⟨53121, by rfl⟩ : syracuseStep 2266517 = 106243) (by norm_num)
theorem B2487709 : Blo 1510952 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3634589 : Blo 1510952 3634589 := bbase (se 3 (by rfl) ⟨681485, by rfl⟩ : syracuseStep 3634589 = 1362971) (by norm_num)
theorem B7976357 : Blo 1510952 7976357 := bbase (se 4 (by rfl) ⟨747783, by rfl⟩ : syracuseStep 7976357 = 1495567) (by norm_num)
theorem B2266541 : Blo 1510952 2266541 := bbase (se 3 (by rfl) ⟨424976, by rfl⟩ : syracuseStep 2266541 = 849953) (by norm_num)
theorem B1701301 : Blo 1510952 1701301 := bbase (se 5 (by rfl) ⟨79748, by rfl⟩ : syracuseStep 1701301 = 159497) (by norm_num)
theorem B1914293 : Blo 1510952 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B2266565 : Blo 1510952 2266565 := bbase (se 4 (by rfl) ⟨212490, by rfl⟩ : syracuseStep 2266565 = 424981) (by norm_num)
theorem B29439445 : Blo 1510952 29439445 := bbase (se 7 (by rfl) ⟨344993, by rfl⟩ : syracuseStep 29439445 = 689987) (by norm_num)
theorem B1701337 : Blo 1510952 1701337 := bbase (se 2 (by rfl) ⟨638001, by rfl⟩ : syracuseStep 1701337 = 1276003) (by norm_num)
theorem B2266589 : Blo 1510952 2266589 := bbase (se 3 (by rfl) ⟨424985, by rfl⟩ : syracuseStep 2266589 = 849971) (by norm_num)
theorem B1914349 : Blo 1510952 1914349 := bbase (se 3 (by rfl) ⟨358940, by rfl⟩ : syracuseStep 1914349 = 717881) (by norm_num)
theorem B2266613 : Blo 1510952 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1701373 : Blo 1510952 1701373 := bbase (se 3 (by rfl) ⟨319007, by rfl⟩ : syracuseStep 1701373 = 638015) (by norm_num)
theorem B2266637 : Blo 1510952 2266637 := bbase (se 3 (by rfl) ⟨424994, by rfl⟩ : syracuseStep 2266637 = 849989) (by norm_num)
theorem B1701409 : Blo 1510952 1701409 := bbase (se 2 (by rfl) ⟨638028, by rfl⟩ : syracuseStep 1701409 = 1276057) (by norm_num)
theorem B2266661 : Blo 1510952 2266661 := bbase (se 4 (by rfl) ⟨212499, by rfl⟩ : syracuseStep 2266661 = 424999) (by norm_num)
theorem B5101109 : Blo 1510952 5101109 := bbase (se 5 (by rfl) ⟨239114, by rfl⟩ : syracuseStep 5101109 = 478229) (by norm_num)
theorem B5740085 : Blo 1510952 5740085 := bbase (se 5 (by rfl) ⟨269066, by rfl⟩ : syracuseStep 5740085 = 538133) (by norm_num)
theorem B2266685 : Blo 1510952 2266685 := bbase (se 3 (by rfl) ⟨425003, by rfl⟩ : syracuseStep 2266685 = 850007) (by norm_num)
theorem B1701445 : Blo 1510952 1701445 := bbase (se 4 (by rfl) ⟨159510, by rfl⟩ : syracuseStep 1701445 = 319021) (by norm_num)
theorem B1914445 : Blo 1510952 1914445 := bbase (se 3 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 1914445 = 717917) (by norm_num)
theorem B2266709 : Blo 1510952 2266709 := bbase (se 8 (by rfl) ⟨13281, by rfl⟩ : syracuseStep 2266709 = 26563) (by norm_num)
theorem B1701481 : Blo 1510952 1701481 := bbase (se 2 (by rfl) ⟨638055, by rfl⟩ : syracuseStep 1701481 = 1276111) (by norm_num)
theorem B2266733 : Blo 1510952 2266733 := bbase (se 3 (by rfl) ⟨425012, by rfl⟩ : syracuseStep 2266733 = 850025) (by norm_num)
theorem B2266757 : Blo 1510952 2266757 := bbase (se 4 (by rfl) ⟨212508, by rfl⟩ : syracuseStep 2266757 = 425017) (by norm_num)
theorem B1701517 : Blo 1510952 1701517 := bbase (se 3 (by rfl) ⟨319034, by rfl⟩ : syracuseStep 1701517 = 638069) (by norm_num)
theorem B2266781 : Blo 1510952 2266781 := bbase (se 3 (by rfl) ⟨425021, by rfl⟩ : syracuseStep 2266781 = 850043) (by norm_num)
theorem B1701553 : Blo 1510952 1701553 := bbase (se 2 (by rfl) ⟨638082, by rfl⟩ : syracuseStep 1701553 = 1276165) (by norm_num)
theorem B2266805 : Blo 1510952 2266805 := bbase (se 5 (by rfl) ⟨106256, by rfl⟩ : syracuseStep 2266805 = 212513) (by norm_num)
theorem B2266829 : Blo 1510952 2266829 := bbase (se 3 (by rfl) ⟨425030, by rfl⟩ : syracuseStep 2266829 = 850061) (by norm_num)
theorem B1701589 : Blo 1510952 1701589 := bbase (se 7 (by rfl) ⟨19940, by rfl⟩ : syracuseStep 1701589 = 39881) (by norm_num)
theorem B2266853 : Blo 1510952 2266853 := bbase (se 4 (by rfl) ⟨212517, by rfl⟩ : syracuseStep 2266853 = 425035) (by norm_num)
theorem B1701625 : Blo 1510952 1701625 := bbase (se 2 (by rfl) ⟨638109, by rfl⟩ : syracuseStep 1701625 = 1276219) (by norm_num)
theorem B1914617 : Blo 1510952 1914617 := bbase (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) (by norm_num)
theorem B2266877 : Blo 1510952 2266877 := bbase (se 3 (by rfl) ⟨425039, by rfl⟩ : syracuseStep 2266877 = 850079) (by norm_num)
theorem B2266901 : Blo 1510952 2266901 := bbase (se 6 (by rfl) ⟨53130, by rfl⟩ : syracuseStep 2266901 = 106261) (by norm_num)
theorem B1701661 : Blo 1510952 1701661 := bbase (se 3 (by rfl) ⟨319061, by rfl⟩ : syracuseStep 1701661 = 638123) (by norm_num)
theorem B5601061 : Blo 1510952 5601061 := bbase (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) (by norm_num)
theorem B7657253 : Blo 1510952 7657253 := bbase (se 4 (by rfl) ⟨717867, by rfl⟩ : syracuseStep 7657253 = 1435735) (by norm_num)
theorem B2266925 : Blo 1510952 2266925 := bbase (se 3 (by rfl) ⟨425048, by rfl⟩ : syracuseStep 2266925 = 850097) (by norm_num)
theorem B1914673 : Blo 1510952 1914673 := bbase (se 2 (by rfl) ⟨718002, by rfl⟩ : syracuseStep 1914673 = 1436005) (by norm_num)
theorem B2586421 : Blo 1510952 2586421 := bbase (se 5 (by rfl) ⟨121238, by rfl⟩ : syracuseStep 2586421 = 242477) (by norm_num)
theorem B1701697 : Blo 1510952 1701697 := bbase (se 2 (by rfl) ⟨638136, by rfl⟩ : syracuseStep 1701697 = 1276273) (by norm_num)
theorem B2266949 : Blo 1510952 2266949 := bbase (se 4 (by rfl) ⟨212526, by rfl⟩ : syracuseStep 2266949 = 425053) (by norm_num)
theorem B2266973 : Blo 1510952 2266973 := bbase (se 3 (by rfl) ⟨425057, by rfl⟩ : syracuseStep 2266973 = 850115) (by norm_num)
theorem B1701733 : Blo 1510952 1701733 := bbase (se 4 (by rfl) ⟨159537, by rfl⟩ : syracuseStep 1701733 = 319075) (by norm_num)
theorem B2266997 : Blo 1510952 2266997 := bbase (se 5 (by rfl) ⟨106265, by rfl⟩ : syracuseStep 2266997 = 212531) (by norm_num)
theorem B1701769 : Blo 1510952 1701769 := bbase (se 2 (by rfl) ⟨638163, by rfl⟩ : syracuseStep 1701769 = 1276327) (by norm_num)
theorem B2267021 : Blo 1510952 2267021 := bbase (se 3 (by rfl) ⟨425066, by rfl⟩ : syracuseStep 2267021 = 850133) (by norm_num)
theorem B1914769 : Blo 1510952 1914769 := bbase (se 2 (by rfl) ⟨718038, by rfl⟩ : syracuseStep 1914769 = 1436077) (by norm_num)
theorem B2267045 : Blo 1510952 2267045 := bbase (se 4 (by rfl) ⟨212535, by rfl⟩ : syracuseStep 2267045 = 425071) (by norm_num)
theorem B1701805 : Blo 1510952 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B7264181 : Blo 1510952 7264181 := bbase (se 5 (by rfl) ⟨340508, by rfl⟩ : syracuseStep 7264181 = 681017) (by norm_num)
theorem B1841077 : Blo 1510952 1841077 := bbase (se 5 (by rfl) ⟨86300, by rfl⟩ : syracuseStep 1841077 = 172601) (by norm_num)
theorem B3880885 : Blo 1510952 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B2267069 : Blo 1510952 2267069 := bbase (se 3 (by rfl) ⟨425075, by rfl⟩ : syracuseStep 2267069 = 850151) (by norm_num)
theorem B1701841 : Blo 1510952 1701841 := bbase (se 2 (by rfl) ⟨638190, by rfl⟩ : syracuseStep 1701841 = 1276381) (by norm_num)
theorem B2267093 : Blo 1510952 2267093 := bbase (se 7 (by rfl) ⟨26567, by rfl⟩ : syracuseStep 2267093 = 53135) (by norm_num)
theorem B10901461 : Blo 1510952 10901461 := bbase (se 7 (by rfl) ⟨127751, by rfl⟩ : syracuseStep 10901461 = 255503) (by norm_num)
theorem B5101541 : Blo 1510952 5101541 := bbase (se 4 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 5101541 = 956539) (by norm_num)
theorem B2267117 : Blo 1510952 2267117 := bbase (se 3 (by rfl) ⟨425084, by rfl⟩ : syracuseStep 2267117 = 850169) (by norm_num)
theorem B1701877 : Blo 1510952 1701877 := bbase (se 5 (by rfl) ⟨79775, by rfl⟩ : syracuseStep 1701877 = 159551) (by norm_num)
theorem B2267141 : Blo 1510952 2267141 := bbase (se 4 (by rfl) ⟨212544, by rfl⟩ : syracuseStep 2267141 = 425089) (by norm_num)
theorem B1701913 : Blo 1510952 1701913 := bbase (se 2 (by rfl) ⟨638217, by rfl⟩ : syracuseStep 1701913 = 1276435) (by norm_num)
theorem B2267165 : Blo 1510952 2267165 := bbase (se 3 (by rfl) ⟨425093, by rfl⟩ : syracuseStep 2267165 = 850187) (by norm_num)
theorem B6461477 : Blo 1510952 6461477 := bbase (se 4 (by rfl) ⟨605763, by rfl⟩ : syracuseStep 6461477 = 1211527) (by norm_num)
theorem B2422829 : Blo 1510952 2422829 := bbase (se 3 (by rfl) ⟨454280, by rfl⟩ : syracuseStep 2422829 = 908561) (by norm_num)
theorem B10893365 : Blo 1510952 10893365 := bbase (se 5 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 10893365 = 1021253) (by norm_num)
theorem B2267189 : Blo 1510952 2267189 := bbase (se 5 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 2267189 = 212549) (by norm_num)
theorem B1701949 : Blo 1510952 1701949 := bbase (se 3 (by rfl) ⟨319115, by rfl⟩ : syracuseStep 1701949 = 638231) (by norm_num)
theorem B3881029 : Blo 1510952 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B2267213 : Blo 1510952 2267213 := bbase (se 3 (by rfl) ⟨425102, by rfl⟩ : syracuseStep 2267213 = 850205) (by norm_num)
theorem B1701985 : Blo 1510952 1701985 := bbase (se 2 (by rfl) ⟨638244, by rfl⟩ : syracuseStep 1701985 = 1276489) (by norm_num)
theorem B2267237 : Blo 1510952 2267237 := bbase (se 4 (by rfl) ⟨212553, by rfl⟩ : syracuseStep 2267237 = 425107) (by norm_num)
theorem B2267261 : Blo 1510952 2267261 := bbase (se 3 (by rfl) ⟨425111, by rfl⟩ : syracuseStep 2267261 = 850223) (by norm_num)
theorem B1702021 : Blo 1510952 1702021 := bbase (se 4 (by rfl) ⟨159564, by rfl⟩ : syracuseStep 1702021 = 319129) (by norm_num)
theorem B24508565 : Blo 1510952 24508565 := bbase (se 6 (by rfl) ⟨574419, by rfl⟩ : syracuseStep 24508565 = 1148839) (by norm_num)
theorem B2267285 : Blo 1510952 2267285 := bbase (se 6 (by rfl) ⟨53139, by rfl⟩ : syracuseStep 2267285 = 106279) (by norm_num)
theorem B1702057 : Blo 1510952 1702057 := bbase (se 2 (by rfl) ⟨638271, by rfl⟩ : syracuseStep 1702057 = 1276543) (by norm_num)
theorem B2267309 : Blo 1510952 2267309 := bbase (se 3 (by rfl) ⟨425120, by rfl⟩ : syracuseStep 2267309 = 850241) (by norm_num)
theorem B2422957 : Blo 1510952 2422957 := bbase (se 3 (by rfl) ⟨454304, by rfl⟩ : syracuseStep 2422957 = 908609) (by norm_num)
theorem B7649477 : Blo 1510952 7649477 := bbase (se 4 (by rfl) ⟨717138, by rfl⟩ : syracuseStep 7649477 = 1434277) (by norm_num)
theorem B2267333 : Blo 1510952 2267333 := bbase (se 4 (by rfl) ⟨212562, by rfl⟩ : syracuseStep 2267333 = 425125) (by norm_num)
theorem B2267357 : Blo 1510952 2267357 := bbase (se 3 (by rfl) ⟨425129, by rfl⟩ : syracuseStep 2267357 = 850259) (by norm_num)
theorem B2152669 : Blo 1510952 2152669 := bbase (se 3 (by rfl) ⟨403625, by rfl⟩ : syracuseStep 2152669 = 807251) (by norm_num)
theorem B2267381 : Blo 1510952 2267381 := bbase (se 5 (by rfl) ⟨106283, by rfl⟩ : syracuseStep 2267381 = 212567) (by norm_num)
theorem B2267405 : Blo 1510952 2267405 := bbase (se 3 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 2267405 = 850277) (by norm_num)
theorem B2726173 : Blo 1510952 2726173 := bbase (se 3 (by rfl) ⟨511157, by rfl⟩ : syracuseStep 2726173 = 1022315) (by norm_num)
theorem B2267429 : Blo 1510952 2267429 := bbase (se 4 (by rfl) ⟨212571, by rfl⟩ : syracuseStep 2267429 = 425143) (by norm_num)
theorem B3733813 : Blo 1510952 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B3447101 : Blo 1510952 3447101 := bbase (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) (by norm_num)
theorem B2267453 : Blo 1510952 2267453 := bbase (se 3 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 2267453 = 850295) (by norm_num)
theorem B6461765 : Blo 1510952 6461765 := bbase (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) (by norm_num)
theorem B31439189 : Blo 1510952 31439189 := bbase (se 10 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 31439189 = 92107) (by norm_num)
theorem B2267477 : Blo 1510952 2267477 := bbase (se 10 (by rfl) ⟨3321, by rfl⟩ : syracuseStep 2267477 = 6643) (by norm_num)
theorem B2267501 : Blo 1510952 2267501 := bbase (se 3 (by rfl) ⟨425156, by rfl⟩ : syracuseStep 2267501 = 850313) (by norm_num)
theorem B1816949 : Blo 1510952 1816949 := bbase (se 5 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 1816949 = 170339) (by norm_num)
theorem B2267525 : Blo 1510952 2267525 := bbase (se 4 (by rfl) ⟨212580, by rfl⟩ : syracuseStep 2267525 = 425161) (by norm_num)
theorem B5101973 : Blo 1510952 5101973 := bbase (se 6 (by rfl) ⟨119577, by rfl⟩ : syracuseStep 5101973 = 239155) (by norm_num)
theorem B2267549 : Blo 1510952 2267549 := bbase (se 3 (by rfl) ⟨425165, by rfl⟩ : syracuseStep 2267549 = 850331) (by norm_num)
theorem B2267573 : Blo 1510952 2267573 := bbase (se 5 (by rfl) ⟨106292, by rfl⟩ : syracuseStep 2267573 = 212585) (by norm_num)
theorem B2267597 : Blo 1510952 2267597 := bbase (se 3 (by rfl) ⟨425174, by rfl⟩ : syracuseStep 2267597 = 850349) (by norm_num)
theorem B3447269 : Blo 1510952 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B2267621 : Blo 1510952 2267621 := bbase (se 4 (by rfl) ⟨212589, by rfl⟩ : syracuseStep 2267621 = 425179) (by norm_num)
theorem B2267645 : Blo 1510952 2267645 := bbase (se 3 (by rfl) ⟨425183, by rfl⟩ : syracuseStep 2267645 = 850367) (by norm_num)
theorem B2267669 : Blo 1510952 2267669 := bbase (se 6 (by rfl) ⟨53148, by rfl⟩ : syracuseStep 2267669 = 106297) (by norm_num)
theorem B2267693 : Blo 1510952 2267693 := bbase (se 3 (by rfl) ⟨425192, by rfl⟩ : syracuseStep 2267693 = 850385) (by norm_num)
theorem B2267717 : Blo 1510952 2267717 := bbase (se 4 (by rfl) ⟨212598, by rfl⟩ : syracuseStep 2267717 = 425197) (by norm_num)
theorem B4307525 : Blo 1510952 4307525 := bbase (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) (by norm_num)
theorem B2267741 : Blo 1510952 2267741 := bbase (se 3 (by rfl) ⟨425201, by rfl⟩ : syracuseStep 2267741 = 850403) (by norm_num)
theorem B2267765 : Blo 1510952 2267765 := bbase (se 5 (by rfl) ⟨106301, by rfl⟩ : syracuseStep 2267765 = 212603) (by norm_num)
theorem B2267789 : Blo 1510952 2267789 := bbase (se 3 (by rfl) ⟨425210, by rfl⟩ : syracuseStep 2267789 = 850421) (by norm_num)
theorem B2267813 : Blo 1510952 2267813 := bbase (se 4 (by rfl) ⟨212607, by rfl⟩ : syracuseStep 2267813 = 425215) (by norm_num)
theorem B1817257 : Blo 1510952 1817257 := bbase (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) (by norm_num)
theorem B2267837 : Blo 1510952 2267837 := bbase (se 3 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 2267837 = 850439) (by norm_num)
theorem B2267861 : Blo 1510952 2267861 := bbase (se 7 (by rfl) ⟨26576, by rfl⟩ : syracuseStep 2267861 = 53153) (by norm_num)
theorem B2267885 : Blo 1510952 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B2267909 : Blo 1510952 2267909 := bbase (se 4 (by rfl) ⟨212616, by rfl⟩ : syracuseStep 2267909 = 425233) (by norm_num)
theorem B1817353 : Blo 1510952 1817353 := bbase (se 2 (by rfl) ⟨681507, by rfl⟩ : syracuseStep 1817353 = 1363015) (by norm_num)
theorem B2267933 : Blo 1510952 2267933 := bbase (se 3 (by rfl) ⟨425237, by rfl⟩ : syracuseStep 2267933 = 850475) (by norm_num)
theorem B2153261 : Blo 1510952 2153261 := bbase (se 3 (by rfl) ⟨403736, by rfl⟩ : syracuseStep 2153261 = 807473) (by norm_num)
theorem B2267957 : Blo 1510952 2267957 := bbase (se 5 (by rfl) ⟨106310, by rfl⟩ : syracuseStep 2267957 = 212621) (by norm_num)
theorem B5102405 : Blo 1510952 5102405 := bbase (se 4 (by rfl) ⟨478350, by rfl⟩ : syracuseStep 5102405 = 956701) (by norm_num)
theorem B2267981 : Blo 1510952 2267981 := bbase (se 3 (by rfl) ⟨425246, by rfl⟩ : syracuseStep 2267981 = 850493) (by norm_num)
theorem B2268005 : Blo 1510952 2268005 := bbase (se 4 (by rfl) ⟨212625, by rfl⟩ : syracuseStep 2268005 = 425251) (by norm_num)
theorem B9681781 : Blo 1510952 9681781 := bbase (se 5 (by rfl) ⟨453833, by rfl⟩ : syracuseStep 9681781 = 907667) (by norm_num)
theorem B2268029 : Blo 1510952 2268029 := bbase (se 3 (by rfl) ⟨425255, by rfl⟩ : syracuseStep 2268029 = 850511) (by norm_num)
theorem B2153341 : Blo 1510952 2153341 := bbase (se 3 (by rfl) ⟨403751, by rfl⟩ : syracuseStep 2153341 = 807503) (by norm_num)
theorem B2268053 : Blo 1510952 2268053 := bbase (se 6 (by rfl) ⟨53157, by rfl⟩ : syracuseStep 2268053 = 106315) (by norm_num)
theorem B2268077 : Blo 1510952 2268077 := bbase (se 3 (by rfl) ⟨425264, by rfl⟩ : syracuseStep 2268077 = 850529) (by norm_num)
theorem B2587565 : Blo 1510952 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B2268101 : Blo 1510952 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B2268125 : Blo 1510952 2268125 := bbase (se 3 (by rfl) ⟨425273, by rfl⟩ : syracuseStep 2268125 = 850547) (by norm_num)
theorem B2268149 : Blo 1510952 2268149 := bbase (se 5 (by rfl) ⟨106319, by rfl⟩ : syracuseStep 2268149 = 212639) (by norm_num)
theorem B2153461 : Blo 1510952 2153461 := bbase (se 5 (by rfl) ⟨100943, by rfl⟩ : syracuseStep 2153461 = 201887) (by norm_num)
theorem B1940473 : Blo 1510952 1940473 := bbase (se 2 (by rfl) ⟨727677, by rfl⟩ : syracuseStep 1940473 = 1455355) (by norm_num)
theorem B2268173 : Blo 1510952 2268173 := bbase (se 3 (by rfl) ⟨425282, by rfl⟩ : syracuseStep 2268173 = 850565) (by norm_num)
theorem B2268197 : Blo 1510952 2268197 := bbase (se 4 (by rfl) ⟨212643, by rfl⟩ : syracuseStep 2268197 = 425287) (by norm_num)
theorem B7658549 : Blo 1510952 7658549 := bbase (se 5 (by rfl) ⟨358994, by rfl⟩ : syracuseStep 7658549 = 717989) (by norm_num)
theorem B6462517 : Blo 1510952 6462517 := bbase (se 5 (by rfl) ⟨302930, by rfl⟩ : syracuseStep 6462517 = 605861) (by norm_num)
theorem B2268221 : Blo 1510952 2268221 := bbase (se 3 (by rfl) ⟨425291, by rfl⟩ : syracuseStep 2268221 = 850583) (by norm_num)
theorem B2268245 : Blo 1510952 2268245 := bbase (se 8 (by rfl) ⟨13290, by rfl⟩ : syracuseStep 2268245 = 26581) (by norm_num)
theorem B2153557 : Blo 1510952 2153557 := bbase (se 8 (by rfl) ⟨12618, by rfl⟩ : syracuseStep 2153557 = 25237) (by norm_num)
theorem B4660325 : Blo 1510952 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B2268269 : Blo 1510952 2268269 := bbase (se 3 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 2268269 = 850601) (by norm_num)
theorem B2268293 : Blo 1510952 2268293 := bbase (se 4 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 2268293 = 425305) (by norm_num)
theorem B2268317 : Blo 1510952 2268317 := bbase (se 3 (by rfl) ⟨425309, by rfl⟩ : syracuseStep 2268317 = 850619) (by norm_num)
theorem B2268341 : Blo 1510952 2268341 := bbase (se 5 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 2268341 = 212657) (by norm_num)
theorem B2268365 : Blo 1510952 2268365 := bbase (se 3 (by rfl) ⟨425318, by rfl⟩ : syracuseStep 2268365 = 850637) (by norm_num)
theorem B2268389 : Blo 1510952 2268389 := bbase (se 4 (by rfl) ⟨212661, by rfl⟩ : syracuseStep 2268389 = 425323) (by norm_num)
theorem B5102837 : Blo 1510952 5102837 := bbase (se 5 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 5102837 = 478391) (by norm_num)
theorem B2268413 : Blo 1510952 2268413 := bbase (se 3 (by rfl) ⟨425327, by rfl⟩ : syracuseStep 2268413 = 850655) (by norm_num)
theorem B2268437 : Blo 1510952 2268437 := bbase (se 6 (by rfl) ⟨53166, by rfl⟩ : syracuseStep 2268437 = 106333) (by norm_num)
theorem B3824941 : Blo 1510952 3824941 := bbase (se 3 (by rfl) ⟨717176, by rfl⟩ : syracuseStep 3824941 = 1434353) (by norm_num)
theorem B2268461 : Blo 1510952 2268461 := bbase (se 3 (by rfl) ⟨425336, by rfl⟩ : syracuseStep 2268461 = 850673) (by norm_num)
theorem B2268485 : Blo 1510952 2268485 := bbase (se 4 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 2268485 = 425341) (by norm_num)
theorem B2268509 : Blo 1510952 2268509 := bbase (se 3 (by rfl) ⟨425345, by rfl⟩ : syracuseStep 2268509 = 850691) (by norm_num)
theorem B6126949 : Blo 1510952 6126949 := bbase (se 4 (by rfl) ⟨574401, by rfl⟩ : syracuseStep 6126949 = 1148803) (by norm_num)
theorem B2268533 : Blo 1510952 2268533 := bbase (se 5 (by rfl) ⟨106337, by rfl⟩ : syracuseStep 2268533 = 212675) (by norm_num)
theorem B2268557 : Blo 1510952 2268557 := bbase (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) (by norm_num)
theorem B4595093 : Blo 1510952 4595093 := bbase (se 6 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 4595093 = 215395) (by norm_num)
theorem B3825053 : Blo 1510952 3825053 := bbase (se 3 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 3825053 = 1434395) (by norm_num)
theorem B2268581 : Blo 1510952 2268581 := bbase (se 4 (by rfl) ⟨212679, by rfl⟩ : syracuseStep 2268581 = 425359) (by norm_num)
theorem B9821621 : Blo 1510952 9821621 := bbase (se 5 (by rfl) ⟨460388, by rfl⟩ : syracuseStep 9821621 = 920777) (by norm_num)
theorem B2268605 : Blo 1510952 2268605 := bbase (se 3 (by rfl) ⟨425363, by rfl⟩ : syracuseStep 2268605 = 850727) (by norm_num)
theorem B6544837 : Blo 1510952 6544837 := bbase (se 4 (by rfl) ⟨613578, by rfl⟩ : syracuseStep 6544837 = 1227157) (by norm_num)
theorem B2760149 : Blo 1510952 2760149 := bbase (se 7 (by rfl) ⟨32345, by rfl⟩ : syracuseStep 2760149 = 64691) (by norm_num)
theorem B7650773 : Blo 1510952 7650773 := bbase (se 7 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 7650773 = 179315) (by norm_num)
theorem B2268629 : Blo 1510952 2268629 := bbase (se 7 (by rfl) ⟨26585, by rfl⟩ : syracuseStep 2268629 = 53171) (by norm_num)
theorem B44203477 : Blo 1510952 44203477 := bbase (se 7 (by rfl) ⟨518009, by rfl⟩ : syracuseStep 44203477 = 1036019) (by norm_num)
theorem B2268653 : Blo 1510952 2268653 := bbase (se 3 (by rfl) ⟨425372, by rfl⟩ : syracuseStep 2268653 = 850745) (by norm_num)
theorem B3227141 : Blo 1510952 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B2268677 : Blo 1510952 2268677 := bbase (se 4 (by rfl) ⟨212688, by rfl⟩ : syracuseStep 2268677 = 425377) (by norm_num)
theorem B2268701 : Blo 1510952 2268701 := bbase (se 3 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 2268701 = 850763) (by norm_num)
theorem B2268725 : Blo 1510952 2268725 := bbase (se 5 (by rfl) ⟨106346, by rfl⟩ : syracuseStep 2268725 = 212693) (by norm_num)
theorem B2154053 : Blo 1510952 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B2268749 : Blo 1510952 2268749 := bbase (se 3 (by rfl) ⟨425390, by rfl⟩ : syracuseStep 2268749 = 850781) (by norm_num)
theorem B3825245 : Blo 1510952 3825245 := bbase (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) (by norm_num)
theorem B2268773 : Blo 1510952 2268773 := bbase (se 4 (by rfl) ⟨212697, by rfl⟩ : syracuseStep 2268773 = 425395) (by norm_num)
theorem B5742197 : Blo 1510952 5742197 := bbase (se 5 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 5742197 = 538331) (by norm_num)
theorem B2268797 : Blo 1510952 2268797 := bbase (se 3 (by rfl) ⟨425399, by rfl⟩ : syracuseStep 2268797 = 850799) (by norm_num)
theorem B2268821 : Blo 1510952 2268821 := bbase (se 6 (by rfl) ⟨53175, by rfl⟩ : syracuseStep 2268821 = 106351) (by norm_num)
theorem B5103269 : Blo 1510952 5103269 := bbase (se 4 (by rfl) ⟨478431, by rfl⟩ : syracuseStep 5103269 = 956863) (by norm_num)
theorem B2268845 : Blo 1510952 2268845 := bbase (se 3 (by rfl) ⟨425408, by rfl⟩ : syracuseStep 2268845 = 850817) (by norm_num)
theorem B2268869 : Blo 1510952 2268869 := bbase (se 4 (by rfl) ⟨212706, by rfl⟩ : syracuseStep 2268869 = 425413) (by norm_num)
theorem B2268893 : Blo 1510952 2268893 := bbase (se 3 (by rfl) ⟨425417, by rfl⟩ : syracuseStep 2268893 = 850835) (by norm_num)
theorem B2268917 : Blo 1510952 2268917 := bbase (se 5 (by rfl) ⟨106355, by rfl⟩ : syracuseStep 2268917 = 212711) (by norm_num)
theorem B2268941 : Blo 1510952 2268941 := bbase (se 3 (by rfl) ⟨425426, by rfl⟩ : syracuseStep 2268941 = 850853) (by norm_num)
theorem B2268965 : Blo 1510952 2268965 := bbase (se 4 (by rfl) ⟨212715, by rfl⟩ : syracuseStep 2268965 = 425431) (by norm_num)
theorem B7757621 : Blo 1510952 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B2268989 : Blo 1510952 2268989 := bbase (se 3 (by rfl) ⟨425435, by rfl⟩ : syracuseStep 2268989 = 850871) (by norm_num)
theorem B1531721 : Blo 1510952 1531721 := bbase (se 2 (by rfl) ⟨574395, by rfl⟩ : syracuseStep 1531721 = 1148791) (by norm_num)
theorem B3063629 : Blo 1510952 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B2269013 : Blo 1510952 2269013 := bbase (se 9 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 2269013 = 13295) (by norm_num)
theorem B2269037 : Blo 1510952 2269037 := bbase (se 3 (by rfl) ⟨425444, by rfl⟩ : syracuseStep 2269037 = 850889) (by norm_num)
theorem B2269061 : Blo 1510952 2269061 := bbase (se 4 (by rfl) ⟨212724, by rfl⟩ : syracuseStep 2269061 = 425449) (by norm_num)
theorem B7364501 : Blo 1510952 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B5742485 : Blo 1510952 5742485 := bbase (se 6 (by rfl) ⟨134589, by rfl⟩ : syracuseStep 5742485 = 269179) (by norm_num)
theorem B2269085 : Blo 1510952 2269085 := bbase (se 3 (by rfl) ⟨425453, by rfl⟩ : syracuseStep 2269085 = 850907) (by norm_num)
theorem B1613729 : Blo 1510952 1613729 := bbase (se 2 (by rfl) ⟨605148, by rfl⟩ : syracuseStep 1613729 = 1210297) (by norm_num)
theorem B3825589 : Blo 1510952 3825589 := bbase (se 5 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 3825589 = 358649) (by norm_num)
theorem B2269109 : Blo 1510952 2269109 := bbase (se 5 (by rfl) ⟨106364, by rfl⟩ : syracuseStep 2269109 = 212729) (by norm_num)
theorem B2269133 : Blo 1510952 2269133 := bbase (se 3 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 2269133 = 850925) (by norm_num)
theorem B10346453 : Blo 1510952 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B2269157 : Blo 1510952 2269157 := bbase (se 4 (by rfl) ⟨212733, by rfl⟩ : syracuseStep 2269157 = 425467) (by norm_num)
theorem B1613801 : Blo 1510952 1613801 := bbase (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) (by norm_num)
theorem B3399677 : Blo 1510952 3399677 := bbase (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) (by norm_num)
theorem B4087811 : Blo 1510952 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2269187 : Blo 1510952 2269187 := bstep (se 1 (by rfl) ⟨1701890, by rfl⟩ : syracuseStep 2269187 = 3403781) B3403781
theorem B2269217 : Blo 1510952 2269217 := bstep (se 2 (by rfl) ⟨850956, by rfl⟩ : syracuseStep 2269217 = 1701913) B1701913
theorem B2269235 : Blo 1510952 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B3825731 : Blo 1510952 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B2269265 : Blo 1510952 2269265 := bstep (se 2 (by rfl) ⟨850974, by rfl⟩ : syracuseStep 2269265 = 1701949) B1701949
theorem B2269283 : Blo 1510952 2269283 := bstep (se 1 (by rfl) ⟨1701962, by rfl⟩ : syracuseStep 2269283 = 3403925) B3403925
theorem B2269313 : Blo 1510952 2269313 := bstep (se 2 (by rfl) ⟨850992, by rfl⟩ : syracuseStep 2269313 = 1701985) B1701985
theorem B2269331 : Blo 1510952 2269331 := bstep (se 1 (by rfl) ⟨1701998, by rfl⟩ : syracuseStep 2269331 = 3403997) B3403997
theorem B3399857 : Blo 1510952 3399857 := bstep (se 2 (by rfl) ⟨1274946, by rfl⟩ : syracuseStep 3399857 = 2549893) B2549893
theorem B3227825 : Blo 1510952 3227825 := bstep (se 2 (by rfl) ⟨1210434, by rfl⟩ : syracuseStep 3227825 = 2420869) B2420869
theorem B2269361 : Blo 1510952 2269361 := bstep (se 2 (by rfl) ⟨851010, by rfl⟩ : syracuseStep 2269361 = 1702021) B1702021
theorem B3399875 : Blo 1510952 3399875 := bstep (se 1 (by rfl) ⟨2549906, by rfl⟩ : syracuseStep 3399875 = 5099813) B5099813
theorem B2269379 : Blo 1510952 2269379 := bstep (se 1 (by rfl) ⟨1702034, by rfl⟩ : syracuseStep 2269379 = 3404069) B3404069
theorem B2269409 : Blo 1510952 2269409 := bstep (se 2 (by rfl) ⟨851028, by rfl⟩ : syracuseStep 2269409 = 1702057) B1702057
theorem B2269427 : Blo 1510952 2269427 := bstep (se 1 (by rfl) ⟨1702070, by rfl⟩ : syracuseStep 2269427 = 3404141) B3404141
theorem B8610083 : Blo 1510952 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B5103917 : Blo 1510952 5103917 := bstep (se 3 (by rfl) ⟨956984, by rfl⟩ : syracuseStep 5103917 = 1913969) B1913969
theorem B5103971 : Blo 1510952 5103971 := bstep (se 1 (by rfl) ⟨3827978, by rfl⟩ : syracuseStep 5103971 = 7655957) B7655957
theorem B1614211 : Blo 1510952 1614211 := bstep (se 1 (by rfl) ⟨1210658, by rfl⟩ : syracuseStep 1614211 = 2421317) B2421317
theorem B11485637 : Blo 1510952 11485637 := bstep (se 4 (by rfl) ⟨1076778, by rfl⟩ : syracuseStep 11485637 = 2153557) B2153557
theorem B3400145 : Blo 1510952 3400145 := bstep (se 2 (by rfl) ⟨1275054, by rfl⟩ : syracuseStep 3400145 = 2550109) B2550109
theorem B3400163 : Blo 1510952 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B1532467 : Blo 1510952 1532467 := bstep (se 1 (by rfl) ⟨1149350, by rfl⟩ : syracuseStep 1532467 = 2298701) B2298701
theorem B4907587 : Blo 1510952 4907587 := bstep (se 1 (by rfl) ⟨3680690, by rfl⟩ : syracuseStep 4907587 = 7361381) B7361381
theorem B5104241 : Blo 1510952 5104241 := bstep (se 2 (by rfl) ⟨1914090, by rfl⟩ : syracuseStep 5104241 = 3828181) B3828181
theorem B10904291 : Blo 1510952 10904291 := bstep (se 1 (by rfl) ⟨8178218, by rfl⟩ : syracuseStep 10904291 = 16356437) B16356437
theorem B3400433 : Blo 1510952 3400433 := bstep (se 2 (by rfl) ⟨1275162, by rfl⟩ : syracuseStep 3400433 = 2550325) B2550325
theorem B3400451 : Blo 1510952 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B7758605 : Blo 1510952 7758605 := bstep (se 3 (by rfl) ⟨1454738, by rfl⟩ : syracuseStep 7758605 = 2909477) B2909477
theorem B9192269 : Blo 1510952 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B83837837 : Blo 1510952 83837837 := bstep (se 3 (by rfl) ⟨15719594, by rfl⟩ : syracuseStep 83837837 = 31439189) B31439189
theorem B12911501 : Blo 1510952 12911501 := bstep (se 3 (by rfl) ⟨2420906, by rfl⟩ : syracuseStep 12911501 = 4841813) B4841813
theorem B5317571 : Blo 1510952 5317571 := bstep (se 1 (by rfl) ⟨3988178, by rfl⟩ : syracuseStep 5317571 = 7976357) B7976357
theorem B3826673 : Blo 1510952 3826673 := bstep (se 2 (by rfl) ⟨1435002, by rfl⟩ : syracuseStep 3826673 = 2870005) B2870005
theorem B3400721 : Blo 1510952 3400721 := bstep (se 2 (by rfl) ⟨1275270, by rfl⟩ : syracuseStep 3400721 = 2550541) B2550541
theorem B3400739 : Blo 1510952 3400739 := bstep (se 1 (by rfl) ⟨2550554, by rfl⟩ : syracuseStep 3400739 = 5101109) B5101109
theorem B3826723 : Blo 1510952 3826723 := bstep (se 1 (by rfl) ⟨2870042, by rfl⟩ : syracuseStep 3826723 = 5740085) B5740085
theorem B9692237 : Blo 1510952 9692237 := bstep (se 3 (by rfl) ⟨1817294, by rfl⟩ : syracuseStep 9692237 = 3634589) B3634589
theorem B6456419 : Blo 1510952 6456419 := bstep (se 1 (by rfl) ⟨4842314, by rfl⟩ : syracuseStep 6456419 = 9684629) B9684629
theorem B26190989 : Blo 1510952 26190989 := bstep (se 3 (by rfl) ⟨4910810, by rfl⟩ : syracuseStep 26190989 = 9821621) B9821621
theorem B5104781 : Blo 1510952 5104781 := bstep (se 3 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 5104781 = 1914293) B1914293
theorem B3826865 : Blo 1510952 3826865 := bstep (se 2 (by rfl) ⟨1435074, by rfl⟩ : syracuseStep 3826865 = 2870149) B2870149
theorem B5104835 : Blo 1510952 5104835 := bstep (se 1 (by rfl) ⟨3828626, by rfl⟩ : syracuseStep 5104835 = 7657253) B7657253
theorem B4842737 : Blo 1510952 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3401009 : Blo 1510952 3401009 := bstep (se 2 (by rfl) ⟨1275378, by rfl⟩ : syracuseStep 3401009 = 2550757) B2550757
theorem B2868547 : Blo 1510952 2868547 := bstep (se 1 (by rfl) ⟨2151410, by rfl⟩ : syracuseStep 2868547 = 4302821) B4302821
theorem B3401027 : Blo 1510952 3401027 := bstep (se 1 (by rfl) ⟨2550770, by rfl⟩ : syracuseStep 3401027 = 5101541) B5101541
theorem B4842929 : Blo 1510952 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B5105105 : Blo 1510952 5105105 := bstep (se 2 (by rfl) ⟨1914414, by rfl⟩ : syracuseStep 5105105 = 3828829) B3828829
theorem B5744141 : Blo 1510952 5744141 := bstep (se 3 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 5744141 = 2154053) B2154053
theorem B3401297 : Blo 1510952 3401297 := bstep (se 2 (by rfl) ⟨1275486, by rfl⟩ : syracuseStep 3401297 = 2550973) B2550973
theorem B3401315 : Blo 1510952 3401315 := bstep (se 1 (by rfl) ⟨2550986, by rfl⟩ : syracuseStep 3401315 = 5101973) B5101973
theorem B7653041 : Blo 1510952 7653041 := bstep (se 2 (by rfl) ⟨2869890, by rfl⟩ : syracuseStep 7653041 = 5739781) B5739781
theorem B2868995 : Blo 1510952 2868995 := bstep (se 1 (by rfl) ⟨2151746, by rfl⟩ : syracuseStep 2868995 = 4303493) B4303493
theorem B8169265 : Blo 1510952 8169265 := bstep (se 2 (by rfl) ⟨3063474, by rfl⟩ : syracuseStep 8169265 = 6126949) B6126949
theorem B3401585 : Blo 1510952 3401585 := bstep (se 2 (by rfl) ⟨1275594, by rfl⟩ : syracuseStep 3401585 = 2551189) B2551189
theorem B3401603 : Blo 1510952 3401603 := bstep (se 1 (by rfl) ⟨2551202, by rfl⟩ : syracuseStep 3401603 = 5102405) B5102405
theorem B8726449 : Blo 1510952 8726449 := bstep (se 2 (by rfl) ⟨3272418, by rfl⟩ : syracuseStep 8726449 = 6544837) B6544837
theorem B5105645 : Blo 1510952 5105645 := bstep (se 3 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 5105645 = 1914617) B1914617
theorem B2869283 : Blo 1510952 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B8177699 : Blo 1510952 8177699 := bstep (se 1 (by rfl) ⟨6133274, by rfl⟩ : syracuseStep 8177699 = 12266549) B12266549
theorem B5105699 : Blo 1510952 5105699 := bstep (se 1 (by rfl) ⟨3829274, by rfl⟩ : syracuseStep 5105699 = 7658549) B7658549
theorem B3106883 : Blo 1510952 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B2549873 : Blo 1510952 2549873 := bstep (se 2 (by rfl) ⟨956202, by rfl⟩ : syracuseStep 2549873 = 1912405) B1912405
theorem B3401873 : Blo 1510952 3401873 := bstep (se 2 (by rfl) ⟨1275702, by rfl⟩ : syracuseStep 3401873 = 2551405) B2551405
theorem B3827857 : Blo 1510952 3827857 := bstep (se 2 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 3827857 = 2870893) B2870893
theorem B3401891 : Blo 1510952 3401891 := bstep (se 1 (by rfl) ⟨2551418, by rfl⟩ : syracuseStep 3401891 = 5102837) B5102837
theorem B2550001 : Blo 1510952 2550001 := bstep (se 2 (by rfl) ⟨956250, by rfl⟩ : syracuseStep 2550001 = 1912501) B1912501
theorem B2550035 : Blo 1510952 2550035 := bstep (se 1 (by rfl) ⟨1912526, by rfl⟩ : syracuseStep 2550035 = 3825053) B3825053
theorem B5105969 : Blo 1510952 5105969 := bstep (se 2 (by rfl) ⟨1914738, by rfl⟩ : syracuseStep 5105969 = 3829477) B3829477
theorem B2550163 : Blo 1510952 2550163 := bstep (se 1 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 2550163 = 3825245) B3825245
theorem B3828131 : Blo 1510952 3828131 := bstep (se 1 (by rfl) ⟨2871098, by rfl⟩ : syracuseStep 3828131 = 5742197) B5742197
theorem B4303277 : Blo 1510952 4303277 := bstep (se 3 (by rfl) ⟨806864, by rfl⟩ : syracuseStep 4303277 = 1613729) B1613729
theorem B3402161 : Blo 1510952 3402161 := bstep (se 2 (by rfl) ⟨1275810, by rfl⟩ : syracuseStep 3402161 = 2551621) B2551621
theorem B3402179 : Blo 1510952 3402179 := bstep (se 1 (by rfl) ⟨2551634, by rfl⟩ : syracuseStep 3402179 = 5103269) B5103269
theorem B6900173 : Blo 1510952 6900173 := bstep (se 3 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 6900173 = 2587565) B2587565
theorem B2550305 : Blo 1510952 2550305 := bstep (se 2 (by rfl) ⟨956364, by rfl⟩ : syracuseStep 2550305 = 1912729) B1912729
theorem B5171747 : Blo 1510952 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B2042419 : Blo 1510952 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B4909667 : Blo 1510952 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B3828323 : Blo 1510952 3828323 := bstep (se 1 (by rfl) ⟨2871242, by rfl⟩ : syracuseStep 3828323 = 5742485) B5742485
theorem B4303469 : Blo 1510952 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B14535281 : Blo 1510952 14535281 := bstep (se 2 (by rfl) ⟨5450730, by rfl⟩ : syracuseStep 14535281 = 10901461) B10901461
theorem B2550433 : Blo 1510952 2550433 := bstep (se 2 (by rfl) ⟨956412, by rfl⟩ : syracuseStep 2550433 = 1912825) B1912825
theorem B2550467 : Blo 1510952 2550467 := bstep (se 1 (by rfl) ⟨1912850, by rfl⟩ : syracuseStep 2550467 = 3825701) B3825701
theorem B3402449 : Blo 1510952 3402449 := bstep (se 2 (by rfl) ⟨1275918, by rfl⟩ : syracuseStep 3402449 = 2551837) B2551837
theorem B6990563 : Blo 1510952 6990563 := bstep (se 1 (by rfl) ⟨5242922, by rfl⟩ : syracuseStep 6990563 = 10485845) B10485845
theorem B3402467 : Blo 1510952 3402467 := bstep (se 1 (by rfl) ⟨2551850, by rfl⟩ : syracuseStep 3402467 = 5103701) B5103701
theorem B2550595 : Blo 1510952 2550595 := bstep (se 1 (by rfl) ⟨1912946, by rfl⟩ : syracuseStep 2550595 = 3825893) B3825893
theorem B3230609 : Blo 1510952 3230609 := bstep (se 2 (by rfl) ⟨1211478, by rfl⟩ : syracuseStep 3230609 = 2422957) B2422957
theorem B2550737 : Blo 1510952 2550737 := bstep (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) B1913053
theorem B2870225 : Blo 1510952 2870225 := bstep (se 2 (by rfl) ⟨1076334, by rfl⟩ : syracuseStep 2870225 = 2152669) B2152669
theorem B3402737 : Blo 1510952 3402737 := bstep (se 2 (by rfl) ⟨1276026, by rfl⟩ : syracuseStep 3402737 = 2552053) B2552053
theorem B3402755 : Blo 1510952 3402755 := bstep (se 1 (by rfl) ⟨2552066, by rfl⟩ : syracuseStep 3402755 = 5104133) B5104133
theorem B6458417 : Blo 1510952 6458417 := bstep (se 2 (by rfl) ⟨2421906, by rfl⟩ : syracuseStep 6458417 = 4843813) B4843813
theorem B2550865 : Blo 1510952 2550865 := bstep (se 2 (by rfl) ⟨956574, by rfl⟩ : syracuseStep 2550865 = 1913149) B1913149
theorem B7654499 : Blo 1510952 7654499 := bstep (se 1 (by rfl) ⟨5740874, by rfl⟩ : syracuseStep 7654499 = 11481749) B11481749
theorem B2550899 : Blo 1510952 2550899 := bstep (se 1 (by rfl) ⟨1913174, by rfl⟩ : syracuseStep 2550899 = 3826349) B3826349
theorem B17214605 : Blo 1510952 17214605 := bstep (se 3 (by rfl) ⟨3227738, by rfl⟩ : syracuseStep 17214605 = 6455477) B6455477
theorem B2043073 : Blo 1510952 2043073 := bstep (se 2 (by rfl) ⟨766152, by rfl⟩ : syracuseStep 2043073 = 1532305) B1532305
theorem B11480291 : Blo 1510952 11480291 := bstep (se 1 (by rfl) ⟨8610218, by rfl⟩ : syracuseStep 11480291 = 17220437) B17220437
theorem B2551027 : Blo 1510952 2551027 := bstep (se 1 (by rfl) ⟨1913270, by rfl⟩ : syracuseStep 2551027 = 3826541) B3826541
theorem B2043139 : Blo 1510952 2043139 := bstep (se 1 (by rfl) ⟨1532354, by rfl⟩ : syracuseStep 2043139 = 3064709) B3064709
theorem B3403025 : Blo 1510952 3403025 := bstep (se 2 (by rfl) ⟨1276134, by rfl⟩ : syracuseStep 3403025 = 2552269) B2552269
theorem B3403043 : Blo 1510952 3403043 := bstep (se 1 (by rfl) ⟨2552282, by rfl⟩ : syracuseStep 3403043 = 5104565) B5104565
theorem B2551169 : Blo 1510952 2551169 := bstep (se 2 (by rfl) ⟨956688, by rfl⟩ : syracuseStep 2551169 = 1913377) B1913377
theorem B8613317 : Blo 1510952 8613317 := bstep (se 4 (by rfl) ⟨807498, by rfl⟩ : syracuseStep 8613317 = 1614997) B1614997
theorem B2551297 : Blo 1510952 2551297 := bstep (se 2 (by rfl) ⟨956736, by rfl⟩ : syracuseStep 2551297 = 1913473) B1913473
theorem B14536205 : Blo 1510952 14536205 := bstep (se 3 (by rfl) ⟨2725538, by rfl⟩ : syracuseStep 14536205 = 5451077) B5451077
theorem B3829265 : Blo 1510952 3829265 := bstep (se 2 (by rfl) ⟨1435974, by rfl⟩ : syracuseStep 3829265 = 2871949) B2871949
theorem B1912339 : Blo 1510952 1912339 := bstep (se 1 (by rfl) ⟨1434254, by rfl⟩ : syracuseStep 1912339 = 2868509) B2868509
theorem B2551331 : Blo 1510952 2551331 := bstep (se 1 (by rfl) ⟨1913498, by rfl⟩ : syracuseStep 2551331 = 3826997) B3826997
theorem B3591715 : Blo 1510952 3591715 := bstep (se 1 (by rfl) ⟨2693786, by rfl⟩ : syracuseStep 3591715 = 5387573) B5387573
theorem B2723377 : Blo 1510952 2723377 := bstep (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) B2042533
theorem B3403313 : Blo 1510952 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B1510963 : Blo 1510952 1510963 := bstep (se 1 (by rfl) ⟨1133222, by rfl⟩ : syracuseStep 1510963 = 2266445) B2266445
theorem B1510979 : Blo 1510952 1510979 := bstep (se 1 (by rfl) ⟨1133234, by rfl⟩ : syracuseStep 1510979 = 2266469) B2266469
theorem B3403331 : Blo 1510952 3403331 := bstep (se 1 (by rfl) ⟨2552498, by rfl⟩ : syracuseStep 3403331 = 5104997) B5104997
theorem B3829315 : Blo 1510952 3829315 := bstep (se 1 (by rfl) ⟨2871986, by rfl⟩ : syracuseStep 3829315 = 5743973) B5743973
theorem B4304461 : Blo 1510952 4304461 := bstep (se 3 (by rfl) ⟨807086, by rfl⟩ : syracuseStep 4304461 = 1614173) B1614173
theorem B1510995 : Blo 1510952 1510995 := bstep (se 1 (by rfl) ⟨1133246, by rfl⟩ : syracuseStep 1510995 = 2266493) B2266493
theorem B1511011 : Blo 1510952 1511011 := bstep (se 1 (by rfl) ⟨1133258, by rfl⟩ : syracuseStep 1511011 = 2266517) B2266517
theorem B1511027 : Blo 1510952 1511027 := bstep (se 1 (by rfl) ⟨1133270, by rfl⟩ : syracuseStep 1511027 = 2266541) B2266541
theorem B1511043 : Blo 1510952 1511043 := bstep (se 1 (by rfl) ⟨1133282, by rfl⟩ : syracuseStep 1511043 = 2266565) B2266565
theorem B4845197 : Blo 1510952 4845197 := bstep (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) B1816949
theorem B2420369 : Blo 1510952 2420369 := bstep (se 2 (by rfl) ⟨907638, by rfl⟩ : syracuseStep 2420369 = 1815277) B1815277
theorem B1511059 : Blo 1510952 1511059 := bstep (se 1 (by rfl) ⟨1133294, by rfl⟩ : syracuseStep 1511059 = 2266589) B2266589
theorem B1511075 : Blo 1510952 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B2551459 : Blo 1510952 2551459 := bstep (se 1 (by rfl) ⟨1913594, by rfl⟩ : syracuseStep 2551459 = 3827189) B3827189
theorem B1511091 : Blo 1510952 1511091 := bstep (se 1 (by rfl) ⟨1133318, by rfl⟩ : syracuseStep 1511091 = 2266637) B2266637
theorem B2043571 : Blo 1510952 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B1511107 : Blo 1510952 1511107 := bstep (se 1 (by rfl) ⟨1133330, by rfl⟩ : syracuseStep 1511107 = 2266661) B2266661
theorem B3829457 : Blo 1510952 3829457 := bstep (se 2 (by rfl) ⟨1436046, by rfl⟩ : syracuseStep 3829457 = 2872093) B2872093
theorem B1511123 : Blo 1510952 1511123 := bstep (se 1 (by rfl) ⟨1133342, by rfl⟩ : syracuseStep 1511123 = 2266685) B2266685
theorem B1511139 : Blo 1510952 1511139 := bstep (se 1 (by rfl) ⟨1133354, by rfl⟩ : syracuseStep 1511139 = 2266709) B2266709
theorem B1511155 : Blo 1510952 1511155 := bstep (se 1 (by rfl) ⟨1133366, by rfl⟩ : syracuseStep 1511155 = 2266733) B2266733
theorem B2043635 : Blo 1510952 2043635 := bstep (se 1 (by rfl) ⟨1532726, by rfl⟩ : syracuseStep 2043635 = 3065453) B3065453
theorem B1511171 : Blo 1510952 1511171 := bstep (se 1 (by rfl) ⟨1133378, by rfl⟩ : syracuseStep 1511171 = 2266757) B2266757
theorem B1511187 : Blo 1510952 1511187 := bstep (se 1 (by rfl) ⟨1133390, by rfl⟩ : syracuseStep 1511187 = 2266781) B2266781
theorem B1511203 : Blo 1510952 1511203 := bstep (se 1 (by rfl) ⟨1133402, by rfl⟩ : syracuseStep 1511203 = 2266805) B2266805
theorem B2551601 : Blo 1510952 2551601 := bstep (se 2 (by rfl) ⟨956850, by rfl⟩ : syracuseStep 2551601 = 1913701) B1913701
theorem B5451569 : Blo 1510952 5451569 := bstep (se 2 (by rfl) ⟨2044338, by rfl⟩ : syracuseStep 5451569 = 4088677) B4088677
theorem B1511219 : Blo 1510952 1511219 := bstep (se 1 (by rfl) ⟨1133414, by rfl⟩ : syracuseStep 1511219 = 2266829) B2266829
theorem B1511235 : Blo 1510952 1511235 := bstep (se 1 (by rfl) ⟨1133426, by rfl⟩ : syracuseStep 1511235 = 2266853) B2266853
theorem B2420561 : Blo 1510952 2420561 := bstep (se 2 (by rfl) ⟨907710, by rfl⟩ : syracuseStep 2420561 = 1815421) B1815421
theorem B2871121 : Blo 1510952 2871121 := bstep (se 2 (by rfl) ⟨1076670, by rfl⟩ : syracuseStep 2871121 = 2153341) B2153341
theorem B1511251 : Blo 1510952 1511251 := bstep (se 1 (by rfl) ⟨1133438, by rfl⟩ : syracuseStep 1511251 = 2266877) B2266877
theorem B3403601 : Blo 1510952 3403601 := bstep (se 2 (by rfl) ⟨1276350, by rfl⟩ : syracuseStep 3403601 = 2552701) B2552701
theorem B1511267 : Blo 1510952 1511267 := bstep (se 1 (by rfl) ⟨1133450, by rfl⟩ : syracuseStep 1511267 = 2266901) B2266901
theorem B3403619 : Blo 1510952 3403619 := bstep (se 1 (by rfl) ⟨2552714, by rfl⟩ : syracuseStep 3403619 = 5105429) B5105429
theorem B1511283 : Blo 1510952 1511283 := bstep (se 1 (by rfl) ⟨1133462, by rfl⟩ : syracuseStep 1511283 = 2266925) B2266925
theorem B2297729 : Blo 1510952 2297729 := bstep (se 2 (by rfl) ⟨861648, by rfl⟩ : syracuseStep 2297729 = 1723297) B1723297
theorem B1511299 : Blo 1510952 1511299 := bstep (se 1 (by rfl) ⟨1133474, by rfl⟩ : syracuseStep 1511299 = 2266949) B2266949
theorem B4140931 : Blo 1510952 4140931 := bstep (se 1 (by rfl) ⟨3105698, by rfl⟩ : syracuseStep 4140931 = 6211397) B6211397
theorem B7655309 : Blo 1510952 7655309 := bstep (se 3 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 7655309 = 2870741) B2870741
theorem B8613773 : Blo 1510952 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1511315 : Blo 1510952 1511315 := bstep (se 1 (by rfl) ⟨1133486, by rfl⟩ : syracuseStep 1511315 = 2266973) B2266973
theorem B1511331 : Blo 1510952 1511331 := bstep (se 1 (by rfl) ⟨1133498, by rfl⟩ : syracuseStep 1511331 = 2266997) B2266997
theorem B3878833 : Blo 1510952 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B2551729 : Blo 1510952 2551729 := bstep (se 2 (by rfl) ⟨956898, by rfl⟩ : syracuseStep 2551729 = 1913797) B1913797
theorem B1511347 : Blo 1510952 1511347 := bstep (se 1 (by rfl) ⟨1133510, by rfl⟩ : syracuseStep 1511347 = 2267021) B2267021
theorem B1511363 : Blo 1510952 1511363 := bstep (se 1 (by rfl) ⟨1133522, by rfl⟩ : syracuseStep 1511363 = 2267045) B2267045
theorem B1511379 : Blo 1510952 1511379 := bstep (se 1 (by rfl) ⟨1133534, by rfl⟩ : syracuseStep 1511379 = 2267069) B2267069
theorem B2551763 : Blo 1510952 2551763 := bstep (se 1 (by rfl) ⟨1913822, by rfl⟩ : syracuseStep 2551763 = 3827645) B3827645
theorem B1511395 : Blo 1510952 1511395 := bstep (se 1 (by rfl) ⟨1133546, by rfl⟩ : syracuseStep 1511395 = 2267093) B2267093
theorem B14528483 : Blo 1510952 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B2871281 : Blo 1510952 2871281 := bstep (se 2 (by rfl) ⟨1076730, by rfl⟩ : syracuseStep 2871281 = 2153461) B2153461
theorem B1511411 : Blo 1510952 1511411 := bstep (se 1 (by rfl) ⟨1133558, by rfl⟩ : syracuseStep 1511411 = 2267117) B2267117
theorem B1699843 : Blo 1510952 1699843 := bstep (se 1 (by rfl) ⟨1274882, by rfl⟩ : syracuseStep 1699843 = 2549765) B2549765
theorem B1912835 : Blo 1510952 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B1511427 : Blo 1510952 1511427 := bstep (se 1 (by rfl) ⟨1133570, by rfl⟩ : syracuseStep 1511427 = 2267141) B2267141
theorem B8605709 : Blo 1510952 8605709 := bstep (se 3 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 8605709 = 3227141) B3227141
theorem B1511443 : Blo 1510952 1511443 := bstep (se 1 (by rfl) ⟨1133582, by rfl⟩ : syracuseStep 1511443 = 2267165) B2267165
theorem B7262243 : Blo 1510952 7262243 := bstep (se 1 (by rfl) ⟨5446682, by rfl⟩ : syracuseStep 7262243 = 10893365) B10893365
theorem B1511459 : Blo 1510952 1511459 := bstep (se 1 (by rfl) ⟨1133594, by rfl⟩ : syracuseStep 1511459 = 2267189) B2267189
theorem B1511475 : Blo 1510952 1511475 := bstep (se 1 (by rfl) ⟨1133606, by rfl⟩ : syracuseStep 1511475 = 2267213) B2267213
theorem B1511491 : Blo 1510952 1511491 := bstep (se 1 (by rfl) ⟨1133618, by rfl⟩ : syracuseStep 1511491 = 2267237) B2267237
theorem B5099597 : Blo 1510952 5099597 := bstep (se 3 (by rfl) ⟨956174, by rfl⟩ : syracuseStep 5099597 = 1912349) B1912349
theorem B1511507 : Blo 1510952 1511507 := bstep (se 1 (by rfl) ⟨1133630, by rfl⟩ : syracuseStep 1511507 = 2267261) B2267261
theorem B2551891 : Blo 1510952 2551891 := bstep (se 1 (by rfl) ⟨1913918, by rfl⟩ : syracuseStep 2551891 = 3827837) B3827837
theorem B16339043 : Blo 1510952 16339043 := bstep (se 1 (by rfl) ⟨12254282, by rfl⟩ : syracuseStep 16339043 = 24508565) B24508565
theorem B1511523 : Blo 1510952 1511523 := bstep (se 1 (by rfl) ⟨1133642, by rfl⟩ : syracuseStep 1511523 = 2267285) B2267285
theorem B3403889 : Blo 1510952 3403889 := bstep (se 2 (by rfl) ⟨1276458, by rfl⟩ : syracuseStep 3403889 = 2552917) B2552917
theorem B1511539 : Blo 1510952 1511539 := bstep (se 1 (by rfl) ⟨1133654, by rfl⟩ : syracuseStep 1511539 = 2267309) B2267309
theorem B5099651 : Blo 1510952 5099651 := bstep (se 1 (by rfl) ⟨3824738, by rfl⟩ : syracuseStep 5099651 = 7649477) B7649477
theorem B1511555 : Blo 1510952 1511555 := bstep (se 1 (by rfl) ⟨1133666, by rfl⟩ : syracuseStep 1511555 = 2267333) B2267333
theorem B5173379 : Blo 1510952 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B1699987 : Blo 1510952 1699987 := bstep (se 1 (by rfl) ⟨1274990, by rfl⟩ : syracuseStep 1699987 = 2549981) B2549981
theorem B1511571 : Blo 1510952 1511571 := bstep (se 1 (by rfl) ⟨1133678, by rfl⟩ : syracuseStep 1511571 = 2267357) B2267357
theorem B1511587 : Blo 1510952 1511587 := bstep (se 1 (by rfl) ⟨1133690, by rfl⟩ : syracuseStep 1511587 = 2267381) B2267381
theorem B1511603 : Blo 1510952 1511603 := bstep (se 1 (by rfl) ⟨1133702, by rfl⟩ : syracuseStep 1511603 = 2267405) B2267405
theorem B1511619 : Blo 1510952 1511619 := bstep (se 1 (by rfl) ⟨1133714, by rfl⟩ : syracuseStep 1511619 = 2267429) B2267429
theorem B1511635 : Blo 1510952 1511635 := bstep (se 1 (by rfl) ⟨1133726, by rfl⟩ : syracuseStep 1511635 = 2267453) B2267453
theorem B2552033 : Blo 1510952 2552033 := bstep (se 2 (by rfl) ⟨957012, by rfl⟩ : syracuseStep 2552033 = 1914025) B1914025
theorem B1511651 : Blo 1510952 1511651 := bstep (se 1 (by rfl) ⟨1133738, by rfl⟩ : syracuseStep 1511651 = 2267477) B2267477
theorem B1511667 : Blo 1510952 1511667 := bstep (se 1 (by rfl) ⟨1133750, by rfl⟩ : syracuseStep 1511667 = 2267501) B2267501
theorem B1511683 : Blo 1510952 1511683 := bstep (se 1 (by rfl) ⟨1133762, by rfl⟩ : syracuseStep 1511683 = 2267525) B2267525
theorem B1511699 : Blo 1510952 1511699 := bstep (se 1 (by rfl) ⟨1133774, by rfl⟩ : syracuseStep 1511699 = 2267549) B2267549
theorem B1700131 : Blo 1510952 1700131 := bstep (se 1 (by rfl) ⟨1275098, by rfl⟩ : syracuseStep 1700131 = 2550197) B2550197
theorem B1511715 : Blo 1510952 1511715 := bstep (se 1 (by rfl) ⟨1133786, by rfl⟩ : syracuseStep 1511715 = 2267573) B2267573
theorem B1511731 : Blo 1510952 1511731 := bstep (se 1 (by rfl) ⟨1133798, by rfl⟩ : syracuseStep 1511731 = 2267597) B2267597
theorem B2298179 : Blo 1510952 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B1511747 : Blo 1510952 1511747 := bstep (se 1 (by rfl) ⟨1133810, by rfl⟩ : syracuseStep 1511747 = 2267621) B2267621
theorem B1511763 : Blo 1510952 1511763 := bstep (se 1 (by rfl) ⟨1133822, by rfl⟩ : syracuseStep 1511763 = 2267645) B2267645
theorem B2552161 : Blo 1510952 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B1511779 : Blo 1510952 1511779 := bstep (se 1 (by rfl) ⟨1133834, by rfl⟩ : syracuseStep 1511779 = 2267669) B2267669
theorem B11645297 : Blo 1510952 11645297 := bstep (se 2 (by rfl) ⟨4366986, by rfl⟩ : syracuseStep 11645297 = 8733973) B8733973
theorem B1511795 : Blo 1510952 1511795 := bstep (se 1 (by rfl) ⟨1133846, by rfl⟩ : syracuseStep 1511795 = 2267693) B2267693
theorem B1511811 : Blo 1510952 1511811 := bstep (se 1 (by rfl) ⟨1133858, by rfl⟩ : syracuseStep 1511811 = 2267717) B2267717
theorem B2552195 : Blo 1510952 2552195 := bstep (se 1 (by rfl) ⟨1914146, by rfl⟩ : syracuseStep 2552195 = 3828293) B3828293
theorem B2871683 : Blo 1510952 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B5099921 : Blo 1510952 5099921 := bstep (se 2 (by rfl) ⟨1912470, by rfl⟩ : syracuseStep 5099921 = 3824941) B3824941
theorem B1511827 : Blo 1510952 1511827 := bstep (se 1 (by rfl) ⟨1133870, by rfl⟩ : syracuseStep 1511827 = 2267741) B2267741
theorem B1511843 : Blo 1510952 1511843 := bstep (se 1 (by rfl) ⟨1133882, by rfl⟩ : syracuseStep 1511843 = 2267765) B2267765
theorem B1700275 : Blo 1510952 1700275 := bstep (se 1 (by rfl) ⟨1275206, by rfl⟩ : syracuseStep 1700275 = 2550413) B2550413
theorem B1511859 : Blo 1510952 1511859 := bstep (se 1 (by rfl) ⟨1133894, by rfl⟩ : syracuseStep 1511859 = 2267789) B2267789
theorem B1511875 : Blo 1510952 1511875 := bstep (se 1 (by rfl) ⟨1133906, by rfl⟩ : syracuseStep 1511875 = 2267813) B2267813
theorem B1511891 : Blo 1510952 1511891 := bstep (se 1 (by rfl) ⟨1133918, by rfl⟩ : syracuseStep 1511891 = 2267837) B2267837
theorem B1511907 : Blo 1510952 1511907 := bstep (se 1 (by rfl) ⟨1133930, by rfl⟩ : syracuseStep 1511907 = 2267861) B2267861
theorem B1511923 : Blo 1510952 1511923 := bstep (se 1 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 1511923 = 2267885) B2267885
theorem B1511939 : Blo 1510952 1511939 := bstep (se 1 (by rfl) ⟨1133954, by rfl⟩ : syracuseStep 1511939 = 2267909) B2267909
theorem B2552323 : Blo 1510952 2552323 := bstep (se 1 (by rfl) ⟨1914242, by rfl⟩ : syracuseStep 2552323 = 3828485) B3828485
theorem B2298385 : Blo 1510952 2298385 := bstep (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) B1723789
theorem B1511955 : Blo 1510952 1511955 := bstep (se 1 (by rfl) ⟨1133966, by rfl⟩ : syracuseStep 1511955 = 2267933) B2267933
theorem B3403907 : Blo 1510952 3403907 := bstep (se 1 (by rfl) ⟨2552930, by rfl⟩ : syracuseStep 3403907 = 5105861) B5105861
theorem B1511971 : Blo 1510952 1511971 := bstep (se 1 (by rfl) ⟨1133978, by rfl⟩ : syracuseStep 1511971 = 2267957) B2267957
theorem B1511987 : Blo 1510952 1511987 := bstep (se 1 (by rfl) ⟨1133990, by rfl⟩ : syracuseStep 1511987 = 2267981) B2267981
theorem B1700419 : Blo 1510952 1700419 := bstep (se 1 (by rfl) ⟨1275314, by rfl⟩ : syracuseStep 1700419 = 2550629) B2550629
theorem B1512003 : Blo 1510952 1512003 := bstep (se 1 (by rfl) ⟨1134002, by rfl⟩ : syracuseStep 1512003 = 2268005) B2268005
theorem B1512019 : Blo 1510952 1512019 := bstep (se 1 (by rfl) ⟨1134014, by rfl⟩ : syracuseStep 1512019 = 2268029) B2268029
theorem B1512035 : Blo 1510952 1512035 := bstep (se 1 (by rfl) ⟨1134026, by rfl⟩ : syracuseStep 1512035 = 2268053) B2268053
theorem B39252593 : Blo 1510952 39252593 := bstep (se 2 (by rfl) ⟨14719722, by rfl⟩ : syracuseStep 39252593 = 29439445) B29439445
theorem B58937969 : Blo 1510952 58937969 := bstep (se 2 (by rfl) ⟨22101738, by rfl⟩ : syracuseStep 58937969 = 44203477) B44203477
theorem B1512051 : Blo 1510952 1512051 := bstep (se 1 (by rfl) ⟨1134038, by rfl⟩ : syracuseStep 1512051 = 2268077) B2268077
theorem B1512067 : Blo 1510952 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B2552465 : Blo 1510952 2552465 := bstep (se 2 (by rfl) ⟨957174, by rfl⟩ : syracuseStep 2552465 = 1914349) B1914349
theorem B1512083 : Blo 1510952 1512083 := bstep (se 1 (by rfl) ⟨1134062, by rfl⟩ : syracuseStep 1512083 = 2268125) B2268125
theorem B1512099 : Blo 1510952 1512099 := bstep (se 1 (by rfl) ⟨1134074, by rfl⟩ : syracuseStep 1512099 = 2268149) B2268149
theorem B1512115 : Blo 1510952 1512115 := bstep (se 1 (by rfl) ⟨1134086, by rfl⟩ : syracuseStep 1512115 = 2268173) B2268173
theorem B1913539 : Blo 1510952 1913539 := bstep (se 1 (by rfl) ⟨1435154, by rfl⟩ : syracuseStep 1913539 = 2870309) B2870309
theorem B1512131 : Blo 1510952 1512131 := bstep (se 1 (by rfl) ⟨1134098, by rfl⟩ : syracuseStep 1512131 = 2268197) B2268197
theorem B1700563 : Blo 1510952 1700563 := bstep (se 1 (by rfl) ⟨1275422, by rfl⟩ : syracuseStep 1700563 = 2550845) B2550845
theorem B1512147 : Blo 1510952 1512147 := bstep (se 1 (by rfl) ⟨1134110, by rfl⟩ : syracuseStep 1512147 = 2268221) B2268221
theorem B1512163 : Blo 1510952 1512163 := bstep (se 1 (by rfl) ⟨1134122, by rfl⟩ : syracuseStep 1512163 = 2268245) B2268245
theorem B1512179 : Blo 1510952 1512179 := bstep (se 1 (by rfl) ⟨1134134, by rfl⟩ : syracuseStep 1512179 = 2268269) B2268269
theorem B1512195 : Blo 1510952 1512195 := bstep (se 1 (by rfl) ⟨1134146, by rfl⟩ : syracuseStep 1512195 = 2268293) B2268293
theorem B2552593 : Blo 1510952 2552593 := bstep (se 2 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 2552593 = 1914445) B1914445
theorem B1512211 : Blo 1510952 1512211 := bstep (se 1 (by rfl) ⟨1134158, by rfl⟩ : syracuseStep 1512211 = 2268317) B2268317
theorem B1913635 : Blo 1510952 1913635 := bstep (se 1 (by rfl) ⟨1435226, by rfl⟩ : syracuseStep 1913635 = 2870453) B2870453
theorem B1512227 : Blo 1510952 1512227 := bstep (se 1 (by rfl) ⟨1134170, by rfl⟩ : syracuseStep 1512227 = 2268341) B2268341
theorem B1512243 : Blo 1510952 1512243 := bstep (se 1 (by rfl) ⟨1134182, by rfl⟩ : syracuseStep 1512243 = 2268365) B2268365
theorem B2552627 : Blo 1510952 2552627 := bstep (se 1 (by rfl) ⟨1914470, by rfl⟩ : syracuseStep 2552627 = 3828941) B3828941
theorem B1512259 : Blo 1510952 1512259 := bstep (se 1 (by rfl) ⟨1134194, by rfl⟩ : syracuseStep 1512259 = 2268389) B2268389
theorem B1512275 : Blo 1510952 1512275 := bstep (se 1 (by rfl) ⟨1134206, by rfl⟩ : syracuseStep 1512275 = 2268413) B2268413
theorem B1700707 : Blo 1510952 1700707 := bstep (se 1 (by rfl) ⟨1275530, by rfl⟩ : syracuseStep 1700707 = 2551061) B2551061
theorem B1512291 : Blo 1510952 1512291 := bstep (se 1 (by rfl) ⟨1134218, by rfl⟩ : syracuseStep 1512291 = 2268437) B2268437
theorem B4084589 : Blo 1510952 4084589 := bstep (se 3 (by rfl) ⟨765860, by rfl⟩ : syracuseStep 4084589 = 1531721) B1531721
theorem B1512307 : Blo 1510952 1512307 := bstep (se 1 (by rfl) ⟨1134230, by rfl⟩ : syracuseStep 1512307 = 2268461) B2268461
theorem B1512323 : Blo 1510952 1512323 := bstep (se 1 (by rfl) ⟨1134242, by rfl⟩ : syracuseStep 1512323 = 2268485) B2268485
theorem B1512339 : Blo 1510952 1512339 := bstep (se 1 (by rfl) ⟨1134254, by rfl⟩ : syracuseStep 1512339 = 2268509) B2268509
theorem B1512355 : Blo 1510952 1512355 := bstep (se 1 (by rfl) ⟨1134266, by rfl⟩ : syracuseStep 1512355 = 2268533) B2268533
theorem B5100461 : Blo 1510952 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B1512371 : Blo 1510952 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B2552755 : Blo 1510952 2552755 := bstep (se 1 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 2552755 = 3829133) B3829133
theorem B1512387 : Blo 1510952 1512387 := bstep (se 1 (by rfl) ⟨1134290, by rfl⟩ : syracuseStep 1512387 = 2268581) B2268581
theorem B1512403 : Blo 1510952 1512403 := bstep (se 1 (by rfl) ⟨1134302, by rfl⟩ : syracuseStep 1512403 = 2268605) B2268605
theorem B1840099 : Blo 1510952 1840099 := bstep (se 1 (by rfl) ⟨1380074, by rfl⟩ : syracuseStep 1840099 = 2760149) B2760149
theorem B5100515 : Blo 1510952 5100515 := bstep (se 1 (by rfl) ⟨3825386, by rfl⟩ : syracuseStep 5100515 = 7650773) B7650773
theorem B1512419 : Blo 1510952 1512419 := bstep (se 1 (by rfl) ⟨1134314, by rfl⟩ : syracuseStep 1512419 = 2268629) B2268629
theorem B1700851 : Blo 1510952 1700851 := bstep (se 1 (by rfl) ⟨1275638, by rfl⟩ : syracuseStep 1700851 = 2551277) B2551277
theorem B1512435 : Blo 1510952 1512435 := bstep (se 1 (by rfl) ⟨1134326, by rfl⟩ : syracuseStep 1512435 = 2268653) B2268653
theorem B1512451 : Blo 1510952 1512451 := bstep (se 1 (by rfl) ⟨1134338, by rfl⟩ : syracuseStep 1512451 = 2268677) B2268677
theorem B1512467 : Blo 1510952 1512467 := bstep (se 1 (by rfl) ⟨1134350, by rfl⟩ : syracuseStep 1512467 = 2268701) B2268701
theorem B1512483 : Blo 1510952 1512483 := bstep (se 1 (by rfl) ⟨1134362, by rfl⟩ : syracuseStep 1512483 = 2268725) B2268725
theorem B5739569 : Blo 1510952 5739569 := bstep (se 2 (by rfl) ⟨2152338, by rfl⟩ : syracuseStep 5739569 = 4304677) B4304677
theorem B1512499 : Blo 1510952 1512499 := bstep (se 1 (by rfl) ⟨1134374, by rfl⟩ : syracuseStep 1512499 = 2268749) B2268749
theorem B7468081 : Blo 1510952 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B2552897 : Blo 1510952 2552897 := bstep (se 2 (by rfl) ⟨957336, by rfl⟩ : syracuseStep 2552897 = 1914673) B1914673
theorem B1512515 : Blo 1510952 1512515 := bstep (se 1 (by rfl) ⟨1134386, by rfl⟩ : syracuseStep 1512515 = 2268773) B2268773
theorem B1512531 : Blo 1510952 1512531 := bstep (se 1 (by rfl) ⟨1134398, by rfl⟩ : syracuseStep 1512531 = 2268797) B2268797
theorem B1512547 : Blo 1510952 1512547 := bstep (se 1 (by rfl) ⟨1134410, by rfl⟩ : syracuseStep 1512547 = 2268821) B2268821
theorem B2724977 : Blo 1510952 2724977 := bstep (se 2 (by rfl) ⟨1021866, by rfl⟩ : syracuseStep 2724977 = 2043733) B2043733
theorem B2421875 : Blo 1510952 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B1512563 : Blo 1510952 1512563 := bstep (se 1 (by rfl) ⟨1134422, by rfl⟩ : syracuseStep 1512563 = 2268845) B2268845
theorem B1700995 : Blo 1510952 1700995 := bstep (se 1 (by rfl) ⟨1275746, by rfl⟩ : syracuseStep 1700995 = 2551493) B2551493
theorem B1512579 : Blo 1510952 1512579 := bstep (se 1 (by rfl) ⟨1134434, by rfl⟩ : syracuseStep 1512579 = 2268869) B2268869
theorem B19371149 : Blo 1510952 19371149 := bstep (se 3 (by rfl) ⟨3632090, by rfl⟩ : syracuseStep 19371149 = 7264181) B7264181
theorem B1512595 : Blo 1510952 1512595 := bstep (se 1 (by rfl) ⟨1134446, by rfl⟩ : syracuseStep 1512595 = 2268893) B2268893
theorem B1512611 : Blo 1510952 1512611 := bstep (se 1 (by rfl) ⟨1134458, by rfl⟩ : syracuseStep 1512611 = 2268917) B2268917
theorem B1512627 : Blo 1510952 1512627 := bstep (se 1 (by rfl) ⟨1134470, by rfl⟩ : syracuseStep 1512627 = 2268941) B2268941
theorem B2553025 : Blo 1510952 2553025 := bstep (se 2 (by rfl) ⟨957384, by rfl⟩ : syracuseStep 2553025 = 1914769) B1914769
theorem B1512643 : Blo 1510952 1512643 := bstep (se 1 (by rfl) ⟨1134482, by rfl⟩ : syracuseStep 1512643 = 2268965) B2268965
theorem B4846787 : Blo 1510952 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1512659 : Blo 1510952 1512659 := bstep (se 1 (by rfl) ⟨1134494, by rfl⟩ : syracuseStep 1512659 = 2268989) B2268989
theorem B1512675 : Blo 1510952 1512675 := bstep (se 1 (by rfl) ⟨1134506, by rfl⟩ : syracuseStep 1512675 = 2269013) B2269013
theorem B2553059 : Blo 1510952 2553059 := bstep (se 1 (by rfl) ⟨1914794, by rfl⟩ : syracuseStep 2553059 = 3829589) B3829589
theorem B5100785 : Blo 1510952 5100785 := bstep (se 2 (by rfl) ⟨1912794, by rfl⟩ : syracuseStep 5100785 = 3825589) B3825589
theorem B2454769 : Blo 1510952 2454769 := bstep (se 2 (by rfl) ⟨920538, by rfl⟩ : syracuseStep 2454769 = 1841077) B1841077
theorem B5174513 : Blo 1510952 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B1512691 : Blo 1510952 1512691 := bstep (se 1 (by rfl) ⟨1134518, by rfl⟩ : syracuseStep 1512691 = 2269037) B2269037
theorem B1512707 : Blo 1510952 1512707 := bstep (se 1 (by rfl) ⟨1134530, by rfl⟩ : syracuseStep 1512707 = 2269061) B2269061
theorem B4306193 : Blo 1510952 4306193 := bstep (se 2 (by rfl) ⟨1614822, by rfl⟩ : syracuseStep 4306193 = 3229645) B3229645
theorem B1701139 : Blo 1510952 1701139 := bstep (se 1 (by rfl) ⟨1275854, by rfl⟩ : syracuseStep 1701139 = 2551709) B2551709
theorem B1914131 : Blo 1510952 1914131 := bstep (se 1 (by rfl) ⟨1435598, by rfl⟩ : syracuseStep 1914131 = 2871197) B2871197
theorem B1512723 : Blo 1510952 1512723 := bstep (se 1 (by rfl) ⟨1134542, by rfl⟩ : syracuseStep 1512723 = 2269085) B2269085
theorem B1512739 : Blo 1510952 1512739 := bstep (se 1 (by rfl) ⟨1134554, by rfl⟩ : syracuseStep 1512739 = 2269109) B2269109
theorem B1512755 : Blo 1510952 1512755 := bstep (se 1 (by rfl) ⟨1134566, by rfl⟩ : syracuseStep 1512755 = 2269133) B2269133
theorem B2266433 : Blo 1510952 2266433 := bstep (se 2 (by rfl) ⟨849912, by rfl⟩ : syracuseStep 2266433 = 1699825) B1699825
theorem B1512771 : Blo 1510952 1512771 := bstep (se 1 (by rfl) ⟨1134578, by rfl⟩ : syracuseStep 1512771 = 2269157) B2269157
theorem B2266451 : Blo 1510952 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B2422099 : Blo 1510952 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B1512787 : Blo 1510952 1512787 := bstep (se 1 (by rfl) ⟨1134590, by rfl⟩ : syracuseStep 1512787 = 2269181) B2269181
theorem B2299235 : Blo 1510952 2299235 := bstep (se 1 (by rfl) ⟨1724426, by rfl⟩ : syracuseStep 2299235 = 3448853) B3448853
theorem B1512803 : Blo 1510952 1512803 := bstep (se 1 (by rfl) ⟨1134602, by rfl⟩ : syracuseStep 1512803 = 2269205) B2269205
theorem B2266481 : Blo 1510952 2266481 := bstep (se 2 (by rfl) ⟨849930, by rfl⟩ : syracuseStep 2266481 = 1699861) B1699861
theorem B1512819 : Blo 1510952 1512819 := bstep (se 1 (by rfl) ⟨1134614, by rfl⟩ : syracuseStep 1512819 = 2269229) B2269229
theorem B2266499 : Blo 1510952 2266499 := bstep (se 1 (by rfl) ⟨1699874, by rfl⟩ : syracuseStep 2266499 = 3399749) B3399749
theorem B1512835 : Blo 1510952 1512835 := bstep (se 1 (by rfl) ⟨1134626, by rfl⟩ : syracuseStep 1512835 = 2269253) B2269253
theorem B2422163 : Blo 1510952 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1512851 : Blo 1510952 1512851 := bstep (se 1 (by rfl) ⟨1134638, by rfl⟩ : syracuseStep 1512851 = 2269277) B2269277
theorem B2266529 : Blo 1510952 2266529 := bstep (se 2 (by rfl) ⟨849948, by rfl⟩ : syracuseStep 2266529 = 1699897) B1699897
theorem B1701283 : Blo 1510952 1701283 := bstep (se 1 (by rfl) ⟨1275962, by rfl⟩ : syracuseStep 1701283 = 2551925) B2551925
theorem B1512867 : Blo 1510952 1512867 := bstep (se 1 (by rfl) ⟨1134650, by rfl⟩ : syracuseStep 1512867 = 2269301) B2269301
theorem B5174705 : Blo 1510952 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B2266547 : Blo 1510952 2266547 := bstep (se 1 (by rfl) ⟨1699910, by rfl⟩ : syracuseStep 2266547 = 3399821) B3399821
theorem B1512883 : Blo 1510952 1512883 := bstep (se 1 (by rfl) ⟨1134662, by rfl⟩ : syracuseStep 1512883 = 2269325) B2269325
theorem B1512899 : Blo 1510952 1512899 := bstep (se 1 (by rfl) ⟨1134674, by rfl⟩ : syracuseStep 1512899 = 2269349) B2269349
theorem B6460877 : Blo 1510952 6460877 := bstep (se 3 (by rfl) ⟨1211414, by rfl⟩ : syracuseStep 6460877 = 2422829) B2422829
theorem B2266577 : Blo 1510952 2266577 := bstep (se 2 (by rfl) ⟨849966, by rfl⟩ : syracuseStep 2266577 = 1699933) B1699933
theorem B4306385 : Blo 1510952 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B1512915 : Blo 1510952 1512915 := bstep (se 1 (by rfl) ⟨1134686, by rfl⟩ : syracuseStep 1512915 = 2269373) B2269373
theorem B2266595 : Blo 1510952 2266595 := bstep (se 1 (by rfl) ⟨1699946, by rfl⟩ : syracuseStep 2266595 = 3399893) B3399893
theorem B9688547 : Blo 1510952 9688547 := bstep (se 1 (by rfl) ⟨7266410, by rfl⟩ : syracuseStep 9688547 = 14532821) B14532821
theorem B1512931 : Blo 1510952 1512931 := bstep (se 1 (by rfl) ⟨1134698, by rfl⟩ : syracuseStep 1512931 = 2269397) B2269397
theorem B1512947 : Blo 1510952 1512947 := bstep (se 1 (by rfl) ⟨1134710, by rfl⟩ : syracuseStep 1512947 = 2269421) B2269421
theorem B2266625 : Blo 1510952 2266625 := bstep (se 2 (by rfl) ⟨849984, by rfl⟩ : syracuseStep 2266625 = 1699969) B1699969
theorem B2266643 : Blo 1510952 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B2422291 : Blo 1510952 2422291 := bstep (se 1 (by rfl) ⟨1816718, by rfl⟩ : syracuseStep 2422291 = 3633437) B3633437
theorem B2266673 : Blo 1510952 2266673 := bstep (se 2 (by rfl) ⟨850002, by rfl⟩ : syracuseStep 2266673 = 1700005) B1700005
theorem B1701427 : Blo 1510952 1701427 := bstep (se 1 (by rfl) ⟨1276070, by rfl⟩ : syracuseStep 1701427 = 2552141) B2552141
theorem B2266691 : Blo 1510952 2266691 := bstep (se 1 (by rfl) ⟨1700018, by rfl⟩ : syracuseStep 2266691 = 3400037) B3400037
theorem B2152003 : Blo 1510952 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B2266721 : Blo 1510952 2266721 := bstep (se 2 (by rfl) ⟨850020, by rfl⟩ : syracuseStep 2266721 = 1700041) B1700041
theorem B2266739 : Blo 1510952 2266739 := bstep (se 1 (by rfl) ⟨1700054, by rfl⟩ : syracuseStep 2266739 = 3400109) B3400109
theorem B2266769 : Blo 1510952 2266769 := bstep (se 2 (by rfl) ⟨850038, by rfl⟩ : syracuseStep 2266769 = 1700077) B1700077
theorem B2586259 : Blo 1510952 2586259 := bstep (se 1 (by rfl) ⟨1939694, by rfl⟩ : syracuseStep 2586259 = 3879389) B3879389
theorem B2266787 : Blo 1510952 2266787 := bstep (se 1 (by rfl) ⟨1700090, by rfl⟩ : syracuseStep 2266787 = 3400181) B3400181
theorem B2152099 : Blo 1510952 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B2266817 : Blo 1510952 2266817 := bstep (se 2 (by rfl) ⟨850056, by rfl⟩ : syracuseStep 2266817 = 1700113) B1700113
theorem B1701571 : Blo 1510952 1701571 := bstep (se 1 (by rfl) ⟨1276178, by rfl⟩ : syracuseStep 1701571 = 2552357) B2552357
theorem B3634897 : Blo 1510952 3634897 := bstep (se 2 (by rfl) ⟨1363086, by rfl⟩ : syracuseStep 3634897 = 2726173) B2726173
theorem B2266835 : Blo 1510952 2266835 := bstep (se 1 (by rfl) ⟨1700126, by rfl⟩ : syracuseStep 2266835 = 3400253) B3400253
theorem B2266865 : Blo 1510952 2266865 := bstep (se 2 (by rfl) ⟨850074, by rfl⟩ : syracuseStep 2266865 = 1700149) B1700149
theorem B4978417 : Blo 1510952 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B2266883 : Blo 1510952 2266883 := bstep (se 1 (by rfl) ⟨1700162, by rfl⟩ : syracuseStep 2266883 = 3400325) B3400325
theorem B5101325 : Blo 1510952 5101325 := bstep (se 3 (by rfl) ⟨956498, by rfl⟩ : syracuseStep 5101325 = 1912997) B1912997
theorem B2266913 : Blo 1510952 2266913 := bstep (se 2 (by rfl) ⟨850092, by rfl⟩ : syracuseStep 2266913 = 1700185) B1700185
theorem B2266931 : Blo 1510952 2266931 := bstep (se 1 (by rfl) ⟨1700198, by rfl⟩ : syracuseStep 2266931 = 3400397) B3400397
theorem B2299699 : Blo 1510952 2299699 := bstep (se 1 (by rfl) ⟨1724774, by rfl⟩ : syracuseStep 2299699 = 3449549) B3449549
theorem B5101379 : Blo 1510952 5101379 := bstep (se 1 (by rfl) ⟨3826034, by rfl⟩ : syracuseStep 5101379 = 7652069) B7652069
theorem B2266961 : Blo 1510952 2266961 := bstep (se 2 (by rfl) ⟨850110, by rfl⟩ : syracuseStep 2266961 = 1700221) B1700221
theorem B4085585 : Blo 1510952 4085585 := bstep (se 2 (by rfl) ⟨1532094, by rfl⟩ : syracuseStep 4085585 = 3064189) B3064189
theorem B1701715 : Blo 1510952 1701715 := bstep (se 1 (by rfl) ⟨1276286, by rfl⟩ : syracuseStep 1701715 = 2552573) B2552573
theorem B2266979 : Blo 1510952 2266979 := bstep (se 1 (by rfl) ⟨1700234, by rfl⟩ : syracuseStep 2266979 = 3400469) B3400469
theorem B2267009 : Blo 1510952 2267009 := bstep (se 2 (by rfl) ⟨850128, by rfl⟩ : syracuseStep 2267009 = 1700257) B1700257
theorem B2267027 : Blo 1510952 2267027 := bstep (se 1 (by rfl) ⟨1700270, by rfl⟩ : syracuseStep 2267027 = 3400541) B3400541
theorem B9951139 : Blo 1510952 9951139 := bstep (se 1 (by rfl) ⟨7463354, by rfl⟩ : syracuseStep 9951139 = 14926709) B14926709
theorem B2267057 : Blo 1510952 2267057 := bstep (se 2 (by rfl) ⟨850146, by rfl⟩ : syracuseStep 2267057 = 1700293) B1700293
theorem B2267075 : Blo 1510952 2267075 := bstep (se 1 (by rfl) ⟨1700306, by rfl⟩ : syracuseStep 2267075 = 3400613) B3400613
theorem B2267105 : Blo 1510952 2267105 := bstep (se 2 (by rfl) ⟨850164, by rfl⟩ : syracuseStep 2267105 = 1700329) B1700329
theorem B1701859 : Blo 1510952 1701859 := bstep (se 1 (by rfl) ⟨1276394, by rfl⟩ : syracuseStep 1701859 = 2552789) B2552789
theorem B17217521 : Blo 1510952 17217521 := bstep (se 2 (by rfl) ⟨6456570, by rfl⟩ : syracuseStep 17217521 = 12913141) B12913141
theorem B2267123 : Blo 1510952 2267123 := bstep (se 1 (by rfl) ⟨1700342, by rfl⟩ : syracuseStep 2267123 = 3400685) B3400685
theorem B2267153 : Blo 1510952 2267153 := bstep (se 2 (by rfl) ⟨850182, by rfl⟩ : syracuseStep 2267153 = 1700365) B1700365
theorem B7649315 : Blo 1510952 7649315 := bstep (se 1 (by rfl) ⟨5736986, by rfl⟩ : syracuseStep 7649315 = 11473973) B11473973
theorem B2267171 : Blo 1510952 2267171 := bstep (se 1 (by rfl) ⟨1700378, by rfl⟩ : syracuseStep 2267171 = 3400757) B3400757
theorem B6633521 : Blo 1510952 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B2267201 : Blo 1510952 2267201 := bstep (se 2 (by rfl) ⟨850200, by rfl⟩ : syracuseStep 2267201 = 1700401) B1700401
theorem B5101649 : Blo 1510952 5101649 := bstep (se 2 (by rfl) ⟨1913118, by rfl⟩ : syracuseStep 5101649 = 3826237) B3826237
theorem B2267219 : Blo 1510952 2267219 := bstep (se 1 (by rfl) ⟨1700414, by rfl⟩ : syracuseStep 2267219 = 3400829) B3400829
theorem B2267249 : Blo 1510952 2267249 := bstep (se 2 (by rfl) ⟨850218, by rfl⟩ : syracuseStep 2267249 = 1700437) B1700437
theorem B1702003 : Blo 1510952 1702003 := bstep (se 1 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 1702003 = 2553005) B2553005
theorem B2267267 : Blo 1510952 2267267 := bstep (se 1 (by rfl) ⟨1700450, by rfl⟩ : syracuseStep 2267267 = 3400901) B3400901
theorem B2152595 : Blo 1510952 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B2267297 : Blo 1510952 2267297 := bstep (se 2 (by rfl) ⟨850236, by rfl⟩ : syracuseStep 2267297 = 1700473) B1700473
theorem B2267315 : Blo 1510952 2267315 := bstep (se 1 (by rfl) ⟨1700486, by rfl⟩ : syracuseStep 2267315 = 3400973) B3400973
theorem B8607941 : Blo 1510952 8607941 := bstep (se 4 (by rfl) ⟨806994, by rfl⟩ : syracuseStep 8607941 = 1613989) B1613989
theorem B2267345 : Blo 1510952 2267345 := bstep (se 2 (by rfl) ⟨850254, by rfl⟩ : syracuseStep 2267345 = 1700509) B1700509
theorem B2423009 : Blo 1510952 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2267363 : Blo 1510952 2267363 := bstep (se 1 (by rfl) ⟨1700522, by rfl⟩ : syracuseStep 2267363 = 3401045) B3401045
theorem B24533219 : Blo 1510952 24533219 := bstep (se 1 (by rfl) ⟨18399914, by rfl⟩ : syracuseStep 24533219 = 36799829) B36799829
theorem B2267393 : Blo 1510952 2267393 := bstep (se 2 (by rfl) ⟨850272, by rfl⟩ : syracuseStep 2267393 = 1700545) B1700545
theorem B2267411 : Blo 1510952 2267411 := bstep (se 1 (by rfl) ⟨1700558, by rfl⟩ : syracuseStep 2267411 = 3401117) B3401117
theorem B2267441 : Blo 1510952 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B2267459 : Blo 1510952 2267459 := bstep (se 1 (by rfl) ⟨1700594, by rfl⟩ : syracuseStep 2267459 = 3401189) B3401189
theorem B2267489 : Blo 1510952 2267489 := bstep (se 2 (by rfl) ⟨850308, by rfl⟩ : syracuseStep 2267489 = 1700617) B1700617
theorem B2423137 : Blo 1510952 2423137 := bstep (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) B1817353
theorem B2300257 : Blo 1510952 2300257 := bstep (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) B1725193
theorem B7756145 : Blo 1510952 7756145 := bstep (se 2 (by rfl) ⟨2908554, by rfl⟩ : syracuseStep 7756145 = 5817109) B5817109
theorem B2267507 : Blo 1510952 2267507 := bstep (se 1 (by rfl) ⟨1700630, by rfl⟩ : syracuseStep 2267507 = 3401261) B3401261
theorem B2267537 : Blo 1510952 2267537 := bstep (se 2 (by rfl) ⟨850326, by rfl⟩ : syracuseStep 2267537 = 1700653) B1700653
theorem B2267555 : Blo 1510952 2267555 := bstep (se 1 (by rfl) ⟨1700666, by rfl⟩ : syracuseStep 2267555 = 3401333) B3401333
theorem B4307377 : Blo 1510952 4307377 := bstep (se 2 (by rfl) ⟨1615266, by rfl⟩ : syracuseStep 4307377 = 3230533) B3230533
theorem B2267585 : Blo 1510952 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B2267603 : Blo 1510952 2267603 := bstep (se 1 (by rfl) ⟨1700702, by rfl⟩ : syracuseStep 2267603 = 3401405) B3401405
theorem B5741027 : Blo 1510952 5741027 := bstep (se 1 (by rfl) ⟨4305770, by rfl⟩ : syracuseStep 5741027 = 8611541) B8611541
theorem B12909041 : Blo 1510952 12909041 := bstep (se 2 (by rfl) ⟨4840890, by rfl⟩ : syracuseStep 12909041 = 9681781) B9681781
theorem B2267633 : Blo 1510952 2267633 := bstep (se 2 (by rfl) ⟨850362, by rfl⟩ : syracuseStep 2267633 = 1700725) B1700725
theorem B2267651 : Blo 1510952 2267651 := bstep (se 1 (by rfl) ⟨1700738, by rfl⟩ : syracuseStep 2267651 = 3401477) B3401477
theorem B2267681 : Blo 1510952 2267681 := bstep (se 2 (by rfl) ⟨850380, by rfl⟩ : syracuseStep 2267681 = 1700761) B1700761
theorem B2267699 : Blo 1510952 2267699 := bstep (se 1 (by rfl) ⟨1700774, by rfl⟩ : syracuseStep 2267699 = 3401549) B3401549
theorem B2267729 : Blo 1510952 2267729 := bstep (se 2 (by rfl) ⟨850398, by rfl⟩ : syracuseStep 2267729 = 1700797) B1700797
theorem B2267747 : Blo 1510952 2267747 := bstep (se 1 (by rfl) ⟨1700810, by rfl⟩ : syracuseStep 2267747 = 3401621) B3401621
theorem B5102189 : Blo 1510952 5102189 := bstep (se 3 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 5102189 = 1913321) B1913321
theorem B2267777 : Blo 1510952 2267777 := bstep (se 2 (by rfl) ⟨850416, by rfl⟩ : syracuseStep 2267777 = 1700833) B1700833
theorem B2267795 : Blo 1510952 2267795 := bstep (se 1 (by rfl) ⟨1700846, by rfl⟩ : syracuseStep 2267795 = 3401693) B3401693
theorem B2587297 : Blo 1510952 2587297 := bstep (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) B1940473
theorem B5102243 : Blo 1510952 5102243 := bstep (se 1 (by rfl) ⟨3826682, by rfl⟩ : syracuseStep 5102243 = 7653365) B7653365
theorem B2267825 : Blo 1510952 2267825 := bstep (se 2 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 2267825 = 1700869) B1700869
theorem B9689777 : Blo 1510952 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B2267843 : Blo 1510952 2267843 := bstep (se 1 (by rfl) ⟨1700882, by rfl⟩ : syracuseStep 2267843 = 3401765) B3401765
theorem B4307651 : Blo 1510952 4307651 := bstep (se 1 (by rfl) ⟨3230738, by rfl⟩ : syracuseStep 4307651 = 6461477) B6461477
theorem B2267873 : Blo 1510952 2267873 := bstep (se 2 (by rfl) ⟨850452, by rfl⟩ : syracuseStep 2267873 = 1700905) B1700905
theorem B7658225 : Blo 1510952 7658225 := bstep (se 2 (by rfl) ⟨2871834, by rfl⟩ : syracuseStep 7658225 = 5743669) B5743669
theorem B8616689 : Blo 1510952 8616689 := bstep (se 2 (by rfl) ⟨3231258, by rfl⟩ : syracuseStep 8616689 = 6462517) B6462517
theorem B2267891 : Blo 1510952 2267891 := bstep (se 1 (by rfl) ⟨1700918, by rfl⟩ : syracuseStep 2267891 = 3401837) B3401837
theorem B2267921 : Blo 1510952 2267921 := bstep (se 2 (by rfl) ⟨850470, by rfl⟩ : syracuseStep 2267921 = 1700941) B1700941
theorem B2153233 : Blo 1510952 2153233 := bstep (se 2 (by rfl) ⟨807462, by rfl⟩ : syracuseStep 2153233 = 1614925) B1614925
theorem B2267939 : Blo 1510952 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B2267969 : Blo 1510952 2267969 := bstep (se 2 (by rfl) ⟨850488, by rfl⟩ : syracuseStep 2267969 = 1700977) B1700977
theorem B7650125 : Blo 1510952 7650125 := bstep (se 3 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 7650125 = 2868797) B2868797
theorem B2267987 : Blo 1510952 2267987 := bstep (se 1 (by rfl) ⟨1700990, by rfl⟩ : syracuseStep 2267987 = 3401981) B3401981
theorem B8608625 : Blo 1510952 8608625 := bstep (se 2 (by rfl) ⟨3228234, by rfl⟩ : syracuseStep 8608625 = 6456469) B6456469
theorem B2268017 : Blo 1510952 2268017 := bstep (se 2 (by rfl) ⟨850506, by rfl⟩ : syracuseStep 2268017 = 1701013) B1701013
theorem B2268035 : Blo 1510952 2268035 := bstep (se 1 (by rfl) ⟨1701026, by rfl⟩ : syracuseStep 2268035 = 3402053) B3402053
theorem B4307843 : Blo 1510952 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B2268065 : Blo 1510952 2268065 := bstep (se 2 (by rfl) ⟨850524, by rfl⟩ : syracuseStep 2268065 = 1701049) B1701049
theorem B5102513 : Blo 1510952 5102513 := bstep (se 2 (by rfl) ⟨1913442, by rfl⟩ : syracuseStep 5102513 = 3826885) B3826885
theorem B2268083 : Blo 1510952 2268083 := bstep (se 1 (by rfl) ⟨1701062, by rfl⟩ : syracuseStep 2268083 = 3402125) B3402125
theorem B13794245 : Blo 1510952 13794245 := bstep (se 4 (by rfl) ⟨1293210, by rfl⟩ : syracuseStep 13794245 = 2586421) B2586421
theorem B2268113 : Blo 1510952 2268113 := bstep (se 2 (by rfl) ⟨850542, by rfl⟩ : syracuseStep 2268113 = 1701085) B1701085
theorem B2268131 : Blo 1510952 2268131 := bstep (se 1 (by rfl) ⟨1701098, by rfl⟩ : syracuseStep 2268131 = 3402197) B3402197
theorem B6462449 : Blo 1510952 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B2268161 : Blo 1510952 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B2268179 : Blo 1510952 2268179 := bstep (se 1 (by rfl) ⟨1701134, by rfl⟩ : syracuseStep 2268179 = 3402269) B3402269
theorem B2268209 : Blo 1510952 2268209 := bstep (se 2 (by rfl) ⟨850578, by rfl⟩ : syracuseStep 2268209 = 1701157) B1701157
theorem B2268227 : Blo 1510952 2268227 := bstep (se 1 (by rfl) ⟨1701170, by rfl⟩ : syracuseStep 2268227 = 3402341) B3402341
theorem B2268257 : Blo 1510952 2268257 := bstep (se 2 (by rfl) ⟨850596, by rfl⟩ : syracuseStep 2268257 = 1701193) B1701193
theorem B2153569 : Blo 1510952 2153569 := bstep (se 2 (by rfl) ⟨807588, by rfl⟩ : syracuseStep 2153569 = 1615177) B1615177
theorem B2268275 : Blo 1510952 2268275 := bstep (se 1 (by rfl) ⟨1701206, by rfl⟩ : syracuseStep 2268275 = 3402413) B3402413
theorem B2268305 : Blo 1510952 2268305 := bstep (se 2 (by rfl) ⟨850614, by rfl⟩ : syracuseStep 2268305 = 1701229) B1701229
theorem B2268323 : Blo 1510952 2268323 := bstep (se 1 (by rfl) ⟨1701242, by rfl⟩ : syracuseStep 2268323 = 3402485) B3402485
theorem B2268353 : Blo 1510952 2268353 := bstep (se 2 (by rfl) ⟨850632, by rfl⟩ : syracuseStep 2268353 = 1701265) B1701265
theorem B3316945 : Blo 1510952 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B2268371 : Blo 1510952 2268371 := bstep (se 1 (by rfl) ⟨1701278, by rfl⟩ : syracuseStep 2268371 = 3402557) B3402557
theorem B2268401 : Blo 1510952 2268401 := bstep (se 2 (by rfl) ⟨850650, by rfl⟩ : syracuseStep 2268401 = 1701301) B1701301
theorem B2268419 : Blo 1510952 2268419 := bstep (se 1 (by rfl) ⟨1701314, by rfl⟩ : syracuseStep 2268419 = 3402629) B3402629
theorem B2268449 : Blo 1510952 2268449 := bstep (se 2 (by rfl) ⟨850668, by rfl⟩ : syracuseStep 2268449 = 1701337) B1701337
theorem B2268467 : Blo 1510952 2268467 := bstep (se 1 (by rfl) ⟨1701350, by rfl⟩ : syracuseStep 2268467 = 3402701) B3402701
theorem B2268497 : Blo 1510952 2268497 := bstep (se 2 (by rfl) ⟨850686, by rfl⟩ : syracuseStep 2268497 = 1701373) B1701373
theorem B2268515 : Blo 1510952 2268515 := bstep (se 1 (by rfl) ⟨1701386, by rfl⟩ : syracuseStep 2268515 = 3402773) B3402773
theorem B2268545 : Blo 1510952 2268545 := bstep (se 2 (by rfl) ⟨850704, by rfl⟩ : syracuseStep 2268545 = 1701409) B1701409
theorem B2268563 : Blo 1510952 2268563 := bstep (se 1 (by rfl) ⟨1701422, by rfl⟩ : syracuseStep 2268563 = 3402845) B3402845
theorem B2268593 : Blo 1510952 2268593 := bstep (se 2 (by rfl) ⟨850722, by rfl⟩ : syracuseStep 2268593 = 1701445) B1701445
theorem B2268611 : Blo 1510952 2268611 := bstep (se 1 (by rfl) ⟨1701458, by rfl⟩ : syracuseStep 2268611 = 3402917) B3402917
theorem B5103053 : Blo 1510952 5103053 := bstep (se 3 (by rfl) ⟨956822, by rfl⟩ : syracuseStep 5103053 = 1913645) B1913645
theorem B5742029 : Blo 1510952 5742029 := bstep (se 3 (by rfl) ⟨1076630, by rfl⟩ : syracuseStep 5742029 = 2153261) B2153261
theorem B2268641 : Blo 1510952 2268641 := bstep (se 2 (by rfl) ⟨850740, by rfl⟩ : syracuseStep 2268641 = 1701481) B1701481
theorem B2268659 : Blo 1510952 2268659 := bstep (se 1 (by rfl) ⟨1701494, by rfl⟩ : syracuseStep 2268659 = 3402989) B3402989
theorem B5103107 : Blo 1510952 5103107 := bstep (se 1 (by rfl) ⟨3827330, by rfl⟩ : syracuseStep 5103107 = 7654661) B7654661
theorem B2268689 : Blo 1510952 2268689 := bstep (se 2 (by rfl) ⟨850758, by rfl⟩ : syracuseStep 2268689 = 1701517) B1701517
theorem B2268707 : Blo 1510952 2268707 := bstep (se 1 (by rfl) ⟨1701530, by rfl⟩ : syracuseStep 2268707 = 3403061) B3403061
theorem B2268737 : Blo 1510952 2268737 := bstep (se 2 (by rfl) ⟨850776, by rfl⟩ : syracuseStep 2268737 = 1701553) B1701553
theorem B2268755 : Blo 1510952 2268755 := bstep (se 1 (by rfl) ⟨1701566, by rfl⟩ : syracuseStep 2268755 = 3403133) B3403133
theorem B3063395 : Blo 1510952 3063395 := bstep (se 1 (by rfl) ⟨2297546, by rfl⟩ : syracuseStep 3063395 = 4595093) B4595093
theorem B4595309 : Blo 1510952 4595309 := bstep (se 3 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 4595309 = 1723241) B1723241
theorem B3825265 : Blo 1510952 3825265 := bstep (se 2 (by rfl) ⟨1434474, by rfl⟩ : syracuseStep 3825265 = 2868949) B2868949
theorem B2268785 : Blo 1510952 2268785 := bstep (se 2 (by rfl) ⟨850794, by rfl⟩ : syracuseStep 2268785 = 1701589) B1701589
theorem B2268803 : Blo 1510952 2268803 := bstep (se 1 (by rfl) ⟨1701602, by rfl⟩ : syracuseStep 2268803 = 3403205) B3403205
theorem B7265933 : Blo 1510952 7265933 := bstep (se 3 (by rfl) ⟨1362362, by rfl⟩ : syracuseStep 7265933 = 2724725) B2724725
theorem B2268833 : Blo 1510952 2268833 := bstep (se 2 (by rfl) ⟨850812, by rfl⟩ : syracuseStep 2268833 = 1701625) B1701625
theorem B2154161 : Blo 1510952 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B2268851 : Blo 1510952 2268851 := bstep (se 1 (by rfl) ⟨1701638, by rfl⟩ : syracuseStep 2268851 = 3403277) B3403277
theorem B2268881 : Blo 1510952 2268881 := bstep (se 2 (by rfl) ⟨850830, by rfl⟩ : syracuseStep 2268881 = 1701661) B1701661
theorem B2268899 : Blo 1510952 2268899 := bstep (se 1 (by rfl) ⟨1701674, by rfl⟩ : syracuseStep 2268899 = 3403349) B3403349
theorem B2268929 : Blo 1510952 2268929 := bstep (se 2 (by rfl) ⟨850848, by rfl⟩ : syracuseStep 2268929 = 1701697) B1701697
theorem B5103377 : Blo 1510952 5103377 := bstep (se 2 (by rfl) ⟨1913766, by rfl⟩ : syracuseStep 5103377 = 3827533) B3827533
theorem B2268947 : Blo 1510952 2268947 := bstep (se 1 (by rfl) ⟨1701710, by rfl⟩ : syracuseStep 2268947 = 3403421) B3403421
theorem B2268977 : Blo 1510952 2268977 := bstep (se 2 (by rfl) ⟨850866, by rfl⟩ : syracuseStep 2268977 = 1701733) B1701733
theorem B2268995 : Blo 1510952 2268995 := bstep (se 1 (by rfl) ⟨1701746, by rfl⟩ : syracuseStep 2268995 = 3403493) B3403493
theorem B2269025 : Blo 1510952 2269025 := bstep (se 2 (by rfl) ⟨850884, by rfl⟩ : syracuseStep 2269025 = 1701769) B1701769
theorem B2269043 : Blo 1510952 2269043 := bstep (se 1 (by rfl) ⟨1701782, by rfl⟩ : syracuseStep 2269043 = 3403565) B3403565
theorem B3825539 : Blo 1510952 3825539 := bstep (se 1 (by rfl) ⟨2869154, by rfl⟩ : syracuseStep 3825539 = 5738309) B5738309
theorem B2269073 : Blo 1510952 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B2269091 : Blo 1510952 2269091 := bstep (se 1 (by rfl) ⟨1701818, by rfl⟩ : syracuseStep 2269091 = 3403637) B3403637
theorem B2269121 : Blo 1510952 2269121 := bstep (se 2 (by rfl) ⟨850920, by rfl⟩ : syracuseStep 2269121 = 1701841) B1701841
theorem B2269139 : Blo 1510952 2269139 := bstep (se 1 (by rfl) ⟨1701854, by rfl⟩ : syracuseStep 2269139 = 3403709) B3403709
theorem B6897635 : Blo 1510952 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B2269169 : Blo 1510952 2269169 := bstep (se 2 (by rfl) ⟨850938, by rfl⟩ : syracuseStep 2269169 = 1701877) B1701877
theorem B4841495 : Blo 1510952 4841495 := bstep (se 1 (by rfl) ⟨3631121, by rfl⟩ : syracuseStep 4841495 = 7262243) B7262243
theorem B3399731 : Blo 1510952 3399731 := bstep (se 1 (by rfl) ⟨2549798, by rfl⟩ : syracuseStep 3399731 = 5099597) B5099597
theorem B2269259 : Blo 1510952 2269259 := bstep (se 1 (by rfl) ⟨1701944, by rfl⟩ : syracuseStep 2269259 = 3403889) B3403889
theorem B3399767 : Blo 1510952 3399767 := bstep (se 1 (by rfl) ⟨2549825, by rfl⟩ : syracuseStep 3399767 = 5099651) B5099651
theorem B3448919 : Blo 1510952 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B2269271 : Blo 1510952 2269271 := bstep (se 1 (by rfl) ⟨1701953, by rfl⟩ : syracuseStep 2269271 = 3403907) B3403907
theorem B7651421 : Blo 1510952 7651421 := bstep (se 3 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 7651421 = 2869283) B2869283
theorem B2269337 : Blo 1510952 2269337 := bstep (se 2 (by rfl) ⟨851001, by rfl⟩ : syracuseStep 2269337 = 1702003) B1702003
theorem B5103809 : Blo 1510952 5103809 := bstep (se 2 (by rfl) ⟨1913928, by rfl⟩ : syracuseStep 5103809 = 3827857) B3827857
theorem B25845965 : Blo 1510952 25845965 := bstep (se 3 (by rfl) ⟨4846118, by rfl⟩ : syracuseStep 25845965 = 9692237) B9692237
theorem B1532119 : Blo 1510952 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B39829765 : Blo 1510952 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B3399947 : Blo 1510952 3399947 := bstep (se 1 (by rfl) ⟨2549960, by rfl⟩ : syracuseStep 3399947 = 5099921) B5099921
theorem B3400001 : Blo 1510952 3400001 := bstep (se 2 (by rfl) ⟨1275000, by rfl⟩ : syracuseStep 3400001 = 2550001) B2550001
theorem B3400217 : Blo 1510952 3400217 := bstep (se 2 (by rfl) ⟨1275081, by rfl⟩ : syracuseStep 3400217 = 2550163) B2550163
theorem B6128179 : Blo 1510952 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B5743169 : Blo 1510952 5743169 := bstep (se 2 (by rfl) ⟨2153688, by rfl⟩ : syracuseStep 5743169 = 4307377) B4307377
theorem B65421917 : Blo 1510952 65421917 := bstep (se 3 (by rfl) ⟨12266609, by rfl⟩ : syracuseStep 65421917 = 24533219) B24533219
theorem B3400307 : Blo 1510952 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B3400343 : Blo 1510952 3400343 := bstep (se 1 (by rfl) ⟨2550257, by rfl⟩ : syracuseStep 3400343 = 5100515) B5100515
theorem B3826379 : Blo 1510952 3826379 := bstep (se 1 (by rfl) ⟨2869784, by rfl⟩ : syracuseStep 3826379 = 5739569) B5739569
theorem B5104349 : Blo 1510952 5104349 := bstep (se 3 (by rfl) ⟨957065, by rfl⟩ : syracuseStep 5104349 = 1914131) B1914131
theorem B1614583 : Blo 1510952 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B3400523 : Blo 1510952 3400523 := bstep (se 1 (by rfl) ⟨2550392, by rfl⟩ : syracuseStep 3400523 = 5100785) B5100785
theorem B3228491 : Blo 1510952 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B3449675 : Blo 1510952 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B11477861 : Blo 1510952 11477861 := bstep (se 4 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 11477861 = 2152099) B2152099
theorem B3400577 : Blo 1510952 3400577 := bstep (se 2 (by rfl) ⟨1275216, by rfl⟩ : syracuseStep 3400577 = 2550433) B2550433
theorem B3449729 : Blo 1510952 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B3449803 : Blo 1510952 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B3400793 : Blo 1510952 3400793 := bstep (se 2 (by rfl) ⟨1275297, by rfl⟩ : syracuseStep 3400793 = 2550595) B2550595
theorem B3400883 : Blo 1510952 3400883 := bstep (se 1 (by rfl) ⟨2550662, by rfl⟩ : syracuseStep 3400883 = 5101325) B5101325
theorem B3400919 : Blo 1510952 3400919 := bstep (se 1 (by rfl) ⟨2550689, by rfl⟩ : syracuseStep 3400919 = 5101379) B5101379
theorem B13092101 : Blo 1510952 13092101 := bstep (se 4 (by rfl) ⟨1227384, by rfl⟩ : syracuseStep 13092101 = 2454769) B2454769
theorem B11478347 : Blo 1510952 11478347 := bstep (se 1 (by rfl) ⟨8608760, by rfl⟩ : syracuseStep 11478347 = 17217521) B17217521
theorem B3401099 : Blo 1510952 3401099 := bstep (se 1 (by rfl) ⟨2550824, by rfl⟩ : syracuseStep 3401099 = 5101649) B5101649
theorem B3401153 : Blo 1510952 3401153 := bstep (se 2 (by rfl) ⟨1275432, by rfl⟩ : syracuseStep 3401153 = 2550865) B2550865
theorem B1615339 : Blo 1510952 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B5170763 : Blo 1510952 5170763 := bstep (se 1 (by rfl) ⟨3878072, by rfl⟩ : syracuseStep 5170763 = 7756145) B7756145
theorem B13092445 : Blo 1510952 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B2868851 : Blo 1510952 2868851 := bstep (se 1 (by rfl) ⟨2151638, by rfl⟩ : syracuseStep 2868851 = 4303277) B4303277
theorem B3827351 : Blo 1510952 3827351 := bstep (se 1 (by rfl) ⟨2870513, by rfl⟩ : syracuseStep 3827351 = 5741027) B5741027
theorem B3401369 : Blo 1510952 3401369 := bstep (se 2 (by rfl) ⟨1275513, by rfl⟩ : syracuseStep 3401369 = 2551027) B2551027
theorem B3401459 : Blo 1510952 3401459 := bstep (se 1 (by rfl) ⟨2551094, by rfl⟩ : syracuseStep 3401459 = 5102189) B5102189
theorem B3401495 : Blo 1510952 3401495 := bstep (se 1 (by rfl) ⟨2551121, by rfl⟩ : syracuseStep 3401495 = 5102243) B5102243
theorem B3229465 : Blo 1510952 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B5744429 : Blo 1510952 5744429 := bstep (se 3 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 5744429 = 2154161) B2154161
theorem B5105483 : Blo 1510952 5105483 := bstep (se 1 (by rfl) ⟨3829112, by rfl⟩ : syracuseStep 5105483 = 7658225) B7658225
theorem B5744459 : Blo 1510952 5744459 := bstep (se 1 (by rfl) ⟨4308344, by rfl⟩ : syracuseStep 5744459 = 8616689) B8616689
theorem B3401675 : Blo 1510952 3401675 := bstep (se 1 (by rfl) ⟨2551256, by rfl⟩ : syracuseStep 3401675 = 5102513) B5102513
theorem B5449693 : Blo 1510952 5449693 := bstep (se 3 (by rfl) ⟨1021817, by rfl⟩ : syracuseStep 5449693 = 2043635) B2043635
theorem B3401729 : Blo 1510952 3401729 := bstep (se 2 (by rfl) ⟨1275648, by rfl⟩ : syracuseStep 3401729 = 2551297) B2551297
theorem B2549785 : Blo 1510952 2549785 := bstep (se 2 (by rfl) ⟨956169, by rfl⟩ : syracuseStep 2549785 = 1912339) B1912339
theorem B3229721 : Blo 1510952 3229721 := bstep (se 2 (by rfl) ⟨1211145, by rfl⟩ : syracuseStep 3229721 = 2422291) B2422291
theorem B3631169 : Blo 1510952 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B2869337 : Blo 1510952 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B5105753 : Blo 1510952 5105753 := bstep (se 2 (by rfl) ⟨1914657, by rfl⟩ : syracuseStep 5105753 = 3829315) B3829315
theorem B7653527 : Blo 1510952 7653527 := bstep (se 1 (by rfl) ⟨5740145, by rfl⟩ : syracuseStep 7653527 = 11480291) B11480291
theorem B3401945 : Blo 1510952 3401945 := bstep (se 2 (by rfl) ⟨1275729, by rfl⟩ : syracuseStep 3401945 = 2551459) B2551459
theorem B3402035 : Blo 1510952 3402035 := bstep (se 1 (by rfl) ⟨2551526, by rfl⟩ : syracuseStep 3402035 = 5103053) B5103053
theorem B3828019 : Blo 1510952 3828019 := bstep (se 1 (by rfl) ⟨2871014, by rfl⟩ : syracuseStep 3828019 = 5742029) B5742029
theorem B6637889 : Blo 1510952 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B3402071 : Blo 1510952 3402071 := bstep (se 1 (by rfl) ⟨2551553, by rfl⟩ : syracuseStep 3402071 = 5103107) B5103107
theorem B11487581 : Blo 1510952 11487581 := bstep (se 3 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 11487581 = 4307843) B4307843
theorem B2042263 : Blo 1510952 2042263 := bstep (se 1 (by rfl) ⟨1531697, by rfl⟩ : syracuseStep 2042263 = 3063395) B3063395
theorem B3066265 : Blo 1510952 3066265 := bstep (se 2 (by rfl) ⟨1149849, by rfl⟩ : syracuseStep 3066265 = 2299699) B2299699
theorem B4843955 : Blo 1510952 4843955 := bstep (se 1 (by rfl) ⟨3632966, by rfl⟩ : syracuseStep 4843955 = 7265933) B7265933
theorem B3230131 : Blo 1510952 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B3828161 : Blo 1510952 3828161 := bstep (se 2 (by rfl) ⟨1435560, by rfl⟩ : syracuseStep 3828161 = 2871121) B2871121
theorem B3402251 : Blo 1510952 3402251 := bstep (se 1 (by rfl) ⟨2551688, by rfl⟩ : syracuseStep 3402251 = 5103377) B5103377
theorem B11635265 : Blo 1510952 11635265 := bstep (se 2 (by rfl) ⟨4363224, by rfl⟩ : syracuseStep 11635265 = 8726449) B8726449
theorem B5171777 : Blo 1510952 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B3402305 : Blo 1510952 3402305 := bstep (se 2 (by rfl) ⟨1275864, by rfl⟩ : syracuseStep 3402305 = 2551729) B2551729
theorem B2550359 : Blo 1510952 2550359 := bstep (se 1 (by rfl) ⟨1912769, by rfl⟩ : syracuseStep 2550359 = 3825539) B3825539
theorem B9685655 : Blo 1510952 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B4598423 : Blo 1510952 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B5737139 : Blo 1510952 5737139 := bstep (se 1 (by rfl) ⟨4302854, by rfl⟩ : syracuseStep 5737139 = 8605709) B8605709
theorem B2550487 : Blo 1510952 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B12258053 : Blo 1510952 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B3402521 : Blo 1510952 3402521 := bstep (se 2 (by rfl) ⟨1275945, by rfl⟩ : syracuseStep 3402521 = 2551891) B2551891
theorem B3402611 : Blo 1510952 3402611 := bstep (se 1 (by rfl) ⟨2551958, by rfl⟩ : syracuseStep 3402611 = 5103917) B5103917
theorem B3402647 : Blo 1510952 3402647 := bstep (se 1 (by rfl) ⟨2551985, by rfl⟩ : syracuseStep 3402647 = 5103971) B5103971
theorem B26168395 : Blo 1510952 26168395 := bstep (se 1 (by rfl) ⟨19626296, by rfl⟩ : syracuseStep 26168395 = 39252593) B39252593
theorem B3402827 : Blo 1510952 3402827 := bstep (se 1 (by rfl) ⟨2552120, by rfl⟩ : syracuseStep 3402827 = 5104241) B5104241
theorem B39291979 : Blo 1510952 39291979 := bstep (se 1 (by rfl) ⟨29468984, by rfl⟩ : syracuseStep 39291979 = 58937969) B58937969
theorem B3402881 : Blo 1510952 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B3230849 : Blo 1510952 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B7269527 : Blo 1510952 7269527 := bstep (se 1 (by rfl) ⟨5452145, by rfl⟩ : syracuseStep 7269527 = 10904291) B10904291
theorem B2723059 : Blo 1510952 2723059 := bstep (se 1 (by rfl) ⟨2042294, by rfl⟩ : syracuseStep 2723059 = 4084589) B4084589
theorem B2551115 : Blo 1510952 2551115 := bstep (se 1 (by rfl) ⟨1913336, by rfl⟩ : syracuseStep 2551115 = 3826673) B3826673
theorem B3403097 : Blo 1510952 3403097 := bstep (se 2 (by rfl) ⟨1276161, by rfl⟩ : syracuseStep 3403097 = 2552323) B2552323
theorem B4304279 : Blo 1510952 4304279 := bstep (se 1 (by rfl) ⟨3228209, by rfl⟩ : syracuseStep 4304279 = 6456419) B6456419
theorem B2723225 : Blo 1510952 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B2043289 : Blo 1510952 2043289 := bstep (se 2 (by rfl) ⟨766233, by rfl⟩ : syracuseStep 2043289 = 1532467) B1532467
theorem B12914099 : Blo 1510952 12914099 := bstep (se 1 (by rfl) ⟨9685574, by rfl⟩ : syracuseStep 12914099 = 19371149) B19371149
theorem B17460659 : Blo 1510952 17460659 := bstep (se 1 (by rfl) ⟨13095494, by rfl⟩ : syracuseStep 17460659 = 26190989) B26190989
theorem B3403187 : Blo 1510952 3403187 := bstep (se 1 (by rfl) ⟨2552390, by rfl⟩ : syracuseStep 3403187 = 5104781) B5104781
theorem B2551243 : Blo 1510952 2551243 := bstep (se 1 (by rfl) ⟨1913432, by rfl⟩ : syracuseStep 2551243 = 3826865) B3826865
theorem B3403223 : Blo 1510952 3403223 := bstep (se 1 (by rfl) ⟨2552417, by rfl⟩ : syracuseStep 3403223 = 5104835) B5104835
theorem B3231191 : Blo 1510952 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B2870795 : Blo 1510952 2870795 := bstep (se 1 (by rfl) ⟨2153096, by rfl⟩ : syracuseStep 2870795 = 4306193) B4306193
theorem B1510955 : Blo 1510952 1510955 := bstep (se 1 (by rfl) ⟨1133216, by rfl⟩ : syracuseStep 1510955 = 2266433) B2266433
theorem B1510967 : Blo 1510952 1510967 := bstep (se 1 (by rfl) ⟨1133225, by rfl⟩ : syracuseStep 1510967 = 2266451) B2266451
theorem B1510987 : Blo 1510952 1510987 := bstep (se 1 (by rfl) ⟨1133240, by rfl⟩ : syracuseStep 1510987 = 2266481) B2266481
theorem B1510999 : Blo 1510952 1510999 := bstep (se 1 (by rfl) ⟨1133249, by rfl⟩ : syracuseStep 1510999 = 2266499) B2266499
theorem B2551385 : Blo 1510952 2551385 := bstep (se 2 (by rfl) ⟨956769, by rfl⟩ : syracuseStep 2551385 = 1913539) B1913539
theorem B1511019 : Blo 1510952 1511019 := bstep (se 1 (by rfl) ⟨1133264, by rfl⟩ : syracuseStep 1511019 = 2266529) B2266529
theorem B1511031 : Blo 1510952 1511031 := bstep (se 1 (by rfl) ⟨1133273, by rfl⟩ : syracuseStep 1511031 = 2266547) B2266547
theorem B1511051 : Blo 1510952 1511051 := bstep (se 1 (by rfl) ⟨1133288, by rfl⟩ : syracuseStep 1511051 = 2266577) B2266577
theorem B3403403 : Blo 1510952 3403403 := bstep (se 1 (by rfl) ⟨2552552, by rfl⟩ : syracuseStep 3403403 = 5105105) B5105105
theorem B1511063 : Blo 1510952 1511063 := bstep (se 1 (by rfl) ⟨1133297, by rfl⟩ : syracuseStep 1511063 = 2266595) B2266595
theorem B6459031 : Blo 1510952 6459031 := bstep (se 1 (by rfl) ⟨4844273, by rfl⟩ : syracuseStep 6459031 = 9688547) B9688547
theorem B1511083 : Blo 1510952 1511083 := bstep (se 1 (by rfl) ⟨1133312, by rfl⟩ : syracuseStep 1511083 = 2266625) B2266625
theorem B3829427 : Blo 1510952 3829427 := bstep (se 1 (by rfl) ⟨2872070, by rfl⟩ : syracuseStep 3829427 = 5744141) B5744141
theorem B1511095 : Blo 1510952 1511095 := bstep (se 1 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 1511095 = 2266643) B2266643
theorem B2870977 : Blo 1510952 2870977 := bstep (se 2 (by rfl) ⟨1076616, by rfl⟩ : syracuseStep 2870977 = 2153233) B2153233
theorem B3403457 : Blo 1510952 3403457 := bstep (se 2 (by rfl) ⟨1276296, by rfl⟩ : syracuseStep 3403457 = 2552593) B2552593
theorem B1511115 : Blo 1510952 1511115 := bstep (se 1 (by rfl) ⟨1133336, by rfl⟩ : syracuseStep 1511115 = 2266673) B2266673
theorem B1511127 : Blo 1510952 1511127 := bstep (se 1 (by rfl) ⟨1133345, by rfl⟩ : syracuseStep 1511127 = 2266691) B2266691
theorem B2551513 : Blo 1510952 2551513 := bstep (se 2 (by rfl) ⟨956817, by rfl⟩ : syracuseStep 2551513 = 1913635) B1913635
theorem B6459101 : Blo 1510952 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B1511147 : Blo 1510952 1511147 := bstep (se 1 (by rfl) ⟨1133360, by rfl⟩ : syracuseStep 1511147 = 2266721) B2266721
theorem B1511159 : Blo 1510952 1511159 := bstep (se 1 (by rfl) ⟨1133369, by rfl⟩ : syracuseStep 1511159 = 2266739) B2266739
theorem B1511179 : Blo 1510952 1511179 := bstep (se 1 (by rfl) ⟨1133384, by rfl⟩ : syracuseStep 1511179 = 2266769) B2266769
theorem B1511191 : Blo 1510952 1511191 := bstep (se 1 (by rfl) ⟨1133393, by rfl⟩ : syracuseStep 1511191 = 2266787) B2266787
theorem B1511211 : Blo 1510952 1511211 := bstep (se 1 (by rfl) ⟨1133408, by rfl⟩ : syracuseStep 1511211 = 2266817) B2266817
theorem B12914477 : Blo 1510952 12914477 := bstep (se 3 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 12914477 = 4842929) B4842929
theorem B1511223 : Blo 1510952 1511223 := bstep (se 1 (by rfl) ⟨1133417, by rfl⟩ : syracuseStep 1511223 = 2266835) B2266835
theorem B1511243 : Blo 1510952 1511243 := bstep (se 1 (by rfl) ⟨1133432, by rfl⟩ : syracuseStep 1511243 = 2266865) B2266865
theorem B1912663 : Blo 1510952 1912663 := bstep (se 1 (by rfl) ⟨1434497, by rfl⟩ : syracuseStep 1912663 = 2868995) B2868995
theorem B1511255 : Blo 1510952 1511255 := bstep (se 1 (by rfl) ⟨1133441, by rfl⟩ : syracuseStep 1511255 = 2266883) B2266883
theorem B1511275 : Blo 1510952 1511275 := bstep (se 1 (by rfl) ⟨1133456, by rfl⟩ : syracuseStep 1511275 = 2266913) B2266913
theorem B1511287 : Blo 1510952 1511287 := bstep (se 1 (by rfl) ⟨1133465, by rfl⟩ : syracuseStep 1511287 = 2266931) B2266931
theorem B1511307 : Blo 1510952 1511307 := bstep (se 1 (by rfl) ⟨1133480, by rfl⟩ : syracuseStep 1511307 = 2266961) B2266961
theorem B2723723 : Blo 1510952 2723723 := bstep (se 1 (by rfl) ⟨2042792, by rfl⟩ : syracuseStep 2723723 = 4085585) B4085585
theorem B1511319 : Blo 1510952 1511319 := bstep (se 1 (by rfl) ⟨1133489, by rfl⟩ : syracuseStep 1511319 = 2266979) B2266979
theorem B3403673 : Blo 1510952 3403673 := bstep (se 2 (by rfl) ⟨1276377, by rfl⟩ : syracuseStep 3403673 = 2552755) B2552755
theorem B1511339 : Blo 1510952 1511339 := bstep (se 1 (by rfl) ⟨1133504, by rfl⟩ : syracuseStep 1511339 = 2267009) B2267009
theorem B1511351 : Blo 1510952 1511351 := bstep (se 1 (by rfl) ⟨1133513, by rfl⟩ : syracuseStep 1511351 = 2267027) B2267027
theorem B1511371 : Blo 1510952 1511371 := bstep (se 1 (by rfl) ⟨1133528, by rfl⟩ : syracuseStep 1511371 = 2267057) B2267057
theorem B1511383 : Blo 1510952 1511383 := bstep (se 1 (by rfl) ⟨1133537, by rfl⟩ : syracuseStep 1511383 = 2267075) B2267075
theorem B2453465 : Blo 1510952 2453465 := bstep (se 2 (by rfl) ⟨920049, by rfl⟩ : syracuseStep 2453465 = 1840099) B1840099
theorem B1511403 : Blo 1510952 1511403 := bstep (se 1 (by rfl) ⟨1133552, by rfl⟩ : syracuseStep 1511403 = 2267105) B2267105
theorem B3403763 : Blo 1510952 3403763 := bstep (se 1 (by rfl) ⟨2552822, by rfl⟩ : syracuseStep 3403763 = 5105645) B5105645
theorem B1511415 : Blo 1510952 1511415 := bstep (se 1 (by rfl) ⟨1133561, by rfl⟩ : syracuseStep 1511415 = 2267123) B2267123
theorem B1511435 : Blo 1510952 1511435 := bstep (se 1 (by rfl) ⟨1133576, by rfl⟩ : syracuseStep 1511435 = 2267153) B2267153
theorem B5099543 : Blo 1510952 5099543 := bstep (se 1 (by rfl) ⟨3824657, by rfl⟩ : syracuseStep 5099543 = 7649315) B7649315
theorem B1511447 : Blo 1510952 1511447 := bstep (se 1 (by rfl) ⟨1133585, by rfl⟩ : syracuseStep 1511447 = 2267171) B2267171
theorem B5451799 : Blo 1510952 5451799 := bstep (se 1 (by rfl) ⟨4088849, by rfl⟩ : syracuseStep 5451799 = 8177699) B8177699
theorem B3403799 : Blo 1510952 3403799 := bstep (se 1 (by rfl) ⟨2552849, by rfl⟩ : syracuseStep 3403799 = 5105699) B5105699
theorem B1511467 : Blo 1510952 1511467 := bstep (se 1 (by rfl) ⟨1133600, by rfl⟩ : syracuseStep 1511467 = 2267201) B2267201
theorem B1511479 : Blo 1510952 1511479 := bstep (se 1 (by rfl) ⟨1133609, by rfl⟩ : syracuseStep 1511479 = 2267219) B2267219
theorem B1699915 : Blo 1510952 1699915 := bstep (se 1 (by rfl) ⟨1274936, by rfl⟩ : syracuseStep 1699915 = 2549873) B2549873
theorem B1511499 : Blo 1510952 1511499 := bstep (se 1 (by rfl) ⟨1133624, by rfl⟩ : syracuseStep 1511499 = 2267249) B2267249
theorem B1511511 : Blo 1510952 1511511 := bstep (se 1 (by rfl) ⟨1133633, by rfl⟩ : syracuseStep 1511511 = 2267267) B2267267
theorem B13791325 : Blo 1510952 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B1511531 : Blo 1510952 1511531 := bstep (se 1 (by rfl) ⟨1133648, by rfl⟩ : syracuseStep 1511531 = 2267297) B2267297
theorem B1511543 : Blo 1510952 1511543 := bstep (se 1 (by rfl) ⟨1133657, by rfl⟩ : syracuseStep 1511543 = 2267315) B2267315
theorem B2871425 : Blo 1510952 2871425 := bstep (se 2 (by rfl) ⟨1076784, by rfl⟩ : syracuseStep 2871425 = 2153569) B2153569
theorem B5738627 : Blo 1510952 5738627 := bstep (se 1 (by rfl) ⟨4303970, by rfl⟩ : syracuseStep 5738627 = 8607941) B8607941
theorem B1511563 : Blo 1510952 1511563 := bstep (se 1 (by rfl) ⟨1133672, by rfl⟩ : syracuseStep 1511563 = 2267345) B2267345
theorem B1511575 : Blo 1510952 1511575 := bstep (se 1 (by rfl) ⟨1133681, by rfl⟩ : syracuseStep 1511575 = 2267363) B2267363
theorem B1511595 : Blo 1510952 1511595 := bstep (se 1 (by rfl) ⟨1133696, by rfl⟩ : syracuseStep 1511595 = 2267393) B2267393
theorem B1700023 : Blo 1510952 1700023 := bstep (se 1 (by rfl) ⟨1275017, by rfl⟩ : syracuseStep 1700023 = 2550035) B2550035
theorem B1511607 : Blo 1510952 1511607 := bstep (se 1 (by rfl) ⟨1133705, by rfl⟩ : syracuseStep 1511607 = 2267411) B2267411
theorem B1511627 : Blo 1510952 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B3403979 : Blo 1510952 3403979 := bstep (se 1 (by rfl) ⟨2552984, by rfl⟩ : syracuseStep 3403979 = 5105969) B5105969
theorem B1511639 : Blo 1510952 1511639 := bstep (se 1 (by rfl) ⟨1133729, by rfl⟩ : syracuseStep 1511639 = 2267459) B2267459
theorem B1511659 : Blo 1510952 1511659 := bstep (se 1 (by rfl) ⟨1133744, by rfl⟩ : syracuseStep 1511659 = 2267489) B2267489
theorem B1511671 : Blo 1510952 1511671 := bstep (se 1 (by rfl) ⟨1133753, by rfl⟩ : syracuseStep 1511671 = 2267507) B2267507
theorem B2724097 : Blo 1510952 2724097 := bstep (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) B2043073
theorem B3404033 : Blo 1510952 3404033 := bstep (se 2 (by rfl) ⟨1276512, by rfl⟩ : syracuseStep 3404033 = 2553025) B2553025
theorem B1511691 : Blo 1510952 1511691 := bstep (se 1 (by rfl) ⟨1133768, by rfl⟩ : syracuseStep 1511691 = 2267537) B2267537
theorem B1511703 : Blo 1510952 1511703 := bstep (se 1 (by rfl) ⟨1133777, by rfl⟩ : syracuseStep 1511703 = 2267555) B2267555
theorem B2552087 : Blo 1510952 2552087 := bstep (se 1 (by rfl) ⟨1914065, by rfl⟩ : syracuseStep 2552087 = 3828131) B3828131
theorem B1511723 : Blo 1510952 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B4600115 : Blo 1510952 4600115 := bstep (se 1 (by rfl) ⟨3450086, by rfl⟩ : syracuseStep 4600115 = 6900173) B6900173
theorem B1511735 : Blo 1510952 1511735 := bstep (se 1 (by rfl) ⟨1133801, by rfl⟩ : syracuseStep 1511735 = 2267603) B2267603
theorem B8606027 : Blo 1510952 8606027 := bstep (se 1 (by rfl) ⟨6454520, by rfl⟩ : syracuseStep 8606027 = 12909041) B12909041
theorem B1511755 : Blo 1510952 1511755 := bstep (se 1 (by rfl) ⟨1133816, by rfl⟩ : syracuseStep 1511755 = 2267633) B2267633
theorem B1511767 : Blo 1510952 1511767 := bstep (se 1 (by rfl) ⟨1133825, by rfl⟩ : syracuseStep 1511767 = 2267651) B2267651
theorem B2724185 : Blo 1510952 2724185 := bstep (se 2 (by rfl) ⟨1021569, by rfl⟩ : syracuseStep 2724185 = 2043139) B2043139
theorem B1700203 : Blo 1510952 1700203 := bstep (se 1 (by rfl) ⟨1275152, by rfl⟩ : syracuseStep 1700203 = 2550305) B2550305
theorem B1511787 : Blo 1510952 1511787 := bstep (se 1 (by rfl) ⟨1133840, by rfl⟩ : syracuseStep 1511787 = 2267681) B2267681
theorem B1511799 : Blo 1510952 1511799 := bstep (se 1 (by rfl) ⟨1133849, by rfl⟩ : syracuseStep 1511799 = 2267699) B2267699
theorem B1511819 : Blo 1510952 1511819 := bstep (se 1 (by rfl) ⟨1133864, by rfl⟩ : syracuseStep 1511819 = 2267729) B2267729
theorem B1511831 : Blo 1510952 1511831 := bstep (se 1 (by rfl) ⟨1133873, by rfl⟩ : syracuseStep 1511831 = 2267747) B2267747
theorem B2552215 : Blo 1510952 2552215 := bstep (se 1 (by rfl) ⟨1914161, by rfl⟩ : syracuseStep 2552215 = 3828323) B3828323
theorem B1511851 : Blo 1510952 1511851 := bstep (se 1 (by rfl) ⟨1133888, by rfl⟩ : syracuseStep 1511851 = 2267777) B2267777
theorem B1511863 : Blo 1510952 1511863 := bstep (se 1 (by rfl) ⟨1133897, by rfl⟩ : syracuseStep 1511863 = 2267795) B2267795
theorem B1511883 : Blo 1510952 1511883 := bstep (se 1 (by rfl) ⟨1133912, by rfl⟩ : syracuseStep 1511883 = 2267825) B2267825
theorem B6459851 : Blo 1510952 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B1700311 : Blo 1510952 1700311 := bstep (se 1 (by rfl) ⟨1275233, by rfl⟩ : syracuseStep 1700311 = 2550467) B2550467
theorem B1511895 : Blo 1510952 1511895 := bstep (se 1 (by rfl) ⟨1133921, by rfl⟩ : syracuseStep 1511895 = 2267843) B2267843
theorem B2871767 : Blo 1510952 2871767 := bstep (se 1 (by rfl) ⟨2153825, by rfl⟩ : syracuseStep 2871767 = 4307651) B4307651
theorem B1511915 : Blo 1510952 1511915 := bstep (se 1 (by rfl) ⟨1133936, by rfl⟩ : syracuseStep 1511915 = 2267873) B2267873
theorem B1511927 : Blo 1510952 1511927 := bstep (se 1 (by rfl) ⟨1133945, by rfl⟩ : syracuseStep 1511927 = 2267891) B2267891
theorem B12268037 : Blo 1510952 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B1511947 : Blo 1510952 1511947 := bstep (se 1 (by rfl) ⟨1133960, by rfl⟩ : syracuseStep 1511947 = 2267921) B2267921
theorem B1511959 : Blo 1510952 1511959 := bstep (se 1 (by rfl) ⟨1133969, by rfl⟩ : syracuseStep 1511959 = 2267939) B2267939
theorem B1511979 : Blo 1510952 1511979 := bstep (se 1 (by rfl) ⟨1133984, by rfl⟩ : syracuseStep 1511979 = 2267969) B2267969
theorem B5100083 : Blo 1510952 5100083 := bstep (se 1 (by rfl) ⟨3825062, by rfl⟩ : syracuseStep 5100083 = 7650125) B7650125
theorem B1511991 : Blo 1510952 1511991 := bstep (se 1 (by rfl) ⟨1133993, by rfl⟩ : syracuseStep 1511991 = 2267987) B2267987
theorem B5739083 : Blo 1510952 5739083 := bstep (se 1 (by rfl) ⟨4304312, by rfl⟩ : syracuseStep 5739083 = 8608625) B8608625
theorem B1512011 : Blo 1510952 1512011 := bstep (se 1 (by rfl) ⟨1134008, by rfl⟩ : syracuseStep 1512011 = 2268017) B2268017
theorem B1512023 : Blo 1510952 1512023 := bstep (se 1 (by rfl) ⟨1134017, by rfl⟩ : syracuseStep 1512023 = 2268035) B2268035
theorem B1512043 : Blo 1510952 1512043 := bstep (se 1 (by rfl) ⟨1134032, by rfl⟩ : syracuseStep 1512043 = 2268065) B2268065
theorem B1512055 : Blo 1510952 1512055 := bstep (se 1 (by rfl) ⟨1134041, by rfl⟩ : syracuseStep 1512055 = 2268083) B2268083
theorem B9196163 : Blo 1510952 9196163 := bstep (se 1 (by rfl) ⟨6897122, by rfl⟩ : syracuseStep 9196163 = 13794245) B13794245
theorem B1700491 : Blo 1510952 1700491 := bstep (se 1 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 1700491 = 2550737) B2550737
theorem B1913483 : Blo 1510952 1913483 := bstep (se 1 (by rfl) ⟨1435112, by rfl⟩ : syracuseStep 1913483 = 2870225) B2870225
theorem B1512075 : Blo 1510952 1512075 := bstep (se 1 (by rfl) ⟨1134056, by rfl⟩ : syracuseStep 1512075 = 2268113) B2268113
theorem B1512087 : Blo 1510952 1512087 := bstep (se 1 (by rfl) ⟨1134065, by rfl⟩ : syracuseStep 1512087 = 2268131) B2268131
theorem B1512107 : Blo 1510952 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B1512119 : Blo 1510952 1512119 := bstep (se 1 (by rfl) ⟨1134089, by rfl⟩ : syracuseStep 1512119 = 2268179) B2268179
theorem B4305611 : Blo 1510952 4305611 := bstep (se 1 (by rfl) ⟨3229208, by rfl⟩ : syracuseStep 4305611 = 6458417) B6458417
theorem B20689613 : Blo 1510952 20689613 := bstep (se 3 (by rfl) ⟨3879302, by rfl⟩ : syracuseStep 20689613 = 7758605) B7758605
theorem B1512139 : Blo 1510952 1512139 := bstep (se 1 (by rfl) ⟨1134104, by rfl⟩ : syracuseStep 1512139 = 2268209) B2268209
theorem B1512151 : Blo 1510952 1512151 := bstep (se 1 (by rfl) ⟨1134113, by rfl⟩ : syracuseStep 1512151 = 2268227) B2268227
theorem B4788953 : Blo 1510952 4788953 := bstep (se 2 (by rfl) ⟨1795857, by rfl⟩ : syracuseStep 4788953 = 3591715) B3591715
theorem B1512171 : Blo 1510952 1512171 := bstep (se 1 (by rfl) ⟨1134128, by rfl⟩ : syracuseStep 1512171 = 2268257) B2268257
theorem B1700599 : Blo 1510952 1700599 := bstep (se 1 (by rfl) ⟨1275449, by rfl⟩ : syracuseStep 1700599 = 2550899) B2550899
theorem B1512183 : Blo 1510952 1512183 := bstep (se 1 (by rfl) ⟨1134137, by rfl⟩ : syracuseStep 1512183 = 2268275) B2268275
theorem B1512203 : Blo 1510952 1512203 := bstep (se 1 (by rfl) ⟨1134152, by rfl⟩ : syracuseStep 1512203 = 2268305) B2268305
theorem B5739281 : Blo 1510952 5739281 := bstep (se 2 (by rfl) ⟨2152230, by rfl⟩ : syracuseStep 5739281 = 4304461) B4304461
theorem B1512215 : Blo 1510952 1512215 := bstep (se 1 (by rfl) ⟨1134161, by rfl⟩ : syracuseStep 1512215 = 2268323) B2268323
theorem B1512235 : Blo 1510952 1512235 := bstep (se 1 (by rfl) ⟨1134176, by rfl⟩ : syracuseStep 1512235 = 2268353) B2268353
theorem B1512247 : Blo 1510952 1512247 := bstep (se 1 (by rfl) ⟨1134185, by rfl⟩ : syracuseStep 1512247 = 2268371) B2268371
theorem B5100353 : Blo 1510952 5100353 := bstep (se 2 (by rfl) ⟨1912632, by rfl⟩ : syracuseStep 5100353 = 3825265) B3825265
theorem B1512267 : Blo 1510952 1512267 := bstep (se 1 (by rfl) ⟨1134200, by rfl⟩ : syracuseStep 1512267 = 2268401) B2268401
theorem B1512279 : Blo 1510952 1512279 := bstep (se 1 (by rfl) ⟨1134209, by rfl⟩ : syracuseStep 1512279 = 2268419) B2268419
theorem B1512299 : Blo 1510952 1512299 := bstep (se 1 (by rfl) ⟨1134224, by rfl⟩ : syracuseStep 1512299 = 2268449) B2268449
theorem B1512311 : Blo 1510952 1512311 := bstep (se 1 (by rfl) ⟨1134233, by rfl⟩ : syracuseStep 1512311 = 2268467) B2268467
theorem B1512331 : Blo 1510952 1512331 := bstep (se 1 (by rfl) ⟨1134248, by rfl⟩ : syracuseStep 1512331 = 2268497) B2268497
theorem B1512343 : Blo 1510952 1512343 := bstep (se 1 (by rfl) ⟨1134257, by rfl⟩ : syracuseStep 1512343 = 2268515) B2268515
theorem B2724761 : Blo 1510952 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B1700779 : Blo 1510952 1700779 := bstep (se 1 (by rfl) ⟨1275584, by rfl⟩ : syracuseStep 1700779 = 2551169) B2551169
theorem B1512363 : Blo 1510952 1512363 := bstep (se 1 (by rfl) ⟨1134272, by rfl⟩ : syracuseStep 1512363 = 2268545) B2268545
theorem B1512375 : Blo 1510952 1512375 := bstep (se 1 (by rfl) ⟨1134281, by rfl⟩ : syracuseStep 1512375 = 2268563) B2268563
theorem B4846529 : Blo 1510952 4846529 := bstep (se 2 (by rfl) ⟨1817448, by rfl⟩ : syracuseStep 4846529 = 3634897) B3634897
theorem B1512395 : Blo 1510952 1512395 := bstep (se 1 (by rfl) ⟨1134296, by rfl⟩ : syracuseStep 1512395 = 2268593) B2268593
theorem B1512407 : Blo 1510952 1512407 := bstep (se 1 (by rfl) ⟨1134305, by rfl⟩ : syracuseStep 1512407 = 2268611) B2268611
theorem B1512427 : Blo 1510952 1512427 := bstep (se 1 (by rfl) ⟨1134320, by rfl⟩ : syracuseStep 1512427 = 2268641) B2268641
theorem B1512439 : Blo 1510952 1512439 := bstep (se 1 (by rfl) ⟨1134329, by rfl⟩ : syracuseStep 1512439 = 2268659) B2268659
theorem B1512459 : Blo 1510952 1512459 := bstep (se 1 (by rfl) ⟨1134344, by rfl⟩ : syracuseStep 1512459 = 2268689) B2268689
theorem B2552843 : Blo 1510952 2552843 := bstep (se 1 (by rfl) ⟨1914632, by rfl⟩ : syracuseStep 2552843 = 3829265) B3829265
theorem B1700887 : Blo 1510952 1700887 := bstep (se 1 (by rfl) ⟨1275665, by rfl⟩ : syracuseStep 1700887 = 2551331) B2551331
theorem B1512471 : Blo 1510952 1512471 := bstep (se 1 (by rfl) ⟨1134353, by rfl⟩ : syracuseStep 1512471 = 2268707) B2268707
theorem B1512491 : Blo 1510952 1512491 := bstep (se 1 (by rfl) ⟨1134368, by rfl⟩ : syracuseStep 1512491 = 2268737) B2268737
theorem B8614957 : Blo 1510952 8614957 := bstep (se 3 (by rfl) ⟨1615304, by rfl⟩ : syracuseStep 8614957 = 3230609) B3230609
theorem B1512503 : Blo 1510952 1512503 := bstep (se 1 (by rfl) ⟨1134377, by rfl⟩ : syracuseStep 1512503 = 2268755) B2268755
theorem B10892353 : Blo 1510952 10892353 := bstep (se 2 (by rfl) ⟨4084632, by rfl⟩ : syracuseStep 10892353 = 8169265) B8169265
theorem B1512523 : Blo 1510952 1512523 := bstep (se 1 (by rfl) ⟨1134392, by rfl⟩ : syracuseStep 1512523 = 2268785) B2268785
theorem B1512535 : Blo 1510952 1512535 := bstep (se 1 (by rfl) ⟨1134401, by rfl⟩ : syracuseStep 1512535 = 2268803) B2268803
theorem B1512555 : Blo 1510952 1512555 := bstep (se 1 (by rfl) ⟨1134416, by rfl⟩ : syracuseStep 1512555 = 2268833) B2268833
theorem B1512567 : Blo 1510952 1512567 := bstep (se 1 (by rfl) ⟨1134425, by rfl⟩ : syracuseStep 1512567 = 2268851) B2268851
theorem B1512587 : Blo 1510952 1512587 := bstep (se 1 (by rfl) ⟨1134440, by rfl⟩ : syracuseStep 1512587 = 2268881) B2268881
theorem B2552971 : Blo 1510952 2552971 := bstep (se 1 (by rfl) ⟨1914728, by rfl⟩ : syracuseStep 2552971 = 3829457) B3829457
theorem B1512599 : Blo 1510952 1512599 := bstep (se 1 (by rfl) ⟨1134449, by rfl⟩ : syracuseStep 1512599 = 2268899) B2268899
theorem B1512619 : Blo 1510952 1512619 := bstep (se 1 (by rfl) ⟨1134464, by rfl⟩ : syracuseStep 1512619 = 2268929) B2268929
theorem B1512631 : Blo 1510952 1512631 := bstep (se 1 (by rfl) ⟨1134473, by rfl⟩ : syracuseStep 1512631 = 2268947) B2268947
theorem B1701067 : Blo 1510952 1701067 := bstep (se 1 (by rfl) ⟨1275800, by rfl⟩ : syracuseStep 1701067 = 2551601) B2551601
theorem B3634379 : Blo 1510952 3634379 := bstep (se 1 (by rfl) ⟨2725784, by rfl⟩ : syracuseStep 3634379 = 5451569) B5451569
theorem B1512651 : Blo 1510952 1512651 := bstep (se 1 (by rfl) ⟨1134488, by rfl⟩ : syracuseStep 1512651 = 2268977) B2268977
theorem B1512663 : Blo 1510952 1512663 := bstep (se 1 (by rfl) ⟨1134497, by rfl⟩ : syracuseStep 1512663 = 2268995) B2268995
theorem B13268185 : Blo 1510952 13268185 := bstep (se 2 (by rfl) ⟨4975569, by rfl⟩ : syracuseStep 13268185 = 9951139) B9951139
theorem B1512683 : Blo 1510952 1512683 := bstep (se 1 (by rfl) ⟨1134512, by rfl⟩ : syracuseStep 1512683 = 2269025) B2269025
theorem B1512695 : Blo 1510952 1512695 := bstep (se 1 (by rfl) ⟨1134521, by rfl⟩ : syracuseStep 1512695 = 2269043) B2269043
theorem B1512715 : Blo 1510952 1512715 := bstep (se 1 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 1512715 = 2269073) B2269073
theorem B1512727 : Blo 1510952 1512727 := bstep (se 1 (by rfl) ⟨1134545, by rfl⟩ : syracuseStep 1512727 = 2269091) B2269091
theorem B1512747 : Blo 1510952 1512747 := bstep (se 1 (by rfl) ⟨1134560, by rfl⟩ : syracuseStep 1512747 = 2269121) B2269121
theorem B1701175 : Blo 1510952 1701175 := bstep (se 1 (by rfl) ⟨1275881, by rfl⟩ : syracuseStep 1701175 = 2551763) B2551763
theorem B1512759 : Blo 1510952 1512759 := bstep (se 1 (by rfl) ⟨1134569, by rfl⟩ : syracuseStep 1512759 = 2269139) B2269139
theorem B1914187 : Blo 1510952 1914187 := bstep (se 1 (by rfl) ⟨1435640, by rfl⟩ : syracuseStep 1914187 = 2871281) B2871281
theorem B1512779 : Blo 1510952 1512779 := bstep (se 1 (by rfl) ⟨1134584, by rfl⟩ : syracuseStep 1512779 = 2269169) B2269169
theorem B2725207 : Blo 1510952 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B1512791 : Blo 1510952 1512791 := bstep (se 1 (by rfl) ⟨1134593, by rfl⟩ : syracuseStep 1512791 = 2269187) B2269187
theorem B2266457 : Blo 1510952 2266457 := bstep (se 2 (by rfl) ⟨849921, by rfl⟩ : syracuseStep 2266457 = 1699843) B1699843
theorem B5100893 : Blo 1510952 5100893 := bstep (se 3 (by rfl) ⟨956417, by rfl⟩ : syracuseStep 5100893 = 1912835) B1912835
theorem B1512811 : Blo 1510952 1512811 := bstep (se 1 (by rfl) ⟨1134608, by rfl⟩ : syracuseStep 1512811 = 2269217) B2269217
theorem B1512823 : Blo 1510952 1512823 := bstep (se 1 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 1512823 = 2269235) B2269235
theorem B1512843 : Blo 1510952 1512843 := bstep (se 1 (by rfl) ⟨1134632, by rfl⟩ : syracuseStep 1512843 = 2269265) B2269265
theorem B1512855 : Blo 1510952 1512855 := bstep (se 1 (by rfl) ⟨1134641, by rfl⟩ : syracuseStep 1512855 = 2269283) B2269283
theorem B1512875 : Blo 1510952 1512875 := bstep (se 1 (by rfl) ⟨1134656, by rfl⟩ : syracuseStep 1512875 = 2269313) B2269313
theorem B1512887 : Blo 1510952 1512887 := bstep (se 1 (by rfl) ⟨1134665, by rfl⟩ : syracuseStep 1512887 = 2269331) B2269331
theorem B2266571 : Blo 1510952 2266571 := bstep (se 1 (by rfl) ⟨1699928, by rfl⟩ : syracuseStep 2266571 = 3399857) B3399857
theorem B2151883 : Blo 1510952 2151883 := bstep (se 1 (by rfl) ⟨1613912, by rfl⟩ : syracuseStep 2151883 = 3227825) B3227825
theorem B1512907 : Blo 1510952 1512907 := bstep (se 1 (by rfl) ⟨1134680, by rfl⟩ : syracuseStep 1512907 = 2269361) B2269361
theorem B2266583 : Blo 1510952 2266583 := bstep (se 1 (by rfl) ⟨1699937, by rfl⟩ : syracuseStep 2266583 = 3399875) B3399875
theorem B1512919 : Blo 1510952 1512919 := bstep (se 1 (by rfl) ⟨1134689, by rfl⟩ : syracuseStep 1512919 = 2269379) B2269379
theorem B1701355 : Blo 1510952 1701355 := bstep (se 1 (by rfl) ⟨1276016, by rfl⟩ : syracuseStep 1701355 = 2552033) B2552033
theorem B1512939 : Blo 1510952 1512939 := bstep (se 1 (by rfl) ⟨1134704, by rfl⟩ : syracuseStep 1512939 = 2269409) B2269409
theorem B1512951 : Blo 1510952 1512951 := bstep (se 1 (by rfl) ⟨1134713, by rfl⟩ : syracuseStep 1512951 = 2269427) B2269427
theorem B5740055 : Blo 1510952 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B2266649 : Blo 1510952 2266649 := bstep (se 2 (by rfl) ⟨849993, by rfl⟩ : syracuseStep 2266649 = 1699987) B1699987
theorem B7763531 : Blo 1510952 7763531 := bstep (se 1 (by rfl) ⟨5822648, by rfl⟩ : syracuseStep 7763531 = 11645297) B11645297
theorem B1701463 : Blo 1510952 1701463 := bstep (se 1 (by rfl) ⟨1276097, by rfl⟩ : syracuseStep 1701463 = 2552195) B2552195
theorem B1914455 : Blo 1510952 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B43570781 : Blo 1510952 43570781 := bstep (se 3 (by rfl) ⟨8169521, by rfl⟩ : syracuseStep 43570781 = 16339043) B16339043
theorem B7657091 : Blo 1510952 7657091 := bstep (se 1 (by rfl) ⟨5742818, by rfl⟩ : syracuseStep 7657091 = 11485637) B11485637
theorem B2266763 : Blo 1510952 2266763 := bstep (se 1 (by rfl) ⟨1700072, by rfl⟩ : syracuseStep 2266763 = 3400145) B3400145
theorem B2266775 : Blo 1510952 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B2266841 : Blo 1510952 2266841 := bstep (se 2 (by rfl) ⟨850065, by rfl⟩ : syracuseStep 2266841 = 1700131) B1700131
theorem B5740253 : Blo 1510952 5740253 := bstep (se 3 (by rfl) ⟨1076297, by rfl⟩ : syracuseStep 5740253 = 2152595) B2152595
theorem B1701643 : Blo 1510952 1701643 := bstep (se 1 (by rfl) ⟨1276232, by rfl⟩ : syracuseStep 1701643 = 2552465) B2552465
theorem B2266955 : Blo 1510952 2266955 := bstep (se 1 (by rfl) ⟨1700216, by rfl⟩ : syracuseStep 2266955 = 3400433) B3400433
theorem B2266967 : Blo 1510952 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B1701751 : Blo 1510952 1701751 := bstep (se 1 (by rfl) ⟨1276313, by rfl⟩ : syracuseStep 1701751 = 2552627) B2552627
theorem B2267033 : Blo 1510952 2267033 := bstep (se 2 (by rfl) ⟨850137, by rfl⟩ : syracuseStep 2267033 = 1700275) B1700275
theorem B55891891 : Blo 1510952 55891891 := bstep (se 1 (by rfl) ⟨41918918, by rfl⟩ : syracuseStep 55891891 = 83837837) B83837837
theorem B8607667 : Blo 1510952 8607667 := bstep (se 1 (by rfl) ⟨6455750, by rfl⟩ : syracuseStep 8607667 = 12911501) B12911501
theorem B2267147 : Blo 1510952 2267147 := bstep (se 1 (by rfl) ⟨1700360, by rfl⟩ : syracuseStep 2267147 = 3400721) B3400721
theorem B2267159 : Blo 1510952 2267159 := bstep (se 1 (by rfl) ⟨1700369, by rfl⟩ : syracuseStep 2267159 = 3400739) B3400739
theorem B1701931 : Blo 1510952 1701931 := bstep (se 1 (by rfl) ⟨1276448, by rfl⟩ : syracuseStep 1701931 = 2552897) B2552897
theorem B1816651 : Blo 1510952 1816651 := bstep (se 1 (by rfl) ⟨1362488, by rfl⟩ : syracuseStep 1816651 = 2724977) B2724977
theorem B6543449 : Blo 1510952 6543449 := bstep (se 2 (by rfl) ⟨2453793, by rfl⟩ : syracuseStep 6543449 = 4907587) B4907587
theorem B2267225 : Blo 1510952 2267225 := bstep (se 2 (by rfl) ⟨850209, by rfl⟩ : syracuseStep 2267225 = 1700419) B1700419
theorem B1702039 : Blo 1510952 1702039 := bstep (se 1 (by rfl) ⟨1276529, by rfl⟩ : syracuseStep 1702039 = 2553059) B2553059
theorem B2267339 : Blo 1510952 2267339 := bstep (se 1 (by rfl) ⟨1700504, by rfl⟩ : syracuseStep 2267339 = 3401009) B3401009
theorem B2267351 : Blo 1510952 2267351 := bstep (se 1 (by rfl) ⟨1700513, by rfl⟩ : syracuseStep 2267351 = 3401027) B3401027
theorem B2267417 : Blo 1510952 2267417 := bstep (se 2 (by rfl) ⟨850281, by rfl⟩ : syracuseStep 2267417 = 1700563) B1700563
theorem B4307251 : Blo 1510952 4307251 := bstep (se 1 (by rfl) ⟨3230438, by rfl⟩ : syracuseStep 4307251 = 6460877) B6460877
theorem B24525173 : Blo 1510952 24525173 := bstep (se 5 (by rfl) ⟨1149617, by rfl⟩ : syracuseStep 24525173 = 2299235) B2299235
theorem B2267531 : Blo 1510952 2267531 := bstep (se 1 (by rfl) ⟨1700648, by rfl⟩ : syracuseStep 2267531 = 3401297) B3401297
theorem B2267543 : Blo 1510952 2267543 := bstep (se 1 (by rfl) ⟨1700657, by rfl⟩ : syracuseStep 2267543 = 3401315) B3401315
theorem B5102027 : Blo 1510952 5102027 := bstep (se 1 (by rfl) ⟨3826520, by rfl⟩ : syracuseStep 5102027 = 7653041) B7653041
theorem B2267609 : Blo 1510952 2267609 := bstep (se 2 (by rfl) ⟨850353, by rfl⟩ : syracuseStep 2267609 = 1700707) B1700707
theorem B11483693 : Blo 1510952 11483693 := bstep (se 3 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 11483693 = 4306385) B4306385
theorem B2267723 : Blo 1510952 2267723 := bstep (se 1 (by rfl) ⟨1700792, by rfl⟩ : syracuseStep 2267723 = 3401585) B3401585
theorem B2267735 : Blo 1510952 2267735 := bstep (se 1 (by rfl) ⟨1700801, by rfl⟩ : syracuseStep 2267735 = 3401603) B3401603
theorem B2267801 : Blo 1510952 2267801 := bstep (se 2 (by rfl) ⟨850425, by rfl⟩ : syracuseStep 2267801 = 1700851) B1700851
theorem B4422347 : Blo 1510952 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B2071255 : Blo 1510952 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B5102297 : Blo 1510952 5102297 := bstep (se 2 (by rfl) ⟨1913361, by rfl⟩ : syracuseStep 5102297 = 3826723) B3826723
theorem B2267915 : Blo 1510952 2267915 := bstep (se 1 (by rfl) ⟨1700936, by rfl⟩ : syracuseStep 2267915 = 3401873) B3401873
theorem B2267927 : Blo 1510952 2267927 := bstep (se 1 (by rfl) ⟨1700945, by rfl⟩ : syracuseStep 2267927 = 3401891) B3401891
theorem B2267993 : Blo 1510952 2267993 := bstep (se 2 (by rfl) ⟨850497, by rfl⟩ : syracuseStep 2267993 = 1700995) B1700995
theorem B4422593 : Blo 1510952 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2268107 : Blo 1510952 2268107 := bstep (se 1 (by rfl) ⟨1701080, by rfl⟩ : syracuseStep 2268107 = 3402161) B3402161
theorem B11475917 : Blo 1510952 11475917 := bstep (se 3 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 11475917 = 4303469) B4303469
theorem B2268119 : Blo 1510952 2268119 := bstep (se 1 (by rfl) ⟨1701089, by rfl⟩ : syracuseStep 2268119 = 3402179) B3402179
theorem B2268185 : Blo 1510952 2268185 := bstep (se 2 (by rfl) ⟨850569, by rfl⟩ : syracuseStep 2268185 = 1701139) B1701139
theorem B9690187 : Blo 1510952 9690187 := bstep (se 1 (by rfl) ⟨7267640, by rfl⟩ : syracuseStep 9690187 = 14535281) B14535281
theorem B3824729 : Blo 1510952 3824729 := bstep (se 2 (by rfl) ⟨1434273, by rfl⟩ : syracuseStep 3824729 = 2868547) B2868547
theorem B2268299 : Blo 1510952 2268299 := bstep (se 1 (by rfl) ⟨1701224, by rfl⟩ : syracuseStep 2268299 = 3402449) B3402449
theorem B4660375 : Blo 1510952 4660375 := bstep (se 1 (by rfl) ⟨3495281, by rfl⟩ : syracuseStep 4660375 = 6990563) B6990563
theorem B2268311 : Blo 1510952 2268311 := bstep (se 1 (by rfl) ⟨1701233, by rfl⟩ : syracuseStep 2268311 = 3402467) B3402467
theorem B2268377 : Blo 1510952 2268377 := bstep (se 2 (by rfl) ⟨850641, by rfl⟩ : syracuseStep 2268377 = 1701283) B1701283
theorem B2268491 : Blo 1510952 2268491 := bstep (se 1 (by rfl) ⟨1701368, by rfl⟩ : syracuseStep 2268491 = 3402737) B3402737
theorem B4308299 : Blo 1510952 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2268503 : Blo 1510952 2268503 := bstep (se 1 (by rfl) ⟨1701377, by rfl⟩ : syracuseStep 2268503 = 3402755) B3402755
theorem B8609125 : Blo 1510952 8609125 := bstep (se 4 (by rfl) ⟨807105, by rfl⟩ : syracuseStep 8609125 = 1614211) B1614211
theorem B5102999 : Blo 1510952 5102999 := bstep (se 1 (by rfl) ⟨3827249, by rfl⟩ : syracuseStep 5102999 = 7654499) B7654499
theorem B2268569 : Blo 1510952 2268569 := bstep (se 2 (by rfl) ⟨850713, by rfl⟩ : syracuseStep 2268569 = 1701427) B1701427
theorem B11476403 : Blo 1510952 11476403 := bstep (se 1 (by rfl) ⟨8607302, by rfl⟩ : syracuseStep 11476403 = 17214605) B17214605
theorem B2268683 : Blo 1510952 2268683 := bstep (se 1 (by rfl) ⟨1701512, by rfl⟩ : syracuseStep 2268683 = 3403025) B3403025
theorem B2268695 : Blo 1510952 2268695 := bstep (se 1 (by rfl) ⟨1701521, by rfl⟩ : syracuseStep 2268695 = 3403043) B3403043
theorem B3448345 : Blo 1510952 3448345 := bstep (se 2 (by rfl) ⟨1293129, by rfl⟩ : syracuseStep 3448345 = 2586259) B2586259
theorem B6454829 : Blo 1510952 6454829 := bstep (se 3 (by rfl) ⟨1210280, by rfl⟩ : syracuseStep 6454829 = 2420561) B2420561
theorem B2268761 : Blo 1510952 2268761 := bstep (se 2 (by rfl) ⟨850785, by rfl⟩ : syracuseStep 2268761 = 1701571) B1701571
theorem B5742211 : Blo 1510952 5742211 := bstep (se 1 (by rfl) ⟨4306658, by rfl⟩ : syracuseStep 5742211 = 8613317) B8613317
theorem B9690803 : Blo 1510952 9690803 := bstep (se 1 (by rfl) ⟨7268102, by rfl⟩ : syracuseStep 9690803 = 14536205) B14536205
theorem B2268875 : Blo 1510952 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B2268887 : Blo 1510952 2268887 := bstep (se 1 (by rfl) ⟨1701665, by rfl⟩ : syracuseStep 2268887 = 3403331) B3403331
theorem B3063539 : Blo 1510952 3063539 := bstep (se 1 (by rfl) ⟨2297654, by rfl⟩ : syracuseStep 3063539 = 4595309) B4595309
theorem B1613579 : Blo 1510952 1613579 := bstep (se 1 (by rfl) ⟨1210184, by rfl⟩ : syracuseStep 1613579 = 2420369) B2420369
theorem B2268953 : Blo 1510952 2268953 := bstep (se 2 (by rfl) ⟨850857, by rfl⟩ : syracuseStep 2268953 = 1701715) B1701715
theorem B5521241 : Blo 1510952 5521241 := bstep (se 2 (by rfl) ⟨2070465, by rfl⟩ : syracuseStep 5521241 = 4140931) B4140931
theorem B14180189 : Blo 1510952 14180189 := bstep (se 3 (by rfl) ⟨2658785, by rfl⟩ : syracuseStep 14180189 = 5317571) B5317571
theorem B2269067 : Blo 1510952 2269067 := bstep (se 1 (by rfl) ⟨1701800, by rfl⟩ : syracuseStep 2269067 = 3403601) B3403601
theorem B2269079 : Blo 1510952 2269079 := bstep (se 1 (by rfl) ⟨1701809, by rfl⟩ : syracuseStep 2269079 = 3403619) B3403619
theorem B1531819 : Blo 1510952 1531819 := bstep (se 1 (by rfl) ⟨1148864, by rfl⟩ : syracuseStep 1531819 = 2297729) B2297729
theorem B5103539 : Blo 1510952 5103539 := bstep (se 1 (by rfl) ⟨3827654, by rfl⟩ : syracuseStep 5103539 = 7655309) B7655309
theorem B5742515 : Blo 1510952 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B2269145 : Blo 1510952 2269145 := bstep (se 2 (by rfl) ⟨850929, by rfl⟩ : syracuseStep 2269145 = 1701859) B1701859
theorem B3399695 : Blo 1510952 3399695 := bstep (se 1 (by rfl) ⟨2549771, by rfl⟩ : syracuseStep 3399695 = 5099543) B5099543
theorem B3227663 : Blo 1510952 3227663 := bstep (se 1 (by rfl) ⟨2420747, by rfl⟩ : syracuseStep 3227663 = 4841495) B4841495
theorem B2269199 : Blo 1510952 2269199 := bstep (se 1 (by rfl) ⟨1701899, by rfl⟩ : syracuseStep 2269199 = 3403799) B3403799
theorem B3399713 : Blo 1510952 3399713 := bstep (se 2 (by rfl) ⟨1274892, by rfl⟩ : syracuseStep 3399713 = 2549785) B2549785
theorem B2269241 : Blo 1510952 2269241 := bstep (se 2 (by rfl) ⟨850965, by rfl⟩ : syracuseStep 2269241 = 1701931) B1701931
theorem B3825751 : Blo 1510952 3825751 := bstep (se 1 (by rfl) ⟨2869313, by rfl⟩ : syracuseStep 3825751 = 5738627) B5738627
theorem B2269319 : Blo 1510952 2269319 := bstep (se 1 (by rfl) ⟨1701989, by rfl⟩ : syracuseStep 2269319 = 3403979) B3403979
theorem B2269355 : Blo 1510952 2269355 := bstep (se 1 (by rfl) ⟨1702016, by rfl⟩ : syracuseStep 2269355 = 3404033) B3404033
theorem B2269385 : Blo 1510952 2269385 := bstep (se 2 (by rfl) ⟨851019, by rfl⟩ : syracuseStep 2269385 = 1702039) B1702039
theorem B3400055 : Blo 1510952 3400055 := bstep (se 1 (by rfl) ⟨2550041, by rfl⟩ : syracuseStep 3400055 = 5100083) B5100083
theorem B3826055 : Blo 1510952 3826055 := bstep (se 1 (by rfl) ⟨2869541, by rfl⟩ : syracuseStep 3826055 = 5739083) B5739083
theorem B43614611 : Blo 1510952 43614611 := bstep (se 1 (by rfl) ⟨32710958, by rfl⟩ : syracuseStep 43614611 = 65421917) B65421917
theorem B5104025 : Blo 1510952 5104025 := bstep (se 2 (by rfl) ⟨1914009, by rfl⟩ : syracuseStep 5104025 = 3828019) B3828019
theorem B5743001 : Blo 1510952 5743001 := bstep (se 2 (by rfl) ⟨2153625, by rfl⟩ : syracuseStep 5743001 = 4307251) B4307251
theorem B3826187 : Blo 1510952 3826187 := bstep (se 1 (by rfl) ⟨2869640, by rfl⟩ : syracuseStep 3826187 = 5739281) B5739281
theorem B4088353 : Blo 1510952 4088353 := bstep (se 2 (by rfl) ⟨1533132, by rfl⟩ : syracuseStep 4088353 = 3066265) B3066265
theorem B3400235 : Blo 1510952 3400235 := bstep (se 1 (by rfl) ⟨2550176, by rfl⟩ : syracuseStep 3400235 = 5100353) B5100353
theorem B7651907 : Blo 1510952 7651907 := bstep (se 1 (by rfl) ⟨5738930, by rfl⟩ : syracuseStep 7651907 = 11477861) B11477861
theorem B7652231 : Blo 1510952 7652231 := bstep (se 1 (by rfl) ⟨5739173, by rfl⟩ : syracuseStep 7652231 = 11478347) B11478347
theorem B3400595 : Blo 1510952 3400595 := bstep (se 1 (by rfl) ⟨2550446, by rfl⟩ : syracuseStep 3400595 = 5100893) B5100893
theorem B3400649 : Blo 1510952 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B2761673 : Blo 1510952 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B3826703 : Blo 1510952 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B5104727 : Blo 1510952 5104727 := bstep (se 1 (by rfl) ⟨3828545, by rfl⟩ : syracuseStep 5104727 = 7657091) B7657091
theorem B70763653 : Blo 1510952 70763653 := bstep (se 4 (by rfl) ⟨6634092, by rfl⟩ : syracuseStep 70763653 = 13268185) B13268185
theorem B3826835 : Blo 1510952 3826835 := bstep (se 1 (by rfl) ⟨2870126, by rfl⟩ : syracuseStep 3826835 = 5740253) B5740253
theorem B8611109 : Blo 1510952 8611109 := bstep (se 4 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 8611109 = 1614583) B1614583
theorem B11486609 : Blo 1510952 11486609 := bstep (se 2 (by rfl) ⟨4307478, by rfl⟩ : syracuseStep 11486609 = 8614957) B8614957
theorem B34891193 : Blo 1510952 34891193 := bstep (se 2 (by rfl) ⟨13084197, by rfl⟩ : syracuseStep 34891193 = 26168395) B26168395
theorem B12920249 : Blo 1510952 12920249 := bstep (se 2 (by rfl) ⟨4845093, by rfl⟩ : syracuseStep 12920249 = 9690187) B9690187
theorem B52389305 : Blo 1510952 52389305 := bstep (se 2 (by rfl) ⟨19645989, by rfl⟩ : syracuseStep 52389305 = 39291979) B39291979
theorem B13788701 : Blo 1510952 13788701 := bstep (se 3 (by rfl) ⟨2585381, by rfl⟩ : syracuseStep 13788701 = 5170763) B5170763
theorem B5105213 : Blo 1510952 5105213 := bstep (se 3 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 5105213 = 1914455) B1914455
theorem B3229303 : Blo 1510952 3229303 := bstep (se 1 (by rfl) ⟨2421977, by rfl⟩ : syracuseStep 3229303 = 4843955) B4843955
theorem B3401351 : Blo 1510952 3401351 := bstep (se 1 (by rfl) ⟨2551013, by rfl⟩ : syracuseStep 3401351 = 5102027) B5102027
theorem B3630745 : Blo 1510952 3630745 := bstep (se 2 (by rfl) ⟨1361529, by rfl⟩ : syracuseStep 3630745 = 2723059) B2723059
theorem B6457103 : Blo 1510952 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B3065615 : Blo 1510952 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B14534437 : Blo 1510952 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B11478833 : Blo 1510952 11478833 := bstep (se 2 (by rfl) ⟨4304562, by rfl⟩ : syracuseStep 11478833 = 8609125) B8609125
theorem B3401531 : Blo 1510952 3401531 := bstep (se 1 (by rfl) ⟨2551148, by rfl⟩ : syracuseStep 3401531 = 5102297) B5102297
theorem B2869177 : Blo 1510952 2869177 := bstep (se 2 (by rfl) ⟨1075941, by rfl⟩ : syracuseStep 2869177 = 2151883) B2151883
theorem B3401657 : Blo 1510952 3401657 := bstep (se 2 (by rfl) ⟨1275621, by rfl⟩ : syracuseStep 3401657 = 2551243) B2551243
theorem B8169437 : Blo 1510952 8169437 := bstep (se 3 (by rfl) ⟨1531769, by rfl⟩ : syracuseStep 8169437 = 3063539) B3063539
theorem B4302877 : Blo 1510952 4302877 := bstep (se 3 (by rfl) ⟨806789, by rfl⟩ : syracuseStep 4302877 = 1613579) B1613579
theorem B4597793 : Blo 1510952 4597793 := bstep (se 2 (by rfl) ⟨1724172, by rfl⟩ : syracuseStep 4597793 = 3448345) B3448345
theorem B2549819 : Blo 1510952 2549819 := bstep (se 1 (by rfl) ⟨1912364, by rfl⟩ : syracuseStep 2549819 = 3824729) B3824729
theorem B10897541 : Blo 1510952 10897541 := bstep (se 4 (by rfl) ⟨1021644, by rfl⟩ : syracuseStep 10897541 = 2043289) B2043289
theorem B8612041 : Blo 1510952 8612041 := bstep (se 2 (by rfl) ⟨3229515, by rfl⟩ : syracuseStep 8612041 = 6459031) B6459031
theorem B14723309 : Blo 1510952 14723309 := bstep (se 3 (by rfl) ⟨2760620, by rfl⟩ : syracuseStep 14723309 = 5521241) B5521241
theorem B3827969 : Blo 1510952 3827969 := bstep (se 2 (by rfl) ⟨1435488, by rfl⟩ : syracuseStep 3827969 = 2870977) B2870977
theorem B2869519 : Blo 1510952 2869519 := bstep (se 1 (by rfl) ⟨2152139, by rfl⟩ : syracuseStep 2869519 = 4304279) B4304279
theorem B3401999 : Blo 1510952 3401999 := bstep (se 1 (by rfl) ⟨2551499, by rfl⟩ : syracuseStep 3401999 = 5102999) B5102999
theorem B3402017 : Blo 1510952 3402017 := bstep (se 2 (by rfl) ⟨1275756, by rfl⟩ : syracuseStep 3402017 = 2551513) B2551513
theorem B4303219 : Blo 1510952 4303219 := bstep (se 1 (by rfl) ⟨3227414, by rfl⟩ : syracuseStep 4303219 = 6454829) B6454829
theorem B2550217 : Blo 1510952 2550217 := bstep (se 2 (by rfl) ⟨956331, by rfl⟩ : syracuseStep 2550217 = 1912663) B1912663
theorem B2042425 : Blo 1510952 2042425 := bstep (se 2 (by rfl) ⟨765909, by rfl⟩ : syracuseStep 2042425 = 1531819) B1531819
theorem B3402359 : Blo 1510952 3402359 := bstep (se 1 (by rfl) ⟨2551769, by rfl⟩ : syracuseStep 3402359 = 5103539) B5103539
theorem B3828343 : Blo 1510952 3828343 := bstep (se 1 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 3828343 = 5742515) B5742515
theorem B7269065 : Blo 1510952 7269065 := bstep (se 2 (by rfl) ⟨2725899, by rfl⟩ : syracuseStep 7269065 = 5451799) B5451799
theorem B3402539 : Blo 1510952 3402539 := bstep (se 1 (by rfl) ⟨2551904, by rfl⟩ : syracuseStep 3402539 = 5103809) B5103809
theorem B17230643 : Blo 1510952 17230643 := bstep (se 1 (by rfl) ⟨12922982, by rfl⟩ : syracuseStep 17230643 = 25845965) B25845965
theorem B3066743 : Blo 1510952 3066743 := bstep (se 1 (by rfl) ⟨2300057, by rfl⟩ : syracuseStep 3066743 = 4600115) B4600115
theorem B5737351 : Blo 1510952 5737351 := bstep (se 1 (by rfl) ⟨4303013, by rfl⟩ : syracuseStep 5737351 = 8606027) B8606027
theorem B2042825 : Blo 1510952 2042825 := bstep (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) B1532119
theorem B3632129 : Blo 1510952 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B3828779 : Blo 1510952 3828779 := bstep (se 1 (by rfl) ⟨2871584, by rfl⟩ : syracuseStep 3828779 = 5743169) B5743169
theorem B6130775 : Blo 1510952 6130775 := bstep (se 1 (by rfl) ⟨4598081, by rfl⟩ : syracuseStep 6130775 = 9196163) B9196163
theorem B2550919 : Blo 1510952 2550919 := bstep (se 1 (by rfl) ⟨1913189, by rfl⟩ : syracuseStep 2550919 = 3826379) B3826379
theorem B2870407 : Blo 1510952 2870407 := bstep (se 1 (by rfl) ⟨2152805, by rfl⟩ : syracuseStep 2870407 = 4305611) B4305611
theorem B3402899 : Blo 1510952 3402899 := bstep (se 1 (by rfl) ⟨2552174, by rfl⟩ : syracuseStep 3402899 = 5104349) B5104349
theorem B2723017 : Blo 1510952 2723017 := bstep (se 2 (by rfl) ⟨1021131, by rfl⟩ : syracuseStep 2723017 = 2042263) B2042263
theorem B3402953 : Blo 1510952 3402953 := bstep (se 2 (by rfl) ⟨1276107, by rfl⟩ : syracuseStep 3402953 = 2552215) B2552215
theorem B3231019 : Blo 1510952 3231019 := bstep (se 1 (by rfl) ⟨2423264, by rfl⟩ : syracuseStep 3231019 = 4846529) B4846529
theorem B8728067 : Blo 1510952 8728067 := bstep (se 1 (by rfl) ⟨6546050, by rfl⟩ : syracuseStep 8728067 = 13092101) B13092101
theorem B1510971 : Blo 1510952 1510971 := bstep (se 1 (by rfl) ⟨1133228, by rfl⟩ : syracuseStep 1510971 = 2266457) B2266457
theorem B1511047 : Blo 1510952 1511047 := bstep (se 1 (by rfl) ⟨1133285, by rfl⟩ : syracuseStep 1511047 = 2266571) B2266571
theorem B1511055 : Blo 1510952 1511055 := bstep (se 1 (by rfl) ⟨1133291, by rfl⟩ : syracuseStep 1511055 = 2266583) B2266583
theorem B1511099 : Blo 1510952 1511099 := bstep (se 1 (by rfl) ⟨1133324, by rfl⟩ : syracuseStep 1511099 = 2266649) B2266649
theorem B1912567 : Blo 1510952 1912567 := bstep (se 1 (by rfl) ⟨1434425, by rfl⟩ : syracuseStep 1912567 = 2868851) B2868851
theorem B1511175 : Blo 1510952 1511175 := bstep (se 1 (by rfl) ⟨1133381, by rfl⟩ : syracuseStep 1511175 = 2266763) B2266763
theorem B1511183 : Blo 1510952 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B2551567 : Blo 1510952 2551567 := bstep (se 1 (by rfl) ⟨1913675, by rfl⟩ : syracuseStep 2551567 = 3827351) B3827351
theorem B1511227 : Blo 1510952 1511227 := bstep (se 1 (by rfl) ⟨1133420, by rfl⟩ : syracuseStep 1511227 = 2266841) B2266841
theorem B3829619 : Blo 1510952 3829619 := bstep (se 1 (by rfl) ⟨2872214, by rfl⟩ : syracuseStep 3829619 = 5744429) B5744429
theorem B1511303 : Blo 1510952 1511303 := bstep (se 1 (by rfl) ⟨1133477, by rfl⟩ : syracuseStep 1511303 = 2266955) B2266955
theorem B3403655 : Blo 1510952 3403655 := bstep (se 1 (by rfl) ⟨2552741, by rfl⟩ : syracuseStep 3403655 = 5105483) B5105483
theorem B3829639 : Blo 1510952 3829639 := bstep (se 1 (by rfl) ⟨2872229, by rfl⟩ : syracuseStep 3829639 = 5744459) B5744459
theorem B1511311 : Blo 1510952 1511311 := bstep (se 1 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 1511311 = 2266967) B2266967
theorem B4599737 : Blo 1510952 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B1511355 : Blo 1510952 1511355 := bstep (se 1 (by rfl) ⟨1133516, by rfl⟩ : syracuseStep 1511355 = 2267033) B2267033
theorem B1511431 : Blo 1510952 1511431 := bstep (se 1 (by rfl) ⟨1133573, by rfl⟩ : syracuseStep 1511431 = 2267147) B2267147
theorem B32714765 : Blo 1510952 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B1511439 : Blo 1510952 1511439 := bstep (se 1 (by rfl) ⟨1133579, by rfl⟩ : syracuseStep 1511439 = 2267159) B2267159
theorem B2420779 : Blo 1510952 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B4362299 : Blo 1510952 4362299 := bstep (se 1 (by rfl) ⟨3271724, by rfl⟩ : syracuseStep 4362299 = 6543449) B6543449
theorem B1912891 : Blo 1510952 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B1511483 : Blo 1510952 1511483 := bstep (se 1 (by rfl) ⟨1133612, by rfl⟩ : syracuseStep 1511483 = 2267225) B2267225
theorem B3403835 : Blo 1510952 3403835 := bstep (se 1 (by rfl) ⟨2552876, by rfl⟩ : syracuseStep 3403835 = 5105753) B5105753
theorem B1511559 : Blo 1510952 1511559 := bstep (se 1 (by rfl) ⟨1133669, by rfl⟩ : syracuseStep 1511559 = 2267339) B2267339
theorem B1511567 : Blo 1510952 1511567 := bstep (se 1 (by rfl) ⟨1133675, by rfl⟩ : syracuseStep 1511567 = 2267351) B2267351
theorem B1511611 : Blo 1510952 1511611 := bstep (se 1 (by rfl) ⟨1133708, by rfl⟩ : syracuseStep 1511611 = 2267417) B2267417
theorem B3403961 : Blo 1510952 3403961 := bstep (se 2 (by rfl) ⟨1276485, by rfl⟩ : syracuseStep 3403961 = 2552971) B2552971
theorem B6213833 : Blo 1510952 6213833 := bstep (se 2 (by rfl) ⟨2330187, by rfl⟩ : syracuseStep 6213833 = 4660375) B4660375
theorem B1511687 : Blo 1510952 1511687 := bstep (se 1 (by rfl) ⟨1133765, by rfl⟩ : syracuseStep 1511687 = 2267531) B2267531
theorem B1511695 : Blo 1510952 1511695 := bstep (se 1 (by rfl) ⟨1133771, by rfl⟩ : syracuseStep 1511695 = 2267543) B2267543
theorem B2552107 : Blo 1510952 2552107 := bstep (se 1 (by rfl) ⟨1914080, by rfl⟩ : syracuseStep 2552107 = 3828161) B3828161
theorem B1511739 : Blo 1510952 1511739 := bstep (se 1 (by rfl) ⟨1133804, by rfl⟩ : syracuseStep 1511739 = 2267609) B2267609
theorem B7655795 : Blo 1510952 7655795 := bstep (se 1 (by rfl) ⟨5741846, by rfl⟩ : syracuseStep 7655795 = 11483693) B11483693
theorem B1511815 : Blo 1510952 1511815 := bstep (se 1 (by rfl) ⟨1133861, by rfl⟩ : syracuseStep 1511815 = 2267723) B2267723
theorem B1700239 : Blo 1510952 1700239 := bstep (se 1 (by rfl) ⟨1275179, by rfl⟩ : syracuseStep 1700239 = 2550359) B2550359
theorem B1511823 : Blo 1510952 1511823 := bstep (se 1 (by rfl) ⟨1133867, by rfl⟩ : syracuseStep 1511823 = 2267735) B2267735
theorem B2552249 : Blo 1510952 2552249 := bstep (se 2 (by rfl) ⟨957093, by rfl⟩ : syracuseStep 2552249 = 1914187) B1914187
theorem B1511867 : Blo 1510952 1511867 := bstep (se 1 (by rfl) ⟨1133900, by rfl⟩ : syracuseStep 1511867 = 2267801) B2267801
theorem B8172035 : Blo 1510952 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B1511943 : Blo 1510952 1511943 := bstep (se 1 (by rfl) ⟨1133957, by rfl⟩ : syracuseStep 1511943 = 2267915) B2267915
theorem B1511951 : Blo 1510952 1511951 := bstep (se 1 (by rfl) ⟨1133963, by rfl⟩ : syracuseStep 1511951 = 2267927) B2267927
theorem B1511995 : Blo 1510952 1511995 := bstep (se 1 (by rfl) ⟨1133996, by rfl⟩ : syracuseStep 1511995 = 2267993) B2267993
theorem B1512071 : Blo 1510952 1512071 := bstep (se 1 (by rfl) ⟨1134053, by rfl⟩ : syracuseStep 1512071 = 2268107) B2268107
theorem B1512079 : Blo 1510952 1512079 := bstep (se 1 (by rfl) ⟨1134059, by rfl⟩ : syracuseStep 1512079 = 2268119) B2268119
theorem B1512123 : Blo 1510952 1512123 := bstep (se 1 (by rfl) ⟨1134092, by rfl⟩ : syracuseStep 1512123 = 2268185) B2268185
theorem B1512199 : Blo 1510952 1512199 := bstep (se 1 (by rfl) ⟨1134149, by rfl⟩ : syracuseStep 1512199 = 2268299) B2268299
theorem B1512207 : Blo 1510952 1512207 := bstep (se 1 (by rfl) ⟨1134155, by rfl⟩ : syracuseStep 1512207 = 2268311) B2268311
theorem B4846351 : Blo 1510952 4846351 := bstep (se 1 (by rfl) ⟨3634763, by rfl⟩ : syracuseStep 4846351 = 7269527) B7269527
theorem B1512251 : Blo 1510952 1512251 := bstep (se 1 (by rfl) ⟨1134188, by rfl⟩ : syracuseStep 1512251 = 2268377) B2268377
theorem B7656281 : Blo 1510952 7656281 := bstep (se 2 (by rfl) ⟨2871105, by rfl⟩ : syracuseStep 7656281 = 5742211) B5742211
theorem B1700743 : Blo 1510952 1700743 := bstep (se 1 (by rfl) ⟨1275557, by rfl⟩ : syracuseStep 1700743 = 2551115) B2551115
theorem B1512327 : Blo 1510952 1512327 := bstep (se 1 (by rfl) ⟨1134245, by rfl⟩ : syracuseStep 1512327 = 2268491) B2268491
theorem B2872199 : Blo 1510952 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1512335 : Blo 1510952 1512335 := bstep (se 1 (by rfl) ⟨1134251, by rfl⟩ : syracuseStep 1512335 = 2268503) B2268503
theorem B1512379 : Blo 1510952 1512379 := bstep (se 1 (by rfl) ⟨1134284, by rfl⟩ : syracuseStep 1512379 = 2268569) B2268569
theorem B1913863 : Blo 1510952 1913863 := bstep (se 1 (by rfl) ⟨1435397, by rfl⟩ : syracuseStep 1913863 = 2870795) B2870795
theorem B1512455 : Blo 1510952 1512455 := bstep (se 1 (by rfl) ⟨1134341, by rfl⟩ : syracuseStep 1512455 = 2268683) B2268683
theorem B1512463 : Blo 1510952 1512463 := bstep (se 1 (by rfl) ⟨1134347, by rfl⟩ : syracuseStep 1512463 = 2268695) B2268695
theorem B4305953 : Blo 1510952 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B1700923 : Blo 1510952 1700923 := bstep (se 1 (by rfl) ⟨1275692, by rfl⟩ : syracuseStep 1700923 = 2551385) B2551385
theorem B1512507 : Blo 1510952 1512507 := bstep (se 1 (by rfl) ⟨1134380, by rfl⟩ : syracuseStep 1512507 = 2268761) B2268761
theorem B6460535 : Blo 1510952 6460535 := bstep (se 1 (by rfl) ⟨4845401, by rfl⟩ : syracuseStep 6460535 = 9690803) B9690803
theorem B2552951 : Blo 1510952 2552951 := bstep (se 1 (by rfl) ⟨1914713, by rfl⟩ : syracuseStep 2552951 = 3829427) B3829427
theorem B1512583 : Blo 1510952 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B1512591 : Blo 1510952 1512591 := bstep (se 1 (by rfl) ⟨1134443, by rfl⟩ : syracuseStep 1512591 = 2268887) B2268887
theorem B4306067 : Blo 1510952 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B1512635 : Blo 1510952 1512635 := bstep (se 1 (by rfl) ⟨1134476, by rfl⟩ : syracuseStep 1512635 = 2268953) B2268953
theorem B1815815 : Blo 1510952 1815815 := bstep (se 1 (by rfl) ⟨1361861, by rfl⟩ : syracuseStep 1815815 = 2723723) B2723723
theorem B1512711 : Blo 1510952 1512711 := bstep (se 1 (by rfl) ⟨1134533, by rfl⟩ : syracuseStep 1512711 = 2269067) B2269067
theorem B1512719 : Blo 1510952 1512719 := bstep (se 1 (by rfl) ⟨1134539, by rfl⟩ : syracuseStep 1512719 = 2269079) B2269079
theorem B1635643 : Blo 1510952 1635643 := bstep (se 1 (by rfl) ⟨1226732, by rfl⟩ : syracuseStep 1635643 = 2453465) B2453465
theorem B1512763 : Blo 1510952 1512763 := bstep (se 1 (by rfl) ⟨1134572, by rfl⟩ : syracuseStep 1512763 = 2269145) B2269145
theorem B2266487 : Blo 1510952 2266487 := bstep (se 1 (by rfl) ⟨1699865, by rfl⟩ : syracuseStep 2266487 = 3399731) B3399731
theorem B1512839 : Blo 1510952 1512839 := bstep (se 1 (by rfl) ⟨1134629, by rfl⟩ : syracuseStep 1512839 = 2269259) B2269259
theorem B2266511 : Blo 1510952 2266511 := bstep (se 1 (by rfl) ⟨1699883, by rfl⟩ : syracuseStep 2266511 = 3399767) B3399767
theorem B2299279 : Blo 1510952 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B1512847 : Blo 1510952 1512847 := bstep (se 1 (by rfl) ⟨1134635, by rfl⟩ : syracuseStep 1512847 = 2269271) B2269271
theorem B5100947 : Blo 1510952 5100947 := bstep (se 1 (by rfl) ⟨3825710, by rfl⟩ : syracuseStep 5100947 = 7651421) B7651421
theorem B1914283 : Blo 1510952 1914283 := bstep (se 1 (by rfl) ⟨1435712, by rfl⟩ : syracuseStep 1914283 = 2871425) B2871425
theorem B2266553 : Blo 1510952 2266553 := bstep (se 2 (by rfl) ⟨849957, by rfl⟩ : syracuseStep 2266553 = 1699915) B1699915
theorem B1512891 : Blo 1510952 1512891 := bstep (se 1 (by rfl) ⟨1134668, by rfl⟩ : syracuseStep 1512891 = 2269337) B2269337
theorem B18388433 : Blo 1510952 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B2266631 : Blo 1510952 2266631 := bstep (se 1 (by rfl) ⟨1699973, by rfl⟩ : syracuseStep 2266631 = 3399947) B3399947
theorem B1701391 : Blo 1510952 1701391 := bstep (se 1 (by rfl) ⟨1276043, by rfl⟩ : syracuseStep 1701391 = 2552087) B2552087
theorem B2266667 : Blo 1510952 2266667 := bstep (se 1 (by rfl) ⟨1700000, by rfl⟩ : syracuseStep 2266667 = 3400001) B3400001
theorem B1816123 : Blo 1510952 1816123 := bstep (se 1 (by rfl) ⟨1362092, by rfl⟩ : syracuseStep 1816123 = 2724185) B2724185
theorem B2266697 : Blo 1510952 2266697 := bstep (se 2 (by rfl) ⟨850011, by rfl⟩ : syracuseStep 2266697 = 1700023) B1700023
theorem B1914511 : Blo 1510952 1914511 := bstep (se 1 (by rfl) ⟨1435883, by rfl⟩ : syracuseStep 1914511 = 2871767) B2871767
theorem B53106353 : Blo 1510952 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B2266811 : Blo 1510952 2266811 := bstep (se 1 (by rfl) ⟨1700108, by rfl⟩ : syracuseStep 2266811 = 3400217) B3400217
theorem B9688805 : Blo 1510952 9688805 := bstep (se 4 (by rfl) ⟨908325, by rfl⟩ : syracuseStep 9688805 = 1816651) B1816651
theorem B2266871 : Blo 1510952 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B2266895 : Blo 1510952 2266895 := bstep (se 1 (by rfl) ⟨1700171, by rfl⟩ : syracuseStep 2266895 = 3400343) B3400343
theorem B13793075 : Blo 1510952 13793075 := bstep (se 1 (by rfl) ⟨10344806, by rfl⟩ : syracuseStep 13793075 = 20689613) B20689613
theorem B2266937 : Blo 1510952 2266937 := bstep (se 2 (by rfl) ⟨850101, by rfl⟩ : syracuseStep 2266937 = 1700203) B1700203
theorem B3192635 : Blo 1510952 3192635 := bstep (se 1 (by rfl) ⟨2394476, by rfl⟩ : syracuseStep 3192635 = 4788953) B4788953
theorem B2267015 : Blo 1510952 2267015 := bstep (se 1 (by rfl) ⟨1700261, by rfl⟩ : syracuseStep 2267015 = 3400523) B3400523
theorem B2152327 : Blo 1510952 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B4306841 : Blo 1510952 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B2267051 : Blo 1510952 2267051 := bstep (se 1 (by rfl) ⟨1700288, by rfl⟩ : syracuseStep 2267051 = 3400577) B3400577
theorem B1816507 : Blo 1510952 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B2267081 : Blo 1510952 2267081 := bstep (se 2 (by rfl) ⟨850155, by rfl⟩ : syracuseStep 2267081 = 1700311) B1700311
theorem B1701895 : Blo 1510952 1701895 := bstep (se 1 (by rfl) ⟨1276421, by rfl⟩ : syracuseStep 1701895 = 2552843) B2552843
theorem B2267195 : Blo 1510952 2267195 := bstep (se 1 (by rfl) ⟨1700396, by rfl⟩ : syracuseStep 2267195 = 3400793) B3400793
theorem B82810997 : Blo 1510952 82810997 := bstep (se 5 (by rfl) ⟨3881765, by rfl⟩ : syracuseStep 82810997 = 7763531) B7763531
theorem B2267255 : Blo 1510952 2267255 := bstep (se 1 (by rfl) ⟨1700441, by rfl⟩ : syracuseStep 2267255 = 3400883) B3400883
theorem B2422919 : Blo 1510952 2422919 := bstep (se 1 (by rfl) ⟨1817189, by rfl⟩ : syracuseStep 2422919 = 3634379) B3634379
theorem B2267279 : Blo 1510952 2267279 := bstep (se 1 (by rfl) ⟨1700459, by rfl⟩ : syracuseStep 2267279 = 3400919) B3400919
theorem B17701037 : Blo 1510952 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B2267321 : Blo 1510952 2267321 := bstep (se 2 (by rfl) ⟨850245, by rfl⟩ : syracuseStep 2267321 = 1700491) B1700491
theorem B2267399 : Blo 1510952 2267399 := bstep (se 1 (by rfl) ⟨1700549, by rfl⟩ : syracuseStep 2267399 = 3401099) B3401099
theorem B2267435 : Blo 1510952 2267435 := bstep (se 1 (by rfl) ⟨1700576, by rfl⟩ : syracuseStep 2267435 = 3401153) B3401153
theorem B2267465 : Blo 1510952 2267465 := bstep (se 2 (by rfl) ⟨850299, by rfl⟩ : syracuseStep 2267465 = 1700599) B1700599
theorem B29047187 : Blo 1510952 29047187 := bstep (se 1 (by rfl) ⟨21785390, by rfl⟩ : syracuseStep 29047187 = 43570781) B43570781
theorem B130734485 : Blo 1510952 130734485 := bstep (se 6 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 130734485 = 6128179) B6128179
theorem B2267579 : Blo 1510952 2267579 := bstep (se 1 (by rfl) ⟨1700684, by rfl⟩ : syracuseStep 2267579 = 3401369) B3401369
theorem B2267639 : Blo 1510952 2267639 := bstep (se 1 (by rfl) ⟨1700729, by rfl⟩ : syracuseStep 2267639 = 3401459) B3401459
theorem B2267663 : Blo 1510952 2267663 := bstep (se 1 (by rfl) ⟨1700747, by rfl⟩ : syracuseStep 2267663 = 3401495) B3401495
theorem B17226269 : Blo 1510952 17226269 := bstep (se 3 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 17226269 = 6459851) B6459851
theorem B2267705 : Blo 1510952 2267705 := bstep (se 2 (by rfl) ⟨850389, by rfl⟩ : syracuseStep 2267705 = 1700779) B1700779
theorem B2267783 : Blo 1510952 2267783 := bstep (se 1 (by rfl) ⟨1700837, by rfl⟩ : syracuseStep 2267783 = 3401675) B3401675
theorem B2267819 : Blo 1510952 2267819 := bstep (se 1 (by rfl) ⟨1700864, by rfl⟩ : syracuseStep 2267819 = 3401729) B3401729
theorem B2153147 : Blo 1510952 2153147 := bstep (se 1 (by rfl) ⟨1614860, by rfl⟩ : syracuseStep 2153147 = 3229721) B3229721
theorem B2267849 : Blo 1510952 2267849 := bstep (se 2 (by rfl) ⟨850443, by rfl⟩ : syracuseStep 2267849 = 1700887) B1700887
theorem B14523137 : Blo 1510952 14523137 := bstep (se 2 (by rfl) ⟨5446176, by rfl⟩ : syracuseStep 14523137 = 10892353) B10892353
theorem B5102351 : Blo 1510952 5102351 := bstep (se 1 (by rfl) ⟨3826763, by rfl⟩ : syracuseStep 5102351 = 7653527) B7653527
theorem B2267963 : Blo 1510952 2267963 := bstep (se 1 (by rfl) ⟨1700972, by rfl⟩ : syracuseStep 2267963 = 3401945) B3401945
theorem B2268023 : Blo 1510952 2268023 := bstep (se 1 (by rfl) ⟨1701017, by rfl⟩ : syracuseStep 2268023 = 3402035) B3402035
theorem B2268047 : Blo 1510952 2268047 := bstep (se 1 (by rfl) ⟨1701035, by rfl⟩ : syracuseStep 2268047 = 3402071) B3402071
theorem B7658387 : Blo 1510952 7658387 := bstep (se 1 (by rfl) ⟨5743790, by rfl⟩ : syracuseStep 7658387 = 11487581) B11487581
theorem B16350115 : Blo 1510952 16350115 := bstep (se 1 (by rfl) ⟨12262586, by rfl⟩ : syracuseStep 16350115 = 24525173) B24525173
theorem B29047733 : Blo 1510952 29047733 := bstep (se 5 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 29047733 = 2723225) B2723225
theorem B2268089 : Blo 1510952 2268089 := bstep (se 2 (by rfl) ⟨850533, by rfl⟩ : syracuseStep 2268089 = 1701067) B1701067
theorem B2268167 : Blo 1510952 2268167 := bstep (se 1 (by rfl) ⟨1701125, by rfl⟩ : syracuseStep 2268167 = 3402251) B3402251
theorem B5102621 : Blo 1510952 5102621 := bstep (se 3 (by rfl) ⟨956741, by rfl⟩ : syracuseStep 5102621 = 1913483) B1913483
theorem B7756843 : Blo 1510952 7756843 := bstep (se 1 (by rfl) ⟨5817632, by rfl⟩ : syracuseStep 7756843 = 11635265) B11635265
theorem B3447851 : Blo 1510952 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B2268203 : Blo 1510952 2268203 := bstep (se 1 (by rfl) ⟨1701152, by rfl⟩ : syracuseStep 2268203 = 3402305) B3402305
theorem B2268233 : Blo 1510952 2268233 := bstep (se 2 (by rfl) ⟨850587, by rfl⟩ : syracuseStep 2268233 = 1701175) B1701175
theorem B3824759 : Blo 1510952 3824759 := bstep (se 1 (by rfl) ⟨2868569, by rfl⟩ : syracuseStep 3824759 = 5737139) B5737139
theorem B2948231 : Blo 1510952 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B2268347 : Blo 1510952 2268347 := bstep (se 1 (by rfl) ⟨1701260, by rfl⟩ : syracuseStep 2268347 = 3402521) B3402521
theorem B2268407 : Blo 1510952 2268407 := bstep (se 1 (by rfl) ⟨1701305, by rfl⟩ : syracuseStep 2268407 = 3402611) B3402611
theorem B2268431 : Blo 1510952 2268431 := bstep (se 1 (by rfl) ⟨1701323, by rfl⟩ : syracuseStep 2268431 = 3402647) B3402647
theorem B2948395 : Blo 1510952 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B7650611 : Blo 1510952 7650611 := bstep (se 1 (by rfl) ⟨5737958, by rfl⟩ : syracuseStep 7650611 = 11475917) B11475917
theorem B2268473 : Blo 1510952 2268473 := bstep (se 2 (by rfl) ⟨850677, by rfl⟩ : syracuseStep 2268473 = 1701355) B1701355
theorem B2153785 : Blo 1510952 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B2268551 : Blo 1510952 2268551 := bstep (se 1 (by rfl) ⟨1701413, by rfl⟩ : syracuseStep 2268551 = 3402827) B3402827
theorem B2268587 : Blo 1510952 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B2153899 : Blo 1510952 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B2268617 : Blo 1510952 2268617 := bstep (se 2 (by rfl) ⟨850731, by rfl⟩ : syracuseStep 2268617 = 1701463) B1701463
theorem B17456593 : Blo 1510952 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B9199133 : Blo 1510952 9199133 := bstep (se 3 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 9199133 = 3449675) B3449675
theorem B2268731 : Blo 1510952 2268731 := bstep (se 1 (by rfl) ⟨1701548, by rfl⟩ : syracuseStep 2268731 = 3403097) B3403097
theorem B37813837 : Blo 1510952 37813837 := bstep (se 3 (by rfl) ⟨7090094, by rfl⟩ : syracuseStep 37813837 = 14180189) B14180189
theorem B7650935 : Blo 1510952 7650935 := bstep (se 1 (by rfl) ⟨5738201, by rfl⟩ : syracuseStep 7650935 = 11476403) B11476403
theorem B8609399 : Blo 1510952 8609399 := bstep (se 1 (by rfl) ⟨6457049, by rfl⟩ : syracuseStep 8609399 = 12914099) B12914099
theorem B11640439 : Blo 1510952 11640439 := bstep (se 1 (by rfl) ⟨8730329, by rfl⟩ : syracuseStep 11640439 = 17460659) B17460659
theorem B2268791 : Blo 1510952 2268791 := bstep (se 1 (by rfl) ⟨1701593, by rfl⟩ : syracuseStep 2268791 = 3403187) B3403187
theorem B2268815 : Blo 1510952 2268815 := bstep (se 1 (by rfl) ⟨1701611, by rfl⟩ : syracuseStep 2268815 = 3403223) B3403223
theorem B2154127 : Blo 1510952 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B9199277 : Blo 1510952 9199277 := bstep (se 3 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 9199277 = 3449729) B3449729
theorem B2268857 : Blo 1510952 2268857 := bstep (se 2 (by rfl) ⟨850821, by rfl⟩ : syracuseStep 2268857 = 1701643) B1701643
theorem B2268935 : Blo 1510952 2268935 := bstep (se 1 (by rfl) ⟨1701701, by rfl⟩ : syracuseStep 2268935 = 3403403) B3403403
theorem B2268971 : Blo 1510952 2268971 := bstep (se 1 (by rfl) ⟨1701728, by rfl⟩ : syracuseStep 2268971 = 3403457) B3403457
theorem B2269001 : Blo 1510952 2269001 := bstep (se 2 (by rfl) ⟨850875, by rfl⟩ : syracuseStep 2269001 = 1701751) B1701751
theorem B8609651 : Blo 1510952 8609651 := bstep (se 1 (by rfl) ⟨6457238, by rfl⟩ : syracuseStep 8609651 = 12914477) B12914477
theorem B74522521 : Blo 1510952 74522521 := bstep (se 2 (by rfl) ⟨27945945, by rfl⟩ : syracuseStep 74522521 = 55891891) B55891891
theorem B11476889 : Blo 1510952 11476889 := bstep (se 2 (by rfl) ⟨4303833, by rfl⟩ : syracuseStep 11476889 = 8607667) B8607667
theorem B2269115 : Blo 1510952 2269115 := bstep (se 1 (by rfl) ⟨1701836, by rfl⟩ : syracuseStep 2269115 = 3403673) B3403673
theorem B7266257 : Blo 1510952 7266257 := bstep (se 2 (by rfl) ⟨2724846, by rfl⟩ : syracuseStep 7266257 = 5449693) B5449693
theorem B2269175 : Blo 1510952 2269175 := bstep (se 1 (by rfl) ⟨1701881, by rfl⟩ : syracuseStep 2269175 = 3403763) B3403763
theorem B2269193 : Blo 1510952 2269193 := bstep (se 2 (by rfl) ⟨850947, by rfl⟩ : syracuseStep 2269193 = 1701895) B1701895
theorem B2269223 : Blo 1510952 2269223 := bstep (se 1 (by rfl) ⟨1701917, by rfl⟩ : syracuseStep 2269223 = 3403835) B3403835
theorem B3227705 : Blo 1510952 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B2269307 : Blo 1510952 2269307 := bstep (se 1 (by rfl) ⟨1701980, by rfl⟩ : syracuseStep 2269307 = 3403961) B3403961
theorem B5103863 : Blo 1510952 5103863 := bstep (se 1 (by rfl) ⟨3827897, by rfl⟩ : syracuseStep 5103863 = 7655795) B7655795
theorem B5448023 : Blo 1510952 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B3826025 : Blo 1510952 3826025 := bstep (se 2 (by rfl) ⟨1434759, by rfl⟩ : syracuseStep 3826025 = 2869519) B2869519
theorem B5104187 : Blo 1510952 5104187 := bstep (se 1 (by rfl) ⟨3828140, by rfl⟩ : syracuseStep 5104187 = 7656281) B7656281
theorem B3400289 : Blo 1510952 3400289 := bstep (se 2 (by rfl) ⟨1275108, by rfl⟩ : syracuseStep 3400289 = 2550217) B2550217
theorem B46531189 : Blo 1510952 46531189 := bstep (se 5 (by rfl) ⟨2181149, by rfl⟩ : syracuseStep 46531189 = 4362299) B4362299
theorem B4842173 : Blo 1510952 4842173 := bstep (se 3 (by rfl) ⟨907907, by rfl⟩ : syracuseStep 4842173 = 1815815) B1815815
theorem B5104457 : Blo 1510952 5104457 := bstep (se 2 (by rfl) ⟨1914171, by rfl⟩ : syracuseStep 5104457 = 3828343) B3828343
theorem B3400631 : Blo 1510952 3400631 := bstep (se 1 (by rfl) ⟨2550473, by rfl⟩ : syracuseStep 3400631 = 5100947) B5100947
theorem B9192467 : Blo 1510952 9192467 := bstep (se 1 (by rfl) ⟨6894350, by rfl⟩ : syracuseStep 9192467 = 13788701) B13788701
theorem B7652555 : Blo 1510952 7652555 := bstep (se 1 (by rfl) ⟨5739416, by rfl⟩ : syracuseStep 7652555 = 11478833) B11478833
theorem B21800153 : Blo 1510952 21800153 := bstep (se 2 (by rfl) ⟨8175057, by rfl⟩ : syracuseStep 21800153 = 16350115) B16350115
theorem B3065195 : Blo 1510952 3065195 := bstep (se 1 (by rfl) ⟨2298896, by rfl⟩ : syracuseStep 3065195 = 4597793) B4597793
theorem B55207331 : Blo 1510952 55207331 := bstep (se 1 (by rfl) ⟨41405498, by rfl⟩ : syracuseStep 55207331 = 82810997) B82810997
theorem B9815539 : Blo 1510952 9815539 := bstep (se 1 (by rfl) ⟨7361654, by rfl⟩ : syracuseStep 9815539 = 14723309) B14723309
theorem B3401225 : Blo 1510952 3401225 := bstep (se 2 (by rfl) ⟨1275459, by rfl⟩ : syracuseStep 3401225 = 2550919) B2550919
theorem B3827209 : Blo 1510952 3827209 := bstep (se 2 (by rfl) ⟨1435203, by rfl⟩ : syracuseStep 3827209 = 2870407) B2870407
theorem B3630689 : Blo 1510952 3630689 := bstep (se 2 (by rfl) ⟨1361508, by rfl⟩ : syracuseStep 3630689 = 2723017) B2723017
theorem B87156323 : Blo 1510952 87156323 := bstep (se 1 (by rfl) ⟨65367242, by rfl⟩ : syracuseStep 87156323 = 130734485) B130734485
theorem B2180857 : Blo 1510952 2180857 := bstep (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) B1635643
theorem B3401567 : Blo 1510952 3401567 := bstep (se 1 (by rfl) ⟨2551175, by rfl⟩ : syracuseStep 3401567 = 5102351) B5102351
theorem B3065705 : Blo 1510952 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B11487095 : Blo 1510952 11487095 := bstep (se 1 (by rfl) ⟨8615321, by rfl⟩ : syracuseStep 11487095 = 17230643) B17230643
theorem B5105591 : Blo 1510952 5105591 := bstep (se 1 (by rfl) ⟨3829193, by rfl⟩ : syracuseStep 5105591 = 7658387) B7658387
theorem B23275457 : Blo 1510952 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B3401747 : Blo 1510952 3401747 := bstep (se 1 (by rfl) ⟨2551310, by rfl⟩ : syracuseStep 3401747 = 5102621) B5102621
theorem B2549839 : Blo 1510952 2549839 := bstep (se 1 (by rfl) ⟨1912379, by rfl⟩ : syracuseStep 2549839 = 3824759) B3824759
theorem B2550089 : Blo 1510952 2550089 := bstep (se 2 (by rfl) ⟨956283, by rfl⟩ : syracuseStep 2550089 = 1912567) B1912567
theorem B5818711 : Blo 1510952 5818711 := bstep (se 1 (by rfl) ⟨4364033, by rfl⟩ : syracuseStep 5818711 = 8728067) B8728067
theorem B3402089 : Blo 1510952 3402089 := bstep (se 2 (by rfl) ⟨1275783, by rfl⟩ : syracuseStep 3402089 = 2551567) B2551567
theorem B2869769 : Blo 1510952 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B5106185 : Blo 1510952 5106185 := bstep (se 2 (by rfl) ⟨1914819, by rfl⟩ : syracuseStep 5106185 = 3829639) B3829639
theorem B99363361 : Blo 1510952 99363361 := bstep (se 2 (by rfl) ⟨37261260, by rfl⟩ : syracuseStep 99363361 = 74522521) B74522521
theorem B3066491 : Blo 1510952 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B4844171 : Blo 1510952 4844171 := bstep (se 1 (by rfl) ⟨3633128, by rfl⟩ : syracuseStep 4844171 = 7266257) B7266257
theorem B21809843 : Blo 1510952 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B5737169 : Blo 1510952 5737169 := bstep (se 2 (by rfl) ⟨2151438, by rfl⟩ : syracuseStep 5737169 = 4302877) B4302877
theorem B2550521 : Blo 1510952 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B9194269 : Blo 1510952 9194269 := bstep (se 3 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 9194269 = 3447851) B3447851
theorem B2550703 : Blo 1510952 2550703 := bstep (se 1 (by rfl) ⟨1913027, by rfl⟩ : syracuseStep 2550703 = 3826055) B3826055
theorem B29076407 : Blo 1510952 29076407 := bstep (se 1 (by rfl) ⟨21807305, by rfl⟩ : syracuseStep 29076407 = 43614611) B43614611
theorem B3402683 : Blo 1510952 3402683 := bstep (se 1 (by rfl) ⟨2552012, by rfl⟩ : syracuseStep 3402683 = 5104025) B5104025
theorem B3828667 : Blo 1510952 3828667 := bstep (se 1 (by rfl) ⟨2871500, by rfl⟩ : syracuseStep 3828667 = 5743001) B5743001
theorem B2550791 : Blo 1510952 2550791 := bstep (se 1 (by rfl) ⟨1913093, by rfl⟩ : syracuseStep 2550791 = 3826187) B3826187
theorem B3402809 : Blo 1510952 3402809 := bstep (se 2 (by rfl) ⟨1276053, by rfl⟩ : syracuseStep 3402809 = 2552107) B2552107
theorem B5737625 : Blo 1510952 5737625 := bstep (se 2 (by rfl) ⟨2151609, by rfl⟩ : syracuseStep 5737625 = 4303219) B4303219
theorem B2551135 : Blo 1510952 2551135 := bstep (se 1 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 2551135 = 3826703) B3826703
theorem B2870635 : Blo 1510952 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B5451137 : Blo 1510952 5451137 := bstep (se 2 (by rfl) ⟨2044176, by rfl⟩ : syracuseStep 5451137 = 4088353) B4088353
theorem B3403151 : Blo 1510952 3403151 := bstep (se 1 (by rfl) ⟨2552363, by rfl⟩ : syracuseStep 3403151 = 5104727) B5104727
theorem B2723233 : Blo 1510952 2723233 := bstep (se 2 (by rfl) ⟨1021212, by rfl⟩ : syracuseStep 2723233 = 2042425) B2042425
theorem B2551223 : Blo 1510952 2551223 := bstep (se 1 (by rfl) ⟨1913417, by rfl⟩ : syracuseStep 2551223 = 3826835) B3826835
theorem B2870711 : Blo 1510952 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1510991 : Blo 1510952 1510991 := bstep (se 1 (by rfl) ⟨1133243, by rfl⟩ : syracuseStep 1510991 = 2266487) B2266487
theorem B1511007 : Blo 1510952 1511007 := bstep (se 1 (by rfl) ⟨1133255, by rfl⟩ : syracuseStep 1511007 = 2266511) B2266511
theorem B1511035 : Blo 1510952 1511035 := bstep (se 1 (by rfl) ⟨1133276, by rfl⟩ : syracuseStep 1511035 = 2266553) B2266553
theorem B8613499 : Blo 1510952 8613499 := bstep (se 1 (by rfl) ⟨6460124, by rfl⟩ : syracuseStep 8613499 = 12920249) B12920249
theorem B34926203 : Blo 1510952 34926203 := bstep (se 1 (by rfl) ⟨26194652, by rfl⟩ : syracuseStep 34926203 = 52389305) B52389305
theorem B12258955 : Blo 1510952 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B1511087 : Blo 1510952 1511087 := bstep (se 1 (by rfl) ⟨1133315, by rfl⟩ : syracuseStep 1511087 = 2266631) B2266631
theorem B1511111 : Blo 1510952 1511111 := bstep (se 1 (by rfl) ⟨1133333, by rfl⟩ : syracuseStep 1511111 = 2266667) B2266667
theorem B3403475 : Blo 1510952 3403475 := bstep (se 1 (by rfl) ⟨2552606, by rfl⟩ : syracuseStep 3403475 = 5105213) B5105213
theorem B1511131 : Blo 1510952 1511131 := bstep (se 1 (by rfl) ⟨1133348, by rfl⟩ : syracuseStep 1511131 = 2266697) B2266697
theorem B1511207 : Blo 1510952 1511207 := bstep (se 1 (by rfl) ⟨1133405, by rfl⟩ : syracuseStep 1511207 = 2266811) B2266811
theorem B6459203 : Blo 1510952 6459203 := bstep (se 1 (by rfl) ⟨4844402, by rfl⟩ : syracuseStep 6459203 = 9688805) B9688805
theorem B1511247 : Blo 1510952 1511247 := bstep (se 1 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 1511247 = 2266871) B2266871
theorem B1511263 : Blo 1510952 1511263 := bstep (se 1 (by rfl) ⟨1133447, by rfl⟩ : syracuseStep 1511263 = 2266895) B2266895
theorem B4304735 : Blo 1510952 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B2043743 : Blo 1510952 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B9195383 : Blo 1510952 9195383 := bstep (se 1 (by rfl) ⟨6896537, by rfl⟩ : syracuseStep 9195383 = 13793075) B13793075
theorem B1511291 : Blo 1510952 1511291 := bstep (se 1 (by rfl) ⟨1133468, by rfl⟩ : syracuseStep 1511291 = 2266937) B2266937
theorem B1511343 : Blo 1510952 1511343 := bstep (se 1 (by rfl) ⟨1133507, by rfl⟩ : syracuseStep 1511343 = 2267015) B2267015
theorem B2871227 : Blo 1510952 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B1511367 : Blo 1510952 1511367 := bstep (se 1 (by rfl) ⟨1133525, by rfl⟩ : syracuseStep 1511367 = 2267051) B2267051
theorem B1511387 : Blo 1510952 1511387 := bstep (se 1 (by rfl) ⟨1133540, by rfl⟩ : syracuseStep 1511387 = 2267081) B2267081
theorem B2551817 : Blo 1510952 2551817 := bstep (se 2 (by rfl) ⟨956931, by rfl⟩ : syracuseStep 2551817 = 1913863) B1913863
theorem B1699879 : Blo 1510952 1699879 := bstep (se 1 (by rfl) ⟨1274909, by rfl⟩ : syracuseStep 1699879 = 2549819) B2549819
theorem B1511463 : Blo 1510952 1511463 := bstep (se 1 (by rfl) ⟨1133597, by rfl⟩ : syracuseStep 1511463 = 2267195) B2267195
theorem B10342457 : Blo 1510952 10342457 := bstep (se 2 (by rfl) ⟨3878421, by rfl⟩ : syracuseStep 10342457 = 7756843) B7756843
theorem B1511503 : Blo 1510952 1511503 := bstep (se 1 (by rfl) ⟨1133627, by rfl⟩ : syracuseStep 1511503 = 2267255) B2267255
theorem B1511519 : Blo 1510952 1511519 := bstep (se 1 (by rfl) ⟨1133639, by rfl⟩ : syracuseStep 1511519 = 2267279) B2267279
theorem B11800691 : Blo 1510952 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B1511547 : Blo 1510952 1511547 := bstep (se 1 (by rfl) ⟨1133660, by rfl⟩ : syracuseStep 1511547 = 2267321) B2267321
theorem B2551979 : Blo 1510952 2551979 := bstep (se 1 (by rfl) ⟨1913984, by rfl⟩ : syracuseStep 2551979 = 3827969) B3827969
theorem B1511599 : Blo 1510952 1511599 := bstep (se 1 (by rfl) ⟨1133699, by rfl⟩ : syracuseStep 1511599 = 2267399) B2267399
theorem B94351537 : Blo 1510952 94351537 := bstep (se 2 (by rfl) ⟨35381826, by rfl⟩ : syracuseStep 94351537 = 70763653) B70763653
theorem B1511623 : Blo 1510952 1511623 := bstep (se 1 (by rfl) ⟨1133717, by rfl⟩ : syracuseStep 1511623 = 2267435) B2267435
theorem B1511643 : Blo 1510952 1511643 := bstep (se 1 (by rfl) ⟨1133732, by rfl⟩ : syracuseStep 1511643 = 2267465) B2267465
theorem B17232101 : Blo 1510952 17232101 := bstep (se 4 (by rfl) ⟨1615509, by rfl⟩ : syracuseStep 17232101 = 3231019) B3231019
theorem B1511719 : Blo 1510952 1511719 := bstep (se 1 (by rfl) ⟨1133789, by rfl⟩ : syracuseStep 1511719 = 2267579) B2267579
theorem B1511759 : Blo 1510952 1511759 := bstep (se 1 (by rfl) ⟨1133819, by rfl⟩ : syracuseStep 1511759 = 2267639) B2267639
theorem B1511775 : Blo 1510952 1511775 := bstep (se 1 (by rfl) ⟨1133831, by rfl⟩ : syracuseStep 1511775 = 2267663) B2267663
theorem B1511803 : Blo 1510952 1511803 := bstep (se 1 (by rfl) ⟨1133852, by rfl⟩ : syracuseStep 1511803 = 2267705) B2267705
theorem B2871713 : Blo 1510952 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1511855 : Blo 1510952 1511855 := bstep (se 1 (by rfl) ⟨1133891, by rfl⟩ : syracuseStep 1511855 = 2267783) B2267783
theorem B1511879 : Blo 1510952 1511879 := bstep (se 1 (by rfl) ⟨1133909, by rfl⟩ : syracuseStep 1511879 = 2267819) B2267819
theorem B1511899 : Blo 1510952 1511899 := bstep (se 1 (by rfl) ⟨1133924, by rfl⟩ : syracuseStep 1511899 = 2267849) B2267849
theorem B4846043 : Blo 1510952 4846043 := bstep (se 1 (by rfl) ⟨3634532, by rfl⟩ : syracuseStep 4846043 = 7269065) B7269065
theorem B1511975 : Blo 1510952 1511975 := bstep (se 1 (by rfl) ⟨1133981, by rfl⟩ : syracuseStep 1511975 = 2267963) B2267963
theorem B2552377 : Blo 1510952 2552377 := bstep (se 2 (by rfl) ⟨957141, by rfl⟩ : syracuseStep 2552377 = 1914283) B1914283
theorem B2871865 : Blo 1510952 2871865 := bstep (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) B2153899
theorem B1512015 : Blo 1510952 1512015 := bstep (se 1 (by rfl) ⟨1134011, by rfl⟩ : syracuseStep 1512015 = 2268023) B2268023
theorem B2044495 : Blo 1510952 2044495 := bstep (se 1 (by rfl) ⟨1533371, by rfl⟩ : syracuseStep 2044495 = 3066743) B3066743
theorem B1512031 : Blo 1510952 1512031 := bstep (se 1 (by rfl) ⟨1134023, by rfl⟩ : syracuseStep 1512031 = 2268047) B2268047
theorem B1512059 : Blo 1510952 1512059 := bstep (se 1 (by rfl) ⟨1134044, by rfl⟩ : syracuseStep 1512059 = 2268089) B2268089
theorem B2421419 : Blo 1510952 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B1512111 : Blo 1510952 1512111 := bstep (se 1 (by rfl) ⟨1134083, by rfl⟩ : syracuseStep 1512111 = 2268167) B2268167
theorem B1512135 : Blo 1510952 1512135 := bstep (se 1 (by rfl) ⟨1134101, by rfl⟩ : syracuseStep 1512135 = 2268203) B2268203
theorem B2552519 : Blo 1510952 2552519 := bstep (se 1 (by rfl) ⟨1914389, by rfl⟩ : syracuseStep 2552519 = 3828779) B3828779
theorem B1512155 : Blo 1510952 1512155 := bstep (se 1 (by rfl) ⟨1134116, by rfl⟩ : syracuseStep 1512155 = 2268233) B2268233
theorem B2421497 : Blo 1510952 2421497 := bstep (se 2 (by rfl) ⟨908061, by rfl⟩ : syracuseStep 2421497 = 1816123) B1816123
theorem B50418449 : Blo 1510952 50418449 := bstep (se 2 (by rfl) ⟨18906918, by rfl⟩ : syracuseStep 50418449 = 37813837) B37813837
theorem B1512231 : Blo 1510952 1512231 := bstep (se 1 (by rfl) ⟨1134173, by rfl⟩ : syracuseStep 1512231 = 2268347) B2268347
theorem B4305737 : Blo 1510952 4305737 := bstep (se 2 (by rfl) ⟨1614651, by rfl⟩ : syracuseStep 4305737 = 3229303) B3229303
theorem B15520585 : Blo 1510952 15520585 := bstep (se 2 (by rfl) ⟨5820219, by rfl⟩ : syracuseStep 15520585 = 11640439) B11640439
theorem B1512271 : Blo 1510952 1512271 := bstep (se 1 (by rfl) ⟨1134203, by rfl⟩ : syracuseStep 1512271 = 2268407) B2268407
theorem B1512287 : Blo 1510952 1512287 := bstep (se 1 (by rfl) ⟨1134215, by rfl⟩ : syracuseStep 1512287 = 2268431) B2268431
theorem B2552681 : Blo 1510952 2552681 := bstep (se 2 (by rfl) ⟨957255, by rfl⟩ : syracuseStep 2552681 = 1914511) B1914511
theorem B2872169 : Blo 1510952 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B5100407 : Blo 1510952 5100407 := bstep (se 1 (by rfl) ⟨3825305, by rfl⟩ : syracuseStep 5100407 = 7650611) B7650611
theorem B1512315 : Blo 1510952 1512315 := bstep (se 1 (by rfl) ⟨1134236, by rfl⟩ : syracuseStep 1512315 = 2268473) B2268473
theorem B1512367 : Blo 1510952 1512367 := bstep (se 1 (by rfl) ⟨1134275, by rfl⟩ : syracuseStep 1512367 = 2268551) B2268551
theorem B1512391 : Blo 1510952 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B1512411 : Blo 1510952 1512411 := bstep (se 1 (by rfl) ⟨1134308, by rfl⟩ : syracuseStep 1512411 = 2268617) B2268617
theorem B6132755 : Blo 1510952 6132755 := bstep (se 1 (by rfl) ⟨4599566, by rfl⟩ : syracuseStep 6132755 = 9199133) B9199133
theorem B1512487 : Blo 1510952 1512487 := bstep (se 1 (by rfl) ⟨1134365, by rfl⟩ : syracuseStep 1512487 = 2268731) B2268731
theorem B19379249 : Blo 1510952 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B5100623 : Blo 1510952 5100623 := bstep (se 1 (by rfl) ⟨3825467, by rfl⟩ : syracuseStep 5100623 = 7650935) B7650935
theorem B5739599 : Blo 1510952 5739599 := bstep (se 1 (by rfl) ⟨4304699, by rfl⟩ : syracuseStep 5739599 = 8609399) B8609399
theorem B1512527 : Blo 1510952 1512527 := bstep (se 1 (by rfl) ⟨1134395, by rfl⟩ : syracuseStep 1512527 = 2268791) B2268791
theorem B1512543 : Blo 1510952 1512543 := bstep (se 1 (by rfl) ⟨1134407, by rfl⟩ : syracuseStep 1512543 = 2268815) B2268815
theorem B6132851 : Blo 1510952 6132851 := bstep (se 1 (by rfl) ⟨4599638, by rfl⟩ : syracuseStep 6132851 = 9199277) B9199277
theorem B1512571 : Blo 1510952 1512571 := bstep (se 1 (by rfl) ⟨1134428, by rfl⟩ : syracuseStep 1512571 = 2268857) B2268857
theorem B1512623 : Blo 1510952 1512623 := bstep (se 1 (by rfl) ⟨1134467, by rfl⟩ : syracuseStep 1512623 = 2268935) B2268935
theorem B1512647 : Blo 1510952 1512647 := bstep (se 1 (by rfl) ⟨1134485, by rfl⟩ : syracuseStep 1512647 = 2268971) B2268971
theorem B1512667 : Blo 1510952 1512667 := bstep (se 1 (by rfl) ⟨1134500, by rfl⟩ : syracuseStep 1512667 = 2269001) B2269001
theorem B5739767 : Blo 1510952 5739767 := bstep (se 1 (by rfl) ⟨4304825, by rfl⟩ : syracuseStep 5739767 = 8609651) B8609651
theorem B2422009 : Blo 1510952 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B2553079 : Blo 1510952 2553079 := bstep (se 1 (by rfl) ⟨1914809, by rfl⟩ : syracuseStep 2553079 = 3829619) B3829619
theorem B1512743 : Blo 1510952 1512743 := bstep (se 1 (by rfl) ⟨1134557, by rfl⟩ : syracuseStep 1512743 = 2269115) B2269115
theorem B1512783 : Blo 1510952 1512783 := bstep (se 1 (by rfl) ⟨1134587, by rfl⟩ : syracuseStep 1512783 = 2269175) B2269175
theorem B2266463 : Blo 1510952 2266463 := bstep (se 1 (by rfl) ⟨1699847, by rfl⟩ : syracuseStep 2266463 = 3399695) B3399695
theorem B2151775 : Blo 1510952 2151775 := bstep (se 1 (by rfl) ⟨1613831, by rfl⟩ : syracuseStep 2151775 = 3227663) B3227663
theorem B1512799 : Blo 1510952 1512799 := bstep (se 1 (by rfl) ⟨1134599, by rfl⟩ : syracuseStep 1512799 = 2269199) B2269199
theorem B2266475 : Blo 1510952 2266475 := bstep (se 1 (by rfl) ⟨1699856, by rfl⟩ : syracuseStep 2266475 = 3399713) B3399713
theorem B1512827 : Blo 1510952 1512827 := bstep (se 1 (by rfl) ⟨1134620, by rfl⟩ : syracuseStep 1512827 = 2269241) B2269241
theorem B1512879 : Blo 1510952 1512879 := bstep (se 1 (by rfl) ⟨1134659, by rfl⟩ : syracuseStep 1512879 = 2269319) B2269319
theorem B1512903 : Blo 1510952 1512903 := bstep (se 1 (by rfl) ⟨1134677, by rfl⟩ : syracuseStep 1512903 = 2269355) B2269355
theorem B5101001 : Blo 1510952 5101001 := bstep (se 2 (by rfl) ⟨1912875, by rfl⟩ : syracuseStep 5101001 = 3825751) B3825751
theorem B4142555 : Blo 1510952 4142555 := bstep (se 1 (by rfl) ⟨3106916, by rfl⟩ : syracuseStep 4142555 = 6213833) B6213833
theorem B1512923 : Blo 1510952 1512923 := bstep (se 1 (by rfl) ⟨1134692, by rfl⟩ : syracuseStep 1512923 = 2269385) B2269385
theorem B2266703 : Blo 1510952 2266703 := bstep (se 1 (by rfl) ⟨1700027, by rfl⟩ : syracuseStep 2266703 = 3400055) B3400055
theorem B11482721 : Blo 1510952 11482721 := bstep (se 2 (by rfl) ⟨4306020, by rfl⟩ : syracuseStep 11482721 = 8612041) B8612041
theorem B1701499 : Blo 1510952 1701499 := bstep (se 1 (by rfl) ⟨1276124, by rfl⟩ : syracuseStep 1701499 = 2552249) B2552249
theorem B6461117 : Blo 1510952 6461117 := bstep (se 3 (by rfl) ⟨1211459, by rfl⟩ : syracuseStep 6461117 = 2422919) B2422919
theorem B2266823 : Blo 1510952 2266823 := bstep (se 1 (by rfl) ⟨1700117, by rfl⟩ : syracuseStep 2266823 = 3400235) B3400235
theorem B5101271 : Blo 1510952 5101271 := bstep (se 1 (by rfl) ⟨3825953, by rfl⟩ : syracuseStep 5101271 = 7651907) B7651907
theorem B2266985 : Blo 1510952 2266985 := bstep (se 2 (by rfl) ⟨850119, by rfl⟩ : syracuseStep 2266985 = 1700239) B1700239
theorem B5101487 : Blo 1510952 5101487 := bstep (se 1 (by rfl) ⟨3826115, by rfl⟩ : syracuseStep 5101487 = 7652231) B7652231
theorem B2267063 : Blo 1510952 2267063 := bstep (se 1 (by rfl) ⟨1700297, by rfl⟩ : syracuseStep 2267063 = 3400595) B3400595
theorem B2267099 : Blo 1510952 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B4307023 : Blo 1510952 4307023 := bstep (se 1 (by rfl) ⟨3230267, by rfl⟩ : syracuseStep 4307023 = 6460535) B6460535
theorem B1701967 : Blo 1510952 1701967 := bstep (se 1 (by rfl) ⟨1276475, by rfl⟩ : syracuseStep 1701967 = 2552951) B2552951
theorem B5740739 : Blo 1510952 5740739 := bstep (se 1 (by rfl) ⟨4305554, by rfl⟩ : syracuseStep 5740739 = 8611109) B8611109
theorem B7657739 : Blo 1510952 7657739 := bstep (se 1 (by rfl) ⟨5743304, by rfl⟩ : syracuseStep 7657739 = 11486609) B11486609
theorem B6461801 : Blo 1510952 6461801 := bstep (se 2 (by rfl) ⟨2423175, by rfl⟩ : syracuseStep 6461801 = 4846351) B4846351
theorem B2267567 : Blo 1510952 2267567 := bstep (se 1 (by rfl) ⟨1700675, by rfl⟩ : syracuseStep 2267567 = 3401351) B3401351
theorem B35404235 : Blo 1510952 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B93043181 : Blo 1510952 93043181 := bstep (se 3 (by rfl) ⟨17445596, by rfl⟩ : syracuseStep 93043181 = 34891193) B34891193
theorem B7649801 : Blo 1510952 7649801 := bstep (se 2 (by rfl) ⟨2868675, by rfl⟩ : syracuseStep 7649801 = 5737351) B5737351
theorem B2267657 : Blo 1510952 2267657 := bstep (se 2 (by rfl) ⟨850371, by rfl⟩ : syracuseStep 2267657 = 1700743) B1700743
theorem B2267687 : Blo 1510952 2267687 := bstep (se 1 (by rfl) ⟨1700765, by rfl⟩ : syracuseStep 2267687 = 3401531) B3401531
theorem B2128423 : Blo 1510952 2128423 := bstep (se 1 (by rfl) ⟨1596317, by rfl⟩ : syracuseStep 2128423 = 3192635) B3192635
theorem B2267771 : Blo 1510952 2267771 := bstep (se 1 (by rfl) ⟨1700828, by rfl⟩ : syracuseStep 2267771 = 3401657) B3401657
theorem B5446291 : Blo 1510952 5446291 := bstep (se 1 (by rfl) ⟨4084718, by rfl⟩ : syracuseStep 5446291 = 8169437) B8169437
theorem B2267897 : Blo 1510952 2267897 := bstep (se 2 (by rfl) ⟨850461, by rfl⟩ : syracuseStep 2267897 = 1700923) B1700923
theorem B7265027 : Blo 1510952 7265027 := bstep (se 1 (by rfl) ⟨5448770, by rfl⟩ : syracuseStep 7265027 = 10897541) B10897541
theorem B2267999 : Blo 1510952 2267999 := bstep (se 1 (by rfl) ⟨1700999, by rfl⟩ : syracuseStep 2267999 = 3401999) B3401999
theorem B2268011 : Blo 1510952 2268011 := bstep (se 1 (by rfl) ⟨1701008, by rfl⟩ : syracuseStep 2268011 = 3402017) B3402017
theorem B19364791 : Blo 1510952 19364791 := bstep (se 1 (by rfl) ⟨14523593, by rfl⟩ : syracuseStep 19364791 = 29047187) B29047187
theorem B11484179 : Blo 1510952 11484179 := bstep (se 1 (by rfl) ⟨8613134, by rfl⟩ : syracuseStep 11484179 = 17226269) B17226269
theorem B3931193 : Blo 1510952 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2268239 : Blo 1510952 2268239 := bstep (se 1 (by rfl) ⟨1701179, by rfl⟩ : syracuseStep 2268239 = 3402359) B3402359
theorem B5741725 : Blo 1510952 5741725 := bstep (se 3 (by rfl) ⟨1076573, by rfl⟩ : syracuseStep 5741725 = 2153147) B2153147
theorem B9682091 : Blo 1510952 9682091 := bstep (se 1 (by rfl) ⟨7261568, by rfl⟩ : syracuseStep 9682091 = 14523137) B14523137
theorem B2268359 : Blo 1510952 2268359 := bstep (se 1 (by rfl) ⟨1701269, by rfl⟩ : syracuseStep 2268359 = 3402539) B3402539
theorem B19365155 : Blo 1510952 19365155 := bstep (se 1 (by rfl) ⟨14523866, by rfl⟩ : syracuseStep 19365155 = 29047733) B29047733
theorem B2268521 : Blo 1510952 2268521 := bstep (se 2 (by rfl) ⟨850695, by rfl⟩ : syracuseStep 2268521 = 1701391) B1701391
theorem B4087183 : Blo 1510952 4087183 := bstep (se 1 (by rfl) ⟨3065387, by rfl⟩ : syracuseStep 4087183 = 6130775) B6130775
theorem B1965487 : Blo 1510952 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B2268599 : Blo 1510952 2268599 := bstep (se 1 (by rfl) ⟨1701449, by rfl⟩ : syracuseStep 2268599 = 3402899) B3402899
theorem B2268635 : Blo 1510952 2268635 := bstep (se 1 (by rfl) ⟨1701476, by rfl⟩ : syracuseStep 2268635 = 3402953) B3402953
theorem B4840993 : Blo 1510952 4840993 := bstep (se 2 (by rfl) ⟨1815372, by rfl⟩ : syracuseStep 4840993 = 3630745) B3630745
theorem B7659197 : Blo 1510952 7659197 := bstep (se 3 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 7659197 = 2872199) B2872199
theorem B5447533 : Blo 1510952 5447533 := bstep (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) B2042825
theorem B7364461 : Blo 1510952 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B3825569 : Blo 1510952 3825569 := bstep (se 2 (by rfl) ⟨1434588, by rfl⟩ : syracuseStep 3825569 = 2869177) B2869177
theorem B2269103 : Blo 1510952 2269103 := bstep (se 1 (by rfl) ⟨1701827, by rfl⟩ : syracuseStep 2269103 = 3403655) B3403655
theorem B7651259 : Blo 1510952 7651259 := bstep (se 1 (by rfl) ⟨5738444, by rfl⟩ : syracuseStep 7651259 = 11476889) B11476889
theorem B3399785 : Blo 1510952 3399785 := bstep (se 2 (by rfl) ⟨1274919, by rfl⟩ : syracuseStep 3399785 = 2549839) B2549839
theorem B5742697 : Blo 1510952 5742697 := bstep (se 2 (by rfl) ⟨2153511, by rfl⟩ : syracuseStep 5742697 = 4307023) B4307023
theorem B2269289 : Blo 1510952 2269289 := bstep (se 2 (by rfl) ⟨850983, by rfl⟩ : syracuseStep 2269289 = 1701967) B1701967
theorem B7758281 : Blo 1510952 7758281 := bstep (se 2 (by rfl) ⟨2909355, by rfl⟩ : syracuseStep 7758281 = 5818711) B5818711
theorem B3228115 : Blo 1510952 3228115 := bstep (se 1 (by rfl) ⟨2421086, by rfl⟩ : syracuseStep 3228115 = 4842173) B4842173
theorem B1614331 : Blo 1510952 1614331 := bstep (se 1 (by rfl) ⟨1210748, by rfl⟩ : syracuseStep 1614331 = 2421497) B2421497
theorem B33612299 : Blo 1510952 33612299 := bstep (se 1 (by rfl) ⟨25209224, by rfl⟩ : syracuseStep 33612299 = 50418449) B50418449
theorem B3400271 : Blo 1510952 3400271 := bstep (se 1 (by rfl) ⟨2550203, by rfl⟩ : syracuseStep 3400271 = 5100407) B5100407
theorem B6128311 : Blo 1510952 6128311 := bstep (se 1 (by rfl) ⟨4596233, by rfl⟩ : syracuseStep 6128311 = 9192467) B9192467
theorem B4088503 : Blo 1510952 4088503 := bstep (se 1 (by rfl) ⟨3066377, by rfl⟩ : syracuseStep 4088503 = 6132755) B6132755
theorem B12919499 : Blo 1510952 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B3400415 : Blo 1510952 3400415 := bstep (se 1 (by rfl) ⟨2550311, by rfl⟩ : syracuseStep 3400415 = 5100623) B5100623
theorem B3826399 : Blo 1510952 3826399 := bstep (se 1 (by rfl) ⟨2869799, by rfl⟩ : syracuseStep 3826399 = 5739599) B5739599
theorem B4088567 : Blo 1510952 4088567 := bstep (se 1 (by rfl) ⟨3066425, by rfl⟩ : syracuseStep 4088567 = 6132851) B6132851
theorem B14533435 : Blo 1510952 14533435 := bstep (se 1 (by rfl) ⟨10900076, by rfl⟩ : syracuseStep 14533435 = 21800153) B21800153
theorem B3826511 : Blo 1510952 3826511 := bstep (se 1 (by rfl) ⟨2869883, by rfl⟩ : syracuseStep 3826511 = 5739767) B5739767
theorem B3400667 : Blo 1510952 3400667 := bstep (se 1 (by rfl) ⟨2550500, by rfl⟩ : syracuseStep 3400667 = 5101001) B5101001
theorem B2761703 : Blo 1510952 2761703 := bstep (se 1 (by rfl) ⟨2071277, by rfl⟩ : syracuseStep 2761703 = 4142555) B4142555
theorem B21799925 : Blo 1510952 21799925 := bstep (se 5 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 21799925 = 2043743) B2043743
theorem B20694113 : Blo 1510952 20694113 := bstep (se 2 (by rfl) ⟨7760292, by rfl⟩ : syracuseStep 20694113 = 15520585) B15520585
theorem B3400847 : Blo 1510952 3400847 := bstep (se 1 (by rfl) ⟨2550635, by rfl⟩ : syracuseStep 3400847 = 5101271) B5101271
theorem B3400937 : Blo 1510952 3400937 := bstep (se 2 (by rfl) ⟨1275351, by rfl⟩ : syracuseStep 3400937 = 2550703) B2550703
theorem B5104889 : Blo 1510952 5104889 := bstep (se 2 (by rfl) ⟨1914333, by rfl⟩ : syracuseStep 5104889 = 3828667) B3828667
theorem B3400991 : Blo 1510952 3400991 := bstep (se 1 (by rfl) ⟨2550743, by rfl⟩ : syracuseStep 3400991 = 5101487) B5101487
theorem B15516971 : Blo 1510952 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B7652717 : Blo 1510952 7652717 := bstep (se 3 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 7652717 = 2869769) B2869769
theorem B3827159 : Blo 1510952 3827159 := bstep (se 1 (by rfl) ⟨2870369, by rfl⟩ : syracuseStep 3827159 = 5740739) B5740739
theorem B5105159 : Blo 1510952 5105159 := bstep (se 1 (by rfl) ⟨3828869, by rfl⟩ : syracuseStep 5105159 = 7657739) B7657739
theorem B23602823 : Blo 1510952 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B3229345 : Blo 1510952 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B2869033 : Blo 1510952 2869033 := bstep (se 2 (by rfl) ⟨1075887, by rfl⟩ : syracuseStep 2869033 = 2151775) B2151775
theorem B3401513 : Blo 1510952 3401513 := bstep (se 2 (by rfl) ⟨1275567, by rfl⟩ : syracuseStep 3401513 = 2551135) B2551135
theorem B3827513 : Blo 1510952 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B4843351 : Blo 1510952 4843351 := bstep (se 1 (by rfl) ⟨3632513, by rfl⟩ : syracuseStep 4843351 = 7265027) B7265027
theorem B5449577 : Blo 1510952 5449577 := bstep (se 2 (by rfl) ⟨2043591, by rfl⟩ : syracuseStep 5449577 = 4087183) B4087183
theorem B3630977 : Blo 1510952 3630977 := bstep (se 2 (by rfl) ⟨1361616, by rfl⟩ : syracuseStep 3630977 = 2723233) B2723233
theorem B19384271 : Blo 1510952 19384271 := bstep (se 1 (by rfl) ⟨14538203, by rfl⟩ : syracuseStep 19384271 = 29076407) B29076407
theorem B16345273 : Blo 1510952 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B24521021 : Blo 1510952 24521021 := bstep (se 3 (by rfl) ⟨4597691, by rfl⟩ : syracuseStep 24521021 = 9195383) B9195383
theorem B23284135 : Blo 1510952 23284135 := bstep (se 1 (by rfl) ⟨17463101, by rfl⟩ : syracuseStep 23284135 = 34926203) B34926203
theorem B5106131 : Blo 1510952 5106131 := bstep (se 1 (by rfl) ⟨3829598, by rfl⟩ : syracuseStep 5106131 = 7659197) B7659197
theorem B2869823 : Blo 1510952 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B2550379 : Blo 1510952 2550379 := bstep (se 1 (by rfl) ⟨1912784, by rfl⟩ : syracuseStep 2550379 = 3825569) B3825569
theorem B7867127 : Blo 1510952 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B11488067 : Blo 1510952 11488067 := bstep (se 1 (by rfl) ⟨8616050, by rfl⟩ : syracuseStep 11488067 = 17232101) B17232101
theorem B3402575 : Blo 1510952 3402575 := bstep (se 1 (by rfl) ⟨2551931, by rfl⟩ : syracuseStep 3402575 = 5103863) B5103863
theorem B3632015 : Blo 1510952 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B2550683 : Blo 1510952 2550683 := bstep (se 1 (by rfl) ⟨1913012, by rfl⟩ : syracuseStep 2550683 = 3826025) B3826025
theorem B3230695 : Blo 1510952 3230695 := bstep (se 1 (by rfl) ⟨2423021, by rfl⟩ : syracuseStep 3230695 = 4846043) B4846043
theorem B3402791 : Blo 1510952 3402791 := bstep (se 1 (by rfl) ⟨2552093, by rfl⟩ : syracuseStep 3402791 = 5104187) B5104187
theorem B2870491 : Blo 1510952 2870491 := bstep (se 1 (by rfl) ⟨2152868, by rfl⟩ : syracuseStep 2870491 = 4305737) B4305737
theorem B3402971 : Blo 1510952 3402971 := bstep (se 1 (by rfl) ⟨2552228, by rfl⟩ : syracuseStep 3402971 = 5104457) B5104457
theorem B132484481 : Blo 1510952 132484481 := bstep (se 2 (by rfl) ⟨49681680, by rfl⟩ : syracuseStep 132484481 = 99363361) B99363361
theorem B2837897 : Blo 1510952 2837897 := bstep (se 2 (by rfl) ⟨1064211, by rfl⟩ : syracuseStep 2837897 = 2128423) B2128423
theorem B3403169 : Blo 1510952 3403169 := bstep (se 2 (by rfl) ⟨1276188, by rfl⟩ : syracuseStep 3403169 = 2552377) B2552377
theorem B3829153 : Blo 1510952 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B7261721 : Blo 1510952 7261721 := bstep (se 2 (by rfl) ⟨2723145, by rfl⟩ : syracuseStep 7261721 = 5446291) B5446291
theorem B1510975 : Blo 1510952 1510975 := bstep (se 1 (by rfl) ⟨1133231, by rfl⟩ : syracuseStep 1510975 = 2266463) B2266463
theorem B1510983 : Blo 1510952 1510983 := bstep (se 1 (by rfl) ⟨1133237, by rfl⟩ : syracuseStep 1510983 = 2266475) B2266475
theorem B2043463 : Blo 1510952 2043463 := bstep (se 1 (by rfl) ⟨1532597, by rfl⟩ : syracuseStep 2043463 = 3065195) B3065195
theorem B12259025 : Blo 1510952 12259025 := bstep (se 2 (by rfl) ⟨4597134, by rfl⟩ : syracuseStep 12259025 = 9194269) B9194269
theorem B1511135 : Blo 1510952 1511135 := bstep (se 1 (by rfl) ⟨1133351, by rfl⟩ : syracuseStep 1511135 = 2266703) B2266703
theorem B2420459 : Blo 1510952 2420459 := bstep (se 1 (by rfl) ⟨1815344, by rfl⟩ : syracuseStep 2420459 = 3630689) B3630689
theorem B7655147 : Blo 1510952 7655147 := bstep (se 1 (by rfl) ⟨5741360, by rfl⟩ : syracuseStep 7655147 = 11482721) B11482721
theorem B1511215 : Blo 1510952 1511215 := bstep (se 1 (by rfl) ⟨1133411, by rfl⟩ : syracuseStep 1511215 = 2266823) B2266823
theorem B1511323 : Blo 1510952 1511323 := bstep (se 1 (by rfl) ⟨1133492, by rfl⟩ : syracuseStep 1511323 = 2266985) B2266985
theorem B2043803 : Blo 1510952 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B1511375 : Blo 1510952 1511375 := bstep (se 1 (by rfl) ⟨1133531, by rfl⟩ : syracuseStep 1511375 = 2267063) B2267063
theorem B3403727 : Blo 1510952 3403727 := bstep (se 1 (by rfl) ⟨2552795, by rfl⟩ : syracuseStep 3403727 = 5105591) B5105591
theorem B1511399 : Blo 1510952 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B7655633 : Blo 1510952 7655633 := bstep (se 2 (by rfl) ⟨2870862, by rfl⟩ : syracuseStep 7655633 = 5741725) B5741725
theorem B1700059 : Blo 1510952 1700059 := bstep (se 1 (by rfl) ⟨1275044, by rfl⟩ : syracuseStep 1700059 = 2550089) B2550089
theorem B1511711 : Blo 1510952 1511711 := bstep (se 1 (by rfl) ⟨1133783, by rfl⟩ : syracuseStep 1511711 = 2267567) B2267567
theorem B3404105 : Blo 1510952 3404105 := bstep (se 2 (by rfl) ⟨1276539, by rfl⟩ : syracuseStep 3404105 = 2553079) B2553079
theorem B5099867 : Blo 1510952 5099867 := bstep (se 1 (by rfl) ⟨3824900, by rfl⟩ : syracuseStep 5099867 = 7649801) B7649801
theorem B1511771 : Blo 1510952 1511771 := bstep (se 1 (by rfl) ⟨1133828, by rfl⟩ : syracuseStep 1511771 = 2267657) B2267657
theorem B3404123 : Blo 1510952 3404123 := bstep (se 1 (by rfl) ⟨2553092, by rfl⟩ : syracuseStep 3404123 = 5106185) B5106185
theorem B1511791 : Blo 1510952 1511791 := bstep (se 1 (by rfl) ⟨1133843, by rfl⟩ : syracuseStep 1511791 = 2267687) B2267687
theorem B1511847 : Blo 1510952 1511847 := bstep (se 1 (by rfl) ⟨1133885, by rfl⟩ : syracuseStep 1511847 = 2267771) B2267771
theorem B2044327 : Blo 1510952 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B1700347 : Blo 1510952 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B1511931 : Blo 1510952 1511931 := bstep (se 1 (by rfl) ⟨1133948, by rfl⟩ : syracuseStep 1511931 = 2267897) B2267897
theorem B1511999 : Blo 1510952 1511999 := bstep (se 1 (by rfl) ⟨1133999, by rfl⟩ : syracuseStep 1511999 = 2267999) B2267999
theorem B1512007 : Blo 1510952 1512007 := bstep (se 1 (by rfl) ⟨1134005, by rfl⟩ : syracuseStep 1512007 = 2268011) B2268011
theorem B13087385 : Blo 1510952 13087385 := bstep (se 2 (by rfl) ⟨4907769, by rfl⟩ : syracuseStep 13087385 = 9815539) B9815539
theorem B1700527 : Blo 1510952 1700527 := bstep (se 1 (by rfl) ⟨1275395, by rfl⟩ : syracuseStep 1700527 = 2550791) B2550791
theorem B7656119 : Blo 1510952 7656119 := bstep (se 1 (by rfl) ⟨5742089, by rfl⟩ : syracuseStep 7656119 = 11484179) B11484179
theorem B1512159 : Blo 1510952 1512159 := bstep (se 1 (by rfl) ⟨1134119, by rfl⟩ : syracuseStep 1512159 = 2268239) B2268239
theorem B1512239 : Blo 1510952 1512239 := bstep (se 1 (by rfl) ⟨1134179, by rfl⟩ : syracuseStep 1512239 = 2268359) B2268359
theorem B1512347 : Blo 1510952 1512347 := bstep (se 1 (by rfl) ⟨1134260, by rfl⟩ : syracuseStep 1512347 = 2268521) B2268521
theorem B3634091 : Blo 1510952 3634091 := bstep (se 1 (by rfl) ⟨2725568, by rfl⟩ : syracuseStep 3634091 = 5451137) B5451137
theorem B1700815 : Blo 1510952 1700815 := bstep (se 1 (by rfl) ⟨1275611, by rfl⟩ : syracuseStep 1700815 = 2551223) B2551223
theorem B1913807 : Blo 1510952 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B1512399 : Blo 1510952 1512399 := bstep (se 1 (by rfl) ⟨1134299, by rfl⟩ : syracuseStep 1512399 = 2268599) B2268599
theorem B1512423 : Blo 1510952 1512423 := bstep (se 1 (by rfl) ⟨1134317, by rfl⟩ : syracuseStep 1512423 = 2268635) B2268635
theorem B7263377 : Blo 1510952 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B9819281 : Blo 1510952 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B7656605 : Blo 1510952 7656605 := bstep (se 3 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 7656605 = 2871227) B2871227
theorem B4306135 : Blo 1510952 4306135 := bstep (se 1 (by rfl) ⟨3229601, by rfl⟩ : syracuseStep 4306135 = 6459203) B6459203
theorem B1512735 : Blo 1510952 1512735 := bstep (se 1 (by rfl) ⟨1134551, by rfl⟩ : syracuseStep 1512735 = 2269103) B2269103
theorem B5100839 : Blo 1510952 5100839 := bstep (se 1 (by rfl) ⟨3825629, by rfl⟩ : syracuseStep 5100839 = 7651259) B7651259
theorem B1701211 : Blo 1510952 1701211 := bstep (se 1 (by rfl) ⟨1275908, by rfl⟩ : syracuseStep 1701211 = 2551817) B2551817
theorem B1512795 : Blo 1510952 1512795 := bstep (se 1 (by rfl) ⟨1134596, by rfl⟩ : syracuseStep 1512795 = 2269193) B2269193
theorem B1512815 : Blo 1510952 1512815 := bstep (se 1 (by rfl) ⟨1134611, by rfl⟩ : syracuseStep 1512815 = 2269223) B2269223
theorem B2151803 : Blo 1510952 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B6894971 : Blo 1510952 6894971 := bstep (se 1 (by rfl) ⟨5171228, by rfl⟩ : syracuseStep 6894971 = 10342457) B10342457
theorem B2266505 : Blo 1510952 2266505 := bstep (se 2 (by rfl) ⟨849939, by rfl⟩ : syracuseStep 2266505 = 1699879) B1699879
theorem B1512871 : Blo 1510952 1512871 := bstep (se 1 (by rfl) ⟨1134653, by rfl⟩ : syracuseStep 1512871 = 2269307) B2269307
theorem B1701319 : Blo 1510952 1701319 := bstep (se 1 (by rfl) ⟨1275989, by rfl⟩ : syracuseStep 1701319 = 2551979) B2551979
theorem B10483181 : Blo 1510952 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B2266859 : Blo 1510952 2266859 := bstep (se 1 (by rfl) ⟨1700144, by rfl⟩ : syracuseStep 2266859 = 3400289) B3400289
theorem B1701679 : Blo 1510952 1701679 := bstep (se 1 (by rfl) ⟨1276259, by rfl⟩ : syracuseStep 1701679 = 2552519) B2552519
theorem B1701787 : Blo 1510952 1701787 := bstep (se 1 (by rfl) ⟨1276340, by rfl⟩ : syracuseStep 1701787 = 2552681) B2552681
theorem B1914779 : Blo 1510952 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B248166341 : Blo 1510952 248166341 := bstep (se 4 (by rfl) ⟨23265594, by rfl⟩ : syracuseStep 248166341 = 46531189) B46531189
theorem B2267087 : Blo 1510952 2267087 := bstep (se 1 (by rfl) ⟨1700315, by rfl⟩ : syracuseStep 2267087 = 3400631) B3400631
theorem B2725993 : Blo 1510952 2725993 := bstep (se 2 (by rfl) ⟨1022247, by rfl⟩ : syracuseStep 2725993 = 2044495) B2044495
theorem B5101703 : Blo 1510952 5101703 := bstep (se 1 (by rfl) ⟨3826277, by rfl⟩ : syracuseStep 5101703 = 7652555) B7652555
theorem B503208197 : Blo 1510952 503208197 := bstep (se 4 (by rfl) ⟨47175768, by rfl⟩ : syracuseStep 503208197 = 94351537) B94351537
theorem B36804887 : Blo 1510952 36804887 := bstep (se 1 (by rfl) ⟨27603665, by rfl⟩ : syracuseStep 36804887 = 55207331) B55207331
theorem B2267483 : Blo 1510952 2267483 := bstep (se 1 (by rfl) ⟨1700612, by rfl⟩ : syracuseStep 2267483 = 3401225) B3401225
theorem B58104215 : Blo 1510952 58104215 := bstep (se 1 (by rfl) ⟨43578161, by rfl⟩ : syracuseStep 58104215 = 87156323) B87156323
theorem B7657901 : Blo 1510952 7657901 := bstep (se 3 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 7657901 = 2871713) B2871713
theorem B4307411 : Blo 1510952 4307411 := bstep (se 1 (by rfl) ⟨3230558, by rfl⟩ : syracuseStep 4307411 = 6461117) B6461117
theorem B2267711 : Blo 1510952 2267711 := bstep (se 1 (by rfl) ⟨1700783, by rfl⟩ : syracuseStep 2267711 = 3401567) B3401567
theorem B25819721 : Blo 1510952 25819721 := bstep (se 2 (by rfl) ⟨9682395, by rfl⟩ : syracuseStep 25819721 = 19364791) B19364791
theorem B7658063 : Blo 1510952 7658063 := bstep (se 1 (by rfl) ⟨5743547, by rfl⟩ : syracuseStep 7658063 = 11487095) B11487095
theorem B2267831 : Blo 1510952 2267831 := bstep (se 1 (by rfl) ⟨1700873, by rfl⟩ : syracuseStep 2267831 = 3401747) B3401747
theorem B2268059 : Blo 1510952 2268059 := bstep (se 1 (by rfl) ⟨1701044, by rfl⟩ : syracuseStep 2268059 = 3402089) B3402089
theorem B4307867 : Blo 1510952 4307867 := bstep (se 1 (by rfl) ⟨3230900, by rfl⟩ : syracuseStep 4307867 = 6461801) B6461801
theorem B62028787 : Blo 1510952 62028787 := bstep (se 1 (by rfl) ⟨46521590, by rfl⟩ : syracuseStep 62028787 = 93043181) B93043181
theorem B12917789 : Blo 1510952 12917789 := bstep (se 3 (by rfl) ⟨2422085, by rfl⟩ : syracuseStep 12917789 = 4844171) B4844171
theorem B25828469 : Blo 1510952 25828469 := bstep (se 5 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 25828469 = 2421419) B2421419
theorem B14539895 : Blo 1510952 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B3824779 : Blo 1510952 3824779 := bstep (se 1 (by rfl) ⟨2868584, by rfl⟩ : syracuseStep 3824779 = 5737169) B5737169
theorem B2620649 : Blo 1510952 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B2268455 : Blo 1510952 2268455 := bstep (se 1 (by rfl) ⟨1701341, by rfl⟩ : syracuseStep 2268455 = 3402683) B3402683
theorem B5102945 : Blo 1510952 5102945 := bstep (se 2 (by rfl) ⟨1913604, by rfl⟩ : syracuseStep 5102945 = 3827209) B3827209
theorem B2268539 : Blo 1510952 2268539 := bstep (se 1 (by rfl) ⟨1701404, by rfl⟩ : syracuseStep 2268539 = 3402809) B3402809
theorem B6454657 : Blo 1510952 6454657 := bstep (se 2 (by rfl) ⟨2420496, by rfl⟩ : syracuseStep 6454657 = 4840993) B4840993
theorem B3825083 : Blo 1510952 3825083 := bstep (se 1 (by rfl) ⟨2868812, by rfl⟩ : syracuseStep 3825083 = 5737625) B5737625
theorem B6454727 : Blo 1510952 6454727 := bstep (se 1 (by rfl) ⟨4841045, by rfl⟩ : syracuseStep 6454727 = 9682091) B9682091
theorem B11484665 : Blo 1510952 11484665 := bstep (se 2 (by rfl) ⟨4306749, by rfl⟩ : syracuseStep 11484665 = 8613499) B8613499
theorem B2268665 : Blo 1510952 2268665 := bstep (se 2 (by rfl) ⟨850749, by rfl⟩ : syracuseStep 2268665 = 1701499) B1701499
theorem B12910103 : Blo 1510952 12910103 := bstep (se 1 (by rfl) ⟨9682577, by rfl⟩ : syracuseStep 12910103 = 19365155) B19365155
theorem B2268767 : Blo 1510952 2268767 := bstep (se 1 (by rfl) ⟨1701575, by rfl⟩ : syracuseStep 2268767 = 3403151) B3403151
theorem B2907809 : Blo 1510952 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B2268983 : Blo 1510952 2268983 := bstep (se 1 (by rfl) ⟨1701737, by rfl⟩ : syracuseStep 2268983 = 3403475) B3403475
theorem B5103755 : Blo 1510952 5103755 := bstep (se 1 (by rfl) ⟨3827816, by rfl⟩ : syracuseStep 5103755 = 7655633) B7655633
theorem B2269403 : Blo 1510952 2269403 := bstep (se 1 (by rfl) ⟨1702052, by rfl⟩ : syracuseStep 2269403 = 3404105) B3404105
theorem B3399911 : Blo 1510952 3399911 := bstep (se 1 (by rfl) ⟨2549933, by rfl⟩ : syracuseStep 3399911 = 5099867) B5099867
theorem B2269415 : Blo 1510952 2269415 := bstep (se 1 (by rfl) ⟨1702061, by rfl⟩ : syracuseStep 2269415 = 3404123) B3404123
theorem B8724923 : Blo 1510952 8724923 := bstep (se 1 (by rfl) ⟨6543692, by rfl⟩ : syracuseStep 8724923 = 13087385) B13087385
theorem B5104079 : Blo 1510952 5104079 := bstep (se 1 (by rfl) ⟨3828059, by rfl⟩ : syracuseStep 5104079 = 7656119) B7656119
theorem B14533283 : Blo 1510952 14533283 := bstep (se 1 (by rfl) ⟨10899962, by rfl⟩ : syracuseStep 14533283 = 21799925) B21799925
theorem B13796075 : Blo 1510952 13796075 := bstep (se 1 (by rfl) ⟨10347056, by rfl⟩ : syracuseStep 13796075 = 20694113) B20694113
theorem B4842251 : Blo 1510952 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B6546187 : Blo 1510952 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B5104403 : Blo 1510952 5104403 := bstep (se 1 (by rfl) ⟨3828302, by rfl⟩ : syracuseStep 5104403 = 7656605) B7656605
theorem B3400505 : Blo 1510952 3400505 := bstep (se 2 (by rfl) ⟨1275189, by rfl⟩ : syracuseStep 3400505 = 2550379) B2550379
theorem B3400559 : Blo 1510952 3400559 := bstep (se 1 (by rfl) ⟨2550419, by rfl⟩ : syracuseStep 3400559 = 5100839) B5100839
theorem B4596647 : Blo 1510952 4596647 := bstep (se 1 (by rfl) ⟨3447485, by rfl⟩ : syracuseStep 4596647 = 6894971) B6894971
theorem B6988787 : Blo 1510952 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B3401135 : Blo 1510952 3401135 := bstep (se 1 (by rfl) ⟨2550851, by rfl⟩ : syracuseStep 3401135 = 5101703) B5101703
theorem B335472131 : Blo 1510952 335472131 := bstep (se 1 (by rfl) ⟨251604098, by rfl⟩ : syracuseStep 335472131 = 503208197) B503208197
theorem B24536591 : Blo 1510952 24536591 := bstep (se 1 (by rfl) ⟨18402443, by rfl⟩ : syracuseStep 24536591 = 36804887) B36804887
theorem B5105267 : Blo 1510952 5105267 := bstep (se 1 (by rfl) ⟨3828950, by rfl⟩ : syracuseStep 5105267 = 7657901) B7657901
theorem B3827321 : Blo 1510952 3827321 := bstep (se 2 (by rfl) ⟨1435245, by rfl⟩ : syracuseStep 3827321 = 2870491) B2870491
theorem B111814357 : Blo 1510952 111814357 := bstep (se 7 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 111814357 = 2620649) B2620649
theorem B17213147 : Blo 1510952 17213147 := bstep (se 1 (by rfl) ⟨12909860, by rfl⟩ : syracuseStep 17213147 = 25819721) B25819721
theorem B5105375 : Blo 1510952 5105375 := bstep (se 1 (by rfl) ⟨3829031, by rfl⟩ : syracuseStep 5105375 = 7658063) B7658063
theorem B5244751 : Blo 1510952 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B5105537 : Blo 1510952 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B8611859 : Blo 1510952 8611859 := bstep (se 1 (by rfl) ⟨6458894, by rfl⟩ : syracuseStep 8611859 = 12917789) B12917789
theorem B9693263 : Blo 1510952 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B3401963 : Blo 1510952 3401963 := bstep (se 1 (by rfl) ⟨2551472, by rfl⟩ : syracuseStep 3401963 = 5102945) B5102945
theorem B2550055 : Blo 1510952 2550055 := bstep (se 1 (by rfl) ⟨1912541, by rfl⟩ : syracuseStep 2550055 = 3825083) B3825083
theorem B4303151 : Blo 1510952 4303151 := bstep (se 1 (by rfl) ⟨3227363, by rfl⟩ : syracuseStep 4303151 = 6454727) B6454727
theorem B5450141 : Blo 1510952 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B5106077 : Blo 1510952 5106077 := bstep (se 3 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 5106077 = 1914779) B1914779
theorem B6457801 : Blo 1510952 6457801 := bstep (se 2 (by rfl) ⟨2421675, by rfl⟩ : syracuseStep 6457801 = 4843351) B4843351
theorem B21793697 : Blo 1510952 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B5172187 : Blo 1510952 5172187 := bstep (se 1 (by rfl) ⟨3879140, by rfl⟩ : syracuseStep 5172187 = 7758281) B7758281
theorem B22408199 : Blo 1510952 22408199 := bstep (se 1 (by rfl) ⟨16806149, by rfl⟩ : syracuseStep 22408199 = 33612299) B33612299
theorem B8612999 : Blo 1510952 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B2551007 : Blo 1510952 2551007 := bstep (se 1 (by rfl) ⟨1913255, by rfl⟩ : syracuseStep 2551007 = 3826511) B3826511
theorem B4304153 : Blo 1510952 4304153 := bstep (se 2 (by rfl) ⟨1614057, by rfl⟩ : syracuseStep 4304153 = 3228115) B3228115
theorem B3403259 : Blo 1510952 3403259 := bstep (se 1 (by rfl) ⟨2552444, by rfl⟩ : syracuseStep 3403259 = 5104889) B5104889
theorem B8171081 : Blo 1510952 8171081 := bstep (se 2 (by rfl) ⟨3064155, by rfl⟩ : syracuseStep 8171081 = 6128311) B6128311
theorem B5451337 : Blo 1510952 5451337 := bstep (se 2 (by rfl) ⟨2044251, by rfl⟩ : syracuseStep 5451337 = 4088503) B4088503
theorem B1511003 : Blo 1510952 1511003 := bstep (se 1 (by rfl) ⟨1133252, by rfl⟩ : syracuseStep 1511003 = 2266505) B2266505
theorem B2551439 : Blo 1510952 2551439 := bstep (se 1 (by rfl) ⟨1913579, by rfl⟩ : syracuseStep 2551439 = 3827159) B3827159
theorem B5738141 : Blo 1510952 5738141 := bstep (se 3 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 5738141 = 2151803) B2151803
theorem B3403439 : Blo 1510952 3403439 := bstep (se 1 (by rfl) ⟨2552579, by rfl⟩ : syracuseStep 3403439 = 5105159) B5105159
theorem B19377913 : Blo 1510952 19377913 := bstep (se 2 (by rfl) ⟨7266717, by rfl⟩ : syracuseStep 19377913 = 14533435) B14533435
theorem B1511239 : Blo 1510952 1511239 := bstep (se 1 (by rfl) ⟨1133429, by rfl⟩ : syracuseStep 1511239 = 2266859) B2266859
theorem B2551675 : Blo 1510952 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B2420651 : Blo 1510952 2420651 := bstep (se 1 (by rfl) ⟨1815488, by rfl⟩ : syracuseStep 2420651 = 3630977) B3630977
theorem B1511391 : Blo 1510952 1511391 := bstep (se 1 (by rfl) ⟨1133543, by rfl⟩ : syracuseStep 1511391 = 2267087) B2267087
theorem B12922847 : Blo 1510952 12922847 := bstep (se 1 (by rfl) ⟨9692135, by rfl⟩ : syracuseStep 12922847 = 19384271) B19384271
theorem B5099705 : Blo 1510952 5099705 := bstep (se 2 (by rfl) ⟨1912389, by rfl⟩ : syracuseStep 5099705 = 3824779) B3824779
theorem B16347347 : Blo 1510952 16347347 := bstep (se 1 (by rfl) ⟨12260510, by rfl⟩ : syracuseStep 16347347 = 24521021) B24521021
theorem B1511655 : Blo 1510952 1511655 := bstep (se 1 (by rfl) ⟨1133741, by rfl⟩ : syracuseStep 1511655 = 2267483) B2267483
theorem B38736143 : Blo 1510952 38736143 := bstep (se 1 (by rfl) ⟨29052107, by rfl⟩ : syracuseStep 38736143 = 58104215) B58104215
theorem B2871607 : Blo 1510952 2871607 := bstep (se 1 (by rfl) ⟨2153705, by rfl⟩ : syracuseStep 2871607 = 4307411) B4307411
theorem B3404087 : Blo 1510952 3404087 := bstep (se 1 (by rfl) ⟨2553065, by rfl⟩ : syracuseStep 3404087 = 5106131) B5106131
theorem B1913215 : Blo 1510952 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B1511807 : Blo 1510952 1511807 := bstep (se 1 (by rfl) ⟨1133855, by rfl⟩ : syracuseStep 1511807 = 2267711) B2267711
theorem B1511887 : Blo 1510952 1511887 := bstep (se 1 (by rfl) ⟨1133915, by rfl⟩ : syracuseStep 1511887 = 2267831) B2267831
theorem B8606209 : Blo 1510952 8606209 := bstep (se 2 (by rfl) ⟨3227328, by rfl⟩ : syracuseStep 8606209 = 6454657) B6454657
theorem B2421343 : Blo 1510952 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B1700455 : Blo 1510952 1700455 := bstep (se 1 (by rfl) ⟨1275341, by rfl⟩ : syracuseStep 1700455 = 2550683) B2550683
theorem B1512039 : Blo 1510952 1512039 := bstep (se 1 (by rfl) ⟨1134029, by rfl⟩ : syracuseStep 1512039 = 2268059) B2268059
theorem B2871911 : Blo 1510952 2871911 := bstep (se 1 (by rfl) ⟨2153933, by rfl⟩ : syracuseStep 2871911 = 4307867) B4307867
theorem B2724617 : Blo 1510952 2724617 := bstep (se 2 (by rfl) ⟨1021731, by rfl⟩ : syracuseStep 2724617 = 2043463) B2043463
theorem B1512303 : Blo 1510952 1512303 := bstep (se 1 (by rfl) ⟨1134227, by rfl⟩ : syracuseStep 1512303 = 2268455) B2268455
theorem B4305793 : Blo 1510952 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B1512359 : Blo 1510952 1512359 := bstep (se 1 (by rfl) ⟨1134269, by rfl⟩ : syracuseStep 1512359 = 2268539) B2268539
theorem B88322987 : Blo 1510952 88322987 := bstep (se 1 (by rfl) ⟨66242240, by rfl⟩ : syracuseStep 88322987 = 132484481) B132484481
theorem B7656443 : Blo 1510952 7656443 := bstep (se 1 (by rfl) ⟨5742332, by rfl⟩ : syracuseStep 7656443 = 11484665) B11484665
theorem B1512443 : Blo 1510952 1512443 := bstep (se 1 (by rfl) ⟨1134332, by rfl⟩ : syracuseStep 1512443 = 2268665) B2268665
theorem B8606735 : Blo 1510952 8606735 := bstep (se 1 (by rfl) ⟨6455051, by rfl⟩ : syracuseStep 8606735 = 12910103) B12910103
theorem B1512511 : Blo 1510952 1512511 := bstep (se 1 (by rfl) ⟨1134383, by rfl⟩ : syracuseStep 1512511 = 2268767) B2268767
theorem B1938539 : Blo 1510952 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B8172683 : Blo 1510952 8172683 := bstep (se 1 (by rfl) ⟨6129512, by rfl⟩ : syracuseStep 8172683 = 12259025) B12259025
theorem B1512655 : Blo 1510952 1512655 := bstep (se 1 (by rfl) ⟨1134491, by rfl⟩ : syracuseStep 1512655 = 2268983) B2268983
theorem B2266523 : Blo 1510952 2266523 := bstep (se 1 (by rfl) ⟨1699892, by rfl⟩ : syracuseStep 2266523 = 3399785) B3399785
theorem B1512859 : Blo 1510952 1512859 := bstep (se 1 (by rfl) ⟨1134644, by rfl⟩ : syracuseStep 1512859 = 2269289) B2269289
theorem B7656929 : Blo 1510952 7656929 := bstep (se 2 (by rfl) ⟨2871348, by rfl⟩ : syracuseStep 7656929 = 5742697) B5742697
theorem B2266745 : Blo 1510952 2266745 := bstep (se 2 (by rfl) ⟨850029, by rfl⟩ : syracuseStep 2266745 = 1700059) B1700059
theorem B2266847 : Blo 1510952 2266847 := bstep (se 1 (by rfl) ⟨1700135, by rfl⟩ : syracuseStep 2266847 = 3400271) B3400271
theorem B2266943 : Blo 1510952 2266943 := bstep (se 1 (by rfl) ⟨1700207, by rfl⟩ : syracuseStep 2266943 = 3400415) B3400415
theorem B14538629 : Blo 1510952 14538629 := bstep (se 4 (by rfl) ⟨1362996, by rfl⟩ : syracuseStep 14538629 = 2725993) B2725993
theorem B31045513 : Blo 1510952 31045513 := bstep (se 2 (by rfl) ⟨11642067, by rfl⟩ : syracuseStep 31045513 = 23284135) B23284135
theorem B2725769 : Blo 1510952 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B2422727 : Blo 1510952 2422727 := bstep (se 1 (by rfl) ⟨1817045, by rfl⟩ : syracuseStep 2422727 = 3634091) B3634091
theorem B2267111 : Blo 1510952 2267111 := bstep (se 1 (by rfl) ⟨1700333, by rfl⟩ : syracuseStep 2267111 = 3400667) B3400667
theorem B1841135 : Blo 1510952 1841135 := bstep (se 1 (by rfl) ⟨1380851, by rfl⟩ : syracuseStep 1841135 = 2761703) B2761703
theorem B2267129 : Blo 1510952 2267129 := bstep (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) B1700347
theorem B2152441 : Blo 1510952 2152441 := bstep (se 2 (by rfl) ⟨807165, by rfl⟩ : syracuseStep 2152441 = 1614331) B1614331
theorem B2267231 : Blo 1510952 2267231 := bstep (se 1 (by rfl) ⟨1700423, by rfl⟩ : syracuseStep 2267231 = 3400847) B3400847
theorem B2267291 : Blo 1510952 2267291 := bstep (se 1 (by rfl) ⟨1700468, by rfl⟩ : syracuseStep 2267291 = 3400937) B3400937
theorem B2267327 : Blo 1510952 2267327 := bstep (se 1 (by rfl) ⟨1700495, by rfl⟩ : syracuseStep 2267327 = 3400991) B3400991
theorem B10344647 : Blo 1510952 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B2267369 : Blo 1510952 2267369 := bstep (se 2 (by rfl) ⟨850263, by rfl⟩ : syracuseStep 2267369 = 1700527) B1700527
theorem B5101811 : Blo 1510952 5101811 := bstep (se 1 (by rfl) ⟨3826358, by rfl⟩ : syracuseStep 5101811 = 7652717) B7652717
theorem B5101865 : Blo 1510952 5101865 := bstep (se 2 (by rfl) ⟨1913199, by rfl⟩ : syracuseStep 5101865 = 3826399) B3826399
theorem B15735215 : Blo 1510952 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B2267675 : Blo 1510952 2267675 := bstep (se 1 (by rfl) ⟨1700756, by rfl⟩ : syracuseStep 2267675 = 3401513) B3401513
theorem B2267753 : Blo 1510952 2267753 := bstep (se 2 (by rfl) ⟨850407, by rfl⟩ : syracuseStep 2267753 = 1700815) B1700815
theorem B165444227 : Blo 1510952 165444227 := bstep (se 1 (by rfl) ⟨124083170, by rfl⟩ : syracuseStep 165444227 = 248166341) B248166341
theorem B4307593 : Blo 1510952 4307593 := bstep (se 2 (by rfl) ⟨1615347, by rfl⟩ : syracuseStep 4307593 = 3230695) B3230695
theorem B82705049 : Blo 1510952 82705049 := bstep (se 2 (by rfl) ⟨31014393, by rfl⟩ : syracuseStep 82705049 = 62028787) B62028787
theorem B5741513 : Blo 1510952 5741513 := bstep (se 2 (by rfl) ⟨2153067, by rfl⟩ : syracuseStep 5741513 = 4306135) B4306135
theorem B2268281 : Blo 1510952 2268281 := bstep (se 2 (by rfl) ⟨850605, by rfl⟩ : syracuseStep 2268281 = 1701211) B1701211
theorem B7658711 : Blo 1510952 7658711 := bstep (se 1 (by rfl) ⟨5744033, by rfl⟩ : syracuseStep 7658711 = 11488067) B11488067
theorem B2268383 : Blo 1510952 2268383 := bstep (se 1 (by rfl) ⟨1701287, by rfl⟩ : syracuseStep 2268383 = 3402575) B3402575
theorem B2268425 : Blo 1510952 2268425 := bstep (se 2 (by rfl) ⟨850659, by rfl⟩ : syracuseStep 2268425 = 1701319) B1701319
theorem B10902845 : Blo 1510952 10902845 := bstep (se 3 (by rfl) ⟨2044283, by rfl⟩ : syracuseStep 10902845 = 4088567) B4088567
theorem B2268527 : Blo 1510952 2268527 := bstep (se 1 (by rfl) ⟨1701395, by rfl⟩ : syracuseStep 2268527 = 3402791) B3402791
theorem B17218979 : Blo 1510952 17218979 := bstep (se 1 (by rfl) ⟨12914234, by rfl⟩ : syracuseStep 17218979 = 25828469) B25828469
theorem B2268647 : Blo 1510952 2268647 := bstep (se 1 (by rfl) ⟨1701485, by rfl⟩ : syracuseStep 2268647 = 3402971) B3402971
theorem B1891931 : Blo 1510952 1891931 := bstep (se 1 (by rfl) ⟨1418948, by rfl⟩ : syracuseStep 1891931 = 2837897) B2837897
theorem B2268779 : Blo 1510952 2268779 := bstep (se 1 (by rfl) ⟨1701584, by rfl⟩ : syracuseStep 2268779 = 3403169) B3403169
theorem B14532205 : Blo 1510952 14532205 := bstep (se 3 (by rfl) ⟨2724788, by rfl⟩ : syracuseStep 14532205 = 5449577) B5449577
theorem B4841147 : Blo 1510952 4841147 := bstep (se 1 (by rfl) ⟨3630860, by rfl⟩ : syracuseStep 4841147 = 7261721) B7261721
theorem B3825377 : Blo 1510952 3825377 := bstep (se 2 (by rfl) ⟨1434516, by rfl⟩ : syracuseStep 3825377 = 2869033) B2869033
theorem B2268905 : Blo 1510952 2268905 := bstep (se 2 (by rfl) ⟨850839, by rfl⟩ : syracuseStep 2268905 = 1701679) B1701679
theorem B1613639 : Blo 1510952 1613639 := bstep (se 1 (by rfl) ⟨1210229, by rfl⟩ : syracuseStep 1613639 = 2420459) B2420459
theorem B5103431 : Blo 1510952 5103431 := bstep (se 1 (by rfl) ⟨3827573, by rfl⟩ : syracuseStep 5103431 = 7655147) B7655147
theorem B2269049 : Blo 1510952 2269049 := bstep (se 2 (by rfl) ⟨850893, by rfl⟩ : syracuseStep 2269049 = 1701787) B1701787
theorem B5103485 : Blo 1510952 5103485 := bstep (se 3 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 5103485 = 1913807) B1913807
theorem B2269151 : Blo 1510952 2269151 := bstep (se 1 (by rfl) ⟨1701863, by rfl⟩ : syracuseStep 2269151 = 3403727) B3403727
theorem B3399803 : Blo 1510952 3399803 := bstep (se 1 (by rfl) ⟨2549852, by rfl⟩ : syracuseStep 3399803 = 5099705) B5099705
theorem B2269391 : Blo 1510952 2269391 := bstep (se 1 (by rfl) ⟨1702043, by rfl⟩ : syracuseStep 2269391 = 3404087) B3404087
theorem B5169437 : Blo 1510952 5169437 := bstep (se 3 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 5169437 = 1938539) B1938539
theorem B5816615 : Blo 1510952 5816615 := bstep (se 1 (by rfl) ⟨4362461, by rfl⟩ : syracuseStep 5816615 = 8724923) B8724923
theorem B3400073 : Blo 1510952 3400073 := bstep (se 2 (by rfl) ⟨1275027, by rfl⟩ : syracuseStep 3400073 = 2550055) B2550055
theorem B3228167 : Blo 1510952 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B8610401 : Blo 1510952 8610401 := bstep (se 2 (by rfl) ⟨3228900, by rfl⟩ : syracuseStep 8610401 = 6457801) B6457801
theorem B5104295 : Blo 1510952 5104295 := bstep (se 1 (by rfl) ⟨3828221, by rfl⟩ : syracuseStep 5104295 = 7656443) B7656443
theorem B5448455 : Blo 1510952 5448455 := bstep (se 1 (by rfl) ⟨4086341, by rfl⟩ : syracuseStep 5448455 = 8172683) B8172683
theorem B3228457 : Blo 1510952 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B5743457 : Blo 1510952 5743457 := bstep (se 2 (by rfl) ⟨2153796, by rfl⟩ : syracuseStep 5743457 = 4307593) B4307593
theorem B5104619 : Blo 1510952 5104619 := bstep (se 1 (by rfl) ⟨3828464, by rfl⟩ : syracuseStep 5104619 = 7656929) B7656929
theorem B9692419 : Blo 1510952 9692419 := bstep (se 1 (by rfl) ⟨7269314, by rfl⟩ : syracuseStep 9692419 = 14538629) B14538629
theorem B1615151 : Blo 1510952 1615151 := bstep (se 1 (by rfl) ⟨1211363, by rfl⟩ : syracuseStep 1615151 = 2422727) B2422727
theorem B894592349 : Blo 1510952 894592349 := bstep (se 3 (by rfl) ⟨167736065, by rfl⟩ : syracuseStep 894592349 = 335472131) B335472131
theorem B3401207 : Blo 1510952 3401207 := bstep (se 1 (by rfl) ⟨2550905, by rfl⟩ : syracuseStep 3401207 = 5101811) B5101811
theorem B3401243 : Blo 1510952 3401243 := bstep (se 1 (by rfl) ⟨2550932, by rfl⟩ : syracuseStep 3401243 = 5101865) B5101865
theorem B2868767 : Blo 1510952 2868767 := bstep (se 1 (by rfl) ⟨2151575, by rfl⟩ : syracuseStep 2868767 = 4303151) B4303151
theorem B3827675 : Blo 1510952 3827675 := bstep (se 1 (by rfl) ⟨2870756, by rfl⟩ : syracuseStep 3827675 = 5741513) B5741513
theorem B7268449 : Blo 1510952 7268449 := bstep (se 2 (by rfl) ⟨2725668, by rfl⟩ : syracuseStep 7268449 = 5451337) B5451337
theorem B5105807 : Blo 1510952 5105807 := bstep (se 1 (by rfl) ⟨3829355, by rfl⟩ : syracuseStep 5105807 = 7658711) B7658711
theorem B19376273 : Blo 1510952 19376273 := bstep (se 2 (by rfl) ⟨7266102, by rfl⟩ : syracuseStep 19376273 = 14532205) B14532205
theorem B2869435 : Blo 1510952 2869435 := bstep (se 1 (by rfl) ⟨2152076, by rfl⟩ : syracuseStep 2869435 = 4304153) B4304153
theorem B4303037 : Blo 1510952 4303037 := bstep (se 3 (by rfl) ⟨806819, by rfl⟩ : syracuseStep 4303037 = 1613639) B1613639
theorem B7268563 : Blo 1510952 7268563 := bstep (se 1 (by rfl) ⟨5451422, by rfl⟩ : syracuseStep 7268563 = 10902845) B10902845
theorem B11479319 : Blo 1510952 11479319 := bstep (se 1 (by rfl) ⟨8609489, by rfl⟩ : syracuseStep 11479319 = 17218979) B17218979
theorem B7268717 : Blo 1510952 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B12257725 : Blo 1510952 12257725 := bstep (se 3 (by rfl) ⟨2298323, by rfl⟩ : syracuseStep 12257725 = 4596647) B4596647
theorem B2550251 : Blo 1510952 2550251 := bstep (se 1 (by rfl) ⟨1912688, by rfl⟩ : syracuseStep 2550251 = 3825377) B3825377
theorem B3402233 : Blo 1510952 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B3402287 : Blo 1510952 3402287 := bstep (se 1 (by rfl) ⟨2551715, by rfl⟩ : syracuseStep 3402287 = 5103431) B5103431
theorem B3402323 : Blo 1510952 3402323 := bstep (se 1 (by rfl) ⟨2551742, by rfl⟩ : syracuseStep 3402323 = 5103485) B5103485
theorem B4909693 : Blo 1510952 4909693 := bstep (se 3 (by rfl) ⟨920567, by rfl⟩ : syracuseStep 4909693 = 1841135) B1841135
theorem B2869921 : Blo 1510952 2869921 := bstep (se 2 (by rfl) ⟨1076220, by rfl⟩ : syracuseStep 2869921 = 2152441) B2152441
theorem B3402503 : Blo 1510952 3402503 := bstep (se 1 (by rfl) ⟨2551877, by rfl⟩ : syracuseStep 3402503 = 5103755) B5103755
theorem B10898231 : Blo 1510952 10898231 := bstep (se 1 (by rfl) ⟨8173673, by rfl⟩ : syracuseStep 10898231 = 16347347) B16347347
theorem B25824095 : Blo 1510952 25824095 := bstep (se 1 (by rfl) ⟨19368071, by rfl⟩ : syracuseStep 25824095 = 38736143) B38736143
theorem B3402719 : Blo 1510952 3402719 := bstep (se 1 (by rfl) ⟨2552039, by rfl⟩ : syracuseStep 3402719 = 5104079) B5104079
theorem B3828809 : Blo 1510952 3828809 := bstep (se 2 (by rfl) ⟨1435803, by rfl⟩ : syracuseStep 3828809 = 2871607) B2871607
theorem B2550953 : Blo 1510952 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B3402935 : Blo 1510952 3402935 := bstep (se 1 (by rfl) ⟨2552201, by rfl⟩ : syracuseStep 3402935 = 5104403) B5104403
theorem B5737823 : Blo 1510952 5737823 := bstep (se 1 (by rfl) ⟨4303367, by rfl⟩ : syracuseStep 5737823 = 8606735) B8606735
theorem B1511015 : Blo 1510952 1511015 := bstep (se 1 (by rfl) ⟨1133261, by rfl⟩ : syracuseStep 1511015 = 2266523) B2266523
theorem B8728249 : Blo 1510952 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B3403511 : Blo 1510952 3403511 := bstep (se 1 (by rfl) ⟨2552633, by rfl⟩ : syracuseStep 3403511 = 5105267) B5105267
theorem B1511163 : Blo 1510952 1511163 := bstep (se 1 (by rfl) ⟨1133372, by rfl⟩ : syracuseStep 1511163 = 2266745) B2266745
theorem B2551547 : Blo 1510952 2551547 := bstep (se 1 (by rfl) ⟨1913660, by rfl⟩ : syracuseStep 2551547 = 3827321) B3827321
theorem B1511231 : Blo 1510952 1511231 := bstep (se 1 (by rfl) ⟨1133423, by rfl⟩ : syracuseStep 1511231 = 2266847) B2266847
theorem B3403583 : Blo 1510952 3403583 := bstep (se 1 (by rfl) ⟨2552687, by rfl⟩ : syracuseStep 3403583 = 5105375) B5105375
theorem B1511295 : Blo 1510952 1511295 := bstep (se 1 (by rfl) ⟨1133471, by rfl⟩ : syracuseStep 1511295 = 2266943) B2266943
theorem B3403691 : Blo 1510952 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B1511407 : Blo 1510952 1511407 := bstep (se 1 (by rfl) ⟨1133555, by rfl⟩ : syracuseStep 1511407 = 2267111) B2267111
theorem B1511419 : Blo 1510952 1511419 := bstep (se 1 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 1511419 = 2267129) B2267129
theorem B1511487 : Blo 1510952 1511487 := bstep (se 1 (by rfl) ⟨1133615, by rfl⟩ : syracuseStep 1511487 = 2267231) B2267231
theorem B1511527 : Blo 1510952 1511527 := bstep (se 1 (by rfl) ⟨1133645, by rfl⟩ : syracuseStep 1511527 = 2267291) B2267291
theorem B1511551 : Blo 1510952 1511551 := bstep (se 1 (by rfl) ⟨1133663, by rfl⟩ : syracuseStep 1511551 = 2267327) B2267327
theorem B1511579 : Blo 1510952 1511579 := bstep (se 1 (by rfl) ⟨1133684, by rfl⟩ : syracuseStep 1511579 = 2267369) B2267369
theorem B3633427 : Blo 1510952 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B3404051 : Blo 1510952 3404051 := bstep (se 1 (by rfl) ⟨2553038, by rfl⟩ : syracuseStep 3404051 = 5106077) B5106077
theorem B10490143 : Blo 1510952 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B1511783 : Blo 1510952 1511783 := bstep (se 1 (by rfl) ⟨1133837, by rfl⟩ : syracuseStep 1511783 = 2267675) B2267675
theorem B1511835 : Blo 1510952 1511835 := bstep (se 1 (by rfl) ⟨1133876, by rfl⟩ : syracuseStep 1511835 = 2267753) B2267753
theorem B55136699 : Blo 1510952 55136699 := bstep (se 1 (by rfl) ⟨41352524, by rfl⟩ : syracuseStep 55136699 = 82705049) B82705049
theorem B14529131 : Blo 1510952 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B14938799 : Blo 1510952 14938799 := bstep (se 1 (by rfl) ⟨11204099, by rfl⟩ : syracuseStep 14938799 = 22408199) B22408199
theorem B1512187 : Blo 1510952 1512187 := bstep (se 1 (by rfl) ⟨1134140, by rfl⟩ : syracuseStep 1512187 = 2268281) B2268281
theorem B1700671 : Blo 1510952 1700671 := bstep (se 1 (by rfl) ⟨1275503, by rfl⟩ : syracuseStep 1700671 = 2551007) B2551007
theorem B1512255 : Blo 1510952 1512255 := bstep (se 1 (by rfl) ⟨1134191, by rfl⟩ : syracuseStep 1512255 = 2268383) B2268383
theorem B1512283 : Blo 1510952 1512283 := bstep (se 1 (by rfl) ⟨1134212, by rfl⟩ : syracuseStep 1512283 = 2268425) B2268425
theorem B1512351 : Blo 1510952 1512351 := bstep (se 1 (by rfl) ⟨1134263, by rfl⟩ : syracuseStep 1512351 = 2268527) B2268527
theorem B1512431 : Blo 1510952 1512431 := bstep (se 1 (by rfl) ⟨1134323, by rfl⟩ : syracuseStep 1512431 = 2268647) B2268647
theorem B1512519 : Blo 1510952 1512519 := bstep (se 1 (by rfl) ⟨1134389, by rfl⟩ : syracuseStep 1512519 = 2268779) B2268779
theorem B1700959 : Blo 1510952 1700959 := bstep (se 1 (by rfl) ⟨1275719, by rfl⟩ : syracuseStep 1700959 = 2551439) B2551439
theorem B6993001 : Blo 1510952 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B1512603 : Blo 1510952 1512603 := bstep (se 1 (by rfl) ⟨1134452, by rfl⟩ : syracuseStep 1512603 = 2268905) B2268905
theorem B1512699 : Blo 1510952 1512699 := bstep (se 1 (by rfl) ⟨1134524, by rfl⟩ : syracuseStep 1512699 = 2269049) B2269049
theorem B8615231 : Blo 1510952 8615231 := bstep (se 1 (by rfl) ⟨6461423, by rfl⟩ : syracuseStep 8615231 = 12922847) B12922847
theorem B1512767 : Blo 1510952 1512767 := bstep (se 1 (by rfl) ⟨1134575, by rfl⟩ : syracuseStep 1512767 = 2269151) B2269151
theorem B1512935 : Blo 1510952 1512935 := bstep (se 1 (by rfl) ⟨1134701, by rfl⟩ : syracuseStep 1512935 = 2269403) B2269403
theorem B2266607 : Blo 1510952 2266607 := bstep (se 1 (by rfl) ⟨1699955, by rfl⟩ : syracuseStep 2266607 = 3399911) B3399911
theorem B1512943 : Blo 1510952 1512943 := bstep (se 1 (by rfl) ⟨1134707, by rfl⟩ : syracuseStep 1512943 = 2269415) B2269415
theorem B1914607 : Blo 1510952 1914607 := bstep (se 1 (by rfl) ⟨1435955, by rfl⟩ : syracuseStep 1914607 = 2871911) B2871911
theorem B9688855 : Blo 1510952 9688855 := bstep (se 1 (by rfl) ⟨7266641, by rfl⟩ : syracuseStep 9688855 = 14533283) B14533283
theorem B9197383 : Blo 1510952 9197383 := bstep (se 1 (by rfl) ⟨6898037, by rfl⟩ : syracuseStep 9197383 = 13796075) B13796075
theorem B1816411 : Blo 1510952 1816411 := bstep (se 1 (by rfl) ⟨1362308, by rfl⟩ : syracuseStep 1816411 = 2724617) B2724617
theorem B2267003 : Blo 1510952 2267003 := bstep (se 1 (by rfl) ⟨1700252, by rfl⟩ : syracuseStep 2267003 = 3400505) B3400505
theorem B2267039 : Blo 1510952 2267039 := bstep (se 1 (by rfl) ⟨1700279, by rfl⟩ : syracuseStep 2267039 = 3400559) B3400559
theorem B58881991 : Blo 1510952 58881991 := bstep (se 1 (by rfl) ⟨44161493, by rfl⟩ : syracuseStep 58881991 = 88322987) B88322987
theorem B4659191 : Blo 1510952 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B11474945 : Blo 1510952 11474945 := bstep (se 2 (by rfl) ⟨4303104, by rfl⟩ : syracuseStep 11474945 = 8606209) B8606209
theorem B2267273 : Blo 1510952 2267273 := bstep (se 2 (by rfl) ⟨850227, by rfl⟩ : syracuseStep 2267273 = 1700455) B1700455
theorem B2267423 : Blo 1510952 2267423 := bstep (se 1 (by rfl) ⟨1700567, by rfl⟩ : syracuseStep 2267423 = 3401135) B3401135
theorem B16357727 : Blo 1510952 16357727 := bstep (se 1 (by rfl) ⟨12268295, by rfl⟩ : syracuseStep 16357727 = 24536591) B24536591
theorem B11475431 : Blo 1510952 11475431 := bstep (se 1 (by rfl) ⟨8606573, by rfl⟩ : syracuseStep 11475431 = 17213147) B17213147
theorem B5741057 : Blo 1510952 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B6896249 : Blo 1510952 6896249 := bstep (se 2 (by rfl) ⟨2586093, by rfl⟩ : syracuseStep 6896249 = 5172187) B5172187
theorem B5741239 : Blo 1510952 5741239 := bstep (se 1 (by rfl) ⟨4305929, by rfl⟩ : syracuseStep 5741239 = 8611859) B8611859
theorem B6462175 : Blo 1510952 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B6896431 : Blo 1510952 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B2267975 : Blo 1510952 2267975 := bstep (se 1 (by rfl) ⟨1700981, by rfl⟩ : syracuseStep 2267975 = 3401963) B3401963
theorem B5045149 : Blo 1510952 5045149 := bstep (se 3 (by rfl) ⟨945965, by rfl⟩ : syracuseStep 5045149 = 1891931) B1891931
theorem B110296151 : Blo 1510952 110296151 := bstep (se 1 (by rfl) ⟨82722113, by rfl⟩ : syracuseStep 110296151 = 165444227) B165444227
theorem B12909725 : Blo 1510952 12909725 := bstep (se 3 (by rfl) ⟨2420573, by rfl⟩ : syracuseStep 12909725 = 4841147) B4841147
theorem B5741999 : Blo 1510952 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B149085809 : Blo 1510952 149085809 := bstep (se 2 (by rfl) ⟨55907178, by rfl⟩ : syracuseStep 149085809 = 111814357) B111814357
theorem B25837217 : Blo 1510952 25837217 := bstep (se 2 (by rfl) ⟨9688956, by rfl⟩ : syracuseStep 25837217 = 19377913) B19377913
theorem B2268839 : Blo 1510952 2268839 := bstep (se 1 (by rfl) ⟨1701629, by rfl⟩ : syracuseStep 2268839 = 3403259) B3403259
theorem B5447387 : Blo 1510952 5447387 := bstep (se 1 (by rfl) ⟨4085540, by rfl⟩ : syracuseStep 5447387 = 8171081) B8171081
theorem B3825427 : Blo 1510952 3825427 := bstep (se 1 (by rfl) ⟨2869070, by rfl⟩ : syracuseStep 3825427 = 5738141) B5738141
theorem B2268959 : Blo 1510952 2268959 := bstep (se 1 (by rfl) ⟨1701719, by rfl⟩ : syracuseStep 2268959 = 3403439) B3403439
theorem B41394017 : Blo 1510952 41394017 := bstep (se 2 (by rfl) ⟨15522756, by rfl⟩ : syracuseStep 41394017 = 31045513) B31045513
theorem B1613767 : Blo 1510952 1613767 := bstep (se 1 (by rfl) ⟨1210325, by rfl⟩ : syracuseStep 1613767 = 2420651) B2420651
theorem B9691265 : Blo 1510952 9691265 := bstep (se 2 (by rfl) ⟨3634224, by rfl⟩ : syracuseStep 9691265 = 7268449) B7268449
theorem B2269367 : Blo 1510952 2269367 := bstep (se 1 (by rfl) ⟨1702025, by rfl⟩ : syracuseStep 2269367 = 3404051) B3404051
theorem B3825913 : Blo 1510952 3825913 := bstep (se 2 (by rfl) ⟨1434717, by rfl⟩ : syracuseStep 3825913 = 2869435) B2869435
theorem B9691417 : Blo 1510952 9691417 := bstep (se 2 (by rfl) ⟨3634281, by rfl⟩ : syracuseStep 9691417 = 7268563) B7268563
theorem B36757799 : Blo 1510952 36757799 := bstep (se 1 (by rfl) ⟨27568349, by rfl⟩ : syracuseStep 36757799 = 55136699) B55136699
theorem B16343633 : Blo 1510952 16343633 := bstep (se 2 (by rfl) ⟨6128862, by rfl⟩ : syracuseStep 16343633 = 12257725) B12257725
theorem B6546257 : Blo 1510952 6546257 := bstep (se 2 (by rfl) ⟨2454846, by rfl⟩ : syracuseStep 6546257 = 4909693) B4909693
theorem B3826561 : Blo 1510952 3826561 := bstep (se 2 (by rfl) ⟨1434960, by rfl⟩ : syracuseStep 3826561 = 2869921) B2869921
theorem B5743487 : Blo 1510952 5743487 := bstep (se 1 (by rfl) ⟨4307615, by rfl⟩ : syracuseStep 5743487 = 8615231) B8615231
theorem B596394899 : Blo 1510952 596394899 := bstep (se 1 (by rfl) ⟨447296174, by rfl⟩ : syracuseStep 596394899 = 894592349) B894592349
theorem B19383245 : Blo 1510952 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B6726865 : Blo 1510952 6726865 := bstep (se 2 (by rfl) ⟨2522574, by rfl⟩ : syracuseStep 6726865 = 5045149) B5045149
theorem B3106127 : Blo 1510952 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B2868691 : Blo 1510952 2868691 := bstep (se 1 (by rfl) ⟨2151518, by rfl⟩ : syracuseStep 2868691 = 4303037) B4303037
theorem B9324001 : Blo 1510952 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B7652879 : Blo 1510952 7652879 := bstep (se 1 (by rfl) ⟨5739659, by rfl⟩ : syracuseStep 7652879 = 11479319) B11479319
theorem B3827371 : Blo 1510952 3827371 := bstep (se 1 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 3827371 = 5741057) B5741057
theorem B4597499 : Blo 1510952 4597499 := bstep (se 1 (by rfl) ⟨3448124, by rfl⟩ : syracuseStep 4597499 = 6896249) B6896249
theorem B3827999 : Blo 1510952 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B3631591 : Blo 1510952 3631591 := bstep (se 1 (by rfl) ⟨2723693, by rfl⟩ : syracuseStep 3631591 = 5447387) B5447387
theorem B13986857 : Blo 1510952 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B9686087 : Blo 1510952 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B3402863 : Blo 1510952 3402863 := bstep (se 1 (by rfl) ⟨2552147, by rfl⟩ : syracuseStep 3402863 = 5104295) B5104295
theorem B3632303 : Blo 1510952 3632303 := bstep (se 1 (by rfl) ⟨2724227, by rfl⟩ : syracuseStep 3632303 = 5448455) B5448455
theorem B3828971 : Blo 1510952 3828971 := bstep (se 1 (by rfl) ⟨2871728, by rfl⟩ : syracuseStep 3828971 = 5743457) B5743457
theorem B3403079 : Blo 1510952 3403079 := bstep (se 1 (by rfl) ⟨2552309, by rfl⟩ : syracuseStep 3403079 = 5104619) B5104619
theorem B7654985 : Blo 1510952 7654985 := bstep (se 2 (by rfl) ⟨2870619, by rfl⟩ : syracuseStep 7654985 = 5741239) B5741239
theorem B1511071 : Blo 1510952 1511071 := bstep (se 1 (by rfl) ⟨1133303, by rfl⟩ : syracuseStep 1511071 = 2266607) B2266607
theorem B1912511 : Blo 1510952 1912511 := bstep (se 1 (by rfl) ⟨1434383, by rfl⟩ : syracuseStep 1912511 = 2868767) B2868767
theorem B4304609 : Blo 1510952 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B1511335 : Blo 1510952 1511335 := bstep (se 1 (by rfl) ⟨1133501, by rfl⟩ : syracuseStep 1511335 = 2267003) B2267003
theorem B1511359 : Blo 1510952 1511359 := bstep (se 1 (by rfl) ⟨1133519, by rfl⟩ : syracuseStep 1511359 = 2267039) B2267039
theorem B2551783 : Blo 1510952 2551783 := bstep (se 1 (by rfl) ⟨1913837, by rfl⟩ : syracuseStep 2551783 = 3827675) B3827675
theorem B1511515 : Blo 1510952 1511515 := bstep (se 1 (by rfl) ⟨1133636, by rfl⟩ : syracuseStep 1511515 = 2267273) B2267273
theorem B3403871 : Blo 1510952 3403871 := bstep (se 1 (by rfl) ⟨2552903, by rfl⟩ : syracuseStep 3403871 = 5105807) B5105807
theorem B19378277 : Blo 1510952 19378277 := bstep (se 4 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 19378277 = 3633427) B3633427
theorem B1511615 : Blo 1510952 1511615 := bstep (se 1 (by rfl) ⟨1133711, by rfl⟩ : syracuseStep 1511615 = 2267423) B2267423
theorem B1700167 : Blo 1510952 1700167 := bstep (se 1 (by rfl) ⟨1275125, by rfl⟩ : syracuseStep 1700167 = 2550251) B2550251
theorem B12923225 : Blo 1510952 12923225 := bstep (se 2 (by rfl) ⟨4846209, by rfl⟩ : syracuseStep 12923225 = 9692419) B9692419
theorem B159347189 : Blo 1510952 159347189 := bstep (se 5 (by rfl) ⟨7469399, by rfl⟩ : syracuseStep 159347189 = 14938799) B14938799
theorem B1511983 : Blo 1510952 1511983 := bstep (se 1 (by rfl) ⟨1133987, by rfl⟩ : syracuseStep 1511983 = 2267975) B2267975
theorem B17216063 : Blo 1510952 17216063 := bstep (se 1 (by rfl) ⟨12912047, by rfl⟩ : syracuseStep 17216063 = 25824095) B25824095
theorem B2552539 : Blo 1510952 2552539 := bstep (se 1 (by rfl) ⟨1914404, by rfl⟩ : syracuseStep 2552539 = 3828809) B3828809
theorem B8606483 : Blo 1510952 8606483 := bstep (se 1 (by rfl) ⟨6454862, by rfl⟩ : syracuseStep 8606483 = 12909725) B12909725
theorem B1700635 : Blo 1510952 1700635 := bstep (se 1 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 1700635 = 2550953) B2550953
theorem B29061949 : Blo 1510952 29061949 := bstep (se 3 (by rfl) ⟨5449115, by rfl⟩ : syracuseStep 29061949 = 10898231) B10898231
theorem B11637665 : Blo 1510952 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B2552809 : Blo 1510952 2552809 := bstep (se 2 (by rfl) ⟨957303, by rfl⟩ : syracuseStep 2552809 = 1914607) B1914607
theorem B5100569 : Blo 1510952 5100569 := bstep (se 2 (by rfl) ⟨1912713, by rfl⟩ : syracuseStep 5100569 = 3825427) B3825427
theorem B99390539 : Blo 1510952 99390539 := bstep (se 1 (by rfl) ⟨74542904, by rfl⟩ : syracuseStep 99390539 = 149085809) B149085809
theorem B17224811 : Blo 1510952 17224811 := bstep (se 1 (by rfl) ⟨12918608, by rfl⟩ : syracuseStep 17224811 = 25837217) B25837217
theorem B1512559 : Blo 1510952 1512559 := bstep (se 1 (by rfl) ⟨1134419, by rfl⟩ : syracuseStep 1512559 = 2268839) B2268839
theorem B2421881 : Blo 1510952 2421881 := bstep (se 2 (by rfl) ⟨908205, by rfl⟩ : syracuseStep 2421881 = 1816411) B1816411
theorem B1701031 : Blo 1510952 1701031 := bstep (se 1 (by rfl) ⟨1275773, by rfl⟩ : syracuseStep 1701031 = 2551547) B2551547
theorem B1512639 : Blo 1510952 1512639 := bstep (se 1 (by rfl) ⟨1134479, by rfl⟩ : syracuseStep 1512639 = 2268959) B2268959
theorem B27596011 : Blo 1510952 27596011 := bstep (se 1 (by rfl) ⟨20697008, by rfl⟩ : syracuseStep 27596011 = 41394017) B41394017
theorem B78509321 : Blo 1510952 78509321 := bstep (se 2 (by rfl) ⟨29440995, by rfl⟩ : syracuseStep 78509321 = 58881991) B58881991
theorem B2151689 : Blo 1510952 2151689 := bstep (se 2 (by rfl) ⟨806883, by rfl⟩ : syracuseStep 2151689 = 1613767) B1613767
theorem B2266535 : Blo 1510952 2266535 := bstep (se 1 (by rfl) ⟨1699901, by rfl⟩ : syracuseStep 2266535 = 3399803) B3399803
theorem B1512927 : Blo 1510952 1512927 := bstep (se 1 (by rfl) ⟨1134695, by rfl⟩ : syracuseStep 1512927 = 2269391) B2269391
theorem B3446291 : Blo 1510952 3446291 := bstep (se 1 (by rfl) ⟨2584718, by rfl⟩ : syracuseStep 3446291 = 5169437) B5169437
theorem B2266715 : Blo 1510952 2266715 := bstep (se 1 (by rfl) ⟨1700036, by rfl⟩ : syracuseStep 2266715 = 3400073) B3400073
theorem B2152111 : Blo 1510952 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B5740267 : Blo 1510952 5740267 := bstep (se 1 (by rfl) ⟨4305200, by rfl⟩ : syracuseStep 5740267 = 8610401) B8610401
theorem B62043893 : Blo 1510952 62043893 := bstep (se 5 (by rfl) ⟨2908307, by rfl⟩ : syracuseStep 62043893 = 5816615) B5816615
theorem B4307069 : Blo 1510952 4307069 := bstep (se 3 (by rfl) ⟨807575, by rfl⟩ : syracuseStep 4307069 = 1615151) B1615151
theorem B43620605 : Blo 1510952 43620605 := bstep (se 3 (by rfl) ⟨8178863, by rfl⟩ : syracuseStep 43620605 = 16357727) B16357727
theorem B8616233 : Blo 1510952 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B2267471 : Blo 1510952 2267471 := bstep (se 1 (by rfl) ⟨1700603, by rfl⟩ : syracuseStep 2267471 = 3401207) B3401207
theorem B2267495 : Blo 1510952 2267495 := bstep (se 1 (by rfl) ⟨1700621, by rfl⟩ : syracuseStep 2267495 = 3401243) B3401243
theorem B2267561 : Blo 1510952 2267561 := bstep (se 2 (by rfl) ⟨850335, by rfl⟩ : syracuseStep 2267561 = 1700671) B1700671
theorem B7649963 : Blo 1510952 7649963 := bstep (se 1 (by rfl) ⟨5737472, by rfl⟩ : syracuseStep 7649963 = 11474945) B11474945
theorem B12917515 : Blo 1510952 12917515 := bstep (se 1 (by rfl) ⟨9688136, by rfl⟩ : syracuseStep 12917515 = 19376273) B19376273
theorem B2267945 : Blo 1510952 2267945 := bstep (se 2 (by rfl) ⟨850479, by rfl⟩ : syracuseStep 2267945 = 1700959) B1700959
theorem B36780965 : Blo 1510952 36780965 := bstep (se 4 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 36780965 = 6896431) B6896431
theorem B7650287 : Blo 1510952 7650287 := bstep (se 1 (by rfl) ⟨5737715, by rfl⟩ : syracuseStep 7650287 = 11475431) B11475431
theorem B2268155 : Blo 1510952 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B2268191 : Blo 1510952 2268191 := bstep (se 1 (by rfl) ⟨1701143, by rfl⟩ : syracuseStep 2268191 = 3402287) B3402287
theorem B2268215 : Blo 1510952 2268215 := bstep (se 1 (by rfl) ⟨1701161, by rfl⟩ : syracuseStep 2268215 = 3402323) B3402323
theorem B2268335 : Blo 1510952 2268335 := bstep (se 1 (by rfl) ⟨1701251, by rfl⟩ : syracuseStep 2268335 = 3402503) B3402503
theorem B2268479 : Blo 1510952 2268479 := bstep (se 1 (by rfl) ⟨1701359, by rfl⟩ : syracuseStep 2268479 = 3402719) B3402719
theorem B73530767 : Blo 1510952 73530767 := bstep (se 1 (by rfl) ⟨55148075, by rfl⟩ : syracuseStep 73530767 = 110296151) B110296151
theorem B2268623 : Blo 1510952 2268623 := bstep (se 1 (by rfl) ⟨1701467, by rfl⟩ : syracuseStep 2268623 = 3402935) B3402935
theorem B3825215 : Blo 1510952 3825215 := bstep (se 1 (by rfl) ⟨2868911, by rfl⟩ : syracuseStep 3825215 = 5737823) B5737823
theorem B12918473 : Blo 1510952 12918473 := bstep (se 2 (by rfl) ⟨4844427, by rfl⟩ : syracuseStep 12918473 = 9688855) B9688855
theorem B12263177 : Blo 1510952 12263177 := bstep (se 2 (by rfl) ⟨4598691, by rfl⟩ : syracuseStep 12263177 = 9197383) B9197383
theorem B2269007 : Blo 1510952 2269007 := bstep (se 1 (by rfl) ⟨1701755, by rfl⟩ : syracuseStep 2269007 = 3403511) B3403511
theorem B2269055 : Blo 1510952 2269055 := bstep (se 1 (by rfl) ⟨1701791, by rfl⟩ : syracuseStep 2269055 = 3403583) B3403583
theorem B2269127 : Blo 1510952 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B2269247 : Blo 1510952 2269247 := bstep (se 1 (by rfl) ⟨1701935, by rfl⟩ : syracuseStep 2269247 = 3403871) B3403871
theorem B12918851 : Blo 1510952 12918851 := bstep (se 1 (by rfl) ⟨9689138, by rfl⟩ : syracuseStep 12918851 = 19378277) B19378277
theorem B11477375 : Blo 1510952 11477375 := bstep (se 1 (by rfl) ⟨8608031, by rfl⟩ : syracuseStep 11477375 = 17216063) B17216063
theorem B10895755 : Blo 1510952 10895755 := bstep (se 1 (by rfl) ⟨8171816, by rfl⟩ : syracuseStep 10895755 = 16343633) B16343633
theorem B7758443 : Blo 1510952 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B4842121 : Blo 1510952 4842121 := bstep (se 2 (by rfl) ⟨1815795, by rfl⟩ : syracuseStep 4842121 = 3631591) B3631591
theorem B3400379 : Blo 1510952 3400379 := bstep (se 1 (by rfl) ⟨2550284, by rfl⟩ : syracuseStep 3400379 = 5100569) B5100569
theorem B1614587 : Blo 1510952 1614587 := bstep (se 1 (by rfl) ⟨1210940, by rfl⟩ : syracuseStep 1614587 = 2421881) B2421881
theorem B52339547 : Blo 1510952 52339547 := bstep (se 1 (by rfl) ⟨39254660, by rfl⟩ : syracuseStep 52339547 = 78509321) B78509321
theorem B8283005 : Blo 1510952 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B38749265 : Blo 1510952 38749265 := bstep (se 2 (by rfl) ⟨14530974, by rfl⟩ : syracuseStep 38749265 = 29061949) B29061949
theorem B41362595 : Blo 1510952 41362595 := bstep (se 1 (by rfl) ⟨31021946, by rfl⟩ : syracuseStep 41362595 = 62043893) B62043893
theorem B3064999 : Blo 1510952 3064999 := bstep (se 1 (by rfl) ⟨2298749, by rfl⟩ : syracuseStep 3064999 = 4597499) B4597499
theorem B5744155 : Blo 1510952 5744155 := bstep (se 1 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 5744155 = 8616233) B8616233
theorem B24520643 : Blo 1510952 24520643 := bstep (se 1 (by rfl) ⟨18390482, by rfl⟩ : syracuseStep 24520643 = 36780965) B36780965
theorem B9324571 : Blo 1510952 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B6457391 : Blo 1510952 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B2869481 : Blo 1510952 2869481 := bstep (se 2 (by rfl) ⟨1076055, by rfl⟩ : syracuseStep 2869481 = 2152111) B2152111
theorem B7653689 : Blo 1510952 7653689 := bstep (se 2 (by rfl) ⟨2870133, by rfl⟩ : syracuseStep 7653689 = 5740267) B5740267
theorem B2550143 : Blo 1510952 2550143 := bstep (se 1 (by rfl) ⟨1912607, by rfl⟩ : syracuseStep 2550143 = 3825215) B3825215
theorem B8612315 : Blo 1510952 8612315 := bstep (se 1 (by rfl) ⟨6459236, by rfl⟩ : syracuseStep 8612315 = 12918473) B12918473
theorem B2869739 : Blo 1510952 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B3402377 : Blo 1510952 3402377 := bstep (se 2 (by rfl) ⟨1275891, by rfl⟩ : syracuseStep 3402377 = 2551783) B2551783
theorem B24505199 : Blo 1510952 24505199 := bstep (se 1 (by rfl) ⟨18378899, by rfl⟩ : syracuseStep 24505199 = 36757799) B36757799
theorem B12921889 : Blo 1510952 12921889 := bstep (se 2 (by rfl) ⟨4845708, by rfl⟩ : syracuseStep 12921889 = 9691417) B9691417
theorem B9686141 : Blo 1510952 9686141 := bstep (se 3 (by rfl) ⟨1816151, by rfl⟩ : syracuseStep 9686141 = 3632303) B3632303
theorem B5737655 : Blo 1510952 5737655 := bstep (se 1 (by rfl) ⟨4303241, by rfl⟩ : syracuseStep 5737655 = 8606483) B8606483
theorem B3828991 : Blo 1510952 3828991 := bstep (se 1 (by rfl) ⟨2871743, by rfl⟩ : syracuseStep 3828991 = 5743487) B5743487
theorem B12922163 : Blo 1510952 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B5737837 : Blo 1510952 5737837 := bstep (se 3 (by rfl) ⟨1075844, by rfl⟩ : syracuseStep 5737837 = 2151689) B2151689
theorem B66260359 : Blo 1510952 66260359 := bstep (se 1 (by rfl) ⟨49695269, by rfl⟩ : syracuseStep 66260359 = 99390539) B99390539
theorem B1511023 : Blo 1510952 1511023 := bstep (se 1 (by rfl) ⟨1133267, by rfl⟩ : syracuseStep 1511023 = 2266535) B2266535
theorem B3403385 : Blo 1510952 3403385 := bstep (se 2 (by rfl) ⟨1276269, by rfl⟩ : syracuseStep 3403385 = 2552539) B2552539
theorem B2297527 : Blo 1510952 2297527 := bstep (se 1 (by rfl) ⟨1723145, by rfl⟩ : syracuseStep 2297527 = 3446291) B3446291
theorem B17223353 : Blo 1510952 17223353 := bstep (se 2 (by rfl) ⟨6458757, by rfl⟩ : syracuseStep 17223353 = 12917515) B12917515
theorem B1511143 : Blo 1510952 1511143 := bstep (se 1 (by rfl) ⟨1133357, by rfl⟩ : syracuseStep 1511143 = 2266715) B2266715
theorem B3403745 : Blo 1510952 3403745 := bstep (se 2 (by rfl) ⟨1276404, by rfl⟩ : syracuseStep 3403745 = 2552809) B2552809
theorem B2871379 : Blo 1510952 2871379 := bstep (se 1 (by rfl) ⟨2153534, by rfl⟩ : syracuseStep 2871379 = 4307069) B4307069
theorem B2551999 : Blo 1510952 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B1511647 : Blo 1510952 1511647 := bstep (se 1 (by rfl) ⟨1133735, by rfl⟩ : syracuseStep 1511647 = 2267471) B2267471
theorem B1511663 : Blo 1510952 1511663 := bstep (se 1 (by rfl) ⟨1133747, by rfl⟩ : syracuseStep 1511663 = 2267495) B2267495
theorem B1511707 : Blo 1510952 1511707 := bstep (se 1 (by rfl) ⟨1133780, by rfl⟩ : syracuseStep 1511707 = 2267561) B2267561
theorem B36794681 : Blo 1510952 36794681 := bstep (se 2 (by rfl) ⟨13798005, by rfl⟩ : syracuseStep 36794681 = 27596011) B27596011
theorem B5099975 : Blo 1510952 5099975 := bstep (se 1 (by rfl) ⟨3824981, by rfl⟩ : syracuseStep 5099975 = 7649963) B7649963
theorem B5100029 : Blo 1510952 5100029 := bstep (se 3 (by rfl) ⟨956255, by rfl⟩ : syracuseStep 5100029 = 1912511) B1912511
theorem B1511963 : Blo 1510952 1511963 := bstep (se 1 (by rfl) ⟨1133972, by rfl⟩ : syracuseStep 1511963 = 2267945) B2267945
theorem B12432001 : Blo 1510952 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B5100191 : Blo 1510952 5100191 := bstep (se 1 (by rfl) ⟨3825143, by rfl⟩ : syracuseStep 5100191 = 7650287) B7650287
theorem B1512103 : Blo 1510952 1512103 := bstep (se 1 (by rfl) ⟨1134077, by rfl⟩ : syracuseStep 1512103 = 2268155) B2268155
theorem B1512127 : Blo 1510952 1512127 := bstep (se 1 (by rfl) ⟨1134095, by rfl⟩ : syracuseStep 1512127 = 2268191) B2268191
theorem B1512143 : Blo 1510952 1512143 := bstep (se 1 (by rfl) ⟨1134107, by rfl⟩ : syracuseStep 1512143 = 2268215) B2268215
theorem B1512223 : Blo 1510952 1512223 := bstep (se 1 (by rfl) ⟨1134167, by rfl⟩ : syracuseStep 1512223 = 2268335) B2268335
theorem B2552647 : Blo 1510952 2552647 := bstep (se 1 (by rfl) ⟨1914485, by rfl⟩ : syracuseStep 2552647 = 3828971) B3828971
theorem B1512319 : Blo 1510952 1512319 := bstep (se 1 (by rfl) ⟨1134239, by rfl⟩ : syracuseStep 1512319 = 2268479) B2268479
theorem B1512415 : Blo 1510952 1512415 := bstep (se 1 (by rfl) ⟨1134311, by rfl⟩ : syracuseStep 1512415 = 2268623) B2268623
theorem B1512671 : Blo 1510952 1512671 := bstep (se 1 (by rfl) ⟨1134503, by rfl⟩ : syracuseStep 1512671 = 2269007) B2269007
theorem B1512703 : Blo 1510952 1512703 := bstep (se 1 (by rfl) ⟨1134527, by rfl⟩ : syracuseStep 1512703 = 2269055) B2269055
theorem B1512751 : Blo 1510952 1512751 := bstep (se 1 (by rfl) ⟨1134563, by rfl⟩ : syracuseStep 1512751 = 2269127) B2269127
theorem B6460843 : Blo 1510952 6460843 := bstep (se 1 (by rfl) ⟨4845632, by rfl⟩ : syracuseStep 6460843 = 9691265) B9691265
theorem B1512911 : Blo 1510952 1512911 := bstep (se 1 (by rfl) ⟨1134683, by rfl⟩ : syracuseStep 1512911 = 2269367) B2269367
theorem B8615483 : Blo 1510952 8615483 := bstep (se 1 (by rfl) ⟨6461612, by rfl⟩ : syracuseStep 8615483 = 12923225) B12923225
theorem B5101217 : Blo 1510952 5101217 := bstep (se 2 (by rfl) ⟨1912956, by rfl⟩ : syracuseStep 5101217 = 3825913) B3825913
theorem B106231459 : Blo 1510952 106231459 := bstep (se 1 (by rfl) ⟨79673594, by rfl⟩ : syracuseStep 106231459 = 159347189) B159347189
theorem B2266889 : Blo 1510952 2266889 := bstep (se 2 (by rfl) ⟨850083, by rfl⟩ : syracuseStep 2266889 = 1700167) B1700167
theorem B4364171 : Blo 1510952 4364171 := bstep (se 1 (by rfl) ⟨3273128, by rfl⟩ : syracuseStep 4364171 = 6546257) B6546257
theorem B397596599 : Blo 1510952 397596599 := bstep (se 1 (by rfl) ⟨298197449, by rfl⟩ : syracuseStep 397596599 = 596394899) B596394899
theorem B11483207 : Blo 1510952 11483207 := bstep (se 1 (by rfl) ⟨8612405, by rfl⟩ : syracuseStep 11483207 = 17224811) B17224811
theorem B5101919 : Blo 1510952 5101919 := bstep (se 1 (by rfl) ⟨3826439, by rfl⟩ : syracuseStep 5101919 = 7652879) B7652879
theorem B2267513 : Blo 1510952 2267513 := bstep (se 2 (by rfl) ⟨850317, by rfl⟩ : syracuseStep 2267513 = 1700635) B1700635
theorem B5102081 : Blo 1510952 5102081 := bstep (se 2 (by rfl) ⟨1913280, by rfl⟩ : syracuseStep 5102081 = 3826561) B3826561
theorem B29080403 : Blo 1510952 29080403 := bstep (se 1 (by rfl) ⟨21810302, by rfl⟩ : syracuseStep 29080403 = 43620605) B43620605
theorem B2268041 : Blo 1510952 2268041 := bstep (se 2 (by rfl) ⟨850515, by rfl⟩ : syracuseStep 2268041 = 1701031) B1701031
theorem B8969153 : Blo 1510952 8969153 := bstep (se 2 (by rfl) ⟨3363432, by rfl⟩ : syracuseStep 8969153 = 6726865) B6726865
theorem B3824921 : Blo 1510952 3824921 := bstep (se 2 (by rfl) ⟨1434345, by rfl⟩ : syracuseStep 3824921 = 2868691) B2868691
theorem B2268575 : Blo 1510952 2268575 := bstep (se 1 (by rfl) ⟨1701431, by rfl⟩ : syracuseStep 2268575 = 3402863) B3402863
theorem B2268719 : Blo 1510952 2268719 := bstep (se 1 (by rfl) ⟨1701539, by rfl⟩ : syracuseStep 2268719 = 3403079) B3403079
theorem B5103161 : Blo 1510952 5103161 := bstep (se 2 (by rfl) ⟨1913685, by rfl⟩ : syracuseStep 5103161 = 3827371) B3827371
theorem B49020511 : Blo 1510952 49020511 := bstep (se 1 (by rfl) ⟨36765383, by rfl⟩ : syracuseStep 49020511 = 73530767) B73530767
theorem B5103323 : Blo 1510952 5103323 := bstep (se 1 (by rfl) ⟨3827492, by rfl⟩ : syracuseStep 5103323 = 7654985) B7654985
theorem B8175451 : Blo 1510952 8175451 := bstep (se 1 (by rfl) ⟨6131588, by rfl⟩ : syracuseStep 8175451 = 12263177) B12263177
theorem B7651583 : Blo 1510952 7651583 := bstep (se 1 (by rfl) ⟨5738687, by rfl⟩ : syracuseStep 7651583 = 11477375) B11477375
theorem B3399983 : Blo 1510952 3399983 := bstep (se 1 (by rfl) ⟨2549987, by rfl⟩ : syracuseStep 3399983 = 5099975) B5099975
theorem B3400019 : Blo 1510952 3400019 := bstep (se 1 (by rfl) ⟨2550014, by rfl⟩ : syracuseStep 3400019 = 5100029) B5100029
theorem B3400127 : Blo 1510952 3400127 := bstep (se 1 (by rfl) ⟨2550095, by rfl⟩ : syracuseStep 3400127 = 5100191) B5100191
theorem B5522003 : Blo 1510952 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B27575063 : Blo 1510952 27575063 := bstep (se 1 (by rfl) ⟨20681297, by rfl⟩ : syracuseStep 27575063 = 41362595) B41362595
theorem B6456161 : Blo 1510952 6456161 := bstep (se 2 (by rfl) ⟨2421060, by rfl⟩ : syracuseStep 6456161 = 4842121) B4842121
theorem B5743655 : Blo 1510952 5743655 := bstep (se 1 (by rfl) ⟨4307741, by rfl⟩ : syracuseStep 5743655 = 8615483) B8615483
theorem B3400811 : Blo 1510952 3400811 := bstep (se 1 (by rfl) ⟨2550608, by rfl⟩ : syracuseStep 3400811 = 5101217) B5101217
theorem B2909447 : Blo 1510952 2909447 := bstep (se 1 (by rfl) ⟨2182085, by rfl⟩ : syracuseStep 2909447 = 4364171) B4364171
theorem B17229185 : Blo 1510952 17229185 := bstep (se 2 (by rfl) ⟨6460944, by rfl⟩ : syracuseStep 17229185 = 12921889) B12921889
theorem B3401279 : Blo 1510952 3401279 := bstep (se 1 (by rfl) ⟨2550959, by rfl⟩ : syracuseStep 3401279 = 5101919) B5101919
theorem B5105321 : Blo 1510952 5105321 := bstep (se 2 (by rfl) ⟨1914495, by rfl⟩ : syracuseStep 5105321 = 3828991) B3828991
theorem B3401387 : Blo 1510952 3401387 := bstep (se 1 (by rfl) ⟨2551040, by rfl⟩ : syracuseStep 3401387 = 5102081) B5102081
theorem B16336799 : Blo 1510952 16336799 := bstep (se 1 (by rfl) ⟨12252599, by rfl⟩ : syracuseStep 16336799 = 24505199) B24505199
theorem B6457427 : Blo 1510952 6457427 := bstep (se 1 (by rfl) ⟨4843070, by rfl⟩ : syracuseStep 6457427 = 9686141) B9686141
theorem B2549947 : Blo 1510952 2549947 := bstep (se 1 (by rfl) ⟨1912460, by rfl⟩ : syracuseStep 2549947 = 3824921) B3824921
theorem B141641945 : Blo 1510952 141641945 := bstep (se 2 (by rfl) ⟨53115729, by rfl⟩ : syracuseStep 141641945 = 106231459) B106231459
theorem B3402107 : Blo 1510952 3402107 := bstep (se 1 (by rfl) ⟨2551580, by rfl⟩ : syracuseStep 3402107 = 5103161) B5103161
theorem B3402215 : Blo 1510952 3402215 := bstep (se 1 (by rfl) ⟨2551661, by rfl⟩ : syracuseStep 3402215 = 5103323) B5103323
theorem B8612567 : Blo 1510952 8612567 := bstep (se 1 (by rfl) ⟨6459425, by rfl⟩ : syracuseStep 8612567 = 12918851) B12918851
theorem B3828505 : Blo 1510952 3828505 := bstep (se 2 (by rfl) ⟨1435689, by rfl⟩ : syracuseStep 3828505 = 2871379) B2871379
theorem B24529787 : Blo 1510952 24529787 := bstep (se 1 (by rfl) ⟨18397340, by rfl⟩ : syracuseStep 24529787 = 36794681) B36794681
theorem B3402665 : Blo 1510952 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B14527673 : Blo 1510952 14527673 := bstep (se 2 (by rfl) ⟨5447877, by rfl⟩ : syracuseStep 14527673 = 10895755) B10895755
theorem B34893031 : Blo 1510952 34893031 := bstep (se 1 (by rfl) ⟨26169773, by rfl⟩ : syracuseStep 34893031 = 52339547) B52339547
theorem B25832843 : Blo 1510952 25832843 := bstep (se 1 (by rfl) ⟨19374632, by rfl⟩ : syracuseStep 25832843 = 38749265) B38749265
theorem B16576001 : Blo 1510952 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B3403529 : Blo 1510952 3403529 := bstep (se 2 (by rfl) ⟨1276323, by rfl⟩ : syracuseStep 3403529 = 2552647) B2552647
theorem B1511259 : Blo 1510952 1511259 := bstep (se 1 (by rfl) ⟨1133444, by rfl⟩ : syracuseStep 1511259 = 2266889) B2266889
theorem B265064399 : Blo 1510952 265064399 := bstep (se 1 (by rfl) ⟨198798299, by rfl⟩ : syracuseStep 265064399 = 397596599) B397596599
theorem B16347095 : Blo 1510952 16347095 := bstep (se 1 (by rfl) ⟨12260321, by rfl⟩ : syracuseStep 16347095 = 24520643) B24520643
theorem B4304927 : Blo 1510952 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B7655471 : Blo 1510952 7655471 := bstep (se 1 (by rfl) ⟨5741603, by rfl⟩ : syracuseStep 7655471 = 11483207) B11483207
theorem B1912987 : Blo 1510952 1912987 := bstep (se 1 (by rfl) ⟨1434740, by rfl⟩ : syracuseStep 1912987 = 2869481) B2869481
theorem B1511675 : Blo 1510952 1511675 := bstep (se 1 (by rfl) ⟨1133756, by rfl⟩ : syracuseStep 1511675 = 2267513) B2267513
theorem B1700095 : Blo 1510952 1700095 := bstep (se 1 (by rfl) ⟨1275071, by rfl⟩ : syracuseStep 1700095 = 2550143) B2550143
theorem B20689181 : Blo 1510952 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B1913159 : Blo 1510952 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B88347145 : Blo 1510952 88347145 := bstep (se 2 (by rfl) ⟨33130179, by rfl⟩ : syracuseStep 88347145 = 66260359) B66260359
theorem B19386935 : Blo 1510952 19386935 := bstep (se 1 (by rfl) ⟨14540201, by rfl⟩ : syracuseStep 19386935 = 29080403) B29080403
theorem B8614457 : Blo 1510952 8614457 := bstep (se 2 (by rfl) ⟨3230421, by rfl⟩ : syracuseStep 8614457 = 6460843) B6460843
theorem B1512027 : Blo 1510952 1512027 := bstep (se 1 (by rfl) ⟨1134020, by rfl⟩ : syracuseStep 1512027 = 2268041) B2268041
theorem B4305565 : Blo 1510952 4305565 := bstep (se 3 (by rfl) ⟨807293, by rfl⟩ : syracuseStep 4305565 = 1614587) B1614587
theorem B95670965 : Blo 1510952 95670965 := bstep (se 5 (by rfl) ⟨4484576, by rfl⟩ : syracuseStep 95670965 = 8969153) B8969153
theorem B65360681 : Blo 1510952 65360681 := bstep (se 2 (by rfl) ⟨24510255, by rfl⟩ : syracuseStep 65360681 = 49020511) B49020511
theorem B8614775 : Blo 1510952 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B1512383 : Blo 1510952 1512383 := bstep (se 1 (by rfl) ⟨1134287, by rfl⟩ : syracuseStep 1512383 = 2268575) B2268575
theorem B1512479 : Blo 1510952 1512479 := bstep (se 1 (by rfl) ⟨1134359, by rfl⟩ : syracuseStep 1512479 = 2268719) B2268719
theorem B10900601 : Blo 1510952 10900601 := bstep (se 2 (by rfl) ⟨4087725, by rfl⟩ : syracuseStep 10900601 = 8175451) B8175451
theorem B11482235 : Blo 1510952 11482235 := bstep (se 1 (by rfl) ⟨8611676, by rfl⟩ : syracuseStep 11482235 = 17223353) B17223353
theorem B12432761 : Blo 1510952 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B1512831 : Blo 1510952 1512831 := bstep (se 1 (by rfl) ⟨1134623, by rfl⟩ : syracuseStep 1512831 = 2269247) B2269247
theorem B2266919 : Blo 1510952 2266919 := bstep (se 1 (by rfl) ⟨1700189, by rfl⟩ : syracuseStep 2266919 = 3400379) B3400379
theorem B12253477 : Blo 1510952 12253477 := bstep (se 4 (by rfl) ⟨1148763, by rfl⟩ : syracuseStep 12253477 = 2297527) B2297527
theorem B5102459 : Blo 1510952 5102459 := bstep (se 1 (by rfl) ⟨3826844, by rfl⟩ : syracuseStep 5102459 = 7653689) B7653689
theorem B4086665 : Blo 1510952 4086665 := bstep (se 2 (by rfl) ⟨1532499, by rfl⟩ : syracuseStep 4086665 = 3064999) B3064999
theorem B5741543 : Blo 1510952 5741543 := bstep (se 1 (by rfl) ⟨4306157, by rfl⟩ : syracuseStep 5741543 = 8612315) B8612315
theorem B2268251 : Blo 1510952 2268251 := bstep (se 1 (by rfl) ⟨1701188, by rfl⟩ : syracuseStep 2268251 = 3402377) B3402377
theorem B7650449 : Blo 1510952 7650449 := bstep (se 2 (by rfl) ⟨2868918, by rfl⟩ : syracuseStep 7650449 = 5737837) B5737837
theorem B7658873 : Blo 1510952 7658873 := bstep (se 2 (by rfl) ⟨2872077, by rfl⟩ : syracuseStep 7658873 = 5744155) B5744155
theorem B3825103 : Blo 1510952 3825103 := bstep (se 1 (by rfl) ⟨2868827, by rfl⟩ : syracuseStep 3825103 = 5737655) B5737655
theorem B2268923 : Blo 1510952 2268923 := bstep (se 1 (by rfl) ⟨1701692, by rfl⟩ : syracuseStep 2268923 = 3403385) B3403385
theorem B2269163 : Blo 1510952 2269163 := bstep (se 1 (by rfl) ⟨1701872, by rfl⟩ : syracuseStep 2269163 = 3403745) B3403745
theorem B5103647 : Blo 1510952 5103647 := bstep (se 1 (by rfl) ⟨3827735, by rfl⟩ : syracuseStep 5103647 = 7655471) B7655471
theorem B3399929 : Blo 1510952 3399929 := bstep (se 2 (by rfl) ⟨1274973, by rfl⟩ : syracuseStep 3399929 = 2549947) B2549947
theorem B5742971 : Blo 1510952 5742971 := bstep (se 1 (by rfl) ⟨4307228, by rfl⟩ : syracuseStep 5742971 = 8614457) B8614457
theorem B18383375 : Blo 1510952 18383375 := bstep (se 1 (by rfl) ⟨13787531, by rfl⟩ : syracuseStep 18383375 = 27575063) B27575063
theorem B43573787 : Blo 1510952 43573787 := bstep (se 1 (by rfl) ⟨32680340, by rfl⟩ : syracuseStep 43573787 = 65360681) B65360681
theorem B5743183 : Blo 1510952 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B7267067 : Blo 1510952 7267067 := bstep (se 1 (by rfl) ⟨5450300, by rfl⟩ : syracuseStep 7267067 = 10900601) B10900601
theorem B11486123 : Blo 1510952 11486123 := bstep (se 1 (by rfl) ⟨8614592, by rfl⟩ : syracuseStep 11486123 = 17229185) B17229185
theorem B5104673 : Blo 1510952 5104673 := bstep (se 2 (by rfl) ⟨1914252, by rfl⟩ : syracuseStep 5104673 = 3828505) B3828505
theorem B46524041 : Blo 1510952 46524041 := bstep (se 2 (by rfl) ⟨17446515, by rfl⟩ : syracuseStep 46524041 = 34893031) B34893031
theorem B3401639 : Blo 1510952 3401639 := bstep (se 1 (by rfl) ⟨2551229, by rfl⟩ : syracuseStep 3401639 = 5102459) B5102459
theorem B16353191 : Blo 1510952 16353191 := bstep (se 1 (by rfl) ⟨12264893, by rfl⟩ : syracuseStep 16353191 = 24529787) B24529787
theorem B3827695 : Blo 1510952 3827695 := bstep (se 1 (by rfl) ⟨2870771, by rfl⟩ : syracuseStep 3827695 = 5741543) B5741543
theorem B9685115 : Blo 1510952 9685115 := bstep (se 1 (by rfl) ⟨7263836, by rfl⟩ : syracuseStep 9685115 = 14527673) B14527673
theorem B5105915 : Blo 1510952 5105915 := bstep (se 1 (by rfl) ⟨3829436, by rfl⟩ : syracuseStep 5105915 = 7658873) B7658873
theorem B17221895 : Blo 1510952 17221895 := bstep (se 1 (by rfl) ⟨12916421, by rfl⟩ : syracuseStep 17221895 = 25832843) B25832843
theorem B10898063 : Blo 1510952 10898063 := bstep (se 1 (by rfl) ⟨8173547, by rfl⟩ : syracuseStep 10898063 = 16347095) B16347095
theorem B11479805 : Blo 1510952 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B2550649 : Blo 1510952 2550649 := bstep (se 2 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 2550649 = 1912987) B1912987
theorem B16337969 : Blo 1510952 16337969 := bstep (se 2 (by rfl) ⟨6126738, by rfl⟩ : syracuseStep 16337969 = 12253477) B12253477
theorem B3681335 : Blo 1510952 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B4304107 : Blo 1510952 4304107 := bstep (se 1 (by rfl) ⟨3228080, by rfl⟩ : syracuseStep 4304107 = 6456161) B6456161
theorem B117796193 : Blo 1510952 117796193 := bstep (se 2 (by rfl) ⟨44173572, by rfl⟩ : syracuseStep 117796193 = 88347145) B88347145
theorem B3829103 : Blo 1510952 3829103 := bstep (se 1 (by rfl) ⟨2871827, by rfl⟩ : syracuseStep 3829103 = 5743655) B5743655
theorem B7654823 : Blo 1510952 7654823 := bstep (se 1 (by rfl) ⟨5741117, by rfl⟩ : syracuseStep 7654823 = 11482235) B11482235
theorem B3403547 : Blo 1510952 3403547 := bstep (se 1 (by rfl) ⟨2552660, by rfl⟩ : syracuseStep 3403547 = 5105321) B5105321
theorem B1511279 : Blo 1510952 1511279 := bstep (se 1 (by rfl) ⟨1133459, by rfl⟩ : syracuseStep 1511279 = 2266919) B2266919
theorem B10891199 : Blo 1510952 10891199 := bstep (se 1 (by rfl) ⟨8168399, by rfl⟩ : syracuseStep 10891199 = 16336799) B16336799
theorem B4304951 : Blo 1510952 4304951 := bstep (se 1 (by rfl) ⟨3228713, by rfl⟩ : syracuseStep 4304951 = 6457427) B6457427
theorem B2724443 : Blo 1510952 2724443 := bstep (se 1 (by rfl) ⟨2043332, by rfl⟩ : syracuseStep 2724443 = 4086665) B4086665
theorem B5100137 : Blo 1510952 5100137 := bstep (se 2 (by rfl) ⟨1912551, by rfl⟩ : syracuseStep 5100137 = 3825103) B3825103
theorem B1512167 : Blo 1510952 1512167 := bstep (se 1 (by rfl) ⟨1134125, by rfl⟩ : syracuseStep 1512167 = 2268251) B2268251
theorem B5100299 : Blo 1510952 5100299 := bstep (se 1 (by rfl) ⟨3825224, by rfl⟩ : syracuseStep 5100299 = 7650449) B7650449
theorem B1512615 : Blo 1510952 1512615 := bstep (se 1 (by rfl) ⟨1134461, by rfl⟩ : syracuseStep 1512615 = 2268923) B2268923
theorem B1512775 : Blo 1510952 1512775 := bstep (se 1 (by rfl) ⟨1134581, by rfl⟩ : syracuseStep 1512775 = 2269163) B2269163
theorem B5101055 : Blo 1510952 5101055 := bstep (se 1 (by rfl) ⟨3825791, by rfl⟩ : syracuseStep 5101055 = 7651583) B7651583
theorem B13792787 : Blo 1510952 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B2266655 : Blo 1510952 2266655 := bstep (se 1 (by rfl) ⟨1699991, by rfl⟩ : syracuseStep 2266655 = 3399983) B3399983
theorem B2266679 : Blo 1510952 2266679 := bstep (se 1 (by rfl) ⟨1700009, by rfl⟩ : syracuseStep 2266679 = 3400019) B3400019
theorem B2266751 : Blo 1510952 2266751 := bstep (se 1 (by rfl) ⟨1700063, by rfl⟩ : syracuseStep 2266751 = 3400127) B3400127
theorem B2266793 : Blo 1510952 2266793 := bstep (se 2 (by rfl) ⟨850047, by rfl⟩ : syracuseStep 2266793 = 1700095) B1700095
theorem B12924623 : Blo 1510952 12924623 := bstep (se 1 (by rfl) ⟨9693467, by rfl⟩ : syracuseStep 12924623 = 19386935) B19386935
theorem B63780643 : Blo 1510952 63780643 := bstep (se 1 (by rfl) ⟨47835482, by rfl⟩ : syracuseStep 63780643 = 95670965) B95670965
theorem B2267207 : Blo 1510952 2267207 := bstep (se 1 (by rfl) ⟨1700405, by rfl⟩ : syracuseStep 2267207 = 3400811) B3400811
theorem B1939631 : Blo 1510952 1939631 := bstep (se 1 (by rfl) ⟨1454723, by rfl⟩ : syracuseStep 1939631 = 2909447) B2909447
theorem B5101757 : Blo 1510952 5101757 := bstep (se 3 (by rfl) ⟨956579, by rfl⟩ : syracuseStep 5101757 = 1913159) B1913159
theorem B5740753 : Blo 1510952 5740753 := bstep (se 2 (by rfl) ⟨2152782, by rfl⟩ : syracuseStep 5740753 = 4305565) B4305565
theorem B8288507 : Blo 1510952 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B2267519 : Blo 1510952 2267519 := bstep (se 1 (by rfl) ⟨1700639, by rfl⟩ : syracuseStep 2267519 = 3401279) B3401279
theorem B2267591 : Blo 1510952 2267591 := bstep (se 1 (by rfl) ⟨1700693, by rfl⟩ : syracuseStep 2267591 = 3401387) B3401387
theorem B94427963 : Blo 1510952 94427963 := bstep (se 1 (by rfl) ⟨70820972, by rfl⟩ : syracuseStep 94427963 = 141641945) B141641945
theorem B2268071 : Blo 1510952 2268071 := bstep (se 1 (by rfl) ⟨1701053, by rfl⟩ : syracuseStep 2268071 = 3402107) B3402107
theorem B2268143 : Blo 1510952 2268143 := bstep (se 1 (by rfl) ⟨1701107, by rfl⟩ : syracuseStep 2268143 = 3402215) B3402215
theorem B5741711 : Blo 1510952 5741711 := bstep (se 1 (by rfl) ⟨4306283, by rfl⟩ : syracuseStep 5741711 = 8612567) B8612567
theorem B2268443 : Blo 1510952 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B11050667 : Blo 1510952 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B2269019 : Blo 1510952 2269019 := bstep (se 1 (by rfl) ⟨1701764, by rfl⟩ : syracuseStep 2269019 = 3403529) B3403529
theorem B176709599 : Blo 1510952 176709599 := bstep (se 1 (by rfl) ⟨132532199, by rfl⟩ : syracuseStep 176709599 = 265064399) B265064399
theorem B12255583 : Blo 1510952 12255583 := bstep (se 1 (by rfl) ⟨9191687, by rfl⟩ : syracuseStep 12255583 = 18383375) B18383375
theorem B29049191 : Blo 1510952 29049191 := bstep (se 1 (by rfl) ⟨21786893, by rfl⟩ : syracuseStep 29049191 = 43573787) B43573787
theorem B3400091 : Blo 1510952 3400091 := bstep (se 1 (by rfl) ⟨2550068, by rfl⟩ : syracuseStep 3400091 = 5100137) B5100137
theorem B3400199 : Blo 1510952 3400199 := bstep (se 1 (by rfl) ⟨2550149, by rfl⟩ : syracuseStep 3400199 = 5100299) B5100299
theorem B3400703 : Blo 1510952 3400703 := bstep (se 1 (by rfl) ⟨2550527, by rfl⟩ : syracuseStep 3400703 = 5101055) B5101055
theorem B31016027 : Blo 1510952 31016027 := bstep (se 1 (by rfl) ⟨23262020, by rfl⟩ : syracuseStep 31016027 = 46524041) B46524041
theorem B3400865 : Blo 1510952 3400865 := bstep (se 2 (by rfl) ⟨1275324, by rfl⟩ : syracuseStep 3400865 = 2550649) B2550649
theorem B6456743 : Blo 1510952 6456743 := bstep (se 1 (by rfl) ⟨4842557, by rfl⟩ : syracuseStep 6456743 = 9685115) B9685115
theorem B3401171 : Blo 1510952 3401171 := bstep (se 1 (by rfl) ⟨2550878, by rfl⟩ : syracuseStep 3401171 = 5101757) B5101757
theorem B7653203 : Blo 1510952 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B3827807 : Blo 1510952 3827807 := bstep (se 1 (by rfl) ⟨2870855, by rfl⟩ : syracuseStep 3827807 = 5741711) B5741711
theorem B78530795 : Blo 1510952 78530795 := bstep (se 1 (by rfl) ⟨58898096, by rfl⟩ : syracuseStep 78530795 = 117796193) B117796193
theorem B7367111 : Blo 1510952 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B7260799 : Blo 1510952 7260799 := bstep (se 1 (by rfl) ⟨5445599, by rfl⟩ : syracuseStep 7260799 = 10891199) B10891199
theorem B3402431 : Blo 1510952 3402431 := bstep (se 1 (by rfl) ⟨2551823, by rfl⟩ : syracuseStep 3402431 = 5103647) B5103647
theorem B2869967 : Blo 1510952 2869967 := bstep (se 1 (by rfl) ⟨2152475, by rfl⟩ : syracuseStep 2869967 = 4304951) B4304951
theorem B3828647 : Blo 1510952 3828647 := bstep (se 1 (by rfl) ⟨2871485, by rfl⟩ : syracuseStep 3828647 = 5742971) B5742971
theorem B7654337 : Blo 1510952 7654337 := bstep (se 2 (by rfl) ⟨2870376, by rfl⟩ : syracuseStep 7654337 = 5740753) B5740753
theorem B4844711 : Blo 1510952 4844711 := bstep (se 1 (by rfl) ⟨3633533, by rfl⟩ : syracuseStep 4844711 = 7267067) B7267067
theorem B3403115 : Blo 1510952 3403115 := bstep (se 1 (by rfl) ⟨2552336, by rfl⟩ : syracuseStep 3403115 = 5104673) B5104673
theorem B9195191 : Blo 1510952 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B1511103 : Blo 1510952 1511103 := bstep (se 1 (by rfl) ⟨1133327, by rfl⟩ : syracuseStep 1511103 = 2266655) B2266655
theorem B1511119 : Blo 1510952 1511119 := bstep (se 1 (by rfl) ⟨1133339, by rfl⟩ : syracuseStep 1511119 = 2266679) B2266679
theorem B1511167 : Blo 1510952 1511167 := bstep (se 1 (by rfl) ⟨1133375, by rfl⟩ : syracuseStep 1511167 = 2266751) B2266751
theorem B1511195 : Blo 1510952 1511195 := bstep (se 1 (by rfl) ⟨1133396, by rfl⟩ : syracuseStep 1511195 = 2266793) B2266793
theorem B1511471 : Blo 1510952 1511471 := bstep (se 1 (by rfl) ⟨1133603, by rfl⟩ : syracuseStep 1511471 = 2267207) B2267207
theorem B5525671 : Blo 1510952 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B3403943 : Blo 1510952 3403943 := bstep (se 1 (by rfl) ⟨2552957, by rfl⟩ : syracuseStep 3403943 = 5105915) B5105915
theorem B11481263 : Blo 1510952 11481263 := bstep (se 1 (by rfl) ⟨8610947, by rfl⟩ : syracuseStep 11481263 = 17221895) B17221895
theorem B1511679 : Blo 1510952 1511679 := bstep (se 1 (by rfl) ⟨1133759, by rfl⟩ : syracuseStep 1511679 = 2267519) B2267519
theorem B1511727 : Blo 1510952 1511727 := bstep (se 1 (by rfl) ⟨1133795, by rfl⟩ : syracuseStep 1511727 = 2267591) B2267591
theorem B5738809 : Blo 1510952 5738809 := bstep (se 2 (by rfl) ⟨2152053, by rfl⟩ : syracuseStep 5738809 = 4304107) B4304107
theorem B20689397 : Blo 1510952 20689397 := bstep (se 5 (by rfl) ⟨969815, by rfl⟩ : syracuseStep 20689397 = 1939631) B1939631
theorem B62951975 : Blo 1510952 62951975 := bstep (se 1 (by rfl) ⟨47213981, by rfl⟩ : syracuseStep 62951975 = 94427963) B94427963
theorem B1512047 : Blo 1510952 1512047 := bstep (se 1 (by rfl) ⟨1134035, by rfl⟩ : syracuseStep 1512047 = 2268071) B2268071
theorem B1512095 : Blo 1510952 1512095 := bstep (se 1 (by rfl) ⟨1134071, by rfl⟩ : syracuseStep 1512095 = 2268143) B2268143
theorem B10891979 : Blo 1510952 10891979 := bstep (se 1 (by rfl) ⟨8168984, by rfl⟩ : syracuseStep 10891979 = 16337969) B16337969
theorem B2454223 : Blo 1510952 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B1512295 : Blo 1510952 1512295 := bstep (se 1 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 1512295 = 2268443) B2268443
theorem B2552735 : Blo 1510952 2552735 := bstep (se 1 (by rfl) ⟨1914551, by rfl⟩ : syracuseStep 2552735 = 3829103) B3829103
theorem B1512679 : Blo 1510952 1512679 := bstep (se 1 (by rfl) ⟨1134509, by rfl⟩ : syracuseStep 1512679 = 2269019) B2269019
theorem B117806399 : Blo 1510952 117806399 := bstep (se 1 (by rfl) ⟨88354799, by rfl⟩ : syracuseStep 117806399 = 176709599) B176709599
theorem B2266619 : Blo 1510952 2266619 := bstep (se 1 (by rfl) ⟨1699964, by rfl⟩ : syracuseStep 2266619 = 3399929) B3399929
theorem B1816295 : Blo 1510952 1816295 := bstep (se 1 (by rfl) ⟨1362221, by rfl⟩ : syracuseStep 1816295 = 2724443) B2724443
theorem B7657415 : Blo 1510952 7657415 := bstep (se 1 (by rfl) ⟨5743061, by rfl⟩ : syracuseStep 7657415 = 11486123) B11486123
theorem B7657577 : Blo 1510952 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B8616415 : Blo 1510952 8616415 := bstep (se 1 (by rfl) ⟨6462311, by rfl⟩ : syracuseStep 8616415 = 12924623) B12924623
theorem B2267759 : Blo 1510952 2267759 := bstep (se 1 (by rfl) ⟨1700819, by rfl⟩ : syracuseStep 2267759 = 3401639) B3401639
theorem B10902127 : Blo 1510952 10902127 := bstep (se 1 (by rfl) ⟨8176595, by rfl⟩ : syracuseStep 10902127 = 16353191) B16353191
theorem B7265375 : Blo 1510952 7265375 := bstep (se 1 (by rfl) ⟨5449031, by rfl⟩ : syracuseStep 7265375 = 10898063) B10898063
theorem B5103215 : Blo 1510952 5103215 := bstep (se 1 (by rfl) ⟨3827411, by rfl⟩ : syracuseStep 5103215 = 7654823) B7654823
theorem B85040857 : Blo 1510952 85040857 := bstep (se 2 (by rfl) ⟨31890321, by rfl⟩ : syracuseStep 85040857 = 63780643) B63780643
theorem B2269031 : Blo 1510952 2269031 := bstep (se 1 (by rfl) ⟨1701773, by rfl⟩ : syracuseStep 2269031 = 3403547) B3403547
theorem B5103593 : Blo 1510952 5103593 := bstep (se 2 (by rfl) ⟨1913847, by rfl⟩ : syracuseStep 5103593 = 3827695) B3827695
theorem B2269295 : Blo 1510952 2269295 := bstep (se 1 (by rfl) ⟨1701971, by rfl⟩ : syracuseStep 2269295 = 3403943) B3403943
theorem B19366127 : Blo 1510952 19366127 := bstep (se 1 (by rfl) ⟨14524595, by rfl⟩ : syracuseStep 19366127 = 29049191) B29049191
theorem B41967983 : Blo 1510952 41967983 := bstep (se 1 (by rfl) ⟨31475987, by rfl⟩ : syracuseStep 41967983 = 62951975) B62951975
theorem B7651745 : Blo 1510952 7651745 := bstep (se 2 (by rfl) ⟨2869404, by rfl⟩ : syracuseStep 7651745 = 5738809) B5738809
theorem B20677351 : Blo 1510952 20677351 := bstep (se 1 (by rfl) ⟨15508013, by rfl⟩ : syracuseStep 20677351 = 31016027) B31016027
theorem B78537599 : Blo 1510952 78537599 := bstep (se 1 (by rfl) ⟨58903199, by rfl⟩ : syracuseStep 78537599 = 117806399) B117806399
theorem B453551237 : Blo 1510952 453551237 := bstep (se 4 (by rfl) ⟨42520428, by rfl⟩ : syracuseStep 453551237 = 85040857) B85040857
theorem B5104943 : Blo 1510952 5104943 := bstep (se 1 (by rfl) ⟨3828707, by rfl⟩ : syracuseStep 5104943 = 7657415) B7657415
theorem B5105051 : Blo 1510952 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B4843583 : Blo 1510952 4843583 := bstep (se 1 (by rfl) ⟨3632687, by rfl⟩ : syracuseStep 4843583 = 7265375) B7265375
theorem B3229807 : Blo 1510952 3229807 := bstep (se 1 (by rfl) ⟨2422355, by rfl⟩ : syracuseStep 3229807 = 4844711) B4844711
theorem B3402143 : Blo 1510952 3402143 := bstep (se 1 (by rfl) ⟨2551607, by rfl⟩ : syracuseStep 3402143 = 5103215) B5103215
theorem B6130127 : Blo 1510952 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B3402395 : Blo 1510952 3402395 := bstep (se 1 (by rfl) ⟨2551796, by rfl⟩ : syracuseStep 3402395 = 5103593) B5103593
theorem B7654175 : Blo 1510952 7654175 := bstep (se 1 (by rfl) ⟨5740631, by rfl⟩ : syracuseStep 7654175 = 11481263) B11481263
theorem B7367561 : Blo 1510952 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B7261319 : Blo 1510952 7261319 := bstep (se 1 (by rfl) ⟨5445989, by rfl⟩ : syracuseStep 7261319 = 10891979) B10891979
theorem B11488553 : Blo 1510952 11488553 := bstep (se 2 (by rfl) ⟨4308207, by rfl⟩ : syracuseStep 11488553 = 8616415) B8616415
theorem B14536169 : Blo 1510952 14536169 := bstep (se 2 (by rfl) ⟨5451063, by rfl⟩ : syracuseStep 14536169 = 10902127) B10902127
theorem B3272297 : Blo 1510952 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B4304495 : Blo 1510952 4304495 := bstep (se 1 (by rfl) ⟨3228371, by rfl⟩ : syracuseStep 4304495 = 6456743) B6456743
theorem B1511079 : Blo 1510952 1511079 := bstep (se 1 (by rfl) ⟨1133309, by rfl⟩ : syracuseStep 1511079 = 2266619) B2266619
theorem B2551871 : Blo 1510952 2551871 := bstep (se 1 (by rfl) ⟨1913903, by rfl⟩ : syracuseStep 2551871 = 3827807) B3827807
theorem B4911407 : Blo 1510952 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B1511839 : Blo 1510952 1511839 := bstep (se 1 (by rfl) ⟨1133879, by rfl⟩ : syracuseStep 1511839 = 2267759) B2267759
theorem B1913311 : Blo 1510952 1913311 := bstep (se 1 (by rfl) ⟨1434983, by rfl⟩ : syracuseStep 1913311 = 2869967) B2869967
theorem B2552431 : Blo 1510952 2552431 := bstep (se 1 (by rfl) ⟨1914323, by rfl⟩ : syracuseStep 2552431 = 3828647) B3828647
theorem B1512687 : Blo 1510952 1512687 := bstep (se 1 (by rfl) ⟨1134515, by rfl⟩ : syracuseStep 1512687 = 2269031) B2269031
theorem B2266727 : Blo 1510952 2266727 := bstep (se 1 (by rfl) ⟨1700045, by rfl⟩ : syracuseStep 2266727 = 3400091) B3400091
theorem B13792931 : Blo 1510952 13792931 := bstep (se 1 (by rfl) ⟨10344698, by rfl⟩ : syracuseStep 13792931 = 20689397) B20689397
theorem B2266799 : Blo 1510952 2266799 := bstep (se 1 (by rfl) ⟨1700099, by rfl⟩ : syracuseStep 2266799 = 3400199) B3400199
theorem B16340777 : Blo 1510952 16340777 := bstep (se 2 (by rfl) ⟨6127791, by rfl⟩ : syracuseStep 16340777 = 12255583) B12255583
theorem B1701823 : Blo 1510952 1701823 := bstep (se 1 (by rfl) ⟨1276367, by rfl⟩ : syracuseStep 1701823 = 2552735) B2552735
theorem B2267135 : Blo 1510952 2267135 := bstep (se 1 (by rfl) ⟨1700351, by rfl⟩ : syracuseStep 2267135 = 3400703) B3400703
theorem B2267243 : Blo 1510952 2267243 := bstep (se 1 (by rfl) ⟨1700432, by rfl⟩ : syracuseStep 2267243 = 3400865) B3400865
theorem B9681065 : Blo 1510952 9681065 := bstep (se 2 (by rfl) ⟨3630399, by rfl⟩ : syracuseStep 9681065 = 7260799) B7260799
theorem B2267447 : Blo 1510952 2267447 := bstep (se 1 (by rfl) ⟨1700585, by rfl⟩ : syracuseStep 2267447 = 3401171) B3401171
theorem B5102135 : Blo 1510952 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B52353863 : Blo 1510952 52353863 := bstep (se 1 (by rfl) ⟨39265397, by rfl⟩ : syracuseStep 52353863 = 78530795) B78530795
theorem B2268287 : Blo 1510952 2268287 := bstep (se 1 (by rfl) ⟨1701215, by rfl⟩ : syracuseStep 2268287 = 3402431) B3402431
theorem B5102891 : Blo 1510952 5102891 := bstep (se 1 (by rfl) ⟨3827168, by rfl⟩ : syracuseStep 5102891 = 7654337) B7654337
theorem B2268743 : Blo 1510952 2268743 := bstep (se 1 (by rfl) ⟨1701557, by rfl⟩ : syracuseStep 2268743 = 3403115) B3403115
theorem B19373813 : Blo 1510952 19373813 := bstep (se 5 (by rfl) ⟨908147, by rfl⟩ : syracuseStep 19373813 = 1816295) B1816295
theorem B12910751 : Blo 1510952 12910751 := bstep (se 1 (by rfl) ⟨9683063, by rfl⟩ : syracuseStep 12910751 = 19366127) B19366127
theorem B302367491 : Blo 1510952 302367491 := bstep (se 1 (by rfl) ⟨226775618, by rfl⟩ : syracuseStep 302367491 = 453551237) B453551237
theorem B3229055 : Blo 1510952 3229055 := bstep (se 1 (by rfl) ⟨2421791, by rfl⟩ : syracuseStep 3229055 = 4843583) B4843583
theorem B8726125 : Blo 1510952 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B3401423 : Blo 1510952 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B3401927 : Blo 1510952 3401927 := bstep (se 1 (by rfl) ⟨2551445, by rfl⟩ : syracuseStep 3401927 = 5102891) B5102891
theorem B2869663 : Blo 1510952 2869663 := bstep (se 1 (by rfl) ⟨2152247, by rfl⟩ : syracuseStep 2869663 = 4304495) B4304495
theorem B52358399 : Blo 1510952 52358399 := bstep (se 1 (by rfl) ⟨39268799, by rfl⟩ : syracuseStep 52358399 = 78537599) B78537599
theorem B2551081 : Blo 1510952 2551081 := bstep (se 2 (by rfl) ⟨956655, by rfl⟩ : syracuseStep 2551081 = 1913311) B1913311
theorem B3403241 : Blo 1510952 3403241 := bstep (se 2 (by rfl) ⟨1276215, by rfl⟩ : syracuseStep 3403241 = 2552431) B2552431
theorem B3403295 : Blo 1510952 3403295 := bstep (se 1 (by rfl) ⟨2552471, by rfl⟩ : syracuseStep 3403295 = 5104943) B5104943
theorem B3403367 : Blo 1510952 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B111914621 : Blo 1510952 111914621 := bstep (se 3 (by rfl) ⟨20983991, by rfl⟩ : syracuseStep 111914621 = 41967983) B41967983
theorem B27569801 : Blo 1510952 27569801 := bstep (se 2 (by rfl) ⟨10338675, by rfl⟩ : syracuseStep 27569801 = 20677351) B20677351
theorem B1511151 : Blo 1510952 1511151 := bstep (se 1 (by rfl) ⟨1133363, by rfl⟩ : syracuseStep 1511151 = 2266727) B2266727
theorem B9195287 : Blo 1510952 9195287 := bstep (se 1 (by rfl) ⟨6896465, by rfl⟩ : syracuseStep 9195287 = 13792931) B13792931
theorem B1511199 : Blo 1510952 1511199 := bstep (se 1 (by rfl) ⟨1133399, by rfl⟩ : syracuseStep 1511199 = 2266799) B2266799
theorem B16347005 : Blo 1510952 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B1511423 : Blo 1510952 1511423 := bstep (se 1 (by rfl) ⟨1133567, by rfl⟩ : syracuseStep 1511423 = 2267135) B2267135
theorem B1511495 : Blo 1510952 1511495 := bstep (se 1 (by rfl) ⟨1133621, by rfl⟩ : syracuseStep 1511495 = 2267243) B2267243
theorem B1511631 : Blo 1510952 1511631 := bstep (se 1 (by rfl) ⟨1133723, by rfl⟩ : syracuseStep 1511631 = 2267447) B2267447
theorem B34902575 : Blo 1510952 34902575 := bstep (se 1 (by rfl) ⟨26176931, by rfl⟩ : syracuseStep 34902575 = 52353863) B52353863
theorem B4911707 : Blo 1510952 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B1512191 : Blo 1510952 1512191 := bstep (se 1 (by rfl) ⟨1134143, by rfl⟩ : syracuseStep 1512191 = 2268287) B2268287
theorem B1512495 : Blo 1510952 1512495 := bstep (se 1 (by rfl) ⟨1134371, by rfl⟩ : syracuseStep 1512495 = 2268743) B2268743
theorem B12915875 : Blo 1510952 12915875 := bstep (se 1 (by rfl) ⟨9686906, by rfl⟩ : syracuseStep 12915875 = 19373813) B19373813
theorem B1701247 : Blo 1510952 1701247 := bstep (se 1 (by rfl) ⟨1275935, by rfl⟩ : syracuseStep 1701247 = 2551871) B2551871
theorem B1512863 : Blo 1510952 1512863 := bstep (se 1 (by rfl) ⟨1134647, by rfl⟩ : syracuseStep 1512863 = 2269295) B2269295
theorem B4306409 : Blo 1510952 4306409 := bstep (se 2 (by rfl) ⟨1614903, by rfl⟩ : syracuseStep 4306409 = 3229807) B3229807
theorem B3274271 : Blo 1510952 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B5101163 : Blo 1510952 5101163 := bstep (se 1 (by rfl) ⟨3825872, by rfl⟩ : syracuseStep 5101163 = 7651745) B7651745
theorem B10893851 : Blo 1510952 10893851 := bstep (se 1 (by rfl) ⟨8170388, by rfl⟩ : syracuseStep 10893851 = 16340777) B16340777
theorem B6454043 : Blo 1510952 6454043 := bstep (se 1 (by rfl) ⟨4840532, by rfl⟩ : syracuseStep 6454043 = 9681065) B9681065
theorem B2268095 : Blo 1510952 2268095 := bstep (se 1 (by rfl) ⟨1701071, by rfl⟩ : syracuseStep 2268095 = 3402143) B3402143
theorem B2268263 : Blo 1510952 2268263 := bstep (se 1 (by rfl) ⟨1701197, by rfl⟩ : syracuseStep 2268263 = 3402395) B3402395
theorem B5102783 : Blo 1510952 5102783 := bstep (se 1 (by rfl) ⟨3827087, by rfl⟩ : syracuseStep 5102783 = 7654175) B7654175
theorem B4840879 : Blo 1510952 4840879 := bstep (se 1 (by rfl) ⟨3630659, by rfl⟩ : syracuseStep 4840879 = 7261319) B7261319
theorem B7659035 : Blo 1510952 7659035 := bstep (se 1 (by rfl) ⟨5744276, by rfl⟩ : syracuseStep 7659035 = 11488553) B11488553
theorem B9690779 : Blo 1510952 9690779 := bstep (se 1 (by rfl) ⟨7268084, by rfl⟩ : syracuseStep 9690779 = 14536169) B14536169
theorem B2269097 : Blo 1510952 2269097 := bstep (se 2 (by rfl) ⟨850911, by rfl⟩ : syracuseStep 2269097 = 1701823) B1701823
theorem B3826217 : Blo 1510952 3826217 := bstep (se 2 (by rfl) ⟨1434831, by rfl⟩ : syracuseStep 3826217 = 2869663) B2869663
theorem B8610583 : Blo 1510952 8610583 := bstep (se 1 (by rfl) ⟨6457937, by rfl⟩ : syracuseStep 8610583 = 12915875) B12915875
theorem B3400775 : Blo 1510952 3400775 := bstep (se 1 (by rfl) ⟨2550581, by rfl⟩ : syracuseStep 3400775 = 5101163) B5101163
theorem B3401441 : Blo 1510952 3401441 := bstep (se 2 (by rfl) ⟨1275540, by rfl⟩ : syracuseStep 3401441 = 2551081) B2551081
theorem B4302695 : Blo 1510952 4302695 := bstep (se 1 (by rfl) ⟨3227021, by rfl⟩ : syracuseStep 4302695 = 6454043) B6454043
theorem B24520765 : Blo 1510952 24520765 := bstep (se 3 (by rfl) ⟨4597643, by rfl⟩ : syracuseStep 24520765 = 9195287) B9195287
theorem B3401855 : Blo 1510952 3401855 := bstep (se 1 (by rfl) ⟨2551391, by rfl⟩ : syracuseStep 3401855 = 5102783) B5102783
theorem B11634833 : Blo 1510952 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B5106023 : Blo 1510952 5106023 := bstep (se 1 (by rfl) ⟨3829517, by rfl⟩ : syracuseStep 5106023 = 7659035) B7659035
theorem B10898003 : Blo 1510952 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B23268383 : Blo 1510952 23268383 := bstep (se 1 (by rfl) ⟨17451287, by rfl⟩ : syracuseStep 23268383 = 34902575) B34902575
theorem B2870939 : Blo 1510952 2870939 := bstep (se 1 (by rfl) ⟨2153204, by rfl⟩ : syracuseStep 2870939 = 4306409) B4306409
theorem B2182847 : Blo 1510952 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B7262567 : Blo 1510952 7262567 := bstep (se 1 (by rfl) ⟨5446925, by rfl⟩ : syracuseStep 7262567 = 10893851) B10893851
theorem B1512063 : Blo 1510952 1512063 := bstep (se 1 (by rfl) ⟨1134047, by rfl⟩ : syracuseStep 1512063 = 2268095) B2268095
theorem B1512175 : Blo 1510952 1512175 := bstep (se 1 (by rfl) ⟨1134131, by rfl⟩ : syracuseStep 1512175 = 2268263) B2268263
theorem B74609747 : Blo 1510952 74609747 := bstep (se 1 (by rfl) ⟨55957310, by rfl⟩ : syracuseStep 74609747 = 111914621) B111914621
theorem B18379867 : Blo 1510952 18379867 := bstep (se 1 (by rfl) ⟨13784900, by rfl⟩ : syracuseStep 18379867 = 27569801) B27569801
theorem B6460519 : Blo 1510952 6460519 := bstep (se 1 (by rfl) ⟨4845389, by rfl⟩ : syracuseStep 6460519 = 9690779) B9690779
theorem B1512731 : Blo 1510952 1512731 := bstep (se 1 (by rfl) ⟨1134548, by rfl⟩ : syracuseStep 1512731 = 2269097) B2269097
theorem B8607167 : Blo 1510952 8607167 := bstep (se 1 (by rfl) ⟨6455375, by rfl⟩ : syracuseStep 8607167 = 12910751) B12910751
theorem B3274471 : Blo 1510952 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B201578327 : Blo 1510952 201578327 := bstep (se 1 (by rfl) ⟨151183745, by rfl⟩ : syracuseStep 201578327 = 302367491) B302367491
theorem B2152703 : Blo 1510952 2152703 := bstep (se 1 (by rfl) ⟨1614527, by rfl⟩ : syracuseStep 2152703 = 3229055) B3229055
theorem B2267615 : Blo 1510952 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B2267951 : Blo 1510952 2267951 := bstep (se 1 (by rfl) ⟨1700963, by rfl⟩ : syracuseStep 2267951 = 3401927) B3401927
theorem B2268329 : Blo 1510952 2268329 := bstep (se 2 (by rfl) ⟨850623, by rfl⟩ : syracuseStep 2268329 = 1701247) B1701247
theorem B6454505 : Blo 1510952 6454505 := bstep (se 2 (by rfl) ⟨2420439, by rfl⟩ : syracuseStep 6454505 = 4840879) B4840879
theorem B34905599 : Blo 1510952 34905599 := bstep (se 1 (by rfl) ⟨26179199, by rfl⟩ : syracuseStep 34905599 = 52358399) B52358399
theorem B2268827 : Blo 1510952 2268827 := bstep (se 1 (by rfl) ⟨1701620, by rfl⟩ : syracuseStep 2268827 = 3403241) B3403241
theorem B2268863 : Blo 1510952 2268863 := bstep (se 1 (by rfl) ⟨1701647, by rfl⟩ : syracuseStep 2268863 = 3403295) B3403295
theorem B2268911 : Blo 1510952 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B32694353 : Blo 1510952 32694353 := bstep (se 2 (by rfl) ⟨12260382, by rfl⟩ : syracuseStep 32694353 = 24520765) B24520765
theorem B4841711 : Blo 1510952 4841711 := bstep (se 1 (by rfl) ⟨3631283, by rfl⟩ : syracuseStep 4841711 = 7262567) B7262567
theorem B2868463 : Blo 1510952 2868463 := bstep (se 1 (by rfl) ⟨2151347, by rfl⟩ : syracuseStep 2868463 = 4302695) B4302695
theorem B4303003 : Blo 1510952 4303003 := bstep (se 1 (by rfl) ⟨3227252, by rfl⟩ : syracuseStep 4303003 = 6454505) B6454505
theorem B2550811 : Blo 1510952 2550811 := bstep (se 1 (by rfl) ⟨1913108, by rfl⟩ : syracuseStep 2550811 = 3826217) B3826217
theorem B5738111 : Blo 1510952 5738111 := bstep (se 1 (by rfl) ⟨4303583, by rfl⟩ : syracuseStep 5738111 = 8607167) B8607167
theorem B11480777 : Blo 1510952 11480777 := bstep (se 2 (by rfl) ⟨4305291, by rfl⟩ : syracuseStep 11480777 = 8610583) B8610583
theorem B134385551 : Blo 1510952 134385551 := bstep (se 1 (by rfl) ⟨100789163, by rfl⟩ : syracuseStep 134385551 = 201578327) B201578327
theorem B24506489 : Blo 1510952 24506489 := bstep (se 2 (by rfl) ⟨9189933, by rfl⟩ : syracuseStep 24506489 = 18379867) B18379867
theorem B8614025 : Blo 1510952 8614025 := bstep (se 2 (by rfl) ⟨3230259, by rfl⟩ : syracuseStep 8614025 = 6460519) B6460519
theorem B3404015 : Blo 1510952 3404015 := bstep (se 1 (by rfl) ⟨2553011, by rfl⟩ : syracuseStep 3404015 = 5106023) B5106023
theorem B1511743 : Blo 1510952 1511743 := bstep (se 1 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 1511743 = 2267615) B2267615
theorem B5820925 : Blo 1510952 5820925 := bstep (se 3 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 5820925 = 2182847) B2182847
theorem B1511967 : Blo 1510952 1511967 := bstep (se 1 (by rfl) ⟨1133975, by rfl⟩ : syracuseStep 1511967 = 2267951) B2267951
theorem B15512255 : Blo 1510952 15512255 := bstep (se 1 (by rfl) ⟨11634191, by rfl⟩ : syracuseStep 15512255 = 23268383) B23268383
theorem B1512219 : Blo 1510952 1512219 := bstep (se 1 (by rfl) ⟨1134164, by rfl⟩ : syracuseStep 1512219 = 2268329) B2268329
theorem B23270399 : Blo 1510952 23270399 := bstep (se 1 (by rfl) ⟨17452799, by rfl⟩ : syracuseStep 23270399 = 34905599) B34905599
theorem B1913959 : Blo 1510952 1913959 := bstep (se 1 (by rfl) ⟨1435469, by rfl⟩ : syracuseStep 1913959 = 2870939) B2870939
theorem B1512551 : Blo 1510952 1512551 := bstep (se 1 (by rfl) ⟨1134413, by rfl⟩ : syracuseStep 1512551 = 2268827) B2268827
theorem B1512575 : Blo 1510952 1512575 := bstep (se 1 (by rfl) ⟨1134431, by rfl⟩ : syracuseStep 1512575 = 2268863) B2268863
theorem B1512607 : Blo 1510952 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B5740541 : Blo 1510952 5740541 := bstep (se 3 (by rfl) ⟨1076351, by rfl⟩ : syracuseStep 5740541 = 2152703) B2152703
theorem B2267183 : Blo 1510952 2267183 := bstep (se 1 (by rfl) ⟨1700387, by rfl⟩ : syracuseStep 2267183 = 3400775) B3400775
theorem B49739831 : Blo 1510952 49739831 := bstep (se 1 (by rfl) ⟨37304873, by rfl⟩ : syracuseStep 49739831 = 74609747) B74609747
theorem B2267627 : Blo 1510952 2267627 := bstep (se 1 (by rfl) ⟨1700720, by rfl⟩ : syracuseStep 2267627 = 3401441) B3401441
theorem B17463845 : Blo 1510952 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B2267903 : Blo 1510952 2267903 := bstep (se 1 (by rfl) ⟨1700927, by rfl⟩ : syracuseStep 2267903 = 3401855) B3401855
theorem B7756555 : Blo 1510952 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B7265335 : Blo 1510952 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B5742683 : Blo 1510952 5742683 := bstep (se 1 (by rfl) ⟨4307012, by rfl⟩ : syracuseStep 5742683 = 8614025) B8614025
theorem B3227807 : Blo 1510952 3227807 := bstep (se 1 (by rfl) ⟨2420855, by rfl⟩ : syracuseStep 3227807 = 4841711) B4841711
theorem B2269343 : Blo 1510952 2269343 := bstep (se 1 (by rfl) ⟨1702007, by rfl⟩ : syracuseStep 2269343 = 3404015) B3404015
theorem B3827027 : Blo 1510952 3827027 := bstep (se 1 (by rfl) ⟨2870270, by rfl⟩ : syracuseStep 3827027 = 5740541) B5740541
theorem B3401081 : Blo 1510952 3401081 := bstep (se 2 (by rfl) ⟨1275405, by rfl⟩ : syracuseStep 3401081 = 2550811) B2550811
theorem B11642563 : Blo 1510952 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B7653851 : Blo 1510952 7653851 := bstep (se 1 (by rfl) ⟨5740388, by rfl⟩ : syracuseStep 7653851 = 11480777) B11480777
theorem B89590367 : Blo 1510952 89590367 := bstep (se 1 (by rfl) ⟨67192775, by rfl⟩ : syracuseStep 89590367 = 134385551) B134385551
theorem B5737337 : Blo 1510952 5737337 := bstep (se 2 (by rfl) ⟨2151501, by rfl⟩ : syracuseStep 5737337 = 4303003) B4303003
theorem B65350637 : Blo 1510952 65350637 := bstep (se 3 (by rfl) ⟨12253244, by rfl⟩ : syracuseStep 65350637 = 24506489) B24506489
theorem B10341503 : Blo 1510952 10341503 := bstep (se 1 (by rfl) ⟨7756127, by rfl⟩ : syracuseStep 10341503 = 15512255) B15512255
theorem B7761233 : Blo 1510952 7761233 := bstep (se 2 (by rfl) ⟨2910462, by rfl⟩ : syracuseStep 7761233 = 5820925) B5820925
theorem B10342073 : Blo 1510952 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B1511455 : Blo 1510952 1511455 := bstep (se 1 (by rfl) ⟨1133591, by rfl⟩ : syracuseStep 1511455 = 2267183) B2267183
theorem B9687113 : Blo 1510952 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B2551945 : Blo 1510952 2551945 := bstep (se 2 (by rfl) ⟨956979, by rfl⟩ : syracuseStep 2551945 = 1913959) B1913959
theorem B1511751 : Blo 1510952 1511751 := bstep (se 1 (by rfl) ⟨1133813, by rfl⟩ : syracuseStep 1511751 = 2267627) B2267627
theorem B1511935 : Blo 1510952 1511935 := bstep (se 1 (by rfl) ⟨1133951, by rfl⟩ : syracuseStep 1511935 = 2267903) B2267903
theorem B21796235 : Blo 1510952 21796235 := bstep (se 1 (by rfl) ⟨16347176, by rfl⟩ : syracuseStep 21796235 = 32694353) B32694353
theorem B15513599 : Blo 1510952 15513599 := bstep (se 1 (by rfl) ⟨11635199, by rfl⟩ : syracuseStep 15513599 = 23270399) B23270399
theorem B33159887 : Blo 1510952 33159887 := bstep (se 1 (by rfl) ⟨24869915, by rfl⟩ : syracuseStep 33159887 = 49739831) B49739831
theorem B3824617 : Blo 1510952 3824617 := bstep (se 2 (by rfl) ⟨1434231, by rfl⟩ : syracuseStep 3824617 = 2868463) B2868463
theorem B3825407 : Blo 1510952 3825407 := bstep (se 1 (by rfl) ⟨2869055, by rfl⟩ : syracuseStep 3825407 = 5738111) B5738111
theorem B43567091 : Blo 1510952 43567091 := bstep (se 1 (by rfl) ⟨32675318, by rfl⟩ : syracuseStep 43567091 = 65350637) B65350637
theorem B2550271 : Blo 1510952 2550271 := bstep (se 1 (by rfl) ⟨1912703, by rfl⟩ : syracuseStep 2550271 = 3825407) B3825407
theorem B6458075 : Blo 1510952 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B3828455 : Blo 1510952 3828455 := bstep (se 1 (by rfl) ⟨2871341, by rfl⟩ : syracuseStep 3828455 = 5742683) B5742683
theorem B3402593 : Blo 1510952 3402593 := bstep (se 2 (by rfl) ⟨1275972, by rfl⟩ : syracuseStep 3402593 = 2551945) B2551945
theorem B2551351 : Blo 1510952 2551351 := bstep (se 1 (by rfl) ⟨1913513, by rfl⟩ : syracuseStep 2551351 = 3827027) B3827027
theorem B5099489 : Blo 1510952 5099489 := bstep (se 2 (by rfl) ⟨1912308, by rfl⟩ : syracuseStep 5099489 = 3824617) B3824617
theorem B10342399 : Blo 1510952 10342399 := bstep (se 1 (by rfl) ⟨7756799, by rfl⟩ : syracuseStep 10342399 = 15513599) B15513599
theorem B22106591 : Blo 1510952 22106591 := bstep (se 1 (by rfl) ⟨16579943, by rfl⟩ : syracuseStep 22106591 = 33159887) B33159887
theorem B6894335 : Blo 1510952 6894335 := bstep (se 1 (by rfl) ⟨5170751, by rfl⟩ : syracuseStep 6894335 = 10341503) B10341503
theorem B5174155 : Blo 1510952 5174155 := bstep (se 1 (by rfl) ⟨3880616, by rfl⟩ : syracuseStep 5174155 = 7761233) B7761233
theorem B6894715 : Blo 1510952 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B1512895 : Blo 1510952 1512895 := bstep (se 1 (by rfl) ⟨1134671, by rfl⟩ : syracuseStep 1512895 = 2269343) B2269343
theorem B8607485 : Blo 1510952 8607485 := bstep (se 3 (by rfl) ⟨1613903, by rfl⟩ : syracuseStep 8607485 = 3227807) B3227807
theorem B2267387 : Blo 1510952 2267387 := bstep (se 1 (by rfl) ⟨1700540, by rfl⟩ : syracuseStep 2267387 = 3401081) B3401081
theorem B14530823 : Blo 1510952 14530823 := bstep (se 1 (by rfl) ⟨10898117, by rfl⟩ : syracuseStep 14530823 = 21796235) B21796235
theorem B5102567 : Blo 1510952 5102567 := bstep (se 1 (by rfl) ⟨3826925, by rfl⟩ : syracuseStep 5102567 = 7653851) B7653851
theorem B59726911 : Blo 1510952 59726911 := bstep (se 1 (by rfl) ⟨44795183, by rfl⟩ : syracuseStep 59726911 = 89590367) B89590367
theorem B3824891 : Blo 1510952 3824891 := bstep (se 1 (by rfl) ⟨2868668, by rfl⟩ : syracuseStep 3824891 = 5737337) B5737337
theorem B15523417 : Blo 1510952 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B14737727 : Blo 1510952 14737727 := bstep (se 1 (by rfl) ⟨11053295, by rfl⟩ : syracuseStep 14737727 = 22106591) B22106591
theorem B4596223 : Blo 1510952 4596223 := bstep (se 1 (by rfl) ⟨3447167, by rfl⟩ : syracuseStep 4596223 = 6894335) B6894335
theorem B3400361 : Blo 1510952 3400361 := bstep (se 2 (by rfl) ⟨1275135, by rfl⟩ : syracuseStep 3400361 = 2550271) B2550271
theorem B6898873 : Blo 1510952 6898873 := bstep (se 2 (by rfl) ⟨2587077, by rfl⟩ : syracuseStep 6898873 = 5174155) B5174155
theorem B79635881 : Blo 1510952 79635881 := bstep (se 2 (by rfl) ⟨29863455, by rfl⟩ : syracuseStep 79635881 = 59726911) B59726911
theorem B9192953 : Blo 1510952 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B3401711 : Blo 1510952 3401711 := bstep (se 1 (by rfl) ⟨2551283, by rfl⟩ : syracuseStep 3401711 = 5102567) B5102567
theorem B3401801 : Blo 1510952 3401801 := bstep (se 2 (by rfl) ⟨1275675, by rfl⟩ : syracuseStep 3401801 = 2551351) B2551351
theorem B2549927 : Blo 1510952 2549927 := bstep (se 1 (by rfl) ⟨1912445, by rfl⟩ : syracuseStep 2549927 = 3824891) B3824891
theorem B13789865 : Blo 1510952 13789865 := bstep (se 2 (by rfl) ⟨5171199, by rfl⟩ : syracuseStep 13789865 = 10342399) B10342399
theorem B5738323 : Blo 1510952 5738323 := bstep (se 1 (by rfl) ⟨4303742, by rfl⟩ : syracuseStep 5738323 = 8607485) B8607485
theorem B29044727 : Blo 1510952 29044727 := bstep (se 1 (by rfl) ⟨21783545, by rfl⟩ : syracuseStep 29044727 = 43567091) B43567091
theorem B1511591 : Blo 1510952 1511591 := bstep (se 1 (by rfl) ⟨1133693, by rfl⟩ : syracuseStep 1511591 = 2267387) B2267387
theorem B9687215 : Blo 1510952 9687215 := bstep (se 1 (by rfl) ⟨7265411, by rfl⟩ : syracuseStep 9687215 = 14530823) B14530823
theorem B4305383 : Blo 1510952 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B2552303 : Blo 1510952 2552303 := bstep (se 1 (by rfl) ⟨1914227, by rfl⟩ : syracuseStep 2552303 = 3828455) B3828455
theorem B20697889 : Blo 1510952 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B2268395 : Blo 1510952 2268395 := bstep (se 1 (by rfl) ⟨1701296, by rfl⟩ : syracuseStep 2268395 = 3402593) B3402593
theorem B3399659 : Blo 1510952 3399659 := bstep (se 1 (by rfl) ⟨2549744, by rfl⟩ : syracuseStep 3399659 = 5099489) B5099489
theorem B6128297 : Blo 1510952 6128297 := bstep (se 2 (by rfl) ⟨2298111, by rfl⟩ : syracuseStep 6128297 = 4596223) B4596223
theorem B6128635 : Blo 1510952 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B9193243 : Blo 1510952 9193243 := bstep (se 1 (by rfl) ⟨6894932, by rfl⟩ : syracuseStep 9193243 = 13789865) B13789865
theorem B6458143 : Blo 1510952 6458143 := bstep (se 1 (by rfl) ⟨4843607, by rfl⟩ : syracuseStep 6458143 = 9687215) B9687215
theorem B9825151 : Blo 1510952 9825151 := bstep (se 1 (by rfl) ⟨7368863, by rfl⟩ : syracuseStep 9825151 = 14737727) B14737727
theorem B2870255 : Blo 1510952 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B1699951 : Blo 1510952 1699951 := bstep (se 1 (by rfl) ⟨1274963, by rfl⟩ : syracuseStep 1699951 = 2549927) B2549927
theorem B1512263 : Blo 1510952 1512263 := bstep (se 1 (by rfl) ⟨1134197, by rfl⟩ : syracuseStep 1512263 = 2268395) B2268395
theorem B2266439 : Blo 1510952 2266439 := bstep (se 1 (by rfl) ⟨1699829, by rfl⟩ : syracuseStep 2266439 = 3399659) B3399659
theorem B19363151 : Blo 1510952 19363151 := bstep (se 1 (by rfl) ⟨14522363, by rfl⟩ : syracuseStep 19363151 = 29044727) B29044727
theorem B1701535 : Blo 1510952 1701535 := bstep (se 1 (by rfl) ⟨1276151, by rfl⟩ : syracuseStep 1701535 = 2552303) B2552303
theorem B2266907 : Blo 1510952 2266907 := bstep (se 1 (by rfl) ⟨1700180, by rfl⟩ : syracuseStep 2266907 = 3400361) B3400361
theorem B53090587 : Blo 1510952 53090587 := bstep (se 1 (by rfl) ⟨39817940, by rfl⟩ : syracuseStep 53090587 = 79635881) B79635881
theorem B27597185 : Blo 1510952 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B2267807 : Blo 1510952 2267807 := bstep (se 1 (by rfl) ⟨1700855, by rfl⟩ : syracuseStep 2267807 = 3401711) B3401711
theorem B2267867 : Blo 1510952 2267867 := bstep (se 1 (by rfl) ⟨1700900, by rfl⟩ : syracuseStep 2267867 = 3401801) B3401801
theorem B9198497 : Blo 1510952 9198497 := bstep (se 2 (by rfl) ⟨3449436, by rfl⟩ : syracuseStep 9198497 = 6898873) B6898873
theorem B7651097 : Blo 1510952 7651097 := bstep (se 2 (by rfl) ⟨2869161, by rfl⟩ : syracuseStep 7651097 = 5738323) B5738323
theorem B70787449 : Blo 1510952 70787449 := bstep (se 2 (by rfl) ⟨26545293, by rfl⟩ : syracuseStep 70787449 = 53090587) B53090587
theorem B8610857 : Blo 1510952 8610857 := bstep (se 2 (by rfl) ⟨3229071, by rfl⟩ : syracuseStep 8610857 = 6458143) B6458143
theorem B13100201 : Blo 1510952 13100201 := bstep (se 2 (by rfl) ⟨4912575, by rfl⟩ : syracuseStep 13100201 = 9825151) B9825151
theorem B12257657 : Blo 1510952 12257657 := bstep (se 2 (by rfl) ⟨4596621, by rfl⟩ : syracuseStep 12257657 = 9193243) B9193243
theorem B7654013 : Blo 1510952 7654013 := bstep (se 3 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 7654013 = 2870255) B2870255
theorem B1510959 : Blo 1510952 1510959 := bstep (se 1 (by rfl) ⟨1133219, by rfl⟩ : syracuseStep 1510959 = 2266439) B2266439
theorem B1511271 : Blo 1510952 1511271 := bstep (se 1 (by rfl) ⟨1133453, by rfl⟩ : syracuseStep 1511271 = 2266907) B2266907
theorem B8171513 : Blo 1510952 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B1511871 : Blo 1510952 1511871 := bstep (se 1 (by rfl) ⟨1133903, by rfl⟩ : syracuseStep 1511871 = 2267807) B2267807
theorem B1511911 : Blo 1510952 1511911 := bstep (se 1 (by rfl) ⟨1133933, by rfl⟩ : syracuseStep 1511911 = 2267867) B2267867
theorem B6132331 : Blo 1510952 6132331 := bstep (se 1 (by rfl) ⟨4599248, by rfl⟩ : syracuseStep 6132331 = 9198497) B9198497
theorem B5100731 : Blo 1510952 5100731 := bstep (se 1 (by rfl) ⟨3825548, by rfl⟩ : syracuseStep 5100731 = 7651097) B7651097
theorem B2266601 : Blo 1510952 2266601 := bstep (se 2 (by rfl) ⟨849975, by rfl⟩ : syracuseStep 2266601 = 1699951) B1699951
theorem B4085531 : Blo 1510952 4085531 := bstep (se 1 (by rfl) ⟨3064148, by rfl⟩ : syracuseStep 4085531 = 6128297) B6128297
theorem B12908767 : Blo 1510952 12908767 := bstep (se 1 (by rfl) ⟨9681575, by rfl⟩ : syracuseStep 12908767 = 19363151) B19363151
theorem B18398123 : Blo 1510952 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B2268713 : Blo 1510952 2268713 := bstep (se 2 (by rfl) ⟨850767, by rfl⟩ : syracuseStep 2268713 = 1701535) B1701535
theorem B17211689 : Blo 1510952 17211689 := bstep (se 2 (by rfl) ⟨6454383, by rfl⟩ : syracuseStep 17211689 = 12908767) B12908767
theorem B8733467 : Blo 1510952 8733467 := bstep (se 1 (by rfl) ⟨6550100, by rfl⟩ : syracuseStep 8733467 = 13100201) B13100201
theorem B3400487 : Blo 1510952 3400487 := bstep (se 1 (by rfl) ⟨2550365, by rfl⟩ : syracuseStep 3400487 = 5100731) B5100731
theorem B12265415 : Blo 1510952 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B32705765 : Blo 1510952 32705765 := bstep (se 4 (by rfl) ⟨3066165, by rfl⟩ : syracuseStep 32705765 = 6132331) B6132331
theorem B1511067 : Blo 1510952 1511067 := bstep (se 1 (by rfl) ⟨1133300, by rfl⟩ : syracuseStep 1511067 = 2266601) B2266601
theorem B2723687 : Blo 1510952 2723687 := bstep (se 1 (by rfl) ⟨2042765, by rfl⟩ : syracuseStep 2723687 = 4085531) B4085531
theorem B8171771 : Blo 1510952 8171771 := bstep (se 1 (by rfl) ⟨6128828, by rfl⟩ : syracuseStep 8171771 = 12257657) B12257657
theorem B377533061 : Blo 1510952 377533061 := bstep (se 4 (by rfl) ⟨35393724, by rfl⟩ : syracuseStep 377533061 = 70787449) B70787449
theorem B1512475 : Blo 1510952 1512475 := bstep (se 1 (by rfl) ⟨1134356, by rfl⟩ : syracuseStep 1512475 = 2268713) B2268713
theorem B5740571 : Blo 1510952 5740571 := bstep (se 1 (by rfl) ⟨4305428, by rfl⟩ : syracuseStep 5740571 = 8610857) B8610857
theorem B5102675 : Blo 1510952 5102675 := bstep (se 1 (by rfl) ⟨3827006, by rfl⟩ : syracuseStep 5102675 = 7654013) B7654013
theorem B5447675 : Blo 1510952 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B21791389 : Blo 1510952 21791389 := bstep (se 3 (by rfl) ⟨4085885, by rfl⟩ : syracuseStep 21791389 = 8171771) B8171771
theorem B8176943 : Blo 1510952 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B3827047 : Blo 1510952 3827047 := bstep (se 1 (by rfl) ⟨2870285, by rfl⟩ : syracuseStep 3827047 = 5740571) B5740571
theorem B3401783 : Blo 1510952 3401783 := bstep (se 1 (by rfl) ⟨2551337, by rfl⟩ : syracuseStep 3401783 = 5102675) B5102675
theorem B14527133 : Blo 1510952 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B21803843 : Blo 1510952 21803843 := bstep (se 1 (by rfl) ⟨16352882, by rfl⟩ : syracuseStep 21803843 = 32705765) B32705765
theorem B1815791 : Blo 1510952 1815791 := bstep (se 1 (by rfl) ⟨1361843, by rfl⟩ : syracuseStep 1815791 = 2723687) B2723687
theorem B11474459 : Blo 1510952 11474459 := bstep (se 1 (by rfl) ⟨8605844, by rfl⟩ : syracuseStep 11474459 = 17211689) B17211689
theorem B251688707 : Blo 1510952 251688707 := bstep (se 1 (by rfl) ⟨188766530, by rfl⟩ : syracuseStep 251688707 = 377533061) B377533061
theorem B2266991 : Blo 1510952 2266991 := bstep (se 1 (by rfl) ⟨1700243, by rfl⟩ : syracuseStep 2266991 = 3400487) B3400487
theorem B23289245 : Blo 1510952 23289245 := bstep (se 3 (by rfl) ⟨4366733, by rfl⟩ : syracuseStep 23289245 = 8733467) B8733467
theorem B4842109 : Blo 1510952 4842109 := bstep (se 3 (by rfl) ⟨907895, by rfl⟩ : syracuseStep 4842109 = 1815791) B1815791
theorem B9684755 : Blo 1510952 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B15526163 : Blo 1510952 15526163 := bstep (se 1 (by rfl) ⟨11644622, by rfl⟩ : syracuseStep 15526163 = 23289245) B23289245
theorem B5451295 : Blo 1510952 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B167792471 : Blo 1510952 167792471 := bstep (se 1 (by rfl) ⟨125844353, by rfl⟩ : syracuseStep 167792471 = 251688707) B251688707
theorem B1511327 : Blo 1510952 1511327 := bstep (se 1 (by rfl) ⟨1133495, by rfl⟩ : syracuseStep 1511327 = 2266991) B2266991
theorem B58143581 : Blo 1510952 58143581 := bstep (se 3 (by rfl) ⟨10901921, by rfl⟩ : syracuseStep 58143581 = 21803843) B21803843
theorem B29055185 : Blo 1510952 29055185 := bstep (se 2 (by rfl) ⟨10895694, by rfl⟩ : syracuseStep 29055185 = 21791389) B21791389
theorem B7649639 : Blo 1510952 7649639 := bstep (se 1 (by rfl) ⟨5737229, by rfl⟩ : syracuseStep 7649639 = 11474459) B11474459
theorem B2267855 : Blo 1510952 2267855 := bstep (se 1 (by rfl) ⟨1700891, by rfl⟩ : syracuseStep 2267855 = 3401783) B3401783
theorem B5102729 : Blo 1510952 5102729 := bstep (se 2 (by rfl) ⟨1913523, by rfl⟩ : syracuseStep 5102729 = 3827047) B3827047
theorem B6456145 : Blo 1510952 6456145 := bstep (se 2 (by rfl) ⟨2421054, by rfl⟩ : syracuseStep 6456145 = 4842109) B4842109
theorem B6456503 : Blo 1510952 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B7268393 : Blo 1510952 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B3401819 : Blo 1510952 3401819 := bstep (se 1 (by rfl) ⟨2551364, by rfl⟩ : syracuseStep 3401819 = 5102729) B5102729
theorem B19370123 : Blo 1510952 19370123 := bstep (se 1 (by rfl) ⟨14527592, by rfl⟩ : syracuseStep 19370123 = 29055185) B29055185
theorem B10350775 : Blo 1510952 10350775 := bstep (se 1 (by rfl) ⟨7763081, by rfl⟩ : syracuseStep 10350775 = 15526163) B15526163
theorem B5099759 : Blo 1510952 5099759 := bstep (se 1 (by rfl) ⟨3824819, by rfl⟩ : syracuseStep 5099759 = 7649639) B7649639
theorem B1511903 : Blo 1510952 1511903 := bstep (se 1 (by rfl) ⟨1133927, by rfl⟩ : syracuseStep 1511903 = 2267855) B2267855
theorem B38762387 : Blo 1510952 38762387 := bstep (se 1 (by rfl) ⟨29071790, by rfl⟩ : syracuseStep 38762387 = 58143581) B58143581
theorem B111861647 : Blo 1510952 111861647 := bstep (se 1 (by rfl) ⟨83896235, by rfl⟩ : syracuseStep 111861647 = 167792471) B167792471
theorem B3399839 : Blo 1510952 3399839 := bstep (se 1 (by rfl) ⟨2549879, by rfl⟩ : syracuseStep 3399839 = 5099759) B5099759
theorem B74574431 : Blo 1510952 74574431 := bstep (se 1 (by rfl) ⟨55930823, by rfl⟩ : syracuseStep 74574431 = 111861647) B111861647
theorem B12913415 : Blo 1510952 12913415 := bstep (se 1 (by rfl) ⟨9685061, by rfl⟩ : syracuseStep 12913415 = 19370123) B19370123
theorem B4304335 : Blo 1510952 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B25841591 : Blo 1510952 25841591 := bstep (se 1 (by rfl) ⟨19381193, by rfl⟩ : syracuseStep 25841591 = 38762387) B38762387
theorem B4845595 : Blo 1510952 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B13801033 : Blo 1510952 13801033 := bstep (se 2 (by rfl) ⟨5175387, by rfl⟩ : syracuseStep 13801033 = 10350775) B10350775
theorem B8608193 : Blo 1510952 8608193 := bstep (se 2 (by rfl) ⟨3228072, by rfl⟩ : syracuseStep 8608193 = 6456145) B6456145
theorem B2267879 : Blo 1510952 2267879 := bstep (se 1 (by rfl) ⟨1700909, by rfl⟩ : syracuseStep 2267879 = 3401819) B3401819
theorem B18401377 : Blo 1510952 18401377 := bstep (se 2 (by rfl) ⟨6900516, by rfl⟩ : syracuseStep 18401377 = 13801033) B13801033
theorem B5738795 : Blo 1510952 5738795 := bstep (se 1 (by rfl) ⟨4304096, by rfl⟩ : syracuseStep 5738795 = 8608193) B8608193
theorem B1511919 : Blo 1510952 1511919 := bstep (se 1 (by rfl) ⟨1133939, by rfl⟩ : syracuseStep 1511919 = 2267879) B2267879
theorem B5739113 : Blo 1510952 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B6460793 : Blo 1510952 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B2266559 : Blo 1510952 2266559 := bstep (se 1 (by rfl) ⟨1699919, by rfl⟩ : syracuseStep 2266559 = 3399839) B3399839
theorem B49716287 : Blo 1510952 49716287 := bstep (se 1 (by rfl) ⟨37287215, by rfl⟩ : syracuseStep 49716287 = 74574431) B74574431
theorem B8608943 : Blo 1510952 8608943 := bstep (se 1 (by rfl) ⟨6456707, by rfl⟩ : syracuseStep 8608943 = 12913415) B12913415
theorem B17227727 : Blo 1510952 17227727 := bstep (se 1 (by rfl) ⟨12920795, by rfl⟩ : syracuseStep 17227727 = 25841591) B25841591
theorem B24535169 : Blo 1510952 24535169 := bstep (se 2 (by rfl) ⟨9200688, by rfl⟩ : syracuseStep 24535169 = 18401377) B18401377
theorem B3825863 : Blo 1510952 3825863 := bstep (se 1 (by rfl) ⟨2869397, by rfl⟩ : syracuseStep 3825863 = 5738795) B5738795
theorem B3826075 : Blo 1510952 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B1511039 : Blo 1510952 1511039 := bstep (se 1 (by rfl) ⟨1133279, by rfl⟩ : syracuseStep 1511039 = 2266559) B2266559
theorem B5739295 : Blo 1510952 5739295 := bstep (se 1 (by rfl) ⟨4304471, by rfl⟩ : syracuseStep 5739295 = 8608943) B8608943
theorem B4307195 : Blo 1510952 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B33144191 : Blo 1510952 33144191 := bstep (se 1 (by rfl) ⟨24858143, by rfl⟩ : syracuseStep 33144191 = 49716287) B49716287
theorem B11485151 : Blo 1510952 11485151 := bstep (se 1 (by rfl) ⟨8613863, by rfl⟩ : syracuseStep 11485151 = 17227727) B17227727
theorem B7652393 : Blo 1510952 7652393 := bstep (se 2 (by rfl) ⟨2869647, by rfl⟩ : syracuseStep 7652393 = 5739295) B5739295
theorem B22096127 : Blo 1510952 22096127 := bstep (se 1 (by rfl) ⟨16572095, by rfl⟩ : syracuseStep 22096127 = 33144191) B33144191
theorem B2550575 : Blo 1510952 2550575 := bstep (se 1 (by rfl) ⟨1912931, by rfl⟩ : syracuseStep 2550575 = 3825863) B3825863
theorem B2871463 : Blo 1510952 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B7656767 : Blo 1510952 7656767 := bstep (se 1 (by rfl) ⟨5742575, by rfl⟩ : syracuseStep 7656767 = 11485151) B11485151
theorem B16356779 : Blo 1510952 16356779 := bstep (se 1 (by rfl) ⟨12267584, by rfl⟩ : syracuseStep 16356779 = 24535169) B24535169
theorem B5101433 : Blo 1510952 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B5104511 : Blo 1510952 5104511 := bstep (se 1 (by rfl) ⟨3828383, by rfl⟩ : syracuseStep 5104511 = 7656767) B7656767
theorem B10904519 : Blo 1510952 10904519 := bstep (se 1 (by rfl) ⟨8178389, by rfl⟩ : syracuseStep 10904519 = 16356779) B16356779
theorem B3400955 : Blo 1510952 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B14730751 : Blo 1510952 14730751 := bstep (se 1 (by rfl) ⟨11048063, by rfl⟩ : syracuseStep 14730751 = 22096127) B22096127
theorem B3828617 : Blo 1510952 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B1700383 : Blo 1510952 1700383 := bstep (se 1 (by rfl) ⟨1275287, by rfl⟩ : syracuseStep 1700383 = 2550575) B2550575
theorem B5101595 : Blo 1510952 5101595 := bstep (se 1 (by rfl) ⟨3826196, by rfl⟩ : syracuseStep 5101595 = 7652393) B7652393
theorem B3401063 : Blo 1510952 3401063 := bstep (se 1 (by rfl) ⟨2550797, by rfl⟩ : syracuseStep 3401063 = 5101595) B5101595
theorem B78564005 : Blo 1510952 78564005 := bstep (se 4 (by rfl) ⟨7365375, by rfl⟩ : syracuseStep 78564005 = 14730751) B14730751
theorem B3403007 : Blo 1510952 3403007 := bstep (se 1 (by rfl) ⟨2552255, by rfl⟩ : syracuseStep 3403007 = 5104511) B5104511
theorem B7269679 : Blo 1510952 7269679 := bstep (se 1 (by rfl) ⟨5452259, by rfl⟩ : syracuseStep 7269679 = 10904519) B10904519
theorem B2552411 : Blo 1510952 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B2267177 : Blo 1510952 2267177 := bstep (se 2 (by rfl) ⟨850191, by rfl⟩ : syracuseStep 2267177 = 1700383) B1700383
theorem B2267303 : Blo 1510952 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B9692905 : Blo 1510952 9692905 := bstep (se 2 (by rfl) ⟨3634839, by rfl⟩ : syracuseStep 9692905 = 7269679) B7269679
theorem B1511451 : Blo 1510952 1511451 := bstep (se 1 (by rfl) ⟨1133588, by rfl⟩ : syracuseStep 1511451 = 2267177) B2267177
theorem B1511535 : Blo 1510952 1511535 := bstep (se 1 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 1511535 = 2267303) B2267303
theorem B52376003 : Blo 1510952 52376003 := bstep (se 1 (by rfl) ⟨39282002, by rfl⟩ : syracuseStep 52376003 = 78564005) B78564005
theorem B1701607 : Blo 1510952 1701607 := bstep (se 1 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 1701607 = 2552411) B2552411
theorem B2267375 : Blo 1510952 2267375 := bstep (se 1 (by rfl) ⟨1700531, by rfl⟩ : syracuseStep 2267375 = 3401063) B3401063
theorem B2268671 : Blo 1510952 2268671 := bstep (se 1 (by rfl) ⟨1701503, by rfl⟩ : syracuseStep 2268671 = 3403007) B3403007
theorem B34917335 : Blo 1510952 34917335 := bstep (se 1 (by rfl) ⟨26188001, by rfl⟩ : syracuseStep 34917335 = 52376003) B52376003
theorem B1511583 : Blo 1510952 1511583 := bstep (se 1 (by rfl) ⟨1133687, by rfl⟩ : syracuseStep 1511583 = 2267375) B2267375
theorem B12923873 : Blo 1510952 12923873 := bstep (se 2 (by rfl) ⟨4846452, by rfl⟩ : syracuseStep 12923873 = 9692905) B9692905
theorem B1512447 : Blo 1510952 1512447 := bstep (se 1 (by rfl) ⟨1134335, by rfl⟩ : syracuseStep 1512447 = 2268671) B2268671
theorem B2268809 : Blo 1510952 2268809 := bstep (se 2 (by rfl) ⟨850803, by rfl⟩ : syracuseStep 2268809 = 1701607) B1701607
theorem B23278223 : Blo 1510952 23278223 := bstep (se 1 (by rfl) ⟨17458667, by rfl⟩ : syracuseStep 23278223 = 34917335) B34917335
theorem B1512539 : Blo 1510952 1512539 := bstep (se 1 (by rfl) ⟨1134404, by rfl⟩ : syracuseStep 1512539 = 2268809) B2268809
theorem B8615915 : Blo 1510952 8615915 := bstep (se 1 (by rfl) ⟨6461936, by rfl⟩ : syracuseStep 8615915 = 12923873) B12923873
theorem B5743943 : Blo 1510952 5743943 := bstep (se 1 (by rfl) ⟨4307957, by rfl⟩ : syracuseStep 5743943 = 8615915) B8615915
theorem B62075261 : Blo 1510952 62075261 := bstep (se 3 (by rfl) ⟨11639111, by rfl⟩ : syracuseStep 62075261 = 23278223) B23278223
theorem B3829295 : Blo 1510952 3829295 := bstep (se 1 (by rfl) ⟨2871971, by rfl⟩ : syracuseStep 3829295 = 5743943) B5743943
theorem B165534029 : Blo 1510952 165534029 := bstep (se 3 (by rfl) ⟨31037630, by rfl⟩ : syracuseStep 165534029 = 62075261) B62075261
theorem B110356019 : Blo 1510952 110356019 := bstep (se 1 (by rfl) ⟨82767014, by rfl⟩ : syracuseStep 110356019 = 165534029) B165534029
theorem B2552863 : Blo 1510952 2552863 := bstep (se 1 (by rfl) ⟨1914647, by rfl⟩ : syracuseStep 2552863 = 3829295) B3829295
theorem B3403817 : Blo 1510952 3403817 := bstep (se 2 (by rfl) ⟨1276431, by rfl⟩ : syracuseStep 3403817 = 2552863) B2552863
theorem B73570679 : Blo 1510952 73570679 := bstep (se 1 (by rfl) ⟨55178009, by rfl⟩ : syracuseStep 73570679 = 110356019) B110356019
theorem B2269211 : Blo 1510952 2269211 := bstep (se 1 (by rfl) ⟨1701908, by rfl⟩ : syracuseStep 2269211 = 3403817) B3403817
theorem B49047119 : Blo 1510952 49047119 := bstep (se 1 (by rfl) ⟨36785339, by rfl⟩ : syracuseStep 49047119 = 73570679) B73570679
theorem B32698079 : Blo 1510952 32698079 := bstep (se 1 (by rfl) ⟨24523559, by rfl⟩ : syracuseStep 32698079 = 49047119) B49047119
theorem B1512807 : Blo 1510952 1512807 := bstep (se 1 (by rfl) ⟨1134605, by rfl⟩ : syracuseStep 1512807 = 2269211) B2269211
theorem B21798719 : Blo 1510952 21798719 := bstep (se 1 (by rfl) ⟨16349039, by rfl⟩ : syracuseStep 21798719 = 32698079) B32698079
theorem B14532479 : Blo 1510952 14532479 := bstep (se 1 (by rfl) ⟨10899359, by rfl⟩ : syracuseStep 14532479 = 21798719) B21798719
theorem B9688319 : Blo 1510952 9688319 := bstep (se 1 (by rfl) ⟨7266239, by rfl⟩ : syracuseStep 9688319 = 14532479) B14532479
theorem B6458879 : Blo 1510952 6458879 := bstep (se 1 (by rfl) ⟨4844159, by rfl⟩ : syracuseStep 6458879 = 9688319) B9688319
theorem B4305919 : Blo 1510952 4305919 := bstep (se 1 (by rfl) ⟨3229439, by rfl⟩ : syracuseStep 4305919 = 6458879) B6458879
theorem B5741225 : Blo 1510952 5741225 := bstep (se 2 (by rfl) ⟨2152959, by rfl⟩ : syracuseStep 5741225 = 4305919) B4305919
theorem B3827483 : Blo 1510952 3827483 := bstep (se 1 (by rfl) ⟨2870612, by rfl⟩ : syracuseStep 3827483 = 5741225) B5741225
theorem B2551655 : Blo 1510952 2551655 := bstep (se 1 (by rfl) ⟨1913741, by rfl⟩ : syracuseStep 2551655 = 3827483) B3827483
theorem B1701103 : Blo 1510952 1701103 := bstep (se 1 (by rfl) ⟨1275827, by rfl⟩ : syracuseStep 1701103 = 2551655) B2551655
theorem B2268137 : Blo 1510952 2268137 := bstep (se 2 (by rfl) ⟨850551, by rfl⟩ : syracuseStep 2268137 = 1701103) B1701103
theorem B1512091 : Blo 1510952 1512091 := bstep (se 1 (by rfl) ⟨1134068, by rfl⟩ : syracuseStep 1512091 = 2268137) B2268137

theorem C0 (j : ℕ) (h1 : 377738 ≤ j) (h2 : j ≤ 378237) : Blo 1510952 (4 * j + 3) := by
  interval_cases j
  · exact B1510955
  · exact B1510959
  · exact B1510963
  · exact B1510967
  · exact B1510971
  · exact B1510975
  · exact B1510979
  · exact B1510983
  · exact B1510987
  · exact B1510991
  · exact B1510995
  · exact B1510999
  · exact B1511003
  · exact B1511007
  · exact B1511011
  · exact B1511015
  · exact B1511019
  · exact B1511023
  · exact B1511027
  · exact B1511031
  · exact B1511035
  · exact B1511039
  · exact B1511043
  · exact B1511047
  · exact B1511051
  · exact B1511055
  · exact B1511059
  · exact B1511063
  · exact B1511067
  · exact B1511071
  · exact B1511075
  · exact B1511079
  · exact B1511083
  · exact B1511087
  · exact B1511091
  · exact B1511095
  · exact B1511099
  · exact B1511103
  · exact B1511107
  · exact B1511111
  · exact B1511115
  · exact B1511119
  · exact B1511123
  · exact B1511127
  · exact B1511131
  · exact B1511135
  · exact B1511139
  · exact B1511143
  · exact B1511147
  · exact B1511151
  · exact B1511155
  · exact B1511159
  · exact B1511163
  · exact B1511167
  · exact B1511171
  · exact B1511175
  · exact B1511179
  · exact B1511183
  · exact B1511187
  · exact B1511191
  · exact B1511195
  · exact B1511199
  · exact B1511203
  · exact B1511207
  · exact B1511211
  · exact B1511215
  · exact B1511219
  · exact B1511223
  · exact B1511227
  · exact B1511231
  · exact B1511235
  · exact B1511239
  · exact B1511243
  · exact B1511247
  · exact B1511251
  · exact B1511255
  · exact B1511259
  · exact B1511263
  · exact B1511267
  · exact B1511271
  · exact B1511275
  · exact B1511279
  · exact B1511283
  · exact B1511287
  · exact B1511291
  · exact B1511295
  · exact B1511299
  · exact B1511303
  · exact B1511307
  · exact B1511311
  · exact B1511315
  · exact B1511319
  · exact B1511323
  · exact B1511327
  · exact B1511331
  · exact B1511335
  · exact B1511339
  · exact B1511343
  · exact B1511347
  · exact B1511351
  · exact B1511355
  · exact B1511359
  · exact B1511363
  · exact B1511367
  · exact B1511371
  · exact B1511375
  · exact B1511379
  · exact B1511383
  · exact B1511387
  · exact B1511391
  · exact B1511395
  · exact B1511399
  · exact B1511403
  · exact B1511407
  · exact B1511411
  · exact B1511415
  · exact B1511419
  · exact B1511423
  · exact B1511427
  · exact B1511431
  · exact B1511435
  · exact B1511439
  · exact B1511443
  · exact B1511447
  · exact B1511451
  · exact B1511455
  · exact B1511459
  · exact B1511463
  · exact B1511467
  · exact B1511471
  · exact B1511475
  · exact B1511479
  · exact B1511483
  · exact B1511487
  · exact B1511491
  · exact B1511495
  · exact B1511499
  · exact B1511503
  · exact B1511507
  · exact B1511511
  · exact B1511515
  · exact B1511519
  · exact B1511523
  · exact B1511527
  · exact B1511531
  · exact B1511535
  · exact B1511539
  · exact B1511543
  · exact B1511547
  · exact B1511551
  · exact B1511555
  · exact B1511559
  · exact B1511563
  · exact B1511567
  · exact B1511571
  · exact B1511575
  · exact B1511579
  · exact B1511583
  · exact B1511587
  · exact B1511591
  · exact B1511595
  · exact B1511599
  · exact B1511603
  · exact B1511607
  · exact B1511611
  · exact B1511615
  · exact B1511619
  · exact B1511623
  · exact B1511627
  · exact B1511631
  · exact B1511635
  · exact B1511639
  · exact B1511643
  · exact B1511647
  · exact B1511651
  · exact B1511655
  · exact B1511659
  · exact B1511663
  · exact B1511667
  · exact B1511671
  · exact B1511675
  · exact B1511679
  · exact B1511683
  · exact B1511687
  · exact B1511691
  · exact B1511695
  · exact B1511699
  · exact B1511703
  · exact B1511707
  · exact B1511711
  · exact B1511715
  · exact B1511719
  · exact B1511723
  · exact B1511727
  · exact B1511731
  · exact B1511735
  · exact B1511739
  · exact B1511743
  · exact B1511747
  · exact B1511751
  · exact B1511755
  · exact B1511759
  · exact B1511763
  · exact B1511767
  · exact B1511771
  · exact B1511775
  · exact B1511779
  · exact B1511783
  · exact B1511787
  · exact B1511791
  · exact B1511795
  · exact B1511799
  · exact B1511803
  · exact B1511807
  · exact B1511811
  · exact B1511815
  · exact B1511819
  · exact B1511823
  · exact B1511827
  · exact B1511831
  · exact B1511835
  · exact B1511839
  · exact B1511843
  · exact B1511847
  · exact B1511851
  · exact B1511855
  · exact B1511859
  · exact B1511863
  · exact B1511867
  · exact B1511871
  · exact B1511875
  · exact B1511879
  · exact B1511883
  · exact B1511887
  · exact B1511891
  · exact B1511895
  · exact B1511899
  · exact B1511903
  · exact B1511907
  · exact B1511911
  · exact B1511915
  · exact B1511919
  · exact B1511923
  · exact B1511927
  · exact B1511931
  · exact B1511935
  · exact B1511939
  · exact B1511943
  · exact B1511947
  · exact B1511951
  · exact B1511955
  · exact B1511959
  · exact B1511963
  · exact B1511967
  · exact B1511971
  · exact B1511975
  · exact B1511979
  · exact B1511983
  · exact B1511987
  · exact B1511991
  · exact B1511995
  · exact B1511999
  · exact B1512003
  · exact B1512007
  · exact B1512011
  · exact B1512015
  · exact B1512019
  · exact B1512023
  · exact B1512027
  · exact B1512031
  · exact B1512035
  · exact B1512039
  · exact B1512043
  · exact B1512047
  · exact B1512051
  · exact B1512055
  · exact B1512059
  · exact B1512063
  · exact B1512067
  · exact B1512071
  · exact B1512075
  · exact B1512079
  · exact B1512083
  · exact B1512087
  · exact B1512091
  · exact B1512095
  · exact B1512099
  · exact B1512103
  · exact B1512107
  · exact B1512111
  · exact B1512115
  · exact B1512119
  · exact B1512123
  · exact B1512127
  · exact B1512131
  · exact B1512135
  · exact B1512139
  · exact B1512143
  · exact B1512147
  · exact B1512151
  · exact B1512155
  · exact B1512159
  · exact B1512163
  · exact B1512167
  · exact B1512171
  · exact B1512175
  · exact B1512179
  · exact B1512183
  · exact B1512187
  · exact B1512191
  · exact B1512195
  · exact B1512199
  · exact B1512203
  · exact B1512207
  · exact B1512211
  · exact B1512215
  · exact B1512219
  · exact B1512223
  · exact B1512227
  · exact B1512231
  · exact B1512235
  · exact B1512239
  · exact B1512243
  · exact B1512247
  · exact B1512251
  · exact B1512255
  · exact B1512259
  · exact B1512263
  · exact B1512267
  · exact B1512271
  · exact B1512275
  · exact B1512279
  · exact B1512283
  · exact B1512287
  · exact B1512291
  · exact B1512295
  · exact B1512299
  · exact B1512303
  · exact B1512307
  · exact B1512311
  · exact B1512315
  · exact B1512319
  · exact B1512323
  · exact B1512327
  · exact B1512331
  · exact B1512335
  · exact B1512339
  · exact B1512343
  · exact B1512347
  · exact B1512351
  · exact B1512355
  · exact B1512359
  · exact B1512363
  · exact B1512367
  · exact B1512371
  · exact B1512375
  · exact B1512379
  · exact B1512383
  · exact B1512387
  · exact B1512391
  · exact B1512395
  · exact B1512399
  · exact B1512403
  · exact B1512407
  · exact B1512411
  · exact B1512415
  · exact B1512419
  · exact B1512423
  · exact B1512427
  · exact B1512431
  · exact B1512435
  · exact B1512439
  · exact B1512443
  · exact B1512447
  · exact B1512451
  · exact B1512455
  · exact B1512459
  · exact B1512463
  · exact B1512467
  · exact B1512471
  · exact B1512475
  · exact B1512479
  · exact B1512483
  · exact B1512487
  · exact B1512491
  · exact B1512495
  · exact B1512499
  · exact B1512503
  · exact B1512507
  · exact B1512511
  · exact B1512515
  · exact B1512519
  · exact B1512523
  · exact B1512527
  · exact B1512531
  · exact B1512535
  · exact B1512539
  · exact B1512543
  · exact B1512547
  · exact B1512551
  · exact B1512555
  · exact B1512559
  · exact B1512563
  · exact B1512567
  · exact B1512571
  · exact B1512575
  · exact B1512579
  · exact B1512583
  · exact B1512587
  · exact B1512591
  · exact B1512595
  · exact B1512599
  · exact B1512603
  · exact B1512607
  · exact B1512611
  · exact B1512615
  · exact B1512619
  · exact B1512623
  · exact B1512627
  · exact B1512631
  · exact B1512635
  · exact B1512639
  · exact B1512643
  · exact B1512647
  · exact B1512651
  · exact B1512655
  · exact B1512659
  · exact B1512663
  · exact B1512667
  · exact B1512671
  · exact B1512675
  · exact B1512679
  · exact B1512683
  · exact B1512687
  · exact B1512691
  · exact B1512695
  · exact B1512699
  · exact B1512703
  · exact B1512707
  · exact B1512711
  · exact B1512715
  · exact B1512719
  · exact B1512723
  · exact B1512727
  · exact B1512731
  · exact B1512735
  · exact B1512739
  · exact B1512743
  · exact B1512747
  · exact B1512751
  · exact B1512755
  · exact B1512759
  · exact B1512763
  · exact B1512767
  · exact B1512771
  · exact B1512775
  · exact B1512779
  · exact B1512783
  · exact B1512787
  · exact B1512791
  · exact B1512795
  · exact B1512799
  · exact B1512803
  · exact B1512807
  · exact B1512811
  · exact B1512815
  · exact B1512819
  · exact B1512823
  · exact B1512827
  · exact B1512831
  · exact B1512835
  · exact B1512839
  · exact B1512843
  · exact B1512847
  · exact B1512851
  · exact B1512855
  · exact B1512859
  · exact B1512863
  · exact B1512867
  · exact B1512871
  · exact B1512875
  · exact B1512879
  · exact B1512883
  · exact B1512887
  · exact B1512891
  · exact B1512895
  · exact B1512899
  · exact B1512903
  · exact B1512907
  · exact B1512911
  · exact B1512915
  · exact B1512919
  · exact B1512923
  · exact B1512927
  · exact B1512931
  · exact B1512935
  · exact B1512939
  · exact B1512943
  · exact B1512947
  · exact B1512951

theorem solution (m : ℕ) (hlo : 1510952 ≤ m) (hhi : m ≤ 1512952) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 377738 ≤ j := by omega
    have hj2 : j ≤ 378237 := by omega
    have hb : Blo 1510952 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
