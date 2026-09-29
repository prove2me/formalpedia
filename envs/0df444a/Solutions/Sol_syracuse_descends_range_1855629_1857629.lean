-- Prove2me | solution 1 for syracuse_descends_range_1855629_1857629
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:08:40.555233+00:00
-- url     : https://prove2.me/submissions/ebea7f27-cfd0-466e-99c1-04cc4c46430a

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


theorem B4177925 : Blo 1855629 4177925 := bbase (se 4 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 4177925 = 783361) (by norm_num)
theorem B2613269 : Blo 1855629 2613269 := bbase (se 6 (by rfl) ⟨61248, by rfl⟩ : syracuseStep 2613269 = 122497) (by norm_num)
theorem B2785301 : Blo 1855629 2785301 := bbase (se 6 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 2785301 = 130561) (by norm_num)
theorem B2088985 : Blo 1855629 2088985 := bbase (se 2 (by rfl) ⟨783369, by rfl⟩ : syracuseStep 2088985 = 1566739) (by norm_num)
theorem B2785325 : Blo 1855629 2785325 := bbase (se 3 (by rfl) ⟨522248, by rfl⟩ : syracuseStep 2785325 = 1044497) (by norm_num)
theorem B5947445 : Blo 1855629 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B2089021 : Blo 1855629 2089021 := bbase (se 3 (by rfl) ⟨391691, by rfl⟩ : syracuseStep 2089021 = 783383) (by norm_num)
theorem B3964997 : Blo 1855629 3964997 := bbase (se 4 (by rfl) ⟨371718, by rfl⟩ : syracuseStep 3964997 = 743437) (by norm_num)
theorem B2785349 : Blo 1855629 2785349 := bbase (se 4 (by rfl) ⟨261126, by rfl⟩ : syracuseStep 2785349 = 522253) (by norm_num)
theorem B4177997 : Blo 1855629 4177997 := bbase (se 3 (by rfl) ⟨783374, by rfl⟩ : syracuseStep 4177997 = 1566749) (by norm_num)
theorem B4243549 : Blo 1855629 4243549 := bbase (se 3 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 4243549 = 1591331) (by norm_num)
theorem B2785373 : Blo 1855629 2785373 := bbase (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) (by norm_num)
theorem B2089057 : Blo 1855629 2089057 := bbase (se 2 (by rfl) ⟨783396, by rfl⟩ : syracuseStep 2089057 = 1566793) (by norm_num)
theorem B2785397 : Blo 1855629 2785397 := bbase (se 5 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 2785397 = 261131) (by norm_num)
theorem B1982593 : Blo 1855629 1982593 := bbase (se 2 (by rfl) ⟨743472, by rfl⟩ : syracuseStep 1982593 = 1486945) (by norm_num)
theorem B2089093 : Blo 1855629 2089093 := bbase (se 4 (by rfl) ⟨195852, by rfl⟩ : syracuseStep 2089093 = 391705) (by norm_num)
theorem B2785421 : Blo 1855629 2785421 := bbase (se 3 (by rfl) ⟨522266, by rfl⟩ : syracuseStep 2785421 = 1044533) (by norm_num)
theorem B4178069 : Blo 1855629 4178069 := bbase (se 6 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 4178069 = 195847) (by norm_num)
theorem B2785445 : Blo 1855629 2785445 := bbase (se 4 (by rfl) ⟨261135, by rfl⟩ : syracuseStep 2785445 = 522271) (by norm_num)
theorem B2089129 : Blo 1855629 2089129 := bbase (se 2 (by rfl) ⟨783423, by rfl⟩ : syracuseStep 2089129 = 1566847) (by norm_num)
theorem B2785469 : Blo 1855629 2785469 := bbase (se 3 (by rfl) ⟨522275, by rfl⟩ : syracuseStep 2785469 = 1044551) (by norm_num)
theorem B6267077 : Blo 1855629 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B2089165 : Blo 1855629 2089165 := bbase (se 3 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 2089165 = 783437) (by norm_num)
theorem B6029525 : Blo 1855629 6029525 := bbase (se 7 (by rfl) ⟨70658, by rfl⟩ : syracuseStep 6029525 = 141317) (by norm_num)
theorem B2785493 : Blo 1855629 2785493 := bbase (se 7 (by rfl) ⟨32642, by rfl⟩ : syracuseStep 2785493 = 65285) (by norm_num)
theorem B4178141 : Blo 1855629 4178141 := bbase (se 3 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 4178141 = 1566803) (by norm_num)
theorem B2785517 : Blo 1855629 2785517 := bbase (se 3 (by rfl) ⟨522284, by rfl⟩ : syracuseStep 2785517 = 1044569) (by norm_num)
theorem B2089201 : Blo 1855629 2089201 := bbase (se 2 (by rfl) ⟨783450, by rfl⟩ : syracuseStep 2089201 = 1566901) (by norm_num)
theorem B3391741 : Blo 1855629 3391741 := bbase (se 3 (by rfl) ⟨635951, by rfl⟩ : syracuseStep 3391741 = 1271903) (by norm_num)
theorem B9396485 : Blo 1855629 9396485 := bbase (se 4 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 9396485 = 1761841) (by norm_num)
theorem B2785541 : Blo 1855629 2785541 := bbase (se 4 (by rfl) ⟨261144, by rfl⟩ : syracuseStep 2785541 = 522289) (by norm_num)
theorem B2089237 : Blo 1855629 2089237 := bbase (se 6 (by rfl) ⟨48966, by rfl⟩ : syracuseStep 2089237 = 97933) (by norm_num)
theorem B2785565 : Blo 1855629 2785565 := bbase (se 3 (by rfl) ⟨522293, by rfl⟩ : syracuseStep 2785565 = 1044587) (by norm_num)
theorem B4178213 : Blo 1855629 4178213 := bbase (se 4 (by rfl) ⟨391707, by rfl⟩ : syracuseStep 4178213 = 783415) (by norm_num)
theorem B2785589 : Blo 1855629 2785589 := bbase (se 5 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 2785589 = 261149) (by norm_num)
theorem B2089273 : Blo 1855629 2089273 := bbase (se 2 (by rfl) ⟨783477, by rfl⟩ : syracuseStep 2089273 = 1566955) (by norm_num)
theorem B2785613 : Blo 1855629 2785613 := bbase (se 3 (by rfl) ⟨522302, by rfl⟩ : syracuseStep 2785613 = 1044605) (by norm_num)
theorem B2089309 : Blo 1855629 2089309 := bbase (se 3 (by rfl) ⟨391745, by rfl⟩ : syracuseStep 2089309 = 783491) (by norm_num)
theorem B2785637 : Blo 1855629 2785637 := bbase (se 4 (by rfl) ⟨261153, by rfl⟩ : syracuseStep 2785637 = 522307) (by norm_num)
theorem B4178285 : Blo 1855629 4178285 := bbase (se 3 (by rfl) ⟨783428, by rfl⟩ : syracuseStep 4178285 = 1566857) (by norm_num)
theorem B2785661 : Blo 1855629 2785661 := bbase (se 3 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 2785661 = 1044623) (by norm_num)
theorem B2089345 : Blo 1855629 2089345 := bbase (se 2 (by rfl) ⟨783504, by rfl⟩ : syracuseStep 2089345 = 1567009) (by norm_num)
theorem B2785685 : Blo 1855629 2785685 := bbase (se 6 (by rfl) ⟨65289, by rfl⟩ : syracuseStep 2785685 = 130579) (by norm_num)
theorem B4522397 : Blo 1855629 4522397 := bbase (se 3 (by rfl) ⟨847949, by rfl⟩ : syracuseStep 4522397 = 1695899) (by norm_num)
theorem B2089381 : Blo 1855629 2089381 := bbase (se 4 (by rfl) ⟨195879, by rfl⟩ : syracuseStep 2089381 = 391759) (by norm_num)
theorem B2785709 : Blo 1855629 2785709 := bbase (se 3 (by rfl) ⟨522320, by rfl⟩ : syracuseStep 2785709 = 1044641) (by norm_num)
theorem B3965365 : Blo 1855629 3965365 := bbase (se 5 (by rfl) ⟨185876, by rfl⟩ : syracuseStep 3965365 = 371753) (by norm_num)
theorem B2974133 : Blo 1855629 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B4178357 : Blo 1855629 4178357 := bbase (se 5 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 4178357 = 391721) (by norm_num)
theorem B2785733 : Blo 1855629 2785733 := bbase (se 4 (by rfl) ⟨261162, by rfl⟩ : syracuseStep 2785733 = 522325) (by norm_num)
theorem B2089417 : Blo 1855629 2089417 := bbase (se 2 (by rfl) ⟨783531, by rfl⟩ : syracuseStep 2089417 = 1567063) (by norm_num)
theorem B2785757 : Blo 1855629 2785757 := bbase (se 3 (by rfl) ⟨522329, by rfl⟩ : syracuseStep 2785757 = 1044659) (by norm_num)
theorem B2089453 : Blo 1855629 2089453 := bbase (se 3 (by rfl) ⟨391772, by rfl⟩ : syracuseStep 2089453 = 783545) (by norm_num)
theorem B2785781 : Blo 1855629 2785781 := bbase (se 5 (by rfl) ⟨130583, by rfl⟩ : syracuseStep 2785781 = 261167) (by norm_num)
theorem B4178429 : Blo 1855629 4178429 := bbase (se 3 (by rfl) ⟨783455, by rfl⟩ : syracuseStep 4178429 = 1566911) (by norm_num)
theorem B2146817 : Blo 1855629 2146817 := bbase (se 2 (by rfl) ⟨805056, by rfl⟩ : syracuseStep 2146817 = 1610113) (by norm_num)
theorem B2785805 : Blo 1855629 2785805 := bbase (se 3 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 2785805 = 1044677) (by norm_num)
theorem B2089489 : Blo 1855629 2089489 := bbase (se 2 (by rfl) ⟨783558, by rfl⟩ : syracuseStep 2089489 = 1567117) (by norm_num)
theorem B2785829 : Blo 1855629 2785829 := bbase (se 4 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 2785829 = 522343) (by norm_num)
theorem B2974261 : Blo 1855629 2974261 := bbase (se 5 (by rfl) ⟨139418, by rfl⟩ : syracuseStep 2974261 = 278837) (by norm_num)
theorem B2089525 : Blo 1855629 2089525 := bbase (se 5 (by rfl) ⟨97946, by rfl⟩ : syracuseStep 2089525 = 195893) (by norm_num)
theorem B1983037 : Blo 1855629 1983037 := bbase (se 3 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 1983037 = 743639) (by norm_num)
theorem B2785853 : Blo 1855629 2785853 := bbase (se 3 (by rfl) ⟨522347, by rfl⟩ : syracuseStep 2785853 = 1044695) (by norm_num)
theorem B4178501 : Blo 1855629 4178501 := bbase (se 4 (by rfl) ⟨391734, by rfl⟩ : syracuseStep 4178501 = 783469) (by norm_num)
theorem B2785877 : Blo 1855629 2785877 := bbase (se 8 (by rfl) ⟨16323, by rfl⟩ : syracuseStep 2785877 = 32647) (by norm_num)
theorem B2089561 : Blo 1855629 2089561 := bbase (se 2 (by rfl) ⟨783585, by rfl⟩ : syracuseStep 2089561 = 1567171) (by norm_num)
theorem B5284453 : Blo 1855629 5284453 := bbase (se 4 (by rfl) ⟨495417, by rfl⟩ : syracuseStep 5284453 = 990835) (by norm_num)
theorem B2785901 : Blo 1855629 2785901 := bbase (se 3 (by rfl) ⟨522356, by rfl⟩ : syracuseStep 2785901 = 1044713) (by norm_num)
theorem B3523189 : Blo 1855629 3523189 := bbase (se 5 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 3523189 = 330299) (by norm_num)
theorem B6267509 : Blo 1855629 6267509 := bbase (se 5 (by rfl) ⟨293789, by rfl⟩ : syracuseStep 6267509 = 587579) (by norm_num)
theorem B2089597 : Blo 1855629 2089597 := bbase (se 3 (by rfl) ⟨391799, by rfl⟩ : syracuseStep 2089597 = 783599) (by norm_num)
theorem B2785925 : Blo 1855629 2785925 := bbase (se 4 (by rfl) ⟨261180, by rfl⟩ : syracuseStep 2785925 = 522361) (by norm_num)
theorem B4178573 : Blo 1855629 4178573 := bbase (se 3 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 4178573 = 1566965) (by norm_num)
theorem B2785949 : Blo 1855629 2785949 := bbase (se 3 (by rfl) ⟨522365, by rfl⟩ : syracuseStep 2785949 = 1044731) (by norm_num)
theorem B2089633 : Blo 1855629 2089633 := bbase (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) (by norm_num)
theorem B8921765 : Blo 1855629 8921765 := bbase (se 4 (by rfl) ⟨836415, by rfl⟩ : syracuseStep 8921765 = 1672831) (by norm_num)
theorem B2785973 : Blo 1855629 2785973 := bbase (se 5 (by rfl) ⟨130592, by rfl⟩ : syracuseStep 2785973 = 261185) (by norm_num)
theorem B1983161 : Blo 1855629 1983161 := bbase (se 2 (by rfl) ⟨743685, by rfl⟩ : syracuseStep 1983161 = 1487371) (by norm_num)
theorem B2089669 : Blo 1855629 2089669 := bbase (se 4 (by rfl) ⟨195906, by rfl⟩ : syracuseStep 2089669 = 391813) (by norm_num)
theorem B2785997 : Blo 1855629 2785997 := bbase (se 3 (by rfl) ⟨522374, by rfl⟩ : syracuseStep 2785997 = 1044749) (by norm_num)
theorem B4178645 : Blo 1855629 4178645 := bbase (se 7 (by rfl) ⟨48968, by rfl⟩ : syracuseStep 4178645 = 97937) (by norm_num)
theorem B2786021 : Blo 1855629 2786021 := bbase (se 4 (by rfl) ⟨261189, by rfl⟩ : syracuseStep 2786021 = 522379) (by norm_num)
theorem B2089705 : Blo 1855629 2089705 := bbase (se 2 (by rfl) ⟨783639, by rfl⟩ : syracuseStep 2089705 = 1567279) (by norm_num)
theorem B3621613 : Blo 1855629 3621613 := bbase (se 3 (by rfl) ⟨679052, by rfl⟩ : syracuseStep 3621613 = 1358105) (by norm_num)
theorem B2786045 : Blo 1855629 2786045 := bbase (se 3 (by rfl) ⟨522383, by rfl⟩ : syracuseStep 2786045 = 1044767) (by norm_num)
theorem B3523333 : Blo 1855629 3523333 := bbase (se 4 (by rfl) ⟨330312, by rfl⟩ : syracuseStep 3523333 = 660625) (by norm_num)
theorem B2089741 : Blo 1855629 2089741 := bbase (se 3 (by rfl) ⟨391826, by rfl⟩ : syracuseStep 2089741 = 783653) (by norm_num)
theorem B2786069 : Blo 1855629 2786069 := bbase (se 6 (by rfl) ⟨65298, by rfl⟩ : syracuseStep 2786069 = 130597) (by norm_num)
theorem B4178717 : Blo 1855629 4178717 := bbase (se 3 (by rfl) ⟨783509, by rfl⟩ : syracuseStep 4178717 = 1567019) (by norm_num)
theorem B2786093 : Blo 1855629 2786093 := bbase (se 3 (by rfl) ⟨522392, by rfl⟩ : syracuseStep 2786093 = 1044785) (by norm_num)
theorem B2089777 : Blo 1855629 2089777 := bbase (se 2 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 2089777 = 1567333) (by norm_num)
theorem B3392309 : Blo 1855629 3392309 := bbase (se 5 (by rfl) ⟨159014, by rfl⟩ : syracuseStep 3392309 = 318029) (by norm_num)
theorem B2786117 : Blo 1855629 2786117 := bbase (se 4 (by rfl) ⟨261198, by rfl⟩ : syracuseStep 2786117 = 522397) (by norm_num)
theorem B2089813 : Blo 1855629 2089813 := bbase (se 9 (by rfl) ⟨6122, by rfl⟩ : syracuseStep 2089813 = 12245) (by norm_num)
theorem B2786141 : Blo 1855629 2786141 := bbase (se 3 (by rfl) ⟨522401, by rfl⟩ : syracuseStep 2786141 = 1044803) (by norm_num)
theorem B4178789 : Blo 1855629 4178789 := bbase (se 4 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 4178789 = 783523) (by norm_num)
theorem B2786165 : Blo 1855629 2786165 := bbase (se 5 (by rfl) ⟨130601, by rfl⟩ : syracuseStep 2786165 = 261203) (by norm_num)
theorem B5358469 : Blo 1855629 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B2786189 : Blo 1855629 2786189 := bbase (se 3 (by rfl) ⟨522410, by rfl⟩ : syracuseStep 2786189 = 1044821) (by norm_num)
theorem B3523493 : Blo 1855629 3523493 := bbase (se 4 (by rfl) ⟨330327, by rfl⟩ : syracuseStep 3523493 = 660655) (by norm_num)
theorem B2786213 : Blo 1855629 2786213 := bbase (se 4 (by rfl) ⟨261207, by rfl⟩ : syracuseStep 2786213 = 522415) (by norm_num)
theorem B3572653 : Blo 1855629 3572653 := bbase (se 3 (by rfl) ⟨669872, by rfl⟩ : syracuseStep 3572653 = 1339745) (by norm_num)
theorem B4178861 : Blo 1855629 4178861 := bbase (se 3 (by rfl) ⟨783536, by rfl⟩ : syracuseStep 4178861 = 1567073) (by norm_num)
theorem B15057845 : Blo 1855629 15057845 := bbase (se 5 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 15057845 = 1411673) (by norm_num)
theorem B2974645 : Blo 1855629 2974645 := bbase (se 5 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 2974645 = 278873) (by norm_num)
theorem B1983413 : Blo 1855629 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B2786237 : Blo 1855629 2786237 := bbase (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) (by norm_num)
theorem B2786261 : Blo 1855629 2786261 := bbase (se 7 (by rfl) ⟨32651, by rfl⟩ : syracuseStep 2786261 = 65303) (by norm_num)
theorem B48915413 : Blo 1855629 48915413 := bbase (se 7 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 48915413 = 1146455) (by norm_num)
theorem B2786285 : Blo 1855629 2786285 := bbase (se 3 (by rfl) ⟨522428, by rfl⟩ : syracuseStep 2786285 = 1044857) (by norm_num)
theorem B4178933 : Blo 1855629 4178933 := bbase (se 5 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 4178933 = 391775) (by norm_num)
theorem B7046149 : Blo 1855629 7046149 := bbase (se 4 (by rfl) ⟨660576, by rfl⟩ : syracuseStep 7046149 = 1321153) (by norm_num)
theorem B2786309 : Blo 1855629 2786309 := bbase (se 4 (by rfl) ⟨261216, by rfl⟩ : syracuseStep 2786309 = 522433) (by norm_num)
theorem B8471573 : Blo 1855629 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B2786333 : Blo 1855629 2786333 := bbase (se 3 (by rfl) ⟨522437, by rfl⟩ : syracuseStep 2786333 = 1044875) (by norm_num)
theorem B6267941 : Blo 1855629 6267941 := bbase (se 4 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 6267941 = 1175239) (by norm_num)
theorem B3523637 : Blo 1855629 3523637 := bbase (se 5 (by rfl) ⟨165170, by rfl⟩ : syracuseStep 3523637 = 330341) (by norm_num)
theorem B2786357 : Blo 1855629 2786357 := bbase (se 5 (by rfl) ⟨130610, by rfl⟩ : syracuseStep 2786357 = 261221) (by norm_num)
theorem B4179005 : Blo 1855629 4179005 := bbase (se 3 (by rfl) ⟨783563, by rfl⟩ : syracuseStep 4179005 = 1567127) (by norm_num)
theorem B2786381 : Blo 1855629 2786381 := bbase (se 3 (by rfl) ⟨522446, by rfl⟩ : syracuseStep 2786381 = 1044893) (by norm_num)
theorem B7529557 : Blo 1855629 7529557 := bbase (se 8 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 7529557 = 88237) (by norm_num)
theorem B2786405 : Blo 1855629 2786405 := bbase (se 4 (by rfl) ⟨261225, by rfl⟩ : syracuseStep 2786405 = 522451) (by norm_num)
theorem B2786429 : Blo 1855629 2786429 := bbase (se 3 (by rfl) ⟨522455, by rfl⟩ : syracuseStep 2786429 = 1044911) (by norm_num)
theorem B4179077 : Blo 1855629 4179077 := bbase (se 4 (by rfl) ⟨391788, by rfl⟩ : syracuseStep 4179077 = 783577) (by norm_num)
theorem B2974901 : Blo 1855629 2974901 := bbase (se 5 (by rfl) ⟨139448, by rfl⟩ : syracuseStep 2974901 = 278897) (by norm_num)
theorem B2507965 : Blo 1855629 2507965 := bbase (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) (by norm_num)
theorem B4179149 : Blo 1855629 4179149 := bbase (se 3 (by rfl) ⟨783590, by rfl⟩ : syracuseStep 4179149 = 1567181) (by norm_num)
theorem B10175701 : Blo 1855629 10175701 := bbase (se 7 (by rfl) ⟨119246, by rfl⟩ : syracuseStep 10175701 = 238493) (by norm_num)
theorem B7931141 : Blo 1855629 7931141 := bbase (se 4 (by rfl) ⟨743544, by rfl⟩ : syracuseStep 7931141 = 1487089) (by norm_num)
theorem B4179221 : Blo 1855629 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B7046453 : Blo 1855629 7046453 := bbase (se 5 (by rfl) ⟨330302, by rfl⟩ : syracuseStep 7046453 = 660605) (by norm_num)
theorem B8922437 : Blo 1855629 8922437 := bbase (se 4 (by rfl) ⟨836478, by rfl⟩ : syracuseStep 8922437 = 1672957) (by norm_num)
theorem B3523925 : Blo 1855629 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B4179293 : Blo 1855629 4179293 := bbase (se 3 (by rfl) ⟨783617, by rfl⟩ : syracuseStep 4179293 = 1567235) (by norm_num)
theorem B23782805 : Blo 1855629 23782805 := bbase (se 6 (by rfl) ⟨557409, by rfl⟩ : syracuseStep 23782805 = 1114819) (by norm_num)
theorem B4179365 : Blo 1855629 4179365 := bbase (se 4 (by rfl) ⟨391815, by rfl⟩ : syracuseStep 4179365 = 783631) (by norm_num)
theorem B6268373 : Blo 1855629 6268373 := bbase (se 7 (by rfl) ⟨73457, by rfl⟩ : syracuseStep 6268373 = 146915) (by norm_num)
theorem B3524077 : Blo 1855629 3524077 := bbase (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) (by norm_num)
theorem B4179437 : Blo 1855629 4179437 := bbase (se 3 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 4179437 = 1567289) (by norm_num)
theorem B12699125 : Blo 1855629 12699125 := bbase (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) (by norm_num)
theorem B2229773 : Blo 1855629 2229773 := bbase (se 3 (by rfl) ⟨418082, by rfl⟩ : syracuseStep 2229773 = 836165) (by norm_num)
theorem B9397781 : Blo 1855629 9397781 := bbase (se 6 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 9397781 = 440521) (by norm_num)
theorem B7931429 : Blo 1855629 7931429 := bbase (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) (by norm_num)
theorem B4179509 : Blo 1855629 4179509 := bbase (se 5 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 4179509 = 391829) (by norm_num)
theorem B3343997 : Blo 1855629 3343997 := bbase (se 3 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 3343997 = 1253999) (by norm_num)
theorem B4179581 : Blo 1855629 4179581 := bbase (se 3 (by rfl) ⟨783671, by rfl⟩ : syracuseStep 4179581 = 1567343) (by norm_num)
theorem B2008733 : Blo 1855629 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B4179653 : Blo 1855629 4179653 := bbase (se 4 (by rfl) ⟨391842, by rfl⟩ : syracuseStep 4179653 = 783685) (by norm_num)
theorem B5646037 : Blo 1855629 5646037 := bbase (se 7 (by rfl) ⟨66164, by rfl⟩ : syracuseStep 5646037 = 132329) (by norm_num)
theorem B3524381 : Blo 1855629 3524381 := bbase (se 3 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 3524381 = 1321643) (by norm_num)
theorem B6268805 : Blo 1855629 6268805 := bbase (se 4 (by rfl) ⟨587700, by rfl⟩ : syracuseStep 6268805 = 1175401) (by norm_num)
theorem B3966869 : Blo 1855629 3966869 := bbase (se 6 (by rfl) ⟨92973, by rfl⟩ : syracuseStep 3966869 = 185947) (by norm_num)
theorem B4524013 : Blo 1855629 4524013 := bbase (se 3 (by rfl) ⟨848252, by rfl⟩ : syracuseStep 4524013 = 1696505) (by norm_num)
theorem B3967013 : Blo 1855629 3967013 := bbase (se 4 (by rfl) ⟨371907, by rfl⟩ : syracuseStep 3967013 = 743815) (by norm_num)
theorem B3131453 : Blo 1855629 3131453 := bbase (se 3 (by rfl) ⟨587147, by rfl⟩ : syracuseStep 3131453 = 1174295) (by norm_num)
theorem B3131581 : Blo 1855629 3131581 := bbase (se 3 (by rfl) ⟨587171, by rfl⟩ : syracuseStep 3131581 = 1174343) (by norm_num)
theorem B2230465 : Blo 1855629 2230465 := bbase (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) (by norm_num)
theorem B4458701 : Blo 1855629 4458701 := bbase (se 3 (by rfl) ⟨836006, by rfl⟩ : syracuseStep 4458701 = 1672013) (by norm_num)
theorem B3131669 : Blo 1855629 3131669 := bbase (se 6 (by rfl) ⟨73398, by rfl⟩ : syracuseStep 3131669 = 146797) (by norm_num)
theorem B7932181 : Blo 1855629 7932181 := bbase (se 6 (by rfl) ⟨185910, by rfl⟩ : syracuseStep 7932181 = 371821) (by norm_num)
theorem B2230561 : Blo 1855629 2230561 := bbase (se 2 (by rfl) ⟨836460, by rfl⟩ : syracuseStep 2230561 = 1672921) (by norm_num)
theorem B6269237 : Blo 1855629 6269237 := bbase (se 5 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 6269237 = 587741) (by norm_num)
theorem B2509165 : Blo 1855629 2509165 := bbase (se 3 (by rfl) ⟨470468, by rfl⟩ : syracuseStep 2509165 = 940937) (by norm_num)
theorem B3967373 : Blo 1855629 3967373 := bbase (se 3 (by rfl) ⟨743882, by rfl⟩ : syracuseStep 3967373 = 1487765) (by norm_num)
theorem B3131797 : Blo 1855629 3131797 := bbase (se 6 (by rfl) ⟨73401, by rfl⟩ : syracuseStep 3131797 = 146803) (by norm_num)
theorem B4762037 : Blo 1855629 4762037 := bbase (se 5 (by rfl) ⟨223220, by rfl⟩ : syracuseStep 4762037 = 446441) (by norm_num)
theorem B3344861 : Blo 1855629 3344861 := bbase (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) (by norm_num)
theorem B4458989 : Blo 1855629 4458989 := bbase (se 3 (by rfl) ⟨836060, by rfl⟩ : syracuseStep 4458989 = 1672121) (by norm_num)
theorem B3131885 : Blo 1855629 3131885 := bbase (se 3 (by rfl) ⟨587228, by rfl⟩ : syracuseStep 3131885 = 1174457) (by norm_num)
theorem B3574253 : Blo 1855629 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B3525133 : Blo 1855629 3525133 := bbase (se 3 (by rfl) ⟨660962, by rfl⟩ : syracuseStep 3525133 = 1321925) (by norm_num)
theorem B28576277 : Blo 1855629 28576277 := bbase (se 6 (by rfl) ⟨669756, by rfl⟩ : syracuseStep 28576277 = 1339513) (by norm_num)
theorem B3132013 : Blo 1855629 3132013 := bbase (se 3 (by rfl) ⟨587252, by rfl⟩ : syracuseStep 3132013 = 1174505) (by norm_num)
theorem B3525277 : Blo 1855629 3525277 := bbase (se 3 (by rfl) ⟨660989, by rfl⟩ : syracuseStep 3525277 = 1321979) (by norm_num)
theorem B2230945 : Blo 1855629 2230945 := bbase (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) (by norm_num)
theorem B3345085 : Blo 1855629 3345085 := bbase (se 3 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 3345085 = 1254407) (by norm_num)
theorem B3132101 : Blo 1855629 3132101 := bbase (se 4 (by rfl) ⟨293634, by rfl⟩ : syracuseStep 3132101 = 587269) (by norm_num)
theorem B9399077 : Blo 1855629 9399077 := bbase (se 4 (by rfl) ⟨881163, by rfl⟩ : syracuseStep 9399077 = 1762327) (by norm_num)
theorem B3525437 : Blo 1855629 3525437 := bbase (se 3 (by rfl) ⟨661019, by rfl⟩ : syracuseStep 3525437 = 1322039) (by norm_num)
theorem B3132229 : Blo 1855629 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B15854453 : Blo 1855629 15854453 := bbase (se 5 (by rfl) ⟨743177, by rfl⟩ : syracuseStep 15854453 = 1486355) (by norm_num)
theorem B3132317 : Blo 1855629 3132317 := bbase (se 3 (by rfl) ⟨587309, by rfl⟩ : syracuseStep 3132317 = 1174619) (by norm_num)
theorem B3525581 : Blo 1855629 3525581 := bbase (se 3 (by rfl) ⟨661046, by rfl⟩ : syracuseStep 3525581 = 1322093) (by norm_num)
theorem B7932917 : Blo 1855629 7932917 := bbase (se 5 (by rfl) ⟨371855, by rfl⟩ : syracuseStep 7932917 = 743711) (by norm_num)
theorem B3132445 : Blo 1855629 3132445 := bbase (se 3 (by rfl) ⟨587333, by rfl⟩ : syracuseStep 3132445 = 1174667) (by norm_num)
theorem B4697149 : Blo 1855629 4697149 := bbase (se 3 (by rfl) ⟨880715, by rfl⟩ : syracuseStep 4697149 = 1761431) (by norm_num)
theorem B3132533 : Blo 1855629 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B4697261 : Blo 1855629 4697261 := bbase (se 3 (by rfl) ⟨880736, by rfl⟩ : syracuseStep 4697261 = 1761473) (by norm_num)
theorem B5016773 : Blo 1855629 5016773 := bbase (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) (by norm_num)
theorem B10579157 : Blo 1855629 10579157 := bbase (se 7 (by rfl) ⟨123974, by rfl⟩ : syracuseStep 10579157 = 247949) (by norm_num)
theorem B3525869 : Blo 1855629 3525869 := bbase (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) (by norm_num)
theorem B3132661 : Blo 1855629 3132661 := bbase (se 5 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 3132661 = 293687) (by norm_num)
theorem B3132749 : Blo 1855629 3132749 := bbase (se 3 (by rfl) ⟨587390, by rfl⟩ : syracuseStep 3132749 = 1174781) (by norm_num)
theorem B10571093 : Blo 1855629 10571093 := bbase (se 11 (by rfl) ⟨7742, by rfl⟩ : syracuseStep 10571093 = 15485) (by norm_num)
theorem B4697453 : Blo 1855629 4697453 := bbase (se 3 (by rfl) ⟨880772, by rfl⟩ : syracuseStep 4697453 = 1761545) (by norm_num)
theorem B7048565 : Blo 1855629 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B5287301 : Blo 1855629 5287301 := bbase (se 4 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 5287301 = 991369) (by norm_num)
theorem B3526021 : Blo 1855629 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B6688165 : Blo 1855629 6688165 := bbase (se 4 (by rfl) ⟨627015, by rfl⟩ : syracuseStep 6688165 = 1254031) (by norm_num)
theorem B3722669 : Blo 1855629 3722669 := bbase (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) (by norm_num)
theorem B3132877 : Blo 1855629 3132877 := bbase (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) (by norm_num)
theorem B7523861 : Blo 1855629 7523861 := bbase (se 6 (by rfl) ⟨176340, by rfl⟩ : syracuseStep 7523861 = 352681) (by norm_num)
theorem B3132965 : Blo 1855629 3132965 := bbase (se 4 (by rfl) ⟨293715, by rfl⟩ : syracuseStep 3132965 = 587431) (by norm_num)
theorem B6688325 : Blo 1855629 6688325 := bbase (se 4 (by rfl) ⟨627030, by rfl⟩ : syracuseStep 6688325 = 1254061) (by norm_num)
theorem B5017205 : Blo 1855629 5017205 := bbase (se 5 (by rfl) ⟨235181, by rfl⟩ : syracuseStep 5017205 = 470363) (by norm_num)
theorem B7048853 : Blo 1855629 7048853 := bbase (se 6 (by rfl) ⟨165207, by rfl⟩ : syracuseStep 7048853 = 330415) (by norm_num)
theorem B3133093 : Blo 1855629 3133093 := bbase (se 4 (by rfl) ⟨293727, by rfl⟩ : syracuseStep 3133093 = 587455) (by norm_num)
theorem B3526325 : Blo 1855629 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B4697797 : Blo 1855629 4697797 := bbase (se 4 (by rfl) ⟨440418, by rfl⟩ : syracuseStep 4697797 = 880837) (by norm_num)
theorem B14102261 : Blo 1855629 14102261 := bbase (se 5 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 14102261 = 1322087) (by norm_num)
theorem B3133181 : Blo 1855629 3133181 := bbase (se 3 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 3133181 = 1174943) (by norm_num)
theorem B4697909 : Blo 1855629 4697909 := bbase (se 5 (by rfl) ⟨220214, by rfl⟩ : syracuseStep 4697909 = 440429) (by norm_num)
theorem B3133309 : Blo 1855629 3133309 := bbase (se 3 (by rfl) ⟨587495, by rfl⟩ : syracuseStep 3133309 = 1174991) (by norm_num)
theorem B6352805 : Blo 1855629 6352805 := bbase (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) (by norm_num)
theorem B8466373 : Blo 1855629 8466373 := bbase (se 4 (by rfl) ⟨793722, by rfl⟩ : syracuseStep 8466373 = 1587445) (by norm_num)
theorem B3133397 : Blo 1855629 3133397 := bbase (se 7 (by rfl) ⟨36719, by rfl⟩ : syracuseStep 3133397 = 73439) (by norm_num)
theorem B6262757 : Blo 1855629 6262757 := bbase (se 4 (by rfl) ⟨587133, by rfl⟩ : syracuseStep 6262757 = 1174267) (by norm_num)
theorem B4698101 : Blo 1855629 4698101 := bbase (se 5 (by rfl) ⟨220223, by rfl⟩ : syracuseStep 4698101 = 440447) (by norm_num)
theorem B9400373 : Blo 1855629 9400373 := bbase (se 5 (by rfl) ⟨440642, by rfl⟩ : syracuseStep 9400373 = 881285) (by norm_num)
theorem B2822221 : Blo 1855629 2822221 := bbase (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) (by norm_num)
theorem B21139541 : Blo 1855629 21139541 := bbase (se 8 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 21139541 = 247729) (by norm_num)
theorem B10719317 : Blo 1855629 10719317 := bbase (se 8 (by rfl) ⟨62808, by rfl⟩ : syracuseStep 10719317 = 125617) (by norm_num)
theorem B3133525 : Blo 1855629 3133525 := bbase (se 8 (by rfl) ⟨18360, by rfl⟩ : syracuseStep 3133525 = 36721) (by norm_num)
theorem B5296261 : Blo 1855629 5296261 := bbase (se 4 (by rfl) ⟨496524, by rfl⟩ : syracuseStep 5296261 = 993049) (by norm_num)
theorem B14094485 : Blo 1855629 14094485 := bbase (se 6 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 14094485 = 660679) (by norm_num)
theorem B3133613 : Blo 1855629 3133613 := bbase (se 3 (by rfl) ⟨587552, by rfl⟩ : syracuseStep 3133613 = 1175105) (by norm_num)
theorem B5648629 : Blo 1855629 5648629 := bbase (se 5 (by rfl) ⟨264779, by rfl⟩ : syracuseStep 5648629 = 529559) (by norm_num)
theorem B3133741 : Blo 1855629 3133741 := bbase (se 3 (by rfl) ⟨587576, by rfl⟩ : syracuseStep 3133741 = 1175153) (by norm_num)
theorem B4698445 : Blo 1855629 4698445 := bbase (se 3 (by rfl) ⟨880958, by rfl⟩ : syracuseStep 4698445 = 1761917) (by norm_num)
theorem B3133829 : Blo 1855629 3133829 := bbase (se 4 (by rfl) ⟨293796, by rfl⟩ : syracuseStep 3133829 = 587593) (by norm_num)
theorem B6263189 : Blo 1855629 6263189 := bbase (se 6 (by rfl) ⟨146793, by rfl⟩ : syracuseStep 6263189 = 293587) (by norm_num)
theorem B4698557 : Blo 1855629 4698557 := bbase (se 3 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 4698557 = 1761959) (by norm_num)
theorem B3133957 : Blo 1855629 3133957 := bbase (se 4 (by rfl) ⟨293808, by rfl⟩ : syracuseStep 3133957 = 587617) (by norm_num)
theorem B5288485 : Blo 1855629 5288485 := bbase (se 4 (by rfl) ⟨495795, by rfl⟩ : syracuseStep 5288485 = 991591) (by norm_num)
theorem B6779461 : Blo 1855629 6779461 := bbase (se 4 (by rfl) ⟨635574, by rfl⟩ : syracuseStep 6779461 = 1271149) (by norm_num)
theorem B3134045 : Blo 1855629 3134045 := bbase (se 3 (by rfl) ⟨587633, by rfl⟩ : syracuseStep 3134045 = 1175267) (by norm_num)
theorem B2642557 : Blo 1855629 2642557 := bbase (se 3 (by rfl) ⟨495479, by rfl⟩ : syracuseStep 2642557 = 990959) (by norm_num)
theorem B4698749 : Blo 1855629 4698749 := bbase (se 3 (by rfl) ⟨881015, by rfl⟩ : syracuseStep 4698749 = 1762031) (by norm_num)
theorem B2118313 : Blo 1855629 2118313 := bbase (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) (by norm_num)
theorem B5288645 : Blo 1855629 5288645 := bbase (se 4 (by rfl) ⟨495810, by rfl⟩ : syracuseStep 5288645 = 991621) (by norm_num)
theorem B3134173 : Blo 1855629 3134173 := bbase (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) (by norm_num)
theorem B7050037 : Blo 1855629 7050037 := bbase (se 5 (by rfl) ⟨330470, by rfl⟩ : syracuseStep 7050037 = 660941) (by norm_num)
theorem B3134261 : Blo 1855629 3134261 := bbase (se 5 (by rfl) ⟨146918, by rfl⟩ : syracuseStep 3134261 = 293837) (by norm_num)
theorem B6263621 : Blo 1855629 6263621 := bbase (se 4 (by rfl) ⟨587214, by rfl⟩ : syracuseStep 6263621 = 1174429) (by norm_num)
theorem B2380681 : Blo 1855629 2380681 := bbase (se 2 (by rfl) ⟨892755, by rfl⟩ : syracuseStep 2380681 = 1785511) (by norm_num)
theorem B5288885 : Blo 1855629 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B3134389 : Blo 1855629 3134389 := bbase (se 5 (by rfl) ⟨146924, by rfl⟩ : syracuseStep 3134389 = 293849) (by norm_num)
theorem B4830149 : Blo 1855629 4830149 := bbase (se 4 (by rfl) ⟨452826, by rfl⟩ : syracuseStep 4830149 = 905653) (by norm_num)
theorem B4699093 : Blo 1855629 4699093 := bbase (se 7 (by rfl) ⟨55067, by rfl⟩ : syracuseStep 4699093 = 110135) (by norm_num)
theorem B3134477 : Blo 1855629 3134477 := bbase (se 3 (by rfl) ⟨587714, by rfl⟩ : syracuseStep 3134477 = 1175429) (by norm_num)
theorem B4699205 : Blo 1855629 4699205 := bbase (se 4 (by rfl) ⟨440550, by rfl⟩ : syracuseStep 4699205 = 881101) (by norm_num)
theorem B7050341 : Blo 1855629 7050341 := bbase (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) (by norm_num)
theorem B5289077 : Blo 1855629 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B3134605 : Blo 1855629 3134605 := bbase (se 3 (by rfl) ⟨587738, by rfl⟩ : syracuseStep 3134605 = 1175477) (by norm_num)
theorem B4019357 : Blo 1855629 4019357 := bbase (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) (by norm_num)
theorem B2643149 : Blo 1855629 2643149 := bbase (se 3 (by rfl) ⟨495590, by rfl⟩ : syracuseStep 2643149 = 991181) (by norm_num)
theorem B3134693 : Blo 1855629 3134693 := bbase (se 4 (by rfl) ⟨293877, by rfl⟩ : syracuseStep 3134693 = 587755) (by norm_num)
theorem B6264053 : Blo 1855629 6264053 := bbase (se 5 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 6264053 = 587255) (by norm_num)
theorem B4699397 : Blo 1855629 4699397 := bbase (se 4 (by rfl) ⟨440568, by rfl⟩ : syracuseStep 4699397 = 881137) (by norm_num)
theorem B2643229 : Blo 1855629 2643229 := bbase (se 3 (by rfl) ⟨495605, by rfl⟩ : syracuseStep 2643229 = 991211) (by norm_num)
theorem B2823493 : Blo 1855629 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B9401669 : Blo 1855629 9401669 := bbase (se 4 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 9401669 = 1762813) (by norm_num)
theorem B4175189 : Blo 1855629 4175189 := bbase (se 13 (by rfl) ⟨764, by rfl⟩ : syracuseStep 4175189 = 1529) (by norm_num)
theorem B3765629 : Blo 1855629 3765629 := bbase (se 3 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 3765629 = 1412111) (by norm_num)
theorem B2643349 : Blo 1855629 2643349 := bbase (se 6 (by rfl) ⟨61953, by rfl⟩ : syracuseStep 2643349 = 123907) (by norm_num)
theorem B4175261 : Blo 1855629 4175261 := bbase (se 3 (by rfl) ⟨782861, by rfl⟩ : syracuseStep 4175261 = 1565723) (by norm_num)
theorem B1881517 : Blo 1855629 1881517 := bbase (se 3 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 1881517 = 705569) (by norm_num)
theorem B4175333 : Blo 1855629 4175333 := bbase (se 4 (by rfl) ⟨391437, by rfl⟩ : syracuseStep 4175333 = 782875) (by norm_num)
theorem B2643445 : Blo 1855629 2643445 := bbase (se 5 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 2643445 = 247823) (by norm_num)
theorem B18093557 : Blo 1855629 18093557 := bbase (se 5 (by rfl) ⟨848135, by rfl⟩ : syracuseStep 18093557 = 1696271) (by norm_num)
theorem B4175405 : Blo 1855629 4175405 := bbase (se 3 (by rfl) ⟨782888, by rfl⟩ : syracuseStep 4175405 = 1565777) (by norm_num)
theorem B2348605 : Blo 1855629 2348605 := bbase (se 3 (by rfl) ⟨440363, by rfl⟩ : syracuseStep 2348605 = 880727) (by norm_num)
theorem B4462141 : Blo 1855629 4462141 := bbase (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) (by norm_num)
theorem B7525973 : Blo 1855629 7525973 := bbase (se 8 (by rfl) ⟨44097, by rfl⟩ : syracuseStep 7525973 = 88195) (by norm_num)
theorem B4699741 : Blo 1855629 4699741 := bbase (se 3 (by rfl) ⟨881201, by rfl⟩ : syracuseStep 4699741 = 1762403) (by norm_num)
theorem B4175477 : Blo 1855629 4175477 := bbase (se 5 (by rfl) ⟨195725, by rfl⟩ : syracuseStep 4175477 = 391451) (by norm_num)
theorem B6264485 : Blo 1855629 6264485 := bbase (se 4 (by rfl) ⟨587295, by rfl⟩ : syracuseStep 6264485 = 1174591) (by norm_num)
theorem B4175549 : Blo 1855629 4175549 := bbase (se 3 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 4175549 = 1565831) (by norm_num)
theorem B4699853 : Blo 1855629 4699853 := bbase (se 3 (by rfl) ⟨881222, by rfl⟩ : syracuseStep 4699853 = 1762445) (by norm_num)
theorem B2348777 : Blo 1855629 2348777 := bbase (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) (by norm_num)
theorem B4175621 : Blo 1855629 4175621 := bbase (se 4 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 4175621 = 782929) (by norm_num)
theorem B2348833 : Blo 1855629 2348833 := bbase (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) (by norm_num)
theorem B4175693 : Blo 1855629 4175693 := bbase (se 3 (by rfl) ⟨782942, by rfl⟩ : syracuseStep 4175693 = 1565885) (by norm_num)
theorem B2348929 : Blo 1855629 2348929 := bbase (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) (by norm_num)
theorem B2381705 : Blo 1855629 2381705 := bbase (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) (by norm_num)
theorem B4700045 : Blo 1855629 4700045 := bbase (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) (by norm_num)
theorem B4175765 : Blo 1855629 4175765 := bbase (se 6 (by rfl) ⟨97869, by rfl⟩ : syracuseStep 4175765 = 195739) (by norm_num)
theorem B4175837 : Blo 1855629 4175837 := bbase (se 3 (by rfl) ⟨782969, by rfl⟩ : syracuseStep 4175837 = 1565939) (by norm_num)
theorem B2643941 : Blo 1855629 2643941 := bbase (se 4 (by rfl) ⟨247869, by rfl⟩ : syracuseStep 2643941 = 495739) (by norm_num)
theorem B4175909 : Blo 1855629 4175909 := bbase (se 4 (by rfl) ⟨391491, by rfl⟩ : syracuseStep 4175909 = 782983) (by norm_num)
theorem B2349101 : Blo 1855629 2349101 := bbase (se 3 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 2349101 = 880913) (by norm_num)
theorem B6264917 : Blo 1855629 6264917 := bbase (se 8 (by rfl) ⟨36708, by rfl⟩ : syracuseStep 6264917 = 73417) (by norm_num)
theorem B2349157 : Blo 1855629 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B4175981 : Blo 1855629 4175981 := bbase (se 3 (by rfl) ⟨782996, by rfl⟩ : syracuseStep 4175981 = 1565993) (by norm_num)
theorem B4176053 : Blo 1855629 4176053 := bbase (se 5 (by rfl) ⟨195752, by rfl⟩ : syracuseStep 4176053 = 391505) (by norm_num)
theorem B2349253 : Blo 1855629 2349253 := bbase (se 4 (by rfl) ⟨220242, by rfl⟩ : syracuseStep 2349253 = 440485) (by norm_num)
theorem B2783453 : Blo 1855629 2783453 := bbase (se 3 (by rfl) ⟨521897, by rfl⟩ : syracuseStep 2783453 = 1043795) (by norm_num)
theorem B4462813 : Blo 1855629 4462813 := bbase (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) (by norm_num)
theorem B4700389 : Blo 1855629 4700389 := bbase (se 4 (by rfl) ⟨440661, by rfl⟩ : syracuseStep 4700389 = 881323) (by norm_num)
theorem B2783477 : Blo 1855629 2783477 := bbase (se 5 (by rfl) ⟨130475, by rfl⟩ : syracuseStep 2783477 = 260951) (by norm_num)
theorem B4176125 : Blo 1855629 4176125 := bbase (se 3 (by rfl) ⟨783023, by rfl⟩ : syracuseStep 4176125 = 1566047) (by norm_num)
theorem B9525509 : Blo 1855629 9525509 := bbase (se 4 (by rfl) ⟨893016, by rfl⟩ : syracuseStep 9525509 = 1786033) (by norm_num)
theorem B2783501 : Blo 1855629 2783501 := bbase (se 3 (by rfl) ⟨521906, by rfl⟩ : syracuseStep 2783501 = 1043813) (by norm_num)
theorem B2783525 : Blo 1855629 2783525 := bbase (se 4 (by rfl) ⟨260955, by rfl⟩ : syracuseStep 2783525 = 521911) (by norm_num)
theorem B1882409 : Blo 1855629 1882409 := bbase (se 2 (by rfl) ⟨705903, by rfl⟩ : syracuseStep 1882409 = 1411807) (by norm_num)
theorem B2783549 : Blo 1855629 2783549 := bbase (se 3 (by rfl) ⟨521915, by rfl⟩ : syracuseStep 2783549 = 1043831) (by norm_num)
theorem B4176197 : Blo 1855629 4176197 := bbase (se 4 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 4176197 = 783037) (by norm_num)
theorem B2783573 : Blo 1855629 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B4700501 : Blo 1855629 4700501 := bbase (se 10 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 4700501 = 13771) (by norm_num)
theorem B2783597 : Blo 1855629 2783597 := bbase (se 3 (by rfl) ⟨521924, by rfl⟩ : syracuseStep 2783597 = 1043849) (by norm_num)
theorem B2349425 : Blo 1855629 2349425 := bbase (se 2 (by rfl) ⟨881034, by rfl⟩ : syracuseStep 2349425 = 1762069) (by norm_num)
theorem B2783621 : Blo 1855629 2783621 := bbase (se 4 (by rfl) ⟨260964, by rfl⟩ : syracuseStep 2783621 = 521929) (by norm_num)
theorem B8468869 : Blo 1855629 8468869 := bbase (se 4 (by rfl) ⟨793956, by rfl⟩ : syracuseStep 8468869 = 1587913) (by norm_num)
theorem B4176269 : Blo 1855629 4176269 := bbase (se 3 (by rfl) ⟨783050, by rfl⟩ : syracuseStep 4176269 = 1566101) (by norm_num)
theorem B2783645 : Blo 1855629 2783645 := bbase (se 3 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 2783645 = 1043867) (by norm_num)
theorem B2349481 : Blo 1855629 2349481 := bbase (se 2 (by rfl) ⟨881055, by rfl⟩ : syracuseStep 2349481 = 1762111) (by norm_num)
theorem B2783669 : Blo 1855629 2783669 := bbase (se 5 (by rfl) ⟨130484, by rfl⟩ : syracuseStep 2783669 = 260969) (by norm_num)
theorem B4463045 : Blo 1855629 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B2783693 : Blo 1855629 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B4176341 : Blo 1855629 4176341 := bbase (se 7 (by rfl) ⟨48941, by rfl⟩ : syracuseStep 4176341 = 97883) (by norm_num)
theorem B2783717 : Blo 1855629 2783717 := bbase (se 4 (by rfl) ⟨260973, by rfl⟩ : syracuseStep 2783717 = 521947) (by norm_num)
theorem B2783741 : Blo 1855629 2783741 := bbase (se 3 (by rfl) ⟨521951, by rfl⟩ : syracuseStep 2783741 = 1043903) (by norm_num)
theorem B4233725 : Blo 1855629 4233725 := bbase (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) (by norm_num)
theorem B6265349 : Blo 1855629 6265349 := bbase (se 4 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 6265349 = 1174753) (by norm_num)
theorem B2349577 : Blo 1855629 2349577 := bbase (se 2 (by rfl) ⟨881091, by rfl⟩ : syracuseStep 2349577 = 1762183) (by norm_num)
theorem B2644493 : Blo 1855629 2644493 := bbase (se 3 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 2644493 = 991685) (by norm_num)
theorem B2783765 : Blo 1855629 2783765 := bbase (se 6 (by rfl) ⟨65244, by rfl⟩ : syracuseStep 2783765 = 130489) (by norm_num)
theorem B4700693 : Blo 1855629 4700693 := bbase (se 6 (by rfl) ⟨110172, by rfl⟩ : syracuseStep 4700693 = 220345) (by norm_num)
theorem B4176413 : Blo 1855629 4176413 := bbase (se 3 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 4176413 = 1566155) (by norm_num)
theorem B2783789 : Blo 1855629 2783789 := bbase (se 3 (by rfl) ⟨521960, by rfl⟩ : syracuseStep 2783789 = 1043921) (by norm_num)
theorem B10033717 : Blo 1855629 10033717 := bbase (se 5 (by rfl) ⟨470330, by rfl⟩ : syracuseStep 10033717 = 940661) (by norm_num)
theorem B11893301 : Blo 1855629 11893301 := bbase (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) (by norm_num)
theorem B2783813 : Blo 1855629 2783813 := bbase (se 4 (by rfl) ⟨260982, by rfl⟩ : syracuseStep 2783813 = 521965) (by norm_num)
theorem B4233797 : Blo 1855629 4233797 := bbase (se 4 (by rfl) ⟨396918, by rfl⟩ : syracuseStep 4233797 = 793837) (by norm_num)
theorem B9402965 : Blo 1855629 9402965 := bbase (se 8 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 9402965 = 110191) (by norm_num)
theorem B4463189 : Blo 1855629 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B2783837 : Blo 1855629 2783837 := bbase (se 3 (by rfl) ⟨521969, by rfl⟩ : syracuseStep 2783837 = 1043939) (by norm_num)
theorem B4176485 : Blo 1855629 4176485 := bbase (se 4 (by rfl) ⟨391545, by rfl⟩ : syracuseStep 4176485 = 783091) (by norm_num)
theorem B2783861 : Blo 1855629 2783861 := bbase (se 5 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 2783861 = 260987) (by norm_num)
theorem B4020853 : Blo 1855629 4020853 := bbase (se 5 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 4020853 = 376955) (by norm_num)
theorem B4463237 : Blo 1855629 4463237 := bbase (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) (by norm_num)
theorem B2783885 : Blo 1855629 2783885 := bbase (se 3 (by rfl) ⟨521978, by rfl⟩ : syracuseStep 2783885 = 1043957) (by norm_num)
theorem B4291213 : Blo 1855629 4291213 := bbase (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) (by norm_num)
theorem B2783909 : Blo 1855629 2783909 := bbase (se 4 (by rfl) ⟨260991, by rfl⟩ : syracuseStep 2783909 = 521983) (by norm_num)
theorem B4176557 : Blo 1855629 4176557 := bbase (se 3 (by rfl) ⟨783104, by rfl⟩ : syracuseStep 4176557 = 1566209) (by norm_num)
theorem B2349749 : Blo 1855629 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B15866549 : Blo 1855629 15866549 := bbase (se 5 (by rfl) ⟨743744, by rfl⟩ : syracuseStep 15866549 = 1487489) (by norm_num)
theorem B2783933 : Blo 1855629 2783933 := bbase (se 3 (by rfl) ⟨521987, by rfl⟩ : syracuseStep 2783933 = 1043975) (by norm_num)
theorem B2087617 : Blo 1855629 2087617 := bbase (se 2 (by rfl) ⟨782856, by rfl⟩ : syracuseStep 2087617 = 1565713) (by norm_num)
theorem B2783957 : Blo 1855629 2783957 := bbase (se 7 (by rfl) ⟨32624, by rfl⟩ : syracuseStep 2783957 = 65249) (by norm_num)
theorem B2087653 : Blo 1855629 2087653 := bbase (se 4 (by rfl) ⟨195717, by rfl⟩ : syracuseStep 2087653 = 391435) (by norm_num)
theorem B2783981 : Blo 1855629 2783981 := bbase (se 3 (by rfl) ⟨521996, by rfl⟩ : syracuseStep 2783981 = 1043993) (by norm_num)
theorem B2349805 : Blo 1855629 2349805 := bbase (se 3 (by rfl) ⟨440588, by rfl⟩ : syracuseStep 2349805 = 881177) (by norm_num)
theorem B4176629 : Blo 1855629 4176629 := bbase (se 5 (by rfl) ⟨195779, by rfl⟩ : syracuseStep 4176629 = 391559) (by norm_num)
theorem B2784005 : Blo 1855629 2784005 := bbase (se 4 (by rfl) ⟨261000, by rfl⟩ : syracuseStep 2784005 = 522001) (by norm_num)
theorem B2087689 : Blo 1855629 2087689 := bbase (se 2 (by rfl) ⟨782883, by rfl⟩ : syracuseStep 2087689 = 1565767) (by norm_num)
theorem B26753813 : Blo 1855629 26753813 := bbase (se 6 (by rfl) ⟨627042, by rfl⟩ : syracuseStep 26753813 = 1254085) (by norm_num)
theorem B2784029 : Blo 1855629 2784029 := bbase (se 3 (by rfl) ⟨522005, by rfl⟩ : syracuseStep 2784029 = 1044011) (by norm_num)
theorem B2087725 : Blo 1855629 2087725 := bbase (se 3 (by rfl) ⟨391448, by rfl⟩ : syracuseStep 2087725 = 782897) (by norm_num)
theorem B2784053 : Blo 1855629 2784053 := bbase (se 5 (by rfl) ⟨130502, by rfl⟩ : syracuseStep 2784053 = 261005) (by norm_num)
theorem B4176701 : Blo 1855629 4176701 := bbase (se 3 (by rfl) ⟨783131, by rfl⟩ : syracuseStep 4176701 = 1566263) (by norm_num)
theorem B3963725 : Blo 1855629 3963725 := bbase (se 3 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 3963725 = 1486397) (by norm_num)
theorem B2784077 : Blo 1855629 2784077 := bbase (se 3 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 2784077 = 1044029) (by norm_num)
theorem B2349901 : Blo 1855629 2349901 := bbase (se 3 (by rfl) ⟨440606, by rfl⟩ : syracuseStep 2349901 = 881213) (by norm_num)
theorem B2087761 : Blo 1855629 2087761 := bbase (se 2 (by rfl) ⟨782910, by rfl⟩ : syracuseStep 2087761 = 1565821) (by norm_num)
theorem B2784101 : Blo 1855629 2784101 := bbase (se 4 (by rfl) ⟨261009, by rfl⟩ : syracuseStep 2784101 = 522019) (by norm_num)
theorem B4701037 : Blo 1855629 4701037 := bbase (se 3 (by rfl) ⟨881444, by rfl⟩ : syracuseStep 4701037 = 1762889) (by norm_num)
theorem B2087797 : Blo 1855629 2087797 := bbase (se 5 (by rfl) ⟨97865, by rfl⟩ : syracuseStep 2087797 = 195731) (by norm_num)
theorem B2784125 : Blo 1855629 2784125 := bbase (se 3 (by rfl) ⟨522023, by rfl⟩ : syracuseStep 2784125 = 1044047) (by norm_num)
theorem B4176773 : Blo 1855629 4176773 := bbase (se 4 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 4176773 = 783145) (by norm_num)
theorem B2784149 : Blo 1855629 2784149 := bbase (se 6 (by rfl) ⟨65253, by rfl⟩ : syracuseStep 2784149 = 130507) (by norm_num)
theorem B2087833 : Blo 1855629 2087833 := bbase (se 2 (by rfl) ⟨782937, by rfl⟩ : syracuseStep 2087833 = 1565875) (by norm_num)
theorem B2784173 : Blo 1855629 2784173 := bbase (se 3 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 2784173 = 1044065) (by norm_num)
theorem B6265781 : Blo 1855629 6265781 := bbase (se 5 (by rfl) ⟨293708, by rfl⟩ : syracuseStep 6265781 = 587417) (by norm_num)
theorem B2087869 : Blo 1855629 2087869 := bbase (se 3 (by rfl) ⟨391475, by rfl⟩ : syracuseStep 2087869 = 782951) (by norm_num)
theorem B2784197 : Blo 1855629 2784197 := bbase (se 4 (by rfl) ⟨261018, by rfl⟩ : syracuseStep 2784197 = 522037) (by norm_num)
theorem B2972621 : Blo 1855629 2972621 := bbase (se 3 (by rfl) ⟨557366, by rfl⟩ : syracuseStep 2972621 = 1114733) (by norm_num)
theorem B4176845 : Blo 1855629 4176845 := bbase (se 3 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 4176845 = 1566317) (by norm_num)
theorem B2784221 : Blo 1855629 2784221 := bbase (se 3 (by rfl) ⟨522041, by rfl⟩ : syracuseStep 2784221 = 1044083) (by norm_num)
theorem B4701149 : Blo 1855629 4701149 := bbase (se 3 (by rfl) ⟨881465, by rfl⟩ : syracuseStep 4701149 = 1762931) (by norm_num)
theorem B2087905 : Blo 1855629 2087905 := bbase (se 2 (by rfl) ⟨782964, by rfl⟩ : syracuseStep 2087905 = 1565929) (by norm_num)
theorem B2145253 : Blo 1855629 2145253 := bbase (se 4 (by rfl) ⟨201117, by rfl⟩ : syracuseStep 2145253 = 402235) (by norm_num)
theorem B9395189 : Blo 1855629 9395189 := bbase (se 5 (by rfl) ⟨440399, by rfl⟩ : syracuseStep 9395189 = 880799) (by norm_num)
theorem B2784245 : Blo 1855629 2784245 := bbase (se 5 (by rfl) ⟨130511, by rfl⟩ : syracuseStep 2784245 = 261023) (by norm_num)
theorem B2350073 : Blo 1855629 2350073 := bbase (se 2 (by rfl) ⟨881277, by rfl⟩ : syracuseStep 2350073 = 1762555) (by norm_num)
theorem B2087941 : Blo 1855629 2087941 := bbase (se 4 (by rfl) ⟨195744, by rfl⟩ : syracuseStep 2087941 = 391489) (by norm_num)
theorem B2784269 : Blo 1855629 2784269 := bbase (se 3 (by rfl) ⟨522050, by rfl⟩ : syracuseStep 2784269 = 1044101) (by norm_num)
theorem B4176917 : Blo 1855629 4176917 := bbase (se 6 (by rfl) ⟨97896, by rfl⟩ : syracuseStep 4176917 = 195793) (by norm_num)
theorem B2784293 : Blo 1855629 2784293 := bbase (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) (by norm_num)
theorem B2087977 : Blo 1855629 2087977 := bbase (se 2 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 2087977 = 1565983) (by norm_num)
theorem B3177517 : Blo 1855629 3177517 := bbase (se 3 (by rfl) ⟨595784, by rfl⟩ : syracuseStep 3177517 = 1191569) (by norm_num)
theorem B2350129 : Blo 1855629 2350129 := bbase (se 2 (by rfl) ⟨881298, by rfl⟩ : syracuseStep 2350129 = 1762597) (by norm_num)
theorem B2784317 : Blo 1855629 2784317 := bbase (se 3 (by rfl) ⟨522059, by rfl⟩ : syracuseStep 2784317 = 1044119) (by norm_num)
theorem B2088013 : Blo 1855629 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B2784341 : Blo 1855629 2784341 := bbase (se 8 (by rfl) ⟨16314, by rfl⟩ : syracuseStep 2784341 = 32629) (by norm_num)
theorem B4176989 : Blo 1855629 4176989 := bbase (se 3 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 4176989 = 1566371) (by norm_num)
theorem B2784365 : Blo 1855629 2784365 := bbase (se 3 (by rfl) ⟨522068, by rfl⟩ : syracuseStep 2784365 = 1044137) (by norm_num)
theorem B2088049 : Blo 1855629 2088049 := bbase (se 2 (by rfl) ⟨783018, by rfl⟩ : syracuseStep 2088049 = 1566037) (by norm_num)
theorem B2784389 : Blo 1855629 2784389 := bbase (se 4 (by rfl) ⟨261036, by rfl⟩ : syracuseStep 2784389 = 522073) (by norm_num)
theorem B2350225 : Blo 1855629 2350225 := bbase (se 2 (by rfl) ⟨881334, by rfl⟩ : syracuseStep 2350225 = 1762669) (by norm_num)
theorem B1981589 : Blo 1855629 1981589 := bbase (se 6 (by rfl) ⟨46443, by rfl⟩ : syracuseStep 1981589 = 92887) (by norm_num)
theorem B2088085 : Blo 1855629 2088085 := bbase (se 6 (by rfl) ⟨48939, by rfl⟩ : syracuseStep 2088085 = 97879) (by norm_num)
theorem B2784413 : Blo 1855629 2784413 := bbase (se 3 (by rfl) ⟨522077, by rfl⟩ : syracuseStep 2784413 = 1044155) (by norm_num)
theorem B4701341 : Blo 1855629 4701341 := bbase (se 3 (by rfl) ⟨881501, by rfl⟩ : syracuseStep 4701341 = 1763003) (by norm_num)
theorem B4177061 : Blo 1855629 4177061 := bbase (se 4 (by rfl) ⟨391599, by rfl⟩ : syracuseStep 4177061 = 783199) (by norm_num)
theorem B7052453 : Blo 1855629 7052453 := bbase (se 4 (by rfl) ⟨661167, by rfl⟩ : syracuseStep 7052453 = 1322335) (by norm_num)
theorem B2784437 : Blo 1855629 2784437 := bbase (se 5 (by rfl) ⟨130520, by rfl⟩ : syracuseStep 2784437 = 261041) (by norm_num)
theorem B2088121 : Blo 1855629 2088121 := bbase (se 2 (by rfl) ⟨783045, by rfl⟩ : syracuseStep 2088121 = 1566091) (by norm_num)
theorem B2784461 : Blo 1855629 2784461 := bbase (se 3 (by rfl) ⟨522086, by rfl⟩ : syracuseStep 2784461 = 1044173) (by norm_num)
theorem B2088157 : Blo 1855629 2088157 := bbase (se 3 (by rfl) ⟨391529, by rfl⟩ : syracuseStep 2088157 = 783059) (by norm_num)
theorem B2784485 : Blo 1855629 2784485 := bbase (se 4 (by rfl) ⟨261045, by rfl⟩ : syracuseStep 2784485 = 522091) (by norm_num)
theorem B4177133 : Blo 1855629 4177133 := bbase (se 3 (by rfl) ⟨783212, by rfl⟩ : syracuseStep 4177133 = 1566425) (by norm_num)
theorem B2784509 : Blo 1855629 2784509 := bbase (se 3 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 2784509 = 1044191) (by norm_num)
theorem B2088193 : Blo 1855629 2088193 := bbase (se 2 (by rfl) ⟨783072, by rfl⟩ : syracuseStep 2088193 = 1566145) (by norm_num)
theorem B2784533 : Blo 1855629 2784533 := bbase (se 6 (by rfl) ⟨65262, by rfl⟩ : syracuseStep 2784533 = 130525) (by norm_num)
theorem B2088229 : Blo 1855629 2088229 := bbase (se 4 (by rfl) ⟨195771, by rfl⟩ : syracuseStep 2088229 = 391543) (by norm_num)
theorem B2784557 : Blo 1855629 2784557 := bbase (se 3 (by rfl) ⟨522104, by rfl⟩ : syracuseStep 2784557 = 1044209) (by norm_num)
theorem B4177205 : Blo 1855629 4177205 := bbase (se 5 (by rfl) ⟨195806, by rfl⟩ : syracuseStep 4177205 = 391613) (by norm_num)
theorem B2350397 : Blo 1855629 2350397 := bbase (se 3 (by rfl) ⟨440699, by rfl⟩ : syracuseStep 2350397 = 881399) (by norm_num)
theorem B2784581 : Blo 1855629 2784581 := bbase (se 4 (by rfl) ⟨261054, by rfl⟩ : syracuseStep 2784581 = 522109) (by norm_num)
theorem B2088265 : Blo 1855629 2088265 := bbase (se 2 (by rfl) ⟨783099, by rfl⟩ : syracuseStep 2088265 = 1566199) (by norm_num)
theorem B2973005 : Blo 1855629 2973005 := bbase (se 3 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 2973005 = 1114877) (by norm_num)
theorem B2784605 : Blo 1855629 2784605 := bbase (se 3 (by rfl) ⟨522113, by rfl⟩ : syracuseStep 2784605 = 1044227) (by norm_num)
theorem B6266213 : Blo 1855629 6266213 := bbase (se 4 (by rfl) ⟨587457, by rfl⟩ : syracuseStep 6266213 = 1174915) (by norm_num)
theorem B2088301 : Blo 1855629 2088301 := bbase (se 3 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 2088301 = 783113) (by norm_num)
theorem B2784629 : Blo 1855629 2784629 := bbase (se 5 (by rfl) ⟨130529, by rfl⟩ : syracuseStep 2784629 = 261059) (by norm_num)
theorem B2350453 : Blo 1855629 2350453 := bbase (se 5 (by rfl) ⟨110177, by rfl⟩ : syracuseStep 2350453 = 220355) (by norm_num)
theorem B4177277 : Blo 1855629 4177277 := bbase (se 3 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 4177277 = 1566479) (by norm_num)
theorem B2784653 : Blo 1855629 2784653 := bbase (se 3 (by rfl) ⟨522122, by rfl⟩ : syracuseStep 2784653 = 1044245) (by norm_num)
theorem B2088337 : Blo 1855629 2088337 := bbase (se 2 (by rfl) ⟨783126, by rfl⟩ : syracuseStep 2088337 = 1566253) (by norm_num)
theorem B4521365 : Blo 1855629 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B10722709 : Blo 1855629 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B2784677 : Blo 1855629 2784677 := bbase (se 4 (by rfl) ⟨261063, by rfl⟩ : syracuseStep 2784677 = 522127) (by norm_num)
theorem B2088373 : Blo 1855629 2088373 := bbase (se 5 (by rfl) ⟨97892, by rfl⟩ : syracuseStep 2088373 = 195785) (by norm_num)
theorem B2784701 : Blo 1855629 2784701 := bbase (se 3 (by rfl) ⟨522131, by rfl⟩ : syracuseStep 2784701 = 1044263) (by norm_num)
theorem B4177349 : Blo 1855629 4177349 := bbase (se 4 (by rfl) ⟨391626, by rfl⟩ : syracuseStep 4177349 = 783253) (by norm_num)
theorem B7052741 : Blo 1855629 7052741 := bbase (se 4 (by rfl) ⟨661194, by rfl⟩ : syracuseStep 7052741 = 1322389) (by norm_num)
theorem B2973133 : Blo 1855629 2973133 := bbase (se 3 (by rfl) ⟨557462, by rfl⟩ : syracuseStep 2973133 = 1114925) (by norm_num)
theorem B2784725 : Blo 1855629 2784725 := bbase (se 7 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 2784725 = 65267) (by norm_num)
theorem B2350549 : Blo 1855629 2350549 := bbase (se 7 (by rfl) ⟨27545, by rfl⟩ : syracuseStep 2350549 = 55091) (by norm_num)
theorem B2088409 : Blo 1855629 2088409 := bbase (se 2 (by rfl) ⟨783153, by rfl⟩ : syracuseStep 2088409 = 1566307) (by norm_num)
theorem B2784749 : Blo 1855629 2784749 := bbase (se 3 (by rfl) ⟨522140, by rfl⟩ : syracuseStep 2784749 = 1044281) (by norm_num)
theorem B4701685 : Blo 1855629 4701685 := bbase (se 5 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 4701685 = 440783) (by norm_num)
theorem B2088445 : Blo 1855629 2088445 := bbase (se 3 (by rfl) ⟨391583, by rfl⟩ : syracuseStep 2088445 = 783167) (by norm_num)
theorem B2784773 : Blo 1855629 2784773 := bbase (se 4 (by rfl) ⟨261072, by rfl⟩ : syracuseStep 2784773 = 522145) (by norm_num)
theorem B2260489 : Blo 1855629 2260489 := bbase (se 2 (by rfl) ⟨847683, by rfl⟩ : syracuseStep 2260489 = 1695367) (by norm_num)
theorem B4177421 : Blo 1855629 4177421 := bbase (se 3 (by rfl) ⟨783266, by rfl⟩ : syracuseStep 4177421 = 1566533) (by norm_num)
theorem B2784797 : Blo 1855629 2784797 := bbase (se 3 (by rfl) ⟨522149, by rfl⟩ : syracuseStep 2784797 = 1044299) (by norm_num)
theorem B2088481 : Blo 1855629 2088481 := bbase (se 2 (by rfl) ⟨783180, by rfl⟩ : syracuseStep 2088481 = 1566361) (by norm_num)
theorem B2784821 : Blo 1855629 2784821 := bbase (se 5 (by rfl) ⟨130538, by rfl⟩ : syracuseStep 2784821 = 261077) (by norm_num)
theorem B3964477 : Blo 1855629 3964477 := bbase (se 3 (by rfl) ⟨743339, by rfl⟩ : syracuseStep 3964477 = 1486679) (by norm_num)
theorem B2088517 : Blo 1855629 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B2784845 : Blo 1855629 2784845 := bbase (se 3 (by rfl) ⟨522158, by rfl⟩ : syracuseStep 2784845 = 1044317) (by norm_num)
theorem B4177493 : Blo 1855629 4177493 := bbase (se 8 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 4177493 = 48955) (by norm_num)
theorem B2784869 : Blo 1855629 2784869 := bbase (se 4 (by rfl) ⟨261081, by rfl⟩ : syracuseStep 2784869 = 522163) (by norm_num)
theorem B4701797 : Blo 1855629 4701797 := bbase (se 4 (by rfl) ⟨440793, by rfl⟩ : syracuseStep 4701797 = 881587) (by norm_num)
theorem B2088553 : Blo 1855629 2088553 := bbase (se 2 (by rfl) ⟨783207, by rfl⟩ : syracuseStep 2088553 = 1566415) (by norm_num)
theorem B2784893 : Blo 1855629 2784893 := bbase (se 3 (by rfl) ⟨522167, by rfl⟩ : syracuseStep 2784893 = 1044335) (by norm_num)
theorem B2350721 : Blo 1855629 2350721 := bbase (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) (by norm_num)
theorem B2088589 : Blo 1855629 2088589 := bbase (se 3 (by rfl) ⟨391610, by rfl⟩ : syracuseStep 2088589 = 783221) (by norm_num)
theorem B2784917 : Blo 1855629 2784917 := bbase (se 6 (by rfl) ⟨65271, by rfl⟩ : syracuseStep 2784917 = 130543) (by norm_num)
theorem B4177565 : Blo 1855629 4177565 := bbase (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) (by norm_num)
theorem B2784941 : Blo 1855629 2784941 := bbase (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) (by norm_num)
theorem B2088625 : Blo 1855629 2088625 := bbase (se 2 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 2088625 = 1566469) (by norm_num)
theorem B2350777 : Blo 1855629 2350777 := bbase (se 2 (by rfl) ⟨881541, by rfl⟩ : syracuseStep 2350777 = 1763083) (by norm_num)
theorem B2784965 : Blo 1855629 2784965 := bbase (se 4 (by rfl) ⟨261090, by rfl⟩ : syracuseStep 2784965 = 522181) (by norm_num)
theorem B3964621 : Blo 1855629 3964621 := bbase (se 3 (by rfl) ⟨743366, by rfl⟩ : syracuseStep 3964621 = 1486733) (by norm_num)
theorem B2088661 : Blo 1855629 2088661 := bbase (se 7 (by rfl) ⟨24476, by rfl⟩ : syracuseStep 2088661 = 48953) (by norm_num)
theorem B12705493 : Blo 1855629 12705493 := bbase (se 7 (by rfl) ⟨148892, by rfl⟩ : syracuseStep 12705493 = 297785) (by norm_num)
theorem B2784989 : Blo 1855629 2784989 := bbase (se 3 (by rfl) ⟨522185, by rfl⟩ : syracuseStep 2784989 = 1044371) (by norm_num)
theorem B4177637 : Blo 1855629 4177637 := bbase (se 4 (by rfl) ⟨391653, by rfl⟩ : syracuseStep 4177637 = 783307) (by norm_num)
theorem B2785013 : Blo 1855629 2785013 := bbase (se 5 (by rfl) ⟨130547, by rfl⟩ : syracuseStep 2785013 = 261095) (by norm_num)
theorem B2088697 : Blo 1855629 2088697 := bbase (se 2 (by rfl) ⟨783261, by rfl⟩ : syracuseStep 2088697 = 1566523) (by norm_num)
theorem B2785037 : Blo 1855629 2785037 := bbase (se 3 (by rfl) ⟨522194, by rfl⟩ : syracuseStep 2785037 = 1044389) (by norm_num)
theorem B6266645 : Blo 1855629 6266645 := bbase (se 6 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 6266645 = 293749) (by norm_num)
theorem B2350873 : Blo 1855629 2350873 := bbase (se 2 (by rfl) ⟨881577, by rfl⟩ : syracuseStep 2350873 = 1763155) (by norm_num)
theorem B2088733 : Blo 1855629 2088733 := bbase (se 3 (by rfl) ⟨391637, by rfl⟩ : syracuseStep 2088733 = 783275) (by norm_num)
theorem B2785061 : Blo 1855629 2785061 := bbase (se 4 (by rfl) ⟨261099, by rfl⟩ : syracuseStep 2785061 = 522199) (by norm_num)
theorem B4701989 : Blo 1855629 4701989 := bbase (se 4 (by rfl) ⟨440811, by rfl⟩ : syracuseStep 4701989 = 881623) (by norm_num)
theorem B4177709 : Blo 1855629 4177709 := bbase (se 3 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 4177709 = 1566641) (by norm_num)
theorem B2785085 : Blo 1855629 2785085 := bbase (se 3 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 2785085 = 1044407) (by norm_num)
theorem B2088769 : Blo 1855629 2088769 := bbase (se 2 (by rfl) ⟨783288, by rfl⟩ : syracuseStep 2088769 = 1566577) (by norm_num)
theorem B2785109 : Blo 1855629 2785109 := bbase (se 9 (by rfl) ⟨8159, by rfl⟩ : syracuseStep 2785109 = 16319) (by norm_num)
theorem B2088805 : Blo 1855629 2088805 := bbase (se 4 (by rfl) ⟨195825, by rfl⟩ : syracuseStep 2088805 = 391651) (by norm_num)
theorem B2785133 : Blo 1855629 2785133 := bbase (se 3 (by rfl) ⟨522212, by rfl⟩ : syracuseStep 2785133 = 1044425) (by norm_num)
theorem B4177781 : Blo 1855629 4177781 := bbase (se 5 (by rfl) ⟨195833, by rfl⟩ : syracuseStep 4177781 = 391667) (by norm_num)
theorem B1982341 : Blo 1855629 1982341 := bbase (se 4 (by rfl) ⟨185844, by rfl⟩ : syracuseStep 1982341 = 371689) (by norm_num)
theorem B2785157 : Blo 1855629 2785157 := bbase (se 4 (by rfl) ⟨261108, by rfl⟩ : syracuseStep 2785157 = 522217) (by norm_num)
theorem B2088841 : Blo 1855629 2088841 := bbase (se 2 (by rfl) ⟨783315, by rfl⟩ : syracuseStep 2088841 = 1566631) (by norm_num)
theorem B2785181 : Blo 1855629 2785181 := bbase (se 3 (by rfl) ⟨522221, by rfl⟩ : syracuseStep 2785181 = 1044443) (by norm_num)
theorem B2088877 : Blo 1855629 2088877 := bbase (se 3 (by rfl) ⟨391664, by rfl⟩ : syracuseStep 2088877 = 783329) (by norm_num)
theorem B2785205 : Blo 1855629 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B4177853 : Blo 1855629 4177853 := bbase (se 3 (by rfl) ⟨783347, by rfl⟩ : syracuseStep 4177853 = 1566695) (by norm_num)
theorem B2351045 : Blo 1855629 2351045 := bbase (se 4 (by rfl) ⟨220410, by rfl⟩ : syracuseStep 2351045 = 440821) (by norm_num)
theorem B1982413 : Blo 1855629 1982413 := bbase (se 3 (by rfl) ⟨371702, by rfl⟩ : syracuseStep 1982413 = 743405) (by norm_num)
theorem B2785229 : Blo 1855629 2785229 := bbase (se 3 (by rfl) ⟨522230, by rfl⟩ : syracuseStep 2785229 = 1044461) (by norm_num)
theorem B2088913 : Blo 1855629 2088913 := bbase (se 2 (by rfl) ⟨783342, by rfl⟩ : syracuseStep 2088913 = 1566685) (by norm_num)
theorem B2785253 : Blo 1855629 2785253 := bbase (se 4 (by rfl) ⟨261117, by rfl⟩ : syracuseStep 2785253 = 522235) (by norm_num)
theorem B2088949 : Blo 1855629 2088949 := bbase (se 5 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 2088949 = 195839) (by norm_num)
theorem B2785277 : Blo 1855629 2785277 := bbase (se 3 (by rfl) ⟨522239, by rfl⟩ : syracuseStep 2785277 = 1044479) (by norm_num)
theorem B2785283 : Blo 1855629 2785283 := bstep (se 1 (by rfl) ⟨2088962, by rfl⟩ : syracuseStep 2785283 = 4177925) B4177925
theorem B2785313 : Blo 1855629 2785313 := bstep (se 2 (by rfl) ⟨1044492, by rfl⟩ : syracuseStep 2785313 = 2088985) B2088985
theorem B3964963 : Blo 1855629 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B6266915 : Blo 1855629 6266915 := bstep (se 1 (by rfl) ⟨4700186, by rfl⟩ : syracuseStep 6266915 = 9400373) B9400373
theorem B2785331 : Blo 1855629 2785331 := bstep (se 1 (by rfl) ⟨2088998, by rfl⟩ : syracuseStep 2785331 = 4177997) B4177997
theorem B2785361 : Blo 1855629 2785361 := bstep (se 2 (by rfl) ⟨1044510, by rfl⟩ : syracuseStep 2785361 = 2089021) B2089021
theorem B9396323 : Blo 1855629 9396323 := bstep (se 1 (by rfl) ⟨7047242, by rfl⟩ : syracuseStep 9396323 = 14094485) B14094485
theorem B2785379 : Blo 1855629 2785379 := bstep (se 1 (by rfl) ⟨2089034, by rfl⟩ : syracuseStep 2785379 = 4178069) B4178069
theorem B4178033 : Blo 1855629 4178033 := bstep (se 2 (by rfl) ⟨1566762, by rfl⟩ : syracuseStep 4178033 = 3133525) B3133525
theorem B2089075 : Blo 1855629 2089075 := bstep (se 1 (by rfl) ⟨1566806, by rfl⟩ : syracuseStep 2089075 = 3133613) B3133613
theorem B2785409 : Blo 1855629 2785409 := bstep (se 2 (by rfl) ⟨1044528, by rfl⟩ : syracuseStep 2785409 = 2089057) B2089057
theorem B4178051 : Blo 1855629 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B2785427 : Blo 1855629 2785427 := bstep (se 1 (by rfl) ⟨2089070, by rfl⟩ : syracuseStep 2785427 = 4178141) B4178141
theorem B7061681 : Blo 1855629 7061681 := bstep (se 2 (by rfl) ⟨2648130, by rfl⟩ : syracuseStep 7061681 = 5296261) B5296261
theorem B2785457 : Blo 1855629 2785457 := bstep (se 2 (by rfl) ⟨1044546, by rfl⟩ : syracuseStep 2785457 = 2089093) B2089093
theorem B2785475 : Blo 1855629 2785475 := bstep (se 1 (by rfl) ⟨2089106, by rfl⟩ : syracuseStep 2785475 = 4178213) B4178213
theorem B2785505 : Blo 1855629 2785505 := bstep (se 2 (by rfl) ⟨1044564, by rfl⟩ : syracuseStep 2785505 = 2089129) B2089129
theorem B2785523 : Blo 1855629 2785523 := bstep (se 1 (by rfl) ⟨2089142, by rfl⟩ : syracuseStep 2785523 = 4178285) B4178285
theorem B2973953 : Blo 1855629 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B2089219 : Blo 1855629 2089219 := bstep (se 1 (by rfl) ⟨1566914, by rfl⟩ : syracuseStep 2089219 = 3133829) B3133829
theorem B2785553 : Blo 1855629 2785553 := bstep (se 2 (by rfl) ⟨1044582, by rfl⟩ : syracuseStep 2785553 = 2089165) B2089165
theorem B1982755 : Blo 1855629 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B2785571 : Blo 1855629 2785571 := bstep (se 1 (by rfl) ⟨2089178, by rfl⟩ : syracuseStep 2785571 = 4178357) B4178357
theorem B6267185 : Blo 1855629 6267185 := bstep (se 2 (by rfl) ⟨2350194, by rfl⟩ : syracuseStep 6267185 = 4700389) B4700389
theorem B2785601 : Blo 1855629 2785601 := bstep (se 2 (by rfl) ⟨1044600, by rfl⟩ : syracuseStep 2785601 = 2089201) B2089201
theorem B4522321 : Blo 1855629 4522321 := bstep (se 2 (by rfl) ⟨1695870, by rfl⟩ : syracuseStep 4522321 = 3391741) B3391741
theorem B2785619 : Blo 1855629 2785619 := bstep (se 1 (by rfl) ⟨2089214, by rfl⟩ : syracuseStep 2785619 = 4178429) B4178429
theorem B10576241 : Blo 1855629 10576241 := bstep (se 2 (by rfl) ⟨3966090, by rfl⟩ : syracuseStep 10576241 = 7932181) B7932181
theorem B2785649 : Blo 1855629 2785649 := bstep (se 2 (by rfl) ⟨1044618, by rfl⟩ : syracuseStep 2785649 = 2089237) B2089237
theorem B2974081 : Blo 1855629 2974081 := bstep (se 2 (by rfl) ⟨1115280, by rfl⟩ : syracuseStep 2974081 = 2230561) B2230561
theorem B2785667 : Blo 1855629 2785667 := bstep (se 1 (by rfl) ⟨2089250, by rfl⟩ : syracuseStep 2785667 = 4178501) B4178501
theorem B5284237 : Blo 1855629 5284237 := bstep (se 3 (by rfl) ⟨990794, by rfl⟩ : syracuseStep 5284237 = 1981589) B1981589
theorem B4178321 : Blo 1855629 4178321 := bstep (se 2 (by rfl) ⟨1566870, by rfl⟩ : syracuseStep 4178321 = 3133741) B3133741
theorem B2089363 : Blo 1855629 2089363 := bstep (se 1 (by rfl) ⟨1567022, by rfl⟩ : syracuseStep 2089363 = 3134045) B3134045
theorem B2785697 : Blo 1855629 2785697 := bstep (se 2 (by rfl) ⟨1044636, by rfl⟩ : syracuseStep 2785697 = 2089273) B2089273
theorem B4178339 : Blo 1855629 4178339 := bstep (se 1 (by rfl) ⟨3133754, by rfl⟩ : syracuseStep 4178339 = 6267509) B6267509
theorem B2785715 : Blo 1855629 2785715 := bstep (se 1 (by rfl) ⟨2089286, by rfl⟩ : syracuseStep 2785715 = 4178573) B4178573
theorem B20079029 : Blo 1855629 20079029 := bstep (se 5 (by rfl) ⟨941204, by rfl⟩ : syracuseStep 20079029 = 1882409) B1882409
theorem B5947843 : Blo 1855629 5947843 := bstep (se 1 (by rfl) ⟨4460882, by rfl⟩ : syracuseStep 5947843 = 8921765) B8921765
theorem B2785745 : Blo 1855629 2785745 := bstep (se 2 (by rfl) ⟨1044654, by rfl⟩ : syracuseStep 2785745 = 2089309) B2089309
theorem B2785763 : Blo 1855629 2785763 := bstep (se 1 (by rfl) ⟨2089322, by rfl⟩ : syracuseStep 2785763 = 4178645) B4178645
theorem B2785793 : Blo 1855629 2785793 := bstep (se 2 (by rfl) ⟨1044672, by rfl⟩ : syracuseStep 2785793 = 2089345) B2089345
theorem B13378061 : Blo 1855629 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B2785811 : Blo 1855629 2785811 := bstep (se 1 (by rfl) ⟨2089358, by rfl⟩ : syracuseStep 2785811 = 4178717) B4178717
theorem B2261539 : Blo 1855629 2261539 := bstep (se 1 (by rfl) ⟨1696154, by rfl⟩ : syracuseStep 2261539 = 3392309) B3392309
theorem B2089507 : Blo 1855629 2089507 := bstep (se 1 (by rfl) ⟨1567130, by rfl⟩ : syracuseStep 2089507 = 3134261) B3134261
theorem B2785841 : Blo 1855629 2785841 := bstep (se 2 (by rfl) ⟨1044690, by rfl⟩ : syracuseStep 2785841 = 2089381) B2089381
theorem B2785859 : Blo 1855629 2785859 := bstep (se 1 (by rfl) ⟨2089394, by rfl⟩ : syracuseStep 2785859 = 4178789) B4178789
theorem B2785889 : Blo 1855629 2785889 := bstep (se 2 (by rfl) ⟨1044708, by rfl⟩ : syracuseStep 2785889 = 2089417) B2089417
theorem B2785907 : Blo 1855629 2785907 := bstep (se 1 (by rfl) ⟨2089430, by rfl⟩ : syracuseStep 2785907 = 4178861) B4178861
theorem B2785937 : Blo 1855629 2785937 := bstep (se 2 (by rfl) ⟨1044726, by rfl⟩ : syracuseStep 2785937 = 2089453) B2089453
theorem B2785955 : Blo 1855629 2785955 := bstep (se 1 (by rfl) ⟨2089466, by rfl⟩ : syracuseStep 2785955 = 4178933) B4178933
theorem B4178609 : Blo 1855629 4178609 := bstep (se 2 (by rfl) ⟨1566978, by rfl⟩ : syracuseStep 4178609 = 3133957) B3133957
theorem B2089651 : Blo 1855629 2089651 := bstep (se 1 (by rfl) ⟨1567238, by rfl⟩ : syracuseStep 2089651 = 3134477) B3134477
theorem B2785985 : Blo 1855629 2785985 := bstep (se 2 (by rfl) ⟨1044744, by rfl⟩ : syracuseStep 2785985 = 2089489) B2089489
theorem B4178627 : Blo 1855629 4178627 := bstep (se 1 (by rfl) ⟨3133970, by rfl⟩ : syracuseStep 4178627 = 6267941) B6267941
theorem B2786003 : Blo 1855629 2786003 := bstep (se 1 (by rfl) ⟨2089502, by rfl⟩ : syracuseStep 2786003 = 4179005) B4179005
theorem B13378289 : Blo 1855629 13378289 := bstep (se 2 (by rfl) ⟨5016858, by rfl⟩ : syracuseStep 13378289 = 10033717) B10033717
theorem B3965681 : Blo 1855629 3965681 := bstep (se 2 (by rfl) ⟨1487130, by rfl⟩ : syracuseStep 3965681 = 2974261) B2974261
theorem B2786033 : Blo 1855629 2786033 := bstep (se 2 (by rfl) ⟨1044762, by rfl⟩ : syracuseStep 2786033 = 2089525) B2089525
theorem B2786051 : Blo 1855629 2786051 := bstep (se 1 (by rfl) ⟨2089538, by rfl⟩ : syracuseStep 2786051 = 4179077) B4179077
theorem B2679571 : Blo 1855629 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B2786081 : Blo 1855629 2786081 := bstep (se 2 (by rfl) ⟨1044780, by rfl⟩ : syracuseStep 2786081 = 2089561) B2089561
theorem B7045937 : Blo 1855629 7045937 := bstep (se 2 (by rfl) ⟨2642226, by rfl⟩ : syracuseStep 7045937 = 5284453) B5284453
theorem B2786099 : Blo 1855629 2786099 := bstep (se 1 (by rfl) ⟨2089574, by rfl⟩ : syracuseStep 2786099 = 4179149) B4179149
theorem B2089795 : Blo 1855629 2089795 := bstep (se 1 (by rfl) ⟨1567346, by rfl⟩ : syracuseStep 2089795 = 3134693) B3134693
theorem B6267725 : Blo 1855629 6267725 := bstep (se 3 (by rfl) ⟨1175198, by rfl⟩ : syracuseStep 6267725 = 2350397) B2350397
theorem B3523409 : Blo 1855629 3523409 := bstep (se 2 (by rfl) ⟨1321278, by rfl⟩ : syracuseStep 3523409 = 2642557) B2642557
theorem B2786129 : Blo 1855629 2786129 := bstep (se 2 (by rfl) ⟨1044798, by rfl⟩ : syracuseStep 2786129 = 2089597) B2089597
theorem B2786147 : Blo 1855629 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B2786177 : Blo 1855629 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B5948291 : Blo 1855629 5948291 := bstep (se 1 (by rfl) ⟨4461218, by rfl⟩ : syracuseStep 5948291 = 8922437) B8922437
theorem B6267779 : Blo 1855629 6267779 := bstep (se 1 (by rfl) ⟨4700834, by rfl⟩ : syracuseStep 6267779 = 9401669) B9401669
theorem B9397133 : Blo 1855629 9397133 := bstep (se 3 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 9397133 = 3523925) B3523925
theorem B2786195 : Blo 1855629 2786195 := bstep (se 1 (by rfl) ⟨2089646, by rfl⟩ : syracuseStep 2786195 = 4179293) B4179293
theorem B2786225 : Blo 1855629 2786225 := bstep (se 2 (by rfl) ⟨1044834, by rfl⟩ : syracuseStep 2786225 = 2089669) B2089669
theorem B2786243 : Blo 1855629 2786243 := bstep (se 1 (by rfl) ⟨2089682, by rfl⟩ : syracuseStep 2786243 = 4179365) B4179365
theorem B4178897 : Blo 1855629 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B2786273 : Blo 1855629 2786273 := bstep (se 2 (by rfl) ⟨1044852, by rfl⟩ : syracuseStep 2786273 = 2089705) B2089705
theorem B4178915 : Blo 1855629 4178915 := bstep (se 1 (by rfl) ⟨3134186, by rfl⟩ : syracuseStep 4178915 = 6268373) B6268373
theorem B2786291 : Blo 1855629 2786291 := bstep (se 1 (by rfl) ⟨2089718, by rfl⟩ : syracuseStep 2786291 = 4179437) B4179437
theorem B2786321 : Blo 1855629 2786321 := bstep (se 2 (by rfl) ⟨1044870, by rfl⟩ : syracuseStep 2786321 = 2089741) B2089741
theorem B2786339 : Blo 1855629 2786339 := bstep (se 1 (by rfl) ⟨2089754, by rfl⟩ : syracuseStep 2786339 = 4179509) B4179509
theorem B2786369 : Blo 1855629 2786369 := bstep (se 2 (by rfl) ⟨1044888, by rfl⟩ : syracuseStep 2786369 = 2089777) B2089777
theorem B2229331 : Blo 1855629 2229331 := bstep (se 1 (by rfl) ⟨1671998, by rfl⟩ : syracuseStep 2229331 = 3343997) B3343997
theorem B2786387 : Blo 1855629 2786387 := bstep (se 1 (by rfl) ⟨2089790, by rfl⟩ : syracuseStep 2786387 = 4179581) B4179581
theorem B2786417 : Blo 1855629 2786417 := bstep (se 2 (by rfl) ⟨1044906, by rfl⟩ : syracuseStep 2786417 = 2089813) B2089813
theorem B2786435 : Blo 1855629 2786435 := bstep (se 1 (by rfl) ⟨2089826, by rfl⟩ : syracuseStep 2786435 = 4179653) B4179653
theorem B12698765 : Blo 1855629 12698765 := bstep (se 3 (by rfl) ⟨2381018, by rfl⟩ : syracuseStep 12698765 = 4762037) B4762037
theorem B6268049 : Blo 1855629 6268049 := bstep (se 2 (by rfl) ⟨2350518, by rfl⟩ : syracuseStep 6268049 = 4701037) B4701037
theorem B7144625 : Blo 1855629 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B3966193 : Blo 1855629 3966193 := bstep (se 2 (by rfl) ⟨1487322, by rfl⟩ : syracuseStep 3966193 = 2974645) B2974645
theorem B4179185 : Blo 1855629 4179185 := bstep (se 2 (by rfl) ⟨1567194, by rfl⟩ : syracuseStep 4179185 = 3134389) B3134389
theorem B4179203 : Blo 1855629 4179203 := bstep (se 1 (by rfl) ⟨3134402, by rfl⟩ : syracuseStep 4179203 = 6268805) B6268805
theorem B2860337 : Blo 1855629 2860337 := bstep (se 2 (by rfl) ⟨1072626, by rfl⟩ : syracuseStep 2860337 = 2145253) B2145253
theorem B20063629 : Blo 1855629 20063629 := bstep (se 3 (by rfl) ⟨3761930, by rfl⟩ : syracuseStep 20063629 = 7523861) B7523861
theorem B4236689 : Blo 1855629 4236689 := bstep (se 2 (by rfl) ⟨1588758, by rfl⟩ : syracuseStep 4236689 = 3177517) B3177517
theorem B25404853 : Blo 1855629 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B6350339 : Blo 1855629 6350339 := bstep (se 1 (by rfl) ⟨4762754, by rfl⟩ : syracuseStep 6350339 = 9525509) B9525509
theorem B4179473 : Blo 1855629 4179473 := bstep (se 2 (by rfl) ⟨1567302, by rfl⟩ : syracuseStep 4179473 = 3134605) B3134605
theorem B4179491 : Blo 1855629 4179491 := bstep (se 1 (by rfl) ⟨3134618, by rfl⟩ : syracuseStep 4179491 = 6269237) B6269237
theorem B13567601 : Blo 1855629 13567601 := bstep (se 2 (by rfl) ⟨5087850, by rfl⟩ : syracuseStep 13567601 = 10175701) B10175701
theorem B2975363 : Blo 1855629 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B6268589 : Blo 1855629 6268589 := bstep (se 3 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 6268589 = 2350721) B2350721
theorem B3524305 : Blo 1855629 3524305 := bstep (se 2 (by rfl) ⟨1321614, by rfl⟩ : syracuseStep 3524305 = 2643229) B2643229
theorem B6268643 : Blo 1855629 6268643 := bstep (se 1 (by rfl) ⟨4701482, by rfl⟩ : syracuseStep 6268643 = 9402965) B9402965
theorem B2975459 : Blo 1855629 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B2975491 : Blo 1855629 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B10577699 : Blo 1855629 10577699 := bstep (se 1 (by rfl) ⟨7933274, by rfl⟩ : syracuseStep 10577699 = 15866549) B15866549
theorem B17835875 : Blo 1855629 17835875 := bstep (se 1 (by rfl) ⟨13376906, by rfl⟩ : syracuseStep 17835875 = 26753813) B26753813
theorem B3524465 : Blo 1855629 3524465 := bstep (se 2 (by rfl) ⟨1321674, by rfl⟩ : syracuseStep 3524465 = 2643349) B2643349
theorem B2508689 : Blo 1855629 2508689 := bstep (se 2 (by rfl) ⟨940758, by rfl⟩ : syracuseStep 2508689 = 1881517) B1881517
theorem B10569635 : Blo 1855629 10569635 := bstep (se 1 (by rfl) ⟨7927226, by rfl⟩ : syracuseStep 10569635 = 15854453) B15854453
theorem B6268913 : Blo 1855629 6268913 := bstep (se 2 (by rfl) ⟨2350842, by rfl⟩ : syracuseStep 6268913 = 4701685) B4701685
theorem B3131473 : Blo 1855629 3131473 := bstep (se 2 (by rfl) ⟨1174302, by rfl⟩ : syracuseStep 3131473 = 2348605) B2348605
theorem B5285969 : Blo 1855629 5285969 := bstep (se 2 (by rfl) ⟨1982238, by rfl⟩ : syracuseStep 5285969 = 3964477) B3964477
theorem B5949521 : Blo 1855629 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B3131507 : Blo 1855629 3131507 := bstep (se 1 (by rfl) ⟨2348630, by rfl⟩ : syracuseStep 3131507 = 4697261) B4697261
theorem B7047395 : Blo 1855629 7047395 := bstep (se 1 (by rfl) ⟨5285546, by rfl⟩ : syracuseStep 7047395 = 10571093) B10571093
theorem B3131635 : Blo 1855629 3131635 := bstep (se 1 (by rfl) ⟨2348726, by rfl⟩ : syracuseStep 3131635 = 4697453) B4697453
theorem B3524867 : Blo 1855629 3524867 := bstep (se 1 (by rfl) ⟨2643650, by rfl⟩ : syracuseStep 3524867 = 5287301) B5287301
theorem B5286161 : Blo 1855629 5286161 := bstep (se 2 (by rfl) ⟨1982310, by rfl⟩ : syracuseStep 5286161 = 3964621) B3964621
theorem B3131777 : Blo 1855629 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B4458883 : Blo 1855629 4458883 := bstep (se 1 (by rfl) ⟨3344162, by rfl⟩ : syracuseStep 4458883 = 6688325) B6688325
theorem B3344803 : Blo 1855629 3344803 := bstep (se 1 (by rfl) ⟨2508602, by rfl⟩ : syracuseStep 3344803 = 5017205) B5017205
theorem B3131905 : Blo 1855629 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B12880397 : Blo 1855629 12880397 := bstep (se 3 (by rfl) ⟨2415074, by rfl⟩ : syracuseStep 12880397 = 4830149) B4830149
theorem B6269453 : Blo 1855629 6269453 := bstep (se 3 (by rfl) ⟨1175522, by rfl⟩ : syracuseStep 6269453 = 2351045) B2351045
theorem B3131939 : Blo 1855629 3131939 := bstep (se 1 (by rfl) ⟨2348954, by rfl⟩ : syracuseStep 3131939 = 4697909) B4697909
theorem B6032017 : Blo 1855629 6032017 := bstep (se 2 (by rfl) ⟨2262006, by rfl⟩ : syracuseStep 6032017 = 4524013) B4524013
theorem B3132067 : Blo 1855629 3132067 := bstep (se 1 (by rfl) ⟨2349050, by rfl⟩ : syracuseStep 3132067 = 4698101) B4698101
theorem B14093027 : Blo 1855629 14093027 := bstep (se 1 (by rfl) ⟨10569770, by rfl⟩ : syracuseStep 14093027 = 21139541) B21139541
theorem B7146211 : Blo 1855629 7146211 := bstep (se 1 (by rfl) ⟨5359658, by rfl⟩ : syracuseStep 7146211 = 10719317) B10719317
theorem B10578701 : Blo 1855629 10578701 := bstep (se 3 (by rfl) ⟨1983506, by rfl⟩ : syracuseStep 10578701 = 3967013) B3967013
theorem B3132209 : Blo 1855629 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B3132337 : Blo 1855629 3132337 := bstep (se 2 (by rfl) ⟨1174626, by rfl⟩ : syracuseStep 3132337 = 2349253) B2349253
theorem B5950417 : Blo 1855629 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B3132371 : Blo 1855629 3132371 := bstep (se 1 (by rfl) ⟨2349278, by rfl⟩ : syracuseStep 3132371 = 4698557) B4698557
theorem B7531505 : Blo 1855629 7531505 := bstep (se 2 (by rfl) ⟨2824314, by rfl⟩ : syracuseStep 7531505 = 5648629) B5648629
theorem B15051845 : Blo 1855629 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B3132499 : Blo 1855629 3132499 := bstep (se 1 (by rfl) ⟨2349374, by rfl⟩ : syracuseStep 3132499 = 4698749) B4698749
theorem B3525763 : Blo 1855629 3525763 := bstep (se 1 (by rfl) ⟨2644322, by rfl⟩ : syracuseStep 3525763 = 5288645) B5288645
theorem B7933069 : Blo 1855629 7933069 := bstep (se 3 (by rfl) ⟨1487450, by rfl⟩ : syracuseStep 7933069 = 2974901) B2974901
theorem B3345553 : Blo 1855629 3345553 := bstep (se 2 (by rfl) ⟨1254582, by rfl⟩ : syracuseStep 3345553 = 2509165) B2509165
theorem B11291825 : Blo 1855629 11291825 := bstep (se 2 (by rfl) ⟨4234434, by rfl⟩ : syracuseStep 11291825 = 8468869) B8468869
theorem B7048397 : Blo 1855629 7048397 := bstep (se 3 (by rfl) ⟨1321574, by rfl⟩ : syracuseStep 7048397 = 2643149) B2643149
theorem B3132641 : Blo 1855629 3132641 := bstep (se 2 (by rfl) ⟨1174740, by rfl⟩ : syracuseStep 3132641 = 2349481) B2349481
theorem B5287153 : Blo 1855629 5287153 := bstep (se 2 (by rfl) ⟨1982682, by rfl⟩ : syracuseStep 5287153 = 3965365) B3965365
theorem B10038563 : Blo 1855629 10038563 := bstep (se 1 (by rfl) ⟨7528922, by rfl⟩ : syracuseStep 10038563 = 15057845) B15057845
theorem B3525923 : Blo 1855629 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B3132769 : Blo 1855629 3132769 := bstep (se 2 (by rfl) ⟨1174788, by rfl⟩ : syracuseStep 3132769 = 2349577) B2349577
theorem B5647715 : Blo 1855629 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B3132803 : Blo 1855629 3132803 := bstep (se 1 (by rfl) ⟨2349602, by rfl⟩ : syracuseStep 3132803 = 4699205) B4699205
theorem B9039281 : Blo 1855629 9039281 := bstep (se 2 (by rfl) ⟨3389730, by rfl⟩ : syracuseStep 9039281 = 6779461) B6779461
theorem B4697585 : Blo 1855629 4697585 := bstep (se 2 (by rfl) ⟨1761594, by rfl⟩ : syracuseStep 4697585 = 3523189) B3523189
theorem B5361137 : Blo 1855629 5361137 := bstep (se 2 (by rfl) ⟨2010426, by rfl⟩ : syracuseStep 5361137 = 4020853) B4020853
theorem B3132931 : Blo 1855629 3132931 := bstep (se 1 (by rfl) ⟨2349698, by rfl⟩ : syracuseStep 3132931 = 4699397) B4699397
theorem B5287427 : Blo 1855629 5287427 := bstep (se 1 (by rfl) ⟨3965570, by rfl⟩ : syracuseStep 5287427 = 7931141) B7931141
theorem B5721617 : Blo 1855629 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B4697635 : Blo 1855629 4697635 := bstep (se 1 (by rfl) ⟨3523226, by rfl⟩ : syracuseStep 4697635 = 7046453) B7046453
theorem B4460113 : Blo 1855629 4460113 := bstep (se 2 (by rfl) ⟨1672542, by rfl⟩ : syracuseStep 4460113 = 3345085) B3345085
theorem B15855203 : Blo 1855629 15855203 := bstep (se 1 (by rfl) ⟨11891402, by rfl⟩ : syracuseStep 15855203 = 23782805) B23782805
theorem B3133073 : Blo 1855629 3133073 := bstep (se 2 (by rfl) ⟨1174902, by rfl⟩ : syracuseStep 3133073 = 2349805) B2349805
theorem B4828817 : Blo 1855629 4828817 := bstep (se 2 (by rfl) ⟨1810806, by rfl⟩ : syracuseStep 4828817 = 3621613) B3621613
theorem B8466083 : Blo 1855629 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B12062371 : Blo 1855629 12062371 := bstep (se 1 (by rfl) ⟨9046778, by rfl⟩ : syracuseStep 12062371 = 18093557) B18093557
theorem B4697777 : Blo 1855629 4697777 := bstep (se 2 (by rfl) ⟨1761666, by rfl⟩ : syracuseStep 4697777 = 3523333) B3523333
theorem B5287619 : Blo 1855629 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B5017315 : Blo 1855629 5017315 := bstep (se 1 (by rfl) ⟨3762986, by rfl⟩ : syracuseStep 5017315 = 7525973) B7525973
theorem B9400049 : Blo 1855629 9400049 := bstep (se 2 (by rfl) ⟨3525018, by rfl⟩ : syracuseStep 9400049 = 7050037) B7050037
theorem B3133201 : Blo 1855629 3133201 := bstep (se 2 (by rfl) ⟨1174950, by rfl⟩ : syracuseStep 3133201 = 2349901) B2349901
theorem B3133235 : Blo 1855629 3133235 := bstep (se 1 (by rfl) ⟨2349926, by rfl⟩ : syracuseStep 3133235 = 4699853) B4699853
theorem B3174241 : Blo 1855629 3174241 := bstep (se 2 (by rfl) ⟨1190340, by rfl⟩ : syracuseStep 3174241 = 2380681) B2380681
theorem B4763537 : Blo 1855629 4763537 := bstep (se 2 (by rfl) ⟨1786326, by rfl⟩ : syracuseStep 4763537 = 3572653) B3572653
theorem B3133363 : Blo 1855629 3133363 := bstep (se 1 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 3133363 = 4700045) B4700045
theorem B11890637 : Blo 1855629 11890637 := bstep (se 3 (by rfl) ⟨2229494, by rfl⟩ : syracuseStep 11890637 = 4458989) B4458989
theorem B3133505 : Blo 1855629 3133505 := bstep (se 2 (by rfl) ⟨1175064, by rfl⟩ : syracuseStep 3133505 = 2350129) B2350129
theorem B6262865 : Blo 1855629 6262865 := bstep (se 2 (by rfl) ⟨2348574, by rfl⟩ : syracuseStep 6262865 = 4697149) B4697149
theorem B10039409 : Blo 1855629 10039409 := bstep (se 2 (by rfl) ⟨3764778, by rfl⟩ : syracuseStep 10039409 = 7529557) B7529557
theorem B1855635 : Blo 1855629 1855635 := bstep (se 1 (by rfl) ⟨1391726, by rfl⟩ : syracuseStep 1855635 = 2783453) B2783453
theorem B1855651 : Blo 1855629 1855651 := bstep (se 1 (by rfl) ⟨1391738, by rfl⟩ : syracuseStep 1855651 = 2783477) B2783477
theorem B1855667 : Blo 1855629 1855667 := bstep (se 1 (by rfl) ⟨1391750, by rfl⟩ : syracuseStep 1855667 = 2783501) B2783501
theorem B3133633 : Blo 1855629 3133633 := bstep (se 2 (by rfl) ⟨1175112, by rfl⟩ : syracuseStep 3133633 = 2350225) B2350225
theorem B1855683 : Blo 1855629 1855683 := bstep (se 1 (by rfl) ⟨1391762, by rfl⟩ : syracuseStep 1855683 = 2783525) B2783525
theorem B1855699 : Blo 1855629 1855699 := bstep (se 1 (by rfl) ⟨1391774, by rfl⟩ : syracuseStep 1855699 = 2783549) B2783549
theorem B1855715 : Blo 1855629 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B3133667 : Blo 1855629 3133667 := bstep (se 1 (by rfl) ⟨2350250, by rfl⟩ : syracuseStep 3133667 = 4700501) B4700501
theorem B1855731 : Blo 1855629 1855731 := bstep (se 1 (by rfl) ⟨1391798, by rfl⟩ : syracuseStep 1855731 = 2783597) B2783597
theorem B1855747 : Blo 1855629 1855747 := bstep (se 1 (by rfl) ⟨1391810, by rfl⟩ : syracuseStep 1855747 = 2783621) B2783621
theorem B1855763 : Blo 1855629 1855763 := bstep (se 1 (by rfl) ⟨1391822, by rfl⟩ : syracuseStep 1855763 = 2783645) B2783645
theorem B1855779 : Blo 1855629 1855779 := bstep (se 1 (by rfl) ⟨1391834, by rfl⟩ : syracuseStep 1855779 = 2783669) B2783669
theorem B1855795 : Blo 1855629 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B48238901 : Blo 1855629 48238901 := bstep (se 5 (by rfl) ⟨2261198, by rfl⟩ : syracuseStep 48238901 = 4522397) B4522397
theorem B1855811 : Blo 1855629 1855811 := bstep (se 1 (by rfl) ⟨1391858, by rfl⟩ : syracuseStep 1855811 = 2783717) B2783717
theorem B1855827 : Blo 1855629 1855827 := bstep (se 1 (by rfl) ⟨1391870, by rfl⟩ : syracuseStep 1855827 = 2783741) B2783741
theorem B2822483 : Blo 1855629 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B1855843 : Blo 1855629 1855843 := bstep (se 1 (by rfl) ⟨1391882, by rfl⟩ : syracuseStep 1855843 = 2783765) B2783765
theorem B19050851 : Blo 1855629 19050851 := bstep (se 1 (by rfl) ⟨14288138, by rfl⟩ : syracuseStep 19050851 = 28576277) B28576277
theorem B3133795 : Blo 1855629 3133795 := bstep (se 1 (by rfl) ⟨2350346, by rfl⟩ : syracuseStep 3133795 = 4700693) B4700693
theorem B1855859 : Blo 1855629 1855859 := bstep (se 1 (by rfl) ⟨1391894, by rfl⟩ : syracuseStep 1855859 = 2783789) B2783789
theorem B1855875 : Blo 1855629 1855875 := bstep (se 1 (by rfl) ⟨1391906, by rfl⟩ : syracuseStep 1855875 = 2783813) B2783813
theorem B2822531 : Blo 1855629 2822531 := bstep (se 1 (by rfl) ⟨2116898, by rfl⟩ : syracuseStep 2822531 = 4233797) B4233797
theorem B1855891 : Blo 1855629 1855891 := bstep (se 1 (by rfl) ⟨1391918, by rfl⟩ : syracuseStep 1855891 = 2783837) B2783837
theorem B1855907 : Blo 1855629 1855907 := bstep (se 1 (by rfl) ⟨1391930, by rfl⟩ : syracuseStep 1855907 = 2783861) B2783861
theorem B3764657 : Blo 1855629 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B1855923 : Blo 1855629 1855923 := bstep (se 1 (by rfl) ⟨1391942, by rfl⟩ : syracuseStep 1855923 = 2783885) B2783885
theorem B1855939 : Blo 1855629 1855939 := bstep (se 1 (by rfl) ⟨1391954, by rfl⟩ : syracuseStep 1855939 = 2783909) B2783909
theorem B1855955 : Blo 1855629 1855955 := bstep (se 1 (by rfl) ⟨1391966, by rfl⟩ : syracuseStep 1855955 = 2783933) B2783933
theorem B1855971 : Blo 1855629 1855971 := bstep (se 1 (by rfl) ⟨1391978, by rfl⟩ : syracuseStep 1855971 = 2783957) B2783957
theorem B5288429 : Blo 1855629 5288429 := bstep (se 3 (by rfl) ⟨991580, by rfl⟩ : syracuseStep 5288429 = 1983161) B1983161
theorem B3133937 : Blo 1855629 3133937 := bstep (se 2 (by rfl) ⟨1175226, by rfl⟩ : syracuseStep 3133937 = 2350453) B2350453
theorem B1855987 : Blo 1855629 1855987 := bstep (se 1 (by rfl) ⟨1391990, by rfl⟩ : syracuseStep 1855987 = 2783981) B2783981
theorem B1856003 : Blo 1855629 1856003 := bstep (se 1 (by rfl) ⟨1392002, by rfl⟩ : syracuseStep 1856003 = 2784005) B2784005
theorem B1856019 : Blo 1855629 1856019 := bstep (se 1 (by rfl) ⟨1392014, by rfl⟩ : syracuseStep 1856019 = 2784029) B2784029
theorem B1856035 : Blo 1855629 1856035 := bstep (se 1 (by rfl) ⟨1392026, by rfl⟩ : syracuseStep 1856035 = 2784053) B2784053
theorem B8917553 : Blo 1855629 8917553 := bstep (se 2 (by rfl) ⟨3344082, by rfl⟩ : syracuseStep 8917553 = 6688165) B6688165
theorem B2642483 : Blo 1855629 2642483 := bstep (se 1 (by rfl) ⟨1981862, by rfl⟩ : syracuseStep 2642483 = 3963725) B3963725
theorem B1856051 : Blo 1855629 1856051 := bstep (se 1 (by rfl) ⟨1392038, by rfl⟩ : syracuseStep 1856051 = 2784077) B2784077
theorem B1856067 : Blo 1855629 1856067 := bstep (se 1 (by rfl) ⟨1392050, by rfl⟩ : syracuseStep 1856067 = 2784101) B2784101
theorem B1856083 : Blo 1855629 1856083 := bstep (se 1 (by rfl) ⟨1392062, by rfl⟩ : syracuseStep 1856083 = 2784125) B2784125
theorem B1856099 : Blo 1855629 1856099 := bstep (se 1 (by rfl) ⟨1392074, by rfl⟩ : syracuseStep 1856099 = 2784149) B2784149
theorem B6263405 : Blo 1855629 6263405 := bstep (se 3 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 6263405 = 2348777) B2348777
theorem B3134065 : Blo 1855629 3134065 := bstep (se 2 (by rfl) ⟨1175274, by rfl⟩ : syracuseStep 3134065 = 2350549) B2350549
theorem B1856115 : Blo 1855629 1856115 := bstep (se 1 (by rfl) ⟨1392086, by rfl⟩ : syracuseStep 1856115 = 2784173) B2784173
theorem B1856131 : Blo 1855629 1856131 := bstep (se 1 (by rfl) ⟨1392098, by rfl⟩ : syracuseStep 1856131 = 2784197) B2784197
theorem B4698769 : Blo 1855629 4698769 := bstep (se 2 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 4698769 = 3524077) B3524077
theorem B1856147 : Blo 1855629 1856147 := bstep (se 1 (by rfl) ⟨1392110, by rfl⟩ : syracuseStep 1856147 = 2784221) B2784221
theorem B3134099 : Blo 1855629 3134099 := bstep (se 1 (by rfl) ⟨2350574, by rfl⟩ : syracuseStep 3134099 = 4701149) B4701149
theorem B6263459 : Blo 1855629 6263459 := bstep (se 1 (by rfl) ⟨4697594, by rfl⟩ : syracuseStep 6263459 = 9395189) B9395189
theorem B1856163 : Blo 1855629 1856163 := bstep (se 1 (by rfl) ⟨1392122, by rfl⟩ : syracuseStep 1856163 = 2784245) B2784245
theorem B5288611 : Blo 1855629 5288611 := bstep (se 1 (by rfl) ⟨3966458, by rfl⟩ : syracuseStep 5288611 = 7932917) B7932917
theorem B1856179 : Blo 1855629 1856179 := bstep (se 1 (by rfl) ⟨1392134, by rfl⟩ : syracuseStep 1856179 = 2784269) B2784269
theorem B1856195 : Blo 1855629 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1856211 : Blo 1855629 1856211 := bstep (se 1 (by rfl) ⟨1392158, by rfl⟩ : syracuseStep 1856211 = 2784317) B2784317
theorem B1856227 : Blo 1855629 1856227 := bstep (se 1 (by rfl) ⟨1392170, by rfl⟩ : syracuseStep 1856227 = 2784341) B2784341
theorem B1856243 : Blo 1855629 1856243 := bstep (se 1 (by rfl) ⟨1392182, by rfl⟩ : syracuseStep 1856243 = 2784365) B2784365
theorem B1856259 : Blo 1855629 1856259 := bstep (se 1 (by rfl) ⟨1392194, by rfl⟩ : syracuseStep 1856259 = 2784389) B2784389
theorem B1856275 : Blo 1855629 1856275 := bstep (se 1 (by rfl) ⟨1392206, by rfl⟩ : syracuseStep 1856275 = 2784413) B2784413
theorem B3134227 : Blo 1855629 3134227 := bstep (se 1 (by rfl) ⟨2350670, by rfl⟩ : syracuseStep 3134227 = 4701341) B4701341
theorem B1856291 : Blo 1855629 1856291 := bstep (se 1 (by rfl) ⟨1392218, by rfl⟩ : syracuseStep 1856291 = 2784437) B2784437
theorem B1856307 : Blo 1855629 1856307 := bstep (se 1 (by rfl) ⟨1392230, by rfl⟩ : syracuseStep 1856307 = 2784461) B2784461
theorem B1856323 : Blo 1855629 1856323 := bstep (se 1 (by rfl) ⟨1392242, by rfl⟩ : syracuseStep 1856323 = 2784485) B2784485
theorem B1856339 : Blo 1855629 1856339 := bstep (se 1 (by rfl) ⟨1392254, by rfl⟩ : syracuseStep 1856339 = 2784509) B2784509
theorem B1856355 : Blo 1855629 1856355 := bstep (se 1 (by rfl) ⟨1392266, by rfl⟩ : syracuseStep 1856355 = 2784533) B2784533
theorem B1856371 : Blo 1855629 1856371 := bstep (se 1 (by rfl) ⟨1392278, by rfl⟩ : syracuseStep 1856371 = 2784557) B2784557
theorem B1856387 : Blo 1855629 1856387 := bstep (se 1 (by rfl) ⟨1392290, by rfl⟩ : syracuseStep 1856387 = 2784581) B2784581
theorem B1856403 : Blo 1855629 1856403 := bstep (se 1 (by rfl) ⟨1392302, by rfl⟩ : syracuseStep 1856403 = 2784605) B2784605
theorem B3134369 : Blo 1855629 3134369 := bstep (se 2 (by rfl) ⟨1175388, by rfl⟩ : syracuseStep 3134369 = 2350777) B2350777
theorem B4699043 : Blo 1855629 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1856419 : Blo 1855629 1856419 := bstep (se 1 (by rfl) ⟨1392314, by rfl⟩ : syracuseStep 1856419 = 2784629) B2784629
theorem B6263729 : Blo 1855629 6263729 := bstep (se 2 (by rfl) ⟨2348898, by rfl⟩ : syracuseStep 6263729 = 4697797) B4697797
theorem B1856435 : Blo 1855629 1856435 := bstep (se 1 (by rfl) ⟨1392326, by rfl⟩ : syracuseStep 1856435 = 2784653) B2784653
theorem B1856451 : Blo 1855629 1856451 := bstep (se 1 (by rfl) ⟨1392338, by rfl⟩ : syracuseStep 1856451 = 2784677) B2784677
theorem B1856467 : Blo 1855629 1856467 := bstep (se 1 (by rfl) ⟨1392350, by rfl⟩ : syracuseStep 1856467 = 2784701) B2784701
theorem B1856483 : Blo 1855629 1856483 := bstep (se 1 (by rfl) ⟨1392362, by rfl⟩ : syracuseStep 1856483 = 2784725) B2784725
theorem B1856499 : Blo 1855629 1856499 := bstep (se 1 (by rfl) ⟨1392374, by rfl⟩ : syracuseStep 1856499 = 2784749) B2784749
theorem B1856515 : Blo 1855629 1856515 := bstep (se 1 (by rfl) ⟨1392386, by rfl⟩ : syracuseStep 1856515 = 2784773) B2784773
theorem B1856531 : Blo 1855629 1856531 := bstep (se 1 (by rfl) ⟨1392398, by rfl⟩ : syracuseStep 1856531 = 2784797) B2784797
theorem B3134497 : Blo 1855629 3134497 := bstep (se 2 (by rfl) ⟨1175436, by rfl⟩ : syracuseStep 3134497 = 2350873) B2350873
theorem B1856547 : Blo 1855629 1856547 := bstep (se 1 (by rfl) ⟨1392410, by rfl⟩ : syracuseStep 1856547 = 2784821) B2784821
theorem B1856563 : Blo 1855629 1856563 := bstep (se 1 (by rfl) ⟨1392422, by rfl⟩ : syracuseStep 1856563 = 2784845) B2784845
theorem B1856579 : Blo 1855629 1856579 := bstep (se 1 (by rfl) ⟨1392434, by rfl⟩ : syracuseStep 1856579 = 2784869) B2784869
theorem B3134531 : Blo 1855629 3134531 := bstep (se 1 (by rfl) ⟨2350898, by rfl⟩ : syracuseStep 3134531 = 4701797) B4701797
theorem B10572869 : Blo 1855629 10572869 := bstep (se 4 (by rfl) ⟨991206, by rfl⟩ : syracuseStep 10572869 = 1982413) B1982413
theorem B1856595 : Blo 1855629 1856595 := bstep (se 1 (by rfl) ⟨1392446, by rfl⟩ : syracuseStep 1856595 = 2784893) B2784893
theorem B4699235 : Blo 1855629 4699235 := bstep (se 1 (by rfl) ⟨3524426, by rfl⟩ : syracuseStep 4699235 = 7048853) B7048853
theorem B1856611 : Blo 1855629 1856611 := bstep (se 1 (by rfl) ⟨1392458, by rfl⟩ : syracuseStep 1856611 = 2784917) B2784917
theorem B1856627 : Blo 1855629 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B1856643 : Blo 1855629 1856643 := bstep (se 1 (by rfl) ⟨1392482, by rfl⟩ : syracuseStep 1856643 = 2784965) B2784965
theorem B5289101 : Blo 1855629 5289101 := bstep (se 3 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 5289101 = 1983413) B1983413
theorem B1856659 : Blo 1855629 1856659 := bstep (se 1 (by rfl) ⟨1392494, by rfl⟩ : syracuseStep 1856659 = 2784989) B2784989
theorem B1856675 : Blo 1855629 1856675 := bstep (se 1 (by rfl) ⟨1392506, by rfl⟩ : syracuseStep 1856675 = 2785013) B2785013
theorem B9401507 : Blo 1855629 9401507 := bstep (se 1 (by rfl) ⟨7051130, by rfl⟩ : syracuseStep 9401507 = 14102261) B14102261
theorem B2643121 : Blo 1855629 2643121 := bstep (se 2 (by rfl) ⟨991170, by rfl⟩ : syracuseStep 2643121 = 1982341) B1982341
theorem B1856691 : Blo 1855629 1856691 := bstep (se 1 (by rfl) ⟨1392518, by rfl⟩ : syracuseStep 1856691 = 2785037) B2785037
theorem B1856707 : Blo 1855629 1856707 := bstep (se 1 (by rfl) ⟨1392530, by rfl⟩ : syracuseStep 1856707 = 2785061) B2785061
theorem B3134659 : Blo 1855629 3134659 := bstep (se 1 (by rfl) ⟨2350994, by rfl⟩ : syracuseStep 3134659 = 4701989) B4701989
theorem B1856723 : Blo 1855629 1856723 := bstep (se 1 (by rfl) ⟨1392542, by rfl⟩ : syracuseStep 1856723 = 2785085) B2785085
theorem B1856739 : Blo 1855629 1856739 := bstep (se 1 (by rfl) ⟨1392554, by rfl⟩ : syracuseStep 1856739 = 2785109) B2785109
theorem B1856755 : Blo 1855629 1856755 := bstep (se 1 (by rfl) ⟨1392566, by rfl⟩ : syracuseStep 1856755 = 2785133) B2785133
theorem B1856771 : Blo 1855629 1856771 := bstep (se 1 (by rfl) ⟨1392578, by rfl⟩ : syracuseStep 1856771 = 2785157) B2785157
theorem B7050509 : Blo 1855629 7050509 := bstep (se 3 (by rfl) ⟨1321970, by rfl⟩ : syracuseStep 7050509 = 2643941) B2643941
theorem B1856787 : Blo 1855629 1856787 := bstep (se 1 (by rfl) ⟨1392590, by rfl⟩ : syracuseStep 1856787 = 2785181) B2785181
theorem B1856803 : Blo 1855629 1856803 := bstep (se 1 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 1856803 = 2785205) B2785205
theorem B1856819 : Blo 1855629 1856819 := bstep (se 1 (by rfl) ⟨1392614, by rfl⟩ : syracuseStep 1856819 = 2785229) B2785229
theorem B4175171 : Blo 1855629 4175171 := bstep (se 1 (by rfl) ⟨3131378, by rfl⟩ : syracuseStep 4175171 = 6262757) B6262757
theorem B1856835 : Blo 1855629 1856835 := bstep (se 1 (by rfl) ⟨1392626, by rfl⟩ : syracuseStep 1856835 = 2785253) B2785253
theorem B1856851 : Blo 1855629 1856851 := bstep (se 1 (by rfl) ⟨1392638, by rfl⟩ : syracuseStep 1856851 = 2785277) B2785277
theorem B1856867 : Blo 1855629 1856867 := bstep (se 1 (by rfl) ⟨1392650, by rfl⟩ : syracuseStep 1856867 = 2785301) B2785301
theorem B1856883 : Blo 1855629 1856883 := bstep (se 1 (by rfl) ⟨1392662, by rfl⟩ : syracuseStep 1856883 = 2785325) B2785325
theorem B1856899 : Blo 1855629 1856899 := bstep (se 1 (by rfl) ⟨1392674, by rfl⟩ : syracuseStep 1856899 = 2785349) B2785349
theorem B6968717 : Blo 1855629 6968717 := bstep (se 3 (by rfl) ⟨1306634, by rfl⟩ : syracuseStep 6968717 = 2613269) B2613269
theorem B1856915 : Blo 1855629 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B1856931 : Blo 1855629 1856931 := bstep (se 1 (by rfl) ⟨1392698, by rfl⟩ : syracuseStep 1856931 = 2785397) B2785397
theorem B1856947 : Blo 1855629 1856947 := bstep (se 1 (by rfl) ⟨1392710, by rfl⟩ : syracuseStep 1856947 = 2785421) B2785421
theorem B1856963 : Blo 1855629 1856963 := bstep (se 1 (by rfl) ⟨1392722, by rfl⟩ : syracuseStep 1856963 = 2785445) B2785445
theorem B6264269 : Blo 1855629 6264269 := bstep (se 3 (by rfl) ⟨1174550, by rfl⟩ : syracuseStep 6264269 = 2349101) B2349101
theorem B5658065 : Blo 1855629 5658065 := bstep (se 2 (by rfl) ⟨2121774, by rfl⟩ : syracuseStep 5658065 = 4243549) B4243549
theorem B1856979 : Blo 1855629 1856979 := bstep (se 1 (by rfl) ⟨1392734, by rfl⟩ : syracuseStep 1856979 = 2785469) B2785469
theorem B1856995 : Blo 1855629 1856995 := bstep (se 1 (by rfl) ⟨1392746, by rfl⟩ : syracuseStep 1856995 = 2785493) B2785493
theorem B1857011 : Blo 1855629 1857011 := bstep (se 1 (by rfl) ⟨1392758, by rfl⟩ : syracuseStep 1857011 = 2785517) B2785517
theorem B2643457 : Blo 1855629 2643457 := bstep (se 2 (by rfl) ⟨991296, by rfl⟩ : syracuseStep 2643457 = 1982593) B1982593
theorem B6264323 : Blo 1855629 6264323 := bstep (se 1 (by rfl) ⟨4698242, by rfl⟩ : syracuseStep 6264323 = 9396485) B9396485
theorem B1857027 : Blo 1855629 1857027 := bstep (se 1 (by rfl) ⟨1392770, by rfl⟩ : syracuseStep 1857027 = 2785541) B2785541
theorem B10573325 : Blo 1855629 10573325 := bstep (se 3 (by rfl) ⟨1982498, by rfl⟩ : syracuseStep 10573325 = 3964997) B3964997
theorem B1857043 : Blo 1855629 1857043 := bstep (se 1 (by rfl) ⟨1392782, by rfl⟩ : syracuseStep 1857043 = 2785565) B2785565
theorem B1857059 : Blo 1855629 1857059 := bstep (se 1 (by rfl) ⟨1392794, by rfl⟩ : syracuseStep 1857059 = 2785589) B2785589
theorem B1857075 : Blo 1855629 1857075 := bstep (se 1 (by rfl) ⟨1392806, by rfl⟩ : syracuseStep 1857075 = 2785613) B2785613
theorem B1857091 : Blo 1855629 1857091 := bstep (se 1 (by rfl) ⟨1392818, by rfl⟩ : syracuseStep 1857091 = 2785637) B2785637
theorem B4175441 : Blo 1855629 4175441 := bstep (se 2 (by rfl) ⟨1565790, by rfl⟩ : syracuseStep 4175441 = 3131581) B3131581
theorem B1857107 : Blo 1855629 1857107 := bstep (se 1 (by rfl) ⟨1392830, by rfl⟩ : syracuseStep 1857107 = 2785661) B2785661
theorem B4175459 : Blo 1855629 4175459 := bstep (se 1 (by rfl) ⟨3131594, by rfl⟩ : syracuseStep 4175459 = 6263189) B6263189
theorem B1857123 : Blo 1855629 1857123 := bstep (se 1 (by rfl) ⟨1392842, by rfl⟩ : syracuseStep 1857123 = 2785685) B2785685
theorem B1857139 : Blo 1855629 1857139 := bstep (se 1 (by rfl) ⟨1392854, by rfl⟩ : syracuseStep 1857139 = 2785709) B2785709
theorem B1857155 : Blo 1855629 1857155 := bstep (se 1 (by rfl) ⟨1392866, by rfl⟩ : syracuseStep 1857155 = 2785733) B2785733
theorem B14104205 : Blo 1855629 14104205 := bstep (se 3 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 14104205 = 5289077) B5289077
theorem B1857171 : Blo 1855629 1857171 := bstep (se 1 (by rfl) ⟨1392878, by rfl⟩ : syracuseStep 1857171 = 2785757) B2785757
theorem B1857187 : Blo 1855629 1857187 := bstep (se 1 (by rfl) ⟨1392890, by rfl⟩ : syracuseStep 1857187 = 2785781) B2785781
theorem B1857203 : Blo 1855629 1857203 := bstep (se 1 (by rfl) ⟨1392902, by rfl⟩ : syracuseStep 1857203 = 2785805) B2785805
theorem B1857219 : Blo 1855629 1857219 := bstep (se 1 (by rfl) ⟨1392914, by rfl⟩ : syracuseStep 1857219 = 2785829) B2785829
theorem B1857235 : Blo 1855629 1857235 := bstep (se 1 (by rfl) ⟨1392926, by rfl⟩ : syracuseStep 1857235 = 2785853) B2785853
theorem B1857251 : Blo 1855629 1857251 := bstep (se 1 (by rfl) ⟨1392938, by rfl⟩ : syracuseStep 1857251 = 2785877) B2785877
theorem B1857267 : Blo 1855629 1857267 := bstep (se 1 (by rfl) ⟨1392950, by rfl⟩ : syracuseStep 1857267 = 2785901) B2785901
theorem B1857283 : Blo 1855629 1857283 := bstep (se 1 (by rfl) ⟨1392962, by rfl⟩ : syracuseStep 1857283 = 2785925) B2785925
theorem B6264593 : Blo 1855629 6264593 := bstep (se 2 (by rfl) ⟨2349222, by rfl⟩ : syracuseStep 6264593 = 4698445) B4698445
theorem B1857299 : Blo 1855629 1857299 := bstep (se 1 (by rfl) ⟨1392974, by rfl⟩ : syracuseStep 1857299 = 2785949) B2785949
theorem B1857315 : Blo 1855629 1857315 := bstep (se 1 (by rfl) ⟨1392986, by rfl⟩ : syracuseStep 1857315 = 2785973) B2785973
theorem B1857331 : Blo 1855629 1857331 := bstep (se 1 (by rfl) ⟨1392998, by rfl⟩ : syracuseStep 1857331 = 2785997) B2785997
theorem B1857347 : Blo 1855629 1857347 := bstep (se 1 (by rfl) ⟨1393010, by rfl⟩ : syracuseStep 1857347 = 2786021) B2786021
theorem B1857363 : Blo 1855629 1857363 := bstep (se 1 (by rfl) ⟨1393022, by rfl⟩ : syracuseStep 1857363 = 2786045) B2786045
theorem B1857379 : Blo 1855629 1857379 := bstep (se 1 (by rfl) ⟨1393034, by rfl⟩ : syracuseStep 1857379 = 2786069) B2786069
theorem B4175729 : Blo 1855629 4175729 := bstep (se 2 (by rfl) ⟨1565898, by rfl⟩ : syracuseStep 4175729 = 3131797) B3131797
theorem B1857395 : Blo 1855629 1857395 := bstep (se 1 (by rfl) ⟨1393046, by rfl⟩ : syracuseStep 1857395 = 2786093) B2786093
theorem B4175747 : Blo 1855629 4175747 := bstep (se 1 (by rfl) ⟨3131810, by rfl⟩ : syracuseStep 4175747 = 6263621) B6263621
theorem B1857411 : Blo 1855629 1857411 := bstep (se 1 (by rfl) ⟨1393058, by rfl⟩ : syracuseStep 1857411 = 2786117) B2786117
theorem B16078733 : Blo 1855629 16078733 := bstep (se 3 (by rfl) ⟨3014762, by rfl⟩ : syracuseStep 16078733 = 6029525) B6029525
theorem B1857427 : Blo 1855629 1857427 := bstep (se 1 (by rfl) ⟨1393070, by rfl⟩ : syracuseStep 1857427 = 2786141) B2786141
theorem B1857443 : Blo 1855629 1857443 := bstep (se 1 (by rfl) ⟨1393082, by rfl⟩ : syracuseStep 1857443 = 2786165) B2786165
theorem B1857459 : Blo 1855629 1857459 := bstep (se 1 (by rfl) ⟨1393094, by rfl⟩ : syracuseStep 1857459 = 2786189) B2786189
theorem B2348995 : Blo 1855629 2348995 := bstep (se 1 (by rfl) ⟨1761746, by rfl⟩ : syracuseStep 2348995 = 3523493) B3523493
theorem B1857475 : Blo 1855629 1857475 := bstep (se 1 (by rfl) ⟨1393106, by rfl⟩ : syracuseStep 1857475 = 2786213) B2786213
theorem B9402317 : Blo 1855629 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B1857491 : Blo 1855629 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B1857507 : Blo 1855629 1857507 := bstep (se 1 (by rfl) ⟨1393130, by rfl⟩ : syracuseStep 1857507 = 2786261) B2786261
theorem B32610275 : Blo 1855629 32610275 := bstep (se 1 (by rfl) ⟨24457706, by rfl⟩ : syracuseStep 32610275 = 48915413) B48915413
theorem B1857523 : Blo 1855629 1857523 := bstep (se 1 (by rfl) ⟨1393142, by rfl⟩ : syracuseStep 1857523 = 2786285) B2786285
theorem B1857539 : Blo 1855629 1857539 := bstep (se 1 (by rfl) ⟨1393154, by rfl⟩ : syracuseStep 1857539 = 2786309) B2786309
theorem B4700177 : Blo 1855629 4700177 := bstep (se 2 (by rfl) ⟨1762566, by rfl⟩ : syracuseStep 4700177 = 3525133) B3525133
theorem B47593493 : Blo 1855629 47593493 := bstep (se 6 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 47593493 = 2230945) B2230945
theorem B1857555 : Blo 1855629 1857555 := bstep (se 1 (by rfl) ⟨1393166, by rfl⟩ : syracuseStep 1857555 = 2786333) B2786333
theorem B2349091 : Blo 1855629 2349091 := bstep (se 1 (by rfl) ⟨1761818, by rfl⟩ : syracuseStep 2349091 = 3523637) B3523637
theorem B1857571 : Blo 1855629 1857571 := bstep (se 1 (by rfl) ⟨1393178, by rfl⟩ : syracuseStep 1857571 = 2786357) B2786357
theorem B7051313 : Blo 1855629 7051313 := bstep (se 2 (by rfl) ⟨2644242, by rfl⟩ : syracuseStep 7051313 = 5288485) B5288485
theorem B1857587 : Blo 1855629 1857587 := bstep (se 1 (by rfl) ⟨1393190, by rfl⟩ : syracuseStep 1857587 = 2786381) B2786381
theorem B4700227 : Blo 1855629 4700227 := bstep (se 1 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 4700227 = 7050341) B7050341
theorem B1857603 : Blo 1855629 1857603 := bstep (se 1 (by rfl) ⟨1393202, by rfl⟩ : syracuseStep 1857603 = 2786405) B2786405
theorem B2644049 : Blo 1855629 2644049 := bstep (se 2 (by rfl) ⟨991518, by rfl⟩ : syracuseStep 2644049 = 1983037) B1983037
theorem B1857619 : Blo 1855629 1857619 := bstep (se 1 (by rfl) ⟨1393214, by rfl⟩ : syracuseStep 1857619 = 2786429) B2786429
theorem B4176017 : Blo 1855629 4176017 := bstep (se 2 (by rfl) ⟨1566006, by rfl⟩ : syracuseStep 4176017 = 3132013) B3132013
theorem B4176035 : Blo 1855629 4176035 := bstep (se 1 (by rfl) ⟨3132026, by rfl⟩ : syracuseStep 4176035 = 6264053) B6264053
theorem B4700369 : Blo 1855629 4700369 := bstep (se 2 (by rfl) ⟨1762638, by rfl⟩ : syracuseStep 4700369 = 3525277) B3525277
theorem B2824417 : Blo 1855629 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B2783459 : Blo 1855629 2783459 := bstep (se 1 (by rfl) ⟨2087594, by rfl⟩ : syracuseStep 2783459 = 4175189) B4175189
theorem B2783489 : Blo 1855629 2783489 := bstep (se 2 (by rfl) ⟨1043808, by rfl⟩ : syracuseStep 2783489 = 2087617) B2087617
theorem B2783507 : Blo 1855629 2783507 := bstep (se 1 (by rfl) ⟨2087630, by rfl⟩ : syracuseStep 2783507 = 4175261) B4175261
theorem B6265133 : Blo 1855629 6265133 := bstep (se 3 (by rfl) ⟨1174712, by rfl⟩ : syracuseStep 6265133 = 2349425) B2349425
theorem B2783537 : Blo 1855629 2783537 := bstep (se 2 (by rfl) ⟨1043826, by rfl⟩ : syracuseStep 2783537 = 2087653) B2087653
theorem B2783555 : Blo 1855629 2783555 := bstep (se 1 (by rfl) ⟨2087666, by rfl⟩ : syracuseStep 2783555 = 4175333) B4175333
theorem B13375813 : Blo 1855629 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B10041677 : Blo 1855629 10041677 := bstep (se 3 (by rfl) ⟨1882814, by rfl⟩ : syracuseStep 10041677 = 3765629) B3765629
theorem B2783585 : Blo 1855629 2783585 := bstep (se 2 (by rfl) ⟨1043844, by rfl⟩ : syracuseStep 2783585 = 2087689) B2087689
theorem B6265187 : Blo 1855629 6265187 := bstep (se 1 (by rfl) ⟨4698890, by rfl⟩ : syracuseStep 6265187 = 9397781) B9397781
theorem B2783603 : Blo 1855629 2783603 := bstep (se 1 (by rfl) ⟨2087702, by rfl⟩ : syracuseStep 2783603 = 4175405) B4175405
theorem B2783633 : Blo 1855629 2783633 := bstep (se 2 (by rfl) ⟨1043862, by rfl⟩ : syracuseStep 2783633 = 2087725) B2087725
theorem B2783651 : Blo 1855629 2783651 := bstep (se 1 (by rfl) ⟨2087738, by rfl⟩ : syracuseStep 2783651 = 4175477) B4175477
theorem B4176305 : Blo 1855629 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B2783681 : Blo 1855629 2783681 := bstep (se 2 (by rfl) ⟨1043880, by rfl⟩ : syracuseStep 2783681 = 2087761) B2087761
theorem B4176323 : Blo 1855629 4176323 := bstep (se 1 (by rfl) ⟨3132242, by rfl⟩ : syracuseStep 4176323 = 6264485) B6264485
theorem B2783699 : Blo 1855629 2783699 := bstep (se 1 (by rfl) ⟨2087774, by rfl⟩ : syracuseStep 2783699 = 4175549) B4175549
theorem B2783729 : Blo 1855629 2783729 := bstep (se 2 (by rfl) ⟨1043898, by rfl⟩ : syracuseStep 2783729 = 2087797) B2087797
theorem B2783747 : Blo 1855629 2783747 := bstep (se 1 (by rfl) ⟨2087810, by rfl⟩ : syracuseStep 2783747 = 4175621) B4175621
theorem B2349587 : Blo 1855629 2349587 := bstep (se 1 (by rfl) ⟨1762190, by rfl⟩ : syracuseStep 2349587 = 3524381) B3524381
theorem B2783777 : Blo 1855629 2783777 := bstep (se 2 (by rfl) ⟨1043916, by rfl⟩ : syracuseStep 2783777 = 2087833) B2087833
theorem B2783795 : Blo 1855629 2783795 := bstep (se 1 (by rfl) ⟨2087846, by rfl⟩ : syracuseStep 2783795 = 4175693) B4175693
theorem B8919629 : Blo 1855629 8919629 := bstep (se 3 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 8919629 = 3344861) B3344861
theorem B2783825 : Blo 1855629 2783825 := bstep (se 2 (by rfl) ⟨1043934, by rfl⟩ : syracuseStep 2783825 = 2087869) B2087869
theorem B2783843 : Blo 1855629 2783843 := bstep (se 1 (by rfl) ⟨2087882, by rfl⟩ : syracuseStep 2783843 = 4175765) B4175765
theorem B2644579 : Blo 1855629 2644579 := bstep (se 1 (by rfl) ⟨1983434, by rfl⟩ : syracuseStep 2644579 = 3966869) B3966869
theorem B6265457 : Blo 1855629 6265457 := bstep (se 2 (by rfl) ⟨2349546, by rfl⟩ : syracuseStep 6265457 = 4699093) B4699093
theorem B2783873 : Blo 1855629 2783873 := bstep (se 2 (by rfl) ⟨1043952, by rfl⟩ : syracuseStep 2783873 = 2087905) B2087905
theorem B2783891 : Blo 1855629 2783891 := bstep (se 1 (by rfl) ⟨2087918, by rfl⟩ : syracuseStep 2783891 = 4175837) B4175837
theorem B5724845 : Blo 1855629 5724845 := bstep (se 3 (by rfl) ⟨1073408, by rfl⟩ : syracuseStep 5724845 = 2146817) B2146817
theorem B9394865 : Blo 1855629 9394865 := bstep (se 2 (by rfl) ⟨3523074, by rfl⟩ : syracuseStep 9394865 = 7046149) B7046149
theorem B2783921 : Blo 1855629 2783921 := bstep (se 2 (by rfl) ⟨1043970, by rfl⟩ : syracuseStep 2783921 = 2087941) B2087941
theorem B2783939 : Blo 1855629 2783939 := bstep (se 1 (by rfl) ⟨2087954, by rfl⟩ : syracuseStep 2783939 = 4175909) B4175909
theorem B5946061 : Blo 1855629 5946061 := bstep (se 3 (by rfl) ⟨1114886, by rfl⟩ : syracuseStep 5946061 = 2229773) B2229773
theorem B7051981 : Blo 1855629 7051981 := bstep (se 3 (by rfl) ⟨1322246, by rfl⟩ : syracuseStep 7051981 = 2644493) B2644493
theorem B4176593 : Blo 1855629 4176593 := bstep (se 2 (by rfl) ⟨1566222, by rfl⟩ : syracuseStep 4176593 = 3132445) B3132445
theorem B2087635 : Blo 1855629 2087635 := bstep (se 1 (by rfl) ⟨1565726, by rfl⟩ : syracuseStep 2087635 = 3131453) B3131453
theorem B2783969 : Blo 1855629 2783969 := bstep (se 2 (by rfl) ⟨1043988, by rfl⟩ : syracuseStep 2783969 = 2087977) B2087977
theorem B4176611 : Blo 1855629 4176611 := bstep (se 1 (by rfl) ⟨3132458, by rfl⟩ : syracuseStep 4176611 = 6264917) B6264917
theorem B2783987 : Blo 1855629 2783987 := bstep (se 1 (by rfl) ⟨2087990, by rfl⟩ : syracuseStep 2783987 = 4175981) B4175981
theorem B2784017 : Blo 1855629 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B2784035 : Blo 1855629 2784035 := bstep (se 1 (by rfl) ⟨2088026, by rfl⟩ : syracuseStep 2784035 = 4176053) B4176053
theorem B2972467 : Blo 1855629 2972467 := bstep (se 1 (by rfl) ⟨2229350, by rfl⟩ : syracuseStep 2972467 = 4458701) B4458701
theorem B2784065 : Blo 1855629 2784065 := bstep (se 2 (by rfl) ⟨1044024, by rfl⟩ : syracuseStep 2784065 = 2088049) B2088049
theorem B2784083 : Blo 1855629 2784083 := bstep (se 1 (by rfl) ⟨2088062, by rfl⟩ : syracuseStep 2784083 = 4176125) B4176125
theorem B2087779 : Blo 1855629 2087779 := bstep (se 1 (by rfl) ⟨1565834, by rfl⟩ : syracuseStep 2087779 = 3131669) B3131669
theorem B2784113 : Blo 1855629 2784113 := bstep (se 2 (by rfl) ⟨1044042, by rfl⟩ : syracuseStep 2784113 = 2088085) B2088085
theorem B2784131 : Blo 1855629 2784131 := bstep (se 1 (by rfl) ⟨2088098, by rfl⟩ : syracuseStep 2784131 = 4176197) B4176197
theorem B2784161 : Blo 1855629 2784161 := bstep (se 2 (by rfl) ⟨1044060, by rfl⟩ : syracuseStep 2784161 = 2088121) B2088121
theorem B2784179 : Blo 1855629 2784179 := bstep (se 1 (by rfl) ⟨2088134, by rfl⟩ : syracuseStep 2784179 = 4176269) B4176269
theorem B2644915 : Blo 1855629 2644915 := bstep (se 1 (by rfl) ⟨1983686, by rfl⟩ : syracuseStep 2644915 = 3967373) B3967373
theorem B2784209 : Blo 1855629 2784209 := bstep (se 2 (by rfl) ⟨1044078, by rfl⟩ : syracuseStep 2784209 = 2088157) B2088157
theorem B2784227 : Blo 1855629 2784227 := bstep (se 1 (by rfl) ⟨2088170, by rfl⟩ : syracuseStep 2784227 = 4176341) B4176341
theorem B4176881 : Blo 1855629 4176881 := bstep (se 2 (by rfl) ⟨1566330, by rfl⟩ : syracuseStep 4176881 = 3132661) B3132661
theorem B2087923 : Blo 1855629 2087923 := bstep (se 1 (by rfl) ⟨1565942, by rfl⟩ : syracuseStep 2087923 = 3131885) B3131885
theorem B2382835 : Blo 1855629 2382835 := bstep (se 1 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 2382835 = 3574253) B3574253
theorem B2784257 : Blo 1855629 2784257 := bstep (se 2 (by rfl) ⟨1044096, by rfl⟩ : syracuseStep 2784257 = 2088193) B2088193
theorem B4176899 : Blo 1855629 4176899 := bstep (se 1 (by rfl) ⟨3132674, by rfl⟩ : syracuseStep 4176899 = 6265349) B6265349
theorem B2784275 : Blo 1855629 2784275 := bstep (se 1 (by rfl) ⟨2088206, by rfl⟩ : syracuseStep 2784275 = 4176413) B4176413
theorem B7928867 : Blo 1855629 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B2784305 : Blo 1855629 2784305 := bstep (se 2 (by rfl) ⟨1044114, by rfl⟩ : syracuseStep 2784305 = 2088229) B2088229
theorem B2784323 : Blo 1855629 2784323 := bstep (se 1 (by rfl) ⟨2088242, by rfl⟩ : syracuseStep 2784323 = 4176485) B4176485
theorem B5356621 : Blo 1855629 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B2784353 : Blo 1855629 2784353 := bstep (se 2 (by rfl) ⟨1044132, by rfl⟩ : syracuseStep 2784353 = 2088265) B2088265
theorem B2784371 : Blo 1855629 2784371 := bstep (se 1 (by rfl) ⟨2088278, by rfl⟩ : syracuseStep 2784371 = 4176557) B4176557
theorem B2088067 : Blo 1855629 2088067 := bstep (se 1 (by rfl) ⟨1566050, by rfl⟩ : syracuseStep 2088067 = 3132101) B3132101
theorem B6265997 : Blo 1855629 6265997 := bstep (se 3 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 6265997 = 2349749) B2349749
theorem B2784401 : Blo 1855629 2784401 := bstep (se 2 (by rfl) ⟨1044150, by rfl⟩ : syracuseStep 2784401 = 2088301) B2088301
theorem B2784419 : Blo 1855629 2784419 := bstep (se 1 (by rfl) ⟨2088314, by rfl⟩ : syracuseStep 2784419 = 4176629) B4176629
theorem B4701361 : Blo 1855629 4701361 := bstep (se 2 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 4701361 = 3526021) B3526021
theorem B2784449 : Blo 1855629 2784449 := bstep (se 2 (by rfl) ⟨1044168, by rfl⟩ : syracuseStep 2784449 = 2088337) B2088337
theorem B6266051 : Blo 1855629 6266051 := bstep (se 1 (by rfl) ⟨4699538, by rfl⟩ : syracuseStep 6266051 = 9399077) B9399077
theorem B2784467 : Blo 1855629 2784467 := bstep (se 1 (by rfl) ⟨2088350, by rfl⟩ : syracuseStep 2784467 = 4176701) B4176701
theorem B2350291 : Blo 1855629 2350291 := bstep (se 1 (by rfl) ⟨1762718, by rfl⟩ : syracuseStep 2350291 = 3525437) B3525437
theorem B2784497 : Blo 1855629 2784497 := bstep (se 2 (by rfl) ⟨1044186, by rfl⟩ : syracuseStep 2784497 = 2088373) B2088373
theorem B2784515 : Blo 1855629 2784515 := bstep (se 1 (by rfl) ⟨2088386, by rfl⟩ : syracuseStep 2784515 = 4176773) B4176773
theorem B3964177 : Blo 1855629 3964177 := bstep (se 2 (by rfl) ⟨1486566, by rfl⟩ : syracuseStep 3964177 = 2973133) B2973133
theorem B4177169 : Blo 1855629 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B2088211 : Blo 1855629 2088211 := bstep (se 1 (by rfl) ⟨1566158, by rfl⟩ : syracuseStep 2088211 = 3132317) B3132317
theorem B2784545 : Blo 1855629 2784545 := bstep (se 2 (by rfl) ⟨1044204, by rfl⟩ : syracuseStep 2784545 = 2088409) B2088409
theorem B4177187 : Blo 1855629 4177187 := bstep (se 1 (by rfl) ⟨3132890, by rfl⟩ : syracuseStep 4177187 = 6265781) B6265781
theorem B1981747 : Blo 1855629 1981747 := bstep (se 1 (by rfl) ⟨1486310, by rfl⟩ : syracuseStep 1981747 = 2972621) B2972621
theorem B2784563 : Blo 1855629 2784563 := bstep (se 1 (by rfl) ⟨2088422, by rfl⟩ : syracuseStep 2784563 = 4176845) B4176845
theorem B2350387 : Blo 1855629 2350387 := bstep (se 1 (by rfl) ⟨1762790, by rfl⟩ : syracuseStep 2350387 = 3525581) B3525581
theorem B2784593 : Blo 1855629 2784593 := bstep (se 2 (by rfl) ⟨1044222, by rfl⟩ : syracuseStep 2784593 = 2088445) B2088445
theorem B3013985 : Blo 1855629 3013985 := bstep (se 2 (by rfl) ⟨1130244, by rfl⟩ : syracuseStep 3013985 = 2260489) B2260489
theorem B2784611 : Blo 1855629 2784611 := bstep (se 1 (by rfl) ⟨2088458, by rfl⟩ : syracuseStep 2784611 = 4176917) B4176917
theorem B2784641 : Blo 1855629 2784641 := bstep (se 2 (by rfl) ⟨1044240, by rfl⟩ : syracuseStep 2784641 = 2088481) B2088481
theorem B2784659 : Blo 1855629 2784659 := bstep (se 1 (by rfl) ⟨2088494, by rfl⟩ : syracuseStep 2784659 = 4176989) B4176989
theorem B2088355 : Blo 1855629 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B2784689 : Blo 1855629 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B2784707 : Blo 1855629 2784707 := bstep (se 1 (by rfl) ⟨2088530, by rfl⟩ : syracuseStep 2784707 = 4177061) B4177061
theorem B4701635 : Blo 1855629 4701635 := bstep (se 1 (by rfl) ⟨3526226, by rfl⟩ : syracuseStep 4701635 = 7052453) B7052453
theorem B57187781 : Blo 1855629 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B6266321 : Blo 1855629 6266321 := bstep (se 2 (by rfl) ⟨2349870, by rfl⟩ : syracuseStep 6266321 = 4699741) B4699741
theorem B2784737 : Blo 1855629 2784737 := bstep (se 2 (by rfl) ⟨1044276, by rfl⟩ : syracuseStep 2784737 = 2088553) B2088553
theorem B7052771 : Blo 1855629 7052771 := bstep (se 1 (by rfl) ⟨5289578, by rfl⟩ : syracuseStep 7052771 = 10579157) B10579157
theorem B2784755 : Blo 1855629 2784755 := bstep (se 1 (by rfl) ⟨2088566, by rfl⟩ : syracuseStep 2784755 = 4177133) B4177133
theorem B2784785 : Blo 1855629 2784785 := bstep (se 2 (by rfl) ⟨1044294, by rfl⟩ : syracuseStep 2784785 = 2088589) B2088589
theorem B2784803 : Blo 1855629 2784803 := bstep (se 1 (by rfl) ⟨2088602, by rfl⟩ : syracuseStep 2784803 = 4177205) B4177205
theorem B4177457 : Blo 1855629 4177457 := bstep (se 2 (by rfl) ⟨1566546, by rfl⟩ : syracuseStep 4177457 = 3133093) B3133093
theorem B1982003 : Blo 1855629 1982003 := bstep (se 1 (by rfl) ⟨1486502, by rfl⟩ : syracuseStep 1982003 = 2973005) B2973005
theorem B2088499 : Blo 1855629 2088499 := bstep (se 1 (by rfl) ⟨1566374, by rfl⟩ : syracuseStep 2088499 = 3132749) B3132749
theorem B2784833 : Blo 1855629 2784833 := bstep (se 2 (by rfl) ⟨1044312, by rfl⟩ : syracuseStep 2784833 = 2088625) B2088625
theorem B4177475 : Blo 1855629 4177475 := bstep (se 1 (by rfl) ⟨3133106, by rfl⟩ : syracuseStep 4177475 = 6266213) B6266213
theorem B2784851 : Blo 1855629 2784851 := bstep (se 1 (by rfl) ⟨2088638, by rfl⟩ : syracuseStep 2784851 = 4177277) B4177277
theorem B3014243 : Blo 1855629 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B2784881 : Blo 1855629 2784881 := bstep (se 2 (by rfl) ⟨1044330, by rfl⟩ : syracuseStep 2784881 = 2088661) B2088661
theorem B7528049 : Blo 1855629 7528049 := bstep (se 2 (by rfl) ⟨2823018, by rfl⟩ : syracuseStep 7528049 = 5646037) B5646037
theorem B16940657 : Blo 1855629 16940657 := bstep (se 2 (by rfl) ⟨6352746, by rfl⟩ : syracuseStep 16940657 = 12705493) B12705493
theorem B2481779 : Blo 1855629 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B2784899 : Blo 1855629 2784899 := bstep (se 1 (by rfl) ⟨2088674, by rfl⟩ : syracuseStep 2784899 = 4177349) B4177349
theorem B4701827 : Blo 1855629 4701827 := bstep (se 1 (by rfl) ⟨3526370, by rfl⟩ : syracuseStep 4701827 = 7052741) B7052741
theorem B2784929 : Blo 1855629 2784929 := bstep (se 2 (by rfl) ⟨1044348, by rfl⟩ : syracuseStep 2784929 = 2088697) B2088697
theorem B2784947 : Blo 1855629 2784947 := bstep (se 1 (by rfl) ⟨2088710, by rfl⟩ : syracuseStep 2784947 = 4177421) B4177421
theorem B2088643 : Blo 1855629 2088643 := bstep (se 1 (by rfl) ⟨1566482, by rfl⟩ : syracuseStep 2088643 = 3132965) B3132965
theorem B2784977 : Blo 1855629 2784977 := bstep (se 2 (by rfl) ⟨1044366, by rfl⟩ : syracuseStep 2784977 = 2088733) B2088733
theorem B2784995 : Blo 1855629 2784995 := bstep (se 1 (by rfl) ⟨2088746, by rfl⟩ : syracuseStep 2784995 = 4177493) B4177493
theorem B2785025 : Blo 1855629 2785025 := bstep (se 2 (by rfl) ⟨1044384, by rfl⟩ : syracuseStep 2785025 = 2088769) B2088769
theorem B2785043 : Blo 1855629 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B2350883 : Blo 1855629 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B2785073 : Blo 1855629 2785073 := bstep (se 2 (by rfl) ⟨1044402, by rfl⟩ : syracuseStep 2785073 = 2088805) B2088805
theorem B2785091 : Blo 1855629 2785091 := bstep (se 1 (by rfl) ⟨2088818, by rfl⟩ : syracuseStep 2785091 = 4177637) B4177637
theorem B4177745 : Blo 1855629 4177745 := bstep (se 2 (by rfl) ⟨1566654, by rfl⟩ : syracuseStep 4177745 = 3133309) B3133309
theorem B2088787 : Blo 1855629 2088787 := bstep (se 1 (by rfl) ⟨1566590, by rfl⟩ : syracuseStep 2088787 = 3133181) B3133181
theorem B2785121 : Blo 1855629 2785121 := bstep (se 2 (by rfl) ⟨1044420, by rfl⟩ : syracuseStep 2785121 = 2088841) B2088841
theorem B4177763 : Blo 1855629 4177763 := bstep (se 1 (by rfl) ⟨3133322, by rfl⟩ : syracuseStep 4177763 = 6266645) B6266645
theorem B2785139 : Blo 1855629 2785139 := bstep (se 1 (by rfl) ⟨2088854, by rfl⟩ : syracuseStep 2785139 = 4177709) B4177709
theorem B2785169 : Blo 1855629 2785169 := bstep (se 2 (by rfl) ⟨1044438, by rfl⟩ : syracuseStep 2785169 = 2088877) B2088877
theorem B2785187 : Blo 1855629 2785187 := bstep (se 1 (by rfl) ⟨2088890, by rfl⟩ : syracuseStep 2785187 = 4177781) B4177781
theorem B11288497 : Blo 1855629 11288497 := bstep (se 2 (by rfl) ⟨4233186, by rfl⟩ : syracuseStep 11288497 = 8466373) B8466373
theorem B2785217 : Blo 1855629 2785217 := bstep (se 2 (by rfl) ⟨1044456, by rfl⟩ : syracuseStep 2785217 = 2088913) B2088913
theorem B4235203 : Blo 1855629 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B14098373 : Blo 1855629 14098373 := bstep (se 4 (by rfl) ⟨1321722, by rfl⟩ : syracuseStep 14098373 = 2643445) B2643445
theorem B2785235 : Blo 1855629 2785235 := bstep (se 1 (by rfl) ⟨2088926, by rfl⟩ : syracuseStep 2785235 = 4177853) B4177853
theorem B2088931 : Blo 1855629 2088931 := bstep (se 1 (by rfl) ⟨1566698, by rfl⟩ : syracuseStep 2088931 = 3133397) B3133397
theorem B6266861 : Blo 1855629 6266861 := bstep (se 3 (by rfl) ⟨1175036, by rfl⟩ : syracuseStep 6266861 = 2350073) B2350073
theorem B2785265 : Blo 1855629 2785265 := bstep (se 2 (by rfl) ⟨1044474, by rfl⟩ : syracuseStep 2785265 = 2088949) B2088949
theorem B4177943 : Blo 1855629 4177943 := bstep (se 1 (by rfl) ⟨3133457, by rfl⟩ : syracuseStep 4177943 = 6266915) B6266915
theorem B2089003 : Blo 1855629 2089003 := bstep (se 1 (by rfl) ⟨1566752, by rfl⟩ : syracuseStep 2089003 = 3133505) B3133505
theorem B2785355 : Blo 1855629 2785355 := bstep (se 1 (by rfl) ⟨2089016, by rfl⟩ : syracuseStep 2785355 = 4178033) B4178033
theorem B6692939 : Blo 1855629 6692939 := bstep (se 1 (by rfl) ⟨5019704, by rfl⟩ : syracuseStep 6692939 = 10039409) B10039409
theorem B2785367 : Blo 1855629 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B6266969 : Blo 1855629 6266969 := bstep (se 2 (by rfl) ⟨2350113, by rfl⟩ : syracuseStep 6266969 = 4700227) B4700227
theorem B2089111 : Blo 1855629 2089111 := bstep (se 1 (by rfl) ⟨1566833, by rfl⟩ : syracuseStep 2089111 = 3133667) B3133667
theorem B2785433 : Blo 1855629 2785433 := bstep (se 2 (by rfl) ⟨1044537, by rfl⟩ : syracuseStep 2785433 = 2089075) B2089075
theorem B4178123 : Blo 1855629 4178123 := bstep (se 1 (by rfl) ⟨3133592, by rfl⟩ : syracuseStep 4178123 = 6267185) B6267185
theorem B4178177 : Blo 1855629 4178177 := bstep (se 2 (by rfl) ⟨1566816, by rfl⟩ : syracuseStep 4178177 = 3133633) B3133633
theorem B2785547 : Blo 1855629 2785547 := bstep (se 1 (by rfl) ⟨2089160, by rfl⟩ : syracuseStep 2785547 = 4178321) B4178321
theorem B2785559 : Blo 1855629 2785559 := bstep (se 1 (by rfl) ⟨2089169, by rfl⟩ : syracuseStep 2785559 = 4178339) B4178339
theorem B13386019 : Blo 1855629 13386019 := bstep (se 1 (by rfl) ⟨10039514, by rfl⟩ : syracuseStep 13386019 = 20079029) B20079029
theorem B2089291 : Blo 1855629 2089291 := bstep (se 1 (by rfl) ⟨1566968, by rfl⟩ : syracuseStep 2089291 = 3133937) B3133937
theorem B2785625 : Blo 1855629 2785625 := bstep (se 2 (by rfl) ⟨1044609, by rfl⟩ : syracuseStep 2785625 = 2089219) B2089219
theorem B17834417 : Blo 1855629 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B2089399 : Blo 1855629 2089399 := bstep (se 1 (by rfl) ⟨1567049, by rfl⟩ : syracuseStep 2089399 = 3134099) B3134099
theorem B6029761 : Blo 1855629 6029761 := bstep (se 2 (by rfl) ⟨2261160, by rfl⟩ : syracuseStep 6029761 = 4522321) B4522321
theorem B2785739 : Blo 1855629 2785739 := bstep (se 1 (by rfl) ⟨2089304, by rfl⟩ : syracuseStep 2785739 = 4178609) B4178609
theorem B2785751 : Blo 1855629 2785751 := bstep (se 1 (by rfl) ⟨2089313, by rfl⟩ : syracuseStep 2785751 = 4178627) B4178627
theorem B4178393 : Blo 1855629 4178393 := bstep (se 2 (by rfl) ⟨1566897, by rfl⟩ : syracuseStep 4178393 = 3133795) B3133795
theorem B3965441 : Blo 1855629 3965441 := bstep (se 2 (by rfl) ⟨1487040, by rfl⟩ : syracuseStep 3965441 = 2974081) B2974081
theorem B7045649 : Blo 1855629 7045649 := bstep (se 2 (by rfl) ⟨2642118, by rfl⟩ : syracuseStep 7045649 = 5284237) B5284237
theorem B2785817 : Blo 1855629 2785817 := bstep (se 2 (by rfl) ⟨1044681, by rfl⟩ : syracuseStep 2785817 = 2089363) B2089363
theorem B4178483 : Blo 1855629 4178483 := bstep (se 1 (by rfl) ⟨3133862, by rfl⟩ : syracuseStep 4178483 = 6267725) B6267725
theorem B3965527 : Blo 1855629 3965527 := bstep (se 1 (by rfl) ⟨2974145, by rfl⟩ : syracuseStep 3965527 = 5948291) B5948291
theorem B4178519 : Blo 1855629 4178519 := bstep (se 1 (by rfl) ⟨3133889, by rfl⟩ : syracuseStep 4178519 = 6267779) B6267779
theorem B7930457 : Blo 1855629 7930457 := bstep (se 2 (by rfl) ⟨2973921, by rfl⟩ : syracuseStep 7930457 = 5947843) B5947843
theorem B2089579 : Blo 1855629 2089579 := bstep (se 1 (by rfl) ⟨1567184, by rfl⟩ : syracuseStep 2089579 = 3134369) B3134369
theorem B2785931 : Blo 1855629 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B2785943 : Blo 1855629 2785943 := bstep (se 1 (by rfl) ⟨2089457, by rfl⟩ : syracuseStep 2785943 = 4178915) B4178915
theorem B7930541 : Blo 1855629 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B2089687 : Blo 1855629 2089687 := bstep (se 1 (by rfl) ⟨1567265, by rfl⟩ : syracuseStep 2089687 = 3134531) B3134531
theorem B2786009 : Blo 1855629 2786009 := bstep (se 2 (by rfl) ⟨1044753, by rfl⟩ : syracuseStep 2786009 = 2089507) B2089507
theorem B17842949 : Blo 1855629 17842949 := bstep (se 4 (by rfl) ⟨1672776, by rfl⟩ : syracuseStep 17842949 = 3345553) B3345553
theorem B4178699 : Blo 1855629 4178699 := bstep (se 1 (by rfl) ⟨3134024, by rfl⟩ : syracuseStep 4178699 = 6268049) B6268049
theorem B6267671 : Blo 1855629 6267671 := bstep (se 1 (by rfl) ⟨4700753, by rfl⟩ : syracuseStep 6267671 = 9401507) B9401507
theorem B7627565 : Blo 1855629 7627565 := bstep (se 3 (by rfl) ⟨1430168, by rfl⟩ : syracuseStep 7627565 = 2860337) B2860337
theorem B4178753 : Blo 1855629 4178753 := bstep (se 2 (by rfl) ⟨1567032, by rfl⟩ : syracuseStep 4178753 = 3134065) B3134065
theorem B2786123 : Blo 1855629 2786123 := bstep (se 1 (by rfl) ⟨2089592, by rfl⟩ : syracuseStep 2786123 = 4179185) B4179185
theorem B2786135 : Blo 1855629 2786135 := bstep (se 1 (by rfl) ⟨2089601, by rfl⟩ : syracuseStep 2786135 = 4179203) B4179203
theorem B2786201 : Blo 1855629 2786201 := bstep (se 2 (by rfl) ⟨1044825, by rfl⟩ : syracuseStep 2786201 = 2089651) B2089651
theorem B4645811 : Blo 1855629 4645811 := bstep (se 1 (by rfl) ⟨3484358, by rfl⟩ : syracuseStep 4645811 = 6968717) B6968717
theorem B9528281 : Blo 1855629 9528281 := bstep (se 2 (by rfl) ⟨3573105, by rfl⟩ : syracuseStep 9528281 = 7146211) B7146211
theorem B2786315 : Blo 1855629 2786315 := bstep (se 1 (by rfl) ⟨2089736, by rfl⟩ : syracuseStep 2786315 = 4179473) B4179473
theorem B2786327 : Blo 1855629 2786327 := bstep (se 1 (by rfl) ⟨2089745, by rfl⟩ : syracuseStep 2786327 = 4179491) B4179491
theorem B3572761 : Blo 1855629 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B4178969 : Blo 1855629 4178969 := bstep (se 2 (by rfl) ⟨1567113, by rfl⟩ : syracuseStep 4178969 = 3134227) B3134227
theorem B11297837 : Blo 1855629 11297837 := bstep (se 3 (by rfl) ⟨2118344, by rfl⟩ : syracuseStep 11297837 = 4236689) B4236689
theorem B9045067 : Blo 1855629 9045067 := bstep (se 1 (by rfl) ⟨6783800, by rfl⟩ : syracuseStep 9045067 = 13567601) B13567601
theorem B1983575 : Blo 1855629 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B2786393 : Blo 1855629 2786393 := bstep (se 2 (by rfl) ⟨1044897, by rfl⟩ : syracuseStep 2786393 = 2089795) B2089795
theorem B4179059 : Blo 1855629 4179059 := bstep (se 1 (by rfl) ⟨3134294, by rfl⟩ : syracuseStep 4179059 = 6268589) B6268589
theorem B4179095 : Blo 1855629 4179095 := bstep (se 1 (by rfl) ⟨3134321, by rfl⟩ : syracuseStep 4179095 = 6268643) B6268643
theorem B7046423 : Blo 1855629 7046423 := bstep (se 1 (by rfl) ⟨5284817, by rfl⟩ : syracuseStep 7046423 = 10569635) B10569635
theorem B6268211 : Blo 1855629 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B4179275 : Blo 1855629 4179275 := bstep (se 1 (by rfl) ⟨3134456, by rfl⟩ : syracuseStep 4179275 = 6268913) B6268913
theorem B31728995 : Blo 1855629 31728995 := bstep (se 1 (by rfl) ⟨23796746, by rfl⟩ : syracuseStep 31728995 = 47593493) B47593493
theorem B4179329 : Blo 1855629 4179329 := bstep (se 2 (by rfl) ⟨1567248, by rfl⟩ : syracuseStep 4179329 = 3134497) B3134497
theorem B3523979 : Blo 1855629 3523979 := bstep (se 1 (by rfl) ⟨2642984, by rfl⟩ : syracuseStep 3523979 = 5285969) B5285969
theorem B3966347 : Blo 1855629 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B7046621 : Blo 1855629 7046621 := bstep (se 3 (by rfl) ⟨1321241, by rfl⟩ : syracuseStep 7046621 = 2642483) B2642483
theorem B5285341 : Blo 1855629 5285341 := bstep (se 3 (by rfl) ⟨991001, by rfl⟩ : syracuseStep 5285341 = 1982003) B1982003
theorem B10577425 : Blo 1855629 10577425 := bstep (se 2 (by rfl) ⟨3966534, by rfl⟩ : syracuseStep 10577425 = 7933069) B7933069
theorem B6694451 : Blo 1855629 6694451 := bstep (se 1 (by rfl) ⟨5020838, by rfl⟩ : syracuseStep 6694451 = 10041677) B10041677
theorem B3524161 : Blo 1855629 3524161 := bstep (se 2 (by rfl) ⟨1321560, by rfl⟩ : syracuseStep 3524161 = 2643121) B2643121
theorem B6268481 : Blo 1855629 6268481 := bstep (se 2 (by rfl) ⟨2350680, by rfl⟩ : syracuseStep 6268481 = 4701361) B4701361
theorem B4179545 : Blo 1855629 4179545 := bstep (se 2 (by rfl) ⟨1567329, by rfl⟩ : syracuseStep 4179545 = 3134659) B3134659
theorem B4179635 : Blo 1855629 4179635 := bstep (se 1 (by rfl) ⟨3134726, by rfl⟩ : syracuseStep 4179635 = 6269453) B6269453
theorem B5285569 : Blo 1855629 5285569 := bstep (se 2 (by rfl) ⟨1982088, by rfl⟩ : syracuseStep 5285569 = 3964177) B3964177
theorem B14100317 : Blo 1855629 14100317 := bstep (se 3 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 14100317 = 5287619) B5287619
theorem B3524609 : Blo 1855629 3524609 := bstep (se 2 (by rfl) ⟨1321728, by rfl⟩ : syracuseStep 3524609 = 2643457) B2643457
theorem B5285911 : Blo 1855629 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B6269021 : Blo 1855629 6269021 := bstep (se 3 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 6269021 = 2350883) B2350883
theorem B16083161 : Blo 1855629 16083161 := bstep (se 2 (by rfl) ⟨6031185, by rfl⟩ : syracuseStep 16083161 = 12062371) B12062371
theorem B2009323 : Blo 1855629 2009323 := bstep (se 1 (by rfl) ⟨1506992, by rfl⟩ : syracuseStep 2009323 = 3013985) B3013985
theorem B3131723 : Blo 1855629 3131723 := bstep (se 1 (by rfl) ⟨2348792, by rfl⟩ : syracuseStep 3131723 = 4697585) B4697585
theorem B3574091 : Blo 1855629 3574091 := bstep (se 1 (by rfl) ⟨2680568, by rfl⟩ : syracuseStep 3574091 = 5361137) B5361137
theorem B3524951 : Blo 1855629 3524951 := bstep (se 1 (by rfl) ⟨2643713, by rfl⟩ : syracuseStep 3524951 = 5287427) B5287427
theorem B3967321 : Blo 1855629 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B10570135 : Blo 1855629 10570135 := bstep (se 1 (by rfl) ⟨7927601, by rfl⟩ : syracuseStep 10570135 = 15855203) B15855203
theorem B2009495 : Blo 1855629 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B3131851 : Blo 1855629 3131851 := bstep (se 1 (by rfl) ⟨2348888, by rfl⟩ : syracuseStep 3131851 = 4697777) B4697777
theorem B15051329 : Blo 1855629 15051329 := bstep (se 2 (by rfl) ⟨5644248, by rfl⟩ : syracuseStep 15051329 = 11288497) B11288497
theorem B3131993 : Blo 1855629 3131993 := bstep (se 2 (by rfl) ⟨1174497, by rfl⟩ : syracuseStep 3131993 = 2348995) B2348995
theorem B5646937 : Blo 1855629 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B9398915 : Blo 1855629 9398915 := bstep (se 1 (by rfl) ⟨7049186, by rfl⟩ : syracuseStep 9398915 = 14098373) B14098373
theorem B3132121 : Blo 1855629 3132121 := bstep (se 2 (by rfl) ⟨1174545, by rfl⟩ : syracuseStep 3132121 = 2349091) B2349091
theorem B5286617 : Blo 1855629 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B12061541 : Blo 1855629 12061541 := bstep (se 4 (by rfl) ⟨1130769, by rfl⟩ : syracuseStep 12061541 = 2261539) B2261539
theorem B12700567 : Blo 1855629 12700567 := bstep (se 1 (by rfl) ⟨9525425, by rfl⟩ : syracuseStep 12700567 = 19050851) B19050851
theorem B2509771 : Blo 1855629 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B3525619 : Blo 1855629 3525619 := bstep (se 1 (by rfl) ⟨2644214, by rfl⟩ : syracuseStep 3525619 = 5288429) B5288429
theorem B28568645 : Blo 1855629 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B4697291 : Blo 1855629 4697291 := bstep (se 1 (by rfl) ⟨3522968, by rfl⟩ : syracuseStep 4697291 = 7045937) B7045937
theorem B3132695 : Blo 1855629 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B7048579 : Blo 1855629 7048579 := bstep (se 1 (by rfl) ⟨5286434, by rfl⟩ : syracuseStep 7048579 = 10572869) B10572869
theorem B3132823 : Blo 1855629 3132823 := bstep (se 1 (by rfl) ⟨2349617, by rfl⟩ : syracuseStep 3132823 = 4699235) B4699235
theorem B8465843 : Blo 1855629 8465843 := bstep (se 1 (by rfl) ⟨6349382, by rfl⟩ : syracuseStep 8465843 = 12698765) B12698765
theorem B3526067 : Blo 1855629 3526067 := bstep (se 1 (by rfl) ⟨2644550, by rfl⟩ : syracuseStep 3526067 = 5289101) B5289101
theorem B3526105 : Blo 1855629 3526105 := bstep (se 2 (by rfl) ⟨1322289, by rfl⟩ : syracuseStep 3526105 = 2644579) B2644579
theorem B3772043 : Blo 1855629 3772043 := bstep (se 1 (by rfl) ⟨2829032, by rfl⟩ : syracuseStep 3772043 = 5658065) B5658065
theorem B7048883 : Blo 1855629 7048883 := bstep (se 1 (by rfl) ⟨5286662, by rfl⟩ : syracuseStep 7048883 = 10573325) B10573325
theorem B24104749 : Blo 1855629 24104749 := bstep (se 3 (by rfl) ⟨4519640, by rfl⟩ : syracuseStep 24104749 = 9039281) B9039281
theorem B11890583 : Blo 1855629 11890583 := bstep (se 1 (by rfl) ⟨8917937, by rfl⟩ : syracuseStep 11890583 = 17835875) B17835875
theorem B3526553 : Blo 1855629 3526553 := bstep (se 2 (by rfl) ⟨1322457, by rfl⟩ : syracuseStep 3526553 = 2644915) B2644915
theorem B10719155 : Blo 1855629 10719155 := bstep (se 1 (by rfl) ⟨8039366, by rfl⟩ : syracuseStep 10719155 = 16078733) B16078733
theorem B7933889 : Blo 1855629 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B3133451 : Blo 1855629 3133451 := bstep (se 1 (by rfl) ⟨2350088, by rfl⟩ : syracuseStep 3133451 = 4700177) B4700177
theorem B3133579 : Blo 1855629 3133579 := bstep (se 1 (by rfl) ⟨2350184, by rfl⟩ : syracuseStep 3133579 = 4700369) B4700369
theorem B1855639 : Blo 1855629 1855639 := bstep (se 1 (by rfl) ⟨1391729, by rfl⟩ : syracuseStep 1855639 = 2783459) B2783459
theorem B4698263 : Blo 1855629 4698263 := bstep (se 1 (by rfl) ⟨3523697, by rfl⟩ : syracuseStep 4698263 = 7047395) B7047395
theorem B1855659 : Blo 1855629 1855659 := bstep (se 1 (by rfl) ⟨1391744, by rfl⟩ : syracuseStep 1855659 = 2783489) B2783489
theorem B1855671 : Blo 1855629 1855671 := bstep (se 1 (by rfl) ⟨1391753, by rfl⟩ : syracuseStep 1855671 = 2783507) B2783507
theorem B1855691 : Blo 1855629 1855691 := bstep (se 1 (by rfl) ⟨1391768, by rfl⟩ : syracuseStep 1855691 = 2783537) B2783537
theorem B1855703 : Blo 1855629 1855703 := bstep (se 1 (by rfl) ⟨1391777, by rfl⟩ : syracuseStep 1855703 = 2783555) B2783555
theorem B1855723 : Blo 1855629 1855723 := bstep (se 1 (by rfl) ⟨1391792, by rfl⟩ : syracuseStep 1855723 = 2783585) B2783585
theorem B1855735 : Blo 1855629 1855735 := bstep (se 1 (by rfl) ⟨1391801, by rfl⟩ : syracuseStep 1855735 = 2783603) B2783603
theorem B1855755 : Blo 1855629 1855755 := bstep (se 1 (by rfl) ⟨1391816, by rfl⟩ : syracuseStep 1855755 = 2783633) B2783633
theorem B1855767 : Blo 1855629 1855767 := bstep (se 1 (by rfl) ⟨1391825, by rfl⟩ : syracuseStep 1855767 = 2783651) B2783651
theorem B3133721 : Blo 1855629 3133721 := bstep (se 2 (by rfl) ⟨1175145, by rfl⟩ : syracuseStep 3133721 = 2350291) B2350291
theorem B1855787 : Blo 1855629 1855787 := bstep (se 1 (by rfl) ⟨1391840, by rfl⟩ : syracuseStep 1855787 = 2783681) B2783681
theorem B1855799 : Blo 1855629 1855799 := bstep (se 1 (by rfl) ⟨1391849, by rfl⟩ : syracuseStep 1855799 = 2783699) B2783699
theorem B7049537 : Blo 1855629 7049537 := bstep (se 2 (by rfl) ⟨2643576, by rfl⟩ : syracuseStep 7049537 = 5287153) B5287153
theorem B5288257 : Blo 1855629 5288257 := bstep (se 2 (by rfl) ⟨1983096, by rfl⟩ : syracuseStep 5288257 = 3966193) B3966193
theorem B1855819 : Blo 1855629 1855819 := bstep (se 1 (by rfl) ⟨1391864, by rfl⟩ : syracuseStep 1855819 = 2783729) B2783729
theorem B1855831 : Blo 1855629 1855831 := bstep (se 1 (by rfl) ⟨1391873, by rfl⟩ : syracuseStep 1855831 = 2783747) B2783747
theorem B1855851 : Blo 1855629 1855851 := bstep (se 1 (by rfl) ⟨1391888, by rfl⟩ : syracuseStep 1855851 = 2783777) B2783777
theorem B1855863 : Blo 1855629 1855863 := bstep (se 1 (by rfl) ⟨1391897, by rfl⟩ : syracuseStep 1855863 = 2783795) B2783795
theorem B1855883 : Blo 1855629 1855883 := bstep (se 1 (by rfl) ⟨1391912, by rfl⟩ : syracuseStep 1855883 = 2783825) B2783825
theorem B1855895 : Blo 1855629 1855895 := bstep (se 1 (by rfl) ⟨1391921, by rfl⟩ : syracuseStep 1855895 = 2783843) B2783843
theorem B2642329 : Blo 1855629 2642329 := bstep (se 2 (by rfl) ⟨990873, by rfl⟩ : syracuseStep 2642329 = 1981747) B1981747
theorem B3133849 : Blo 1855629 3133849 := bstep (se 2 (by rfl) ⟨1175193, by rfl⟩ : syracuseStep 3133849 = 2350387) B2350387
theorem B1855915 : Blo 1855629 1855915 := bstep (se 1 (by rfl) ⟨1391936, by rfl⟩ : syracuseStep 1855915 = 2783873) B2783873
theorem B1855927 : Blo 1855629 1855927 := bstep (se 1 (by rfl) ⟨1391945, by rfl⟩ : syracuseStep 1855927 = 2783891) B2783891
theorem B6263243 : Blo 1855629 6263243 := bstep (se 1 (by rfl) ⟨4697432, by rfl⟩ : syracuseStep 6263243 = 9394865) B9394865
theorem B1855947 : Blo 1855629 1855947 := bstep (se 1 (by rfl) ⟨1391960, by rfl⟩ : syracuseStep 1855947 = 2783921) B2783921
theorem B1855959 : Blo 1855629 1855959 := bstep (se 1 (by rfl) ⟨1391969, by rfl⟩ : syracuseStep 1855959 = 2783939) B2783939
theorem B1855979 : Blo 1855629 1855979 := bstep (se 1 (by rfl) ⟨1391984, by rfl⟩ : syracuseStep 1855979 = 2783969) B2783969
theorem B1855991 : Blo 1855629 1855991 := bstep (se 1 (by rfl) ⟨1391993, by rfl⟩ : syracuseStep 1855991 = 2783987) B2783987
theorem B1856011 : Blo 1855629 1856011 := bstep (se 1 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 1856011 = 2784017) B2784017
theorem B26751505 : Blo 1855629 26751505 := bstep (se 2 (by rfl) ⟨10031814, by rfl⟩ : syracuseStep 26751505 = 20063629) B20063629
theorem B1856023 : Blo 1855629 1856023 := bstep (se 1 (by rfl) ⟨1392017, by rfl⟩ : syracuseStep 1856023 = 2784035) B2784035
theorem B1856043 : Blo 1855629 1856043 := bstep (se 1 (by rfl) ⟨1392032, by rfl⟩ : syracuseStep 1856043 = 2784065) B2784065
theorem B1856055 : Blo 1855629 1856055 := bstep (se 1 (by rfl) ⟨1392041, by rfl⟩ : syracuseStep 1856055 = 2784083) B2784083
theorem B1856075 : Blo 1855629 1856075 := bstep (se 1 (by rfl) ⟨1392056, by rfl⟩ : syracuseStep 1856075 = 2784113) B2784113
theorem B1856087 : Blo 1855629 1856087 := bstep (se 1 (by rfl) ⟨1392065, by rfl⟩ : syracuseStep 1856087 = 2784131) B2784131
theorem B7934557 : Blo 1855629 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B1856107 : Blo 1855629 1856107 := bstep (se 1 (by rfl) ⟨1392080, by rfl⟩ : syracuseStep 1856107 = 2784161) B2784161
theorem B1856119 : Blo 1855629 1856119 := bstep (se 1 (by rfl) ⟨1392089, by rfl⟩ : syracuseStep 1856119 = 2784179) B2784179
theorem B1856139 : Blo 1855629 1856139 := bstep (se 1 (by rfl) ⟨1392104, by rfl⟩ : syracuseStep 1856139 = 2784209) B2784209
theorem B1856151 : Blo 1855629 1856151 := bstep (se 1 (by rfl) ⟨1392113, by rfl⟩ : syracuseStep 1856151 = 2784227) B2784227
theorem B1856171 : Blo 1855629 1856171 := bstep (se 1 (by rfl) ⟨1392128, by rfl⟩ : syracuseStep 1856171 = 2784257) B2784257
theorem B1856183 : Blo 1855629 1856183 := bstep (se 1 (by rfl) ⟨1392137, by rfl⟩ : syracuseStep 1856183 = 2784275) B2784275
theorem B1856203 : Blo 1855629 1856203 := bstep (se 1 (by rfl) ⟨1392152, by rfl⟩ : syracuseStep 1856203 = 2784305) B2784305
theorem B1856215 : Blo 1855629 1856215 := bstep (se 1 (by rfl) ⟨1392161, by rfl⟩ : syracuseStep 1856215 = 2784323) B2784323
theorem B6263513 : Blo 1855629 6263513 := bstep (se 2 (by rfl) ⟨2348817, by rfl⟩ : syracuseStep 6263513 = 4697635) B4697635
theorem B1856235 : Blo 1855629 1856235 := bstep (se 1 (by rfl) ⟨1392176, by rfl⟩ : syracuseStep 1856235 = 2784353) B2784353
theorem B1856247 : Blo 1855629 1856247 := bstep (se 1 (by rfl) ⟨1392185, by rfl⟩ : syracuseStep 1856247 = 2784371) B2784371
theorem B1856267 : Blo 1855629 1856267 := bstep (se 1 (by rfl) ⟨1392200, by rfl⟩ : syracuseStep 1856267 = 2784401) B2784401
theorem B1856279 : Blo 1855629 1856279 := bstep (se 1 (by rfl) ⟨1392209, by rfl⟩ : syracuseStep 1856279 = 2784419) B2784419
theorem B1856299 : Blo 1855629 1856299 := bstep (se 1 (by rfl) ⟨1392224, by rfl⟩ : syracuseStep 1856299 = 2784449) B2784449
theorem B4698931 : Blo 1855629 4698931 := bstep (se 1 (by rfl) ⟨3524198, by rfl⟩ : syracuseStep 4698931 = 7048397) B7048397
theorem B1856311 : Blo 1855629 1856311 := bstep (se 1 (by rfl) ⟨1392233, by rfl⟩ : syracuseStep 1856311 = 2784467) B2784467
theorem B1856331 : Blo 1855629 1856331 := bstep (se 1 (by rfl) ⟨1392248, by rfl⟩ : syracuseStep 1856331 = 2784497) B2784497
theorem B1856343 : Blo 1855629 1856343 := bstep (se 1 (by rfl) ⟨1392257, by rfl⟩ : syracuseStep 1856343 = 2784515) B2784515
theorem B17838949 : Blo 1855629 17838949 := bstep (se 4 (by rfl) ⟨1672401, by rfl⟩ : syracuseStep 17838949 = 3344803) B3344803
theorem B1856363 : Blo 1855629 1856363 := bstep (se 1 (by rfl) ⟨1392272, by rfl⟩ : syracuseStep 1856363 = 2784545) B2784545
theorem B1856375 : Blo 1855629 1856375 := bstep (se 1 (by rfl) ⟨1392281, by rfl⟩ : syracuseStep 1856375 = 2784563) B2784563
theorem B1856395 : Blo 1855629 1856395 := bstep (se 1 (by rfl) ⟨1392296, by rfl⟩ : syracuseStep 1856395 = 2784593) B2784593
theorem B1856407 : Blo 1855629 1856407 := bstep (se 1 (by rfl) ⟨1392305, by rfl⟩ : syracuseStep 1856407 = 2784611) B2784611
theorem B3765143 : Blo 1855629 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B1856427 : Blo 1855629 1856427 := bstep (se 1 (by rfl) ⟨1392320, by rfl⟩ : syracuseStep 1856427 = 2784641) B2784641
theorem B1856439 : Blo 1855629 1856439 := bstep (se 1 (by rfl) ⟨1392329, by rfl⟩ : syracuseStep 1856439 = 2784659) B2784659
theorem B4699073 : Blo 1855629 4699073 := bstep (se 2 (by rfl) ⟨1762152, by rfl⟩ : syracuseStep 4699073 = 3524305) B3524305
theorem B1856459 : Blo 1855629 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B1856471 : Blo 1855629 1856471 := bstep (se 1 (by rfl) ⟨1392353, by rfl⟩ : syracuseStep 1856471 = 2784707) B2784707
theorem B3134423 : Blo 1855629 3134423 := bstep (se 1 (by rfl) ⟨2350817, by rfl⟩ : syracuseStep 3134423 = 4701635) B4701635
theorem B6689753 : Blo 1855629 6689753 := bstep (se 2 (by rfl) ⟨2508657, by rfl⟩ : syracuseStep 6689753 = 5017315) B5017315
theorem B1856491 : Blo 1855629 1856491 := bstep (se 1 (by rfl) ⟨1392368, by rfl⟩ : syracuseStep 1856491 = 2784737) B2784737
theorem B1856503 : Blo 1855629 1856503 := bstep (se 1 (by rfl) ⟨1392377, by rfl⟩ : syracuseStep 1856503 = 2784755) B2784755
theorem B3814411 : Blo 1855629 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B1856523 : Blo 1855629 1856523 := bstep (se 1 (by rfl) ⟨1392392, by rfl⟩ : syracuseStep 1856523 = 2784785) B2784785
theorem B1856535 : Blo 1855629 1856535 := bstep (se 1 (by rfl) ⟨1392401, by rfl⟩ : syracuseStep 1856535 = 2784803) B2784803
theorem B1856555 : Blo 1855629 1856555 := bstep (se 1 (by rfl) ⟨1392416, by rfl⟩ : syracuseStep 1856555 = 2784833) B2784833
theorem B6689837 : Blo 1855629 6689837 := bstep (se 3 (by rfl) ⟨1254344, by rfl⟩ : syracuseStep 6689837 = 2508689) B2508689
theorem B1856567 : Blo 1855629 1856567 := bstep (se 1 (by rfl) ⟨1392425, by rfl⟩ : syracuseStep 1856567 = 2784851) B2784851
theorem B1856587 : Blo 1855629 1856587 := bstep (se 1 (by rfl) ⟨1392440, by rfl⟩ : syracuseStep 1856587 = 2784881) B2784881
theorem B5018699 : Blo 1855629 5018699 := bstep (se 1 (by rfl) ⟨3764024, by rfl⟩ : syracuseStep 5018699 = 7528049) B7528049
theorem B11293771 : Blo 1855629 11293771 := bstep (se 1 (by rfl) ⟨8470328, by rfl⟩ : syracuseStep 11293771 = 16940657) B16940657
theorem B1856599 : Blo 1855629 1856599 := bstep (se 1 (by rfl) ⟨1392449, by rfl⟩ : syracuseStep 1856599 = 2784899) B2784899
theorem B3134551 : Blo 1855629 3134551 := bstep (se 1 (by rfl) ⟨2350913, by rfl⟩ : syracuseStep 3134551 = 4701827) B4701827
theorem B1856619 : Blo 1855629 1856619 := bstep (se 1 (by rfl) ⟨1392464, by rfl⟩ : syracuseStep 1856619 = 2784929) B2784929
theorem B1856631 : Blo 1855629 1856631 := bstep (se 1 (by rfl) ⟨1392473, by rfl⟩ : syracuseStep 1856631 = 2784947) B2784947
theorem B4232321 : Blo 1855629 4232321 := bstep (se 2 (by rfl) ⟨1587120, by rfl⟩ : syracuseStep 4232321 = 3174241) B3174241
theorem B1856651 : Blo 1855629 1856651 := bstep (se 1 (by rfl) ⟨1392488, by rfl⟩ : syracuseStep 1856651 = 2784977) B2784977
theorem B1856663 : Blo 1855629 1856663 := bstep (se 1 (by rfl) ⟨1392497, by rfl⟩ : syracuseStep 1856663 = 2784995) B2784995
theorem B1856683 : Blo 1855629 1856683 := bstep (se 1 (by rfl) ⟨1392512, by rfl⟩ : syracuseStep 1856683 = 2785025) B2785025
theorem B1856695 : Blo 1855629 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B1856715 : Blo 1855629 1856715 := bstep (se 1 (by rfl) ⟨1392536, by rfl⟩ : syracuseStep 1856715 = 2785073) B2785073
theorem B1856727 : Blo 1855629 1856727 := bstep (se 1 (by rfl) ⟨1392545, by rfl⟩ : syracuseStep 1856727 = 2785091) B2785091
theorem B1856747 : Blo 1855629 1856747 := bstep (se 1 (by rfl) ⟨1392560, by rfl⟩ : syracuseStep 1856747 = 2785121) B2785121
theorem B1856759 : Blo 1855629 1856759 := bstep (se 1 (by rfl) ⟨1392569, by rfl⟩ : syracuseStep 1856759 = 2785139) B2785139
theorem B3175691 : Blo 1855629 3175691 := bstep (se 1 (by rfl) ⟨2381768, by rfl⟩ : syracuseStep 3175691 = 4763537) B4763537
theorem B1856779 : Blo 1855629 1856779 := bstep (se 1 (by rfl) ⟨1392584, by rfl⟩ : syracuseStep 1856779 = 2785169) B2785169
theorem B1856791 : Blo 1855629 1856791 := bstep (se 1 (by rfl) ⟨1392593, by rfl⟩ : syracuseStep 1856791 = 2785187) B2785187
theorem B1856811 : Blo 1855629 1856811 := bstep (se 1 (by rfl) ⟨1392608, by rfl⟩ : syracuseStep 1856811 = 2785217) B2785217
theorem B7927091 : Blo 1855629 7927091 := bstep (se 1 (by rfl) ⟨5945318, by rfl⟩ : syracuseStep 7927091 = 11890637) B11890637
theorem B1856823 : Blo 1855629 1856823 := bstep (se 1 (by rfl) ⟨1392617, by rfl⟩ : syracuseStep 1856823 = 2785235) B2785235
theorem B1856843 : Blo 1855629 1856843 := bstep (se 1 (by rfl) ⟨1392632, by rfl⟩ : syracuseStep 1856843 = 2785265) B2785265
theorem B1856855 : Blo 1855629 1856855 := bstep (se 1 (by rfl) ⟨1392641, by rfl⟩ : syracuseStep 1856855 = 2785283) B2785283
theorem B1856875 : Blo 1855629 1856875 := bstep (se 1 (by rfl) ⟨1392656, by rfl⟩ : syracuseStep 1856875 = 2785313) B2785313
theorem B1856887 : Blo 1855629 1856887 := bstep (se 1 (by rfl) ⟨1392665, by rfl⟩ : syracuseStep 1856887 = 2785331) B2785331
theorem B4175243 : Blo 1855629 4175243 := bstep (se 1 (by rfl) ⟨3131432, by rfl⟩ : syracuseStep 4175243 = 6262865) B6262865
theorem B1856907 : Blo 1855629 1856907 := bstep (se 1 (by rfl) ⟨1392680, by rfl⟩ : syracuseStep 1856907 = 2785361) B2785361
theorem B6264215 : Blo 1855629 6264215 := bstep (se 1 (by rfl) ⟨4698161, by rfl⟩ : syracuseStep 6264215 = 9396323) B9396323
theorem B1856919 : Blo 1855629 1856919 := bstep (se 1 (by rfl) ⟨1392689, by rfl⟩ : syracuseStep 1856919 = 2785379) B2785379
theorem B1856939 : Blo 1855629 1856939 := bstep (se 1 (by rfl) ⟨1392704, by rfl⟩ : syracuseStep 1856939 = 2785409) B2785409
theorem B1856951 : Blo 1855629 1856951 := bstep (se 1 (by rfl) ⟨1392713, by rfl⟩ : syracuseStep 1856951 = 2785427) B2785427
theorem B4175297 : Blo 1855629 4175297 := bstep (se 2 (by rfl) ⟨1565736, by rfl⟩ : syracuseStep 4175297 = 3131473) B3131473
theorem B1856971 : Blo 1855629 1856971 := bstep (se 1 (by rfl) ⟨1392728, by rfl⟩ : syracuseStep 1856971 = 2785457) B2785457
theorem B1856983 : Blo 1855629 1856983 := bstep (se 1 (by rfl) ⟨1392737, by rfl⟩ : syracuseStep 1856983 = 2785475) B2785475
theorem B1857003 : Blo 1855629 1857003 := bstep (se 1 (by rfl) ⟨1392752, by rfl⟩ : syracuseStep 1857003 = 2785505) B2785505
theorem B1857015 : Blo 1855629 1857015 := bstep (se 1 (by rfl) ⟨1392761, by rfl⟩ : syracuseStep 1857015 = 2785523) B2785523
theorem B1857035 : Blo 1855629 1857035 := bstep (se 1 (by rfl) ⟨1392776, by rfl⟩ : syracuseStep 1857035 = 2785553) B2785553
theorem B40138253 : Blo 1855629 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B1857047 : Blo 1855629 1857047 := bstep (se 1 (by rfl) ⟨1392785, by rfl⟩ : syracuseStep 1857047 = 2785571) B2785571
theorem B32159267 : Blo 1855629 32159267 := bstep (se 1 (by rfl) ⟨24119450, by rfl⟩ : syracuseStep 32159267 = 48238901) B48238901
theorem B1857067 : Blo 1855629 1857067 := bstep (se 1 (by rfl) ⟨1392800, by rfl⟩ : syracuseStep 1857067 = 2785601) B2785601
theorem B7050797 : Blo 1855629 7050797 := bstep (se 3 (by rfl) ⟨1322024, by rfl⟩ : syracuseStep 7050797 = 2644049) B2644049
theorem B1857079 : Blo 1855629 1857079 := bstep (se 1 (by rfl) ⟨1392809, by rfl⟩ : syracuseStep 1857079 = 2785619) B2785619
theorem B7050827 : Blo 1855629 7050827 := bstep (se 1 (by rfl) ⟨5288120, by rfl⟩ : syracuseStep 7050827 = 10576241) B10576241
theorem B1857099 : Blo 1855629 1857099 := bstep (se 1 (by rfl) ⟨1392824, by rfl⟩ : syracuseStep 1857099 = 2785649) B2785649
theorem B1857111 : Blo 1855629 1857111 := bstep (se 1 (by rfl) ⟨1392833, by rfl⟩ : syracuseStep 1857111 = 2785667) B2785667
theorem B1857131 : Blo 1855629 1857131 := bstep (se 1 (by rfl) ⟨1392848, by rfl⟩ : syracuseStep 1857131 = 2785697) B2785697
theorem B1857143 : Blo 1855629 1857143 := bstep (se 1 (by rfl) ⟨1392857, by rfl⟩ : syracuseStep 1857143 = 2785715) B2785715
theorem B3765889 : Blo 1855629 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B1857163 : Blo 1855629 1857163 := bstep (se 1 (by rfl) ⟨1392872, by rfl⟩ : syracuseStep 1857163 = 2785745) B2785745
theorem B1857175 : Blo 1855629 1857175 := bstep (se 1 (by rfl) ⟨1392881, by rfl⟩ : syracuseStep 1857175 = 2785763) B2785763
theorem B4175513 : Blo 1855629 4175513 := bstep (se 2 (by rfl) ⟨1565817, by rfl⟩ : syracuseStep 4175513 = 3131635) B3131635
theorem B1857195 : Blo 1855629 1857195 := bstep (se 1 (by rfl) ⟨1392896, by rfl⟩ : syracuseStep 1857195 = 2785793) B2785793
theorem B8918707 : Blo 1855629 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B1857207 : Blo 1855629 1857207 := bstep (se 1 (by rfl) ⟨1392905, by rfl⟩ : syracuseStep 1857207 = 2785811) B2785811
theorem B1857227 : Blo 1855629 1857227 := bstep (se 1 (by rfl) ⟨1392920, by rfl⟩ : syracuseStep 1857227 = 2785841) B2785841
theorem B1857239 : Blo 1855629 1857239 := bstep (se 1 (by rfl) ⟨1392929, by rfl⟩ : syracuseStep 1857239 = 2785859) B2785859
theorem B2643673 : Blo 1855629 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B1857259 : Blo 1855629 1857259 := bstep (se 1 (by rfl) ⟨1392944, by rfl⟩ : syracuseStep 1857259 = 2785889) B2785889
theorem B4175603 : Blo 1855629 4175603 := bstep (se 1 (by rfl) ⟨3131702, by rfl⟩ : syracuseStep 4175603 = 6263405) B6263405
theorem B1857271 : Blo 1855629 1857271 := bstep (se 1 (by rfl) ⟨1392953, by rfl⟩ : syracuseStep 1857271 = 2785907) B2785907
theorem B23787269 : Blo 1855629 23787269 := bstep (se 4 (by rfl) ⟨2230056, by rfl⟩ : syracuseStep 23787269 = 4460113) B4460113
theorem B1857291 : Blo 1855629 1857291 := bstep (se 1 (by rfl) ⟨1392968, by rfl⟩ : syracuseStep 1857291 = 2785937) B2785937
theorem B4175639 : Blo 1855629 4175639 := bstep (se 1 (by rfl) ⟨3131729, by rfl⟩ : syracuseStep 4175639 = 6263459) B6263459
theorem B1857303 : Blo 1855629 1857303 := bstep (se 1 (by rfl) ⟨1392977, by rfl⟩ : syracuseStep 1857303 = 2785955) B2785955
theorem B18831149 : Blo 1855629 18831149 := bstep (se 3 (by rfl) ⟨3530840, by rfl⟩ : syracuseStep 18831149 = 7061681) B7061681
theorem B19052333 : Blo 1855629 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B30111533 : Blo 1855629 30111533 := bstep (se 3 (by rfl) ⟨5645912, by rfl⟩ : syracuseStep 30111533 = 11291825) B11291825
theorem B1857323 : Blo 1855629 1857323 := bstep (se 1 (by rfl) ⟨1392992, by rfl⟩ : syracuseStep 1857323 = 2785985) B2785985
theorem B1857335 : Blo 1855629 1857335 := bstep (se 1 (by rfl) ⟨1393001, by rfl⟩ : syracuseStep 1857335 = 2786003) B2786003
theorem B2643787 : Blo 1855629 2643787 := bstep (se 1 (by rfl) ⟨1982840, by rfl⟩ : syracuseStep 2643787 = 3965681) B3965681
theorem B1857355 : Blo 1855629 1857355 := bstep (se 1 (by rfl) ⟨1393016, by rfl⟩ : syracuseStep 1857355 = 2786033) B2786033
theorem B1857367 : Blo 1855629 1857367 := bstep (se 1 (by rfl) ⟨1393025, by rfl⟩ : syracuseStep 1857367 = 2786051) B2786051
theorem B5945177 : Blo 1855629 5945177 := bstep (se 2 (by rfl) ⟨2229441, by rfl⟩ : syracuseStep 5945177 = 4458883) B4458883
theorem B1857387 : Blo 1855629 1857387 := bstep (se 1 (by rfl) ⟨1393040, by rfl⟩ : syracuseStep 1857387 = 2786081) B2786081
theorem B1857399 : Blo 1855629 1857399 := bstep (se 1 (by rfl) ⟨1393049, by rfl⟩ : syracuseStep 1857399 = 2786099) B2786099
theorem B2348939 : Blo 1855629 2348939 := bstep (se 1 (by rfl) ⟨1761704, by rfl⟩ : syracuseStep 2348939 = 3523409) B3523409
theorem B1857419 : Blo 1855629 1857419 := bstep (se 1 (by rfl) ⟨1393064, by rfl⟩ : syracuseStep 1857419 = 2786129) B2786129
theorem B1857431 : Blo 1855629 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1857451 : Blo 1855629 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B6264755 : Blo 1855629 6264755 := bstep (se 1 (by rfl) ⟨4698566, by rfl⟩ : syracuseStep 6264755 = 9397133) B9397133
theorem B1857463 : Blo 1855629 1857463 := bstep (se 1 (by rfl) ⟨1393097, by rfl⟩ : syracuseStep 1857463 = 2786195) B2786195
theorem B4175819 : Blo 1855629 4175819 := bstep (se 1 (by rfl) ⟨3131864, by rfl⟩ : syracuseStep 4175819 = 6263729) B6263729
theorem B1857483 : Blo 1855629 1857483 := bstep (se 1 (by rfl) ⟨1393112, by rfl⟩ : syracuseStep 1857483 = 2786225) B2786225
theorem B1857495 : Blo 1855629 1857495 := bstep (se 1 (by rfl) ⟨1393121, by rfl⟩ : syracuseStep 1857495 = 2786243) B2786243
theorem B1857515 : Blo 1855629 1857515 := bstep (se 1 (by rfl) ⟨1393136, by rfl⟩ : syracuseStep 1857515 = 2786273) B2786273
theorem B1857527 : Blo 1855629 1857527 := bstep (se 1 (by rfl) ⟨1393145, by rfl⟩ : syracuseStep 1857527 = 2786291) B2786291
theorem B4175873 : Blo 1855629 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B1857547 : Blo 1855629 1857547 := bstep (se 1 (by rfl) ⟨1393160, by rfl⟩ : syracuseStep 1857547 = 2786321) B2786321
theorem B1857559 : Blo 1855629 1857559 := bstep (se 1 (by rfl) ⟨1393169, by rfl⟩ : syracuseStep 1857559 = 2786339) B2786339
theorem B1857579 : Blo 1855629 1857579 := bstep (se 1 (by rfl) ⟨1393184, by rfl⟩ : syracuseStep 1857579 = 2786369) B2786369
theorem B14096429 : Blo 1855629 14096429 := bstep (se 3 (by rfl) ⟨2643080, by rfl⟩ : syracuseStep 14096429 = 5286161) B5286161
theorem B1857591 : Blo 1855629 1857591 := bstep (se 1 (by rfl) ⟨1393193, by rfl⟩ : syracuseStep 1857591 = 2786387) B2786387
theorem B1857611 : Blo 1855629 1857611 := bstep (se 1 (by rfl) ⟨1393208, by rfl⟩ : syracuseStep 1857611 = 2786417) B2786417
theorem B1857623 : Blo 1855629 1857623 := bstep (se 1 (by rfl) ⟨1393217, by rfl⟩ : syracuseStep 1857623 = 2786435) B2786435
theorem B4700339 : Blo 1855629 4700339 := bstep (se 1 (by rfl) ⟨3525254, by rfl⟩ : syracuseStep 4700339 = 7050509) B7050509
theorem B6265025 : Blo 1855629 6265025 := bstep (se 2 (by rfl) ⟨2349384, by rfl⟩ : syracuseStep 6265025 = 4698769) B4698769
theorem B8042689 : Blo 1855629 8042689 := bstep (se 2 (by rfl) ⟨3016008, by rfl⟩ : syracuseStep 8042689 = 6032017) B6032017
theorem B2783447 : Blo 1855629 2783447 := bstep (se 1 (by rfl) ⟨2087585, by rfl⟩ : syracuseStep 2783447 = 4175171) B4175171
theorem B4176089 : Blo 1855629 4176089 := bstep (se 2 (by rfl) ⟨1566033, by rfl⟩ : syracuseStep 4176089 = 3132067) B3132067
theorem B7051481 : Blo 1855629 7051481 := bstep (se 2 (by rfl) ⟨2644305, by rfl⟩ : syracuseStep 7051481 = 5288611) B5288611
theorem B7526621 : Blo 1855629 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B7928081 : Blo 1855629 7928081 := bstep (se 2 (by rfl) ⟨2973030, by rfl⟩ : syracuseStep 7928081 = 5946061) B5946061
theorem B9402641 : Blo 1855629 9402641 := bstep (se 2 (by rfl) ⟨3525990, by rfl⟩ : syracuseStep 9402641 = 7051981) B7051981
theorem B2783513 : Blo 1855629 2783513 := bstep (se 2 (by rfl) ⟨1043817, by rfl⟩ : syracuseStep 2783513 = 2087635) B2087635
theorem B4176179 : Blo 1855629 4176179 := bstep (se 1 (by rfl) ⟨3132134, by rfl⟩ : syracuseStep 4176179 = 6264269) B6264269
theorem B4176215 : Blo 1855629 4176215 := bstep (se 1 (by rfl) ⟨3132161, by rfl⟩ : syracuseStep 4176215 = 6264323) B6264323
theorem B4233559 : Blo 1855629 4233559 := bstep (se 1 (by rfl) ⟨3175169, by rfl⟩ : syracuseStep 4233559 = 6350339) B6350339
theorem B7526749 : Blo 1855629 7526749 := bstep (se 3 (by rfl) ⟨1411265, by rfl⟩ : syracuseStep 7526749 = 2822531) B2822531
theorem B2783627 : Blo 1855629 2783627 := bstep (se 1 (by rfl) ⟨2087720, by rfl⟩ : syracuseStep 2783627 = 4175441) B4175441
theorem B2783639 : Blo 1855629 2783639 := bstep (se 1 (by rfl) ⟨2087729, by rfl⟩ : syracuseStep 2783639 = 4175459) B4175459
theorem B3963289 : Blo 1855629 3963289 := bstep (se 2 (by rfl) ⟨1486233, by rfl⟩ : syracuseStep 3963289 = 2972467) B2972467
theorem B9402803 : Blo 1855629 9402803 := bstep (se 1 (by rfl) ⟨7052102, by rfl⟩ : syracuseStep 9402803 = 14104205) B14104205
theorem B2783705 : Blo 1855629 2783705 := bstep (se 2 (by rfl) ⟨1043889, by rfl⟩ : syracuseStep 2783705 = 2087779) B2087779
theorem B4176395 : Blo 1855629 4176395 := bstep (se 1 (by rfl) ⟨3132296, by rfl⟩ : syracuseStep 4176395 = 6264593) B6264593
theorem B7051799 : Blo 1855629 7051799 := bstep (se 1 (by rfl) ⟨5288849, by rfl⟩ : syracuseStep 7051799 = 10577699) B10577699
theorem B4176449 : Blo 1855629 4176449 := bstep (se 2 (by rfl) ⟨1566168, by rfl⟩ : syracuseStep 4176449 = 3132337) B3132337
theorem B2783819 : Blo 1855629 2783819 := bstep (se 1 (by rfl) ⟨2087864, by rfl⟩ : syracuseStep 2783819 = 4175729) B4175729
theorem B2349643 : Blo 1855629 2349643 := bstep (se 1 (by rfl) ⟨1762232, by rfl⟩ : syracuseStep 2349643 = 3524465) B3524465
theorem B2783831 : Blo 1855629 2783831 := bstep (se 1 (by rfl) ⟨2087873, by rfl⟩ : syracuseStep 2783831 = 4175747) B4175747
theorem B21740183 : Blo 1855629 21740183 := bstep (se 1 (by rfl) ⟨16305137, by rfl⟩ : syracuseStep 21740183 = 32610275) B32610275
theorem B2783897 : Blo 1855629 2783897 := bstep (se 2 (by rfl) ⟨1043961, by rfl⟩ : syracuseStep 2783897 = 2087923) B2087923
theorem B3177113 : Blo 1855629 3177113 := bstep (se 2 (by rfl) ⟨1191417, by rfl⟩ : syracuseStep 3177113 = 2382835) B2382835
theorem B4700875 : Blo 1855629 4700875 := bstep (se 1 (by rfl) ⟨3525656, by rfl⟩ : syracuseStep 4700875 = 7051313) B7051313
theorem B34347725 : Blo 1855629 34347725 := bstep (se 3 (by rfl) ⟨6440198, by rfl⟩ : syracuseStep 34347725 = 12880397) B12880397
theorem B6265565 : Blo 1855629 6265565 := bstep (se 3 (by rfl) ⟨1174793, by rfl⟩ : syracuseStep 6265565 = 2349587) B2349587
theorem B2087671 : Blo 1855629 2087671 := bstep (se 1 (by rfl) ⟨1565753, by rfl⟩ : syracuseStep 2087671 = 3131507) B3131507
theorem B2784011 : Blo 1855629 2784011 := bstep (se 1 (by rfl) ⟨2088008, by rfl⟩ : syracuseStep 2784011 = 4176017) B4176017
theorem B2784023 : Blo 1855629 2784023 := bstep (se 1 (by rfl) ⟨2088017, by rfl⟩ : syracuseStep 2784023 = 4176035) B4176035
theorem B2972441 : Blo 1855629 2972441 := bstep (se 2 (by rfl) ⟨1114665, by rfl⟩ : syracuseStep 2972441 = 2229331) B2229331
theorem B4176665 : Blo 1855629 4176665 := bstep (se 2 (by rfl) ⟨1566249, by rfl⟩ : syracuseStep 4176665 = 3132499) B3132499
theorem B23780141 : Blo 1855629 23780141 := bstep (se 3 (by rfl) ⟨4458776, by rfl⟩ : syracuseStep 23780141 = 8917553) B8917553
theorem B2349911 : Blo 1855629 2349911 := bstep (se 1 (by rfl) ⟨1762433, by rfl⟩ : syracuseStep 2349911 = 3524867) B3524867
theorem B2784089 : Blo 1855629 2784089 := bstep (se 2 (by rfl) ⟨1044033, by rfl⟩ : syracuseStep 2784089 = 2088067) B2088067
theorem B4701017 : Blo 1855629 4701017 := bstep (se 2 (by rfl) ⟨1762881, by rfl⟩ : syracuseStep 4701017 = 3525763) B3525763
theorem B4176755 : Blo 1855629 4176755 := bstep (se 1 (by rfl) ⟨3132566, by rfl⟩ : syracuseStep 4176755 = 6265133) B6265133
theorem B4176791 : Blo 1855629 4176791 := bstep (se 1 (by rfl) ⟨3132593, by rfl⟩ : syracuseStep 4176791 = 6265187) B6265187
theorem B2087851 : Blo 1855629 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B2784203 : Blo 1855629 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B2784215 : Blo 1855629 2784215 := bstep (se 1 (by rfl) ⟨2088161, by rfl⟩ : syracuseStep 2784215 = 4176323) B4176323
theorem B6618077 : Blo 1855629 6618077 := bstep (se 3 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 6618077 = 2481779) B2481779
theorem B2087959 : Blo 1855629 2087959 := bstep (se 1 (by rfl) ⟨1565969, by rfl⟩ : syracuseStep 2087959 = 3131939) B3131939
theorem B2784281 : Blo 1855629 2784281 := bstep (se 2 (by rfl) ⟨1044105, by rfl⟩ : syracuseStep 2784281 = 2088211) B2088211
theorem B5946419 : Blo 1855629 5946419 := bstep (se 1 (by rfl) ⟨4459814, by rfl⟩ : syracuseStep 5946419 = 8919629) B8919629
theorem B4176971 : Blo 1855629 4176971 := bstep (se 1 (by rfl) ⟨3132728, by rfl⟩ : syracuseStep 4176971 = 6265457) B6265457
theorem B3816563 : Blo 1855629 3816563 := bstep (se 1 (by rfl) ⟨2862422, by rfl⟩ : syracuseStep 3816563 = 5724845) B5724845
theorem B4177025 : Blo 1855629 4177025 := bstep (se 2 (by rfl) ⟨1566384, by rfl⟩ : syracuseStep 4177025 = 3132769) B3132769
theorem B2784395 : Blo 1855629 2784395 := bstep (se 1 (by rfl) ⟨2088296, by rfl⟩ : syracuseStep 2784395 = 4176593) B4176593
theorem B9395351 : Blo 1855629 9395351 := bstep (se 1 (by rfl) ⟨7046513, by rfl⟩ : syracuseStep 9395351 = 14093027) B14093027
theorem B2784407 : Blo 1855629 2784407 := bstep (se 1 (by rfl) ⟨2088305, by rfl⟩ : syracuseStep 2784407 = 4176611) B4176611
theorem B7052467 : Blo 1855629 7052467 := bstep (se 1 (by rfl) ⟨5289350, by rfl⟩ : syracuseStep 7052467 = 10578701) B10578701
theorem B2088139 : Blo 1855629 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B2784473 : Blo 1855629 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B33873137 : Blo 1855629 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B35675437 : Blo 1855629 35675437 := bstep (se 3 (by rfl) ⟨6689144, by rfl⟩ : syracuseStep 35675437 = 13378289) B13378289
theorem B2088247 : Blo 1855629 2088247 := bstep (se 1 (by rfl) ⟨1566185, by rfl⟩ : syracuseStep 2088247 = 3132371) B3132371
theorem B2784587 : Blo 1855629 2784587 := bstep (se 1 (by rfl) ⟨2088440, by rfl⟩ : syracuseStep 2784587 = 4176881) B4176881
theorem B5021003 : Blo 1855629 5021003 := bstep (se 1 (by rfl) ⟨3765752, by rfl⟩ : syracuseStep 5021003 = 7531505) B7531505
theorem B2784599 : Blo 1855629 2784599 := bstep (se 1 (by rfl) ⟨2088449, by rfl⟩ : syracuseStep 2784599 = 4176899) B4176899
theorem B4177241 : Blo 1855629 4177241 := bstep (se 2 (by rfl) ⟨1566465, by rfl⟩ : syracuseStep 4177241 = 3132931) B3132931
theorem B2784665 : Blo 1855629 2784665 := bstep (se 2 (by rfl) ⟨1044249, by rfl⟩ : syracuseStep 2784665 = 2088499) B2088499
theorem B4177331 : Blo 1855629 4177331 := bstep (se 1 (by rfl) ⟨3132998, by rfl⟩ : syracuseStep 4177331 = 6265997) B6265997
theorem B4177367 : Blo 1855629 4177367 := bstep (se 1 (by rfl) ⟨3133025, by rfl⟩ : syracuseStep 4177367 = 6266051) B6266051
theorem B2088427 : Blo 1855629 2088427 := bstep (se 1 (by rfl) ⟨1566320, by rfl⟩ : syracuseStep 2088427 = 3132641) B3132641
theorem B2784779 : Blo 1855629 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B2784791 : Blo 1855629 2784791 := bstep (se 1 (by rfl) ⟨2088593, by rfl⟩ : syracuseStep 2784791 = 4177187) B4177187
theorem B6692375 : Blo 1855629 6692375 := bstep (se 1 (by rfl) ⟨5019281, by rfl⟩ : syracuseStep 6692375 = 10038563) B10038563
theorem B2350615 : Blo 1855629 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B2088535 : Blo 1855629 2088535 := bstep (se 1 (by rfl) ⟨1566401, by rfl⟩ : syracuseStep 2088535 = 3132803) B3132803
theorem B2784857 : Blo 1855629 2784857 := bstep (se 2 (by rfl) ⟨1044321, by rfl⟩ : syracuseStep 2784857 = 2088643) B2088643
theorem B38125187 : Blo 1855629 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B4177547 : Blo 1855629 4177547 := bstep (se 1 (by rfl) ⟨3133160, by rfl⟩ : syracuseStep 4177547 = 6266321) B6266321
theorem B4701847 : Blo 1855629 4701847 := bstep (se 1 (by rfl) ⟨3526385, by rfl⟩ : syracuseStep 4701847 = 7052771) B7052771
theorem B4177601 : Blo 1855629 4177601 := bstep (se 2 (by rfl) ⟨1566600, by rfl⟩ : syracuseStep 4177601 = 3133201) B3133201
theorem B2784971 : Blo 1855629 2784971 := bstep (se 1 (by rfl) ⟨2088728, by rfl⟩ : syracuseStep 2784971 = 4177457) B4177457
theorem B2784983 : Blo 1855629 2784983 := bstep (se 1 (by rfl) ⟨2088737, by rfl⟩ : syracuseStep 2784983 = 4177475) B4177475
theorem B2088715 : Blo 1855629 2088715 := bstep (se 1 (by rfl) ⟨1566536, by rfl⟩ : syracuseStep 2088715 = 3133073) B3133073
theorem B3219211 : Blo 1855629 3219211 := bstep (se 1 (by rfl) ⟨2414408, by rfl⟩ : syracuseStep 3219211 = 4828817) B4828817
theorem B5644055 : Blo 1855629 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B2785049 : Blo 1855629 2785049 := bstep (se 2 (by rfl) ⟨1044393, by rfl⟩ : syracuseStep 2785049 = 2088787) B2088787
theorem B6266699 : Blo 1855629 6266699 := bstep (se 1 (by rfl) ⟨4700024, by rfl⟩ : syracuseStep 6266699 = 9400049) B9400049
theorem B2088823 : Blo 1855629 2088823 := bstep (se 1 (by rfl) ⟨1566617, by rfl⟩ : syracuseStep 2088823 = 3133235) B3133235
theorem B2785163 : Blo 1855629 2785163 := bstep (se 1 (by rfl) ⟨2088872, by rfl⟩ : syracuseStep 2785163 = 4177745) B4177745
theorem B2785175 : Blo 1855629 2785175 := bstep (se 1 (by rfl) ⟨2088881, by rfl⟩ : syracuseStep 2785175 = 4177763) B4177763
theorem B4177817 : Blo 1855629 4177817 := bstep (se 2 (by rfl) ⟨1566681, by rfl⟩ : syracuseStep 4177817 = 3133363) B3133363
theorem B2785241 : Blo 1855629 2785241 := bstep (se 2 (by rfl) ⟨1044465, by rfl⟩ : syracuseStep 2785241 = 2088931) B2088931
theorem B4177907 : Blo 1855629 4177907 := bstep (se 1 (by rfl) ⟨3133430, by rfl⟩ : syracuseStep 4177907 = 6266861) B6266861
theorem B2088967 : Blo 1855629 2088967 := bstep (se 1 (by rfl) ⟨1566725, by rfl⟩ : syracuseStep 2088967 = 3133451) B3133451
theorem B2785295 : Blo 1855629 2785295 := bstep (se 1 (by rfl) ⟨2088971, by rfl⟩ : syracuseStep 2785295 = 4177943) B4177943
theorem B2785337 : Blo 1855629 2785337 := bstep (se 2 (by rfl) ⟨1044501, by rfl⟩ : syracuseStep 2785337 = 2089003) B2089003
theorem B4177979 : Blo 1855629 4177979 := bstep (se 1 (by rfl) ⟨3133484, by rfl⟩ : syracuseStep 4177979 = 6266969) B6266969
theorem B2785415 : Blo 1855629 2785415 := bstep (se 1 (by rfl) ⟨2089061, by rfl⟩ : syracuseStep 2785415 = 4178123) B4178123
theorem B2785451 : Blo 1855629 2785451 := bstep (se 1 (by rfl) ⟨2089088, by rfl⟩ : syracuseStep 2785451 = 4178177) B4178177
theorem B4178105 : Blo 1855629 4178105 := bstep (se 2 (by rfl) ⟨1566789, by rfl⟩ : syracuseStep 4178105 = 3133579) B3133579
theorem B2089147 : Blo 1855629 2089147 := bstep (se 1 (by rfl) ⟨1566860, by rfl⟩ : syracuseStep 2089147 = 3133721) B3133721
theorem B2785481 : Blo 1855629 2785481 := bstep (se 2 (by rfl) ⟨1044555, by rfl⟩ : syracuseStep 2785481 = 2089111) B2089111
theorem B10723585 : Blo 1855629 10723585 := bstep (se 2 (by rfl) ⟨4021344, by rfl⟩ : syracuseStep 10723585 = 8042689) B8042689
theorem B2679097 : Blo 1855629 2679097 := bstep (se 2 (by rfl) ⟨1004661, by rfl⟩ : syracuseStep 2679097 = 2009323) B2009323
theorem B2785595 : Blo 1855629 2785595 := bstep (se 1 (by rfl) ⟨2089196, by rfl⟩ : syracuseStep 2785595 = 4178393) B4178393
theorem B2785655 : Blo 1855629 2785655 := bstep (se 1 (by rfl) ⟨2089241, by rfl⟩ : syracuseStep 2785655 = 4178483) B4178483
theorem B2785679 : Blo 1855629 2785679 := bstep (se 1 (by rfl) ⟨2089259, by rfl⟩ : syracuseStep 2785679 = 4178519) B4178519
theorem B2785721 : Blo 1855629 2785721 := bstep (se 2 (by rfl) ⟨1044645, by rfl⟩ : syracuseStep 2785721 = 2089291) B2089291
theorem B5644745 : Blo 1855629 5644745 := bstep (se 2 (by rfl) ⟨2116779, by rfl⟩ : syracuseStep 5644745 = 4233559) B4233559
theorem B10035665 : Blo 1855629 10035665 := bstep (se 2 (by rfl) ⟨3763374, by rfl⟩ : syracuseStep 10035665 = 7526749) B7526749
theorem B11895299 : Blo 1855629 11895299 := bstep (se 1 (by rfl) ⟨8921474, by rfl⟩ : syracuseStep 11895299 = 17842949) B17842949
theorem B2785799 : Blo 1855629 2785799 := bstep (se 1 (by rfl) ⟨2089349, by rfl⟩ : syracuseStep 2785799 = 4178699) B4178699
theorem B4178447 : Blo 1855629 4178447 := bstep (se 1 (by rfl) ⟨3133835, by rfl⟩ : syracuseStep 4178447 = 6267671) B6267671
theorem B5284385 : Blo 1855629 5284385 := bstep (se 2 (by rfl) ⟨1981644, by rfl⟩ : syracuseStep 5284385 = 3963289) B3963289
theorem B3523105 : Blo 1855629 3523105 := bstep (se 2 (by rfl) ⟨1321164, by rfl⟩ : syracuseStep 3523105 = 2642329) B2642329
theorem B4178465 : Blo 1855629 4178465 := bstep (se 2 (by rfl) ⟨1566924, by rfl⟩ : syracuseStep 4178465 = 3133849) B3133849
theorem B2785835 : Blo 1855629 2785835 := bstep (se 1 (by rfl) ⟨2089376, by rfl⟩ : syracuseStep 2785835 = 4178753) B4178753
theorem B2785865 : Blo 1855629 2785865 := bstep (se 2 (by rfl) ⟨1044699, by rfl⟩ : syracuseStep 2785865 = 2089399) B2089399
theorem B20070989 : Blo 1855629 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3097207 : Blo 1855629 3097207 := bstep (se 1 (by rfl) ⟨2322905, by rfl⟩ : syracuseStep 3097207 = 4645811) B4645811
theorem B2089615 : Blo 1855629 2089615 := bstep (se 1 (by rfl) ⟨1567211, by rfl⟩ : syracuseStep 2089615 = 3134423) B3134423
theorem B2785979 : Blo 1855629 2785979 := bstep (se 1 (by rfl) ⟨2089484, by rfl⟩ : syracuseStep 2785979 = 4178969) B4178969
theorem B35668673 : Blo 1855629 35668673 := bstep (se 2 (by rfl) ⟨13375752, by rfl⟩ : syracuseStep 35668673 = 26751505) B26751505
theorem B2786039 : Blo 1855629 2786039 := bstep (se 1 (by rfl) ⟨2089529, by rfl⟩ : syracuseStep 2786039 = 4179059) B4179059
theorem B2786063 : Blo 1855629 2786063 := bstep (se 1 (by rfl) ⟨2089547, by rfl⟩ : syracuseStep 2786063 = 4179095) B4179095
theorem B7529249 : Blo 1855629 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B2786105 : Blo 1855629 2786105 := bstep (se 2 (by rfl) ⟨1044789, by rfl⟩ : syracuseStep 2786105 = 2089579) B2089579
theorem B5284727 : Blo 1855629 5284727 := bstep (se 1 (by rfl) ⟨3963545, by rfl⟩ : syracuseStep 5284727 = 7927091) B7927091
theorem B4178807 : Blo 1855629 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B2786183 : Blo 1855629 2786183 := bstep (se 1 (by rfl) ⟨2089637, by rfl⟩ : syracuseStep 2786183 = 4179275) B4179275
theorem B21152663 : Blo 1855629 21152663 := bstep (se 1 (by rfl) ⟨15864497, by rfl⟩ : syracuseStep 21152663 = 31728995) B31728995
theorem B2786219 : Blo 1855629 2786219 := bstep (se 1 (by rfl) ⟨2089664, by rfl⟩ : syracuseStep 2786219 = 4179329) B4179329
theorem B6267833 : Blo 1855629 6267833 := bstep (se 2 (by rfl) ⟨2350437, by rfl⟩ : syracuseStep 6267833 = 4700875) B4700875
theorem B2786249 : Blo 1855629 2786249 := bstep (se 2 (by rfl) ⟨1044843, by rfl⟩ : syracuseStep 2786249 = 2089687) B2089687
theorem B21439511 : Blo 1855629 21439511 := bstep (se 1 (by rfl) ⟨16079633, by rfl⟩ : syracuseStep 21439511 = 32159267) B32159267
theorem B10576925 : Blo 1855629 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B4178987 : Blo 1855629 4178987 := bstep (se 1 (by rfl) ⟨3134240, by rfl⟩ : syracuseStep 4178987 = 6268481) B6268481
theorem B2786363 : Blo 1855629 2786363 := bstep (se 1 (by rfl) ⟨2089772, by rfl⟩ : syracuseStep 2786363 = 4179545) B4179545
theorem B5358653 : Blo 1855629 5358653 := bstep (se 3 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 5358653 = 2009495) B2009495
theorem B2786423 : Blo 1855629 2786423 := bstep (se 1 (by rfl) ⟨2089817, by rfl⟩ : syracuseStep 2786423 = 4179635) B4179635
theorem B9397619 : Blo 1855629 9397619 := bstep (se 1 (by rfl) ⟨7048214, by rfl⟩ : syracuseStep 9397619 = 14096429) B14096429
theorem B4179347 : Blo 1855629 4179347 := bstep (se 1 (by rfl) ⟨3134510, by rfl⟩ : syracuseStep 4179347 = 6269021) B6269021
theorem B12060089 : Blo 1855629 12060089 := bstep (se 2 (by rfl) ⟨4522533, by rfl⟩ : syracuseStep 12060089 = 9045067) B9045067
theorem B15058361 : Blo 1855629 15058361 := bstep (se 2 (by rfl) ⟨5646885, by rfl⟩ : syracuseStep 15058361 = 11293771) B11293771
theorem B4179401 : Blo 1855629 4179401 := bstep (se 2 (by rfl) ⟨1567275, by rfl⟩ : syracuseStep 4179401 = 3134551) B3134551
theorem B5285387 : Blo 1855629 5285387 := bstep (se 1 (by rfl) ⟨3964040, by rfl⟩ : syracuseStep 5285387 = 7928081) B7928081
theorem B6268427 : Blo 1855629 6268427 := bstep (se 1 (by rfl) ⟨4701320, by rfl⟩ : syracuseStep 6268427 = 9402641) B9402641
theorem B6268535 : Blo 1855629 6268535 := bstep (se 1 (by rfl) ⟨4701401, by rfl⟩ : syracuseStep 6268535 = 9402803) B9402803
theorem B14493455 : Blo 1855629 14493455 := bstep (se 1 (by rfl) ⟨10870091, by rfl⟩ : syracuseStep 14493455 = 21740183) B21740183
theorem B22898483 : Blo 1855629 22898483 := bstep (se 1 (by rfl) ⟨17173862, by rfl⟩ : syracuseStep 22898483 = 34347725) B34347725
theorem B3524411 : Blo 1855629 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B9398105 : Blo 1855629 9398105 := bstep (se 2 (by rfl) ⟨3524289, by rfl⟩ : syracuseStep 9398105 = 7048579) B7048579
theorem B15853427 : Blo 1855629 15853427 := bstep (se 1 (by rfl) ⟨11890070, by rfl⟩ : syracuseStep 15853427 = 23780141) B23780141
theorem B7047121 : Blo 1855629 7047121 := bstep (se 2 (by rfl) ⟨2642670, by rfl⟩ : syracuseStep 7047121 = 5285341) B5285341
theorem B3131527 : Blo 1855629 3131527 := bstep (se 1 (by rfl) ⟨2348645, by rfl⟩ : syracuseStep 3131527 = 4697291) B4697291
theorem B6269129 : Blo 1855629 6269129 := bstep (se 2 (by rfl) ⟨2350923, by rfl⟩ : syracuseStep 6269129 = 4701847) B4701847
theorem B15853805 : Blo 1855629 15853805 := bstep (se 3 (by rfl) ⟨2972588, by rfl⟩ : syracuseStep 15853805 = 5945177) B5945177
theorem B7047425 : Blo 1855629 7047425 := bstep (se 2 (by rfl) ⟨2642784, by rfl⟩ : syracuseStep 7047425 = 5285569) B5285569
theorem B3524897 : Blo 1855629 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B32139665 : Blo 1855629 32139665 := bstep (se 2 (by rfl) ⟨12052374, by rfl⟩ : syracuseStep 32139665 = 24104749) B24104749
theorem B3525049 : Blo 1855629 3525049 := bstep (se 2 (by rfl) ⟨1321893, by rfl⟩ : syracuseStep 3525049 = 2643787) B2643787
theorem B3762703 : Blo 1855629 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B7146103 : Blo 1855629 7146103 := bstep (se 1 (by rfl) ⟨5359577, by rfl⟩ : syracuseStep 7146103 = 10719155) B10719155
theorem B7047881 : Blo 1855629 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B3132175 : Blo 1855629 3132175 := bstep (se 1 (by rfl) ⟨2349131, by rfl⟩ : syracuseStep 3132175 = 4698263) B4698263
theorem B11889611 : Blo 1855629 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B10177501 : Blo 1855629 10177501 := bstep (se 3 (by rfl) ⟨1908281, by rfl⟩ : syracuseStep 10177501 = 3816563) B3816563
theorem B4697099 : Blo 1855629 4697099 := bstep (se 1 (by rfl) ⟨3522824, by rfl⟩ : syracuseStep 4697099 = 7045649) B7045649
theorem B5286971 : Blo 1855629 5286971 := bstep (se 1 (by rfl) ⟨3965228, by rfl⟩ : syracuseStep 5286971 = 7930457) B7930457
theorem B5287027 : Blo 1855629 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B14093513 : Blo 1855629 14093513 := bstep (se 2 (by rfl) ⟨5285067, by rfl⟩ : syracuseStep 14093513 = 10570135) B10570135
theorem B8039681 : Blo 1855629 8039681 := bstep (se 2 (by rfl) ⟨3014880, by rfl⟩ : syracuseStep 8039681 = 6029761) B6029761
theorem B3132715 : Blo 1855629 3132715 := bstep (se 1 (by rfl) ⟨2349536, by rfl⟩ : syracuseStep 3132715 = 4699073) B4699073
theorem B4459835 : Blo 1855629 4459835 := bstep (se 1 (by rfl) ⟨3344876, by rfl⟩ : syracuseStep 4459835 = 6689753) B6689753
theorem B6352187 : Blo 1855629 6352187 := bstep (se 1 (by rfl) ⟨4764140, by rfl⟩ : syracuseStep 6352187 = 9528281) B9528281
theorem B3345799 : Blo 1855629 3345799 := bstep (se 1 (by rfl) ⟨2509349, by rfl⟩ : syracuseStep 3345799 = 5018699) B5018699
theorem B2821547 : Blo 1855629 2821547 := bstep (se 1 (by rfl) ⟨2116160, by rfl⟩ : syracuseStep 2821547 = 4232321) B4232321
theorem B3132857 : Blo 1855629 3132857 := bstep (se 2 (by rfl) ⟨1174821, by rfl⟩ : syracuseStep 3132857 = 2349643) B2349643
theorem B5287369 : Blo 1855629 5287369 := bstep (se 2 (by rfl) ⟨1982763, by rfl⟩ : syracuseStep 5287369 = 3965527) B3965527
theorem B10579409 : Blo 1855629 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B4697615 : Blo 1855629 4697615 := bstep (se 1 (by rfl) ⟨3523211, by rfl⟩ : syracuseStep 4697615 = 7046423) B7046423
theorem B4697747 : Blo 1855629 4697747 := bstep (se 1 (by rfl) ⟨3523310, by rfl⟩ : syracuseStep 4697747 = 7046621) B7046621
theorem B26758835 : Blo 1855629 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B23785265 : Blo 1855629 23785265 := bstep (se 2 (by rfl) ⟨8919474, by rfl⟩ : syracuseStep 23785265 = 17838949) B17838949
theorem B12554099 : Blo 1855629 12554099 := bstep (se 1 (by rfl) ⟨9415574, by rfl⟩ : syracuseStep 12554099 = 18831149) B18831149
theorem B12701555 : Blo 1855629 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B20074355 : Blo 1855629 20074355 := bstep (se 1 (by rfl) ⟨15055766, by rfl⟩ : syracuseStep 20074355 = 30111533) B30111533
theorem B9400211 : Blo 1855629 9400211 := bstep (se 1 (by rfl) ⟨7050158, by rfl⟩ : syracuseStep 9400211 = 14100317) B14100317
theorem B3346361 : Blo 1855629 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B4763681 : Blo 1855629 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B3133559 : Blo 1855629 3133559 := bstep (se 1 (by rfl) ⟨2350169, by rfl⟩ : syracuseStep 3133559 = 4700339) B4700339
theorem B1855631 : Blo 1855629 1855631 := bstep (se 1 (by rfl) ⟨1391723, by rfl⟩ : syracuseStep 1855631 = 2783447) B2783447
theorem B1855675 : Blo 1855629 1855675 := bstep (se 1 (by rfl) ⟨1391756, by rfl⟩ : syracuseStep 1855675 = 2783513) B2783513
theorem B1855751 : Blo 1855629 1855751 := bstep (se 1 (by rfl) ⟨1391813, by rfl⟩ : syracuseStep 1855751 = 2783627) B2783627
theorem B1855759 : Blo 1855629 1855759 := bstep (se 1 (by rfl) ⟨1391819, by rfl⟩ : syracuseStep 1855759 = 2783639) B2783639
theorem B1855803 : Blo 1855629 1855803 := bstep (se 1 (by rfl) ⟨1391852, by rfl⟩ : syracuseStep 1855803 = 2783705) B2783705
theorem B1855879 : Blo 1855629 1855879 := bstep (se 1 (by rfl) ⟨1391909, by rfl⟩ : syracuseStep 1855879 = 2783819) B2783819
theorem B1855887 : Blo 1855629 1855887 := bstep (se 1 (by rfl) ⟨1391915, by rfl⟩ : syracuseStep 1855887 = 2783831) B2783831
theorem B47567249 : Blo 1855629 47567249 := bstep (se 2 (by rfl) ⟨17837718, by rfl⟩ : syracuseStep 47567249 = 35675437) B35675437
theorem B1855931 : Blo 1855629 1855931 := bstep (se 1 (by rfl) ⟨1391948, by rfl⟩ : syracuseStep 1855931 = 2783897) B2783897
theorem B1856007 : Blo 1855629 1856007 := bstep (se 1 (by rfl) ⟨1392005, by rfl⟩ : syracuseStep 1856007 = 2784011) B2784011
theorem B1856015 : Blo 1855629 1856015 := bstep (se 1 (by rfl) ⟨1392011, by rfl⟩ : syracuseStep 1856015 = 2784023) B2784023
theorem B1856059 : Blo 1855629 1856059 := bstep (se 1 (by rfl) ⟨1392044, by rfl⟩ : syracuseStep 1856059 = 2784089) B2784089
theorem B3134011 : Blo 1855629 3134011 := bstep (se 1 (by rfl) ⟨2350508, by rfl⟩ : syracuseStep 3134011 = 4701017) B4701017
theorem B8041027 : Blo 1855629 8041027 := bstep (se 1 (by rfl) ⟨6030770, by rfl⟩ : syracuseStep 8041027 = 12061541) B12061541
theorem B1856135 : Blo 1855629 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B1856143 : Blo 1855629 1856143 := bstep (se 1 (by rfl) ⟨1392107, by rfl⟩ : syracuseStep 1856143 = 2784215) B2784215
theorem B4412051 : Blo 1855629 4412051 := bstep (se 1 (by rfl) ⟨3309038, by rfl⟩ : syracuseStep 4412051 = 6618077) B6618077
theorem B1856187 : Blo 1855629 1856187 := bstep (se 1 (by rfl) ⟨1392140, by rfl⟩ : syracuseStep 1856187 = 2784281) B2784281
theorem B14103233 : Blo 1855629 14103233 := bstep (se 2 (by rfl) ⟨5288712, by rfl⟩ : syracuseStep 14103233 = 10577425) B10577425
theorem B3134153 : Blo 1855629 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B4698881 : Blo 1855629 4698881 := bstep (se 2 (by rfl) ⟨1762080, by rfl⟩ : syracuseStep 4698881 = 3524161) B3524161
theorem B1856263 : Blo 1855629 1856263 := bstep (se 1 (by rfl) ⟨1392197, by rfl⟩ : syracuseStep 1856263 = 2784395) B2784395
theorem B6263567 : Blo 1855629 6263567 := bstep (se 1 (by rfl) ⟨4697675, by rfl⟩ : syracuseStep 6263567 = 9395351) B9395351
theorem B1856271 : Blo 1855629 1856271 := bstep (se 1 (by rfl) ⟨1392203, by rfl⟩ : syracuseStep 1856271 = 2784407) B2784407
theorem B67736357 : Blo 1855629 67736357 := bstep (se 4 (by rfl) ⟨6350283, by rfl⟩ : syracuseStep 67736357 = 12700567) B12700567
theorem B1856315 : Blo 1855629 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B22582091 : Blo 1855629 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B1856391 : Blo 1855629 1856391 := bstep (se 1 (by rfl) ⟨1392293, by rfl⟩ : syracuseStep 1856391 = 2784587) B2784587
theorem B3347335 : Blo 1855629 3347335 := bstep (se 1 (by rfl) ⟨2510501, by rfl⟩ : syracuseStep 3347335 = 5021003) B5021003
theorem B1856399 : Blo 1855629 1856399 := bstep (se 1 (by rfl) ⟨1392299, by rfl⟩ : syracuseStep 1856399 = 2784599) B2784599
theorem B11891609 : Blo 1855629 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B1856443 : Blo 1855629 1856443 := bstep (se 1 (by rfl) ⟨1392332, by rfl⟩ : syracuseStep 1856443 = 2784665) B2784665
theorem B1856519 : Blo 1855629 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B1856527 : Blo 1855629 1856527 := bstep (se 1 (by rfl) ⟨1392395, by rfl⟩ : syracuseStep 1856527 = 2784791) B2784791
theorem B4461583 : Blo 1855629 4461583 := bstep (se 1 (by rfl) ⟨3346187, by rfl⟩ : syracuseStep 4461583 = 6692375) B6692375
theorem B6263837 : Blo 1855629 6263837 := bstep (se 3 (by rfl) ⟨1174469, by rfl⟩ : syracuseStep 6263837 = 2348939) B2348939
theorem B1856571 : Blo 1855629 1856571 := bstep (se 1 (by rfl) ⟨1392428, by rfl⟩ : syracuseStep 1856571 = 2784857) B2784857
theorem B10040381 : Blo 1855629 10040381 := bstep (se 3 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 10040381 = 3765143) B3765143
theorem B25416791 : Blo 1855629 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B4699255 : Blo 1855629 4699255 := bstep (se 1 (by rfl) ⟨3524441, by rfl⟩ : syracuseStep 4699255 = 7048883) B7048883
theorem B1856647 : Blo 1855629 1856647 := bstep (se 1 (by rfl) ⟨1392485, by rfl⟩ : syracuseStep 1856647 = 2784971) B2784971
theorem B1856655 : Blo 1855629 1856655 := bstep (se 1 (by rfl) ⟨1392491, by rfl⟩ : syracuseStep 1856655 = 2784983) B2784983
theorem B21157037 : Blo 1855629 21157037 := bstep (se 3 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 21157037 = 7933889) B7933889
theorem B1856699 : Blo 1855629 1856699 := bstep (se 1 (by rfl) ⟨1392524, by rfl⟩ : syracuseStep 1856699 = 2785049) B2785049
theorem B1856775 : Blo 1855629 1856775 := bstep (se 1 (by rfl) ⟨1392581, by rfl⟩ : syracuseStep 1856775 = 2785163) B2785163
theorem B7927055 : Blo 1855629 7927055 := bstep (se 1 (by rfl) ⟨5945291, by rfl⟩ : syracuseStep 7927055 = 11890583) B11890583
theorem B1856783 : Blo 1855629 1856783 := bstep (se 1 (by rfl) ⟨1392587, by rfl⟩ : syracuseStep 1856783 = 2785175) B2785175
theorem B1856827 : Blo 1855629 1856827 := bstep (se 1 (by rfl) ⟨1392620, by rfl⟩ : syracuseStep 1856827 = 2785241) B2785241
theorem B1856903 : Blo 1855629 1856903 := bstep (se 1 (by rfl) ⟨1392677, by rfl⟩ : syracuseStep 1856903 = 2785355) B2785355
theorem B4461959 : Blo 1855629 4461959 := bstep (se 1 (by rfl) ⟨3346469, by rfl⟩ : syracuseStep 4461959 = 6692939) B6692939
theorem B1856911 : Blo 1855629 1856911 := bstep (se 1 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 1856911 = 2785367) B2785367
theorem B1856955 : Blo 1855629 1856955 := bstep (se 1 (by rfl) ⟨1392716, by rfl⟩ : syracuseStep 1856955 = 2785433) B2785433
theorem B17839565 : Blo 1855629 17839565 := bstep (se 3 (by rfl) ⟨3344918, by rfl⟩ : syracuseStep 17839565 = 6689837) B6689837
theorem B30127565 : Blo 1855629 30127565 := bstep (se 3 (by rfl) ⟨5648918, by rfl⟩ : syracuseStep 30127565 = 11297837) B11297837
theorem B15857117 : Blo 1855629 15857117 := bstep (se 3 (by rfl) ⟨2973209, by rfl⟩ : syracuseStep 15857117 = 5946419) B5946419
theorem B1857031 : Blo 1855629 1857031 := bstep (se 1 (by rfl) ⟨1392773, by rfl⟩ : syracuseStep 1857031 = 2785547) B2785547
theorem B1857039 : Blo 1855629 1857039 := bstep (se 1 (by rfl) ⟨1392779, by rfl⟩ : syracuseStep 1857039 = 2785559) B2785559
theorem B4699691 : Blo 1855629 4699691 := bstep (se 1 (by rfl) ⟨3524768, by rfl⟩ : syracuseStep 4699691 = 7049537) B7049537
theorem B1857083 : Blo 1855629 1857083 := bstep (se 1 (by rfl) ⟨1392812, by rfl⟩ : syracuseStep 1857083 = 2785625) B2785625
theorem B5289533 : Blo 1855629 5289533 := bstep (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) B1983575
theorem B4175495 : Blo 1855629 4175495 := bstep (se 1 (by rfl) ⟨3131621, by rfl⟩ : syracuseStep 4175495 = 6263243) B6263243
theorem B1857159 : Blo 1855629 1857159 := bstep (se 1 (by rfl) ⟨1392869, by rfl⟩ : syracuseStep 1857159 = 2785739) B2785739
theorem B1857167 : Blo 1855629 1857167 := bstep (se 1 (by rfl) ⟨1392875, by rfl⟩ : syracuseStep 1857167 = 2785751) B2785751
theorem B1857211 : Blo 1855629 1857211 := bstep (se 1 (by rfl) ⟨1392908, by rfl⟩ : syracuseStep 1857211 = 2785817) B2785817
theorem B17848025 : Blo 1855629 17848025 := bstep (se 2 (by rfl) ⟨6693009, by rfl⟩ : syracuseStep 17848025 = 13386019) B13386019
theorem B7051009 : Blo 1855629 7051009 := bstep (se 2 (by rfl) ⟨2644128, by rfl⟩ : syracuseStep 7051009 = 5288257) B5288257
theorem B1857287 : Blo 1855629 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B1857295 : Blo 1855629 1857295 := bstep (se 1 (by rfl) ⟨1392971, by rfl⟩ : syracuseStep 1857295 = 2785943) B2785943
theorem B5289761 : Blo 1855629 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B4175675 : Blo 1855629 4175675 := bstep (se 1 (by rfl) ⟨3131756, by rfl⟩ : syracuseStep 4175675 = 6263513) B6263513
theorem B1857339 : Blo 1855629 1857339 := bstep (se 1 (by rfl) ⟨1393004, by rfl⟩ : syracuseStep 1857339 = 2786009) B2786009
theorem B1857415 : Blo 1855629 1857415 := bstep (se 1 (by rfl) ⟨1393061, by rfl⟩ : syracuseStep 1857415 = 2786123) B2786123
theorem B1857423 : Blo 1855629 1857423 := bstep (se 1 (by rfl) ⟨1393067, by rfl⟩ : syracuseStep 1857423 = 2786135) B2786135
theorem B4175801 : Blo 1855629 4175801 := bstep (se 2 (by rfl) ⟨1565925, by rfl⟩ : syracuseStep 4175801 = 3131851) B3131851
theorem B1857467 : Blo 1855629 1857467 := bstep (se 1 (by rfl) ⟨1393100, by rfl⟩ : syracuseStep 1857467 = 2786201) B2786201
theorem B1857543 : Blo 1855629 1857543 := bstep (se 1 (by rfl) ⟨1393157, by rfl⟩ : syracuseStep 1857543 = 2786315) B2786315
theorem B1857551 : Blo 1855629 1857551 := bstep (se 1 (by rfl) ⟨1393163, by rfl⟩ : syracuseStep 1857551 = 2786327) B2786327
theorem B8468509 : Blo 1855629 8468509 := bstep (se 3 (by rfl) ⟨1587845, by rfl⟩ : syracuseStep 8468509 = 3175691) B3175691
theorem B1857595 : Blo 1855629 1857595 := bstep (se 1 (by rfl) ⟨1393196, by rfl⟩ : syracuseStep 1857595 = 2786393) B2786393
theorem B2783495 : Blo 1855629 2783495 := bstep (se 1 (by rfl) ⟨2087621, by rfl⟩ : syracuseStep 2783495 = 4175243) B4175243
theorem B2349319 : Blo 1855629 2349319 := bstep (se 1 (by rfl) ⟨1761989, by rfl⟩ : syracuseStep 2349319 = 3523979) B3523979
theorem B4176143 : Blo 1855629 4176143 := bstep (se 1 (by rfl) ⟨3132107, by rfl⟩ : syracuseStep 4176143 = 6264215) B6264215
theorem B4176161 : Blo 1855629 4176161 := bstep (se 2 (by rfl) ⟨1566060, by rfl⟩ : syracuseStep 4176161 = 3132121) B3132121
theorem B2783531 : Blo 1855629 2783531 := bstep (se 1 (by rfl) ⟨2087648, by rfl⟩ : syracuseStep 2783531 = 4175297) B4175297
theorem B2783561 : Blo 1855629 2783561 := bstep (se 2 (by rfl) ⟨1043835, by rfl⟩ : syracuseStep 2783561 = 2087671) B2087671
theorem B4700531 : Blo 1855629 4700531 := bstep (se 1 (by rfl) ⟨3525398, by rfl⟩ : syracuseStep 4700531 = 7050797) B7050797
theorem B4462967 : Blo 1855629 4462967 := bstep (se 1 (by rfl) ⟨3347225, by rfl⟩ : syracuseStep 4462967 = 6694451) B6694451
theorem B4700551 : Blo 1855629 4700551 := bstep (se 1 (by rfl) ⟨3525413, by rfl⟩ : syracuseStep 4700551 = 7050827) B7050827
theorem B6265241 : Blo 1855629 6265241 := bstep (se 2 (by rfl) ⟨2349465, by rfl⟩ : syracuseStep 6265241 = 4698931) B4698931
theorem B2783675 : Blo 1855629 2783675 := bstep (se 1 (by rfl) ⟨2087756, by rfl⟩ : syracuseStep 2783675 = 4175513) B4175513
theorem B22575581 : Blo 1855629 22575581 := bstep (se 3 (by rfl) ⟨4232921, by rfl⟩ : syracuseStep 22575581 = 8465843) B8465843
theorem B2783735 : Blo 1855629 2783735 := bstep (se 1 (by rfl) ⟨2087801, by rfl⟩ : syracuseStep 2783735 = 4175603) B4175603
theorem B15858179 : Blo 1855629 15858179 := bstep (se 1 (by rfl) ⟨11893634, by rfl⟩ : syracuseStep 15858179 = 23787269) B23787269
theorem B2783759 : Blo 1855629 2783759 := bstep (se 1 (by rfl) ⟨2087819, by rfl⟩ : syracuseStep 2783759 = 4175639) B4175639
theorem B2783801 : Blo 1855629 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B4176503 : Blo 1855629 4176503 := bstep (se 1 (by rfl) ⟨3132377, by rfl⟩ : syracuseStep 4176503 = 6264755) B6264755
theorem B2783879 : Blo 1855629 2783879 := bstep (se 1 (by rfl) ⟨2087909, by rfl⟩ : syracuseStep 2783879 = 4175819) B4175819
theorem B4700825 : Blo 1855629 4700825 := bstep (se 2 (by rfl) ⟨1762809, by rfl⟩ : syracuseStep 4700825 = 3525619) B3525619
theorem B2783915 : Blo 1855629 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B2349739 : Blo 1855629 2349739 := bstep (se 1 (by rfl) ⟨1762304, by rfl⟩ : syracuseStep 2349739 = 3524609) B3524609
theorem B10574509 : Blo 1855629 10574509 := bstep (se 3 (by rfl) ⟨1982720, by rfl⟩ : syracuseStep 10574509 = 3965441) B3965441
theorem B5085881 : Blo 1855629 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B2783945 : Blo 1855629 2783945 := bstep (se 2 (by rfl) ⟨1043979, by rfl⟩ : syracuseStep 2783945 = 2087959) B2087959
theorem B4176683 : Blo 1855629 4176683 := bstep (se 1 (by rfl) ⟨3132512, by rfl⟩ : syracuseStep 4176683 = 6265025) B6265025
theorem B2784059 : Blo 1855629 2784059 := bstep (se 1 (by rfl) ⟨2088044, by rfl⟩ : syracuseStep 2784059 = 4176089) B4176089
theorem B4700987 : Blo 1855629 4700987 := bstep (se 1 (by rfl) ⟨3525740, by rfl⟩ : syracuseStep 4700987 = 7051481) B7051481
theorem B10722107 : Blo 1855629 10722107 := bstep (se 1 (by rfl) ⟨8041580, by rfl⟩ : syracuseStep 10722107 = 16083161) B16083161
theorem B2784119 : Blo 1855629 2784119 := bstep (se 1 (by rfl) ⟨2088089, by rfl⟩ : syracuseStep 2784119 = 4176179) B4176179
theorem B2087815 : Blo 1855629 2087815 := bstep (se 1 (by rfl) ⟨1565861, by rfl⟩ : syracuseStep 2087815 = 3131723) B3131723
theorem B2382727 : Blo 1855629 2382727 := bstep (se 1 (by rfl) ⟨1787045, by rfl⟩ : syracuseStep 2382727 = 3574091) B3574091
theorem B2784143 : Blo 1855629 2784143 := bstep (se 1 (by rfl) ⟨2088107, by rfl⟩ : syracuseStep 2784143 = 4176215) B4176215
theorem B2349967 : Blo 1855629 2349967 := bstep (se 1 (by rfl) ⟨1762475, by rfl⟩ : syracuseStep 2349967 = 3524951) B3524951
theorem B9403289 : Blo 1855629 9403289 := bstep (se 2 (by rfl) ⟨3526233, by rfl⟩ : syracuseStep 9403289 = 7052467) B7052467
theorem B33889205 : Blo 1855629 33889205 := bstep (se 5 (by rfl) ⟨1588556, by rfl⟩ : syracuseStep 33889205 = 3177113) B3177113
theorem B2784185 : Blo 1855629 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B2784263 : Blo 1855629 2784263 := bstep (se 1 (by rfl) ⟨2088197, by rfl⟩ : syracuseStep 2784263 = 4176395) B4176395
theorem B4701199 : Blo 1855629 4701199 := bstep (se 1 (by rfl) ⟨3525899, by rfl⟩ : syracuseStep 4701199 = 7051799) B7051799
theorem B10034219 : Blo 1855629 10034219 := bstep (se 1 (by rfl) ⟨7525664, by rfl⟩ : syracuseStep 10034219 = 15051329) B15051329
theorem B2784299 : Blo 1855629 2784299 := bstep (se 1 (by rfl) ⟨2088224, by rfl⟩ : syracuseStep 2784299 = 4176449) B4176449
theorem B2087995 : Blo 1855629 2087995 := bstep (se 1 (by rfl) ⟨1565996, by rfl⟩ : syracuseStep 2087995 = 3131993) B3131993
theorem B2784329 : Blo 1855629 2784329 := bstep (se 2 (by rfl) ⟨1044123, by rfl⟩ : syracuseStep 2784329 = 2088247) B2088247
theorem B6265943 : Blo 1855629 6265943 := bstep (se 1 (by rfl) ⟨4699457, by rfl⟩ : syracuseStep 6265943 = 9398915) B9398915
theorem B4177043 : Blo 1855629 4177043 := bstep (se 1 (by rfl) ⟨3132782, by rfl⟩ : syracuseStep 4177043 = 6265565) B6265565
theorem B1981627 : Blo 1855629 1981627 := bstep (se 1 (by rfl) ⟨1486220, by rfl⟩ : syracuseStep 1981627 = 2972441) B2972441
theorem B2784443 : Blo 1855629 2784443 := bstep (se 1 (by rfl) ⟨2088332, by rfl⟩ : syracuseStep 2784443 = 4176665) B4176665
theorem B4177097 : Blo 1855629 4177097 := bstep (se 2 (by rfl) ⟨1566411, by rfl⟩ : syracuseStep 4177097 = 3132823) B3132823
theorem B2784503 : Blo 1855629 2784503 := bstep (se 1 (by rfl) ⟨2088377, by rfl⟩ : syracuseStep 2784503 = 4176755) B4176755
theorem B2784527 : Blo 1855629 2784527 := bstep (se 1 (by rfl) ⟨2088395, by rfl⟩ : syracuseStep 2784527 = 4176791) B4176791
theorem B4701473 : Blo 1855629 4701473 := bstep (se 2 (by rfl) ⟨1763052, by rfl⟩ : syracuseStep 4701473 = 3526105) B3526105
theorem B2784569 : Blo 1855629 2784569 := bstep (se 2 (by rfl) ⟨1044213, by rfl⟩ : syracuseStep 2784569 = 2088427) B2088427
theorem B19045763 : Blo 1855629 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B2784647 : Blo 1855629 2784647 := bstep (se 1 (by rfl) ⟨2088485, by rfl⟩ : syracuseStep 2784647 = 4176971) B4176971
theorem B2784683 : Blo 1855629 2784683 := bstep (se 1 (by rfl) ⟨2088512, by rfl⟩ : syracuseStep 2784683 = 4177025) B4177025
theorem B2784713 : Blo 1855629 2784713 := bstep (se 2 (by rfl) ⟨1044267, by rfl⟩ : syracuseStep 2784713 = 2088535) B2088535
theorem B20340173 : Blo 1855629 20340173 := bstep (se 3 (by rfl) ⟨3813782, by rfl⟩ : syracuseStep 20340173 = 7627565) B7627565
theorem B5021185 : Blo 1855629 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B2088463 : Blo 1855629 2088463 := bstep (se 1 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 2088463 = 3132695) B3132695
theorem B2784827 : Blo 1855629 2784827 := bstep (se 1 (by rfl) ⟨2088620, by rfl⟩ : syracuseStep 2784827 = 4177241) B4177241
theorem B6266429 : Blo 1855629 6266429 := bstep (se 3 (by rfl) ⟨1174955, by rfl⟩ : syracuseStep 6266429 = 2349911) B2349911
theorem B2784887 : Blo 1855629 2784887 := bstep (se 1 (by rfl) ⟨2088665, by rfl⟩ : syracuseStep 2784887 = 4177331) B4177331
theorem B2350711 : Blo 1855629 2350711 := bstep (se 1 (by rfl) ⟨1763033, by rfl⟩ : syracuseStep 2350711 = 3526067) B3526067
theorem B2784911 : Blo 1855629 2784911 := bstep (se 1 (by rfl) ⟨2088683, by rfl⟩ : syracuseStep 2784911 = 4177367) B4177367
theorem B2784953 : Blo 1855629 2784953 := bstep (se 2 (by rfl) ⟨1044357, by rfl⟩ : syracuseStep 2784953 = 2088715) B2088715
theorem B4292281 : Blo 1855629 4292281 := bstep (se 2 (by rfl) ⟨1609605, by rfl⟩ : syracuseStep 4292281 = 3219211) B3219211
theorem B2785031 : Blo 1855629 2785031 := bstep (se 1 (by rfl) ⟨2088773, by rfl⟩ : syracuseStep 2785031 = 4177547) B4177547
theorem B2514695 : Blo 1855629 2514695 := bstep (se 1 (by rfl) ⟨1886021, by rfl⟩ : syracuseStep 2514695 = 3772043) B3772043
theorem B2785067 : Blo 1855629 2785067 := bstep (se 1 (by rfl) ⟨2088800, by rfl⟩ : syracuseStep 2785067 = 4177601) B4177601
theorem B2785097 : Blo 1855629 2785097 := bstep (se 2 (by rfl) ⟨1044411, by rfl⟩ : syracuseStep 2785097 = 2088823) B2088823
theorem B4177799 : Blo 1855629 4177799 := bstep (se 1 (by rfl) ⟨3133349, by rfl⟩ : syracuseStep 4177799 = 6266699) B6266699
theorem B2785211 : Blo 1855629 2785211 := bstep (se 1 (by rfl) ⟨2088908, by rfl⟩ : syracuseStep 2785211 = 4177817) B4177817
theorem B2351035 : Blo 1855629 2351035 := bstep (se 1 (by rfl) ⟨1763276, by rfl⟩ : syracuseStep 2351035 = 3526553) B3526553
theorem B2785271 : Blo 1855629 2785271 := bstep (se 1 (by rfl) ⟨2088953, by rfl⟩ : syracuseStep 2785271 = 4177907) B4177907
theorem B2785289 : Blo 1855629 2785289 := bstep (se 2 (by rfl) ⟨1044483, by rfl⟩ : syracuseStep 2785289 = 2088967) B2088967
theorem B2785319 : Blo 1855629 2785319 := bstep (se 1 (by rfl) ⟨2088989, by rfl⟩ : syracuseStep 2785319 = 4177979) B4177979
theorem B2089039 : Blo 1855629 2089039 := bstep (se 1 (by rfl) ⟨1566779, by rfl⟩ : syracuseStep 2089039 = 3133559) B3133559
theorem B2785403 : Blo 1855629 2785403 := bstep (se 1 (by rfl) ⟨2089052, by rfl⟩ : syracuseStep 2785403 = 4178105) B4178105
theorem B2785529 : Blo 1855629 2785529 := bstep (se 2 (by rfl) ⟨1044573, by rfl⟩ : syracuseStep 2785529 = 2089147) B2089147
theorem B31711499 : Blo 1855629 31711499 := bstep (se 1 (by rfl) ⟨23783624, by rfl⟩ : syracuseStep 31711499 = 47567249) B47567249
theorem B7930199 : Blo 1855629 7930199 := bstep (se 1 (by rfl) ⟨5947649, by rfl⟩ : syracuseStep 7930199 = 11895299) B11895299
theorem B2785631 : Blo 1855629 2785631 := bstep (se 1 (by rfl) ⟨2089223, by rfl⟩ : syracuseStep 2785631 = 4178447) B4178447
theorem B3522923 : Blo 1855629 3522923 := bstep (se 1 (by rfl) ⟨2642192, by rfl⟩ : syracuseStep 3522923 = 5284385) B5284385
theorem B2785643 : Blo 1855629 2785643 := bstep (se 1 (by rfl) ⟨2089232, by rfl⟩ : syracuseStep 2785643 = 4178465) B4178465
theorem B3572129 : Blo 1855629 3572129 := bstep (se 2 (by rfl) ⟨1339548, by rfl⟩ : syracuseStep 3572129 = 2679097) B2679097
theorem B2941367 : Blo 1855629 2941367 := bstep (se 1 (by rfl) ⟨2206025, by rfl⟩ : syracuseStep 2941367 = 4412051) B4412051
theorem B2089435 : Blo 1855629 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem B6267401 : Blo 1855629 6267401 := bstep (se 2 (by rfl) ⟨2350275, by rfl⟩ : syracuseStep 6267401 = 4700551) B4700551
theorem B3523151 : Blo 1855629 3523151 := bstep (se 1 (by rfl) ⟨2642363, by rfl⟩ : syracuseStep 3523151 = 5284727) B5284727
theorem B2785871 : Blo 1855629 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B4178555 : Blo 1855629 4178555 := bstep (se 1 (by rfl) ⟨3133916, by rfl⟩ : syracuseStep 4178555 = 6267833) B6267833
theorem B2785991 : Blo 1855629 2785991 := bstep (se 1 (by rfl) ⟨2089493, by rfl⟩ : syracuseStep 2785991 = 4178987) B4178987
theorem B3572435 : Blo 1855629 3572435 := bstep (se 1 (by rfl) ⟨2679326, by rfl⟩ : syracuseStep 3572435 = 5358653) B5358653
theorem B6693587 : Blo 1855629 6693587 := bstep (se 1 (by rfl) ⟨5020190, by rfl⟩ : syracuseStep 6693587 = 10040381) B10040381
theorem B4178681 : Blo 1855629 4178681 := bstep (se 2 (by rfl) ⟨1567005, by rfl⟩ : syracuseStep 4178681 = 3134011) B3134011
theorem B4129609 : Blo 1855629 4129609 := bstep (se 2 (by rfl) ⟨1548603, by rfl⟩ : syracuseStep 4129609 = 3097207) B3097207
theorem B9528137 : Blo 1855629 9528137 := bstep (se 2 (by rfl) ⟨3573051, by rfl⟩ : syracuseStep 9528137 = 7146103) B7146103
theorem B5284703 : Blo 1855629 5284703 := bstep (se 1 (by rfl) ⟨3963527, by rfl⟩ : syracuseStep 5284703 = 7927055) B7927055
theorem B2786153 : Blo 1855629 2786153 := bstep (se 2 (by rfl) ⟨1044807, by rfl⟩ : syracuseStep 2786153 = 2089615) B2089615
theorem B14099345 : Blo 1855629 14099345 := bstep (se 2 (by rfl) ⟨5287254, by rfl⟩ : syracuseStep 14099345 = 10574509) B10574509
theorem B2974639 : Blo 1855629 2974639 := bstep (se 1 (by rfl) ⟨2230979, by rfl⟩ : syracuseStep 2974639 = 4461959) B4461959
theorem B2786231 : Blo 1855629 2786231 := bstep (se 1 (by rfl) ⟨2089673, by rfl⟩ : syracuseStep 2786231 = 4179347) B4179347
theorem B2786267 : Blo 1855629 2786267 := bstep (se 1 (by rfl) ⟨2089700, by rfl⟩ : syracuseStep 2786267 = 4179401) B4179401
theorem B10568677 : Blo 1855629 10568677 := bstep (se 4 (by rfl) ⟨990813, by rfl⟩ : syracuseStep 10568677 = 1981627) B1981627
theorem B3523591 : Blo 1855629 3523591 := bstep (se 1 (by rfl) ⟨2642693, by rfl⟩ : syracuseStep 3523591 = 5285387) B5285387
theorem B4178951 : Blo 1855629 4178951 := bstep (se 1 (by rfl) ⟨3134213, by rfl⟩ : syracuseStep 4178951 = 6268427) B6268427
theorem B4179023 : Blo 1855629 4179023 := bstep (se 1 (by rfl) ⟨3134267, by rfl⟩ : syracuseStep 4179023 = 6268535) B6268535
theorem B54240461 : Blo 1855629 54240461 := bstep (se 3 (by rfl) ⟨10170086, by rfl⟩ : syracuseStep 54240461 = 20340173) B20340173
theorem B10568951 : Blo 1855629 10568951 := bstep (se 1 (by rfl) ⟨7926713, by rfl⟩ : syracuseStep 10568951 = 15853427) B15853427
theorem B5948777 : Blo 1855629 5948777 := bstep (se 2 (by rfl) ⟨2230791, by rfl⟩ : syracuseStep 5948777 = 4461583) B4461583
theorem B6268265 : Blo 1855629 6268265 := bstep (se 2 (by rfl) ⟨2350599, by rfl⟩ : syracuseStep 6268265 = 4701199) B4701199
theorem B4179419 : Blo 1855629 4179419 := bstep (se 1 (by rfl) ⟨3134564, by rfl⟩ : syracuseStep 4179419 = 6269129) B6269129
theorem B10569203 : Blo 1855629 10569203 := bstep (se 1 (by rfl) ⟨7926902, by rfl⟩ : syracuseStep 10569203 = 15853805) B15853805
theorem B2975311 : Blo 1855629 2975311 := bstep (se 1 (by rfl) ⟨2231483, by rfl⟩ : syracuseStep 2975311 = 4462967) B4462967
theorem B15050387 : Blo 1855629 15050387 := bstep (se 1 (by rfl) ⟨11287790, by rfl⟩ : syracuseStep 15050387 = 22575581) B22575581
theorem B6268859 : Blo 1855629 6268859 := bstep (se 1 (by rfl) ⟨4701644, by rfl⟩ : syracuseStep 6268859 = 9403289) B9403289
theorem B6694913 : Blo 1855629 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B3131399 : Blo 1855629 3131399 := bstep (se 1 (by rfl) ⟨2348549, by rfl⟩ : syracuseStep 3131399 = 4697099) B4697099
theorem B3524647 : Blo 1855629 3524647 := bstep (se 1 (by rfl) ⟨2643485, by rfl⟩ : syracuseStep 3524647 = 5286971) B5286971
theorem B9398429 : Blo 1855629 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B5359787 : Blo 1855629 5359787 := bstep (se 1 (by rfl) ⟨4019840, by rfl⟩ : syracuseStep 5359787 = 8039681) B8039681
theorem B3131743 : Blo 1855629 3131743 := bstep (se 1 (by rfl) ⟨2348807, by rfl⟩ : syracuseStep 3131743 = 4697615) B4697615
theorem B3131831 : Blo 1855629 3131831 := bstep (se 1 (by rfl) ⟨2348873, by rfl⟩ : syracuseStep 3131831 = 4697747) B4697747
theorem B2230907 : Blo 1855629 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B11291345 : Blo 1855629 11291345 := bstep (se 2 (by rfl) ⟨4234254, by rfl⟩ : syracuseStep 11291345 = 8468509) B8468509
theorem B26823413 : Blo 1855629 26823413 := bstep (se 5 (by rfl) ⟨1257347, by rfl⟩ : syracuseStep 26823413 = 2514695) B2514695
theorem B3763163 : Blo 1855629 3763163 := bstep (se 1 (by rfl) ⟨2822372, by rfl⟩ : syracuseStep 3763163 = 5644745) B5644745
theorem B14298113 : Blo 1855629 14298113 := bstep (se 2 (by rfl) ⟨5361792, by rfl⟩ : syracuseStep 14298113 = 10723585) B10723585
theorem B3132425 : Blo 1855629 3132425 := bstep (se 2 (by rfl) ⟨1174659, by rfl⟩ : syracuseStep 3132425 = 2349319) B2349319
theorem B13380659 : Blo 1855629 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B3132587 : Blo 1855629 3132587 := bstep (se 1 (by rfl) ⟨2349440, by rfl⟩ : syracuseStep 3132587 = 4698881) B4698881
theorem B45157571 : Blo 1855629 45157571 := bstep (se 1 (by rfl) ⟨33868178, by rfl⟩ : syracuseStep 45157571 = 67736357) B67736357
theorem B14101775 : Blo 1855629 14101775 := bstep (se 1 (by rfl) ⟨10576331, by rfl⟩ : syracuseStep 14101775 = 21152663) B21152663
theorem B5016937 : Blo 1855629 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B4697473 : Blo 1855629 4697473 := bstep (se 2 (by rfl) ⟨1761552, by rfl⟩ : syracuseStep 4697473 = 3523105) B3523105
theorem B16944527 : Blo 1855629 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B9399725 : Blo 1855629 9399725 := bstep (se 3 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 9399725 = 3524897) B3524897
theorem B3132985 : Blo 1855629 3132985 := bstep (se 2 (by rfl) ⟨1174869, by rfl⟩ : syracuseStep 3132985 = 2349739) B2349739
theorem B8040059 : Blo 1855629 8040059 := bstep (se 1 (by rfl) ⟨6030044, by rfl⟩ : syracuseStep 8040059 = 12060089) B12060089
theorem B10038907 : Blo 1855629 10038907 := bstep (se 1 (by rfl) ⟨7529180, by rfl⟩ : syracuseStep 10038907 = 15058361) B15058361
theorem B22892165 : Blo 1855629 22892165 := bstep (se 4 (by rfl) ⟨2146140, by rfl⟩ : syracuseStep 22892165 = 4292281) B4292281
theorem B10571411 : Blo 1855629 10571411 := bstep (se 1 (by rfl) ⟨7928558, by rfl⟩ : syracuseStep 10571411 = 15857117) B15857117
theorem B3133127 : Blo 1855629 3133127 := bstep (se 1 (by rfl) ⟨2349845, by rfl⟩ : syracuseStep 3133127 = 4699691) B4699691
theorem B3526355 : Blo 1855629 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B11898683 : Blo 1855629 11898683 := bstep (se 1 (by rfl) ⟨8924012, by rfl⟩ : syracuseStep 11898683 = 17848025) B17848025
theorem B9662303 : Blo 1855629 9662303 := bstep (se 1 (by rfl) ⟨7246727, by rfl⟩ : syracuseStep 9662303 = 14493455) B14493455
theorem B3133289 : Blo 1855629 3133289 := bstep (se 2 (by rfl) ⟨1174983, by rfl⟩ : syracuseStep 3133289 = 2349967) B2349967
theorem B3526507 : Blo 1855629 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B15265655 : Blo 1855629 15265655 := bstep (se 1 (by rfl) ⟨11449241, by rfl⟩ : syracuseStep 15265655 = 22898483) B22898483
theorem B13570001 : Blo 1855629 13570001 := bstep (se 2 (by rfl) ⟨5088750, by rfl⟩ : syracuseStep 13570001 = 10177501) B10177501
theorem B7049369 : Blo 1855629 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B4698283 : Blo 1855629 4698283 := bstep (se 1 (by rfl) ⟨3523712, by rfl⟩ : syracuseStep 4698283 = 7047425) B7047425
theorem B1855663 : Blo 1855629 1855663 := bstep (se 1 (by rfl) ⟨1391747, by rfl⟩ : syracuseStep 1855663 = 2783495) B2783495
theorem B1855687 : Blo 1855629 1855687 := bstep (se 1 (by rfl) ⟨1391765, by rfl⟩ : syracuseStep 1855687 = 2783531) B2783531
theorem B1855707 : Blo 1855629 1855707 := bstep (se 1 (by rfl) ⟨1391780, by rfl⟩ : syracuseStep 1855707 = 2783561) B2783561
theorem B3133687 : Blo 1855629 3133687 := bstep (se 1 (by rfl) ⟨2350265, by rfl⟩ : syracuseStep 3133687 = 4700531) B4700531
theorem B21426443 : Blo 1855629 21426443 := bstep (se 1 (by rfl) ⟨16069832, by rfl⟩ : syracuseStep 21426443 = 32139665) B32139665
theorem B1855783 : Blo 1855629 1855783 := bstep (se 1 (by rfl) ⟨1391837, by rfl⟩ : syracuseStep 1855783 = 2783675) B2783675
theorem B1855823 : Blo 1855629 1855823 := bstep (se 1 (by rfl) ⟨1391867, by rfl⟩ : syracuseStep 1855823 = 2783735) B2783735
theorem B10572119 : Blo 1855629 10572119 := bstep (se 1 (by rfl) ⟨7929089, by rfl⟩ : syracuseStep 10572119 = 15858179) B15858179
theorem B1855839 : Blo 1855629 1855839 := bstep (se 1 (by rfl) ⟨1391879, by rfl⟩ : syracuseStep 1855839 = 2783759) B2783759
theorem B1855867 : Blo 1855629 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B1855919 : Blo 1855629 1855919 := bstep (se 1 (by rfl) ⟨1391939, by rfl⟩ : syracuseStep 1855919 = 2783879) B2783879
theorem B3133883 : Blo 1855629 3133883 := bstep (se 1 (by rfl) ⟨2350412, by rfl⟩ : syracuseStep 3133883 = 4700825) B4700825
theorem B1855943 : Blo 1855629 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B1855963 : Blo 1855629 1855963 := bstep (se 1 (by rfl) ⟨1391972, by rfl⟩ : syracuseStep 1855963 = 2783945) B2783945
theorem B4698587 : Blo 1855629 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B4461065 : Blo 1855629 4461065 := bstep (se 2 (by rfl) ⟨1672899, by rfl⟩ : syracuseStep 4461065 = 3345799) B3345799
theorem B1856039 : Blo 1855629 1856039 := bstep (se 1 (by rfl) ⟨1392029, by rfl⟩ : syracuseStep 1856039 = 2784059) B2784059
theorem B3133991 : Blo 1855629 3133991 := bstep (se 1 (by rfl) ⟨2350493, by rfl⟩ : syracuseStep 3133991 = 4700987) B4700987
theorem B7148071 : Blo 1855629 7148071 := bstep (se 1 (by rfl) ⟨5361053, by rfl⟩ : syracuseStep 7148071 = 10722107) B10722107
theorem B1856079 : Blo 1855629 1856079 := bstep (se 1 (by rfl) ⟨1392059, by rfl⟩ : syracuseStep 1856079 = 2784119) B2784119
theorem B1856095 : Blo 1855629 1856095 := bstep (se 1 (by rfl) ⟨1392071, by rfl⟩ : syracuseStep 1856095 = 2784143) B2784143
theorem B7049825 : Blo 1855629 7049825 := bstep (se 2 (by rfl) ⟨2643684, by rfl⟩ : syracuseStep 7049825 = 5287369) B5287369
theorem B1856123 : Blo 1855629 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B7926407 : Blo 1855629 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B1856175 : Blo 1855629 1856175 := bstep (se 1 (by rfl) ⟨1392131, by rfl⟩ : syracuseStep 1856175 = 2784263) B2784263
theorem B6689479 : Blo 1855629 6689479 := bstep (se 1 (by rfl) ⟨5017109, by rfl⟩ : syracuseStep 6689479 = 10034219) B10034219
theorem B1856199 : Blo 1855629 1856199 := bstep (se 1 (by rfl) ⟨1392149, by rfl⟩ : syracuseStep 1856199 = 2784299) B2784299
theorem B1856219 : Blo 1855629 1856219 := bstep (se 1 (by rfl) ⟨1392164, by rfl⟩ : syracuseStep 1856219 = 2784329) B2784329
theorem B1856295 : Blo 1855629 1856295 := bstep (se 1 (by rfl) ⟨1392221, by rfl⟩ : syracuseStep 1856295 = 2784443) B2784443
theorem B3134281 : Blo 1855629 3134281 := bstep (se 2 (by rfl) ⟨1175355, by rfl⟩ : syracuseStep 3134281 = 2350711) B2350711
theorem B1856335 : Blo 1855629 1856335 := bstep (se 1 (by rfl) ⟨1392251, by rfl⟩ : syracuseStep 1856335 = 2784503) B2784503
theorem B1856351 : Blo 1855629 1856351 := bstep (se 1 (by rfl) ⟨1392263, by rfl⟩ : syracuseStep 1856351 = 2784527) B2784527
theorem B3134315 : Blo 1855629 3134315 := bstep (se 1 (by rfl) ⟨2350736, by rfl⟩ : syracuseStep 3134315 = 4701473) B4701473
theorem B1856379 : Blo 1855629 1856379 := bstep (se 1 (by rfl) ⟨1392284, by rfl⟩ : syracuseStep 1856379 = 2784569) B2784569
theorem B1856431 : Blo 1855629 1856431 := bstep (se 1 (by rfl) ⟨1392323, by rfl⟩ : syracuseStep 1856431 = 2784647) B2784647
theorem B1881031 : Blo 1855629 1881031 := bstep (se 1 (by rfl) ⟨1410773, by rfl⟩ : syracuseStep 1881031 = 2821547) B2821547
theorem B1856455 : Blo 1855629 1856455 := bstep (se 1 (by rfl) ⟨1392341, by rfl⟩ : syracuseStep 1856455 = 2784683) B2784683
theorem B1856475 : Blo 1855629 1856475 := bstep (se 1 (by rfl) ⟨1392356, by rfl⟩ : syracuseStep 1856475 = 2784713) B2784713
theorem B9401345 : Blo 1855629 9401345 := bstep (se 2 (by rfl) ⟨3525504, by rfl⟩ : syracuseStep 9401345 = 7051009) B7051009
theorem B1856551 : Blo 1855629 1856551 := bstep (se 1 (by rfl) ⟨1392413, by rfl⟩ : syracuseStep 1856551 = 2784827) B2784827
theorem B1856591 : Blo 1855629 1856591 := bstep (se 1 (by rfl) ⟨1392443, by rfl⟩ : syracuseStep 1856591 = 2784887) B2784887
theorem B1856607 : Blo 1855629 1856607 := bstep (se 1 (by rfl) ⟨1392455, by rfl⟩ : syracuseStep 1856607 = 2784911) B2784911
theorem B17839223 : Blo 1855629 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B1856635 : Blo 1855629 1856635 := bstep (se 1 (by rfl) ⟨1392476, by rfl⟩ : syracuseStep 1856635 = 2784953) B2784953
theorem B1856687 : Blo 1855629 1856687 := bstep (se 1 (by rfl) ⟨1392515, by rfl⟩ : syracuseStep 1856687 = 2785031) B2785031
theorem B1856711 : Blo 1855629 1856711 := bstep (se 1 (by rfl) ⟨1392533, by rfl⟩ : syracuseStep 1856711 = 2785067) B2785067
theorem B15856843 : Blo 1855629 15856843 := bstep (se 1 (by rfl) ⟨11892632, by rfl⟩ : syracuseStep 15856843 = 23785265) B23785265
theorem B1856731 : Blo 1855629 1856731 := bstep (se 1 (by rfl) ⟨1392548, by rfl⟩ : syracuseStep 1856731 = 2785097) B2785097
theorem B8369399 : Blo 1855629 8369399 := bstep (se 1 (by rfl) ⟨6277049, by rfl⟩ : syracuseStep 8369399 = 12554099) B12554099
theorem B8467703 : Blo 1855629 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B13382903 : Blo 1855629 13382903 := bstep (se 1 (by rfl) ⟨10037177, by rfl⟩ : syracuseStep 13382903 = 20074355) B20074355
theorem B3134713 : Blo 1855629 3134713 := bstep (se 2 (by rfl) ⟨1175517, by rfl⟩ : syracuseStep 3134713 = 2351035) B2351035
theorem B1856807 : Blo 1855629 1856807 := bstep (se 1 (by rfl) ⟨1392605, by rfl⟩ : syracuseStep 1856807 = 2785211) B2785211
theorem B1856847 : Blo 1855629 1856847 := bstep (se 1 (by rfl) ⟨1392635, by rfl⟩ : syracuseStep 1856847 = 2785271) B2785271
theorem B1856863 : Blo 1855629 1856863 := bstep (se 1 (by rfl) ⟨1392647, by rfl⟩ : syracuseStep 1856863 = 2785295) B2785295
theorem B3175787 : Blo 1855629 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B1856891 : Blo 1855629 1856891 := bstep (se 1 (by rfl) ⟨1392668, by rfl⟩ : syracuseStep 1856891 = 2785337) B2785337
theorem B1856943 : Blo 1855629 1856943 := bstep (se 1 (by rfl) ⟨1392707, by rfl⟩ : syracuseStep 1856943 = 2785415) B2785415
theorem B1856967 : Blo 1855629 1856967 := bstep (se 1 (by rfl) ⟨1392725, by rfl⟩ : syracuseStep 1856967 = 2785451) B2785451
theorem B1856987 : Blo 1855629 1856987 := bstep (se 1 (by rfl) ⟨1392740, by rfl⟩ : syracuseStep 1856987 = 2785481) B2785481
theorem B4175369 : Blo 1855629 4175369 := bstep (se 2 (by rfl) ⟨1565763, by rfl⟩ : syracuseStep 4175369 = 3131527) B3131527
theorem B1857063 : Blo 1855629 1857063 := bstep (se 1 (by rfl) ⟨1392797, by rfl⟩ : syracuseStep 1857063 = 2785595) B2785595
theorem B1857103 : Blo 1855629 1857103 := bstep (se 1 (by rfl) ⟨1392827, by rfl⟩ : syracuseStep 1857103 = 2785655) B2785655
theorem B1857119 : Blo 1855629 1857119 := bstep (se 1 (by rfl) ⟨1392839, by rfl⟩ : syracuseStep 1857119 = 2785679) B2785679
theorem B1857147 : Blo 1855629 1857147 := bstep (se 1 (by rfl) ⟨1392860, by rfl⟩ : syracuseStep 1857147 = 2785721) B2785721
theorem B6690443 : Blo 1855629 6690443 := bstep (se 1 (by rfl) ⟨5017832, by rfl⟩ : syracuseStep 6690443 = 10035665) B10035665
theorem B1857199 : Blo 1855629 1857199 := bstep (se 1 (by rfl) ⟨1392899, by rfl⟩ : syracuseStep 1857199 = 2785799) B2785799
theorem B1857223 : Blo 1855629 1857223 := bstep (se 1 (by rfl) ⟨1392917, by rfl⟩ : syracuseStep 1857223 = 2785835) B2785835
theorem B1857243 : Blo 1855629 1857243 := bstep (se 1 (by rfl) ⟨1392932, by rfl⟩ : syracuseStep 1857243 = 2785865) B2785865
theorem B1857319 : Blo 1855629 1857319 := bstep (se 1 (by rfl) ⟨1392989, by rfl⟩ : syracuseStep 1857319 = 2785979) B2785979
theorem B23779115 : Blo 1855629 23779115 := bstep (se 1 (by rfl) ⟨17834336, by rfl⟩ : syracuseStep 23779115 = 35668673) B35668673
theorem B9402155 : Blo 1855629 9402155 := bstep (se 1 (by rfl) ⟨7051616, by rfl⟩ : syracuseStep 9402155 = 14103233) B14103233
theorem B1857359 : Blo 1855629 1857359 := bstep (se 1 (by rfl) ⟨1393019, by rfl⟩ : syracuseStep 1857359 = 2786039) B2786039
theorem B4175711 : Blo 1855629 4175711 := bstep (se 1 (by rfl) ⟨3131783, by rfl⟩ : syracuseStep 4175711 = 6263567) B6263567
theorem B1857375 : Blo 1855629 1857375 := bstep (se 1 (by rfl) ⟨1393031, by rfl⟩ : syracuseStep 1857375 = 2786063) B2786063
theorem B5019499 : Blo 1855629 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B1857403 : Blo 1855629 1857403 := bstep (se 1 (by rfl) ⟨1393052, by rfl⟩ : syracuseStep 1857403 = 2786105) B2786105
theorem B4700065 : Blo 1855629 4700065 := bstep (se 2 (by rfl) ⟨1762524, by rfl⟩ : syracuseStep 4700065 = 3525049) B3525049
theorem B1857455 : Blo 1855629 1857455 := bstep (se 1 (by rfl) ⟨1393091, by rfl⟩ : syracuseStep 1857455 = 2786183) B2786183
theorem B7927739 : Blo 1855629 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B1857479 : Blo 1855629 1857479 := bstep (se 1 (by rfl) ⟨1393109, by rfl⟩ : syracuseStep 1857479 = 2786219) B2786219
theorem B1857499 : Blo 1855629 1857499 := bstep (se 1 (by rfl) ⟨1393124, by rfl⟩ : syracuseStep 1857499 = 2786249) B2786249
theorem B14293007 : Blo 1855629 14293007 := bstep (se 1 (by rfl) ⟨10719755, by rfl⟩ : syracuseStep 14293007 = 21439511) B21439511
theorem B4175891 : Blo 1855629 4175891 := bstep (se 1 (by rfl) ⟨3131918, by rfl⟩ : syracuseStep 4175891 = 6263837) B6263837
theorem B7051283 : Blo 1855629 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B1857575 : Blo 1855629 1857575 := bstep (se 1 (by rfl) ⟨1393181, by rfl⟩ : syracuseStep 1857575 = 2786363) B2786363
theorem B1857615 : Blo 1855629 1857615 := bstep (se 1 (by rfl) ⟨1393211, by rfl⟩ : syracuseStep 1857615 = 2786423) B2786423
theorem B10721369 : Blo 1855629 10721369 := bstep (se 2 (by rfl) ⟨4020513, by rfl⟩ : syracuseStep 10721369 = 8041027) B8041027
theorem B14104691 : Blo 1855629 14104691 := bstep (se 1 (by rfl) ⟨10578518, by rfl⟩ : syracuseStep 14104691 = 21157037) B21157037
theorem B16939165 : Blo 1855629 16939165 := bstep (se 3 (by rfl) ⟨3176093, by rfl⟩ : syracuseStep 16939165 = 6352187) B6352187
theorem B6265079 : Blo 1855629 6265079 := bstep (se 1 (by rfl) ⟨4698809, by rfl⟩ : syracuseStep 6265079 = 9397619) B9397619
theorem B11893043 : Blo 1855629 11893043 := bstep (se 1 (by rfl) ⟨8919782, by rfl⟩ : syracuseStep 11893043 = 17839565) B17839565
theorem B20085043 : Blo 1855629 20085043 := bstep (se 1 (by rfl) ⟨15063782, by rfl⟩ : syracuseStep 20085043 = 30127565) B30127565
theorem B4176233 : Blo 1855629 4176233 := bstep (se 2 (by rfl) ⟨1566087, by rfl⟩ : syracuseStep 4176233 = 3132175) B3132175
theorem B2783663 : Blo 1855629 2783663 := bstep (se 1 (by rfl) ⟨2087747, by rfl⟩ : syracuseStep 2783663 = 4175495) B4175495
theorem B2783753 : Blo 1855629 2783753 := bstep (se 2 (by rfl) ⟨1043907, by rfl⟩ : syracuseStep 2783753 = 2087815) B2087815
theorem B3176969 : Blo 1855629 3176969 := bstep (se 2 (by rfl) ⟨1191363, by rfl⟩ : syracuseStep 3176969 = 2382727) B2382727
theorem B4463113 : Blo 1855629 4463113 := bstep (se 2 (by rfl) ⟨1673667, by rfl⟩ : syracuseStep 4463113 = 3347335) B3347335
theorem B2783783 : Blo 1855629 2783783 := bstep (se 1 (by rfl) ⟨2087837, by rfl⟩ : syracuseStep 2783783 = 4175675) B4175675
theorem B6265403 : Blo 1855629 6265403 := bstep (se 1 (by rfl) ⟨4699052, by rfl⟩ : syracuseStep 6265403 = 9398105) B9398105
theorem B2783867 : Blo 1855629 2783867 := bstep (se 1 (by rfl) ⟨2087900, by rfl⟩ : syracuseStep 2783867 = 4175801) B4175801
theorem B2783993 : Blo 1855629 2783993 := bstep (se 2 (by rfl) ⟨1043997, by rfl⟩ : syracuseStep 2783993 = 2087995) B2087995
theorem B6265673 : Blo 1855629 6265673 := bstep (se 2 (by rfl) ⟨2349627, by rfl⟩ : syracuseStep 6265673 = 4699255) B4699255
theorem B2784095 : Blo 1855629 2784095 := bstep (se 1 (by rfl) ⟨2088071, by rfl⟩ : syracuseStep 2784095 = 4176143) B4176143
theorem B2784107 : Blo 1855629 2784107 := bstep (se 1 (by rfl) ⟨2088080, by rfl⟩ : syracuseStep 2784107 = 4176161) B4176161
theorem B4176827 : Blo 1855629 4176827 := bstep (se 1 (by rfl) ⟨3132620, by rfl⟩ : syracuseStep 4176827 = 6265241) B6265241
theorem B4176953 : Blo 1855629 4176953 := bstep (se 2 (by rfl) ⟨1566357, by rfl⟩ : syracuseStep 4176953 = 3132715) B3132715
theorem B2784335 : Blo 1855629 2784335 := bstep (se 1 (by rfl) ⟨2088251, by rfl⟩ : syracuseStep 2784335 = 4176503) B4176503
theorem B3390587 : Blo 1855629 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2784455 : Blo 1855629 2784455 := bstep (se 1 (by rfl) ⟨2088341, by rfl⟩ : syracuseStep 2784455 = 4176683) B4176683
theorem B22592803 : Blo 1855629 22592803 := bstep (se 1 (by rfl) ⟨16944602, by rfl⟩ : syracuseStep 22592803 = 33889205) B33889205
theorem B2784617 : Blo 1855629 2784617 := bstep (se 2 (by rfl) ⟨1044231, by rfl⟩ : syracuseStep 2784617 = 2088463) B2088463
theorem B4177295 : Blo 1855629 4177295 := bstep (se 1 (by rfl) ⟨3132971, by rfl⟩ : syracuseStep 4177295 = 6265943) B6265943
theorem B2784695 : Blo 1855629 2784695 := bstep (se 1 (by rfl) ⟨2088521, by rfl⟩ : syracuseStep 2784695 = 4177043) B4177043
theorem B9395675 : Blo 1855629 9395675 := bstep (se 1 (by rfl) ⟨7046756, by rfl⟩ : syracuseStep 9395675 = 14093513) B14093513
theorem B2784731 : Blo 1855629 2784731 := bstep (se 1 (by rfl) ⟨2088548, by rfl⟩ : syracuseStep 2784731 = 4177097) B4177097
theorem B60218909 : Blo 1855629 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B2973223 : Blo 1855629 2973223 := bstep (se 1 (by rfl) ⟨2229917, by rfl⟩ : syracuseStep 2973223 = 4459835) B4459835
theorem B12697175 : Blo 1855629 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B2088571 : Blo 1855629 2088571 := bstep (se 1 (by rfl) ⟨1566428, by rfl⟩ : syracuseStep 2088571 = 3132857) B3132857
theorem B7052939 : Blo 1855629 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B4177619 : Blo 1855629 4177619 := bstep (se 1 (by rfl) ⟨3133214, by rfl⟩ : syracuseStep 4177619 = 6266429) B6266429
theorem B2785199 : Blo 1855629 2785199 := bstep (se 1 (by rfl) ⟨2088899, by rfl⟩ : syracuseStep 2785199 = 4177799) B4177799
theorem B6266807 : Blo 1855629 6266807 := bstep (se 1 (by rfl) ⟨4700105, by rfl⟩ : syracuseStep 6266807 = 9400211) B9400211
theorem B9396161 : Blo 1855629 9396161 := bstep (se 2 (by rfl) ⟨3523560, by rfl⟩ : syracuseStep 9396161 = 7047121) B7047121
theorem B2785385 : Blo 1855629 2785385 := bstep (se 2 (by rfl) ⟨1044519, by rfl⟩ : syracuseStep 2785385 = 2089039) B2089039
theorem B22585553 : Blo 1855629 22585553 := bstep (se 2 (by rfl) ⟨8469582, by rfl⟩ : syracuseStep 22585553 = 16939165) B16939165
theorem B28590317 : Blo 1855629 28590317 := bstep (se 3 (by rfl) ⟨5360684, by rfl⟩ : syracuseStep 28590317 = 10721369) B10721369
theorem B2089255 : Blo 1855629 2089255 := bstep (se 1 (by rfl) ⟨1566941, by rfl⟩ : syracuseStep 2089255 = 3133883) B3133883
theorem B4178249 : Blo 1855629 4178249 := bstep (se 2 (by rfl) ⟨1566843, by rfl⟩ : syracuseStep 4178249 = 3133687) B3133687
theorem B2974043 : Blo 1855629 2974043 := bstep (se 1 (by rfl) ⟨2230532, by rfl⟩ : syracuseStep 2974043 = 4461065) B4461065
theorem B4178267 : Blo 1855629 4178267 := bstep (se 1 (by rfl) ⟨3133700, by rfl⟩ : syracuseStep 4178267 = 6267401) B6267401
theorem B2089327 : Blo 1855629 2089327 := bstep (se 1 (by rfl) ⟨1566995, by rfl⟩ : syracuseStep 2089327 = 3133991) B3133991
theorem B26780057 : Blo 1855629 26780057 := bstep (se 2 (by rfl) ⟨10042521, by rfl⟩ : syracuseStep 26780057 = 20085043) B20085043
theorem B15868325 : Blo 1855629 15868325 := bstep (se 4 (by rfl) ⟨1487655, by rfl⟩ : syracuseStep 15868325 = 2975311) B2975311
theorem B2785703 : Blo 1855629 2785703 := bstep (se 1 (by rfl) ⟨2089277, by rfl⟩ : syracuseStep 2785703 = 4178555) B4178555
theorem B5284271 : Blo 1855629 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B2785787 : Blo 1855629 2785787 := bstep (se 1 (by rfl) ⟨2089340, by rfl⟩ : syracuseStep 2785787 = 4178681) B4178681
theorem B2089543 : Blo 1855629 2089543 := bstep (se 1 (by rfl) ⟨1567157, by rfl⟩ : syracuseStep 2089543 = 3134315) B3134315
theorem B2785913 : Blo 1855629 2785913 := bstep (se 2 (by rfl) ⟨1044717, by rfl⟩ : syracuseStep 2785913 = 2089435) B2089435
theorem B6267563 : Blo 1855629 6267563 := bstep (se 1 (by rfl) ⟨4700672, by rfl⟩ : syracuseStep 6267563 = 9401345) B9401345
theorem B2785967 : Blo 1855629 2785967 := bstep (se 1 (by rfl) ⟨2089475, by rfl⟩ : syracuseStep 2785967 = 4178951) B4178951
theorem B2786015 : Blo 1855629 2786015 := bstep (se 1 (by rfl) ⟨2089511, by rfl⟩ : syracuseStep 2786015 = 4179023) B4179023
theorem B36160307 : Blo 1855629 36160307 := bstep (se 1 (by rfl) ⟨27120230, by rfl⟩ : syracuseStep 36160307 = 54240461) B54240461
theorem B5645135 : Blo 1855629 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B7045967 : Blo 1855629 7045967 := bstep (se 1 (by rfl) ⟨5284475, by rfl⟩ : syracuseStep 7045967 = 10568951) B10568951
theorem B5579599 : Blo 1855629 5579599 := bstep (se 1 (by rfl) ⟨4184699, by rfl⟩ : syracuseStep 5579599 = 8369399) B8369399
theorem B8921935 : Blo 1855629 8921935 := bstep (se 1 (by rfl) ⟨6691451, by rfl⟩ : syracuseStep 8921935 = 13382903) B13382903
theorem B3965851 : Blo 1855629 3965851 := bstep (se 1 (by rfl) ⟨2974388, by rfl⟩ : syracuseStep 3965851 = 5948777) B5948777
theorem B4178843 : Blo 1855629 4178843 := bstep (se 1 (by rfl) ⟨3134132, by rfl⟩ : syracuseStep 4178843 = 6268265) B6268265
theorem B2786279 : Blo 1855629 2786279 := bstep (se 1 (by rfl) ⟨2089709, by rfl⟩ : syracuseStep 2786279 = 4179419) B4179419
theorem B7046135 : Blo 1855629 7046135 := bstep (se 1 (by rfl) ⟨5284601, by rfl⟩ : syracuseStep 7046135 = 10569203) B10569203
theorem B5506145 : Blo 1855629 5506145 := bstep (se 2 (by rfl) ⟨2064804, by rfl⟩ : syracuseStep 5506145 = 4129609) B4129609
theorem B4179041 : Blo 1855629 4179041 := bstep (se 2 (by rfl) ⟨1567140, by rfl⟩ : syracuseStep 4179041 = 3134281) B3134281
theorem B15852743 : Blo 1855629 15852743 := bstep (se 1 (by rfl) ⟨11889557, by rfl⟩ : syracuseStep 15852743 = 23779115) B23779115
theorem B6268103 : Blo 1855629 6268103 := bstep (se 1 (by rfl) ⟨4701077, by rfl⟩ : syracuseStep 6268103 = 9402155) B9402155
theorem B3966185 : Blo 1855629 3966185 := bstep (se 2 (by rfl) ⟨1487319, by rfl⟩ : syracuseStep 3966185 = 2974639) B2974639
theorem B2508041 : Blo 1855629 2508041 := bstep (se 2 (by rfl) ⟨940515, by rfl⟩ : syracuseStep 2508041 = 1881031) B1881031
theorem B5285159 : Blo 1855629 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B4179239 : Blo 1855629 4179239 := bstep (se 1 (by rfl) ⟨3134429, by rfl⟩ : syracuseStep 4179239 = 6268859) B6268859
theorem B14091569 : Blo 1855629 14091569 := bstep (se 2 (by rfl) ⟨5284338, by rfl⟩ : syracuseStep 14091569 = 10568677) B10568677
theorem B9528671 : Blo 1855629 9528671 := bstep (se 1 (by rfl) ⟨7146503, by rfl⟩ : syracuseStep 9528671 = 14293007) B14293007
theorem B8471917 : Blo 1855629 8471917 := bstep (se 3 (by rfl) ⟨1588484, by rfl⟩ : syracuseStep 8471917 = 3176969) B3176969
theorem B3573191 : Blo 1855629 3573191 := bstep (se 1 (by rfl) ⟨2679893, by rfl⟩ : syracuseStep 3573191 = 5359787) B5359787
theorem B33859133 : Blo 1855629 33859133 := bstep (se 3 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 33859133 = 12697175) B12697175
theorem B5949085 : Blo 1855629 5949085 := bstep (se 3 (by rfl) ⟨1115453, by rfl⟩ : syracuseStep 5949085 = 2230907) B2230907
theorem B4179617 : Blo 1855629 4179617 := bstep (se 2 (by rfl) ⟨1567356, by rfl⟩ : syracuseStep 4179617 = 3134713) B3134713
theorem B30123737 : Blo 1855629 30123737 := bstep (se 2 (by rfl) ⟨11296401, by rfl⟩ : syracuseStep 30123737 = 22592803) B22592803
theorem B14092541 : Blo 1855629 14092541 := bstep (se 3 (by rfl) ⟨2642351, by rfl⟩ : syracuseStep 14092541 = 5284703) B5284703
theorem B5360039 : Blo 1855629 5360039 := bstep (se 1 (by rfl) ⟨4020029, by rfl⟩ : syracuseStep 5360039 = 8040059) B8040059
theorem B7047607 : Blo 1855629 7047607 := bstep (se 1 (by rfl) ⟨5285705, by rfl⟩ : syracuseStep 7047607 = 10571411) B10571411
theorem B7932455 : Blo 1855629 7932455 := bstep (se 1 (by rfl) ⟨5949341, by rfl⟩ : syracuseStep 7932455 = 11898683) B11898683
theorem B6441535 : Blo 1855629 6441535 := bstep (se 1 (by rfl) ⟨4831151, by rfl⟩ : syracuseStep 6441535 = 9662303) B9662303
theorem B10177103 : Blo 1855629 10177103 := bstep (se 1 (by rfl) ⟨7632827, by rfl⟩ : syracuseStep 10177103 = 15265655) B15265655
theorem B9046667 : Blo 1855629 9046667 := bstep (se 1 (by rfl) ⟨6785000, by rfl⟩ : syracuseStep 9046667 = 13570001) B13570001
theorem B7048079 : Blo 1855629 7048079 := bstep (se 1 (by rfl) ⟨5286059, by rfl⟩ : syracuseStep 7048079 = 10572119) B10572119
theorem B5286799 : Blo 1855629 5286799 := bstep (se 1 (by rfl) ⟨3965099, by rfl⟩ : syracuseStep 5286799 = 7930199) B7930199
theorem B3132391 : Blo 1855629 3132391 := bstep (se 1 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 3132391 = 4698587) B4698587
theorem B6352091 : Blo 1855629 6352091 := bstep (se 1 (by rfl) ⟨4764068, by rfl⟩ : syracuseStep 6352091 = 9528137) B9528137
theorem B9399563 : Blo 1855629 9399563 := bstep (se 1 (by rfl) ⟨7049672, by rfl⟩ : syracuseStep 9399563 = 14099345) B14099345
theorem B5950817 : Blo 1855629 5950817 := bstep (se 2 (by rfl) ⟨2231556, by rfl⟩ : syracuseStep 5950817 = 4463113) B4463113
theorem B2117191 : Blo 1855629 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B7843645 : Blo 1855629 7843645 := bstep (se 3 (by rfl) ⟨1470683, by rfl⟩ : syracuseStep 7843645 = 2941367) B2941367
theorem B4698121 : Blo 1855629 4698121 := bstep (se 2 (by rfl) ⟨1761795, by rfl⟩ : syracuseStep 4698121 = 3523591) B3523591
theorem B1855775 : Blo 1855629 1855775 := bstep (se 1 (by rfl) ⟨1391831, by rfl⟩ : syracuseStep 1855775 = 2783663) B2783663
theorem B1855835 : Blo 1855629 1855835 := bstep (se 1 (by rfl) ⟨1391876, by rfl⟩ : syracuseStep 1855835 = 2783753) B2783753
theorem B1855855 : Blo 1855629 1855855 := bstep (se 1 (by rfl) ⟨1391891, by rfl⟩ : syracuseStep 1855855 = 2783783) B2783783
theorem B1855911 : Blo 1855629 1855911 := bstep (se 1 (by rfl) ⟨1391933, by rfl⟩ : syracuseStep 1855911 = 2783867) B2783867
theorem B6689249 : Blo 1855629 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B1855995 : Blo 1855629 1855995 := bstep (se 1 (by rfl) ⟨1391996, by rfl⟩ : syracuseStep 1855995 = 2783993) B2783993
theorem B6263297 : Blo 1855629 6263297 := bstep (se 2 (by rfl) ⟨2348736, by rfl⟩ : syracuseStep 6263297 = 4697473) B4697473
theorem B1856063 : Blo 1855629 1856063 := bstep (se 1 (by rfl) ⟨1392047, by rfl⟩ : syracuseStep 1856063 = 2784095) B2784095
theorem B1856071 : Blo 1855629 1856071 := bstep (se 1 (by rfl) ⟨1392053, by rfl⟩ : syracuseStep 1856071 = 2784107) B2784107
theorem B71529101 : Blo 1855629 71529101 := bstep (se 3 (by rfl) ⟨13411706, by rfl⟩ : syracuseStep 71529101 = 26823413) B26823413
theorem B9532075 : Blo 1855629 9532075 := bstep (se 1 (by rfl) ⟨7149056, by rfl⟩ : syracuseStep 9532075 = 14298113) B14298113
theorem B1856223 : Blo 1855629 1856223 := bstep (se 1 (by rfl) ⟨1392167, by rfl⟩ : syracuseStep 1856223 = 2784335) B2784335
theorem B1856303 : Blo 1855629 1856303 := bstep (se 1 (by rfl) ⟨1392227, by rfl⟩ : syracuseStep 1856303 = 2784455) B2784455
theorem B9401183 : Blo 1855629 9401183 := bstep (se 1 (by rfl) ⟨7050887, by rfl⟩ : syracuseStep 9401183 = 14101775) B14101775
theorem B1856411 : Blo 1855629 1856411 := bstep (se 1 (by rfl) ⟨1392308, by rfl⟩ : syracuseStep 1856411 = 2784617) B2784617
theorem B1856463 : Blo 1855629 1856463 := bstep (se 1 (by rfl) ⟨1392347, by rfl⟩ : syracuseStep 1856463 = 2784695) B2784695
theorem B6263783 : Blo 1855629 6263783 := bstep (se 1 (by rfl) ⟨4697837, by rfl⟩ : syracuseStep 6263783 = 9395675) B9395675
theorem B1856487 : Blo 1855629 1856487 := bstep (se 1 (by rfl) ⟨1392365, by rfl⟩ : syracuseStep 1856487 = 2784731) B2784731
theorem B40145939 : Blo 1855629 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B1856799 : Blo 1855629 1856799 := bstep (se 1 (by rfl) ⟨1392599, by rfl⟩ : syracuseStep 1856799 = 2785199) B2785199
theorem B6264107 : Blo 1855629 6264107 := bstep (se 1 (by rfl) ⟨4698080, by rfl⟩ : syracuseStep 6264107 = 9396161) B9396161
theorem B1856859 : Blo 1855629 1856859 := bstep (se 1 (by rfl) ⟨1392644, by rfl⟩ : syracuseStep 1856859 = 2785289) B2785289
theorem B1856879 : Blo 1855629 1856879 := bstep (se 1 (by rfl) ⟨1392659, by rfl⟩ : syracuseStep 1856879 = 2785319) B2785319
theorem B4699529 : Blo 1855629 4699529 := bstep (se 2 (by rfl) ⟨1762323, by rfl⟩ : syracuseStep 4699529 = 3524647) B3524647
theorem B1856935 : Blo 1855629 1856935 := bstep (se 1 (by rfl) ⟨1392701, by rfl⟩ : syracuseStep 1856935 = 2785403) B2785403
theorem B4699579 : Blo 1855629 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B1857019 : Blo 1855629 1857019 := bstep (se 1 (by rfl) ⟨1392764, by rfl⟩ : syracuseStep 1857019 = 2785529) B2785529
theorem B14284295 : Blo 1855629 14284295 := bstep (se 1 (by rfl) ⟨10713221, by rfl⟩ : syracuseStep 14284295 = 21426443) B21426443
theorem B21140999 : Blo 1855629 21140999 := bstep (se 1 (by rfl) ⟨15855749, by rfl⟩ : syracuseStep 21140999 = 31711499) B31711499
theorem B38123045 : Blo 1855629 38123045 := bstep (se 4 (by rfl) ⟨3574035, by rfl⟩ : syracuseStep 38123045 = 7148071) B7148071
theorem B6264377 : Blo 1855629 6264377 := bstep (se 2 (by rfl) ⟨2349141, by rfl⟩ : syracuseStep 6264377 = 4698283) B4698283
theorem B1857087 : Blo 1855629 1857087 := bstep (se 1 (by rfl) ⟨1392815, by rfl⟩ : syracuseStep 1857087 = 2785631) B2785631
theorem B2348615 : Blo 1855629 2348615 := bstep (se 1 (by rfl) ⟨1761461, by rfl⟩ : syracuseStep 2348615 = 3522923) B3522923
theorem B1857095 : Blo 1855629 1857095 := bstep (se 1 (by rfl) ⟨1392821, by rfl⟩ : syracuseStep 1857095 = 2785643) B2785643
theorem B2381419 : Blo 1855629 2381419 := bstep (se 1 (by rfl) ⟨1786064, by rfl⟩ : syracuseStep 2381419 = 3572129) B3572129
theorem B2348767 : Blo 1855629 2348767 := bstep (se 1 (by rfl) ⟨1761575, by rfl⟩ : syracuseStep 2348767 = 3523151) B3523151
theorem B1857247 : Blo 1855629 1857247 := bstep (se 1 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 1857247 = 2785871) B2785871
theorem B4699883 : Blo 1855629 4699883 := bstep (se 1 (by rfl) ⟨3524912, by rfl⟩ : syracuseStep 4699883 = 7049825) B7049825
theorem B4175657 : Blo 1855629 4175657 := bstep (se 2 (by rfl) ⟨1565871, by rfl⟩ : syracuseStep 4175657 = 3131743) B3131743
theorem B1857327 : Blo 1855629 1857327 := bstep (se 1 (by rfl) ⟨1392995, by rfl⟩ : syracuseStep 1857327 = 2785991) B2785991
theorem B4462391 : Blo 1855629 4462391 := bstep (se 1 (by rfl) ⟨3346793, by rfl⟩ : syracuseStep 4462391 = 6693587) B6693587
theorem B1857435 : Blo 1855629 1857435 := bstep (se 1 (by rfl) ⟨1393076, by rfl⟩ : syracuseStep 1857435 = 2786153) B2786153
theorem B1857487 : Blo 1855629 1857487 := bstep (se 1 (by rfl) ⟨1393115, by rfl⟩ : syracuseStep 1857487 = 2786231) B2786231
theorem B53540837 : Blo 1855629 53540837 := bstep (se 4 (by rfl) ⟨5019453, by rfl⟩ : syracuseStep 53540837 = 10038907) B10038907
theorem B1857511 : Blo 1855629 1857511 := bstep (se 1 (by rfl) ⟨1393133, by rfl⟩ : syracuseStep 1857511 = 2786267) B2786267
theorem B11892815 : Blo 1855629 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B8919305 : Blo 1855629 8919305 := bstep (se 2 (by rfl) ⟨3344739, by rfl⟩ : syracuseStep 8919305 = 6689479) B6689479
theorem B2783579 : Blo 1855629 2783579 := bstep (se 1 (by rfl) ⟨2087684, by rfl⟩ : syracuseStep 2783579 = 4175369) B4175369
theorem B10033591 : Blo 1855629 10033591 := bstep (se 1 (by rfl) ⟨7525193, by rfl⟩ : syracuseStep 10033591 = 15050387) B15050387
theorem B2783807 : Blo 1855629 2783807 := bstep (se 1 (by rfl) ⟨2087855, by rfl⟩ : syracuseStep 2783807 = 4175711) B4175711
theorem B2087599 : Blo 1855629 2087599 := bstep (se 1 (by rfl) ⟨1565699, by rfl⟩ : syracuseStep 2087599 = 3131399) B3131399
theorem B4463275 : Blo 1855629 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B2783927 : Blo 1855629 2783927 := bstep (se 1 (by rfl) ⟨2087945, by rfl⟩ : syracuseStep 2783927 = 4175891) B4175891
theorem B4700855 : Blo 1855629 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B9403127 : Blo 1855629 9403127 := bstep (se 1 (by rfl) ⟨7052345, by rfl⟩ : syracuseStep 9403127 = 14104691) B14104691
theorem B6265619 : Blo 1855629 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B4176719 : Blo 1855629 4176719 := bstep (se 1 (by rfl) ⟨3132539, by rfl⟩ : syracuseStep 4176719 = 6265079) B6265079
theorem B7928695 : Blo 1855629 7928695 := bstep (se 1 (by rfl) ⟨5946521, by rfl⟩ : syracuseStep 7928695 = 11893043) B11893043
theorem B2784155 : Blo 1855629 2784155 := bstep (se 1 (by rfl) ⟨2088116, by rfl⟩ : syracuseStep 2784155 = 4176233) B4176233
theorem B21142457 : Blo 1855629 21142457 := bstep (se 2 (by rfl) ⟨7928421, by rfl⟩ : syracuseStep 21142457 = 15856843) B15856843
theorem B2087887 : Blo 1855629 2087887 := bstep (se 1 (by rfl) ⟨1565915, by rfl⟩ : syracuseStep 2087887 = 3131831) B3131831
theorem B17841181 : Blo 1855629 17841181 := bstep (se 3 (by rfl) ⟨3345221, by rfl⟩ : syracuseStep 17841181 = 6690443) B6690443
theorem B4176935 : Blo 1855629 4176935 := bstep (se 1 (by rfl) ⟨3132701, by rfl⟩ : syracuseStep 4176935 = 6265403) B6265403
theorem B7527563 : Blo 1855629 7527563 := bstep (se 1 (by rfl) ⟨5645672, by rfl⟩ : syracuseStep 7527563 = 11291345) B11291345
theorem B4177115 : Blo 1855629 4177115 := bstep (se 1 (by rfl) ⟨3132836, by rfl⟩ : syracuseStep 4177115 = 6265673) B6265673
theorem B9526493 : Blo 1855629 9526493 := bstep (se 3 (by rfl) ⟨1786217, by rfl⟩ : syracuseStep 9526493 = 3572435) B3572435
theorem B9403613 : Blo 1855629 9403613 := bstep (se 3 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 9403613 = 3526355) B3526355
theorem B2784551 : Blo 1855629 2784551 := bstep (se 1 (by rfl) ⟨2088413, by rfl⟩ : syracuseStep 2784551 = 4176827) B4176827
theorem B2088283 : Blo 1855629 2088283 := bstep (se 1 (by rfl) ⟨1566212, by rfl⟩ : syracuseStep 2088283 = 3132425) B3132425
theorem B8920439 : Blo 1855629 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B2784635 : Blo 1855629 2784635 := bstep (se 1 (by rfl) ⟨2088476, by rfl⟩ : syracuseStep 2784635 = 4176953) B4176953
theorem B3964297 : Blo 1855629 3964297 := bstep (se 2 (by rfl) ⟨1486611, by rfl⟩ : syracuseStep 3964297 = 2973223) B2973223
theorem B4177313 : Blo 1855629 4177313 := bstep (se 2 (by rfl) ⟨1566492, by rfl⟩ : syracuseStep 4177313 = 3132985) B3132985
theorem B2260391 : Blo 1855629 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B2088391 : Blo 1855629 2088391 := bstep (se 1 (by rfl) ⟨1566293, by rfl⟩ : syracuseStep 2088391 = 3132587) B3132587
theorem B30105047 : Blo 1855629 30105047 := bstep (se 1 (by rfl) ⟨22578785, by rfl⟩ : syracuseStep 30105047 = 45157571) B45157571
theorem B2784761 : Blo 1855629 2784761 := bstep (se 2 (by rfl) ⟨1044285, by rfl⟩ : syracuseStep 2784761 = 2088571) B2088571
theorem B2784863 : Blo 1855629 2784863 := bstep (se 1 (by rfl) ⟨2088647, by rfl⟩ : syracuseStep 2784863 = 4177295) B4177295
theorem B11296351 : Blo 1855629 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B6266483 : Blo 1855629 6266483 := bstep (se 1 (by rfl) ⟨4699862, by rfl⟩ : syracuseStep 6266483 = 9399725) B9399725
theorem B15261443 : Blo 1855629 15261443 := bstep (se 1 (by rfl) ⟨11446082, by rfl⟩ : syracuseStep 15261443 = 22892165) B22892165
theorem B4701959 : Blo 1855629 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B2088751 : Blo 1855629 2088751 := bstep (se 1 (by rfl) ⟨1566563, by rfl⟩ : syracuseStep 2088751 = 3133127) B3133127
theorem B2785079 : Blo 1855629 2785079 := bstep (se 1 (by rfl) ⟨2088809, by rfl⟩ : syracuseStep 2785079 = 4177619) B4177619
theorem B6692665 : Blo 1855629 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B4702009 : Blo 1855629 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B6266753 : Blo 1855629 6266753 := bstep (se 2 (by rfl) ⟨2350032, by rfl⟩ : syracuseStep 6266753 = 4700065) B4700065
theorem B2088859 : Blo 1855629 2088859 := bstep (se 1 (by rfl) ⟨1566644, by rfl⟩ : syracuseStep 2088859 = 3133289) B3133289
theorem B10035101 : Blo 1855629 10035101 := bstep (se 3 (by rfl) ⟨1881581, by rfl⟩ : syracuseStep 10035101 = 3763163) B3763163
theorem B4177871 : Blo 1855629 4177871 := bstep (se 1 (by rfl) ⟨3133403, by rfl⟩ : syracuseStep 4177871 = 6266807) B6266807
theorem B15057035 : Blo 1855629 15057035 := bstep (se 1 (by rfl) ⟨11292776, by rfl⟩ : syracuseStep 15057035 = 22585553) B22585553
theorem B2785499 : Blo 1855629 2785499 := bstep (se 1 (by rfl) ⟨2089124, by rfl⟩ : syracuseStep 2785499 = 4178249) B4178249
theorem B2785511 : Blo 1855629 2785511 := bstep (se 1 (by rfl) ⟨2089133, by rfl⟩ : syracuseStep 2785511 = 4178267) B4178267
theorem B3522847 : Blo 1855629 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B2785673 : Blo 1855629 2785673 := bstep (se 2 (by rfl) ⟨1044627, by rfl⟩ : syracuseStep 2785673 = 2089255) B2089255
theorem B47686067 : Blo 1855629 47686067 := bstep (se 1 (by rfl) ⟨35764550, by rfl⟩ : syracuseStep 47686067 = 71529101) B71529101
theorem B4178375 : Blo 1855629 4178375 := bstep (se 1 (by rfl) ⟨3133781, by rfl⟩ : syracuseStep 4178375 = 6267563) B6267563
theorem B2785769 : Blo 1855629 2785769 := bstep (se 2 (by rfl) ⟨1044663, by rfl⟩ : syracuseStep 2785769 = 2089327) B2089327
theorem B6267455 : Blo 1855629 6267455 := bstep (se 1 (by rfl) ⟨4700591, by rfl⟩ : syracuseStep 6267455 = 9401183) B9401183
theorem B13378121 : Blo 1855629 13378121 := bstep (se 2 (by rfl) ⟨5016795, by rfl⟩ : syracuseStep 13378121 = 10033591) B10033591
theorem B9396809 : Blo 1855629 9396809 := bstep (se 2 (by rfl) ⟨3523803, by rfl⟩ : syracuseStep 9396809 = 7047607) B7047607
theorem B2785895 : Blo 1855629 2785895 := bstep (se 1 (by rfl) ⟨2089421, by rfl⟩ : syracuseStep 2785895 = 4178843) B4178843
theorem B10576493 : Blo 1855629 10576493 := bstep (se 3 (by rfl) ⟨1983092, by rfl⟩ : syracuseStep 10576493 = 3966185) B3966185
theorem B26763959 : Blo 1855629 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B3670763 : Blo 1855629 3670763 := bstep (se 1 (by rfl) ⟨2753072, by rfl⟩ : syracuseStep 3670763 = 5506145) B5506145
theorem B2786027 : Blo 1855629 2786027 := bstep (se 1 (by rfl) ⟨2089520, by rfl⟩ : syracuseStep 2786027 = 4179041) B4179041
theorem B2786057 : Blo 1855629 2786057 := bstep (se 2 (by rfl) ⟨1044771, by rfl⟩ : syracuseStep 2786057 = 2089543) B2089543
theorem B10568495 : Blo 1855629 10568495 := bstep (se 1 (by rfl) ⟨7926371, by rfl⟩ : syracuseStep 10568495 = 15852743) B15852743
theorem B4178735 : Blo 1855629 4178735 := bstep (se 1 (by rfl) ⟨3134051, by rfl⟩ : syracuseStep 4178735 = 6268103) B6268103
theorem B3523439 : Blo 1855629 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B2786159 : Blo 1855629 2786159 := bstep (se 1 (by rfl) ⟨2089619, by rfl⟩ : syracuseStep 2786159 = 4179239) B4179239
theorem B7930781 : Blo 1855629 7930781 := bstep (se 3 (by rfl) ⟨1487021, by rfl⟩ : syracuseStep 7930781 = 2974043) B2974043
theorem B7439465 : Blo 1855629 7439465 := bstep (se 2 (by rfl) ⟨2789799, by rfl⟩ : syracuseStep 7439465 = 5579599) B5579599
theorem B11895913 : Blo 1855629 11895913 := bstep (se 2 (by rfl) ⟨4460967, by rfl⟩ : syracuseStep 11895913 = 8921935) B8921935
theorem B2786411 : Blo 1855629 2786411 := bstep (se 1 (by rfl) ⟨2089808, by rfl⟩ : syracuseStep 2786411 = 4179617) B4179617
theorem B9528509 : Blo 1855629 9528509 := bstep (se 3 (by rfl) ⟨1786595, by rfl⟩ : syracuseStep 9528509 = 3573191) B3573191
theorem B35693891 : Blo 1855629 35693891 := bstep (se 1 (by rfl) ⟨26770418, by rfl⟩ : syracuseStep 35693891 = 53540837) B53540837
theorem B3573359 : Blo 1855629 3573359 := bstep (se 1 (by rfl) ⟨2680019, by rfl⟩ : syracuseStep 3573359 = 5360039) B5360039
theorem B6784735 : Blo 1855629 6784735 := bstep (se 1 (by rfl) ⟨5088551, by rfl⟩ : syracuseStep 6784735 = 10177103) B10177103
theorem B6031111 : Blo 1855629 6031111 := bstep (se 1 (by rfl) ⟨4523333, by rfl⟩ : syracuseStep 6031111 = 9046667) B9046667
theorem B6268751 : Blo 1855629 6268751 := bstep (se 1 (by rfl) ⟨4701563, by rfl⟩ : syracuseStep 6268751 = 9403127) B9403127
theorem B5285729 : Blo 1855629 5285729 := bstep (se 2 (by rfl) ⟨1982148, by rfl⟩ : syracuseStep 5285729 = 3964297) B3964297
theorem B6350995 : Blo 1855629 6350995 := bstep (se 1 (by rfl) ⟨4763246, by rfl⟩ : syracuseStep 6350995 = 9526493) B9526493
theorem B6269075 : Blo 1855629 6269075 := bstep (se 1 (by rfl) ⟨4701806, by rfl⟩ : syracuseStep 6269075 = 9403613) B9403613
theorem B7932113 : Blo 1855629 7932113 := bstep (se 2 (by rfl) ⟨2974542, by rfl⟩ : syracuseStep 7932113 = 5949085) B5949085
theorem B3967211 : Blo 1855629 3967211 := bstep (se 1 (by rfl) ⟨2975408, by rfl⟩ : syracuseStep 3967211 = 5950817) B5950817
theorem B3131689 : Blo 1855629 3131689 := bstep (se 2 (by rfl) ⟨1174383, by rfl⟩ : syracuseStep 3131689 = 2348767) B2348767
theorem B8923553 : Blo 1855629 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B6269345 : Blo 1855629 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B17853371 : Blo 1855629 17853371 := bstep (se 1 (by rfl) ⟨13390028, by rfl⟩ : syracuseStep 17853371 = 26780057) B26780057
theorem B10578883 : Blo 1855629 10578883 := bstep (se 1 (by rfl) ⟨7934162, by rfl⟩ : syracuseStep 10578883 = 15868325) B15868325
theorem B4459499 : Blo 1855629 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B4697311 : Blo 1855629 4697311 := bstep (se 1 (by rfl) ⟨3522983, by rfl⟩ : syracuseStep 4697311 = 7045967) B7045967
theorem B3763423 : Blo 1855629 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B12700901 : Blo 1855629 12700901 := bstep (se 4 (by rfl) ⟨1190709, by rfl⟩ : syracuseStep 12700901 = 2381419) B2381419
theorem B4697423 : Blo 1855629 4697423 := bstep (se 1 (by rfl) ⟨3523067, by rfl⟩ : syracuseStep 4697423 = 7046135) B7046135
theorem B6688109 : Blo 1855629 6688109 := bstep (se 3 (by rfl) ⟨1254020, by rfl⟩ : syracuseStep 6688109 = 2508041) B2508041
theorem B12709433 : Blo 1855629 12709433 := bstep (se 2 (by rfl) ⟨4766037, by rfl⟩ : syracuseStep 12709433 = 9532075) B9532075
theorem B5951033 : Blo 1855629 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B6352447 : Blo 1855629 6352447 := bstep (se 1 (by rfl) ⟨4764335, by rfl⟩ : syracuseStep 6352447 = 9528671) B9528671
theorem B3133019 : Blo 1855629 3133019 := bstep (se 1 (by rfl) ⟨2349764, by rfl⟩ : syracuseStep 3133019 = 4699529) B4699529
theorem B9522863 : Blo 1855629 9522863 := bstep (se 1 (by rfl) ⟨7142147, by rfl⟩ : syracuseStep 9522863 = 14284295) B14284295
theorem B14093999 : Blo 1855629 14093999 := bstep (se 1 (by rfl) ⟨10570499, by rfl⟩ : syracuseStep 14093999 = 21140999) B21140999
theorem B25415363 : Blo 1855629 25415363 := bstep (se 1 (by rfl) ⟨19061522, by rfl⟩ : syracuseStep 25415363 = 38123045) B38123045
theorem B22572755 : Blo 1855629 22572755 := bstep (se 1 (by rfl) ⟨16929566, by rfl⟩ : syracuseStep 22572755 = 33859133) B33859133
theorem B20082491 : Blo 1855629 20082491 := bstep (se 1 (by rfl) ⟨15061868, by rfl⟩ : syracuseStep 20082491 = 30123737) B30123737
theorem B3133255 : Blo 1855629 3133255 := bstep (se 1 (by rfl) ⟨2349941, by rfl⟩ : syracuseStep 3133255 = 4699883) B4699883
theorem B10571593 : Blo 1855629 10571593 := bstep (se 2 (by rfl) ⟨3964347, by rfl⟩ : syracuseStep 10571593 = 7928695) B7928695
theorem B7049065 : Blo 1855629 7049065 := bstep (se 2 (by rfl) ⟨2643399, by rfl⟩ : syracuseStep 7049065 = 5286799) B5286799
theorem B6262973 : Blo 1855629 6262973 := bstep (se 3 (by rfl) ⟨1174307, by rfl⟩ : syracuseStep 6262973 = 2348615) B2348615
theorem B1855719 : Blo 1855629 1855719 := bstep (se 1 (by rfl) ⟨1391789, by rfl⟩ : syracuseStep 1855719 = 2783579) B2783579
theorem B41832773 : Blo 1855629 41832773 := bstep (se 4 (by rfl) ⟨3921822, by rfl⟩ : syracuseStep 41832773 = 7843645) B7843645
theorem B5288303 : Blo 1855629 5288303 := bstep (se 1 (by rfl) ⟨3966227, by rfl⟩ : syracuseStep 5288303 = 7932455) B7932455
theorem B1855871 : Blo 1855629 1855871 := bstep (se 1 (by rfl) ⟨1391903, by rfl⟩ : syracuseStep 1855871 = 2783807) B2783807
theorem B1855951 : Blo 1855629 1855951 := bstep (se 1 (by rfl) ⟨1391963, by rfl⟩ : syracuseStep 1855951 = 2783927) B2783927
theorem B3133903 : Blo 1855629 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B45183557 : Blo 1855629 45183557 := bstep (se 4 (by rfl) ⟨4235958, by rfl⟩ : syracuseStep 45183557 = 8471917) B8471917
theorem B4698719 : Blo 1855629 4698719 := bstep (se 1 (by rfl) ⟨3524039, by rfl⟩ : syracuseStep 4698719 = 7048079) B7048079
theorem B1856103 : Blo 1855629 1856103 := bstep (se 1 (by rfl) ⟨1392077, by rfl⟩ : syracuseStep 1856103 = 2784155) B2784155
theorem B14094971 : Blo 1855629 14094971 := bstep (se 1 (by rfl) ⟨10571228, by rfl⟩ : syracuseStep 14094971 = 21142457) B21142457
theorem B5018375 : Blo 1855629 5018375 := bstep (se 1 (by rfl) ⟨3763781, by rfl⟩ : syracuseStep 5018375 = 7527563) B7527563
theorem B2822921 : Blo 1855629 2822921 := bstep (se 2 (by rfl) ⟨1058595, by rfl⟩ : syracuseStep 2822921 = 2117191) B2117191
theorem B15061801 : Blo 1855629 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B11899709 : Blo 1855629 11899709 := bstep (se 3 (by rfl) ⟨2231195, by rfl⟩ : syracuseStep 11899709 = 4462391) B4462391
theorem B1856367 : Blo 1855629 1856367 := bstep (se 1 (by rfl) ⟨1392275, by rfl⟩ : syracuseStep 1856367 = 2784551) B2784551
theorem B1856423 : Blo 1855629 1856423 := bstep (se 1 (by rfl) ⟨1392317, by rfl⟩ : syracuseStep 1856423 = 2784635) B2784635
theorem B1856507 : Blo 1855629 1856507 := bstep (se 1 (by rfl) ⟨1392380, by rfl⟩ : syracuseStep 1856507 = 2784761) B2784761
theorem B1856575 : Blo 1855629 1856575 := bstep (se 1 (by rfl) ⟨1392431, by rfl⟩ : syracuseStep 1856575 = 2784863) B2784863
theorem B26760269 : Blo 1855629 26760269 := bstep (se 3 (by rfl) ⟨5017550, by rfl⟩ : syracuseStep 26760269 = 10035101) B10035101
theorem B3134639 : Blo 1855629 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B1856719 : Blo 1855629 1856719 := bstep (se 1 (by rfl) ⟨1392539, by rfl⟩ : syracuseStep 1856719 = 2785079) B2785079
theorem B6264161 : Blo 1855629 6264161 := bstep (se 2 (by rfl) ⟨2349060, by rfl⟩ : syracuseStep 6264161 = 4698121) B4698121
theorem B1856923 : Blo 1855629 1856923 := bstep (se 1 (by rfl) ⟨1392692, by rfl⟩ : syracuseStep 1856923 = 2785385) B2785385
theorem B19060211 : Blo 1855629 19060211 := bstep (se 1 (by rfl) ⟨14295158, by rfl⟩ : syracuseStep 19060211 = 28590317) B28590317
theorem B1857135 : Blo 1855629 1857135 := bstep (se 1 (by rfl) ⟨1392851, by rfl⟩ : syracuseStep 1857135 = 2785703) B2785703
theorem B34354853 : Blo 1855629 34354853 := bstep (se 4 (by rfl) ⟨3220767, by rfl⟩ : syracuseStep 34354853 = 6441535) B6441535
theorem B1857191 : Blo 1855629 1857191 := bstep (se 1 (by rfl) ⟨1392893, by rfl⟩ : syracuseStep 1857191 = 2785787) B2785787
theorem B4175531 : Blo 1855629 4175531 := bstep (se 1 (by rfl) ⟨3131648, by rfl⟩ : syracuseStep 4175531 = 6263297) B6263297
theorem B1857275 : Blo 1855629 1857275 := bstep (se 1 (by rfl) ⟨1392956, by rfl⟩ : syracuseStep 1857275 = 2785913) B2785913
theorem B1857311 : Blo 1855629 1857311 := bstep (se 1 (by rfl) ⟨1392983, by rfl⟩ : syracuseStep 1857311 = 2785967) B2785967
theorem B1857343 : Blo 1855629 1857343 := bstep (se 1 (by rfl) ⟨1393007, by rfl⟩ : syracuseStep 1857343 = 2786015) B2786015
theorem B24106871 : Blo 1855629 24106871 := bstep (se 1 (by rfl) ⟨18080153, by rfl⟩ : syracuseStep 24106871 = 36160307) B36160307
theorem B4175855 : Blo 1855629 4175855 := bstep (se 1 (by rfl) ⟨3131891, by rfl⟩ : syracuseStep 4175855 = 6263783) B6263783
theorem B1857519 : Blo 1855629 1857519 := bstep (se 1 (by rfl) ⟨1393139, by rfl⟩ : syracuseStep 1857519 = 2786279) B2786279
theorem B4176071 : Blo 1855629 4176071 := bstep (se 1 (by rfl) ⟨3132053, by rfl⟩ : syracuseStep 4176071 = 6264107) B6264107
theorem B9394379 : Blo 1855629 9394379 := bstep (se 1 (by rfl) ⟨7045784, by rfl⟩ : syracuseStep 9394379 = 14091569) B14091569
theorem B2783465 : Blo 1855629 2783465 := bstep (se 2 (by rfl) ⟨1043799, by rfl⟩ : syracuseStep 2783465 = 2087599) B2087599
theorem B4176251 : Blo 1855629 4176251 := bstep (se 1 (by rfl) ⟨3132188, by rfl⟩ : syracuseStep 4176251 = 6264377) B6264377
theorem B6027709 : Blo 1855629 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B2783771 : Blo 1855629 2783771 := bstep (se 1 (by rfl) ⟨2087828, by rfl⟩ : syracuseStep 2783771 = 4175657) B4175657
theorem B2783849 : Blo 1855629 2783849 := bstep (se 2 (by rfl) ⟨1043943, by rfl⟩ : syracuseStep 2783849 = 2087887) B2087887
theorem B4176521 : Blo 1855629 4176521 := bstep (se 2 (by rfl) ⟨1566195, by rfl⟩ : syracuseStep 4176521 = 3132391) B3132391
theorem B23788241 : Blo 1855629 23788241 := bstep (se 2 (by rfl) ⟨8920590, by rfl⟩ : syracuseStep 23788241 = 17841181) B17841181
theorem B7928543 : Blo 1855629 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B9395027 : Blo 1855629 9395027 := bstep (se 1 (by rfl) ⟨7046270, by rfl⟩ : syracuseStep 9395027 = 14092541) B14092541
theorem B5946203 : Blo 1855629 5946203 := bstep (se 1 (by rfl) ⟨4459652, by rfl⟩ : syracuseStep 5946203 = 8919305) B8919305
theorem B2784377 : Blo 1855629 2784377 := bstep (se 2 (by rfl) ⟨1044141, by rfl⟩ : syracuseStep 2784377 = 2088283) B2088283
theorem B4177079 : Blo 1855629 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B2784479 : Blo 1855629 2784479 := bstep (se 1 (by rfl) ⟨2088359, by rfl⟩ : syracuseStep 2784479 = 4176719) B4176719
theorem B6266105 : Blo 1855629 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B2784521 : Blo 1855629 2784521 := bstep (se 2 (by rfl) ⟨1044195, by rfl⟩ : syracuseStep 2784521 = 2088391) B2088391
theorem B2784623 : Blo 1855629 2784623 := bstep (se 1 (by rfl) ⟨2088467, by rfl⟩ : syracuseStep 2784623 = 4176935) B4176935
theorem B21151205 : Blo 1855629 21151205 := bstep (se 4 (by rfl) ⟨1982925, by rfl⟩ : syracuseStep 21151205 = 3965851) B3965851
theorem B2784743 : Blo 1855629 2784743 := bstep (se 1 (by rfl) ⟨2088557, by rfl⟩ : syracuseStep 2784743 = 4177115) B4177115
theorem B4234727 : Blo 1855629 4234727 := bstep (se 1 (by rfl) ⟨3176045, by rfl⟩ : syracuseStep 4234727 = 6352091) B6352091
theorem B6266375 : Blo 1855629 6266375 := bstep (se 1 (by rfl) ⟨4699781, by rfl⟩ : syracuseStep 6266375 = 9399563) B9399563
theorem B5946959 : Blo 1855629 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B2784875 : Blo 1855629 2784875 := bstep (se 1 (by rfl) ⟨2088656, by rfl⟩ : syracuseStep 2784875 = 4177313) B4177313
theorem B20070031 : Blo 1855629 20070031 := bstep (se 1 (by rfl) ⟨15052523, by rfl⟩ : syracuseStep 20070031 = 30105047) B30105047
theorem B2785001 : Blo 1855629 2785001 := bstep (se 2 (by rfl) ⟨1044375, by rfl⟩ : syracuseStep 2785001 = 2088751) B2088751
theorem B4177655 : Blo 1855629 4177655 := bstep (se 1 (by rfl) ⟨3133241, by rfl⟩ : syracuseStep 4177655 = 6266483) B6266483
theorem B10174295 : Blo 1855629 10174295 := bstep (se 1 (by rfl) ⟨7630721, by rfl⟩ : syracuseStep 10174295 = 15261443) B15261443
theorem B2785145 : Blo 1855629 2785145 := bstep (se 2 (by rfl) ⟨1044429, by rfl⟩ : syracuseStep 2785145 = 2088859) B2088859
theorem B4177835 : Blo 1855629 4177835 := bstep (se 1 (by rfl) ⟨3133376, by rfl⟩ : syracuseStep 4177835 = 6266753) B6266753
theorem B2785247 : Blo 1855629 2785247 := bstep (se 1 (by rfl) ⟨2088935, by rfl⟩ : syracuseStep 2785247 = 4177871) B4177871
theorem B2785583 : Blo 1855629 2785583 := bstep (se 1 (by rfl) ⟨2089187, by rfl⟩ : syracuseStep 2785583 = 4178375) B4178375
theorem B4178303 : Blo 1855629 4178303 := bstep (se 1 (by rfl) ⟨3133727, by rfl⟩ : syracuseStep 4178303 = 6267455) B6267455
theorem B30122371 : Blo 1855629 30122371 := bstep (se 1 (by rfl) ⟨22591778, by rfl⟩ : syracuseStep 30122371 = 45183557) B45183557
theorem B9396647 : Blo 1855629 9396647 := bstep (se 1 (by rfl) ⟨7047485, by rfl⟩ : syracuseStep 9396647 = 14094971) B14094971
theorem B7045663 : Blo 1855629 7045663 := bstep (se 1 (by rfl) ⟨5284247, by rfl⟩ : syracuseStep 7045663 = 10568495) B10568495
theorem B2785823 : Blo 1855629 2785823 := bstep (se 1 (by rfl) ⟨2089367, by rfl⟩ : syracuseStep 2785823 = 4178735) B4178735
theorem B8036945 : Blo 1855629 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B4178537 : Blo 1855629 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2089759 : Blo 1855629 2089759 := bstep (se 1 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 2089759 = 3134639) B3134639
theorem B12706807 : Blo 1855629 12706807 := bstep (se 1 (by rfl) ⟨9530105, by rfl⟩ : syracuseStep 12706807 = 19060211) B19060211
theorem B4179167 : Blo 1855629 4179167 := bstep (se 1 (by rfl) ⟨3134375, by rfl⟩ : syracuseStep 4179167 = 6268751) B6268751
theorem B3523819 : Blo 1855629 3523819 := bstep (se 1 (by rfl) ⟨2642864, by rfl⟩ : syracuseStep 3523819 = 5285729) B5285729
theorem B4179383 : Blo 1855629 4179383 := bstep (se 1 (by rfl) ⟨3134537, by rfl⟩ : syracuseStep 4179383 = 6269075) B6269075
theorem B15861217 : Blo 1855629 15861217 := bstep (se 2 (by rfl) ⟨5947956, by rfl⟩ : syracuseStep 15861217 = 11895913) B11895913
theorem B33891821 : Blo 1855629 33891821 := bstep (se 3 (by rfl) ⟨6354716, by rfl⟩ : syracuseStep 33891821 = 12709433) B12709433
theorem B5949035 : Blo 1855629 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B4179563 : Blo 1855629 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B71370557 : Blo 1855629 71370557 := bstep (se 3 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 71370557 = 26763959) B26763959
theorem B5285695 : Blo 1855629 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B3131615 : Blo 1855629 3131615 := bstep (se 1 (by rfl) ⟨2348711, by rfl⟩ : syracuseStep 3131615 = 4697423) B4697423
theorem B4458739 : Blo 1855629 4458739 := bstep (se 1 (by rfl) ⟨3344054, by rfl⟩ : syracuseStep 4458739 = 6688109) B6688109
theorem B9046313 : Blo 1855629 9046313 := bstep (se 2 (by rfl) ⟨3392367, by rfl⟩ : syracuseStep 9046313 = 6784735) B6784735
theorem B14100803 : Blo 1855629 14100803 := bstep (se 1 (by rfl) ⟨10575602, by rfl⟩ : syracuseStep 14100803 = 21151205) B21151205
theorem B3967355 : Blo 1855629 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B16943575 : Blo 1855629 16943575 := bstep (se 1 (by rfl) ⟨12707681, by rfl⟩ : syracuseStep 16943575 = 25415363) B25415363
theorem B9398753 : Blo 1855629 9398753 := bstep (se 2 (by rfl) ⟨3524532, by rfl⟩ : syracuseStep 9398753 = 7049065) B7049065
theorem B13388327 : Blo 1855629 13388327 := bstep (se 1 (by rfl) ⟨10041245, by rfl⟩ : syracuseStep 13388327 = 20082491) B20082491
theorem B10038023 : Blo 1855629 10038023 := bstep (se 1 (by rfl) ⟨7528517, by rfl⟩ : syracuseStep 10038023 = 15057035) B15057035
theorem B27888515 : Blo 1855629 27888515 := bstep (se 1 (by rfl) ⟨20916386, by rfl⟩ : syracuseStep 27888515 = 41832773) B41832773
theorem B3525535 : Blo 1855629 3525535 := bstep (se 1 (by rfl) ⟨2644151, by rfl⟩ : syracuseStep 3525535 = 5288303) B5288303
theorem B4697129 : Blo 1855629 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B3132479 : Blo 1855629 3132479 := bstep (se 1 (by rfl) ⟨2349359, by rfl⟩ : syracuseStep 3132479 = 4698719) B4698719
theorem B3345583 : Blo 1855629 3345583 := bstep (se 1 (by rfl) ⟨2509187, by rfl⟩ : syracuseStep 3345583 = 5018375) B5018375
theorem B7933139 : Blo 1855629 7933139 := bstep (se 1 (by rfl) ⟨5949854, by rfl⟩ : syracuseStep 7933139 = 11899709) B11899709
theorem B5287187 : Blo 1855629 5287187 := bstep (se 1 (by rfl) ⟨3965390, by rfl⟩ : syracuseStep 5287187 = 7930781) B7930781
theorem B4959643 : Blo 1855629 4959643 := bstep (se 1 (by rfl) ⟨3719732, by rfl⟩ : syracuseStep 4959643 = 7439465) B7439465
theorem B6352339 : Blo 1855629 6352339 := bstep (se 1 (by rfl) ⟨4764254, by rfl⟩ : syracuseStep 6352339 = 9528509) B9528509
theorem B20082401 : Blo 1855629 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B11292605 : Blo 1855629 11292605 := bstep (se 3 (by rfl) ⟨2117363, by rfl⟩ : syracuseStep 11292605 = 4234727) B4234727
theorem B6262919 : Blo 1855629 6262919 := bstep (se 1 (by rfl) ⟨4697189, by rfl⟩ : syracuseStep 6262919 = 9394379) B9394379
theorem B5288075 : Blo 1855629 5288075 := bstep (se 1 (by rfl) ⟨3966056, by rfl⟩ : syracuseStep 5288075 = 7932113) B7932113
theorem B1855643 : Blo 1855629 1855643 := bstep (se 1 (by rfl) ⟨1391732, by rfl⟩ : syracuseStep 1855643 = 2783465) B2783465
theorem B6263081 : Blo 1855629 6263081 := bstep (se 2 (by rfl) ⟨2348655, by rfl⟩ : syracuseStep 6263081 = 4697311) B4697311
theorem B5017897 : Blo 1855629 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B1855847 : Blo 1855629 1855847 := bstep (se 1 (by rfl) ⟨1391885, by rfl⟩ : syracuseStep 1855847 = 2783771) B2783771
theorem B1855899 : Blo 1855629 1855899 := bstep (se 1 (by rfl) ⟨1391924, by rfl⟩ : syracuseStep 1855899 = 2783849) B2783849
theorem B6263351 : Blo 1855629 6263351 := bstep (se 1 (by rfl) ⟨4697513, by rfl⟩ : syracuseStep 6263351 = 9395027) B9395027
theorem B1856251 : Blo 1855629 1856251 := bstep (se 1 (by rfl) ⟨1392188, by rfl⟩ : syracuseStep 1856251 = 2784377) B2784377
theorem B1856319 : Blo 1855629 1856319 := bstep (se 1 (by rfl) ⟨1392239, by rfl⟩ : syracuseStep 1856319 = 2784479) B2784479
theorem B8467267 : Blo 1855629 8467267 := bstep (se 1 (by rfl) ⟨6350450, by rfl⟩ : syracuseStep 8467267 = 12700901) B12700901
theorem B1856347 : Blo 1855629 1856347 := bstep (se 1 (by rfl) ⟨1392260, by rfl⟩ : syracuseStep 1856347 = 2784521) B2784521
theorem B26760041 : Blo 1855629 26760041 := bstep (se 2 (by rfl) ⟨10035015, by rfl⟩ : syracuseStep 26760041 = 20070031) B20070031
theorem B1856415 : Blo 1855629 1856415 := bstep (se 1 (by rfl) ⟨1392311, by rfl⟩ : syracuseStep 1856415 = 2784623) B2784623
theorem B1856495 : Blo 1855629 1856495 := bstep (se 1 (by rfl) ⟨1392371, by rfl⟩ : syracuseStep 1856495 = 2784743) B2784743
theorem B8041481 : Blo 1855629 8041481 := bstep (se 2 (by rfl) ⟨3015555, by rfl⟩ : syracuseStep 8041481 = 6031111) B6031111
theorem B1856583 : Blo 1855629 1856583 := bstep (se 1 (by rfl) ⟨1392437, by rfl⟩ : syracuseStep 1856583 = 2784875) B2784875
theorem B14095457 : Blo 1855629 14095457 := bstep (se 2 (by rfl) ⟨5285796, by rfl⟩ : syracuseStep 14095457 = 10571593) B10571593
theorem B1856667 : Blo 1855629 1856667 := bstep (se 1 (by rfl) ⟨1392500, by rfl⟩ : syracuseStep 1856667 = 2785001) B2785001
theorem B1856763 : Blo 1855629 1856763 := bstep (se 1 (by rfl) ⟨1392572, by rfl⟩ : syracuseStep 1856763 = 2785145) B2785145
theorem B1856831 : Blo 1855629 1856831 := bstep (se 1 (by rfl) ⟨1392623, by rfl⟩ : syracuseStep 1856831 = 2785247) B2785247
theorem B4175315 : Blo 1855629 4175315 := bstep (se 1 (by rfl) ⟨3131486, by rfl⟩ : syracuseStep 4175315 = 6262973) B6262973
theorem B1856999 : Blo 1855629 1856999 := bstep (se 1 (by rfl) ⟨1392749, by rfl⟩ : syracuseStep 1856999 = 2785499) B2785499
theorem B1857007 : Blo 1855629 1857007 := bstep (se 1 (by rfl) ⟨1392755, by rfl⟩ : syracuseStep 1857007 = 2785511) B2785511
theorem B8467993 : Blo 1855629 8467993 := bstep (se 2 (by rfl) ⟨3175497, by rfl⟩ : syracuseStep 8467993 = 6350995) B6350995
theorem B1857115 : Blo 1855629 1857115 := bstep (se 1 (by rfl) ⟨1392836, by rfl⟩ : syracuseStep 1857115 = 2785673) B2785673
theorem B31790711 : Blo 1855629 31790711 := bstep (se 1 (by rfl) ⟨23843033, by rfl⟩ : syracuseStep 31790711 = 47686067) B47686067
theorem B1857179 : Blo 1855629 1857179 := bstep (se 1 (by rfl) ⟨1392884, by rfl⟩ : syracuseStep 1857179 = 2785769) B2785769
theorem B8918747 : Blo 1855629 8918747 := bstep (se 1 (by rfl) ⟨6689060, by rfl⟩ : syracuseStep 8918747 = 13378121) B13378121
theorem B6264539 : Blo 1855629 6264539 := bstep (se 1 (by rfl) ⟨4698404, by rfl⟩ : syracuseStep 6264539 = 9396809) B9396809
theorem B4175585 : Blo 1855629 4175585 := bstep (se 2 (by rfl) ⟨1565844, by rfl⟩ : syracuseStep 4175585 = 3131689) B3131689
theorem B1857263 : Blo 1855629 1857263 := bstep (se 1 (by rfl) ⟨1392947, by rfl⟩ : syracuseStep 1857263 = 2785895) B2785895
theorem B7050995 : Blo 1855629 7050995 := bstep (se 1 (by rfl) ⟨5288246, by rfl⟩ : syracuseStep 7050995 = 10576493) B10576493
theorem B1857351 : Blo 1855629 1857351 := bstep (se 1 (by rfl) ⟨1393013, by rfl⟩ : syracuseStep 1857351 = 2786027) B2786027
theorem B1881947 : Blo 1855629 1881947 := bstep (se 1 (by rfl) ⟨1411460, by rfl⟩ : syracuseStep 1881947 = 2822921) B2822921
theorem B1857371 : Blo 1855629 1857371 := bstep (se 1 (by rfl) ⟨1393028, by rfl⟩ : syracuseStep 1857371 = 2786057) B2786057
theorem B1857439 : Blo 1855629 1857439 := bstep (se 1 (by rfl) ⟨1393079, by rfl⟩ : syracuseStep 1857439 = 2786159) B2786159
theorem B17840179 : Blo 1855629 17840179 := bstep (se 1 (by rfl) ⟨13380134, by rfl⟩ : syracuseStep 17840179 = 26760269) B26760269
theorem B1857607 : Blo 1855629 1857607 := bstep (se 1 (by rfl) ⟨1393205, by rfl⟩ : syracuseStep 1857607 = 2786411) B2786411
theorem B23795927 : Blo 1855629 23795927 := bstep (se 1 (by rfl) ⟨17846945, by rfl⟩ : syracuseStep 23795927 = 35693891) B35693891
theorem B4176107 : Blo 1855629 4176107 := bstep (se 1 (by rfl) ⟨3132080, by rfl⟩ : syracuseStep 4176107 = 6264161) B6264161
theorem B2382239 : Blo 1855629 2382239 := bstep (se 1 (by rfl) ⟨1786679, by rfl⟩ : syracuseStep 2382239 = 3573359) B3573359
theorem B22903235 : Blo 1855629 22903235 := bstep (se 1 (by rfl) ⟨17177426, by rfl⟩ : syracuseStep 22903235 = 34354853) B34354853
theorem B2783687 : Blo 1855629 2783687 := bstep (se 1 (by rfl) ⟨2087765, by rfl⟩ : syracuseStep 2783687 = 4175531) B4175531
theorem B16071247 : Blo 1855629 16071247 := bstep (se 1 (by rfl) ⟨12053435, by rfl⟩ : syracuseStep 16071247 = 24106871) B24106871
theorem B14105177 : Blo 1855629 14105177 := bstep (se 2 (by rfl) ⟨5289441, by rfl⟩ : syracuseStep 14105177 = 10578883) B10578883
theorem B2783903 : Blo 1855629 2783903 := bstep (se 1 (by rfl) ⟨2087927, by rfl⟩ : syracuseStep 2783903 = 4175855) B4175855
theorem B2784047 : Blo 1855629 2784047 := bstep (se 1 (by rfl) ⟨2088035, by rfl⟩ : syracuseStep 2784047 = 4176071) B4176071
theorem B2644807 : Blo 1855629 2644807 := bstep (se 1 (by rfl) ⟨1983605, by rfl⟩ : syracuseStep 2644807 = 3967211) B3967211
theorem B2784167 : Blo 1855629 2784167 := bstep (se 1 (by rfl) ⟨2088125, by rfl⟩ : syracuseStep 2784167 = 4176251) B4176251
theorem B2784347 : Blo 1855629 2784347 := bstep (se 1 (by rfl) ⟨2088260, by rfl⟩ : syracuseStep 2784347 = 4176521) B4176521
theorem B15858827 : Blo 1855629 15858827 := bstep (se 1 (by rfl) ⟨11894120, by rfl⟩ : syracuseStep 15858827 = 23788241) B23788241
theorem B3964135 : Blo 1855629 3964135 := bstep (se 1 (by rfl) ⟨2973101, by rfl⟩ : syracuseStep 3964135 = 5946203) B5946203
theorem B9788701 : Blo 1855629 9788701 := bstep (se 3 (by rfl) ⟨1835381, by rfl⟩ : syracuseStep 9788701 = 3670763) B3670763
theorem B11902247 : Blo 1855629 11902247 := bstep (se 1 (by rfl) ⟨8926685, by rfl⟩ : syracuseStep 11902247 = 17853371) B17853371
theorem B2972999 : Blo 1855629 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B8469929 : Blo 1855629 8469929 := bstep (se 2 (by rfl) ⟨3176223, by rfl⟩ : syracuseStep 8469929 = 6352447) B6352447
theorem B2784719 : Blo 1855629 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B4177403 : Blo 1855629 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B27131453 : Blo 1855629 27131453 := bstep (se 3 (by rfl) ⟨5087147, by rfl⟩ : syracuseStep 27131453 = 10174295) B10174295
theorem B9395837 : Blo 1855629 9395837 := bstep (se 3 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 9395837 = 3523439) B3523439
theorem B4177583 : Blo 1855629 4177583 := bstep (se 1 (by rfl) ⟨3133187, by rfl⟩ : syracuseStep 4177583 = 6266375) B6266375
theorem B3964639 : Blo 1855629 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B2088679 : Blo 1855629 2088679 := bstep (se 1 (by rfl) ⟨1566509, by rfl⟩ : syracuseStep 2088679 = 3133019) B3133019
theorem B4177673 : Blo 1855629 4177673 := bstep (se 2 (by rfl) ⟨1566627, by rfl⟩ : syracuseStep 4177673 = 3133255) B3133255
theorem B6348575 : Blo 1855629 6348575 := bstep (se 1 (by rfl) ⟨4761431, by rfl⟩ : syracuseStep 6348575 = 9522863) B9522863
theorem B9395999 : Blo 1855629 9395999 := bstep (se 1 (by rfl) ⟨7046999, by rfl⟩ : syracuseStep 9395999 = 14093999) B14093999
theorem B15048503 : Blo 1855629 15048503 := bstep (se 1 (by rfl) ⟨11286377, by rfl⟩ : syracuseStep 15048503 = 22572755) B22572755
theorem B2785103 : Blo 1855629 2785103 := bstep (se 1 (by rfl) ⟨2088827, by rfl⟩ : syracuseStep 2785103 = 4177655) B4177655
theorem B2785223 : Blo 1855629 2785223 := bstep (se 1 (by rfl) ⟨2088917, by rfl⟩ : syracuseStep 2785223 = 4177835) B4177835
theorem B45162629 : Blo 1855629 45162629 := bstep (se 4 (by rfl) ⟨4233996, by rfl⟩ : syracuseStep 45162629 = 8467993) B8467993
theorem B2785535 : Blo 1855629 2785535 := bstep (se 1 (by rfl) ⟨2089151, by rfl⟩ : syracuseStep 2785535 = 4178303) B4178303
theorem B5357963 : Blo 1855629 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B2785691 : Blo 1855629 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B9396971 : Blo 1855629 9396971 := bstep (se 1 (by rfl) ⟨7047728, by rfl⟩ : syracuseStep 9396971 = 14095457) B14095457
theorem B2786111 : Blo 1855629 2786111 := bstep (se 1 (by rfl) ⟨2089583, by rfl⟩ : syracuseStep 2786111 = 4179167) B4179167
theorem B2786255 : Blo 1855629 2786255 := bstep (se 1 (by rfl) ⟨2089691, by rfl⟩ : syracuseStep 2786255 = 4179383) B4179383
theorem B22594547 : Blo 1855629 22594547 := bstep (se 1 (by rfl) ⟨16945910, by rfl⟩ : syracuseStep 22594547 = 33891821) B33891821
theorem B2786345 : Blo 1855629 2786345 := bstep (se 2 (by rfl) ⟨1044879, by rfl⟩ : syracuseStep 2786345 = 2089759) B2089759
theorem B3966023 : Blo 1855629 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B2786375 : Blo 1855629 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B21193807 : Blo 1855629 21193807 := bstep (se 1 (by rfl) ⟨15895355, by rfl⟩ : syracuseStep 21193807 = 31790711) B31790711
theorem B11289689 : Blo 1855629 11289689 := bstep (se 2 (by rfl) ⟨4233633, by rfl⟩ : syracuseStep 11289689 = 8467267) B8467267
theorem B47580371 : Blo 1855629 47580371 := bstep (se 1 (by rfl) ⟨35685278, by rfl⟩ : syracuseStep 47580371 = 71370557) B71370557
theorem B16942409 : Blo 1855629 16942409 := bstep (se 2 (by rfl) ⟨6353403, by rfl⟩ : syracuseStep 16942409 = 12706807) B12706807
theorem B6030875 : Blo 1855629 6030875 := bstep (se 1 (by rfl) ⟨4523156, by rfl⟩ : syracuseStep 6030875 = 9046313) B9046313
theorem B5285513 : Blo 1855629 5285513 := bstep (se 2 (by rfl) ⟨1982067, by rfl⟩ : syracuseStep 5285513 = 3964135) B3964135
theorem B13051601 : Blo 1855629 13051601 := bstep (se 2 (by rfl) ⟨4894350, by rfl⟩ : syracuseStep 13051601 = 9788701) B9788701
theorem B6612857 : Blo 1855629 6612857 := bstep (se 2 (by rfl) ⟨2479821, by rfl⟩ : syracuseStep 6612857 = 4959643) B4959643
theorem B3131419 : Blo 1855629 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B3524791 : Blo 1855629 3524791 := bstep (se 1 (by rfl) ⟨2643593, by rfl⟩ : syracuseStep 3524791 = 5287187) B5287187
theorem B5646619 : Blo 1855629 5646619 := bstep (se 1 (by rfl) ⟨4234964, by rfl⟩ : syracuseStep 5646619 = 8469929) B8469929
theorem B5286185 : Blo 1855629 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B7047593 : Blo 1855629 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B13388267 : Blo 1855629 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B3525383 : Blo 1855629 3525383 := bstep (se 1 (by rfl) ⟨2644037, by rfl⟩ : syracuseStep 3525383 = 5288075) B5288075
theorem B5360987 : Blo 1855629 5360987 := bstep (se 1 (by rfl) ⟨4020740, by rfl⟩ : syracuseStep 5360987 = 8041481) B8041481
theorem B6352637 : Blo 1855629 6352637 := bstep (se 3 (by rfl) ⟨1191119, by rfl⟩ : syracuseStep 6352637 = 2382239) B2382239
theorem B3526409 : Blo 1855629 3526409 := bstep (se 2 (by rfl) ⟨1322403, by rfl⟩ : syracuseStep 3526409 = 2644807) B2644807
theorem B15863951 : Blo 1855629 15863951 := bstep (se 1 (by rfl) ⟨11897963, by rfl⟩ : syracuseStep 15863951 = 23795927) B23795927
theorem B9400535 : Blo 1855629 9400535 := bstep (se 1 (by rfl) ⟨7050401, by rfl⟩ : syracuseStep 9400535 = 14100803) B14100803
theorem B4460777 : Blo 1855629 4460777 := bstep (se 2 (by rfl) ⟨1672791, by rfl⟩ : syracuseStep 4460777 = 3345583) B3345583
theorem B1855791 : Blo 1855629 1855791 := bstep (se 1 (by rfl) ⟨1391843, by rfl⟩ : syracuseStep 1855791 = 2783687) B2783687
theorem B4698425 : Blo 1855629 4698425 := bstep (se 2 (by rfl) ⟨1761909, by rfl⟩ : syracuseStep 4698425 = 3523819) B3523819
theorem B8925551 : Blo 1855629 8925551 := bstep (se 1 (by rfl) ⟨6694163, by rfl⟩ : syracuseStep 8925551 = 13388327) B13388327
theorem B1855935 : Blo 1855629 1855935 := bstep (se 1 (by rfl) ⟨1391951, by rfl⟩ : syracuseStep 1855935 = 2783903) B2783903
theorem B1856031 : Blo 1855629 1856031 := bstep (se 1 (by rfl) ⟨1392023, by rfl⟩ : syracuseStep 1856031 = 2784047) B2784047
theorem B18592343 : Blo 1855629 18592343 := bstep (se 1 (by rfl) ⟨13944257, by rfl⟩ : syracuseStep 18592343 = 27888515) B27888515
theorem B1856111 : Blo 1855629 1856111 := bstep (se 1 (by rfl) ⟨1392083, by rfl⟩ : syracuseStep 1856111 = 2784167) B2784167
theorem B21148289 : Blo 1855629 21148289 := bstep (se 2 (by rfl) ⟨7930608, by rfl⟩ : syracuseStep 21148289 = 15861217) B15861217
theorem B1856231 : Blo 1855629 1856231 := bstep (se 1 (by rfl) ⟨1392173, by rfl⟩ : syracuseStep 1856231 = 2784347) B2784347
theorem B16929533 : Blo 1855629 16929533 := bstep (se 3 (by rfl) ⟨3174287, by rfl⟩ : syracuseStep 16929533 = 6348575) B6348575
theorem B10572551 : Blo 1855629 10572551 := bstep (se 1 (by rfl) ⟨7929413, by rfl⟩ : syracuseStep 10572551 = 15858827) B15858827
theorem B5288759 : Blo 1855629 5288759 := bstep (se 1 (by rfl) ⟨3966569, by rfl⟩ : syracuseStep 5288759 = 7933139) B7933139
theorem B7934831 : Blo 1855629 7934831 := bstep (se 1 (by rfl) ⟨5951123, by rfl⟩ : syracuseStep 7934831 = 11902247) B11902247
theorem B5018525 : Blo 1855629 5018525 := bstep (se 3 (by rfl) ⟨940973, by rfl⟩ : syracuseStep 5018525 = 1881947) B1881947
theorem B1856479 : Blo 1855629 1856479 := bstep (se 1 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 1856479 = 2784719) B2784719
theorem B6263891 : Blo 1855629 6263891 := bstep (se 1 (by rfl) ⟨4697918, by rfl⟩ : syracuseStep 6263891 = 9395837) B9395837
theorem B6263999 : Blo 1855629 6263999 := bstep (se 1 (by rfl) ⟨4697999, by rfl⟩ : syracuseStep 6263999 = 9395999) B9395999
theorem B10032335 : Blo 1855629 10032335 := bstep (se 1 (by rfl) ⟨7524251, by rfl⟩ : syracuseStep 10032335 = 15048503) B15048503
theorem B1856735 : Blo 1855629 1856735 := bstep (se 1 (by rfl) ⟨1392551, by rfl⟩ : syracuseStep 1856735 = 2785103) B2785103
theorem B1856815 : Blo 1855629 1856815 := bstep (se 1 (by rfl) ⟨1392611, by rfl⟩ : syracuseStep 1856815 = 2785223) B2785223
theorem B23786905 : Blo 1855629 23786905 := bstep (se 2 (by rfl) ⟨8920089, by rfl⟩ : syracuseStep 23786905 = 17840179) B17840179
theorem B4175279 : Blo 1855629 4175279 := bstep (se 1 (by rfl) ⟨3131459, by rfl⟩ : syracuseStep 4175279 = 6262919) B6262919
theorem B4175387 : Blo 1855629 4175387 := bstep (se 1 (by rfl) ⟨3131540, by rfl⟩ : syracuseStep 4175387 = 6263081) B6263081
theorem B1857055 : Blo 1855629 1857055 := bstep (se 1 (by rfl) ⟨1392791, by rfl⟩ : syracuseStep 1857055 = 2785583) B2785583
theorem B6264431 : Blo 1855629 6264431 := bstep (se 1 (by rfl) ⟨4698323, by rfl⟩ : syracuseStep 6264431 = 9396647) B9396647
theorem B5944985 : Blo 1855629 5944985 := bstep (se 2 (by rfl) ⟨2229369, by rfl⟩ : syracuseStep 5944985 = 4458739) B4458739
theorem B1857215 : Blo 1855629 1857215 := bstep (se 1 (by rfl) ⟨1392911, by rfl⟩ : syracuseStep 1857215 = 2785823) B2785823
theorem B4175567 : Blo 1855629 4175567 := bstep (se 1 (by rfl) ⟨3131675, by rfl⟩ : syracuseStep 4175567 = 6263351) B6263351
theorem B6690529 : Blo 1855629 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B40163161 : Blo 1855629 40163161 := bstep (se 2 (by rfl) ⟨15061185, by rfl⟩ : syracuseStep 40163161 = 30122371) B30122371
theorem B17840027 : Blo 1855629 17840027 := bstep (se 1 (by rfl) ⟨13380020, by rfl⟩ : syracuseStep 17840027 = 26760041) B26760041
theorem B22591433 : Blo 1855629 22591433 := bstep (se 2 (by rfl) ⟨8471787, by rfl⟩ : syracuseStep 22591433 = 16943575) B16943575
theorem B9394217 : Blo 1855629 9394217 := bstep (se 2 (by rfl) ⟨3522831, by rfl⟩ : syracuseStep 9394217 = 7045663) B7045663
theorem B21428329 : Blo 1855629 21428329 := bstep (se 2 (by rfl) ⟨8035623, by rfl⟩ : syracuseStep 21428329 = 16071247) B16071247
theorem B2783543 : Blo 1855629 2783543 := bstep (se 1 (by rfl) ⟨2087657, by rfl⟩ : syracuseStep 2783543 = 4175315) B4175315
theorem B5945831 : Blo 1855629 5945831 := bstep (se 1 (by rfl) ⟨4459373, by rfl⟩ : syracuseStep 5945831 = 8918747) B8918747
theorem B4176359 : Blo 1855629 4176359 := bstep (se 1 (by rfl) ⟨3132269, by rfl⟩ : syracuseStep 4176359 = 6264539) B6264539
theorem B2783723 : Blo 1855629 2783723 := bstep (se 1 (by rfl) ⟨2087792, by rfl⟩ : syracuseStep 2783723 = 4175585) B4175585
theorem B4700663 : Blo 1855629 4700663 := bstep (se 1 (by rfl) ⟨3525497, by rfl⟩ : syracuseStep 4700663 = 7050995) B7050995
theorem B4700713 : Blo 1855629 4700713 := bstep (se 2 (by rfl) ⟨1762767, by rfl⟩ : syracuseStep 4700713 = 3525535) B3525535
theorem B2087743 : Blo 1855629 2087743 := bstep (se 1 (by rfl) ⟨1565807, by rfl⟩ : syracuseStep 2087743 = 3131615) B3131615
theorem B2784071 : Blo 1855629 2784071 := bstep (se 1 (by rfl) ⟨2088053, by rfl⟩ : syracuseStep 2784071 = 4176107) B4176107
theorem B2644903 : Blo 1855629 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B15268823 : Blo 1855629 15268823 := bstep (se 1 (by rfl) ⟨11451617, by rfl⟩ : syracuseStep 15268823 = 22903235) B22903235
theorem B6265835 : Blo 1855629 6265835 := bstep (se 1 (by rfl) ⟨4699376, by rfl⟩ : syracuseStep 6265835 = 9398753) B9398753
theorem B9403451 : Blo 1855629 9403451 := bstep (se 1 (by rfl) ⟨7052588, by rfl⟩ : syracuseStep 9403451 = 14105177) B14105177
theorem B6692015 : Blo 1855629 6692015 := bstep (se 1 (by rfl) ⟨5019011, by rfl⟩ : syracuseStep 6692015 = 10038023) B10038023
theorem B8469785 : Blo 1855629 8469785 := bstep (se 2 (by rfl) ⟨3176169, by rfl⟩ : syracuseStep 8469785 = 6352339) B6352339
theorem B2088319 : Blo 1855629 2088319 := bstep (se 1 (by rfl) ⟨1566239, by rfl⟩ : syracuseStep 2088319 = 3132479) B3132479
theorem B1981999 : Blo 1855629 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B2784905 : Blo 1855629 2784905 := bstep (se 2 (by rfl) ⟨1044339, by rfl⟩ : syracuseStep 2784905 = 2088679) B2088679
theorem B2784935 : Blo 1855629 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B18087635 : Blo 1855629 18087635 := bstep (se 1 (by rfl) ⟨13565726, by rfl⟩ : syracuseStep 18087635 = 27131453) B27131453
theorem B2785055 : Blo 1855629 2785055 := bstep (se 1 (by rfl) ⟨2088791, by rfl⟩ : syracuseStep 2785055 = 4177583) B4177583
theorem B2785115 : Blo 1855629 2785115 := bstep (se 1 (by rfl) ⟨2088836, by rfl⟩ : syracuseStep 2785115 = 4177673) B4177673
theorem B7528403 : Blo 1855629 7528403 := bstep (se 1 (by rfl) ⟨5646302, by rfl⟩ : syracuseStep 7528403 = 11292605) B11292605
theorem B10575967 : Blo 1855629 10575967 := bstep (se 1 (by rfl) ⟨7931975, by rfl⟩ : syracuseStep 10575967 = 15863951) B15863951
theorem B6267023 : Blo 1855629 6267023 := bstep (se 1 (by rfl) ⟨4700267, by rfl⟩ : syracuseStep 6267023 = 9400535) B9400535
theorem B2973851 : Blo 1855629 2973851 := bstep (se 1 (by rfl) ⟨2230388, by rfl⟩ : syracuseStep 2973851 = 4460777) B4460777
theorem B3571975 : Blo 1855629 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B7528825 : Blo 1855629 7528825 := bstep (se 2 (by rfl) ⟨2823309, by rfl⟩ : syracuseStep 7528825 = 5646619) B5646619
theorem B12394895 : Blo 1855629 12394895 := bstep (se 1 (by rfl) ⟨9296171, by rfl⟩ : syracuseStep 12394895 = 18592343) B18592343
theorem B14098859 : Blo 1855629 14098859 := bstep (se 1 (by rfl) ⟨10574144, by rfl⟩ : syracuseStep 14098859 = 21148289) B21148289
theorem B6267617 : Blo 1855629 6267617 := bstep (se 2 (by rfl) ⟨2350356, by rfl⟩ : syracuseStep 6267617 = 4700713) B4700713
theorem B31720247 : Blo 1855629 31720247 := bstep (se 1 (by rfl) ⟨23790185, by rfl⟩ : syracuseStep 31720247 = 47580371) B47580371
theorem B3523675 : Blo 1855629 3523675 := bstep (se 1 (by rfl) ⟨2642756, by rfl⟩ : syracuseStep 3523675 = 5285513) B5285513
theorem B8701067 : Blo 1855629 8701067 := bstep (se 1 (by rfl) ⟨6525800, by rfl⟩ : syracuseStep 8701067 = 13051601) B13051601
theorem B4408571 : Blo 1855629 4408571 := bstep (se 1 (by rfl) ⟨3306428, by rfl⟩ : syracuseStep 4408571 = 6612857) B6612857
theorem B35702045 : Blo 1855629 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B16082333 : Blo 1855629 16082333 := bstep (se 3 (by rfl) ⟨3015437, by rfl⟩ : syracuseStep 16082333 = 6030875) B6030875
theorem B3524123 : Blo 1855629 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B6268967 : Blo 1855629 6268967 := bstep (se 1 (by rfl) ⟨4701725, by rfl⟩ : syracuseStep 6268967 = 9403451) B9403451
theorem B5646523 : Blo 1855629 5646523 := bstep (se 1 (by rfl) ⟨4234892, by rfl⟩ : syracuseStep 5646523 = 8469785) B8469785
theorem B3573991 : Blo 1855629 3573991 := bstep (se 1 (by rfl) ⟨2680493, by rfl⟩ : syracuseStep 3573991 = 5360987) B5360987
theorem B30108419 : Blo 1855629 30108419 := bstep (se 1 (by rfl) ⟨22581314, by rfl⟩ : syracuseStep 30108419 = 45162629) B45162629
theorem B3132283 : Blo 1855629 3132283 := bstep (se 1 (by rfl) ⟨2349212, by rfl⟩ : syracuseStep 3132283 = 4698425) B4698425
theorem B5950367 : Blo 1855629 5950367 := bstep (se 1 (by rfl) ⟨4462775, by rfl⟩ : syracuseStep 5950367 = 8925551) B8925551
theorem B10570661 : Blo 1855629 10570661 := bstep (se 4 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 10570661 = 1981999) B1981999
theorem B17845373 : Blo 1855629 17845373 := bstep (se 3 (by rfl) ⟨3346007, by rfl⟩ : syracuseStep 17845373 = 6692015) B6692015
theorem B7048367 : Blo 1855629 7048367 := bstep (se 1 (by rfl) ⟨5286275, by rfl⟩ : syracuseStep 7048367 = 10572551) B10572551
theorem B3525839 : Blo 1855629 3525839 := bstep (se 1 (by rfl) ⟨2644379, by rfl⟩ : syracuseStep 3525839 = 5288759) B5288759
theorem B3345683 : Blo 1855629 3345683 := bstep (se 1 (by rfl) ⟨2509262, by rfl⟩ : syracuseStep 3345683 = 5018525) B5018525
theorem B6688223 : Blo 1855629 6688223 := bstep (se 1 (by rfl) ⟨5016167, by rfl⟩ : syracuseStep 6688223 = 10032335) B10032335
theorem B6262811 : Blo 1855629 6262811 := bstep (se 1 (by rfl) ⟨4697108, by rfl⟩ : syracuseStep 6262811 = 9394217) B9394217
theorem B28258409 : Blo 1855629 28258409 := bstep (se 2 (by rfl) ⟨10596903, by rfl⟩ : syracuseStep 28258409 = 21193807) B21193807
theorem B1855695 : Blo 1855629 1855695 := bstep (se 1 (by rfl) ⟨1391771, by rfl⟩ : syracuseStep 1855695 = 2783543) B2783543
theorem B4698395 : Blo 1855629 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B1855815 : Blo 1855629 1855815 := bstep (se 1 (by rfl) ⟨1391861, by rfl⟩ : syracuseStep 1855815 = 2783723) B2783723
theorem B3133775 : Blo 1855629 3133775 := bstep (se 1 (by rfl) ⟨2350331, by rfl⟩ : syracuseStep 3133775 = 4700663) B4700663
theorem B31715873 : Blo 1855629 31715873 := bstep (se 2 (by rfl) ⟨11893452, by rfl⟩ : syracuseStep 31715873 = 23786905) B23786905
theorem B1856047 : Blo 1855629 1856047 := bstep (se 1 (by rfl) ⟨1392035, by rfl⟩ : syracuseStep 1856047 = 2784071) B2784071
theorem B10179215 : Blo 1855629 10179215 := bstep (se 1 (by rfl) ⟨7634411, by rfl⟩ : syracuseStep 10179215 = 15268823) B15268823
theorem B9401021 : Blo 1855629 9401021 := bstep (se 3 (by rfl) ⟨1762691, by rfl⟩ : syracuseStep 9401021 = 3525383) B3525383
theorem B1856603 : Blo 1855629 1856603 := bstep (se 1 (by rfl) ⟨1392452, by rfl⟩ : syracuseStep 1856603 = 2784905) B2784905
theorem B1856623 : Blo 1855629 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B1856703 : Blo 1855629 1856703 := bstep (se 1 (by rfl) ⟨1392527, by rfl⟩ : syracuseStep 1856703 = 2785055) B2785055
theorem B1856743 : Blo 1855629 1856743 := bstep (se 1 (by rfl) ⟨1392557, by rfl⟩ : syracuseStep 1856743 = 2785115) B2785115
theorem B67761461 : Blo 1855629 67761461 := bstep (se 5 (by rfl) ⟨3176318, by rfl⟩ : syracuseStep 67761461 = 6352637) B6352637
theorem B5018935 : Blo 1855629 5018935 := bstep (se 1 (by rfl) ⟨3764201, by rfl⟩ : syracuseStep 5018935 = 7528403) B7528403
theorem B4175225 : Blo 1855629 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B28571105 : Blo 1855629 28571105 := bstep (se 2 (by rfl) ⟨10714164, by rfl⟩ : syracuseStep 28571105 = 21428329) B21428329
theorem B1857023 : Blo 1855629 1857023 := bstep (se 1 (by rfl) ⟨1392767, by rfl⟩ : syracuseStep 1857023 = 2785535) B2785535
theorem B4699721 : Blo 1855629 4699721 := bstep (se 2 (by rfl) ⟨1762395, by rfl⟩ : syracuseStep 4699721 = 3524791) B3524791
theorem B1857127 : Blo 1855629 1857127 := bstep (se 1 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 1857127 = 2785691) B2785691
theorem B6264647 : Blo 1855629 6264647 := bstep (se 1 (by rfl) ⟨4698485, by rfl⟩ : syracuseStep 6264647 = 9396971) B9396971
theorem B1857407 : Blo 1855629 1857407 := bstep (se 1 (by rfl) ⟨1393055, by rfl⟩ : syracuseStep 1857407 = 2786111) B2786111
theorem B5289887 : Blo 1855629 5289887 := bstep (se 1 (by rfl) ⟨3967415, by rfl⟩ : syracuseStep 5289887 = 7934831) B7934831
theorem B1857503 : Blo 1855629 1857503 := bstep (se 1 (by rfl) ⟨1393127, by rfl⟩ : syracuseStep 1857503 = 2786255) B2786255
theorem B15063031 : Blo 1855629 15063031 := bstep (se 1 (by rfl) ⟨11297273, by rfl⟩ : syracuseStep 15063031 = 22594547) B22594547
theorem B1857563 : Blo 1855629 1857563 := bstep (se 1 (by rfl) ⟨1393172, by rfl⟩ : syracuseStep 1857563 = 2786345) B2786345
theorem B2644015 : Blo 1855629 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B1857583 : Blo 1855629 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B4175927 : Blo 1855629 4175927 := bstep (se 1 (by rfl) ⟨3131945, by rfl⟩ : syracuseStep 4175927 = 6263891) B6263891
theorem B7526459 : Blo 1855629 7526459 := bstep (se 1 (by rfl) ⟨5644844, by rfl⟩ : syracuseStep 7526459 = 11289689) B11289689
theorem B4175999 : Blo 1855629 4175999 := bstep (se 1 (by rfl) ⟨3131999, by rfl⟩ : syracuseStep 4175999 = 6263999) B6263999
theorem B11294939 : Blo 1855629 11294939 := bstep (se 1 (by rfl) ⟨8471204, by rfl⟩ : syracuseStep 11294939 = 16942409) B16942409
theorem B2783519 : Blo 1855629 2783519 := bstep (se 1 (by rfl) ⟨2087639, by rfl⟩ : syracuseStep 2783519 = 4175279) B4175279
theorem B2783591 : Blo 1855629 2783591 := bstep (se 1 (by rfl) ⟨2087693, by rfl⟩ : syracuseStep 2783591 = 4175387) B4175387
theorem B4176287 : Blo 1855629 4176287 := bstep (se 1 (by rfl) ⟨3132215, by rfl⟩ : syracuseStep 4176287 = 6264431) B6264431
theorem B2783657 : Blo 1855629 2783657 := bstep (se 2 (by rfl) ⟨1043871, by rfl⟩ : syracuseStep 2783657 = 2087743) B2087743
theorem B3963323 : Blo 1855629 3963323 := bstep (se 1 (by rfl) ⟨2972492, by rfl⟩ : syracuseStep 3963323 = 5944985) B5944985
theorem B2783711 : Blo 1855629 2783711 := bstep (se 1 (by rfl) ⟨2087783, by rfl⟩ : syracuseStep 2783711 = 4175567) B4175567
theorem B11893351 : Blo 1855629 11893351 := bstep (se 1 (by rfl) ⟨8920013, by rfl⟩ : syracuseStep 11893351 = 17840027) B17840027
theorem B3963887 : Blo 1855629 3963887 := bstep (se 1 (by rfl) ⟨2972915, by rfl⟩ : syracuseStep 3963887 = 5945831) B5945831
theorem B2784239 : Blo 1855629 2784239 := bstep (se 1 (by rfl) ⟨2088179, by rfl⟩ : syracuseStep 2784239 = 4176359) B4176359
theorem B2784425 : Blo 1855629 2784425 := bstep (se 2 (by rfl) ⟨1044159, by rfl⟩ : syracuseStep 2784425 = 2088319) B2088319
theorem B48233693 : Blo 1855629 48233693 := bstep (se 3 (by rfl) ⟨9043817, by rfl⟩ : syracuseStep 48233693 = 18087635) B18087635
theorem B4177223 : Blo 1855629 4177223 := bstep (se 1 (by rfl) ⟨3132917, by rfl⟩ : syracuseStep 4177223 = 6265835) B6265835
theorem B45145421 : Blo 1855629 45145421 := bstep (se 3 (by rfl) ⟨8464766, by rfl⟩ : syracuseStep 45145421 = 16929533) B16929533
theorem B14106149 : Blo 1855629 14106149 := bstep (se 4 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 14106149 = 2644903) B2644903
theorem B8920705 : Blo 1855629 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B53550881 : Blo 1855629 53550881 := bstep (se 2 (by rfl) ⟨20081580, by rfl⟩ : syracuseStep 53550881 = 40163161) B40163161
theorem B2350939 : Blo 1855629 2350939 := bstep (se 1 (by rfl) ⟨1763204, by rfl⟩ : syracuseStep 2350939 = 3526409) B3526409
theorem B60243821 : Blo 1855629 60243821 := bstep (se 3 (by rfl) ⟨11295716, by rfl⟩ : syracuseStep 60243821 = 22591433) B22591433
theorem B4178015 : Blo 1855629 4178015 := bstep (se 1 (by rfl) ⟨3133511, by rfl⟩ : syracuseStep 4178015 = 6267023) B6267023
theorem B1982567 : Blo 1855629 1982567 := bstep (se 1 (by rfl) ⟨1486925, by rfl⟩ : syracuseStep 1982567 = 2973851) B2973851
theorem B2089183 : Blo 1855629 2089183 := bstep (se 1 (by rfl) ⟨1566887, by rfl⟩ : syracuseStep 2089183 = 3133775) B3133775
theorem B7528697 : Blo 1855629 7528697 := bstep (se 2 (by rfl) ⟨2823261, by rfl⟩ : syracuseStep 7528697 = 5646523) B5646523
theorem B21143915 : Blo 1855629 21143915 := bstep (se 1 (by rfl) ⟨15857936, by rfl⟩ : syracuseStep 21143915 = 31715873) B31715873
theorem B6267347 : Blo 1855629 6267347 := bstep (se 1 (by rfl) ⟨4700510, by rfl⟩ : syracuseStep 6267347 = 9401021) B9401021
theorem B4178411 : Blo 1855629 4178411 := bstep (se 1 (by rfl) ⟨3133808, by rfl⟩ : syracuseStep 4178411 = 6267617) B6267617
theorem B8921821 : Blo 1855629 8921821 := bstep (se 3 (by rfl) ⟨1672841, by rfl⟩ : syracuseStep 8921821 = 3345683) B3345683
theorem B19047403 : Blo 1855629 19047403 := bstep (se 1 (by rfl) ⟨14285552, by rfl⟩ : syracuseStep 19047403 = 28571105) B28571105
theorem B4179311 : Blo 1855629 4179311 := bstep (se 1 (by rfl) ⟨3134483, by rfl⟩ : syracuseStep 4179311 = 6268967) B6268967
theorem B7529959 : Blo 1855629 7529959 := bstep (se 1 (by rfl) ⟨5647469, by rfl⟩ : syracuseStep 7529959 = 11294939) B11294939
theorem B20072279 : Blo 1855629 20072279 := bstep (se 1 (by rfl) ⟨15054209, by rfl⟩ : syracuseStep 20072279 = 30108419) B30108419
theorem B3966911 : Blo 1855629 3966911 := bstep (se 1 (by rfl) ⟨2975183, by rfl⟩ : syracuseStep 3966911 = 5950367) B5950367
theorem B7047107 : Blo 1855629 7047107 := bstep (se 1 (by rfl) ⟨5285330, by rfl⟩ : syracuseStep 7047107 = 10570661) B10570661
theorem B11896915 : Blo 1855629 11896915 := bstep (se 1 (by rfl) ⟨8922686, by rfl⟩ : syracuseStep 11896915 = 17845373) B17845373
theorem B32155795 : Blo 1855629 32155795 := bstep (se 1 (by rfl) ⟨24116846, by rfl⟩ : syracuseStep 32155795 = 48233693) B48233693
theorem B4458815 : Blo 1855629 4458815 := bstep (se 1 (by rfl) ⟨3344111, by rfl⟩ : syracuseStep 4458815 = 6688223) B6688223
theorem B3525353 : Blo 1855629 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B14101289 : Blo 1855629 14101289 := bstep (se 2 (by rfl) ⟨5287983, by rfl⟩ : syracuseStep 14101289 = 10575967) B10575967
theorem B3132263 : Blo 1855629 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B9399239 : Blo 1855629 9399239 := bstep (se 1 (by rfl) ⟨7049429, by rfl⟩ : syracuseStep 9399239 = 14098859) B14098859
theorem B4762633 : Blo 1855629 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B23202845 : Blo 1855629 23202845 := bstep (se 3 (by rfl) ⟨4350533, by rfl⟩ : syracuseStep 23202845 = 8701067) B8701067
theorem B6786143 : Blo 1855629 6786143 := bstep (se 1 (by rfl) ⟨5089607, by rfl⟩ : syracuseStep 6786143 = 10179215) B10179215
theorem B10038433 : Blo 1855629 10038433 := bstep (se 2 (by rfl) ⟨3764412, by rfl⟩ : syracuseStep 10038433 = 7528825) B7528825
theorem B21146831 : Blo 1855629 21146831 := bstep (se 1 (by rfl) ⟨15860123, by rfl⟩ : syracuseStep 21146831 = 31720247) B31720247
theorem B23801363 : Blo 1855629 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B45174307 : Blo 1855629 45174307 := bstep (se 1 (by rfl) ⟨33880730, by rfl⟩ : syracuseStep 45174307 = 67761461) B67761461
theorem B3133147 : Blo 1855629 3133147 := bstep (se 1 (by rfl) ⟨2349860, by rfl⟩ : syracuseStep 3133147 = 4699721) B4699721
theorem B3526591 : Blo 1855629 3526591 := bstep (se 1 (by rfl) ⟨2644943, by rfl⟩ : syracuseStep 3526591 = 5289887) B5289887
theorem B5017639 : Blo 1855629 5017639 := bstep (se 1 (by rfl) ⟨3763229, by rfl⟩ : syracuseStep 5017639 = 7526459) B7526459
theorem B4698233 : Blo 1855629 4698233 := bstep (se 2 (by rfl) ⟨1761837, by rfl⟩ : syracuseStep 4698233 = 3523675) B3523675
theorem B1855679 : Blo 1855629 1855679 := bstep (se 1 (by rfl) ⟨1391759, by rfl⟩ : syracuseStep 1855679 = 2783519) B2783519
theorem B1855727 : Blo 1855629 1855727 := bstep (se 1 (by rfl) ⟨1391795, by rfl⟩ : syracuseStep 1855727 = 2783591) B2783591
theorem B1855771 : Blo 1855629 1855771 := bstep (se 1 (by rfl) ⟨1391828, by rfl⟩ : syracuseStep 1855771 = 2783657) B2783657
theorem B2642215 : Blo 1855629 2642215 := bstep (se 1 (by rfl) ⟨1981661, by rfl⟩ : syracuseStep 2642215 = 3963323) B3963323
theorem B1855807 : Blo 1855629 1855807 := bstep (se 1 (by rfl) ⟨1391855, by rfl⟩ : syracuseStep 1855807 = 2783711) B2783711
theorem B2642591 : Blo 1855629 2642591 := bstep (se 1 (by rfl) ⟨1981943, by rfl⟩ : syracuseStep 2642591 = 3963887) B3963887
theorem B1856159 : Blo 1855629 1856159 := bstep (se 1 (by rfl) ⟨1392119, by rfl⟩ : syracuseStep 1856159 = 2784239) B2784239
theorem B1856283 : Blo 1855629 1856283 := bstep (se 1 (by rfl) ⟨1392212, by rfl⟩ : syracuseStep 1856283 = 2784425) B2784425
theorem B4698911 : Blo 1855629 4698911 := bstep (se 1 (by rfl) ⟨3524183, by rfl⟩ : syracuseStep 4698911 = 7048367) B7048367
theorem B3134585 : Blo 1855629 3134585 := bstep (se 2 (by rfl) ⟨1175469, by rfl⟩ : syracuseStep 3134585 = 2350939) B2350939
theorem B40162547 : Blo 1855629 40162547 := bstep (se 1 (by rfl) ⟨30121910, by rfl⟩ : syracuseStep 40162547 = 60243821) B60243821
theorem B20084041 : Blo 1855629 20084041 := bstep (se 2 (by rfl) ⟨7531515, by rfl⟩ : syracuseStep 20084041 = 15063031) B15063031
theorem B4175207 : Blo 1855629 4175207 := bstep (se 1 (by rfl) ⟨3131405, by rfl⟩ : syracuseStep 4175207 = 6262811) B6262811
theorem B18838939 : Blo 1855629 18838939 := bstep (se 1 (by rfl) ⟨14129204, by rfl⟩ : syracuseStep 18838939 = 28258409) B28258409
theorem B4765321 : Blo 1855629 4765321 := bstep (se 2 (by rfl) ⟨1786995, by rfl⟩ : syracuseStep 4765321 = 3573991) B3573991
theorem B15857801 : Blo 1855629 15857801 := bstep (se 2 (by rfl) ⟨5946675, by rfl⟩ : syracuseStep 15857801 = 11893351) B11893351
theorem B2939047 : Blo 1855629 2939047 := bstep (se 1 (by rfl) ⟨2204285, by rfl⟩ : syracuseStep 2939047 = 4408571) B4408571
theorem B2783483 : Blo 1855629 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B10721555 : Blo 1855629 10721555 := bstep (se 1 (by rfl) ⟨8041166, by rfl⟩ : syracuseStep 10721555 = 16082333) B16082333
theorem B2349415 : Blo 1855629 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B33053053 : Blo 1855629 33053053 := bstep (se 3 (by rfl) ⟨6197447, by rfl⟩ : syracuseStep 33053053 = 12394895) B12394895
theorem B4176377 : Blo 1855629 4176377 := bstep (se 2 (by rfl) ⟨1566141, by rfl⟩ : syracuseStep 4176377 = 3132283) B3132283
theorem B4176431 : Blo 1855629 4176431 := bstep (se 1 (by rfl) ⟨3132323, by rfl⟩ : syracuseStep 4176431 = 6264647) B6264647
theorem B2783951 : Blo 1855629 2783951 := bstep (se 1 (by rfl) ⟨2087963, by rfl⟩ : syracuseStep 2783951 = 4175927) B4175927
theorem B2783999 : Blo 1855629 2783999 := bstep (se 1 (by rfl) ⟨2087999, by rfl⟩ : syracuseStep 2783999 = 4175999) B4175999
theorem B2784191 : Blo 1855629 2784191 := bstep (se 1 (by rfl) ⟨2088143, by rfl⟩ : syracuseStep 2784191 = 4176287) B4176287
theorem B6691913 : Blo 1855629 6691913 := bstep (se 2 (by rfl) ⟨2509467, by rfl⟩ : syracuseStep 6691913 = 5018935) B5018935
theorem B2350559 : Blo 1855629 2350559 := bstep (se 1 (by rfl) ⟨1762919, by rfl⟩ : syracuseStep 2350559 = 3525839) B3525839
theorem B11894273 : Blo 1855629 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B2784815 : Blo 1855629 2784815 := bstep (se 1 (by rfl) ⟨2088611, by rfl⟩ : syracuseStep 2784815 = 4177223) B4177223
theorem B30096947 : Blo 1855629 30096947 := bstep (se 1 (by rfl) ⟨22572710, by rfl⟩ : syracuseStep 30096947 = 45145421) B45145421
theorem B9404099 : Blo 1855629 9404099 := bstep (se 1 (by rfl) ⟨7053074, by rfl⟩ : syracuseStep 9404099 = 14106149) B14106149
theorem B35700587 : Blo 1855629 35700587 := bstep (se 1 (by rfl) ⟨26775440, by rfl⟩ : syracuseStep 35700587 = 53550881) B53550881
theorem B2785343 : Blo 1855629 2785343 := bstep (se 1 (by rfl) ⟨2089007, by rfl⟩ : syracuseStep 2785343 = 4178015) B4178015
theorem B2785577 : Blo 1855629 2785577 := bstep (se 2 (by rfl) ⟨1044591, by rfl⟩ : syracuseStep 2785577 = 2089183) B2089183
theorem B4178231 : Blo 1855629 4178231 := bstep (se 1 (by rfl) ⟨3133673, by rfl⟩ : syracuseStep 4178231 = 6267347) B6267347
theorem B2785607 : Blo 1855629 2785607 := bstep (se 1 (by rfl) ⟨2089205, by rfl⟩ : syracuseStep 2785607 = 4178411) B4178411
theorem B3522953 : Blo 1855629 3522953 := bstep (se 2 (by rfl) ⟨1321107, by rfl⟩ : syracuseStep 3522953 = 2642215) B2642215
theorem B2089723 : Blo 1855629 2089723 := bstep (se 1 (by rfl) ⟨1567292, by rfl⟩ : syracuseStep 2089723 = 3134585) B3134585
theorem B2786207 : Blo 1855629 2786207 := bstep (se 1 (by rfl) ⟨2089655, by rfl⟩ : syracuseStep 2786207 = 4179311) B4179311
theorem B11895761 : Blo 1855629 11895761 := bstep (se 2 (by rfl) ⟨4460910, by rfl⟩ : syracuseStep 11895761 = 8921821) B8921821
theorem B6268157 : Blo 1855629 6268157 := bstep (se 3 (by rfl) ⟨1175279, by rfl⟩ : syracuseStep 6268157 = 2350559) B2350559
theorem B6350177 : Blo 1855629 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B7046909 : Blo 1855629 7046909 := bstep (se 3 (by rfl) ⟨1321295, by rfl⟩ : syracuseStep 7046909 = 2642591) B2642591
theorem B25118585 : Blo 1855629 25118585 := bstep (se 2 (by rfl) ⟨9419469, by rfl⟩ : syracuseStep 25118585 = 18838939) B18838939
theorem B15468563 : Blo 1855629 15468563 := bstep (se 1 (by rfl) ⟨11601422, by rfl⟩ : syracuseStep 15468563 = 23202845) B23202845
theorem B4524095 : Blo 1855629 4524095 := bstep (se 1 (by rfl) ⟨3393071, by rfl⟩ : syracuseStep 4524095 = 6786143) B6786143
theorem B20064631 : Blo 1855629 20064631 := bstep (se 1 (by rfl) ⟨15048473, by rfl⟩ : syracuseStep 20064631 = 30096947) B30096947
theorem B6269399 : Blo 1855629 6269399 := bstep (se 1 (by rfl) ⟨4702049, by rfl⟩ : syracuseStep 6269399 = 9404099) B9404099
theorem B23800391 : Blo 1855629 23800391 := bstep (se 1 (by rfl) ⟨17850293, by rfl⟩ : syracuseStep 23800391 = 35700587) B35700587
theorem B3132155 : Blo 1855629 3132155 := bstep (se 1 (by rfl) ⟨2349116, by rfl⟩ : syracuseStep 3132155 = 4698233) B4698233
theorem B15862553 : Blo 1855629 15862553 := bstep (se 2 (by rfl) ⟨5948457, by rfl⟩ : syracuseStep 15862553 = 11896915) B11896915
theorem B5286845 : Blo 1855629 5286845 := bstep (se 3 (by rfl) ⟨991283, by rfl⟩ : syracuseStep 5286845 = 1982567) B1982567
theorem B3132553 : Blo 1855629 3132553 := bstep (se 2 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 3132553 = 2349415) B2349415
theorem B3132607 : Blo 1855629 3132607 := bstep (se 1 (by rfl) ⟨2349455, by rfl⟩ : syracuseStep 3132607 = 4698911) B4698911
theorem B25415045 : Blo 1855629 25415045 := bstep (se 4 (by rfl) ⟨2382660, by rfl⟩ : syracuseStep 25415045 = 4765321) B4765321
theorem B26775031 : Blo 1855629 26775031 := bstep (se 1 (by rfl) ⟨20081273, by rfl⟩ : syracuseStep 26775031 = 40162547) B40162547
theorem B15674917 : Blo 1855629 15674917 := bstep (se 4 (by rfl) ⟨1469523, by rfl⟩ : syracuseStep 15674917 = 2939047) B2939047
theorem B13381519 : Blo 1855629 13381519 := bstep (se 1 (by rfl) ⟨10036139, by rfl⟩ : syracuseStep 13381519 = 20072279) B20072279
theorem B4698071 : Blo 1855629 4698071 := bstep (se 1 (by rfl) ⟨3523553, by rfl⟩ : syracuseStep 4698071 = 7047107) B7047107
theorem B10571867 : Blo 1855629 10571867 := bstep (se 1 (by rfl) ⟨7928900, by rfl⟩ : syracuseStep 10571867 = 15857801) B15857801
theorem B1855655 : Blo 1855629 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B7147703 : Blo 1855629 7147703 := bstep (se 1 (by rfl) ⟨5360777, by rfl⟩ : syracuseStep 7147703 = 10721555) B10721555
theorem B107114885 : Blo 1855629 107114885 := bstep (se 4 (by rfl) ⟨10042020, by rfl⟩ : syracuseStep 107114885 = 20084041) B20084041
theorem B1855967 : Blo 1855629 1855967 := bstep (se 1 (by rfl) ⟨1391975, by rfl⟩ : syracuseStep 1855967 = 2783951) B2783951
theorem B1855999 : Blo 1855629 1855999 := bstep (se 1 (by rfl) ⟨1391999, by rfl⟩ : syracuseStep 1855999 = 2783999) B2783999
theorem B9400859 : Blo 1855629 9400859 := bstep (se 1 (by rfl) ⟨7050644, by rfl⟩ : syracuseStep 9400859 = 14101289) B14101289
theorem B1856127 : Blo 1855629 1856127 := bstep (se 1 (by rfl) ⟨1392095, by rfl⟩ : syracuseStep 1856127 = 2784191) B2784191
theorem B10039945 : Blo 1855629 10039945 := bstep (se 2 (by rfl) ⟨3764979, by rfl⟩ : syracuseStep 10039945 = 7529959) B7529959
theorem B60232409 : Blo 1855629 60232409 := bstep (se 2 (by rfl) ⟨22587153, by rfl⟩ : syracuseStep 60232409 = 45174307) B45174307
theorem B4461275 : Blo 1855629 4461275 := bstep (se 1 (by rfl) ⟨3345956, by rfl⟩ : syracuseStep 4461275 = 6691913) B6691913
theorem B1856543 : Blo 1855629 1856543 := bstep (se 1 (by rfl) ⟨1392407, by rfl⟩ : syracuseStep 1856543 = 2784815) B2784815
theorem B101586149 : Blo 1855629 101586149 := bstep (se 4 (by rfl) ⟨9523701, by rfl⟩ : syracuseStep 101586149 = 19047403) B19047403
theorem B6690185 : Blo 1855629 6690185 := bstep (se 2 (by rfl) ⟨2508819, by rfl⟩ : syracuseStep 6690185 = 5017639) B5017639
theorem B5019131 : Blo 1855629 5019131 := bstep (se 1 (by rfl) ⟨3764348, by rfl⟩ : syracuseStep 5019131 = 7528697) B7528697
theorem B42874393 : Blo 1855629 42874393 := bstep (se 2 (by rfl) ⟨16077897, by rfl⟩ : syracuseStep 42874393 = 32155795) B32155795
theorem B14095943 : Blo 1855629 14095943 := bstep (se 1 (by rfl) ⟨10571957, by rfl⟩ : syracuseStep 14095943 = 21143915) B21143915
theorem B44070737 : Blo 1855629 44070737 := bstep (se 2 (by rfl) ⟨16526526, by rfl⟩ : syracuseStep 44070737 = 33053053) B33053053
theorem B2783471 : Blo 1855629 2783471 := bstep (se 1 (by rfl) ⟨2087603, by rfl⟩ : syracuseStep 2783471 = 4175207) B4175207
theorem B2644607 : Blo 1855629 2644607 := bstep (se 1 (by rfl) ⟨1983455, by rfl⟩ : syracuseStep 2644607 = 3966911) B3966911
theorem B2972543 : Blo 1855629 2972543 := bstep (se 1 (by rfl) ⟨2229407, by rfl⟩ : syracuseStep 2972543 = 4458815) B4458815
theorem B13384577 : Blo 1855629 13384577 := bstep (se 2 (by rfl) ⟨5019216, by rfl⟩ : syracuseStep 13384577 = 10038433) B10038433
theorem B2784251 : Blo 1855629 2784251 := bstep (se 1 (by rfl) ⟨2088188, by rfl⟩ : syracuseStep 2784251 = 4176377) B4176377
theorem B2784287 : Blo 1855629 2784287 := bstep (se 1 (by rfl) ⟨2088215, by rfl⟩ : syracuseStep 2784287 = 4176431) B4176431
theorem B2350235 : Blo 1855629 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B2088175 : Blo 1855629 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B6266159 : Blo 1855629 6266159 := bstep (se 1 (by rfl) ⟨4699619, by rfl⟩ : syracuseStep 6266159 = 9399239) B9399239
theorem B14097887 : Blo 1855629 14097887 := bstep (se 1 (by rfl) ⟨10573415, by rfl⟩ : syracuseStep 14097887 = 21146831) B21146831
theorem B4177529 : Blo 1855629 4177529 := bstep (se 2 (by rfl) ⟨1566573, by rfl⟩ : syracuseStep 4177529 = 3133147) B3133147
theorem B7929515 : Blo 1855629 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B15867575 : Blo 1855629 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B4702121 : Blo 1855629 4702121 := bstep (se 2 (by rfl) ⟨1763295, by rfl⟩ : syracuseStep 4702121 = 3526591) B3526591
theorem B2785487 : Blo 1855629 2785487 := bstep (se 1 (by rfl) ⟨2089115, by rfl⟩ : syracuseStep 2785487 = 4178231) B4178231
theorem B71409923 : Blo 1855629 71409923 := bstep (se 1 (by rfl) ⟨53557442, by rfl⟩ : syracuseStep 71409923 = 107114885) B107114885
theorem B6267239 : Blo 1855629 6267239 := bstep (se 1 (by rfl) ⟨4700429, by rfl⟩ : syracuseStep 6267239 = 9400859) B9400859
theorem B6267293 : Blo 1855629 6267293 := bstep (se 3 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 6267293 = 2350235) B2350235
theorem B7930507 : Blo 1855629 7930507 := bstep (se 1 (by rfl) ⟨5947880, by rfl⟩ : syracuseStep 7930507 = 11895761) B11895761
theorem B67724099 : Blo 1855629 67724099 := bstep (se 1 (by rfl) ⟨50793074, by rfl⟩ : syracuseStep 67724099 = 101586149) B101586149
theorem B4178771 : Blo 1855629 4178771 := bstep (se 1 (by rfl) ⟨3134078, by rfl⟩ : syracuseStep 4178771 = 6268157) B6268157
theorem B13386593 : Blo 1855629 13386593 := bstep (se 2 (by rfl) ⟨5019972, by rfl⟩ : syracuseStep 13386593 = 10039945) B10039945
theorem B16933805 : Blo 1855629 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B2786297 : Blo 1855629 2786297 := bstep (se 2 (by rfl) ⟨1044861, by rfl⟩ : syracuseStep 2786297 = 2089723) B2089723
theorem B9397295 : Blo 1855629 9397295 := bstep (se 1 (by rfl) ⟨7047971, by rfl⟩ : syracuseStep 9397295 = 14095943) B14095943
theorem B16745723 : Blo 1855629 16745723 := bstep (se 1 (by rfl) ⟨12559292, by rfl⟩ : syracuseStep 16745723 = 25118585) B25118585
theorem B3016063 : Blo 1855629 3016063 := bstep (se 1 (by rfl) ⟨2262047, by rfl⟩ : syracuseStep 3016063 = 4524095) B4524095
theorem B4179599 : Blo 1855629 4179599 := bstep (se 1 (by rfl) ⟨3134699, by rfl⟩ : syracuseStep 4179599 = 6269399) B6269399
theorem B21145373 : Blo 1855629 21145373 := bstep (se 3 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 21145373 = 7929515) B7929515
theorem B11896733 : Blo 1855629 11896733 := bstep (se 3 (by rfl) ⟨2230637, by rfl⟩ : syracuseStep 11896733 = 4461275) B4461275
theorem B8923051 : Blo 1855629 8923051 := bstep (se 1 (by rfl) ⟨6692288, by rfl⟩ : syracuseStep 8923051 = 13384577) B13384577
theorem B3524563 : Blo 1855629 3524563 := bstep (se 1 (by rfl) ⟨2643422, by rfl⟩ : syracuseStep 3524563 = 5286845) B5286845
theorem B57165857 : Blo 1855629 57165857 := bstep (se 2 (by rfl) ⟨21437196, by rfl⟩ : syracuseStep 57165857 = 42874393) B42874393
theorem B20899889 : Blo 1855629 20899889 := bstep (se 2 (by rfl) ⟨7837458, by rfl⟩ : syracuseStep 20899889 = 15674917) B15674917
theorem B16943363 : Blo 1855629 16943363 := bstep (se 1 (by rfl) ⟨12707522, by rfl⟩ : syracuseStep 16943363 = 25415045) B25415045
theorem B9398591 : Blo 1855629 9398591 := bstep (se 1 (by rfl) ⟨7048943, by rfl⟩ : syracuseStep 9398591 = 14097887) B14097887
theorem B10578383 : Blo 1855629 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B3132047 : Blo 1855629 3132047 := bstep (se 1 (by rfl) ⟨2349035, by rfl⟩ : syracuseStep 3132047 = 4698071) B4698071
theorem B7047911 : Blo 1855629 7047911 := bstep (se 1 (by rfl) ⟨5285933, by rfl⟩ : syracuseStep 7047911 = 10571867) B10571867
theorem B4460123 : Blo 1855629 4460123 := bstep (se 1 (by rfl) ⟨3345092, by rfl⟩ : syracuseStep 4460123 = 6690185) B6690185
theorem B4697939 : Blo 1855629 4697939 := bstep (se 1 (by rfl) ⟨3523454, by rfl⟩ : syracuseStep 4697939 = 7046909) B7046909
theorem B31707125 : Blo 1855629 31707125 := bstep (se 5 (by rfl) ⟨1486271, by rfl⟩ : syracuseStep 31707125 = 2972543) B2972543
theorem B1855647 : Blo 1855629 1855647 := bstep (se 1 (by rfl) ⟨1391735, by rfl⟩ : syracuseStep 1855647 = 2783471) B2783471
theorem B1856167 : Blo 1855629 1856167 := bstep (se 1 (by rfl) ⟨1392125, by rfl⟩ : syracuseStep 1856167 = 2784251) B2784251
theorem B1856191 : Blo 1855629 1856191 := bstep (se 1 (by rfl) ⟨1392143, by rfl⟩ : syracuseStep 1856191 = 2784287) B2784287
theorem B3134747 : Blo 1855629 3134747 := bstep (se 1 (by rfl) ⟨2351060, by rfl⟩ : syracuseStep 3134747 = 4702121) B4702121
theorem B1856895 : Blo 1855629 1856895 := bstep (se 1 (by rfl) ⟨1392671, by rfl⟩ : syracuseStep 1856895 = 2785343) B2785343
theorem B1857051 : Blo 1855629 1857051 := bstep (se 1 (by rfl) ⟨1392788, by rfl⟩ : syracuseStep 1857051 = 2785577) B2785577
theorem B1857071 : Blo 1855629 1857071 := bstep (se 1 (by rfl) ⟨1392803, by rfl⟩ : syracuseStep 1857071 = 2785607) B2785607
theorem B40154939 : Blo 1855629 40154939 := bstep (se 1 (by rfl) ⟨30116204, by rfl⟩ : syracuseStep 40154939 = 60232409) B60232409
theorem B19060541 : Blo 1855629 19060541 := bstep (se 3 (by rfl) ⟨3573851, by rfl⟩ : syracuseStep 19060541 = 7147703) B7147703
theorem B26752841 : Blo 1855629 26752841 := bstep (se 2 (by rfl) ⟨10032315, by rfl⟩ : syracuseStep 26752841 = 20064631) B20064631
theorem B1857471 : Blo 1855629 1857471 := bstep (se 1 (by rfl) ⟨1393103, by rfl⟩ : syracuseStep 1857471 = 2786207) B2786207
theorem B9394541 : Blo 1855629 9394541 := bstep (se 3 (by rfl) ⟨1761476, by rfl⟩ : syracuseStep 9394541 = 3522953) B3522953
theorem B13384349 : Blo 1855629 13384349 := bstep (se 3 (by rfl) ⟨2509565, by rfl⟩ : syracuseStep 13384349 = 5019131) B5019131
theorem B10312375 : Blo 1855629 10312375 := bstep (se 1 (by rfl) ⟨7734281, by rfl⟩ : syracuseStep 10312375 = 15468563) B15468563
theorem B4176737 : Blo 1855629 4176737 := bstep (se 2 (by rfl) ⟨1566276, by rfl⟩ : syracuseStep 4176737 = 3132553) B3132553
theorem B4176809 : Blo 1855629 4176809 := bstep (se 2 (by rfl) ⟨1566303, by rfl⟩ : syracuseStep 4176809 = 3132607) B3132607
theorem B2784233 : Blo 1855629 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B7052285 : Blo 1855629 7052285 := bstep (se 3 (by rfl) ⟨1322303, by rfl⟩ : syracuseStep 7052285 = 2644607) B2644607
theorem B15866927 : Blo 1855629 15866927 := bstep (se 1 (by rfl) ⟨11900195, by rfl⟩ : syracuseStep 15866927 = 23800391) B23800391
theorem B2088103 : Blo 1855629 2088103 := bstep (se 1 (by rfl) ⟨1566077, by rfl⟩ : syracuseStep 2088103 = 3132155) B3132155
theorem B10575035 : Blo 1855629 10575035 := bstep (se 1 (by rfl) ⟨7931276, by rfl⟩ : syracuseStep 10575035 = 15862553) B15862553
theorem B35700041 : Blo 1855629 35700041 := bstep (se 2 (by rfl) ⟨13387515, by rfl⟩ : syracuseStep 35700041 = 26775031) B26775031
theorem B4177439 : Blo 1855629 4177439 := bstep (se 1 (by rfl) ⟨3133079, by rfl⟩ : syracuseStep 4177439 = 6266159) B6266159
theorem B117521965 : Blo 1855629 117521965 := bstep (se 3 (by rfl) ⟨22035368, by rfl⟩ : syracuseStep 117521965 = 44070737) B44070737
theorem B2785019 : Blo 1855629 2785019 := bstep (se 1 (by rfl) ⟨2088764, by rfl⟩ : syracuseStep 2785019 = 4177529) B4177529
theorem B17842025 : Blo 1855629 17842025 := bstep (se 2 (by rfl) ⟨6690759, by rfl⟩ : syracuseStep 17842025 = 13381519) B13381519
theorem B4178159 : Blo 1855629 4178159 := bstep (se 1 (by rfl) ⟨3133619, by rfl⟩ : syracuseStep 4178159 = 6267239) B6267239
theorem B4178195 : Blo 1855629 4178195 := bstep (se 1 (by rfl) ⟨3133646, by rfl⟩ : syracuseStep 4178195 = 6267293) B6267293
theorem B2785847 : Blo 1855629 2785847 := bstep (se 1 (by rfl) ⟨2089385, by rfl⟩ : syracuseStep 2785847 = 4178771) B4178771
theorem B11289203 : Blo 1855629 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B2089831 : Blo 1855629 2089831 := bstep (se 1 (by rfl) ⟨1567373, by rfl⟩ : syracuseStep 2089831 = 3134747) B3134747
theorem B2786399 : Blo 1855629 2786399 := bstep (se 1 (by rfl) ⟨2089799, by rfl⟩ : syracuseStep 2786399 = 4179599) B4179599
theorem B12707027 : Blo 1855629 12707027 := bstep (se 1 (by rfl) ⟨9530270, by rfl⟩ : syracuseStep 12707027 = 19060541) B19060541
theorem B17835227 : Blo 1855629 17835227 := bstep (se 1 (by rfl) ⟨13376420, by rfl⟩ : syracuseStep 17835227 = 26752841) B26752841
theorem B38110571 : Blo 1855629 38110571 := bstep (se 1 (by rfl) ⟨28582928, by rfl⟩ : syracuseStep 38110571 = 57165857) B57165857
theorem B8922899 : Blo 1855629 8922899 := bstep (se 1 (by rfl) ⟨6692174, by rfl⟩ : syracuseStep 8922899 = 13384349) B13384349
theorem B10577951 : Blo 1855629 10577951 := bstep (se 1 (by rfl) ⟨7933463, by rfl⟩ : syracuseStep 10577951 = 15866927) B15866927
theorem B23800027 : Blo 1855629 23800027 := bstep (se 1 (by rfl) ⟨17850020, by rfl⟩ : syracuseStep 23800027 = 35700041) B35700041
theorem B3131959 : Blo 1855629 3131959 := bstep (se 1 (by rfl) ⟨2348969, by rfl⟩ : syracuseStep 3131959 = 4697939) B4697939
theorem B11897401 : Blo 1855629 11897401 := bstep (se 2 (by rfl) ⟨4461525, by rfl⟩ : syracuseStep 11897401 = 8923051) B8923051
theorem B21138083 : Blo 1855629 21138083 := bstep (se 1 (by rfl) ⟨15853562, by rfl⟩ : syracuseStep 21138083 = 31707125) B31707125
theorem B47606615 : Blo 1855629 47606615 := bstep (se 1 (by rfl) ⟨35704961, by rfl⟩ : syracuseStep 47606615 = 71409923) B71409923
theorem B45149399 : Blo 1855629 45149399 := bstep (se 1 (by rfl) ⟨33862049, by rfl⟩ : syracuseStep 45149399 = 67724099) B67724099
theorem B13749833 : Blo 1855629 13749833 := bstep (se 2 (by rfl) ⟨5156187, by rfl⟩ : syracuseStep 13749833 = 10312375) B10312375
theorem B6263027 : Blo 1855629 6263027 := bstep (se 1 (by rfl) ⟨4697270, by rfl⟩ : syracuseStep 6263027 = 9394541) B9394541
theorem B4698607 : Blo 1855629 4698607 := bstep (se 1 (by rfl) ⟨3523955, by rfl⟩ : syracuseStep 4698607 = 7047911) B7047911
theorem B1856155 : Blo 1855629 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B7050023 : Blo 1855629 7050023 := bstep (se 1 (by rfl) ⟨5287517, by rfl⟩ : syracuseStep 7050023 = 10575035) B10575035
theorem B35697581 : Blo 1855629 35697581 := bstep (se 3 (by rfl) ⟨6693296, by rfl⟩ : syracuseStep 35697581 = 13386593) B13386593
theorem B31724621 : Blo 1855629 31724621 := bstep (se 3 (by rfl) ⟨5948366, by rfl⟩ : syracuseStep 31724621 = 11896733) B11896733
theorem B1856679 : Blo 1855629 1856679 := bstep (se 1 (by rfl) ⟨1392509, by rfl⟩ : syracuseStep 1856679 = 2785019) B2785019
theorem B4699417 : Blo 1855629 4699417 := bstep (se 2 (by rfl) ⟨1762281, by rfl⟩ : syracuseStep 4699417 = 3524563) B3524563
theorem B1856991 : Blo 1855629 1856991 := bstep (se 1 (by rfl) ⟨1392743, by rfl⟩ : syracuseStep 1856991 = 2785487) B2785487
theorem B1857531 : Blo 1855629 1857531 := bstep (se 1 (by rfl) ⟨1393148, by rfl⟩ : syracuseStep 1857531 = 2786297) B2786297
theorem B6264863 : Blo 1855629 6264863 := bstep (se 1 (by rfl) ⟨4698647, by rfl⟩ : syracuseStep 6264863 = 9397295) B9397295
theorem B11163815 : Blo 1855629 11163815 := bstep (se 1 (by rfl) ⟨8372861, by rfl⟩ : syracuseStep 11163815 = 16745723) B16745723
theorem B10574009 : Blo 1855629 10574009 := bstep (se 2 (by rfl) ⟨3965253, by rfl⟩ : syracuseStep 10574009 = 7930507) B7930507
theorem B14096915 : Blo 1855629 14096915 := bstep (se 1 (by rfl) ⟨10572686, by rfl⟩ : syracuseStep 14096915 = 21145373) B21145373
theorem B26769959 : Blo 1855629 26769959 := bstep (se 1 (by rfl) ⟨20077469, by rfl⟩ : syracuseStep 26769959 = 40154939) B40154939
theorem B13933259 : Blo 1855629 13933259 := bstep (se 1 (by rfl) ⟨10449944, by rfl⟩ : syracuseStep 13933259 = 20899889) B20899889
theorem B11295575 : Blo 1855629 11295575 := bstep (se 1 (by rfl) ⟨8471681, by rfl⟩ : syracuseStep 11295575 = 16943363) B16943363
theorem B6265727 : Blo 1855629 6265727 := bstep (se 1 (by rfl) ⟨4699295, by rfl⟩ : syracuseStep 6265727 = 9398591) B9398591
theorem B2784137 : Blo 1855629 2784137 := bstep (se 2 (by rfl) ⟨1044051, by rfl⟩ : syracuseStep 2784137 = 2088103) B2088103
theorem B7052255 : Blo 1855629 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B2088031 : Blo 1855629 2088031 := bstep (se 1 (by rfl) ⟨1566023, by rfl⟩ : syracuseStep 2088031 = 3132047) B3132047
theorem B4021417 : Blo 1855629 4021417 := bstep (se 2 (by rfl) ⟨1508031, by rfl⟩ : syracuseStep 4021417 = 3016063) B3016063
theorem B2784491 : Blo 1855629 2784491 := bstep (se 1 (by rfl) ⟨2088368, by rfl⟩ : syracuseStep 2784491 = 4176737) B4176737
theorem B2784539 : Blo 1855629 2784539 := bstep (se 1 (by rfl) ⟨2088404, by rfl⟩ : syracuseStep 2784539 = 4176809) B4176809
theorem B4701523 : Blo 1855629 4701523 := bstep (se 1 (by rfl) ⟨3526142, by rfl⟩ : syracuseStep 4701523 = 7052285) B7052285
theorem B156695953 : Blo 1855629 156695953 := bstep (se 2 (by rfl) ⟨58760982, by rfl⟩ : syracuseStep 156695953 = 117521965) B117521965
theorem B2784959 : Blo 1855629 2784959 := bstep (se 1 (by rfl) ⟨2088719, by rfl⟩ : syracuseStep 2784959 = 4177439) B4177439
theorem B2973415 : Blo 1855629 2973415 := bstep (se 1 (by rfl) ⟨2230061, by rfl⟩ : syracuseStep 2973415 = 4460123) B4460123
theorem B11894683 : Blo 1855629 11894683 := bstep (se 1 (by rfl) ⟨8921012, by rfl⟩ : syracuseStep 11894683 = 17842025) B17842025
theorem B2785439 : Blo 1855629 2785439 := bstep (se 1 (by rfl) ⟨2089079, by rfl⟩ : syracuseStep 2785439 = 4178159) B4178159
theorem B2785463 : Blo 1855629 2785463 := bstep (se 1 (by rfl) ⟨2089097, by rfl⟩ : syracuseStep 2785463 = 4178195) B4178195
theorem B23798387 : Blo 1855629 23798387 := bstep (se 1 (by rfl) ⟨17848790, by rfl⟩ : syracuseStep 23798387 = 35697581) B35697581
theorem B8471351 : Blo 1855629 8471351 := bstep (se 1 (by rfl) ⟨6353513, by rfl⟩ : syracuseStep 8471351 = 12707027) B12707027
theorem B2786441 : Blo 1855629 2786441 := bstep (se 2 (by rfl) ⟨1044915, by rfl⟩ : syracuseStep 2786441 = 2089831) B2089831
theorem B5948599 : Blo 1855629 5948599 := bstep (se 1 (by rfl) ⟨4461449, by rfl⟩ : syracuseStep 5948599 = 8922899) B8922899
theorem B9397943 : Blo 1855629 9397943 := bstep (se 1 (by rfl) ⟨7048457, by rfl⟩ : syracuseStep 9397943 = 14096915) B14096915
theorem B14092055 : Blo 1855629 14092055 := bstep (se 1 (by rfl) ⟨10569041, by rfl⟩ : syracuseStep 14092055 = 21138083) B21138083
theorem B6268697 : Blo 1855629 6268697 := bstep (se 2 (by rfl) ⟨2350761, by rfl⟩ : syracuseStep 6268697 = 4701523) B4701523
theorem B7530383 : Blo 1855629 7530383 := bstep (se 1 (by rfl) ⟨5647787, by rfl⟩ : syracuseStep 7530383 = 11295575) B11295575
theorem B31737743 : Blo 1855629 31737743 := bstep (se 1 (by rfl) ⟨23803307, by rfl⟩ : syracuseStep 31737743 = 47606615) B47606615
theorem B30099599 : Blo 1855629 30099599 := bstep (se 1 (by rfl) ⟨22574699, by rfl⟩ : syracuseStep 30099599 = 45149399) B45149399
theorem B15863201 : Blo 1855629 15863201 := bstep (se 2 (by rfl) ⟨5948700, by rfl⟩ : syracuseStep 15863201 = 11897401) B11897401
theorem B11890151 : Blo 1855629 11890151 := bstep (se 1 (by rfl) ⟨8917613, by rfl⟩ : syracuseStep 11890151 = 17835227) B17835227
theorem B25407047 : Blo 1855629 25407047 := bstep (se 1 (by rfl) ⟨19055285, by rfl⟩ : syracuseStep 25407047 = 38110571) B38110571
theorem B7442543 : Blo 1855629 7442543 := bstep (se 1 (by rfl) ⟨5581907, by rfl⟩ : syracuseStep 7442543 = 11163815) B11163815
theorem B7049339 : Blo 1855629 7049339 := bstep (se 1 (by rfl) ⟨5287004, by rfl⟩ : syracuseStep 7049339 = 10574009) B10574009
theorem B5361889 : Blo 1855629 5361889 := bstep (se 2 (by rfl) ⟨2010708, by rfl⟩ : syracuseStep 5361889 = 4021417) B4021417
theorem B17846639 : Blo 1855629 17846639 := bstep (se 1 (by rfl) ⟨13384979, by rfl⟩ : syracuseStep 17846639 = 26769959) B26769959
theorem B1856091 : Blo 1855629 1856091 := bstep (se 1 (by rfl) ⟨1392068, by rfl⟩ : syracuseStep 1856091 = 2784137) B2784137
theorem B1856327 : Blo 1855629 1856327 := bstep (se 1 (by rfl) ⟨1392245, by rfl⟩ : syracuseStep 1856327 = 2784491) B2784491
theorem B1856359 : Blo 1855629 1856359 := bstep (se 1 (by rfl) ⟨1392269, by rfl⟩ : syracuseStep 1856359 = 2784539) B2784539
theorem B1856639 : Blo 1855629 1856639 := bstep (se 1 (by rfl) ⟨1392479, by rfl⟩ : syracuseStep 1856639 = 2784959) B2784959
theorem B4175351 : Blo 1855629 4175351 := bstep (se 1 (by rfl) ⟨3131513, by rfl⟩ : syracuseStep 4175351 = 6263027) B6263027
theorem B31733369 : Blo 1855629 31733369 := bstep (se 2 (by rfl) ⟨11900013, by rfl⟩ : syracuseStep 31733369 = 23800027) B23800027
theorem B1857231 : Blo 1855629 1857231 := bstep (se 1 (by rfl) ⟨1392923, by rfl⟩ : syracuseStep 1857231 = 2785847) B2785847
theorem B7526135 : Blo 1855629 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B4700015 : Blo 1855629 4700015 := bstep (se 1 (by rfl) ⟨3525011, by rfl⟩ : syracuseStep 4700015 = 7050023) B7050023
theorem B6264809 : Blo 1855629 6264809 := bstep (se 2 (by rfl) ⟨2349303, by rfl⟩ : syracuseStep 6264809 = 4698607) B4698607
theorem B21149747 : Blo 1855629 21149747 := bstep (se 1 (by rfl) ⟨15862310, by rfl⟩ : syracuseStep 21149747 = 31724621) B31724621
theorem B1857599 : Blo 1855629 1857599 := bstep (se 1 (by rfl) ⟨1393199, by rfl⟩ : syracuseStep 1857599 = 2786399) B2786399
theorem B4175945 : Blo 1855629 4175945 := bstep (se 2 (by rfl) ⟨1565979, by rfl⟩ : syracuseStep 4175945 = 3131959) B3131959
theorem B4176575 : Blo 1855629 4176575 := bstep (se 1 (by rfl) ⟨3132431, by rfl⟩ : syracuseStep 4176575 = 6264863) B6264863
theorem B7051967 : Blo 1855629 7051967 := bstep (se 1 (by rfl) ⟨5288975, by rfl⟩ : syracuseStep 7051967 = 10577951) B10577951
theorem B2784041 : Blo 1855629 2784041 := bstep (se 2 (by rfl) ⟨1044015, by rfl⟩ : syracuseStep 2784041 = 2088031) B2088031
theorem B6265889 : Blo 1855629 6265889 := bstep (se 2 (by rfl) ⟨2349708, by rfl⟩ : syracuseStep 6265889 = 4699417) B4699417
theorem B9288839 : Blo 1855629 9288839 := bstep (se 1 (by rfl) ⟨6966629, by rfl⟩ : syracuseStep 9288839 = 13933259) B13933259
theorem B208927937 : Blo 1855629 208927937 := bstep (se 2 (by rfl) ⟨78347976, by rfl⟩ : syracuseStep 208927937 = 156695953) B156695953
theorem B4177151 : Blo 1855629 4177151 := bstep (se 1 (by rfl) ⟨3132863, by rfl⟩ : syracuseStep 4177151 = 6265727) B6265727
theorem B4701503 : Blo 1855629 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B3964553 : Blo 1855629 3964553 := bstep (se 2 (by rfl) ⟨1486707, by rfl⟩ : syracuseStep 3964553 = 2973415) B2973415
theorem B9166555 : Blo 1855629 9166555 := bstep (se 1 (by rfl) ⟨6874916, by rfl⟩ : syracuseStep 9166555 = 13749833) B13749833
theorem B15859577 : Blo 1855629 15859577 := bstep (se 2 (by rfl) ⟨5947341, by rfl⟩ : syracuseStep 15859577 = 11894683) B11894683
theorem B4179131 : Blo 1855629 4179131 := bstep (se 1 (by rfl) ⟨3134348, by rfl⟩ : syracuseStep 4179131 = 6268697) B6268697
theorem B14099831 : Blo 1855629 14099831 := bstep (se 1 (by rfl) ⟨10574873, by rfl⟩ : syracuseStep 14099831 = 21149747) B21149747
theorem B7931465 : Blo 1855629 7931465 := bstep (se 2 (by rfl) ⟨2974299, by rfl⟩ : syracuseStep 7931465 = 5948599) B5948599
theorem B11897759 : Blo 1855629 11897759 := bstep (se 1 (by rfl) ⟨8923319, by rfl⟩ : syracuseStep 11897759 = 17846639) B17846639
theorem B5647567 : Blo 1855629 5647567 := bstep (se 1 (by rfl) ⟨4235675, by rfl⟩ : syracuseStep 5647567 = 8471351) B8471351
theorem B21155579 : Blo 1855629 21155579 := bstep (se 1 (by rfl) ⟨15866684, by rfl⟩ : syracuseStep 21155579 = 31733369) B31733369
theorem B5017423 : Blo 1855629 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B3133343 : Blo 1855629 3133343 := bstep (se 1 (by rfl) ⟨2350007, by rfl⟩ : syracuseStep 3133343 = 4700015) B4700015
theorem B20066399 : Blo 1855629 20066399 := bstep (se 1 (by rfl) ⟨15049799, by rfl⟩ : syracuseStep 20066399 = 30099599) B30099599
theorem B1856027 : Blo 1855629 1856027 := bstep (se 1 (by rfl) ⟨1392020, by rfl⟩ : syracuseStep 1856027 = 2784041) B2784041
theorem B139285291 : Blo 1855629 139285291 := bstep (se 1 (by rfl) ⟨104463968, by rfl⟩ : syracuseStep 139285291 = 208927937) B208927937
theorem B3134335 : Blo 1855629 3134335 := bstep (se 1 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 3134335 = 4701503) B4701503
theorem B7926767 : Blo 1855629 7926767 := bstep (se 1 (by rfl) ⟨5945075, by rfl⟩ : syracuseStep 7926767 = 11890151) B11890151
theorem B16938031 : Blo 1855629 16938031 := bstep (se 1 (by rfl) ⟨12703523, by rfl⟩ : syracuseStep 16938031 = 25407047) B25407047
theorem B2643035 : Blo 1855629 2643035 := bstep (se 1 (by rfl) ⟨1982276, by rfl⟩ : syracuseStep 2643035 = 3964553) B3964553
theorem B10573051 : Blo 1855629 10573051 := bstep (se 1 (by rfl) ⟨7929788, by rfl⟩ : syracuseStep 10573051 = 15859577) B15859577
theorem B4961695 : Blo 1855629 4961695 := bstep (se 1 (by rfl) ⟨3721271, by rfl⟩ : syracuseStep 4961695 = 7442543) B7442543
theorem B4699559 : Blo 1855629 4699559 := bstep (se 1 (by rfl) ⟨3524669, by rfl⟩ : syracuseStep 4699559 = 7049339) B7049339
theorem B1856959 : Blo 1855629 1856959 := bstep (se 1 (by rfl) ⟨1392719, by rfl⟩ : syracuseStep 1856959 = 2785439) B2785439
theorem B1856975 : Blo 1855629 1856975 := bstep (se 1 (by rfl) ⟨1392731, by rfl⟩ : syracuseStep 1856975 = 2785463) B2785463
theorem B7149185 : Blo 1855629 7149185 := bstep (se 2 (by rfl) ⟨2680944, by rfl⟩ : syracuseStep 7149185 = 5361889) B5361889
theorem B15865591 : Blo 1855629 15865591 := bstep (se 1 (by rfl) ⟨11899193, by rfl⟩ : syracuseStep 15865591 = 23798387) B23798387
theorem B1857627 : Blo 1855629 1857627 := bstep (se 1 (by rfl) ⟨1393220, by rfl⟩ : syracuseStep 1857627 = 2786441) B2786441
theorem B2783567 : Blo 1855629 2783567 := bstep (se 1 (by rfl) ⟨2087675, by rfl⟩ : syracuseStep 2783567 = 4175351) B4175351
theorem B6265295 : Blo 1855629 6265295 := bstep (se 1 (by rfl) ⟨4698971, by rfl⟩ : syracuseStep 6265295 = 9397943) B9397943
theorem B9394703 : Blo 1855629 9394703 := bstep (se 1 (by rfl) ⟨7046027, by rfl⟩ : syracuseStep 9394703 = 14092055) B14092055
theorem B5020255 : Blo 1855629 5020255 := bstep (se 1 (by rfl) ⟨3765191, by rfl⟩ : syracuseStep 5020255 = 7530383) B7530383
theorem B21158495 : Blo 1855629 21158495 := bstep (se 1 (by rfl) ⟨15868871, by rfl⟩ : syracuseStep 21158495 = 31737743) B31737743
theorem B4176539 : Blo 1855629 4176539 := bstep (se 1 (by rfl) ⟨3132404, by rfl⟩ : syracuseStep 4176539 = 6264809) B6264809
theorem B2783963 : Blo 1855629 2783963 := bstep (se 1 (by rfl) ⟨2087972, by rfl⟩ : syracuseStep 2783963 = 4175945) B4175945
theorem B2784383 : Blo 1855629 2784383 := bstep (se 1 (by rfl) ⟨2088287, by rfl⟩ : syracuseStep 2784383 = 4176575) B4176575
theorem B4701311 : Blo 1855629 4701311 := bstep (se 1 (by rfl) ⟨3525983, by rfl⟩ : syracuseStep 4701311 = 7051967) B7051967
theorem B4177259 : Blo 1855629 4177259 := bstep (se 1 (by rfl) ⟨3132944, by rfl⟩ : syracuseStep 4177259 = 6265889) B6265889
theorem B6192559 : Blo 1855629 6192559 := bstep (se 1 (by rfl) ⟨4644419, by rfl⟩ : syracuseStep 6192559 = 9288839) B9288839
theorem B2784767 : Blo 1855629 2784767 := bstep (se 1 (by rfl) ⟨2088575, by rfl⟩ : syracuseStep 2784767 = 4177151) B4177151
theorem B10575467 : Blo 1855629 10575467 := bstep (se 1 (by rfl) ⟨7931600, by rfl⟩ : syracuseStep 10575467 = 15863201) B15863201
theorem B12222073 : Blo 1855629 12222073 := bstep (se 2 (by rfl) ⟨4583277, by rfl⟩ : syracuseStep 12222073 = 9166555) B9166555
theorem B13377599 : Blo 1855629 13377599 := bstep (se 1 (by rfl) ⟨10033199, by rfl⟩ : syracuseStep 13377599 = 20066399) B20066399
theorem B65184389 : Blo 1855629 65184389 := bstep (se 4 (by rfl) ⟨6111036, by rfl⟩ : syracuseStep 65184389 = 12222073) B12222073
theorem B5284511 : Blo 1855629 5284511 := bstep (se 1 (by rfl) ⟨3963383, by rfl⟩ : syracuseStep 5284511 = 7926767) B7926767
theorem B2786087 : Blo 1855629 2786087 := bstep (se 1 (by rfl) ⟨2089565, by rfl⟩ : syracuseStep 2786087 = 4179131) B4179131
theorem B6693673 : Blo 1855629 6693673 := bstep (se 2 (by rfl) ⟨2510127, by rfl⟩ : syracuseStep 6693673 = 5020255) B5020255
theorem B185713721 : Blo 1855629 185713721 := bstep (se 2 (by rfl) ⟨69642645, by rfl⟩ : syracuseStep 185713721 = 139285291) B139285291
theorem B4179113 : Blo 1855629 4179113 := bstep (se 2 (by rfl) ⟨1567167, by rfl⟩ : syracuseStep 4179113 = 3134335) B3134335
theorem B7530089 : Blo 1855629 7530089 := bstep (se 2 (by rfl) ⟨2823783, by rfl⟩ : syracuseStep 7530089 = 5647567) B5647567
theorem B7931839 : Blo 1855629 7931839 := bstep (se 1 (by rfl) ⟨5948879, by rfl⟩ : syracuseStep 7931839 = 11897759) B11897759
theorem B21154121 : Blo 1855629 21154121 := bstep (se 2 (by rfl) ⟨7932795, by rfl⟩ : syracuseStep 21154121 = 15865591) B15865591
theorem B7048093 : Blo 1855629 7048093 := bstep (se 3 (by rfl) ⟨1321517, by rfl⟩ : syracuseStep 7048093 = 2643035) B2643035
theorem B9399887 : Blo 1855629 9399887 := bstep (se 1 (by rfl) ⟨7049915, by rfl⟩ : syracuseStep 9399887 = 14099831) B14099831
theorem B3133039 : Blo 1855629 3133039 := bstep (se 1 (by rfl) ⟨2349779, by rfl⟩ : syracuseStep 3133039 = 4699559) B4699559
theorem B5287643 : Blo 1855629 5287643 := bstep (se 1 (by rfl) ⟨3965732, by rfl⟩ : syracuseStep 5287643 = 7931465) B7931465
theorem B1855711 : Blo 1855629 1855711 := bstep (se 1 (by rfl) ⟨1391783, by rfl⟩ : syracuseStep 1855711 = 2783567) B2783567
theorem B6263135 : Blo 1855629 6263135 := bstep (se 1 (by rfl) ⟨4697351, by rfl⟩ : syracuseStep 6263135 = 9394703) B9394703
theorem B1855975 : Blo 1855629 1855975 := bstep (se 1 (by rfl) ⟨1391981, by rfl⟩ : syracuseStep 1855975 = 2783963) B2783963
theorem B6615593 : Blo 1855629 6615593 := bstep (se 2 (by rfl) ⟨2480847, by rfl⟩ : syracuseStep 6615593 = 4961695) B4961695
theorem B1856255 : Blo 1855629 1856255 := bstep (se 1 (by rfl) ⟨1392191, by rfl⟩ : syracuseStep 1856255 = 2784383) B2784383
theorem B3134207 : Blo 1855629 3134207 := bstep (se 1 (by rfl) ⟨2350655, by rfl⟩ : syracuseStep 3134207 = 4701311) B4701311
theorem B1856511 : Blo 1855629 1856511 := bstep (se 1 (by rfl) ⟨1392383, by rfl⟩ : syracuseStep 1856511 = 2784767) B2784767
theorem B7050311 : Blo 1855629 7050311 := bstep (se 1 (by rfl) ⟨5287733, by rfl⟩ : syracuseStep 7050311 = 10575467) B10575467
theorem B6689897 : Blo 1855629 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B14103719 : Blo 1855629 14103719 := bstep (se 1 (by rfl) ⟨10577789, by rfl⟩ : syracuseStep 14103719 = 21155579) B21155579
theorem B4766123 : Blo 1855629 4766123 := bstep (se 1 (by rfl) ⟨3574592, by rfl⟩ : syracuseStep 4766123 = 7149185) B7149185
theorem B22584041 : Blo 1855629 22584041 := bstep (se 2 (by rfl) ⟨8469015, by rfl⟩ : syracuseStep 22584041 = 16938031) B16938031
theorem B4176863 : Blo 1855629 4176863 := bstep (se 1 (by rfl) ⟨3132647, by rfl⟩ : syracuseStep 4176863 = 6265295) B6265295
theorem B14097401 : Blo 1855629 14097401 := bstep (se 2 (by rfl) ⟨5286525, by rfl⟩ : syracuseStep 14097401 = 10573051) B10573051
theorem B14105663 : Blo 1855629 14105663 := bstep (se 1 (by rfl) ⟨10579247, by rfl⟩ : syracuseStep 14105663 = 21158495) B21158495
theorem B2784359 : Blo 1855629 2784359 := bstep (se 1 (by rfl) ⟨2088269, by rfl⟩ : syracuseStep 2784359 = 4176539) B4176539
theorem B8256745 : Blo 1855629 8256745 := bstep (se 2 (by rfl) ⟨3096279, by rfl⟩ : syracuseStep 8256745 = 6192559) B6192559
theorem B2784839 : Blo 1855629 2784839 := bstep (se 1 (by rfl) ⟨2088629, by rfl⟩ : syracuseStep 2784839 = 4177259) B4177259
theorem B2088895 : Blo 1855629 2088895 := bstep (se 1 (by rfl) ⟨1566671, by rfl⟩ : syracuseStep 2088895 = 3133343) B3133343
theorem B3523007 : Blo 1855629 3523007 := bstep (se 1 (by rfl) ⟨2642255, by rfl⟩ : syracuseStep 3523007 = 5284511) B5284511
theorem B2089471 : Blo 1855629 2089471 := bstep (se 1 (by rfl) ⟨1567103, by rfl⟩ : syracuseStep 2089471 = 3134207) B3134207
theorem B2786075 : Blo 1855629 2786075 := bstep (se 1 (by rfl) ⟨2089556, by rfl⟩ : syracuseStep 2786075 = 4179113) B4179113
theorem B9397457 : Blo 1855629 9397457 := bstep (se 2 (by rfl) ⟨3524046, by rfl⟩ : syracuseStep 9397457 = 7048093) B7048093
theorem B20080237 : Blo 1855629 20080237 := bstep (se 3 (by rfl) ⟨3765044, by rfl⟩ : syracuseStep 20080237 = 7530089) B7530089
theorem B9398267 : Blo 1855629 9398267 := bstep (se 1 (by rfl) ⟨7048700, by rfl⟩ : syracuseStep 9398267 = 14097401) B14097401
theorem B3525095 : Blo 1855629 3525095 := bstep (se 1 (by rfl) ⟨2643821, by rfl⟩ : syracuseStep 3525095 = 5287643) B5287643
theorem B4410395 : Blo 1855629 4410395 := bstep (se 1 (by rfl) ⟨3307796, by rfl⟩ : syracuseStep 4410395 = 6615593) B6615593
theorem B123809147 : Blo 1855629 123809147 := bstep (se 1 (by rfl) ⟨92856860, by rfl⟩ : syracuseStep 123809147 = 185713721) B185713721
theorem B4459931 : Blo 1855629 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B8924897 : Blo 1855629 8924897 := bstep (se 2 (by rfl) ⟨3346836, by rfl⟩ : syracuseStep 8924897 = 6693673) B6693673
theorem B14102747 : Blo 1855629 14102747 := bstep (se 1 (by rfl) ⟨10577060, by rfl⟩ : syracuseStep 14102747 = 21154121) B21154121
theorem B1856239 : Blo 1855629 1856239 := bstep (se 1 (by rfl) ⟨1392179, by rfl⟩ : syracuseStep 1856239 = 2784359) B2784359
theorem B1856559 : Blo 1855629 1856559 := bstep (se 1 (by rfl) ⟨1392419, by rfl⟩ : syracuseStep 1856559 = 2784839) B2784839
theorem B8918399 : Blo 1855629 8918399 := bstep (se 1 (by rfl) ⟨6688799, by rfl⟩ : syracuseStep 8918399 = 13377599) B13377599
theorem B4175423 : Blo 1855629 4175423 := bstep (se 1 (by rfl) ⟨3131567, by rfl⟩ : syracuseStep 4175423 = 6263135) B6263135
theorem B43456259 : Blo 1855629 43456259 := bstep (se 1 (by rfl) ⟨32592194, by rfl⟩ : syracuseStep 43456259 = 65184389) B65184389
theorem B1857391 : Blo 1855629 1857391 := bstep (se 1 (by rfl) ⟨1393043, by rfl⟩ : syracuseStep 1857391 = 2786087) B2786087
theorem B4700207 : Blo 1855629 4700207 := bstep (se 1 (by rfl) ⟨3525155, by rfl⟩ : syracuseStep 4700207 = 7050311) B7050311
theorem B9402479 : Blo 1855629 9402479 := bstep (se 1 (by rfl) ⟨7051859, by rfl⟩ : syracuseStep 9402479 = 14103719) B14103719
theorem B3177415 : Blo 1855629 3177415 := bstep (se 1 (by rfl) ⟨2383061, by rfl⟩ : syracuseStep 3177415 = 4766123) B4766123
theorem B11008993 : Blo 1855629 11008993 := bstep (se 2 (by rfl) ⟨4128372, by rfl⟩ : syracuseStep 11008993 = 8256745) B8256745
theorem B15056027 : Blo 1855629 15056027 := bstep (se 1 (by rfl) ⟨11292020, by rfl⟩ : syracuseStep 15056027 = 22584041) B22584041
theorem B2784575 : Blo 1855629 2784575 := bstep (se 1 (by rfl) ⟨2088431, by rfl⟩ : syracuseStep 2784575 = 4176863) B4176863
theorem B9403775 : Blo 1855629 9403775 := bstep (se 1 (by rfl) ⟨7052831, by rfl⟩ : syracuseStep 9403775 = 14105663) B14105663
theorem B4177385 : Blo 1855629 4177385 := bstep (se 2 (by rfl) ⟨1566519, by rfl⟩ : syracuseStep 4177385 = 3133039) B3133039
theorem B6266591 : Blo 1855629 6266591 := bstep (se 1 (by rfl) ⟨4699943, by rfl⟩ : syracuseStep 6266591 = 9399887) B9399887
theorem B2785193 : Blo 1855629 2785193 := bstep (se 2 (by rfl) ⟨1044447, by rfl⟩ : syracuseStep 2785193 = 2088895) B2088895
theorem B10575785 : Blo 1855629 10575785 := bstep (se 2 (by rfl) ⟨3965919, by rfl⟩ : syracuseStep 10575785 = 7931839) B7931839
theorem B2785961 : Blo 1855629 2785961 := bstep (se 2 (by rfl) ⟨1044735, by rfl⟩ : syracuseStep 2785961 = 2089471) B2089471
theorem B4236553 : Blo 1855629 4236553 := bstep (se 2 (by rfl) ⟨1588707, by rfl⟩ : syracuseStep 4236553 = 3177415) B3177415
theorem B6268319 : Blo 1855629 6268319 := bstep (se 1 (by rfl) ⟨4701239, by rfl⟩ : syracuseStep 6268319 = 9402479) B9402479
theorem B10037351 : Blo 1855629 10037351 := bstep (se 1 (by rfl) ⟨7528013, by rfl⟩ : syracuseStep 10037351 = 15056027) B15056027
theorem B26773649 : Blo 1855629 26773649 := bstep (se 2 (by rfl) ⟨10040118, by rfl⟩ : syracuseStep 26773649 = 20080237) B20080237
theorem B6269183 : Blo 1855629 6269183 := bstep (se 1 (by rfl) ⟨4701887, by rfl⟩ : syracuseStep 6269183 = 9403775) B9403775
theorem B5949931 : Blo 1855629 5949931 := bstep (se 1 (by rfl) ⟨4462448, by rfl⟩ : syracuseStep 5949931 = 8924897) B8924897
theorem B28970839 : Blo 1855629 28970839 := bstep (se 1 (by rfl) ⟨21728129, by rfl⟩ : syracuseStep 28970839 = 43456259) B43456259
theorem B3133471 : Blo 1855629 3133471 := bstep (se 1 (by rfl) ⟨2350103, by rfl⟩ : syracuseStep 3133471 = 4700207) B4700207
theorem B1856383 : Blo 1855629 1856383 := bstep (se 1 (by rfl) ⟨1392287, by rfl⟩ : syracuseStep 1856383 = 2784575) B2784575
theorem B82539431 : Blo 1855629 82539431 := bstep (se 1 (by rfl) ⟨61904573, by rfl⟩ : syracuseStep 82539431 = 123809147) B123809147
theorem B1856795 : Blo 1855629 1856795 := bstep (se 1 (by rfl) ⟨1392596, by rfl⟩ : syracuseStep 1856795 = 2785193) B2785193
theorem B7050523 : Blo 1855629 7050523 := bstep (se 1 (by rfl) ⟨5287892, by rfl⟩ : syracuseStep 7050523 = 10575785) B10575785
theorem B9401831 : Blo 1855629 9401831 := bstep (se 1 (by rfl) ⟨7051373, by rfl⟩ : syracuseStep 9401831 = 14102747) B14102747
theorem B2348671 : Blo 1855629 2348671 := bstep (se 1 (by rfl) ⟨1761503, by rfl⟩ : syracuseStep 2348671 = 3523007) B3523007
theorem B1857383 : Blo 1855629 1857383 := bstep (se 1 (by rfl) ⟨1393037, by rfl⟩ : syracuseStep 1857383 = 2786075) B2786075
theorem B6264971 : Blo 1855629 6264971 := bstep (se 1 (by rfl) ⟨4698728, by rfl⟩ : syracuseStep 6264971 = 9397457) B9397457
theorem B5945599 : Blo 1855629 5945599 := bstep (se 1 (by rfl) ⟨4459199, by rfl⟩ : syracuseStep 5945599 = 8918399) B8918399
theorem B2783615 : Blo 1855629 2783615 := bstep (se 1 (by rfl) ⟨2087711, by rfl⟩ : syracuseStep 2783615 = 4175423) B4175423
theorem B14678657 : Blo 1855629 14678657 := bstep (se 2 (by rfl) ⟨5504496, by rfl⟩ : syracuseStep 14678657 = 11008993) B11008993
theorem B6265511 : Blo 1855629 6265511 := bstep (se 1 (by rfl) ⟨4699133, by rfl⟩ : syracuseStep 6265511 = 9398267) B9398267
theorem B2350063 : Blo 1855629 2350063 := bstep (se 1 (by rfl) ⟨1762547, by rfl⟩ : syracuseStep 2350063 = 3525095) B3525095
theorem B2940263 : Blo 1855629 2940263 := bstep (se 1 (by rfl) ⟨2205197, by rfl⟩ : syracuseStep 2940263 = 4410395) B4410395
theorem B2973287 : Blo 1855629 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B2784923 : Blo 1855629 2784923 := bstep (se 1 (by rfl) ⟨2088692, by rfl⟩ : syracuseStep 2784923 = 4177385) B4177385
theorem B4177727 : Blo 1855629 4177727 := bstep (se 1 (by rfl) ⟨3133295, by rfl⟩ : syracuseStep 4177727 = 6266591) B6266591
theorem B4177961 : Blo 1855629 4177961 := bstep (se 2 (by rfl) ⟨1566735, by rfl⟩ : syracuseStep 4177961 = 3133471) B3133471
theorem B55026287 : Blo 1855629 55026287 := bstep (se 1 (by rfl) ⟨41269715, by rfl⟩ : syracuseStep 55026287 = 82539431) B82539431
theorem B4178879 : Blo 1855629 4178879 := bstep (se 1 (by rfl) ⟨3134159, by rfl⟩ : syracuseStep 4178879 = 6268319) B6268319
theorem B6267887 : Blo 1855629 6267887 := bstep (se 1 (by rfl) ⟨4700915, by rfl⟩ : syracuseStep 6267887 = 9401831) B9401831
theorem B4179455 : Blo 1855629 4179455 := bstep (se 1 (by rfl) ⟨3134591, by rfl⟩ : syracuseStep 4179455 = 6269183) B6269183
theorem B3131561 : Blo 1855629 3131561 := bstep (se 2 (by rfl) ⟨1174335, by rfl⟩ : syracuseStep 3131561 = 2348671) B2348671
theorem B38627785 : Blo 1855629 38627785 := bstep (se 2 (by rfl) ⟨14485419, by rfl⟩ : syracuseStep 38627785 = 28970839) B28970839
theorem B7933241 : Blo 1855629 7933241 := bstep (se 2 (by rfl) ⟨2974965, by rfl⟩ : syracuseStep 7933241 = 5949931) B5949931
theorem B31362805 : Blo 1855629 31362805 := bstep (se 5 (by rfl) ⟨1470131, by rfl⟩ : syracuseStep 31362805 = 2940263) B2940263
theorem B3133417 : Blo 1855629 3133417 := bstep (se 2 (by rfl) ⟨1175031, by rfl⟩ : syracuseStep 3133417 = 2350063) B2350063
theorem B1855743 : Blo 1855629 1855743 := bstep (se 1 (by rfl) ⟨1391807, by rfl⟩ : syracuseStep 1855743 = 2783615) B2783615
theorem B5648737 : Blo 1855629 5648737 := bstep (se 2 (by rfl) ⟨2118276, by rfl⟩ : syracuseStep 5648737 = 4236553) B4236553
theorem B9400697 : Blo 1855629 9400697 := bstep (se 2 (by rfl) ⟨3525261, by rfl⟩ : syracuseStep 9400697 = 7050523) B7050523
theorem B9785771 : Blo 1855629 9785771 := bstep (se 1 (by rfl) ⟨7339328, by rfl⟩ : syracuseStep 9785771 = 14678657) B14678657
theorem B1856615 : Blo 1855629 1856615 := bstep (se 1 (by rfl) ⟨1392461, by rfl⟩ : syracuseStep 1856615 = 2784923) B2784923
theorem B7927465 : Blo 1855629 7927465 := bstep (se 2 (by rfl) ⟨2972799, by rfl⟩ : syracuseStep 7927465 = 5945599) B5945599
theorem B1857307 : Blo 1855629 1857307 := bstep (se 1 (by rfl) ⟨1392980, by rfl⟩ : syracuseStep 1857307 = 2785961) B2785961
theorem B6691567 : Blo 1855629 6691567 := bstep (se 1 (by rfl) ⟨5018675, by rfl⟩ : syracuseStep 6691567 = 10037351) B10037351
theorem B4176647 : Blo 1855629 4176647 := bstep (se 1 (by rfl) ⟨3132485, by rfl⟩ : syracuseStep 4176647 = 6264971) B6264971
theorem B17849099 : Blo 1855629 17849099 := bstep (se 1 (by rfl) ⟨13386824, by rfl⟩ : syracuseStep 17849099 = 26773649) B26773649
theorem B7928765 : Blo 1855629 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B4177007 : Blo 1855629 4177007 := bstep (se 1 (by rfl) ⟨3132755, by rfl⟩ : syracuseStep 4177007 = 6265511) B6265511
theorem B2785151 : Blo 1855629 2785151 := bstep (se 1 (by rfl) ⟨2088863, by rfl⟩ : syracuseStep 2785151 = 4177727) B4177727
theorem B2785307 : Blo 1855629 2785307 := bstep (se 1 (by rfl) ⟨2088980, by rfl⟩ : syracuseStep 2785307 = 4177961) B4177961
theorem B6267131 : Blo 1855629 6267131 := bstep (se 1 (by rfl) ⟨4700348, by rfl⟩ : syracuseStep 6267131 = 9400697) B9400697
theorem B36684191 : Blo 1855629 36684191 := bstep (se 1 (by rfl) ⟨27513143, by rfl⟩ : syracuseStep 36684191 = 55026287) B55026287
theorem B2785919 : Blo 1855629 2785919 := bstep (se 1 (by rfl) ⟨2089439, by rfl⟩ : syracuseStep 2785919 = 4178879) B4178879
theorem B4178591 : Blo 1855629 4178591 := bstep (se 1 (by rfl) ⟨3133943, by rfl⟩ : syracuseStep 4178591 = 6267887) B6267887
theorem B8922089 : Blo 1855629 8922089 := bstep (se 2 (by rfl) ⟨3345783, by rfl⟩ : syracuseStep 8922089 = 6691567) B6691567
theorem B2786303 : Blo 1855629 2786303 := bstep (se 1 (by rfl) ⟨2089727, by rfl⟩ : syracuseStep 2786303 = 4179455) B4179455
theorem B5285843 : Blo 1855629 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B10569953 : Blo 1855629 10569953 := bstep (se 2 (by rfl) ⟨3963732, by rfl⟩ : syracuseStep 10569953 = 7927465) B7927465
theorem B206014853 : Blo 1855629 206014853 := bstep (se 4 (by rfl) ⟨19313892, by rfl⟩ : syracuseStep 206014853 = 38627785) B38627785
theorem B6523847 : Blo 1855629 6523847 := bstep (se 1 (by rfl) ⟨4892885, by rfl⟩ : syracuseStep 6523847 = 9785771) B9785771
theorem B7531649 : Blo 1855629 7531649 := bstep (se 2 (by rfl) ⟨2824368, by rfl⟩ : syracuseStep 7531649 = 5648737) B5648737
theorem B11899399 : Blo 1855629 11899399 := bstep (se 1 (by rfl) ⟨8924549, by rfl⟩ : syracuseStep 11899399 = 17849099) B17849099
theorem B5288827 : Blo 1855629 5288827 := bstep (se 1 (by rfl) ⟨3966620, by rfl⟩ : syracuseStep 5288827 = 7933241) B7933241
theorem B41817073 : Blo 1855629 41817073 := bstep (se 2 (by rfl) ⟨15681402, by rfl⟩ : syracuseStep 41817073 = 31362805) B31362805
theorem B1856767 : Blo 1855629 1856767 := bstep (se 1 (by rfl) ⟨1392575, by rfl⟩ : syracuseStep 1856767 = 2785151) B2785151
theorem B2087707 : Blo 1855629 2087707 := bstep (se 1 (by rfl) ⟨1565780, by rfl⟩ : syracuseStep 2087707 = 3131561) B3131561
theorem B2784431 : Blo 1855629 2784431 := bstep (se 1 (by rfl) ⟨2088323, by rfl⟩ : syracuseStep 2784431 = 4176647) B4176647
theorem B2784671 : Blo 1855629 2784671 := bstep (se 1 (by rfl) ⟨2088503, by rfl⟩ : syracuseStep 2784671 = 4177007) B4177007
theorem B4177889 : Blo 1855629 4177889 := bstep (se 2 (by rfl) ⟨1566708, by rfl⟩ : syracuseStep 4177889 = 3133417) B3133417
theorem B4178087 : Blo 1855629 4178087 := bstep (se 1 (by rfl) ⟨3133565, by rfl⟩ : syracuseStep 4178087 = 6267131) B6267131
theorem B2785727 : Blo 1855629 2785727 := bstep (se 1 (by rfl) ⟨2089295, by rfl⟩ : syracuseStep 2785727 = 4178591) B4178591
theorem B3523895 : Blo 1855629 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B55756097 : Blo 1855629 55756097 := bstep (se 2 (by rfl) ⟨20908536, by rfl⟩ : syracuseStep 55756097 = 41817073) B41817073
theorem B7046635 : Blo 1855629 7046635 := bstep (se 1 (by rfl) ⟨5284976, by rfl⟩ : syracuseStep 7046635 = 10569953) B10569953
theorem B23792237 : Blo 1855629 23792237 := bstep (se 3 (by rfl) ⟨4461044, by rfl⟩ : syracuseStep 23792237 = 8922089) B8922089
theorem B24456127 : Blo 1855629 24456127 := bstep (se 1 (by rfl) ⟨18342095, by rfl⟩ : syracuseStep 24456127 = 36684191) B36684191
theorem B137343235 : Blo 1855629 137343235 := bstep (se 1 (by rfl) ⟨103007426, by rfl⟩ : syracuseStep 137343235 = 206014853) B206014853
theorem B1856287 : Blo 1855629 1856287 := bstep (se 1 (by rfl) ⟨1392215, by rfl⟩ : syracuseStep 1856287 = 2784431) B2784431
theorem B1856447 : Blo 1855629 1856447 := bstep (se 1 (by rfl) ⟨1392335, by rfl⟩ : syracuseStep 1856447 = 2784671) B2784671
theorem B1856871 : Blo 1855629 1856871 := bstep (se 1 (by rfl) ⟨1392653, by rfl⟩ : syracuseStep 1856871 = 2785307) B2785307
theorem B1857279 : Blo 1855629 1857279 := bstep (se 1 (by rfl) ⟨1392959, by rfl⟩ : syracuseStep 1857279 = 2785919) B2785919
theorem B1857535 : Blo 1855629 1857535 := bstep (se 1 (by rfl) ⟨1393151, by rfl⟩ : syracuseStep 1857535 = 2786303) B2786303
theorem B15865865 : Blo 1855629 15865865 := bstep (se 2 (by rfl) ⟨5949699, by rfl⟩ : syracuseStep 15865865 = 11899399) B11899399
theorem B2783609 : Blo 1855629 2783609 := bstep (se 2 (by rfl) ⟨1043853, by rfl⟩ : syracuseStep 2783609 = 2087707) B2087707
theorem B7051769 : Blo 1855629 7051769 := bstep (se 2 (by rfl) ⟨2644413, by rfl⟩ : syracuseStep 7051769 = 5288827) B5288827
theorem B4349231 : Blo 1855629 4349231 := bstep (se 1 (by rfl) ⟨3261923, by rfl⟩ : syracuseStep 4349231 = 6523847) B6523847
theorem B5021099 : Blo 1855629 5021099 := bstep (se 1 (by rfl) ⟨3765824, by rfl⟩ : syracuseStep 5021099 = 7531649) B7531649
theorem B2785259 : Blo 1855629 2785259 := bstep (se 1 (by rfl) ⟨2088944, by rfl⟩ : syracuseStep 2785259 = 4177889) B4177889
theorem B2785391 : Blo 1855629 2785391 := bstep (se 1 (by rfl) ⟨2089043, by rfl⟩ : syracuseStep 2785391 = 4178087) B4178087
theorem B183124313 : Blo 1855629 183124313 := bstep (se 2 (by rfl) ⟨68671617, by rfl⟩ : syracuseStep 183124313 = 137343235) B137343235
theorem B10577243 : Blo 1855629 10577243 := bstep (se 1 (by rfl) ⟨7932932, by rfl⟩ : syracuseStep 10577243 = 15865865) B15865865
theorem B15861491 : Blo 1855629 15861491 := bstep (se 1 (by rfl) ⟨11896118, by rfl⟩ : syracuseStep 15861491 = 23792237) B23792237
theorem B37170731 : Blo 1855629 37170731 := bstep (se 1 (by rfl) ⟨27878048, by rfl⟩ : syracuseStep 37170731 = 55756097) B55756097
theorem B32608169 : Blo 1855629 32608169 := bstep (se 2 (by rfl) ⟨12228063, by rfl⟩ : syracuseStep 32608169 = 24456127) B24456127
theorem B1855739 : Blo 1855629 1855739 := bstep (se 1 (by rfl) ⟨1391804, by rfl⟩ : syracuseStep 1855739 = 2783609) B2783609
theorem B3347399 : Blo 1855629 3347399 := bstep (se 1 (by rfl) ⟨2510549, by rfl⟩ : syracuseStep 3347399 = 5021099) B5021099
theorem B1856839 : Blo 1855629 1856839 := bstep (se 1 (by rfl) ⟨1392629, by rfl⟩ : syracuseStep 1856839 = 2785259) B2785259
theorem B1857151 : Blo 1855629 1857151 := bstep (se 1 (by rfl) ⟨1392863, by rfl⟩ : syracuseStep 1857151 = 2785727) B2785727
theorem B2349263 : Blo 1855629 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B4701179 : Blo 1855629 4701179 := bstep (se 1 (by rfl) ⟨3525884, by rfl⟩ : syracuseStep 4701179 = 7051769) B7051769
theorem B9395513 : Blo 1855629 9395513 := bstep (se 2 (by rfl) ⟨3523317, by rfl⟩ : syracuseStep 9395513 = 7046635) B7046635
theorem B2899487 : Blo 1855629 2899487 := bstep (se 1 (by rfl) ⟨2174615, by rfl⟩ : syracuseStep 2899487 = 4349231) B4349231
theorem B2231599 : Blo 1855629 2231599 := bstep (se 1 (by rfl) ⟨1673699, by rfl⟩ : syracuseStep 2231599 = 3347399) B3347399
theorem B3134119 : Blo 1855629 3134119 := bstep (se 1 (by rfl) ⟨2350589, by rfl⟩ : syracuseStep 3134119 = 4701179) B4701179
theorem B6263675 : Blo 1855629 6263675 := bstep (se 1 (by rfl) ⟨4697756, by rfl⟩ : syracuseStep 6263675 = 9395513) B9395513
theorem B21738779 : Blo 1855629 21738779 := bstep (se 1 (by rfl) ⟨16304084, by rfl⟩ : syracuseStep 21738779 = 32608169) B32608169
theorem B1856927 : Blo 1855629 1856927 := bstep (se 1 (by rfl) ⟨1392695, by rfl⟩ : syracuseStep 1856927 = 2785391) B2785391
theorem B122082875 : Blo 1855629 122082875 := bstep (se 1 (by rfl) ⟨91562156, by rfl⟩ : syracuseStep 122082875 = 183124313) B183124313
theorem B6264701 : Blo 1855629 6264701 := bstep (se 3 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 6264701 = 2349263) B2349263
theorem B7051495 : Blo 1855629 7051495 := bstep (se 1 (by rfl) ⟨5288621, by rfl⟩ : syracuseStep 7051495 = 10577243) B10577243
theorem B10574327 : Blo 1855629 10574327 := bstep (se 1 (by rfl) ⟨7930745, by rfl⟩ : syracuseStep 10574327 = 15861491) B15861491
theorem B1932991 : Blo 1855629 1932991 := bstep (se 1 (by rfl) ⟨1449743, by rfl⟩ : syracuseStep 1932991 = 2899487) B2899487
theorem B24780487 : Blo 1855629 24780487 := bstep (se 1 (by rfl) ⟨18585365, by rfl⟩ : syracuseStep 24780487 = 37170731) B37170731
theorem B14492519 : Blo 1855629 14492519 := bstep (se 1 (by rfl) ⟨10869389, by rfl⟩ : syracuseStep 14492519 = 21738779) B21738779
theorem B4178825 : Blo 1855629 4178825 := bstep (se 2 (by rfl) ⟨1567059, by rfl⟩ : syracuseStep 4178825 = 3134119) B3134119
theorem B81388583 : Blo 1855629 81388583 := bstep (se 1 (by rfl) ⟨61041437, by rfl⟩ : syracuseStep 81388583 = 122082875) B122082875
theorem B2975465 : Blo 1855629 2975465 := bstep (se 2 (by rfl) ⟨1115799, by rfl⟩ : syracuseStep 2975465 = 2231599) B2231599
theorem B33040649 : Blo 1855629 33040649 := bstep (se 2 (by rfl) ⟨12390243, by rfl⟩ : syracuseStep 33040649 = 24780487) B24780487
theorem B10309285 : Blo 1855629 10309285 := bstep (se 4 (by rfl) ⟨966495, by rfl⟩ : syracuseStep 10309285 = 1932991) B1932991
theorem B7049551 : Blo 1855629 7049551 := bstep (se 1 (by rfl) ⟨5287163, by rfl⟩ : syracuseStep 7049551 = 10574327) B10574327
theorem B9401993 : Blo 1855629 9401993 := bstep (se 2 (by rfl) ⟨3525747, by rfl⟩ : syracuseStep 9401993 = 7051495) B7051495
theorem B4175783 : Blo 1855629 4175783 := bstep (se 1 (by rfl) ⟨3131837, by rfl⟩ : syracuseStep 4175783 = 6263675) B6263675
theorem B4176467 : Blo 1855629 4176467 := bstep (se 1 (by rfl) ⟨3132350, by rfl⟩ : syracuseStep 4176467 = 6264701) B6264701
theorem B2785883 : Blo 1855629 2785883 := bstep (se 1 (by rfl) ⟨2089412, by rfl⟩ : syracuseStep 2785883 = 4178825) B4178825
theorem B6267995 : Blo 1855629 6267995 := bstep (se 1 (by rfl) ⟨4700996, by rfl⟩ : syracuseStep 6267995 = 9401993) B9401993
theorem B9399401 : Blo 1855629 9399401 := bstep (se 2 (by rfl) ⟨3524775, by rfl⟩ : syracuseStep 9399401 = 7049551) B7049551
theorem B9661679 : Blo 1855629 9661679 := bstep (se 1 (by rfl) ⟨7246259, by rfl⟩ : syracuseStep 9661679 = 14492519) B14492519
theorem B54259055 : Blo 1855629 54259055 := bstep (se 1 (by rfl) ⟨40694291, by rfl⟩ : syracuseStep 54259055 = 81388583) B81388583
theorem B7934573 : Blo 1855629 7934573 := bstep (se 3 (by rfl) ⟨1487732, by rfl⟩ : syracuseStep 7934573 = 2975465) B2975465
theorem B2783855 : Blo 1855629 2783855 := bstep (se 1 (by rfl) ⟨2087891, by rfl⟩ : syracuseStep 2783855 = 4175783) B4175783
theorem B22027099 : Blo 1855629 22027099 := bstep (se 1 (by rfl) ⟨16520324, by rfl⟩ : syracuseStep 22027099 = 33040649) B33040649
theorem B2784311 : Blo 1855629 2784311 := bstep (se 1 (by rfl) ⟨2088233, by rfl⟩ : syracuseStep 2784311 = 4176467) B4176467
theorem B13745713 : Blo 1855629 13745713 := bstep (se 2 (by rfl) ⟨5154642, by rfl⟩ : syracuseStep 13745713 = 10309285) B10309285
theorem B4178663 : Blo 1855629 4178663 := bstep (se 1 (by rfl) ⟨3133997, by rfl⟩ : syracuseStep 4178663 = 6267995) B6267995
theorem B29369465 : Blo 1855629 29369465 := bstep (se 2 (by rfl) ⟨11013549, by rfl⟩ : syracuseStep 29369465 = 22027099) B22027099
theorem B18327617 : Blo 1855629 18327617 := bstep (se 2 (by rfl) ⟨6872856, by rfl⟩ : syracuseStep 18327617 = 13745713) B13745713
theorem B6441119 : Blo 1855629 6441119 := bstep (se 1 (by rfl) ⟨4830839, by rfl⟩ : syracuseStep 6441119 = 9661679) B9661679
theorem B1855903 : Blo 1855629 1855903 := bstep (se 1 (by rfl) ⟨1391927, by rfl⟩ : syracuseStep 1855903 = 2783855) B2783855
theorem B1856207 : Blo 1855629 1856207 := bstep (se 1 (by rfl) ⟨1392155, by rfl⟩ : syracuseStep 1856207 = 2784311) B2784311
theorem B36172703 : Blo 1855629 36172703 := bstep (se 1 (by rfl) ⟨27129527, by rfl⟩ : syracuseStep 36172703 = 54259055) B54259055
theorem B1857255 : Blo 1855629 1857255 := bstep (se 1 (by rfl) ⟨1392941, by rfl⟩ : syracuseStep 1857255 = 2785883) B2785883
theorem B5289715 : Blo 1855629 5289715 := bstep (se 1 (by rfl) ⟨3967286, by rfl⟩ : syracuseStep 5289715 = 7934573) B7934573
theorem B6266267 : Blo 1855629 6266267 := bstep (se 1 (by rfl) ⟨4699700, by rfl⟩ : syracuseStep 6266267 = 9399401) B9399401
theorem B2785775 : Blo 1855629 2785775 := bstep (se 1 (by rfl) ⟨2089331, by rfl⟩ : syracuseStep 2785775 = 4178663) B4178663
theorem B19579643 : Blo 1855629 19579643 := bstep (se 1 (by rfl) ⟨14684732, by rfl⟩ : syracuseStep 19579643 = 29369465) B29369465
theorem B4294079 : Blo 1855629 4294079 := bstep (se 1 (by rfl) ⟨3220559, by rfl⟩ : syracuseStep 4294079 = 6441119) B6441119
theorem B12218411 : Blo 1855629 12218411 := bstep (se 1 (by rfl) ⟨9163808, by rfl⟩ : syracuseStep 12218411 = 18327617) B18327617
theorem B4177511 : Blo 1855629 4177511 := bstep (se 1 (by rfl) ⟨3133133, by rfl⟩ : syracuseStep 4177511 = 6266267) B6266267
theorem B7052953 : Blo 1855629 7052953 := bstep (se 2 (by rfl) ⟨2644857, by rfl⟩ : syracuseStep 7052953 = 5289715) B5289715
theorem B96460541 : Blo 1855629 96460541 := bstep (se 3 (by rfl) ⟨18086351, by rfl⟩ : syracuseStep 96460541 = 36172703) B36172703
theorem B8145607 : Blo 1855629 8145607 := bstep (se 1 (by rfl) ⟨6109205, by rfl⟩ : syracuseStep 8145607 = 12218411) B12218411
theorem B13053095 : Blo 1855629 13053095 := bstep (se 1 (by rfl) ⟨9789821, by rfl⟩ : syracuseStep 13053095 = 19579643) B19579643
theorem B2862719 : Blo 1855629 2862719 := bstep (se 1 (by rfl) ⟨2147039, by rfl⟩ : syracuseStep 2862719 = 4294079) B4294079
theorem B1857183 : Blo 1855629 1857183 := bstep (se 1 (by rfl) ⟨1392887, by rfl⟩ : syracuseStep 1857183 = 2785775) B2785775
theorem B9403937 : Blo 1855629 9403937 := bstep (se 2 (by rfl) ⟨3526476, by rfl⟩ : syracuseStep 9403937 = 7052953) B7052953
theorem B2785007 : Blo 1855629 2785007 := bstep (se 1 (by rfl) ⟨2088755, by rfl⟩ : syracuseStep 2785007 = 4177511) B4177511
theorem B64307027 : Blo 1855629 64307027 := bstep (se 1 (by rfl) ⟨48230270, by rfl⟩ : syracuseStep 64307027 = 96460541) B96460541
theorem B8702063 : Blo 1855629 8702063 := bstep (se 1 (by rfl) ⟨6526547, by rfl⟩ : syracuseStep 8702063 = 13053095) B13053095
theorem B6269291 : Blo 1855629 6269291 := bstep (se 1 (by rfl) ⟨4701968, by rfl⟩ : syracuseStep 6269291 = 9403937) B9403937
theorem B42871351 : Blo 1855629 42871351 := bstep (se 1 (by rfl) ⟨32153513, by rfl⟩ : syracuseStep 42871351 = 64307027) B64307027
theorem B1856671 : Blo 1855629 1856671 := bstep (se 1 (by rfl) ⟨1392503, by rfl⟩ : syracuseStep 1856671 = 2785007) B2785007
theorem B10860809 : Blo 1855629 10860809 := bstep (se 2 (by rfl) ⟨4072803, by rfl⟩ : syracuseStep 10860809 = 8145607) B8145607
theorem B1908479 : Blo 1855629 1908479 := bstep (se 1 (by rfl) ⟨1431359, by rfl⟩ : syracuseStep 1908479 = 2862719) B2862719
theorem B5801375 : Blo 1855629 5801375 := bstep (se 1 (by rfl) ⟨4351031, by rfl⟩ : syracuseStep 5801375 = 8702063) B8702063
theorem B4179527 : Blo 1855629 4179527 := bstep (se 1 (by rfl) ⟨3134645, by rfl⟩ : syracuseStep 4179527 = 6269291) B6269291
theorem B5089277 : Blo 1855629 5089277 := bstep (se 3 (by rfl) ⟨954239, by rfl⟩ : syracuseStep 5089277 = 1908479) B1908479
theorem B28962157 : Blo 1855629 28962157 := bstep (se 3 (by rfl) ⟨5430404, by rfl⟩ : syracuseStep 28962157 = 10860809) B10860809
theorem B57161801 : Blo 1855629 57161801 := bstep (se 2 (by rfl) ⟨21435675, by rfl⟩ : syracuseStep 57161801 = 42871351) B42871351
theorem B3867583 : Blo 1855629 3867583 := bstep (se 1 (by rfl) ⟨2900687, by rfl⟩ : syracuseStep 3867583 = 5801375) B5801375
theorem B2786351 : Blo 1855629 2786351 := bstep (se 1 (by rfl) ⟨2089763, by rfl⟩ : syracuseStep 2786351 = 4179527) B4179527
theorem B3392851 : Blo 1855629 3392851 := bstep (se 1 (by rfl) ⟨2544638, by rfl⟩ : syracuseStep 3392851 = 5089277) B5089277
theorem B38107867 : Blo 1855629 38107867 := bstep (se 1 (by rfl) ⟨28580900, by rfl⟩ : syracuseStep 38107867 = 57161801) B57161801
theorem B38616209 : Blo 1855629 38616209 := bstep (se 2 (by rfl) ⟨14481078, by rfl⟩ : syracuseStep 38616209 = 28962157) B28962157
theorem B4523801 : Blo 1855629 4523801 := bstep (se 2 (by rfl) ⟨1696425, by rfl⟩ : syracuseStep 4523801 = 3392851) B3392851
theorem B50810489 : Blo 1855629 50810489 := bstep (se 2 (by rfl) ⟨19053933, by rfl⟩ : syracuseStep 50810489 = 38107867) B38107867
theorem B5156777 : Blo 1855629 5156777 := bstep (se 2 (by rfl) ⟨1933791, by rfl⟩ : syracuseStep 5156777 = 3867583) B3867583
theorem B25744139 : Blo 1855629 25744139 := bstep (se 1 (by rfl) ⟨19308104, by rfl⟩ : syracuseStep 25744139 = 38616209) B38616209
theorem B1857567 : Blo 1855629 1857567 := bstep (se 1 (by rfl) ⟨1393175, by rfl⟩ : syracuseStep 1857567 = 2786351) B2786351
theorem B17162759 : Blo 1855629 17162759 := bstep (se 1 (by rfl) ⟨12872069, by rfl⟩ : syracuseStep 17162759 = 25744139) B25744139
theorem B48253877 : Blo 1855629 48253877 := bstep (se 5 (by rfl) ⟨2261900, by rfl⟩ : syracuseStep 48253877 = 4523801) B4523801
theorem B3437851 : Blo 1855629 3437851 := bstep (se 1 (by rfl) ⟨2578388, by rfl⟩ : syracuseStep 3437851 = 5156777) B5156777
theorem B33873659 : Blo 1855629 33873659 := bstep (se 1 (by rfl) ⟨25405244, by rfl⟩ : syracuseStep 33873659 = 50810489) B50810489
theorem B4583801 : Blo 1855629 4583801 := bstep (se 2 (by rfl) ⟨1718925, by rfl⟩ : syracuseStep 4583801 = 3437851) B3437851
theorem B22582439 : Blo 1855629 22582439 := bstep (se 1 (by rfl) ⟨16936829, by rfl⟩ : syracuseStep 22582439 = 33873659) B33873659
theorem B45767357 : Blo 1855629 45767357 := bstep (se 3 (by rfl) ⟨8581379, by rfl⟩ : syracuseStep 45767357 = 17162759) B17162759
theorem B32169251 : Blo 1855629 32169251 := bstep (se 1 (by rfl) ⟨24126938, by rfl⟩ : syracuseStep 32169251 = 48253877) B48253877
theorem B3055867 : Blo 1855629 3055867 := bstep (se 1 (by rfl) ⟨2291900, by rfl⟩ : syracuseStep 3055867 = 4583801) B4583801
theorem B30511571 : Blo 1855629 30511571 := bstep (se 1 (by rfl) ⟨22883678, by rfl⟩ : syracuseStep 30511571 = 45767357) B45767357
theorem B15054959 : Blo 1855629 15054959 := bstep (se 1 (by rfl) ⟨11291219, by rfl⟩ : syracuseStep 15054959 = 22582439) B22582439
theorem B21446167 : Blo 1855629 21446167 := bstep (se 1 (by rfl) ⟨16084625, by rfl⟩ : syracuseStep 21446167 = 32169251) B32169251
theorem B81364189 : Blo 1855629 81364189 := bstep (se 3 (by rfl) ⟨15255785, by rfl⟩ : syracuseStep 81364189 = 30511571) B30511571
theorem B10036639 : Blo 1855629 10036639 := bstep (se 1 (by rfl) ⟨7527479, by rfl⟩ : syracuseStep 10036639 = 15054959) B15054959
theorem B16297957 : Blo 1855629 16297957 := bstep (se 4 (by rfl) ⟨1527933, by rfl⟩ : syracuseStep 16297957 = 3055867) B3055867
theorem B28594889 : Blo 1855629 28594889 := bstep (se 2 (by rfl) ⟨10723083, by rfl⟩ : syracuseStep 28594889 = 21446167) B21446167
theorem B19063259 : Blo 1855629 19063259 := bstep (se 1 (by rfl) ⟨14297444, by rfl⟩ : syracuseStep 19063259 = 28594889) B28594889
theorem B13382185 : Blo 1855629 13382185 := bstep (se 2 (by rfl) ⟨5018319, by rfl⟩ : syracuseStep 13382185 = 10036639) B10036639
theorem B21730609 : Blo 1855629 21730609 := bstep (se 2 (by rfl) ⟨8148978, by rfl⟩ : syracuseStep 21730609 = 16297957) B16297957
theorem B108485585 : Blo 1855629 108485585 := bstep (se 2 (by rfl) ⟨40682094, by rfl⟩ : syracuseStep 108485585 = 81364189) B81364189
theorem B17842913 : Blo 1855629 17842913 := bstep (se 2 (by rfl) ⟨6691092, by rfl⟩ : syracuseStep 17842913 = 13382185) B13382185
theorem B12708839 : Blo 1855629 12708839 := bstep (se 1 (by rfl) ⟨9531629, by rfl⟩ : syracuseStep 12708839 = 19063259) B19063259
theorem B115896581 : Blo 1855629 115896581 := bstep (se 4 (by rfl) ⟨10865304, by rfl⟩ : syracuseStep 115896581 = 21730609) B21730609
theorem B72323723 : Blo 1855629 72323723 := bstep (se 1 (by rfl) ⟨54242792, by rfl⟩ : syracuseStep 72323723 = 108485585) B108485585
theorem B11895275 : Blo 1855629 11895275 := bstep (se 1 (by rfl) ⟨8921456, by rfl⟩ : syracuseStep 11895275 = 17842913) B17842913
theorem B8472559 : Blo 1855629 8472559 := bstep (se 1 (by rfl) ⟨6354419, by rfl⟩ : syracuseStep 8472559 = 12708839) B12708839
theorem B77264387 : Blo 1855629 77264387 := bstep (se 1 (by rfl) ⟨57948290, by rfl⟩ : syracuseStep 77264387 = 115896581) B115896581
theorem B192863261 : Blo 1855629 192863261 := bstep (se 3 (by rfl) ⟨36161861, by rfl⟩ : syracuseStep 192863261 = 72323723) B72323723
theorem B7930183 : Blo 1855629 7930183 := bstep (se 1 (by rfl) ⟨5947637, by rfl⟩ : syracuseStep 7930183 = 11895275) B11895275
theorem B128575507 : Blo 1855629 128575507 := bstep (se 1 (by rfl) ⟨96431630, by rfl⟩ : syracuseStep 128575507 = 192863261) B192863261
theorem B51509591 : Blo 1855629 51509591 := bstep (se 1 (by rfl) ⟨38632193, by rfl⟩ : syracuseStep 51509591 = 77264387) B77264387
theorem B11296745 : Blo 1855629 11296745 := bstep (se 2 (by rfl) ⟨4236279, by rfl⟩ : syracuseStep 11296745 = 8472559) B8472559
theorem B171434009 : Blo 1855629 171434009 := bstep (se 2 (by rfl) ⟨64287753, by rfl⟩ : syracuseStep 171434009 = 128575507) B128575507
theorem B7531163 : Blo 1855629 7531163 := bstep (se 1 (by rfl) ⟨5648372, by rfl⟩ : syracuseStep 7531163 = 11296745) B11296745
theorem B10573577 : Blo 1855629 10573577 := bstep (se 2 (by rfl) ⟨3965091, by rfl⟩ : syracuseStep 10573577 = 7930183) B7930183
theorem B34339727 : Blo 1855629 34339727 := bstep (se 1 (by rfl) ⟨25754795, by rfl⟩ : syracuseStep 34339727 = 51509591) B51509591
theorem B457157357 : Blo 1855629 457157357 := bstep (se 3 (by rfl) ⟨85717004, by rfl⟩ : syracuseStep 457157357 = 171434009) B171434009
theorem B7049051 : Blo 1855629 7049051 := bstep (se 1 (by rfl) ⟨5286788, by rfl⟩ : syracuseStep 7049051 = 10573577) B10573577
theorem B22893151 : Blo 1855629 22893151 := bstep (se 1 (by rfl) ⟨17169863, by rfl⟩ : syracuseStep 22893151 = 34339727) B34339727
theorem B5020775 : Blo 1855629 5020775 := bstep (se 1 (by rfl) ⟨3765581, by rfl⟩ : syracuseStep 5020775 = 7531163) B7531163
theorem B30524201 : Blo 1855629 30524201 := bstep (se 2 (by rfl) ⟨11446575, by rfl⟩ : syracuseStep 30524201 = 22893151) B22893151
theorem B304771571 : Blo 1855629 304771571 := bstep (se 1 (by rfl) ⟨228578678, by rfl⟩ : syracuseStep 304771571 = 457157357) B457157357
theorem B3347183 : Blo 1855629 3347183 := bstep (se 1 (by rfl) ⟨2510387, by rfl⟩ : syracuseStep 3347183 = 5020775) B5020775
theorem B4699367 : Blo 1855629 4699367 := bstep (se 1 (by rfl) ⟨3524525, by rfl⟩ : syracuseStep 4699367 = 7049051) B7049051
theorem B20349467 : Blo 1855629 20349467 := bstep (se 1 (by rfl) ⟨15262100, by rfl⟩ : syracuseStep 20349467 = 30524201) B30524201
theorem B203181047 : Blo 1855629 203181047 := bstep (se 1 (by rfl) ⟨152385785, by rfl⟩ : syracuseStep 203181047 = 304771571) B304771571
theorem B3132911 : Blo 1855629 3132911 := bstep (se 1 (by rfl) ⟨2349683, by rfl⟩ : syracuseStep 3132911 = 4699367) B4699367
theorem B8925821 : Blo 1855629 8925821 := bstep (se 3 (by rfl) ⟨1673591, by rfl⟩ : syracuseStep 8925821 = 3347183) B3347183
theorem B13566311 : Blo 1855629 13566311 := bstep (se 1 (by rfl) ⟨10174733, by rfl⟩ : syracuseStep 13566311 = 20349467) B20349467
theorem B5950547 : Blo 1855629 5950547 := bstep (se 1 (by rfl) ⟨4462910, by rfl⟩ : syracuseStep 5950547 = 8925821) B8925821
theorem B135454031 : Blo 1855629 135454031 := bstep (se 1 (by rfl) ⟨101590523, by rfl⟩ : syracuseStep 135454031 = 203181047) B203181047
theorem B2088607 : Blo 1855629 2088607 := bstep (se 1 (by rfl) ⟨1566455, by rfl⟩ : syracuseStep 2088607 = 3132911) B3132911
theorem B9044207 : Blo 1855629 9044207 := bstep (se 1 (by rfl) ⟨6783155, by rfl⟩ : syracuseStep 9044207 = 13566311) B13566311
theorem B3967031 : Blo 1855629 3967031 := bstep (se 1 (by rfl) ⟨2975273, by rfl⟩ : syracuseStep 3967031 = 5950547) B5950547
theorem B90302687 : Blo 1855629 90302687 := bstep (se 1 (by rfl) ⟨67727015, by rfl⟩ : syracuseStep 90302687 = 135454031) B135454031
theorem B2784809 : Blo 1855629 2784809 := bstep (se 2 (by rfl) ⟨1044303, by rfl⟩ : syracuseStep 2784809 = 2088607) B2088607
theorem B6029471 : Blo 1855629 6029471 := bstep (se 1 (by rfl) ⟨4522103, by rfl⟩ : syracuseStep 6029471 = 9044207) B9044207
theorem B1856539 : Blo 1855629 1856539 := bstep (se 1 (by rfl) ⟨1392404, by rfl⟩ : syracuseStep 1856539 = 2784809) B2784809
theorem B2644687 : Blo 1855629 2644687 := bstep (se 1 (by rfl) ⟨1983515, by rfl⟩ : syracuseStep 2644687 = 3967031) B3967031
theorem B60201791 : Blo 1855629 60201791 := bstep (se 1 (by rfl) ⟨45151343, by rfl⟩ : syracuseStep 60201791 = 90302687) B90302687
theorem B40134527 : Blo 1855629 40134527 := bstep (se 1 (by rfl) ⟨30100895, by rfl⟩ : syracuseStep 40134527 = 60201791) B60201791
theorem B3526249 : Blo 1855629 3526249 := bstep (se 2 (by rfl) ⟨1322343, by rfl⟩ : syracuseStep 3526249 = 2644687) B2644687
theorem B16078589 : Blo 1855629 16078589 := bstep (se 3 (by rfl) ⟨3014735, by rfl⟩ : syracuseStep 16078589 = 6029471) B6029471
theorem B26756351 : Blo 1855629 26756351 := bstep (se 1 (by rfl) ⟨20067263, by rfl⟩ : syracuseStep 26756351 = 40134527) B40134527
theorem B10719059 : Blo 1855629 10719059 := bstep (se 1 (by rfl) ⟨8039294, by rfl⟩ : syracuseStep 10719059 = 16078589) B16078589
theorem B4701665 : Blo 1855629 4701665 := bstep (se 2 (by rfl) ⟨1763124, by rfl⟩ : syracuseStep 4701665 = 3526249) B3526249
theorem B28584157 : Blo 1855629 28584157 := bstep (se 3 (by rfl) ⟨5359529, by rfl⟩ : syracuseStep 28584157 = 10719059) B10719059
theorem B17837567 : Blo 1855629 17837567 := bstep (se 1 (by rfl) ⟨13378175, by rfl⟩ : syracuseStep 17837567 = 26756351) B26756351
theorem B3134443 : Blo 1855629 3134443 := bstep (se 1 (by rfl) ⟨2350832, by rfl⟩ : syracuseStep 3134443 = 4701665) B4701665
theorem B4179257 : Blo 1855629 4179257 := bstep (se 2 (by rfl) ⟨1567221, by rfl⟩ : syracuseStep 4179257 = 3134443) B3134443
theorem B38112209 : Blo 1855629 38112209 := bstep (se 2 (by rfl) ⟨14292078, by rfl⟩ : syracuseStep 38112209 = 28584157) B28584157
theorem B11891711 : Blo 1855629 11891711 := bstep (se 1 (by rfl) ⟨8918783, by rfl⟩ : syracuseStep 11891711 = 17837567) B17837567
theorem B2786171 : Blo 1855629 2786171 := bstep (se 1 (by rfl) ⟨2089628, by rfl⟩ : syracuseStep 2786171 = 4179257) B4179257
theorem B25408139 : Blo 1855629 25408139 := bstep (se 1 (by rfl) ⟨19056104, by rfl⟩ : syracuseStep 25408139 = 38112209) B38112209
theorem B7927807 : Blo 1855629 7927807 := bstep (se 1 (by rfl) ⟨5945855, by rfl⟩ : syracuseStep 7927807 = 11891711) B11891711
theorem B10570409 : Blo 1855629 10570409 := bstep (se 2 (by rfl) ⟨3963903, by rfl⟩ : syracuseStep 10570409 = 7927807) B7927807
theorem B1857447 : Blo 1855629 1857447 := bstep (se 1 (by rfl) ⟨1393085, by rfl⟩ : syracuseStep 1857447 = 2786171) B2786171
theorem B67755037 : Blo 1855629 67755037 := bstep (se 3 (by rfl) ⟨12704069, by rfl⟩ : syracuseStep 67755037 = 25408139) B25408139
theorem B7046939 : Blo 1855629 7046939 := bstep (se 1 (by rfl) ⟨5285204, by rfl⟩ : syracuseStep 7046939 = 10570409) B10570409
theorem B90340049 : Blo 1855629 90340049 := bstep (se 2 (by rfl) ⟨33877518, by rfl⟩ : syracuseStep 90340049 = 67755037) B67755037
theorem B4697959 : Blo 1855629 4697959 := bstep (se 1 (by rfl) ⟨3523469, by rfl⟩ : syracuseStep 4697959 = 7046939) B7046939
theorem B60226699 : Blo 1855629 60226699 := bstep (se 1 (by rfl) ⟨45170024, by rfl⟩ : syracuseStep 60226699 = 90340049) B90340049
theorem B80302265 : Blo 1855629 80302265 := bstep (se 2 (by rfl) ⟨30113349, by rfl⟩ : syracuseStep 80302265 = 60226699) B60226699
theorem B6263945 : Blo 1855629 6263945 := bstep (se 2 (by rfl) ⟨2348979, by rfl⟩ : syracuseStep 6263945 = 4697959) B4697959
theorem B53534843 : Blo 1855629 53534843 := bstep (se 1 (by rfl) ⟨40151132, by rfl⟩ : syracuseStep 53534843 = 80302265) B80302265
theorem B4175963 : Blo 1855629 4175963 := bstep (se 1 (by rfl) ⟨3131972, by rfl⟩ : syracuseStep 4175963 = 6263945) B6263945
theorem B35689895 : Blo 1855629 35689895 := bstep (se 1 (by rfl) ⟨26767421, by rfl⟩ : syracuseStep 35689895 = 53534843) B53534843
theorem B2783975 : Blo 1855629 2783975 := bstep (se 1 (by rfl) ⟨2087981, by rfl⟩ : syracuseStep 2783975 = 4175963) B4175963
theorem B23793263 : Blo 1855629 23793263 := bstep (se 1 (by rfl) ⟨17844947, by rfl⟩ : syracuseStep 23793263 = 35689895) B35689895
theorem B1855983 : Blo 1855629 1855983 := bstep (se 1 (by rfl) ⟨1391987, by rfl⟩ : syracuseStep 1855983 = 2783975) B2783975
theorem B15862175 : Blo 1855629 15862175 := bstep (se 1 (by rfl) ⟨11896631, by rfl⟩ : syracuseStep 15862175 = 23793263) B23793263
theorem B10574783 : Blo 1855629 10574783 := bstep (se 1 (by rfl) ⟨7931087, by rfl⟩ : syracuseStep 10574783 = 15862175) B15862175
theorem B7049855 : Blo 1855629 7049855 := bstep (se 1 (by rfl) ⟨5287391, by rfl⟩ : syracuseStep 7049855 = 10574783) B10574783
theorem B4699903 : Blo 1855629 4699903 := bstep (se 1 (by rfl) ⟨3524927, by rfl⟩ : syracuseStep 4699903 = 7049855) B7049855
theorem B6266537 : Blo 1855629 6266537 := bstep (se 2 (by rfl) ⟨2349951, by rfl⟩ : syracuseStep 6266537 = 4699903) B4699903
theorem B4177691 : Blo 1855629 4177691 := bstep (se 1 (by rfl) ⟨3133268, by rfl⟩ : syracuseStep 4177691 = 6266537) B6266537
theorem B2785127 : Blo 1855629 2785127 := bstep (se 1 (by rfl) ⟨2088845, by rfl⟩ : syracuseStep 2785127 = 4177691) B4177691
theorem B1856751 : Blo 1855629 1856751 := bstep (se 1 (by rfl) ⟨1392563, by rfl⟩ : syracuseStep 1856751 = 2785127) B2785127

theorem C0 (j : ℕ) (h1 : 463907 ≤ j) (h2 : j ≤ 464406) : Blo 1855629 (4 * j + 3) := by
  interval_cases j
  · exact B1855631
  · exact B1855635
  · exact B1855639
  · exact B1855643
  · exact B1855647
  · exact B1855651
  · exact B1855655
  · exact B1855659
  · exact B1855663
  · exact B1855667
  · exact B1855671
  · exact B1855675
  · exact B1855679
  · exact B1855683
  · exact B1855687
  · exact B1855691
  · exact B1855695
  · exact B1855699
  · exact B1855703
  · exact B1855707
  · exact B1855711
  · exact B1855715
  · exact B1855719
  · exact B1855723
  · exact B1855727
  · exact B1855731
  · exact B1855735
  · exact B1855739
  · exact B1855743
  · exact B1855747
  · exact B1855751
  · exact B1855755
  · exact B1855759
  · exact B1855763
  · exact B1855767
  · exact B1855771
  · exact B1855775
  · exact B1855779
  · exact B1855783
  · exact B1855787
  · exact B1855791
  · exact B1855795
  · exact B1855799
  · exact B1855803
  · exact B1855807
  · exact B1855811
  · exact B1855815
  · exact B1855819
  · exact B1855823
  · exact B1855827
  · exact B1855831
  · exact B1855835
  · exact B1855839
  · exact B1855843
  · exact B1855847
  · exact B1855851
  · exact B1855855
  · exact B1855859
  · exact B1855863
  · exact B1855867
  · exact B1855871
  · exact B1855875
  · exact B1855879
  · exact B1855883
  · exact B1855887
  · exact B1855891
  · exact B1855895
  · exact B1855899
  · exact B1855903
  · exact B1855907
  · exact B1855911
  · exact B1855915
  · exact B1855919
  · exact B1855923
  · exact B1855927
  · exact B1855931
  · exact B1855935
  · exact B1855939
  · exact B1855943
  · exact B1855947
  · exact B1855951
  · exact B1855955
  · exact B1855959
  · exact B1855963
  · exact B1855967
  · exact B1855971
  · exact B1855975
  · exact B1855979
  · exact B1855983
  · exact B1855987
  · exact B1855991
  · exact B1855995
  · exact B1855999
  · exact B1856003
  · exact B1856007
  · exact B1856011
  · exact B1856015
  · exact B1856019
  · exact B1856023
  · exact B1856027
  · exact B1856031
  · exact B1856035
  · exact B1856039
  · exact B1856043
  · exact B1856047
  · exact B1856051
  · exact B1856055
  · exact B1856059
  · exact B1856063
  · exact B1856067
  · exact B1856071
  · exact B1856075
  · exact B1856079
  · exact B1856083
  · exact B1856087
  · exact B1856091
  · exact B1856095
  · exact B1856099
  · exact B1856103
  · exact B1856107
  · exact B1856111
  · exact B1856115
  · exact B1856119
  · exact B1856123
  · exact B1856127
  · exact B1856131
  · exact B1856135
  · exact B1856139
  · exact B1856143
  · exact B1856147
  · exact B1856151
  · exact B1856155
  · exact B1856159
  · exact B1856163
  · exact B1856167
  · exact B1856171
  · exact B1856175
  · exact B1856179
  · exact B1856183
  · exact B1856187
  · exact B1856191
  · exact B1856195
  · exact B1856199
  · exact B1856203
  · exact B1856207
  · exact B1856211
  · exact B1856215
  · exact B1856219
  · exact B1856223
  · exact B1856227
  · exact B1856231
  · exact B1856235
  · exact B1856239
  · exact B1856243
  · exact B1856247
  · exact B1856251
  · exact B1856255
  · exact B1856259
  · exact B1856263
  · exact B1856267
  · exact B1856271
  · exact B1856275
  · exact B1856279
  · exact B1856283
  · exact B1856287
  · exact B1856291
  · exact B1856295
  · exact B1856299
  · exact B1856303
  · exact B1856307
  · exact B1856311
  · exact B1856315
  · exact B1856319
  · exact B1856323
  · exact B1856327
  · exact B1856331
  · exact B1856335
  · exact B1856339
  · exact B1856343
  · exact B1856347
  · exact B1856351
  · exact B1856355
  · exact B1856359
  · exact B1856363
  · exact B1856367
  · exact B1856371
  · exact B1856375
  · exact B1856379
  · exact B1856383
  · exact B1856387
  · exact B1856391
  · exact B1856395
  · exact B1856399
  · exact B1856403
  · exact B1856407
  · exact B1856411
  · exact B1856415
  · exact B1856419
  · exact B1856423
  · exact B1856427
  · exact B1856431
  · exact B1856435
  · exact B1856439
  · exact B1856443
  · exact B1856447
  · exact B1856451
  · exact B1856455
  · exact B1856459
  · exact B1856463
  · exact B1856467
  · exact B1856471
  · exact B1856475
  · exact B1856479
  · exact B1856483
  · exact B1856487
  · exact B1856491
  · exact B1856495
  · exact B1856499
  · exact B1856503
  · exact B1856507
  · exact B1856511
  · exact B1856515
  · exact B1856519
  · exact B1856523
  · exact B1856527
  · exact B1856531
  · exact B1856535
  · exact B1856539
  · exact B1856543
  · exact B1856547
  · exact B1856551
  · exact B1856555
  · exact B1856559
  · exact B1856563
  · exact B1856567
  · exact B1856571
  · exact B1856575
  · exact B1856579
  · exact B1856583
  · exact B1856587
  · exact B1856591
  · exact B1856595
  · exact B1856599
  · exact B1856603
  · exact B1856607
  · exact B1856611
  · exact B1856615
  · exact B1856619
  · exact B1856623
  · exact B1856627
  · exact B1856631
  · exact B1856635
  · exact B1856639
  · exact B1856643
  · exact B1856647
  · exact B1856651
  · exact B1856655
  · exact B1856659
  · exact B1856663
  · exact B1856667
  · exact B1856671
  · exact B1856675
  · exact B1856679
  · exact B1856683
  · exact B1856687
  · exact B1856691
  · exact B1856695
  · exact B1856699
  · exact B1856703
  · exact B1856707
  · exact B1856711
  · exact B1856715
  · exact B1856719
  · exact B1856723
  · exact B1856727
  · exact B1856731
  · exact B1856735
  · exact B1856739
  · exact B1856743
  · exact B1856747
  · exact B1856751
  · exact B1856755
  · exact B1856759
  · exact B1856763
  · exact B1856767
  · exact B1856771
  · exact B1856775
  · exact B1856779
  · exact B1856783
  · exact B1856787
  · exact B1856791
  · exact B1856795
  · exact B1856799
  · exact B1856803
  · exact B1856807
  · exact B1856811
  · exact B1856815
  · exact B1856819
  · exact B1856823
  · exact B1856827
  · exact B1856831
  · exact B1856835
  · exact B1856839
  · exact B1856843
  · exact B1856847
  · exact B1856851
  · exact B1856855
  · exact B1856859
  · exact B1856863
  · exact B1856867
  · exact B1856871
  · exact B1856875
  · exact B1856879
  · exact B1856883
  · exact B1856887
  · exact B1856891
  · exact B1856895
  · exact B1856899
  · exact B1856903
  · exact B1856907
  · exact B1856911
  · exact B1856915
  · exact B1856919
  · exact B1856923
  · exact B1856927
  · exact B1856931
  · exact B1856935
  · exact B1856939
  · exact B1856943
  · exact B1856947
  · exact B1856951
  · exact B1856955
  · exact B1856959
  · exact B1856963
  · exact B1856967
  · exact B1856971
  · exact B1856975
  · exact B1856979
  · exact B1856983
  · exact B1856987
  · exact B1856991
  · exact B1856995
  · exact B1856999
  · exact B1857003
  · exact B1857007
  · exact B1857011
  · exact B1857015
  · exact B1857019
  · exact B1857023
  · exact B1857027
  · exact B1857031
  · exact B1857035
  · exact B1857039
  · exact B1857043
  · exact B1857047
  · exact B1857051
  · exact B1857055
  · exact B1857059
  · exact B1857063
  · exact B1857067
  · exact B1857071
  · exact B1857075
  · exact B1857079
  · exact B1857083
  · exact B1857087
  · exact B1857091
  · exact B1857095
  · exact B1857099
  · exact B1857103
  · exact B1857107
  · exact B1857111
  · exact B1857115
  · exact B1857119
  · exact B1857123
  · exact B1857127
  · exact B1857131
  · exact B1857135
  · exact B1857139
  · exact B1857143
  · exact B1857147
  · exact B1857151
  · exact B1857155
  · exact B1857159
  · exact B1857163
  · exact B1857167
  · exact B1857171
  · exact B1857175
  · exact B1857179
  · exact B1857183
  · exact B1857187
  · exact B1857191
  · exact B1857195
  · exact B1857199
  · exact B1857203
  · exact B1857207
  · exact B1857211
  · exact B1857215
  · exact B1857219
  · exact B1857223
  · exact B1857227
  · exact B1857231
  · exact B1857235
  · exact B1857239
  · exact B1857243
  · exact B1857247
  · exact B1857251
  · exact B1857255
  · exact B1857259
  · exact B1857263
  · exact B1857267
  · exact B1857271
  · exact B1857275
  · exact B1857279
  · exact B1857283
  · exact B1857287
  · exact B1857291
  · exact B1857295
  · exact B1857299
  · exact B1857303
  · exact B1857307
  · exact B1857311
  · exact B1857315
  · exact B1857319
  · exact B1857323
  · exact B1857327
  · exact B1857331
  · exact B1857335
  · exact B1857339
  · exact B1857343
  · exact B1857347
  · exact B1857351
  · exact B1857355
  · exact B1857359
  · exact B1857363
  · exact B1857367
  · exact B1857371
  · exact B1857375
  · exact B1857379
  · exact B1857383
  · exact B1857387
  · exact B1857391
  · exact B1857395
  · exact B1857399
  · exact B1857403
  · exact B1857407
  · exact B1857411
  · exact B1857415
  · exact B1857419
  · exact B1857423
  · exact B1857427
  · exact B1857431
  · exact B1857435
  · exact B1857439
  · exact B1857443
  · exact B1857447
  · exact B1857451
  · exact B1857455
  · exact B1857459
  · exact B1857463
  · exact B1857467
  · exact B1857471
  · exact B1857475
  · exact B1857479
  · exact B1857483
  · exact B1857487
  · exact B1857491
  · exact B1857495
  · exact B1857499
  · exact B1857503
  · exact B1857507
  · exact B1857511
  · exact B1857515
  · exact B1857519
  · exact B1857523
  · exact B1857527
  · exact B1857531
  · exact B1857535
  · exact B1857539
  · exact B1857543
  · exact B1857547
  · exact B1857551
  · exact B1857555
  · exact B1857559
  · exact B1857563
  · exact B1857567
  · exact B1857571
  · exact B1857575
  · exact B1857579
  · exact B1857583
  · exact B1857587
  · exact B1857591
  · exact B1857595
  · exact B1857599
  · exact B1857603
  · exact B1857607
  · exact B1857611
  · exact B1857615
  · exact B1857619
  · exact B1857623
  · exact B1857627

theorem solution (m : ℕ) (hlo : 1855629 ≤ m) (hhi : m ≤ 1857629) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 463907 ≤ j := by omega
    have hj2 : j ≤ 464406 := by omega
    have hb : Blo 1855629 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
