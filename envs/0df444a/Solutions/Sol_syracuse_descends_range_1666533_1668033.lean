-- Prove2me | solution 1 for syracuse_descends_range_1666533_1668033
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:20:13.36879+00:00
-- url     : https://prove2.me/submissions/13711b3b-ed68-426f-b8b7-727494a067d1

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


theorem B1875973 : Blo 1666533 1875973 := bbase (se 4 (by rfl) ⟨175872, by rfl⟩ : syracuseStep 1875973 = 351745) (by norm_num)
theorem B3751973 : Blo 1666533 3751973 := bbase (se 4 (by rfl) ⟨351747, by rfl⟩ : syracuseStep 3751973 = 703495) (by norm_num)
theorem B1876009 : Blo 1666533 1876009 := bbase (se 2 (by rfl) ⟨703503, by rfl⟩ : syracuseStep 1876009 = 1407007) (by norm_num)
theorem B4218925 : Blo 1666533 4218925 := bbase (se 3 (by rfl) ⟨791048, by rfl⟩ : syracuseStep 4218925 = 1582097) (by norm_num)
theorem B2670661 : Blo 1666533 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B1876045 : Blo 1666533 1876045 := bbase (se 3 (by rfl) ⟨351758, by rfl⟩ : syracuseStep 1876045 = 703517) (by norm_num)
theorem B3752045 : Blo 1666533 3752045 := bbase (se 3 (by rfl) ⟨703508, by rfl⟩ : syracuseStep 3752045 = 1407017) (by norm_num)
theorem B1876081 : Blo 1666533 1876081 := bbase (se 2 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 1876081 = 1407061) (by norm_num)
theorem B1876117 : Blo 1666533 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B4219037 : Blo 1666533 4219037 := bbase (se 3 (by rfl) ⟨791069, by rfl⟩ : syracuseStep 4219037 = 1582139) (by norm_num)
theorem B3752117 : Blo 1666533 3752117 := bbase (se 5 (by rfl) ⟨175880, by rfl⟩ : syracuseStep 3752117 = 351761) (by norm_num)
theorem B1876153 : Blo 1666533 1876153 := bbase (se 2 (by rfl) ⟨703557, by rfl⟩ : syracuseStep 1876153 = 1407115) (by norm_num)
theorem B3801277 : Blo 1666533 3801277 := bbase (se 3 (by rfl) ⟨712739, by rfl⟩ : syracuseStep 3801277 = 1425479) (by norm_num)
theorem B2744533 : Blo 1666533 2744533 := bbase (se 7 (by rfl) ⟨32162, by rfl⟩ : syracuseStep 2744533 = 64325) (by norm_num)
theorem B1876189 : Blo 1666533 1876189 := bbase (se 3 (by rfl) ⟨351785, by rfl⟩ : syracuseStep 1876189 = 703571) (by norm_num)
theorem B5628149 : Blo 1666533 5628149 := bbase (se 5 (by rfl) ⟨263819, by rfl⟩ : syracuseStep 5628149 = 527639) (by norm_num)
theorem B3752189 : Blo 1666533 3752189 := bbase (se 3 (by rfl) ⟨703535, by rfl⟩ : syracuseStep 3752189 = 1407071) (by norm_num)
theorem B1876225 : Blo 1666533 1876225 := bbase (se 2 (by rfl) ⟨703584, by rfl⟩ : syracuseStep 1876225 = 1407169) (by norm_num)
theorem B1876261 : Blo 1666533 1876261 := bbase (se 4 (by rfl) ⟨175899, by rfl⟩ : syracuseStep 1876261 = 351799) (by norm_num)
theorem B3752261 : Blo 1666533 3752261 := bbase (se 4 (by rfl) ⟨351774, by rfl⟩ : syracuseStep 3752261 = 703549) (by norm_num)
theorem B1876297 : Blo 1666533 1876297 := bbase (se 2 (by rfl) ⟨703611, by rfl⟩ : syracuseStep 1876297 = 1407223) (by norm_num)
theorem B4219229 : Blo 1666533 4219229 := bbase (se 3 (by rfl) ⟨791105, by rfl⟩ : syracuseStep 4219229 = 1582211) (by norm_num)
theorem B1876333 : Blo 1666533 1876333 := bbase (se 3 (by rfl) ⟨351812, by rfl⟩ : syracuseStep 1876333 = 703625) (by norm_num)
theorem B3752333 : Blo 1666533 3752333 := bbase (se 3 (by rfl) ⟨703562, by rfl⟩ : syracuseStep 3752333 = 1407125) (by norm_num)
theorem B1900945 : Blo 1666533 1900945 := bbase (se 2 (by rfl) ⟨712854, by rfl⟩ : syracuseStep 1900945 = 1425709) (by norm_num)
theorem B1876369 : Blo 1666533 1876369 := bbase (se 2 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 1876369 = 1407277) (by norm_num)
theorem B4506005 : Blo 1666533 4506005 := bbase (se 6 (by rfl) ⟨105609, by rfl⟩ : syracuseStep 4506005 = 211219) (by norm_num)
theorem B1876405 : Blo 1666533 1876405 := bbase (se 5 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 1876405 = 175913) (by norm_num)
theorem B3752405 : Blo 1666533 3752405 := bbase (se 7 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 3752405 = 87947) (by norm_num)
theorem B1876441 : Blo 1666533 1876441 := bbase (se 2 (by rfl) ⟨703665, by rfl⟩ : syracuseStep 1876441 = 1407331) (by norm_num)
theorem B5071349 : Blo 1666533 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B1876477 : Blo 1666533 1876477 := bbase (se 3 (by rfl) ⟨351839, by rfl⟩ : syracuseStep 1876477 = 703679) (by norm_num)
theorem B3752477 : Blo 1666533 3752477 := bbase (se 3 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 3752477 = 1407179) (by norm_num)
theorem B1876513 : Blo 1666533 1876513 := bbase (se 2 (by rfl) ⟨703692, by rfl⟩ : syracuseStep 1876513 = 1407385) (by norm_num)
theorem B2253349 : Blo 1666533 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B12182069 : Blo 1666533 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B3752549 : Blo 1666533 3752549 := bbase (se 4 (by rfl) ⟨351801, by rfl⟩ : syracuseStep 3752549 = 703603) (by norm_num)
theorem B5628581 : Blo 1666533 5628581 := bbase (se 4 (by rfl) ⟨527679, by rfl⟩ : syracuseStep 5628581 = 1055359) (by norm_num)
theorem B3752621 : Blo 1666533 3752621 := bbase (se 3 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 3752621 = 1407233) (by norm_num)
theorem B4219573 : Blo 1666533 4219573 := bbase (se 5 (by rfl) ⟨197792, by rfl⟩ : syracuseStep 4219573 = 395585) (by norm_num)
theorem B3752693 : Blo 1666533 3752693 := bbase (se 5 (by rfl) ⟨175907, by rfl⟩ : syracuseStep 3752693 = 351815) (by norm_num)
theorem B6333173 : Blo 1666533 6333173 := bbase (se 5 (by rfl) ⟨296867, by rfl⟩ : syracuseStep 6333173 = 593735) (by norm_num)
theorem B4219685 : Blo 1666533 4219685 := bbase (se 4 (by rfl) ⟨395595, by rfl⟩ : syracuseStep 4219685 = 791191) (by norm_num)
theorem B3752765 : Blo 1666533 3752765 := bbase (se 3 (by rfl) ⟨703643, by rfl⟩ : syracuseStep 3752765 = 1407287) (by norm_num)
theorem B3752837 : Blo 1666533 3752837 := bbase (se 4 (by rfl) ⟨351828, by rfl⟩ : syracuseStep 3752837 = 703657) (by norm_num)
theorem B2253749 : Blo 1666533 2253749 := bbase (se 5 (by rfl) ⟨105644, by rfl⟩ : syracuseStep 2253749 = 211289) (by norm_num)
theorem B4006837 : Blo 1666533 4006837 := bbase (se 5 (by rfl) ⟨187820, by rfl⟩ : syracuseStep 4006837 = 375641) (by norm_num)
theorem B3752909 : Blo 1666533 3752909 := bbase (se 3 (by rfl) ⟨703670, by rfl⟩ : syracuseStep 3752909 = 1407341) (by norm_num)
theorem B8438741 : Blo 1666533 8438741 := bbase (se 7 (by rfl) ⟨98891, by rfl⟩ : syracuseStep 8438741 = 197783) (by norm_num)
theorem B4219877 : Blo 1666533 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B10683413 : Blo 1666533 10683413 := bbase (se 6 (by rfl) ⟨250392, by rfl⟩ : syracuseStep 10683413 = 500785) (by norm_num)
theorem B3752981 : Blo 1666533 3752981 := bbase (se 6 (by rfl) ⟨87960, by rfl⟩ : syracuseStep 3752981 = 175921) (by norm_num)
theorem B5629013 : Blo 1666533 5629013 := bbase (se 8 (by rfl) ⟨32982, by rfl⟩ : syracuseStep 5629013 = 65965) (by norm_num)
theorem B3753053 : Blo 1666533 3753053 := bbase (se 3 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 3753053 = 1407395) (by norm_num)
theorem B1901665 : Blo 1666533 1901665 := bbase (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) (by norm_num)
theorem B2253997 : Blo 1666533 2253997 := bbase (se 3 (by rfl) ⟨422624, by rfl⟩ : syracuseStep 2253997 = 845249) (by norm_num)
theorem B8012981 : Blo 1666533 8012981 := bbase (se 5 (by rfl) ⟨375608, by rfl⟩ : syracuseStep 8012981 = 751217) (by norm_num)
theorem B2499821 : Blo 1666533 2499821 := bbase (se 3 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 2499821 = 937433) (by norm_num)
theorem B1901821 : Blo 1666533 1901821 := bbase (se 3 (by rfl) ⟨356591, by rfl⟩ : syracuseStep 1901821 = 713183) (by norm_num)
theorem B2499845 : Blo 1666533 2499845 := bbase (se 4 (by rfl) ⟨234360, by rfl⟩ : syracuseStep 2499845 = 468721) (by norm_num)
theorem B2499869 : Blo 1666533 2499869 := bbase (se 3 (by rfl) ⟨468725, by rfl⟩ : syracuseStep 2499869 = 937451) (by norm_num)
theorem B2499893 : Blo 1666533 2499893 := bbase (se 5 (by rfl) ⟨117182, by rfl⟩ : syracuseStep 2499893 = 234365) (by norm_num)
theorem B4220221 : Blo 1666533 4220221 := bbase (se 3 (by rfl) ⟨791291, by rfl⟩ : syracuseStep 4220221 = 1582583) (by norm_num)
theorem B2499917 : Blo 1666533 2499917 := bbase (se 3 (by rfl) ⟨468734, by rfl⟩ : syracuseStep 2499917 = 937469) (by norm_num)
theorem B10020181 : Blo 1666533 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B210920789 : Blo 1666533 210920789 := bbase (se 12 (by rfl) ⟨77241, by rfl⟩ : syracuseStep 210920789 = 154483) (by norm_num)
theorem B2499941 : Blo 1666533 2499941 := bbase (se 4 (by rfl) ⟨234369, by rfl⟩ : syracuseStep 2499941 = 468739) (by norm_num)
theorem B17114485 : Blo 1666533 17114485 := bbase (se 5 (by rfl) ⟨802241, by rfl⟩ : syracuseStep 17114485 = 1604483) (by norm_num)
theorem B2499965 : Blo 1666533 2499965 := bbase (se 3 (by rfl) ⟨468743, by rfl⟩ : syracuseStep 2499965 = 937487) (by norm_num)
theorem B2499989 : Blo 1666533 2499989 := bbase (se 6 (by rfl) ⟨58593, by rfl⟩ : syracuseStep 2499989 = 117187) (by norm_num)
theorem B2500013 : Blo 1666533 2500013 := bbase (se 3 (by rfl) ⟨468752, by rfl⟩ : syracuseStep 2500013 = 937505) (by norm_num)
theorem B4220333 : Blo 1666533 4220333 := bbase (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) (by norm_num)
theorem B2500037 : Blo 1666533 2500037 := bbase (se 4 (by rfl) ⟨234378, by rfl⟩ : syracuseStep 2500037 = 468757) (by norm_num)
theorem B7120325 : Blo 1666533 7120325 := bbase (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) (by norm_num)
theorem B1713613 : Blo 1666533 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B2500061 : Blo 1666533 2500061 := bbase (se 3 (by rfl) ⟨468761, by rfl⟩ : syracuseStep 2500061 = 937523) (by norm_num)
theorem B2500085 : Blo 1666533 2500085 := bbase (se 5 (by rfl) ⟨117191, by rfl⟩ : syracuseStep 2500085 = 234383) (by norm_num)
theorem B5629445 : Blo 1666533 5629445 := bbase (se 4 (by rfl) ⟨527760, by rfl⟩ : syracuseStep 5629445 = 1055521) (by norm_num)
theorem B2500109 : Blo 1666533 2500109 := bbase (se 3 (by rfl) ⟨468770, by rfl⟩ : syracuseStep 2500109 = 937541) (by norm_num)
theorem B2500133 : Blo 1666533 2500133 := bbase (se 4 (by rfl) ⟨234387, by rfl⟩ : syracuseStep 2500133 = 468775) (by norm_num)
theorem B2500157 : Blo 1666533 2500157 := bbase (se 3 (by rfl) ⟨468779, by rfl⟩ : syracuseStep 2500157 = 937559) (by norm_num)
theorem B2500181 : Blo 1666533 2500181 := bbase (se 8 (by rfl) ⟨14649, by rfl⟩ : syracuseStep 2500181 = 29299) (by norm_num)
theorem B2500205 : Blo 1666533 2500205 := bbase (se 3 (by rfl) ⟨468788, by rfl⟩ : syracuseStep 2500205 = 937577) (by norm_num)
theorem B4220525 : Blo 1666533 4220525 := bbase (se 3 (by rfl) ⟨791348, by rfl⟩ : syracuseStep 4220525 = 1582697) (by norm_num)
theorem B2500229 : Blo 1666533 2500229 := bbase (se 4 (by rfl) ⟨234396, by rfl⟩ : syracuseStep 2500229 = 468793) (by norm_num)
theorem B2139793 : Blo 1666533 2139793 := bbase (se 2 (by rfl) ⟨802422, by rfl⟩ : syracuseStep 2139793 = 1604845) (by norm_num)
theorem B1926805 : Blo 1666533 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B2500253 : Blo 1666533 2500253 := bbase (se 3 (by rfl) ⟨468797, by rfl⟩ : syracuseStep 2500253 = 937595) (by norm_num)
theorem B2500277 : Blo 1666533 2500277 := bbase (se 5 (by rfl) ⟨117200, by rfl⟩ : syracuseStep 2500277 = 234401) (by norm_num)
theorem B3163853 : Blo 1666533 3163853 := bbase (se 3 (by rfl) ⟨593222, by rfl⟩ : syracuseStep 3163853 = 1186445) (by norm_num)
theorem B2500301 : Blo 1666533 2500301 := bbase (se 3 (by rfl) ⟨468806, by rfl⟩ : syracuseStep 2500301 = 937613) (by norm_num)
theorem B2500325 : Blo 1666533 2500325 := bbase (se 4 (by rfl) ⟨234405, by rfl⟩ : syracuseStep 2500325 = 468811) (by norm_num)
theorem B2500349 : Blo 1666533 2500349 := bbase (se 3 (by rfl) ⟨468815, by rfl⟩ : syracuseStep 2500349 = 937631) (by norm_num)
theorem B2500373 : Blo 1666533 2500373 := bbase (se 6 (by rfl) ⟨58602, by rfl⟩ : syracuseStep 2500373 = 117205) (by norm_num)
theorem B6006565 : Blo 1666533 6006565 := bbase (se 4 (by rfl) ⟨563115, by rfl⟩ : syracuseStep 6006565 = 1126231) (by norm_num)
theorem B2500397 : Blo 1666533 2500397 := bbase (se 3 (by rfl) ⟨468824, by rfl⟩ : syracuseStep 2500397 = 937649) (by norm_num)
theorem B2500421 : Blo 1666533 2500421 := bbase (se 4 (by rfl) ⟨234414, by rfl⟩ : syracuseStep 2500421 = 468829) (by norm_num)
theorem B3163997 : Blo 1666533 3163997 := bbase (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) (by norm_num)
theorem B2500445 : Blo 1666533 2500445 := bbase (se 3 (by rfl) ⟨468833, by rfl⟩ : syracuseStep 2500445 = 937667) (by norm_num)
theorem B2500469 : Blo 1666533 2500469 := bbase (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) (by norm_num)
theorem B2500493 : Blo 1666533 2500493 := bbase (se 3 (by rfl) ⟨468842, by rfl⟩ : syracuseStep 2500493 = 937685) (by norm_num)
theorem B1689509 : Blo 1666533 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B2500517 : Blo 1666533 2500517 := bbase (se 4 (by rfl) ⟨234423, by rfl⟩ : syracuseStep 2500517 = 468847) (by norm_num)
theorem B1804205 : Blo 1666533 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B2500541 : Blo 1666533 2500541 := bbase (se 3 (by rfl) ⟨468851, by rfl⟩ : syracuseStep 2500541 = 937703) (by norm_num)
theorem B1689541 : Blo 1666533 1689541 := bbase (se 4 (by rfl) ⟨158394, by rfl⟩ : syracuseStep 1689541 = 316789) (by norm_num)
theorem B4220869 : Blo 1666533 4220869 := bbase (se 4 (by rfl) ⟨395706, by rfl⟩ : syracuseStep 4220869 = 791413) (by norm_num)
theorem B2500565 : Blo 1666533 2500565 := bbase (se 7 (by rfl) ⟨29303, by rfl⟩ : syracuseStep 2500565 = 58607) (by norm_num)
theorem B6760421 : Blo 1666533 6760421 := bbase (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) (by norm_num)
theorem B2500589 : Blo 1666533 2500589 := bbase (se 3 (by rfl) ⟨468860, by rfl⟩ : syracuseStep 2500589 = 937721) (by norm_num)
theorem B2500613 : Blo 1666533 2500613 := bbase (se 4 (by rfl) ⟨234432, by rfl⟩ : syracuseStep 2500613 = 468865) (by norm_num)
theorem B2500637 : Blo 1666533 2500637 := bbase (se 3 (by rfl) ⟨468869, by rfl⟩ : syracuseStep 2500637 = 937739) (by norm_num)
theorem B2500661 : Blo 1666533 2500661 := bbase (se 5 (by rfl) ⟨117218, by rfl⟩ : syracuseStep 2500661 = 234437) (by norm_num)
theorem B4220981 : Blo 1666533 4220981 := bbase (se 5 (by rfl) ⟨197858, by rfl⟩ : syracuseStep 4220981 = 395717) (by norm_num)
theorem B2500685 : Blo 1666533 2500685 := bbase (se 3 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 2500685 = 937757) (by norm_num)
theorem B2500709 : Blo 1666533 2500709 := bbase (se 4 (by rfl) ⟨234441, by rfl⟩ : syracuseStep 2500709 = 468883) (by norm_num)
theorem B3164285 : Blo 1666533 3164285 := bbase (se 3 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 3164285 = 1186607) (by norm_num)
theorem B2500733 : Blo 1666533 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B2500757 : Blo 1666533 2500757 := bbase (se 6 (by rfl) ⟨58611, by rfl⟩ : syracuseStep 2500757 = 117223) (by norm_num)
theorem B2500781 : Blo 1666533 2500781 := bbase (se 3 (by rfl) ⟨468896, by rfl⟩ : syracuseStep 2500781 = 937793) (by norm_num)
theorem B2500805 : Blo 1666533 2500805 := bbase (se 4 (by rfl) ⟨234450, by rfl⟩ : syracuseStep 2500805 = 468901) (by norm_num)
theorem B2500829 : Blo 1666533 2500829 := bbase (se 3 (by rfl) ⟨468905, by rfl⟩ : syracuseStep 2500829 = 937811) (by norm_num)
theorem B8669413 : Blo 1666533 8669413 := bbase (se 4 (by rfl) ⟨812757, by rfl⟩ : syracuseStep 8669413 = 1625515) (by norm_num)
theorem B1779941 : Blo 1666533 1779941 := bbase (se 4 (by rfl) ⟨166869, by rfl⟩ : syracuseStep 1779941 = 333739) (by norm_num)
theorem B8440037 : Blo 1666533 8440037 := bbase (se 4 (by rfl) ⟨791253, by rfl⟩ : syracuseStep 8440037 = 1582507) (by norm_num)
theorem B2500853 : Blo 1666533 2500853 := bbase (se 5 (by rfl) ⟨117227, by rfl⟩ : syracuseStep 2500853 = 234455) (by norm_num)
theorem B4221173 : Blo 1666533 4221173 := bbase (se 5 (by rfl) ⟨197867, by rfl⟩ : syracuseStep 4221173 = 395735) (by norm_num)
theorem B2500877 : Blo 1666533 2500877 := bbase (se 3 (by rfl) ⟨468914, by rfl⟩ : syracuseStep 2500877 = 937829) (by norm_num)
theorem B3164437 : Blo 1666533 3164437 := bbase (se 6 (by rfl) ⟨74166, by rfl⟩ : syracuseStep 3164437 = 148333) (by norm_num)
theorem B2500901 : Blo 1666533 2500901 := bbase (se 4 (by rfl) ⟨234459, by rfl⟩ : syracuseStep 2500901 = 468919) (by norm_num)
theorem B1780013 : Blo 1666533 1780013 := bbase (se 3 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 1780013 = 667505) (by norm_num)
theorem B2500925 : Blo 1666533 2500925 := bbase (se 3 (by rfl) ⟨468923, by rfl⟩ : syracuseStep 2500925 = 937847) (by norm_num)
theorem B2500949 : Blo 1666533 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B7317845 : Blo 1666533 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B2500973 : Blo 1666533 2500973 := bbase (se 3 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 2500973 = 937865) (by norm_num)
theorem B2500997 : Blo 1666533 2500997 := bbase (se 4 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 2500997 = 468937) (by norm_num)
theorem B2501021 : Blo 1666533 2501021 := bbase (se 3 (by rfl) ⟨468941, by rfl⟩ : syracuseStep 2501021 = 937883) (by norm_num)
theorem B7121317 : Blo 1666533 7121317 := bbase (se 4 (by rfl) ⟨667623, by rfl⟩ : syracuseStep 7121317 = 1335247) (by norm_num)
theorem B2812333 : Blo 1666533 2812333 := bbase (se 3 (by rfl) ⟨527312, by rfl⟩ : syracuseStep 2812333 = 1054625) (by norm_num)
theorem B2501045 : Blo 1666533 2501045 := bbase (se 5 (by rfl) ⟨117236, by rfl⟩ : syracuseStep 2501045 = 234473) (by norm_num)
theorem B2501069 : Blo 1666533 2501069 := bbase (se 3 (by rfl) ⟨468950, by rfl⟩ : syracuseStep 2501069 = 937901) (by norm_num)
theorem B2501093 : Blo 1666533 2501093 := bbase (se 4 (by rfl) ⟨234477, by rfl⟩ : syracuseStep 2501093 = 468955) (by norm_num)
theorem B1780201 : Blo 1666533 1780201 := bbase (se 2 (by rfl) ⟨667575, by rfl⟩ : syracuseStep 1780201 = 1335151) (by norm_num)
theorem B2501117 : Blo 1666533 2501117 := bbase (se 3 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 2501117 = 937919) (by norm_num)
theorem B2812421 : Blo 1666533 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B2501141 : Blo 1666533 2501141 := bbase (se 6 (by rfl) ⟨58620, by rfl⟩ : syracuseStep 2501141 = 117241) (by norm_num)
theorem B2501165 : Blo 1666533 2501165 := bbase (se 3 (by rfl) ⟨468968, by rfl⟩ : syracuseStep 2501165 = 937937) (by norm_num)
theorem B3803693 : Blo 1666533 3803693 := bbase (se 3 (by rfl) ⟨713192, by rfl⟩ : syracuseStep 3803693 = 1426385) (by norm_num)
theorem B3164741 : Blo 1666533 3164741 := bbase (se 4 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 3164741 = 593389) (by norm_num)
theorem B2501189 : Blo 1666533 2501189 := bbase (se 4 (by rfl) ⟨234486, by rfl⟩ : syracuseStep 2501189 = 468973) (by norm_num)
theorem B4221517 : Blo 1666533 4221517 := bbase (se 3 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 4221517 = 1583069) (by norm_num)
theorem B2501213 : Blo 1666533 2501213 := bbase (se 3 (by rfl) ⟨468977, by rfl⟩ : syracuseStep 2501213 = 937955) (by norm_num)
theorem B2501237 : Blo 1666533 2501237 := bbase (se 5 (by rfl) ⟨117245, by rfl⟩ : syracuseStep 2501237 = 234491) (by norm_num)
theorem B2812549 : Blo 1666533 2812549 := bbase (se 4 (by rfl) ⟨263676, by rfl⟩ : syracuseStep 2812549 = 527353) (by norm_num)
theorem B2501261 : Blo 1666533 2501261 := bbase (se 3 (by rfl) ⟨468986, by rfl⟩ : syracuseStep 2501261 = 937973) (by norm_num)
theorem B1780385 : Blo 1666533 1780385 := bbase (se 2 (by rfl) ⟨667644, by rfl⟩ : syracuseStep 1780385 = 1335289) (by norm_num)
theorem B2501285 : Blo 1666533 2501285 := bbase (se 4 (by rfl) ⟨234495, by rfl⟩ : syracuseStep 2501285 = 468991) (by norm_num)
theorem B2501309 : Blo 1666533 2501309 := bbase (se 3 (by rfl) ⟨468995, by rfl⟩ : syracuseStep 2501309 = 937991) (by norm_num)
theorem B4221629 : Blo 1666533 4221629 := bbase (se 3 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 4221629 = 1583111) (by norm_num)
theorem B2501333 : Blo 1666533 2501333 := bbase (se 7 (by rfl) ⟨29312, by rfl⟩ : syracuseStep 2501333 = 58625) (by norm_num)
theorem B2812637 : Blo 1666533 2812637 := bbase (se 3 (by rfl) ⟨527369, by rfl⟩ : syracuseStep 2812637 = 1054739) (by norm_num)
theorem B2501357 : Blo 1666533 2501357 := bbase (se 3 (by rfl) ⟨469004, by rfl⟩ : syracuseStep 2501357 = 938009) (by norm_num)
theorem B2501381 : Blo 1666533 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B2501405 : Blo 1666533 2501405 := bbase (se 3 (by rfl) ⟨469013, by rfl⟩ : syracuseStep 2501405 = 938027) (by norm_num)
theorem B2501429 : Blo 1666533 2501429 := bbase (se 5 (by rfl) ⟨117254, by rfl⟩ : syracuseStep 2501429 = 234509) (by norm_num)
theorem B4746053 : Blo 1666533 4746053 := bbase (se 4 (by rfl) ⟨444942, by rfl⟩ : syracuseStep 4746053 = 889885) (by norm_num)
theorem B2501453 : Blo 1666533 2501453 := bbase (se 3 (by rfl) ⟨469022, by rfl⟩ : syracuseStep 2501453 = 938045) (by norm_num)
theorem B2812765 : Blo 1666533 2812765 := bbase (se 3 (by rfl) ⟨527393, by rfl⟩ : syracuseStep 2812765 = 1054787) (by norm_num)
theorem B2501477 : Blo 1666533 2501477 := bbase (se 4 (by rfl) ⟨234513, by rfl⟩ : syracuseStep 2501477 = 469027) (by norm_num)
theorem B2501501 : Blo 1666533 2501501 := bbase (se 3 (by rfl) ⟨469031, by rfl⟩ : syracuseStep 2501501 = 938063) (by norm_num)
theorem B4221821 : Blo 1666533 4221821 := bbase (se 3 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 4221821 = 1583183) (by norm_num)
theorem B2501525 : Blo 1666533 2501525 := bbase (se 6 (by rfl) ⟨58629, by rfl⟩ : syracuseStep 2501525 = 117259) (by norm_num)
theorem B4336541 : Blo 1666533 4336541 := bbase (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) (by norm_num)
theorem B2501549 : Blo 1666533 2501549 := bbase (se 3 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 2501549 = 938081) (by norm_num)
theorem B2812853 : Blo 1666533 2812853 := bbase (se 5 (by rfl) ⟨131852, by rfl⟩ : syracuseStep 2812853 = 263705) (by norm_num)
theorem B2501573 : Blo 1666533 2501573 := bbase (se 4 (by rfl) ⟨234522, by rfl⟩ : syracuseStep 2501573 = 469045) (by norm_num)
theorem B13519829 : Blo 1666533 13519829 := bbase (se 7 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 13519829 = 316871) (by norm_num)
theorem B2501597 : Blo 1666533 2501597 := bbase (se 3 (by rfl) ⟨469049, by rfl⟩ : syracuseStep 2501597 = 938099) (by norm_num)
theorem B2501621 : Blo 1666533 2501621 := bbase (se 5 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 2501621 = 234527) (by norm_num)
theorem B2501645 : Blo 1666533 2501645 := bbase (se 3 (by rfl) ⟨469058, by rfl⟩ : syracuseStep 2501645 = 938117) (by norm_num)
theorem B4516901 : Blo 1666533 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B2501669 : Blo 1666533 2501669 := bbase (se 4 (by rfl) ⟨234531, by rfl⟩ : syracuseStep 2501669 = 469063) (by norm_num)
theorem B1690669 : Blo 1666533 1690669 := bbase (se 3 (by rfl) ⟨317000, by rfl⟩ : syracuseStep 1690669 = 634001) (by norm_num)
theorem B2812981 : Blo 1666533 2812981 := bbase (se 5 (by rfl) ⟨131858, by rfl⟩ : syracuseStep 2812981 = 263717) (by norm_num)
theorem B2501693 : Blo 1666533 2501693 := bbase (se 3 (by rfl) ⟨469067, by rfl⟩ : syracuseStep 2501693 = 938135) (by norm_num)
theorem B2501717 : Blo 1666533 2501717 := bbase (se 8 (by rfl) ⟨14658, by rfl⟩ : syracuseStep 2501717 = 29317) (by norm_num)
theorem B2501741 : Blo 1666533 2501741 := bbase (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) (by norm_num)
theorem B4279405 : Blo 1666533 4279405 := bbase (se 3 (by rfl) ⟨802388, by rfl⟩ : syracuseStep 4279405 = 1604777) (by norm_num)
theorem B6089861 : Blo 1666533 6089861 := bbase (se 4 (by rfl) ⟨570924, by rfl⟩ : syracuseStep 6089861 = 1141849) (by norm_num)
theorem B2501765 : Blo 1666533 2501765 := bbase (se 4 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 2501765 = 469081) (by norm_num)
theorem B2813069 : Blo 1666533 2813069 := bbase (se 3 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 2813069 = 1054901) (by norm_num)
theorem B2501789 : Blo 1666533 2501789 := bbase (se 3 (by rfl) ⟨469085, by rfl⟩ : syracuseStep 2501789 = 938171) (by norm_num)
theorem B2501813 : Blo 1666533 2501813 := bbase (se 5 (by rfl) ⟨117272, by rfl⟩ : syracuseStep 2501813 = 234545) (by norm_num)
theorem B2501837 : Blo 1666533 2501837 := bbase (se 3 (by rfl) ⟨469094, by rfl⟩ : syracuseStep 2501837 = 938189) (by norm_num)
theorem B4222165 : Blo 1666533 4222165 := bbase (se 7 (by rfl) ⟨49478, by rfl⟩ : syracuseStep 4222165 = 98957) (by norm_num)
theorem B2501861 : Blo 1666533 2501861 := bbase (se 4 (by rfl) ⟨234549, by rfl⟩ : syracuseStep 2501861 = 469099) (by norm_num)
theorem B2002169 : Blo 1666533 2002169 := bbase (se 2 (by rfl) ⟨750813, by rfl⟩ : syracuseStep 2002169 = 1501627) (by norm_num)
theorem B2501885 : Blo 1666533 2501885 := bbase (se 3 (by rfl) ⟨469103, by rfl⟩ : syracuseStep 2501885 = 938207) (by norm_num)
theorem B2813197 : Blo 1666533 2813197 := bbase (se 3 (by rfl) ⟨527474, by rfl⟩ : syracuseStep 2813197 = 1054949) (by norm_num)
theorem B2501909 : Blo 1666533 2501909 := bbase (se 6 (by rfl) ⟨58638, by rfl⟩ : syracuseStep 2501909 = 117277) (by norm_num)
theorem B2501933 : Blo 1666533 2501933 := bbase (se 3 (by rfl) ⟨469112, by rfl⟩ : syracuseStep 2501933 = 938225) (by norm_num)
theorem B3165493 : Blo 1666533 3165493 := bbase (se 5 (by rfl) ⟨148382, by rfl⟩ : syracuseStep 3165493 = 296765) (by norm_num)
theorem B2501957 : Blo 1666533 2501957 := bbase (se 4 (by rfl) ⟨234558, by rfl⟩ : syracuseStep 2501957 = 469117) (by norm_num)
theorem B2501981 : Blo 1666533 2501981 := bbase (se 3 (by rfl) ⟨469121, by rfl⟩ : syracuseStep 2501981 = 938243) (by norm_num)
theorem B2813285 : Blo 1666533 2813285 := bbase (se 4 (by rfl) ⟨263745, by rfl⟩ : syracuseStep 2813285 = 527491) (by norm_num)
theorem B2502005 : Blo 1666533 2502005 := bbase (se 5 (by rfl) ⟨117281, by rfl⟩ : syracuseStep 2502005 = 234563) (by norm_num)
theorem B6761861 : Blo 1666533 6761861 := bbase (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) (by norm_num)
theorem B2502029 : Blo 1666533 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B1781137 : Blo 1666533 1781137 := bbase (se 2 (by rfl) ⟨667926, by rfl⟩ : syracuseStep 1781137 = 1335853) (by norm_num)
theorem B9498005 : Blo 1666533 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B2002333 : Blo 1666533 2002333 := bbase (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) (by norm_num)
theorem B2002361 : Blo 1666533 2002361 := bbase (se 2 (by rfl) ⟨750885, by rfl⟩ : syracuseStep 2002361 = 1501771) (by norm_num)
theorem B3165637 : Blo 1666533 3165637 := bbase (se 4 (by rfl) ⟨296778, by rfl⟩ : syracuseStep 3165637 = 593557) (by norm_num)
theorem B1781209 : Blo 1666533 1781209 := bbase (se 2 (by rfl) ⟨667953, by rfl⟩ : syracuseStep 1781209 = 1335907) (by norm_num)
theorem B4746725 : Blo 1666533 4746725 := bbase (se 4 (by rfl) ⟨445005, by rfl⟩ : syracuseStep 4746725 = 890011) (by norm_num)
theorem B2813413 : Blo 1666533 2813413 := bbase (se 4 (by rfl) ⟨263757, by rfl⟩ : syracuseStep 2813413 = 527515) (by norm_num)
theorem B8441333 : Blo 1666533 8441333 := bbase (se 5 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 8441333 = 791375) (by norm_num)
theorem B2002477 : Blo 1666533 2002477 := bbase (se 3 (by rfl) ⟨375464, by rfl⟩ : syracuseStep 2002477 = 750929) (by norm_num)
theorem B2813501 : Blo 1666533 2813501 := bbase (se 3 (by rfl) ⟨527531, by rfl⟩ : syracuseStep 2813501 = 1055063) (by norm_num)
theorem B2534981 : Blo 1666533 2534981 := bbase (se 4 (by rfl) ⟨237654, by rfl⟩ : syracuseStep 2534981 = 475309) (by norm_num)
theorem B3165797 : Blo 1666533 3165797 := bbase (se 4 (by rfl) ⟨296793, by rfl⟩ : syracuseStep 3165797 = 593587) (by norm_num)
theorem B2002573 : Blo 1666533 2002573 := bbase (se 3 (by rfl) ⟨375482, by rfl⟩ : syracuseStep 2002573 = 750965) (by norm_num)
theorem B2813629 : Blo 1666533 2813629 := bbase (se 3 (by rfl) ⟨527555, by rfl⟩ : syracuseStep 2813629 = 1055111) (by norm_num)
theorem B3165941 : Blo 1666533 3165941 := bbase (se 5 (by rfl) ⟨148403, by rfl⟩ : syracuseStep 3165941 = 296807) (by norm_num)
theorem B2813717 : Blo 1666533 2813717 := bbase (se 6 (by rfl) ⟨65946, by rfl⟩ : syracuseStep 2813717 = 131893) (by norm_num)
theorem B4747157 : Blo 1666533 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B2813845 : Blo 1666533 2813845 := bbase (se 6 (by rfl) ⟨65949, by rfl⟩ : syracuseStep 2813845 = 131899) (by norm_num)
theorem B2109341 : Blo 1666533 2109341 := bbase (se 3 (by rfl) ⟨395501, by rfl⟩ : syracuseStep 2109341 = 791003) (by norm_num)
theorem B2109397 : Blo 1666533 2109397 := bbase (se 7 (by rfl) ⟨24719, by rfl⟩ : syracuseStep 2109397 = 49439) (by norm_num)
theorem B2813933 : Blo 1666533 2813933 := bbase (se 3 (by rfl) ⟨527612, by rfl⟩ : syracuseStep 2813933 = 1055225) (by norm_num)
theorem B3166229 : Blo 1666533 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B2109493 : Blo 1666533 2109493 := bbase (se 5 (by rfl) ⟨98882, by rfl⟩ : syracuseStep 2109493 = 197765) (by norm_num)
theorem B2003053 : Blo 1666533 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B2814061 : Blo 1666533 2814061 := bbase (se 3 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 2814061 = 1055273) (by norm_num)
theorem B3559565 : Blo 1666533 3559565 := bbase (se 3 (by rfl) ⟨667418, by rfl⟩ : syracuseStep 3559565 = 1334837) (by norm_num)
theorem B3166381 : Blo 1666533 3166381 := bbase (se 3 (by rfl) ⟨593696, by rfl⟩ : syracuseStep 3166381 = 1187393) (by norm_num)
theorem B2814149 : Blo 1666533 2814149 := bbase (se 4 (by rfl) ⟨263826, by rfl⟩ : syracuseStep 2814149 = 527653) (by norm_num)
theorem B18993365 : Blo 1666533 18993365 := bbase (se 7 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 18993365 = 445157) (by norm_num)
theorem B2109665 : Blo 1666533 2109665 := bbase (se 2 (by rfl) ⟨791124, by rfl⟩ : syracuseStep 2109665 = 1582249) (by norm_num)
theorem B2109721 : Blo 1666533 2109721 := bbase (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) (by norm_num)
theorem B2814277 : Blo 1666533 2814277 := bbase (se 4 (by rfl) ⟨263838, by rfl⟩ : syracuseStep 2814277 = 527677) (by norm_num)
theorem B2109817 : Blo 1666533 2109817 := bbase (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) (by norm_num)
theorem B2814365 : Blo 1666533 2814365 := bbase (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) (by norm_num)
theorem B8556997 : Blo 1666533 8556997 := bbase (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) (by norm_num)
theorem B5706197 : Blo 1666533 5706197 := bbase (se 7 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 5706197 = 133739) (by norm_num)
theorem B2814493 : Blo 1666533 2814493 := bbase (se 3 (by rfl) ⟨527717, by rfl⟩ : syracuseStep 2814493 = 1055435) (by norm_num)
theorem B2109989 : Blo 1666533 2109989 := bbase (se 4 (by rfl) ⟨197811, by rfl⟩ : syracuseStep 2109989 = 395623) (by norm_num)
theorem B3379781 : Blo 1666533 3379781 := bbase (se 4 (by rfl) ⟨316854, by rfl⟩ : syracuseStep 3379781 = 633709) (by norm_num)
theorem B2110045 : Blo 1666533 2110045 := bbase (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) (by norm_num)
theorem B2814581 : Blo 1666533 2814581 := bbase (se 5 (by rfl) ⟨131933, by rfl⟩ : syracuseStep 2814581 = 263867) (by norm_num)
theorem B4747909 : Blo 1666533 4747909 := bbase (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) (by norm_num)
theorem B2110141 : Blo 1666533 2110141 := bbase (se 3 (by rfl) ⟨395651, by rfl⟩ : syracuseStep 2110141 = 791303) (by norm_num)
theorem B2814709 : Blo 1666533 2814709 := bbase (se 5 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 2814709 = 263879) (by norm_num)
theorem B8442629 : Blo 1666533 8442629 := bbase (se 4 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 8442629 = 1582993) (by norm_num)
theorem B3961669 : Blo 1666533 3961669 := bbase (se 4 (by rfl) ⟨371406, by rfl⟩ : syracuseStep 3961669 = 742813) (by norm_num)
theorem B2814797 : Blo 1666533 2814797 := bbase (se 3 (by rfl) ⟨527774, by rfl⟩ : syracuseStep 2814797 = 1055549) (by norm_num)
theorem B2110313 : Blo 1666533 2110313 := bbase (se 2 (by rfl) ⟨791367, by rfl⟩ : syracuseStep 2110313 = 1582735) (by norm_num)
theorem B5624693 : Blo 1666533 5624693 := bbase (se 5 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 5624693 = 527315) (by norm_num)
theorem B2110369 : Blo 1666533 2110369 := bbase (se 2 (by rfl) ⟨791388, by rfl⟩ : syracuseStep 2110369 = 1582777) (by norm_num)
theorem B3609533 : Blo 1666533 3609533 := bbase (se 3 (by rfl) ⟨676787, by rfl⟩ : syracuseStep 3609533 = 1353575) (by norm_num)
theorem B6329285 : Blo 1666533 6329285 := bbase (se 4 (by rfl) ⟨593370, by rfl⟩ : syracuseStep 6329285 = 1186741) (by norm_num)
theorem B3560429 : Blo 1666533 3560429 := bbase (se 3 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 3560429 = 1335161) (by norm_num)
theorem B2110465 : Blo 1666533 2110465 := bbase (se 2 (by rfl) ⟨791424, by rfl⟩ : syracuseStep 2110465 = 1582849) (by norm_num)
theorem B7918597 : Blo 1666533 7918597 := bbase (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) (by norm_num)
theorem B14242837 : Blo 1666533 14242837 := bbase (se 6 (by rfl) ⟨333816, by rfl⟩ : syracuseStep 14242837 = 667633) (by norm_num)
theorem B5067893 : Blo 1666533 5067893 := bbase (se 5 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 5067893 = 475115) (by norm_num)
theorem B3560573 : Blo 1666533 3560573 := bbase (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) (by norm_num)
theorem B2110637 : Blo 1666533 2110637 := bbase (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) (by norm_num)
theorem B6329573 : Blo 1666533 6329573 := bbase (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) (by norm_num)
theorem B2110693 : Blo 1666533 2110693 := bbase (se 4 (by rfl) ⟨197877, by rfl⟩ : syracuseStep 2110693 = 395755) (by norm_num)
theorem B2372861 : Blo 1666533 2372861 := bbase (se 3 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 2372861 = 889823) (by norm_num)
theorem B5625125 : Blo 1666533 5625125 := bbase (se 4 (by rfl) ⟨527355, by rfl⟩ : syracuseStep 5625125 = 1054711) (by norm_num)
theorem B7607605 : Blo 1666533 7607605 := bbase (se 5 (by rfl) ⟨356606, by rfl⟩ : syracuseStep 7607605 = 713213) (by norm_num)
theorem B2110789 : Blo 1666533 2110789 := bbase (se 4 (by rfl) ⟨197886, by rfl⟩ : syracuseStep 2110789 = 395773) (by norm_num)
theorem B2110961 : Blo 1666533 2110961 := bbase (se 2 (by rfl) ⟨791610, by rfl⟩ : syracuseStep 2110961 = 1583221) (by norm_num)
theorem B2111017 : Blo 1666533 2111017 := bbase (se 2 (by rfl) ⟨791631, by rfl⟩ : syracuseStep 2111017 = 1583263) (by norm_num)
theorem B5625557 : Blo 1666533 5625557 := bbase (se 7 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 5625557 = 131849) (by norm_num)
theorem B3561317 : Blo 1666533 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B3749741 : Blo 1666533 3749741 := bbase (se 3 (by rfl) ⟨703076, by rfl⟩ : syracuseStep 3749741 = 1406153) (by norm_num)
theorem B3004285 : Blo 1666533 3004285 := bbase (se 3 (by rfl) ⟨563303, by rfl⟩ : syracuseStep 3004285 = 1126607) (by norm_num)
theorem B3749813 : Blo 1666533 3749813 := bbase (se 5 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 3749813 = 351545) (by norm_num)
theorem B2406373 : Blo 1666533 2406373 := bbase (se 4 (by rfl) ⟨225597, by rfl⟩ : syracuseStep 2406373 = 451195) (by norm_num)
theorem B3749885 : Blo 1666533 3749885 := bbase (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) (by norm_num)
theorem B8443925 : Blo 1666533 8443925 := bbase (se 6 (by rfl) ⟨197904, by rfl⟩ : syracuseStep 8443925 = 395809) (by norm_num)
theorem B3749957 : Blo 1666533 3749957 := bbase (se 4 (by rfl) ⟨351558, by rfl⟩ : syracuseStep 3749957 = 703117) (by norm_num)
theorem B5625989 : Blo 1666533 5625989 := bbase (se 4 (by rfl) ⟨527436, by rfl⟩ : syracuseStep 5625989 = 1054873) (by norm_num)
theorem B3750029 : Blo 1666533 3750029 := bbase (se 3 (by rfl) ⟨703130, by rfl⟩ : syracuseStep 3750029 = 1406261) (by norm_num)
theorem B3750101 : Blo 1666533 3750101 := bbase (se 7 (by rfl) ⟨43946, by rfl⟩ : syracuseStep 3750101 = 87893) (by norm_num)
theorem B66771157 : Blo 1666533 66771157 := bbase (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) (by norm_num)
theorem B3750173 : Blo 1666533 3750173 := bbase (se 3 (by rfl) ⟨703157, by rfl⟩ : syracuseStep 3750173 = 1406315) (by norm_num)
theorem B2283869 : Blo 1666533 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B3750245 : Blo 1666533 3750245 := bbase (se 4 (by rfl) ⟨351585, by rfl⟩ : syracuseStep 3750245 = 703171) (by norm_num)
theorem B6330757 : Blo 1666533 6330757 := bbase (se 4 (by rfl) ⟨593508, by rfl⟩ : syracuseStep 6330757 = 1187017) (by norm_num)
theorem B6945173 : Blo 1666533 6945173 := bbase (se 6 (by rfl) ⟨162777, by rfl⟩ : syracuseStep 6945173 = 325555) (by norm_num)
theorem B3750317 : Blo 1666533 3750317 := bbase (se 3 (by rfl) ⟨703184, by rfl⟩ : syracuseStep 3750317 = 1406369) (by norm_num)
theorem B8010197 : Blo 1666533 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B3750389 : Blo 1666533 3750389 := bbase (se 5 (by rfl) ⟨175799, by rfl⟩ : syracuseStep 3750389 = 351599) (by norm_num)
theorem B5626421 : Blo 1666533 5626421 := bbase (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) (by norm_num)
theorem B3750461 : Blo 1666533 3750461 := bbase (se 3 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 3750461 = 1406423) (by norm_num)
theorem B3562069 : Blo 1666533 3562069 := bbase (se 8 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 3562069 = 41743) (by norm_num)
theorem B3750533 : Blo 1666533 3750533 := bbase (se 4 (by rfl) ⟨351612, by rfl⟩ : syracuseStep 3750533 = 703225) (by norm_num)
theorem B2374285 : Blo 1666533 2374285 := bbase (se 3 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 2374285 = 890357) (by norm_num)
theorem B3005093 : Blo 1666533 3005093 := bbase (se 4 (by rfl) ⟨281727, by rfl⟩ : syracuseStep 3005093 = 563455) (by norm_num)
theorem B6331061 : Blo 1666533 6331061 := bbase (se 5 (by rfl) ⟨296768, by rfl⟩ : syracuseStep 6331061 = 593537) (by norm_num)
theorem B3750605 : Blo 1666533 3750605 := bbase (se 3 (by rfl) ⟨703238, by rfl⟩ : syracuseStep 3750605 = 1406477) (by norm_num)
theorem B3562213 : Blo 1666533 3562213 := bbase (se 4 (by rfl) ⟨333957, by rfl⟩ : syracuseStep 3562213 = 667915) (by norm_num)
theorem B3750677 : Blo 1666533 3750677 := bbase (se 6 (by rfl) ⟨87906, by rfl⟩ : syracuseStep 3750677 = 175813) (by norm_num)
theorem B4004645 : Blo 1666533 4004645 := bbase (se 4 (by rfl) ⟨375435, by rfl⟩ : syracuseStep 4004645 = 750871) (by norm_num)
theorem B3750749 : Blo 1666533 3750749 := bbase (se 3 (by rfl) ⟨703265, by rfl⟩ : syracuseStep 3750749 = 1406531) (by norm_num)
theorem B12663701 : Blo 1666533 12663701 := bbase (se 6 (by rfl) ⟨296805, by rfl⟩ : syracuseStep 12663701 = 593611) (by norm_num)
theorem B3750821 : Blo 1666533 3750821 := bbase (se 4 (by rfl) ⟨351639, by rfl⟩ : syracuseStep 3750821 = 703279) (by norm_num)
theorem B1874857 : Blo 1666533 1874857 := bbase (se 2 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 1874857 = 1406143) (by norm_num)
theorem B1874893 : Blo 1666533 1874893 := bbase (se 3 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 1874893 = 703085) (by norm_num)
theorem B14244821 : Blo 1666533 14244821 := bbase (se 7 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 14244821 = 333863) (by norm_num)
theorem B5626853 : Blo 1666533 5626853 := bbase (se 4 (by rfl) ⟨527517, by rfl⟩ : syracuseStep 5626853 = 1055035) (by norm_num)
theorem B3750893 : Blo 1666533 3750893 := bbase (se 3 (by rfl) ⟨703292, by rfl⟩ : syracuseStep 3750893 = 1406585) (by norm_num)
theorem B1874929 : Blo 1666533 1874929 := bbase (se 2 (by rfl) ⟨703098, by rfl⟩ : syracuseStep 1874929 = 1406197) (by norm_num)
theorem B1874965 : Blo 1666533 1874965 := bbase (se 6 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 1874965 = 87889) (by norm_num)
theorem B3750965 : Blo 1666533 3750965 := bbase (se 5 (by rfl) ⟨175826, by rfl⟩ : syracuseStep 3750965 = 351653) (by norm_num)
theorem B1875001 : Blo 1666533 1875001 := bbase (se 2 (by rfl) ⟨703125, by rfl⟩ : syracuseStep 1875001 = 1406251) (by norm_num)
theorem B24042581 : Blo 1666533 24042581 := bbase (se 8 (by rfl) ⟨140874, by rfl⟩ : syracuseStep 24042581 = 281749) (by norm_num)
theorem B1875037 : Blo 1666533 1875037 := bbase (se 3 (by rfl) ⟨351569, by rfl⟩ : syracuseStep 1875037 = 703139) (by norm_num)
theorem B3751037 : Blo 1666533 3751037 := bbase (se 3 (by rfl) ⟨703319, by rfl⟩ : syracuseStep 3751037 = 1406639) (by norm_num)
theorem B1875073 : Blo 1666533 1875073 := bbase (se 2 (by rfl) ⟨703152, by rfl⟩ : syracuseStep 1875073 = 1406305) (by norm_num)
theorem B1875109 : Blo 1666533 1875109 := bbase (se 4 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 1875109 = 351583) (by norm_num)
theorem B3751109 : Blo 1666533 3751109 := bbase (se 4 (by rfl) ⟨351666, by rfl⟩ : syracuseStep 3751109 = 703333) (by norm_num)
theorem B1875145 : Blo 1666533 1875145 := bbase (se 2 (by rfl) ⟨703179, by rfl⟩ : syracuseStep 1875145 = 1406359) (by norm_num)
theorem B2374877 : Blo 1666533 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B1875181 : Blo 1666533 1875181 := bbase (se 3 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 1875181 = 703193) (by norm_num)
theorem B3751181 : Blo 1666533 3751181 := bbase (se 3 (by rfl) ⟨703346, by rfl⟩ : syracuseStep 3751181 = 1406693) (by norm_num)
theorem B1875217 : Blo 1666533 1875217 := bbase (se 2 (by rfl) ⟨703206, by rfl⟩ : syracuseStep 1875217 = 1406413) (by norm_num)
theorem B2374957 : Blo 1666533 2374957 := bbase (se 3 (by rfl) ⟨445304, by rfl⟩ : syracuseStep 2374957 = 890609) (by norm_num)
theorem B12655925 : Blo 1666533 12655925 := bbase (se 5 (by rfl) ⟨593246, by rfl⟩ : syracuseStep 12655925 = 1186493) (by norm_num)
theorem B1875253 : Blo 1666533 1875253 := bbase (se 5 (by rfl) ⟨87902, by rfl⟩ : syracuseStep 1875253 = 175805) (by norm_num)
theorem B3751253 : Blo 1666533 3751253 := bbase (se 11 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 3751253 = 5495) (by norm_num)
theorem B1875289 : Blo 1666533 1875289 := bbase (se 2 (by rfl) ⟨703233, by rfl⟩ : syracuseStep 1875289 = 1406467) (by norm_num)
theorem B1875325 : Blo 1666533 1875325 := bbase (se 3 (by rfl) ⟨351623, by rfl⟩ : syracuseStep 1875325 = 703247) (by norm_num)
theorem B2030977 : Blo 1666533 2030977 := bbase (se 2 (by rfl) ⟨761616, by rfl⟩ : syracuseStep 2030977 = 1523233) (by norm_num)
theorem B5627285 : Blo 1666533 5627285 := bbase (se 6 (by rfl) ⟨131889, by rfl⟩ : syracuseStep 5627285 = 263779) (by norm_num)
theorem B3751325 : Blo 1666533 3751325 := bbase (se 3 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 3751325 = 1406747) (by norm_num)
theorem B1875361 : Blo 1666533 1875361 := bbase (se 2 (by rfl) ⟨703260, by rfl⟩ : syracuseStep 1875361 = 1406521) (by norm_num)
theorem B1875397 : Blo 1666533 1875397 := bbase (se 4 (by rfl) ⟨175818, by rfl⟩ : syracuseStep 1875397 = 351637) (by norm_num)
theorem B16031189 : Blo 1666533 16031189 := bbase (se 7 (by rfl) ⟨187865, by rfl⟩ : syracuseStep 16031189 = 375731) (by norm_num)
theorem B3751397 : Blo 1666533 3751397 := bbase (se 4 (by rfl) ⟨351693, by rfl⟩ : syracuseStep 3751397 = 703387) (by norm_num)
theorem B1875433 : Blo 1666533 1875433 := bbase (se 2 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 1875433 = 1406575) (by norm_num)
theorem B1875469 : Blo 1666533 1875469 := bbase (se 3 (by rfl) ⟨351650, by rfl⟩ : syracuseStep 1875469 = 703301) (by norm_num)
theorem B3751469 : Blo 1666533 3751469 := bbase (se 3 (by rfl) ⟨703400, by rfl⟩ : syracuseStep 3751469 = 1406801) (by norm_num)
theorem B1875505 : Blo 1666533 1875505 := bbase (se 2 (by rfl) ⟨703314, by rfl⟩ : syracuseStep 1875505 = 1406629) (by norm_num)
theorem B15416885 : Blo 1666533 15416885 := bbase (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) (by norm_num)
theorem B5340757 : Blo 1666533 5340757 := bbase (se 8 (by rfl) ⟨31293, by rfl⟩ : syracuseStep 5340757 = 62587) (by norm_num)
theorem B1875541 : Blo 1666533 1875541 := bbase (se 8 (by rfl) ⟨10989, by rfl⟩ : syracuseStep 1875541 = 21979) (by norm_num)
theorem B3751541 : Blo 1666533 3751541 := bbase (se 5 (by rfl) ⟨175853, by rfl⟩ : syracuseStep 3751541 = 351707) (by norm_num)
theorem B1875577 : Blo 1666533 1875577 := bbase (se 2 (by rfl) ⟨703341, by rfl⟩ : syracuseStep 1875577 = 1406683) (by norm_num)
theorem B1875613 : Blo 1666533 1875613 := bbase (se 3 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 1875613 = 703355) (by norm_num)
theorem B3751613 : Blo 1666533 3751613 := bbase (se 3 (by rfl) ⟨703427, by rfl⟩ : syracuseStep 3751613 = 1406855) (by norm_num)
theorem B1875649 : Blo 1666533 1875649 := bbase (se 2 (by rfl) ⟨703368, by rfl⟩ : syracuseStep 1875649 = 1406737) (by norm_num)
theorem B8437445 : Blo 1666533 8437445 := bbase (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) (by norm_num)
theorem B4218581 : Blo 1666533 4218581 := bbase (se 7 (by rfl) ⟨49436, by rfl⟩ : syracuseStep 4218581 = 98873) (by norm_num)
theorem B1875685 : Blo 1666533 1875685 := bbase (se 4 (by rfl) ⟨175845, by rfl⟩ : syracuseStep 1875685 = 351691) (by norm_num)
theorem B2252549 : Blo 1666533 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B3751685 : Blo 1666533 3751685 := bbase (se 4 (by rfl) ⟨351720, by rfl⟩ : syracuseStep 3751685 = 703441) (by norm_num)
theorem B1875721 : Blo 1666533 1875721 := bbase (se 2 (by rfl) ⟨703395, by rfl⟩ : syracuseStep 1875721 = 1406791) (by norm_num)
theorem B1875757 : Blo 1666533 1875757 := bbase (se 3 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 1875757 = 703409) (by norm_num)
theorem B5627717 : Blo 1666533 5627717 := bbase (se 4 (by rfl) ⟨527598, by rfl⟩ : syracuseStep 5627717 = 1055197) (by norm_num)
theorem B3751757 : Blo 1666533 3751757 := bbase (se 3 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 3751757 = 1406909) (by norm_num)
theorem B1875793 : Blo 1666533 1875793 := bbase (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) (by norm_num)
theorem B32481109 : Blo 1666533 32481109 := bbase (se 9 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 32481109 = 190319) (by norm_num)
theorem B1875829 : Blo 1666533 1875829 := bbase (se 5 (by rfl) ⟨87929, by rfl⟩ : syracuseStep 1875829 = 175859) (by norm_num)
theorem B4276109 : Blo 1666533 4276109 := bbase (se 3 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 4276109 = 1603541) (by norm_num)
theorem B3751829 : Blo 1666533 3751829 := bbase (se 6 (by rfl) ⟨87933, by rfl⟩ : syracuseStep 3751829 = 175867) (by norm_num)
theorem B21372821 : Blo 1666533 21372821 := bbase (se 6 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 21372821 = 1001851) (by norm_num)
theorem B1875865 : Blo 1666533 1875865 := bbase (se 2 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 1875865 = 1406899) (by norm_num)
theorem B1875901 : Blo 1666533 1875901 := bbase (se 3 (by rfl) ⟨351731, by rfl⟩ : syracuseStep 1875901 = 703463) (by norm_num)
theorem B3751901 : Blo 1666533 3751901 := bbase (se 3 (by rfl) ⟨703481, by rfl⟩ : syracuseStep 3751901 = 1406963) (by norm_num)
theorem B1875937 : Blo 1666533 1875937 := bbase (se 2 (by rfl) ⟨703476, by rfl⟩ : syracuseStep 1875937 = 1406953) (by norm_num)
theorem B1876099 : Blo 1666533 1876099 := bstep (se 1 (by rfl) ⟨1407074, by rfl⟩ : syracuseStep 1876099 = 2814149) B2814149
theorem B2670737 : Blo 1666533 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B3752081 : Blo 1666533 3752081 := bstep (se 2 (by rfl) ⟨1407030, by rfl⟩ : syracuseStep 3752081 = 2814061) B2814061
theorem B3752099 : Blo 1666533 3752099 := bstep (se 1 (by rfl) ⟨2814074, by rfl⟩ : syracuseStep 3752099 = 5628149) B5628149
theorem B1876243 : Blo 1666533 1876243 := bstep (se 1 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 1876243 = 2814365) B2814365
theorem B11559217 : Blo 1666533 11559217 := bstep (se 2 (by rfl) ⟨4334706, by rfl⟩ : syracuseStep 11559217 = 8669413) B8669413
theorem B8438093 : Blo 1666533 8438093 := bstep (se 3 (by rfl) ⟨1582142, by rfl⟩ : syracuseStep 8438093 = 3164285) B3164285
theorem B4219249 : Blo 1666533 4219249 := bstep (se 2 (by rfl) ⟨1582218, by rfl⟩ : syracuseStep 4219249 = 3164437) B3164437
theorem B2253187 : Blo 1666533 2253187 := bstep (se 1 (by rfl) ⟨1689890, by rfl⟩ : syracuseStep 2253187 = 3379781) B3379781
theorem B1876387 : Blo 1666533 1876387 := bstep (se 1 (by rfl) ⟨1407290, by rfl⟩ : syracuseStep 1876387 = 2814581) B2814581
theorem B3752369 : Blo 1666533 3752369 := bstep (se 2 (by rfl) ⟨1407138, by rfl⟩ : syracuseStep 3752369 = 2814277) B2814277
theorem B3752387 : Blo 1666533 3752387 := bstep (se 1 (by rfl) ⟨2814290, by rfl⟩ : syracuseStep 3752387 = 5628581) B5628581
theorem B5628365 : Blo 1666533 5628365 := bstep (se 3 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 5628365 = 2110637) B2110637
theorem B5628419 : Blo 1666533 5628419 := bstep (se 1 (by rfl) ⟨4221314, by rfl⟩ : syracuseStep 5628419 = 8442629) B8442629
theorem B9495089 : Blo 1666533 9495089 := bstep (se 2 (by rfl) ⟨3560658, by rfl⟩ : syracuseStep 9495089 = 7121317) B7121317
theorem B1876531 : Blo 1666533 1876531 := bstep (se 1 (by rfl) ⟨1407398, by rfl⟩ : syracuseStep 1876531 = 2814797) B2814797
theorem B6333005 : Blo 1666533 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B4219523 : Blo 1666533 4219523 := bstep (se 1 (by rfl) ⟨3164642, by rfl⟩ : syracuseStep 4219523 = 6329285) B6329285
theorem B3752657 : Blo 1666533 3752657 := bstep (se 2 (by rfl) ⟨1407246, by rfl⟩ : syracuseStep 3752657 = 2814493) B2814493
theorem B3752675 : Blo 1666533 3752675 := bstep (se 1 (by rfl) ⟨2814506, by rfl⟩ : syracuseStep 3752675 = 5629013) B5629013
theorem B5628689 : Blo 1666533 5628689 := bstep (se 2 (by rfl) ⟨2110758, by rfl⟩ : syracuseStep 5628689 = 4221517) B4221517
theorem B5341987 : Blo 1666533 5341987 := bstep (se 1 (by rfl) ⟨4006490, by rfl⟩ : syracuseStep 5341987 = 8012981) B8012981
theorem B4219715 : Blo 1666533 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B3752945 : Blo 1666533 3752945 := bstep (se 2 (by rfl) ⟨1407354, by rfl⟩ : syracuseStep 3752945 = 2814709) B2814709
theorem B3752963 : Blo 1666533 3752963 := bstep (se 1 (by rfl) ⟨2814722, by rfl⟩ : syracuseStep 3752963 = 5629445) B5629445
theorem B2499809 : Blo 1666533 2499809 := bstep (se 2 (by rfl) ⟨937428, by rfl⟩ : syracuseStep 2499809 = 1874857) B1874857
theorem B5342449 : Blo 1666533 5342449 := bstep (se 2 (by rfl) ⟨2003418, by rfl⟩ : syracuseStep 5342449 = 4006837) B4006837
theorem B2499827 : Blo 1666533 2499827 := bstep (se 1 (by rfl) ⟨1874870, by rfl⟩ : syracuseStep 2499827 = 3749741) B3749741
theorem B2499857 : Blo 1666533 2499857 := bstep (se 2 (by rfl) ⟨937446, by rfl⟩ : syracuseStep 2499857 = 1874893) B1874893
theorem B2499875 : Blo 1666533 2499875 := bstep (se 1 (by rfl) ⟨1874906, by rfl⟩ : syracuseStep 2499875 = 3749813) B3749813
theorem B5629229 : Blo 1666533 5629229 := bstep (se 3 (by rfl) ⟨1055480, by rfl⟩ : syracuseStep 5629229 = 2110961) B2110961
theorem B2499905 : Blo 1666533 2499905 := bstep (se 2 (by rfl) ⟨937464, by rfl⟩ : syracuseStep 2499905 = 1874929) B1874929
theorem B4506947 : Blo 1666533 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B2499923 : Blo 1666533 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B5629283 : Blo 1666533 5629283 := bstep (se 1 (by rfl) ⟨4221962, by rfl⟩ : syracuseStep 5629283 = 8443925) B8443925
theorem B2499953 : Blo 1666533 2499953 := bstep (se 2 (by rfl) ⟨937482, by rfl⟩ : syracuseStep 2499953 = 1874965) B1874965
theorem B18990449 : Blo 1666533 18990449 := bstep (se 2 (by rfl) ⟨7121418, by rfl⟩ : syracuseStep 18990449 = 14242837) B14242837
theorem B2499971 : Blo 1666533 2499971 := bstep (se 1 (by rfl) ⟨1874978, by rfl⟩ : syracuseStep 2499971 = 3749957) B3749957
theorem B2254225 : Blo 1666533 2254225 := bstep (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) B1690669
theorem B2500001 : Blo 1666533 2500001 := bstep (se 2 (by rfl) ⟨937500, by rfl⟩ : syracuseStep 2500001 = 1875001) B1875001
theorem B2500019 : Blo 1666533 2500019 := bstep (se 1 (by rfl) ⟨1875014, by rfl⟩ : syracuseStep 2500019 = 3750029) B3750029
theorem B10143181 : Blo 1666533 10143181 := bstep (se 3 (by rfl) ⟨1901846, by rfl⟩ : syracuseStep 10143181 = 3803693) B3803693
theorem B2500049 : Blo 1666533 2500049 := bstep (se 2 (by rfl) ⟨937518, by rfl⟩ : syracuseStep 2500049 = 1875037) B1875037
theorem B2500067 : Blo 1666533 2500067 := bstep (se 1 (by rfl) ⟨1875050, by rfl⟩ : syracuseStep 2500067 = 3750101) B3750101
theorem B2500097 : Blo 1666533 2500097 := bstep (se 2 (by rfl) ⟨937536, by rfl⟩ : syracuseStep 2500097 = 1875073) B1875073
theorem B6759949 : Blo 1666533 6759949 := bstep (se 3 (by rfl) ⟨1267490, by rfl⟩ : syracuseStep 6759949 = 2534981) B2534981
theorem B2500115 : Blo 1666533 2500115 := bstep (se 1 (by rfl) ⟨1875086, by rfl⟩ : syracuseStep 2500115 = 3750173) B3750173
theorem B2500145 : Blo 1666533 2500145 := bstep (se 2 (by rfl) ⟨937554, by rfl⟩ : syracuseStep 2500145 = 1875109) B1875109
theorem B2500163 : Blo 1666533 2500163 := bstep (se 1 (by rfl) ⟨1875122, by rfl⟩ : syracuseStep 2500163 = 3750245) B3750245
theorem B2500193 : Blo 1666533 2500193 := bstep (se 2 (by rfl) ⟨937572, by rfl⟩ : syracuseStep 2500193 = 1875145) B1875145
theorem B4630115 : Blo 1666533 4630115 := bstep (se 1 (by rfl) ⟨3472586, by rfl⟩ : syracuseStep 4630115 = 6945173) B6945173
theorem B5629553 : Blo 1666533 5629553 := bstep (se 2 (by rfl) ⟨2111082, by rfl⟩ : syracuseStep 5629553 = 4222165) B4222165
theorem B2500211 : Blo 1666533 2500211 := bstep (se 1 (by rfl) ⟨1875158, by rfl⟩ : syracuseStep 2500211 = 3750317) B3750317
theorem B2500241 : Blo 1666533 2500241 := bstep (se 2 (by rfl) ⟨937590, by rfl⟩ : syracuseStep 2500241 = 1875181) B1875181
theorem B2500259 : Blo 1666533 2500259 := bstep (se 1 (by rfl) ⟨1875194, by rfl⟩ : syracuseStep 2500259 = 3750389) B3750389
theorem B2500289 : Blo 1666533 2500289 := bstep (se 2 (by rfl) ⟨937608, by rfl⟩ : syracuseStep 2500289 = 1875217) B1875217
theorem B2500307 : Blo 1666533 2500307 := bstep (se 1 (by rfl) ⟨1875230, by rfl⟩ : syracuseStep 2500307 = 3750461) B3750461
theorem B2500337 : Blo 1666533 2500337 := bstep (se 2 (by rfl) ⟨937626, by rfl⟩ : syracuseStep 2500337 = 1875253) B1875253
theorem B4220657 : Blo 1666533 4220657 := bstep (se 2 (by rfl) ⟨1582746, by rfl⟩ : syracuseStep 4220657 = 3165493) B3165493
theorem B10143473 : Blo 1666533 10143473 := bstep (se 2 (by rfl) ⟨3803802, by rfl⟩ : syracuseStep 10143473 = 7607605) B7607605
theorem B2500355 : Blo 1666533 2500355 := bstep (se 1 (by rfl) ⟨1875266, by rfl⟩ : syracuseStep 2500355 = 3750533) B3750533
theorem B2500385 : Blo 1666533 2500385 := bstep (se 2 (by rfl) ⟨937644, by rfl⟩ : syracuseStep 2500385 = 1875289) B1875289
theorem B4220707 : Blo 1666533 4220707 := bstep (se 1 (by rfl) ⟨3165530, by rfl⟩ : syracuseStep 4220707 = 6331061) B6331061
theorem B2500403 : Blo 1666533 2500403 := bstep (se 1 (by rfl) ⟨1875302, by rfl⟩ : syracuseStep 2500403 = 3750605) B3750605
theorem B2500433 : Blo 1666533 2500433 := bstep (se 2 (by rfl) ⟨937662, by rfl⟩ : syracuseStep 2500433 = 1875325) B1875325
theorem B2500451 : Blo 1666533 2500451 := bstep (se 1 (by rfl) ⟨1875338, by rfl⟩ : syracuseStep 2500451 = 3750677) B3750677
theorem B2500481 : Blo 1666533 2500481 := bstep (se 2 (by rfl) ⟨937680, by rfl⟩ : syracuseStep 2500481 = 1875361) B1875361
theorem B3164035 : Blo 1666533 3164035 := bstep (se 1 (by rfl) ⟨2373026, by rfl⟩ : syracuseStep 3164035 = 4746053) B4746053
theorem B2500499 : Blo 1666533 2500499 := bstep (se 1 (by rfl) ⟨1875374, by rfl⟩ : syracuseStep 2500499 = 3750749) B3750749
theorem B2500529 : Blo 1666533 2500529 := bstep (se 2 (by rfl) ⟨937698, by rfl⟩ : syracuseStep 2500529 = 1875397) B1875397
theorem B4220849 : Blo 1666533 4220849 := bstep (se 2 (by rfl) ⟨1582818, by rfl⟩ : syracuseStep 4220849 = 3165637) B3165637
theorem B2500547 : Blo 1666533 2500547 := bstep (se 1 (by rfl) ⟨1875410, by rfl⟩ : syracuseStep 2500547 = 3750821) B3750821
theorem B2500577 : Blo 1666533 2500577 := bstep (se 2 (by rfl) ⟨937716, by rfl⟩ : syracuseStep 2500577 = 1875433) B1875433
theorem B9496547 : Blo 1666533 9496547 := bstep (se 1 (by rfl) ⟨7122410, by rfl⟩ : syracuseStep 9496547 = 14244821) B14244821
theorem B2500595 : Blo 1666533 2500595 := bstep (se 1 (by rfl) ⟨1875446, by rfl⟩ : syracuseStep 2500595 = 3750893) B3750893
theorem B10831877 : Blo 1666533 10831877 := bstep (se 4 (by rfl) ⟨1015488, by rfl⟩ : syracuseStep 10831877 = 2030977) B2030977
theorem B6006797 : Blo 1666533 6006797 := bstep (se 3 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 6006797 = 2252549) B2252549
theorem B2500625 : Blo 1666533 2500625 := bstep (se 2 (by rfl) ⟨937734, by rfl⟩ : syracuseStep 2500625 = 1875469) B1875469
theorem B2500643 : Blo 1666533 2500643 := bstep (se 1 (by rfl) ⟨1875482, by rfl⟩ : syracuseStep 2500643 = 3750965) B3750965
theorem B2500673 : Blo 1666533 2500673 := bstep (se 2 (by rfl) ⟨937752, by rfl⟩ : syracuseStep 2500673 = 1875505) B1875505
theorem B2500691 : Blo 1666533 2500691 := bstep (se 1 (by rfl) ⟨1875518, by rfl⟩ : syracuseStep 2500691 = 3751037) B3751037
theorem B7121009 : Blo 1666533 7121009 := bstep (se 2 (by rfl) ⟨2670378, by rfl⟩ : syracuseStep 7121009 = 5340757) B5340757
theorem B2500721 : Blo 1666533 2500721 := bstep (se 2 (by rfl) ⟨937770, by rfl⟩ : syracuseStep 2500721 = 1875541) B1875541
theorem B2500739 : Blo 1666533 2500739 := bstep (se 1 (by rfl) ⟨1875554, by rfl⟩ : syracuseStep 2500739 = 3751109) B3751109
theorem B2500769 : Blo 1666533 2500769 := bstep (se 2 (by rfl) ⟨937788, by rfl⟩ : syracuseStep 2500769 = 1875577) B1875577
theorem B2500787 : Blo 1666533 2500787 := bstep (se 1 (by rfl) ⟨1875590, by rfl⟩ : syracuseStep 2500787 = 3751181) B3751181
theorem B2500817 : Blo 1666533 2500817 := bstep (se 2 (by rfl) ⟨937806, by rfl⟩ : syracuseStep 2500817 = 1875613) B1875613
theorem B2500835 : Blo 1666533 2500835 := bstep (se 1 (by rfl) ⟨1875626, by rfl⟩ : syracuseStep 2500835 = 3751253) B3751253
theorem B2500865 : Blo 1666533 2500865 := bstep (se 2 (by rfl) ⟨937824, by rfl⟩ : syracuseStep 2500865 = 1875649) B1875649
theorem B4507907 : Blo 1666533 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2500883 : Blo 1666533 2500883 := bstep (se 1 (by rfl) ⟨1875662, by rfl⟩ : syracuseStep 2500883 = 3751325) B3751325
theorem B2500913 : Blo 1666533 2500913 := bstep (se 2 (by rfl) ⟨937842, by rfl⟩ : syracuseStep 2500913 = 1875685) B1875685
theorem B3164483 : Blo 1666533 3164483 := bstep (se 1 (by rfl) ⟨2373362, by rfl⟩ : syracuseStep 3164483 = 4746725) B4746725
theorem B2500931 : Blo 1666533 2500931 := bstep (se 1 (by rfl) ⟨1875698, by rfl⟩ : syracuseStep 2500931 = 3751397) B3751397
theorem B2500961 : Blo 1666533 2500961 := bstep (se 2 (by rfl) ⟨937860, by rfl⟩ : syracuseStep 2500961 = 1875721) B1875721
theorem B2500979 : Blo 1666533 2500979 := bstep (se 1 (by rfl) ⟨1875734, by rfl⟩ : syracuseStep 2500979 = 3751469) B3751469
theorem B2501009 : Blo 1666533 2501009 := bstep (se 2 (by rfl) ⟨937878, by rfl⟩ : syracuseStep 2501009 = 1875757) B1875757
theorem B2501027 : Blo 1666533 2501027 := bstep (se 1 (by rfl) ⟨1875770, by rfl⟩ : syracuseStep 2501027 = 3751541) B3751541
theorem B2501057 : Blo 1666533 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B4811213 : Blo 1666533 4811213 := bstep (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) B1804205
theorem B2501075 : Blo 1666533 2501075 := bstep (se 1 (by rfl) ⟨1875806, by rfl⟩ : syracuseStep 2501075 = 3751613) B3751613
theorem B2812387 : Blo 1666533 2812387 := bstep (se 1 (by rfl) ⟨2109290, by rfl⟩ : syracuseStep 2812387 = 4218581) B4218581
theorem B2501105 : Blo 1666533 2501105 := bstep (se 2 (by rfl) ⟨937914, by rfl⟩ : syracuseStep 2501105 = 1875829) B1875829
theorem B2501123 : Blo 1666533 2501123 := bstep (se 1 (by rfl) ⟨1875842, by rfl⟩ : syracuseStep 2501123 = 3751685) B3751685
theorem B2501153 : Blo 1666533 2501153 := bstep (se 2 (by rfl) ⟨937932, by rfl⟩ : syracuseStep 2501153 = 1875865) B1875865
theorem B2501171 : Blo 1666533 2501171 := bstep (se 1 (by rfl) ⟨1875878, by rfl⟩ : syracuseStep 2501171 = 3751757) B3751757
theorem B2501201 : Blo 1666533 2501201 := bstep (se 2 (by rfl) ⟨937950, by rfl⟩ : syracuseStep 2501201 = 1875901) B1875901
theorem B3164771 : Blo 1666533 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2501219 : Blo 1666533 2501219 := bstep (se 1 (by rfl) ⟨1875914, by rfl⟩ : syracuseStep 2501219 = 3751829) B3751829
theorem B14248547 : Blo 1666533 14248547 := bstep (se 1 (by rfl) ⟨10686410, by rfl⟩ : syracuseStep 14248547 = 21372821) B21372821
theorem B2812529 : Blo 1666533 2812529 := bstep (se 2 (by rfl) ⟨1054698, by rfl⟩ : syracuseStep 2812529 = 2109397) B2109397
theorem B2501249 : Blo 1666533 2501249 := bstep (se 2 (by rfl) ⟨937968, by rfl⟩ : syracuseStep 2501249 = 1875937) B1875937
theorem B2501267 : Blo 1666533 2501267 := bstep (se 1 (by rfl) ⟨1875950, by rfl⟩ : syracuseStep 2501267 = 3751901) B3751901
theorem B2501297 : Blo 1666533 2501297 := bstep (se 2 (by rfl) ⟨937986, by rfl⟩ : syracuseStep 2501297 = 1875973) B1875973
theorem B2501315 : Blo 1666533 2501315 := bstep (se 1 (by rfl) ⟨1875986, by rfl⟩ : syracuseStep 2501315 = 3751973) B3751973
theorem B2501345 : Blo 1666533 2501345 := bstep (se 2 (by rfl) ⟨938004, by rfl⟩ : syracuseStep 2501345 = 1876009) B1876009
theorem B2812657 : Blo 1666533 2812657 := bstep (se 2 (by rfl) ⟨1054746, by rfl⟩ : syracuseStep 2812657 = 2109493) B2109493
theorem B2501363 : Blo 1666533 2501363 := bstep (se 1 (by rfl) ⟨1876022, by rfl⟩ : syracuseStep 2501363 = 3752045) B3752045
theorem B2501393 : Blo 1666533 2501393 := bstep (se 2 (by rfl) ⟨938022, by rfl⟩ : syracuseStep 2501393 = 1876045) B1876045
theorem B2812691 : Blo 1666533 2812691 := bstep (se 1 (by rfl) ⟨2109518, by rfl⟩ : syracuseStep 2812691 = 4219037) B4219037
theorem B2501411 : Blo 1666533 2501411 := bstep (se 1 (by rfl) ⟨1876058, by rfl⟩ : syracuseStep 2501411 = 3752117) B3752117
theorem B2501441 : Blo 1666533 2501441 := bstep (se 2 (by rfl) ⟨938040, by rfl⟩ : syracuseStep 2501441 = 1876081) B1876081
theorem B2501459 : Blo 1666533 2501459 := bstep (se 1 (by rfl) ⟨1876094, by rfl⟩ : syracuseStep 2501459 = 3752189) B3752189
theorem B2501489 : Blo 1666533 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B2501507 : Blo 1666533 2501507 := bstep (se 1 (by rfl) ⟨1876130, by rfl⟩ : syracuseStep 2501507 = 3752261) B3752261
theorem B4221841 : Blo 1666533 4221841 := bstep (se 2 (by rfl) ⟨1583190, by rfl⟩ : syracuseStep 4221841 = 3166381) B3166381
theorem B2812819 : Blo 1666533 2812819 := bstep (se 1 (by rfl) ⟨2109614, by rfl⟩ : syracuseStep 2812819 = 4219229) B4219229
theorem B2501537 : Blo 1666533 2501537 := bstep (se 2 (by rfl) ⟨938076, by rfl⟩ : syracuseStep 2501537 = 1876153) B1876153
theorem B2501555 : Blo 1666533 2501555 := bstep (se 1 (by rfl) ⟨1876166, by rfl⟩ : syracuseStep 2501555 = 3752333) B3752333
theorem B2501585 : Blo 1666533 2501585 := bstep (se 2 (by rfl) ⟨938094, by rfl⟩ : syracuseStep 2501585 = 1876189) B1876189
theorem B2501603 : Blo 1666533 2501603 := bstep (se 1 (by rfl) ⟨1876202, by rfl⟩ : syracuseStep 2501603 = 3752405) B3752405
theorem B3804131 : Blo 1666533 3804131 := bstep (se 1 (by rfl) ⟨2853098, by rfl⟩ : syracuseStep 3804131 = 5706197) B5706197
theorem B2501633 : Blo 1666533 2501633 := bstep (se 2 (by rfl) ⟨938112, by rfl⟩ : syracuseStep 2501633 = 1876225) B1876225
theorem B16239629 : Blo 1666533 16239629 := bstep (se 3 (by rfl) ⟨3044930, by rfl⟩ : syracuseStep 16239629 = 6089861) B6089861
theorem B2501651 : Blo 1666533 2501651 := bstep (se 1 (by rfl) ⟨1876238, by rfl⟩ : syracuseStep 2501651 = 3752477) B3752477
theorem B45648917 : Blo 1666533 45648917 := bstep (se 6 (by rfl) ⟨1069896, by rfl⟩ : syracuseStep 45648917 = 2139793) B2139793
theorem B2812961 : Blo 1666533 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B8121379 : Blo 1666533 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B2501681 : Blo 1666533 2501681 := bstep (se 2 (by rfl) ⟨938130, by rfl⟩ : syracuseStep 2501681 = 1876261) B1876261
theorem B2501699 : Blo 1666533 2501699 := bstep (se 1 (by rfl) ⟨1876274, by rfl⟩ : syracuseStep 2501699 = 3752549) B3752549
theorem B2501729 : Blo 1666533 2501729 := bstep (se 2 (by rfl) ⟨938148, by rfl⟩ : syracuseStep 2501729 = 1876297) B1876297
theorem B2501747 : Blo 1666533 2501747 := bstep (se 1 (by rfl) ⟨1876310, by rfl⟩ : syracuseStep 2501747 = 3752621) B3752621
theorem B2501777 : Blo 1666533 2501777 := bstep (se 2 (by rfl) ⟨938166, by rfl⟩ : syracuseStep 2501777 = 1876333) B1876333
theorem B2813089 : Blo 1666533 2813089 := bstep (se 2 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 2813089 = 2109817) B2109817
theorem B2501795 : Blo 1666533 2501795 := bstep (se 1 (by rfl) ⟨1876346, by rfl⟩ : syracuseStep 2501795 = 3752693) B3752693
theorem B4222115 : Blo 1666533 4222115 := bstep (se 1 (by rfl) ⟨3166586, by rfl⟩ : syracuseStep 4222115 = 6333173) B6333173
theorem B8441009 : Blo 1666533 8441009 := bstep (se 2 (by rfl) ⟨3165378, by rfl⟩ : syracuseStep 8441009 = 6330757) B6330757
theorem B2534593 : Blo 1666533 2534593 := bstep (se 2 (by rfl) ⟨950472, by rfl⟩ : syracuseStep 2534593 = 1900945) B1900945
theorem B2501825 : Blo 1666533 2501825 := bstep (se 2 (by rfl) ⟨938184, by rfl⟩ : syracuseStep 2501825 = 1876369) B1876369
theorem B2813123 : Blo 1666533 2813123 := bstep (se 1 (by rfl) ⟨2109842, by rfl⟩ : syracuseStep 2813123 = 4219685) B4219685
theorem B2501843 : Blo 1666533 2501843 := bstep (se 1 (by rfl) ⟨1876382, by rfl⟩ : syracuseStep 2501843 = 3752765) B3752765
theorem B2501873 : Blo 1666533 2501873 := bstep (se 2 (by rfl) ⟨938202, by rfl⟩ : syracuseStep 2501873 = 1876405) B1876405
theorem B2501891 : Blo 1666533 2501891 := bstep (se 1 (by rfl) ⟨1876418, by rfl⟩ : syracuseStep 2501891 = 3752837) B3752837
theorem B4746509 : Blo 1666533 4746509 := bstep (se 3 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 4746509 = 1779941) B1779941
theorem B2501921 : Blo 1666533 2501921 := bstep (se 2 (by rfl) ⟨938220, by rfl⟩ : syracuseStep 2501921 = 1876441) B1876441
theorem B2501939 : Blo 1666533 2501939 := bstep (se 1 (by rfl) ⟨1876454, by rfl⟩ : syracuseStep 2501939 = 3752909) B3752909
theorem B2813251 : Blo 1666533 2813251 := bstep (se 1 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 2813251 = 4219877) B4219877
theorem B6327629 : Blo 1666533 6327629 := bstep (se 3 (by rfl) ⟨1186430, by rfl⟩ : syracuseStep 6327629 = 2372861) B2372861
theorem B2501969 : Blo 1666533 2501969 := bstep (se 2 (by rfl) ⟨938238, by rfl⟩ : syracuseStep 2501969 = 1876477) B1876477
theorem B7122275 : Blo 1666533 7122275 := bstep (se 1 (by rfl) ⟨5341706, by rfl⟩ : syracuseStep 7122275 = 10683413) B10683413
theorem B2501987 : Blo 1666533 2501987 := bstep (se 1 (by rfl) ⟨1876490, by rfl⟩ : syracuseStep 2501987 = 3752981) B3752981
theorem B2502017 : Blo 1666533 2502017 := bstep (se 2 (by rfl) ⟨938256, by rfl⟩ : syracuseStep 2502017 = 1876513) B1876513
theorem B2502035 : Blo 1666533 2502035 := bstep (se 1 (by rfl) ⟨1876526, by rfl⟩ : syracuseStep 2502035 = 3753053) B3753053
theorem B3378595 : Blo 1666533 3378595 := bstep (se 1 (by rfl) ⟨2533946, by rfl⟩ : syracuseStep 3378595 = 5067893) B5067893
theorem B4746701 : Blo 1666533 4746701 := bstep (se 3 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 4746701 = 1780013) B1780013
theorem B2813393 : Blo 1666533 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B1666547 : Blo 1666533 1666547 := bstep (se 1 (by rfl) ⟨1249910, by rfl⟩ : syracuseStep 1666547 = 2499821) B2499821
theorem B1666563 : Blo 1666533 1666563 := bstep (se 1 (by rfl) ⟨1249922, by rfl⟩ : syracuseStep 1666563 = 2499845) B2499845
theorem B3165713 : Blo 1666533 3165713 := bstep (se 2 (by rfl) ⟨1187142, by rfl⟩ : syracuseStep 3165713 = 2374285) B2374285
theorem B1666579 : Blo 1666533 1666579 := bstep (se 1 (by rfl) ⟨1249934, by rfl⟩ : syracuseStep 1666579 = 2499869) B2499869
theorem B1666595 : Blo 1666533 1666595 := bstep (se 1 (by rfl) ⟨1249946, by rfl⟩ : syracuseStep 1666595 = 2499893) B2499893
theorem B1666611 : Blo 1666533 1666611 := bstep (se 1 (by rfl) ⟨1249958, by rfl⟩ : syracuseStep 1666611 = 2499917) B2499917
theorem B1666627 : Blo 1666533 1666627 := bstep (se 1 (by rfl) ⟨1249970, by rfl⟩ : syracuseStep 1666627 = 2499941) B2499941
theorem B12021317 : Blo 1666533 12021317 := bstep (se 4 (by rfl) ⟨1126998, by rfl⟩ : syracuseStep 12021317 = 2253997) B2253997
theorem B6090317 : Blo 1666533 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B2813521 : Blo 1666533 2813521 := bstep (se 2 (by rfl) ⟨1055070, by rfl⟩ : syracuseStep 2813521 = 2110141) B2110141
theorem B1666643 : Blo 1666533 1666643 := bstep (se 1 (by rfl) ⟨1249982, by rfl⟩ : syracuseStep 1666643 = 2499965) B2499965
theorem B1666659 : Blo 1666533 1666659 := bstep (se 1 (by rfl) ⟨1249994, by rfl⟩ : syracuseStep 1666659 = 2499989) B2499989
theorem B1666675 : Blo 1666533 1666675 := bstep (se 1 (by rfl) ⟨1250006, by rfl⟩ : syracuseStep 1666675 = 2500013) B2500013
theorem B2813555 : Blo 1666533 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B1666691 : Blo 1666533 1666691 := bstep (se 1 (by rfl) ⟨1250018, by rfl⟩ : syracuseStep 1666691 = 2500037) B2500037
theorem B1666707 : Blo 1666533 1666707 := bstep (se 1 (by rfl) ⟨1250030, by rfl⟩ : syracuseStep 1666707 = 2500061) B2500061
theorem B1666723 : Blo 1666533 1666723 := bstep (se 1 (by rfl) ⟨1250042, by rfl⟩ : syracuseStep 1666723 = 2500085) B2500085
theorem B1666739 : Blo 1666533 1666739 := bstep (se 1 (by rfl) ⟨1250054, by rfl⟩ : syracuseStep 1666739 = 2500109) B2500109
theorem B1666755 : Blo 1666533 1666755 := bstep (se 1 (by rfl) ⟨1250066, by rfl⟩ : syracuseStep 1666755 = 2500133) B2500133
theorem B1666771 : Blo 1666533 1666771 := bstep (se 1 (by rfl) ⟨1250078, by rfl⟩ : syracuseStep 1666771 = 2500157) B2500157
theorem B1666787 : Blo 1666533 1666787 := bstep (se 1 (by rfl) ⟨1250090, by rfl⟩ : syracuseStep 1666787 = 2500181) B2500181
theorem B1666803 : Blo 1666533 1666803 := bstep (se 1 (by rfl) ⟨1250102, by rfl⟩ : syracuseStep 1666803 = 2500205) B2500205
theorem B2813683 : Blo 1666533 2813683 := bstep (se 1 (by rfl) ⟨2110262, by rfl⟩ : syracuseStep 2813683 = 4220525) B4220525
theorem B1666819 : Blo 1666533 1666819 := bstep (se 1 (by rfl) ⟨1250114, by rfl⟩ : syracuseStep 1666819 = 2500229) B2500229
theorem B1666835 : Blo 1666533 1666835 := bstep (se 1 (by rfl) ⟨1250126, by rfl⟩ : syracuseStep 1666835 = 2500253) B2500253
theorem B1666851 : Blo 1666533 1666851 := bstep (se 1 (by rfl) ⟨1250138, by rfl⟩ : syracuseStep 1666851 = 2500277) B2500277
theorem B2109235 : Blo 1666533 2109235 := bstep (se 1 (by rfl) ⟨1581926, by rfl⟩ : syracuseStep 2109235 = 3163853) B3163853
theorem B1666867 : Blo 1666533 1666867 := bstep (se 1 (by rfl) ⟨1250150, by rfl⟩ : syracuseStep 1666867 = 2500301) B2500301
theorem B1666883 : Blo 1666533 1666883 := bstep (se 1 (by rfl) ⟨1250162, by rfl⟩ : syracuseStep 1666883 = 2500325) B2500325
theorem B1666899 : Blo 1666533 1666899 := bstep (se 1 (by rfl) ⟨1250174, by rfl⟩ : syracuseStep 1666899 = 2500349) B2500349
theorem B1666915 : Blo 1666533 1666915 := bstep (se 1 (by rfl) ⟨1250186, by rfl⟩ : syracuseStep 1666915 = 2500373) B2500373
theorem B1666931 : Blo 1666533 1666931 := bstep (se 1 (by rfl) ⟨1250198, by rfl⟩ : syracuseStep 1666931 = 2500397) B2500397
theorem B2813825 : Blo 1666533 2813825 := bstep (se 2 (by rfl) ⟨1055184, by rfl⟩ : syracuseStep 2813825 = 2110369) B2110369
theorem B1666947 : Blo 1666533 1666947 := bstep (se 1 (by rfl) ⟨1250210, by rfl⟩ : syracuseStep 1666947 = 2500421) B2500421
theorem B2109331 : Blo 1666533 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B1666963 : Blo 1666533 1666963 := bstep (se 1 (by rfl) ⟨1250222, by rfl⟩ : syracuseStep 1666963 = 2500445) B2500445
theorem B1666979 : Blo 1666533 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B1666995 : Blo 1666533 1666995 := bstep (se 1 (by rfl) ⟨1250246, by rfl⟩ : syracuseStep 1666995 = 2500493) B2500493
theorem B1667011 : Blo 1666533 1667011 := bstep (se 1 (by rfl) ⟨1250258, by rfl⟩ : syracuseStep 1667011 = 2500517) B2500517
theorem B1667027 : Blo 1666533 1667027 := bstep (se 1 (by rfl) ⟨1250270, by rfl⟩ : syracuseStep 1667027 = 2500541) B2500541
theorem B1667043 : Blo 1666533 1667043 := bstep (se 1 (by rfl) ⟨1250282, by rfl⟩ : syracuseStep 1667043 = 2500565) B2500565
theorem B1667059 : Blo 1666533 1667059 := bstep (se 1 (by rfl) ⟨1250294, by rfl⟩ : syracuseStep 1667059 = 2500589) B2500589
theorem B2813953 : Blo 1666533 2813953 := bstep (se 2 (by rfl) ⟨1055232, by rfl⟩ : syracuseStep 2813953 = 2110465) B2110465
theorem B1667075 : Blo 1666533 1667075 := bstep (se 1 (by rfl) ⟨1250306, by rfl⟩ : syracuseStep 1667075 = 2500613) B2500613
theorem B1667091 : Blo 1666533 1667091 := bstep (se 1 (by rfl) ⟨1250318, by rfl⟩ : syracuseStep 1667091 = 2500637) B2500637
theorem B1667107 : Blo 1666533 1667107 := bstep (se 1 (by rfl) ⟨1250330, by rfl⟩ : syracuseStep 1667107 = 2500661) B2500661
theorem B2813987 : Blo 1666533 2813987 := bstep (se 1 (by rfl) ⟨2110490, by rfl⟩ : syracuseStep 2813987 = 4220981) B4220981
theorem B1667123 : Blo 1666533 1667123 := bstep (se 1 (by rfl) ⟨1250342, by rfl⟩ : syracuseStep 1667123 = 2500685) B2500685
theorem B1667139 : Blo 1666533 1667139 := bstep (se 1 (by rfl) ⟨1250354, by rfl⟩ : syracuseStep 1667139 = 2500709) B2500709
theorem B1667155 : Blo 1666533 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B1667171 : Blo 1666533 1667171 := bstep (se 1 (by rfl) ⟨1250378, by rfl⟩ : syracuseStep 1667171 = 2500757) B2500757
theorem B1667187 : Blo 1666533 1667187 := bstep (se 1 (by rfl) ⟨1250390, by rfl⟩ : syracuseStep 1667187 = 2500781) B2500781
theorem B2535553 : Blo 1666533 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B1667203 : Blo 1666533 1667203 := bstep (se 1 (by rfl) ⟨1250402, by rfl⟩ : syracuseStep 1667203 = 2500805) B2500805
theorem B5705873 : Blo 1666533 5705873 := bstep (se 2 (by rfl) ⟨2139702, by rfl⟩ : syracuseStep 5705873 = 4279405) B4279405
theorem B1667219 : Blo 1666533 1667219 := bstep (se 1 (by rfl) ⟨1250414, by rfl⟩ : syracuseStep 1667219 = 2500829) B2500829
theorem B1667235 : Blo 1666533 1667235 := bstep (se 1 (by rfl) ⟨1250426, by rfl⟩ : syracuseStep 1667235 = 2500853) B2500853
theorem B2814115 : Blo 1666533 2814115 := bstep (se 1 (by rfl) ⟨2110586, by rfl⟩ : syracuseStep 2814115 = 4221173) B4221173
theorem B1667251 : Blo 1666533 1667251 := bstep (se 1 (by rfl) ⟨1250438, by rfl⟩ : syracuseStep 1667251 = 2500877) B2500877
theorem B1667267 : Blo 1666533 1667267 := bstep (se 1 (by rfl) ⟨1250450, by rfl⟩ : syracuseStep 1667267 = 2500901) B2500901
theorem B1667283 : Blo 1666533 1667283 := bstep (se 1 (by rfl) ⟨1250462, by rfl⟩ : syracuseStep 1667283 = 2500925) B2500925
theorem B1667299 : Blo 1666533 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B4878563 : Blo 1666533 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1667315 : Blo 1666533 1667315 := bstep (se 1 (by rfl) ⟨1250486, by rfl⟩ : syracuseStep 1667315 = 2500973) B2500973
theorem B1667331 : Blo 1666533 1667331 := bstep (se 1 (by rfl) ⟨1250498, by rfl⟩ : syracuseStep 1667331 = 2500997) B2500997
theorem B1667347 : Blo 1666533 1667347 := bstep (se 1 (by rfl) ⟨1250510, by rfl⟩ : syracuseStep 1667347 = 2501021) B2501021
theorem B1667363 : Blo 1666533 1667363 := bstep (se 1 (by rfl) ⟨1250522, by rfl⟩ : syracuseStep 1667363 = 2501045) B2501045
theorem B2814257 : Blo 1666533 2814257 := bstep (se 2 (by rfl) ⟨1055346, by rfl⟩ : syracuseStep 2814257 = 2110693) B2110693
theorem B1667379 : Blo 1666533 1667379 := bstep (se 1 (by rfl) ⟨1250534, by rfl⟩ : syracuseStep 1667379 = 2501069) B2501069
theorem B1667395 : Blo 1666533 1667395 := bstep (se 1 (by rfl) ⟨1250546, by rfl⟩ : syracuseStep 1667395 = 2501093) B2501093
theorem B2535761 : Blo 1666533 2535761 := bstep (se 2 (by rfl) ⟨950910, by rfl⟩ : syracuseStep 2535761 = 1901821) B1901821
theorem B1667411 : Blo 1666533 1667411 := bstep (se 1 (by rfl) ⟨1250558, by rfl⟩ : syracuseStep 1667411 = 2501117) B2501117
theorem B1667427 : Blo 1666533 1667427 := bstep (se 1 (by rfl) ⟨1250570, by rfl⟩ : syracuseStep 1667427 = 2501141) B2501141
theorem B1667443 : Blo 1666533 1667443 := bstep (se 1 (by rfl) ⟨1250582, by rfl⟩ : syracuseStep 1667443 = 2501165) B2501165
theorem B2109827 : Blo 1666533 2109827 := bstep (se 1 (by rfl) ⟨1582370, by rfl⟩ : syracuseStep 2109827 = 3164741) B3164741
theorem B1667459 : Blo 1666533 1667459 := bstep (se 1 (by rfl) ⟨1250594, by rfl⟩ : syracuseStep 1667459 = 2501189) B2501189
theorem B3166609 : Blo 1666533 3166609 := bstep (se 2 (by rfl) ⟨1187478, by rfl⟩ : syracuseStep 3166609 = 2374957) B2374957
theorem B1667475 : Blo 1666533 1667475 := bstep (se 1 (by rfl) ⟨1250606, by rfl⟩ : syracuseStep 1667475 = 2501213) B2501213
theorem B1667491 : Blo 1666533 1667491 := bstep (se 1 (by rfl) ⟨1250618, by rfl⟩ : syracuseStep 1667491 = 2501237) B2501237
theorem B4747693 : Blo 1666533 4747693 := bstep (se 3 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 4747693 = 1780385) B1780385
theorem B2814385 : Blo 1666533 2814385 := bstep (se 2 (by rfl) ⟨1055394, by rfl⟩ : syracuseStep 2814385 = 2110789) B2110789
theorem B1667507 : Blo 1666533 1667507 := bstep (se 1 (by rfl) ⟨1250630, by rfl⟩ : syracuseStep 1667507 = 2501261) B2501261
theorem B1667523 : Blo 1666533 1667523 := bstep (se 1 (by rfl) ⟨1250642, by rfl⟩ : syracuseStep 1667523 = 2501285) B2501285
theorem B2003395 : Blo 1666533 2003395 := bstep (se 1 (by rfl) ⟨1502546, by rfl⟩ : syracuseStep 2003395 = 3005093) B3005093
theorem B1667539 : Blo 1666533 1667539 := bstep (se 1 (by rfl) ⟨1250654, by rfl⟩ : syracuseStep 1667539 = 2501309) B2501309
theorem B2814419 : Blo 1666533 2814419 := bstep (se 1 (by rfl) ⟨2110814, by rfl⟩ : syracuseStep 2814419 = 4221629) B4221629
theorem B1667555 : Blo 1666533 1667555 := bstep (se 1 (by rfl) ⟨1250666, by rfl⟩ : syracuseStep 1667555 = 2501333) B2501333
theorem B22819313 : Blo 1666533 22819313 := bstep (se 2 (by rfl) ⟨8557242, by rfl⟩ : syracuseStep 22819313 = 17114485) B17114485
theorem B1667571 : Blo 1666533 1667571 := bstep (se 1 (by rfl) ⟨1250678, by rfl⟩ : syracuseStep 1667571 = 2501357) B2501357
theorem B1667587 : Blo 1666533 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B1667603 : Blo 1666533 1667603 := bstep (se 1 (by rfl) ⟨1250702, by rfl⟩ : syracuseStep 1667603 = 2501405) B2501405
theorem B1667619 : Blo 1666533 1667619 := bstep (se 1 (by rfl) ⟨1250714, by rfl⟩ : syracuseStep 1667619 = 2501429) B2501429
theorem B1667635 : Blo 1666533 1667635 := bstep (se 1 (by rfl) ⟨1250726, by rfl⟩ : syracuseStep 1667635 = 2501453) B2501453
theorem B1667651 : Blo 1666533 1667651 := bstep (se 1 (by rfl) ⟨1250738, by rfl⟩ : syracuseStep 1667651 = 2501477) B2501477
theorem B1667667 : Blo 1666533 1667667 := bstep (se 1 (by rfl) ⟨1250750, by rfl⟩ : syracuseStep 1667667 = 2501501) B2501501
theorem B2814547 : Blo 1666533 2814547 := bstep (se 1 (by rfl) ⟨2110910, by rfl⟩ : syracuseStep 2814547 = 4221821) B4221821
theorem B8442467 : Blo 1666533 8442467 := bstep (se 1 (by rfl) ⟨6331850, by rfl⟩ : syracuseStep 8442467 = 12663701) B12663701
theorem B1667683 : Blo 1666533 1667683 := bstep (se 1 (by rfl) ⟨1250762, by rfl⟩ : syracuseStep 1667683 = 2501525) B2501525
theorem B1667699 : Blo 1666533 1667699 := bstep (se 1 (by rfl) ⟨1250774, by rfl⟩ : syracuseStep 1667699 = 2501549) B2501549
theorem B1667715 : Blo 1666533 1667715 := bstep (se 1 (by rfl) ⟨1250786, by rfl⟩ : syracuseStep 1667715 = 2501573) B2501573
theorem B1667731 : Blo 1666533 1667731 := bstep (se 1 (by rfl) ⟨1250798, by rfl⟩ : syracuseStep 1667731 = 2501597) B2501597
theorem B1667747 : Blo 1666533 1667747 := bstep (se 1 (by rfl) ⟨1250810, by rfl⟩ : syracuseStep 1667747 = 2501621) B2501621
theorem B1667763 : Blo 1666533 1667763 := bstep (se 1 (by rfl) ⟨1250822, by rfl⟩ : syracuseStep 1667763 = 2501645) B2501645
theorem B3011267 : Blo 1666533 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B1667779 : Blo 1666533 1667779 := bstep (se 1 (by rfl) ⟨1250834, by rfl⟩ : syracuseStep 1667779 = 2501669) B2501669
theorem B1667795 : Blo 1666533 1667795 := bstep (se 1 (by rfl) ⟨1250846, by rfl⟩ : syracuseStep 1667795 = 2501693) B2501693
theorem B2814689 : Blo 1666533 2814689 := bstep (se 2 (by rfl) ⟨1055508, by rfl⟩ : syracuseStep 2814689 = 2111017) B2111017
theorem B16028387 : Blo 1666533 16028387 := bstep (se 1 (by rfl) ⟨12021290, by rfl⟩ : syracuseStep 16028387 = 24042581) B24042581
theorem B1667811 : Blo 1666533 1667811 := bstep (se 1 (by rfl) ⟨1250858, by rfl⟩ : syracuseStep 1667811 = 2501717) B2501717
theorem B1667827 : Blo 1666533 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B1667843 : Blo 1666533 1667843 := bstep (se 1 (by rfl) ⟨1250882, by rfl⟩ : syracuseStep 1667843 = 2501765) B2501765
theorem B10679053 : Blo 1666533 10679053 := bstep (se 3 (by rfl) ⟨2002322, by rfl⟩ : syracuseStep 10679053 = 4004645) B4004645
theorem B1667859 : Blo 1666533 1667859 := bstep (se 1 (by rfl) ⟨1250894, by rfl⟩ : syracuseStep 1667859 = 2501789) B2501789
theorem B51335957 : Blo 1666533 51335957 := bstep (se 6 (by rfl) ⟨1203186, by rfl⟩ : syracuseStep 51335957 = 2406373) B2406373
theorem B1667875 : Blo 1666533 1667875 := bstep (se 1 (by rfl) ⟨1250906, by rfl⟩ : syracuseStep 1667875 = 2501813) B2501813
theorem B1667891 : Blo 1666533 1667891 := bstep (se 1 (by rfl) ⟨1250918, by rfl⟩ : syracuseStep 1667891 = 2501837) B2501837
theorem B1667907 : Blo 1666533 1667907 := bstep (se 1 (by rfl) ⟨1250930, by rfl⟩ : syracuseStep 1667907 = 2501861) B2501861
theorem B1667923 : Blo 1666533 1667923 := bstep (se 1 (by rfl) ⟨1250942, by rfl⟩ : syracuseStep 1667923 = 2501885) B2501885
theorem B1667939 : Blo 1666533 1667939 := bstep (se 1 (by rfl) ⟨1250954, by rfl⟩ : syracuseStep 1667939 = 2501909) B2501909
theorem B2569073 : Blo 1666533 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B1667955 : Blo 1666533 1667955 := bstep (se 1 (by rfl) ⟨1250966, by rfl⟩ : syracuseStep 1667955 = 2501933) B2501933
theorem B1667971 : Blo 1666533 1667971 := bstep (se 1 (by rfl) ⟨1250978, by rfl⟩ : syracuseStep 1667971 = 2501957) B2501957
theorem B1667987 : Blo 1666533 1667987 := bstep (se 1 (by rfl) ⟨1250990, by rfl⟩ : syracuseStep 1667987 = 2501981) B2501981
theorem B1668003 : Blo 1666533 1668003 := bstep (se 1 (by rfl) ⟨1251002, by rfl⟩ : syracuseStep 1668003 = 2502005) B2502005
theorem B1668019 : Blo 1666533 1668019 := bstep (se 1 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 1668019 = 2502029) B2502029
theorem B10687459 : Blo 1666533 10687459 := bstep (se 1 (by rfl) ⟨8015594, by rfl⟩ : syracuseStep 10687459 = 16031189) B16031189
theorem B10277923 : Blo 1666533 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B8008753 : Blo 1666533 8008753 := bstep (se 2 (by rfl) ⟨3003282, by rfl⟩ : syracuseStep 8008753 = 6006565) B6006565
theorem B2110531 : Blo 1666533 2110531 := bstep (se 1 (by rfl) ⟨1582898, by rfl⟩ : syracuseStep 2110531 = 3165797) B3165797
theorem B5624909 : Blo 1666533 5624909 := bstep (se 3 (by rfl) ⟨1054670, by rfl⟩ : syracuseStep 5624909 = 2109341) B2109341
theorem B43308145 : Blo 1666533 43308145 := bstep (se 2 (by rfl) ⟨16240554, by rfl⟩ : syracuseStep 43308145 = 32481109) B32481109
theorem B5624963 : Blo 1666533 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B9499781 : Blo 1666533 9499781 := bstep (se 4 (by rfl) ⟨890604, by rfl⟩ : syracuseStep 9499781 = 1781209) B1781209
theorem B6009997 : Blo 1666533 6009997 := bstep (se 3 (by rfl) ⟨1126874, by rfl⟩ : syracuseStep 6009997 = 2253749) B2253749
theorem B2110627 : Blo 1666533 2110627 := bstep (se 1 (by rfl) ⟨1582970, by rfl⟩ : syracuseStep 2110627 = 3165941) B3165941
theorem B8443277 : Blo 1666533 8443277 := bstep (se 3 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 8443277 = 3166229) B3166229
theorem B5625233 : Blo 1666533 5625233 := bstep (se 2 (by rfl) ⟨2109462, by rfl⟩ : syracuseStep 5625233 = 4218925) B4218925
theorem B3560881 : Blo 1666533 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B12662243 : Blo 1666533 12662243 := bstep (se 1 (by rfl) ⟨9496682, by rfl⟩ : syracuseStep 12662243 = 18993365) B18993365
theorem B5068369 : Blo 1666533 5068369 := bstep (se 2 (by rfl) ⟨1900638, by rfl⟩ : syracuseStep 5068369 = 3801277) B3801277
theorem B3004003 : Blo 1666533 3004003 := bstep (se 1 (by rfl) ⟨2253002, by rfl⟩ : syracuseStep 3004003 = 4506005) B4506005
theorem B89028209 : Blo 1666533 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B9492173 : Blo 1666533 9492173 := bstep (se 3 (by rfl) ⟨1779782, by rfl⟩ : syracuseStep 9492173 = 3559565) B3559565
theorem B3749777 : Blo 1666533 3749777 := bstep (se 2 (by rfl) ⟨1406166, by rfl⟩ : syracuseStep 3749777 = 2812333) B2812333
theorem B3749795 : Blo 1666533 3749795 := bstep (se 1 (by rfl) ⟨2812346, by rfl⟩ : syracuseStep 3749795 = 5624693) B5624693
theorem B5625773 : Blo 1666533 5625773 := bstep (se 3 (by rfl) ⟨1054832, by rfl⟩ : syracuseStep 5625773 = 2109665) B2109665
theorem B11409329 : Blo 1666533 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B2406355 : Blo 1666533 2406355 := bstep (se 1 (by rfl) ⟨1804766, by rfl⟩ : syracuseStep 2406355 = 3609533) B3609533
theorem B5625827 : Blo 1666533 5625827 := bstep (se 1 (by rfl) ⟨4219370, by rfl⟩ : syracuseStep 5625827 = 8438741) B8438741
theorem B5339117 : Blo 1666533 5339117 := bstep (se 3 (by rfl) ⟨1001084, by rfl⟩ : syracuseStep 5339117 = 2002169) B2002169
theorem B2373619 : Blo 1666533 2373619 := bstep (se 1 (by rfl) ⟨1780214, by rfl⟩ : syracuseStep 2373619 = 3560429) B3560429
theorem B3004465 : Blo 1666533 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B2373715 : Blo 1666533 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B4749425 : Blo 1666533 4749425 := bstep (se 2 (by rfl) ⟨1781034, by rfl⟩ : syracuseStep 4749425 = 3562069) B3562069
theorem B3750065 : Blo 1666533 3750065 := bstep (se 2 (by rfl) ⟨1406274, by rfl⟩ : syracuseStep 3750065 = 2812549) B2812549
theorem B6330545 : Blo 1666533 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B3750083 : Blo 1666533 3750083 := bstep (se 1 (by rfl) ⟨2812562, by rfl⟩ : syracuseStep 3750083 = 5625125) B5625125
theorem B140613859 : Blo 1666533 140613859 := bstep (se 1 (by rfl) ⟨105460394, by rfl⟩ : syracuseStep 140613859 = 210920789) B210920789
theorem B5626097 : Blo 1666533 5626097 := bstep (se 2 (by rfl) ⟨2109786, by rfl⟩ : syracuseStep 5626097 = 4219573) B4219573
theorem B4749617 : Blo 1666533 4749617 := bstep (se 2 (by rfl) ⟨1781106, by rfl⟩ : syracuseStep 4749617 = 3562213) B3562213
theorem B5282225 : Blo 1666533 5282225 := bstep (se 2 (by rfl) ⟨1980834, by rfl⟩ : syracuseStep 5282225 = 3961669) B3961669
theorem B14637509 : Blo 1666533 14637509 := bstep (se 4 (by rfl) ⟨1372266, by rfl⟩ : syracuseStep 14637509 = 2744533) B2744533
theorem B3750353 : Blo 1666533 3750353 := bstep (se 2 (by rfl) ⟨1406382, by rfl⟩ : syracuseStep 3750353 = 2812765) B2812765
theorem B3750371 : Blo 1666533 3750371 := bstep (se 1 (by rfl) ⟨2812778, by rfl⟩ : syracuseStep 3750371 = 5625557) B5625557
theorem B5339629 : Blo 1666533 5339629 := bstep (se 3 (by rfl) ⟨1001180, by rfl⟩ : syracuseStep 5339629 = 2002361) B2002361
theorem B18987533 : Blo 1666533 18987533 := bstep (se 3 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 18987533 = 7120325) B7120325
theorem B2374211 : Blo 1666533 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B13523597 : Blo 1666533 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B10558129 : Blo 1666533 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B3750641 : Blo 1666533 3750641 := bstep (se 2 (by rfl) ⟨1406490, by rfl⟩ : syracuseStep 3750641 = 2812981) B2812981
theorem B3750659 : Blo 1666533 3750659 := bstep (se 1 (by rfl) ⟨2812994, by rfl⟩ : syracuseStep 3750659 = 5625989) B5625989
theorem B5626637 : Blo 1666533 5626637 := bstep (se 3 (by rfl) ⟨1054994, by rfl⟩ : syracuseStep 5626637 = 2109989) B2109989
theorem B5626691 : Blo 1666533 5626691 := bstep (se 1 (by rfl) ⟨4220018, by rfl⟩ : syracuseStep 5626691 = 8440037) B8440037
theorem B5340131 : Blo 1666533 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B1874947 : Blo 1666533 1874947 := bstep (se 1 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 1874947 = 2812421) B2812421
theorem B3750929 : Blo 1666533 3750929 := bstep (se 2 (by rfl) ⟨1406598, by rfl⟩ : syracuseStep 3750929 = 2813197) B2813197
theorem B3750947 : Blo 1666533 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B5626961 : Blo 1666533 5626961 := bstep (se 2 (by rfl) ⟨2110110, by rfl⟩ : syracuseStep 5626961 = 4220221) B4220221
theorem B13360241 : Blo 1666533 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B1875091 : Blo 1666533 1875091 := bstep (se 1 (by rfl) ⟨1406318, by rfl⟩ : syracuseStep 1875091 = 2812637) B2812637
theorem B2374849 : Blo 1666533 2374849 := bstep (se 2 (by rfl) ⟨890568, by rfl⟩ : syracuseStep 2374849 = 1781137) B1781137
theorem B2669777 : Blo 1666533 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B2891027 : Blo 1666533 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B2284817 : Blo 1666533 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B1875235 : Blo 1666533 1875235 := bstep (se 1 (by rfl) ⟨1406426, by rfl⟩ : syracuseStep 1875235 = 2812853) B2812853
theorem B3751217 : Blo 1666533 3751217 := bstep (se 2 (by rfl) ⟨1406706, by rfl⟩ : syracuseStep 3751217 = 2813413) B2813413
theorem B3751235 : Blo 1666533 3751235 := bstep (se 1 (by rfl) ⟨2813426, by rfl⟩ : syracuseStep 3751235 = 5626853) B5626853
theorem B2669969 : Blo 1666533 2669969 := bstep (se 2 (by rfl) ⟨1001238, by rfl⟩ : syracuseStep 2669969 = 2002477) B2002477
theorem B1875379 : Blo 1666533 1875379 := bstep (se 1 (by rfl) ⟨1406534, by rfl⟩ : syracuseStep 1875379 = 2813069) B2813069
theorem B2670097 : Blo 1666533 2670097 := bstep (se 2 (by rfl) ⟨1001286, by rfl⟩ : syracuseStep 2670097 = 2002573) B2002573
theorem B8437283 : Blo 1666533 8437283 := bstep (se 1 (by rfl) ⟨6327962, by rfl⟩ : syracuseStep 8437283 = 12655925) B12655925
theorem B1875523 : Blo 1666533 1875523 := bstep (se 1 (by rfl) ⟨1406642, by rfl⟩ : syracuseStep 1875523 = 2813285) B2813285
theorem B3751505 : Blo 1666533 3751505 := bstep (se 2 (by rfl) ⟨1406814, by rfl⟩ : syracuseStep 3751505 = 2813629) B2813629
theorem B3751523 : Blo 1666533 3751523 := bstep (se 1 (by rfl) ⟨2813642, by rfl⟩ : syracuseStep 3751523 = 5627285) B5627285
theorem B6332003 : Blo 1666533 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B5627501 : Blo 1666533 5627501 := bstep (se 3 (by rfl) ⟨1055156, by rfl⟩ : syracuseStep 5627501 = 2110313) B2110313
theorem B5627555 : Blo 1666533 5627555 := bstep (se 1 (by rfl) ⟨4220666, by rfl⟩ : syracuseStep 5627555 = 8441333) B8441333
theorem B9010885 : Blo 1666533 9010885 := bstep (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) B1689541
theorem B11402957 : Blo 1666533 11402957 := bstep (se 3 (by rfl) ⟨2138054, by rfl⟩ : syracuseStep 11402957 = 4276109) B4276109
theorem B1875667 : Blo 1666533 1875667 := bstep (se 1 (by rfl) ⟨1406750, by rfl⟩ : syracuseStep 1875667 = 2813501) B2813501
theorem B4505357 : Blo 1666533 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B4005713 : Blo 1666533 4005713 := bstep (se 2 (by rfl) ⟨1502142, by rfl⟩ : syracuseStep 4005713 = 3004285) B3004285
theorem B1875811 : Blo 1666533 1875811 := bstep (se 1 (by rfl) ⟨1406858, by rfl⟩ : syracuseStep 1875811 = 2813717) B2813717
theorem B3751793 : Blo 1666533 3751793 := bstep (se 2 (by rfl) ⟨1406922, by rfl⟩ : syracuseStep 3751793 = 2813845) B2813845
theorem B3751811 : Blo 1666533 3751811 := bstep (se 1 (by rfl) ⟨2813858, by rfl⟩ : syracuseStep 3751811 = 5627717) B5627717
theorem B9494405 : Blo 1666533 9494405 := bstep (se 4 (by rfl) ⟨890100, by rfl⟩ : syracuseStep 9494405 = 1780201) B1780201
theorem B36052877 : Blo 1666533 36052877 := bstep (se 3 (by rfl) ⟨6759914, by rfl⟩ : syracuseStep 36052877 = 13519829) B13519829
theorem B5627825 : Blo 1666533 5627825 := bstep (se 2 (by rfl) ⟨2110434, by rfl⟩ : syracuseStep 5627825 = 4220869) B4220869
theorem B1875955 : Blo 1666533 1875955 := bstep (se 1 (by rfl) ⟨1406966, by rfl⟩ : syracuseStep 1875955 = 2813933) B2813933
theorem B3751937 : Blo 1666533 3751937 := bstep (se 2 (by rfl) ⟨1406976, by rfl⟩ : syracuseStep 3751937 = 2813953) B2813953
theorem B1875991 : Blo 1666533 1875991 := bstep (se 1 (by rfl) ⟨1406993, by rfl⟩ : syracuseStep 1875991 = 2813987) B2813987
theorem B4005953 : Blo 1666533 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B24371381 : Blo 1666533 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B1876171 : Blo 1666533 1876171 := bstep (se 1 (by rfl) ⟨1407128, by rfl⟩ : syracuseStep 1876171 = 2814257) B2814257
theorem B3752153 : Blo 1666533 3752153 := bstep (se 2 (by rfl) ⟨1407057, by rfl⟩ : syracuseStep 3752153 = 2814115) B2814115
theorem B35627309 : Blo 1666533 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B3752243 : Blo 1666533 3752243 := bstep (se 1 (by rfl) ⟨2814182, by rfl⟩ : syracuseStep 3752243 = 5628365) B5628365
theorem B1876279 : Blo 1666533 1876279 := bstep (se 1 (by rfl) ⟨1407209, by rfl⟩ : syracuseStep 1876279 = 2814419) B2814419
theorem B15212875 : Blo 1666533 15212875 := bstep (se 1 (by rfl) ⟨11409656, by rfl⟩ : syracuseStep 15212875 = 22819313) B22819313
theorem B3752279 : Blo 1666533 3752279 := bstep (se 1 (by rfl) ⟨2814209, by rfl⟩ : syracuseStep 3752279 = 5628419) B5628419
theorem B5628311 : Blo 1666533 5628311 := bstep (se 1 (by rfl) ⟨4221233, by rfl⟩ : syracuseStep 5628311 = 8442467) B8442467
theorem B1876459 : Blo 1666533 1876459 := bstep (se 1 (by rfl) ⟨1407344, by rfl⟩ : syracuseStep 1876459 = 2814689) B2814689
theorem B3752459 : Blo 1666533 3752459 := bstep (se 1 (by rfl) ⟨2814344, by rfl⟩ : syracuseStep 3752459 = 5628689) B5628689
theorem B3752513 : Blo 1666533 3752513 := bstep (se 2 (by rfl) ⟨1407192, by rfl⟩ : syracuseStep 3752513 = 2814385) B2814385
theorem B2671193 : Blo 1666533 2671193 := bstep (se 2 (by rfl) ⟨1001697, by rfl⟩ : syracuseStep 2671193 = 2003395) B2003395
theorem B13009501 : Blo 1666533 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B7119505 : Blo 1666533 7119505 := bstep (se 2 (by rfl) ⟨2669814, by rfl⟩ : syracuseStep 7119505 = 5339629) B5339629
theorem B6333187 : Blo 1666533 6333187 := bstep (se 1 (by rfl) ⟨4749890, by rfl⟩ : syracuseStep 6333187 = 9499781) B9499781
theorem B3752729 : Blo 1666533 3752729 := bstep (se 2 (by rfl) ⟨1407273, by rfl⟩ : syracuseStep 3752729 = 2814547) B2814547
theorem B12665645 : Blo 1666533 12665645 := bstep (se 3 (by rfl) ⟨2374808, by rfl⟩ : syracuseStep 12665645 = 4749617) B4749617
theorem B3752819 : Blo 1666533 3752819 := bstep (se 1 (by rfl) ⟨2814614, by rfl⟩ : syracuseStep 3752819 = 5629229) B5629229
theorem B3752855 : Blo 1666533 3752855 := bstep (se 1 (by rfl) ⟨2814641, by rfl⟩ : syracuseStep 3752855 = 5629283) B5629283
theorem B5628851 : Blo 1666533 5628851 := bstep (se 1 (by rfl) ⟨4221638, by rfl⟩ : syracuseStep 5628851 = 8443277) B8443277
theorem B14238737 : Blo 1666533 14238737 := bstep (se 2 (by rfl) ⟨5339526, by rfl⟩ : syracuseStep 14238737 = 10679053) B10679053
theorem B59352139 : Blo 1666533 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B3753035 : Blo 1666533 3753035 := bstep (se 1 (by rfl) ⟨2814776, by rfl⟩ : syracuseStep 3753035 = 5629553) B5629553
theorem B5629121 : Blo 1666533 5629121 := bstep (se 2 (by rfl) ⟨2110920, by rfl⟩ : syracuseStep 5629121 = 4221841) B4221841
theorem B12657869 : Blo 1666533 12657869 := bstep (se 3 (by rfl) ⟨2373350, by rfl⟩ : syracuseStep 12657869 = 4746701) B4746701
theorem B2499851 : Blo 1666533 2499851 := bstep (se 1 (by rfl) ⟨1874888, by rfl⟩ : syracuseStep 2499851 = 3749777) B3749777
theorem B2499863 : Blo 1666533 2499863 := bstep (se 1 (by rfl) ⟨1874897, by rfl⟩ : syracuseStep 2499863 = 3749795) B3749795
theorem B2499929 : Blo 1666533 2499929 := bstep (se 2 (by rfl) ⟨937473, by rfl⟩ : syracuseStep 2499929 = 1874947) B1874947
theorem B2500043 : Blo 1666533 2500043 := bstep (se 1 (by rfl) ⟨1875032, by rfl⟩ : syracuseStep 2500043 = 3750065) B3750065
theorem B4220363 : Blo 1666533 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B2500055 : Blo 1666533 2500055 := bstep (se 1 (by rfl) ⟨1875041, by rfl⟩ : syracuseStep 2500055 = 3750083) B3750083
theorem B8013329 : Blo 1666533 8013329 := bstep (se 2 (by rfl) ⟨3004998, by rfl⟩ : syracuseStep 8013329 = 6009997) B6009997
theorem B2500121 : Blo 1666533 2500121 := bstep (se 2 (by rfl) ⟨937545, by rfl⟩ : syracuseStep 2500121 = 1875091) B1875091
theorem B8439389 : Blo 1666533 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B9758339 : Blo 1666533 9758339 := bstep (se 1 (by rfl) ⟨7318754, by rfl⟩ : syracuseStep 9758339 = 14637509) B14637509
theorem B2500235 : Blo 1666533 2500235 := bstep (se 1 (by rfl) ⟨1875176, by rfl⟩ : syracuseStep 2500235 = 3750353) B3750353
theorem B2500247 : Blo 1666533 2500247 := bstep (se 1 (by rfl) ⟨1875185, by rfl⟩ : syracuseStep 2500247 = 3750371) B3750371
theorem B12658355 : Blo 1666533 12658355 := bstep (se 1 (by rfl) ⟨9493766, by rfl⟩ : syracuseStep 12658355 = 18987533) B18987533
theorem B2500313 : Blo 1666533 2500313 := bstep (se 2 (by rfl) ⟨937617, by rfl⟩ : syracuseStep 2500313 = 1875235) B1875235
theorem B2500427 : Blo 1666533 2500427 := bstep (se 1 (by rfl) ⟨1875320, by rfl⟩ : syracuseStep 2500427 = 3750641) B3750641
theorem B2500439 : Blo 1666533 2500439 := bstep (se 1 (by rfl) ⟨1875329, by rfl⟩ : syracuseStep 2500439 = 3750659) B3750659
theorem B8030045 : Blo 1666533 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B2500505 : Blo 1666533 2500505 := bstep (se 2 (by rfl) ⟨937689, by rfl⟩ : syracuseStep 2500505 = 1875379) B1875379
theorem B2500619 : Blo 1666533 2500619 := bstep (se 1 (by rfl) ⟨1875464, by rfl⟩ : syracuseStep 2500619 = 3750929) B3750929
theorem B9013265 : Blo 1666533 9013265 := bstep (se 2 (by rfl) ⟨3379974, by rfl⟩ : syracuseStep 9013265 = 6759949) B6759949
theorem B2500631 : Blo 1666533 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B2500697 : Blo 1666533 2500697 := bstep (se 2 (by rfl) ⟨937761, by rfl⟩ : syracuseStep 2500697 = 1875523) B1875523
theorem B1779851 : Blo 1666533 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B3164339 : Blo 1666533 3164339 := bstep (se 1 (by rfl) ⟨2373254, by rfl⟩ : syracuseStep 3164339 = 4746509) B4746509
theorem B1927351 : Blo 1666533 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B2500811 : Blo 1666533 2500811 := bstep (se 1 (by rfl) ⟨1875608, by rfl⟩ : syracuseStep 2500811 = 3751217) B3751217
theorem B2500823 : Blo 1666533 2500823 := bstep (se 1 (by rfl) ⟨1875617, by rfl⟩ : syracuseStep 2500823 = 3751235) B3751235
theorem B1779979 : Blo 1666533 1779979 := bstep (se 1 (by rfl) ⟨1334984, by rfl⟩ : syracuseStep 1779979 = 2669969) B2669969
theorem B2500889 : Blo 1666533 2500889 := bstep (se 2 (by rfl) ⟨937833, by rfl⟩ : syracuseStep 2500889 = 1875667) B1875667
theorem B6850861 : Blo 1666533 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B8014211 : Blo 1666533 8014211 := bstep (se 1 (by rfl) ⟨6010658, by rfl⟩ : syracuseStep 8014211 = 12021317) B12021317
theorem B2501003 : Blo 1666533 2501003 := bstep (se 1 (by rfl) ⟨1875752, by rfl⟩ : syracuseStep 2501003 = 3751505) B3751505
theorem B2501015 : Blo 1666533 2501015 := bstep (se 1 (by rfl) ⟨1875761, by rfl⟩ : syracuseStep 2501015 = 3751523) B3751523
theorem B4221335 : Blo 1666533 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B2812313 : Blo 1666533 2812313 := bstep (se 2 (by rfl) ⟨1054617, by rfl⟩ : syracuseStep 2812313 = 2109235) B2109235
theorem B2501081 : Blo 1666533 2501081 := bstep (se 2 (by rfl) ⟨937905, by rfl⟩ : syracuseStep 2501081 = 1875811) B1875811
theorem B2812441 : Blo 1666533 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B2501195 : Blo 1666533 2501195 := bstep (se 1 (by rfl) ⟨1875896, by rfl⟩ : syracuseStep 2501195 = 3751793) B3751793
theorem B2501207 : Blo 1666533 2501207 := bstep (se 1 (by rfl) ⟨1875905, by rfl⟩ : syracuseStep 2501207 = 3751811) B3751811
theorem B10144349 : Blo 1666533 10144349 := bstep (se 3 (by rfl) ⟨1902065, by rfl⟩ : syracuseStep 10144349 = 3804131) B3804131
theorem B3164825 : Blo 1666533 3164825 := bstep (se 2 (by rfl) ⟨1186809, by rfl⟩ : syracuseStep 3164825 = 2373619) B2373619
theorem B2501273 : Blo 1666533 2501273 := bstep (se 2 (by rfl) ⟨937977, by rfl⟩ : syracuseStep 2501273 = 1875955) B1875955
theorem B43305677 : Blo 1666533 43305677 := bstep (se 3 (by rfl) ⟨8119814, by rfl⟩ : syracuseStep 43305677 = 16239629) B16239629
theorem B2501387 : Blo 1666533 2501387 := bstep (se 1 (by rfl) ⟨1876040, by rfl⟩ : syracuseStep 2501387 = 3752081) B3752081
theorem B3803915 : Blo 1666533 3803915 := bstep (se 1 (by rfl) ⟨2852936, by rfl⟩ : syracuseStep 3803915 = 5705873) B5705873
theorem B2501399 : Blo 1666533 2501399 := bstep (se 1 (by rfl) ⟨1876049, by rfl⟩ : syracuseStep 2501399 = 3752099) B3752099
theorem B2501465 : Blo 1666533 2501465 := bstep (se 2 (by rfl) ⟨938049, by rfl⟩ : syracuseStep 2501465 = 1876099) B1876099
theorem B1690507 : Blo 1666533 1690507 := bstep (se 1 (by rfl) ⟨1267880, by rfl⟩ : syracuseStep 1690507 = 2535761) B2535761
theorem B2501579 : Blo 1666533 2501579 := bstep (se 1 (by rfl) ⟨1876184, by rfl⟩ : syracuseStep 2501579 = 3752369) B3752369
theorem B2501591 : Blo 1666533 2501591 := bstep (se 1 (by rfl) ⟨1876193, by rfl⟩ : syracuseStep 2501591 = 3752387) B3752387
theorem B2501657 : Blo 1666533 2501657 := bstep (se 2 (by rfl) ⟨938121, by rfl⟩ : syracuseStep 2501657 = 1876243) B1876243
theorem B4222003 : Blo 1666533 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B15412289 : Blo 1666533 15412289 := bstep (se 2 (by rfl) ⟨5779608, by rfl⟩ : syracuseStep 15412289 = 11559217) B11559217
theorem B2813015 : Blo 1666533 2813015 := bstep (se 1 (by rfl) ⟨2109761, by rfl⟩ : syracuseStep 2813015 = 4219523) B4219523
theorem B12659813 : Blo 1666533 12659813 := bstep (se 4 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 12659813 = 2373715) B2373715
theorem B2501771 : Blo 1666533 2501771 := bstep (se 1 (by rfl) ⟨1876328, by rfl⟩ : syracuseStep 2501771 = 3752657) B3752657
theorem B10685591 : Blo 1666533 10685591 := bstep (se 1 (by rfl) ⟨8014193, by rfl⟩ : syracuseStep 10685591 = 16028387) B16028387
theorem B2501783 : Blo 1666533 2501783 := bstep (se 1 (by rfl) ⟨1876337, by rfl⟩ : syracuseStep 2501783 = 3752675) B3752675
theorem B4222145 : Blo 1666533 4222145 := bstep (se 2 (by rfl) ⟨1583304, by rfl⟩ : syracuseStep 4222145 = 3166609) B3166609
theorem B2813143 : Blo 1666533 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B2501849 : Blo 1666533 2501849 := bstep (se 2 (by rfl) ⟨938193, by rfl⟩ : syracuseStep 2501849 = 1876387) B1876387
theorem B2501963 : Blo 1666533 2501963 := bstep (se 1 (by rfl) ⟨1876472, by rfl⟩ : syracuseStep 2501963 = 3752945) B3752945
theorem B2501975 : Blo 1666533 2501975 := bstep (se 1 (by rfl) ⟨1876481, by rfl⟩ : syracuseStep 2501975 = 3752963) B3752963
theorem B12021085 : Blo 1666533 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B2502041 : Blo 1666533 2502041 := bstep (se 2 (by rfl) ⟨938265, by rfl⟩ : syracuseStep 2502041 = 1876531) B1876531
theorem B1666539 : Blo 1666533 1666539 := bstep (se 1 (by rfl) ⟨1249904, by rfl⟩ : syracuseStep 1666539 = 2499809) B2499809
theorem B1666551 : Blo 1666533 1666551 := bstep (se 1 (by rfl) ⟨1249913, by rfl⟩ : syracuseStep 1666551 = 2499827) B2499827
theorem B1666571 : Blo 1666533 1666571 := bstep (se 1 (by rfl) ⟨1249928, by rfl⟩ : syracuseStep 1666571 = 2499857) B2499857
theorem B1666583 : Blo 1666533 1666583 := bstep (se 1 (by rfl) ⟨1249937, by rfl⟩ : syracuseStep 1666583 = 2499875) B2499875
theorem B1666603 : Blo 1666533 1666603 := bstep (se 1 (by rfl) ⟨1249952, by rfl⟩ : syracuseStep 1666603 = 2499905) B2499905
theorem B1666615 : Blo 1666533 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B14077505 : Blo 1666533 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B1666635 : Blo 1666533 1666635 := bstep (se 1 (by rfl) ⟨1249976, by rfl⟩ : syracuseStep 1666635 = 2499953) B2499953
theorem B12660299 : Blo 1666533 12660299 := bstep (se 1 (by rfl) ⟨9495224, by rfl⟩ : syracuseStep 12660299 = 18990449) B18990449
theorem B1666647 : Blo 1666533 1666647 := bstep (se 1 (by rfl) ⟨1249985, by rfl⟩ : syracuseStep 1666647 = 2499971) B2499971
theorem B1666667 : Blo 1666533 1666667 := bstep (se 1 (by rfl) ⟨1250000, by rfl⟩ : syracuseStep 1666667 = 2500001) B2500001
theorem B1666679 : Blo 1666533 1666679 := bstep (se 1 (by rfl) ⟨1250009, by rfl⟩ : syracuseStep 1666679 = 2500019) B2500019
theorem B1666699 : Blo 1666533 1666699 := bstep (se 1 (by rfl) ⟨1250024, by rfl⟩ : syracuseStep 1666699 = 2500049) B2500049
theorem B1666711 : Blo 1666533 1666711 := bstep (se 1 (by rfl) ⟨1250033, by rfl⟩ : syracuseStep 1666711 = 2500067) B2500067
theorem B8441495 : Blo 1666533 8441495 := bstep (se 1 (by rfl) ⟨6331121, by rfl⟩ : syracuseStep 8441495 = 12662243) B12662243
theorem B1666731 : Blo 1666533 1666731 := bstep (se 1 (by rfl) ⟨1250048, by rfl⟩ : syracuseStep 1666731 = 2500097) B2500097
theorem B1666743 : Blo 1666533 1666743 := bstep (se 1 (by rfl) ⟨1250057, by rfl⟩ : syracuseStep 1666743 = 2500115) B2500115
theorem B1666763 : Blo 1666533 1666763 := bstep (se 1 (by rfl) ⟨1250072, by rfl⟩ : syracuseStep 1666763 = 2500145) B2500145
theorem B1666775 : Blo 1666533 1666775 := bstep (se 1 (by rfl) ⟨1250081, by rfl⟩ : syracuseStep 1666775 = 2500163) B2500163
theorem B7122649 : Blo 1666533 7122649 := bstep (se 2 (by rfl) ⟨2670993, by rfl⟩ : syracuseStep 7122649 = 5341987) B5341987
theorem B1666795 : Blo 1666533 1666795 := bstep (se 1 (by rfl) ⟨1250096, by rfl⟩ : syracuseStep 1666795 = 2500193) B2500193
theorem B1666807 : Blo 1666533 1666807 := bstep (se 1 (by rfl) ⟨1250105, by rfl⟩ : syracuseStep 1666807 = 2500211) B2500211
theorem B1666827 : Blo 1666533 1666827 := bstep (se 1 (by rfl) ⟨1250120, by rfl⟩ : syracuseStep 1666827 = 2500241) B2500241
theorem B1666839 : Blo 1666533 1666839 := bstep (se 1 (by rfl) ⟨1250129, by rfl⟩ : syracuseStep 1666839 = 2500259) B2500259
theorem B1666859 : Blo 1666533 1666859 := bstep (se 1 (by rfl) ⟨1250144, by rfl⟩ : syracuseStep 1666859 = 2500289) B2500289
theorem B6328115 : Blo 1666533 6328115 := bstep (se 1 (by rfl) ⟨4746086, by rfl⟩ : syracuseStep 6328115 = 9492173) B9492173
theorem B1666871 : Blo 1666533 1666871 := bstep (se 1 (by rfl) ⟨1250153, by rfl⟩ : syracuseStep 1666871 = 2500307) B2500307
theorem B1666891 : Blo 1666533 1666891 := bstep (se 1 (by rfl) ⟨1250168, by rfl⟩ : syracuseStep 1666891 = 2500337) B2500337
theorem B2813771 : Blo 1666533 2813771 := bstep (se 1 (by rfl) ⟨2110328, by rfl⟩ : syracuseStep 2813771 = 4220657) B4220657
theorem B1666903 : Blo 1666533 1666903 := bstep (se 1 (by rfl) ⟨1250177, by rfl⟩ : syracuseStep 1666903 = 2500355) B2500355
theorem B749940581 : Blo 1666533 749940581 := bstep (se 4 (by rfl) ⟨70306929, by rfl⟩ : syracuseStep 749940581 = 140613859) B140613859
theorem B1666923 : Blo 1666533 1666923 := bstep (se 1 (by rfl) ⟨1250192, by rfl⟩ : syracuseStep 1666923 = 2500385) B2500385
theorem B1666935 : Blo 1666533 1666935 := bstep (se 1 (by rfl) ⟨1250201, by rfl⟩ : syracuseStep 1666935 = 2500403) B2500403
theorem B1666955 : Blo 1666533 1666955 := bstep (se 1 (by rfl) ⟨1250216, by rfl⟩ : syracuseStep 1666955 = 2500433) B2500433
theorem B1666967 : Blo 1666533 1666967 := bstep (se 1 (by rfl) ⟨1250225, by rfl⟩ : syracuseStep 1666967 = 2500451) B2500451
theorem B1666987 : Blo 1666533 1666987 := bstep (se 1 (by rfl) ⟨1250240, by rfl⟩ : syracuseStep 1666987 = 2500481) B2500481
theorem B1666999 : Blo 1666533 1666999 := bstep (se 1 (by rfl) ⟨1250249, by rfl⟩ : syracuseStep 1666999 = 2500499) B2500499
theorem B1667019 : Blo 1666533 1667019 := bstep (se 1 (by rfl) ⟨1250264, by rfl⟩ : syracuseStep 1667019 = 2500529) B2500529
theorem B2813899 : Blo 1666533 2813899 := bstep (se 1 (by rfl) ⟨2110424, by rfl⟩ : syracuseStep 2813899 = 4220849) B4220849
theorem B7606219 : Blo 1666533 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B1667031 : Blo 1666533 1667031 := bstep (se 1 (by rfl) ⟨1250273, by rfl⟩ : syracuseStep 1667031 = 2500547) B2500547
theorem B14249945 : Blo 1666533 14249945 := bstep (se 2 (by rfl) ⟨5343729, by rfl⟩ : syracuseStep 14249945 = 10687459) B10687459
theorem B1667051 : Blo 1666533 1667051 := bstep (se 1 (by rfl) ⟨1250288, by rfl⟩ : syracuseStep 1667051 = 2500577) B2500577
theorem B3559411 : Blo 1666533 3559411 := bstep (se 1 (by rfl) ⟨2669558, by rfl⟩ : syracuseStep 3559411 = 5339117) B5339117
theorem B1667063 : Blo 1666533 1667063 := bstep (se 1 (by rfl) ⟨1250297, by rfl⟩ : syracuseStep 1667063 = 2500595) B2500595
theorem B7221251 : Blo 1666533 7221251 := bstep (se 1 (by rfl) ⟨5415938, by rfl⟩ : syracuseStep 7221251 = 10831877) B10831877
theorem B1667083 : Blo 1666533 1667083 := bstep (se 1 (by rfl) ⟨1250312, by rfl⟩ : syracuseStep 1667083 = 2500625) B2500625
theorem B1667095 : Blo 1666533 1667095 := bstep (se 1 (by rfl) ⟨1250321, by rfl⟩ : syracuseStep 1667095 = 2500643) B2500643
theorem B1667115 : Blo 1666533 1667115 := bstep (se 1 (by rfl) ⟨1250336, by rfl⟩ : syracuseStep 1667115 = 2500673) B2500673
theorem B1667127 : Blo 1666533 1667127 := bstep (se 1 (by rfl) ⟨1250345, by rfl⟩ : syracuseStep 1667127 = 2500691) B2500691
theorem B10678337 : Blo 1666533 10678337 := bstep (se 2 (by rfl) ⟨4004376, by rfl⟩ : syracuseStep 10678337 = 8008753) B8008753
theorem B4747339 : Blo 1666533 4747339 := bstep (se 1 (by rfl) ⟨3560504, by rfl⟩ : syracuseStep 4747339 = 7121009) B7121009
theorem B1667147 : Blo 1666533 1667147 := bstep (se 1 (by rfl) ⟨1250360, by rfl⟩ : syracuseStep 1667147 = 2500721) B2500721
theorem B3166283 : Blo 1666533 3166283 := bstep (se 1 (by rfl) ⟨2374712, by rfl⟩ : syracuseStep 3166283 = 4749425) B4749425
theorem B1667159 : Blo 1666533 1667159 := bstep (se 1 (by rfl) ⟨1250369, by rfl⟩ : syracuseStep 1667159 = 2500739) B2500739
theorem B2814041 : Blo 1666533 2814041 := bstep (se 2 (by rfl) ⟨1055265, by rfl⟩ : syracuseStep 2814041 = 2110531) B2110531
theorem B1667179 : Blo 1666533 1667179 := bstep (se 1 (by rfl) ⟨1250384, by rfl⟩ : syracuseStep 1667179 = 2500769) B2500769
theorem B1667191 : Blo 1666533 1667191 := bstep (se 1 (by rfl) ⟨1250393, by rfl⟩ : syracuseStep 1667191 = 2500787) B2500787
theorem B1667211 : Blo 1666533 1667211 := bstep (se 1 (by rfl) ⟨1250408, by rfl⟩ : syracuseStep 1667211 = 2500817) B2500817
theorem B1667223 : Blo 1666533 1667223 := bstep (se 1 (by rfl) ⟨1250417, by rfl⟩ : syracuseStep 1667223 = 2500835) B2500835
theorem B1667243 : Blo 1666533 1667243 := bstep (se 1 (by rfl) ⟨1250432, by rfl⟩ : syracuseStep 1667243 = 2500865) B2500865
theorem B28487861 : Blo 1666533 28487861 := bstep (se 5 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 28487861 = 2670737) B2670737
theorem B1667255 : Blo 1666533 1667255 := bstep (se 1 (by rfl) ⟨1250441, by rfl⟩ : syracuseStep 1667255 = 2500883) B2500883
theorem B1667275 : Blo 1666533 1667275 := bstep (se 1 (by rfl) ⟨1250456, by rfl⟩ : syracuseStep 1667275 = 2500913) B2500913
theorem B2109655 : Blo 1666533 2109655 := bstep (se 1 (by rfl) ⟨1582241, by rfl⟩ : syracuseStep 2109655 = 3164483) B3164483
theorem B1667287 : Blo 1666533 1667287 := bstep (se 1 (by rfl) ⟨1250465, by rfl⟩ : syracuseStep 1667287 = 2500931) B2500931
theorem B2814169 : Blo 1666533 2814169 := bstep (se 2 (by rfl) ⟨1055313, by rfl⟩ : syracuseStep 2814169 = 2110627) B2110627
theorem B1667307 : Blo 1666533 1667307 := bstep (se 1 (by rfl) ⟨1250480, by rfl⟩ : syracuseStep 1667307 = 2500961) B2500961
theorem B1667319 : Blo 1666533 1667319 := bstep (se 1 (by rfl) ⟨1250489, by rfl⟩ : syracuseStep 1667319 = 2500979) B2500979
theorem B3379457 : Blo 1666533 3379457 := bstep (se 2 (by rfl) ⟨1267296, by rfl⟩ : syracuseStep 3379457 = 2534593) B2534593
theorem B3166465 : Blo 1666533 3166465 := bstep (se 2 (by rfl) ⟨1187424, by rfl⟩ : syracuseStep 3166465 = 2374849) B2374849
theorem B1667339 : Blo 1666533 1667339 := bstep (se 1 (by rfl) ⟨1250504, by rfl⟩ : syracuseStep 1667339 = 2501009) B2501009
theorem B1667351 : Blo 1666533 1667351 := bstep (se 1 (by rfl) ⟨1250513, by rfl⟩ : syracuseStep 1667351 = 2501027) B2501027
theorem B1667371 : Blo 1666533 1667371 := bstep (se 1 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 1667371 = 2501057) B2501057
theorem B3207475 : Blo 1666533 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B1667383 : Blo 1666533 1667383 := bstep (se 1 (by rfl) ⟨1250537, by rfl⟩ : syracuseStep 1667383 = 2501075) B2501075
theorem B7123265 : Blo 1666533 7123265 := bstep (se 2 (by rfl) ⟨2671224, by rfl⟩ : syracuseStep 7123265 = 5342449) B5342449
theorem B1667403 : Blo 1666533 1667403 := bstep (se 1 (by rfl) ⟨1250552, by rfl⟩ : syracuseStep 1667403 = 2501105) B2501105
theorem B1667415 : Blo 1666533 1667415 := bstep (se 1 (by rfl) ⟨1250561, by rfl⟩ : syracuseStep 1667415 = 2501123) B2501123
theorem B1667435 : Blo 1666533 1667435 := bstep (se 1 (by rfl) ⟨1250576, by rfl⟩ : syracuseStep 1667435 = 2501153) B2501153
theorem B1667447 : Blo 1666533 1667447 := bstep (se 1 (by rfl) ⟨1250585, by rfl⟩ : syracuseStep 1667447 = 2501171) B2501171
theorem B1667467 : Blo 1666533 1667467 := bstep (se 1 (by rfl) ⟨1250600, by rfl⟩ : syracuseStep 1667467 = 2501201) B2501201
theorem B1667479 : Blo 1666533 1667479 := bstep (se 1 (by rfl) ⟨1250609, by rfl⟩ : syracuseStep 1667479 = 2501219) B2501219
theorem B9499031 : Blo 1666533 9499031 := bstep (se 1 (by rfl) ⟨7124273, by rfl⟩ : syracuseStep 9499031 = 14248547) B14248547
theorem B1667499 : Blo 1666533 1667499 := bstep (se 1 (by rfl) ⟨1250624, by rfl⟩ : syracuseStep 1667499 = 2501249) B2501249
theorem B9015731 : Blo 1666533 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B1667511 : Blo 1666533 1667511 := bstep (se 1 (by rfl) ⟨1250633, by rfl⟩ : syracuseStep 1667511 = 2501267) B2501267
theorem B1667531 : Blo 1666533 1667531 := bstep (se 1 (by rfl) ⟨1250648, by rfl⟩ : syracuseStep 1667531 = 2501297) B2501297
theorem B1667543 : Blo 1666533 1667543 := bstep (se 1 (by rfl) ⟨1250657, by rfl⟩ : syracuseStep 1667543 = 2501315) B2501315
theorem B1667563 : Blo 1666533 1667563 := bstep (se 1 (by rfl) ⟨1250672, by rfl⟩ : syracuseStep 1667563 = 2501345) B2501345
theorem B1667575 : Blo 1666533 1667575 := bstep (se 1 (by rfl) ⟨1250681, by rfl⟩ : syracuseStep 1667575 = 2501363) B2501363
theorem B1667595 : Blo 1666533 1667595 := bstep (se 1 (by rfl) ⟨1250696, by rfl⟩ : syracuseStep 1667595 = 2501393) B2501393
theorem B1667607 : Blo 1666533 1667607 := bstep (se 1 (by rfl) ⟨1250705, by rfl⟩ : syracuseStep 1667607 = 2501411) B2501411
theorem B1667627 : Blo 1666533 1667627 := bstep (se 1 (by rfl) ⟨1250720, by rfl⟩ : syracuseStep 1667627 = 2501441) B2501441
theorem B1667639 : Blo 1666533 1667639 := bstep (se 1 (by rfl) ⟨1250729, by rfl⟩ : syracuseStep 1667639 = 2501459) B2501459
theorem B4747841 : Blo 1666533 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B1667659 : Blo 1666533 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B1667671 : Blo 1666533 1667671 := bstep (se 1 (by rfl) ⟨1250753, by rfl⟩ : syracuseStep 1667671 = 2501507) B2501507
theorem B1667691 : Blo 1666533 1667691 := bstep (se 1 (by rfl) ⟨1250768, by rfl⟩ : syracuseStep 1667691 = 2501537) B2501537
theorem B1667703 : Blo 1666533 1667703 := bstep (se 1 (by rfl) ⟨1250777, by rfl⟩ : syracuseStep 1667703 = 2501555) B2501555
theorem B1667723 : Blo 1666533 1667723 := bstep (se 1 (by rfl) ⟨1250792, by rfl⟩ : syracuseStep 1667723 = 2501585) B2501585
theorem B3560087 : Blo 1666533 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B1667735 : Blo 1666533 1667735 := bstep (se 1 (by rfl) ⟨1250801, by rfl⟩ : syracuseStep 1667735 = 2501603) B2501603
theorem B1667755 : Blo 1666533 1667755 := bstep (se 1 (by rfl) ⟨1250816, by rfl⟩ : syracuseStep 1667755 = 2501633) B2501633
theorem B1667767 : Blo 1666533 1667767 := bstep (se 1 (by rfl) ⟨1250825, by rfl⟩ : syracuseStep 1667767 = 2501651) B2501651
theorem B3560129 : Blo 1666533 3560129 := bstep (se 2 (by rfl) ⟨1335048, by rfl⟩ : syracuseStep 3560129 = 2670097) B2670097
theorem B1667787 : Blo 1666533 1667787 := bstep (se 1 (by rfl) ⟨1250840, by rfl⟩ : syracuseStep 1667787 = 2501681) B2501681
theorem B1667799 : Blo 1666533 1667799 := bstep (se 1 (by rfl) ⟨1250849, by rfl⟩ : syracuseStep 1667799 = 2501699) B2501699
theorem B1667819 : Blo 1666533 1667819 := bstep (se 1 (by rfl) ⟨1250864, by rfl⟩ : syracuseStep 1667819 = 2501729) B2501729
theorem B1667831 : Blo 1666533 1667831 := bstep (se 1 (by rfl) ⟨1250873, by rfl⟩ : syracuseStep 1667831 = 2501747) B2501747
theorem B1667851 : Blo 1666533 1667851 := bstep (se 1 (by rfl) ⟨1250888, by rfl⟩ : syracuseStep 1667851 = 2501777) B2501777
theorem B1667863 : Blo 1666533 1667863 := bstep (se 1 (by rfl) ⟨1250897, by rfl⟩ : syracuseStep 1667863 = 2501795) B2501795
theorem B2814743 : Blo 1666533 2814743 := bstep (se 1 (by rfl) ⟨2111057, by rfl⟩ : syracuseStep 2814743 = 4222115) B4222115
theorem B1667883 : Blo 1666533 1667883 := bstep (se 1 (by rfl) ⟨1250912, by rfl⟩ : syracuseStep 1667883 = 2501825) B2501825
theorem B1667895 : Blo 1666533 1667895 := bstep (se 1 (by rfl) ⟨1250921, by rfl⟩ : syracuseStep 1667895 = 2501843) B2501843
theorem B1667915 : Blo 1666533 1667915 := bstep (se 1 (by rfl) ⟨1250936, by rfl⟩ : syracuseStep 1667915 = 2501873) B2501873
theorem B1667927 : Blo 1666533 1667927 := bstep (se 1 (by rfl) ⟨1250945, by rfl⟩ : syracuseStep 1667927 = 2501891) B2501891
theorem B1667947 : Blo 1666533 1667947 := bstep (se 1 (by rfl) ⟨1250960, by rfl⟩ : syracuseStep 1667947 = 2501921) B2501921
theorem B1667959 : Blo 1666533 1667959 := bstep (se 1 (by rfl) ⟨1250969, by rfl⟩ : syracuseStep 1667959 = 2501939) B2501939
theorem B1667979 : Blo 1666533 1667979 := bstep (se 1 (by rfl) ⟨1250984, by rfl⟩ : syracuseStep 1667979 = 2501969) B2501969
theorem B4748183 : Blo 1666533 4748183 := bstep (se 1 (by rfl) ⟨3561137, by rfl⟩ : syracuseStep 4748183 = 7122275) B7122275
theorem B1667991 : Blo 1666533 1667991 := bstep (se 1 (by rfl) ⟨1250993, by rfl⟩ : syracuseStep 1667991 = 2501987) B2501987
theorem B1668011 : Blo 1666533 1668011 := bstep (se 1 (by rfl) ⟨1251008, by rfl⟩ : syracuseStep 1668011 = 2502017) B2502017
theorem B12014513 : Blo 1666533 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B1668023 : Blo 1666533 1668023 := bstep (se 1 (by rfl) ⟨1251017, by rfl⟩ : syracuseStep 1668023 = 2502035) B2502035
theorem B2110475 : Blo 1666533 2110475 := bstep (se 1 (by rfl) ⟨1582856, by rfl⟩ : syracuseStep 2110475 = 3165713) B3165713
theorem B5624855 : Blo 1666533 5624855 := bstep (se 1 (by rfl) ⟨4218641, by rfl⟩ : syracuseStep 5624855 = 8437283) B8437283
theorem B4060211 : Blo 1666533 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B12833893 : Blo 1666533 12833893 := bstep (se 4 (by rfl) ⟨1203177, by rfl⟩ : syracuseStep 12833893 = 2406355) B2406355
theorem B3003571 : Blo 1666533 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B6329603 : Blo 1666533 6329603 := bstep (se 1 (by rfl) ⟨4747202, by rfl⟩ : syracuseStep 6329603 = 9494405) B9494405
theorem B5625395 : Blo 1666533 5625395 := bstep (se 1 (by rfl) ⟨4219046, by rfl⟩ : syracuseStep 5625395 = 8438093) B8438093
theorem B6330059 : Blo 1666533 6330059 := bstep (se 1 (by rfl) ⟨4747544, by rfl⟩ : syracuseStep 6330059 = 9495089) B9495089
theorem B5625665 : Blo 1666533 5625665 := bstep (se 2 (by rfl) ⟨2109624, by rfl⟩ : syracuseStep 5625665 = 4219249) B4219249
theorem B34223971 : Blo 1666533 34223971 := bstep (se 1 (by rfl) ⟨25667978, by rfl⟩ : syracuseStep 34223971 = 51335957) B51335957
theorem B6330257 : Blo 1666533 6330257 := bstep (se 2 (by rfl) ⟨2373846, by rfl⟩ : syracuseStep 6330257 = 4747693) B4747693
theorem B3749849 : Blo 1666533 3749849 := bstep (se 2 (by rfl) ⟨1406193, by rfl⟩ : syracuseStep 3749849 = 2812387) B2812387
theorem B13522949 : Blo 1666533 13522949 := bstep (se 4 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 13522949 = 2535553) B2535553
theorem B3749939 : Blo 1666533 3749939 := bstep (se 1 (by rfl) ⟨2812454, by rfl⟩ : syracuseStep 3749939 = 5624909) B5624909
theorem B3749975 : Blo 1666533 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B3004631 : Blo 1666533 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B3750155 : Blo 1666533 3750155 := bstep (se 1 (by rfl) ⟨2812616, by rfl⟩ : syracuseStep 3750155 = 5625233) B5625233
theorem B3750209 : Blo 1666533 3750209 := bstep (se 2 (by rfl) ⟨1406328, by rfl⟩ : syracuseStep 3750209 = 2812657) B2812657
theorem B5626205 : Blo 1666533 5626205 := bstep (se 3 (by rfl) ⟨1054913, by rfl⟩ : syracuseStep 5626205 = 2109827) B2109827
theorem B3086743 : Blo 1666533 3086743 := bstep (se 1 (by rfl) ⟨2315057, by rfl⟩ : syracuseStep 3086743 = 4630115) B4630115
theorem B3750425 : Blo 1666533 3750425 := bstep (se 2 (by rfl) ⟨1406409, by rfl⟩ : syracuseStep 3750425 = 2812819) B2812819
theorem B3750515 : Blo 1666533 3750515 := bstep (se 1 (by rfl) ⟨2812886, by rfl⟩ : syracuseStep 3750515 = 5625773) B5625773
theorem B3750551 : Blo 1666533 3750551 := bstep (se 1 (by rfl) ⟨2812913, by rfl⟩ : syracuseStep 3750551 = 5625827) B5625827
theorem B6331031 : Blo 1666533 6331031 := bstep (se 1 (by rfl) ⟨4748273, by rfl⟩ : syracuseStep 6331031 = 9496547) B9496547
theorem B4004531 : Blo 1666533 4004531 := bstep (se 1 (by rfl) ⟨3003398, by rfl⟩ : syracuseStep 4004531 = 6006797) B6006797
theorem B13703897 : Blo 1666533 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B10828505 : Blo 1666533 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B57744193 : Blo 1666533 57744193 := bstep (se 2 (by rfl) ⟨21654072, by rfl⟩ : syracuseStep 57744193 = 43308145) B43308145
theorem B3750731 : Blo 1666533 3750731 := bstep (se 1 (by rfl) ⟨2813048, by rfl⟩ : syracuseStep 3750731 = 5626097) B5626097
theorem B6331229 : Blo 1666533 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B3750785 : Blo 1666533 3750785 := bstep (se 2 (by rfl) ⟨1406544, by rfl⟩ : syracuseStep 3750785 = 2813089) B2813089
theorem B3521483 : Blo 1666533 3521483 := bstep (se 1 (by rfl) ⟨2641112, by rfl⟩ : syracuseStep 3521483 = 5282225) B5282225
theorem B1875019 : Blo 1666533 1875019 := bstep (se 1 (by rfl) ⟨1406264, by rfl⟩ : syracuseStep 1875019 = 2812529) B2812529
theorem B3751001 : Blo 1666533 3751001 := bstep (se 2 (by rfl) ⟨1406625, by rfl⟩ : syracuseStep 3751001 = 2813251) B2813251
theorem B3751091 : Blo 1666533 3751091 := bstep (se 1 (by rfl) ⟨2813318, by rfl⟩ : syracuseStep 3751091 = 5626637) B5626637
theorem B1875127 : Blo 1666533 1875127 := bstep (se 1 (by rfl) ⟨1406345, by rfl⟩ : syracuseStep 1875127 = 2812691) B2812691
theorem B3005633 : Blo 1666533 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B3751127 : Blo 1666533 3751127 := bstep (se 1 (by rfl) ⟨2813345, by rfl⟩ : syracuseStep 3751127 = 5626691) B5626691
theorem B4504793 : Blo 1666533 4504793 := bstep (se 2 (by rfl) ⟨1689297, by rfl⟩ : syracuseStep 4504793 = 3378595) B3378595
theorem B13524241 : Blo 1666533 13524241 := bstep (se 2 (by rfl) ⟨5071590, by rfl⟩ : syracuseStep 13524241 = 10143181) B10143181
theorem B27049261 : Blo 1666533 27049261 := bstep (se 3 (by rfl) ⟨5071736, by rfl⟩ : syracuseStep 27049261 = 10143473) B10143473
theorem B30432611 : Blo 1666533 30432611 := bstep (se 1 (by rfl) ⟨22824458, by rfl⟩ : syracuseStep 30432611 = 45648917) B45648917
theorem B12016997 : Blo 1666533 12016997 := bstep (se 4 (by rfl) ⟨1126593, by rfl⟩ : syracuseStep 12016997 = 2253187) B2253187
theorem B1875307 : Blo 1666533 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B3751307 : Blo 1666533 3751307 := bstep (se 1 (by rfl) ⟨2813480, by rfl⟩ : syracuseStep 3751307 = 5626961) B5626961
theorem B6757825 : Blo 1666533 6757825 := bstep (se 2 (by rfl) ⟨2534184, by rfl⟩ : syracuseStep 6757825 = 5068369) B5068369
theorem B3751361 : Blo 1666533 3751361 := bstep (se 2 (by rfl) ⟨1406760, by rfl⟩ : syracuseStep 3751361 = 2813521) B2813521
theorem B5627339 : Blo 1666533 5627339 := bstep (se 1 (by rfl) ⟨4220504, by rfl⟩ : syracuseStep 5627339 = 8441009) B8441009
theorem B1875415 : Blo 1666533 1875415 := bstep (se 1 (by rfl) ⟨1406561, by rfl⟩ : syracuseStep 1875415 = 2813123) B2813123
theorem B4005337 : Blo 1666533 4005337 := bstep (se 2 (by rfl) ⟨1502001, by rfl⟩ : syracuseStep 4005337 = 3004003) B3004003
theorem B10681901 : Blo 1666533 10681901 := bstep (se 3 (by rfl) ⟨2002856, by rfl⟩ : syracuseStep 10681901 = 4005713) B4005713
theorem B4218419 : Blo 1666533 4218419 := bstep (se 1 (by rfl) ⟨3163814, by rfl⟩ : syracuseStep 4218419 = 6327629) B6327629
theorem B1875595 : Blo 1666533 1875595 := bstep (se 1 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 1875595 = 2813393) B2813393
theorem B3751577 : Blo 1666533 3751577 := bstep (se 2 (by rfl) ⟨1406841, by rfl⟩ : syracuseStep 3751577 = 2813683) B2813683
theorem B5627609 : Blo 1666533 5627609 := bstep (se 2 (by rfl) ⟨2110353, by rfl⟩ : syracuseStep 5627609 = 4220707) B4220707
theorem B3751667 : Blo 1666533 3751667 := bstep (se 1 (by rfl) ⟨2813750, by rfl⟩ : syracuseStep 3751667 = 5627501) B5627501
theorem B1875703 : Blo 1666533 1875703 := bstep (se 1 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 1875703 = 2813555) B2813555
theorem B3751703 : Blo 1666533 3751703 := bstep (se 1 (by rfl) ⟨2813777, by rfl⟩ : syracuseStep 3751703 = 5627555) B5627555
theorem B7601971 : Blo 1666533 7601971 := bstep (se 1 (by rfl) ⟨5701478, by rfl⟩ : syracuseStep 7601971 = 11402957) B11402957
theorem B4218713 : Blo 1666533 4218713 := bstep (se 2 (by rfl) ⟨1582017, by rfl⟩ : syracuseStep 4218713 = 3164035) B3164035
theorem B1875883 : Blo 1666533 1875883 := bstep (se 1 (by rfl) ⟨1406912, by rfl⟩ : syracuseStep 1875883 = 2813825) B2813825
theorem B24035251 : Blo 1666533 24035251 := bstep (se 1 (by rfl) ⟨18026438, by rfl⟩ : syracuseStep 24035251 = 36052877) B36052877
theorem B3751883 : Blo 1666533 3751883 := bstep (se 1 (by rfl) ⟨2813912, by rfl⟩ : syracuseStep 3751883 = 5627825) B5627825
theorem B5627933 : Blo 1666533 5627933 := bstep (se 3 (by rfl) ⟨1055237, by rfl⟩ : syracuseStep 5627933 = 2110475) B2110475
theorem B7118891 : Blo 1666533 7118891 := bstep (se 1 (by rfl) ⟨5339168, by rfl⟩ : syracuseStep 7118891 = 10678337) B10678337
theorem B2670635 : Blo 1666533 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1876027 : Blo 1666533 1876027 := bstep (se 1 (by rfl) ⟨1407020, by rfl⟩ : syracuseStep 1876027 = 2814041) B2814041
theorem B2252971 : Blo 1666533 2252971 := bstep (se 1 (by rfl) ⟨1689728, by rfl⟩ : syracuseStep 2252971 = 3379457) B3379457
theorem B41099437 : Blo 1666533 41099437 := bstep (se 3 (by rfl) ⟨7706144, by rfl⟩ : syracuseStep 41099437 = 15412289) B15412289
theorem B3752207 : Blo 1666533 3752207 := bstep (se 1 (by rfl) ⟨2814155, by rfl⟩ : syracuseStep 3752207 = 5628311) B5628311
theorem B6332687 : Blo 1666533 6332687 := bstep (se 1 (by rfl) ⟨4749515, by rfl⟩ : syracuseStep 6332687 = 9499031) B9499031
theorem B3752225 : Blo 1666533 3752225 := bstep (se 2 (by rfl) ⟨1407084, by rfl⟩ : syracuseStep 3752225 = 2814169) B2814169
theorem B4276633 : Blo 1666533 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B20283833 : Blo 1666533 20283833 := bstep (se 2 (by rfl) ⟨7606437, by rfl⟩ : syracuseStep 20283833 = 15212875) B15212875
theorem B1876495 : Blo 1666533 1876495 := bstep (se 1 (by rfl) ⟨1407371, by rfl⟩ : syracuseStep 1876495 = 2814743) B2814743
theorem B3752567 : Blo 1666533 3752567 := bstep (se 1 (by rfl) ⟨2814425, by rfl⟩ : syracuseStep 3752567 = 5628851) B5628851
theorem B3752747 : Blo 1666533 3752747 := bstep (se 1 (by rfl) ⟨2814560, by rfl⟩ : syracuseStep 3752747 = 5629121) B5629121
theorem B8438579 : Blo 1666533 8438579 := bstep (se 1 (by rfl) ⟨6328934, by rfl⟩ : syracuseStep 8438579 = 12657869) B12657869
theorem B4219735 : Blo 1666533 4219735 := bstep (se 1 (by rfl) ⟨3164801, by rfl⟩ : syracuseStep 4219735 = 6329603) B6329603
theorem B5342219 : Blo 1666533 5342219 := bstep (se 1 (by rfl) ⟨4006664, by rfl⟩ : syracuseStep 5342219 = 8013329) B8013329
theorem B6505559 : Blo 1666533 6505559 := bstep (se 1 (by rfl) ⟨4879169, by rfl⟩ : syracuseStep 6505559 = 9758339) B9758339
theorem B8438903 : Blo 1666533 8438903 := bstep (se 1 (by rfl) ⟨6329177, by rfl⟩ : syracuseStep 8438903 = 12658355) B12658355
theorem B4220039 : Blo 1666533 4220039 := bstep (se 1 (by rfl) ⟨3165029, by rfl⟩ : syracuseStep 4220039 = 6330059) B6330059
theorem B2254009 : Blo 1666533 2254009 := bstep (se 2 (by rfl) ⟨845253, by rfl⟩ : syracuseStep 2254009 = 1690507) B1690507
theorem B4220171 : Blo 1666533 4220171 := bstep (se 1 (by rfl) ⟨3165128, by rfl⟩ : syracuseStep 4220171 = 6330257) B6330257
theorem B2499899 : Blo 1666533 2499899 := bstep (se 1 (by rfl) ⟨1874924, by rfl⟩ : syracuseStep 2499899 = 3749849) B3749849
theorem B2499959 : Blo 1666533 2499959 := bstep (se 1 (by rfl) ⟨1874969, by rfl⟩ : syracuseStep 2499959 = 3749939) B3749939
theorem B2499983 : Blo 1666533 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B5629337 : Blo 1666533 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B2500025 : Blo 1666533 2500025 := bstep (se 2 (by rfl) ⟨937509, by rfl⟩ : syracuseStep 2500025 = 1875019) B1875019
theorem B79136185 : Blo 1666533 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B2500103 : Blo 1666533 2500103 := bstep (se 1 (by rfl) ⟨1875077, by rfl⟩ : syracuseStep 2500103 = 3750155) B3750155
theorem B2500139 : Blo 1666533 2500139 := bstep (se 1 (by rfl) ⟨1875104, by rfl⟩ : syracuseStep 2500139 = 3750209) B3750209
theorem B36537925 : Blo 1666533 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B2500169 : Blo 1666533 2500169 := bstep (se 2 (by rfl) ⟨937563, by rfl⟩ : syracuseStep 2500169 = 1875127) B1875127
theorem B5342807 : Blo 1666533 5342807 := bstep (se 1 (by rfl) ⟨4007105, by rfl⟩ : syracuseStep 5342807 = 8014211) B8014211
theorem B2500283 : Blo 1666533 2500283 := bstep (se 1 (by rfl) ⟨1875212, by rfl⟩ : syracuseStep 2500283 = 3750425) B3750425
theorem B18032321 : Blo 1666533 18032321 := bstep (se 2 (by rfl) ⟨6762120, by rfl⟩ : syracuseStep 18032321 = 13524241) B13524241
theorem B2500343 : Blo 1666533 2500343 := bstep (se 1 (by rfl) ⟨1875257, by rfl⟩ : syracuseStep 2500343 = 3750515) B3750515
theorem B2500367 : Blo 1666533 2500367 := bstep (se 1 (by rfl) ⟨1875275, by rfl⟩ : syracuseStep 2500367 = 3750551) B3750551
theorem B4220687 : Blo 1666533 4220687 := bstep (se 1 (by rfl) ⟨3165515, by rfl⟩ : syracuseStep 4220687 = 6331031) B6331031
theorem B28870451 : Blo 1666533 28870451 := bstep (se 1 (by rfl) ⟨21652838, by rfl⟩ : syracuseStep 28870451 = 43305677) B43305677
theorem B2500409 : Blo 1666533 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B9135931 : Blo 1666533 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B7219003 : Blo 1666533 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B2500487 : Blo 1666533 2500487 := bstep (se 1 (by rfl) ⟨1875365, by rfl⟩ : syracuseStep 2500487 = 3750731) B3750731
theorem B4220819 : Blo 1666533 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B2500523 : Blo 1666533 2500523 := bstep (se 1 (by rfl) ⟨1875392, by rfl⟩ : syracuseStep 2500523 = 3750785) B3750785
theorem B2500553 : Blo 1666533 2500553 := bstep (se 2 (by rfl) ⟨937707, by rfl⟩ : syracuseStep 2500553 = 1875415) B1875415
theorem B2500667 : Blo 1666533 2500667 := bstep (se 1 (by rfl) ⟨1875500, by rfl⟩ : syracuseStep 2500667 = 3751001) B3751001
theorem B8439875 : Blo 1666533 8439875 := bstep (se 1 (by rfl) ⟨6329906, by rfl⟩ : syracuseStep 8439875 = 12659813) B12659813
theorem B2500727 : Blo 1666533 2500727 := bstep (se 1 (by rfl) ⟨1875545, by rfl⟩ : syracuseStep 2500727 = 3751091) B3751091
theorem B2500751 : Blo 1666533 2500751 := bstep (se 1 (by rfl) ⟨1875563, by rfl⟩ : syracuseStep 2500751 = 3751127) B3751127
theorem B2500793 : Blo 1666533 2500793 := bstep (se 2 (by rfl) ⟨937797, by rfl⟩ : syracuseStep 2500793 = 1875595) B1875595
theorem B2500871 : Blo 1666533 2500871 := bstep (se 1 (by rfl) ⟨1875653, by rfl⟩ : syracuseStep 2500871 = 3751307) B3751307
theorem B9496865 : Blo 1666533 9496865 := bstep (se 2 (by rfl) ⟨3561324, by rfl⟩ : syracuseStep 9496865 = 7122649) B7122649
theorem B2500907 : Blo 1666533 2500907 := bstep (se 1 (by rfl) ⟨1875680, by rfl⟩ : syracuseStep 2500907 = 3751361) B3751361
theorem B2500937 : Blo 1666533 2500937 := bstep (se 2 (by rfl) ⟨937851, by rfl⟩ : syracuseStep 2500937 = 1875703) B1875703
theorem B7121267 : Blo 1666533 7121267 := bstep (se 1 (by rfl) ⟨5340950, by rfl⟩ : syracuseStep 7121267 = 10681901) B10681901
theorem B2812279 : Blo 1666533 2812279 := bstep (se 1 (by rfl) ⟨2109209, by rfl⟩ : syracuseStep 2812279 = 4218419) B4218419
theorem B8440199 : Blo 1666533 8440199 := bstep (se 1 (by rfl) ⟨6330149, by rfl⟩ : syracuseStep 8440199 = 12660299) B12660299
theorem B10135961 : Blo 1666533 10135961 := bstep (se 2 (by rfl) ⟨3800985, by rfl⟩ : syracuseStep 10135961 = 7601971) B7601971
theorem B2501051 : Blo 1666533 2501051 := bstep (se 1 (by rfl) ⟨1875788, by rfl⟩ : syracuseStep 2501051 = 3751577) B3751577
theorem B45631961 : Blo 1666533 45631961 := bstep (se 2 (by rfl) ⟨17111985, by rfl⟩ : syracuseStep 45631961 = 34223971) B34223971
theorem B2501111 : Blo 1666533 2501111 := bstep (se 1 (by rfl) ⟨1875833, by rfl⟩ : syracuseStep 2501111 = 3751667) B3751667
theorem B2501135 : Blo 1666533 2501135 := bstep (se 1 (by rfl) ⟨1875851, by rfl⟩ : syracuseStep 2501135 = 3751703) B3751703
theorem B2501177 : Blo 1666533 2501177 := bstep (se 2 (by rfl) ⟨937941, by rfl⟩ : syracuseStep 2501177 = 1875883) B1875883
theorem B2812475 : Blo 1666533 2812475 := bstep (se 1 (by rfl) ⟨2109356, by rfl⟩ : syracuseStep 2812475 = 4218713) B4218713
theorem B499960387 : Blo 1666533 499960387 := bstep (se 1 (by rfl) ⟨374970290, by rfl⟩ : syracuseStep 499960387 = 749940581) B749940581
theorem B2501255 : Blo 1666533 2501255 := bstep (se 1 (by rfl) ⟨1875941, by rfl⟩ : syracuseStep 2501255 = 3751883) B3751883
theorem B4745881 : Blo 1666533 4745881 := bstep (se 2 (by rfl) ⟨1779705, by rfl⟩ : syracuseStep 4745881 = 3559411) B3559411
theorem B2501291 : Blo 1666533 2501291 := bstep (se 1 (by rfl) ⟨1875968, by rfl⟩ : syracuseStep 2501291 = 3751937) B3751937
theorem B2501321 : Blo 1666533 2501321 := bstep (se 2 (by rfl) ⟨937995, by rfl⟩ : syracuseStep 2501321 = 1875991) B1875991
theorem B18991907 : Blo 1666533 18991907 := bstep (se 1 (by rfl) ⟨14243930, by rfl⟩ : syracuseStep 18991907 = 28487861) B28487861
theorem B2501435 : Blo 1666533 2501435 := bstep (se 1 (by rfl) ⟨1876076, by rfl⟩ : syracuseStep 2501435 = 3752153) B3752153
theorem B23751539 : Blo 1666533 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B2501495 : Blo 1666533 2501495 := bstep (se 1 (by rfl) ⟨1876121, by rfl⟩ : syracuseStep 2501495 = 3752243) B3752243
theorem B2501519 : Blo 1666533 2501519 := bstep (se 1 (by rfl) ⟨1876139, by rfl⟩ : syracuseStep 2501519 = 3752279) B3752279
theorem B2501561 : Blo 1666533 2501561 := bstep (se 2 (by rfl) ⟨938085, by rfl⟩ : syracuseStep 2501561 = 1876171) B1876171
theorem B2812873 : Blo 1666533 2812873 := bstep (se 2 (by rfl) ⟨1054827, by rfl⟩ : syracuseStep 2812873 = 2109655) B2109655
theorem B4221953 : Blo 1666533 4221953 := bstep (se 2 (by rfl) ⟨1583232, by rfl⟩ : syracuseStep 4221953 = 3166465) B3166465
theorem B2501639 : Blo 1666533 2501639 := bstep (se 1 (by rfl) ⟨1876229, by rfl⟩ : syracuseStep 2501639 = 3752459) B3752459
theorem B4746269 : Blo 1666533 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B3165227 : Blo 1666533 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B2501675 : Blo 1666533 2501675 := bstep (se 1 (by rfl) ⟨1876256, by rfl⟩ : syracuseStep 2501675 = 3752513) B3752513
theorem B1780795 : Blo 1666533 1780795 := bstep (se 1 (by rfl) ⟨1335596, by rfl⟩ : syracuseStep 1780795 = 2671193) B2671193
theorem B2501705 : Blo 1666533 2501705 := bstep (se 2 (by rfl) ⟨938139, by rfl⟩ : syracuseStep 2501705 = 1876279) B1876279
theorem B64990349 : Blo 1666533 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B8015021 : Blo 1666533 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B2501819 : Blo 1666533 2501819 := bstep (se 1 (by rfl) ⟨1876364, by rfl⟩ : syracuseStep 2501819 = 3752729) B3752729
theorem B68447429 : Blo 1666533 68447429 := bstep (se 4 (by rfl) ⟨6416946, by rfl⟩ : syracuseStep 68447429 = 12833893) B12833893
theorem B4115657 : Blo 1666533 4115657 := bstep (se 2 (by rfl) ⟨1543371, by rfl⟩ : syracuseStep 4115657 = 3086743) B3086743
theorem B12012781 : Blo 1666533 12012781 := bstep (se 3 (by rfl) ⟨2252396, by rfl⟩ : syracuseStep 12012781 = 4504793) B4504793
theorem B2501879 : Blo 1666533 2501879 := bstep (se 1 (by rfl) ⟨1876409, by rfl⟩ : syracuseStep 2501879 = 3752819) B3752819
theorem B3165455 : Blo 1666533 3165455 := bstep (se 1 (by rfl) ⟨2374091, by rfl⟩ : syracuseStep 3165455 = 4748183) B4748183
theorem B2501903 : Blo 1666533 2501903 := bstep (se 1 (by rfl) ⟨1876427, by rfl⟩ : syracuseStep 2501903 = 3752855) B3752855
theorem B2501945 : Blo 1666533 2501945 := bstep (se 2 (by rfl) ⟨938229, by rfl⟩ : syracuseStep 2501945 = 1876459) B1876459
theorem B2502023 : Blo 1666533 2502023 := bstep (se 1 (by rfl) ⟨1876517, by rfl⟩ : syracuseStep 2502023 = 3753035) B3753035
theorem B17346001 : Blo 1666533 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B1666567 : Blo 1666533 1666567 := bstep (se 1 (by rfl) ⟨1249925, by rfl⟩ : syracuseStep 1666567 = 2499851) B2499851
theorem B1666575 : Blo 1666533 1666575 := bstep (se 1 (by rfl) ⟨1249931, by rfl⟩ : syracuseStep 1666575 = 2499863) B2499863
theorem B1666619 : Blo 1666533 1666619 := bstep (se 1 (by rfl) ⟨1249964, by rfl⟩ : syracuseStep 1666619 = 2499929) B2499929
theorem B16019045 : Blo 1666533 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B1666695 : Blo 1666533 1666695 := bstep (se 1 (by rfl) ⟨1250021, by rfl⟩ : syracuseStep 1666695 = 2500043) B2500043
theorem B2813575 : Blo 1666533 2813575 := bstep (se 1 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 2813575 = 4220363) B4220363
theorem B1666703 : Blo 1666533 1666703 := bstep (se 1 (by rfl) ⟨1250027, by rfl⟩ : syracuseStep 1666703 = 2500055) B2500055
theorem B1666747 : Blo 1666533 1666747 := bstep (se 1 (by rfl) ⟨1250060, by rfl⟩ : syracuseStep 1666747 = 2500121) B2500121
theorem B76992257 : Blo 1666533 76992257 := bstep (se 2 (by rfl) ⟨28872096, by rfl⟩ : syracuseStep 76992257 = 57744193) B57744193
theorem B1666823 : Blo 1666533 1666823 := bstep (se 1 (by rfl) ⟨1250117, by rfl⟩ : syracuseStep 1666823 = 2500235) B2500235
theorem B1666831 : Blo 1666533 1666831 := bstep (se 1 (by rfl) ⟨1250123, by rfl⟩ : syracuseStep 1666831 = 2500247) B2500247
theorem B1666875 : Blo 1666533 1666875 := bstep (se 1 (by rfl) ⟨1250156, by rfl⟩ : syracuseStep 1666875 = 2500313) B2500313
theorem B1666951 : Blo 1666533 1666951 := bstep (se 1 (by rfl) ⟨1250213, by rfl⟩ : syracuseStep 1666951 = 2500427) B2500427
theorem B1666959 : Blo 1666533 1666959 := bstep (se 1 (by rfl) ⟨1250219, by rfl⟩ : syracuseStep 1666959 = 2500439) B2500439
theorem B5353363 : Blo 1666533 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B1667003 : Blo 1666533 1667003 := bstep (se 1 (by rfl) ⟨1250252, by rfl⟩ : syracuseStep 1667003 = 2500505) B2500505
theorem B9015299 : Blo 1666533 9015299 := bstep (se 1 (by rfl) ⟨6761474, by rfl⟩ : syracuseStep 9015299 = 13522949) B13522949
theorem B1667079 : Blo 1666533 1667079 := bstep (se 1 (by rfl) ⟨1250309, by rfl⟩ : syracuseStep 1667079 = 2500619) B2500619
theorem B6008843 : Blo 1666533 6008843 := bstep (se 1 (by rfl) ⟨4506632, by rfl⟩ : syracuseStep 6008843 = 9013265) B9013265
theorem B1667087 : Blo 1666533 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1667131 : Blo 1666533 1667131 := bstep (se 1 (by rfl) ⟨1250348, by rfl⟩ : syracuseStep 1667131 = 2500697) B2500697
theorem B2109559 : Blo 1666533 2109559 := bstep (se 1 (by rfl) ⟨1582169, by rfl⟩ : syracuseStep 2109559 = 3164339) B3164339
theorem B1667207 : Blo 1666533 1667207 := bstep (se 1 (by rfl) ⟨1250405, by rfl⟩ : syracuseStep 1667207 = 2500811) B2500811
theorem B1667215 : Blo 1666533 1667215 := bstep (se 1 (by rfl) ⟨1250411, by rfl⟩ : syracuseStep 1667215 = 2500823) B2500823
theorem B2003087 : Blo 1666533 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B1667259 : Blo 1666533 1667259 := bstep (se 1 (by rfl) ⟨1250444, by rfl⟩ : syracuseStep 1667259 = 2500889) B2500889
theorem B1667335 : Blo 1666533 1667335 := bstep (se 1 (by rfl) ⟨1250501, by rfl⟩ : syracuseStep 1667335 = 2501003) B2501003
theorem B1667343 : Blo 1666533 1667343 := bstep (se 1 (by rfl) ⟨1250507, by rfl⟩ : syracuseStep 1667343 = 2501015) B2501015
theorem B2814223 : Blo 1666533 2814223 := bstep (se 1 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 2814223 = 4221335) B4221335
theorem B1667387 : Blo 1666533 1667387 := bstep (se 1 (by rfl) ⟨1250540, by rfl⟩ : syracuseStep 1667387 = 2501081) B2501081
theorem B1667463 : Blo 1666533 1667463 := bstep (se 1 (by rfl) ⟨1250597, by rfl⟩ : syracuseStep 1667463 = 2501195) B2501195
theorem B1667471 : Blo 1666533 1667471 := bstep (se 1 (by rfl) ⟨1250603, by rfl⟩ : syracuseStep 1667471 = 2501207) B2501207
theorem B36065681 : Blo 1666533 36065681 := bstep (se 2 (by rfl) ⟨13524630, by rfl⟩ : syracuseStep 36065681 = 27049261) B27049261
theorem B6762899 : Blo 1666533 6762899 := bstep (se 1 (by rfl) ⟨5072174, by rfl⟩ : syracuseStep 6762899 = 10144349) B10144349
theorem B2109883 : Blo 1666533 2109883 := bstep (se 1 (by rfl) ⟨1582412, by rfl⟩ : syracuseStep 2109883 = 3164825) B3164825
theorem B1667515 : Blo 1666533 1667515 := bstep (se 1 (by rfl) ⟨1250636, by rfl⟩ : syracuseStep 1667515 = 2501273) B2501273
theorem B16028113 : Blo 1666533 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1667591 : Blo 1666533 1667591 := bstep (se 1 (by rfl) ⟨1250693, by rfl⟩ : syracuseStep 1667591 = 2501387) B2501387
theorem B2535943 : Blo 1666533 2535943 := bstep (se 1 (by rfl) ⟨1901957, by rfl⟩ : syracuseStep 2535943 = 3803915) B3803915
theorem B1667599 : Blo 1666533 1667599 := bstep (se 1 (by rfl) ⟨1250699, by rfl⟩ : syracuseStep 1667599 = 2501399) B2501399
theorem B1667643 : Blo 1666533 1667643 := bstep (se 1 (by rfl) ⟨1250732, by rfl⟩ : syracuseStep 1667643 = 2501465) B2501465
theorem B1667719 : Blo 1666533 1667719 := bstep (se 1 (by rfl) ⟨1250789, by rfl⟩ : syracuseStep 1667719 = 2501579) B2501579
theorem B2347655 : Blo 1666533 2347655 := bstep (se 1 (by rfl) ⟨1760741, by rfl⟩ : syracuseStep 2347655 = 3521483) B3521483
theorem B1667727 : Blo 1666533 1667727 := bstep (se 1 (by rfl) ⟨1250795, by rfl⟩ : syracuseStep 1667727 = 2501591) B2501591
theorem B1667771 : Blo 1666533 1667771 := bstep (se 1 (by rfl) ⟨1250828, by rfl⟩ : syracuseStep 1667771 = 2501657) B2501657
theorem B1667847 : Blo 1666533 1667847 := bstep (se 1 (by rfl) ⟨1250885, by rfl⟩ : syracuseStep 1667847 = 2501771) B2501771
theorem B7123727 : Blo 1666533 7123727 := bstep (se 1 (by rfl) ⟨5342795, by rfl⟩ : syracuseStep 7123727 = 10685591) B10685591
theorem B1667855 : Blo 1666533 1667855 := bstep (se 1 (by rfl) ⟨1250891, by rfl⟩ : syracuseStep 1667855 = 2501783) B2501783
theorem B2814763 : Blo 1666533 2814763 := bstep (se 1 (by rfl) ⟨2111072, by rfl⟩ : syracuseStep 2814763 = 4222145) B4222145
theorem B1667899 : Blo 1666533 1667899 := bstep (se 1 (by rfl) ⟨1250924, by rfl⟩ : syracuseStep 1667899 = 2501849) B2501849
theorem B1667975 : Blo 1666533 1667975 := bstep (se 1 (by rfl) ⟨1250981, by rfl⟩ : syracuseStep 1667975 = 2501963) B2501963
theorem B1667983 : Blo 1666533 1667983 := bstep (se 1 (by rfl) ⟨1250987, by rfl⟩ : syracuseStep 1667983 = 2501975) B2501975
theorem B20288407 : Blo 1666533 20288407 := bstep (se 1 (by rfl) ⟨15216305, by rfl⟩ : syracuseStep 20288407 = 30432611) B30432611
theorem B1668027 : Blo 1666533 1668027 := bstep (se 1 (by rfl) ⟨1251020, by rfl⟩ : syracuseStep 1668027 = 2502041) B2502041
theorem B9385003 : Blo 1666533 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B9499963 : Blo 1666533 9499963 := bstep (se 1 (by rfl) ⟨7124972, by rfl⟩ : syracuseStep 9499963 = 14249945) B14249945
theorem B4814167 : Blo 1666533 4814167 := bstep (se 1 (by rfl) ⟨3610625, by rfl⟩ : syracuseStep 4814167 = 7221251) B7221251
theorem B2110855 : Blo 1666533 2110855 := bstep (se 1 (by rfl) ⟨1583141, by rfl⟩ : syracuseStep 2110855 = 3166283) B3166283
theorem B6329785 : Blo 1666533 6329785 := bstep (se 2 (by rfl) ⟨2373669, by rfl⟩ : syracuseStep 6329785 = 4747339) B4747339
theorem B10827229 : Blo 1666533 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B4748843 : Blo 1666533 4748843 := bstep (se 1 (by rfl) ⟨3561632, by rfl⟩ : syracuseStep 4748843 = 7123265) B7123265
theorem B2569801 : Blo 1666533 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B6010487 : Blo 1666533 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B2373305 : Blo 1666533 2373305 := bstep (se 2 (by rfl) ⟨889989, by rfl⟩ : syracuseStep 2373305 = 1779979) B1779979
theorem B2373391 : Blo 1666533 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B2373419 : Blo 1666533 2373419 := bstep (se 1 (by rfl) ⟨1780064, by rfl⟩ : syracuseStep 2373419 = 3560129) B3560129
theorem B8443763 : Blo 1666533 8443763 := bstep (se 1 (by rfl) ⟨6332822, by rfl⟩ : syracuseStep 8443763 = 12665645) B12665645
theorem B8009675 : Blo 1666533 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B9492491 : Blo 1666533 9492491 := bstep (se 1 (by rfl) ⟨7119368, by rfl⟩ : syracuseStep 9492491 = 14238737) B14238737
theorem B3749903 : Blo 1666533 3749903 := bstep (se 1 (by rfl) ⟨2812427, by rfl⟩ : syracuseStep 3749903 = 5624855) B5624855
theorem B3749921 : Blo 1666533 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B9492673 : Blo 1666533 9492673 := bstep (se 2 (by rfl) ⟨3559752, by rfl⟩ : syracuseStep 9492673 = 7119505) B7119505
theorem B8444249 : Blo 1666533 8444249 := bstep (se 2 (by rfl) ⟨3166593, by rfl⟩ : syracuseStep 8444249 = 6333187) B6333187
theorem B3750263 : Blo 1666533 3750263 := bstep (se 1 (by rfl) ⟨2812697, by rfl⟩ : syracuseStep 3750263 = 5625395) B5625395
theorem B5626259 : Blo 1666533 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B3750443 : Blo 1666533 3750443 := bstep (se 1 (by rfl) ⟨2812832, by rfl⟩ : syracuseStep 3750443 = 5625665) B5625665
theorem B3750803 : Blo 1666533 3750803 := bstep (se 1 (by rfl) ⟨2813102, by rfl⟩ : syracuseStep 3750803 = 5626205) B5626205
theorem B1874875 : Blo 1666533 1874875 := bstep (se 1 (by rfl) ⟨1406156, by rfl⟩ : syracuseStep 1874875 = 2812313) B2812313
theorem B3750857 : Blo 1666533 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B2669687 : Blo 1666533 2669687 := bstep (se 1 (by rfl) ⟨2002265, by rfl⟩ : syracuseStep 2669687 = 4004531) B4004531
theorem B9010433 : Blo 1666533 9010433 := bstep (se 2 (by rfl) ⟨3378912, by rfl⟩ : syracuseStep 9010433 = 6757825) B6757825
theorem B5340449 : Blo 1666533 5340449 := bstep (se 2 (by rfl) ⟨2002668, by rfl⟩ : syracuseStep 5340449 = 4005337) B4005337
theorem B1875343 : Blo 1666533 1875343 := bstep (se 1 (by rfl) ⟨1406507, by rfl⟩ : syracuseStep 1875343 = 2813015) B2813015
theorem B8011331 : Blo 1666533 8011331 := bstep (se 1 (by rfl) ⟨6008498, by rfl⟩ : syracuseStep 8011331 = 12016997) B12016997
theorem B3751559 : Blo 1666533 3751559 := bstep (se 1 (by rfl) ⟨2813669, by rfl⟩ : syracuseStep 3751559 = 5627339) B5627339
theorem B5627663 : Blo 1666533 5627663 := bstep (se 1 (by rfl) ⟨4220747, by rfl⟩ : syracuseStep 5627663 = 8441495) B8441495
theorem B3751739 : Blo 1666533 3751739 := bstep (se 1 (by rfl) ⟨2813804, by rfl⟩ : syracuseStep 3751739 = 5627609) B5627609
theorem B4218743 : Blo 1666533 4218743 := bstep (se 1 (by rfl) ⟨3164057, by rfl⟩ : syracuseStep 4218743 = 6328115) B6328115
theorem B1875847 : Blo 1666533 1875847 := bstep (se 1 (by rfl) ⟨1406885, by rfl⟩ : syracuseStep 1875847 = 2813771) B2813771
theorem B32047001 : Blo 1666533 32047001 := bstep (se 2 (by rfl) ⟨12017625, by rfl⟩ : syracuseStep 32047001 = 24035251) B24035251
theorem B3751865 : Blo 1666533 3751865 := bstep (se 2 (by rfl) ⟨1406949, by rfl⟩ : syracuseStep 3751865 = 2813899) B2813899
theorem B10141625 : Blo 1666533 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B3751955 : Blo 1666533 3751955 := bstep (se 1 (by rfl) ⟨2813966, by rfl⟩ : syracuseStep 3751955 = 5627933) B5627933
theorem B16023581 : Blo 1666533 16023581 := bstep (se 3 (by rfl) ⟨3004421, by rfl⟩ : syracuseStep 16023581 = 6008843) B6008843
theorem B12656897 : Blo 1666533 12656897 := bstep (se 2 (by rfl) ⟨4746336, by rfl⟩ : syracuseStep 12656897 = 9492673) B9492673
theorem B24043787 : Blo 1666533 24043787 := bstep (se 1 (by rfl) ⟨18032840, by rfl⟩ : syracuseStep 24043787 = 36065681) B36065681
theorem B3752297 : Blo 1666533 3752297 := bstep (se 2 (by rfl) ⟨1407111, by rfl⟩ : syracuseStep 3752297 = 2814223) B2814223
theorem B5341565 : Blo 1666533 5341565 := bstep (se 3 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 5341565 = 2003087) B2003087
theorem B5702177 : Blo 1666533 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B3752891 : Blo 1666533 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B3753017 : Blo 1666533 3753017 := bstep (se 2 (by rfl) ⟨1407381, by rfl⟩ : syracuseStep 3753017 = 2814763) B2814763
theorem B4006991 : Blo 1666533 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B27051209 : Blo 1666533 27051209 := bstep (se 2 (by rfl) ⟨10144203, by rfl⟩ : syracuseStep 27051209 = 20288407) B20288407
theorem B5629175 : Blo 1666533 5629175 := bstep (se 1 (by rfl) ⟨4221881, by rfl⟩ : syracuseStep 5629175 = 8443763) B8443763
theorem B2499833 : Blo 1666533 2499833 := bstep (se 2 (by rfl) ⟨937437, by rfl⟩ : syracuseStep 2499833 = 1874875) B1874875
theorem B2499935 : Blo 1666533 2499935 := bstep (se 1 (by rfl) ⟨1874951, by rfl⟩ : syracuseStep 2499935 = 3749903) B3749903
theorem B2499947 : Blo 1666533 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B5629499 : Blo 1666533 5629499 := bstep (se 1 (by rfl) ⟨4222124, by rfl⟩ : syracuseStep 5629499 = 8444249) B8444249
theorem B14247485 : Blo 1666533 14247485 := bstep (se 3 (by rfl) ⟨2671403, by rfl⟩ : syracuseStep 14247485 = 5342807) B5342807
theorem B2500175 : Blo 1666533 2500175 := bstep (se 1 (by rfl) ⟨1875131, by rfl⟩ : syracuseStep 2500175 = 3750263) B3750263
theorem B16017041 : Blo 1666533 16017041 := bstep (se 2 (by rfl) ⟨6006390, by rfl⟩ : syracuseStep 16017041 = 12012781) B12012781
theorem B6260413 : Blo 1666533 6260413 := bstep (se 3 (by rfl) ⟨1173827, by rfl⟩ : syracuseStep 6260413 = 2347655) B2347655
theorem B2500295 : Blo 1666533 2500295 := bstep (se 1 (by rfl) ⟨1875221, by rfl⟩ : syracuseStep 2500295 = 3750443) B3750443
theorem B12666617 : Blo 1666533 12666617 := bstep (se 2 (by rfl) ⟨4749981, by rfl⟩ : syracuseStep 12666617 = 9499963) B9499963
theorem B2500457 : Blo 1666533 2500457 := bstep (se 2 (by rfl) ⟨937671, by rfl⟩ : syracuseStep 2500457 = 1875343) B1875343
theorem B8439713 : Blo 1666533 8439713 := bstep (se 2 (by rfl) ⟨3164892, by rfl⟩ : syracuseStep 8439713 = 6329785) B6329785
theorem B105514913 : Blo 1666533 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B2500535 : Blo 1666533 2500535 := bstep (se 1 (by rfl) ⟨1875401, by rfl⟩ : syracuseStep 2500535 = 3750803) B3750803
theorem B23128001 : Blo 1666533 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B14436305 : Blo 1666533 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B2500571 : Blo 1666533 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B3164179 : Blo 1666533 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B1779791 : Blo 1666533 1779791 := bstep (se 1 (by rfl) ⟨1334843, by rfl⟩ : syracuseStep 1779791 = 2669687) B2669687
theorem B3426401 : Blo 1666533 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B5343347 : Blo 1666533 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B45631619 : Blo 1666533 45631619 := bstep (se 1 (by rfl) ⟨34223714, by rfl⟩ : syracuseStep 45631619 = 68447429) B68447429
theorem B6006955 : Blo 1666533 6006955 := bstep (se 1 (by rfl) ⟨4505216, by rfl⟩ : syracuseStep 6006955 = 9010433) B9010433
theorem B3164521 : Blo 1666533 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B2501039 : Blo 1666533 2501039 := bstep (se 1 (by rfl) ⟨1875779, by rfl⟩ : syracuseStep 2501039 = 3751559) B3751559
theorem B2501129 : Blo 1666533 2501129 := bstep (se 2 (by rfl) ⟨937923, by rfl⟩ : syracuseStep 2501129 = 1875847) B1875847
theorem B7137817 : Blo 1666533 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B2501159 : Blo 1666533 2501159 := bstep (se 1 (by rfl) ⟨1875869, by rfl⟩ : syracuseStep 2501159 = 3751739) B3751739
theorem B2812495 : Blo 1666533 2812495 := bstep (se 1 (by rfl) ⟨2109371, by rfl⟩ : syracuseStep 2812495 = 4218743) B4218743
theorem B2501243 : Blo 1666533 2501243 := bstep (se 1 (by rfl) ⟨1875932, by rfl⟩ : syracuseStep 2501243 = 3751865) B3751865
theorem B6761083 : Blo 1666533 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B4745927 : Blo 1666533 4745927 := bstep (se 1 (by rfl) ⟨3559445, by rfl⟩ : syracuseStep 4745927 = 7118891) B7118891
theorem B1780423 : Blo 1666533 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B2501369 : Blo 1666533 2501369 := bstep (se 2 (by rfl) ⟨938013, by rfl⟩ : syracuseStep 2501369 = 1876027) B1876027
theorem B2812745 : Blo 1666533 2812745 := bstep (se 2 (by rfl) ⟨1054779, by rfl⟩ : syracuseStep 2812745 = 2109559) B2109559
theorem B2501471 : Blo 1666533 2501471 := bstep (se 1 (by rfl) ⟨1876103, by rfl⟩ : syracuseStep 2501471 = 3752207) B3752207
theorem B4221791 : Blo 1666533 4221791 := bstep (se 1 (by rfl) ⟨3166343, by rfl⟩ : syracuseStep 4221791 = 6332687) B6332687
theorem B2501483 : Blo 1666533 2501483 := bstep (se 1 (by rfl) ⟨1876112, by rfl⟩ : syracuseStep 2501483 = 3752225) B3752225
theorem B54799249 : Blo 1666533 54799249 := bstep (se 2 (by rfl) ⟨20549718, by rfl⟩ : syracuseStep 54799249 = 41099437) B41099437
theorem B9497573 : Blo 1666533 9497573 := bstep (se 4 (by rfl) ⟨890397, by rfl⟩ : syracuseStep 9497573 = 1780795) B1780795
theorem B2501711 : Blo 1666533 2501711 := bstep (se 1 (by rfl) ⟨1876283, by rfl⟩ : syracuseStep 2501711 = 3752567) B3752567
theorem B2501831 : Blo 1666533 2501831 := bstep (se 1 (by rfl) ⟨1876373, by rfl⟩ : syracuseStep 2501831 = 3752747) B3752747
theorem B2813177 : Blo 1666533 2813177 := bstep (se 2 (by rfl) ⟨1054941, by rfl⟩ : syracuseStep 2813177 = 2109883) B2109883
theorem B2501993 : Blo 1666533 2501993 := bstep (se 2 (by rfl) ⟨938247, by rfl⟩ : syracuseStep 2501993 = 1876495) B1876495
theorem B4337039 : Blo 1666533 4337039 := bstep (se 1 (by rfl) ⟨3252779, by rfl⟩ : syracuseStep 4337039 = 6505559) B6505559
theorem B14241197 : Blo 1666533 14241197 := bstep (se 3 (by rfl) ⟨2670224, by rfl⟩ : syracuseStep 14241197 = 5340449) B5340449
theorem B2813359 : Blo 1666533 2813359 := bstep (se 1 (by rfl) ⟨2110019, by rfl⟩ : syracuseStep 2813359 = 4220039) B4220039
theorem B2813447 : Blo 1666533 2813447 := bstep (se 1 (by rfl) ⟨2110085, by rfl⟩ : syracuseStep 2813447 = 4220171) B4220171
theorem B6327841 : Blo 1666533 6327841 := bstep (se 2 (by rfl) ⟨2372940, by rfl⟩ : syracuseStep 6327841 = 4745881) B4745881
theorem B1666599 : Blo 1666533 1666599 := bstep (se 1 (by rfl) ⟨1249949, by rfl⟩ : syracuseStep 1666599 = 2499899) B2499899
theorem B1666639 : Blo 1666533 1666639 := bstep (se 1 (by rfl) ⟨1249979, by rfl⟩ : syracuseStep 1666639 = 2499959) B2499959
theorem B1666655 : Blo 1666533 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B1666683 : Blo 1666533 1666683 := bstep (se 1 (by rfl) ⟨1250012, by rfl⟩ : syracuseStep 1666683 = 2500025) B2500025
theorem B1666735 : Blo 1666533 1666735 := bstep (se 1 (by rfl) ⟨1250051, by rfl⟩ : syracuseStep 1666735 = 2500103) B2500103
theorem B1666759 : Blo 1666533 1666759 := bstep (se 1 (by rfl) ⟨1250069, by rfl⟩ : syracuseStep 1666759 = 2500139) B2500139
theorem B3165895 : Blo 1666533 3165895 := bstep (se 1 (by rfl) ⟨2374421, by rfl⟩ : syracuseStep 3165895 = 4748843) B4748843
theorem B1666779 : Blo 1666533 1666779 := bstep (se 1 (by rfl) ⟨1250084, by rfl⟩ : syracuseStep 1666779 = 2500169) B2500169
theorem B18034397 : Blo 1666533 18034397 := bstep (se 3 (by rfl) ⟨3381449, by rfl⟩ : syracuseStep 18034397 = 6762899) B6762899
theorem B1666855 : Blo 1666533 1666855 := bstep (se 1 (by rfl) ⟨1250141, by rfl⟩ : syracuseStep 1666855 = 2500283) B2500283
theorem B12021547 : Blo 1666533 12021547 := bstep (se 1 (by rfl) ⟨9016160, by rfl⟩ : syracuseStep 12021547 = 18032321) B18032321
theorem B1666895 : Blo 1666533 1666895 := bstep (se 1 (by rfl) ⟨1250171, by rfl⟩ : syracuseStep 1666895 = 2500343) B2500343
theorem B1666911 : Blo 1666533 1666911 := bstep (se 1 (by rfl) ⟨1250183, by rfl⟩ : syracuseStep 1666911 = 2500367) B2500367
theorem B2813791 : Blo 1666533 2813791 := bstep (se 1 (by rfl) ⟨2110343, by rfl⟩ : syracuseStep 2813791 = 4220687) B4220687
theorem B19246967 : Blo 1666533 19246967 := bstep (se 1 (by rfl) ⟨14435225, by rfl⟩ : syracuseStep 19246967 = 28870451) B28870451
theorem B1666939 : Blo 1666533 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B1666991 : Blo 1666533 1666991 := bstep (se 1 (by rfl) ⟨1250243, by rfl⟩ : syracuseStep 1666991 = 2500487) B2500487
theorem B2813879 : Blo 1666533 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B1667015 : Blo 1666533 1667015 := bstep (se 1 (by rfl) ⟨1250261, by rfl⟩ : syracuseStep 1667015 = 2500523) B2500523
theorem B1667035 : Blo 1666533 1667035 := bstep (se 1 (by rfl) ⟨1250276, by rfl⟩ : syracuseStep 1667035 = 2500553) B2500553
theorem B6328327 : Blo 1666533 6328327 := bstep (se 1 (by rfl) ⟨4746245, by rfl⟩ : syracuseStep 6328327 = 9492491) B9492491
theorem B1667111 : Blo 1666533 1667111 := bstep (se 1 (by rfl) ⟨1250333, by rfl⟩ : syracuseStep 1667111 = 2500667) B2500667
theorem B12513337 : Blo 1666533 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B1667151 : Blo 1666533 1667151 := bstep (se 1 (by rfl) ⟨1250363, by rfl⟩ : syracuseStep 1667151 = 2500727) B2500727
theorem B1667167 : Blo 1666533 1667167 := bstep (se 1 (by rfl) ⟨1250375, by rfl⟩ : syracuseStep 1667167 = 2500751) B2500751
theorem B1667195 : Blo 1666533 1667195 := bstep (se 1 (by rfl) ⟨1250396, by rfl⟩ : syracuseStep 1667195 = 2500793) B2500793
theorem B1667247 : Blo 1666533 1667247 := bstep (se 1 (by rfl) ⟨1250435, by rfl⟩ : syracuseStep 1667247 = 2500871) B2500871
theorem B1667271 : Blo 1666533 1667271 := bstep (se 1 (by rfl) ⟨1250453, by rfl⟩ : syracuseStep 1667271 = 2500907) B2500907
theorem B1667291 : Blo 1666533 1667291 := bstep (se 1 (by rfl) ⟨1250468, by rfl⟩ : syracuseStep 1667291 = 2500937) B2500937
theorem B4747511 : Blo 1666533 4747511 := bstep (se 1 (by rfl) ⟨3560633, by rfl⟩ : syracuseStep 4747511 = 7121267) B7121267
theorem B1667367 : Blo 1666533 1667367 := bstep (se 1 (by rfl) ⟨1250525, by rfl⟩ : syracuseStep 1667367 = 2501051) B2501051
theorem B30421307 : Blo 1666533 30421307 := bstep (se 1 (by rfl) ⟨22815980, by rfl⟩ : syracuseStep 30421307 = 45631961) B45631961
theorem B1667407 : Blo 1666533 1667407 := bstep (se 1 (by rfl) ⟨1250555, by rfl⟩ : syracuseStep 1667407 = 2501111) B2501111
theorem B1667423 : Blo 1666533 1667423 := bstep (se 1 (by rfl) ⟨1250567, by rfl⟩ : syracuseStep 1667423 = 2501135) B2501135
theorem B1667451 : Blo 1666533 1667451 := bstep (se 1 (by rfl) ⟨1250588, by rfl⟩ : syracuseStep 1667451 = 2501177) B2501177
theorem B1667503 : Blo 1666533 1667503 := bstep (se 1 (by rfl) ⟨1250627, by rfl⟩ : syracuseStep 1667503 = 2501255) B2501255
theorem B1667527 : Blo 1666533 1667527 := bstep (se 1 (by rfl) ⟨1250645, by rfl⟩ : syracuseStep 1667527 = 2501291) B2501291
theorem B6418889 : Blo 1666533 6418889 := bstep (se 2 (by rfl) ⟨2407083, by rfl⟩ : syracuseStep 6418889 = 4814167) B4814167
theorem B1667547 : Blo 1666533 1667547 := bstep (se 1 (by rfl) ⟨1250660, by rfl⟩ : syracuseStep 1667547 = 2501321) B2501321
theorem B6328813 : Blo 1666533 6328813 := bstep (se 3 (by rfl) ⟨1186652, by rfl⟩ : syracuseStep 6328813 = 2373305) B2373305
theorem B2814473 : Blo 1666533 2814473 := bstep (se 2 (by rfl) ⟨1055427, by rfl⟩ : syracuseStep 2814473 = 2110855) B2110855
theorem B12661271 : Blo 1666533 12661271 := bstep (se 1 (by rfl) ⟨9495953, by rfl⟩ : syracuseStep 12661271 = 18991907) B18991907
theorem B1667623 : Blo 1666533 1667623 := bstep (se 1 (by rfl) ⟨1250717, by rfl⟩ : syracuseStep 1667623 = 2501435) B2501435
theorem B1667663 : Blo 1666533 1667663 := bstep (se 1 (by rfl) ⟨1250747, by rfl⟩ : syracuseStep 1667663 = 2501495) B2501495
theorem B1667679 : Blo 1666533 1667679 := bstep (se 1 (by rfl) ⟨1250759, by rfl⟩ : syracuseStep 1667679 = 2501519) B2501519
theorem B1667707 : Blo 1666533 1667707 := bstep (se 1 (by rfl) ⟨1250780, by rfl⟩ : syracuseStep 1667707 = 2501561) B2501561
theorem B2814635 : Blo 1666533 2814635 := bstep (se 1 (by rfl) ⟨2110976, by rfl⟩ : syracuseStep 2814635 = 4221953) B4221953
theorem B1667759 : Blo 1666533 1667759 := bstep (se 1 (by rfl) ⟨1250819, by rfl⟩ : syracuseStep 1667759 = 2501639) B2501639
theorem B2110151 : Blo 1666533 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B1667783 : Blo 1666533 1667783 := bstep (se 1 (by rfl) ⟨1250837, by rfl⟩ : syracuseStep 1667783 = 2501675) B2501675
theorem B1667803 : Blo 1666533 1667803 := bstep (se 1 (by rfl) ⟨1250852, by rfl⟩ : syracuseStep 1667803 = 2501705) B2501705
theorem B6329117 : Blo 1666533 6329117 := bstep (se 3 (by rfl) ⟨1186709, by rfl⟩ : syracuseStep 6329117 = 2373419) B2373419
theorem B1667879 : Blo 1666533 1667879 := bstep (se 1 (by rfl) ⟨1250909, by rfl⟩ : syracuseStep 1667879 = 2501819) B2501819
theorem B1667919 : Blo 1666533 1667919 := bstep (se 1 (by rfl) ⟨1250939, by rfl⟩ : syracuseStep 1667919 = 2501879) B2501879
theorem B2110303 : Blo 1666533 2110303 := bstep (se 1 (by rfl) ⟨1582727, by rfl⟩ : syracuseStep 2110303 = 3165455) B3165455
theorem B1667935 : Blo 1666533 1667935 := bstep (se 1 (by rfl) ⟨1250951, by rfl⟩ : syracuseStep 1667935 = 2501903) B2501903
theorem B1667963 : Blo 1666533 1667963 := bstep (se 1 (by rfl) ⟨1250972, by rfl⟩ : syracuseStep 1667963 = 2501945) B2501945
theorem B1668015 : Blo 1666533 1668015 := bstep (se 1 (by rfl) ⟨1251011, by rfl⟩ : syracuseStep 1668015 = 2502023) B2502023
theorem B10679363 : Blo 1666533 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B51328171 : Blo 1666533 51328171 := bstep (se 1 (by rfl) ⟨38496128, by rfl⟩ : syracuseStep 51328171 = 76992257) B76992257
theorem B6010199 : Blo 1666533 6010199 := bstep (se 1 (by rfl) ⟨4507649, by rfl⟩ : syracuseStep 6010199 = 9015299) B9015299
theorem B3003961 : Blo 1666533 3003961 := bstep (se 2 (by rfl) ⟨1126485, by rfl⟩ : syracuseStep 3003961 = 2252971) B2252971
theorem B13522555 : Blo 1666533 13522555 := bstep (se 1 (by rfl) ⟨10141916, by rfl⟩ : syracuseStep 13522555 = 20283833) B20283833
theorem B3749705 : Blo 1666533 3749705 := bstep (se 2 (by rfl) ⟨1406139, by rfl⟩ : syracuseStep 3749705 = 2812279) B2812279
theorem B4749151 : Blo 1666533 4749151 := bstep (se 1 (by rfl) ⟨3561863, by rfl⟩ : syracuseStep 4749151 = 7123727) B7123727
theorem B10975085 : Blo 1666533 10975085 := bstep (se 3 (by rfl) ⟨2057828, by rfl⟩ : syracuseStep 10975085 = 4115657) B4115657
theorem B5625719 : Blo 1666533 5625719 := bstep (se 1 (by rfl) ⟨4219289, by rfl⟩ : syracuseStep 5625719 = 8438579) B8438579
theorem B21370817 : Blo 1666533 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B3561479 : Blo 1666533 3561479 := bstep (se 1 (by rfl) ⟨2671109, by rfl⟩ : syracuseStep 3561479 = 5342219) B5342219
theorem B3381257 : Blo 1666533 3381257 := bstep (se 2 (by rfl) ⟨1267971, by rfl⟩ : syracuseStep 3381257 = 2535943) B2535943
theorem B5625935 : Blo 1666533 5625935 := bstep (se 1 (by rfl) ⟨4219451, by rfl⟩ : syracuseStep 5625935 = 8438903) B8438903
theorem B666613849 : Blo 1666533 666613849 := bstep (se 2 (by rfl) ⟨249980193, by rfl⟩ : syracuseStep 666613849 = 499960387) B499960387
theorem B5626313 : Blo 1666533 5626313 := bstep (se 2 (by rfl) ⟨2109867, by rfl⟩ : syracuseStep 5626313 = 4219735) B4219735
theorem B3750497 : Blo 1666533 3750497 := bstep (se 2 (by rfl) ⟨1406436, by rfl⟩ : syracuseStep 3750497 = 2812873) B2812873
theorem B5339783 : Blo 1666533 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B5626583 : Blo 1666533 5626583 := bstep (se 1 (by rfl) ⟨4219937, by rfl⟩ : syracuseStep 5626583 = 8439875) B8439875
theorem B6331243 : Blo 1666533 6331243 := bstep (se 1 (by rfl) ⟨4748432, by rfl⟩ : syracuseStep 6331243 = 9496865) B9496865
theorem B3005345 : Blo 1666533 3005345 := bstep (se 2 (by rfl) ⟨1127004, by rfl⟩ : syracuseStep 3005345 = 2254009) B2254009
theorem B5626799 : Blo 1666533 5626799 := bstep (se 1 (by rfl) ⟨4220099, by rfl⟩ : syracuseStep 5626799 = 8440199) B8440199
theorem B3750839 : Blo 1666533 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B6757307 : Blo 1666533 6757307 := bstep (se 1 (by rfl) ⟨5067980, by rfl⟩ : syracuseStep 6757307 = 10135961) B10135961
theorem B1874983 : Blo 1666533 1874983 := bstep (se 1 (by rfl) ⟨1406237, by rfl⟩ : syracuseStep 1874983 = 2812475) B2812475
theorem B15834359 : Blo 1666533 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B48717233 : Blo 1666533 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B43326899 : Blo 1666533 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B3751433 : Blo 1666533 3751433 := bstep (se 2 (by rfl) ⟨1406787, by rfl⟩ : syracuseStep 3751433 = 2813575) B2813575
theorem B5340887 : Blo 1666533 5340887 := bstep (se 1 (by rfl) ⟨4005665, by rfl⟩ : syracuseStep 5340887 = 8011331) B8011331
theorem B12181241 : Blo 1666533 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B9625337 : Blo 1666533 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B3751775 : Blo 1666533 3751775 := bstep (se 1 (by rfl) ⟨2813831, by rfl⟩ : syracuseStep 3751775 = 5627663) B5627663
theorem B21364667 : Blo 1666533 21364667 := bstep (se 1 (by rfl) ⟨16023500, by rfl⟩ : syracuseStep 21364667 = 32047001) B32047001
theorem B8437769 : Blo 1666533 8437769 := bstep (se 2 (by rfl) ⟨3164163, by rfl⟩ : syracuseStep 8437769 = 6328327) B6328327
theorem B10682387 : Blo 1666533 10682387 := bstep (se 1 (by rfl) ⟨8011790, by rfl⟩ : syracuseStep 10682387 = 16023581) B16023581
theorem B4218905 : Blo 1666533 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B8437931 : Blo 1666533 8437931 := bstep (se 1 (by rfl) ⟨6328448, by rfl⟩ : syracuseStep 8437931 = 12656897) B12656897
theorem B1876315 : Blo 1666533 1876315 := bstep (se 1 (by rfl) ⟨1407236, by rfl⟩ : syracuseStep 1876315 = 2814473) B2814473
theorem B3801451 : Blo 1666533 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B1876423 : Blo 1666533 1876423 := bstep (se 1 (by rfl) ⟨1407317, by rfl⟩ : syracuseStep 1876423 = 2814635) B2814635
theorem B4219361 : Blo 1666533 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B4219411 : Blo 1666533 4219411 := bstep (se 1 (by rfl) ⟨3164558, by rfl⟩ : syracuseStep 4219411 = 6329117) B6329117
theorem B152273429 : Blo 1666533 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B8438417 : Blo 1666533 8438417 := bstep (se 2 (by rfl) ⟨3164406, by rfl⟩ : syracuseStep 8438417 = 6328813) B6328813
theorem B7119575 : Blo 1666533 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B2671327 : Blo 1666533 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B3752783 : Blo 1666533 3752783 := bstep (se 1 (by rfl) ⟨2814587, by rfl⟩ : syracuseStep 3752783 = 5629175) B5629175
theorem B4006799 : Blo 1666533 4006799 := bstep (se 1 (by rfl) ⟨3005099, by rfl⟩ : syracuseStep 4006799 = 6010199) B6010199
theorem B9495589 : Blo 1666533 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B3752999 : Blo 1666533 3752999 := bstep (se 1 (by rfl) ⟨2814749, by rfl⟩ : syracuseStep 3752999 = 5629499) B5629499
theorem B73065665 : Blo 1666533 73065665 := bstep (se 2 (by rfl) ⟨27399624, by rfl⟩ : syracuseStep 73065665 = 54799249) B54799249
theorem B2499803 : Blo 1666533 2499803 := bstep (se 1 (by rfl) ⟨1874852, by rfl⟩ : syracuseStep 2499803 = 3749705) B3749705
theorem B7316723 : Blo 1666533 7316723 := bstep (se 1 (by rfl) ⟨5487542, by rfl⟩ : syracuseStep 7316723 = 10975085) B10975085
theorem B15418667 : Blo 1666533 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B14247211 : Blo 1666533 14247211 := bstep (se 1 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 14247211 = 21370817) B21370817
theorem B2254171 : Blo 1666533 2254171 := bstep (se 1 (by rfl) ⟨1690628, by rfl⟩ : syracuseStep 2254171 = 3381257) B3381257
theorem B2499977 : Blo 1666533 2499977 := bstep (se 2 (by rfl) ⟨937491, by rfl⟩ : syracuseStep 2499977 = 1874983) B1874983
theorem B68437561 : Blo 1666533 68437561 := bstep (se 2 (by rfl) ⟨25664085, by rfl⟩ : syracuseStep 68437561 = 51328171) B51328171
theorem B14239421 : Blo 1666533 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B2500331 : Blo 1666533 2500331 := bstep (se 1 (by rfl) ⟨1875248, by rfl⟩ : syracuseStep 2500331 = 3750497) B3750497
theorem B3163951 : Blo 1666533 3163951 := bstep (se 1 (by rfl) ⟨2372963, by rfl⟩ : syracuseStep 3163951 = 4745927) B4745927
theorem B2500559 : Blo 1666533 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B4221193 : Blo 1666533 4221193 := bstep (se 2 (by rfl) ⟨1582947, by rfl⟩ : syracuseStep 4221193 = 3165895) B3165895
theorem B2500955 : Blo 1666533 2500955 := bstep (se 1 (by rfl) ⟨1875716, by rfl⟩ : syracuseStep 2500955 = 3751433) B3751433
theorem B281373101 : Blo 1666533 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B8120827 : Blo 1666533 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B6416891 : Blo 1666533 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B2501183 : Blo 1666533 2501183 := bstep (se 1 (by rfl) ⟨1875887, by rfl⟩ : syracuseStep 2501183 = 3751775) B3751775
theorem B12831311 : Blo 1666533 12831311 := bstep (se 1 (by rfl) ⟨9623483, by rfl⟩ : syracuseStep 12831311 = 19246967) B19246967
theorem B2501303 : Blo 1666533 2501303 := bstep (se 1 (by rfl) ⟨1875977, by rfl⟩ : syracuseStep 2501303 = 3751955) B3751955
theorem B888818465 : Blo 1666533 888818465 := bstep (se 2 (by rfl) ⟨333306924, by rfl⟩ : syracuseStep 888818465 = 666613849) B666613849
theorem B3165007 : Blo 1666533 3165007 := bstep (se 1 (by rfl) ⟨2373755, by rfl⟩ : syracuseStep 3165007 = 4747511) B4747511
theorem B4746109 : Blo 1666533 4746109 := bstep (se 3 (by rfl) ⟨889895, by rfl⟩ : syracuseStep 4746109 = 1779791) B1779791
theorem B2501531 : Blo 1666533 2501531 := bstep (se 1 (by rfl) ⟨1876148, by rfl⟩ : syracuseStep 2501531 = 3752297) B3752297
theorem B9137069 : Blo 1666533 9137069 := bstep (se 3 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 9137069 = 3426401) B3426401
theorem B4279259 : Blo 1666533 4279259 := bstep (se 1 (by rfl) ⟨3209444, by rfl⟩ : syracuseStep 4279259 = 6418889) B6418889
theorem B8440847 : Blo 1666533 8440847 := bstep (se 1 (by rfl) ⟨6330635, by rfl⟩ : syracuseStep 8440847 = 12661271) B12661271
theorem B2501927 : Blo 1666533 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B2502011 : Blo 1666533 2502011 := bstep (se 1 (by rfl) ⟨1876508, by rfl⟩ : syracuseStep 2502011 = 3753017) B3753017
theorem B18034139 : Blo 1666533 18034139 := bstep (se 1 (by rfl) ⟨13525604, by rfl⟩ : syracuseStep 18034139 = 27051209) B27051209
theorem B9014777 : Blo 1666533 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1666555 : Blo 1666533 1666555 := bstep (se 1 (by rfl) ⟨1249916, by rfl⟩ : syracuseStep 1666555 = 2499833) B2499833
theorem B1666623 : Blo 1666533 1666623 := bstep (se 1 (by rfl) ⟨1249967, by rfl⟩ : syracuseStep 1666623 = 2499935) B2499935
theorem B1666631 : Blo 1666533 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B9498323 : Blo 1666533 9498323 := bstep (se 1 (by rfl) ⟨7123742, by rfl⟩ : syracuseStep 9498323 = 14247485) B14247485
theorem B1666783 : Blo 1666533 1666783 := bstep (se 1 (by rfl) ⟨1250087, by rfl⟩ : syracuseStep 1666783 = 2500175) B2500175
theorem B2813737 : Blo 1666533 2813737 := bstep (se 2 (by rfl) ⟨1055151, by rfl⟩ : syracuseStep 2813737 = 2110303) B2110303
theorem B1666863 : Blo 1666533 1666863 := bstep (se 1 (by rfl) ⟨1250147, by rfl⟩ : syracuseStep 1666863 = 2500295) B2500295
theorem B8441657 : Blo 1666533 8441657 := bstep (se 2 (by rfl) ⟨3165621, by rfl⟩ : syracuseStep 8441657 = 6331243) B6331243
theorem B1666971 : Blo 1666533 1666971 := bstep (se 1 (by rfl) ⟨1250228, by rfl⟩ : syracuseStep 1666971 = 2500457) B2500457
theorem B1667023 : Blo 1666533 1667023 := bstep (se 1 (by rfl) ⟨1250267, by rfl⟩ : syracuseStep 1667023 = 2500535) B2500535
theorem B1667047 : Blo 1666533 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B30421079 : Blo 1666533 30421079 := bstep (se 1 (by rfl) ⟨22815809, by rfl⟩ : syracuseStep 30421079 = 45631619) B45631619
theorem B1667359 : Blo 1666533 1667359 := bstep (se 1 (by rfl) ⟨1250519, by rfl⟩ : syracuseStep 1667359 = 2501039) B2501039
theorem B1667419 : Blo 1666533 1667419 := bstep (se 1 (by rfl) ⟨1250564, by rfl⟩ : syracuseStep 1667419 = 2501129) B2501129
theorem B1667439 : Blo 1666533 1667439 := bstep (se 1 (by rfl) ⟨1250579, by rfl⟩ : syracuseStep 1667439 = 2501159) B2501159
theorem B1667495 : Blo 1666533 1667495 := bstep (se 1 (by rfl) ⟨1250621, by rfl⟩ : syracuseStep 1667495 = 2501243) B2501243
theorem B1667579 : Blo 1666533 1667579 := bstep (se 1 (by rfl) ⟨1250684, by rfl⟩ : syracuseStep 1667579 = 2501369) B2501369
theorem B1667647 : Blo 1666533 1667647 := bstep (se 1 (by rfl) ⟨1250735, by rfl⟩ : syracuseStep 1667647 = 2501471) B2501471
theorem B2814527 : Blo 1666533 2814527 := bstep (se 1 (by rfl) ⟨2110895, by rfl⟩ : syracuseStep 2814527 = 4221791) B4221791
theorem B1667655 : Blo 1666533 1667655 := bstep (se 1 (by rfl) ⟨1250741, by rfl⟩ : syracuseStep 1667655 = 2501483) B2501483
theorem B2003563 : Blo 1666533 2003563 := bstep (se 1 (by rfl) ⟨1502672, by rfl⟩ : syracuseStep 2003563 = 3005345) B3005345
theorem B1667807 : Blo 1666533 1667807 := bstep (se 1 (by rfl) ⟨1250855, by rfl⟩ : syracuseStep 1667807 = 2501711) B2501711
theorem B1667887 : Blo 1666533 1667887 := bstep (se 1 (by rfl) ⟨1250915, by rfl⟩ : syracuseStep 1667887 = 2501831) B2501831
theorem B10556239 : Blo 1666533 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B1667995 : Blo 1666533 1667995 := bstep (se 1 (by rfl) ⟨1250996, by rfl⟩ : syracuseStep 1667995 = 2501993) B2501993
theorem B32478155 : Blo 1666533 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B16028729 : Blo 1666533 16028729 := bstep (se 2 (by rfl) ⟨6010773, by rfl⟩ : syracuseStep 16028729 = 12021547) B12021547
theorem B3560591 : Blo 1666533 3560591 := bstep (se 1 (by rfl) ⟨2670443, by rfl⟩ : syracuseStep 3560591 = 5340887) B5340887
theorem B12022931 : Blo 1666533 12022931 := bstep (se 1 (by rfl) ⟨9017198, by rfl⟩ : syracuseStep 12022931 = 18034397) B18034397
theorem B14243111 : Blo 1666533 14243111 := bstep (se 1 (by rfl) ⟨10682333, by rfl⟩ : syracuseStep 14243111 = 21364667) B21364667
theorem B16029191 : Blo 1666533 16029191 := bstep (se 1 (by rfl) ⟨12021893, by rfl⟩ : syracuseStep 16029191 = 24043787) B24043787
theorem B20280871 : Blo 1666533 20280871 := bstep (se 1 (by rfl) ⟨15210653, by rfl⟩ : syracuseStep 20280871 = 30421307) B30421307
theorem B8009273 : Blo 1666533 8009273 := bstep (se 2 (by rfl) ⟨3003477, by rfl⟩ : syracuseStep 8009273 = 6006955) B6006955
theorem B3749993 : Blo 1666533 3749993 := bstep (se 2 (by rfl) ⟨1406247, by rfl⟩ : syracuseStep 3749993 = 2812495) B2812495
theorem B14244173 : Blo 1666533 14244173 := bstep (se 3 (by rfl) ⟨2670782, by rfl⟩ : syracuseStep 14244173 = 5341565) B5341565
theorem B8444411 : Blo 1666533 8444411 := bstep (se 1 (by rfl) ⟨6333308, by rfl⟩ : syracuseStep 8444411 = 12666617) B12666617
theorem B266951189 : Blo 1666533 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B3750479 : Blo 1666533 3750479 := bstep (se 1 (by rfl) ⟨2812859, by rfl⟩ : syracuseStep 3750479 = 5625719) B5625719
theorem B5626475 : Blo 1666533 5626475 := bstep (se 1 (by rfl) ⟨4219856, by rfl⟩ : syracuseStep 5626475 = 8439713) B8439713
theorem B9624203 : Blo 1666533 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B2374319 : Blo 1666533 2374319 := bstep (se 1 (by rfl) ⟨1780739, by rfl⟩ : syracuseStep 2374319 = 3561479) B3561479
theorem B3750623 : Blo 1666533 3750623 := bstep (se 1 (by rfl) ⟨2812967, by rfl⟩ : syracuseStep 3750623 = 5625935) B5625935
theorem B3562231 : Blo 1666533 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B3750875 : Blo 1666533 3750875 := bstep (se 1 (by rfl) ⟨2813156, by rfl⟩ : syracuseStep 3750875 = 5626313) B5626313
theorem B42712109 : Blo 1666533 42712109 := bstep (se 3 (by rfl) ⟨8008520, by rfl⟩ : syracuseStep 42712109 = 16017041) B16017041
theorem B3751055 : Blo 1666533 3751055 := bstep (se 1 (by rfl) ⟨2813291, by rfl⟩ : syracuseStep 3751055 = 5626583) B5626583
theorem B5627069 : Blo 1666533 5627069 := bstep (se 3 (by rfl) ⟨1055075, by rfl⟩ : syracuseStep 5627069 = 2110151) B2110151
theorem B1875163 : Blo 1666533 1875163 := bstep (se 1 (by rfl) ⟨1406372, by rfl⟩ : syracuseStep 1875163 = 2812745) B2812745
theorem B3751145 : Blo 1666533 3751145 := bstep (se 2 (by rfl) ⟨1406679, by rfl⟩ : syracuseStep 3751145 = 2813359) B2813359
theorem B3751199 : Blo 1666533 3751199 := bstep (se 1 (by rfl) ⟨2813399, by rfl⟩ : syracuseStep 3751199 = 5626799) B5626799
theorem B4504871 : Blo 1666533 4504871 := bstep (se 1 (by rfl) ⟨3378653, by rfl⟩ : syracuseStep 4504871 = 6757307) B6757307
theorem B6331715 : Blo 1666533 6331715 := bstep (se 1 (by rfl) ⟨4748786, by rfl⟩ : syracuseStep 6331715 = 9497573) B9497573
theorem B8437121 : Blo 1666533 8437121 := bstep (se 2 (by rfl) ⟨3163920, by rfl⟩ : syracuseStep 8437121 = 6327841) B6327841
theorem B4005281 : Blo 1666533 4005281 := bstep (se 2 (by rfl) ⟨1501980, by rfl⟩ : syracuseStep 4005281 = 3003961) B3003961
theorem B18030073 : Blo 1666533 18030073 := bstep (se 2 (by rfl) ⟨6761277, by rfl⟩ : syracuseStep 18030073 = 13522555) B13522555
theorem B1875451 : Blo 1666533 1875451 := bstep (se 1 (by rfl) ⟨1406588, by rfl⟩ : syracuseStep 1875451 = 2813177) B2813177
theorem B8347217 : Blo 1666533 8347217 := bstep (se 2 (by rfl) ⟨3130206, by rfl⟩ : syracuseStep 8347217 = 6260413) B6260413
theorem B2891359 : Blo 1666533 2891359 := bstep (se 1 (by rfl) ⟨2168519, by rfl⟩ : syracuseStep 2891359 = 4337039) B4337039
theorem B9494131 : Blo 1666533 9494131 := bstep (se 1 (by rfl) ⟨7120598, by rfl⟩ : syracuseStep 9494131 = 14241197) B14241197
theorem B28884599 : Blo 1666533 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B1875631 : Blo 1666533 1875631 := bstep (se 1 (by rfl) ⟨1406723, by rfl⟩ : syracuseStep 1875631 = 2813447) B2813447
theorem B3751721 : Blo 1666533 3751721 := bstep (se 2 (by rfl) ⟨1406895, by rfl⟩ : syracuseStep 3751721 = 2813791) B2813791
theorem B6332201 : Blo 1666533 6332201 := bstep (se 2 (by rfl) ⟨2374575, by rfl⟩ : syracuseStep 6332201 = 4749151) B4749151
theorem B1875919 : Blo 1666533 1875919 := bstep (se 1 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 1875919 = 2813879) B2813879
theorem B5628257 : Blo 1666533 5628257 := bstep (se 2 (by rfl) ⟨2110596, by rfl⟩ : syracuseStep 5628257 = 4221193) B4221193
theorem B101515619 : Blo 1666533 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B1876351 : Blo 1666533 1876351 := bstep (se 1 (by rfl) ⟨1407263, by rfl⟩ : syracuseStep 1876351 = 2814527) B2814527
theorem B2671199 : Blo 1666533 2671199 := bstep (se 1 (by rfl) ⟨2003399, by rfl⟩ : syracuseStep 2671199 = 4006799) B4006799
theorem B21652103 : Blo 1666533 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B48710443 : Blo 1666533 48710443 := bstep (se 1 (by rfl) ⟨36532832, by rfl⟩ : syracuseStep 48710443 = 73065665) B73065665
theorem B2671417 : Blo 1666533 2671417 := bstep (se 2 (by rfl) ⟨1001781, by rfl⟩ : syracuseStep 2671417 = 2003563) B2003563
theorem B9495407 : Blo 1666533 9495407 := bstep (se 1 (by rfl) ⟨7121555, by rfl⟩ : syracuseStep 9495407 = 14243111) B14243111
theorem B14074985 : Blo 1666533 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B4220009 : Blo 1666533 4220009 := bstep (se 2 (by rfl) ⟨1582503, by rfl⟩ : syracuseStep 4220009 = 3165007) B3165007
theorem B2499995 : Blo 1666533 2499995 := bstep (se 1 (by rfl) ⟨1874996, by rfl⟩ : syracuseStep 2499995 = 3749993) B3749993
theorem B22259245 : Blo 1666533 22259245 := bstep (se 3 (by rfl) ⟨4173608, by rfl⟩ : syracuseStep 22259245 = 8347217) B8347217
theorem B9496115 : Blo 1666533 9496115 := bstep (se 1 (by rfl) ⟨7122086, by rfl⟩ : syracuseStep 9496115 = 14244173) B14244173
theorem B187582067 : Blo 1666533 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B2500217 : Blo 1666533 2500217 := bstep (se 2 (by rfl) ⟨937581, by rfl⟩ : syracuseStep 2500217 = 1875163) B1875163
theorem B4277927 : Blo 1666533 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B5629607 : Blo 1666533 5629607 := bstep (se 1 (by rfl) ⟨4222205, by rfl⟩ : syracuseStep 5629607 = 8444411) B8444411
theorem B2500319 : Blo 1666533 2500319 := bstep (se 1 (by rfl) ⟨1875239, by rfl⟩ : syracuseStep 2500319 = 3750479) B3750479
theorem B8554207 : Blo 1666533 8554207 := bstep (se 1 (by rfl) ⟨6415655, by rfl⟩ : syracuseStep 8554207 = 12831311) B12831311
theorem B6416135 : Blo 1666533 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B2500415 : Blo 1666533 2500415 := bstep (se 1 (by rfl) ⟨1875311, by rfl⟩ : syracuseStep 2500415 = 3750623) B3750623
theorem B2500583 : Blo 1666533 2500583 := bstep (se 1 (by rfl) ⟨1875437, by rfl⟩ : syracuseStep 2500583 = 3750875) B3750875
theorem B2852839 : Blo 1666533 2852839 := bstep (se 1 (by rfl) ⟨2139629, by rfl⟩ : syracuseStep 2852839 = 4279259) B4279259
theorem B2500601 : Blo 1666533 2500601 := bstep (se 2 (by rfl) ⟨937725, by rfl⟩ : syracuseStep 2500601 = 1875451) B1875451
theorem B2500703 : Blo 1666533 2500703 := bstep (se 1 (by rfl) ⟨1875527, by rfl⟩ : syracuseStep 2500703 = 3751055) B3751055
theorem B12658841 : Blo 1666533 12658841 := bstep (se 2 (by rfl) ⟨4747065, by rfl⟩ : syracuseStep 12658841 = 9494131) B9494131
theorem B2500763 : Blo 1666533 2500763 := bstep (se 1 (by rfl) ⟨1875572, by rfl⟩ : syracuseStep 2500763 = 3751145) B3751145
theorem B2500799 : Blo 1666533 2500799 := bstep (se 1 (by rfl) ⟨1875599, by rfl⟩ : syracuseStep 2500799 = 3751199) B3751199
theorem B4221143 : Blo 1666533 4221143 := bstep (se 1 (by rfl) ⟨3165857, by rfl⟩ : syracuseStep 4221143 = 6331715) B6331715
theorem B2500841 : Blo 1666533 2500841 := bstep (se 2 (by rfl) ⟨937815, by rfl⟩ : syracuseStep 2500841 = 1875631) B1875631
theorem B2501147 : Blo 1666533 2501147 := bstep (se 1 (by rfl) ⟨1875860, by rfl⟩ : syracuseStep 2501147 = 3751721) B3751721
theorem B4221467 : Blo 1666533 4221467 := bstep (se 1 (by rfl) ⟨3166100, by rfl⟩ : syracuseStep 4221467 = 6332201) B6332201
theorem B2501225 : Blo 1666533 2501225 := bstep (se 2 (by rfl) ⟨937959, by rfl⟩ : syracuseStep 2501225 = 1875919) B1875919
theorem B7121591 : Blo 1666533 7121591 := bstep (se 1 (by rfl) ⟨5341193, by rfl⟩ : syracuseStep 7121591 = 10682387) B10682387
theorem B2812603 : Blo 1666533 2812603 := bstep (se 1 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 2812603 = 4218905) B4218905
theorem B2812907 : Blo 1666533 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B2501753 : Blo 1666533 2501753 := bstep (se 2 (by rfl) ⟨938157, by rfl⟩ : syracuseStep 2501753 = 1876315) B1876315
theorem B4746383 : Blo 1666533 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B15420581 : Blo 1666533 15420581 := bstep (se 4 (by rfl) ⟨1445679, by rfl⟩ : syracuseStep 15420581 = 2891359) B2891359
theorem B2501855 : Blo 1666533 2501855 := bstep (se 1 (by rfl) ⟨1876391, by rfl⟩ : syracuseStep 2501855 = 3752783) B3752783
theorem B2501897 : Blo 1666533 2501897 := bstep (se 2 (by rfl) ⟨938211, by rfl⟩ : syracuseStep 2501897 = 1876423) B1876423
theorem B2501999 : Blo 1666533 2501999 := bstep (se 1 (by rfl) ⟨1876499, by rfl⟩ : syracuseStep 2501999 = 3752999) B3752999
theorem B10685819 : Blo 1666533 10685819 := bstep (se 1 (by rfl) ⟨8014364, by rfl⟩ : syracuseStep 10685819 = 16028729) B16028729
theorem B8015287 : Blo 1666533 8015287 := bstep (se 1 (by rfl) ⟨6011465, by rfl⟩ : syracuseStep 8015287 = 12022931) B12022931
theorem B1666535 : Blo 1666533 1666535 := bstep (se 1 (by rfl) ⟨1249901, by rfl⟩ : syracuseStep 1666535 = 2499803) B2499803
theorem B4877815 : Blo 1666533 4877815 := bstep (se 1 (by rfl) ⟨3658361, by rfl⟩ : syracuseStep 4877815 = 7316723) B7316723
theorem B1666651 : Blo 1666533 1666651 := bstep (se 1 (by rfl) ⟨1249988, by rfl⟩ : syracuseStep 1666651 = 2499977) B2499977
theorem B10686127 : Blo 1666533 10686127 := bstep (se 1 (by rfl) ⟨8014595, by rfl⟩ : syracuseStep 10686127 = 16029191) B16029191
theorem B1666887 : Blo 1666533 1666887 := bstep (se 1 (by rfl) ⟨1250165, by rfl⟩ : syracuseStep 1666887 = 2500331) B2500331
theorem B6328145 : Blo 1666533 6328145 := bstep (se 2 (by rfl) ⟨2373054, by rfl⟩ : syracuseStep 6328145 = 4746109) B4746109
theorem B1667039 : Blo 1666533 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B12660785 : Blo 1666533 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B1667303 : Blo 1666533 1667303 := bstep (se 1 (by rfl) ⟨1250477, by rfl⟩ : syracuseStep 1667303 = 2500955) B2500955
theorem B177967459 : Blo 1666533 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B1667455 : Blo 1666533 1667455 := bstep (se 1 (by rfl) ⟨1250591, by rfl⟩ : syracuseStep 1667455 = 2501183) B2501183
theorem B1667535 : Blo 1666533 1667535 := bstep (se 1 (by rfl) ⟨1250651, by rfl⟩ : syracuseStep 1667535 = 2501303) B2501303
theorem B1667687 : Blo 1666533 1667687 := bstep (se 1 (by rfl) ⟨1250765, by rfl⟩ : syracuseStep 1667687 = 2501531) B2501531
theorem B6091379 : Blo 1666533 6091379 := bstep (se 1 (by rfl) ⟨4568534, by rfl⟩ : syracuseStep 6091379 = 9137069) B9137069
theorem B24040097 : Blo 1666533 24040097 := bstep (se 2 (by rfl) ⟨9015036, by rfl⟩ : syracuseStep 24040097 = 18030073) B18030073
theorem B3003247 : Blo 1666533 3003247 := bstep (se 1 (by rfl) ⟨2252435, by rfl⟩ : syracuseStep 3003247 = 4504871) B4504871
theorem B1667951 : Blo 1666533 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B5624747 : Blo 1666533 5624747 := bstep (se 1 (by rfl) ⟨4218560, by rfl⟩ : syracuseStep 5624747 = 8437121) B8437121
theorem B1668007 : Blo 1666533 1668007 := bstep (se 1 (by rfl) ⟨1251005, by rfl⟩ : syracuseStep 1668007 = 2502011) B2502011
theorem B12022759 : Blo 1666533 12022759 := bstep (se 1 (by rfl) ⟨9017069, by rfl⟩ : syracuseStep 12022759 = 18034139) B18034139
theorem B6009851 : Blo 1666533 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B19256399 : Blo 1666533 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B5625179 : Blo 1666533 5625179 := bstep (se 1 (by rfl) ⟨4218884, by rfl⟩ : syracuseStep 5625179 = 8437769) B8437769
theorem B20280719 : Blo 1666533 20280719 := bstep (se 1 (by rfl) ⟨15210539, by rfl⟩ : syracuseStep 20280719 = 30421079) B30421079
theorem B5625287 : Blo 1666533 5625287 := bstep (se 1 (by rfl) ⟨4218965, by rfl⟩ : syracuseStep 5625287 = 8437931) B8437931
theorem B5625611 : Blo 1666533 5625611 := bstep (se 1 (by rfl) ⟨4219208, by rfl⟩ : syracuseStep 5625611 = 8438417) B8438417
theorem B5068601 : Blo 1666533 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B10827769 : Blo 1666533 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B5625881 : Blo 1666533 5625881 := bstep (se 2 (by rfl) ⟨2109705, by rfl⟩ : syracuseStep 5625881 = 4219411) B4219411
theorem B2373727 : Blo 1666533 2373727 := bstep (se 1 (by rfl) ⟨1780295, by rfl⟩ : syracuseStep 2373727 = 3560591) B3560591
theorem B10279111 : Blo 1666533 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B3561769 : Blo 1666533 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B4749641 : Blo 1666533 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B5339515 : Blo 1666533 5339515 := bstep (se 1 (by rfl) ⟨4004636, by rfl⟩ : syracuseStep 5339515 = 8009273) B8009273
theorem B9492947 : Blo 1666533 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B18996281 : Blo 1666533 18996281 := bstep (se 2 (by rfl) ⟨7123605, by rfl⟩ : syracuseStep 18996281 = 14247211) B14247211
theorem B3750983 : Blo 1666533 3750983 := bstep (se 1 (by rfl) ⟨2813237, by rfl⟩ : syracuseStep 3750983 = 5626475) B5626475
theorem B3005561 : Blo 1666533 3005561 := bstep (se 2 (by rfl) ⟨1127085, by rfl⟩ : syracuseStep 3005561 = 2254171) B2254171
theorem B6331517 : Blo 1666533 6331517 := bstep (se 3 (by rfl) ⟨1187159, by rfl⟩ : syracuseStep 6331517 = 2374319) B2374319
theorem B5627231 : Blo 1666533 5627231 := bstep (se 1 (by rfl) ⟨4220423, by rfl⟩ : syracuseStep 5627231 = 8440847) B8440847
theorem B28474739 : Blo 1666533 28474739 := bstep (se 1 (by rfl) ⟨21356054, by rfl⟩ : syracuseStep 28474739 = 42712109) B42712109
theorem B27041161 : Blo 1666533 27041161 := bstep (se 2 (by rfl) ⟨10140435, by rfl⟩ : syracuseStep 27041161 = 20280871) B20280871
theorem B91250081 : Blo 1666533 91250081 := bstep (se 2 (by rfl) ⟨34218780, by rfl⟩ : syracuseStep 91250081 = 68437561) B68437561
theorem B2370182573 : Blo 1666533 2370182573 := bstep (se 3 (by rfl) ⟨444409232, by rfl⟩ : syracuseStep 2370182573 = 888818465) B888818465
theorem B3751379 : Blo 1666533 3751379 := bstep (se 1 (by rfl) ⟨2813534, by rfl⟩ : syracuseStep 3751379 = 5627069) B5627069
theorem B2670187 : Blo 1666533 2670187 := bstep (se 1 (by rfl) ⟨2002640, by rfl⟩ : syracuseStep 2670187 = 4005281) B4005281
theorem B3751649 : Blo 1666533 3751649 := bstep (se 2 (by rfl) ⟨1406868, by rfl⟩ : syracuseStep 3751649 = 2813737) B2813737
theorem B4218601 : Blo 1666533 4218601 := bstep (se 2 (by rfl) ⟨1581975, by rfl⟩ : syracuseStep 4218601 = 3163951) B3163951
theorem B6332215 : Blo 1666533 6332215 := bstep (se 1 (by rfl) ⟨4749161, by rfl⟩ : syracuseStep 6332215 = 9498323) B9498323
theorem B5627771 : Blo 1666533 5627771 := bstep (se 1 (by rfl) ⟨4220828, by rfl⟩ : syracuseStep 5627771 = 8441657) B8441657
theorem B3752171 : Blo 1666533 3752171 := bstep (se 1 (by rfl) ⟨2814128, by rfl⟩ : syracuseStep 3752171 = 5628257) B5628257
theorem B13705481 : Blo 1666533 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B14434735 : Blo 1666533 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B237289945 : Blo 1666533 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B7119353 : Blo 1666533 7119353 := bstep (se 2 (by rfl) ⟨2669757, by rfl⟩ : syracuseStep 7119353 = 5339515) B5339515
theorem B4006567 : Blo 1666533 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B12837599 : Blo 1666533 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B64947257 : Blo 1666533 64947257 := bstep (se 2 (by rfl) ⟨24355221, by rfl⟩ : syracuseStep 64947257 = 48710443) B48710443
theorem B2851951 : Blo 1666533 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B3753071 : Blo 1666533 3753071 := bstep (se 1 (by rfl) ⟨2814803, by rfl⟩ : syracuseStep 3753071 = 5629607) B5629607
theorem B4277423 : Blo 1666533 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B8439227 : Blo 1666533 8439227 := bstep (se 1 (by rfl) ⟨6329420, by rfl⟩ : syracuseStep 8439227 = 12658841) B12658841
theorem B36054881 : Blo 1666533 36054881 := bstep (se 2 (by rfl) ⟨13520580, by rfl⟩ : syracuseStep 36054881 = 27041161) B27041161
theorem B2500655 : Blo 1666533 2500655 := bstep (se 1 (by rfl) ⟨1875491, by rfl⟩ : syracuseStep 2500655 = 3750983) B3750983
theorem B4221011 : Blo 1666533 4221011 := bstep (se 1 (by rfl) ⟨3165758, by rfl⟩ : syracuseStep 4221011 = 6331517) B6331517
theorem B3164255 : Blo 1666533 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B14248169 : Blo 1666533 14248169 := bstep (se 2 (by rfl) ⟨5343063, by rfl⟩ : syracuseStep 14248169 = 10686127) B10686127
theorem B18983159 : Blo 1666533 18983159 := bstep (se 1 (by rfl) ⟨14237369, by rfl⟩ : syracuseStep 18983159 = 28474739) B28474739
theorem B11405609 : Blo 1666533 11405609 := bstep (se 2 (by rfl) ⟨4277103, by rfl⟩ : syracuseStep 11405609 = 8554207) B8554207
theorem B2500919 : Blo 1666533 2500919 := bstep (se 1 (by rfl) ⟨1875689, by rfl⟩ : syracuseStep 2500919 = 3751379) B3751379
theorem B2501099 : Blo 1666533 2501099 := bstep (se 1 (by rfl) ⟨1875824, by rfl⟩ : syracuseStep 2501099 = 3751649) B3751649
theorem B15215141 : Blo 1666533 15215141 := bstep (se 4 (by rfl) ⟨1426419, by rfl⟩ : syracuseStep 15215141 = 2852839) B2852839
theorem B14437025 : Blo 1666533 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B8440523 : Blo 1666533 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B3164969 : Blo 1666533 3164969 := bstep (se 2 (by rfl) ⟨1186863, by rfl⟩ : syracuseStep 3164969 = 2373727) B2373727
theorem B67677079 : Blo 1666533 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B1780799 : Blo 1666533 1780799 := bstep (se 1 (by rfl) ⟨1335599, by rfl⟩ : syracuseStep 1780799 = 2671199) B2671199
theorem B16026731 : Blo 1666533 16026731 := bstep (se 1 (by rfl) ⟨12020048, by rfl⟩ : syracuseStep 16026731 = 24040097) B24040097
theorem B2501801 : Blo 1666533 2501801 := bstep (se 2 (by rfl) ⟨938175, by rfl⟩ : syracuseStep 2501801 = 1876351) B1876351
theorem B2813339 : Blo 1666533 2813339 := bstep (se 1 (by rfl) ⟨2110004, by rfl⟩ : syracuseStep 2813339 = 4220009) B4220009
theorem B13520479 : Blo 1666533 13520479 := bstep (se 1 (by rfl) ⟨10140359, by rfl⟩ : syracuseStep 13520479 = 20280719) B20280719
theorem B1666663 : Blo 1666533 1666663 := bstep (se 1 (by rfl) ⟨1249997, by rfl⟩ : syracuseStep 1666663 = 2499995) B2499995
theorem B125054711 : Blo 1666533 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B1666811 : Blo 1666533 1666811 := bstep (se 1 (by rfl) ⟨1250108, by rfl⟩ : syracuseStep 1666811 = 2500217) B2500217
theorem B1666879 : Blo 1666533 1666879 := bstep (se 1 (by rfl) ⟨1250159, by rfl⟩ : syracuseStep 1666879 = 2500319) B2500319
theorem B3379067 : Blo 1666533 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B1666943 : Blo 1666533 1666943 := bstep (se 1 (by rfl) ⟨1250207, by rfl⟩ : syracuseStep 1666943 = 2500415) B2500415
theorem B1667055 : Blo 1666533 1667055 := bstep (se 1 (by rfl) ⟨1250291, by rfl⟩ : syracuseStep 1667055 = 2500583) B2500583
theorem B1667067 : Blo 1666533 1667067 := bstep (se 1 (by rfl) ⟨1250300, by rfl⟩ : syracuseStep 1667067 = 2500601) B2500601
theorem B1667135 : Blo 1666533 1667135 := bstep (se 1 (by rfl) ⟨1250351, by rfl⟩ : syracuseStep 1667135 = 2500703) B2500703
theorem B1667175 : Blo 1666533 1667175 := bstep (se 1 (by rfl) ⟨1250381, by rfl⟩ : syracuseStep 1667175 = 2500763) B2500763
theorem B1667199 : Blo 1666533 1667199 := bstep (se 1 (by rfl) ⟨1250399, by rfl⟩ : syracuseStep 1667199 = 2500799) B2500799
theorem B2814095 : Blo 1666533 2814095 := bstep (se 1 (by rfl) ⟨2110571, by rfl⟩ : syracuseStep 2814095 = 4221143) B4221143
theorem B1667227 : Blo 1666533 1667227 := bstep (se 1 (by rfl) ⟨1250420, by rfl⟩ : syracuseStep 1667227 = 2500841) B2500841
theorem B3166427 : Blo 1666533 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B6328631 : Blo 1666533 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B1667431 : Blo 1666533 1667431 := bstep (se 1 (by rfl) ⟨1250573, by rfl⟩ : syracuseStep 1667431 = 2501147) B2501147
theorem B2814311 : Blo 1666533 2814311 := bstep (se 1 (by rfl) ⟨2110733, by rfl⟩ : syracuseStep 2814311 = 4221467) B4221467
theorem B1667483 : Blo 1666533 1667483 := bstep (se 1 (by rfl) ⟨1250612, by rfl⟩ : syracuseStep 1667483 = 2501225) B2501225
theorem B4747727 : Blo 1666533 4747727 := bstep (se 1 (by rfl) ⟨3560795, by rfl⟩ : syracuseStep 4747727 = 7121591) B7121591
theorem B10687049 : Blo 1666533 10687049 := bstep (se 2 (by rfl) ⟨4007643, by rfl⟩ : syracuseStep 10687049 = 8015287) B8015287
theorem B1667835 : Blo 1666533 1667835 := bstep (se 1 (by rfl) ⟨1250876, by rfl⟩ : syracuseStep 1667835 = 2501753) B2501753
theorem B2003707 : Blo 1666533 2003707 := bstep (se 1 (by rfl) ⟨1502780, by rfl⟩ : syracuseStep 2003707 = 3005561) B3005561
theorem B3560249 : Blo 1666533 3560249 := bstep (se 2 (by rfl) ⟨1335093, by rfl⟩ : syracuseStep 3560249 = 2670187) B2670187
theorem B1667903 : Blo 1666533 1667903 := bstep (se 1 (by rfl) ⟨1250927, by rfl⟩ : syracuseStep 1667903 = 2501855) B2501855
theorem B1667931 : Blo 1666533 1667931 := bstep (se 1 (by rfl) ⟨1250948, by rfl⟩ : syracuseStep 1667931 = 2501897) B2501897
theorem B1667999 : Blo 1666533 1667999 := bstep (se 1 (by rfl) ⟨1250999, by rfl⟩ : syracuseStep 1667999 = 2501999) B2501999
theorem B7123879 : Blo 1666533 7123879 := bstep (se 1 (by rfl) ⟨5342909, by rfl⟩ : syracuseStep 7123879 = 10685819) B10685819
theorem B5624801 : Blo 1666533 5624801 := bstep (se 2 (by rfl) ⟨2109300, by rfl⟩ : syracuseStep 5624801 = 4218601) B4218601
theorem B8442953 : Blo 1666533 8442953 := bstep (se 2 (by rfl) ⟨3166107, by rfl⟩ : syracuseStep 8442953 = 6332215) B6332215
theorem B37533293 : Blo 1666533 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B4749025 : Blo 1666533 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B4060919 : Blo 1666533 4060919 := bstep (se 1 (by rfl) ⟨3045689, by rfl⟩ : syracuseStep 4060919 = 6091379) B6091379
theorem B6330271 : Blo 1666533 6330271 := bstep (se 1 (by rfl) ⟨4747703, by rfl⟩ : syracuseStep 6330271 = 9495407) B9495407
theorem B3749831 : Blo 1666533 3749831 := bstep (se 1 (by rfl) ⟨2812373, by rfl⟩ : syracuseStep 3749831 = 5624747) B5624747
theorem B3750119 : Blo 1666533 3750119 := bstep (se 1 (by rfl) ⟨2812589, by rfl⟩ : syracuseStep 3750119 = 5625179) B5625179
theorem B3750137 : Blo 1666533 3750137 := bstep (se 2 (by rfl) ⟨1406301, by rfl⟩ : syracuseStep 3750137 = 2812603) B2812603
theorem B3750191 : Blo 1666533 3750191 := bstep (se 1 (by rfl) ⟨2812643, by rfl⟩ : syracuseStep 3750191 = 5625287) B5625287
theorem B6330743 : Blo 1666533 6330743 := bstep (se 1 (by rfl) ⟨4748057, by rfl⟩ : syracuseStep 6330743 = 9496115) B9496115
theorem B3561889 : Blo 1666533 3561889 := bstep (se 2 (by rfl) ⟨1335708, by rfl⟩ : syracuseStep 3561889 = 2671417) B2671417
theorem B4004329 : Blo 1666533 4004329 := bstep (se 2 (by rfl) ⟨1501623, by rfl⟩ : syracuseStep 4004329 = 3003247) B3003247
theorem B3750407 : Blo 1666533 3750407 := bstep (se 1 (by rfl) ⟨2812805, by rfl⟩ : syracuseStep 3750407 = 5625611) B5625611
theorem B16030345 : Blo 1666533 16030345 := bstep (se 2 (by rfl) ⟨6011379, by rfl⟩ : syracuseStep 16030345 = 12022759) B12022759
theorem B3750587 : Blo 1666533 3750587 := bstep (se 1 (by rfl) ⟨2812940, by rfl⟩ : syracuseStep 3750587 = 5625881) B5625881
theorem B1875271 : Blo 1666533 1875271 := bstep (se 1 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 1875271 = 2812907) B2812907
theorem B6503753 : Blo 1666533 6503753 := bstep (se 2 (by rfl) ⟨2438907, by rfl⟩ : syracuseStep 6503753 = 4877815) B4877815
theorem B12664187 : Blo 1666533 12664187 := bstep (se 1 (by rfl) ⟨9498140, by rfl⟩ : syracuseStep 12664187 = 18996281) B18996281
theorem B29678993 : Blo 1666533 29678993 := bstep (se 2 (by rfl) ⟨11129622, by rfl⟩ : syracuseStep 29678993 = 22259245) B22259245
theorem B10280387 : Blo 1666533 10280387 := bstep (se 1 (by rfl) ⟨7710290, by rfl⟩ : syracuseStep 10280387 = 15420581) B15420581
theorem B3751487 : Blo 1666533 3751487 := bstep (se 1 (by rfl) ⟨2813615, by rfl⟩ : syracuseStep 3751487 = 5627231) B5627231
theorem B60833387 : Blo 1666533 60833387 := bstep (se 1 (by rfl) ⟨45625040, by rfl⟩ : syracuseStep 60833387 = 91250081) B91250081
theorem B1580121715 : Blo 1666533 1580121715 := bstep (se 1 (by rfl) ⟨1185091286, by rfl⟩ : syracuseStep 1580121715 = 2370182573) B2370182573
theorem B4218763 : Blo 1666533 4218763 := bstep (se 1 (by rfl) ⟨3164072, by rfl⟩ : syracuseStep 4218763 = 6328145) B6328145
theorem B3751847 : Blo 1666533 3751847 := bstep (se 1 (by rfl) ⟨2813885, by rfl⟩ : syracuseStep 3751847 = 5627771) B5627771
theorem B1876063 : Blo 1666533 1876063 := bstep (se 1 (by rfl) ⟨1407047, by rfl⟩ : syracuseStep 1876063 = 2814095) B2814095
theorem B4219087 : Blo 1666533 4219087 := bstep (se 1 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 4219087 = 6328631) B6328631
theorem B1876207 : Blo 1666533 1876207 := bstep (se 1 (by rfl) ⟨1407155, by rfl⟩ : syracuseStep 1876207 = 2814311) B2814311
theorem B5628635 : Blo 1666533 5628635 := bstep (se 1 (by rfl) ⟨4221476, by rfl⟩ : syracuseStep 5628635 = 8442953) B8442953
theorem B2851615 : Blo 1666533 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B21373793 : Blo 1666533 21373793 := bstep (se 2 (by rfl) ⟨8015172, by rfl⟩ : syracuseStep 21373793 = 16030345) B16030345
theorem B2671609 : Blo 1666533 2671609 := bstep (se 2 (by rfl) ⟨1001853, by rfl⟩ : syracuseStep 2671609 = 2003707) B2003707
theorem B90236105 : Blo 1666533 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B24036587 : Blo 1666533 24036587 := bstep (se 1 (by rfl) ⟨18027440, by rfl⟩ : syracuseStep 24036587 = 36054881) B36054881
theorem B2499887 : Blo 1666533 2499887 := bstep (se 1 (by rfl) ⟨1874915, by rfl⟩ : syracuseStep 2499887 = 3749831) B3749831
theorem B3802601 : Blo 1666533 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B2500079 : Blo 1666533 2500079 := bstep (se 1 (by rfl) ⟨1875059, by rfl⟩ : syracuseStep 2500079 = 3750119) B3750119
theorem B2500091 : Blo 1666533 2500091 := bstep (se 1 (by rfl) ⟨1875068, by rfl⟩ : syracuseStep 2500091 = 3750137) B3750137
theorem B7603739 : Blo 1666533 7603739 := bstep (se 1 (by rfl) ⟨5702804, by rfl⟩ : syracuseStep 7603739 = 11405609) B11405609
theorem B2500127 : Blo 1666533 2500127 := bstep (se 1 (by rfl) ⟨1875095, by rfl⟩ : syracuseStep 2500127 = 3750191) B3750191
theorem B4220495 : Blo 1666533 4220495 := bstep (se 1 (by rfl) ⟨3165371, by rfl⟩ : syracuseStep 4220495 = 6330743) B6330743
theorem B2500271 : Blo 1666533 2500271 := bstep (se 1 (by rfl) ⟨1875203, by rfl⟩ : syracuseStep 2500271 = 3750407) B3750407
theorem B10143427 : Blo 1666533 10143427 := bstep (se 1 (by rfl) ⟨7607570, by rfl⟩ : syracuseStep 10143427 = 15215141) B15215141
theorem B2500361 : Blo 1666533 2500361 := bstep (se 2 (by rfl) ⟨937635, by rfl⟩ : syracuseStep 2500361 = 1875271) B1875271
theorem B2500391 : Blo 1666533 2500391 := bstep (se 1 (by rfl) ⟨1875293, by rfl⟩ : syracuseStep 2500391 = 3750587) B3750587
theorem B10684487 : Blo 1666533 10684487 := bstep (se 1 (by rfl) ⟨8013365, by rfl⟩ : syracuseStep 10684487 = 16026731) B16026731
theorem B2106828953 : Blo 1666533 2106828953 := bstep (se 2 (by rfl) ⟨790060857, by rfl⟩ : syracuseStep 2106828953 = 1580121715) B1580121715
theorem B4335835 : Blo 1666533 4335835 := bstep (se 1 (by rfl) ⟨3251876, by rfl⟩ : syracuseStep 4335835 = 6503753) B6503753
theorem B19785995 : Blo 1666533 19785995 := bstep (se 1 (by rfl) ⟨14839496, by rfl⟩ : syracuseStep 19785995 = 29678993) B29678993
theorem B2500991 : Blo 1666533 2500991 := bstep (se 1 (by rfl) ⟨1875743, by rfl⟩ : syracuseStep 2500991 = 3751487) B3751487
theorem B8440361 : Blo 1666533 8440361 := bstep (se 2 (by rfl) ⟨3165135, by rfl⟩ : syracuseStep 8440361 = 6330271) B6330271
theorem B2501231 : Blo 1666533 2501231 := bstep (se 1 (by rfl) ⟨1875923, by rfl⟩ : syracuseStep 2501231 = 3751847) B3751847
theorem B2501447 : Blo 1666533 2501447 := bstep (se 1 (by rfl) ⟨1876085, by rfl⟩ : syracuseStep 2501447 = 3752171) B3752171
theorem B3165151 : Blo 1666533 3165151 := bstep (se 1 (by rfl) ⟨2373863, by rfl⟩ : syracuseStep 3165151 = 4747727) B4747727
theorem B4746235 : Blo 1666533 4746235 := bstep (se 1 (by rfl) ⟨3559676, by rfl⟩ : syracuseStep 4746235 = 7119353) B7119353
theorem B19246313 : Blo 1666533 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B316386593 : Blo 1666533 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B36547949 : Blo 1666533 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B43298171 : Blo 1666533 43298171 := bstep (se 1 (by rfl) ⟨32473628, by rfl⟩ : syracuseStep 43298171 = 64947257) B64947257
theorem B2502047 : Blo 1666533 2502047 := bstep (se 1 (by rfl) ⟨1876535, by rfl⟩ : syracuseStep 2502047 = 3753071) B3753071
theorem B21368357 : Blo 1666533 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B25022195 : Blo 1666533 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B9498505 : Blo 1666533 9498505 := bstep (se 2 (by rfl) ⟨3561939, by rfl⟩ : syracuseStep 9498505 = 7123879) B7123879
theorem B1667103 : Blo 1666533 1667103 := bstep (se 1 (by rfl) ⟨1250327, by rfl⟩ : syracuseStep 1667103 = 2500655) B2500655
theorem B2814007 : Blo 1666533 2814007 := bstep (se 1 (by rfl) ⟨2110505, by rfl⟩ : syracuseStep 2814007 = 4221011) B4221011
theorem B2109503 : Blo 1666533 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B9498779 : Blo 1666533 9498779 := bstep (se 1 (by rfl) ⟨7124084, by rfl⟩ : syracuseStep 9498779 = 14248169) B14248169
theorem B1667279 : Blo 1666533 1667279 := bstep (se 1 (by rfl) ⟨1250459, by rfl⟩ : syracuseStep 1667279 = 2500919) B2500919
theorem B162222365 : Blo 1666533 162222365 := bstep (se 3 (by rfl) ⟨30416693, by rfl⟩ : syracuseStep 162222365 = 60833387) B60833387
theorem B1667399 : Blo 1666533 1667399 := bstep (se 1 (by rfl) ⟨1250549, by rfl⟩ : syracuseStep 1667399 = 2501099) B2501099
theorem B2109979 : Blo 1666533 2109979 := bstep (se 1 (by rfl) ⟨1582484, by rfl⟩ : syracuseStep 2109979 = 3164969) B3164969
theorem B1667867 : Blo 1666533 1667867 := bstep (se 1 (by rfl) ⟨1250900, by rfl⟩ : syracuseStep 1667867 = 2501801) B2501801
theorem B18027305 : Blo 1666533 18027305 := bstep (se 2 (by rfl) ⟨6760239, by rfl⟩ : syracuseStep 18027305 = 13520479) B13520479
theorem B8442791 : Blo 1666533 8442791 := bstep (se 1 (by rfl) ⟨6332093, by rfl⟩ : syracuseStep 8442791 = 12664187) B12664187
theorem B6853591 : Blo 1666533 6853591 := bstep (se 1 (by rfl) ⟨5140193, by rfl⟩ : syracuseStep 6853591 = 10280387) B10280387
theorem B5625017 : Blo 1666533 5625017 := bstep (se 2 (by rfl) ⟨2109381, by rfl⟩ : syracuseStep 5625017 = 4218763) B4218763
theorem B2110951 : Blo 1666533 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B4748797 : Blo 1666533 4748797 := bstep (se 3 (by rfl) ⟨890399, by rfl⟩ : syracuseStep 4748797 = 1780799) B1780799
theorem B7124699 : Blo 1666533 7124699 := bstep (se 1 (by rfl) ⟨5343524, by rfl⟩ : syracuseStep 7124699 = 10687049) B10687049
theorem B8558399 : Blo 1666533 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B2373499 : Blo 1666533 2373499 := bstep (se 1 (by rfl) ⟨1780124, by rfl⟩ : syracuseStep 2373499 = 3560249) B3560249
theorem B4749185 : Blo 1666533 4749185 := bstep (se 2 (by rfl) ⟨1780944, by rfl⟩ : syracuseStep 4749185 = 3561889) B3561889
theorem B5339105 : Blo 1666533 5339105 := bstep (se 2 (by rfl) ⟨2002164, by rfl⟩ : syracuseStep 5339105 = 4004329) B4004329
theorem B3749867 : Blo 1666533 3749867 := bstep (se 1 (by rfl) ⟨2812400, by rfl⟩ : syracuseStep 3749867 = 5624801) B5624801
theorem B5626151 : Blo 1666533 5626151 := bstep (se 1 (by rfl) ⟨4219613, by rfl⟩ : syracuseStep 5626151 = 8439227) B8439227
theorem B12655439 : Blo 1666533 12655439 := bstep (se 1 (by rfl) ⟨9491579, by rfl⟩ : syracuseStep 12655439 = 18983159) B18983159
theorem B9624683 : Blo 1666533 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B5627015 : Blo 1666533 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B10829117 : Blo 1666533 10829117 := bstep (se 3 (by rfl) ⟨2030459, by rfl⟩ : syracuseStep 10829117 = 4060919) B4060919
theorem B1875559 : Blo 1666533 1875559 := bstep (se 1 (by rfl) ⟨1406669, by rfl⟩ : syracuseStep 1875559 = 2813339) B2813339
theorem B6332033 : Blo 1666533 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B83369807 : Blo 1666533 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B2252711 : Blo 1666533 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B3752009 : Blo 1666533 3752009 := bstep (se 2 (by rfl) ⟨1407003, by rfl⟩ : syracuseStep 3752009 = 2814007) B2814007
theorem B6332519 : Blo 1666533 6332519 := bstep (se 1 (by rfl) ⟨4749389, by rfl⟩ : syracuseStep 6332519 = 9498779) B9498779
theorem B25665821 : Blo 1666533 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B3752423 : Blo 1666533 3752423 := bstep (se 1 (by rfl) ⟨2814317, by rfl⟩ : syracuseStep 3752423 = 5628635) B5628635
theorem B12018203 : Blo 1666533 12018203 := bstep (se 1 (by rfl) ⟨9013652, by rfl⟩ : syracuseStep 12018203 = 18027305) B18027305
theorem B5628527 : Blo 1666533 5628527 := bstep (se 1 (by rfl) ⟨4221395, by rfl⟩ : syracuseStep 5628527 = 8442791) B8442791
theorem B16024391 : Blo 1666533 16024391 := bstep (se 1 (by rfl) ⟨12018293, by rfl⟩ : syracuseStep 16024391 = 24036587) B24036587
theorem B3802153 : Blo 1666533 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B4220201 : Blo 1666533 4220201 := bstep (se 2 (by rfl) ⟨1582575, by rfl⟩ : syracuseStep 4220201 = 3165151) B3165151
theorem B2499911 : Blo 1666533 2499911 := bstep (se 1 (by rfl) ⟨1874933, by rfl⟩ : syracuseStep 2499911 = 3749867) B3749867
theorem B1404552635 : Blo 1666533 1404552635 := bstep (se 1 (by rfl) ⟨1053414476, by rfl⟩ : syracuseStep 1404552635 = 2106828953) B2106828953
theorem B13190663 : Blo 1666533 13190663 := bstep (se 1 (by rfl) ⟨9892997, by rfl⟩ : syracuseStep 13190663 = 19785995) B19785995
theorem B18999197 : Blo 1666533 18999197 := bstep (se 3 (by rfl) ⟨3562349, by rfl⟩ : syracuseStep 18999197 = 7124699) B7124699
theorem B2500745 : Blo 1666533 2500745 := bstep (se 2 (by rfl) ⟨937779, by rfl⟩ : syracuseStep 2500745 = 1875559) B1875559
theorem B12830875 : Blo 1666533 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B7219411 : Blo 1666533 7219411 := bstep (se 1 (by rfl) ⟨5414558, by rfl⟩ : syracuseStep 7219411 = 10829117) B10829117
theorem B24365299 : Blo 1666533 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B4221355 : Blo 1666533 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B6007229 : Blo 1666533 6007229 := bstep (se 3 (by rfl) ⟨1126355, by rfl⟩ : syracuseStep 6007229 = 2252711) B2252711
theorem B16681463 : Blo 1666533 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B3164665 : Blo 1666533 3164665 := bstep (se 2 (by rfl) ⟨1186749, by rfl⟩ : syracuseStep 3164665 = 2373499) B2373499
theorem B2501417 : Blo 1666533 2501417 := bstep (se 2 (by rfl) ⟨938031, by rfl⟩ : syracuseStep 2501417 = 1876063) B1876063
theorem B2501609 : Blo 1666533 2501609 := bstep (se 2 (by rfl) ⟨938103, by rfl⟩ : syracuseStep 2501609 = 1876207) B1876207
theorem B14249195 : Blo 1666533 14249195 := bstep (se 1 (by rfl) ⟨10686896, by rfl⟩ : syracuseStep 14249195 = 21373793) B21373793
theorem B2813305 : Blo 1666533 2813305 := bstep (se 2 (by rfl) ⟨1054989, by rfl⟩ : syracuseStep 2813305 = 2109979) B2109979
theorem B60157403 : Blo 1666533 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B1666591 : Blo 1666533 1666591 := bstep (se 1 (by rfl) ⟨1249943, by rfl⟩ : syracuseStep 1666591 = 2499887) B2499887
theorem B2535067 : Blo 1666533 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B1666719 : Blo 1666533 1666719 := bstep (se 1 (by rfl) ⟨1250039, by rfl⟩ : syracuseStep 1666719 = 2500079) B2500079
theorem B1666727 : Blo 1666533 1666727 := bstep (se 1 (by rfl) ⟨1250045, by rfl⟩ : syracuseStep 1666727 = 2500091) B2500091
theorem B1666751 : Blo 1666533 1666751 := bstep (se 1 (by rfl) ⟨1250063, by rfl⟩ : syracuseStep 1666751 = 2500127) B2500127
theorem B2813663 : Blo 1666533 2813663 := bstep (se 1 (by rfl) ⟨2110247, by rfl⟩ : syracuseStep 2813663 = 4220495) B4220495
theorem B1666847 : Blo 1666533 1666847 := bstep (se 1 (by rfl) ⟨1250135, by rfl⟩ : syracuseStep 1666847 = 2500271) B2500271
theorem B1666907 : Blo 1666533 1666907 := bstep (se 1 (by rfl) ⟨1250180, by rfl⟩ : syracuseStep 1666907 = 2500361) B2500361
theorem B1666927 : Blo 1666533 1666927 := bstep (se 1 (by rfl) ⟨1250195, by rfl⟩ : syracuseStep 1666927 = 2500391) B2500391
theorem B5705599 : Blo 1666533 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B3166123 : Blo 1666533 3166123 := bstep (se 1 (by rfl) ⟨2374592, by rfl⟩ : syracuseStep 3166123 = 4749185) B4749185
theorem B3559403 : Blo 1666533 3559403 := bstep (se 1 (by rfl) ⟨2669552, by rfl⟩ : syracuseStep 3559403 = 5339105) B5339105
theorem B6328313 : Blo 1666533 6328313 := bstep (se 2 (by rfl) ⟨2373117, by rfl⟩ : syracuseStep 6328313 = 4746235) B4746235
theorem B7122991 : Blo 1666533 7122991 := bstep (se 1 (by rfl) ⟨5342243, by rfl⟩ : syracuseStep 7122991 = 10684487) B10684487
theorem B1667327 : Blo 1666533 1667327 := bstep (se 1 (by rfl) ⟨1250495, by rfl⟩ : syracuseStep 1667327 = 2500991) B2500991
theorem B1667487 : Blo 1666533 1667487 := bstep (se 1 (by rfl) ⟨1250615, by rfl⟩ : syracuseStep 1667487 = 2501231) B2501231
theorem B1667631 : Blo 1666533 1667631 := bstep (se 1 (by rfl) ⟨1250723, by rfl⟩ : syracuseStep 1667631 = 2501447) B2501447
theorem B2814601 : Blo 1666533 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B210924395 : Blo 1666533 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B28865447 : Blo 1666533 28865447 := bstep (se 1 (by rfl) ⟨21649085, by rfl⟩ : syracuseStep 28865447 = 43298171) B43298171
theorem B1668031 : Blo 1666533 1668031 := bstep (se 1 (by rfl) ⟨1251023, by rfl⟩ : syracuseStep 1668031 = 2502047) B2502047
theorem B55579871 : Blo 1666533 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B5625341 : Blo 1666533 5625341 := bstep (se 3 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 5625341 = 2109503) B2109503
theorem B108148243 : Blo 1666533 108148243 := bstep (se 1 (by rfl) ⟨81111182, by rfl⟩ : syracuseStep 108148243 = 162222365) B162222365
theorem B5625449 : Blo 1666533 5625449 := bstep (se 2 (by rfl) ⟨2109543, by rfl⟩ : syracuseStep 5625449 = 4219087) B4219087
theorem B5781113 : Blo 1666533 5781113 := bstep (se 2 (by rfl) ⟨2167917, by rfl⟩ : syracuseStep 5781113 = 4335835) B4335835
theorem B3750011 : Blo 1666533 3750011 := bstep (se 1 (by rfl) ⟨2812508, by rfl⟩ : syracuseStep 3750011 = 5625017) B5625017
theorem B5069159 : Blo 1666533 5069159 := bstep (se 1 (by rfl) ⟨3801869, by rfl⟩ : syracuseStep 5069159 = 7603739) B7603739
theorem B3562145 : Blo 1666533 3562145 := bstep (se 2 (by rfl) ⟨1335804, by rfl⟩ : syracuseStep 3562145 = 2671609) B2671609
theorem B3750767 : Blo 1666533 3750767 := bstep (se 1 (by rfl) ⟨2813075, by rfl⟩ : syracuseStep 3750767 = 5626151) B5626151
theorem B5626907 : Blo 1666533 5626907 := bstep (se 1 (by rfl) ⟨4220180, by rfl⟩ : syracuseStep 5626907 = 8440361) B8440361
theorem B8436959 : Blo 1666533 8436959 := bstep (se 1 (by rfl) ⟨6327719, by rfl⟩ : syracuseStep 8436959 = 12655439) B12655439
theorem B6331729 : Blo 1666533 6331729 := bstep (se 2 (by rfl) ⟨2374398, by rfl⟩ : syracuseStep 6331729 = 4748797) B4748797
theorem B3751343 : Blo 1666533 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B13524569 : Blo 1666533 13524569 := bstep (se 2 (by rfl) ⟨5071713, by rfl⟩ : syracuseStep 13524569 = 10143427) B10143427
theorem B14245571 : Blo 1666533 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B36552485 : Blo 1666533 36552485 := bstep (se 4 (by rfl) ⟨3426795, by rfl⟩ : syracuseStep 36552485 = 6853591) B6853591
theorem B12664673 : Blo 1666533 12664673 := bstep (se 2 (by rfl) ⟨4749252, by rfl⟩ : syracuseStep 12664673 = 9498505) B9498505
theorem B8012135 : Blo 1666533 8012135 := bstep (se 1 (by rfl) ⟨6009101, by rfl⟩ : syracuseStep 8012135 = 12018203) B12018203
theorem B3752351 : Blo 1666533 3752351 := bstep (se 1 (by rfl) ⟨2814263, by rfl⟩ : syracuseStep 3752351 = 5628527) B5628527
theorem B10682927 : Blo 1666533 10682927 := bstep (se 1 (by rfl) ⟨8012195, by rfl⟩ : syracuseStep 10682927 = 16024391) B16024391
theorem B5628473 : Blo 1666533 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B140616263 : Blo 1666533 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B19243631 : Blo 1666533 19243631 := bstep (se 1 (by rfl) ⟨14432723, by rfl⟩ : syracuseStep 19243631 = 28865447) B28865447
theorem B4219553 : Blo 1666533 4219553 := bstep (se 2 (by rfl) ⟨1582332, by rfl⟩ : syracuseStep 4219553 = 3164665) B3164665
theorem B37053247 : Blo 1666533 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B3752801 : Blo 1666533 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B38503525 : Blo 1666533 38503525 := bstep (se 4 (by rfl) ⟨3609705, by rfl⟩ : syracuseStep 38503525 = 7219411) B7219411
theorem B12666131 : Blo 1666533 12666131 := bstep (se 1 (by rfl) ⟨9499598, by rfl⟩ : syracuseStep 12666131 = 18999197) B18999197
theorem B2500007 : Blo 1666533 2500007 := bstep (se 1 (by rfl) ⟨1875005, by rfl⟩ : syracuseStep 2500007 = 3750011) B3750011
theorem B2500511 : Blo 1666533 2500511 := bstep (se 1 (by rfl) ⟨1875383, by rfl⟩ : syracuseStep 2500511 = 3750767) B3750767
theorem B144197657 : Blo 1666533 144197657 := bstep (se 2 (by rfl) ⟨54074121, by rfl⟩ : syracuseStep 144197657 = 108148243) B108148243
theorem B2500895 : Blo 1666533 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B9497047 : Blo 1666533 9497047 := bstep (se 1 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 9497047 = 14245571) B14245571
theorem B4221497 : Blo 1666533 4221497 := bstep (se 2 (by rfl) ⟨1583061, by rfl⟩ : syracuseStep 4221497 = 3166123) B3166123
theorem B2501339 : Blo 1666533 2501339 := bstep (se 1 (by rfl) ⟨1876004, by rfl⟩ : syracuseStep 2501339 = 3752009) B3752009
theorem B9497321 : Blo 1666533 9497321 := bstep (se 2 (by rfl) ⟨3561495, by rfl⟩ : syracuseStep 9497321 = 7122991) B7122991
theorem B4221679 : Blo 1666533 4221679 := bstep (se 1 (by rfl) ⟨3166259, by rfl⟩ : syracuseStep 4221679 = 6332519) B6332519
theorem B2501615 : Blo 1666533 2501615 := bstep (se 1 (by rfl) ⟨1876211, by rfl⟩ : syracuseStep 2501615 = 3752423) B3752423
theorem B68431333 : Blo 1666533 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B2813467 : Blo 1666533 2813467 := bstep (se 1 (by rfl) ⟨2110100, by rfl⟩ : syracuseStep 2813467 = 4220201) B4220201
theorem B1666607 : Blo 1666533 1666607 := bstep (se 1 (by rfl) ⟨1249955, by rfl⟩ : syracuseStep 1666607 = 2499911) B2499911
theorem B8793775 : Blo 1666533 8793775 := bstep (se 1 (by rfl) ⟨6595331, by rfl⟩ : syracuseStep 8793775 = 13190663) B13190663
theorem B3854075 : Blo 1666533 3854075 := bstep (se 1 (by rfl) ⟨2890556, by rfl⟩ : syracuseStep 3854075 = 5781113) B5781113
theorem B1667163 : Blo 1666533 1667163 := bstep (se 1 (by rfl) ⟨1250372, by rfl⟩ : syracuseStep 1667163 = 2500745) B2500745
theorem B3379439 : Blo 1666533 3379439 := bstep (se 1 (by rfl) ⟨2534579, by rfl⟩ : syracuseStep 3379439 = 5069159) B5069159
theorem B11120975 : Blo 1666533 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B8442305 : Blo 1666533 8442305 := bstep (se 2 (by rfl) ⟨3165864, by rfl⟩ : syracuseStep 8442305 = 6331729) B6331729
theorem B1667611 : Blo 1666533 1667611 := bstep (se 1 (by rfl) ⟨1250708, by rfl⟩ : syracuseStep 1667611 = 2501417) B2501417
theorem B1667739 : Blo 1666533 1667739 := bstep (se 1 (by rfl) ⟨1250804, by rfl⟩ : syracuseStep 1667739 = 2501609) B2501609
theorem B97473293 : Blo 1666533 97473293 := bstep (se 3 (by rfl) ⟨18276242, by rfl⟩ : syracuseStep 97473293 = 36552485) B36552485
theorem B5624639 : Blo 1666533 5624639 := bstep (se 1 (by rfl) ⟨4218479, by rfl⟩ : syracuseStep 5624639 = 8436959) B8436959
theorem B9499463 : Blo 1666533 9499463 := bstep (se 1 (by rfl) ⟨7124597, by rfl⟩ : syracuseStep 9499463 = 14249195) B14249195
theorem B3380089 : Blo 1666533 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B40104935 : Blo 1666533 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B9016379 : Blo 1666533 9016379 := bstep (se 1 (by rfl) ⟨6762284, by rfl⟩ : syracuseStep 9016379 = 13524569) B13524569
theorem B7607465 : Blo 1666533 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B8443115 : Blo 1666533 8443115 := bstep (se 1 (by rfl) ⟨6332336, by rfl⟩ : syracuseStep 8443115 = 12664673) B12664673
theorem B9491741 : Blo 1666533 9491741 := bstep (se 3 (by rfl) ⟨1779701, by rfl⟩ : syracuseStep 9491741 = 3559403) B3559403
theorem B17110547 : Blo 1666533 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B32487065 : Blo 1666533 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B936368423 : Blo 1666533 936368423 := bstep (se 1 (by rfl) ⟨702276317, by rfl⟩ : syracuseStep 936368423 = 1404552635) B1404552635
theorem B3750227 : Blo 1666533 3750227 := bstep (se 1 (by rfl) ⟨2812670, by rfl⟩ : syracuseStep 3750227 = 5625341) B5625341
theorem B3750299 : Blo 1666533 3750299 := bstep (se 1 (by rfl) ⟨2812724, by rfl⟩ : syracuseStep 3750299 = 5625449) B5625449
theorem B5069537 : Blo 1666533 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B4004819 : Blo 1666533 4004819 := bstep (se 1 (by rfl) ⟨3003614, by rfl⟩ : syracuseStep 4004819 = 6007229) B6007229
theorem B2374763 : Blo 1666533 2374763 := bstep (se 1 (by rfl) ⟨1781072, by rfl⟩ : syracuseStep 2374763 = 3562145) B3562145
theorem B3751073 : Blo 1666533 3751073 := bstep (se 2 (by rfl) ⟨1406652, by rfl⟩ : syracuseStep 3751073 = 2813305) B2813305
theorem B3751271 : Blo 1666533 3751271 := bstep (se 1 (by rfl) ⟨2813453, by rfl⟩ : syracuseStep 3751271 = 5626907) B5626907
theorem B1875775 : Blo 1666533 1875775 := bstep (se 1 (by rfl) ⟨1406831, by rfl⟩ : syracuseStep 1875775 = 2813663) B2813663
theorem B4218875 : Blo 1666533 4218875 := bstep (se 1 (by rfl) ⟨3164156, by rfl⟩ : syracuseStep 4218875 = 6328313) B6328313
theorem B7413983 : Blo 1666533 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B6332701 : Blo 1666533 6332701 := bstep (se 3 (by rfl) ⟨1187381, by rfl⟩ : syracuseStep 6332701 = 2374763) B2374763
theorem B5628203 : Blo 1666533 5628203 := bstep (se 1 (by rfl) ⟨4221152, by rfl⟩ : syracuseStep 5628203 = 8442305) B8442305
theorem B3752315 : Blo 1666533 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B6332975 : Blo 1666533 6332975 := bstep (se 1 (by rfl) ⟨4749731, by rfl⟩ : syracuseStep 6332975 = 9499463) B9499463
theorem B9011837 : Blo 1666533 9011837 := bstep (se 3 (by rfl) ⟨1689719, by rfl⟩ : syracuseStep 9011837 = 3379439) B3379439
theorem B5071643 : Blo 1666533 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B5628743 : Blo 1666533 5628743 := bstep (se 1 (by rfl) ⟨4221557, by rfl⟩ : syracuseStep 5628743 = 8443115) B8443115
theorem B46900133 : Blo 1666533 46900133 := bstep (se 4 (by rfl) ⟨4396887, by rfl⟩ : syracuseStep 46900133 = 8793775) B8793775
theorem B21365693 : Blo 1666533 21365693 := bstep (se 3 (by rfl) ⟨4006067, by rfl⟩ : syracuseStep 21365693 = 8012135) B8012135
theorem B5628905 : Blo 1666533 5628905 := bstep (se 2 (by rfl) ⟨2110839, by rfl⟩ : syracuseStep 5628905 = 4221679) B4221679
theorem B4506785 : Blo 1666533 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B2500151 : Blo 1666533 2500151 := bstep (se 1 (by rfl) ⟨1875113, by rfl⟩ : syracuseStep 2500151 = 3750227) B3750227
theorem B2500199 : Blo 1666533 2500199 := bstep (se 1 (by rfl) ⟨1875149, by rfl⟩ : syracuseStep 2500199 = 3750299) B3750299
theorem B51316349 : Blo 1666533 51316349 := bstep (se 3 (by rfl) ⟨9621815, by rfl⟩ : syracuseStep 51316349 = 19243631) B19243631
theorem B2500715 : Blo 1666533 2500715 := bstep (se 1 (by rfl) ⟨1875536, by rfl⟩ : syracuseStep 2500715 = 3751073) B3751073
theorem B2500847 : Blo 1666533 2500847 := bstep (se 1 (by rfl) ⟨1875635, by rfl⟩ : syracuseStep 2500847 = 3751271) B3751271
theorem B2501033 : Blo 1666533 2501033 := bstep (se 2 (by rfl) ⟨937887, by rfl⟩ : syracuseStep 2501033 = 1875775) B1875775
theorem B2812583 : Blo 1666533 2812583 := bstep (se 1 (by rfl) ⟨2109437, by rfl⟩ : syracuseStep 2812583 = 4218875) B4218875
theorem B2501567 : Blo 1666533 2501567 := bstep (se 1 (by rfl) ⟨1876175, by rfl⟩ : syracuseStep 2501567 = 3752351) B3752351
theorem B7121951 : Blo 1666533 7121951 := bstep (se 1 (by rfl) ⟨5341463, by rfl⟩ : syracuseStep 7121951 = 10682927) B10682927
theorem B2813035 : Blo 1666533 2813035 := bstep (se 1 (by rfl) ⟨2109776, by rfl⟩ : syracuseStep 2813035 = 4219553) B4219553
theorem B64982195 : Blo 1666533 64982195 := bstep (se 1 (by rfl) ⟨48736646, by rfl⟩ : syracuseStep 64982195 = 97473293) B97473293
theorem B2501867 : Blo 1666533 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B6327827 : Blo 1666533 6327827 := bstep (se 1 (by rfl) ⟨4745870, by rfl⟩ : syracuseStep 6327827 = 9491741) B9491741
theorem B1666671 : Blo 1666533 1666671 := bstep (se 1 (by rfl) ⟨1250003, by rfl⟩ : syracuseStep 1666671 = 2500007) B2500007
theorem B11407031 : Blo 1666533 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B1667007 : Blo 1666533 1667007 := bstep (se 1 (by rfl) ⟨1250255, by rfl⟩ : syracuseStep 1667007 = 2500511) B2500511
theorem B374976701 : Blo 1666533 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B1667263 : Blo 1666533 1667263 := bstep (se 1 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 1667263 = 2500895) B2500895
theorem B2814331 : Blo 1666533 2814331 := bstep (se 1 (by rfl) ⟨2110748, by rfl⟩ : syracuseStep 2814331 = 4221497) B4221497
theorem B1667559 : Blo 1666533 1667559 := bstep (se 1 (by rfl) ⟨1250669, by rfl⟩ : syracuseStep 1667559 = 2501339) B2501339
theorem B3379691 : Blo 1666533 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B10277533 : Blo 1666533 10277533 := bstep (se 3 (by rfl) ⟨1927037, by rfl⟩ : syracuseStep 10277533 = 3854075) B3854075
theorem B1667743 : Blo 1666533 1667743 := bstep (se 1 (by rfl) ⟨1250807, by rfl⟩ : syracuseStep 1667743 = 2501615) B2501615
theorem B3749759 : Blo 1666533 3749759 := bstep (se 1 (by rfl) ⟨2812319, by rfl⟩ : syracuseStep 3749759 = 5624639) B5624639
theorem B12662729 : Blo 1666533 12662729 := bstep (se 2 (by rfl) ⟨4748523, by rfl⟩ : syracuseStep 12662729 = 9497047) B9497047
theorem B26736623 : Blo 1666533 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B6010919 : Blo 1666533 6010919 := bstep (se 1 (by rfl) ⟨4508189, by rfl⟩ : syracuseStep 6010919 = 9016379) B9016379
theorem B8444087 : Blo 1666533 8444087 := bstep (se 1 (by rfl) ⟨6333065, by rfl⟩ : syracuseStep 8444087 = 12666131) B12666131
theorem B49404329 : Blo 1666533 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B21658043 : Blo 1666533 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B96131771 : Blo 1666533 96131771 := bstep (se 1 (by rfl) ⟨72098828, by rfl⟩ : syracuseStep 96131771 = 144197657) B144197657
theorem B51338033 : Blo 1666533 51338033 := bstep (se 2 (by rfl) ⟨19251762, by rfl⟩ : syracuseStep 51338033 = 38503525) B38503525
theorem B624245615 : Blo 1666533 624245615 := bstep (se 1 (by rfl) ⟨468184211, by rfl⟩ : syracuseStep 624245615 = 936368423) B936368423
theorem B6331547 : Blo 1666533 6331547 := bstep (se 1 (by rfl) ⟨4748660, by rfl⟩ : syracuseStep 6331547 = 9497321) B9497321
theorem B91241777 : Blo 1666533 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B2669879 : Blo 1666533 2669879 := bstep (se 1 (by rfl) ⟨2002409, by rfl⟩ : syracuseStep 2669879 = 4004819) B4004819
theorem B3751289 : Blo 1666533 3751289 := bstep (se 2 (by rfl) ⟨1406733, by rfl⟩ : syracuseStep 3751289 = 2813467) B2813467
theorem B3752135 : Blo 1666533 3752135 := bstep (se 1 (by rfl) ⟨2814101, by rfl⟩ : syracuseStep 3752135 = 5628203) B5628203
theorem B3752441 : Blo 1666533 3752441 := bstep (se 2 (by rfl) ⟨1407165, by rfl⟩ : syracuseStep 3752441 = 2814331) B2814331
theorem B3752495 : Blo 1666533 3752495 := bstep (se 1 (by rfl) ⟨2814371, by rfl⟩ : syracuseStep 3752495 = 5628743) B5628743
theorem B3752603 : Blo 1666533 3752603 := bstep (se 1 (by rfl) ⟨2814452, by rfl⟩ : syracuseStep 3752603 = 5628905) B5628905
theorem B7119677 : Blo 1666533 7119677 := bstep (se 3 (by rfl) ⟨1334939, by rfl⟩ : syracuseStep 7119677 = 2669879) B2669879
theorem B2499839 : Blo 1666533 2499839 := bstep (se 1 (by rfl) ⟨1874879, by rfl⟩ : syracuseStep 2499839 = 3749759) B3749759
theorem B9012509 : Blo 1666533 9012509 := bstep (se 3 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 9012509 = 3379691) B3379691
theorem B4007279 : Blo 1666533 4007279 := bstep (se 1 (by rfl) ⟨3005459, by rfl⟩ : syracuseStep 4007279 = 6010919) B6010919
theorem B5629391 : Blo 1666533 5629391 := bstep (se 1 (by rfl) ⟨4222043, by rfl⟩ : syracuseStep 5629391 = 8444087) B8444087
theorem B64087847 : Blo 1666533 64087847 := bstep (se 1 (by rfl) ⟨48065885, by rfl⟩ : syracuseStep 64087847 = 96131771) B96131771
theorem B416163743 : Blo 1666533 416163743 := bstep (se 1 (by rfl) ⟨312122807, by rfl⟩ : syracuseStep 416163743 = 624245615) B624245615
theorem B4221031 : Blo 1666533 4221031 := bstep (se 1 (by rfl) ⟨3165773, by rfl⟩ : syracuseStep 4221031 = 6331547) B6331547
theorem B43321463 : Blo 1666533 43321463 := bstep (se 1 (by rfl) ⟨32491097, by rfl⟩ : syracuseStep 43321463 = 64982195) B64982195
theorem B60827851 : Blo 1666533 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B2500859 : Blo 1666533 2500859 := bstep (se 1 (by rfl) ⟨1875644, by rfl⟩ : syracuseStep 2500859 = 3751289) B3751289
theorem B7604687 : Blo 1666533 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B285190645 : Blo 1666533 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B4942655 : Blo 1666533 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B2501543 : Blo 1666533 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B4221983 : Blo 1666533 4221983 := bstep (se 1 (by rfl) ⟨3166487, by rfl⟩ : syracuseStep 4221983 = 6332975) B6332975
theorem B6007891 : Blo 1666533 6007891 := bstep (se 1 (by rfl) ⟨4505918, by rfl⟩ : syracuseStep 6007891 = 9011837) B9011837
theorem B1666767 : Blo 1666533 1666767 := bstep (se 1 (by rfl) ⟨1250075, by rfl⟩ : syracuseStep 1666767 = 2500151) B2500151
theorem B1666799 : Blo 1666533 1666799 := bstep (se 1 (by rfl) ⟨1250099, by rfl⟩ : syracuseStep 1666799 = 2500199) B2500199
theorem B8441819 : Blo 1666533 8441819 := bstep (se 1 (by rfl) ⟨6331364, by rfl⟩ : syracuseStep 8441819 = 12662729) B12662729
theorem B1667143 : Blo 1666533 1667143 := bstep (se 1 (by rfl) ⟨1250357, by rfl⟩ : syracuseStep 1667143 = 2500715) B2500715
theorem B1667231 : Blo 1666533 1667231 := bstep (se 1 (by rfl) ⟨1250423, by rfl⟩ : syracuseStep 1667231 = 2500847) B2500847
theorem B1667355 : Blo 1666533 1667355 := bstep (se 1 (by rfl) ⟨1250516, by rfl⟩ : syracuseStep 1667355 = 2501033) B2501033
theorem B32936219 : Blo 1666533 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B14438695 : Blo 1666533 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B136843597 : Blo 1666533 136843597 := bstep (se 3 (by rfl) ⟨25658174, by rfl⟩ : syracuseStep 136843597 = 51316349) B51316349
theorem B1667711 : Blo 1666533 1667711 := bstep (se 1 (by rfl) ⟨1250783, by rfl⟩ : syracuseStep 1667711 = 2501567) B2501567
theorem B4747967 : Blo 1666533 4747967 := bstep (se 1 (by rfl) ⟨3560975, by rfl⟩ : syracuseStep 4747967 = 7121951) B7121951
theorem B1667911 : Blo 1666533 1667911 := bstep (se 1 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 1667911 = 2501867) B2501867
theorem B249984467 : Blo 1666533 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B8443601 : Blo 1666533 8443601 := bstep (se 2 (by rfl) ⟨3166350, by rfl⟩ : syracuseStep 8443601 = 6332701) B6332701
theorem B3381095 : Blo 1666533 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B31266755 : Blo 1666533 31266755 := bstep (se 1 (by rfl) ⟨23450066, by rfl⟩ : syracuseStep 31266755 = 46900133) B46900133
theorem B14243795 : Blo 1666533 14243795 := bstep (se 1 (by rfl) ⟨10682846, by rfl⟩ : syracuseStep 14243795 = 21365693) B21365693
theorem B3004523 : Blo 1666533 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B13703377 : Blo 1666533 13703377 := bstep (se 2 (by rfl) ⟨5138766, by rfl⟩ : syracuseStep 13703377 = 10277533) B10277533
theorem B3750713 : Blo 1666533 3750713 := bstep (se 2 (by rfl) ⟨1406517, by rfl⟩ : syracuseStep 3750713 = 2813035) B2813035
theorem B1875055 : Blo 1666533 1875055 := bstep (se 1 (by rfl) ⟨1406291, by rfl⟩ : syracuseStep 1875055 = 2812583) B2812583
theorem B34225355 : Blo 1666533 34225355 := bstep (se 1 (by rfl) ⟨25669016, by rfl⟩ : syracuseStep 34225355 = 51338033) B51338033
theorem B4218551 : Blo 1666533 4218551 := bstep (se 1 (by rfl) ⟨3163913, by rfl⟩ : syracuseStep 4218551 = 6327827) B6327827
theorem B5628041 : Blo 1666533 5628041 := bstep (se 2 (by rfl) ⟨2110515, by rfl⟩ : syracuseStep 5628041 = 4221031) B4221031
theorem B19251593 : Blo 1666533 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B3752927 : Blo 1666533 3752927 := bstep (se 1 (by rfl) ⟨2814695, by rfl⟩ : syracuseStep 3752927 = 5629391) B5629391
theorem B5629067 : Blo 1666533 5629067 := bstep (se 1 (by rfl) ⟨4221800, by rfl⟩ : syracuseStep 5629067 = 8443601) B8443601
theorem B2254063 : Blo 1666533 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B9495863 : Blo 1666533 9495863 := bstep (se 1 (by rfl) ⟨7121897, by rfl⟩ : syracuseStep 9495863 = 14243795) B14243795
theorem B2500073 : Blo 1666533 2500073 := bstep (se 2 (by rfl) ⟨937527, by rfl⟩ : syracuseStep 2500073 = 1875055) B1875055
theorem B2500475 : Blo 1666533 2500475 := bstep (se 1 (by rfl) ⟨1875356, by rfl⟩ : syracuseStep 2500475 = 3750713) B3750713
theorem B3295103 : Blo 1666533 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B22816903 : Blo 1666533 22816903 := bstep (se 1 (by rfl) ⟨17112677, by rfl⟩ : syracuseStep 22816903 = 34225355) B34225355
theorem B2812367 : Blo 1666533 2812367 := bstep (se 1 (by rfl) ⟨2109275, by rfl⟩ : syracuseStep 2812367 = 4218551) B4218551
theorem B2501423 : Blo 1666533 2501423 := bstep (se 1 (by rfl) ⟨1876067, by rfl⟩ : syracuseStep 2501423 = 3752135) B3752135
theorem B21957479 : Blo 1666533 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B81103801 : Blo 1666533 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B18271169 : Blo 1666533 18271169 := bstep (se 2 (by rfl) ⟨6851688, by rfl⟩ : syracuseStep 18271169 = 13703377) B13703377
theorem B2501627 : Blo 1666533 2501627 := bstep (se 1 (by rfl) ⟨1876220, by rfl⟩ : syracuseStep 2501627 = 3752441) B3752441
theorem B2501663 : Blo 1666533 2501663 := bstep (se 1 (by rfl) ⟨1876247, by rfl⟩ : syracuseStep 2501663 = 3752495) B3752495
theorem B2501735 : Blo 1666533 2501735 := bstep (se 1 (by rfl) ⟨1876301, by rfl⟩ : syracuseStep 2501735 = 3752603) B3752603
theorem B3165311 : Blo 1666533 3165311 := bstep (se 1 (by rfl) ⟨2373983, by rfl⟩ : syracuseStep 3165311 = 4747967) B4747967
theorem B4746451 : Blo 1666533 4746451 := bstep (se 1 (by rfl) ⟨3559838, by rfl⟩ : syracuseStep 4746451 = 7119677) B7119677
theorem B1666559 : Blo 1666533 1666559 := bstep (se 1 (by rfl) ⟨1249919, by rfl⟩ : syracuseStep 1666559 = 2499839) B2499839
theorem B6008339 : Blo 1666533 6008339 := bstep (se 1 (by rfl) ⟨4506254, by rfl⟩ : syracuseStep 6008339 = 9012509) B9012509
theorem B10686077 : Blo 1666533 10686077 := bstep (se 3 (by rfl) ⟨2003639, by rfl⟩ : syracuseStep 10686077 = 4007279) B4007279
theorem B42725231 : Blo 1666533 42725231 := bstep (se 1 (by rfl) ⟨32043923, by rfl⟩ : syracuseStep 42725231 = 64087847) B64087847
theorem B277442495 : Blo 1666533 277442495 := bstep (se 1 (by rfl) ⟨208081871, by rfl⟩ : syracuseStep 277442495 = 416163743) B416163743
theorem B20844503 : Blo 1666533 20844503 := bstep (se 1 (by rfl) ⟨15633377, by rfl⟩ : syracuseStep 20844503 = 31266755) B31266755
theorem B2003015 : Blo 1666533 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B28880975 : Blo 1666533 28880975 := bstep (se 1 (by rfl) ⟨21660731, by rfl⟩ : syracuseStep 28880975 = 43321463) B43321463
theorem B1667239 : Blo 1666533 1667239 := bstep (se 1 (by rfl) ⟨1250429, by rfl⟩ : syracuseStep 1667239 = 2500859) B2500859
theorem B1667695 : Blo 1666533 1667695 := bstep (se 1 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 1667695 = 2501543) B2501543
theorem B2814655 : Blo 1666533 2814655 := bstep (se 1 (by rfl) ⟨2110991, by rfl⟩ : syracuseStep 2814655 = 4221983) B4221983
theorem B182458129 : Blo 1666533 182458129 := bstep (se 2 (by rfl) ⟨68421798, by rfl⟩ : syracuseStep 182458129 = 136843597) B136843597
theorem B380254193 : Blo 1666533 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B166656311 : Blo 1666533 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B8010521 : Blo 1666533 8010521 := bstep (se 2 (by rfl) ⟨3003945, by rfl⟩ : syracuseStep 8010521 = 6007891) B6007891
theorem B5069791 : Blo 1666533 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B5627879 : Blo 1666533 5627879 := bstep (se 1 (by rfl) ⟨4220909, by rfl⟩ : syracuseStep 5627879 = 8441819) B8441819
theorem B3752027 : Blo 1666533 3752027 := bstep (se 1 (by rfl) ⟨2814020, by rfl⟩ : syracuseStep 3752027 = 5628041) B5628041
theorem B5341373 : Blo 1666533 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B3752711 : Blo 1666533 3752711 := bstep (se 1 (by rfl) ⟨2814533, by rfl⟩ : syracuseStep 3752711 = 5629067) B5629067
theorem B3752873 : Blo 1666533 3752873 := bstep (se 2 (by rfl) ⟨1407327, by rfl⟩ : syracuseStep 3752873 = 2814655) B2814655
theorem B6759721 : Blo 1666533 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B253502795 : Blo 1666533 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B184961663 : Blo 1666533 184961663 := bstep (se 1 (by rfl) ⟨138721247, by rfl⟩ : syracuseStep 184961663 = 277442495) B277442495
theorem B13896335 : Blo 1666533 13896335 := bstep (se 1 (by rfl) ⟨10422251, by rfl⟩ : syracuseStep 13896335 = 20844503) B20844503
theorem B19253983 : Blo 1666533 19253983 := bstep (se 1 (by rfl) ⟨14440487, by rfl⟩ : syracuseStep 19253983 = 28880975) B28880975
theorem B2501951 : Blo 1666533 2501951 := bstep (se 1 (by rfl) ⟨1876463, by rfl⟩ : syracuseStep 2501951 = 3752927) B3752927
theorem B1666715 : Blo 1666533 1666715 := bstep (se 1 (by rfl) ⟨1250036, by rfl⟩ : syracuseStep 1666715 = 2500073) B2500073
theorem B108138401 : Blo 1666533 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B1666983 : Blo 1666533 1666983 := bstep (se 1 (by rfl) ⟨1250237, by rfl⟩ : syracuseStep 1666983 = 2500475) B2500475
theorem B35147765 : Blo 1666533 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B111104207 : Blo 1666533 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B6328601 : Blo 1666533 6328601 := bstep (se 2 (by rfl) ⟨2373225, by rfl⟩ : syracuseStep 6328601 = 4746451) B4746451
theorem B1667615 : Blo 1666533 1667615 := bstep (se 1 (by rfl) ⟨1250711, by rfl⟩ : syracuseStep 1667615 = 2501423) B2501423
theorem B1667751 : Blo 1666533 1667751 := bstep (se 1 (by rfl) ⟨1250813, by rfl⟩ : syracuseStep 1667751 = 2501627) B2501627
theorem B1667775 : Blo 1666533 1667775 := bstep (se 1 (by rfl) ⟨1250831, by rfl⟩ : syracuseStep 1667775 = 2501663) B2501663
theorem B1667823 : Blo 1666533 1667823 := bstep (se 1 (by rfl) ⟨1250867, by rfl⟩ : syracuseStep 1667823 = 2501735) B2501735
theorem B2110207 : Blo 1666533 2110207 := bstep (se 1 (by rfl) ⟨1582655, by rfl⟩ : syracuseStep 2110207 = 3165311) B3165311
theorem B7124051 : Blo 1666533 7124051 := bstep (se 1 (by rfl) ⟨5343038, by rfl⟩ : syracuseStep 7124051 = 10686077) B10686077
theorem B30422537 : Blo 1666533 30422537 := bstep (se 2 (by rfl) ⟨11408451, by rfl⟩ : syracuseStep 30422537 = 22816903) B22816903
theorem B12834395 : Blo 1666533 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B6330575 : Blo 1666533 6330575 := bstep (se 1 (by rfl) ⟨4747931, by rfl⟩ : syracuseStep 6330575 = 9495863) B9495863
theorem B1874911 : Blo 1666533 1874911 := bstep (se 1 (by rfl) ⟨1406183, by rfl⟩ : syracuseStep 1874911 = 2812367) B2812367
theorem B3005417 : Blo 1666533 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B5340347 : Blo 1666533 5340347 := bstep (se 1 (by rfl) ⟨4005260, by rfl⟩ : syracuseStep 5340347 = 8010521) B8010521
theorem B14638319 : Blo 1666533 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B12180779 : Blo 1666533 12180779 := bstep (se 1 (by rfl) ⟨9135584, by rfl⟩ : syracuseStep 12180779 = 18271169) B18271169
theorem B4005559 : Blo 1666533 4005559 := bstep (se 1 (by rfl) ⟨3004169, by rfl⟩ : syracuseStep 4005559 = 6008339) B6008339
theorem B243277505 : Blo 1666533 243277505 := bstep (se 2 (by rfl) ⟨91229064, by rfl⟩ : syracuseStep 243277505 = 182458129) B182458129
theorem B28483487 : Blo 1666533 28483487 := bstep (se 1 (by rfl) ⟨21362615, by rfl⟩ : syracuseStep 28483487 = 42725231) B42725231
theorem B3751919 : Blo 1666533 3751919 := bstep (se 1 (by rfl) ⟨2813939, by rfl⟩ : syracuseStep 3751919 = 5627879) B5627879
theorem B4219067 : Blo 1666533 4219067 := bstep (se 1 (by rfl) ⟨3164300, by rfl⟩ : syracuseStep 4219067 = 6328601) B6328601
theorem B2499881 : Blo 1666533 2499881 := bstep (se 2 (by rfl) ⟨937455, by rfl⟩ : syracuseStep 2499881 = 1874911) B1874911
theorem B4220383 : Blo 1666533 4220383 := bstep (se 1 (by rfl) ⟨3165287, by rfl⟩ : syracuseStep 4220383 = 6330575) B6330575
theorem B9012961 : Blo 1666533 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B123307775 : Blo 1666533 123307775 := bstep (se 1 (by rfl) ⟨92480831, by rfl⟩ : syracuseStep 123307775 = 184961663) B184961663
theorem B9758879 : Blo 1666533 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B8120519 : Blo 1666533 8120519 := bstep (se 1 (by rfl) ⟨6090389, by rfl⟩ : syracuseStep 8120519 = 12180779) B12180779
theorem B72092267 : Blo 1666533 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B2501279 : Blo 1666533 2501279 := bstep (se 1 (by rfl) ⟨1875959, by rfl⟩ : syracuseStep 2501279 = 3751919) B3751919
theorem B23431843 : Blo 1666533 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B2501351 : Blo 1666533 2501351 := bstep (se 1 (by rfl) ⟨1876013, by rfl⟩ : syracuseStep 2501351 = 3752027) B3752027
theorem B2501807 : Blo 1666533 2501807 := bstep (se 1 (by rfl) ⟨1876355, by rfl⟩ : syracuseStep 2501807 = 3752711) B3752711
theorem B2501915 : Blo 1666533 2501915 := bstep (se 1 (by rfl) ⟨1876436, by rfl⟩ : syracuseStep 2501915 = 3752873) B3752873
theorem B676007453 : Blo 1666533 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B2813609 : Blo 1666533 2813609 := bstep (se 2 (by rfl) ⟨1055103, by rfl⟩ : syracuseStep 2813609 = 2110207) B2110207
theorem B8556263 : Blo 1666533 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B2003611 : Blo 1666533 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B3560231 : Blo 1666533 3560231 := bstep (se 1 (by rfl) ⟨2670173, by rfl⟩ : syracuseStep 3560231 = 5340347) B5340347
theorem B1667967 : Blo 1666533 1667967 := bstep (se 1 (by rfl) ⟨1250975, by rfl⟩ : syracuseStep 1667967 = 2501951) B2501951
theorem B3560915 : Blo 1666533 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B74069471 : Blo 1666533 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B4749367 : Blo 1666533 4749367 := bstep (se 1 (by rfl) ⟨3562025, by rfl⟩ : syracuseStep 4749367 = 7124051) B7124051
theorem B25671977 : Blo 1666533 25671977 := bstep (se 2 (by rfl) ⟨9626991, by rfl⟩ : syracuseStep 25671977 = 19253983) B19253983
theorem B20281691 : Blo 1666533 20281691 := bstep (se 1 (by rfl) ⟨15211268, by rfl⟩ : syracuseStep 20281691 = 30422537) B30422537
theorem B9264223 : Blo 1666533 9264223 := bstep (se 1 (by rfl) ⟨6948167, by rfl⟩ : syracuseStep 9264223 = 13896335) B13896335
theorem B5340745 : Blo 1666533 5340745 := bstep (se 2 (by rfl) ⟨2002779, by rfl⟩ : syracuseStep 5340745 = 4005559) B4005559
theorem B162185003 : Blo 1666533 162185003 := bstep (se 1 (by rfl) ⟨121638752, by rfl⟩ : syracuseStep 162185003 = 243277505) B243277505
theorem B18988991 : Blo 1666533 18988991 := bstep (se 1 (by rfl) ⟨14241743, by rfl⟩ : syracuseStep 18988991 = 28483487) B28483487
theorem B6332489 : Blo 1666533 6332489 := bstep (se 2 (by rfl) ⟨2374683, by rfl⟩ : syracuseStep 6332489 = 4749367) B4749367
theorem B2671481 : Blo 1666533 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B54084509 : Blo 1666533 54084509 := bstep (se 3 (by rfl) ⟨10140845, by rfl⟩ : syracuseStep 54084509 = 20281691) B20281691
theorem B6505919 : Blo 1666533 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B17114651 : Blo 1666533 17114651 := bstep (se 1 (by rfl) ⟨12835988, by rfl⟩ : syracuseStep 17114651 = 25671977) B25671977
theorem B7120993 : Blo 1666533 7120993 := bstep (se 2 (by rfl) ⟨2670372, by rfl⟩ : syracuseStep 7120993 = 5340745) B5340745
theorem B5704175 : Blo 1666533 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B12659327 : Blo 1666533 12659327 := bstep (se 1 (by rfl) ⟨9494495, by rfl⟩ : syracuseStep 12659327 = 18988991) B18988991
theorem B2812711 : Blo 1666533 2812711 := bstep (se 1 (by rfl) ⟨2109533, by rfl⟩ : syracuseStep 2812711 = 4219067) B4219067
theorem B1666587 : Blo 1666533 1666587 := bstep (se 1 (by rfl) ⟨1249940, by rfl⟩ : syracuseStep 1666587 = 2499881) B2499881
theorem B1667519 : Blo 1666533 1667519 := bstep (se 1 (by rfl) ⟨1250639, by rfl⟩ : syracuseStep 1667519 = 2501279) B2501279
theorem B1667567 : Blo 1666533 1667567 := bstep (se 1 (by rfl) ⟨1250675, by rfl⟩ : syracuseStep 1667567 = 2501351) B2501351
theorem B1667871 : Blo 1666533 1667871 := bstep (se 1 (by rfl) ⟨1250903, by rfl⟩ : syracuseStep 1667871 = 2501807) B2501807
theorem B1667943 : Blo 1666533 1667943 := bstep (se 1 (by rfl) ⟨1250957, by rfl⟩ : syracuseStep 1667943 = 2501915) B2501915
theorem B450671635 : Blo 1666533 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B108123335 : Blo 1666533 108123335 := bstep (se 1 (by rfl) ⟨81092501, by rfl⟩ : syracuseStep 108123335 = 162185003) B162185003
theorem B31242457 : Blo 1666533 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B2373943 : Blo 1666533 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B49379647 : Blo 1666533 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B82205183 : Blo 1666533 82205183 := bstep (se 1 (by rfl) ⟨61653887, by rfl⟩ : syracuseStep 82205183 = 123307775) B123307775
theorem B12352297 : Blo 1666533 12352297 := bstep (se 2 (by rfl) ⟨4632111, by rfl⟩ : syracuseStep 12352297 = 9264223) B9264223
theorem B5413679 : Blo 1666533 5413679 := bstep (se 1 (by rfl) ⟨4060259, by rfl⟩ : syracuseStep 5413679 = 8120519) B8120519
theorem B48061511 : Blo 1666533 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B5627177 : Blo 1666533 5627177 := bstep (se 2 (by rfl) ⟨2110191, by rfl⟩ : syracuseStep 5627177 = 4220383) B4220383
theorem B9493949 : Blo 1666533 9493949 := bstep (se 3 (by rfl) ⟨1780115, by rfl⟩ : syracuseStep 9493949 = 3560231) B3560231
theorem B12017281 : Blo 1666533 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B1875739 : Blo 1666533 1875739 := bstep (se 1 (by rfl) ⟨1406804, by rfl⟩ : syracuseStep 1875739 = 2813609) B2813609
theorem B9494657 : Blo 1666533 9494657 := bstep (se 2 (by rfl) ⟨3560496, by rfl⟩ : syracuseStep 9494657 = 7120993) B7120993
theorem B41656609 : Blo 1666533 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B72082223 : Blo 1666533 72082223 := bstep (se 1 (by rfl) ⟨54061667, by rfl⟩ : syracuseStep 72082223 = 108123335) B108123335
theorem B3802783 : Blo 1666533 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B8439551 : Blo 1666533 8439551 := bstep (se 1 (by rfl) ⟨6329663, by rfl⟩ : syracuseStep 8439551 = 12659327) B12659327
theorem B32041007 : Blo 1666533 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B2500985 : Blo 1666533 2500985 := bstep (se 2 (by rfl) ⟨937869, by rfl⟩ : syracuseStep 2500985 = 1875739) B1875739
theorem B4221659 : Blo 1666533 4221659 := bstep (se 1 (by rfl) ⟨3166244, by rfl⟩ : syracuseStep 4221659 = 6332489) B6332489
theorem B3165257 : Blo 1666533 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B36056339 : Blo 1666533 36056339 := bstep (se 1 (by rfl) ⟨27042254, by rfl⟩ : syracuseStep 36056339 = 54084509) B54084509
theorem B4337279 : Blo 1666533 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B16469729 : Blo 1666533 16469729 := bstep (se 2 (by rfl) ⟨6176148, by rfl⟩ : syracuseStep 16469729 = 12352297) B12352297
theorem B600895513 : Blo 1666533 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B3609119 : Blo 1666533 3609119 := bstep (se 1 (by rfl) ⟨2706839, by rfl⟩ : syracuseStep 3609119 = 5413679) B5413679
theorem B6329299 : Blo 1666533 6329299 := bstep (se 1 (by rfl) ⟨4746974, by rfl⟩ : syracuseStep 6329299 = 9493949) B9493949
theorem B7123949 : Blo 1666533 7123949 := bstep (se 3 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 7123949 = 2671481) B2671481
theorem B11409767 : Blo 1666533 11409767 := bstep (se 1 (by rfl) ⟨8557325, by rfl⟩ : syracuseStep 11409767 = 17114651) B17114651
theorem B3750281 : Blo 1666533 3750281 := bstep (se 2 (by rfl) ⟨1406355, by rfl⟩ : syracuseStep 3750281 = 2812711) B2812711
theorem B1053432469 : Blo 1666533 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B54803455 : Blo 1666533 54803455 := bstep (se 1 (by rfl) ⟨41102591, by rfl⟩ : syracuseStep 54803455 = 82205183) B82205183
theorem B16023041 : Blo 1666533 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B3751451 : Blo 1666533 3751451 := bstep (se 1 (by rfl) ⟨2813588, by rfl⟩ : syracuseStep 3751451 = 5627177) B5627177
theorem B801194017 : Blo 1666533 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B55542145 : Blo 1666533 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B48054815 : Blo 1666533 48054815 := bstep (se 1 (by rfl) ⟨36041111, by rfl⟩ : syracuseStep 48054815 = 72082223) B72082223
theorem B1404576625 : Blo 1666533 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B8439065 : Blo 1666533 8439065 := bstep (se 2 (by rfl) ⟨3164649, by rfl⟩ : syracuseStep 8439065 = 6329299) B6329299
theorem B2500187 : Blo 1666533 2500187 := bstep (se 1 (by rfl) ⟨1875140, by rfl⟩ : syracuseStep 2500187 = 3750281) B3750281
theorem B24037559 : Blo 1666533 24037559 := bstep (se 1 (by rfl) ⟨18028169, by rfl⟩ : syracuseStep 24037559 = 36056339) B36056339
theorem B2500967 : Blo 1666533 2500967 := bstep (se 1 (by rfl) ⟨1875725, by rfl⟩ : syracuseStep 2500967 = 3751451) B3751451
theorem B10979819 : Blo 1666533 10979819 := bstep (se 1 (by rfl) ⟨8234864, by rfl⟩ : syracuseStep 10979819 = 16469729) B16469729
theorem B292285093 : Blo 1666533 292285093 := bstep (se 4 (by rfl) ⟨27401727, by rfl⟩ : syracuseStep 292285093 = 54803455) B54803455
theorem B8440685 : Blo 1666533 8440685 := bstep (se 3 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 8440685 = 3165257) B3165257
theorem B21360671 : Blo 1666533 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B7606511 : Blo 1666533 7606511 := bstep (se 1 (by rfl) ⟨5704883, by rfl⟩ : syracuseStep 7606511 = 11409767) B11409767
theorem B1667323 : Blo 1666533 1667323 := bstep (se 1 (by rfl) ⟨1250492, by rfl⟩ : syracuseStep 1667323 = 2500985) B2500985
theorem B2814439 : Blo 1666533 2814439 := bstep (se 1 (by rfl) ⟨2110829, by rfl⟩ : syracuseStep 2814439 = 4221659) B4221659
theorem B6329771 : Blo 1666533 6329771 := bstep (se 1 (by rfl) ⟨4747328, by rfl⟩ : syracuseStep 6329771 = 9494657) B9494657
theorem B2406079 : Blo 1666533 2406079 := bstep (se 1 (by rfl) ⟨1804559, by rfl⟩ : syracuseStep 2406079 = 3609119) B3609119
theorem B4749299 : Blo 1666533 4749299 := bstep (se 1 (by rfl) ⟨3561974, by rfl⟩ : syracuseStep 4749299 = 7123949) B7123949
theorem B5626367 : Blo 1666533 5626367 := bstep (se 1 (by rfl) ⟨4219775, by rfl⟩ : syracuseStep 5626367 = 8439551) B8439551
theorem B5070377 : Blo 1666533 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B10682027 : Blo 1666533 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B2891519 : Blo 1666533 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B5071007 : Blo 1666533 5071007 := bstep (se 1 (by rfl) ⟨3803255, by rfl⟩ : syracuseStep 5071007 = 7606511) B7606511
theorem B74056193 : Blo 1666533 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B3752585 : Blo 1666533 3752585 := bstep (se 2 (by rfl) ⟨1407219, by rfl⟩ : syracuseStep 3752585 = 2814439) B2814439
theorem B4219847 : Blo 1666533 4219847 := bstep (se 1 (by rfl) ⟨3164885, by rfl⟩ : syracuseStep 4219847 = 6329771) B6329771
theorem B16025039 : Blo 1666533 16025039 := bstep (se 1 (by rfl) ⟨12018779, by rfl⟩ : syracuseStep 16025039 = 24037559) B24037559
theorem B7121351 : Blo 1666533 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B14240447 : Blo 1666533 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B389713457 : Blo 1666533 389713457 := bstep (se 2 (by rfl) ⟨146142546, by rfl⟩ : syracuseStep 389713457 = 292285093) B292285093
theorem B1666791 : Blo 1666533 1666791 := bstep (se 1 (by rfl) ⟨1250093, by rfl⟩ : syracuseStep 1666791 = 2500187) B2500187
theorem B1872768833 : Blo 1666533 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B3166199 : Blo 1666533 3166199 := bstep (se 1 (by rfl) ⟨2374649, by rfl⟩ : syracuseStep 3166199 = 4749299) B4749299
theorem B13521005 : Blo 1666533 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B1667311 : Blo 1666533 1667311 := bstep (se 1 (by rfl) ⟨1250483, by rfl⟩ : syracuseStep 1667311 = 2500967) B2500967
theorem B7319879 : Blo 1666533 7319879 := bstep (se 1 (by rfl) ⟨5489909, by rfl⟩ : syracuseStep 7319879 = 10979819) B10979819
theorem B3208105 : Blo 1666533 3208105 := bstep (se 2 (by rfl) ⟨1203039, by rfl⟩ : syracuseStep 3208105 = 2406079) B2406079
theorem B1068258689 : Blo 1666533 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B32036543 : Blo 1666533 32036543 := bstep (se 1 (by rfl) ⟨24027407, by rfl⟩ : syracuseStep 32036543 = 48054815) B48054815
theorem B5626043 : Blo 1666533 5626043 := bstep (se 1 (by rfl) ⟨4219532, by rfl⟩ : syracuseStep 5626043 = 8439065) B8439065
theorem B3750911 : Blo 1666533 3750911 := bstep (se 1 (by rfl) ⟨2813183, by rfl⟩ : syracuseStep 3750911 = 5626367) B5626367
theorem B5627123 : Blo 1666533 5627123 := bstep (se 1 (by rfl) ⟨4220342, by rfl⟩ : syracuseStep 5627123 = 8440685) B8440685
theorem B30842869 : Blo 1666533 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B712172459 : Blo 1666533 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B10683359 : Blo 1666533 10683359 := bstep (se 1 (by rfl) ⟨8012519, by rfl⟩ : syracuseStep 10683359 = 16025039) B16025039
theorem B21357695 : Blo 1666533 21357695 := bstep (se 1 (by rfl) ⟨16018271, by rfl⟩ : syracuseStep 21357695 = 32036543) B32036543
theorem B2500607 : Blo 1666533 2500607 := bstep (se 1 (by rfl) ⟨1875455, by rfl⟩ : syracuseStep 2500607 = 3750911) B3750911
theorem B1248512555 : Blo 1666533 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B9014003 : Blo 1666533 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B2501723 : Blo 1666533 2501723 := bstep (se 1 (by rfl) ⟨1876292, by rfl⟩ : syracuseStep 2501723 = 3752585) B3752585
theorem B2813231 : Blo 1666533 2813231 := bstep (se 1 (by rfl) ⟨2109923, by rfl⟩ : syracuseStep 2813231 = 4219847) B4219847
theorem B4747567 : Blo 1666533 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B17109893 : Blo 1666533 17109893 := bstep (se 4 (by rfl) ⟨1604052, by rfl⟩ : syracuseStep 17109893 = 3208105) B3208105
theorem B2110799 : Blo 1666533 2110799 := bstep (se 1 (by rfl) ⟨1583099, by rfl⟩ : syracuseStep 2110799 = 3166199) B3166199
theorem B3380671 : Blo 1666533 3380671 := bstep (se 1 (by rfl) ⟨2535503, by rfl⟩ : syracuseStep 3380671 = 5071007) B5071007
theorem B4879919 : Blo 1666533 4879919 := bstep (se 1 (by rfl) ⟨3659939, by rfl⟩ : syracuseStep 4879919 = 7319879) B7319879
theorem B49370795 : Blo 1666533 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B3750695 : Blo 1666533 3750695 := bstep (se 1 (by rfl) ⟨2813021, by rfl⟩ : syracuseStep 3750695 = 5626043) B5626043
theorem B9493631 : Blo 1666533 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B3751415 : Blo 1666533 3751415 := bstep (se 1 (by rfl) ⟨2813561, by rfl⟩ : syracuseStep 3751415 = 5627123) B5627123
theorem B259808971 : Blo 1666533 259808971 := bstep (se 1 (by rfl) ⟨194856728, by rfl⟩ : syracuseStep 259808971 = 389713457) B389713457
theorem B41123825 : Blo 1666533 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B14238463 : Blo 1666533 14238463 := bstep (se 1 (by rfl) ⟨10678847, by rfl⟩ : syracuseStep 14238463 = 21357695) B21357695
theorem B5628797 : Blo 1666533 5628797 := bstep (se 3 (by rfl) ⟨1055399, by rfl⟩ : syracuseStep 5628797 = 2110799) B2110799
theorem B3253279 : Blo 1666533 3253279 := bstep (se 1 (by rfl) ⟨2439959, by rfl⟩ : syracuseStep 3253279 = 4879919) B4879919
theorem B832341703 : Blo 1666533 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B2500463 : Blo 1666533 2500463 := bstep (se 1 (by rfl) ⟨1875347, by rfl⟩ : syracuseStep 2500463 = 3750695) B3750695
theorem B4507561 : Blo 1666533 4507561 := bstep (se 2 (by rfl) ⟨1690335, by rfl⟩ : syracuseStep 4507561 = 3380671) B3380671
theorem B2500943 : Blo 1666533 2500943 := bstep (se 1 (by rfl) ⟨1875707, by rfl⟩ : syracuseStep 2500943 = 3751415) B3751415
theorem B11406595 : Blo 1666533 11406595 := bstep (se 1 (by rfl) ⟨8554946, by rfl⟩ : syracuseStep 11406595 = 17109893) B17109893
theorem B7122239 : Blo 1666533 7122239 := bstep (se 1 (by rfl) ⟨5341679, by rfl⟩ : syracuseStep 7122239 = 10683359) B10683359
theorem B1667071 : Blo 1666533 1667071 := bstep (se 1 (by rfl) ⟨1250303, by rfl⟩ : syracuseStep 1667071 = 2500607) B2500607
theorem B6009335 : Blo 1666533 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B1667815 : Blo 1666533 1667815 := bstep (se 1 (by rfl) ⟨1250861, by rfl⟩ : syracuseStep 1667815 = 2501723) B2501723
theorem B6329087 : Blo 1666533 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B346411961 : Blo 1666533 346411961 := bstep (se 2 (by rfl) ⟨129904485, by rfl⟩ : syracuseStep 346411961 = 259808971) B259808971
theorem B27415883 : Blo 1666533 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B6330089 : Blo 1666533 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B32913863 : Blo 1666533 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B1875487 : Blo 1666533 1875487 := bstep (se 1 (by rfl) ⟨1406615, by rfl⟩ : syracuseStep 1875487 = 2813231) B2813231
theorem B1899126557 : Blo 1666533 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B4006223 : Blo 1666533 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B4219391 : Blo 1666533 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B3752531 : Blo 1666533 3752531 := bstep (se 1 (by rfl) ⟨2814398, by rfl⟩ : syracuseStep 3752531 = 5628797) B5628797
theorem B230941307 : Blo 1666533 230941307 := bstep (se 1 (by rfl) ⟨173205980, by rfl⟩ : syracuseStep 230941307 = 346411961) B346411961
theorem B18277255 : Blo 1666533 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B4220059 : Blo 1666533 4220059 := bstep (se 1 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 4220059 = 6330089) B6330089
theorem B2500649 : Blo 1666533 2500649 := bstep (se 2 (by rfl) ⟨937743, by rfl⟩ : syracuseStep 2500649 = 1875487) B1875487
theorem B1109788937 : Blo 1666533 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B1266084371 : Blo 1666533 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B18984617 : Blo 1666533 18984617 := bstep (se 2 (by rfl) ⟨7119231, by rfl⟩ : syracuseStep 18984617 = 14238463) B14238463
theorem B1666975 : Blo 1666533 1666975 := bstep (se 1 (by rfl) ⟨1250231, by rfl⟩ : syracuseStep 1666975 = 2500463) B2500463
theorem B4337705 : Blo 1666533 4337705 := bstep (se 2 (by rfl) ⟨1626639, by rfl⟩ : syracuseStep 4337705 = 3253279) B3253279
theorem B1667295 : Blo 1666533 1667295 := bstep (se 1 (by rfl) ⟨1250471, by rfl⟩ : syracuseStep 1667295 = 2500943) B2500943
theorem B21942575 : Blo 1666533 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B15208793 : Blo 1666533 15208793 := bstep (se 2 (by rfl) ⟨5703297, by rfl⟩ : syracuseStep 15208793 = 11406595) B11406595
theorem B4748159 : Blo 1666533 4748159 := bstep (se 1 (by rfl) ⟨3561119, by rfl⟩ : syracuseStep 4748159 = 7122239) B7122239
theorem B6010081 : Blo 1666533 6010081 := bstep (se 2 (by rfl) ⟨2253780, by rfl⟩ : syracuseStep 6010081 = 4507561) B4507561
theorem B2891803 : Blo 1666533 2891803 := bstep (se 1 (by rfl) ⟨2168852, by rfl⟩ : syracuseStep 2891803 = 4337705) B4337705
theorem B2670815 : Blo 1666533 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B153960871 : Blo 1666533 153960871 := bstep (se 1 (by rfl) ⟨115470653, by rfl⟩ : syracuseStep 153960871 = 230941307) B230941307
theorem B844056247 : Blo 1666533 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B2812927 : Blo 1666533 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B2501687 : Blo 1666533 2501687 := bstep (se 1 (by rfl) ⟨1876265, by rfl⟩ : syracuseStep 2501687 = 3752531) B3752531
theorem B1667099 : Blo 1666533 1667099 := bstep (se 1 (by rfl) ⟨1250324, by rfl⟩ : syracuseStep 1667099 = 2500649) B2500649
theorem B12661757 : Blo 1666533 12661757 := bstep (se 3 (by rfl) ⟨2374079, by rfl⟩ : syracuseStep 12661757 = 4748159) B4748159
theorem B14628383 : Blo 1666533 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B10139195 : Blo 1666533 10139195 := bstep (se 1 (by rfl) ⟨7604396, by rfl⟩ : syracuseStep 10139195 = 15208793) B15208793
theorem B32053765 : Blo 1666533 32053765 := bstep (se 4 (by rfl) ⟨3005040, by rfl⟩ : syracuseStep 32053765 = 6010081) B6010081
theorem B24369673 : Blo 1666533 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B739859291 : Blo 1666533 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B5626745 : Blo 1666533 5626745 := bstep (se 2 (by rfl) ⟨2110029, by rfl⟩ : syracuseStep 5626745 = 4220059) B4220059
theorem B12656411 : Blo 1666533 12656411 := bstep (se 1 (by rfl) ⟨9492308, by rfl⟩ : syracuseStep 12656411 = 18984617) B18984617
theorem B42738353 : Blo 1666533 42738353 := bstep (se 2 (by rfl) ⟨16026882, by rfl⟩ : syracuseStep 42738353 = 32053765) B32053765
theorem B6759463 : Blo 1666533 6759463 := bstep (se 1 (by rfl) ⟨5069597, by rfl⟩ : syracuseStep 6759463 = 10139195) B10139195
theorem B1780543 : Blo 1666533 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B8441171 : Blo 1666533 8441171 := bstep (se 1 (by rfl) ⟨6330878, by rfl⟩ : syracuseStep 8441171 = 12661757) B12661757
theorem B32492897 : Blo 1666533 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B9752255 : Blo 1666533 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B1667791 : Blo 1666533 1667791 := bstep (se 1 (by rfl) ⟨1250843, by rfl⟩ : syracuseStep 1667791 = 2501687) B2501687
theorem B3855737 : Blo 1666533 3855737 := bstep (se 2 (by rfl) ⟨1445901, by rfl⟩ : syracuseStep 3855737 = 2891803) B2891803
theorem B205281161 : Blo 1666533 205281161 := bstep (se 2 (by rfl) ⟨76980435, by rfl⟩ : syracuseStep 205281161 = 153960871) B153960871
theorem B3750569 : Blo 1666533 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B493239527 : Blo 1666533 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B3751163 : Blo 1666533 3751163 := bstep (se 1 (by rfl) ⟨2813372, by rfl⟩ : syracuseStep 3751163 = 5626745) B5626745
theorem B1125408329 : Blo 1666533 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B8437607 : Blo 1666533 8437607 := bstep (se 1 (by rfl) ⟨6328205, by rfl⟩ : syracuseStep 8437607 = 12656411) B12656411
theorem B28492235 : Blo 1666533 28492235 := bstep (se 1 (by rfl) ⟨21369176, by rfl⟩ : syracuseStep 28492235 = 42738353) B42738353
theorem B9012617 : Blo 1666533 9012617 := bstep (se 2 (by rfl) ⟨3379731, by rfl⟩ : syracuseStep 9012617 = 6759463) B6759463
theorem B2500379 : Blo 1666533 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B2500775 : Blo 1666533 2500775 := bstep (se 1 (by rfl) ⟨1875581, by rfl⟩ : syracuseStep 2500775 = 3751163) B3751163
theorem B21661931 : Blo 1666533 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B6501503 : Blo 1666533 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B5625071 : Blo 1666533 5625071 := bstep (se 1 (by rfl) ⟨4218803, by rfl⟩ : syracuseStep 5625071 = 8437607) B8437607
theorem B2570491 : Blo 1666533 2570491 := bstep (se 1 (by rfl) ⟨1927868, by rfl⟩ : syracuseStep 2570491 = 3855737) B3855737
theorem B2374057 : Blo 1666533 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B136854107 : Blo 1666533 136854107 := bstep (se 1 (by rfl) ⟨102640580, by rfl⟩ : syracuseStep 136854107 = 205281161) B205281161
theorem B328826351 : Blo 1666533 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B5627447 : Blo 1666533 5627447 := bstep (se 1 (by rfl) ⟨4220585, by rfl⟩ : syracuseStep 5627447 = 8441171) B8441171
theorem B750272219 : Blo 1666533 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B4334335 : Blo 1666533 4334335 := bstep (se 1 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 4334335 = 6501503) B6501503
theorem B91236071 : Blo 1666533 91236071 := bstep (se 1 (by rfl) ⟨68427053, by rfl⟩ : syracuseStep 91236071 = 136854107) B136854107
theorem B500181479 : Blo 1666533 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B3427321 : Blo 1666533 3427321 := bstep (se 2 (by rfl) ⟨1285245, by rfl⟩ : syracuseStep 3427321 = 2570491) B2570491
theorem B3165409 : Blo 1666533 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B57765149 : Blo 1666533 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B6008411 : Blo 1666533 6008411 := bstep (se 1 (by rfl) ⟨4506308, by rfl⟩ : syracuseStep 6008411 = 9012617) B9012617
theorem B1666919 : Blo 1666533 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B1667183 : Blo 1666533 1667183 := bstep (se 1 (by rfl) ⟨1250387, by rfl⟩ : syracuseStep 1667183 = 2500775) B2500775
theorem B18994823 : Blo 1666533 18994823 := bstep (se 1 (by rfl) ⟨14246117, by rfl⟩ : syracuseStep 18994823 = 28492235) B28492235
theorem B3750047 : Blo 1666533 3750047 := bstep (se 1 (by rfl) ⟨2812535, by rfl⟩ : syracuseStep 3750047 = 5625071) B5625071
theorem B876870269 : Blo 1666533 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B3751631 : Blo 1666533 3751631 := bstep (se 1 (by rfl) ⟨2813723, by rfl⟩ : syracuseStep 3751631 = 5627447) B5627447
theorem B2500031 : Blo 1666533 2500031 := bstep (se 1 (by rfl) ⟨1875023, by rfl⟩ : syracuseStep 2500031 = 3750047) B3750047
theorem B4220545 : Blo 1666533 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B2501087 : Blo 1666533 2501087 := bstep (se 1 (by rfl) ⟨1875815, by rfl⟩ : syracuseStep 2501087 = 3751631) B3751631
theorem B92465813 : Blo 1666533 92465813 := bstep (se 6 (by rfl) ⟨2167167, by rfl⟩ : syracuseStep 92465813 = 4334335) B4334335
theorem B12663215 : Blo 1666533 12663215 := bstep (se 1 (by rfl) ⟨9497411, by rfl⟩ : syracuseStep 12663215 = 18994823) B18994823
theorem B60824047 : Blo 1666533 60824047 := bstep (se 1 (by rfl) ⟨45618035, by rfl⟩ : syracuseStep 60824047 = 91236071) B91236071
theorem B4569761 : Blo 1666533 4569761 := bstep (se 2 (by rfl) ⟨1713660, by rfl⟩ : syracuseStep 4569761 = 3427321) B3427321
theorem B333454319 : Blo 1666533 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B584580179 : Blo 1666533 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B38510099 : Blo 1666533 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B4005607 : Blo 1666533 4005607 := bstep (se 1 (by rfl) ⟨3004205, by rfl⟩ : syracuseStep 4005607 = 6008411) B6008411
theorem B389720119 : Blo 1666533 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B1666687 : Blo 1666533 1666687 := bstep (se 1 (by rfl) ⟨1250015, by rfl⟩ : syracuseStep 1666687 = 2500031) B2500031
theorem B8442143 : Blo 1666533 8442143 := bstep (se 1 (by rfl) ⟨6331607, by rfl⟩ : syracuseStep 8442143 = 12663215) B12663215
theorem B1667391 : Blo 1666533 1667391 := bstep (se 1 (by rfl) ⟨1250543, by rfl⟩ : syracuseStep 1667391 = 2501087) B2501087
theorem B222302879 : Blo 1666533 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B81098729 : Blo 1666533 81098729 := bstep (se 2 (by rfl) ⟨30412023, by rfl⟩ : syracuseStep 81098729 = 60824047) B60824047
theorem B61643875 : Blo 1666533 61643875 := bstep (se 1 (by rfl) ⟨46232906, by rfl⟩ : syracuseStep 61643875 = 92465813) B92465813
theorem B3046507 : Blo 1666533 3046507 := bstep (se 1 (by rfl) ⟨2284880, by rfl⟩ : syracuseStep 3046507 = 4569761) B4569761
theorem B5627393 : Blo 1666533 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B5340809 : Blo 1666533 5340809 := bstep (se 2 (by rfl) ⟨2002803, by rfl⟩ : syracuseStep 5340809 = 4005607) B4005607
theorem B25673399 : Blo 1666533 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B519626825 : Blo 1666533 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B5628095 : Blo 1666533 5628095 := bstep (se 1 (by rfl) ⟨4221071, by rfl⟩ : syracuseStep 5628095 = 8442143) B8442143
theorem B148201919 : Blo 1666533 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B82191833 : Blo 1666533 82191833 := bstep (se 2 (by rfl) ⟨30821937, by rfl⟩ : syracuseStep 82191833 = 61643875) B61643875
theorem B17115599 : Blo 1666533 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B16248037 : Blo 1666533 16248037 := bstep (se 4 (by rfl) ⟨1523253, by rfl⟩ : syracuseStep 16248037 = 3046507) B3046507
theorem B3560539 : Blo 1666533 3560539 := bstep (se 1 (by rfl) ⟨2670404, by rfl⟩ : syracuseStep 3560539 = 5340809) B5340809
theorem B54065819 : Blo 1666533 54065819 := bstep (se 1 (by rfl) ⟨40549364, by rfl⟩ : syracuseStep 54065819 = 81098729) B81098729
theorem B3751595 : Blo 1666533 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B3752063 : Blo 1666533 3752063 := bstep (se 1 (by rfl) ⟨2814047, by rfl⟩ : syracuseStep 3752063 = 5628095) B5628095
theorem B2501063 : Blo 1666533 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B346417883 : Blo 1666533 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B4747385 : Blo 1666533 4747385 := bstep (se 2 (by rfl) ⟨1780269, by rfl⟩ : syracuseStep 4747385 = 3560539) B3560539
theorem B21664049 : Blo 1666533 21664049 := bstep (se 2 (by rfl) ⟨8124018, by rfl⟩ : syracuseStep 21664049 = 16248037) B16248037
theorem B98801279 : Blo 1666533 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B54794555 : Blo 1666533 54794555 := bstep (se 1 (by rfl) ⟨41095916, by rfl⟩ : syracuseStep 54794555 = 82191833) B82191833
theorem B11410399 : Blo 1666533 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B36043879 : Blo 1666533 36043879 := bstep (se 1 (by rfl) ⟨27032909, by rfl⟩ : syracuseStep 36043879 = 54065819) B54065819
theorem B36529703 : Blo 1666533 36529703 := bstep (se 1 (by rfl) ⟨27397277, by rfl⟩ : syracuseStep 36529703 = 54794555) B54794555
theorem B3164923 : Blo 1666533 3164923 := bstep (se 1 (by rfl) ⟨2373692, by rfl⟩ : syracuseStep 3164923 = 4747385) B4747385
theorem B2501375 : Blo 1666533 2501375 := bstep (se 1 (by rfl) ⟨1876031, by rfl⟩ : syracuseStep 2501375 = 3752063) B3752063
theorem B231083189 : Blo 1666533 231083189 := bstep (se 5 (by rfl) ⟨10832024, by rfl⟩ : syracuseStep 231083189 = 21664049) B21664049
theorem B65867519 : Blo 1666533 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B48058505 : Blo 1666533 48058505 := bstep (se 2 (by rfl) ⟨18021939, by rfl⟩ : syracuseStep 48058505 = 36043879) B36043879
theorem B1667375 : Blo 1666533 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B230945255 : Blo 1666533 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B60855461 : Blo 1666533 60855461 := bstep (se 4 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 60855461 = 11410399) B11410399
theorem B32039003 : Blo 1666533 32039003 := bstep (se 1 (by rfl) ⟨24029252, by rfl⟩ : syracuseStep 32039003 = 48058505) B48058505
theorem B4219897 : Blo 1666533 4219897 := bstep (se 2 (by rfl) ⟨1582461, by rfl⟩ : syracuseStep 4219897 = 3164923) B3164923
theorem B175646717 : Blo 1666533 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B153963503 : Blo 1666533 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B40570307 : Blo 1666533 40570307 := bstep (se 1 (by rfl) ⟨30427730, by rfl⟩ : syracuseStep 40570307 = 60855461) B60855461
theorem B1667583 : Blo 1666533 1667583 := bstep (se 1 (by rfl) ⟨1250687, by rfl⟩ : syracuseStep 1667583 = 2501375) B2501375
theorem B154055459 : Blo 1666533 154055459 := bstep (se 1 (by rfl) ⟨115541594, by rfl⟩ : syracuseStep 154055459 = 231083189) B231083189
theorem B24353135 : Blo 1666533 24353135 := bstep (se 1 (by rfl) ⟨18264851, by rfl⟩ : syracuseStep 24353135 = 36529703) B36529703
theorem B102703639 : Blo 1666533 102703639 := bstep (se 1 (by rfl) ⟨77027729, by rfl⟩ : syracuseStep 102703639 = 154055459) B154055459
theorem B117097811 : Blo 1666533 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B21359335 : Blo 1666533 21359335 := bstep (se 1 (by rfl) ⟨16019501, by rfl⟩ : syracuseStep 21359335 = 32039003) B32039003
theorem B102642335 : Blo 1666533 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B27046871 : Blo 1666533 27046871 := bstep (se 1 (by rfl) ⟨20285153, by rfl⟩ : syracuseStep 27046871 = 40570307) B40570307
theorem B5626529 : Blo 1666533 5626529 := bstep (se 2 (by rfl) ⟨2109948, by rfl⟩ : syracuseStep 5626529 = 4219897) B4219897
theorem B16235423 : Blo 1666533 16235423 := bstep (se 1 (by rfl) ⟨12176567, by rfl⟩ : syracuseStep 16235423 = 24353135) B24353135
theorem B68428223 : Blo 1666533 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B18031247 : Blo 1666533 18031247 := bstep (se 1 (by rfl) ⟨13523435, by rfl⟩ : syracuseStep 18031247 = 27046871) B27046871
theorem B136938185 : Blo 1666533 136938185 := bstep (se 2 (by rfl) ⟨51351819, by rfl⟩ : syracuseStep 136938185 = 102703639) B102703639
theorem B10823615 : Blo 1666533 10823615 := bstep (se 1 (by rfl) ⟨8117711, by rfl⟩ : syracuseStep 10823615 = 16235423) B16235423
theorem B78065207 : Blo 1666533 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B28479113 : Blo 1666533 28479113 := bstep (se 2 (by rfl) ⟨10679667, by rfl⟩ : syracuseStep 28479113 = 21359335) B21359335
theorem B3751019 : Blo 1666533 3751019 := bstep (se 1 (by rfl) ⟨2813264, by rfl⟩ : syracuseStep 3751019 = 5626529) B5626529
theorem B91292123 : Blo 1666533 91292123 := bstep (se 1 (by rfl) ⟨68469092, by rfl⟩ : syracuseStep 91292123 = 136938185) B136938185
theorem B2500679 : Blo 1666533 2500679 := bstep (se 1 (by rfl) ⟨1875509, by rfl⟩ : syracuseStep 2500679 = 3751019) B3751019
theorem B12020831 : Blo 1666533 12020831 := bstep (se 1 (by rfl) ⟨9015623, by rfl⟩ : syracuseStep 12020831 = 18031247) B18031247
theorem B18986075 : Blo 1666533 18986075 := bstep (se 1 (by rfl) ⟨14239556, by rfl⟩ : syracuseStep 18986075 = 28479113) B28479113
theorem B45618815 : Blo 1666533 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B7215743 : Blo 1666533 7215743 := bstep (se 1 (by rfl) ⟨5411807, by rfl⟩ : syracuseStep 7215743 = 10823615) B10823615
theorem B52043471 : Blo 1666533 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B12657383 : Blo 1666533 12657383 := bstep (se 1 (by rfl) ⟨9493037, by rfl⟩ : syracuseStep 12657383 = 18986075) B18986075
theorem B4810495 : Blo 1666533 4810495 := bstep (se 1 (by rfl) ⟨3607871, by rfl⟩ : syracuseStep 4810495 = 7215743) B7215743
theorem B8013887 : Blo 1666533 8013887 := bstep (se 1 (by rfl) ⟨6010415, by rfl⟩ : syracuseStep 8013887 = 12020831) B12020831
theorem B34695647 : Blo 1666533 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B60861415 : Blo 1666533 60861415 := bstep (se 1 (by rfl) ⟨45646061, by rfl⟩ : syracuseStep 60861415 = 91292123) B91292123
theorem B30412543 : Blo 1666533 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B1667119 : Blo 1666533 1667119 := bstep (se 1 (by rfl) ⟨1250339, by rfl⟩ : syracuseStep 1667119 = 2500679) B2500679
theorem B8438255 : Blo 1666533 8438255 := bstep (se 1 (by rfl) ⟨6328691, by rfl⟩ : syracuseStep 8438255 = 12657383) B12657383
theorem B5342591 : Blo 1666533 5342591 := bstep (se 1 (by rfl) ⟨4006943, by rfl⟩ : syracuseStep 5342591 = 8013887) B8013887
theorem B23130431 : Blo 1666533 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B81148553 : Blo 1666533 81148553 := bstep (se 2 (by rfl) ⟨30430707, by rfl⟩ : syracuseStep 81148553 = 60861415) B60861415
theorem B6413993 : Blo 1666533 6413993 := bstep (se 2 (by rfl) ⟨2405247, by rfl⟩ : syracuseStep 6413993 = 4810495) B4810495
theorem B40550057 : Blo 1666533 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B15420287 : Blo 1666533 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B5625503 : Blo 1666533 5625503 := bstep (se 1 (by rfl) ⟨4219127, by rfl⟩ : syracuseStep 5625503 = 8438255) B8438255
theorem B3561727 : Blo 1666533 3561727 := bstep (se 1 (by rfl) ⟨2671295, by rfl⟩ : syracuseStep 3561727 = 5342591) B5342591
theorem B54099035 : Blo 1666533 54099035 := bstep (se 1 (by rfl) ⟨40574276, by rfl⟩ : syracuseStep 54099035 = 81148553) B81148553
theorem B4275995 : Blo 1666533 4275995 := bstep (se 1 (by rfl) ⟨3206996, by rfl⟩ : syracuseStep 4275995 = 6413993) B6413993
theorem B27033371 : Blo 1666533 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B36066023 : Blo 1666533 36066023 := bstep (se 1 (by rfl) ⟨27049517, by rfl⟩ : syracuseStep 36066023 = 54099035) B54099035
theorem B4748969 : Blo 1666533 4748969 := bstep (se 2 (by rfl) ⟨1780863, by rfl⟩ : syracuseStep 4748969 = 3561727) B3561727
theorem B3750335 : Blo 1666533 3750335 := bstep (se 1 (by rfl) ⟨2812751, by rfl⟩ : syracuseStep 3750335 = 5625503) B5625503
theorem B10280191 : Blo 1666533 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B11402653 : Blo 1666533 11402653 := bstep (se 3 (by rfl) ⟨2137997, by rfl⟩ : syracuseStep 11402653 = 4275995) B4275995
theorem B18022247 : Blo 1666533 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B24044015 : Blo 1666533 24044015 := bstep (se 1 (by rfl) ⟨18033011, by rfl⟩ : syracuseStep 24044015 = 36066023) B36066023
theorem B2500223 : Blo 1666533 2500223 := bstep (se 1 (by rfl) ⟨1875167, by rfl⟩ : syracuseStep 2500223 = 3750335) B3750335
theorem B13706921 : Blo 1666533 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B3165979 : Blo 1666533 3165979 := bstep (se 1 (by rfl) ⟨2374484, by rfl⟩ : syracuseStep 3165979 = 4748969) B4748969
theorem B12014831 : Blo 1666533 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B15203537 : Blo 1666533 15203537 := bstep (se 2 (by rfl) ⟨5701326, by rfl⟩ : syracuseStep 15203537 = 11402653) B11402653
theorem B32039549 : Blo 1666533 32039549 := bstep (se 3 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 32039549 = 12014831) B12014831
theorem B10135691 : Blo 1666533 10135691 := bstep (se 1 (by rfl) ⟨7601768, by rfl⟩ : syracuseStep 10135691 = 15203537) B15203537
theorem B4221305 : Blo 1666533 4221305 := bstep (se 2 (by rfl) ⟨1582989, by rfl⟩ : syracuseStep 4221305 = 3165979) B3165979
theorem B1666815 : Blo 1666533 1666815 := bstep (se 1 (by rfl) ⟨1250111, by rfl⟩ : syracuseStep 1666815 = 2500223) B2500223
theorem B9137947 : Blo 1666533 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B16029343 : Blo 1666533 16029343 := bstep (se 1 (by rfl) ⟨12022007, by rfl⟩ : syracuseStep 16029343 = 24044015) B24044015
theorem B12183929 : Blo 1666533 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B21359699 : Blo 1666533 21359699 := bstep (se 1 (by rfl) ⟨16019774, by rfl⟩ : syracuseStep 21359699 = 32039549) B32039549
theorem B2814203 : Blo 1666533 2814203 := bstep (se 1 (by rfl) ⟨2110652, by rfl⟩ : syracuseStep 2814203 = 4221305) B4221305
theorem B6757127 : Blo 1666533 6757127 := bstep (se 1 (by rfl) ⟨5067845, by rfl⟩ : syracuseStep 6757127 = 10135691) B10135691
theorem B21372457 : Blo 1666533 21372457 := bstep (se 2 (by rfl) ⟨8014671, by rfl⟩ : syracuseStep 21372457 = 16029343) B16029343
theorem B1876135 : Blo 1666533 1876135 := bstep (se 1 (by rfl) ⟨1407101, by rfl⟩ : syracuseStep 1876135 = 2814203) B2814203
theorem B14239799 : Blo 1666533 14239799 := bstep (se 1 (by rfl) ⟨10679849, by rfl⟩ : syracuseStep 14239799 = 21359699) B21359699
theorem B8122619 : Blo 1666533 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B28496609 : Blo 1666533 28496609 := bstep (se 2 (by rfl) ⟨10686228, by rfl⟩ : syracuseStep 28496609 = 21372457) B21372457
theorem B4504751 : Blo 1666533 4504751 := bstep (se 1 (by rfl) ⟨3378563, by rfl⟩ : syracuseStep 4504751 = 6757127) B6757127
theorem B18997739 : Blo 1666533 18997739 := bstep (se 1 (by rfl) ⟨14248304, by rfl⟩ : syracuseStep 18997739 = 28496609) B28496609
theorem B21660317 : Blo 1666533 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B2501513 : Blo 1666533 2501513 := bstep (se 2 (by rfl) ⟨938067, by rfl⟩ : syracuseStep 2501513 = 1876135) B1876135
theorem B3003167 : Blo 1666533 3003167 := bstep (se 1 (by rfl) ⟨2252375, by rfl⟩ : syracuseStep 3003167 = 4504751) B4504751
theorem B9493199 : Blo 1666533 9493199 := bstep (se 1 (by rfl) ⟨7119899, by rfl⟩ : syracuseStep 9493199 = 14239799) B14239799
theorem B12665159 : Blo 1666533 12665159 := bstep (se 1 (by rfl) ⟨9498869, by rfl⟩ : syracuseStep 12665159 = 18997739) B18997739
theorem B6328799 : Blo 1666533 6328799 := bstep (se 1 (by rfl) ⟨4746599, by rfl⟩ : syracuseStep 6328799 = 9493199) B9493199
theorem B1667675 : Blo 1666533 1667675 := bstep (se 1 (by rfl) ⟨1250756, by rfl⟩ : syracuseStep 1667675 = 2501513) B2501513
theorem B8008445 : Blo 1666533 8008445 := bstep (se 3 (by rfl) ⟨1501583, by rfl⟩ : syracuseStep 8008445 = 3003167) B3003167
theorem B14440211 : Blo 1666533 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B4219199 : Blo 1666533 4219199 := bstep (se 1 (by rfl) ⟨3164399, by rfl⟩ : syracuseStep 4219199 = 6328799) B6328799
theorem B9626807 : Blo 1666533 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B8443439 : Blo 1666533 8443439 := bstep (se 1 (by rfl) ⟨6332579, by rfl⟩ : syracuseStep 8443439 = 12665159) B12665159
theorem B5338963 : Blo 1666533 5338963 := bstep (se 1 (by rfl) ⟨4004222, by rfl⟩ : syracuseStep 5338963 = 8008445) B8008445
theorem B5628959 : Blo 1666533 5628959 := bstep (se 1 (by rfl) ⟨4221719, by rfl⟩ : syracuseStep 5628959 = 8443439) B8443439
theorem B2812799 : Blo 1666533 2812799 := bstep (se 1 (by rfl) ⟨2109599, by rfl⟩ : syracuseStep 2812799 = 4219199) B4219199
theorem B25671485 : Blo 1666533 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B7118617 : Blo 1666533 7118617 := bstep (se 2 (by rfl) ⟨2669481, by rfl⟩ : syracuseStep 7118617 = 5338963) B5338963
theorem B3752639 : Blo 1666533 3752639 := bstep (se 1 (by rfl) ⟨2814479, by rfl⟩ : syracuseStep 3752639 = 5628959) B5628959
theorem B17114323 : Blo 1666533 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B9491489 : Blo 1666533 9491489 := bstep (se 2 (by rfl) ⟨3559308, by rfl⟩ : syracuseStep 9491489 = 7118617) B7118617
theorem B1875199 : Blo 1666533 1875199 := bstep (se 1 (by rfl) ⟨1406399, by rfl⟩ : syracuseStep 1875199 = 2812799) B2812799
theorem B2500265 : Blo 1666533 2500265 := bstep (se 2 (by rfl) ⟨937599, by rfl⟩ : syracuseStep 2500265 = 1875199) B1875199
theorem B2501759 : Blo 1666533 2501759 := bstep (se 1 (by rfl) ⟨1876319, by rfl⟩ : syracuseStep 2501759 = 3752639) B3752639
theorem B6327659 : Blo 1666533 6327659 := bstep (se 1 (by rfl) ⟨4745744, by rfl⟩ : syracuseStep 6327659 = 9491489) B9491489
theorem B22819097 : Blo 1666533 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B15212731 : Blo 1666533 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B1666843 : Blo 1666533 1666843 := bstep (se 1 (by rfl) ⟨1250132, by rfl⟩ : syracuseStep 1666843 = 2500265) B2500265
theorem B1667839 : Blo 1666533 1667839 := bstep (se 1 (by rfl) ⟨1250879, by rfl⟩ : syracuseStep 1667839 = 2501759) B2501759
theorem B4218439 : Blo 1666533 4218439 := bstep (se 1 (by rfl) ⟨3163829, by rfl⟩ : syracuseStep 4218439 = 6327659) B6327659
theorem B20283641 : Blo 1666533 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B5624585 : Blo 1666533 5624585 := bstep (se 2 (by rfl) ⟨2109219, by rfl⟩ : syracuseStep 5624585 = 4218439) B4218439
theorem B13522427 : Blo 1666533 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B3749723 : Blo 1666533 3749723 := bstep (se 1 (by rfl) ⟨2812292, by rfl⟩ : syracuseStep 3749723 = 5624585) B5624585
theorem B2499815 : Blo 1666533 2499815 := bstep (se 1 (by rfl) ⟨1874861, by rfl⟩ : syracuseStep 2499815 = 3749723) B3749723
theorem B9014951 : Blo 1666533 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B1666543 : Blo 1666533 1666543 := bstep (se 1 (by rfl) ⟨1249907, by rfl⟩ : syracuseStep 1666543 = 2499815) B2499815
theorem B6009967 : Blo 1666533 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 1666533 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B10684385 : Blo 1666533 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 1666533 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B4748615 : Blo 1666533 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 1666533 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B8441981 : Blo 1666533 8441981 := bstep (se 3 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 8441981 = 3165743) B3165743
theorem B5627987 : Blo 1666533 5627987 := bstep (se 1 (by rfl) ⟨4220990, by rfl⟩ : syracuseStep 5627987 = 8441981) B8441981
theorem B3751991 : Blo 1666533 3751991 := bstep (se 1 (by rfl) ⟨2813993, by rfl⟩ : syracuseStep 3751991 = 5627987) B5627987
theorem B2501327 : Blo 1666533 2501327 := bstep (se 1 (by rfl) ⟨1875995, by rfl⟩ : syracuseStep 2501327 = 3751991) B3751991
theorem B1667551 : Blo 1666533 1667551 := bstep (se 1 (by rfl) ⟨1250663, by rfl⟩ : syracuseStep 1667551 = 2501327) B2501327

theorem C0 (j : ℕ) (h1 : 416633 ≤ j) (h2 : j ≤ 417007) : Blo 1666533 (4 * j + 3) := by
  interval_cases j
  · exact B1666535
  · exact B1666539
  · exact B1666543
  · exact B1666547
  · exact B1666551
  · exact B1666555
  · exact B1666559
  · exact B1666563
  · exact B1666567
  · exact B1666571
  · exact B1666575
  · exact B1666579
  · exact B1666583
  · exact B1666587
  · exact B1666591
  · exact B1666595
  · exact B1666599
  · exact B1666603
  · exact B1666607
  · exact B1666611
  · exact B1666615
  · exact B1666619
  · exact B1666623
  · exact B1666627
  · exact B1666631
  · exact B1666635
  · exact B1666639
  · exact B1666643
  · exact B1666647
  · exact B1666651
  · exact B1666655
  · exact B1666659
  · exact B1666663
  · exact B1666667
  · exact B1666671
  · exact B1666675
  · exact B1666679
  · exact B1666683
  · exact B1666687
  · exact B1666691
  · exact B1666695
  · exact B1666699
  · exact B1666703
  · exact B1666707
  · exact B1666711
  · exact B1666715
  · exact B1666719
  · exact B1666723
  · exact B1666727
  · exact B1666731
  · exact B1666735
  · exact B1666739
  · exact B1666743
  · exact B1666747
  · exact B1666751
  · exact B1666755
  · exact B1666759
  · exact B1666763
  · exact B1666767
  · exact B1666771
  · exact B1666775
  · exact B1666779
  · exact B1666783
  · exact B1666787
  · exact B1666791
  · exact B1666795
  · exact B1666799
  · exact B1666803
  · exact B1666807
  · exact B1666811
  · exact B1666815
  · exact B1666819
  · exact B1666823
  · exact B1666827
  · exact B1666831
  · exact B1666835
  · exact B1666839
  · exact B1666843
  · exact B1666847
  · exact B1666851
  · exact B1666855
  · exact B1666859
  · exact B1666863
  · exact B1666867
  · exact B1666871
  · exact B1666875
  · exact B1666879
  · exact B1666883
  · exact B1666887
  · exact B1666891
  · exact B1666895
  · exact B1666899
  · exact B1666903
  · exact B1666907
  · exact B1666911
  · exact B1666915
  · exact B1666919
  · exact B1666923
  · exact B1666927
  · exact B1666931
  · exact B1666935
  · exact B1666939
  · exact B1666943
  · exact B1666947
  · exact B1666951
  · exact B1666955
  · exact B1666959
  · exact B1666963
  · exact B1666967
  · exact B1666971
  · exact B1666975
  · exact B1666979
  · exact B1666983
  · exact B1666987
  · exact B1666991
  · exact B1666995
  · exact B1666999
  · exact B1667003
  · exact B1667007
  · exact B1667011
  · exact B1667015
  · exact B1667019
  · exact B1667023
  · exact B1667027
  · exact B1667031
  · exact B1667035
  · exact B1667039
  · exact B1667043
  · exact B1667047
  · exact B1667051
  · exact B1667055
  · exact B1667059
  · exact B1667063
  · exact B1667067
  · exact B1667071
  · exact B1667075
  · exact B1667079
  · exact B1667083
  · exact B1667087
  · exact B1667091
  · exact B1667095
  · exact B1667099
  · exact B1667103
  · exact B1667107
  · exact B1667111
  · exact B1667115
  · exact B1667119
  · exact B1667123
  · exact B1667127
  · exact B1667131
  · exact B1667135
  · exact B1667139
  · exact B1667143
  · exact B1667147
  · exact B1667151
  · exact B1667155
  · exact B1667159
  · exact B1667163
  · exact B1667167
  · exact B1667171
  · exact B1667175
  · exact B1667179
  · exact B1667183
  · exact B1667187
  · exact B1667191
  · exact B1667195
  · exact B1667199
  · exact B1667203
  · exact B1667207
  · exact B1667211
  · exact B1667215
  · exact B1667219
  · exact B1667223
  · exact B1667227
  · exact B1667231
  · exact B1667235
  · exact B1667239
  · exact B1667243
  · exact B1667247
  · exact B1667251
  · exact B1667255
  · exact B1667259
  · exact B1667263
  · exact B1667267
  · exact B1667271
  · exact B1667275
  · exact B1667279
  · exact B1667283
  · exact B1667287
  · exact B1667291
  · exact B1667295
  · exact B1667299
  · exact B1667303
  · exact B1667307
  · exact B1667311
  · exact B1667315
  · exact B1667319
  · exact B1667323
  · exact B1667327
  · exact B1667331
  · exact B1667335
  · exact B1667339
  · exact B1667343
  · exact B1667347
  · exact B1667351
  · exact B1667355
  · exact B1667359
  · exact B1667363
  · exact B1667367
  · exact B1667371
  · exact B1667375
  · exact B1667379
  · exact B1667383
  · exact B1667387
  · exact B1667391
  · exact B1667395
  · exact B1667399
  · exact B1667403
  · exact B1667407
  · exact B1667411
  · exact B1667415
  · exact B1667419
  · exact B1667423
  · exact B1667427
  · exact B1667431
  · exact B1667435
  · exact B1667439
  · exact B1667443
  · exact B1667447
  · exact B1667451
  · exact B1667455
  · exact B1667459
  · exact B1667463
  · exact B1667467
  · exact B1667471
  · exact B1667475
  · exact B1667479
  · exact B1667483
  · exact B1667487
  · exact B1667491
  · exact B1667495
  · exact B1667499
  · exact B1667503
  · exact B1667507
  · exact B1667511
  · exact B1667515
  · exact B1667519
  · exact B1667523
  · exact B1667527
  · exact B1667531
  · exact B1667535
  · exact B1667539
  · exact B1667543
  · exact B1667547
  · exact B1667551
  · exact B1667555
  · exact B1667559
  · exact B1667563
  · exact B1667567
  · exact B1667571
  · exact B1667575
  · exact B1667579
  · exact B1667583
  · exact B1667587
  · exact B1667591
  · exact B1667595
  · exact B1667599
  · exact B1667603
  · exact B1667607
  · exact B1667611
  · exact B1667615
  · exact B1667619
  · exact B1667623
  · exact B1667627
  · exact B1667631
  · exact B1667635
  · exact B1667639
  · exact B1667643
  · exact B1667647
  · exact B1667651
  · exact B1667655
  · exact B1667659
  · exact B1667663
  · exact B1667667
  · exact B1667671
  · exact B1667675
  · exact B1667679
  · exact B1667683
  · exact B1667687
  · exact B1667691
  · exact B1667695
  · exact B1667699
  · exact B1667703
  · exact B1667707
  · exact B1667711
  · exact B1667715
  · exact B1667719
  · exact B1667723
  · exact B1667727
  · exact B1667731
  · exact B1667735
  · exact B1667739
  · exact B1667743
  · exact B1667747
  · exact B1667751
  · exact B1667755
  · exact B1667759
  · exact B1667763
  · exact B1667767
  · exact B1667771
  · exact B1667775
  · exact B1667779
  · exact B1667783
  · exact B1667787
  · exact B1667791
  · exact B1667795
  · exact B1667799
  · exact B1667803
  · exact B1667807
  · exact B1667811
  · exact B1667815
  · exact B1667819
  · exact B1667823
  · exact B1667827
  · exact B1667831
  · exact B1667835
  · exact B1667839
  · exact B1667843
  · exact B1667847
  · exact B1667851
  · exact B1667855
  · exact B1667859
  · exact B1667863
  · exact B1667867
  · exact B1667871
  · exact B1667875
  · exact B1667879
  · exact B1667883
  · exact B1667887
  · exact B1667891
  · exact B1667895
  · exact B1667899
  · exact B1667903
  · exact B1667907
  · exact B1667911
  · exact B1667915
  · exact B1667919
  · exact B1667923
  · exact B1667927
  · exact B1667931
  · exact B1667935
  · exact B1667939
  · exact B1667943
  · exact B1667947
  · exact B1667951
  · exact B1667955
  · exact B1667959
  · exact B1667963
  · exact B1667967
  · exact B1667971
  · exact B1667975
  · exact B1667979
  · exact B1667983
  · exact B1667987
  · exact B1667991
  · exact B1667995
  · exact B1667999
  · exact B1668003
  · exact B1668007
  · exact B1668011
  · exact B1668015
  · exact B1668019
  · exact B1668023
  · exact B1668027
  · exact B1668031

theorem solution (m : ℕ) (hlo : 1666533 ≤ m) (hhi : m ≤ 1668033) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 416633 ≤ j := by omega
    have hj2 : j ≤ 417007 := by omega
    have hb : Blo 1666533 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
